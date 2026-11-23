// Mirrors dafny/logging/UndoRedoRecovery.dfy — Two-pass Undo/Redo crash recovery
// (Pass 1: forward Redo of committed transactions; Pass 2: backward Undo of
// uncommitted transactions).

import type { RecoveryAction, RecoveryResult, RecoveryStrategy } from "./dispatch";
import { lastCompleteCheckpointIndex } from "./redoRecovery";
import { committedTxs, finishedTxs, type DatabaseState, type LogRecord, type TxId } from "./types";

export class UndoRedoRecoveryStrategy implements RecoveryStrategy {
  recoverFromCrash(
    diskAtCrash: DatabaseState,
    flushedLog: readonly LogRecord[]
  ): RecoveryResult {
    const committed = committedTxs(flushedLog);
    const finished = finishedTxs(flushedLog);
    const startIdx = lastCompleteCheckpointIndex(flushedLog);

    const recoveredDisk: DatabaseState = { ...diskAtCrash };
    const recoveryAborts: LogRecord[] = [];
    const actions: RecoveryAction[] = [];
    const abortedSet = new Set<TxId>();

    // Phase 1: Forward Redo pass for committed transactions from startIdx
    if (startIdx > 0) {
      actions.push({
        kind: "CHECKPOINT_BOUNDARY",
        note: `Phase 1 (Redo): starting forward scan at checkpoint boundary (record #${startIdx + 1})`
      });
    }

    for (let idx = startIdx; idx < flushedLog.length; idx++) {
      const rec = flushedLog[idx];
      if (
        rec.kind === "LogUndoRedoUpdate" &&
        committed.has(rec.tx) &&
        rec.element in recoveredDisk
      ) {
        recoveredDisk[rec.element] = rec.newValue;
        actions.push({
          kind: "REDO",
          tx: rec.tx,
          element: rec.element,
          value: rec.newValue
        });
      }
    }

    // Phase 2: Backward Undo pass for uncommitted transactions
    for (let idx = flushedLog.length - 1; idx >= 0; idx--) {
      const rec = flushedLog[idx];
      switch (rec.kind) {
        case "LogUndoRedoUpdate":
          if (!committed.has(rec.tx) && rec.element in recoveredDisk) {
            recoveredDisk[rec.element] = rec.oldValue;
            actions.push({
              kind: "RESTORE",
              tx: rec.tx,
              element: rec.element,
              value: rec.oldValue
            });
          }
          break;
        case "LogStart":
          if (!finished.has(rec.tx) && !abortedSet.has(rec.tx)) {
            recoveryAborts.push({ kind: "LogAbort", tx: rec.tx });
            abortedSet.add(rec.tx);
            actions.push({ kind: "ABORT", tx: rec.tx });
          }
          break;
        case "LogCheckpoint":
          actions.push({
            kind: "CHECKPOINT_BOUNDARY",
            note: `Phase 2 (Undo): stopped backward scan at quiescent <CKPT> (record #${idx + 1})`
          });
          return { recoveredDisk, recoveryAborts, actions };
        default:
          break;
      }
    }

    return { recoveredDisk, recoveryAborts, actions };
  }
}

export function recoverUndoRedoFromCrash(
  diskAtCrash: DatabaseState,
  flushedLog: readonly LogRecord[]
): RecoveryResult {
  return new UndoRedoRecoveryStrategy().recoverFromCrash(diskAtCrash, flushedLog);
}
