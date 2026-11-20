// Mirrors dafny/logging/RedoRecovery.dfy — Checkpoint-aware Redo crash recovery.

import type { RecoveryAction, RecoveryResult, RecoveryStrategy } from "./dispatch";
import { committedTxs, finishedTxs, type DatabaseState, type LogRecord, type TxId } from "./types";

export function lastCompleteCheckpointIndex(flushedLog: readonly LogRecord[]): number {
  let sawEndCkpt = false;
  for (let idx = flushedLog.length - 1; idx >= 0; idx--) {
    const rec = flushedLog[idx];
    if (rec.kind === "LogCheckpoint" && !sawEndCkpt) {
      return idx;
    }
    if (rec.kind === "LogEndCheckpoint") {
      sawEndCkpt = true;
    } else if (rec.kind === "LogStartCheckpoint" && sawEndCkpt) {
      return idx;
    }
  }
  return 0;
}

export class RedoRecoveryStrategy implements RecoveryStrategy {
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

    if (startIdx > 0) {
      actions.push({
        kind: "CHECKPOINT_BOUNDARY",
        note: `Started forward replay at checkpoint boundary (record #${startIdx + 1})`
      });
    }

    for (let idx = startIdx; idx < flushedLog.length; idx++) {
      const rec = flushedLog[idx];
      switch (rec.kind) {
        case "LogRedoUpdate":
          if (committed.has(rec.tx) && rec.element in recoveredDisk) {
            recoveredDisk[rec.element] = rec.newValue;
            actions.push({
              kind: "REDO",
              tx: rec.tx,
              element: rec.element,
              value: rec.newValue
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
        case "LogStartCheckpoint":
          for (const tx of rec.activeTxs) {
            if (!finished.has(tx) && !abortedSet.has(tx)) {
              recoveryAborts.push({ kind: "LogAbort", tx });
              abortedSet.add(tx);
              actions.push({ kind: "ABORT", tx });
            }
          }
          break;
        default:
          break;
      }
    }

    return { recoveredDisk, recoveryAborts, actions };
  }
}

export function recoverRedoFromCrash(
  diskAtCrash: DatabaseState,
  flushedLog: readonly LogRecord[]
): RecoveryResult {
  return new RedoRecoveryStrategy().recoverFromCrash(diskAtCrash, flushedLog);
}
