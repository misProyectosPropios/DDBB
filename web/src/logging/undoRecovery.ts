// Mirrors dafny/logging/UndoRecovery.dfy — Checkpoint-aware Undo crash recovery.

import type { RecoveryAction, RecoveryResult, RecoveryStrategy } from "./dispatch";
import { finishedTxs, type DatabaseState, type LogRecord, type TxId } from "./types";

export class UndoRecoveryStrategy implements RecoveryStrategy {
  recoverFromCrash(
    diskAtCrash: DatabaseState,
    flushedLog: readonly LogRecord[]
  ): RecoveryResult {
    const finished = finishedTxs(flushedLog);
    const recoveredDisk: DatabaseState = { ...diskAtCrash };
    const recoveryAborts: LogRecord[] = [];
    const actions: RecoveryAction[] = [];
    const abortedSet = new Set<TxId>();
    let sawEndCkpt = false;

    for (let idx = flushedLog.length - 1; idx >= 0; idx--) {
      const rec = flushedLog[idx];
      switch (rec.kind) {
        case "LogUndoUpdate":
          if (!finished.has(rec.tx) && rec.element in recoveredDisk) {
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
            note: `Stopped backward scan at quiescent <CKPT> (record #${idx + 1})`
          });
          return { recoveredDisk, recoveryAborts, actions };
        case "LogEndCheckpoint":
          sawEndCkpt = true;
          break;
        case "LogStartCheckpoint":
          if (sawEndCkpt) {
            actions.push({
              kind: "CHECKPOINT_BOUNDARY",
              note: `Stopped backward scan at completed <START CKPT(${rec.activeTxs.join(", ")})> (record #${idx + 1})`
            });
            return { recoveredDisk, recoveryAborts, actions };
          }
          break;
        default:
          break;
      }
    }

    return { recoveredDisk, recoveryAborts, actions };
  }
}

export function recoverFromCrash(
  diskAtCrash: DatabaseState,
  flushedLog: readonly LogRecord[]
): RecoveryResult {
  return new UndoRecoveryStrategy().recoverFromCrash(diskAtCrash, flushedLog);
}
