// Mirrors dafny/logging/UndoRecovery.dfy — Pure Undo crash recovery from
// on-disk state and flushed Undo log.

import type { DatabaseState, LogRecord, TxId } from "./types";

export interface RecoveryAction {
  kind: "RESTORE" | "ABORT";
  tx: TxId;
  element?: string;
  oldValue?: number;
}

export interface RecoveryResult {
  recoveredDisk: DatabaseState;
  recoveryAborts: LogRecord[];
  actions: RecoveryAction[];
}

export function finishedTxs(flushedLog: readonly LogRecord[]): Set<TxId> {
  const finished = new Set<TxId>();
  for (const rec of flushedLog) {
    if (rec.kind === "LogCommit" || rec.kind === "LogAbort") {
      finished.add(rec.tx);
    }
  }
  return finished;
}

export function recoverFromCrash(
  diskAtCrash: DatabaseState,
  flushedLog: readonly LogRecord[]
): RecoveryResult {
  const finished = finishedTxs(flushedLog);
  const recoveredDisk: DatabaseState = { ...diskAtCrash };
  const recoveryAborts: LogRecord[] = [];
  const actions: RecoveryAction[] = [];
  const abortedSet = new Set<TxId>();

  for (let idx = flushedLog.length - 1; idx >= 0; idx--) {
    const rec = flushedLog[idx];
    if (rec.kind === "LogUndoUpdate") {
      if (!finished.has(rec.tx) && rec.element in recoveredDisk) {
        recoveredDisk[rec.element] = rec.oldValue;
        actions.push({
          kind: "RESTORE",
          tx: rec.tx,
          element: rec.element,
          oldValue: rec.oldValue
        });
      }
    } else if (rec.kind === "LogStart") {
      if (!finished.has(rec.tx) && !abortedSet.has(rec.tx)) {
        recoveryAborts.push({ kind: "LogAbort", tx: rec.tx });
        abortedSet.add(rec.tx);
        actions.push({ kind: "ABORT", tx: rec.tx });
      }
    }
  }

  return { recoveredDisk, recoveryAborts, actions };
}
