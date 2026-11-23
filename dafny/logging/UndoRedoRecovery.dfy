// Undo/Redo Crash Recovery module implementing RecoveryStrategy.
//
// Under Undo/Redo logging (STEAL / NO-FORCE buffer management), at crash time:
//   - Some uncommitted changes may already have been written to disk (STEAL),
//     requiring a backward UNDO pass using `oldVal`.
//   - Some committed changes may not yet have been written to disk (NO-FORCE),
//     requiring a forward REDO pass using `newVal`.
//
// Following Garcia-Molina Section 17.4.1, recovery executes two passes over
// `flushedLog`:
//   1. Forward Redo Pass (earliest-first from the last completed checkpoint
//      or index 0): for every <T, X, oldVal, newVal> belonging to a committed
//      transaction T, sets disk[X] := newVal.
//   2. Backward Undo Pass (latest-first from the end of `flushedLog`): for
//      every <T, X, oldVal, newVal> belonging to an uncommitted transaction T,
//      restores disk[X] := oldVal, and emits <ABORT T> for every incomplete
//      transaction.

include "Types.dfy"
include "Dispatch.dfy"
include "RedoRecovery.dfy"

module UndoRedoRecovery {
  import opened LoggingTypes
  import opened LoggingDispatch
  import RedoRecovery

  // Elements touched by any Undo/Redo update record in `flushedLog`.
  ghost function ModifiedUndoRedoElements(flushedLog: seq<LogRecord>): set<ElementId>
  {
    set i | 0 <= i < |flushedLog| && flushedLog[i].LogUndoRedoUpdate? :: flushedLog[i].element
  }

  // Phase 1: Forward Redo pass for all committed transactions from `startIdx`.
  method RedoCommittedPass(
    diskAtCrash: DatabaseState,
    flushedLog: seq<LogRecord>,
    committed: set<TxId>
  ) returns (afterRedo: DatabaseState)
    ensures afterRedo.Keys == diskAtCrash.Keys
    ensures forall e :: e in diskAtCrash.Keys && e !in ModifiedUndoRedoElements(flushedLog) ==>
      afterRedo[e] == diskAtCrash[e]
  {
    var startIdx := RedoRecovery.LastCompleteCheckpointIndex(flushedLog);
    afterRedo := diskAtCrash;
    var idx := startIdx;
    while idx < |flushedLog|
      invariant startIdx <= idx <= |flushedLog|
      invariant afterRedo.Keys == diskAtCrash.Keys
      invariant forall e :: e in diskAtCrash.Keys && e !in ModifiedUndoRedoElements(flushedLog) ==>
        afterRedo[e] == diskAtCrash[e]
      decreases |flushedLog| - idx
    {
      var rec := flushedLog[idx];
      if rec.LogUndoRedoUpdate? && rec.tx in committed && rec.element in afterRedo {
        assert rec.element in ModifiedUndoRedoElements(flushedLog);
        afterRedo := afterRedo[rec.element := rec.newValue];
      }
      idx := idx + 1;
    }
  }

  // Phase 2: Backward Undo pass for all uncommitted transactions.
  method UndoUncommittedPass(
    diskAfterRedo: DatabaseState,
    flushedLog: seq<LogRecord>,
    committed: set<TxId>,
    finished: set<TxId>
  ) returns (recoveredDisk: DatabaseState, recoveryAborts: seq<LogRecord>)
    requires finished == FinishedTxs(flushedLog)
    ensures recoveredDisk.Keys == diskAfterRedo.Keys
    ensures forall e :: e in diskAfterRedo.Keys && e !in ModifiedUndoRedoElements(flushedLog) ==>
      recoveredDisk[e] == diskAfterRedo[e]
    ensures forall k :: 0 <= k < |recoveryAborts| ==>
      recoveryAborts[k].LogAbort? && recoveryAborts[k].tx !in FinishedTxs(flushedLog)
    ensures forall i, j :: 0 <= i < j < |recoveryAborts| ==>
      recoveryAborts[i].tx != recoveryAborts[j].tx
  {
    recoveredDisk := diskAfterRedo;
    recoveryAborts := [];
    var abortedSet: set<TxId> := {};

    var idx := |flushedLog|;
    while idx > 0
      invariant 0 <= idx <= |flushedLog|
      invariant recoveredDisk.Keys == diskAfterRedo.Keys
      invariant forall e :: e in diskAfterRedo.Keys && e !in ModifiedUndoRedoElements(flushedLog) ==>
        recoveredDisk[e] == diskAfterRedo[e]
      invariant forall k :: 0 <= k < |recoveryAborts| ==>
        recoveryAborts[k].LogAbort? &&
        recoveryAborts[k].tx !in finished &&
        recoveryAborts[k].tx in abortedSet
      invariant forall tx :: tx in abortedSet ==>
        exists k :: 0 <= k < |recoveryAborts| && recoveryAborts[k] == LogAbort(tx)
      invariant forall i, j :: 0 <= i < j < |recoveryAborts| ==>
        recoveryAborts[i].tx != recoveryAborts[j].tx
      decreases idx
    {
      idx := idx - 1;
      var rec := flushedLog[idx];
      match rec {
        case LogUndoRedoUpdate(tx, elem, oldVal, _) =>
          if tx !in committed && elem in recoveredDisk {
            assert elem in ModifiedUndoRedoElements(flushedLog);
            recoveredDisk := recoveredDisk[elem := oldVal];
          }
        case LogStart(tx) =>
          if tx !in finished && tx !in abortedSet {
            ghost var prevAborts := recoveryAborts;
            recoveryAborts := recoveryAborts + [LogAbort(tx)];
            abortedSet := abortedSet + {tx};
            forall t | t in abortedSet
              ensures exists k :: 0 <= k < |recoveryAborts| && recoveryAborts[k] == LogAbort(t)
            {
              if t == tx {
                assert recoveryAborts[|prevAborts|] == LogAbort(tx);
              } else {
                var k :| 0 <= k < |prevAborts| && prevAborts[k] == LogAbort(t);
                assert recoveryAborts[k] == LogAbort(t);
              }
            }
          }
        case LogCheckpoint => {
          // Quiescent checkpoint: all prior transactions finished before <CKPT>.
          break;
        }
        case LogEndCheckpoint => {
          // Non-quiescent checkpoint completion marker.
        }
        case LogStartCheckpoint(_) => {
          // Unlike Undo logging, in Undo/Redo logging <END CKPT> only means
          // dirty buffers were flushed, not that active transactions finished;
          // we continue scanning back to undo any incomplete active transaction.
        }
        case LogUndoUpdate(_, _, _) => {}
        case LogRedoUpdate(_, _, _) => {}
        case LogCommit(_) => {}
        case LogAbort(_) => {}
      }
    }
  }

  @AssumeCrossModuleTermination
  class UndoRedoRecoveryStrategy extends RecoveryStrategy {
    constructor () {}

    method RecoverFromCrash(diskAtCrash: DatabaseState, flushedLog: seq<LogRecord>)
      returns (recoveredDisk: DatabaseState, recoveryAborts: seq<LogRecord>)
      ensures recoveredDisk.Keys == diskAtCrash.Keys
      ensures forall e :: e in diskAtCrash.Keys && e !in ModifiedUndoRedoElements(flushedLog) ==>
        recoveredDisk[e] == diskAtCrash[e]
      ensures forall k :: 0 <= k < |recoveryAborts| ==>
        recoveryAborts[k].LogAbort? && recoveryAborts[k].tx !in FinishedTxs(flushedLog)
      ensures forall i, j :: 0 <= i < j < |recoveryAborts| ==>
        recoveryAborts[i].tx != recoveryAborts[j].tx
    {
      var committed := CommittedTxs(flushedLog);
      var finished := FinishedTxs(flushedLog);
      var afterRedo := RedoCommittedPass(diskAtCrash, flushedLog, committed);
      recoveredDisk, recoveryAborts := UndoUncommittedPass(afterRedo, flushedLog, committed, finished);
    }
  }

  // Convenience wrapper matching UndoRecovery.RecoverFromCrash and RedoRecovery.RecoverFromCrash.
  method RecoverFromCrash(diskAtCrash: DatabaseState, flushedLog: seq<LogRecord>)
    returns (recoveredDisk: DatabaseState, recoveryAborts: seq<LogRecord>)
    ensures recoveredDisk.Keys == diskAtCrash.Keys
    ensures forall e :: e in diskAtCrash.Keys && e !in ModifiedUndoRedoElements(flushedLog) ==>
      recoveredDisk[e] == diskAtCrash[e]
    ensures forall k :: 0 <= k < |recoveryAborts| ==>
      recoveryAborts[k].LogAbort? && recoveryAborts[k].tx !in FinishedTxs(flushedLog)
    ensures forall i, j :: 0 <= i < j < |recoveryAborts| ==>
      recoveryAborts[i].tx != recoveryAborts[j].tx
  {
    var strategy := new UndoRedoRecoveryStrategy();
    recoveredDisk, recoveryAborts := strategy.RecoverFromCrash(diskAtCrash, flushedLog);
  }
}
