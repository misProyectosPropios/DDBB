// Pure Redo Crash Recovery module implementing RecoveryStrategy.
//
// Given the on-disk database state at crash time and the flushed portion of a
// Redo log, scans the log forward from start to end:
//   1. Identifies committed transactions (those with <COMMIT T> in flushedLog).
//   2. For every <T, X, newVal> belonging to a committed transaction T,
//      redoes the write on disk: disk[X] := newVal.
//   3. Ignores uncommitted transactions during redo (Rule R1 guarantees none
//      of their updates ever reached disk) and emits <ABORT T> for every
//      incomplete transaction.

include "Types.dfy"
include "Dispatch.dfy"

module RedoRecovery {
  import opened LoggingTypes
  import opened LoggingDispatch

  // Elements modified by at least one committed transaction in the flushed log.
  ghost function CommittedModifiedElements(flushedLog: seq<LogRecord>): set<ElementId>
  {
    var committed := CommittedTxs(flushedLog);
    set i | 0 <= i < |flushedLog| &&
            flushedLog[i].LogRedoUpdate? &&
            flushedLog[i].tx in committed :: flushedLog[i].element
  }

  // Pure specification of the forward Redo replay over `flushedLog`.
  function ApplyRedoPass(
    disk: DatabaseState,
    flushedLog: seq<LogRecord>,
    committed: set<TxId>
  ): DatabaseState
    decreases |flushedLog|
  {
    if |flushedLog| == 0 then disk
    else
      var prev := ApplyRedoPass(disk, flushedLog[..|flushedLog| - 1], committed);
      var last := flushedLog[|flushedLog| - 1];
      if last.LogRedoUpdate? && last.tx in committed && last.element in prev then
        prev[last.element := last.newValue]
      else
        prev
  }

  @AssumeCrossModuleTermination
  class RedoRecoveryStrategy extends RecoveryStrategy {
    constructor () {}

    // Performs Redo recovery by scanning `flushedLog` forward from start to end.
    method RecoverFromCrash(diskAtCrash: DatabaseState, flushedLog: seq<LogRecord>)
      returns (recoveredDisk: DatabaseState, recoveryAborts: seq<LogRecord>)
      ensures recoveredDisk.Keys == diskAtCrash.Keys
      ensures recoveredDisk == ApplyRedoPass(diskAtCrash, flushedLog, CommittedTxs(flushedLog))
      // Any database element not modified by a committed transaction is untouched.
      ensures forall e :: e in diskAtCrash.Keys && e !in CommittedModifiedElements(flushedLog) ==>
                            recoveredDisk[e] == diskAtCrash[e]
      // Every emitted recovery record is an ABORT for an unfinished transaction.
      ensures forall k :: 0 <= k < |recoveryAborts| ==>
                            recoveryAborts[k].LogAbort? && recoveryAborts[k].tx !in FinishedTxs(flushedLog)
      // No duplicate ABORT records are emitted.
      ensures forall i, j :: 0 <= i < j < |recoveryAborts| ==>
                               recoveryAborts[i].tx != recoveryAborts[j].tx
    {
      var committed := CommittedTxs(flushedLog);
      var finished := FinishedTxs(flushedLog);
      recoveredDisk := diskAtCrash;
      recoveryAborts := [];
      var abortedSet: set<TxId> := {};

      var idx := 0;
      while idx < |flushedLog|
        invariant 0 <= idx <= |flushedLog|
        invariant recoveredDisk.Keys == diskAtCrash.Keys
        invariant recoveredDisk == ApplyRedoPass(diskAtCrash, flushedLog[..idx], committed)
        invariant forall e :: e in diskAtCrash.Keys && e !in CommittedModifiedElements(flushedLog) ==>
                                recoveredDisk[e] == diskAtCrash[e]
        invariant forall k :: 0 <= k < |recoveryAborts| ==>
                                recoveryAborts[k].LogAbort? &&
                                recoveryAborts[k].tx !in finished &&
                                recoveryAborts[k].tx in abortedSet
        invariant forall tx :: tx in abortedSet ==>
                                 exists k :: 0 <= k < |recoveryAborts| && recoveryAborts[k] == LogAbort(tx)
        invariant forall i, j :: 0 <= i < j < |recoveryAborts| ==>
                                   recoveryAborts[i].tx != recoveryAborts[j].tx
        decreases |flushedLog| - idx
      {
        var rec := flushedLog[idx];
        assert flushedLog[..idx + 1][..idx] == flushedLog[..idx];
        assert flushedLog[..idx + 1][idx] == rec;

        match rec {
          case LogRedoUpdate(tx, elem, newVal) =>
            if tx in committed && elem in recoveredDisk {
              assert elem in CommittedModifiedElements(flushedLog);
              recoveredDisk := recoveredDisk[elem := newVal];
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
          case LogUndoUpdate(_, _, _) => {
            // Redo recovery ignores Undo update records.
          }
          case LogCommit(_) => {
            // Committed transactions were collected up front in `committed`.
          }
          case LogAbort(_) => {
            // Aborted transactions were never written to disk under Rule R1.
          }
        }

        idx := idx + 1;
      }

      assert flushedLog[..|flushedLog|] == flushedLog;
    }
  }

  // Convenience wrapper mirroring UndoRecovery.RecoverFromCrash.
  method RecoverFromCrash(diskAtCrash: DatabaseState, flushedLog: seq<LogRecord>)
    returns (recoveredDisk: DatabaseState, recoveryAborts: seq<LogRecord>)
    ensures recoveredDisk.Keys == diskAtCrash.Keys
    ensures recoveredDisk == ApplyRedoPass(diskAtCrash, flushedLog, CommittedTxs(flushedLog))
    ensures forall e :: e in diskAtCrash.Keys && e !in CommittedModifiedElements(flushedLog) ==>
                          recoveredDisk[e] == diskAtCrash[e]
    ensures forall k :: 0 <= k < |recoveryAborts| ==>
                          recoveryAborts[k].LogAbort? && recoveryAborts[k].tx !in FinishedTxs(flushedLog)
    ensures forall i, j :: 0 <= i < j < |recoveryAborts| ==>
                             recoveryAborts[i].tx != recoveryAborts[j].tx
  {
    var strategy := new RedoRecoveryStrategy();
    recoveredDisk, recoveryAborts := strategy.RecoverFromCrash(diskAtCrash, flushedLog);
  }
}
