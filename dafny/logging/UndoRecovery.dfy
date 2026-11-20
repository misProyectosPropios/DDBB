// Pure Undo Crash Recovery module.
//
// Given the on-disk database state at crash time and the flushed portion of an
// Undo log, scans the log backwards:
//   1. Identifies finished transactions (those with <COMMIT T> or <ABORT T>).
//   2. For every <T, X, oldVal> belonging to an unfinished transaction T,
//      restores disk[X] := oldVal.
//   3. Emits <ABORT T> for every incomplete transaction that appeared in the
//      flushed log without a COMMIT or ABORT record.

include "Types.dfy"

module UndoRecovery {
  import opened LoggingTypes

  function FinishedTxs(flushedLog: seq<LogRecord>): set<TxId>
  {
    set i | 0 <= i < |flushedLog| && (flushedLog[i].LogCommit? || flushedLog[i].LogAbort?) :: flushedLog[i].tx
  }

  function StartedTxs(flushedLog: seq<LogRecord>): set<TxId>
  {
    set i | 0 <= i < |flushedLog| && flushedLog[i].LogStart? :: flushedLog[i].tx
  }

  function IncompleteTxs(flushedLog: seq<LogRecord>): set<TxId>
  {
    StartedTxs(flushedLog) - FinishedTxs(flushedLog)
  }

  // Elements touched by at least one unfinished transaction in the flushed log.
  ghost function UnfinishedModifiedElements(flushedLog: seq<LogRecord>): set<ElementId>
  {
    var finished := FinishedTxs(flushedLog);
    set i | 0 <= i < |flushedLog| &&
            flushedLog[i].LogUndoUpdate? &&
            flushedLog[i].tx !in finished :: flushedLog[i].element
  }

  // Performs Undo recovery by scanning `flushedLog` from end to start.
  method RecoverFromCrash(diskAtCrash: DatabaseState, flushedLog: seq<LogRecord>)
    returns (recoveredDisk: DatabaseState, recoveryAborts: seq<LogRecord>)
    ensures recoveredDisk.Keys == diskAtCrash.Keys
    // Any database element not modified by an unfinished transaction is untouched.
    ensures forall e :: e in diskAtCrash.Keys && e !in UnfinishedModifiedElements(flushedLog) ==>
      recoveredDisk[e] == diskAtCrash[e]
    // Every emitted recovery record is an ABORT for an unfinished transaction.
    ensures forall k :: 0 <= k < |recoveryAborts| ==>
      recoveryAborts[k].LogAbort? && recoveryAborts[k].tx !in FinishedTxs(flushedLog)
    // No duplicate ABORT records are emitted.
    ensures forall i, j :: 0 <= i < j < |recoveryAborts| ==>
      recoveryAborts[i].tx != recoveryAborts[j].tx
  {
    var finished := FinishedTxs(flushedLog);
    recoveredDisk := diskAtCrash;
    recoveryAborts := [];
    var abortedSet: set<TxId> := {};

    var idx := |flushedLog|;
    while idx > 0
      invariant 0 <= idx <= |flushedLog|
      invariant recoveredDisk.Keys == diskAtCrash.Keys
      invariant forall e :: e in diskAtCrash.Keys && e !in UnfinishedModifiedElements(flushedLog) ==>
        recoveredDisk[e] == diskAtCrash[e]
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
        case LogUndoUpdate(tx, elem, oldVal) =>
          if tx !in finished && elem in recoveredDisk {
            assert elem in UnfinishedModifiedElements(flushedLog);
            recoveredDisk := recoveredDisk[elem := oldVal];
          }
        case LogStart(tx) =>
          if tx !in finished && tx !in abortedSet {
            recoveryAborts := recoveryAborts + [LogAbort(tx)];
            abortedSet := abortedSet + {tx};
          }
        case LogCommit(_) => {
          // Already committed; Rule U2 guarantees its writes are on disk.
        }
        case LogAbort(_) => {
          // Already aborted.
        }
      }
    }
  }
}
