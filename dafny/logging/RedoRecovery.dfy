// Redo Crash Recovery module implementing RecoveryStrategy, with support for
// quiescent (<CKPT>) and non-quiescent (<START CKPT(...)>, <END CKPT>)
// checkpoints.
//
// Given the on-disk database state at crash time and the flushed portion of a
// Redo log:
//   1. Locates the earliest point needed for replay (last quiescent <CKPT>,
//      or the <START CKPT(...)> matching the last <END CKPT>, or index 0).
//   2. Scans forward from that point, replaying <T, X, newVal> onto disk for
//      every committed transaction T.
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

  // Finds the starting index for Redo replay:
  //   - If a quiescent <CKPT> appears after the last completed non-quiescent
  //     checkpoint, starts right at that <CKPT>.
  //   - If an <END CKPT> has a matching earlier <START CKPT(...)>, starts at
  //     that <START CKPT(...)>.
  //   - Otherwise starts at 0.
  function FindCheckpointStartIndex(flushedLog: seq<LogRecord>, idx: nat, sawEndCkpt: bool): nat
    requires idx <= |flushedLog|
    ensures FindCheckpointStartIndex(flushedLog, idx, sawEndCkpt) <= |flushedLog|
    decreases idx
  {
    if idx == 0 then 0
    else
      var rec := flushedLog[idx - 1];
      if rec.LogCheckpoint? && !sawEndCkpt then idx - 1
      else if rec.LogEndCheckpoint? then FindCheckpointStartIndex(flushedLog, idx - 1, true)
      else if rec.LogStartCheckpoint? && sawEndCkpt then idx - 1
      else FindCheckpointStartIndex(flushedLog, idx - 1, sawEndCkpt)
  }

  function LastCompleteCheckpointIndex(flushedLog: seq<LogRecord>): nat
    ensures LastCompleteCheckpointIndex(flushedLog) <= |flushedLog|
  {
    FindCheckpointStartIndex(flushedLog, |flushedLog|, false)
  }

  // Pure specification of the forward Redo replay over a log slice.
  function ApplyRedoPass(
    disk: DatabaseState,
    logSlice: seq<LogRecord>,
    committed: set<TxId>
  ): DatabaseState
    decreases |logSlice|
  {
    if |logSlice| == 0 then disk
    else
      var prev := ApplyRedoPass(disk, logSlice[..|logSlice| - 1], committed);
      var last := logSlice[|logSlice| - 1];
      if last.LogRedoUpdate? && last.tx in committed && last.element in prev then
        prev[last.element := last.newValue]
      else
        prev
  }

  @AssumeCrossModuleTermination
  class RedoRecoveryStrategy extends RecoveryStrategy {
    constructor () {}

    // Performs checkpoint-aware Redo recovery by scanning forward from the last
    // completed checkpoint (or index 0 if none exists).
    method RecoverFromCrash(diskAtCrash: DatabaseState, flushedLog: seq<LogRecord>)
      returns (recoveredDisk: DatabaseState, recoveryAborts: seq<LogRecord>)
      ensures recoveredDisk.Keys == diskAtCrash.Keys
      ensures recoveredDisk == ApplyRedoPass(
        diskAtCrash,
        flushedLog[LastCompleteCheckpointIndex(flushedLog)..],
        CommittedTxs(flushedLog)
      )
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
      var startIdx := LastCompleteCheckpointIndex(flushedLog);
      var replaySlice := flushedLog[startIdx..];

      recoveredDisk := diskAtCrash;
      recoveryAborts := [];
      var abortedSet: set<TxId> := {};

      var idx := 0;
      while idx < |replaySlice|
        invariant 0 <= idx <= |replaySlice|
        invariant recoveredDisk.Keys == diskAtCrash.Keys
        invariant recoveredDisk == ApplyRedoPass(diskAtCrash, replaySlice[..idx], committed)
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
        decreases |replaySlice| - idx
      {
        var rec := replaySlice[idx];
        assert flushedLog[startIdx + idx] == rec;
        assert replaySlice[..idx + 1][..idx] == replaySlice[..idx];
        assert replaySlice[..idx + 1][idx] == rec;

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
          case LogStartCheckpoint(activeTxs) => {
            // Also record ABORT for any transaction that was active at <START CKPT>
            // and never finished before the crash.
            var j := 0;
            while j < |activeTxs|
              invariant 0 <= j <= |activeTxs|
              invariant forall k :: 0 <= k < |recoveryAborts| ==>
                recoveryAborts[k].LogAbort? &&
                recoveryAborts[k].tx !in finished &&
                recoveryAborts[k].tx in abortedSet
              invariant forall tx :: tx in abortedSet ==>
                exists k :: 0 <= k < |recoveryAborts| && recoveryAborts[k] == LogAbort(tx)
              invariant forall i, m :: 0 <= i < m < |recoveryAborts| ==>
                recoveryAborts[i].tx != recoveryAborts[m].tx
              decreases |activeTxs| - j
            {
              var tx := activeTxs[j];
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
              j := j + 1;
            }
          }
          case LogCheckpoint => {
            // Quiescent checkpoint marker; replay continues forward from here.
          }
          case LogEndCheckpoint => {
            // Non-quiescent checkpoint completion marker.
          }
          case LogUndoUpdate(_, _, _) => {
            // Redo recovery ignores Undo update records.
          }
          case LogUndoRedoUpdate(_, _, _, _) => {
            // Handled by UndoRedoRecoveryStrategy.
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

      assert replaySlice[..|replaySlice|] == replaySlice;
    }
  }

  // Convenience wrapper mirroring UndoRecovery.RecoverFromCrash.
  method RecoverFromCrash(diskAtCrash: DatabaseState, flushedLog: seq<LogRecord>)
    returns (recoveredDisk: DatabaseState, recoveryAborts: seq<LogRecord>)
    ensures recoveredDisk.Keys == diskAtCrash.Keys
    ensures recoveredDisk == ApplyRedoPass(
      diskAtCrash,
      flushedLog[LastCompleteCheckpointIndex(flushedLog)..],
      CommittedTxs(flushedLog)
    )
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
