// Undo/Redo Logging implementation extending LoggingStrategy and composing a
// CheckpointStrategy (None, Quiescent, or Non-Quiescent).
//
// Enforces and formally proves Garcia-Molina's Undo/Redo Logging Rule UR1:
//   - Every write emits a 4-tuple update record <T, X, oldVal, newVal>.
//   - Rule UR1 (Write-Ahead Logging): Before any modified database element X is
//     written to disk (OUTPUT), the log record <T, X, oldVal, newVal> must
//     already be flushed to disk (FLUSH LOG).
//   - STEAL / NO-FORCE flexibility: dirty buffer elements may be flushed to
//     disk either before <COMMIT T> (e.g., during a checkpoint) or after
//     <COMMIT T>.

include "Types.dfy"
include "Checkpointing.dfy"
include "Dispatch.dfy"

module UndoRedoLogging {
  import opened LoggingTypes
  import opened Checkpointing
  import opened LoggingDispatch

  @AssumeCrossModuleTermination
  class UndoRedoLogger extends LoggingStrategy {
    const checkpointStrategy: CheckpointStrategy

    var disk: DatabaseState
    var buffer: DatabaseState
    var flushedLogLen: nat
    var activeTxs: set<TxId>
    var activeOrder: seq<TxId>
    var committedTxs: set<TxId>
    var abortedTxs: set<TxId>
    var dirtyElements: map<TxId, seq<ElementId>>
    var ckptState: CheckpointState

    ghost predicate Valid()
      reads this
    {
      // 1. Disjoint transaction states
      activeTxs !! committedTxs &&
      activeTxs !! abortedTxs &&
      committedTxs !! abortedTxs &&
      (forall tx :: tx in activeOrder <==> tx in activeTxs) &&

      // 2. Consistent database element universe between memory buffer and disk
      disk.Keys == buffer.Keys &&

      // 3. Dirty-element tracking for active transactions
      dirtyElements.Keys == activeTxs &&
      (forall tx :: tx in activeTxs ==>
        forall e :: e in dirtyElements[tx] ==> e in buffer.Keys) &&

      // 4. Flushed log boundary and trace-to-log correspondence
      flushedLogLen <= |log| &&
      ExtractLog(trace) == log &&
      LastFlushedCount(trace) == flushedLogLen &&

      // 5. Log-transaction and checkpoint lifecycle consistency
      (forall i :: 0 <= i < |log| && IsTxRecord(log[i]) ==>
        log[i].tx in activeTxs + committedTxs + abortedTxs) &&
      (forall i :: 0 <= i < |log| && log[i].LogUndoRedoUpdate? ==>
        log[i].element in buffer.Keys) &&
      (forall tx :: tx in activeTxs ==>
        HasStart(log, tx) && !HasCommit(log, tx) && !HasAbort(log, tx)) &&
      (forall tx :: tx in committedTxs ==>
        HasStart(log, tx) && HasCommit(log, tx) && !HasAbort(log, tx)) &&
      (forall tx :: tx in abortedTxs ==>
        HasStart(log, tx) && !HasCommit(log, tx) && HasAbort(log, tx)) &&
      StartBeforeEnd(log) &&
      EndCheckpointHasStartBefore(log) &&
      ValidCheckpointState(ckptState, activeTxs, log) &&

      // 6. Undo/Redo Logging correctness rules (Rule UR1: WAL before OUTPUT)
      WriteHasUndoRedoLogBefore(trace) &&
      RuleUR1_FlushBeforeOutput(trace)
    }

    constructor (initialDb: DatabaseState, strategy: CheckpointStrategy)
      ensures Valid()
      ensures checkpointStrategy == strategy
      ensures log == []
      ensures trace == []
      ensures errors == []
      ensures disk == initialDb
      ensures buffer == initialDb
      ensures flushedLogLen == 0
      ensures activeTxs == {}
      ensures activeOrder == []
      ensures committedTxs == {}
      ensures abortedTxs == {}
      ensures ckptState == CkptIdle
    {
      this.checkpointStrategy := strategy;
      this.log := [];
      this.trace := [];
      this.errors := [];
      this.disk := initialDb;
      this.buffer := initialDb;
      this.flushedLogLen := 0;
      this.activeTxs := {};
      this.activeOrder := [];
      this.committedTxs := {};
      this.abortedTxs := {};
      this.dirtyElements := map[];
      this.ckptState := CkptIdle;
    }

    // -------------------------------------------------------------------------
    // Visitor methods (invoked via Operation.Accept)
    // -------------------------------------------------------------------------

    method VisitStart(tx: TxId)
      requires Valid()
      modifies this
      ensures Valid()
      ensures old(log) <= log
      ensures old(trace) <= trace
      ensures (old(ckptState.CkptIdle?) &&
               old(tx !in (activeTxs + committedTxs + abortedTxs))) ==>
        log == old(log) + [LogStart(tx)] &&
        activeTxs == old(activeTxs) + {tx} &&
        committedTxs == old(committedTxs) &&
        abortedTxs == old(abortedTxs) &&
        buffer == old(buffer) &&
        disk == old(disk) &&
        flushedLogLen == old(flushedLogLen) &&
        ckptState == old(ckptState) &&
        errors == old(errors)
    {
      if !checkpointStrategy.CanStartTransaction(ckptState) {
        errors := errors + [checkpointStrategy.BlockedStartMessage(tx)];
        return;
      }
      if tx in activeTxs || tx in committedTxs || tx in abortedTxs {
        errors := errors + ["Cannot START " + tx + ": transaction was already started."];
        return;
      }

      var rec := LogStart(tx);
      var ev := EventLog(rec);
      ghost var prevLog := log;
      ghost var prevTrace := trace;

      LemmaAppendLogPreservesLifecycle(prevLog, rec);
      LemmaAppendNonWritePreservesUndoRedoTrace(prevTrace, ev);

      log := log + [rec];
      trace := trace + [ev];
      activeTxs := activeTxs + {tx};
      activeOrder := activeOrder + [tx];
      dirtyElements := dirtyElements[tx := []];

      assert log[|prevLog|] == LogStart(tx);
    }

    method VisitRead(tx: TxId, element: ElementId)
      requires Valid()
      modifies this
      ensures Valid()
      ensures old(log) <= log
      ensures old(trace) <= trace
      ensures log == old(log)
      ensures buffer == old(buffer)
      ensures disk == old(disk)
      ensures activeTxs == old(activeTxs)
      ensures committedTxs == old(committedTxs)
      ensures abortedTxs == old(abortedTxs)
      ensures flushedLogLen == old(flushedLogLen)
      ensures ckptState == old(ckptState)
      ensures (old(tx in activeTxs) && old(element in buffer)) ==>
        errors == old(errors)
    {
      if tx !in activeTxs {
        errors := errors + ["Cannot READ in " + tx + ": transaction is not active."];
        return;
      }
      if element !in buffer {
        errors := errors + ["Cannot READ " + element + " in " + tx + ": unknown database element."];
        return;
      }

      var val := buffer[element];
      var ev := EventRead(tx, element, val);
      ghost var prevTrace := trace;
      LemmaAppendNonWritePreservesUndoRedoTrace(prevTrace, ev);
      trace := trace + [ev];
    }

    method VisitWrite(tx: TxId, element: ElementId, newValue: Value)
      requires Valid()
      modifies this
      ensures Valid()
      ensures old(log) <= log
      ensures old(trace) <= trace
      ensures (old(tx in activeTxs) && old(element in buffer)) ==>
        log == old(log) + [LogUndoRedoUpdate(tx, element, old(buffer[element]), newValue)] &&
        buffer == old(buffer)[element := newValue] &&
        disk == old(disk) &&
        activeTxs == old(activeTxs) &&
        committedTxs == old(committedTxs) &&
        abortedTxs == old(abortedTxs) &&
        flushedLogLen == old(flushedLogLen) &&
        ckptState == old(ckptState) &&
        errors == old(errors)
    {
      if tx !in activeTxs {
        errors := errors + ["Cannot WRITE in " + tx + ": transaction is not active."];
        return;
      }
      if element !in buffer {
        errors := errors + ["Cannot WRITE " + element + " in " + tx + ": unknown database element."];
        return;
      }

      var oldVal := buffer[element];
      var rec := LogUndoRedoUpdate(tx, element, oldVal, newValue);

      ghost var prevLog := log;
      ghost var t0 := trace;
      LemmaAppendLogPreservesLifecycle(prevLog, rec);
      LemmaAppendNonWritePreservesUndoRedoTrace(t0, EventLog(rec));
      log := log + [rec];
      trace := trace + [EventLog(rec)];

      var writeEv := EventWriteBuffer(tx, element, oldVal, newValue);
      ghost var t1 := trace;
      LemmaAppendPreservesRuleU1(t1, writeEv);
      buffer := buffer[element := newValue];
      trace := trace + [writeEv];
      assert trace[..|t1|] == t1;
      assert t0 <= t1 && t1 <= trace;

      var curDirty := dirtyElements[tx];
      if element !in curDirty {
        dirtyElements := dirtyElements[tx := curDirty + [element]];
      }
    }

    // -------------------------------------------------------------------------
    // Modular Checkpointing & Buffer Flushing Helpers
    // -------------------------------------------------------------------------

    // Rule UR1 (WAL): flush all pending log records to disk before any OUTPUT.
    method FlushLogIfNeeded()
      requires Valid()
      modifies this
      ensures Valid()
      ensures old(trace) <= trace
      ensures flushedLogLen == |log|
      ensures log == old(log)
      ensures buffer == old(buffer)
      ensures disk == old(disk)
      ensures activeTxs == old(activeTxs)
      ensures activeOrder == old(activeOrder)
      ensures committedTxs == old(committedTxs)
      ensures abortedTxs == old(abortedTxs)
      ensures dirtyElements == old(dirtyElements)
      ensures ckptState == old(ckptState)
      ensures errors == old(errors)
    {
      if flushedLogLen < |log| {
        var flushEv := EventFlushLog(|log|);
        ghost var prevTrace := trace;
        LemmaAppendNonWritePreservesUndoRedoTrace(prevTrace, flushEv);
        flushedLogLen := |log|;
        trace := trace + [flushEv];
      }
    }

    // Writes a list of dirty elements from memory buffer to disk (requires the
    // log to be flushed first under Rule UR1).
    method OutputDirtyList(dirty: seq<ElementId>)
      requires Valid()
      requires forall e :: e in dirty ==> e in buffer.Keys
      requires flushedLogLen == |log|
      modifies this
      ensures Valid()
      ensures old(trace) <= trace
      ensures log == old(log)
      ensures flushedLogLen == |log|
      ensures buffer == old(buffer)
      ensures activeTxs == old(activeTxs)
      ensures activeOrder == old(activeOrder)
      ensures committedTxs == old(committedTxs)
      ensures abortedTxs == old(abortedTxs)
      ensures dirtyElements == old(dirtyElements)
      ensures ckptState == old(ckptState)
      ensures errors == old(errors)
    {
      ghost var preTrace := trace;
      var k := 0;
      while k < |dirty|
        invariant 0 <= k <= |dirty|
        invariant Valid()
        invariant preTrace <= trace
        invariant log == old(log)
        invariant flushedLogLen == |log|
        invariant buffer == old(buffer)
        invariant activeTxs == old(activeTxs)
        invariant activeOrder == old(activeOrder)
        invariant committedTxs == old(committedTxs)
        invariant abortedTxs == old(abortedTxs)
        invariant dirtyElements == old(dirtyElements)
        invariant ckptState == old(ckptState)
        invariant errors == old(errors)
        decreases |dirty| - k
      {
        var elem := dirty[k];
        var val := buffer[elem];
        var outEv := EventOutput(elem, val);
        disk := disk[elem := val];

        ghost var prevTrace := trace;
        LemmaAppendNonWritePreservesUndoRedoTrace(prevTrace, outEv);
        trace := trace + [outEv];
        assert preTrace <= prevTrace && prevTrace <= trace;

        k := k + 1;
      }
    }

    // Flushes dirty buffers of all currently active transactions to disk during
    // an Undo/Redo checkpoint (Garcia-Molina 17.4.2: flush log, then flush dirty
    // buffer pages to disk before writing <END CKPT>).
    method FlushAllActiveDirtyBuffers()
      requires Valid()
      requires flushedLogLen == |log|
      modifies this
      ensures Valid()
      ensures old(trace) <= trace
      ensures log == old(log)
      ensures flushedLogLen == |log|
      ensures buffer == old(buffer)
      ensures activeTxs == old(activeTxs)
      ensures activeOrder == old(activeOrder)
      ensures committedTxs == old(committedTxs)
      ensures abortedTxs == old(abortedTxs)
      ensures dirtyElements == old(dirtyElements)
      ensures ckptState == old(ckptState)
      ensures errors == old(errors)
    {
      ghost var preTrace := trace;
      var i := 0;
      while i < |activeOrder|
        invariant 0 <= i <= |activeOrder|
        invariant Valid()
        invariant preTrace <= trace
        invariant log == old(log)
        invariant flushedLogLen == |log|
        invariant buffer == old(buffer)
        invariant activeTxs == old(activeTxs)
        invariant activeOrder == old(activeOrder)
        invariant committedTxs == old(committedTxs)
        invariant abortedTxs == old(abortedTxs)
        invariant dirtyElements == old(dirtyElements)
        invariant ckptState == old(ckptState)
        invariant errors == old(errors)
        decreases |activeOrder| - i
      {
        var tx := activeOrder[i];
        assert tx in activeTxs;
        ghost var prevTrace := trace;
        OutputDirtyList(dirtyElements[tx]);
        assert preTrace <= prevTrace && prevTrace <= trace;
        i := i + 1;
      }
    }

    method EmitSingleCheckpointRecord(rec: LogRecord)
      requires Valid()
      requires IsCheckpointRecord(rec)
      requires rec.LogEndCheckpoint? ==> HasStartCheckpoint(log)
      modifies this
      ensures Valid()
      ensures old(log) <= log
      ensures old(trace) <= trace
      ensures log == old(log) + [rec]
      ensures HasStartCheckpoint(old(log)) ==> HasStartCheckpoint(log)
      ensures rec.LogStartCheckpoint? ==> HasStartCheckpoint(log)
      ensures flushedLogLen == old(flushedLogLen)
      ensures buffer == old(buffer)
      ensures disk == old(disk)
      ensures activeTxs == old(activeTxs)
      ensures activeOrder == old(activeOrder)
      ensures committedTxs == old(committedTxs)
      ensures abortedTxs == old(abortedTxs)
      ensures dirtyElements == old(dirtyElements)
      ensures ckptState == old(ckptState)
      ensures errors == old(errors)
    {
      var ev := EventLog(rec);
      ghost var prevLog := log;
      ghost var prevTrace := trace;
      LemmaAppendLogPreservesLifecycle(prevLog, rec);
      LemmaAppendNonWritePreservesUndoRedoTrace(prevTrace, ev);
      log := log + [rec];
      trace := trace + [ev];
    }

    method ApplyCheckpointTransition(
      prevState: CheckpointState,
      nextState: CheckpointState,
      recs: seq<LogRecord>
    )
      requires Valid()
      requires ckptState == CkptIdle
      requires prevState.CkptActiveNonQuiescent? ==> HasStartCheckpoint(log)
      requires ValidCheckpointEmission(recs, prevState.CkptActiveNonQuiescent?)
      requires nextState.CkptDrainingQuiescent? ==> activeTxs != {}
      requires nextState.CkptActiveNonQuiescent? ==>
        nextState.watchedTxs <= activeTxs &&
        nextState.watchedTxs != {} &&
        (prevState.CkptActiveNonQuiescent? || HasStartCheckpointIn(recs))
      modifies this
      ensures Valid()
      ensures old(log) <= log
      ensures old(trace) <= trace
      ensures log == old(log) + recs
      ensures |recs| > 0 ==> flushedLogLen == |log|
      ensures |recs| == 0 ==> flushedLogLen == old(flushedLogLen)
      ensures ckptState == nextState
      ensures buffer == old(buffer)
      ensures disk == old(disk)
      ensures activeTxs == old(activeTxs)
      ensures activeOrder == old(activeOrder)
      ensures committedTxs == old(committedTxs)
      ensures abortedTxs == old(abortedTxs)
      ensures dirtyElements == old(dirtyElements)
      ensures errors == old(errors)
    {
      ghost var initLog := log;
      ghost var initTrace := trace;
      var k := 0;
      while k < |recs|
        invariant 0 <= k <= |recs|
        invariant Valid()
        invariant ckptState == CkptIdle
        invariant log == initLog + recs[..k]
        invariant initLog <= log
        invariant initTrace <= trace
        invariant flushedLogLen == old(flushedLogLen)
        invariant buffer == old(buffer)
        invariant disk == old(disk)
        invariant activeTxs == old(activeTxs)
        invariant activeOrder == old(activeOrder)
        invariant committedTxs == old(committedTxs)
        invariant abortedTxs == old(abortedTxs)
        invariant dirtyElements == old(dirtyElements)
        invariant errors == old(errors)
        invariant prevState.CkptActiveNonQuiescent? ==> HasStartCheckpoint(log)
        invariant forall s :: 0 <= s < k && recs[s].LogStartCheckpoint? ==> HasStartCheckpoint(log)
        decreases |recs| - k
      {
        ghost var prevTrace := trace;
        EmitSingleCheckpointRecord(recs[k]);
        assert recs[..k + 1] == recs[..k] + [recs[k]];
        assert initTrace <= prevTrace && prevTrace <= trace;
        k := k + 1;
      }

      assert recs[..|recs|] == recs;

      if |recs| > 0 {
        ghost var preFlushTrace := trace;
        FlushLogIfNeeded();
        assert initTrace <= preFlushTrace && preFlushTrace <= trace;
      }

      ckptState := nextState;
    }

    method VisitCheckpoint()
      requires Valid()
      modifies this
      ensures Valid()
      ensures old(log) <= log
      ensures old(trace) <= trace
    {
      // Undo/Redo non-quiescent checkpointing flushes the WAL, writes dirty
      // buffers to disk, and emits <START CKPT(...)> + <END CKPT> immediately.
      var res := checkpointStrategy.OnCheckpointRequested(
        ckptState, activeTxs, activeOrder, false
      );
      var nextState := res.0;
      var recs := res.1;
      var err := res.2;
      if err != "" {
        errors := errors + [err];
        return;
      }

      ghost var t0 := trace;
      FlushLogIfNeeded();
      ghost var t1 := trace;
      FlushAllActiveDirtyBuffers();
      ghost var t2 := trace;
      assert t0 <= t1 && t1 <= t2;

      var prevState := ckptState;
      ckptState := CkptIdle;
      ApplyCheckpointTransition(prevState, nextState, recs);
      assert t2 <= trace;
    }

    // -------------------------------------------------------------------------
    // Modular Commit & Abort helpers
    // -------------------------------------------------------------------------

    method EmitCommitAndFinalize(tx: TxId)
      returns (prevCkpt: CheckpointState, dirty: seq<ElementId>)
      requires Valid()
      requires tx in activeTxs
      modifies this
      ensures Valid()
      ensures old(log) <= log
      ensures old(trace) <= trace
      ensures log == old(log) + [LogCommit(tx)]
      ensures flushedLogLen == |log|
      ensures tx in committedTxs
      ensures tx !in activeTxs
      ensures forall e :: e in dirty ==> e in buffer.Keys
      ensures errors == old(errors)
      ensures ckptState == CkptIdle
      ensures prevCkpt == old(ckptState)
      ensures prevCkpt.CkptActiveNonQuiescent? ==>
        prevCkpt.watchedTxs <= activeTxs + {tx} && HasStartCheckpoint(log)
    {
      prevCkpt := ckptState;
      dirty := dirtyElements[tx];
      ghost var initTrace := trace;
      ghost var prevLog := log;
      ghost var oldLogLen := |log|;
      var commitRec := LogCommit(tx);
      var commitEv := EventLog(commitRec);

      LemmaAppendLogPreservesLifecycle(prevLog, commitRec);
      LemmaAppendNonWritePreservesUndoRedoTrace(initTrace, commitEv);

      log := log + [commitRec];
      trace := trace + [commitEv];
      assert log[oldLogLen] == LogCommit(tx);
      assert HasCommit(log, tx);

      var finalFlushEv := EventFlushLog(|log|);
      ghost var tBeforeFlush := trace;
      LemmaAppendNonWritePreservesUndoRedoTrace(tBeforeFlush, finalFlushEv);

      flushedLogLen := |log|;
      trace := trace + [finalFlushEv];
      assert initTrace <= tBeforeFlush && tBeforeFlush <= trace;

      LemmaRemoveTxMembership(activeOrder, tx);
      activeTxs := activeTxs - {tx};
      activeOrder := RemoveTx(activeOrder, tx);
      committedTxs := committedTxs + {tx};
      dirtyElements := dirtyElements - {tx};
      ckptState := CkptIdle;
    }

    method VisitCommit(tx: TxId)
      requires Valid()
      modifies this
      ensures Valid()
      ensures old(log) <= log
      ensures old(trace) <= trace
      ensures old(tx in activeTxs) ==>
        old(log) + [LogCommit(tx)] <= log &&
        flushedLogLen == |log| &&
        tx in committedTxs &&
        tx !in activeTxs &&
        errors == old(errors)
      ensures (old(tx in activeTxs) && old(ckptState == CkptIdle)) ==>
        log == old(log) + [LogCommit(tx)]
    {
      if tx !in activeTxs {
        errors := errors + ["Cannot COMMIT " + tx + ": transaction is not active."];
        return;
      }

      var prevCkpt, dirty := EmitCommitAndFinalize(tx);
      OutputDirtyList(dirty);
      var res := checkpointStrategy.OnTransactionFinished(prevCkpt, tx, activeTxs);
      ApplyCheckpointTransition(prevCkpt, res.0, res.1);
    }

    // Rolls back `tx`'s buffer modifications in reverse log order using the
    // `oldValue` component of each <tx, elem, oldVal, newVal> record.
    method RollbackTxBuffer(tx: TxId)
      requires Valid()
      requires tx in activeTxs
      modifies this
      ensures Valid()
      ensures old(trace) <= trace
      ensures log == old(log)
      ensures flushedLogLen == old(flushedLogLen)
      ensures disk == old(disk)
      ensures activeTxs == old(activeTxs)
      ensures activeOrder == old(activeOrder)
      ensures committedTxs == old(committedTxs)
      ensures abortedTxs == old(abortedTxs)
      ensures dirtyElements == old(dirtyElements)
      ensures ckptState == old(ckptState)
      ensures errors == old(errors)
    {
      ghost var preTrace := trace;
      var idx := |log|;
      while idx > 0
        invariant 0 <= idx <= |log|
        invariant Valid()
        invariant preTrace <= trace
        invariant log == old(log)
        invariant flushedLogLen == old(flushedLogLen)
        invariant disk == old(disk)
        invariant activeTxs == old(activeTxs)
        invariant activeOrder == old(activeOrder)
        invariant committedTxs == old(committedTxs)
        invariant abortedTxs == old(abortedTxs)
        invariant dirtyElements == old(dirtyElements)
        invariant ckptState == old(ckptState)
        invariant errors == old(errors)
        decreases idx
      {
        idx := idx - 1;
        if log[idx].LogUndoRedoUpdate? && log[idx].tx == tx {
          var elem := log[idx].element;
          var oldVal := log[idx].oldValue;
          var undoEv := EventUndoRestore(tx, elem, oldVal);
          buffer := buffer[elem := oldVal];

          ghost var prevTrace := trace;
          LemmaAppendNonWritePreservesUndoRedoTrace(prevTrace, undoEv);
          trace := trace + [undoEv];
          assert preTrace <= prevTrace && prevTrace <= trace;
        }
      }
    }

    method EmitAbortAndFinalize(tx: TxId) returns (prevCkpt: CheckpointState)
      requires Valid()
      requires tx in activeTxs
      modifies this
      ensures Valid()
      ensures old(log) <= log
      ensures old(trace) <= trace
      ensures log == old(log) + [LogAbort(tx)]
      ensures flushedLogLen == |log|
      ensures tx in abortedTxs
      ensures tx !in activeTxs
      ensures errors == old(errors)
      ensures ckptState == CkptIdle
      ensures prevCkpt == old(ckptState)
      ensures prevCkpt.CkptActiveNonQuiescent? ==>
        prevCkpt.watchedTxs <= activeTxs + {tx} && HasStartCheckpoint(log)
    {
      prevCkpt := ckptState;
      ghost var initTrace := trace;
      ghost var prevLog := log;
      ghost var oldLogLen := |log|;
      var abortRec := LogAbort(tx);
      var abortEv := EventLog(abortRec);

      LemmaAppendLogPreservesLifecycle(prevLog, abortRec);
      LemmaAppendNonWritePreservesUndoRedoTrace(initTrace, abortEv);

      log := log + [abortRec];
      trace := trace + [abortEv];
      assert log[oldLogLen] == LogAbort(tx);
      assert HasAbort(log, tx);

      var flushEv := EventFlushLog(|log|);
      ghost var tBeforeFlush := trace;
      LemmaAppendNonWritePreservesUndoRedoTrace(tBeforeFlush, flushEv);

      flushedLogLen := |log|;
      trace := trace + [flushEv];
      assert initTrace <= tBeforeFlush && tBeforeFlush <= trace;

      LemmaRemoveTxMembership(activeOrder, tx);
      activeTxs := activeTxs - {tx};
      activeOrder := RemoveTx(activeOrder, tx);
      abortedTxs := abortedTxs + {tx};
      dirtyElements := dirtyElements - {tx};
      ckptState := CkptIdle;
    }

    method VisitAbort(tx: TxId)
      requires Valid()
      modifies this
      ensures Valid()
      ensures old(log) <= log
      ensures old(trace) <= trace
      ensures old(tx in activeTxs) ==>
        old(log) + [LogAbort(tx)] <= log &&
        flushedLogLen == |log| &&
        tx in abortedTxs &&
        tx !in activeTxs &&
        errors == old(errors)
    {
      if tx !in activeTxs {
        errors := errors + ["Cannot ABORT " + tx + ": transaction is not active."];
        return;
      }

      RollbackTxBuffer(tx);
      var prevCkpt := EmitAbortAndFinalize(tx);

      var res := checkpointStrategy.OnTransactionFinished(prevCkpt, tx, activeTxs);
      ApplyCheckpointTransition(prevCkpt, res.0, res.1);
    }

    // -------------------------------------------------------------------------
    // State inspection accessors
    // -------------------------------------------------------------------------

    function GetFlushedLog(): seq<LogRecord>
      requires Valid()
      reads this
    {
      log[..flushedLogLen]
    }

    function GetDisk(): DatabaseState
      reads this
    {
      disk
    }

    function GetBuffer(): DatabaseState
      reads this
    {
      buffer
    }

    function GetActiveTxs(): set<TxId>
      reads this
    {
      activeTxs
    }

    function GetCommittedTxs(): set<TxId>
      reads this
    {
      committedTxs
    }

    function GetAbortedTxs(): set<TxId>
      reads this
    {
      abortedTxs
    }

    function GetCheckpointState(): CheckpointState
      reads this
    {
      ckptState
    }
  }

  // Convenience entry point: given an initial database state, a checkpoint
  // strategy, and a Schedule, runs Undo/Redo logging via dispatch.
  method GenerateUndoRedoLog(
    initialDb: DatabaseState,
    checkpointStrategy: CheckpointStrategy,
    schedule: Schedule
  )
    returns (logResult: seq<LogRecord>, traceResult: seq<TraceEvent>, errorResult: seq<string>)
  {
    var logger := new UndoRedoLogger(initialDb, checkpointStrategy);
    logResult, traceResult, errorResult := schedule.Run(logger);
  }
}
