// Undo Logging implementation extending LoggingStrategy and composing a
// CheckpointStrategy (None, Quiescent, or Non-Quiescent).
//
// Enforces and formally proves Garcia-Molina's Undo Logging rules:
//   - Rule U1 (Write-Ahead Logging): all log records are flushed to disk before
//     any modified database element is written to disk (OUTPUT).
//   - Rule U2 (Output Before Commit): every element modified by a transaction T
//     is OUTPUT to disk before <COMMIT T> is written to the log and flushed.
//   - Checkpoint correctness: every <END CKPT> is preceded by <START CKPT(...)>,
//     and checkpoint transitions follow the composed CheckpointStrategy.

include "Types.dfy"
include "Checkpointing.dfy"
include "Dispatch.dfy"

module UndoLogging {
  import opened LoggingTypes
  import opened Checkpointing
  import opened LoggingDispatch

  @AssumeCrossModuleTermination
  class UndoLogger extends LoggingStrategy {
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
      (forall i :: 0 <= i < |log| && log[i].LogUndoUpdate? ==>
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

      // 6. Undo Logging correctness rules (WAL + Output Before Commit)
      WriteHasUndoLogBefore(trace) &&
      RuleU1_FlushBeforeOutput(trace) &&
      RuleU2_OutputBeforeCommit(trace) &&

      // 7. Every in-memory write by an active transaction is tracked as dirty
      (forall tx :: tx in activeTxs ==>
        forall j :: 0 <= j < |trace| && trace[j].EventWriteBuffer? && trace[j].tx == tx ==>
          trace[j].element in dirtyElements[tx])
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
      ghost var prevLog := log;
      ghost var prevTrace := trace;

      LemmaAppendLogPreservesLifecycle(prevLog, rec);
      LemmaAppendPreservesRuleU1(prevTrace, EventLog(rec));
      LemmaAppendNonCommitPreservesRuleU2(prevTrace, EventLog(rec));

      log := log + [rec];
      trace := trace + [EventLog(rec)];
      activeTxs := activeTxs + {tx};
      activeOrder := activeOrder + [tx];
      dirtyElements := dirtyElements[tx := []];

      assert trace[..|prevTrace|] == prevTrace;
      assert log[|prevLog|] == LogStart(tx);

      // Show no prior WriteBuffer events exist for the brand-new transaction.
      forall j | 0 <= j < |trace| && trace[j].EventWriteBuffer? && trace[j].tx == tx
        ensures trace[j].element in dirtyElements[tx]
      {
        assert j < |prevTrace|;
        assert prevTrace[j] == trace[j];
        assert j > 0;
        assert prevTrace[j - 1].EventLog?;
        assert prevTrace[j - 1].record.LogUndoUpdate?;
        assert prevTrace[j - 1].record.tx == tx;
        LemmaEventLogInExtractLog(prevTrace, j - 1);
        var idx :| 0 <= idx < |prevLog| && prevLog[idx] == prevTrace[j - 1].record;
        assert IsTxRecord(prevLog[idx]) && prevLog[idx].tx == tx;
      }
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
      LemmaAppendPreservesRuleU1(prevTrace, ev);
      LemmaAppendNonCommitPreservesRuleU2(prevTrace, ev);
      trace := trace + [ev];
      assert trace[..|prevTrace|] == prevTrace;
    }

    method VisitWrite(tx: TxId, element: ElementId, newValue: Value)
      requires Valid()
      modifies this
      ensures Valid()
      ensures old(log) <= log
      ensures old(trace) <= trace
      ensures (old(tx in activeTxs) && old(element in buffer)) ==>
        log == old(log) + [LogUndoUpdate(tx, element, old(buffer[element]))] &&
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
      var rec := LogUndoUpdate(tx, element, oldVal);

      ghost var prevLog := log;
      ghost var t0 := trace;
      LemmaAppendLogPreservesLifecycle(prevLog, rec);
      LemmaAppendPreservesRuleU1(t0, EventLog(rec));
      LemmaAppendNonCommitPreservesRuleU2(t0, EventLog(rec));
      log := log + [rec];
      trace := trace + [EventLog(rec)];
      assert trace[..|t0|] == t0;

      var writeEv := EventWriteBuffer(tx, element, oldVal, newValue);
      ghost var t1 := trace;
      LemmaAppendPreservesRuleU1(t1, writeEv);
      LemmaAppendNonCommitPreservesRuleU2(t1, writeEv);
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
    // Modular Checkpointing helpers
    // -------------------------------------------------------------------------

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
      LemmaAppendNonWritePreservesTrace(prevTrace, ev);
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
      var res := checkpointStrategy.OnCheckpointRequested(
        ckptState, activeTxs, activeOrder, true
      );
      var nextState := res.0;
      var recs := res.1;
      var err := res.2;
      if err != "" {
        errors := errors + [err];
        return;
      }

      var prevState := ckptState;
      ckptState := CkptIdle;
      ApplyCheckpointTransition(prevState, nextState, recs);
    }

    // -------------------------------------------------------------------------
    // Modular Commit & Abort helpers (keep each proof obligation small and fast)
    // -------------------------------------------------------------------------

    // Rule U1 (WAL): flush all pending log records to disk before any OUTPUT.
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
        LemmaAppendNonWritePreservesTrace(prevTrace, flushEv);
        flushedLogLen := |log|;
        trace := trace + [flushEv];
      }
    }

    // Rule U2: OUTPUT every element modified by `tx` from buffer to disk.
    method OutputDirtyElements(tx: TxId)
      requires Valid()
      requires tx in activeTxs
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
      ensures forall j :: 0 <= j < |trace| && trace[j].EventWriteBuffer? && trace[j].tx == tx ==>
        exists o :: j < o < |trace| && trace[o].EventOutput? && trace[o].element == trace[j].element
    {
      var dirty := dirtyElements[tx];
      ghost var preTrace := trace;
      ghost var preLen := |trace|;

      var k := 0;
      while k < |dirty|
        invariant 0 <= k <= |dirty|
        invariant Valid()
        invariant preLen <= |trace|
        invariant preTrace <= trace
        invariant trace[..preLen] == preTrace
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
        invariant forall j :: preLen <= j < |trace| ==> trace[j].EventOutput?
        invariant forall m :: 0 <= m < k ==>
          exists o :: preLen <= o < |trace| && trace[o].EventOutput? && trace[o].element == dirty[m]
        decreases |dirty| - k
      {
        var elem := dirty[k];
        var val := buffer[elem];
        var outEv := EventOutput(elem, val);
        disk := disk[elem := val];

        ghost var prevTrace := trace;
        LemmaAppendNonWritePreservesTrace(prevTrace, outEv);
        trace := trace + [outEv];

        assert preTrace <= prevTrace && prevTrace <= trace;
        assert trace[..preLen] == preTrace;

        forall m | 0 <= m < k + 1
          ensures exists o :: preLen <= o < |trace| && trace[o].EventOutput? && trace[o].element == dirty[m]
        {
          if m < k {
            var o :| preLen <= o < |prevTrace| && prevTrace[o].EventOutput? && prevTrace[o].element == dirty[m];
            assert trace[o] == prevTrace[o];
          } else {
            assert trace[|prevTrace|] == outEv;
            assert preLen <= |prevTrace| < |trace|;
          }
        }

        k := k + 1;
      }

      forall j | 0 <= j < |trace| && trace[j].EventWriteBuffer? && trace[j].tx == tx
        ensures exists o :: j < o < |trace| && trace[o].EventOutput? && trace[o].element == trace[j].element
      {
        assert j < preLen;
        assert preTrace[j] == trace[j];
        assert trace[j].element in dirty;
        var m :| 0 <= m < |dirty| && dirty[m] == trace[j].element;
        var o :| preLen <= o < |trace| && trace[o].EventOutput? && trace[o].element == dirty[m];
        assert j < o < |trace|;
      }
    }

    // Emits <COMMIT tx>, flushes the log, moves `tx` to committedTxs, and
    // returns the prior checkpoint state for OnTransactionFinished handling.
    method EmitCommitAndFinalize(tx: TxId) returns (prevCkpt: CheckpointState)
      requires Valid()
      requires tx in activeTxs
      requires forall j :: 0 <= j < |trace| && trace[j].EventWriteBuffer? && trace[j].tx == tx ==>
        exists o :: j < o < |trace| && trace[o].EventOutput? && trace[o].element == trace[j].element
      modifies this
      ensures Valid()
      ensures old(log) <= log
      ensures old(trace) <= trace
      ensures log == old(log) + [LogCommit(tx)]
      ensures flushedLogLen == |log|
      ensures tx in committedTxs
      ensures tx !in activeTxs
      ensures errors == old(errors)
      ensures ckptState == CkptIdle
      ensures prevCkpt == old(ckptState)
      ensures prevCkpt.CkptActiveNonQuiescent? ==>
        prevCkpt.watchedTxs <= activeTxs + {tx} && HasStartCheckpoint(log)
    {
      prevCkpt := ckptState;
      ghost var initTrace := trace;
      ghost var initTraceLen := |trace|;
      ghost var prevLog := log;
      ghost var oldLogLen := |log|;
      var commitRec := LogCommit(tx);
      var commitEv := EventLog(commitRec);

      LemmaAppendLogPreservesLifecycle(prevLog, commitRec);
      LemmaAppendPreservesRuleU1(initTrace, commitEv);
      LemmaAppendCommitPreservesRuleU2(initTrace, tx);

      log := log + [commitRec];
      trace := trace + [commitEv];
      assert trace[..initTraceLen] == initTrace;
      assert log[oldLogLen] == LogCommit(tx);
      assert HasCommit(log, tx);

      var finalFlushEv := EventFlushLog(|log|);
      ghost var tBeforeFlush := trace;
      LemmaAppendNonWritePreservesTrace(tBeforeFlush, finalFlushEv);

      flushedLogLen := |log|;
      trace := trace + [finalFlushEv];
      assert trace[..initTraceLen] == initTrace;
      assert initTrace <= tBeforeFlush && tBeforeFlush <= trace;
      assert forall j :: initTraceLen <= j < |trace| ==> !trace[j].EventWriteBuffer?;

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

      FlushLogIfNeeded();
      OutputDirtyElements(tx);
      var prevCkpt := EmitCommitAndFinalize(tx);

      var res := checkpointStrategy.OnTransactionFinished(prevCkpt, tx, activeTxs);
      ApplyCheckpointTransition(prevCkpt, res.0, res.1);
    }

    // Rolls back `tx`'s buffer modifications in reverse log order.
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
        if log[idx].LogUndoUpdate? && log[idx].tx == tx {
          var elem := log[idx].element;
          var oldVal := log[idx].oldValue;
          var undoEv := EventUndoRestore(tx, elem, oldVal);
          buffer := buffer[elem := oldVal];

          ghost var prevTrace := trace;
          LemmaAppendNonWritePreservesTrace(prevTrace, undoEv);
          trace := trace + [undoEv];
          assert preTrace <= prevTrace && prevTrace <= trace;
        }
      }
    }

    // Emits <ABORT tx>, flushes the log, moves `tx` to abortedTxs, and
    // returns the prior checkpoint state for OnTransactionFinished handling.
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
      ghost var initTraceLen := |trace|;
      ghost var prevLog := log;
      ghost var oldLogLen := |log|;
      var abortRec := LogAbort(tx);
      var abortEv := EventLog(abortRec);

      LemmaAppendLogPreservesLifecycle(prevLog, abortRec);
      LemmaAppendNonWritePreservesTrace(initTrace, abortEv);

      log := log + [abortRec];
      trace := trace + [abortEv];
      assert trace[..initTraceLen] == initTrace;
      assert log[oldLogLen] == LogAbort(tx);
      assert HasAbort(log, tx);

      var flushEv := EventFlushLog(|log|);
      ghost var tBeforeFlush := trace;
      LemmaAppendNonWritePreservesTrace(tBeforeFlush, flushEv);

      flushedLogLen := |log|;
      trace := trace + [flushEv];
      assert trace[..initTraceLen] == initTrace;
      assert initTrace <= tBeforeFlush && tBeforeFlush <= trace;
      assert forall j :: initTraceLen <= j < |trace| ==> !trace[j].EventWriteBuffer?;

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
  // strategy, and a Schedule, runs Undo logging via dispatch.
  method GenerateUndoLog(
    initialDb: DatabaseState,
    checkpointStrategy: CheckpointStrategy,
    schedule: Schedule
  )
    returns (logResult: seq<LogRecord>, traceResult: seq<TraceEvent>, errorResult: seq<string>)
  {
    var logger := new UndoLogger(initialDb, checkpointStrategy);
    logResult, traceResult, errorResult := schedule.Run(logger);
  }
}
