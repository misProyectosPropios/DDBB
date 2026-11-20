// Simple (Pure) Undo Logging implementation extending LoggingStrategy.
//
// Enforces and formally proves Garcia-Molina's Undo Logging rules:
//   - Rule U1 (Write-Ahead Logging): all log records are flushed to disk before
//     any modified database element is written to disk (OUTPUT).
//   - Rule U2 (Output Before Commit): every element modified by a transaction T
//     is OUTPUT to disk before <COMMIT T> is written to the log and flushed.
//   - Append-only log monotonicity and transaction lifecycle invariants.
//
// Checkpointing (quiescent and non-quiescent) is intentionally deferred to
// later modules.

include "Types.dfy"
include "Dispatch.dfy"

module UndoLogging {
  import opened LoggingTypes
  import opened LoggingDispatch

  @AssumeCrossModuleTermination
  class UndoLogger extends LoggingStrategy {
    var disk: DatabaseState
    var buffer: DatabaseState
    var flushedLogLen: nat
    var activeTxs: set<TxId>
    var committedTxs: set<TxId>
    var abortedTxs: set<TxId>
    // Preserves insertion order of modified elements per active transaction so
    // OUTPUT order at COMMIT is deterministic.
    var dirtyElements: map<TxId, seq<ElementId>>

    ghost predicate Valid()
      reads this
    {
      // 1. Disjoint transaction states
      activeTxs !! committedTxs &&
      activeTxs !! abortedTxs &&
      committedTxs !! abortedTxs &&

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

      // 5. Log-transaction lifecycle consistency
      (forall i :: 0 <= i < |log| ==>
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

      // 6. Undo Logging correctness rules (WAL + Output Before Commit)
      WriteHasUndoLogBefore(trace) &&
      RuleU1_FlushBeforeOutput(trace) &&
      RuleU2_OutputBeforeCommit(trace) &&

      // 7. Every in-memory write by an active transaction is tracked as dirty
      (forall tx :: tx in activeTxs ==>
        forall j :: 0 <= j < |trace| && trace[j].EventWriteBuffer? && trace[j].tx == tx ==>
          trace[j].element in dirtyElements[tx])
    }

    constructor (initialDb: DatabaseState)
      ensures Valid()
      ensures log == []
      ensures trace == []
      ensures errors == []
      ensures disk == initialDb
      ensures buffer == initialDb
      ensures flushedLogLen == 0
      ensures activeTxs == {}
      ensures committedTxs == {}
      ensures abortedTxs == {}
    {
      this.log := [];
      this.trace := [];
      this.errors := [];
      this.disk := initialDb;
      this.buffer := initialDb;
      this.flushedLogLen := 0;
      this.activeTxs := {};
      this.committedTxs := {};
      this.abortedTxs := {};
      this.dirtyElements := map[];
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
      ensures old(tx !in (activeTxs + committedTxs + abortedTxs)) ==>
        log == old(log) + [LogStart(tx)] &&
        activeTxs == old(activeTxs) + {tx} &&
        committedTxs == old(committedTxs) &&
        abortedTxs == old(abortedTxs) &&
        buffer == old(buffer) &&
        disk == old(disk) &&
        flushedLogLen == old(flushedLogLen) &&
        errors == old(errors)
    {
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
      dirtyElements := dirtyElements[tx := []];

      assert trace[..|prevTrace|] == prevTrace;
      assert log[|prevLog|] == LogStart(tx);

      // Show no prior WriteBuffer events exist for the brand-new transaction.
      forall j | 0 <= j < |trace| && trace[j].EventWriteBuffer? && trace[j].tx == tx
        ensures trace[j].element in dirtyElements[tx]
      {
        assert j < |prevTrace|;
        assert prevTrace[j] == trace[j];
        // WriteHasUndoLogBefore implies prevTrace[j - 1] is EventLog(LogUndoUpdate(tx, ...)),
        // which would place tx in ExtractLog(prevTrace) == prevLog — impossible since tx
        // was not in old(activeTxs + committedTxs + abortedTxs).
        assert j > 0;
        assert prevTrace[j - 1].EventLog?;
        assert prevTrace[j - 1].record.tx == tx;
        LemmaEventLogInExtractLog(prevTrace, j - 1);
        var idx :| 0 <= idx < |prevLog| && prevLog[idx] == prevTrace[j - 1].record;
        assert prevLog[idx].tx == tx;
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
      ensures committedTxs == old(committedTxs)
      ensures abortedTxs == old(abortedTxs)
      ensures dirtyElements == old(dirtyElements)
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
      ensures committedTxs == old(committedTxs)
      ensures abortedTxs == old(abortedTxs)
      ensures dirtyElements == old(dirtyElements)
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

    // Emits <COMMIT tx>, flushes the log, and moves `tx` to committedTxs.
    method EmitCommitAndFinalize(tx: TxId)
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
    {
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

      activeTxs := activeTxs - {tx};
      committedTxs := committedTxs + {tx};
      dirtyElements := dirtyElements - {tx};
    }

    method VisitCommit(tx: TxId)
      requires Valid()
      modifies this
      ensures Valid()
      ensures old(log) <= log
      ensures old(trace) <= trace
      ensures old(tx in activeTxs) ==>
        log == old(log) + [LogCommit(tx)] &&
        flushedLogLen == |log| &&
        tx in committedTxs &&
        tx !in activeTxs &&
        errors == old(errors)
    {
      if tx !in activeTxs {
        errors := errors + ["Cannot COMMIT " + tx + ": transaction is not active."];
        return;
      }

      FlushLogIfNeeded();
      OutputDirtyElements(tx);
      EmitCommitAndFinalize(tx);
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
      ensures committedTxs == old(committedTxs)
      ensures abortedTxs == old(abortedTxs)
      ensures dirtyElements == old(dirtyElements)
      ensures errors == old(errors)
    {
      ghost var preTrace := trace;
      var idx := |log|;
      while idx > 0
        invariant 0 <= idx <= |log|
        invariant Valid()
        invariant preTrace <= trace
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

    // Emits <ABORT tx>, flushes the log, and moves `tx` to abortedTxs.
    method EmitAbortAndFinalize(tx: TxId)
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
    {
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

      activeTxs := activeTxs - {tx};
      abortedTxs := abortedTxs + {tx};
      dirtyElements := dirtyElements - {tx};
    }

    method VisitAbort(tx: TxId)
      requires Valid()
      modifies this
      ensures Valid()
      ensures old(log) <= log
      ensures old(trace) <= trace
      ensures old(tx in activeTxs) ==>
        log == old(log) + [LogAbort(tx)] &&
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
      EmitAbortAndFinalize(tx);
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
  }

  // Helper lemma: any EventLog at index `k` in `t` appears at some index in `ExtractLog(t)`.
  lemma LemmaEventLogInExtractLog(t: seq<TraceEvent>, k: int)
    requires 0 <= k < |t|
    requires t[k].EventLog?
    ensures exists idx :: 0 <= idx < |ExtractLog(t)| && ExtractLog(t)[idx] == t[k].record
    decreases |t|
  {
    if k == |t| - 1 {
      var prev := ExtractLog(t[..|t| - 1]);
      assert ExtractLog(t)[|prev|] == t[k].record;
    } else {
      LemmaEventLogInExtractLog(t[..|t| - 1], k);
      var idx :| 0 <= idx < |ExtractLog(t[..|t| - 1])| && ExtractLog(t[..|t| - 1])[idx] == t[k].record;
      assert ExtractLog(t)[idx] == t[k].record;
    }
  }

  // Convenience entry point: given an initial database state and a Schedule,
  // runs pure Undo logging via double dispatch and returns the generated log.
  method GenerateUndoLog(initialDb: DatabaseState, schedule: Schedule)
    returns (logResult: seq<LogRecord>, traceResult: seq<TraceEvent>, errorResult: seq<string>)
  {
    var logger := new UndoLogger(initialDb);
    logResult, traceResult, errorResult := schedule.Run(logger);
  }
}
