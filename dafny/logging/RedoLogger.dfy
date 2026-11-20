// Simple (Pure) Redo Logging implementation extending LoggingStrategy.
//
// Enforces and formally proves Garcia-Molina's Redo Logging Rule R1:
//   - Rule R1 (WAL + Commit Before Disk Output): Before any modified database
//     element is written out to disk (OUTPUT), both its Redo update record
//     <T, X, newVal> and <COMMIT T> must already be emitted and flushed to disk
//     (FLUSH LOG).
//   - Loading disk blocks into memory (INPUT) is intentionally not modeled
//     since it is outside the logging protocol.
//   - Checkpointing (quiescent and non-quiescent) is deferred to later modules.

include "Types.dfy"
include "Dispatch.dfy"

module RedoLogging {
  import opened LoggingTypes
  import opened LoggingDispatch

  // Invariant helper: every dirty element tracked for an active transaction has
  // a corresponding <tx, e, newVal> Redo update record already recorded in `t`.
  ghost predicate {:opaque} DirtyWritesLogged(
    activeTxs: set<TxId>,
    dirtyElements: map<TxId, seq<ElementId>>,
    dirtyValues: map<TxId, map<ElementId, Value>>,
    t: seq<TraceEvent>
  )
    requires dirtyElements.Keys == activeTxs && dirtyValues.Keys == activeTxs
  {
    forall tx :: tx in activeTxs ==>
      forall e :: e in dirtyElements[tx] ==>
        e in dirtyValues[tx] &&
        exists u :: 0 <= u < |t| &&
          t[u] == EventLog(LogRedoUpdate(tx, e, dirtyValues[tx][e]))
  }

  // Extending a trace preserves all existing Redo update witnesses.
  lemma LemmaPrefixPreservesDirtyWritesLogged(
    activeTxs: set<TxId>,
    dirtyElements: map<TxId, seq<ElementId>>,
    dirtyValues: map<TxId, map<ElementId, Value>>,
    t1: seq<TraceEvent>,
    t2: seq<TraceEvent>
  )
    requires dirtyElements.Keys == activeTxs && dirtyValues.Keys == activeTxs
    requires t1 <= t2
    requires DirtyWritesLogged(activeTxs, dirtyElements, dirtyValues, t1)
    ensures DirtyWritesLogged(activeTxs, dirtyElements, dirtyValues, t2)
  {
    reveal DirtyWritesLogged();
    forall tx | tx in activeTxs
      ensures forall e :: e in dirtyElements[tx] ==>
        e in dirtyValues[tx] &&
        exists u :: 0 <= u < |t2| &&
          t2[u] == EventLog(LogRedoUpdate(tx, e, dirtyValues[tx][e]))
    {
      forall e | e in dirtyElements[tx]
        ensures e in dirtyValues[tx] &&
          exists u :: 0 <= u < |t2| &&
            t2[u] == EventLog(LogRedoUpdate(tx, e, dirtyValues[tx][e]))
      {
        var u :| 0 <= u < |t1| && t1[u] == EventLog(LogRedoUpdate(tx, e, dirtyValues[tx][e]));
        assert t2[u] == t1[u];
      }
    }
  }

  // Recording a new Redo write at `updateIdx` preserves DirtyWritesLogged.
  lemma LemmaUpdateDirtyWritesLogged(
    activeTxs: set<TxId>,
    oldDirtyElems: map<TxId, seq<ElementId>>,
    oldDirtyVals: map<TxId, map<ElementId, Value>>,
    newDirtyElems: map<TxId, seq<ElementId>>,
    newDirtyVals: map<TxId, map<ElementId, Value>>,
    tx: TxId,
    element: ElementId,
    newValue: Value,
    t: seq<TraceEvent>,
    updateIdx: nat
  )
    requires tx in activeTxs
    requires oldDirtyElems.Keys == activeTxs && oldDirtyVals.Keys == activeTxs
    requires newDirtyElems.Keys == activeTxs && newDirtyVals.Keys == activeTxs
    requires DirtyWritesLogged(activeTxs, oldDirtyElems, oldDirtyVals, t)
    requires updateIdx < |t| && t[updateIdx] == EventLog(LogRedoUpdate(tx, element, newValue))
    requires newDirtyElems == oldDirtyElems[tx := if element in oldDirtyElems[tx] then oldDirtyElems[tx] else oldDirtyElems[tx] + [element]]
    requires newDirtyVals == oldDirtyVals[tx := oldDirtyVals[tx][element := newValue]]
    ensures DirtyWritesLogged(activeTxs, newDirtyElems, newDirtyVals, t)
  {
    reveal DirtyWritesLogged();
    forall txn | txn in activeTxs
      ensures forall e :: e in newDirtyElems[txn] ==>
        e in newDirtyVals[txn] &&
        exists u :: 0 <= u < |t| &&
          t[u] == EventLog(LogRedoUpdate(txn, e, newDirtyVals[txn][e]))
    {
      forall e | e in newDirtyElems[txn]
        ensures e in newDirtyVals[txn] &&
          exists u :: 0 <= u < |t| &&
            t[u] == EventLog(LogRedoUpdate(txn, e, newDirtyVals[txn][e]))
      {
        if txn == tx && e == element {
          assert newDirtyVals[txn][e] == newValue;
          assert t[updateIdx] == EventLog(LogRedoUpdate(txn, e, newDirtyVals[txn][e]));
        } else {
          assert e in oldDirtyElems[txn];
          assert newDirtyVals[txn][e] == oldDirtyVals[txn][e];
          var u :| 0 <= u < |t| && t[u] == EventLog(LogRedoUpdate(txn, e, oldDirtyVals[txn][e]));
          assert t[u] == EventLog(LogRedoUpdate(txn, e, newDirtyVals[txn][e]));
        }
      }
    }
  }

  @AssumeCrossModuleTermination
  class RedoLogger extends LoggingStrategy {
    var disk: DatabaseState
    var buffer: DatabaseState
    var flushedLogLen: nat
    var activeTxs: set<TxId>
    var committedTxs: set<TxId>
    var abortedTxs: set<TxId>
    // Preserves insertion order of modified elements per active transaction so
    // OUTPUT order after COMMIT is deterministic.
    var dirtyElements: map<TxId, seq<ElementId>>
    // Latest written value per (active tx, element) so OUTPUT after COMMIT
    // writes only committed values to disk, never uncommitted writes.
    var dirtyValues: map<TxId, map<ElementId, Value>>

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
      dirtyValues.Keys == activeTxs &&
      (forall tx :: tx in activeTxs ==>
        forall e :: e in dirtyElements[tx] ==> e in buffer.Keys) &&
      DirtyWritesLogged(activeTxs, dirtyElements, dirtyValues, trace) &&

      // 4. Flushed log boundary and trace-to-log correspondence
      flushedLogLen <= |log| &&
      ExtractLog(trace) == log &&
      LastFlushedCount(trace) == flushedLogLen &&

      // 5. Log-transaction lifecycle consistency
      (forall i :: 0 <= i < |log| ==>
        log[i].tx in activeTxs + committedTxs + abortedTxs) &&
      (forall i :: 0 <= i < |log| && log[i].LogRedoUpdate? ==>
        log[i].element in buffer.Keys) &&
      (forall tx :: tx in activeTxs ==>
        HasStart(log, tx) && !HasCommit(log, tx) && !HasAbort(log, tx)) &&
      (forall tx :: tx in committedTxs ==>
        HasStart(log, tx) && HasCommit(log, tx) && !HasAbort(log, tx)) &&
      (forall tx :: tx in abortedTxs ==>
        HasStart(log, tx) && !HasCommit(log, tx) && HasAbort(log, tx)) &&
      StartBeforeEnd(log) &&

      // 6. Redo Logging correctness rules (WAL + Commit Before Output)
      WriteHasRedoLogBefore(trace) &&
      RuleR1_FlushAndCommitBeforeOutput(trace)
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
      this.dirtyValues := map[];
      LemmaEmptyTraceRuleR1();
      reveal DirtyWritesLogged();
    }

    // -------------------------------------------------------------------------
    // Visitor methods (same interface as UndoLogger, invoked via Operation.Accept)
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
      var ev := EventLog(rec);
      ghost var prevLog := log;
      ghost var prevTrace := trace;
      ghost var oldActive := activeTxs;
      ghost var oldDirtyElems := dirtyElements;
      ghost var oldDirtyVals := dirtyValues;

      LemmaAppendLogPreservesLifecycle(prevLog, rec);
      LemmaAppendNonWritePreservesRedoTrace(prevTrace, ev);

      log := log + [rec];
      trace := trace + [ev];
      LemmaPrefixPreservesDirtyWritesLogged(oldActive, oldDirtyElems, oldDirtyVals, prevTrace, trace);

      activeTxs := activeTxs + {tx};
      dirtyElements := dirtyElements[tx := []];
      dirtyValues := dirtyValues[tx := map[]];

      reveal DirtyWritesLogged();
      assert log[|prevLog|] == LogStart(tx);
      assert HasStart(log, tx);
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
      LemmaAppendNonWritePreservesRedoTrace(prevTrace, ev);
      trace := trace + [ev];
      LemmaPrefixPreservesDirtyWritesLogged(activeTxs, dirtyElements, dirtyValues, prevTrace, trace);
    }

    method VisitWrite(tx: TxId, element: ElementId, newValue: Value)
      requires Valid()
      modifies this
      ensures Valid()
      ensures old(log) <= log
      ensures old(trace) <= trace
      ensures (old(tx in activeTxs) && old(element in buffer)) ==>
        log == old(log) + [LogRedoUpdate(tx, element, newValue)] &&
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
      var rec := LogRedoUpdate(tx, element, newValue);
      var logEv := EventLog(rec);

      ghost var prevLog := log;
      ghost var t0 := trace;
      ghost var updateTraceIdx := |t0|;
      LemmaAppendLogPreservesLifecycle(prevLog, rec);
      LemmaAppendNonWritePreservesRedoTrace(t0, logEv);
      log := log + [rec];
      trace := trace + [logEv];

      var writeEv := EventWriteBuffer(tx, element, oldVal, newValue);
      ghost var t1 := trace;
      LemmaAppendPreservesRuleR1(t1, writeEv);
      buffer := buffer[element := newValue];
      trace := trace + [writeEv];
      assert trace[..|t1|] == t1;
      assert t0 <= t1 && t1 <= trace;
      assert trace[updateTraceIdx] == EventLog(LogRedoUpdate(tx, element, newValue));

      ghost var oldDirtyElems := dirtyElements;
      ghost var oldDirtyVals := dirtyValues;
      LemmaPrefixPreservesDirtyWritesLogged(activeTxs, oldDirtyElems, oldDirtyVals, t0, trace);

      var curDirty := dirtyElements[tx];
      if element !in curDirty {
        dirtyElements := dirtyElements[tx := curDirty + [element]];
      }
      var curVals := dirtyValues[tx];
      dirtyValues := dirtyValues[tx := curVals[element := newValue]];

      LemmaUpdateDirtyWritesLogged(
        activeTxs, oldDirtyElems, oldDirtyVals,
        dirtyElements, dirtyValues,
        tx, element, newValue, trace, updateTraceIdx
      );
    }

    // -------------------------------------------------------------------------
    // Modular Commit & Abort helpers (keep each proof obligation small and fast)
    // -------------------------------------------------------------------------

    // Rule R1 (WAL): emit <COMMIT tx>, flush the log to disk, and transition
    // `tx` to committedTxs BEFORE any modified element is written to disk.
    method EmitCommitAndFlush(tx: TxId)
      returns (dirty: seq<ElementId>, vals: map<ElementId, Value>, ghost commitIdx: nat)
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
      ensures errors == old(errors)
      ensures commitIdx < |trace| && trace[commitIdx] == EventLog(LogCommit(tx))
      ensures forall e :: e in dirty ==>
        e in buffer.Keys &&
        e in vals &&
        exists u :: 0 <= u < commitIdx &&
          trace[u] == EventLog(LogRedoUpdate(tx, e, vals[e]))
    {
      dirty := dirtyElements[tx];
      vals := dirtyValues[tx];
      commitIdx := |trace|;

      ghost var initTrace := trace;
      ghost var prevLog := log;
      ghost var oldLogLen := |log|;
      var commitRec := LogCommit(tx);
      var commitEv := EventLog(commitRec);

      LemmaAppendLogPreservesLifecycle(prevLog, commitRec);
      LemmaAppendNonWritePreservesRedoTrace(initTrace, commitEv);

      log := log + [commitRec];
      trace := trace + [commitEv];
      assert trace[commitIdx] == EventLog(LogCommit(tx));
      assert log[oldLogLen] == LogCommit(tx);
      assert HasCommit(log, tx);

      var flushEv := EventFlushLog(|log|);
      ghost var tBeforeFlush := trace;
      LemmaAppendNonWritePreservesRedoTrace(tBeforeFlush, flushEv);

      flushedLogLen := |log|;
      trace := trace + [flushEv];
      assert initTrace <= tBeforeFlush && tBeforeFlush <= trace;
      assert trace[commitIdx] == EventLog(LogCommit(tx));

      reveal DirtyWritesLogged();
      forall e | e in dirty
        ensures e in buffer.Keys &&
          e in vals &&
          exists u :: 0 <= u < commitIdx &&
            trace[u] == EventLog(LogRedoUpdate(tx, e, vals[e]))
      {
        var u :| 0 <= u < |initTrace| &&
          initTrace[u] == EventLog(LogRedoUpdate(tx, e, vals[e]));
        assert trace[u] == initTrace[u];
      }

      activeTxs := activeTxs - {tx};
      committedTxs := committedTxs + {tx};
      dirtyElements := dirtyElements - {tx};
      dirtyValues := dirtyValues - {tx};

      forall t | t in activeTxs
        ensures forall e :: e in dirtyElements[t] ==>
          e in dirtyValues[t] &&
          exists u :: 0 <= u < |trace| &&
            trace[u] == EventLog(LogRedoUpdate(t, e, dirtyValues[t][e]))
      {
        forall e | e in dirtyElements[t]
          ensures e in dirtyValues[t] &&
            exists u :: 0 <= u < |trace| &&
              trace[u] == EventLog(LogRedoUpdate(t, e, dirtyValues[t][e]))
        {
          var u :| 0 <= u < |initTrace| &&
            initTrace[u] == EventLog(LogRedoUpdate(t, e, dirtyValues[t][e]));
          assert trace[u] == initTrace[u];
        }
      }
    }

    // Writes one committed element update down to disk, preserving Valid() and Rule R1.
    method OutputSingleCommittedElement(
      tx: TxId,
      elem: ElementId,
      val: Value,
      ghost commitIdx: nat,
      ghost updateIdx: nat
    )
      requires Valid()
      requires flushedLogLen == |log|
      requires elem in buffer.Keys
      requires updateIdx < commitIdx < |trace|
      requires trace[updateIdx] == EventLog(LogRedoUpdate(tx, elem, val))
      requires trace[commitIdx] == EventLog(LogCommit(tx))
      modifies this
      ensures Valid()
      ensures old(trace) <= trace
      ensures disk == old(disk)[elem := val]
      ensures log == old(log)
      ensures flushedLogLen == |log|
      ensures buffer == old(buffer)
      ensures activeTxs == old(activeTxs)
      ensures committedTxs == old(committedTxs)
      ensures abortedTxs == old(abortedTxs)
      ensures dirtyElements == old(dirtyElements)
      ensures dirtyValues == old(dirtyValues)
      ensures errors == old(errors)
    {
      var outEv := EventOutput(elem, val);
      ghost var prevTrace := trace;
      LemmaAppendNonWritePreservesRedoTrace(prevTrace, outEv);
      disk := disk[elem := val];
      trace := trace + [outEv];
      LemmaPrefixPreservesDirtyWritesLogged(activeTxs, dirtyElements, dirtyValues, prevTrace, trace);
    }

    // Writes the committed transaction's updates down to disk after <COMMIT tx>
    // has already been flushed (preserving Rule R1).
    method OutputCommittedElements(
      tx: TxId,
      dirty: seq<ElementId>,
      vals: map<ElementId, Value>,
      ghost commitIdx: nat
    )
      requires Valid()
      requires flushedLogLen == |log|
      requires commitIdx < |trace| && trace[commitIdx] == EventLog(LogCommit(tx))
      requires forall e :: e in dirty ==>
        e in buffer.Keys &&
        e in vals &&
        exists u :: 0 <= u < commitIdx &&
          trace[u] == EventLog(LogRedoUpdate(tx, e, vals[e]))
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
      ensures dirtyValues == old(dirtyValues)
      ensures errors == old(errors)
      ensures forall e :: e in dirty ==> disk[e] == vals[e]
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
        invariant committedTxs == old(committedTxs)
        invariant abortedTxs == old(abortedTxs)
        invariant dirtyElements == old(dirtyElements)
        invariant dirtyValues == old(dirtyValues)
        invariant errors == old(errors)
        invariant forall m :: 0 <= m < k ==> disk[dirty[m]] == vals[dirty[m]]
        decreases |dirty| - k
      {
        var elem := dirty[k];
        var val := vals[elem];
        ghost var u :| 0 <= u < commitIdx &&
          preTrace[u] == EventLog(LogRedoUpdate(tx, elem, val));
        assert trace[u] == preTrace[u];
        assert trace[commitIdx] == preTrace[commitIdx];

        ghost var prevTrace := trace;
        OutputSingleCommittedElement(tx, elem, val, commitIdx, u);
        assert preTrace <= prevTrace && prevTrace <= trace;

        k := k + 1;
      }
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

      var dirty, vals, commitIdx := EmitCommitAndFlush(tx);
      OutputCommittedElements(tx, dirty, vals, commitIdx);
    }

    // Discards `tx`'s uncommitted buffer edits by restoring each dirty element
    // from the clean on-disk state (Rule R1 guarantees disk was untouched by `tx`).
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
      ensures dirtyValues == old(dirtyValues)
      ensures errors == old(errors)
    {
      var dirty := dirtyElements[tx];
      ghost var preTrace := trace;
      var k := 0;
      while k < |dirty|
        invariant 0 <= k <= |dirty|
        invariant Valid()
        invariant preTrace <= trace
        invariant log == old(log)
        invariant flushedLogLen == old(flushedLogLen)
        invariant disk == old(disk)
        invariant activeTxs == old(activeTxs)
        invariant committedTxs == old(committedTxs)
        invariant abortedTxs == old(abortedTxs)
        invariant dirtyElements == old(dirtyElements)
        invariant dirtyValues == old(dirtyValues)
        invariant errors == old(errors)
        decreases |dirty| - k
      {
        var elem := dirty[k];
        var restoredVal := disk[elem];
        var undoEv := EventUndoRestore(tx, elem, restoredVal);
        buffer := buffer[elem := restoredVal];

        ghost var prevTrace := trace;
        LemmaAppendNonWritePreservesRedoTrace(prevTrace, undoEv);
        trace := trace + [undoEv];
        LemmaPrefixPreservesDirtyWritesLogged(activeTxs, dirtyElements, dirtyValues, prevTrace, trace);
        assert preTrace <= prevTrace && prevTrace <= trace;

        k := k + 1;
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
      ghost var prevLog := log;
      ghost var oldLogLen := |log|;
      var abortRec := LogAbort(tx);
      var abortEv := EventLog(abortRec);

      LemmaAppendLogPreservesLifecycle(prevLog, abortRec);
      LemmaAppendNonWritePreservesRedoTrace(initTrace, abortEv);

      log := log + [abortRec];
      trace := trace + [abortEv];
      assert log[oldLogLen] == LogAbort(tx);
      assert HasAbort(log, tx);

      var flushEv := EventFlushLog(|log|);
      ghost var tBeforeFlush := trace;
      LemmaAppendNonWritePreservesRedoTrace(tBeforeFlush, flushEv);

      flushedLogLen := |log|;
      trace := trace + [flushEv];
      assert initTrace <= tBeforeFlush && tBeforeFlush <= trace;

      activeTxs := activeTxs - {tx};
      abortedTxs := abortedTxs + {tx};
      dirtyElements := dirtyElements - {tx};
      dirtyValues := dirtyValues - {tx};

      reveal DirtyWritesLogged();
      forall t | t in activeTxs
        ensures forall e :: e in dirtyElements[t] ==>
          e in dirtyValues[t] &&
          exists u :: 0 <= u < |trace| &&
            trace[u] == EventLog(LogRedoUpdate(t, e, dirtyValues[t][e]))
      {
        forall e | e in dirtyElements[t]
          ensures e in dirtyValues[t] &&
            exists u :: 0 <= u < |trace| &&
              trace[u] == EventLog(LogRedoUpdate(t, e, dirtyValues[t][e]))
        {
          var u :| 0 <= u < |initTrace| &&
            initTrace[u] == EventLog(LogRedoUpdate(t, e, dirtyValues[t][e]));
          assert trace[u] == initTrace[u];
        }
      }
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
    // State inspection accessors (same interface as UndoLogger)
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

  // Convenience entry point: given an initial database state and a Schedule,
  // runs pure Redo logging via dispatch and returns the generated log.
  method GenerateRedoLog(initialDb: DatabaseState, schedule: Schedule)
    returns (logResult: seq<LogRecord>, traceResult: seq<TraceEvent>, errorResult: seq<string>)
  {
    var logger := new RedoLogger(initialDb);
    logResult, traceResult, errorResult := schedule.Run(logger);
  }
}
