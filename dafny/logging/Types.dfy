// Core domain types, Undo log records, execution trace events, formal Undo
// logging correctness predicates (Garcia-Molina Rules U1 & U2), and string
// formatters.

module LoggingTypes {
  type TxId = string
  type ElementId = string
  type Value = int
  type DatabaseState = map<ElementId, Value>

  // Pure Undo log records (no checkpoints yet; quiescent/non-quiescent
  // checkpoints and Redo / Undo-Redo records will be introduced later).
  datatype LogRecord =
    | LogStart(tx: TxId)
    | LogUndoUpdate(tx: TxId, element: ElementId, oldValue: Value)
    | LogCommit(tx: TxId)
    | LogAbort(tx: TxId)

  // Step-by-step execution trace showing log emissions alongside buffer reads,
  // buffer writes, rollback restores, WAL flushes (FLUSH LOG), and disk writes
  // (OUTPUT).
  datatype TraceEvent =
    | EventLog(record: LogRecord)
    | EventRead(tx: TxId, element: ElementId, value: Value)
    | EventWriteBuffer(tx: TxId, element: ElementId, oldVal: Value, newVal: Value)
    | EventUndoRestore(tx: TxId, element: ElementId, restoredVal: Value)
    | EventFlushLog(flushedCount: nat)
    | EventOutput(element: ElementId, value: Value)

  // ---------------------------------------------------------------------------
  // Pure trace projection functions (defined from the tail so appending a
  // single event unfolds in one step during verification).
  // ---------------------------------------------------------------------------

  function ExtractLog(t: seq<TraceEvent>): seq<LogRecord>
    decreases |t|
  {
    if |t| == 0 then []
    else
      var prev := ExtractLog(t[..|t| - 1]);
      var last := t[|t| - 1];
      if last.EventLog? then prev + [last.record] else prev
  }

  function LastFlushedCount(t: seq<TraceEvent>): nat
    decreases |t|
  {
    if |t| == 0 then 0
    else
      var last := t[|t| - 1];
      if last.EventFlushLog? then last.flushedCount
      else LastFlushedCount(t[..|t| - 1])
  }

  // ---------------------------------------------------------------------------
  // Formal Undo Logging specification predicates
  // ---------------------------------------------------------------------------

  ghost predicate HasStart(log: seq<LogRecord>, tx: TxId)
  {
    exists i :: 0 <= i < |log| && log[i] == LogStart(tx)
  }

  ghost predicate HasCommit(log: seq<LogRecord>, tx: TxId)
  {
    exists i :: 0 <= i < |log| && log[i] == LogCommit(tx)
  }

  ghost predicate HasAbort(log: seq<LogRecord>, tx: TxId)
  {
    exists i :: 0 <= i < |log| && log[i] == LogAbort(tx)
  }

  // Every COMMIT or ABORT record for a transaction must be preceded by its
  // START record.
  ghost predicate StartBeforeEnd(log: seq<LogRecord>)
  {
    forall i :: 0 <= i < |log| && (log[i].LogCommit? || log[i].LogAbort?) ==>
      exists s :: 0 <= s < i && log[s] == LogStart(log[i].tx)
  }

  // Every in-memory write is immediately preceded by its Undo update record
  // <T, X, oldVal>.
  ghost predicate WriteHasUndoLogBefore(t: seq<TraceEvent>)
  {
    forall j :: 0 <= j < |t| && t[j].EventWriteBuffer? ==>
      j > 0 && t[j - 1] == EventLog(LogUndoUpdate(t[j].tx, t[j].element, t[j].oldVal))
  }

  // Undo Logging Rule U1 (Write-Ahead Logging):
  // Before any modified database element is written to disk (OUTPUT), all log
  // records emitted prior to that OUTPUT must already be flushed to disk.
  ghost predicate RuleU1_FlushBeforeOutput(t: seq<TraceEvent>)
  {
    forall i :: 0 <= i < |t| && t[i].EventOutput? ==>
      LastFlushedCount(t[..i]) == |ExtractLog(t[..i])|
  }

  // Undo Logging Rule U2 (Output Before Commit):
  // Before <COMMIT T> is written to the log, every element modified by T must
  // have been written to disk (OUTPUT) after the write occurred.
  ghost predicate RuleU2_OutputBeforeCommit(t: seq<TraceEvent>)
  {
    forall i :: 0 <= i < |t| && t[i].EventLog? && t[i].record.LogCommit? ==>
      var tx := t[i].record.tx;
      forall j :: 0 <= j < i && t[j].EventWriteBuffer? && t[j].tx == tx ==>
        exists o :: j < o < i && t[o].EventOutput? && t[o].element == t[j].element
  }

  // ---------------------------------------------------------------------------
  // Append-preservation lemmas (help Dafny lift slice/existential invariants
  // across `seq + [elem]` updates)
  // ---------------------------------------------------------------------------

  lemma LemmaAppendPreservesRuleU1(t: seq<TraceEvent>, e: TraceEvent)
    requires RuleU1_FlushBeforeOutput(t)
    requires e.EventOutput? ==> LastFlushedCount(t) == |ExtractLog(t)|
    ensures RuleU1_FlushBeforeOutput(t + [e])
  {
    var t' := t + [e];
    forall i | 0 <= i < |t'| && t'[i].EventOutput?
      ensures LastFlushedCount(t'[..i]) == |ExtractLog(t'[..i])|
    {
      if i < |t| {
        assert t'[..i] == t[..i];
      } else {
        assert i == |t|;
        assert t'[..i] == t;
      }
    }
  }

  lemma LemmaAppendNonCommitPreservesRuleU2(t: seq<TraceEvent>, e: TraceEvent)
    requires RuleU2_OutputBeforeCommit(t)
    requires !(e.EventLog? && e.record.LogCommit?)
    ensures RuleU2_OutputBeforeCommit(t + [e])
  {
    var t' := t + [e];
    forall i | 0 <= i < |t'| && t'[i].EventLog? && t'[i].record.LogCommit?
      ensures forall j :: 0 <= j < i && t'[j].EventWriteBuffer? && t'[j].tx == t'[i].record.tx ==>
        exists o :: j < o < i && t'[o].EventOutput? && t'[o].element == t'[j].element
    {
      assert i < |t|;
      var tx := t[i].record.tx;
      forall j | 0 <= j < i && t'[j].EventWriteBuffer? && t'[j].tx == tx
        ensures exists o :: j < o < i && t'[o].EventOutput? && t'[o].element == t'[j].element
      {
        assert t[j] == t'[j];
        var o :| j < o < i && t[o].EventOutput? && t[o].element == t[j].element;
        assert t'[o] == t[o];
      }
    }
  }

  lemma LemmaAppendCommitPreservesRuleU2(t: seq<TraceEvent>, tx: TxId)
    requires RuleU2_OutputBeforeCommit(t)
    requires forall j :: 0 <= j < |t| && t[j].EventWriteBuffer? && t[j].tx == tx ==>
      exists o :: j < o < |t| && t[o].EventOutput? && t[o].element == t[j].element
    ensures RuleU2_OutputBeforeCommit(t + [EventLog(LogCommit(tx))])
  {
    var t' := t + [EventLog(LogCommit(tx))];
    forall i | 0 <= i < |t'| && t'[i].EventLog? && t'[i].record.LogCommit?
      ensures forall j :: 0 <= j < i && t'[j].EventWriteBuffer? && t'[j].tx == t'[i].record.tx ==>
        exists o :: j < o < i && t'[o].EventOutput? && t'[o].element == t'[j].element
    {
      if i < |t| {
        var txi := t[i].record.tx;
        forall j | 0 <= j < i && t'[j].EventWriteBuffer? && t'[j].tx == txi
          ensures exists o :: j < o < i && t'[o].EventOutput? && t'[o].element == t'[j].element
        {
          assert t[j] == t'[j];
          var o :| j < o < i && t[o].EventOutput? && t[o].element == t[j].element;
          assert t'[o] == t[o];
        }
      } else {
        assert i == |t|;
        forall j | 0 <= j < i && t'[j].EventWriteBuffer? && t'[j].tx == tx
          ensures exists o :: j < o < i && t'[o].EventOutput? && t'[o].element == t'[j].element
        {
          assert t[j] == t'[j];
          var o :| j < o < |t| && t[o].EventOutput? && t[o].element == t[j].element;
          assert t'[o] == t[o];
        }
      }
    }
  }

  lemma LemmaAppendNonWritePreservesTrace(t: seq<TraceEvent>, e: TraceEvent)
    requires !e.EventWriteBuffer?
    requires WriteHasUndoLogBefore(t)
    requires RuleU1_FlushBeforeOutput(t)
    requires e.EventOutput? ==> LastFlushedCount(t) == |ExtractLog(t)|
    requires RuleU2_OutputBeforeCommit(t)
    requires !(e.EventLog? && e.record.LogCommit?)
    ensures var t' := t + [e];
      t <= t' &&
      t'[..|t|] == t &&
      ExtractLog(t') == (if e.EventLog? then ExtractLog(t) + [e.record] else ExtractLog(t)) &&
      LastFlushedCount(t') == (if e.EventFlushLog? then e.flushedCount else LastFlushedCount(t)) &&
      WriteHasUndoLogBefore(t') &&
      RuleU1_FlushBeforeOutput(t') &&
      RuleU2_OutputBeforeCommit(t')
  {
    var t' := t + [e];
    assert t'[..|t|] == t;
    LemmaAppendPreservesRuleU1(t, e);
    LemmaAppendNonCommitPreservesRuleU2(t, e);
  }

  lemma LemmaAppendLogPreservesLifecycle(log: seq<LogRecord>, rec: LogRecord)
    requires StartBeforeEnd(log)
    requires (rec.LogCommit? || rec.LogAbort?) ==> HasStart(log, rec.tx)
    ensures StartBeforeEnd(log + [rec])
    ensures forall tx :: HasStart(log, tx) ==> HasStart(log + [rec], tx)
    ensures forall tx :: HasCommit(log, tx) ==> HasCommit(log + [rec], tx)
    ensures forall tx :: HasAbort(log, tx) ==> HasAbort(log + [rec], tx)
    ensures forall tx :: !HasStart(log, tx) && rec != LogStart(tx) ==> !HasStart(log + [rec], tx)
    ensures forall tx :: !HasCommit(log, tx) && rec != LogCommit(tx) ==> !HasCommit(log + [rec], tx)
    ensures forall tx :: !HasAbort(log, tx) && rec != LogAbort(tx) ==> !HasAbort(log + [rec], tx)
  {
    var log' := log + [rec];
    forall i | 0 <= i < |log'| && (log'[i].LogCommit? || log'[i].LogAbort?)
      ensures exists s :: 0 <= s < i && log'[s] == LogStart(log'[i].tx)
    {
      if i < |log| {
        var s :| 0 <= s < i && log[s] == LogStart(log[i].tx);
        assert log'[s] == LogStart(log'[i].tx);
      } else {
        var s :| 0 <= s < |log| && log[s] == LogStart(rec.tx);
        assert 0 <= s < i && log'[s] == LogStart(log'[i].tx);
      }
    }
    forall tx | HasStart(log, tx)
      ensures HasStart(log', tx)
    {
      var i :| 0 <= i < |log| && log[i] == LogStart(tx);
      assert log'[i] == LogStart(tx);
    }
    forall tx | HasCommit(log, tx)
      ensures HasCommit(log', tx)
    {
      var i :| 0 <= i < |log| && log[i] == LogCommit(tx);
      assert log'[i] == LogCommit(tx);
    }
    forall tx | HasAbort(log, tx)
      ensures HasAbort(log', tx)
    {
      var i :| 0 <= i < |log| && log[i] == LogAbort(tx);
      assert log'[i] == LogAbort(tx);
    }
  }

  // ---------------------------------------------------------------------------
  // String formatting helpers (zero external library dependencies)
  // ---------------------------------------------------------------------------

  function DigitToString(d: nat): string
    requires d < 10
  {
    match d
    case 0 => "0"
    case 1 => "1"
    case 2 => "2"
    case 3 => "3"
    case 4 => "4"
    case 5 => "5"
    case 6 => "6"
    case 7 => "7"
    case 8 => "8"
    case 9 => "9"
  }

  function NatToString(n: nat): string
    decreases n
  {
    if n < 10 then
      DigitToString(n)
    else
      NatToString(n / 10) + DigitToString(n % 10)
  }

  function IntToString(n: int): string
  {
    if n < 0 then "-" + NatToString(-n)
    else NatToString(n)
  }

  function FormatLogRecord(r: LogRecord): string
  {
    match r
    case LogStart(tx) =>
      "<START " + tx + ">"
    case LogUndoUpdate(tx, elem, oldVal) =>
      "<" + tx + ", " + elem + ", " + IntToString(oldVal) + ">"
    case LogCommit(tx) =>
      "<COMMIT " + tx + ">"
    case LogAbort(tx) =>
      "<ABORT " + tx + ">"
  }

  function FormatTraceEvent(e: TraceEvent): string
  {
    match e
    case EventLog(r) =>
      "LOG    " + FormatLogRecord(r)
    case EventRead(tx, elem, val) =>
      "READ   " + tx + "(" + elem + ") => " + IntToString(val)
    case EventWriteBuffer(tx, elem, oldVal, newVal) =>
      "WRITE  " + tx + "(" + elem + "): " + IntToString(oldVal) + " -> " + IntToString(newVal) + " [buffer]"
    case EventUndoRestore(tx, elem, restoredVal) =>
      "UNDO   " + tx + "(" + elem + ") := " + IntToString(restoredVal) + " [buffer]"
    case EventFlushLog(n) =>
      "FLUSH  LOG (up to record #" + NatToString(n) + ")"
    case EventOutput(elem, val) =>
      "OUTPUT " + elem + " = " + IntToString(val) + " [disk]"
  }

  function FormatLog(log: seq<LogRecord>): string
    decreases |log|
  {
    if |log| == 0 then ""
    else if |log| == 1 then FormatLogRecord(log[0])
    else FormatLogRecord(log[0]) + "\n" + FormatLog(log[1..])
  }

  function FormatTrace(trace: seq<TraceEvent>): string
    decreases |trace|
  {
    if |trace| == 0 then ""
    else if |trace| == 1 then FormatTraceEvent(trace[0])
    else FormatTraceEvent(trace[0]) + "\n" + FormatTrace(trace[1..])
  }
}
