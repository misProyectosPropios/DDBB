// Dispatch (Visitor) protocol connecting Schedule Operations and Logging
// Strategies.
//
// Call flow for each schedule operation:
//   Schedule.GenerateLog(strategy)
//     -> strategy.Process(op)        [1st dispatch: LoggingStrategy receives op]
//       -> op.Accept(strategy)       [2nd dispatch: Operation calls matching Visit*]
//         -> strategy.Visit*(...)    [executes strategy-specific logging logic]
//
// Operations and Schedule are immutable Dafny `datatype`s so callers can build
// schedules directly as pure expressions (`[StartOp("T1"), WriteOp("T1", "A", 16), ...]`)
// without heap allocation (`new`), while concrete logging protocols (Undo,
// Redo, Undo/Redo, Quiescent & Non-Quiescent Checkpointing) extend
// `LoggingStrategy`.

include "Types.dfy"

module LoggingDispatch {
  import opened LoggingTypes

  // ---------------------------------------------------------------------------
  // Operation datatype (visited elements)
  // ---------------------------------------------------------------------------

  datatype Operation =
    | StartOp(tx: TxId)
    | ReadOp(tx: TxId, element: ElementId)
    | WriteOp(tx: TxId, element: ElementId, newValue: Value)
    | CommitOp(tx: TxId)
    | AbortOp(tx: TxId)
  {
    // Dispatches this operation to the corresponding Visit* method on `visitor`.
    method Accept(visitor: LoggingStrategy)
      requires visitor.Valid()
      modifies visitor
      ensures visitor.Valid()
      ensures old(visitor.log) <= visitor.log
      ensures old(visitor.trace) <= visitor.trace
    {
      match this {
        case StartOp(tx) => visitor.VisitStart(tx);
        case ReadOp(tx, element) => visitor.VisitRead(tx, element);
        case WriteOp(tx, element, newValue) => visitor.VisitWrite(tx, element, newValue);
        case CommitOp(tx) => visitor.VisitCommit(tx);
        case AbortOp(tx) => visitor.VisitAbort(tx);
      }
    }
  }

  // ---------------------------------------------------------------------------
  // LoggingStrategy trait (visitor)
  // ---------------------------------------------------------------------------

  trait LoggingStrategy extends object {
    var log: seq<LogRecord>
    var trace: seq<TraceEvent>
    var errors: seq<string>

    ghost predicate Valid()
      reads this

    method VisitStart(tx: TxId)
      requires Valid()
      modifies this
      ensures Valid()
      ensures old(log) <= log
      ensures old(trace) <= trace

    method VisitRead(tx: TxId, element: ElementId)
      requires Valid()
      modifies this
      ensures Valid()
      ensures old(log) <= log
      ensures old(trace) <= trace

    method VisitWrite(tx: TxId, element: ElementId, newValue: Value)
      requires Valid()
      modifies this
      ensures Valid()
      ensures old(log) <= log
      ensures old(trace) <= trace

    method VisitCommit(tx: TxId)
      requires Valid()
      modifies this
      ensures Valid()
      ensures old(log) <= log
      ensures old(trace) <= trace

    method VisitAbort(tx: TxId)
      requires Valid()
      modifies this
      ensures Valid()
      ensures old(log) <= log
      ensures old(trace) <= trace

    // Entry point for dispatch: receives an Operation and hands `this`
    // to `op.Accept(this)`, which dispatches back to the specific Visit* method.
    method Process(op: Operation)
      requires Valid()
      modifies this
      ensures Valid()
      ensures old(log) <= log
      ensures old(trace) <= trace
    {
      op.Accept(this);
    }

    function GetLog(): seq<LogRecord>
      reads this
    {
      log
    }

    function GetTrace(): seq<TraceEvent>
      reads this
    {
      trace
    }

    function GetErrors(): seq<string>
      reads this
    {
      errors
    }
  }

  // ---------------------------------------------------------------------------
  // Schedule runner
  // ---------------------------------------------------------------------------

  datatype Schedule = Schedule(operations: seq<Operation>) {
    // Executes the schedule using the provided LoggingStrategy via dispatch
    // and returns the generated log.
    method GenerateLog(strategy: LoggingStrategy) returns (result: seq<LogRecord>)
      requires strategy.Valid()
      modifies strategy
      ensures strategy.Valid()
      ensures old(strategy.log) <= strategy.log
      ensures old(strategy.trace) <= strategy.trace
      ensures result == strategy.log
    {
      var i := 0;
      while i < |operations|
        invariant 0 <= i <= |operations|
        invariant strategy.Valid()
        invariant old(strategy.log) <= strategy.log
        invariant old(strategy.trace) <= strategy.trace
        decreases |operations| - i
      {
        strategy.Process(operations[i]);
        i := i + 1;
      }
      result := strategy.GetLog();
    }

    // Runs the schedule and returns the generated log, full execution trace,
    // and any schedule validation errors.
    method Run(strategy: LoggingStrategy)
      returns (logResult: seq<LogRecord>, traceResult: seq<TraceEvent>, errorResult: seq<string>)
      requires strategy.Valid()
      modifies strategy
      ensures strategy.Valid()
      ensures old(strategy.log) <= strategy.log
      ensures old(strategy.trace) <= strategy.trace
      ensures logResult == strategy.log
      ensures traceResult == strategy.trace
      ensures errorResult == strategy.errors
    {
      logResult := GenerateLog(strategy);
      traceResult := strategy.GetTrace();
      errorResult := strategy.GetErrors();
    }
  }
}
