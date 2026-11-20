// Runnable demonstrations and verified test cases for the Dafny Undo & Redo
// Logging modules using Dispatch and shared LoggingStrategy / RecoveryStrategy
// interfaces.

include "Types.dfy"
include "Dispatch.dfy"
include "UndoLogger.dfy"
include "UndoRecovery.dfy"
include "RedoLogger.dfy"
include "RedoRecovery.dfy"

module Main {
  import opened LoggingTypes
  import opened LoggingDispatch
  import opened UndoLogging
  import UndoRecovery
  import opened RedoLogging
  import RedoRecovery

  // ---------------------------------------------------------------------------
  // Statically verified unit tests (proved by Dafny at compile/verify time)
  // ---------------------------------------------------------------------------

  // Classic Garcia-Molina example (Undo): T1 doubles A and B (initial A=8, B=8).
  method TestSingleTransactionUndoVerified()
  {
    var initialDb: DatabaseState := map["A" := 8, "B" := 8];
    var logger := new UndoLogger(initialDb);

    logger.VisitStart("T1");
    assert logger.log == [LogStart("T1")];

    logger.VisitRead("T1", "A");
    assert logger.log == [LogStart("T1")];

    logger.VisitWrite("T1", "A", 16);
    assert logger.log == [LogStart("T1"), LogUndoUpdate("T1", "A", 8)];
    assert logger.buffer["A"] == 16 && logger.disk["A"] == 8;

    logger.VisitRead("T1", "B");
    logger.VisitWrite("T1", "B", 16);
    assert logger.log == [
      LogStart("T1"),
      LogUndoUpdate("T1", "A", 8),
      LogUndoUpdate("T1", "B", 8)
    ];

    logger.VisitCommit("T1");
    assert logger.log == [
      LogStart("T1"),
      LogUndoUpdate("T1", "A", 8),
      LogUndoUpdate("T1", "B", 8),
      LogCommit("T1")
    ];
    assert logger.flushedLogLen == 4;
    assert logger.errors == [];
    assert "T1" in logger.committedTxs;
  }

  // Classic Garcia-Molina example (Redo): T1 doubles A and B (initial A=8, B=8).
  method TestSingleTransactionRedoVerified()
  {
    var initialDb: DatabaseState := map["A" := 8, "B" := 8];
    var logger := new RedoLogger(initialDb);

    logger.VisitStart("T1");
    assert logger.log == [LogStart("T1")];

    logger.VisitRead("T1", "A");
    assert logger.log == [LogStart("T1")];

    logger.VisitWrite("T1", "A", 16);
    assert logger.log == [LogStart("T1"), LogRedoUpdate("T1", "A", 16)];
    assert logger.buffer["A"] == 16 && logger.disk["A"] == 8;

    logger.VisitRead("T1", "B");
    logger.VisitWrite("T1", "B", 16);
    assert logger.log == [
      LogStart("T1"),
      LogRedoUpdate("T1", "A", 16),
      LogRedoUpdate("T1", "B", 16)
    ];

    logger.VisitCommit("T1");
    assert logger.log == [
      LogStart("T1"),
      LogRedoUpdate("T1", "A", 16),
      LogRedoUpdate("T1", "B", 16),
      LogCommit("T1")
    ];
    assert logger.flushedLogLen == 4;
    assert logger.errors == [];
    assert "T1" in logger.committedTxs;
  }

  // Polymorphic runner accepting any LoggingStrategy (UndoLogger or RedoLogger).
  method RunWithAnyStrategy(schedule: Schedule, strategy: LoggingStrategy)
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
    logResult, traceResult, errorResult := schedule.Run(strategy);
  }

  // ---------------------------------------------------------------------------
  // Undo Logging Demos
  // ---------------------------------------------------------------------------

  method DemoSingleTransactionUndo()
  {
    var initialDb: DatabaseState := map["A" := 8, "B" := 8];
    var ops: seq<Operation> := [
      StartOp("T1"),
      ReadOp("T1", "A"),
      WriteOp("T1", "A", 16),
      ReadOp("T1", "B"),
      WriteOp("T1", "B", 16),
      CommitOp("T1")
    ];
    var schedule := Schedule(ops);
    var logger := new UndoLogger(initialDb);

    var generatedLog, generatedTrace, errs := RunWithAnyStrategy(schedule, logger);

    expect errs == [];
    expect generatedLog == [
      LogStart("T1"),
      LogUndoUpdate("T1", "A", 8),
      LogUndoUpdate("T1", "B", 8),
      LogCommit("T1")
    ];
    expect "A" in logger.GetDisk() && logger.GetDisk()["A"] == 16;
    expect "B" in logger.GetDisk() && logger.GetDisk()["B"] == 16;

    print "=== Demo 1 (Undo): Single Transaction (T1 commits) ===\n";
    print "--- Undo Log ---\n", FormatLog(generatedLog), "\n";
    print "--- Execution Trace (WAL + OUTPUT order) ---\n", FormatTrace(generatedTrace), "\n\n";
  }

  method DemoInterleavedCommitAndAbortUndo()
  {
    var initialDb: DatabaseState := map["A" := 10, "B" := 20];
    var ops: seq<Operation> := [
      StartOp("T1"),
      StartOp("T2"),
      WriteOp("T1", "A", 15),
      WriteOp("T2", "B", 99),
      CommitOp("T1"),
      AbortOp("T2")
    ];
    var schedule := Schedule(ops);
    var logger := new UndoLogger(initialDb);

    var generatedLog, generatedTrace, errs := schedule.Run(logger);

    expect errs == [];
    expect generatedLog == [
      LogStart("T1"),
      LogStart("T2"),
      LogUndoUpdate("T1", "A", 10),
      LogUndoUpdate("T2", "B", 20),
      LogCommit("T1"),
      LogAbort("T2")
    ];
    expect "A" in logger.GetDisk() && logger.GetDisk()["A"] == 15;
    expect "B" in logger.GetDisk() && logger.GetDisk()["B"] == 20;
    expect "A" in logger.GetBuffer() && logger.GetBuffer()["A"] == 15;
    expect "B" in logger.GetBuffer() && logger.GetBuffer()["B"] == 20;

    print "=== Demo 2 (Undo): Interleaved Transactions (T1 commits, T2 aborts) ===\n";
    print "--- Undo Log ---\n", FormatLog(generatedLog), "\n";
    print "--- Execution Trace ---\n", FormatTrace(generatedTrace), "\n\n";
  }

  method DemoUndoCrashRecovery()
  {
    var initialDb: DatabaseState := map["A" := 10, "B" := 20];
    var ops: seq<Operation> := [
      StartOp("T1"),
      StartOp("T2"),
      WriteOp("T1", "A", 50),
      WriteOp("T2", "B", 999),
      CommitOp("T1")
    ];
    var schedule := Schedule(ops);
    var logger := new UndoLogger(initialDb);

    var _, _, errs := schedule.Run(logger);
    expect errs == [];

    var flushedLog := logger.GetFlushedLog();
    var diskAtCrash := logger.GetDisk()["B" := 999];
    var recovery: RecoveryStrategy := new UndoRecovery.UndoRecoveryStrategy();
    var recoveredDisk, recoveryAborts := recovery.RecoverFromCrash(diskAtCrash, flushedLog);

    expect "A" in recoveredDisk && recoveredDisk["A"] == 50;
    expect "B" in recoveredDisk && recoveredDisk["B"] == 20;
    expect recoveryAborts == [LogAbort("T2")];

    print "=== Demo 3 (Undo): Crash Recovery (T1 committed, T2 crashed) ===\n";
    print "--- Flushed Undo Log ---\n", FormatLog(flushedLog), "\n";
    print "--- Recovery Abort Records ---\n", FormatLog(recoveryAborts), "\n";
    print "Recovered disk: A=", recoveredDisk["A"], ", B=", recoveredDisk["B"], "\n\n";
  }

  // ---------------------------------------------------------------------------
  // Redo Logging Demos
  // ---------------------------------------------------------------------------

  method DemoSingleTransactionRedo()
  {
    var initialDb: DatabaseState := map["A" := 8, "B" := 8];
    var ops: seq<Operation> := [
      StartOp("T1"),
      ReadOp("T1", "A"),
      WriteOp("T1", "A", 16),
      ReadOp("T1", "B"),
      WriteOp("T1", "B", 16),
      CommitOp("T1")
    ];
    var schedule := Schedule(ops);
    var logger := new RedoLogger(initialDb);

    var generatedLog, generatedTrace, errs := RunWithAnyStrategy(schedule, logger);

    expect errs == [];
    expect generatedLog == [
      LogStart("T1"),
      LogRedoUpdate("T1", "A", 16),
      LogRedoUpdate("T1", "B", 16),
      LogCommit("T1")
    ];
    expect "A" in logger.GetDisk() && logger.GetDisk()["A"] == 16;
    expect "B" in logger.GetDisk() && logger.GetDisk()["B"] == 16;

    print "=== Demo 4 (Redo): Single Transaction (T1 commits) ===\n";
    print "--- Redo Log ---\n", FormatLog(generatedLog), "\n";
    print "--- Execution Trace (WAL + COMMIT + FLUSH before OUTPUT) ---\n", FormatTrace(generatedTrace), "\n\n";
  }

  method DemoRedoCrashRecovery()
  {
    var initialDb: DatabaseState := map["A" := 10, "B" := 20];
    var ops: seq<Operation> := [
      StartOp("T1"),
      StartOp("T2"),
      WriteOp("T1", "A", 50),
      WriteOp("T2", "B", 999),
      CommitOp("T1")
    ];
    var schedule := Schedule(ops);
    var logger := new RedoLogger(initialDb);

    var _, _, errs := schedule.Run(logger);
    expect errs == [];

    var flushedLog := logger.GetFlushedLog();
    // Simulate a crash right after <COMMIT T1> was flushed to disk, BEFORE
    // T1's OUTPUT(A) reached disk. Redo recovery replays T1's A := 50 and
    // ignores uncommitted T2 (leaving B = 20) while emitting <ABORT T2>.
    var diskAtCrash := initialDb;
    var recovery: RecoveryStrategy := new RedoRecovery.RedoRecoveryStrategy();
    var recoveredDisk, recoveryAborts := recovery.RecoverFromCrash(diskAtCrash, flushedLog);

    expect "A" in recoveredDisk && recoveredDisk["A"] == 50;
    expect "B" in recoveredDisk && recoveredDisk["B"] == 20;
    expect recoveryAborts == [LogAbort("T2")];

    print "=== Demo 5 (Redo): Crash Recovery (T1 committed before OUTPUT, T2 crashed) ===\n";
    print "--- Flushed Redo Log ---\n", FormatLog(flushedLog), "\n";
    print "--- Recovery Abort Records ---\n", FormatLog(recoveryAborts), "\n";
    print "Recovered disk: A=", recoveredDisk["A"], ", B=", recoveredDisk["B"], "\n\n";
  }

  method Main()
  {
    TestSingleTransactionUndoVerified();
    TestSingleTransactionRedoVerified();
    DemoSingleTransactionUndo();
    DemoInterleavedCommitAndAbortUndo();
    DemoUndoCrashRecovery();
    DemoSingleTransactionRedo();
    DemoRedoCrashRecovery();
  }
}
