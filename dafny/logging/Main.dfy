// Runnable demonstrations and verified test cases for the Dafny Undo Logging
// module using Dispatch.

include "Types.dfy"
include "Dispatch.dfy"
include "UndoLogger.dfy"
include "UndoRecovery.dfy"

module Main {
  import opened LoggingTypes
  import opened LoggingDispatch
  import opened UndoLogging
  import opened UndoRecovery

  // ---------------------------------------------------------------------------
  // Statically verified unit tests (proved by Dafny at compile/verify time)
  // ---------------------------------------------------------------------------

  // Classic Garcia-Molina example: T1 doubles A and B (initial A=8, B=8).
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

  // Demonstrates polymorphic dispatch via Schedule.Run.
  method DemoSingleTransactionSchedule()
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

    var generatedLog, generatedTrace, errs := schedule.Run(logger);

    expect errs == [];
    expect generatedLog == [
      LogStart("T1"),
      LogUndoUpdate("T1", "A", 8),
      LogUndoUpdate("T1", "B", 8),
      LogCommit("T1")
    ];
    expect "A" in logger.GetDisk() && logger.GetDisk()["A"] == 16;
    expect "B" in logger.GetDisk() && logger.GetDisk()["B"] == 16;

    print "=== Demo 1: Single Transaction (T1 commits) ===\n";
    print "--- Undo Log ---\n", FormatLog(generatedLog), "\n";
    print "--- Execution Trace (WAL + OUTPUT order) ---\n", FormatTrace(generatedTrace), "\n\n";
  }

  // Demonstrates two interleaved transactions: T1 commits, T2 aborts.
  method DemoInterleavedCommitAndAbort()
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

    print "=== Demo 2: Interleaved Transactions (T1 commits, T2 aborts) ===\n";
    print "--- Undo Log ---\n", FormatLog(generatedLog), "\n";
    print "--- Execution Trace ---\n", FormatTrace(generatedTrace), "\n\n";
  }

  // Demonstrates crash recovery when T1 commits but T2 crashes mid-execution.
  method DemoCrashRecovery()
  {
    var initialDb: DatabaseState := map["A" := 10, "B" := 20];
    var ops: seq<Operation> := [
      StartOp("T1"),
      StartOp("T2"),
      WriteOp("T1", "A", 50),
      WriteOp("T2", "B", 999),
      CommitOp("T1")
      // System crashes before T2 commits!
      // Note: T1's COMMIT flushed the log up to <COMMIT T1>, which already
      // includes <T2, B, 20>. Even if B=999 reached disk, Undo recovery
      // restores B to 20 while preserving T1's committed A=50.
    ];
    var schedule := Schedule(ops);
    var logger := new UndoLogger(initialDb);

    var generatedLog, _, errs := schedule.Run(logger);
    expect errs == [];

    var flushedLog := logger.GetFlushedLog();
    // Simulate a dirty write of B=999 reaching disk before the crash.
    var diskAtCrash := logger.GetDisk()["B" := 999];
    var recoveredDisk, recoveryAborts := RecoverFromCrash(diskAtCrash, flushedLog);

    expect "A" in recoveredDisk && recoveredDisk["A"] == 50;
    expect "B" in recoveredDisk && recoveredDisk["B"] == 20;
    expect recoveryAborts == [LogAbort("T2")];

    print "=== Demo 3: Crash Recovery (T1 committed, T2 crashed) ===\n";
    print "--- Flushed Undo Log ---\n", FormatLog(flushedLog), "\n";
    print "--- Recovery Abort Records ---\n", FormatLog(recoveryAborts), "\n";
    print "Recovered disk: A=", recoveredDisk["A"], ", B=", recoveredDisk["B"], "\n\n";
  }

  // Demonstrates graceful error handling for invalid schedule operations.
  method DemoInvalidSchedule()
  {
    var initialDb: DatabaseState := map["A" := 10];
    var ops: seq<Operation> := [
      WriteOp("T1", "A", 20),   // Error: T1 not started
      StartOp("T1"),
      WriteOp("T1", "Z", 99),   // Error: Z unknown
      CommitOp("T1")
    ];
    var schedule := Schedule(ops);
    var logger := new UndoLogger(initialDb);

    var generatedLog, _, errs := schedule.Run(logger);
    expect |errs| == 2;
    expect generatedLog == [LogStart("T1"), LogCommit("T1")];

    print "=== Demo 4: Invalid Operations Handling ===\n";
    print "--- Undo Log ---\n", FormatLog(generatedLog), "\n";
    print "Errors captured: ", |errs|, "\n";
  }

  method Main()
  {
    TestSingleTransactionUndoVerified();
    DemoSingleTransactionSchedule();
    DemoInterleavedCommitAndAbort();
    DemoCrashRecovery();
    DemoInvalidSchedule();
  }
}
