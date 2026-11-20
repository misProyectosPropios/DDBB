// Runnable demonstrations and verified test cases for Undo & Redo Logging
// composed with NoCheckpoint, Quiescent, and Non-Quiescent checkpoint strategies.

include "Types.dfy"
include "Checkpointing.dfy"
include "Dispatch.dfy"
include "UndoLogger.dfy"
include "UndoRecovery.dfy"
include "RedoLogger.dfy"
include "RedoRecovery.dfy"

module Main {
  import opened LoggingTypes
  import opened Checkpointing
  import opened LoggingDispatch
  import opened UndoLogging
  import UndoRecovery
  import opened RedoLogging
  import RedoRecovery

  // ---------------------------------------------------------------------------
  // Statically verified unit tests (proved by Dafny at compile/verify time)
  // ---------------------------------------------------------------------------

  // Classic Garcia-Molina example (Undo, no checkpoints): T1 doubles A and B.
  method TestSingleTransactionUndoVerified()
  {
    var initialDb: DatabaseState := map["A" := 8, "B" := 8];
    var ckpt := new NoCheckpointStrategy();
    var logger := new UndoLogger(initialDb, ckpt);

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

  // Classic Garcia-Molina example (Redo, no checkpoints): T1 doubles A and B.
  method TestSingleTransactionRedoVerified()
  {
    var initialDb: DatabaseState := map["A" := 8, "B" := 8];
    var ckpt := new NoCheckpointStrategy();
    var logger := new RedoLogger(initialDb, ckpt);

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

  // Polymorphic runner accepting any LoggingStrategy (Undo or Redo with any
  // CheckpointStrategy).
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
  // Quiescent vs. Non-Quiescent Checkpointing Demos (Undo & Redo)
  // ---------------------------------------------------------------------------

  // Quiescent Undo: CheckpointOp stops new transactions (T2 is rejected while
  // T1 is still active), waits for T1 to finish, emits <CKPT>, then lets T3 start.
  method DemoQuiescentUndo()
  {
    var initialDb: DatabaseState := map["X" := 5, "Y" := 10];
    var ops: seq<Operation> := [
      StartOp("T1"),
      WriteOp("T1", "X", 12),
      CheckpointOp,           // Enters draining mode (T1 still active)
      StartOp("T2"),          // Blocked by quiescent checkpoint!
      CommitOp("T1"),         // Last active tx finishes -> emits <CKPT>
      StartOp("T3"),          // Allowed again after <CKPT>
      WriteOp("T3", "Y", 20),
      CommitOp("T3")
    ];
    var schedule := Schedule(ops);
    var quiescent := new QuiescentCheckpointStrategy();
    var logger := new UndoLogger(initialDb, quiescent);

    var generatedLog, generatedTrace, errs := RunWithAnyStrategy(schedule, logger);

    expect |errs| == 1;
    expect generatedLog == [
      LogStart("T1"),
      LogUndoUpdate("T1", "X", 5),
      LogCommit("T1"),
      LogCheckpoint,
      LogStart("T3"),
      LogUndoUpdate("T3", "Y", 10),
      LogCommit("T3")
    ];

    print "=== Demo 1: Quiescent Undo Checkpointing ===\n";
    print "--- Undo Log ---\n", FormatLog(generatedLog), "\n";
    print "Blocked operations: ", |errs|, "\n";
    print "--- Trace ---\n", FormatTrace(generatedTrace), "\n\n";
  }

  // Non-Quiescent Undo: CheckpointOp emits <START CKPT(T1)>, allows T2 to start
  // concurrently, and emits <END CKPT> as soon as T1 finishes (even while T2 runs).
  method DemoNonQuiescentUndo()
  {
    var initialDb: DatabaseState := map["X" := 5, "Y" := 10];
    var ops: seq<Operation> := [
      StartOp("T1"),
      WriteOp("T1", "X", 12),
      CheckpointOp,           // Emits <START CKPT(T1)>
      StartOp("T2"),          // Allowed! Non-quiescent does not block T2
      WriteOp("T2", "Y", 99),
      CommitOp("T1"),         // T1 (the watched tx) finishes -> emits <END CKPT>
      CommitOp("T2")
    ];
    var schedule := Schedule(ops);
    var nonQuiescent := new NonQuiescentCheckpointStrategy();
    var logger := new UndoLogger(initialDb, nonQuiescent);

    var generatedLog, generatedTrace, errs := RunWithAnyStrategy(schedule, logger);

    expect errs == [];
    expect generatedLog == [
      LogStart("T1"),
      LogUndoUpdate("T1", "X", 5),
      LogStartCheckpoint(["T1"]),
      LogStart("T2"),
      LogUndoUpdate("T2", "Y", 10),
      LogCommit("T1"),
      LogEndCheckpoint,
      LogCommit("T2")
    ];

    print "=== Demo 2: Non-Quiescent Undo Checkpointing ===\n";
    print "--- Undo Log ---\n", FormatLog(generatedLog), "\n";
    print "--- Trace ---\n", FormatTrace(generatedTrace), "\n\n";
  }

  // Non-Quiescent Redo: CheckpointOp emits <START CKPT(T1)> and <END CKPT>
  // immediately (committed updates are already on disk), while T1 and T2 keep running.
  method DemoNonQuiescentRedo()
  {
    var initialDb: DatabaseState := map["X" := 5, "Y" := 10];
    var ops: seq<Operation> := [
      StartOp("T1"),
      WriteOp("T1", "X", 12),
      CheckpointOp,           // Emits <START CKPT(T1)> and <END CKPT> immediately
      StartOp("T2"),
      WriteOp("T2", "Y", 25),
      CommitOp("T1"),
      CommitOp("T2")
    ];
    var schedule := Schedule(ops);
    var nonQuiescent := new NonQuiescentCheckpointStrategy();
    var logger := new RedoLogger(initialDb, nonQuiescent);

    var generatedLog, generatedTrace, errs := RunWithAnyStrategy(schedule, logger);

    expect errs == [];
    expect generatedLog == [
      LogStart("T1"),
      LogRedoUpdate("T1", "X", 12),
      LogStartCheckpoint(["T1"]),
      LogEndCheckpoint,
      LogStart("T2"),
      LogRedoUpdate("T2", "Y", 25),
      LogCommit("T1"),
      LogCommit("T2")
    ];

    print "=== Demo 3: Non-Quiescent Redo Checkpointing ===\n";
    print "--- Redo Log ---\n", FormatLog(generatedLog), "\n";
    print "--- Trace ---\n", FormatTrace(generatedTrace), "\n\n";
  }

  // Crash recovery with checkpoints (Undo & Redo).
  method DemoRecoveryWithCheckpoints()
  {
    var initialDb: DatabaseState := map["A" := 10, "B" := 20];
    var ops: seq<Operation> := [
      StartOp("T1"),
      WriteOp("T1", "A", 50),
      CommitOp("T1"),
      CheckpointOp,           // Quiescent <CKPT> while idle
      StartOp("T2"),
      WriteOp("T2", "B", 999)
      // Crash before T2 commits!
    ];
    var schedule := Schedule(ops);

    // Undo crash recovery stops early at <CKPT>
    var undoCkpt := new QuiescentCheckpointStrategy();
    var undoLogger := new UndoLogger(initialDb, undoCkpt);
    var _, _, uErrs := schedule.Run(undoLogger);
    expect uErrs == [];
    var undoFlushed := undoLogger.GetFlushedLog();
    var undoRec: RecoveryStrategy := new UndoRecovery.UndoRecoveryStrategy();
    var uDisk, uAborts := undoRec.RecoverFromCrash(undoLogger.GetDisk(), undoFlushed);
    expect "A" in uDisk && uDisk["A"] == 50;
    expect "B" in uDisk && uDisk["B"] == 20;

    // Redo crash recovery starts forward replay at <CKPT>
    var redoCkpt := new QuiescentCheckpointStrategy();
    var redoLogger := new RedoLogger(initialDb, redoCkpt);
    var _, _, rErrs := schedule.Run(redoLogger);
    expect rErrs == [];
    var redoFlushed := redoLogger.GetFlushedLog();
    var redoRec: RecoveryStrategy := new RedoRecovery.RedoRecoveryStrategy();
    var rDisk, rAborts := redoRec.RecoverFromCrash(redoLogger.GetDisk(), redoFlushed);
    expect "A" in rDisk && rDisk["A"] == 50;
    expect "B" in rDisk && rDisk["B"] == 20;

    print "=== Demo 4: Crash Recovery with Quiescent <CKPT> ===\n";
    print "Undo recovered: A=", uDisk["A"], ", B=", uDisk["B"], " (aborts: ", |uAborts|, ")\n";
    print "Redo recovered: A=", rDisk["A"], ", B=", rDisk["B"], " (aborts: ", |rAborts|, ")\n\n";
  }

  method Main()
  {
    TestSingleTransactionUndoVerified();
    TestSingleTransactionRedoVerified();
    DemoQuiescentUndo();
    DemoNonQuiescentUndo();
    DemoNonQuiescentRedo();
    DemoRecoveryWithCheckpoints();
  }
}
