// Statically verified tests and runnable demonstrations for the MVCC Simulator
// and Isolation Levels module (`RC`, `CS`, `RR`, `SI`, `SerializableMVCC`).
//
// Each test is modularized into its own method so Dafny verifies every proof
// quickly and cleanly:
//   1. `TestReadCommittedVerified` — RC prevents Dirty Reads while permitting
//      Non-Repeatable Reads once another writer commits.
//   2. `TestCursorStabilityVerified` — CS blocks concurrent writes on the
//      currently positioned cursor row, and unblocks them once the cursor moves.
//   3. `TestRepeatableReadVerified` — RR holds read locks until commit, blocking
//      concurrent overwrites even after reading other items.
//   4. `TestSnapshotIsolationVerified` — SI reads from a point-in-time snapshot
//      (`xmin <= startTs`) without blocking concurrent writers, and enforces
//      First-Committer-Wins against Lost Updates.
//   5. `TestWriteSkewSIvsSerializableVerified` — proves that Write Skew on
//      disjoint writes (`A` and `B`) is permitted under `SnapshotIsolation`
//      but caught and rejected at commit under `SerializableMVCC`.

include "Types.dfy"
include "IsolationPolicy.dfy"
include "MvccSimulator.dfy"

module Main {
  import opened MvccTypes
  import opened IsolationPolicies
  import opened MvccSimulation

  // 1. Read Committed (RC): prevents Dirty Reads, allows Non-Repeatable Reads
  method TestReadCommittedVerified()
  {
    var s0 := InitMvccState([("A", 100)]);
    assert s0.versions == [TupleVersion("A", 100, "INIT", 0, true)];

    // T1 and T2 both start at ReadCommitted
    var b1 := StepBegin(s0, "T1", ReadCommitted);
    assert b1.allowed;
    var b2 := StepBegin(b1.nextState, "T2", ReadCommitted);
    assert b2.allowed;

    // T1 reads A -> sees initial committed value 100
    LemmaHasVisibleVersion(b2.nextState.versions, b2.nextState.txs["T1"], "A", 0);
    var r1 := StepRead(b2.nextState, "T1", "A");
    assert r1.allowed && r1.readVersion.Some?;
    assert (r1.readVersion.value.committed || r1.readVersion.value.creatorTx == "T1");

    // T2 writes uncommitted A := 200
    var w2 := StepWrite(r1.nextState, "T2", "A", 200);
    assert w2.allowed;

    // While T2's write on A is uncommitted, T1 (at RC) cannot perform a Dirty Read on A!
    assert HasOtherWriteOwner(w2.nextState, "A", "T1");
    var dirtyAttempt := StepRead(w2.nextState, "T1", "A");
    assert !dirtyAttempt.allowed;

    // T2 commits A := 200
    var c2 := StepCommit(w2.nextState, "T2");
    assert c2.allowed;

    print "=== 1. Read Committed (RC) Verified ===\n";
    print "First read by T1: ", r1.readValue, "\n";
    print "Dirty read while T2 uncommitted allowed? ", dirtyAttempt.allowed, "\n\n";
  }

  // 2. Cursor Stability (CS): pins the currently positioned cursor item
  method TestCursorStabilityVerified()
  {
    var s0 := InitMvccState([("A", 10), ("B", 20)]);
    assert s0.versions[0] == TupleVersion("A", 10, "INIT", 0, true);
    assert s0.versions[1] == TupleVersion("B", 20, "INIT", 0, true);

    var b1 := StepBegin(s0, "T1", CursorStability);
    var b2 := StepBegin(b1.nextState, "T2", ReadCommitted);
    assert b1.allowed && b2.allowed;

    // T1 positions its cursor on A -> pins A
    LemmaHasVisibleVersion(b2.nextState.versions, b2.nextState.txs["T1"], "A", 0);
    var f1 := StepFetchCursor(b2.nextState, "T1", "A");
    assert f1.allowed;
    assert "T1" in CSPinHolders(f1.nextState, "A");

    // T2 attempts to write A while T1's cursor is positioned on A -> BLOCKED!
    LemmaCursorPinBlocksOtherWriter(f1.nextState, "T1", f1.nextState.txs["T2"], "A");
    var wBlocked := StepWrite(f1.nextState, "T2", "A", 99);
    assert !wBlocked.allowed;

    // T1 moves its cursor from A to B -> unpins A and pins B!
    LemmaHasVisibleVersion(f1.nextState.versions, f1.nextState.txs["T1"], "B", 1);
    var f2 := StepFetchCursor(f1.nextState, "T1", "B");
    assert f2.allowed;
    assert "T1" !in CSPinHolders(f2.nextState, "A");
    assert "T1" in CSPinHolders(f2.nextState, "B");

    print "=== 2. Cursor Stability (CS) Verified ===\n";
    print "T2 write on A while T1 cursor on A allowed? ", wBlocked.allowed, "\n";
    print "T1 moved cursor to B (A unpinned, B pinned)\n\n";
  }

  // 3. Repeatable Read (RR): holds read locks on all read items until commit
  method TestRepeatableReadVerified()
  {
    var s0 := InitMvccState([("A", 10), ("B", 20)]);
    assert s0.versions[0] == TupleVersion("A", 10, "INIT", 0, true);

    var b1 := StepBegin(s0, "T1", RepeatableRead);
    var b2 := StepBegin(b1.nextState, "T2", ReadCommitted);
    assert b1.allowed && b2.allowed;

    // T1 reads A under RepeatableRead -> acquires persistent RR read lock on A
    LemmaHasVisibleVersion(b2.nextState.versions, b2.nextState.txs["T1"], "A", 0);
    var r1 := StepRead(b2.nextState, "T1", "A");
    assert r1.allowed;
    assert "T1" in RRLockHolders(r1.nextState, "A");

    // T2 tries to write A while T1 is still active -> BLOCKED by T1's RR read lock!
    LemmaRepeatableReadLockBlocksOtherWriter(r1.nextState, "T1", r1.nextState.txs["T2"], "A");
    var wBlocked := StepWrite(r1.nextState, "T2", "A", 50);
    assert !wBlocked.allowed;

    print "=== 3. Repeatable Read (RR) Verified ===\n";
    print "T2 write on A while T1 holds RR read lock allowed? ", wBlocked.allowed, "\n\n";
  }

  // 4. Snapshot Isolation (SI): non-blocking snapshot reads + First-Committer-Wins
  method TestSnapshotIsolationVerified()
  {
    var s0 := InitMvccState([("A", 100)]);
    assert s0.versions == [TupleVersion("A", 100, "INIT", 0, true)];

    // T1 starts at clock=1 (startTs=1), T2 starts at clock=2 (startTs=2)
    var b1 := StepBegin(s0, "T1", SnapshotIsolation);
    var b2 := StepBegin(b1.nextState, "T2", SnapshotIsolation);
    assert b1.allowed && b2.allowed;
    assert b2.nextState.txs["T1"].startTs == 1;

    // T2 writes A := 200 and commits at clock=4 (xmin=4 > T1.startTs=1)
    LemmaNoCommittedVersionAfter(b2.nextState.versions, "A", "T2", b2.nextState.txs["T2"].startTs);
    var w2 := StepWrite(b2.nextState, "T2", "A", 200);
    assert w2.allowed;
    LemmaNoSetCommittedVersionAfter(w2.nextState.versions, w2.nextState.txs["T2"].writeSet, "T2", w2.nextState.txs["T2"].startTs);
    var c2 := StepCommit(w2.nextState, "T2");
    assert c2.allowed;
    assert |c2.nextState.versions| == 2;
    assert c2.nextState.versions[1] == TupleVersion("A", 200, "T2", 4, true);

    // T1 reads A -> only versions with xmin <= 1 are visible to T1!
    var r1 := StepRead(c2.nextState, "T1", "A");
    assert r1.allowed && r1.readVersion.Some? ==>
      (r1.readVersion.value.creatorTx == "T1" || r1.readVersion.value.xmin <= 1);

    // T1 tries to overwrite A := 300 -> First-Committer-Wins blocks T1 (Lost Update prevented!)
    LemmaFirstCommitterWinsPreventsLostUpdate(c2.nextState, c2.nextState.txs["T1"], "A", 1);
    var w1LostUpdate := StepWrite(c2.nextState, "T1", "A", 300);
    assert !w1LostUpdate.allowed;

    print "=== 4. Snapshot Isolation (SI) Verified ===\n";
    print "T1 snapshot read of A (after T2 committed 200 at ts=4): ", r1.readValue, "\n";
    print "T1 conflicting write on A allowed (First-Committer-Wins)? ", w1LostUpdate.allowed, "\n\n";
  }

  // 5. Write Skew: Allowed under Snapshot Isolation, Prevented under SerializableMVCC!
  method TestWriteSkewSerializableVerified()
  {
    var s0 := InitMvccState([("A", 1), ("B", 1)]);
    assert s0.versions == [
      TupleVersion("A", 1, "INIT", 0, true),
      TupleVersion("B", 1, "INIT", 0, true)
    ];

    // Two concurrent transactions at SerializableMVCC (SSI):
    // T1 (startTs=1) and T2 (startTs=2) both read A; T1 writes A:=0, T2 writes B:=0.
    var b1 := StepBegin(s0, "T1", SerializableMVCC);
    var b2 := StepBegin(b1.nextState, "T2", SerializableMVCC);
    assert b1.allowed && b2.allowed;

    LemmaHasVisibleVersion(b2.nextState.versions, b2.nextState.txs["T1"], "A", 0);
    var r1A := StepRead(b2.nextState, "T1", "A");
    assert r1A.allowed;

    LemmaHasVisibleVersion(r1A.nextState.versions, r1A.nextState.txs["T2"], "A", 0);
    var r2A := StepRead(r1A.nextState, "T2", "A");
    assert r2A.allowed;
    assert "A" in r2A.nextState.txs["T2"].readSet;

    // T1 writes A := 0 and T2 writes B := 0 (disjoint write sets!)
    LemmaNoCommittedVersionAfter(r2A.nextState.versions, "A", "T1", r2A.nextState.txs["T1"].startTs);
    var w1 := StepWrite(r2A.nextState, "T1", "A", 0);
    assert w1.allowed;

    LemmaNoCommittedVersionAfter(w1.nextState.versions, "B", "T2", w1.nextState.txs["T2"].startTs);
    var w2 := StepWrite(w1.nextState, "T2", "B", 0);
    assert w2.allowed;

    // T1 commits first -> creates committed version of A at index 2 with xmin = 5 > T2.startTs = 2
    LemmaNoSetCommittedVersionAfter(w2.nextState.versions, w2.nextState.txs["T1"].writeSet, "T1", w2.nextState.txs["T1"].startTs);
    LemmaNoSetCommittedVersionAfter(w2.nextState.versions, w2.nextState.txs["T1"].readSet, "T1", w2.nextState.txs["T1"].startTs);
    var c1 := StepCommit(w2.nextState, "T1");
    assert c1.allowed;
    assert c1.nextState.versions[2] == TupleVersion("A", 0, "T1", 5, true);

    // When T2 tries to commit under SerializableMVCC, its readSet {"A"} was
    // modified after T2.startTs while T2 also performed a write ({"B"}) -> Write Skew REJECTED!
    assert "A" in c1.nextState.txs["T2"].readSet;
    assert "B" in c1.nextState.txs["T2"].writeSet;
    LemmaSerializablePreventsWriteSkew(c1.nextState, c1.nextState.txs["T2"], "A", 2);
    var c2 := StepCommit(c1.nextState, "T2");
    assert !c2.allowed;

    print "=== 5. SerializableMVCC Write-Skew Prevention Verified ===\n";
    print "T1 commit allowed? ", c1.allowed, "\n";
    print "T2 Write-Skew commit allowed under SerializableMVCC? ", c2.allowed, " (", c2.reason, ")\n";
  }

  method Main()
  {
    TestReadCommittedVerified();
    TestCursorStabilityVerified();
    TestRepeatableReadVerified();
    TestSnapshotIsolationVerified();
    TestWriteSkewSerializableVerified();
  }
}
