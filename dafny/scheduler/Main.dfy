// Runnable demonstrations and statically verified tests for the Pessimistic
// Scheduler with MultipleLockPolicy (Shared/Exclusive 2PL) and
// Conflict-Serializability checking.

include "Types.dfy"
include "LockPolicy.dfy"
include "Serializability.dfy"
include "PessimisticScheduler.dfy"

module Main {
  import opened SchedulerTypes
  import opened LockPolicies
  import opened Serializability
  import opened PessimisticScheduling

  // ---------------------------------------------------------------------------
  // Statically verified checks
  // ---------------------------------------------------------------------------

  // Verifies that MultipleLockPolicy permits Shared+Shared, rejects Exclusive
  // while another transaction holds Shared, allows S->X upgrade once the other
  // unlocks, and rejects lock acquisition after unlock (2PL).
  method TestMultipleLockPolicyVerified()
  {
    var policy := new MultipleLockPolicy();
    var s0 := EmptyLockTableState();

    // T1 acquires Shared lock on A
    var d1 := policy.Dispatch(s0, SL("T1", "A"));
    assert d1.allowed;
    assert d1.nextState == SetLock(s0, "T1", "A", Shared);

    // T2 also acquires Shared lock on A (compatible!)
    var d2 := policy.Dispatch(d1.nextState, SL("T2", "A"));
    assert d2.allowed;
    assert d2.nextState == SetLock(d1.nextState, "T2", "A", Shared);
    assert "T2" in HoldersOf(d2.nextState, "A") && HoldersOf(d2.nextState, "A")["T2"] == Shared;

    // T1 tries to upgrade to Exclusive on A while T2 still holds Shared -> rejected
    var d3 := policy.Dispatch(d2.nextState, XL("T1", "A"));
    assert !policy.Compatible(Shared, Exclusive);
    assert !d3.allowed;

    // T2 unlocks A -> now T1 can upgrade A from Shared to Exclusive!
    assert HoldsLock(d2.nextState, "T2", "A");
    var d4 := policy.Dispatch(d2.nextState, U("T2", "A"));
    assert d4.allowed;
    assert d4.nextState == RemoveLock(d2.nextState, "T2", "A");
    var d5 := policy.Dispatch(d4.nextState, XL("T1", "A"));
    assert d5.allowed;

    // T2 tries to lock B after unlocking A -> 2PL violation!
    assert "T2" in d5.nextState.shrinkingTxs;
    var d6 := policy.Dispatch(d5.nextState, SL("T2", "B"));
    assert !d6.allowed;
  }

  // ---------------------------------------------------------------------------
  // Runnable Demos
  // ---------------------------------------------------------------------------

  // Demo 1: Valid interleaved S/X 2PL schedule that is conflict-serializable
  // to (T1 followed by T2), and NOT serializable to (T2 followed by T1).
  method DemoValidScheduleAndSerializability()
  {
    var policy := new MultipleLockPolicy();
    var scheduler := new PessimisticScheduler(policy);

    var interleaved: seq<SchedOp> := [
      SL("T1", "A"),
      R("T1", "A"),
      SL("T2", "A"),
      R("T2", "A"),
      U("T2", "A"),
      XL("T1", "A"),   // Valid S -> X upgrade once T2 releases A
      W("T1", "A"),
      U("T1", "A"),
      C("T1"),
      C("T2")
    ];

    // Conflict in `interleaved`: R(T2, A) precedes W(T1, A) => T2 -> T1!
    var serialT2ThenT1: seq<SchedOp> := [
      R("T2", "A"),
      R("T1", "A"),
      W("T1", "A")
    ];
    var serialT1ThenT2: seq<SchedOp> := [
      R("T1", "A"),
      W("T1", "A"),
      R("T2", "A")
    ];

    var valid, serializableToT2T1, finalState, errs :=
      scheduler.ValidateAndCheckSerializable(interleaved, serialT2ThenT1);
    var serializableToT1T2 :=
      scheduler.IsSerializableTo(interleaved, serialT1ThenT2);

    expect valid && errs == [];
    expect AllLocksReleased(finalState);
    expect serializableToT2T1;
    expect !serializableToT1T2;

    print "=== Demo 1: Valid Multiple-Mode 2PL Schedule ===\n";
    print "Locks valid: ", valid, "\n";
    print "Serializable to (T2 -> T1): ", serializableToT2T1, "\n";
    print "Serializable to (T1 -> T2): ", serializableToT1T2, "\n\n";
  }

  // Demo 2: Invalid schedule showing lock conflict, missing X lock on write,
  // and 2PL shrinking-phase violation.
  method DemoInvalidLockSchedule()
  {
    var policy := new MultipleLockPolicy();
    var scheduler := new PessimisticScheduler(policy);

    var badSchedule: seq<SchedOp> := [
      SL("T1", "A"),
      W("T1", "A"),    // Error 1: writing with only an S lock
      XL("T2", "A"),   // Error 2: X conflicts with T1's S lock
      U("T1", "A"),
      SL("T1", "B"),   // Error 3: 2PL violation (lock after unlock)
      C("T1"),
      C("T2")
    ];

    var valid, _, errs := scheduler.ValidateSchedule(badSchedule);
    expect !valid && |errs| == 3;

    print "=== Demo 2: Invalid Lock Schedule ===\n";
    print "Locks valid: ", valid, " (", |errs|, " errors)\n";
    var i := 0;
    while i < |errs|
      decreases |errs| - i
    {
      print "  - ", errs[i], "\n";
      i := i + 1;
    }
    print "\n";
  }

  // Demo 3: Non-serializable schedule (conflict cycle T1 -> T2 on A and T2 -> T1 on B).
  method DemoNonSerializableCycle()
  {
    var policy := new MultipleLockPolicy();
    var scheduler := new PessimisticScheduler(policy);

    var cyclicSchedule: seq<SchedOp> := [
      R("T1", "A"),
      W("T2", "A"),    // T1 -> T2 on A
      R("T2", "B"),
      W("T1", "B")     // T2 -> T1 on B (cycle!)
    ];
    var serialT1T2: seq<SchedOp> := [
      R("T1", "A"),
      W("T1", "B"),
      W("T2", "A"),
      R("T2", "B")
    ];
    var serialT2T1: seq<SchedOp> := [
      W("T2", "A"),
      R("T2", "B"),
      R("T1", "A"),
      W("T1", "B")
    ];

    var ser1 := scheduler.IsSerializableTo(cyclicSchedule, serialT1T2);
    var ser2 := scheduler.IsSerializableTo(cyclicSchedule, serialT2T1);
    expect !ser1 && !ser2;

    print "=== Demo 3: Cyclic (Non-Serializable) Schedule ===\n";
    print "Serializable to (T1 -> T2): ", ser1, "\n";
    print "Serializable to (T2 -> T1): ", ser2, "\n\n";
  }

  method Main()
  {
    TestMultipleLockPolicyVerified();
    DemoValidScheduleAndSerializability();
    DemoInvalidLockSchedule();
    DemoNonSerializableCycle();
  }
}
