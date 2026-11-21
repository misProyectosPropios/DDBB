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

  // Verifies TernaryLockPolicy (S / U / X) asymmetric compatibility and
  // upgrade rules:
  //   - T1 holds S(A), T2 requests U(A) => ALLOWED (S -> U compatible)
  //   - T3 requests S(A) while T2 holds U(A) => REJECTED (U -> S incompatible)
  //   - T3 requests U(A) while T2 holds U(A) => REJECTED (U -> U incompatible)
  //   - T1 tries direct S -> X upgrade => REJECTED (only U -> X allowed)
  //   - T1 unlocks A, then T2 upgrades U -> X => ALLOWED!
  method TestTernaryLockPolicyVerified()
  {
    var policy := new TernaryLockPolicy();
    var s0 := EmptyLockTableState();

    // T1 acquires S(A)
    var d1 := policy.Dispatch(s0, SL("T1", "A"));
    assert d1.allowed;
    assert d1.nextState == SetLock(s0, "T1", "A", Shared);

    // T2 acquires U(A) while T1 holds S(A) -> compatible!
    assert policy.Compatible(Shared, Update);
    var d2 := policy.Dispatch(d1.nextState, UL("T2", "A"));
    assert d2.allowed;
    assert d2.nextState == SetLock(d1.nextState, "T2", "A", Update);
    assert "T2" in HoldersOf(d2.nextState, "A") && HoldersOf(d2.nextState, "A")["T2"] == Update;

    // T3 tries S(A) while T2 holds U(A) -> rejected (asymmetric!)
    assert !policy.Compatible(Update, Shared);
    var d3 := policy.Dispatch(d2.nextState, SL("T3", "A"));
    assert !d3.allowed;

    // T3 tries U(A) while T2 holds U(A) -> rejected!
    assert !policy.Compatible(Update, Update);
    var d4 := policy.Dispatch(d2.nextState, UL("T3", "A"));
    assert !d4.allowed;

    // T1 tries direct S -> X upgrade -> rejected (only U -> X is allowed)
    assert HoldsLock(d2.nextState, "T1", "A") && GetLockMode(d2.nextState, "T1", "A") == Shared;
    assert !policy.CanUpgrade(Shared, Exclusive);
    var d5 := policy.Dispatch(d2.nextState, XL("T1", "A"));
    assert !d5.allowed;

    // T1 unlocks A -> now T2 can upgrade U -> X!
    assert HoldsLock(d2.nextState, "T1", "A");
    var d6 := policy.Dispatch(d2.nextState, U("T1", "A"));
    assert d6.allowed;
    assert d6.nextState == RemoveLock(d2.nextState, "T1", "A");
    assert HoldsLock(d6.nextState, "T2", "A") && GetLockMode(d6.nextState, "T2", "A") == Update;
    assert policy.CanUpgrade(Update, Exclusive);
    var d7 := policy.Dispatch(d6.nextState, XL("T2", "A"));
    assert d7.allowed;
  }

  // Verifies SimpleBinaryLockPolicy: rejects S/U modes, enforces strict mutual
  // exclusion on L(T, A), allows T2 after T1 unlocks, and enforces 2PL.
  method TestSimpleBinaryLockPolicyVerified()
  {
    var policy := new SimpleBinaryLockPolicy();
    var s0 := EmptyLockTableState();

    // Shared and Update modes are not supported by SimpleBinaryLockPolicy
    assert !policy.SupportsMode(Shared);
    var dBadS := policy.Dispatch(s0, SL("T1", "A"));
    assert !dBadS.allowed;

    // T1 acquires binary lock L(T1, A)
    var d1 := policy.Dispatch(s0, L("T1", "A"));
    assert d1.allowed;
    assert d1.nextState == SetLock(s0, "T1", "A", Exclusive);
    assert "T1" in HoldersOf(d1.nextState, "A") && HoldersOf(d1.nextState, "A")["T1"] == Exclusive;

    // T2 tries L(T2, A) while T1 holds A -> rejected!
    assert !policy.Compatible(Exclusive, Exclusive);
    var d2 := policy.Dispatch(d1.nextState, L("T2", "A"));
    assert !d2.allowed;

    // T1 unlocks A -> now T2 can acquire L(T2, A)
    assert HoldsLock(d1.nextState, "T1", "A");
    var d3 := policy.Dispatch(d1.nextState, U("T1", "A"));
    assert d3.allowed;
    assert d3.nextState == RemoveLock(d1.nextState, "T1", "A");
    var d4 := policy.Dispatch(d3.nextState, L("T2", "A"));
    assert d4.allowed;

    // T1 tries to acquire L(T1, B) after unlocking A -> 2PL violation!
    assert "T1" in d4.nextState.shrinkingTxs;
    var d5 := policy.Dispatch(d4.nextState, L("T1", "B"));
    assert !d5.allowed;
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

  // Demo 4: Ternary (S / U / X) Lock Policy with U -> X upgrade and serializability.
  method DemoTernaryLockSchedule()
  {
    var policy := new TernaryLockPolicy();
    var scheduler := new PessimisticScheduler(policy);

    var validTernary: seq<SchedOp> := [
      SL("T1", "A"),
      R("T1", "A"),
      UL("T2", "A"),   // U is compatible with existing S
      R("T2", "A"),    // U permits reading
      U("T1", "A"),    // T1 finishes reading and releases S
      XL("T2", "A"),   // T2 upgrades U -> X once T1 unlocks
      W("T2", "A"),
      U("T2", "A"),
      C("T1"),
      C("T2")
    ];

    var serialT1ThenT2: seq<SchedOp> := [
      R("T1", "A"),
      R("T2", "A"),
      W("T2", "A")
    ];

    var valid, serializable, finalState, errs :=
      scheduler.ValidateAndCheckSerializable(validTernary, serialT1ThenT2);
    expect valid && errs == [];
    expect AllLocksReleased(finalState);
    expect serializable;

    print "=== Demo 4: Valid Ternary (S/U/X) 2PL Schedule ===\n";
    print "Locks valid: ", valid, "\n";
    print "Serializable to (T1 -> T2): ", serializable, "\n\n";
  }

  // Demo 5: Simple Binary Lock Policy (single exclusive lock mode).
  method DemoSimpleBinaryLockSchedule()
  {
    var policy := new SimpleBinaryLockPolicy();
    var scheduler := new PessimisticScheduler(policy);

    var validBinary: seq<SchedOp> := [
      L("T1", "A"),
      R("T1", "A"),
      W("T1", "A"),
      L("T2", "B"),
      R("T2", "B"),
      U("T1", "A"),
      L("T2", "A"),
      R("T2", "A"),
      W("T2", "A"),
      U("T2", "B"),
      U("T2", "A"),
      C("T1"),
      C("T2")
    ];

    var serialT1ThenT2: seq<SchedOp> := [
      R("T1", "A"),
      W("T1", "A"),
      R("T2", "B"),
      R("T2", "A"),
      W("T2", "A")
    ];

    var valid, serializable, finalState, errs :=
      scheduler.ValidateAndCheckSerializable(validBinary, serialT1ThenT2);
    expect valid && errs == [];
    expect AllLocksReleased(finalState);
    expect serializable;

    print "=== Demo 5: Valid Simple Binary 2PL Schedule ===\n";
    print "Locks valid: ", valid, "\n";
    print "Serializable to (T1 -> T2): ", serializable, "\n\n";
  }

  method Main()
  {
    TestMultipleLockPolicyVerified();
    TestTernaryLockPolicyVerified();
    TestSimpleBinaryLockPolicyVerified();
    DemoValidScheduleAndSerializability();
    DemoInvalidLockSchedule();
    DemoNonSerializableCycle();
    DemoTernaryLockSchedule();
    DemoSimpleBinaryLockSchedule();
  }
}
