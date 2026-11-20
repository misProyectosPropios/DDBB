// Pessimistic Scheduler module.
//
// Composes a `LockPolicy` object (e.g. `MultipleLockPolicy`) and dispatches
// every schedule operation through `policy.Dispatch(state, op)` (`op.Accept`)
// to decide whether the schedule's locks and operations are valid.
// Also checks whether a schedule is conflict-serializable to another (serial)
// schedule.

include "Types.dfy"
include "LockPolicy.dfy"
include "Serializability.dfy"

module PessimisticScheduling {
  import opened SchedulerTypes
  import opened LockPolicies
  import opened Serializability

  // Pure recursive specification of running `policy` over `ops` from `initState`.
  function RunPolicySpec(
    policy: LockPolicy,
    ops: seq<SchedOp>,
    initState: LockTableState
  ): (bool, LockTableState)
    requires LocksAreCompatible(policy, initState)
    ensures LocksAreCompatible(policy, RunPolicySpec(policy, ops, initState).1)
    decreases |ops|
  {
    if |ops| == 0 then
      (true, initState)
    else
      var prev := RunPolicySpec(policy, ops[..|ops| - 1], initState);
      var decision := policy.Dispatch(prev.1, ops[|ops| - 1]);
      (prev.0 && decision.allowed, decision.nextState)
  }

  class PessimisticScheduler {
    const policy: LockPolicy

    constructor (policy: LockPolicy)
      ensures this.policy == policy
    {
      this.policy := policy;
    }

    // Runs over the list of operations, dispatching each to `policy` to verify
    // lock compatibility, 2PL ordering, and read/write lock requirements.
    method ValidateSchedule(ops: seq<SchedOp>)
      returns (isValid: bool, finalState: LockTableState, errors: seq<string>)
      ensures LocksAreCompatible(policy, finalState)
      ensures isValid <==> |errors| == 0
      ensures (isValid, finalState) == RunPolicySpec(policy, ops, EmptyLockTableState())
    {
      finalState := EmptyLockTableState();
      errors := [];
      isValid := true;

      var i := 0;
      while i < |ops|
        invariant 0 <= i <= |ops|
        invariant LocksAreCompatible(policy, finalState)
        invariant isValid <==> |errors| == 0
        invariant (isValid, finalState) == RunPolicySpec(policy, ops[..i], EmptyLockTableState())
        decreases |ops| - i
      {
        assert ops[..i + 1][..i] == ops[..i];
        assert ops[..i + 1][i] == ops[i];

        var decision := policy.Dispatch(finalState, ops[i]);
        finalState := decision.nextState;
        if !decision.allowed {
          isValid := false;
          errors := errors + [decision.reason];
        }

        i := i + 1;
      }

      assert ops[..|ops|] == ops;
    }

    // Determines whether `schedule` is conflict-serializable to `targetSerial`.
    method IsSerializableTo(schedule: seq<SchedOp>, targetSerial: seq<SchedOp>)
      returns (serializable: bool)
      ensures serializable <==> IsConflictSerializableTo(schedule, targetSerial)
    {
      serializable := IsConflictSerializableTo(schedule, targetSerial);
    }

    // Combined check: validates all locks in `schedule` via `policy` AND
    // checks whether `schedule` is conflict-serializable to `targetSerial`.
    method ValidateAndCheckSerializable(
      schedule: seq<SchedOp>,
      targetSerial: seq<SchedOp>
    )
      returns (
        locksValid: bool,
        serializable: bool,
        finalState: LockTableState,
        errors: seq<string>
      )
      ensures LocksAreCompatible(policy, finalState)
      ensures locksValid <==> |errors| == 0
      ensures (locksValid, finalState) == RunPolicySpec(policy, schedule, EmptyLockTableState())
      ensures serializable <==> IsConflictSerializableTo(schedule, targetSerial)
    {
      locksValid, finalState, errors := ValidateSchedule(schedule);
      serializable := IsSerializableTo(schedule, targetSerial);
    }
  }
}
