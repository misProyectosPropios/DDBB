// Dispatch protocol connecting Schedule Operations (`SchedOp`) with
// Lock Policies (`LockPolicy`), plus the `MultipleLockPolicy` implementation
// (Shared / Exclusive Two-Phase Locking).
//
// Dispatch flow per operation:
//   PessimisticScheduler.ValidateSchedule(ops)
//     -> policy.Dispatch(state, op)     [1st dispatch: LockPolicy receives op]
//       -> op.Accept(policy, state)     [2nd dispatch: op invokes matching Visit*]
//         -> policy.Visit*(state, ...)  [decides whether the lock/op is valid]

include "Types.dfy"

module LockPolicies {
  import opened SchedulerTypes

  // ---------------------------------------------------------------------------
  // Schedule Operations (visited elements in dispatch)
  // ---------------------------------------------------------------------------

  datatype SchedOp =
    | LockOp(tx: TxId, element: ElementId, mode: LockMode)
    | UnlockOp(tx: TxId, element: ElementId)
    | ReadOp(tx: TxId, element: ElementId)
    | WriteOp(tx: TxId, element: ElementId)
    | CommitOp(tx: TxId)
    | AbortOp(tx: TxId)
  {
    function Accept(policy: LockPolicy, state: LockTableState): PolicyDecision
      requires LocksAreCompatible(policy, state)
      ensures LocksAreCompatible(policy, Accept(policy, state).nextState)
    {
      match this
      case LockOp(tx, element, mode) => policy.VisitLock(state, tx, element, mode)
      case UnlockOp(tx, element) => policy.VisitUnlock(state, tx, element)
      case ReadOp(tx, element) => policy.VisitRead(state, tx, element)
      case WriteOp(tx, element) => policy.VisitWrite(state, tx, element)
      case CommitOp(tx) => policy.VisitCommit(state, tx)
      case AbortOp(tx) => policy.VisitAbort(state, tx)
    }
  }

  // Shorthand operation builders
  function SL(tx: TxId, element: ElementId): SchedOp { LockOp(tx, element, Shared) }
  function XL(tx: TxId, element: ElementId): SchedOp { LockOp(tx, element, Exclusive) }
  function U(tx: TxId, element: ElementId): SchedOp { UnlockOp(tx, element) }
  function R(tx: TxId, element: ElementId): SchedOp { ReadOp(tx, element) }
  function W(tx: TxId, element: ElementId): SchedOp { WriteOp(tx, element) }
  function C(tx: TxId): SchedOp { CommitOp(tx) }
  function A(tx: TxId): SchedOp { AbortOp(tx) }

  function FormatSchedOp(op: SchedOp): string
  {
    match op
    case LockOp(tx, elem, mode) =>
      FormatLockMode(mode) + "L(" + tx + ", " + elem + ")"
    case UnlockOp(tx, elem) =>
      "U(" + tx + ", " + elem + ")"
    case ReadOp(tx, elem) =>
      "R(" + tx + ", " + elem + ")"
    case WriteOp(tx, elem) =>
      "W(" + tx + ", " + elem + ")"
    case CommitOp(tx) =>
      "C(" + tx + ")"
    case AbortOp(tx) =>
      "A(" + tx + ")"
  }

  // Mutual-compatibility invariant: for every database element, any two
  // distinct transactions holding locks on that element hold compatible modes.
  ghost predicate LocksAreCompatible(policy: LockPolicy, state: LockTableState)
  {
    forall elem :: elem in state.locks ==>
      forall t1, t2 :: t1 in state.locks[elem] && t2 in state.locks[elem] && t1 != t2 ==>
        policy.Compatible(state.locks[elem][t1], state.locks[elem][t2])
  }

  // ---------------------------------------------------------------------------
  // LockPolicy interface (dispatched strategy that dictates lock validity)
  // ---------------------------------------------------------------------------

  trait LockPolicy extends object {
    function Name(): string

    // Compatibility matrix between an existing lock mode and a requested mode.
    predicate Compatible(existing: LockMode, requested: LockMode)

    function VisitLock(
      state: LockTableState,
      tx: TxId,
      element: ElementId,
      mode: LockMode
    ): PolicyDecision
      requires LocksAreCompatible(this, state)
      ensures var res := VisitLock(state, tx, element, mode);
        LocksAreCompatible(this, res.nextState) &&
        (!res.allowed ==> res.nextState == state) &&
        ((tx in state.finishedTxs || tx in state.shrinkingTxs) ==> !res.allowed) &&
        (forall other :: other in HoldersOf(state, element) && other != tx &&
            (!Compatible(HoldersOf(state, element)[other], mode) ||
             !Compatible(mode, HoldersOf(state, element)[other])) ==> !res.allowed) &&
        ((tx !in state.finishedTxs && tx !in state.shrinkingTxs &&
          (forall other :: other in HoldersOf(state, element) && other != tx ==>
            Compatible(HoldersOf(state, element)[other], mode) &&
            Compatible(mode, HoldersOf(state, element)[other]))) ==>
          res.allowed &&
          (res.nextState == SetLock(state, tx, element, mode) ||
            (HoldsLock(state, tx, element) && res.nextState == state)))

    function VisitUnlock(
      state: LockTableState,
      tx: TxId,
      element: ElementId
    ): PolicyDecision
      requires LocksAreCompatible(this, state)
      ensures var res := VisitUnlock(state, tx, element);
        LocksAreCompatible(this, res.nextState) &&
        (res.allowed <==> HoldsLock(state, tx, element)) &&
        (res.allowed ==> res.nextState == RemoveLock(state, tx, element)) &&
        (!res.allowed ==> res.nextState == state)

    function VisitRead(
      state: LockTableState,
      tx: TxId,
      element: ElementId
    ): PolicyDecision
      requires LocksAreCompatible(this, state)
      ensures var res := VisitRead(state, tx, element);
        LocksAreCompatible(this, res.nextState) &&
        res.nextState == state &&
        ((tx in state.finishedTxs || !HoldsLock(state, tx, element)) ==> !res.allowed)

    function VisitWrite(
      state: LockTableState,
      tx: TxId,
      element: ElementId
    ): PolicyDecision
      requires LocksAreCompatible(this, state)
      ensures var res := VisitWrite(state, tx, element);
        LocksAreCompatible(this, res.nextState) &&
        res.nextState == state &&
        ((tx in state.finishedTxs || !HoldsLock(state, tx, element)) ==> !res.allowed)

    function VisitCommit(state: LockTableState, tx: TxId): PolicyDecision
      requires LocksAreCompatible(this, state)
      ensures var res := VisitCommit(state, tx);
        LocksAreCompatible(this, res.nextState) &&
        (res.allowed <==> tx !in state.finishedTxs) &&
        (res.allowed ==> res.nextState == MarkFinished(state, tx)) &&
        (!res.allowed ==> res.nextState == state)

    function VisitAbort(state: LockTableState, tx: TxId): PolicyDecision
      requires LocksAreCompatible(this, state)
      ensures var res := VisitAbort(state, tx);
        LocksAreCompatible(this, res.nextState) &&
        (res.allowed <==> tx !in state.finishedTxs) &&
        (res.allowed ==> res.nextState == MarkFinished(state, tx)) &&
        (!res.allowed ==> res.nextState == state)

    // Entry point for dispatch: hands `this` to `op.Accept(this, state)`.
    function Dispatch(state: LockTableState, op: SchedOp): PolicyDecision
      requires LocksAreCompatible(this, state)
      ensures LocksAreCompatible(this, Dispatch(state, op).nextState)
    {
      op.Accept(this, state)
    }
  }

  // ---------------------------------------------------------------------------
  // MultipleLockPolicy — Multiple-Mode (Shared / Exclusive) Two-Phase Locking
  //
  // Rules enforced:
  //   1. Compatibility: Shared + Shared is compatible; Exclusive conflicts with
  //      any lock held by another transaction.
  //   2. Lock upgrade: a transaction holding Shared may upgrade to Exclusive if
  //      no other transaction holds a lock on the element.
  //   3. Two-Phase Locking (2PL): once a transaction releases a lock (UnlockOp),
  //      it enters the shrinking phase and cannot acquire or upgrade any lock.
  //   4. Well-formedness: READ requires Shared or Exclusive; WRITE requires
  //      Exclusive; UNLOCK requires holding a lock; finished transactions
  //      cannot perform new locks, reads, writes, or duplicate commits/aborts.
  // ---------------------------------------------------------------------------

  class MultipleLockPolicy extends LockPolicy {
    constructor () {}

    function Name(): string { "Multiple-Mode (Shared/Exclusive 2PL)" }

    predicate Compatible(existing: LockMode, requested: LockMode)
    {
      existing.Shared? && requested.Shared?
    }

    function VisitLock(
      state: LockTableState,
      tx: TxId,
      element: ElementId,
      mode: LockMode
    ): PolicyDecision
      requires LocksAreCompatible(this, state)
      ensures var res := VisitLock(state, tx, element, mode);
        LocksAreCompatible(this, res.nextState) &&
        (!res.allowed ==> res.nextState == state) &&
        ((tx in state.finishedTxs || tx in state.shrinkingTxs) ==> !res.allowed) &&
        (forall other :: other in HoldersOf(state, element) && other != tx &&
            (!Compatible(HoldersOf(state, element)[other], mode) ||
             !Compatible(mode, HoldersOf(state, element)[other])) ==> !res.allowed) &&
        ((tx !in state.finishedTxs && tx !in state.shrinkingTxs &&
          (forall other :: other in HoldersOf(state, element) && other != tx ==>
            Compatible(HoldersOf(state, element)[other], mode) &&
            Compatible(mode, HoldersOf(state, element)[other]))) ==>
          res.allowed &&
          (res.nextState == SetLock(state, tx, element, mode) ||
            (HoldsLock(state, tx, element) && res.nextState == state)))
    {
      if tx in state.finishedTxs then
        PolicyDecision(
          false,
          state,
          "Cannot lock " + element + " for " + tx + ": transaction already finished."
        )
      else if tx in state.shrinkingTxs then
        PolicyDecision(
          false,
          state,
          "2PL violation: " + tx + " cannot acquire " + FormatLockMode(mode) +
          " lock on " + element + " after unlocking."
        )
      else
        var holders := HoldersOf(state, element);
        if tx in holders && holders[tx].Exclusive? then
          // Already holds strongest lock (Exclusive); re-requesting S or X is a valid no-op.
          PolicyDecision(true, state, "")
        else if tx in holders && holders[tx].Shared? && mode.Shared? then
          // Already holds Shared lock; re-requesting Shared is a valid no-op.
          PolicyDecision(true, state, "")
        else if forall other :: other in holders && other != tx ==>
          Compatible(holders[other], mode) && Compatible(mode, holders[other])
        then
          PolicyDecision(true, SetLock(state, tx, element, mode), "")
        else
          PolicyDecision(
            false,
            state,
            "Lock conflict: " + tx + " cannot acquire " + FormatLockMode(mode) +
            " lock on " + element + " due to an incompatible lock held by another transaction."
          )
    }

    function VisitUnlock(
      state: LockTableState,
      tx: TxId,
      element: ElementId
    ): PolicyDecision
      requires LocksAreCompatible(this, state)
      ensures var res := VisitUnlock(state, tx, element);
        LocksAreCompatible(this, res.nextState) &&
        (res.allowed <==> HoldsLock(state, tx, element)) &&
        (res.allowed ==> res.nextState == RemoveLock(state, tx, element)) &&
        (!res.allowed ==> res.nextState == state)
    {
      if !HoldsLock(state, tx, element) then
        PolicyDecision(
          false,
          state,
          "Cannot unlock " + element + " for " + tx + ": transaction does not hold a lock on it."
        )
      else
        PolicyDecision(true, RemoveLock(state, tx, element), "")
    }

    function VisitRead(
      state: LockTableState,
      tx: TxId,
      element: ElementId
    ): PolicyDecision
      requires LocksAreCompatible(this, state)
      ensures var res := VisitRead(state, tx, element);
        LocksAreCompatible(this, res.nextState) &&
        res.nextState == state &&
        ((tx in state.finishedTxs || !HoldsLock(state, tx, element)) ==> !res.allowed)
    {
      if tx in state.finishedTxs then
        PolicyDecision(
          false,
          state,
          "Cannot READ " + element + " for " + tx + ": transaction already finished."
        )
      else if !HoldsLock(state, tx, element) then
        PolicyDecision(
          false,
          state,
          "Missing lock: " + tx + " must hold an S or X lock on " + element + " before reading."
        )
      else
        PolicyDecision(true, state, "")
    }

    function VisitWrite(
      state: LockTableState,
      tx: TxId,
      element: ElementId
    ): PolicyDecision
      requires LocksAreCompatible(this, state)
      ensures var res := VisitWrite(state, tx, element);
        LocksAreCompatible(this, res.nextState) &&
        res.nextState == state &&
        ((tx in state.finishedTxs || !HoldsLock(state, tx, element)) ==> !res.allowed)
    {
      if tx in state.finishedTxs then
        PolicyDecision(
          false,
          state,
          "Cannot WRITE " + element + " for " + tx + ": transaction already finished."
        )
      else if !HoldsLock(state, tx, element) || GetLockMode(state, tx, element) != Exclusive then
        PolicyDecision(
          false,
          state,
          "Missing exclusive lock: " + tx + " must hold an X lock on " + element + " before writing."
        )
      else
        PolicyDecision(true, state, "")
    }

    function VisitCommit(state: LockTableState, tx: TxId): PolicyDecision
      requires LocksAreCompatible(this, state)
      ensures var res := VisitCommit(state, tx);
        LocksAreCompatible(this, res.nextState) &&
        (res.allowed <==> tx !in state.finishedTxs) &&
        (res.allowed ==> res.nextState == MarkFinished(state, tx)) &&
        (!res.allowed ==> res.nextState == state)
    {
      if tx in state.finishedTxs then
        PolicyDecision(
          false,
          state,
          "Cannot COMMIT " + tx + ": transaction already finished."
        )
      else
        PolicyDecision(true, MarkFinished(state, tx), "")
    }

    function VisitAbort(state: LockTableState, tx: TxId): PolicyDecision
      requires LocksAreCompatible(this, state)
      ensures var res := VisitAbort(state, tx);
        LocksAreCompatible(this, res.nextState) &&
        (res.allowed <==> tx !in state.finishedTxs) &&
        (res.allowed ==> res.nextState == MarkFinished(state, tx)) &&
        (!res.allowed ==> res.nextState == state)
    {
      if tx in state.finishedTxs then
        PolicyDecision(
          false,
          state,
          "Cannot ABORT " + tx + ": transaction already finished."
        )
      else
        PolicyDecision(true, MarkFinished(state, tx), "")
    }
  }
}
