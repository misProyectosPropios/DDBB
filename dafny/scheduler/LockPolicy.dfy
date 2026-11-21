// Dispatch protocol connecting Schedule Operations (`SchedOp`) with
// Lock Policies (`LockPolicy`), plus concrete implementations:
//   - `SimpleBinaryLockPolicy`: Single-mode Binary (Exclusive-only) 2PL
//   - `MultipleLockPolicy`:     Shared / Exclusive (S / X) 2PL
//   - `TernaryLockPolicy`:      Shared / Update / Exclusive (S / U / X) 2PL
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
  function L(tx: TxId, element: ElementId): SchedOp { LockOp(tx, element, Exclusive) }
  function SL(tx: TxId, element: ElementId): SchedOp { LockOp(tx, element, Shared) }
  function UL(tx: TxId, element: ElementId): SchedOp { LockOp(tx, element, Update) }
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

  // Coexistence invariant: for every database element, any two distinct
  // transactions holding locks on that element hold modes such that one was
  // compatible to be granted while the other was held (supports both symmetric
  // S/X and asymmetric S/U/X compatibility matrices).
  ghost predicate LocksAreCompatible(policy: LockPolicy, state: LockTableState)
  {
    forall elem :: elem in state.locks ==>
      forall t1, t2 :: t1 in state.locks[elem] && t2 in state.locks[elem] && t1 != t2 ==>
        policy.Compatible(state.locks[elem][t1], state.locks[elem][t2]) ||
        policy.Compatible(state.locks[elem][t2], state.locks[elem][t1])
  }

  // ---------------------------------------------------------------------------
  // LockPolicy interface (dispatched strategy that dictates lock validity)
  // ---------------------------------------------------------------------------

  trait LockPolicy extends object {
    function Name(): string

    // Whether this lock policy supports `mode`.
    predicate SupportsMode(mode: LockMode)

    // Directional compatibility matrix: whether `requested` may be granted when
    // another transaction already holds `existing`.
    predicate Compatible(existing: LockMode, requested: LockMode)

    // Whether a transaction already holding `current` may request/upgrade to `requested`.
    predicate CanUpgrade(current: LockMode, requested: LockMode)

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
        (!SupportsMode(mode) ==> !res.allowed) &&
        ((tx in state.finishedTxs || tx in state.shrinkingTxs) ==> !res.allowed) &&
        ((HoldsLock(state, tx, element) && !CanUpgrade(GetLockMode(state, tx, element), mode)) ==> !res.allowed) &&
        (forall other :: other in HoldersOf(state, element) && other != tx &&
            !Compatible(HoldersOf(state, element)[other], mode) ==> !res.allowed) &&
        ((SupportsMode(mode) &&
          tx !in state.finishedTxs &&
          tx !in state.shrinkingTxs &&
          (!HoldsLock(state, tx, element) || CanUpgrade(GetLockMode(state, tx, element), mode)) &&
          (forall other :: other in HoldersOf(state, element) && other != tx ==>
            Compatible(HoldersOf(state, element)[other], mode))) ==>
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
  // 1. MultipleLockPolicy — Shared / Exclusive (S / X) Two-Phase Locking
  //
  // Compatibility:
  //   - S + S => compatible
  //   - X conflicts with any lock held by another transaction
  //   - Update (U) locks are not supported by this policy
  //   - Lock upgrades S -> X are allowed when no other transaction holds a lock
  // ---------------------------------------------------------------------------

  class MultipleLockPolicy extends LockPolicy {
    constructor () {}

    function Name(): string { "Multiple-Mode (Shared/Exclusive 2PL)" }

    predicate SupportsMode(mode: LockMode)
    {
      mode.Shared? || mode.Exclusive?
    }

    predicate Compatible(existing: LockMode, requested: LockMode)
    {
      existing.Shared? && requested.Shared?
    }

    predicate CanUpgrade(current: LockMode, requested: LockMode)
    {
      SupportsMode(current) && SupportsMode(requested)
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
        (!SupportsMode(mode) ==> !res.allowed) &&
        ((tx in state.finishedTxs || tx in state.shrinkingTxs) ==> !res.allowed) &&
        ((HoldsLock(state, tx, element) && !CanUpgrade(GetLockMode(state, tx, element), mode)) ==> !res.allowed) &&
        (forall other :: other in HoldersOf(state, element) && other != tx &&
            !Compatible(HoldersOf(state, element)[other], mode) ==> !res.allowed) &&
        ((SupportsMode(mode) &&
          tx !in state.finishedTxs &&
          tx !in state.shrinkingTxs &&
          (!HoldsLock(state, tx, element) || CanUpgrade(GetLockMode(state, tx, element), mode)) &&
          (forall other :: other in HoldersOf(state, element) && other != tx ==>
            Compatible(HoldersOf(state, element)[other], mode))) ==>
          res.allowed &&
          (res.nextState == SetLock(state, tx, element, mode) ||
            (HoldsLock(state, tx, element) && res.nextState == state)))
    {
      if !SupportsMode(mode) then
        PolicyDecision(
          false,
          state,
          "Unsupported lock mode " + FormatLockMode(mode) + " for MultipleLockPolicy (only S and X are supported)."
        )
      else if tx in state.finishedTxs then
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
      else if HoldsLock(state, tx, element) && !CanUpgrade(GetLockMode(state, tx, element), mode) then
        PolicyDecision(
          false,
          state,
          "Cannot transition lock on " + element + " for " + tx + "."
        )
      else
        var holders := HoldersOf(state, element);
        if tx in holders && holders[tx].Exclusive? then
          PolicyDecision(true, state, "")
        else if tx in holders && holders[tx].Shared? && mode.Shared? then
          PolicyDecision(true, state, "")
        else if forall other :: other in holders && other != tx ==>
          Compatible(holders[other], mode)
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

  // ---------------------------------------------------------------------------
  // 2. TernaryLockPolicy — Shared / Update / Exclusive (S / U / X) 2PL
  //    (Garcia-Molina §18.4.4 Update Locks)
  //
  // Asymmetric compatibility matrix (existing -> requested):
  //   - Existing S allows requested S or U (forbids X)
  //   - Existing U forbids requested S, U, and X (prevents new readers & dual-U)
  //   - Existing X forbids requested S, U, and X
  //
  // Upgrade rules:
  //   - Only Update (U) locks may upgrade to Exclusive (X) (once all other
  //     Shared holders have unlocked).
  //   - Shared (S) locks CANNOT upgrade directly to U or X.
  //   - READ requires S, U, or X; WRITE requires X.
  // ---------------------------------------------------------------------------

  class TernaryLockPolicy extends LockPolicy {
    constructor () {}

    function Name(): string { "Ternary (Shared/Update/Exclusive 2PL)" }

    predicate SupportsMode(mode: LockMode)
    {
      true
    }

    predicate Compatible(existing: LockMode, requested: LockMode)
    {
      existing.Shared? && (requested.Shared? || requested.Update?)
    }

    predicate CanUpgrade(current: LockMode, requested: LockMode)
    {
      match current
      case Shared => requested.Shared?
      case Update => true
      case Exclusive => true
    }

    lemma LemmaExclusiveHasNoOtherHolders(state: LockTableState, tx: TxId, element: ElementId)
      requires LocksAreCompatible(this, state)
      requires HoldsLock(state, tx, element) && GetLockMode(state, tx, element).Exclusive?
      ensures forall other :: other in HoldersOf(state, element) && other != tx ==> false
    {
      var holders := HoldersOf(state, element);
      forall other | other in holders && other != tx
        ensures false
      {
        assert Compatible(holders[tx], holders[other]) || Compatible(holders[other], holders[tx]);
      }
    }

    lemma LemmaUpdateOtherHoldersAreShared(state: LockTableState, tx: TxId, element: ElementId)
      requires LocksAreCompatible(this, state)
      requires HoldsLock(state, tx, element) && GetLockMode(state, tx, element).Update?
      ensures forall other :: other in HoldersOf(state, element) && other != tx ==>
        HoldersOf(state, element)[other].Shared?
    {
      var holders := HoldersOf(state, element);
      forall other | other in holders && other != tx
        ensures holders[other].Shared?
      {
        assert Compatible(holders[tx], holders[other]) || Compatible(holders[other], holders[tx]);
      }
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
        (!SupportsMode(mode) ==> !res.allowed) &&
        ((tx in state.finishedTxs || tx in state.shrinkingTxs) ==> !res.allowed) &&
        ((HoldsLock(state, tx, element) && !CanUpgrade(GetLockMode(state, tx, element), mode)) ==> !res.allowed) &&
        (forall other :: other in HoldersOf(state, element) && other != tx &&
            !Compatible(HoldersOf(state, element)[other], mode) ==> !res.allowed) &&
        ((SupportsMode(mode) &&
          tx !in state.finishedTxs &&
          tx !in state.shrinkingTxs &&
          (!HoldsLock(state, tx, element) || CanUpgrade(GetLockMode(state, tx, element), mode)) &&
          (forall other :: other in HoldersOf(state, element) && other != tx ==>
            Compatible(HoldersOf(state, element)[other], mode))) ==>
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
      else if HoldsLock(state, tx, element) && !CanUpgrade(GetLockMode(state, tx, element), mode) then
        PolicyDecision(
          false,
          state,
          "Ternary lock rule: " + tx + " cannot upgrade " +
          FormatLockMode(GetLockMode(state, tx, element)) + " lock on " + element +
          " to " + FormatLockMode(mode) + " (acquire a U lock first)."
        )
      else
        var holders := HoldersOf(state, element);
        if tx in holders && holders[tx].Exclusive? then
          // Already holds Exclusive (strongest mode); no other tx can hold a lock on element.
          LemmaExclusiveHasNoOtherHolders(state, tx, element);
          PolicyDecision(true, state, "")
        else if tx in holders && holders[tx].Update? && (mode.Shared? || mode.Update?) then
          // Already holds Update; any other holder must hold Shared, which is compatible with S and U.
          LemmaUpdateOtherHoldersAreShared(state, tx, element);
          PolicyDecision(true, state, "")
        else if forall other :: other in holders && other != tx ==>
          Compatible(holders[other], mode)
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
          "Missing lock: " + tx + " must hold an S, U, or X lock on " + element + " before reading."
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
          "Missing exclusive lock: " + tx + " must hold an X lock on " + element + " before writing (upgrade U -> X first)."
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

  // ---------------------------------------------------------------------------
  // 3. SimpleBinaryLockPolicy — Binary (Single-Mode Exclusive) 2PL
  //    (Garcia-Molina §18.3 Simple Locks)
  //
  // Rules enforced:
  //   - Only one lock mode exists: Exclusive (`L(T, X)` / `XL(T, X)`).
  //     Shared and Update modes are not supported.
  //   - Strict mutual exclusion: Compatible(_, _) is always false, so at most
  //     one transaction may hold a lock on any element at a time.
  //   - Two-Phase Locking (2PL): no lock acquisitions after unlocking.
  //   - Both READ and WRITE require holding the binary (Exclusive) lock.
  // ---------------------------------------------------------------------------

  class SimpleBinaryLockPolicy extends LockPolicy {
    constructor () {}

    function Name(): string { "Simple Binary (Exclusive-Only 2PL)" }

    predicate SupportsMode(mode: LockMode)
    {
      mode.Exclusive?
    }

    predicate Compatible(existing: LockMode, requested: LockMode)
    {
      false
    }

    predicate CanUpgrade(current: LockMode, requested: LockMode)
    {
      current.Exclusive? && requested.Exclusive?
    }

    lemma LemmaBinaryHasNoOtherHolders(state: LockTableState, tx: TxId, element: ElementId)
      requires LocksAreCompatible(this, state)
      requires HoldsLock(state, tx, element)
      ensures forall other :: other in HoldersOf(state, element) && other != tx ==> false
    {
      var holders := HoldersOf(state, element);
      forall other | other in holders && other != tx
        ensures false
      {
        assert Compatible(holders[tx], holders[other]) || Compatible(holders[other], holders[tx]);
      }
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
        (!SupportsMode(mode) ==> !res.allowed) &&
        ((tx in state.finishedTxs || tx in state.shrinkingTxs) ==> !res.allowed) &&
        ((HoldsLock(state, tx, element) && !CanUpgrade(GetLockMode(state, tx, element), mode)) ==> !res.allowed) &&
        (forall other :: other in HoldersOf(state, element) && other != tx &&
            !Compatible(HoldersOf(state, element)[other], mode) ==> !res.allowed) &&
        ((SupportsMode(mode) &&
          tx !in state.finishedTxs &&
          tx !in state.shrinkingTxs &&
          (!HoldsLock(state, tx, element) || CanUpgrade(GetLockMode(state, tx, element), mode)) &&
          (forall other :: other in HoldersOf(state, element) && other != tx ==>
            Compatible(HoldersOf(state, element)[other], mode))) ==>
          res.allowed &&
          (res.nextState == SetLock(state, tx, element, mode) ||
            (HoldsLock(state, tx, element) && res.nextState == state)))
    {
      if !SupportsMode(mode) then
        PolicyDecision(
          false,
          state,
          "Unsupported lock mode " + FormatLockMode(mode) + " for SimpleBinaryLockPolicy (only exclusive binary locks are supported)."
        )
      else if tx in state.finishedTxs then
        PolicyDecision(
          false,
          state,
          "Cannot lock " + element + " for " + tx + ": transaction already finished."
        )
      else if tx in state.shrinkingTxs then
        PolicyDecision(
          false,
          state,
          "2PL violation: " + tx + " cannot acquire lock on " + element + " after unlocking."
        )
      else if HoldsLock(state, tx, element) && !CanUpgrade(GetLockMode(state, tx, element), mode) then
        PolicyDecision(
          false,
          state,
          "Invalid lock mode currently held on " + element + " for " + tx + "."
        )
      else
        var holders := HoldersOf(state, element);
        if tx in holders then
          LemmaBinaryHasNoOtherHolders(state, tx, element);
          PolicyDecision(true, state, "")
        else if forall other :: other in holders && other != tx ==>
          Compatible(holders[other], mode)
        then
          PolicyDecision(true, SetLock(state, tx, element, mode), "")
        else
          PolicyDecision(
            false,
            state,
            "Lock conflict: " + tx + " cannot lock " + element + " while another transaction holds it."
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
          "Missing lock: " + tx + " must hold the binary lock on " + element + " before reading."
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
          "Missing lock: " + tx + " must hold the binary lock on " + element + " before writing."
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
