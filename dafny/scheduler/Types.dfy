// Core domain types for the Pessimistic Scheduler module:
// transaction/element identifiers, lock modes, lock-table state, policy
// decisions, and lock-table manipulation helpers.

module SchedulerTypes {
  type TxId = string
  type ElementId = string

  // Lock modes: Shared (S), Update (U), and Exclusive (X).
  datatype LockMode =
    | Shared
    | Update
    | Exclusive

  // Immutable snapshot of the scheduler's lock table and 2PL transaction phases.
  datatype LockTableState = LockTableState(
    locks: map<ElementId, map<TxId, LockMode>>,
    shrinkingTxs: set<TxId>,
    finishedTxs: set<TxId>
  )

  // Result returned by a LockPolicy when evaluating a single operation.
  datatype PolicyDecision = PolicyDecision(
    allowed: bool,
    nextState: LockTableState,
    reason: string
  )

  function EmptyLockTableState(): LockTableState
  {
    LockTableState(map[], {}, {})
  }

  function HoldersOf(state: LockTableState, elem: ElementId): map<TxId, LockMode>
  {
    if elem in state.locks then state.locks[elem] else map[]
  }

  predicate HoldsLock(state: LockTableState, tx: TxId, elem: ElementId)
  {
    elem in state.locks && tx in state.locks[elem]
  }

  function GetLockMode(state: LockTableState, tx: TxId, elem: ElementId): LockMode
    requires HoldsLock(state, tx, elem)
  {
    state.locks[elem][tx]
  }

  function SetLock(
    state: LockTableState,
    tx: TxId,
    elem: ElementId,
    mode: LockMode
  ): LockTableState
  {
    var holders := HoldersOf(state, elem);
    var updatedHolders := holders[tx := mode];
    LockTableState(
      state.locks[elem := updatedHolders],
      state.shrinkingTxs,
      state.finishedTxs
    )
  }

  function RemoveLock(
    state: LockTableState,
    tx: TxId,
    elem: ElementId
  ): LockTableState
  {
    var holders := HoldersOf(state, elem);
    var remaining := holders - {tx};
    var nextLocks :=
      if remaining == map[] then state.locks - {elem}
      else state.locks[elem := remaining];
    LockTableState(
      nextLocks,
      state.shrinkingTxs + {tx},
      state.finishedTxs
    )
  }

  function MarkFinished(state: LockTableState, tx: TxId): LockTableState
  {
    LockTableState(
      state.locks,
      state.shrinkingTxs,
      state.finishedTxs + {tx}
    )
  }

  predicate AllLocksReleased(state: LockTableState)
  {
    forall elem :: elem in state.locks ==> state.locks[elem] == map[]
  }

  function FormatLockMode(mode: LockMode): string
  {
    match mode
    case Shared => "S"
    case Update => "U"
    case Exclusive => "X"
  }
}
