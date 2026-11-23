// Core domain types for the MVCC (Multi-Version Concurrency Control) Simulator
// and Isolation Levels module:
//   - Isolation levels: ReadCommitted (RC), CursorStability (CS),
//     RepeatableRead (RR), SnapshotIsolation (SI), SerializableMVCC (SSI)
//   - Multi-version tuples (`TupleVersion` with creatorTx, xmin, committed)
//   - Transaction descriptors (`TxMeta` with snapshot startTs, cursor pin,
//     readSet, and writeSet)
//   - MVCC database state (`MvccState`) and core safety invariants.

module MvccTypes {
  type TxId = string
  type ElementId = string
  type Value = int
  type Timestamp = nat

  datatype Option<T> =
    | None
    | Some(value: T)

  // Supported SQL & MVCC Isolation Levels:
  //   - ReadCommitted (RC):    Reads latest committed version at each read; holds write locks until commit.
  //   - CursorStability (CS):  RC + pins the currently fetched cursor row so no other tx can modify it while positioned.
  //   - RepeatableRead (RR):   Holds read locks on all read items + write locks until commit.
  //   - SnapshotIsolation (SI): Reads from a consistent point-in-time snapshot (xmin <= startTs) without blocking writes;
  //                            enforces First-Committer-Wins on write conflicts.
  //   - SerializableMVCC:      Snapshot Isolation + read-set validation at commit (prevents Write Skew).
  datatype IsolationLevel =
    | ReadCommitted
    | CursorStability
    | RepeatableRead
    | SnapshotIsolation
    | SerializableMVCC

  datatype TxStatus =
    | TxActive
    | TxCommitted
    | TxAborted

  // A single immutable version of a data element in the MVCC version store.
  datatype TupleVersion = TupleVersion(
    element: ElementId,
    value: Value,
    creatorTx: TxId,
    xmin: Timestamp,
    committed: bool
  )

  // Per-transaction runtime metadata and read/write tracking.
  datatype TxMeta = TxMeta(
    tx: TxId,
    level: IsolationLevel,
    status: TxStatus,
    startTs: Timestamp,
    commitTs: Timestamp,
    cursorElem: Option<ElementId>,
    readSet: set<ElementId>,
    writeSet: set<ElementId>
  )

  // Complete snapshot of the MVCC storage engine and active concurrency control state.
  datatype MvccState = MvccState(
    clock: Timestamp,
    versions: seq<TupleVersion>,
    txs: map<TxId, TxMeta>,
    // Uncommitted write owner per element (prevents Dirty Writes at all levels)
    writeOwners: map<ElementId, TxId>,
    // Active Repeatable-Read (RR) read locks per element
    rrReadLocks: map<ElementId, set<TxId>>,
    // Active Cursor-Stability (CS) cursor pins per element
    csCursorPins: map<ElementId, set<TxId>>
  )

  // Schedule operations executed by the MVCC simulator.
  datatype MvccOp =
    | BeginOp(tx: TxId, level: IsolationLevel)
    | ReadOp(tx: TxId, element: ElementId)
    | FetchCursorOp(tx: TxId, element: ElementId)
    | CloseCursorOp(tx: TxId)
    | WriteOp(tx: TxId, element: ElementId, newValue: Value)
    | CommitOp(tx: TxId)
    | AbortOp(tx: TxId)

  // Result of executing a single MVCC operation.
  datatype MvccStepResult = MvccStepResult(
    allowed: bool,
    nextState: MvccState,
    readValue: Option<Value>,
    readVersion: Option<TupleVersion>,
    reason: string
  )

  // ---------------------------------------------------------------------------
  // State Inspection & Manipulation Helpers
  // ---------------------------------------------------------------------------

  function RRLockHolders(state: MvccState, elem: ElementId): set<TxId>
  {
    if elem in state.rrReadLocks then state.rrReadLocks[elem] else {}
  }

  function CSPinHolders(state: MvccState, elem: ElementId): set<TxId>
  {
    if elem in state.csCursorPins then state.csCursorPins[elem] else {}
  }

  opaque predicate OtherTxInSet(holders: set<TxId>, tx: TxId)
    ensures holders == {} ==> !OtherTxInSet(holders, tx)
    ensures holders == {tx} ==> !OtherTxInSet(holders, tx)
  {
    (holders - {tx}) != {}
  }

  lemma LemmaOtherTxInSet(holders: set<TxId>, tx: TxId, other: TxId)
    requires other in holders && other != tx
    ensures OtherTxInSet(holders, tx)
  {
    reveal OtherTxInSet();
    assert other in (holders - {tx});
  }

  predicate HasOtherRRLock(state: MvccState, elem: ElementId, tx: TxId)
  {
    OtherTxInSet(RRLockHolders(state, elem), tx)
  }

  predicate HasOtherCSPin(state: MvccState, elem: ElementId, tx: TxId)
  {
    OtherTxInSet(CSPinHolders(state, elem), tx)
  }

  predicate HasOtherWriteOwner(state: MvccState, elem: ElementId, tx: TxId)
  {
    elem in state.writeOwners && state.writeOwners[elem] != tx
  }

  function AddRRLock(state: MvccState, elem: ElementId, tx: TxId): MvccState
  {
    var cur := RRLockHolders(state, elem);
    state.(rrReadLocks := state.rrReadLocks[elem := cur + {tx}])
  }

  function SetCSPin(
    state: MvccState,
    oldElem: Option<ElementId>,
    newElem: Option<ElementId>,
    tx: TxId
  ): MvccState
  {
    var cleared :=
      match oldElem
      case None => state.csCursorPins
      case Some(prevEl) =>
        var cur := CSPinHolders(state, prevEl);
        state.csCursorPins[prevEl := cur - {tx}];
    var updated :=
      match newElem
      case None => cleared
      case Some(nextEl) =>
        var cur := if nextEl in cleared then cleared[nextEl] else {};
        cleared[nextEl := cur + {tx}];
    state.(csCursorPins := updated)
  }

  // Checks if any transaction other than `tx` committed a version of `elem`
  // with `xmin > sinceTs` (used by Snapshot Isolation First-Committer-Wins
  // and SerializableMVCC read-set validation).
  opaque predicate HasCommittedVersionAfter(
    versions: seq<TupleVersion>,
    elem: ElementId,
    tx: TxId,
    sinceTs: Timestamp
  )
  {
    exists i ::
      0 <= i < |versions| &&
      versions[i].element == elem &&
      versions[i].committed &&
      versions[i].creatorTx != tx &&
      versions[i].xmin > sinceTs
  }

  lemma LemmaHasCommittedVersionAfterWitness(
    versions: seq<TupleVersion>,
    elem: ElementId,
    tx: TxId,
    sinceTs: Timestamp,
    vIdx: nat
  )
    requires vIdx < |versions|
    requires versions[vIdx].element == elem
    requires versions[vIdx].committed
    requires versions[vIdx].creatorTx != tx
    requires versions[vIdx].xmin > sinceTs
    ensures HasCommittedVersionAfter(versions, elem, tx, sinceTs)
  {
    reveal HasCommittedVersionAfter();
  }

  lemma LemmaNoCommittedVersionAfter(
    versions: seq<TupleVersion>,
    elem: ElementId,
    tx: TxId,
    sinceTs: Timestamp
  )
    requires forall i :: 0 <= i < |versions| ==>
      !(versions[i].element == elem &&
        versions[i].committed &&
        versions[i].creatorTx != tx &&
        versions[i].xmin > sinceTs)
    ensures !HasCommittedVersionAfter(versions, elem, tx, sinceTs)
  {
    reveal HasCommittedVersionAfter();
  }

  // Checks if any element in `elemSet` has a committed version by another
  // transaction with `xmin > sinceTs`.
  opaque predicate SetHasCommittedVersionAfter(
    versions: seq<TupleVersion>,
    elemSet: set<ElementId>,
    tx: TxId,
    sinceTs: Timestamp
  )
  {
    exists i ::
      0 <= i < |versions| &&
      versions[i].element in elemSet &&
      versions[i].committed &&
      versions[i].creatorTx != tx &&
      versions[i].xmin > sinceTs
  }

  lemma LemmaSetHasCommittedVersionAfterWitness(
    versions: seq<TupleVersion>,
    elemSet: set<ElementId>,
    tx: TxId,
    sinceTs: Timestamp,
    vIdx: nat
  )
    requires vIdx < |versions|
    requires versions[vIdx].element in elemSet
    requires versions[vIdx].committed
    requires versions[vIdx].creatorTx != tx
    requires versions[vIdx].xmin > sinceTs
    ensures SetHasCommittedVersionAfter(versions, elemSet, tx, sinceTs)
  {
    reveal SetHasCommittedVersionAfter();
  }

  lemma LemmaNoSetCommittedVersionAfter(
    versions: seq<TupleVersion>,
    elemSet: set<ElementId>,
    tx: TxId,
    sinceTs: Timestamp
  )
    requires forall i :: 0 <= i < |versions| ==>
      !(versions[i].element in elemSet &&
        versions[i].committed &&
        versions[i].creatorTx != tx &&
        versions[i].xmin > sinceTs)
    ensures !SetHasCommittedVersionAfter(versions, elemSet, tx, sinceTs)
  {
    reveal SetHasCommittedVersionAfter();
  }

  // Well-formedness invariant of the MVCC engine state.
  predicate ValidMvccState(state: MvccState)
  {
    (forall tx :: tx in state.txs ==> state.txs[tx].tx == tx) &&
    (forall el :: el in state.writeOwners ==>
      var owner := state.writeOwners[el];
      owner in state.txs && state.txs[owner].status == TxActive)
  }

  // Builds an initial MVCC database state from a list of `(element, initialValue)` pairs
  // committed at timestamp 0 by the system pseudo-transaction `"INIT"`.
  function InitVersions(items: seq<(ElementId, Value)>): seq<TupleVersion>
    ensures |InitVersions(items)| == |items|
    ensures forall i :: 0 <= i < |InitVersions(items)| ==>
      InitVersions(items)[i].committed &&
      InitVersions(items)[i].xmin == 0 &&
      InitVersions(items)[i].creatorTx == "INIT"
    decreases |items|
  {
    if |items| == 0 then []
    else
      [TupleVersion(items[0].0, items[0].1, "INIT", 0, true)] +
      InitVersions(items[1..])
  }

  function InitMvccState(items: seq<(ElementId, Value)>): MvccState
    ensures ValidMvccState(InitMvccState(items))
  {
    MvccState(1, InitVersions(items), map[], map[], map[], map[])
  }

  // ---------------------------------------------------------------------------
  // Formatting Helpers
  // ---------------------------------------------------------------------------

  function FormatIsolationLevel(level: IsolationLevel): string
  {
    match level
    case ReadCommitted => "RC (Read Committed)"
    case CursorStability => "CS (Cursor Stability)"
    case RepeatableRead => "RR (Repeatable Read)"
    case SnapshotIsolation => "SI (Snapshot Isolation)"
    case SerializableMVCC => "Serializable (SSI)"
  }
}
