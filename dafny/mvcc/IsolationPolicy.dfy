// Isolation Level Visibility & Conflict Rules for the MVCC Simulator.
//
// Defines:
//   - Version visibility rules (`IsVersionVisible`) for RC, CS, RR, SI, and
//     SerializableMVCC, formally proving that NO isolation level ever allows
//     Dirty Reads (`v.committed || v.creatorTx == tx`) and that SI /
//     SerializableMVCC only read committed versions with `v.xmin <= startTs`.
//   - Latest visible version lookup (`FindLatestVisibleVersion`).
//   - Write-conflict rules (`CheckWriteAllowed`) covering Dirty Writes,
//     CS cursor pins, RR read locks, and SI First-Committer-Wins.
//   - Commit validation rules (`CheckCommitAllowed`) covering SI First-Committer-Wins
//     and SerializableMVCC read-set validation (preventing Write Skew).

include "Types.dfy"

module IsolationPolicies {
  import opened MvccTypes

  // ---------------------------------------------------------------------------
  // 1. Version Visibility per Isolation Level
  // ---------------------------------------------------------------------------

  // Determines whether `v` is visible to transaction `meta`:
  //   - A transaction always sees its own uncommitted writes (`v.creatorTx == meta.tx`).
  //   - Otherwise `v` MUST be committed (`v.committed == true`):
  //       * Under RC, CS, and RR: any committed version is visible (the engine
  //         picks the most recent one, while RR/CS use read locks/pins to block
  //         concurrent overwrites).
  //       * Under SnapshotIsolation (SI) and SerializableMVCC: `v` must also
  //         have been committed at or before `meta.startTs` (`v.xmin <= meta.startTs`).
  predicate IsVersionVisible(meta: TxMeta, v: TupleVersion)
  {
    if v.creatorTx == meta.tx then
      true
    else if !v.committed then
      false
    else
      match meta.level
      case ReadCommitted => true
      case CursorStability => true
      case RepeatableRead => true
      case SnapshotIsolation => v.xmin <= meta.startTs
      case SerializableMVCC => v.xmin <= meta.startTs
  }

  // Formal Safety Lemma 1: No isolation level ever permits Dirty Reads
  // (reading another transaction's uncommitted version).
  lemma LemmaNoDirtyReads(meta: TxMeta, v: TupleVersion)
    requires IsVersionVisible(meta, v)
    ensures v.committed || v.creatorTx == meta.tx
  {
  }

  // Formal Safety Lemma 2: Snapshot Isolation and SerializableMVCC strictly
  // bound visible versions from other transactions by `meta.startTs`.
  lemma LemmaSnapshotBoundedByStartTs(meta: TxMeta, v: TupleVersion)
    requires IsVersionVisible(meta, v)
    requires meta.level == SnapshotIsolation || meta.level == SerializableMVCC
    requires v.creatorTx != meta.tx
    ensures v.committed && v.xmin <= meta.startTs
  {
  }

  opaque predicate HasVisibleVersion(
    versions: seq<TupleVersion>,
    meta: TxMeta,
    elem: ElementId
  )
  {
    exists k ::
      0 <= k < |versions| &&
      versions[k].element == elem &&
      IsVersionVisible(meta, versions[k])
  }

  lemma LemmaHasVisibleVersion(
    versions: seq<TupleVersion>,
    meta: TxMeta,
    elem: ElementId,
    k: nat
  )
    requires k < |versions|
    requires versions[k].element == elem
    requires IsVersionVisible(meta, versions[k])
    ensures HasVisibleVersion(versions, meta, elem)
  {
    reveal HasVisibleVersion();
  }

  // Scans the version chain backwards (`|versions| - 1` down to `0`) to return
  // the most recently created/committed version of `elem` visible to `meta`.
  // Priority:
  //   1. If `meta.tx` has its own uncommitted version of `elem`, return the latest such version.
  //   2. Otherwise return the visible committed version of `elem` with the largest `xmin`
  //      (breaking ties by latest position in `versions`).
  method FindLatestVisibleVersion(
    versions: seq<TupleVersion>,
    meta: TxMeta,
    elem: ElementId
  ) returns (found: Option<TupleVersion>)
    ensures HasVisibleVersion(versions, meta, elem) ==>
      found.Some?
    ensures found.Some? ==>
      found.value in versions &&
      found.value.element == elem &&
      IsVersionVisible(meta, found.value) &&
      (found.value.committed || found.value.creatorTx == meta.tx)
    ensures (found.Some? &&
             (meta.level == SnapshotIsolation || meta.level == SerializableMVCC) &&
             found.value.creatorTx != meta.tx) ==>
      found.value.xmin <= meta.startTs
  {
    reveal HasVisibleVersion();
    // Pass 1: check if `meta.tx` has its own uncommitted write on `elem`
    var idx := |versions|;
    while idx > 0
      invariant 0 <= idx <= |versions|
      decreases idx
    {
      idx := idx - 1;
      var v := versions[idx];
      if v.element == elem && v.creatorTx == meta.tx && !v.committed {
        return Some(v);
      }
    }

    // Pass 2: find the visible committed version with highest `xmin`
    found := None;
    var i := 0;
    while i < |versions|
      invariant 0 <= i <= |versions|
      invariant (exists k :: 0 <= k < i && versions[k].element == elem && IsVersionVisible(meta, versions[k])) ==>
        found.Some?
      invariant found.Some? ==>
        found.value in versions &&
        found.value.element == elem &&
        IsVersionVisible(meta, found.value)
      decreases |versions| - i
    {
      var v := versions[i];
      if v.element == elem && IsVersionVisible(meta, v) {
        match found {
          case None =>
            found := Some(v);
          case Some(best) =>
            if v.xmin >= best.xmin {
              found := Some(v);
            }
        }
      }
      i := i + 1;
    }
  }

  // ---------------------------------------------------------------------------
  // 2. Write Conflict Rules per Isolation Level
  // ---------------------------------------------------------------------------

  // Checks whether transaction `meta` is allowed to write `elem` in `state`:
  //   1. All levels: cannot write if another active transaction already owns an
  //      uncommitted write on `elem` (prevents Dirty Writes).
  //   2. All levels: cannot write if another transaction currently has its
  //      Cursor Stability (CS) cursor positioned on `elem`.
  //   3. All levels: cannot write if another transaction holds an active
  //      Repeatable Read (RR) read lock on `elem`.
  //   4. SnapshotIsolation & SerializableMVCC (First-Committer-Wins):
  //      cannot write if another transaction already committed a new version
  //      of `elem` with `xmin > meta.startTs`.
  predicate WriteAllowed(
    state: MvccState,
    meta: TxMeta,
    elem: ElementId
  )
  {
    !HasOtherWriteOwner(state, elem, meta.tx) &&
    !HasOtherCSPin(state, elem, meta.tx) &&
    !HasOtherRRLock(state, elem, meta.tx) &&
    !((meta.level == SnapshotIsolation || meta.level == SerializableMVCC) &&
      HasCommittedVersionAfter(state.versions, elem, meta.tx, meta.startTs))
  }

  function CheckWriteAllowed(
    state: MvccState,
    meta: TxMeta,
    elem: ElementId
  ): (bool, string)
    ensures CheckWriteAllowed(state, meta, elem).0 == WriteAllowed(state, meta, elem)
  {
    if HasOtherWriteOwner(state, elem, meta.tx) then
      (false, "Write blocked: another active transaction holds an uncommitted write")
    else if HasOtherCSPin(state, elem, meta.tx) then
      (false, "Write blocked by Cursor Stability (CS): another transaction cursor is positioned on element")
    else if HasOtherRRLock(state, elem, meta.tx) then
      (false, "Write blocked by Repeatable Read (RR): another transaction holds a read lock on element")
    else if (meta.level == SnapshotIsolation || meta.level == SerializableMVCC) &&
            HasCommittedVersionAfter(state.versions, elem, meta.tx, meta.startTs) then
      (false, "First-Committer-Wins violation (SI/Serializable): concurrent transaction committed after startTs")
    else
      (true, "Write permitted")
  }

  // ---------------------------------------------------------------------------
  // 3. Commit Validation Rules (SI First-Committer-Wins & Serializable SSI)
  // ---------------------------------------------------------------------------

  // Checks whether transaction `meta` is allowed to commit in `state`:
  //   - ReadCommitted, CursorStability, RepeatableRead: always allowed once
  //     reads/writes succeeded during execution.
  //   - SnapshotIsolation: First-Committer-Wins check on `meta.writeSet` — no
  //     other transaction may have committed any `el in meta.writeSet` with
  //     `xmin > meta.startTs`.
  //   - SerializableMVCC: First-Committer-Wins on `meta.writeSet` PLUS
  //     if `meta.writeSet != {}`, no other transaction may have committed any
  //     `el in meta.readSet` with `xmin > meta.startTs` (prevents Write Skew!).
  predicate CommitAllowed(state: MvccState, meta: TxMeta)
  {
    match meta.level
    case ReadCommitted => true
    case CursorStability => true
    case RepeatableRead => true
    case SnapshotIsolation =>
      !SetHasCommittedVersionAfter(state.versions, meta.writeSet, meta.tx, meta.startTs)
    case SerializableMVCC =>
      !SetHasCommittedVersionAfter(state.versions, meta.writeSet, meta.tx, meta.startTs) &&
      !(meta.writeSet != {} &&
        SetHasCommittedVersionAfter(state.versions, meta.readSet, meta.tx, meta.startTs))
  }

  function CheckCommitAllowed(state: MvccState, meta: TxMeta): (bool, string)
    ensures CheckCommitAllowed(state, meta).0 == CommitAllowed(state, meta)
  {
    match meta.level
    case ReadCommitted =>
      (true, "Read Committed commit OK")
    case CursorStability =>
      (true, "Cursor Stability commit OK")
    case RepeatableRead =>
      (true, "Repeatable Read commit OK")
    case SnapshotIsolation =>
      if SetHasCommittedVersionAfter(state.versions, meta.writeSet, meta.tx, meta.startTs) then
        (false, "Snapshot Isolation abort (First-Committer-Wins): concurrent committed write on writeSet")
      else
        (true, "Snapshot Isolation commit OK")
    case SerializableMVCC =>
      if SetHasCommittedVersionAfter(state.versions, meta.writeSet, meta.tx, meta.startTs) then
        (false, "Serializable abort (First-Committer-Wins): concurrent committed write on writeSet")
      else if meta.writeSet != {} &&
              SetHasCommittedVersionAfter(state.versions, meta.readSet, meta.tx, meta.startTs) then
        (false, "Serializable abort (Write Skew / rw-antidependency): readSet was modified after snapshot startTs")
      else
        (true, "Serializable MVCC commit OK")
  }
}
