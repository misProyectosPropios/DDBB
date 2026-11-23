// MVCC (Multi-Version Concurrency Control) Simulator & Formal Isolation Lemmas.
//
// Executes MVCC operations (`BeginOp`, `ReadOp`, `FetchCursorOp`, `CloseCursorOp`,
// `WriteOp`, `CommitOp`, `AbortOp`) while maintaining `ValidMvccState` and
// enforcing the exact visibility, locking/pinning, and commit-validation rules
// of each isolation level (`RC`, `CS`, `RR`, `SI`, `SerializableMVCC`).

include "Types.dfy"
include "IsolationPolicy.dfy"

module MvccSimulation {
  import opened MvccTypes
  import opened IsolationPolicies

  // ---------------------------------------------------------------------------
  // Version-Chain & Lock Cleanup Helpers on Commit / Abort
  // ---------------------------------------------------------------------------

  // Marks every uncommitted version created by `tx` as committed at `commitTs`.
  function CommitTxVersions(
    versions: seq<TupleVersion>,
    tx: TxId,
    commitTs: Timestamp
  ): seq<TupleVersion>
    ensures |CommitTxVersions(versions, tx, commitTs)| == |versions|
    ensures forall i :: 0 <= i < |versions| ==>
      CommitTxVersions(versions, tx, commitTs)[i] ==
        (if versions[i].creatorTx == tx && !versions[i].committed then
           TupleVersion(versions[i].element, versions[i].value, tx, commitTs, true)
         else
           versions[i])
  {
    seq(|versions|, i requires 0 <= i < |versions| =>
      if versions[i].creatorTx == tx && !versions[i].committed then
        TupleVersion(versions[i].element, versions[i].value, tx, commitTs, true)
      else
        versions[i])
  }

  // Removes uncommitted versions created by `tx` upon abort/rollback.
  function RollbackTxVersions(
    versions: seq<TupleVersion>,
    tx: TxId
  ): seq<TupleVersion>
    decreases |versions|
  {
    if |versions| == 0 then []
    else if versions[0].creatorTx == tx && !versions[0].committed then
      RollbackTxVersions(versions[1..], tx)
    else
      [versions[0]] + RollbackTxVersions(versions[1..], tx)
  }

  function ReleaseTxWriteOwners(
    writeOwners: map<ElementId, TxId>,
    tx: TxId
  ): map<ElementId, TxId>
    ensures forall el :: el in ReleaseTxWriteOwners(writeOwners, tx) ==>
      el in writeOwners &&
      writeOwners[el] != tx &&
      ReleaseTxWriteOwners(writeOwners, tx)[el] == writeOwners[el]
  {
    map el | el in writeOwners && writeOwners[el] != tx :: writeOwners[el]
  }

  function ReleaseTxLockMap(
    locks: map<ElementId, set<TxId>>,
    tx: TxId
  ): map<ElementId, set<TxId>>
  {
    map el | el in locks :: locks[el] - {tx}
  }

  // ---------------------------------------------------------------------------
  // Modular Per-Operation Execution Handlers
  // ---------------------------------------------------------------------------

  // 1. BEGIN TRANSACTION at a chosen IsolationLevel
  method StepBegin(
    state: MvccState,
    tx: TxId,
    level: IsolationLevel
  ) returns (res: MvccStepResult)
    requires ValidMvccState(state)
    ensures ValidMvccState(res.nextState)
    ensures tx !in state.txs ==>
      res.allowed &&
      res.nextState == state.(
        clock := state.clock + 1,
        txs := state.txs[tx := TxMeta(tx, level, TxActive, state.clock, 0, None, {}, {})]
      )
  {
    if tx in state.txs {
      return MvccStepResult(false, state, None, None, "Transaction already exists");
    }
    var meta := TxMeta(tx, level, TxActive, state.clock, 0, None, {}, {});
    var nextState := state.(
      clock := state.clock + 1,
      txs := state.txs[tx := meta]
    );
    return MvccStepResult(true, nextState, None, None, "Transaction started");
  }

  // 2. READ ELEMENT
  method StepRead(
    state: MvccState,
    tx: TxId,
    elem: ElementId
  ) returns (res: MvccStepResult)
    requires ValidMvccState(state)
    ensures ValidMvccState(res.nextState)
    // Formal Guarantee 1: Read never returns another transaction's uncommitted write (No Dirty Reads)
    ensures res.allowed && res.readVersion.Some? ==>
      res.readVersion.value in state.versions &&
      res.readVersion.value.element == elem &&
      (res.readVersion.value.committed || res.readVersion.value.creatorTx == tx) &&
      res.readValue == Some(res.readVersion.value.value)
    // Formal Guarantee 2: Under SI and SerializableMVCC, reads of other txs' writes obey `xmin <= startTs`
    ensures (res.allowed &&
             res.readVersion.Some? &&
             tx in state.txs &&
             (state.txs[tx].level == SnapshotIsolation || state.txs[tx].level == SerializableMVCC) &&
             res.readVersion.value.creatorTx != tx) ==>
      res.readVersion.value.xmin <= state.txs[tx].startTs
    // Formal Guarantee 3: Under RepeatableRead, reading `elem` places `tx` in `rrReadLocks[elem]`
    ensures (res.allowed &&
             tx in state.txs &&
             state.txs[tx].level == RepeatableRead) ==>
      tx in RRLockHolders(res.nextState, elem)
    // Formal Guarantee 4: Under RC/CS/RR, reading an element with another tx's uncommitted write is blocked
    ensures (tx in state.txs &&
             (state.txs[tx].level == ReadCommitted ||
              state.txs[tx].level == CursorStability ||
              state.txs[tx].level == RepeatableRead) &&
             HasOtherWriteOwner(state, elem, tx)) ==>
      !res.allowed
    // Completeness & state framing when read succeeds
    ensures (tx in state.txs &&
             state.txs[tx].status == TxActive &&
             !((state.txs[tx].level == ReadCommitted ||
                state.txs[tx].level == CursorStability ||
                state.txs[tx].level == RepeatableRead) &&
               HasOtherWriteOwner(state, elem, tx)) &&
             HasVisibleVersion(state.versions, state.txs[tx], elem)) ==>
      res.allowed &&
      res.readVersion.Some? &&
      res.nextState.clock == state.clock &&
      res.nextState.versions == state.versions &&
      res.nextState.writeOwners == state.writeOwners &&
      res.nextState.csCursorPins == state.csCursorPins &&
      res.nextState.rrReadLocks ==
        (if state.txs[tx].level == RepeatableRead then
           state.rrReadLocks[elem := RRLockHolders(state, elem) + {tx}]
         else
           state.rrReadLocks) &&
      res.nextState.txs == state.txs[tx := state.txs[tx].(readSet := state.txs[tx].readSet + {elem})]
  {
    if tx !in state.txs || state.txs[tx].status != TxActive {
      return MvccStepResult(false, state, None, None, "Transaction is not active");
    }
    var meta := state.txs[tx];

    // Under locking-based levels (RC, CS, RR), reading an element with an active
    // uncommitted write by ANOTHER transaction is blocked until that writer finishes.
    if (meta.level == ReadCommitted || meta.level == CursorStability || meta.level == RepeatableRead) &&
       HasOtherWriteOwner(state, elem, tx) {
      return MvccStepResult(false, state, None, None, "Read blocked: another transaction holds an uncommitted write lock");
    }

    var found := FindLatestVisibleVersion(state.versions, meta, elem);
    match found {
      case None =>
        return MvccStepResult(false, state, None, None, "No visible version found");
      case Some(v) =>
        var updatedMeta := meta.(readSet := meta.readSet + {elem});
        var nextState := state.(txs := state.txs[tx := updatedMeta]);
        if meta.level == RepeatableRead {
          nextState := AddRRLock(nextState, elem, tx);
        }
        return MvccStepResult(true, nextState, Some(v.value), Some(v), "Read succeeded");
    }
  }

  // 3. FETCH CURSOR (Cursor Stability CS: pins `elem` and unpins previous cursor element)
  method StepFetchCursor(
    state: MvccState,
    tx: TxId,
    elem: ElementId
  ) returns (res: MvccStepResult)
    requires ValidMvccState(state)
    ensures ValidMvccState(res.nextState)
    ensures res.allowed && res.readVersion.Some? ==>
      (res.readVersion.value.committed || res.readVersion.value.creatorTx == tx) &&
      res.readValue == Some(res.readVersion.value.value)
    ensures res.allowed ==>
      tx in res.nextState.txs &&
      tx in CSPinHolders(res.nextState, elem) &&
      res.nextState.txs[tx].cursorElem == Some(elem)
    ensures (res.allowed &&
             tx in state.txs &&
             state.txs[tx].cursorElem.Some? &&
             state.txs[tx].cursorElem.value != elem) ==>
      tx !in CSPinHolders(res.nextState, state.txs[tx].cursorElem.value)
    ensures (tx in state.txs &&
             state.txs[tx].status == TxActive &&
             !HasOtherWriteOwner(state, elem, tx) &&
             HasVisibleVersion(state.versions, state.txs[tx], elem)) ==>
      res.allowed &&
      res.readVersion.Some? &&
      res.nextState.clock == state.clock &&
      res.nextState.versions == state.versions &&
      res.nextState.writeOwners == state.writeOwners &&
      res.nextState.rrReadLocks ==
        (if state.txs[tx].level == RepeatableRead then
           state.rrReadLocks[elem := RRLockHolders(state, elem) + {tx}]
         else
           state.rrReadLocks) &&
      res.nextState.csCursorPins ==
        SetCSPin(state, state.txs[tx].cursorElem, Some(elem), tx).csCursorPins &&
      res.nextState.txs == state.txs[tx := state.txs[tx].(
        cursorElem := Some(elem),
        readSet := state.txs[tx].readSet + {elem}
      )]
  {
    if tx !in state.txs || state.txs[tx].status != TxActive {
      return MvccStepResult(false, state, None, None, "Transaction is not active");
    }
    var meta := state.txs[tx];
    if HasOtherWriteOwner(state, elem, tx) {
      return MvccStepResult(false, state, None, None, "Cursor fetch blocked: another transaction holds an uncommitted write");
    }

    var found := FindLatestVisibleVersion(state.versions, meta, elem);
    match found {
      case None =>
        return MvccStepResult(false, state, None, None, "No visible version found for cursor");
      case Some(v) =>
        var pinnedState := SetCSPin(state, meta.cursorElem, Some(elem), tx);
        var updatedMeta := meta.(
          cursorElem := Some(elem),
          readSet := meta.readSet + {elem}
        );
        var nextState := pinnedState.(txs := pinnedState.txs[tx := updatedMeta]);
        if meta.level == RepeatableRead {
          nextState := AddRRLock(nextState, elem, tx);
        }
        return MvccStepResult(true, nextState, Some(v.value), Some(v), "Positioned cursor");
    }
  }

  // 4. CLOSE CURSOR (releases active cursor pin)
  method StepCloseCursor(state: MvccState, tx: TxId) returns (res: MvccStepResult)
    requires ValidMvccState(state)
    ensures ValidMvccState(res.nextState)
    ensures (res.allowed &&
             tx in state.txs &&
             state.txs[tx].cursorElem.Some?) ==>
      tx !in CSPinHolders(res.nextState, state.txs[tx].cursorElem.value)
  {
    if tx !in state.txs || state.txs[tx].status != TxActive {
      return MvccStepResult(false, state, None, None, "Transaction is not active");
    }
    var meta := state.txs[tx];
    var unpinned := SetCSPin(state, meta.cursorElem, None, tx);
    var updatedMeta := meta.(cursorElem := None);
    var nextState := unpinned.(txs := unpinned.txs[tx := updatedMeta]);
    return MvccStepResult(true, nextState, None, None, "Closed cursor");
  }

  // 5. WRITE ELEMENT (creates a new uncommitted TupleVersion and records write ownership)
  method StepWrite(
    state: MvccState,
    tx: TxId,
    elem: ElementId,
    newValue: Value
  ) returns (res: MvccStepResult)
    requires ValidMvccState(state)
    ensures ValidMvccState(res.nextState)
    ensures res.allowed ==>
      !HasOtherWriteOwner(state, elem, tx) &&
      !HasOtherCSPin(state, elem, tx) &&
      !HasOtherRRLock(state, elem, tx)
    ensures (tx in state.txs &&
             state.txs[tx].status == TxActive &&
             !WriteAllowed(state, state.txs[tx], elem)) ==>
      !res.allowed
    ensures (tx in state.txs &&
             state.txs[tx].status == TxActive &&
             WriteAllowed(state, state.txs[tx], elem)) ==>
      res.allowed &&
      res.nextState == state.(
        clock := state.clock + 1,
        versions := state.versions + [TupleVersion(elem, newValue, tx, state.clock, false)],
        txs := state.txs[tx := state.txs[tx].(writeSet := state.txs[tx].writeSet + {elem})],
        writeOwners := state.writeOwners[elem := tx]
      )
  {
    if tx !in state.txs || state.txs[tx].status != TxActive {
      return MvccStepResult(false, state, None, None, "Transaction is not active");
    }
    var meta := state.txs[tx];
    var (ok, reason) := CheckWriteAllowed(state, meta, elem);
    if !ok {
      return MvccStepResult(false, state, None, None, reason);
    }

    var newVer := TupleVersion(elem, newValue, tx, state.clock, false);
    var updatedMeta := meta.(writeSet := meta.writeSet + {elem});
    var nextState := state.(
      clock := state.clock + 1,
      versions := state.versions + [newVer],
      txs := state.txs[tx := updatedMeta],
      writeOwners := state.writeOwners[elem := tx]
    );
    return MvccStepResult(true, nextState, None, Some(newVer), "Wrote uncommitted version");
  }

  // 6. COMMIT TRANSACTION (validates SI / Serializable rules, publishes versions at commitTs, releases locks/pins)
  method StepCommit(state: MvccState, tx: TxId) returns (res: MvccStepResult)
    requires ValidMvccState(state)
    ensures ValidMvccState(res.nextState)
    ensures (tx in state.txs &&
             state.txs[tx].status == TxActive &&
             !CommitAllowed(state, state.txs[tx])) ==>
      !res.allowed
    ensures (tx in state.txs &&
             state.txs[tx].status == TxActive &&
             CommitAllowed(state, state.txs[tx])) ==>
      res.allowed &&
      res.nextState == MvccState(
        state.clock + 1,
        CommitTxVersions(state.versions, tx, state.clock),
        state.txs[tx := state.txs[tx].(
          status := TxCommitted,
          commitTs := state.clock,
          cursorElem := None
        )],
        ReleaseTxWriteOwners(state.writeOwners, tx),
        ReleaseTxLockMap(state.rrReadLocks, tx),
        ReleaseTxLockMap(state.csCursorPins, tx)
      )
  {
    if tx !in state.txs || state.txs[tx].status != TxActive {
      return MvccStepResult(false, state, None, None, "Transaction is not active");
    }
    var meta := state.txs[tx];
    var (ok, reason) := CheckCommitAllowed(state, meta);
    if !ok {
      return MvccStepResult(false, state, None, None, reason);
    }

    var commitTs := state.clock;
    var committedVersions := CommitTxVersions(state.versions, tx, commitTs);
    var cleanedOwners := ReleaseTxWriteOwners(state.writeOwners, tx);
    var cleanedRR := ReleaseTxLockMap(state.rrReadLocks, tx);
    var cleanedCS := ReleaseTxLockMap(state.csCursorPins, tx);
    var committedMeta := meta.(
      status := TxCommitted,
      commitTs := commitTs,
      cursorElem := None
    );

    var nextState := MvccState(
      state.clock + 1,
      committedVersions,
      state.txs[tx := committedMeta],
      cleanedOwners,
      cleanedRR,
      cleanedCS
    );
    return MvccStepResult(true, nextState, None, None, reason);
  }

  // 7. ABORT TRANSACTION (rolls back uncommitted versions, releases write ownership, RR locks, and CS pins)
  method StepAbort(state: MvccState, tx: TxId) returns (res: MvccStepResult)
    requires ValidMvccState(state)
    ensures ValidMvccState(res.nextState)
    ensures (tx in state.txs && state.txs[tx].status == TxActive) ==>
      res.allowed &&
      res.nextState == MvccState(
        state.clock + 1,
        RollbackTxVersions(state.versions, tx),
        state.txs[tx := state.txs[tx].(
          status := TxAborted,
          cursorElem := None
        )],
        ReleaseTxWriteOwners(state.writeOwners, tx),
        ReleaseTxLockMap(state.rrReadLocks, tx),
        ReleaseTxLockMap(state.csCursorPins, tx)
      )
  {
    if tx !in state.txs || state.txs[tx].status != TxActive {
      return MvccStepResult(false, state, None, None, "Transaction is not active");
    }
    var meta := state.txs[tx];
    var rolledBackVersions := RollbackTxVersions(state.versions, tx);
    var cleanedOwners := ReleaseTxWriteOwners(state.writeOwners, tx);
    var cleanedRR := ReleaseTxLockMap(state.rrReadLocks, tx);
    var cleanedCS := ReleaseTxLockMap(state.csCursorPins, tx);
    var abortedMeta := meta.(
      status := TxAborted,
      cursorElem := None
    );

    var nextState := MvccState(
      state.clock + 1,
      rolledBackVersions,
      state.txs[tx := abortedMeta],
      cleanedOwners,
      cleanedRR,
      cleanedCS
    );
    return MvccStepResult(true, nextState, None, None, "Transaction aborted and rolled back");
  }

  // Unified single-step dispatcher
  method StepMvcc(state: MvccState, op: MvccOp) returns (res: MvccStepResult)
    requires ValidMvccState(state)
    ensures ValidMvccState(res.nextState)
  {
    match op {
      case BeginOp(tx, level) =>
        res := StepBegin(state, tx, level);
      case ReadOp(tx, elem) =>
        res := StepRead(state, tx, elem);
      case FetchCursorOp(tx, elem) =>
        res := StepFetchCursor(state, tx, elem);
      case CloseCursorOp(tx) =>
        res := StepCloseCursor(state, tx);
      case WriteOp(tx, elem, val) =>
        res := StepWrite(state, tx, elem, val);
      case CommitOp(tx) =>
        res := StepCommit(state, tx);
      case AbortOp(tx) =>
        res := StepAbort(state, tx);
    }
  }

  // Executes a sequence of MVCC operations while preserving `ValidMvccState`.
  method SimulateSchedule(initState: MvccState, ops: seq<MvccOp>)
    returns (finalState: MvccState, results: seq<MvccStepResult>)
    requires ValidMvccState(initState)
    ensures ValidMvccState(finalState)
    ensures |results| == |ops|
  {
    finalState := initState;
    results := [];
    var i := 0;
    while i < |ops|
      invariant 0 <= i <= |ops|
      invariant ValidMvccState(finalState)
      invariant |results| == i
      decreases |ops| - i
    {
      var stepRes := StepMvcc(finalState, ops[i]);
      finalState := stepRes.nextState;
      results := results + [stepRes];
      i := i + 1;
    }
  }

  // ---------------------------------------------------------------------------
  // Formal Isolation & Anomaly Prevention Lemmas
  // ---------------------------------------------------------------------------

  // Lemma 1: Under Cursor Stability (CS), if `holderTx` currently holds a cursor
  // pin on `elem`, any other transaction `writerTx != holderTx` is forbidden
  // from writing `elem`.
  lemma LemmaCursorPinBlocksOtherWriter(
    state: MvccState,
    holderTx: TxId,
    writerMeta: TxMeta,
    elem: ElementId
  )
    requires holderTx in CSPinHolders(state, elem)
    requires writerMeta.tx != holderTx
    ensures !WriteAllowed(state, writerMeta, elem)
  {
    LemmaOtherTxInSet(CSPinHolders(state, elem), writerMeta.tx, holderTx);
  }

  // Lemma 2: Under Repeatable Read (RR), if `holderTx` holds an active RR read
  // lock on `elem`, any other transaction `writerTx != holderTx` is forbidden
  // from writing `elem`.
  lemma LemmaRepeatableReadLockBlocksOtherWriter(
    state: MvccState,
    holderTx: TxId,
    writerMeta: TxMeta,
    elem: ElementId
  )
    requires holderTx in RRLockHolders(state, elem)
    requires writerMeta.tx != holderTx
    ensures !WriteAllowed(state, writerMeta, elem)
  {
    LemmaOtherTxInSet(RRLockHolders(state, elem), writerMeta.tx, holderTx);
  }

  // Lemma 3: Under Snapshot Isolation (SI) or SerializableMVCC, if another
  // transaction `otherTx != meta.tx` committed a version `v` of `elem` in
  // `state.versions` with `v.xmin > meta.startTs`, First-Committer-Wins
  // rejects any write on `elem` by `meta` (preventing Lost Updates).
  lemma LemmaFirstCommitterWinsPreventsLostUpdate(
    state: MvccState,
    meta: TxMeta,
    elem: ElementId,
    vIdx: nat
  )
    requires meta.level == SnapshotIsolation || meta.level == SerializableMVCC
    requires vIdx < |state.versions|
    requires state.versions[vIdx].element == elem
    requires state.versions[vIdx].committed
    requires state.versions[vIdx].creatorTx != meta.tx
    requires state.versions[vIdx].xmin > meta.startTs
    ensures !WriteAllowed(state, meta, elem)
  {
    LemmaHasCommittedVersionAfterWitness(state.versions, elem, meta.tx, meta.startTs, vIdx);
  }

  // Lemma 4: Under SerializableMVCC (SSI), if `meta` read `readElem`
  // (`readElem in meta.readSet`) and wrote at least one element (`meta.writeSet != {}`),
  // and another transaction committed a new version of `readElem` at index `vIdx`
  // with `xmin > meta.startTs`, then `CommitAllowed(state, meta)` rejects
  // `meta`'s commit (preventing Write Skew!).
  lemma LemmaSerializablePreventsWriteSkew(
    state: MvccState,
    meta: TxMeta,
    readElem: ElementId,
    vIdx: nat
  )
    requires meta.level == SerializableMVCC
    requires readElem in meta.readSet
    requires meta.writeSet != {}
    requires vIdx < |state.versions|
    requires state.versions[vIdx].element == readElem
    requires state.versions[vIdx].committed
    requires state.versions[vIdx].creatorTx != meta.tx
    requires state.versions[vIdx].xmin > meta.startTs
    ensures !CommitAllowed(state, meta)
  {
    LemmaSetHasCommittedVersionAfterWitness(state.versions, meta.readSet, meta.tx, meta.startTs, vIdx);
  }
}
