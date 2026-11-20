// Composable Checkpointing Strategy interface and implementations
// (NoCheckpoint, Quiescent, NonQuiescent).
//
// Both UndoLogger and RedoLogger compose a `CheckpointStrategy` instance and
// store a `CheckpointState` value, separating *how* checkpointing works from
// *how* Undo / Redo logging works (Strategy / Bridge composition).

include "Types.dfy"

module Checkpointing {
  import opened LoggingTypes

  // Runtime state of an in-progress checkpoint (stored on the logger).
  datatype CheckpointState =
    | CkptIdle
    | CkptDrainingQuiescent
    | CkptActiveNonQuiescent(watchedTxs: set<TxId>)

  // Invariant connecting checkpoint state, active transactions, and log history.
  ghost predicate ValidCheckpointState(
    state: CheckpointState,
    activeTxs: set<TxId>,
    log: seq<LogRecord>
  )
  {
    match state
    case CkptIdle => true
    case CkptDrainingQuiescent => activeTxs != {}
    case CkptActiveNonQuiescent(watched) =>
      watched <= activeTxs && watched != {} && HasStartCheckpoint(log)
  }

  // Ensures emitted checkpoint records are exclusively checkpoint records and
  // any <END CKPT> is preceded by a <START CKPT(...)> either already in the log
  // or earlier in `recs`.
  ghost predicate ValidCheckpointEmission(recs: seq<LogRecord>, alreadyHasStart: bool)
  {
    (forall i :: 0 <= i < |recs| ==> IsCheckpointRecord(recs[i])) &&
    (forall i :: 0 <= i < |recs| && recs[i].LogEndCheckpoint? ==>
      alreadyHasStart || exists s :: 0 <= s < i && recs[s].LogStartCheckpoint?)
  }

  ghost predicate HasStartCheckpointIn(recs: seq<LogRecord>)
  {
    exists i :: 0 <= i < |recs| && recs[i].LogStartCheckpoint?
  }

  // Proof helpers supplying explicit index-0 witnesses for non-quiescent
  // checkpoint record emissions.
  lemma LemmaStartAndEndEmission(activeOrder: seq<TxId>, alreadyHasStart: bool)
    ensures ValidCheckpointEmission([LogStartCheckpoint(activeOrder), LogEndCheckpoint], alreadyHasStart)
  {
    var recs := [LogStartCheckpoint(activeOrder), LogEndCheckpoint];
    assert recs[0].LogStartCheckpoint?;
  }

  lemma LemmaStartOnlyEmission(activeOrder: seq<TxId>, alreadyHasStart: bool)
    ensures ValidCheckpointEmission([LogStartCheckpoint(activeOrder)], alreadyHasStart)
    ensures HasStartCheckpointIn([LogStartCheckpoint(activeOrder)])
  {
    var recs := [LogStartCheckpoint(activeOrder)];
    assert recs[0].LogStartCheckpoint?;
  }

  // ---------------------------------------------------------------------------
  // CheckpointStrategy interface
  // ---------------------------------------------------------------------------

  trait CheckpointStrategy extends object {
    function Name(): string

    // Whether a new transaction is allowed to START in `state`.
    function CanStartTransaction(state: CheckpointState): bool

    function BlockedStartMessage(tx: TxId): string

    // Called when a CheckpointOp is processed.
    // `waitsForActiveOnNonQuiescent`:
    //   - true for Undo logging (must wait for snapshotted activeTxs to finish
    //     before writing <END CKPT>)
    //   - false for Redo logging (writes <START CKPT(...)> and <END CKPT>
    //     immediately once committed updates are on disk)
    function OnCheckpointRequested(
      state: CheckpointState,
      activeTxs: set<TxId>,
      activeOrder: seq<TxId>,
      waitsForActiveOnNonQuiescent: bool
    ): (CheckpointState, seq<LogRecord>, string)
      requires forall tx :: tx in activeOrder <==> tx in activeTxs
      ensures var res := OnCheckpointRequested(state, activeTxs, activeOrder, waitsForActiveOnNonQuiescent);
        var nextState := res.0;
        var recs := res.1;
        var err := res.2;
        ValidCheckpointEmission(recs, state.CkptActiveNonQuiescent?) &&
        (err != "" ==> nextState == state && recs == []) &&
        (err == "" ==>
          (nextState.CkptDrainingQuiescent? ==> activeTxs != {}) &&
          (nextState.CkptActiveNonQuiescent? ==>
            nextState.watchedTxs <= activeTxs &&
            nextState.watchedTxs != {} &&
            (state.CkptActiveNonQuiescent? || HasStartCheckpointIn(recs))))

    // Called right after `tx` commits or aborts (`remainingActiveTxs` no longer
    // contains `tx`).
    function OnTransactionFinished(
      state: CheckpointState,
      tx: TxId,
      remainingActiveTxs: set<TxId>
    ): (CheckpointState, seq<LogRecord>)
      requires state.CkptActiveNonQuiescent? ==> state.watchedTxs <= remainingActiveTxs + {tx}
      ensures var res := OnTransactionFinished(state, tx, remainingActiveTxs);
        var nextState := res.0;
        var recs := res.1;
        ValidCheckpointEmission(recs, state.CkptActiveNonQuiescent?) &&
        (nextState.CkptDrainingQuiescent? ==> remainingActiveTxs != {}) &&
        (nextState.CkptActiveNonQuiescent? ==>
          nextState.watchedTxs <= remainingActiveTxs &&
          nextState.watchedTxs != {} &&
          state.CkptActiveNonQuiescent?)
  }

  // ---------------------------------------------------------------------------
  // 1. NoCheckpointStrategy — pure logging without checkpoints
  // ---------------------------------------------------------------------------

  class NoCheckpointStrategy extends CheckpointStrategy {
    constructor () {}

    function Name(): string { "None" }

    function CanStartTransaction(state: CheckpointState): bool { true }

    function BlockedStartMessage(tx: TxId): string { "" }

    function OnCheckpointRequested(
      state: CheckpointState,
      activeTxs: set<TxId>,
      activeOrder: seq<TxId>,
      waitsForActiveOnNonQuiescent: bool
    ): (CheckpointState, seq<LogRecord>, string)
      requires forall tx :: tx in activeOrder <==> tx in activeTxs
      ensures var res := OnCheckpointRequested(state, activeTxs, activeOrder, waitsForActiveOnNonQuiescent);
        var nextState := res.0;
        var recs := res.1;
        var err := res.2;
        ValidCheckpointEmission(recs, state.CkptActiveNonQuiescent?) &&
        (err != "" ==> nextState == state && recs == []) &&
        (err == "" ==>
          (nextState.CkptDrainingQuiescent? ==> activeTxs != {}) &&
          (nextState.CkptActiveNonQuiescent? ==>
            nextState.watchedTxs <= activeTxs &&
            nextState.watchedTxs != {} &&
            (state.CkptActiveNonQuiescent? || HasStartCheckpointIn(recs))))
    {
      (state, [], "Checkpointing is disabled for this logger.")
    }

    function OnTransactionFinished(
      state: CheckpointState,
      tx: TxId,
      remainingActiveTxs: set<TxId>
    ): (CheckpointState, seq<LogRecord>)
      requires state.CkptActiveNonQuiescent? ==> state.watchedTxs <= remainingActiveTxs + {tx}
      ensures var res := OnTransactionFinished(state, tx, remainingActiveTxs);
        var nextState := res.0;
        var recs := res.1;
        ValidCheckpointEmission(recs, state.CkptActiveNonQuiescent?) &&
        (nextState.CkptDrainingQuiescent? ==> remainingActiveTxs != {}) &&
        (nextState.CkptActiveNonQuiescent? ==>
          nextState.watchedTxs <= remainingActiveTxs &&
          nextState.watchedTxs != {} &&
          state.CkptActiveNonQuiescent?)
    {
      (CkptIdle, [])
    }
  }

  // ---------------------------------------------------------------------------
  // 2. QuiescentCheckpointStrategy — blocks new transactions until activeTxs
  //    drain, then emits <CKPT> and resumes accepting new transactions.
  // ---------------------------------------------------------------------------

  class QuiescentCheckpointStrategy extends CheckpointStrategy {
    constructor () {}

    function Name(): string { "Quiescent" }

    function CanStartTransaction(state: CheckpointState): bool
    {
      !state.CkptDrainingQuiescent?
    }

    function BlockedStartMessage(tx: TxId): string
    {
      "Cannot START " + tx + ": quiescent checkpoint is waiting for active transactions to finish."
    }

    function OnCheckpointRequested(
      state: CheckpointState,
      activeTxs: set<TxId>,
      activeOrder: seq<TxId>,
      waitsForActiveOnNonQuiescent: bool
    ): (CheckpointState, seq<LogRecord>, string)
      requires forall tx :: tx in activeOrder <==> tx in activeTxs
      ensures var res := OnCheckpointRequested(state, activeTxs, activeOrder, waitsForActiveOnNonQuiescent);
        var nextState := res.0;
        var recs := res.1;
        var err := res.2;
        ValidCheckpointEmission(recs, state.CkptActiveNonQuiescent?) &&
        (err != "" ==> nextState == state && recs == []) &&
        (err == "" ==>
          (nextState.CkptDrainingQuiescent? ==> activeTxs != {}) &&
          (nextState.CkptActiveNonQuiescent? ==>
            nextState.watchedTxs <= activeTxs &&
            nextState.watchedTxs != {} &&
            (state.CkptActiveNonQuiescent? || HasStartCheckpointIn(recs))))
    {
      if !state.CkptIdle? then
        (state, [], "Cannot start checkpoint: another checkpoint is already in progress.")
      else if activeTxs == {} then
        (CkptIdle, [LogCheckpoint], "")
      else
        (CkptDrainingQuiescent, [], "")
    }

    function OnTransactionFinished(
      state: CheckpointState,
      tx: TxId,
      remainingActiveTxs: set<TxId>
    ): (CheckpointState, seq<LogRecord>)
      requires state.CkptActiveNonQuiescent? ==> state.watchedTxs <= remainingActiveTxs + {tx}
      ensures var res := OnTransactionFinished(state, tx, remainingActiveTxs);
        var nextState := res.0;
        var recs := res.1;
        ValidCheckpointEmission(recs, state.CkptActiveNonQuiescent?) &&
        (nextState.CkptDrainingQuiescent? ==> remainingActiveTxs != {}) &&
        (nextState.CkptActiveNonQuiescent? ==>
          nextState.watchedTxs <= remainingActiveTxs &&
          nextState.watchedTxs != {} &&
          state.CkptActiveNonQuiescent?)
    {
      if state.CkptDrainingQuiescent? then
        if remainingActiveTxs == {} then
          (CkptIdle, [LogCheckpoint])
        else
          (CkptDrainingQuiescent, [])
      else
        (CkptIdle, [])
    }
  }

  // ---------------------------------------------------------------------------
  // 3. NonQuiescentCheckpointStrategy — allows new transactions to start while
  //    checkpointing.
  //    - Undo (`waitsForActiveOnNonQuiescent == true`): writes <START CKPT(active)>
  //      and emits <END CKPT> once all snapshotted active transactions finish.
  //    - Redo (`waitsForActiveOnNonQuiescent == false`): writes <START CKPT(active)>
  //      and <END CKPT> immediately (committed data is already on disk).
  // ---------------------------------------------------------------------------

  class NonQuiescentCheckpointStrategy extends CheckpointStrategy {
    constructor () {}

    function Name(): string { "Non-Quiescent" }

    function CanStartTransaction(state: CheckpointState): bool { true }

    function BlockedStartMessage(tx: TxId): string { "" }

    function OnCheckpointRequested(
      state: CheckpointState,
      activeTxs: set<TxId>,
      activeOrder: seq<TxId>,
      waitsForActiveOnNonQuiescent: bool
    ): (CheckpointState, seq<LogRecord>, string)
      requires forall tx :: tx in activeOrder <==> tx in activeTxs
      ensures var res := OnCheckpointRequested(state, activeTxs, activeOrder, waitsForActiveOnNonQuiescent);
        var nextState := res.0;
        var recs := res.1;
        var err := res.2;
        ValidCheckpointEmission(recs, state.CkptActiveNonQuiescent?) &&
        (err != "" ==> nextState == state && recs == []) &&
        (err == "" ==>
          (nextState.CkptDrainingQuiescent? ==> activeTxs != {}) &&
          (nextState.CkptActiveNonQuiescent? ==>
            nextState.watchedTxs <= activeTxs &&
            nextState.watchedTxs != {} &&
            (state.CkptActiveNonQuiescent? || HasStartCheckpointIn(recs))))
    {
      if !state.CkptIdle? then
        (state, [], "Cannot start checkpoint: another checkpoint is already in progress.")
      else if !waitsForActiveOnNonQuiescent || activeTxs == {} then
        LemmaStartAndEndEmission(activeOrder, state.CkptActiveNonQuiescent?);
        (CkptIdle, [LogStartCheckpoint(activeOrder), LogEndCheckpoint], "")
      else
        LemmaStartOnlyEmission(activeOrder, state.CkptActiveNonQuiescent?);
        (CkptActiveNonQuiescent(activeTxs), [LogStartCheckpoint(activeOrder)], "")
    }

    function OnTransactionFinished(
      state: CheckpointState,
      tx: TxId,
      remainingActiveTxs: set<TxId>
    ): (CheckpointState, seq<LogRecord>)
      requires state.CkptActiveNonQuiescent? ==> state.watchedTxs <= remainingActiveTxs + {tx}
      ensures var res := OnTransactionFinished(state, tx, remainingActiveTxs);
        var nextState := res.0;
        var recs := res.1;
        ValidCheckpointEmission(recs, state.CkptActiveNonQuiescent?) &&
        (nextState.CkptDrainingQuiescent? ==> remainingActiveTxs != {}) &&
        (nextState.CkptActiveNonQuiescent? ==>
          nextState.watchedTxs <= remainingActiveTxs &&
          nextState.watchedTxs != {} &&
          state.CkptActiveNonQuiescent?)
    {
      if state.CkptActiveNonQuiescent? then
        var remaining := state.watchedTxs - {tx};
        if remaining == {} then
          (CkptIdle, [LogEndCheckpoint])
        else
          (CkptActiveNonQuiescent(remaining), [])
      else
        (CkptIdle, [])
    }
  }
}
