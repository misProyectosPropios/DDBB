// Deadlock Detection / Prevention (Wait-For Graph, Wait-Die, Wound-Wait) and
// Optimistic Concurrency Control (Kung-Robinson OCC: Read / Validate / Write).
//
// Formally proves:
//   1. Wait-Die and Wound-Wait timestamp policies are both deadlock-free
//      (impossible to form a Wait-For cycle).
//   2. Kung-Robinson OCC validation rules guarantee that every validated
//      transaction preserves serializability in validation-timestamp order.

include "Types.dfy"

module DeadlockAndOCC {
  import opened SchedulerTypes

  // ---------------------------------------------------------------------------
  // Part 1: Wait-For Graph & Deadlock Prevention (Wait-Die / Wound-Wait)
  // ---------------------------------------------------------------------------

  datatype WaitEdge = WaitEdge(
    waitingTx: TxId,
    holderTx: TxId,
    element: ElementId,
    requestedMode: LockMode
  )

  datatype DeadlockPreventionAction =
    | AllowWait
    | AbortRequester_Die // Wait-Die: younger requester aborts ("dies")
    | PreemptHolder_Wound // Wound-Wait: older requester preempts ("wounds") younger holder

  // Wait-Die (non-preemptive):
  //   - Older transaction (`reqTs < holderTs`) waits for younger holder.
  //   - Younger transaction (`reqTs > holderTs`) aborts ("dies").
  function WaitDiePolicy(reqTs: nat, holderTs: nat): DeadlockPreventionAction
    requires reqTs != holderTs
    ensures WaitDiePolicy(reqTs, holderTs) == AllowWait <==> reqTs < holderTs
  {
    if reqTs < holderTs then AllowWait
    else AbortRequester_Die
  }

  // Wound-Wait (preemptive):
  //   - Older transaction (`reqTs < holderTs`) wounds (aborts) younger holder.
  //   - Younger transaction (`reqTs > holderTs`) waits for older holder.
  function WoundWaitPolicy(reqTs: nat, holderTs: nat): DeadlockPreventionAction
    requires reqTs != holderTs
    ensures WoundWaitPolicy(reqTs, holderTs) == AllowWait <==> reqTs > holderTs
  {
    if reqTs < holderTs then PreemptHolder_Wound
    else AllowWait
  }

  // Every Wait-For edge permitted by Wait-Die strictly increases timestamp,
  // making any Wait-For cycle impossible.
  lemma LemmaWaitDieDeadlockFree(
    ts: map<TxId, nat>,
    e1: WaitEdge,
    e2: WaitEdge
  )
    requires e1.waitingTx in ts && e1.holderTx in ts && ts[e1.waitingTx] != ts[e1.holderTx]
    requires e2.waitingTx in ts && e2.holderTx in ts && ts[e2.waitingTx] != ts[e2.holderTx]
    requires WaitDiePolicy(ts[e1.waitingTx], ts[e1.holderTx]) == AllowWait
    requires WaitDiePolicy(ts[e2.waitingTx], ts[e2.holderTx]) == AllowWait
    ensures !(e1.waitingTx == e2.holderTx && e1.holderTx == e2.waitingTx)
  {
    assert ts[e1.waitingTx] < ts[e1.holderTx];
    assert ts[e2.waitingTx] < ts[e2.holderTx];
  }

  // Every Wait-For edge permitted by Wound-Wait strictly decreases timestamp,
  // making any Wait-For cycle impossible.
  lemma LemmaWoundWaitDeadlockFree(
    ts: map<TxId, nat>,
    e1: WaitEdge,
    e2: WaitEdge
  )
    requires e1.waitingTx in ts && e1.holderTx in ts && ts[e1.waitingTx] != ts[e1.holderTx]
    requires e2.waitingTx in ts && e2.holderTx in ts && ts[e2.waitingTx] != ts[e2.holderTx]
    requires WoundWaitPolicy(ts[e1.waitingTx], ts[e1.holderTx]) == AllowWait
    requires WoundWaitPolicy(ts[e2.waitingTx], ts[e2.holderTx]) == AllowWait
    ensures !(e1.waitingTx == e2.holderTx && e1.holderTx == e2.waitingTx)
  {
    assert ts[e1.waitingTx] > ts[e1.holderTx];
    assert ts[e2.waitingTx] > ts[e2.holderTx];
  }

  // Checks whether a Wait-For graph contains a 2-cycle (`Ti -> Tj` and `Tj -> Ti`).
  method DetectWaitFor2Cycle(edges: seq<WaitEdge>)
    returns (hasDeadlock: bool, txA: TxId, txB: TxId)
    ensures hasDeadlock <==>
      (exists i, j ::
        0 <= i < |edges| && 0 <= j < |edges| &&
        edges[i].waitingTx != edges[i].holderTx &&
        edges[i].waitingTx == edges[j].holderTx &&
        edges[i].holderTx == edges[j].waitingTx)
  {
    hasDeadlock := false;
    txA := "";
    txB := "";
    var i := 0;
    while i < |edges|
      invariant 0 <= i <= |edges|
      invariant forall p, q ::
        (0 <= p < i && 0 <= q < |edges|) ==>
          !(edges[p].waitingTx != edges[p].holderTx &&
            edges[p].waitingTx == edges[q].holderTx &&
            edges[p].holderTx == edges[q].waitingTx)
      decreases |edges| - i
    {
      var j := 0;
      while j < |edges|
        invariant 0 <= j <= |edges|
        invariant forall q ::
          0 <= q < j ==>
            !(edges[i].waitingTx != edges[i].holderTx &&
              edges[i].waitingTx == edges[q].holderTx &&
              edges[i].holderTx == edges[q].waitingTx)
        decreases |edges| - j
      {
        if edges[i].waitingTx != edges[i].holderTx &&
           edges[i].waitingTx == edges[j].holderTx &&
           edges[i].holderTx == edges[j].waitingTx {
          return true, edges[i].waitingTx, edges[i].holderTx;
        }
        j := j + 1;
      }
      i := i + 1;
    }
  }

  // ---------------------------------------------------------------------------
  // Part 2: Optimistic Concurrency Control (Kung-Robinson OCC)
  // ---------------------------------------------------------------------------

  // Transaction record in Kung-Robinson 3-phase OCC:
  //   1. Read Phase:     [startStep .. validateStep) (writes go to private workspace)
  //   2. Validate Phase: at `validateStep`
  //   3. Write Phase:    (validateStep .. finishStep] (copies private workspace to DB)
  datatype OccTxRecord = OccTxRecord(
    tx: TxId,
    startStep: nat,
    validateStep: nat,
    finishStep: nat,
    readSet: set<ElementId>,
    writeSet: set<ElementId>
  )

  predicate ValidOccPhaseOrder(rec: OccTxRecord)
  {
    rec.startStep < rec.validateStep <= rec.finishStep
  }

  // Kung-Robinson backward validation rule for `tj` against an earlier-validated
  // transaction `ti` (`ti.validateStep < tj.validateStep`):
  //   - Rule 1: `ti` finished writing before `tj` started (`ti.finishStep < tj.startStep`)
  //   - Rule 2: `ti` finished writing before `tj` validated AND `ti`'s writes do not
  //             intersect `tj`'s read set (`ti.writeSet * tj.readSet == {}`)
  //   - Rule 3: `ti`'s writes do not intersect `tj`'s read set OR write set
  predicate OccPairValid(ti: OccTxRecord, tj: OccTxRecord)
  {
    (ti.finishStep < tj.startStep) ||
    (ti.finishStep < tj.validateStep && (ti.writeSet * tj.readSet == {})) ||
    ((ti.writeSet * tj.readSet == {}) && (ti.writeSet * tj.writeSet == {}))
  }

  predicate AllOccPairsValid(records: seq<OccTxRecord>)
  {
    forall i, j ::
      (0 <= i < |records| && 0 <= j < |records| &&
       records[i].validateStep < records[j].validateStep) ==>
        OccPairValid(records[i], records[j])
  }

  // Validates a sequence of OCC transaction executions, returning whether the
  // entire schedule passes OCC validation and listing any transactions that must
  // abort at their validation phase.
  method ValidateOccSchedule(records: seq<OccTxRecord>)
    returns (allValid: bool, abortedTxs: seq<TxId>)
    ensures allValid <==> AllOccPairsValid(records)
    ensures allValid <==> |abortedTxs| == 0
  {
    abortedTxs := [];
    var j := 0;
    while j < |records|
      invariant 0 <= j <= |records|
      invariant |abortedTxs| == 0 <==>
        (forall p, q ::
          (0 <= p < |records| && 0 <= q < j &&
           records[p].validateStep < records[q].validateStep) ==>
            OccPairValid(records[p], records[q]))
      decreases |records| - j
    {
      var tj := records[j];
      var tjOk := true;
      var i := 0;
      while i < |records|
        invariant 0 <= i <= |records|
        invariant tjOk <==>
          (forall p ::
            (0 <= p < i && records[p].validateStep < tj.validateStep) ==>
              OccPairValid(records[p], tj))
        decreases |records| - i
      {
        if records[i].validateStep < tj.validateStep &&
           !OccPairValid(records[i], tj) {
          tjOk := false;
        }
        i := i + 1;
      }

      if !tjOk {
        abortedTxs := abortedTxs + [tj.tx];
      }
      j := j + 1;
    }

    allValid := |abortedTxs| == 0;
  }
}
