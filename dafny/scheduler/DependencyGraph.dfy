// Precedence / Dependency Graph Generator & Topological Serial-Order Verifier.
//
// Constructs the conflict graph `G = (V, E)` of a schedule `ops`:
//   - Nodes `V`: distinct transaction IDs participating in `ops`
//   - Directed edges `E`: `Ti -> Tj` whenever an operation of `Ti` precedes a
//     conflicting operation of `Tj` on the same element (`RW`, `WR`, or `WW`).
// Also verifies topological transaction orders and proves that any schedule
// admitting a topological order is free of conflict cycles.

include "Types.dfy"
include "LockPolicy.dfy"
include "Serializability.dfy"

module DependencyGraph {
  import opened SchedulerTypes
  import opened LockPolicies
  import opened Serializability

  datatype ConflictKind =
    | ConflictRW // Read(Ti, X)  before Write(Tj, X) — Anti-dependency
    | ConflictWR // Write(Ti, X) before Read(Tj, X)  — Read-From / Dirty-Read dependency
    | ConflictWW // Write(Ti, X) before Write(Tj, X) — Overwrite dependency

  datatype ConflictEdge = ConflictEdge(
    fromTx: TxId,
    toTx: TxId,
    element: ElementId,
    kind: ConflictKind,
    fromStep: nat,
    toStep: nat
  )

  datatype PrecedenceGraph = PrecedenceGraph(
    nodes: seq<TxId>,
    edges: seq<ConflictEdge>
  )

  function ClassifyConflict(a: SchedOp, b: SchedOp): ConflictKind
    requires IsDataOp(a) && IsDataOp(b)
    requires Conflicts(a, b)
  {
    if a.ReadOp? && b.WriteOp? then ConflictRW
    else if a.WriteOp? && b.ReadOp? then ConflictWR
    else ConflictWW
  }

  function FormatConflictKind(k: ConflictKind): string
  {
    match k
    case ConflictRW => "RW"
    case ConflictWR => "WR"
    case ConflictWW => "WW"
  }

  predicate HasConflictPairEdge(
    edges: seq<ConflictEdge>,
    fromTx: TxId,
    toTx: TxId
  )
  {
    exists k :: 0 <= k < |edges| && edges[k].fromTx == fromTx && edges[k].toTx == toTx
  }

  // Builds the complete precedence graph of `ops`, guaranteeing that every
  // conflicting pair in `DataOps(ops)` is represented by a directed edge.
  method BuildPrecedenceGraph(ops: seq<SchedOp>) returns (g: PrecedenceGraph)
    ensures var d := DataOps(ops);
      forall i, j :: (0 <= i < j < |d| && Conflicts(d[i], d[j])) ==>
        HasConflictPairEdge(g.edges, d[i].tx, d[j].tx)
    ensures forall k :: 0 <= k < |g.edges| ==> g.edges[k].fromTx != g.edges[k].toTx
  {
    var d := DataOps(ops);
    var nodes: seq<TxId> := [];
    var nIdx := 0;
    while nIdx < |ops|
      invariant 0 <= nIdx <= |ops|
      decreases |ops| - nIdx
    {
      var tx := ops[nIdx].tx;
      if tx !in nodes {
        nodes := nodes + [tx];
      }
      nIdx := nIdx + 1;
    }

    var edges: seq<ConflictEdge> := [];
    var i := 0;
    while i < |d|
      invariant 0 <= i <= |d|
      invariant forall k :: 0 <= k < |edges| ==> edges[k].fromTx != edges[k].toTx
      invariant forall p, q :: (0 <= p < i && p < q < |d| && Conflicts(d[p], d[q])) ==>
        HasConflictPairEdge(edges, d[p].tx, d[q].tx)
      decreases |d| - i
    {
      var j := i + 1;
      while j < |d|
        invariant i < j <= |d|
        invariant forall k :: 0 <= k < |edges| ==> edges[k].fromTx != edges[k].toTx
        invariant forall p, q :: (0 <= p < i && p < q < |d| && Conflicts(d[p], d[q])) ==>
          HasConflictPairEdge(edges, d[p].tx, d[q].tx)
        invariant forall q :: (i < q < j && Conflicts(d[i], d[q])) ==>
          HasConflictPairEdge(edges, d[i].tx, d[q].tx)
        decreases |d| - j
      {
        if Conflicts(d[i], d[j]) {
          var kind := ClassifyConflict(d[i], d[j]);
          var edge := ConflictEdge(d[i].tx, d[j].tx, d[i].element, kind, i, j);
          var prev := edges;
          edges := edges + [edge];
          assert edges[|prev|] == edge;
          assert HasConflictPairEdge(edges, d[i].tx, d[j].tx);
          forall p, q | 0 <= p < i && p < q < |d| && Conflicts(d[p], d[q])
            ensures HasConflictPairEdge(edges, d[p].tx, d[q].tx)
          {
            var w :| 0 <= w < |prev| && prev[w].fromTx == d[p].tx && prev[w].toTx == d[q].tx;
            assert edges[w] == prev[w];
          }
          forall q | i < q < j && Conflicts(d[i], d[q])
            ensures HasConflictPairEdge(edges, d[i].tx, d[q].tx)
          {
            var w :| 0 <= w < |prev| && prev[w].fromTx == d[i].tx && prev[w].toTx == d[q].tx;
            assert edges[w] == prev[w];
          }
        }
        j := j + 1;
      }
      i := i + 1;
    }

    g := PrecedenceGraph(nodes, edges);
  }

  // ---------------------------------------------------------------------------
  // Topological Order & Acyclicity Verification
  // ---------------------------------------------------------------------------

  function TxPosition(order: seq<TxId>, tx: TxId): int
    ensures TxPosition(order, tx) >= -1
    ensures TxPosition(order, tx) >= 0 ==>
      TxPosition(order, tx) < |order| && order[TxPosition(order, tx)] == tx
    decreases |order|
  {
    if |order| == 0 then -1
    else if order[0] == tx then 0
    else
      var sub := TxPosition(order[1..], tx);
      if sub == -1 then -1 else 1 + sub
  }

  predicate RespectsTopologicalOrder(g: PrecedenceGraph, order: seq<TxId>)
  {
    forall k :: 0 <= k < |g.edges| ==>
      0 <= TxPosition(order, g.edges[k].fromTx) < TxPosition(order, g.edges[k].toTx)
  }

  // Soundness Lemma: If `g` respects a topological transaction order `order`,
  // then `g` cannot contain a 2-cycle between any two transactions.
  lemma LemmaTopologicalOrderImpliesNo2Cycle(
    g: PrecedenceGraph,
    order: seq<TxId>,
    k1: nat,
    k2: nat
  )
    requires RespectsTopologicalOrder(g, order)
    requires k1 < |g.edges| && k2 < |g.edges|
    ensures !(g.edges[k1].fromTx == g.edges[k2].toTx &&
              g.edges[k1].toTx == g.edges[k2].fromTx)
  {
    assert TxPosition(order, g.edges[k1].fromTx) < TxPosition(order, g.edges[k1].toTx);
    assert TxPosition(order, g.edges[k2].fromTx) < TxPosition(order, g.edges[k2].toTx);
  }
}
