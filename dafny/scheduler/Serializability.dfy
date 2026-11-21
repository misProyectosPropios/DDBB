// Conflict-Serializability module:
// Determines whether a schedule `s1` is conflict-serializable to a target
// serial schedule `targetSerial`, with formal proofs of reflexivity and
// conflict-cycle impossibility.

include "Types.dfy"
include "LockPolicy.dfy"

module Serializability {
  import opened SchedulerTypes
  import opened LockPolicies

  // Only Read and Write operations participate in data conflicts.
  predicate IsDataOp(op: SchedOp)
  {
    op.ReadOp? || op.WriteOp?
  }

  // Projects a schedule to its sequence of Read/Write operations.
  function DataOps(ops: seq<SchedOp>): seq<SchedOp>
    ensures forall i :: 0 <= i < |DataOps(ops)| ==> IsDataOp(DataOps(ops)[i])
    decreases |ops|
  {
    if |ops| == 0 then []
    else if IsDataOp(ops[0]) then [ops[0]] + DataOps(ops[1..])
    else DataOps(ops[1..])
  }

  // Two data operations conflict iff they belong to different transactions,
  // access the same database element, and at least one of them is a Write.
  predicate Conflicts(a: SchedOp, b: SchedOp)
    requires IsDataOp(a) && IsDataOp(b)
  {
    a.tx != b.tx &&
    a.element == b.element &&
    (a.WriteOp? || b.WriteOp?)
  }

  // A schedule is serial iff every transaction's operations appear in a single
  // contiguous block (no interleaving between transactions).
  predicate IsSerial(dataOps: seq<SchedOp>)
  {
    forall i, j, k ::
      (0 <= i < j < k < |dataOps| &&
       dataOps[i].tx == dataOps[k].tx) ==> dataOps[j].tx == dataOps[i].tx
  }

  function TxSet(dataOps: seq<SchedOp>): set<TxId>
  {
    set i | 0 <= i < |dataOps| :: dataOps[i].tx
  }

  function TxDataOps(dataOps: seq<SchedOp>, tx: TxId): seq<SchedOp>
    decreases |dataOps|
  {
    if |dataOps| == 0 then []
    else if dataOps[0].tx == tx then [dataOps[0]] + TxDataOps(dataOps[1..], tx)
    else TxDataOps(dataOps[1..], tx)
  }

  // Two data-operation sequences contain the exact same transactions and each
  // transaction performs the exact same sequence of reads and writes.
  predicate SameTxDataOps(d1: seq<SchedOp>, d2: seq<SchedOp>)
  {
    TxSet(d1) == TxSet(d2) &&
    forall tx :: tx in TxSet(d1) ==> TxDataOps(d1, tx) == TxDataOps(d2, tx)
  }

  lemma LemmaTxInTail(dataOps: seq<SchedOp>, tx: TxId)
    requires |dataOps| > 0 && dataOps[0].tx != tx && tx in TxSet(dataOps)
    ensures tx in TxSet(dataOps[1..])
  {
    var i :| 0 <= i < |dataOps| && dataOps[i].tx == tx;
    assert i > 0 && dataOps[1..][i - 1].tx == tx;
  }

  // Index of the first operation belonging to `tx` in `dataOps`.
  function FirstTxIndex(dataOps: seq<SchedOp>, tx: TxId): nat
    requires tx in TxSet(dataOps)
    ensures FirstTxIndex(dataOps, tx) < |dataOps|
    ensures dataOps[FirstTxIndex(dataOps, tx)].tx == tx
    ensures forall k :: 0 <= k < FirstTxIndex(dataOps, tx) ==> dataOps[k].tx != tx
    decreases |dataOps|
  {
    if dataOps[0].tx == tx then 0
    else
      LemmaTxInTail(dataOps, tx);
      1 + FirstTxIndex(dataOps[1..], tx)
  }

  // Every conflicting pair (d1[i] before d1[j]) in `d1` orders transaction
  // `d1[i].tx` strictly before transaction `d1[j].tx` in the serial schedule `d2`.
  predicate ConflictOrderPreserved(d1: seq<SchedOp>, d2: seq<SchedOp>)
    requires forall i :: 0 <= i < |d1| ==> IsDataOp(d1[i])
    requires TxSet(d1) == TxSet(d2)
  {
    forall i, j :: 0 <= i < j < |d1| && Conflicts(d1[i], d1[j]) ==>
      FirstTxIndex(d2, d1[i].tx) < FirstTxIndex(d2, d1[j].tx)
  }

  // Main predicate: `s1` is conflict-serializable to `targetSerial` iff
  // `targetSerial` is serial, both perform the exact same per-transaction
  // reads/writes, and every conflict in `s1` respects the transaction order
  // in `targetSerial`.
  // Marked {:opaque} so callers with concrete schedules evaluate it at runtime
  // without causing cubic quantifier blowup in Z3.
  opaque predicate IsConflictSerializableTo(s1: seq<SchedOp>, targetSerial: seq<SchedOp>)
  {
    var d1 := DataOps(s1);
    var d2 := DataOps(targetSerial);
    IsSerial(d2) &&
    SameTxDataOps(d1, d2) &&
    ConflictOrderPreserved(d1, d2)
  }

  // ---------------------------------------------------------------------------
  // Formal properties of conflict-serializability
  // ---------------------------------------------------------------------------

  // In a serial schedule, if t1 starts before t2, then EVERY operation of t1
  // appears strictly before EVERY operation of t2.
  lemma LemmaSerialOrderConsistent(d: seq<SchedOp>, t1: TxId, t2: TxId)
    requires IsSerial(d)
    requires t1 in TxSet(d) && t2 in TxSet(d)
    requires FirstTxIndex(d, t1) < FirstTxIndex(d, t2)
    ensures forall a, b :: 0 <= a < |d| && 0 <= b < |d| && d[a].tx == t1 && d[b].tx == t2 ==> a < b
  {
    var p1 := FirstTxIndex(d, t1);
    var p2 := FirstTxIndex(d, t2);
    forall a, b | 0 <= a < |d| && 0 <= b < |d| && d[a].tx == t1 && d[b].tx == t2
      ensures a < b
    {
      assert p2 <= b;
      if b <= a {
        assert t1 != t2;
        assert p1 < b < a;
        assert d[p1].tx == d[a].tx;
        assert d[b].tx == t1;
      }
    }
  }

  // Reflexivity: every serial schedule is conflict-serializable to itself.
  lemma LemmaSerialSelfSerializable(s: seq<SchedOp>)
    requires IsSerial(DataOps(s))
    ensures IsConflictSerializableTo(s, s)
  {
    reveal IsConflictSerializableTo();
    var d := DataOps(s);
    forall i, j | 0 <= i < j < |d| && Conflicts(d[i], d[j])
      ensures FirstTxIndex(d, d[i].tx) < FirstTxIndex(d, d[j].tx)
    {
      var pi := FirstTxIndex(d, d[i].tx);
      var pj := FirstTxIndex(d, d[j].tx);
      assert pi <= i;
      if pj <= pi {
        assert d[i].tx != d[j].tx;
        assert pj < i < j;
        assert d[pj].tx == d[j].tx;
        assert d[i].tx == d[j].tx;
      }
    }
  }

  // Soundness: if `s1` is conflict-serializable to `targetSerial`, then `s1`
  // cannot contain a 2-cycle of conflicts between any two transactions.
  lemma LemmaSerializableImpliesNoConflictCycle(
    s1: seq<SchedOp>,
    targetSerial: seq<SchedOp>,
    i1: int, j1: int,
    i2: int, j2: int
  )
    requires IsConflictSerializableTo(s1, targetSerial)
    requires var d1 := DataOps(s1);
      0 <= i1 < j1 < |d1| && Conflicts(d1[i1], d1[j1]) &&
      0 <= i2 < j2 < |d1| && Conflicts(d1[i2], d1[j2])
    ensures var d1 := DataOps(s1);
      !(d1[i1].tx == d1[j2].tx && d1[j1].tx == d1[i2].tx)
  {
    reveal IsConflictSerializableTo();
    var d1 := DataOps(s1);
    var d2 := DataOps(targetSerial);
    assert FirstTxIndex(d2, d1[i1].tx) < FirstTxIndex(d2, d1[j1].tx);
    assert FirstTxIndex(d2, d1[i2].tx) < FirstTxIndex(d2, d1[j2].tx);
  }
}
