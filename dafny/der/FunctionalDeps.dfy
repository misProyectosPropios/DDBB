// Functional Dependencies (FDs), Attribute Closure (X+), Superkeys, Candidate
// Keys, Prime Attributes, Canonical / Minimal Cover, and FD Projection.
//
// All algorithms are 100% pure, compilable (deterministic over `seq<Name>`),
// and formally verified in Dafny 4.

include "Types.dfy"

module FunctionalDeps {
  import opened DerTypes

  // Functional Dependency: lhs -> rhs
  datatype FD = FD(
    lhs: set<Name>,
    rhs: set<Name>
  )

  // ---------------------------------------------------------------------------
  // Sequence / Set helpers
  // ---------------------------------------------------------------------------

  function SeqToSet<T>(s: seq<T>): set<T>
  {
    set x | x in s
  }

  lemma LemmaSeqToSetMembership<T>(s: seq<T>, x: T)
    ensures x in SeqToSet(s) <==> x in s
  {
  }

  predicate UniqueNames(s: seq<Name>)
  {
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
  }

  function FilterInSet(s: seq<Name>, keep: set<Name>): seq<Name>
    ensures forall x :: x in FilterInSet(s, keep) <==> (x in s && x in keep)
    ensures UniqueNames(s) ==> UniqueNames(FilterInSet(s, keep))
    decreases |s|
  {
    if |s| == 0 then []
    else if s[0] in keep then [s[0]] + FilterInSet(s[1..], keep)
    else FilterInSet(s[1..], keep)
  }

  lemma LemmaFilterInSetSeqToSet(s: seq<Name>, keep: set<Name>)
    ensures SeqToSet(FilterInSet(s, keep)) == SeqToSet(s) * keep
    decreases |s|
  {
    if |s| > 0 {
      LemmaFilterInSetSeqToSet(s[1..], keep);
    }
  }

  function DeduplicateNames(s: seq<Name>): seq<Name>
    ensures UniqueNames(DeduplicateNames(s))
    ensures SeqToSet(DeduplicateNames(s)) == SeqToSet(s)
    decreases |s|
  {
    if |s| == 0 then []
    else
      var rest := DeduplicateNames(s[1..]);
      assert SeqToSet(s) == {s[0]} + SeqToSet(s[1..]) by {
        assert s == [s[0]] + s[1..];
      }
      if s[0] in rest then
        assert s[0] in SeqToSet(rest);
        rest
      else
        assert SeqToSet([s[0]] + rest) == {s[0]} + SeqToSet(rest);
        [s[0]] + rest
  }

  // ---------------------------------------------------------------------------
  // Functional Dependency validity & basics
  // ---------------------------------------------------------------------------

  predicate ValidFD(fd: FD, universe: set<Name>)
  {
    fd.lhs != {} &&
    fd.rhs != {} &&
    fd.lhs <= universe &&
    fd.rhs <= universe
  }

  predicate ValidFDs(fds: seq<FD>, universe: set<Name>)
  {
    forall i :: 0 <= i < |fds| ==> ValidFD(fds[i], universe)
  }

  predicate IsTrivialFD(fd: FD)
  {
    fd.rhs <= fd.lhs
  }

  function AllLhsAttrs(fds: seq<FD>): set<Name>
    decreases |fds|
  {
    if |fds| == 0 then {}
    else fds[0].lhs + AllLhsAttrs(fds[1..])
  }

  lemma LemmaLhsSubsetAllLhs(fds: seq<FD>, i: nat)
    requires i < |fds|
    ensures fds[i].lhs <= AllLhsAttrs(fds)
    decreases |fds|
  {
    if i > 0 {
      LemmaLhsSubsetAllLhs(fds[1..], i - 1);
    }
  }

  function AllNonTrivialRhsAttrs(fds: seq<FD>): set<Name>
    decreases |fds|
  {
    if |fds| == 0 then {}
    else (fds[0].rhs - fds[0].lhs) + AllNonTrivialRhsAttrs(fds[1..])
  }

  lemma LemmaNonTrivialRhsMember(fds: seq<FD>, i: nat)
    requires i < |fds|
    ensures (fds[i].rhs - fds[i].lhs) <= AllNonTrivialRhsAttrs(fds)
    decreases |fds|
  {
    if i > 0 {
      LemmaNonTrivialRhsMember(fds[1..], i - 1);
    }
  }

  // ---------------------------------------------------------------------------
  // Attribute Closure (X+ under FDs within `universe`)
  // ---------------------------------------------------------------------------

  function ClosureStep(acc: set<Name>, fds: seq<FD>, universe: set<Name>): set<Name>
    ensures acc <= ClosureStep(acc, fds, universe)
    ensures acc <= universe ==> ClosureStep(acc, fds, universe) <= universe
    decreases |fds|
  {
    if |fds| == 0 then acc
    else
      var next :=
        if fds[0].lhs <= acc then acc + (fds[0].rhs * universe)
        else acc;
      ClosureStep(next, fds[1..], universe)
  }

  lemma LemmaClosureStepFiresFD(acc: set<Name>, fds: seq<FD>, universe: set<Name>, idx: nat)
    requires idx < |fds|
    requires fds[idx].lhs <= acc
    ensures (fds[idx].rhs * universe) <= ClosureStep(acc, fds, universe)
    decreases |fds|
  {
    if idx == 0 {
      // fds[0] fires immediately and ClosureStep is monotone in acc.
    } else {
      var next :=
        if fds[0].lhs <= acc then acc + (fds[0].rhs * universe)
        else acc;
      assert fds[idx].lhs <= next;
      LemmaClosureStepFiresFD(next, fds[1..], universe, idx - 1);
    }
  }

  lemma LemmaClosureStepMonotone(a: set<Name>, b: set<Name>, fds: seq<FD>, universe: set<Name>)
    requires a <= b
    ensures ClosureStep(a, fds, universe) <= ClosureStep(b, fds, universe)
    decreases |fds|
  {
    if |fds| > 0 {
      var nextA := if fds[0].lhs <= a then a + (fds[0].rhs * universe) else a;
      var nextB := if fds[0].lhs <= b then b + (fds[0].rhs * universe) else b;
      assert nextA <= nextB;
      LemmaClosureStepMonotone(nextA, nextB, fds[1..], universe);
    }
  }

  lemma LemmaClosureStepPreservesFixed(acc: set<Name>, fds: seq<FD>, universe: set<Name>)
    requires forall i :: 0 <= i < |fds| && fds[i].lhs <= acc ==> (fds[i].rhs * universe) <= acc
    ensures ClosureStep(acc, fds, universe) == acc
    decreases |fds|
  {
    if |fds| > 0 {
      var next := if fds[0].lhs <= acc then acc + (fds[0].rhs * universe) else acc;
      assert next == acc;
      forall i | 0 <= i < |fds[1..]| && fds[1..][i].lhs <= acc
        ensures (fds[1..][i].rhs * universe) <= acc
      {
        assert fds[1..][i] == fds[i + 1];
      }
      LemmaClosureStepPreservesFixed(acc, fds[1..], universe);
    }
  }

  function ClosureLoop(acc: set<Name>, fds: seq<FD>, universe: set<Name>): set<Name>
    requires acc <= universe
    ensures acc <= ClosureLoop(acc, fds, universe) <= universe
    ensures forall i :: 0 <= i < |fds| && fds[i].lhs <= ClosureLoop(acc, fds, universe) ==>
      (fds[i].rhs * universe) <= ClosureLoop(acc, fds, universe)
    decreases universe - acc
  {
    var next := ClosureStep(acc, fds, universe);
    if next == acc then
      assert forall i :: 0 <= i < |fds| && fds[i].lhs <= acc ==> (fds[i].rhs * universe) <= acc by {
        forall i | 0 <= i < |fds| && fds[i].lhs <= acc
          ensures (fds[i].rhs * universe) <= acc
        {
          LemmaClosureStepFiresFD(acc, fds, universe, i);
        }
      }
      acc
    else
      assert acc < next && next <= universe;
      assert (universe - next) < (universe - acc);
      ClosureLoop(next, fds, universe)
  }

  function AttributeClosure(x: set<Name>, fds: seq<FD>, universe: set<Name>): set<Name>
    ensures (x * universe) <= AttributeClosure(x, fds, universe) <= universe
    ensures x <= universe ==> x <= AttributeClosure(x, fds, universe)
    ensures forall i :: 0 <= i < |fds| && fds[i].lhs <= AttributeClosure(x, fds, universe) ==>
      (fds[i].rhs * universe) <= AttributeClosure(x, fds, universe)
  {
    ClosureLoop(x * universe, fds, universe)
  }

  // If `sup <= universe` already contains `acc` and is closed under `fds`, then
  // `ClosureLoop(acc, fds, universe) <= sup`.
  lemma LemmaClosureLoopMinimal(
    acc: set<Name>,
    sup: set<Name>,
    fds: seq<FD>,
    universe: set<Name>
  )
    requires acc <= sup <= universe
    requires forall i :: 0 <= i < |fds| && fds[i].lhs <= sup ==> (fds[i].rhs * universe) <= sup
    ensures ClosureLoop(acc, fds, universe) <= sup
    decreases universe - acc
  {
    var next := ClosureStep(acc, fds, universe);
    LemmaClosureStepMonotone(acc, sup, fds, universe);
    LemmaClosureStepPreservesFixed(sup, fds, universe);
    assert next <= sup;
    if next != acc {
      assert (universe - next) < (universe - acc);
      LemmaClosureLoopMinimal(next, sup, fds, universe);
    }
  }

  lemma LemmaClosureMonotone(
    x: set<Name>,
    y: set<Name>,
    fds: seq<FD>,
    universe: set<Name>
  )
    requires x <= y
    ensures AttributeClosure(x, fds, universe) <= AttributeClosure(y, fds, universe)
  {
    var clY := AttributeClosure(y, fds, universe);
    assert (x * universe) <= (y * universe) <= clY;
    LemmaClosureLoopMinimal(x * universe, clY, fds, universe);
  }

  lemma LemmaClosureIdempotent(x: set<Name>, fds: seq<FD>, universe: set<Name>)
    ensures AttributeClosure(AttributeClosure(x, fds, universe), fds, universe) ==
            AttributeClosure(x, fds, universe)
  {
    var cl := AttributeClosure(x, fds, universe);
    LemmaClosureLoopMinimal(cl, cl, fds, universe);
  }

  // ---------------------------------------------------------------------------
  // FD Implication & Equivalence
  // ---------------------------------------------------------------------------

  predicate ImpliesFD(fds: seq<FD>, fd: FD, universe: set<Name>)
  {
    fd.rhs <= AttributeClosure(fd.lhs, fds, universe)
  }

  predicate ImpliesAllFDs(fds1: seq<FD>, fds2: seq<FD>, universe: set<Name>)
  {
    forall i :: 0 <= i < |fds2| ==> ImpliesFD(fds1, fds2[i], universe)
  }

  predicate EquivalentFDs(fds1: seq<FD>, fds2: seq<FD>, universe: set<Name>)
  {
    ImpliesAllFDs(fds1, fds2, universe) &&
    ImpliesAllFDs(fds2, fds1, universe)
  }

  // If `fds1` implies every FD in `fds2`, then `AttributeClosure(x, fds2) <= AttributeClosure(x, fds1)`.
  lemma LemmaImpliesAllSubsetClosure(
    x: set<Name>,
    fds1: seq<FD>,
    fds2: seq<FD>,
    universe: set<Name>
  )
    requires ValidFDs(fds2, universe)
    requires ImpliesAllFDs(fds1, fds2, universe)
    ensures AttributeClosure(x, fds2, universe) <= AttributeClosure(x, fds1, universe)
  {
    var cl1 := AttributeClosure(x, fds1, universe);
    forall i | 0 <= i < |fds2| && fds2[i].lhs <= cl1
      ensures (fds2[i].rhs * universe) <= cl1
    {
      assert ImpliesFD(fds1, fds2[i], universe);
      LemmaClosureMonotone(fds2[i].lhs, cl1, fds1, universe);
      LemmaClosureIdempotent(x, fds1, universe);
      assert fds2[i].rhs <= AttributeClosure(fds2[i].lhs, fds1, universe) <= cl1;
    }
    LemmaClosureLoopMinimal(x * universe, cl1, fds2, universe);
  }

  lemma LemmaEquivalentSameClosure(
    x: set<Name>,
    fds1: seq<FD>,
    fds2: seq<FD>,
    universe: set<Name>
  )
    requires ValidFDs(fds1, universe) && ValidFDs(fds2, universe)
    requires EquivalentFDs(fds1, fds2, universe)
    ensures AttributeClosure(x, fds1, universe) == AttributeClosure(x, fds2, universe)
  {
    LemmaImpliesAllSubsetClosure(x, fds1, fds2, universe);
    LemmaImpliesAllSubsetClosure(x, fds2, fds1, universe);
  }

  // ---------------------------------------------------------------------------
  // Superkeys, Candidate Keys & Prime Attributes
  // ---------------------------------------------------------------------------

  predicate IsSuperkey(k: set<Name>, attrs: set<Name>, fds: seq<FD>)
  {
    k <= attrs && attrs <= AttributeClosure(k, fds, attrs)
  }

  predicate IsCandidateKey(k: set<Name>, attrs: set<Name>, fds: seq<FD>)
  {
    IsSuperkey(k, attrs, fds) &&
    (forall a :: a in k ==> !IsSuperkey(k - {a}, attrs, fds))
  }

  // Executable minimality test using an ordered attribute list `attrsSeq`.
  predicate IsCandidateKeyExec(k: set<Name>, attrsSeq: seq<Name>, fds: seq<FD>)
  {
    var attrs := SeqToSet(attrsSeq);
    IsSuperkey(k, attrs, fds) &&
    (forall i :: 0 <= i < |attrsSeq| && attrsSeq[i] in k ==>
      !IsSuperkey(k - {attrsSeq[i]}, attrs, fds))
  }

  lemma LemmaCandidateKeyExecEquiv(k: set<Name>, attrsSeq: seq<Name>, fds: seq<FD>)
    ensures IsCandidateKeyExec(k, attrsSeq, fds) <==> IsCandidateKey(k, SeqToSet(attrsSeq), fds)
  {
    var attrs := SeqToSet(attrsSeq);
    if IsCandidateKeyExec(k, attrsSeq, fds) {
      forall a | a in k
        ensures !IsSuperkey(k - {a}, attrs, fds)
      {
        assert a in attrs;
        LemmaSeqToSetMembership(attrsSeq, a);
        var idx :| 0 <= idx < |attrsSeq| && attrsSeq[idx] == a;
        assert attrsSeq[idx] in k;
      }
    }
    if IsCandidateKey(k, attrs, fds) {
      forall i | 0 <= i < |attrsSeq| && attrsSeq[i] in k
        ensures !IsSuperkey(k - {attrsSeq[i]}, attrs, fds)
      {
      }
    }
  }

  // Core attributes never appear on any non-trivial RHS, so they MUST belong to
  // every superkey (and every candidate key).
  function CoreAttrs(attrs: set<Name>, fds: seq<FD>): set<Name>
  {
    attrs - AllNonTrivialRhsAttrs(fds)
  }

  lemma LemmaCoreInEverySuperkey(k: set<Name>, attrs: set<Name>, fds: seq<FD>)
    requires IsSuperkey(k, attrs, fds)
    ensures CoreAttrs(attrs, fds) <= k
  {
    forall a | a in CoreAttrs(attrs, fds)
      ensures a in k
    {
      if a !in k {
        var sup := attrs - {a};
        assert k <= sup;
        forall i | 0 <= i < |fds| && fds[i].lhs <= sup
          ensures (fds[i].rhs * attrs) <= sup
        {
          LemmaNonTrivialRhsMember(fds, i);
          assert a !in (fds[i].rhs - fds[i].lhs);
          assert a !in fds[i].lhs;
          assert a !in fds[i].rhs;
        }
        LemmaClosureLoopMinimal(k * attrs, sup, fds, attrs);
        assert AttributeClosure(k, fds, attrs) <= sup;
        assert a !in AttributeClosure(k, fds, attrs);
        assert false;
      }
    }
  }

  // Dead attributes (non-core attributes that never appear on any LHS) can
  // NEVER belong to any candidate key.
  lemma LemmaNoDeadAttrInCandidateKey(k: set<Name>, attrs: set<Name>, fds: seq<FD>, a: Name)
    requires ValidFDs(fds, attrs)
    requires IsCandidateKey(k, attrs, fds)
    requires a in k
    requires a !in CoreAttrs(attrs, fds)
    ensures a in AllLhsAttrs(fds)
  {
    if a !in AllLhsAttrs(fds) {
      var cl0 := AttributeClosure(k - {a}, fds, attrs);
      var sup := cl0 + {a};
      assert k <= sup <= attrs;
      forall i | 0 <= i < |fds| && fds[i].lhs <= sup
        ensures (fds[i].rhs * attrs) <= sup
      {
        LemmaLhsSubsetAllLhs(fds, i);
        assert a !in fds[i].lhs;
        assert fds[i].lhs <= cl0;
        assert (fds[i].rhs * attrs) <= cl0 <= sup;
      }
      LemmaClosureLoopMinimal(k * attrs, sup, fds, attrs);
      assert attrs <= AttributeClosure(k, fds, attrs) <= cl0 + {a};
      assert (attrs - {a}) <= cl0;
      // Since a !in CoreAttrs(attrs, fds), some FD has a in rhs - lhs.
      assert a in AllNonTrivialRhsAttrs(fds);
      var idx := FindNonTrivialRhsWitness(fds, a);
      LemmaLhsSubsetAllLhs(fds, idx);
      assert a !in fds[idx].lhs;
      assert fds[idx].lhs <= attrs - {a} <= cl0;
      assert (fds[idx].rhs * attrs) <= cl0;
      assert a in cl0;
      assert attrs <= cl0;
      assert IsSuperkey(k - {a}, attrs, fds);
      assert false;
    }
  }

  lemma FindNonTrivialRhsWitness(fds: seq<FD>, a: Name) returns (idx: nat)
    requires a in AllNonTrivialRhsAttrs(fds)
    ensures idx < |fds| && a in (fds[idx].rhs - fds[idx].lhs)
    decreases |fds|
  {
    if a in (fds[0].rhs - fds[0].lhs) {
      idx := 0;
    } else {
      var sub := FindNonTrivialRhsWitness(fds[1..], a);
      idx := sub + 1;
    }
  }

  // Enumerates all subsets of `s` (deterministically).
  function AllSubsets(s: seq<Name>): seq<set<Name>>
    decreases |s|
  {
    if |s| == 0 then [{}]
    else
      var rest := AllSubsets(s[1..]);
      rest + AddElemToAll(s[0], rest)
  }

  function AddElemToAll(x: Name, sets: seq<set<Name>>): seq<set<Name>>
    ensures |AddElemToAll(x, sets)| == |sets|
    ensures forall i :: 0 <= i < |sets| ==> AddElemToAll(x, sets)[i] == sets[i] + {x}
    decreases |sets|
  {
    if |sets| == 0 then []
    else [sets[0] + {x}] + AddElemToAll(x, sets[1..])
  }

  lemma LemmaAllSubsetsComplete(s: seq<Name>, sub: set<Name>)
    ensures sub in AllSubsets(s) <==> sub <= SeqToSet(s)
    decreases |s|
  {
    if |s| == 0 {
      assert SeqToSet(s) == {};
      assert AllSubsets(s) == [{}];
    } else {
      var rest := AllSubsets(s[1..]);
      var withHead := AddElemToAll(s[0], rest);
      if sub <= SeqToSet(s) {
        if s[0] in sub {
          var without := sub - {s[0]};
          assert without <= SeqToSet(s[1..]);
          LemmaAllSubsetsComplete(s[1..], without);
          var idx :| 0 <= idx < |rest| && rest[idx] == without;
          assert withHead[idx] == without + {s[0]} == sub;
          assert sub in withHead;
        } else {
          assert sub <= SeqToSet(s[1..]);
          LemmaAllSubsetsComplete(s[1..], sub);
          assert sub in rest;
        }
      }
      if sub in AllSubsets(s) {
        if sub in rest {
          LemmaAllSubsetsComplete(s[1..], sub);
        } else {
          assert sub in withHead;
          var idx :| 0 <= idx < |withHead| && withHead[idx] == sub;
          LemmaAllSubsetsComplete(s[1..], rest[idx]);
          assert rest[idx] <= SeqToSet(s[1..]);
        }
      }
    }
  }

  // Exact, executable finder for ALL candidate keys of `(attrsSeq, fds)`.
  // Uses Core + Middle pruning so only attributes appearing on both LHS and RHS
  // are subset-enumerated, while formally proving 100% completeness!
  method FindCandidateKeys(attrsSeq: seq<Name>, fds: seq<FD>) returns (cks: seq<set<Name>>)
    requires |attrsSeq| > 0
    requires ValidFDs(fds, SeqToSet(attrsSeq))
    ensures |cks| > 0
    ensures forall i :: 0 <= i < |cks| ==> IsCandidateKey(cks[i], SeqToSet(attrsSeq), fds)
    ensures forall k :: IsCandidateKey(k, SeqToSet(attrsSeq), fds) ==> k in cks
  {
    var attrs := SeqToSet(attrsSeq);
    var core := CoreAttrs(attrs, fds);
    var middleSet := (attrs * AllLhsAttrs(fds)) - core;
    var middleSeq := FilterInSet(DeduplicateNames(attrsSeq), middleSet);
    LemmaFilterInSetSeqToSet(DeduplicateNames(attrsSeq), middleSet);
    assert SeqToSet(middleSeq) == middleSet;

    var subs := AllSubsets(middleSeq);
    cks := [];
    var i := 0;
    while i < |subs|
      invariant 0 <= i <= |subs|
      invariant forall j :: 0 <= j < |cks| ==> IsCandidateKey(cks[j], attrs, fds)
      invariant forall j :: 0 <= j < i && IsCandidateKey(core + subs[j], attrs, fds) ==>
        (core + subs[j]) in cks
      decreases |subs| - i
    {
      var cand := core + subs[i];
      LemmaCandidateKeyExecEquiv(cand, attrsSeq, fds);
      if IsCandidateKeyExec(cand, attrsSeq, fds) && cand !in cks {
        cks := cks + [cand];
      }
      i := i + 1;
    }

    // Completeness proof: every candidate key `k` satisfies `core <= k <= core + middleSet`.
    forall k | IsCandidateKey(k, attrs, fds)
      ensures k in cks
    {
      LemmaCoreInEverySuperkey(k, attrs, fds);
      var mid := k - core;
      forall a | a in mid
        ensures a in middleSet
      {
        LemmaNoDeadAttrInCandidateKey(k, attrs, fds, a);
      }
      assert mid <= SeqToSet(middleSeq);
      LemmaAllSubsetsComplete(middleSeq, mid);
      var idx :| 0 <= idx < |subs| && subs[idx] == mid;
      assert core + subs[idx] == k;
    }

    // Existence of at least one candidate key: shrink `attrs` to a minimal superkey.
    var oneKey := ShrinkToCandidateKey(attrs, attrsSeq, fds);
    assert oneKey in cks;
  }

  // Greedily drops redundant attributes from a superkey until it is minimal.
  method ShrinkToCandidateKey(
    start: set<Name>,
    attrsSeq: seq<Name>,
    fds: seq<FD>
  ) returns (ck: set<Name>)
    requires IsSuperkey(start, SeqToSet(attrsSeq), fds)
    ensures ck <= start
    ensures IsCandidateKey(ck, SeqToSet(attrsSeq), fds)
  {
    var attrs := SeqToSet(attrsSeq);
    ck := start;
    var i := 0;
    while i < |attrsSeq|
      invariant 0 <= i <= |attrsSeq|
      invariant ck <= start
      invariant IsSuperkey(ck, attrs, fds)
      invariant forall j :: 0 <= j < i && attrsSeq[j] in ck ==>
        !IsSuperkey(ck - {attrsSeq[j]}, attrs, fds)
      decreases |attrsSeq| - i
    {
      var a := attrsSeq[i];
      if a in ck && IsSuperkey(ck - {a}, attrs, fds) {
        var nextCk := ck - {a};
        forall j | 0 <= j < i && attrsSeq[j] in nextCk
          ensures !IsSuperkey(nextCk - {attrsSeq[j]}, attrs, fds)
        {
          if IsSuperkey(nextCk - {attrsSeq[j]}, attrs, fds) {
            LemmaClosureMonotone(nextCk - {attrsSeq[j]}, ck - {attrsSeq[j]}, fds, attrs);
            assert IsSuperkey(ck - {attrsSeq[j]}, attrs, fds);
            assert false;
          }
        }
        ck := nextCk;
      }
      i := i + 1;
    }
    LemmaCandidateKeyExecEquiv(ck, attrsSeq, fds);
  }

  predicate IsPrimeAttribute(a: Name, candidateKeys: seq<set<Name>>)
  {
    exists i :: 0 <= i < |candidateKeys| && a in candidateKeys[i]
  }

  // ---------------------------------------------------------------------------
  // Canonical / Minimal Cover (used by Bernstein's 3NF Synthesis)
  // ---------------------------------------------------------------------------

  // Step 1: Split every FD `X -> Y` into singleton non-trivial FDs `X -> {a}`.
  method SplitToSingletonRHS(fds: seq<FD>, attrsSeq: seq<Name>) returns (singles: seq<FD>)
    requires ValidFDs(fds, SeqToSet(attrsSeq))
    ensures ValidFDs(singles, SeqToSet(attrsSeq))
    ensures forall i :: 0 <= i < |singles| ==> |singles[i].rhs| == 1 && !IsTrivialFD(singles[i])
    ensures EquivalentFDs(fds, singles, SeqToSet(attrsSeq))
  {
    var universe := SeqToSet(attrsSeq);
    singles := [];
    var i := 0;
    while i < |fds|
      invariant 0 <= i <= |fds|
      invariant ValidFDs(singles, universe)
      invariant forall k :: 0 <= k < |singles| ==> |singles[k].rhs| == 1 && !IsTrivialFD(singles[k])
      invariant ImpliesAllFDs(fds, singles, universe)
      invariant ImpliesAllFDs(singles, fds[..i], universe)
      decreases |fds| - i
    {
      var fd := fds[i];
      var j := 0;
      while j < |attrsSeq|
        invariant 0 <= j <= |attrsSeq|
        invariant ValidFDs(singles, universe)
        invariant forall k :: 0 <= k < |singles| ==> |singles[k].rhs| == 1 && !IsTrivialFD(singles[k])
        invariant ImpliesAllFDs(fds, singles, universe)
        invariant ImpliesAllFDs(singles, fds[..i], universe)
        invariant forall p :: 0 <= p < j && attrsSeq[p] in fd.rhs ==>
          attrsSeq[p] in AttributeClosure(fd.lhs, singles, universe)
        decreases |attrsSeq| - j
      {
        var a := attrsSeq[j];
        if a in fd.rhs && a !in fd.lhs {
          var sfd := FD(fd.lhs, {a});
          assert ValidFD(sfd, universe);
          // Prove fds implies sfd:
          assert fd.lhs <= AttributeClosure(fd.lhs, fds, universe);
          assert (fd.rhs * universe) <= AttributeClosure(fd.lhs, fds, universe);
          assert ImpliesFD(fds, sfd, universe);

          var prev := singles;
          singles := singles + [sfd];

          // Adding an FD preserves all existing implications from `prev`:
          forall k | 0 <= k < |prev|
            ensures ImpliesFD(singles, prev[k], universe)
          {
            assert prev[k] == singles[k];
          }
          forall k | 0 <= k < i
            ensures ImpliesFD(singles, fds[k], universe)
          {
            LemmaImpliesAllSubsetClosure(fds[k].lhs, singles, prev, universe);
          }
          forall p | 0 <= p < j && attrsSeq[p] in fd.rhs
            ensures attrsSeq[p] in AttributeClosure(fd.lhs, singles, universe)
          {
            LemmaImpliesAllSubsetClosure(fd.lhs, singles, prev, universe);
          }
          // And sfd itself fires from fd.lhs:
          assert singles[|prev|] == sfd;
          assert sfd.lhs <= AttributeClosure(fd.lhs, singles, universe);
          assert (sfd.rhs * universe) <= AttributeClosure(fd.lhs, singles, universe);
          assert a in AttributeClosure(fd.lhs, singles, universe);
        }
        j := j + 1;
      }

      // Now every `a in fd.rhs` is in `AttributeClosure(fd.lhs, singles, universe)`:
      forall a | a in fd.rhs
        ensures a in AttributeClosure(fd.lhs, singles, universe)
      {
        assert a in universe;
        LemmaSeqToSetMembership(attrsSeq, a);
        var p :| 0 <= p < |attrsSeq| && attrsSeq[p] == a;
        assert attrsSeq[p] in fd.rhs;
      }
      assert ImpliesFD(singles, fd, universe);
      assert fds[..i + 1] == fds[..i] + [fd];
      i := i + 1;
    }
    assert fds[..|fds|] == fds;
  }

  // Step 2: Reduce extraneous LHS attributes on each singleton FD.
  method ReduceLHS(fds: seq<FD>, attrsSeq: seq<Name>) returns (reduced: seq<FD>)
    requires ValidFDs(fds, SeqToSet(attrsSeq))
    requires forall i :: 0 <= i < |fds| ==> |fds[i].rhs| == 1 && !IsTrivialFD(fds[i])
    ensures ValidFDs(reduced, SeqToSet(attrsSeq))
    ensures forall i :: 0 <= i < |reduced| ==> |reduced[i].rhs| == 1 && !IsTrivialFD(reduced[i])
    ensures EquivalentFDs(fds, reduced, SeqToSet(attrsSeq))
  {
    var universe := SeqToSet(attrsSeq);
    reduced := fds;
    var i := 0;
    while i < |reduced|
      invariant 0 <= i <= |reduced|
      invariant ValidFDs(reduced, universe)
      invariant forall k :: 0 <= k < |reduced| ==> |reduced[k].rhs| == 1 && !IsTrivialFD(reduced[k])
      invariant EquivalentFDs(fds, reduced, universe)
      decreases |reduced| - i
    {
      var j := 0;
      while j < |attrsSeq|
        invariant 0 <= j <= |attrsSeq|
        invariant i < |reduced|
        invariant ValidFDs(reduced, universe)
        invariant forall k :: 0 <= k < |reduced| ==> |reduced[k].rhs| == 1 && !IsTrivialFD(reduced[k])
        invariant EquivalentFDs(fds, reduced, universe)
        decreases |attrsSeq| - j
      {
        var cur := reduced[i];
        var b := attrsSeq[j];
        if b in cur.lhs && |cur.lhs| > 1 {
          var candLhs := cur.lhs - {b};
          if cur.rhs <= AttributeClosure(candLhs, reduced, universe) {
            var newFd := FD(candLhs, cur.rhs);
            var prev := reduced;
            reduced := reduced[i := newFd];

            // Prove `EquivalentFDs(prev, reduced, universe)`:
            // 1) `prev` implies `reduced`:
            forall k | 0 <= k < |reduced|
              ensures ImpliesFD(prev, reduced[k], universe)
            {
              if k == i {
                assert ImpliesFD(prev, newFd, universe);
              } else {
                assert reduced[k] == prev[k];
              }
            }
            // 2) `reduced` implies `prev` (since `candLhs <= cur.lhs`):
            forall k | 0 <= k < |prev|
              ensures ImpliesFD(reduced, prev[k], universe)
            {
              if k == i {
                assert newFd.lhs <= cur.lhs;
                LemmaClosureMonotone(newFd.lhs, cur.lhs, reduced, universe);
                assert newFd.rhs <= AttributeClosure(newFd.lhs, reduced, universe);
              } else {
                assert prev[k] == reduced[k];
              }
            }
            // Transitivity of equivalence: `fds` <-> `prev` <-> `reduced`:
            forall k | 0 <= k < |reduced|
              ensures ImpliesFD(fds, reduced[k], universe)
            {
              LemmaEquivalentSameClosure(reduced[k].lhs, fds, prev, universe);
            }
            forall k | 0 <= k < |fds|
              ensures ImpliesFD(reduced, fds[k], universe)
            {
              LemmaEquivalentSameClosure(fds[k].lhs, prev, reduced, universe);
            }
          }
        }
        j := j + 1;
      }
      i := i + 1;
    }
  }

  // Step 3: Remove redundant FDs implied by the remaining FDs.
  method RemoveRedundantFDs(fds: seq<FD>, attrsSeq: seq<Name>) returns (clean: seq<FD>)
    requires ValidFDs(fds, SeqToSet(attrsSeq))
    requires forall i :: 0 <= i < |fds| ==> |fds[i].rhs| == 1 && !IsTrivialFD(fds[i])
    ensures ValidFDs(clean, SeqToSet(attrsSeq))
    ensures forall i :: 0 <= i < |clean| ==> |clean[i].rhs| == 1 && !IsTrivialFD(clean[i])
    ensures EquivalentFDs(fds, clean, SeqToSet(attrsSeq))
  {
    var universe := SeqToSet(attrsSeq);
    clean := fds;
    var i := 0;
    while i < |clean|
      invariant 0 <= i <= |clean|
      invariant ValidFDs(clean, universe)
      invariant forall k :: 0 <= k < |clean| ==> |clean[k].rhs| == 1 && !IsTrivialFD(clean[k])
      invariant EquivalentFDs(fds, clean, universe)
      decreases |clean| - i
    {
      var withoutI := clean[..i] + clean[i + 1..];
      if ImpliesFD(withoutI, clean[i], universe) {
        var prev := clean;
        // Prove `EquivalentFDs(prev, withoutI, universe)`:
        forall k | 0 <= k < |withoutI|
          ensures ImpliesFD(prev, withoutI[k], universe)
        {
          if k < i {
            assert withoutI[k] == prev[k];
          } else {
            assert withoutI[k] == prev[k + 1];
          }
        }
        forall k | 0 <= k < |prev|
          ensures ImpliesFD(withoutI, prev[k], universe)
        {
          if k < i {
            assert prev[k] == withoutI[k];
          } else if k == i {
            assert ImpliesFD(withoutI, prev[i], universe);
          } else {
            assert prev[k] == withoutI[k - 1];
          }
        }
        forall k | 0 <= k < |withoutI|
          ensures ImpliesFD(fds, withoutI[k], universe)
        {
          LemmaEquivalentSameClosure(withoutI[k].lhs, fds, prev, universe);
        }
        forall k | 0 <= k < |fds|
          ensures ImpliesFD(withoutI, fds[k], universe)
        {
          LemmaEquivalentSameClosure(fds[k].lhs, prev, withoutI, universe);
        }
        clean := withoutI;
      } else {
        i := i + 1;
      }
    }
  }

  // Computes a canonical (minimal) cover equivalent to `fds`.
  method ComputeMinimalCover(fds: seq<FD>, attrsSeq: seq<Name>) returns (cover: seq<FD>)
    requires ValidFDs(fds, SeqToSet(attrsSeq))
    ensures ValidFDs(cover, SeqToSet(attrsSeq))
    ensures forall i :: 0 <= i < |cover| ==> |cover[i].rhs| == 1 && !IsTrivialFD(cover[i])
    ensures EquivalentFDs(fds, cover, SeqToSet(attrsSeq))
  {
    var universe := SeqToSet(attrsSeq);
    var s1 := SplitToSingletonRHS(fds, attrsSeq);
    var s2 := ReduceLHS(s1, attrsSeq);
    cover := RemoveRedundantFDs(s2, attrsSeq);

    // Chain equivalences: fds <-> s1 <-> s2 <-> cover
    forall k | 0 <= k < |cover|
      ensures ImpliesFD(fds, cover[k], universe)
    {
      LemmaEquivalentSameClosure(cover[k].lhs, fds, s1, universe);
      LemmaEquivalentSameClosure(cover[k].lhs, s1, s2, universe);
      LemmaEquivalentSameClosure(cover[k].lhs, s2, cover, universe);
    }
    forall k | 0 <= k < |fds|
      ensures ImpliesFD(cover, fds[k], universe)
    {
      LemmaEquivalentSameClosure(fds[k].lhs, fds, s1, universe);
      LemmaEquivalentSameClosure(fds[k].lhs, s1, s2, universe);
      LemmaEquivalentSameClosure(fds[k].lhs, s2, cover, universe);
    }
  }

  // ---------------------------------------------------------------------------
  // FD Projection onto a sub-relation `subAttrsSeq`
  // ---------------------------------------------------------------------------

  // Computes a sound, complete projection `pi_{sub}(fds)` of all non-trivial
  // FDs implied by `fds` whose attributes lie within `subAttrsSeq`.
  method ProjectFDs(
    subAttrsSeq: seq<Name>,
    fds: seq<FD>,
    universe: set<Name>
  ) returns (proj: seq<FD>)
    requires SeqToSet(subAttrsSeq) <= universe
    requires ValidFDs(fds, universe)
    ensures ValidFDs(proj, SeqToSet(subAttrsSeq))
    ensures ImpliesAllFDs(fds, proj, universe)
  {
    var subSet := SeqToSet(subAttrsSeq);
    var lhsSub := FilterInSet(DeduplicateNames(subAttrsSeq), AllLhsAttrs(fds));
    LemmaFilterInSetSeqToSet(DeduplicateNames(subAttrsSeq), AllLhsAttrs(fds));
    var subs := AllSubsets(lhsSub);
    proj := [];
    var i := 0;
    while i < |subs|
      invariant 0 <= i <= |subs|
      invariant ValidFDs(proj, subSet)
      invariant ImpliesAllFDs(fds, proj, universe)
      decreases |subs| - i
    {
      var x := subs[i];
      if x != {} {
        LemmaAllSubsetsComplete(lhsSub, x);
        assert x <= subSet <= universe;
        var rhs := (AttributeClosure(x, fds, universe) * subSet) - x;
        if rhs != {} {
          var fd := FD(x, rhs);
          assert ValidFD(fd, subSet);
          assert ImpliesFD(fds, fd, universe);
          proj := proj + [fd];
        }
      }
      i := i + 1;
    }
  }

  // ---------------------------------------------------------------------------
  // Formatting helpers
  // ---------------------------------------------------------------------------

  function JoinSetNames(s: set<Name>, order: seq<Name>): string
    decreases |order|
  {
    var filtered := FilterInSet(order, s);
    JoinSeqNames(filtered)
  }

  function JoinSeqNames(names: seq<Name>): string
    decreases |names|
  {
    if |names| == 0 then ""
    else if |names| == 1 then names[0]
    else names[0] + ", " + JoinSeqNames(names[1..])
  }

  function FormatFD(fd: FD, order: seq<Name>): string
  {
    "{" + JoinSetNames(fd.lhs, order) + "} -> {" + JoinSetNames(fd.rhs, order) + "}"
  }
}
