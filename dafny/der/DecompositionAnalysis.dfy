// Decomposition Analysis Algorithms:
//   1. Lossless-Join Test:
//        - Full Aho-Beeri-Ullman Chase (Tableau) Algorithm for arbitrary
//          n-way decompositions `R1, R2, ..., Rk` with a verified strictly
//          decreasing potential measure (`TableauPotential`).
//        - Classic Binary Lossless-Join criterion (`IsBinaryLossless`) plus
//          a formal soundness lemma for FD-driven splits `(X U Y, R \ Y)`.
//   2. Dependency-Preservation Test:
//        - Ullman's polynomial-time algorithm (`CheckDependencyPreserving`)
//          for arbitrary n-way decompositions without computing `F+`, also
//          returning the exact list of any lost functional dependencies.

include "Types.dfy"
include "FunctionalDeps.dfy"

module DecompositionAnalysis {
  import opened DerTypes
  import opened FunctionalDeps

  // ---------------------------------------------------------------------------
  // Analysis result type
  // ---------------------------------------------------------------------------

  datatype DecompositionReport = DecompositionReport(
    losslessJoin: bool,
    dependencyPreserving: bool,
    lostDependencies: seq<FD>
  )

  // ---------------------------------------------------------------------------
  // Binary Lossless-Join Criterion & Split Soundness Lemma
  // ---------------------------------------------------------------------------

  predicate IsBinaryLossless(
    r1: set<Name>,
    r2: set<Name>,
    fds: seq<FD>,
    universe: set<Name>
  )
  {
    var common := r1 * r2;
    (r1 + r2 == universe) &&
    (r1 <= AttributeClosure(common, fds, universe) ||
     r2 <= AttributeClosure(common, fds, universe))
  }

  // Every standard FD-based decomposition of `universe` along `x -> y`
  // (where `x` and `y` are disjoint subsets of `universe`) into
  // `R1 = x + y` and `R2 = universe - y` is GUARANTEED lossless-join.
  lemma LemmaBinarySplitIsLossless(
    x: set<Name>,
    y: set<Name>,
    fds: seq<FD>,
    universe: set<Name>
  )
    requires x <= universe && y <= universe && (x * y == {})
    requires y <= AttributeClosure(x, fds, universe)
    ensures IsBinaryLossless(x + y, universe - y, fds, universe)
  {
    var r1 := x + y;
    var r2 := universe - y;
    assert r1 + r2 == universe;
    forall a | a in x
      ensures a !in y
    {
      if a in y {
        assert a in x * y;
      }
    }
    assert r1 * r2 == x;
    assert x <= AttributeClosure(x, fds, universe);
    assert r1 <= AttributeClosure(r1 * r2, fds, universe);
  }

  // ---------------------------------------------------------------------------
  // Chase (Tableau) Algorithm for General n-Way Lossless-Join Verification
  // ---------------------------------------------------------------------------

  datatype Cell =
    | Distinguished
    | Subscripted(rowId: nat)

  type Row = seq<Cell>
  type Tableau = seq<Row>

  predicate ValidTableau(tab: Tableau, numCols: nat)
  {
    forall r :: 0 <= r < |tab| ==> |tab[r]| == numCols
  }

  // Strictly injective rank: Distinguished -> 0, Subscripted(r) -> r + 1.
  function CellRank(c: Cell): nat
  {
    match c
    case Distinguished => 0
    case Subscripted(r) => r + 1
  }

  function MinCell(c1: Cell, c2: Cell): Cell
  {
    if CellRank(c1) <= CellRank(c2) then c1 else c2
  }

  lemma LemmaMinCellRank(c1: Cell, c2: Cell)
    requires c1 != c2
    ensures CellRank(MinCell(c1, c2)) <= CellRank(c1)
    ensures CellRank(MinCell(c1, c2)) <= CellRank(c2)
    ensures CellRank(MinCell(c1, c2)) < CellRank(c1) ||
            CellRank(MinCell(c1, c2)) < CellRank(c2)
  {
    match (c1, c2) {
      case (Distinguished, Distinguished) => assert false;
      case (Distinguished, Subscripted(r)) =>
      case (Subscripted(r), Distinguished) =>
      case (Subscripted(r1), Subscripted(r2)) =>
    }
  }

  function RowPotential(row: Row): nat
    decreases |row|
  {
    if |row| == 0 then 0
    else CellRank(row[0]) + RowPotential(row[1..])
  }

  function TableauPotential(tab: Tableau): nat
    decreases |tab|
  {
    if |tab| == 0 then 0
    else RowPotential(tab[0]) + TableauPotential(tab[1..])
  }

  lemma LemmaRowPotentialUpdate(row: Row, c: nat, newVal: Cell)
    requires c < |row|
    ensures RowPotential(row[c := newVal]) + CellRank(row[c]) ==
            RowPotential(row) + CellRank(newVal)
    decreases |row|
  {
    if c == 0 {
      assert row[0 := newVal][0] == newVal;
      assert row[0 := newVal][1..] == row[1..];
    } else {
      assert row[c := newVal][0] == row[0];
      assert row[c := newVal][1..] == row[1..][c - 1 := newVal];
      LemmaRowPotentialUpdate(row[1..], c - 1, newVal);
    }
  }

  lemma LemmaTableauPotentialUpdate(tab: Tableau, r: nat, newRow: Row)
    requires r < |tab|
    ensures TableauPotential(tab[r := newRow]) + RowPotential(tab[r]) ==
            TableauPotential(tab) + RowPotential(newRow)
    decreases |tab|
  {
    if r == 0 {
      assert tab[0 := newRow][0] == newRow;
      assert tab[0 := newRow][1..] == tab[1..];
    } else {
      assert tab[r := newRow][0] == tab[0];
      assert tab[r := newRow][1..] == tab[1..][r - 1 := newRow];
      LemmaTableauPotentialUpdate(tab[1..], r - 1, newRow);
    }
  }

  lemma LemmaSetCellNonIncreasing(tab: Tableau, r: nat, c: nat, newVal: Cell)
    requires r < |tab| && c < |tab[r]|
    requires CellRank(newVal) <= CellRank(tab[r][c])
    ensures var updated := tab[r := tab[r][c := newVal]];
      TableauPotential(updated) <= TableauPotential(tab) &&
      (CellRank(newVal) < CellRank(tab[r][c]) ==>
        TableauPotential(updated) < TableauPotential(tab))
  {
    var newRow := tab[r][c := newVal];
    LemmaRowPotentialUpdate(tab[r], c, newVal);
    LemmaTableauPotentialUpdate(tab, r, newRow);
  }

  method InitTableau(attrsSeq: seq<Name>, decomp: seq<set<Name>>) returns (tab: Tableau)
    ensures |tab| == |decomp|
    ensures ValidTableau(tab, |attrsSeq|)
  {
    tab := [];
    var i := 0;
    while i < |decomp|
      invariant 0 <= i <= |decomp|
      invariant |tab| == i
      invariant ValidTableau(tab, |attrsSeq|)
      decreases |decomp| - i
    {
      var row: Row := [];
      var j := 0;
      while j < |attrsSeq|
        invariant 0 <= j <= |attrsSeq|
        invariant |row| == j
        decreases |attrsSeq| - j
      {
        var cell := if attrsSeq[j] in decomp[i] then Distinguished else Subscripted(i);
        row := row + [cell];
        j := j + 1;
      }
      tab := tab + [row];
      i := i + 1;
    }
  }

  predicate RowsAgreeOn(r1: Row, r2: Row, attrsSeq: seq<Name>, x: set<Name>)
    requires |r1| == |attrsSeq| && |r2| == |attrsSeq|
  {
    forall c :: 0 <= c < |attrsSeq| && attrsSeq[c] in x ==> r1[c] == r2[c]
  }

  predicate IsAllDistinguishedRow(row: Row)
  {
    forall c :: 0 <= c < |row| ==> row[c].Distinguished?
  }

  predicate HasAllDistinguishedRow(tab: Tableau)
  {
    exists r :: 0 <= r < |tab| && IsAllDistinguishedRow(tab[r])
  }

  // Equates rows `r1` and `r2` on every column in `rhs` using `MinCell`.
  method EquateRowsOnRhs(
    tab: Tableau,
    attrsSeq: seq<Name>,
    r1: nat,
    r2: nat,
    rhs: set<Name>
  ) returns (updated: Tableau, changed: bool)
    requires ValidTableau(tab, |attrsSeq|)
    requires r1 < |tab| && r2 < |tab| && r1 != r2
    ensures |updated| == |tab|
    ensures ValidTableau(updated, |attrsSeq|)
    ensures TableauPotential(updated) <= TableauPotential(tab)
    ensures changed ==> TableauPotential(updated) < TableauPotential(tab)
  {
    updated := tab;
    changed := false;
    var c := 0;
    while c < |attrsSeq|
      invariant 0 <= c <= |attrsSeq|
      invariant |updated| == |tab|
      invariant ValidTableau(updated, |attrsSeq|)
      invariant TableauPotential(updated) <= TableauPotential(tab)
      invariant changed ==> TableauPotential(updated) < TableauPotential(tab)
      decreases |attrsSeq| - c
    {
      if attrsSeq[c] in rhs {
        var v1 := updated[r1][c];
        var v2 := updated[r2][c];
        if v1 != v2 {
          var m := MinCell(v1, v2);
          LemmaMinCellRank(v1, v2);
          ghost var p0 := TableauPotential(updated);
          if CellRank(m) < CellRank(v1) {
            LemmaSetCellNonIncreasing(updated, r1, c, m);
            updated := updated[r1 := updated[r1][c := m]];
            assert TableauPotential(updated) < p0;
          }
          ghost var p1 := TableauPotential(updated);
          assert updated[r2][c] == v2;
          if CellRank(m) < CellRank(v2) {
            LemmaSetCellNonIncreasing(updated, r2, c, m);
            updated := updated[r2 := updated[r2][c := m]];
            assert TableauPotential(updated) < p1;
          }
          assert TableauPotential(updated) < p0;
          changed := true;
        }
      }
      c := c + 1;
    }
  }

  // Applies one pass of every FD across every pair of rows in the tableau.
  method ChasePass(
    tab: Tableau,
    attrsSeq: seq<Name>,
    fds: seq<FD>
  ) returns (updated: Tableau, changed: bool)
    requires ValidTableau(tab, |attrsSeq|)
    ensures |updated| == |tab|
    ensures ValidTableau(updated, |attrsSeq|)
    ensures TableauPotential(updated) <= TableauPotential(tab)
    ensures changed ==> TableauPotential(updated) < TableauPotential(tab)
  {
    updated := tab;
    changed := false;
    var f := 0;
    while f < |fds|
      invariant 0 <= f <= |fds|
      invariant |updated| == |tab|
      invariant ValidTableau(updated, |attrsSeq|)
      invariant TableauPotential(updated) <= TableauPotential(tab)
      invariant changed ==> TableauPotential(updated) < TableauPotential(tab)
      decreases |fds| - f
    {
      var fd := fds[f];
      var r1 := 0;
      while r1 < |updated|
        invariant 0 <= r1 <= |updated|
        invariant |updated| == |tab|
        invariant ValidTableau(updated, |attrsSeq|)
        invariant TableauPotential(updated) <= TableauPotential(tab)
        invariant changed ==> TableauPotential(updated) < TableauPotential(tab)
        decreases |updated| - r1
      {
        var r2 := r1 + 1;
        while r2 < |updated|
          invariant r1 < r2 <= |updated|
          invariant |updated| == |tab|
          invariant ValidTableau(updated, |attrsSeq|)
          invariant TableauPotential(updated) <= TableauPotential(tab)
          invariant changed ==> TableauPotential(updated) < TableauPotential(tab)
          decreases |updated| - r2
        {
          if RowsAgreeOn(updated[r1], updated[r2], attrsSeq, fd.lhs) {
            var stepChanged: bool;
            updated, stepChanged := EquateRowsOnRhs(updated, attrsSeq, r1, r2, fd.rhs);
            if stepChanged {
              changed := true;
            }
          }
          r2 := r2 + 1;
        }
        r1 := r1 + 1;
      }
      f := f + 1;
    }
  }

  // Full Aho-Beeri-Ullman Chase Algorithm: returns true iff `decomp` is a
  // lossless-join decomposition of `attrsSeq` under `fds`.
  method CheckLosslessJoin(
    attrsSeq: seq<Name>,
    decomp: seq<set<Name>>,
    fds: seq<FD>
  ) returns (lossless: bool)
  {
    if |attrsSeq| == 0 {
      return true;
    }
    if |decomp| == 0 {
      return false;
    }

    var tab := InitTableau(attrsSeq, decomp);
    var changed := true;
    while changed
      invariant |tab| == |decomp|
      invariant ValidTableau(tab, |attrsSeq|)
      decreases TableauPotential(tab), if changed then 1 else 0
    {
      var nextTab, stepChanged := ChasePass(tab, attrsSeq, fds);
      tab := nextTab;
      changed := stepChanged;
    }
    lossless := HasAllDistinguishedRow(tab);
  }

  // ---------------------------------------------------------------------------
  // Ullman's Polynomial-Time Dependency-Preservation Algorithm
  // ---------------------------------------------------------------------------

  // Checks whether a single FD `fd` (X -> Y) is preserved by the projection
  // of `fds` onto the decomposed schemas `decomp`.
  method CheckSingleFDPreserved(
    attrsSeq: seq<Name>,
    decomp: seq<set<Name>>,
    fds: seq<FD>,
    fd: FD
  ) returns (preserved: bool)
  {
    var universe := SeqToSet(attrsSeq);
    var res := fd.lhs * universe;
    var changed := true;
    while changed
      invariant res <= universe
      decreases universe - res, if changed then 1 else 0
    {
      ghost var prevRes := res;
      changed := false;
      var i := 0;
      while i < |decomp|
        invariant 0 <= i <= |decomp|
        invariant prevRes <= res <= universe
        invariant changed ==> (universe - res) < (universe - prevRes)
        decreases |decomp| - i
      {
        var ri := decomp[i] * universe;
        var t := AttributeClosure(res * ri, fds, universe) * ri;
        if !(t <= res) {
          assert res < res + t && (res + t) <= universe;
          assert (universe - (res + t)) < (universe - res);
          res := res + t;
          assert (universe - res) < (universe - prevRes);
          changed := true;
        }
        i := i + 1;
      }
    }
    preserved := fd.rhs <= res;
  }

  // Checks whether ALL FDs in `fds` are preserved by `decomp`, returning both
  // the verdict and the exact sequence of lost dependencies (if any).
  method CheckDependencyPreserving(
    attrsSeq: seq<Name>,
    decomp: seq<set<Name>>,
    fds: seq<FD>
  ) returns (preserving: bool, lost: seq<FD>)
    ensures preserving <==> |lost| == 0
  {
    lost := [];
    var i := 0;
    while i < |fds|
      invariant 0 <= i <= |fds|
      decreases |fds| - i
    {
      var ok := CheckSingleFDPreserved(attrsSeq, decomp, fds, fds[i]);
      if !ok {
        lost := lost + [fds[i]];
      }
      i := i + 1;
    }
    preserving := |lost| == 0;
  }

  // Unified decomposition analyzer: verifies BOTH lossless-join (no loss of
  // information) and dependency preservation (no loss of dependencies).
  method AnalyzeDecomposition(
    attrsSeq: seq<Name>,
    decomp: seq<set<Name>>,
    fds: seq<FD>
  ) returns (report: DecompositionReport)
    ensures report.dependencyPreserving <==> |report.lostDependencies| == 0
  {
    var lossless := CheckLosslessJoin(attrsSeq, decomp, fds);
    var depPres, lost := CheckDependencyPreserving(attrsSeq, decomp, fds);
    report := DecompositionReport(lossless, depPres, lost);
  }

  // ---------------------------------------------------------------------------
  // Formatting helper
  // ---------------------------------------------------------------------------

  function FormatLostFDs(lost: seq<FD>, order: seq<Name>): string
    decreases |lost|
  {
    if |lost| == 0 then ""
    else "    - " + FormatFD(lost[0], order) + "\n" + FormatLostFDs(lost[1..], order)
  }

  function FormatDecompositionReport(report: DecompositionReport, order: seq<Name>): string
  {
    "  Lossless-Join (No Information Loss): " +
      (if report.losslessJoin then "YES" else "NO") + "\n" +
    "  Dependency-Preserving (No FD Loss):  " +
      (if report.dependencyPreserving then "YES" else "NO") + "\n" +
    (if |report.lostDependencies| == 0 then ""
     else "  Lost Dependencies:\n" + FormatLostFDs(report.lostDependencies, order))
  }
}
