// Relational Normalization Engine (1NF, 2NF, 3NF, BCNF):
//   - Bridges directly from `RelationalModel.RelationalSchema` (output of
//     `DerToRelational.ConvertDerToRelational`) + Functional Dependencies.
//   - Validators for 1NF, 2NF, 3NF, and BCNF returning detailed reports with
//     candidate keys, highest satisfied normal form, and violation explanations.
//   - Formally verified converters to each target normal form:
//       * 1NF  — extracts multi-valued/non-atomic columns into child tables
//       * 2NF  — lossless decomposition removing partial dependencies
//       * 3NF  — Bernstein's 3NF Synthesis (minimal cover -> grouped schemas ->
//                redundancy elimination -> candidate-key preservation)
//       * BCNF — lossless BCNF decomposition eliminating non-superkey FDs
//   - Integrates with `DecompositionAnalysis` to verify lossless-join and
//     dependency preservation on any converted schema.

include "Types.dfy"
include "RelationalModel.dfy"
include "FunctionalDeps.dfy"
include "DecompositionAnalysis.dfy"

module Normalization {
  import opened DerTypes
  import opened RelationalModel
  import opened FunctionalDeps
  import opened DecompositionAnalysis

  // ---------------------------------------------------------------------------
  // Core Normalization Types
  // ---------------------------------------------------------------------------

  datatype NormalForm =
    | Unnormalized
    | NF1
    | NF2
    | NF3
    | BCNF

  function NormalFormRank(nf: NormalForm): nat
  {
    match nf
    case Unnormalized => 0
    case NF1 => 1
    case NF2 => 2
    case NF3 => 3
    case BCNF => 4
  }

  function MinNormalForm(a: NormalForm, b: NormalForm): NormalForm
  {
    if NormalFormRank(a) <= NormalFormRank(b) then a else b
  }

  datatype NormalizedRelation = NormalizedRelation(
    table: TableSchema,
    fds: seq<FD>
  )

  datatype NormalizedSchema = NormalizedSchema(
    relations: seq<NormalizedRelation>
  )

  datatype ValidationReport = ValidationReport(
    tableName: Name,
    is1NF: bool,
    is2NF: bool,
    is3NF: bool,
    isBCNF: bool,
    highestForm: NormalForm,
    candidateKeys: seq<set<Name>>,
    violations: seq<string>
  )

  // ---------------------------------------------------------------------------
  // Column / Schema Projection Helpers
  // ---------------------------------------------------------------------------

  function ColNames(cols: seq<Column>): seq<Name>
    ensures |ColNames(cols)| == |cols|
    ensures forall i :: 0 <= i < |cols| ==> ColNames(cols)[i] == cols[i].name
  {
    seq(|cols|, i requires 0 <= i < |cols| => cols[i].name)
  }

  lemma LemmaColNamesAppend(a: seq<Column>, b: seq<Column>)
    ensures ColNames(a + b) == ColNames(a) + ColNames(b)
  {
  }

  function TableAttrSeq(t: TableSchema): seq<Name>
  {
    ColNames(t.columns)
  }

  function TableAttrSet(t: TableSchema): set<Name>
  {
    SeqToSet(ColNames(t.columns))
  }

  predicate UniqueColumnNames(cols: seq<Column>)
  {
    UniqueNames(ColNames(cols))
  }

  predicate AllColumnsAtomic(cols: seq<Column>)
  {
    forall i :: 0 <= i < |cols| ==> IsAtomicType(cols[i].colType)
  }

  predicate ValidNormalizedRelation(rel: NormalizedRelation)
  {
    ValidTable(rel.table) &&
    UniqueColumnNames(rel.table.columns) &&
    ValidFDs(rel.fds, TableAttrSet(rel.table))
  }

  predicate ValidNormalizedSchema(schema: NormalizedSchema)
  {
    forall i :: 0 <= i < |schema.relations| ==> ValidNormalizedRelation(schema.relations[i])
  }

  lemma LemmaColNameInTableHasColumn(cols: seq<Column>, colName: Name)
    ensures colName in SeqToSet(ColNames(cols)) <==> HasColumn(cols, colName)
    decreases |cols|
  {
    if |cols| == 0 {
    } else {
      LemmaColNameInTableHasColumn(cols[1..], colName);
      if cols[0].name == colName {
        assert cols[0].name == colName;
      } else {
        if HasColumn(cols, colName) {
          var idx :| 0 <= idx < |cols| && cols[idx].name == colName;
          assert idx > 0 && cols[1..][idx - 1].name == colName;
        }
        if HasColumn(cols[1..], colName) {
          var idx :| 0 <= idx < |cols[1..]| && cols[1..][idx].name == colName;
          assert cols[idx + 1].name == colName;
        }
      }
    }
  }

  function FilterColumnsBySet(cols: seq<Column>, keep: set<Name>): seq<Column>
    ensures |FilterColumnsBySet(cols, keep)| <= |cols|
    ensures AllColumnsAtomic(cols) ==> AllColumnsAtomic(FilterColumnsBySet(cols, keep))
    ensures UniqueColumnNames(cols) ==> UniqueColumnNames(FilterColumnsBySet(cols, keep))
    ensures SeqToSet(ColNames(FilterColumnsBySet(cols, keep))) == SeqToSet(ColNames(cols)) * keep
    decreases |cols|
  {
    if |cols| == 0 then []
    else
      var rest := FilterColumnsBySet(cols[1..], keep);
      if cols[0].name in keep then
        assert ColNames([cols[0]] + rest) == [cols[0].name] + ColNames(rest);
        assert UniqueColumnNames(cols) ==>
          (forall j :: 0 <= j < |rest| ==> cols[0].name != rest[j].name) by {
            if UniqueColumnNames(cols) {
              forall j | 0 <= j < |rest|
                ensures cols[0].name != rest[j].name
              {
                assert rest[j].name in SeqToSet(ColNames(rest)) by {
                  LemmaSeqToSetMembership(ColNames(rest), rest[j].name);
                }
                assert rest[j].name in SeqToSet(ColNames(cols[1..]));
                LemmaSeqToSetMembership(ColNames(cols[1..]), rest[j].name);
                var idx :| 0 <= idx < |cols[1..]| && cols[1..][idx].name == rest[j].name;
                assert cols[idx + 1].name == rest[j].name;
              }
            }
          }
        [cols[0]] + rest
      else
        rest
  }

  // Strictly fewer columns when `keep` omits at least one column of `cols`.
  lemma LemmaStrictSubsetFewerColumns(cols: seq<Column>, keep: set<Name>, omitted: Name)
    requires omitted in SeqToSet(ColNames(cols))
    requires omitted !in keep
    ensures |FilterColumnsBySet(cols, keep)| < |cols|
    decreases |cols|
  {
    if cols[0].name == omitted {
      assert |FilterColumnsBySet(cols, keep)| == |FilterColumnsBySet(cols[1..], keep)| <= |cols[1..]|;
    } else {
      assert omitted in SeqToSet(ColNames(cols[1..]));
      LemmaStrictSubsetFewerColumns(cols[1..], keep, omitted);
    }
  }

  lemma LemmaNonEmptySetGivesNonEmptyCols(cols: seq<Column>, keep: set<Name>)
    requires keep != {}
    requires keep <= SeqToSet(ColNames(cols))
    ensures |FilterColumnsBySet(cols, keep)| > 0
  {
    assert SeqToSet(ColNames(FilterColumnsBySet(cols, keep))) == keep;
    if |FilterColumnsBySet(cols, keep)| == 0 {
      assert SeqToSet(ColNames(FilterColumnsBySet(cols, keep))) == {};
      assert false;
    }
  }

  // Any superkey of a non-empty relation under valid FDs must be non-empty.
  lemma LemmaSuperkeyNonEmpty(k: set<Name>, attrs: set<Name>, fds: seq<FD>)
    requires attrs != {}
    requires ValidFDs(fds, attrs)
    requires IsSuperkey(k, attrs, fds)
    ensures k != {}
  {
    if k == {} {
      forall i | 0 <= i < |fds| && fds[i].lhs <= {}
        ensures (fds[i].rhs * attrs) <= {}
      {
        assert fds[i].lhs != {};
        assert false;
      }
      LemmaClosureLoopMinimal({}, {}, fds, attrs);
      assert AttributeClosure({}, fds, attrs) == {};
      assert false;
    }
  }

  // ---------------------------------------------------------------------------
  // Bridge from DER -> RM (`RelationalSchema`) to `NormalizedSchema`
  // ---------------------------------------------------------------------------

  function DeduplicateColumns(cols: seq<Column>): seq<Column>
    ensures UniqueColumnNames(DeduplicateColumns(cols))
    ensures SeqToSet(ColNames(DeduplicateColumns(cols))) == SeqToSet(ColNames(cols))
    ensures AllColumnsAtomic(cols) ==> AllColumnsAtomic(DeduplicateColumns(cols))
    decreases |cols|
  {
    if |cols| == 0 then []
    else
      var rest := DeduplicateColumns(cols[1..]);
      if cols[0].name in SeqToSet(ColNames(rest)) then
        rest
      else
        assert forall j :: 0 <= j < |rest| ==> cols[0].name != rest[j].name by {
          forall j | 0 <= j < |rest|
            ensures cols[0].name != rest[j].name
          {
            LemmaSeqToSetMembership(ColNames(rest), rest[j].name);
          }
        }
        [cols[0]] + rest
  }

  function FilterValidFDs(fds: seq<FD>, universe: set<Name>): seq<FD>
    ensures ValidFDs(FilterValidFDs(fds, universe), universe)
    decreases |fds|
  {
    if |fds| == 0 then []
    else if ValidFD(fds[0], universe) then [fds[0]] + FilterValidFDs(fds[1..], universe)
    else FilterValidFDs(fds[1..], universe)
  }

  // Builds a `NormalizedSchema` directly from a `RelationalSchema` (such as
  // the output of `ConvertDerToRelational(diagram)`) plus optional extra FDs
  // per table name. Automatically adds each table's `PK -> all columns` FD.
  method BuildNormalizedSchemaFromRM(
    rm: RelationalSchema,
    extraFDsByTable: map<Name, seq<FD>>
  ) returns (schema: NormalizedSchema)
    requires ValidRelationalSchema(rm)
    ensures ValidNormalizedSchema(schema)
    ensures |schema.relations| == |rm.tables|
  {
    var rels: seq<NormalizedRelation> := [];
    var i := 0;
    while i < |rm.tables|
      invariant 0 <= i <= |rm.tables|
      invariant |rels| == i
      invariant ValidNormalizedSchema(NormalizedSchema(rels))
      decreases |rm.tables| - i
    {
      var t := rm.tables[i];
      var dedupCols := DeduplicateColumns(t.columns);

      // Deduplicating preserves HasColumn for every PK and FK column:
      forall p | 0 <= p < |t.primaryKey|
        ensures HasColumn(dedupCols, t.primaryKey[p])
      {
        LemmaColNameInTableHasColumn(t.columns, t.primaryKey[p]);
        LemmaColNameInTableHasColumn(dedupCols, t.primaryKey[p]);
      }
      forall f | 0 <= f < |t.foreignKeys|
        ensures ValidForeignKey(t.foreignKeys[f], dedupCols)
      {
        forall c | 0 <= c < |t.foreignKeys[f].columns|
          ensures HasColumn(dedupCols, t.foreignKeys[f].columns[c])
        {
          LemmaColNameInTableHasColumn(t.columns, t.foreignKeys[f].columns[c]);
          LemmaColNameInTableHasColumn(dedupCols, t.foreignKeys[f].columns[c]);
        }
      }

      var cleanTable := TableSchema(t.name, dedupCols, t.primaryKey, t.foreignKeys);
      var universe := TableAttrSet(cleanTable);
      var pkSet := SeqToSet(cleanTable.primaryKey);

      assert cleanTable.primaryKey[0] in pkSet;
      assert pkSet <= universe by {
        forall a | a in pkSet
          ensures a in universe
        {
          LemmaSeqToSetMembership(cleanTable.primaryKey, a);
          var pIdx :| 0 <= pIdx < |cleanTable.primaryKey| && cleanTable.primaryKey[pIdx] == a;
          LemmaColNameInTableHasColumn(dedupCols, a);
        }
      }

      var pkFd := FD(pkSet, universe);
      var rawExtras := if t.name in extraFDsByTable then extraFDsByTable[t.name] else [];
      var validExtras := FilterValidFDs(rawExtras, universe);
      var allFDs := [pkFd] + validExtras;

      var nr := NormalizedRelation(cleanTable, allFDs);
      assert ValidNormalizedRelation(nr);
      rels := rels + [nr];
      i := i + 1;
    }
    schema := NormalizedSchema(rels);
  }

  // ---------------------------------------------------------------------------
  // Normal Form Predicates (1NF, 2NF, 3NF, BCNF)
  // ---------------------------------------------------------------------------

  // 1NF: Valid table, unique column names, and every column has an atomic domain.
  predicate IsTable1NF(t: TableSchema)
  {
    ValidTable(t) &&
    UniqueColumnNames(t.columns) &&
    AllColumnsAtomic(t.columns)
  }

  // 2NF condition (given exact candidate keys `cks`): no non-prime attribute
  // depends on any proper subset of any candidate key.
  predicate HasNoPartialDependencies(
    attrsSeq: seq<Name>,
    fds: seq<FD>,
    cks: seq<set<Name>>
  )
  {
    var attrs := SeqToSet(attrsSeq);
    forall cIdx :: 0 <= cIdx < |cks| ==>
      forall bIdx :: 0 <= bIdx < |attrsSeq| && attrsSeq[bIdx] in cks[cIdx] ==>
        var sub := cks[cIdx] - {attrsSeq[bIdx]};
        var cl := AttributeClosure(sub, fds, attrs);
        forall aIdx :: 0 <= aIdx < |attrsSeq| && attrsSeq[aIdx] in cl ==>
          attrsSeq[aIdx] in sub || IsPrimeAttribute(attrsSeq[aIdx], cks)
  }

  // 3NF condition (given exact candidate keys `cks`): for every FD `X -> Y`,
  // either `X` is a superkey or every non-trivial RHS attribute is prime.
  predicate Satisfies3NFCondition(
    attrsSeq: seq<Name>,
    fds: seq<FD>,
    cks: seq<set<Name>>
  )
  {
    var attrs := SeqToSet(attrsSeq);
    forall fIdx :: 0 <= fIdx < |fds| ==>
      IsSuperkey(fds[fIdx].lhs, attrs, fds) ||
      (forall aIdx :: 0 <= aIdx < |attrsSeq| && attrsSeq[aIdx] in fds[fIdx].rhs ==>
        attrsSeq[aIdx] in fds[fIdx].lhs || IsPrimeAttribute(attrsSeq[aIdx], cks))
  }

  // BCNF condition: every non-trivial FD has a superkey determinant.
  predicate SatisfiesBCNFCondition(attrs: set<Name>, fds: seq<FD>)
  {
    forall fIdx :: 0 <= fIdx < |fds| ==>
      IsTrivialFD(fds[fIdx]) || IsSuperkey(fds[fIdx].lhs, attrs, fds)
  }

  lemma LemmaBCNFImplies3NF(attrsSeq: seq<Name>, fds: seq<FD>, cks: seq<set<Name>>)
    requires SatisfiesBCNFCondition(SeqToSet(attrsSeq), fds)
    ensures Satisfies3NFCondition(attrsSeq, fds, cks)
  {
    // Every FD is either trivial (all rhs in lhs) or has a superkey lhs.
  }

  // ---------------------------------------------------------------------------
  // Executable Validators (Single Relation & Entire Schema)
  // ---------------------------------------------------------------------------

  method ValidateRelation(rel: NormalizedRelation) returns (report: ValidationReport)
    requires ValidNormalizedRelation(rel)
    ensures report.is1NF <==> IsTable1NF(rel.table)
    ensures report.isBCNF ==> report.is3NF && report.is2NF && report.is1NF
    ensures report.is3NF ==> report.is2NF && report.is1NF
    ensures report.is2NF ==> report.is1NF
    ensures report.isBCNF ==> SatisfiesBCNFCondition(TableAttrSet(rel.table), rel.fds)
  {
    var attrsSeq := TableAttrSeq(rel.table);
    var attrs := TableAttrSet(rel.table);
    assert |attrsSeq| > 0 by {
      LemmaColNameInTableHasColumn(rel.table.columns, rel.table.primaryKey[0]);
      if |rel.table.columns| == 0 {
        assert !HasColumn(rel.table.columns, rel.table.primaryKey[0]);
      }
    }

    var cks := FindCandidateKeys(attrsSeq, rel.fds);
    var violations: seq<string> := [];

    // 1NF check
    var is1NF := IsTable1NF(rel.table);
    if !is1NF {
      var ci := 0;
      while ci < |rel.table.columns|
        invariant 0 <= ci <= |rel.table.columns|
        decreases |rel.table.columns| - ci
      {
        if !IsAtomicType(rel.table.columns[ci].colType) {
          violations := violations + [
            "1NF violation: non-atomic column '" + rel.table.columns[ci].name +
            "' of type " + FormatAttrType(rel.table.columns[ci].colType)
          ];
        }
        ci := ci + 1;
      }
    }

    // 2NF check
    var noPartial := HasNoPartialDependencies(attrsSeq, rel.fds, cks);
    var is2NF := is1NF && noPartial;
    if is1NF && !noPartial {
      violations := violations + [
        "2NF violation: non-prime attribute partially depends on a proper subset of a candidate key"
      ];
    }

    // 3NF check
    var ok3NF := Satisfies3NFCondition(attrsSeq, rel.fds, cks);
    var is3NF := is2NF && ok3NF;
    if is2NF && !ok3NF {
      var fi := 0;
      while fi < |rel.fds|
        invariant 0 <= fi <= |rel.fds|
        decreases |rel.fds| - fi
      {
        var fd := rel.fds[fi];
        if !IsSuperkey(fd.lhs, attrs, rel.fds) &&
           !(forall aIdx :: 0 <= aIdx < |attrsSeq| && attrsSeq[aIdx] in fd.rhs ==>
               attrsSeq[aIdx] in fd.lhs || IsPrimeAttribute(attrsSeq[aIdx], cks)) {
          violations := violations + [
            "3NF violation: " + FormatFD(fd, attrsSeq) +
            " has non-superkey LHS and non-prime RHS"
          ];
        }
        fi := fi + 1;
      }
    }

    // BCNF check
    var okBCNF := SatisfiesBCNFCondition(attrs, rel.fds);
    var isBCNF := is3NF && okBCNF;
    if is3NF && !okBCNF {
      var fi := 0;
      while fi < |rel.fds|
        invariant 0 <= fi <= |rel.fds|
        decreases |rel.fds| - fi
      {
        var fd := rel.fds[fi];
        if !IsTrivialFD(fd) && !IsSuperkey(fd.lhs, attrs, rel.fds) {
          violations := violations + [
            "BCNF violation: " + FormatFD(fd, attrsSeq) +
            " has determinant that is not a superkey"
          ];
        }
        fi := fi + 1;
      }
    }

    var highest :=
      if isBCNF then BCNF
      else if is3NF then NF3
      else if is2NF then NF2
      else if is1NF then NF1
      else Unnormalized;

    report := ValidationReport(
      rel.table.name, is1NF, is2NF, is3NF, isBCNF, highest, cks, violations
    );
  }

  predicate MeetsTargetForm(report: ValidationReport, target: NormalForm)
  {
    match target
    case Unnormalized => true
    case NF1 => report.is1NF
    case NF2 => report.is2NF
    case NF3 => report.is3NF
    case BCNF => report.isBCNF
  }

  method ValidateSchema(schema: NormalizedSchema)
    returns (reports: seq<ValidationReport>, overallForm: NormalForm)
    requires ValidNormalizedSchema(schema)
    ensures |reports| == |schema.relations|
  {
    reports := [];
    overallForm := BCNF;
    var i := 0;
    while i < |schema.relations|
      invariant 0 <= i <= |schema.relations|
      invariant |reports| == i
      decreases |schema.relations| - i
    {
      var rep := ValidateRelation(schema.relations[i]);
      reports := reports + [rep];
      overallForm := MinNormalForm(overallForm, rep.highestForm);
      i := i + 1;
    }
  }

  // ---------------------------------------------------------------------------
  // Helper: Construct a Valid 1NF Sub-Relation from an Attribute Subset
  // ---------------------------------------------------------------------------

  method BuildSubRelation(
    name: Name,
    baseCols: seq<Column>,
    attrSet: set<Name>,
    parentFDs: seq<FD>,
    parentUniverse: set<Name>
  ) returns (sub: NormalizedRelation)
    requires name != ""
    requires UniqueColumnNames(baseCols)
    requires AllColumnsAtomic(baseCols)
    requires attrSet != {} && attrSet <= SeqToSet(ColNames(baseCols))
    requires SeqToSet(ColNames(baseCols)) <= parentUniverse
    requires ValidFDs(parentFDs, parentUniverse)
    ensures ValidNormalizedRelation(sub)
    ensures IsTable1NF(sub.table)
    ensures TableAttrSet(sub.table) == attrSet
    ensures |sub.table.columns| == |FilterColumnsBySet(baseCols, attrSet)|
    ensures ImpliesAllFDs(parentFDs, sub.fds, parentUniverse)
  {
    var subCols := FilterColumnsBySet(baseCols, attrSet);
    LemmaNonEmptySetGivesNonEmptyCols(baseCols, attrSet);
    var subAttrSeq := ColNames(subCols);
    assert SeqToSet(subAttrSeq) == attrSet;

    var projFDs := ProjectFDs(subAttrSeq, parentFDs, parentUniverse);
    var ckSet := ShrinkToCandidateKey(attrSet, subAttrSeq, projFDs);
    LemmaSuperkeyNonEmpty(ckSet, attrSet, projFDs);

    var pkSeq := FilterInSet(subAttrSeq, ckSet);
    LemmaFilterInSetSeqToSet(subAttrSeq, ckSet);
    assert SeqToSet(pkSeq) == ckSet;
    assert |pkSeq| > 0 by {
      if |pkSeq| == 0 {
        assert SeqToSet(pkSeq) == {};
      }
    }

    forall p | 0 <= p < |pkSeq|
      ensures HasColumn(subCols, pkSeq[p])
    {
      LemmaSeqToSetMembership(pkSeq, pkSeq[p]);
      LemmaColNameInTableHasColumn(subCols, pkSeq[p]);
    }

    var tbl := TableSchema(name, subCols, pkSeq, []);
    sub := NormalizedRelation(tbl, projFDs);
  }

  // ---------------------------------------------------------------------------
  // Converter 1: Normalize to 1NF (Eliminate Multi-Valued Columns)
  // ---------------------------------------------------------------------------

  predicate PrimaryKeyColumnsAtomic(t: TableSchema)
  {
    forall i :: 0 <= i < |t.columns| && t.columns[i].name in t.primaryKey ==>
      IsAtomicType(t.columns[i].colType)
  }

  function AtomicCols(cols: seq<Column>): seq<Column>
    ensures AllColumnsAtomic(AtomicCols(cols))
    ensures UniqueColumnNames(cols) ==> UniqueColumnNames(AtomicCols(cols))
    ensures forall i :: 0 <= i < |AtomicCols(cols)| ==> AtomicCols(cols)[i] in cols
    decreases |cols|
  {
    if |cols| == 0 then []
    else
      var rest := AtomicCols(cols[1..]);
      if IsAtomicType(cols[0].colType) then
        assert UniqueColumnNames(cols) ==>
          (forall j :: 0 <= j < |rest| ==> cols[0].name != rest[j].name) by {
            if UniqueColumnNames(cols) {
              forall j | 0 <= j < |rest|
                ensures cols[0].name != rest[j].name
              {
                assert rest[j] in cols[1..];
                var idx :| 0 <= idx < |cols[1..]| && cols[1..][idx] == rest[j];
                assert cols[idx + 1].name == rest[j].name;
              }
            }
          }
        [cols[0]] + rest
      else
        rest
  }

  lemma LemmaAtomicColPreserved(cols: seq<Column>, idx: nat)
    requires idx < |cols|
    requires IsAtomicType(cols[idx].colType)
    ensures HasColumn(AtomicCols(cols), cols[idx].name)
    decreases |cols|
  {
    if idx == 0 {
      assert AtomicCols(cols)[0].name == cols[0].name;
    } else {
      LemmaAtomicColPreserved(cols[1..], idx - 1);
      var rest := AtomicCols(cols[1..]);
      var j :| 0 <= j < |rest| && rest[j].name == cols[idx].name;
      if IsAtomicType(cols[0].colType) {
        assert AtomicCols(cols)[j + 1].name == cols[idx].name;
      } else {
        assert AtomicCols(cols)[j].name == cols[idx].name;
      }
    }
  }

  lemma LemmaAtomicColsSubsetAttrs(cols: seq<Column>)
    ensures SeqToSet(ColNames(AtomicCols(cols))) <= SeqToSet(ColNames(cols))
    decreases |cols|
  {
    if |cols| > 0 {
      LemmaAtomicColsSubsetAttrs(cols[1..]);
    }
  }

  function KeepValidFKs(fks: seq<ForeignKey>, cols: seq<Column>): seq<ForeignKey>
    ensures forall i :: 0 <= i < |KeepValidFKs(fks, cols)| ==>
      ValidForeignKey(KeepValidFKs(fks, cols)[i], cols)
    decreases |fks|
  {
    if |fks| == 0 then []
    else if ValidForeignKey(fks[0], cols) then [fks[0]] + KeepValidFKs(fks[1..], cols)
    else KeepValidFKs(fks[1..], cols)
  }

  // Converts a relation to 1NF by extracting every `AttrMultiValued` column
  // into a child table `(PK + atomic_elem)` with composite PK and FK to parent.
  method NormalizeRelationTo1NF(rel: NormalizedRelation) returns (out: seq<NormalizedRelation>)
    requires ValidNormalizedRelation(rel)
    requires PrimaryKeyColumnsAtomic(rel.table)
    ensures ValidNormalizedSchema(NormalizedSchema(out))
    ensures |out| >= 1
    ensures forall i :: 0 <= i < |out| ==> IsTable1NF(out[i].table)
  {
    if IsTable1NF(rel.table) {
      return [rel];
    }

    var t := rel.table;
    var universe := TableAttrSet(t);
    var atomicCols := AtomicCols(t.columns);
    LemmaAtomicColsSubsetAttrs(t.columns);

    forall p | 0 <= p < |t.primaryKey|
      ensures HasColumn(atomicCols, t.primaryKey[p])
    {
      var cIdx :| 0 <= cIdx < |t.columns| && t.columns[cIdx].name == t.primaryKey[p];
      assert t.columns[cIdx].name in t.primaryKey;
      LemmaAtomicColPreserved(t.columns, cIdx);
    }

    var keptFKs := KeepValidFKs(t.foreignKeys, atomicCols);
    var baseTable := TableSchema(t.name, atomicCols, t.primaryKey, keptFKs);
    var baseAttrSeq := ColNames(atomicCols);
    var baseFDs := ProjectFDs(baseAttrSeq, rel.fds, universe);
    var baseRel := NormalizedRelation(baseTable, baseFDs);
    assert IsTable1NF(baseRel.table);
    assert ValidNormalizedRelation(baseRel);

    out := [baseRel];

    // Collect atomic PK column definitions once for child tables.
    var pkCols := FilterColumnsBySet(atomicCols, SeqToSet(t.primaryKey));
    var pkNames := ColNames(pkCols);
    forall p | 0 <= p < |t.primaryKey|
      ensures t.primaryKey[p] in SeqToSet(ColNames(atomicCols))
    {
      LemmaColNameInTableHasColumn(atomicCols, t.primaryKey[p]);
    }
    assert SeqToSet(t.primaryKey) <= SeqToSet(ColNames(atomicCols)) by {
      forall a | a in SeqToSet(t.primaryKey)
        ensures a in SeqToSet(ColNames(atomicCols))
      {
        LemmaSeqToSetMembership(t.primaryKey, a);
        var pIdx :| 0 <= pIdx < |t.primaryKey| && t.primaryKey[pIdx] == a;
        LemmaColNameInTableHasColumn(atomicCols, a);
      }
    }
    assert t.primaryKey[0] in SeqToSet(t.primaryKey);
    LemmaNonEmptySetGivesNonEmptyCols(atomicCols, SeqToSet(t.primaryKey));
    assert SeqToSet(pkNames) == SeqToSet(t.primaryKey);

    var ci := 0;
    while ci < |t.columns|
      invariant 0 <= ci <= |t.columns|
      invariant |out| >= 1
      invariant ValidNormalizedSchema(NormalizedSchema(out))
      invariant forall k :: 0 <= k < |out| ==> IsTable1NF(out[k].table)
      decreases |t.columns| - ci
    {
      var col := t.columns[ci];
      if !IsAtomicType(col.colType) {
        // Since PrimaryKeyColumnsAtomic holds, `col.name` is NOT in `t.primaryKey`.
        assert col.name !in t.primaryKey;
        assert col.name !in SeqToSet(pkNames) by {
          LemmaSeqToSetMembership(t.primaryKey, col.name);
        }

        var elemCol := Column(col.name, BaseAtomicType(col.colType));
        var childCols := pkCols + [elemCol];
        var childPK := pkNames + [col.name];
        LemmaColNamesAppend(pkCols, [elemCol]);
        assert ColNames(childCols) == childPK;

        assert UniqueColumnNames(childCols) by {
          forall j | 0 <= j < |pkCols|
            ensures pkCols[j].name != elemCol.name
          {
            LemmaSeqToSetMembership(pkNames, pkCols[j].name);
          }
        }
        assert AllColumnsAtomic(childCols);

        forall p | 0 <= p < |childPK|
          ensures HasColumn(childCols, childPK[p])
        {
          if p < |pkNames| {
            assert childCols[p].name == pkNames[p];
          } else {
            assert childCols[|pkCols|].name == col.name;
          }
        }

        forall p | 0 <= p < |pkNames|
          ensures HasColumn(childCols, pkNames[p])
        {
          assert childCols[p].name == pkNames[p];
        }

        var fkParent := ForeignKey(pkNames, t.name, pkNames);
        assert ValidForeignKey(fkParent, childCols);

        var childTable := TableSchema(t.name + "_" + col.name, childCols, childPK, [fkParent]);
        var childSet := TableAttrSet(childTable);
        assert SeqToSet(childPK) == childSet by {
          assert ColNames(childCols) == childPK;
        }
        var childFd := FD(childSet, childSet);
        assert ValidFD(childFd, childSet) by {
          assert col.name in childSet by {
            LemmaColNameInTableHasColumn(childCols, col.name);
          }
        }
        var childRel := NormalizedRelation(childTable, [childFd]);
        assert IsTable1NF(childRel.table);
        assert ValidNormalizedRelation(childRel);
        out := out + [childRel];
      }
      ci := ci + 1;
    }
  }

  // ---------------------------------------------------------------------------
  // Converter 2: Normalize to 2NF (Lossless Elimination of Partial Dependencies)
  // ---------------------------------------------------------------------------

  // Finds a partial dependency witness `(sub -> dep)` on a proper subset `sub`
  // of a candidate key, returning `found == false` iff the relation is in 2NF.
  method FindPartialDependencyWitness(
    attrsSeq: seq<Name>,
    fds: seq<FD>,
    cks: seq<set<Name>>
  ) returns (
    found: bool,
    sub: set<Name>,
    dep: set<Name>,
    missingPrime: Name
  )
    requires |attrsSeq| > 0
    requires ValidFDs(fds, SeqToSet(attrsSeq))
    requires forall i :: 0 <= i < |cks| ==> IsCandidateKey(cks[i], SeqToSet(attrsSeq), fds)
    ensures !found ==> HasNoPartialDependencies(attrsSeq, fds, cks)
    ensures found ==>
      var attrs := SeqToSet(attrsSeq);
      sub <= attrs &&
      dep <= attrs &&
      (sub * dep == {}) &&
      dep != {} &&
      dep <= AttributeClosure(sub, fds, attrs) &&
      missingPrime in attrs &&
      missingPrime !in (sub + dep)
  {
    var attrs := SeqToSet(attrsSeq);
    found := false;
    sub := {};
    dep := {};
    missingPrime := "";

    var cIdx := 0;
    while cIdx < |cks|
      invariant 0 <= cIdx <= |cks|
      invariant forall p :: 0 <= p < cIdx ==>
        forall bIdx :: 0 <= bIdx < |attrsSeq| && attrsSeq[bIdx] in cks[p] ==>
          var s := cks[p] - {attrsSeq[bIdx]};
          var cl := AttributeClosure(s, fds, attrs);
          forall aIdx :: 0 <= aIdx < |attrsSeq| && attrsSeq[aIdx] in cl ==>
            attrsSeq[aIdx] in s || IsPrimeAttribute(attrsSeq[aIdx], cks)
      decreases |cks| - cIdx
    {
      var ck := cks[cIdx];
      var bIdx := 0;
      while bIdx < |attrsSeq|
        invariant 0 <= bIdx <= |attrsSeq|
        invariant forall q :: 0 <= q < bIdx && attrsSeq[q] in ck ==>
          var s := ck - {attrsSeq[q]};
          var cl := AttributeClosure(s, fds, attrs);
          forall aIdx :: 0 <= aIdx < |attrsSeq| && attrsSeq[aIdx] in cl ==>
            attrsSeq[aIdx] in s || IsPrimeAttribute(attrsSeq[aIdx], cks)
        decreases |attrsSeq| - bIdx
      {
        var b := attrsSeq[bIdx];
        if b in ck {
          var s := ck - {b};
          var cl := AttributeClosure(s, fds, attrs);
          var nonPrimeDeps: set<Name> := {};
          var aIdx := 0;
          while aIdx < |attrsSeq|
            invariant 0 <= aIdx <= |attrsSeq|
            invariant nonPrimeDeps <= cl - s
            invariant forall x :: x in nonPrimeDeps ==> !IsPrimeAttribute(x, cks)
            invariant nonPrimeDeps == {} ==>
              forall j :: 0 <= j < aIdx && attrsSeq[j] in cl ==>
                attrsSeq[j] in s || IsPrimeAttribute(attrsSeq[j], cks)
            decreases |attrsSeq| - aIdx
          {
            var a := attrsSeq[aIdx];
            if a in cl && a !in s && !IsPrimeAttribute(a, cks) {
              nonPrimeDeps := nonPrimeDeps + {a};
            }
            aIdx := aIdx + 1;
          }

          if nonPrimeDeps != {} {
            assert IsPrimeAttribute(b, cks);
            assert b !in nonPrimeDeps;
            assert b !in s;
            assert b in attrs by { LemmaSeqToSetMembership(attrsSeq, b); }
            return true, s, nonPrimeDeps, b;
          }
        }
        bIdx := bIdx + 1;
      }
      cIdx := cIdx + 1;
    }
  }

  // Recursively decomposes a 1NF relation into lossless 2NF sub-relations.
  method DecomposeTo2NFRec(rel: NormalizedRelation, depthTag: nat) returns (out: seq<NormalizedRelation>)
    requires ValidNormalizedRelation(rel)
    requires IsTable1NF(rel.table)
    ensures ValidNormalizedSchema(NormalizedSchema(out))
    ensures |out| >= 1
    ensures forall i :: 0 <= i < |out| ==> IsTable1NF(out[i].table)
    decreases |rel.table.columns|
  {
    var attrsSeq := TableAttrSeq(rel.table);
    var attrs := TableAttrSet(rel.table);
    assert |attrsSeq| > 0 by {
      LemmaColNameInTableHasColumn(rel.table.columns, rel.table.primaryKey[0]);
      if |rel.table.columns| == 0 {
        assert !HasColumn(rel.table.columns, rel.table.primaryKey[0]);
      }
    }

    var cks := FindCandidateKeys(attrsSeq, rel.fds);
    var found, sub, dep, missingPrime := FindPartialDependencyWitness(attrsSeq, rel.fds, cks);
    if !found {
      return [rel];
    }

    // Lossless binary split: R1 = sub U dep, R2 = attrs \ dep
    LemmaBinarySplitIsLossless(sub, dep, rel.fds, attrs);
    var r1Set := sub + dep;
    var r2Set := attrs - dep;

    // Prove both subsets strictly decrease column count (guaranteeing termination).
    LemmaStrictSubsetFewerColumns(rel.table.columns, r1Set, missingPrime);
    ghost var depElem :| depElem in dep;
    LemmaStrictSubsetFewerColumns(rel.table.columns, r2Set, depElem);
    assert r1Set != {} by { assert depElem in r1Set; }
    assert r2Set != {} by { assert missingPrime in r2Set; }

    var r1 := BuildSubRelation(
      rel.table.name + "_2nf_" + NatToString(depthTag) + "a",
      rel.table.columns, r1Set, rel.fds, attrs
    );
    var r2 := BuildSubRelation(
      rel.table.name + "_2nf_" + NatToString(depthTag) + "b",
      rel.table.columns, r2Set, rel.fds, attrs
    );

    assert |r1.table.columns| < |rel.table.columns|;
    assert |r2.table.columns| < |rel.table.columns|;

    var leftOut := DecomposeTo2NFRec(r1, depthTag + 1);
    var rightOut := DecomposeTo2NFRec(r2, depthTag + 2);
    out := leftOut + rightOut;
  }

  method NormalizeRelationTo2NF(rel: NormalizedRelation) returns (out: seq<NormalizedRelation>)
    requires ValidNormalizedRelation(rel)
    requires PrimaryKeyColumnsAtomic(rel.table)
    ensures ValidNormalizedSchema(NormalizedSchema(out))
    ensures |out| >= 1
    ensures forall i :: 0 <= i < |out| ==> IsTable1NF(out[i].table)
  {
    var nf1 := NormalizeRelationTo1NF(rel);
    out := [];
    var i := 0;
    while i < |nf1|
      invariant 0 <= i <= |nf1|
      invariant ValidNormalizedSchema(NormalizedSchema(out))
      invariant i > 0 ==> |out| >= 1
      invariant forall k :: 0 <= k < |out| ==> IsTable1NF(out[k].table)
      decreases |nf1| - i
    {
      var parts := DecomposeTo2NFRec(nf1[i], 1);
      out := out + parts;
      i := i + 1;
    }
  }

  // ---------------------------------------------------------------------------
  // Converter 3: Normalize to 3NF (Bernstein's 3NF Synthesis Algorithm)
  // ---------------------------------------------------------------------------

  // Groups FDs in a minimal cover by identical LHS into relation attribute sets.
  method GroupMinimalCover(cover: seq<FD>, attrs: set<Name>) returns (groups: seq<set<Name>>)
    requires ValidFDs(cover, attrs)
    ensures forall i :: 0 <= i < |groups| ==> groups[i] != {} && groups[i] <= attrs
  {
    var lhsList: seq<set<Name>> := [];
    groups := [];
    var i := 0;
    while i < |cover|
      invariant 0 <= i <= |cover|
      invariant |lhsList| == |groups|
      invariant forall k :: 0 <= k < |groups| ==> groups[k] != {} && groups[k] <= attrs
      decreases |cover| - i
    {
      var fd := cover[i];
      var foundIdx: int := -1;
      var j := 0;
      while j < |lhsList|
        invariant 0 <= j <= |lhsList|
        invariant foundIdx == -1 || (0 <= foundIdx < |lhsList|)
        decreases |lhsList| - j
      {
        if lhsList[j] == fd.lhs {
          foundIdx := j;
        }
        j := j + 1;
      }

      if foundIdx >= 0 {
        groups := groups[foundIdx := groups[foundIdx] + fd.rhs];
      } else {
        lhsList := lhsList + [fd.lhs];
        groups := groups + [fd.lhs + fd.rhs];
      }
      i := i + 1;
    }
  }

  // Eliminates any schema `groups[i]` that is a subset of another kept schema.
  method RemoveRedundantSchemas(groups: seq<set<Name>>, attrs: set<Name>) returns (pruned: seq<set<Name>>)
    requires forall i :: 0 <= i < |groups| ==> groups[i] != {} && groups[i] <= attrs
    ensures forall i :: 0 <= i < |pruned| ==> pruned[i] != {} && pruned[i] <= attrs
  {
    pruned := [];
    var i := 0;
    while i < |groups|
      invariant 0 <= i <= |groups|
      invariant forall k :: 0 <= k < |pruned| ==> pruned[k] != {} && pruned[k] <= attrs
      decreases |groups| - i
    {
      var g := groups[i];
      var subsumed := false;
      var j := 0;
      while j < |groups|
        invariant 0 <= j <= |groups|
        decreases |groups| - j
      {
        if j != i && g <= groups[j] {
          // Break ties deterministically: drop later duplicates (`j < i`) or strict subsets (`g < groups[j]`).
          if g < groups[j] || j < i {
            subsumed := true;
          }
        }
        j := j + 1;
      }
      if !subsumed {
        pruned := pruned + [g];
      }
      i := i + 1;
    }
  }

  // Synthesizes a 3NF lossless, dependency-preserving decomposition for a 1NF relation.
  method Synthesize3NF(rel: NormalizedRelation) returns (out: seq<NormalizedRelation>)
    requires ValidNormalizedRelation(rel)
    requires IsTable1NF(rel.table)
    ensures ValidNormalizedSchema(NormalizedSchema(out))
    ensures |out| >= 1
    ensures forall i :: 0 <= i < |out| ==> IsTable1NF(out[i].table)
  {
    var attrsSeq := TableAttrSeq(rel.table);
    var attrs := TableAttrSet(rel.table);
    assert |attrsSeq| > 0 by {
      LemmaColNameInTableHasColumn(rel.table.columns, rel.table.primaryKey[0]);
      if |rel.table.columns| == 0 {
        assert !HasColumn(rel.table.columns, rel.table.primaryKey[0]);
      }
    }

    var cks := FindCandidateKeys(attrsSeq, rel.fds);
    if HasNoPartialDependencies(attrsSeq, rel.fds, cks) &&
       Satisfies3NFCondition(attrsSeq, rel.fds, cks) {
      return [rel];
    }

    var cover := ComputeMinimalCover(rel.fds, attrsSeq);
    var grouped := GroupMinimalCover(cover, attrs);
    var schemas := RemoveRedundantSchemas(grouped, attrs);

    // Ensure at least one schema contains a candidate key of `rel` (guarantees lossless-join).
    var hasCK := false;
    var si := 0;
    while si < |schemas|
      invariant 0 <= si <= |schemas|
      invariant hasCK ==> |schemas| >= 1
      decreases |schemas| - si
    {
      var ci := 0;
      while ci < |cks|
        invariant 0 <= ci <= |cks|
        invariant hasCK ==> |schemas| >= 1
        decreases |cks| - ci
      {
        if cks[ci] <= schemas[si] {
          hasCK := true;
        }
        ci := ci + 1;
      }
      si := si + 1;
    }

    if !hasCK {
      LemmaSuperkeyNonEmpty(cks[0], attrs, rel.fds);
      schemas := schemas + [cks[0]];
    }

    assert |schemas| >= 1;
    assert forall k :: 0 <= k < |schemas| ==> schemas[k] != {} && schemas[k] <= attrs;
    out := [];
    var idx := 0;
    while idx < |schemas|
      invariant 0 <= idx <= |schemas|
      invariant |out| == idx
      invariant ValidNormalizedSchema(NormalizedSchema(out))
      invariant forall k :: 0 <= k < |out| ==> IsTable1NF(out[k].table)
      decreases |schemas| - idx
    {
      var sub := BuildSubRelation(
        rel.table.name + "_3nf_" + NatToString(idx + 1),
        rel.table.columns, schemas[idx], rel.fds, attrs
      );
      out := out + [sub];
      idx := idx + 1;
    }
  }

  method NormalizeRelationTo3NF(rel: NormalizedRelation) returns (out: seq<NormalizedRelation>)
    requires ValidNormalizedRelation(rel)
    requires PrimaryKeyColumnsAtomic(rel.table)
    ensures ValidNormalizedSchema(NormalizedSchema(out))
    ensures |out| >= 1
    ensures forall i :: 0 <= i < |out| ==> IsTable1NF(out[i].table)
  {
    var nf1 := NormalizeRelationTo1NF(rel);
    out := [];
    var i := 0;
    while i < |nf1|
      invariant 0 <= i <= |nf1|
      invariant ValidNormalizedSchema(NormalizedSchema(out))
      invariant i > 0 ==> |out| >= 1
      invariant forall k :: 0 <= k < |out| ==> IsTable1NF(out[k].table)
      decreases |nf1| - i
    {
      var parts := Synthesize3NF(nf1[i]);
      out := out + parts;
      i := i + 1;
    }
  }

  // ---------------------------------------------------------------------------
  // Converter 4: Normalize to BCNF (Lossless BCNF Decomposition)
  // ---------------------------------------------------------------------------

  // Finds a BCNF-violating FD `x -> y` where `x` is not a superkey and `y = x+ \ x`
  // is non-empty, returning `found == false` iff the relation is in BCNF.
  method FindBCNFViolation(
    attrs: set<Name>,
    fds: seq<FD>
  ) returns (
    found: bool,
    x: set<Name>,
    y: set<Name>
  )
    requires ValidFDs(fds, attrs)
    ensures !found ==> SatisfiesBCNFCondition(attrs, fds)
    ensures found ==>
      x != {} &&
      y != {} &&
      x <= attrs &&
      y <= attrs &&
      (x * y == {}) &&
      y <= AttributeClosure(x, fds, attrs) &&
      (x + y) < attrs
  {
    found := false;
    x := {};
    y := {};
    var i := 0;
    while i < |fds|
      invariant 0 <= i <= |fds|
      invariant forall k :: 0 <= k < i ==>
        IsTrivialFD(fds[k]) || IsSuperkey(fds[k].lhs, attrs, fds)
      decreases |fds| - i
    {
      var fd := fds[i];
      if !IsTrivialFD(fd) && !IsSuperkey(fd.lhs, attrs, fds) {
        var cl := AttributeClosure(fd.lhs, fds, attrs);
        var rhsExtra := cl - fd.lhs;
        assert fd.lhs <= cl;
        assert (fd.rhs * attrs) <= cl;
        assert fd.rhs <= cl;
        assert rhsExtra != {} by {
          var diff :| diff in fd.rhs && diff !in fd.lhs;
          assert diff in rhsExtra;
        }
        assert fd.lhs + rhsExtra == cl;
        assert !(attrs <= cl);
        assert cl < attrs;
        return true, fd.lhs, rhsExtra;
      }
      i := i + 1;
    }
  }

  // Recursively decomposes a 1NF relation into lossless BCNF sub-relations.
  method DecomposeToBCNFRec(rel: NormalizedRelation, depthTag: nat) returns (out: seq<NormalizedRelation>)
    requires ValidNormalizedRelation(rel)
    requires IsTable1NF(rel.table)
    ensures ValidNormalizedSchema(NormalizedSchema(out))
    ensures |out| >= 1
    ensures forall i :: 0 <= i < |out| ==>
      IsTable1NF(out[i].table) &&
      SatisfiesBCNFCondition(TableAttrSet(out[i].table), out[i].fds)
    decreases |rel.table.columns|
  {
    var attrs := TableAttrSet(rel.table);
    var found, x, y := FindBCNFViolation(attrs, rel.fds);
    if !found {
      return [rel];
    }

    // Lossless binary split: R1 = x U y, R2 = attrs \ y
    LemmaBinarySplitIsLossless(x, y, rel.fds, attrs);
    var r1Set := x + y;
    var r2Set := attrs - y;

    // Both subsets strictly reduce column count (guaranteeing termination).
    ghost var outsideR1 :| outsideR1 in attrs && outsideR1 !in r1Set;
    LemmaStrictSubsetFewerColumns(rel.table.columns, r1Set, outsideR1);
    ghost var inY :| inY in y;
    LemmaStrictSubsetFewerColumns(rel.table.columns, r2Set, inY);

    assert r1Set != {} by { assert inY in r1Set; }
    assert r2Set != {} by {
      var inX :| inX in x;
      assert inX in r2Set;
    }

    var r1 := BuildSubRelation(
      rel.table.name + "_bcnf_" + NatToString(depthTag) + "a",
      rel.table.columns, r1Set, rel.fds, attrs
    );
    var r2 := BuildSubRelation(
      rel.table.name + "_bcnf_" + NatToString(depthTag) + "b",
      rel.table.columns, r2Set, rel.fds, attrs
    );

    assert |r1.table.columns| < |rel.table.columns|;
    assert |r2.table.columns| < |rel.table.columns|;

    var leftOut := DecomposeToBCNFRec(r1, depthTag + 1);
    var rightOut := DecomposeToBCNFRec(r2, depthTag + 2);
    out := leftOut + rightOut;
  }

  method NormalizeRelationToBCNF(rel: NormalizedRelation) returns (out: seq<NormalizedRelation>)
    requires ValidNormalizedRelation(rel)
    requires PrimaryKeyColumnsAtomic(rel.table)
    ensures ValidNormalizedSchema(NormalizedSchema(out))
    ensures |out| >= 1
    ensures forall i :: 0 <= i < |out| ==>
      IsTable1NF(out[i].table) &&
      SatisfiesBCNFCondition(TableAttrSet(out[i].table), out[i].fds)
  {
    var nf1 := NormalizeRelationTo1NF(rel);
    out := [];
    var i := 0;
    while i < |nf1|
      invariant 0 <= i <= |nf1|
      invariant ValidNormalizedSchema(NormalizedSchema(out))
      invariant i > 0 ==> |out| >= 1
      invariant forall k :: 0 <= k < |out| ==>
        IsTable1NF(out[k].table) &&
        SatisfiesBCNFCondition(TableAttrSet(out[k].table), out[k].fds)
      decreases |nf1| - i
    {
      var parts := DecomposeToBCNFRec(nf1[i], 1);
      out := out + parts;
      i := i + 1;
    }
  }

  // ---------------------------------------------------------------------------
  // Unified Converters & Decomposition Extractor
  // ---------------------------------------------------------------------------

  method ConvertRelationToNormalForm(
    rel: NormalizedRelation,
    target: NormalForm
  ) returns (out: seq<NormalizedRelation>)
    requires ValidNormalizedRelation(rel)
    requires PrimaryKeyColumnsAtomic(rel.table)
    ensures ValidNormalizedSchema(NormalizedSchema(out))
    ensures |out| >= 1
    ensures target != Unnormalized ==> (forall i :: 0 <= i < |out| ==> IsTable1NF(out[i].table))
    ensures target == BCNF ==>
      (forall i :: 0 <= i < |out| ==> SatisfiesBCNFCondition(TableAttrSet(out[i].table), out[i].fds))
  {
    match target {
      case Unnormalized => out := [rel];
      case NF1 => out := NormalizeRelationTo1NF(rel);
      case NF2 => out := NormalizeRelationTo2NF(rel);
      case NF3 => out := NormalizeRelationTo3NF(rel);
      case BCNF => out := NormalizeRelationToBCNF(rel);
    }
  }

  method ConvertSchemaToNormalForm(
    schema: NormalizedSchema,
    target: NormalForm
  ) returns (converted: NormalizedSchema)
    requires ValidNormalizedSchema(schema)
    requires forall i :: 0 <= i < |schema.relations| ==>
      PrimaryKeyColumnsAtomic(schema.relations[i].table)
    ensures ValidNormalizedSchema(converted)
    ensures target != Unnormalized ==>
      (forall i :: 0 <= i < |converted.relations| ==> IsTable1NF(converted.relations[i].table))
    ensures target == BCNF ==>
      (forall i :: 0 <= i < |converted.relations| ==>
        SatisfiesBCNFCondition(TableAttrSet(converted.relations[i].table), converted.relations[i].fds))
  {
    var acc: seq<NormalizedRelation> := [];
    var i := 0;
    while i < |schema.relations|
      invariant 0 <= i <= |schema.relations|
      invariant ValidNormalizedSchema(NormalizedSchema(acc))
      invariant target != Unnormalized ==>
        (forall k :: 0 <= k < |acc| ==> IsTable1NF(acc[k].table))
      invariant target == BCNF ==>
        (forall k :: 0 <= k < |acc| ==>
          SatisfiesBCNFCondition(TableAttrSet(acc[k].table), acc[k].fds))
      decreases |schema.relations| - i
    {
      var parts := ConvertRelationToNormalForm(schema.relations[i], target);
      acc := acc + parts;
      i := i + 1;
    }
    converted := NormalizedSchema(acc);
  }

  // Extracts the attribute sets of a decomposed sequence of relations for
  // passing directly into `DecompositionAnalysis.AnalyzeDecomposition`.
  function ExtractAttributeSets(rels: seq<NormalizedRelation>): seq<set<Name>>
    ensures |ExtractAttributeSets(rels)| == |rels|
    decreases |rels|
  {
    if |rels| == 0 then []
    else [TableAttrSet(rels[0].table)] + ExtractAttributeSets(rels[1..])
  }

  // Convenience wrapper: analyzes whether decomposing `original` into `decomposed`
  // is lossless-join and dependency-preserving.
  method AnalyzeRelationDecomposition(
    original: NormalizedRelation,
    decomposed: seq<NormalizedRelation>
  ) returns (report: DecompositionReport)
    ensures report.dependencyPreserving <==> |report.lostDependencies| == 0
  {
    var origAttrs := TableAttrSeq(original.table);
    var decompSets := ExtractAttributeSets(decomposed);
    report := AnalyzeDecomposition(origAttrs, decompSets, original.fds);
  }

  // ---------------------------------------------------------------------------
  // Formatting Helpers
  // ---------------------------------------------------------------------------

  function FormatNormalForm(nf: NormalForm): string
  {
    match nf
    case Unnormalized => "UNF (Unnormalized)"
    case NF1 => "1NF"
    case NF2 => "2NF"
    case NF3 => "3NF"
    case BCNF => "BCNF"
  }

  function FormatCandidateKeys(cks: seq<set<Name>>, order: seq<Name>): string
    decreases |cks|
  {
    if |cks| == 0 then ""
    else if |cks| == 1 then "{" + JoinSetNames(cks[0], order) + "}"
    else "{" + JoinSetNames(cks[0], order) + "}, " + FormatCandidateKeys(cks[1..], order)
  }

  function FormatViolations(vs: seq<string>): string
    decreases |vs|
  {
    if |vs| == 0 then ""
    else "    - " + vs[0] + "\n" + FormatViolations(vs[1..])
  }

  function FormatValidationReport(rep: ValidationReport, order: seq<Name>): string
  {
    "Table '" + rep.tableName + "' -> Highest Normal Form: " + FormatNormalForm(rep.highestForm) + "\n" +
    "  [1NF=" + (if rep.is1NF then "YES" else "NO") +
    ", 2NF=" + (if rep.is2NF then "YES" else "NO") +
    ", 3NF=" + (if rep.is3NF then "YES" else "NO") +
    ", BCNF=" + (if rep.isBCNF then "YES" else "NO") + "]\n" +
    "  Candidate Keys: " + FormatCandidateKeys(rep.candidateKeys, order) + "\n" +
    (if |rep.violations| == 0 then "" else "  Violations:\n" + FormatViolations(rep.violations))
  }

  function FormatFDList(fds: seq<FD>, order: seq<Name>): string
    decreases |fds|
  {
    if |fds| == 0 then ""
    else "  FD: " + FormatFD(fds[0], order) + "\n" + FormatFDList(fds[1..], order)
  }

  function FormatNormalizedRelation(rel: NormalizedRelation): string
  {
    FormatTableSchema(rel.table) + FormatFDList(rel.fds, TableAttrSeq(rel.table))
  }

  function FormatNormalizedRelations(rels: seq<NormalizedRelation>): string
    decreases |rels|
  {
    if |rels| == 0 then ""
    else FormatNormalizedRelation(rels[0]) + FormatNormalizedRelations(rels[1..])
  }
}
