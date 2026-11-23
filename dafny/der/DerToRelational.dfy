// DER -> Relational Model (RM) Converter.
//
// Standard ER-to-Relational mapping rules implemented and verified:
//   1. Entities:
//        Each `Entity` becomes a table with the same name, all its attributes
//        as columns, and the exact same Primary Key.
//   2. Aggregations:
//        Each `Aggregation` wrapping `(innerSource --[innerRelation]--> target)`
//        becomes a table with prefixed PKs of both endpoints, the relation's
//        attributes, the aggregation's own attributes, FKs to both endpoints,
//        and PK determined by `innerRelation.Kind()` (both PKs for N:M, N-side
//        PK for 1:N / N:1, source PK for 1:1).
//   3. Relations (not already materialized by an Aggregation):
//        - N:M (`KindManyToMany`): new join table named `rel.name` whose PK is
//          the union of both participating entities' prefixed PKs, plus `rel`'s
//          attributes and FKs to both endpoints.
//        - 1:N (`KindOneToMany`): propagates source's PK as an FK (plus `rel`'s
//          attributes) into the N-side (`rel.target`) table.
//        - N:1 (`KindManyToOne`): propagates target's PK as an FK (plus `rel`'s
//          attributes) into the N-side (`source`) table.
//        - 1:1 (`KindOneToOne`): propagates source's PK as an FK (plus `rel`'s
//          attributes) into the target (`rel.target`) table.

include "Types.dfy"
include "Model.dfy"
include "RelationalModel.dfy"

module DerToRelational {
  import opened DerTypes
  import opened DerModel
  import opened RelationalModel

  // ---------------------------------------------------------------------------
  // Attribute / Key projection helpers
  // ---------------------------------------------------------------------------

  function FilterKeyAttrs(attrs: seq<Attribute>): seq<Attribute>
    decreases |attrs|
  {
    if |attrs| == 0 then []
    else if attrs[0].isKey then [attrs[0]] + FilterKeyAttrs(attrs[1..])
    else FilterKeyAttrs(attrs[1..])
  }

  lemma LemmaHasKeyImpliesNonEmptyKeys(attrs: seq<Attribute>)
    requires HasKeyAttribute(attrs)
    ensures |FilterKeyAttrs(attrs)| > 0
    decreases |attrs|
  {
    if attrs[0].isKey {
      // Base case: attrs[0] is included in FilterKeyAttrs(attrs).
    } else {
      var idx :| 0 <= idx < |attrs| && attrs[idx].isKey;
      assert idx > 0 && attrs[1..][idx - 1].isKey;
      assert HasKeyAttribute(attrs[1..]);
      LemmaHasKeyImpliesNonEmptyKeys(attrs[1..]);
    }
  }

  function AttrsToColumns(attrs: seq<Attribute>): seq<Column>
    ensures |AttrsToColumns(attrs)| == |attrs|
    ensures forall i :: 0 <= i < |attrs| ==> AttrsToColumns(attrs)[i] == Column(attrs[i].name, attrs[i].attrType)
    decreases |attrs|
  {
    if |attrs| == 0 then []
    else [Column(attrs[0].name, attrs[0].attrType)] + AttrsToColumns(attrs[1..])
  }

  function AttrNames(attrs: seq<Attribute>): seq<Name>
    ensures |AttrNames(attrs)| == |attrs|
    ensures forall i :: 0 <= i < |attrs| ==> AttrNames(attrs)[i] == attrs[i].name
    decreases |attrs|
  {
    if |attrs| == 0 then []
    else [attrs[0].name] + AttrNames(attrs[1..])
  }

  function PrefixedAttrs(prefix: Name, attrs: seq<Attribute>): seq<Attribute>
    ensures |PrefixedAttrs(prefix, attrs)| == |attrs|
    ensures forall i :: 0 <= i < |attrs| ==>
      PrefixedAttrs(prefix, attrs)[i] == Attribute(prefix + "_" + attrs[i].name, attrs[i].attrType, attrs[i].isKey)
    decreases |attrs|
  {
    if |attrs| == 0 then []
    else [Attribute(prefix + "_" + attrs[0].name, attrs[0].attrType, attrs[0].isKey)] +
         PrefixedAttrs(prefix, attrs[1..])
  }

  lemma LemmaFilterKeyAttrsInColumns(attrs: seq<Attribute>)
    ensures var keys := FilterKeyAttrs(attrs);
      var cols := AttrsToColumns(attrs);
      forall i :: 0 <= i < |keys| ==> HasColumn(cols, keys[i].name)
    decreases |attrs|
  {
    if |attrs| > 0 {
      LemmaFilterKeyAttrsInColumns(attrs[1..]);
      var restCols := AttrsToColumns(attrs[1..]);
      var allCols := AttrsToColumns(attrs);
      var keys := FilterKeyAttrs(attrs);
      forall i | 0 <= i < |keys|
        ensures HasColumn(allCols, keys[i].name)
      {
        if attrs[0].isKey && i == 0 {
          assert allCols[0].name == keys[0].name;
        } else {
          var restIdx := if attrs[0].isKey then i - 1 else i;
          assert HasColumn(restCols, keys[i].name);
          var cIdx :| 0 <= cIdx < |restCols| && restCols[cIdx].name == keys[i].name;
          assert allCols[cIdx + 1].name == keys[i].name;
        }
      }
    }
  }

  lemma LemmaAttrNamesInColumns(attrs: seq<Attribute>)
    ensures var cols := AttrsToColumns(attrs);
      var names := AttrNames(attrs);
      forall i :: 0 <= i < |names| ==> HasColumn(cols, names[i])
  {
    var cols := AttrsToColumns(attrs);
    var names := AttrNames(attrs);
    forall i | 0 <= i < |names|
      ensures HasColumn(cols, names[i])
    {
      assert cols[i].name == names[i];
    }
  }

  // Computes the primary key attributes of any EntityElement (Entity or
  // Aggregation wrapping Entity endpoints).
  function ElementKeyAttrs(elem: EntityElement): seq<Attribute>
    reads elem,
          if elem.AggregationDetails().AggregationOf? then
            {elem.AggregationDetails().innerSource, elem.AggregationDetails().innerRelation}
          else
            {},
          if elem.AggregationDetails().AggregationOf? then
            {elem.AggregationDetails().innerRelation.target}
          else
            {}
  {
    match elem.AggregationDetails()
    case NotAnAggregation =>
      FilterKeyAttrs(elem.attributes)
    case AggregationOf(src, rel) =>
      var srcKeys := FilterKeyAttrs(src.attributes);
      var dstKeys := FilterKeyAttrs(rel.target.attributes);
      var pSrc := PrefixedAttrs(src.name, srcKeys);
      var pDst := PrefixedAttrs(rel.target.name, dstKeys);
      match rel.Kind()
      case KindManyToMany => pSrc + pDst
      case KindOneToMany => pDst
      case KindManyToOne => pSrc
      case KindOneToOne => pSrc
  }

  // Framing helper: since `ElementKeyAttrs` only reads `const` fields on `elem`
  // (and on an aggregation's inner endpoints/relation), it is preserved across
  // any heap transition that does not modify those objects.
  twostate lemma LemmaElementKeyAttrsUnchanged(elem: EntityElement)
    requires unchanged(elem)
    requires old(elem.AggregationDetails()).AggregationOf? ==>
      var d := old(elem.AggregationDetails());
      unchanged(d.innerSource) &&
      unchanged(d.innerRelation) &&
      unchanged(d.innerRelation.target)
    ensures ElementKeyAttrs(elem) == old(ElementKeyAttrs(elem))
  {
    assert elem.AggregationDetails() == old(elem.AggregationDetails());
    match elem.AggregationDetails() {
      case NotAnAggregation =>
      case AggregationOf(src, rel) =>
        assert rel.Kind() == old(rel.Kind());
    }
  }

  // Precondition predicate guaranteeing every EntityElement in `diagram` is
  // valid and has a well-defined non-empty primary key.
  // Marked `opaque` so loop-heavy conversion methods don't pay the cost of
  // unfolding diagram-wide quantifiers at every step.
  opaque ghost predicate ConvertibleDiagram(diagram: DerDiagram)
    reads diagram, diagram.elements,
          set e, o | e in diagram.elements && o in e.Repr :: o
  {
    diagram.Valid() &&
    (forall i :: 0 <= i < |diagram.elements| ==>
      diagram as object !in diagram.elements[i].Repr &&
      (forall j :: 0 <= j < |diagram.elements| && j != i ==>
        diagram.elements[j] as object !in diagram.elements[i].Repr)) &&
    (forall i :: 0 <= i < |diagram.elements| ==>
      var elem := diagram.elements[i];
      elem.Valid() &&
      match elem.AggregationDetails() {
        case NotAnAggregation =>
          HasKeyAttribute(elem.attributes)
        case AggregationOf(src, rel) =>
          src in diagram.elements &&
          rel in elem.Repr &&
          rel as object != elem as object &&
          rel.ValidRelation() &&
          rel.target in diagram.elements &&
          src.AggregationDetails().NotAnAggregation? &&
          rel.target.AggregationDetails().NotAnAggregation?
      }) &&
    (forall i :: 0 <= i < |diagram.elements| ==>
      forall r :: r in diagram.elements[i].relations ==>
        r.target in diagram.elements)
  }

  // ---------------------------------------------------------------------------
  // Incremental `ConvertibleDiagram` builders (callers never need to reveal
  // `ConvertibleDiagram` when assembling a DER diagram step by step)
  // ---------------------------------------------------------------------------

  lemma LemmaEmptyDiagramConvertible(diagram: DerDiagram)
    requires diagram.Valid()
    requires diagram.elements == []
    ensures ConvertibleDiagram(diagram)
  {
    reveal ConvertibleDiagram();
  }

  method AddConvertibleEntity(diagram: DerDiagram, e: Entity)
    requires ConvertibleDiagram(diagram)
    requires e.Valid()
    requires e.relations == []
    requires e.Repr == {e}
    requires e as object != diagram as object
    requires forall i :: 0 <= i < |diagram.elements| ==>
      diagram.elements[i] != e &&
      diagram.elements[i].name != e.name &&
      e as object !in diagram.elements[i].Repr
    modifies diagram
    ensures ConvertibleDiagram(diagram)
    ensures diagram.elements == old(diagram.elements) + [e]
  {
    reveal ConvertibleDiagram();
    diagram.AddElement(e);
  }

  method AddConvertibleAggregation(diagram: DerDiagram, agg: Aggregation)
    requires ConvertibleDiagram(diagram)
    requires agg.Valid()
    requires agg.relations == []
    requires agg.Repr == {agg, agg.innerRelation}
    requires agg as object != diagram as object
    requires agg.innerRelation as object != diagram as object
    requires agg.innerSource in diagram.elements
    requires agg.innerRelation.target in diagram.elements
    requires agg.innerSource.AggregationDetails().NotAnAggregation?
    requires agg.innerRelation.target.AggregationDetails().NotAnAggregation?
    requires forall i :: 0 <= i < |diagram.elements| ==>
      diagram.elements[i] != agg &&
      diagram.elements[i].name != agg.name &&
      agg as object !in diagram.elements[i].Repr &&
      diagram.elements[i] as object != agg.innerRelation as object
    modifies diagram
    ensures ConvertibleDiagram(diagram)
    ensures diagram.elements == old(diagram.elements) + [agg]
  {
    reveal ConvertibleDiagram();
    diagram.AddElement(agg);
  }

  method LinkConvertibleRelation(
    diagram: DerDiagram,
    source: EntityElement,
    rel: Relation
  )
    requires ConvertibleDiagram(diagram)
    requires source in diagram.elements && rel.target in diagram.elements
    requires rel.ValidRelation()
    requires rel as object != source as object
    requires rel as object != diagram as object
    requires forall i :: 0 <= i < |diagram.elements| ==>
      diagram.elements[i] as object != rel as object
    requires forall i :: 0 <= i < |source.relations| ==>
      DistinctRelations(source.relations[i], rel)
    modifies source
    ensures ConvertibleDiagram(diagram)
    ensures source.Valid()
    ensures source.relations == old(source.relations) + [rel]
    ensures source.Repr == old(source.Repr) + {rel}
    ensures source.AggregationDetails() == old(source.AggregationDetails())
  {
    reveal ConvertibleDiagram();
    ghost var sIdx :| 0 <= sIdx < |diagram.elements| && diagram.elements[sIdx] == source;
    assert diagram.elements[sIdx].Valid();
    forall i | 0 <= i < |diagram.elements| && i != sIdx
      ensures source as object !in diagram.elements[i].Repr
    {
      assert diagram.elements[sIdx] as object !in diagram.elements[i].Repr;
    }
    diagram.LinkRelation(source, rel);
    forall i | 0 <= i < |diagram.elements|
      ensures diagram.elements[i].Valid()
      ensures diagram.elements[i].AggregationDetails() == old(diagram.elements[i].AggregationDetails())
    {
      if i == sIdx {
        assert diagram.elements[i] == source;
      } else {
        assert diagram.elements[i] != source;
      }
    }
  }

  // Extracts concrete element validity, non-empty names, and non-empty primary
  // keys from `ConvertibleDiagram` using explicit index witnesses so table
  // builders never have to unfold diagram-wide quantifiers.
  lemma LemmaConvertibleElementFacts(diagram: DerDiagram, elem: EntityElement)
    requires ConvertibleDiagram(diagram)
    requires elem in diagram.elements
    ensures elem.Valid()
    ensures elem.name != ""
    ensures |ElementKeyAttrs(elem)| > 0
    ensures elem.AggregationDetails().NotAnAggregation? ==>
      HasKeyAttribute(elem.attributes)
    ensures elem.AggregationDetails().AggregationOf? ==>
      var d := elem.AggregationDetails();
      d.innerSource in diagram.elements &&
      d.innerRelation in elem.Repr &&
      d.innerRelation.ValidRelation() &&
      d.innerRelation.name != "" &&
      d.innerRelation.target in diagram.elements &&
      d.innerSource.Valid() &&
      d.innerSource.name != "" &&
      d.innerSource.AggregationDetails().NotAnAggregation? &&
      HasKeyAttribute(d.innerSource.attributes) &&
      d.innerRelation.target.Valid() &&
      d.innerRelation.target.name != "" &&
      d.innerRelation.target.AggregationDetails().NotAnAggregation? &&
      HasKeyAttribute(d.innerRelation.target.attributes)
  {
    reveal ConvertibleDiagram();
    var i :| 0 <= i < |diagram.elements| && diagram.elements[i] == elem;
    assert diagram.elements[i].Valid();
    match elem.AggregationDetails() {
      case NotAnAggregation =>
        LemmaHasKeyImpliesNonEmptyKeys(elem.attributes);
      case AggregationOf(src, rel) =>
        var j :| 0 <= j < |diagram.elements| && diagram.elements[j] == src;
        var k :| 0 <= k < |diagram.elements| && diagram.elements[k] == rel.target;
        assert diagram.elements[j].Valid();
        assert diagram.elements[k].Valid();
        LemmaHasKeyImpliesNonEmptyKeys(src.attributes);
        LemmaHasKeyImpliesNonEmptyKeys(rel.target.attributes);
    }
  }

  // Extracts concrete relation and target facts for any relation attached to
  // an element of a `ConvertibleDiagram`.
  lemma LemmaConvertibleRelationFacts(
    diagram: DerDiagram,
    src: EntityElement,
    rel: Relation
  )
    requires ConvertibleDiagram(diagram)
    requires src in diagram.elements
    requires rel in src.relations
    ensures rel.ValidRelation()
    ensures rel.name != ""
    ensures rel.target in diagram.elements
    ensures rel.target.name != ""
    ensures |ElementKeyAttrs(rel.target)| > 0
  {
    reveal ConvertibleDiagram();
    var sIdx :| 0 <= sIdx < |diagram.elements| && diagram.elements[sIdx] == src;
    assert diagram.elements[sIdx].Valid();
    var rIdx :| 0 <= rIdx < |src.relations| && src.relations[rIdx] == rel;
    assert src.relations[rIdx].ValidRelation();
    assert rel.target in diagram.elements;
    LemmaConvertibleElementFacts(diagram, rel.target);
  }

  // Checks whether `rel` is already materialized by an `Aggregation` in `elements`.
  predicate IsAggregatedRelation(elements: seq<EntityElement>, rel: Relation)
    reads elements
  {
    exists i :: 0 <= i < |elements| &&
      elements[i].AggregationDetails().AggregationOf? &&
      elements[i].AggregationDetails().innerRelation == rel
  }

  // ---------------------------------------------------------------------------
  // Modular Table Builders (one per ER-to-RM rule)
  // ---------------------------------------------------------------------------

  // Rule 1: Entity -> Table with exact same name and exact same PK.
  method BuildEntityTable(e: EntityElement) returns (t: TableSchema)
    requires e.name != ""
    requires HasKeyAttribute(e.attributes)
    ensures ValidTable(t)
    ensures t.name == e.name
    ensures t.primaryKey == AttrNames(FilterKeyAttrs(e.attributes))
  {
    var keyAttrs := FilterKeyAttrs(e.attributes);
    LemmaHasKeyImpliesNonEmptyKeys(e.attributes);
    LemmaFilterKeyAttrsInColumns(e.attributes);

    var cols := AttrsToColumns(e.attributes);
    var pk := AttrNames(keyAttrs);
    t := TableSchema(e.name, cols, pk, []);
  }

  // Rule 2: Aggregation -> Table composing innerSource PK, target PK,
  // innerRelation attributes, and aggregation's own attributes.
  method BuildAggregationTable(agg: EntityElement) returns (t: TableSchema)
    requires agg.name != ""
    requires agg.AggregationDetails().AggregationOf?
    requires var d := agg.AggregationDetails();
      d.innerSource.name != "" &&
      d.innerRelation.target.name != "" &&
      HasKeyAttribute(d.innerSource.attributes) &&
      HasKeyAttribute(d.innerRelation.target.attributes)
    ensures ValidTable(t)
    ensures t.name == agg.name
    ensures t.primaryKey == AttrNames(ElementKeyAttrs(agg))
  {
    var details := agg.AggregationDetails();
    var src := details.innerSource;
    var rel := details.innerRelation;
    var dst := rel.target;
    LemmaHasKeyImpliesNonEmptyKeys(src.attributes);
    LemmaHasKeyImpliesNonEmptyKeys(dst.attributes);

    var srcKeys := FilterKeyAttrs(src.attributes);
    var dstKeys := FilterKeyAttrs(dst.attributes);
    var pSrcAttrs := PrefixedAttrs(src.name, srcKeys);
    var pDstAttrs := PrefixedAttrs(dst.name, dstKeys);

    var pSrcCols := AttrsToColumns(pSrcAttrs);
    var pDstCols := AttrsToColumns(pDstAttrs);
    var relCols := AttrsToColumns(rel.attributes);
    var ownCols := AttrsToColumns(agg.attributes);
    var allCols := pSrcCols + pDstCols + relCols + ownCols;

    var pSrcNames := AttrNames(pSrcAttrs);
    var pDstNames := AttrNames(pDstAttrs);
    var srcRefNames := AttrNames(srcKeys);
    var dstRefNames := AttrNames(dstKeys);

    LemmaAttrNamesInColumns(pSrcAttrs);
    LemmaAttrNamesInColumns(pDstAttrs);

    forall i | 0 <= i < |pSrcNames|
      ensures HasColumn(allCols, pSrcNames[i])
    {
      LemmaHasColumnLeft(pSrcCols, pDstCols + relCols + ownCols, pSrcNames[i]);
      assert pSrcCols + (pDstCols + relCols + ownCols) == allCols;
    }

    forall i | 0 <= i < |pDstNames|
      ensures HasColumn(allCols, pDstNames[i])
    {
      LemmaHasColumnRight(pSrcCols, pDstCols, pDstNames[i]);
      LemmaHasColumnLeft(pSrcCols + pDstCols, relCols + ownCols, pDstNames[i]);
      assert (pSrcCols + pDstCols) + (relCols + ownCols) == allCols;
    }

    var pk := AttrNames(ElementKeyAttrs(agg));
    forall i | 0 <= i < |pk|
      ensures HasColumn(allCols, pk[i])
    {
      match rel.Kind() {
        case KindManyToMany =>
          assert ElementKeyAttrs(agg) == pSrcAttrs + pDstAttrs;
          if i < |pSrcAttrs| {
            assert pk[i] == pSrcNames[i];
          } else {
            assert pk[i] == pDstNames[i - |pSrcAttrs|];
          }
        case KindOneToMany =>
          assert pk[i] == pDstNames[i];
        case KindManyToOne =>
          assert pk[i] == pSrcNames[i];
        case KindOneToOne =>
          assert pk[i] == pSrcNames[i];
      }
    }

    var fkSrc := ForeignKey(pSrcNames, src.name, srcRefNames);
    var fkDst := ForeignKey(pDstNames, dst.name, dstRefNames);
    assert ValidForeignKey(fkSrc, allCols);
    assert ValidForeignKey(fkDst, allCols);
    t := TableSchema(agg.name, allCols, pk, [fkSrc, fkDst]);
    assert t.name != "";
    assert |t.primaryKey| > 0;
  }

  // Rule 3a: N:M Relation -> Join Table whose PK is ALL PKs of both endpoints.
  method BuildManyToManyTable(
    src: EntityElement,
    rel: Relation
  ) returns (t: TableSchema)
    requires src.name != ""
    requires rel.name != ""
    requires rel.target.name != ""
    requires |ElementKeyAttrs(src)| > 0
    requires |ElementKeyAttrs(rel.target)| > 0
    ensures ValidTable(t)
    ensures t.name == rel.name
    ensures t.primaryKey ==
      AttrNames(PrefixedAttrs(src.name, ElementKeyAttrs(src))) +
      AttrNames(PrefixedAttrs(rel.target.name, ElementKeyAttrs(rel.target)))
  {
    var dst := rel.target;
    var srcKeys := ElementKeyAttrs(src);
    var dstKeys := ElementKeyAttrs(dst);
    var pSrcAttrs := PrefixedAttrs(src.name, srcKeys);
    var pDstAttrs := PrefixedAttrs(dst.name, dstKeys);

    var pSrcCols := AttrsToColumns(pSrcAttrs);
    var pDstCols := AttrsToColumns(pDstAttrs);
    var relCols := AttrsToColumns(rel.attributes);
    var allCols := pSrcCols + pDstCols + relCols;

    var pSrcNames := AttrNames(pSrcAttrs);
    var pDstNames := AttrNames(pDstAttrs);
    var pk := pSrcNames + pDstNames;

    LemmaAttrNamesInColumns(pSrcAttrs);
    LemmaAttrNamesInColumns(pDstAttrs);

    forall i | 0 <= i < |pSrcNames|
      ensures HasColumn(allCols, pSrcNames[i])
    {
      LemmaHasColumnLeft(pSrcCols, pDstCols + relCols, pSrcNames[i]);
      assert pSrcCols + (pDstCols + relCols) == allCols;
    }

    forall i | 0 <= i < |pDstNames|
      ensures HasColumn(allCols, pDstNames[i])
    {
      LemmaHasColumnRight(pSrcCols, pDstCols, pDstNames[i]);
      LemmaHasColumnLeft(pSrcCols + pDstCols, relCols, pDstNames[i]);
      assert (pSrcCols + pDstCols) + relCols == allCols;
    }

    forall i | 0 <= i < |pk|
      ensures HasColumn(allCols, pk[i])
    {
      if i < |pSrcNames| {
        assert pk[i] == pSrcNames[i];
      } else {
        assert pk[i] == pDstNames[i - |pSrcNames|];
      }
    }

    var fkSrc := ForeignKey(pSrcNames, src.name, AttrNames(srcKeys));
    var fkDst := ForeignKey(pDstNames, dst.name, AttrNames(dstKeys));
    assert ValidForeignKey(fkSrc, allCols);
    assert ValidForeignKey(fkDst, allCols);
    t := TableSchema(rel.name, allCols, pk, [fkSrc, fkDst]);
    assert t.name != "";
    assert |t.primaryKey| > 0;
  }

  // Rule 3b/3c/3d: Appends an FK (plus relation attributes) onto an existing
  // table while preserving its name, primary key, and `ValidRelationalSchema`.
  method AppendForeignKeyToTable(
    tables: seq<TableSchema>,
    hostTableName: Name,
    refTableName: Name,
    refKeyAttrs: seq<Attribute>,
    relAttrs: seq<Attribute>
  ) returns (updated: seq<TableSchema>)
    requires ValidRelationalSchema(RelationalSchema(tables))
    requires refTableName != ""
    requires |refKeyAttrs| > 0
    ensures ValidRelationalSchema(RelationalSchema(updated))
    ensures |updated| == |tables|
    ensures forall i :: 0 <= i < |tables| ==>
      updated[i].name == tables[i].name &&
      updated[i].primaryKey == tables[i].primaryKey
  {
    var pRefAttrs := PrefixedAttrs(refTableName, refKeyAttrs);
    var fkCols := AttrsToColumns(pRefAttrs);
    var extraCols := AttrsToColumns(relAttrs);
    var fkNames := AttrNames(pRefAttrs);
    var refNames := AttrNames(refKeyAttrs);
    var newFk := ForeignKey(fkNames, refTableName, refNames);

    LemmaAttrNamesInColumns(pRefAttrs);

    updated := [];
    var i := 0;
    while i < |tables|
      invariant 0 <= i <= |tables|
      invariant |updated| == i
      invariant forall k :: 0 <= k < i ==> ValidTable(updated[k])
      invariant forall k :: 0 <= k < i ==>
        updated[k].name == tables[k].name &&
        updated[k].primaryKey == tables[k].primaryKey
      decreases |tables| - i
    {
      var cur := tables[i];
      if cur.name == hostTableName {
        var addedCols := fkCols + extraCols;
        var newCols := cur.columns + addedCols;

        forall p | 0 <= p < |cur.primaryKey|
          ensures HasColumn(newCols, cur.primaryKey[p])
        {
          LemmaHasColumnLeft(cur.columns, addedCols, cur.primaryKey[p]);
        }

        forall f | 0 <= f < |cur.foreignKeys|
          ensures ValidForeignKey(cur.foreignKeys[f], newCols)
        {
          LemmaAppendColumnsPreservesFK(cur.foreignKeys[f], cur.columns, addedCols);
        }

        forall c | 0 <= c < |fkNames|
          ensures HasColumn(newCols, fkNames[c])
        {
          LemmaHasColumnLeft(fkCols, extraCols, fkNames[c]);
          LemmaHasColumnRight(cur.columns, addedCols, fkNames[c]);
        }

        var nextTable := TableSchema(cur.name, newCols, cur.primaryKey, cur.foreignKeys + [newFk]);
        assert ValidTable(nextTable);
        updated := updated + [nextTable];
      } else {
        updated := updated + [cur];
      }
      i := i + 1;
    }
  }

  // ---------------------------------------------------------------------------
  // Modular Conversion Passes (split to keep verification fast)
  // ---------------------------------------------------------------------------

  // Pass 1 & 2: Create one base table for each Entity and each Aggregation.
  method BuildBaseTables(diagram: DerDiagram) returns (tables: seq<TableSchema>)
    requires ConvertibleDiagram(diagram)
    ensures |tables| == |diagram.elements|
    ensures ValidRelationalSchema(RelationalSchema(tables))
    ensures forall k :: 0 <= k < |diagram.elements| ==>
      tables[k].name == diagram.elements[k].name &&
      tables[k].primaryKey == AttrNames(ElementKeyAttrs(diagram.elements[k]))
  {
    tables := [];
    var i := 0;
    while i < |diagram.elements|
      invariant 0 <= i <= |diagram.elements|
      invariant |tables| == i
      invariant ValidRelationalSchema(RelationalSchema(tables))
      invariant forall k :: 0 <= k < i ==>
        tables[k].name == diagram.elements[k].name &&
        tables[k].primaryKey == AttrNames(old(ElementKeyAttrs(diagram.elements[k])))
      decreases |diagram.elements| - i
    {
      var elem := diagram.elements[i];
      LemmaConvertibleElementFacts(diagram, elem);
      var tbl: TableSchema;
      if elem.AggregationDetails().NotAnAggregation? {
        tbl := BuildEntityTable(elem);
        assert elem.AggregationDetails().NotAnAggregation?;
        assert tbl.primaryKey == AttrNames(ElementKeyAttrs(elem));
      } else {
        tbl := BuildAggregationTable(elem);
      }
      LemmaElementKeyAttrsUnchanged(elem);
      assert elem == old(diagram.elements)[i];
      tables := tables + [tbl];
      i := i + 1;
    }

    forall k | 0 <= k < |diagram.elements|
      ensures tables[k].primaryKey == AttrNames(ElementKeyAttrs(diagram.elements[k]))
    {
      var elem := diagram.elements[k];
      LemmaConvertibleElementFacts(diagram, elem);
      assert elem.AggregationDetails() == old(elem.AggregationDetails());
      if elem.AggregationDetails().AggregationOf? {
        var d := elem.AggregationDetails();
        assert d.innerSource in old(diagram.elements);
        assert d.innerRelation in old(elem.Repr);
        assert d.innerRelation.target in old(diagram.elements);
      }
      LemmaElementKeyAttrsUnchanged(elem);
    }
  }

  // Pass 3a: Convert one attached relation (either adding an N:M join table or
  // propagating an FK into the appropriate host table).
  method ApplySingleRelation(
    diagram: DerDiagram,
    tables: seq<TableSchema>,
    src: EntityElement,
    rel: Relation
  ) returns (updated: seq<TableSchema>)
    requires ConvertibleDiagram(diagram)
    requires ValidRelationalSchema(RelationalSchema(tables))
    requires src in diagram.elements && rel in src.relations
    ensures ValidRelationalSchema(RelationalSchema(updated))
    ensures |updated| >= |tables|
    ensures forall k :: 0 <= k < |tables| ==>
      updated[k].name == tables[k].name &&
      updated[k].primaryKey == tables[k].primaryKey
  {
    LemmaConvertibleElementFacts(diagram, src);
    LemmaConvertibleRelationFacts(diagram, src, rel);
    updated := tables;
    if !IsAggregatedRelation(diagram.elements, rel) {
      match rel.Kind() {
        case KindManyToMany => {
          var joinTable := BuildManyToManyTable(src, rel);
          updated := tables + [joinTable];
        }
        case KindOneToMany => {
          updated := AppendForeignKeyToTable(
            tables, rel.target.name, src.name, ElementKeyAttrs(src), rel.attributes
          );
        }
        case KindManyToOne => {
          updated := AppendForeignKeyToTable(
            tables, src.name, rel.target.name, ElementKeyAttrs(rel.target), rel.attributes
          );
        }
        case KindOneToOne => {
          updated := AppendForeignKeyToTable(
            tables, rel.target.name, src.name, ElementKeyAttrs(src), rel.attributes
          );
        }
      }
    }
  }

  // Pass 3b: Convert every relation attached to a single EntityElement.
  method ApplyElementRelations(
    diagram: DerDiagram,
    tables: seq<TableSchema>,
    src: EntityElement
  ) returns (updated: seq<TableSchema>)
    requires ConvertibleDiagram(diagram)
    requires ValidRelationalSchema(RelationalSchema(tables))
    requires src in diagram.elements
    ensures ValidRelationalSchema(RelationalSchema(updated))
    ensures |updated| >= |tables|
    ensures forall k :: 0 <= k < |tables| ==>
      updated[k].name == tables[k].name &&
      updated[k].primaryKey == tables[k].primaryKey
  {
    updated := tables;
    var rIdx := 0;
    while rIdx < |src.relations|
      invariant 0 <= rIdx <= |src.relations|
      invariant ValidRelationalSchema(RelationalSchema(updated))
      invariant |updated| >= |tables|
      invariant forall k :: 0 <= k < |tables| ==>
        updated[k].name == tables[k].name &&
        updated[k].primaryKey == tables[k].primaryKey
      decreases |src.relations| - rIdx
    {
      var rel := src.relations[rIdx];
      ghost var prev := updated;
      updated := ApplySingleRelation(diagram, updated, src, rel);
      forall k | 0 <= k < |tables|
        ensures updated[k].name == tables[k].name
        ensures updated[k].primaryKey == tables[k].primaryKey
      {
        assert updated[k].name == prev[k].name;
        assert prev[k].name == tables[k].name;
        assert updated[k].primaryKey == prev[k].primaryKey;
        assert prev[k].primaryKey == tables[k].primaryKey;
      }
      rIdx := rIdx + 1;
    }
  }

  // ---------------------------------------------------------------------------
  // Main Converter: DER -> RelationalSchema
  // ---------------------------------------------------------------------------

  method ConvertDerToRelational(diagram: DerDiagram) returns (rm: RelationalSchema)
    requires ConvertibleDiagram(diagram)
    ensures ValidRelationalSchema(rm)
    // Every Entity and Aggregation in the DER produces a table with the same
    // name and primary key.
    ensures forall i :: 0 <= i < |diagram.elements| ==>
      HasTable(rm, diagram.elements[i].name) &&
      exists k :: 0 <= k < |rm.tables| &&
        rm.tables[k].name == diagram.elements[i].name &&
        rm.tables[k].primaryKey == AttrNames(ElementKeyAttrs(diagram.elements[i]))
  {
    var baseTables := BuildBaseTables(diagram);
    label AfterBase:
    var tables := baseTables;

    var eIdx := 0;
    while eIdx < |diagram.elements|
      invariant 0 <= eIdx <= |diagram.elements|
      invariant |tables| >= |baseTables|
      invariant ValidRelationalSchema(RelationalSchema(tables))
      invariant forall k :: 0 <= k < |baseTables| ==>
        tables[k].name == baseTables[k].name &&
        tables[k].primaryKey == baseTables[k].primaryKey
      decreases |diagram.elements| - eIdx
    {
      ghost var prev := tables;
      tables := ApplyElementRelations(diagram, tables, diagram.elements[eIdx]);
      forall k | 0 <= k < |baseTables|
        ensures tables[k].name == baseTables[k].name
        ensures tables[k].primaryKey == baseTables[k].primaryKey
      {
        assert tables[k].name == prev[k].name;
        assert prev[k].name == baseTables[k].name;
        assert tables[k].primaryKey == prev[k].primaryKey;
        assert prev[k].primaryKey == baseTables[k].primaryKey;
      }
      eIdx := eIdx + 1;
    }

    rm := RelationalSchema(tables);
    forall i | 0 <= i < |diagram.elements|
      ensures HasTable(rm, diagram.elements[i].name)
      ensures exists k :: 0 <= k < |rm.tables| &&
        rm.tables[k].name == diagram.elements[i].name &&
        rm.tables[k].primaryKey == AttrNames(ElementKeyAttrs(diagram.elements[i]))
    {
      var elem := diagram.elements[i];
      LemmaConvertibleElementFacts(diagram, elem);
      assert elem.AggregationDetails() == old@AfterBase(elem.AggregationDetails());
      if elem.AggregationDetails().AggregationOf? {
        var d := elem.AggregationDetails();
        assert d.innerSource in old@AfterBase(diagram.elements);
        assert d.innerRelation in old@AfterBase(elem.Repr);
        assert d.innerRelation.target in old@AfterBase(diagram.elements);
      }
      LemmaElementKeyAttrsUnchanged@AfterBase(elem);
      assert baseTables[i].name == elem.name;
      assert baseTables[i].primaryKey == AttrNames(old@AfterBase(ElementKeyAttrs(elem)));
      assert rm.tables[i].name == baseTables[i].name;
      assert rm.tables[i].primaryKey == baseTables[i].primaryKey;
    }
  }
}
