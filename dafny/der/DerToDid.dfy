// DER -> DID (Document Instance Diagram) Converter.
//
// Converts a verified `DerDiagram` + customizable `DidConfig` into a
// hierarchical NoSQL `DidDatabase` (and Mongo-style XML):
//   - Entities & Aggregations become document collections (filtered or ordered
//     by `config.rootCollectionNames` if specified).
//   - Attributes become scalar `_id`/key fields or native `<ArrayField>`s
//     (for `AttrMultiValued`).
//   - Relations are materialized according to `config.modeOverrides` (or
//     `ModeAuto` defaults):
//       * 1:1 (`KindOneToOne`)   -> Embedded sub-document (or Reference)
//       * 1:N (`KindOneToMany`)  -> Embedded array of sub-documents (or ReferenceArray)
//       * N:1 (`KindManyToOne`)  -> DocumentReference to the 1-side collection (or Embedded)
//       * N:M (`KindManyToMany`) -> ReferenceArray with relation attributes (or EmbeddedArray)
//   - Aggregations compose their inner relationship endpoints + attributes and
//     nest their outer relations (e.g., `Cursada` embeds `EvaluadaPor -> Examen`).

include "Types.dfy"
include "Model.dfy"
include "RelationalModel.dfy"
include "DerToRelational.dfy"
include "DidModel.dfy"

module DerToDid {
  import opened DerTypes
  import opened DerModel
  import opened RelationalModel
  import opened DerToRelational
  import opened DidModel

  // ---------------------------------------------------------------------------
  // Mode Resolution & Attribute Mapping Helpers
  // ---------------------------------------------------------------------------

  function EffectiveRelationMode(
    cfg: DidConfig,
    relName: Name,
    kind: RelationKind
  ): ( bool, bool ) // returns (shouldEmbed, isArray)
  {
    var isArray := (kind == KindOneToMany || kind == KindManyToMany);
    var mode :=
      if relName in cfg.modeOverrides then cfg.modeOverrides[relName]
      else ModeAuto;
    var shouldEmbed :=
      match mode
      case ModeEmbed => true
      case ModeReference => false
      case ModeAuto => (kind == KindOneToOne || kind == KindOneToMany);
    (shouldEmbed, isArray)
  }

  function AttrToDidField(a: Attribute): DidField
    requires a.name != ""
    ensures ValidDidField(AttrToDidField(a))
  {
    match a.attrType
    case AttrMultiValued(inner) =>
      DidMultiValuedField(a.name, BaseAtomicType(inner))
    case _ =>
      DidScalarField(a.name, a.attrType, a.isKey)
  }

  method BuildAttributeFields(attrs: seq<Attribute>) returns (fields: seq<DidField>)
    ensures forall i :: 0 <= i < |fields| ==> ValidDidField(fields[i])
  {
    fields := [];
    var i := 0;
    while i < |attrs|
      invariant 0 <= i <= |attrs|
      invariant forall k :: 0 <= k < |fields| ==> ValidDidField(fields[k])
      decreases |attrs| - i
    {
      if attrs[i].name != "" {
        var f := AttrToDidField(attrs[i]);
        fields := fields + [f];
      }
      i := i + 1;
    }
  }

  // ---------------------------------------------------------------------------
  // Recursive DID Document Builder (bounded by `depth`)
  // ---------------------------------------------------------------------------

  method BuildDidDocument(
    diagram: DerDiagram,
    elem: EntityElement,
    cfg: DidConfig,
    depth: nat
  ) returns (doc: DidDocument)
    requires ConvertibleDiagram(diagram)
    requires elem in diagram.elements
    ensures ValidDidDocument(doc)
    ensures doc.docName == elem.name
    decreases depth
  {
    LemmaConvertibleElementFacts(diagram, elem);
    var keyAttrs := ElementKeyAttrs(elem);
    var ownFields := BuildAttributeFields(elem.attributes);
    var fields: seq<DidField> := [];

    // If `elem` is an Aggregation, include references to both inner endpoints
    // plus the inner relation's own attributes before its outer relations.
    var origin := "entity";
    match elem.AggregationDetails() {
      case NotAnAggregation => {
        origin := "entity";
        fields := ownFields;
      }
      case AggregationOf(src, innerRel) => {
        origin := "aggregation";
        LemmaConvertibleElementFacts(diagram, src);
        LemmaConvertibleElementFacts(diagram, innerRel.target);
        var refSrc := DidReferenceField(
          innerRel.name + "_source",
          innerRel.Kind(),
          src.name,
          ElementKeyAttrs(src),
          [],
          false
        );
        var refDst := DidReferenceField(
          innerRel.name + "_target",
          innerRel.Kind(),
          innerRel.target.name,
          ElementKeyAttrs(innerRel.target),
          innerRel.attributes,
          false
        );
        assert ValidDidField(refSrc);
        assert ValidDidField(refDst);
        fields := [refSrc, refDst] + ownFields;
      }
    }

    // Materialize every attached relation (unless already wrapped by an Aggregation
    // when building at the root level, or embed/reference according to `cfg`).
    var rIdx := 0;
    while rIdx < |elem.relations|
      invariant 0 <= rIdx <= |elem.relations|
      invariant forall k :: 0 <= k < |fields| ==> ValidDidField(fields[k])
      decreases |elem.relations| - rIdx
    {
      var rel := elem.relations[rIdx];
      LemmaConvertibleRelationFacts(diagram, elem, rel);
      var (shouldEmbed, isArray) := EffectiveRelationMode(cfg, rel.name, rel.Kind());

      var relField: DidField;
      if shouldEmbed && depth > 0 && rel.target != elem {
        var childDoc := BuildDidDocument(diagram, rel.target, cfg, depth - 1);
        relField := DidEmbeddedChild(
          rel.name,
          rel.Kind(),
          isArray,
          rel.attributes,
          childDoc
        );
      } else {
        var targetKeys := ElementKeyAttrs(rel.target);
        relField := DidReferenceField(
          rel.name,
          rel.Kind(),
          rel.target.name,
          targetKeys,
          rel.attributes,
          isArray
        );
      }
      assert ValidDidField(relField);
      fields := fields + [relField];
      rIdx := rIdx + 1;
    }

    doc := DidDocument(elem.name, origin, keyAttrs, fields);
  }

  // ---------------------------------------------------------------------------
  // Main DER -> DID Converter
  // ---------------------------------------------------------------------------

  predicate ShouldIncludeAsCollection(cfg: DidConfig, elemName: Name)
  {
    |cfg.rootCollectionNames| == 0 || elemName in cfg.rootCollectionNames
  }

  method ConvertDerToDid(
    diagram: DerDiagram,
    cfg: DidConfig
  ) returns (did: DidDatabase)
    requires ConvertibleDiagram(diagram)
    requires cfg.dbName != ""
    ensures ValidDidDatabase(did)
    ensures did.dbName == cfg.dbName
    ensures |cfg.rootCollectionNames| == 0 ==>
      |did.collections| == |diagram.elements| &&
      (forall i :: 0 <= i < |diagram.elements| ==>
        did.collections[i].collectionName == diagram.elements[i].name &&
        HasCollection(did, diagram.elements[i].name))
  {
    var cols: seq<DidCollection> := [];
    var i := 0;
    while i < |diagram.elements|
      invariant 0 <= i <= |diagram.elements|
      invariant forall k :: 0 <= k < |cols| ==> ValidDidCollection(cols[k])
      invariant |cfg.rootCollectionNames| == 0 ==>
        |cols| == i &&
        (forall k :: 0 <= k < i ==> cols[k].collectionName == diagram.elements[k].name)
      decreases |diagram.elements| - i
    {
      var elem := diagram.elements[i];
      if ShouldIncludeAsCollection(cfg, elem.name) {
        var rootDoc := BuildDidDocument(diagram, elem, cfg, cfg.maxDepth);
        var origin :=
          if elem.AggregationDetails().NotAnAggregation? then "entity"
          else "aggregation";
        var col := DidCollection(elem.name, origin, rootDoc);
        assert ValidDidCollection(col);
        cols := cols + [col];
      }
      i := i + 1;
    }

    did := DidDatabase(cfg.dbName, cols);
    if |cfg.rootCollectionNames| == 0 {
      forall k | 0 <= k < |diagram.elements|
        ensures HasCollection(did, diagram.elements[k].name)
      {
        assert did.collections[k].collectionName == diagram.elements[k].name;
      }
    }
  }

  // Converts a DER diagram directly to both a `DidDatabase` and its Mongo-style
  // XML representation in one verified call.
  method ConvertDerToDidXml(
    diagram: DerDiagram,
    cfg: DidConfig
  ) returns (did: DidDatabase, xml: string)
    requires ConvertibleDiagram(diagram)
    requires cfg.dbName != ""
    ensures ValidDidDatabase(did)
    ensures xml == FormatDidDatabaseXml(did)
    ensures |xml| > 0
  {
    did := ConvertDerToDid(diagram, cfg);
    xml := FormatDidDatabaseXml(did);
  }
}
