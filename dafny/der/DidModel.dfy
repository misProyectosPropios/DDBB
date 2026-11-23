// Document Instance Diagram (DID) / Hierarchical NoSQL Document Model
// (MongoDB-style collections, embedded sub-documents, embedded arrays, and
// document references) + XML Schema/Instance Generator.
//
// Formally models:
//   - Customizable storage directives (`ModeAuto`, `ModeEmbed`, `ModeReference`)
//     allowing a DER diagram to be modified/configured into different DIDs.
//   - Inductive document trees (`DidDocument`, `DidField`, `DidCollection`,
//     `DidDatabase`) with well-formedness invariants (`ValidDidDatabase`).
//   - Structured Mongo-style XML generation (`FormatDidDatabaseXml`).

include "Types.dfy"

module DidModel {
  import opened DerTypes

  // ---------------------------------------------------------------------------
  // DID Customization / Modification Config
  // ---------------------------------------------------------------------------

  // Controls how a DER relation is materialized in the DID document hierarchy:
  //   - ModeAuto:      1:1 -> Embedded Document, 1:N -> Embedded Array,
  //                    N:1 -> Reference, N:M -> Embedded Array of References
  //   - ModeEmbed:     Force embedding the target document (up to maxDepth)
  //   - ModeReference: Force referencing the target collection by its _id/PK
  datatype RelationStorageMode =
    | ModeAuto
    | ModeEmbed
    | ModeReference

  datatype DidConfig = DidConfig(
    dbName: Name,
    // Optional filter of entity/aggregation names to expose as top-level
    // collections (if empty, all entities/aggregations in the DER are included).
    rootCollectionNames: seq<Name>,
    // Per-relation overrides allowing the user to modify how any relation is
    // represented in the DID (Embed vs Reference).
    modeOverrides: map<Name, RelationStorageMode>,
    // Maximum embedding depth (prevents infinite recursion on cyclic relations).
    maxDepth: nat
  )

  function DefaultDidConfig(dbName: Name): DidConfig
    requires dbName != ""
  {
    DidConfig(dbName, [], map[], 2)
  }

  function WithRelationMode(
    cfg: DidConfig,
    relName: Name,
    mode: RelationStorageMode
  ): DidConfig
  {
    DidConfig(
      cfg.dbName,
      cfg.rootCollectionNames,
      cfg.modeOverrides[relName := mode],
      cfg.maxDepth
    )
  }

  function WithRootCollections(cfg: DidConfig, roots: seq<Name>): DidConfig
  {
    DidConfig(cfg.dbName, roots, cfg.modeOverrides, cfg.maxDepth)
  }

  function WithMaxDepth(cfg: DidConfig, maxDepth: nat): DidConfig
  {
    DidConfig(cfg.dbName, cfg.rootCollectionNames, cfg.modeOverrides, maxDepth)
  }

  // ---------------------------------------------------------------------------
  // DID Document Hierarchy Datatypes
  // ---------------------------------------------------------------------------

  datatype DidField =
    | DidScalarField(
        name: Name,
        attrType: AttrType,
        isKey: bool
      )
    | DidMultiValuedField(
        name: Name,
        elemType: AttrType
      )
    | DidReferenceField(
        relName: Name,
        relKind: RelationKind,
        targetCollection: Name,
        targetKeys: seq<Attribute>,
        relAttributes: seq<Attribute>,
        isArray: bool
      )
    | DidEmbeddedChild(
        relName: Name,
        relKind: RelationKind,
        isArray: bool,
        relAttributes: seq<Attribute>,
        childDoc: DidDocument
      )

  datatype DidDocument = DidDocument(
    docName: Name,
    originKind: string, // "entity" | "aggregation"
    idFields: seq<Attribute>,
    fields: seq<DidField>
  )

  datatype DidCollection = DidCollection(
    collectionName: Name,
    originKind: string,
    rootDoc: DidDocument
  )

  datatype DidDatabase = DidDatabase(
    dbName: Name,
    collections: seq<DidCollection>
  )

  // ---------------------------------------------------------------------------
  // Well-formedness Predicates (100% pure datatype invariants)
  // ---------------------------------------------------------------------------

  predicate ValidDidField(f: DidField)
    decreases f
  {
    match f
    case DidScalarField(name, _, _) =>
      name != ""
    case DidMultiValuedField(name, _) =>
      name != ""
    case DidReferenceField(relName, _, targetCol, targetKeys, _, _) =>
      relName != "" && targetCol != "" && |targetKeys| > 0
    case DidEmbeddedChild(relName, _, _, _, childDoc) =>
      relName != "" && ValidDidDocument(childDoc)
  }

  predicate ValidDidDocument(doc: DidDocument)
    decreases doc
  {
    doc.docName != "" &&
    |doc.idFields| > 0 &&
    (forall i :: 0 <= i < |doc.fields| ==> ValidDidField(doc.fields[i]))
  }

  predicate ValidDidCollection(col: DidCollection)
  {
    col.collectionName != "" &&
    ValidDidDocument(col.rootDoc)
  }

  predicate ValidDidDatabase(db: DidDatabase)
  {
    db.dbName != "" &&
    (forall i :: 0 <= i < |db.collections| ==> ValidDidCollection(db.collections[i]))
  }

  predicate HasCollection(db: DidDatabase, name: Name)
  {
    exists i :: 0 <= i < |db.collections| && db.collections[i].collectionName == name
  }

  // ---------------------------------------------------------------------------
  // Mongo-Style XML Generator for DID
  // ---------------------------------------------------------------------------

  function Indent(level: nat): string
    decreases level
  {
    if level == 0 then ""
    else "  " + Indent(level - 1)
  }

  function FormatXmlKeyFields(keys: seq<Attribute>, level: nat): string
    decreases |keys|
  {
    if |keys| == 0 then ""
    else
      Indent(level) + "<KeyField name=\"" + keys[0].name +
      "\" type=\"" + FormatAttrType(keys[0].attrType) + "\" />\n" +
      FormatXmlKeyFields(keys[1..], level)
  }

  function FormatXmlRelAttributes(attrs: seq<Attribute>, level: nat): string
    decreases |attrs|
  {
    if |attrs| == 0 then ""
    else
      Indent(level) + "<RelationField name=\"" + attrs[0].name +
      "\" type=\"" + FormatAttrType(attrs[0].attrType) + "\" />\n" +
      FormatXmlRelAttributes(attrs[1..], level)
  }

  function FormatXmlRefKeys(keys: seq<Attribute>, targetCol: Name, level: nat): string
    decreases |keys|
  {
    if |keys| == 0 then ""
    else
      Indent(level) + "<RefKey field=\"" + targetCol + "_" + keys[0].name +
      "\" refField=\"" + keys[0].name +
      "\" type=\"" + FormatAttrType(keys[0].attrType) + "\" />\n" +
      FormatXmlRefKeys(keys[1..], targetCol, level)
  }

  function FormatDidFieldXml(f: DidField, level: nat): string
    decreases f
  {
    var pad := Indent(level);
    match f
    case DidScalarField(name, attrType, isKey) =>
      pad + "<Field name=\"" + name + "\" type=\"" + FormatAttrType(attrType) +
      "\"" + (if isKey then " isKey=\"true\"" else "") + " />\n"
    case DidMultiValuedField(name, elemType) =>
      pad + "<ArrayField name=\"" + name + "\" elemType=\"" + FormatAttrType(elemType) + "\">\n" +
      Indent(level + 1) + "<Item type=\"" + FormatAttrType(elemType) + "\" />\n" +
      pad + "</ArrayField>\n"
    case DidReferenceField(relName, relKind, targetCol, targetKeys, relAttrs, isArray) =>
      var tag := if isArray then "ReferenceArray" else "DocumentReference";
      pad + "<" + tag + " relation=\"" + relName +
      "\" kind=\"" + FormatRelationKind(relKind) +
      "\" refCollection=\"" + targetCol + "\">\n" +
      FormatXmlRefKeys(targetKeys, targetCol, level + 1) +
      FormatXmlRelAttributes(relAttrs, level + 1) +
      pad + "</" + tag + ">\n"
    case DidEmbeddedChild(relName, relKind, isArray, relAttrs, childDoc) =>
      var tag := if isArray then "EmbeddedArray" else "EmbeddedDocument";
      pad + "<" + tag + " relation=\"" + relName +
      "\" kind=\"" + FormatRelationKind(relKind) +
      "\" entity=\"" + childDoc.docName + "\">\n" +
      FormatXmlRelAttributes(relAttrs, level + 1) +
      FormatDidDocumentXml(childDoc, level + 1) +
      pad + "</" + tag + ">\n"
  }

  function FormatDidFieldsXml(fields: seq<DidField>, level: nat): string
    decreases fields
  {
    if |fields| == 0 then ""
    else FormatDidFieldXml(fields[0], level) + FormatDidFieldsXml(fields[1..], level)
  }

  function FormatDidDocumentXml(doc: DidDocument, level: nat): string
    decreases doc
  {
    var pad := Indent(level);
    pad + "<Document entity=\"" + doc.docName + "\" origin=\"" + doc.originKind + "\">\n" +
    Indent(level + 1) + "<Id>\n" +
    FormatXmlKeyFields(doc.idFields, level + 2) +
    Indent(level + 1) + "</Id>\n" +
    FormatDidFieldsXml(doc.fields, level + 1) +
    pad + "</Document>\n"
  }

  function FormatDidCollectionsXml(cols: seq<DidCollection>, level: nat): string
    decreases |cols|
  {
    if |cols| == 0 then ""
    else
      var c := cols[0];
      var pad := Indent(level);
      pad + "<Collection name=\"" + c.collectionName + "\" origin=\"" + c.originKind + "\">\n" +
      FormatDidDocumentXml(c.rootDoc, level + 1) +
      pad + "</Collection>\n" +
      FormatDidCollectionsXml(cols[1..], level)
  }

  function FormatDidDatabaseXml(db: DidDatabase): string
    ensures |FormatDidDatabaseXml(db)| > 0
  {
    "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" +
    "<MongoDocumentDatabase name=\"" + db.dbName + "\" model=\"DID\">\n" +
    FormatDidCollectionsXml(db.collections, 1) +
    "</MongoDocumentDatabase>\n"
  }
}
