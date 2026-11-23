// Unified NoSQL Transformation Engine (Document, Graph, Column, Key-Value)
// built on top of the DER diagram and `dafny/der/DidModel.dfy` + `DerToDid.dfy`:
//   - Supports Partial Incrustation (subset of target attributes embedded
//     alongside reference) and Complete Incrustation (all target attributes
//     embedded inside host).
//   - Supports Table / Collection Deletion (Absorption) when a target entity
//     (such as a Weak Entity or 1:1 / 1:N dependent entity) is completely
//     incrusted and has no unabsorbed external references.
//   - Generates structured models, visual metadata, native query/schema scripts,
//     and XML for all 4 NoSQL paradigms:
//       1. Document  (DID / MongoDB XML & BSON/JSON)
//       2. Graph     (Property Graph / Neo4j Cypher & Graph XML)
//       3. Column    (Wide-Column / Apache Cassandra CQL & Column-Family XML)
//       4. Key-Value (Redis Keyspace Patterns & Key-Value XML)

import { baseAtomicType, elementKeyAttrs, relationKindOf } from "./derToRelational";
import type {
  Attribute,
  AttrTypeKind,
  DerAggregation,
  DerDiagramData,
  DerElement,
  DerRelation,
  RelationKind
} from "./types";

export type NoSqlModelKind = "document" | "graph" | "column" | "keyvalue";

// Incrustation (embedding) level for a relation:
//   - "auto":     1:1 & 1:N -> complete incrustation; N:1 & N:M -> reference only ("none")
//   - "none":     Reference only (foreign key / DBRef), no non-key target attributes incrusted
//   - "partial":  Incrusts a user-chosen subset of target attributes (`incrustedAttrs`) + reference
//   - "complete": Incrusts ALL attributes of the target entity inside the host
export type IncrustationMode = "auto" | "none" | "partial" | "complete";

export interface RelationIncrustationRule {
  mode: IncrustationMode;
  // For "partial" mode: which non-key attributes of the target entity to embed
  partialAttrs: string[];
  // Whether to delete (absorb) the target entity's standalone table/collection if eligible
  deleteTargetTable: boolean;
}

export interface DidConfig {
  dbName: string;
  rootCollectionNames: string[]; // Optional manual filter
  relationRules: Record<string, RelationIncrustationRule>;
  maxDepth: number;
}

export interface TableDeletionCheck {
  targetId: string;
  targetName: string;
  isWeak: boolean;
  requestedDelete: boolean;
  canDelete: boolean;
  actuallyDeleted: boolean;
  absorbedInto: string[];
  reason: string;
}

export type DidField =
  | {
      kind: "scalar";
      name: string;
      attrType: AttrTypeKind;
      isKey: boolean;
    }
  | {
      kind: "multivalued";
      name: string;
      elemType: AttrTypeKind;
    }
  | {
      kind: "reference";
      relName: string;
      relKind: RelationKind;
      targetCollection: string;
      targetKeys: Attribute[];
      relAttributes: Attribute[];
      isArray: boolean;
    }
  | {
      kind: "partial-incrustation";
      relName: string;
      relKind: RelationKind;
      targetCollection: string;
      targetKeys: Attribute[];
      incrustedAttributes: Attribute[];
      relAttributes: Attribute[];
      isArray: boolean;
    }
  | {
      kind: "embedded";
      relName: string;
      relKind: RelationKind;
      isArray: boolean;
      absorbedTable: boolean;
      relAttributes: Attribute[];
      childDoc: DidDocument;
    };

export interface DidDocument {
  docName: string;
  originKind: "entity" | "aggregation";
  isWeak: boolean;
  idFields: Attribute[];
  fields: DidField[];
}

export interface DidCollection {
  collectionName: string;
  originKind: "entity" | "aggregation";
  isWeak: boolean;
  rootDoc: DidDocument;
}

export interface DidDatabase {
  dbName: string;
  collections: DidCollection[];
  deletedTables: TableDeletionCheck[];
  allDeletionChecks: TableDeletionCheck[];
}

export function defaultDidConfig(dbName = "DDBB_NoSQL"): DidConfig {
  return {
    dbName,
    rootCollectionNames: [],
    relationRules: {},
    maxDepth: 2
  };
}

export function getRelationRule(
  cfg: DidConfig,
  rel: DerRelation,
  targetElem: DerElement | undefined
): RelationIncrustationRule {
  const existing = cfg.relationRules[rel.name];
  if (existing) return existing;
  const isTargetWeak = Boolean(
    targetElem && targetElem.kind === "entity" && targetElem.isWeak
  );
  const nonKeyAttrs = (targetElem?.attributes ?? [])
    .filter((a) => !a.isKey)
    .map((a) => a.name);
  return {
    mode: "auto",
    partialAttrs: nonKeyAttrs.slice(0, 1),
    deleteTargetTable: isTargetWeak
  };
}

export function effectiveIncrustation(
  cfg: DidConfig,
  rel: DerRelation,
  targetElem: DerElement | undefined
): {
  resolvedMode: "none" | "partial" | "complete";
  isArray: boolean;
  incrustedAttrs: Attribute[];
  wantsDeleteTarget: boolean;
} {
  const kind = relationKindOf(rel);
  const isArray = kind === "1:N" || kind === "N:M";
  const rule = getRelationRule(cfg, rel, targetElem);

  const resolvedMode: "none" | "partial" | "complete" =
    rule.mode === "auto"
      ? kind === "1:1" || kind === "1:N"
        ? "complete"
        : "none"
      : rule.mode;

  const targetAttrs = targetElem?.attributes ?? [];
  let incrustedAttrs: Attribute[] = [];
  if (resolvedMode === "complete") {
    incrustedAttrs = targetAttrs;
  } else if (resolvedMode === "partial") {
    const picked = new Set(rule.partialAttrs);
    incrustedAttrs = targetAttrs.filter((a) => !a.isKey && picked.has(a.name));
    if (incrustedAttrs.length === 0 && targetAttrs.length > 0) {
      incrustedAttrs = targetAttrs.slice(0, 1);
    }
  }

  return {
    resolvedMode,
    isArray,
    incrustedAttrs,
    wantsDeleteTarget: rule.deleteTargetTable
  };
}

// ---------------------------------------------------------------------------
// Table Deletion / Absorption Eligibility Analyzer (Weak Entities & Complete Incrustation)
// ---------------------------------------------------------------------------

export function analyzeTableDeletions(
  diagram: DerDiagramData,
  cfg: DidConfig
): TableDeletionCheck[] {
  return diagram.elements.map((elem) => {
    const isWeak = elem.kind === "entity" && Boolean(elem.isWeak);
    const incomingRels = diagram.relations.filter(
      (r) => r.targetId === elem.id && r.sourceId !== elem.id
    );
    const outgoingRels = diagram.relations.filter(
      (r) => r.sourceId === elem.id && r.targetId !== elem.id
    );

    const completeHosts: string[] = [];
    const partialOnlyHosts: string[] = [];
    const refOnlyHosts: string[] = [];
    let requestedDelete = false;

    for (const rel of incomingRels) {
      const src = diagram.elements.find((e) => e.id === rel.sourceId);
      const eff = effectiveIncrustation(cfg, rel, elem);
      if (eff.wantsDeleteTarget) {
        requestedDelete = true;
      }
      if (eff.resolvedMode === "complete") {
        completeHosts.push(`${src?.name ?? "?"} (via ${rel.name})`);
      } else if (eff.resolvedMode === "partial") {
        partialOnlyHosts.push(`${src?.name ?? "?"} (via ${rel.name})`);
      } else {
        refOnlyHosts.push(`${src?.name ?? "?"} (via ${rel.name})`);
      }
    }

    if (completeHosts.length === 0) {
      const reason =
        partialOnlyHosts.length > 0
          ? `Cannot delete table '${elem.name}': only partially incrusted into ${partialOnlyHosts.join(
              ", "
            )} (non-incrusted attributes would be lost). Switch to Complete Incrustation to delete.`
          : `Cannot delete table '${elem.name}': not completely incrusted into any parent entity.`;
      return {
        targetId: elem.id,
        targetName: elem.name,
        isWeak,
        requestedDelete,
        canDelete: false,
        actuallyDeleted: false,
        absorbedInto: [],
        reason
      };
    }

    if (refOnlyHosts.length > 0 || partialOnlyHosts.length > 0) {
      const ext = [...partialOnlyHosts, ...refOnlyHosts].join(", ");
      return {
        targetId: elem.id,
        targetName: elem.name,
        isWeak,
        requestedDelete,
        canDelete: false,
        actuallyDeleted: false,
        absorbedInto: completeHosts,
        reason: `Cannot delete table '${elem.name}': still referenced externally by ${ext}.`
      };
    }

    if (outgoingRels.length > 0 && elem.kind === "aggregation") {
      return {
        targetId: elem.id,
        targetName: elem.name,
        isWeak,
        requestedDelete,
        canDelete: false,
        actuallyDeleted: false,
        absorbedInto: completeHosts,
        reason: `Cannot delete Aggregation '${elem.name}': owns outer relations (${outgoingRels
          .map((r) => r.name)
          .join(", ")}).`
      };
    }

    const reason = isWeak
      ? `Weak Entity '${elem.name}' is completely incrusted into ${completeHosts.join(
          ", "
        )} — safe to delete standalone table.`
      : `'${elem.name}' is completely incrusted into ${completeHosts.join(
          ", "
        )} with no external references — can be deleted (absorbed).`;

    return {
      targetId: elem.id,
      targetName: elem.name,
      isWeak,
      requestedDelete,
      canDelete: true,
      actuallyDeleted: requestedDelete,
      absorbedInto: completeHosts,
      reason
    };
  });
}

// ---------------------------------------------------------------------------
// 1. Document Model (DID) & Mongo-Style XML / BSON Generator
// ---------------------------------------------------------------------------

function attrToDidField(a: Attribute): DidField {
  if (a.attrType.startsWith("SET<")) {
    return {
      kind: "multivalued",
      name: a.name,
      elemType: baseAtomicType(a.attrType)
    };
  }
  return {
    kind: "scalar",
    name: a.name,
    attrType: a.attrType,
    isKey: a.isKey
  };
}

function buildDidDocument(
  diagram: DerDiagramData,
  elem: DerElement,
  cfg: DidConfig,
  deletedIds: Set<string>,
  depth: number
): DidDocument {
  const keyAttrs = elementKeyAttrs(elem, diagram);
  const ownFields = elem.attributes
    .filter((a) => a.name.trim() !== "")
    .map(attrToDidField);

  let fields: DidField[] = [];
  const originKind = elem.kind;
  const isWeak = elem.kind === "entity" && Boolean(elem.isWeak);

  if (elem.kind === "aggregation") {
    const agg = elem as DerAggregation;
    const innerRel = diagram.relations.find((r) => r.id === agg.innerRelationId);
    if (innerRel) {
      const src = diagram.elements.find((e) => e.id === innerRel.sourceId);
      const dst = diagram.elements.find((e) => e.id === innerRel.targetId);
      const rKind = relationKindOf(innerRel);
      if (src) {
        fields.push({
          kind: "reference",
          relName: `${innerRel.name}_source`,
          relKind: rKind,
          targetCollection: src.name,
          targetKeys: elementKeyAttrs(src, diagram),
          relAttributes: [],
          isArray: false
        });
      }
      if (dst) {
        fields.push({
          kind: "reference",
          relName: `${innerRel.name}_target`,
          relKind: rKind,
          targetCollection: dst.name,
          targetKeys: elementKeyAttrs(dst, diagram),
          relAttributes: innerRel.attributes,
          isArray: false
        });
      }
    }
    fields.push(...ownFields);
  } else {
    fields = [...ownFields];
  }

  const attachedRels = diagram.relations.filter((r) => r.sourceId === elem.id);

  for (const rel of attachedRels) {
    const targetElem = diagram.elements.find((e) => e.id === rel.targetId);
    if (!targetElem) continue;

    const rKind = relationKindOf(rel);
    const eff = effectiveIncrustation(cfg, rel, targetElem);

    if (eff.resolvedMode === "complete" && depth > 0 && targetElem.id !== elem.id) {
      const childDoc = buildDidDocument(
        diagram,
        targetElem,
        cfg,
        deletedIds,
        depth - 1
      );
      fields.push({
        kind: "embedded",
        relName: rel.name,
        relKind: rKind,
        isArray: eff.isArray,
        absorbedTable: deletedIds.has(targetElem.id),
        relAttributes: rel.attributes,
        childDoc
      });
    } else if (eff.resolvedMode === "partial") {
      fields.push({
        kind: "partial-incrustation",
        relName: rel.name,
        relKind: rKind,
        targetCollection: targetElem.name,
        targetKeys: elementKeyAttrs(targetElem, diagram),
        incrustedAttributes: eff.incrustedAttrs,
        relAttributes: rel.attributes,
        isArray: eff.isArray
      });
    } else {
      fields.push({
        kind: "reference",
        relName: rel.name,
        relKind: rKind,
        targetCollection: targetElem.name,
        targetKeys: elementKeyAttrs(targetElem, diagram),
        relAttributes: rel.attributes,
        isArray: eff.isArray
      });
    }
  }

  return {
    docName: elem.name,
    originKind,
    isWeak,
    idFields: keyAttrs,
    fields
  };
}

export function convertDerToDid(
  diagram: DerDiagramData,
  cfg: DidConfig
): DidDatabase {
  const allDeletionChecks = analyzeTableDeletions(diagram, cfg);
  const deletedTables = allDeletionChecks.filter((c) => c.actuallyDeleted);
  const deletedIds = new Set(deletedTables.map((c) => c.targetId));

  const collections: DidCollection[] = [];

  for (const elem of diagram.elements) {
    // Skip tables that were absorbed & deleted!
    if (deletedIds.has(elem.id)) continue;

    const include =
      cfg.rootCollectionNames.length === 0 ||
      cfg.rootCollectionNames.includes(elem.name);
    if (!include) continue;

    const rootDoc = buildDidDocument(
      diagram,
      elem,
      cfg,
      deletedIds,
      cfg.maxDepth
    );
    collections.push({
      collectionName: elem.name,
      originKind: elem.kind,
      isWeak: elem.kind === "entity" && Boolean(elem.isWeak),
      rootDoc
    });
  }

  return {
    dbName: cfg.dbName || "DDBB_NoSQL",
    collections,
    deletedTables,
    allDeletionChecks
  };
}

// ---------------------------------------------------------------------------
// XML & BSON Formatters for Document Model (DID)
// ---------------------------------------------------------------------------

function indent(level: number): string {
  return "  ".repeat(level);
}

function xmlAttr(v: string): string {
  return v
    .replace(/&/g, "&amp;")
    .replace(/"/g, "&quot;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;");
}

function formatXmlKeyFields(keys: Attribute[], level: number): string {
  return keys
    .map(
      (k) =>
        `${indent(level)}<KeyField name="${xmlAttr(k.name)}" type="${xmlAttr(
          k.attrType
        )}" />\n`
    )
    .join("");
}

function formatXmlRelAttributes(attrs: Attribute[], level: number): string {
  return attrs
    .map(
      (a) =>
        `${indent(level)}<RelationField name="${xmlAttr(a.name)}" type="${xmlAttr(
          a.attrType
        )}" />\n`
    )
    .join("");
}

function formatXmlRefKeys(
  keys: Attribute[],
  targetCol: string,
  level: number
): string {
  return keys
    .map(
      (k) =>
        `${indent(level)}<RefKey field="${xmlAttr(
          `${targetCol}_${k.name}`
        )}" refField="${xmlAttr(k.name)}" type="${xmlAttr(k.attrType)}" />\n`
    )
    .join("");
}

function formatDidFieldXml(f: DidField, level: number): string {
  const pad = indent(level);
  switch (f.kind) {
    case "scalar":
      return `${pad}<Field name="${xmlAttr(f.name)}" type="${xmlAttr(
        f.attrType
      )}"${f.isKey ? ' isKey="true"' : ""} />\n`;
    case "multivalued":
      return (
        `${pad}<ArrayField name="${xmlAttr(f.name)}" elemType="${xmlAttr(
          f.elemType
        )}">\n` +
        `${indent(level + 1)}<Item type="${xmlAttr(f.elemType)}" />\n` +
        `${pad}</ArrayField>\n`
      );
    case "reference": {
      const tag = f.isArray ? "ReferenceArray" : "DocumentReference";
      return (
        `${pad}<${tag} relation="${xmlAttr(f.relName)}" kind="${xmlAttr(
          f.relKind
        )}" incrustation="none" refCollection="${xmlAttr(f.targetCollection)}">\n` +
        formatXmlRefKeys(f.targetKeys, f.targetCollection, level + 1) +
        formatXmlRelAttributes(f.relAttributes, level + 1) +
        `${pad}</${tag}>\n`
      );
    }
    case "partial-incrustation": {
      const tag = f.isArray
        ? "PartialIncrustationArray"
        : "PartialIncrustation";
      const incFields = f.incrustedAttributes
        .map(
          (a) =>
            `${indent(level + 1)}<IncrustedField name="${xmlAttr(
              a.name
            )}" type="${xmlAttr(a.attrType)}" />\n`
        )
        .join("");
      return (
        `${pad}<${tag} relation="${xmlAttr(f.relName)}" kind="${xmlAttr(
          f.relKind
        )}" incrustation="partial" refCollection="${xmlAttr(
          f.targetCollection
        )}">\n` +
        formatXmlRefKeys(f.targetKeys, f.targetCollection, level + 1) +
        incFields +
        formatXmlRelAttributes(f.relAttributes, level + 1) +
        `${pad}</${tag}>\n`
      );
    }
    case "embedded": {
      const tag = f.isArray ? "EmbeddedArray" : "EmbeddedDocument";
      return (
        `${pad}<${tag} relation="${xmlAttr(f.relName)}" kind="${xmlAttr(
          f.relKind
        )}" incrustation="complete" entity="${xmlAttr(
          f.childDoc.docName
        )}" absorbedTable="${f.absorbedTable ? "true" : "false"}">\n` +
        formatXmlRelAttributes(f.relAttributes, level + 1) +
        formatDidDocumentXml(f.childDoc, level + 1) +
        `${pad}</${tag}>\n`
      );
    }
  }
}

function formatDidDocumentXml(doc: DidDocument, level: number): string {
  const pad = indent(level);
  const weakAttr = doc.isWeak ? ' weakEntity="true"' : "";
  return (
    `${pad}<Document entity="${xmlAttr(doc.docName)}" origin="${xmlAttr(
      doc.originKind
    )}"${weakAttr}>\n` +
    `${indent(level + 1)}<Id>\n` +
    formatXmlKeyFields(doc.idFields, level + 2) +
    `${indent(level + 1)}</Id>\n` +
    doc.fields.map((f) => formatDidFieldXml(f, level + 1)).join("") +
    `${pad}</Document>\n`
  );
}

export function formatDidDatabaseXml(db: DidDatabase): string {
  const deletedXml =
    db.deletedTables.length > 0
      ? `${indent(1)}<AbsorbedDeletedTables>\n` +
        db.deletedTables
          .map(
            (d) =>
              `${indent(2)}<DeletedTable name="${xmlAttr(
                d.targetName
              )}" weakEntity="${d.isWeak ? "true" : "false"}" absorbedInto="${xmlAttr(
                d.absorbedInto.join("; ")
              )}" />\n`
          )
          .join("") +
        `${indent(1)}</AbsorbedDeletedTables>\n`
      : "";

  const colsXml = db.collections
    .map(
      (c) =>
        `${indent(1)}<Collection name="${xmlAttr(
          c.collectionName
        )}" origin="${xmlAttr(c.originKind)}">\n` +
        formatDidDocumentXml(c.rootDoc, 2) +
        `${indent(1)}</Collection>\n`
    )
    .join("");

  return (
    `<?xml version="1.0" encoding="UTF-8"?>\n` +
    `<MongoDocumentDatabase name="${xmlAttr(db.dbName)}" model="DID">\n` +
    deletedXml +
    colsXml +
    `</MongoDocumentDatabase>`
  );
}

function buildMongoDocObject(doc: DidDocument): Record<string, unknown> {
  const obj: Record<string, unknown> = {};
  if (doc.idFields.length === 1) {
    obj["_id"] = `<${doc.idFields[0].name}: ${doc.idFields[0].attrType}>`;
  } else {
    const comp: Record<string, string> = {};
    for (const k of doc.idFields) {
      comp[k.name] = `<${k.attrType}>`;
    }
    obj["_id"] = comp;
  }

  for (const f of doc.fields) {
    switch (f.kind) {
      case "scalar":
        obj[f.name] = `<${f.attrType}${f.isKey ? " (PK)" : ""}>`;
        break;
      case "multivalued":
        obj[f.name] = [`<${f.elemType}>`];
        break;
      case "reference": {
        const refObj: Record<string, unknown> = {
          $ref: f.targetCollection
        };
        for (const k of f.targetKeys) {
          refObj[`${f.targetCollection}_${k.name}`] = `<${k.attrType}>`;
        }
        for (const ra of f.relAttributes) {
          refObj[ra.name] = `<${ra.attrType}>`;
        }
        obj[f.relName] = f.isArray ? [refObj] : refObj;
        break;
      }
      case "partial-incrustation": {
        const partObj: Record<string, unknown> = {
          $ref: f.targetCollection
        };
        for (const k of f.targetKeys) {
          partObj[`${f.targetCollection}_${k.name}`] = `<${k.attrType}>`;
        }
        for (const inc of f.incrustedAttributes) {
          partObj[inc.name] = `<${inc.attrType} (partial incrustation)>`;
        }
        for (const ra of f.relAttributes) {
          partObj[ra.name] = `<${ra.attrType}>`;
        }
        obj[f.relName] = f.isArray ? [partObj] : partObj;
        break;
      }
      case "embedded": {
        const childObj: Record<string, unknown> = {};
        for (const ra of f.relAttributes) {
          childObj[ra.name] = `<${ra.attrType}>`;
        }
        childObj[f.childDoc.docName] = buildMongoDocObject(f.childDoc);
        obj[f.relName] = f.isArray ? [childObj] : childObj;
        break;
      }
    }
  }
  return obj;
}

export function formatDidMongoJson(db: DidDatabase): string {
  const root: Record<string, unknown> = {};
  if (db.deletedTables.length > 0) {
    root["_absorbedAndDeletedTables"] = db.deletedTables.map((d) => ({
      table: d.targetName,
      weakEntity: d.isWeak,
      absorbedInto: d.absorbedInto
    }));
  }
  for (const col of db.collections) {
    root[`db.${col.collectionName}`] = buildMongoDocObject(col.rootDoc);
  }
  return JSON.stringify(root, null, 2);
}

// ---------------------------------------------------------------------------
// 2. Graph Model (Property Graph / Neo4j Cypher & Graph XML)
// ---------------------------------------------------------------------------

export interface GraphNodeSchema {
  label: string;
  originKind: "entity" | "aggregation";
  keys: Attribute[];
  properties: { name: string; type: string; origin: string }[];
}

export interface GraphEdgeSchema {
  type: string;
  fromLabel: string;
  toLabel: string;
  cardinality: RelationKind;
  incrustation: "none" | "partial";
  properties: { name: string; type: string; origin: string }[];
}

export interface GraphModelOutput {
  nodes: GraphNodeSchema[];
  edges: GraphEdgeSchema[];
  deletedNodes: TableDeletionCheck[];
  cypherScript: string;
  xmlOutput: string;
}

export function convertDerToGraphModel(
  diagram: DerDiagramData,
  cfg: DidConfig
): GraphModelOutput {
  const checks = analyzeTableDeletions(diagram, cfg);
  const deletedNodes = checks.filter((c) => c.actuallyDeleted);
  const deletedIds = new Set(deletedNodes.map((c) => c.targetId));

  const nodes: GraphNodeSchema[] = [];
  const edges: GraphEdgeSchema[] = [];

  for (const elem of diagram.elements) {
    if (deletedIds.has(elem.id)) continue;

    const props: { name: string; type: string; origin: string }[] = elem.attributes.map(
      (a) => ({
        name: a.name,
        type: a.attrType,
        origin: a.isKey ? "key" : "own"
      })
    );

    // Fold completely incrusted target entities directly into this node's properties
    const outRels = diagram.relations.filter((r) => r.sourceId === elem.id);
    for (const rel of outRels) {
      const target = diagram.elements.find((e) => e.id === rel.targetId);
      if (!target) continue;
      const eff = effectiveIncrustation(cfg, rel, target);

      if (eff.resolvedMode === "complete" && target.id !== elem.id) {
        const prefix = target.name.toLowerCase();
        for (const a of target.attributes) {
          props.push({
            name: `${prefix}_${a.name}`,
            type: eff.isArray ? `LIST<${a.attrType}>` : a.attrType,
            origin: `complete-incrustation (${rel.name} -> ${target.name}${
              deletedIds.has(target.id) ? ", table deleted" : ""
            })`
          });
        }
        for (const ra of rel.attributes) {
          props.push({
            name: `${rel.name.toLowerCase()}_${ra.name}`,
            type: eff.isArray ? `LIST<${ra.attrType}>` : ra.attrType,
            origin: `relation (${rel.name})`
          });
        }
      } else if (!deletedIds.has(target.id)) {
        const edgeProps: { name: string; type: string; origin: string }[] =
          rel.attributes.map((ra) => ({
            name: ra.name,
            type: ra.attrType,
            origin: "relation"
          }));

        if (eff.resolvedMode === "partial") {
          for (const inc of eff.incrustedAttrs) {
            edgeProps.push({
              name: `${target.name.toLowerCase()}_${inc.name}`,
              type: inc.attrType,
              origin: `partial-incrustation from ${target.name}`
            });
          }
        }

        edges.push({
          type: rel.name.toUpperCase(),
          fromLabel: elem.name,
          toLabel: target.name,
          cardinality: relationKindOf(rel),
          incrustation: eff.resolvedMode === "partial" ? "partial" : "none",
          properties: edgeProps
        });
      }
    }

    nodes.push({
      label: elem.name,
      originKind: elem.kind,
      keys: elementKeyAttrs(elem, diagram),
      properties: props
    });
  }

  const cypherLines: string[] = [
    `// Neo4j Property Graph Schema generated from DER (${cfg.dbName})`
  ];
  if (deletedNodes.length > 0) {
    cypherLines.push(
      `// Absorbed & Deleted Standalone Nodes: ${deletedNodes
        .map((d) => `${d.targetName} -> ${d.absorbedInto.join(", ")}`)
        .join("; ")}`
    );
  }
  for (const n of nodes) {
    if (n.keys.length > 0) {
      const kList = n.keys.map((k) => `n.${k.name}`).join(", ");
      cypherLines.push(
        `CREATE CONSTRAINT ${n.label.toLowerCase()}_pk IF NOT EXISTS FOR (n:${
          n.label
        }) REQUIRE (${kList}) IS UNIQUE;`
      );
    }
    const propStr = n.properties
      .map((p) => `${p.name}: <${p.type}>`)
      .join(", ");
    cypherLines.push(`// Node: (:${n.label} { ${propStr} })`);
  }
  cypherLines.push("");
  for (const e of edges) {
    const pStr =
      e.properties.length > 0
        ? ` { ${e.properties.map((p) => `${p.name}: <${p.type}>`).join(", ")} }`
        : "";
    cypherLines.push(
      `// Edge [${e.cardinality}, incrustation=${e.incrustation}]: (:${e.fromLabel})-[:${e.type}${pStr}]->(:${e.toLabel})`
    );
  }

  const xmlOutput =
    `<?xml version="1.0" encoding="UTF-8"?>\n` +
    `<PropertyGraphDatabase name="${xmlAttr(cfg.dbName)}" model="Graph">\n` +
    (deletedNodes.length > 0
      ? `  <AbsorbedDeletedNodes>\n` +
        deletedNodes
          .map(
            (d) =>
              `    <DeletedNode name="${xmlAttr(
                d.targetName
              )}" absorbedInto="${xmlAttr(d.absorbedInto.join("; "))}" />\n`
          )
          .join("") +
        `  </AbsorbedDeletedNodes>\n`
      : "") +
    nodes
      .map(
        (n) =>
          `  <NodeLabel label="${xmlAttr(n.label)}" origin="${xmlAttr(
            n.originKind
          )}">\n` +
          n.properties
            .map(
              (p) =>
                `    <Property name="${xmlAttr(p.name)}" type="${xmlAttr(
                  p.type
                )}" origin="${xmlAttr(p.origin)}" />\n`
            )
            .join("") +
          `  </NodeLabel>\n`
      )
      .join("") +
    edges
      .map(
        (e) =>
          `  <EdgeType type="${xmlAttr(e.type)}" from="${xmlAttr(
            e.fromLabel
          )}" to="${xmlAttr(e.toLabel)}" cardinality="${xmlAttr(
            e.cardinality
          )}" incrustation="${xmlAttr(e.incrustation)}">\n` +
          e.properties
            .map(
              (p) =>
                `    <Property name="${xmlAttr(p.name)}" type="${xmlAttr(
                  p.type
                )}" origin="${xmlAttr(p.origin)}" />\n`
            )
            .join("") +
          `  </EdgeType>\n`
      )
      .join("") +
    `</PropertyGraphDatabase>`;

  return {
    nodes,
    edges,
    deletedNodes,
    cypherScript: cypherLines.join("\n"),
    xmlOutput
  };
}

// ---------------------------------------------------------------------------
// 3. Column Model (Wide-Column / Cassandra CQL & Column-Family XML)
// ---------------------------------------------------------------------------

export interface ColumnFamilyColumn {
  name: string;
  cqlType: string;
  role: "partition-key" | "clustering-key" | "regular" | "incrusted-complete" | "incrusted-partial";
  sourceInfo: string;
}

export interface ColumnFamilySchema {
  name: string;
  partitionKeys: string[];
  clusteringKeys: string[];
  columns: ColumnFamilyColumn[];
}

export interface ColumnModelOutput {
  families: ColumnFamilySchema[];
  deletedFamilies: TableDeletionCheck[];
  cqlScript: string;
  xmlOutput: string;
}

function toCqlType(t: AttrTypeKind): string {
  switch (t) {
    case "INT":
      return "INT";
    case "STRING":
      return "TEXT";
    case "BOOL":
      return "BOOLEAN";
    case "DATE":
      return "DATE";
    case "DECIMAL":
      return "DECIMAL";
    case "SET<STRING>":
      return "SET<TEXT>";
    case "SET<INT>":
      return "SET<INT>";
  }
}

export function convertDerToColumnModel(
  diagram: DerDiagramData,
  cfg: DidConfig
): ColumnModelOutput {
  const checks = analyzeTableDeletions(diagram, cfg);
  const deletedFamilies = checks.filter((c) => c.actuallyDeleted);
  const deletedIds = new Set(deletedFamilies.map((c) => c.targetId));

  const families: ColumnFamilySchema[] = [];

  for (const elem of diagram.elements) {
    if (deletedIds.has(elem.id)) continue;

    const pks = elementKeyAttrs(elem, diagram).map((k) => k.name);
    const cks: string[] = [];
    const cols: ColumnFamilyColumn[] = [];

    for (const k of elementKeyAttrs(elem, diagram)) {
      cols.push({
        name: k.name,
        cqlType: toCqlType(k.attrType),
        role: "partition-key",
        sourceInfo: "PK"
      });
    }

    for (const a of elem.attributes) {
      if (pks.includes(a.name)) continue;
      cols.push({
        name: a.name,
        cqlType: toCqlType(a.attrType),
        role: "regular",
        sourceInfo: "own attribute"
      });
    }

    const outRels = diagram.relations.filter((r) => r.sourceId === elem.id);
    for (const rel of outRels) {
      const target = diagram.elements.find((e) => e.id === rel.targetId);
      if (!target) continue;
      const eff = effectiveIncrustation(cfg, rel, target);
      const tKeys = elementKeyAttrs(target, diagram);

      if (eff.resolvedMode === "complete" && target.id !== elem.id) {
        if (eff.isArray) {
          for (const tk of tKeys) {
            const ckName = `${target.name.toLowerCase()}_${tk.name}`;
            cks.push(ckName);
            cols.push({
              name: ckName,
              cqlType: toCqlType(tk.attrType),
              role: "clustering-key",
              sourceInfo: `clustering key (${rel.name} -> ${target.name})`
            });
          }
        }
        for (const a of target.attributes) {
          if (eff.isArray && tKeys.some((k) => k.name === a.name)) continue;
          cols.push({
            name: `${target.name.toLowerCase()}_${a.name}`,
            cqlType: toCqlType(a.attrType),
            role: "incrusted-complete",
            sourceInfo: `complete incrustation (${rel.name} -> ${target.name}${
              deletedIds.has(target.id) ? ", table deleted" : ""
            })`
          });
        }
        for (const ra of rel.attributes) {
          cols.push({
            name: `${rel.name.toLowerCase()}_${ra.name}`,
            cqlType: toCqlType(ra.attrType),
            role: "incrusted-complete",
            sourceInfo: `relation (${rel.name})`
          });
        }
      } else if (eff.resolvedMode === "partial") {
        for (const tk of tKeys) {
          cols.push({
            name: `${target.name.toLowerCase()}_${tk.name}`,
            cqlType: eff.isArray ? `SET<${toCqlType(tk.attrType)}>` : toCqlType(tk.attrType),
            role: "incrusted-partial",
            sourceInfo: `reference key (${target.name})`
          });
        }
        for (const inc of eff.incrustedAttrs) {
          cols.push({
            name: `${target.name.toLowerCase()}_${inc.name}`,
            cqlType: eff.isArray ? `LIST<${toCqlType(inc.attrType)}>` : toCqlType(inc.attrType),
            role: "incrusted-partial",
            sourceInfo: `partial incrustation (${rel.name} -> ${target.name})`
          });
        }
      } else {
        for (const tk of tKeys) {
          cols.push({
            name: `${target.name.toLowerCase()}_${tk.name}`,
            cqlType: eff.isArray ? `SET<${toCqlType(tk.attrType)}>` : toCqlType(tk.attrType),
            role: "regular",
            sourceInfo: `foreign ref (${rel.name} -> ${target.name})`
          });
        }
      }
    }

    families.push({
      name: elem.name,
      partitionKeys: pks,
      clusteringKeys: cks,
      columns: cols
    });
  }

  const cqlLines: string[] = [
    `-- Apache Cassandra Wide-Column Schema (${cfg.dbName})`,
    `CREATE KEYSPACE IF NOT EXISTS ${cfg.dbName.toLowerCase()} WITH replication = {'class': 'SimpleStrategy', 'replication_factor': 1};`,
    ""
  ];
  if (deletedFamilies.length > 0) {
    cqlLines.push(
      `-- Absorbed & Deleted Column Families: ${deletedFamilies
        .map((d) => `${d.targetName} (into ${d.absorbedInto.join(", ")})`)
        .join("; ")}`,
      ""
    );
  }
  for (const cf of families) {
    const colDefs = cf.columns.map(
      (c) => `  ${c.name} ${c.cqlType} /* ${c.role}: ${c.sourceInfo} */`
    );
    const pkPart =
      cf.partitionKeys.length > 1
        ? `(${cf.partitionKeys.join(", ")})`
        : cf.partitionKeys.join(", ");
    const fullPk =
      cf.clusteringKeys.length > 0
        ? `(${pkPart}, ${cf.clusteringKeys.join(", ")})`
        : `(${pkPart})`;
    cqlLines.push(
      `CREATE TABLE ${cfg.dbName.toLowerCase()}.${cf.name.toLowerCase()} (\n${colDefs.join(
        ",\n"
      )},\n  PRIMARY KEY ${fullPk}\n);`,
      ""
    );
  }

  const xmlOutput =
    `<?xml version="1.0" encoding="UTF-8"?>\n` +
    `<ColumnFamilyDatabase name="${xmlAttr(cfg.dbName)}" model="WideColumn">\n` +
    (deletedFamilies.length > 0
      ? `  <AbsorbedDeletedColumnFamilies>\n` +
        deletedFamilies
          .map(
            (d) =>
              `    <DeletedColumnFamily name="${xmlAttr(
                d.targetName
              )}" absorbedInto="${xmlAttr(d.absorbedInto.join("; "))}" />\n`
          )
          .join("") +
        `  </AbsorbedDeletedColumnFamilies>\n`
      : "") +
    families
      .map(
        (cf) =>
          `  <ColumnFamily name="${xmlAttr(cf.name)}">\n` +
          `    <PartitionKey columns="${xmlAttr(cf.partitionKeys.join(", "))}" />\n` +
          (cf.clusteringKeys.length > 0
            ? `    <ClusteringKey columns="${xmlAttr(
                cf.clusteringKeys.join(", ")
              )}" />\n`
            : "") +
          cf.columns
            .map(
              (c) =>
                `    <Column name="${xmlAttr(c.name)}" cqlType="${xmlAttr(
                  c.cqlType
                )}" role="${xmlAttr(c.role)}" source="${xmlAttr(
                  c.sourceInfo
                )}" />\n`
            )
            .join("") +
          `  </ColumnFamily>\n`
      )
      .join("") +
    `</ColumnFamilyDatabase>`;

  return {
    families,
    deletedFamilies,
    cqlScript: cqlLines.join("\n"),
    xmlOutput
  };
}

// ---------------------------------------------------------------------------
// 4. Key-Value Model (Redis Keyspace & KV XML)
// ---------------------------------------------------------------------------

export interface KeyValueBucketSchema {
  entityName: string;
  keyPattern: string;
  valueFields: { name: string; type: string; origin: string }[];
  secondaryIndexKeys: string[];
}

export interface KeyValueModelOutput {
  buckets: KeyValueBucketSchema[];
  deletedBuckets: TableDeletionCheck[];
  redisScript: string;
  xmlOutput: string;
}

export function convertDerToKeyValueModel(
  diagram: DerDiagramData,
  cfg: DidConfig
): KeyValueModelOutput {
  const checks = analyzeTableDeletions(diagram, cfg);
  const deletedBuckets = checks.filter((c) => c.actuallyDeleted);
  const deletedIds = new Set(deletedBuckets.map((c) => c.targetId));

  const buckets: KeyValueBucketSchema[] = [];

  for (const elem of diagram.elements) {
    if (deletedIds.has(elem.id)) continue;

    const pks = elementKeyAttrs(elem, diagram);
    const keyPattern = `${elem.name.toLowerCase()}:${pks
      .map((k) => `{${k.name}}`)
      .join(":")}`;

    const valueFields: { name: string; type: string; origin: string }[] =
      elem.attributes.map((a) => ({
        name: a.name,
        type: a.attrType,
        origin: a.isKey ? "key" : "own"
      }));
    const secondaryIndexKeys: string[] = [];

    const outRels = diagram.relations.filter((r) => r.sourceId === elem.id);
    for (const rel of outRels) {
      const target = diagram.elements.find((e) => e.id === rel.targetId);
      if (!target) continue;
      const eff = effectiveIncrustation(cfg, rel, target);
      const tKeys = elementKeyAttrs(target, diagram);

      if (eff.resolvedMode === "complete" && target.id !== elem.id) {
        const subFields = target.attributes
          .map((a) => `${a.name}:${a.attrType}`)
          .join(", ");
        valueFields.push({
          name: rel.name.toLowerCase(),
          type: eff.isArray ? `JSON_ARRAY<{${subFields}}>` : `JSON_OBJ<{${subFields}}>`,
          origin: `complete incrustation (${target.name}${
            deletedIds.has(target.id) ? ", table deleted" : ""
          })`
        });
      } else if (eff.resolvedMode === "partial") {
        const subFields = [
          ...tKeys.map((k) => `${k.name}:${k.attrType}`),
          ...eff.incrustedAttrs.map((a) => `${a.name}:${a.attrType}`)
        ].join(", ");
        valueFields.push({
          name: `${rel.name.toLowerCase()}_cached`,
          type: eff.isArray ? `JSON_ARRAY<{${subFields}}>` : `JSON_OBJ<{${subFields}}>`,
          origin: `partial incrustation (${target.name})`
        });
      } else {
        const targetKeyRef = `${target.name.toLowerCase()}:${tKeys
          .map((k) => `{${k.name}}`)
          .join(":")}`;
        if (eff.isArray) {
          secondaryIndexKeys.push(
            `${keyPattern}:${rel.name.toLowerCase()} -> SET<${targetKeyRef}>`
          );
        } else {
          valueFields.push({
            name: `${rel.name.toLowerCase()}_ref`,
            type: `KEY_REF<${targetKeyRef}>`,
            origin: `reference (${target.name})`
          });
        }
      }
    }

    buckets.push({
      entityName: elem.name,
      keyPattern,
      valueFields,
      secondaryIndexKeys
    });
  }

  const redisLines: string[] = [
    `# Redis Key-Value Store Commands (${cfg.dbName})`
  ];
  if (deletedBuckets.length > 0) {
    redisLines.push(
      `# Absorbed & Deleted Standalone Keyspaces: ${deletedBuckets
        .map((d) => `${d.targetName} (into ${d.absorbedInto.join(", ")})`)
        .join("; ")}`
    );
  }
  for (const b of buckets) {
    const fieldPairs = b.valueFields
      .map((f) => `${f.name} "<${f.type}>"`)
      .join(" ");
    redisLines.push(`HSET ${b.keyPattern} ${fieldPairs}`);
    for (const sec of b.secondaryIndexKeys) {
      redisLines.push(`# Index Set: ${sec}`);
    }
  }

  const xmlOutput =
    `<?xml version="1.0" encoding="UTF-8"?>\n` +
    `<KeyValueDatabase name="${xmlAttr(cfg.dbName)}" model="KeyValue">\n` +
    (deletedBuckets.length > 0
      ? `  <AbsorbedDeletedKeyspaces>\n` +
        deletedBuckets
          .map(
            (d) =>
              `    <DeletedKeyspace entity="${xmlAttr(
                d.targetName
              )}" absorbedInto="${xmlAttr(d.absorbedInto.join("; "))}" />\n`
          )
          .join("") +
        `  </AbsorbedDeletedKeyspaces>\n`
      : "") +
    buckets
      .map(
        (b) =>
          `  <KeySpace entity="${xmlAttr(b.entityName)}" keyPattern="${xmlAttr(
            b.keyPattern
          )}">\n` +
          b.valueFields
            .map(
              (f) =>
                `    <ValueField name="${xmlAttr(f.name)}" type="${xmlAttr(
                  f.type
                )}" origin="${xmlAttr(f.origin)}" />\n`
            )
            .join("") +
          b.secondaryIndexKeys
            .map((s) => `    <IndexSet pattern="${xmlAttr(s)}" />\n`)
            .join("") +
          `  </KeySpace>\n`
      )
      .join("") +
    `</KeyValueDatabase>`;

  return {
    buckets,
    deletedBuckets,
    redisScript: redisLines.join("\n"),
    xmlOutput
  };
}
