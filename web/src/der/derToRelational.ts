// TypeScript implementation of `dafny/der/Types.dfy`, `Model.dfy`,
// `RelationalModel.dfy`, and `DerToRelational.dfy`, plus diagram presets
// and localStorage persistence (including straight-line corner waypoints).

import type {
  Attribute,
  AttrTypeKind,
  Cardinality,
  Column,
  DerAggregation,
  DerDiagramData,
  DerElement,
  DerEntity,
  DerRelation,
  ForeignKey,
  RelationClassKind,
  RelationKind,
  RelationalSchema,
  TableSchema
} from "./types";

// ---------------------------------------------------------------------------
// Cardinality & Atomic Type helpers (`dafny/der/Types.dfy`)
// ---------------------------------------------------------------------------

export function isAtomicType(t: AttrTypeKind): boolean {
  return !t.startsWith("SET<");
}

export function baseAtomicType(t: AttrTypeKind): AttrTypeKind {
  if (t === "SET<STRING>") return "STRING";
  if (t === "SET<INT>") return "INT";
  return t;
}

export function validCardinality(c: Cardinality): boolean {
  if (c.min < 0) return false;
  if (c.max === "*") return true;
  return c.max >= 1 && c.min <= c.max;
}

export function isSingle(c: Cardinality): boolean {
  return validCardinality(c) && c.max === 1;
}

export function isMany(c: Cardinality): boolean {
  if (!validCardinality(c)) return false;
  return c.max === "*" || c.max > 1;
}

export function classifyRelation(src: Cardinality, dst: Cardinality): RelationKind {
  if (isSingle(src) && isSingle(dst)) return "1:1";
  if (isSingle(src) && isMany(dst)) return "1:N";
  if (isMany(src) && isMany(dst)) return "N:M";
  return "N:1";
}

export function defaultCardinalitiesForClass(
  classKind: RelationClassKind
): { sourceCard: Cardinality; targetCard: Cardinality } {
  switch (classKind) {
    case "OneToOneRelation":
      return { sourceCard: { min: 1, max: 1 }, targetCard: { min: 0, max: 1 } };
    case "OneToManyRelation":
      return { sourceCard: { min: 1, max: 1 }, targetCard: { min: 1, max: "*" } };
    case "ManyToManyRelation":
      return { sourceCard: { min: 0, max: "*" }, targetCard: { min: 1, max: "*" } };
    case "GeneralRelation":
      return { sourceCard: { min: 2, max: 5 }, targetCard: { min: 1, max: "*" } };
  }
}

export function formatCardinality(c: Cardinality): string {
  return `${c.min}..${c.max}`;
}

export function relationKindOf(rel: DerRelation): RelationKind {
  switch (rel.classKind) {
    case "OneToOneRelation":
      return "1:1";
    case "OneToManyRelation":
      return "1:N";
    case "ManyToManyRelation":
      return "N:M";
    case "GeneralRelation":
      return classifyRelation(rel.sourceCard, rel.targetCard);
  }
}

// ---------------------------------------------------------------------------
// DER -> Relational Model Converter (`dafny/der/DerToRelational.dfy`)
// ---------------------------------------------------------------------------

function filterKeyAttrs(attrs: Attribute[]): Attribute[] {
  return attrs.filter((a) => a.isKey);
}

function attrsToColumns(attrs: Attribute[]): Column[] {
  return attrs.map((a) => ({ name: a.name, colType: a.attrType }));
}

function attrNames(attrs: Attribute[]): string[] {
  return attrs.map((a) => a.name);
}

function prefixedAttrs(prefix: string, attrs: Attribute[]): Attribute[] {
  return attrs.map((a) => ({
    name: `${prefix}_${a.name}`,
    attrType: a.attrType,
    isKey: a.isKey
  }));
}

export function elementKeyAttrs(
  elem: DerElement,
  diagram: DerDiagramData
): Attribute[] {
  if (elem.kind === "entity") {
    const keys = filterKeyAttrs(elem.attributes);
    return keys.length > 0 ? keys : elem.attributes.slice(0, 1);
  }
  const innerRel = diagram.relations.find((r) => r.id === elem.innerRelationId);
  if (!innerRel) {
    return elem.attributes.slice(0, 1);
  }
  const srcElem = diagram.elements.find((e) => e.id === innerRel.sourceId);
  const dstElem = diagram.elements.find((e) => e.id === innerRel.targetId);
  const srcKeys = srcElem && srcElem.kind === "entity" ? filterKeyAttrs(srcElem.attributes) : [];
  const dstKeys = dstElem && dstElem.kind === "entity" ? filterKeyAttrs(dstElem.attributes) : [];
  const pSrc = srcElem ? prefixedAttrs(srcElem.name, srcKeys) : [];
  const pDst = dstElem ? prefixedAttrs(dstElem.name, dstKeys) : [];

  const kind = relationKindOf(innerRel);
  switch (kind) {
    case "N:M":
      return [...pSrc, ...pDst];
    case "1:N":
      return pDst;
    case "N:1":
      return pSrc;
    case "1:1":
      return pSrc;
  }
}

function buildEntityTable(e: DerEntity): TableSchema {
  const keyAttrs = filterKeyAttrs(e.attributes);
  const effectiveKeys = keyAttrs.length > 0 ? keyAttrs : e.attributes.slice(0, 1);
  return {
    name: e.name,
    columns: attrsToColumns(e.attributes),
    primaryKey: attrNames(effectiveKeys),
    foreignKeys: [],
    originKind: "entity"
  };
}

function buildAggregationTable(
  agg: DerAggregation,
  diagram: DerDiagramData
): TableSchema | null {
  const innerRel = diagram.relations.find((r) => r.id === agg.innerRelationId);
  if (!innerRel) return null;
  const src = diagram.elements.find((e) => e.id === innerRel.sourceId);
  const dst = diagram.elements.find((e) => e.id === innerRel.targetId);
  if (!src || !dst) return null;

  const srcKeys = elementKeyAttrs(src, diagram);
  const dstKeys = elementKeyAttrs(dst, diagram);
  const pSrcAttrs = prefixedAttrs(src.name, srcKeys);
  const pDstAttrs = prefixedAttrs(dst.name, dstKeys);

  const allCols: Column[] = [
    ...attrsToColumns(pSrcAttrs),
    ...attrsToColumns(pDstAttrs),
    ...attrsToColumns(innerRel.attributes),
    ...attrsToColumns(agg.attributes)
  ];

  const pSrcNames = attrNames(pSrcAttrs);
  const pDstNames = attrNames(pDstAttrs);
  const pk = attrNames(elementKeyAttrs(agg, diagram));

  const fks: ForeignKey[] = [
    { columns: pSrcNames, refTable: src.name, refColumns: attrNames(srcKeys) },
    { columns: pDstNames, refTable: dst.name, refColumns: attrNames(dstKeys) }
  ];

  return {
    name: agg.name,
    columns: allCols,
    primaryKey: pk,
    foreignKeys: fks,
    originKind: "aggregation"
  };
}

function buildManyToManyTable(
  rel: DerRelation,
  src: DerElement,
  dst: DerElement,
  diagram: DerDiagramData
): TableSchema {
  const srcKeys = elementKeyAttrs(src, diagram);
  const dstKeys = elementKeyAttrs(dst, diagram);
  const pSrcAttrs = prefixedAttrs(src.name, srcKeys);
  const pDstAttrs = prefixedAttrs(dst.name, dstKeys);
  const sameEndpoint = src.id === dst.id;
  const effectiveDstAttrs = sameEndpoint
    ? prefixedAttrs(`${dst.name}_dest`, dstKeys)
    : pDstAttrs;

  const allCols: Column[] = [
    ...attrsToColumns(pSrcAttrs),
    ...attrsToColumns(effectiveDstAttrs),
    ...attrsToColumns(rel.attributes)
  ];

  const pSrcNames = attrNames(pSrcAttrs);
  const pDstNames = attrNames(effectiveDstAttrs);

  return {
    name: rel.name,
    columns: allCols,
    primaryKey: [...pSrcNames, ...pDstNames],
    foreignKeys: [
      { columns: pSrcNames, refTable: src.name, refColumns: attrNames(srcKeys) },
      { columns: pDstNames, refTable: dst.name, refColumns: attrNames(dstKeys) }
    ],
    originKind: "nm-relation"
  };
}

function appendForeignKeyToTable(
  tables: TableSchema[],
  hostTableName: string,
  refTableName: string,
  refKeyAttrs: Attribute[],
  relAttrs: Attribute[]
): TableSchema[] {
  const pRefAttrs = prefixedAttrs(refTableName, refKeyAttrs);
  const fkCols = attrsToColumns(pRefAttrs);
  const extraCols = attrsToColumns(relAttrs);
  const fkNames = attrNames(pRefAttrs);
  const refNames = attrNames(refKeyAttrs);
  const newFk: ForeignKey = {
    columns: fkNames,
    refTable: refTableName,
    refColumns: refNames
  };

  return tables.map((cur) => {
    if (cur.name !== hostTableName) return cur;
    const existingNames = new Set(cur.columns.map((c) => c.name));
    const addedCols = [...fkCols, ...extraCols].filter((c) => !existingNames.has(c.name));
    return {
      ...cur,
      columns: [...cur.columns, ...addedCols],
      foreignKeys: [...cur.foreignKeys, newFk]
    };
  });
}

function isAggregatedRelation(diagram: DerDiagramData, relId: string): boolean {
  return diagram.elements.some(
    (e) => e.kind === "aggregation" && e.innerRelationId === relId
  );
}

export function convertDerToRelational(diagram: DerDiagramData): RelationalSchema {
  let tables: TableSchema[] = [];

  // Pass 1 & 2: Entities and Aggregations
  for (const elem of diagram.elements) {
    if (elem.kind === "entity") {
      tables.push(buildEntityTable(elem));
    } else {
      const aggTbl = buildAggregationTable(elem, diagram);
      if (aggTbl) tables.push(aggTbl);
    }
  }

  // Pass 3: Non-aggregated Relations
  for (const rel of diagram.relations) {
    if (isAggregatedRelation(diagram, rel.id)) continue;
    const src = diagram.elements.find((e) => e.id === rel.sourceId);
    const dst = diagram.elements.find((e) => e.id === rel.targetId);
    if (!src || !dst) continue;

    const kind = relationKindOf(rel);
    switch (kind) {
      case "N:M": {
        tables.push(buildManyToManyTable(rel, src, dst, diagram));
        break;
      }
      case "1:N": {
        tables = appendForeignKeyToTable(
          tables,
          dst.name,
          src.name,
          elementKeyAttrs(src, diagram),
          rel.attributes
        );
        break;
      }
      case "N:1": {
        tables = appendForeignKeyToTable(
          tables,
          src.name,
          dst.name,
          elementKeyAttrs(dst, diagram),
          rel.attributes
        );
        break;
      }
      case "1:1": {
        tables = appendForeignKeyToTable(
          tables,
          dst.name,
          src.name,
          elementKeyAttrs(src, diagram),
          rel.attributes
        );
        break;
      }
    }
  }

  return { tables };
}

// ---------------------------------------------------------------------------
// Generic SQL DDL Generator
// ---------------------------------------------------------------------------

function sqlTypeFor(t: AttrTypeKind): string {
  switch (t) {
    case "INT":
      return "INTEGER";
    case "STRING":
      return "VARCHAR(255)";
    case "BOOL":
      return "BOOLEAN";
    case "DATE":
      return "DATE";
    case "DECIMAL":
      return "DECIMAL(10, 2)";
    case "SET<STRING>":
      return "TEXT /* NON-ATOMIC SET<STRING> */";
    case "SET<INT>":
      return "TEXT /* NON-ATOMIC SET<INT> */";
  }
}

export function generateGenericSqlDDL(tables: TableSchema[]): string {
  return tables
    .map((t) => {
      const colLines = t.columns.map((c) => {
        const notNull = t.primaryKey.includes(c.name) ? " NOT NULL" : "";
        return `  ${c.name} ${sqlTypeFor(c.colType)}${notNull}`;
      });
      const pkLine =
        t.primaryKey.length > 0
          ? [`  PRIMARY KEY (${t.primaryKey.join(", ")})`]
          : [];
      const fkLines = t.foreignKeys.map(
        (fk) =>
          `  FOREIGN KEY (${fk.columns.join(", ")}) REFERENCES ${fk.refTable}(${fk.refColumns.join(", ")})`
      );
      const body = [...colLines, ...pkLine, ...fkLines].join(",\n");
      return `CREATE TABLE ${t.name} (\n${body}\n);`;
    })
    .join("\n\n");
}

// ---------------------------------------------------------------------------
// Built-in Preset DER Diagrams & LocalStorage Persistence
// ---------------------------------------------------------------------------

export const PRESET_DER_DIAGRAMS: DerDiagramData[] = [
  {
    id: "preset-university-hr",
    title: "1. Full DER (1:1, 1:N, N:M, General 2..5 & Aggregation)",
    description:
      "Mirrors dafny/der/Main.dfy: Persona-Pasaporte (1:1), Departamento-Empleado (1:N), Departamento-Colabora (2..5 -> 1..*), and Aggregation Cursada(Alumno-Cursa-Materia) -> Examen (1:N).",
    elements: [
      {
        id: "ent-persona",
        kind: "entity",
        name: "Persona",
        position: { x: 110, y: 95 },
        attributes: [
          { name: "dni", attrType: "INT", isKey: true },
          { name: "nombre", attrType: "STRING", isKey: false }
        ]
      },
      {
        id: "ent-pasaporte",
        kind: "entity",
        name: "Pasaporte",
        isWeak: true,
        position: { x: 470, y: 95 },
        attributes: [
          { name: "numero", attrType: "STRING", isKey: true },
          { name: "vencimiento", attrType: "DATE", isKey: false }
        ]
      },
      {
        id: "ent-depto",
        kind: "entity",
        name: "Departamento",
        position: { x: 780, y: 110 },
        attributes: [
          { name: "codigo", attrType: "INT", isKey: true },
          { name: "nombre", attrType: "STRING", isKey: false }
        ]
      },
      {
        id: "ent-empleado",
        kind: "entity",
        name: "Empleado",
        position: { x: 780, y: 390 },
        attributes: [
          { name: "legajo", attrType: "INT", isKey: true },
          { name: "salario", attrType: "DECIMAL", isKey: false }
        ]
      },
      {
        id: "ent-alumno",
        kind: "entity",
        name: "Alumno",
        position: { x: 120, y: 280 },
        attributes: [
          { name: "padron", attrType: "INT", isKey: true },
          { name: "nombre", attrType: "STRING", isKey: false }
        ]
      },
      {
        id: "ent-materia",
        kind: "entity",
        name: "Materia",
        position: { x: 480, y: 280 },
        attributes: [
          { name: "codigo", attrType: "STRING", isKey: true },
          { name: "creditos", attrType: "INT", isKey: false }
        ]
      },
      {
        id: "agg-cursada",
        kind: "aggregation",
        name: "Cursada",
        innerRelationId: "rel-cursa",
        position: { x: 300, y: 280 },
        attributes: [{ name: "estado", attrType: "STRING", isKey: false }]
      },
      {
        id: "ent-examen",
        kind: "entity",
        name: "Examen",
        isWeak: true,
        position: { x: 300, y: 500 },
        attributes: [
          { name: "id_examen", attrType: "INT", isKey: true },
          { name: "nota", attrType: "DECIMAL", isKey: false }
        ]
      }
    ],
    relations: [
      {
        id: "rel-tiene",
        name: "Tiene",
        classKind: "OneToOneRelation",
        sourceId: "ent-persona",
        targetId: "ent-pasaporte",
        sourceCard: { min: 1, max: 1 },
        targetCard: { min: 0, max: 1 },
        attributes: [],
        position: { x: 290, y: 95 },
        sourceCorners: [],
        targetCorners: []
      },
      {
        id: "rel-emplea",
        name: "Emplea",
        classKind: "OneToManyRelation",
        sourceId: "ent-depto",
        targetId: "ent-empleado",
        sourceCard: { min: 1, max: 1 },
        targetCard: { min: 1, max: "*" },
        attributes: [{ name: "fecha_ingreso", attrType: "DATE", isKey: false }],
        position: { x: 780, y: 250 },
        sourceCorners: [],
        targetCorners: []
      },
      {
        id: "rel-colabora",
        name: "Colabora",
        classKind: "GeneralRelation",
        sourceId: "ent-depto",
        targetId: "ent-depto",
        sourceCard: { min: 2, max: 5 },
        targetCard: { min: 1, max: "*" },
        attributes: [],
        position: { x: 965, y: 110 },
        sourceCorners: [{ x: 880, y: 60 }, { x: 965, y: 60 }],
        targetCorners: [{ x: 965, y: 165 }, { x: 880, y: 165 }]
      },
      {
        id: "rel-cursa",
        name: "Cursa",
        classKind: "ManyToManyRelation",
        sourceId: "ent-alumno",
        targetId: "ent-materia",
        sourceCard: { min: 0, max: "*" },
        targetCard: { min: 1, max: "*" },
        attributes: [{ name: "cuatrimestre", attrType: "STRING", isKey: false }],
        position: { x: 300, y: 280 },
        sourceCorners: [],
        targetCorners: []
      },
      {
        id: "rel-evaluada",
        name: "EvaluadaPor",
        classKind: "OneToManyRelation",
        sourceId: "agg-cursada",
        targetId: "ent-examen",
        sourceCard: { min: 1, max: 1 },
        targetCard: { min: 0, max: "*" },
        attributes: [{ name: "instancia", attrType: "STRING", isKey: false }],
        position: { x: 300, y: 410 },
        sourceCorners: [],
        targetCorners: []
      }
    ],
    extraFDsByTable: {}
  },
  {
    id: "preset-2nf-3nf-inscripcion",
    title: "2. 2NF & 3NF Demo (Partial & Transitive Dependencies)",
    description:
      "Inscripcion(padron*, cod_materia*, nombre_alumno, cod_depto, nombre_depto, nota) with partial FDs {padron}->{nombre_alumno}, {cod_materia}->{cod_depto} and transitive FD {cod_depto}->{nombre_depto}.",
    elements: [
      {
        id: "ent-inscripcion",
        kind: "entity",
        name: "Inscripcion",
        position: { x: 380, y: 220 },
        attributes: [
          { name: "padron", attrType: "INT", isKey: true },
          { name: "cod_materia", attrType: "STRING", isKey: true },
          { name: "nombre_alumno", attrType: "STRING", isKey: false },
          { name: "cod_depto", attrType: "INT", isKey: false },
          { name: "nombre_depto", attrType: "STRING", isKey: false },
          { name: "nota", attrType: "DECIMAL", isKey: false }
        ]
      }
    ],
    relations: [],
    extraFDsByTable: {
      Inscripcion: [
        { id: "fd-1", lhs: ["padron"], rhs: ["nombre_alumno"] },
        { id: "fd-2", lhs: ["cod_materia"], rhs: ["cod_depto"] },
        { id: "fd-3", lhs: ["cod_depto"], rhs: ["nombre_depto"] }
      ]
    }
  },
  {
    id: "preset-bcnf-direccion",
    title: "3. BCNF vs 3NF Trade-off (Direccion: Lossless but Loses FD)",
    description:
      "Direccion(ciudad*, calle*, cp) with {ciudad, calle} -> {cp} and {cp} -> {ciudad}. In 3NF, but violates BCNF because cp is not a superkey.",
    elements: [
      {
        id: "ent-direccion",
        kind: "entity",
        name: "Direccion",
        position: { x: 380, y: 220 },
        attributes: [
          { name: "ciudad", attrType: "STRING", isKey: true },
          { name: "calle", attrType: "STRING", isKey: true },
          { name: "cp", attrType: "STRING", isKey: false }
        ]
      }
    ],
    relations: [],
    extraFDsByTable: {
      Direccion: [
        { id: "fd-cp-ciudad", lhs: ["cp"], rhs: ["ciudad"] }
      ]
    }
  },
  {
    id: "preset-1nf-cliente",
    title: "4. Unnormalized -> 1NF (Multi-Valued Attribute telefonos)",
    description:
      "Cliente(id_cliente*, nombre, telefonos: SET<STRING>) violating 1NF due to a multi-valued column; 1NF converter extracts Cliente_telefonos.",
    elements: [
      {
        id: "ent-cliente",
        kind: "entity",
        name: "Cliente",
        position: { x: 240, y: 220 },
        attributes: [
          { name: "id_cliente", attrType: "INT", isKey: true },
          { name: "nombre", attrType: "STRING", isKey: false },
          { name: "telefonos", attrType: "SET<STRING>", isKey: false }
        ]
      },
      {
        id: "ent-pedido",
        kind: "entity",
        name: "Pedido",
        position: { x: 640, y: 220 },
        attributes: [
          { name: "id_pedido", attrType: "INT", isKey: true },
          { name: "total", attrType: "DECIMAL", isKey: false }
        ]
      }
    ],
    relations: [
      {
        id: "rel-realiza",
        name: "Realiza",
        classKind: "OneToManyRelation",
        sourceId: "ent-cliente",
        targetId: "ent-pedido",
        sourceCard: { min: 1, max: 1 },
        targetCard: { min: 0, max: "*" },
        attributes: [],
        position: { x: 440, y: 220 },
        sourceCorners: [],
        targetCorners: []
      }
    ],
    extraFDsByTable: {}
  }
];

const STORAGE_KEY = "ddbb_der_saved_diagrams_v1";

export function cloneDiagram(d: DerDiagramData): DerDiagramData {
  return JSON.parse(JSON.stringify(d)) as DerDiagramData;
}

export function loadSavedDiagrams(): DerDiagramData[] {
  try {
    const raw = window.localStorage.getItem(STORAGE_KEY);
    if (!raw) return PRESET_DER_DIAGRAMS.map(cloneDiagram);
    const parsed = JSON.parse(raw) as DerDiagramData[];
    if (!Array.isArray(parsed) || parsed.length === 0) {
      return PRESET_DER_DIAGRAMS.map(cloneDiagram);
    }
    return parsed;
  } catch {
    return PRESET_DER_DIAGRAMS.map(cloneDiagram);
  }
}

export function saveDiagramsToStorage(diagrams: DerDiagramData[]): void {
  try {
    window.localStorage.setItem(STORAGE_KEY, JSON.stringify(diagrams));
  } catch {
    // Ignore storage quota errors in restricted environments
  }
}
