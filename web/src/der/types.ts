// Domain types mirroring `dafny/der/Types.dfy`, `Model.dfy`,
// `RelationalModel.dfy`, `FunctionalDeps.dfy`, `DecompositionAnalysis.dfy`,
// and `Normalization.dfy`, plus 2D canvas positions and editable polyline corners.

export interface Point {
  x: number;
  y: number;
}

export type AttrTypeKind =
  | "INT"
  | "STRING"
  | "BOOL"
  | "DATE"
  | "DECIMAL"
  | "SET<STRING>"
  | "SET<INT>";

export interface Attribute {
  name: string;
  attrType: AttrTypeKind;
  isKey: boolean;
}

// Bound: finite positive number or "*" (Unbounded)
export interface Cardinality {
  min: number;
  max: number | "*";
}

export type RelationKind = "1:1" | "1:N" | "N:M" | "N:1";

export type RelationClassKind =
  | "OneToOneRelation"
  | "OneToManyRelation"
  | "ManyToManyRelation"
  | "GeneralRelation";

// Relation node in the DER diagram (owned by `sourceId`, pointing to `targetId`).
// Positioned as a diamond on the canvas with straight-line polylines and
// user-editable corner waypoints on both the source->diamond and diamond->target legs.
export interface DerRelation {
  id: string;
  name: string;
  classKind: RelationClassKind;
  sourceId: string; // Entity or Aggregation ID
  targetId: string; // Entity or Aggregation ID
  sourceCard: Cardinality;
  targetCard: Cardinality;
  attributes: Attribute[];
  position: Point; // Diamond center on canvas
  sourceCorners: Point[]; // Intermediate straight-line corners from source -> diamond
  targetCorners: Point[]; // Intermediate straight-line corners from diamond -> target
}

export interface DerEntity {
  id: string;
  kind: "entity";
  name: string;
  attributes: Attribute[];
  position: Point;
}

export interface DerAggregation {
  id: string;
  kind: "aggregation";
  name: string;
  innerRelationId: string; // Composes (innerRelation.sourceId --[innerRelationId]--> innerRelation.targetId)
  attributes: Attribute[];
  position: Point;
}

export type DerElement = DerEntity | DerAggregation;

export interface FunctionalDepInput {
  id: string;
  lhs: string[];
  rhs: string[];
}

export interface DerDiagramData {
  id: string;
  title: string;
  description: string;
  elements: DerElement[];
  relations: DerRelation[];
  // Extra user-specified Functional Dependencies per RM table name
  extraFDsByTable: Record<string, FunctionalDepInput[]>;
}

// ---------------------------------------------------------------------------
// Relational Model (RM) types (`dafny/der/RelationalModel.dfy`)
// ---------------------------------------------------------------------------

export interface Column {
  name: string;
  colType: AttrTypeKind;
}

export interface ForeignKey {
  columns: string[];
  refTable: string;
  refColumns: string[];
}

export interface TableSchema {
  name: string;
  columns: Column[];
  primaryKey: string[];
  foreignKeys: ForeignKey[];
  originKind: "entity" | "aggregation" | "nm-relation" | "normalized";
}

export interface RelationalSchema {
  tables: TableSchema[];
}

// ---------------------------------------------------------------------------
// Normalization & Decomposition Analysis types
// ---------------------------------------------------------------------------

export type NormalForm = "UNF" | "1NF" | "2NF" | "3NF" | "BCNF";

export interface FD {
  lhs: string[];
  rhs: string[];
}

export interface NormalizedRelation {
  table: TableSchema;
  fds: FD[];
}

export interface ValidationReport {
  tableName: string;
  is1NF: boolean;
  is2NF: boolean;
  is3NF: boolean;
  isBCNF: boolean;
  highestForm: NormalForm;
  candidateKeys: string[][];
  primeAttributes: string[];
  violations: string[];
}

export interface ChaseCell {
  distinguished: boolean;
  label: string; // e.g. "a1" or "b2,1"
  rowId: number;
}

export interface DecompositionReport {
  losslessJoin: boolean;
  dependencyPreserving: boolean;
  lostDependencies: FD[];
  initialTableau: ChaseCell[][];
  finalTableau: ChaseCell[][];
  tableauColNames: string[];
  tableauRowNames: string[];
}
