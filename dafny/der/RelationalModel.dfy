// Relational Model (RM) representation:
//   - Column(name, colType)
//   - ForeignKey(columns, refTable, refColumns)
//   - TableSchema(name, columns, primaryKey, foreignKeys)
//   - RelationalSchema(tables)
//
// Includes well-formedness invariants (`ValidTable`, `ValidRelationalSchema`),
// append-preservation lemmas, and human-readable Relational Model formatters.

include "Types.dfy"

module RelationalModel {
  import opened DerTypes

  datatype Column = Column(
    name: Name,
    colType: AttrType
  )

  datatype ForeignKey = ForeignKey(
    columns: seq<Name>,
    refTable: Name,
    refColumns: seq<Name>
  )

  datatype TableSchema = TableSchema(
    name: Name,
    columns: seq<Column>,
    primaryKey: seq<Name>,
    foreignKeys: seq<ForeignKey>
  )

  datatype RelationalSchema = RelationalSchema(
    tables: seq<TableSchema>
  )

  // ---------------------------------------------------------------------------
  // Well-formedness predicates
  // ---------------------------------------------------------------------------

  predicate HasColumn(cols: seq<Column>, colName: Name)
  {
    exists i :: 0 <= i < |cols| && cols[i].name == colName
  }

  predicate ValidForeignKey(fk: ForeignKey, cols: seq<Column>)
  {
    fk.refTable != "" &&
    |fk.columns| > 0 &&
    |fk.columns| == |fk.refColumns| &&
    (forall i :: 0 <= i < |fk.columns| ==> HasColumn(cols, fk.columns[i]))
  }

  predicate ValidTable(t: TableSchema)
  {
    t.name != "" &&
    |t.primaryKey| > 0 &&
    (forall i :: 0 <= i < |t.primaryKey| ==> HasColumn(t.columns, t.primaryKey[i])) &&
    (forall i :: 0 <= i < |t.foreignKeys| ==> ValidForeignKey(t.foreignKeys[i], t.columns))
  }

  predicate ValidRelationalSchema(rm: RelationalSchema)
  {
    forall i :: 0 <= i < |rm.tables| ==> ValidTable(rm.tables[i])
  }

  predicate HasTable(rm: RelationalSchema, tableName: Name)
  {
    exists i :: 0 <= i < |rm.tables| && rm.tables[i].name == tableName
  }

  // ---------------------------------------------------------------------------
  // Column / FK preservation lemmas
  // ---------------------------------------------------------------------------

  lemma LemmaHasColumnLeft(c1: seq<Column>, c2: seq<Column>, colName: Name)
    requires HasColumn(c1, colName)
    ensures HasColumn(c1 + c2, colName)
  {
    var i :| 0 <= i < |c1| && c1[i].name == colName;
    assert (c1 + c2)[i].name == colName;
  }

  lemma LemmaHasColumnRight(c1: seq<Column>, c2: seq<Column>, colName: Name)
    requires HasColumn(c2, colName)
    ensures HasColumn(c1 + c2, colName)
  {
    var i :| 0 <= i < |c2| && c2[i].name == colName;
    assert (c1 + c2)[|c1| + i].name == colName;
  }

  lemma LemmaAppendColumnsPreservesFK(fk: ForeignKey, c1: seq<Column>, c2: seq<Column>)
    requires ValidForeignKey(fk, c1)
    ensures ValidForeignKey(fk, c1 + c2)
  {
    forall i | 0 <= i < |fk.columns|
      ensures HasColumn(c1 + c2, fk.columns[i])
    {
      LemmaHasColumnLeft(c1, c2, fk.columns[i]);
    }
  }

  // ---------------------------------------------------------------------------
  // Formatting helpers (classic RM notation: PK columns marked with *)
  // ---------------------------------------------------------------------------

  function JoinNames(names: seq<Name>): string
    decreases |names|
  {
    if |names| == 0 then ""
    else if |names| == 1 then names[0]
    else names[0] + ", " + JoinNames(names[1..])
  }

  function FormatColumn(col: Column, pk: seq<Name>): string
  {
    col.name + (if col.name in pk then "*" else "") + ": " + FormatAttrType(col.colType)
  }

  function FormatColumns(cols: seq<Column>, pk: seq<Name>): string
    decreases |cols|
  {
    if |cols| == 0 then ""
    else if |cols| == 1 then FormatColumn(cols[0], pk)
    else FormatColumn(cols[0], pk) + ", " + FormatColumns(cols[1..], pk)
  }

  function FormatForeignKey(fk: ForeignKey): string
  {
    "  FK (" + JoinNames(fk.columns) + ") -> " + fk.refTable + "(" + JoinNames(fk.refColumns) + ")"
  }

  function FormatForeignKeys(fks: seq<ForeignKey>): string
    decreases |fks|
  {
    if |fks| == 0 then ""
    else FormatForeignKey(fks[0]) + "\n" + FormatForeignKeys(fks[1..])
  }

  function FormatTableSchema(t: TableSchema): string
  {
    t.name + "(" + FormatColumns(t.columns, t.primaryKey) + ")\n" +
    "  PK (" + JoinNames(t.primaryKey) + ")\n" +
    FormatForeignKeys(t.foreignKeys)
  }

  function FormatTables(tables: seq<TableSchema>): string
    decreases |tables|
  {
    if |tables| == 0 then ""
    else FormatTableSchema(tables[0]) + FormatTables(tables[1..])
  }

  function FormatRelationalSchema(rm: RelationalSchema): string
  {
    FormatTables(rm.tables)
  }
}
