// Verified tests and runnable demonstration for the Dafny DER + Normalization module:
//   - Entities with primary keys and attributes
//   - Distinct generalized Relation classes: 1:1, 1:N, N:M, and General (min..max)
//   - Relations owned as a list inside each EntityElement
//   - Aggregation composing an inner relationship and participating in outer relations
//   - DER -> Relational Model conversion
//   - Normalization validators & converters (1NF, 2NF, 3NF, BCNF)
//   - Lossless-join (Chase) & dependency-preservation (Ullman) decomposition analysis

include "Types.dfy"
include "Model.dfy"
include "RelationalModel.dfy"
include "DerToRelational.dfy"
include "FunctionalDeps.dfy"
include "DecompositionAnalysis.dfy"
include "Normalization.dfy"

// Kept in its own module so Z3 verifies DER construction + DER -> RM
// conversion without loading FunctionalDeps / Normalization axioms.
module DerTests {
  import opened DerTypes
  import opened DerModel
  import opened RelationalModel
  import opened DerToRelational

  // Step 1: Creates and adds the 7 base entities while maintaining
  // `ConvertibleDiagram` incrementally (never revealing its quantifiers).
  method BuildBaseEntities()
    returns (
      diagram: DerDiagram,
      persona: Entity,
      pasaporte: Entity,
      departamento: Entity,
      empleado: Entity,
      alumno: Entity,
      materia: Entity,
      examen: Entity
    )
    ensures ConvertibleDiagram(diagram)
    ensures diagram.elements == [persona, pasaporte, departamento, empleado, alumno, materia, examen]
    ensures persona.name == "Persona" && persona.relations == []
    ensures pasaporte.name == "Pasaporte" && pasaporte.relations == []
    ensures departamento.name == "Departamento" && departamento.relations == []
    ensures empleado.name == "Empleado" && empleado.relations == []
    ensures alumno.name == "Alumno" && alumno.relations == []
    ensures materia.name == "Materia" && materia.relations == []
    ensures examen.name == "Examen" && examen.relations == []
    ensures fresh(diagram)
    ensures fresh(persona) && fresh(pasaporte) && fresh(departamento) &&
            fresh(empleado) && fresh(alumno) && fresh(materia) && fresh(examen)
    ensures persona.Repr == {persona} && pasaporte.Repr == {pasaporte} &&
            departamento.Repr == {departamento} && empleado.Repr == {empleado} &&
            alumno.Repr == {alumno} && materia.Repr == {materia} && examen.Repr == {examen}
  {
    diagram := new DerDiagram();
    LemmaEmptyDiagramConvertible(diagram);

    persona := new Entity("Persona", [
      Attribute("dni", AttrInt, true),
      Attribute("nombre", AttrString, false)
    ]);
    AddConvertibleEntity(diagram, persona);

    pasaporte := new Entity("Pasaporte", [
      Attribute("numero", AttrString, true),
      Attribute("vencimiento", AttrDate, false)
    ]);
    AddConvertibleEntity(diagram, pasaporte);

    departamento := new Entity("Departamento", [
      Attribute("codigo", AttrInt, true),
      Attribute("nombre", AttrString, false)
    ]);
    AddConvertibleEntity(diagram, departamento);

    empleado := new Entity("Empleado", [
      Attribute("legajo", AttrInt, true),
      Attribute("salario", AttrDecimal, false)
    ]);
    AddConvertibleEntity(diagram, empleado);

    alumno := new Entity("Alumno", [
      Attribute("padron", AttrInt, true),
      Attribute("nombre", AttrString, false)
    ]);
    AddConvertibleEntity(diagram, alumno);

    materia := new Entity("Materia", [
      Attribute("codigo", AttrString, true),
      Attribute("creditos", AttrInt, false)
    ]);
    AddConvertibleEntity(diagram, materia);

    examen := new Entity("Examen", [
      Attribute("id_examen", AttrInt, true),
      Attribute("nota", AttrDecimal, false)
    ]);
    AddConvertibleEntity(diagram, examen);
  }

  // Step 2: Links 1:1, 1:N, N:M, General relations and an Aggregation while
  // keeping `ConvertibleDiagram` completely opaque.
  method BuildSampleDiagram() returns (diagram: DerDiagram)
    ensures ConvertibleDiagram(diagram)
    ensures |diagram.elements| == 8
    ensures diagram.elements[0].name == "Persona"
    ensures diagram.elements[1].name == "Pasaporte"
    ensures diagram.elements[2].name == "Departamento"
    ensures diagram.elements[3].name == "Empleado"
    ensures diagram.elements[4].name == "Alumno"
    ensures diagram.elements[5].name == "Materia"
    ensures diagram.elements[6].name == "Examen"
    ensures diagram.elements[7].name == "Cursada"
  {
    var d, persona, pasaporte, departamento, empleado, alumno, materia, examen := BuildBaseEntities();
    diagram := d;

    // 2. 1:1 Relation: Persona (1..1) --[Tiene]--> Pasaporte (0..1)
    var relTiene := new OneToOneRelation(
      "Tiene", pasaporte, CardOne(), CardZeroOrOne(), []
    );
    assert relTiene.Kind() == KindOneToOne;
    LinkConvertibleRelation(diagram, persona, relTiene);
    assert |persona.relations| == 1;

    // 3. 1:N Relation: Departamento (1..1) --[Emplea]--> Empleado (1..*)
    var relEmplea := new OneToManyRelation(
      "Emplea", empleado, CardOne(), CardOneOrMany(), [
        Attribute("fecha_ingreso", AttrDate, false)
      ]
    );
    assert relEmplea.Kind() == KindOneToMany;
    LinkConvertibleRelation(diagram, departamento, relEmplea);

    // 4. N:M Relation: Alumno (0..*) --[Cursa]--> Materia (1..*)
    var relCursa := new ManyToManyRelation(
      "Cursa", materia, CardZeroOrMany(), CardOneOrMany(), [
        Attribute("cuatrimestre", AttrString, false)
      ]
    );
    assert relCursa.Kind() == KindManyToMany;
    LinkConvertibleRelation(diagram, alumno, relCursa);

    // 5. General Relation with custom finite bounds: Departamento (2..5) --[Colabora]--> Departamento (1..*)
    var relColabora := new GeneralRelation(
      "Colabora", departamento, CardRange(2, 5), CardAtLeast(1), []
    );
    assert relColabora.Kind() == KindManyToMany;
    LinkConvertibleRelation(diagram, departamento, relColabora);
    assert |departamento.relations| == 2;

    // 6. Aggregation: `Cursada` composes `(Alumno) --[Cursa]--> (Materia)` so
    //    it can participate in a 1:N relation `EvaluadaPor` with `Examen`!
    var cursada := new Aggregation("Cursada", alumno, relCursa, [
      Attribute("estado", AttrString, false)
    ]);
    AddConvertibleAggregation(diagram, cursada);

    var relEvaluadaPor := new OneToManyRelation(
      "EvaluadaPor", examen, CardOne(), CardZeroOrMany(), [
        Attribute("instancia", AttrString, false)
      ]
    );
    LinkConvertibleRelation(diagram, cursada, relEvaluadaPor);
    assert |cursada.relations| == 1;
    assert cursada.innerRelation == relCursa;
    assert cursada.innerSource == alumno;
  }

  // Converts the verified DER diagram to the Relational Model with
  // `ConvertibleDiagram` kept opaque so verification stays fast.
  method TestDerModelVerified() returns (rm: RelationalSchema)
    ensures ValidRelationalSchema(rm)
  {
    var diagram := BuildSampleDiagram();
    PrintDiagram(diagram);

    // 7. Convert the DER diagram to the Relational Model!
    rm := ConvertDerToRelational(diagram);
    assert ValidRelationalSchema(rm);
    assert HasTable(rm, "Persona");
    assert HasTable(rm, "Pasaporte");
    assert HasTable(rm, "Departamento");
    assert HasTable(rm, "Empleado");
    assert HasTable(rm, "Alumno");
    assert HasTable(rm, "Materia");
    assert HasTable(rm, "Examen");
    assert HasTable(rm, "Cursada");

    print "\n=== Converted Relational Model (RM) ===\n";
    print FormatRelationalSchema(rm);
  }

  method PrintDiagram(diagram: DerDiagram)
  {
    print "=== DER Diagram ===\n";
    var i := 0;
    while i < |diagram.elements|
      decreases |diagram.elements| - i
    {
      var elem := diagram.elements[i];
      print "Entity/Aggregation: ", elem.name, "\n";
      var a := 0;
      while a < |elem.attributes|
        decreases |elem.attributes| - a
      {
        print "  attr: ", FormatAttribute(elem.attributes[a]), "\n";
        a := a + 1;
      }
      var r := 0;
      while r < |elem.relations|
        decreases |elem.relations| - r
      {
        var rel := elem.relations[r];
        print "  rel:  ", rel.Describe(), " -> ", rel.target.name, "\n";
        r := r + 1;
      }
      i := i + 1;
    }
  }
}

module Main {
  import opened DerTypes
  import opened RelationalModel
  import opened FunctionalDeps
  import opened DecompositionAnalysis
  import opened Normalization
  import DerTests

  method ValidateAndPrintRM(rm: RelationalSchema)
    requires ValidRelationalSchema(rm)
  {
    var normSchema := BuildNormalizedSchemaFromRM(rm, map[]);
    var reports, overall := ValidateSchema(normSchema);
    print "\n=== DER -> RM Normal Form Validation (Overall: ", FormatNormalForm(overall), ") ===\n";
    var ri := 0;
    while ri < |reports|
      invariant 0 <= ri <= |reports|
      decreases |reports| - ri
    {
      print FormatValidationReport(reports[ri], TableAttrSeq(normSchema.relations[ri].table));
      ri := ri + 1;
    }
  }

  // Demonstrates 1NF validation and conversion (extracting multi-valued column).
  method Test1NFConversion()
  {
    var cols := [
      Column("id_cliente", AttrInt),
      Column("nombre", AttrString),
      Column("telefonos", AttrMultiValued(AttrString))
    ];
    var tbl := TableSchema("Cliente", cols, ["id_cliente"], []);
    var fds := [FD({"id_cliente"}, {"id_cliente", "nombre", "telefonos"})];
    var rel := NormalizedRelation(tbl, fds);

    assert ColNames(cols) == ["id_cliente", "nombre", "telefonos"];
    assert TableAttrSet(tbl) == {"id_cliente", "nombre", "telefonos"};
    assert HasColumn(cols, "id_cliente");
    assert ValidNormalizedRelation(rel);
    assert PrimaryKeyColumnsAtomic(tbl);

    var beforeRep := ValidateRelation(rel);
    assert !beforeRep.is1NF;

    var nf1Rels := ConvertRelationToNormalForm(rel, NF1);
    assert forall i :: 0 <= i < |nf1Rels| ==> IsTable1NF(nf1Rels[i].table);

    print "\n=== 1NF Conversion Demo ===\n";
    print "Before:\n", FormatValidationReport(beforeRep, TableAttrSeq(tbl));
    print "After 1NF:\n", FormatNormalizedRelations(nf1Rels);
  }

  // Demonstrates 2NF (partial dependencies) and 3NF (Bernstein synthesis +
  // lossless-join & dependency-preservation analysis).
  method Test2NFAnd3NFConversion()
  {
    var cols := [
      Column("padron", AttrInt),
      Column("cod_materia", AttrString),
      Column("nombre_alumno", AttrString),
      Column("cod_depto", AttrInt),
      Column("nombre_depto", AttrString),
      Column("nota", AttrDecimal)
    ];
    var tbl := TableSchema("Inscripcion", cols, ["padron", "cod_materia"], []);
    var fds := [
      FD({"padron", "cod_materia"}, {"nombre_alumno", "cod_depto", "nombre_depto", "nota"}),
      FD({"padron"}, {"nombre_alumno"}),
      FD({"cod_materia"}, {"cod_depto"}),
      FD({"cod_depto"}, {"nombre_depto"})
    ];
    var rel := NormalizedRelation(tbl, fds);

    assert ColNames(cols) == ["padron", "cod_materia", "nombre_alumno", "cod_depto", "nombre_depto", "nota"];
    assert TableAttrSet(tbl) == {"padron", "cod_materia", "nombre_alumno", "cod_depto", "nombre_depto", "nota"};
    assert HasColumn(cols, "padron") && HasColumn(cols, "cod_materia");
    assert ValidNormalizedRelation(rel);
    assert PrimaryKeyColumnsAtomic(tbl);

    var beforeRep := ValidateRelation(rel);
    var nf2Rels := ConvertRelationToNormalForm(rel, NF2);
    var nf3Rels := ConvertRelationToNormalForm(rel, NF3);

    var rep2NFAnalysis := AnalyzeRelationDecomposition(rel, nf2Rels);
    var rep3NFAnalysis := AnalyzeRelationDecomposition(rel, nf3Rels);

    print "\n=== 2NF & 3NF Conversion Demo ===\n";
    print "Original:\n", FormatValidationReport(beforeRep, TableAttrSeq(tbl));
    print "After 2NF:\n", FormatNormalizedRelations(nf2Rels);
    print FormatDecompositionReport(rep2NFAnalysis, TableAttrSeq(tbl));
    print "After 3NF (Bernstein):\n", FormatNormalizedRelations(nf3Rels);
    print FormatDecompositionReport(rep3NFAnalysis, TableAttrSeq(tbl));
  }

  // Demonstrates BCNF vs 3NF dependency-preservation trade-off AND lossy-join detection.
  method TestBCNFAndLossyAnalysis()
  {
    // Classic 3NF-but-not-BCNF example: (ciudad, calle, cp) with
    // {ciudad, calle} -> {cp} and {cp} -> {ciudad}.
    var cols := [
      Column("ciudad", AttrString),
      Column("calle", AttrString),
      Column("cp", AttrString)
    ];
    var tbl := TableSchema("Direccion", cols, ["ciudad", "calle"], []);
    var fds := [
      FD({"ciudad", "calle"}, {"cp"}),
      FD({"cp"}, {"ciudad"})
    ];
    var rel := NormalizedRelation(tbl, fds);

    assert ColNames(cols) == ["ciudad", "calle", "cp"];
    assert TableAttrSet(tbl) == {"ciudad", "calle", "cp"};
    assert HasColumn(cols, "ciudad") && HasColumn(cols, "calle");
    assert ValidNormalizedRelation(rel);
    assert PrimaryKeyColumnsAtomic(tbl);

    var beforeRep := ValidateRelation(rel);
    var bcnfRels := ConvertRelationToNormalForm(rel, BCNF);
    assert forall i :: 0 <= i < |bcnfRels| ==>
                         IsTable1NF(bcnfRels[i].table) &&
                         SatisfiesBCNFCondition(TableAttrSet(bcnfRels[i].table), bcnfRels[i].fds);

    var bcnfAnalysis := AnalyzeRelationDecomposition(rel, bcnfRels);

    print "\n=== BCNF Trade-off Demo (3NF -> BCNF) ===\n";
    print "Original:\n", FormatValidationReport(beforeRep, TableAttrSeq(tbl));
    print "After BCNF:\n", FormatNormalizedRelations(bcnfRels);
    print FormatDecompositionReport(bcnfAnalysis, TableAttrSeq(tbl));

    // Deliberately lossy decomposition: R(A, B, C) with A -> B split into {A, B} and {B, C}
    var lossyAttrs := ["A", "B", "C"];
    var lossyDecomp := [{"A", "B"}, {"B", "C"}];
    var lossyFDs := [FD({"A"}, {"B"})];
    var lossyAnalysis := AnalyzeDecomposition(lossyAttrs, lossyDecomp, lossyFDs);

    print "\n=== Lossy Decomposition Check (R(A,B,C), A->B into {A,B},{B,C}) ===\n";
    print FormatDecompositionReport(lossyAnalysis, lossyAttrs);
  }

  method Main()
  {
    var rm := DerTests.TestDerModelVerified();
    ValidateAndPrintRM(rm);
    Test1NFConversion();
    Test2NFAnd3NFConversion();
    TestBCNFAndLossyAnalysis();
  }
}
