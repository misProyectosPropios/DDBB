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
include "DidModel.dfy"
include "DerToDid.dfy"
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

  // Small helper that constructs a 2-attribute Entity (1 key + 1 non-key) and
  // proves `UniqueAttributeNames` and `HasKeyAttribute` once in isolation.
  method MakeTwoAttrEntity(
    name: Name,
    kName: Name,
    kType: AttrType,
    aName: Name,
    aType: AttrType
  ) returns (e: Entity)
    requires name != "" && kName != aName
    ensures fresh(e)
    ensures e.Valid()
    ensures e.name == name
    ensures e.relations == []
    ensures e.Repr == {e}
  {
    var attrs := [
      Attribute(kName, kType, true),
      Attribute(aName, aType, false)
    ];
    assert attrs[0].isKey;
    e := new Entity(name, attrs);
  }

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

    persona := MakeTwoAttrEntity("Persona", "dni", AttrInt, "nombre", AttrString);
    AddConvertibleEntity(diagram, persona);

    pasaporte := MakeTwoAttrEntity("Pasaporte", "numero", AttrString, "vencimiento", AttrDate);
    AddConvertibleEntity(diagram, pasaporte);

    departamento := MakeTwoAttrEntity("Departamento", "codigo", AttrInt, "nombre", AttrString);
    AddConvertibleEntity(diagram, departamento);

    empleado := MakeTwoAttrEntity("Empleado", "legajo", AttrInt, "salario", AttrDecimal);
    AddConvertibleEntity(diagram, empleado);

    alumno := MakeTwoAttrEntity("Alumno", "padron", AttrInt, "nombre", AttrString);
    AddConvertibleEntity(diagram, alumno);

    materia := MakeTwoAttrEntity("Materia", "codigo", AttrString, "creditos", AttrInt);
    AddConvertibleEntity(diagram, materia);

    examen := MakeTwoAttrEntity("Examen", "id_examen", AttrInt, "nota", AttrDecimal);
    AddConvertibleEntity(diagram, examen);
  }

  // Step 2a: Links the 1:1 (`Tiene`) and 1:N (`Emplea`) relations.
  method LinkOneToOneAndOneToMany(
    diagram: DerDiagram,
    persona: Entity,
    pasaporte: Entity,
    departamento: Entity,
    empleado: Entity
  )
    requires ConvertibleDiagram(diagram)
    requires persona in diagram.elements && pasaporte in diagram.elements
    requires departamento in diagram.elements && empleado in diagram.elements
    requires persona != departamento
    requires persona.relations == [] && departamento.relations == []
    modifies persona, departamento
    ensures ConvertibleDiagram(diagram)
    ensures |persona.relations| == 1
    ensures |departamento.relations| == 1
    ensures departamento.relations[0].name == "Emplea"
  {
    var relTiene := new OneToOneRelation(
      "Tiene", pasaporte, CardOne(), CardZeroOrOne(), []
    );
    assert relTiene.Kind() == KindOneToOne;
    LinkConvertibleRelation(diagram, persona, relTiene);

    var relEmplea := new OneToManyRelation(
      "Emplea", empleado, CardOne(), CardOneOrMany(), [
      Attribute("fecha_ingreso", AttrDate, false)
      ]
    );
    assert relEmplea.Kind() == KindOneToMany;
    LinkConvertibleRelation(diagram, departamento, relEmplea);
  }

  // Step 2b: Links the N:M (`Cursa`) and General (`Colabora`, 2..5 -> 1..*) relations.
  method LinkManyToManyAndGeneral(
    diagram: DerDiagram,
    departamento: Entity,
    alumno: Entity,
    materia: Entity
  ) returns (relCursa: Relation)
    requires ConvertibleDiagram(diagram)
    requires departamento in diagram.elements
    requires alumno in diagram.elements && materia in diagram.elements
    requires alumno != departamento
    requires alumno.relations == []
    requires |departamento.relations| == 1 && departamento.relations[0].name == "Emplea"
    modifies alumno, departamento
    ensures ConvertibleDiagram(diagram)
    ensures |departamento.relations| == 2
    ensures relCursa.ValidRelation()
    ensures relCursa.target == materia
    ensures relCursa as object != diagram as object
    ensures forall i :: 0 <= i < |diagram.elements| ==>
                          diagram.elements[i] as object != relCursa as object
  {
    var cursa := new ManyToManyRelation(
      "Cursa", materia, CardZeroOrMany(), CardOneOrMany(), [
      Attribute("cuatrimestre", AttrString, false)
      ]
    );
    assert cursa.Kind() == KindManyToMany;
    LinkConvertibleRelation(diagram, alumno, cursa);
    relCursa := cursa;

    var relColabora := new GeneralRelation(
      "Colabora", departamento, CardRange(2, 5), CardAtLeast(1), []
    );
    assert relColabora.Kind() == KindManyToMany;
    assert DistinctRelations(departamento.relations[0], relColabora);
    LinkConvertibleRelation(diagram, departamento, relColabora);
  }

  // Step 2c: Adds the `Cursada` Aggregation and links its outer 1:N relation `EvaluadaPor`.
  method AddCursadaAggregation(
    diagram: DerDiagram,
    alumno: Entity,
    materia: Entity,
    examen: Entity,
    relCursa: Relation
  ) returns (cursada: Aggregation)
    requires ConvertibleDiagram(diagram)
    requires |diagram.elements| == 7
    requires diagram.elements[0].name == "Persona"
    requires diagram.elements[1].name == "Pasaporte"
    requires diagram.elements[2].name == "Departamento"
    requires diagram.elements[3].name == "Empleado"
    requires diagram.elements[4].name == "Alumno"
    requires diagram.elements[5].name == "Materia"
    requires diagram.elements[6].name == "Examen"
    requires alumno in diagram.elements && materia in diagram.elements && examen in diagram.elements
    requires relCursa.ValidRelation() && relCursa.target == materia
    requires relCursa as object != diagram as object
    requires forall i :: 0 <= i < |diagram.elements| ==>
                           diagram.elements[i] as object != relCursa as object
    modifies diagram
    ensures ConvertibleDiagram(diagram)
    ensures |diagram.elements| == 8
    ensures diagram.elements[..7] == old(diagram.elements)
    ensures diagram.elements[7] == cursada
    ensures cursada.name == "Cursada"
    ensures |cursada.relations| == 1
    ensures cursada.innerRelation == relCursa
    ensures cursada.innerSource == alumno
    ensures fresh(cursada)
  {
    cursada := new Aggregation("Cursada", alumno, relCursa, [
                               Attribute("estado", AttrString, false)
                               ]);
    AddConvertibleAggregation(diagram, cursada);

    var relEvaluadaPor := new OneToManyRelation(
      "EvaluadaPor", examen, CardOne(), CardZeroOrMany(), [
      Attribute("instancia", AttrString, false)
      ]
    );
    LinkConvertibleRelation(diagram, cursada, relEvaluadaPor);
  }

  // Step 2: Assembles the complete sample DER diagram in 4 modular steps.
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

    LinkOneToOneAndOneToMany(diagram, persona, pasaporte, departamento, empleado);
    var relCursa := LinkManyToManyAndGeneral(diagram, departamento, alumno, materia);
    var cursada := AddCursadaAggregation(diagram, alumno, materia, examen, relCursa);
    assert cursada.name == "Cursada";
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

// Isolated module for verifying DER -> DID conversion & Mongo-style XML generation.
module DidTests {
  import opened DerTypes
  import opened DerModel
  import opened DerToRelational
  import opened DidModel
  import opened DerToDid
  import DerTests

  method TestDerToDidVerified()
  {
    var diagram := DerTests.BuildSampleDiagram();

    // 1. Default DID conversion (1:1 & 1:N embedded, N:M referenced)
    var defaultCfg := DefaultDidConfig("UniversityHR_NoSQL");
    var didDefault, xmlDefault := ConvertDerToDidXml(diagram, defaultCfg);
    assert ValidDidDatabase(didDefault);
    //assert HasCollection(didDefault, "Persona");
    //assert HasCollection(didDefault, "Departamento");
    //assert HasCollection(didDefault, "Cursada");
    assert |xmlDefault| > 0;

    print "\n=== Default DID (Mongo-Style Document XML) ===\n";
    print xmlDefault;

    // 2. Modified DID conversion: override 'Tiene' to Reference and 'Cursa' to Embed,
    //    and filter top-level root collections to Persona, Departamento, and Cursada.
    var customCfg0 := WithRelationMode(defaultCfg, "Tiene", ModeReference);
    var customCfg1 := WithRelationMode(customCfg0, "Cursa", ModeEmbed);
    var customCfg := WithRootCollections(customCfg1, ["Persona", "Departamento", "Cursada"]);

    var didCustom, xmlCustom := ConvertDerToDidXml(diagram, customCfg);
    assert ValidDidDatabase(didCustom);
    assert |xmlCustom| > 0;

    print "\n=== Modified DID (Custom Root Collections & Embed/Reference Overrides) ===\n";
    print xmlCustom;
  }
}

module Main {
  import opened DerTypes
  import opened RelationalModel
  import opened FunctionalDeps
  import opened DecompositionAnalysis
  import opened Normalization
  import DerTests
  import DidTests

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
    DidTests.TestDerToDidVerified();
    Test1NFConversion();
    Test2NFAnd3NFConversion();
    TestBCNFAndLossyAnalysis();
  }
}
