// Verified tests and runnable demonstration for the Dafny DER module:
//   - Entities with primary keys and attributes
//   - Distinct generalized Relation classes: 1:1, 1:N, N:M, and General (min..max)
//   - Relations owned as a list inside each EntityElement
//   - Aggregation composing an inner relationship and participating in outer relations

include "Types.dfy"
include "Model.dfy"
include "RelationalModel.dfy"
include "DerToRelational.dfy"

module Main {
  import opened DerTypes
  import opened DerModel
  import opened RelationalModel
  import opened DerToRelational

  // Statically verified construction of a DER diagram featuring 1:1, 1:N, N:M,
  // general cardinalities, and an Aggregation composing an N:M relationship.
  method TestDerModelVerified()
  {
    var diagram := new DerDiagram();

    // 1. Create Entities
    var persona := new Entity("Persona", [
      Attribute("dni", AttrInt, true),
      Attribute("nombre", AttrString, false)
    ]);
    var pasaporte := new Entity("Pasaporte", [
      Attribute("numero", AttrString, true),
      Attribute("vencimiento", AttrDate, false)
    ]);
    var departamento := new Entity("Departamento", [
      Attribute("codigo", AttrInt, true),
      Attribute("nombre", AttrString, false)
    ]);
    var empleado := new Entity("Empleado", [
      Attribute("legajo", AttrInt, true),
      Attribute("salario", AttrDecimal, false)
    ]);
    var alumno := new Entity("Alumno", [
      Attribute("padron", AttrInt, true),
      Attribute("nombre", AttrString, false)
    ]);
    var materia := new Entity("Materia", [
      Attribute("codigo", AttrString, true),
      Attribute("creditos", AttrInt, false)
    ]);
    var examen := new Entity("Examen", [
      Attribute("id_examen", AttrInt, true),
      Attribute("nota", AttrDecimal, false)
    ]);

    diagram.AddElement(persona);
    diagram.AddElement(pasaporte);
    diagram.AddElement(departamento);
    diagram.AddElement(empleado);
    diagram.AddElement(alumno);
    diagram.AddElement(materia);
    diagram.AddElement(examen);

    // 2. 1:1 Relation: Persona (1..1) --[Tiene]--> Pasaporte (0..1)
    var relTiene := new OneToOneRelation(
      "Tiene", pasaporte, CardOne(), CardZeroOrOne(), []
    );
    assert relTiene.Kind() == KindOneToOne;
    diagram.LinkRelation(persona, relTiene);
    assert |persona.relations| == 1;

    // 3. 1:N Relation: Departamento (1..1) --[Emplea]--> Empleado (1..*)
    var relEmplea := new OneToManyRelation(
      "Emplea", empleado, CardOne(), CardOneOrMany(), [
        Attribute("fecha_ingreso", AttrDate, false)
      ]
    );
    assert relEmplea.Kind() == KindOneToMany;
    diagram.LinkRelation(departamento, relEmplea);

    // 4. N:M Relation: Alumno (0..*) --[Cursa]--> Materia (1..*)
    var relCursa := new ManyToManyRelation(
      "Cursa", materia, CardZeroOrMany(), CardOneOrMany(), [
        Attribute("cuatrimestre", AttrString, false)
      ]
    );
    assert relCursa.Kind() == KindManyToMany;
    diagram.LinkRelation(alumno, relCursa);

    // 5. General Relation with custom finite bounds: Departamento (2..5) --[Colabora]--> Departamento (1..*)
    var relColabora := new GeneralRelation(
      "Colabora", departamento, CardRange(2, 5), CardAtLeast(1), []
    );
    assert relColabora.Kind() == KindManyToMany;
    diagram.LinkRelation(departamento, relColabora);
    assert |departamento.relations| == 2;

    // 6. Aggregation: `Cursada` composes `(Alumno) --[Cursa]--> (Materia)` so
    //    it can participate in a 1:N relation `EvaluadaPor` with `Examen`!
    var cursada := new Aggregation("Cursada", alumno, relCursa, [
      Attribute("estado", AttrString, false)
    ]);
    diagram.AddElement(cursada);

    var relEvaluadaPor := new OneToManyRelation(
      "EvaluadaPor", examen, CardOne(), CardZeroOrMany(), [
        Attribute("instancia", AttrString, false)
      ]
    );
    diagram.LinkRelation(cursada, relEvaluadaPor);
    assert |cursada.relations| == 1;
    assert cursada.innerRelation == relCursa;
    assert cursada.innerSource == alumno;

    PrintDiagram(diagram);

    // 7. Convert the DER diagram to the Relational Model!
    assert diagram.elements == [persona, pasaporte, departamento, empleado, alumno, materia, examen, cursada];
    reveal ConvertibleDiagram();
    var rm := ConvertDerToRelational(diagram);
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

  method Main()
  {
    TestDerModelVerified();
  }
}
