// DER (Entity-Relationship Diagram) Object Model:
//
// 1. Generalized Relation hierarchy (`trait Relation` — a class apart):
//      - `OneToOneRelation`   (1:1 — both sides have max bound 1)
//      - `OneToManyRelation`  (1:N — source max is 1, target max is > 1 or *)
//      - `ManyToManyRelation` (N:M — both sides have max > 1 or *)
//      - `GeneralRelation`    (any valid general (min..max) cardinality pair)
//
// 2. Generalized Entity hierarchy (`trait EntityElement`):
//      - Each EntityElement owns a list of distinct `Relation`s (`relations`).
//      - `Entity`      — standard DER entity with unique attributes and a key.
//      - `Aggregation` — composes an existing `(innerSource, innerRelation)`
//                        so the aggregated relationship behaves as a higher-level
//                        entity that can itself participate in further relations.
//
// 3. `DerDiagram` — diagram container enforcing unique entity/aggregation names
//    and referential integrity for all attached relations.

include "Types.dfy"

module DerModel {
  import opened DerTypes

  // ---------------------------------------------------------------------------
  // Relation hierarchy (generalized, separate from Entity)
  // ---------------------------------------------------------------------------

  trait Relation extends object {
    const name: Name
    const target: EntityElement
    const attributes: seq<Attribute>
    const sourceCard: Cardinality
    const targetCard: Cardinality

    function Kind(): RelationKind
      reads this

    // Subclass-specific cardinality invariant (1:1, 1:N, N:M, or general).
    ghost predicate ValidCardinalities()
      reads this

    // Shared relation invariant guaranteed by every Relation, so callers
    // holding the trait know `name != ""` and `UniqueAttributeNames(attributes)`.
    ghost predicate ValidRelation()
      reads this
    {
      name != "" &&
      UniqueAttributeNames(attributes) &&
      ValidCardinalities()
    }

    function Describe(): string
      reads this
    {
      name + " [" + FormatRelationKind(Kind()) + "] (" +
      FormatCardinality(sourceCard) + " -> " + FormatCardinality(targetCard) + ")"
    }
  }

  // 1:1 Relation — both source and target cardinalities have max bound 1.
  class OneToOneRelation extends Relation {
    constructor (
      name: Name,
      target: EntityElement,
      sourceCard: Cardinality,
      targetCard: Cardinality,
      attributes: seq<Attribute>
    )
      requires name != ""
      requires IsSingle(sourceCard) && IsSingle(targetCard)
      requires UniqueAttributeNames(attributes)
      ensures ValidRelation()
      ensures this.name == name
      ensures this.target == target
      ensures this.sourceCard == sourceCard
      ensures this.targetCard == targetCard
      ensures this.attributes == attributes
      ensures Kind() == KindOneToOne
    {
      this.name := name;
      this.target := target;
      this.sourceCard := sourceCard;
      this.targetCard := targetCard;
      this.attributes := attributes;
    }

    function Kind(): RelationKind
      reads this
    {
      KindOneToOne
    }

    ghost predicate ValidCardinalities()
      reads this
    {
      IsSingle(sourceCard) &&
      IsSingle(targetCard)
    }
  }

  // 1:N Relation — source has max bound 1, target has max bound > 1 or *.
  class OneToManyRelation extends Relation {
    constructor (
      name: Name,
      target: EntityElement,
      sourceCard: Cardinality,
      targetCard: Cardinality,
      attributes: seq<Attribute>
    )
      requires name != ""
      requires IsSingle(sourceCard) && IsMany(targetCard)
      requires UniqueAttributeNames(attributes)
      ensures ValidRelation()
      ensures this.name == name
      ensures this.target == target
      ensures this.sourceCard == sourceCard
      ensures this.targetCard == targetCard
      ensures this.attributes == attributes
      ensures Kind() == KindOneToMany
    {
      this.name := name;
      this.target := target;
      this.sourceCard := sourceCard;
      this.targetCard := targetCard;
      this.attributes := attributes;
    }

    function Kind(): RelationKind
      reads this
    {
      KindOneToMany
    }

    ghost predicate ValidCardinalities()
      reads this
    {
      IsSingle(sourceCard) &&
      IsMany(targetCard)
    }
  }

  // N:M Relation — both source and target have max bound > 1 or *.
  class ManyToManyRelation extends Relation {
    constructor (
      name: Name,
      target: EntityElement,
      sourceCard: Cardinality,
      targetCard: Cardinality,
      attributes: seq<Attribute>
    )
      requires name != ""
      requires IsMany(sourceCard) && IsMany(targetCard)
      requires UniqueAttributeNames(attributes)
      ensures ValidRelation()
      ensures this.name == name
      ensures this.target == target
      ensures this.sourceCard == sourceCard
      ensures this.targetCard == targetCard
      ensures this.attributes == attributes
      ensures Kind() == KindManyToMany
    {
      this.name := name;
      this.target := target;
      this.sourceCard := sourceCard;
      this.targetCard := targetCard;
      this.attributes := attributes;
    }

    function Kind(): RelationKind
      reads this
    {
      KindManyToMany
    }

    ghost predicate ValidCardinalities()
      reads this
    {
      IsMany(sourceCard) &&
      IsMany(targetCard)
    }
  }

  // General Relation — accepts any valid (min..max) cardinality pair (including
  // N:1 or custom finite bounds) and classifies its kind dynamically.
  class GeneralRelation extends Relation {
    constructor (
      name: Name,
      target: EntityElement,
      sourceCard: Cardinality,
      targetCard: Cardinality,
      attributes: seq<Attribute>
    )
      requires name != ""
      requires ValidCardinality(sourceCard) && ValidCardinality(targetCard)
      requires UniqueAttributeNames(attributes)
      ensures ValidRelation()
      ensures this.name == name
      ensures this.target == target
      ensures this.sourceCard == sourceCard
      ensures this.targetCard == targetCard
      ensures this.attributes == attributes
    {
      this.name := name;
      this.target := target;
      this.sourceCard := sourceCard;
      this.targetCard := targetCard;
      this.attributes := attributes;
    }

    function Kind(): RelationKind
      reads this
    {
      if ValidCardinality(sourceCard) && ValidCardinality(targetCard) then
        ClassifyRelation(sourceCard, targetCard)
      else
        KindManyToMany
    }

    ghost predicate ValidCardinalities()
      reads this
    {
      ValidCardinality(sourceCard) &&
      ValidCardinality(targetCard)
    }
  }

  // ---------------------------------------------------------------------------
  // EntityElement hierarchy (entities and aggregations both own a list of
  // distinct relations)
  // ---------------------------------------------------------------------------

  // Checks that two relations are distinct (different object AND not the exact
  // same (name, target, kind) signature).
  predicate DistinctRelations(r1: Relation, r2: Relation)
    reads r1, r2
  {
    r1 != r2 &&
    (r1.name != r2.name || r1.target != r2.target || r1.Kind() != r2.Kind())
  }

  // Discriminant allowing consumers (such as the DER -> RM converter) to
  // inspect whether an EntityElement is a plain Entity or an Aggregation
  // without needing runtime downcasts.
  datatype AggregationInfo =
    | NotAnAggregation
    | AggregationOf(innerSource: EntityElement, innerRelation: Relation)

  trait EntityElement extends object {
    const name: Name
    const attributes: seq<Attribute>
    var relations: seq<Relation>
    ghost var Repr: set<object>

    // Subclass-specific validity conditions (e.g., Entity requires a PK
    // attribute; Aggregation requires a valid inner relationship).
    ghost predicate ValidExtra()
      reads this, Repr

    // Shared validity invariant guaranteed by every EntityElement, so callers
    // holding the trait (such as DerToRelational) know `name != ""` and that
    // all attached relations are valid and distinct.
    ghost predicate Valid()
      reads this, Repr
    {
      name != "" &&
      UniqueAttributeNames(attributes) &&
      this in Repr &&
      (forall i :: 0 <= i < |relations| ==> relations[i] in Repr) &&
      (forall i :: 0 <= i < |relations| ==> relations[i] as object != this as object) &&
      (forall i :: 0 <= i < |relations| ==> relations[i].ValidRelation()) &&
      (forall i, j :: 0 <= i < j < |relations| ==> DistinctRelations(relations[i], relations[j])) &&
      ValidExtra()
    }

    function AggregationDetails(): AggregationInfo
      reads this

    // Attaches a new distinct relation to this entity/aggregation.
    method AddRelation(rel: Relation)
      requires Valid()
      requires rel.ValidRelation()
      requires rel as object != this as object
      requires forall i :: 0 <= i < |relations| ==> DistinctRelations(relations[i], rel)
      modifies this
      ensures Valid()
      ensures relations == old(relations) + [rel]
      ensures Repr == old(Repr) + {rel}

    function GetRelations(): seq<Relation>
      reads this
    {
      relations
    }
  }

  // Standard DER Entity — owns attributes (including at least one primary key)
  // and a list of distinct relations.
  class Entity extends EntityElement {
    constructor (name: Name, attributes: seq<Attribute>)
      requires name != ""
      requires UniqueAttributeNames(attributes)
      requires HasKeyAttribute(attributes)
      ensures Valid()
      ensures this.name == name
      ensures this.attributes == attributes
      ensures this.relations == []
      ensures this.Repr == {this}
    {
      this.name := name;
      this.attributes := attributes;
      this.relations := [];
      this.Repr := {this};
    }

    ghost predicate ValidExtra()
      reads this, Repr
    {
      HasKeyAttribute(attributes)
    }

    function AggregationDetails(): AggregationInfo
      reads this
    {
      NotAnAggregation
    }

    method AddRelation(rel: Relation)
      requires Valid()
      requires rel.ValidRelation()
      requires rel as object != this as object
      requires forall i :: 0 <= i < |relations| ==> DistinctRelations(relations[i], rel)
      modifies this
      ensures Valid()
      ensures relations == old(relations) + [rel]
      ensures Repr == old(Repr) + {rel}
    {
      relations := relations + [rel];
      Repr := Repr + {rel};
    }
  }

  // DER Aggregation — composes an existing relationship `(innerSource --[innerRelation]--> target)`
  // so the whole relationship acts as a higher-level EntityElement that can
  // itself own further relations (e.g., `(Cursada) --[EvaluadaPor]--> (Examen)`).
  class Aggregation extends EntityElement {
    const innerSource: EntityElement
    const innerRelation: Relation

    constructor (
      name: Name,
      innerSource: EntityElement,
      innerRelation: Relation,
      attributes: seq<Attribute>
    )
      requires name != ""
      requires innerRelation.ValidRelation()
      requires UniqueAttributeNames(attributes)
      ensures Valid()
      ensures this.name == name
      ensures this.innerSource == innerSource
      ensures this.innerRelation == innerRelation
      ensures this.attributes == attributes
      ensures this.relations == []
      ensures this.Repr == {this, innerRelation}
    {
      this.name := name;
      this.innerSource := innerSource;
      this.innerRelation := innerRelation;
      this.attributes := attributes;
      this.relations := [];
      this.Repr := {this, innerRelation};
    }

    ghost predicate ValidExtra()
      reads this, Repr
    {
      innerRelation in Repr &&
      innerRelation as object != this as object &&
      innerRelation.ValidRelation() &&
      innerSource != this &&
      innerRelation.target != this
    }

    function AggregationDetails(): AggregationInfo
      reads this
    {
      AggregationOf(innerSource, innerRelation)
    }

    method AddRelation(rel: Relation)
      requires Valid()
      requires rel.ValidRelation()
      requires rel as object != this as object
      requires forall i :: 0 <= i < |relations| ==> DistinctRelations(relations[i], rel)
      modifies this
      ensures Valid()
      ensures relations == old(relations) + [rel]
      ensures Repr == old(Repr) + {rel}
    {
      relations := relations + [rel];
      Repr := Repr + {rel};
    }
  }

  // ---------------------------------------------------------------------------
  // DER Diagram container
  // ---------------------------------------------------------------------------

  class DerDiagram {
    var elements: seq<EntityElement>

    constructor ()
      ensures Valid()
      ensures elements == []
    {
      this.elements := [];
    }

    ghost predicate Valid()
      reads this, elements
    {
      (forall i :: 0 <= i < |elements| ==> elements[i] as object != this as object) &&
      (forall i, j :: 0 <= i < j < |elements| ==>
        elements[i] != elements[j] && elements[i].name != elements[j].name)
    }

    method AddElement(elem: EntityElement)
      requires Valid()
      requires elem as object != this as object
      requires forall i :: 0 <= i < |elements| ==>
        elements[i] != elem && elements[i].name != elem.name
      modifies this
      ensures Valid()
      ensures elements == old(elements) + [elem]
    {
      elements := elements + [elem];
    }

    // Links `rel` from `source` to `rel.target`, ensuring both endpoints exist
    // in this diagram and `rel` is distinct from existing relations on `source`.
    method LinkRelation(source: EntityElement, rel: Relation)
      requires Valid()
      requires source in elements && rel.target in elements
      requires source.Valid()
      requires rel.ValidRelation()
      requires rel as object != source as object
      requires forall i :: 0 <= i < |source.relations| ==> DistinctRelations(source.relations[i], rel)
      modifies source
      ensures Valid()
      ensures source.Valid()
      ensures source.relations == old(source.relations) + [rel]
      ensures source.Repr == old(source.Repr) + {rel}
    {
      assert source as object != this as object;
      source.AddRelation(rel);
    }
  }
}
