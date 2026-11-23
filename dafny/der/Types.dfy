// Core domain types for the DER (Entity-Relationship Diagram) module:
// attributes, generalized (min..max) cardinalities supporting infinitely many
// multiplicities, relation classification (1:1, 1:N, N:M, N:1), and formatters.

module DerTypes {
  type Name = string

  datatype AttrType =
    | AttrInt
    | AttrString
    | AttrBool
    | AttrDate
    | AttrDecimal
    | AttrCustom(name: string)
    | AttrMultiValued(elemType: AttrType)

  // Atomic types satisfy 1NF; multi-valued/repeating-group types violate 1NF.
  predicate IsAtomicType(t: AttrType)
  {
    !t.AttrMultiValued?
  }

  // Unwraps nested multi-valued wrappers down to an atomic base type.
  function BaseAtomicType(t: AttrType): AttrType
    ensures IsAtomicType(BaseAtomicType(t))
    decreases t
  {
    match t
    case AttrMultiValued(inner) => BaseAtomicType(inner)
    case _ => t
  }

  datatype Attribute = Attribute(
    name: Name,
    attrType: AttrType,
    isKey: bool
  )

  predicate UniqueAttributeNames(attrs: seq<Attribute>)
  {
    forall i, j :: 0 <= i < j < |attrs| ==> attrs[i].name != attrs[j].name
  }

  predicate HasKeyAttribute(attrs: seq<Attribute>)
  {
    exists i :: 0 <= i < |attrs| && attrs[i].isKey
  }

  // Witness lemma when the first attribute in a list is marked as a key.
  lemma LemmaFirstAttrIsKey(attrs: seq<Attribute>)
    requires |attrs| > 0 && attrs[0].isKey
    ensures HasKeyAttribute(attrs)
  {
    assert 0 <= 0 < |attrs| && attrs[0].isKey;
  }

  // Upper bound of a cardinality: either a positive finite integer or unbounded (* / N / M).
  datatype Bound =
    | Finite(n: nat)
    | Unbounded

  // General (min..max) cardinality supporting infinitely many multiplicities
  // such as 0..1, 1..1, 0..*, 1..*, 2..5, 1..10, etc.
  datatype Cardinality = Cardinality(min: nat, max: Bound)

  predicate ValidCardinality(c: Cardinality)
  {
    match c.max
    case Finite(n) => n >= 1 && c.min <= n
    case Unbounded => true
  }

  // "At most one" side (0..1 or 1..1).
  predicate IsSingle(c: Cardinality)
  {
    ValidCardinality(c) && c.max == Finite(1)
  }

  // "Many" side (unbounded * or any finite upper bound > 1).
  predicate IsMany(c: Cardinality)
  {
    ValidCardinality(c) &&
    match c.max
    case Unbounded => true
    case Finite(n) => n > 1
  }

  // Convenience cardinality constructors
  function CardOne(): Cardinality { Cardinality(1, Finite(1)) }
  function CardZeroOrOne(): Cardinality { Cardinality(0, Finite(1)) }
  function CardZeroOrMany(): Cardinality { Cardinality(0, Unbounded) }
  function CardOneOrMany(): Cardinality { Cardinality(1, Unbounded) }

  function CardAtLeast(min: nat): Cardinality
    ensures ValidCardinality(CardAtLeast(min))
    ensures IsMany(CardAtLeast(min))
  {
    Cardinality(min, Unbounded)
  }

  function CardRange(min: nat, max: nat): Cardinality
    requires max >= 1 && min <= max
    ensures ValidCardinality(CardRange(min, max))
  {
    Cardinality(min, Finite(max))
  }

  datatype RelationKind =
    | KindOneToOne
    | KindOneToMany
    | KindManyToMany
    | KindManyToOne

  function ClassifyRelation(src: Cardinality, dst: Cardinality): RelationKind
    requires ValidCardinality(src) && ValidCardinality(dst)
  {
    if IsSingle(src) && IsSingle(dst) then KindOneToOne
    else if IsSingle(src) && IsMany(dst) then KindOneToMany
    else if IsMany(src) && IsMany(dst) then KindManyToMany
    else KindManyToOne
  }

  // ---------------------------------------------------------------------------
  // Formatting helpers
  // ---------------------------------------------------------------------------

  function DigitToString(d: nat): string
    requires d < 10
  {
    match d
    case 0 => "0"
    case 1 => "1"
    case 2 => "2"
    case 3 => "3"
    case 4 => "4"
    case 5 => "5"
    case 6 => "6"
    case 7 => "7"
    case 8 => "8"
    case 9 => "9"
  }

  function NatToString(n: nat): string
    decreases n
  {
    if n < 10 then DigitToString(n)
    else NatToString(n / 10) + DigitToString(n % 10)
  }

  function FormatBound(b: Bound): string
  {
    match b
    case Finite(n) => NatToString(n)
    case Unbounded => "*"
  }

  function FormatCardinality(c: Cardinality): string
  {
    NatToString(c.min) + ".." + FormatBound(c.max)
  }

  function FormatRelationKind(k: RelationKind): string
  {
    match k
    case KindOneToOne => "1:1"
    case KindOneToMany => "1:N"
    case KindManyToMany => "N:M"
    case KindManyToOne => "N:1"
  }

  function FormatAttrType(t: AttrType): string
    decreases t
  {
    match t
    case AttrInt => "INT"
    case AttrString => "STRING"
    case AttrBool => "BOOL"
    case AttrDate => "DATE"
    case AttrDecimal => "DECIMAL"
    case AttrCustom(name) => name
    case AttrMultiValued(inner) => "SET<" + FormatAttrType(inner) + ">"
  }

  function FormatAttribute(a: Attribute): string
  {
    (if a.isKey then "[PK] " else "") + a.name + ": " + FormatAttrType(a.attrType)
  }
}
