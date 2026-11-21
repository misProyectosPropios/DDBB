# Dafny DER (Entity-Relationship Diagram) Module

Formally verified Entity-Relationship (DER) object model in Dafny with generalized cardinalities, distinct relation classes, and composable aggregations.

## Architecture

- **[Types.dfy](Types.dfy)** (`module DerTypes`) — `Attribute`, `AttrType`, generalized `Cardinality(min, max: Bound)` supporting infinitely many multiplicities (`0..1`, `1..1`, `0..*`, `1..*`, `2..5`, etc.), `RelationKind` (`1:1`, `1:N`, `N:M`, `N:1`), and string formatters.
- **[Model.dfy](Model.dfy)** (`module DerModel`):
  - **Generalized `trait Relation`** (separate class hierarchy) with distinct concrete subclasses:
    - `OneToOneRelation` (1:1)
    - `OneToManyRelation` (1:N)
    - `ManyToManyRelation` (N:M)
    - `GeneralRelation` (any valid `(min..max)` cardinality pair)
  - **`trait EntityElement`** — owns a list of distinct `Relation`s (`relations: seq<Relation>`):
    - `Entity` — standard DER entity with unique attribute names and a primary key.
    - `Aggregation` — composes an inner `(innerSource, innerRelation)` relationship so the aggregated relationship acts as an `EntityElement` that can participate in further relations.
  - **`DerDiagram`** — diagram container enforcing unique entity/aggregation names and valid relation endpoints.
- **[Main.dfy](Main.dfy)** (`module Main`) — Statically verified DER construction demo (including `1:1`, `1:N`, `N:M`, custom finite bounds `2..5 -> 1..*`, and an `Aggregation` `Cursada` composing `Alumno --[Cursa]--> Materia` linked to `Examen`).
