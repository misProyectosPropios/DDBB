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
- **[RelationalModel.dfy](RelationalModel.dfy)** (`module RelationalModel`) — `Column`, `ForeignKey`, `TableSchema`, `RelationalSchema`, well-formedness invariants (`ValidTable`, `ValidRelationalSchema`), and classic RM notation formatters.
- **[DerToRelational.dfy](DerToRelational.dfy)** (`module DerToRelational`) — `ConvertDerToRelational(diagram)` implementing and formally verifying the ER-to-Relational conversion rules (Entities, Aggregations, N:M join tables with composite PKs, and 1:1 / 1:N / N:1 FK propagation).
- **[FunctionalDeps.dfy](FunctionalDeps.dfy)** (`module FunctionalDeps`) — Functional Dependencies (`FD`), fixed-point attribute closure (`AttributeClosure`) with soundness/monotonicity/idempotence lemmas, exact candidate-key finder (`FindCandidateKeys`) with verified core/dead-attribute pruning, canonical minimal cover (`ComputeMinimalCover`), and FD projection (`ProjectFDs`).
- **[DecompositionAnalysis.dfy](DecompositionAnalysis.dfy)** (`module DecompositionAnalysis`) — Full Aho–Beeri–Ullman **Chase (Tableau) Algorithm** (`CheckLosslessJoin`) with verified potential-based termination, binary lossless-join soundness lemma (`LemmaBinarySplitIsLossless`), and **Ullman's polynomial dependency-preservation algorithm** (`CheckDependencyPreserving`, returning any lost FDs).
- **[Normalization.dfy](Normalization.dfy)** (`module Normalization`) — Bridges from `ConvertDerToRelational` (`BuildNormalizedSchemaFromRM`), validates **1NF / 2NF / 3NF / BCNF** (`ValidateRelation`, `ValidateSchema`), and converts relations/schemas to **1NF** (multi-valued column extraction), **2NF** (lossless partial-dependency removal), **3NF** (Bernstein synthesis), and **BCNF** (verified lossless BCNF decomposition).
- **[DidModel.dfy](DidModel.dfy)** (`module DidModel`) — Formalization of a NoSQL **Document Instance Diagram (DID)** (`DidDatabase`, `DidCollection`, `DidDocument`, `DidField`), customizable relation storage directives (`ModeAuto`, `ModeEmbed`, `ModeReference`, `DidConfig`), and Mongo-style XML generator (`FormatDidDatabaseXml`).
- **[DerToDid.dfy](DerToDid.dfy)** (`module DerToDid`) — Formally verified `ConvertDerToDid` and `ConvertDerToDidXml` transforming a `DerDiagram` + customizable `DidConfig` into a hierarchical `DidDatabase` and Mongo-style XML with all entities, aggregations, attributes, embedded sub-documents/arrays, and references.
- **[Main.dfy](Main.dfy)** (`module Main`) — Statically verified DER construction, DER → RM conversion, DER → DID & XML generation, 1NF/2NF/3NF/BCNF validation & conversion, and lossless-join / dependency-preservation demonstrations.
