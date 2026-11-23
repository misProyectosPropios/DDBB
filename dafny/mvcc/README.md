# Dafny MVCC Simulator & Isolation Levels Module

Formally verified **Multi-Version Concurrency Control (MVCC)** simulator and **Isolation Levels (`RC`, `CS`, `RR`, `SI`, `SerializableMVCC`)** model in Dafny 4.

## Architecture

- **[Types.dfy](Types.dfy)** (`module MvccTypes`):
  - `IsolationLevel`: `ReadCommitted` (`RC`), `CursorStability` (`CS`), `RepeatableRead` (`RR`), `SnapshotIsolation` (`SI`), and `SerializableMVCC` (`SSI`).
  - `TupleVersion(element, value, creatorTx, xmin, committed)` — immutable versioned records in the MVCC version chain.
  - `TxMeta` — transaction state, snapshot `startTs`, `commitTs`, positioned `cursorElem`, `readSet`, and `writeSet`.
  - `MvccState` & `ValidMvccState` — full engine state with version chain, uncommitted write ownership (`writeOwners`), `RR` read locks (`rrReadLocks`), and `CS` cursor pins (`csCursorPins`).
- **[IsolationPolicy.dfy](IsolationPolicy.dfy)** (`module IsolationPolicies`):
  - `IsVersionVisible(meta, v)` — per-level visibility rules with formal proofs `LemmaNoDirtyReads` (no isolation level ever reads another transaction's uncommitted write) and `LemmaSnapshotBoundedByStartTs` (`SI` and `SerializableMVCC` only see committed versions with `xmin <= startTs`).
  - `FindLatestVisibleVersion(versions, meta, elem)` — backwards/latest-`xmin` version resolver.
  - `CheckWriteAllowed(state, meta, elem)` — enforces No Dirty Writes, `CS` cursor pins, `RR` read locks, and `SI`/`Serializable` First-Committer-Wins.
  - `CheckCommitAllowed(state, meta)` — enforces First-Committer-Wins on `writeSet` (`SI` & `SerializableMVCC`) and `readSet` antidependency validation (`SerializableMVCC`, preventing Write Skew).
- **[MvccSimulator.dfy](MvccSimulator.dfy)** (`module MvccSimulation`):
  - Per-operation handlers (`StepBegin`, `StepRead`, `StepFetchCursor`, `StepCloseCursor`, `StepWrite`, `StepCommit`, `StepAbort`, `StepMvcc`, `SimulateSchedule`) preserving `ValidMvccState`.
  - Formal isolation & anomaly-prevention lemmas:
    - `LemmaCursorPinBlocksOtherWriter` (`CS` protects the currently positioned cursor item)
    - `LemmaRepeatableReadLockBlocksOtherWriter` (`RR` protects all read items until commit)
    - `LemmaFirstCommitterWinsPreventsLostUpdate` (`SI` prevents Lost Updates)
    - `LemmaSerializablePreventsWriteSkew` (`SerializableMVCC` prevents Write Skew)
- **[Main.dfy](Main.dfy)** (`module Main`) — Statically verified tests and runnable demonstrations for all 5 isolation levels.
