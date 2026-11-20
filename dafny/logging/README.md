# Dafny Logging Module (Pure Undo Logging)

Formally verified database logging engine written in Dafny, starting with **Simple (Pure) Undo Logging** (without checkpointing — quiescent and non-quiescent checkpointing, Redo, and Undo/Redo will extend the same strategy trait later).

## Architecture & Double Dispatch

The module uses the **Double Dispatch (Visitor) pattern** so `Schedule` and `Operation` objects stay decoupled from concrete logging strategies:

```text
Schedule.GenerateLog(strategy)
  └─> strategy.Process(op)        (1st dispatch: LoggingStrategy receives Operation)
        └─> op.Accept(strategy)   (2nd dispatch: Operation resolves its concrete type)
              └─> strategy.Visit*(op)
```

- **[Types.dfy](Types.dfy)** (`module LoggingTypes`) — `LogRecord`, `TraceEvent`, formatting functions, and formal Undo specifications (`RuleU1_FlushBeforeOutput`, `RuleU2_OutputBeforeCommit`, `WriteHasUndoLogBefore`, `StartBeforeEnd`).
- **[Dispatch.dfy](Dispatch.dfy)** (`module LoggingDispatch`) — `Operation` datatype (`StartOp`, `ReadOp`, `WriteOp`, `CommitOp`, `AbortOp`) with `Accept(visitor: LoggingStrategy)`, `LoggingStrategy` trait, and `Schedule` datatype runner (`GenerateLog` / `Run`).
- **[UndoLogger.dfy](UndoLogger.dfy)** (`module UndoLogging`) — `UndoLogger extends LoggingStrategy`, implementing pure Undo logging and proving its invariants (`Valid()`).
- **[UndoRecovery.dfy](UndoRecovery.dfy)** (`module UndoRecovery`) — `RecoverFromCrash`, scanning a flushed Undo log backwards to roll back unfinished transactions.
- **[Main.dfy](Main.dfy)** (`module Main`) — Statically verified assertions and runnable schedule demos.

## Verified Properties

1. **Append-only monotonic log & trace**: `old(log) <= log` and `old(trace) <= trace` across every operation and schedule run.
2. **Rule U1 (Write-Ahead Logging)**: Before any `OUTPUT(X)` writes to disk, all prior log records are flushed (`LastFlushedCount(t[..i]) == |ExtractLog(t[..i])|`).
3. **Rule U2 (Output Before Commit)**: Before `<COMMIT T>` is emitted, every database element written by `T` has been `OUTPUT` to disk.
4. **Transaction lifecycle consistency**: `activeTxs`, `committedTxs`, and `abortedTxs` remain pairwise disjoint, and every `<COMMIT T>` / `<ABORT T>` is preceded by `<START T>`.
5. **Recovery preservation**: Elements untouched by unfinished transactions remain intact during Undo crash recovery.

## Running & Compiling with Dafny

```bash
# Formally verify all modules
dafny verify dafny/logging/Main.dfy

# Run the demos and tests
dafny run dafny/logging/Main.dfy

# Compile to JavaScript for the web frontend later
dafny build --target:js dafny/logging/Main.dfy
```
