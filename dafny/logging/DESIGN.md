# Logging Module — Class & Method Specification (Plain English)

This document describes what every module, type, trait, class, method, and helper in `dafny/logging/` is responsible for, along with what each one expects before running and guarantees afterward—written in plain, precise language rather than formal logic.

---

## 1. `Types.dfy` (`module LoggingTypes`)

Defines the shared vocabulary for database states, Undo log records, execution trace events, Undo correctness rules, and human-readable formatting.

### Data Types
- **`TxId` / `ElementId` / `Value` / `DatabaseState`**:
  - Transaction names (`"T1"`), database element names (`"A"`), integer values (`8`), and a mapping from element names to their integer values.
- **`LogRecord`**: Represents one record written to the database Undo log:
  - `LogStart(tx)` — marks that transaction `tx` has started (`<START tx>`).
  - `LogUndoUpdate(tx, element, oldValue)` — records the value `element` had *before* `tx` overwrote it (`<tx, element, oldValue>`).
  - `LogCommit(tx)` — marks that `tx` has committed (`<COMMIT tx>`).
  - `LogAbort(tx)` — marks that `tx` has aborted (`<ABORT tx>`).
- **`TraceEvent`**: Represents one observable step in the full execution history:
  - `EventLog(record)` — a log record was appended to the log buffer.
  - `EventRead(tx, element, value)` — `tx` read `value` from `element` in memory.
  - `EventWriteBuffer(tx, element, oldVal, newVal)` — `tx` updated `element` in memory from `oldVal` to `newVal`.
  - `EventUndoRestore(tx, element, restoredVal)` — aborting `tx` restored `element` in memory back to `restoredVal`.
  - `EventFlushLog(flushedCount)` — the log buffer was flushed to disk up to record number `flushedCount`.
  - `EventOutput(element, value)` — `element`'s current value was written from memory out to disk.

### Trace Projection Helpers
- **`ExtractLog(t)`**: Walks through a trace and returns only the `LogRecord`s that were emitted, in the exact order they appeared.
- **`LastFlushedCount(t)`**: Returns the record count from the most recent `EventFlushLog` in the trace, or `0` if the log has never been flushed.

### Correctness Rules (Checked Internally by the Verifier)
- **`HasStart(log, tx)` / `HasCommit(log, tx)` / `HasAbort(log, tx)`**: Checks whether `log` contains a start, commit, or abort record for `tx`.
- **`StartBeforeEnd(log)`**: Checks that every commit or abort record in `log` is preceded somewhere earlier in `log` by a start record for the same transaction.
- **`WriteHasUndoLogBefore(t)`**: Checks that every in-memory buffer write in the trace is immediately preceded by the matching `<tx, element, oldVal>` Undo log record.
- **`RuleU1_FlushBeforeOutput(t)` (Write-Ahead Logging)**: Checks that right before any `OUTPUT` writes an element to disk, every log record emitted up to that moment has already been flushed to disk.
- **`RuleU2_OutputBeforeCommit(t)` (Output Before Commit)**: Checks that right before `<COMMIT tx>` appears in the trace, every element that `tx` wrote in memory has already been written out to disk (`OUTPUT`) at some point after that write.

### Proof Support Lemmas
These do no work at runtime; they exist only to help Dafny confirm that appending one new record or trace event does not break earlier guarantees:
- **`LemmaAppendPreservesRuleU1(t, e)`**: Expects Rule U1 to hold on `t` (and if `e` is an `OUTPUT`, expects the log to already be fully flushed). Guarantees Rule U1 still holds after appending `e`.
- **`LemmaAppendNonCommitPreservesRuleU2(t, e)`**: Expects Rule U2 to hold on `t` and `e` not to be a commit log event. Guarantees Rule U2 still holds after appending `e`.
- **`LemmaAppendCommitPreservesRuleU2(t, tx)`**: Expects Rule U2 to hold on `t` and every earlier buffer write by `tx` to already have a later `OUTPUT` in `t`. Guarantees Rule U2 still holds after appending `<COMMIT tx>`.
- **`LemmaAppendNonWritePreservesTrace(t, e)`**: Expects `e` not to be a buffer write or a commit log record, and all trace rules (Write-Ahead, Rule U1, Rule U2) to hold on `t` (with the log flushed if `e` is an `OUTPUT`). Guarantees that appending `e` extends `t` without altering earlier events, updates `ExtractLog` and `LastFlushedCount` as expected, and preserves all three trace rules.
- **`LemmaAppendLogPreservesLifecycle(log, rec)`**: Expects `StartBeforeEnd` to hold on `log`, and if `rec` is a commit or abort, expects `tx` to already have a start record in `log`. Guarantees `StartBeforeEnd` still holds after appending `rec`, and existing start/commit/abort facts for all transactions remain intact.

### Formatting Functions
- **`DigitToString(d)`**: Expects a single digit from `0` to `9`; returns its one-character string.
- **`NatToString(n)` / `IntToString(n)`**: Converts a non-negative or signed integer to its decimal string.
- **`FormatLogRecord(r)` / `FormatLog(log)`**: Formats one log record (e.g., `<T1, A, 8>`) or a full log as newline-separated text.
- **`FormatTraceEvent(e)` / `FormatTrace(trace)`**: Formats one trace event or a full execution trace as newline-separated text.

---

## 2. `Dispatch.dfy` (`module LoggingDispatch`)

Defines the Visitor / Dispatch contract that decouples schedule operations from concrete logging strategies (such as Undo now, and Redo, Undo/Redo, or checkpointing later).

### `datatype Operation`
Represents one high-level action in a schedule (`StartOp`, `ReadOp`, `WriteOp`, `CommitOp`, or `AbortOp`).
- **`Accept(visitor)`**:
  - **What it does**: Inspects which operation variant this value is and calls the matching `VisitStart`, `VisitRead`, `VisitWrite`, `VisitCommit`, or `VisitAbort` method on `visitor`.
  - **Expects before running**: `visitor` must currently be in a valid internal state.
  - **Guarantees after running**: `visitor` remains in a valid internal state, and neither its log nor its trace loses or rewrites any previously recorded entries (both can only grow).

### `trait LoggingStrategy`
The common interface that every logging strategy implements. Holds the strategy's `log`, `trace`, and `errors`.
- **`Valid()`**: Describes what it means for a concrete strategy's internal state to be consistent. Each subclass defines its own exact rules.
- **`VisitStart(tx)` / `VisitRead(tx, element)` / `VisitWrite(tx, element, newValue)` / `VisitCommit(tx)` / `VisitAbort(tx)`**:
  - **What they do**: Handle one specific operation according to the concrete logging protocol.
  - **Expects before running**: The strategy is in a valid state.
  - **Guarantees after running**: The strategy remains in a valid state, and its `log` and `trace` only grow (append-only).
- **`Process(op)`**:
  - **What it does**: Entry point for dispatch—receives an `Operation` and passes itself to `op.Accept(this)`, which calls back into the appropriate `Visit*` method.
  - **Expects before running**: The strategy is in a valid state.
  - **Guarantees after running**: The strategy remains valid and its `log` and `trace` only grow.
- **`GetLog()` / `GetTrace()` / `GetErrors()`**:
  - **What they do**: Return the strategy's current log records, execution trace events, or accumulated error messages without changing any state.

### `datatype Schedule`
Holds an ordered list of `Operation` values (`operations`).
- **`GenerateLog(strategy)`**:
  - **What it does**: Iterates through `operations` from start to finish, passing each one to `strategy.Process(op)`, and returns the resulting `log`.
  - **Expects before running**: `strategy` is in a valid state.
  - **Guarantees after running**: `strategy` remains valid, its `log` and `trace` only grew from before the run, and the returned sequence is `strategy`'s log.
- **`Run(strategy)`**:
  - **What it does**: Calls `GenerateLog(strategy)` and returns all three outputs together: the generated log, the full execution trace, and any validation errors.
  - **Expects before running**: `strategy` is in a valid state.
  - **Guarantees after running**: Same as `GenerateLog`, and each returned value matches `strategy`'s final `log`, `trace`, and `errors`.

---

## 3. `UndoLogger.dfy` (`module UndoLogging`)

Implements pure Undo Logging (without checkpoints) by extending `LoggingStrategy`.

### `class UndoLogger`
Tracks the in-memory `buffer`, on-disk `disk`, how many log records have been flushed (`flushedLogLen`), the sets of `activeTxs`, `committedTxs`, and `abortedTxs`, and the ordered list of modified (`dirtyElements`) per active transaction.

- **`Valid()`** (internal invariant maintained across every operation):
  - Active, committed, and aborted transaction sets never overlap.
  - Memory `buffer` and `disk` always contain the exact same set of database elements.
  - `dirtyElements` has an entry for every active transaction (and no others), and every dirty element exists in the database.
  - `flushedLogLen` never exceeds the length of `log`, and the log records and flush position inside `trace` always match `log` and `flushedLogLen`.
  - Every log record belongs to a known transaction; every Undo update refers to an existing element; active transactions have a start record and no commit/abort; committed transactions have start + commit and no abort; aborted transactions have start + abort and no commit; every commit/abort comes after a start.
  - Every buffer write is preceded by its Undo log record, Rule U1 holds for every `OUTPUT`, Rule U2 holds for every `COMMIT`, and every element written by an active transaction is listed in its `dirtyElements`.

- **`constructor(initialDb)`**:
  - **What it does**: Initializes both `disk` and `buffer` to `initialDb`, with empty `log`, `trace`, `errors`, empty transaction sets, empty `dirtyElements`, and `flushedLogLen` at `0`.
  - **Expects before running**: Nothing (any initial database map is accepted).
  - **Guarantees after running**: The new logger starts in a valid state with matching `disk` and `buffer` and no recorded history yet.

- **`VisitStart(tx)`**:
  - **What it does**: If `tx` was already started (active, committed, or aborted), appends an error message and leaves everything else untouched. Otherwise, emits `<START tx>` to `log` and `trace`, adds `tx` to `activeTxs`, and initializes `dirtyElements[tx]` as empty.
  - **Expects before running**: Logger is valid.
  - **Guarantees after running**: Logger stays valid, `log` and `trace` only grow. If `tx` was brand-new, `<START tx>` is appended, `tx` becomes active, `buffer`/`disk`/`flushedLogLen`/`errors` do not change, and committed/aborted sets stay unchanged.

- **`VisitRead(tx, element)`**:
  - **What it does**: Checks that `tx` is active and `element` exists in `buffer`; if either check fails, records an error and returns. Otherwise, reads the current value from `buffer` and appends an `EventRead` to `trace`. Does not emit any log record.
  - **Expects before running**: Logger is valid.
  - **Guarantees after running**: Logger stays valid, `trace` only grows, and `log`, `buffer`, `disk`, `flushedLogLen`, and all transaction sets remain completely unchanged. If `tx` was active and `element` existed, no error is added.

- **`VisitWrite(tx, element, newValue)`**:
  - **What it does**: Checks that `tx` is active and `element` exists in `buffer`; if either check fails, records an error and returns. Otherwise, reads `oldVal` from `buffer[element]`, emits `<tx, element, oldVal>` to `log` and `trace`, updates `buffer[element]` to `newValue`, records `EventWriteBuffer` in `trace`, and adds `element` to `dirtyElements[tx]` if not already listed. Does not write to `disk` or flush the log yet.
  - **Expects before running**: Logger is valid.
  - **Guarantees after running**: Logger stays valid, `log` and `trace` only grow. If `tx` was active and `element` existed, the Undo record with the previous buffer value is appended to `log`, `buffer` reflects `newValue`, `disk`, `flushedLogLen`, transaction sets, and `errors` are unchanged.

- **`FlushLogIfNeeded()`** *(Commit helper — Rule U1)*:
  - **What it does**: If there are unflushed records in `log` (`flushedLogLen` is behind the length of `log`), advances `flushedLogLen` to the end of `log` and appends `EventFlushLog` to `trace`. Does nothing if the log is already fully flushed.
  - **Expects before running**: Logger is valid.
  - **Guarantees after running**: Logger stays valid, `trace` only grows, the entire `log` is now flushed, and all other fields (`log`, `buffer`, `disk`, transaction sets, `dirtyElements`, `errors`) are unchanged.

- **`OutputDirtyElements(tx)`** *(Commit helper — Rule U2)*:
  - **What it does**: Loops through `dirtyElements[tx]` in insertion order, copying each element's value from `buffer` to `disk` and recording an `EventOutput` in `trace`.
  - **Expects before running**: Logger is valid, `tx` is active, and the log is already fully flushed (Rule U1 satisfied).
  - **Guarantees after running**: Logger stays valid, `trace` only grows, the log stays fully flushed, every buffer write `tx` ever performed now has a subsequent `EventOutput` in `trace`, and `log`, `buffer`, transaction sets, `dirtyElements`, and `errors` are unchanged.

- **`EmitCommitAndFinalize(tx)`** *(Commit helper — Finalize)*:
  - **What it does**: Appends `<COMMIT tx>` to `log` and `trace`, flushes the log to disk, and moves `tx` from `activeTxs` to `committedTxs` while removing `tx` from `dirtyElements`.
  - **Expects before running**: Logger is valid, `tx` is active, and every element written by `tx` has already been `OUTPUT` to disk.
  - **Guarantees after running**: Logger stays valid, `log` has `<COMMIT tx>` appended, the entire log is flushed, `tx` is now committed and no longer active, and no errors were added.

- **`VisitCommit(tx)`**:
  - **What it does**: If `tx` is not active, records an error and returns. Otherwise runs the three commit steps in order: `FlushLogIfNeeded()`, `OutputDirtyElements(tx)`, and `EmitCommitAndFinalize(tx)`.
  - **Expects before running**: Logger is valid.
  - **Guarantees after running**: Logger stays valid, `log` and `trace` only grow. If `tx` was active, `<COMMIT tx>` is appended and flushed, `tx` moves to `committedTxs`, and no error is recorded.

- **`RollbackTxBuffer(tx)`** *(Abort helper — Undo in memory)*:
  - **What it does**: Scans `log` backwards from end to start; whenever it sees an Undo update `<tx, element, oldVal>` for `tx`, it restores `buffer[element]` back to `oldVal` and records `EventUndoRestore` in `trace`.
  - **Expects before running**: Logger is valid and `tx` is active.
  - **Guarantees after running**: Logger stays valid, `trace` only grows, and `log`, `flushedLogLen`, `disk`, transaction sets, `dirtyElements`, and `errors` remain unchanged.

- **`EmitAbortAndFinalize(tx)`** *(Abort helper — Finalize)*:
  - **What it does**: Appends `<ABORT tx>` to `log` and `trace`, flushes the log to disk, and moves `tx` from `activeTxs` to `abortedTxs` while removing `tx` from `dirtyElements`.
  - **Expects before running**: Logger is valid and `tx` is active.
  - **Guarantees after running**: Logger stays valid, `log` has `<ABORT tx>` appended, the entire log is flushed, `tx` is now aborted and no longer active, and no errors were added.

- **`VisitAbort(tx)`**:
  - **What it does**: If `tx` is not active, records an error and returns. Otherwise runs `RollbackTxBuffer(tx)` followed by `EmitAbortAndFinalize(tx)`.
  - **Expects before running**: Logger is valid.
  - **Guarantees after running**: Logger stays valid, `log` and `trace` only grow. If `tx` was active, `<ABORT tx>` is appended and flushed, `tx` moves to `abortedTxs`, and no error is recorded.

- **Inspection Accessors**:
  - **`GetFlushedLog()`**: Expects the logger to be valid; returns only the prefix of `log` that has been flushed to disk.
  - **`GetDisk()` / `GetBuffer()` / `GetActiveTxs()` / `GetCommittedTxs()` / `GetAbortedTxs()`**: Return the current on-disk state, memory buffer, or transaction sets without modifying anything.

### Module-Level Helpers in `UndoLogging`
- **`LemmaEventLogInExtractLog(t, k)`**: Proof helper expecting `k` to point to an `EventLog` entry in `t`; guarantees that exact log record appears somewhere inside `ExtractLog(t)`.
- **`GenerateUndoLog(initialDb, schedule)`**: Convenience entry point that creates a fresh `UndoLogger(initialDb)`, runs `schedule.Run(logger)`, and returns `(logResult, traceResult, errorResult)`.

---

## 4. `UndoRecovery.dfy` (`module UndoRecovery`)

Implements crash recovery from an on-disk database state and the flushed portion of an Undo log.

### Helper Functions
- **`FinishedTxs(flushedLog)`**: Returns all transaction IDs that have either a `<COMMIT T>` or `<ABORT T>` record in `flushedLog`.
- **`StartedTxs(flushedLog)`**: Returns all transaction IDs that have a `<START T>` record in `flushedLog`.
- **`IncompleteTxs(flushedLog)`**: Returns all transactions that started in `flushedLog` but have neither committed nor aborted.
- **`UnfinishedModifiedElements(flushedLog)`**: Returns the set of database elements that were modified by at least one unfinished transaction in `flushedLog`.

### Recovery Method
- **`RecoverFromCrash(diskAtCrash, flushedLog)`**:
  - **What it does**: Scans `flushedLog` backwards from the last record to the first:
    - For each `<tx, elem, oldVal>` belonging to an unfinished transaction (and where `elem` exists on disk), overwrites `recoveredDisk[elem]` with `oldVal`.
    - For each `<START tx>` belonging to an unfinished transaction not yet aborted during recovery, appends `<ABORT tx>` to `recoveryAborts`.
    - Skips committed and already-aborted transactions (Rule U2 ensures committed transactions already have their writes on disk).
  - **Expects before running**: Nothing beyond a valid disk map and flushed log sequence.
  - **Guarantees after running**:
    - `recoveredDisk` has the exact same set of element keys as `diskAtCrash`.
    - Any database element not touched by an unfinished transaction keeps its exact value from `diskAtCrash`.
    - Every record in `recoveryAborts` is an `<ABORT tx>` for an unfinished transaction, with no duplicate abort records for the same transaction.

---

## 5. `Main.dfy` (`module Main`)

Provides compile-time verified assertions and runnable end-to-end demonstrations.

- **`TestSingleTransactionUndoVerified()`**: Steps directly through `VisitStart`, `VisitRead`, `VisitWrite`, and `VisitCommit` on the classic `T1` (`A: 8 -> 16`, `B: 8 -> 16`) example and statically verifies the exact Undo log, buffer/disk values, flush length, and committed status.
- **`DemoSingleTransactionSchedule()`**: Runs the same `T1` scenario polymorphically through `Schedule.Run(logger)`, checks the expected log and disk values, and prints both the Undo log and full execution trace.
- **`DemoInterleavedCommitAndAbort()`**: Runs two interleaved transactions where `T1` commits and `T2` aborts, verifying that `T1`'s write persists to disk while `T2`'s write is rolled back in memory and never reaches disk.
- **`DemoCrashRecovery()`**: Runs `T1` (commits) and `T2` (writes without committing), simulates a crash where `T2`'s dirty write reached disk, runs `RecoverFromCrash`, and checks that `T1`'s write stays intact while `T2`'s write is restored and `<ABORT T2>` is emitted.
- **`DemoInvalidSchedule()`**: Feeds invalid operations (writing before `START`, writing to an unknown element) alongside valid ones and checks that errors are captured while valid operations still log cleanly.
- **`Main()`**: Executes all verification tests and demos in sequence.
