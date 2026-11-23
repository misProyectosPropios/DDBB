// Mirrors dafny/logging/UndoRedoLogger.dfy — Undo/Redo Logging strategy
// composing a CheckpointStrategy (None, Quiescent, or Non-Quiescent).

import {
  NoCheckpointStrategy,
  type CheckpointState,
  type CheckpointStrategy
} from "./checkpointing";
import type { LoggingStepSnapshot, LoggingStrategy, Operation } from "./dispatch";
import type { DatabaseState, ElementId, LogRecord, TraceEvent, TxId, Value } from "./types";

export class UndoRedoLogger implements LoggingStrategy {
  private _log: LogRecord[] = [];
  private _trace: TraceEvent[] = [];
  private _errors: string[] = [];
  private _disk: DatabaseState;
  private _buffer: DatabaseState;
  private _flushedLogLen = 0;
  private _activeTxs = new Set<TxId>();
  private _activeOrder: TxId[] = [];
  private _committedTxs = new Set<TxId>();
  private _abortedTxs = new Set<TxId>();
  private _dirtyElements = new Map<TxId, ElementId[]>();
  private _ckptState: CheckpointState = { kind: "CkptIdle" };
  private _snapshots: LoggingStepSnapshot[] = [];

  constructor(
    initialDb: DatabaseState,
    readonly checkpointStrategy: CheckpointStrategy = new NoCheckpointStrategy()
  ) {
    this._disk = { ...initialDb };
    this._buffer = { ...initialDb };
    this._snapshots.push(this.captureSnapshot(0, "Initial State", 0));
  }

  get log(): readonly LogRecord[] {
    return this._log;
  }

  get trace(): readonly TraceEvent[] {
    return this._trace;
  }

  get errors(): readonly string[] {
    return this._errors;
  }

  get flushedLogLen(): number {
    return this._flushedLogLen;
  }

  get snapshots(): readonly LoggingStepSnapshot[] {
    return this._snapshots;
  }

  process(op: Operation): void {
    const traceStart = this._trace.length;
    op.accept(this);
    this._snapshots.push(
      this.captureSnapshot(this._snapshots.length, op.format(), traceStart)
    );
  }

  visitStart(tx: TxId): void {
    if (!this.checkpointStrategy.canStartTransaction(this._ckptState)) {
      this._errors.push(this.checkpointStrategy.blockedStartMessage(tx));
      return;
    }
    if (this._activeTxs.has(tx) || this._committedTxs.has(tx) || this._abortedTxs.has(tx)) {
      this._errors.push(`Cannot START ${tx}: transaction was already started.`);
      return;
    }

    const rec: LogRecord = { kind: "LogStart", tx };
    this._log.push(rec);
    this._trace.push({ kind: "EventLog", record: rec });
    this._activeTxs.add(tx);
    this._activeOrder.push(tx);
    this._dirtyElements.set(tx, []);
  }

  visitRead(tx: TxId, element: ElementId): void {
    if (!this._activeTxs.has(tx)) {
      this._errors.push(`Cannot READ in ${tx}: transaction is not active.`);
      return;
    }
    if (!(element in this._buffer)) {
      this._errors.push(`Cannot READ ${element} in ${tx}: unknown database element.`);
      return;
    }

    const value = this._buffer[element];
    this._trace.push({ kind: "EventRead", tx, element, value });
  }

  visitWrite(tx: TxId, element: ElementId, newValue: Value): void {
    if (!this._activeTxs.has(tx)) {
      this._errors.push(`Cannot WRITE in ${tx}: transaction is not active.`);
      return;
    }
    if (!(element in this._buffer)) {
      this._errors.push(`Cannot WRITE ${element} in ${tx}: unknown database element.`);
      return;
    }

    const oldVal = this._buffer[element];
    const rec: LogRecord = {
      kind: "LogUndoRedoUpdate",
      tx,
      element,
      oldValue: oldVal,
      newValue
    };
    this._log.push(rec);
    this._trace.push({ kind: "EventLog", record: rec });

    this._buffer[element] = newValue;
    this._trace.push({ kind: "EventWriteBuffer", tx, element, oldVal, newVal: newValue });

    const dirty = this._dirtyElements.get(tx) ?? [];
    if (!dirty.includes(element)) {
      dirty.push(element);
      this._dirtyElements.set(tx, dirty);
    }
  }

  visitCheckpoint(): void {
    // Undo/Redo non-quiescent checkpointing flushes the WAL, writes dirty buffer
    // elements to disk (STEAL), and emits <START CKPT(...)> + <END CKPT>.
    const res = this.checkpointStrategy.onCheckpointRequested(
      this._ckptState,
      this._activeOrder,
      false
    );
    if (res.error) {
      this._errors.push(res.error);
      return;
    }

    this.flushLogIfNeeded();
    for (const tx of this._activeOrder) {
      this.outputTxDirtyElements(tx);
    }
    this.applyCheckpointTransition(res.nextState, res.records);
  }

  private applyCheckpointTransition(nextState: CheckpointState, records: LogRecord[]): void {
    for (const rec of records) {
      this._log.push(rec);
      this._trace.push({ kind: "EventLog", record: rec });
    }
    if (records.length > 0) {
      this.flushLogIfNeeded();
    }
    this._ckptState = nextState;
  }

  private flushLogIfNeeded(): void {
    if (this._flushedLogLen < this._log.length) {
      this._flushedLogLen = this._log.length;
      this._trace.push({ kind: "EventFlushLog", flushedCount: this._flushedLogLen });
    }
  }

  private outputTxDirtyElements(tx: TxId): void {
    const dirty = this._dirtyElements.get(tx) ?? [];
    for (const elem of dirty) {
      const value = this._buffer[elem];
      this._disk[elem] = value;
      this._trace.push({ kind: "EventOutput", element: elem, value });
    }
  }

  visitCommit(tx: TxId): void {
    if (!this._activeTxs.has(tx)) {
      this._errors.push(`Cannot COMMIT ${tx}: transaction is not active.`);
      return;
    }

    // Rule UR1 (WAL): emit <COMMIT tx>, flush the log to disk, and output dirty
    // elements (in Undo/Redo logging, OUTPUT may happen either before or after COMMIT
    // as long as the log is flushed before OUTPUT).
    const rec: LogRecord = { kind: "LogCommit", tx };
    this._log.push(rec);
    this._trace.push({ kind: "EventLog", record: rec });

    this._flushedLogLen = this._log.length;
    this._trace.push({ kind: "EventFlushLog", flushedCount: this._flushedLogLen });

    this.outputTxDirtyElements(tx);

    this._activeTxs.delete(tx);
    this._activeOrder = this._activeOrder.filter((t) => t !== tx);
    this._committedTxs.add(tx);
    this._dirtyElements.delete(tx);

    const res = this.checkpointStrategy.onTransactionFinished(
      this._ckptState,
      tx,
      this._activeOrder
    );
    this.applyCheckpointTransition(res.nextState, res.records);
  }

  visitAbort(tx: TxId): void {
    if (!this._activeTxs.has(tx)) {
      this._errors.push(`Cannot ABORT ${tx}: transaction is not active.`);
      return;
    }

    for (let idx = this._log.length - 1; idx >= 0; idx--) {
      const rec = this._log[idx];
      if (rec.kind === "LogUndoRedoUpdate" && rec.tx === tx) {
        this._buffer[rec.element] = rec.oldValue;
        this._trace.push({
          kind: "EventUndoRestore",
          tx,
          element: rec.element,
          restoredVal: rec.oldValue
        });
      }
    }

    const rec: LogRecord = { kind: "LogAbort", tx };
    this._log.push(rec);
    this._trace.push({ kind: "EventLog", record: rec });

    this._flushedLogLen = this._log.length;
    this._trace.push({ kind: "EventFlushLog", flushedCount: this._flushedLogLen });

    this._activeTxs.delete(tx);
    this._activeOrder = this._activeOrder.filter((t) => t !== tx);
    this._abortedTxs.add(tx);
    this._dirtyElements.delete(tx);

    const res = this.checkpointStrategy.onTransactionFinished(
      this._ckptState,
      tx,
      this._activeOrder
    );
    this.applyCheckpointTransition(res.nextState, res.records);
  }

  getLog(): readonly LogRecord[] {
    return this._log;
  }

  getTrace(): readonly TraceEvent[] {
    return this._trace;
  }

  getErrors(): readonly string[] {
    return this._errors;
  }

  getFlushedLog(): LogRecord[] {
    return this._log.slice(0, this._flushedLogLen);
  }

  getDisk(): DatabaseState {
    return { ...this._disk };
  }

  getBuffer(): DatabaseState {
    return { ...this._buffer };
  }

  getCheckpointState(): CheckpointState {
    return this._ckptState.kind === "CkptActiveNonQuiescent"
      ? { kind: "CkptActiveNonQuiescent", watchedTxs: [...this._ckptState.watchedTxs] }
      : { ...this._ckptState };
  }

  private captureSnapshot(
    stepIndex: number,
    operationLabel: string,
    newTraceStart: number
  ): LoggingStepSnapshot {
    return {
      stepIndex,
      operationLabel,
      log: [...this._log],
      trace: [...this._trace],
      newTraceStart,
      errors: [...this._errors],
      flushedLogLen: this._flushedLogLen,
      disk: { ...this._disk },
      buffer: { ...this._buffer },
      activeTxs: [...this._activeOrder],
      committedTxs: Array.from(this._committedTxs),
      abortedTxs: Array.from(this._abortedTxs),
      ckptState: this.getCheckpointState()
    };
  }
}
