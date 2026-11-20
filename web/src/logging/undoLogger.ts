// Mirrors dafny/logging/UndoLogger.dfy — Simple (Pure) Undo Logging strategy
// enforcing Rules U1 (Flush before Output) and U2 (Output before Commit).

import type { LoggingStrategy, Operation } from "./dispatch";
import type { DatabaseState, ElementId, LogRecord, TraceEvent, TxId, Value } from "./types";

export interface UndoStepSnapshot {
  stepIndex: number;
  operationLabel: string;
  log: LogRecord[];
  trace: TraceEvent[];
  newTraceStart: number;
  errors: string[];
  flushedLogLen: number;
  disk: DatabaseState;
  buffer: DatabaseState;
  activeTxs: TxId[];
  committedTxs: TxId[];
  abortedTxs: TxId[];
}

export class UndoLogger implements LoggingStrategy {
  private _log: LogRecord[] = [];
  private _trace: TraceEvent[] = [];
  private _errors: string[] = [];
  private _disk: DatabaseState;
  private _buffer: DatabaseState;
  private _flushedLogLen = 0;
  private _activeTxs = new Set<TxId>();
  private _committedTxs = new Set<TxId>();
  private _abortedTxs = new Set<TxId>();
  private _dirtyElements = new Map<TxId, ElementId[]>();
  private _snapshots: UndoStepSnapshot[] = [];

  constructor(initialDb: DatabaseState) {
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

  get snapshots(): readonly UndoStepSnapshot[] {
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
    if (this._activeTxs.has(tx) || this._committedTxs.has(tx) || this._abortedTxs.has(tx)) {
      this._errors.push(`Cannot START ${tx}: transaction was already started.`);
      return;
    }

    const rec: LogRecord = { kind: "LogStart", tx };
    this._log.push(rec);
    this._trace.push({ kind: "EventLog", record: rec });
    this._activeTxs.add(tx);
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
    const rec: LogRecord = { kind: "LogUndoUpdate", tx, element, oldValue: oldVal };
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

  private flushLogIfNeeded(): void {
    if (this._flushedLogLen < this._log.length) {
      this._flushedLogLen = this._log.length;
      this._trace.push({ kind: "EventFlushLog", flushedCount: this._flushedLogLen });
    }
  }

  private outputDirtyElements(tx: TxId): void {
    const dirty = this._dirtyElements.get(tx) ?? [];
    for (const elem of dirty) {
      const value = this._buffer[elem];
      this._disk[elem] = value;
      this._trace.push({ kind: "EventOutput", element: elem, value });
    }
  }

  private emitCommitAndFinalize(tx: TxId): void {
    const rec: LogRecord = { kind: "LogCommit", tx };
    this._log.push(rec);
    this._trace.push({ kind: "EventLog", record: rec });

    this._flushedLogLen = this._log.length;
    this._trace.push({ kind: "EventFlushLog", flushedCount: this._flushedLogLen });

    this._activeTxs.delete(tx);
    this._committedTxs.add(tx);
    this._dirtyElements.delete(tx);
  }

  visitCommit(tx: TxId): void {
    if (!this._activeTxs.has(tx)) {
      this._errors.push(`Cannot COMMIT ${tx}: transaction is not active.`);
      return;
    }

    this.flushLogIfNeeded();
    this.outputDirtyElements(tx);
    this.emitCommitAndFinalize(tx);
  }

  private rollbackTxBuffer(tx: TxId): void {
    for (let idx = this._log.length - 1; idx >= 0; idx--) {
      const rec = this._log[idx];
      if (rec.kind === "LogUndoUpdate" && rec.tx === tx) {
        this._buffer[rec.element] = rec.oldValue;
        this._trace.push({
          kind: "EventUndoRestore",
          tx,
          element: rec.element,
          restoredVal: rec.oldValue
        });
      }
    }
  }

  private emitAbortAndFinalize(tx: TxId): void {
    const rec: LogRecord = { kind: "LogAbort", tx };
    this._log.push(rec);
    this._trace.push({ kind: "EventLog", record: rec });

    this._flushedLogLen = this._log.length;
    this._trace.push({ kind: "EventFlushLog", flushedCount: this._flushedLogLen });

    this._activeTxs.delete(tx);
    this._abortedTxs.add(tx);
    this._dirtyElements.delete(tx);
  }

  visitAbort(tx: TxId): void {
    if (!this._activeTxs.has(tx)) {
      this._errors.push(`Cannot ABORT ${tx}: transaction is not active.`);
      return;
    }

    this.rollbackTxBuffer(tx);
    this.emitAbortAndFinalize(tx);
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

  private captureSnapshot(
    stepIndex: number,
    operationLabel: string,
    newTraceStart: number
  ): UndoStepSnapshot {
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
      activeTxs: Array.from(this._activeTxs),
      committedTxs: Array.from(this._committedTxs),
      abortedTxs: Array.from(this._abortedTxs)
    };
  }
}
