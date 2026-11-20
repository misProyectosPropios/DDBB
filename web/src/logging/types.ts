// Mirrors dafny/logging/Types.dfy — core domain types, Undo & Redo log records,
// checkpoint records, execution trace events, and string formatters.

export type TxId = string;
export type ElementId = string;
export type Value = number;
export type DatabaseState = Record<ElementId, Value>;

export type LogRecord =
  | { kind: "LogStart"; tx: TxId }
  | { kind: "LogUndoUpdate"; tx: TxId; element: ElementId; oldValue: Value }
  | { kind: "LogRedoUpdate"; tx: TxId; element: ElementId; newValue: Value }
  | { kind: "LogCommit"; tx: TxId }
  | { kind: "LogAbort"; tx: TxId }
  | { kind: "LogCheckpoint" }
  | { kind: "LogStartCheckpoint"; activeTxs: TxId[] }
  | { kind: "LogEndCheckpoint" };

export type TraceEvent =
  | { kind: "EventLog"; record: LogRecord }
  | { kind: "EventRead"; tx: TxId; element: ElementId; value: Value }
  | { kind: "EventWriteBuffer"; tx: TxId; element: ElementId; oldVal: Value; newVal: Value }
  | { kind: "EventUndoRestore"; tx: TxId; element: ElementId; restoredVal: Value }
  | { kind: "EventFlushLog"; flushedCount: number }
  | { kind: "EventOutput"; element: ElementId; value: Value };

export function finishedTxs(flushedLog: readonly LogRecord[]): Set<TxId> {
  const finished = new Set<TxId>();
  for (const rec of flushedLog) {
    if (rec.kind === "LogCommit" || rec.kind === "LogAbort") {
      finished.add(rec.tx);
    }
  }
  return finished;
}

export function committedTxs(flushedLog: readonly LogRecord[]): Set<TxId> {
  const committed = new Set<TxId>();
  for (const rec of flushedLog) {
    if (rec.kind === "LogCommit") {
      committed.add(rec.tx);
    }
  }
  return committed;
}

export function formatLogRecord(r: LogRecord): string {
  switch (r.kind) {
    case "LogStart":
      return `<START ${r.tx}>`;
    case "LogUndoUpdate":
      return `<${r.tx}, ${r.element}, ${r.oldValue}>`;
    case "LogRedoUpdate":
      return `<${r.tx}, ${r.element}, ${r.newValue}>`;
    case "LogCommit":
      return `<COMMIT ${r.tx}>`;
    case "LogAbort":
      return `<ABORT ${r.tx}>`;
    case "LogCheckpoint":
      return `<CKPT>`;
    case "LogStartCheckpoint":
      return `<START CKPT(${r.activeTxs.join(", ")})>`;
    case "LogEndCheckpoint":
      return `<END CKPT>`;
  }
}

export function formatTraceEvent(e: TraceEvent): string {
  switch (e.kind) {
    case "EventLog":
      return `LOG    ${formatLogRecord(e.record)}`;
    case "EventRead":
      return `READ   ${e.tx}(${e.element}) => ${e.value}`;
    case "EventWriteBuffer":
      return `WRITE  ${e.tx}(${e.element}): ${e.oldVal} -> ${e.newVal} [buffer]`;
    case "EventUndoRestore":
      return `UNDO   ${e.tx}(${e.element}) := ${e.restoredVal} [buffer]`;
    case "EventFlushLog":
      return `FLUSH  LOG (up to record #${e.flushedCount})`;
    case "EventOutput":
      return `OUTPUT ${e.element} = ${e.value} [disk]`;
  }
}
