// Mirrors dafny/logging/Dispatch.dfy — Visitor / Double-Dispatch protocol
// connecting Schedule Operations and Logging Strategies.

import type { LogRecord, TraceEvent, TxId, ElementId, Value } from "./types";

export interface LoggingStrategy {
  readonly log: readonly LogRecord[];
  readonly trace: readonly TraceEvent[];
  readonly errors: readonly string[];

  visitStart(tx: TxId): void;
  visitRead(tx: TxId, element: ElementId): void;
  visitWrite(tx: TxId, element: ElementId, newValue: Value): void;
  visitCommit(tx: TxId): void;
  visitAbort(tx: TxId): void;

  process(op: Operation): void;
  getLog(): readonly LogRecord[];
  getTrace(): readonly TraceEvent[];
  getErrors(): readonly string[];
}

export interface Operation {
  readonly kind: "START" | "READ" | "WRITE" | "COMMIT" | "ABORT";
  readonly tx: TxId;
  accept(visitor: LoggingStrategy): void;
  format(): string;
}

export class StartOp implements Operation {
  readonly kind = "START" as const;
  constructor(readonly tx: TxId) {}

  accept(visitor: LoggingStrategy): void {
    visitor.visitStart(this.tx);
  }

  format(): string {
    return `START ${this.tx}`;
  }
}

export class ReadOp implements Operation {
  readonly kind = "READ" as const;
  constructor(
    readonly tx: TxId,
    readonly element: ElementId
  ) {}

  accept(visitor: LoggingStrategy): void {
    visitor.visitRead(this.tx, this.element);
  }

  format(): string {
    return `READ ${this.tx} ${this.element}`;
  }
}

export class WriteOp implements Operation {
  readonly kind = "WRITE" as const;
  constructor(
    readonly tx: TxId,
    readonly element: ElementId,
    readonly newValue: Value
  ) {}

  accept(visitor: LoggingStrategy): void {
    visitor.visitWrite(this.tx, this.element, this.newValue);
  }

  format(): string {
    return `WRITE ${this.tx} ${this.element} ${this.newValue}`;
  }
}

export class CommitOp implements Operation {
  readonly kind = "COMMIT" as const;
  constructor(readonly tx: TxId) {}

  accept(visitor: LoggingStrategy): void {
    visitor.visitCommit(this.tx);
  }

  format(): string {
    return `COMMIT ${this.tx}`;
  }
}

export class AbortOp implements Operation {
  readonly kind = "ABORT" as const;
  constructor(readonly tx: TxId) {}

  accept(visitor: LoggingStrategy): void {
    visitor.visitAbort(this.tx);
  }

  format(): string {
    return `ABORT ${this.tx}`;
  }
}

export interface ScheduleRunResult {
  log: readonly LogRecord[];
  trace: readonly TraceEvent[];
  errors: readonly string[];
}

export class Schedule {
  constructor(readonly operations: readonly Operation[]) {}

  generateLog(strategy: LoggingStrategy): readonly LogRecord[] {
    for (const op of this.operations) {
      strategy.process(op);
    }
    return strategy.getLog();
  }

  run(strategy: LoggingStrategy): ScheduleRunResult {
    const log = this.generateLog(strategy);
    return {
      log,
      trace: strategy.getTrace(),
      errors: strategy.getErrors()
    };
  }
}
