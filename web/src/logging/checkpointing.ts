// Mirrors dafny/logging/Checkpointing.dfy — Composable CheckpointStrategy
// interface and NoCheckpoint / Quiescent / NonQuiescent implementations.

import type { LogRecord, TxId } from "./types";

export type CheckpointMode = "none" | "quiescent" | "non-quiescent";

export type CheckpointState =
  | { kind: "CkptIdle" }
  | { kind: "CkptDrainingQuiescent" }
  | { kind: "CkptActiveNonQuiescent"; watchedTxs: TxId[] };

export function formatCheckpointState(state: CheckpointState): string {
  switch (state.kind) {
    case "CkptIdle":
      return "Idle";
    case "CkptDrainingQuiescent":
      return "Draining (blocking new START)";
    case "CkptActiveNonQuiescent":
      return `Active (watching ${state.watchedTxs.join(", ")})`;
  }
}

export interface CheckpointRequestResult {
  nextState: CheckpointState;
  records: LogRecord[];
  error: string;
}

export interface CheckpointFinishResult {
  nextState: CheckpointState;
  records: LogRecord[];
}

export interface CheckpointStrategy {
  readonly mode: CheckpointMode;
  readonly name: string;

  canStartTransaction(state: CheckpointState): boolean;
  blockedStartMessage(tx: TxId): string;

  onCheckpointRequested(
    state: CheckpointState,
    activeOrder: readonly TxId[],
    waitsForActiveOnNonQuiescent: boolean
  ): CheckpointRequestResult;

  onTransactionFinished(
    state: CheckpointState,
    tx: TxId,
    remainingActiveOrder: readonly TxId[]
  ): CheckpointFinishResult;
}

export class NoCheckpointStrategy implements CheckpointStrategy {
  readonly mode = "none" as const;
  readonly name = "None";

  canStartTransaction(): boolean {
    return true;
  }

  blockedStartMessage(): string {
    return "";
  }

  onCheckpointRequested(state: CheckpointState): CheckpointRequestResult {
    return {
      nextState: state,
      records: [],
      error: "Checkpointing is disabled for this logger."
    };
  }

  onTransactionFinished(): CheckpointFinishResult {
    return { nextState: { kind: "CkptIdle" }, records: [] };
  }
}

export class QuiescentCheckpointStrategy implements CheckpointStrategy {
  readonly mode = "quiescent" as const;
  readonly name = "Quiescent";

  canStartTransaction(state: CheckpointState): boolean {
    return state.kind !== "CkptDrainingQuiescent";
  }

  blockedStartMessage(tx: TxId): string {
    return `Cannot START ${tx}: quiescent checkpoint is waiting for active transactions to finish.`;
  }

  onCheckpointRequested(
    state: CheckpointState,
    activeOrder: readonly TxId[]
  ): CheckpointRequestResult {
    if (state.kind !== "CkptIdle") {
      return {
        nextState: state,
        records: [],
        error: "Cannot start checkpoint: another checkpoint is already in progress."
      };
    }
    if (activeOrder.length === 0) {
      return {
        nextState: { kind: "CkptIdle" },
        records: [{ kind: "LogCheckpoint" }],
        error: ""
      };
    }
    return {
      nextState: { kind: "CkptDrainingQuiescent" },
      records: [],
      error: ""
    };
  }

  onTransactionFinished(
    state: CheckpointState,
    _tx: TxId,
    remainingActiveOrder: readonly TxId[]
  ): CheckpointFinishResult {
    if (state.kind === "CkptDrainingQuiescent") {
      if (remainingActiveOrder.length === 0) {
        return {
          nextState: { kind: "CkptIdle" },
          records: [{ kind: "LogCheckpoint" }]
        };
      }
      return {
        nextState: { kind: "CkptDrainingQuiescent" },
        records: []
      };
    }
    return { nextState: { kind: "CkptIdle" }, records: [] };
  }
}

export class NonQuiescentCheckpointStrategy implements CheckpointStrategy {
  readonly mode = "non-quiescent" as const;
  readonly name = "Non-Quiescent";

  canStartTransaction(): boolean {
    return true;
  }

  blockedStartMessage(): string {
    return "";
  }

  onCheckpointRequested(
    state: CheckpointState,
    activeOrder: readonly TxId[],
    waitsForActiveOnNonQuiescent: boolean
  ): CheckpointRequestResult {
    if (state.kind !== "CkptIdle") {
      return {
        nextState: state,
        records: [],
        error: "Cannot start checkpoint: another checkpoint is already in progress."
      };
    }
    if (!waitsForActiveOnNonQuiescent || activeOrder.length === 0) {
      return {
        nextState: { kind: "CkptIdle" },
        records: [
          { kind: "LogStartCheckpoint", activeTxs: [...activeOrder] },
          { kind: "LogEndCheckpoint" }
        ],
        error: ""
      };
    }
    return {
      nextState: { kind: "CkptActiveNonQuiescent", watchedTxs: [...activeOrder] },
      records: [{ kind: "LogStartCheckpoint", activeTxs: [...activeOrder] }],
      error: ""
    };
  }

  onTransactionFinished(
    state: CheckpointState,
    tx: TxId
  ): CheckpointFinishResult {
    if (state.kind === "CkptActiveNonQuiescent") {
      const remaining = state.watchedTxs.filter((t) => t !== tx);
      if (remaining.length === 0) {
        return {
          nextState: { kind: "CkptIdle" },
          records: [{ kind: "LogEndCheckpoint" }]
        };
      }
      return {
        nextState: { kind: "CkptActiveNonQuiescent", watchedTxs: remaining },
        records: []
      };
    }
    return { nextState: { kind: "CkptIdle" }, records: [] };
  }
}

export function createCheckpointStrategy(mode: CheckpointMode): CheckpointStrategy {
  switch (mode) {
    case "none":
      return new NoCheckpointStrategy();
    case "quiescent":
      return new QuiescentCheckpointStrategy();
    case "non-quiescent":
      return new NonQuiescentCheckpointStrategy();
  }
}
