// TypeScript port of `dafny/scheduler/`:
//   - `Types.dfy` (`LockMode`, `LockTableState`, `PolicyDecision`)
//   - `LockPolicy.dfy` (`SimpleBinaryLockPolicy`, `MultipleLockPolicy`, `TernaryLockPolicy` S/U/X)
//   - `Serializability.dfy` (`IsConflictSerializableTo`)
//   - `PessimisticScheduler.dfy` (`PessimisticScheduler`)
//   - `DependencyGraph.dfy` (`BuildPrecedenceGraph`, cycle detection, all topological serial schedules)
//   - `DeadlockAndOCC.dfy` (Wait-For Graph simulator, Wait-Die, Wound-Wait, and Kung-Robinson OCC)

export type TxId = string;
export type ElementId = string;
export type LockMode = "S" | "U" | "X";
export type LockPolicyKind = "binary" | "multiple" | "ternary";
export type DeadlockPolicyKind = "detect" | "wait-die" | "wound-wait";

export type SchedOp =
  | { kind: "lock"; tx: TxId; element: ElementId; mode: LockMode; raw: string }
  | { kind: "unlock"; tx: TxId; element: ElementId; raw: string }
  | { kind: "read"; tx: TxId; element: ElementId; raw: string }
  | { kind: "write"; tx: TxId; element: ElementId; raw: string }
  | { kind: "commit"; tx: TxId; raw: string }
  | { kind: "abort"; tx: TxId; raw: string };

export interface LockTableState {
  // element -> tx -> mode
  locks: Record<ElementId, Record<TxId, LockMode>>;
  shrinkingTxs: string[];
  finishedTxs: string[];
}

export interface StepTrace {
  stepIndex: number;
  op: SchedOp;
  allowed: boolean;
  reason: string;
  stateAfter: LockTableState;
  waitEdgeAdded?: WaitEdge;
  deadlockAction?: string;
}

export type ConflictKind = "RW" | "WR" | "WW";

export interface ConflictEdge {
  fromTx: TxId;
  toTx: TxId;
  element: ElementId;
  kind: ConflictKind;
  fromStep: number;
  toStep: number;
  fromOpRaw: string;
  toOpRaw: string;
}

export interface PrecedenceGraph {
  nodes: TxId[];
  edges: ConflictEdge[];
  hasCycle: boolean;
  cyclePath: TxId[];
  topologicalOrders: TxId[][];
}

export interface WaitEdge {
  waitingTx: TxId;
  holderTx: TxId;
  element: ElementId;
  requestedMode: LockMode;
  stepIndex: number;
}

export interface DeadlockSimulationResult {
  policyKind: DeadlockPolicyKind;
  txTimestamps: Record<TxId, number>;
  waitEdges: WaitEdge[];
  hasDeadlockCycle: boolean;
  deadlockCycle: TxId[];
  events: {
    stepIndex: number;
    opRaw: string;
    status: "granted" | "waiting" | "aborted-die" | "preempted-wound" | "skipped-inactive";
    detail: string;
  }[];
  abortedTxs: TxId[];
}

export interface OccTxPhaseRecord {
  tx: TxId;
  startStep: number;
  validateStep: number;
  finishStep: number;
  readSet: ElementId[];
  writeSet: ElementId[];
}

export interface OccPairCheck {
  earlierTx: TxId;
  laterTx: TxId;
  passed: boolean;
  ruleMatched: string;
}

export interface OccValidationResult {
  records: OccTxPhaseRecord[];
  pairChecks: OccPairCheck[];
  allValid: boolean;
  abortedTxs: TxId[];
}

// ---------------------------------------------------------------------------
// Lock Policy Implementations (`dafny/scheduler/LockPolicy.dfy`)
// ---------------------------------------------------------------------------

export function supportsMode(policy: LockPolicyKind, mode: LockMode): boolean {
  if (policy === "binary") return mode === "X";
  if (policy === "multiple") return mode === "S" || mode === "X";
  return true;
}

export function isCompatible(
  policy: LockPolicyKind,
  held: LockMode,
  requested: LockMode
): boolean {
  if (policy === "binary") return false;
  if (policy === "multiple") {
    return held === "S" && requested === "S";
  }
  // Ternary S / U / X: asymmetric compatibility!
  // Held S is compatible with S and U; Held U is NOT compatible with S, U, or X!
  if (held === "S" && (requested === "S" || requested === "U")) {
    return true;
  }
  return false;
}

export function canUpgrade(
  policy: LockPolicyKind,
  held: LockMode,
  requested: LockMode
): boolean {
  if (held === requested) return true;
  if (policy === "binary") return false;
  if (policy === "multiple") {
    return held === "S" && requested === "X";
  }
  // Ternary policy: only U -> X upgrade is allowed (direct S -> X is forbidden!)
  return held === "U" && requested === "X";
}

function cloneState(s: LockTableState): LockTableState {
  const locks: Record<ElementId, Record<TxId, LockMode>> = {};
  for (const [el, holders] of Object.entries(s.locks)) {
    locks[el] = { ...holders };
  }
  return {
    locks,
    shrinkingTxs: [...s.shrinkingTxs],
    finishedTxs: [...s.finishedTxs]
  };
}

export function emptyLockTableState(): LockTableState {
  return { locks: {}, shrinkingTxs: [], finishedTxs: [] };
}

export function dispatchLockOp(
  policy: LockPolicyKind,
  state: LockTableState,
  op: SchedOp
): { allowed: boolean; nextState: LockTableState; reason: string; conflictingHolders: TxId[] } {
  const next = cloneState(state);

  if (next.finishedTxs.includes(op.tx)) {
    return {
      allowed: false,
      nextState: next,
      reason: `Transaction ${op.tx} has already committed/aborted.`,
      conflictingHolders: []
    };
  }

  switch (op.kind) {
    case "lock": {
      if (!supportsMode(policy, op.mode)) {
        return {
          allowed: false,
          nextState: next,
          reason: `Policy '${policy}' does not support lock mode ${op.mode} on ${op.element}.`,
          conflictingHolders: []
        };
      }
      if (next.shrinkingTxs.includes(op.tx)) {
        return {
          allowed: false,
          nextState: next,
          reason: `2PL violation: ${op.tx} cannot acquire ${op.mode}(${op.element}) after releasing a lock (shrinking phase).`,
          conflictingHolders: []
        };
      }

      const holders = next.locks[op.element] ?? {};
      const existingMode = holders[op.tx];

      if (existingMode && !canUpgrade(policy, existingMode, op.mode)) {
        return {
          allowed: false,
          nextState: next,
          reason: `Invalid lock upgrade ${existingMode} -> ${op.mode} for ${op.tx} on ${op.element} under '${policy}' policy.`,
          conflictingHolders: []
        };
      }

      const conflicts: TxId[] = [];
      for (const [otherTx, heldMode] of Object.entries(holders)) {
        if (otherTx === op.tx) continue;
        if (!isCompatible(policy, heldMode, op.mode)) {
          conflicts.push(otherTx);
        }
      }

      if (conflicts.length > 0) {
        const conflictDesc = conflicts
          .map((t) => `${t}(${holders[t]})`)
          .join(", ");
        return {
          allowed: false,
          nextState: next,
          reason: `Lock conflict on ${op.element}: ${op.tx} requested ${op.mode}, incompatible with held ${conflictDesc}.`,
          conflictingHolders: conflicts
        };
      }

      if (!next.locks[op.element]) next.locks[op.element] = {};
      next.locks[op.element][op.tx] = op.mode;
      return {
        allowed: true,
        nextState: next,
        reason: existingMode
          ? `${op.tx} upgraded lock on ${op.element} from ${existingMode} to ${op.mode}.`
          : `${op.tx} acquired ${op.mode} lock on ${op.element}.`,
        conflictingHolders: []
      };
    }

    case "unlock": {
      const holders = next.locks[op.element] ?? {};
      if (!holders[op.tx]) {
        return {
          allowed: false,
          nextState: next,
          reason: `Cannot unlock ${op.element}: ${op.tx} does not hold a lock on ${op.element}.`,
          conflictingHolders: []
        };
      }
      delete next.locks[op.element][op.tx];
      if (Object.keys(next.locks[op.element]).length === 0) {
        delete next.locks[op.element];
      }
      if (!next.shrinkingTxs.includes(op.tx)) {
        next.shrinkingTxs.push(op.tx);
      }
      return {
        allowed: true,
        nextState: next,
        reason: `${op.tx} released lock on ${op.element} (entered 2PL shrinking phase).`,
        conflictingHolders: []
      };
    }

    case "read": {
      const held = next.locks[op.element]?.[op.tx];
      if (!held) {
        return {
          allowed: false,
          nextState: next,
          reason: `Read rejected: ${op.tx} must hold a lock (S, U, or X) on ${op.element} before reading.`,
          conflictingHolders: []
        };
      }
      return {
        allowed: true,
        nextState: next,
        reason: `${op.tx} read ${op.element} (holding ${held} lock).`,
        conflictingHolders: []
      };
    }

    case "write": {
      const held = next.locks[op.element]?.[op.tx];
      if (held !== "X") {
        return {
          allowed: false,
          nextState: next,
          reason: `Write rejected: ${op.tx} must hold an Exclusive (X) lock on ${op.element} before writing (currently holds ${held ?? "none"}).`,
          conflictingHolders: []
        };
      }
      return {
        allowed: true,
        nextState: next,
        reason: `${op.tx} wrote ${op.element} (holding X lock).`,
        conflictingHolders: []
      };
    }

    case "commit":
    case "abort": {
      const stillHeld: string[] = [];
      for (const [el, holders] of Object.entries(next.locks)) {
        if (holders[op.tx]) {
          stillHeld.push(`${el}(${holders[op.tx]})`);
        }
      }
      if (stillHeld.length > 0) {
        return {
          allowed: false,
          nextState: next,
          reason: `${op.tx} cannot ${op.kind} while still holding locks: ${stillHeld.join(", ")}.`,
          conflictingHolders: []
        };
      }
      if (!next.finishedTxs.includes(op.tx)) {
        next.finishedTxs.push(op.tx);
      }
      return {
        allowed: true,
        nextState: next,
        reason: `${op.tx} ${op.kind === "commit" ? "committed" : "aborted"} cleanly.`,
        conflictingHolders: []
      };
    }
  }
}

export function runPessimisticScheduler(
  policy: LockPolicyKind,
  ops: SchedOp[]
): {
  isValid: boolean;
  traces: StepTrace[];
  finalState: LockTableState;
  errors: string[];
} {
  let state = emptyLockTableState();
  const traces: StepTrace[] = [];
  const errors: string[] = [];

  ops.forEach((op, idx) => {
    const res = dispatchLockOp(policy, state, op);
    state = res.nextState;
    if (!res.allowed) {
      errors.push(`Step ${idx + 1} (${op.raw}): ${res.reason}`);
    }
    traces.push({
      stepIndex: idx,
      op,
      allowed: res.allowed,
      reason: res.reason,
      stateAfter: cloneState(state)
    });
  });

  return {
    isValid: errors.length === 0,
    traces,
    finalState: state,
    errors
  };
}

// ---------------------------------------------------------------------------
// Precedence / Dependency Graph & Conflict Serializability
// ---------------------------------------------------------------------------

export function buildPrecedenceGraph(ops: SchedOp[]): PrecedenceGraph {
  const nodes: TxId[] = [];
  for (const op of ops) {
    if (!nodes.includes(op.tx)) {
      nodes.push(op.tx);
    }
  }

  const dataOps = ops
    .map((op, idx) => ({ op, idx }))
    .filter((item) => item.op.kind === "read" || item.op.kind === "write");

  const edges: ConflictEdge[] = [];
  for (let i = 0; i < dataOps.length; i++) {
    for (let j = i + 1; j < dataOps.length; j++) {
      const a = dataOps[i].op;
      const b = dataOps[j].op;
      if (a.kind !== "read" && a.kind !== "write") continue;
      if (b.kind !== "read" && b.kind !== "write") continue;
      if (a.tx === b.tx || a.element !== b.element) continue;
      if (a.kind === "read" && b.kind === "read") continue;

      const kind: ConflictKind =
        a.kind === "read" && b.kind === "write"
          ? "RW"
          : a.kind === "write" && b.kind === "read"
            ? "WR"
            : "WW";

      edges.push({
        fromTx: a.tx,
        toTx: b.tx,
        element: a.element,
        kind,
        fromStep: dataOps[i].idx + 1,
        toStep: dataOps[j].idx + 1,
        fromOpRaw: a.raw,
        toOpRaw: b.raw
      });
    }
  }

  const { hasCycle, cyclePath } = findDirectedCycle(
    nodes,
    edges.map((e) => [e.fromTx, e.toTx])
  );
  const topologicalOrders = hasCycle
    ? []
    : findAllTopologicalOrders(
        nodes,
        edges.map((e) => [e.fromTx, e.toTx])
      );

  return {
    nodes,
    edges,
    hasCycle,
    cyclePath,
    topologicalOrders
  };
}

function findDirectedCycle(
  nodes: TxId[],
  pairs: [TxId, TxId][]
): { hasCycle: boolean; cyclePath: TxId[] } {
  const adj = new Map<TxId, TxId[]>();
  for (const n of nodes) adj.set(n, []);
  for (const [u, v] of pairs) {
    const list = adj.get(u) ?? [];
    if (!list.includes(v)) list.push(v);
    adj.set(u, list);
  }

  const state = new Map<TxId, 0 | 1 | 2>();
  const stack: TxId[] = [];

  for (const start of nodes) {
    if ((state.get(start) ?? 0) !== 0) continue;

    const dfs = (u: TxId): TxId[] | null => {
      state.set(u, 1);
      stack.push(u);
      for (const v of adj.get(u) ?? []) {
        const st = state.get(v) ?? 0;
        if (st === 1) {
          const idx = stack.indexOf(v);
          return [...stack.slice(idx), v];
        }
        if (st === 0) {
          const found = dfs(v);
          if (found) return found;
        }
      }
      stack.pop();
      state.set(u, 2);
      return null;
    };

    const cyc = dfs(start);
    if (cyc) return { hasCycle: true, cyclePath: cyc };
  }

  return { hasCycle: false, cyclePath: [] };
}

function findAllTopologicalOrders(
  nodes: TxId[],
  pairs: [TxId, TxId][]
): TxId[][] {
  if (nodes.length === 0) return [];
  const results: TxId[][] = [];
  const used = new Set<TxId>();

  const backtrack = (current: TxId[]) => {
    if (results.length >= 12) return;
    if (current.length === nodes.length) {
      results.push([...current]);
      return;
    }
    for (const candidate of nodes) {
      if (used.has(candidate)) continue;
      // Candidate can be placed next iff all its prerequisites are already in `used`
      const blocked = pairs.some(
        ([u, v]) => v === candidate && !used.has(u)
      );
      if (!blocked) {
        used.add(candidate);
        current.push(candidate);
        backtrack(current);
        current.pop();
        used.delete(candidate);
      }
    }
  };

  backtrack([]);
  return results;
}

// ---------------------------------------------------------------------------
// Wait-For Graph & Deadlock Prevention (Wait-Die / Wound-Wait) Simulator
// ---------------------------------------------------------------------------

export function simulateDeadlockAndWaitFor(
  lockPolicy: LockPolicyKind,
  deadlockPolicy: DeadlockPolicyKind,
  ops: SchedOp[]
): DeadlockSimulationResult {
  const txTimestamps: Record<TxId, number> = {};
  let nextTs = 10;
  for (const op of ops) {
    if (!txTimestamps[op.tx]) {
      txTimestamps[op.tx] = nextTs;
      nextTs += 10;
    }
  }

  let state = emptyLockTableState();
  const waitEdges: WaitEdge[] = [];
  const abortedTxs: TxId[] = [];
  const waitingTxs = new Set<TxId>();
  const events: DeadlockSimulationResult["events"] = [];

  const releaseAllLocksOf = (tx: TxId) => {
    for (const el of Object.keys(state.locks)) {
      delete state.locks[el][tx];
      if (Object.keys(state.locks[el]).length === 0) {
        delete state.locks[el];
      }
    }
    for (let i = waitEdges.length - 1; i >= 0; i--) {
      if (waitEdges[i].waitingTx === tx || waitEdges[i].holderTx === tx) {
        waitingTxs.delete(waitEdges[i].waitingTx);
        waitEdges.splice(i, 1);
      }
    }
  };

  ops.forEach((op, idx) => {
    if (abortedTxs.includes(op.tx)) {
      events.push({
        stepIndex: idx + 1,
        opRaw: op.raw,
        status: "skipped-inactive",
        detail: `Skipped: ${op.tx} was already aborted.`
      });
      return;
    }

    if (waitingTxs.has(op.tx) && op.kind !== "abort") {
      events.push({
        stepIndex: idx + 1,
        opRaw: op.raw,
        status: "skipped-inactive",
        detail: `Blocked: ${op.tx} is currently waiting for a lock.`
      });
      return;
    }

    const res = dispatchLockOp(lockPolicy, state, op);
    if (res.allowed) {
      state = res.nextState;
      if (op.kind === "unlock" || op.kind === "commit" || op.kind === "abort") {
        for (let i = waitEdges.length - 1; i >= 0; i--) {
          if (waitEdges[i].holderTx === op.tx) {
            waitingTxs.delete(waitEdges[i].waitingTx);
            waitEdges.splice(i, 1);
          }
        }
      }
      events.push({
        stepIndex: idx + 1,
        opRaw: op.raw,
        status: "granted",
        detail: res.reason
      });
      return;
    }

    // If this was a lock conflict, apply Wait-For / Wait-Die / Wound-Wait
    if (op.kind === "lock" && res.conflictingHolders.length > 0) {
      const reqTs = txTimestamps[op.tx];

      if (deadlockPolicy === "detect") {
        for (const h of res.conflictingHolders) {
          waitEdges.push({
            waitingTx: op.tx,
            holderTx: h,
            element: op.element,
            requestedMode: op.mode,
            stepIndex: idx + 1
          });
        }
        waitingTxs.add(op.tx);
        events.push({
          stepIndex: idx + 1,
          opRaw: op.raw,
          status: "waiting",
          detail: `${op.tx} (TS=${reqTs}) waits for ${res.conflictingHolders.join(", ")} on ${op.element}.`
        });
      } else if (deadlockPolicy === "wait-die") {
        // Older waits; younger dies
        const youngerThanSomeHolder = res.conflictingHolders.some(
          (h) => reqTs > txTimestamps[h]
        );
        if (youngerThanSomeHolder) {
          abortedTxs.push(op.tx);
          releaseAllLocksOf(op.tx);
          events.push({
            stepIndex: idx + 1,
            opRaw: op.raw,
            status: "aborted-die",
            detail: `Wait-Die: younger ${op.tx} (TS=${reqTs}) DIES (aborts) instead of waiting for older holder.`
          });
        } else {
          for (const h of res.conflictingHolders) {
            waitEdges.push({
              waitingTx: op.tx,
              holderTx: h,
              element: op.element,
              requestedMode: op.mode,
              stepIndex: idx + 1
            });
          }
          waitingTxs.add(op.tx);
          events.push({
            stepIndex: idx + 1,
            opRaw: op.raw,
            status: "waiting",
            detail: `Wait-Die: older ${op.tx} (TS=${reqTs}) is allowed to WAIT for younger ${res.conflictingHolders.join(", ")}.`
          });
        }
      } else {
        // Wound-Wait: Older wounds (preempts) younger holder; younger waits for older holder
        const youngerHolders = res.conflictingHolders.filter(
          (h) => reqTs < txTimestamps[h]
        );
        const olderHolders = res.conflictingHolders.filter(
          (h) => reqTs > txTimestamps[h]
        );

        for (const yh of youngerHolders) {
          if (!abortedTxs.includes(yh)) {
            abortedTxs.push(yh);
          }
          releaseAllLocksOf(yh);
        }

        if (olderHolders.length === 0) {
          // All conflicting holders were younger and wounded -> grant lock now!
          const retry = dispatchLockOp(lockPolicy, state, op);
          state = retry.nextState;
          events.push({
            stepIndex: idx + 1,
            opRaw: op.raw,
            status: "preempted-wound",
            detail: `Wound-Wait: older ${op.tx} (TS=${reqTs}) WOUNDED (aborted) younger ${youngerHolders.join(", ")} and acquired ${op.mode}(${op.element}).`
          });
        } else {
          for (const oh of olderHolders) {
            waitEdges.push({
              waitingTx: op.tx,
              holderTx: oh,
              element: op.element,
              requestedMode: op.mode,
              stepIndex: idx + 1
            });
          }
          waitingTxs.add(op.tx);
          events.push({
            stepIndex: idx + 1,
            opRaw: op.raw,
            status: "waiting",
            detail: `Wound-Wait: younger ${op.tx} (TS=${reqTs}) WAITS for older ${olderHolders.join(", ")}.`
          });
        }
      }
      return;
    }

    events.push({
      stepIndex: idx + 1,
      opRaw: op.raw,
      status: "skipped-inactive",
      detail: res.reason
    });
  });

  const allTxs = Object.keys(txTimestamps);
  const { hasCycle, cyclePath } = findDirectedCycle(
    allTxs,
    waitEdges.map((e) => [e.waitingTx, e.holderTx])
  );

  return {
    policyKind: deadlockPolicy,
    txTimestamps,
    waitEdges,
    hasDeadlockCycle: hasCycle,
    deadlockCycle: cyclePath,
    events,
    abortedTxs
  };
}

// ---------------------------------------------------------------------------
// Kung-Robinson Optimistic Concurrency Control (OCC) Analyzer
// ---------------------------------------------------------------------------

export function validateOccFromSchedule(ops: SchedOp[]): OccValidationResult {
  const txMap = new Map<
    TxId,
    {
      startStep: number;
      lastOpStep: number;
      commitStep?: number;
      readSet: Set<ElementId>;
      writeSet: Set<ElementId>;
    }
  >();

  ops.forEach((op, idx) => {
    const step = idx + 1;
    let entry = txMap.get(op.tx);
    if (!entry) {
      entry = {
        startStep: step,
        lastOpStep: step,
        readSet: new Set(),
        writeSet: new Set()
      };
      txMap.set(op.tx, entry);
    }
    entry.lastOpStep = step;
    if (op.kind === "read") entry.readSet.add(op.element);
    if (op.kind === "write") entry.writeSet.add(op.element);
    if (op.kind === "commit") entry.commitStep = step;
  });

  const records: OccTxPhaseRecord[] = [];
  let syntheticValidateOffset = ops.length + 1;
  for (const [tx, info] of txMap.entries()) {
    const validateStep = info.commitStep ?? syntheticValidateOffset++;
    const finishStep = validateStep + (info.writeSet.size > 0 ? 1 : 0);
    records.push({
      tx,
      startStep: info.startStep,
      validateStep,
      finishStep,
      readSet: [...info.readSet],
      writeSet: [...info.writeSet]
    });
  }

  records.sort((a, b) => a.validateStep - b.validateStep);

  const pairChecks: OccPairCheck[] = [];
  const abortedTxs: TxId[] = [];

  for (let j = 0; j < records.length; j++) {
    const tj = records[j];
    let tjValid = true;

    for (let i = 0; i < j; i++) {
      const ti = records[i];
      if (ti.validateStep >= tj.validateStep) continue;

      const writeReadOverlap = ti.writeSet.filter((x) => tj.readSet.includes(x));
      const writeWriteOverlap = ti.writeSet.filter((x) => tj.writeSet.includes(x));

      if (ti.finishStep < tj.startStep) {
        pairChecks.push({
          earlierTx: ti.tx,
          laterTx: tj.tx,
          passed: true,
          ruleMatched: `Rule 1 OK: Finish(${ti.tx})=${ti.finishStep} < Start(${tj.tx})=${tj.startStep}`
        });
      } else if (ti.finishStep < tj.validateStep && writeReadOverlap.length === 0) {
        pairChecks.push({
          earlierTx: ti.tx,
          laterTx: tj.tx,
          passed: true,
          ruleMatched: `Rule 2 OK: WS(${ti.tx}) ∩ RS(${tj.tx}) = ∅ before Validate(${tj.tx})`
        });
      } else if (writeReadOverlap.length === 0 && writeWriteOverlap.length === 0) {
        pairChecks.push({
          earlierTx: ti.tx,
          laterTx: tj.tx,
          passed: true,
          ruleMatched: `Rule 3 OK: WS(${ti.tx}) disjoint from RS(${tj.tx}) and WS(${tj.tx})`
        });
      } else {
        tjValid = false;
        const overlapDesc =
          writeReadOverlap.length > 0
            ? `WS(${ti.tx}) ∩ RS(${tj.tx}) = {${writeReadOverlap.join(", ")}}`
            : `WS(${ti.tx}) ∩ WS(${tj.tx}) = {${writeWriteOverlap.join(", ")}}`;
        pairChecks.push({
          earlierTx: ti.tx,
          laterTx: tj.tx,
          passed: false,
          ruleMatched: `Validation FAILED: ${ti.tx} overlapped ${tj.tx} and ${overlapDesc}`
        });
      }
    }

    if (!tjValid && !abortedTxs.includes(tj.tx)) {
      abortedTxs.push(tj.tx);
    }
  }

  return {
    records,
    pairChecks,
    allValid: abortedTxs.length === 0,
    abortedTxs
  };
}

// ---------------------------------------------------------------------------
// Schedule Text Parser & Preset Schedules
// ---------------------------------------------------------------------------

export function parseScheduleText(text: string): {
  ops: SchedOp[];
  parseErrors: string[];
} {
  const tokens = text
    .split(/[\n;]+/)
    .map((s) => s.trim())
    .filter((s) => s.length > 0 && !s.startsWith("//") && !s.startsWith("#"));

  const ops: SchedOp[] = [];
  const parseErrors: string[] = [];

  for (const tok of tokens) {
    // Match SL(T1, A), XL(T1, A), UL(T1, A), L(T1, A), U(T1, A), R(T1, A), W(T1, A), C(T1), A(T1)
    // Also supports shorthand R1(A), W2(B), SL1(A), XL2(A), U1(A), C1
    const fnMatch = tok.match(
      /^(SL|XL|UL|L|U|UNLOCK|R|READ|W|WRITE|C|COMMIT|A|ABORT)\s*\(\s*([A-Za-z0-9_]+)(?:\s*,\s*([A-Za-z0-9_]+))?\s*\)$/i
    );
    if (fnMatch) {
      const verb = fnMatch[1].toUpperCase();
      const tx = fnMatch[2];
      const elem = fnMatch[3];

      if ((verb === "C" || verb === "COMMIT") && !elem) {
        ops.push({ kind: "commit", tx, raw: `C(${tx})` });
        continue;
      }
      if ((verb === "A" || verb === "ABORT") && !elem) {
        ops.push({ kind: "abort", tx, raw: `A(${tx})` });
        continue;
      }
      if (!elem) {
        parseErrors.push(`Missing element argument in '${tok}'.`);
        continue;
      }
      if (verb === "SL") {
        ops.push({ kind: "lock", tx, element: elem, mode: "S", raw: `SL(${tx}, ${elem})` });
      } else if (verb === "UL") {
        ops.push({ kind: "lock", tx, element: elem, mode: "U", raw: `UL(${tx}, ${elem})` });
      } else if (verb === "XL" || verb === "L") {
        ops.push({ kind: "lock", tx, element: elem, mode: "X", raw: `${verb}(${tx}, ${elem})` });
      } else if (verb === "U" || verb === "UNLOCK") {
        ops.push({ kind: "unlock", tx, element: elem, raw: `U(${tx}, ${elem})` });
      } else if (verb === "R" || verb === "READ") {
        ops.push({ kind: "read", tx, element: elem, raw: `R(${tx}, ${elem})` });
      } else if (verb === "W" || verb === "WRITE") {
        ops.push({ kind: "write", tx, element: elem, raw: `W(${tx}, ${elem})` });
      }
      continue;
    }

    const shortMatch = tok.match(
      /^(SL|XL|UL|L|U|R|W|C|A)([0-9]+)(?:\s*\(\s*([A-Za-z0-9_]+)\s*\))?$/i
    );
    if (shortMatch) {
      const verb = shortMatch[1].toUpperCase();
      const tx = `T${shortMatch[2]}`;
      const elem = shortMatch[3];
      if (verb === "C") {
        ops.push({ kind: "commit", tx, raw: `C(${tx})` });
        continue;
      }
      if (verb === "A") {
        ops.push({ kind: "abort", tx, raw: `A(${tx})` });
        continue;
      }
      if (!elem) {
        parseErrors.push(`Missing element in '${tok}'.`);
        continue;
      }
      if (verb === "SL") ops.push({ kind: "lock", tx, element: elem, mode: "S", raw: `SL(${tx}, ${elem})` });
      else if (verb === "UL") ops.push({ kind: "lock", tx, element: elem, mode: "U", raw: `UL(${tx}, ${elem})` });
      else if (verb === "XL" || verb === "L") ops.push({ kind: "lock", tx, element: elem, mode: "X", raw: `XL(${tx}, ${elem})` });
      else if (verb === "U") ops.push({ kind: "unlock", tx, element: elem, raw: `U(${tx}, ${elem})` });
      else if (verb === "R") ops.push({ kind: "read", tx, element: elem, raw: `R(${tx}, ${elem})` });
      else if (verb === "W") ops.push({ kind: "write", tx, element: elem, raw: `W(${tx}, ${elem})` });
      continue;
    }

    parseErrors.push(`Unrecognized operation '${tok}'. Use e.g. SL(T1, A), R(T1, A), XL(T1, A), W(T1, A), U(T1, A), C(T1).`);
  }

  return { ops, parseErrors };
}

export interface SchedulerPreset {
  id: string;
  title: string;
  policy: LockPolicyKind;
  description: string;
  scheduleText: string;
}

export const SCHEDULER_PRESETS: SchedulerPreset[] = [
  {
    id: "valid-2pl-upgrade",
    title: "1. Valid S/X 2PL + Upgrade (Serializable to T2 → T1)",
    policy: "multiple",
    description:
      "Mirrors Demo 1 in dafny/scheduler/Main.dfy: T1 and T2 share S(A), T2 unlocks A, T1 upgrades S->X on A, writes, unlocks, and commits.",
    scheduleText: [
      "SL(T1, A)",
      "R(T1, A)",
      "SL(T2, A)",
      "R(T2, A)",
      "U(T2, A)",
      "XL(T1, A)",
      "W(T1, A)",
      "U(T1, A)",
      "C(T1)",
      "C(T2)"
    ].join("\n")
  },
  {
    id: "ternary-u-upgrade",
    title: "2. Ternary (S/U/X) Asymmetric Update Lock (T1 → T2)",
    policy: "ternary",
    description:
      "Mirrors Demo 4 in dafny/scheduler/Main.dfy: T1 holds S(A), T2 acquires U(A) (compatible with S!), T1 releases S(A), and T2 upgrades U -> X.",
    scheduleText: [
      "SL(T1, A)",
      "R(T1, A)",
      "UL(T2, A)",
      "R(T2, A)",
      "U(T1, A)",
      "XL(T2, A)",
      "W(T2, A)",
      "U(T2, A)",
      "C(T1)",
      "C(T2)"
    ].join("\n")
  },
  {
    id: "deadlock-2cycle",
    title: "3. Classic 2-Cycle Deadlock (T1 ↔ T2 on A & B)",
    policy: "multiple",
    description:
      "T1 locks A and T2 locks B; then T1 requests X(B) (waits for T2) and T2 requests X(A) (waits for T1), creating a Wait-For cycle resolved by Wait-Die / Wound-Wait.",
    scheduleText: [
      "XL(T1, A)",
      "R(T1, A)",
      "XL(T2, B)",
      "R(T2, B)",
      "XL(T1, B)",
      "XL(T2, A)",
      "W(T1, B)",
      "W(T2, A)"
    ].join("\n")
  },
  {
    id: "cyclic-non-serializable",
    title: "4. Non-Serializable Conflict Cycle (T1 → T2 → T1)",
    policy: "multiple",
    description:
      "Mirrors Demo 3 in dafny/scheduler/Main.dfy: R(T1,A)->W(T2,A) forces T1->T2 on A, while R(T2,B)->W(T1,B) forces T2->T1 on B (cycle in Precedence Graph & OCC abort!).",
    scheduleText: [
      "SL(T1, A)",
      "R(T1, A)",
      "U(T1, A)",
      "XL(T2, A)",
      "W(T2, A)",
      "SL(T2, B)",
      "R(T2, B)",
      "U(T2, A)",
      "U(T2, B)",
      "XL(T1, B)",
      "W(T1, B)",
      "U(T1, B)",
      "C(T2)",
      "C(T1)"
    ].join("\n")
  }
];
