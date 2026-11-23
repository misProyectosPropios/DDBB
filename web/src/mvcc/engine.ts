// TypeScript port of `dafny/mvcc/`:
//   - `Types.dfy` (`IsolationLevel`, `TxStatus`, `TupleVersion`, `TxMeta`, `MvccState`, `MvccOp`, `MvccStepResult`)
//   - `IsolationPolicy.dfy` (`IsVersionVisible`, `FindLatestVisibleVersion`, `WriteAllowed`, `CheckWriteAllowed`, `CommitAllowed`, `CheckCommitAllowed`)
//   - `MvccSimulator.dfy` (`StepBegin`, `StepRead`, `StepFetchCursor`, `StepCloseCursor`, `StepWrite`, `StepCommit`, `StepAbort`, `SimulateSchedule`)

export type TxId = string;
export type ElementId = string;
export type Value = number;
export type Timestamp = number;

export type IsolationLevel =
  | "ReadCommitted"
  | "CursorStability"
  | "RepeatableRead"
  | "SnapshotIsolation"
  | "SerializableMVCC";

export type TxStatus = "TxActive" | "TxCommitted" | "TxAborted";

export interface TupleVersion {
  versionId: number;
  element: ElementId;
  value: Value;
  creatorTx: TxId;
  xmin: Timestamp;
  committed: boolean;
}

export interface TxMeta {
  tx: TxId;
  level: IsolationLevel;
  status: TxStatus;
  startTs: Timestamp;
  commitTs: Timestamp;
  cursorElem: ElementId | null;
  readSet: ElementId[];
  writeSet: ElementId[];
}

export interface MvccState {
  clock: Timestamp;
  versions: TupleVersion[];
  txs: Record<TxId, TxMeta>;
  writeOwners: Record<ElementId, TxId>;
  rrReadLocks: Record<ElementId, TxId[]>;
  csCursorPins: Record<ElementId, TxId[]>;
}

export type MvccOp =
  | { kind: "BeginOp"; tx: TxId; level: IsolationLevel; raw: string }
  | { kind: "ReadOp"; tx: TxId; element: ElementId; raw: string }
  | { kind: "FetchCursorOp"; tx: TxId; element: ElementId; raw: string }
  | { kind: "CloseCursorOp"; tx: TxId; raw: string }
  | { kind: "WriteOp"; tx: TxId; element: ElementId; newValue: Value; raw: string }
  | { kind: "CommitOp"; tx: TxId; raw: string }
  | { kind: "AbortOp"; tx: TxId; raw: string };

export interface MvccStepResult {
  stepIndex: number;
  op: MvccOp;
  allowed: boolean;
  nextState: MvccState;
  readValue: Value | null;
  readVersion: TupleVersion | null;
  reason: string;
}

export interface MvccSimulationSnapshot {
  stepIndex: number;
  label: string;
  op: MvccOp | null;
  result: MvccStepResult | null;
  state: MvccState;
}

export const ISOLATION_LEVELS: {
  id: IsolationLevel;
  shortLabel: string;
  fullLabel: string;
  summary: string;
}[] = [
  {
    id: "ReadCommitted",
    shortLabel: "RC",
    fullLabel: "Read Committed (RC)",
    summary:
      "Reads latest committed version; blocks reads on another transaction's uncommitted write lock; releases read locks immediately."
  },
  {
    id: "CursorStability",
    shortLabel: "CS",
    fullLabel: "Cursor Stability (CS)",
    summary:
      "Read Committed + pins the currently fetched cursor row so no concurrent writer can modify it until the cursor advances or closes."
  },
  {
    id: "RepeatableRead",
    shortLabel: "RR",
    fullLabel: "Repeatable Read (RR)",
    summary:
      "Holds persistent read locks on all read items until commit/abort, preventing Non-Repeatable Reads and Lost Updates."
  },
  {
    id: "SnapshotIsolation",
    shortLabel: "SI",
    fullLabel: "Snapshot Isolation (SI)",
    summary:
      "Non-blocking reads from a consistent point-in-time snapshot (xmin ≤ startTs); enforces First-Committer-Wins on write conflicts."
  },
  {
    id: "SerializableMVCC",
    shortLabel: "Serializable (SSI)",
    fullLabel: "Serializable MVCC (SSI)",
    summary:
      "Snapshot Isolation + commit-time read-set validation (rejects rw-antidependency / Write Skew cycles when readSet was modified after startTs)."
  }
];

export function formatIsolationLevel(level: IsolationLevel): string {
  switch (level) {
    case "ReadCommitted":
      return "RC (Read Committed)";
    case "CursorStability":
      return "CS (Cursor Stability)";
    case "RepeatableRead":
      return "RR (Repeatable Read)";
    case "SnapshotIsolation":
      return "SI (Snapshot Isolation)";
    case "SerializableMVCC":
      return "Serializable (SSI)";
  }
}

export function formatShortLevel(level: IsolationLevel): string {
  switch (level) {
    case "ReadCommitted":
      return "RC";
    case "CursorStability":
      return "CS";
    case "RepeatableRead":
      return "RR";
    case "SnapshotIsolation":
      return "SI";
    case "SerializableMVCC":
      return "SSI";
  }
}

export function parseIsolationLevelToken(token: string, fallback: IsolationLevel = "SnapshotIsolation"): IsolationLevel {
  const norm = token.trim().toUpperCase().replace(/[\s_-]+/g, "");
  if (norm === "RC" || norm === "READCOMMITTED") return "ReadCommitted";
  if (norm === "CS" || norm === "CURSORSTABILITY") return "CursorStability";
  if (norm === "RR" || norm === "REPEATABLEREAD") return "RepeatableRead";
  if (norm === "SI" || norm === "SNAPSHOT" || norm === "SNAPSHOTISOLATION") return "SnapshotIsolation";
  if (norm === "SSI" || norm === "SER" || norm === "SERIALIZABLE" || norm === "SERIALIZABLEMVCC") {
    return "SerializableMVCC";
  }
  return fallback;
}

function cloneState(s: MvccState): MvccState {
  const txs: Record<TxId, TxMeta> = {};
  for (const [k, v] of Object.entries(s.txs)) {
    txs[k] = {
      ...v,
      readSet: [...v.readSet],
      writeSet: [...v.writeSet]
    };
  }
  const rrReadLocks: Record<ElementId, TxId[]> = {};
  for (const [k, v] of Object.entries(s.rrReadLocks)) {
    rrReadLocks[k] = [...v];
  }
  const csCursorPins: Record<ElementId, TxId[]> = {};
  for (const [k, v] of Object.entries(s.csCursorPins)) {
    csCursorPins[k] = [...v];
  }
  return {
    clock: s.clock,
    versions: s.versions.map((ver) => ({ ...ver })),
    txs,
    writeOwners: { ...s.writeOwners },
    rrReadLocks,
    csCursorPins
  };
}

export function initMvccState(items: { name: ElementId; value: Value }[]): MvccState {
  return {
    clock: 1,
    versions: items.map((item, idx) => ({
      versionId: idx + 1,
      element: item.name,
      value: item.value,
      creatorTx: "INIT",
      xmin: 0,
      committed: true
    })),
    txs: {},
    writeOwners: {},
    rrReadLocks: {},
    csCursorPins: {}
  };
}

// ---------------------------------------------------------------------------
// State Inspection Helpers (`dafny/mvcc/Types.dfy`)
// ---------------------------------------------------------------------------

export function rrLockHolders(state: MvccState, elem: ElementId): TxId[] {
  return state.rrReadLocks[elem] ? [...state.rrReadLocks[elem]] : [];
}

export function csPinHolders(state: MvccState, elem: ElementId): TxId[] {
  return state.csCursorPins[elem] ? [...state.csCursorPins[elem]] : [];
}

export function hasOtherRRLock(state: MvccState, elem: ElementId, tx: TxId): boolean {
  return rrLockHolders(state, elem).some((holder) => holder !== tx);
}

export function hasOtherCSPin(state: MvccState, elem: ElementId, tx: TxId): boolean {
  return csPinHolders(state, elem).some((holder) => holder !== tx);
}

export function hasOtherWriteOwner(state: MvccState, elem: ElementId, tx: TxId): boolean {
  return elem in state.writeOwners && state.writeOwners[elem] !== tx;
}

export function hasCommittedVersionAfter(
  versions: TupleVersion[],
  elem: ElementId,
  tx: TxId,
  sinceTs: Timestamp
): boolean {
  return versions.some(
    (v) => v.element === elem && v.committed && v.creatorTx !== tx && v.xmin > sinceTs
  );
}

export function setHasCommittedVersionAfter(
  versions: TupleVersion[],
  elemSet: ElementId[],
  tx: TxId,
  sinceTs: Timestamp
): boolean {
  return versions.some(
    (v) => elemSet.includes(v.element) && v.committed && v.creatorTx !== tx && v.xmin > sinceTs
  );
}

// ---------------------------------------------------------------------------
// Isolation Policy Rules (`dafny/mvcc/IsolationPolicy.dfy`)
// ---------------------------------------------------------------------------

export function isVersionVisible(meta: TxMeta, v: TupleVersion): boolean {
  if (v.creatorTx === meta.tx) return true;
  if (!v.committed) return false;
  switch (meta.level) {
    case "ReadCommitted":
    case "CursorStability":
    case "RepeatableRead":
      return true;
    case "SnapshotIsolation":
    case "SerializableMVCC":
      return v.xmin <= meta.startTs;
  }
}

export function findLatestVisibleVersion(
  versions: TupleVersion[],
  meta: TxMeta,
  elem: ElementId
): TupleVersion | null {
  // Pass 1: transaction's own uncommitted write on `elem`
  for (let idx = versions.length - 1; idx >= 0; idx--) {
    const v = versions[idx];
    if (v.element === elem && v.creatorTx === meta.tx && !v.committed) {
      return v;
    }
  }
  // Pass 2: visible committed version with highest `xmin`
  let found: TupleVersion | null = null;
  for (const v of versions) {
    if (v.element === elem && isVersionVisible(meta, v)) {
      if (found === null || v.xmin >= found.xmin) {
        found = v;
      }
    }
  }
  return found;
}

export function checkWriteAllowed(
  state: MvccState,
  meta: TxMeta,
  elem: ElementId
): { ok: boolean; reason: string } {
  if (hasOtherWriteOwner(state, elem, meta.tx)) {
    const owner = state.writeOwners[elem];
    return {
      ok: false,
      reason: `Write blocked (Dirty Write prevention): ${owner} holds an uncommitted write lock on ${elem}.`
    };
  }
  if (hasOtherCSPin(state, elem, meta.tx)) {
    const holders = csPinHolders(state, elem).filter((t) => t !== meta.tx);
    return {
      ok: false,
      reason: `Write blocked by Cursor Stability (CS): ${holders.join(", ")} has an active cursor pin on ${elem}.`
    };
  }
  if (hasOtherRRLock(state, elem, meta.tx)) {
    const holders = rrLockHolders(state, elem).filter((t) => t !== meta.tx);
    return {
      ok: false,
      reason: `Write blocked by Repeatable Read (RR): ${holders.join(", ")} holds an RR read lock on ${elem}.`
    };
  }
  if (
    (meta.level === "SnapshotIsolation" || meta.level === "SerializableMVCC") &&
    hasCommittedVersionAfter(state.versions, elem, meta.tx, meta.startTs)
  ) {
    return {
      ok: false,
      reason: `First-Committer-Wins violation (${formatShortLevel(meta.level)}): another transaction committed ${elem} after ${meta.tx}.startTs=${meta.startTs}.`
    };
  }
  return { ok: true, reason: `Write permitted on ${elem}.` };
}

export function checkCommitAllowed(
  state: MvccState,
  meta: TxMeta
): { ok: boolean; reason: string } {
  switch (meta.level) {
    case "ReadCommitted":
      return { ok: true, reason: `Read Committed commit OK at ts=${state.clock}.` };
    case "CursorStability":
      return { ok: true, reason: `Cursor Stability commit OK at ts=${state.clock}.` };
    case "RepeatableRead":
      return { ok: true, reason: `Repeatable Read commit OK at ts=${state.clock} (releases RR read locks).` };
    case "SnapshotIsolation":
      if (setHasCommittedVersionAfter(state.versions, meta.writeSet, meta.tx, meta.startTs)) {
        return {
          ok: false,
          reason: `Snapshot Isolation abort (First-Committer-Wins): concurrent committed write on writeSet {${meta.writeSet.join(", ")}} after startTs=${meta.startTs}.`
        };
      }
      return { ok: true, reason: `Snapshot Isolation commit OK at ts=${state.clock}.` };
    case "SerializableMVCC":
      if (setHasCommittedVersionAfter(state.versions, meta.writeSet, meta.tx, meta.startTs)) {
        return {
          ok: false,
          reason: `Serializable abort (First-Committer-Wins): concurrent committed write on writeSet {${meta.writeSet.join(", ")}} after startTs=${meta.startTs}.`
        };
      }
      if (
        meta.writeSet.length > 0 &&
        setHasCommittedVersionAfter(state.versions, meta.readSet, meta.tx, meta.startTs)
      ) {
        return {
          ok: false,
          reason: `Serializable abort (Write Skew / rw-antidependency prevented!): readSet {${meta.readSet.join(", ")}} was modified by a concurrent committed tx after ${meta.tx}.startTs=${meta.startTs}.`
        };
      }
      return { ok: true, reason: `Serializable MVCC commit OK at ts=${state.clock}.` };
  }
}

// ---------------------------------------------------------------------------
// Step Execution (`dafny/mvcc/MvccSimulator.dfy`)
// ---------------------------------------------------------------------------

function addUnique<T>(arr: T[], item: T): T[] {
  return arr.includes(item) ? [...arr] : [...arr, item];
}

function setCSPin(
  state: MvccState,
  oldElem: ElementId | null,
  newElem: ElementId | null,
  tx: TxId
): void {
  if (oldElem !== null && state.csCursorPins[oldElem]) {
    state.csCursorPins[oldElem] = state.csCursorPins[oldElem].filter((t) => t !== tx);
    if (state.csCursorPins[oldElem].length === 0) {
      delete state.csCursorPins[oldElem];
    }
  }
  if (newElem !== null) {
    state.csCursorPins[newElem] = addUnique(state.csCursorPins[newElem] ?? [], tx);
  }
}

function releaseTxLocksAndPins(state: MvccState, tx: TxId): void {
  for (const [el, owner] of Object.entries(state.writeOwners)) {
    if (owner === tx) {
      delete state.writeOwners[el];
    }
  }
  for (const el of Object.keys(state.rrReadLocks)) {
    state.rrReadLocks[el] = state.rrReadLocks[el].filter((t) => t !== tx);
    if (state.rrReadLocks[el].length === 0) {
      delete state.rrReadLocks[el];
    }
  }
  for (const el of Object.keys(state.csCursorPins)) {
    state.csCursorPins[el] = state.csCursorPins[el].filter((t) => t !== tx);
    if (state.csCursorPins[el].length === 0) {
      delete state.csCursorPins[el];
    }
  }
}

export function stepMvcc(state: MvccState, op: MvccOp, stepIndex: number): MvccStepResult {
  const next = cloneState(state);

  switch (op.kind) {
    case "BeginOp": {
      if (op.tx in next.txs) {
        return {
          stepIndex,
          op,
          allowed: false,
          nextState: next,
          readValue: null,
          readVersion: null,
          reason: `Transaction ${op.tx} already exists.`
        };
      }
      const startTs = next.clock;
      next.clock += 1;
      next.txs[op.tx] = {
        tx: op.tx,
        level: op.level,
        status: "TxActive",
        startTs,
        commitTs: 0,
        cursorElem: null,
        readSet: [],
        writeSet: []
      };
      return {
        stepIndex,
        op,
        allowed: true,
        nextState: next,
        readValue: null,
        readVersion: null,
        reason: `Started ${op.tx} at ${formatIsolationLevel(op.level)} with snapshot startTs=${startTs}.`
      };
    }

    case "ReadOp": {
      const meta = next.txs[op.tx];
      if (!meta || meta.status !== "TxActive") {
        return {
          stepIndex,
          op,
          allowed: false,
          nextState: next,
          readValue: null,
          readVersion: null,
          reason: `Transaction ${op.tx} is not active.`
        };
      }
      if (
        (meta.level === "ReadCommitted" ||
          meta.level === "CursorStability" ||
          meta.level === "RepeatableRead") &&
        hasOtherWriteOwner(next, op.element, op.tx)
      ) {
        const owner = next.writeOwners[op.element];
        return {
          stepIndex,
          op,
          allowed: false,
          nextState: next,
          readValue: null,
          readVersion: null,
          reason: `Read blocked (Dirty Read prevention under ${formatShortLevel(meta.level)}): ${owner} holds an uncommitted write lock on ${op.element}.`
        };
      }

      const found = findLatestVisibleVersion(next.versions, meta, op.element);
      if (!found) {
        return {
          stepIndex,
          op,
          allowed: false,
          nextState: next,
          readValue: null,
          readVersion: null,
          reason: `No visible version found for ${op.element}.`
        };
      }

      meta.readSet = addUnique(meta.readSet, op.element);
      if (meta.level === "RepeatableRead") {
        next.rrReadLocks[op.element] = addUnique(next.rrReadLocks[op.element] ?? [], op.tx);
      }

      const snapshotNote =
        meta.level === "SnapshotIsolation" || meta.level === "SerializableMVCC"
          ? ` (snapshot xmin=${found.xmin} ≤ startTs=${meta.startTs})`
          : meta.level === "RepeatableRead"
            ? ` (acquired RR read lock on ${op.element})`
            : "";

      return {
        stepIndex,
        op,
        allowed: true,
        nextState: next,
        readValue: found.value,
        readVersion: { ...found },
        reason: `${op.tx} read ${op.element} = ${found.value} from version v#${found.versionId} [creator=${found.creatorTx}, xmin=${found.xmin}]${snapshotNote}.`
      };
    }

    case "FetchCursorOp": {
      const meta = next.txs[op.tx];
      if (!meta || meta.status !== "TxActive") {
        return {
          stepIndex,
          op,
          allowed: false,
          nextState: next,
          readValue: null,
          readVersion: null,
          reason: `Transaction ${op.tx} is not active.`
        };
      }
      if (hasOtherWriteOwner(next, op.element, op.tx)) {
        const owner = next.writeOwners[op.element];
        return {
          stepIndex,
          op,
          allowed: false,
          nextState: next,
          readValue: null,
          readVersion: null,
          reason: `Cursor fetch blocked: ${owner} holds an uncommitted write on ${op.element}.`
        };
      }

      const found = findLatestVisibleVersion(next.versions, meta, op.element);
      if (!found) {
        return {
          stepIndex,
          op,
          allowed: false,
          nextState: next,
          readValue: null,
          readVersion: null,
          reason: `No visible version found for cursor on ${op.element}.`
        };
      }

      const prevCursor = meta.cursorElem;
      setCSPin(next, prevCursor, op.element, op.tx);
      meta.cursorElem = op.element;
      meta.readSet = addUnique(meta.readSet, op.element);
      if (meta.level === "RepeatableRead") {
        next.rrReadLocks[op.element] = addUnique(next.rrReadLocks[op.element] ?? [], op.tx);
      }

      const unpinNote =
        prevCursor && prevCursor !== op.element ? ` (unpinned ${prevCursor}, pinned ${op.element})` : ` (pinned ${op.element})`;

      return {
        stepIndex,
        op,
        allowed: true,
        nextState: next,
        readValue: found.value,
        readVersion: { ...found },
        reason: `${op.tx} fetched cursor on ${op.element} = ${found.value}${unpinNote}.`
      };
    }

    case "CloseCursorOp": {
      const meta = next.txs[op.tx];
      if (!meta || meta.status !== "TxActive") {
        return {
          stepIndex,
          op,
          allowed: false,
          nextState: next,
          readValue: null,
          readVersion: null,
          reason: `Transaction ${op.tx} is not active.`
        };
      }
      const prevCursor = meta.cursorElem;
      setCSPin(next, prevCursor, null, op.tx);
      meta.cursorElem = null;
      return {
        stepIndex,
        op,
        allowed: true,
        nextState: next,
        readValue: null,
        readVersion: null,
        reason: prevCursor
          ? `${op.tx} closed cursor (released CS pin on ${prevCursor}).`
          : `${op.tx} closed cursor.`
      };
    }

    case "WriteOp": {
      const meta = next.txs[op.tx];
      if (!meta || meta.status !== "TxActive") {
        return {
          stepIndex,
          op,
          allowed: false,
          nextState: next,
          readValue: null,
          readVersion: null,
          reason: `Transaction ${op.tx} is not active.`
        };
      }
      const check = checkWriteAllowed(next, meta, op.element);
      if (!check.ok) {
        return {
          stepIndex,
          op,
          allowed: false,
          nextState: next,
          readValue: null,
          readVersion: null,
          reason: check.reason
        };
      }

      const newVer: TupleVersion = {
        versionId: next.versions.length + 1,
        element: op.element,
        value: op.newValue,
        creatorTx: op.tx,
        xmin: next.clock,
        committed: false
      };
      next.clock += 1;
      next.versions.push(newVer);
      meta.writeSet = addUnique(meta.writeSet, op.element);
      next.writeOwners[op.element] = op.tx;

      return {
        stepIndex,
        op,
        allowed: true,
        nextState: next,
        readValue: null,
        readVersion: { ...newVer },
        reason: `${op.tx} created uncommitted version v#${newVer.versionId} of ${op.element} := ${op.newValue} (write owner=${op.tx}).`
      };
    }

    case "CommitOp": {
      const meta = next.txs[op.tx];
      if (!meta || meta.status !== "TxActive") {
        return {
          stepIndex,
          op,
          allowed: false,
          nextState: next,
          readValue: null,
          readVersion: null,
          reason: `Transaction ${op.tx} is not active.`
        };
      }
      const check = checkCommitAllowed(next, meta);
      if (!check.ok) {
        return {
          stepIndex,
          op,
          allowed: false,
          nextState: next,
          readValue: null,
          readVersion: null,
          reason: check.reason
        };
      }

      const commitTs = next.clock;
      next.clock += 1;
      next.versions = next.versions.map((v) =>
        v.creatorTx === op.tx && !v.committed
          ? { ...v, xmin: commitTs, committed: true }
          : v
      );
      releaseTxLocksAndPins(next, op.tx);
      meta.status = "TxCommitted";
      meta.commitTs = commitTs;
      meta.cursorElem = null;

      return {
        stepIndex,
        op,
        allowed: true,
        nextState: next,
        readValue: null,
        readVersion: null,
        reason: check.reason
      };
    }

    case "AbortOp": {
      const meta = next.txs[op.tx];
      if (!meta || meta.status !== "TxActive") {
        return {
          stepIndex,
          op,
          allowed: false,
          nextState: next,
          readValue: null,
          readVersion: null,
          reason: `Transaction ${op.tx} is not active.`
        };
      }
      next.clock += 1;
      next.versions = next.versions.filter((v) => !(v.creatorTx === op.tx && !v.committed));
      releaseTxLocksAndPins(next, op.tx);
      meta.status = "TxAborted";
      meta.cursorElem = null;

      return {
        stepIndex,
        op,
        allowed: true,
        nextState: next,
        readValue: null,
        readVersion: null,
        reason: `${op.tx} aborted and rolled back uncommitted versions.`
      };
    }
  }
}

export function simulateMvccSchedule(
  initialItems: { name: ElementId; value: Value }[],
  ops: MvccOp[]
): {
  snapshots: MvccSimulationSnapshot[];
  results: MvccStepResult[];
  finalState: MvccState;
} {
  let state = initMvccState(initialItems);
  const snapshots: MvccSimulationSnapshot[] = [
    {
      stepIndex: 0,
      label: "Initial MVCC State",
      op: null,
      result: null,
      state: cloneState(state)
    }
  ];
  const results: MvccStepResult[] = [];

  ops.forEach((op, idx) => {
    const res = stepMvcc(state, op, idx + 1);
    state = res.nextState;
    results.push(res);
    snapshots.push({
      stepIndex: idx + 1,
      label: op.raw,
      op,
      result: res,
      state: cloneState(state)
    });
  });

  return {
    snapshots,
    results,
    finalState: state
  };
}

// Runs the same schedule forcing all BEGIN operations to `overrideLevel`
// (for side-by-side comparison across RC, CS, RR, SI, and SerializableMVCC).
export function compareAcrossIsolationLevels(
  initialItems: { name: ElementId; value: Value }[],
  ops: MvccOp[]
): Record<
  IsolationLevel,
  {
    results: MvccStepResult[];
    finalState: MvccState;
    blockedOrRejectedCount: number;
  }
> {
  const levels: IsolationLevel[] = [
    "ReadCommitted",
    "CursorStability",
    "RepeatableRead",
    "SnapshotIsolation",
    "SerializableMVCC"
  ];
  const out = {} as Record<
    IsolationLevel,
    {
      results: MvccStepResult[];
      finalState: MvccState;
      blockedOrRejectedCount: number;
    }
  >;

  for (const lvl of levels) {
    const rewrittenOps: MvccOp[] = ops.map((op) =>
      op.kind === "BeginOp"
        ? {
            ...op,
            level: lvl,
            raw: `BEGIN(${op.tx}, ${formatShortLevel(lvl)})`
          }
        : op
    );
    const sim = simulateMvccSchedule(initialItems, rewrittenOps);
    out[lvl] = {
      results: sim.results,
      finalState: sim.finalState,
      blockedOrRejectedCount: sim.results.filter((r) => !r.allowed).length
    };
  }
  return out;
}

// ---------------------------------------------------------------------------
// Parser & Presets
// ---------------------------------------------------------------------------

export function parseMvccScheduleText(
  text: string,
  defaultLevel: IsolationLevel = "SnapshotIsolation"
): { ops: MvccOp[]; parseErrors: string[] } {
  const ops: MvccOp[] = [];
  const parseErrors: string[] = [];

  const tokens = text
    .split(/[\n;]+/)
    .map((s) => s.trim())
    .filter((s) => s.length > 0 && !s.startsWith("//") && !s.startsWith("#"));

  tokens.forEach((raw, idx) => {
    // Match functional syntax: VERB(arg1, arg2, ...) or whitespace syntax: VERB arg1 arg2
    const parenMatch = raw.match(/^([A-Za-z_]+)\s*\(([^)]*)\)$/);
    let verb = "";
    let args: string[] = [];

    if (parenMatch) {
      verb = parenMatch[1].trim().toUpperCase();
      args = parenMatch[2]
        .split(",")
        .map((a) => a.trim())
        .filter((a) => a.length > 0);
    } else {
      const parts = raw.split(/\s+/);
      verb = (parts[0] ?? "").toUpperCase();
      args = parts.slice(1);
    }

    if (verb === "BEGIN" || verb === "START") {
      const tx = args[0];
      if (!tx) {
        parseErrors.push(`Op #${idx + 1} "${raw}": BEGIN requires a transaction ID.`);
        return;
      }
      const level = args[1] ? parseIsolationLevelToken(args[1], defaultLevel) : defaultLevel;
      ops.push({
        kind: "BeginOp",
        tx,
        level,
        raw: `BEGIN(${tx}, ${formatShortLevel(level)})`
      });
      return;
    }

    if (verb === "R" || verb === "READ") {
      const [tx, element] = args;
      if (!tx || !element) {
        parseErrors.push(`Op #${idx + 1} "${raw}": READ requires (tx, element).`);
        return;
      }
      ops.push({ kind: "ReadOp", tx, element, raw: `READ(${tx}, ${element})` });
      return;
    }

    if (verb === "FETCH" || verb === "FETCH_CURSOR" || verb === "CURSOR") {
      const [tx, element] = args;
      if (!tx || !element) {
        parseErrors.push(`Op #${idx + 1} "${raw}": FETCH_CURSOR requires (tx, element).`);
        return;
      }
      ops.push({
        kind: "FetchCursorOp",
        tx,
        element,
        raw: `FETCH_CURSOR(${tx}, ${element})`
      });
      return;
    }

    if (verb === "CLOSE" || verb === "CLOSE_CURSOR") {
      const [tx] = args;
      if (!tx) {
        parseErrors.push(`Op #${idx + 1} "${raw}": CLOSE_CURSOR requires (tx).`);
        return;
      }
      ops.push({
        kind: "CloseCursorOp",
        tx,
        raw: `CLOSE_CURSOR(${tx})`
      });
      return;
    }

    if (verb === "W" || verb === "WRITE") {
      const [tx, element, valStr] = args;
      const newValue = Number(valStr);
      if (!tx || !element || !Number.isInteger(newValue)) {
        parseErrors.push(`Op #${idx + 1} "${raw}": WRITE requires (tx, element, integerValue).`);
        return;
      }
      ops.push({
        kind: "WriteOp",
        tx,
        element,
        newValue,
        raw: `WRITE(${tx}, ${element}, ${newValue})`
      });
      return;
    }

    if (verb === "C" || verb === "COMMIT") {
      const [tx] = args;
      if (!tx) {
        parseErrors.push(`Op #${idx + 1} "${raw}": COMMIT requires (tx).`);
        return;
      }
      ops.push({ kind: "CommitOp", tx, raw: `COMMIT(${tx})` });
      return;
    }

    if (verb === "A" || verb === "ABORT") {
      const [tx] = args;
      if (!tx) {
        parseErrors.push(`Op #${idx + 1} "${raw}": ABORT requires (tx).`);
        return;
      }
      ops.push({ kind: "AbortOp", tx, raw: `ABORT(${tx})` });
      return;
    }

    parseErrors.push(
      `Op #${idx + 1} "${raw}": unrecognized MVCC operation (use BEGIN, READ, FETCH_CURSOR, CLOSE_CURSOR, WRITE, COMMIT, ABORT).`
    );
  });

  return { ops, parseErrors };
}

export interface MvccPreset {
  id: string;
  title: string;
  description: string;
  defaultLevel: IsolationLevel;
  initialItems: { name: ElementId; value: Value }[];
  scheduleText: string;
}

export const MVCC_PRESETS: MvccPreset[] = [
  {
    id: "si-snapshot-fcw",
    title: "1. Snapshot Isolation & First-Committer-Wins",
    description:
      "Mirrors TestSnapshotIsolationVerified in Main.dfy: T1 reads A=100 from its snapshot (xmin ≤ startTs=1) even after T2 commits A=200 at ts=4, and First-Committer-Wins blocks T1's conflicting overwrite.",
    defaultLevel: "SnapshotIsolation",
    initialItems: [{ name: "A", value: 100 }],
    scheduleText: [
      "BEGIN(T1, SI)",
      "BEGIN(T2, SI)",
      "WRITE(T2, A, 200)",
      "COMMIT(T2)",
      "READ(T1, A)",
      "WRITE(T1, A, 300)"
    ].join("\n")
  },
  {
    id: "write-skew-ssi",
    title: "2. Write Skew (SI Allows vs Serializable Rejects)",
    description:
      "Mirrors TestWriteSkewSerializableVerified in Main.dfy: T1 and T2 both read A=1, B=1; T1 writes A:=0 and T2 writes B:=0 (disjoint write sets). Under SI both commit; under SerializableMVCC (SSI) T2 is rejected at commit!",
    defaultLevel: "SerializableMVCC",
    initialItems: [
      { name: "A", value: 1 },
      { name: "B", value: 1 }
    ],
    scheduleText: [
      "BEGIN(T1, SSI)",
      "BEGIN(T2, SSI)",
      "READ(T1, A)",
      "READ(T2, A)",
      "WRITE(T1, A, 0)",
      "WRITE(T2, B, 0)",
      "COMMIT(T1)",
      "COMMIT(T2)"
    ].join("\n")
  },
  {
    id: "rc-dirty-and-nonrepeatable",
    title: "3. Read Committed: Blocks Dirty Read, Allows Non-Repeatable Read",
    description:
      "Mirrors TestReadCommittedVerified in Main.dfy: T1 reads A=100; while T2 has uncommitted A=200, T1's read is blocked (no Dirty Read); once T2 commits, T1 re-reads A and sees 200 (Non-Repeatable Read).",
    defaultLevel: "ReadCommitted",
    initialItems: [{ name: "A", value: 100 }],
    scheduleText: [
      "BEGIN(T1, RC)",
      "BEGIN(T2, RC)",
      "READ(T1, A)",
      "WRITE(T2, A, 200)",
      "READ(T1, A)",
      "COMMIT(T2)",
      "READ(T1, A)",
      "COMMIT(T1)"
    ].join("\n")
  },
  {
    id: "cs-cursor-pin",
    title: "4. Cursor Stability (CS): Cursor Pinning & Unpinning",
    description:
      "Mirrors TestCursorStabilityVerified in Main.dfy: T1 fetches cursor on A (pinning A and blocking T2's write on A); when T1 advances cursor to B, A is unpinned so T2 can write A.",
    defaultLevel: "CursorStability",
    initialItems: [
      { name: "A", value: 10 },
      { name: "B", value: 20 }
    ],
    scheduleText: [
      "BEGIN(T1, CS)",
      "BEGIN(T2, RC)",
      "FETCH_CURSOR(T1, A)",
      "WRITE(T2, A, 99)",
      "FETCH_CURSOR(T1, B)",
      "WRITE(T2, A, 99)",
      "COMMIT(T2)",
      "COMMIT(T1)"
    ].join("\n")
  },
  {
    id: "rr-persistent-read-lock",
    title: "5. Repeatable Read (RR): Persistent Read Locks Until Commit",
    description:
      "Mirrors TestRepeatableReadVerified in Main.dfy: T1 reads A under RR (acquiring a persistent read lock on A) and then reads B; T2 is still blocked from writing A until T1 commits.",
    defaultLevel: "RepeatableRead",
    initialItems: [
      { name: "A", value: 10 },
      { name: "B", value: 20 }
    ],
    scheduleText: [
      "BEGIN(T1, RR)",
      "BEGIN(T2, RC)",
      "READ(T1, A)",
      "READ(T1, B)",
      "WRITE(T2, A, 50)",
      "COMMIT(T1)",
      "WRITE(T2, A, 50)",
      "COMMIT(T2)"
    ].join("\n")
  }
];
