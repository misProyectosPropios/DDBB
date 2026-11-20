// Interactive Logging Workbench page supporting both Undo and Redo logging,
// composed with None / Quiescent / Non-Quiescent checkpointing and
// checkpoint-aware crash recovery.

import {
  createCheckpointStrategy,
  formatCheckpointState,
  type CheckpointMode
} from "../logging/checkpointing";
import {
  AbortOp,
  CheckpointOp,
  CommitOp,
  ReadOp,
  Schedule,
  StartOp,
  WriteOp,
  type LoggingStepSnapshot,
  type LoggingStrategy,
  type Operation,
  type RecoveryResult,
  type RecoveryStrategy
} from "../logging/dispatch";
import { parseScheduleText, serializeSchedule } from "../logging/parser";
import { RedoLogger } from "../logging/redoLogger";
import { RedoRecoveryStrategy } from "../logging/redoRecovery";
import {
  formatLogRecord,
  formatTraceEvent,
  type DatabaseState,
  type LogRecord,
  type TraceEvent
} from "../logging/types";
import { UndoLogger } from "../logging/undoLogger";
import { UndoRecoveryStrategy } from "../logging/undoRecovery";

export type LoggingProtocol = "undo" | "redo";

interface DbVariable {
  name: string;
  value: number;
}

interface Preset {
  id: string;
  label: string;
  description: string;
  checkpointMode: CheckpointMode;
  variables: DbVariable[];
  scheduleText: string;
}

const PRESETS: Preset[] = [
  {
    id: "xy-basic",
    label: "X=5, Y=10 (Commit & Abort)",
    description: "T1 updates X and commits; T2 updates Y and aborts.",
    checkpointMode: "none",
    variables: [
      { name: "X", value: 5 },
      { name: "Y", value: 10 }
    ],
    scheduleText: [
      "START T1",
      "START T2",
      "READ T1 X",
      "WRITE T1 X 12",
      "WRITE T2 Y 99",
      "COMMIT T1",
      "ABORT T2"
    ].join("\n")
  },
  {
    id: "quiescent-ckpt",
    label: "Quiescent Checkpoint",
    description: "Checkpoint blocks new START T2 while T1 drains, emits <CKPT>, then lets T3 start.",
    checkpointMode: "quiescent",
    variables: [
      { name: "X", value: 5 },
      { name: "Y", value: 10 }
    ],
    scheduleText: [
      "START T1",
      "WRITE T1 X 12",
      "CHECKPOINT",
      "START T2",
      "COMMIT T1",
      "START T3",
      "WRITE T3 Y 20",
      "COMMIT T3"
    ].join("\n")
  },
  {
    id: "non-quiescent-ckpt",
    label: "Non-Quiescent Checkpoint",
    description: "Emits <START CKPT(T1)> while allowing T2 to start concurrently.",
    checkpointMode: "non-quiescent",
    variables: [
      { name: "X", value: 5 },
      { name: "Y", value: 10 }
    ],
    scheduleText: [
      "START T1",
      "WRITE T1 X 12",
      "CHECKPOINT",
      "START T2",
      "WRITE T2 Y 25",
      "COMMIT T1",
      "COMMIT T2"
    ].join("\n")
  },
  {
    id: "crash-ckpt",
    label: "Crash After Checkpoint",
    description: "T1 commits before <CKPT>; T2 writes Y=999 without committing before crash.",
    checkpointMode: "quiescent",
    variables: [
      { name: "X", value: 5 },
      { name: "Y", value: 10 }
    ],
    scheduleText: [
      "START T1",
      "WRITE T1 X 50",
      "COMMIT T1",
      "CHECKPOINT",
      "START T2",
      "WRITE T2 Y 999"
    ].join("\n")
  },
  {
    id: "garcia-molina",
    label: "Classic T1 (A=8, B=8 → 16)",
    description: "Garcia-Molina textbook example: T1 doubles A and B then commits.",
    checkpointMode: "none",
    variables: [
      { name: "A", value: 8 },
      { name: "B", value: 8 }
    ],
    scheduleText: [
      "START T1",
      "READ T1 A",
      "WRITE T1 A 16",
      "READ T1 B",
      "WRITE T1 B 16",
      "COMMIT T1"
    ].join("\n")
  }
];

function escapeHtml(text: string): string {
  return text
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;")
    .replaceAll("'", "&#39;");
}

function logBadgeClass(r: LogRecord): string {
  switch (r.kind) {
    case "LogStart":
      return "badge-start";
    case "LogUndoUpdate":
    case "LogRedoUpdate":
      return "badge-update";
    case "LogCommit":
      return "badge-commit";
    case "LogAbort":
      return "badge-abort";
    case "LogCheckpoint":
    case "LogStartCheckpoint":
    case "LogEndCheckpoint":
      return "badge-ckpt";
  }
}

function traceTag(e: TraceEvent): { label: string; cls: string } {
  switch (e.kind) {
    case "EventLog":
      return { label: "LOG", cls: "tag-log" };
    case "EventRead":
      return { label: "READ", cls: "tag-read" };
    case "EventWriteBuffer":
      return { label: "WRITE", cls: "tag-write" };
    case "EventUndoRestore":
      return { label: "UNDO", cls: "tag-undo" };
    case "EventFlushLog":
      return { label: "FLUSH", cls: "tag-flush" };
    case "EventOutput":
      return { label: "OUTPUT", cls: "tag-output" };
  }
}

export function renderLoggingPage(
  initialProtocol: LoggingProtocol,
  onProtocolChange: (protocol: LoggingProtocol) => void
): HTMLElement {
  const article = document.createElement("article");
  article.className = "blog-article";

  // Workbench state
  let protocol: LoggingProtocol = initialProtocol;
  let checkpointMode: CheckpointMode = PRESETS[0].checkpointMode;
  let variables: DbVariable[] = PRESETS[0].variables.map((v) => ({ ...v }));
  let operations: Operation[] = parseScheduleText(PRESETS[0].scheduleText).operations;
  let scheduleText = serializeSchedule(operations);
  let parseErrors: string[] = [];
  let inputMode: "builder" | "text" = "builder";
  let selectedStep: number | null = null;
  let simulateStaleDiskForRedo = false;
  let crashResult: {
    stepIndex: number;
    protocol: LoggingProtocol;
    checkpointMode: CheckpointMode;
    diskBeforeCrash: DatabaseState;
    flushedLog: LogRecord[];
    result: RecoveryResult;
  } | null = null;

  let newOpKind: Operation["kind"] = "WRITE";
  let newOpTx = "T1";
  let newOpElement = "X";
  let newOpValue = "12";
  let newVarName = "";
  let newVarValue = "0";
  let varFormError = "";

  function buildInitialDb(): DatabaseState {
    const db: DatabaseState = {};
    for (const v of variables) {
      db[v.name] = v.value;
    }
    return db;
  }

  function runSimulation(): {
    snapshots: readonly LoggingStepSnapshot[];
    activeSnapshot: LoggingStepSnapshot;
  } {
    const db = buildInitialDb();
    const ckptStrategy = createCheckpointStrategy(checkpointMode);
    const logger: LoggingStrategy =
      protocol === "undo"
        ? new UndoLogger(db, ckptStrategy)
        : new RedoLogger(db, ckptStrategy);
    const schedule = new Schedule(operations);
    schedule.run(logger);
    const snapshots = logger.snapshots;
    const maxStep = snapshots.length - 1;
    const clampedStep =
      selectedStep === null ? maxStep : Math.max(0, Math.min(selectedStep, maxStep));
    return {
      snapshots,
      activeSnapshot: snapshots[clampedStep]
    };
  }

  function clearCrash(): void {
    crashResult = null;
  }

  function renderHeader(): string {
    if (protocol === "undo") {
      return `
        <header class="article-header">
          <div class="breadcrumb">Logging / Undo Logging</div>
          <h1>Undo Logging</h1>
          <p class="article-lead">
            Undo logging records the <strong>old value</strong> of every element before it is
            modified in memory (<code>&lt;T, X, oldVal&gt;</code>), ensuring uncommitted writes can
            always be reversed during crash recovery.
          </p>

          <div class="callout-rules">
            <div class="rule-card">
              <span class="rule-pill">Rule U1 · WAL</span>
              <p>
                Before an updated element is written to disk (<code>OUTPUT</code>), its
                <code>&lt;T, X, oldVal&gt;</code> record must already be flushed to disk
                (<code>FLUSH LOG</code>).
              </p>
            </div>
            <div class="rule-card">
              <span class="rule-pill">Rule U2 · Commit Order</span>
              <p>
                Before <code>&lt;COMMIT T&gt;</code> is written and flushed, every element modified
                by <code>T</code> must already be written to disk (<code>OUTPUT</code>).
              </p>
            </div>
          </div>
        </header>
      `;
    }

    return `
      <header class="article-header">
        <div class="breadcrumb">Logging / Redo Logging</div>
        <h1>Redo Logging</h1>
        <p class="article-lead">
          Redo logging records the <strong>new value</strong> of every element
          (<code>&lt;T, X, newVal&gt;</code>) and delays disk writes until after
          <code>&lt;COMMIT T&gt;</code> is flushed, ensuring committed writes can always be replayed.
        </p>

        <div class="callout-rules">
          <div class="rule-card">
            <span class="rule-pill">Rule R1 · WAL + Commit First</span>
            <p>
              Before any modified element is written to disk (<code>OUTPUT</code>), both its
              <code>&lt;T, X, newVal&gt;</code> update and <code>&lt;COMMIT T&gt;</code> must be
              flushed to disk (<code>FLUSH LOG</code>).
            </p>
          </div>
          <div class="rule-card">
            <span class="rule-pill">Forward Replay Recovery</span>
            <p>
              On crash, Redo recovery scans <strong>forward</strong> from the last completed
              checkpoint, replaying updates of committed transactions while ignoring uncommitted ones.
            </p>
          </div>
        </div>
      </header>
    `;
  }

  function render(): void {
    const { snapshots, activeSnapshot } = runSimulation();
    const maxStep = snapshots.length - 1;
    const currentStepIdx = activeSnapshot.stepIndex;

    const dbElementNames = variables.map((v) => v.name);
    if (
      dbElementNames.length > 0 &&
      !newOpElement &&
      (newOpKind === "READ" || newOpKind === "WRITE")
    ) {
      newOpElement = dbElementNames[0];
    }

    const ckptBadgeCls =
      activeSnapshot.ckptState.kind === "CkptDrainingQuiescent"
        ? "ckpt-draining"
        : activeSnapshot.ckptState.kind === "CkptActiveNonQuiescent"
          ? "ckpt-active"
          : "ckpt-idle";

    article.innerHTML = `
      ${renderHeader()}

      <section class="workbench" aria-label="Interactive Logging Workbench">
        <!-- Strategy Configuration Bar -->
        <div class="strategy-bar">
          <div class="strategy-group">
            <span class="strategy-label">Logging Protocol</span>
            <div class="segmented" role="group" aria-label="Logging protocol">
              <button
                type="button"
                class="segmented-btn${protocol === "undo" ? " is-active" : ""}"
                data-protocol="undo"
              >Undo</button>
              <button
                type="button"
                class="segmented-btn${protocol === "redo" ? " is-active" : ""}"
                data-protocol="redo"
              >Redo</button>
            </div>
          </div>

          <div class="strategy-group">
            <span class="strategy-label">Checkpointing Strategy</span>
            <div class="segmented" role="group" aria-label="Checkpointing strategy">
              <button
                type="button"
                class="segmented-btn${checkpointMode === "none" ? " is-active" : ""}"
                data-ckpt-mode="none"
              >None</button>
              <button
                type="button"
                class="segmented-btn${checkpointMode === "quiescent" ? " is-active" : ""}"
                data-ckpt-mode="quiescent"
              >Quiescent</button>
              <button
                type="button"
                class="segmented-btn${checkpointMode === "non-quiescent" ? " is-active" : ""}"
                data-ckpt-mode="non-quiescent"
              >Non-Quiescent</button>
            </div>
          </div>
        </div>

        <div class="presets-bar">
          <span class="presets-label">Examples:</span>
          <div class="presets-list">
            ${PRESETS.map(
              (p) => `
              <button type="button" class="btn btn-chip" data-preset="${p.id}" title="${escapeHtml(p.description)}">
                ${escapeHtml(p.label)}
              </button>
            `
            ).join("")}
          </div>
        </div>

        <div class="workbench-inputs">
          <!-- Initial Database State -->
          <div class="panel">
            <div class="panel-header">
              <h2>1. Initial Database State</h2>
              <span class="panel-meta">${variables.length} element${variables.length === 1 ? "" : "s"}</span>
            </div>
            <p class="panel-hint">Starting values stored on disk and in memory (e.g., <code>X = 5</code>, <code>Y = 10</code>).</p>

            <div class="var-list">
              ${
                variables.length === 0
                  ? `<div class="empty-inline">No database elements yet. Add one below.</div>`
                  : variables
                      .map(
                        (v, idx) => `
                <div class="var-chip">
                  <span class="var-name">${escapeHtml(v.name)}</span>
                  <span class="var-eq">=</span>
                  <input
                    type="number"
                    step="1"
                    class="var-value-input"
                    value="${v.value}"
                    data-var-index="${idx}"
                    aria-label="Value of ${escapeHtml(v.name)}"
                  />
                  <button
                    type="button"
                    class="icon-btn"
                    data-remove-var="${idx}"
                    title="Remove ${escapeHtml(v.name)}"
                    aria-label="Remove ${escapeHtml(v.name)}"
                  >×</button>
                </div>
              `
                      )
                      .join("")
              }
            </div>

            <form class="inline-form" data-add-var-form>
              <input
                type="text"
                class="input input-sm"
                name="varName"
                placeholder="Element (e.g. Z)"
                value="${escapeHtml(newVarName)}"
                autocomplete="off"
              />
              <input
                type="number"
                step="1"
                class="input input-sm input-num"
                name="varValue"
                placeholder="Value"
                value="${escapeHtml(newVarValue)}"
              />
              <button type="submit" class="btn btn-secondary">Add Variable</button>
            </form>
            ${varFormError ? `<div class="inline-error">${escapeHtml(varFormError)}</div>` : ""}
          </div>

          <!-- Schedule Builder -->
          <div class="panel">
            <div class="panel-header">
              <h2>2. Schedule</h2>
              <div class="segmented" role="tablist" aria-label="Schedule input mode">
                <button
                  type="button"
                  class="segmented-btn${inputMode === "builder" ? " is-active" : ""}"
                  data-mode="builder"
                >Builder</button>
                <button
                  type="button"
                  class="segmented-btn${inputMode === "text" ? " is-active" : ""}"
                  data-mode="text"
                >Text</button>
              </div>
            </div>

            ${
              inputMode === "builder"
                ? `
              <form class="op-builder-form" data-add-op-form>
                <select class="input input-sm" name="opKind" aria-label="Operation type">
                  ${(["START", "READ", "WRITE", "COMMIT", "ABORT", "CHECKPOINT"] as const)
                    .map(
                      (k) =>
                        `<option value="${k}"${k === newOpKind ? " selected" : ""}>${k}</option>`
                    )
                    .join("")}
                </select>

                ${
                  newOpKind !== "CHECKPOINT"
                    ? `
                  <input
                    type="text"
                    class="input input-sm input-tx"
                    name="opTx"
                    placeholder="Tx (e.g. T1)"
                    value="${escapeHtml(newOpTx)}"
                    aria-label="Transaction ID"
                    autocomplete="off"
                  />
                `
                    : ""
                }

                ${
                  newOpKind === "READ" || newOpKind === "WRITE"
                    ? `
                  <input
                    type="text"
                    class="input input-sm input-elem"
                    name="opElement"
                    list="db-elements-datalist"
                    placeholder="Element (e.g. X)"
                    value="${escapeHtml(newOpElement)}"
                    aria-label="Database element"
                    autocomplete="off"
                  />
                  <datalist id="db-elements-datalist">
                    ${dbElementNames.map((n) => `<option value="${escapeHtml(n)}"></option>`).join("")}
                  </datalist>
                `
                    : ""
                }

                ${
                  newOpKind === "WRITE"
                    ? `
                  <input
                    type="number"
                    step="1"
                    class="input input-sm input-num"
                    name="opValue"
                    placeholder="New value"
                    value="${escapeHtml(newOpValue)}"
                    aria-label="New integer value"
                  />
                `
                    : ""
                }

                <button type="submit" class="btn btn-primary">+ Add</button>
              </form>

              <div class="schedule-list-header">
                <span class="panel-meta">${operations.length} operation${operations.length === 1 ? "" : "s"}</span>
                ${
                  operations.length > 0
                    ? `<button type="button" class="link-danger" data-clear-ops>Clear schedule</button>`
                    : ""
                }
              </div>

              <ol class="schedule-list">
                ${
                  operations.length === 0
                    ? `<li class="empty-inline">Add operations above to build a schedule.</li>`
                    : operations
                        .map((op, idx) => {
                          const stepNum = idx + 1;
                          const isCurrent = stepNum === currentStepIdx;
                          const isFuture = stepNum > currentStepIdx;
                          return `
                    <li class="schedule-row${isCurrent ? " is-current" : ""}${isFuture ? " is-future" : ""}" data-select-step="${stepNum}">
                      <span class="step-num">${stepNum}</span>
                      <code class="op-code">${escapeHtml(op.format())}</code>
                      <span class="row-actions">
                        <button type="button" class="icon-btn" data-move-up="${idx}" ${idx === 0 ? "disabled" : ""} title="Move up" aria-label="Move up">↑</button>
                        <button type="button" class="icon-btn" data-move-down="${idx}" ${idx === operations.length - 1 ? "disabled" : ""} title="Move down" aria-label="Move down">↓</button>
                        <button type="button" class="icon-btn" data-remove-op="${idx}" title="Remove operation" aria-label="Remove operation">×</button>
                      </span>
                    </li>
                  `;
                        })
                        .join("")
                }
              </ol>
            `
                : `
              <p class="panel-hint">
                One operation per line: <code>START T1</code>, <code>READ T1 X</code>,
                <code>WRITE T1 X 12</code>, <code>COMMIT T1</code>, <code>ABORT T2</code>,
                <code>CHECKPOINT</code>.
              </p>
              <textarea
                class="schedule-textarea"
                rows="8"
                spellcheck="false"
                data-schedule-textarea
                aria-label="Schedule text"
              >${escapeHtml(scheduleText)}</textarea>
              ${
                parseErrors.length > 0
                  ? `<div class="error-box">
                      <strong>Syntax issues:</strong>
                      <ul>${parseErrors.map((e) => `<li>${escapeHtml(e)}</li>`).join("")}</ul>
                    </div>`
                  : ""
              }
            `
            }
          </div>
        </div>

        <!-- Step Controls -->
        <div class="step-bar">
          <div class="step-bar-info">
            <span class="step-badge">Step ${currentStepIdx} / ${maxStep}</span>
            <span class="step-label">${escapeHtml(activeSnapshot.operationLabel)}</span>
          </div>
          <div class="step-bar-controls">
            <button type="button" class="btn btn-secondary btn-sm" data-step-first ${currentStepIdx === 0 ? "disabled" : ""}>⏮ Start</button>
            <button type="button" class="btn btn-secondary btn-sm" data-step-prev ${currentStepIdx === 0 ? "disabled" : ""}>← Prev</button>
            <input
              type="range"
              min="0"
              max="${maxStep}"
              value="${currentStepIdx}"
              class="step-slider"
              data-step-slider
              aria-label="Execution step"
            />
            <button type="button" class="btn btn-secondary btn-sm" data-step-next ${currentStepIdx === maxStep ? "disabled" : ""}>Next →</button>
            <button type="button" class="btn btn-secondary btn-sm" data-step-last ${currentStepIdx === maxStep ? "disabled" : ""}>End ⏭</button>
          </div>
        </div>

        ${
          activeSnapshot.errors.length > 0
            ? `
          <div class="error-box">
            <strong>Schedule validation / checkpoint messages (${activeSnapshot.errors.length}):</strong>
            <ul>
              ${activeSnapshot.errors.map((err) => `<li>${escapeHtml(err)}</li>`).join("")}
            </ul>
          </div>
        `
            : ""
        }

        <!-- Live Outputs -->
        <div class="outputs-grid">
          <!-- Generated Log -->
          <div class="panel">
            <div class="panel-header">
              <h2>Generated ${protocol === "undo" ? "Undo" : "Redo"} Log</h2>
              <span class="panel-meta">Flushed: ${activeSnapshot.flushedLogLen} / ${activeSnapshot.log.length}</span>
            </div>
            ${
              activeSnapshot.log.length === 0
                ? `<div class="empty-state">No log records emitted yet.</div>`
                : `
              <ol class="log-list">
                ${activeSnapshot.log
                  .map((rec, idx) => {
                    const isFlushed = idx < activeSnapshot.flushedLogLen;
                    const showFlushDivider =
                      activeSnapshot.flushedLogLen > 0 &&
                      idx === activeSnapshot.flushedLogLen - 1;
                    return `
                    <li class="log-row${isFlushed ? " is-flushed" : " is-unflushed"}">
                      <span class="log-idx">#${idx + 1}</span>
                      <code class="log-record ${logBadgeClass(rec)}">${escapeHtml(formatLogRecord(rec))}</code>
                      <span class="flush-pill">${isFlushed ? "on disk" : "in log buffer"}</span>
                    </li>
                    ${
                      showFlushDivider
                        ? `<li class="flush-divider" aria-hidden="true"><span>↑ flushed to disk (record #${activeSnapshot.flushedLogLen})</span></li>`
                        : ""
                    }
                  `;
                  })
                  .join("")}
              </ol>
            `
            }
          </div>

          <!-- Storage, Transactions & Checkpoint State -->
          <div class="panel">
            <div class="panel-header">
              <h2>Buffer vs. Disk &amp; Transactions</h2>
              <span class="panel-meta">At step ${currentStepIdx}</span>
            </div>

            <div class="tx-status-group">
              <div class="tx-bucket">
                <span class="tx-bucket-label">Checkpoint</span>
                <span class="ckpt-pill ${ckptBadgeCls}">${escapeHtml(formatCheckpointState(activeSnapshot.ckptState))}</span>
              </div>
              <div class="tx-bucket">
                <span class="tx-bucket-label">Active</span>
                ${
                  activeSnapshot.activeTxs.length === 0
                    ? `<span class="tx-none">—</span>`
                    : activeSnapshot.activeTxs
                        .map((t) => `<span class="tx-pill tx-active">${escapeHtml(t)}</span>`)
                        .join("")
                }
              </div>
              <div class="tx-bucket">
                <span class="tx-bucket-label">Committed</span>
                ${
                  activeSnapshot.committedTxs.length === 0
                    ? `<span class="tx-none">—</span>`
                    : activeSnapshot.committedTxs
                        .map((t) => `<span class="tx-pill tx-committed">${escapeHtml(t)}</span>`)
                        .join("")
                }
              </div>
              <div class="tx-bucket">
                <span class="tx-bucket-label">Aborted</span>
                ${
                  activeSnapshot.abortedTxs.length === 0
                    ? `<span class="tx-none">—</span>`
                    : activeSnapshot.abortedTxs
                        .map((t) => `<span class="tx-pill tx-aborted">${escapeHtml(t)}</span>`)
                        .join("")
                }
              </div>
            </div>

            <table class="state-table">
              <thead>
                <tr>
                  <th>Element</th>
                  <th>Memory Buffer</th>
                  <th>Disk</th>
                  <th>Status</th>
                </tr>
              </thead>
              <tbody>
                ${
                  variables.length === 0
                    ? `<tr><td colspan="4" class="empty-inline">No variables defined.</td></tr>`
                    : variables
                        .map((v) => {
                          const bufVal = activeSnapshot.buffer[v.name];
                          const diskVal = activeSnapshot.disk[v.name];
                          const isDirty = bufVal !== diskVal;
                          return `
                    <tr class="${isDirty ? "row-dirty" : ""}">
                      <td><code>${escapeHtml(v.name)}</code></td>
                      <td><code>${bufVal}</code></td>
                      <td><code>${diskVal}</code></td>
                      <td>
                        <span class="sync-pill ${isDirty ? "sync-dirty" : "sync-clean"}">
                          ${isDirty ? "Dirty (in buffer)" : "Synced"}
                        </span>
                      </td>
                    </tr>
                  `;
                        })
                        .join("")
                }
              </tbody>
            </table>
          </div>
        </div>

        <!-- Execution Trace -->
        <div class="panel panel-full">
          <div class="panel-header">
            <h2>Execution Trace (${protocol === "undo" ? "Rules U1 & U2" : "Rule R1 · WAL Before OUTPUT"})</h2>
            <span class="panel-meta">${activeSnapshot.trace.length} event${activeSnapshot.trace.length === 1 ? "" : "s"}</span>
          </div>
          ${
            activeSnapshot.trace.length === 0
              ? `<div class="empty-state">Execute operations to inspect the chronological log, buffer, flush, and disk events.</div>`
              : `
            <ol class="trace-list">
              ${activeSnapshot.trace
                .map((ev, idx) => {
                  const tag = traceTag(ev);
                  const isNew = idx >= activeSnapshot.newTraceStart && currentStepIdx > 0;
                  return `
                  <li class="trace-row${isNew ? " is-new" : ""}">
                    <span class="trace-idx">${idx + 1}</span>
                    <span class="trace-tag ${tag.cls}">${tag.label}</span>
                    <code class="trace-text">${escapeHtml(formatTraceEvent(ev).replace(/^[A-Z]+\s+/, ""))}</code>
                  </li>
                `;
                })
                .join("")}
            </ol>
          `
          }
        </div>

        <!-- Crash Recovery Simulator -->
        <div class="panel panel-full panel-recovery">
          <div class="panel-header">
            <div>
              <h2>${protocol === "undo" ? "Undo" : "Redo"} Crash Recovery Check</h2>
              <p class="panel-hint">
                Runs <code>${protocol === "undo" ? "UndoRecoveryStrategy" : "RedoRecoveryStrategy"}.RecoverFromCrash</code>
                at <strong>step ${currentStepIdx}</strong> using only the flushed log (records #1–#${activeSnapshot.flushedLogLen}).
              </p>
              ${
                protocol === "redo"
                  ? `
                <label class="checkbox-inline">
                  <input type="checkbox" data-stale-disk ${simulateStaleDiskForRedo ? "checked" : ""} />
                  <span>Simulate crash before <code>OUTPUT</code> reached disk (start recovery from initial disk values)</span>
                </label>
              `
                  : ""
              }
            </div>
            <button type="button" class="btn btn-secondary" data-simulate-crash>
              Simulate Crash at Step ${currentStepIdx}
            </button>
          </div>

          ${
            crashResult &&
            crashResult.stepIndex === currentStepIdx &&
            crashResult.protocol === protocol &&
            crashResult.checkpointMode === checkpointMode
              ? `
            <div class="recovery-result">
              <div class="recovery-col">
                <h3>${protocol === "undo" ? "Backward Undo Scan Actions" : "Forward Redo Replay Actions"}</h3>
                ${
                  crashResult.result.actions.length === 0
                    ? `<p class="panel-hint">No recovery actions needed — disk is already consistent with the flushed log.</p>`
                    : `
                  <ul class="recovery-actions">
                    ${crashResult.result.actions
                      .map((act) => {
                        if (act.kind === "RESTORE") {
                          return `<li>Undo <code>${escapeHtml(act.element ?? "")} := ${act.value}</code> (uncommitted <code>${escapeHtml(act.tx ?? "")}</code>)</li>`;
                        }
                        if (act.kind === "REDO") {
                          return `<li>Redo <code>${escapeHtml(act.element ?? "")} := ${act.value}</code> (committed <code>${escapeHtml(act.tx ?? "")}</code>)</li>`;
                        }
                        if (act.kind === "ABORT") {
                          return `<li>Emit <code>&lt;ABORT ${escapeHtml(act.tx ?? "")}&gt;</code></li>`;
                        }
                        return `<li class="recovery-boundary">${escapeHtml(act.note ?? "")}</li>`;
                      })
                      .join("")}
                  </ul>
                `
                }
              </div>
              <div class="recovery-col">
                <h3>Recovered Disk State</h3>
                <div class="var-list">
                  ${Object.entries(crashResult.result.recoveredDisk)
                    .map(
                      ([k, val]) => `
                    <span class="var-chip var-chip-readonly">
                      <span class="var-name">${escapeHtml(k)}</span>
                      <span class="var-eq">=</span>
                      <code>${val}</code>
                    </span>
                  `
                    )
                    .join("")}
                </div>
              </div>
            </div>
          `
              : ""
          }
        </div>
      </section>
    `;

    bindEvents(activeSnapshot, maxStep);
  }

  function bindEvents(activeSnapshot: LoggingStepSnapshot, maxStep: number): void {
    // Protocol toggle (Undo / Redo)
    article.querySelectorAll<HTMLButtonElement>("[data-protocol]").forEach((btn) => {
      btn.addEventListener("click", () => {
        const next = btn.dataset.protocol as LoggingProtocol;
        if (next === protocol) return;
        protocol = next;
        clearCrash();
        onProtocolChange(next);
        render();
      });
    });

    // Checkpointing strategy toggle (None / Quiescent / Non-Quiescent)
    article.querySelectorAll<HTMLButtonElement>("[data-ckpt-mode]").forEach((btn) => {
      btn.addEventListener("click", () => {
        const next = btn.dataset.ckptMode as CheckpointMode;
        if (next === checkpointMode) return;
        checkpointMode = next;
        clearCrash();
        render();
      });
    });

    // Presets
    article.querySelectorAll<HTMLButtonElement>("[data-preset]").forEach((btn) => {
      btn.addEventListener("click", () => {
        const preset = PRESETS.find((p) => p.id === btn.dataset.preset);
        if (!preset) return;
        checkpointMode = preset.checkpointMode;
        variables = preset.variables.map((v) => ({ ...v }));
        const parsed = parseScheduleText(preset.scheduleText);
        operations = parsed.operations;
        scheduleText = serializeSchedule(operations);
        parseErrors = parsed.parseErrors;
        selectedStep = null;
        varFormError = "";
        newOpElement = variables[0]?.name ?? "X";
        clearCrash();
        render();
      });
    });

    // Edit variable values
    article.querySelectorAll<HTMLInputElement>("[data-var-index]").forEach((input) => {
      input.addEventListener("change", () => {
        const idx = Number(input.dataset.varIndex);
        const val = Number(input.value);
        if (!Number.isInteger(val)) {
          input.value = String(variables[idx].value);
          return;
        }
        variables[idx].value = val;
        clearCrash();
        render();
      });
    });

    // Remove variable
    article.querySelectorAll<HTMLButtonElement>("[data-remove-var]").forEach((btn) => {
      btn.addEventListener("click", () => {
        const idx = Number(btn.dataset.removeVar);
        variables.splice(idx, 1);
        clearCrash();
        render();
      });
    });

    // Add variable form
    const addVarForm = article.querySelector<HTMLFormElement>("[data-add-var-form]");
    addVarForm?.addEventListener("submit", (e) => {
      e.preventDefault();
      const formData = new FormData(addVarForm);
      const rawName = String(formData.get("varName") ?? "").trim();
      const rawVal = String(formData.get("varValue") ?? "").trim();
      const parsedVal = Number(rawVal);

      if (!rawName || /\s/.test(rawName)) {
        varFormError = "Element name must be a non-empty identifier with no spaces.";
        render();
        return;
      }
      if (!Number.isInteger(parsedVal)) {
        varFormError = "Initial value must be an integer.";
        render();
        return;
      }

      const existing = variables.find((v) => v.name === rawName);
      if (existing) {
        existing.value = parsedVal;
      } else {
        variables.push({ name: rawName, value: parsedVal });
      }
      newVarName = "";
      newVarValue = "0";
      varFormError = "";
      clearCrash();
      render();
    });

    // Mode toggle (Builder / Text)
    article.querySelectorAll<HTMLButtonElement>("[data-mode]").forEach((btn) => {
      btn.addEventListener("click", () => {
        const mode = btn.dataset.mode as "builder" | "text";
        if (mode === inputMode) return;
        inputMode = mode;
        if (mode === "text") {
          scheduleText = serializeSchedule(operations);
          parseErrors = [];
        }
        render();
      });
    });

    // Builder form
    const addOpForm = article.querySelector<HTMLFormElement>("[data-add-op-form]");
    if (addOpForm) {
      const kindSelect = addOpForm.querySelector<HTMLSelectElement>('select[name="opKind"]');
      const txInput = addOpForm.querySelector<HTMLInputElement>('input[name="opTx"]');
      const elemInput = addOpForm.querySelector<HTMLInputElement>('input[name="opElement"]');
      const valInput = addOpForm.querySelector<HTMLInputElement>('input[name="opValue"]');

      kindSelect?.addEventListener("change", () => {
        newOpKind = kindSelect.value as Operation["kind"];
        if (txInput) newOpTx = txInput.value;
        if (elemInput) newOpElement = elemInput.value;
        if (valInput) newOpValue = valInput.value;
        render();
      });

      addOpForm.addEventListener("submit", (e) => {
        e.preventDefault();
        const tx = (txInput?.value ?? newOpTx).trim() || "T1";
        const elem = (elemInput?.value ?? newOpElement).trim() || variables[0]?.name || "X";
        const num = Number(valInput?.value ?? newOpValue);
        newOpTx = tx;
        newOpElement = elem;
        if (valInput) newOpValue = valInput.value;

        let op: Operation;
        switch (newOpKind) {
          case "START":
            op = new StartOp(tx);
            break;
          case "READ":
            op = new ReadOp(tx, elem);
            break;
          case "WRITE":
            op = new WriteOp(tx, elem, Number.isInteger(num) ? num : 0);
            break;
          case "COMMIT":
            op = new CommitOp(tx);
            break;
          case "ABORT":
            op = new AbortOp(tx);
            break;
          case "CHECKPOINT":
            op = new CheckpointOp();
            break;
        }

        operations.push(op);
        scheduleText = serializeSchedule(operations);
        parseErrors = [];
        selectedStep = null;
        clearCrash();
        render();
      });
    }

    // Schedule row actions
    article.querySelector<HTMLButtonElement>("[data-clear-ops]")?.addEventListener("click", () => {
      operations = [];
      scheduleText = "";
      parseErrors = [];
      selectedStep = null;
      clearCrash();
      render();
    });

    article.querySelectorAll<HTMLButtonElement>("[data-remove-op]").forEach((btn) => {
      btn.addEventListener("click", (e) => {
        e.stopPropagation();
        const idx = Number(btn.dataset.removeOp);
        operations.splice(idx, 1);
        scheduleText = serializeSchedule(operations);
        selectedStep = null;
        clearCrash();
        render();
      });
    });

    article.querySelectorAll<HTMLButtonElement>("[data-move-up]").forEach((btn) => {
      btn.addEventListener("click", (e) => {
        e.stopPropagation();
        const idx = Number(btn.dataset.moveUp);
        if (idx <= 0) return;
        [operations[idx - 1], operations[idx]] = [operations[idx], operations[idx - 1]];
        scheduleText = serializeSchedule(operations);
        clearCrash();
        render();
      });
    });

    article.querySelectorAll<HTMLButtonElement>("[data-move-down]").forEach((btn) => {
      btn.addEventListener("click", (e) => {
        e.stopPropagation();
        const idx = Number(btn.dataset.moveDown);
        if (idx >= operations.length - 1) return;
        [operations[idx + 1], operations[idx]] = [operations[idx], operations[idx + 1]];
        scheduleText = serializeSchedule(operations);
        clearCrash();
        render();
      });
    });

    article.querySelectorAll<HTMLLIElement>("[data-select-step]").forEach((li) => {
      li.addEventListener("click", () => {
        selectedStep = Number(li.dataset.selectStep);
        clearCrash();
        render();
      });
    });

    // Text mode textarea
    const textarea = article.querySelector<HTMLTextAreaElement>("[data-schedule-textarea]");
    textarea?.addEventListener("input", () => {
      const selStart = textarea.selectionStart;
      const selEnd = textarea.selectionEnd;
      scheduleText = textarea.value;
      const parsed = parseScheduleText(scheduleText);
      operations = parsed.operations;
      parseErrors = parsed.parseErrors;
      selectedStep = null;
      clearCrash();
      render();
      const refreshed = article.querySelector<HTMLTextAreaElement>("[data-schedule-textarea]");
      if (refreshed) {
        refreshed.focus();
        refreshed.setSelectionRange(selStart, selEnd);
      }
    });

    // Step controls
    article.querySelector<HTMLButtonElement>("[data-step-first]")?.addEventListener("click", () => {
      selectedStep = 0;
      clearCrash();
      render();
    });
    article.querySelector<HTMLButtonElement>("[data-step-prev]")?.addEventListener("click", () => {
      selectedStep = Math.max(0, activeSnapshot.stepIndex - 1);
      clearCrash();
      render();
    });
    article.querySelector<HTMLButtonElement>("[data-step-next]")?.addEventListener("click", () => {
      selectedStep = Math.min(maxStep, activeSnapshot.stepIndex + 1);
      clearCrash();
      render();
    });
    article.querySelector<HTMLButtonElement>("[data-step-last]")?.addEventListener("click", () => {
      selectedStep = null;
      clearCrash();
      render();
    });
    article.querySelector<HTMLInputElement>("[data-step-slider]")?.addEventListener("input", (e) => {
      const target = e.target as HTMLInputElement;
      const step = Number(target.value);
      selectedStep = step === maxStep ? null : step;
      clearCrash();
      render();
    });

    // Stale disk checkbox for Redo crash simulation
    article
      .querySelector<HTMLInputElement>("[data-stale-disk]")
      ?.addEventListener("change", (e) => {
        simulateStaleDiskForRedo = (e.target as HTMLInputElement).checked;
        clearCrash();
        render();
      });

    // Crash recovery button
    article
      .querySelector<HTMLButtonElement>("[data-simulate-crash]")
      ?.addEventListener("click", () => {
        const flushedLog = activeSnapshot.log.slice(0, activeSnapshot.flushedLogLen);
        const diskBeforeCrash =
          protocol === "redo" && simulateStaleDiskForRedo
            ? buildInitialDb()
            : { ...activeSnapshot.disk };
        const recovery: RecoveryStrategy =
          protocol === "undo" ? new UndoRecoveryStrategy() : new RedoRecoveryStrategy();
        const result = recovery.recoverFromCrash(diskBeforeCrash, flushedLog);
        crashResult = {
          stepIndex: activeSnapshot.stepIndex,
          protocol,
          checkpointMode,
          diskBeforeCrash,
          flushedLog,
          result
        };
        render();
      });
  }

  render();
  return article;
}
