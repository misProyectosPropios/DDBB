// Interactive Undo Logging blog page + workbench.
// Lets users configure initial DB variables (e.g., X = 5, Y = 10), construct a
// schedule via visual builder or text input, step through execution, inspect
// the generated Undo log, execution trace, buffer vs. disk state, and simulate
// crash recovery.

import {
  AbortOp,
  CommitOp,
  ReadOp,
  Schedule,
  StartOp,
  WriteOp,
  type Operation
} from "../logging/dispatch";
import { parseScheduleText, serializeSchedule } from "../logging/parser";
import {
  formatLogRecord,
  formatTraceEvent,
  type DatabaseState,
  type LogRecord,
  type TraceEvent
} from "../logging/types";
import { UndoLogger, type UndoStepSnapshot } from "../logging/undoLogger";
import { recoverFromCrash, type RecoveryResult } from "../logging/undoRecovery";

interface DbVariable {
  name: string;
  value: number;
}

interface Preset {
  id: string;
  label: string;
  description: string;
  variables: DbVariable[];
  scheduleText: string;
}

const PRESETS: Preset[] = [
  {
    id: "xy-basic",
    label: "X=5, Y=10 (Commit & Abort)",
    description: "T1 updates X and commits; T2 updates Y and aborts.",
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
    id: "garcia-molina",
    label: "Classic T1 (A=8, B=8 → 16)",
    description: "Garcia-Molina textbook example: T1 doubles A and B then commits.",
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
  },
  {
    id: "crash-mid-tx",
    label: "Crash Mid-Transaction",
    description: "T1 commits X=50 while T2 writes Y=999 without committing yet.",
    variables: [
      { name: "X", value: 5 },
      { name: "Y", value: 10 }
    ],
    scheduleText: [
      "START T1",
      "START T2",
      "WRITE T1 X 50",
      "WRITE T2 Y 999",
      "COMMIT T1"
    ].join("\n")
  },
  {
    id: "invalid-ops",
    label: "Invalid Operations",
    description: "Demonstrates validation errors when writing before START or to unknown keys.",
    variables: [{ name: "X", value: 5 }],
    scheduleText: [
      "WRITE T1 X 20",
      "START T1",
      "WRITE T1 Z 99",
      "WRITE T1 X 15",
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
      return "badge-update";
    case "LogCommit":
      return "badge-commit";
    case "LogAbort":
      return "badge-abort";
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

export function renderUndoLoggingPage(): HTMLElement {
  const article = document.createElement("article");
  article.className = "blog-article";

  // State
  let variables: DbVariable[] = PRESETS[0].variables.map((v) => ({ ...v }));
  let operations: Operation[] = parseScheduleText(PRESETS[0].scheduleText).operations;
  let scheduleText = serializeSchedule(operations);
  let parseErrors: string[] = [];
  let inputMode: "builder" | "text" = "builder";
  let selectedStep: number | null = null; // null => follow latest step
  let crashResult: {
    stepIndex: number;
    simulatedDirtyDisk: DatabaseState;
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

  function runUndoSimulation(): {
    snapshots: readonly UndoStepSnapshot[];
    activeSnapshot: UndoStepSnapshot;
  } {
    const logger = new UndoLogger(buildInitialDb());
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

  function clearCrashIfStale(): void {
    crashResult = null;
  }

  function render(): void {
    const { snapshots, activeSnapshot } = runUndoSimulation();
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

    article.innerHTML = `
      <header class="article-header">
        <div class="breadcrumb">Logging / Undo Logging</div>
        <h1>Undo Logging</h1>
        <p class="article-lead">
          Pure (simple) Undo logging protects a database against crashes by recording the
          <strong>old value</strong> of every element before it is modified in memory, ensuring
          uncommitted writes can always be reversed.
        </p>

        <div class="callout-rules">
          <div class="rule-card">
            <span class="rule-pill">Rule U1 · WAL</span>
            <p>
              Before an updated element is written to disk (<code>OUTPUT</code>), its
              <code>&lt;T, X, oldVal&gt;</code> log record must already be flushed to disk
              (<code>FLUSH LOG</code>).
            </p>
          </div>
          <div class="rule-card">
            <span class="rule-pill">Rule U2 · Commit Order</span>
            <p>
              Before <code>&lt;COMMIT T&gt;</code> is written to the log and flushed, every
              element modified by <code>T</code> must already be written to disk
              (<code>OUTPUT</code>).
            </p>
          </div>
        </div>
      </header>

      <section class="workbench" aria-label="Interactive Undo Logging Workbench">
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
            <p class="panel-hint">Set the starting values stored on disk and in the memory buffer (e.g., <code>X = 5</code>, <code>Y = 10</code>).</p>

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
                  ${(["START", "READ", "WRITE", "COMMIT", "ABORT"] as const)
                    .map(
                      (k) =>
                        `<option value="${k}"${k === newOpKind ? " selected" : ""}>${k}</option>`
                    )
                    .join("")}
                </select>

                <input
                  type="text"
                  class="input input-sm input-tx"
                  name="opTx"
                  placeholder="Tx (e.g. T1)"
                  value="${escapeHtml(newOpTx)}"
                  aria-label="Transaction ID"
                  autocomplete="off"
                />

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
                <code>WRITE T1 X 12</code>, <code>COMMIT T1</code>, <code>ABORT T2</code>.
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
            <strong>Schedule validation errors (${activeSnapshot.errors.length}):</strong>
            <ul>
              ${activeSnapshot.errors.map((err) => `<li>${escapeHtml(err)}</li>`).join("")}
            </ul>
          </div>
        `
            : ""
        }

        <!-- Live Outputs -->
        <div class="outputs-grid">
          <!-- Undo Log -->
          <div class="panel">
            <div class="panel-header">
              <h2>Generated Undo Log</h2>
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

          <!-- Storage & Transactions State -->
          <div class="panel">
            <div class="panel-header">
              <h2>Buffer vs. Disk &amp; Transactions</h2>
              <span class="panel-meta">At step ${currentStepIdx}</span>
            </div>

            <div class="tx-status-group">
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
            <h2>Execution Trace (WAL &amp; OUTPUT Ordering)</h2>
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
              <h2>Crash Recovery Check</h2>
              <p class="panel-hint">
                Test what <code>UndoRecovery.RecoverFromCrash</code> does if the system crashes
                at <strong>step ${currentStepIdx}</strong> using only the flushed log (records #1–#${activeSnapshot.flushedLogLen}).
              </p>
            </div>
            <button type="button" class="btn btn-secondary" data-simulate-crash>
              Simulate Crash at Step ${currentStepIdx}
            </button>
          </div>

          ${
            crashResult && crashResult.stepIndex === currentStepIdx
              ? `
            <div class="recovery-result">
              <div class="recovery-col">
                <h3>Backward Scan Actions</h3>
                ${
                  crashResult.result.actions.length === 0
                    ? `<p class="panel-hint">No incomplete transactions in the flushed log — disk is already consistent.</p>`
                    : `
                  <ul class="recovery-actions">
                    ${crashResult.result.actions
                      .map((act) =>
                        act.kind === "RESTORE"
                          ? `<li>Restore <code>${escapeHtml(act.element ?? "")} := ${act.oldValue}</code> (undo uncommitted <code>${escapeHtml(act.tx)}</code>)</li>`
                          : `<li>Emit <code>&lt;ABORT ${escapeHtml(act.tx)}&gt;</code></li>`
                      )
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

  function bindEvents(activeSnapshot: UndoStepSnapshot, maxStep: number): void {
    // Presets
    article.querySelectorAll<HTMLButtonElement>("[data-preset]").forEach((btn) => {
      btn.addEventListener("click", () => {
        const preset = PRESETS.find((p) => p.id === btn.dataset.preset);
        if (!preset) return;
        variables = preset.variables.map((v) => ({ ...v }));
        const parsed = parseScheduleText(preset.scheduleText);
        operations = parsed.operations;
        scheduleText = serializeSchedule(operations);
        parseErrors = parsed.parseErrors;
        selectedStep = null;
        varFormError = "";
        newOpElement = variables[0]?.name ?? "X";
        clearCrashIfStale();
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
        clearCrashIfStale();
        render();
      });
    });

    // Remove variable
    article.querySelectorAll<HTMLButtonElement>("[data-remove-var]").forEach((btn) => {
      btn.addEventListener("click", () => {
        const idx = Number(btn.dataset.removeVar);
        variables.splice(idx, 1);
        clearCrashIfStale();
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
      clearCrashIfStale();
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
        newOpTx = txInput?.value ?? newOpTx;
        if (elemInput) newOpElement = elemInput.value;
        if (valInput) newOpValue = valInput.value;
        render();
      });

      addOpForm.addEventListener("submit", (e) => {
        e.preventDefault();
        const tx = (txInput?.value ?? "").trim() || "T1";
        const elem = (elemInput?.value ?? "").trim() || variables[0]?.name || "X";
        const num = Number(valInput?.value ?? "0");
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
        }

        operations.push(op);
        scheduleText = serializeSchedule(operations);
        parseErrors = [];
        selectedStep = null;
        clearCrashIfStale();
        render();
      });
    }

    // Schedule row actions
    article.querySelector<HTMLButtonElement>("[data-clear-ops]")?.addEventListener("click", () => {
      operations = [];
      scheduleText = "";
      parseErrors = [];
      selectedStep = null;
      clearCrashIfStale();
      render();
    });

    article.querySelectorAll<HTMLButtonElement>("[data-remove-op]").forEach((btn) => {
      btn.addEventListener("click", (e) => {
        e.stopPropagation();
        const idx = Number(btn.dataset.removeOp);
        operations.splice(idx, 1);
        scheduleText = serializeSchedule(operations);
        selectedStep = null;
        clearCrashIfStale();
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
        clearCrashIfStale();
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
        clearCrashIfStale();
        render();
      });
    });

    article.querySelectorAll<HTMLLIElement>("[data-select-step]").forEach((li) => {
      li.addEventListener("click", () => {
        selectedStep = Number(li.dataset.selectStep);
        clearCrashIfStale();
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
      clearCrashIfStale();
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
      clearCrashIfStale();
      render();
    });
    article.querySelector<HTMLButtonElement>("[data-step-prev]")?.addEventListener("click", () => {
      selectedStep = Math.max(0, activeSnapshot.stepIndex - 1);
      clearCrashIfStale();
      render();
    });
    article.querySelector<HTMLButtonElement>("[data-step-next]")?.addEventListener("click", () => {
      selectedStep = Math.min(maxStep, activeSnapshot.stepIndex + 1);
      clearCrashIfStale();
      render();
    });
    article.querySelector<HTMLButtonElement>("[data-step-last]")?.addEventListener("click", () => {
      selectedStep = null;
      clearCrashIfStale();
      render();
    });
    article.querySelector<HTMLInputElement>("[data-step-slider]")?.addEventListener("input", (e) => {
      const target = e.target as HTMLInputElement;
      const step = Number(target.value);
      selectedStep = step === maxStep ? null : step;
      clearCrashIfStale();
      render();
    });

    // Crash recovery button
    article
      .querySelector<HTMLButtonElement>("[data-simulate-crash]")
      ?.addEventListener("click", () => {
        const flushedLog = activeSnapshot.log.slice(0, activeSnapshot.flushedLogLen);
        // Recovery scans the flushed log against the current disk state.
        const simulatedDirtyDisk = { ...activeSnapshot.disk };
        const result = recoverFromCrash(simulatedDirtyDisk, flushedLog);
        crashResult = {
          stepIndex: activeSnapshot.stepIndex,
          simulatedDirtyDisk,
          flushedLog,
          result
        };
        render();
      });
  }

  render();
  return article;
}
