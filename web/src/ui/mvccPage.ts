// Interactive Isolation Levels (RC, CS, RR, SI, SerializableMVCC) &
// Multi-Version Concurrency Control (MVCC) Simulator Workbench.
//
// Mirrors `dafny/mvcc/`:
//   - `Types.dfy` (`IsolationLevel`, `TupleVersion`, `TxMeta`, `MvccState`)
//   - `IsolationPolicy.dfy` (`IsVersionVisible`, `FindLatestVisibleVersion`, `CheckWriteAllowed`, `CheckCommitAllowed`)
//   - `MvccSimulator.dfy` (`StepBegin`, `StepRead`, `StepFetchCursor`, `StepCloseCursor`, `StepWrite`, `StepCommit`, `StepAbort`)

import {
  compareAcrossIsolationLevels,
  findLatestVisibleVersion,
  formatShortLevel,
  ISOLATION_LEVELS,
  isVersionVisible,
  MVCC_PRESETS,
  parseMvccScheduleText,
  simulateMvccSchedule,
  type ElementId,
  type IsolationLevel,
  type Value
} from "../mvcc/engine";

export type MvccPageSubsection = "isolation" | "mvcc";

function escapeHtml(s: string): string {
  return s
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}

export function renderMvccPage(
  initialSubsection: MvccPageSubsection = "mvcc",
  onSubsectionChange?: (sub: MvccPageSubsection) => void
): HTMLElement {
  const article = document.createElement("article");
  article.className = "blog-article der-article";

  let subsection: MvccPageSubsection = initialSubsection;
  const initPresetIdx = initialSubsection === "isolation" ? 1 : 0;
  let activePresetId = MVCC_PRESETS[initPresetIdx].id;
  let defaultLevel: IsolationLevel = MVCC_PRESETS[initPresetIdx].defaultLevel;
  let variables: { name: ElementId; value: Value }[] = MVCC_PRESETS[
    initPresetIdx
  ].initialItems.map((v) => ({ ...v }));
  let scheduleText = MVCC_PRESETS[initPresetIdx].scheduleText;
  let selectedStep: number | null = null;
  let varFormError = "";

  let newOpKind:
    | "BEGIN"
    | "READ"
    | "FETCH_CURSOR"
    | "CLOSE_CURSOR"
    | "WRITE"
    | "COMMIT"
    | "ABORT" = "READ";
  let newOpTx = "T1";
  let newOpLevel: IsolationLevel = defaultLevel;
  let newOpElem = variables[0]?.name ?? "A";
  let newOpVal = "200";

  function forceAllBeginLevels(targetLevel: IsolationLevel): void {
    const lines = scheduleText.split(/\n/);
    const updated = lines.map((line) => {
      const m = line.match(/^\s*(BEGIN|START)\s*\(\s*([^,)\s]+)(?:\s*,\s*[^)]*)?\)\s*$/i);
      if (m) {
        return `BEGIN(${m[2].trim()}, ${formatShortLevel(targetLevel)})`;
      }
      return line;
    });
    defaultLevel = targetLevel;
    newOpLevel = targetLevel;
    scheduleText = updated.join("\n");
    selectedStep = null;
  }

  function renderHeaderHtml(): string {
    if (subsection === "isolation") {
      return `
        <header class="article-header">
          <div class="breadcrumb">Scheduler &amp; Concurrency / Isolation Levels (RC, CS, RR, SI, Serializable)</div>
          <h1>Isolation Levels (RC · CS · RR · SI · Serializable MVCC)</h1>
          <p class="article-lead">
            Formally verified in <code>dafny/mvcc/IsolationPolicy.dfy</code> &amp;
            <code>MvccSimulator.dfy</code>: compare how <strong>Read Committed (RC)</strong>,
            <strong>Cursor Stability (CS)</strong>, <strong>Repeatable Read (RR)</strong>,
            <strong>Snapshot Isolation (SI)</strong>, and
            <strong>Serializable MVCC (SSI)</strong> control version visibility, cursor pins,
            read locks, First-Committer-Wins, and Write-Skew validation on the exact same schedule.
          </p>

          <div class="callout-rules">
            <div class="rule-card">
              <span class="rule-pill">Lock/Pin Levels · RC · CS · RR</span>
              <p>
                All levels forbid Dirty Writes and Dirty Reads (<code>LemmaNoDirtyReads</code>).
                <strong>CS</strong> pins the active cursor row
                (<code>LemmaCursorPinBlocksOtherWriter</code>); <strong>RR</strong> holds read locks
                until commit (<code>LemmaRepeatableReadLockBlocksOtherWriter</code>).
              </p>
            </div>
            <div class="rule-card">
              <span class="rule-pill">Snapshot Levels · SI vs Serializable (SSI)</span>
              <p>
                <strong>SI</strong> reads a point-in-time snapshot (<code>xmin ≤ startTs</code>) without
                blocking writers and enforces <strong>First-Committer-Wins</strong>
                (<code>LemmaFirstCommitterWinsPreventsLostUpdate</code>).
                <strong>Serializable MVCC</strong> adds read-set validation at commit to reject
                <strong>Write Skew</strong> (<code>LemmaSerializablePreventsWriteSkew</code>).
              </p>
            </div>
          </div>
        </header>
      `;
    }

    return `
      <header class="article-header">
        <div class="breadcrumb">Scheduler &amp; Concurrency / MVCC Simulator</div>
        <h1>MVCC (Multi-Version Concurrency Control) Simulator</h1>
        <p class="article-lead">
          Step-by-step execution of <code>dafny/mvcc/MvccSimulator.dfy</code>: inspect the live
          <strong>multi-version tuple store</strong> (<code>TupleVersion(element, value, creatorTx, xmin, committed)</code>),
          per-transaction snapshot windows (<code>xmin ≤ startTs</code>), active
          <strong>Cursor Stability pins</strong>, <strong>Repeatable Read locks</strong>, and
          <strong>First-Committer-Wins / SSI Write-Skew</strong> commit validation.
        </p>

        <div class="callout-rules">
          <div class="rule-card">
            <span class="rule-pill">Version Visibility · IsVersionVisible(meta, v)</span>
            <p>
              A transaction always sees its own uncommitted writes (<code>v.creatorTx == tx</code>).
              For other transactions' versions, <code>v.committed</code> must hold, and under
              <strong>SI / Serializable</strong> <code>v.xmin ≤ meta.startTs</code>
              (<code>LemmaSnapshotBoundedByStartTs</code>).
            </p>
          </div>
          <div class="rule-card">
            <span class="rule-pill">Write &amp; Commit Validation · CheckWriteAllowed &amp; CheckCommitAllowed</span>
            <p>
              Writes check uncommitted write ownership, CS cursor pins, RR read locks, and SI
              First-Committer-Wins. Commits publish uncommitted versions at
              <code>xmin := commitTs</code> after validating SI/SSI conflict rules.
            </p>
          </div>
        </div>
      </header>
    `;
  }

  function renderAnomalyMatrixHtml(): string {
    return `
      <section class="panel" id="sec-isolation-matrix">
        <div class="panel-header">
          <div>
            <h2>Formal Isolation Level Rules &amp; Anomaly Prevention Matrix</h2>
            <p class="panel-hint" style="margin:0.15rem 0 0;">
              Summary of visibility, locking/pinning, and anomaly guarantees proved in
              <code>dafny/mvcc/IsolationPolicy.dfy</code> and <code>dafny/mvcc/MvccSimulator.dfy</code>.
            </p>
          </div>
        </div>

        <div class="table-scroll">
          <table class="data-table chase-table">
            <thead>
              <tr>
                <th>Isolation Level</th>
                <th>Read Visibility Rule</th>
                <th>Dirty Write &amp; Dirty Read</th>
                <th>Cursor Lost Update</th>
                <th>Non-Repeatable Read</th>
                <th>Lost Update (Write-Write)</th>
                <th>Write Skew (rw-Cycle)</th>
                <th>Verified Dafny Lemma</th>
              </tr>
            </thead>
            <tbody>
              <tr>
                <td><strong>Read Committed (RC)</strong></td>
                <td>Latest committed (<code>v.committed</code>); blocks if other uncommitted write lock</td>
                <td><span class="nf-badge nf-bcnf">PREVENTED ✓</span></td>
                <td><span class="nf-badge nf-unf">POSSIBLE ✗</span></td>
                <td><span class="nf-badge nf-unf">POSSIBLE ✗</span></td>
                <td><span class="nf-badge nf-unf">POSSIBLE ✗</span></td>
                <td><span class="nf-badge nf-unf">POSSIBLE ✗</span></td>
                <td><code>LemmaNoDirtyReads</code></td>
              </tr>
              <tr>
                <td><strong>Cursor Stability (CS)</strong></td>
                <td>Latest committed + pins currently positioned <code>cursorElem</code></td>
                <td><span class="nf-badge nf-bcnf">PREVENTED ✓</span></td>
                <td><span class="nf-badge nf-bcnf">PREVENTED ✓</span></td>
                <td><span class="nf-badge nf-unf">POSSIBLE (after move)</span></td>
                <td><span class="nf-badge nf-2nf">ON CURSOR ROW ✓</span></td>
                <td><span class="nf-badge nf-unf">POSSIBLE ✗</span></td>
                <td><code>LemmaCursorPinBlocksOtherWriter</code></td>
              </tr>
              <tr>
                <td><strong>Repeatable Read (RR)</strong></td>
                <td>Latest committed + holds persistent <code>rrReadLocks</code> until commit</td>
                <td><span class="nf-badge nf-bcnf">PREVENTED ✓</span></td>
                <td><span class="nf-badge nf-bcnf">PREVENTED ✓</span></td>
                <td><span class="nf-badge nf-bcnf">PREVENTED ✓</span></td>
                <td><span class="nf-badge nf-bcnf">PREVENTED ✓</span></td>
                <td><span class="nf-badge nf-bcnf">PREVENTED (2PL locks) ✓</span></td>
                <td><code>LemmaRepeatableReadLockBlocksOtherWriter</code></td>
              </tr>
              <tr>
                <td><strong>Snapshot Isolation (SI)</strong></td>
                <td>Point-in-time snapshot (<code>v.committed && v.xmin ≤ startTs</code>); non-blocking reads</td>
                <td><span class="nf-badge nf-bcnf">PREVENTED ✓</span></td>
                <td><span class="nf-badge nf-bcnf">PREVENTED (FCW) ✓</span></td>
                <td><span class="nf-badge nf-bcnf">PREVENTED (Snapshot) ✓</span></td>
                <td><span class="nf-badge nf-bcnf">PREVENTED (FCW) ✓</span></td>
                <td><span class="nf-badge nf-unf">POSSIBLE ✗</span></td>
                <td><code>LemmaFirstCommitterWinsPreventsLostUpdate</code></td>
              </tr>
              <tr>
                <td><strong>Serializable MVCC (SSI)</strong></td>
                <td>Point-in-time snapshot (<code>v.xmin ≤ startTs</code>) + commit readSet validation</td>
                <td><span class="nf-badge nf-bcnf">PREVENTED ✓</span></td>
                <td><span class="nf-badge nf-bcnf">PREVENTED ✓</span></td>
                <td><span class="nf-badge nf-bcnf">PREVENTED ✓</span></td>
                <td><span class="nf-badge nf-bcnf">PREVENTED ✓</span></td>
                <td><span class="nf-badge nf-bcnf">PREVENTED (SSI Abort) ✓</span></td>
                <td><code>LemmaSerializablePreventsWriteSkew</code></td>
              </tr>
            </tbody>
          </table>
        </div>
      </section>
    `;
  }

  function render(): void {
    const { ops, parseErrors } = parseMvccScheduleText(scheduleText, defaultLevel);
    const sim = simulateMvccSchedule(variables, ops);
    const comparison = compareAcrossIsolationLevels(variables, ops);

    const maxStep = sim.snapshots.length - 1;
    const clampedStep =
      selectedStep === null ? maxStep : Math.max(0, Math.min(selectedStep, maxStep));
    const activeSnap = sim.snapshots[clampedStep];
    const curState = activeSnap.state;
    const activeTxList = Object.values(curState.txs);

    article.innerHTML = `
      ${renderHeaderHtml()}

      <div class="der-workbench">
        <!-- Subsection Switcher & Preset Selector -->
        <div class="strategy-bar">
          <div class="strategy-group">
            <span class="strategy-label">Workbench Subsection</span>
            <div class="segmented" role="group" aria-label="MVCC Subsection">
              <button
                type="button"
                class="segmented-btn${subsection === "isolation" ? " is-active" : ""}"
                data-mvcc-sub="isolation"
              >Isolation Levels Comparison (RC · CS · RR · SI · SSI)</button>
              <button
                type="button"
                class="segmented-btn${subsection === "mvcc" ? " is-active" : ""}"
                data-mvcc-sub="mvcc"
              >MVCC Version-Chain Simulator</button>
            </div>
          </div>

          <div class="strategy-group">
            <span class="strategy-label">Force All Txs to Level</span>
            <div class="segmented" role="group" aria-label="Force Isolation Level">
              ${ISOLATION_LEVELS.map(
                (lvl) => `
                <button
                  type="button"
                  class="segmented-btn${defaultLevel === lvl.id ? " is-active" : ""}"
                  data-force-level="${lvl.id}"
                  title="Rewrite all BEGIN(...) operations to ${escapeHtml(lvl.fullLabel)}"
                >${escapeHtml(lvl.shortLabel)}</button>
              `
              ).join("")}
            </div>
          </div>
        </div>

        ${subsection === "isolation" ? renderAnomalyMatrixHtml() : ""}

        <!-- Schedule & Initial Elements Builder -->
        <section class="panel">
          <div class="panel-header">
            <div>
              <h2>MVCC Schedule &amp; Initial Database Tuple Store</h2>
              <p class="panel-hint" style="margin:0.15rem 0 0;">
                Operations: <code>BEGIN(T1, SI)</code> (or <code>RC</code>, <code>CS</code>,
                <code>RR</code>, <code>SSI</code>), <code>READ(T1, A)</code>,
                <code>FETCH_CURSOR(T1, A)</code>, <code>CLOSE_CURSOR(T1)</code>,
                <code>WRITE(T1, A, 200)</code>, <code>COMMIT(T1)</code>, <code>ABORT(T1)</code>.
              </p>
            </div>
          </div>

          <div class="presets-bar" style="margin-bottom:0.8rem;">
            <span class="presets-label">Verified Scenarios:</span>
            <div class="presets-list">
              ${MVCC_PRESETS.map(
                (p) => `
                <button
                  type="button"
                  class="btn btn-chip ${p.id === activePresetId ? "is-active-chip" : ""}"
                  data-mvcc-preset="${p.id}"
                  title="${escapeHtml(p.description)}"
                >${escapeHtml(p.title)}</button>
              `
              ).join("")}
            </div>
          </div>

          <div class="der-norm-two-col">
            <!-- Left: Initial Database Elements + Quick Operation Appender -->
            <div class="der-subpanel">
              <div class="der-sub-header">
                <h3>1. Initial Committed Tuples (xmin = 0, creator = INIT)</h3>
              </div>
              <div class="var-list" style="margin-bottom:0.65rem;">
                ${
                  variables.length === 0
                    ? `<div class="empty-inline">No elements defined. Add one below.</div>`
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
                        data-mvcc-var-idx="${idx}"
                      />
                      <button
                        type="button"
                        class="icon-btn"
                        data-mvcc-remove-var="${idx}"
                        title="Remove ${escapeHtml(v.name)}"
                      >×</button>
                    </div>
                  `
                        )
                        .join("")
                }
              </div>

              <form class="inline-form" id="mvcc-add-var-form" style="margin-bottom:1rem;">
                <input
                  type="text"
                  class="input input-sm"
                  name="varName"
                  placeholder="Elem (e.g. C)"
                  style="width:110px;"
                  autocomplete="off"
                />
                <input
                  type="number"
                  step="1"
                  class="input input-sm input-num"
                  name="varValue"
                  placeholder="Value"
                  value="0"
                />
                <button type="submit" class="btn btn-secondary btn-sm">+ Add Tuple</button>
              </form>
              ${varFormError ? `<div class="inline-error">${escapeHtml(varFormError)}</div>` : ""}

              <div class="der-sub-header" style="margin-top:0.5rem;">
                <h3>2. Quick MVCC Operation Appender</h3>
              </div>
              <form class="inline-form" id="mvcc-add-op-form">
                <select class="input input-sm" id="mvcc-op-kind">
                  ${(
                    [
                      "BEGIN",
                      "READ",
                      "FETCH_CURSOR",
                      "CLOSE_CURSOR",
                      "WRITE",
                      "COMMIT",
                      "ABORT"
                    ] as const
                  )
                    .map(
                      (k) =>
                        `<option value="${k}"${k === newOpKind ? " selected" : ""}>${k}</option>`
                    )
                    .join("")}
                </select>
                <input
                  type="text"
                  class="input input-sm"
                  id="mvcc-op-tx"
                  value="${escapeHtml(newOpTx)}"
                  style="width:66px;"
                  placeholder="T1"
                />
                ${
                  newOpKind === "BEGIN"
                    ? `
                  <select class="input input-sm" id="mvcc-op-level">
                    ${ISOLATION_LEVELS.map(
                      (lvl) =>
                        `<option value="${lvl.id}"${
                          lvl.id === newOpLevel ? " selected" : ""
                        }>${escapeHtml(lvl.shortLabel)}</option>`
                    ).join("")}
                  </select>
                `
                    : ""
                }
                ${
                  newOpKind === "READ" ||
                  newOpKind === "FETCH_CURSOR" ||
                  newOpKind === "WRITE"
                    ? `
                  <input
                    type="text"
                    class="input input-sm"
                    id="mvcc-op-elem"
                    value="${escapeHtml(newOpElem)}"
                    style="width:66px;"
                    placeholder="A"
                  />
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
                    id="mvcc-op-val"
                    value="${escapeHtml(newOpVal)}"
                    placeholder="200"
                  />
                `
                    : ""
                }
                <button type="submit" class="btn btn-primary btn-sm">+ Append</button>
              </form>
            </div>

            <!-- Right: Schedule Textarea -->
            <div>
              <label class="der-field-label">MVCC Schedule Operations (one per line)</label>
              <textarea
                id="mvcc-schedule-textarea"
                class="schedule-textarea"
                rows="9"
                spellcheck="false"
              >${escapeHtml(scheduleText)}</textarea>
              ${
                parseErrors.length > 0
                  ? `<div class="error-box" style="margin-top:0.5rem;">
                      <strong>Schedule syntax errors:</strong>
                      <ul>${parseErrors.map((e) => `<li>${escapeHtml(e)}</li>`).join("")}</ul>
                    </div>`
                  : ""
              }
            </div>
          </div>
        </section>

        <!-- Side-by-Side 5-Isolation-Level Schedule Comparison Table -->
        <section class="panel" id="sec-isolation-comparison">
          <div class="panel-header">
            <div>
              <h2>Side-by-Side Schedule Comparison Across All 5 Isolation Levels</h2>
              <p class="panel-hint" style="margin:0.15rem 0 0;">
                Runs the current schedule with all transactions forced to <strong>RC</strong>,
                <strong>CS</strong>, <strong>RR</strong>, <strong>SI</strong>, and
                <strong>Serializable (SSI)</strong> so you can compare read values, blocks, and
                commit-time aborts step by step. Click any column header to load that level into the
                MVCC simulator below.
              </p>
            </div>
          </div>

          <div class="table-scroll">
            <table class="data-table chase-table">
              <thead>
                <tr>
                  <th>Step &amp; Operation</th>
                  ${ISOLATION_LEVELS.map((lvl) => {
                    const stat = comparison[lvl.id];
                    return `
                      <th>
                        <div style="display:flex;align-items:center;justify-content:space-between;gap:0.4rem;">
                          <span>${escapeHtml(lvl.fullLabel)}</span>
                          <button
                            type="button"
                            class="btn btn-secondary btn-sm"
                            style="padding:0.15rem 0.45rem;font-size:0.7rem;"
                            data-force-level="${lvl.id}"
                          >Simulate ${escapeHtml(lvl.shortLabel)} ↓</button>
                        </div>
                        <div style="font-weight:500;font-size:0.72rem;color:var(--text-muted);margin-top:0.15rem;">
                          ${
                            stat.blockedOrRejectedCount === 0
                              ? "All steps allowed ✓"
                              : `${stat.blockedOrRejectedCount} step(s) blocked/aborted ✗`
                          }
                        </div>
                      </th>
                    `;
                  }).join("")}
                </tr>
              </thead>
              <tbody>
                ${
                  ops.length === 0
                    ? `<tr><td colspan="6" class="empty-inline">Add MVCC operations above to compare across isolation levels.</td></tr>`
                    : ops
                        .map((op, idx) => {
                          return `
                    <tr>
                      <td><code>#${idx + 1} <strong>${escapeHtml(op.raw)}</strong></code></td>
                      ${ISOLATION_LEVELS.map((lvl) => {
                        const r = comparison[lvl.id].results[idx];
                        if (!r) return `<td>—</td>`;
                        const valBadge =
                          r.readValue !== null
                            ? ` <code><strong>⇒ ${r.readValue}</strong></code> (v#${r.readVersion?.versionId}, xmin=${r.readVersion?.xmin})`
                            : "";
                        return `
                          <td class="${r.allowed ? "" : "chase-cell-sub"}">
                            <span class="nf-badge ${r.allowed ? "nf-bcnf" : "nf-unf"}">
                              ${r.allowed ? "OK ✓" : "BLOCKED / ABORT ✗"}
                            </span>
                            ${valBadge}
                            <div style="font-size:0.73rem;color:var(--text-muted);margin-top:0.2rem;">
                              ${escapeHtml(r.reason)}
                            </div>
                          </td>
                        `;
                      }).join("")}
                    </tr>
                  `;
                        })
                        .join("")
                }
              </tbody>
            </table>
          </div>
        </section>

        <!-- Step Controls Bar for MVCC State Inspection -->
        <div class="step-bar" id="sec-mvcc-simulator">
          <div class="step-bar-info">
            <span class="step-badge">Step ${activeSnap.stepIndex} / ${maxStep}</span>
            <span class="step-label">${escapeHtml(activeSnap.label)}</span>
            <span class="panel-meta" style="margin-left:0.5rem;">Logical Clock: <code>ts = ${curState.clock}</code></span>
          </div>
          <div class="step-bar-controls">
            <button type="button" class="btn btn-secondary btn-sm" data-mvcc-first ${activeSnap.stepIndex === 0 ? "disabled" : ""}>⏮ Start</button>
            <button type="button" class="btn btn-secondary btn-sm" data-mvcc-prev ${activeSnap.stepIndex === 0 ? "disabled" : ""}>← Prev</button>
            <input
              type="range"
              min="0"
              max="${maxStep}"
              value="${activeSnap.stepIndex}"
              class="step-slider"
              data-mvcc-slider
              aria-label="MVCC execution step"
            />
            <button type="button" class="btn btn-secondary btn-sm" data-mvcc-next ${activeSnap.stepIndex === maxStep ? "disabled" : ""}>Next →</button>
            <button type="button" class="btn btn-secondary btn-sm" data-mvcc-last ${activeSnap.stepIndex === maxStep ? "disabled" : ""}>End ⏭</button>
          </div>
        </div>

        ${
          activeSnap.result
            ? `
          <div class="${activeSnap.result.allowed ? "der-ok-banner" : "error-box"}">
            <strong>Step #${activeSnap.stepIndex} (<code>${escapeHtml(
              activeSnap.result.op.raw
            )}</code>) — ${activeSnap.result.allowed ? "ALLOWED ✓" : "BLOCKED / REJECTED ✗"}:</strong>
            ${escapeHtml(activeSnap.result.reason)}
          </div>
        `
            : ""
        }

        <!-- Live MVCC Version Store & Transaction / Lock State -->
        <div class="der-norm-two-col">
          <!-- Multi-Version Tuple Store (state.versions) -->
          <section class="panel">
            <div class="panel-header">
              <div>
                <h2>Multi-Version Tuple Store (<code>state.versions</code>)</h2>
                <p class="panel-hint" style="margin:0.15rem 0 0;">
                  Each write appends an immutable <code>TupleVersion(element, value, creatorTx, xmin, committed)</code>.
                  Badges indicate which active transactions can see each version
                  (<code>IsVersionVisible</code>) and which version is selected by
                  <code>FindLatestVisibleVersion</code>.
                </p>
              </div>
              <span class="panel-meta">${curState.versions.length} version(s)</span>
            </div>

            <div class="table-scroll">
              <table class="data-table chase-table">
                <thead>
                  <tr>
                    <th>Ver</th>
                    <th>Element</th>
                    <th>Value</th>
                    <th>Creator</th>
                    <th>xmin (TS)</th>
                    <th>Status</th>
                    <th>Visible To Active Txs</th>
                  </tr>
                </thead>
                <tbody>
                  ${curState.versions
                    .map((ver) => {
                      const activeVisible = activeTxList
                        .filter((txMeta) => txMeta.status === "TxActive" && isVersionVisible(txMeta, ver))
                        .map((txMeta) => {
                          const latest = findLatestVisibleVersion(
                            curState.versions,
                            txMeta,
                            ver.element
                          );
                          const isSelected = latest?.versionId === ver.versionId;
                          return `<span class="nf-badge ${
                            isSelected ? "nf-bcnf" : "nf-2nf"
                          }" title="${
                            isSelected
                              ? `Latest visible version of ${ver.element} for ${txMeta.tx}`
                              : `Visible to ${txMeta.tx}, but superseded by a newer visible version`
                          }">${escapeHtml(txMeta.tx)}${isSelected ? " ★" : ""}</span>`;
                        });

                      return `
                        <tr class="${ver.committed ? "" : "row-dirty"}">
                          <td><code>v#${ver.versionId}</code></td>
                          <td><code><strong>${escapeHtml(ver.element)}</strong></code></td>
                          <td><code><strong>${ver.value}</strong></code></td>
                          <td><code>${escapeHtml(ver.creatorTx)}</code></td>
                          <td><code>${ver.xmin}</code></td>
                          <td>
                            <span class="nf-badge ${ver.committed ? "nf-bcnf" : "nf-1nf"}">
                              ${ver.committed ? "COMMITTED" : "UNCOMMITTED"}
                            </span>
                          </td>
                          <td>${activeVisible.length > 0 ? activeVisible.join(" ") : `<span class="panel-meta">—</span>`}</td>
                        </tr>
                      `;
                    })
                    .join("")}
                </tbody>
              </table>
            </div>
          </section>

          <!-- Active Transactions, Snapshots, Cursor Pins & Read/Write Locks -->
          <section class="panel">
            <div class="panel-header">
              <div>
                <h2>Transactions (<code>state.txs</code>) &amp; Locks / Cursor Pins</h2>
                <p class="panel-hint" style="margin:0.15rem 0 0;">
                  Tracks each transaction's <code>IsolationLevel</code>, snapshot
                  <code>startTs</code>, <code>commitTs</code>, <code>cursorElem</code> pin,
                  <code>readSet</code>, and <code>writeSet</code>.
                </p>
              </div>
              <span class="panel-meta">Clock = ${curState.clock}</span>
            </div>

            <div class="tx-status-group" style="margin-bottom:0.75rem;">
              <div class="tx-bucket">
                <span class="tx-bucket-label">Uncommitted Write Owners</span>
                <code>${escapeHtml(
                  Object.entries(curState.writeOwners)
                    .map(([el, t]) => `${el}→${t}`)
                    .join(", ") || "∅"
                )}</code>
              </div>
              <div class="tx-bucket">
                <span class="tx-bucket-label">CS Cursor Pins</span>
                <code>${escapeHtml(
                  Object.entries(curState.csCursorPins)
                    .map(([el, holders]) => `${el}:{${holders.join(",")}}`)
                    .join(", ") || "∅"
                )}</code>
              </div>
              <div class="tx-bucket">
                <span class="tx-bucket-label">RR Read Locks</span>
                <code>${escapeHtml(
                  Object.entries(curState.rrReadLocks)
                    .map(([el, holders]) => `${el}:{${holders.join(",")}}`)
                    .join(", ") || "∅"
                )}</code>
              </div>
            </div>

            <div class="table-scroll">
              <table class="data-table chase-table">
                <thead>
                  <tr>
                    <th>Tx</th>
                    <th>Level</th>
                    <th>Status</th>
                    <th>startTs</th>
                    <th>commitTs</th>
                    <th>Cursor Pin</th>
                    <th>ReadSet</th>
                    <th>WriteSet</th>
                  </tr>
                </thead>
                <tbody>
                  ${
                    activeTxList.length === 0
                      ? `<tr><td colspan="8" class="empty-inline">No transactions started at step ${activeSnap.stepIndex}.</td></tr>`
                      : activeTxList
                          .map((meta) => {
                            const statusBadge =
                              meta.status === "TxCommitted"
                                ? "nf-bcnf"
                                : meta.status === "TxAborted"
                                  ? "nf-unf"
                                  : "nf-3nf";
                            const statusLabel =
                              meta.status === "TxCommitted"
                                ? "COMMITTED"
                                : meta.status === "TxAborted"
                                  ? "ABORTED"
                                  : "ACTIVE";
                            return `
                        <tr>
                          <td><strong>${escapeHtml(meta.tx)}</strong></td>
                          <td><code>${escapeHtml(formatShortLevel(meta.level))}</code></td>
                          <td><span class="nf-badge ${statusBadge}">${statusLabel}</span></td>
                          <td><code>${meta.startTs}</code></td>
                          <td><code>${meta.commitTs > 0 ? meta.commitTs : "—"}</code></td>
                          <td><code>${escapeHtml(meta.cursorElem ?? "—")}</code></td>
                          <td><code>{${escapeHtml(meta.readSet.join(", "))}}</code></td>
                          <td><code>{${escapeHtml(meta.writeSet.join(", "))}}</code></td>
                        </tr>
                      `;
                          })
                          .join("")
                  }
                </tbody>
              </table>
            </div>
          </section>
        </div>

        <!-- Chronological MVCC Execution Trace -->
        <section class="panel">
          <div class="panel-header">
            <div>
              <h2>Chronological MVCC Execution &amp; Conflict Trace</h2>
              <p class="panel-hint" style="margin:0.15rem 0 0;">
                Click any row to jump the MVCC state inspector to that step.
              </p>
            </div>
            <span class="panel-meta">${sim.results.length} operation(s)</span>
          </div>

          <div class="table-scroll">
            <table class="data-table chase-table">
              <thead>
                <tr>
                  <th>Step</th>
                  <th>Operation</th>
                  <th>Verdict</th>
                  <th>Read Value / Version</th>
                  <th>Clock After</th>
                  <th>Formal Policy Explanation</th>
                </tr>
              </thead>
              <tbody>
                ${
                  sim.results.length === 0
                    ? `<tr><td colspan="6" class="empty-inline">No operations in schedule.</td></tr>`
                    : sim.results
                        .map((res) => {
                          const isCurrent = res.stepIndex === activeSnap.stepIndex;
                          const verDesc =
                            res.readValue !== null && res.readVersion
                              ? `${res.readValue} (v#${res.readVersion.versionId}, creator=${res.readVersion.creatorTx}, xmin=${res.readVersion.xmin})`
                              : res.readVersion
                                ? `v#${res.readVersion.versionId} (${res.readVersion.element}:=${res.readVersion.value}, uncommitted)`
                                : "—";
                          return `
                      <tr
                        class="${res.allowed ? "" : "row-error"}${isCurrent ? " is-current" : ""}"
                        style="cursor:pointer;${isCurrent ? "outline:2px solid var(--accent);" : ""}"
                        data-mvcc-jump-step="${res.stepIndex}"
                      >
                        <td><code>#${res.stepIndex}</code></td>
                        <td><code><strong>${escapeHtml(res.op.raw)}</strong></code></td>
                        <td>
                          <span class="nf-badge ${res.allowed ? "nf-bcnf" : "nf-unf"}">
                            ${res.allowed ? "ALLOWED ✓" : "BLOCKED / REJECTED ✗"}
                          </span>
                        </td>
                        <td><code>${escapeHtml(verDesc)}</code></td>
                        <td><code>ts=${res.nextState.clock}</code></td>
                        <td>${escapeHtml(res.reason)}</td>
                      </tr>
                    `;
                        })
                        .join("")
                }
              </tbody>
            </table>
          </div>
        </section>
      </div>
    `;

    bindEvents(maxStep, activeSnap.stepIndex);
  }

  function bindEvents(maxStep: number, currentStepIdx: number): void {
    // Subsection toggle
    article.querySelectorAll<HTMLButtonElement>("[data-mvcc-sub]").forEach((btn) => {
      btn.addEventListener("click", () => {
        const next = btn.dataset.mvccSub as MvccPageSubsection;
        if (next === subsection) return;
        subsection = next;
        onSubsectionChange?.(next);
        render();
      });
    });

    // Force all transactions to a selected isolation level
    article.querySelectorAll<HTMLButtonElement>("[data-force-level]").forEach((btn) => {
      btn.addEventListener("click", () => {
        const lvl = btn.dataset.forceLevel as IsolationLevel;
        forceAllBeginLevels(lvl);
        activePresetId = "";
        render();
      });
    });

    // Presets
    article.querySelectorAll<HTMLButtonElement>("[data-mvcc-preset]").forEach((btn) => {
      btn.addEventListener("click", () => {
        const found = MVCC_PRESETS.find((p) => p.id === btn.dataset.mvccPreset);
        if (!found) return;
        activePresetId = found.id;
        defaultLevel = found.defaultLevel;
        newOpLevel = found.defaultLevel;
        variables = found.initialItems.map((v) => ({ ...v }));
        newOpElem = variables[0]?.name ?? "A";
        scheduleText = found.scheduleText;
        selectedStep = null;
        varFormError = "";
        render();
      });
    });

    // Edit variable values
    article.querySelectorAll<HTMLInputElement>("[data-mvcc-var-idx]").forEach((input) => {
      input.addEventListener("change", () => {
        const idx = Number(input.dataset.mvccVarIdx);
        const val = Number(input.value);
        if (!Number.isInteger(val)) {
          input.value = String(variables[idx].value);
          return;
        }
        variables[idx].value = val;
        render();
      });
    });

    // Remove variable
    article.querySelectorAll<HTMLButtonElement>("[data-mvcc-remove-var]").forEach((btn) => {
      btn.addEventListener("click", () => {
        const idx = Number(btn.dataset.mvccRemoveVar);
        variables.splice(idx, 1);
        render();
      });
    });

    // Add variable form
    const addVarForm = article.querySelector<HTMLFormElement>("#mvcc-add-var-form");
    addVarForm?.addEventListener("submit", (e) => {
      e.preventDefault();
      const fd = new FormData(addVarForm);
      const rawName = String(fd.get("varName") ?? "").trim();
      const parsedVal = Number(String(fd.get("varValue") ?? "0").trim());
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
      varFormError = "";
      render();
    });

    // Quick op form
    const addOpForm = article.querySelector<HTMLFormElement>("#mvcc-add-op-form");
    if (addOpForm) {
      const kindSel = addOpForm.querySelector<HTMLSelectElement>("#mvcc-op-kind");
      const txInput = addOpForm.querySelector<HTMLInputElement>("#mvcc-op-tx");
      const lvlSel = addOpForm.querySelector<HTMLSelectElement>("#mvcc-op-level");
      const elemInput = addOpForm.querySelector<HTMLInputElement>("#mvcc-op-elem");
      const valInput = addOpForm.querySelector<HTMLInputElement>("#mvcc-op-val");

      kindSel?.addEventListener("change", () => {
        newOpKind = kindSel.value as typeof newOpKind;
        if (txInput) newOpTx = txInput.value;
        if (lvlSel) newOpLevel = lvlSel.value as IsolationLevel;
        if (elemInput) newOpElem = elemInput.value;
        if (valInput) newOpVal = valInput.value;
        render();
      });

      addOpForm.addEventListener("submit", (e) => {
        e.preventDefault();
        const tx = (txInput?.value ?? newOpTx).trim() || "T1";
        const elem = (elemInput?.value ?? newOpElem).trim() || variables[0]?.name || "A";
        const lvl = (lvlSel?.value as IsolationLevel) ?? newOpLevel;
        const num = Number(valInput?.value ?? newOpVal);
        newOpTx = tx;
        newOpElem = elem;
        newOpLevel = lvl;
        if (valInput) newOpVal = valInput.value;

        let line = "";
        switch (newOpKind) {
          case "BEGIN":
            line = `BEGIN(${tx}, ${formatShortLevel(lvl)})`;
            break;
          case "READ":
            line = `READ(${tx}, ${elem})`;
            break;
          case "FETCH_CURSOR":
            line = `FETCH_CURSOR(${tx}, ${elem})`;
            break;
          case "CLOSE_CURSOR":
            line = `CLOSE_CURSOR(${tx})`;
            break;
          case "WRITE":
            line = `WRITE(${tx}, ${elem}, ${Number.isInteger(num) ? num : 0})`;
            break;
          case "COMMIT":
            line = `COMMIT(${tx})`;
            break;
          case "ABORT":
            line = `ABORT(${tx})`;
            break;
        }
        scheduleText = scheduleText.trim() ? `${scheduleText.trim()}\n${line}` : line;
        activePresetId = "";
        selectedStep = null;
        render();
      });
    }

    // Schedule textarea
    const textarea = article.querySelector<HTMLTextAreaElement>("#mvcc-schedule-textarea");
    textarea?.addEventListener("input", () => {
      const selStart = textarea.selectionStart;
      const selEnd = textarea.selectionEnd;
      scheduleText = textarea.value;
      activePresetId = "";
      selectedStep = null;
      render();
      const refreshed = article.querySelector<HTMLTextAreaElement>("#mvcc-schedule-textarea");
      if (refreshed) {
        refreshed.focus();
        refreshed.setSelectionRange(selStart, selEnd);
      }
    });

    // Step controls
    article.querySelector<HTMLButtonElement>("[data-mvcc-first]")?.addEventListener("click", () => {
      selectedStep = 0;
      render();
    });
    article.querySelector<HTMLButtonElement>("[data-mvcc-prev]")?.addEventListener("click", () => {
      selectedStep = Math.max(0, currentStepIdx - 1);
      render();
    });
    article.querySelector<HTMLButtonElement>("[data-mvcc-next]")?.addEventListener("click", () => {
      selectedStep = Math.min(maxStep, currentStepIdx + 1);
      render();
    });
    article.querySelector<HTMLButtonElement>("[data-mvcc-last]")?.addEventListener("click", () => {
      selectedStep = null;
      render();
    });
    article.querySelector<HTMLInputElement>("[data-mvcc-slider]")?.addEventListener("input", (e) => {
      const step = Number((e.target as HTMLInputElement).value);
      selectedStep = step === maxStep ? null : step;
      render();
    });

    article.querySelectorAll<HTMLElement>("[data-mvcc-jump-step]").forEach((row) => {
      row.addEventListener("click", () => {
        selectedStep = Number(row.dataset.mvccJumpStep);
        render();
      });
    });
  }

  render();
  return article;
}
