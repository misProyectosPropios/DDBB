// Interactive Scheduler, Conflict Serializability, Precedence / Dependency
// Graph Visualizer, Deadlock Visualizer (Wait-For Graph, Wait-Die, Wound-Wait),
// and Optimistic (Kung-Robinson OCC) vs Pessimistic (2PL) Concurrency Control
// Workbench.
//
// Mirrors `dafny/scheduler/`:
//   - `LockPolicy.dfy` (`SimpleBinaryLockPolicy`, `MultipleLockPolicy`, `TernaryLockPolicy` S/U/X)
//   - `Serializability.dfy` & `DependencyGraph.dfy`
//   - `PessimisticScheduler.dfy`
//   - `DeadlockAndOCC.dfy`

import {
  buildPrecedenceGraph,
  parseScheduleText,
  runPessimisticScheduler,
  SCHEDULER_PRESETS,
  simulateDeadlockAndWaitFor,
  validateOccFromSchedule,
  type DeadlockPolicyKind,
  type LockPolicyKind
} from "../scheduler/engine";

export type SchedulerFocusSection =
  | "serializability"
  | "graphs"
  | "deadlocks"
  | "concurrency";

const SVG_NS = "http://www.w3.org/2000/svg";

function escapeHtml(s: string): string {
  return s
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}

// Renders a directed graph (Precedence Graph or Wait-For Graph) as an SVG diagram.
function renderDirectedGraphSvg(
  nodes: string[],
  edges: { from: string; to: string; label: string; isCycleEdge?: boolean }[],
  cycleNodes: string[],
  emptyText: string
): SVGSVGElement {
  const svg = document.createElementNS(SVG_NS, "svg");
  svg.setAttribute("viewBox", "0 0 540 270");
  svg.setAttribute("class", "sched-graph-svg");

  const defs = document.createElementNS(SVG_NS, "defs");
  defs.innerHTML = `
    <marker id="sched-arrow-normal" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6.5" markerHeight="6.5" orient="auto-start-reverse">
      <path d="M 0 1 L 10 5 L 0 9 z" fill="#2563eb" />
    </marker>
    <marker id="sched-arrow-cycle" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6.5" markerHeight="6.5" orient="auto-start-reverse">
      <path d="M 0 1 L 10 5 L 0 9 z" fill="#be123c" />
    </marker>
  `;
  svg.appendChild(defs);

  if (nodes.length === 0) {
    const txt = document.createElementNS(SVG_NS, "text");
    txt.setAttribute("x", "270");
    txt.setAttribute("y", "135");
    txt.setAttribute("text-anchor", "middle");
    txt.setAttribute("fill", "#94a3b8");
    txt.setAttribute("font-size", "13");
    txt.textContent = emptyText;
    svg.appendChild(txt);
    return svg;
  }

  const cx = 270;
  const cy = 135;
  const radius = nodes.length === 1 ? 0 : nodes.length === 2 ? 125 : 95;
  const nodePos = new Map<string, { x: number; y: number }>();

  nodes.forEach((n, idx) => {
    const angle = -Math.PI / 2 + (2 * Math.PI * idx) / nodes.length;
    const x =
      nodes.length === 2
        ? idx === 0
          ? cx - radius
          : cx + radius
        : Math.round(cx + radius * Math.cos(angle));
    const y =
      nodes.length === 2 ? cy : Math.round(cy + radius * Math.sin(angle));
    nodePos.set(n, { x, y });
  });

  // Deduplicate parallel edges by combining labels
  const groupedEdges = new Map<
    string,
    { from: string; to: string; labels: string[]; isCycleEdge: boolean }
  >();
  for (const e of edges) {
    const key = `${e.from}->${e.to}`;
    const existing = groupedEdges.get(key);
    if (existing) {
      if (!existing.labels.includes(e.label)) {
        existing.labels.push(e.label);
      }
      existing.isCycleEdge = existing.isCycleEdge || Boolean(e.isCycleEdge);
    } else {
      groupedEdges.set(key, {
        from: e.from,
        to: e.to,
        labels: [e.label],
        isCycleEdge: Boolean(e.isCycleEdge)
      });
    }
  }

  const nodeRadius = 26;

  // Render directed edges (curved if bidirectional)
  for (const ge of groupedEdges.values()) {
    const p1 = nodePos.get(ge.from);
    const p2 = nodePos.get(ge.to);
    if (!p1 || !p2) continue;

    const hasReverse = groupedEdges.has(`${ge.to}->${ge.from}`);
    const dx = p2.x - p1.x;
    const dy = p2.y - p1.y;
    const dist = Math.max(1, Math.hypot(dx, dy));
    const ux = dx / dist;
    const uy = dy / dist;
    const nx = -uy;
    const ny = ux;

    const curveOffset = hasReverse ? 24 : 0;
    const startX = p1.x + ux * nodeRadius + nx * (curveOffset * 0.35);
    const startY = p1.y + uy * nodeRadius + ny * (curveOffset * 0.35);
    const endX = p2.x - ux * (nodeRadius + 4) + nx * (curveOffset * 0.35);
    const endY = p2.y - uy * (nodeRadius + 4) + ny * (curveOffset * 0.35);
    const ctrlX = (p1.x + p2.x) / 2 + nx * curveOffset;
    const ctrlY = (p1.y + p2.y) / 2 + ny * curveOffset;

    const path = document.createElementNS(SVG_NS, "path");
    path.setAttribute(
      "d",
      `M ${startX} ${startY} Q ${ctrlX} ${ctrlY} ${endX} ${endY}`
    );
    path.setAttribute("fill", "none");
    path.setAttribute("stroke", ge.isCycleEdge ? "#be123c" : "#2563eb");
    path.setAttribute("stroke-width", ge.isCycleEdge ? "2.6" : "2.1");
    path.setAttribute(
      "marker-end",
      ge.isCycleEdge ? "url(#sched-arrow-cycle)" : "url(#sched-arrow-normal)"
    );
    svg.appendChild(path);

    const labelText = ge.labels.join(", ");
    const lx = Math.round((p1.x + p2.x) / 2 + nx * (curveOffset * 0.85));
    const ly = Math.round(
      (p1.y + p2.y) / 2 + ny * (curveOffset * 0.85) - (hasReverse ? 0 : 8)
    );
    const pillW = Math.max(44, labelText.length * 6.5 + 14);

    const bg = document.createElementNS(SVG_NS, "rect");
    bg.setAttribute("x", String(lx - pillW / 2));
    bg.setAttribute("y", String(ly - 10));
    bg.setAttribute("width", String(pillW));
    bg.setAttribute("height", "18");
    bg.setAttribute("rx", "5");
    bg.setAttribute("fill", ge.isCycleEdge ? "#fff1f2" : "#eff6ff");
    bg.setAttribute("stroke", ge.isCycleEdge ? "#fda4af" : "#bfdbfe");
    svg.appendChild(bg);

    const txt = document.createElementNS(SVG_NS, "text");
    txt.setAttribute("x", String(lx));
    txt.setAttribute("y", String(ly + 3));
    txt.setAttribute("text-anchor", "middle");
    txt.setAttribute("font-size", "10.5");
    txt.setAttribute("font-weight", "700");
    txt.setAttribute("fill", ge.isCycleEdge ? "#be123c" : "#1d4ed8");
    txt.textContent = labelText;
    svg.appendChild(txt);
  }

  // Render transaction nodes
  for (const n of nodes) {
    const pos = nodePos.get(n)!;
    const inCycle = cycleNodes.includes(n);

    const circle = document.createElementNS(SVG_NS, "circle");
    circle.setAttribute("cx", String(pos.x));
    circle.setAttribute("cy", String(pos.y));
    circle.setAttribute("r", String(nodeRadius));
    circle.setAttribute("fill", inCycle ? "#fff1f2" : "#ffffff");
    circle.setAttribute("stroke", inCycle ? "#be123c" : "#0f172a");
    circle.setAttribute("stroke-width", inCycle ? "2.8" : "2.2");
    svg.appendChild(circle);

    const label = document.createElementNS(SVG_NS, "text");
    label.setAttribute("x", String(pos.x));
    label.setAttribute("y", String(pos.y + 4.5));
    label.setAttribute("text-anchor", "middle");
    label.setAttribute("font-size", "13.5");
    label.setAttribute("font-weight", "800");
    label.setAttribute("fill", inCycle ? "#be123c" : "#0f172a");
    label.textContent = n;
    svg.appendChild(label);
  }

  return svg;
}

export function renderSchedulerPage(
  initialFocus: SchedulerFocusSection = "serializability"
): HTMLElement {
  const article = document.createElement("article");
  article.className = "blog-article der-article";

  const initialPresetIdx =
    initialFocus === "deadlocks"
      ? 2
      : initialFocus === "graphs" || initialFocus === "concurrency"
        ? 0
        : 0;

  let activePresetId = SCHEDULER_PRESETS[initialPresetIdx].id;
  let lockPolicy: LockPolicyKind = SCHEDULER_PRESETS[initialPresetIdx].policy;
  let deadlockPolicy: DeadlockPolicyKind = "detect";
  let scheduleText = SCHEDULER_PRESETS[initialPresetIdx].scheduleText;

  article.innerHTML = `
    <header class="article-header">
      <div class="breadcrumb">DDBB Notes / Scheduler &amp; Concurrency</div>
      <h1>Scheduler, Dependency Graphs, Deadlocks &amp; Pessimistic / Optimistic Control</h1>
      <p class="article-lead">
        Interactive simulation of formally verified specifications in
        <code>dafny/scheduler/</code>: test <strong>2PL Lock Policies</strong>
        (Simple Binary <code>L</code>, Multiple <code>S/X</code>, and Ternary
        <code>S/U/X</code> with asymmetric <code>U → X</code> upgrades), build
        <strong>Precedence / Dependency Graphs</strong> for conflict serializability,
        detect and prevent deadlocks with <strong>Wait-For Graphs, Wait-Die &amp; Wound-Wait</strong>,
        and compare <strong>Pessimistic (2PL)</strong> against
        <strong>Optimistic (Kung–Robinson OCC)</strong> concurrency control.
      </p>

      <div class="callout-rules">
        <div class="rule-card">
          <span class="rule-pill">2PL &amp; Lock Policies (Binary · S/X · S/U/X)</span>
          <p>
            Transactions must hold a lock before reading and an <code>X</code> lock before writing,
            cannot acquire locks after any unlock (2PL shrinking phase), and under Ternary 2PL
            <code>U</code> is compatible with held <code>S</code> (preventing upgrade starvation)
            while only <code>U → X</code> upgrades are allowed.
          </p>
        </div>
        <div class="rule-card">
          <span class="rule-pill">Dependency Graphs · Wait-Die / Wound-Wait · OCC</span>
          <p>
            A schedule is conflict-serializable iff its Precedence Graph has no cycles.
            <strong>Wait-Die</strong> &amp; <strong>Wound-Wait</strong> prevent Wait-For cycles via
            transaction timestamps; <strong>Kung–Robinson OCC</strong> executes unlocked and validates
            <code>WriteSet(Ti) ∩ ReadSet(Tj) = ∅</code> at commit.
          </p>
        </div>
      </div>
    </header>

    <div class="der-workbench">
      <!-- Presets & Schedule Input Builder -->
      <section class="panel">
        <div class="panel-header">
          <div>
            <h2>Schedule Builder &amp; 2PL Lock Policy Selector</h2>
            <p class="panel-hint" style="margin:0.15rem 0 0;">
              Choose a preset schedule or add/edit operations below (<code>SL(T1, A)</code>,
              <code>UL(T2, A)</code>, <code>XL(T1, A)</code>, <code>R(T1, A)</code>,
              <code>W(T1, A)</code>, <code>U(T1, A)</code>, <code>C(T1)</code>).
            </p>
          </div>
          <div class="segmented" id="sched-policy-tabs">
            <button type="button" class="segmented-btn" data-lock-policy="binary">
              Simple Binary (L)
            </button>
            <button type="button" class="segmented-btn" data-lock-policy="multiple">
              Multiple (S / X)
            </button>
            <button type="button" class="segmented-btn" data-lock-policy="ternary">
              Ternary (S / U / X)
            </button>
          </div>
        </div>

        <div class="presets-bar" style="margin-bottom:0.75rem;">
          <span class="presets-label">Presets:</span>
          <div class="presets-list" id="sched-presets-list"></div>
        </div>

        <div class="der-norm-two-col">
          <div>
            <label class="der-field-label">Schedule Operations (one per line or semicolon-separated)</label>
            <textarea id="sched-textarea" class="schedule-textarea" rows="8"></textarea>
            <div id="sched-parse-errors"></div>
          </div>

          <div class="der-subpanel">
            <div class="der-sub-header">
              <h3>Quick Operation Appender</h3>
            </div>
            <form class="inline-form" id="sched-add-op-form" style="margin-bottom:0.75rem;">
              <select class="input input-sm" id="sched-op-verb">
                <option value="SL">SL (Shared Lock)</option>
                <option value="UL">UL (Update Lock)</option>
                <option value="XL">XL (Exclusive Lock)</option>
                <option value="R">R (Read)</option>
                <option value="W">W (Write)</option>
                <option value="U">U (Unlock)</option>
                <option value="C">C (Commit)</option>
                <option value="A">A (Abort)</option>
              </select>
              <input type="text" class="input input-sm" id="sched-op-tx" value="T1" style="width:68px;" placeholder="T1" required />
              <input type="text" class="input input-sm" id="sched-op-el" value="A" style="width:68px;" placeholder="A" />
              <button type="submit" class="btn btn-primary btn-sm">+ Append Op</button>
            </form>

            <div class="der-field-label">Active Lock Policy Compatibility Matrix</div>
            <div id="sched-matrix-box"></div>
          </div>
        </div>
      </section>

      <!-- Section 1: Pessimistic 2PL Scheduler & Lock Table Trace -->
      <section class="panel" id="sec-sched-serializability"></section>

      <!-- Section 2: Precedence / Dependency Graph & Topological Serial Orders -->
      <section class="panel" id="sec-sched-graphs"></section>

      <!-- Section 3: Deadlock Visualizer (Wait-For Graph, Wait-Die & Wound-Wait) -->
      <section class="panel" id="sec-sched-deadlocks"></section>

      <!-- Section 4: Optimistic (Kung-Robinson OCC) vs Pessimistic (2PL) Concurrency Control -->
      <section class="panel" id="sec-sched-concurrency"></section>
    </div>
  `;

  const presetsListEl = article.querySelector<HTMLElement>("#sched-presets-list")!;
  const textareaEl = article.querySelector<HTMLTextAreaElement>("#sched-textarea")!;
  const parseErrorsEl = article.querySelector<HTMLElement>("#sched-parse-errors")!;
  const matrixBoxEl = article.querySelector<HTMLElement>("#sched-matrix-box")!;
  const secSerialEl = article.querySelector<HTMLElement>("#sec-sched-serializability")!;
  const secGraphsEl = article.querySelector<HTMLElement>("#sec-sched-graphs")!;
  const secDeadlocksEl = article.querySelector<HTMLElement>("#sec-sched-deadlocks")!;
  const secOccEl = article.querySelector<HTMLElement>("#sec-sched-concurrency")!;

  textareaEl.value = scheduleText;

  function renderMatrixHtml(): string {
    if (lockPolicy === "binary") {
      return `
        <table class="data-table chase-table" style="font-size:0.78rem;">
          <thead><tr><th>Held \\ Req</th><th>L (Exclusive)</th><th>Upgrades</th></tr></thead>
          <tbody>
            <tr><td><strong>L (Exclusive)</strong></td><td class="chase-cell-sub">✗ No</td><td>None</td></tr>
          </tbody>
        </table>
      `;
    }
    if (lockPolicy === "multiple") {
      return `
        <table class="data-table chase-table" style="font-size:0.78rem;">
          <thead><tr><th>Held \\ Req</th><th>S</th><th>X</th><th>Allowed Upgrade</th></tr></thead>
          <tbody>
            <tr><td><strong>S</strong></td><td class="chase-cell-dist">✓ Yes</td><td class="chase-cell-sub">✗ No</td><td><code>S → X</code></td></tr>
            <tr><td><strong>X</strong></td><td class="chase-cell-sub">✗ No</td><td class="chase-cell-sub">✗ No</td><td>—</td></tr>
          </tbody>
        </table>
      `;
    }
    return `
      <table class="data-table chase-table" style="font-size:0.78rem;">
        <thead><tr><th>Held \\ Req</th><th>S</th><th>U</th><th>X</th><th>Allowed Upgrade</th></tr></thead>
        <tbody>
          <tr><td><strong>S</strong></td><td class="chase-cell-dist">✓ Yes</td><td class="chase-cell-dist">✓ Yes</td><td class="chase-cell-sub">✗ No</td><td>✗ (S→X forbidden)</td></tr>
          <tr><td><strong>U</strong></td><td class="chase-cell-sub">✗ No (Asymmetric!)</td><td class="chase-cell-sub">✗ No</td><td class="chase-cell-sub">✗ No</td><td><code>U → X</code> ✓</td></tr>
          <tr><td><strong>X</strong></td><td class="chase-cell-sub">✗ No</td><td class="chase-cell-sub">✗ No</td><td class="chase-cell-sub">✗ No</td><td>—</td></tr>
        </tbody>
      </table>
    `;
  }

  function renderAll(): void {
    // Sync policy tabs
    article.querySelectorAll<HTMLButtonElement>("[data-lock-policy]").forEach((btn) => {
      btn.classList.toggle("is-active", btn.dataset.lockPolicy === lockPolicy);
    });

    // Sync presets
    presetsListEl.innerHTML = SCHEDULER_PRESETS.map(
      (p) => `
      <button type="button" class="btn btn-chip ${
        p.id === activePresetId ? "is-active-chip" : ""
      }" data-preset-id="${p.id}">
        ${escapeHtml(p.title)}
      </button>
    `
    ).join("");

    presetsListEl.querySelectorAll<HTMLButtonElement>("[data-preset-id]").forEach((btn) => {
      btn.addEventListener("click", () => {
        const found = SCHEDULER_PRESETS.find((p) => p.id === btn.dataset.presetId);
        if (found) {
          activePresetId = found.id;
          lockPolicy = found.policy;
          scheduleText = found.scheduleText;
          textareaEl.value = scheduleText;
          renderAll();
        }
      });
    });

    matrixBoxEl.innerHTML = renderMatrixHtml();

    const { ops, parseErrors } = parseScheduleText(scheduleText);
    parseErrorsEl.innerHTML =
      parseErrors.length > 0
        ? `<div class="error-box" style="margin-top:0.5rem;"><ul>${parseErrors
            .map((e) => `<li>${escapeHtml(e)}</li>`)
            .join("")}</ul></div>`
        : "";

    const schedRun = runPessimisticScheduler(lockPolicy, ops);
    const precGraph = buildPrecedenceGraph(ops);
    const deadlockSim = simulateDeadlockAndWaitFor(lockPolicy, deadlockPolicy, ops);
    const occRes = validateOccFromSchedule(ops);

    // -----------------------------------------------------------------------
    // 1. Pessimistic 2PL Scheduler & Lock Table Trace
    // -----------------------------------------------------------------------
    secSerialEl.innerHTML = `
      <div class="panel-header">
        <div>
          <h2>1. Pessimistic 2PL Scheduler &amp; Lock-Table Trace (<code>${escapeHtml(
            lockPolicy.toUpperCase()
          )}</code> Policy)</h2>
          <p class="panel-hint" style="margin:0.15rem 0 0;">
            Dispatches every operation through <code>PessimisticScheduler.ValidateSchedule</code>
            (mirroring <code>dafny/scheduler/PessimisticScheduler.dfy</code>).
          </p>
        </div>
        <span class="verdict-pill ${schedRun.isValid ? "is-ok" : "is-bad"}">
          2PL Locks Valid: ${
            schedRun.isValid ? "YES ✓ (0 errors)" : `NO ✗ (${schedRun.errors.length} errors)`
          }
        </span>
      </div>

      ${
        schedRun.errors.length > 0
          ? `<div class="error-box" style="margin-bottom:0.8rem;">
              <strong>2PL / Lock Policy Violations:</strong>
              <ul>${schedRun.errors.map((e) => `<li>${escapeHtml(e)}</li>`).join("")}</ul>
            </div>`
          : ""
      }

      <div class="table-scroll">
        <table class="data-table chase-table">
          <thead>
            <tr>
              <th>Step</th>
              <th>Operation</th>
              <th>Verdict</th>
              <th>Active Locks After Step</th>
              <th>2PL Shrinking Txs</th>
              <th>Policy Explanation</th>
            </tr>
          </thead>
          <tbody>
            ${schedRun.traces
              .map((tr) => {
                const lockEntries = Object.entries(tr.stateAfter.locks).map(
                  ([el, holders]) =>
                    `${el}: {${Object.entries(holders)
                      .map(([t, m]) => `${t}:${m}`)
                      .join(", ")}}`
                );
                return `
                  <tr class="${tr.allowed ? "" : "row-error"}">
                    <td><code>#${tr.stepIndex + 1}</code></td>
                    <td><code><strong>${escapeHtml(tr.op.raw)}</strong></code></td>
                    <td>
                      <span class="nf-badge ${tr.allowed ? "nf-bcnf" : "nf-unf"}">
                        ${tr.allowed ? "ALLOWED ✓" : "REJECTED ✗"}
                      </span>
                    </td>
                    <td><code>${escapeHtml(lockEntries.join(" | ") || "∅")}</code></td>
                    <td><code>${escapeHtml(
                      tr.stateAfter.shrinkingTxs.join(", ") || "∅"
                    )}</code></td>
                    <td>${escapeHtml(tr.reason)}</td>
                  </tr>
                `;
              })
              .join("")}
          </tbody>
        </table>
      </div>
    `;

    // -----------------------------------------------------------------------
    // 2. Precedence / Dependency Graph & Conflict Serializability
    // -----------------------------------------------------------------------
    secGraphsEl.innerHTML = `
      <div class="panel-header">
        <div>
          <h2>2. Precedence / Dependency Graph &amp; Conflict Serializability</h2>
          <p class="panel-hint" style="margin:0.15rem 0 0;">
            Mirrors <code>dafny/scheduler/Serializability.dfy</code> &amp;
            <code>DependencyGraph.dfy</code>: builds directed edges <code>Ti → Tj</code> for
            every <code>RW</code>, <code>WR</code>, and <code>WW</code> conflict.
          </p>
        </div>
        <span class="verdict-pill ${!precGraph.hasCycle ? "is-ok" : "is-bad"}">
          Conflict-Serializable: ${
            !precGraph.hasCycle
              ? `YES ✓ (${precGraph.topologicalOrders.length} equivalent serial order${
                  precGraph.topologicalOrders.length === 1 ? "" : "s"
                })`
              : `NO ✗ (Cycle: ${precGraph.cyclePath.join(" → ")})`
          }
        </span>
      </div>

      <div class="der-norm-two-col">
        <div class="der-subpanel" id="prec-graph-svg-slot">
          <div class="der-sub-header">
            <h3>Conflict Precedence Graph G = (V, E)</h3>
          </div>
        </div>

        <div class="der-subpanel">
          <div class="der-sub-header">
            <h3>Equivalent Topological Serial Schedules &amp; Conflict Edges</h3>
          </div>

          ${
            !precGraph.hasCycle
              ? `
            <div class="der-ok-banner" style="margin:0 0 0.75rem;">
              <strong>Equivalent Serial Transaction Orders:</strong><br/>
              ${precGraph.topologicalOrders
                .map((ord) => `<code>${escapeHtml(ord.join(" → "))}</code>`)
                .join(" &nbsp;|&nbsp; ")}
            </div>
          `
              : `
            <div class="error-box" style="margin:0 0 0.75rem;">
              <strong>Conflict Cycle Detected:</strong>
              <code>${escapeHtml(precGraph.cyclePath.join(" → "))}</code> —
              by <code>LemmaSerializableImpliesNoConflictCycle</code>, no equivalent serial schedule exists!
            </div>
          `
          }

          <div class="der-field-label">Detected Data Conflicts (${precGraph.edges.length})</div>
          ${
            precGraph.edges.length === 0
              ? `<p class="panel-hint">No conflicting Read/Write pairs across distinct transactions.</p>`
              : `<ul class="der-fd-list">
                  ${precGraph.edges
                    .map(
                      (e) => `
                    <li class="der-fd-item">
                      <span>
                        <strong>${escapeHtml(e.fromTx)} → ${escapeHtml(e.toTx)}</strong>
                        on <code>${escapeHtml(e.element)}</code>
                        <span class="nf-badge nf-3nf">${e.kind}</span>
                      </span>
                      <span class="panel-meta">
                        Step #${e.fromStep} <code>${escapeHtml(
                          e.fromOpRaw
                        )}</code> ≺ Step #${e.toStep} <code>${escapeHtml(e.toOpRaw)}</code>
                      </span>
                    </li>
                  `
                    )
                    .join("")}
                </ul>`
          }
        </div>
      </div>
    `;

    const precSlot = secGraphsEl.querySelector("#prec-graph-svg-slot")!;
    const cycleSet = new Set(precGraph.cyclePath);
    precSlot.appendChild(
      renderDirectedGraphSvg(
        precGraph.nodes,
        precGraph.edges.map((e) => ({
          from: e.fromTx,
          to: e.toTx,
          label: `${e.element}[${e.kind}]`,
          isCycleEdge:
            precGraph.hasCycle &&
            cycleSet.has(e.fromTx) &&
            cycleSet.has(e.toTx)
        })),
        precGraph.cyclePath,
        "Add Read/Write operations to build the Precedence Graph"
      )
    );

    // -----------------------------------------------------------------------
    // 3. Deadlock Visualizer (Wait-For Graph, Wait-Die & Wound-Wait)
    // -----------------------------------------------------------------------
    const tsText = Object.entries(deadlockSim.txTimestamps)
      .map(([tx, ts]) => `${tx}: TS=${ts}`)
      .join(", ");

    secDeadlocksEl.innerHTML = `
      <div class="panel-header">
        <div>
          <h2>3. Deadlock Visualizer (Wait-For Graph · Wait-Die · Wound-Wait)</h2>
          <p class="panel-hint" style="margin:0.15rem 0 0;">
            Mirrors <code>dafny/scheduler/DeadlockAndOCC.dfy</code>
            (<code>LemmaWaitDieDeadlockFree</code> &amp; <code>LemmaWoundWaitDeadlockFree</code>).
            Transaction timestamps: <code>${escapeHtml(tsText)}</code>.
          </p>
        </div>
        <div class="segmented">
          <button type="button" class="segmented-btn ${
            deadlockPolicy === "detect" ? "is-active" : ""
          }" data-dl-policy="detect">
            Wait-For Detection
          </button>
          <button type="button" class="segmented-btn ${
            deadlockPolicy === "wait-die" ? "is-active" : ""
          }" data-dl-policy="wait-die">
            Wait-Die (Non-Preemptive)
          </button>
          <button type="button" class="segmented-btn ${
            deadlockPolicy === "wound-wait" ? "is-active" : ""
          }" data-dl-policy="wound-wait">
            Wound-Wait (Preemptive)
          </button>
        </div>
      </div>

      <div class="der-verdict-row" style="margin-bottom:0.85rem;">
        <span class="verdict-pill ${!deadlockSim.hasDeadlockCycle ? "is-ok" : "is-bad"}">
          Wait-For Graph Deadlock Cycle: ${
            deadlockSim.hasDeadlockCycle
              ? `DEADLOCK DETECTED ✗ (${deadlockSim.deadlockCycle.join(" → ")})`
              : "NONE ✓ (Deadlock-Free)"
          }
        </span>
        <span class="verdict-pill ${
          deadlockSim.abortedTxs.length === 0 ? "is-ok" : "is-warn"
        }">
          Aborted / Preempted Transactions: ${
            deadlockSim.abortedTxs.length === 0
              ? "None"
              : deadlockSim.abortedTxs.join(", ")
          }
        </span>
      </div>

      <div class="der-norm-two-col">
        <div class="der-subpanel" id="waitfor-graph-svg-slot">
          <div class="der-sub-header">
            <h3>Wait-For Graph (Ti → Tj means Ti waits for lock held by Tj)</h3>
          </div>
        </div>

        <div class="der-subpanel">
          <div class="der-sub-header">
            <h3>Lock Request &amp; Deadlock Resolution Trace</h3>
          </div>
          <ul class="der-fd-list" style="max-height:240px;overflow-y:auto;">
            ${deadlockSim.events
              .map(
                (ev) => `
              <li class="der-fd-item">
                <span>
                  <code>#${ev.stepIndex} <strong>${escapeHtml(ev.opRaw)}</strong></code>
                  — ${escapeHtml(ev.detail)}
                </span>
                <span class="nf-badge ${
                  ev.status === "granted"
                    ? "nf-bcnf"
                    : ev.status === "waiting"
                      ? "nf-1nf"
                      : ev.status === "aborted-die" || ev.status === "preempted-wound"
                        ? "nf-unf"
                        : "nf-2nf"
                }">
                  ${escapeHtml(ev.status)}
                </span>
              </li>
            `
              )
              .join("")}
          </ul>
        </div>
      </div>
    `;

    const wfSlot = secDeadlocksEl.querySelector("#waitfor-graph-svg-slot")!;
    const wfCycleSet = new Set(deadlockSim.deadlockCycle);
    wfSlot.appendChild(
      renderDirectedGraphSvg(
        Object.keys(deadlockSim.txTimestamps),
        deadlockSim.waitEdges.map((e) => ({
          from: e.waitingTx,
          to: e.holderTx,
          label: `wait ${e.requestedMode}(${e.element})`,
          isCycleEdge:
            deadlockSim.hasDeadlockCycle &&
            wfCycleSet.has(e.waitingTx) &&
            wfCycleSet.has(e.holderTx)
        })),
        deadlockSim.deadlockCycle,
        "No active Wait-For edges"
      )
    );

    secDeadlocksEl.querySelectorAll<HTMLButtonElement>("[data-dl-policy]").forEach((btn) => {
      btn.addEventListener("click", () => {
        deadlockPolicy = btn.dataset.dlPolicy as DeadlockPolicyKind;
        renderAll();
      });
    });

    // -----------------------------------------------------------------------
    // 4. Optimistic (Kung-Robinson OCC) vs Pessimistic (2PL) Concurrency
    // -----------------------------------------------------------------------
    secOccEl.innerHTML = `
      <div class="panel-header">
        <div>
          <h2>4. Optimistic (Kung–Robinson OCC) vs Pessimistic (2PL) Control</h2>
          <p class="panel-hint" style="margin:0.15rem 0 0;">
            Under <strong>OCC</strong>, transactions read and buffer writes privately without locks,
            then validate at commit time in validation-timestamp order
            (<code>dafny/scheduler/DeadlockAndOCC.dfy</code> → <code>ValidateOccSchedule</code>).
          </p>
        </div>
        <span class="verdict-pill ${occRes.allValid ? "is-ok" : "is-bad"}">
          OCC Validation Verdict: ${
            occRes.allValid
              ? "ALL COMMITTED ✓"
              : `ABORT REQUIRED ✗ (Must abort &amp; restart: ${occRes.abortedTxs.join(", ")})`
          }
        </span>
      </div>

      <div class="der-norm-two-col">
        <div class="der-subpanel">
          <div class="der-sub-header">
            <h3>OCC Transaction Phases &amp; Read/Write Sets</h3>
          </div>
          <div class="table-scroll">
            <table class="data-table chase-table">
              <thead>
                <tr>
                  <th>Tx</th>
                  <th>Start</th>
                  <th>Validate</th>
                  <th>Finish</th>
                  <th>ReadSet(T)</th>
                  <th>WriteSet(T)</th>
                  <th>Status</th>
                </tr>
              </thead>
              <tbody>
                ${occRes.records
                  .map((r) => {
                    const aborted = occRes.abortedTxs.includes(r.tx);
                    return `
                      <tr class="${aborted ? "row-error" : ""}">
                        <td><strong>${escapeHtml(r.tx)}</strong></td>
                        <td><code>#${r.startStep}</code></td>
                        <td><code>#${r.validateStep}</code></td>
                        <td><code>#${r.finishStep}</code></td>
                        <td><code>{${escapeHtml(r.readSet.join(", "))}}</code></td>
                        <td><code>{${escapeHtml(r.writeSet.join(", "))}}</code></td>
                        <td>
                          <span class="nf-badge ${aborted ? "nf-unf" : "nf-bcnf"}">
                            ${aborted ? "ABORT AT VALIDATE ✗" : "VALIDATED ✓"}
                          </span>
                        </td>
                      </tr>
                    `;
                  })
                  .join("")}
              </tbody>
            </table>
          </div>
        </div>

        <div class="der-subpanel">
          <div class="der-sub-header">
            <h3>Kung–Robinson Pairwise Validation Checks (Ti ≺ Tj)</h3>
          </div>
          ${
            occRes.pairChecks.length === 0
              ? `<p class="panel-hint">Need at least two transactions to run pairwise OCC validation.</p>`
              : `<ul class="der-fd-list">
                  ${occRes.pairChecks
                    .map(
                      (chk) => `
                    <li class="der-fd-item">
                      <span>
                        <strong>${escapeHtml(chk.earlierTx)} → ${escapeHtml(
                          chk.laterTx
                        )}</strong>:
                        ${escapeHtml(chk.ruleMatched)}
                      </span>
                      <span class="nf-badge ${chk.passed ? "nf-bcnf" : "nf-unf"}">
                        ${chk.passed ? "PASS ✓" : "FAIL ✗"}
                      </span>
                    </li>
                  `
                    )
                    .join("")}
                </ul>`
          }

          <div class="der-key-summary" style="margin-top:0.75rem;padding-top:0.65rem;border-top:1px solid var(--border);">
            <div><strong>Pessimistic 2PL Verdict:</strong> ${
              schedRun.isValid ? "Valid 2PL schedule ✓" : `Rejected (${schedRun.errors.length} lock errors) ✗`
            }</div>
            <div><strong>Conflict Serializability:</strong> ${
              !precGraph.hasCycle
                ? `Serializable (${precGraph.topologicalOrders
                    .map((o) => o.join("→"))
                    .join(" | ")}) ✓`
                : `Not conflict-serializable (cycle ${precGraph.cyclePath.join("→")}) ✗`
            }</div>
            <div><strong>Optimistic (OCC) Verdict:</strong> ${
              occRes.allValid
                ? "All transactions validate without lock overhead ✓"
                : `Aborts ${occRes.abortedTxs.join(", ")} at validation phase ✗`
            }</div>
          </div>
        </div>
      </div>
    `;
  }

  // Wire top-level policy buttons, textarea, and quick op form
  article.querySelectorAll<HTMLButtonElement>("[data-lock-policy]").forEach((btn) => {
    btn.addEventListener("click", () => {
      lockPolicy = btn.dataset.lockPolicy as LockPolicyKind;
      renderAll();
    });
  });

  textareaEl.addEventListener("input", () => {
    scheduleText = textareaEl.value;
    activePresetId = "";
    renderAll();
  });

  article
    .querySelector<HTMLFormElement>("#sched-add-op-form")
    ?.addEventListener("submit", (ev) => {
      ev.preventDefault();
      const verb = article.querySelector<HTMLSelectElement>("#sched-op-verb")!.value;
      const tx =
        article.querySelector<HTMLInputElement>("#sched-op-tx")!.value.trim() || "T1";
      const el =
        article.querySelector<HTMLInputElement>("#sched-op-el")!.value.trim() || "A";
      const line =
        verb === "C" || verb === "A" ? `${verb}(${tx})` : `${verb}(${tx}, ${el})`;
      scheduleText = scheduleText.trim()
        ? `${scheduleText.trim()}\n${line}`
        : line;
      textareaEl.value = scheduleText;
      activePresetId = "";
      renderAll();
    });

  renderAll();

  if (initialFocus !== "serializability") {
    const targetId =
      initialFocus === "graphs"
        ? "#sec-sched-graphs"
        : initialFocus === "deadlocks"
          ? "#sec-sched-deadlocks"
          : "#sec-sched-concurrency";
    setTimeout(() => {
      article.querySelector(targetId)?.scrollIntoView({ behavior: "smooth", block: "start" });
    }, 40);
  }

  return article;
}
