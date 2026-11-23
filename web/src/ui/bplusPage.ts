// Interactive B+ Tree Visualizer (Search, Linked-Leaf Iteration / Range Scan,
// Insert with Copy-Up / Push-Up Splits, Delete with Borrow / Merge) and
// Index vs. No-Index (Full Table Scan) Cost & Query Planner Comparison.
//
// Mirrors `dafny/indexing/BPlusTree.dfy`.

import {
  allEntries,
  BPLUS_PRESETS,
  buildTreeFromPreset,
  collectLeaves,
  createEmptyBPlusTree,
  deleteBPlusTree,
  evaluateIndexVsTableScan,
  INDEX_COST_PRESETS,
  insertBPlusTree,
  rangeScanBPlusTree,
  resetNodeIds,
  searchBPlusTree,
  type BPlusNode,
  type BPlusOperationResult,
  type BPlusTree,
  type IndexCostParams
} from "../indexing/bplusEngine";

const SVG_NS = "http://www.w3.org/2000/svg";

function escapeHtml(s: string): string {
  return s
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}

// ---------------------------------------------------------------------------
// B+ Tree SVG Layout & Renderer
// ---------------------------------------------------------------------------

interface LayoutBox {
  node: BPlusNode;
  x: number; // left edge
  y: number; // top edge
  w: number;
  h: number;
  cx: number; // center x
  depth: number;
}

function renderBPlusTreeSvg(
  tree: BPlusTree,
  opResult: BPlusOperationResult | null,
  onClickKey: (k: number) => void
): SVGSVGElement {
  const svg = document.createElementNS(SVG_NS, "svg");
  svg.setAttribute("class", "bplus-svg");

  const visitedSet = new Set(opResult?.visitedNodeIds ?? []);
  const leafChainSet = new Set(opResult?.leafChainNodeIds ?? []);
  const matchedKeySet = new Set((opResult?.matchedEntries ?? []).map((e) => e.key));
  const highlightedKey = opResult?.highlightedKey ?? null;

  const LEVEL_GAP_Y = 96;
  const LEAF_GAP_X = 28;
  const CELL_W_LEAF = 52;
  const CELL_W_INT = 42;
  const NODE_H_LEAF = 44;
  const NODE_H_INT = 36;
  const PAD_X = 30;
  const PAD_Y = 28;

  const boxes = new Map<string, LayoutBox>();
  let cursorX = PAD_X;

  function layoutRec(node: BPlusNode, depth: number): LayoutBox {
    const y = PAD_Y + depth * LEVEL_GAP_Y;
    if (node.kind === "Leaf") {
      const cellCount = Math.max(1, node.entries.length);
      const w = Math.max(66, cellCount * CELL_W_LEAF + 12);
      const x = cursorX;
      cursorX += w + LEAF_GAP_X;
      const box: LayoutBox = {
        node,
        x,
        y,
        w,
        h: NODE_H_LEAF,
        cx: x + w / 2,
        depth
      };
      boxes.set(node.id, box);
      return box;
    }

    const childBoxes = node.children.map((ch) => layoutRec(ch, depth + 1));
    const minCx = childBoxes[0].cx;
    const maxCx = childBoxes[childBoxes.length - 1].cx;
    const cx = (minCx + maxCx) / 2;
    const cellCount = Math.max(1, node.keys.length);
    const w = Math.max(62, cellCount * CELL_W_INT + 14);
    const box: LayoutBox = {
      node,
      x: cx - w / 2,
      y,
      w,
      h: NODE_H_INT,
      cx,
      depth
    };
    boxes.set(node.id, box);
    return box;
  }

  layoutRec(tree.root, 0);

  const totalW = Math.max(680, cursorX - LEAF_GAP_X + PAD_X);
  const totalH = Math.max(170, PAD_Y * 2 + tree.height * LEVEL_GAP_Y + NODE_H_LEAF + 24);
  svg.setAttribute("viewBox", `0 0 ${totalW} ${totalH}`);
  svg.style.width = "100%";
  svg.style.minHeight = `${Math.min(360, totalH)}px`;

  const defs = document.createElementNS(SVG_NS, "defs");
  defs.innerHTML = `
    <marker id="bp-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto">
      <path d="M 0 1 L 10 5 L 0 9 z" fill="#64748b" />
    </marker>
    <marker id="bp-arrow-active" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6.5" markerHeight="6.5" orient="auto">
      <path d="M 0 1 L 10 5 L 0 9 z" fill="#2563eb" />
    </marker>
    <marker id="bp-arrow-leaf" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto">
      <path d="M 0 1 L 10 5 L 0 9 z" fill="#94a3b8" />
    </marker>
    <marker id="bp-arrow-leaf-active" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6.5" markerHeight="6.5" orient="auto">
      <path d="M 0 1 L 10 5 L 0 9 z" fill="#059669" />
    </marker>
  `;
  svg.appendChild(defs);

  // 1. Draw parent -> child edges
  for (const box of boxes.values()) {
    if (box.node.kind !== "Internal") continue;
    const childCount = box.node.children.length;
    box.node.children.forEach((child, idx) => {
      const childBox = boxes.get(child.id);
      if (!childBox) return;
      const portX =
        childCount === 1
          ? box.cx
          : box.x + 8 + ((box.w - 16) * idx) / (childCount - 1);
      const portY = box.y + box.h;
      const isEdgeVisited = visitedSet.has(box.node.id) && visitedSet.has(child.id);

      const line = document.createElementNS(SVG_NS, "line");
      line.setAttribute("x1", String(portX));
      line.setAttribute("y1", String(portY));
      line.setAttribute("x2", String(childBox.cx));
      line.setAttribute("y2", String(childBox.y - 2));
      line.setAttribute("stroke", isEdgeVisited ? "#2563eb" : "#94a3b8");
      line.setAttribute("stroke-width", isEdgeVisited ? "2.4" : "1.5");
      line.setAttribute(
        "marker-end",
        isEdgeVisited ? "url(#bp-arrow-active)" : "url(#bp-arrow)"
      );
      svg.appendChild(line);
    });
  }

  // 2. Draw horizontal linked-leaf sibling pointers (Leaf 0 -> Leaf 1 -> ...)
  const leaves = collectLeaves(tree.root);
  for (let i = 0; i + 1 < leaves.length; i++) {
    const lb = boxes.get(leaves[i].id);
    const rb = boxes.get(leaves[i + 1].id);
    if (!lb || !rb) continue;

    const isChainEdge =
      leafChainSet.has(leaves[i].id) && leafChainSet.has(leaves[i + 1].id);

    const arrow = document.createElementNS(SVG_NS, "line");
    arrow.setAttribute("x1", String(lb.x + lb.w + 2));
    arrow.setAttribute("y1", String(lb.y + lb.h / 2));
    arrow.setAttribute("x2", String(rb.x - 4));
    arrow.setAttribute("y2", String(rb.y + rb.h / 2));
    arrow.setAttribute("stroke", isChainEdge ? "#059669" : "#cbd5e1");
    arrow.setAttribute("stroke-width", isChainEdge ? "2.6" : "1.6");
    arrow.setAttribute("stroke-dasharray", isChainEdge ? "none" : "4 3");
    arrow.setAttribute(
      "marker-end",
      isChainEdge ? "url(#bp-arrow-leaf-active)" : "url(#bp-arrow-leaf)"
    );
    svg.appendChild(arrow);
  }

  // 3. Draw nodes
  for (const box of boxes.values()) {
    const g = document.createElementNS(SVG_NS, "g");
    const isVisited = visitedSet.has(box.node.id);
    const isLeafInChain = leafChainSet.has(box.node.id);

    // Node ID label above box
    const idTxt = document.createElementNS(SVG_NS, "text");
    idTxt.setAttribute("x", String(box.x + 4));
    idTxt.setAttribute("y", String(box.y - 5));
    idTxt.setAttribute("font-size", "9.5");
    idTxt.setAttribute("font-weight", "700");
    idTxt.setAttribute(
      "fill",
      isLeafInChain ? "#059669" : isVisited ? "#2563eb" : "#64748b"
    );
    idTxt.textContent =
      box.node.kind === "Leaf" ? `Leaf ${box.node.id}` : `Int ${box.node.id}`;
    g.appendChild(idTxt);

    // Outer node frame
    const rect = document.createElementNS(SVG_NS, "rect");
    rect.setAttribute("x", String(box.x));
    rect.setAttribute("y", String(box.y));
    rect.setAttribute("width", String(box.w));
    rect.setAttribute("height", String(box.h));
    rect.setAttribute("rx", "7");
    rect.setAttribute(
      "fill",
      box.node.kind === "Leaf"
        ? isLeafInChain
          ? "#ecfdf5"
          : "#ffffff"
        : isVisited
          ? "#eff6ff"
          : "#f8fafc"
    );
    rect.setAttribute(
      "stroke",
      isLeafInChain
        ? "#059669"
        : isVisited
          ? "#2563eb"
          : box.node.kind === "Leaf"
            ? "#0f172a"
            : "#475569"
    );
    rect.setAttribute("stroke-width", isVisited || isLeafInChain ? "2.3" : "1.5");
    g.appendChild(rect);

    if (box.node.kind === "Internal") {
      const count = box.node.keys.length;
      const cellW = box.w / Math.max(1, count);
      box.node.keys.forEach((k, idx) => {
        if (idx > 0) {
          const sep = document.createElementNS(SVG_NS, "line");
          sep.setAttribute("x1", String(box.x + idx * cellW));
          sep.setAttribute("y1", String(box.y));
          sep.setAttribute("x2", String(box.x + idx * cellW));
          sep.setAttribute("y2", String(box.y + box.h));
          sep.setAttribute("stroke", "#cbd5e1");
          sep.setAttribute("stroke-width", "1");
          g.appendChild(sep);
        }
        const txt = document.createElementNS(SVG_NS, "text");
        txt.setAttribute("x", String(box.x + idx * cellW + cellW / 2));
        txt.setAttribute("y", String(box.y + 22));
        txt.setAttribute("text-anchor", "middle");
        txt.setAttribute("font-size", "12.5");
        txt.setAttribute("font-weight", "800");
        txt.setAttribute("fill", "#0f172a");
        txt.textContent = String(k);
        g.appendChild(txt);
      });
    } else {
      const entries = box.node.entries;
      if (entries.length === 0) {
        const txt = document.createElementNS(SVG_NS, "text");
        txt.setAttribute("x", String(box.cx));
        txt.setAttribute("y", String(box.y + 26));
        txt.setAttribute("text-anchor", "middle");
        txt.setAttribute("font-size", "11");
        txt.setAttribute("fill", "#94a3b8");
        txt.textContent = "∅ (empty)";
        g.appendChild(txt);
      } else {
        const cellW = box.w / entries.length;
        entries.forEach((entry, idx) => {
          const cellX = box.x + idx * cellW;
          const isMatch = matchedKeySet.has(entry.key) || highlightedKey === entry.key;

          if (isMatch) {
            const hl = document.createElementNS(SVG_NS, "rect");
            hl.setAttribute("x", String(cellX + 2));
            hl.setAttribute("y", String(box.y + 2));
            hl.setAttribute("width", String(cellW - 4));
            hl.setAttribute("height", String(box.h - 4));
            hl.setAttribute("rx", "4");
            hl.setAttribute("fill", "#d1fae5");
            g.appendChild(hl);
          }

          if (idx > 0) {
            const sep = document.createElementNS(SVG_NS, "line");
            sep.setAttribute("x1", String(cellX));
            sep.setAttribute("y1", String(box.y));
            sep.setAttribute("x2", String(cellX));
            sep.setAttribute("y2", String(box.y + box.h));
            sep.setAttribute("stroke", "#e2e8f0");
            sep.setAttribute("stroke-width", "1");
            g.appendChild(sep);
          }

          const keyTxt = document.createElementNS(SVG_NS, "text");
          keyTxt.setAttribute("x", String(cellX + cellW / 2));
          keyTxt.setAttribute("y", String(box.y + 18));
          keyTxt.setAttribute("text-anchor", "middle");
          keyTxt.setAttribute("font-size", "12");
          keyTxt.setAttribute("font-weight", "800");
          keyTxt.setAttribute("fill", isMatch ? "#065f46" : "#0f172a");
          keyTxt.style.cursor = "pointer";
          keyTxt.textContent = String(entry.key);
          keyTxt.addEventListener("click", () => onClickKey(entry.key));
          g.appendChild(keyTxt);

          const valTxt = document.createElementNS(SVG_NS, "text");
          valTxt.setAttribute("x", String(cellX + cellW / 2));
          valTxt.setAttribute("y", String(box.y + 34));
          valTxt.setAttribute("text-anchor", "middle");
          valTxt.setAttribute("font-size", "9.5");
          valTxt.setAttribute("fill", isMatch ? "#047857" : "#64748b");
          valTxt.style.cursor = "pointer";
          valTxt.textContent = `→${entry.val}`;
          valTxt.addEventListener("click", () => onClickKey(entry.key));
          g.appendChild(valTxt);
        });
      }
    }

    svg.appendChild(g);
  }

  return svg;
}

// ---------------------------------------------------------------------------
// Selectivity Crossover Chart SVG (Index Seek vs Full Table Scan vs Full Index Scan)
// ---------------------------------------------------------------------------

function renderCrossoverChartSvg(params: IndexCostParams): SVGSVGElement {
  const svg = document.createElementNS(SVG_NS, "svg");
  svg.setAttribute("viewBox", "0 0 560 230");
  svg.style.width = "100%";
  svg.style.maxHeight = "240px";

  const padL = 56;
  const padR = 20;
  const padT = 20;
  const padB = 34;
  const plotW = 560 - padL - padR;
  const plotH = 230 - padT - padB;

  const samplePcts = [0.1, 1, 2, 4, 6, 8, 10, 15, 20, 25, 30, 40, 50, 60];
  const samples = samplePcts.map((pct) => {
    const cmp = evaluateIndexVsTableScan({
      ...params,
      selectivityPct: pct,
      indexCanSeek: true,
      indexIsCovering: false
    });
    const fullTable = cmp.plans.find((p) => p.id === "full-table-scan")!.effectiveIoCost;
    const idxSeek = cmp.plans.find((p) => p.id === "index-seek-heap")!.effectiveIoCost;
    const fullIdxCover = cmp.indexLeafPages;
    return { pct, fullTable, idxSeek, fullIdxCover };
  });

  const maxCost = Math.max(
    10,
    ...samples.map((s) => Math.max(s.fullTable * 1.4, Math.min(s.idxSeek, s.fullTable * 2.4)))
  );

  const xOf = (pct: number) => padL + (Math.min(60, Math.max(0, pct)) / 60) * plotW;
  const yOf = (cost: number) =>
    padT + plotH - (Math.min(maxCost, Math.max(0, cost)) / maxCost) * plotH;

  // Axes & grid
  const bg = document.createElementNS(SVG_NS, "rect");
  bg.setAttribute("x", String(padL));
  bg.setAttribute("y", String(padT));
  bg.setAttribute("width", String(plotW));
  bg.setAttribute("height", String(plotH));
  bg.setAttribute("fill", "#f8fafc");
  bg.setAttribute("stroke", "#e2e8f0");
  svg.appendChild(bg);

  for (const pct of [0, 10, 20, 30, 40, 50, 60]) {
    const x = xOf(pct);
    const grid = document.createElementNS(SVG_NS, "line");
    grid.setAttribute("x1", String(x));
    grid.setAttribute("y1", String(padT));
    grid.setAttribute("x2", String(x));
    grid.setAttribute("y2", String(padT + plotH));
    grid.setAttribute("stroke", "#e2e8f0");
    grid.setAttribute("stroke-dasharray", "3 3");
    svg.appendChild(grid);

    const lbl = document.createElementNS(SVG_NS, "text");
    lbl.setAttribute("x", String(x));
    lbl.setAttribute("y", String(padT + plotH + 16));
    lbl.setAttribute("text-anchor", "middle");
    lbl.setAttribute("font-size", "10");
    lbl.setAttribute("fill", "#64748b");
    lbl.textContent = `${pct}%`;
    svg.appendChild(lbl);
  }

  const xTitle = document.createElementNS(SVG_NS, "text");
  xTitle.setAttribute("x", String(padL + plotW / 2));
  xTitle.setAttribute("y", String(226));
  xTitle.setAttribute("text-anchor", "middle");
  xTitle.setAttribute("font-size", "10.5");
  xTitle.setAttribute("font-weight", "700");
  xTitle.setAttribute("fill", "#475569");
  xTitle.textContent = "Query Selectivity (% of Rows Matched)";
  svg.appendChild(xTitle);

  const yTitle = document.createElementNS(SVG_NS, "text");
  yTitle.setAttribute("x", "14");
  yTitle.setAttribute("y", String(padT + plotH / 2));
  yTitle.setAttribute("text-anchor", "middle");
  yTitle.setAttribute("font-size", "10");
  yTitle.setAttribute("font-weight", "700");
  yTitle.setAttribute("fill", "#475569");
  yTitle.setAttribute("transform", `rotate(-90 14 ${padT + plotH / 2})`);
  yTitle.textContent = "Effective I/O Cost";
  svg.appendChild(yTitle);

  const makePath = (pts: [number, number][], color: string, dashed = false) => {
    const p = document.createElementNS(SVG_NS, "path");
    p.setAttribute(
      "d",
      pts.map(([x, y], i) => `${i === 0 ? "M" : "L"} ${x.toFixed(1)} ${y.toFixed(1)}`).join(" ")
    );
    p.setAttribute("fill", "none");
    p.setAttribute("stroke", color);
    p.setAttribute("stroke-width", "2.4");
    if (dashed) p.setAttribute("stroke-dasharray", "6 4");
    svg.appendChild(p);
  };

  // Full Table Scan line (slate/amber)
  makePath(
    samples.map((s) => [xOf(s.pct), yOf(s.fullTable)]),
    "#d97706"
  );
  // Full Index Leaf Scan (Covering) line (emerald)
  makePath(
    samples.map((s) => [xOf(s.pct), yOf(s.fullIdxCover)]),
    "#059669",
    true
  );
  // Unclustered Index Seek + Heap Fetch curve (blue)
  makePath(
    samples.map((s) => [xOf(s.pct), yOf(s.idxSeek)]),
    "#2563eb"
  );

  // Current selectivity vertical marker
  const curX = xOf(params.selectivityPct);
  const marker = document.createElementNS(SVG_NS, "line");
  marker.setAttribute("x1", String(curX));
  marker.setAttribute("y1", String(padT));
  marker.setAttribute("x2", String(curX));
  marker.setAttribute("y2", String(padT + plotH));
  marker.setAttribute("stroke", "#be123c");
  marker.setAttribute("stroke-width", "1.8");
  marker.setAttribute("stroke-dasharray", "4 3");
  svg.appendChild(marker);

  const curLbl = document.createElementNS(SVG_NS, "text");
  curLbl.setAttribute("x", String(Math.min(padL + plotW - 35, Math.max(padL + 35, curX))));
  curLbl.setAttribute("y", String(padT + 12));
  curLbl.setAttribute("text-anchor", "middle");
  curLbl.setAttribute("font-size", "9.5");
  curLbl.setAttribute("font-weight", "800");
  curLbl.setAttribute("fill", "#be123c");
  curLbl.textContent = `Current: ${params.selectivityPct}%`;
  svg.appendChild(curLbl);

  return svg;
}

// ---------------------------------------------------------------------------
// Main B+ Tree & Index Cost Page
// ---------------------------------------------------------------------------

export function renderBPlusPage(): HTMLElement {
  const article = document.createElement("article");
  article.className = "blog-article der-article";

  let activePresetId = BPLUS_PRESETS[0].id;
  let tree: BPlusTree = buildTreeFromPreset(BPLUS_PRESETS[0]);
  let lastResult: BPlusOperationResult | null = searchBPlusTree(
    tree,
    BPLUS_PRESETS[0].defaultSearch
  );

  let insertKeyInput = "35";
  let insertValInput = "350";
  let searchKeyInput = String(BPLUS_PRESETS[0].defaultSearch);
  let rangeLoInput = String(BPLUS_PRESETS[0].defaultRange[0]);
  let rangeHiInput = String(BPLUS_PRESETS[0].defaultRange[1]);
  let deleteKeyInput = String(BPLUS_PRESETS[0].defaultDelete);

  // Cost comparison state
  let activeCostPresetId: string = INDEX_COST_PRESETS[2].id; // default to Wide Range showing planner choosing Full Table Scan!
  let costParams: IndexCostParams = { ...INDEX_COST_PRESETS[2].params };
  let activeSqlExample = INDEX_COST_PRESETS[2].sqlExample;

  function render(): void {
    const leaves = collectLeaves(tree.root);
    const totalEntries = allEntries(tree);
    const costCmp = evaluateIndexVsTableScan(costParams);
    const maxPlanCost = Math.max(
      1,
      ...costCmp.plans.filter((p) => p.available).map((p) => p.effectiveIoCost)
    );

    article.innerHTML = `
      <header class="article-header">
        <div class="breadcrumb">Storage &amp; Indexing / B+ Tree &amp; Index Cost</div>
        <h1>B+ Tree Visualizer &amp; Index vs. Table Scan Cost</h1>
        <p class="article-lead">
          Interactive visualization of the formally verified B+ Tree in
          <code>dafny/indexing/BPlusTree.dfy</code>: inspect <strong>root-to-leaf search</strong>,
          <strong>linked-leaf range iteration</strong>, <strong>insertions with Copy-Up &amp; Push-Up splits</strong>,
          and <strong>deletions with sibling borrow / merge</strong> — followed by an interactive
          <strong>Index vs. No-Index Query Planner Cost Comparison</strong> showing when the planner
          prefers a Full Table Scan or a Full Index Leaf Scan even when an index cannot seek.
        </p>

        <div class="callout-rules">
          <div class="rule-card">
            <span class="rule-pill">B+ Tree Structure &amp; Leaf Chain</span>
            <p>
              All <code>(key → value)</code> records live exclusively in <strong>Leaf</strong> nodes at
              uniform depth (<code>height</code>), linked left-to-right for fast sequential range
              iteration. Internal nodes store separator keys (<code>keys[i-1] ≤ k &lt; keys[i]</code>).
            </p>
          </div>
          <div class="rule-card">
            <span class="rule-pill">Why Planners Sometimes Scan Instead of Seeking</span>
            <p>
              An unclustered index seek incurs random heap I/O per matching row — past a selectivity
              threshold (~10–25%), a <strong>Full Table Scan</strong> beats the index! Conversely, for
              a <strong>non-sargable</strong> predicate on a <strong>covering index</strong>, a
              <strong>Full Index Leaf Scan</strong> beats a Full Table Scan because index leaves are
              much narrower than heap pages.
            </p>
          </div>
        </div>
      </header>

      <div class="der-workbench">
        <!-- B+ Tree Controls & Presets -->
        <section class="panel">
          <div class="panel-header">
            <div>
              <h2>1. Interactive B+ Tree Playground</h2>
              <p class="panel-hint" style="margin:0.15rem 0 0;">
                Height: <code>${tree.height}</code> &nbsp;·&nbsp;
                Max keys/node: <code>${tree.maxKeys}</code> (Order ${tree.maxKeys + 1}) &nbsp;·&nbsp;
                Leaves: <code>${leaves.length}</code> &nbsp;·&nbsp;
                Total entries: <code>${totalEntries.length}</code>.
                Click any leaf entry in the diagram to populate Search / Remove.
              </p>
            </div>
            <div class="segmented" role="group" aria-label="B+ Tree maxKeys">
              ${[2, 3, 4]
                .map(
                  (mk) => `
                <button
                  type="button"
                  class="segmented-btn${tree.maxKeys === mk ? " is-active" : ""}"
                  data-bp-maxkeys="${mk}"
                >maxKeys = ${mk} (Order ${mk + 1})</button>
              `
                )
                .join("")}
            </div>
          </div>

          <div class="presets-bar" style="margin-bottom:0.85rem;">
            <span class="presets-label">Presets:</span>
            <div class="presets-list">
              ${BPLUS_PRESETS.map(
                (p) => `
                <button
                  type="button"
                  class="btn btn-chip ${p.id === activePresetId ? "is-active-chip" : ""}"
                  data-bp-preset="${p.id}"
                >${escapeHtml(p.title)}</button>
              `
              ).join("")}
              <button type="button" class="btn btn-chip" data-bp-clear>Clear Tree</button>
            </div>
          </div>

          <!-- 4 Action Forms: Search, Iterate/Range Scan, Insert, Remove -->
          <div class="der-norm-two-col" style="margin-bottom:0.85rem;">
            <div class="der-subpanel">
              <div class="der-sub-header">
                <h3>Search &amp; Linked-Leaf Iteration (Range Scan)</h3>
              </div>

              <form class="inline-form" id="bp-search-form" style="margin-bottom:0.55rem;">
                <label class="der-field-label" style="margin:0;">Search Key:</label>
                <input type="number" step="1" class="input input-sm input-num" name="searchKey" value="${escapeHtml(searchKeyInput)}" required />
                <button type="submit" class="btn btn-primary btn-sm">🔍 Search</button>
              </form>

              <form class="inline-form" id="bp-range-form">
                <label class="der-field-label" style="margin:0;">Iterate Range:</label>
                <input type="number" step="1" class="input input-sm input-num" name="lo" value="${escapeHtml(rangeLoInput)}" placeholder="lo" required />
                <span>to</span>
                <input type="number" step="1" class="input input-sm input-num" name="hi" value="${escapeHtml(rangeHiInput)}" placeholder="hi" required />
                <button type="submit" class="btn btn-secondary btn-sm">⇢ Iterate Range</button>
                <button type="button" class="btn btn-secondary btn-sm" data-bp-iterate-all>Iterate Full Tree</button>
              </form>
            </div>

            <div class="der-subpanel">
              <div class="der-sub-header">
                <h3>Insert (Splits) &amp; Remove (Borrow / Merge)</h3>
              </div>

              <form class="inline-form" id="bp-insert-form" style="margin-bottom:0.55rem;">
                <label class="der-field-label" style="margin:0;">Insert:</label>
                <input type="number" step="1" class="input input-sm input-num" name="key" value="${escapeHtml(insertKeyInput)}" placeholder="Key" required />
                <input type="number" step="1" class="input input-sm input-num" name="val" value="${escapeHtml(insertValInput)}" placeholder="Val" required />
                <button type="submit" class="btn btn-primary btn-sm">+ Insert</button>
              </form>

              <form class="inline-form" id="bp-delete-form">
                <label class="der-field-label" style="margin:0;">Remove Key:</label>
                <input type="number" step="1" class="input input-sm input-num" name="delKey" value="${escapeHtml(deleteKeyInput)}" placeholder="Key" required />
                <button type="submit" class="btn btn-secondary btn-sm" style="color:#be123c;">✕ Remove</button>
              </form>
            </div>
          </div>

          <!-- Live B+ Tree SVG Canvas -->
          <div
            id="bp-svg-container"
            style="background:#ffffff;border:1px solid var(--border);border-radius:10px;padding:0.65rem;overflow-x:auto;margin-bottom:0.85rem;"
          ></div>

          ${
            lastResult
              ? `
            <div class="${lastResult.found ? "der-ok-banner" : "error-box"}" style="margin-bottom:0.75rem;">
              <strong>Result:</strong> ${escapeHtml(lastResult.summary)}
              ${
                lastResult.matchedEntries.length > 0
                  ? `<div style="margin-top:0.35rem;"><strong>Yielded Entries (Sorted):</strong> ${lastResult.matchedEntries
                      .map((e) => `<code>(${e.key} → ${e.val})</code>`)
                      .join(" ⇢ ")}</div>`
                  : ""
              }
            </div>

            <div class="der-subpanel">
              <div class="der-sub-header">
                <h3>Step-by-Step Traversal / Mutation Trace (${lastResult.steps.length} steps)</h3>
              </div>
              <ul class="der-fd-list">
                ${lastResult.steps
                  .map(
                    (st) => `
                  <li class="der-fd-item">
                    <span><code>#${st.step}</code> ${escapeHtml(st.detail)}</span>
                    <span class="nf-badge ${
                      st.action === "found" || st.action === "leaf-next"
                        ? "nf-bcnf"
                        : st.action === "not-found" || st.action === "delete"
                          ? "nf-unf"
                          : st.action === "split-leaf" ||
                              st.action === "split-internal" ||
                              st.action === "split-root" ||
                              st.action === "borrow" ||
                              st.action === "merge" ||
                              st.action === "shrink-root"
                            ? "nf-1nf"
                            : "nf-3nf"
                    }">${escapeHtml(st.action.toUpperCase())}</span>
                  </li>
                `
                  )
                  .join("")}
              </ul>
            </div>
          `
              : ""
          }
        </section>

        <!-- 2. Index vs. No-Index (Full Table Scan) & Planner Decision Comparison -->
        <section class="panel" id="sec-index-vs-scan">
          <div class="panel-header">
            <div>
              <h2>2. Index vs. No-Index (Full Table Scan) &amp; Query Planner Cost Comparison</h2>
              <p class="panel-hint" style="margin:0.15rem 0 0;">
                Explore why a database query planner sometimes <strong>ignores an index</strong>
                (low selectivity on an unclustered index) and why—even when an index <strong>cannot seek</strong>
                (non-sargable predicate)—it still prefers a <strong>Full Index Leaf Scan</strong> over
                a Full Table Scan whenever the index is covering!
              </p>
            </div>
            <span class="verdict-pill is-ok">
              Planner Choice: ${escapeHtml(costCmp.winner.label)}
            </span>
          </div>

          <div class="presets-bar" style="margin-bottom:0.75rem;">
            <span class="presets-label">Planner Scenarios:</span>
            <div class="presets-list">
              ${INDEX_COST_PRESETS.map(
                (p) => `
                <button
                  type="button"
                  class="btn btn-chip ${p.id === activeCostPresetId ? "is-active-chip" : ""}"
                  data-cost-preset="${p.id}"
                >${escapeHtml(p.title)}</button>
              `
              ).join("")}
            </div>
          </div>

          <div class="der-subpanel" style="margin-bottom:0.85rem;">
            <div style="font-size:0.82rem;color:var(--text-muted);margin-bottom:0.25rem;">Example SQL Query:</div>
            <code style="font-size:0.88rem;">${escapeHtml(activeSqlExample)}</code>
          </div>

          <div class="der-norm-two-col" style="margin-bottom:0.85rem;">
            <!-- Controls -->
            <div class="der-subpanel">
              <div class="der-sub-header">
                <h3>Table, Index &amp; Query Parameters</h3>
              </div>

              <div style="display:grid;grid-template-columns:1fr 1fr;gap:0.6rem;font-size:0.83rem;">
                <label>
                  Total Rows (<code>N</code>): <strong>${costParams.totalRows.toLocaleString()}</strong>
                  <input type="range" min="10000" max="500000" step="10000" value="${costParams.totalRows}" data-cost-field="totalRows" style="width:100%;" />
                </label>

                <label>
                  Selectivity: <strong>${costParams.selectivityPct}%</strong> (${costCmp.matchingRows.toLocaleString()} rows)
                  <input type="range" min="0.1" max="60" step="0.5" value="${costParams.selectivityPct}" data-cost-field="selectivityPct" style="width:100%;" />
                </label>

                <label>
                  Heap Rows/Page: <strong>${costParams.rowsPerHeapPage}</strong> (${costCmp.heapPages.toLocaleString()} heap pages)
                  <input type="range" min="10" max="200" step="10" value="${costParams.rowsPerHeapPage}" data-cost-field="rowsPerHeapPage" style="width:100%;" />
                </label>

                <label>
                  Index Entries/Page: <strong>${costParams.entriesPerIndexPage}</strong> (${costCmp.indexLeafPages.toLocaleString()} leaf pages)
                  <input type="range" min="100" max="1000" step="50" value="${costParams.entriesPerIndexPage}" data-cost-field="entriesPerIndexPage" style="width:100%;" />
                </label>

                <label>
                  Random I/O Penalty: <strong>${costParams.randomIoMultiplier}×</strong> sequential
                  <input type="range" min="1" max="10" step="1" value="${costParams.randomIoMultiplier}" data-cost-field="randomIoMultiplier" style="width:100%;" />
                </label>

                <label>
                  B+ Tree Height (<code>h</code>): <strong>${costParams.treeHeight}</strong>
                  <input type="range" min="1" max="5" step="1" value="${costParams.treeHeight}" data-cost-field="treeHeight" style="width:100%;" />
                </label>
              </div>

              <div style="display:flex;gap:1.2rem;flex-wrap:wrap;margin-top:0.75rem;font-size:0.84rem;">
                <label class="checkbox-inline">
                  <input type="checkbox" data-cost-bool="indexCanSeek" ${costParams.indexCanSeek ? "checked" : ""} />
                  <span><strong>Index Can Seek</strong> (Sargable predicate on leading key)</span>
                </label>
                <label class="checkbox-inline">
                  <input type="checkbox" data-cost-bool="indexIsCovering" ${costParams.indexIsCovering ? "checked" : ""} />
                  <span><strong>Covering Index</strong> (All SELECT columns live in index leaves)</span>
                </label>
              </div>
            </div>

            <!-- Selectivity Crossover Chart -->
            <div class="der-subpanel">
              <div class="der-sub-header">
                <h3>Selectivity Crossover Curve (I/O Cost vs. % Rows Matched)</h3>
              </div>
              <div id="bp-crossover-chart-slot"></div>
              <div style="display:flex;gap:0.9rem;flex-wrap:wrap;font-size:0.76rem;margin-top:0.35rem;">
                <span><strong style="color:#2563eb;">━━</strong> Index Seek + Heap Fetch</span>
                <span><strong style="color:#d97706;">━━</strong> Full Table Scan (No Index)</span>
                <span><strong style="color:#059669;">╌╌</strong> Full Index Leaf Scan (Covering)</span>
              </div>
            </div>
          </div>

          <div class="der-ok-banner" style="margin-bottom:0.85rem;">
            <strong>Planner Insight:</strong> ${escapeHtml(costCmp.takeaway)}
          </div>

          <!-- Plan Cost Comparison Table & Bars -->
          <div class="table-scroll">
            <table class="data-table chase-table">
              <thead>
                <tr>
                  <th>Candidate Execution Plan</th>
                  <th>Status</th>
                  <th>Pages Touched</th>
                  <th>Effective I/O Cost</th>
                  <th>Relative Cost</th>
                  <th>Explanation</th>
                </tr>
              </thead>
              <tbody>
                ${costCmp.plans
                  .map((pl) => {
                    const isWinner = pl.id === costCmp.winner.id;
                    const pctWidth = pl.available
                      ? Math.max(4, Math.min(100, Math.round((pl.effectiveIoCost / maxPlanCost) * 100)))
                      : 0;
                    return `
                    <tr class="${isWinner ? "is-current" : ""}">
                      <td><strong>${escapeHtml(pl.label)}</strong></td>
                      <td>
                        <span class="nf-badge ${
                          isWinner ? "nf-bcnf" : pl.available ? "nf-2nf" : "nf-unf"
                        }">
                          ${isWinner ? "CHOSEN ✓" : pl.available ? "AVAILABLE" : "UNAVAILABLE ✗"}
                        </span>
                      </td>
                      <td><code>${pl.available ? pl.pagesRead.toLocaleString() : "—"}</code></td>
                      <td><code><strong>${pl.available ? pl.effectiveIoCost.toLocaleString() : "—"}</strong></code></td>
                      <td style="min-width:130px;">
                        ${
                          pl.available
                            ? `<div style="background:#e2e8f0;border-radius:4px;height:10px;overflow:hidden;">
                                 <div style="width:${pctWidth}%;height:100%;background:${
                                   isWinner ? "#059669" : "#64748b"
                                 };"></div>
                               </div>`
                            : `<span class="panel-meta">N/A</span>`
                        }
                      </td>
                      <td style="font-size:0.8rem;">${escapeHtml(pl.explanation)}</td>
                    </tr>
                  `;
                  })
                  .join("")}
              </tbody>
            </table>
          </div>
        </section>
      </div>
    `;

    // Mount B+ Tree SVG
    const svgHost = article.querySelector<HTMLElement>("#bp-svg-container")!;
    svgHost.appendChild(
      renderBPlusTreeSvg(tree, lastResult, (clickedKey) => {
        searchKeyInput = String(clickedKey);
        deleteKeyInput = String(clickedKey);
        lastResult = searchBPlusTree(tree, clickedKey);
        render();
      })
    );

    // Mount Crossover Chart SVG
    const chartHost = article.querySelector<HTMLElement>("#bp-crossover-chart-slot")!;
    chartHost.appendChild(renderCrossoverChartSvg(costParams));

    bindEvents();
  }

  function bindEvents(): void {
    // Change maxKeys (rebuilds current entries into a tree of new order)
    article.querySelectorAll<HTMLButtonElement>("[data-bp-maxkeys]").forEach((btn) => {
      btn.addEventListener("click", () => {
        const nextMax = Number(btn.dataset.bpMaxkeys);
        if (nextMax === tree.maxKeys) return;
        const current = allEntries(tree);
        resetNodeIds();
        let rebuilt = createEmptyBPlusTree(nextMax);
        for (const e of current) {
          rebuilt = insertBPlusTree(rebuilt, e.key, e.val).tree;
        }
        tree = rebuilt;
        activePresetId = "";
        lastResult = null;
        render();
      });
    });

    // Presets
    article.querySelectorAll<HTMLButtonElement>("[data-bp-preset]").forEach((btn) => {
      btn.addEventListener("click", () => {
        const found = BPLUS_PRESETS.find((p) => p.id === btn.dataset.bpPreset);
        if (!found) return;
        activePresetId = found.id;
        tree = buildTreeFromPreset(found);
        searchKeyInput = String(found.defaultSearch);
        rangeLoInput = String(found.defaultRange[0]);
        rangeHiInput = String(found.defaultRange[1]);
        deleteKeyInput = String(found.defaultDelete);
        lastResult = searchBPlusTree(tree, found.defaultSearch);
        render();
      });
    });

    // Clear tree
    article.querySelector<HTMLButtonElement>("[data-bp-clear]")?.addEventListener("click", () => {
      resetNodeIds();
      tree = createEmptyBPlusTree(tree.maxKeys);
      activePresetId = "";
      lastResult = null;
      render();
    });

    // Search
    article.querySelector<HTMLFormElement>("#bp-search-form")?.addEventListener("submit", (e) => {
      e.preventDefault();
      const fd = new FormData(e.currentTarget as HTMLFormElement);
      const k = Number(fd.get("searchKey"));
      if (!Number.isInteger(k)) return;
      searchKeyInput = String(k);
      lastResult = searchBPlusTree(tree, k);
      render();
    });

    // Range scan / iterate
    article.querySelector<HTMLFormElement>("#bp-range-form")?.addEventListener("submit", (e) => {
      e.preventDefault();
      const fd = new FormData(e.currentTarget as HTMLFormElement);
      const lo = Number(fd.get("lo"));
      const hi = Number(fd.get("hi"));
      if (!Number.isInteger(lo) || !Number.isInteger(hi)) return;
      rangeLoInput = String(lo);
      rangeHiInput = String(hi);
      lastResult = rangeScanBPlusTree(tree, Math.min(lo, hi), Math.max(lo, hi));
      render();
    });

    // Iterate full tree
    article.querySelector<HTMLButtonElement>("[data-bp-iterate-all]")?.addEventListener("click", () => {
      const ents = allEntries(tree);
      if (ents.length === 0) {
        lastResult = rangeScanBPlusTree(tree, 0, 0);
      } else {
        const lo = ents[0].key;
        const hi = ents[ents.length - 1].key;
        rangeLoInput = String(lo);
        rangeHiInput = String(hi);
        lastResult = rangeScanBPlusTree(tree, lo, hi);
      }
      render();
    });

    // Insert
    article.querySelector<HTMLFormElement>("#bp-insert-form")?.addEventListener("submit", (e) => {
      e.preventDefault();
      const fd = new FormData(e.currentTarget as HTMLFormElement);
      const k = Number(fd.get("key"));
      const v = Number(fd.get("val"));
      if (!Number.isInteger(k) || !Number.isInteger(v)) return;
      insertKeyInput = String(k);
      insertValInput = String(v);
      const res = insertBPlusTree(tree, k, v);
      tree = res.tree;
      lastResult = res;
      activePresetId = "";
      render();
    });

    // Delete
    article.querySelector<HTMLFormElement>("#bp-delete-form")?.addEventListener("submit", (e) => {
      e.preventDefault();
      const fd = new FormData(e.currentTarget as HTMLFormElement);
      const k = Number(fd.get("delKey"));
      if (!Number.isInteger(k)) return;
      deleteKeyInput = String(k);
      const res = deleteBPlusTree(tree, k);
      tree = res.tree;
      lastResult = res;
      activePresetId = "";
      render();
    });

    // Cost presets
    article.querySelectorAll<HTMLButtonElement>("[data-cost-preset]").forEach((btn) => {
      btn.addEventListener("click", () => {
        const found = INDEX_COST_PRESETS.find((p) => p.id === btn.dataset.costPreset);
        if (!found) return;
        activeCostPresetId = found.id;
        costParams = { ...found.params };
        activeSqlExample = found.sqlExample;
        render();
      });
    });

    // Cost sliders
    article.querySelectorAll<HTMLInputElement>("[data-cost-field]").forEach((inp) => {
      inp.addEventListener("input", () => {
        const field = inp.dataset.costField as keyof IndexCostParams;
        const val = Number(inp.value);
        if (!Number.isFinite(val)) return;
        (costParams[field] as number) = val;
        activeCostPresetId = "";
        render();
      });
    });

    // Cost checkboxes
    article.querySelectorAll<HTMLInputElement>("[data-cost-bool]").forEach((chk) => {
      chk.addEventListener("change", () => {
        const field = chk.dataset.costBool as "indexCanSeek" | "indexIsCovering";
        costParams[field] = chk.checked;
        activeCostPresetId = "";
        render();
      });
    });
  }

  render();
  return article;
}
