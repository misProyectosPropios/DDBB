// Interactive DER Diagram Editor, DER -> Relational Model Converter, and
// 1NF / 2NF / 3NF / BCNF Normalizer + Lossless-Join (Chase) & Dependency
// Preservation (Ullman) Workbench.
//
// Features:
//   - Interactive SVG canvas for Entities, Relations (1:1, 1:N, N:M, General
//     min..max), and Aggregations.
//   - Straight-line polyline connectors with user-generated and draggable
//     corners (click segment midpoint '+' or double-click segment to add a
//     corner; drag corner circles to reshape; right-click/double-click corner
//     to remove; or auto-generate 90-degree orthogonal corners).
//   - Persistent storage of DER diagrams (including all node positions,
//     line corners, and functional dependencies) in localStorage + JSON export.
//   - Live conversion from DER -> Relational Model + Generic SQL DDL.
//   - Live validation & conversion to 1NF, 2NF, 3NF (Bernstein synthesis),
//     and BCNF, plus Chase Tableau (Lossless-Join) and Ullman (Dependency
//     Preservation) verification.

import {
  cloneDiagram,
  convertDerToRelational,
  defaultCardinalitiesForClass,
  formatCardinality,
  generateGenericSqlDDL,
  loadSavedDiagrams,
  PRESET_DER_DIAGRAMS,
  relationKindOf,
  saveDiagramsToStorage
} from "../der/derToRelational";
import {
  convertDerToColumnModel,
  convertDerToDid,
  convertDerToGraphModel,
  convertDerToKeyValueModel,
  defaultDidConfig,
  effectiveIncrustation,
  formatDidDatabaseXml,
  formatDidMongoJson,
  getRelationRule,
  type DidConfig,
  type DidDocument,
  type DidField,
  type IncrustationMode,
  type NoSqlModelKind,
  type TableDeletionCheck
} from "../der/did";
import {
  analyzeDecomposition,
  attributeClosure,
  buildNormalizedRelationsFromRM,
  convertRelationToNormalForm,
  validateRelation
} from "../der/normalization";
import type {
  AttrTypeKind,
  Cardinality,
  ChaseCell,
  DerAggregation,
  DerDiagramData,
  DerElement,
  DerEntity,
  DerRelation,
  NormalForm,
  Point,
  RelationClassKind,
  TableSchema
} from "../der/types";

export type DerWorkbenchFocus =
  | "der"
  | "normalization"
  | "nosql-document"
  | "nosql-graph"
  | "nosql-column"
  | "nosql-keyvalue";

interface SelectionState {
  kind: "element" | "relation" | null;
  id: string | null;
}

interface DragState {
  mode: "element" | "relation" | "corner";
  id: string;
  leg?: "source" | "target";
  cornerIndex?: number;
  offsetX: number;
  offsetY: number;
}

const ATTR_TYPES: AttrTypeKind[] = [
  "INT",
  "STRING",
  "BOOL",
  "DATE",
  "DECIMAL",
  "SET<STRING>",
  "SET<INT>"
];

const SVG_NS = "http://www.w3.org/2000/svg";

function escapeHtml(s: string): string {
  return s
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}

function snapVal(v: number, snap: boolean): number {
  return snap ? Math.round(v / 10) * 10 : Math.round(v);
}

// Computes orthogonal (90-degree) corners between p1 and p2
function buildOrthogonalCorners(p1: Point, p2: Point): Point[] {
  const midX = Math.round((p1.x + p2.x) / 2);
  if (Math.abs(p1.x - p2.x) < 12 || Math.abs(p1.y - p2.y) < 12) {
    return [];
  }
  return [
    { x: midX, y: Math.round(p1.y) },
    { x: midX, y: Math.round(p2.y) }
  ];
}

export function renderDerPage(initialFocus: DerWorkbenchFocus = "der"): HTMLElement {
  const article = document.createElement("article");
  article.className = "blog-article der-article";

  let diagrams: DerDiagramData[] = loadSavedDiagrams();
  let currentDiagramIndex = initialFocus === "normalization" && diagrams.length > 1 ? 1 : 0;
  let selection: SelectionState = {
    kind: "element",
    id: diagrams[currentDiagramIndex]?.elements[0]?.id ?? null
  };
  let snapToGrid = true;
  let targetNormalForm: NormalForm = initialFocus === "normalization" ? "3NF" : "1NF";
  let selectedTableName: string | null = null;
  let closureInputCols: string[] = [];
  let customDecompInput = "";
  let showSqlModal = false;
  let didConfig: DidConfig = defaultDidConfig("DDBB_NoSQL");
  let activeNoSqlModel: NoSqlModelKind =
    initialFocus === "nosql-graph"
      ? "graph"
      : initialFocus === "nosql-column"
        ? "column"
        : initialFocus === "nosql-keyvalue"
          ? "keyvalue"
          : "document";
  let didOutputFormat: "xml" | "native" = "xml";

  const getDiagram = (): DerDiagramData => diagrams[currentDiagramIndex];

  const persist = (): void => {
    saveDiagramsToStorage(diagrams);
  };

  article.innerHTML = `
    <header class="article-header">
      <div class="breadcrumb">DDBB Notes / SQL Design &amp; Normalization</div>
      <h1>DER Editor, Relational Model &amp; Normalization (1NF–BCNF)</h1>
      <p class="article-lead">
        Build and store Entity-Relationship (DER) diagrams with <strong>1:1</strong>,
        <strong>1:N</strong>, <strong>N:M</strong>, <strong>General (min..max)</strong> relations,
        and composable <strong>Aggregations</strong>. Route straight connector lines with editable
        corners, convert automatically to the <strong>Relational Model (RM)</strong> and
        <strong>Generic SQL</strong>, and validate or normalize to <strong>1NF, 2NF, 3NF, and BCNF</strong>
        with <strong>Lossless-Join (Chase)</strong> and <strong>Dependency-Preservation (Ullman)</strong> proofs.
      </p>

      <div class="callout-rules">
        <div class="rule-card">
          <span class="rule-pill">DER → RM Rules</span>
          <p>
            Entities keep their exact PK; N:M relations become join tables with composite PKs of
            both endpoints; 1:N / 1:1 propagate FKs; Aggregations compose an inner relationship
            into a higher-level connectable table.
          </p>
        </div>
        <div class="rule-card">
          <span class="rule-pill">1NF · 2NF · 3NF · BCNF + Chase &amp; Ullman</span>
          <p>
            Backed by <code>dafny/der/Normalization.dfy</code> &amp;
            <code>DecompositionAnalysis.dfy</code>: checks candidate keys, partial/transitive FDs,
            synthesizes 3NF covers, decomposes to BCNF, and verifies zero information or FD loss.
          </p>
        </div>
      </div>
    </header>

    <div class="der-workbench">
      <!-- Diagram Storage Bar -->
      <section class="panel der-storage-bar">
        <div class="der-storage-row">
          <div class="der-storage-left">
            <label class="presets-label" for="der-diagram-select">Stored Diagram:</label>
            <select id="der-diagram-select" class="input input-sm der-select-wide"></select>
            <input id="der-diagram-title" type="text" class="input input-sm" placeholder="Diagram title" />
          </div>
          <div class="der-storage-actions">
            <button type="button" class="btn btn-secondary btn-sm" data-action="new-diagram">+ New Diagram</button>
            <button type="button" class="btn btn-secondary btn-sm" data-action="dup-diagram">Duplicate</button>
            <button type="button" class="btn btn-secondary btn-sm" data-action="delete-diagram">Delete</button>
            <button type="button" class="btn btn-secondary btn-sm" data-action="export-json">Export JSON</button>
            <button type="button" class="btn btn-secondary btn-sm" data-action="import-json">Import JSON</button>
            <button type="button" class="btn btn-secondary btn-sm" data-action="reset-presets">Reset Presets</button>
          </div>
        </div>
        <p class="panel-hint" id="der-diagram-desc" style="margin:0.45rem 0 0;"></p>
      </section>

      <!-- DER Canvas + Inspector Split -->
      <div class="der-editor-grid">
        <section class="panel der-canvas-panel">
          <div class="der-canvas-toolbar">
            <div class="der-toolbar-group">
              <button type="button" class="btn btn-primary btn-sm" data-action="add-entity">+ Entity</button>
              <button type="button" class="btn btn-secondary btn-sm" data-action="add-rel-11">+ 1:1 Rel</button>
              <button type="button" class="btn btn-secondary btn-sm" data-action="add-rel-1n">+ 1:N Rel</button>
              <button type="button" class="btn btn-secondary btn-sm" data-action="add-rel-nm">+ N:M Rel</button>
              <button type="button" class="btn btn-secondary btn-sm" data-action="add-rel-gen">+ General Rel</button>
              <button type="button" class="btn btn-secondary btn-sm" data-action="add-aggregation">+ Aggregation</button>
            </div>
            <div class="der-toolbar-group">
              <button type="button" class="btn btn-chip btn-sm" data-action="ortho-selected" title="Create 90-degree straight-line corners">
                ↱ 90° Corners
              </button>
              <button type="button" class="btn btn-chip btn-sm" data-action="clear-corners" title="Remove corners on selected relation">
                ╱ Straighten
              </button>
              <label class="der-snap-label">
                <input type="checkbox" id="der-snap-toggle" checked />
                Snap 10px
              </label>
            </div>
          </div>

          <div class="der-canvas-tip">
            <span><strong>Lines &amp; Corners:</strong> Click any green <code>+</code> midpoint (or double-click any straight line segment) to create a corner. Drag blue corner handles <code>●</code> to route lines; right-click or double-click a corner <code>●</code> to remove it.</span>
          </div>

          <div class="der-svg-wrapper">
            <svg id="der-canvas-svg" class="der-canvas-svg" viewBox="0 0 1050 580" preserveAspectRatio="xMidYMid meet"></svg>
          </div>
        </section>

        <!-- Inspector Panel -->
        <aside class="panel der-inspector-panel" id="der-inspector"></aside>
      </div>

      <!-- Step 2: Converted Relational Model (RM) & SQL DDL -->
      <section class="panel" id="der-rm-section"></section>

      <!-- Step 3: Normal Form Validator, Converter (1NF / 2NF / 3NF / BCNF) & Lossless / FD-Preservation Analysis -->
      <section class="panel" id="der-norm-section"></section>

      <!-- Step 4: NoSQL DID (Document Instance Diagram) & Mongo-Style XML Generator -->
      <section class="panel" id="der-did-section"></section>
    </div>
  `;

  const svgEl = article.querySelector<SVGSVGElement>("#der-canvas-svg")!;
  const inspectorEl = article.querySelector<HTMLElement>("#der-inspector")!;
  const rmSectionEl = article.querySelector<HTMLElement>("#der-rm-section")!;
  const normSectionEl = article.querySelector<HTMLElement>("#der-norm-section")!;
  const didSectionEl = article.querySelector<HTMLElement>("#der-did-section")!;
  const selectEl = article.querySelector<HTMLSelectElement>("#der-diagram-select")!;
  const titleInputEl = article.querySelector<HTMLInputElement>("#der-diagram-title")!;
  const descEl = article.querySelector<HTMLElement>("#der-diagram-desc")!;
  const snapToggleEl = article.querySelector<HTMLInputElement>("#der-snap-toggle")!;

  let dragState: DragState | null = null;

  function clientToSvgPoint(clientX: number, clientY: number): Point {
    const rect = svgEl.getBoundingClientRect();
    const vb = svgEl.viewBox.baseVal;
    const scaleX = vb.width / Math.max(rect.width, 1);
    const scaleY = vb.height / Math.max(rect.height, 1);
    return {
      x: Math.max(20, Math.min(vb.width - 20, (clientX - rect.left) * scaleX)),
      y: Math.max(20, Math.min(vb.height - 20, (clientY - rect.top) * scaleY))
    };
  }

  function findElementCenter(elem: DerElement, diagram: DerDiagramData): Point {
    if (elem.kind === "entity") {
      return elem.position;
    }
    const innerRel = diagram.relations.find((r) => r.id === elem.innerRelationId);
    if (!innerRel) return elem.position;
    return elem.position;
  }

  function getAggregationBounds(
    agg: DerAggregation,
    diagram: DerDiagramData
  ): { x: number; y: number; w: number; h: number; cx: number; cy: number } {
    const innerRel = diagram.relations.find((r) => r.id === agg.innerRelationId);
    if (!innerRel) {
      return {
        x: agg.position.x - 120,
        y: agg.position.y - 60,
        w: 240,
        h: 120,
        cx: agg.position.x,
        cy: agg.position.y
      };
    }
    const src = diagram.elements.find((e) => e.id === innerRel.sourceId);
    const dst = diagram.elements.find((e) => e.id === innerRel.targetId);
    const pts: Point[] = [
      innerRel.position,
      ...innerRel.sourceCorners,
      ...innerRel.targetCorners
    ];
    if (src) pts.push(src.position);
    if (dst) pts.push(dst.position);

    const xs = pts.map((p) => p.x);
    const ys = pts.map((p) => p.y);
    const minX = Math.min(...xs) - 95;
    const maxX = Math.max(...xs) + 95;
    const minY = Math.min(...ys) - 68;
    const maxY = Math.max(...ys) + 58;
    return {
      x: minX,
      y: minY,
      w: Math.max(220, maxX - minX),
      h: Math.max(125, maxY - minY),
      cx: Math.round((minX + maxX) / 2),
      cy: Math.round((minY + maxY) / 2)
    };
  }

  // -------------------------------------------------------------------------
  // Render Top Storage Bar
  // -------------------------------------------------------------------------

  function renderStorageBar(): void {
    const d = getDiagram();
    selectEl.innerHTML = diagrams
      .map(
        (diag, idx) =>
          `<option value="${idx}" ${idx === currentDiagramIndex ? "selected" : ""}>${escapeHtml(
            diag.title
          )}</option>`
      )
      .join("");
    titleInputEl.value = d.title;
    descEl.textContent = d.description;
  }

  // -------------------------------------------------------------------------
  // Render SVG DER Canvas (Straight Lines + Corner Handles + Nodes)
  // -------------------------------------------------------------------------

  function renderCanvas(): void {
    const diagram = getDiagram();
    svgEl.innerHTML = "";

    // Background grid pattern
    const defs = document.createElementNS(SVG_NS, "defs");
    defs.innerHTML = `
      <pattern id="der-grid-pattern" width="20" height="20" patternUnits="userSpaceOnUse">
        <path d="M 20 0 L 0 0 0 20" fill="none" stroke="#e2e8f0" stroke-width="0.75" />
      </pattern>
    `;
    svgEl.appendChild(defs);

    const bgRect = document.createElementNS(SVG_NS, "rect");
    bgRect.setAttribute("width", "1050");
    bgRect.setAttribute("height", "580");
    bgRect.setAttribute("fill", "url(#der-grid-pattern)");
    svgEl.appendChild(bgRect);

    // 1. Render Aggregation bounding frames first (background layer)
    for (const elem of diagram.elements) {
      if (elem.kind !== "aggregation") continue;
      const bounds = getAggregationBounds(elem, diagram);
      elem.position = { x: bounds.cx, y: bounds.cy };

      const isSelected = selection.kind === "element" && selection.id === elem.id;
      const g = document.createElementNS(SVG_NS, "g");
      g.setAttribute("class", `der-agg-group${isSelected ? " is-selected" : ""}`);

      const rect = document.createElementNS(SVG_NS, "rect");
      rect.setAttribute("x", String(bounds.x));
      rect.setAttribute("y", String(bounds.y));
      rect.setAttribute("width", String(bounds.w));
      rect.setAttribute("height", String(bounds.h));
      rect.setAttribute("rx", "12");
      rect.setAttribute("fill", isSelected ? "rgba(109, 40, 217, 0.07)" : "rgba(109, 40, 217, 0.035)");
      rect.setAttribute("stroke", isSelected ? "#6d28d9" : "#8b5cf6");
      rect.setAttribute("stroke-width", isSelected ? "2.4" : "1.8");
      rect.setAttribute("stroke-dasharray", "7 5");
      g.appendChild(rect);

      // Aggregation header pill
      const badge = document.createElementNS(SVG_NS, "rect");
      badge.setAttribute("x", String(bounds.x + 12));
      badge.setAttribute("y", String(bounds.y - 13));
      badge.setAttribute("width", String(Math.max(130, elem.name.length * 9 + 76)));
      badge.setAttribute("height", "24");
      badge.setAttribute("rx", "6");
      badge.setAttribute("fill", "#6d28d9");
      g.appendChild(badge);

      const label = document.createElementNS(SVG_NS, "text");
      label.setAttribute("x", String(bounds.x + 22));
      label.setAttribute("y", String(bounds.y + 3));
      label.setAttribute("fill", "#ffffff");
      label.setAttribute("font-size", "11.5");
      label.setAttribute("font-weight", "700");
      const attrSuffix =
        elem.attributes.length > 0
          ? ` (${elem.attributes.map((a) => a.name).join(", ")})`
          : "";
      label.textContent = `[AGG] ${elem.name}${attrSuffix}`;
      g.appendChild(label);

      g.addEventListener("mousedown", (ev) => {
        ev.stopPropagation();
        selection = { kind: "element", id: elem.id };
        renderCanvas();
        renderInspector();
      });

      svgEl.appendChild(g);
    }

    // 2. Render Straight Polyline Connectors & Corner Handles for each Relation
    for (const rel of diagram.relations) {
      const src = diagram.elements.find((e) => e.id === rel.sourceId);
      const dst = diagram.elements.find((e) => e.id === rel.targetId);
      if (!src || !dst) continue;

      const srcAnchor: Point =
        src.kind === "aggregation"
          ? (() => {
              const b = getAggregationBounds(src, diagram);
              return { x: b.cx, y: b.y + b.h };
            })()
          : findElementCenter(src, diagram);

      const dstAnchor: Point =
        dst.kind === "aggregation"
          ? (() => {
              const b = getAggregationBounds(dst, diagram);
              return { x: b.cx, y: b.y };
            })()
          : findElementCenter(dst, diagram);

      const isRelSelected = selection.kind === "relation" && selection.id === rel.id;

      renderPolylineLeg(
        rel,
        "source",
        [srcAnchor, ...rel.sourceCorners, rel.position],
        formatCardinality(rel.sourceCard),
        isRelSelected
      );
      renderPolylineLeg(
        rel,
        "target",
        [rel.position, ...rel.targetCorners, dstAnchor],
        formatCardinality(rel.targetCard),
        isRelSelected
      );
    }

    // 3. Render Relation Diamonds
    for (const rel of diagram.relations) {
      const isSelected = selection.kind === "relation" && selection.id === rel.id;
      const g = document.createElementNS(SVG_NS, "g");
      g.setAttribute("class", `der-rel-node${isSelected ? " is-selected" : ""}`);
      g.style.cursor = "grab";

      const { x, y } = rel.position;
      const rx = 56;
      const ry = 32;
      const points = `${x},${y - ry} ${x + rx},${y} ${x},${y + ry} ${x - rx},${y}`;

      const poly = document.createElementNS(SVG_NS, "polygon");
      poly.setAttribute("points", points);
      poly.setAttribute("fill", isSelected ? "#eff6ff" : "#ffffff");
      poly.setAttribute("stroke", isSelected ? "#2563eb" : "#334155");
      poly.setAttribute("stroke-width", isSelected ? "2.5" : "1.8");
      g.appendChild(poly);

      const nameText = document.createElementNS(SVG_NS, "text");
      nameText.setAttribute("x", String(x));
      nameText.setAttribute("y", String(y - 2));
      nameText.setAttribute("text-anchor", "middle");
      nameText.setAttribute("fill", "#0f172a");
      nameText.setAttribute("font-size", "12");
      nameText.setAttribute("font-weight", "700");
      nameText.textContent = rel.name;
      g.appendChild(nameText);

      const kindText = document.createElementNS(SVG_NS, "text");
      kindText.setAttribute("x", String(x));
      kindText.setAttribute("y", String(y + 13));
      kindText.setAttribute("text-anchor", "middle");
      kindText.setAttribute("fill", "#2563eb");
      kindText.setAttribute("font-size", "10");
      kindText.setAttribute("font-weight", "700");
      kindText.textContent = `[${relationKindOf(rel)}]`;
      g.appendChild(kindText);

      // Render relation attributes as a small pill below the diamond
      if (rel.attributes.length > 0) {
        const attrStr = rel.attributes.map((a) => `${a.name}: ${a.attrType}`).join(", ");
        const pillW = Math.max(84, attrStr.length * 6.2 + 16);
        const pill = document.createElementNS(SVG_NS, "rect");
        pill.setAttribute("x", String(x - pillW / 2));
        pill.setAttribute("y", String(y + ry + 5));
        pill.setAttribute("width", String(pillW));
        pill.setAttribute("height", "18");
        pill.setAttribute("rx", "9");
        pill.setAttribute("fill", "#f8fafc");
        pill.setAttribute("stroke", "#cbd5e1");
        g.appendChild(pill);

        const attrTxt = document.createElementNS(SVG_NS, "text");
        attrTxt.setAttribute("x", String(x));
        attrTxt.setAttribute("y", String(y + ry + 17));
        attrTxt.setAttribute("text-anchor", "middle");
        attrTxt.setAttribute("fill", "#475569");
        attrTxt.setAttribute("font-size", "10");
        attrTxt.textContent = attrStr;
        g.appendChild(attrTxt);
      }

      g.addEventListener("mousedown", (ev) => {
        ev.stopPropagation();
        const pt = clientToSvgPoint(ev.clientX, ev.clientY);
        selection = { kind: "relation", id: rel.id };
        dragState = {
          mode: "relation",
          id: rel.id,
          offsetX: pt.x - rel.position.x,
          offsetY: pt.y - rel.position.y
        };
        renderCanvas();
        renderInspector();
      });

      svgEl.appendChild(g);
    }

    // 4. Render Entity Boxes (with PK & attribute rows)
    for (const elem of diagram.elements) {
      if (elem.kind !== "entity") continue;
      const isSelected = selection.kind === "element" && selection.id === elem.id;
      const g = document.createElementNS(SVG_NS, "g");
      g.setAttribute("class", `der-entity-node${isSelected ? " is-selected" : ""}`);
      g.style.cursor = "grab";

      const w = 156;
      const rowH = 19;
      const headerH = 26;
      const attrCount = Math.max(1, elem.attributes.length);
      const h = headerH + attrCount * rowH + 8;
      const left = elem.position.x - w / 2;
      const top = elem.position.y - h / 2;

      const box = document.createElementNS(SVG_NS, "rect");
      box.setAttribute("x", String(left));
      box.setAttribute("y", String(top));
      box.setAttribute("width", String(w));
      box.setAttribute("height", String(h));
      box.setAttribute("rx", "7");
      box.setAttribute("fill", "#ffffff");
      box.setAttribute("stroke", isSelected ? "#2563eb" : elem.isWeak ? "#b45309" : "#0f172a");
      box.setAttribute("stroke-width", isSelected ? "2.5" : "1.8");
      g.appendChild(box);

      // Double-border inner frame for Weak Entities (classic ER notation)
      if (elem.isWeak) {
        const innerBox = document.createElementNS(SVG_NS, "rect");
        innerBox.setAttribute("x", String(left - 4));
        innerBox.setAttribute("y", String(top - 4));
        innerBox.setAttribute("width", String(w + 8));
        innerBox.setAttribute("height", String(h + 8));
        innerBox.setAttribute("rx", "9");
        innerBox.setAttribute("fill", "none");
        innerBox.setAttribute("stroke", isSelected ? "#2563eb" : "#b45309");
        innerBox.setAttribute("stroke-width", "1.5");
        innerBox.setAttribute("stroke-dasharray", "4 2");
        g.appendChild(innerBox);
      }

      const headerRect = document.createElementNS(SVG_NS, "rect");
      headerRect.setAttribute("x", String(left));
      headerRect.setAttribute("y", String(top));
      headerRect.setAttribute("width", String(w));
      headerRect.setAttribute("height", String(headerH));
      headerRect.setAttribute("rx", "6");
      headerRect.setAttribute("fill", isSelected ? "#2563eb" : elem.isWeak ? "#b45309" : "#0f172a");
      g.appendChild(headerRect);

      const title = document.createElementNS(SVG_NS, "text");
      title.setAttribute("x", String(elem.position.x));
      title.setAttribute("y", String(top + 17));
      title.setAttribute("text-anchor", "middle");
      title.setAttribute("fill", "#ffffff");
      title.setAttribute("font-size", "12.5");
      title.setAttribute("font-weight", "700");
      title.textContent = elem.isWeak ? `${elem.name} [WEAK]` : elem.name;
      g.appendChild(title);

      elem.attributes.forEach((attr, idx) => {
        const ay = top + headerH + 15 + idx * rowH;
        const txt = document.createElementNS(SVG_NS, "text");
        txt.setAttribute("x", String(left + 10));
        txt.setAttribute("y", String(ay));
        txt.setAttribute("font-size", "11");
        txt.setAttribute("fill", attr.isKey ? "#0f172a" : "#334155");
        if (attr.isKey) {
          txt.setAttribute("font-weight", "700");
          txt.setAttribute("text-decoration", "underline");
        }
        const prefix = attr.isKey ? "🔑 " : attr.attrType.startsWith("SET<") ? "◎ " : "• ";
        txt.textContent = `${prefix}${attr.name}: ${attr.attrType}`;
        g.appendChild(txt);
      });

      g.addEventListener("mousedown", (ev) => {
        ev.stopPropagation();
        const pt = clientToSvgPoint(ev.clientX, ev.clientY);
        selection = { kind: "element", id: elem.id };
        dragState = {
          mode: "element",
          id: elem.id,
          offsetX: pt.x - elem.position.x,
          offsetY: pt.y - elem.position.y
        };
        renderCanvas();
        renderInspector();
      });

      svgEl.appendChild(g);
    }
  }

  function renderPolylineLeg(
    rel: DerRelation,
    leg: "source" | "target",
    pts: Point[],
    cardLabel: string,
    isRelSelected: boolean
  ): void {
    const corners = leg === "source" ? rel.sourceCorners : rel.targetCorners;
    const pointsAttr = pts.map((p) => `${p.x},${p.y}`).join(" ");

    // Invisible wide hit-area polyline for easy clicking & double-clicking
    const hitPoly = document.createElementNS(SVG_NS, "polyline");
    hitPoly.setAttribute("points", pointsAttr);
    hitPoly.setAttribute("fill", "none");
    hitPoly.setAttribute("stroke", "transparent");
    hitPoly.setAttribute("stroke-width", "14");
    hitPoly.style.cursor = "pointer";

    hitPoly.addEventListener("mousedown", (ev) => {
      ev.stopPropagation();
      selection = { kind: "relation", id: rel.id };
      renderCanvas();
      renderInspector();
    });

    // Double-click anywhere along a straight segment to insert a corner at that point
    hitPoly.addEventListener("dblclick", (ev) => {
      ev.stopPropagation();
      const clickPt = clientToSvgPoint(ev.clientX, ev.clientY);
      const snapped: Point = {
        x: snapVal(clickPt.x, snapToGrid),
        y: snapVal(clickPt.y, snapToGrid)
      };
      // Find closest segment index
      let bestSeg = 0;
      let bestDist = Infinity;
      for (let i = 0; i < pts.length - 1; i++) {
        const mx = (pts[i].x + pts[i + 1].x) / 2;
        const my = (pts[i].y + pts[i + 1].y) / 2;
        const d = Math.hypot(clickPt.x - mx, clickPt.y - my);
        if (d < bestDist) {
          bestDist = d;
          bestSeg = i;
        }
      }
      corners.splice(bestSeg, 0, snapped);
      selection = { kind: "relation", id: rel.id };
      persist();
      renderCanvas();
      renderInspector();
    });

    // Visible straight-line polyline
    const poly = document.createElementNS(SVG_NS, "polyline");
    poly.setAttribute("points", pointsAttr);
    poly.setAttribute("fill", "none");
    poly.setAttribute("stroke", isRelSelected ? "#2563eb" : "#475569");
    poly.setAttribute("stroke-width", isRelSelected ? "2.6" : "2");
    poly.setAttribute("stroke-linejoin", "round");
    poly.setAttribute("stroke-linecap", "round");

    svgEl.appendChild(poly);
    svgEl.appendChild(hitPoly);

    // Cardinality badge near the entity endpoint
    const entityEnd = leg === "source" ? pts[0] : pts[pts.length - 1];
    const adjPoint = leg === "source" ? pts[1] : pts[pts.length - 2];
    const t = 0.42;
    const lx = Math.round(entityEnd.x + (adjPoint.x - entityEnd.x) * t);
    const ly = Math.round(entityEnd.y + (adjPoint.y - entityEnd.y) * t);

    const cardBg = document.createElementNS(SVG_NS, "rect");
    cardBg.setAttribute("x", String(lx - 18));
    cardBg.setAttribute("y", String(ly - 10));
    cardBg.setAttribute("width", "36");
    cardBg.setAttribute("height", "18");
    cardBg.setAttribute("rx", "5");
    cardBg.setAttribute("fill", "#ffffff");
    cardBg.setAttribute("stroke", isRelSelected ? "#93c5fd" : "#cbd5e1");
    svgEl.appendChild(cardBg);

    const cardTxt = document.createElementNS(SVG_NS, "text");
    cardTxt.setAttribute("x", String(lx));
    cardTxt.setAttribute("y", String(ly + 3));
    cardTxt.setAttribute("text-anchor", "middle");
    cardTxt.setAttribute("font-size", "10.5");
    cardTxt.setAttribute("font-weight", "700");
    cardTxt.setAttribute("fill", "#1e293b");
    cardTxt.textContent = cardLabel;
    svgEl.appendChild(cardTxt);

    // Midpoint '+' handles on every straight segment to generate a new corner with 1 click
    for (let segIdx = 0; segIdx < pts.length - 1; segIdx++) {
      const pA = pts[segIdx];
      const pB = pts[segIdx + 1];
      const dist = Math.hypot(pB.x - pA.x, pB.y - pA.y);
      if (dist < 42) continue;

      const mx = Math.round((pA.x + pB.x) / 2);
      const my = Math.round((pA.y + pB.y) / 2);

      const addGroup = document.createElementNS(SVG_NS, "g");
      addGroup.setAttribute(
        "class",
        `der-midpoint-handle${isRelSelected ? " is-visible" : ""}`
      );
      addGroup.style.cursor = "copy";

      const midCircle = document.createElementNS(SVG_NS, "circle");
      midCircle.setAttribute("cx", String(mx));
      midCircle.setAttribute("cy", String(my));
      midCircle.setAttribute("r", "7");
      midCircle.setAttribute("fill", "#ecfdf5");
      midCircle.setAttribute("stroke", "#059669");
      midCircle.setAttribute("stroke-width", "1.5");
      addGroup.appendChild(midCircle);

      const plusTxt = document.createElementNS(SVG_NS, "text");
      plusTxt.setAttribute("x", String(mx));
      plusTxt.setAttribute("y", String(my + 3.5));
      plusTxt.setAttribute("text-anchor", "middle");
      plusTxt.setAttribute("font-size", "11");
      plusTxt.setAttribute("font-weight", "700");
      plusTxt.setAttribute("fill", "#059669");
      plusTxt.textContent = "+";
      addGroup.appendChild(plusTxt);

      addGroup.addEventListener("mousedown", (ev) => {
        ev.stopPropagation();
        const newCorner: Point = {
          x: snapVal(mx, snapToGrid),
          y: snapVal(my, snapToGrid)
        };
        corners.splice(segIdx, 0, newCorner);
        selection = { kind: "relation", id: rel.id };
        dragState = {
          mode: "corner",
          id: rel.id,
          leg,
          cornerIndex: segIdx,
          offsetX: 0,
          offsetY: 0
        };
        persist();
        renderCanvas();
        renderInspector();
      });

      svgEl.appendChild(addGroup);
    }

    // Existing Corner Waypoint Handles ('●') — drag to move, right-click/double-click to delete
    corners.forEach((corner, cIdx) => {
      const handle = document.createElementNS(SVG_NS, "circle");
      handle.setAttribute("cx", String(corner.x));
      handle.setAttribute("cy", String(corner.y));
      handle.setAttribute("r", isRelSelected ? "6.5" : "5.5");
      handle.setAttribute("fill", "#2563eb");
      handle.setAttribute("stroke", "#ffffff");
      handle.setAttribute("stroke-width", "2");
      handle.style.cursor = "move";

      handle.addEventListener("mousedown", (ev) => {
        ev.stopPropagation();
        if (ev.button === 2) return;
        selection = { kind: "relation", id: rel.id };
        dragState = {
          mode: "corner",
          id: rel.id,
          leg,
          cornerIndex: cIdx,
          offsetX: 0,
          offsetY: 0
        };
        renderCanvas();
        renderInspector();
      });

      const removeCorner = (ev: MouseEvent) => {
        ev.preventDefault();
        ev.stopPropagation();
        corners.splice(cIdx, 1);
        persist();
        renderCanvas();
        renderInspector();
      };

      handle.addEventListener("contextmenu", removeCorner);
      handle.addEventListener("dblclick", removeCorner);

      svgEl.appendChild(handle);
    });
  }

  // Global SVG drag listeners
  svgEl.addEventListener("mousemove", (ev) => {
    if (!dragState) return;
    const pt = clientToSvgPoint(ev.clientX, ev.clientY);
    const diagram = getDiagram();

    if (dragState.mode === "element") {
      const elem = diagram.elements.find((e) => e.id === dragState!.id);
      if (elem && elem.kind === "entity") {
        elem.position = {
          x: snapVal(pt.x - dragState.offsetX, snapToGrid),
          y: snapVal(pt.y - dragState.offsetY, snapToGrid)
        };
        renderCanvas();
      }
    } else if (dragState.mode === "relation") {
      const rel = diagram.relations.find((r) => r.id === dragState!.id);
      if (rel) {
        rel.position = {
          x: snapVal(pt.x - dragState.offsetX, snapToGrid),
          y: snapVal(pt.y - dragState.offsetY, snapToGrid)
        };
        renderCanvas();
      }
    } else if (dragState.mode === "corner") {
      const rel = diagram.relations.find((r) => r.id === dragState!.id);
      if (rel && dragState.leg && dragState.cornerIndex !== undefined) {
        const arr =
          dragState.leg === "source" ? rel.sourceCorners : rel.targetCorners;
        if (arr[dragState.cornerIndex]) {
          arr[dragState.cornerIndex] = {
            x: snapVal(pt.x, snapToGrid),
            y: snapVal(pt.y, snapToGrid)
          };
          renderCanvas();
        }
      }
    }
  });

  window.addEventListener("mouseup", () => {
    if (dragState) {
      dragState = null;
      persist();
      renderInspector();
    }
  });

  // -------------------------------------------------------------------------
  // Render Right-Hand Inspector Panel
  // -------------------------------------------------------------------------

  function renderInspector(): void {
    const diagram = getDiagram();

    if (selection.kind === "element" && selection.id) {
      const elem = diagram.elements.find((e) => e.id === selection.id);
      if (elem) {
        renderElementInspector(elem, diagram);
        return;
      }
    }

    if (selection.kind === "relation" && selection.id) {
      const rel = diagram.relations.find((r) => r.id === selection.id);
      if (rel) {
        renderRelationInspector(rel, diagram);
        return;
      }
    }

    inspectorEl.innerHTML = `
      <div class="panel-header">
        <h2>Inspector</h2>
      </div>
      <p class="panel-hint">Click any Entity, Aggregation, Relation diamond, or line on the canvas to edit its properties, attributes, cardinalities, or line corners.</p>
    `;
  }

  function renderElementInspector(elem: DerElement, diagram: DerDiagramData): void {
    const isAgg = elem.kind === "aggregation";
    const attachedRels = diagram.relations.filter(
      (r) => r.sourceId === elem.id || r.targetId === elem.id
    );

    inspectorEl.innerHTML = `
      <div class="panel-header">
        <h2>${isAgg ? "Aggregation" : "Entity"} Inspector</h2>
        <button type="button" class="link-danger" data-del-elem>Delete</button>
      </div>

      <div class="der-form-group">
        <label class="der-field-label">Name</label>
        <input type="text" class="input input-sm" id="insp-elem-name" value="${escapeHtml(elem.name)}" />
      </div>

      ${
        !isAgg
          ? `
        <div class="der-form-group">
          <label class="der-pk-check" style="font-size:0.8rem;">
            <input type="checkbox" id="insp-elem-weak" ${
              (elem as DerEntity).isWeak ? "checked" : ""
            } />
            Weak Entity (Entidad Débil — candidate for complete incrustation &amp; table deletion)
          </label>
        </div>
      `
          : ""
      }

      ${
        isAgg
          ? `
        <div class="der-form-group">
          <label class="der-field-label">Composed Inner Relation</label>
          <select class="input input-sm" id="insp-agg-inner">
            ${diagram.relations
              .filter((r) => r.sourceId !== elem.id && r.targetId !== elem.id)
              .map(
                (r) =>
                  `<option value="${r.id}" ${
                    r.id === (elem as DerAggregation).innerRelationId ? "selected" : ""
                  }>${escapeHtml(r.name)} [${relationKindOf(r)}]</option>`
              )
              .join("")}
          </select>
        </div>
      `
          : ""
      }

      <div class="der-form-group">
        <div class="der-sub-header">
          <span class="der-field-label">Attributes (${elem.attributes.length})</span>
        </div>
        <ul class="der-attr-list">
          ${elem.attributes
            .map(
              (a, idx) => `
            <li class="der-attr-row">
              <label class="der-pk-check" title="Primary Key">
                <input type="checkbox" data-attr-pk="${idx}" ${a.isKey ? "checked" : ""} ${
                  isAgg ? "disabled" : ""
                } />
                PK
              </label>
              <input type="text" class="input input-sm der-attr-name-in" data-attr-name="${idx}" value="${escapeHtml(
                a.name
              )}" />
              <select class="input input-sm der-attr-type-in" data-attr-type="${idx}">
                ${ATTR_TYPES.map(
                  (t) => `<option value="${t}" ${t === a.attrType ? "selected" : ""}>${t}</option>`
                ).join("")}
              </select>
              <button type="button" class="icon-btn" data-del-attr="${idx}" title="Remove attribute">×</button>
            </li>
          `
            )
            .join("")}
        </ul>

        <form class="inline-form" id="insp-add-attr-form" style="margin-top:0.45rem;">
          <input type="text" class="input input-sm" id="new-attr-name" placeholder="attr_name" style="width:110px;" required />
          <select class="input input-sm" id="new-attr-type">
            ${ATTR_TYPES.map((t) => `<option value="${t}">${t}</option>`).join("")}
          </select>
          ${
            !isAgg
              ? `<label class="der-pk-check"><input type="checkbox" id="new-attr-pk" /> PK</label>`
              : ""
          }
          <button type="submit" class="btn btn-secondary btn-sm">+ Add</button>
        </form>
      </div>

      <div class="der-form-group">
        <span class="der-field-label">Attached Relations (${attachedRels.length})</span>
        <div class="der-chip-row">
          ${
            attachedRels.length === 0
              ? `<span class="panel-meta">None yet</span>`
              : attachedRels
                  .map(
                    (r) =>
                      `<button type="button" class="btn btn-chip btn-sm" data-select-rel="${r.id}">${escapeHtml(
                        r.name
                      )} [${relationKindOf(r)}]</button>`
                  )
                  .join("")
          }
        </div>
      </div>
    `;

    inspectorEl
      .querySelector<HTMLInputElement>("#insp-elem-name")
      ?.addEventListener("input", (ev) => {
        const val = (ev.target as HTMLInputElement).value.trim();
        if (val) {
          elem.name = val;
          persist();
          renderCanvas();
          renderRelationalAndNormalization();
          renderDidSection();
        }
      });

    inspectorEl
      .querySelector<HTMLInputElement>("#insp-elem-weak")
      ?.addEventListener("change", (ev) => {
        if (elem.kind === "entity") {
          elem.isWeak = (ev.target as HTMLInputElement).checked;
          persist();
          renderCanvas();
          renderDidSection();
        }
      });

    inspectorEl
      .querySelector<HTMLSelectElement>("#insp-agg-inner")
      ?.addEventListener("change", (ev) => {
        if (elem.kind === "aggregation") {
          elem.innerRelationId = (ev.target as HTMLSelectElement).value;
          persist();
          renderCanvas();
          renderRelationalAndNormalization();
        }
      });

    inspectorEl.querySelector("[data-del-elem]")?.addEventListener("click", () => {
      diagram.elements = diagram.elements.filter((e) => e.id !== elem.id);
      diagram.relations = diagram.relations.filter(
        (r) => r.sourceId !== elem.id && r.targetId !== elem.id
      );
      selection = {
        kind: "element",
        id: diagram.elements[0]?.id ?? null
      };
      persist();
      renderAll();
    });

    inspectorEl.querySelectorAll<HTMLInputElement>("[data-attr-pk]").forEach((cb) => {
      cb.addEventListener("change", () => {
        const idx = Number(cb.dataset.attrPk);
        elem.attributes[idx].isKey = cb.checked;
        persist();
        renderCanvas();
        renderRelationalAndNormalization();
      });
    });

    inspectorEl.querySelectorAll<HTMLInputElement>("[data-attr-name]").forEach((inp) => {
      inp.addEventListener("input", () => {
        const idx = Number(inp.dataset.attrName);
        const val = inp.value.trim();
        if (val) {
          elem.attributes[idx].name = val;
          persist();
          renderCanvas();
          renderRelationalAndNormalization();
        }
      });
    });

    inspectorEl.querySelectorAll<HTMLSelectElement>("[data-attr-type]").forEach((sel) => {
      sel.addEventListener("change", () => {
        const idx = Number(sel.dataset.attrType);
        elem.attributes[idx].attrType = sel.value as AttrTypeKind;
        persist();
        renderCanvas();
        renderRelationalAndNormalization();
      });
    });

    inspectorEl.querySelectorAll<HTMLButtonElement>("[data-del-attr]").forEach((btn) => {
      btn.addEventListener("click", () => {
        const idx = Number(btn.dataset.delAttr);
        elem.attributes.splice(idx, 1);
        persist();
        renderAll();
      });
    });

    inspectorEl
      .querySelector<HTMLFormElement>("#insp-add-attr-form")
      ?.addEventListener("submit", (ev) => {
        ev.preventDefault();
        const nameIn = inspectorEl.querySelector<HTMLInputElement>("#new-attr-name")!;
        const typeIn = inspectorEl.querySelector<HTMLSelectElement>("#new-attr-type")!;
        const pkIn = inspectorEl.querySelector<HTMLInputElement>("#new-attr-pk");
        const name = nameIn.value.trim();
        if (!name) return;
        elem.attributes.push({
          name,
          attrType: typeIn.value as AttrTypeKind,
          isKey: Boolean(pkIn?.checked)
        });
        persist();
        renderAll();
      });

    inspectorEl.querySelectorAll<HTMLButtonElement>("[data-select-rel]").forEach((btn) => {
      btn.addEventListener("click", () => {
        selection = { kind: "relation", id: btn.dataset.selectRel! };
        renderCanvas();
        renderInspector();
      });
    });
  }

  function renderRelationInspector(rel: DerRelation, diagram: DerDiagramData): void {
    const classOptions: { value: RelationClassKind; label: string }[] = [
      { value: "OneToOneRelation", label: "OneToOneRelation (1:1)" },
      { value: "OneToManyRelation", label: "OneToManyRelation (1:N)" },
      { value: "ManyToManyRelation", label: "ManyToManyRelation (N:M)" },
      { value: "GeneralRelation", label: "GeneralRelation (min..max)" }
    ];

    inspectorEl.innerHTML = `
      <div class="panel-header">
        <h2>Relation Inspector <code>[${relationKindOf(rel)}]</code></h2>
        <button type="button" class="link-danger" data-del-rel>Delete</button>
      </div>

      <div class="der-form-group">
        <label class="der-field-label">Relation Name</label>
        <input type="text" class="input input-sm" id="insp-rel-name" value="${escapeHtml(rel.name)}" />
      </div>

      <div class="der-form-group">
        <label class="der-field-label">Dafny Relation Class</label>
        <select class="input input-sm" id="insp-rel-class">
          ${classOptions
            .map(
              (o) =>
                `<option value="${o.value}" ${o.value === rel.classKind ? "selected" : ""}>${
                  o.label
                }</option>`
            )
            .join("")}
        </select>
      </div>

      <div class="der-two-col">
        <div class="der-form-group">
          <label class="der-field-label">Source Element</label>
          <select class="input input-sm" id="insp-rel-src">
            ${diagram.elements
              .map(
                (e) =>
                  `<option value="${e.id}" ${e.id === rel.sourceId ? "selected" : ""}>${escapeHtml(
                    e.name
                  )}</option>`
              )
              .join("")}
          </select>
        </div>
        <div class="der-form-group">
          <label class="der-field-label">Target Element</label>
          <select class="input input-sm" id="insp-rel-dst">
            ${diagram.elements
              .map(
                (e) =>
                  `<option value="${e.id}" ${e.id === rel.targetId ? "selected" : ""}>${escapeHtml(
                    e.name
                  )}</option>`
              )
              .join("")}
          </select>
        </div>
      </div>

      <div class="der-two-col">
        <div class="der-form-group">
          <label class="der-field-label">Source Card (min..max)</label>
          <div class="inline-form">
            <input type="number" min="0" class="input input-sm" id="insp-src-min" value="${
              rel.sourceCard.min
            }" style="width:58px;" />
            <span>..</span>
            <input type="text" class="input input-sm" id="insp-src-max" value="${
              rel.sourceCard.max
            }" style="width:58px;" title="Positive integer or *" />
          </div>
        </div>
        <div class="der-form-group">
          <label class="der-field-label">Target Card (min..max)</label>
          <div class="inline-form">
            <input type="number" min="0" class="input input-sm" id="insp-dst-min" value="${
              rel.targetCard.min
            }" style="width:58px;" />
            <span>..</span>
            <input type="text" class="input input-sm" id="insp-dst-max" value="${
              rel.targetCard.max
            }" style="width:58px;" title="Positive integer or *" />
          </div>
        </div>
      </div>

      <!-- Line Corners Editor -->
      <div class="der-form-group der-corners-box">
        <div class="der-sub-header">
          <span class="der-field-label">Straight-Line Corners (${
            rel.sourceCorners.length + rel.targetCorners.length
          })</span>
          <div class="inline-form">
            <button type="button" class="btn btn-chip btn-sm" data-add-src-corner>+ Src Corner</button>
            <button type="button" class="btn btn-chip btn-sm" data-add-dst-corner>+ Dst Corner</button>
          </div>
        </div>
        <div class="der-corners-list">
          ${rel.sourceCorners
            .map(
              (pt, idx) =>
                `<span class="der-corner-pill">Src #${idx + 1} (${pt.x}, ${pt.y}) <button type="button" data-del-src-c="${idx}">×</button></span>`
            )
            .join("")}
          ${rel.targetCorners
            .map(
              (pt, idx) =>
                `<span class="der-corner-pill">Dst #${idx + 1} (${pt.x}, ${pt.y}) <button type="button" data-del-dst-c="${idx}">×</button></span>`
            )
            .join("")}
          ${
            rel.sourceCorners.length + rel.targetCorners.length === 0
              ? `<span class="panel-meta">Direct straight lines (click '+' on canvas line or buttons above to add corners)</span>`
              : ""
          }
        </div>
      </div>

      <!-- Relation Attributes -->
      <div class="der-form-group">
        <span class="der-field-label">Relation Attributes (${rel.attributes.length})</span>
        <ul class="der-attr-list">
          ${rel.attributes
            .map(
              (a, idx) => `
            <li class="der-attr-row">
              <span class="panel-meta">${escapeHtml(a.name)}: ${a.attrType}</span>
              <button type="button" class="icon-btn" data-del-rel-attr="${idx}">×</button>
            </li>
          `
            )
            .join("")}
        </ul>
        <form class="inline-form" id="insp-add-rel-attr" style="margin-top:0.4rem;">
          <input type="text" class="input input-sm" id="rel-attr-name" placeholder="attr_name" style="width:110px;" required />
          <select class="input input-sm" id="rel-attr-type">
            ${ATTR_TYPES.map((t) => `<option value="${t}">${t}</option>`).join("")}
          </select>
          <button type="submit" class="btn btn-secondary btn-sm">+ Add</button>
        </form>
      </div>
    `;

    inspectorEl.querySelector("[data-del-rel]")?.addEventListener("click", () => {
      diagram.relations = diagram.relations.filter((r) => r.id !== rel.id);
      diagram.elements = diagram.elements.filter(
        (e) => !(e.kind === "aggregation" && e.innerRelationId === rel.id)
      );
      selection = { kind: "element", id: diagram.elements[0]?.id ?? null };
      persist();
      renderAll();
    });

    inspectorEl
      .querySelector<HTMLInputElement>("#insp-rel-name")
      ?.addEventListener("input", (ev) => {
        const val = (ev.target as HTMLInputElement).value.trim();
        if (val) {
          rel.name = val;
          persist();
          renderCanvas();
          renderRelationalAndNormalization();
        }
      });

    inspectorEl
      .querySelector<HTMLSelectElement>("#insp-rel-class")
      ?.addEventListener("change", (ev) => {
        const nextKind = (ev.target as HTMLSelectElement).value as RelationClassKind;
        rel.classKind = nextKind;
        const defaults = defaultCardinalitiesForClass(nextKind);
        rel.sourceCard = defaults.sourceCard;
        rel.targetCard = defaults.targetCard;
        persist();
        renderAll();
      });

    inspectorEl
      .querySelector<HTMLSelectElement>("#insp-rel-src")
      ?.addEventListener("change", (ev) => {
        rel.sourceId = (ev.target as HTMLSelectElement).value;
        persist();
        renderAll();
      });

    inspectorEl
      .querySelector<HTMLSelectElement>("#insp-rel-dst")
      ?.addEventListener("change", (ev) => {
        rel.targetId = (ev.target as HTMLSelectElement).value;
        persist();
        renderAll();
      });

    const parseCard = (minStr: string, maxStr: string, fallback: Cardinality): Cardinality => {
      const min = Math.max(0, parseInt(minStr, 10) || 0);
      const cleanMax = maxStr.trim();
      if (cleanMax === "*" || cleanMax.toUpperCase() === "N" || cleanMax.toUpperCase() === "M") {
        return { min, max: "*" };
      }
      const maxNum = parseInt(cleanMax, 10);
      if (!isNaN(maxNum) && maxNum >= 1 && maxNum >= min) {
        return { min, max: maxNum };
      }
      return fallback;
    };

    const syncCards = () => {
      const sMin = inspectorEl.querySelector<HTMLInputElement>("#insp-src-min")!.value;
      const sMax = inspectorEl.querySelector<HTMLInputElement>("#insp-src-max")!.value;
      const dMin = inspectorEl.querySelector<HTMLInputElement>("#insp-dst-min")!.value;
      const dMax = inspectorEl.querySelector<HTMLInputElement>("#insp-dst-max")!.value;
      rel.sourceCard = parseCard(sMin, sMax, rel.sourceCard);
      rel.targetCard = parseCard(dMin, dMax, rel.targetCard);
      rel.classKind = "GeneralRelation";
      persist();
      renderCanvas();
      renderRelationalAndNormalization();
    };

    ["#insp-src-min", "#insp-src-max", "#insp-dst-min", "#insp-dst-max"].forEach((sel) => {
      inspectorEl.querySelector(sel)?.addEventListener("change", syncCards);
    });

    inspectorEl.querySelector("[data-add-src-corner]")?.addEventListener("click", () => {
      const src = diagram.elements.find((e) => e.id === rel.sourceId);
      const start = src ? src.position : { x: rel.position.x - 100, y: rel.position.y };
      const last = rel.sourceCorners[rel.sourceCorners.length - 1] ?? start;
      rel.sourceCorners.push({
        x: snapVal((last.x + rel.position.x) / 2, snapToGrid),
        y: snapVal((last.y + rel.position.y) / 2 - 30, snapToGrid)
      });
      persist();
      renderCanvas();
      renderInspector();
    });

    inspectorEl.querySelector("[data-add-dst-corner]")?.addEventListener("click", () => {
      const dst = diagram.elements.find((e) => e.id === rel.targetId);
      const end = dst ? dst.position : { x: rel.position.x + 100, y: rel.position.y };
      const first = rel.targetCorners[0] ?? end;
      rel.targetCorners.unshift({
        x: snapVal((rel.position.x + first.x) / 2, snapToGrid),
        y: snapVal((rel.position.y + first.y) / 2 + 30, snapToGrid)
      });
      persist();
      renderCanvas();
      renderInspector();
    });

    inspectorEl.querySelectorAll<HTMLButtonElement>("[data-del-src-c]").forEach((btn) => {
      btn.addEventListener("click", () => {
        rel.sourceCorners.splice(Number(btn.dataset.delSrcC), 1);
        persist();
        renderCanvas();
        renderInspector();
      });
    });

    inspectorEl.querySelectorAll<HTMLButtonElement>("[data-del-dst-c]").forEach((btn) => {
      btn.addEventListener("click", () => {
        rel.targetCorners.splice(Number(btn.dataset.delDstC), 1);
        persist();
        renderCanvas();
        renderInspector();
      });
    });

    inspectorEl.querySelectorAll<HTMLButtonElement>("[data-del-rel-attr]").forEach((btn) => {
      btn.addEventListener("click", () => {
        rel.attributes.splice(Number(btn.dataset.delRelAttr), 1);
        persist();
        renderAll();
      });
    });

    inspectorEl
      .querySelector<HTMLFormElement>("#insp-add-rel-attr")
      ?.addEventListener("submit", (ev) => {
        ev.preventDefault();
        const nameIn = inspectorEl.querySelector<HTMLInputElement>("#rel-attr-name")!;
        const typeIn = inspectorEl.querySelector<HTMLSelectElement>("#rel-attr-type")!;
        const name = nameIn.value.trim();
        if (!name) return;
        rel.attributes.push({
          name,
          attrType: typeIn.value as AttrTypeKind,
          isKey: false
        });
        persist();
        renderAll();
      });
  }

  // -------------------------------------------------------------------------
  // Render Relational Model (RM) & Normalization (1NF / 2NF / 3NF / BCNF)
  // -------------------------------------------------------------------------

  function renderTableCard(t: TableSchema, badgeHtml = ""): string {
    const pkSet = new Set(t.primaryKey);
    const fkColSet = new Set(t.foreignKeys.flatMap((fk) => fk.columns));

    const colsHtml = t.columns
      .map((c) => {
        const isPk = pkSet.has(c.name);
        const isFk = fkColSet.has(c.name);
        const tag = isPk && isFk ? "PK, FK" : isPk ? "PK" : isFk ? "FK" : "";
        return `
          <span class="rm-col-chip${isPk ? " is-pk" : ""}${!c.colType.startsWith("SET<") ? "" : " is-multivalued"}">
            <span class="rm-col-name">${escapeHtml(c.name)}${isPk ? "*" : ""}</span>
            <span class="rm-col-type">${escapeHtml(c.colType)}</span>
            ${tag ? `<span class="rm-col-badge">${tag}</span>` : ""}
          </span>
        `;
      })
      .join("");

    const fksHtml =
      t.foreignKeys.length > 0
        ? `<div class="rm-fk-list">
            ${t.foreignKeys
              .map(
                (fk) =>
                  `<div class="rm-fk-item">↳ <code>FK (${escapeHtml(
                    fk.columns.join(", ")
                  )})</code> → <strong>${escapeHtml(fk.refTable)}</strong>(<code>${escapeHtml(
                    fk.refColumns.join(", ")
                  )}</code>)</div>`
              )
              .join("")}
          </div>`
        : "";

    return `
      <div class="rm-table-card">
        <div class="rm-table-header">
          <div>
            <span class="rm-table-name">${escapeHtml(t.name)}</span>
            <span class="rm-origin-pill">${t.originKind}</span>
          </div>
          <div>${badgeHtml}</div>
        </div>
        <div class="rm-cols-row">${colsHtml}</div>
        <div class="rm-pk-line"><strong>PK:</strong> (${escapeHtml(t.primaryKey.join(", "))})</div>
        ${fksHtml}
      </div>
    `;
  }

  function renderTableauHtml(
    title: string,
    tab: ChaseCell[][],
    colNames: string[],
    rowNames: string[]
  ): string {
    if (tab.length === 0 || colNames.length === 0) return "";
    return `
      <div class="chase-tableau-box">
        <div class="der-field-label" style="margin-bottom:0.3rem;">${escapeHtml(title)}</div>
        <div class="table-scroll">
          <table class="data-table chase-table">
            <thead>
              <tr>
                <th>Sub-Relation</th>
                ${colNames.map((c) => `<th>${escapeHtml(c)}</th>`).join("")}
              </tr>
            </thead>
            <tbody>
              ${tab
                .map((row, rIdx) => {
                  const allDist = row.every((c) => c.distinguished);
                  return `
                    <tr class="${allDist ? "chase-winning-row" : ""}">
                      <td><strong>${escapeHtml(rowNames[rIdx] ?? `R${rIdx + 1}`)}</strong> ${
                        allDist ? `<span class="verified-pill">All Distinguished ★</span>` : ""
                      }</td>
                      ${row
                        .map(
                          (cell) =>
                            `<td class="${
                              cell.distinguished ? "chase-cell-dist" : "chase-cell-sub"
                            }"><code>${escapeHtml(cell.label)}</code></td>`
                        )
                        .join("")}
                    </tr>
                  `;
                })
                .join("")}
            </tbody>
          </table>
        </div>
      </div>
    `;
  }

  function renderRelationalAndNormalization(): void {
    const diagram = getDiagram();
    const rm = convertDerToRelational(diagram);
    const normRelations = buildNormalizedRelationsFromRM(rm, diagram.extraFDsByTable);

    if (
      !selectedTableName ||
      !normRelations.some((r) => r.table.name === selectedTableName)
    ) {
      selectedTableName = normRelations[0]?.table.name ?? null;
    }

    const sqlDdl = generateGenericSqlDDL(rm.tables);

    // 1. Render Converted Relational Model section
    rmSectionEl.innerHTML = `
      <div class="panel-header">
        <div>
          <h2>Step 1 · Converted Relational Model (RM) — ${rm.tables.length} Tables</h2>
          <p class="panel-hint" style="margin:0.2rem 0 0;">
            Automatically converted from the DER above using <code>ConvertDerToRelational</code>
            (Entities, Aggregations, N:M composite-PK join tables, and 1:N / 1:1 Foreign Keys).
          </p>
        </div>
        <button type="button" class="btn btn-secondary btn-sm" id="toggle-sql-btn">
          ${showSqlModal ? "Hide Generic SQL DDL" : "Show Generic SQL DDL"}
        </button>
      </div>

      ${
        showSqlModal
          ? `<pre class="der-sql-pre"><code>${escapeHtml(sqlDdl)}</code></pre>`
          : ""
      }

      <div class="rm-tables-grid">
        ${rm.tables
          .map((t) => {
            const nr = normRelations.find((r) => r.table.name === t.name)!;
            const rep = validateRelation(nr);
            const badge = `<span class="nf-badge nf-${rep.highestForm.toLowerCase()}">${rep.highestForm}</span>`;
            return renderTableCard(t, badge);
          })
          .join("")}
      </div>
    `;

    rmSectionEl.querySelector("#toggle-sql-btn")?.addEventListener("click", () => {
      showSqlModal = !showSqlModal;
      renderRelationalAndNormalization();
    });

    // 2. Render Normalization & Decomposition Analysis Section
    const activeRel = normRelations.find((r) => r.table.name === selectedTableName);
    if (!activeRel) {
      normSectionEl.innerHTML = `<h2>Step 2 · Normalization &amp; Decomposition Analysis</h2><p class="panel-hint">Add at least one entity to begin.</p>`;
      return;
    }

    const activeCols = activeRel.table.columns.map((c) => c.name);
    closureInputCols = closureInputCols.filter((c) => activeCols.includes(c));
    if (closureInputCols.length === 0 && activeRel.table.primaryKey.length > 0) {
      closureInputCols = [...activeRel.table.primaryKey];
    }

    const closureResult = attributeClosure(closureInputCols, activeRel.fds, activeCols);
    const valReport = validateRelation(activeRel);
    const convertedRels = convertRelationToNormalForm(activeRel, targetNormalForm);
    const convertedReports = convertedRels.map((r) => validateRelation(r));

    const decompAttrSets = convertedRels.map((r) => r.table.columns.map((c) => c.name));
    const decompRowNames = convertedRels.map((r) => r.table.name);
    const decompReport = analyzeDecomposition(
      activeCols,
      decompAttrSets,
      decompRowNames,
      activeRel.fds
    );

    const extraFDs = diagram.extraFDsByTable[activeRel.table.name] ?? [];

    // Optional custom decomposition test
    let customDecompReportHtml = "";
    if (customDecompInput.trim()) {
      const customSets = customDecompInput
        .split(";")
        .map((part) =>
          part
            .split(",")
            .map((s) => s.trim())
            .filter((s) => s.length > 0)
        )
        .filter((arr) => arr.length > 0);
      if (customSets.length > 0) {
        const cNames = customSets.map((s, i) => `R${i + 1}(${s.join(",")})`);
        const cRep = analyzeDecomposition(activeCols, customSets, cNames, activeRel.fds);
        customDecompReportHtml = `
          <div class="der-custom-decomp-result">
            <div class="der-verdict-row">
              <span class="verdict-pill ${cRep.losslessJoin ? "is-ok" : "is-bad"}">
                Lossless-Join (No Info Loss): ${cRep.losslessJoin ? "YES ✓" : "NO ✗ (Lossy Join!)"}
              </span>
              <span class="verdict-pill ${cRep.dependencyPreserving ? "is-ok" : "is-warn"}">
                Dependency-Preserving: ${
                  cRep.dependencyPreserving
                    ? "YES ✓"
                    : `NO ✗ (Lost ${cRep.lostDependencies.length} FD)`
                }
              </span>
            </div>
            ${renderTableauHtml(
              "Custom Decomposition — Final Chase Tableau",
              cRep.finalTableau,
              cRep.tableauColNames,
              cRep.tableauRowNames
            )}
          </div>
        `;
      }
    }

    normSectionEl.innerHTML = `
      <div class="panel-header">
        <div>
          <h2>Step 2 · Normal Form Validator, Converter (1NF / 2NF / 3NF / BCNF) &amp; Lossless / FD Analysis</h2>
          <p class="panel-hint" style="margin:0.2rem 0 0;">
            Select any RM table below, add Functional Dependencies, validate its normal form,
            convert to <strong>1NF, 2NF, 3NF (Bernstein), or BCNF</strong>, and verify
            <strong>Lossless-Join (Chase)</strong> &amp; <strong>Dependency Preservation (Ullman)</strong>.
          </p>
        </div>
      </div>

      <!-- Table Selector Tabs -->
      <div class="der-table-tabs">
        <span class="presets-label">Inspect Table:</span>
        ${normRelations
          .map((r) => {
            const rep = validateRelation(r);
            const active = r.table.name === activeRel.table.name;
            return `
              <button type="button" class="btn btn-chip ${
                active ? "is-active-chip" : ""
              }" data-pick-table="${escapeHtml(r.table.name)}">
                ${escapeHtml(r.table.name)}
                <span class="nf-badge nf-${rep.highestForm.toLowerCase()}">${rep.highestForm}</span>
              </button>
            `;
          })
          .join("")}
      </div>

      <div class="der-norm-two-col">
        <!-- Left: Functional Dependencies & Attribute Closure -->
        <div class="der-subpanel">
          <div class="der-sub-header">
            <h3>Functional Dependencies on <code>${escapeHtml(activeRel.table.name)}</code></h3>
          </div>

          <ul class="der-fd-list">
            ${activeRel.fds
              .map(
                (fd, idx) => `
              <li class="der-fd-item">
                <code>{${escapeHtml(fd.lhs.join(", "))}} → {${escapeHtml(fd.rhs.join(", "))}}</code>
                ${
                  idx === 0
                    ? `<span class="panel-meta">(Table PK)</span>`
                    : `<button type="button" class="link-danger" data-del-fd="${
                        idx - 1
                      }">Remove</button>`
                }
              </li>
            `
              )
              .join("")}
          </ul>

          <form class="der-add-fd-form" id="add-fd-form">
            <div class="der-field-label">Add Functional Dependency (X → Y)</div>
            <div class="der-fd-inputs">
              <input type="text" class="input input-sm" id="fd-lhs-in" placeholder="LHS: e.g. padron" required />
              <span>→</span>
              <input type="text" class="input input-sm" id="fd-rhs-in" placeholder="RHS: e.g. nombre_alumno" required />
              <button type="submit" class="btn btn-primary btn-sm">+ Add FD</button>
            </div>
            <div class="panel-meta" style="margin-top:0.25rem;">
              Available columns: ${activeCols.map((c) => `<code>${escapeHtml(c)}</code>`).join(", ")}
            </div>
          </form>

          <!-- Interactive Attribute Closure X+ Calculator -->
          <div class="der-closure-box">
            <div class="der-field-label">Attribute Closure Calculator (X⁺)</div>
            <div class="der-chip-row" style="margin:0.35rem 0;">
              ${activeCols
                .map((col) => {
                  const on = closureInputCols.includes(col);
                  return `<button type="button" class="btn btn-chip btn-sm ${
                    on ? "is-active-chip" : ""
                  }" data-toggle-closure="${escapeHtml(col)}">${escapeHtml(col)}</button>`;
                })
                .join("")}
            </div>
            <div class="der-closure-result">
              <code>{${escapeHtml(closureInputCols.join(", "))}}⁺ = {${escapeHtml(
                closureResult.join(", ")
              )}}</code>
              ${
                closureResult.length === activeCols.length
                  ? `<span class="verified-pill" style="margin-left:0.4rem;">Superkey ✓</span>`
                  : ""
              }
            </div>
          </div>
        </div>

        <!-- Right: Normal Form Validator Report -->
        <div class="der-subpanel">
          <div class="der-sub-header">
            <h3>Normal Form Validator Report</h3>
            <span class="nf-badge nf-${valReport.highestForm.toLowerCase()}">Highest: ${
              valReport.highestForm
            }</span>
          </div>

          <div class="nf-checklist-grid">
            <div class="nf-check-card ${valReport.is1NF ? "is-pass" : "is-fail"}">
              <div class="nf-check-title">1st Normal Form (1NF)</div>
              <div class="nf-check-status">${valReport.is1NF ? "PASS ✓" : "FAIL ✗"}</div>
              <div class="nf-check-desc">All domains atomic (no repeating groups)</div>
            </div>
            <div class="nf-check-card ${valReport.is2NF ? "is-pass" : "is-fail"}">
              <div class="nf-check-title">2nd Normal Form (2NF)</div>
              <div class="nf-check-status">${valReport.is2NF ? "PASS ✓" : "FAIL ✗"}</div>
              <div class="nf-check-desc">1NF + no partial dependency on candidate key</div>
            </div>
            <div class="nf-check-card ${valReport.is3NF ? "is-pass" : "is-fail"}">
              <div class="nf-check-title">3rd Normal Form (3NF)</div>
              <div class="nf-check-status">${valReport.is3NF ? "PASS ✓" : "FAIL ✗"}</div>
              <div class="nf-check-desc">2NF + every non-trivial FD has superkey LHS or prime RHS</div>
            </div>
            <div class="nf-check-card ${valReport.isBCNF ? "is-pass" : "is-fail"}">
              <div class="nf-check-title">Boyce–Codd (BCNF)</div>
              <div class="nf-check-status">${valReport.isBCNF ? "PASS ✓" : "FAIL ✗"}</div>
              <div class="nf-check-desc">Every non-trivial FD determinant is a superkey</div>
            </div>
          </div>

          <div class="der-key-summary">
            <div><strong>Candidate Keys (${valReport.candidateKeys.length}):</strong> ${valReport.candidateKeys
              .map((ck) => `<code>{${escapeHtml(ck.join(", "))}}</code>`)
              .join(", ")}</div>
            <div><strong>Prime Attributes:</strong> ${
              valReport.primeAttributes.length > 0
                ? valReport.primeAttributes.map((a) => `<code>${escapeHtml(a)}</code>`).join(", ")
                : "none"
            }</div>
          </div>

          ${
            valReport.violations.length > 0
              ? `
            <div class="error-box" style="margin-top:0.65rem;">
              <strong>Detected Normal Form Violations:</strong>
              <ul>
                ${valReport.violations.map((v) => `<li>${escapeHtml(v)}</li>`).join("")}
              </ul>
            </div>
          `
              : `<div class="der-ok-banner">This table satisfies all normal forms up to <strong>BCNF</strong>!</div>`
          }
        </div>
      </div>

      <!-- Converter Target Normal Form Bar -->
      <div class="der-converter-bar">
        <div class="der-converter-header">
          <div>
            <h3>Convert <code>${escapeHtml(activeRel.table.name)}</code> to Target Normal Form</h3>
            <p class="panel-hint" style="margin:0.15rem 0 0;">
              Choose a target form below to decompose <code>${escapeHtml(
                activeRel.table.name
              )}</code> and inspect the resulting relations, Chase lossless-join tableau, and Ullman dependency preservation.
            </p>
          </div>
          <div class="segmented">
            ${(["1NF", "2NF", "3NF", "BCNF"] as NormalForm[])
              .map(
                (nf) => `
              <button type="button" class="segmented-btn ${
                targetNormalForm === nf ? "is-active" : ""
              }" data-target-nf="${nf}">
                Convert to ${nf}
              </button>
            `
              )
              .join("")}
          </div>
        </div>

        <!-- Decomposition Verdicts: No Loss of Information & No Loss of Dependency -->
        <div class="der-verdict-row">
          <span class="verdict-pill ${decompReport.losslessJoin ? "is-ok" : "is-bad"}">
            Lossless-Join (No Loss of Information — Chase Algorithm): ${
              decompReport.losslessJoin ? "YES ✓" : "NO ✗"
            }
          </span>
          <span class="verdict-pill ${decompReport.dependencyPreserving ? "is-ok" : "is-warn"}">
            Dependency-Preserving (No Loss of Dependency — Ullman Algorithm): ${
              decompReport.dependencyPreserving
                ? "YES ✓"
                : `NO ✗ (Lost: ${decompReport.lostDependencies
                    .map((fd) => `{${fd.lhs.join(",")}}->{${fd.rhs.join(",")}}`)
                    .join("; ")})`
            }
          </span>
        </div>

        <!-- Decomposed Resulting Tables -->
        <div class="rm-tables-grid" style="margin-top:0.85rem;">
          ${convertedRels
            .map((r, idx) => {
              const rep = convertedReports[idx];
              const fdsText = r.fds
                .map((fd) => `{${fd.lhs.join(", ")}} → {${fd.rhs.join(", ")}}`)
                .join("; ");
              const badge = `<span class="nf-badge nf-${rep.highestForm.toLowerCase()}">${rep.highestForm} ✓</span>`;
              return `
                <div>
                  ${renderTableCard(r.table, badge)}
                  <div class="panel-meta" style="margin-top:0.25rem;padding:0 0.25rem;">
                    <strong>Projected FDs:</strong> <code>${escapeHtml(fdsText)}</code>
                  </div>
                </div>
              `;
            })
            .join("")}
        </div>

        <!-- Chase Algorithm Tableau Visualization -->
        <div class="der-tableau-grid">
          ${renderTableauHtml(
            "Initial Chase Tableau (before applying FDs)",
            decompReport.initialTableau,
            decompReport.tableauColNames,
            decompReport.tableauRowNames
          )}
          ${renderTableauHtml(
            "Final Chase Tableau (row with all 'a' proves Lossless-Join)",
            decompReport.finalTableau,
            decompReport.tableauColNames,
            decompReport.tableauRowNames
          )}
        </div>

        <!-- Custom Decomposition Lossless / FD-Preservation Tester -->
        <div class="der-custom-decomp-box">
          <div class="der-field-label">Test Custom Decomposition on <code>${escapeHtml(
            activeRel.table.name
          )}</code> (verify Lossless-Join &amp; Dependency Preservation)</div>
          <div class="inline-form" style="margin-top:0.35rem;">
            <input
              type="text"
              class="input input-sm"
              id="custom-decomp-in"
              style="flex:1;min-width:260px;"
              placeholder="Semicolon-separated sub-schemas, e.g. ${escapeHtml(
                activeCols.slice(0, 2).join(", ")
              )}; ${escapeHtml(activeCols.slice(1).join(", "))}"
              value="${escapeHtml(customDecompInput)}"
            />
            <button type="button" class="btn btn-secondary btn-sm" id="run-custom-decomp">
              Analyze Custom Split
            </button>
            <button type="button" class="btn btn-chip btn-sm" id="load-lossy-example">
              Try Lossy Split Example
            </button>
          </div>
          ${customDecompReportHtml}
        </div>
      </div>
    `;

    // Wire events in Normalization Section
    normSectionEl.querySelectorAll<HTMLButtonElement>("[data-pick-table]").forEach((btn) => {
      btn.addEventListener("click", () => {
        selectedTableName = btn.dataset.pickTable!;
        closureInputCols = [];
        customDecompInput = "";
        renderRelationalAndNormalization();
      });
    });

    normSectionEl.querySelectorAll<HTMLButtonElement>("[data-del-fd]").forEach((btn) => {
      btn.addEventListener("click", () => {
        const idx = Number(btn.dataset.delFd);
        const list = diagram.extraFDsByTable[activeRel.table.name] ?? [];
        list.splice(idx, 1);
        diagram.extraFDsByTable[activeRel.table.name] = list;
        persist();
        renderRelationalAndNormalization();
      });
    });

    normSectionEl
      .querySelector<HTMLFormElement>("#add-fd-form")
      ?.addEventListener("submit", (ev) => {
        ev.preventDefault();
        const lhsRaw = normSectionEl.querySelector<HTMLInputElement>("#fd-lhs-in")!.value;
        const rhsRaw = normSectionEl.querySelector<HTMLInputElement>("#fd-rhs-in")!.value;
        const lhs = lhsRaw
          .split(",")
          .map((s) => s.trim())
          .filter((s) => activeCols.includes(s));
        const rhs = rhsRaw
          .split(",")
          .map((s) => s.trim())
          .filter((s) => activeCols.includes(s));
        if (lhs.length === 0 || rhs.length === 0) return;

        const list = diagram.extraFDsByTable[activeRel.table.name] ?? [...extraFDs];
        list.push({
          id: `fd-${Date.now()}`,
          lhs,
          rhs
        });
        diagram.extraFDsByTable[activeRel.table.name] = list;
        persist();
        renderRelationalAndNormalization();
      });

    normSectionEl.querySelectorAll<HTMLButtonElement>("[data-toggle-closure]").forEach((btn) => {
      btn.addEventListener("click", () => {
        const col = btn.dataset.toggleClosure!;
        if (closureInputCols.includes(col)) {
          if (closureInputCols.length > 1) {
            closureInputCols = closureInputCols.filter((c) => c !== col);
          }
        } else {
          closureInputCols = [...closureInputCols, col];
        }
        renderRelationalAndNormalization();
      });
    });

    normSectionEl.querySelectorAll<HTMLButtonElement>("[data-target-nf]").forEach((btn) => {
      btn.addEventListener("click", () => {
        targetNormalForm = btn.dataset.targetNf as NormalForm;
        renderRelationalAndNormalization();
      });
    });

    normSectionEl.querySelector("#run-custom-decomp")?.addEventListener("click", () => {
      customDecompInput =
        normSectionEl.querySelector<HTMLInputElement>("#custom-decomp-in")?.value ?? "";
      renderRelationalAndNormalization();
    });

    normSectionEl.querySelector("#load-lossy-example")?.addEventListener("click", () => {
      if (activeCols.length >= 2) {
        const nonKeyCol = activeCols[activeCols.length - 1];
        const left = [activeCols[0], nonKeyCol];
        const right = activeCols.slice(1);
        customDecompInput = `${left.join(", ")}; ${right.join(", ")}`;
        renderRelationalAndNormalization();
      }
    });
  }

  // -------------------------------------------------------------------------
  // Wire Top Storage & Canvas Toolbar Actions
  // -------------------------------------------------------------------------

  selectEl.addEventListener("change", () => {
    currentDiagramIndex = Number(selectEl.value);
    selection = {
      kind: "element",
      id: getDiagram().elements[0]?.id ?? null
    };
    selectedTableName = null;
    customDecompInput = "";
    renderAll();
  });

  titleInputEl.addEventListener("input", () => {
    const val = titleInputEl.value.trim();
    if (val) {
      getDiagram().title = val;
      persist();
      renderStorageBar();
    }
  });

  snapToggleEl.addEventListener("change", () => {
    snapToGrid = snapToggleEl.checked;
  });

  function addRelationWithClass(classKind: RelationClassKind): void {
    const diagram = getDiagram();
    if (diagram.elements.length === 0) return;
    const src =
      (selection.kind === "element" &&
        diagram.elements.find((e) => e.id === selection.id)) ||
      diagram.elements[0];
    const dst =
      diagram.elements.find((e) => e.id !== src.id) ?? src;
    const cards = defaultCardinalitiesForClass(classKind);
    const id = `rel-${Date.now()}`;
    const midX = snapVal((src.position.x + dst.position.x) / 2, snapToGrid);
    const midY = snapVal((src.position.y + dst.position.y) / 2 + 20, snapToGrid);

    const newRel: DerRelation = {
      id,
      name: `Rel_${diagram.relations.length + 1}`,
      classKind,
      sourceId: src.id,
      targetId: dst.id,
      sourceCard: cards.sourceCard,
      targetCard: cards.targetCard,
      attributes: [],
      position: { x: midX, y: midY },
      sourceCorners: [],
      targetCorners: []
    };
    diagram.relations.push(newRel);
    selection = { kind: "relation", id: newRel.id };
    persist();
    renderAll();
  }

  article.querySelectorAll<HTMLButtonElement>("[data-action]").forEach((btn) => {
    btn.addEventListener("click", () => {
      const action = btn.dataset.action;
      const diagram = getDiagram();

      switch (action) {
        case "new-diagram": {
          const fresh: DerDiagramData = {
            id: `diag-${Date.now()}`,
            title: `Custom DER #${diagrams.length + 1}`,
            description: "Custom DER diagram stored in browser localStorage.",
            elements: [
              {
                id: `ent-${Date.now()}-1`,
                kind: "entity",
                name: "EntidadA",
                position: { x: 220, y: 220 },
                attributes: [
                  { name: "id_a", attrType: "INT", isKey: true },
                  { name: "nombre", attrType: "STRING", isKey: false }
                ]
              },
              {
                id: `ent-${Date.now()}-2`,
                kind: "entity",
                name: "EntidadB",
                position: { x: 640, y: 220 },
                attributes: [
                  { name: "id_b", attrType: "INT", isKey: true },
                  { name: "detalle", attrType: "STRING", isKey: false }
                ]
              }
            ],
            relations: [],
            extraFDsByTable: {}
          };
          diagrams.push(fresh);
          currentDiagramIndex = diagrams.length - 1;
          selection = { kind: "element", id: fresh.elements[0].id };
          persist();
          renderAll();
          break;
        }
        case "dup-diagram": {
          const copy = cloneDiagram(diagram);
          copy.id = `diag-${Date.now()}`;
          copy.title = `${diagram.title} (Copy)`;
          diagrams.push(copy);
          currentDiagramIndex = diagrams.length - 1;
          persist();
          renderAll();
          break;
        }
        case "delete-diagram": {
          if (diagrams.length <= 1) return;
          diagrams.splice(currentDiagramIndex, 1);
          currentDiagramIndex = Math.max(0, currentDiagramIndex - 1);
          selection = { kind: "element", id: getDiagram().elements[0]?.id ?? null };
          persist();
          renderAll();
          break;
        }
        case "reset-presets": {
          diagrams = PRESET_DER_DIAGRAMS.map(cloneDiagram);
          currentDiagramIndex = 0;
          selection = { kind: "element", id: diagrams[0].elements[0]?.id ?? null };
          persist();
          renderAll();
          break;
        }
        case "export-json": {
          const blob = new Blob([JSON.stringify(diagram, null, 2)], {
            type: "application/json"
          });
          const url = URL.createObjectURL(blob);
          const a = document.createElement("a");
          a.href = url;
          a.download = `${diagram.title.replace(/[^a-z0-9]+/gi, "_").toLowerCase()}.der.json`;
          a.click();
          URL.revokeObjectURL(url);
          break;
        }
        case "import-json": {
          const input = document.createElement("input");
          input.type = "file";
          input.accept = "application/json,.json";
          input.addEventListener("change", () => {
            const file = input.files?.[0];
            if (!file) return;
            const reader = new FileReader();
            reader.onload = () => {
              try {
                const parsed = JSON.parse(String(reader.result)) as DerDiagramData;
                if (parsed && Array.isArray(parsed.elements) && Array.isArray(parsed.relations)) {
                  diagrams.push(parsed);
                  currentDiagramIndex = diagrams.length - 1;
                  persist();
                  renderAll();
                }
              } catch {
                // Invalid JSON ignored
              }
            };
            reader.readAsText(file);
          });
          input.click();
          break;
        }
        case "add-entity": {
          const idx = diagram.elements.filter((e) => e.kind === "entity").length + 1;
          const newEnt: DerEntity = {
            id: `ent-${Date.now()}`,
            kind: "entity",
            name: `Entidad${idx}`,
            position: {
              x: snapVal(180 + ((idx * 150) % 680), snapToGrid),
              y: snapVal(140 + ((idx * 95) % 340), snapToGrid)
            },
            attributes: [
              { name: `id_${idx}`, attrType: "INT", isKey: true },
              { name: "descripcion", attrType: "STRING", isKey: false }
            ]
          };
          diagram.elements.push(newEnt);
          selection = { kind: "element", id: newEnt.id };
          persist();
          renderAll();
          break;
        }
        case "add-rel-11":
          addRelationWithClass("OneToOneRelation");
          break;
        case "add-rel-1n":
          addRelationWithClass("OneToManyRelation");
          break;
        case "add-rel-nm":
          addRelationWithClass("ManyToManyRelation");
          break;
        case "add-rel-gen":
          addRelationWithClass("GeneralRelation");
          break;
        case "add-aggregation": {
          if (diagram.relations.length === 0) return;
          const targetRel =
            (selection.kind === "relation" &&
              diagram.relations.find((r) => r.id === selection.id)) ||
            diagram.relations[0];
          const newAgg: DerAggregation = {
            id: `agg-${Date.now()}`,
            kind: "aggregation",
            name: `Agregacion_${targetRel.name}`,
            innerRelationId: targetRel.id,
            position: { ...targetRel.position },
            attributes: []
          };
          diagram.elements.push(newAgg);
          selection = { kind: "element", id: newAgg.id };
          persist();
          renderAll();
          break;
        }
        case "ortho-selected": {
          const targetRels =
            selection.kind === "relation" && selection.id
              ? diagram.relations.filter((r) => r.id === selection.id)
              : diagram.relations;
          for (const rel of targetRels) {
            const src = diagram.elements.find((e) => e.id === rel.sourceId);
            const dst = diagram.elements.find((e) => e.id === rel.targetId);
            if (src) {
              rel.sourceCorners = buildOrthogonalCorners(src.position, rel.position);
            }
            if (dst) {
              rel.targetCorners = buildOrthogonalCorners(rel.position, dst.position);
            }
          }
          persist();
          renderCanvas();
          renderInspector();
          break;
        }
        case "clear-corners": {
          const targetRels =
            selection.kind === "relation" && selection.id
              ? diagram.relations.filter((r) => r.id === selection.id)
              : diagram.relations;
          for (const rel of targetRels) {
            rel.sourceCorners = [];
            rel.targetCorners = [];
          }
          persist();
          renderCanvas();
          renderInspector();
          break;
        }
      }
    });
  });

  function renderDidFieldHtml(f: DidField): string {
    switch (f.kind) {
      case "scalar":
        return `
          <div class="did-tree-item">
            <span class="did-field-tag">${f.isKey ? "🔑 _id" : "• field"}</span>
            <code>${escapeHtml(f.name)}</code>:
            <span class="rm-col-type">${escapeHtml(f.attrType)}</span>
          </div>
        `;
      case "multivalued":
        return `
          <div class="did-tree-item">
            <span class="did-field-tag is-array">[ ] array</span>
            <code>${escapeHtml(f.name)}</code>:
            <span class="rm-col-type">ARRAY&lt;${escapeHtml(f.elemType)}&gt;</span>
          </div>
        `;
      case "reference":
        return `
          <div class="did-tree-item is-ref">
            <span class="did-field-tag is-ref-tag">${
              f.isArray ? "↗ RefArray (None)" : "↗ DBRef (None)"
            }</span>
            <strong>${escapeHtml(f.relName)}</strong> <code>[${f.relKind}]</code> →
            collection <code>${escapeHtml(f.targetCollection)}</code>
            (${f.targetKeys.map((k) => `${f.targetCollection}_${k.name}`).join(", ")})
            ${
              f.relAttributes.length > 0
                ? ` + attrs(${f.relAttributes.map((a) => a.name).join(", ")})`
                : ""
            }
          </div>
        `;
      case "partial-incrustation":
        return `
          <div class="did-tree-item is-partial-inc">
            <span class="did-field-tag is-partial-tag">${
              f.isArray ? "◐ PartialIncrustation[]" : "◐ PartialIncrustation"
            }</span>
            <strong>${escapeHtml(f.relName)}</strong> <code>[${f.relKind}]</code> →
            ref <code>${escapeHtml(f.targetCollection)}</code>
            (${f.targetKeys.map((k) => `${f.targetCollection}_${k.name}`).join(", ")}) +
            <strong>incrusted:</strong> { ${f.incrustedAttributes
              .map((a) => `<code>${escapeHtml(a.name)}: ${escapeHtml(a.attrType)}</code>`)
              .join(", ")} }
          </div>
        `;
      case "embedded":
        return `
          <div class="did-embedded-box">
            <div class="did-embedded-header">
              <span class="did-field-tag is-embed-tag">${
                f.isArray ? "⊞ Complete Incrustation[]" : "⊞ Complete Incrustation"
              }</span>
              <strong>${escapeHtml(f.relName)}</strong> <code>[${f.relKind}]</code> →
              embeds <code>${escapeHtml(f.childDoc.docName)}</code>
              ${
                f.absorbedTable
                  ? `<span class="verdict-pill is-ok" style="padding:0.08rem 0.45rem;font-size:0.68rem;">Table Deleted &amp; Absorbed ✓</span>`
                  : ""
              }
              ${
                f.relAttributes.length > 0
                  ? `<span class="panel-meta">(rel attrs: ${escapeHtml(
                      f.relAttributes.map((a) => a.name).join(", ")
                    )})</span>`
                  : ""
              }
            </div>
            ${renderDidDocHtml(f.childDoc)}
          </div>
        `;
    }
  }

  function renderDidDocHtml(doc: DidDocument): string {
    return `
      <div class="did-doc-tree">
        <div class="did-id-line">
          <strong>_id:</strong> { ${doc.idFields
            .map((k) => `<code>${escapeHtml(k.name)}: ${escapeHtml(k.attrType)}</code>`)
            .join(", ")} }
          ${doc.isWeak ? `<span class="rm-origin-pill">Weak Entity</span>` : ""}
        </div>
        <div class="did-fields-list">
          ${doc.fields.map(renderDidFieldHtml).join("")}
        </div>
      </div>
    `;
  }

  function renderDeletedTablesBanner(deleted: TableDeletionCheck[]): string {
    if (deleted.length === 0) {
      return `
        <div class="panel-hint" style="background:var(--bg-subtle);padding:0.45rem 0.7rem;border-radius:7px;border:1px solid var(--border);margin-bottom:0.85rem;">
          <strong>Active Standalone Tables:</strong> All DER entities currently remain standalone tables/collections. To absorb and delete a table (such as a <strong>Weak Entity</strong>), set its incoming relation to <strong>Complete Incrustation</strong> and check <strong>Delete Target Table</strong>.
        </div>
      `;
    }
    return `
      <div class="der-ok-banner" style="margin:0 0 0.85rem;">
        <strong>Absorbed &amp; Deleted Standalone Tables (${deleted.length}):</strong>
        ${deleted
          .map(
            (d) =>
              `<span class="rm-col-chip" style="background:#ffffff;margin-left:0.35rem;">
                🗑 <s><strong>${escapeHtml(d.targetName)}</strong></s> ${
                  d.isWeak ? "(Weak Entity)" : ""
                } → absorbed into <strong>${escapeHtml(d.absorbedInto.join(", "))}</strong>
              </span>`
          )
          .join("")}
      </div>
    `;
  }

  function renderDidSection(): void {
    const diagram = getDiagram();
    const didDb = convertDerToDid(diagram, didConfig);
    const graphOut = convertDerToGraphModel(diagram, didConfig);
    const colOut = convertDerToColumnModel(diagram, didConfig);
    const kvOut = convertDerToKeyValueModel(diagram, didConfig);

    const allRootSelected = didConfig.rootCollectionNames.length === 0;
    const deletionByTarget = new Map<string, TableDeletionCheck>(
      didDb.allDeletionChecks.map((c) => [c.targetId, c])
    );

    const modelLabels: { id: NoSqlModelKind; title: string; subtitle: string }[] = [
      { id: "document", title: "Document (DID / Mongo)", subtitle: "Collections + Embedded / DBRef" },
      { id: "graph", title: "Graph (Property Graph)", subtitle: "Nodes & Edges + Cypher" },
      { id: "column", title: "Column (Wide-Column)", subtitle: "Column Families + Cassandra CQL" },
      { id: "keyvalue", title: "Key-Value (Keyspace)", subtitle: "Key Prefixes + Redis" }
    ];

    let visualLeftHtml = "";
    let activeXml = "";
    let activeNativeScript = "";
    let nativeLabel = "";

    if (activeNoSqlModel === "document") {
      activeXml = formatDidDatabaseXml(didDb);
      activeNativeScript = formatDidMongoJson(didDb);
      nativeLabel = "Mongo BSON / JSON";
      visualLeftHtml = `
        <div class="der-sub-header">
          <h3>Document Model · DID Hierarchy (${didDb.collections.length} Active Collections)</h3>
        </div>
        <div class="did-collections-list">
          ${didDb.collections
            .map(
              (col) => `
            <div class="rm-table-card">
              <div class="rm-table-header">
                <div>
                  <span class="rm-table-name">db.${escapeHtml(col.collectionName)}</span>
                  <span class="rm-origin-pill">${col.originKind}${
                    col.isWeak ? " · weak" : ""
                  }</span>
                </div>
                <span class="verified-pill">DID Collection</span>
              </div>
              ${renderDidDocHtml(col.rootDoc)}
            </div>
          `
            )
            .join("")}
        </div>
      `;
    } else if (activeNoSqlModel === "graph") {
      activeXml = graphOut.xmlOutput;
      activeNativeScript = graphOut.cypherScript;
      nativeLabel = "Neo4j Cypher";
      visualLeftHtml = `
        <div class="der-sub-header">
          <h3>Property Graph Model (${graphOut.nodes.length} Node Labels · ${graphOut.edges.length} Edge Types)</h3>
        </div>
        <div class="did-collections-list">
          ${graphOut.nodes
            .map(
              (n) => `
            <div class="rm-table-card">
              <div class="rm-table-header">
                <div>
                  <span class="rm-table-name">(:${escapeHtml(n.label)})</span>
                  <span class="rm-origin-pill">Graph Node</span>
                </div>
                <span class="nf-badge nf-3nf">PK: ${escapeHtml(
                  n.keys.map((k) => k.name).join(", ")
                )}</span>
              </div>
              <div class="rm-cols-row">
                ${n.properties
                  .map(
                    (p) => `
                  <span class="rm-col-chip ${
                    p.origin === "key"
                      ? "is-pk"
                      : p.origin.startsWith("complete")
                        ? "is-multivalued"
                        : ""
                  }">
                    <span class="rm-col-name">${escapeHtml(p.name)}</span>
                    <span class="rm-col-type">${escapeHtml(p.type)}</span>
                    <span class="rm-col-badge">${escapeHtml(p.origin)}</span>
                  </span>
                `
                  )
                  .join("")}
              </div>
            </div>
          `
            )
            .join("")}
          ${graphOut.edges
            .map(
              (e) => `
            <div class="rm-table-card" style="border-style:dashed;">
              <div class="rm-table-header">
                <div>
                  <span class="rm-table-name">(:${escapeHtml(
                    e.fromLabel
                  )})-[:${escapeHtml(e.type)}]->(:${escapeHtml(e.toLabel)})</span>
                </div>
                <span class="nf-badge nf-2nf">${e.cardinality} · incrustation: ${
                  e.incrustation
                }</span>
              </div>
              <div class="rm-cols-row">
                ${
                  e.properties.length === 0
                    ? `<span class="panel-meta">No edge properties</span>`
                    : e.properties
                        .map(
                          (p) => `
                        <span class="rm-col-chip">
                          <span class="rm-col-name">${escapeHtml(p.name)}</span>
                          <span class="rm-col-type">${escapeHtml(p.type)}</span>
                          <span class="rm-col-badge">${escapeHtml(p.origin)}</span>
                        </span>
                      `
                        )
                        .join("")
                }
              </div>
            </div>
          `
            )
            .join("")}
        </div>
      `;
    } else if (activeNoSqlModel === "column") {
      activeXml = colOut.xmlOutput;
      activeNativeScript = colOut.cqlScript;
      nativeLabel = "Cassandra CQL";
      visualLeftHtml = `
        <div class="der-sub-header">
          <h3>Wide-Column Model (${colOut.families.length} Column Families)</h3>
        </div>
        <div class="did-collections-list">
          ${colOut.families
            .map(
              (cf) => `
            <div class="rm-table-card">
              <div class="rm-table-header">
                <div>
                  <span class="rm-table-name">${escapeHtml(cf.name)}</span>
                  <span class="rm-origin-pill">Column Family</span>
                </div>
                <span class="nf-badge nf-bcnf">Partition: (${escapeHtml(
                  cf.partitionKeys.join(", ")
                )})${
                  cf.clusteringKeys.length > 0
                    ? ` · Cluster: (${escapeHtml(cf.clusteringKeys.join(", "))})`
                    : ""
                }</span>
              </div>
              <div class="rm-cols-row">
                ${cf.columns
                  .map(
                    (c) => `
                  <span class="rm-col-chip ${
                    c.role === "partition-key"
                      ? "is-pk"
                      : c.role.startsWith("incrusted")
                        ? "is-multivalued"
                        : ""
                  }">
                    <span class="rm-col-name">${escapeHtml(c.name)}</span>
                    <span class="rm-col-type">${escapeHtml(c.cqlType)}</span>
                    <span class="rm-col-badge">${escapeHtml(c.role)}</span>
                  </span>
                `
                  )
                  .join("")}
              </div>
            </div>
          `
            )
            .join("")}
        </div>
      `;
    } else {
      activeXml = kvOut.xmlOutput;
      activeNativeScript = kvOut.redisScript;
      nativeLabel = "Redis Commands";
      visualLeftHtml = `
        <div class="der-sub-header">
          <h3>Key-Value Model (${kvOut.buckets.length} Active Keyspace Prefixes)</h3>
        </div>
        <div class="did-collections-list">
          ${kvOut.buckets
            .map(
              (b) => `
            <div class="rm-table-card">
              <div class="rm-table-header">
                <div>
                  <span class="rm-table-name">KEY: <code>${escapeHtml(
                    b.keyPattern
                  )}</code></span>
                </div>
                <span class="rm-origin-pill">${escapeHtml(b.entityName)}</span>
              </div>
              <div class="rm-cols-row">
                ${b.valueFields
                  .map(
                    (f) => `
                  <span class="rm-col-chip ${
                    f.origin === "key"
                      ? "is-pk"
                      : f.origin.includes("incrustation")
                        ? "is-multivalued"
                        : ""
                  }">
                    <span class="rm-col-name">${escapeHtml(f.name)}</span>
                    <span class="rm-col-type">${escapeHtml(f.type)}</span>
                    <span class="rm-col-badge">${escapeHtml(f.origin)}</span>
                  </span>
                `
                  )
                  .join("")}
              </div>
              ${
                b.secondaryIndexKeys.length > 0
                  ? `<div class="rm-fk-list">
                      ${b.secondaryIndexKeys
                        .map((s) => `<div class="rm-fk-item">↳ Index Set: <code>${escapeHtml(s)}</code></div>`)
                        .join("")}
                    </div>`
                  : ""
              }
            </div>
          `
            )
            .join("")}
        </div>
      `;
    }

    didSectionEl.innerHTML = `
      <div class="panel-header">
        <div>
          <h2>Step 3 · NoSQL Models (Document · Graph · Column · Key-Value), Incrustations &amp; Table Deletions</h2>
          <p class="panel-hint" style="margin:0.2rem 0 0;">
            Reuses the DER diagram above across all 4 NoSQL paradigms. Configure
            <strong>Partial Incrustation</strong> (selected attributes) or
            <strong>Complete Incrustation</strong> (all attributes) on any relation, and
            <strong>delete/absorb standalone tables</strong> (such as <strong>Weak Entities</strong>)
            when completely incrusted.
          </p>
        </div>
        <div class="inline-form">
          <button type="button" class="btn btn-secondary btn-sm" id="download-did-xml">
            Download .xml
          </button>
        </div>
      </div>

      <!-- 4 NoSQL Subsection Tabs: Document | Graph | Column | Key-Value -->
      <div class="nosql-model-tabs">
        ${modelLabels
          .map(
            (m) => `
          <button type="button" class="nosql-tab-btn ${
            activeNoSqlModel === m.id ? "is-active" : ""
          }" data-nosql-model="${m.id}">
            <span class="nosql-tab-title">${escapeHtml(m.title)}</span>
            <span class="nosql-tab-sub">${escapeHtml(m.subtitle)}</span>
          </button>
        `
          )
          .join("")}
      </div>

      ${renderDeletedTablesBanner(didDb.deletedTables)}

      <!-- Incrustation (Partial / Complete) & Table Deletion Controls -->
      <div class="der-norm-two-col" style="margin-bottom:1rem;">
        <div class="der-subpanel">
          <div class="der-sub-header">
            <h3>1. Incrustations (Partial / Complete) &amp; Table Deletion</h3>
          </div>
          ${
            diagram.relations.length === 0
              ? `<p class="panel-hint">Add a relation in the DER canvas above to configure incrustations.</p>`
              : `<div class="did-rel-mode-list">
                  ${diagram.relations
                    .map((rel) => {
                      const src = diagram.elements.find((e) => e.id === rel.sourceId);
                      const dst = diagram.elements.find((e) => e.id === rel.targetId);
                      const rKind = relationKindOf(rel);
                      const rule = getRelationRule(didConfig, rel, dst);
                      const eff = effectiveIncrustation(didConfig, rel, dst);
                      const delCheck = dst ? deletionByTarget.get(dst.id) : undefined;
                      const nonKeyTargetAttrs = (dst?.attributes ?? []).filter(
                        (a) => !a.isKey
                      );

                      return `
                        <div class="did-rel-card">
                          <div class="did-rel-mode-row">
                            <div>
                              <strong>${escapeHtml(rel.name)}</strong>
                              <code>[${rKind}]</code>
                              <span class="panel-meta">${escapeHtml(
                                src?.name ?? "?"
                              )} → ${escapeHtml(dst?.name ?? "?")}</span>
                              ${
                                dst && dst.kind === "entity" && dst.isWeak
                                  ? `<span class="nf-badge nf-1nf">Target is Weak Entity</span>`
                                  : ""
                              }
                            </div>
                            <div class="segmented">
                              ${(
                                [
                                  { id: "auto", label: "Auto" },
                                  { id: "none", label: "None (Ref)" },
                                  { id: "partial", label: "Partial" },
                                  { id: "complete", label: "Complete" }
                                ] as { id: IncrustationMode; label: string }[]
                              )
                                .map(
                                  (m) => `
                                <button type="button" class="segmented-btn ${
                                  rule.mode === m.id ? "is-active" : ""
                                }" data-did-rel="${escapeHtml(rel.name)}" data-did-mode="${m.id}">
                                  ${m.label}
                                </button>
                              `
                                )
                                .join("")}
                            </div>
                          </div>

                          ${
                            eff.resolvedMode === "partial"
                              ? `
                            <div class="did-partial-picker">
                              <span class="der-field-label" style="margin-bottom:0.2rem;">
                                Partial Incrustation Attributes from <code>${escapeHtml(
                                  dst?.name ?? ""
                                )}</code> (PK is always included as reference):
                              </span>
                              <div class="der-chip-row">
                                ${
                                  nonKeyTargetAttrs.length === 0
                                    ? `<span class="panel-meta">Target only has PK attributes</span>`
                                    : nonKeyTargetAttrs
                                        .map((attr) => {
                                          const checked = eff.incrustedAttrs.some(
                                            (a) => a.name === attr.name
                                          );
                                          return `
                                            <label class="der-pk-check" style="background:#ffffff;border:1px solid var(--border);padding:0.15rem 0.45rem;border-radius:6px;">
                                              <input type="checkbox" data-partial-rel="${escapeHtml(
                                                rel.name
                                              )}" data-partial-attr="${escapeHtml(
                                                attr.name
                                              )}" ${checked ? "checked" : ""} />
                                              ${escapeHtml(attr.name)} (${attr.attrType})
                                            </label>
                                          `;
                                        })
                                        .join("")
                                }
                              </div>
                            </div>
                          `
                              : ""
                          }

                          ${
                            dst && dst.id !== src?.id
                              ? `
                            <div class="did-delete-row">
                              <label class="der-pk-check">
                                <input type="checkbox" data-delete-rel="${escapeHtml(
                                  rel.name
                                )}" ${rule.deleteTargetTable ? "checked" : ""} />
                                Delete standalone table <code>${escapeHtml(
                                  dst.name
                                )}</code> (absorb into <code>${escapeHtml(
                                  src?.name ?? "?"
                                )}</code>)
                              </label>
                              ${
                                delCheck
                                  ? `<span class="panel-meta" style="color:${
                                      delCheck.actuallyDeleted
                                        ? "var(--green)"
                                        : rule.deleteTargetTable && !delCheck.canDelete
                                          ? "var(--rose)"
                                          : "var(--ink-secondary)"
                                    };">
                                      ${escapeHtml(delCheck.reason)}
                                    </span>`
                                  : ""
                              }
                            </div>
                          `
                              : ""
                          }
                        </div>
                      `;
                    })
                    .join("")}
                </div>`
          }
        </div>

        <div class="der-subpanel">
          <div class="der-sub-header">
            <h3>2. Database &amp; Root Filter Settings</h3>
            <button type="button" class="btn btn-chip btn-sm" id="did-reset-roots">
              ${allRootSelected ? "All Non-Deleted Roots Active ✓" : "Select All Roots"}
            </button>
          </div>

          <div class="der-two-col" style="margin-bottom:0.65rem;">
            <div>
              <label class="der-field-label">Database / Keyspace Name</label>
              <input type="text" class="input input-sm" id="did-db-name" value="${escapeHtml(
                didConfig.dbName
              )}" style="width:100%;" />
            </div>
            <div>
              <label class="der-field-label">Max Nesting Depth</label>
              <select class="input input-sm" id="did-max-depth" style="width:100%;">
                ${[1, 2, 3]
                  .map(
                    (d) =>
                      `<option value="${d}" ${
                        didConfig.maxDepth === d ? "selected" : ""
                      }>${d} level${d > 1 ? "s" : ""}</option>`
                  )
                  .join("")}
              </select>
            </div>
          </div>

          <div class="der-field-label">Entities / Aggregations Status (Weak Entities &amp; Table Deletions)</div>
          <div class="did-entity-status-list">
            ${didDb.allDeletionChecks
              .map(
                (chk) => `
              <div class="did-entity-status-row">
                <div>
                  <strong>${escapeHtml(chk.targetName)}</strong>
                  ${chk.isWeak ? `<span class="nf-badge nf-1nf">Weak Entity</span>` : ""}
                </div>
                <div>
                  ${
                    chk.actuallyDeleted
                      ? `<span class="nf-badge nf-bcnf">Deleted &amp; Absorbed ✓</span>`
                      : chk.canDelete
                        ? `<span class="nf-badge nf-3nf">Eligible for Deletion</span>`
                        : `<span class="rm-origin-pill">Active Standalone Table</span>`
                  }
                </div>
              </div>
            `
              )
              .join("")}
          </div>
        </div>
      </div>

      <!-- Visual NoSQL Model Cards + Generated XML / Native Script -->
      <div class="der-norm-two-col">
        <div>
          ${visualLeftHtml}
        </div>

        <div>
          <div class="der-sub-header">
            <h3>Generated Output (${modelLabels.find((m) => m.id === activeNoSqlModel)?.title})</h3>
            <div class="segmented">
              <button type="button" class="segmented-btn ${
                didOutputFormat === "xml" ? "is-active" : ""
              }" data-did-fmt="xml">
                XML Output
              </button>
              <button type="button" class="segmented-btn ${
                didOutputFormat === "native" ? "is-active" : ""
              }" data-did-fmt="native">
                ${escapeHtml(nativeLabel)}
              </button>
            </div>
          </div>
          <pre class="der-sql-pre" style="max-height:540px;overflow:auto;"><code>${escapeHtml(
            didOutputFormat === "xml" ? activeXml : activeNativeScript
          )}</code></pre>
        </div>
      </div>
    `;

    didSectionEl.querySelectorAll<HTMLButtonElement>("[data-nosql-model]").forEach((btn) => {
      btn.addEventListener("click", () => {
        activeNoSqlModel = btn.dataset.nosqlModel as NoSqlModelKind;
        renderDidSection();
      });
    });

    didSectionEl
      .querySelector<HTMLInputElement>("#did-db-name")
      ?.addEventListener("input", (ev) => {
        const val = (ev.target as HTMLInputElement).value.trim();
        if (val) {
          didConfig.dbName = val;
          renderDidSection();
        }
      });

    didSectionEl
      .querySelector<HTMLSelectElement>("#did-max-depth")
      ?.addEventListener("change", (ev) => {
        didConfig.maxDepth = Number((ev.target as HTMLSelectElement).value) || 2;
        renderDidSection();
      });

    didSectionEl.querySelector("#did-reset-roots")?.addEventListener("click", () => {
      didConfig.rootCollectionNames = [];
      renderDidSection();
    });

    didSectionEl.querySelectorAll<HTMLButtonElement>("[data-did-rel]").forEach((btn) => {
      btn.addEventListener("click", () => {
        const relName = btn.dataset.didRel!;
        const mode = btn.dataset.didMode as IncrustationMode;
        const rel = diagram.relations.find((r) => r.name === relName);
        const dst = diagram.elements.find((e) => e.id === rel?.targetId);
        const cur = getRelationRule(didConfig, rel!, dst);
        didConfig.relationRules[relName] = {
          ...cur,
          mode,
          // If switching to partial/none, cannot delete standalone table
          deleteTargetTable:
            mode === "partial" || mode === "none" ? false : cur.deleteTargetTable
        };
        renderDidSection();
      });
    });

    didSectionEl
      .querySelectorAll<HTMLInputElement>("[data-partial-rel]")
      .forEach((cb) => {
        cb.addEventListener("change", () => {
          const relName = cb.dataset.partialRel!;
          const attrName = cb.dataset.partialAttr!;
          const rel = diagram.relations.find((r) => r.name === relName);
          const dst = diagram.elements.find((e) => e.id === rel?.targetId);
          const cur = getRelationRule(didConfig, rel!, dst);
          const set = new Set(cur.partialAttrs);
          if (cb.checked) {
            set.add(attrName);
          } else if (set.size > 1) {
            set.delete(attrName);
          }
          didConfig.relationRules[relName] = {
            ...cur,
            partialAttrs: [...set]
          };
          renderDidSection();
        });
      });

    didSectionEl
      .querySelectorAll<HTMLInputElement>("[data-delete-rel]")
      .forEach((cb) => {
        cb.addEventListener("change", () => {
          const relName = cb.dataset.deleteRel!;
          const rel = diagram.relations.find((r) => r.name === relName);
          const dst = diagram.elements.find((e) => e.id === rel?.targetId);
          const cur = getRelationRule(didConfig, rel!, dst);
          didConfig.relationRules[relName] = {
            ...cur,
            // Auto-upgrade to complete incrustation when user requests table deletion
            mode: cb.checked && cur.mode !== "complete" ? "complete" : cur.mode,
            deleteTargetTable: cb.checked
          };
          renderDidSection();
        });
      });

    didSectionEl.querySelectorAll<HTMLButtonElement>("[data-did-fmt]").forEach((btn) => {
      btn.addEventListener("click", () => {
        didOutputFormat = btn.dataset.didFmt as "xml" | "native";
        renderDidSection();
      });
    });

    didSectionEl.querySelector("#download-did-xml")?.addEventListener("click", () => {
      const blob = new Blob([activeXml], { type: "application/xml" });
      const url = URL.createObjectURL(blob);
      const a = document.createElement("a");
      a.href = url;
      a.download = `${didConfig.dbName.toLowerCase()}.${activeNoSqlModel}.xml`;
      a.click();
      URL.revokeObjectURL(url);
    });
  }

  function renderAll(): void {
    renderStorageBar();
    renderCanvas();
    renderInspector();
    renderRelationalAndNormalization();
    renderDidSection();
  }

  renderAll();
  if (initialFocus.startsWith("nosql-")) {
    setTimeout(() => {
      didSectionEl.scrollIntoView({ behavior: "smooth", block: "start" });
    }, 40);
  }
  return article;
}
