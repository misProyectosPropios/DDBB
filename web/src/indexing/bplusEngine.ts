// TypeScript port & interactive extension of `dafny/indexing/BPlusTree.dfy`:
//   - Balanced B+ Tree with `Insert` (Leaf Copy-Up Split & Internal Push-Up Split),
//     `Search`, `RangeScan` (linked leaf-chain iteration), and `Delete` (Borrow /
//     Redistribute from sibling & Merge / Root Collapse).
//   - Index vs. No-Index (Full Table Scan) & Covering Full Index Scan Cost Model
//     demonstrating why a query planner sometimes ignores an index (low selectivity
//     random heap lookups) or scans the index leaves linearly even when it cannot seek.

export interface BPlusEntry {
  key: number;
  val: number;
}

export type BPlusNode =
  | { kind: "Leaf"; id: string; entries: BPlusEntry[] }
  | { kind: "Internal"; id: string; keys: number[]; children: BPlusNode[] };

export interface BPlusTree {
  maxKeys: number; // max keys per node (order = maxKeys + 1), >= 2
  height: number; // 0 = single leaf root
  root: BPlusNode;
}

export interface BPlusTraceStep {
  step: number;
  nodeId: string;
  action: "visit" | "found" | "not-found" | "leaf-next" | "split-leaf" | "split-internal" | "split-root" | "delete" | "borrow" | "merge" | "shrink-root";
  detail: string;
}

export interface BPlusOperationResult {
  tree: BPlusTree;
  visitedNodeIds: string[];
  leafChainNodeIds: string[];
  highlightedKey: number | null;
  matchedEntries: BPlusEntry[];
  found: boolean;
  summary: string;
  steps: BPlusTraceStep[];
}

let nextNodeCounter = 1;
function allocNodeId(prefix: "L" | "I"): string {
  return `${prefix}${nextNodeCounter++}`;
}

export function resetNodeIds(): void {
  nextNodeCounter = 1;
}

function cloneNode(node: BPlusNode): BPlusNode {
  if (node.kind === "Leaf") {
    return {
      kind: "Leaf",
      id: node.id,
      entries: node.entries.map((e) => ({ ...e }))
    };
  }
  return {
    kind: "Internal",
    id: node.id,
    keys: [...node.keys],
    children: node.children.map(cloneNode)
  };
}

export function cloneTree(tree: BPlusTree): BPlusTree {
  return {
    maxKeys: tree.maxKeys,
    height: tree.height,
    root: cloneNode(tree.root)
  };
}

export function createEmptyBPlusTree(maxKeys = 3): BPlusTree {
  return {
    maxKeys: Math.max(2, maxKeys),
    height: 0,
    root: { kind: "Leaf", id: allocNodeId("L"), entries: [] }
  };
}

function findChildIndex(keys: number[], k: number): number {
  let idx = 0;
  while (idx < keys.length && k >= keys[idx]) {
    idx++;
  }
  return idx;
}

export function collectLeaves(node: BPlusNode): Extract<BPlusNode, { kind: "Leaf" }>[] {
  if (node.kind === "Leaf") return [node];
  const out: Extract<BPlusNode, { kind: "Leaf" }>[] = [];
  for (const child of node.children) {
    out.push(...collectLeaves(child));
  }
  return out;
}

export function allEntries(tree: BPlusTree): BPlusEntry[] {
  return collectLeaves(tree.root).flatMap((l) => l.entries);
}

// ---------------------------------------------------------------------------
// 1. Search with Path Trace
// ---------------------------------------------------------------------------

export function searchBPlusTree(tree: BPlusTree, key: number): BPlusOperationResult {
  const visitedNodeIds: string[] = [];
  const steps: BPlusTraceStep[] = [];
  let cur = tree.root;

  while (cur.kind === "Internal") {
    visitedNodeIds.push(cur.id);
    const idx = findChildIndex(cur.keys, key);
    const loDesc = idx === 0 ? "-∞" : String(cur.keys[idx - 1]);
    const hiDesc = idx === cur.keys.length ? "+∞" : String(cur.keys[idx]);
    steps.push({
      step: steps.length + 1,
      nodeId: cur.id,
      action: "visit",
      detail: `Internal ${cur.id} [${cur.keys.join(", ")}]: ${key} ∈ [${loDesc}, ${hiDesc}) → follow child #${idx} (${cur.children[idx].id})`
    });
    cur = cur.children[idx];
  }

  visitedNodeIds.push(cur.id);
  const hit = cur.entries.find((e) => e.key === key);
  if (hit) {
    steps.push({
      step: steps.length + 1,
      nodeId: cur.id,
      action: "found",
      detail: `Leaf ${cur.id} [${cur.entries.map((e) => e.key).join(", ")}]: FOUND key ${key} → value ${hit.val} (in ${visitedNodeIds.length} node reads)`
    });
    return {
      tree,
      visitedNodeIds,
      leafChainNodeIds: [cur.id],
      highlightedKey: key,
      matchedEntries: [{ ...hit }],
      found: true,
      summary: `Found (${key} → ${hit.val}) in leaf ${cur.id} after ${visitedNodeIds.length} node visit(s).`,
      steps
    };
  }

  steps.push({
    step: steps.length + 1,
    nodeId: cur.id,
    action: "not-found",
    detail: `Leaf ${cur.id} [${cur.entries.map((e) => e.key).join(", ")}]: key ${key} NOT FOUND (${visitedNodeIds.length} node reads)`
  });
  return {
    tree,
    visitedNodeIds,
    leafChainNodeIds: [cur.id],
    highlightedKey: key,
    matchedEntries: [],
    found: false,
    summary: `Key ${key} not found (checked leaf ${cur.id} after ${visitedNodeIds.length} node visit(s)).`,
    steps
  };
}

// ---------------------------------------------------------------------------
// 2. Iterate / Range Scan (`[lo, hi]`) via Root Descent + Leaf Linked List
// ---------------------------------------------------------------------------

export function rangeScanBPlusTree(
  tree: BPlusTree,
  lo: number,
  hi: number
): BPlusOperationResult {
  const visitedNodeIds: string[] = [];
  const leafChainNodeIds: string[] = [];
  const matchedEntries: BPlusEntry[] = [];
  const steps: BPlusTraceStep[] = [];

  // Phase 1: Descend from root to the starting leaf for `lo`
  let cur = tree.root;
  while (cur.kind === "Internal") {
    visitedNodeIds.push(cur.id);
    const idx = findChildIndex(cur.keys, lo);
    steps.push({
      step: steps.length + 1,
      nodeId: cur.id,
      action: "visit",
      detail: `Seek lower bound ${lo} at ${cur.id} [${cur.keys.join(", ")}] → child #${idx} (${cur.children[idx].id})`
    });
    cur = cur.children[idx];
  }

  // Phase 2: Follow sibling leaf pointers from the starting leaf onward
  const leaves = collectLeaves(tree.root);
  const startLeafIdx = Math.max(
    0,
    leaves.findIndex((l) => l.id === cur.id)
  );

  for (let i = startLeafIdx; i < leaves.length; i++) {
    const leaf = leaves[i];
    if (i > startLeafIdx) {
      steps.push({
        step: steps.length + 1,
        nodeId: leaf.id,
        action: "leaf-next",
        detail: `Follow leaf next-pointer → ${leaf.id} [${leaf.entries.map((e) => e.key).join(", ")}]`
      });
    } else {
      visitedNodeIds.push(leaf.id);
      steps.push({
        step: steps.length + 1,
        nodeId: leaf.id,
        action: "visit",
        detail: `Arrived at starting leaf ${leaf.id} [${leaf.entries.map((e) => e.key).join(", ")}]`
      });
    }

    leafChainNodeIds.push(leaf.id);
    let passedUpper = false;
    for (const entry of leaf.entries) {
      if (entry.key < lo) continue;
      if (entry.key > hi) {
        passedUpper = true;
        steps.push({
          step: steps.length + 1,
          nodeId: leaf.id,
          action: "found",
          detail: `Stopped iteration at key ${entry.key} > upper bound ${hi}`
        });
        break;
      }
      matchedEntries.push({ ...entry });
    }
    if (passedUpper) break;
  }

  return {
    tree,
    visitedNodeIds,
    leafChainNodeIds,
    highlightedKey: null,
    matchedEntries,
    found: matchedEntries.length > 0,
    summary: `Iterated [${lo}, ${hi}]: descended ${tree.height} internal level(s), scanned ${leafChainNodeIds.length} leaf node(s) via next-pointers, yielded ${matchedEntries.length} entry/entries.`,
    steps
  };
}

// ---------------------------------------------------------------------------
// 3. Insert with Leaf Copy-Up Split & Internal Push-Up Split
// ---------------------------------------------------------------------------

type SplitOutcome =
  | { split: false; node: BPlusNode }
  | { split: true; left: BPlusNode; sepKey: number; right: BPlusNode };

export function insertBPlusTree(
  inputTree: BPlusTree,
  key: number,
  val: number
): BPlusOperationResult {
  const tree = cloneTree(inputTree);
  const visitedNodeIds: string[] = [];
  const steps: BPlusTraceStep[] = [];

  function insertRec(node: BPlusNode): SplitOutcome {
    visitedNodeIds.push(node.id);
    if (node.kind === "Leaf") {
      const existingIdx = node.entries.findIndex((e) => e.key === key);
      if (existingIdx >= 0) {
        node.entries[existingIdx].val = val;
        steps.push({
          step: steps.length + 1,
          nodeId: node.id,
          action: "found",
          detail: `Updated existing key ${key} := ${val} in leaf ${node.id}`
        });
        return { split: false, node };
      }

      const nextEntries = [...node.entries, { key, val }].sort((a, b) => a.key - b.key);
      if (nextEntries.length <= tree.maxKeys) {
        node.entries = nextEntries;
        steps.push({
          step: steps.length + 1,
          nodeId: node.id,
          action: "found",
          detail: `Inserted (${key} → ${val}) into leaf ${node.id} (now ${nextEntries.length}/${tree.maxKeys} keys)`
        });
        return { split: false, node };
      }

      // Leaf Copy-Up Split!
      const mid = Math.floor(nextEntries.length / 2);
      const leftEntries = nextEntries.slice(0, mid);
      const rightEntries = nextEntries.slice(mid);
      const sepKey = rightEntries[0].key;
      const rightLeaf: BPlusNode = {
        kind: "Leaf",
        id: allocNodeId("L"),
        entries: rightEntries
      };
      node.entries = leftEntries;
      steps.push({
        step: steps.length + 1,
        nodeId: node.id,
        action: "split-leaf",
        detail: `Leaf ${node.id} overflowed (${nextEntries.length} > ${tree.maxKeys}) → Copy-Up Split! Left ${node.id} [${leftEntries.map((e) => e.key).join(", ")}], Right ${rightLeaf.id} [${rightEntries.map((e) => e.key).join(", ")}], copied separator ${sepKey} up.`
      });
      return { split: true, left: node, sepKey, right: rightLeaf };
    }

    // Internal node
    const idx = findChildIndex(node.keys, key);
    steps.push({
      step: steps.length + 1,
      nodeId: node.id,
      action: "visit",
      detail: `Internal ${node.id} [${node.keys.join(", ")}] → descending to child #${idx} (${node.children[idx].id})`
    });
    const childRes = insertRec(node.children[idx]);
    if (!childRes.split) {
      node.children[idx] = childRes.node;
      return { split: false, node };
    }

    const newKeys = [
      ...node.keys.slice(0, idx),
      childRes.sepKey,
      ...node.keys.slice(idx)
    ];
    const newChildren = [
      ...node.children.slice(0, idx),
      childRes.left,
      childRes.right,
      ...node.children.slice(idx + 1)
    ];

    if (newKeys.length <= tree.maxKeys) {
      node.keys = newKeys;
      node.children = newChildren;
      return { split: false, node };
    }

    // Internal Push-Up Split!
    const mid = Math.floor(newKeys.length / 2);
    const promotedKey = newKeys[mid];
    const leftKeys = newKeys.slice(0, mid);
    const rightKeys = newKeys.slice(mid + 1);
    const leftChildren = newChildren.slice(0, mid + 1);
    const rightChildren = newChildren.slice(mid + 1);
    node.keys = leftKeys;
    node.children = leftChildren;
    const rightInternal: BPlusNode = {
      kind: "Internal",
      id: allocNodeId("I"),
      keys: rightKeys,
      children: rightChildren
    };
    steps.push({
      step: steps.length + 1,
      nodeId: node.id,
      action: "split-internal",
      detail: `Internal ${node.id} overflowed (${newKeys.length} > ${tree.maxKeys}) → Push-Up Split! Pushed median separator ${promotedKey} up, created ${rightInternal.id} [${rightKeys.join(", ")}].`
    });
    return { split: true, left: node, sepKey: promotedKey, right: rightInternal };
  }

  const rootRes = insertRec(tree.root);
  if (rootRes.split) {
    const newRoot: BPlusNode = {
      kind: "Internal",
      id: allocNodeId("I"),
      keys: [rootRes.sepKey],
      children: [rootRes.left, rootRes.right]
    };
    tree.root = newRoot;
    tree.height += 1;
    visitedNodeIds.unshift(newRoot.id);
    steps.push({
      step: steps.length + 1,
      nodeId: newRoot.id,
      action: "split-root",
      detail: `Root split! Created new root ${newRoot.id} [${rootRes.sepKey}]; tree height grew to ${tree.height}.`
    });
  } else {
    tree.root = rootRes.node;
  }

  return {
    tree,
    visitedNodeIds,
    leafChainNodeIds: [],
    highlightedKey: key,
    matchedEntries: [{ key, val }],
    found: true,
    summary: `Inserted (${key} → ${val}). Tree height = ${tree.height}, total entries = ${allEntries(tree).length}.`,
    steps
  };
}

// ---------------------------------------------------------------------------
// 4. Delete with Underflow Handling (Borrow from Sibling / Merge / Root Shrink)
// ---------------------------------------------------------------------------

export function deleteBPlusTree(inputTree: BPlusTree, key: number): BPlusOperationResult {
  const tree = cloneTree(inputTree);
  const visitedNodeIds: string[] = [];
  const steps: BPlusTraceStep[] = [];
  const minLeafKeys = Math.ceil(tree.maxKeys / 2);
  const minInternalKeys = Math.floor(tree.maxKeys / 2);
  let removed = false;

  function firstLeafKey(node: BPlusNode): number {
    let cur = node;
    while (cur.kind === "Internal") {
      cur = cur.children[0];
    }
    return cur.entries[0]?.key ?? 0;
  }

  function deleteRec(node: BPlusNode): void {
    visitedNodeIds.push(node.id);
    if (node.kind === "Leaf") {
      const idx = node.entries.findIndex((e) => e.key === key);
      if (idx < 0) {
        steps.push({
          step: steps.length + 1,
          nodeId: node.id,
          action: "not-found",
          detail: `Leaf ${node.id}: key ${key} not found — nothing removed.`
        });
        return;
      }
      node.entries.splice(idx, 1);
      removed = true;
      steps.push({
        step: steps.length + 1,
        nodeId: node.id,
        action: "delete",
        detail: `Removed key ${key} from leaf ${node.id} (remaining: [${node.entries.map((e) => e.key).join(", ")}])`
      });
      return;
    }

    // Internal node
    const idx = findChildIndex(node.keys, key);
    steps.push({
      step: steps.length + 1,
      nodeId: node.id,
      action: "visit",
      detail: `Internal ${node.id} [${node.keys.join(", ")}] → descending to child #${idx} (${node.children[idx].id})`
    });
    const child = node.children[idx];
    deleteRec(child);
    if (!removed) return;

    // Update parent separator if child's first key changed (and child is non-empty)
    if (idx > 0 && child.kind === "Leaf" && child.entries.length > 0) {
      node.keys[idx - 1] = child.entries[0].key;
    }

    // Check for child underflow
    if (child.kind === "Leaf" && child.entries.length < minLeafKeys) {
      const leftSib = idx > 0 ? node.children[idx - 1] : null;
      const rightSib = idx + 1 < node.children.length ? node.children[idx + 1] : null;

      // Try borrow from left leaf sibling
      if (leftSib && leftSib.kind === "Leaf" && leftSib.entries.length > minLeafKeys) {
        const borrowed = leftSib.entries.pop()!;
        child.entries.unshift(borrowed);
        node.keys[idx - 1] = child.entries[0].key;
        steps.push({
          step: steps.length + 1,
          nodeId: child.id,
          action: "borrow",
          detail: `Leaf ${child.id} underflowed (< ${minLeafKeys}) → Borrowed key ${borrowed.key} from left sibling ${leftSib.id}; updated parent separator to ${node.keys[idx - 1]}.`
        });
        return;
      }

      // Try borrow from right leaf sibling
      if (rightSib && rightSib.kind === "Leaf" && rightSib.entries.length > minLeafKeys) {
        const borrowed = rightSib.entries.shift()!;
        child.entries.push(borrowed);
        node.keys[idx] = rightSib.entries[0].key;
        if (idx > 0) node.keys[idx - 1] = child.entries[0].key;
        steps.push({
          step: steps.length + 1,
          nodeId: child.id,
          action: "borrow",
          detail: `Leaf ${child.id} underflowed (< ${minLeafKeys}) → Borrowed key ${borrowed.key} from right sibling ${rightSib.id}; updated parent separator to ${node.keys[idx]}.`
        });
        return;
      }

      // Otherwise merge with left or right leaf sibling
      if (leftSib && leftSib.kind === "Leaf") {
        leftSib.entries.push(...child.entries);
        node.children.splice(idx, 1);
        const droppedSep = node.keys.splice(idx - 1, 1)[0];
        steps.push({
          step: steps.length + 1,
          nodeId: leftSib.id,
          action: "merge",
          detail: `Leaf ${child.id} underflowed → Merged into left sibling ${leftSib.id} ([${leftSib.entries.map((e) => e.key).join(", ")}]) and dropped parent separator ${droppedSep}.`
        });
      } else if (rightSib && rightSib.kind === "Leaf") {
        child.entries.push(...rightSib.entries);
        node.children.splice(idx + 1, 1);
        const droppedSep = node.keys.splice(idx, 1)[0];
        steps.push({
          step: steps.length + 1,
          nodeId: child.id,
          action: "merge",
          detail: `Leaf ${child.id} underflowed → Merged right sibling ${rightSib.id} into ${child.id} ([${child.entries.map((e) => e.key).join(", ")}]) and dropped parent separator ${droppedSep}.`
        });
      }
      return;
    }

    // Internal child underflow
    if (child.kind === "Internal" && child.keys.length < minInternalKeys) {
      const leftSib = idx > 0 ? node.children[idx - 1] : null;
      const rightSib = idx + 1 < node.children.length ? node.children[idx + 1] : null;

      if (leftSib && leftSib.kind === "Internal" && leftSib.keys.length > minInternalKeys) {
        const pullDownKey = node.keys[idx - 1];
        const moveUpKey = leftSib.keys.pop()!;
        const movedChild = leftSib.children.pop()!;
        child.keys.unshift(pullDownKey);
        child.children.unshift(movedChild);
        node.keys[idx - 1] = moveUpKey;
        steps.push({
          step: steps.length + 1,
          nodeId: child.id,
          action: "borrow",
          detail: `Internal ${child.id} underflowed → Rotated separator ${pullDownKey} down from ${node.id} and promoted ${moveUpKey} from left sibling ${leftSib.id}.`
        });
        return;
      }

      if (rightSib && rightSib.kind === "Internal" && rightSib.keys.length > minInternalKeys) {
        const pullDownKey = node.keys[idx];
        const moveUpKey = rightSib.keys.shift()!;
        const movedChild = rightSib.children.shift()!;
        child.keys.push(pullDownKey);
        child.children.push(movedChild);
        node.keys[idx] = moveUpKey;
        steps.push({
          step: steps.length + 1,
          nodeId: child.id,
          action: "borrow",
          detail: `Internal ${child.id} underflowed → Rotated separator ${pullDownKey} down from ${node.id} and promoted ${moveUpKey} from right sibling ${rightSib.id}.`
        });
        return;
      }

      if (leftSib && leftSib.kind === "Internal") {
        const pullDownKey = node.keys.splice(idx - 1, 1)[0];
        leftSib.keys.push(pullDownKey, ...child.keys);
        leftSib.children.push(...child.children);
        node.children.splice(idx, 1);
        steps.push({
          step: steps.length + 1,
          nodeId: leftSib.id,
          action: "merge",
          detail: `Internal ${child.id} underflowed → Merged into left sibling ${leftSib.id} pulling down separator ${pullDownKey}.`
        });
      } else if (rightSib && rightSib.kind === "Internal") {
        const pullDownKey = node.keys.splice(idx, 1)[0];
        child.keys.push(pullDownKey, ...rightSib.keys);
        child.children.push(...rightSib.children);
        node.children.splice(idx + 1, 1);
        steps.push({
          step: steps.length + 1,
          nodeId: child.id,
          action: "merge",
          detail: `Internal ${child.id} underflowed → Merged right sibling ${rightSib.id} into ${child.id} pulling down separator ${pullDownKey}.`
        });
      }
    }

    // Refresh separators above non-empty children if needed
    for (let s = 0; s < node.keys.length; s++) {
      const rightChild = node.children[s + 1];
      if (rightChild.kind === "Leaf" && rightChild.entries.length > 0) {
        node.keys[s] = firstLeafKey(rightChild);
      }
    }
  }

  deleteRec(tree.root);

  // If root is an internal node with 0 keys (1 remaining child), collapse root!
  if (tree.root.kind === "Internal" && tree.root.keys.length === 0 && tree.root.children.length === 1) {
    const oldRootId = tree.root.id;
    tree.root = tree.root.children[0];
    tree.height = Math.max(0, tree.height - 1);
    steps.push({
      step: steps.length + 1,
      nodeId: tree.root.id,
      action: "shrink-root",
      detail: `Root ${oldRootId} became empty → Collapsed root! ${tree.root.id} is the new root; tree height shrank to ${tree.height}.`
    });
  }

  return {
    tree,
    visitedNodeIds,
    leafChainNodeIds: [],
    highlightedKey: key,
    matchedEntries: [],
    found: removed,
    summary: removed
      ? `Removed key ${key}. Tree height = ${tree.height}, remaining entries = ${allEntries(tree).length}.`
      : `Key ${key} was not in the tree.`,
    steps
  };
}

// ---------------------------------------------------------------------------
// 5. Presets
// ---------------------------------------------------------------------------

export interface BPlusPreset {
  id: string;
  title: string;
  maxKeys: number;
  entries: BPlusEntry[];
  defaultSearch: number;
  defaultRange: [number, number];
  defaultDelete: number;
}

export const BPLUS_PRESETS: BPlusPreset[] = [
  {
    id: "order3-balanced",
    title: "7-Key Tree (maxKeys = 2, Height 2)",
    maxKeys: 2,
    entries: [
      { key: 10, val: 100 },
      { key: 20, val: 200 },
      { key: 30, val: 300 },
      { key: 40, val: 400 },
      { key: 50, val: 500 },
      { key: 25, val: 250 },
      { key: 15, val: 150 }
    ],
    defaultSearch: 25,
    defaultRange: [15, 40],
    defaultDelete: 20
  },
  {
    id: "order4-classic",
    title: "14-Key Tree (maxKeys = 3, Order 4)",
    maxKeys: 3,
    entries: [5, 12, 18, 25, 31, 38, 44, 52, 60, 67, 73, 81, 89, 95].map((k) => ({
      key: k,
      val: k * 10
    })),
    defaultSearch: 44,
    defaultRange: [25, 67],
    defaultDelete: 38
  },
  {
    id: "order5-wide",
    title: "18-Key Tree (maxKeys = 4, Order 5)",
    maxKeys: 4,
    entries: [
      3, 7, 11, 14, 19, 23, 28, 33, 39, 42, 47, 51, 56, 62, 68, 74, 82, 91
    ].map((k) => ({ key: k, val: k * 5 })),
    defaultSearch: 47,
    defaultRange: [19, 56],
    defaultDelete: 28
  }
];

export function buildTreeFromPreset(preset: BPlusPreset): BPlusTree {
  resetNodeIds();
  let t = createEmptyBPlusTree(preset.maxKeys);
  for (const e of preset.entries) {
    t = insertBPlusTree(t, e.key, e.val).tree;
  }
  return t;
}

// ---------------------------------------------------------------------------
// 6. Index vs. No-Index (Full Table Scan) & Planner Decision Cost Model
// ---------------------------------------------------------------------------

export type QueryAccessScenarioId =
  | "point-lookup"
  | "narrow-range"
  | "wide-range-unclustered"
  | "non-sargable-covering"
  | "non-sargable-noncovering";

export interface IndexCostParams {
  totalRows: number; // N
  rowsPerHeapPage: number; // R_heap (wide table rows)
  entriesPerIndexPage: number; // R_idx (skinny index entries: key + RID)
  treeHeight: number; // h
  selectivityPct: number; // 0.01 .. 100
  randomIoMultiplier: number; // random page fetch cost vs sequential (e.g. 4x)
  indexCanSeek: boolean; // false for non-sargable / non-leading column predicates
  indexIsCovering: boolean; // true if index contains all SELECT columns (Index-Only Scan)
}

export interface PlanCostOption {
  id: "full-table-scan" | "index-seek-heap" | "full-index-scan-only" | "full-index-plus-heap";
  label: string;
  available: boolean;
  pagesRead: number;
  effectiveIoCost: number;
  explanation: string;
}

export interface IndexCostComparison {
  heapPages: number;
  indexLeafPages: number;
  matchingRows: number;
  plans: PlanCostOption[];
  winner: PlanCostOption;
  takeaway: string;
}

export interface CostScenarioPreset {
  id: QueryAccessScenarioId;
  title: string;
  sqlExample: string;
  params: IndexCostParams;
}

export const INDEX_COST_PRESETS: CostScenarioPreset[] = [
  {
    id: "point-lookup",
    title: "1. Point Lookup (0.01% selectivity)",
    sqlExample: "SELECT * FROM Orders WHERE order_id = 42017;",
    params: {
      totalRows: 100000,
      rowsPerHeapPage: 50,
      entriesPerIndexPage: 400,
      treeHeight: 3,
      selectivityPct: 0.01,
      randomIoMultiplier: 4,
      indexCanSeek: true,
      indexIsCovering: false
    }
  },
  {
    id: "narrow-range",
    title: "2. Narrow Range Scan (2% selectivity)",
    sqlExample: "SELECT * FROM Orders WHERE order_id BETWEEN 1000 AND 3000;",
    params: {
      totalRows: 100000,
      rowsPerHeapPage: 50,
      entriesPerIndexPage: 400,
      treeHeight: 3,
      selectivityPct: 2,
      randomIoMultiplier: 4,
      indexCanSeek: true,
      indexIsCovering: false
    }
  },
  {
    id: "wide-range-unclustered",
    title: "3. Wide Range (35% selectivity — Planner Ignores Index!)",
    sqlExample: "SELECT * FROM Orders WHERE order_id > 65000;",
    params: {
      totalRows: 100000,
      rowsPerHeapPage: 50,
      entriesPerIndexPage: 400,
      treeHeight: 3,
      selectivityPct: 35,
      randomIoMultiplier: 4,
      indexCanSeek: true,
      indexIsCovering: false
    }
  },
  {
    id: "non-sargable-covering",
    title: "4. Non-Seekable Predicate on Covering Index (Full Index Scan Wins!)",
    sqlExample: "SELECT order_id FROM Orders WHERE order_id % 10 = 0;  -- (cannot seek, but index covers SELECT)",
    params: {
      totalRows: 100000,
      rowsPerHeapPage: 50,
      entriesPerIndexPage: 400,
      treeHeight: 3,
      selectivityPct: 10,
      randomIoMultiplier: 4,
      indexCanSeek: false,
      indexIsCovering: true
    }
  },
  {
    id: "non-sargable-noncovering",
    title: "5. Non-Seekable + SELECT * (Full Table Scan Wins)",
    sqlExample: "SELECT * FROM Orders WHERE order_id + 1 = 42018;  -- (non-sargable, not covering)",
    params: {
      totalRows: 100000,
      rowsPerHeapPage: 50,
      entriesPerIndexPage: 400,
      treeHeight: 3,
      selectivityPct: 0.01,
      randomIoMultiplier: 4,
      indexCanSeek: false,
      indexIsCovering: false
    }
  }
];

export function evaluateIndexVsTableScan(p: IndexCostParams): IndexCostComparison {
  const heapPages = Math.max(1, Math.ceil(p.totalRows / Math.max(1, p.rowsPerHeapPage)));
  const indexLeafPages = Math.max(1, Math.ceil(p.totalRows / Math.max(1, p.entriesPerIndexPage)));
  const frac = Math.max(0.00001, Math.min(1, p.selectivityPct / 100));
  const matchingRows = Math.max(1, Math.round(p.totalRows * frac));

  // Mackert-Lohman / Cardenas expected distinct heap pages touched by `matchingRows` random RIDs
  const expectedHeapFetches = Math.min(
    matchingRows,
    Math.ceil(heapPages * (1 - Math.pow(1 - 1 / heapPages, matchingRows)))
  );

  // Plan 1: Full Sequential Table Scan (No Index)
  const fullTablePlan: PlanCostOption = {
    id: "full-table-scan",
    label: "Full Table Scan (Sequential Heap Scan)",
    available: true,
    pagesRead: heapPages,
    effectiveIoCost: Math.round(heapPages * 1.0),
    explanation: `Reads all ${heapPages.toLocaleString()} heap pages sequentially (1.0× sequential I/O per page). Ignores the B+ Tree completely.`
  };

  // Plan 2: B+ Tree Index Seek + Leaf Range (+ Heap Fetch if not covering)
  const seekLeafPages = Math.max(1, Math.ceil(indexLeafPages * frac));
  const seekPagesRead = p.indexIsCovering
    ? p.treeHeight + seekLeafPages
    : p.treeHeight + seekLeafPages + expectedHeapFetches;
  const seekEffectiveCost = p.indexIsCovering
    ? Math.round(p.treeHeight * p.randomIoMultiplier + seekLeafPages * 1.0)
    : Math.round(
        p.treeHeight * p.randomIoMultiplier +
          seekLeafPages * 1.0 +
          expectedHeapFetches * p.randomIoMultiplier
      );

  const indexSeekPlan: PlanCostOption = {
    id: "index-seek-heap",
    label: p.indexIsCovering
      ? "B+ Tree Index Seek (Index-Only)"
      : "B+ Tree Index Seek + Random Heap Fetches",
    available: p.indexCanSeek,
    pagesRead: seekPagesRead,
    effectiveIoCost: seekEffectiveCost,
    explanation: !p.indexCanSeek
      ? "Unavailable: predicate is non-sargable (e.g. function on key or non-leading composite column), so B+ Tree cannot seek from root."
      : p.indexIsCovering
        ? `Descends ${p.treeHeight} level(s), scans ${seekLeafPages.toLocaleString()} leaf page(s); no heap fetches needed because index is covering.`
        : `Descends ${p.treeHeight} level(s), scans ${seekLeafPages.toLocaleString()} leaf page(s), then performs ~${expectedHeapFetches.toLocaleString()} random heap page fetches (${p.randomIoMultiplier}× random I/O penalty).`
  };

  // Plan 3: Full Index Leaf Scan (Index-Only Scan — even when index CANNOT seek!)
  const fullIndexOnlyPlan: PlanCostOption = {
    id: "full-index-scan-only",
    label: "Full Index Leaf Scan (Index-Only — No Root Seek)",
    available: p.indexIsCovering,
    pagesRead: indexLeafPages,
    effectiveIoCost: Math.round(indexLeafPages * 1.0),
    explanation: !p.indexIsCovering
      ? "Unavailable: query requests columns not stored in the index (non-covering)."
      : `Scans all ${indexLeafPages.toLocaleString()} skinny B+ Tree leaf pages sequentially via leaf-linked pointers — ${Math.round((heapPages / indexLeafPages) * 10) / 10}× smaller than the ${heapPages.toLocaleString()}-page heap table!`
  };

  const plans = [fullTablePlan, indexSeekPlan, fullIndexOnlyPlan];
  const availablePlans = plans.filter((pl) => pl.available);
  const winner = availablePlans.reduce((best, cur) =>
    cur.effectiveIoCost < best.effectiveIoCost ? cur : best
  );

  let takeaway = "";
  if (winner.id === "full-table-scan" && p.indexCanSeek) {
    takeaway = `Even though the B+ Tree CAN seek, returning ${p.selectivityPct}% of rows requires ~${expectedHeapFetches.toLocaleString()} random heap fetches (cost ${indexSeekPlan.effectiveIoCost.toLocaleString()}) vs. reading ${heapPages.toLocaleString()} sequential heap pages. The planner chooses Full Table Scan!`;
  } else if (winner.id === "full-index-scan-only" && !p.indexCanSeek) {
    takeaway = `Even though the index CANNOT seek (non-sargable predicate), it is covering and only ${indexLeafPages.toLocaleString()} pages wide vs. ${heapPages.toLocaleString()} heap pages — so the planner STILL prefers a Full Index Leaf Scan over a Full Table Scan!`;
  } else if (winner.id === "full-table-scan" && !p.indexCanSeek) {
    takeaway = `The predicate cannot seek the B+ Tree AND the index does not cover all SELECT columns, so the planner falls back to a Full Table Scan (${heapPages.toLocaleString()} sequential pages).`;
  } else {
    takeaway = `High selectivity (${p.selectivityPct}%) lets the B+ Tree jump straight to the matching leaf pages with minimal I/O (cost ${winner.effectiveIoCost.toLocaleString()} vs. ${fullTablePlan.effectiveIoCost.toLocaleString()} for a Full Table Scan).`;
  }

  return {
    heapPages,
    indexLeafPages,
    matchingRows,
    plans,
    winner,
    takeaway
  };
}
