// TypeScript port of `dafny/der/FunctionalDeps.dfy`,
// `dafny/der/DecompositionAnalysis.dfy`, and `dafny/der/Normalization.dfy`:
//   - Fixed-point Attribute Closure (X+)
//   - Exact Candidate-Key discovery with Core + Middle pruning
//   - Canonical Minimal Cover (singleton RHS -> LHS reduction -> redundant FD removal)
//   - FD Projection
//   - Aho-Beeri-Ullman Chase (Tableau) Lossless-Join algorithm
//   - Ullman's Polynomial Dependency-Preservation algorithm
//   - 1NF, 2NF, 3NF (Bernstein synthesis), and BCNF validators & converters

import { baseAtomicType, isAtomicType } from "./derToRelational";
import type {
  ChaseCell,
  Column,
  DecompositionReport,
  FD,
  ForeignKey,
  FunctionalDepInput,
  NormalForm,
  NormalizedRelation,
  RelationalSchema,
  TableSchema,
  ValidationReport
} from "./types";

// ---------------------------------------------------------------------------
// Set / Sequence helpers
// ---------------------------------------------------------------------------

function deduplicate(items: string[]): string[] {
  const seen = new Set<string>();
  const out: string[] = [];
  for (const x of items) {
    if (!seen.has(x)) {
      seen.add(x);
      out.push(x);
    }
  }
  return out;
}

function isSubset(sub: Iterable<string>, sup: Set<string>): boolean {
  for (const x of sub) {
    if (!sup.has(x)) return false;
  }
  return true;
}

function sameSet(a: string[], b: string[]): boolean {
  const sa = new Set(a);
  const sb = new Set(b);
  if (sa.size !== sb.size) return false;
  return isSubset(sa, sb);
}

function filterInOrder(order: string[], keep: Set<string>): string[] {
  return deduplicate(order).filter((x) => keep.has(x));
}

function allSubsets(items: string[]): string[][] {
  let result: string[][] = [[]];
  for (const x of items) {
    const withX = result.map((sub) => [...sub, x]);
    result = [...result, ...withX];
  }
  return result;
}

// ---------------------------------------------------------------------------
// Attribute Closure (X+) & Implication (`dafny/der/FunctionalDeps.dfy`)
// ---------------------------------------------------------------------------

export function attributeClosure(
  x: string[],
  fds: FD[],
  universe: string[]
): string[] {
  const uSet = new Set(universe);
  const acc = new Set(x.filter((a) => uSet.has(a)));

  let changed = true;
  while (changed) {
    changed = false;
    for (const fd of fds) {
      if (isSubset(fd.lhs, acc)) {
        for (const r of fd.rhs) {
          if (uSet.has(r) && !acc.has(r)) {
            acc.add(r);
            changed = true;
          }
        }
      }
    }
  }
  return filterInOrder(universe, acc);
}

export function impliesFD(fds: FD[], fd: FD, universe: string[]): boolean {
  const cl = new Set(attributeClosure(fd.lhs, fds, universe));
  return isSubset(fd.rhs, cl);
}

export function isTrivialFD(fd: FD): boolean {
  const lhsSet = new Set(fd.lhs);
  return isSubset(fd.rhs, lhsSet);
}

// ---------------------------------------------------------------------------
// Superkeys, Candidate Keys & Prime Attributes
// ---------------------------------------------------------------------------

export function isSuperkey(k: string[], attrsSeq: string[], fds: FD[]): boolean {
  const uSet = new Set(attrsSeq);
  if (!isSubset(k, uSet)) return false;
  const cl = new Set(attributeClosure(k, fds, attrsSeq));
  return isSubset(uSet, cl);
}

export function isCandidateKey(k: string[], attrsSeq: string[], fds: FD[]): boolean {
  if (!isSuperkey(k, attrsSeq, fds)) return false;
  for (const a of k) {
    const withoutA = k.filter((x) => x !== a);
    if (isSuperkey(withoutA, attrsSeq, fds)) return false;
  }
  return true;
}

export function shrinkToCandidateKey(
  start: string[],
  attrsSeq: string[],
  fds: FD[]
): string[] {
  let ck = filterInOrder(attrsSeq, new Set(start));
  for (const a of attrsSeq) {
    if (ck.includes(a)) {
      const withoutA = ck.filter((x) => x !== a);
      if (isSuperkey(withoutA, attrsSeq, fds)) {
        ck = withoutA;
      }
    }
  }
  return ck;
}

export function findCandidateKeys(attrsSeq: string[], fds: FD[]): string[][] {
  const uniqueAttrs = deduplicate(attrsSeq);
  if (uniqueAttrs.length === 0) return [];

  const nonTrivialRhs = new Set<string>();
  const allLhs = new Set<string>();
  for (const fd of fds) {
    const lhsSet = new Set(fd.lhs);
    for (const l of fd.lhs) allLhs.add(l);
    for (const r of fd.rhs) {
      if (!lhsSet.has(r)) nonTrivialRhs.add(r);
    }
  }

  const core = uniqueAttrs.filter((a) => !nonTrivialRhs.has(a));
  const coreSet = new Set(core);
  const middle = uniqueAttrs.filter((a) => allLhs.has(a) && !coreSet.has(a));

  const subs = allSubsets(middle);
  const cks: string[][] = [];
  for (const sub of subs) {
    const cand = filterInOrder(uniqueAttrs, new Set([...core, ...sub]));
    if (isCandidateKey(cand, uniqueAttrs, fds)) {
      if (!cks.some((existing) => sameSet(existing, cand))) {
        cks.push(cand);
      }
    }
  }

  if (cks.length === 0) {
    cks.push(shrinkToCandidateKey(uniqueAttrs, uniqueAttrs, fds));
  }
  return cks;
}

export function isPrimeAttribute(a: string, cks: string[][]): boolean {
  return cks.some((ck) => ck.includes(a));
}

// ---------------------------------------------------------------------------
// Canonical / Minimal Cover & FD Projection
// ---------------------------------------------------------------------------

export function computeMinimalCover(fds: FD[], attrsSeq: string[]): FD[] {
  const uniqueAttrs = deduplicate(attrsSeq);

  // Step 1: Singleton non-trivial RHS
  let singles: FD[] = [];
  for (const fd of fds) {
    const lhsSet = new Set(fd.lhs);
    for (const a of uniqueAttrs) {
      if (fd.rhs.includes(a) && !lhsSet.has(a)) {
        singles.push({ lhs: filterInOrder(uniqueAttrs, lhsSet), rhs: [a] });
      }
    }
  }

  // Step 2: Reduce extraneous LHS attributes
  let reduced = singles.map((fd) => ({ lhs: [...fd.lhs], rhs: [...fd.rhs] }));
  for (let i = 0; i < reduced.length; i++) {
    for (const b of uniqueAttrs) {
      const cur = reduced[i];
      if (cur.lhs.length > 1 && cur.lhs.includes(b)) {
        const candLhs = cur.lhs.filter((x) => x !== b);
        const cl = new Set(attributeClosure(candLhs, reduced, uniqueAttrs));
        if (isSubset(cur.rhs, cl)) {
          reduced[i] = { lhs: candLhs, rhs: cur.rhs };
        }
      }
    }
  }

  // Step 3: Remove redundant FDs
  const clean = [...reduced];
  let idx = 0;
  while (idx < clean.length) {
    const withoutIdx = [...clean.slice(0, idx), ...clean.slice(idx + 1)];
    if (impliesFD(withoutIdx, clean[idx], uniqueAttrs)) {
      clean.splice(idx, 1);
    } else {
      idx++;
    }
  }
  return clean;
}

export function projectFDs(
  subAttrsSeq: string[],
  fds: FD[],
  universe: string[]
): FD[] {
  const subAttrs = deduplicate(subAttrsSeq);
  const subSet = new Set(subAttrs);
  const allLhs = new Set<string>();
  for (const fd of fds) {
    for (const l of fd.lhs) allLhs.add(l);
  }
  const lhsSub = subAttrs.filter((a) => allLhs.has(a));
  const subs = allSubsets(lhsSub);

  const rawProj: FD[] = [];
  for (const x of subs) {
    if (x.length === 0) continue;
    const xSet = new Set(x);
    const cl = attributeClosure(x, fds, universe);
    const rhs = cl.filter((a) => subSet.has(a) && !xSet.has(a));
    if (rhs.length > 0) {
      rawProj.push({ lhs: x, rhs });
    }
  }

  return computeMinimalCover(rawProj, subAttrs);
}

// ---------------------------------------------------------------------------
// Chase (Tableau) Lossless-Join & Ullman Dependency-Preservation Algorithms
// ---------------------------------------------------------------------------

function cellRank(c: ChaseCell): number {
  return c.distinguished ? 0 : c.rowId + 1;
}

function minCell(c1: ChaseCell, c2: ChaseCell): ChaseCell {
  return cellRank(c1) <= cellRank(c2) ? { ...c1 } : { ...c2 };
}

function cloneTableau(tab: ChaseCell[][]): ChaseCell[][] {
  return tab.map((row) => row.map((cell) => ({ ...cell })));
}

export function checkLosslessJoinWithTableau(
  attrsSeq: string[],
  decomp: string[][],
  fds: FD[]
): {
  lossless: boolean;
  initialTableau: ChaseCell[][];
  finalTableau: ChaseCell[][];
} {
  const cols = deduplicate(attrsSeq);
  if (cols.length === 0) {
    return { lossless: true, initialTableau: [], finalTableau: [] };
  }
  if (decomp.length === 0) {
    return { lossless: false, initialTableau: [], finalTableau: [] };
  }

  const initialTableau: ChaseCell[][] = decomp.map((relAttrs, rIdx) => {
    const rSet = new Set(relAttrs);
    return cols.map((attr, cIdx) =>
      rSet.has(attr)
        ? { distinguished: true, label: `a${cIdx + 1}`, rowId: rIdx }
        : { distinguished: false, label: `b${rIdx + 1},${cIdx + 1}`, rowId: rIdx }
    );
  });

  const tab = cloneTableau(initialTableau);
  let changed = true;
  while (changed) {
    changed = false;
    for (const fd of fds) {
      const lhsIndices = cols
        .map((c, idx) => (fd.lhs.includes(c) ? idx : -1))
        .filter((idx) => idx >= 0);
      const rhsIndices = cols
        .map((c, idx) => (fd.rhs.includes(c) ? idx : -1))
        .filter((idx) => idx >= 0);

      for (let r1 = 0; r1 < tab.length; r1++) {
        for (let r2 = r1 + 1; r2 < tab.length; r2++) {
          const agree = lhsIndices.every(
            (cIdx) =>
              tab[r1][cIdx].distinguished === tab[r2][cIdx].distinguished &&
              tab[r1][cIdx].rowId === tab[r2][cIdx].rowId
          );
          if (agree) {
            for (const cIdx of rhsIndices) {
              const v1 = tab[r1][cIdx];
              const v2 = tab[r2][cIdx];
              if (
                v1.distinguished !== v2.distinguished ||
                v1.rowId !== v2.rowId
              ) {
                const m = minCell(v1, v2);
                tab[r1][cIdx] = { ...m };
                tab[r2][cIdx] = { ...m };
                changed = true;
              }
            }
          }
        }
      }
    }
  }

  const lossless = tab.some((row) => row.every((cell) => cell.distinguished));
  return { lossless, initialTableau, finalTableau: tab };
}

export function checkSingleFDPreserved(
  attrsSeq: string[],
  decomp: string[][],
  fds: FD[],
  fd: FD
): boolean {
  const universe = deduplicate(attrsSeq);
  const uSet = new Set(universe);
  const res = new Set(fd.lhs.filter((a) => uSet.has(a)));

  let changed = true;
  while (changed) {
    changed = false;
    for (const ri of decomp) {
      const riSet = new Set(ri.filter((a) => uSet.has(a)));
      const inter = [...res].filter((a) => riSet.has(a));
      const cl = attributeClosure(inter, fds, universe);
      for (const a of cl) {
        if (riSet.has(a) && !res.has(a)) {
          res.add(a);
          changed = true;
        }
      }
    }
  }
  return isSubset(fd.rhs, res);
}

export function checkDependencyPreserving(
  attrsSeq: string[],
  decomp: string[][],
  fds: FD[]
): { preserving: boolean; lost: FD[] } {
  const lost: FD[] = [];
  for (const fd of fds) {
    if (isTrivialFD(fd)) continue;
    if (!checkSingleFDPreserved(attrsSeq, decomp, fds, fd)) {
      lost.push(fd);
    }
  }
  return { preserving: lost.length === 0, lost };
}

export function analyzeDecomposition(
  attrsSeq: string[],
  decomp: string[][],
  rowNames: string[],
  fds: FD[]
): DecompositionReport {
  const cols = deduplicate(attrsSeq);
  const { lossless, initialTableau, finalTableau } =
    checkLosslessJoinWithTableau(cols, decomp, fds);
  const { preserving, lost } = checkDependencyPreserving(cols, decomp, fds);

  return {
    losslessJoin: lossless,
    dependencyPreserving: preserving,
    lostDependencies: lost,
    initialTableau,
    finalTableau,
    tableauColNames: cols,
    tableauRowNames: rowNames
  };
}

// ---------------------------------------------------------------------------
// Bridge: `RelationalSchema` + Extra FDs -> `NormalizedRelation[]`
// ---------------------------------------------------------------------------

export function buildNormalizedRelationsFromRM(
  rm: RelationalSchema,
  extraFDsByTable: Record<string, FunctionalDepInput[]>
): NormalizedRelation[] {
  return rm.tables.map((t) => {
    const colNames = deduplicate(t.columns.map((c) => c.name));
    const uSet = new Set(colNames);
    const pk = t.primaryKey.filter((p) => uSet.has(p));
    const nonPk = colNames.filter((c) => !pk.includes(c));
    const fds: FD[] = [];

    if (pk.length > 0 && nonPk.length > 0) {
      fds.push({ lhs: pk, rhs: nonPk });
    } else if (pk.length > 0) {
      fds.push({ lhs: pk, rhs: pk });
    }

    const extras = extraFDsByTable[t.name] ?? [];
    for (const ex of extras) {
      const lhs = ex.lhs.filter((a) => uSet.has(a));
      const rhs = ex.rhs.filter((a) => uSet.has(a));
      if (lhs.length > 0 && rhs.length > 0) {
        fds.push({ lhs, rhs });
      }
    }

    return { table: t, fds };
  });
}

// ---------------------------------------------------------------------------
// Normal Form Validators (1NF, 2NF, 3NF, BCNF)
// ---------------------------------------------------------------------------

export function isTable1NF(t: TableSchema): boolean {
  if (!t.name || t.primaryKey.length === 0) return false;
  const names = t.columns.map((c) => c.name);
  if (new Set(names).size !== names.length) return false;
  return t.columns.every((c) => isAtomicType(c.colType));
}

export function validateRelation(rel: NormalizedRelation): ValidationReport {
  const attrsSeq = deduplicate(rel.table.columns.map((c) => c.name));
  const cks = findCandidateKeys(attrsSeq, rel.fds);
  const primeAttributes = attrsSeq.filter((a) => isPrimeAttribute(a, cks));
  const violations: string[] = [];

  // 1NF check
  const is1NF = isTable1NF(rel.table);
  if (!is1NF) {
    for (const col of rel.table.columns) {
      if (!isAtomicType(col.colType)) {
        violations.push(
          `1NF violation: non-atomic multi-valued column '${col.name}' (${col.colType})`
        );
      }
    }
    if (violations.length === 0) {
      violations.push("1NF violation: duplicate column names or empty primary key");
    }
  }

  // 2NF check: no non-prime attribute depends on a proper subset of any candidate key
  let hasPartial = false;
  for (const ck of cks) {
    if (ck.length <= 1) continue;
    for (const b of ck) {
      const sub = ck.filter((x) => x !== b);
      const subSet = new Set(sub);
      const cl = attributeClosure(sub, rel.fds, attrsSeq);
      const partialNonPrimes = cl.filter(
        (a) => !subSet.has(a) && !isPrimeAttribute(a, cks)
      );
      if (partialNonPrimes.length > 0) {
        hasPartial = true;
        violations.push(
          `2NF violation: non-prime {${partialNonPrimes.join(", ")}} partially depends on proper subset {${sub.join(", ")}} of candidate key {${ck.join(", ")}}`
        );
      }
    }
  }
  const is2NF = is1NF && !hasPartial;

  // 3NF check
  let fails3NF = false;
  for (const fd of rel.fds) {
    if (isTrivialFD(fd)) continue;
    const superLhs = isSuperkey(fd.lhs, attrsSeq, rel.fds);
    if (!superLhs) {
      const lhsSet = new Set(fd.lhs);
      const badRhs = fd.rhs.filter(
        (a) => !lhsSet.has(a) && !isPrimeAttribute(a, cks)
      );
      if (badRhs.length > 0) {
        fails3NF = true;
        violations.push(
          `3NF violation: {${fd.lhs.join(", ")}} -> {${badRhs.join(", ")}} (LHS is not a superkey and RHS is non-prime)`
        );
      }
    }
  }
  const is3NF = is2NF && !fails3NF;

  // BCNF check
  let failsBCNF = false;
  for (const fd of rel.fds) {
    if (isTrivialFD(fd)) continue;
    if (!isSuperkey(fd.lhs, attrsSeq, rel.fds)) {
      failsBCNF = true;
      const lhsSet = new Set(fd.lhs);
      const nonTrivRhs = fd.rhs.filter((a) => !lhsSet.has(a));
      violations.push(
        `BCNF violation: {${fd.lhs.join(", ")}} -> {${nonTrivRhs.join(", ")}} (determinant {${fd.lhs.join(", ")}} is not a superkey)`
      );
    }
  }
  const isBCNF = is3NF && !failsBCNF;

  const highestForm: NormalForm = isBCNF
    ? "BCNF"
    : is3NF
      ? "3NF"
      : is2NF
        ? "2NF"
        : is1NF
          ? "1NF"
          : "UNF";

  return {
    tableName: rel.table.name,
    is1NF,
    is2NF,
    is3NF,
    isBCNF,
    highestForm,
    candidateKeys: cks,
    primeAttributes,
    violations: deduplicate(violations)
  };
}

// ---------------------------------------------------------------------------
// Sub-Relation Builder & Normal Form Converters (1NF, 2NF, 3NF, BCNF)
// ---------------------------------------------------------------------------

function buildSubRelation(
  name: string,
  baseCols: Column[],
  attrSet: Set<string>,
  parentFDs: FD[],
  parentUniverse: string[],
  preferredKey?: string[],
  foreignKeys: ForeignKey[] = []
): NormalizedRelation {
  const subCols = baseCols
    .filter((c) => attrSet.has(c.name))
    .map((c) => ({ name: c.name, colType: baseAtomicType(c.colType) }));
  const subAttrSeq = subCols.map((c) => c.name);
  const proj = projectFDs(subAttrSeq, parentFDs, parentUniverse);

  let pk: string[];
  if (
    preferredKey &&
    preferredKey.length > 0 &&
    preferredKey.every((k) => attrSet.has(k)) &&
    isCandidateKey(preferredKey, subAttrSeq, proj)
  ) {
    pk = preferredKey;
  } else {
    const cks = findCandidateKeys(subAttrSeq, proj);
    pk = cks[0] ?? subAttrSeq.slice(0, 1);
  }

  const nonPk = subAttrSeq.filter((a) => !pk.includes(a));
  const fdsWithPk =
    proj.length > 0
      ? proj
      : nonPk.length > 0
        ? [{ lhs: pk, rhs: nonPk }]
        : [{ lhs: pk, rhs: pk }];

  return {
    table: {
      name,
      columns: subCols,
      primaryKey: pk,
      foreignKeys,
      originKind: "normalized"
    },
    fds: fdsWithPk
  };
}

// 1NF Converter: Extracts multi-valued columns into child tables with composite PK + FK.
export function normalizeRelationTo1NF(
  rel: NormalizedRelation
): NormalizedRelation[] {
  if (isTable1NF(rel.table)) {
    return [rel];
  }

  const t = rel.table;
  const universe = deduplicate(t.columns.map((c) => c.name));
  const atomicCols = t.columns.filter((c) => isAtomicType(c.colType));
  const atomicNames = new Set(atomicCols.map((c) => c.name));

  const validFKs = t.foreignKeys.filter((fk) =>
    fk.columns.every((c) => atomicNames.has(c))
  );
  const baseAttrSeq = atomicCols.map((c) => c.name);
  const baseFDs = projectFDs(baseAttrSeq, rel.fds, universe);
  const basePk = t.primaryKey.filter((k) => atomicNames.has(k));
  const nonPk = baseAttrSeq.filter((c) => !basePk.includes(c));
  const effectiveBaseFDs =
    baseFDs.length > 0
      ? baseFDs
      : nonPk.length > 0
        ? [{ lhs: basePk, rhs: nonPk }]
        : [{ lhs: basePk, rhs: basePk }];

  const baseRel: NormalizedRelation = {
    table: {
      name: t.name,
      columns: atomicCols,
      primaryKey: basePk,
      foreignKeys: validFKs,
      originKind: t.originKind
    },
    fds: effectiveBaseFDs
  };

  const out: NormalizedRelation[] = [baseRel];
  const pkCols = atomicCols.filter((c) => basePk.includes(c.name));
  const pkNames = pkCols.map((c) => c.name);

  for (const col of t.columns) {
    if (!isAtomicType(col.colType)) {
      const elemCol: Column = {
        name: col.name,
        colType: baseAtomicType(col.colType)
      };
      const childCols = [...pkCols, elemCol];
      const childPK = [...pkNames, col.name];
      const childFk: ForeignKey = {
        columns: pkNames,
        refTable: t.name,
        refColumns: pkNames
      };
      out.push({
        table: {
          name: `${t.name}_${col.name}`,
          columns: childCols,
          primaryKey: childPK,
          foreignKeys: [childFk],
          originKind: "normalized"
        },
        fds: [{ lhs: childPK, rhs: childPK }]
      });
    }
  }
  return out;
}

// 2NF Converter: Recursive lossless decomposition removing partial dependencies.
function decomposeTo2NFRec(
  rel: NormalizedRelation,
  stepRef: { count: number }
): NormalizedRelation[] {
  const attrsSeq = deduplicate(rel.table.columns.map((c) => c.name));
  const cks = findCandidateKeys(attrsSeq, rel.fds);

  for (const ck of cks) {
    if (ck.length <= 1) continue;
    for (const b of ck) {
      const sub = ck.filter((x) => x !== b);
      const subSet = new Set(sub);
      const cl = attributeClosure(sub, rel.fds, attrsSeq);
      const dep = cl.filter((a) => !subSet.has(a) && !isPrimeAttribute(a, cks));
      if (dep.length > 0) {
        stepRef.count++;
        const depSet = new Set(dep);
        const r1Set = new Set([...sub, ...dep]);
        const r2Set = new Set(attrsSeq.filter((a) => !depSet.has(a)));

        const r1Name = `${rel.table.name}_${sub.join("_")}`;
        const r1 = buildSubRelation(
          r1Name,
          rel.table.columns,
          r1Set,
          rel.fds,
          attrsSeq,
          sub
        );
        const fkToR1: ForeignKey = {
          columns: sub,
          refTable: r1.table.name,
          refColumns: sub
        };
        const r2 = buildSubRelation(
          rel.table.name,
          rel.table.columns,
          r2Set,
          rel.fds,
          attrsSeq,
          ck,
          [...rel.table.foreignKeys.filter((fk) => fk.columns.every((c) => r2Set.has(c))), fkToR1]
        );

        return [
          ...decomposeTo2NFRec(r1, stepRef),
          ...decomposeTo2NFRec(r2, stepRef)
        ];
      }
    }
  }

  return [rel];
}

export function normalizeRelationTo2NF(
  rel: NormalizedRelation
): NormalizedRelation[] {
  const nf1 = normalizeRelationTo1NF(rel);
  const stepRef = { count: 0 };
  const out: NormalizedRelation[] = [];
  for (const r of nf1) {
    out.push(...decomposeTo2NFRec(r, stepRef));
  }
  return out;
}

// 3NF Converter: Bernstein's 3NF Synthesis Algorithm.
function synthesize3NF(rel: NormalizedRelation): NormalizedRelation[] {
  const rep = validateRelation(rel);
  if (rep.is3NF) return [rel];

  const attrsSeq = deduplicate(rel.table.columns.map((c) => c.name));
  const cks = rep.candidateKeys;
  const cover = computeMinimalCover(rel.fds, attrsSeq);

  // Group FDs in minimal cover by identical LHS
  const lhsGroups: { lhs: string[]; attrs: Set<string> }[] = [];
  for (const fd of cover) {
    const existing = lhsGroups.find((g) => sameSet(g.lhs, fd.lhs));
    if (existing) {
      for (const r of fd.rhs) existing.attrs.add(r);
    } else {
      lhsGroups.push({
        lhs: fd.lhs,
        attrs: new Set([...fd.lhs, ...fd.rhs])
      });
    }
  }

  // Eliminate redundant schemas (subset of another schema)
  const pruned = lhsGroups.filter((g, i) => {
    return !lhsGroups.some((other, j) => {
      if (i === j) return false;
      const isSub = isSubset(g.attrs, other.attrs);
      if (!isSub) return false;
      if (g.attrs.size < other.attrs.size) return true;
      return j < i;
    });
  });

  // Ensure at least one schema contains a candidate key
  const hasCK = pruned.some((g) =>
    cks.some((ck) => isSubset(ck, g.attrs))
  );
  if (!hasCK && cks.length > 0) {
    pruned.push({
      lhs: cks[0],
      attrs: new Set(cks[0])
    });
  }

  return pruned.map((g, idx) => {
    const suffix = g.lhs.join("_") || `${idx + 1}`;
    const tblName =
      pruned.length === 1 ? rel.table.name : `${rel.table.name}_3nf_${suffix}`;
    return buildSubRelation(
      tblName,
      rel.table.columns,
      g.attrs,
      rel.fds,
      attrsSeq,
      g.lhs
    );
  });
}

export function normalizeRelationTo3NF(
  rel: NormalizedRelation
): NormalizedRelation[] {
  const nf1 = normalizeRelationTo1NF(rel);
  const out: NormalizedRelation[] = [];
  for (const r of nf1) {
    out.push(...synthesize3NF(r));
  }
  return out;
}

// BCNF Converter: Recursive lossless BCNF decomposition.
function decomposeToBCNFRec(
  rel: NormalizedRelation,
  stepRef: { count: number }
): NormalizedRelation[] {
  const attrsSeq = deduplicate(rel.table.columns.map((c) => c.name));

  for (const fd of rel.fds) {
    if (!isTrivialFD(fd) && !isSuperkey(fd.lhs, attrsSeq, rel.fds)) {
      stepRef.count++;
      const x = fd.lhs;
      const xSet = new Set(x);
      const cl = attributeClosure(x, rel.fds, attrsSeq);
      const y = cl.filter((a) => !xSet.has(a));
      const ySet = new Set(y);

      const r1Set = new Set([...x, ...y]);
      const r2Set = new Set(attrsSeq.filter((a) => !ySet.has(a)));

      const r1Name = `${rel.table.name}_bcnf_${x.join("_")}`;
      const r1 = buildSubRelation(
        r1Name,
        rel.table.columns,
        r1Set,
        rel.fds,
        attrsSeq,
        x
      );
      const fkToR1: ForeignKey = {
        columns: x,
        refTable: r1.table.name,
        refColumns: x
      };
      const r2 = buildSubRelation(
        `${rel.table.name}_rest_${stepRef.count}`,
        rel.table.columns,
        r2Set,
        rel.fds,
        attrsSeq,
        undefined,
        [fkToR1]
      );

      return [
        ...decomposeToBCNFRec(r1, stepRef),
        ...decomposeToBCNFRec(r2, stepRef)
      ];
    }
  }

  return [rel];
}

export function normalizeRelationToBCNF(
  rel: NormalizedRelation
): NormalizedRelation[] {
  const nf1 = normalizeRelationTo1NF(rel);
  const stepRef = { count: 0 };
  const out: NormalizedRelation[] = [];
  for (const r of nf1) {
    out.push(...decomposeToBCNFRec(r, stepRef));
  }
  return out;
}

export function convertRelationToNormalForm(
  rel: NormalizedRelation,
  target: NormalForm
): NormalizedRelation[] {
  switch (target) {
    case "UNF":
      return [rel];
    case "1NF":
      return normalizeRelationTo1NF(rel);
    case "2NF":
      return normalizeRelationTo2NF(rel);
    case "3NF":
      return normalizeRelationTo3NF(rel);
    case "BCNF":
      return normalizeRelationToBCNF(rel);
  }
}
