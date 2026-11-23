// Static blog overview / landing page.

import type { RouteId } from "./sidebar";

export function renderOverviewPage(onNavigate: (route: RouteId) => void): HTMLElement {
  const article = document.createElement("article");
  article.className = "blog-article";

  article.innerHTML = `
    <header class="article-header">
      <div class="breadcrumb">DDBB Notes / Overview</div>
      <h1>Database Internals, Step by Step</h1>
      <p class="article-lead">
        An interactive handbook for relational and NoSQL database internals — recovery logging,
        schedulers, concurrency control, isolation levels, and schema design — backed by formal
        correctness proofs in Dafny.
      </p>
    </header>

    <section class="prose-section">
      <h2>Available Interactive Pages</h2>
      <p>
        Both Undo and Redo logging are available now, each composable with
        <strong>Quiescent</strong> and <strong>Non-Quiescent</strong> checkpointing and
        checkpoint-aware crash recovery.
      </p>

      <div class="topic-card-grid">
        <div class="topic-card topic-card-ready">
          <div class="topic-card-eyebrow">Logging · Available Now</div>
          <h3>Undo Logging</h3>
          <p>
            Records old values (<code>&lt;T, X, oldVal&gt;</code>), enforces Rules U1 &amp; U2,
            supports Quiescent &amp; Non-Quiescent checkpointing, and runs backward Undo crash recovery.
          </p>
          <button type="button" class="btn btn-primary" data-open-undo>
            Open Undo Logging →
          </button>
        </div>

        <div class="topic-card topic-card-ready">
          <div class="topic-card-eyebrow">Logging · Available Now</div>
          <h3>Redo &amp; Undo/Redo Logging</h3>
          <p>
            Redo records new values (<code>&lt;T, X, newVal&gt;</code>, Rule R1), while
            <strong>Undo/Redo Logging</strong> records 4-tuples
            (<code>&lt;T, X, oldVal, newVal&gt;</code>, Rule UR1 · STEAL/NO-FORCE) with two-pass
            crash recovery.
          </p>
          <div style="display:flex;gap:0.5rem;flex-wrap:wrap">
            <button type="button" class="btn btn-primary" data-open-redo>
              Open Redo →
            </button>
            <button type="button" class="btn btn-secondary" data-open-undoredo>
              Open Undo/Redo →
            </button>
          </div>
        </div>

        <div class="topic-card topic-card-ready">
          <div class="topic-card-eyebrow">Concurrency · Available Now</div>
          <h3>Scheduler, Dependency Graphs, Deadlocks &amp; OCC</h3>
          <p>
            Simulate <strong>2PL Lock Policies</strong> (Binary, S/X, Ternary S/U/X), visualize
            <strong>Conflict Precedence Graphs</strong>, resolve deadlocks with
            <strong>Wait-Die &amp; Wound-Wait</strong>, and compare with
            <strong>Kung–Robinson OCC</strong>.
          </p>
          <button type="button" class="btn btn-primary" data-open-sched>
            Open Scheduler &amp; Concurrency →
          </button>
        </div>

        <div class="topic-card topic-card-ready">
          <div class="topic-card-eyebrow">Concurrency · Available Now</div>
          <h3>Isolation Levels &amp; MVCC Simulator</h3>
          <p>
            Compare <strong>RC, CS, RR, Snapshot Isolation (SI), and Serializable MVCC (SSI)</strong>
            side by side, inspect multi-version tuple chains (<code>xmin ≤ startTs</code>), cursor
            pins, RR locks, <strong>First-Committer-Wins</strong>, and <strong>Write-Skew</strong>
            prevention.
          </p>
          <div style="display:flex;gap:0.5rem;flex-wrap:wrap">
            <button type="button" class="btn btn-primary" data-open-isolation>
              Open Isolation Levels →
            </button>
            <button type="button" class="btn btn-secondary" data-open-mvcc>
              Open MVCC Simulator →
            </button>
          </div>
        </div>

        <div class="topic-card topic-card-ready">
          <div class="topic-card-eyebrow">Storage &amp; Indexing · Available Now</div>
          <h3>B+ Tree Visualizer &amp; Index vs. Table Scan Cost</h3>
          <p>
            Visualize <strong>B+ Tree</strong> search, linked-leaf range iteration, Copy-Up/Push-Up
            splits, and sibling borrow/merge deletions, plus compare <strong>Index Seek</strong>,
            <strong>Full Table Scan</strong>, and <strong>Covering Full Index Leaf Scan</strong> I/O costs.
          </p>
          <button type="button" class="btn btn-primary" data-open-bplus>
            Open B+ Tree &amp; Index Cost →
          </button>
        </div>

        <div class="topic-card topic-card-ready">
          <div class="topic-card-eyebrow">SQL Design · Available Now</div>
          <h3>DER Editor → Relational Model &amp; SQL</h3>
          <p>
            Interactive canvas for Entities, 1:1 / 1:N / N:M / General (min..max) Relations, and
            Aggregations with straight lines &amp; editable corners, persistent storage, and
            verified DER → RM + Generic SQL conversion.
          </p>
          <button type="button" class="btn btn-primary" data-open-der>
            Open DER Editor →
          </button>
        </div>

        <div class="topic-card topic-card-ready">
          <div class="topic-card-eyebrow">SQL Design · Available Now</div>
          <h3>Normalization (1NF, 2NF, 3NF, BCNF)</h3>
          <p>
            Validates and converts schemas to 1NF, 2NF, 3NF (Bernstein synthesis), and BCNF, and
            verifies <strong>Lossless-Join (Chase Tableau)</strong> and
            <strong>Dependency Preservation (Ullman)</strong>.
          </p>
          <button type="button" class="btn btn-primary" data-open-norm>
            Open Normalization →
          </button>
        </div>

        <div class="topic-card topic-card-ready">
          <div class="topic-card-eyebrow">NoSQL · Available Now</div>
          <h3>NoSQL Models (Document, Graph, Column, Key-Value)</h3>
          <p>
            Reuses the DER editor to design <strong>Document (DID)</strong>,
            <strong>Graph</strong>, <strong>Column-Family</strong>, and
            <strong>Key-Value</strong> schemas with <strong>Partial or Complete Incrustations</strong>
            and <strong>Table Deletion / Weak Entity Absorption</strong>.
          </p>
          <button type="button" class="btn btn-primary" data-open-did>
            Open NoSQL Workbench →
          </button>
        </div>
      </div>
    </section>
  `;

  article.querySelector<HTMLButtonElement>("[data-open-undo]")?.addEventListener("click", () => {
    onNavigate("undo");
  });
  article.querySelector<HTMLButtonElement>("[data-open-redo]")?.addEventListener("click", () => {
    onNavigate("redo");
  });
  article.querySelector<HTMLButtonElement>("[data-open-undoredo]")?.addEventListener("click", () => {
    onNavigate("undo-redo");
  });
  article.querySelector<HTMLButtonElement>("[data-open-sched]")?.addEventListener("click", () => {
    onNavigate("sched-serializability");
  });
  article.querySelector<HTMLButtonElement>("[data-open-isolation]")?.addEventListener("click", () => {
    onNavigate("sched-isolation");
  });
  article.querySelector<HTMLButtonElement>("[data-open-mvcc]")?.addEventListener("click", () => {
    onNavigate("sched-mvcc");
  });
  article.querySelector<HTMLButtonElement>("[data-open-bplus]")?.addEventListener("click", () => {
    onNavigate("index-bplus");
  });
  article.querySelector<HTMLButtonElement>("[data-open-der]")?.addEventListener("click", () => {
    onNavigate("der");
  });
  article.querySelector<HTMLButtonElement>("[data-open-norm]")?.addEventListener("click", () => {
    onNavigate("normalization");
  });
  article.querySelector<HTMLButtonElement>("[data-open-did]")?.addEventListener("click", () => {
    onNavigate("nosql-document");
  });

  return article;
}
