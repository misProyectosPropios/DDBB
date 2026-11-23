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
          <h3>Redo Logging</h3>
          <p>
            Records new values (<code>&lt;T, X, newVal&gt;</code>), enforces Rule R1 (WAL + commit
            flush before <code>OUTPUT</code>), supports Quiescent &amp; Non-Quiescent checkpointing,
            and runs forward Redo crash recovery.
          </p>
          <button type="button" class="btn btn-primary" data-open-redo>
            Open Redo Logging →
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
