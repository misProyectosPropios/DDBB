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
        We are building one topic at a time, starting with transaction recovery and logging.
        Use the sidebar on the left to browse the curriculum.
      </p>

      <div class="topic-card-grid">
        <div class="topic-card topic-card-ready">
          <div class="topic-card-eyebrow">Logging · Available Now</div>
          <h3>Undo Logging (Simple / Pure)</h3>
          <p>
            Define initial database variables (such as <code>X = 5</code>, <code>Y = 10</code>),
            build a schedule of transactions, inspect the generated Undo log records, trace
            <code>FLUSH LOG</code> and <code>OUTPUT</code> ordering (Rules U1 &amp; U2), and simulate crash recovery.
          </p>
          <button type="button" class="btn btn-primary" data-open-undo>
            Open Undo Logging →
          </button>
        </div>

        <div class="topic-card topic-card-muted">
          <div class="topic-card-eyebrow">Up Next</div>
          <h3>Redo, Undo/Redo &amp; Non-Quiescent Checkpointing</h3>
          <p>
            Additional logging strategies will plug into the same double-dispatch
            <code>LoggingStrategy</code> architecture without changing schedule definitions.
          </p>
        </div>
      </div>
    </section>
  `;

  const openUndoBtn = article.querySelector<HTMLButtonElement>("[data-open-undo]");
  openUndoBtn?.addEventListener("click", () => onNavigate("undo"));

  return article;
}
