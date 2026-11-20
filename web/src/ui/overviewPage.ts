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
      </div>
    </section>
  `;

  article.querySelector<HTMLButtonElement>("[data-open-undo]")?.addEventListener("click", () => {
    onNavigate("undo");
  });
  article.querySelector<HTMLButtonElement>("[data-open-redo]")?.addEventListener("click", () => {
    onNavigate("redo");
  });

  return article;
}
