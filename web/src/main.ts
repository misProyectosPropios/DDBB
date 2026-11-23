import "./styles.css";
import { renderDerPage } from "./ui/derPage";
import { renderLoggingPage, type LoggingProtocol } from "./ui/loggingPage";
import { renderOverviewPage } from "./ui/overviewPage";
import { renderSidebar, type RouteId } from "./ui/sidebar";

function routeFromHash(): RouteId {
  const hash = window.location.hash.replace(/^#\/?/, "");
  if (hash === "overview") return "overview";
  if (hash === "logging/redo") return "redo";
  if (hash === "der") return "der";
  if (hash === "normalization") return "normalization";
  if (hash === "did" || hash === "nosql/document") return "nosql-document";
  if (hash === "nosql/graph") return "nosql-graph";
  if (hash === "nosql/column") return "nosql-column";
  if (hash === "nosql/key-value") return "nosql-keyvalue";
  return "undo";
}

let suppressHashChange = false;

function setHash(route: RouteId): void {
  const target =
    route === "overview"
      ? "#/overview"
      : route === "redo"
        ? "#/logging/redo"
        : route === "der"
          ? "#/der"
          : route === "normalization"
            ? "#/normalization"
            : route === "nosql-document"
              ? "#/nosql/document"
              : route === "nosql-graph"
                ? "#/nosql/graph"
                : route === "nosql-column"
                  ? "#/nosql/column"
                  : route === "nosql-keyvalue"
                    ? "#/nosql/key-value"
                    : "#/logging/undo";
  if (window.location.hash !== target) {
    window.location.hash = target;
  }
}

function renderApp(): void {
  const root = document.getElementById("app");
  if (!root) return;

  const route = routeFromHash();
  root.innerHTML = "";

  const navigate = (next: RouteId) => {
    setHash(next);
    renderApp();
  };

  const handleProtocolSwitch = (nextProtocol: LoggingProtocol) => {
    suppressHashChange = true;
    setHash(nextProtocol);
    // Sync sidebar highlight without resetting workbench state
    const existingSidebar = root.querySelector(".sidebar");
    if (existingSidebar) {
      const updated = renderSidebar(nextProtocol, (next) => {
        updated.classList.remove("is-open");
        navigate(next);
      });
      existingSidebar.replaceWith(updated);
    }
  };

  // Mobile header bar
  const mobileBar = document.createElement("div");
  mobileBar.className = "mobile-topbar";
  mobileBar.innerHTML = `
    <button type="button" class="btn btn-secondary btn-sm" data-toggle-sidebar aria-label="Toggle navigation">
      ☰ Menu
    </button>
    <span class="mobile-title">DDBB Notes</span>
  `;

  const sidebar = renderSidebar(route, (next) => {
    sidebar.classList.remove("is-open");
    navigate(next);
  });

  mobileBar.querySelector("[data-toggle-sidebar]")?.addEventListener("click", () => {
    root.querySelector(".sidebar")?.classList.toggle("is-open");
  });

  const main = document.createElement("main");
  main.className = "blog-main";
  main.appendChild(
    route === "overview"
      ? renderOverviewPage(navigate)
      : route === "der"
        ? renderDerPage("der")
        : route === "normalization"
          ? renderDerPage("normalization")
          : route === "nosql-document" ||
              route === "nosql-graph" ||
              route === "nosql-column" ||
              route === "nosql-keyvalue"
            ? renderDerPage(route)
            : renderLoggingPage(route, handleProtocolSwitch)
  );

  root.appendChild(mobileBar);
  root.appendChild(sidebar);
  root.appendChild(main);
}

window.addEventListener("hashchange", () => {
  if (suppressHashChange) {
    suppressHashChange = false;
    return;
  }
  renderApp();
});
renderApp();
