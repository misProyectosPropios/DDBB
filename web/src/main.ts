import "./styles.css";
import { renderOverviewPage } from "./ui/overviewPage";
import { renderSidebar, type RouteId } from "./ui/sidebar";
import { renderUndoLoggingPage } from "./ui/undoPage";

function routeFromHash(): RouteId {
  const hash = window.location.hash.replace(/^#\/?/, "");
  if (hash === "overview") return "overview";
  return "undo";
}

function setHash(route: RouteId): void {
  const target = route === "overview" ? "#/overview" : "#/logging/undo";
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
    sidebar.classList.toggle("is-open");
  });

  const main = document.createElement("main");
  main.className = "blog-main";
  main.appendChild(
    route === "overview" ? renderOverviewPage(navigate) : renderUndoLoggingPage()
  );

  root.appendChild(mobileBar);
  root.appendChild(sidebar);
  root.appendChild(main);
}

window.addEventListener("hashchange", renderApp);
renderApp();
