// Left sidebar navigation for the static blog layout.
// Lists all planned DDBB curriculum sections as titles; Undo Logging and Redo
// Logging (with Quiescent & Non-Quiescent checkpointing) are active pages.

export type RouteId = "undo" | "redo" | "overview";

interface NavItem {
  label: string;
  route?: RouteId;
  status?: "active" | "soon";
}

interface NavSection {
  title: string;
  items: NavItem[];
}

export const NAV_SECTIONS: NavSection[] = [
  {
    title: "Logging",
    items: [
      { label: "Undo Logging", route: "undo", status: "active" },
      { label: "Redo Logging", route: "redo", status: "active" },
      { label: "Undo / Redo Logging", status: "soon" }
    ]
  },
  {
    title: "Scheduler & Concurrency",
    items: [
      { label: "Scheduler & Serializability", status: "soon" },
      { label: "Dependency Graphs", status: "soon" },
      { label: "Isolation Levels (RR, RC, CS)", status: "soon" },
      { label: "Deadlock Visualizer", status: "soon" },
      { label: "Optimistic & Pessimistic Control", status: "soon" },
      { label: "MVCC Simulator", status: "soon" }
    ]
  },
  {
    title: "SQL Design & Internals",
    items: [
      { label: "DER to Generic SQL", status: "soon" },
      { label: "Triggers & Stored Procedures", status: "soon" },
      { label: "Normalization", status: "soon" }
    ]
  },
  {
    title: "NoSQL",
    items: [
      { label: "DID", status: "soon" },
      { label: "DER to Column-Family", status: "soon" },
      { label: "DER to Workflow & Entities", status: "soon" }
    ]
  }
];

export function renderSidebar(
  currentRoute: RouteId,
  onNavigate: (route: RouteId) => void
): HTMLElement {
  const aside = document.createElement("aside");
  aside.className = "sidebar";
  aside.setAttribute("aria-label", "DDBB Topics Navigation");

  const header = document.createElement("div");
  header.className = "sidebar-brand";

  const brandBtn = document.createElement("button");
  brandBtn.type = "button";
  brandBtn.className = "brand-button";
  brandBtn.innerHTML = `
    <span class="brand-mark">DB</span>
    <span class="brand-copy">
      <span class="brand-title">DDBB Notes</span>
      <span class="brand-subtitle">Interactive Database Guide</span>
    </span>
  `;
  brandBtn.addEventListener("click", () => onNavigate("overview"));
  header.appendChild(brandBtn);
  aside.appendChild(header);

  const nav = document.createElement("nav");
  nav.className = "sidebar-nav";

  const overviewLink = document.createElement("button");
  overviewLink.type = "button";
  overviewLink.className = `nav-link nav-link-top${currentRoute === "overview" ? " is-current" : ""}`;
  overviewLink.textContent = "Overview";
  overviewLink.addEventListener("click", () => onNavigate("overview"));
  nav.appendChild(overviewLink);

  for (const section of NAV_SECTIONS) {
    const group = document.createElement("div");
    group.className = "nav-section";

    const heading = document.createElement("div");
    heading.className = "nav-section-title";
    heading.textContent = section.title;
    group.appendChild(heading);

    const list = document.createElement("ul");
    list.className = "nav-list";

    for (const item of section.items) {
      const li = document.createElement("li");
      if (item.route) {
        const btn = document.createElement("button");
        btn.type = "button";
        btn.className = `nav-link${currentRoute === item.route ? " is-current" : ""}`;
        btn.innerHTML = `
          <span class="nav-dot"></span>
          <span>${item.label}</span>
        `;
        btn.addEventListener("click", () => onNavigate(item.route!));
        li.appendChild(btn);
      } else {
        const span = document.createElement("span");
        span.className = "nav-item-disabled";
        span.setAttribute("aria-disabled", "true");
        span.innerHTML = `
          <span>${item.label}</span>
          <span class="nav-soon">Soon</span>
        `;
        li.appendChild(span);
      }
      list.appendChild(li);
    }

    group.appendChild(list);
    nav.appendChild(group);
  }

  aside.appendChild(nav);

  const footer = document.createElement("div");
  footer.className = "sidebar-footer";
  footer.innerHTML = `
    <span class="verified-pill">Verified in Dafny</span>
    <p>Algorithms mirror the formally verified specs in <code>dafny/logging/</code>.</p>
  `;
  aside.appendChild(footer);

  return aside;
}
