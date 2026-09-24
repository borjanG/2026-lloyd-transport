/* A Lloyd-stabilized Voronoï particle method — visual paper.
   Dependency graph (HTML nodes over an SVG edge layer, hand-made layout),
   reading panel, search, routing.  Data comes from site/data.js, which
   site/build.py generates from the LaTeX source. */
(function () {
  "use strict";
  const D = window.PAPER;
  const N = D.nodes;
  const META = D.meta;
  const $ = (sel, root) => (root || document).querySelector(sel);
  const $$ = (sel, root) => Array.from((root || document).querySelectorAll(sel));

  // The macro list must match site/tools/check-math.mjs.
  const MACROS = {
    "\\R": "\\mathbb{R}", "\\N": "\\mathbb{N}", "\\diff": "\\mathrm{d}", "\\dist": "\\operatorname{dist}",
    "\\supp": "\\operatorname{supp}", "\\le": "\\leqslant", "\\leq": "\\leqslant", "\\ge": "\\geqslant",
    "\\geq": "\\geqslant", "\\mbox": "\\text",
  };

  const GROUP_OF_KIND = {};
  for (const k of Object.keys(D.kinds)) GROUP_OF_KIND[k] = D.kinds[k].group;
  const GROUP_ORDER = ["theorem", "result", "estimate", "definition", "remark", "figure", "section", "external"];
  const groupOf = (id) => GROUP_OF_KIND[N[id].kind] || "definition";
  const paperOrder = D.order.filter((id) => N[id].kind !== "external");
  const readingOrder = paperOrder; // sections interleaved with their parts, as in the paper

  // ------------------------------------------------------------------ utilities
  const esc = (s) => String(s == null ? "" : s).replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
  function store(key, value) { try { if (value === null) localStorage.removeItem(key); else localStorage.setItem(key, value); } catch (e) {} }
  function load(key) { try { return localStorage.getItem(key); } catch (e) { return null; } }

  function renderMath(root) {
    $$(".math, .math-display", root).forEach((el) => {
      if (el.dataset.rendered) return;
      const tex = el.dataset.tex || "";
      try {
        katex.render(tex, el, { displayMode: el.classList.contains("math-display"), macros: MACROS, throwOnError: false, strict: "ignore", trust: false });
      } catch (e) {
        el.textContent = tex;
      }
      el.dataset.rendered = "1";
    });
  }

  function numberOf(id) {
    const n = N[id];
    if (n.number) return n.number;
    if (n.kind === "external") return "External input";
    return (D.kinds[n.kind] || {}).label || n.kind;
  }
  function shortNumber(id) {
    const n = N[id];
    if (n.shortNumber) return n.shortNumber;
    if (n.kind === "section") return n.number.replace("Section ", "§").replace("Appendix ", "App. ");
    if (n.number) return n.number.replace(/^Estimates? /, "").replace(/^Figures? /, "Fig. ").replace(/^Appendix B, /, "App. B · ");
    if (n.kind === "external") return "input";
    return (D.kinds[n.kind] || {}).label || n.kind;
  }

  // ------------------------------------------------------------------ state
  const state = {
    selected: null,       // node id shown in the panel (or null for welcome / bib / notation)
    graphMode: "map",     // "map" | "focus"
    hops: 1,
    panelView: "welcome", // welcome | node | bib | notation
  };

  // ------------------------------------------------------------------ graph layout
  // Map view: one lane per section, in the order of the paper.  A lane shows its
  // primary parts (numbered results, figures, the results marked "primary");
  // the other parts are folded into the lane head until it is expanded.  Edges
  // of folded parts are lifted to the lane head, so "§1 -> Theorem 3.1" reads
  // "definitions of Section 1 are used in Theorem 3.1".
  const NODE_W = 164, NODE_H = 60, GAP = 14, LANE_PAD = 12, LANE_HEAD = 152, HEAD_ONLY_W = 200, LANE_GAP = 30, MARGIN = 26, ROW_MAX_W = 1080;
  const BIG_W = 236, BIG_H = 88;
  const PRIMARY_KINDS = new Set(["theorem", "corollary", "proposition", "lemma", "figure"]);
  const isPrimary = (id) => PRIMARY_KINDS.has(N[id].kind) || !!N[id].primary;

  const sections = D.order.filter((id) => N[id].kind === "section");
  const expandedLanes = new Set();
  const edgesAll = D.edges;
  const usesOf = (id) => N[id].uses || [];
  const usedByOf = (id) => N[id].usedBy || [];

  function laneChildren(sid) {
    const kids = N[sid].children || [];
    return expandedLanes.has(sid) ? kids : kids.filter(isPrimary);
  }

  function mapLayout() {
    const pos = {}, lanes = [], hidden = {};   // hidden: folded node id -> its lane id
    const geo = {};
    sections.forEach((sid) => {
      const kids = laneChildren(sid);
      const perRow = kids.length > 4 ? Math.ceil(kids.length / 2) : Math.max(1, kids.length);
      const rows = kids.length ? Math.ceil(kids.length / perRow) : 0;
      const contentW = kids.length ? perRow * (NODE_W + GAP) - GAP : 0;
      const w = kids.length ? LANE_HEAD + LANE_PAD + contentW + LANE_PAD : HEAD_ONLY_W;
      const h = kids.length ? rows * NODE_H + (rows - 1) * GAP + 2 * LANE_PAD : 46;
      (N[sid].children || []).forEach((c) => { if (!kids.includes(c)) hidden[c] = sid; });
      geo[sid] = { sid, kids, perRow, rows, contentW, w, h };
    });
    const mainIds = sections.filter((sid) => !N[sid].number.startsWith("Appendix"));
    const appIds = sections.filter((sid) => N[sid].number.startsWith("Appendix"));
    const mainW = Math.max(...mainIds.map((sid) => geo[sid].w));
    const appW = appIds.length ? Math.max(...appIds.map((sid) => geo[sid].w)) : 0;
    const placeLane = (sid, x, y, w) => {
      const g = geo[sid];
      lanes.push({ id: sid, x, y, w, h: g.h, headW: g.kids.length ? LANE_HEAD : w, folded: (N[sid].children || []).length - g.kids.length, expanded: expandedLanes.has(sid), headOnly: !g.kids.length });
      const contentW = w - LANE_HEAD - 2 * LANE_PAD;
      const startX = x + LANE_HEAD + LANE_PAD;
      g.kids.forEach((cid, j) => {
        const r = Math.floor(j / g.perRow), c = j % g.perRow;
        const inRow = Math.min(g.perRow, g.kids.length - r * g.perRow);
        const rowW = inRow * (NODE_W + GAP) - GAP;
        const off = (contentW - rowW) / 2;
        pos[cid] = { x: startX + off + c * (NODE_W + GAP), y: y + LANE_PAD + r * (NODE_H + GAP), w: NODE_W, h: NODE_H, lane: sid };
      });
    };
    // main column
    const rowY = {};
    let y = MARGIN;
    mainIds.forEach((sid) => { rowY[sid] = y; placeLane(sid, MARGIN, y, mainW); y += geo[sid].h + LANE_GAP; });
    let totalH = y - LANE_GAP + MARGIN;
    // appendix column, each lane level with the first main section that uses one of its parts
    const appX = MARGIN + mainW + LANE_GAP + 10;
    let lastBottom = MARGIN;
    appIds.forEach((sid) => {
      const users = new Set();
      (N[sid].children || []).forEach((c) => usedByOf(c).forEach((u) => { const lane = N[u].parent || (N[u].kind === "section" ? u : null); if (lane && rowY[lane] != null) users.add(lane); }));
      let ay = users.size ? Math.min(...Array.from(users).map((l) => rowY[l])) : lastBottom;
      ay = Math.max(ay, lastBottom);
      placeLane(sid, appX, ay, appW);
      lastBottom = ay + geo[sid].h + LANE_GAP;
      totalH = Math.max(totalH, ay + geo[sid].h + MARGIN);
    });
    lanes.forEach((L) => { pos[L.id] = { x: L.x, y: L.y, w: L.headW, h: L.h, head: true, lane: L.id }; });
    const seen = new Set(), edges = [];
    edgesAll.forEach((e) => {
      let a = e.from, b = e.to;
      if (hidden[a]) a = hidden[a];
      if (hidden[b]) b = hidden[b];
      if (!pos[a] || !pos[b] || a === b) return;
      if (N[a].kind === "section" && N[b].kind === "section") return;
      if ((hidden[e.from] && hidden[e.from] === pos[b].lane) || (hidden[e.to] && hidden[e.to] === pos[a].lane)) return; // folded part of the same lane
      const key = a + ">" + b;
      if (seen.has(key)) return;
      seen.add(key);
      edges.push({ from: a, to: b, lifted: a !== e.from || b !== e.to });
    });
    const totalW = appX + (appIds.length ? appW : 0) + MARGIN;
    return { pos, lanes, edges, labels: [], world: { w: totalW, h: totalH }, hidden };
  }

  function sortIds(ids) {
    return ids.slice().sort((a, b) => {
      const ga = GROUP_ORDER.indexOf(groupOf(a)), gb = GROUP_ORDER.indexOf(groupOf(b));
      if (ga !== gb) return ga - gb;
      return D.order.indexOf(a) - D.order.indexOf(b);
    });
  }

  function focusLayout(center, hops) {
    const levels = { 0: [center] };
    const seen = new Set([center]);
    let frontier = [center];
    for (let l = 1; l <= hops; l++) {
      const next = [];
      frontier.forEach((id) => usesOf(id).forEach((u) => { if (!seen.has(u)) { seen.add(u); next.push(u); } }));
      levels[-l] = sortIds(next); frontier = next;
    }
    frontier = [center];
    for (let l = 1; l <= hops; l++) {
      const next = [];
      frontier.forEach((id) => usedByOf(id).forEach((u) => { if (!seen.has(u)) { seen.add(u); next.push(u); } }));
      levels[l] = sortIds(next); frontier = next;
    }
    const colGap = 104, rowGap = 12, h = NODE_H, w = NODE_W;
    const heights = {};
    let maxH = BIG_H;
    Object.keys(levels).forEach((l) => { const n = levels[l].length; heights[l] = Math.max(0, n * (h + rowGap) - rowGap); maxH = Math.max(maxH, heights[l]); });
    const topPad = 70;
    const cy = topPad + maxH / 2;
    const pos = {}, labels = [], level = { [center]: 0 };
    const cx0 = MARGIN + hops * (w + colGap) + BIG_W / 2;
    pos[center] = { x: cx0 - BIG_W / 2, y: cy - BIG_H / 2, w: BIG_W, h: BIG_H, big: true };
    Object.keys(levels).map(Number).filter((l) => l !== 0).forEach((l) => {
      const ids = levels[l];
      const x = l < 0 ? cx0 - BIG_W / 2 - colGap * (-l) - w * (-l) : cx0 + BIG_W / 2 + colGap * l + w * (l - 1);
      const top = cy - heights[l] / 2;
      ids.forEach((id, i) => { pos[id] = { x, y: top + i * (h + rowGap), w, h }; level[id] = l; });
      if (ids.length) labels.push({ x, y: Math.min(top, cy - BIG_H / 2) - 28, w, text: l < 0 ? (l === -1 ? "Uses" : "Used further back") : (l === 1 ? "Used by" : "Used further on") });
    });
    // the section the result belongs to, as a chip above it
    const parent = N[center].parent;
    if (parent) { pos[parent] = { x: cx0 - 130, y: cy - BIG_H / 2 - 62, w: 260, h: 34, chip: true }; }
    const width = MARGIN * 2 + BIG_W + 2 * hops * (w + colGap);
    const edges = edgesAll.filter((e) => pos[e.from] && pos[e.to] && !(pos[e.from].chip || pos[e.to].chip) && Math.abs(level[e.from] - level[e.to]) === 1).map((e) => ({ from: e.from, to: e.to }));
    return { pos, lanes: [], edges, labels, world: { w: width, h: topPad + maxH + MARGIN + 20 }, center, focus: true };
  }

  // ------------------------------------------------------------------ graph rendering
  const viewport = $("#graph-viewport"), world = $("#graph-world"), edgeSvg = $("#graph-edges"), edgeLayer = $("#graph-edge-layer"), nodeLayer = $("#graph-nodes");
  let layout = null;
  const view = { tx: 0, ty: 0, s: 1 };

  function applyView() { world.style.transform = `translate(${view.tx}px, ${view.ty}px) scale(${view.s})`; }
  function fitView(animate) {
    if (!layout) return;
    const vw = viewport.clientWidth, vh = viewport.clientHeight;
    if (!vw || !vh) return;
    const top = 64, bottom = $("#graph-legend").offsetHeight ? $("#graph-legend").offsetHeight + 24 : 24, side = 18;
    const s = Math.min((vw - side * 2) / layout.world.w, (vh - top - bottom) / layout.world.h, 1.1);
    view.s = Math.max(0.2, s);
    view.tx = (vw - layout.world.w * view.s) / 2;
    view.ty = top + Math.max(0, (vh - top - bottom - layout.world.h * view.s) / 2);
    if (animate) { world.style.transition = "transform .35s ease"; setTimeout(() => (world.style.transition = ""), 380); }
    applyView();
  }
  function zoomAt(factor, px, py) {
    const ns = Math.min(3, Math.max(0.2, view.s * factor));
    const k = ns / view.s;
    view.tx = px - (px - view.tx) * k;
    view.ty = py - (py - view.ty) * k;
    view.s = ns;
    applyView();
  }
  function zoomCenter(factor) { zoomAt(factor, viewport.clientWidth / 2, viewport.clientHeight / 2); }

  function edgePath(a, b) {
    const ax = a.x + a.w / 2, bx = b.x + b.w / 2, ay = a.y + a.h / 2, by = b.y + b.h / 2;
    if (layout.focus) {
      const fromRight = a.x < b.x;
      const x1 = fromRight ? a.x + a.w : a.x, x2 = fromRight ? b.x : b.x + b.w;
      const dx = (x2 - x1) * 0.5;
      return `M${x1},${ay} C${x1 + dx},${ay} ${x2 - dx},${by} ${x2},${by}`;
    }
    const sameBand = Math.abs(ay - by) < NODE_H;   // same row of boxes
    if (sameBand && !a.head && !b.head) {
      const adjacent = Math.abs(bx - ax) <= NODE_W + GAP + 2 && a.lane === b.lane;
      if (adjacent) {
        const x1 = bx > ax ? a.x + a.w : a.x, x2 = bx > ax ? b.x : b.x + b.w;
        return `M${x1},${ay} L${x2},${by}`;
      }
      // hop underneath the boxes in between
      const y1 = a.y + a.h, y2 = b.y + b.h, hop = 34;
      return `M${ax},${y1} C${ax},${y1 + hop} ${bx},${y2 + hop} ${bx},${y2}`;
    }
    if (by >= ay) { // target below (or a head in the same band: leave from the bottom)
      const y1 = a.y + a.h, y2 = b.y;
      if (y2 <= y1) { const hop = 34; return `M${ax},${y1} C${ax},${y1 + hop} ${bx},${b.y + b.h + hop} ${bx},${b.y + b.h}`; }
      const dy = Math.max(18, (y2 - y1) * 0.5);
      return `M${ax},${y1} C${ax},${y1 + dy} ${bx},${y2 - dy} ${bx},${y2}`;
    }
    const y1 = a.y, y2 = b.y + b.h;  // target above
    if (y2 >= y1) { const hop = 34; return `M${ax},${y1} C${ax},${y1 - hop} ${bx},${b.y - hop} ${bx},${b.y}`; }
    const dy = Math.max(18, (y1 - y2) * 0.5);
    return `M${ax},${y1} C${ax},${y1 - dy} ${bx},${y2 + dy} ${bx},${y2}`;
  }

  function nodeHtml(id, p) {
    const n = N[id];
    if (p.head) {
      const lane = layout.lanes.find((L) => L.id === id);
      const more = lane && lane.folded > 0 ? `<span class="glane__more">+${lane.folded} more</span>` : lane && lane.expanded ? `<span class="glane__more">fold</span>` : "";
      return `<div class="glane__headwrap${lane && lane.headOnly ? " is-headonly" : ""}" style="left:${p.x}px;top:${p.y}px;width:${p.w}px;height:${p.h}px">
        <button type="button" class="glane__head" data-id="${esc(id)}" title="Read ${esc(n.number)}: ${esc(n.title)}"><span class="glane__num">${esc(shortNumber(id))}</span><span class="glane__title">${esc(n.shortTitle || n.title)}</span></button>
        ${lane && (lane.folded > 0 || lane.expanded) ? `<button type="button" class="glane__toggle" data-toggle-lane="${esc(id)}" aria-expanded="${lane.expanded}" title="${lane.expanded ? "Fold the section's parts" : "Show all parts of the section"}">${more}</button>` : ""}</div>`;
    }
    if (p.chip) {
      return `<button type="button" class="gnode gnode--chip gnode--section" data-id="${esc(id)}" style="left:${p.x}px;top:${p.y}px;width:${p.w}px;height:${p.h}px" title="Read ${esc(n.number)}"><span class="gnode__title">${esc(shortNumber(id))} · ${esc(n.shortTitle || n.title)}</span></button>`;
    }
    const g = groupOf(id);
    const lean = n.lean && n.lean.length ? '<span class="gnode__lean" title="Components checked in Lean">✓</span>' : "";
    return `<button type="button" class="gnode gnode--${g}${p.big ? " gnode--big" : ""}" data-id="${esc(id)}" style="left:${p.x}px;top:${p.y}px;width:${p.w}px;height:${p.h}px" title="${esc(numberOf(id))} — ${esc(n.title)}">
      <span class="gnode__num">${esc(shortNumber(id))}</span><span class="gnode__title">${esc(p.big ? n.title : (n.shortTitle || n.title))}</span>${lean}</button>`;
  }

  function renderGraph(opts) {
    opts = opts || {};
    const wasFocus = layout && layout.focus;
    layout = state.graphMode === "focus" && state.selected && N[state.selected].kind !== "section"
      ? focusLayout(state.selected, state.hops) : mapLayout();
    world.style.width = layout.world.w + "px"; world.style.height = layout.world.h + "px";
    edgeSvg.setAttribute("width", layout.world.w); edgeSvg.setAttribute("height", layout.world.h);
    edgeSvg.setAttribute("viewBox", `0 0 ${layout.world.w} ${layout.world.h}`);
    let html = "";
    layout.lanes.forEach((L) => {
      html += `<div class="glane${L.expanded ? " is-expanded" : ""}" data-lane="${esc(L.id)}" style="left:${L.x}px;top:${L.y}px;width:${L.w}px;height:${L.h}px"></div>`;
    });
    layout.labels.forEach((l) => { html += `<div class="gcol-label" style="left:${l.x}px;top:${l.y}px;width:${l.w}px">${esc(l.text)}</div>`; });
    Object.keys(layout.pos).forEach((id) => { html += nodeHtml(id, layout.pos[id]); });
    nodeLayer.innerHTML = html;
    edgeLayer.innerHTML = layout.edges.map((e) => `<path class="graph-edge${e.lifted ? " graph-edge--lifted" : ""}" data-from="${esc(e.from)}" data-to="${esc(e.to)}" d="${edgePath(layout.pos[e.from], layout.pos[e.to])}"/>`).join("");
    updateGraphSelection();
    $("[data-focus-controls]").hidden = !layout.focus;
    $(".graph-btn--map").classList.toggle("is-active", !layout.focus);
    $("[data-graph-hint]").textContent = layout.focus
      ? "Left: what it uses. Right: what uses it. Click any box to go there."
      : "Click a result to read it and see what it uses and what uses it. Click a section title to read the section; “+ more” shows its definitions and estimates.";
    if (opts.keepView && !!wasFocus === !!layout.focus) applyView(); else fitView(false);
  }

  function updateGraphSelection() {
    const sel = state.selected;
    const nb = new Set();
    if (sel) { usesOf(sel).forEach((u) => nb.add(layout.hidden && layout.hidden[u] ? layout.hidden[u] : u)); usedByOf(sel).forEach((u) => nb.add(layout.hidden && layout.hidden[u] ? layout.hidden[u] : u)); nb.add(sel); if (N[sel].parent) nb.add(N[sel].parent); }
    const dimming = !!sel && !layout.focus && N[sel].kind !== "section";
    $$(".gnode", nodeLayer).forEach((el) => {
      const id = el.dataset.id;
      el.classList.toggle("is-selected", id === sel);
      el.classList.toggle("is-dim", dimming && !nb.has(id));
    });
    $$(".glane__head", nodeLayer).forEach((el) => { el.classList.toggle("is-selected", el.dataset.id === sel); el.classList.toggle("is-related", dimming && nb.has(el.dataset.id) && el.dataset.id !== sel); });
    $$(".glane", nodeLayer).forEach((el) => {
      const lane = el.dataset.lane;
      el.classList.toggle("is-dim", dimming && !nb.has(lane) && !(N[lane].children || []).some((c) => nb.has(c)));
    });
    $$(".graph-edge", edgeLayer).forEach((p) => {
      const inc = sel && (p.dataset.from === sel || p.dataset.to === sel);
      p.classList.toggle("is-hi", !!inc);
      p.classList.toggle("is-dim", dimming && !inc);
    });
  }

  // pan & zoom (pointer events; wheel zooms around the cursor; two fingers pinch)
  (function panZoom() {
    let dragging = false, moved = false, sx = 0, sy = 0, ox = 0, oy = 0, pinchDist = 0, downTarget = null;
    const pointers = new Map();
    viewport.addEventListener("pointerdown", (e) => {
      if (e.button !== 0) return;
      pointers.set(e.pointerId, e);
      downTarget = e.target;  // pointer capture retargets later events to the viewport
      if (pointers.size === 1) { dragging = true; moved = false; sx = e.clientX; sy = e.clientY; ox = view.tx; oy = view.ty; }
      else if (pointers.size === 2) { const [a, b] = Array.from(pointers.values()); pinchDist = Math.hypot(a.clientX - b.clientX, a.clientY - b.clientY); }
      viewport.setPointerCapture(e.pointerId);
    });
    viewport.addEventListener("pointermove", (e) => {
      if (!pointers.has(e.pointerId)) return;
      pointers.set(e.pointerId, e);
      if (pointers.size === 2) {
        const [a, b] = Array.from(pointers.values());
        const d = Math.hypot(a.clientX - b.clientX, a.clientY - b.clientY);
        if (pinchDist) { const r = viewport.getBoundingClientRect(); zoomAt(d / pinchDist, (a.clientX + b.clientX) / 2 - r.left, (a.clientY + b.clientY) / 2 - r.top); }
        pinchDist = d; moved = true; return;
      }
      if (!dragging) return;
      const dx = e.clientX - sx, dy = e.clientY - sy;
      if (!moved && Math.hypot(dx, dy) > 4) { moved = true; viewport.classList.add("is-panning"); }
      if (moved) { view.tx = ox + dx; view.ty = oy + dy; applyView(); }
    });
    const end = (e) => {
      pointers.delete(e.pointerId);
      if (pointers.size < 2) pinchDist = 0;
      if (pointers.size === 0) {
        dragging = false; viewport.classList.remove("is-panning");
        if (!moved && downTarget) {
          const t = downTarget; downTarget = null;
          const tog = t.closest && t.closest("[data-toggle-lane]");
          if (tog) { toggleLane(tog.dataset.toggleLane); return; }
          const btn = t.closest && t.closest("[data-id]");
          if (btn) selectFromGraph(btn.dataset.id);
        }
      }
    };
    viewport.addEventListener("pointerup", end);
    viewport.addEventListener("pointercancel", end);
    viewport.addEventListener("wheel", (e) => {
      e.preventDefault();
      const r = viewport.getBoundingClientRect();
      const factor = Math.exp(-e.deltaY * (e.deltaMode === 1 ? 0.05 : 0.0015));
      zoomAt(factor, e.clientX - r.left, e.clientY - r.top);
    }, { passive: false });
    nodeLayer.addEventListener("keydown", (e) => {
      if (e.key !== "Enter" && e.key !== " ") return;
      if (e.target.dataset.toggleLane) { e.preventDefault(); toggleLane(e.target.dataset.toggleLane); }
      else if (e.target.dataset.id) { e.preventDefault(); selectFromGraph(e.target.dataset.id); }
    });
    new ResizeObserver(() => fitView(false)).observe(viewport);
  })();

  function toggleLane(sid) {
    if (expandedLanes.has(sid)) expandedLanes.delete(sid); else expandedLanes.add(sid);
    renderGraph({ keepView: false });
  }

  function selectFromGraph(id) {
    if (N[id].kind === "section") { state.graphMode = "map"; if (location.hash === "#" + id) { lastHash = null; route(); } else location.hash = "#" + id; return; }
    state.graphMode = "focus";
    if (location.hash === "#" + id) { lastHash = null; route(); } else location.hash = "#" + id;
    if (window.matchMedia("(max-width: 900px)").matches) setPane("panel");
  }

  // ------------------------------------------------------------------ panel rendering
  const panel = $("#panel"), content = $("#panel-content");

  function kindBadge(id) {
    const n = N[id], g = groupOf(id);
    return `<span class="badge badge--kind chip--${g}">${esc((D.kinds[n.kind] || {}).label || n.kind)}</span>`;
  }
  function chip(id) {
    const n = N[id];
    return `<a class="chip chip--${groupOf(id)}" href="#${esc(id)}"><span class="chip__num">${esc(shortNumber(id))}</span><span class="chip__title">${esc(n.title)}</span></a>`;
  }
  function chips(ids, emptyText) {
    if (!ids || !ids.length) return `<p class="chips--empty">${esc(emptyText)}</p>`;
    return `<div class="chips">${sortIds(ids).map(chip).join("")}</div>`;
  }
  function leanBadge(n) {
    if (!n.lean || !n.lean.length) return "";
    return `<a class="badge badge--lean" href="${esc(n.lean[0].url)}" target="_blank" rel="noopener" title="Components of this argument are checked in Lean; see below">Lean ✓ ${n.lean.length > 1 ? n.lean.length + " files" : n.lean[0].file.split("/").pop()}</a>`;
  }
  function leanSection(n) {
    if (!n.lean || !n.lean.length) return "";
    return `<div class="section-label">Lean formalization</div>
      <ul class="lean-list">${n.lean.map((l) => `<li><a href="${esc(l.url)}" target="_blank" rel="noopener">${esc(l.file)}</a><p>${l.noteHtml || ""}</p></li>`).join("")}</ul>
      <p class="lean-note">Checked components with explicitly stated inputs, not an end-to-end formalization of the result; see the <a href="${esc(META.leanTargetsUrl)}" target="_blank" rel="noopener">targets</a> and <a href="${esc(META.leanStatusUrl)}" target="_blank" rel="noopener">status</a> notes.</p>`;
  }
  function pager(id) {
    const i = readingOrder.indexOf(id);
    if (i < 0) return "";
    const prev = readingOrder[i - 1], next = readingOrder[i + 1];
    return `<nav class="pager" aria-label="Previous and next in the paper">
      ${prev ? `<a href="#${esc(prev)}"><span>Previous</span><span>${esc(shortNumber(prev))} · ${esc(N[prev].title)}</span></a>` : "<span></span>"}
      ${next ? `<a href="#${esc(next)}"><span>Next</span><span>${esc(shortNumber(next))} · ${esc(N[next].title)}</span></a>` : ""}
    </nav>`;
  }
  function sourceLine(n) {
    if (!n.sourceLine) return "";
    return `<p class="source-line">Source: <a href="${esc(META.repoUrl)}/blob/main/site/source/v7.tex#L${n.sourceLine}" target="_blank" rel="noopener">manuscript source, line ${n.sourceLine}</a>.</p>`;
  }

  function movieArrow(label) {
    return `<svg viewBox="0 0 44 18" aria-hidden="true"><path d="M2 9h36" stroke="currentColor" stroke-width="1.8" fill="none"/><path d="M32 3.5 40 9l-8 5.5" stroke="currentColor" stroke-width="1.8" fill="none" stroke-linejoin="round"/></svg><span>${esc(label)}</span>`;
  }
  function moviesHtml() {
    const m = META.movies;
    return `<div class="movies">
      <div class="movies__grid">
        <figure class="movie"><video data-movie="${esc(m[0].id)}" controls muted loop playsinline preload="none" poster="${esc(m[0].poster)}"><source src="${esc(m[0].src)}" type="video/mp4"></video><figcaption><p class="movie__title">${esc(m[0].title)}</p><p class="movie__caption">${esc(m[0].caption)}</p></figcaption></figure>
        <div class="movies__arrow">${movieArrow("Lloyd")}</div>
        <figure class="movie"><video data-movie="${esc(m[1].id)}" controls muted loop playsinline preload="none" poster="${esc(m[1].poster)}"><source src="${esc(m[1].src)}" type="video/mp4"></video><figcaption><p class="movie__title">${esc(m[1].title)}</p><p class="movie__caption">${esc(m[1].caption)}</p></figcaption></figure>
      </div>
      <div class="movies__bar"><button type="button" class="btn btn--small btn--primary" data-action="play-both">▶ Play both together</button><button type="button" class="btn btn--small" data-action="restart-both">↺ Restart</button>
        <a class="btn btn--small" href="${esc(m[0].src)}" download>Download mp4 (without)</a><a class="btn btn--small" href="${esc(m[1].src)}" download>Download mp4 (with)</a></div>
      <p class="movies__note">${META.movieNoteHtml || ""}</p>
    </div>`;
  }
  function figureCard(f, opts) {
    const imgs = f.images || [];
    let inner = "";
    if (f.arrow && imgs.length === 2) {
      inner = `<div class="fig__images"><div style="flex:1 1 200px;min-width:0"><img class="fig__img" src="${esc(imgs[0].src)}" alt="${esc(imgs[0].alt)}" loading="lazy"><div class="fig__label">${esc(imgs[0].label || "")}</div></div>
        <div class="fig__arrow">${movieArrow(f.arrow)}</div>
        <div style="flex:1 1 200px;min-width:0"><img class="fig__img" src="${esc(imgs[1].src)}" alt="${esc(imgs[1].alt)}" loading="lazy"><div class="fig__label">${esc(imgs[1].label || "")}</div></div></div>`;
    } else {
      inner = `<div class="fig__images">${imgs.map((im) => `<img class="fig__img fig__img--wide" src="${esc(im.src)}" alt="${esc(im.alt)}" loading="lazy">`).join("")}</div>`;
    }
    const movies = f.movies && opts && opts.movies !== false ? moviesHtml() : "";
    return `<figure class="fig" id="${esc(f.label)}">${inner}<figcaption><b>Figure ${esc(f.num)}.</b> ${f.captionHtml}</figcaption>${movies}</figure>`;
  }
  function figureBlocksOf(label) {
    for (const id of D.order) {
      const n = N[id];
      if (n.figureBlocks) for (const f of n.figureBlocks) if (f.label === label) return f;
    }
    return null;
  }

  function renderNode(id, opts) {
    const n = N[id];
    const g = groupOf(id);
    let html = "";
    const where = n.where ? `<span class="badge badge--where">${esc(n.where)}</span>` : "";
    html += `<div class="node-head" style="--k-border:var(--k-${g});--k-bg:var(--k-${g}-bg);--k-ink:var(--k-${g}-ink)">
      <div class="node-head__eyebrow">${kindBadge(id)}${where}${leanBadge(n)}</div>
      <h2 class="node-head__title">${n.number ? `<span class="mono">${esc(n.number)}</span>` : ""}${esc(n.title)}</h2></div>`;

    if (n.kind === "section") {
      html += `<div class="section-label section-label--tight">In brief</div><div class="prose prose--summary">${n.summaryHtml || ""}</div>`;
      if (n.children && n.children.length) html += `<div class="section-label">In this section</div>${chips(n.children)}`;
      html += `<div class="section-label">The paper's text</div><div class="prose prose--body">${n.bodyHtml || ""}</div>`;
    } else if (n.kind === "external") {
      html += `<div class="section-label section-label--tight">What is used</div><div class="prose">${n.summaryHtml || ""}</div>`;
      if (n.citations && n.citations.length) {
        html += `<div class="section-label">References</div><ol class="biblist">${n.citations.map((c) => `<li id="bib:${esc(c.key)}"><span class="biblist__num">[${c.num}]</span><span>${c.html}${c.url ? ` <a class="biblist__link" href="${esc(c.url)}" target="_blank" rel="noopener">link</a>` : ""}</span></li>`).join("")}</ol>`;
      }
      html += `<div class="section-label">Used by</div>${chips(usedByOf(id), "Not used elsewhere.")}`;
    } else {
      if (n.summaryHtml) html += `<div class="section-label section-label--tight">${n.kind === "figure" ? "What it shows" : "What it says"}</div><div class="prose prose--summary">${n.summaryHtml}</div><p class="summary-note">A summary in plain words, not the paper's text. ${["theorem", "corollary", "proposition", "lemma"].includes(n.kind) ? "The exact statement follows." : "The paper's own text follows."}</p>`;
      if (n.noteHtml) html += `<div class="prose"><p class="summary-note" style="font-size:13px">${n.noteHtml}</p></div>`;
      if (n.figureBlocks) {
        html += `<div class="section-label">Figures</div>` + n.figureBlocks.map((f) => figureCard(f, {})).join("");
      }
      if (n.statementHtml) {
        const head = n.kind === "figure" ? "Discussion in the paper" : (n.kind === "definition" || n.kind === "remark" || n.kind === "example" || n.kind === "estimate") ? "The paper's text" : "Statement";
        html += `<div class="section-label" id="statement">${head}</div>
          <div class="statement" style="--k-border:var(--k-${g});--k-bg:var(--k-${g === "theorem" ? "result" : g}-bg)">${n.numberOnly ? `<div class="statement__head"><span>${esc(n.number)}.</span></div>` : ""}<div class="prose">${n.statementHtml}</div></div>`;
      }
      if (n.ideaHtml) html += `<div class="section-label">Proof idea</div><div class="prose prose--summary">${n.ideaHtml}</div>`;
      if (n.proofHtml) html += `<div class="section-label" id="proof">Proof <button type="button" class="proof-toggle" data-action="toggle-proof" aria-expanded="true">Collapse</button></div><div class="proof prose" data-proof>${n.proofHtml}<p class="proof__end">□</p></div>`;
      html += `<div class="section-label">Uses</div>${chips(usesOf(id), "Nothing outside its own definitions.")}`;
      html += `<div class="section-label">Used by</div>${chips(usedByOf(id), "Not used by later results.")}`;
      html += leanSection(n);
      html += sourceLine(n);
    }
    html += pager(id);
    setPanel(html);
    // fill figure slots inside section bodies
    $$(".figure-slot", content).forEach((slot) => {
      const f = figureBlocksOf(slot.dataset.figure);
      if (f) { slot.outerHTML = figureCard(f, { movies: true }); }
    });
    $$(".result-card[data-node]", content).forEach((card) => {
      const t = card.dataset.node; if (t && N[t]) card.classList.add("result-card--" + N[t].kind);
    });
    renderMath(content);
    fitDisplays();
    afterRender(opts);
  }

  function renderWelcome() {
    const authors = META.authors.map((a) => esc(a.name)).join(" and ");
    const affil = Array.from(new Set(META.authors.map((a) => a.affiliation))).map(esc).join(" · ");
    const paperLinks = [
      META.arxivId ? `<a class="btn" href="https://arxiv.org/abs/${esc(META.arxivId)}" target="_blank" rel="noopener">arXiv:${esc(META.arxivId)}</a>` : "",
      META.pdfUrl ? `<a class="btn" href="${esc(META.pdfUrl)}" target="_blank" rel="noopener">PDF</a>` : "",
    ].join("");
    const start = META.startHere.map((id, i) => `<a class="btn ${i === 0 ? "btn--primary" : ""}" href="#${esc(id)}">${i === 0 ? "Start with " : ""}${esc(N[id].kind === "section" ? "Read the " + N[id].title.toLowerCase() : N[id].number)}</a>`).join("");
    const nTheorems = D.order.filter((id) => ["theorem", "corollary", "proposition"].includes(N[id].kind)).length;
    const html = `<div class="welcome">
      <div class="welcome__kicker">${esc(META.kicker)}</div>
      <h1 class="welcome__title">${esc(META.title)}</h1>
      <div class="welcome__authors">${authors}</div>
      <div class="welcome__affil">${affil}</div>
      ${paperLinks ? `<div class="btn-row">${paperLinks}</div>` : ""}
      <div class="welcome__abstract prose">${META.abstractHtml}</div>
      <div class="btn-row">${start}<a class="btn" href="#bib">References</a></div>
      <div class="section-label">The stabilization in one picture</div>
      ${moviesHtml()}
      <div class="section-label">How to read this page</div>
      <div class="howto"><p>The graph on the left is the paper's dependency structure: its sections, and inside them the definitions, the ${nTheorems} numbered results, the labelled estimates, the figures. An arrow from A to B means that A is used in B. Click a box to read it here; the graph then shows what it uses (left) and what uses it (right). Click a section title to read the section as in the paper.</p>
      <ul><li>Each result comes with a short summary in plain words, the exact statement and proof from the manuscript, what it uses and what uses it. Summaries and proof ideas are marked as such; everything else is the paper's own text.</li>
      <li>Equation numbers such as (2.3) and citations such as [8] are links. <a href="#notation">Notation</a> and <a href="#bib">references</a> have pages of their own.</li>
      <li>A green ✓ marks results of which components are checked in Lean; the badge links to the Lean file, and the section at the bottom of the page says precisely what is checked and what is assumed.</li>
      <li>Keys: <kbd>/</kbd> search, <kbd>g</kbd> hide the graph, <kbd>f</kbd> expand it, <kbd>t</kbd> theme, <kbd>+</kbd> <kbd>−</kbd> <kbd>0</kbd> zoom.</li></ul></div>
      <div class="section-label">Lean formalization</div>
      <div class="howto"><p>Four targeted arguments of the paper have Lean proofs with explicitly stated inputs: the periodic face identity and the one-sided estimate <span class="math" data-tex="\\mathscr T_v\\le4L\\mathscr F"></span>, the removal–insertion bounds behind Corollary 3.2, the centroid drift, non-collision and energy identity behind Theorem 4.1, and the mollification estimate of Appendix B. Neither Theorem 4.1 nor the full Section 5 extension is certified end to end. See the <a href="${esc(META.leanReadmeUrl)}" target="_blank" rel="noopener">Lean project</a>, its <a href="${esc(META.leanTargetsUrl)}" target="_blank" rel="noopener">targets</a> and <a href="${esc(META.leanStatusUrl)}" target="_blank" rel="noopener">status</a>.</p></div>
      <div class="section-label">Cite</div>
      <pre class="bibtex">${esc(META.bibtex)}<button type="button" class="btn btn--small bibtex__copy" data-action="copy-bibtex">Copy</button></pre>
      <div class="welcome__foot">
        <p>© ${esc(META.year)} ${authors}. ${esc(META.funding || "")}</p>
        <p>${esc(META.editorialNote || "")}</p>
        <p>Built from the manuscript source with <code>site/build.py</code>; the site and the Lean project live at <a href="${esc(META.repoUrl)}" target="_blank" rel="noopener">${esc(META.repoUrl.replace("https://", ""))}</a>. Mathematics rendered with <a href="https://katex.org" target="_blank" rel="noopener">KaTeX</a> (MIT).</p>
      </div></div>`;
    setPanel(html);
    renderMath(content);
    afterRender({});
  }

  function renderBibliography(key) {
    const items = D.bibliography.map((b) => `<li id="bib:${esc(b.key)}"><span class="biblist__num">[${b.num}]</span><span>${b.html}${b.url ? ` <a class="biblist__link" href="${esc(b.url)}" target="_blank" rel="noopener">${esc(b.url.replace(/^https?:\/\/(doi\.org\/)?/, "").slice(0, 40))}</a>` : ""}</span></li>`).join("");
    setPanel(`<div class="node-head"><div class="node-head__eyebrow"><span class="badge">Bibliography</span></div><h2 class="node-head__title">References</h2><p class="node-head__meta">${D.bibliography.length} items, numbered as in the manuscript. Citations throughout the text link here.</p></div><ol class="biblist">${items}</ol>`);
    renderMath(content);
    afterRender({ anchorId: key ? "bib:" + key : null });
  }

  function renderNotation() {
    const rows = D.notation.map((n) => `<tr><td><span class="math" data-tex="${esc(n.sym)}"></span></td><td>${n.textHtml}</td><td>${n.node && N[n.node] ? `<a href="#${esc(n.node)}">${esc(N[n.node].shortNumber || N[n.node].number || N[n.node].shortTitle || N[n.node].title)}</a>` : ""}</td></tr>`).join("");
    setPanel(`<div class="node-head"><div class="node-head__eyebrow"><span class="badge">Notation</span></div><h2 class="node-head__title">Notation</h2><p class="node-head__meta">The recurring symbols of the paper, with the place where each is introduced.</p></div><table class="notation"><tbody>${rows}</tbody></table>`);
    renderMath(content);
    afterRender({});
  }

  function setPanel(html) { content.innerHTML = html; panel.scrollTop = 0; }

  // Shrink display equations that are wider than the panel (down to 72%), instead of clipping the tag.
  function fitDisplays() {
    $$(".math-display", content).forEach((el) => {
      el.style.fontSize = "";
      const inner = el.firstElementChild; if (!inner) return;
      const avail = el.clientWidth, need = inner.scrollWidth;
      if (need > avail + 1) el.style.fontSize = Math.max(0.72, avail / (need + 8)).toFixed(3) + "em";
    });
  }
  let fitTimer = null;
  new ResizeObserver(() => { clearTimeout(fitTimer); fitTimer = setTimeout(fitDisplays, 60); }).observe(panel);

  function afterRender(opts) {
    opts = opts || {};
    let target = null;
    if (opts.eqLabel) target = document.getElementById(opts.eqLabel) || $(`[data-labels~="${opts.eqLabel}"]`, content);
    else if (opts.anchorId) target = document.getElementById(opts.anchorId);
    if (target) {
      requestAnimationFrame(() => {
        target.scrollIntoView({ block: "center", behavior: "smooth" });
        target.classList.remove("is-flash"); void target.offsetWidth; target.classList.add("is-flash");
      });
    }
  }

  // ------------------------------------------------------------------ routing
  let lastHash = null;
  function route() {
    const raw = decodeURIComponent(location.hash.replace(/^#/, ""));
    if (raw === lastHash) return;
    const previous = state.selected;
    let id = null, anchorId = null, eqLabel = null, viewName = "node";
    if (!raw || raw === "welcome") { viewName = "welcome"; }
    else if (raw === "bib" || raw.startsWith("bib/")) { viewName = "bib"; anchorId = raw.split("/")[1] || null; }
    else if (raw === "notation") { viewName = "notation"; }
    else if (raw.startsWith("eq/") || raw.startsWith("fig/")) {
      // an anchor route: stay on the current page if it shows the target, else go to the page that does
      eqLabel = raw.slice(raw.indexOf("/") + 1);
      const info = D.labels[eqLabel];
      if (!info) { viewName = "welcome"; }
      else if (state.panelView === "node" && state.selected && document.getElementById(eqLabel)) { id = state.selected; }
      else if (state.selected && info.nodes && info.nodes.includes(state.selected)) { id = state.selected; }
      else { id = (info.nodes && info.nodes[0]) || info.node; }
      if (id && !N[id]) { viewName = "welcome"; }
    } else {
      const parts = raw.split("/");
      id = parts[0]; anchorId = parts[1] || null;
      if (!N[id]) { const lab = D.labels[id]; if (lab && lab.node) { id = lab.node; anchorId = raw; } else viewName = "welcome"; }
    }
    lastHash = raw;
    if (viewName === "welcome") { state.selected = null; state.panelView = "welcome"; state.graphMode = "map"; renderWelcome(); }
    else if (viewName === "bib") { state.panelView = "bib"; state.selected = null; state.graphMode = "map"; renderBibliography(anchorId); }
    else if (viewName === "notation") { state.panelView = "notation"; state.selected = null; state.graphMode = "map"; renderNotation(); }
    else {
      const sameNode = id === previous && state.panelView === "node" && content.children.length;
      state.panelView = "node";
      state.selected = id;
      if (N[id].kind === "section") state.graphMode = "map";
      else if (!sameNode) state.graphMode = "focus";
      if (N[id].parent && !isPrimary(id)) expandedLanes.add(N[id].parent);
      if (sameNode && (eqLabel || anchorId)) afterRender({ eqLabel, anchorId });
      else renderNode(id, { eqLabel, anchorId });
    }
    document.title = (state.selected ? `${numberOf(state.selected)} · ${N[state.selected].title} — ` : "") + META.shortTitle + " — visual paper";
    if (state.panelView !== "node") { if (state.graphMode === "focus") state.graphMode = "map"; }
    renderGraph();
    if (window.matchMedia("(max-width: 900px)").matches && state.panelView !== "welcome" && lastHash) setPane("panel");
  }
  window.addEventListener("hashchange", route);

  // ------------------------------------------------------------------ actions
  document.addEventListener("click", (e) => {
    const actionEl = e.target.closest("[data-action]");
    if (actionEl) {
      const a = actionEl.dataset.action;
      if (a === "home") { location.hash = ""; if (!location.hash) route(); }
      else if (a === "whole-map") { state.graphMode = "map"; renderGraph(); }
      else if (a === "hops-1" || a === "hops-2") { state.hops = a === "hops-1" ? 1 : 2; $$("[data-focus-controls] .segmented__btn").forEach((b) => { const on = b.dataset.action === a; b.classList.toggle("is-active", on); b.setAttribute("aria-pressed", on); }); renderGraph(); }
      else if (a === "zoom-in") zoomCenter(1.25);
      else if (a === "zoom-out") zoomCenter(0.8);
      else if (a === "fit") fitView(true);
      else if (a === "expand-graph") toggleExpand();
      else if (a === "toggle-graph") toggleGraph();
      else if (a === "toggle-theme") toggleTheme();
      else if (a === "text-smaller") setTextScale(textScale - 0.1);
      else if (a === "text-larger") setTextScale(textScale + 0.1);
      else if (a === "text-reset") setTextScale(1);
      else if (a === "toggle-proof") {
        const body = $("[data-proof]", content); const open = body.hasAttribute("hidden");
        body.toggleAttribute("hidden", !open); actionEl.textContent = open ? "Collapse" : "Expand"; actionEl.setAttribute("aria-expanded", open);
      }
      else if (a === "play-both") { $$("video[data-movie]", content).forEach((v) => { v.currentTime = 0; v.play().catch(() => {}); }); }
      else if (a === "restart-both") { $$("video[data-movie]", content).forEach((v) => { v.pause(); v.currentTime = 0; }); }
      else if (a === "copy-bibtex") { navigator.clipboard && navigator.clipboard.writeText(META.bibtex).then(() => { actionEl.textContent = "Copied"; setTimeout(() => (actionEl.textContent = "Copy"), 1500); }); }
      else if (a === "lightbox-close") $("#lightbox").close();
      return;
    }
    const fn = e.target.closest(".fn-mark");
    if (fn) { fn.closest(".footnote").classList.toggle("is-open"); return; }
    const img = e.target.closest(".fig__img");
    if (img) { openLightbox(img); return; }
    const pane = e.target.closest("[data-pane]");
    if (pane) { setPane(pane.dataset.pane); return; }
    // clicking a link to the current hash should still re-route (e.g. equation in the same node)
    const link = e.target.closest('a[href^="#"]');
    if (link) {
      const h = link.getAttribute("href");
      if (h === location.hash) { e.preventDefault(); lastHash = null; route(); }
    }
  });

  function openLightbox(img) {
    const lb = $("#lightbox");
    $(".lightbox__body", lb).innerHTML = `<img src="${esc(img.getAttribute("src"))}" alt="${esc(img.alt)}">`;
    lb.showModal();
  }
  $("#lightbox").addEventListener("click", (e) => { if (e.target === e.currentTarget) e.currentTarget.close(); });

  // graph hide / expand
  const layoutEl = $("#layout");
  function toggleGraph(force) {
    const hide = force != null ? force : !layoutEl.classList.contains("layout--no-graph");
    layoutEl.classList.toggle("layout--no-graph", hide);
    layoutEl.classList.remove("layout--expanded");
    const b = $('[data-action="toggle-graph"]'); b.setAttribute("aria-pressed", hide); b.textContent = hide ? "Show graph" : "Hide graph";
    store("lloyd-graph-hidden", hide ? "1" : null);
    setTimeout(() => fitView(false), 30);
  }
  function toggleExpand() {
    const on = !layoutEl.classList.contains("layout--expanded");
    layoutEl.classList.toggle("layout--expanded", on);
    layoutEl.classList.remove("layout--no-graph");
    $('[data-action="expand-graph"]').setAttribute("aria-pressed", on);
    setTimeout(() => fitView(true), 30);
  }

  // theme
  function currentTheme() {
    const t = document.documentElement.dataset.theme;
    if (t) return t;
    return window.matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light";
  }
  function toggleTheme() {
    const next = currentTheme() === "dark" ? "light" : "dark";
    document.documentElement.dataset.theme = next;
    store("lloyd-theme", next);
  }

  // text size
  let textScale = parseFloat(load("lloyd-text-scale") || "1") || 1;
  function setTextScale(v) {
    textScale = Math.round(Math.min(1.5, Math.max(0.8, v)) * 10) / 10;
    panel.style.setProperty("--reading-scale", textScale);
    $('[data-action="text-reset"]').title = `Text size ${Math.round(textScale * 100)}% (click to reset)`;
    store("lloyd-text-scale", textScale === 1 ? null : String(textScale));
  }
  setTextScale(textScale);

  // panes (mobile)
  function setPane(name) {
    $$(".tabbar__btn").forEach((b) => b.classList.toggle("is-active", b.dataset.pane === name));
    $("#graph-pane").classList.toggle("is-active", name === "graph");
    $("#panel").classList.toggle("is-active", name === "panel");
    if (name === "graph") setTimeout(() => fitView(false), 30);
  }

  // divider
  (function divider() {
    const div = $("#pane-divider");
    const saved = parseFloat(load("lloyd-panel-width"));
    if (saved && saved >= 28 && saved <= 80) { layoutEl.style.setProperty("--panel-width", saved + "%"); div.setAttribute("aria-valuenow", Math.round(saved)); }
    let dragging = false;
    const setW = (pct) => {
      pct = Math.min(80, Math.max(28, pct));
      layoutEl.style.setProperty("--panel-width", pct + "%");
      div.setAttribute("aria-valuenow", Math.round(pct));
      store("lloyd-panel-width", pct.toFixed(1));
    };
    div.addEventListener("pointerdown", (e) => { dragging = true; div.classList.add("is-dragging"); div.setPointerCapture(e.pointerId); });
    div.addEventListener("pointermove", (e) => {
      if (!dragging) return;
      const r = layoutEl.getBoundingClientRect();
      setW(((r.right - e.clientX) / r.width) * 100);
    });
    const stop = () => { if (dragging) { dragging = false; div.classList.remove("is-dragging"); fitView(false); } };
    div.addEventListener("pointerup", stop); div.addEventListener("pointercancel", stop);
    div.addEventListener("dblclick", () => { setW(46); fitView(false); });
    div.addEventListener("keydown", (e) => {
      const cur = parseFloat(getComputedStyle(layoutEl).getPropertyValue("--panel-width")) || 46;
      if (e.key === "ArrowLeft") { setW(cur + 2); fitView(false); } else if (e.key === "ArrowRight") { setW(cur - 2); fitView(false); }
    });
  })();

  // legend
  (function legend() {
    const seen = new Set();
    const items = [];
    for (const k of Object.keys(D.kinds)) {
      const g = D.kinds[k].group; if (seen.has(g) || g === "section") continue; seen.add(g);
      items.push(`<span class="graph-legend__item"><i class="legend-swatch" style="--sw-bg:var(--k-${g}-bg);--sw-border:var(--k-${g})"></i>${esc(D.kinds[k].legend)}</span>`);
    }
    items.push(`<span class="graph-legend__item"><i class="legend-swatch" style="--sw-bg:var(--lean);--sw-border:var(--lean);border-radius:50%"></i>Lean ✓</span>`);
    items.push(`<span class="graph-legend__key">A → B: A is used in B</span>`);
    $("#graph-legend").innerHTML = items.join("");
  })();

  // ------------------------------------------------------------------ search
  (function search() {
    const input = $("#search-input"), results = $("#search-results");
    const index = [];
    D.order.forEach((id) => {
      const n = N[id];
      index.push({ kind: (D.kinds[n.kind] || {}).label || n.kind, num: shortNumber(id), title: n.title, text: `${n.number || ""} ${n.title} ${id} ${n.label || ""} ${(n.labels || []).join(" ")} ${n.where || ""}`.toLowerCase(), href: "#" + id, group: groupOf(id) });
    });
    Object.keys(D.labels).forEach((lab) => {
      const L = D.labels[lab];
      if (L.type === "equation") { const node = (L.nodes && L.nodes[0]) || L.node; if (node) index.push({ kind: "Equation", num: `(${L.num})`, title: `in ${numberOf(node)} — ${N[node].title}`, text: `(${L.num}) ${lab} eq ${L.num}`.toLowerCase(), href: "#eq/" + lab, group: "definition" }); }
    });
    D.bibliography.forEach((b) => index.push({ kind: "Reference", num: `[${b.num}]`, title: b.text.slice(0, 110), text: `[${b.num}] ${b.text} ${b.key}`.toLowerCase(), href: "#bib/" + b.key, group: "external" }));
    index.push({ kind: "Page", num: "", title: "Notation", text: "notation symbols", href: "#notation", group: "section" });
    index.push({ kind: "Page", num: "", title: "References", text: "references bibliography", href: "#bib", group: "section" });
    let active = -1, current = [];
    function run() {
      const q = input.value.trim().toLowerCase();
      if (!q) { results.hidden = true; return; }
      const words = q.split(/\s+/);
      current = index.map((it) => {
        let score = 0;
        for (const w of words) { if (!it.text.includes(w)) return null; score += it.num.toLowerCase().startsWith(w) ? 5 : it.title.toLowerCase().includes(w) ? 3 : 1; }
        if (it.num.toLowerCase() === q || it.title.toLowerCase() === q) score += 10;
        return { it, score };
      }).filter(Boolean).sort((a, b) => b.score - a.score).slice(0, 14).map((r) => r.it);
      active = -1;
      results.innerHTML = current.length ? current.map((it, i) => `<button type="button" class="search-result" role="option" data-i="${i}"><span class="search-result__num">${esc(it.num)}</span><span class="search-result__title">${hl(it.title, words)}</span><span class="search-result__kind">${esc(it.kind)}</span></button>`).join("") : `<div class="search-results__empty">Nothing matches “${esc(input.value.trim())}”.</div>`;
      results.hidden = false;
    }
    function hl(text, words) { let out = esc(text); for (const w of words) { if (w.length < 2) continue; out = out.replace(new RegExp("(" + w.replace(/[.*+?^${}()|[\]\\]/g, "\\$&") + ")", "ig"), "<mark>$1</mark>"); } return out; }
    function go(i) { const it = current[i]; if (!it) return; results.hidden = true; input.value = ""; input.blur(); if (location.hash === it.href) { lastHash = null; route(); } else location.hash = it.href; }
    input.addEventListener("input", run);
    input.addEventListener("focus", run);
    input.addEventListener("keydown", (e) => {
      if (e.key === "ArrowDown" || e.key === "ArrowUp") {
        e.preventDefault(); if (!current.length) return;
        active = (active + (e.key === "ArrowDown" ? 1 : -1) + current.length) % current.length;
        $$(".search-result", results).forEach((b, i) => b.classList.toggle("is-active", i === active));
      } else if (e.key === "Enter") { e.preventDefault(); go(active >= 0 ? active : 0); }
      else if (e.key === "Escape") { results.hidden = true; input.blur(); }
    });
    results.addEventListener("click", (e) => { const b = e.target.closest(".search-result"); if (b) go(+b.dataset.i); });
    document.addEventListener("click", (e) => { if (!e.target.closest(".topbar__search")) results.hidden = true; });
  })();

  // ------------------------------------------------------------------ keyboard
  document.addEventListener("keydown", (e) => {
    const typing = /^(INPUT|TEXTAREA|SELECT)$/.test(document.activeElement.tagName) || document.activeElement.isContentEditable;
    if (e.key === "/" && !typing) { e.preventDefault(); $("#search-input").focus(); return; }
    if (typing || e.metaKey || e.ctrlKey || e.altKey) return;
    if (e.key === "g") toggleGraph();
    else if (e.key === "f") toggleExpand();
    else if (e.key === "t") toggleTheme();
    else if (e.key === "+" || e.key === "=") zoomCenter(1.25);
    else if (e.key === "-") zoomCenter(0.8);
    else if (e.key === "0") fitView(true);
    else if (e.key === "Escape") {
      if ($("#lightbox").open) $("#lightbox").close();
      else if (layoutEl.classList.contains("layout--expanded")) toggleExpand();
      else if (state.graphMode === "focus") { state.graphMode = "map"; renderGraph(); }
    }
  });

  // ------------------------------------------------------------------ boot
  if (META.pdfUrl) { const a = $("#pdf-link"); a.href = META.pdfUrl; a.hidden = false; }
  if (load("lloyd-graph-hidden") === "1" && !window.matchMedia("(max-width: 900px)").matches) toggleGraph(true);
  if (window.matchMedia("(max-width: 900px)").matches) setPane("panel"); else { $("#graph-pane").classList.add("is-active"); $("#panel").classList.add("is-active"); }
  route();
})();
