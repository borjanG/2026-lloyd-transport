#!/usr/bin/env node
// Renders every formula in site/data.js with the vendored KaTeX and reports
// parse errors, plus dangling cross-reference targets.  Run from the repo root:
//
//     node site/tools/check-math.mjs
//
import { createRequire } from "node:module";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import path from "node:path";

const here = path.dirname(fileURLToPath(import.meta.url));
const site = path.resolve(here, "..");
const require = createRequire(import.meta.url);
const katex = require(path.join(site, "vendor", "katex", "katex.min.js"));

const src = readFileSync(path.join(site, "data.js"), "utf8");
const json = src.slice(src.indexOf("window.PAPER = ") + "window.PAPER = ".length).trim().replace(/;$/, "");
const data = JSON.parse(json);

// The macro list must match site/app.js.
const macros = {
  "\\R": "\\mathbb{R}", "\\N": "\\mathbb{N}", "\\diff": "\\mathrm{d}", "\\dist": "\\operatorname{dist}",
  "\\supp": "\\operatorname{supp}", "\\le": "\\leqslant", "\\leq": "\\leqslant", "\\ge": "\\geqslant",
  "\\geq": "\\geqslant", "\\mbox": "\\text",
};

const unescape = (s) => s.replace(/&quot;/g, '"').replace(/&#x27;/g, "'").replace(/&lt;/g, "<").replace(/&gt;/g, ">").replace(/&amp;/g, "&");

let formulas = 0, errors = 0;
const seen = new Set();
function checkHtml(where, html) {
  if (typeof html !== "string") return;
  const re = /<(span|div) class="math(?:-display)?"[^>]*data-tex="([^"]*)"/g;
  let m;
  while ((m = re.exec(html))) {
    const display = m[1] === "div";
    const tex = unescape(m[2]);
    formulas++;
    try {
      katex.renderToString(tex, { displayMode: display, macros, throwOnError: true, strict: "ignore", trust: false });
    } catch (e) {
      errors++;
      const key = where + tex.slice(0, 40);
      if (!seen.has(key)) {
        seen.add(key);
        console.log(`ERROR in ${where}: ${e.message}\n    ${tex.slice(0, 200)}`);
      }
    }
  }
}
function walk(obj, where) {
  if (typeof obj === "string") return checkHtml(where, obj);
  if (Array.isArray(obj)) return obj.forEach((v, i) => walk(v, where + "[" + i + "]"));
  if (obj && typeof obj === "object") for (const k of Object.keys(obj)) walk(obj[k], where + "." + k);
}
walk(data.nodes, "nodes");
walk(data.meta, "meta");
walk(data.bibliography, "bibliography");
for (const n of data.notation) {
  formulas++;
  try { katex.renderToString(n.sym, { macros, throwOnError: true, strict: "ignore" }); }
  catch (e) { errors++; console.log(`ERROR in notation ${n.sym}: ${e.message}`); }
  checkHtml("notation", n.textHtml);
}

// cross references (run over the raw HTML strings)
let badRefs = 0, refCount = 0;
const ids = new Set(Object.keys(data.nodes));
const labels = data.labels;
const bib = new Set(data.bibliography.map((b) => b.key));
const hrefRe = /href="#([^"]*)"/g;
const htmlStrings = [];
(function collect(obj) {
  if (typeof obj === "string") { if (obj.includes("href=")) htmlStrings.push(obj); return; }
  if (Array.isArray(obj)) return obj.forEach(collect);
  if (obj && typeof obj === "object") for (const k of Object.keys(obj)) collect(obj[k]);
})([data.nodes, data.meta, data.notation]);
for (const html of htmlStrings) {
  let m;
  while ((m = hrefRe.exec(html))) {
    const h = m[1]; refCount++;
    if (h.startsWith("eq/") || h.startsWith("fig/")) { const lab = h.slice(h.indexOf("/") + 1); if (!labels[lab]) { badRefs++; console.log("dangling label ref", h); } }
    else if (h.startsWith("bib/")) { if (!bib.has(h.slice(4))) { badRefs++; console.log("dangling citation", h); } }
    else if (h === "bib" || h === "notation" || h === "") continue;
    else if (!ids.has(h.split("/")[0])) { badRefs++; console.log("dangling node ref", h); }
  }
}
console.log(`${formulas} formulas checked, ${errors} KaTeX errors; ${refCount} internal links checked, ${badRefs} dangling`);
process.exit(errors || badRefs ? 1 : 0);
