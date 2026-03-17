import { readFileSync, existsSync, mkdirSync, createWriteStream } from "fs";
import { join, dirname } from "path";
import { fileURLToPath } from "url";
import { JSDOM } from "jsdom";
import * as d3 from "d3";
import PDFDocument from "pdfkit";
import SVGtoPDF from "svg-to-pdfkit";

const base = dirname(fileURLToPath(import.meta.url));
const mode = process.argv[2] === "--structured" ? "structured" : "random";

function loadTimes(file) {
  const dataPath = join(base, "data", file);
  const prerecPath = join(base, "prerecorded", file);
  const path = existsSync(dataPath) ? dataPath : prerecPath;
  return JSON.parse(readFileSync(path, "utf8"));
}

const series =
  mode === "random"
    ? [
        { name: "EREQ", color: "#2166ac", dash: "", marker: "circle", times: loadTimes("all_automatark_ereq.json") },
        { name: "MONA", color: "#b2182b", dash: "6,3", marker: "triangle", times: loadTimes("all_automatark_mona.json") },
      ]
    : [
        { name: "EREQ", color: "#2166ac", dash: "", marker: "circle", times: loadTimes("structured_ereq.json") },
        { name: "MONA", color: "#b2182b", dash: "6,3", marker: "triangle", times: loadTimes("structured_mona.json") },
      ];

const totalInstances = mode === "structured" ? 50 : undefined;
for (const s of series) console.log(`${s.name}: ${s.times.length} solved`);

// --- build SVG ---
const margin = { top: 20, right: 20, bottom: 50, left: 65 };
const width = 460;
const height = 256;
const innerW = width - margin.left - margin.right;
const innerH = height - margin.top - margin.bottom;

const dom = new JSDOM("<!DOCTYPE html><html><body></body></html>");
const body = d3.select(dom.window.document.body);

const svg = body
  .append("svg")
  .attr("xmlns", "http://www.w3.org/2000/svg")
  .attr("width", width)
  .attr("height", height)
  .attr("viewBox", `0 0 ${width} ${height}`);

svg.append("rect").attr("width", width).attr("height", height).attr("fill", "white");

const g = svg.append("g").attr("transform", `translate(${margin.left},${margin.top})`);

const nonEmpty = series.filter((s) => s.times.length > 0);
const maxN = totalInstances ?? Math.max(...nonEmpty.map((s) => s.times.length));
const maxT = Math.max(...nonEmpty.map((s) => s.times[s.times.length - 1]));
const minT = Math.min(...nonEmpty.map((s) => s.times[0]));

const x = d3.scaleLinear().domain([0, maxN]).range([0, innerW]);
const y = d3.scaleLog().domain([minT * 0.8, maxT * 1.2]).range([innerH, 0]);

// grid
g.append("g")
  .selectAll("line")
  .data(y.ticks(6))
  .join("line")
  .attr("x1", 0)
  .attr("x2", innerW)
  .attr("y1", (d) => y(d))
  .attr("y2", (d) => y(d))
  .attr("stroke", "#e0e0e0")
  .attr("stroke-width", 0.5);

const font = "Helvetica, Arial, sans-serif";

// x-axis
g.append("line").attr("x1", 0).attr("x2", innerW).attr("y1", innerH).attr("y2", innerH).attr("stroke", "black");

for (const v of x.ticks(8)) {
  g.append("line").attr("x1", x(v)).attr("x2", x(v)).attr("y1", innerH).attr("y2", innerH + 6).attr("stroke", "black");
  g.append("text").attr("x", x(v)).attr("y", innerH + 18).attr("text-anchor", "middle").attr("font-size", "10px").attr("font-family", font).text(v);
}

// y-axis
g.append("line").attr("x1", 0).attr("x2", 0).attr("y1", 0).attr("y2", innerH).attr("stroke", "black");

const yTicks = [0.001, 0.01, 0.1, 1, 10, 60];
for (const v of yTicks) {
  if (v < y.domain()[0] || v > y.domain()[1]) continue;
  g.append("line").attr("x1", -6).attr("x2", 0).attr("y1", y(v)).attr("y2", y(v)).attr("stroke", "black");
  g.append("text").attr("x", -10).attr("y", y(v) + 3.5).attr("text-anchor", "end").attr("font-size", "10px").attr("font-family", font).text(v >= 1 ? v : v.toString());
}

// axis labels
g.append("text").attr("x", innerW / 2).attr("y", innerH + 40).attr("text-anchor", "middle").attr("font-size", "12px").attr("font-family", font).text("instances solved");
g.append("text").attr("transform", "rotate(-90)").attr("x", -innerH / 2).attr("y", -50).attr("text-anchor", "middle").attr("font-size", "12px").attr("font-family", font).text("time (s)");

// lines + markers
const line = d3
  .line()
  .x((_d, i) => x(i + 1))
  .y((d) => y(d));

for (const s of series) {
  g.append("path").datum(s.times).attr("fill", "none").attr("stroke", s.color).attr("stroke-width", 1.8).attr("stroke-dasharray", s.dash).attr("d", line);

  const step = Math.max(1, Math.floor(s.times.length / 15));
  const ptsIdx = s.times.map((_, i) => i).filter((i) => i % step === 0 || i === s.times.length - 1);
  for (const i of ptsIdx) {
    const cx = x(i + 1),
      cy = y(s.times[i]);
    if (s.marker === "circle") {
      g.append("circle").attr("cx", cx).attr("cy", cy).attr("r", 3).attr("fill", "white").attr("stroke", s.color).attr("stroke-width", 1.2);
    } else {
      const r = 3.5;
      g.append("path")
        .attr("d", `M${cx},${cy - r}L${cx - r},${cy + r}L${cx + r},${cy + r}Z`)
        .attr("fill", "white")
        .attr("stroke", s.color)
        .attr("stroke-width", 1.2);
    }
  }
}

// legend
const legend = g.append("g").attr("transform", `translate(15, 10)`);
series.forEach((s, i) => {
  const row = legend.append("g").attr("transform", `translate(0, ${i * 18})`);
  row.append("line").attr("x1", 0).attr("x2", 18).attr("y1", 0).attr("y2", 0).attr("stroke", s.color).attr("stroke-width", 2).attr("stroke-dasharray", s.dash);
  if (s.marker === "circle") {
    row.append("circle").attr("cx", 9).attr("cy", 0).attr("r", 2.5).attr("fill", "white").attr("stroke", s.color).attr("stroke-width", 1);
  } else {
    const r = 3;
    row.append("path")
      .attr("d", `M9,${-r}L${9 - r},${r}L${9 + r},${r}Z`)
      .attr("fill", "white")
      .attr("stroke", s.color)
      .attr("stroke-width", 1);
  }
  row
    .append("text")
    .attr("x", 24)
    .attr("y", 4)
    .attr("font-size", "10px")
    .attr("font-family", font)
    .text(totalInstances ? `${s.name} (${s.times.length}/${totalInstances})` : `${s.name} (n = ${s.times.length})`);
});

// --- render to PDF ---
mkdirSync(join(base, "figs"), { recursive: true });
const outName = `figs/cactus-${mode}.pdf`;
const svgStr = body.select("svg").node().outerHTML;
const doc = new PDFDocument({ size: [width, height], margin: 0 });
const out = createWriteStream(join(base, outName));
doc.pipe(out);
SVGtoPDF(doc, svgStr, 0, 0, { width, height });
doc.end();
out.on("finish", () => console.log(`wrote ${outName}`));
