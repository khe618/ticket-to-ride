/** ---------- Seeded RNG (xmur3 + sfc32) ---------- **/
function xmur3(str) {
  let h = 1779033703 ^ str.length;
  for (let i = 0; i < str.length; i++) {
    h = Math.imul(h ^ str.charCodeAt(i), 3432918353);
    h = (h << 13) | (h >>> 19);
  }
  return function() {
    h = Math.imul(h ^ (h >>> 16), 2246822507);
    h = Math.imul(h ^ (h >>> 13), 3266489909);
    h ^= h >>> 16;
    return h >>> 0;
  };
}
function sfc32(a, b, c, d) {
  return function() {
    a >>>= 0; b >>>= 0; c >>>= 0; d >>>= 0;
    let t = (a + b) | 0;
    a = b ^ (b >>> 9);
    b = (c + (c << 3)) | 0;
    c = (c << 21) | (c >>> 11);
    d = (d + 1) | 0;
    t = (t + d) | 0;
    c = (c + t) | 0;
    return (t >>> 0) / 4294967296;
  }
}
function makeRng(seedStr) {
  const seed = xmur3(seedStr);
  return sfc32(seed(), seed(), seed(), seed());
}
function randInt(rng, lo, hi) { // inclusive
  return lo + Math.floor(rng() * (hi - lo + 1));
}
function shuffleInPlace(rng, arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(rng() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}

/** ---------- Geometry helpers ---------- **/
function dist(a, b) {
  const dx = a.x - b.x, dy = a.y - b.y;
  return Math.hypot(dx, dy);
}
function clamp(x, lo, hi) { return Math.max(lo, Math.min(hi, x)); }
function lerp(a, b, t) { return a + (b - a) * t; }

function segIntersects(p1, p2, q1, q2) {
  // Proper segment intersection excluding shared endpoints
  function orient(a, b, c) {
    return (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x);
  }
  function onSegment(a, b, c) {
    return Math.min(a.x, b.x) <= c.x + 1e-9 && c.x <= Math.max(a.x, b.x) + 1e-9 &&
           Math.min(a.y, b.y) <= c.y + 1e-9 && c.y <= Math.max(a.y, b.y) + 1e-9;
  }
  const o1 = orient(p1, p2, q1);
  const o2 = orient(p1, p2, q2);
  const o3 = orient(q1, q2, p1);
  const o4 = orient(q1, q2, p2);

  const shared =
    (p1.id === q1.id) || (p1.id === q2.id) || (p2.id === q1.id) || (p2.id === q2.id);
  if (shared) return false;

  // General case
  if ((o1 > 0) !== (o2 > 0) && (o3 > 0) !== (o4 > 0)) return true;

  // Collinear cases
  if (Math.abs(o1) < 1e-9 && onSegment(p1, p2, q1)) return true;
  if (Math.abs(o2) < 1e-9 && onSegment(p1, p2, q2)) return true;
  if (Math.abs(o3) < 1e-9 && onSegment(q1, q2, p1)) return true;
  if (Math.abs(o4) < 1e-9 && onSegment(q1, q2, p2)) return true;

  return false;
}

/** ---------- Graph utilities ---------- **/
function keyEdge(a, b) { return a < b ? `${a}-${b}` : `${b}-${a}`; }

class DSU {
  constructor(n) { this.p = Array.from({length:n}, (_,i)=>i); this.r = Array(n).fill(0); }
  find(x){ while(this.p[x]!==x){ this.p[x]=this.p[this.p[x]]; x=this.p[x]; } return x; }
  union(a,b){
    a=this.find(a); b=this.find(b);
    if(a===b) return false;
    if(this.r[a]<this.r[b]) [a,b]=[b,a];
    this.p[b]=a;
    if(this.r[a]===this.r[b]) this.r[a]++;
    return true;
  }
}

/** ---------- Map generation ---------- **/
function generateCities(rng, N) {
  // 4 regions with gaussian sampling + min distance rejection.
  const regions = 4;
  const centers = [];
  const minCenterDist = 0.35;

  function randNorm() {
    // Box-Muller
    let u = 0, v = 0;
    while (u === 0) u = rng();
    while (v === 0) v = rng();
    return Math.sqrt(-2.0 * Math.log(u)) * Math.cos(2.0 * Math.PI * v);
  }

  // Place region centers
  while (centers.length < regions) {
    const c = { x: 0.15 + 0.7 * rng(), y: 0.15 + 0.7 * rng() };
    if (centers.every(o => dist(c, o) >= minCenterDist)) centers.push(c);
  }

  // Allocate cities per region
  const base = Math.floor(N / regions);
  const counts = Array(regions).fill(base);
  for (let i = 0; i < (N - base*regions); i++) counts[i]++;

  const cities = [];
  const minDist = 0.06; // tune for spacing

  // helper to attempt add point with minDist
  function tryAdd(x, y) {
    const p = { x, y };
    if (x < 0.05 || x > 0.95 || y < 0.05 || y > 0.95) return false;
    for (const q of cities) if (dist(p, q) < minDist) return false;
    p.id = cities.length;
    p.name = `City ${p.id+1}`;
    cities.push(p);
    return true;
  }

  // Add clustered points
  for (let r = 0; r < regions; r++) {
    const c = centers[r];
    const sigma = 0.10; // cluster tightness
    let added = 0;
    let tries = 0;
    while (added < counts[r] && tries < 20000) {
      tries++;
      const x = c.x + sigma * randNorm();
      const y = c.y + sigma * randNorm();
      if (tryAdd(x, y)) added++;
    }
  }

  // If we somehow undershoot, fill uniformly
  let guard = 0;
  while (cities.length < N && guard++ < 20000) {
    const x = 0.05 + 0.90 * rng();
    const y = 0.05 + 0.90 * rng();
    tryAdd(x, y);
  }

  // Light relaxation to reduce near-overlaps (Lloyd-ish)
  for (let it = 0; it < 10; it++) {
    for (const a of cities) {
      let fx = 0, fy = 0;
      for (const b of cities) {
        if (a === b) continue;
        const d = dist(a, b);
        if (d < 1e-6) continue;
        const push = d < (minDist*1.05) ? (minDist*1.05 - d) : 0;
        if (push > 0) {
          fx += (a.x - b.x) / d * push * 0.15;
          fy += (a.y - b.y) / d * push * 0.15;
        }
      }
      a.x = clamp(a.x + fx, 0.05, 0.95);
      a.y = clamp(a.y + fy, 0.05, 0.95);
    }
  }

  return cities;
}

function buildCandidateEdges(cities, k) {
  // kNN candidates, undirected, de-duplicated
  const N = cities.length;
  const edges = [];
  const seen = new Set();

  for (let i = 0; i < N; i++) {
    const dists = [];
    for (let j = 0; j < N; j++) {
      if (i === j) continue;
      dists.push({ j, d: dist(cities[i], cities[j]) });
    }
    dists.sort((a,b)=>a.d-b.d);
    for (let t = 0; t < Math.min(k, dists.length); t++) {
      const j = dists[t].j;
      const key = keyEdge(i, j);
      if (seen.has(key)) continue;
      seen.add(key);
      edges.push({ u: i, v: j, d: dists[t].d });
    }
  }
  return edges;
}

function computeMST(cities, candidates) {
  // Kruskal on candidates (must be sufficiently connected; kNN generally is)
  const edges = [...candidates].sort((a,b)=>a.d-b.d);
  const dsu = new DSU(cities.length);
  const mst = [];
  for (const e of edges) {
    if (dsu.union(e.u, e.v)) mst.push(e);
    if (mst.length === cities.length - 1) break;
  }
  return mst;
}

function addEdgesNoCrossing(rng, cities, mstEdges, candidates, eTarget, maxDeg) {
  const selected = [];
  const selectedSet = new Set();
  const deg = Array(cities.length).fill(0);

  function canAdd(e) {
    if (selectedSet.has(keyEdge(e.u, e.v))) return false;
    if (deg[e.u] >= maxDeg || deg[e.v] >= maxDeg) return false;

    const p1 = cities[e.u], p2 = cities[e.v];
    for (const s of selected) {
      const q1 = cities[s.u], q2 = cities[s.v];
      if (segIntersects(p1, p2, q1, q2)) return false;
    }
    return true;
  }

  // Add MST first (may include a rare crossing if candidates cross; but kNN + clusters usually ok)
  for (const e of mstEdges) {
    if (canAdd(e)) {
      selected.push(e);
      selectedSet.add(keyEdge(e.u, e.v));
      deg[e.u]++; deg[e.v]++;
    }
  }

  // We want cycles/alternates: prioritize edges that connect already-connected areas (in MST sense)
  // We'll do a cheap cycle-bonus: edges whose endpoints are already connected via DSU of selected.
  const dsu = new DSU(cities.length);
  for (const e of selected) dsu.union(e.u, e.v);

  const pool = [...candidates].filter(e => !selectedSet.has(keyEdge(e.u, e.v)));
  // Shuffle for randomness, then sort by a heuristic score
  shuffleInPlace(rng, pool);

  function scoreEdge(e) {
    const cycle = (dsu.find(e.u) === dsu.find(e.v)) ? 1 : 0;
    const lenPref = -Math.abs(e.d - 0.18); // prefer moderate-local edges early
    const degPref = -(deg[e.u] + deg[e.v]) * 0.08;
    return cycle * 2.0 + lenPref + degPref + (rng() * 0.05);
  }

  // Iteratively pick best-scoring among a random window (keeps variety)
  while (selected.length < eTarget && pool.length > 0) {
    // Consider a window of candidates and choose best
    const windowSize = Math.min(40, pool.length);
    let bestIdx = -1, bestScore = -1e9;
    for (let i = 0; i < windowSize; i++) {
      const e = pool[i];
      if (!canAdd(e)) continue;
      const sc = scoreEdge(e);
      if (sc > bestScore) { bestScore = sc; bestIdx = i; }
    }
    if (bestIdx === -1) {
      // No addable edge in window; drop some edges and keep trying
      pool.splice(0, windowSize);
      continue;
    }
    const e = pool.splice(bestIdx, 1)[0];
    if (!canAdd(e)) continue;

    selected.push(e);
    selectedSet.add(keyEdge(e.u, e.v));
    deg[e.u]++; deg[e.v]++;
    dsu.union(e.u, e.v);
  }

  return { edges: selected, deg };
}

function percentile(arr, p) {
  if (arr.length === 0) return 0;
  const a = [...arr].sort((x,y)=>x-y);
  const idx = (a.length - 1) * p;
  const lo = Math.floor(idx), hi = Math.ceil(idx);
  if (lo === hi) return a[lo];
  const t = idx - lo;
  return lerp(a[lo], a[hi], t);
}

function assignLengths(edges) {
  const ds = edges.map(e => e.d);
  const d10 = percentile(ds, 0.10);
  const d90 = percentile(ds, 0.90);
  const denom = (d90 - d10) || 1e-6;

  for (const e of edges) {
    const t = clamp((e.d - d10) / denom, 0, 1);
    const len = 1 + Math.round(5 * t); // 1..6
    e.len = clamp(len, 1, 6);
  }
}

const ROUTE_COLORS = [
  { name: "red",    hex: "#e74c3c" },
  { name: "blue",   hex: "#3498db" },
  { name: "green",  hex: "#2ecc71" },
  { name: "yellow", hex: "#f1c40f" },
  { name: "black",  hex: "#2d3436" },
  { name: "white",  hex: "#ecf0f1" },
  { name: "orange", hex: "#e67e22" },
  { name: "purple", hex: "#9b59b6" },
];
const GRAY = { name: "gray", hex: "#95a5a6" };

function assignColors(rng, edges, pGray) {
  // Balance by total length-load per color.
  const load = new Map();
  for (const c of ROUTE_COLORS) load.set(c.name, 0);

  // Sort longest first so balancing matters
  const sorted = [...edges].sort((a,b)=>b.len-a.len);

  for (const e of sorted) {
    if (rng() < pGray) {
      e.color = GRAY;
      continue;
    }
    // choose among 3 lowest-load colors at random
    const ranked = [...ROUTE_COLORS].sort((a,b)=>load.get(a.name)-load.get(b.name));
    const top = ranked.slice(0, 3);
    const pick = top[Math.floor(rng() * top.length)];
    e.color = pick;
    load.set(pick.name, load.get(pick.name) + e.len);
  }
}

function generateMap(seedStr, params) {
  const rng = makeRng(seedStr);
  const N = params.nCities;
  const k = params.kNN;
  const eTarget = params.eTarget;
  const maxDeg = params.maxDeg;
  const pGray = params.pGray;

  const cities = generateCities(rng, N);
  const candidates = buildCandidateEdges(cities, k);

  const mst = computeMST(cities, candidates);
  // If MST failed (rare), increase k or regenerate; for simplicity we'll just try once more with higher k
  if (mst.length < N - 1) {
    const candidates2 = buildCandidateEdges(cities, Math.min(8, k + 2));
    const mst2 = computeMST(cities, candidates2);
    if (mst2.length < N - 1) throw new Error("Failed to build connected MST; try increasing kNN.");
    const res2 = addEdgesNoCrossing(rng, cities, mst2, candidates2, eTarget, maxDeg);
    assignLengths(res2.edges);
    assignColors(rng, res2.edges, pGray);
    return { cities, edges: res2.edges, deg: res2.deg };
  }

  const res = addEdgesNoCrossing(rng, cities, mst, candidates, eTarget, maxDeg);
  assignLengths(res.edges);
  assignColors(rng, res.edges, pGray);
  return { cities, edges: res.edges, deg: res.deg };
}

/** ---------- Rendering ---------- **/
function drawMap(ctx, canvas, map, opts) {
  const { cities, edges } = map;

  // Fit to canvas with padding
  const pad = 60;
  const w = canvas.width, h = canvas.height;

  // Compute bbox in [0,1]
  let minX=Infinity, minY=Infinity, maxX=-Infinity, maxY=-Infinity;
  for (const c of cities) {
    minX = Math.min(minX, c.x); minY = Math.min(minY, c.y);
    maxX = Math.max(maxX, c.x); maxY = Math.max(maxY, c.y);
  }
  const bx = maxX - minX || 1;
  const by = maxY - minY || 1;

  function toScreen(p) {
    const sx = pad + ( (p.x - minX) / bx ) * (w - 2*pad);
    const sy = pad + ( (p.y - minY) / by ) * (h - 2*pad);
    return { x: sx, y: sy };
  }

  ctx.clearRect(0,0,w,h);

  // subtle grid
  ctx.save();
  ctx.globalAlpha = 0.08;
  ctx.strokeStyle = "#8aa0d6";
  for (let x=pad; x<w-pad; x+=80){ ctx.beginPath(); ctx.moveTo(x,pad); ctx.lineTo(x,h-pad); ctx.stroke(); }
  for (let y=pad; y<h-pad; y+=80){ ctx.beginPath(); ctx.moveTo(pad,y); ctx.lineTo(w-pad,y); ctx.stroke(); }
  ctx.restore();

  // Draw edges (routes)
  // Thickness scales a bit with route length; draw a darker under-stroke for contrast
  for (const e of edges) {
    const a = toScreen(cities[e.u]);
    const b = toScreen(cities[e.v]);

    // curve slightly to reduce overlap (deterministic from endpoints)
    const mx = (a.x + b.x) / 2;
    const my = (a.y + b.y) / 2;
    const dx = b.x - a.x, dy = b.y - a.y;
    const L = Math.hypot(dx, dy) || 1;
    const nx = -dy / L, ny = dx / L;
    const curve = ((e.u + 1) * 73856093 ^ (e.v + 1) * 19349663) % 2;
    const sign = curve === 0 ? -1 : 1;
    const mag = 8 + e.len * 1.5;
    const cx = mx + nx * mag * sign;
    const cy = my + ny * mag * sign;

    const width = 2.5 + e.len * 0.9;

    // under-stroke
    ctx.beginPath();
    ctx.moveTo(a.x, a.y);
    ctx.quadraticCurveTo(cx, cy, b.x, b.y);
    ctx.strokeStyle = "rgba(0,0,0,0.55)";
    ctx.lineWidth = width + 3;
    ctx.lineCap = "round";
    ctx.stroke();

    // color stroke
    ctx.beginPath();
    ctx.moveTo(a.x, a.y);
    ctx.quadraticCurveTo(cx, cy, b.x, b.y);
    ctx.strokeStyle = e.color.hex;
    ctx.lineWidth = width;
    ctx.lineCap = "round";
    ctx.stroke();

    // draw little "train segments" dots along the route (1-6)
    ctx.save();
    ctx.fillStyle = "rgba(255,255,255,0.85)";
    const steps = e.len;
    for (let i = 1; i <= steps; i++) {
      const t = i / (steps + 1);
      // quadratic bezier point
      const x = (1-t)*(1-t)*a.x + 2*(1-t)*t*cx + t*t*b.x;
      const y = (1-t)*(1-t)*a.y + 2*(1-t)*t*cy + t*t*b.y;
      ctx.beginPath();
      ctx.arc(x, y, 2.0, 0, Math.PI*2);
      ctx.fill();
    }
    ctx.restore();
  }

  // Draw cities
  for (const c of cities) {
    const p = toScreen(c);
    // glow
    ctx.save();
    ctx.beginPath();
    ctx.arc(p.x, p.y, 10, 0, Math.PI*2);
    ctx.fillStyle = "rgba(110,160,255,0.12)";
    ctx.fill();
    ctx.restore();

    // node
    ctx.beginPath();
    ctx.arc(p.x, p.y, 6.5, 0, Math.PI*2);
    ctx.fillStyle = "#e7eaf0";
    ctx.fill();
    ctx.lineWidth = 2;
    ctx.strokeStyle = "#0b0d12";
    ctx.stroke();

    if (opts.labels) {
      ctx.font = "12px system-ui, -apple-system, Segoe UI, Roboto, sans-serif";
      ctx.fillStyle = "rgba(231,234,240,0.85)";
      ctx.textAlign = "left";
      ctx.textBaseline = "middle";
      ctx.fillText(c.name, p.x + 10, p.y - 10);
    }
  }
}

/** ---------- Stats / validation-ish ---------- **/
function mapStats(map) {
  const N = map.cities.length;
  const E = map.edges.length;
  const deg = map.deg;
  const avgDeg = deg.reduce((a,b)=>a+b,0)/N;
  const minDeg = Math.min(...deg);
  const maxDeg = Math.max(...deg);

  const lenCount = Array(7).fill(0);
  let gray = 0;
  const colorCount = new Map();

  for (const e of map.edges) {
    lenCount[e.len]++;
    if (e.color.name === "gray") gray++;
    colorCount.set(e.color.name, (colorCount.get(e.color.name)||0) + 1);
  }

  const lines = [];
  lines.push(`Cities: ${N}`);
  lines.push(`Routes: ${E}`);
  lines.push(`Avg degree: ${avgDeg.toFixed(2)} (min ${minDeg}, max ${maxDeg})`);
  lines.push(`Lengths 1..6: ` + [1,2,3,4,5,6].map(L=>`${L}:${lenCount[L]}`).join("  "));
  lines.push(`Gray routes: ${gray} (${Math.round(100*gray/E)}%)`);
  lines.push(`Colors (count):`);
  const keys = [...colorCount.keys()].sort((a,b)=>a.localeCompare(b));
  for (const k of keys) lines.push(`  ${k}: ${colorCount.get(k)}`);
  return lines.join("\n");
}

/** ---------- App wiring ---------- **/
const canvas = document.getElementById("c");
const ctx = canvas.getContext("2d");
const statsEl = document.getElementById("stats");

function resize() {
  const rect = canvas.getBoundingClientRect();
  const dpr = window.devicePixelRatio || 1;
  canvas.width = Math.floor(rect.width * dpr);
  canvas.height = Math.floor(rect.height * dpr);
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0); // draw in CSS pixels
  render();
}
window.addEventListener("resize", resize);

let currentMap = null;

function getParams() {
  return {
    nCities: parseInt(document.getElementById("nCities").value, 10),
    eTarget: parseInt(document.getElementById("eTarget").value, 10),
    kNN: parseInt(document.getElementById("kNN").value, 10),
    maxDeg: parseInt(document.getElementById("maxDeg").value, 10),
    pGray: parseFloat(document.getElementById("pGray").value),
    labels: document.getElementById("labels").checked,
  };
}

function render() {
  if (!currentMap) return;
  const opts = getParams();
  drawMap(ctx, canvas, currentMap, { labels: opts.labels });
  statsEl.textContent = mapStats(currentMap);
}

function regenerate() {
  const seedStr = document.getElementById("seed").value.trim() || "seed";
  const params = getParams();

  try {
    currentMap = generateMap(seedStr, params);
    render();
  } catch (err) {
    statsEl.textContent = `Error: ${err.message}`;
    ctx.clearRect(0,0,canvas.width,canvas.height);
  }
}

document.getElementById("regen").addEventListener("click", regenerate);
document.getElementById("newSeed").addEventListener("click", () => {
  const s = `seed-${Math.floor(Math.random()*1e9)}-${Date.now()}`;
  document.getElementById("seed").value = s;
  regenerate();
});

for (const id of ["seed","nCities","eTarget","kNN","maxDeg","pGray","labels"]) {
  document.getElementById(id).addEventListener("change", regenerate);
}

resize();
regenerate();
