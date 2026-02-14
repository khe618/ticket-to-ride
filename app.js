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
function generateCities(rng, N, bounds) {
  // Poisson disk sampling for even spacing (no region clustering).
  const xMin = bounds.xMin;
  const xMax = bounds.xMax;
  const yMin = bounds.yMin;
  const yMax = bounds.yMax;
  const w = xMax - xMin;
  const h = yMax - yMin;

  const area = w * h;
  let minDist = 0.85 * Math.sqrt(area / N);
  minDist = clamp(minDist, 0.045 * Math.min(w, h), 0.12 * Math.min(w, h));

  function poissonSample(targetCount) {
    const cellSize = minDist / Math.SQRT2;
    const gridW = Math.ceil(w / cellSize);
    const gridH = Math.ceil(h / cellSize);
    const grid = Array.from({ length: gridW * gridH }, () => null);
    const active = [];
    const points = [];

    function gridIndex(x, y) {
      const gx = Math.floor((x - xMin) / cellSize);
      const gy = Math.floor((y - yMin) / cellSize);
      return { gx, gy, idx: gy * gridW + gx };
    }

    function inBounds(x, y) {
      return x >= xMin && x <= xMax && y >= yMin && y <= yMax;
    }

    function farEnough(x, y) {
      const gi = gridIndex(x, y);
      const gx0 = Math.max(0, gi.gx - 2);
      const gx1 = Math.min(gridW - 1, gi.gx + 2);
      const gy0 = Math.max(0, gi.gy - 2);
      const gy1 = Math.min(gridH - 1, gi.gy + 2);
      for (let gy = gy0; gy <= gy1; gy++) {
        for (let gx = gx0; gx <= gx1; gx++) {
          const p = grid[gy * gridW + gx];
          if (!p) continue;
          if (dist(p, { x, y }) < minDist) return false;
        }
      }
      return true;
    }

    // initial point
    const x0 = xMin + w * rng();
    const y0 = yMin + h * rng();
    const p0 = { x: x0, y: y0 };
    points.push(p0);
    active.push(p0);
    const g0 = gridIndex(x0, y0);
    grid[g0.idx] = p0;

    const k = 30;
    while (active.length && points.length < targetCount) {
      const idx = Math.floor(rng() * active.length);
      const p = active[idx];
      let found = false;
      for (let i = 0; i < k; i++) {
        const ang = rng() * Math.PI * 2;
        const rad = minDist * (1 + rng());
        const x = p.x + Math.cos(ang) * rad;
        const y = p.y + Math.sin(ang) * rad;
        if (!inBounds(x, y)) continue;
        if (!farEnough(x, y)) continue;
        const np = { x, y };
        points.push(np);
        active.push(np);
        const gi = gridIndex(x, y);
        grid[gi.idx] = np;
        found = true;
        if (points.length >= targetCount) break;
      }
      if (!found) active.splice(idx, 1);
    }
    return points;
  }

  let points = poissonSample(N);
  if (points.length < N) {
    minDist *= 0.9;
    points = poissonSample(N);
  }

  const CITY_NAMES = [
    "Valmere",
    "Stonehaven",
    "Alderon",
    "Westfall",
    "Brindle",
    "Norwick",
    "Calden",
    "Evermont",
    "Highmoor",
    "Driftmark",
    "Roswick",
    "Falken",
    "Lowen",
    "Crestfall",
    "Windor",
    "Belmere",
    "Thornby",
    "Greyhaven",
    "Ashen",
    "Marrow",
    "Halden",
    "Verdan",
    "Eastmere",
    "Skarn",
    "Brightonel",
    "Northam",
    "Elden",
    "Larkspur",
    "Holloway",
    "Dunmere",
    "Ravenel",
    "Karsen",
    "Velden",
    "Mirewood",
    "Solmar",
    "Briarwick",
    "Corhaven",
  ];

  const cities = points.slice(0, N).map((p, i) => ({
    x: p.x,
    y: p.y,
    id: i,
    name: CITY_NAMES[i] || `City ${i + 1}`,
  }));

  // Light relaxation to reduce near-overlaps (Lloyd-ish)
  for (let it = 0; it < 8; it++) {
    for (const a of cities) {
      let fx = 0, fy = 0;
      for (const b of cities) {
        if (a === b) continue;
        const d = dist(a, b);
        if (d < 1e-6) continue;
        const push = d < (minDist*1.12) ? (minDist*1.12 - d) : 0;
        if (push > 0) {
          fx += (a.x - b.x) / d * push * 0.15;
          fy += (a.y - b.y) / d * push * 0.15;
        }
      }
      a.x = clamp(a.x + fx, xMin, xMax);
      a.y = clamp(a.y + fy, yMin, yMax);
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

function pruneCollinearEdges(cities, edges, angleDeg = 170) {
  const edgeSet = new Set(edges.map(e => keyEdge(e.u, e.v)));
  const adj = Array.from({ length: cities.length }, () => []);
  for (const e of edges) {
    adj[e.u].push(e.v);
    adj[e.v].push(e.u);
  }

  function angleAt(a, b, c) {
    // angle ABC between BA and BC
    const bax = cities[a].x - cities[b].x;
    const bay = cities[a].y - cities[b].y;
    const bcx = cities[c].x - cities[b].x;
    const bcy = cities[c].y - cities[b].y;
    const dot = bax * bcx + bay * bcy;
    const na = Math.hypot(bax, bay) || 1;
    const nb = Math.hypot(bcx, bcy) || 1;
    const cos = clamp(dot / (na * nb), -1, 1);
    return Math.acos(cos) * 180 / Math.PI;
  }

  const toRemove = new Set();
  for (let b = 0; b < cities.length; b++) {
    const neighbors = adj[b];
    for (let i = 0; i < neighbors.length; i++) {
      for (let j = i + 1; j < neighbors.length; j++) {
        const a = neighbors[i];
        const c = neighbors[j];
        const ang = angleAt(a, b, c);
        if (ang < angleDeg) continue;

        const keyAC = keyEdge(a, c);
        if (!edgeSet.has(keyAC)) continue;

        const dAB = dist(cities[a], cities[b]);
        const dBC = dist(cities[b], cities[c]);
        const dAC = dist(cities[a], cities[c]);

        // If A-B-C are nearly collinear, drop the long direct edge A-C.
        if (dAC >= Math.max(dAB, dBC) * 1.15) {
          toRemove.add(keyAC);
        }
      }
    }
  }

  if (toRemove.size === 0) return edges;
  return edges.filter(e => !toRemove.has(keyEdge(e.u, e.v)));
}

const ROUTE_COLORS = [
  { name: "red",    hex: "#e74c3c" },
  { name: "blue",   hex: "#3498db" },
  { name: "green",  hex: "#2ecc71" },
  { name: "yellow", hex: "#f1c40f" },
  { name: "black",  hex: "#2d3436" },
  { name: "white",  hex: "#ecf0f1" },
  { name: "orange", hex: "#e67e22" },
  { name: "pink",   hex: "#ff6fb1" },
];
const GRAY = { name: "gray", hex: "#95a5a6" };

function assignColors(rng, edges, pGray) {
  // Balance by total length-load per color.
  const load = new Map();
  for (const c of ROUTE_COLORS) load.set(c.name, 0);
  const usedByCity = new Map();
  function citySet(id) {
    if (!usedByCity.has(id)) usedByCity.set(id, new Set());
    return usedByCity.get(id);
  }

  // Sort longest first so balancing matters
  const sorted = [...edges].sort((a,b)=>b.len-a.len);

  for (const e of sorted) {
    if (rng() < pGray) {
      e.color = GRAY;
      continue;
    }
    // choose among 3 lowest-load colors at random
    const ranked = [...ROUTE_COLORS].sort((a,b)=>load.get(a.name)-load.get(b.name));
    const forbid = new Set([...citySet(e.u), ...citySet(e.v)]);
    const allowed = ranked.filter(c => !forbid.has(c.name));
    const pool = (allowed.length ? allowed : ranked).slice(0, 3);
    const pick = pool[Math.floor(rng() * pool.length)];
    e.color = pick;
    load.set(pick.name, load.get(pick.name) + e.len);
    citySet(e.u).add(pick.name);
    citySet(e.v).add(pick.name);
  }
}

function generateMap(seedStr, params) {
  const rng = makeRng(seedStr);
  const N = params.nCities;
  const k = params.kNN;
  const eTarget = params.eTarget;
  const maxDeg = params.maxDeg;
  const pGray = params.pGray;

  const margin = 0.08;
  const bounds = { xMin: margin, xMax: 1 - margin, yMin: margin, yMax: 1 - margin };
  const cities = generateCities(rng, N, bounds);
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
  const pruned = pruneCollinearEdges(cities, res.edges, 150);
  assignLengths(pruned);
  assignColors(rng, pruned, pGray);
  const deg = Array(cities.length).fill(0);
  for (const e of pruned) { deg[e.u]++; deg[e.v]++; }
  return { cities, edges: pruned, deg };
}

const PLAYER_SHAPES = ["circle", "square", "triangle", "star"];
const PLAYER_SHAPE_GLYPHS = {
  circle: "●",
  square: "■",
  triangle: "▲",
  star: "★",
};

function playerShapeGlyph(shape) {
  return PLAYER_SHAPE_GLYPHS[shape] || "";
}

function buildPlayerShapeMappings(players) {
  const byId = new Map();
  const byColor = {};
  if (!Array.isArray(players)) return { byId, byColor };
  players.forEach((player, idx) => {
    const shape = PLAYER_SHAPES[idx % PLAYER_SHAPES.length];
    const playerId = String(player?.id || "");
    const color = String(player?.color || "").toLowerCase();
    if (playerId) byId.set(playerId, shape);
    if (color) byColor[color] = shape;
  });
  return { byId, byColor };
}

function createRouteClaimShape(shape, cx, cy, size, rotationDeg = 0) {
  const ns = "http://www.w3.org/2000/svg";
  const symbolSize = Math.max(5, size * 0.7);
  let shapeEl = null;

  if (shape === "circle") {
    shapeEl = document.createElementNS(ns, "circle");
    shapeEl.setAttribute("cx", cx);
    shapeEl.setAttribute("cy", cy);
    shapeEl.setAttribute("r", symbolSize * 0.3);
  } else if (shape === "square") {
    const side = symbolSize * 0.6;
    shapeEl = document.createElementNS(ns, "rect");
    shapeEl.setAttribute("x", cx - side / 2);
    shapeEl.setAttribute("y", cy - side / 2);
    shapeEl.setAttribute("width", side);
    shapeEl.setAttribute("height", side);
    shapeEl.setAttribute("rx", 1.5);
    shapeEl.setAttribute("ry", 1.5);
  } else if (shape === "triangle") {
    const r = symbolSize * 0.4;
    const points = [
      `${cx} ${cy - r}`,
      `${cx + r * 0.86} ${cy + r * 0.55}`,
      `${cx - r * 0.86} ${cy + r * 0.55}`,
    ];
    shapeEl = document.createElementNS(ns, "polygon");
    shapeEl.setAttribute("points", points.join(" "));
  } else if (shape === "star") {
    const outer = symbolSize * 0.42;
    const inner = outer * 0.5;
    const points = [];
    for (let i = 0; i < 10; i++) {
      const angle = -Math.PI / 2 + i * (Math.PI / 5);
      const radius = i % 2 === 0 ? outer : inner;
      const x = cx + Math.cos(angle) * radius;
      const y = cy + Math.sin(angle) * radius;
      points.push(`${x} ${y}`);
    }
    shapeEl = document.createElementNS(ns, "polygon");
    shapeEl.setAttribute("points", points.join(" "));
  }

  if (!shapeEl) return null;
  if ((shape === "triangle" || shape === "star") && Number.isFinite(rotationDeg)) {
    shapeEl.setAttribute("transform", `rotate(${rotationDeg} ${cx} ${cy})`);
  }
  shapeEl.setAttribute("class", `route-claim-shape route-claim-shape-${shape}`);
  shapeEl.style.pointerEvents = "none";
  return shapeEl;
}

/** ---------- SVG Rendering ---------- **/
function renderSvg(svg, map, opts) {
  const { cities, edges } = map;
  const box = 1000;
  const pad = 120;
  const usable = box - pad * 2;

  let minX=Infinity, minY=Infinity, maxX=-Infinity, maxY=-Infinity;
  for (const c of cities) {
    minX = Math.min(minX, c.x); minY = Math.min(minY, c.y);
    maxX = Math.max(maxX, c.x); maxY = Math.max(maxY, c.y);
  }
  const bx = maxX - minX || 1;
  const by = maxY - minY || 1;

  function toScreen(p) {
    const sx = pad + ( (p.x - minX) / bx ) * usable;
    const sy = pad + ( (p.y - minY) / by ) * usable;
    return { x: sx, y: sy };
  }

  function quadPoint(a, c, b, t) {
    const mt = 1 - t;
    return {
      x: mt*mt*a.x + 2*mt*t*c.x + t*t*b.x,
      y: mt*mt*a.y + 2*mt*t*c.y + t*t*b.y,
    };
  }

  function quadTangent(a, c, b, t) {
    return {
      x: 2*(1-t)*(c.x - a.x) + 2*t*(b.x - c.x),
      y: 2*(1-t)*(c.y - a.y) + 2*t*(b.y - c.y),
    };
  }

  function buildArcTable(a, c, b, steps = 40) {
    const table = [{ t: 0, len: 0, p: a }];
    let total = 0;
    let prev = a;
    for (let i = 1; i <= steps; i++) {
      const t = i / steps;
      const p = quadPoint(a, c, b, t);
      total += Math.hypot(p.x - prev.x, p.y - prev.y);
      table.push({ t, len: total, p });
      prev = p;
    }
    return table;
  }

  function tAtLength(table, targetLen) {
    if (targetLen <= 0) return 0;
    const last = table[table.length - 1];
    if (targetLen >= last.len) return 1;
    for (let i = 1; i < table.length; i++) {
      const a = table[i - 1];
      const b = table[i];
      if (targetLen <= b.len) {
        const span = b.len - a.len || 1;
        const f = (targetLen - a.len) / span;
        return a.t + (b.t - a.t) * f;
      }
    }
    return 1;
  }

  svg.innerHTML = "";

  for (let x = pad; x <= box - pad; x += 80) {
    const line = document.createElementNS("http://www.w3.org/2000/svg", "line");
    line.setAttribute("x1", x);
    line.setAttribute("y1", pad);
    line.setAttribute("x2", x);
    line.setAttribute("y2", box - pad);
    line.setAttribute("class", "grid-line");
    svg.appendChild(line);
  }
  for (let y = pad; y <= box - pad; y += 80) {
    const line = document.createElementNS("http://www.w3.org/2000/svg", "line");
    line.setAttribute("x1", pad);
    line.setAttribute("y1", y);
    line.setAttribute("x2", box - pad);
    line.setAttribute("y2", y);
    line.setAttribute("class", "grid-line");
    svg.appendChild(line);
  }

  const routeGroup = document.createElementNS("http://www.w3.org/2000/svg", "g");
  svg.appendChild(routeGroup);

  const tickets = opts.tickets || {};
  const trainsRemaining = Number.isFinite(opts.trainsRemaining) ? opts.trainsRemaining : Infinity;
  const canInteract = opts.interactive !== false;
  const claimedShapeByColor = opts.claimedShapeByColor || {};
  const showClaimShapes = !!opts.showClaimShapes;
  for (const e of edges) {
    const a = toScreen(cities[e.u]);
    const b = toScreen(cities[e.v]);
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

    const pathData = `M ${a.x} ${a.y} Q ${cx} ${cy} ${b.x} ${b.y}`;
    const claimedHex = e.claimedBy ? CLAIM_COLOR_MAP[e.claimedBy] : null;
    const claimedShape = e.claimedBy ? claimedShapeByColor[String(e.claimedBy).toLowerCase()] : "";
    const strokeHex = claimedHex || e.color.hex;
    const affordable = canInteract && !e.claimedBy && canAffordRoute(tickets, trainsRemaining, e.color.name, e.len);

    const under = document.createElementNS("http://www.w3.org/2000/svg", "path");
    under.setAttribute("d", pathData);
    under.setAttribute("class", "route route-under");
    under.setAttribute("stroke-width", width + 3);
    if (e.claimedBy) {
      under.classList.add("route-under-claimed");
      under.setAttribute("stroke-width", width + 5);
    }
    routeGroup.appendChild(under);

    const color = document.createElementNS("http://www.w3.org/2000/svg", "path");
    color.setAttribute("d", pathData);
    color.setAttribute("class", "route route-color");
    color.setAttribute("stroke", strokeHex);
    color.setAttribute("stroke-width", width);
    color.style.setProperty("--route-w", `${width}px`);
    const edgeId = keyEdge(e.u, e.v);
    color.dataset.edgeId = edgeId;
    color.dataset.len = String(e.len);
    color.dataset.color = e.claimedBy || e.color.name;
    color.dataset.routeColor = e.color.name;
    color.dataset.from = cities[e.u].name;
    color.dataset.to = cities[e.v].name;
    color.dataset.claimed = e.claimedBy ? "true" : "false";
    color.dataset.affordable = affordable ? "true" : "false";
    if (e.claimedBy) {
      color.classList.add("route-claimed", "route-disabled");
      color.style.pointerEvents = "none";
    } else if (!affordable) {
      color.classList.add("route-disabled", canInteract ? "dim" : "offturn");
      color.style.pointerEvents = "none";
    }
    routeGroup.appendChild(color);

    const arcTable = buildArcTable(a, { x: cx, y: cy }, b, 50);
    const totalLen = arcTable[arcTable.length - 1].len || 1;
    const blockLen = totalLen / e.len;

    for (let i = 0; i < e.len; i++) {
      const targetLen = blockLen * (i + 0.5);
      const t = tAtLength(arcTable, targetLen);
      const p = quadPoint(a, { x: cx, y: cy }, b, t);
      const tan = quadTangent(a, { x: cx, y: cy }, b, t);
      const ang = Math.atan2(tan.y, tan.x) * 180 / Math.PI;

      const bw = Math.min(30, Math.max(18, blockLen * 0.95));
      const bh = Math.min(12, Math.max(8, bw * 0.45));

      const block = document.createElementNS("http://www.w3.org/2000/svg", "rect");
      let bwDraw = bw;
      let bhDraw = bh;
      if (e.claimedBy) {
        bwDraw = bw * 1.18;
        bhDraw = bh * 1.18;
      }
      block.setAttribute("x", p.x - bwDraw / 2);
      block.setAttribute("y", p.y - bhDraw / 2);
      block.setAttribute("width", bwDraw);
      block.setAttribute("height", bhDraw);
      block.setAttribute("rx", 2);
      block.setAttribute("ry", 2);
      block.setAttribute("class", "route-seg route-hit");
      block.setAttribute("fill", strokeHex);
      block.style.setProperty("--route-w", `${bw}px`);
      block.dataset.edgeId = edgeId;
      block.dataset.segIndex = String(i);
      block.dataset.segCount = String(e.len);
      block.dataset.len = String(e.len);
      block.dataset.color = e.claimedBy || e.color.name;
      block.dataset.routeColor = e.color.name;
      block.dataset.from = cities[e.u].name;
      block.dataset.to = cities[e.v].name;
      block.dataset.claimed = e.claimedBy ? "true" : "false";
      block.dataset.affordable = affordable ? "true" : "false";
      if (e.claimedBy) {
        block.classList.add("route-claimed", "route-disabled");
        block.style.pointerEvents = "none";
      } else if (!affordable) {
        block.classList.add("route-disabled", canInteract ? "dim" : "offturn");
        block.style.pointerEvents = "none";
      }
      block.setAttribute("transform", `rotate(${ang} ${p.x} ${p.y})`);
      routeGroup.appendChild(block);
      if (e.claimedBy && showClaimShapes && claimedShape) {
        const shapeEl = createRouteClaimShape(claimedShape, p.x, p.y, bwDraw, ang);
        if (shapeEl) {
          shapeEl.dataset.edgeId = edgeId;
          shapeEl.dataset.segIndex = String(i);
          routeGroup.appendChild(shapeEl);
        }
      }
    }
  }

  const cityGroup = document.createElementNS("http://www.w3.org/2000/svg", "g");
  svg.appendChild(cityGroup);

  for (const c of cities) {
    const p = toScreen(c);

    const glow = document.createElementNS("http://www.w3.org/2000/svg", "circle");
    glow.setAttribute("cx", p.x);
    glow.setAttribute("cy", p.y);
    glow.setAttribute("r", 12);
    glow.setAttribute("class", "city-glow");
    glow.dataset.cityId = String(c.id);
    cityGroup.appendChild(glow);

    const node = document.createElementNS("http://www.w3.org/2000/svg", "circle");
    node.setAttribute("cx", p.x);
    node.setAttribute("cy", p.y);
    node.setAttribute("r", 7);
    node.setAttribute("class", "city");
    node.dataset.cityId = String(c.id);
    cityGroup.appendChild(node);

    if (opts.labels) {
      const label = document.createElementNS("http://www.w3.org/2000/svg", "text");
      label.setAttribute("x", p.x + 10);
      label.setAttribute("y", p.y - 10);
      label.setAttribute("class", "label");
      label.dataset.cityId = String(c.id);
      label.textContent = c.name;
      cityGroup.appendChild(label);
    }
  }
}

/** ---------- App wiring ---------- **/
const CLAIM_COLORS = [
  { name: "claim-red", hex: "#cc0000" },
  { name: "claim-green", hex: "#008000" },
  { name: "claim-blue", hex: "#0000cc" },
  { name: "claim-yellow", hex: "#b58900" },
];
const CLAIM_COLOR_MAP = {
  red: "#cc0000",
  green: "#008000",
  blue: "#0000cc",
  yellow: "#b58900",
};

const CARD_ORDER = [
  "red",
  "blue",
  "green",
  "yellow",
  "black",
  "white",
  "orange",
  "pink",
  "rainbow",
];

const gameWrapEl = document.getElementById("gameWrap");
const lobbyScreenEl = document.getElementById("lobbyScreen");
const lobbyJoinFormEl = document.getElementById("lobbyJoinForm");
const lobbyNameInputEl = document.getElementById("lobbyNameInput");
const lobbyJoinBtnEl = document.getElementById("lobbyJoinBtn");
const lobbyStartBtnEl = document.getElementById("lobbyStartBtn");
const lobbyHowToPlayBtnEl = document.getElementById("lobbyHowToPlayBtn");
const lobbyPlayersListEl = document.getElementById("lobbyPlayersList");
const lobbyStatusEl = document.getElementById("lobbyStatus");

const svg = document.getElementById("mapSvg");
const routeInfo = document.getElementById("routeInfo");
const submitBtn = document.getElementById("submitBtn");
const faceUpEl = document.getElementById("faceUpCards");
const gameBox = document.getElementById("gameBox");
const stageInner = document.querySelector(".stage-inner");
const ticketPileEl = document.getElementById("ticketPile");
const deckBackEl = document.getElementById("deckBack");
const playersListEl = document.getElementById("playersList");
const logListEl = document.getElementById("logList");
const colorModalEl = document.getElementById("colorModal");
const colorOptionsEl = document.getElementById("colorOptions");
const colorSubmitEl = document.getElementById("colorSubmit");
const colorCancelEl = document.getElementById("colorCancel");
const gameOverModalEl = document.getElementById("gameOverModal");
const gameOverSummaryEl = document.getElementById("gameOverSummary");
const standingsListEl = document.getElementById("standingsList");
const gameOverCloseBtnEl = document.getElementById("gameOverCloseBtn");
const returnLobbyBtnEl = document.getElementById("returnLobbyBtn");
const endGameActionsEl = document.getElementById("endGameActions");
const viewResultsBtnEl = document.getElementById("viewResultsBtn");
const sidebarReturnLobbyBtnEl = document.getElementById("sidebarReturnLobbyBtn");
const howToPlayModalEl = document.getElementById("howToPlayModal");
const howToPlayCloseBtnEl = document.getElementById("howToPlayCloseBtn");
const chatPanelEl = document.getElementById("chatPanel");
const chatToggleBtnEl = document.getElementById("chatToggleBtn");
const chatBodyEl = document.getElementById("chatBody");
const chatMessagesEl = document.getElementById("chatMessages");
const chatFormEl = document.getElementById("chatForm");
const chatInputEl = document.getElementById("chatInput");
const chatSendBtnEl = document.getElementById("chatSendBtn");
const destinationTicketsListEl = document.getElementById("destinationTicketsList");
const drawDestinationBtnEl = document.getElementById("drawDestinationBtn");
const ticketSelectPanelEl = document.getElementById("ticketSelectPanel");
const ticketSelectHintEl = document.getElementById("ticketSelectHint");
const ticketSelectListEl = document.getElementById("ticketSelectList");
const ticketSelectSubmitEl = document.getElementById("ticketSelectSubmit");
const colorBlindToggleEl = document.getElementById("colorBlindToggle");

let currentMap = null;
let selectedEdgeId = null;
let selectedEdgeMeta = null;
let pendingColor = null;
let idleRouteInfoText = "Select a route";
let ticketCounts = Object.fromEntries(CARD_ORDER.map((k) => [k, 0]));
let myTrainsRemaining = 0;
let destinationTickets = [];
let destinationTicketResults = [];
let pendingDestinationOffer = [];
let selectedOfferTicketIds = new Set();
let destinationTicketMinKeep = 2;
let destinationSelectionPending = false;
let destinationTicketsRemaining = 0;
let setupPhase = false;
let chatMessages = [];
let ws = null;
let turnDrawCount = 0;
let isMyTurn = false;
let amPlayer = false;
let myPlayerId = null;
let gameStarted = false;
let gameOver = false;
let lobbyCanJoin = false;
let lobbyCanStart = false;
let lastFaceUpCards = [];
let activeFaceUpDealAnimation = null;
let lastSeenFaceUpReplacementSeq = null;
let lastEdgeClaimsById = null;
let routeBuildAnimationTimers = [];
let pendingCardPickupAnimations = [];
let ticketArrivalTimers = [];
let playerShapeById = new Map();
let playerShapeByColor = {};
let playersSnapshot = [];
let currentTurnSnapshot = 0;
const CLIENT_TOKEN_KEY = "ticket_to_ride_client_token";
const COLORBLIND_MODE_KEY = "ticket_to_ride_colorblind_mode";
const ticketSelectAudio = new Audio("/sound/ticket_select.wav");
ticketSelectAudio.preload = "auto";
const routeBuildAudio = new Audio("/sound/route_build.wav");
routeBuildAudio.preload = "auto";
const trainWhistleAudio = new Audio("/sound/train_whistle.wav");
trainWhistleAudio.preload = "auto";
const destinationTicketDrawAudio = new Audio("/sound/destination_ticket_draw.wav");
destinationTicketDrawAudio.preload = "auto";
const turnNotificationAudio = new Audio("/sound/turn_notification.wav");
turnNotificationAudio.preload = "auto";

function getRoomNameFromPath() {
  const parts = window.location.pathname.split("/").filter(Boolean);
  return parts.length > 0 ? parts[0] : "";
}

const currentRoomName = getRoomNameFromPath();

function playAudioSafe(audioEl) {
  if (!audioEl) return;
  try {
    audioEl.currentTime = 0;
    const playPromise = audioEl.play();
    if (playPromise && typeof playPromise.catch === "function") {
      playPromise.catch(() => {});
    }
  } catch (err) {
    // ignore autoplay / audio errors
  }
}

function setGameVisibility(showGame) {
  if (gameWrapEl) gameWrapEl.classList.toggle("hidden", !showGame);
  if (lobbyScreenEl) lobbyScreenEl.classList.toggle("hidden", showGame);
  if (showGame) hideHowToPlayModal();
}

function setChatCollapsed(collapsed) {
  if (!chatPanelEl || !chatToggleBtnEl) return;
  chatPanelEl.classList.toggle("collapsed", !!collapsed);
  chatToggleBtnEl.setAttribute("aria-expanded", collapsed ? "false" : "true");
  chatToggleBtnEl.textContent = collapsed ? "\u25A1" : "-";
  chatToggleBtnEl.setAttribute("aria-label", collapsed ? "Show chat" : "Hide chat");
}

function applyChatInputAccess() {
  const canSend = !!(gameStarted && amPlayer);
  if (chatInputEl) {
    chatInputEl.disabled = !canSend;
    chatInputEl.placeholder = canSend ? "Type a message" : "Chat is read-only for spectators";
  }
  if (chatSendBtnEl) chatSendBtnEl.disabled = !canSend;
}

function isColorBlindModeEnabled() {
  return document.body.classList.contains("colorblind-mode");
}

function getPlayerShapeForPlayer(player) {
  if (!player) return "";
  const playerId = String(player.id || "");
  if (playerId && playerShapeById.has(playerId)) {
    return playerShapeById.get(playerId) || "";
  }
  const color = String(player.color || "").toLowerCase();
  return color ? (playerShapeByColor[color] || "") : "";
}

function getPlayerShapeForChatEntry(entry) {
  if (!entry) return "";
  const playerId = String(entry.playerId || "");
  if (playerId && playerShapeById.has(playerId)) {
    return playerShapeById.get(playerId) || "";
  }
  const color = String(entry.playerColor || "").toLowerCase();
  return color ? (playerShapeByColor[color] || "") : "";
}

function makePlayerShapeTag(shape, className = "player-shape-tag") {
  const tag = document.createElement("span");
  tag.className = className;
  tag.dataset.shape = shape;
  tag.textContent = playerShapeGlyph(shape);
  tag.setAttribute("aria-hidden", "true");
  return tag;
}

function applyPlayerSwatchAppearance(swatch, player) {
  if (!(swatch instanceof HTMLElement)) return;
  const color = player?.hex || player?.color || "#8b8b8b";
  if (isColorBlindModeEnabled()) {
    const shape = getPlayerShapeForPlayer(player);
    swatch.classList.add("shape-mode");
    if (shape) {
      swatch.dataset.shape = shape;
      swatch.textContent = playerShapeGlyph(shape);
    } else {
      delete swatch.dataset.shape;
      swatch.textContent = "";
    }
    swatch.style.background = "rgba(255, 245, 226, 0.95)";
    return;
  }

  swatch.classList.remove("shape-mode");
  delete swatch.dataset.shape;
  swatch.textContent = "";
  swatch.style.background = color;
}

function renderChatMessages() {
  if (!chatMessagesEl) return;
  chatMessagesEl.innerHTML = "";
  if (!Array.isArray(chatMessages) || chatMessages.length === 0) {
    const empty = document.createElement("div");
    empty.className = "chat-empty";
    empty.textContent = "No messages yet.";
    chatMessagesEl.appendChild(empty);
    return;
  }
  chatMessages.forEach((entry) => {
    const row = document.createElement("div");
    row.className = "chat-message";

    const sender = document.createElement("span");
    sender.className = "chat-sender";
    if (isColorBlindModeEnabled()) {
      const shape = getPlayerShapeForChatEntry(entry);
      if (shape) sender.appendChild(makePlayerShapeTag(shape, "chat-shape-tag"));
      const senderName = document.createElement("span");
      senderName.textContent = `${entry.playerName || "Player"}: `;
      sender.appendChild(senderName);
      sender.style.color = "";
    } else {
      sender.textContent = `${entry.playerName || "Player"}: `;
      sender.style.color = entry.playerHex || "";
    }
    row.appendChild(sender);

    const text = document.createElement("span");
    text.textContent = entry.text || "";
    row.appendChild(text);
    chatMessagesEl.appendChild(row);
  });
  chatMessagesEl.scrollTop = chatMessagesEl.scrollHeight;
}

function setChatMessages(nextMessages) {
  chatMessages = Array.isArray(nextMessages)
    ? nextMessages.filter((m) => m && typeof m.text === "string")
    : [];
  renderChatMessages();
}

function appendChatMessage(entry) {
  if (!entry || typeof entry.text !== "string") return;
  const id = String(entry.id || "");
  if (id && chatMessages.some((m) => m.id === id)) return;
  chatMessages.push(entry);
  if (chatMessages.length > 120) {
    chatMessages = chatMessages.slice(chatMessages.length - 120);
  }
  renderChatMessages();
}

function hideGameOverModal() {
  if (gameOverModalEl) gameOverModalEl.classList.add("hidden");
}

const COLOR_ASSIST_LABELS = {
  red: "R",
  blue: "B",
  green: "G",
  yellow: "Y",
  black: "K",
  white: "W",
  orange: "O",
  pink: "P",
  rainbow: "*",
  gray: "GY",
};

function colorAssistLabel(color) {
  const key = String(color || "").toLowerCase();
  return COLOR_ASSIST_LABELS[key] || key.slice(0, 2).toUpperCase();
}

function makeColorAssistTag(color) {
  const tag = document.createElement("span");
  tag.className = "color-assist-tag";
  tag.textContent = colorAssistLabel(color);
  tag.setAttribute("aria-hidden", "true");
  return tag;
}

function applyColorBlindMode(enabled) {
  const on = !!enabled;
  document.body.classList.toggle("colorblind-mode", on);
  if (colorBlindToggleEl) colorBlindToggleEl.checked = on;
  try {
    window.localStorage.setItem(COLORBLIND_MODE_KEY, on ? "1" : "0");
  } catch (err) {
    // ignore storage failures
  }
  renderChatMessages();
  if (playersSnapshot.length > 0) {
    renderPlayers(playersSnapshot, currentTurnSnapshot);
  }
  if (gameStarted && currentMap) {
    const prevSelectedEdgeId = selectedEdgeId;
    const prevRouteText = routeInfo?.textContent || "";
    clearRouteBuildAnimations();
    render();
    if (prevSelectedEdgeId) {
      const selectedEl = svg.querySelector(`.route-color[data-edge-id="${prevSelectedEdgeId}"], .route-hit[data-edge-id="${prevSelectedEdgeId}"]`);
      if (selectedEl && selectedEl.dataset.claimed !== "true" && selectedEl.dataset.affordable === "true") {
        svg.querySelectorAll(`[data-edge-id="${prevSelectedEdgeId}"]`).forEach((el) => el.classList.add("route-selected"));
        selectedEdgeId = prevSelectedEdgeId;
        selectedEdgeMeta = {
          edgeId: prevSelectedEdgeId,
          routeColor: selectedEl.dataset.routeColor || selectedEl.dataset.color,
          len: Number(selectedEl.dataset.len),
          claimed: false,
          affordable: true,
        };
        submitBtn.disabled = false;
        if (routeInfo) {
          routeInfo.textContent = prevRouteText || `${selectedEl.dataset.from} - ${selectedEl.dataset.to}`;
        }
      }
    }
  }
}

function showGameOverModal() {
  if (gameOverModalEl) gameOverModalEl.classList.remove("hidden");
}

function refreshEndGameControls() {
  if (endGameActionsEl) endGameActionsEl.classList.toggle("hidden", !gameOver);
  const canReturn = !!(gameOver && amPlayer && ws && ws.readyState === WebSocket.OPEN);
  if (sidebarReturnLobbyBtnEl) sidebarReturnLobbyBtnEl.disabled = !canReturn;
}

function sendReturnToLobby() {
  if (!ws || ws.readyState !== WebSocket.OPEN) return;
  ws.send(JSON.stringify({ type: "return_to_lobby" }));
}

function showHowToPlayModal() {
  if (howToPlayModalEl) howToPlayModalEl.classList.remove("hidden");
}

function hideHowToPlayModal() {
  if (howToPlayModalEl) howToPlayModalEl.classList.add("hidden");
}

function closeTicketSelectModal() {
  if (ticketSelectPanelEl) ticketSelectPanelEl.classList.add("hidden");
  pendingDestinationOffer = [];
  selectedOfferTicketIds = new Set();
  clearCityHighlights();
}

function setInitialTicketSelectionFocus(active) {
  if (gameWrapEl) gameWrapEl.classList.toggle("initial-ticket-focus", !!active);
  if (ticketSelectPanelEl) ticketSelectPanelEl.classList.toggle("focus-emphasis", !!active);
}

function refreshDestinationControls() {
  if (!drawDestinationBtnEl) return;
  const canDraw = amPlayer &&
    isMyTurn &&
    !gameOver &&
    !setupPhase &&
    !destinationSelectionPending &&
    turnDrawCount === 0 &&
    destinationTicketsRemaining > 0;
  drawDestinationBtnEl.disabled = !canDraw;
  drawDestinationBtnEl.textContent = destinationTicketsRemaining > 0
    ? `Draw destination tickets (${destinationTicketsRemaining})`
    : "Draw destination tickets";
}

function canTakeTurnActions() {
  return amPlayer && isMyTurn && !gameOver && !setupPhase && !destinationSelectionPending;
}

function canTakeNonDrawTurnActions() {
  return canTakeTurnActions() && turnDrawCount === 0;
}

function setHighlightedCities(cityIds) {
  clearCityHighlights();
  if (!Array.isArray(cityIds) || cityIds.length === 0) return;
  cityIds.forEach((cityId) => {
    svg
      .querySelectorAll(`[data-city-id="${cityId}"]`)
      .forEach((el) => el.classList.add("city-highlight"));
  });
}

function clearCityHighlights() {
  svg.querySelectorAll(".city-highlight").forEach((el) => el.classList.remove("city-highlight"));
}

function setLobbyStatus(text) {
  if (!lobbyStatusEl) return;
  lobbyStatusEl.textContent = text || "";
}

function refreshLobbyControls() {
  const name = (lobbyNameInputEl?.value || "").trim();
  if (lobbyJoinBtnEl) lobbyJoinBtnEl.disabled = !lobbyCanJoin || !name;
  if (lobbyNameInputEl) lobbyNameInputEl.disabled = !lobbyCanJoin;
  if (lobbyStartBtnEl) lobbyStartBtnEl.disabled = !lobbyCanStart;
}

function renderLobby(payload) {
  const players = (payload && payload.players) || [];
  const activeGame = !!payload?.activeGame;
  if (lobbyPlayersListEl) {
    lobbyPlayersListEl.innerHTML = "";
    players.forEach((p) => {
      const row = document.createElement("div");
      row.className = "lobby-player";

      const swatch = document.createElement("div");
      swatch.className = "player-swatch";
      swatch.style.background = p.hex || p.color;

      const name = document.createElement("div");
      name.textContent = `${p.name}`;

      row.appendChild(swatch);
      row.appendChild(name);
      lobbyPlayersListEl.appendChild(row);
    });
  }

  lobbyCanJoin = !!(payload && payload.canJoin);
  lobbyCanStart = !!(payload && payload.canStart);

  const showStart = !activeGame && players.length >= 2;
  if (lobbyStartBtnEl) lobbyStartBtnEl.classList.toggle("hidden", !showStart);

  if (payload?.you) {
    setLobbyStatus("");
    if (lobbyNameInputEl && !lobbyNameInputEl.value) {
      lobbyNameInputEl.value = payload.you.name || "";
    }
  } else if (activeGame) {
    setLobbyStatus("Game in progress. You can wait in the lobby.");
  } else if (players.length >= (payload?.maxPlayers || 4)) {
    setLobbyStatus("Lobby is full.");
  } else {
    setLobbyStatus("");
  }

  refreshLobbyControls();
}

function setIdleRouteInfo(text) {
  idleRouteInfoText = text || "Select a route";
  if (!selectedEdgeMeta && routeInfo) {
    routeInfo.textContent = idleRouteInfoText;
  }
}

function updateTurnStatus(
  players,
  currentTurn,
  finalRoundActive,
  finalRoundTriggeredBy,
  isGameOver,
  setupPhase,
  awaitingTicketSelection
) {
  if (isGameOver) {
    setIdleRouteInfo("Game over");
    return;
  }
  if (setupPhase) {
    if (amPlayer && awaitingTicketSelection) {
      setIdleRouteInfo("Choose destination tickets");
      return;
    }
    setIdleRouteInfo("Waiting for players to choose destination tickets");
    return;
  }

  const active = players[currentTurn] || null;
  if (!active) {
    setIdleRouteInfo("Select a route");
    return;
  }

  if (amPlayer && isMyTurn) {
    setIdleRouteInfo(finalRoundActive ? "Final round: take your last turn" : "Select a route");
    return;
  }

  if (finalRoundActive) {
    setIdleRouteInfo(`Final round. Waiting for ${active.name}`);
    return;
  }

  setIdleRouteInfo(`Waiting for ${active.name}`);
}

function render() {
  if (!currentMap) return;
  renderSvg(svg, currentMap, {
    labels: true,
    tickets: ticketCounts,
    trainsRemaining: myTrainsRemaining,
    interactive: canTakeNonDrawTurnActions(),
    claimedShapeByColor: playerShapeByColor,
    showClaimShapes: isColorBlindModeEnabled(),
  });
  wireRoutes();
  selectedEdgeId = null;
  selectedEdgeMeta = null;
  submitBtn.disabled = true;
  routeInfo.textContent = idleRouteInfoText;
}

function clearFaceUpDealAnimation() {
  if (!activeFaceUpDealAnimation) return;
  const { animation, mover, target, revealTimer } = activeFaceUpDealAnimation;
  if (Number.isFinite(revealTimer)) {
    window.clearTimeout(revealTimer);
  }
  if (animation && typeof animation.cancel === "function") {
    try {
      animation.cancel();
    } catch (err) {
      // ignore animation cancellation errors
    }
  }
  if (mover?.isConnected) mover.remove();
  if (target instanceof HTMLElement) {
    target.classList.remove("incoming-from-deck");
    target.classList.remove("deal-arrived");
  }
  activeFaceUpDealAnimation = null;
}

function revealIncomingFaceUpCard(target, mover) {
  if (mover?.isConnected) mover.remove();
  if (!(target instanceof HTMLElement)) return;
  target.classList.remove("incoming-from-deck");
  target.classList.add("deal-arrived");
  const revealTimer = window.setTimeout(() => {
    target.classList.remove("deal-arrived");
    if (activeFaceUpDealAnimation?.target === target) {
      activeFaceUpDealAnimation = null;
    }
  }, 320);
  if (activeFaceUpDealAnimation?.target === target) {
    activeFaceUpDealAnimation.revealTimer = revealTimer;
  }
}

function animateDeckToFaceUpSlot(index) {
  if (!Number.isFinite(index) || index < 0) return;
  if (!deckBackEl || !faceUpEl) return;
  if (typeof window.matchMedia === "function" &&
      window.matchMedia("(prefers-reduced-motion: reduce)").matches) {
    return;
  }
  const target = faceUpEl.querySelector(`img[data-index="${index}"]`);
  if (!(target instanceof HTMLImageElement)) return;

  const deckRect = deckBackEl.getBoundingClientRect();
  const targetRect = target.getBoundingClientRect();
  if (deckRect.width <= 0 || deckRect.height <= 0 || targetRect.width <= 0 || targetRect.height <= 0) {
    return;
  }

  target.classList.add("incoming-from-deck");
  const mover = document.createElement("img");
  mover.className = "card deck-deal-fly";
  mover.src = "/img/back.png";
  mover.alt = "";
  mover.setAttribute("aria-hidden", "true");
  mover.style.position = "fixed";
  mover.style.left = `${deckRect.left}px`;
  mover.style.top = `${deckRect.top}px`;
  mover.style.width = `${deckRect.width}px`;
  mover.style.height = `${deckRect.height}px`;
  mover.style.pointerEvents = "none";
  mover.style.zIndex = "1200";
  mover.style.margin = "0";
  document.body.appendChild(mover);

  const dx = targetRect.left - deckRect.left;
  const dy = targetRect.top - deckRect.top;
  const sx = targetRect.width / deckRect.width;
  const sy = targetRect.height / deckRect.height;

  if (typeof mover.animate !== "function") {
    revealIncomingFaceUpCard(target, mover);
    return;
  }

  const animation = mover.animate(
    [
      { transform: "translate(0px, 0px) scale(1, 1)", opacity: 1 },
      { transform: `translate(${dx}px, ${dy}px) scale(${sx}, ${sy})`, opacity: 1 },
    ],
    {
      duration: 520,
      easing: "cubic-bezier(0.2, 0.7, 0.25, 1)",
      fill: "forwards",
    }
  );
  activeFaceUpDealAnimation = {
    animation,
    mover,
    target,
    revealTimer: null,
  };
  animation.onfinish = () => {
    if (activeFaceUpDealAnimation?.animation !== animation) return;
    revealIncomingFaceUpCard(target, mover);
  };
  animation.oncancel = () => {
    if (mover?.isConnected) mover.remove();
    target.classList.remove("incoming-from-deck");
    if (activeFaceUpDealAnimation?.animation === animation) {
      activeFaceUpDealAnimation = null;
    }
  };
}

function findFaceUpReplacementIndex(prevFaceUp, nextFaceUp) {
  if (!Array.isArray(prevFaceUp) || !Array.isArray(nextFaceUp)) return -1;
  if (prevFaceUp.length <= 0 || prevFaceUp.length !== nextFaceUp.length) return -1;
  let changed = -1;
  for (let i = 0; i < nextFaceUp.length; i++) {
    if (prevFaceUp[i] === nextFaceUp[i]) continue;
    if (changed >= 0) return -1;
    changed = i;
  }
  return changed;
}

function drawFaceUp(faceUp, animatedReplacementIndex = -1) {
  clearFaceUpDealAnimation();
  faceUpEl.innerHTML = "";
  for (let i = 0; i < faceUp.length; i++) {
    const name = faceUp[i];
    const shell = document.createElement("div");
    shell.className = "face-up-card-shell";
    const img = document.createElement("img");
    img.className = "card";
    img.alt = `${name} card`;
    img.src = `/img/${name}.png`;
    img.dataset.color = name;
    img.dataset.index = String(i);

    const canPick = canTakeTurnActions() && !(name === "rainbow" && turnDrawCount > 0);
    if (canPick) {
      img.classList.add("clickable");
    } else if (canTakeTurnActions() && name === "rainbow" && turnDrawCount > 0) {
      img.classList.add("disabled");
    }

    shell.appendChild(img);
    shell.appendChild(makeColorAssistTag(name));
    faceUpEl.appendChild(shell);
  }

  if (animatedReplacementIndex >= 0) {
    animateDeckToFaceUpSlot(animatedReplacementIndex);
  }
}

function clearRouteBuildAnimations() {
  if (routeBuildAnimationTimers.length > 0) {
    routeBuildAnimationTimers.forEach((timerId) => window.clearTimeout(timerId));
    routeBuildAnimationTimers = [];
  }
  svg.querySelectorAll(".route-build-pending").forEach((el) => el.classList.remove("route-build-pending"));
  svg.querySelectorAll(".route-build-active").forEach((el) => el.classList.remove("route-build-active"));
  svg.querySelectorAll(".route-build-path").forEach((el) => el.classList.remove("route-build-path"));
}

function queueRouteBuildTimer(fn, delayMs) {
  const timerId = window.setTimeout(() => {
    routeBuildAnimationTimers = routeBuildAnimationTimers.filter((id) => id !== timerId);
    fn();
  }, delayMs);
  routeBuildAnimationTimers.push(timerId);
}

function buildEdgeClaimsMap(edges) {
  const claims = new Map();
  if (!Array.isArray(edges)) return claims;
  edges.forEach((e) => {
    const edgeId = keyEdge(e.u, e.v);
    claims.set(edgeId, String(e.claimedBy || ""));
  });
  return claims;
}

function findNewlyClaimedEdgeIds(prevClaimsByEdgeId, nextEdges) {
  if (!(prevClaimsByEdgeId instanceof Map) || !Array.isArray(nextEdges)) return [];
  const newlyClaimed = [];
  nextEdges.forEach((e) => {
    const edgeId = keyEdge(e.u, e.v);
    const nextClaim = String(e.claimedBy || "");
    const prevClaim = String(prevClaimsByEdgeId.get(edgeId) || "");
    if (!prevClaim && nextClaim) {
      newlyClaimed.push(edgeId);
    }
  });
  return newlyClaimed;
}

function animateClaimedRoute(edgeId, edgeOffsetMs = 0) {
  if (!edgeId) return;
  const segs = [...svg.querySelectorAll(`.route-seg[data-edge-id="${edgeId}"]`)];
  if (segs.length <= 0) return;
  segs.sort((a, b) => Number(a.dataset.segIndex) - Number(b.dataset.segIndex));

  const pathEls = [...svg.querySelectorAll(`.route-color[data-edge-id="${edgeId}"]`)];
  segs.forEach((seg) => {
    seg.classList.remove("route-build-active");
    seg.classList.add("route-build-pending");
  });
  pathEls.forEach((el) => el.classList.add("route-build-path"));

  const stepMs = 140;
  const activeMs = 220;
  segs.forEach((seg, idx) => {
    queueRouteBuildTimer(() => {
      seg.classList.add("route-build-active");
      queueRouteBuildTimer(() => {
        seg.classList.remove("route-build-active");
      }, activeMs);
    }, edgeOffsetMs + idx * stepMs);
  });

  const cleanupDelay = edgeOffsetMs + segs.length * stepMs + activeMs + 50;
  queueRouteBuildTimer(() => {
    segs.forEach((seg) => {
      seg.classList.remove("route-build-pending");
      seg.classList.remove("route-build-active");
    });
    pathEls.forEach((el) => el.classList.remove("route-build-path"));
  }, cleanupDelay);
}

function animateClaimedRoutes(edgeIds) {
  if (!Array.isArray(edgeIds) || edgeIds.length <= 0) return;
  clearRouteBuildAnimations();
  edgeIds.forEach((edgeId, idx) => {
    animateClaimedRoute(edgeId, idx * 180);
  });
}

function snapshotRect(el) {
  if (!(el instanceof Element)) return null;
  const rect = el.getBoundingClientRect();
  if (rect.width <= 0 || rect.height <= 0) return null;
  return {
    left: rect.left,
    top: rect.top,
    width: rect.width,
    height: rect.height,
  };
}

function queuePendingCardPickup(sourceEl, cardImageSrc) {
  const sourceRect = snapshotRect(sourceEl);
  if (!sourceRect) return;
  pendingCardPickupAnimations.push({
    sourceRect,
    cardImageSrc: String(cardImageSrc || "/img/back.png"),
    requestedAt: Date.now(),
  });
}

function prunePendingCardPickupAnimations(maxAgeMs = 5000) {
  const now = Date.now();
  pendingCardPickupAnimations = pendingCardPickupAnimations.filter((entry) =>
    (now - (entry.requestedAt || 0)) <= maxAgeMs
  );
}

function clearCardPickupAnimationState(clearPending = true) {
  if (clearPending) {
    pendingCardPickupAnimations = [];
  }
  if (ticketArrivalTimers.length > 0) {
    ticketArrivalTimers.forEach((timerId) => window.clearTimeout(timerId));
    ticketArrivalTimers = [];
  }
  ticketPileEl?.querySelectorAll(".ticket-arrive").forEach((el) => el.classList.remove("ticket-arrive"));
  document.querySelectorAll(".ticket-transfer-fly").forEach((el) => el.remove());
}

function getSingleCardGainColor(prevCounts, nextCounts) {
  if (!prevCounts || !nextCounts) return "";
  let totalDelta = 0;
  let gainColor = "";
  for (const color of CARD_ORDER) {
    const prev = Number(prevCounts[color] || 0);
    const next = Number(nextCounts[color] || 0);
    const delta = next - prev;
    totalDelta += delta;
    if (delta < 0) return "";
    if (delta > 0) {
      if (delta !== 1 || gainColor) return "";
      gainColor = color;
    }
  }
  return totalDelta === 1 ? gainColor : "";
}

function markTicketPileArrival(color) {
  if (!ticketPileEl || !color) return;
  const item = ticketPileEl.querySelector(`.ticket-item[data-color="${color}"]`);
  if (!(item instanceof HTMLElement)) return;
  item.classList.add("ticket-arrive");
  const timerId = window.setTimeout(() => {
    item.classList.remove("ticket-arrive");
    ticketArrivalTimers = ticketArrivalTimers.filter((id) => id !== timerId);
  }, 320);
  ticketArrivalTimers.push(timerId);
}

function animateCardPickupToTicketPile(drawRequest, gainedColor) {
  if (!drawRequest || !gainedColor || !ticketPileEl) return;
  markTicketPileArrival(gainedColor);
  if (typeof window.matchMedia === "function" &&
      window.matchMedia("(prefers-reduced-motion: reduce)").matches) {
    return;
  }

  const sourceRect = drawRequest.sourceRect || null;
  const targetImg = ticketPileEl.querySelector(`.ticket-item[data-color="${gainedColor}"] img`);
  const targetRect = snapshotRect(targetImg || ticketPileEl);
  if (!sourceRect || !targetRect) return;

  const mover = document.createElement("img");
  mover.className = "card ticket-transfer-fly";
  mover.src = drawRequest.cardImageSrc || `/img/${gainedColor}.png`;
  mover.alt = "";
  mover.setAttribute("aria-hidden", "true");
  mover.style.position = "fixed";
  mover.style.left = `${sourceRect.left}px`;
  mover.style.top = `${sourceRect.top}px`;
  mover.style.width = `${sourceRect.width}px`;
  mover.style.height = `${sourceRect.height}px`;
  mover.style.pointerEvents = "none";
  mover.style.zIndex = "1250";
  mover.style.margin = "0";
  document.body.appendChild(mover);

  const fromCx = sourceRect.left + sourceRect.width / 2;
  const fromCy = sourceRect.top + sourceRect.height / 2;
  const toCx = targetRect.left + targetRect.width / 2;
  const toCy = targetRect.top + targetRect.height / 2;
  const dx = toCx - fromCx;
  const dy = toCy - fromCy;
  const sx = Math.max(0.55, Math.min(1.1, targetRect.width / sourceRect.width));
  const sy = Math.max(0.55, Math.min(1.1, targetRect.height / sourceRect.height));

  if (typeof mover.animate !== "function") {
    mover.remove();
    return;
  }

  const animation = mover.animate(
    [
      { transform: "translate(0px, 0px) scale(1, 1)", opacity: 1 },
      { transform: `translate(${dx}px, ${dy}px) scale(${sx}, ${sy})`, opacity: 0.98 },
    ],
    {
      duration: 430,
      easing: "cubic-bezier(0.2, 0.75, 0.25, 1)",
      fill: "forwards",
    }
  );
  animation.onfinish = () => {
    if (mover.isConnected) mover.remove();
  };
  animation.oncancel = () => {
    if (mover.isConnected) mover.remove();
  };
}

function maybeAnimatePendingCardPickup(prevCounts, nextCounts) {
  if (pendingCardPickupAnimations.length <= 0) return;
  prunePendingCardPickupAnimations();
  if (pendingCardPickupAnimations.length <= 0) return;
  const gainedColor = getSingleCardGainColor(prevCounts, nextCounts);
  if (!gainedColor) return;
  const drawRequest = pendingCardPickupAnimations.shift();
  animateCardPickupToTicketPile(drawRequest, gainedColor);
}

function renderTicketPile() {
  ticketPileEl.innerHTML = "";
  for (const color of CARD_ORDER) {
    const count = ticketCounts[color] || 0;
    if (count <= 0) continue;
    const item = document.createElement("div");
    item.className = "ticket-item";
    item.dataset.color = color;
    const img = document.createElement("img");
    img.src = `/img/${color}.png`;
    img.alt = `${color} ticket`;
    item.appendChild(img);
    const badge = document.createElement("div");
    badge.className = "ticket-count";
    badge.textContent = String(count);
    item.appendChild(badge);
    item.appendChild(makeColorAssistTag(color));
    ticketPileEl.appendChild(item);
  }
}

function ticketResultById(ticketId) {
  return destinationTicketResults.find((r) => r.id === ticketId) || null;
}

function destinationTicketLabel(ticket) {
  if (!ticket || !currentMap || !currentMap.cities) return "Unknown route";
  const from = currentMap.cities[ticket.u]?.name || `City ${ticket.u + 1}`;
  const to = currentMap.cities[ticket.v]?.name || `City ${ticket.v + 1}`;
  return `${from} - ${to}`;
}

function renderDestinationTickets() {
  if (!destinationTicketsListEl) return;
  destinationTicketsListEl.innerHTML = "";
  if (!Array.isArray(destinationTickets) || destinationTickets.length === 0) {
    const empty = document.createElement("div");
    empty.className = "destination-ticket-empty";
    empty.textContent = "No destination tickets selected.";
    destinationTicketsListEl.appendChild(empty);
    return;
  }

  destinationTickets.forEach((ticket) => {
    const row = document.createElement("div");
    row.className = "destination-ticket-item";
    row.dataset.ticketId = ticket.id;
    const result = ticketResultById(ticket.id);
    if (result?.completed) {
      row.classList.add("completed");
    }

    const name = document.createElement("div");
    name.className = "destination-ticket-name";
    name.textContent = destinationTicketLabel(ticket);

    const points = document.createElement("div");
    points.className = "destination-ticket-points";
    points.textContent = `${ticket.points} pts`;

    row.appendChild(name);
    row.appendChild(points);
    row.addEventListener("mouseenter", () => {
      setHighlightedCities([ticket.u, ticket.v]);
    });
    row.addEventListener("mouseleave", () => {
      clearCityHighlights();
    });
    destinationTicketsListEl.appendChild(row);
  });
}

function renderTicketSelectionList() {
  if (!ticketSelectListEl) return;
  ticketSelectListEl.innerHTML = "";
  pendingDestinationOffer.forEach((ticket) => {
    const row = document.createElement("div");
    row.className = "destination-ticket-item";
    row.dataset.ticketId = ticket.id;
    const selected = selectedOfferTicketIds.has(ticket.id);
    if (!selected) row.classList.add("unselected");

    const name = document.createElement("div");
    name.className = "destination-ticket-name";
    name.textContent = destinationTicketLabel(ticket);

    const points = document.createElement("div");
    points.className = "destination-ticket-points";
    points.textContent = `${ticket.points} pts`;

    row.appendChild(name);
    row.appendChild(points);
    row.addEventListener("mouseenter", () => {
      setHighlightedCities([ticket.u, ticket.v]);
    });
    row.addEventListener("mouseleave", () => {
      clearCityHighlights();
    });
    row.addEventListener("click", (e) => {
      e.stopPropagation();
      if (selectedOfferTicketIds.has(ticket.id)) {
        selectedOfferTicketIds.delete(ticket.id);
      } else {
        selectedOfferTicketIds.add(ticket.id);
      }
      renderTicketSelectionList();
      updateTicketSelectionSubmit();
    });
    ticketSelectListEl.appendChild(row);
  });
}

function updateTicketSelectionSubmit() {
  if (!ticketSelectSubmitEl) return;
  ticketSelectSubmitEl.disabled = selectedOfferTicketIds.size < destinationTicketMinKeep;
}

function openTicketSelectModal(offer, minKeep) {
  if (!ticketSelectPanelEl) return;
  const nextOffer = Array.isArray(offer) ? offer.slice() : [];
  const prevIds = new Set((pendingDestinationOffer || []).map((ticket) => ticket.id));
  const nextIds = new Set(nextOffer.map((ticket) => ticket.id));
  const sameOffer =
    prevIds.size === nextIds.size &&
    [...prevIds].every((id) => nextIds.has(id));
  pendingDestinationOffer = nextOffer;
  destinationTicketMinKeep = Number.isFinite(minKeep) ? minKeep : 2;
  if (sameOffer && selectedOfferTicketIds.size > 0) {
    selectedOfferTicketIds = new Set(
      [...selectedOfferTicketIds].filter((id) => nextIds.has(id))
    );
  } else {
    selectedOfferTicketIds = new Set();
  }
  if (ticketSelectHintEl) {
    ticketSelectHintEl.textContent = `Keep at least ${destinationTicketMinKeep} tickets.`;
  }
  renderTicketSelectionList();
  updateTicketSelectionSubmit();
  ticketSelectPanelEl.classList.remove("hidden");
}

function canAffordTickets(tickets, routeColor, len) {
  const wild = tickets.rainbow || 0;
  if (routeColor === "gray") {
    const colors = CARD_ORDER.filter((c) => c !== "rainbow");
    return colors.some((c) => (tickets[c] || 0) + wild >= len);
  }
  const have = (tickets[routeColor] || 0) + wild;
  return have >= len;
}

function canAffordRoute(tickets, trainsRemaining, routeColor, len) {
  if ((trainsRemaining || 0) < len) return false;
  return canAffordTickets(tickets, routeColor, len);
}

function possibleColors(tickets, routeColor, len) {
  const wild = tickets.rainbow || 0;
  if (routeColor === "gray") {
    const colors = CARD_ORDER.filter((c) => c !== "rainbow");
    const nonWildTotal = colors.reduce((a, c) => a + (tickets[c] || 0), 0);
    if (nonWildTotal === 0 && wild >= len) return ["red"];
    const options = colors.filter((c) => {
      const base = tickets[c] || 0;
      if (base <= 0) return false;
      return base + wild >= len;
    });
    return options;
  }
  return (tickets[routeColor] || 0) + wild >= len ? [routeColor] : [];
}

function renderPlayers(players, currentTurn) {
  if (!playersListEl) return;
  playersListEl.innerHTML = "";
  players.forEach((p, idx) => {
    const row = document.createElement("div");
    row.className = `player${idx === currentTurn ? " active" : ""}${p.id === myPlayerId ? " you" : ""}`;

    const swatch = document.createElement("div");
    swatch.className = "player-swatch";
    applyPlayerSwatchAppearance(swatch, p);

    const info = document.createElement("div");
    info.className = "player-info";

    const name = document.createElement("div");
    name.className = "player-name";
    const score = p.score ?? 0;
    const trains = p.trains ?? 0;
    const youTag = p.id === myPlayerId ? " (You)" : "";
    name.textContent = `${p.name || p.color}${youTag}`;

    const points = document.createElement("div");
    points.className = "player-points";
    points.textContent = `${score} pts`;

    const trainsLine = document.createElement("div");
    trainsLine.className = "player-trains";
    trainsLine.textContent = `${trains} trains left`;

    const destinationCount = document.createElement("div");
    destinationCount.className = "player-destination-count";
    destinationCount.textContent = `${p.destinationTicketCount ?? 0} destination tickets`;

    const tickets = document.createElement("div");
    tickets.className = "player-tickets";
    const img = document.createElement("img");
    img.src = "/img/back.png";
    img.alt = "Tickets";
    const total = p.ticketTotal ?? 0;
    const count = document.createElement("span");
    count.textContent = String(total);

    tickets.appendChild(img);
    tickets.appendChild(count);
    info.appendChild(name);
    info.appendChild(points);
    info.appendChild(trainsLine);
    info.appendChild(destinationCount);
    info.appendChild(tickets);
    row.appendChild(swatch);
    row.appendChild(info);
    playersListEl.appendChild(row);
  });
}

function renderGameOver(state) {
  if (!gameOverModalEl || !standingsListEl || !gameOverSummaryEl) return;
  const standings = Array.isArray(state?.standings) ? state.standings : [];
  standingsListEl.innerHTML = "";
  standings.forEach((entry, idx) => {
    const row = document.createElement("div");
    row.className = "standing-row";

    const place = document.createElement("div");
    place.className = "standing-place";
    place.textContent = `#${idx + 1}`;

    const name = document.createElement("div");
    name.className = "standing-name";
    const youTag = entry.id === myPlayerId ? " (You)" : "";
    name.textContent = `${entry.name}${youTag}`;

    const score = document.createElement("div");
    score.className = "standing-score";
    score.textContent = `${entry.score || 0} pts`;

    const details = document.createElement("div");
    details.className = "standing-details";

    const routePoints = Number.isFinite(entry.routePoints) ? entry.routePoints : 0;
    const destinationPoints = Number.isFinite(entry.destinationPoints) ? entry.destinationPoints : 0;
    const globetrotterBonus = Number.isFinite(entry.globetrotterBonus) ? entry.globetrotterBonus : 0;
    const longestRoadBonus = Number.isFinite(entry.longestRoadBonus) ? entry.longestRoadBonus : 0;
    const longestRoadLength = Number.isFinite(entry.longestRoadLength) ? entry.longestRoadLength : 0;
    const bonusPoints = Number.isFinite(entry.bonusPoints)
      ? entry.bonusPoints
      : (globetrotterBonus + longestRoadBonus);
    const breakdown = document.createElement("div");
    breakdown.className = "standing-breakdown";
    const destinationSign = destinationPoints >= 0 ? "+" : "";
    const bonusSign = bonusPoints >= 0 ? "+" : "";
    breakdown.textContent = `Trains: ${routePoints} pts | Tickets: ${destinationSign}${destinationPoints} pts | Bonuses: ${bonusSign}${bonusPoints} pts`;
    details.appendChild(breakdown);
    const roadLength = document.createElement("div");
    roadLength.className = "standing-road-length";
    roadLength.textContent = `Longest road length: ${longestRoadLength}`;
    details.appendChild(roadLength);
    if (globetrotterBonus > 0) {
      const badge = document.createElement("div");
      badge.className = "standing-globetrotter";
      badge.textContent = `Received Globetrotter bonus (+${globetrotterBonus} pts)`;
      details.appendChild(badge);
    }
    if (longestRoadBonus > 0) {
      const badge = document.createElement("div");
      badge.className = "standing-longest-road";
      badge.textContent = `Received Longest Road bonus (+${longestRoadBonus} pts)`;
      details.appendChild(badge);
    }

    const ticketList = document.createElement("div");
    ticketList.className = "standing-ticket-list";
    const ticketEntries = Array.isArray(entry.destinationTickets) ? entry.destinationTickets : [];
    if (ticketEntries.length === 0) {
      const none = document.createElement("div");
      none.className = "standing-ticket-item";
      none.textContent = "No destination tickets";
      ticketList.appendChild(none);
    } else {
      ticketEntries.forEach((ticket) => {
        const item = document.createElement("div");
        item.className = `standing-ticket-item ${ticket.completed ? "completed" : "incomplete"}`;
        const ticketLabel = destinationTicketLabel(ticket);
        const prefix = ticket.completed ? "+" : "-";
        item.textContent = `${ticketLabel} (${prefix}${ticket.points} pts)`;
        ticketList.appendChild(item);
      });
    }
    details.appendChild(ticketList);

    row.appendChild(place);
    row.appendChild(name);
    row.appendChild(score);
    row.appendChild(details);
    standingsListEl.appendChild(row);
  });

  gameOverSummaryEl.textContent = "Final round complete.";
  showGameOverModal();
}

function applyState(state) {
  if (!state) return;
  const couldTakeTurnActions = canTakeTurnActions();
  const prevTicketCounts = { ...ticketCounts };
  const nextEdges = Array.isArray(state.edges) ? state.edges : [];
  const newlyClaimedEdgeIds = findNewlyClaimedEdgeIds(lastEdgeClaimsById, nextEdges);
  const nextFaceUp = Array.isArray(state.faceUp) ? state.faceUp.slice() : [];
  const hasServerFaceUpReplacementSignal = Number.isFinite(state.faceUpReplacementSeq);
  const nextFaceUpReplacementSeq = hasServerFaceUpReplacementSignal
    ? state.faceUpReplacementSeq
    : 0;
  const serverReplacementIndex = Number.isFinite(state.faceUpReplacementIndex)
    ? state.faceUpReplacementIndex
    : -1;
  let replacementIndex = -1;
  if (hasServerFaceUpReplacementSignal) {
    if (
      lastSeenFaceUpReplacementSeq !== null &&
      nextFaceUpReplacementSeq > lastSeenFaceUpReplacementSeq &&
      serverReplacementIndex >= 0 &&
      serverReplacementIndex < nextFaceUp.length
    ) {
      replacementIndex = serverReplacementIndex;
    }
  } else {
    replacementIndex = findFaceUpReplacementIndex(lastFaceUpCards, nextFaceUp);
  }

  gameStarted = true;
  setGameVisibility(true);

  turnDrawCount = state.turnDrawCount || 0;
  const you = state.you || {};
  amPlayer = !!you.isPlayer;
  isMyTurn = !!you.isTurn;
  myPlayerId = you.playerId || null;
  gameOver = !!state.gameOver;
  setupPhase = !!state.setupPhase;

  ticketCounts = { ...Object.fromEntries(CARD_ORDER.map((k) => [k, 0])), ...(state.tickets || {}) };
  currentMap = { cities: state.cities || [], edges: nextEdges };
  destinationTickets = Array.isArray(state.destinationTickets) ? state.destinationTickets.slice() : [];
  destinationTicketResults = Array.isArray(state.destinationTicketResults) ? state.destinationTicketResults.slice() : [];
  destinationSelectionPending = !!state.destinationSelectionPending;
  destinationTicketsRemaining = Number.isFinite(state.destinationTicketsRemaining)
    ? state.destinationTicketsRemaining
    : 0;
  destinationTicketMinKeep = Number.isFinite(state.destinationTicketMinKeep)
    ? state.destinationTicketMinKeep
    : 2;
  const destinationOffer = Array.isArray(state.destinationOffer) ? state.destinationOffer.slice() : [];
  const canTakeTurnActionsNow = canTakeTurnActions();
  if (!couldTakeTurnActions && canTakeTurnActionsNow) {
    playAudioSafe(turnNotificationAudio);
  }

  const players = (state.players || []).map((p, idx) => ({
    ...p,
    ticketTotal: (state.ticketTotals || [])[idx] || 0,
    destinationTicketCount: (state.destinationTicketCounts || [])[idx] || 0,
    score: (state.scores || [])[idx] || 0,
    trains: p.trains ?? 0,
  }));
  const myIdx = Number.isFinite(you.playerIndex) ? you.playerIndex : -1;
  myTrainsRemaining = myIdx >= 0 ? (players[myIdx]?.trains ?? 0) : 0;
  playersSnapshot = players;
  currentTurnSnapshot = state.currentTurn ?? 0;
  const shapeMappings = buildPlayerShapeMappings(playersSnapshot);
  playerShapeById = shapeMappings.byId;
  playerShapeByColor = shapeMappings.byColor;
  setChatMessages(Array.isArray(state.chatMessages) ? state.chatMessages : []);

  clearRouteBuildAnimations();
  render();
  animateClaimedRoutes(newlyClaimedEdgeIds);
  drawFaceUp(nextFaceUp, replacementIndex);
  lastFaceUpCards = nextFaceUp;
  lastSeenFaceUpReplacementSeq = hasServerFaceUpReplacementSignal ? nextFaceUpReplacementSeq : null;
  lastEdgeClaimsById = buildEdgeClaimsMap(nextEdges);
  renderTicketPile();
  maybeAnimatePendingCardPickup(prevTicketCounts, ticketCounts);
  renderDestinationTickets();

  const currentTurn = currentTurnSnapshot;
  renderPlayers(players, currentTurn);
  updateTurnStatus(
    players,
    currentTurn,
    !!state.finalRoundActive,
    state.finalRoundTriggeredBy,
    gameOver,
    setupPhase,
    destinationSelectionPending
  );

  if (deckBackEl) {
    const empty = (state.deckRemaining ?? 1) <= 0;
    if (!canTakeTurnActions()) {
      deckBackEl.classList.remove("disabled");
      deckBackEl.classList.remove("clickable");
    } else if (empty) {
      deckBackEl.classList.add("disabled");
      deckBackEl.classList.remove("clickable");
    } else {
      deckBackEl.classList.remove("disabled");
      deckBackEl.classList.add("clickable");
    }
  }

  if (!amPlayer || !isMyTurn || gameOver || turnDrawCount > 0) {
    closeColorModal();
  }

  if (destinationSelectionPending && amPlayer && destinationOffer.length > 0) {
    openTicketSelectModal(destinationOffer, destinationTicketMinKeep);
  } else {
    closeTicketSelectModal();
  }
  setInitialTicketSelectionFocus(!!(setupPhase && destinationSelectionPending && amPlayer && destinationOffer.length > 0));
  refreshDestinationControls();
  applyChatInputAccess();

  if (gameOver) {
    renderGameOver(state);
  } else {
    hideGameOverModal();
  }
  refreshEndGameControls();

  updateCardSizing();
}

function handleServerError(payload) {
  const text = payload?.message || "Server rejected that action.";
  if (!gameStarted) {
    setLobbyStatus(text);
  } else if (routeInfo) {
    routeInfo.textContent = text;
  }
}

function connectSocket() {
  if (!currentRoomName) {
    setLobbyStatus("Invalid room.");
    return;
  }
  const protocol = window.location.protocol === "https:" ? "wss" : "ws";
  ws = new WebSocket(`${protocol}://${window.location.host}?room=${encodeURIComponent(currentRoomName)}`);

  ws.addEventListener("open", () => {
    let storedToken = "";
    try {
      storedToken = String(window.localStorage.getItem(CLIENT_TOKEN_KEY) || "");
    } catch (err) {
      storedToken = "";
    }
    ws.send(JSON.stringify({ type: "auth", token: storedToken }));
  });

  ws.addEventListener("close", () => {
    setLobbyStatus("Disconnected from server.");
  });

  ws.addEventListener("message", (event) => {
    let msg = null;
    try {
      msg = JSON.parse(event.data);
    } catch (err) {
      return;
    }

    if (!msg || typeof msg.type !== "string") return;

    if (msg.type === "auth") {
      const token = String(msg?.payload?.token || "");
      if (token) {
        try {
          window.localStorage.setItem(CLIENT_TOKEN_KEY, token);
        } catch (err) {
          // ignore storage failures
        }
      }
      return;
    }

    if (msg.type === "lobby") {
      renderLobby(msg.payload || {});
      if (msg.payload && msg.payload.gameStarted) {
        setGameVisibility(true);
      } else {
        gameStarted = false;
        gameOver = false;
        setupPhase = false;
        isMyTurn = false;
        playersSnapshot = [];
        currentTurnSnapshot = 0;
        playerShapeById = new Map();
        playerShapeByColor = {};
        destinationTickets = [];
        destinationTicketResults = [];
        destinationTicketsRemaining = 0;
        setChatMessages([]);
        clearCityHighlights();
        hideGameOverModal();
        closeColorModal();
        closeTicketSelectModal();
        setInitialTicketSelectionFocus(false);
        lastFaceUpCards = [];
        lastSeenFaceUpReplacementSeq = null;
        lastEdgeClaimsById = null;
        clearFaceUpDealAnimation();
        clearRouteBuildAnimations();
        clearCardPickupAnimationState();
        renderDestinationTickets();
        refreshDestinationControls();
        applyChatInputAccess();
        refreshEndGameControls();
        setGameVisibility(false);
      }
      return;
    }

    if (msg.type === "state") {
      applyState(msg.payload);
      return;
    }

    if (msg.type === "log") {
      appendLog(msg.payload);
      return;
    }

    if (msg.type === "chat") {
      appendChatMessage(msg.payload);
      return;
    }

    if (msg.type === "error") {
      handleServerError(msg.payload);
    }
  });
}

function appendLog(entry) {
  if (!logListEl || !entry) return;
  if (entry.sfx === "ticket_select") {
    playAudioSafe(ticketSelectAudio);
  } else if (entry.sfx === "route_build") {
    playAudioSafe(routeBuildAudio);
  } else if (entry.sfx === "train_whistle") {
    playAudioSafe(trainWhistleAudio);
  } else if (entry.sfx === "destination_ticket_draw") {
    playAudioSafe(destinationTicketDrawAudio);
  }
  const item = document.createElement("div");
  item.className = "log-item";

  const text = document.createElement("span");
  text.textContent = entry.message || `${entry.playerName} took `;
  item.appendChild(text);

  if (entry.cards && Array.isArray(entry.cards) && entry.cards.length > 0) {
    const cardsWrap = document.createElement("span");
    cardsWrap.className = "log-cards";

    entry.cards.forEach((c) => {
      const img = document.createElement("img");
      img.src = `/img/${c}.png`;
      img.alt = `${c} card`;
      cardsWrap.appendChild(img);
    });

    if (entry.newline) {
      item.classList.add("log-item-stacked");
    }
    item.appendChild(cardsWrap);
  }

  logListEl.prepend(item);
}

lobbyJoinFormEl?.addEventListener("submit", (e) => {
  e.preventDefault();
  if (!ws || ws.readyState !== WebSocket.OPEN) return;
  if (!lobbyCanJoin) return;
  const name = (lobbyNameInputEl?.value || "").trim();
  if (!name) return;
  ws.send(JSON.stringify({ type: "join_lobby", name }));
});

lobbyNameInputEl?.addEventListener("input", () => {
  refreshLobbyControls();
});

lobbyStartBtnEl?.addEventListener("click", () => {
  if (!ws || ws.readyState !== WebSocket.OPEN) return;
  if (!lobbyCanStart) return;
  ws.send(JSON.stringify({ type: "start_game" }));
});

lobbyHowToPlayBtnEl?.addEventListener("click", () => {
  showHowToPlayModal();
});

howToPlayCloseBtnEl?.addEventListener("click", () => {
  hideHowToPlayModal();
});

howToPlayModalEl?.addEventListener("click", (e) => {
  if (e.target === howToPlayModalEl) {
    hideHowToPlayModal();
  }
});

document.addEventListener("keydown", (e) => {
  if (e.key === "Escape" && howToPlayModalEl && !howToPlayModalEl.classList.contains("hidden")) {
    hideHowToPlayModal();
    return;
  }
  if (e.key === "Escape" && gameOverModalEl && !gameOverModalEl.classList.contains("hidden")) {
    hideGameOverModal();
  }
});

gameOverModalEl?.addEventListener("click", (e) => {
  if (e.target === gameOverModalEl) {
    hideGameOverModal();
  }
});

chatToggleBtnEl?.addEventListener("click", () => {
  const collapsed = chatPanelEl?.classList.contains("collapsed");
  setChatCollapsed(!collapsed);
});

chatFormEl?.addEventListener("submit", (e) => {
  e.preventDefault();
  if (!ws || ws.readyState !== WebSocket.OPEN) return;
  if (!gameStarted || !amPlayer) return;
  const text = String(chatInputEl?.value || "").trim();
  if (!text) return;
  ws.send(JSON.stringify({ type: "chat_send", text }));
  if (chatInputEl) chatInputEl.value = "";
});

returnLobbyBtnEl?.addEventListener("click", () => {
  sendReturnToLobby();
});

sidebarReturnLobbyBtnEl?.addEventListener("click", () => {
  sendReturnToLobby();
});

viewResultsBtnEl?.addEventListener("click", () => {
  if (!gameOver) return;
  showGameOverModal();
});

gameOverCloseBtnEl?.addEventListener("click", () => {
  hideGameOverModal();
});

drawDestinationBtnEl?.addEventListener("click", () => {
  if (!canTakeNonDrawTurnActions()) return;
  if (destinationTicketsRemaining <= 0) return;
  if (!ws || ws.readyState !== WebSocket.OPEN) return;
  ws.send(JSON.stringify({ type: "draw_destination_tickets" }));
});

ticketSelectSubmitEl?.addEventListener("click", () => {
  if (!destinationSelectionPending) return;
  if (selectedOfferTicketIds.size < destinationTicketMinKeep) return;
  if (!ws || ws.readyState !== WebSocket.OPEN) return;
  ws.send(JSON.stringify({
    type: "select_tickets",
    keepTicketIds: [...selectedOfferTicketIds],
  }));
});

faceUpEl.addEventListener("click", (e) => {
  if (!canTakeTurnActions()) return;
  const target = e.target;
  if (!(target instanceof HTMLImageElement)) return;
  if (target.classList.contains("disabled")) return;
  const idx = Number(target.dataset.index);
  if (!Number.isFinite(idx)) return;
  if (ws && ws.readyState === WebSocket.OPEN) {
    queuePendingCardPickup(target, target.getAttribute("src") || `/img/${target.dataset.color || "back"}.png`);
    ws.send(JSON.stringify({ type: "draw_faceup", index: idx }));
  }
});

deckBackEl.addEventListener("click", () => {
  if (!canTakeTurnActions()) return;
  if (deckBackEl.classList.contains("disabled")) return;
  if (ws && ws.readyState === WebSocket.OPEN) {
    queuePendingCardPickup(deckBackEl, deckBackEl.getAttribute("src") || "/img/back.png");
    ws.send(JSON.stringify({ type: "draw_deck" }));
  }
});

function wireRoutes() {
  const routes = svg.querySelectorAll(".route-color, .route-hit");
  if (!canTakeNonDrawTurnActions()) return;

  function setClassForEdge(edgeId, cls, on) {
    if (!edgeId) return;
    const els = svg.querySelectorAll(`[data-edge-id="${edgeId}"]`);
    els.forEach((el) => el.classList.toggle(cls, on));
  }

  function clearAll(cls) {
    svg.querySelectorAll(`.${cls}`).forEach((el) => el.classList.remove(cls));
  }

  routes.forEach((el) => {
    if (el.dataset.claimed === "true") return;
    if (el.dataset.affordable !== "true") return;

    el.addEventListener("mouseenter", () => {
      const edgeId = el.dataset.edgeId;
      setClassForEdge(edgeId, "route-hover", true);
    });

    el.addEventListener("mouseleave", () => {
      const edgeId = el.dataset.edgeId;
      setClassForEdge(edgeId, "route-hover", false);
    });

    el.addEventListener("click", (e) => {
      clearAll("route-selected");
      const edgeId = el.dataset.edgeId;
      setClassForEdge(edgeId, "route-selected", true);
      selectedEdgeId = edgeId;
      selectedEdgeMeta = {
        edgeId,
        routeColor: el.dataset.routeColor || el.dataset.color,
        len: Number(el.dataset.len),
        claimed: el.dataset.claimed === "true",
        affordable: el.dataset.affordable === "true",
      };
      submitBtn.disabled = el.dataset.claimed === "true" || el.dataset.affordable !== "true";
      const from = el.dataset.from;
      const to = el.dataset.to;
      routeInfo.textContent = `${from} - ${to}`;
      e.stopPropagation();
    });
  });
}

svg.addEventListener("click", () => {
  svg.querySelectorAll(".route-selected").forEach((r) => r.classList.remove("route-selected"));
  routeInfo.textContent = idleRouteInfoText;
  selectedEdgeId = null;
  selectedEdgeMeta = null;
  submitBtn.disabled = true;
  clearCityHighlights();
});

submitBtn.addEventListener("click", () => {
  if (!canTakeNonDrawTurnActions()) return;
  if (!selectedEdgeMeta || !selectedEdgeMeta.affordable || selectedEdgeMeta.claimed) return;
  const colors = possibleColors(ticketCounts, selectedEdgeMeta.routeColor, selectedEdgeMeta.len);
  if (colors.length <= 0) return;
  if (colors.length === 1) {
    sendSubmitRoute(selectedEdgeMeta.edgeId, colors[0]);
    return;
  }
  openColorModal(colors);
});

function sendSubmitRoute(edgeId, color) {
  if (!canTakeNonDrawTurnActions()) return;
  if (ws && ws.readyState === WebSocket.OPEN) {
    ws.send(JSON.stringify({ type: "submit_route", edgeId, color }));
  }
}

function openColorModal(colors) {
  pendingColor = null;
  colorOptionsEl.innerHTML = "";
  colors.forEach((c) => {
    const opt = document.createElement("div");
    opt.className = "modal-option";
    opt.dataset.color = c;
    const img = document.createElement("img");
    img.src = `/img/${c}.png`;
    img.alt = `${c} ticket`;
    opt.appendChild(img);
    opt.appendChild(makeColorAssistTag(c));
    opt.addEventListener("click", () => {
      colorOptionsEl.querySelectorAll(".modal-option").forEach((el) => el.classList.remove("selected"));
      opt.classList.add("selected");
      pendingColor = c;
      colorSubmitEl.disabled = false;
    });
    colorOptionsEl.appendChild(opt);
  });
  colorSubmitEl.disabled = true;
  colorModalEl.classList.remove("hidden");
}

function closeColorModal() {
  pendingColor = null;
  colorModalEl.classList.add("hidden");
}

colorCancelEl.addEventListener("click", () => {
  closeColorModal();
});

colorSubmitEl.addEventListener("click", () => {
  if (!pendingColor || !selectedEdgeMeta) return;
  sendSubmitRoute(selectedEdgeMeta.edgeId, pendingColor);
  closeColorModal();
});

colorBlindToggleEl?.addEventListener("change", () => {
  applyColorBlindMode(!!colorBlindToggleEl.checked);
});

let storedColorBlindMode = false;
try {
  storedColorBlindMode = window.localStorage.getItem(COLORBLIND_MODE_KEY) === "1";
} catch (err) {
  storedColorBlindMode = false;
}
applyColorBlindMode(storedColorBlindMode);

setGameVisibility(false);
refreshLobbyControls();
renderDestinationTickets();
setChatCollapsed(false);
applyChatInputAccess();
renderChatMessages();
refreshDestinationControls();
refreshEndGameControls();
connectSocket();

if (typeof ResizeObserver !== "undefined") {
  const ro = new ResizeObserver(() => updateCardSizing());
  if (gameBox) ro.observe(gameBox);
  updateCardSizing();
} else {
  window.addEventListener("resize", updateCardSizing);
  updateCardSizing();
}

function updateCardSizing() {
  if (!gameBox || !stageInner) return;
  const rect = gameBox.getBoundingClientRect();
  const size = Math.max(110, Math.min(220, rect.width * 0.18));
  const gap = Math.max(12, Math.min(28, size * 0.14));
  stageInner.style.setProperty("--card-size", `${size.toFixed(1)}px`);
  stageInner.style.setProperty("--card-gap", `${gap.toFixed(1)}px`);
  const ticketGap = 10;
  const ticketSize = Math.max(48, Math.min(110, (rect.width - ticketGap * 8) / 9));
  stageInner.style.setProperty("--ticket-size", `${ticketSize.toFixed(1)}px`);
}
