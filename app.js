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
const returnLobbyBtnEl = document.getElementById("returnLobbyBtn");
const destinationTicketsListEl = document.getElementById("destinationTicketsList");
const drawDestinationBtnEl = document.getElementById("drawDestinationBtn");
const ticketSelectPanelEl = document.getElementById("ticketSelectPanel");
const ticketSelectHintEl = document.getElementById("ticketSelectHint");
const ticketSelectListEl = document.getElementById("ticketSelectList");
const ticketSelectSubmitEl = document.getElementById("ticketSelectSubmit");

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
let ws = null;
let turnDrawCount = 0;
let isMyTurn = false;
let amPlayer = false;
let myPlayerId = null;
let gameStarted = false;
let gameOver = false;
let lobbyCanJoin = false;
let lobbyCanStart = false;
const CLIENT_TOKEN_KEY = "ticket_to_ride_client_token";

function setGameVisibility(showGame) {
  if (gameWrapEl) gameWrapEl.classList.toggle("hidden", !showGame);
  if (lobbyScreenEl) lobbyScreenEl.classList.toggle("hidden", showGame);
}

function hideGameOverModal() {
  if (gameOverModalEl) gameOverModalEl.classList.add("hidden");
}

function closeTicketSelectModal() {
  if (ticketSelectPanelEl) ticketSelectPanelEl.classList.add("hidden");
  pendingDestinationOffer = [];
  selectedOfferTicketIds = new Set();
  clearCityHighlights();
}

function refreshDestinationControls() {
  if (!drawDestinationBtnEl) return;
  const canDraw = amPlayer &&
    isMyTurn &&
    !gameOver &&
    !setupPhase &&
    !destinationSelectionPending &&
    destinationTicketsRemaining > 0;
  drawDestinationBtnEl.disabled = !canDraw;
  drawDestinationBtnEl.textContent = destinationTicketsRemaining > 0
    ? `Draw destination tickets (${destinationTicketsRemaining})`
    : "Draw destination tickets";
}

function canTakeTurnActions() {
  return amPlayer && isMyTurn && !gameOver && !setupPhase && !destinationSelectionPending;
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
    interactive: canTakeTurnActions(),
  });
  wireRoutes();
  selectedEdgeId = null;
  selectedEdgeMeta = null;
  submitBtn.disabled = true;
  routeInfo.textContent = idleRouteInfoText;
}

function drawFaceUp(faceUp) {
  faceUpEl.innerHTML = "";
  for (let i = 0; i < faceUp.length; i++) {
    const name = faceUp[i];
    const img = document.createElement("img");
    img.className = "card";
    img.alt = `${name} card`;
    img.src = `img/${name}.png`;
    img.dataset.color = name;
    img.dataset.index = String(i);

    const canPick = canTakeTurnActions() && !(name === "rainbow" && turnDrawCount > 0);
    if (canPick) {
      img.classList.add("clickable");
    } else if (canTakeTurnActions() && name === "rainbow" && turnDrawCount > 0) {
      img.classList.add("disabled");
    }

    faceUpEl.appendChild(img);
  }
}

function renderTicketPile() {
  ticketPileEl.innerHTML = "";
  for (const color of CARD_ORDER) {
    const count = ticketCounts[color] || 0;
    if (count <= 0) continue;
    const item = document.createElement("div");
    item.className = "ticket-item";
    const img = document.createElement("img");
    img.src = `img/${color}.png`;
    img.alt = `${color} ticket`;
    item.appendChild(img);
    const badge = document.createElement("div");
    badge.className = "ticket-count";
    badge.textContent = String(count);
    item.appendChild(badge);
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
    const completion = result ? (result.completed ? " complete" : " incomplete") : "";

    const name = document.createElement("div");
    name.className = "destination-ticket-name";
    name.textContent = destinationTicketLabel(ticket) + completion;

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
    swatch.style.background = p.hex || p.color;

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
    img.src = "img/back.png";
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
    const breakdown = document.createElement("div");
    breakdown.className = "standing-breakdown";
    const destinationSign = destinationPoints >= 0 ? "+" : "";
    breakdown.textContent = `Trains: ${routePoints} pts | Tickets: ${destinationSign}${destinationPoints} pts`;
    details.appendChild(breakdown);

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
  gameOverModalEl.classList.remove("hidden");
}

function applyState(state) {
  if (!state) return;

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
  currentMap = { cities: state.cities || [], edges: state.edges || [] };
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

  const players = (state.players || []).map((p, idx) => ({
    ...p,
    ticketTotal: (state.ticketTotals || [])[idx] || 0,
    destinationTicketCount: (state.destinationTicketCounts || [])[idx] || 0,
    score: (state.scores || [])[idx] || 0,
    trains: p.trains ?? 0,
  }));
  const myIdx = Number.isFinite(you.playerIndex) ? you.playerIndex : -1;
  myTrainsRemaining = myIdx >= 0 ? (players[myIdx]?.trains ?? 0) : 0;

  render();
  drawFaceUp(state.faceUp || []);
  renderTicketPile();
  renderDestinationTickets();

  const currentTurn = state.currentTurn ?? 0;
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

  if (!amPlayer || !isMyTurn || gameOver) {
    closeColorModal();
  }

  if (destinationSelectionPending && amPlayer && destinationOffer.length > 0) {
    openTicketSelectModal(destinationOffer, destinationTicketMinKeep);
  } else {
    closeTicketSelectModal();
  }
  refreshDestinationControls();

  if (gameOver) {
    renderGameOver(state);
  } else {
    hideGameOverModal();
  }

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
  const protocol = window.location.protocol === "https:" ? "wss" : "ws";
  ws = new WebSocket(`${protocol}://${window.location.host}`);

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
        destinationTickets = [];
        destinationTicketResults = [];
        destinationTicketsRemaining = 0;
        clearCityHighlights();
        hideGameOverModal();
        closeColorModal();
        closeTicketSelectModal();
        renderDestinationTickets();
        refreshDestinationControls();
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

    if (msg.type === "error") {
      handleServerError(msg.payload);
    }
  });
}

function appendLog(entry) {
  if (!logListEl || !entry) return;
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
      img.src = `img/${c}.png`;
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

returnLobbyBtnEl?.addEventListener("click", () => {
  if (!ws || ws.readyState !== WebSocket.OPEN) return;
  ws.send(JSON.stringify({ type: "return_to_lobby" }));
});

drawDestinationBtnEl?.addEventListener("click", () => {
  if (!canTakeTurnActions()) return;
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
    ws.send(JSON.stringify({ type: "draw_faceup", index: idx }));
  }
});

deckBackEl.addEventListener("click", () => {
  if (!canTakeTurnActions()) return;
  if (deckBackEl.classList.contains("disabled")) return;
  if (ws && ws.readyState === WebSocket.OPEN) {
    ws.send(JSON.stringify({ type: "draw_deck" }));
  }
});

function wireRoutes() {
  const routes = svg.querySelectorAll(".route-color, .route-hit");
  if (!canTakeTurnActions()) return;

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
  if (!canTakeTurnActions()) return;
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
  if (!canTakeTurnActions()) return;
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
    img.src = `img/${c}.png`;
    img.alt = `${c} ticket`;
    opt.appendChild(img);
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

setGameVisibility(false);
refreshLobbyControls();
renderDestinationTickets();
refreshDestinationControls();
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
