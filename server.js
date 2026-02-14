const path = require("path");
const http = require("http");
const express = require("express");
const { WebSocketServer } = require("ws");
const Chance = require("chance");

const app = express();
const PORT = process.env.PORT || 3000;
const ROOM_NAME_REGEX = /^[A-Za-z0-9_-]{1,40}$/;

app.use(express.static(__dirname, { index: false }));

app.get("/", (req, res) => {
  res.sendFile(path.join(__dirname, "home.html"));
});

app.get("/api/rooms", (req, res) => {
  const roomList = [...rooms.values()]
    .filter((room) => room.socketClientIds.size > 0 || room.lobbyPlayers.length > 0 || room.gameStarted)
    .map((room) => ({
      name: room.name,
      players: room.lobbyPlayers.length,
      inGame: !!room.gameStarted,
    }))
    .sort((a, b) => a.name.localeCompare(b.name));
  res.json({ rooms: roomList });
});

app.get("/:roomName", (req, res) => {
  const normalized = sanitizeRoomName(req.params.roomName);
  if (!normalized) {
    res.redirect("/");
    return;
  }
  if (req.params.roomName !== normalized) {
    res.redirect(`/${normalized}`);
    return;
  }
  res.sendFile(path.join(__dirname, "index.html"));
});

const server = http.createServer(app);
const wss = new WebSocketServer({ server });
const chance = new Chance();

const DEFAULTS = {
  nCities: 35,
  eTarget: 70,
  kNN: 5,
  maxDeg: 6,
  pGray: 0.25,
  labels: true,
};

const ROUTE_COLORS = [
  { name: "red", hex: "#e74c3c" },
  { name: "blue", hex: "#3498db" },
  { name: "green", hex: "#2ecc71" },
  { name: "yellow", hex: "#f1c40f" },
  { name: "black", hex: "#2d3436" },
  { name: "white", hex: "#ecf0f1" },
  { name: "orange", hex: "#e67e22" },
  { name: "pink", hex: "#ff6fb1" },
];
const GRAY = { name: "gray", hex: "#95a5a6" };


const CARD_COUNTS = {
  red: 12,
  blue: 12,
  green: 12,
  yellow: 12,
  black: 12,
  white: 12,
  orange: 12,
  pink: 12,
  rainbow: 14,
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

const ROUTE_POINTS = {
  1: 1,
  2: 2,
  3: 4,
  4: 7,
  5: 10,
  6: 15,
};

const STARTING_TRAINS = 45;
const STARTING_TRAIN_CARDS = 4;
const FINAL_TURN_THRESHOLD = 2;
const DESTINATION_TICKET_COUNT = 30;
const DESTINATION_TICKET_OFFER_COUNT = 5;
const DESTINATION_TICKET_MIN_KEEP = 2;
const DESTINATION_TICKET_DRAW_COUNT = 3;
const DESTINATION_TICKET_DRAW_MIN_KEEP = 1;
const GLOBETROTTER_BONUS_POINTS = 10;
const LONGEST_ROAD_BONUS_POINTS = 15;
const CHAT_MAX_MESSAGE_LENGTH = 220;
const CHAT_HISTORY_LIMIT = 120;

const PLAYER_POOL = [
  { color: "red", hex: "#cc0000" },
  { color: "green", hex: "#008000" },
  { color: "blue", hex: "#0000cc" },
  { color: "yellow", hex: "#b58900" },
];

function rng() {
  return chance.floating({ min: 0, max: 1 });
}

function shuffleInPlace(rand, arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(rand() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}

function dist(a, b) {
  const dx = a.x - b.x, dy = a.y - b.y;
  return Math.hypot(dx, dy);
}

function clamp(x, lo, hi) { return Math.max(lo, Math.min(hi, x)); }
function lerp(a, b, t) { return a + (b - a) * t; }

function segIntersects(p1, p2, q1, q2) {
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

  if ((o1 > 0) !== (o2 > 0) && (o3 > 0) !== (o4 > 0)) return true;

  if (Math.abs(o1) < 1e-9 && onSegment(p1, p2, q1)) return true;
  if (Math.abs(o2) < 1e-9 && onSegment(p1, p2, q2)) return true;
  if (Math.abs(o3) < 1e-9 && onSegment(q1, q2, p1)) return true;
  if (Math.abs(o4) < 1e-9 && onSegment(q1, q2, p2)) return true;

  return false;
}

function keyEdge(a, b) { return a < b ? `${a}-${b}` : `${b}-${a}`; }

function normalizeEdgeId(edgeId) {
  const parts = edgeId.split("-").map((v) => Number(v));
  if (parts.length !== 2 || parts.some((n) => !Number.isFinite(n))) return null;
  return keyEdge(parts[0], parts[1]);
}

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

function generateCities(rand, N, bounds) {
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

    const x0 = xMin + w * rand();
    const y0 = yMin + h * rand();
    const p0 = { x: x0, y: y0 };
    points.push(p0);
    active.push(p0);
    const g0 = gridIndex(x0, y0);
    grid[g0.idx] = p0;

    const k = 30;
    while (active.length && points.length < targetCount) {
      const idx = Math.floor(rand() * active.length);
      const p = active[idx];
      let found = false;
      for (let i = 0; i < k; i++) {
        const ang = rand() * Math.PI * 2;
        const rad = minDist * (1 + rand());
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
  const edges = [...candidates].sort((a,b)=>a.d-b.d);
  const dsu = new DSU(cities.length);
  const mst = [];
  for (const e of edges) {
    if (dsu.union(e.u, e.v)) mst.push(e);
    if (mst.length === cities.length - 1) break;
  }
  return mst;
}

function addEdgesNoCrossing(rand, cities, mstEdges, candidates, eTarget, maxDeg) {
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

  for (const e of mstEdges) {
    if (canAdd(e)) {
      selected.push(e);
      selectedSet.add(keyEdge(e.u, e.v));
      deg[e.u]++; deg[e.v]++;
    }
  }

  const dsu = new DSU(cities.length);
  for (const e of selected) dsu.union(e.u, e.v);

  const pool = [...candidates].filter(e => !selectedSet.has(keyEdge(e.u, e.v)));
  shuffleInPlace(rand, pool);

  function scoreEdge(e) {
    const cycle = (dsu.find(e.u) === dsu.find(e.v)) ? 1 : 0;
    const lenPref = -Math.abs(e.d - 0.18);
    const degPref = -(deg[e.u] + deg[e.v]) * 0.08;
    return cycle * 2.0 + lenPref + degPref + (rand() * 0.05);
  }

  while (selected.length < eTarget && pool.length > 0) {
    const windowSize = Math.min(40, pool.length);
    let bestIdx = -1, bestScore = -1e9;
    for (let i = 0; i < windowSize; i++) {
      const e = pool[i];
      if (!canAdd(e)) continue;
      const sc = scoreEdge(e);
      if (sc > bestScore) { bestScore = sc; bestIdx = i; }
    }
    if (bestIdx === -1) {
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
    const len = 1 + Math.round(5 * t);
    e.len = clamp(len, 1, 6);
  }
}

function assignColors(rand, edges, pGray) {
  const load = new Map();
  for (const c of ROUTE_COLORS) load.set(c.name, 0);
  const usedByCity = new Map();
  function citySet(id) {
    if (!usedByCity.has(id)) usedByCity.set(id, new Set());
    return usedByCity.get(id);
  }

  const sorted = [...edges].sort((a,b)=>b.len-a.len);

  for (const e of sorted) {
    if (rand() < pGray) {
      e.color = GRAY;
      continue;
    }
    const ranked = [...ROUTE_COLORS].sort((a,b)=>load.get(a.name)-load.get(b.name));
    const forbid = new Set([...citySet(e.u), ...citySet(e.v)]);
    const allowed = ranked.filter(c => !forbid.has(c.name));
    const pool = (allowed.length ? allowed : ranked).slice(0, 3);
    const pick = pool[Math.floor(rand() * pool.length)];
    e.color = pick;
    load.set(pick.name, load.get(pick.name) + e.len);
    citySet(e.u).add(pick.name);
    citySet(e.v).add(pick.name);
  }
}

function pruneCollinearEdges(cities, edges, angleDeg = 160) {
  const edgeSet = new Set(edges.map(e => keyEdge(e.u, e.v)));
  const adj = Array.from({ length: cities.length }, () => []);
  for (const e of edges) {
    adj[e.u].push(e.v);
    adj[e.v].push(e.u);
  }

  function angleAt(a, b, c) {
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

        if (dAC >= Math.max(dAB, dBC) * 1.15) {
          toRemove.add(keyAC);
        }
      }
    }
  }

  if (toRemove.size === 0) return edges;
  return edges.filter(e => !toRemove.has(keyEdge(e.u, e.v)));
}

function generateMap(params) {
  const rand = rng;
  const N = params.nCities;
  const k = params.kNN;
  const eTarget = params.eTarget;
  const maxDeg = params.maxDeg;
  const pGray = params.pGray;

  const margin = 0.08;
  const bounds = { xMin: margin, xMax: 1 - margin, yMin: margin, yMax: 1 - margin };
  const cities = generateCities(rand, N, bounds);
  const candidates = buildCandidateEdges(cities, k);

  const mst = computeMST(cities, candidates);
  if (mst.length < N - 1) {
    const candidates2 = buildCandidateEdges(cities, Math.min(8, k + 2));
    const mst2 = computeMST(cities, candidates2);
    if (mst2.length < N - 1) throw new Error("Failed to build connected MST; try increasing kNN.");
    const res2 = addEdgesNoCrossing(rand, cities, mst2, candidates2, eTarget, maxDeg);
    const pruned2 = pruneCollinearEdges(cities, res2.edges, 160);
    assignLengths(pruned2);
    assignColors(rand, pruned2, pGray);
    return { cities, edges: pruned2 };
  }

  const res = addEdgesNoCrossing(rand, cities, mst, candidates, eTarget, maxDeg);
  const pruned = pruneCollinearEdges(cities, res.edges, 160);
  assignLengths(pruned);
  assignColors(rand, pruned, pGray);
  return { cities, edges: pruned };
}

function buildMapAdjacency(map) {
  const adj = Array.from({ length: map.cities.length }, () => []);
  for (const e of map.edges) {
    adj[e.u].push({ to: e.v, len: e.len });
    adj[e.v].push({ to: e.u, len: e.len });
  }
  return adj;
}

function shortestPathStatsByRoads(adj, source, target) {
  const n = adj.length;
  const bestRoads = Array(n).fill(Infinity);
  const bestLen = Array(n).fill(Infinity);
  const open = [{ node: source, roads: 0, len: 0 }];
  bestRoads[source] = 0;
  bestLen[source] = 0;

  while (open.length > 0) {
    open.sort((a, b) => a.roads - b.roads || a.len - b.len);
    const current = open.shift();
    if (!current) break;
    const { node, roads, len } = current;
    if (roads > bestRoads[node] || (roads === bestRoads[node] && len > bestLen[node])) {
      continue;
    }
    if (node === target) {
      return { roads, totalLength: len };
    }
    for (const next of adj[node]) {
      const nextRoads = roads + 1;
      const nextLen = len + next.len;
      if (nextRoads < bestRoads[next.to] || (nextRoads === bestRoads[next.to] && nextLen < bestLen[next.to])) {
        bestRoads[next.to] = nextRoads;
        bestLen[next.to] = nextLen;
        open.push({ node: next.to, roads: nextRoads, len: nextLen });
      }
    }
  }
  return null;
}

function assignDestinationTicketPoints(tickets) {
  if (tickets.length === 0) return tickets;
  if (tickets.length === 1) {
    tickets[0].points = 5;
    return tickets;
  }
  for (let i = 0; i < tickets.length; i++) {
    const points = 5 + Math.floor((i * 20) / (tickets.length - 1));
    tickets[i].points = clamp(points, 5, 25);
  }
  return tickets;
}

function generateDestinationTickets(map, count) {
  const adj = buildMapAdjacency(map);
  const candidates = [];

  for (let u = 0; u < map.cities.length; u++) {
    for (let v = u + 1; v < map.cities.length; v++) {
      const stats = shortestPathStatsByRoads(adj, u, v);
      if (!stats) continue;
      if (stats.roads < 2) continue;
      const difficulty = stats.roads * 1000 + stats.totalLength;
      candidates.push({
        u,
        v,
        minRoads: stats.roads,
        minPathLength: stats.totalLength,
        difficulty,
      });
    }
  }

  candidates.sort((a, b) =>
    a.difficulty - b.difficulty ||
    a.minRoads - b.minRoads ||
    a.minPathLength - b.minPathLength ||
    a.u - b.u ||
    a.v - b.v
  );

  if (candidates.length < count) {
    throw new Error('Not enough city pairs to generate destination tickets.');
  }

  const selected = [];
  const used = new Set();
  for (let i = 0; i < count; i++) {
    let idx = Math.round((i * (candidates.length - 1)) / (count - 1));
    while (used.has(idx) && idx < candidates.length - 1) idx += 1;
    while (used.has(idx) && idx > 0) idx -= 1;
    if (used.has(idx)) continue;
    used.add(idx);
    selected.push({ ...candidates[idx] });
  }
  if (selected.length < count) {
    for (let i = 0; i < candidates.length && selected.length < count; i++) {
      if (used.has(i)) continue;
      used.add(i);
      selected.push({ ...candidates[i] });
    }
  }

  selected.sort((a, b) =>
    a.difficulty - b.difficulty ||
    a.minRoads - b.minRoads ||
    a.minPathLength - b.minPathLength ||
    a.u - b.u ||
    a.v - b.v
  );
  assignDestinationTicketPoints(selected);

  return selected.map((t, idx) => ({
    id: `ticket-${idx + 1}`,
    u: t.u,
    v: t.v,
    minRoads: t.minRoads,
    minPathLength: t.minPathLength,
    difficulty: t.difficulty,
    points: t.points,
  }));
}

function buildDeck() {
  const deck = [];
  for (const [name, count] of Object.entries(CARD_COUNTS)) {
    for (let i = 0; i < count; i++) deck.push(name);
  }
  return deck;
}

function sanitizeName(value) {
  return String(value || '')
    .trim()
    .replace(/\s+/g, ' ')
    .slice(0, 24);
}

function sanitizeRoomName(value) {
  const room = String(value || '').trim().toLowerCase();
  if (!ROOM_NAME_REGEX.test(room)) return '';
  return room;
}

function sanitizeToken(value) {
  const token = String(value || '').trim();
  if (!token) return '';
  if (!/^[A-Za-z0-9_-]{8,128}$/.test(token)) return '';
  return token;
}

function sanitizeChatText(value) {
  return String(value || '')
    .replace(/\s+/g, ' ')
    .trim()
    .slice(0, CHAT_MAX_MESSAGE_LENGTH);
}

function pickRandom(arr) {
  if (!Array.isArray(arr) || arr.length === 0) return null;
  return arr[Math.floor(rng() * arr.length)] || null;
}

function initGame(players) {
  const map = generateMap(DEFAULTS);
  const destinationTickets = generateDestinationTickets(map, DESTINATION_TICKET_COUNT);
  const deck = buildDeck();
  shuffleInPlace(rng, deck);
  const ticketsByPlayer = players.map(() => Object.fromEntries(CARD_ORDER.map((k) => [k, 0])));
  let deckIndex = 0;
  for (let draw = 0; draw < STARTING_TRAIN_CARDS; draw++) {
    for (let p = 0; p < players.length; p++) {
      const card = deck[deckIndex++];
      if (!card) break;
      ticketsByPlayer[p][card] = (ticketsByPlayer[p][card] || 0) + 1;
    }
  }
  const faceUp = deck.slice(deckIndex, deckIndex + 5);
  deckIndex += faceUp.length;
  const destinationDeck = [...destinationTickets];
  shuffleInPlace(rng, destinationDeck);
  const destinationOffersByPlayer = players.map(() => destinationDeck.splice(0, DESTINATION_TICKET_OFFER_COUNT));
  const currentTurn = Math.floor(rng() * players.length);
  return {
    map,
    deck,
    deckIndex,
    faceUp,
    faceUpReplacementSeq: 0,
    faceUpReplacementIndex: -1,
    ticketsByPlayer,
    destinationTickets,
    destinationDeck,
    destinationOffersByPlayer,
    destinationTicketsByPlayer: players.map(() => []),
    destinationSelectionPendingByPlayer: players.map(() => true),
    destinationTicketMinKeepByPlayer: players.map(() => DESTINATION_TICKET_MIN_KEEP),
    destinationSelectionModeByPlayer: players.map(() => 'setup'),
    setupPhase: true,
    discard: [],
    players: players.map((p) => ({ ...p, connected: true, trains: STARTING_TRAINS })),
    currentTurn,
    turnDrawCount: 0,
    finalRoundActive: false,
    finalRoundTurnsRemaining: 0,
    finalRoundTriggeredBy: null,
    gameOver: false,
    standings: [],
    chatMessages: [],
  };
}

const rooms = new Map();
const wsRooms = new Map();
let lobbyPlayers = [];
let socketClientIds = new Map();
let socketsByClientId = new Map();
let game = null;
let gameStarted = false;

function getOrCreateRoomState(roomName) {
  if (!rooms.has(roomName)) {
    rooms.set(roomName, {
      name: roomName,
      lobbyPlayers: [],
      socketClientIds: new Map(),
      socketsByClientId: new Map(),
      game: null,
      gameStarted: false,
    });
  }
  return rooms.get(roomName);
}

function withRoomState(roomName, fn) {
  const state = getOrCreateRoomState(roomName);
  lobbyPlayers = state.lobbyPlayers;
  socketClientIds = state.socketClientIds;
  socketsByClientId = state.socketsByClientId;
  game = state.game;
  gameStarted = state.gameStarted;

  try {
    return fn(state);
  } finally {
    state.lobbyPlayers = lobbyPlayers;
    state.socketClientIds = socketClientIds;
    state.socketsByClientId = socketsByClientId;
    state.game = game;
    state.gameStarted = gameStarted;
    if (state.socketClientIds.size === 0 && state.lobbyPlayers.length === 0 && !state.gameStarted) {
      rooms.delete(roomName);
    }
  }
}

function addSocketBinding(clientId, ws) {
  if (!socketsByClientId.has(clientId)) {
    socketsByClientId.set(clientId, new Set());
  }
  socketsByClientId.get(clientId).add(ws);
}

function removeSocketBinding(clientId, ws) {
  const set = socketsByClientId.get(clientId);
  if (!set) return;
  set.delete(ws);
  if (set.size === 0) {
    socketsByClientId.delete(clientId);
  }
}

function bindSocketClientId(ws, clientId) {
  const prev = socketClientIds.get(ws);
  if (prev === clientId) return prev;
  if (prev) removeSocketBinding(prev, ws);
  socketClientIds.set(ws, clientId);
  addSocketBinding(clientId, ws);
  return prev;
}

function unbindSocket(ws) {
  const prev = socketClientIds.get(ws);
  if (!prev) return '';
  removeSocketBinding(prev, ws);
  socketClientIds.delete(ws);
  return prev;
}

function isClientConnected(clientId) {
  const set = socketsByClientId.get(clientId);
  return !!(set && set.size > 0);
}

function getLobbyPlayerIndex(clientId) {
  return lobbyPlayers.findIndex((p) => p.id === clientId);
}

function getPlayerIndexForClient(clientId) {
  if (!gameStarted || !game) return -1;
  return game.players.findIndex((p) => p.id === clientId);
}

function shouldShowGameForClient(clientId) {
  if (!gameStarted || !game) return false;
  if (!game.gameOver) {
    // Live games are visible to all connected clients, including spectators.
    return true;
  }
  if (getLobbyPlayerIndex(clientId) >= 0) return false;
  return getPlayerIndexForClient(clientId) >= 0;
}

function getPlayerIndexForSocket(ws) {
  const clientId = socketClientIds.get(ws);
  if (!clientId) return -1;
  return getPlayerIndexForClient(clientId);
}

function buildLobbyPayload(clientId) {
  const you = lobbyPlayers.find((p) => p.id === clientId) || null;
  const showGame = shouldShowGameForClient(clientId);
  return {
    players: lobbyPlayers.map((p) => ({
      id: p.id,
      name: p.name,
      color: p.color,
      hex: p.hex,
    })),
    minPlayers: 2,
    maxPlayers: PLAYER_POOL.length,
    canJoin: !showGame && !you && lobbyPlayers.length < PLAYER_POOL.length,
    canStart: !gameStarted && lobbyPlayers.length >= 2,
    gameStarted: showGame,
    activeGame: gameStarted,
    you,
  };
}

function sendLobby(ws) {
  const clientId = socketClientIds.get(ws);
  const payload = buildLobbyPayload(clientId);
  ws.send(JSON.stringify({ type: 'lobby', payload }));
}

function broadcastLobby() {
  socketClientIds.forEach((_, client) => {
    if (client.readyState !== 1) return;
    sendLobby(client);
  });
}

function sendError(ws, message) {
  ws.send(JSON.stringify({ type: 'error', payload: { message } }));
}

function addPlayerToLobby(player) {
  if (!player) return;
  if (getLobbyPlayerIndex(player.id) >= 0) return;
  if (lobbyPlayers.length >= PLAYER_POOL.length) return;
  lobbyPlayers.push({
    id: player.id,
    name: player.name,
    color: player.color,
    hex: player.hex,
  });
}

function maybeFinishGameAfterReturns() {
  if (!gameStarted || !game || !game.gameOver) return;
  const everyoneReturnedOrGone = game.players.every((p) => {
    if (!isClientConnected(p.id)) return true;
    return getLobbyPlayerIndex(p.id) >= 0;
  });
  if (!everyoneReturnedOrGone) return;
  game = null;
  gameStarted = false;
}

function maybeResetGameIfAllPlayersDisconnected() {
  if (!gameStarted || !game) return;
  const allPlayersDisconnected = game.players.every((p) => !isClientConnected(p.id));
  if (!allPlayersDisconnected) return;
  lobbyPlayers.splice(0, lobbyPlayers.length);
  game = null;
  gameStarted = false;
}

function startGame() {
  if (gameStarted) return;
  if (lobbyPlayers.length < 2) return;
  const startingPlayers = lobbyPlayers.slice();
  game = initGame(startingPlayers);
  lobbyPlayers.splice(0, lobbyPlayers.length);
  gameStarted = true;
  maybeResetFaceUp();
  broadcastLobby();
  broadcastState();
}

function buildClaimedAdjacencyForPlayer(playerColor) {
  if (!game) return [];
  const adj = Array.from({ length: game.map.cities.length }, () => []);
  for (const e of game.map.edges) {
    if (e.claimedBy !== playerColor) continue;
    adj[e.u].push(e.v);
    adj[e.v].push(e.u);
  }
  return adj;
}

function hasPathBetweenCities(adj, source, target) {
  if (source === target) return true;
  const seen = new Set([source]);
  const queue = [source];
  while (queue.length > 0) {
    const node = queue.shift();
    const nextList = adj[node] || [];
    for (const next of nextList) {
      if (seen.has(next)) continue;
      if (next === target) return true;
      seen.add(next);
      queue.push(next);
    }
  }
  return false;
}

function getDestinationTicketResultForPlayer(playerIdx, ticket, cachedAdj) {
  if (!game) return false;
  const player = game.players[playerIdx];
  if (!player || !ticket) return false;
  const adj = cachedAdj || buildClaimedAdjacencyForPlayer(player.color);
  return hasPathBetweenCities(adj, ticket.u, ticket.v);
}

function computeRouteScores() {
  if (!game) return [];
  return game.players.map((p) => {
    let total = 0;
    for (const e of game.map.edges) {
      if (e.claimedBy === p.color) {
        total += ROUTE_POINTS[e.len] || 0;
      }
    }
    return total;
  });
}

function buildDestinationTicketBreakdownForPlayer(playerIdx) {
  if (!game) return { pointsDelta: 0, tickets: [] };
  const tickets = game.destinationTicketsByPlayer[playerIdx] || [];
  if (tickets.length === 0) {
    return { pointsDelta: 0, tickets: [] };
  }
  const adj = buildClaimedAdjacencyForPlayer(game.players[playerIdx].color);
  let delta = 0;
  const detail = tickets.map((ticket) => {
    const completed = getDestinationTicketResultForPlayer(playerIdx, ticket, adj);
    delta += completed ? ticket.points : -ticket.points;
    return {
      id: ticket.id,
      u: ticket.u,
      v: ticket.v,
      points: ticket.points,
      completed,
    };
  });
  return { pointsDelta: delta, tickets: detail };
}

function computeLongestRoadLengthForPlayer(playerIdx) {
  if (!game) return 0;
  const player = game.players[playerIdx];
  if (!player) return 0;
  const claimedEdges = game.map.edges
    .filter((e) => e.claimedBy === player.color)
    .map((e) => ({ u: e.u, v: e.v, len: e.len }));
  if (claimedEdges.length === 0) return 0;

  const adj = Array.from({ length: game.map.cities.length }, () => []);
  claimedEdges.forEach((edge, edgeIdx) => {
    adj[edge.u].push({ edgeIdx, next: edge.v });
    adj[edge.v].push({ edgeIdx, next: edge.u });
  });

  const usedEdge = Array(claimedEdges.length).fill(false);
  let best = 0;

  function dfs(node, totalLen) {
    if (totalLen > best) best = totalLen;
    const nextList = adj[node] || [];
    for (const next of nextList) {
      const idx = next.edgeIdx;
      if (usedEdge[idx]) continue;
      usedEdge[idx] = true;
      dfs(next.next, totalLen + (claimedEdges[idx].len || 0));
      usedEdge[idx] = false;
    }
  }

  for (let node = 0; node < adj.length; node++) {
    dfs(node, 0);
  }

  return best;
}

function computeLongestRoadLengths() {
  if (!game) return [];
  return game.players.map((_, idx) => computeLongestRoadLengthForPlayer(idx));
}

function computeLongestRoadBonuses(longestRoadLengths) {
  if (!Array.isArray(longestRoadLengths) || longestRoadLengths.length === 0) return [];
  const maxRoad = Math.max(...longestRoadLengths);
  return longestRoadLengths.map((len) => (len === maxRoad ? LONGEST_ROAD_BONUS_POINTS : 0));
}

function computeGlobetrotterBonuses(destinationBreakdowns) {
  if (!Array.isArray(destinationBreakdowns) || destinationBreakdowns.length === 0) return [];
  const completedCounts = destinationBreakdowns.map((b) =>
    (b?.tickets || []).reduce((acc, t) => acc + (t.completed ? 1 : 0), 0)
  );
  const maxCompleted = Math.max(...completedCounts);
  return completedCounts.map((count) => (count === maxCompleted ? GLOBETROTTER_BONUS_POINTS : 0));
}

function computeScores(options = {}) {
  const includeDestinationTickets = !!options.includeDestinationTickets;
  if (!game) return [];
  const routeScores = computeRouteScores();
  if (!includeDestinationTickets) return routeScores;

  const destinationBreakdowns = game.players.map((_, idx) =>
    buildDestinationTicketBreakdownForPlayer(idx)
  );
  return routeScores.map((routeScore, idx) => routeScore + destinationBreakdowns[idx].pointsDelta);
}

function buildStandings(scores, routeScores, destinationBreakdowns, globetrotterBonuses, longestRoadBonuses, longestRoadLengths) {
  if (!game) return [];
  return game.players
    .map((p, idx) => ({
      id: p.id,
      name: p.name,
      color: p.color,
      hex: p.hex,
      score: scores[idx] || 0,
      routePoints: routeScores ? (routeScores[idx] || 0) : 0,
      destinationPoints: destinationBreakdowns ? (destinationBreakdowns[idx]?.pointsDelta || 0) : 0,
      destinationTickets: destinationBreakdowns ? (destinationBreakdowns[idx]?.tickets || []) : [],
      globetrotterBonus: globetrotterBonuses ? (globetrotterBonuses[idx] || 0) : 0,
      longestRoadBonus: longestRoadBonuses ? (longestRoadBonuses[idx] || 0) : 0,
      longestRoadLength: longestRoadLengths ? (longestRoadLengths[idx] || 0) : 0,
      bonusPoints: (globetrotterBonuses ? (globetrotterBonuses[idx] || 0) : 0) +
        (longestRoadBonuses ? (longestRoadBonuses[idx] || 0) : 0),
    }))
    .sort((a, b) => b.score - a.score || a.name.localeCompare(b.name));
}

function endGame() {
  if (!game || game.gameOver) return;
  game.gameOver = true;
  game.turnDrawCount = 0;
  const routeScores = computeRouteScores();
  const destinationBreakdowns = game.players.map((_, idx) =>
    buildDestinationTicketBreakdownForPlayer(idx)
  );
  const globetrotterBonuses = computeGlobetrotterBonuses(destinationBreakdowns);
  const longestRoadLengths = computeLongestRoadLengths();
  const longestRoadBonuses = computeLongestRoadBonuses(longestRoadLengths);
  const scores = routeScores.map(
    (routeScore, idx) => routeScore +
      destinationBreakdowns[idx].pointsDelta +
      globetrotterBonuses[idx] +
      longestRoadBonuses[idx]
  );
  game.standings = buildStandings(
    scores,
    routeScores,
    destinationBreakdowns,
    globetrotterBonuses,
    longestRoadBonuses,
    longestRoadLengths
  );
}

function broadcastGameOverSummaryLog() {
  if (!game || !game.gameOver) return;
  const standings = Array.isArray(game.standings) ? game.standings : [];
  if (standings.length === 0) {
    broadcastLog({ message: 'Game over. Final standings are now available.' });
    return;
  }
  const topScore = Number(standings[0]?.score || 0);
  const winners = standings
    .filter((entry) => Number(entry?.score || 0) === topScore)
    .map((entry) => entry.name)
    .filter((name) => !!name);
  broadcastLog({ message: 'Game over. Final standings are now available.' });
  if (winners.length === 1) {
    broadcastLog({ message: `Winner: ${winners[0]} (${topScore} pts).` });
  } else if (winners.length > 1) {
    broadcastLog({ message: `Winners: ${winners.join(', ')} (${topScore} pts).` });
  }
}

function triggerFinalRound(triggerIdx) {
  if (!game || game.finalRoundActive) return;
  game.finalRoundActive = true;
  game.finalRoundTurnsRemaining = game.players.length;
  game.finalRoundTriggeredBy = game.players[triggerIdx]?.id || null;
}

function advanceTurn(options = {}) {
  const tickFinalRound = options.tickFinalRound !== false;
  if (!game) return;
  game.turnDrawCount = 0;
  if (game.gameOver) return;
  const nextTurn = (game.currentTurn + 1) % game.players.length;
  if (game.finalRoundActive && tickFinalRound) {
    game.finalRoundTurnsRemaining = Math.max(0, (game.finalRoundTurnsRemaining || 0) - 1);
    if (game.finalRoundTurnsRemaining <= 0) {
      endGame();
      return;
    }
  }
  game.currentTurn = nextTurn;
}

function canAffordTickets(tickets, routeColor, len) {
  const wild = tickets.rainbow || 0;
  if (routeColor === 'gray') {
    const colors = CARD_ORDER.filter((c) => c !== 'rainbow');
    return colors.some((c) => (tickets[c] || 0) + wild >= len);
  }
  const have = (tickets[routeColor] || 0) + wild;
  return have >= len;
}

function reshuffleIfNeeded() {
  if (!game) return;
  if (game.deckIndex < game.deck.length) return;
  if (game.discard.length === 0) return;
  game.deck = [...game.discard];
  game.discard = [];
  shuffleInPlace(rng, game.deck);
  game.deckIndex = 0;
}

function drawFromDeck() {
  if (!game) return null;
  if (game.deckIndex >= game.deck.length) {
    reshuffleIfNeeded();
  }
  if (game.deckIndex >= game.deck.length) return null;
  return game.deck[game.deckIndex++];
}

function maybeResetFaceUp() {
  if (!game) return false;
  const rainbowCount = game.faceUp.filter((c) => c === 'rainbow').length;
  const remaining = game.deck.length - game.deckIndex;
  if (rainbowCount < 3 || remaining < 5) return false;
  for (const c of game.faceUp) game.discard.push(c);
  const newFaceUp = [];
  for (let i = 0; i < 5; i++) {
    const next = drawFromDeck();
    if (!next) break;
    newFaceUp.push(next);
  }
  game.faceUp = newFaceUp;
  game.faceUpReplacementIndex = -1;
  broadcastLog({
    message: 'Face-up cards were cleared and refilled.',
    sfx: 'train_whistle',
  });
  maybeResetFaceUp();
  return true;
}

function drawDestinationOffer(count) {
  if (!game) return [];
  const drawCount = Math.max(0, Math.min(count, game.destinationDeck.length));
  if (drawCount <= 0) return [];
  return game.destinationDeck.splice(0, drawCount);
}

function spendTickets(playerIdx, color, len) {
  if (!game) return false;
  const pile = game.ticketsByPlayer[playerIdx];
  const wild = pile.rainbow || 0;
  const base = pile[color] || 0;
  const useColor = Math.min(base, len);
  const useWild = len - useColor;
  if (useWild > wild) return false;
  pile[color] = base - useColor;
  pile.rainbow = wild - useWild;
  for (let i = 0; i < useColor; i++) game.discard.push(color);
  for (let i = 0; i < useWild; i++) game.discard.push('rainbow');
  return true;
}

function getStateForClient(clientId) {
  if (!gameStarted || !game) return null;
  const playerIdx = getPlayerIndexForClient(clientId);
  const ticketTotals = game.ticketsByPlayer.map((counts) =>
    Object.values(counts).reduce((a, b) => a + b, 0)
  );
  const destinationTicketCounts = game.destinationTicketsByPlayer.map((tickets) => tickets.length);
  const scores = game.gameOver
    ? game.players.map((p) => {
        const standing = (game.standings || []).find((s) => s.id === p.id);
        return standing ? standing.score : 0;
      })
    : computeScores({ includeDestinationTickets: false });
  const deckRemaining = Math.max(0, (game.deck.length - game.deckIndex) + game.discard.length);
  const finalRoundTriggeredByPlayer = game.players.find((p) => p.id === game.finalRoundTriggeredBy) || null;
  const destinationTickets = playerIdx >= 0 ? (game.destinationTicketsByPlayer[playerIdx] || []) : [];
  const destinationOffer = playerIdx >= 0 ? (game.destinationOffersByPlayer[playerIdx] || []) : [];
  const destinationSelectionPending = playerIdx >= 0
    ? !!game.destinationSelectionPendingByPlayer[playerIdx]
    : false;
  const destinationTicketMinKeep = playerIdx >= 0
    ? (game.destinationTicketMinKeepByPlayer[playerIdx] || DESTINATION_TICKET_MIN_KEEP)
    : DESTINATION_TICKET_MIN_KEEP;
  const destinationTicketResults = playerIdx >= 0
    ? destinationTickets.map((ticket) => ({
        id: ticket.id,
        completed: getDestinationTicketResultForPlayer(playerIdx, ticket),
      }))
    : [];
  return {
    cities: game.map.cities,
    edges: game.map.edges,
    faceUp: game.faceUp,
    faceUpReplacementSeq: game.faceUpReplacementSeq || 0,
    faceUpReplacementIndex: Number.isFinite(game.faceUpReplacementIndex) ? game.faceUpReplacementIndex : -1,
    tickets: playerIdx >= 0 ? (game.ticketsByPlayer[playerIdx] || {}) : {},
    ticketTotals,
    destinationTicketCounts,
    discardCount: game.discard.length,
    deckRemaining,
    scores,
    players: game.players,
    currentTurn: game.currentTurn,
    turnDrawCount: game.turnDrawCount,
    gameOver: game.gameOver,
    finalRoundActive: game.finalRoundActive,
    finalRoundTriggeredBy: finalRoundTriggeredByPlayer ? finalRoundTriggeredByPlayer.name : null,
    standings: game.standings || [],
    setupPhase: !!game.setupPhase,
    destinationTickets,
    destinationOffer: destinationSelectionPending ? destinationOffer : [],
    destinationSelectionPending,
    destinationTicketMinKeep,
    destinationTicketsRemaining: game.destinationDeck.length,
    destinationTicketResults,
    chatMessages: game.chatMessages || [],
    you: {
      isPlayer: playerIdx >= 0,
      isTurn: !game.gameOver && !game.setupPhase && playerIdx >= 0 && playerIdx === game.currentTurn,
      playerIndex: playerIdx,
      playerId: playerIdx >= 0 ? game.players[playerIdx].id : null,
      name: playerIdx >= 0 ? game.players[playerIdx].name : null,
      color: playerIdx >= 0 ? game.players[playerIdx].color : null,
    },
  };
}

function sendState(ws) {
  const clientId = socketClientIds.get(ws);
  if (!clientId) return;
  if (!shouldShowGameForClient(clientId)) return;
  const payload = getStateForClient(clientId);
  if (!payload) return;
  ws.send(JSON.stringify({ type: 'state', payload }));
}

function broadcastState() {
  socketClientIds.forEach((_, client) => {
    if (client.readyState !== 1) return;
    sendState(client);
  });
}

function broadcastChat(payload) {
  const msg = JSON.stringify({
    type: 'chat',
    payload: {
      ...payload,
      ts: payload?.ts || Date.now(),
    },
  });
  socketClientIds.forEach((clientId, client) => {
    if (client.readyState !== 1) return;
    if (!clientId || !shouldShowGameForClient(clientId)) return;
    client.send(msg);
  });
}

function broadcastLog(payload) {
  const msg = JSON.stringify({
    type: 'log',
    payload: {
      ...payload,
      ts: Date.now(),
    },
  });
  socketClientIds.forEach((_, client) => {
    if (client.readyState === 1) client.send(msg);
  });
}

function ticketsUsedForClaim(playerIdx, color, len) {
  if (!game) return [];
  const pile = game.ticketsByPlayer[playerIdx];
  const wild = pile.rainbow || 0;
  const base = pile[color] || 0;
  const useColor = Math.min(base, len);
  const useWild = len - useColor;
  const used = [];
  for (let i = 0; i < useColor; i++) used.push(color);
  for (let i = 0; i < useWild; i++) used.push('rainbow');
  return used;
}

wss.on('connection', (ws, req) => {
  const host = req?.headers?.host || 'localhost';
  let roomName = '';
  try {
    const reqUrl = new URL(req?.url || '/', `http://${host}`);
    roomName = sanitizeRoomName(reqUrl.searchParams.get('room'));
  } catch (err) {
    roomName = '';
  }
  if (!roomName) {
    sendError(ws, 'Missing or invalid room name.');
    ws.close();
    return;
  }

  wsRooms.set(ws, roomName);

  withRoomState(roomName, () => {
    const clientId = chance.guid();
    bindSocketClientId(ws, clientId);
    ws.send(JSON.stringify({ type: 'auth', payload: { token: clientId } }));
    sendLobby(ws);
    sendState(ws);
  });

  ws.on('message', (data) => {
    withRoomState(roomName, () => {
      let msg = null;
      try {
        msg = JSON.parse(data.toString());
      } catch (err) {
        return;
      }

      if (!msg || typeof msg.type !== 'string') return;

      if (msg.type === 'auth') {
      const requested = sanitizeToken(msg.token);
      const nextClientId = requested || chance.guid();
      const currentClientId = socketClientIds.get(ws) || '';
      const wasDifferent = nextClientId !== currentClientId;
      bindSocketClientId(ws, nextClientId);
      ws.send(JSON.stringify({ type: 'auth', payload: { token: nextClientId } }));

      if (gameStarted && game) {
        const playerIdx = getPlayerIndexForClient(nextClientId);
        if (playerIdx >= 0 && game.players[playerIdx].connected === false) {
          game.players[playerIdx].connected = true;
          broadcastLog({
            playerName: game.players[playerIdx].name,
            message: game.players[playerIdx].name + ' reconnected.',
          });
        } else if (playerIdx >= 0 && wasDifferent && !isClientConnected(currentClientId)) {
          game.players[playerIdx].connected = true;
        }
      }

        sendLobby(ws);
        sendState(ws);
        return;
      }

      if (msg.type === 'join_lobby') {
      const boundClientId = socketClientIds.get(ws) || '';
      if (lobbyPlayers.length >= PLAYER_POOL.length) {
        sendError(ws, 'Lobby is full.');
        return;
      }
      if (shouldShowGameForClient(boundClientId)) {
        sendError(ws, 'Finish or return from your game first.');
        return;
      }
      if (getLobbyPlayerIndex(boundClientId) >= 0) {
        sendError(ws, 'You already joined the lobby.');
        return;
      }
      const name = sanitizeName(msg.name);
      if (!name) {
        sendError(ws, 'Please enter a valid name.');
        return;
      }
      const usedColors = new Set(lobbyPlayers.map((p) => p.color));
      const available = PLAYER_POOL.filter((p) => !usedColors.has(p.color));
      const chosen = pickRandom(available);
      if (!chosen) {
        sendError(ws, 'No player colors remain.');
        return;
      }
      lobbyPlayers.push({
        id: boundClientId,
        name,
        color: chosen.color,
        hex: chosen.hex,
      });
      broadcastLobby();
        return;
      }

      if (msg.type === 'start_game') {
      if (gameStarted) {
        sendError(ws, 'Game already started.');
        return;
      }
      if (lobbyPlayers.length < 2) {
        sendError(ws, 'Need at least 2 players to start.');
        return;
      }
        startGame();
        return;
      }

      if (msg.type === 'return_to_lobby') {
      if (!gameStarted || !game || !game.gameOver) return;
      const boundClientId = socketClientIds.get(ws) || '';
      const playerIdx = getPlayerIndexForClient(boundClientId);
      if (playerIdx < 0) return;
      addPlayerToLobby(game.players[playerIdx]);
      maybeFinishGameAfterReturns();
      broadcastLobby();
        return;
      }

      if (!gameStarted || !game) return;

      const playerIdx = getPlayerIndexForSocket(ws);
      if (playerIdx < 0) return;
      if (msg.type === 'chat_send') {
      const text = sanitizeChatText(msg.text);
      if (!text) return;
      const player = game.players[playerIdx];
      if (!player) return;
      const chatMessage = {
        id: chance.guid(),
        playerId: player.id,
        playerName: player.name,
        playerColor: player.color,
        playerHex: player.hex,
        text,
        ts: Date.now(),
      };
      game.chatMessages.push(chatMessage);
      if (game.chatMessages.length > CHAT_HISTORY_LIMIT) {
        game.chatMessages = game.chatMessages.slice(game.chatMessages.length - CHAT_HISTORY_LIMIT);
      }
      broadcastChat(chatMessage);
        return;
      }
      if (msg.type === 'select_tickets') {
      const offer = game.destinationOffersByPlayer[playerIdx] || [];
      const selectionMode = game.destinationSelectionModeByPlayer[playerIdx] || 'setup';
      const minKeep = game.destinationTicketMinKeepByPlayer[playerIdx] || DESTINATION_TICKET_MIN_KEEP;
      if (!game.destinationSelectionPendingByPlayer[playerIdx]) {
        sendError(ws, 'You already selected destination tickets.');
        return;
      }
      if (offer.length <= 0) {
        sendError(ws, 'No destination tickets available to choose.');
        return;
      }
      const keepIdsRaw = Array.isArray(msg.keepTicketIds) ? msg.keepTicketIds : [];
      const keepIds = [...new Set(keepIdsRaw.map((v) => String(v || '')))].filter((v) => v);
      if (keepIds.length < minKeep || keepIds.length > offer.length) {
        sendError(ws, `Keep between ${minKeep} and ${offer.length} tickets.`);
        return;
      }
      const offerById = new Map(offer.map((ticket) => [ticket.id, ticket]));
      const kept = [];
      for (const id of keepIds) {
        const ticket = offerById.get(id);
        if (!ticket) {
          sendError(ws, 'Invalid destination ticket selection.');
          return;
        }
        kept.push(ticket);
      }
      const returned = offer.filter((ticket) => !keepIds.includes(ticket.id));
      if (returned.length > 0) {
        game.destinationDeck.push(...returned);
      }
      if (selectionMode === 'draw') {
        game.destinationTicketsByPlayer[playerIdx] = [
          ...(game.destinationTicketsByPlayer[playerIdx] || []),
          ...kept,
        ];
      } else {
        game.destinationTicketsByPlayer[playerIdx] = kept;
      }
      game.destinationOffersByPlayer[playerIdx] = [];
      game.destinationSelectionPendingByPlayer[playerIdx] = false;
      game.destinationTicketMinKeepByPlayer[playerIdx] = 0;
      game.destinationSelectionModeByPlayer[playerIdx] = '';

      broadcastLog({
        playerName: game.players[playerIdx].name,
        message: game.players[playerIdx].name + ' chose ' + kept.length + ' destination tickets.',
      });

      if (selectionMode === 'draw') {
        advanceTurn();
        if (game.gameOver) {
          broadcastGameOverSummaryLog();
        }
      } else if (game.destinationSelectionPendingByPlayer.every((pending) => !pending)) {
        game.setupPhase = false;
        broadcastLog({
          message: 'All players chose destination tickets. The game has begun.',
        });
      }
      broadcastState();
        return;
      }
      if (game.gameOver) return;
      if (game.destinationSelectionPendingByPlayer[playerIdx]) {
      sendError(ws, 'Choose your destination tickets first.');
        return;
      }
      if (game.setupPhase) {
      sendError(ws, 'Waiting for other players to choose destination tickets.');
        return;
      }
      if (playerIdx !== game.currentTurn) return;

      if (msg.type === 'draw_destination_tickets') {
      if (game.destinationSelectionPendingByPlayer[playerIdx]) {
        sendError(ws, 'Choose your destination tickets first.');
        return;
      }
      const offer = drawDestinationOffer(DESTINATION_TICKET_DRAW_COUNT);
      if (offer.length <= 0) {
        sendError(ws, 'No destination tickets remain.');
        return;
      }
      game.destinationOffersByPlayer[playerIdx] = offer;
      game.destinationSelectionPendingByPlayer[playerIdx] = true;
      game.destinationTicketMinKeepByPlayer[playerIdx] = DESTINATION_TICKET_DRAW_MIN_KEEP;
      game.destinationSelectionModeByPlayer[playerIdx] = 'draw';
      broadcastLog({
        playerName: game.players[playerIdx].name,
        message: game.players[playerIdx].name + ' drew destination tickets.',
        sfx: 'destination_ticket_draw',
      });
      broadcastState();
        return;
      }

      if (msg.type === 'draw_faceup') {
      const idx = Number(msg.index);
      if (!Number.isFinite(idx)) return;
      if (idx < 0 || idx >= game.faceUp.length) return;
      const color = game.faceUp[idx];
      if (!color) return;
      if (game.turnDrawCount >= 2) return;
      if (color === 'rainbow' && game.turnDrawCount > 0) return;
      const p = playerIdx;
      game.ticketsByPlayer[p][color] = (game.ticketsByPlayer[p][color] || 0) + 1;
      const next = drawFromDeck();
      if (next) {
        game.faceUp[idx] = next;
      } else {
        game.faceUp.splice(idx, 1);
      }
      const faceUpWasReset = maybeResetFaceUp();
      if (next && !faceUpWasReset) {
        game.faceUpReplacementSeq = (game.faceUpReplacementSeq || 0) + 1;
        game.faceUpReplacementIndex = idx;
      } else {
        game.faceUpReplacementIndex = -1;
      }
      if (color === 'rainbow') {
        advanceTurn();
      } else {
        game.turnDrawCount += 1;
        if (game.turnDrawCount >= 2) advanceTurn();
      }
      broadcastLog({
        playerName: game.players[p].name,
        message: game.players[p].name + ' took ',
        cards: [color],
        faceDown: false,
        sfx: 'ticket_select',
      });
      if (game.gameOver) {
        broadcastGameOverSummaryLog();
      }
      broadcastState();
        return;
      }

      if (msg.type === 'draw_deck') {
      const color = drawFromDeck();
      if (!color) return;
      if (game.turnDrawCount >= 2) return;
      const p = playerIdx;
      game.ticketsByPlayer[p][color] = (game.ticketsByPlayer[p][color] || 0) + 1;
      game.turnDrawCount += 1;
      if (game.turnDrawCount >= 2) advanceTurn();
      maybeResetFaceUp();
      broadcastLog({
        playerName: game.players[p].name,
        message: game.players[p].name + ' took ',
        cards: ['back'],
        faceDown: true,
        sfx: 'ticket_select',
      });
      if (game.gameOver) {
        broadcastGameOverSummaryLog();
      }
      broadcastState();
        return;
      }

      if (msg.type === 'submit_route') {
      const rawEdgeId = String(msg.edgeId || '');
      const chosen = String(msg.color || '');
      const edgeId = normalizeEdgeId(rawEdgeId);
      console.log('[claim] request edge=' + rawEdgeId + ' color=' + chosen + ' player=' + game.players[playerIdx].name);
      if (!edgeId) {
        console.log('[claim] rejected: missing edgeId');
        sendError(ws, 'Invalid route selection.');
        return;
      }
      const edge = game.map.edges.find((e) => keyEdge(e.u, e.v) === edgeId);
      if (!edge) {
        console.log('[claim] rejected: edge not found');
        sendError(ws, 'Route not found.');
        return;
      }
      if (edge.claimedBy) {
        console.log('[claim] rejected: already claimed');
        sendError(ws, 'That route has already been claimed.');
        return;
      }
      const p = playerIdx;
      if (!CARD_ORDER.includes(chosen) || chosen === 'rainbow') {
        console.log('[claim] rejected: invalid chosen color');
        sendError(ws, 'Invalid color selection.');
        return;
      }
      if (edge.color.name !== 'gray' && chosen !== edge.color.name) {
        console.log('[claim] rejected: color mismatch');
        sendError(ws, 'That route requires a different color.');
        return;
      }
      if (edge.color.name === 'gray' && !chosen) {
        console.log('[claim] rejected: missing color for gray route');
        sendError(ws, 'Choose a color for gray routes.');
        return;
      }
      if ((game.players[p].trains || 0) < edge.len) {
        console.log('[claim] rejected: insufficient trains');
        sendError(ws, 'Not enough trains for that route.');
        return;
      }
      const canClaim = canAffordTickets(game.ticketsByPlayer[p], chosen, edge.len);
      if (!canClaim) {
        console.log('[claim] rejected: insufficient tickets');
        sendError(ws, 'Not enough cards for that route.');
        return;
      }
      const used = ticketsUsedForClaim(p, chosen, edge.len);
      if (!spendTickets(p, chosen, edge.len)) {
        console.log('[claim] rejected: spend failed');
        sendError(ws, 'Could not spend cards for that route.');
        return;
      }
      const player = game.players[p];
      edge.claimedBy = player.color;
      player.trains = Math.max(0, (player.trains || 0) - edge.len);
      broadcastLog({
        playerName: player.name,
        message: player.name + ' claimed ' + game.map.cities[edge.u].name + ' - ' + game.map.cities[edge.v].name + ' using',
        newline: true,
        cards: used,
        sfx: 'route_build',
      });
      let triggeredFinalRoundThisTurn = false;
      if (!game.finalRoundActive && player.trains <= FINAL_TURN_THRESHOLD) {
        triggerFinalRound(p);
        triggeredFinalRoundThisTurn = true;
        broadcastLog({
          playerName: player.name,
          message: 'Final round has begun. Each player gets one final turn.',
        });
      }
      advanceTurn({ tickFinalRound: !triggeredFinalRoundThisTurn });
      if (game.gameOver) {
        broadcastGameOverSummaryLog();
      }
      broadcastState();
        console.log('[claim] accepted');
      }
    });
  });

  ws.on('close', () => {
    wsRooms.delete(ws);
    withRoomState(roomName, () => {
      const disconnectedClientId = unbindSocket(ws);
      if (!disconnectedClientId) return;

      const lobbyIdx = getLobbyPlayerIndex(disconnectedClientId);
      if (lobbyIdx >= 0) {
        lobbyPlayers.splice(lobbyIdx, 1);
        maybeFinishGameAfterReturns();
        broadcastLobby();
      }

      if (gameStarted && game) {
        const playerIdx = getPlayerIndexForClient(disconnectedClientId);
        if (playerIdx >= 0 && !isClientConnected(disconnectedClientId) && game.players[playerIdx].connected !== false) {
          game.players[playerIdx].connected = false;
          broadcastLog({
            playerName: game.players[playerIdx].name,
            message: game.players[playerIdx].name + ' disconnected.',
          });
          maybeFinishGameAfterReturns();
        }
        maybeResetGameIfAllPlayersDisconnected();
        broadcastLobby();
        return;
      }
    });
  });
});

server.listen(PORT, () => {
  console.log('Server running at http://localhost:' + PORT);
});
