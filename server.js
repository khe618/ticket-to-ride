const path = require("path");
const http = require("http");
const express = require("express");
const { WebSocketServer } = require("ws");
const Chance = require("chance");

const app = express();
const PORT = process.env.PORT || 3000;

app.use(express.static(__dirname));

app.get("/", (req, res) => {
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
  6: 16,
};

const PLAYERS = [
  { name: "Red", color: "red", hex: "#cc0000" },
  { name: "Green", color: "green", hex: "#008000" },
  { name: "Blue", color: "blue", hex: "#0000cc" },
  { name: "Yellow", color: "yellow", hex: "#b58900" },
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

function buildDeck() {
  const deck = [];
  for (const [name, count] of Object.entries(CARD_COUNTS)) {
    for (let i = 0; i < count; i++) deck.push(name);
  }
  return deck;
}

function initGame() {
  const map = generateMap(DEFAULTS);
  const deck = buildDeck();
  shuffleInPlace(rng, deck);
  const faceUp = deck.slice(0, 5);
  const ticketsByPlayer = PLAYERS.map(() => Object.fromEntries(CARD_ORDER.map(k => [k, 0])));
  const currentTurn = Math.floor(rng() * PLAYERS.length);
  return {
    map,
    deck,
    deckIndex: 5,
    faceUp,
    ticketsByPlayer,
    discard: [],
    players: PLAYERS,
    currentTurn,
    turnDrawCount: 0,
  };
}

let game = initGame();
// enforce rainbow reset rule on initial face-up draw
maybeResetFaceUp();

function advanceTurn() {
  game.currentTurn = (game.currentTurn + 1) % game.players.length;
  game.turnDrawCount = 0;
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

function reshuffleIfNeeded() {
  if (game.deckIndex < game.deck.length) return;
  if (game.discard.length === 0) return;
  game.deck = [...game.discard];
  game.discard = [];
  shuffleInPlace(rng, game.deck);
  game.deckIndex = 0;
}

function drawFromDeck() {
  if (game.deckIndex >= game.deck.length) {
    reshuffleIfNeeded();
  }
  if (game.deckIndex >= game.deck.length) return null;
  return game.deck[game.deckIndex++];
}

function maybeResetFaceUp() {
  const rainbowCount = game.faceUp.filter((c) => c === "rainbow").length;
  const remaining = game.deck.length - game.deckIndex;
  if (rainbowCount < 3 || remaining < 5) return;
  for (const c of game.faceUp) game.discard.push(c);
  const newFaceUp = [];
  for (let i = 0; i < 5; i++) {
    const next = drawFromDeck();
    if (!next) break;
    newFaceUp.push(next);
  }
  game.faceUp = newFaceUp;
  maybeResetFaceUp();
}

function spendTickets(playerIdx, color, len) {
  const pile = game.ticketsByPlayer[playerIdx];
  const wild = pile.rainbow || 0;
  const base = pile[color] || 0;
  const useColor = Math.min(base, len);
  const useWild = len - useColor;
  if (useWild > wild) return false;
  pile[color] = base - useColor;
  pile.rainbow = wild - useWild;
  for (let i = 0; i < useColor; i++) game.discard.push(color);
  for (let i = 0; i < useWild; i++) game.discard.push("rainbow");
  return true;
}

function getState() {
  const ticketTotals = game.ticketsByPlayer.map((counts) =>
    Object.values(counts).reduce((a, b) => a + b, 0)
  );
  const scores = game.players.map((p) => {
    let total = 0;
    for (const e of game.map.edges) {
      if (e.claimedBy === p.color) {
        total += ROUTE_POINTS[e.len] || 0;
      }
    }
    return total;
  });
  const deckRemaining = Math.max(0, (game.deck.length - game.deckIndex) + game.discard.length);
  return {
    cities: game.map.cities,
    edges: game.map.edges,
    faceUp: game.faceUp,
    tickets: game.ticketsByPlayer[game.currentTurn] || {},
    ticketTotals,
    discardCount: game.discard.length,
    deckRemaining,
    scores,
    players: game.players,
    currentTurn: game.currentTurn,
    turnDrawCount: game.turnDrawCount,
  };
}

function broadcastState() {
  const msg = JSON.stringify({ type: "state", payload: getState() });
  wss.clients.forEach((client) => {
    if (client.readyState === 1) client.send(msg);
  });
}

function broadcastLog(payload) {
  const msg = JSON.stringify({
    type: "log",
    payload: {
      ...payload,
      ts: Date.now(),
    },
  });
  wss.clients.forEach((client) => {
    if (client.readyState === 1) client.send(msg);
  });
}

function ticketsUsedForClaim(playerIdx, color, len) {
  const pile = game.ticketsByPlayer[playerIdx];
  const wild = pile.rainbow || 0;
  const base = pile[color] || 0;
  const useColor = Math.min(base, len);
  const useWild = len - useColor;
  const used = [];
  for (let i = 0; i < useColor; i++) used.push(color);
  for (let i = 0; i < useWild; i++) used.push("rainbow");
  return used;
}

wss.on("connection", (ws) => {
  ws.send(JSON.stringify({ type: "state", payload: getState() }));

  ws.on("message", (data) => {
    let msg = null;
    try {
      msg = JSON.parse(data.toString());
    } catch (err) {
      return;
    }

    if (!msg || typeof msg.type !== "string") return;

    if (msg.type === "draw_faceup") {
      const idx = Number(msg.index);
      if (!Number.isFinite(idx)) return;
      if (idx < 0 || idx >= game.faceUp.length) return;
      const color = game.faceUp[idx];
      if (!color) return;
      if (game.turnDrawCount >= 2) return;
      if (color === "rainbow" && game.turnDrawCount > 0) return;
      const p = game.currentTurn;
      game.ticketsByPlayer[p][color] = (game.ticketsByPlayer[p][color] || 0) + 1;
      const next = drawFromDeck();
      if (next) {
        game.faceUp[idx] = next;
      } else {
        game.faceUp.splice(idx, 1);
      }
      maybeResetFaceUp();
      if (color === "rainbow") {
        advanceTurn();
      } else {
        game.turnDrawCount += 1;
        if (game.turnDrawCount >= 2) advanceTurn();
      }
      broadcastLog({
        playerName: game.players[p].name,
        message: `${game.players[p].name} took `,
        cards: [color],
        faceDown: false,
      });
      broadcastState();
      return;
    }

    if (msg.type === "draw_deck") {
      const color = drawFromDeck();
      if (!color) return;
      if (game.turnDrawCount >= 2) return;
      const p = game.currentTurn;
      game.ticketsByPlayer[p][color] = (game.ticketsByPlayer[p][color] || 0) + 1;
      game.turnDrawCount += 1;
      if (game.turnDrawCount >= 2) advanceTurn();
      maybeResetFaceUp();
      broadcastLog({
        playerName: game.players[p].name,
        message: `${game.players[p].name} took `,
        cards: ["back"],
        faceDown: true,
      });
      broadcastState();
      return;
    }

    if (msg.type === "submit_route") {
      const rawEdgeId = String(msg.edgeId || "");
      const chosen = String(msg.color || "");
      const edgeId = normalizeEdgeId(rawEdgeId);
      console.log(`[claim] request edge=${rawEdgeId} color=${chosen} player=${game.players[game.currentTurn].name}`);
      if (!edgeId) {
        console.log("[claim] rejected: missing edgeId");
        return;
      }
      const edge = game.map.edges.find((e) => keyEdge(e.u, e.v) === edgeId);
      if (!edge) {
        console.log("[claim] rejected: edge not found");
        return;
      }
      if (edge.claimedBy) {
        console.log("[claim] rejected: already claimed");
        return;
      }
      const p = game.currentTurn;
      if (edge.color.name !== "gray" && chosen !== edge.color.name) {
        console.log("[claim] rejected: color mismatch");
        return;
      }
      if (edge.color.name === "gray" && !chosen) {
        console.log("[claim] rejected: missing color for gray route");
        return;
      }
      const canClaim = canAffordTickets(game.ticketsByPlayer[p], chosen, edge.len);
      if (!canClaim) {
        console.log("[claim] rejected: insufficient tickets");
        return;
      }
      const used = ticketsUsedForClaim(p, chosen, edge.len);
      if (!spendTickets(p, chosen, edge.len)) {
        console.log("[claim] rejected: spend failed");
        return;
      }
      const player = game.players[game.currentTurn];
      edge.claimedBy = player.color;
      broadcastLog({
        playerName: player.name,
        message: `${player.name} claimed ${game.map.cities[edge.u].name} — ${game.map.cities[edge.v].name} using`,
        newline: true,
        cards: used,
      });
      advanceTurn();
      broadcastState();
      console.log("[claim] accepted");
    }
  });
});

server.listen(PORT, () => {
  console.log(`Server running at http://localhost:${PORT}`);
});
