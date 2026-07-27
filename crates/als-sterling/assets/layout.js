/**
 * The graph view's layout: one state's atoms and tuples -> node and edge
 * geometry. Pure — model in, positions out, no DOM and no document, exactly
 * like `instance.js`.
 *
 * **Determinism is the invariant this module exists to hold.** The same state
 * must produce byte-identical geometry on every machine and every render, so
 * that stepping a trace back and forth does not reshuffle the picture and two
 * people looking at the same instance are looking at the same drawing. That
 * means, throughout:
 *
 * - every iteration is over an **array in document order** (the writer's order,
 *   itself deterministic — `alloy6-instance-xml.md` §2);
 * - the one `Map` is keyed by **atom label** and is only ever `get`/`set`, never
 *   iterated;
 * - every sort is total: a numeric key **and** a label tie-break, so no
 *   comparison ever falls through to the engine's own stability;
 * - nothing reads `Math.random`, the clock, object identity, or insertion order
 *   of anything unordered.
 *
 * The algorithm is the classical layered one (rank, order, place, route), at
 * the smallest size that draws an Alloy instance honestly: cycles are broken by
 * a depth-first pass whose back edges are *drawn as back edges* rather than
 * hidden, ranks come from longest-path layering, and crossing reduction is a
 * fixed number of barycenter sweeps.
 *
 * `tests/frontend/layout-determinism.mjs` (dev-only, never served) checks the
 * invariant above directly.
 */

import { isHiddenRelation, isHiddenSig, isMacroSkolem, shortLabel } from './instance.js';

/** Every node is one line of label plus at most one line of tags. */
const NODE_HEIGHT = 44;
const MIN_NODE_WIDTH = 64;
/**
 * Estimated advance widths, in pixels per character, for the two monospace
 * sizes the drawing uses (12px atom labels, 10px edge labels, 9.5px tags).
 *
 * Estimated on purpose: see `placeLabels`. A monospace face makes the estimate
 * accurate to the face's own aspect ratio, and every consumer pads for the rest.
 */
const LABEL_CHAR_WIDTH = 7.4;
const TAG_CHAR_WIDTH = 5.8;
const LABEL_WIDTH_10PX = 6.1;
const NODE_PADDING = 18;

/** Vertical distance between one rank's boxes and the next's. */
const RANK_GAP = 84;
/** Horizontal distance between two boxes on the same rank. */
const NODE_GAP = 28;
/** Lateral separation between parallel edges joining the same pair of atoms. */
const PARALLEL_GAP = 20;
/** The width a crossing edge reserves on a rank it merely passes through. */
const BEND_WIDTH = 14;
/** How far a self-loop or a same-rank edge bows out from its node. */
const LOOP_REACH = 46;
/** How far a back edge bows out to the side on its way up the drawing. */
const BACK_REACH = 62;

/**
 * Down-then-up barycenter sweeps. Four is where the crossing count stops
 * improving on instance-sized graphs, and a *fixed* count is what keeps the
 * result a function of the input rather than of a convergence test.
 */
const SWEEPS = 4;

/**
 * Lays out one state.
 *
 * Returns `{nodes, edges, width, height}` in a coordinate space whose origin is
 * the top-left of the drawing; the renderer supplies its own padding.
 */
export function layoutGraph(state, { showBuiltins }) {
  const { nodes, edges, sigs } = collect(state, showBuiltins);
  const ranks = assignRanks(nodes, edges);
  const segments = addBends(nodes, edges, ranks);
  orderRanks(nodes, segments, ranks);
  const size = place(nodes, ranks);
  // Side-routed edges (back edges, self-loops, same-rank arcs) and their labels
  // reach past the rightmost box, so the drawing is wider than its ranks are.
  size.width = Math.max(size.width, route(nodes, edges));
  // The bend points did their work in the ordering and the routing; they are
  // not atoms, so they never reach the drawing.
  return { nodes: nodes.filter((node) => !node.bend), edges, sigs, ...size };
}

/* ---------- what is in the picture ---------- */

/**
 * The nodes and edges of one state: an atom per node, a tuple per edge.
 *
 * Three conventions, all the reference visualizer's:
 * - a relation of arity > 2 is still **one** edge, first column to last, with
 *   the middle atoms carried in its label;
 * - a relation of arity 1 is not an edge at all — it is a **tag** on its atom
 *   (this is what makes `$first`/`$last`-shaped skolems readable);
 * - an atom that a tuple names but no visible sig lists still gets a node
 *   (integers, which the schema never gives `<atom>` children, arrive this
 *   way); dropping the edge instead would silently lose a fact.
 */
function collect(state, showBuiltins) {
  const nodes = [];
  const sigs = [];
  const byAtom = new Map();
  const visible = (sig) => showBuiltins || !isHiddenSig(sig);

  let sigIndex = 0;
  for (const sig of state.sigs) {
    if (!visible(sig)) continue;
    const label = shortLabel(sig.label);
    // The legend's own list: which sigs the drawing is showing, in the order
    // they were met, which is the order their hues were assigned.
    sigs.push({ index: sigIndex, label, atoms: sig.atoms.length });
    for (const atom of sig.atoms) {
      const existing = byAtom.get(atom);
      // An atom is written under its most specific sig (§2), so the first sig
      // to claim it is the one it *is*; any later claim is a subset sig it is
      // also a member of, which is a tag rather than a second node.
      if (existing === undefined) {
        nodes.push(newNode(atom, sigIndex, label, byAtom));
      } else {
        existing.tags.push(label);
      }
    }
    sigIndex += 1;
  }

  const edges = [];
  const relations = [
    ...state.fields.map((field) => ({ relation: field, witness: false, derived: false })),
    // A macro skolem is bookkeeping for a zero-arg `fun`, not a chosen witness
    // (see `isMacroSkolem`): it draws, but it neither marks its atoms nor
    // competes with the model's own fields for attention.
    ...state.skolems.map((skolem) => ({
      relation: skolem,
      witness: !isMacroSkolem(skolem),
      derived: isMacroSkolem(skolem),
    })),
  ];
  for (const { relation, witness, derived } of relations) {
    if (!showBuiltins && isHiddenRelation(relation, state.sigsById)) continue;
    const name = relationName(relation, state.sigsById);
    for (const tuple of relation.tuples) {
      const touched = tuple.map((atom) => atomNode(atom, nodes, byAtom));
      if (witness) for (const node of touched) node.witness = true;
      if (tuple.length === 1) {
        touched[0].tags.push(name);
        continue;
      }
      edges.push({
        from: touched[0].index,
        to: touched[touched.length - 1].index,
        label: edgeLabel(name, tuple),
        witness,
        derived,
        temporal: relation.flags.includes('var'),
      });
    }
  }
  return { nodes, edges, sigs };
}

function newNode(atom, sigIndex, sigLabel, byAtom) {
  const node = {
    index: byAtom.size,
    atom,
    /** Which visible sig owns it — the renderer's hue key. `-1` if none does. */
    sigIndex,
    sigLabel,
    /** Subset memberships and unary-relation names, in document order. */
    tags: [],
    /** Whether any skolem — a solver-chosen witness — names this atom. */
    witness: false,
    rank: 0,
    order: 0,
    x: 0,
    y: 0,
    width: MIN_NODE_WIDTH,
    height: NODE_HEIGHT,
  };
  byAtom.set(atom, node);
  return node;
}

/** The node for an atom, minting the "no visible sig lists it" case. */
function atomNode(atom, nodes, byAtom) {
  const existing = byAtom.get(atom);
  if (existing !== undefined) return existing;
  const node = newNode(atom, -1, '', byAtom);
  nodes.push(node);
  return node;
}

/** `Node.color` for a field, `$x` for a skolem — the table view's naming. */
function relationName(relation, sigsById) {
  const owner = relation.parentId === null ? undefined : sigsById.get(relation.parentId);
  return owner === undefined
    ? shortLabel(relation.label)
    : `${shortLabel(owner.label)}.${relation.label}`;
}

/** An arity-3 tuple `a->b->c` draws as `a -> c` labelled `f [b]`. */
function edgeLabel(name, tuple) {
  const middle = tuple.slice(1, -1);
  return middle.length === 0 ? name : `${name} [${middle.join(', ')}]`;
}

/* ---------- rank ---------- */

/**
 * Assigns every node a rank, and marks the edges that had to point backwards
 * for that to be possible.
 *
 * Cycles are broken by a depth-first pass in node order: an edge into a node
 * still on the stack is a **back edge**, recorded as such and excluded from the
 * layering — the renderer then draws it going back up the page, which is the
 * honest picture of a cyclic relation (an ordering's `prev`, a graph's own
 * loop) rather than a lie about where it points.
 *
 * Returns the ranks as arrays of node indices.
 */
function assignRanks(nodes, edges) {
  const outgoing = nodes.map(() => []);
  for (const [index, edge] of edges.entries()) {
    edge.self = edge.from === edge.to;
    edge.back = false;
    if (!edge.self) outgoing[edge.from].push(index);
  }
  markBackEdges(nodes, edges, outgoing);

  // Longest-path layering over what is left, which is now acyclic: a node sits
  // one rank below the lowest of its predecessors.
  const indegree = nodes.map(() => 0);
  for (const edge of edges) {
    if (!edge.self && !edge.back) indegree[edge.to] += 1;
  }
  const queue = nodes.filter((node) => indegree[node.index] === 0).map((node) => node.index);
  let head = 0;
  let settled = 0;
  while (head < queue.length) {
    const from = queue[head];
    head += 1;
    settled += 1;
    for (const index of outgoing[from]) {
      const edge = edges[index];
      if (edge.back) continue;
      nodes[edge.to].rank = Math.max(nodes[edge.to].rank, nodes[from].rank + 1);
      indegree[edge.to] -= 1;
      if (indegree[edge.to] === 0) queue.push(edge.to);
    }
  }
  if (settled !== nodes.length) {
    // Removing every back edge leaves a DAG by construction, so this is a bug
    // in the pass above rather than a shape some instance can have.
    throw new Error('graph layout: the layering pass left a cycle behind');
  }

  const depth = nodes.reduce((most, node) => Math.max(most, node.rank), 0) + 1;
  const ranks = Array.from({ length: depth }, () => []);
  for (const node of nodes) ranks[node.rank].push(node.index);
  return ranks;
}

/** The depth-first pass, iterative so that a long chain cannot blow the stack. */
function markBackEdges(nodes, edges, outgoing) {
  const WHITE = 0;
  const GRAY = 1;
  const BLACK = 2;
  const colour = nodes.map(() => WHITE);
  for (const root of nodes) {
    if (colour[root.index] !== WHITE) continue;
    const stack = [{ node: root.index, next: 0 }];
    colour[root.index] = GRAY;
    while (stack.length > 0) {
      const frame = stack[stack.length - 1];
      if (frame.next === outgoing[frame.node].length) {
        colour[frame.node] = BLACK;
        stack.pop();
        continue;
      }
      const edge = edges[outgoing[frame.node][frame.next]];
      frame.next += 1;
      if (colour[edge.to] === GRAY) edge.back = true;
      else if (colour[edge.to] === WHITE) {
        colour[edge.to] = GRAY;
        stack.push({ node: edge.to, next: 0 });
      }
    }
  }
}

/* ---------- bends ---------- */

/**
 * Gives every edge that spans more than one rank a **bend point** on each rank
 * it crosses.
 *
 * Without them a long edge is a straight line drawn over whatever happens to be
 * between its ends — in a model with an ordering, that is the whole column of
 * atoms — and crossing reduction cannot see it at all, because it touches no
 * intermediate rank. With them, the edge occupies width on every rank it
 * crosses, so the ranks spread to make room and the ordering pass routes it
 * around the boxes rather than through them.
 *
 * Returns the adjacency the ordering pass should use: one entry per *segment*,
 * so a long edge pulls each of its bends towards its neighbours instead of
 * pulling its two endpoints towards each other.
 */
function addBends(nodes, edges, ranks) {
  const segments = [];
  for (const [index, edge] of edges.entries()) {
    edge.through = [];
    if (edge.self || edge.back) continue;
    const top = nodes[edge.from].rank;
    const bottom = nodes[edge.to].rank;
    if (bottom - top <= 1) {
      if (bottom !== top) segments.push([edge.from, edge.to]);
      continue;
    }
    let previous = edge.from;
    for (let rank = top + 1; rank < bottom; rank += 1) {
      const bend = {
        index: nodes.length,
        // Unique per edge and rank, so the ordering pass's label tie-break is
        // still a total order once bends are in the mix.
        atom: ` bend ${index} ${rank}`,
        sigIndex: -1,
        sigLabel: '',
        tags: [],
        witness: false,
        bend: true,
        rank,
        order: 0,
        x: 0,
        y: 0,
        width: BEND_WIDTH,
        height: 0,
      };
      nodes.push(bend);
      ranks[rank].push(bend.index);
      edge.through.push(bend.index);
      segments.push([previous, bend.index]);
      previous = bend.index;
    }
    segments.push([previous, edge.to]);
  }
  return segments;
}

/* ---------- order ---------- */

/**
 * Reduces crossings by barycenter sweeps: a node wants to sit above the average
 * position of the nodes it points at, and below the average of those pointing
 * at it. Ties — including every node with no neighbour in the adjacent rank —
 * are broken by the atom label, so the result never depends on which node the
 * sort happened to see first.
 */
function orderRanks(nodes, segments, ranks) {
  const predecessors = nodes.map(() => []);
  const successors = nodes.map(() => []);
  for (const [from, to] of segments) {
    successors[from].push(to);
    predecessors[to].push(from);
  }
  writeOrder(nodes, ranks);
  for (let sweep = 0; sweep < SWEEPS; sweep += 1) {
    for (let rank = 1; rank < ranks.length; rank += 1) sortRank(nodes, ranks, rank, predecessors);
    for (let rank = ranks.length - 2; rank >= 0; rank -= 1) sortRank(nodes, ranks, rank, successors);
  }
}

function sortRank(nodes, ranks, rank, neighbours) {
  const rankNodes = ranks[rank];
  const barycentre = new Map();
  for (const index of rankNodes) {
    const near = neighbours[index];
    const mean = near.length === 0
      // No neighbour to be pulled towards: stay put, which is what keeps an
      // isolated atom from drifting across the rank on every sweep.
      ? nodes[index].order
      : near.reduce((total, other) => total + nodes[other].order, 0) / near.length;
    barycentre.set(index, mean);
  }
  rankNodes.sort((left, right) => {
    const difference = barycentre.get(left) - barycentre.get(right);
    return difference !== 0 ? difference : compareAtoms(nodes[left], nodes[right]);
  });
  writeOrder(nodes, ranks);
}

function writeOrder(nodes, ranks) {
  for (const rankNodes of ranks) {
    for (const [position, index] of rankNodes.entries()) nodes[index].order = position;
  }
}

/** The total tie-break: atom labels are unique within an instance. */
function compareAtoms(left, right) {
  if (left.atom === right.atom) return 0;
  return left.atom < right.atom ? -1 : 1;
}

/* ---------- place ---------- */

/** Gives every node a size and a position, and reports the drawing's extent. */
function place(nodes, ranks) {
  for (const node of nodes) {
    if (node.bend) continue;
    const label = node.atom.length * LABEL_CHAR_WIDTH;
    const tags = tagLine(node).length * TAG_CHAR_WIDTH;
    node.width = Math.max(MIN_NODE_WIDTH, Math.max(label, tags) + NODE_PADDING * 2);
  }

  const widths = ranks.map((rankNodes) =>
    rankNodes.reduce((total, index) => total + nodes[index].width + NODE_GAP, -NODE_GAP));
  const width = Math.max(0, ...widths);
  for (const [rank, rankNodes] of ranks.entries()) {
    // Every rank is centred on the widest one, so the drawing reads down its
    // own middle rather than flush left.
    let x = (width - widths[rank]) / 2;
    for (const index of rankNodes) {
      const node = nodes[index];
      node.x = x + node.width / 2;
      node.y = rank * (NODE_HEIGHT + RANK_GAP) + NODE_HEIGHT / 2;
      x += node.width + NODE_GAP;
    }
  }
  const height = ranks.length * NODE_HEIGHT + Math.max(0, ranks.length - 1) * RANK_GAP;
  return { width, height };
}

/** The node's second line: subset memberships and unary-relation names. */
export function tagLine(node) {
  return node.tags.join(' · ');
}

/* ---------- route ---------- */

/**
 * Gives every edge an SVG path and a point to hang its label on.
 *
 * Four shapes, so that nothing is ever drawn on top of something else it could
 * be confused with: a plain cubic down the page for a forward edge, a side
 * bulge for two atoms on the same rank, a wide bow to the right for a back
 * edge, and a closed loop beside the node for a self-edge. Parallel edges
 * between the same pair are fanned apart by their position in document order.
 */
function route(nodes, edges) {
  const seen = new Map();
  const totals = new Map();
  let right = 0;
  for (const edge of edges) {
    const key = `${edge.from} ${edge.to}`;
    totals.set(key, (totals.get(key) ?? 0) + 1);
  }
  for (const edge of edges) {
    const key = `${edge.from} ${edge.to}`;
    const position = seen.get(key) ?? 0;
    seen.set(key, position + 1);
    const spread = (position - (totals.get(key) - 1) / 2) * PARALLEL_GAP;
    const from = nodes[edge.from];
    const to = nodes[edge.to];
    const shape = edge.self
      ? selfLoop(from, spread)
      : edge.back
        ? backEdge(from, to, spread)
        : from.rank === to.rank
          ? sameRank(from, to, spread)
          : edge.through.length > 0
            ? throughBends(nodes, edge, from, to)
            : forward(from, to, spread);
    edge.path = shape.path;
    edge.labelAt = shape.labelAt;
    // The label is centred on its anchor, so half of it hangs to the right; the
    // width below is the widest label this instance can produce there.
    right = Math.max(right, shape.reach ?? 0, edge.labelAt.x + (edge.label.length * LABEL_WIDTH_10PX) / 2);
  }
  placeLabels(edges);
  return right;
}

/**
 * Keeps edge labels off each other.
 *
 * Every edge between one pair of ranks hangs its label at the same height, so a
 * rank with four outgoing tuples would print four labels on one line, on top of
 * each other. Each label is given an estimated box — **character count times a
 * fixed per-character width, never a DOM measurement** — and then dealt into
 * the first of five vertical lanes where that box misses everything already
 * placed in the same lane; if all five are taken, it goes to the lane it
 * overlaps least, argmin with a first-lane-wins tie-break.
 *
 * The estimate is the point, not a shortcut: this module has to be a pure
 * function of the instance and has to produce the same geometry in a headless
 * determinism check as in a browser, and a measured box would make it depend on
 * the machine's font rasterization. Monospace makes the estimate close, and the
 * padding below absorbs the error.
 */
function placeLabels(edges) {
  const LANES = [0, -14, 14, -28, 28];
  const PADDING = 7;
  const lanes = new Map();
  for (const edge of edges) {
    const half = (edge.label.length * LABEL_WIDTH_10PX) / 2 + PADDING;
    const box = { from: edge.labelAt.x - half, to: edge.labelAt.x + half };
    const line = Math.round(edge.labelAt.y / 12);
    let best = 0;
    let leastOverlap = Infinity;
    for (const [lane, offset] of LANES.entries()) {
      const taken = lanes.get(`${line} ${lane}`) ?? [];
      const overlap = taken.reduce((most, other) => Math.max(most, span(box, other)), 0);
      if (overlap === 0) {
        best = lane;
        leastOverlap = 0;
        break;
      }
      if (overlap < leastOverlap) {
        leastOverlap = overlap;
        best = lane;
      }
    }
    const key = `${line} ${best}`;
    lanes.set(key, [...(lanes.get(key) ?? []), box]);
    edge.labelAt = { x: edge.labelAt.x, y: round(edge.labelAt.y + LANES[best]) };
  }
}

/** How much two label boxes overlap horizontally; `0` when they miss. */
function span(one, two) {
  return Math.max(0, Math.min(one.to, two.to) - Math.max(one.from, two.from));
}

function forward(from, to, spread) {
  const start = { x: from.x + spread, y: from.y + from.height / 2 };
  const end = { x: to.x + spread, y: to.y - to.height / 2 };
  const lift = (end.y - start.y) / 2;
  const one = { x: start.x, y: start.y + lift };
  const two = { x: end.x, y: end.y - lift };
  return { path: cubic(start, one, two, end), labelAt: midpoint(start, one, two, end) };
}

/**
 * A multi-rank edge, drawn through its bend points as a chain of vertical
 * cubics — smooth at every joint because each segment leaves and enters
 * vertically, which is also what keeps it visually parallel to its neighbours
 * in a bundle.
 */
function throughBends(nodes, edge, from, to) {
  const points = [
    { x: from.x, y: from.y + from.height / 2 },
    ...edge.through.map((index) => ({ x: nodes[index].x, y: nodes[index].y })),
    { x: to.x, y: to.y - to.height / 2 },
  ];
  let path = `M ${round(points[0].x)} ${round(points[0].y)}`;
  for (let index = 1; index < points.length; index += 1) {
    const start = points[index - 1];
    const end = points[index];
    const lift = (end.y - start.y) / 2;
    path += ` C ${round(start.x)} ${round(start.y + lift)}, ${round(end.x)} ${round(end.y - lift)}, ${round(end.x)} ${round(end.y)}`;
  }
  // The middle bend, so a long edge's label sits on the part of it that is
  // furthest from both endpoints' own clutter.
  // Hung on the first span rather than on a bend: a bend sits on a rank line,
  // which is exactly where the boxes are, so a label there lands on top of an
  // atom. Between two ranks there is nothing but other labels.
  const above = points[0];
  const below = points[1];
  return {
    path,
    labelAt: { x: round((above.x + below.x) / 2), y: round((above.y + below.y) / 2) },
  };
}

function sameRank(from, to, spread) {
  const [left, right] = from.x <= to.x ? [from, to] : [to, from];
  const start = { x: left.x + left.width / 2, y: left.y };
  const end = { x: right.x - right.width / 2, y: right.y };
  const bulge = LOOP_REACH + Math.abs(spread);
  const one = { x: start.x + bulge / 2, y: start.y - bulge };
  const two = { x: end.x - bulge / 2, y: end.y - bulge };
  return { path: cubic(start, one, two, end), labelAt: midpoint(start, one, two, end), reach: one.x };
}

function backEdge(from, to, spread) {
  const start = { x: from.x + from.width / 2, y: from.y };
  const end = { x: to.x + to.width / 2, y: to.y };
  const reach = BACK_REACH + Math.abs(spread);
  const one = { x: start.x + reach, y: start.y };
  const two = { x: end.x + reach, y: end.y };
  return { path: cubic(start, one, two, end), labelAt: midpoint(start, one, two, end), reach: one.x };
}

function selfLoop(node, spread) {
  const reach = LOOP_REACH + Math.abs(spread);
  const start = { x: node.x + node.width / 2, y: node.y - node.height / 4 };
  const end = { x: node.x + node.width / 2, y: node.y + node.height / 4 };
  const one = { x: start.x + reach, y: start.y - reach / 2 };
  const two = { x: end.x + reach, y: end.y + reach / 2 };
  return { path: cubic(start, one, two, end), labelAt: midpoint(start, one, two, end), reach: one.x };
}

function cubic(start, one, two, end) {
  return `M ${round(start.x)} ${round(start.y)} C ${round(one.x)} ${round(one.y)}, ${round(two.x)} ${round(two.y)}, ${round(end.x)} ${round(end.y)}`;
}

/** A cubic's own midpoint (`t = 0.5`), where its label sits. */
function midpoint(start, one, two, end) {
  return {
    x: round((start.x + 3 * one.x + 3 * two.x + end.x) / 8),
    y: round((start.y + 3 * one.y + 3 * two.y + end.y) / 8),
  };
}

/**
 * Two decimal places, everywhere a coordinate reaches the output.
 *
 * Not cosmetic: barycentres are means, so coordinates carry binary fractions,
 * and rounding them at the boundary is what makes "the same instance draws the
 * same SVG" a claim about the *text* and not just about the geometry.
 */
function round(value) {
  return Math.round(value * 100) / 100;
}
