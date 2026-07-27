/**
 * The graph view: `layout.js`'s geometry, drawn as SVG.
 *
 * Rendering only — every decision about *where* something goes was already
 * made, deterministically, in the layout module; this file turns coordinates
 * into elements and owns the one piece of interaction the view has (panning and
 * zooming its own `viewBox`).
 *
 * Colour is a per-sig hue set as a custom property on each node's group, which
 * is what lets the stylesheet keep both schemes in one place: the hue is the
 * datum, and `graph.css` decides what lightness it gets in light and in dark.
 *
 * Two affordances live here besides the drawing itself. The **legend** is the
 * key to those hues and doubles as the control for them — past ten sigs hues
 * repeat, and a key you can point at is what keeps that honest. **Focus** is
 * subtractive: hovering an atom, an edge or a legend key dims everything that
 * is not part of it, and clicking pins that state until it is cleared, so the
 * drawing never gains a colour it did not already have.
 */

import { tagLine } from './layout.js';
import { blank } from './ui.js';

const SVG_NS = 'http://www.w3.org/2000/svg';

/**
 * Hues, in the order sigs are met.
 *
 * Ten well-separated values rather than a generated ramp: an instance with more
 * than ten signatures repeats a hue, which is honest (the label is what names
 * the sig — the hue only groups it) and beats ten near-identical colours.
 */
const HUES = [212, 158, 28, 288, 96, 340, 188, 52, 262, 128];

/** Room around the drawing, so nothing touches the edge of the frame. */
const PADDING = 32;

/** One wheel notch. */
const ZOOM_STEP = 1.15;
const MIN_SCALE = 0.2;
const MAX_SCALE = 6;

/**
 * Draws `layout` into `container`, replacing its contents.
 *
 * `viewBox` restores a pan/zoom the caller is holding on to (`null` fits the
 * drawing); `onViewBox` is called with the new one whenever the user moves it,
 * so that the caller — not this module — owns that state.
 */
export function renderGraph(container, layout, { viewBox, onViewBox }) {
  if (layout.nodes.length === 0) {
    container.replaceChildren(blank(
      'nothing to draw',
      'This state has no atoms. Turn on builtins to see the empty built-in signatures, or open the table view.',
    ));
    return;
  }
  const svg = element('svg', 'graph');
  svg.setAttribute('xmlns', SVG_NS);
  const fitted = fit(layout);
  // Drawn at its natural size — one layout unit is one CSS pixel — and left to
  // the stylesheet to scale it *down* when it does not fit. Fitting a tall
  // drawing to the viewport instead would squeeze an ordering's column of atoms
  // into an unreadable ribbon; scrolling a legible picture beats seeing all of
  // an illegible one, and the wheel is there for the rest.
  svg.setAttribute('width', String(fitted.width));
  svg.setAttribute('height', String(fitted.height));
  applyViewBox(svg, viewBox ?? fitted);
  svg.append(defs(), edgeLayer(layout), nodeLayer(layout));
  panAndZoom(svg, fitted, onViewBox);
  const legend = legendFor(layout, svg);
  attention(svg, layout, legend);
  container.replaceChildren(legend, svg);
}

/** The `viewBox` that shows the whole drawing. */
function fit(layout) {
  return {
    x: -PADDING,
    y: -PADDING,
    // A drawing narrower than its own padding still needs a positive extent.
    width: Math.max(1, layout.width + PADDING * 2),
    height: Math.max(1, layout.height + PADDING * 2),
  };
}

function applyViewBox(svg, box) {
  svg.setAttribute('viewBox', `${box.x} ${box.y} ${box.width} ${box.height}`);
}

/** The arrowheads. Two, because a back edge is drawn in its own colour. */
function defs() {
  const node = document.createElementNS(SVG_NS, 'defs');
  for (const kind of ['arrow', 'arrow-back']) {
    const marker = document.createElementNS(SVG_NS, 'marker');
    marker.setAttribute('id', kind);
    marker.setAttribute('viewBox', '0 0 10 10');
    marker.setAttribute('refX', '9');
    marker.setAttribute('refY', '5');
    marker.setAttribute('markerWidth', '7');
    marker.setAttribute('markerHeight', '7');
    marker.setAttribute('orient', 'auto-start-reverse');
    marker.setAttribute('markerUnits', 'userSpaceOnUse');
    const head = document.createElementNS(SVG_NS, 'path');
    head.setAttribute('d', 'M 0 1 L 10 5 L 0 9 z');
    head.setAttribute('class', kind);
    marker.append(head);
    node.append(marker);
  }
  return node;
}

function edgeLayer(layout) {
  const layer = element('g', 'edges');
  for (const [index, edge] of layout.edges.entries()) {
    const group = element('g', edgeClass(edge));
    group.dataset.edge = String(index);
    group.dataset.from = String(edge.from);
    group.dataset.to = String(edge.to);
    // The visible line, and a fat transparent twin under it that is what the
    // pointer actually hits — 1.4px of curve is not a target.
    const hit = document.createElementNS(SVG_NS, 'path');
    hit.setAttribute('d', edge.path);
    hit.setAttribute('class', 'hit');
    const line = document.createElementNS(SVG_NS, 'path');
    line.setAttribute('d', edge.path);
    line.setAttribute('class', 'wire');
    line.setAttribute('marker-end', edge.back ? 'url(#arrow-back)' : 'url(#arrow)');
    group.append(hit, line, text(edge.label, edge.labelAt.x, edge.labelAt.y, 'edge-label'));
    layer.append(group);
  }
  return layer;
}

function edgeClass(edge) {
  const classes = ['edge'];
  if (edge.back) classes.push('back');
  if (edge.self) classes.push('self');
  if (edge.witness) classes.push('witness');
  if (edge.derived) classes.push('derived');
  // `var` fields hold different tuples at different states; saying so costs one
  // class and answers "why did this edge move when I stepped?".
  if (edge.temporal) classes.push('temporal');
  return classes.join(' ');
}

function nodeLayer(layout) {
  const layer = element('g', 'nodes');
  for (const node of layout.nodes) {
    const group = element('g', node.witness ? 'node witness' : 'node');
    group.dataset.node = String(node.index);
    // `-1` is an atom no visible sig lists (an integer, a filtered-out sig's
    // atom reached through a relation): no hue, so it reads as outside the
    // model's own structure rather than as one more sig.
    if (node.sigIndex >= 0) {
      group.dataset.sig = String(node.sigIndex);
      group.style.setProperty('--hue', String(hueFor(node.sigIndex)));
    } else {
      group.classList.add('unowned');
    }

    const box = document.createElementNS(SVG_NS, 'rect');
    box.setAttribute('x', String(node.x - node.width / 2));
    box.setAttribute('y', String(node.y - node.height / 2));
    box.setAttribute('width', String(node.width));
    box.setAttribute('height', String(node.height));
    box.setAttribute('rx', '8');
    group.append(box);

    const tags = tagLine(node);
    const label = text(node.atom, node.x, tags === '' ? node.y : node.y - 5, 'atom');
    group.append(label);
    if (tags !== '') group.append(text(tags, node.x, node.y + 11, 'node-tags'));
    if (node.sigLabel !== '') {
      const title = document.createElementNS(SVG_NS, 'title');
      title.textContent = tags === '' ? node.sigLabel : `${node.sigLabel} — ${tags}`;
      group.append(title);
    }
    layer.append(group);
  }
  return layer;
}

/** The hue a signature's atoms are drawn in, by the order it was met. */
function hueFor(sigIndex) {
  return HUES[sigIndex % HUES.length];
}

/**
 * The key to the hues, and the control for them.
 *
 * Every visible signature gets a swatch, its name and its atom count. Pointing
 * at a key lights that signature's atoms; clicking pins it. Past ten
 * signatures the hues repeat, and this is what keeps that from being a puzzle:
 * the key is right there to disambiguate, and pinning answers "which of these
 * two teal ones is `Name`?" directly.
 */
function legendFor(layout, svg) {
  const legend = document.createElement('div');
  legend.className = 'legend';
  const label = document.createElement('span');
  label.className = 'eyebrow';
  label.textContent = 'signatures';
  legend.append(label);
  for (const sig of layout.sigs) {
    const key = document.createElement('button');
    key.type = 'button';
    key.className = 'legend-key';
    key.dataset.sig = String(sig.index);
    key.setAttribute('aria-pressed', 'false');
    key.style.setProperty('--hue', String(hueFor(sig.index)));
    const swatch = document.createElement('span');
    swatch.className = 'swatch';
    const name = document.createElement('span');
    name.textContent = sig.label;
    const count = document.createElement('span');
    count.className = 'legend-count';
    count.textContent = String(sig.atoms);
    key.append(swatch, name, count);
    legend.append(key);
  }
  // A drawing with no named signature (only unowned atoms) has nothing to key.
  return layout.sigs.length === 0 ? emptyLegend() : legend;
}

function emptyLegend() {
  const legend = document.createElement('div');
  legend.className = 'legend';
  legend.hidden = true;
  return legend;
}

/**
 * Hover and selection, subtractively.
 *
 * One `focused` class on the drawing dims everything, and `focus`/`related`
 * marks put back what belongs to whatever is being pointed at: an atom brings
 * its incident tuples and their far ends, a tuple brings both its atoms, a
 * legend key brings a whole signature. A click pins the current focus (Escape
 * or a click on empty space clears it), which is what makes it usable for
 * *reading* — following one atom's relations through a dense drawing — rather
 * than only for pointing.
 */
function attention(svg, layout, legend) {
  const nodes = new Map([...svg.querySelectorAll('.node')].map((node) => [node.dataset.node, node]));
  const edges = [...svg.querySelectorAll('.edge')];
  let pinned = null;

  const clear = () => {
    svg.classList.remove('focused');
    for (const node of nodes.values()) node.classList.remove('focus', 'related', 'pinned');
    for (const edge of edges) edge.classList.remove('related');
    for (const key of legend.querySelectorAll('.legend-key')) key.setAttribute('aria-pressed', 'false');
  };

  const show = (focus) => {
    clear();
    if (focus === null) return;
    svg.classList.add('focused');
    focus();
  };

  const focusNode = (index) => () => {
    nodes.get(index)?.classList.add('focus');
    for (const edge of edges) {
      if (edge.dataset.from !== index && edge.dataset.to !== index) continue;
      edge.classList.add('related');
      nodes.get(edge.dataset.from)?.classList.add('related');
      nodes.get(edge.dataset.to)?.classList.add('related');
    }
  };

  const focusEdge = (edge) => () => {
    edge.classList.add('related');
    nodes.get(edge.dataset.from)?.classList.add('focus');
    nodes.get(edge.dataset.to)?.classList.add('focus');
  };

  const focusSig = (sigIndex) => () => {
    for (const node of nodes.values()) {
      if (node.dataset.sig === sigIndex) node.classList.add('focus');
    }
    for (const edge of edges) {
      const ends = [edge.dataset.from, edge.dataset.to];
      if (ends.some((end) => nodes.get(end)?.dataset.sig === sigIndex)) edge.classList.add('related');
    }
  };

  const hover = (focus) => {
    if (pinned === null) show(focus);
  };

  for (const [index, node] of nodes) {
    node.addEventListener('pointerenter', () => hover(focusNode(index)));
    node.addEventListener('pointerleave', () => hover(null));
    node.addEventListener('click', (event) => {
      event.stopPropagation();
      pinned = pinned === `node ${index}` ? null : `node ${index}`;
      show(pinned === null ? null : focusNode(index));
      if (pinned !== null) nodes.get(index)?.classList.add('pinned');
    });
  }

  for (const edge of edges) {
    edge.addEventListener('pointerenter', () => hover(focusEdge(edge)));
    edge.addEventListener('pointerleave', () => hover(null));
  }

  for (const key of legend.querySelectorAll('.legend-key')) {
    const sigIndex = key.dataset.sig;
    key.addEventListener('pointerenter', () => hover(focusSig(sigIndex)));
    key.addEventListener('pointerleave', () => hover(null));
    // The keys are the one part of the drawing a keyboard can reach, so they
    // light their signature on focus as well as on hover.
    key.addEventListener('focus', () => hover(focusSig(sigIndex)));
    key.addEventListener('blur', () => hover(null));
    key.addEventListener('click', () => {
      pinned = pinned === `sig ${sigIndex}` ? null : `sig ${sigIndex}`;
      show(pinned === null ? null : focusSig(sigIndex));
      if (pinned !== null) key.setAttribute('aria-pressed', 'true');
    });
  }

  // Empty space and Escape both mean "stop looking at that".
  svg.addEventListener('click', () => {
    pinned = null;
    show(null);
  });
  document.addEventListener('keydown', (event) => {
    if (event.key !== 'Escape' || pinned === null) return;
    pinned = null;
    show(null);
  });
}

function text(content, x, y, className) {
  const node = document.createElementNS(SVG_NS, 'text');
  node.setAttribute('x', String(x));
  node.setAttribute('y', String(y));
  node.setAttribute('class', className);
  node.setAttribute('text-anchor', 'middle');
  node.setAttribute('dominant-baseline', 'central');
  node.textContent = content;
  return node;
}

/**
 * Wheel to zoom about the pointer, drag to pan, double-click to fit again.
 *
 * Deliberately the whole interaction budget of this view: it moves the window
 * over a fixed drawing and never moves anything *in* the drawing, so what is on
 * screen stays a function of the instance (there is no hand-placed layout to
 * lose, and nothing to persist).
 */
function panAndZoom(svg, fitted, onViewBox) {
  // Whatever `renderGraph` already applied — the restored one, or the fit.
  let box = readViewBox(svg);
  const publish = () => {
    applyViewBox(svg, box);
    onViewBox(box);
  };

  svg.addEventListener('wheel', (event) => {
    event.preventDefault();
    const scale = event.deltaY < 0 ? 1 / ZOOM_STEP : ZOOM_STEP;
    const next = box.width * scale;
    if (next < fitted.width / MAX_SCALE || next > fitted.width / MIN_SCALE) return;
    // Zoom about the pointer: the graph coordinate under the cursor is the one
    // that must not move.
    const point = toGraph(svg, box, event);
    box = {
      x: point.x - (point.x - box.x) * scale,
      y: point.y - (point.y - box.y) * scale,
      width: box.width * scale,
      height: box.height * scale,
    };
    publish();
  }, { passive: false });

  svg.addEventListener('pointerdown', (event) => {
    if (event.button !== 0) return;
    const origin = toGraph(svg, box, event);
    svg.setPointerCapture(event.pointerId);
    svg.classList.add('panning');
    const move = (moved) => {
      const now = toGraph(svg, box, moved);
      box = { ...box, x: box.x + (origin.x - now.x), y: box.y + (origin.y - now.y) };
      publish();
    };
    const release = () => {
      svg.classList.remove('panning');
      svg.removeEventListener('pointermove', move);
      svg.removeEventListener('pointerup', release);
      svg.removeEventListener('pointercancel', release);
    };
    svg.addEventListener('pointermove', move);
    svg.addEventListener('pointerup', release);
    svg.addEventListener('pointercancel', release);
  });

  svg.addEventListener('dblclick', () => {
    box = { ...fitted };
    publish();
  });
}

function readViewBox(svg) {
  const { x, y, width, height } = svg.viewBox.baseVal;
  return { x, y, width, height };
}

/** Where a pointer event is, in the drawing's own coordinates. */
function toGraph(svg, box, event) {
  const frame = svg.getBoundingClientRect();
  return {
    x: box.x + ((event.clientX - frame.left) / frame.width) * box.width,
    y: box.y + ((event.clientY - frame.top) / frame.height) * box.height,
  };
}

/** An SVG element — its own namespace, which is why `ui.js`'s is not this one. */
function element(tag, className) {
  const node = document.createElementNS(SVG_NS, tag);
  node.setAttribute('class', className);
  return node;
}
