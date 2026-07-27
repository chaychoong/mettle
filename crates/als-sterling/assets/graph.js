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
 * datum, and `app.css` decides what lightness it gets in light and in dark.
 */

import { tagLine } from './layout.js';

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
    container.replaceChildren(notice('This state has no atoms to draw.'));
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
  container.replaceChildren(svg);
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
  for (const edge of layout.edges) {
    const group = element('g', edgeClass(edge));
    const line = document.createElementNS(SVG_NS, 'path');
    line.setAttribute('d', edge.path);
    line.setAttribute('marker-end', edge.back ? 'url(#arrow-back)' : 'url(#arrow)');
    group.append(line, text(edge.label, edge.labelAt.x, edge.labelAt.y, 'edge-label'));
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
    // `-1` is an atom no visible sig lists (an integer, a filtered-out sig's
    // atom reached through a relation): no hue, so it reads as outside the
    // model's own structure rather than as one more sig.
    if (node.sigIndex >= 0) group.style.setProperty('--hue', String(HUES[node.sigIndex % HUES.length]));
    else group.classList.add('unowned');

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

function element(tag, className) {
  const node = document.createElementNS(SVG_NS, tag);
  node.setAttribute('class', className);
  return node;
}

function notice(message) {
  const node = document.createElement('p');
  node.className = 'notice';
  node.textContent = message;
  return node;
}
