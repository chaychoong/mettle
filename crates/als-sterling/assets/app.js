/**
 * `mettle serve`'s frontend (mt-075): the shell that wires the provider
 * connection to the trace stepper, the table view, the evaluator pane, and the
 * provider's own action buttons.
 *
 * Three rules shape everything here:
 *
 * 1. **The provider owns the actions.** Buttons are rendered from the
 *    `buttons` list the server sends with each datum and nothing else — no
 *    verb is hardcoded, so a verb that retires server-side (an exhausted
 *    enumeration) simply stops being offered. The one exception is spelled out
 *    at `isBlocked`, and it hides a button the server would refuse anyway.
 * 2. **Stepping is client-side.** A temporal `data` payload is the whole
 *    lasso, so moving between states is a re-render, never a request. The one
 *    thing the server has to be told is which state a `new-fork` should fork
 *    after, which rides the `click` payload's optional `state` field.
 * 3. **The evaluator sits at the displayed state.** The reference GUI's
 *    visualizer and console share one `current` index
 *    (`alloy6-temporal.md` §(h)); here the stepper is that index, and the pane
 *    is moved to it with the REPL's own `:state N` before an expression is
 *    evaluated — lazily, so merely stepping through a trace costs no traffic.
 * 4. **The views are projections of one state, not modes.** `view.step` and
 *    the builtins toggle are the single source of truth; graph and table are
 *    two renderings of it, so switching views changes nothing but the
 *    rendering — and everything else (stepper, buttons, evaluator) is
 *    identical either way.
 */

import { countHidden, normalizeState, parseInstanceXml } from './instance.js';
import { renderGraph } from './graph.js';
import { layoutGraph } from './layout.js';
import { connectProvider } from './protocol.js';
import { renderState } from './tables.js';

const dom = {
  status: document.getElementById('status'),
  command: document.getElementById('command'),
  actions: document.getElementById('actions'),
  showBuiltins: document.getElementById('show-builtins'),
  hiddenNote: document.getElementById('hidden-note'),
  stepper: document.getElementById('stepper'),
  states: document.getElementById('states'),
  loopNote: document.getElementById('loop-note'),
  instance: document.getElementById('instance'),
  evaluator: document.getElementById('evaluator'),
  evaluatorState: document.getElementById('evaluator-state'),
  history: document.getElementById('history'),
  prompt: document.getElementById('prompt'),
  expression: document.getElementById('expression'),
  views: document.getElementById('views'),
  toasts: document.getElementById('toasts'),
};

const view = {
  /** The datum on screen, as the provider described it. */
  datum: null,
  /** Its parsed XML, or `null` if it did not parse. */
  instance: null,
  /** The displayed state index — the client-side half of the trace stepper. */
  step: 0,
  /** The state the provider's evaluator pane is known to sit at (it starts at 0). */
  evaluatorState: 0,
  /** True between sending a `click` and the `data`/`error` that answers it. */
  busy: false,
  /**
   * `graph` or `table`. The graph opens first, as the reference GUI does —
   * the picture is what an instance is usually read as, and the table is one
   * click away for when it is not.
   */
  mode: 'graph',
  /**
   * The graph's pan/zoom, or `null` for "fit the drawing".
   *
   * Kept across a state step (comparing two states of a trace at the same
   * magnification is the point of a stepper) and dropped when the datum
   * changes, where the old window would be over a different drawing.
   */
  viewBox: null,
};

const provider = connectProvider(providerUrl(), {
  onStatus: showStatus,
  onMeta: showMeta,
  onDatum: showDatum,
  onError: showError,
});

/** The socket lives on this page's own origin (`server.rs` routes on `Upgrade`). */
function providerUrl() {
  const scheme = window.location.protocol === 'https:' ? 'wss:' : 'ws:';
  return `${scheme}//${window.location.host}/ws`;
}

function showStatus(state) {
  dom.status.dataset.state = state;
  dom.status.textContent = state;
}

function showMeta(meta) {
  if (typeof meta.generators?.[0] === 'string') dom.command.textContent = meta.generators[0];
  // A provider that offers no evaluator gets no evaluator pane, rather than a
  // pane whose every expression is refused.
  dom.evaluator.hidden = meta.evaluator === false;
}

function showDatum(datum) {
  const advanced = view.datum !== null && view.datum.id !== datum.id;
  const rerun = view.datum !== null && view.datum.id === datum.id;
  view.datum = datum;
  view.busy = false;
  if (!rerun) {
    // A *new* datum is a freshly built evaluator on the provider's side, and
    // that one starts at state 0 (`serve/session.rs`). The same datum arriving
    // again — a reconnect, or another tab's refresh — moved nothing, so where
    // this page was looking still holds.
    view.step = 0;
    view.evaluatorState = 0;
    view.viewBox = null;
  }
  try {
    view.instance = parseInstanceXml(datum.data ?? '');
  } catch (failure) {
    view.instance = null;
    showError({ code: 'unparseable-instance', message: failure.message });
  }
  if (advanced) appendHistory('note', `— now showing ${datum.id} —`);
  render();
}

function showError({ code, message }) {
  view.busy = false;
  renderActions();
  const toast = document.createElement('div');
  toast.className = 'toast';
  const label = document.createElement('span');
  label.className = 'code';
  label.textContent = code;
  toast.append(label, document.createTextNode(message));
  toast.addEventListener('click', () => toast.remove());
  dom.toasts.append(toast);
  setTimeout(() => toast.remove(), 9000);
}

/* ---------- rendering ---------- */

function render() {
  renderActions();
  renderStepper();
  renderInstance();
  renderEvaluatorState();
}

function renderActions() {
  const buttons = view.datum?.buttons ?? [];
  dom.actions.replaceChildren(...buttons.map((button) => {
    const node = document.createElement('button');
    node.type = 'button';
    node.textContent = button.text;
    if (button.mouseover) node.title = button.mouseover;
    const blocked = isBlocked(button.onClick);
    node.disabled = view.busy || blocked !== null;
    if (blocked !== null) node.title = blocked;
    node.addEventListener('click', () => act(button.onClick));
    return node;
  }));
}

/**
 * Why a button cannot be pressed right now, or `null`.
 *
 * The single case: forking *after* the last state of a lasso has nowhere to go
 * — the provider refuses it unconditionally (mt-076 probe P-076-6), and it
 * cannot know from here which state is displayed until the click carries it.
 * Disabling locally is the same "absent, never wrong" discipline the provider
 * applies to its own button list.
 */
function isBlocked(onClick) {
  if (onClick !== 'new-fork' || view.instance === null || !view.instance.temporal) return null;
  return view.step + 1 < view.instance.traceLength
    ? null
    : 'a fork after the last state of the trace has nowhere to go';
}

function act(onClick) {
  if (view.busy || view.datum === null) return;
  view.busy = true;
  renderActions();
  // Only `new-fork` reads the displayed state; every other verb asks a
  // question the state index has no bearing on, and sending it anyway would
  // suggest otherwise.
  const state = onClick === 'new-fork' ? view.step : undefined;
  if (!provider.click(view.datum.id, onClick, state)) {
    // Nothing was sent, so nothing will answer — the buttons must come back
    // rather than sit disabled waiting for a reply that cannot arrive.
    showError({ code: 'not-connected', message: 'the provider connection is down; the action was not sent.' });
  }
}

function renderStepper() {
  const instance = view.instance;
  dom.stepper.hidden = instance === null || !instance.temporal;
  if (dom.stepper.hidden) return;

  dom.states.replaceChildren(...Array.from({ length: instance.traceLength }, (unused, index) => {
    const chip = document.createElement('button');
    chip.type = 'button';
    chip.className = index === instance.loopState ? 'state-chip loop-target' : 'state-chip';
    chip.textContent = `state ${index}`;
    chip.setAttribute('role', 'tab');
    chip.setAttribute('aria-selected', String(index === view.step));
    if (index === instance.loopState) chip.title = 'the trace loops back to this state';
    chip.addEventListener('click', () => step(index));
    return chip;
  }));
  dom.loopNote.textContent = loopNote(instance);
}

/** What the lasso does at its end, said in words next to the chips. */
function loopNote(instance) {
  const last = instance.traceLength - 1;
  if (instance.loopState === null) return '';
  if (instance.loopState === last) return `state ${last} repeats forever`;
  return `state ${last} loops back to state ${instance.loopState}`;
}

function renderInstance() {
  for (const button of dom.views.querySelectorAll('button')) {
    button.setAttribute('aria-pressed', String(button.dataset.view === view.mode));
  }
  if (view.instance === null) {
    dom.instance.replaceChildren(notice('This datum did not parse as Alloy instance XML.'));
    dom.hiddenNote.textContent = '';
    return;
  }
  const state = view.instance.states[view.step];
  const options = { showBuiltins: dom.showBuiltins.checked };
  if (view.mode === 'graph') {
    renderGraph(dom.instance, layoutGraph(state, options), {
      viewBox: view.viewBox,
      onViewBox: (box) => {
        view.viewBox = box;
      },
    });
  } else {
    renderState(dom.instance, state, options);
  }
  const hidden = options.showBuiltins ? 0 : countHidden(state);
  dom.hiddenNote.textContent = hidden === 0 ? '' : `${hidden} builtin/private hidden`;
}

function renderEvaluatorState() {
  dom.evaluatorState.textContent = view.instance?.temporal ? `at state ${view.step}` : '';
}

function step(index) {
  if (view.instance === null || index === view.step) return;
  view.step = index;
  render();
}

function notice(text) {
  const node = document.createElement('p');
  node.className = 'notice';
  node.textContent = text;
  return node;
}

/* ---------- evaluator ---------- */

dom.prompt.addEventListener('submit', (event) => {
  event.preventDefault();
  const expression = dom.expression.value.trim();
  if (expression === '') return;
  dom.expression.value = '';
  evaluate(expression);
});

dom.expression.addEventListener('keydown', (event) => {
  if (event.key === 'Enter' && !event.shiftKey) {
    event.preventDefault();
    dom.prompt.requestSubmit();
  }
});

async function evaluate(expression) {
  if (view.datum === null) return;
  appendHistory('input', expression);
  const typedMove = statePragma(expression);
  try {
    // The user's own `:state N` wins over the stepper's position — it *is* the
    // move, so syncing first would send two of them.
    if (typedMove === null) await syncEvaluatorState();
    appendHistory('result', await provider.evaluate(view.datum.id, expression));
    if (typedMove !== null) applyTypedMove(typedMove);
  } catch (failure) {
    appendHistory('failed', failure.message);
  }
}

/**
 * Moves the provider's evaluator to the displayed state, if it isn't there.
 *
 * Not shown in the history: it is not something the user typed, and the pane's
 * own header already says which state expressions are answered at.
 */
async function syncEvaluatorState() {
  if (view.instance === null || !view.instance.temporal) return;
  if (view.evaluatorState === view.step) return;
  await provider.evaluate(view.datum.id, `:state ${view.step}`);
  view.evaluatorState = view.step;
}

/** A hand-typed `:state N`, so the stepper can follow it (rule 3 in the module docs). */
function statePragma(expression) {
  const match = /^:state\s+(-?\d+)\s*$/.exec(expression);
  return match === null ? null : Number.parseInt(match[1], 10);
}

function applyTypedMove(requested) {
  if (view.instance === null || !view.instance.temporal) return;
  // The provider normalizes an out-of-range index rather than refusing it
  // (`alloy6-temporal.md` §(h)); the stepper has to land where it landed.
  const landed = normalizeState(requested, view.instance.traceLength, view.instance.loopState);
  view.evaluatorState = landed;
  step(landed);
  renderEvaluatorState();
}

function appendHistory(kind, text) {
  // The shell's standing hint is the pane's empty state; the first real entry
  // is what it was waiting for.
  document.getElementById('hint')?.remove();
  const entry = document.createElement('div');
  entry.className = `entry ${kind}`;
  entry.textContent = text;
  dom.history.append(entry);
  dom.history.scrollTop = dom.history.scrollHeight;
}

/* ---------- global affordances ---------- */

dom.showBuiltins.addEventListener('change', () => {
  // The filter changes what is drawn, so a pan/zoom taken over the old drawing
  // no longer frames anything in particular.
  view.viewBox = null;
  renderInstance();
});

dom.views.addEventListener('click', (event) => {
  const chosen = event.target.closest('button')?.dataset.view;
  if (chosen === undefined || chosen === view.mode) return;
  view.mode = chosen;
  renderInstance();
});

document.addEventListener('keydown', (event) => {
  const typing = event.target instanceof HTMLTextAreaElement || event.target instanceof HTMLInputElement;
  if (typing || view.instance === null || !view.instance.temporal) return;
  if (event.key === 'ArrowLeft') step(Math.max(0, view.step - 1));
  if (event.key === 'ArrowRight') step(Math.min(view.instance.traceLength - 1, view.step + 1));
});

window.addEventListener('beforeunload', () => provider.close());

provider.start();
