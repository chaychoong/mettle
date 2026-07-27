/**
 * Alloy instance XML -> the small model everything else in the app renders.
 *
 * This module is pure: it touches `DOMParser` and nothing else — no network,
 * no document, no state. Every fact the rest of the app knows about the shape
 * of an instance is derived here, so no rendering code ever walks an XML node.
 *
 * The schema is `docs/reference/alloy6-instance-xml.md`; four of its findings
 * are load-bearing here and are the invariants this module maintains:
 *
 * - **§7 — the physical `<instance>` block count is NOT `tracelength`.** A
 *   model with a reachable zero-arg `fun` of nonzero past depth makes the
 *   writer emit `tracelength + extra*(tracelength - loopState)` blocks: the
 *   extra ones are unrolled further passes through the loop, the mechanism
 *   that feeds those macros, *not* states of the trace. Only the first
 *   `tracelength` blocks are states, and only those are exposed as
 *   `states[]`; the rest are counted into `extraBlocks` and dropped.
 * - **§1 — `looplength = tracelength - loopState`** (the reference jar's
 *   dialect, which is what mettle's own server writes). Sterling's upstream
 *   parser reads `backloop`/`loop` instead and never `looplength`
 *   (`docs/reference/sterling.md` §2.4); that dialect is an adapter for
 *   external clients and never reaches this frontend, so it is deliberately
 *   not parsed here.
 * - **§1 — `mintrace="-1"` is the static-command sentinel**, and is how a
 *   static instance is told from a one-state trace.
 * - **§2/§5 — `<field>`/`<skolem>` carry one `<types>` element per
 *   `Type.fold()` entry**, so a union-typed relation has several; the column
 *   headers are therefore the union of each group's label for that column,
 *   not the first group's.
 *
 * Element order is preserved everywhere: the writer's order is deterministic
 * (its lazy-memoized touch order, §2), so preserving it makes two renders of
 * the same instance identical.
 */

/** `mintrace`/`maxtrace` for a command with no temporal dimension (§1). */
const STATIC_SENTINEL = -1;

/** Every boolean-ish `<sig>` attribute the schema defines (§3), in print order. */
const SIG_FLAGS = [
  'builtin', 'abstract', 'one', 'lone', 'some',
  'private', 'meta', 'exact', 'enum', 'var',
];

/** The same, for `<field>`/`<skolem>` (§5). */
const RELATION_FLAGS = ['private', 'meta', 'var'];

/**
 * Parses one `data` payload.
 *
 * Throws an `Error` naming the problem if the document is not instance XML —
 * a malformed datum is shown to the user, never swallowed.
 */
export function parseInstanceXml(text) {
  const doc = new DOMParser().parseFromString(text, 'application/xml');
  const failure = doc.querySelector('parsererror');
  if (failure) {
    throw new Error(`the instance XML did not parse: ${failure.textContent.trim()}`);
  }
  const blocks = childrenNamed(doc.documentElement, 'instance');
  if (blocks.length === 0) {
    throw new Error('the instance XML carries no <instance> element');
  }

  // Every block repeats these identically (§1), so the first is authoritative.
  const head = blocks[0];
  const declaredLength = numberAttribute(head, 'tracelength') ?? blocks.length;
  const stateCount = Math.max(1, Math.min(declaredLength, blocks.length));
  const states = blocks.slice(0, stateCount).map(parseState);
  const minTrace = numberAttribute(head, 'mintrace') ?? STATIC_SENTINEL;

  return {
    command: head.getAttribute('command') ?? '',
    filename: head.getAttribute('filename') ?? '',
    bitwidth: numberAttribute(head, 'bitwidth'),
    maxSeq: numberAttribute(head, 'maxseq'),
    temporal: minTrace !== STATIC_SENTINEL,
    traceLength: states.length,
    loopState: loopTarget(states.length, numberAttribute(head, 'looplength')),
    /** Blocks past `tracelength` — the §7 macro mechanism, never displayed. */
    extraBlocks: blocks.length - states.length,
    states,
  };
}

/**
 * The state a trace loops back to, from the jar's `looplength` encoding.
 *
 * `null` when the attribute is absent or describes a target outside the trace:
 * a loop marker the document does not support is not drawn, rather than drawn
 * in the wrong place.
 */
function loopTarget(traceLength, loopLength) {
  if (loopLength === null || loopLength === undefined) return null;
  const target = traceLength - loopLength;
  return Number.isInteger(target) && target >= 0 && target < traceLength ? target : null;
}

/**
 * The evaluator's state-index rule (`als_core::normalize_state`, pinned in
 * `docs/reference/alloy6-temporal.md` §(h)): a negative index clamps to 0, an
 * index at or past the end wraps through the loop. Never an error.
 *
 * Kept here rather than at a call site because the app has to agree with the
 * server about what `:state 7` means on a 3-state lasso.
 */
export function normalizeState(index, traceLength, loopState) {
  const clamped = Math.max(0, Math.trunc(index));
  const loop = loopState ?? 0;
  if (clamped <= loop) return clamped;
  return ((clamped - loop) % (traceLength - loop)) + loop;
}

function parseState(element) {
  const sigs = [];
  const fields = [];
  const skolems = [];
  for (const child of element.children) {
    if (child.tagName === 'sig') sigs.push(parseSig(child));
    else if (child.tagName === 'field') fields.push(parseRelation(child));
    else if (child.tagName === 'skolem') skolems.push(parseRelation(child));
  }
  return { sigs, fields, skolems, sigsById: new Map(sigs.map((sig) => [sig.id, sig])) };
}

function parseSig(element) {
  const atoms = [];
  const subsetOf = [];
  for (const child of element.children) {
    if (child.tagName === 'atom') atoms.push(child.getAttribute('label') ?? '');
    // §3: a subset sig has no `parentID`; its parents are `<type>` children,
    // which is how multi-parent `sig X in A + B` is encoded.
    else if (child.tagName === 'type') subsetOf.push(child.getAttribute('ID') ?? '');
  }
  return {
    id: element.getAttribute('ID') ?? '',
    label: element.getAttribute('label') ?? '',
    parentId: element.getAttribute('parentID'),
    flags: flagsOf(element, SIG_FLAGS),
    subsetOf,
    atoms,
  };
}

function parseRelation(element) {
  const tuples = [];
  const typeGroups = [];
  for (const child of element.children) {
    if (child.tagName === 'tuple') {
      tuples.push(childrenNamed(child, 'atom').map((atom) => atom.getAttribute('label') ?? ''));
    } else if (child.tagName === 'types') {
      typeGroups.push(childrenNamed(child, 'type').map((type) => type.getAttribute('ID') ?? ''));
    }
  }
  return {
    id: element.getAttribute('ID') ?? '',
    label: element.getAttribute('label') ?? '',
    /** The owning sig for a `<field>`; absent for a `<skolem>` (§5, §6). */
    parentId: element.getAttribute('parentID'),
    flags: flagsOf(element, RELATION_FLAGS),
    typeGroups,
    tuples,
  };
}

/**
 * The column headers of a relation: one short sig label per column, unioned
 * across `<types>` groups (§5) and falling back to `univ` when a column's type
 * id names a sig this state does not carry.
 */
export function columnLabels(relation, sigsById) {
  const arity = relation.tuples[0]?.length ?? relation.typeGroups[0]?.length ?? 0;
  const labels = [];
  for (let column = 0; column < arity; column += 1) {
    const names = [];
    for (const group of relation.typeGroups) {
      const name = shortLabel(sigsById.get(group[column])?.label ?? '');
      if (name && !names.includes(name)) names.push(name);
    }
    labels.push(names.length > 0 ? names.join(' + ') : '·');
  }
  return labels;
}

/**
 * A sig's display name: `this/Node` -> `Node`, while a namespaced label from
 * another module (`ordering/Ord`, `seq/Int`) keeps its qualifier, which is the
 * only thing that tells two same-named sigs apart.
 */
export function shortLabel(label) {
  return label.startsWith('this/') ? label.slice('this/'.length) : label;
}

/**
 * Whether a sig is hidden unless "show builtins" is on.
 *
 * Two kinds: the four `builtin` sigs (`univ`, `Int`, `seq/Int`, `String` — the
 * first three structurally never carry atoms at all, §3), and `private` sigs,
 * which is what the machinery a model never wrote is marked as — the
 * `ordering/Ord` sig an `enum` injects (§3) and `util/ordering`'s own
 * structure. The reference visualizer hides both by default too.
 */
export function isHiddenSig(sig) {
  return sig.flags.includes('builtin') || sig.flags.includes('private');
}

/** The same rule for a relation: its own `private`, or its owner's. */
export function isHiddenRelation(relation, sigsById) {
  if (relation.flags.includes('private')) return true;
  const owner = relation.parentId === null ? undefined : sigsById.get(relation.parentId);
  return owner !== undefined && isHiddenSig(owner);
}

/**
 * Whether a skolem is a **macro** skolem rather than a witness the solver
 * chose.
 *
 * Two independent mechanisms share the `<skolem>` element (§6). One is the real
 * thing: an existential's witness, named `$x`/`$cmd_x`. The other is
 * bookkeeping the writer synthesizes for *every* reachable zero-arg relational
 * `fun` in the model — `$ordering/next`, `$this/Best` — which is why a model
 * that opens `util/ordering` has most of its atoms mentioned by some skolem.
 * They are told apart by their ID: macros come from a separate `m<i>`
 * namespace, ordinary skolems from the shared numeric one.
 *
 * The distinction is worth drawing precisely because of that reach: marking
 * every atom a macro mentions as "a solver-chosen witness" would mark nearly
 * all of them, and a marker that is always on says nothing.
 */
export function isMacroSkolem(relation) {
  return relation.id.startsWith('m');
}

/**
 * How many sigs and relations the builtin filter is currently keeping out of a
 * state. Shared by both views, so the toolbar's count means the same thing in
 * each.
 */
export function countHidden(state) {
  const sigs = state.sigs.filter(isHiddenSig).length;
  const relations = [...state.fields, ...state.skolems]
    .filter((relation) => isHiddenRelation(relation, state.sigsById)).length;
  return sigs + relations;
}

function flagsOf(element, names) {
  // The schema writes presence only (`attr="yes"`, never `attr="no"`, §3).
  return names.filter((name) => element.getAttribute(name) === 'yes');
}

function childrenNamed(element, tagName) {
  return Array.from(element.children).filter((child) => child.tagName === tagName);
}

function numberAttribute(element, name) {
  const raw = element.getAttribute(name);
  if (raw === null) return null;
  const value = Number.parseInt(raw, 10);
  return Number.isNaN(value) ? null : value;
}
