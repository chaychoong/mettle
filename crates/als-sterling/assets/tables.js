/**
 * The table view: one card per signature and per relation of the displayed
 * state.
 *
 * This is the workhorse view — the one that answers "what is actually in this
 * instance" without a layout algorithm between the reader and the data. It
 * renders exactly what the XML says, in the order the writer wrote it (which
 * is deterministic, `alloy6-instance-xml.md` §2), and derives nothing: a
 * signature's card carries the atoms that block listed *under that sig*, which
 * is the same partitioning `mettle exec` prints (an atom appears under its
 * most specific sig, §2), not a recomputed transitive extent.
 *
 * DOM is built with `document.createElement` throughout: atom labels can be
 * string literals carrying arbitrary characters (§4), and an innerHTML
 * template would make that a rendering hazard for no gain.
 */

import { columnLabels, isHiddenRelation, isHiddenSig, shortLabel } from './instance.js';

/** Renders one state into `container`, replacing whatever was there. */
export function renderState(container, state, { showBuiltins }) {
  const keep = (item, hidden) => showBuiltins || !hidden(item);
  const sigs = state.sigs.filter((sig) => keep(sig, isHiddenSig));
  const fields = state.fields.filter((field) => keep(field, (f) => isHiddenRelation(f, state.sigsById)));
  const skolems = state.skolems.filter((skolem) => keep(skolem, (s) => isHiddenRelation(s, state.sigsById)));

  const groups = [];
  groups.push(group('Signatures', sigs.length, sigs.map((sig) => sigCard(sig, state.sigsById))));
  if (fields.length > 0) {
    groups.push(group('Relations', fields.length, fields.map((field) => relationCard(field, state.sigsById, fieldTitle(field, state.sigsById)))));
  }
  if (skolems.length > 0) {
    // Skolems are the witnesses the solver chose for the command's own
    // existentials; they belong beside the model's relations but are not part
    // of it, so they get their own group rather than being mixed in.
    groups.push(group('Skolems', skolems.length, skolems.map((skolem) => relationCard(skolem, state.sigsById, shortLabel(skolem.label)))));
  }
  if (sigs.length === 0 && fields.length === 0 && skolems.length === 0) {
    groups.push(notice('This state has nothing to show with the current filter.'));
  }
  container.replaceChildren(...groups);
}

function group(title, count, cards) {
  const section = element('section', 'group');
  const head = element('div', 'group-head');
  head.append(element('h2', null, title), element('span', 'count', String(count)));
  const grid = element('div', 'cards');
  grid.append(...cards);
  section.append(head, grid);
  return section;
}

function sigCard(sig, sigsById) {
  const card = element('div', 'card');
  card.append(cardHead(shortLabel(sig.label), sig.flags, `${sig.atoms.length}`));
  const parentage = sigParentage(sig, sigsById);
  if (parentage !== null) card.append(element('div', 'card-sub', parentage));
  card.append(sig.atoms.length === 0
    ? element('div', 'empty', 'no atoms')
    : table(['atom'], sig.atoms.map((atom) => [atom])));
  return card;
}

function relationCard(relation, sigsById, title) {
  const card = element('div', 'card');
  const columns = columnLabels(relation, sigsById);
  card.append(cardHead(title, relation.flags, `${relation.tuples.length}`));
  card.append(relation.tuples.length === 0
    ? element('div', 'empty', 'no tuples')
    : table(columns, relation.tuples));
  return card;
}

/** `Node.color` — a field is named by its owner, which is its first column. */
function fieldTitle(field, sigsById) {
  const owner = field.parentId === null ? undefined : sigsById.get(field.parentId);
  const prefix = owner === undefined ? '' : `${shortLabel(owner.label)}.`;
  return `${prefix}${field.label}`;
}

/** `extends Color` / `in A + B` — the one line of structure a sig's atoms don't carry. */
function sigParentage(sig, sigsById) {
  if (sig.subsetOf.length > 0) {
    const parents = sig.subsetOf.map((id) => shortLabel(sigsById.get(id)?.label ?? '?'));
    return `in ${parents.join(' + ')}`;
  }
  const parent = sig.parentId === null ? undefined : sigsById.get(sig.parentId);
  if (parent === undefined || parent.label === 'univ') return null;
  return `extends ${shortLabel(parent.label)}`;
}

function cardHead(title, flags, count) {
  const head = element('div', 'card-head');
  head.append(element('span', 'card-title', title));
  for (const flag of flags) {
    // `builtin` is what the filter is about, not something to label every row
    // with; the rest are declarations a reader wants to see.
    if (flag !== 'builtin') head.append(element('span', 'flag', flag));
  }
  head.append(element('span', 'card-arity', count));
  return head;
}

function table(columns, rows) {
  const node = document.createElement('table');
  const head = document.createElement('thead');
  const headRow = document.createElement('tr');
  for (const column of columns) {
    const cell = document.createElement('th');
    cell.textContent = column;
    headRow.append(cell);
  }
  head.append(headRow);
  const body = document.createElement('tbody');
  for (const row of rows) {
    const bodyRow = document.createElement('tr');
    for (const value of row) {
      const cell = document.createElement('td');
      cell.textContent = value;
      bodyRow.append(cell);
    }
    body.append(bodyRow);
  }
  node.append(head, body);
  return node;
}

function notice(text) {
  return element('p', 'notice', text);
}

function element(tag, className, text) {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
}
