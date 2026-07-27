#!/usr/bin/env node
/**
 * The graph layout's determinism invariant, checked directly.
 *
 * **Dev-only.** This file is not embedded in the binary and is never served —
 * `frontend.rs`'s `ASSETS` table is the whole shipped surface, and it lists
 * only `assets/`. It lives beside the crate's Rust tests, in a subdirectory so
 * that cargo (which compiles `tests/*.rs`) ignores it, and is run by hand:
 *
 *     node crates/als-sterling/tests/frontend/layout-determinism.mjs
 *
 * It exits 0 when the invariant holds and 1 with a diff-shaped message when it
 * does not. It is not wired into `cargo test` on purpose: that would make the
 * suite depend on a node installation the project otherwise does not need.
 * (node warns `MODULE_TYPELESS_PACKAGE_JSON` on the way in, because there is no
 * `package.json` next to `assets/` declaring those `.js` files as ES modules —
 * the served page has no such question to answer, since the server states
 * `text/javascript` and the shell loads them with `type="module"`.)
 *
 * What it pins (`assets/layout.js`'s module docs state the invariant):
 *
 * 1. **Idempotence** — laying the same state out twice is byte-identical.
 * 2. **Identity independence** — a structurally equal state built from
 *    *different objects* lays out identically, which is what rules out any
 *    ordering that leaked from object identity or from a `Map`/`Set` iteration.
 * 3. **Order sensitivity, deliberately** — permuting the document order of the
 *    sigs *does* change the drawing. That is not a determinism failure: the
 *    writer's order is itself deterministic, and the layout is a function of
 *    the whole input including it. Asserted so that nobody "fixes" it into a
 *    sort and quietly changes every picture.
 */

import { layoutGraph } from '../../assets/layout.js';

/** A state shaped like `instance.js` produces: sigs, fields, skolems, index. */
function state({ swapSigs = false } = {}) {
  const sigs = [
    sig('4', 'this/Node', ['Node$0', 'Node$1', 'Node$2']),
    sig('5', 'this/Colour', ['Red$0', 'Green$0']),
  ];
  if (swapSigs) sigs.reverse();
  const fields = [
    relation('6', 'next', '4', [
      ['Node$0', 'Node$1'],
      ['Node$1', 'Node$2'],
      // A cycle, so the back-edge pass runs; a self-loop and a parallel edge,
      // so the routing cases do too.
      ['Node$2', 'Node$0'],
      ['Node$0', 'Node$0'],
      ['Node$0', 'Node$1'],
    ]),
    // Arity 3: drawn first column to last, middle atom in the label.
    relation('7', 'tint', '4', [['Node$0', 'Red$0', 'Node$2']]),
  ];
  const skolems = [
    relation('8', '$witness', null, [['Node$1']]),
    relation('9', '$pair', null, [['Node$1', 'Green$0']]),
  ];
  return {
    sigs,
    fields,
    skolems,
    sigsById: new Map(sigs.map((entry) => [entry.id, entry])),
  };
}

function sig(id, label, atoms) {
  return { id, label, parentId: '2', flags: [], subsetOf: [], atoms };
}

function relation(id, label, parentId, tuples) {
  return { id, label, parentId, flags: [], typeGroups: [], tuples };
}

const options = { showBuiltins: false };
const draw = (input) => JSON.stringify(layoutGraph(input, options));

let failures = 0;
const check = (name, condition, detail) => {
  if (condition) {
    console.log(`ok   ${name}`);
    return;
  }
  failures += 1;
  console.error(`FAIL ${name}\n     ${detail}`);
};

const first = draw(state());
const second = draw(state());
check('the same state lays out identically twice', first === second, difference(first, second));

// Two independently-built states: every object differs, the content does not.
check(
  'a structurally equal state built from different objects lays out identically',
  draw(state()) === first,
  'object identity reached the geometry',
);

check(
  'permuting document order is a different (still deterministic) drawing',
  draw(state({ swapSigs: true })) !== first,
  'sig order stopped mattering — the layout is sorting its input somewhere',
);
check(
  'and that permutation is itself stable',
  draw(state({ swapSigs: true })) === draw(state({ swapSigs: true })),
  'the permuted layout is not reproducible',
);

// Coordinates reach the output as short decimals rather than binary fractions,
// which is what makes the comparisons above textual rather than approximate.
const geometry = layoutGraph(state(), options);
const coordinates = geometry.nodes.flatMap((node) => [node.x, node.y, node.width]);
check(
  'every coordinate is rounded at the boundary',
  coordinates.every((value) => Math.abs(value * 100 - Math.round(value * 100)) < 1e-9),
  `unrounded coordinates: ${coordinates.filter((v) => Math.abs(v * 100 - Math.round(v * 100)) >= 1e-9)}`,
);

function difference(left, right) {
  for (let index = 0; index < Math.max(left.length, right.length); index += 1) {
    if (left[index] !== right[index]) {
      return `first difference at ${index}: ${left.slice(index, index + 60)} vs ${right.slice(index, index + 60)}`;
    }
  }
  return 'no textual difference';
}

process.exit(failures === 0 ? 0 : 1);
