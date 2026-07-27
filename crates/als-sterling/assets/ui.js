/**
 * The two DOM helpers every view needs, in one place.
 *
 * Small on purpose: this is not a component library, it is the shared spelling
 * of the page's one empty-state shape and the element builder that avoids
 * `innerHTML`. Everything here writes text through `textContent`, because atom
 * labels are user-influenced text (a string literal's own quoted spelling, for
 * one) and a template would make that a rendering hazard for no gain.
 */

/** An HTML element with an optional class and text. */
export function element(tag, className, text) {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
}

/**
 * The page's empty state: a silkscreen label, then one sentence in mettle's own
 * voice saying what is not here and what to do about it.
 *
 * `alert` marks the ones that report a failure rather than an absence, which is
 * the only distinction the styling draws.
 */
export function blank(eyebrow, message, { alert = false } = {}) {
  const panel = element('div', alert ? 'blank alert' : 'blank');
  panel.append(element('span', 'eyebrow', eyebrow), element('p', null, message));
  return panel;
}
