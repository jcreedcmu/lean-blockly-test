import * as blockly from 'blockly';

/**
 * Shared renderer for the marker pill — the small selectable oblong used by
 * both `FieldGoalMarker` and `FieldProofStatus`. It is just the pill shape
 * (no label): white when unselected, blue when selected. Anything else (e.g.
 * a status decoration) is drawn by the field alongside it.
 */

export const PILL_WIDTH = 26;
export const PILL_HEIGHT = 14;

/** Create the marker pill (a rounded rect) inside a field group. */
export function createPill(parent: SVGGElement): SVGRectElement {
  return blockly.utils.dom.createSvgElement(
    blockly.utils.Svg.RECT,
    {
      'x': '0', 'y': '0',
      'width': String(PILL_WIDTH), 'height': String(PILL_HEIGHT),
      'rx': String(PILL_HEIGHT / 2), 'ry': String(PILL_HEIGHT / 2),
      'stroke-width': '1',
    },
    parent,
  ) as SVGRectElement;
}

/** Style the marker pill: white when unselected, blue when selected. */
export function updatePill(bg: SVGRectElement, selected: boolean): void {
  bg.setAttribute('fill', selected ? '#1565c0' : '#ffffff');
  bg.setAttribute('stroke', selected ? '#1565c0' : '#888888');
}

/**
 * Briefly flash the pill with the shared red error glow — the same effect used
 * for block flashes (the `flashError` class in App.css). Adds the class, then
 * removes it after the animation. Leaves the pill's own fill/decoration intact.
 */
export function flashPillError(bg: SVGRectElement): void {
  bg.classList.add('flashError');
  setTimeout(() => bg.classList.remove('flashError'), 700);
}
