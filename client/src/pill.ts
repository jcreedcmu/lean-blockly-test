import * as blockly from 'blockly';

/**
 * Shared rendering for the marker pills (`FieldProofStatus`, `FieldGoalMarker`)
 * so the two are visually identical in shape and size: a fixed 48×18 oblong
 * pill with an optional centered label and a selection ring.
 */

export const PILL_WIDTH = 26;
export const PILL_HEIGHT = 14;

export interface PillElements {
  bg: SVGRectElement;
  text: SVGTextElement;
}

export interface PillStyle {
  fill: string;
  fillOpacity?: string;
  /** Border/selection color (each field decides how selection looks). */
  stroke?: string;
  strokeWidth?: string;
  text?: string;
  textFill?: string;
  fontSize?: string;
}

/** Create the pill SVG (background + centered label) inside a field group. */
export function createPill(parent: SVGGElement): PillElements {
  const Svg = blockly.utils.Svg;
  const bg = blockly.utils.dom.createSvgElement(
    Svg.RECT,
    {
      'x': '0', 'y': '0',
      'width': String(PILL_WIDTH), 'height': String(PILL_HEIGHT),
      'rx': String(PILL_HEIGHT / 2), 'ry': String(PILL_HEIGHT / 2),
    },
    parent,
  ) as SVGRectElement;
  const text = blockly.utils.dom.createSvgElement(
    Svg.TEXT,
    {
      'x': String(PILL_WIDTH / 2), 'y': String(PILL_HEIGHT / 2),
      'dominant-baseline': 'central', 'text-anchor': 'middle',
      'font-weight': 'bold', 'pointer-events': 'none',
    },
    parent,
  ) as SVGTextElement;
  return { bg, text };
}

/** Apply colors/label to an existing pill. */
export function updatePill(els: PillElements, style: PillStyle): void {
  els.bg.setAttribute('fill', style.fill);
  els.bg.setAttribute('fill-opacity', style.fillOpacity ?? '1');
  els.bg.setAttribute('stroke', style.stroke ?? 'none');
  els.bg.setAttribute('stroke-width', style.strokeWidth ?? '0');
  els.text.textContent = style.text ?? '';
  els.text.setAttribute('fill', style.textFill ?? 'rgba(0,0,0,0)');
  els.text.setAttribute('font-size', style.fontSize ?? '12');
}
