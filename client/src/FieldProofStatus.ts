import * as blockly from 'blockly';
import { Field, FieldConfig } from 'blockly';
import { dispatchMarkerClick, GoalPositionMarker } from './goalMarker';
import { PILL_WIDTH, PILL_HEIGHT, createPill, updatePill } from './pill';

export type ProofStatus = 'unknown' | 'complete' | 'incomplete';

/** Gap (px) between the marker pill and the status decoration to its right. */
const DECORATION_GAP = 4;

type StatusDecoration = { text: string; fill: string };

/** The text decoration drawn to the right of the pill, conveying good/bad. */
const STATUS_DECORATION: Record<ProofStatus, StatusDecoration> = {
  complete: { text: '✓', fill: '#fff' },     // good
  incomplete: { text: '✕', fill: '#fff' },  // bad
  unknown: { text: '', fill: 'rgba(0,0,0,0)' }, // nothing yet
};

/**
 * Proof-position marker: the shared {@link createPill} marker pill (selectable,
 * white/blue, no label), plus a plain-text decoration to its right conveying
 * whether the proof is good (`✓`) or bad (`sorry`). The pill sits exactly where
 * the marker pill goes; the decoration overflows to the right of it. The custom
 * renderer centers the pill on the statement notch above.
 */
export class FieldProofStatus extends Field<string> implements GoalPositionMarker {
  private status_: ProofStatus = 'unknown';
  private pill_: SVGRectElement | null = null;
  private decoration_: SVGTextElement | null = null;
  // Goal-position-marker state.
  private target_ = '';
  private selected_ = false;

  EDITABLE = false;
  SERIALIZABLE = false;

  constructor() {
    super(Field.SKIP_SETUP);
  }

  protected initView(): void {
    this.pill_ = createPill(this.fieldGroup_ as SVGGElement);
    this.decoration_ = blockly.utils.dom.createSvgElement(
      blockly.utils.Svg.TEXT,
      {
        'x': String(PILL_WIDTH + DECORATION_GAP),
        'y': String(PILL_HEIGHT / 2),
        'dominant-baseline': 'central',
        'text-anchor': 'start',
        'font-weight': 'bold',
        'font-size': '12',
        'pointer-events': 'none',
      },
      this.fieldGroup_,
    ) as SVGTextElement;
    this.redraw_();
  }

  private redraw_(): void {
    if (this.pill_) updatePill(this.pill_, this.selected_);
    if (this.decoration_) {
      const d = STATUS_DECORATION[this.status_];
      this.decoration_.textContent = d.text;
      this.decoration_.setAttribute('fill', d.fill);
    }
  }

  setStatus(status: ProofStatus): void {
    this.status_ = status;
    this.redraw_();
  }

  getStatus(): ProofStatus {
    return this.status_;
  }

  getTarget(): string {
    return this.target_;
  }

  setSelected(selected: boolean): void {
    this.selected_ = selected;
    this.redraw_();
  }

  isClickable(): boolean {
    return true;
  }

  protected showEditor_(): void {
    const block = this.getSourceBlock();
    dispatchMarkerClick(block ? block.id : '', this.target_);
  }

  getSize(): blockly.utils.Size {
    return new blockly.utils.Size(PILL_WIDTH, PILL_HEIGHT);
  }

  protected get size_(): blockly.utils.Size {
    return new blockly.utils.Size(PILL_WIDTH, PILL_HEIGHT);
  }

  protected set size_(_newValue: blockly.utils.Size) {
    // Fixed size — ignore external resize attempts.
  }

  protected updateSize_(): void {
    // Fixed size, nothing to recompute.
  }

  saveState(): null {
    return null;
  }

  loadState(_state: unknown): void {
    // Status/selection are ephemeral, not serialized.
  }

  static fromJson(options: FieldConfig): FieldProofStatus {
    const field = new FieldProofStatus();
    field.target_ = (options as { target?: string }).target ?? '';
    return field;
  }
}

blockly.fieldRegistry.register('field_proof_status', FieldProofStatus);
