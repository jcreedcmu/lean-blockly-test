import * as blockly from 'blockly';
import { Field, FieldConfig } from 'blockly';

export type ProofStatus = 'unknown' | 'complete' | 'incomplete';

type StatusStyle = {
  fill: string;
  fillOpacity: string;
  text: string;
  textFill: string;
  fontSize: string;
};

/** Per-status appearance. The pill background always spans the field's
 * full (possibly renderer-stretched) width; only colors/glyph differ. */
const STATUS_STYLES: Record<ProofStatus, StatusStyle> = {
  complete: { fill: '#4a90e2', fillOpacity: '1', text: '✓', textFill: '#000', fontSize: '12' },
  incomplete: { fill: '#d11', fillOpacity: '1', text: 'sorry', textFill: '#fff', fontSize: '12' },
  unknown: { fill: '#888', fillOpacity: '0', text: '?', textFill: 'rgba(0,0,0,0)', fontSize: '12' },
};

/**
 * Custom field showing a proof status indicator (checkmark, `sorry` pill, or
 * question mark). Rendered as a rounded pill that spans the field's width.
 *
 * The width is dynamic: the custom renderer calls {@link setRenderWidth} to
 * stretch each instance to match the statement input it reports on, so the
 * pill lines up with the proof slot directly above it.
 */
export class FieldProofStatus extends Field<string> {
  private status_: ProofStatus = 'unknown';
  private renderWidth_ = FieldProofStatus.DEFAULT_WIDTH;
  private bgRect_: SVGRectElement | null = null;
  private iconElement_: SVGTextElement | null = null;
  private onClickHandler_: ((blockId: string, fieldName: string) => void) | null = null;

  static readonly DEFAULT_WIDTH = 50;
  static readonly HEIGHT = 24;

  EDITABLE = false;
  SERIALIZABLE = false;

  constructor() {
    super(Field.SKIP_SETUP);
  }

  protected initView(): void {
    const Svg = blockly.utils.Svg;
    this.bgRect_ = blockly.utils.dom.createSvgElement(
      Svg.RECT,
      {
        'x': '0',
        'y': '0',
        'height': String(FieldProofStatus.HEIGHT),
        'rx': String(FieldProofStatus.HEIGHT / 2),
        'ry': String(FieldProofStatus.HEIGHT / 2),
      },
      this.fieldGroup_,
    );
    this.iconElement_ = blockly.utils.dom.createSvgElement(
      Svg.TEXT,
      {
        'y': String(FieldProofStatus.HEIGHT / 2),
        'dominant-baseline': 'central',
        'text-anchor': 'middle',
        'font-weight': 'bold',
        'pointer-events': 'none',
      },
      this.fieldGroup_,
    );
    this.redraw_();
  }

  /** Re-apply geometry (width) and per-status styling to the SVG. */
  private redraw_(): void {
    if (!this.bgRect_ || !this.iconElement_) return;
    const style = STATUS_STYLES[this.status_];
    const w = this.renderWidth_;
    this.bgRect_.setAttribute('width', String(w));
    this.bgRect_.setAttribute('fill', style.fill);
    this.bgRect_.setAttribute('fill-opacity', style.fillOpacity);
    this.iconElement_.setAttribute('x', String(w / 2));
    this.iconElement_.setAttribute('font-size', style.fontSize);
    this.iconElement_.setAttribute('fill', style.textFill);
    this.iconElement_.textContent = style.text;
  }

  setStatus(status: ProofStatus): void {
    this.status_ = status;
    this.redraw_();
  }

  getStatus(): ProofStatus {
    return this.status_;
  }

  /** Set the rendered width. Called by the custom renderer to match the
   * notch of the preceding statement input. */
  setRenderWidth(width: number): void {
    this.renderWidth_ = Math.max(width);
    this.redraw_();
  }

  isClickable(): boolean {
    return true;
  }

  protected showEditor_(): void {
    if (this.onClickHandler_) {
      const block = this.getSourceBlock();
      this.onClickHandler_(block ? block.id : '', this.name ?? '');
    } else {
      console.log('[FieldProofStatus] clicked, no handler set');
    }
  }

  setOnClick(handler: (blockId: string, fieldName: string) => void): void {
    this.onClickHandler_ = handler;
  }

  getSize(): blockly.utils.Size {
    return new blockly.utils.Size(this.renderWidth_ ?? FieldProofStatus.DEFAULT_WIDTH, FieldProofStatus.HEIGHT);
  }

  protected get size_(): blockly.utils.Size {
    return new blockly.utils.Size(this.renderWidth_ ?? FieldProofStatus.DEFAULT_WIDTH, FieldProofStatus.HEIGHT);
  }

  protected set size_(_newValue: blockly.utils.Size) {
    // Width is renderer-driven, height is fixed — ignore external resize.
  }

  protected updateSize_(): void {
    // Size is managed via renderWidth_, nothing to recompute.
  }

  saveState(): null {
    return null;
  }

  loadState(_state: unknown): void {
    // Status is ephemeral, not serialized.
  }

  static fromJson(_options: FieldConfig): FieldProofStatus {
    return new FieldProofStatus();
  }
}

blockly.fieldRegistry.register('field_proof_status', FieldProofStatus);
