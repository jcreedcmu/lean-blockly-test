import * as blockly from 'blockly';
import { Field, FieldConfig } from 'blockly';

export type ProofStatus = 'unknown' | 'complete' | 'incomplete';

const STATUSES: ProofStatus[] = ['unknown', 'complete', 'incomplete'];

/**
 * Custom field showing a proof status indicator (checkmark, X, or question mark).
 */
export class FieldProofStatus extends Field<string> {
  private status_: ProofStatus = 'unknown';
  private circleBg_: SVGCircleElement | null = null;
  private iconElement_: SVGTextElement | null = null;
  private onClickHandler_: ((blockId: string, fieldName: string) => void) | null = null;

  static readonly WIDTH = 24;
  static readonly HEIGHT = 24;

  EDITABLE = false;
  SERIALIZABLE = false;

  constructor() {
    super(Field.SKIP_SETUP);
  }

  protected initView(): void {
    const Svg = blockly.utils.Svg;
    this.circleBg_ = blockly.utils.dom.createSvgElement(
      Svg.CIRCLE,
      {
        'cx': String(FieldProofStatus.WIDTH / 2),
        'cy': String(FieldProofStatus.HEIGHT / 2),
        'r': String(FieldProofStatus.WIDTH / 2 - 2),
        'fill': '#888',
        'fill-opacity': '0.3',
      },
      this.fieldGroup_,
    );
    this.iconElement_ = blockly.utils.dom.createSvgElement(
      Svg.TEXT,
      {
        'x': String(FieldProofStatus.WIDTH / 2),
        'y': String(FieldProofStatus.HEIGHT / 2),
        'dominant-baseline': 'central',
        'text-anchor': 'middle',
        'font-size': '14',
        'font-weight': 'bold',
        'fill': '#888',
        'pointer-events': 'none',
      },
      this.fieldGroup_,
    );
    this.iconElement_.textContent = '?';
    this.size_ = new blockly.utils.Size(FieldProofStatus.WIDTH, FieldProofStatus.HEIGHT);
  }

  setStatus(status: ProofStatus): void {
    this.status_ = status;
    if (!this.circleBg_ || !this.iconElement_) return;
    switch (status) {
      case 'complete':
        this.circleBg_.setAttribute('fill', '#4CAF50');
        this.circleBg_.setAttribute('fill-opacity', '0.3');
        this.iconElement_.setAttribute('fill', '#2E7D32');
        this.iconElement_.textContent = '\u2713';
        break;
      case 'incomplete':
        this.circleBg_.setAttribute('fill', '#F44336');
        this.circleBg_.setAttribute('fill-opacity', '0.3');
        this.iconElement_.setAttribute('fill', '#C62828');
        this.iconElement_.textContent = '\u2717';
        break;
      case 'unknown':
      default:
        this.circleBg_.setAttribute('fill', '#888');
        this.circleBg_.setAttribute('fill-opacity', '0.3');
        this.iconElement_.setAttribute('fill', '#888');
        this.iconElement_.textContent = '?';
        break;
    }
  }

  getStatus(): ProofStatus {
    return this.status_;
  }

  private cycleStatus(): void {
    const i = STATUSES.indexOf(this.status_);
    this.setStatus(STATUSES[(i + 1) % STATUSES.length]);
  }

  isClickable(): boolean {
    return true;
  }

  protected showEditor_(): void {
    if (this.onClickHandler_) {
      const block = this.getSourceBlock();
      const blockId = block ? block.id : '';
      this.onClickHandler_(blockId, this.name ?? '');
    } else {
      this.cycleStatus();
    }
  }

  setOnClick(handler: (blockId: string, fieldName: string) => void): void {
    this.onClickHandler_ = handler;
  }

  getSize(): blockly.utils.Size {
    return new blockly.utils.Size(FieldProofStatus.WIDTH, FieldProofStatus.HEIGHT);
  }

  protected get size_(): blockly.utils.Size {
    return new blockly.utils.Size(FieldProofStatus.WIDTH, FieldProofStatus.HEIGHT);
  }

  protected set size_(newValue: blockly.utils.Size) {
    // Fixed size — ignore external resize attempts.
  }

  protected updateSize_(): void {
    // Fixed size, nothing to update.
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
