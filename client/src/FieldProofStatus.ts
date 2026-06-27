import * as blockly from 'blockly';
import { Field, FieldConfig } from 'blockly';
import { dispatchMarkerClick, GoalPositionMarker } from './goalMarker';
import { PILL_WIDTH, PILL_HEIGHT, PillElements, createPill, updatePill } from './pill';

export type ProofStatus = 'unknown' | 'complete' | 'incomplete';

type StatusStyle = {
  fill: string;
  fillOpacity: string;
  text: string;
  textFill: string;
  fontSize: string;
};

/** Per-status appearance, drawn on the shared fixed-size pill. */
const STATUS_STYLES: Record<ProofStatus, StatusStyle> = {
  complete: { fill: '#4a90e2', fillOpacity: '1', text: '✓', textFill: '#000', fontSize: '12' },
  incomplete: { fill: '#d11', fillOpacity: '1', text: 'sorry', textFill: '#fff', fontSize: '12' },
  unknown: { fill: '#888', fillOpacity: '0', text: '?', textFill: 'rgba(0,0,0,0)', fontSize: '12' },
};

/**
 * Proof-status indicator pill (checkmark / `sorry` / `?`) that doubles as a
 * goal-position marker. Uses the shared {@link createPill} renderer, so it is
 * the same fixed 48×18 oblong shape as {@link import('./FieldGoalMarker')}. The
 * custom renderer centers it on the statement notch above (it is no longer
 * dynamically sized).
 */
export class FieldProofStatus extends Field<string> implements GoalPositionMarker {
  private status_: ProofStatus = 'unknown';
  private pill_: PillElements | null = null;
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
    this.redraw_();
  }

  private redraw_(): void {
    if (!this.pill_) return;
    const s = STATUS_STYLES[this.status_];
    updatePill(this.pill_, {
      fill: s.fill,
      fillOpacity: s.fillOpacity,
      text: s.text,
      textFill: s.textFill,
      fontSize: s.fontSize,
      // Selection ring (keeps the status color visible underneath).
      stroke: this.selected_ ? '#1565c0' : 'none',
      strokeWidth: this.selected_ ? '2' : '0',
    });
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
