import * as blockly from 'blockly';
import { Field, FieldConfig } from 'blockly';
import { dispatchMarkerClick, GoalPositionMarker } from './goalMarker';
import { PILL_HEIGHT, createPill, updatePill, flashPillError } from './pill';

export type ProofStatus = 'unknown' | 'complete' | 'incomplete';

/** Gap (px) between the marker pill and the status decoration to its right. */
const DECORATION_GAP = 4;

type StatusDecoration = { text: string; fill: string };

/** The text decoration drawn to the right of the pill, conveying good/bad. */
const STATUS_DECORATION: Record<ProofStatus, StatusDecoration> = {
  complete: { text: '✓', fill: '#166534' },
  incomplete: { text: 'sorry', fill: '#8a5a00' },
  unknown: { text: '', fill: 'rgba(0,0,0,0)' }, // nothing yet
};

/**
 * Proof-position marker with its status centered inside the pill: cream
 * `sorry` for an unfinished subproof, pale green `✓` for a completed one, and
 * an empty cream pill while Lean is checking. The custom renderer centers the
 * pill on the statement notch above.
 */
export class FieldProofStatus extends Field<string> implements GoalPositionMarker {
  private status_: ProofStatus = 'unknown';
  private pill_: SVGRectElement | null = null;
  private decoration_: SVGTextElement | null = null;
  private incompleteDecoration_: StatusDecoration = STATUS_DECORATION.incomplete;
  private completeDecoration_: StatusDecoration = STATUS_DECORATION.complete;
  private decorationInside_ = true;
  private pillWidth_ = 42;
  private incompletePillFill_: string | null = '#fff4cc';
  private incompletePillStroke_: string | null = '#d19a00';
  private completePillFill_: string | null = '#dcfce7';
  private completePillStroke_: string | null = '#16a34a';
  private unknownPillFill_: string | null = '#fff4cc';
  private unknownPillStroke_: string | null = '#d19a00';
  // Goal-position-marker state.
  private target_ = '';
  private selected_ = false;

  EDITABLE = false;
  SERIALIZABLE = false;

  constructor() {
    super(Field.SKIP_SETUP);
  }

  protected initView(): void {
    this.pill_ = createPill(this.fieldGroup_ as SVGGElement, this.pillWidth_);
    this.decoration_ = blockly.utils.dom.createSvgElement(
      blockly.utils.Svg.TEXT,
      {
        'x': String(this.decorationInside_
          ? this.pillWidth_ / 2
          : this.pillWidth_ + DECORATION_GAP),
        'y': String(PILL_HEIGHT / 2),
        'dominant-baseline': 'central',
        'text-anchor': this.decorationInside_ ? 'middle' : 'start',
        'font-weight': 'bold',
        'font-size': this.decorationInside_ ? '10' : '12',
        'pointer-events': 'none',
      },
      this.fieldGroup_,
    ) as SVGTextElement;
    this.redraw_();
  }

  private redraw_(): void {
    if (this.pill_) {
      updatePill(this.pill_, this.selected_);
      if (this.status_ === 'incomplete') {
        if (this.incompletePillFill_) {
          this.pill_.setAttribute('fill', this.incompletePillFill_);
        }
        if (this.incompletePillStroke_) {
          this.pill_.setAttribute('stroke', this.incompletePillStroke_);
        }
      } else if (this.status_ === 'complete') {
        if (this.completePillFill_) {
          this.pill_.setAttribute('fill', this.completePillFill_);
        }
        if (this.completePillStroke_) {
          this.pill_.setAttribute('stroke', this.completePillStroke_);
        }
      } else {
        if (this.unknownPillFill_) {
          this.pill_.setAttribute('fill', this.unknownPillFill_);
        }
        if (this.unknownPillStroke_) {
          this.pill_.setAttribute('stroke', this.unknownPillStroke_);
        }
      }
    }
    if (this.decoration_) {
      const d = this.status_ === 'incomplete'
        ? this.incompleteDecoration_
        : this.status_ === 'complete'
          ? this.completeDecoration_
          : STATUS_DECORATION.unknown;
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

  /** Briefly flash the pill with the shared red error glow. */
  flashError(): void {
    if (this.pill_) flashPillError(this.pill_);
  }

  isClickable(): boolean {
    return true;
  }

  protected showEditor_(): void {
    const block = this.getSourceBlock();
    dispatchMarkerClick(block ? block.id : '', this.target_);
  }

  getSize(): blockly.utils.Size {
    return new blockly.utils.Size(this.pillWidth_, PILL_HEIGHT);
  }

  protected get size_(): blockly.utils.Size {
    return new blockly.utils.Size(this.pillWidth_, PILL_HEIGHT);
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
    const config = options as {
      target?: string;
      incompleteText?: string;
      incompleteFill?: string;
      completeText?: string;
      completeFill?: string;
      decorationInside?: boolean;
      pillWidth?: number;
      incompletePillFill?: string;
      incompletePillStroke?: string;
      completePillFill?: string;
      completePillStroke?: string;
      unknownPillFill?: string;
      unknownPillStroke?: string;
    };
    field.target_ = config.target ?? '';
    field.decorationInside_ = config.decorationInside ?? field.decorationInside_;
    field.pillWidth_ = config.pillWidth ?? field.pillWidth_;
    field.incompletePillFill_ = config.incompletePillFill ?? field.incompletePillFill_;
    field.incompletePillStroke_ = config.incompletePillStroke ?? field.incompletePillStroke_;
    field.completePillFill_ = config.completePillFill ?? field.completePillFill_;
    field.completePillStroke_ = config.completePillStroke ?? field.completePillStroke_;
    field.unknownPillFill_ = config.unknownPillFill ?? field.unknownPillFill_;
    field.unknownPillStroke_ = config.unknownPillStroke ?? field.unknownPillStroke_;
    field.incompleteDecoration_ = {
      text: config.incompleteText ?? STATUS_DECORATION.incomplete.text,
      fill: config.incompleteFill ?? STATUS_DECORATION.incomplete.fill,
    };
    field.completeDecoration_ = {
      text: config.completeText ?? STATUS_DECORATION.complete.text,
      fill: config.completeFill ?? STATUS_DECORATION.complete.fill,
    };
    return field;
  }
}

blockly.fieldRegistry.register('field_proof_status', FieldProofStatus);
