import * as blockly from 'blockly';
import { Field, FieldConfig } from 'blockly';
import { dispatchMarkerClick, GoalPositionMarker } from './goalMarker';
import { PILL_WIDTH, PILL_HEIGHT, createPill, updatePill } from './pill';

/**
 * A clickable marker pill that selects a proof position for goal display, for
 * tactics that have no proof-status pill of their own (e.g. `intro`). Uses the
 * shared {@link createPill} renderer, so it is the same pill as the one in
 * {@link import('./FieldProofStatus')} (which adds a status decoration beside it).
 *
 * `target` names a statement input whose sub-proof position this pill points
 * to; an empty `target` means the block's own position. On click it reports
 * `(blockId, target)` to the shared marker sink.
 */
export class FieldGoalMarker extends Field<string> implements GoalPositionMarker {
  private target_: string;
  private selected_ = false;
  private pill_: SVGRectElement | null = null;

  EDITABLE = false;
  SERIALIZABLE = false;

  constructor(target: string = '') {
    super(Field.SKIP_SETUP);
    this.target_ = target;
  }

  protected initView(): void {
    this.pill_ = createPill(this.fieldGroup_ as SVGGElement);
    this.redraw_();
  }

  private redraw_(): void {
    if (this.pill_) updatePill(this.pill_, this.selected_);
  }

  setSelected(selected: boolean): void {
    this.selected_ = selected;
    this.redraw_();
  }

  getTarget(): string {
    return this.target_;
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

  protected set size_(_v: blockly.utils.Size) {
    // Fixed size — ignore external resize attempts.
  }

  protected updateSize_(): void {
    // Fixed size, nothing to recompute.
  }

  saveState(): null {
    return null;
  }

  loadState(_state: unknown): void {
    // Selection is ephemeral, not serialized.
  }

  static fromJson(options: FieldConfig): FieldGoalMarker {
    return new FieldGoalMarker((options as { target?: string }).target ?? '');
  }
}

blockly.fieldRegistry.register('field_goal_marker', FieldGoalMarker);
