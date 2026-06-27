/**
 * Shared selection mechanism for "goal-position marker" pills.
 *
 * Several fields act as markers — `FieldProofStatus` (the per-sub-proof status
 * pill) and `FieldGoalMarker` (a plain selection dot for tactics without a
 * sub-proof). Each carries a `target` (a statement-input name on its block, or
 * `''` for the block itself) and, when clicked, reports `(blockId, target)` to
 * a single host-registered sink. The host resolves that to a source location.
 */
export interface GoalPositionMarker {
  getTarget(): string;
  setSelected(selected: boolean): void;
}

let markerClickHandler: ((blockId: string, target: string) => void) | null = null;

/** Register the host's click sink (call with `null` to clear). */
export function setMarkerClickHandler(
  fn: ((blockId: string, target: string) => void) | null,
): void {
  markerClickHandler = fn;
}

/** Called by a marker field on click. */
export function dispatchMarkerClick(blockId: string, target: string): void {
  markerClickHandler?.(blockId, target);
}

/** Duck-typed check so the host can iterate marker fields without importing
 * every field class. */
export function isGoalPositionMarker(field: unknown): field is GoalPositionMarker {
  return !!field
    && typeof (field as GoalPositionMarker).getTarget === 'function'
    && typeof (field as GoalPositionMarker).setSelected === 'function';
}
