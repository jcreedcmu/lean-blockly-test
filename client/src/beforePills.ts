/**
 * Pure helpers for giving tactic blocks a clickable "before" goal-marker pill
 * on their left, marking (and selecting) the proof state *before* the tactic
 * runs. Kept free of any `blockly` import so it can be unit-tested in
 * isolation; `blocks.ts` wires the result into `defineBlocksWithJsonArray`.
 *
 * The pill reuses the same `field_goal_marker` field and `target=''` convention
 * that `intro` and `conv` already use, so selection/highlight and goal-query
 * behavior come for free. Blocks that already start with a marker (intro, conv)
 * are skipped, which makes the transform idempotent; a start pill is *added
 * alongside* any sub-proof pills a block already has (have, show,
 * constructor/"pair", transform).
 */

export type BlockJson = {
  type?: string;
  message0?: string;
  args0?: unknown[];
  [k: string]: unknown;
};

/** Tactic blocks that should NOT get a start pill: conv-mode navigation that
 * isn't a sequential tactic acting on an ordinary goal. */
export const NO_BEFORE_PILL = new Set<string>([
  'tactic_enter',
]);

/** True if the block's first field is already a goal marker (intro, conv). */
function hasStartMarker(def: BlockJson): boolean {
  const first = (def.args0 as Array<{ type?: unknown }> | undefined)?.[0];
  return !!first && first.type === 'field_goal_marker';
}

/**
 * Whether a block definition should receive a left "before" goal-marker pill:
 * every `tactic_*` block, except conv-internal ones ({@link NO_BEFORE_PILL})
 * and any that already start with a marker (so applying this twice is a no-op).
 */
export function shouldGetBeforePill(def: BlockJson): boolean {
  return typeof def.type === 'string'
    && def.type.startsWith('tactic_')
    && !NO_BEFORE_PILL.has(def.type)
    && !hasStartMarker(def);
}

/**
 * Prepend a `field_goal_marker` as the block's first field (rendered to the
 * left of the tactic) and shift every existing `%N` placeholder up by one so
 * the message still matches its args.
 */
export function prependGoalMarker(def: BlockJson): BlockJson {
  const shifted = (def.message0 ?? '').replace(/%(\d+)/g, (_m, n) => `%${Number(n) + 1}`);
  return {
    ...def,
    message0: `%1 ${shifted}`,
    args0: [{ type: 'field_goal_marker', name: 'GOAL_AT' }, ...(def.args0 ?? [])],
  };
}

/** Map over a block-definition array, adding a start "before" pill to every
 * block for which {@link shouldGetBeforePill} holds and passing the rest
 * through unchanged. */
export function applyBeforePills(
  defs: Array<Record<string, unknown>>,
): Array<Record<string, unknown>> {
  return defs.map((d) => (shouldGetBeforePill(d as BlockJson) ? prependGoalMarker(d as BlockJson) : d));
}
