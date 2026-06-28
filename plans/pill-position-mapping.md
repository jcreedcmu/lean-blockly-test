# Plan: a canonical pill ↔ text-position model

## Motivation

Goal-position marker pills (`FieldProofStatus`, `FieldGoalMarker`, both
`GoalPositionMarker`) need to relate to specific line/column positions in the
generated Lean text, in **two directions**:

1. **Forward (pill → position).** Clicking a pill must yield a specific
   document position to RPC-query the goal state at (`getInteractiveGoals`).
2. **Backward (position → pill).** When we have the whole file's diagnostics,
   each diagnostic must map to the pill that is its *best match*. This is
   inherently less injective of a function: a diagnostic's reported position is often *near* but not
   *exactly* at the pill's position (an unsolved-goals error lands on
   `theorem`/`by` or end-of-proof, not on a specific tactic). We want to map
   to the pill that "governs" that position.

Today these two directions ride on **different position models**, which is the
core problem this plan fixes.

## Core idea: one canonical per-pill range

When we compute the lean text from the blocks workspace, we should
very naturally, at the same time, produce *textual ranges* (i.e. beginning line/col and ending line/col) for each pill
that exists in any block. The invariants that must hold of this data
are:
- the ranges are all disjoint.
- if R is the range for pill P, then *any* RPC querying for goals at a position in range R
  should produce the same goal state, and this should be logically the goal state "at pill P".
- if we get a diagnostic that says it occurs at position LC, then there is at most one
  range R that includes it, and if LC is logically at a particular pill P, then range R
  is associated with pill P.

This means we are free to arbitrarily pick the start of the range in
the forward direction.

## Where the current code is

**Forward — already exact and per-pill:**
- `markerResolve.ts` `resolveMarkerLocation(workspace, sourceInfo, blockId,
  target)` → a target-aware contribution range (arm span via the `.next`
  chain, synthesized empty-arm placeholder via `emptyArmId`, or the block's
  own range for self-anchored pills).
- `LevelEvaluator.goalsAtContributionPosition(pos)` offsets by
  `preludeLineCount` → document position.
- `LeanSessionManager.getGoalsAtPosition(uri, pos)` → `$/lean/rpc/call` for
  `Lean.Widget.getInteractiveGoals`.
- Wired through `Blockly.tsx` (marker click → `resolveMarkerLocation`) and
  `App.tsx` `onMarkerSelect` (currently logs start/end goals — slice-2 step 1).

**Backward — crude and per-block:**
- `App.tsx` `runEvaluation` filters severity-1 diagnostics, then for each
  `sourceInfo` block range marks it `incomplete` iff a diagnostic's **line
  interval overlaps** the block's line interval; else `complete`.
- `Blockly.tsx` `updateProofStatuses(Map<blockId, status>)` sets **every**
  `FieldProofStatus` field on a block to that status.

Limits of the backward path:
- **Line-based**, **binary** (error-present, not goal content).
- **Per-block, not per-pill**: keyed by block id, so a block's multiple pills
  (e.g. the constructor's `STATUS_1`/`STATUS_2`) always show the *same* status
  — it can't distinguish arms.
- Uses the **raw block range** (`sourceInfo[id]`), *not* the per-pill resolved
  range that the forward direction uses → the two directions disagree.

Separately, `LevelEvaluator` `leafGoals` carry positions
(`translatePositionToContribution(diag.range.start)`) but are only listed in
the goal view, never matched to pills.

.

## Suggested implementation order

1. **Enumerate pills + ranges.** A helper that walks the workspace for every
   `GoalPositionMarker` field, resolves each via `resolveMarkerLocation`, and
   returns `{ blockId, target, range }[]`. Pure-ish; unit-testable like
   `markerResolve.test.ts`.
2. **Rework the backward pass (Strategy A).** Replace the per-block overlap in
   `App.runEvaluation` with per-pill best-match against those ranges; make
   `updateProofStatuses` set status per `(blockId, target)` rather than per
   block (so sibling arm pills can differ). Add tests for the matching
   heuristic (containing, nearest, tolerance, no-match).
3. **Forward selection (slice-2 steps 2–3).** Lift selection into `App`, query
   the selected pill's position, and show that goal in the panel.
4. **(Optional) Strategy B** for selected-pill or all-pill precise status.

## Estimated effort

Steps 1–2: ~half a day incl. tests (mostly the matching heuristic + making
status per-pill). Steps 3–4 are the slice-2 display work, separate.
