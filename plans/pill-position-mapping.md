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

When we compute the Lean text from the blocks workspace, we should — at the
same time — produce a *textual range* (begin line/col, end line/col) for each
pill in any block. Target invariants:

- the ranges are disjoint;
- if R is the range for pill P, then *any* goal RPC at a position in R returns
  the same goal state, which is logically "the goal at P";
- a diagnostic at position LC falls in at most one range R, and if LC is
  logically at pill P then R is P's range.

### How we make these hold: constant-goal gaps, anchored by `skip`

A pill's range is a **constant-goal gap** — an inter-step region (mostly
whitespace/comments) where no tactic runs, so the goal is constant. *Which* gap
a pill names is **per block type**:

- **intro** (and other leaf position markers) → the gap *before* the tactic
  (the goal entering it).
- **constructor arm** (status pill) → the gap *after* that arm (where Lean
  reports `unsolved goals` if the arm is incomplete).
- **lemma** (status pill) → the gap *after* the whole proof.

To keep these gaps distinct and addressable — and to aid debugging — the
codegen inserts a no-op **`skip`** at each pill's gap, and the pill's range is
the region around its `skip`. `skip` is a no-op even with **no goals**
(verified: `by trivial; skip` and trailing `skip`s in completed `·` blocks both
elaborate clean), so it's safe after complete proofs and changes no goal state.

Backward only needs to catch **goal-state diagnostics** (unsolved goals), which
land in these gaps — not tactic-interior errors (a type error on a tactic),
which are out of scope for pill mapping.

### Disjointness is a target, not a hard requirement

Liberal `skip` insertion should keep ranges disjoint in practice (e.g. a
lemma-proved-by-trailing-constructor gets its own `skip` for the lemma gap,
distinct from the last arm's). But overlaps **must not be fatal**: if a position
falls in several ranges, pick deterministically (innermost) and carry on. The
game must never break because the gap reasoning was imperfect.

## Where the current code is

**Forward — exact and per-pill, but uses the *wrong* (wide) range:**
- `markerResolve.ts` `resolveMarkerLocation(workspace, sourceInfo, blockId,
  target)` → a target-aware contribution range (arm span via the `.next`
  chain, synthesized empty-arm placeholder via `emptyArmId`, or the block's
  own range for self-anchored pills). This computes the *span of the tactics*,
  not the constant-goal gap — so its range is wide and won't satisfy the
  invariants. The narrow-gap model above replaces this arm-span logic with a
  lookup into codegen-emitted gap ranges.
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

## Suggested implementation order

1. **Codegen emits gap ranges + `skip` anchors.** In `workspaceToLean`, at each
   pill's gap (per the per-block rules above), emit a no-op `skip` and record a
   narrow range keyed by `(blockId, target)`. Output these `pillRanges`
   alongside `sourceInfo`. Unit-test the emitted ranges (extend
   `workspaceToLean.test.ts`): each pill gets a gap range, intro's is before /
   constructor-arm's after / lemma's after the whole proof.
2. **Forward uses `pillRanges`.** Replace `resolveMarkerLocation`'s arm-span
   computation with a lookup into `pillRanges` (keep it as a thin adapter so
   `Blockly.tsx`/`App.tsx` call sites are unchanged). Query goals at a position
   inside the gap.
3. **Rework the backward pass, per-pill + defensive.** Replace the per-block
   line-overlap in `App.runEvaluation`: restrict to **goal-state** diagnostics,
   match each to the `pillRanges` entry containing it (innermost on overlap,
   never throw), and set status per `(blockId, target)`. Make
   `updateProofStatuses` key on `(blockId, target)` so sibling arm pills differ.
   Test the matching (containing, overlap→innermost, no-match).
4. **Forward selection display (slice-2 steps 2–3).** Lift selection into
   `App`, query the selected pill's position, show that goal in the panel
   (replacing the current console.log debug).

## Estimated effort

Steps 1–3: ~a day incl. tests (codegen gap emission + per-pill defensive
backward matching). Step 4 is the slice-2 display work, separate.
