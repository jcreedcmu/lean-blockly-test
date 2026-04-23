# Tutorial System: Representation and Integration Plan

## Motivation

The AK_work branch adds a per-level tutorial system (react-joyride based)
with auto-advance conditions. After rebasing onto main, the tutorial code
works but its state management is interleaved with game logic in `App.tsx`.
We want to:

1. Keep tutorial framework minimally coupled with game implementation.
2. Support tutorials in both the world overview and individual levels.
3. Tutorial content lives in its own files, separate from level
   definitions and from the components that render them.

## The tutorial protocol

A tutorial is a sequence of **steps**. Each step points at a UI element
(the "target"), shows a tooltip with markdown content, and optionally
**detects** a condition to auto-advance and/or **performs an action** on
behalf of the user.

### What a step can detect (advance conditions)

A step may have an `conditions` field. When present, the tutorial polls
every 250ms and auto-advances (after `advanceDelayMs`, default 500ms)
once the condition is met. Three condition kinds exist:

| Kind | Fields | What it checks |
|------|--------|----------------|
| `workspaceHasBlock` | `block: TutorialBlockPattern`, `location?: 'any' \| 'topLevel' \| 'theoremProof'` | A block matching the pattern exists in the Blockly workspace. The pattern can match on `type`, `fields` (by name/value), and `inputs` (recursively nested block patterns). `location` constrains where: anywhere (default), only at the top level, or only inside a lemma block's `LEMMA_PROOF` input. |
| `elementExists` | `selector: string`, `visible?: boolean` | A DOM element matching the CSS selector exists. If `visible` is true, also checks that the element (and all ancestors) have nonzero size, `display` is not `none`, `visibility` is not `hidden`/`collapse`, and `opacity` is not `0`. |
| `proofComplete` | *(none)* | The Lean evaluator reports that the current proof is complete. |

The condition evaluation is implemented in `tutorialConditions.ts` and is
a pure function of `(condition, workspaceState, proofComplete)` — it has
no side effects and does not import any React or Blockly code (it operates
on the serialized workspace JSON).

### What a step can do (side effects)

A step may have an `action` field of type `TutorialAction`. Currently
one variant exists:

| Action kind | Fields | Effect |
|-------------|--------|--------|
| `openToolboxCategory` | `category: string` | Opens the named Blockly toolbox category's flyout.

Actions flow through the `onStepActive` callback: `Tutorial.tsx` calls
`onStepActive(step)` on activation. Callback iterates `step.actions`
and dispatches on each action's `kind`.

Adding a new side effect means adding a variant to `TutorialAction`
and a case in the `onStepActive` handler. `TutorialStep` and
`Tutorial.tsx` don't change.

### What a step displays

| Field | Type | Purpose |
|-------|------|---------|
| `target` | `string` (CSS selector) | Element to anchor the tooltip to |
| `spotlightTarget` | `string?` (CSS selector) | Alternative element to spotlight (if different from anchor) |
| `content` | `string` | Markdown with KaTeX math support |
| `title` | `string?` | Optional heading above content |
| `placement` | `'top' \| 'right' \| 'bottom' \| 'left' \| 'auto' \| 'center'` | Tooltip position relative to target |
| `offset` | `number?` | Pixel offset from target |
| `skipScroll` | `boolean?` | Don't scroll to bring target into view |
| `targetWaitTimeout` | `number?` | ms to wait for target element to appear in DOM |

### Navigation

- Steps without `conditions`: user clicks Next/Back/Close manually.
- Steps with `conditions`: Next button is hidden; Back and Close are
  shown. The step auto-advances when all conditions are met (after the
  delay).
- Closing or skipping marks the tutorial as done (persisted to
  localStorage under the step's `storageKey`).

### Full types

```typescript
// ── Side effects a step can trigger ──────────────────────────

type TutorialAction =
  | { kind: 'openToolboxCategory'; category: string };

// ── Conditions a step can wait on ────────────────────────────

type TutorialCondition =
  | { kind: 'workspaceHasBlock';
      block: TutorialBlockPattern;
      location?: 'any' | 'topLevel' | 'theoremProof'; }
  | { kind: 'elementExists';
      selector: string;
      visible?: boolean; }
  | { kind: 'proofComplete' };

type TutorialBlockPattern = {
  type: string;
  fields?: Record<string, string>;
  inputs?: Record<string, TutorialBlockPattern>;
};

// ── A single tutorial step ───────────────────────────────────

type TutorialStep = {
  // What to show
  target: string;                  // CSS selector to anchor tooltip
  spotlightTarget?: string;        // alternative element to spotlight
  title?: string;
  content: string;                 // markdown with KaTeX
  placement?: 'top' | 'right' | 'bottom' | 'left' | 'auto' | 'center';
  offset?: number;
  targetWaitTimeout?: number;      // ms to wait for target to appear
  skipScroll?: boolean;

  // What to do (all actions fire while step is active)
  actions?: TutorialAction[];

  // When to auto-advance (all conditions must be met)
  conditions?: TutorialCondition[];
  advanceDelayMs?: number;         // delay after all conditions met (default 650ms)
};
```

Adding a new side effect means adding a variant to `TutorialAction`;
adding a new auto-advance trigger means adding a variant to
`TutorialCondition`. Neither requires touching `TutorialStep`.

A step with multiple actions performs all of them. A step with multiple
conditions requires all of them to be satisfied before auto-advancing.

## Available CSS targets

Tutorial steps reference UI elements by CSS selector. These are the
stable class names that exist for tutorial targeting:

| Selector | Element | Added by |
|----------|---------|----------|
| `.world-3d-container` | 3D world overview scene | WorldOverview3D.tsx |
| `.world-3d-why-btn` | "Why Real Analysis?" button | WorldOverview3D.tsx |
| `.world-3d-reset-btn` | Browser reset button | WorldOverview3D.tsx |
| `.world-3d-help-btn` | Help/tutorial button | WorldOverview3D.tsx |
| `.world-3d-first-world-anchor` | Invisible anchor at first world's screen position | WorldOverview3D.tsx |
| `.blocklySvg` | The Blockly canvas | Blockly (built-in) |
| `.blocklyToolbox` | Toolbox sidebar | Blockly (built-in) |
| `.blocklyFlyout [data-id="tutorial-toolbox-apply"]` | Apply block in flyout | toolbox.ts |
| `.tutorial-theorem-block` | The main lemma block | Blockly.tsx |
| `.tutorial-tactics-category-row` | Tactics category row in toolbox | toolbox.ts |
| `.tutorial-tactics-category-label` | Tactics category label | toolbox.ts |
| `.tutorial-hyp-{name}` | A specific hypothesis (name is sanitized) | Hyp.tsx |
| `.tutorial-workspace-anchor` | Small centered div in workspace area | App.tsx |
| `.goals-panel` | Goals display panel | App.tsx |
| `.proof-status` | Proof completion indicator | App.tsx |
| `.navbar-btn`, `.navbar-back-btn`, `.navbar-reset-btn`, `.navbar-info-btn`, `.navbar-tutorial-btn`, `.navbar-next-level-btn`, `.navbar-prev-level-btn` | Navbar buttons | App.tsx |

## Tutorial content organization

Tutorial content lives in separate files alongside the levels they
belong to, not inlined on `LevelSource`:

```
client/src/levels/
  RealAnalysisStory/
    L00_the_problem.ts           ← level definition
    L00_the_problem_tutorial.ts  ← tutorial for that level
    L02_rfl.ts
    L02_rfl_tutorial.ts
  worldOverviewTutorial.ts       ← world overview tutorial
```

Each tutorial file exports a `TutorialStep[]`:
```typescript
import type { TutorialStep } from '../../gameData';
const tutorial: TutorialStep[] = [ ... ];
export default tutorial;
```

The `tutorial` field is removed from `LevelSource`. Instead, tutorial
files are loaded via a parallel `import.meta.glob` in `gameData.ts`,
matched to their level by filename convention (`*_tutorial.ts`), and
attached to `LevelDefinition` during conversion.

The world overview tutorial moves to its own file
(`levels/worldOverviewTutorial.ts` or similar) and is imported directly
by `WorldOverview3D.tsx`.

## Refactoring plan

### 1. Extract `useLevelTutorial` hook

**New file: `client/src/useLevelTutorial.ts`**

Pulls out of `App.tsx`:
- `runTutorial` and `tutorialWorkspaceState` state
- `isTutorialStepComplete` callback
- Auto-start useEffect
- `tutorialStorageKey()` helper

Returns a simple object that App.tsx consumes:
```typescript
{
  run: boolean,
  start(): void,             // navbar button
  stop(): void,              // onDone
  updateWorkspace(s): void,  // called from onBlocklyChange
  resetWorkspace(s): void,   // called from resetCurrentLevel
  tutorialProps: TutorialProps,
}
```

App.tsx still owns the `onStepActive` callback (because it needs
`blocklyRef`), but everything else moves into the hook.

### 2. Move tutorial content to separate files

- Move per-level tutorial arrays out of level `.ts` files into
  sibling `*_tutorial.ts` files.
- Remove `tutorial` from `LevelSource`. Keep it on `LevelDefinition`
  (populated during loading by matching `*_tutorial.ts` files).
- Add a second `import.meta.glob('./levels/*/*_tutorial.ts', { eager: true })`
  in `gameData.ts` to load tutorial files and join them to levels.
- Move world overview tutorial steps from `WorldOverview3D.tsx` to
  `client/src/levels/worldOverviewTutorial.ts`.

### 3. Rename types and restructure fields

In `gameData.ts`:
- Rename `TutorialAdvanceCondition` → `TutorialCondition`
- Add `TutorialAction = { kind: 'openToolboxCategory'; category: string }`
- In `TutorialStep`: replace `openToolboxCategory?: string` with
  `actions?: TutorialAction[]`; replace `advanceOn?: TutorialAdvanceCondition`
  with `conditions?: TutorialCondition[]`

In `tutorialConditions.ts`:
- Update import to use `TutorialCondition`
- Callers check that *all* conditions in the array are met

In `Tutorial.tsx`:
- Strip `actions` (instead of `openToolboxCategory`) before passing to
  Joyride; if step has any actions, set up the re-fire interval
- Check `step.conditions?.length` instead of `step.advanceOn` for
  auto-advance and button hiding logic

In `App.tsx` (the `onStepActive` callback):
- Iterate `step.actions` and dispatch on each action's `kind`
- `isStepComplete` checks all conditions are met

In level files (`L00_the_problem.ts`, any others):
- Replace `openToolboxCategory: "Tactics"` with
  `actions: [{ kind: 'openToolboxCategory', category: 'Tactics' }]`
- Replace `advanceOn: { kind: ... }` with
  `conditions: [{ kind: ... }]`

### 5. Files touched

| File | Change |
|------|--------|
| `client/src/useLevelTutorial.ts` | **New** — custom hook |
| `client/src/levels/worldOverviewTutorial.ts` | **New** — world overview tutorial data |
| `client/src/levels/*_tutorial.ts` | **New** — per-level tutorial data (extracted from level files) |
| `client/src/gameData.ts` | Add `TutorialAction`, rename `TutorialAdvanceCondition` → `TutorialCondition`, update `TutorialStep`, remove `tutorial` from `LevelSource`, add tutorial glob loading |
| `client/src/tutorialConditions.ts` | Update import |
| `client/src/Tutorial.tsx` | Handle `actions` list instead of `openToolboxCategory` |
| `client/src/App.tsx` | Remove tutorial state/effects, use hook, update `onStepActive` dispatch |
| `client/src/WorldOverview3D.tsx` | Import steps from `levels/worldOverviewTutorial.ts` |
| `client/src/levels/*/L*.ts` | Remove inline `tutorial` arrays |

### 4. What stays coupled (and why)

- **CSS class annotations** in Blockly.tsx, Hyp.tsx, toolbox.ts — one
  line each, just adding a class name. Removing them would require a
  semantic-target indirection layer that adds complexity without value.
- **`onStepActive` callback** in App.tsx — tutorial legitimately needs
  to trigger `openToolboxCategory`, which requires a ref to Blockly.
- **`proofComplete` passed to hook** — tutorial reads proof state for
  `{ kind: 'proofComplete' }` conditions. Read-only dependency.
