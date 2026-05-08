# Refactor: Remove BlocklyState from LevelDefinition

## Motivation

`LevelDefinition` currently contains an `initial: BlocklyState` field —
a pre-built Blockly workspace serialization blob with pixel coordinates,
block IDs, and Blockly-internal field names like `THEOREM_BLOCK_LABEL`.
This couples the level data model to Blockly's serialization format.

The upcoming LeanBlocksGame DSL will produce JSON level data. The closer
`LevelDefinition` is to that JSON, the less translation code we need. If
`LevelDefinition` holds abstract theorem data instead of a Blockly
workspace blob, the JSON from `MakeGame` can map to `LevelDefinition`
nearly 1:1.

This refactor is independently valuable: it makes the data model cleaner
regardless of whether the DSL migration proceeds.

## Current State

### LevelDefinition (gameData.ts:46–60)

```ts
type LevelDefinition = {
  name: string;
  theoremName: string;
  initial: BlocklyState;        // ← Blockly workspace blob
  permissions?: LevelPermission[];
  introduction?: string;
  conclusion?: string;
  tutorial?: TutorialStep[];
  display?: string;             // ← pre-formatted "Objects:\n  ...\nGoal:\n  ..."
};
```

### How `initial` is created (gameData.ts:128–148)

`makeLevelState()` builds a `BlocklyState` from three values:
- `theoremName` (e.g. `"RealAnalysisStory_2"`)
- `declaration` (e.g. `"(x y : ℝ) : x ^ 2 + 2 * y = x ^ 2 + 2 * y"`)
- `theoremBlockLabel` (optional, e.g. `"Example"`)

### How `initial` is consumed

1. **App.tsx:51–54** — Initializes `levelStates` from `l.initial` for
   every level. `levelStates` tracks the *current* workspace state per
   level (mutated as the player edits).

2. **App.tsx:238–240** — `resetCurrentLevel()` reloads `l.initial` into
   the Blockly workspace.

3. **Blockly.tsx:90–91** — `blockly.serialization.workspaces.load(initialData, ws)`
   deserializes the blob into a live Blockly workspace.

### How `display` is created (gameData.ts:162–169)

`formatDisplay()` assembles `objects`, `assumptions`, `goal` from
`LevelSource` into a multi-line string. This is purely presentational.

## Field Glossary

Every name-like field, with examples from two representative levels:

### Tutorial level (L00_the_problem, anonymous statement)

| Field | Value | Role |
|-|-|-|
| `name` | `"The \"apply\" Tactic"` | Human-readable level title, shown in the level list and header. |
| `theoremName` | `"RealAnalysisStory_1"` | Synthetic Lean identifier used as the declaration name in codegen. The generated Lean is `theorem RealAnalysisStory_1 (x : ℝ) (h : x = 5) : x = 5 := by ...`. Not shown to the player directly. |
| `theoremStatement` | `"(x : ℝ) (h : x = 5) : x = 5"` | The Lean declaration signature (binders + `: returnType`), excluding the `theorem` keyword and `:= by`. Fed to codegen after `theorem <theoremName>`. |
| `theoremBlockLabel` | `"Example"` | Overrides the default label on the lemma block. Without this, the block would display `"theorem RealAnalysisStory_1"`. With it, the block displays `"Example"`. |
| `objects` | `"x : ℝ"` | Non-Prop binders, for the structured "Objects:" display on the lemma block. |
| `assumptions` | `"h : x = 5"` | Prop binders, for the "Assumptions:" display. |
| `goal` | `"x = 5"` | The target type, for the "Goal:" display. |
| `introduction` | `"# Your First Formal Proof\n..."` | Markdown text shown to the player before they start the level. |
| `conclusion` | `"Perfect! You've completed..."` | Markdown text shown after the player completes the level. |

### Named theorem level (L01_ArchProp)

| Field | Value | Role |
|-|-|-|
| `name` | `"Archimedean Property"` | Human-readable level title. |
| `theoremName` | `"Lecture3_1"` | Synthetic Lean identifier for codegen. |
| `theoremStatement` | `"ArchProp {ε : ℝ} (hε : 0 < ε) :\n    ∃ (N : ℕ), 1 / ε < N"` | **Note**: includes `ArchProp` at the start. The generated Lean becomes `theorem Lecture3_1 ArchProp {ε : ℝ} ...`. This is a current quirk — `ArchProp` is the real theorem name in the vendor source's `Statement ArchProp ...`, but in the current encoding it's baked into the `theoremStatement` string while `theoremName` is a separate synthetic identifier. |
| `theoremBlockLabel` | (absent) | Block displays default: `"theorem Lecture3_1"`. |
| `objects` | `"{ε : ℝ}"` | Non-Prop binders. |
| `assumptions` | `"(hε : 0 < ε)"` | Prop binders. |
| `goal` | `"∃ (N : ℕ), 1 / ε < N"` | Target type. |

### The `theoremName` / `theoremStatement` relationship today

Currently, `theoremName` is always a synthetic identifier like
`WorldId_N` (e.g. `"Lecture3_1"`). When the vendor source names the
theorem (e.g. `Statement ArchProp ...`), that name appears as the
*first token* of `theoremStatement`, making `theoremStatement` a hybrid of name +
signature. The codegen produces `theorem <theoremName> <theoremStatement>`,
so the emitted Lean is `theorem Lecture3_1 ArchProp {ε : ℝ} ...`
where Lean parses `Lecture3_1` as the declaration name.

In the DSL-based future, the `Statement` elaborator knows the real
theorem name and the signature separately. The JSON can emit them as
distinct fields, eliminating this conflation.

## Proposed LevelDefinition

```ts
type LevelDefinition = {
  /** Human-readable level title, e.g. "Archimedean Property". */
  name: string;
  /** Lean identifier for codegen. Used as the declaration name in
   *  `theorem <theoremName> <theoremStatement> := by ...`.
   *  Example: "Lecture3_1" or "ArchProp". */
  theoremName: string;
  /** The Lean declaration signature: binders + `: returnType`.
   *  Does NOT include the theorem keyword, name, or `:= by`.
   *  Example: "{ε : ℝ} (hε : 0 < ε) : ∃ (N : ℕ), 1 / ε < N" */
  theoremStatement: string;
  /** Label shown on the lemma block. If absent, defaults to
   *  "theorem <theoremName>".
   *  Example: "Example", or "theorem ArchProp". */
  theoremBlockLabel?: string;
  /** Non-Prop binders for structured display. Example: "{ε : ℝ}" */
  objects?: string;
  /** Prop binders for structured display. Example: "(hε : 0 < ε)" */
  assumptions?: string;
  /** Target type for structured display.
   *  Example: "∃ (N : ℕ), 1 / ε < N" */
  goal?: string;
  permissions?: LevelPermission[];
  /** Markdown introduction shown before the level. */
  introduction?: string;
  /** Markdown conclusion shown after completing the level. */
  conclusion?: string;
  tutorial?: TutorialStep[];
};
```

Changes from current `LevelDefinition`:
- `initial: BlocklyState` is removed.
- `display: string` is removed (computed at render time from
  objects/assumptions/goal).
- `theoremStatement: string` is added (the Lean declaration signature,
  previously buried inside the BlocklyState blob as `THEOREM_DECLARATION`).
- `theoremBlockLabel?: string` is added.
- `objects`, `assumptions`, `goal` are added as optional structured
  fields (previously only on `LevelSource`, collapsed into `display`
  at load time).

## Where BlocklyState Generation Moves

`makeLevelState(theoremName, theoremStatement, theoremBlockLabel)` still
exists, but is called at the point of consumption rather than at data
load time:

### App.tsx — levelStates initialization

```ts
// Before:
const [levelStates, setLevelStates] = useState<Record<string, BlocklyState[]>>(
  () => Object.fromEntries(
    gameData.worlds.map(w => [w.id, w.levels.map(l => l.initial)])
  )
);

// After:
const [levelStates, setLevelStates] = useState<Record<string, BlocklyState[]>>(
  () => Object.fromEntries(
    gameData.worlds.map(w => [w.id, w.levels.map(l => makeLevelState(l))])
  )
);
```

`makeLevelState` moves from `gameData.ts` to somewhere the Blockly
layer can own it (could stay in `gameData.ts` or move to `Blockly.tsx`
— it just takes `LevelDefinition` fields and returns `BlocklyState`).

### App.tsx — resetCurrentLevel

```ts
// Before:
const initialState = world.levels[levelIndex].initial;

// After:
const initialState = makeLevelState(world.levels[levelIndex]);
```

### formatDisplay moves to render time

The `display` string is currently computed once at load time by
`formatDisplay()` and stored on `LevelDefinition`. Instead, the lemma
block renderer computes it from `objects`/`assumptions`/`goal` when
rendering. `formatDisplay()` can move to wherever the
`FieldTheoremStatement` reads it (likely `Blockly.tsx` or `blocks.ts`).

## LevelSource simplification

`LevelSource` (the shape of hand-authored `.ts` level files) currently
has most of these abstract fields already. After the refactor,
`levelSourceToDefinition()` becomes trivial — it's essentially a
pass-through, since `LevelSource` and `LevelDefinition` share the same
abstract shape. The remaining differences:

- `LevelSource` has `world` and `level` (used for grouping/sorting,
  not stored on `LevelDefinition`).

## Files to Modify

| File | Change |
|------|--------|
| `client/src/gameData.ts` | Update `LevelDefinition` type; simplify `levelSourceToDefinition()`; move `makeLevelState()` out of the data path |
| `client/src/App.tsx` | Call `makeLevelState()` when initializing `levelStates` and resetting levels |
| `client/src/Blockly.tsx` | No change (still receives `BlocklyState` from App) |
| `client/src/useLevelTutorial.ts` | No change (operates on `BlocklyState` from App) |
| `client/src/workspaceToLean.ts` | No change (operates on `BlocklyState`) |
| Level files (`client/src/levels/**/*.ts`) | No change needed (they export `LevelSource`, which already has the abstract fields) |

## Verification

1. `npm run dev` — app loads, all worlds/levels render correctly.
2. Theorem blocks display the correct Objects/Assumptions/Goal
   decomposition.
3. Reset level restores the workspace to a fresh lemma block.
4. Tutorials still function (they operate on `BlocklyState` from App,
   unchanged).
5. `workspaceToLean` still produces correct Lean source.
