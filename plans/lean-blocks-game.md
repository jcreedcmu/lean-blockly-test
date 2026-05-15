# LeanBlocksGame: Lean DSL for Blockly Game Authoring

## Motivation

Currently, levels are hand-authored as TypeScript `LevelSource` objects in
`client/src/levels/`. These were manually transcribed from the Lean4Game DSL
files in `vendor/RealAnalysisGame/`. The goal is to let game authors write
`.lean` files using a DSL similar to the existing Lean4Game format, with
Blockly-specific extensions, and have a build pipeline produce data the
Blockly client can consume directly.

## Architecture

```
Author writes .lean level files (familiar Lean4Game-style DSL)
        |
        v
    lake build
        |
        v
Lean elaborators store game data in environment extensions
        |
        v
    MakeGame command
        |
        v
JSON in .lake/gamedata/     (game.json, level__*__*.json, inventory.json)
        |
        v
Vite import.meta.glob loads JSON at build time
        |
        v
gameData.ts converts JSON to LevelDefinitions (existing client mechanism)
```

## New Packages

Two new Lean packages live at the project root:

### `LeanBlocksGame/`

The DSL framework. A fork of the *definition-oriented* subset of
`vendor/lean4game/server/GameServer/` (~2500 lines, 18 files). The four
server/runtime files (`Game.lean`, `RpcHandlers.lean`, `Runner.lean`,
`InteractiveGoal.lean`) are excluded; this package is purely about
*defining* games, not *serving* them.

### `RealAnalysisGame/`

The actual game content. Depends on `LeanBlocksGame` via a local path in
its `lakefile.toml`. For now it lives in this repo since we're developing
the framework and the example game in tandem. It can be extracted to a
standalone repo later.

## Package Structure

### LeanBlocksGame/

```
LeanBlocksGame/
  lakefile.toml
  lean-toolchain                    # leanprover/lean4:v4.28.0
  LeanBlocksGame.lean               # root import
  LeanBlocksGame/
    EnvExtensions.lean               # data structures + environment extensions
    Commands.lean                    # DSL command elaborators
    SaveData.lean                    # JSON export
    Graph.lean                       # directed graph for world dependencies
    Inventory.lean                   # inventory helpers
    Hints.lean                       # hint structures (retained for future)
    AbstractCtx.lean                 # goal abstraction for hints
    Structures.lean                  # core interactive data types
    Options.lean                     # custom Lean options
    Utils.lean                       # string utilities
    Helpers.lean                     # doc comment parsing, graph algorithms
    Helpers/
      DeclSig.lean                   # declaration signature utilities
      PrettyPrinter.lean             # statement rendering
    Tactic/
      Hint.lean                      # Hint tactic (used inside Statement proofs)
      Branch.lean                    # Branch tactic
      LetIntros.lean                 # let_intros helper
      Template.lean                  # proof template support
```

### RealAnalysisGame/

```
RealAnalysisGame/
  lakefile.toml
  lean-toolchain                    # leanprover/lean4:v4.28.0
  Game.lean                          # imports all worlds, Dependency edges, MakeGame
  Game/
    Metadata.lean                    # Mathlib imports, custom tactics, shared defs
    Levels/
      L1RealAnalysisStory.lean       # world file: imports its levels
      L1RealAnalysisStory/
        L00_the_problem.lean
        L02_rfl.lean
        ...
      L2NewtonsCalculationOfPi.lean
      L2NewtonsCalculationOfPi/
        L01.lean
      ...
```

## Modifications to the Upstream GameServer

The fork starts from the 18 definition-oriented files in
`vendor/lean4game/server/GameServer/`. The following changes are made:

### Remove external dependencies

- **`I18n`**: Strip all `.translate` calls and the `import I18n` statements.
  Can be re-added later.
- **`RpcHandlers` import**: Line 8 of `Commands.lean` imports `RpcHandlers`
  solely for translation string collection. Remove it.

### Rename namespace

`GameServer` becomes `LeanBlocksGame` throughout.

### Add Blockly-specific fields to `GameLevel` (EnvExtensions.lean)

Add fields to `GameLevel` for tracking block/affordance permissions
during elaboration:

```lean
  /-- Blockly block type names allowed in this level -/
  allowedBlocks : Array String := #[]
  /-- Affordances allowed: "apply", "rewrite", "use", "choose" -/
  allowedAffordances : Array String := #[]
  /-- If true, all affordances are allowed -/
  allAffordances : Bool := false
  /-- Optional label override for the theorem block (e.g. "Example") -/
  theoremBlockLabel : Option String := none
```

These are internal to the build. `MakeGame` resolves them (including
cumulative unlocking) and emits the final JSON in the `LevelDefinition`
shape — `permissions` as the discriminated-union array, plus
`theoremStatement`, `objects`, `assumptions`, `goal`, etc. as
top-level fields. The `objects`/`assumptions`/`goal` decomposition is
computed from the elaborated type in the `Statement` command and
stored on `GameLevel` as well.

Replace `LevelInfo` (the JSON-serializable structure) with one that
matches `LevelDefinition` exactly.

### Add Blockly DSL commands (Commands.lean)

```lean
elab "AllowBlock" args:str* : command =>
  modifyCurLevel fun level => pure {level with
    blocklyInfo := {level.blocklyInfo with
      allowedBlocks := level.blocklyInfo.allowedBlocks ++ args.map (·.getString)}}

elab "AllowAffordance" args:str* : command =>
  modifyCurLevel fun level => pure {level with
    blocklyInfo := {level.blocklyInfo with
      allowedAffordances :=
        level.blocklyInfo.allowedAffordances ++ args.map (·.getString)}}

elab "AllowAllAffordances" : command =>
  modifyCurLevel fun level => pure {level with
    blocklyInfo := {level.blocklyInfo with allAffordances := true}}

elab "TheoremBlockLabel" label:str : command =>
  modifyCurLevel fun level => pure {level with
    blocklyInfo := {level.blocklyInfo with theoremBlockLabel := label.getString}}
```

### Automatic statement decomposition (Commands.lean)

Inside the `Statement` elaborator, after elaborating the declaration
signature, decompose it into objects/assumptions/goal:

```lean
-- After: elabCommand thmStatement
-- Use forallTelescope to walk binders, isProp to classify:
--   non-Prop binders → objects (e.g. "(x : R) (y : R)")
--   Prop binders     → assumptions (e.g. "(h : x > 0)")
--   final target     → goal (e.g. "x > 0")
-- Pretty-print each group, store in blocklyInfo
```

This uses `Lean.Meta.forallTelescope` and `Lean.Meta.isProp`, the same
classification the runtime `getHypKinds` RPC already performs. Doing it
at build time produces the static Objects/Assumptions/Goal display on
the lemma block (currently hand-authored in the TypeScript level files).
The runtime `getHypKinds` RPC is still needed separately — it classifies
hypotheses in the *live goal state* as the player edits their proof.

### Cumulative block/affordance permissions (Commands.lean, in MakeGame)

During the `MakeGame` inventory computation, compute cumulative
block/affordance availability using the same pattern as tactic unlocking:

- `AllowBlock "tactic_refl"` in world W, level N makes `tactic_refl`
  available in levels N+ of W, and in all worlds that depend on W.
- `AllowAffordance "rewrite"` accumulates the same way.
- `AllowAllAffordances` in any predecessor means all affordances are
  available going forward.

The per-level JSON includes the *resolved* set of allowed blocks and
affordances. The client consumes these as flat whitelists (matching the
existing `LevelPermission` model), so no client changes are needed.

## Level Authoring Format

A level file in `RealAnalysisGame` looks like:

```lean
import Game.Metadata

World "RealAnalysisStory"
Level 2
Title "The rfl tactic"

Introduction "
# When things are identical to themselves

Sometimes in mathematics, we need to prove that something equals itself...
"

TacticDoc rfl

Statement (x y : R) : x ^ 2 + 2 * y = x ^ 2 + 2 * y := by
  rfl

NewTactic rfl

-- Blockly-specific:
AllowBlock "prop" "tactic_apply" "tactic_refl"

Conclusion "
Excellent! You've learned the `rfl` tactic...
"
```

This is intentionally close to the existing Lean4Game format. An author
familiar with Lean4Game needs to learn only the `AllowBlock`,
`AllowAffordance`, `AllowAllAffordances`, and `TheoremBlockLabel` commands.

## Client Integration

The client reads `.lake/gamedata/` JSON directly via Vite's
`import.meta.glob`. The per-level JSON is 1:1 with `LevelDefinition`:

### Per-level JSON format

`MakeGame` emits each level's JSON in exactly the `LevelDefinition`
shape, so the client can consume it with no conversion. The per-level
file (`level__<World>__<N>.json`) contains:

```json
{
  "name": "The rfl tactic",
  "theoremName": "RealAnalysisStory_2",
  "theoremStatement": "(x y : ℝ) : x ^ 2 + 2 * y = x ^ 2 + 2 * y",
  "theoremBlockLabel": null,
  "objects": "(x y : ℝ)",
  "assumptions": null,
  "goal": "x ^ 2 + 2 * y = x ^ 2 + 2 * y",
  "permissions": [
    { "t": "allowTactic", "tacticName": "prop" },
    { "t": "allowTactic", "tacticName": "tactic_refl" }
  ],
  "introduction": "# When things are identical...",
  "conclusion": "Excellent! You've learned..."
}
```

This means `MakeGame` is responsible for:
- Emitting `theoremStatement` as the bare signature (no `theorem`
  keyword, no name, no `:= by`).
- Emitting `theoremName` as the Lean declaration name (from the
  `Statement` command's optional name, or a synthetic `WorldId_N`
  fallback).
- Computing `objects`/`assumptions`/`goal` from the elaborated type
  at build time.
- Assembling the `permissions` array in the `LevelPermission`
  discriminated-union format from the cumulative `AllowBlock`,
  `AllowAffordance`, and `AllowAllAffordances` state.

### Game-level field mapping

| JSON (`game.json`) | `GameData` derivation |
|-|-|
| `worlds.nodes[id].title` | `worlds[i].name` |
| `worlds.edges` | `worlds[i].dependsOn` |
| world id | `worlds[i].id` |

During the migration period, both the hand-authored TypeScript levels
and the JSON-loaded levels coexist. The world list in `gameData.ts` can
be derived from `game.json` or remain hand-authored, with JSON levels
merged in for worlds that have been ported to the DSL.

## Lean Toolchain

`LeanBlocksGame` and `RealAnalysisGame` use **leanprover/lean4:v4.28.0**,
matching `vendor/RealAnalysisGame` and `vendor/lean4game/server/`.

## Implementation Milestones

The migration is smooth and incremental. Both the existing `.ts` level
definitions and JSON-loaded levels coexist throughout, so we can
compare outputs and catch regressions at each step. The goal is to get
a single level working end-to-end as quickly as possible, then widen
scope incrementally.

### Coexistence mechanism

`gameData.ts` loads levels from two sources:

1. **Existing**: `import.meta.glob('./levels/*/*.ts')` — the current
   hand-authored TypeScript files.
2. **New**: `import.meta.glob('../../RealAnalysisGame/.lake/gamedata/level__*__*.json')`
   — JSON emitted by `MakeGame`.

Both produce `LevelDefinition` objects. For a given world, the JSON
source takes precedence if present; otherwise the TypeScript source is
used. This means:

- Porting a single level or world to the DSL doesn't require touching
  any other levels.
- The hand-authored `.ts` file can be kept alongside the JSON version
  for comparison/testing, then deleted once validated.
- Tutorials (`*_tutorial.ts`) remain as TypeScript files throughout,
  matched by filename convention as today.

### Milestone 1: LeanBlocksGame compiles

Fork the 18 definition-oriented files from
`vendor/lean4game/server/GameServer/` into `LeanBlocksGame/`. Remove
`I18n`, `RpcHandlers` import. Rename namespace to `LeanBlocksGame`.
Add `BlocklyInfo` fields to `GameLevel`. Add `AllowBlock`,
`AllowAffordance`, `AllowAllAffordances`, `TheoremBlockLabel`
commands. Stub out the statement decomposition and `MakeGame` JSON
output changes (can emit placeholder values for now).

**Done when**: `cd LeanBlocksGame && lake build` succeeds.

### Milestone 2: RealAnalysisGame with one level emits JSON

Create `RealAnalysisGame/` with `lakefile.toml`, `lean-toolchain`,
`Game/Metadata.lean`, one world file, and one level file
(e.g. `L00_the_problem.lean`). Write `Game.lean` with one `Dependency`
and `MakeGame`. The level file uses the DSL commands including
`AllowBlock`.

**Done when**: `cd RealAnalysisGame && lake build` succeeds and
`.lake/gamedata/level__RealAnalysisStory__1.json` exists with the
correct `LevelDefinition`-shaped content.

### Milestone 3: Client loads one JSON level alongside .ts levels

Add the JSON glob to `gameData.ts`. The single DSL-authored level
loads alongside the existing `.ts` levels. Compare the resulting
`LevelDefinition` against the hand-authored `.ts` version — all
fields should match (name, theoremName, theoremStatement, objects,
assumptions, goal, permissions, theoremBlockLabel, introduction,
conclusion). Verify the level plays identically in the app.

**Done when**: `npm run dev` loads the JSON-authored level and it
behaves identically to its hand-authored `.ts` counterpart.

### Milestone 4: Statement decomposition works

Implement the `forallTelescope`/`isProp` decomposition in the
`Statement` elaborator so that `objects`, `assumptions`, `goal` are
computed automatically from the Lean type. Remove the need to
hand-author these fields.

**Done when**: The JSON for the test level has correct `objects`,
`assumptions`, `goal` values matching the hand-authored `.ts` file,
without any manual specification in the `.lean` source.

### Milestone 5: Cumulative permissions work

Implement cumulative block/affordance unlocking in `MakeGame` — the
same pattern as the upstream tactic unlocking, extended to
`AllowBlock`/`AllowAffordance`/`AllowAllAffordances`. The resolved
`permissions` array appears in each level's JSON.

**Done when**: A multi-level world correctly inherits permissions
from earlier levels, matching the hand-authored `.ts` equivalents.

### Milestone 6: One full world ported

Port all ~9 levels of `RealAnalysisStory` to the DSL. Validate each
against the existing `.ts` version. The `.ts` files for this world
can be deleted once confirmed.

**Done when**: The RealAnalysisStory world loads entirely from JSON
and plays identically to before.

### Milestone 7: Incremental expansion

Port additional worlds one at a time, validating each. The
hand-authored `.ts` files for unported worlds continue to work
unchanged. Once all worlds are ported, remove the TypeScript level
files and the first glob from `gameData.ts`.

### Milestone 8: Cleanup

Remove any remaining code that imports old data, as well as comments
that pertain to that process.

## Deferred Work

- **Inventory browser UI**: The DSL captures `TacticDoc`, `TheoremDoc`,
  `DefinitionDoc` and the `NewTactic`/`NewTheorem`/`NewDefinition`
  unlocking. The JSON includes this data. Building a client-side inventory
  browser is separate work.
- **Hints**: The DSL retains `Hint` and `Branch` tactics from upstream.
  Building a client-side hint display is separate.
- **Tutorials**: Remain as TypeScript files; not represented in the DSL.
- **Toolchain bump**: `Projects/MathlibDemo` currently uses
  v4.25.0-rc2 and will need to be bumped to v4.28.0 to match. This
  is independent of the DSL work and can happen in parallel.
