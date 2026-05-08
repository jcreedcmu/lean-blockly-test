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

### Add `BlocklyInfo` structure (EnvExtensions.lean)

```lean
structure BlocklyInfo where
  /-- Blockly block type names allowed in this level (e.g. "tactic_apply") -/
  allowedBlocks : Array String := #[]
  /-- Affordances allowed: "apply", "rewrite", "use", "choose" -/
  allowedAffordances : Array String := #[]
  /-- If true, all affordances are allowed -/
  allAffordances : Bool := false
  /-- Decomposed statement: the non-Prop binders (e.g. "(x : R)") -/
  objects : String := ""
  /-- Decomposed statement: the Prop binders (e.g. "(h : x > 0)") -/
  assumptions : String := ""
  /-- Decomposed statement: the target type (e.g. "x > 0") -/
  goal : String := ""
  /-- Optional label override for the theorem block (e.g. "Example").
      Default is derived from the statement name by the ingestion script. -/
  theoremBlockLabel : Option String := none
deriving ToJson, FromJson, Repr, Inhabited
```

Add `blocklyInfo : BlocklyInfo := default` to `GameLevel`.
Add corresponding fields to `LevelInfo` for JSON serialization.

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

## Prerequisite: LevelDefinition Refactor

See `plans/level-definition-refactor.md` (includes a detailed glossary
of all name-like fields with examples). Before or alongside this work,
`LevelDefinition` should be refactored to hold abstract theorem data
(theoremStatement, theoremName, objects, assumptions, goal, theoremBlockLabel,
permissions) rather than a pre-built `BlocklyState`. After that refactor,
`LevelDefinition` and the JSON output from `MakeGame` share essentially
the same shape.

## Client Integration

The client reads `.lake/gamedata/` JSON directly via Vite's
`import.meta.glob`. After the LevelDefinition refactor, the per-level
JSON maps nearly 1:1 to `LevelDefinition`:

### Per-level field mapping

| JSON field (`level__*__*.json`) | `LevelDefinition` field |
|-|-|
| `title` | `name` |
| `index` | (used for ordering) |
| `introduction` | `introduction` |
| `conclusion` | `conclusion` |
| `descrFormat` (strip keyword + `:= by`) | `theoremStatement` |
| `statementName` (or `WorldId_N` fallback) | `theoremName` |
| `blocklyInfo.objects` | `objects` |
| `blocklyInfo.assumptions` | `assumptions` |
| `blocklyInfo.goal` | `goal` |
| `blocklyInfo.theoremBlockLabel` | `theoremBlockLabel` |
| `blocklyInfo.allowedBlocks` | `permissions` (`allowTactic` entries) |
| `blocklyInfo.allowedAffordances` | `permissions` (`allowAffordance` entries) |
| `blocklyInfo.allAffordances` | `permissions` (`allowAllAffordances`) |

The only non-trivial mappings are:
- `descrFormat` needs the keyword (`theorem`/`def`/`example`) and
  trailing `:= by` stripped.
- `blocklyInfo.allowed*` fields are converted to the `LevelPermission`
  discriminated union format.

These could potentially be eliminated entirely by having `MakeGame`
emit the JSON in exactly the `LevelDefinition` shape (with `theoremStatement`
pre-stripped and `permissions` pre-formatted). This is a design choice:
keeping the JSON format "neutral" vs. making it client-native.

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

All Lean packages in the project use **leanprover/lean4:v4.28.0**. This
matches `vendor/RealAnalysisGame` and `vendor/lean4game/server/`, so
the fork into `LeanBlocksGame` and the porting of level files from
vendor require no toolchain-related adjustments.

`Projects/MathlibDemo` (the runtime `lake serve` target) currently uses
v4.25.0-rc2 and will be bumped to v4.28.0 to match. This requires
updating its mathlib dependency to a compatible revision and verifying
that `Preamble.lean` and the other library modules still compile.

## Migration Strategy

1. Both systems coexist: hand-authored TypeScript levels and DSL-generated
   levels can live side by side in `client/src/levels/`.
2. Port one world at a time from hand-authored to DSL-generated.
3. Validate each ported world by comparing the generated TypeScript against
   the hand-authored version.
4. Once all worlds are ported, remove the hand-authored files.
5. Tutorials (`*_tutorial.ts`) remain hand-authored for now; they're loaded
   separately and matched by filename convention.

## MVP Scope

The minimum viable product validates the full pipeline end-to-end:

1. `LeanBlocksGame/` compiles with `lake build`.
2. `RealAnalysisGame/` with one world (RealAnalysisStory, ~9 levels)
   compiles and produces `.lake/gamedata/` JSON with Blockly fields.
3. `gameData.ts` loads the JSON and converts it to `LevelDefinition`s.
4. The app loads and the tutorial world works identically.

## Deferred Work

- **Inventory browser UI**: The DSL captures `TacticDoc`, `TheoremDoc`,
  `DefinitionDoc` and the `NewTactic`/`NewTheorem`/`NewDefinition`
  unlocking. The JSON includes this data. Building a client-side inventory
  browser is separate work.
- **Hints**: The DSL retains `Hint` and `Branch` tactics from upstream.
  Building a client-side hint display is separate.
- **Tutorials**: Remain as TypeScript files; not represented in the DSL.
- **Full game port**: After MVP, port remaining ~35 worlds.
