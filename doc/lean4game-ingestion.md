# Ingesting lean4game JSON into the Blockly client

## Overview

The lean4game build (`lake build` on a game project) produces JSON files
in `.lake/gamedata/`. This document compares the data structures in
that JSON with the `LevelSource`/`LevelDefinition` types used by our
Blockly client, and identifies what impedance matching is needed.

## File layout

lean4game produces:
- `game.json` — game metadata, world graph (nodes + edges), world sizes
- `level__<WorldId>__<N>.json` — one file per level
- `inventory.json` — all tactic/theorem/definition documentation
- `doc__<Kind>__<Name>.json` — individual item docs

Our client currently uses:
- `client/src/levels/<WorldId>/<file>.ts` — one TypeScript file per level,
  each exporting a `LevelSource` object
- `client/src/gameData.ts` — assembles everything into a `GameData` at
  build time via `import.meta.glob`

## Game-level structure

| Concept | lean4game `game.json` | Blockly `GameData` |
|---|---|---|
| Game title | `title` | not stored (implicit) |
| Game intro | `introduction` | not stored |
| World list | `worlds.nodes` (dict keyed by id) | `worlds` (array of `World`) |
| World name | `worlds.nodes[id].title` | `worlds[i].name` |
| World intro | `worlds.nodes[id].introduction` | not stored at world level |
| World deps | `worlds.edges` (array of `[from, to]` pairs) | `worlds[i].dependsOn` (array of ids) |
| Level count | `worldSize[id]` | `worlds[i].levels.length` |
| Levels | separate `level__*__*.json` files | inline in `worlds[i].levels` |

### What lean4game has that we don't use
- `tile` — landing-page card display info (title, short description, image, languages)
- `settings` — game-wide options (e.g. `allowAnonymousPlayer`)
- `authors`, `info`, `conclusion`, `image`
- `worldSize` — redundant if levels are loaded

### What we have that lean4game doesn't produce
- `World.description` — we have an optional field; lean4game uses `introduction` instead

## Level structure

| Concept | lean4game `level__*__*.json` | Blockly `LevelSource` |
|---|---|---|
| Level name | `title` | `name` |
| Level index | `index` (1-based) | `level` (1-based) |
| Introduction text | `introduction` | `introduction` |
| Conclusion text | `conclusion` | `conclusion` |
| Theorem statement | `descrFormat` (e.g. `"example (x : ℝ) (h : x = 5) : x = 5 := by"`) | `statement` (e.g. `"(x : ℝ) (h : x = 5) : x = 5"`) |
| Theorem name | `statementName` (often `"[anonymous]"`) | `theoremName` |
| Description | `descrText` (human-readable summary) | not stored separately |
| Module path | `module` (Lean module name) | `world` (just the world id) |

### Tactic/block availability

This is the biggest structural difference.

**lean4game** has a rich inventory system per level:
- `tactics`: array of `{ name, displayName, locked, new, disabled, hidden, category, ... }`
- `lemmas`: same shape, for lemma/theorem references
- `definitions`: same shape, for definition references

Each item carries `locked` (not yet introduced), `new` (introduced this level),
`disabled` (explicitly forbidden), `hidden`, etc. The game progressively
unlocks tactics as the player advances.

**Blockly** has a simpler permissions model:
- `permissions`: array of `LevelPermission` discriminated unions:
  - `{ t: 'allowTactic', tacticName: string }` — whitelist a specific block
  - `{ t: 'allowAffordance', affordance: 'rewrite' | 'apply' | ... }` — whitelist a drag affordance
  - `{ t: 'allowAllAffordances' }` — unrestrict affordances
- If `permissions` is absent, all blocks are available.

**Mapping**: lean4game's unlocked+not-disabled tactics → Blockly's `allowTactic` permissions.
The `locked`/`new`/`disabled` flags could be collapsed into a simple whitelist.
lean4game's `lemmas` and `definitions` have no direct Blockly equivalent since
Blockly doesn't have blocks for invoking specific lemmas or definitions by name
(users type them into free-text fields).

### Theorem statement parsing

**lean4game** provides `descrFormat` as a single string like:
```
"example (x : ℝ) (h : x = 5) : x = 5  := by"
```

**Blockly** needs the statement decomposed into:
- `statement`: `"(x : ℝ) (h : x = 5) : x = 5"` (the raw declaration for codegen)
- `objects`: `"(x : ℝ)"` (display only)
- `assumptions`: `"(h : x = 5)"` (display only)
- `goal`: `"x = 5"` (display only)

The `objects`/`assumptions`/`goal` split is currently hand-authored. An ingestion
pipeline would need to parse the Lean declaration signature to decompose it, or
this could be done in the Lean metaprogramming layer (the `getHypKinds` RPC
method already classifies hypotheses at runtime; a build-time equivalent could
produce the decomposition).

### Initial workspace state

**lean4game** doesn't produce anything like this — the lean4game client is a
text editor, not a block workspace. 

**Blockly** needs `initial: BlocklyState` — a serialized Blockly workspace
containing a pre-placed `lemma` block with the theorem name and declaration
fields set. This is synthesized by `makeLevelState()` in `gameData.ts`.

This is purely a Blockly concern and can be generated mechanically from the
theorem name and statement.

### What lean4game has that we don't use (per-level)
- `template` — pre-filled proof template text
- `lemmaTab` — default tab to show in the lemma browser
- `descrText` — human-readable one-line summary of the exercise
- `displayName` — alternative display name for the statement
- `image` — level-specific image
- Hint system (not in the JSON, delivered via LSP at runtime)

### What we have that lean4game doesn't produce
- `theoremBlockLabel` — display-only label override (e.g. "Example")
- `objects` / `assumptions` / `goal` — decomposed signature for block display
- `permissions` with affordance control — lean4game only controls tactic/lemma availability

## Proposed ingestion pipeline

1. Read `game.json` → build `World[]` with ids, names, dependency edges
2. For each level file `level__<world>__<N>.json`:
   - Map `title` → `name`, `index` → `level`
   - Map `introduction`, `conclusion` directly
   - Parse `descrFormat` to extract `statement` (strip `theorem`/`example` keyword and trailing `:= by`)
   - Extract or synthesize `theoremName` from `statementName` (use world+index if anonymous)
   - Derive `objects`/`assumptions`/`goal` by parsing the declaration signature (or leave empty and rely on runtime display)
   - Convert unlocked tactics to `permissions` array
   - Generate `initial` BlocklyState via `makeLevelState()`
3. Output `LevelSource` objects (or directly `LevelDefinition`)
