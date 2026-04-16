## Project Summary

This is an experimental, pedagogically-oriented web app that uses
[Blockly](https://developers.google.com/blockly) as a drag-and-drop interface
for constructing tactic proofs in [Lean 4](https://lean-lang.org/). Users
assemble blocks representing tactics; the app translates the workspace into
Lean tactic source, sends it via LSP to a `lake serve` subprocess running
against `Projects/MathlibDemo/`, and renders back the goal state and
diagnostics. It is derived from
[Lean4Web](https://github.com/leanprover-community/lean4web) and currently
hosts level content adapted from Alex Kontorovich's Real Analysis course.

The high-level architecture is:

```
Browser (React + Blockly)  ↕ WebSocket/JSON-RPC ↕  Node relay (server/index.mjs)  ↕ stdio ↕  lake serve
```

See `doc/Architecture.md` for the full data flow, including the preamble
split (on-disk `Projects/MathlibDemo/MathlibDemo/Preamble.lean` plus an
in-memory prelude in `LevelEvaluator.ts`) and the custom `getHypKinds` RPC
method used to classify hypotheses as objects vs. assumptions.

## Directory Map

- `client/src/` — React + Blockly frontend.
  - `blocks.ts` — Blockly block *definitions* (one entry per block `type`,
    including `message0`, connections, tooltip, style). This is where you
    rename a block, change its label, or add a new one.
  - `toolbox.ts` — Which blocks appear in the toolbox palette and in what
    category. New block types must be registered here to be visible.
  - `workspaceToLean.ts` — Converts a Blockly workspace into Lean tactic
    text. Has a `case 'tactic_<name>':` per block `type` that emits the
    actual Lean tactic string. **The block `type` and the Lean tactic
    emitted are independent** — e.g. a block typed `tactic_ring_nf` could
    be relabeled `ring` while still emitting `ring_nf\n`.
  - `LevelEvaluator.ts`, `LeanSessionManager.ts`, `LeanSession.ts`,
    `LeanLspClient.ts` — Lean LSP transport and domain layers (see
    `doc/Architecture.md`).
  - `App.tsx`, `Blockly.tsx`, `infoview/` — UI.
  - `levels/` — One subdirectory per "world" (Lecture*, L*Pset,
    RealAnalysisStory, ...); each `.ts` file inside is one level with its
    starting workspace and goal.
- `server/index.mjs` — Express + WebSocket relay; spawns `lake serve` per
  client and rewrites virtual `file:///blockly/...` URIs to real paths.
- `Projects/MathlibDemo/` — The Lake project the server runs. Contains
  `MathlibDemo/Preamble.lean` (the on-disk part of the preamble — defines
  the `getHypKinds` `@[server_rpc_method]` and imports Mathlib).
- `doc/` — `Architecture.md`, `Development.md`, `Installation.md`, `Usage.md`.
- `plans/` — Design notes for in-progress refactors.
- `cypress/` — End-to-end tests.

## Conventions

- Block `type` strings are namespaced with a kind prefix, e.g. `tactic_*`,
  `term_*`. The user-visible label is `message0` in `blocks.ts`; it is
  separate from both the block `type` and the Lean source emitted by
  `workspaceToLean.ts`. Renaming what the user sees does not require
  changing either of the others.
- When adding or renaming a block, three files are typically involved:
  `blocks.ts` (definition), `toolbox.ts` (palette registration), and
  `workspaceToLean.ts` (Lean codegen).

## GitHub API Access

A GitHub personal access token is stored in `.env` as `GH_TOKEN`. To use it with the `gh` CLI:

```bash
source .env && gh <command>
```
