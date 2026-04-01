# Plan: Distinguish Term Variables from Assumptions

## Goal

In the blockly game interface, visually separate hypotheses into two groups:
- **Objects**: term variables like `x : Nat`, `f : R -> R` (type is a `Type`/`Sort`)
- **Assumptions**: propositional hypotheses like `h : x > 0`, `hne : x != c` (type is a `Prop`)

This matches what lean4game does in its interface.

## Approach: Inline `@[server_rpc_method]` in the Preamble

The key insight is that Lean's `@[server_rpc_method]` attribute registers an RPC
method at elaboration time. Any RPC call at a position *after* the definition can
invoke it. Since we already send a preamble before the user's proof code, we can
define a custom RPC method directly in that preamble — no server-side Lean package
or server code changes required.

### How lean4game does it (for reference)

lean4game defines extended structures in `GameServer.Structures` and a custom
`goalToInteractive` in `GameServer.InteractiveGoal`. The critical line is:

```lean
isAssumption? := if (← inferType type).isProp then true else none
```

This checks whether each hypothesis's type lives in `Prop` (via `inferType` which
gives the type-of-the-type, then `.isProp`). lean4game serves this through a custom
`Game.getProofState` RPC method called from its client.

### Our approach

We don't need the full lean4game machinery. We define a minimal `@[server_rpc_method]`
in the preamble that:

1. Takes goal position params
2. Calls the standard `getInteractiveGoals` to get the goals with their `MVarId`s
3. For each goal, iterates the local context and checks `(← inferType type).isProp`
   for each hypothesis
4. Returns a mapping from `FVarId` to `Bool` (is-assumption)

The client then joins this mapping with the standard `InteractiveGoal.hyps` data
it already has.

## Implementation Steps

### Step 1: Write and validate the preamble RPC method

Write a small Lean snippet that defines the `@[server_rpc_method]`. Validate it
works by testing on live.lean-lang.org (or locally) — define the method, then
confirm it can be called via RPC at a position after the definition.

The method signature would be something like:

```lean
structure HypKindResult where
  goals : Array (Array (String × Bool))  -- per goal: array of (fvarId, isAssumption)
  deriving FromJson, ToJson

@[server_rpc_method]
def getHypKinds (p : Lean.Lsp.PlainGoalParams) :
    Lean.Server.RequestM (Lean.Server.RequestTask HypKindResult) := do
  -- get goals at position, iterate local contexts, check isProp
  ...
```

Open questions for this step:
- What imports are needed? `import Lean` should suffice (it brings in
  `Lean.Server`, `Lean.Meta`, `Lean.Widget`, etc.), but we already import
  `Mathlib` which transitively includes everything.
- Can we reuse `Lean.Widget.FileWorker.getInteractiveGoals` internals, or
  do we need to walk the info tree ourselves?
- What's the most compact way to identify hypotheses? `FVarId` as string is
  the natural key since the client already receives `fvarIds` in
  `InteractiveHypothesisBundle`.

### Step 2: Add the method to the preamble in `App.tsx`

Extend the `prelude` string in `client/src/App.tsx` (currently lines 50-55) to
include the `@[server_rpc_method]` definition. Update `preludeLines` accounting
(already handled dynamically via `prelude.split('\n').length - 1`).

### Step 3: Add an RPC call in `LeanRpcSession.ts`

After the existing `getInteractiveDiagnostics` call in `getGoals()`, add a second
RPC call to our custom method:

```ts
const hypKinds = await this.connection.sendRequest('$/lean/rpc/call', {
  textDocument: { uri: this.uri },
  position: { line: preludeLines, character: 0 },  // after preamble
  sessionId: this.sessionId,
  method: 'getHypKinds',
  params: { textDocument: { uri: this.uri }, position: { line: ..., character: 0 } },
});
```

The position for the RPC *call dispatch* must be after the `@[server_rpc_method]`
definition. The position in the *params* should be at the tactic whose goal state
we want.

The return type of `getGoals` would be extended to include the hyp-kind mapping
alongside the existing `InteractiveGoals`.

### Step 4: Update the infoview components

In `client/src/infoview/Goal.tsx`:
- Accept a `hypKinds` map (fvarId -> isAssumption) as a prop
- Split `hyps` into two groups based on the map
- Render "Objects" and "Assumptions" sections with headers (like lean4game's
  `goals.tsx` lines 187-201)

In `client/src/infoview/infoview.css`:
- Add styles for `.hyp-group` and `.hyp-group-title`

### Step 5: Thread the data through

- `App.tsx`: pass `hypKinds` from `getGoals` result down to `<Goals>`
- `Goals.tsx`: pass it through to `<Goal>`
- `Goal.tsx`: use it to split hypotheses

## Future Improvement: Preamble as an Imported Module

Currently the preamble is inlined in the Lean source sent to the server. This
works but has downsides:
- The preamble gets re-elaborated on every document change
- Line number offset bookkeeping is fragile
- The preamble will grow as we add more custom RPC methods

A cleaner approach (not for this PR) would be to use `textDocument/didOpen` to
create a *second* virtual file (e.g., `file:///blockly/Preamble.lean`) containing
the preamble code, and then have the main file `import Preamble`. The Lean server
should treat it as a separate module that only needs elaboration once.

This would require:
- Sending a second `textDocument/didOpen` for the preamble file
- Investigating whether Lean's LSP server resolves imports from virtual documents
  (it may require the URI to map to a real path in a `lakefile.lean` project)
- Possibly using `lake env` or similar to configure the search path

We're not doing this yet, but it's the natural next step once the preamble grows
beyond a few definitions.

## Key Files

| File | Change |
|------|--------|
| `client/src/App.tsx` | Extend `prelude` with RPC method; thread `hypKinds` to Goals |
| `client/src/LeanRpcSession.ts` | Add `getHypKinds()` RPC call; extend `getGoals()` return type |
| `client/src/infoview/Goal.tsx` | Split hyps into Objects/Assumptions sections |
| `client/src/infoview/Goals.tsx` | Pass `hypKinds` through |
| `client/src/infoview/infoview.css` | Styles for grouped hypothesis sections |

## Reference: lean4game Implementation

- `vendor/lean4game/server/GameServer/Structures.lean` — extended `InteractiveHypothesisBundle` with `isAssumption?`
- `vendor/lean4game/server/GameServer/InteractiveGoal.lean` — `goalToInteractive` with `isProp` check
- `vendor/lean4game/client/src/components/infoview/goals.tsx` — client-side filtering into Objects/Assumptions
