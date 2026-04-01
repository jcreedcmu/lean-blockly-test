# How Lean's LSP RPC Mechanism Works (and How Web Apps Use It)

## The Core Idea

Lean's language server extends the standard LSP protocol with four custom JSON-RPC methods under `$/lean/rpc/`. These let clients call arbitrary Lean functions on the server and manipulate heavyweight Lean objects (like `Expr`, `Environment`, `MessageData`) without serializing them — the client gets **opaque numeric references** instead.

The core code lives in:
- `src/Lean/Server/Rpc/Basic.lean` — Core types: `RpcRef`, `WithRpcRef`, `RpcObjectStore`, `RpcEncodable`
- `src/Lean/Server/Rpc/RequestHandling.lean` — Registration of RPC methods, `@[server_rpc_method]` attribute, call dispatch
- `src/Lean/Server/Rpc/Deriving.lean` — `deriving RpcEncodable` handler
- `src/Lean/Data/Lsp/Extra.lean` — LSP protocol types: `RpcCallParams`, `RpcConnectParams`, etc.
- `src/Lean/Server/FileWorker.lean` — Session management, connect/release/keepAlive handlers
- `src/Lean/Server/FileWorker/WidgetRequests.lean` — Builtin RPC method implementations

## The Four RPC Endpoints

| Method | Type | Purpose |
|--------|------|---------|
| `$/lean/rpc/connect` | Request | Opens an RPC session for a document URI, returns a `sessionId` |
| `$/lean/rpc/call` | Request | Calls a named Lean function with JSON params, returns JSON result |
| `$/lean/rpc/release` | Notification | Tells server the client no longer needs certain object references |
| `$/lean/rpc/keepAlive` | Notification | Must be sent every 10s or the session expires after 30s |

### `$/lean/rpc/connect`

```
params:  { uri: DocumentUri }
result:  { sessionId: UInt64 }
```

Opens an RPC session for a file. Returns a random session ID. Multiple sessions can coexist.

### `$/lean/rpc/call`

```
params: {
  textDocument: { uri: DocumentUri },
  position: { line: Nat, character: Nat },
  sessionId: UInt64,
  method: Name,          -- fully qualified, e.g. "Lean.Widget.getInteractiveGoals"
  params: Json           -- RPC-encoded parameters
}
result: Json             -- RPC-encoded response
```

The **position** is critical — it determines which Lean snapshot is used, meaning which definitions/imports are in scope. An RPC method defined via `@[server_rpc_method]` is only available at positions *after* the code defining it has been elaborated.

Example JSON-RPC message:

```json
{
  "jsonrpc": "2.0",
  "id": 42,
  "method": "$/lean/rpc/call",
  "params": {
    "textDocument": { "uri": "file:///path/to/File.lean" },
    "position": { "line": 10, "character": 0 },
    "sessionId": 12345678,
    "method": "Lean.Widget.getInteractiveGoals",
    "params": {
      "textDocument": { "uri": "file:///path/to/File.lean" },
      "position": { "line": 10, "character": 0 }
    }
  }
}
```

### `$/lean/rpc/release`

```
params: {
  uri: DocumentUri,
  sessionId: UInt64,
  refs: Array Json       -- array of RpcRef values to release
}
```

Tells the server the client no longer needs certain references. The server maintains a reference count; you must release a reference as many times as you received it.

### `$/lean/rpc/keepAlive`

```
params: {
  uri: DocumentUri,
  sessionId: UInt64
}
```

Must be sent every 10 seconds. After 30 seconds of inactivity, the server drops the session and all its references.

## Opaque References (`WithRpcRef` and `RpcRef`)

Some types (like `MessageData`, `InfoWithCtx`) are too complex to serialize as JSON. The key abstraction is `WithRpcRef α`. On the server side, it wraps a value of type `α` with a unique `id`. On the wire, it becomes an opaque reference — just a number.

**Wire format** (negotiated at initialization via `ClientCapabilities.rpcWireFormat`):
- **v0 (legacy)**: References serialized as `{"p": n}`
- **v1 (current default)**: References serialized as `{"__rpcref": n}`

The `RpcObjectStore` (per session) tracks:
- `aliveRefs`: maps `RpcRef` → `(Dynamic, id, refcount)` — the actual objects being held alive
- `refsById`: maps object `id` → `RpcRef` — enables reusing the same ref for the same object
- `nextRef`: monotonically increasing counter for fresh refs

When the server encodes a `WithRpcRef α`, it stores the value in the `RpcObjectStore` and sends just the numeric reference. When decoding, it looks up the reference and retrieves the typed value using `Dynamic`. References are reference-counted and must be explicitly released.

## Defining Custom RPC Methods (Server Side, in Lean)

There are two mechanisms:

### A. `@[server_rpc_method]` attribute (for user code)

A function must have the signature `α → RequestM (RequestTask β)` where `[RpcEncodable α]` and `[RpcEncodable β]`.

```lean
structure MyParams where
  name : String
  deriving RpcEncodable

structure MyResult where
  greeting : String
  deriving RpcEncodable

@[server_rpc_method]
def myMethod (p : MyParams) : RequestM (RequestTask MyResult) :=
  RequestM.pureTask do
    return { greeting := s!"Hello, {p.name}!" }
```

Under the hood, `registerRpcProcedure` wraps the function with `wrapRpcProcedure` which handles session lookup, JSON decoding via `RpcEncodable`, and encoding the response. The wrapped procedure is stored in `userRpcProcedures` (a `MapDeclarationExtension`), keyed by the fully qualified name.

### B. `registerBuiltinRpcProcedure` (for core Lean)

Used by built-in procedures that need to exist without importing additional modules. Called in `builtin_initialize` blocks:

```lean
builtin_initialize
  registerBuiltinRpcProcedure
    `Lean.Widget.getInteractiveGoals
    Lsp.PlainGoalParams
    (Option InteractiveGoals)
    FileWorker.getInteractiveGoals
```

### The `RpcEncodable` Typeclass

```lean
class RpcEncodable (α : Type) where
  rpcEncode : α → StateM RpcObjectStore Json
  rpcDecode : Json → ExceptT String (ReaderT RpcObjectStore Id) α
```

- Encoding is `StateM RpcObjectStore Json` because it may need to store new references.
- Decoding is `ReaderT RpcObjectStore` because it may need to look up existing references.
- Any type with `FromJson`/`ToJson` automatically gets an `RpcEncodable` instance (plain JSON round-trip).
- `WithRpcRef α` has a special instance that serializes to/from the opaque reference format.
- You can `deriving RpcEncodable` on structures and inductives.

## Call Dispatch (`handleRpcCall`)

When the server receives a `$/lean/rpc/call`:

1. First checks `builtinRpcProcedures` (a persistent hash map). If found, runs it immediately.
2. Otherwise, searches `userRpcProcedures` by waiting for the snapshot at the call position. User RPC methods are only available if the code defining them has been elaborated at/before the given position.
3. If neither is found, returns a `methodNotFound` error.

The `wrapRpcProcedure` function:
- Looks up the RPC session by `sessionId`, returning `rpcNeedsReconnect` error if not found
- Decodes params from JSON using `rpcDecode` (which may resolve `RpcRef`s back to objects)
- Calls the handler
- Encodes the response using `rpcEncode` (which may store new objects and return `RpcRef`s)
- Both decode and encode operate on the session's `RpcObjectStore`, which is mutated atomically via `IO.Ref`

## RPC Session Lifecycle

1. **Connect**: Client sends `$/lean/rpc/connect` with a document URI. Server creates an `RpcSession` with a random `UInt64` ID and an empty `RpcObjectStore`.
2. **Calls**: Client sends `$/lean/rpc/call`. Responses may contain `RpcRef`s (opaque numbers). The client must hold these and pass them back in future calls.
3. **KeepAlive**: Client must send `$/lean/rpc/keepAlive` every 10 seconds. Sessions expire after 30 seconds of inactivity (`keepAliveTimeMs = 30000`).
4. **Release**: Client sends `$/lean/rpc/release` with refs it no longer needs.
5. **Reconnect**: If the server drops a session (crash, timeout, file re-elaboration), subsequent calls return error code `rpcNeedsReconnect`. The client should discard all references and call `$/lean/rpc/connect` again.

## Built-in RPC Methods

| Method | Params | Response |
|--------|--------|----------|
| `Lean.Widget.getInteractiveGoals` | `PlainGoalParams` | `Option InteractiveGoals` |
| `Lean.Widget.getInteractiveTermGoal` | `PlainTermGoalParams` | `Option InteractiveTermGoal` |
| `Lean.Widget.getInteractiveDiagnostics` | diagnostic params | `Array InteractiveDiagnostic` |
| `Lean.Widget.InteractiveDiagnostics.msgToInteractive` | `MsgToInteractive` (contains `WithRpcRef MessageData`) | `InteractiveMessage` |
| `Lean.Widget.InteractiveDiagnostics.infoToInteractive` | `WithRpcRef InfoWithCtx` | `InfoPopup` |
| `Lean.Widget.getGoToLocation` | `GetGoToLocationParams` | `Array LocationLink` |
| `Lean.Widget.lazyTraceChildrenToInteractive` | `WithRpcRef LazyTraceChildren` | `Array InteractiveMessage` |
| `Lean.Widget.highlightMatches` | `HighlightMatchesParams` | `HighlightedInteractiveMessage` |
| `Lean.Widget.getWidgetSource` | `GetWidgetSourceParams` | `WidgetSource` |
| `Lean.Widget.getWidgets` | `Position` | `GetWidgetsResponse` |

---

# Case Study: lean4game

## Architecture

```
Browser (React) ←WebSocket→ Node.js Relay ←stdin/stdout→ Lean server (lake serve)
```

The relay (`relay/src/serverProcess.ts`) spawns one Lean server per player and does **message translation** between the browser and Lean.

## Message Translation Layer

When the player types a tactic proof, the relay wraps it in a synthetic Lean file:

```lean
import Game.Levels.MyLevel
import GameServer.Runner
Runner "MyGame" "MyWorld" 3 (difficulty := 2) (inventory := [...]) := by
  <player's tactic proof here>
```

Line numbers are shifted by +2 on the way in (client→server), -2 on the way out (server→client). The `Runner` command sets up the level's goal state and scope.

## Custom RPC Methods

Two custom methods defined in `server/GameServer/RpcHandlers.lean`:

```lean
@[server_rpc_method]
def Game.getInteractiveGoals (p : Lsp.PlainGoalParams) :
    RequestM (RequestTask (Option Widget.InteractiveGoals)) :=
  FileWorker.getInteractiveGoals p

@[server_rpc_method]
def Game.getProofState (p : GameServer.ProofStateParams) :
    RequestM (RequestTask (Option GameServer.ProofState)) :=
  GameServer.getProofState p
```

### `Game.getProofState` — The Main Custom Method

Returns:

```lean
structure ProofState where
  steps : Array InteractiveGoalsWithHints
  diagnostics : Array InteractiveDiagnostic
  completed : Bool
  completedWithWarnings : Bool
  lastPos : Nat
```

This does things standard Lean LSP can't:

- **Iterates every line** of the tactic proof collecting goals-after-each-step (powers the "typewriter" UI)
- **Matches hints**: structurally compares the player's current goal against hint trigger patterns (up to variable renaming) and substitutes the player's variable names into hint text
- **Detects completion**: reports whether the level is solved, with or without warnings
- **Checks forbidden tactics**: the `Runner` command validates each tactic against the level's inventory/difficulty settings

### Client-Side Calls

In `client/src/components/infoview/info.tsx`:

```ts
const proofReq = rpcSess.call('Game.getProofState', {
    ...DocumentPosition.toTdpp(pos),
    worldId, levelId
})
const goalsReq = rpcSess.call('Game.getInteractiveGoals', DocumentPosition.toTdpp(pos))
```

The `rpcSess` is obtained via `useRpcSessionAtPos(pos)` from the `@leanprover/infoview-api` library. The `rpcSess.call()` method sends a `$/lean/rpc/call` JSON-RPC request over the WebSocket connection.

---

# Case Study: lean4web

lean4web has a simpler version of the same pattern.

## Server Side (`server/index.mjs`)

```js
function startServerProcess(project) {
  let projectPath = path.join(projectsBasePath, project)
  if (isDevelopment) {
    return cp.spawn("lake", ["serve", "--"], { cwd: projectPath })
  } else {
    return cp.spawn("./bubblewrap.sh", [projectPath], { cwd: __dirname })
  }
}
```

When a browser connects to `/websocket/<project>`, the server spawns a Lean LSP server and forwards JSON-RPC messages bidirectionally with URI rewriting.

## Client Side (`client/src/LeanRpcSession.ts`)

The `LeanRpcSession` class manages the full lifecycle:

1. Sends `textDocument/didOpen` with the user's code
2. Waits for `$/lean/fileProgress` to report processing complete
3. Sends `$/lean/rpc/connect` to get a session
4. Calls `Lean.Widget.getInteractiveDiagnostics` via `$/lean/rpc/call`:

```ts
return await this.connection.sendRequest('$/lean/rpc/call', {
  textDocument: { uri: this.uri },
  position: { line: 0, character: 0 },
  sessionId: this.sessionId,
  method: 'Lean.Widget.getInteractiveDiagnostics',
  params: { textDocument: { uri: this.uri } },
});
```

5. Extracts goal information from the diagnostic tree
6. Maintains a keepalive timer (every 10s)

---

# Case Study: ProofWidgets4

ProofWidgets is the canonical example of rich custom RPC, building interactive widgets that render in the Lean infoview.

## `@[server_rpc_method]` Definitions in ProofWidgets

| Method | Purpose |
|--------|---------|
| `ppExprTagged` | Pretty-print an expression with interactive tags |
| `goalsLocationsToExprs` | Convert goal locations to expressions |
| `getExprPresentations` | Get alternative presentations for an expression |
| `updateSvg` | Interactive SVG state update loop |
| `cancelRequest` / `checkRequest` | Cancellable RPC protocol |
| Various demo widgets (`VennDisplay.rpc`, `EuclideanDisplay.rpc`, etc.) | Domain-specific visualizations |

## The `mk_rpc_widget%` Bridge

Converts a `@[server_rpc_method]` that returns `Html` into a renderable widget component:

```lean
@[server_rpc_method]
def MyComponent.rpc (ps : MyProps) : RequestM (RequestTask Html) := ...

@[widget_module]
def MyComponent : Component MyProps :=
  mk_rpc_widget% MyComponent.rpc
```

This generates a JS wrapper that, when rendered in the browser, calls the named RPC method, receives `Html` back, and renders it.

## The `Html` Type

```lean
inductive Html where
  | element : String → Array (String × Json) → Array Html → Html
  | text : String → Html
  | component : UInt64 → String → LazyEncodable Json → Array Html → Html
```

A Lean `@[server_rpc_method]` computes an `Html` tree server-side. This tree is RPC-encoded as JSON and sent to the browser for rendering.

## The Widget Flow

1. Lean code registers JS via `@[widget_module]` (stored by content hash)
2. `Widget.savePanelWidgetInfo` stores the hash + encoded props at a source location
3. The infoview discovers `UserWidgetInstance` at the cursor position
4. `importWidgetModule(rs, pos, hash)` fetches the JS source from the server via RPC
5. The JS is dynamically imported and its `default` export is rendered as a React component

## Panel Widgets

Panel widgets appear in the infoview alongside the goal state:

```lean
structure PanelWidgetProps : Type where
  pos : Lsp.Position
  goals : Array Widget.InteractiveGoal
  termGoal? : Option Widget.InteractiveTermGoal
  selectedLocations : Array SubExpr.GoalsLocation
```

Registered using `with_panel_widgets [MyWidget]` in tactic blocks.

## Interactive SVG: A Stateful RPC Pattern

`InteractiveSvg` shows a rich pattern where the JS widget maintains local state (time, selection, mouse position) and repeatedly calls the `updateSvg` RPC method. The server runs the update/render cycle and returns new `Html` and updated state, enabling interactive stateful visualizations at ~33ms callback intervals.

## Cancellable RPC

ProofWidgets adds `@[server_rpc_method_cancellable]` — a userspace protocol on top of core RPC. Long-running methods return a `RequestId` immediately. The client polls with `checkRequest` and can cancel with `cancelRequest`.

---

# Summary: Building Your Own

To get custom information from Lean to a web app:

1. **Define Lean structures** for your params and result, `deriving RpcEncodable`
2. **Write a `@[server_rpc_method]`** function that computes what you need (you have full access to `Environment`, `MetaM`, `TacticM`, etc.)
3. **On the client**, connect via WebSocket → LSP initialize → `$/lean/rpc/connect` → `$/lean/rpc/call` with your method name
4. The **position** you pass determines which snapshot (and therefore which definitions) are in scope
5. For rich interactive widgets, use ProofWidgets' `mk_rpc_widget%` pattern to bridge Lean-computed `Html` to React components
