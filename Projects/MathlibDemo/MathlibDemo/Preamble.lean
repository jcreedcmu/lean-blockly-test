/-
Stable preamble for the Blockly Lean game.

This file is `import`ed by the in-memory `Blockly.lean` document the
client sends via LSP. Putting these definitions in a real on-disk file
inside the `MathlibDemo` lake library means they get compiled exactly
once into a `.olean`, and edits to the player's contribution no longer
re-elaborate Mathlib or this preamble on every keystroke.

Anything that varies per level (e.g. domain-specific definitions like
`FunLimAt`) stays in the in-memory prelude assembled by
`client/src/LevelEvaluator.ts`, not here.
-/
import Mathlib

/-
  Per-goal information extracted from the Lean `Expr` AST and served to
  the client via the `getGoalInfo` RPC.

  For each hypothesis we report whether it is an *assumption* (a
  `Prop`-typed hyp, e.g. `h : x = y`) or an *object* (a type-typed hyp
  like `x : ℝ`), plus a list of the drag-and-drop `Affordance`s that
  *could* apply to it. For the goal target we similarly report which
  affordances could apply.

  The RPC reports what is *potentially* available — i.e. what the Lean
  AST actually supports. The TypeScript client intersects this with the
  per-level `allowedAffordances` (keyed by affordance kind) before
  rendering.

  Affordance variants:

    hypothesis:
      .apply                 — hyp is an assumption (its type is a Prop)
      .rewrite               — hyp is an assumption whose type is top-level
                               `Eq` (i.e. `h : a = b`). `rewrite` also
                               works on `Iff` and `HEq`; broaden here
                               if/when levels need it.
      .choose suggestedName  — hyp is an assumption whose type is top-level
                               `Exists`; `suggestedName` is the binder
                               name from the existential (e.g. `c` for
                               `∃ c, f c = 2`), used as the default
                               variable name in the dragged tactic block.
    target:
      .use                   — goal's target is top-level `Exists`

  JSON wire format: `{"kind": "apply"}` / `{"kind": "choose",
  "suggestedName": "c"}` / etc. The client mirrors this as a tagged
  union. Adding a new affordance means extending the inductive and
  updating both codec instances below.
-/
open Lean Server Widget Elab in
inductive Affordance where
  | apply
  | rewrite
  | choose (suggestedName : String)
  | use
  deriving Inhabited

open Lean Server Widget Elab in
instance : ToJson Affordance where
  toJson
    | .apply        => Json.mkObj [("kind", Json.str "apply")]
    | .rewrite      => Json.mkObj [("kind", Json.str "rewrite")]
    | .choose name  => Json.mkObj [("kind", Json.str "choose"),
                                   ("suggestedName", Json.str name)]
    | .use          => Json.mkObj [("kind", Json.str "use")]

open Lean Server Widget Elab in
instance : FromJson Affordance where
  fromJson? j := do
    let kind ← j.getObjValAs? String "kind"
    match kind with
    | "apply"   => pure .apply
    | "rewrite" => pure .rewrite
    | "choose"  => do
        let name ← j.getObjValAs? String "suggestedName"
        pure (.choose name)
    | "use"     => pure .use
    | k         => throw s!"unknown affordance kind: {k}"

open Lean Server Widget Elab in
structure HypInfo where
  fvarId : String
  isAssumption : Bool
  affordances : Array Affordance
  deriving FromJson, ToJson

open Lean Server Widget Elab in
structure TargetInfo where
  affordances : Array Affordance
  deriving FromJson, ToJson

open Lean Server Widget Elab in
structure GoalInfo where
  mvarId : String
  hyps : Array HypInfo
  target : TargetInfo
  deriving FromJson, ToJson

open Lean Server Widget Elab in
structure GoalInfoParams where
  ctx : WithRpcRef ContextInfo
  mvarId : String
  deriving RpcEncodable

open Lean Server Widget Elab Meta in
def parseLeanName (s : String) : Name :=
  s.splitOn "." |>.foldl (fun acc part =>
    match part.toNat? with
    | some n => Name.mkNum acc n
    | none => Name.mkStr acc part
  ) Name.anonymous

open Lean Server Widget Elab Meta in
/-- The binder name of a top-level `Exists` application, falling back
    to `"x"` if the predicate isn't in the expected `fun x => _` form. -/
def existsBinderName? (e : Expr) : String :=
  -- `∃ x, P x` elaborates to `Exists (fun x => P x)`; the predicate is
  -- the last argument of the `Exists` application.
  match e.getAppArgs.back? with
  | some (.lam name _ _ _) => name.toString
  | _                      => "x"

open Lean Server Widget Elab Meta in
@[server_rpc_method]
def getGoalInfo (p : GoalInfoParams) :
    RequestM (RequestTask GoalInfo) :=
  RequestM.pureTask do
    let ci := p.ctx.val
    ci.runMetaM {} do
      let mvarId := MVarId.mk (parseLeanName p.mvarId)
      let mctx ← getMCtx
      let some mvarDecl := mctx.findDecl? mvarId
        | return { mvarId := p.mvarId, hyps := #[], target := { affordances := #[] } }
      withLCtx mvarDecl.lctx mvarDecl.localInstances do
        let mut hyps : Array HypInfo := #[]
        for decl in ← getLCtx do
          if decl.isAuxDecl then continue
          let hypType ← instantiateMVars decl.type
          let typeOfType ← inferType hypType
          let isAssumption := typeOfType.isProp
          let mut affordances : Array Affordance := #[]
          if isAssumption then
            affordances := affordances.push .apply
            if hypType.isAppOf ``Eq then
              affordances := affordances.push .rewrite
            if hypType.isAppOf ``Exists then
              affordances := affordances.push (.choose (existsBinderName? hypType))
          hyps := hyps.push {
            fvarId := toString decl.fvarId.name
            isAssumption
            affordances
          }
        let target ← instantiateMVars mvarDecl.type
        let mut targetAffordances : Array Affordance := #[]
        if target.isAppOf ``Exists then
          targetAffordances := targetAffordances.push .use
        return {
          mvarId := p.mvarId
          hyps
          target := { affordances := targetAffordances }
        }
