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
  like `x : ℝ`), plus a list of the drag-and-drop affordances that
  *could* apply to it. For the goal target we similarly report which
  affordances could apply.

  The RPC reports what is *potentially* available — i.e. what the Lean
  AST actually supports. The TypeScript client intersects this with the
  per-level `allowedAffordances` before rendering.

  Affordance name → where it comes from:

    hypothesis:
      "apply"    — hyp is an assumption (its type is a Prop)
      "rewrite"  — hyp is an assumption whose type is top-level `Eq`
                   (i.e. `h : a = b`). `rewrite` also works on `Iff`
                   and `HEq`; broaden here if/when levels need it.
      "choose"   — hyp is an assumption whose type is top-level `Exists`
    target:
      "use"      — goal's target is top-level `Exists`

  Add a new affordance by extending the `Array String` returned here —
  no need to add or migrate fields.
-/
open Lean Server Widget Elab in
structure HypInfo where
  fvarId : String
  isAssumption : Bool
  affordances : Array String
  deriving FromJson, ToJson

open Lean Server Widget Elab in
structure TargetInfo where
  affordances : Array String
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
          let mut affordances : Array String := #[]
          if isAssumption then
            affordances := affordances.push "apply"
            if hypType.isAppOf ``Eq then
              affordances := affordances.push "rewrite"
            if hypType.isAppOf ``Exists then
              affordances := affordances.push "choose"
          hyps := hyps.push {
            fvarId := toString decl.fvarId.name
            isAssumption
            affordances
          }
        let target ← instantiateMVars mvarDecl.type
        let mut targetAffordances : Array String := #[]
        if target.isAppOf ``Exists then
          targetAffordances := targetAffordances.push "use"
        return {
          mvarId := p.mvarId
          hyps
          target := { affordances := targetAffordances }
        }
