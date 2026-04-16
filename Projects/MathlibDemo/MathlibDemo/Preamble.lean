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
  the client via the `getGoalInfo` RPC. The client uses this for two
  things today:

  * **Hypothesis classification** — `hyps` carries, per fvarId, whether
    the hypothesis is an *assumption* (its type is a `Prop`) or an
    *object* (its type is a `Type`/`Sort`). This drives the split
    between the "Objects" and "Assumptions" sections of the infoview
    and decides which drag affordances (`apply`, `rewrite`) appear.

  * **Target syntax classification** — `target` holds syntactic
    features of the goal's target type (currently just `isExists`).
    This is a principled check on the elaborated `Expr`, not a
    pretty-printer-surface heuristic, and it drives affordances that
    depend on what the goal "shapes up as" (e.g. the `use` drag
    affordance for existentials).

  Extend `TargetInfo` (and the client-side `GoalInfo` mirror) when new
  goal-shape classifiers are needed; extending the record leaves
  existing consumers unaffected.
-/
open Lean Server Widget Elab in
structure HypIsAssumption where
  fvarId : String
  isAssumption : Bool
  deriving FromJson, ToJson

open Lean Server Widget Elab in
structure TargetInfo where
  isExists : Bool
  deriving FromJson, ToJson

open Lean Server Widget Elab in
structure GoalInfo where
  mvarId : String
  hyps : Array HypIsAssumption
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
        | return { mvarId := p.mvarId, hyps := #[], target := { isExists := false } }
      withLCtx mvarDecl.lctx mvarDecl.localInstances do
        let mut hyps : Array HypIsAssumption := #[]
        for decl in ← getLCtx do
          if decl.isAuxDecl then continue
          let typeOfType ← inferType decl.type
          hyps := hyps.push {
            fvarId := toString decl.fvarId.name
            isAssumption := typeOfType.isProp
          }
        let target ← instantiateMVars mvarDecl.type
        return {
          mvarId := p.mvarId
          hyps
          target := { isExists := target.isAppOf ``Exists }
        }
