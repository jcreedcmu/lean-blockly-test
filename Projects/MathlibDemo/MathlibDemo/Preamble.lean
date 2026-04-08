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

open Lean Server Widget Elab in
structure HypIsAssumption where
  fvarId : String
  isAssumption : Bool
  deriving FromJson, ToJson

open Lean Server Widget Elab in
structure GoalHypKinds where
  mvarId : String
  hyps : Array HypIsAssumption
  deriving FromJson, ToJson

open Lean Server Widget Elab in
structure HypKindResult where
  goals : Array GoalHypKinds
  deriving FromJson, ToJson

open Lean Server Widget Elab in
structure HypKindParams where
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
def getHypKinds (p : HypKindParams) :
    RequestM (RequestTask HypKindResult) :=
  RequestM.pureTask do
    let ci := p.ctx.val
    ci.runMetaM {} do
      let mvarId := MVarId.mk (parseLeanName p.mvarId)
      let mctx ← getMCtx
      let some mvarDecl := mctx.findDecl? mvarId
        | return { goals := #[] }
      withLCtx mvarDecl.lctx mvarDecl.localInstances do
        let mut hyps : Array HypIsAssumption := #[]
        for decl in ← getLCtx do
          if decl.isAuxDecl then continue
          let typeOfType ← inferType decl.type
          hyps := hyps.push {
            fvarId := toString decl.fvarId.name
            isAssumption := typeOfType.isProp
          }
        return { goals := #[{ mvarId := p.mvarId, hyps }] }
