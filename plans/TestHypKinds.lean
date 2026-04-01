/-
  This file tests the Lean code that goes into the preamble in App.tsx.
  Run with: lake env lean TestHypKinds.lean
-/
import Lean

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

-- Test the core isProp logic via a tactic (doesn't test RPC, but tests the logic)
open Lean Elab Tactic Meta in
elab "test_hyp_kinds" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let lctx ← getLCtx
    for decl in lctx do
      if decl.isAuxDecl then continue
      let typeOfType ← inferType decl.type
      let kind := if typeOfType.isProp then "assumption" else "object"
      logInfo m!"{decl.userName} : {← ppExpr decl.type} [{kind}]"

-- Test parseLeanName
#eval do
  let n := parseLeanName "_uniq.5128"
  IO.println s!"parsed: {n}"
  IO.println s!"components: {n.components}"

example (x : Nat) (h : x > 0) (f : Nat → Nat) (heq : f x = 3) : x ≥ 1 := by
  test_hyp_kinds
  omega
