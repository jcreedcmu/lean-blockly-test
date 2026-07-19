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
  | intro (suggestedName : String)
  | specialize
  deriving Inhabited

open Lean Server Widget Elab in
instance : ToJson Affordance where
  toJson
    | .apply        => Json.mkObj [("kind", Json.str "apply")]
    | .rewrite      => Json.mkObj [("kind", Json.str "rewrite")]
    | .choose name  => Json.mkObj [("kind", Json.str "choose"),
                                   ("suggestedName", Json.str name)]
    | .use          => Json.mkObj [("kind", Json.str "use")]
    | .intro name   => Json.mkObj [("kind", Json.str "intro"),
                                   ("suggestedName", Json.str name)]
    | .specialize   => Json.mkObj [("kind", Json.str "specialize")]

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
    | "intro"   => do
        let name ← j.getObjValAs? String "suggestedName"
        pure (.intro name)
    | "specialize"  => pure .specialize
    | k             => throw s!"unknown affordance kind: {k}"

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
/-- The binder name of a top-level `∀` (i.e. `.forallE`), falling back
    to `"x"` if `e` isn't a `forallE`. -/
def forallBinderName? (e : Expr) : String :=
  match e with
  | .forallE name _ _ _ => name.toString
  | _                   => "x"

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
            if hypType.isForall then
              affordances := affordances.push .specialize
          hyps := hyps.push {
            fvarId := toString decl.fvarId.name
            isAssumption
            affordances
          }
        let target ← instantiateMVars mvarDecl.type
        let mut targetAffordances : Array Affordance := #[]
        if target.isAppOf ``Exists then
          targetAffordances := targetAffordances.push .use
        if target.isForall then
          targetAffordances := targetAffordances.push (.intro (forallBinderName? target))
        return {
          mvarId := p.mvarId
          hyps
          target := { affordances := targetAffordances }
        }

/-
  Conv navigation for goal subexpressions, served via the `getConvTargets`
  RPC. Given the goal's `mvarId` and a list of subexpression positions (the
  slash-encoded `SubExpr.Pos` strings the client already holds from the
  goal's `CodeWithInfos`), we return, for the subset that are valid `conv`
  targets, the `enter [...]` arguments that zoom `conv` onto them.

  The association is intentionally PARTIAL: positions that `conv` can't reach
  (implicit arguments, application heads, binder domains) are omitted, and the
  client simply offers no conv block for those subexpressions.

  `solveLevel` — the one-step `SubExpr.Pos` → `enter` translation — is copied
  from Mathlib's `conv?` widget (`Mathlib/Tactic/Widget/Conv.lean`, Apache-2.0,
  authors Robin Böhne, Wojciech Nawrocki, Patrick Massot). It handles the
  subtleties that make a naive client-side implementation wrong: counting
  explicit vs. implicit application arguments for 1-based `enter` indices, and
  emitting binder names for `∀`/`λ`.
-/

open Lean Server Widget Elab Meta in
private structure SolveReturn where
  expr : Expr
  val? : Option String
  listRest : List Nat

open Lean Server Widget Elab Meta in
private def solveLevel (expr : Expr) (path : List Nat) : MetaM SolveReturn := match expr with
  | Expr.app _ _ => do
    let mut descExp := expr
    let mut count := 0
    let mut explicitList := []
    -- walk the application spine, recording explicit/implicit for each arg
    while descExp.isApp do
      if (← Lean.Meta.inferType descExp.appFn!).bindingInfo!.isExplicit then
        explicitList := true::explicitList
        count := count + 1
      else
        explicitList := false::explicitList
      descExp := descExp.appFn!
    -- the `enter` index is the count of explicit args, minus those skipped
    let mut mutablePath := path
    let mut length := count
    explicitList := List.reverse explicitList
    while !mutablePath.isEmpty && mutablePath.head! == 0 do
      if explicitList.head! == true then
        count := count - 1
      explicitList := explicitList.tail!
      mutablePath := mutablePath.tail!
    let mut nextExp := expr
    while length > count do
      nextExp := nextExp.appFn!
      length := length - 1
    nextExp := nextExp.appArg!
    let pathRest := if mutablePath.isEmpty then [] else mutablePath.tail!
    return { expr := nextExp, val? := toString count, listRest := pathRest }
  | Expr.lam n _ b _ => do
    let name := match n with
      | Name.str _ s => s
      | _ => panic! "no name found"
    return { expr := b, val? := name, listRest := path.tail! }
  | Expr.forallE n _ b _ => do
    let name := match n with
      | Name.str _ s => s
      | _ => panic! "no name found"
    return { expr := b, val? := name, listRest := path.tail! }
  | Expr.mdata _ b => do
    match b with
      | Expr.mdata _ _ => return { expr := b, val? := none, listRest := path }
      | _ => return { expr := b.appFn!.appArg!, val? := none, listRest := path.tail!.tail! }
  | _ => do
    return {
      expr := ← (Lean.Core.viewSubexpr path.head! expr)
      val? := toString (path.head! + 1)
      listRest := path.tail!
    }

open Lean Server Widget Elab Meta in
/-- The `conv => enter [...]` arguments navigating to `pos` within `goalType`,
    or `none` if `pos` isn't a valid `conv` target. -/
private def convArgsForPos (goalType : Expr) (pos : SubExpr.Pos) :
    MetaM (Option (Array String)) := do
  let mut list := (SubExpr.Pos.toArray pos).toList
  let mut expr := goalType
  let mut retList : List String := []
  while !list.isEmpty do
    let res ← solveLevel expr list
    expr := res.expr
    retList := match res.val? with
      | none => retList
      | some val => val :: retList
    list := res.listRest
  let args := retList.reverse
  -- `enter` is 1-based: a "0" means navigation landed on a non-conv-target
  -- (implicit arg / application head). The empty path is the goal root.
  if args.isEmpty || args.contains "0" then
    return none
  return some args.toArray

open Lean Server Widget Elab in
structure ConvTarget where
  /-- The subexpression position, echoing the client's `subexprPos` string. -/
  pos : String
  /-- The `enter [...]` arguments (explicit-arg indices and/or binder names). -/
  enter : Array String
  deriving FromJson, ToJson

open Lean Server Widget Elab in
structure ConvTargets where
  mvarId : String
  targets : Array ConvTarget
  deriving FromJson, ToJson

open Lean Server Widget Elab in
structure ConvTargetParams where
  ctx : WithRpcRef ContextInfo
  mvarId : String
  /-- Subexpression positions to evaluate, as slash-encoded `SubExpr.Pos`
      strings (exactly the `subexprPos` values the client already holds). -/
  positions : Array String
  deriving RpcEncodable

open Lean Server Widget Elab Meta in
@[server_rpc_method]
def getConvTargets (p : ConvTargetParams) :
    RequestM (RequestTask ConvTargets) :=
  RequestM.pureTask do
    let ci := p.ctx.val
    ci.runMetaM {} do
      let mvarId := MVarId.mk (parseLeanName p.mvarId)
      let mctx ← getMCtx
      let some mvarDecl := mctx.findDecl? mvarId
        | return { mvarId := p.mvarId, targets := #[] }
      withLCtx mvarDecl.lctx mvarDecl.localInstances do
        let goalType ← instantiateMVars mvarDecl.type
        let mut targets : Array ConvTarget := #[]
        for posStr in p.positions do
          match SubExpr.Pos.fromString? posStr with
          | .ok pos =>
            let res ← (try convArgsForPos goalType pos catch _ => pure none)
            match res with
            | some enter => targets := targets.push { pos := posStr, enter }
            | none => pure ()
          | .error _ => pure ()
        return { mvarId := p.mvarId, targets }

/-
  Unit tests for the conv-path generation. Each `#eval` runs `convArgsForPos`
  on a closed example goal at a hand-written `SubExpr.Pos` and prints the
  resulting `enter` args; `#guard_msgs` pins the expected output. These run at
  preamble *build* time only (importing the olean does not re-run them).

  NOTE: the expected `info:` values were written by hand. If a build reports a
  `#guard_msgs` mismatch, its message shows the actual output to paste in.
-/
section ConvPathTests
open Lean Qq Meta

private def egArith : Q(Prop) := q((2 : Nat) + 3 = 5)
private def egForall : Q(Prop) := q(∀ n : Nat, n = n)

-- `(2 + 3 = 5)` is `@Eq Nat (2 + 3) 5`; positions index the binary `Expr` tree.

/-- info: some #["1"] -/        -- lhs `2 + 3` (first explicit arg of `Eq`)
#guard_msgs in #eval convArgsForPos egArith (.fromString! "/0/1")

/-- info: some #["2"] -/        -- rhs `5` (second explicit arg of `Eq`)
#guard_msgs in #eval convArgsForPos egArith (.fromString! "/1")

/-- info: some #["1", "1"] -/   -- the `2` (first explicit arg of `+`, inside lhs)
#guard_msgs in #eval convArgsForPos egArith (.fromString! "/0/1/0/1")

/-- info: some #["1", "2"] -/   -- the `3` (second explicit arg of `+`)
#guard_msgs in #eval convArgsForPos egArith (.fromString! "/0/1/1")

/-- info: none -/               -- the goal root has no `enter`, so no conv target
#guard_msgs in #eval convArgsForPos egArith (.fromString! "/")

/-- info: some #["n"] -/        -- body of `∀ n, n = n` (enter the binder by name)
#guard_msgs in #eval convArgsForPos egForall (.fromString! "/1")

/- A realistic goal with a deeply-nested target subexpression. Rather than
   hand-write the `SubExpr.Pos` of `x ^ 3` (impractical at this depth), we
   locate it by its pretty-printed form and check the conv path. -/

/-- Position of the first subexpression of `e` whose pretty-printed form
    (spaces removed) equals `needle`, descending only where `conv` can reach
    (app fn/arg, binder bodies) — matching `convArgsForPos`. -/
private partial def findSubexprPos (needle : String) (e : Expr)
    (pos : SubExpr.Pos := .root) : MetaM (Option SubExpr.Pos) := do
  let isMatch ← (try return (← ppExpr e).pretty.replace " " "" == needle
                 catch _ => return false)
  if isMatch then return some pos
  match e with
  | .app f a =>
    match ← findSubexprPos needle f pos.pushAppFn with
    | some r => return some r
    | none   => findSubexprPos needle a pos.pushAppArg
  | .lam _ _ b _     => findSubexprPos needle b pos.pushBindingBody
  | .forallE _ _ b _ => findSubexprPos needle b pos.pushBindingBody
  | .mdata _ b       => findSubexprPos needle b pos
  | _ => return none

/-- The goal `∃ c, (x+y)^4 = …`, with `x y : ℝ` introduced as local
    variables so the target has the same shape the player sees. -/
private def withExpansionGoal (k : Expr → MetaM (Option (Array String))) :
    MetaM (Option (Array String)) := do
  let p : Q(Prop) := q(∀ x y : ℝ, ∃ c : ℝ,
    (x + y) ^ 4 = x ^ 4 + 4 * x ^ 3 * y + c * x ^ 2 * y ^ 2 + 4 * x * y ^ 3 + y ^ 4)
  forallTelescope p fun _ body => k body

private def convForSubterm (needle : String) : MetaM (Option (Array String)) :=
  withExpansionGoal fun body => do
    match ← findSubexprPos needle body with
    | some pos => convArgsForPos body pos
    | none     => return none

-- NOTE: the two expected values below are predicted by hand; confirm/adjust
-- against the build's `#guard_msgs` report on first run.

/-- info: some #["1", "c", "1"] -/   -- `(x + y) ^ 4`, the lhs of the equation
#guard_msgs in #eval convForSubterm "(x+y)^4"

/-- info: some #["1", "c", "2", "1", "1", "1", "2", "1", "2"] -/   -- the `x ^ 3`
#guard_msgs in #eval convForSubterm "x^3"

end ConvPathTests

/-!
Hard-coded parity helpers for the standalone NAS presentation level.

These live in the compiled preamble so theorem-expression blocks in the
browser can refer to them without re-elaborating their proofs on every edit.
-/

open Classical

theorem sum_card_fibers_eq_card_relation
    {α : Type}
    (s : Finset α)
    (R : α → α → Prop) :
    (∑ x ∈ s, {y ∈ s | R x y}.card) =
      ((s ×ˢ s).filter fun p => R p.1 p.2).card := by
  classical
  calc
    _ = ∑ x ∈ s, ∑ y ∈ s, if R x y then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ p ∈ s ×ˢ s, if R p.1 p.2 then 1 else 0 := by
      rw [Finset.sum_product]
    _ = _ := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem even_card_symmetric_irreflexive_relation
    {α : Type}
    (s : Finset α)
    (R : α → α → Prop)
    (hsymm : ∀ x y, R x y → R y x)
    (hirref : ∀ x, ¬ R x x) :
    Even ((s ×ˢ s).filter fun p => R p.1 p.2).card := by
  classical
  rw [← sum_card_fibers_eq_card_relation s R]
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      let n := {y ∈ s | R a y}.card
      have hrow : {y ∈ insert a s | R a y}.card = n := by
        rw [Finset.filter_insert]
        simp [n, hirref]
      have hcol (x : α) (hx : x ∈ s) :
          {y ∈ insert a s | R x y}.card =
            {y ∈ s | R x y}.card + if R x a then 1 else 0 := by
        rw [Finset.filter_insert]
        by_cases h : R x a <;> simp [ha, h]
      have hindicator :
          ∑ x ∈ s, (if R x a then 1 else 0) = n := by
        rw [← Finset.card_filter]
        congr 1
        ext x
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hx, hxa⟩
          exact ⟨hx, hsymm x a hxa⟩
        · rintro ⟨hx, hax⟩
          exact ⟨hx, hsymm a x hax⟩
      have hsumcol :
          (∑ x ∈ s, {y ∈ insert a s | R x y}.card) =
            ∑ x ∈ s, ({y ∈ s | R x y}.card + if R x a then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hcol x hx
      rw [Finset.sum_insert ha, hrow, hsumcol, Finset.sum_add_distrib, hindicator]
      have hn : Even (2 * n) := by simp
      simpa [n, two_mul, add_assoc, add_comm, add_left_comm] using ih.add hn

theorem sum_eq_sum_even_add_sum_odd
    {α : Type}
    (s : Finset α)
    (f : α → ℕ) :
    (∑ x ∈ s, f x) =
      (∑ x ∈ s.filter fun x => Even (f x), f x) +
      (∑ x ∈ s.filter fun x => Odd (f x), f x) := by
  rw [← Finset.sum_filter_add_sum_filter_not s (fun x => Even (f x))]
  congr 2
  ext x
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro hx
  exact Nat.not_even_iff_odd

theorem even_sum_even_terms
    {α : Type}
    (s : Finset α)
    (f : α → ℕ) :
    Even (∑ x ∈ s.filter fun x => Even (f x), f x) := by
  apply Finset.even_sum
  simp

theorem even_right_of_even_add
    {a b : ℕ}
    (hab : Even (a + b))
    (ha : Even a) :
    Even b :=
  (Nat.even_add.mp hab).mp ha

theorem odd_sum_of_odd_terms_of_odd_card
    {α : Type}
    (s : Finset α)
    (f : α → ℕ)
    (hall : ∀ x ∈ s, Odd (f x))
    (hcard : Odd s.card) :
    Odd (∑ x ∈ s, f x) := by
  rw [Finset.odd_sum_iff_odd_card_odd]
  have hfilter : s.filter (fun x => Odd (f x)) = s :=
    Finset.filter_eq_self.mpr hall
  rwa [hfilter]
