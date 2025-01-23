import Lean.Elab.Tactic
import Grw.Morphism
import Grw.Eauto
import Batteries
import Aesop

open Lean
open Lean.Meta
open Lean.Elab.Tactic

set_option trace.aesop true
set_option trace.aesop.ruleSet true

namespace Tactic

/--
The result of a rewrite.

`rewCar` is the carrier relation.
`rewMVars` are constraints that result throughout the algorithm.
-/
structure RewriteResultInfo where
  rewCar : Expr
  rewFrom : Expr
  rewTo : Expr
  rewPrf : Expr
  rewMVars : List Expr
  deriving BEq

/--
The Information about the hypothesis uses in a rewrite (e.g. `h` for `grewrite [h]`).

`prf`: Proof of the term (`h` in the above rewrite).
`prf` must be of type `∀ ci,...,cj, r c1 c2` and the type of c1 and c2 is the carrier `car`. When variables are telescoped and not reassigned not during unification those locally bound vars are stored in `holes`.
-/
structure HypInfo where
  prf : Expr
  car : Expr
  rel : Expr
  sort : Bool -- Even required? Does it matter in Lean?
  c1 : Expr -- Lhs of rel
  c2 : Expr -- Rhs of rel
  holes : List MVarId

def toHypInfo (term : Expr) : MetaM HypInfo := do
  let T ← inferType term
  match T with
  | .app (.app r lhs) rhs => do
    pure ⟨term, ← inferType lhs, r, lhs.isSort, lhs, rhs, []⟩
  | .forallE _ _ (.app (.app _ _) _) _ => do
    let (exprs, _, .app (.app r lhs) rhs) ← forallMetaTelescope T | throwError "MetaTelescope broke structure of rw lemma"
    let exprs := exprs.map fun e => e.mvarId!
    pure ⟨term, ← inferType lhs, r, lhs.isSort, lhs, rhs, exprs.toList⟩
  | _ => throwError "The given rewrite hypothesis {term} must be of the form ∀ Φs, R αs t u."

/--
`fail` not clear right now
`id` is when we don't rewrite because no subterm can't be unified (ATOM or binary APP).
`success` successful subterm rewrite.
-/
inductive RewriteResult where
  | fail
  | id
  | success (r : RewriteResultInfo)

abbrev RWM := ReaderT HypInfo MetaM <| List MVarId × RewriteResult

private def srep : Nat → String
  | n => n.fold (fun _ s => s ++ "  ") ""

def unify (Ψ : List MVarId) (t : Expr) (l2r : Bool) : RWM := do
  let ρ ← read
  let lhs := if l2r then ρ.c1 else ρ.c2
  let rhs := if l2r then ρ.c2 else ρ.c1
  -- Take all initial holes and add collect the ones not reassigned to make them subgoals for the user to solve.
  if ← isDefEq lhs t then
    let subgoals ← ρ.holes.filterM fun mv => do pure !(← mv.isAssignedOrDelayedAssigned)
    pure (Ψ, RewriteResult.success ⟨ρ.rel, t, rhs, ρ.prf, subgoals.map mkMVar⟩)
  else
    pure (Ψ, .id)

/--
Note from paper:
The variant unify∗ ρ(Γ, Ψ, τ ) tries unification on all subterms and succeeds if at least one
unification does. The function unify(Γ, Ψ, t, u) does a standard unification of t and u.
-/
def unifyStar (Ψ : List MVarId) (t : Expr) (l2r : Bool) : RWM := do
  let ρ ← read
  let lhs := if l2r then ρ.c1 else ρ.c2
  let rhs := if l2r then ρ.c2 else ρ.c1
  let b ← IO.mkRef false
  forEachExpr t fun t' => do
    b.set <| (← isDefEq lhs t') || (← b.get)
  if ← b.get then
    let subgoals ← ρ.holes.filterM fun mv => do pure !(← mv.isAssignedOrDelayedAssigned)
    pure (Ψ, RewriteResult.success ⟨ρ.rel, t, rhs, ρ.prf, subgoals.map mkMVar⟩)
  else
    pure (Ψ, .id)

def atom (Ψ : List MVarId) (t : Expr) (r2l : Bool) : RWM := do
  -- TODO probably a duplicate check.
  if let (Ψ, .success res) ← unifyStar Ψ t r2l then
    return (Ψ, .success res)
  let T ← inferType t
  let S ← mkFreshExprMVar <| ← mkAppM ``relation #[T]
  let m ← mkFreshExprMVar <| ← mkAppM ``Proper #[S, t]
  -- TODO confirm below line
  let p ← mkAppOptM ``Proper.proper #[none, none, none, m]
  -- paper says include S.mvardId! But those will implicitly reappear when setting new goals
  let u := t
  logInfo m!"{t} ↝ {u}, Proof: {p}, Relation: {S}"
  return (Ψ ∪ [m.mvarId!], .success ⟨S, t, t, p, []⟩)

private def getRelType (rel : Expr) : Expr :=
  if let .app _ b := rel then
    b
  else
    rel

def arrowCount (curr : Nat) : Expr → Nat
  | .forallE n T b i => arrowCount (curr + 1) b
  | _ => curr

def respectfulN (mvars : List Expr) : MetaM  Expr :=
  match mvars with
  | x :: [] => pure x
  | x :: xs => do mkAppM ``respectful #[x, ← respectfulN xs]
  | _ => throwError "Cannot create empty respectful chain."


/--
`rew` always succeeds and returns a tuple (Ψ, R, τ', p) with the output constraints, a relation R, a new term τ' and a proof p : R τ τ'. In case no rewrite happens we can just have an application of ATOM.

This output tuple represents the proof sekelton that is used in the proof search.
-/
partial def rew (Ψ : List MVarId) (t : Expr) (desiredRel : Option Expr) (l2r : Bool) (depth : Nat) : RWM := do
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"{srep <| depth}rew Ψ ({t}) ρ") do
  let ρ ← read
  if let (Ψ', .success res) ← unify Ψ t l2r ρ then
    trace[Meta.Tactic.grewrite] "{srep depth} |UNIFY⇓ {res.rewFrom} ↝ {res.rewTo}"
    return (Ψ', .success res)
  match t with
  | .app f e => do
    let Tf ← whnf <| ← inferType f
    if let .some (τ, σ) := Tf.arrow? then
      trace[Meta.Tactic.grewrite] "{srep depth} |APPSUB ({f}) ({e})"
      let (Ψ, fRes) ← rew Ψ f none l2r (depth+1) ρ
      let (Ψ, eRes) ← rew Ψ e none l2r (depth+1) ρ
      match (fRes, eRes) with
      | (.id, .id) =>
        pure (Ψ, .id)
      | (.success fInfo, .success eInfo) =>
        -- Expensive case if both sides of the app can be rewritten (usually unfolded non binary apps).
        let r := f.getAppFn
        -- the next four lines just determine the ==> ... ==> chain when we skipped id rws.
        let mvars := fInfo.rewMVars ∪ eInfo.rewMVars
        let args := mvars ∪ desiredRel.toList
        let args := if args.length < arrowCount 1 (← inferType r) then [ρ.rel] ∪ args else args
        let respectful ← respectfulN <| args ∪ desiredRel.toList
        let prp ← mkFreshExprMVar <| ← mkAppM ``Proper #[respectful, r]
        let p ← mkAppOptM ``Proper.proper #[none, none, none, prp]
        let u := .app fInfo.rewTo eInfo.rewTo
        let Ψ := Ψ ∪ [prp.mvarId!]
        pure (Ψ, .success ⟨prp, t, u, p, fInfo.rewMVars ∪ eInfo.rewMVars⟩)
      | (.id, .success eInfo) =>
        -- When only the rhs succeeds with a rewrite we defer the generated constraints and avoid unneccessary nesting.
        let rel ← match desiredRel with
        | .some rel => pure rel
        | .none => do pure <| ← mkFreshExprMVar <| ← mkAppM ``relation #[σ]
        let lhs := if eInfo.rewMVars.isEmpty then ρ.rel else eInfo.rewMVars.get! 0
        let prp ← mkFreshExprMVar <| ← mkAppM ``Proper #[← mkAppM ``respectful #[lhs, rel], f]
        let p ← mkAppOptM ``Proper.proper #[none, none, f, prp]
        let u := .app f eInfo.rewTo
        -- When we're in the middle of an appN we want to wait with creating the constraints until on top (collecting relation holes as we go to later build ==> ... ==> with them).
        if arrowCount 0 (← inferType f) < 2 then
          let Ψ := Ψ ∪ [prp.mvarId!]
          return (Ψ, .success ⟨rel, t, u, p, eInfo.rewMVars ∪ [rel]⟩)
        else
          -- At this point our holes are taken care of and we just skip until there is something to do
          pure (Ψ, .success ⟨rel, t, u, p, eInfo.rewMVars⟩)
      | (.success fInfo, .id) => do
        -- When only the lhs succeeds we follow the same approach but use a proxy.
        let rel ← match desiredRel with
        | .some rel => pure rel
        | .none => do pure <| ← mkFreshExprMVar <| ← mkAppM ``relation #[σ]
        let lhs := if fInfo.rewMVars.isEmpty then ρ.rel else fInfo.rewMVars.get! 0
        let r := f.getAppFn
        let mvar ← mkFreshExprMVar <| ← mkAppM ``relation #[← inferType e]
        let respectful ← respectfulN [lhs, mvar, rel]
        let prp ← mkFreshExprMVar <| ← mkAppM ``Proper #[respectful, r]
        let proxy ← mkFreshExprMVar <| ← mkAppM ``ProperProxy #[mvar, e]
        let p ← mkAppOptM ``Proper.proper #[none, none, none, prp]
        let u := .app fInfo.rewTo e
        if arrowCount 0 (← inferType e) < 2 then
          let Ψ := Ψ ∪ [prp.mvarId!, proxy.mvarId!]
          return (Ψ, .success ⟨rel, t, u, p, fInfo.rewMVars ∪ [rel]⟩)
        else
          pure (Ψ, .success ⟨rel, t, u, p, fInfo.rewMVars⟩)
      | _ => return (Ψ, .fail)
    else
      atom Ψ t l2r
  | .lam n T b i => do
    trace[Meta.Tactic.grewrite] "{srep depth} |LAM {t}"
    lambdaTelescope t (fun _xs b => do
      let (Ψ, .success ⟨S, _, b, p, subgoals⟩) ← rew Ψ b none l2r (depth+1) ρ | return (Ψ, .id)
      let .app (.app _ lhs) _ := S | throwError m!"{S} in {t} must be a relation."
      let S ← mkAppM ``pointwiseRelation #[← inferType lhs, S]
      let p := .lam n T p i
      let u := .lam n T b i
      pure (Ψ, .success ⟨S, t, u, p, subgoals⟩))
  | .forallE n T b i => do
    if let .some (α, β) := t.arrow? then
      trace[Meta.Tactic.grewrite] "{srep depth} |Arrow {t}"
      let (Ψ, .success ⟨S, _, b, p, subgoals⟩) ← rew Ψ (mkApp2 (mkConst ``impl) α β) desiredRel l2r (depth+1) | pure (Ψ, .id)
      let .app (.app _ α) β := b | throwError "Rewrite of `Impl α β` resulted in a different (thus wrong) type."
      let u ← mkArrow α β
      return (Ψ, .success ⟨S, t, u, p, subgoals⟩)
    else
      trace[Meta.Tactic.grewrite] "{srep depth} |PI {t}"
      let (Ψ', res) ← unifyStar Ψ T l2r
      match res with
      | .success info => return (Ψ', .success info)
      | .id =>
        let (Ψ, .success ⟨S, _, .app _ (.lam n T b i), p, subgoals⟩) ← rew Ψ (← mkAppM ``all #[T, .lam n T b i]) none l2r (depth+1)
          | throwError "Rewrite of `all λ x ↦ y` resulted in a different (thus wrong) type."
        let u := .forallE n T b i
        pure (Ψ, .success ⟨S, t, u, p, subgoals⟩)
      | .fail => return (Ψ , .fail)
  | _ => do
    trace[Meta.Tactic.grewrite] "{srep depth} |ATOM {t}"
    --atom Ψ t l2r
    pure (Ψ, .id)

def aesopSearch (Ψ : List MVarId) (p : Expr) : TacticM Unit := do
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"proofSearch") do
  trace[Meta.Tactic.grewrite] "{Ψ}"
    let mut progress := true
    while progress do
      -- Bruteforce approach just for testing purposes.
      progress := false
      for goal in Ψ do
        try
          let rs ← Aesop.Frontend.getGlobalRuleSet `grewrite
          let options : Aesop.Options := {strategy := Aesop.Strategy.depthFirst, enableSimp := false, enableUnfold := false, useDefaultSimpSet := false}
          let rs ← Aesop.mkLocalRuleSet #[rs] (← options.toOptions')
          let _ ← Aesop.search goal (ruleSet? := .some rs) (options := options)
          progress := progress || true;
        catch _ =>
          pure ()
  let goal ← getMainGoal
  let subgoals ← goal.apply (← instantiateMVars p)
  replaceMainGoal subgoals

def eautoSearch (Ψ : List MVarId) (p : Expr) : TacticM Unit := do
  -- Try to solve the constraints with `typeclasses_eauto with grewrite`
  let success ← Eauto.eautoMain Ψ #[`grewrite] true
  if !success then
    throwError "grewrite: unable to solve constraints"

  let goal ← getMainGoal
  let subgoals ← goal.apply (← instantiateMVars p)
  replaceMainGoal subgoals

def nopSearch (Ψ : List MVarId) (p : Expr) : TacticM Unit := do
  let goal ← getMainGoal
  let subgoals ← goal.apply (← instantiateMVars p)
  replaceMainGoal subgoals

declare_syntax_cat rw
syntax ("←")? ident: rw

def algorithm (ps : Syntax.TSepArray `rw ",") : TacticM Unit := withMainContext do
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"algorithm") do
  let lctx ← getLCtx
  -- Confirm all passed lemmas are in the local context
  let mut ldecls : List (LocalDecl × Bool × TSyntax `rw) := []
  for ps' in lctx do
    for p in ps.getElems do
      let (name, l2r) ← match p with
      | `(rw|← $i:ident) => do pure (i.getId, false)
      | `(rw|$i:ident) => do pure (i.getId, true)
      | s => throwError m!"syntax {s} is invalid."
      if name == ps'.userName then
        ldecls := ldecls ++ [(ps', l2r, p)]
      else
        continue
  for (ldecl, l2r, stx) in ldecls do
    let goal ← getMainGoal
    let goalType ← goal.getType
    let Ψ := []
    let ρ ← toHypInfo ldecl.toExpr
    let (Ψ, res) ← rew Ψ goalType (← mkAppM ``flip #[mkConst ``impl]) l2r 0 ρ
    match res with
    | .id => logWarningAt stx m!"Nothing to rewrite for {ldecl.userName}."
    | .fail => logError "Rewrite failed to generate constraints."
    | .success ⟨r, _, u, p, subgoals⟩ =>
    logInfo m!"{Ψ}"
    -- Final rw for goal is subrel flip impl (see: https://coq.zulipchat.com/#narrow/channel/237977-Coq-users/topic/.E2.9C.94.20Generalized.20rewriting.20-.20proof.20skeleton.20generation)
    --let finalGoal ← mkAppM ``Subrel #[r, ← mkAppM ``flip #[mkConst ``impl]]
    --let m ← mkFreshExprMVar finalGoal
    --let p ← mkAppOptM ``Subrel.subrelation #[none, none, none, m, none, none, p]
    --let Ψ := Ψ.insert m.mvarId!


    -- It doesn't matter if Subrel or not. The final proof should be: (some goal with P) <- (some goal with Q)
    trace[Meta.Tactic.grewrite]"Starting Proof Search:"
    trace[Meta.Tactic.grewrite]"Solving {Ψ}"
    logInfo m!"{Ψ}"
    -- TODO: set subgoals
    nopSearch Ψ p

elab "grewrite" "[" ps:rw,+ "]" : tactic =>
  algorithm ps

end Tactic

/- ✓
Produces: wrt. to subrelationProper and do_subrelation:
  ?m1 : Proper (Iff ==> ?r ==> flip impl) impl
  ?m2 : ProperProxy ?r Q
-/
example : ∀ P Q : Prop, (P ↔ Q) → (P → Q) := by
  intros P Q H
  grewrite [H]
  repeat sorry

/- ✓
Produces: wrt. to subrelationProper and do_subrelation:
  ?m1 : Proper (Iff ==> flip impl) (impl Q)
-/
example : ∀ P Q : Prop, (P ↔ Q) → (Q → P) := by
  intros P Q H
  grewrite [H]
  repeat sorry

-- ✓ This is (seemingly) just different by moving the first applicant out the app into a proxy. Still sus.
/-
Produces: wrt. to subrelationProper and do_subrelation:
  ?m1 : Proper (Iff ==> ?r0 ==> ?r) impl
  ?m2 : ProperProxy ?r0 Q
  ?m2 : Proper (Iff ==> ?r ==> flip impl) And
-/
example : ∀ P Q : Prop, (P ↔ Q) → P ∧ (P → Q) := by
  intros P Q H
  grewrite [H]
  repeat sorry

/- ✓
Produces: wrt. to subrelationProper and do_subrelation:
  ?m1 : Proper (Iff ==> ?r) (impl Q)
  ?m2 : Proper (Iff ==> ?r ==> flip impl) And
-/
example : ∀ P Q : Prop, (P ↔ Q) → P ∧ (Q → P) := by
  intros P Q H
  grewrite [H]
  repeat sorry

/- ✓
Produces: wrt. to subrelationProper and do_subrelation:
  ?m1 : Proper (Iff ==> ?r) (impl Q)
  ?m2 : Proper (?r ==> flip impl) (And Q)
-/
example : ∀ P Q : Prop, (P ↔ Q) → Q ∧ (Q → P) := by
  intros P Q H
  grewrite [H]
  repeat sorry

/- ✓
Produces: wrt. to subrelationProper and do_subrelation:
  ?m2 : Proper (?r ==> ?r0 ==> ?r) impl
  ?m3 : ProperProxy ?r0 Q
  ?m1 : Proper (?r ==> flip impl) (And Q)
-/
example : ∀ P Q : Prop, (P ↔ Q) → Q ∧ (P → Q) := by
  intros P Q H
  grewrite [H]
  repeat sorry

/- ✓
Produces: wrt. to subrelationProper and do_subrelation:
  ?m1 : Proper (?r ==> ?r0 ==> flip impl) and
  ?m2 : Proper (iff ==> ?r0) (impl Q)
  ?r : Relation Prop
  ?m3 : Proper (Iff => ?r) (impl Q)
  ?r0 : Relation Prop
-/
example : ∀ P Q : Prop, (P ↔ Q) → (Q → P) ∧ (Q → P) := by
  intros P Q H
  grewrite [H]
  repeat sorry
