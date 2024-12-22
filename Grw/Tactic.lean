/-
# Tactic

## Arguments
- Theorem p : ∀Φ, rα t u        e.g. grw [p]
- Constraints Ψ : Set (?ₓ : Γ ⊢ Τ)  e.g. {hr : r x y, hr' : r y z}

## Algorithm

## Tips from Jannis:
synth instance finds type class instances
forall telescopes to move BVars to FVars
isdefeq = unify
withoutModifyingState at top level to restore state
stay in MetaM for core functionality, TacticM entrypoint
-/

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
Note from paper:
The unification function for a
given lemma ρ is denoted unify_ρ(Γ, Ψ, τ ). It takes as input a typing environment,
a constraint set and a term and tries to unify the left-hand side of the lemma’s
applied relation with the term. It uses the same unification algorithm as the one
used when applying a lemma during a proof.

get lhs of ρ (match for app)
change all vars in Phi to mvars (forallMetaTelescope)
isdefeq auf term t
check which of the newly generated mvars are assigned
(isAssignedOrDelayedAssigned)
(<- instanciateMvar $ Expr.mvar ?x1 == Expr.mvar ?x1)
the ones not assigned -> constraint set

side note:
unification in t can contain more mvars which could get assigned:
  + if a rule fails
  + look up (commitIfSuccess)
-/

abbrev RWM := ReaderT Expr MetaM

private def srep : Nat → String
  | n => n.fold (fun _ s => s ++ "  ") ""

def unify (Ψ : List MVarId) (t : Expr) : RWM <| List MVarId × Expr × Expr × Expr × Bool := do
  let ρ ← read
  match ← inferType ρ with
  | .app (.app r lhs) rhs =>
    let unifyable ← isDefEq lhs t -- Extends the local context
    pure (Ψ, r, ρ, rhs, unifyable)
  | .forallE _ _ (.app (.app r lhs) rhs) _ =>
    let (exprs, _, e) ← forallMetaTelescope lhs
    let unifyable ← isDefEq e t -- Extends the local context
    let mut Ψ := Ψ
    for expr in exprs do
      -- Precondition e is forall
      -- Invariant expr is a mvar
      let mvarId := expr.mvarId!
      let reassigned ← mvarId.isAssignedOrDelayedAssigned
      if !reassigned then
        Ψ := Ψ.insert mvarId
    pure (Ψ, r, ρ, rhs, unifyable)
  | _ => throwError "{ρ} is not a relation"

/--
Note from paper:
The variant unify∗ ρ(Γ, Ψ, τ ) tries unification on all subterms and succeeds if at least one
unification does. The function unify(Γ, Ψ, t, u) does a standard unification of t and u.
-/
def unifyStar (Ψ : List MVarId) (t : Expr) : RWM <| List MVarId × Expr × Expr × Expr × Bool := do
  let ρ ← read
  match ← inferType ρ with
  | .app (.app r lhs) rhs => do
    let b ← IO.mkRef false
    forEachExpr t fun t' => do
      b.set <| (← isDefEq lhs t') || (← b.get)
    pure (Ψ, r, ρ, rhs, ← b.get)
  | .forallE _ _ (.app (.app r lhs) rhs) _ => do
    let (exprs, _, t) ← forallMetaTelescope lhs
    let b ← IO.mkRef false
    forEachExpr t fun t' => do
      b.set <| (← isDefEq lhs t') || (← b.get)
    let mut Ψ := Ψ
    for expr in exprs do
      -- Precondition e is forall
      -- Invariant expr is a mvar
      let mvarId := expr.mvarId!
      let reassigned ← mvarId.isAssignedOrDelayedAssigned
      if !reassigned then
        Ψ := Ψ.insert mvarId
    pure (Ψ, r, ρ, rhs, ← b.get)
  | _ => throwError "{ρ} is not a relation"

def atom (Ψ : List MVarId) (t : Expr) : RWM <| List MVarId × Expr × Expr × Expr := do
  let ρ ← read
  /-
  preconditions:
    - No other rule can be applied
    - Unify* failed
  -/
  let (Ψ', u, R, p, b) ← unifyStar Ψ t ρ
  if b then
    return (Ψ', R, u, p)
  let T ← inferType t
  let S ← mkFreshExprMVar <| ← mkAppM ``relation #[T]
  let m ← mkFreshExprMVar <| ← mkAppM ``Proper #[S, t]
  -- TODO confirm below line
  let p ← mkAppOptM ``Proper.proper #[none, none, none, m]
  -- paper says include S.mvardId! But it seems counterintuitive to guess the relation aswell
  return (Ψ ∪ [m.mvarId!], S, t, p)

private def getRelType (rel : Expr) : Expr :=
  if let .app _ b := rel then
    b
  else
    rel

/--
`rew` always succeeds and returns a tuple (Ψ, R, τ', p) with the output constraints, a relation R, a new term τ' and a proof p : R τ τ'. In case no rewrite happens we can just have an application of ATOM.

This output tuple represents the proof sekelton that is used in the proof search.
-/
partial def rew (Ψ : List MVarId) (t : Expr) (depth : Nat) : RWM (List MVarId × Expr × Expr × Expr) := do
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"{srep <| depth}rew Ψ ({t}) ρ") do
  let ρ ← read
  /-
  invariants:
    - ρ is of type Relation
  -/
  let (Ψ', r, p', u, unifyable) ← unify Ψ t ρ
  if unifyable then
    trace[Meta.Tactic.grewrite] "{srep depth} |UNIFY⇓ {t} ↝ {u}"
    return (Ψ', r, u, p')
  trace[Meta.Tactic.grewrite] "{srep depth} |Unify⇑ {t}"
  match t with
  | .app f e => do
    trace[Meta.Tactic.grewrite] "{srep depth} |APPSUB ({f}) ({e})"
    let (Ψ, F, f', pf) ← rew Ψ f (depth+1) ρ
    let (Ψ, E, e', pe) ← rew Ψ e (depth+1) ρ
    /-
    preconditions:
      - t is an application f e
      - when e is of type τ then f must be of τ → σ
      - rewrite on f happened
      - rewrite on e happened
    -/
    let Tf ← whnf <| ← inferType f
    if let .some (_τ, σ) := Tf.arrow? then
      -- precondition: type(Γ, Ψ, f)↑ ≡ τ → σ
      let rel ← mkFreshExprMVar <| ← mkAppM ``relation #[σ]
      let sub ← mkFreshExprMVar <| ← mkAppM ``Subrel #[F, ← mkAppM ``respectful #[E, rel]]
      -- TODO is Subrel.subrelation correct here? -> Yes seems like the paper means Subrel.subrelation implicitly as it's the only constructor.
      let p ← mkAppOptM ``Subrel.subrelation #[none, none, none, sub, f, f', pf, e, e', pe]
      -- paper says include S.mvardId! But it seems counterintuitive to guess the relation aswell
      pure (Ψ ∪ [sub.mvarId!], rel, .app f' e', p)
    else
      atom Ψ t
  | .lam n T b i => do
    trace[Meta.Tactic.grewrite] "{srep depth} |LAM {t}"
    lambdaTelescope t (fun xs b => do
      let (Ψ, S, b, p) ← rew Ψ b (depth+1) ρ
      /-
      preconditions:
        - t is a lambda abstraction λ x.b
        - rewrite on b happened
      -/
      let S := mkApp3 (mkConst ``pointwiseRelation [0]) T (getRelType (← inferType S)) S
      let p := .lam n T p i
      pure (Ψ, S, .lam n T b i, p))
  | .forallE n T b i => do
    trace[Meta.Tactic.grewrite] "{srep depth} |PI {t}"
    let (Ψ', r, p', u, unifyable) ← unifyStar Ψ T
    if unifyable then
      pure (Ψ', r, u, p')
    else
      let (Ψ, S, b, p) ← rew Ψ (mkApp (mkConst ``all) <| .lam n T b i) (depth+1)
      /-
      preconditions:
        - unify* on T failed
        - rewrite on b as arrow with `all` happened
      -/
      if let .app _c (.lam n T b i) := b then
        pure (Ψ, S, .forallE n T b i, p)
      else
        throwError "Rewrite of `all λ x ↦ y` resulted in a different (thus wrong) type."
  | _ => match t.arrow? with
  | .some (α, β) =>
    trace[Meta.Tactic.grewrite] "{srep depth} |Arrow {t}"
    let (Ψ, S, b, p) ← rew Ψ (mkApp2 (mkConst ``impl) α β) (depth+1)
    if let .app (.app _c α) β := b then
      pure (Ψ, S, ← mkArrow α β, p)
    else
      throwError "Rewrite of `Impl α β` resulted in a different (thus wrong) type."
  | .none => do
    trace[Meta.Tactic.grewrite] "{srep depth} |ATOM {t}"
    atom Ψ t

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
          try
            let _ ← goal.assumption
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

def algorithm (ps : Syntax.TSepArray `ident ",") : TacticM Unit := withMainContext do
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"algorithm") do
  let lctx ← getLCtx
  -- Confirm all passed lemmas are in the local context
  let mut ldecls : List LocalDecl := []
  for ps' in lctx do
    for p in ps.getElems do
      let name := p.getId
      if name == ps'.userName then
        ldecls := ldecls ++ [ps']
      else
        continue
  for ldecl in ldecls do
    let goal ← getMainGoal
    let ρ := ldecl.toExpr
    let goalType ← goal.getType
    let Ψ := []
    let (Ψ, R, u, p) ← rew Ψ goalType 0 ρ
    -- Final rw for goal is subrel flip impl (see: https://coq.zulipchat.com/#narrow/channel/237977-Coq-users/topic/.E2.9C.94.20Generalized.20rewriting.20-.20proof.20skeleton.20generation)
    let finalGoal ← mkAppM ``Subrel #[R, ← mkAppM ``flip #[mkConst ``impl]]
    let m ← mkFreshExprMVar finalGoal
    let p ← mkAppOptM ``Subrel.subrelation #[none, none, none, m, none, none, p]
    let Ψ := Ψ.insert m.mvarId!
    eautoSearch Ψ p

elab "grewrite" "[" ps:ident,+ "]" : tactic =>
  algorithm ps

end Tactic
