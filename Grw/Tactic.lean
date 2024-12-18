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
open Morphism
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

structure RWCtx where
-- Rewrite is of the form p = r t u
  term : Expr
  h : Expr
  r : Expr
  t : Expr
  u : Expr

abbrev RWM := ReaderT RWCtx MetaM

def unify (Ψ : List MVarId) (t : Expr) : RWM <| List MVarId × Expr × Expr × Expr × Bool := do
  let ρ ← read
  match ρ.term with
  | .app (.app r lhs) rhs =>
    let unifyable ← isDefEq lhs t -- Extends the local context
    pure (Ψ, r, ρ.h, rhs, unifyable)
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
    pure (Ψ, r, ρ.h, rhs, unifyable)
  | _ => throwError "{ρ.term} is not a relation"

/--
Note from paper:
The variant unify∗ ρ(Γ, Ψ, τ ) tries unification on all subterms and succeeds if at least one
unification does. The function unify(Γ, Ψ, t, u) does a standard unification of t and u.
-/
def unifyStar (Ψ : List MVarId) (t : Expr) : RWM <| List MVarId × Expr × Expr × Expr × Bool := do
  let ρ ← read
  match ρ.term with
  | .app (.app r lhs) rhs => do
    let b ← IO.mkRef false
    forEachExpr t fun t' => do
      b.set <| (← isDefEq lhs t') || (← b.get)
    pure (Ψ, r, ρ.h, rhs, ← b.get)
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
    pure (Ψ, r, ρ.h, rhs, ← b.get)
  | _ => throwError "{ρ.term} is not a relation"

def atom (Ψ : List MVarId) (t : Expr) : RWM <| List MVarId × Expr × Expr × Expr := do
  /-
  preconditions:
    - No other rule can be applied
    - Unify* failed
  -/
  let (Ψ', t', R, p', b) ← unifyStar Ψ t
  if b then
    return (Ψ', R, t', p')
  let T ← inferType t
  let rel ← mkFreshExprMVar <| ← mkAppM ``relation #[T]
  let prp ← mkFreshExprMVar <| ← mkAppM ``Proper #[rel, t]
  let p ← mkAppOptM ``Proper.proper #[none, none, none, prp]
  return (Ψ ∪ [rel.mvarId!, prp.mvarId!], rel, t, p)

/--
`rew` always succeeds and returns a tuple (Ψ, R, τ', p) with the output constraints, a relation R, a new term τ' and a proof p : R τ τ'. In case no rewrite happens we can just have an application of ATOM.

This output tuple represents the proof sekelton that is used in the proof search.
-/
partial def rew (Ψ : List MVarId) (t : Expr) : RWM (List MVarId × Expr × Expr × Expr) := do
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"rew Ψ ({t}) ρ") do
  /-
  invariants:
    - p is of type Relation
  -/
  let (Ψ', r, p', u, unifyable) ← unify Ψ t
  if unifyable then
    trace[Meta.Tactic.grewrite] "UNIFY⇓ {t} ↝ {u}"
    return (Ψ', r, u, p')
  trace[Meta.Tactic.grewrite] "Unify⇑ {t}"
  match t with
  | .app f e => do
    trace[Meta.Tactic.grewrite] "APPSUB ({f}) ({e})"
    let (Ψ, F, f', pf) ← rew Ψ f
    let (Ψ, E, e', pe) ← rew Ψ e
    /-
    preconditions:
      - t is an application f e
      - when e is of type τ then f must be of τ → σ
      - rewrite on f happened
      - rewrite on e happened
    -/
    let Tf ← whnf <| ← inferType f
    let (_τ, σ) ← match Tf.arrow? with
    | .some (τ, σ) => pure (τ, σ)
    | .none => throwError "Type of f in f e must be of the form σ → τ but is {Tf}"
    -- precondition: type(Γ, Ψ, f)↑ ≡ τ → σ
    let rel ← mkFreshExprMVar <| ← mkAppM ``relation #[σ]
    let sub ← mkFreshExprMVar <| ← mkAppM ``Subrel #[F, ← mkAppM ``respectful #[E, rel]]
    -- TODO is Subrel.subrelation correct here?
    let p ← mkAppOptM ``Subrel.subrelation #[none, none, none, sub, f, f', pf, e, e', pe]
    pure (Ψ ∪ [sub.mvarId!, rel.mvarId!], rel, .app f' e', p)
  | .lam n T b i => do
    trace[Meta.Tactic.grewrite] "LAM {t}"
    let (Ψ, S, b, p) ← rew Ψ b
    /-
    preconditions:
      - t is a lambda abstraction λ x.b
      - rewrite on b happened
    -/
    let S := mkApp2 (mkConst ``pointwiseRelation) T S
    -- TODO p must be replaced with λ x : T p
    pure (Ψ, S, .lam n T b i, p)
  | .forallE n T b i => do
    trace[Meta.Tactic.grewrite] "PI {t}"
    let (Ψ', r, p', u, unifyable) ← unifyStar Ψ T
    if unifyable then
      pure (Ψ', r, u, p')
    else
      let (Ψ, S, b, p) ← rew Ψ (mkApp (mkConst ``all) <| .lam n T b i)
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
    trace[Meta.Tactic.grewrite] "Arrow {t}"
    let (Ψ, S, b, p) ← rew Ψ (mkApp2 (mkConst ``impl) α β)
    if let .app (.app _c α) β := b then
      pure (Ψ, S, ← mkArrow α β, p)
    else
      throwError "Rewrite of `Impl α β` resulted in a different (thus wrong) type."
  | .none => do
    trace[Meta.Tactic.grewrite] "ATOM {t}"
    atom Ψ t

  -- iterate over constraits and call synthInstance
def proofSearchGoal (Ψ : List MVarId) (R : Expr) (u : Expr) (p : Expr) : TacticM Unit := do
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"proofSearch") do
  let rewrite ← mkAppM ``Subrel #[R, ← mkAppM ``flip #[(mkConst ``impl)]]
  let sub ← mkFreshExprMVar rewrite
  let p := mkApp2 (mkConst ``Subrel.subrelation [0]) sub p
  let Ψ := Ψ.insert sub.mvarId!
  trace[Meta.Tactic.grewrite] "{Ψ}"
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
    let h := ldecl.toExpr
    let term ← inferType h
    let goalType ← goal.getType
    let Ψ := []
    let ρ : RWState ← match term with
    | .app (.app r t) u => do pure ⟨term, h, r, t, u⟩
    | .forallE _ _ (.app (.app r t) u) _ => do pure ⟨term, h, r, t, u⟩
    | _ => throwError "{term} is not a relation"
    let (Ψ, R, u, p) ← rew Ψ goalType ρ
    proofSearchGoal Ψ R u p

elab "grewrite" "[" ps:ident,+ "]" : tactic =>
  algorithm ps

end Tactic

set_option trace.Meta.Tactic.grewrite true
set_option trace.Meta.Tactic.eauto true
set_option trace.Meta.Tactic.eauto.hints true

example : ∀ {α : Sort u} {r : relation α} {x y z : α}, [Transitive r] → r x y → r y z → r x z := by
  intro a r x y z t h h₀
  --grewrite [h]
  sorry

variable (α β γ: Type)
variable (Rα: relation α) (Rβ: relation β) (Rγ: relation γ)
variable (Pα: α → Prop) (Pβ: β → Prop) (Pγ: γ → Prop)
variable (Pαβγ: α → β → Prop)
variable (fαβ: α → β) (fβγ: β → γ)
variable [Proper_fαβ: Proper (Rα ⟹ Rβ) fαβ]
variable [Proper_Pα: Proper (Rα ⟹ Iff) Pα]

example (h: Rα a a') (finish: Pα a') : Pα a := by
  grewrite [h]
  exact finish

example (h: Rα a a') : Rα a x := by
  grewrite [h]
  sorry

example (h: Rα a a') (finish: Pα a') : Pα a := by
  grewrite [h]
  assumption

-- Rewrite a PER within itself
example (h: Rα a a') (finish: Rα a' x) : Rα a x := by
  grewrite [h]
  assumption
example (h: Rα a a') (finish: Rα x a') : Rα x a := by
  grewrite [h]
  assumption

example (h: Rα a a') (finish: Rβ (fαβ a') x): Rβ (fαβ a) x := by
  grewrite [h]
  assumption

example (h: Rα a a') (finish: Rα a' a'): Rα a a := by
  grewrite [h]
  assumption
