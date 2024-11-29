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
import Batteries

open Lean
open Lean.Meta
open Lean.Elab.Tactic

def isRelation (e : Expr) : MetaM <| Expr × Expr × Expr := do
  match e with
  | .app (.app r a) b => pure (r, a, b)
  | _ => throwError "Not a relation"

/--
Note from paper:
The unification function for a
given lemma ρ is denoted unify_ρ(Γ, Ψ, τ ). It takes as input a typing environment,
a constraint set and a term and tries to unify the left-hand side of the lemma’s
applied relation with the term. It uses the same unification algorithm as the one
used when applying a lemma during a proof.
-/
def unify (Ψ : List MVarId) (t : Expr) (p : Expr) : MetaM <| List MVarId × Expr × Expr × Bool := do
  let (_, lhs, _) ← isRelation p
  let unifyable ← isDefEq lhs <| t -- Extends the local context
  /-
  TODO:
    - How to obtain updated constraints?
    - How to obtain `u` with unification from `t` to `u`?
    - How to obtain the updated lemma `p`
  -/
  pure (Ψ, p, t, unifyable)

/--
Note from paper:
The variant unify∗ ρ(Γ, Ψ, τ ) tries unification on all subterms and succeeds if at least one
unification does. The function unify(Γ, Ψ, t, u) does a standard unification of t and u.
-/
def unifyStar (Ψ : List MVarId) (t : Expr) (p : Expr) : MetaM <| List MVarId × Expr × Expr × Bool := do
  let (_, lhs, _) ← isRelation p
  let b ← IO.mkRef false
  forEachExpr t fun e => do
    b.set <| (← isDefEq lhs e) || (← b.get)
  /-
  TODO:
    - How to obtain updated constraints?
    - How to obtain `u` with unification from `t` to `u`?
    - How to obtain the updated lemma `p`
  -/
  pure (Ψ, p, t, ← b.get)

def mkRel (T : Expr) :=
  mkApp (mkConst ``Relation) T

def atom (Ψ : List MVarId) (t : Expr) (p : Expr) : MetaM <| List MVarId × Expr × Expr × Expr := do
  /-
  preconditions:
    - No other rule can be applied
    - Unify failed
  -/
  let T ← inferType t
  let rel ← mkFreshExprMVar <| mkRel T
  let prp ← mkFreshExprMVar <| mkApp3 (mkConst ``Proper) T rel t
  return (Ψ ∪ [rel.mvarId!, prp.mvarId!], rel, t, p)

/--
`rew` always succeeds and returns a tuple (Ψ, R, τ', p) with the output constraints, a relation R, a new term τ' and a proof p : R τ τ'. In case no rewrite happens we can just have an application of ATOM.

This output tuple represents the proof sekelton that is used in the proof search.
-/
partial def rew (Ψ : List MVarId) (t : Expr) (p : Expr) : MetaM (List MVarId × Expr × Expr × Expr) := do
  /-
  invariants:
    - p is of type Relation
  -/
  let (Ψ', p', _u, unifyable) ← unify Ψ t p
  if unifyable then
    logInfo "Unify⇓"
    let (R, _a, _b) ← isRelation p
    return (Ψ', R, t, p')
  logInfo "Unify⇑"
  match t with
  | .app f e => do
    logInfo m!"App {t}"
    let (Ψ, E, f, p) ← rew Ψ f p
    let (Ψ, F, e, p) ← rew Ψ e p
    /-
    preconditions:
      - t is an application f e
      - when e is of type τ then f must be of τ → σ
      - rewrite on f happened
      - rewrite on e happened
    -/
    let Tf ← inferType <| ← whnf f
    let (_τ, σ) ← match Tf.arrow? with
    | .some (τ, σ) => pure (τ, σ)
    | .none => throwError "Type of f in f e must be of the form σ → τ"
    -- precondition: type(Γ, Ψ, f)↑ ≡ τ → σ
    let rel ← mkFreshExprMVar <| mkRel σ
    let sub ← mkFreshExprMVar <| mkApp2 (mkConst ``Subrel) F <| mkApp2 (mkConst ``respectful) E rel
    pure (Ψ ∪ [sub.mvarId!, rel.mvarId!], sub, .app f e, p)
  | .lam n T b i => do
    logInfo m!"Lam {t}"
    let (Ψ, S, b, p) ← rew Ψ b p
    /-
    preconditions:
      - t is a lambda abstraction λ x.b
      - rewrite on b happened
    -/
    let S := mkApp2 (mkConst ``pointwiseRelation) T S
    pure (Ψ, S, .lam n T b i, p)
  | .forallE n T b i => do
    logInfo m!"Pi {t}"
    let (Ψ', p', u, unifyable) ← unifyStar Ψ T p
    if unifyable then
      let (R, _, _) ← isRelation p
      pure (Ψ', R, u, p')
    else
      let (Ψ, S, b, p) ← rew Ψ (mkApp (mkConst ``all) <| .lam n T b i) p
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
    logInfo m!"Arrow {t}"
    let (Ψ, S, b, p) ← rew Ψ (mkApp2 (mkConst ``Impl) α β) p
    if let .app (.app _c α) β := b then
      pure (Ψ, S, ← mkArrow α β, p)
    else
      throwError "Rewrite of `Impl α β` resulted in a different (thus wrong) type."
  | .none => do
    logInfo m!"Atom {t}"
    atom Ψ t p

def proofSearch (constraints : List MVarId) (p : Expr) : MetaM Unit := do
  sorry

def algorithm (ps : Syntax.TSepArray `ident ",") : TacticM Unit := withMainContext do
  let p ← getMainGoal
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
    let t := ldecl.type
    let p := mkMVar p
    let p := ← inferType p
    let Ψ := []
    let (Ψ, _R, _u, _p) ← rew Ψ p t
    logInfo m!"{Ψ}"

elab "myrw" "[" ps:ident,+ "]" : tactic =>
  algorithm ps

example : ∀ {α : Type} {r : α → α → Prop} {x y z : α}, [Transitive r] → r x y → r y z → r x z := by
  intro a r x y z t h h₀
  myrw [h]
  --assumption
  sorry
