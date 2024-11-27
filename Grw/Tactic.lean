/-
# Tactic

## Arguments
- Theorem p : ∀Φ, rα t u        e.g. grw [p]
- Constraints Ψ : Set (?ₓ : Γ ⊢ Τ)  e.g. {hr : r x y, hr' : r y z}

## Term Differenciation
- Unify: Term unifies directly with the lemma
- App:

## Algorithm

1. Find unifyable subterm in lhs or rhs of the lemma
2. Generate a proof that rw is correct
  1. Proof skeleton and constraints/existential vars
  2. If constraints solved using type class instances obtain closed terms
  3. Substitute closed terms in skeleton
  4.

# Quersions
- When is Proper more helpful than Reflexive?
- What does the "proof skeleton" look like?
- What is Atom and why do we differenciate between arrow, app, lambda?

synth instance finds type class instances
forall telescopes
isdefeq = unify
without modifying state
stay in MetaM for core functionality, TacticM entrypoint
-/

import Lean.Elab.Tactic
import Grw.Morphism
import Batteries

open Lean
open Lean.Meta
open Lean.Elab.Tactic

/--
Note from paper:
The unification function for a
given lemma ρ is denoted unify_ρ(Γ, ψ, τ ). It takes as input a typing environment,
a constraint set and a term and tries to unify the left-hand side of the lemma’s
applied relation with the term. It uses the same unification algorithm as the one
used when applying a lemma during a proof.
-/
def unify (p : Expr) (Ψ : List MVarId) (t : Expr) : MetaM (Bool × List MVarId) := do
  let unifyable ← isDefEq p <| t
  -- TODO: When does Ψ change here?
  pure (unifyable, Ψ)

/--
Note from paper:
The variant unify∗ ρ(Γ, ψ, τ ) tries unification on all subterms and succeeds if at least one
unification does. The function unify(Γ, ψ, t, u) does a standard unification of t and u.
-/
def unify_star (p : Expr) (Ψ : List MVarId) (t : Expr) : MetaM (Bool × List MVarId) := do
  let unifyable ← t.foldlM (fun b e => do
    if e.hasLooseBVars then
      -- TODO: difference between loose bound vars and locally bound vars? Reference from paper: As we go under abstractions, we must also extend a context Γ for the locally-bound variables.
      return false
    else
      return (← isDefEq e p) || b) false
  -- TODO: When does Ψ change here?
  pure (unifyable, Ψ)

def mkRel (T : Expr) :=
  mkArrowN #[T, T] <| .sort .zero

def atom (Ψ : List MVarId) (t : Expr) : MetaM <| List MVarId × Expr := do
  /-
  preconditions:
    - No other rule can be applied
    - Unify failed
  -/
  let T ← inferType t
  let rel ← mkFreshExprMVar <| ← mkRel T
  let prp ← mkFreshExprMVar <| mkApp3 (mkConst ``Proper) T rel t
  return (Ψ ∪ [rel.mvarId!, prp.mvarId!], rel)

/--
The rewrite function always performs a rewrite on the term. If unification succeeds the result will be a rewrite from `t` to `u` given a relation `r t u`. If unification fails `t` will be rewritten to `t` and the constraint set `Ψ` is extended.
-/
def envrw (p : Expr) (Ψ : List MVarId) (t : Expr) : MetaM <| List MVarId × Expr := do
  let (succeeded, Ψ') ← unify p Ψ t
  if succeeded then
    return (Ψ', p)
  else
    atom Ψ t
  -- postcondition: result Expr is a relation

def appSub (Ψ : List MVarId) (p : Expr) (t : Expr) : MetaM <| List MVarId × Expr := do
  /-
  preconditions:
    - t is an application f e
    - when e is of type τ then f must be of τ → σ
    - rewrite on f happened
    - rewrite on e happened
  -/
  let (f, e) ← match t with
  | .app f e => pure (f, e)
  | _ => throwError "Term t must be an application but is: {t}"
  let Tf ← inferType <| ← whnf f
  let (_τ, σ) ← match Tf.arrow? with
  | .some (τ, σ)  => pure (τ, σ)
  | .none => throwError "Type of f in f e must be of the form σ → τ"
  -- precondition: type(Γ, Ψ, f)↑ ≡ τ → σ
  let (Ψ', E) ← envrw p Ψ f
  let (Ψ'', F) ← envrw p Ψ' e
  let rel ← mkFreshExprMVar <| ← mkRel σ
  let sub ← mkFreshExprMVar <| mkApp2 (mkConst ``Subrel) F <| mkApp2 (mkConst ``respectful) E rel
  let Ψ''' := [sub.mvarId!, rel.mvarId!]
  pure (Ψ'' ∪ Ψ''', sub)

def lambda (Ψ : List MVarId) (p : Expr) (t : Expr) : MetaM <| List MVarId × Expr := do
  /-
  preconditions:
    - t is a lambda abstraction λ x.b
    - rewrite on b happened
  -/
  let (body, T) ← match t with
  | .lam _n T b _i => pure (b, T)
  | _ => throwError "The lambda rule only accepts lambda abstractions."
  let (ψ', S) ← envrw p Ψ body
  let S' := mkApp2 (mkConst ``pointwiseRelation) T S
  -- TODO: My interpretation seems fishy. What am I missing?
  pure (ψ', S')

def pi (Ψ : List MVarId) (p : Expr) (t : Expr) : MetaM <| List MVarId × Expr := do
  /-
  preconditions:
    - unify on t failed
    - t is a dep. prod. type
  -/
  let (succeeded, _) ← unify p Ψ t
  sorry--??

def arrow (Ψ : List MVarId) (p : Expr) (t : Expr) : MetaM <| List MVarId × Expr := do
  sorry--??

/--
`rew` always succeeds and returns a tuple (ψ, R, τ', p) with the output constraints, a relation R, a new term τ' and a proof p : R τ τ'. In case no rewrite happens we can just have an application of ATOM.

This output tuple represents the proof sekelton that is used in the proof search.
-/
def rew (p : Expr) (t : Expr) : MetaM (List MVarId × Expr × Expr × Expr) := do
    let Ψ := []
    logInfo m!"{Ψ}"
    pure (Ψ, sorry, sorry, sorry)

def proofSearch (constraints : List MVarId) : MetaM Unit := do
  sorry

def algorithm (ps : Syntax.TSepArray `ident ",") : TacticM Unit := withMainContext do
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
  let _ ← rew sorry sorry
  proofSearch sorry
  sorry

elab "myrw" "[" ps:ident,+ "]" : tactic =>
  algorithm ps

example : ∀ {α : Type} {r : α → α → Prop} {x y z : α}, [Transitive r] → r x y → r y z → r x z := by
  intro a r x y z t h h₀
  sorry
  --myrw [h]
  --assumption
