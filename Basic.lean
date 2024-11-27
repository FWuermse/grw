import Lean.Elab.Term

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

-/
