import Grw.Tactic
import Grw.Attribute

set_option trace.Meta.Tactic.grewrite true

def setEq {α : Type} : List α → List α → Prop :=
  fun l1 l2 => ∀ x, x ∈ l1 <-> x ∈ l2

instance setEqEquivalence {α : Type} : Equivalence (@setEq α) where
  refl := fun l1 x => Iff.rfl  -- Reflexivity: l1 ≈ l1
  symm := by  -- Symmetry: If l1 ≈ l2, then l2 ≈ l1
    intro x y hxy
    unfold setEq
    intro a
    apply Iff.symm
    exact hxy a
  trans := by
    intro x y z hxy hyz
    unfold setEq at *
    intro a
    apply Iff.intro
    intro hx
    rw [hxy a] at hx
    rw [hyz a] at hx
    assumption
    intro hy
    rw [← hyz a] at hy
    rw [← hxy a] at hy
    assumption

def addElem {α : Type} (x : α) (l : List α) : List α :=
  x :: l

@[grw]
theorem addElemProper {α : Type} (x : α) : @Proper (List α → List α) (setEq ⟹ setEq) (addElem x) := by
  constructor
  unfold respectful
  intro l1 l2 heq x
  simp [addElem]
  constructor
  · intro hx
    cases hx with
    | inl => left; assumption
    | inr h' =>
      right; exact (heq x).mp h'
  · intro hx
    cases hx with
    | inl => left; assumption
    | inr h' => right; exact (heq x).mpr h'

theorem rewriteExample : setEq [1,2,3] [3,2,1] → setEq (addElem 4 [1,2,3]) (addElem 4 [3,2,1]) := by
  intro h
  grewrite [h]
  unfold setEq
  simp
  repeat sorry
