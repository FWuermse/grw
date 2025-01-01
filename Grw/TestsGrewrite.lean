import Grw.Tactic
import Grw.Eauto

section Examples

set_option trace.Meta.Tactic.grewrite true
set_option trace.Meta.Tactic.eauto true
set_option trace.Meta.Tactic.eauto.hints true

-- ATOM
example {r : relation Prop} [Subrel r (flip impl)] : r a b → b → a := by
  intro rab hb
  grewrite [rab]
  exact hb

-- Simple app
example {r : relation α} {P : α → Prop} [Proper (r ⟹ Iff) P] : r a a' → P a' → P a := by
  intros h finish
  grewrite [h]
  exact finish

-- RW under respectful f
example {f : α → α} [Proper (r ⟹ r) f] [Proper (r ⟹ Iff) P] : r a a' → P (f a') → P (f a) := by
  intro h finish
  grewrite [h]
  exact finish

-- RW under lambda
example {a : α} {P : (α → α) → Prop} [Proper (pointwiseRelation α r ⟹ Iff) P] : r a a' → P (λ _ => a') → P (λ _ => a) := by
  intro h finish
  grewrite [h]
  exact finish

-- Transitive RW in equiv
example {r : α → α → Prop} [Equiv r] : r a b → r b c → r a c := by
  intro rab rbc
  grewrite [rab]
  exact rbc

-- Examples from Sébastien Michelland

variable (α β γ: Type)
variable (Rα: relation α) (Rβ: relation β) (Rγ: relation γ)
variable (Pα: α → Prop) (Pβ: β → Prop) (Pγ: γ → Prop)
variable (Pαβγ: α → β → Prop)
variable (fαβ: α → β) (fβγ: β → γ)
variable [Proper_fαβ: Proper (Rα ⟹ Rβ) fαβ]
variable [Proper_Pα: Proper (Rα ⟹ Iff) Pα]
variable [PER Rα] [PER Rβ]

-- Smallest example
example (h: Rα a a') (finish: Pα a') : Pα a := by
  grewrite [h]
  exact finish

-- Rewrite a PER within itself
example (h: Rα a a') (finish: Rα a' x) : Rα a x := by
  grewrite [h]
  exact finish
example (h: Rα a a') (finish: Rα x a') : Rα x a := by
  grewrite [h]
  exact finish

-- Nested function call
example (h: Rα a a') (finish: Rβ (fαβ a') x): Rβ (fαβ a) x := by
  grewrite [h]
  exact finish

-- Multiple occurrences
example (h: Rα a a') (finish: Rα a' a'): Rα a a := by
  grewrite [h]
  exact finish

-- More complex selection
example (h: Rα a a') (finish: Pα a'): Pα a ∧ Pα a ∧ Pα a ∧ Pα a ∧ Pα a ∧ Pα a := by
  sorry

-- Examples from the Paper
variable {SET : Type}
variable {eqset : relation SET}
def trueRelation (α : Type) : relation α := fun _ _ => True
variable {eqsetEquiv : Equiv eqset}
variable {empty : SET}
variable {union : SET → SET → SET}
variable {unionEmpty : ∀ s, eqset (union s empty) s}
variable {unionIdem : ∀ s, eqset (union s s) s}
variable {unionCompat : ∀ s s', eqset s s' → ∀ t t', eqset t t' → eqset (union s t) (union s' t')}

@[grw]
instance unionProper : Proper (eqset ⟹ eqset ⟹ eqset) union := ⟨unionCompat⟩

-- Not ideal :P
set_option maxHeartbeats 500000

example : ∀ s, eqset (union (union s empty) s) s := by
  intro s
  grewrite [unionEmpty]
  grewrite [unionIdem]
  apply Reflexive.rfl

end Examples
