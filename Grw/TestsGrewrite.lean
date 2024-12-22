import Grw.Tactic
import Grw.Eauto

section Examples

variable (α β γ: Type)
variable (Rα: relation α) (Rβ: relation β) (Rγ: relation γ)
variable (Pα: α → Prop) (Pβ: β → Prop) (Pγ: γ → Prop)
variable (Pαβγ: α → β → Prop)
variable (fαβ: α → β) (fβγ: β → γ)
variable [Proper_fαβ: Proper (Rα ⟹ Rβ) fαβ]
variable [Proper_Pα: Proper (Rα ⟹ Iff) Pα]
variable [PER Rα] [PER Rβ]

set_option trace.Meta.Tactic.grewrite true
set_option trace.Meta.Tactic.eauto true
set_option trace.Meta.Tactic.eauto.hints true

example [Proper (r ⟹ Iff) P] : r a a' → P a' → P (λ a => a) := by
  intro h finish
  grewrite [h]
  exact finish

example {f : α → α} [Proper (r ⟹ Iff) P] : r a a' → P a' → P (f a) := by
  intro h finish
  grewrite [h]
  exact finish

example {r : relation α} {P : α → Prop} [Proper (r ⟹ Iff) P] : r a a' → P a' → P a := by
  intro h finish
  grewrite [h]
  exact finish

example {r : α → α → Prop} [Equiv r] : r a b → r b c → r a c := by
  intro rab rbc
  grewrite [rab]
  exact rbc

example {r : α → α → Prop} [Equiv r] : r a b → r b b → r a a := by
  intro rab rbb
  grewrite [rab]
  exact rbb

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

-- From Paper
variable {SET : Type}
variable {eqset : relation SET}
def trueRelation (α : Type) : relation α := fun _ _ => True
variable {eqsetEquiv : Equiv eqset}
variable {empty : SET}
variable {union : SET → SET → SET}
variable {unionEmpty : ∀ s, eqset (union s empty) s}
variable {unionIdem : ∀ s, eqset (union s s) s}
variable {unionCompat : ∀ s s', eqset s s' → ∀ t t', eqset t t' → eqset (union s t) (union s' t')}

instance unionProper : Proper (eqset ⟹ eqset ⟹ eqset) union := ⟨unionCompat⟩

-- Without grewrite
example : ∀ s, eqset (union (union s empty) s ) s := by
  intro s
  grewrite [unionEmpty]


end Examples
