import Grw.Tactic
import Grw.Morphism

open Morphism

-- Examples
set_option trace.Meta.Tactic.grewrite true

example : ∀ {α : Type} {r : α → α → Prop} {x y z : α}, [Transitive r] → r x y → r y z → r x z := by
  intro a r x y z t h h₀
  grewrite [h]

  assumption

variable (α β γ: Type)
variable (Rα: relation α) (Rβ: relation β) (Rγ: relation γ)
variable (Pα: α → Prop) (Pβ: β → Prop) (Pγ: γ → Prop)
variable (Pαβγ: α → β → Prop)
variable (fαβ: α → β) (fβγ: β → γ)
variable [Proper_fαβ: Proper (Rα ⟹ Rβ) fαβ]
variable [Proper_Pα: Proper (Rα ⟹ Iff) Pα]

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
