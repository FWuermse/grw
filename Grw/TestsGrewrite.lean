import Grw.Tactic
import Grw.Eauto

section Examples

set_option trace.Meta.Tactic.grewrite true
set_option trace.Meta.Tactic.eauto true
set_option trace.Meta.Tactic.eauto.hints true
set_option trace.Meta.Tactic.eauto.goals true
set_option trace.Meta.Tactic.eauto.instances true

-- ATOM
example {r : relation Prop} [hp : Proper (r ⟹ Iff) id] : r a b → b → a := by
  intro rab hb
  grewrite [rab]
  exact hb
  constructor
  have hp' := hp.proper
  rw [respectful] at hp'
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
-- Coq TC:
#check Proper (r ⟹ flip impl) Pα
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

example : ∀ P Q : Prop, (P ↔ Q) → (Q → P ) := by
  intros P Q H
  grewrite [H]
  . simp [impl]
  . exact (flip impl)
  . constructor
    intros
    assumption
  . exact (flip impl) ⟹ Iff
  . constructor
    intros f g h
    rw [respectful] at *
    aesop
    specialize h x x
    rw [flip, impl] at *
    aesop
  . exact impl ⟹ flip impl ⟹ Iff
  . exact Iff
  . have inner := Subrel.subrelation impl impl (Proper.mk Q Q)
    apply (Subrel.subrelation (impl Q) (impl Q) (Subrel.subrelation impl impl Proper.proper Q Q Proper.proper) P Q H)
    sorry
  . sorry
  . sorry
--Proof: Subrel.subrelation (impl Q) (impl Q) (Subrel.subrelation impl impl Proper.proper Q Q Proper.proper) P Q H

-- Examples from the Paper
inductive ex {A : Sort u} (P : A → Prop) : Prop
  | intro : ∀ x : A, P x → ex P

example {A : Sort u} {P Q : A → Sort v} [Proper (pointwiseRelation A <| iff ⟹ iff) (@ex A)] : ∀A P Q, (∀ x : A, P x ↔ Q x) → (∃x:A, ¬Q x) → (∃x:A, ¬P x) := by
  sorry

example : ∀ P Q : Prop, (P ↔ Q) → (Q → P ) ∧ (Q → P ) := by
  intros P Q H
  grewrite [H]
  simp

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

/-
Some Coq constraints for problems:
-/

-- Produces: Subrel Iff (flip impl)
example : ∀ P Q : Prop, (P ↔ Q) → Q → P := by
  intros P Q H HQ
  grewrite [H]
  exact HQ

--Produces: Proper (r ⟹ flip impl) P
example {r : relation α} {P : α → Prop} [Proper (r ⟹ Iff) P] : r a a' → P a' → P a := by
  intros h finish
  grewrite [h]
  exact finish

/-
Produces wrt. to subrelationProper and do_subrelation:
  ?m1 : Relation A
  ?m2 : Proper (r ==> ?m1) f
  ?m3 : Proper (r ==> flip impl) P
-/
example {f : α → α} [Proper (r ⟹ r) f] [Proper (r ⟹ Iff) P] : r a a' → P (f a') → P (f a) := by
  intro h finish
  grewrite [h]
  exact finish

/-
Produces: Nothing to rewrite.
-/
-- RW under lambda
example {a : α} {P : (α → α) → Prop} [Proper (pointwiseRelation α r ⟹ Iff) P] : r a a' → P (λ _ => a') → P (λ _ => a) := by
  intro h finish
  grewrite [h]
  exact finish

/-
Produces: wrt. to subrelationProper and do_subrelation:
  ?m1 : Proper (Iff ==> flip impl) (impl Q)
-/
example : ∀ P Q : Prop, (P ↔ Q) → (Q → P):= by
  intros P Q H
  grewrite [H]
  simp

/-
Produces: wrt. to subrelationProper and do_subrelation:
  ?m1 : Proper (Iff ==> flip impl) (impl Q)
-/
example : ∀ P Q : Prop, (P ↔ Q) → (Q → P) := by
  intros P Q H
  grewrite [H]
  simp

/-
Produces: wrt. to subrelationProper and do_subrelation:
  ?m1 : Proper (?r ==> ?r0 ==> flip impl) impl
  ?m2 : Proper (iff ==> ?r0) (impl Q)
  ?r : Relation Prop
  ?m3 : Proper (Iff => ?r) (impl Q)
  ?r0 : Relation Prop
-/
example : ∀ P Q : Prop, (P ↔ Q) → (Q → P) → (Q → P) := by
  intros P Q H
  grewrite [H]
  simp

/-
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
  simp

/-
Produces: wrt. to subrelationProper and do_subrelation:
  ?m1 : ProperProxy ?r0 (Q -> Q)
  ?m2 : Proper (?r ==> ?r0 ==> flip impl) And
  ?m3 : Proper (Iff ==> ?r) (impl Q)
  ?r : Relation Prop
-/
example : ∀ P Q : Prop, (P ↔ Q) → (Q → P) ∧ (Q → Q) := by
  intros P Q H
  grewrite [H]
  simp
