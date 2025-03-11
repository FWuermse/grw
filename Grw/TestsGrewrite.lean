import Grw.Tactic
import Grw.Eauto

section Examples

set_option trace.Meta.Tactic.grewrite true
set_option trace.Meta.Tactic.eauto true
set_option trace.Meta.Tactic.eauto.hints true
set_option trace.Meta.Tactic.eauto.goals true
set_option trace.Meta.Tactic.eauto.instances true

/- Coq constraints: ✓
Proper (Iff ==> flip impl) (impl Q)
-/
example : ∀ P Q : Prop, (P ↔ Q) → (Q → P) := by
  intro P Q h
  grewrite [h]
  repeat sorry

example : ∀ P Q : Prop, (P ↔ Q) → P ∧ Q := by
  intro P Q h
  grewrite [h]
  repeat sorry

/- Coq constraints: ✓
Proper (?r ==> ?r0 ==> flip impl) (And)
Proper (Iff ==> ?r0) (impl Q)
Proper (Iff ==> ?r) (impl Q)
-/
example : ∀ P Q : Prop, (P ↔ Q) → (Q → P) ∧ (Q → P) := by
  intro P Q h
  grewrite [h]
  repeat sorry

-- ATOM
/- Coq constraints: ✓
Subrel r (flip impl)
-/
example {r : relation Prop} [hp : Proper (r ⟹ Iff) id] : r a b → b → a := by
  intro rab hb
  grewrite [rab]
  repeat sorry

-- Simple app
/- Coq constraints: ✓
Proper (r ==> flip impl) P
-/
example {r : relation α} {P : α → Prop} [Proper (r ⟹ Iff) P] : r a a' → P a' → P a := by
  intros h finish
  grewrite [h]
  repeat sorry

-- RW under respectful f
/- Coq constraints: ✓
Proper (r ==> ?r) f
Proper (?r ==> flip impl) P
-/
example {f : α → α} [Proper (r ⟹ r) f] [Proper (r ⟹ Iff) P] : r a a' → P (f a') → P (f a) := by
  intro h finish
  grewrite [h]
  repeat sorry

-- RW under lambda
/- Coq constraints:
Tactic failure: Nothing to rewrite.
-/
example {a : α} {P : (α → α) → Prop} [Proper (pointwiseRelation α r ⟹ Iff) P] : r a a' → P (λ _ => a') → P (λ _ => a) := by
  intro h finish
  grewrite [h]
  repeat sorry

-- TODO: pi example

-- Transitive RW in equiv
/- Coq constraints: ✓
Proper (r ==> ?r ==> flip impl) r
ProperProxy ?r c
-/
example {r : α → α → Prop} [Equiv r] : r a b → r b c → r a c := by
  intro rab rbc
  grewrite [rab]
  repeat sorry

-- More Coq comparisons:

/- ✓
Produces:
  ?m1 : Proper (Iff ==> ?r) (impl Q)
  ?m2 : Proper (?r ==> flip impl) (And Q)
-/
example : ∀ P Q : Prop, (P ↔ Q) → Q ∧ (Q → P) := by
  intros P Q H
  grewrite [H]
  repeat sorry

example (m2 : Proper (m1 ⟹ flip impl) (And Q)) (H: P ↔ Q) (m3 : Proper (Iff ⟹ m1) (impl Q)) (hs : Subrel (flip impl) (m1)) : (P ↔ Q) → Q ∧ (Q → P) := by
  intro h
  have p := @Proper.proper (Prop → Prop) (m1 ⟹ flip impl) (And Q) m2 (impl Q P) (impl Q Q) (@Proper.proper (Prop → Prop) (Iff ⟹ m1) (impl Q) m3 P Q H)
  have s := @Subrel.subrelation _ (flip impl) m1 hs (Q ∧ impl Q P) (Q ∧ impl Q Q) p
  sorry

/- ✓
Produces:
  ?m2 : Proper (Iff ==> ?r0 ==> ?r) impl
  ?m3 : ProperProxy ?r0 Q
  ?m1 : Proper (?r ==> flip impl) (And Q)
-/
example : ∀ P Q : Prop, (P ↔ Q) → Q ∧ (P → Q) := by
  intros P Q H
  grewrite [H]
  repeat sorry

/- ✓
Produces:
  ?m1 : Proper (Iff ==> ?r ==> flip impl) impl
  ?m2 : ProperProxy ?r Q
-/
example : ∀ P Q : Prop, (P ↔ Q) → P := by
  intros P Q H
  grewrite [H]
  repeat sorry

variable (P Q : Prop)
variable (H : P <-> Q)
variable (mv : Subrel Iff (flip impl))
#check @Subrel.subrelation Prop Iff (flip impl) mv P-- Q H

/- ✓
Produces:
  ?m1 : Proper (Iff ==> ?r ==> flip impl) impl
  ?m2 : ProperProxy ?r Q
-/
example : ∀ P Q : Prop, (P ↔ Q) → (P → Q) := by
  intros P Q H
  grewrite [H]
  repeat sorry

/- ✓
Produces:
  ?m1 : Proper (Iff ==> flip impl) (impl Q)
-/
example : ∀ P Q : Prop, (P ↔ Q) → (Q → P) := by
  intros P Q H
  grewrite [H]
  repeat sorry

-- ✓ This is (seemingly) just different by moving the first applicant out the app into a proxy. Still sus.
/-
Produces:
  ?m2 : Proper (Iff ==> ?r ==> flip impl) And
  ?m1 : Proper (Iff ==> ?r0 ==> ?r) impl
  ?m2 : ProperProxy ?r0 Q
-/
example : ∀ P Q : Prop, (P ↔ Q) → P ∧ (P → Q) := by
  intros P Q H
  grewrite [H]
  repeat sorry

/- ✓
Produces:
  ?m1 : Proper (Iff ==> ?r) (impl Q)
  ?m2 : Proper (Iff ==> ?r ==> flip impl) And
-/
example : ∀ P Q : Prop, (P ↔ Q) → P ∧ (Q → P) := by
  intros P Q H
  grewrite [H]
  repeat sorry

/- ✓
Produces:
  ?m1 : Proper (?r ==> ?r0 ==> flip impl) and
  ?m2 : Proper (iff ==> ?r0) (impl Q)
  ?r : Relation Prop
  ?m3 : Proper (Iff => ?r) (impl Q)
  ?r0 : Relation Prop
-/
example : ∀ P Q : Prop, (P ↔ Q) → (Q → P) ∧ (Q → P) := by
  intros P Q H
  grewrite [H]
  repeat sorry

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
/- Coq constraints ✓
Proper (Rα ==> flip impl) Pα
-/
example (h: Rα a a') (finish: Pα a') : Pα a := by
  grewrite [h]
  repeat sorry

-- Rewrite a PER within itself
/- Coq constraints ✓
Proper (Rα ==> ?r ==> Basics.flip Basics.impl) Rα
ProperProxy ?r x
-/
example (h: Rα a a') (finish: Rα a' x) : Rα a x := by
  grewrite [h]
  repeat sorry

/- Coq constraints: ✓
Proper (Rα ==> flip impl) (Rα x)
-/
example (h: Rα a a') (finish: Rα x a') : Rα x a := by
  grewrite [h]
  repeat sorry

-- Nested function call ✓
/- Coq constraints:
Proper (Rα ==> =r) fαβ
Proper (?r ==> ?r0 ==> flip impl) Rαβ
ProperProxy ?r0 x
-/
example (h: Rα a a') (finish: Rβ (fαβ a') x): Rβ (fαβ a) x := by
  grewrite [h]
  repeat sorry

-- Multiple occurrences ✓
/- Coq constraints:
Proper (Rα ==> Rα ==> Basics.flip Basics.impl) Rα
-/
example (h: Rα a a') (finish: Rα a' a'): Rα a a := by
  grewrite [h]
  repeat sorry

-- More complex selection ✓
/- Coq constraints:
Proper (Rα ==> ?r) Pα
Proper (Rα ==> ?r0) Pα
Proper (Rα ==> ?r1) Pα
Proper (Rα ==> ?r2) Pα
Proper (Rα ==> ?r3) Pα
Proper (Rα ==> ?r4) Pα
Proper (?r3 ==> ?r4 ==> ?r5) and
Proper (?r2 ==> ?r5 ==> ?r6) and
Proper (?r1 ==> ?r6 ==> ?r7) and
Proper (?r0 ==> ?r7 ==> ?r8) and
Proper (?r ==> ?r8 ==> Basics.flip Basics.impl) and
-/
example (h: Rα a a') (finish: Pα a'): Pα a ∧ Pα a ∧ Pα a ∧ Pα a ∧ Pα a ∧ Pα a := by
  grewrite [h]
  repeat sorry

example : ∀ P Q : Prop, (P ↔ Q) → (Q → P) := by
  intros P Q H
  grewrite [H]
  repeat sorry

--Proof: Subrel.subrelation (impl Q) (impl Q) (Subrel.subrelation impl impl Proper.proper Q Q Proper.proper) P Q H

-- Examples from the Paper
example : ∀ P Q : Prop, (P ↔ Q) → (Q → P ) ∧ (Q → P ) := by
  intros P Q H
  grewrite [H]
  repeat sorry

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
  --apply Reflexive.rfl
  repeat sorry


/-
Some Coq constraints for problems:
-/

-- Produces: Subrel Iff (flip impl) ✓
example : ∀ P Q : Prop, (P ↔ Q) → Q → P := by
  intros P Q H HQ
  grewrite [H]
  repeat sorry

/- Coq constraints ✓
Proper (r ==> flip impl) (f c b)
-/
example (a b c : α) (r : relation α) (h: r a b) (f: α → α → α → Prop) : f c b a := by
  grewrite [h]
  repeat sorry

/- Coq constraints ✓
Proper (?r0 ==> ?r ==> flip impl) f
ProperProxy ?r0 b
ProperProxy ?r c
-/
example (r : relation α) (h : r a x) (f: α → β → γ → Prop) : f a b c := by
  grewrite [h]
  repeat sorry

example (r : relation α) (h : r a x) (f: α → β → γ → α → Prop) : f a b c a := by
  grewrite [h]
  repeat sorry

/- Coq constraints
Proper (r ==> ?r) g
Proper (?r ==> r ==> Basics.flip Basics.impl) (f b b)
-/
example (r : relation α) (g : α → α) (h : r a x) (f: β → β → α → α → Prop) : f b b (g a) a := by
  grewrite [h]
  repeat sorry


/- Coq instances ✓
Proper (r ==> ?r) g
Proper (r ==> ?r0 ==> ?r ==> r ==> Basics.flip Basics.impl) f
ProperProxy ?r0 b
-/
example (r : relation α) (g : α → α) (h : r a x) (f: α → β → α → α → Prop) : f a b (g a) a := by
  grewrite [h]
  repeat sorry

/- ✓
Produces
  ?m1 : Relation A
  ?m2 : Proper (r ==> ?m1) f
  ?m3 : Proper (r ==> flip impl) P
-/
example {f : α → α} [Proper (r ⟹ r) f] [Proper (r ⟹ Iff) P] : r a a' → P (f a') → P (f a) := by
  intro h finish
  grewrite [h]
  repeat sorry

/-
Produces: Nothing to rewrite.
-/
-- RW under lambda
example {a : α} {P : (α → α) → Prop} [Proper (pointwiseRelation α r ⟹ Iff) P] : r a a' → P (λ _ => a') → P (λ _ => a) := by
  intro h finish
  grewrite [h]
  repeat sorry

/- ✓
Produces:
  ?m1 : Proper (Iff ==> flip impl) (impl Q)
-/
example : ∀ P Q : Prop, (P ↔ Q) → (Q → P):= by
  intros P Q H
  grewrite [H]
  repeat sorry

/- ✓
Produces:
  ?m0 : ProperProxy ?r Q
  ?m1 : Proper (Iff ==> ?r ==> flip impl) impl
  ?mr : relation Prop
-/
example : ∀ P Q : Prop, (P ↔ Q) → (P → Q) := by
  intros P Q H
  grewrite [H]
  repeat sorry

/- ✓
Produces:
  ?m1 : Proper (?r ==> ?r0 ==> flip impl) impl
  ?m2 : Proper (iff ==> ?r0) (impl Q)
  ?r : Relation Prop
  ?m3 : Proper (Iff => ?r) (impl Q)
  ?r0 : Relation Prop
-/
example : ∀ P Q : Prop, (P ↔ Q) → (Q → P) → (Q → P) := by
  intros P Q H
  grewrite [H]
  repeat sorry

/- ✓
Produces:
  ?m1 : Proper (?r ==> ?r0 ==> flip impl) and
  ?m2 : Proper (iff ==> ?r0) (impl Q)
  ?r : Relation Prop
  ?m3 : Proper (Iff => ?r) (impl Q)
  ?r0 : Relation Prop
-/
example : ∀ P Q : Prop, (P ↔ Q) → (Q → P) ∧ (Q → P) := by
  intros P Q H
  grewrite [H]
  repeat sorry

/-
Produces
  ?m1 : ProperProxy ?r0 (Q -> Q)
  ?m2 : Proper (?r ==> ?r0 ==> flip impl) And
  ?m3 : Proper (Iff ==> ?r) (impl Q)
  ?r : Relation Prop
  ?r0 : Relation Prop
-/
example : ∀ P Q : Prop, (P ↔ Q) → (Q → P) ∧ (Q → Q) := by
  intros P Q H
  grewrite [H]
  repeat sorry

/- ✓
Produces
  ?m1 : Proper (?r ==> flip impl) (And (Q -> Q))
  ?m2 : Proper (Iff ==> ?r) (impl Q)
  ?r : relation Prop
-/
example : ∀ P Q : Prop, (P ↔ Q) → (Q → Q) ∧ (Q → P) := by
  intros P Q H
  grewrite [H]
  repeat sorry

-- No rewrite possible on first two proofs.
example (r₁ : relation Prop) (r₂ : relation Prop) (h₁ : r₁ P Q) (h₂ : r₂ P Q) (H : Prop) (h₃ : r₁ H P) : H := by
  -- show error only on h₁ and h₂
  grewrite [h₁, ← h₂, h₃]
  repeat sorry

-- Reverse rewrite with `←`
/- Coq constraints:
TBD
-/
example {r : α → α → Prop} [Equiv r] : r b a → r b c → r a c := by
  intro rab rbc
  grewrite [← rab]
  repeat sorry

end Examples

example : Subrel r (Iff ⟹ rr) := by
  constructor
  rw [Subrelation]
  intros x y hr
  rw [respectful]
  intros a b iff
  sorry
