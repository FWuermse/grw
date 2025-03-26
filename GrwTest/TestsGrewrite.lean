import Grw.Tactic

section Examples

set_option trace.Meta.Tactic.grewrite true

macro "finish_impl" : tactic =>
  `(tactic| simp [impl, imp_self])

example : ∀ P Q : Prop , (P ↔ Q) → (Q → P) := by
  intro P Q h
  grewrite [h]
  finish_impl

example : ∀ P Q : Prop, (P ↔ Q) → (Q → P) ∧ (Q → P) := by
  intro P Q h
  grewrite [h]
  finish_impl

example {r : relation Prop} [hp : Subrel r (flip impl)] : r a b → b → a := by
  intro rab hb
  grewrite [rab]
  exact hb

example {r : relation α} {P : α → Prop} [Proper (r ⟹ flip impl) P] : r a a' → P a' → P a := by
  intros h finish
  grewrite [h]
  exact finish

example {f : α → α} [Proper (r ⟹ r) f] [Proper (r ⟹ flip impl) P] : r a a' → P (f a') → P (f a) := by
  intro h finish
  grewrite [h]
  exact finish

example {a : α} {P : (α → α) → Prop} [Proper (pointwiseRelation α r ⟹ flip impl) P] : r a a' → P (λ _ => a') → P (λ _ => a) := by
  intro h finish
  grewrite [h]
  exact finish

-- TODO: pi example

example {r : α → α → Prop} [Equiv r] : r a b → r b c → r a c := by
  intro rab rbc
  grewrite [rab]
  assumption
  -- TODO: missing theorems for Equiv rels in proof search
  repeat sorry

example : ∀ P Q : Prop, (P ↔ Q) → Q ∧ (Q → Q) → Q ∧ (Q → P) := by
  intros P Q H finish
  grewrite [H]
  exact finish

example : ∀ P Q : Prop, (P ↔ Q) → Q ∧ (Q → Q) → Q ∧ (P → Q) := by
  intros P Q H finish
  grewrite [H]
  exact finish

example [Subrel Iff (flip impl)] : ∀ P Q : Prop, (P ↔ Q) → Q → P := by
  intros P Q H finish
  grewrite [H]
  exact finish

example : ∀ P Q : Prop, (P ↔ Q) → (Q → Q) → (P → Q) := by
  intros P Q H finish
  grewrite [H]
  exact finish

example : ∀ P Q : Prop, (P ↔ Q) → (Q → Q) → (Q → P) := by
  intros P Q H finish
  grewrite [H]
  exact finish

example : ∀ P Q : Prop, (P ↔ Q) → Q ∧ (Q → Q) → P ∧ (P → Q) := by
  intros P Q H finish
  grewrite [H]
  exact finish

example : ∀ P Q : Prop, (P ↔ Q) → Q ∧ (Q → Q) → P ∧ (Q → P) := by
  intros P Q H finish
  grewrite [H]
  exact finish

example : ∀ P Q : Prop, (P ↔ Q) → (Q → Q) ∧ (Q → Q) → (Q → P) ∧ (Q → P) := by
  intros P Q H finish
  grewrite [H]
  exact finish

-- Examples from Sébastien Michelland
-- TODO add per theorems to proof search

variable (α β γ: Sort u)
variable (Rα: relation α) (Rβ: relation β) (Rγ: relation γ)
variable (Pα: α → Prop) (Pβ: β → Prop) (Pγ: γ → Prop)
variable (Pαβγ: α → β → Prop)
variable (fαβ: α → β) (fβγ: β → γ)
variable [Proper_fαβ: Proper (Rα ⟹ Rβ) fαβ]
variable (Proper_Pα: Proper (Rα ⟹ Iff) Pα)
variable [PER Rα] [PER Rβ]

example (h: Rα a a') (finish: Pα a') : Pα a := by
  grewrite [h]
  -- TODO add per theorems to proof search
  exact finish
  sorry

-- Rewrite a PER within itself
/- Coq constraints ✓
Proper (Rα ==> ?r ==> Basics.flip Basics.impl) Rα
ProperProxy ?r x
-/
example (h: Rα a a') (finish: Rα a' x) : Rα a x := by
  grewrite [h]
  exact finish
  repeat sorry

/- Coq constraints: ✓
Proper (Rα ==> flip impl) (Rα x)
-/
example (h: Rα a a') (finish: Rα x a') : Rα x a := by
  grewrite [h]
  exact finish
  sorry

-- Nested function call ✓
/- Coq constraints:
Proper (Rα ==> =r) fαβ
Proper (?r ==> ?r0 ==> flip impl) Rαβ
ProperProxy ?r0 x
-/
example (h: Rα a a') (finish: Rβ (fαβ a') x): Rβ (fαβ a) x := by
  grewrite [h]
  exact finish
  repeat sorry

-- Multiple occurrences ✓
/- Coq constraints:
Proper (Rα ==> Rα ==> Basics.flip Basics.impl) Rα
-/
example (h: Rα a a') (finish: Rα a' a'): Rα a a := by
  grewrite [h]
  exact finish
  sorry

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
example (h: Rα a a') (finish: Pα a' ∧ Pα a' ∧ Pα a' ∧ Pα a' ∧ Pα a' ∧ Pα a') : Pα a ∧ Pα a ∧ Pα a ∧ Pα a ∧ Pα a ∧ Pα a := by
  grewrite [h]
  exact finish

example : ∀ P Q : Prop, (P ↔ Q) → (Q → P) := by
  intros P Q H
  grewrite [H]
  finish_impl

--Proof: Subrel.subrelation (impl Q) (impl Q) (Subrel.subrelation impl impl Proper.proper Q Q Proper.proper) P Q H

-- Examples from the Paper
example : ∀ P Q : Prop, (P ↔ Q) → (Q → P) ∧ (Q → P) := by
  intros P Q H
  grewrite [H]
  simp_all
  finish_impl

variable {SET : Type}
variable {eqset : relation SET}
def trueRelation (α : Type) : relation α := fun _ _ => True
variable {eqsetEquiv : Equiv eqset}
variable {empty : SET}
variable {union : SET → SET → SET}
variable {unionEmpty : ∀ s, eqset (union s empty) s}
variable {unionIdem : ∀ s, eqset (union s s) s}
variable {unionCompat : ∀ s s', eqset s s' → ∀ t t', eqset t t' → eqset (union s t) (union s' t')}

@[grewrite]
instance unionProper : Proper (eqset ⟹ eqset ⟹ eqset) union := ⟨unionCompat⟩

example : ∀ s, eqset (union (union s empty) s) s := by
  intro s
  grewrite [unionEmpty]
  grewrite [unionIdem]
  apply Reflexive.rfl
  repeat sorry


/-
Some Coq constraints for problems:
-/

-- Produces: Subrel Iff (flip impl) ✓
example (s : Subrel Iff (flip impl)) : ∀ P Q : Prop, (P ↔ Q) → Q → P := by
  intros P Q H HQ
  grewrite [H]
  exact HQ

/- Coq constraints ✓
Proper (r ==> flip impl) (f c b)
-/
example (a b c : α) (r : relation α) (h: r a b) (f: α → α → α → Prop) (finish: f c b b) : f c b a := by
  grewrite [h]
  exact finish
  sorry

/- Coq constraints ✓
Proper (?r0 ==> ?r ==> flip impl) f
ProperProxy ?r0 b
ProperProxy ?r c
-/
example (r : relation α) (h : r a x) (f: α → β → γ → Prop) (finish : f x b c): f a b c := by
  grewrite [h]
  exact finish
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
  finish_impl

/- ✓
Produces:
  ?m0 : ProperProxy ?r Q
  ?m1 : Proper (Iff ==> ?r ==> flip impl) impl
  ?mr : relation Prop
-/
example : ∀ P Q : Prop, (P ↔ Q) → (P → Q) := by
  intros P Q H
  grewrite [H]
  finish_impl

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
  finish_impl

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
  apply And.intro <;> finish_impl

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
  apply And.intro <;> finish_impl

/- ✓
Produces
  ?m1 : Proper (?r ==> flip impl) (And (Q -> Q))
  ?m2 : Proper (Iff ==> ?r) (impl Q)
  ?r : relation Prop
-/
example : ∀ P Q : Prop, (P ↔ Q) → (Q → Q) ∧ (Q → P) := by
  intros P Q H
  grewrite [H]
  apply And.intro <;> finish_impl

-- No rewrite possible on first two proofs.
example (r₁ : relation Prop) (r₂ : relation Prop) (s : Subrel r₁ (flip impl)) (h₁ : r₁ P Q) (h₂ : r₂ P Q) (H : Prop) (h₃ : r₁ H P) (finish: P) : H := by
  -- show error only on h₁ and h₂
  grewrite [h₁, ← h₂, h₃]
  exact finish

-- Reverse rewrite with `←`
/- Coq constraints:
TBD
-/
example {r : α → α → Prop} [Equiv r] : r b a → r b c → r a c := by
  intro rab rbc
  -- TODO. make rhs and lhs abstract everywhere not just in unify.
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

/-
example (h₁ : a + e ≤ b + e) (h₂ : b < c) (h₃ : c ≤ d) : a + e ≤ d + e := by
  grewrite [h₂, h₃] at h₁
  exact h₁
-/
