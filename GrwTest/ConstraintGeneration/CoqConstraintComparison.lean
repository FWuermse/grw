import Grw.Tactic
import Grw.Eauto

section Examples

/- Coq constraints: ✓
Proper (Iff ==> flip impl) (impl Q)
-/
example : ∀ P Q : Prop, (P ↔ Q) → (Q → P) := by
  intro P Q h
  assert_constraints [h]
    (Proper (Iff ⟹ flip impl) (impl Q));
  sorry

/- Coq constraints: ✓
Proper (?r ==> ?r0 ==> flip impl) (And)
Proper (Iff ==> ?r0) (impl Q)
Proper (Iff ==> ?r) (impl Q)
-/
example : ∀ P Q : Prop, (P ↔ Q) → (Q → P) ∧ (Q → P) := by
  intro P Q h
  assert_constraints [h]
    (relation Prop),
    (Proper (Iff ⟹ ?r0) (impl Q)),
    (relation Prop),
    (Proper (Iff ⟹ ?r) (impl Q)),
    (Proper (?r ⟹ ?r0 ⟹ flip impl) (And));
  sorry

-- ATOM
/- Coq constraints: ✓
Subrel r (flip impl)
-/
example {r : relation Prop} [hp : Proper (r ⟹ Iff) id] : r a b → b → a := by
  intro rab hb
  assert_constraints [rab] (Subrel r (flip impl));
  sorry

-- Simple app
/- Coq constraints: ✓
Proper (r ==> flip impl) P
-/
example {r : relation α} {P : α → Prop} [Proper (r ⟹ Iff) P] : r a a' → P a' → P a := by
  intros h finish
  assert_constraints [h] (Proper (r ⟹ flip impl) P);
  sorry

-- RW under respectful f
/- Coq constraints: ✓
Proper (r ==> ?r) f
Proper (?r ==> flip impl) P
-/
example {f : α → α} [Proper (r ⟹ r) f] [Proper (r ⟹ Iff) P] : r a a' → P (f a') → P (f a) := by
  intro h finish
  assert_constraints [h]
    (relation α),
    (Proper (r ⟹ ?r) f),
    (Proper (?r ⟹ flip impl) P);
  sorry

-- RW under lambda
/- Coq constraints:
Tactic failure: Nothing to rewrite. BUT WE CAN!
-/
example {a : α} {P : (α → α) → Prop} [Proper (pointwiseRelation α r ⟹ Iff) P] : r a a' → P (λ _ => a') → P (λ _ => a) := by
  intro h finish
  assert_constraints [h]
    (Proper (pointwiseRelation α r ⟹ flip impl) P);
  sorry

-- TODO: pi example

-- Transitive RW in equiv
/- Coq constraints: ✓
Proper (r ==> ?r ==> flip impl) r
ProperProxy ?r c
-/
example {r : α → α → Prop} [Equiv r] : r a b → r b c → r a c := by
  intro rab rbc
  assert_constraints [rab]
    (ProperProxy ?r c),
    -- I omitted optional rel constraints from the coq exports. So this is expected.
    (relation α),
    (Proper (r ⟹ ?r ⟹ flip impl) r);
  sorry

-- More Coq comparisons:

/- ✓
Produces:
  ?m1 : Proper (Iff ==> ?r) (impl Q)
  ?m2 : Proper (?r ==> flip impl) (And Q)
-/
example : ∀ P Q : Prop, (P ↔ Q) → Q ∧ (Q → P) := by
  intros P Q H
  assert_constraints [H]
    (relation Prop),
    (Proper (Iff ⟹ ?r) (impl Q)),
    (Proper (?r ⟹ flip impl) (And Q));
  sorry

/- ✓
Produces:
  ?m2 : Proper (Iff ==> ?r0 ==> ?r) impl
  ?m3 : ProperProxy ?r0 Q
  ?m1 : Proper (?r ==> flip impl) (And Q)
-/
example : ∀ P Q : Prop, (P ↔ Q) → Q ∧ (P → Q) := by
  intros P Q H
  assert_constraints [H]
    (ProperProxy ?r0 Q),
    (relation Prop),
    (relation Prop),
    (Proper (Iff ⟹ ?r0 ⟹ ?r) impl),
    (Proper (?r ⟹ flip impl) (And Q));
  sorry

/- ✓
Produces:
  ?m1 : Subrel Iff (flip impl)
-/
example : ∀ P Q : Prop, (P ↔ Q) → P := by
  intros P Q H
  assert_constraints [H]
    (Subrel Iff (flip impl));
  sorry

/- ✓
Produces:
  ?m1 : Proper (Iff ==> ?r ==> flip impl) impl
  ?m2 : ProperProxy ?r Q
-/
example : ∀ P Q : Prop, (P ↔ Q) → (P → Q) := by
  intros P Q H
  assert_constraints [H]
    (ProperProxy ?r Q),
    (relation Prop),
    (Proper (Iff ⟹ ?r ⟹ flip impl) impl);
  sorry

/- ✓
Produces:
  ?m1 : Proper (Iff ==> flip impl) (impl Q)
-/
example : ∀ P Q : Prop, (P ↔ Q) → (Q → P) := by
  intros P Q H
  assert_constraints [H]
    (Proper (Iff ⟹ flip impl) (impl Q));
  sorry

-- ✓
/-
Produces:
  ?m2 : Proper (Iff ==> ?r ==> flip impl) And
  ?m1 : Proper (Iff ==> ?r0 ==> ?r) impl
  ?m2 : ProperProxy ?r0 Q
-/
example : ∀ P Q : Prop, (P ↔ Q) → P ∧ (P → Q) := by
  intros P Q H
  assert_constraints [H]
    (ProperProxy ?r0 Q),
    (relation Prop),
    (relation Prop),
    (Proper (Iff ⟹ ?r0 ⟹ ?r) impl),
    (Proper (Iff ⟹ ?r ⟹ flip impl) And);
  sorry

/- ✓
Produces:
  ?m1 : Proper (Iff ==> ?r) (impl Q)
  ?m2 : Proper (Iff ==> ?r ==> flip impl) And
-/
example : ∀ P Q : Prop, (P ↔ Q) → P ∧ (Q → P) := by
  intros P Q H
  assert_constraints [H]
    (relation Prop),
    (Proper (Iff ⟹ ?r) (impl Q)),
    (Proper (Iff ⟹ ?r ⟹ flip impl) And);
  sorry

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
  assert_constraints [H]
    (relation Prop),
    (Proper (Iff ⟹ ?r0) (impl Q)),
    (relation Prop),
    (Proper (Iff ⟹ ?r) (impl Q)),
    (Proper (?r ⟹ ?r0 ⟹ flip impl) And),
    (relation Prop),
    (relation Prop);
  sorry

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
  assert_constraints [h]
    (Proper (Rα ⟹ flip impl) Pα);
  sorry

-- Rewrite a PER within itself
/- Coq constraints ✓
Proper (Rα ==> ?r ==> Basics.flip Basics.impl) Rα
ProperProxy ?r x
-/
example (h: Rα a a') (finish: Rα a' x) : Rα a x := by
  assert_constraints [h]
    (ProperProxy ?r x),
    (relation α),
    (Proper (Rα ⟹ ?r ⟹ flip impl) Rα);
  sorry

/- Coq constraints: ✓
Proper (Rα ==> flip impl) (Rα x)
-/
example (h: Rα a a') (finish: Rα x a') : Rα x a := by
  assert_constraints [h]
    (Proper (Rα ⟹ flip impl) (Rα x));
  sorry

-- Nested function call ✓
/- Coq constraints:
Proper (Rα ==> =r) fαβ
Proper (?r ==> ?r0 ==> flip impl) Rβ
ProperProxy ?r0 x
-/
example (h: Rα a a') (finish: Rβ (fαβ a') x): Rβ (fαβ a) x := by
  assert_constraints [h]
    (relation β),
    (Proper (Rα ⟹ ?r) fαβ),
    (ProperProxy ?r0 x),
    (relation β),
    (Proper (?r ⟹ ?r0 ⟹ flip impl) Rβ);
  sorry

-- Multiple occurrences ✓
/- Coq constraints:
Proper (Rα ==> Rα ==> Basics.flip Basics.impl) Rα
-/
example (h: Rα a a') (finish: Rα a' a'): Rα a a := by
  assert_constraints [h]
    (Proper (Rα ⟹ Rα ⟹ flip impl) Rα);
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
example (h: Rα a a') (finish: Pα a'): Pα a ∧ Pα a ∧ Pα a ∧ Pα a ∧ Pα a ∧ Pα a := by
  assert_constraints [h]
    -- Names shuffled because I couldn't bother doing that SAT assignment.
    (relation Prop),
    (Proper (Rα ⟹ ?r0) Pα),
    (relation Prop),
    (Proper (Rα ⟹ ?r1) Pα),
    (relation Prop),
    (Proper (?r1 ⟹ ?r0 ⟹ ?r2) And),
    (relation Prop),
    (Proper (Rα ⟹ ?r3) Pα),
    (relation Prop),
    (Proper (?r3 ⟹ ?r2 ⟹ ?r4) And),
    (relation Prop),
    (Proper (Rα ⟹ ?r5) Pα),
    (relation Prop),
    (Proper (?r5 ⟹ ?r4 ⟹ ?r6) And),
    (relation Prop),
    (Proper (Rα ⟹ ?r7) Pα),
    (relation Prop),
    (Proper (?r7 ⟹ ?r6 ⟹ ?r8) And),
    (relation Prop),
    (Proper (Rα ⟹ ?r9) Pα),
    (Proper (?r9 ⟹ ?r8 ⟹ flip impl) And);
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

@[grwerite]
instance unionProper : Proper (eqset ⟹ eqset ⟹ eqset) union := ⟨unionCompat⟩

example : ∀ s, eqset (union (union s empty) s) s := by
  intro s
  assert_constraints [unionEmpty]
    (ProperProxy ?r s),
    (relation SET),
    (relation SET),
    (Proper (eqset ⟹ ?r ⟹ ?r0) union),
    (ProperProxy ?r1 s),
    (relation SET),
    (Proper (?r0 ⟹ ?r1 ⟹ flip impl) eqset);
  --assert_constraints [unionIdem]
  --apply Reflexive.rfl
  sorry


/-
Some more Coq constraints for problems:
-/

/- Coq constraints ✓
Proper (r ==> flip impl) (f c b)
-/
example (a b c : α) (r : relation α) (h: r a b) (f: α → α → α → Prop) : f c b a := by
  assert_constraints [h]
    (Proper (r ⟹ flip impl) (f c b));
  sorry

/- Coq constraints ✓
Proper (r ==> ?r0 ==> ?r ==> flip impl) f
ProperProxy ?r0 b
ProperProxy ?r c
-/
example (r : relation α) (h : r a x) (f : α → β → γ → Prop) : f a b c := by
  assert_constraints [h]
    (ProperProxy ?r0 b),
    (relation β),
    (ProperProxy ?r c),
    (relation γ),
    (Proper (r ⟹ ?r0 ⟹ ?r ⟹ flip impl) f);
  sorry

example (r : relation α) (h : r a x) (f: α → β → γ → α → Prop) : f a b c a := by
  assert_constraints [h]
    (ProperProxy ?r b),
    (relation β),
    (ProperProxy ?r0 c),
    (relation γ),
    (Proper (r ⟹ ?r ⟹ ?r0 ⟹ r ⟹ flip impl) f);
  sorry

/- Coq constraints
Proper (r ==> ?r) g
Proper (?r ==> r ==> Basics.flip Basics.impl) (f b b)
-/
example (r : relation α) (g : α → α) (h : r a x) (f: β → β → α → α → Prop) : f b b (g a) a := by
  assert_constraints [h]
    (relation α),
    (Proper (r ⟹ ?r) g),
    (Proper (?r ⟹ r ⟹ flip impl) (f b b));
  sorry

/- Coq instances ✓
Proper (r ==> ?r) g
Proper (r ==> ?r0 ==> ?r ==> r ==> Basics.flip Basics.impl) f
ProperProxy ?r0 b
-/
example (r : relation α) (g : α → α) (h : r a x) (f: α → β → α → α → Prop) : f a b (g a) a := by
  assert_constraints [h]
    (relation α),
    (Proper (r ⟹ ?r) g),
    (ProperProxy ?r0 b),
    (relation β),
    (Proper (r ⟹ ?r0 ⟹ ?r ⟹ r ⟹ flip impl) f);
  sorry

/- ✓
Produces
  ?m1 : Relation A
  ?m2 : Proper (r ==> ?m1) f
  ?m3 : Proper (r ==> flip impl) P
-/
example {f : α → α} [Proper (r ⟹ r) f] [Proper (r ⟹ Iff) P] : r a a' → P (f a') → P (f a) := by
  intro h finish
  assert_constraints [h]
    (relation α),
    (Proper (r ⟹ ?m1) f),
    (Proper (?m1 ⟹ flip impl) P);
  sorry

/-
Produces: Nothing to rewrite. BUT WE CAN!
-/
-- RW under lambda
example {a : α} {P : (α → α) → Prop} [Proper (pointwiseRelation α r ⟹ Iff) P] : r a a' → P (λ _ => a') → P (λ _ => a) := by
  intro h finish
  assert_constraints [h]
    (Proper (pointwiseRelation α r ⟹ flip impl) P);
  sorry

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
  assert_constraints [H]
    (relation Prop),
    (Proper (Iff ⟹ ?r) (impl Q)),
    (ProperProxy ?r0 (Q -> Q)),
    (relation Prop),
    (Proper (?r ⟹ ?r0 ⟹ flip impl) And);
  sorry

/- ✓
Produces
  ?m1 : Proper (?r ==> flip impl) (And (Q -> Q))
  ?m2 : Proper (Iff ==> ?r) (impl Q)
  ?r : relation Prop
-/
example : ∀ P Q : Prop, (P ↔ Q) → (Q → Q) ∧ (Q → P) := by
  intros P Q H
  assert_constraints [H]
    (relation Prop),
    (Proper (Iff ⟹ ?r) (impl Q)),
    (Proper (?r ⟹ flip impl) (And (Q -> Q)));
  sorry

-- No rewrite possible on first two proofs.
example (r₁ : relation Prop) (r₂ : relation Prop) (h₁ : r₁ P Q) (h₂ : r₂ P Q) (H : Prop) (h₃ : r₁ H P) : H := by
  -- show error only on h₁ and h₂
  assert_constraints [h₁, ← h₂, h₃]
    (Subrel r₁ (flip impl));
  sorry

-- Reverse rewrite with `←`
/- Coq constraints:
TBD
-/
example {r : α → α → Prop} [Equiv r] : r b a → r b c → r a c := by
  intro rab rbc
  assert_constraints [← rab]
    (ProperProxy ?r c),
    (relation α),
    (Proper (r ⟹ ?r ⟹ flip impl) r);
  sorry

/- Coq constraints:
Fails with invalid constraints. Only works with leibniz equality in Coq. BUT WE CAN!

variable (f : α → Prop → γ → Prop)
example (h: f = g) : f a (f a (f a (f a True c) c) c ∧ True) c := by
  assert_constraints [h]
    (relation Prop),
    (ProperProxy ?r c),
    (relation γ),
    (relation Prop),
    (Proper (?r0 ⟹ ?r ⟹ ?r1) (g a)),
    (Subrel ?r2 (flip impl)),
    (Subrel ?r1 (flip impl)),
    (Transitive (flip impl)),
    (ProperProxy ?r3 c),
    (relation γ),
    (Proper (flip impl ⟹ ?r3 ⟹ ?r4) (g a)),
    (Subrel ?r5 (flip impl)),
    (Subrel ?r4 (flip impl)),
    (Transitive (flip impl)),
    (ProperProxy ?r5 True),
    (relation Prop),
    (Proper (flip impl ⟹ ?r5 ⟹ ?r6) And),
    (ProperProxy ?r7 c),
    (relation γ),
    (Proper (?r6 ⟹ ?r7 ⟹ flip impl) (g a)),
    (Subrel ?r8 (flip impl)),
    (Transitive (flip impl));
  sorry

-/
end Examples
