import Grw.Attribute

--attribute [grewrite] Iff for existing theorems
--set_option trace.Meta.Tactic.grewrite.hints true

@[grewrite]
abbrev relation (α : Sort u) := α → α → Prop

@[grewrite]
def impl (α β : Prop) : Prop := α → β

@[grewrite]
def all (α : Sort u) (p : α -> Prop) :=
  ∀x, p x

@[grewrite]
def relation.inverse {α : Sort u} (r : relation α) : α → α → Prop :=
λ x y => r y x

postfix:max "⁻¹" => relation.inverse

@[grewrite]
class Reflexive {α : Sort u} (rel : relation α) where
  rfl : ∀ x, rel x x

@[grewrite]
class Symmetric {α : Sort u} (rel : relation α) where
  symm : ∀ x y, rel x y → rel⁻¹ x y

@[grewrite]
class Transitive {α : Sort u} (rel : relation α) where
  trans : ∀ x y z, rel x y → rel y z → rel x z

@[grewrite]
class PER {α: Sort u} (R: relation α) extends Symmetric R, Transitive R

@[grewrite]
class Equiv {α: Sort u} (R: relation α) extends PER R, Reflexive R

@[grewrite]
theorem flipReflexive {α : Sort u} {r : relation α} : Reflexive r → Reflexive r⁻¹ := by
  intro r
  constructor
  intro x
  rw [relation.inverse]
  apply Reflexive.rfl x

@[grewrite]
theorem implReflexive : Reflexive impl :=
  Reflexive.mk fun _ => id

@[grewrite]
theorem implTransitive : Transitive impl :=
  Transitive.mk fun _ _ _ pqr pq => pq ∘ pqr

@[grewrite]
class Subrel {α : Sort u} (q r : relation α) : Prop where
  subrelation : Subrelation q r

@[grewrite]
theorem subrelationRefl {α : Sort u} {r : relation α} : Subrel r r :=
  ⟨id⟩

@[grewrite]
theorem iffImplSubrelation : Subrel Iff impl :=
  ⟨(propext . ▸ .)⟩

@[grewrite]
theorem iffInverseImplSubrelation : Subrel Iff impl⁻¹ :=
  ⟨(propext . ▸ .)⟩

@[grewrite]
class Proper {α : Sort u} (r : relation α) (m : α) where
  proper : r m m

-- This is a Coq hack taking an identical class that works with different instance
@[grewrite]
class ProperProxy {α : Sort u} (r : relation α) (m : α) where
  proxy : r m m

@[grewrite]
class ReflexiveProxy {α : Sort u} (r : relation α) where
  reflexiveProxy : ∀ x, r x x

@[grewrite]
theorem eqProperProxy (x : α) : ReflexiveProxy r → ProperProxy (@Eq α) x := fun _ => ⟨rfl⟩

@[grewrite]
theorem properProperProxy x : Proper r x → ProperProxy r x := fun h => ⟨h.proper⟩

@[grewrite]
theorem reflexiveProperProxy {α : Sort u} {r : relation α} (x : α) : ReflexiveProxy r → ProperProxy r x := fun h => ⟨h.reflexiveProxy x⟩

@[grewrite]
theorem reflexiveReflexiveProxy {α : Sort u} {r : relation α} : Reflexive r → ReflexiveProxy r := fun h => ⟨h.rfl⟩

@[grewrite]
theorem reflexiveProper {α : Sort u} {r : relation α} (x : α) : Reflexive r → Proper r x :=
  fun h => ⟨h.rfl x⟩

@[grewrite]
def respectful {α : Sort u} {β : Sort v} (r : relation α) (r' : relation β) : relation (α → β) :=
  fun f g => ∀ x y, r x y → r' (f x) (g y)

@[grewrite]
theorem contrapositive {a b : Prop} :
  (a → b) → ¬ b → ¬ a :=
  fun hab hnb ha => hnb (hab ha)

@[grewrite]
theorem notIffMorphism : Proper (respectful Iff Iff) Not :=
  Proper.mk fun _ _ x => Iff.intro (contrapositive x.mpr) (contrapositive x.mp)

notation:55 r " ⟹ " r' => respectful r r'
notation:55 r " ⟶ " r' => respectful r⁻¹ r'

@[grewrite]
theorem contraposedMorphism : Proper (impl ⟶ impl) Not := by
  apply Proper.mk
  intro a b f na
  rw [relation.inverse, Not] at *
  apply contrapositive (f) (na)

@[grewrite]
theorem iffImpl : Proper (r ⟹ Iff) a → Proper (r ⟹ flip impl) a := by
  intro p
  constructor
  unfold respectful flip impl
  intros x y rxy ay
  apply (p.proper x y rxy).mpr ay

@[grewrite]
theorem transMorphism : Transitive r → Proper (r ⟶ r ⟹ impl) r := by
  intro ht
  apply Proper.mk
  intro a b iab c d r r'
  rw [relation.inverse] at iab
  apply ht.trans
  apply iab
  apply ht.trans <;>
  assumption

@[grewrite]
def pointwiseRelation (α : Sort u) {β : Sort u} (r : relation β) : relation (α → β) :=
  fun f g => ∀ a, r (f a) (g a)

@[grewrite]
def forallRelation {α: Sort u} {P: α → Sort u}
    (sig: forall a, relation (P a)): relation (forall x, P x) :=
  fun f g => forall a, sig a (f a) (g a)

@[grewrite]
theorem flipProper : Proper (rα ⟹ rβ ⟹ rφ) f → Proper (rβ ⟹ rα ⟹ rφ) (flip f) := by
  intro mor
  apply Proper.mk
  intro b₁ b₂ rb a₁ a₂ ra
  apply mor.proper
  repeat assumption

@[grewrite]
theorem respectfulSubrelation : Subrel r₂ r₁ → Subrel s₁ s₂ → Subrel (r₁ ⟹ s₁) (r₂ ⟹ s₂) := by
  intro rs ss
  apply Subrel.mk
  intro f f' p x y rxy
  apply ss.subrelation
  apply p
  exact rs.subrelation rxy

@[grewrite]
theorem properPointwise : Proper (Subrel ⟹ Subrel) (@pointwiseRelation α β) := by
  apply Proper.mk
  intro rb rb' sr
  apply Subrel.mk
  intro f g hfg x
  apply sr.subrelation
  apply hfg

@[grewrite]
theorem subrelationPointwise α : @Subrel β r r' → Subrel (pointwiseRelation α r) (pointwiseRelation α r') := by
  intro sub
  apply Subrel.mk
  intro f g pr a
  apply sub.subrelation
  apply pr

@[grewrite]
def relationEquivalence : relation (relation α) :=
  Eq

@[grewrite]
theorem proper (α : Sort u) : Proper (relationEquivalence ⟹ Eq ⟹ Iff) (@Proper α) := by
  apply Proper.mk
  intro r r' hreq a b heq
  apply Iff.intro
  . intro hprp
    apply Proper.mk
    rw [← heq, ← hreq]
    apply hprp.proper
  . intro hprp
    apply Proper.mk
    rw [hreq, heq]
    apply hprp.proper

--only apply at the top of the goal with the subrelation flag set to true

theorem subrelationProper : Proper r₁ m → Subrel r₁ r₂ → Proper r₂ m := fun p sr => ⟨sr.subrelation p.proper⟩

--only apply with 10% prio
@[grewrite]
theorem «partial» (h₁ : Proper (r ⟹ r') m) (h₂ : Proper r x) : Proper r' (m x) := by
  constructor
  replace h₁ := h₁.proper
  replace h₂ := h₂.proper
  rw [respectful] at h₁
  exact h₁ x x h₂

@[grewrite]
theorem properInverse : Proper r m → Proper r⁻¹ m := fun p => ⟨p.proper⟩

@[grewrite]
theorem inverseInvol α (r : relation α) : r⁻¹⁻¹ = r := rfl

@[grewrite]
theorem inverseArrow α (ra : relation α) β (rb : relation β) : (ra ⟹ rb)⁻¹ = ra⁻¹ ⟹ rb⁻¹ := by
  funext f g
  apply propext
  apply Iff.intro <;>
  · intro h x y hra
    apply h
    exact hra

@[grewrite]
class Normalizes {α} (m m' : relation α) where
  normalizes : m = m'⁻¹

@[grewrite]
theorem norm1 α r : @Normalizes α r (r⁻¹) := Normalizes.mk rfl

@[grewrite]
theorem norm2 : @Normalizes β r₀ r₁ → @Normalizes β u₀ u₁ → Normalizes (r₀ ⟹ u₀) (r₁ ⟹ u₁) := by
  intro n₁ n₂
  constructor
  funext f g
  apply propext
  apply Iff.intro <;>
  · simp [n₁.normalizes, n₂.normalizes]
    intro h x y hr
    apply h
    exact hr

/- Instances Sébastien Michelland added -/

@[grewrite]
theorem subrelationEqRespectfulEqEq {α β: Sort u} : Subrel Eq (@Eq α ⟹ @Eq β) := by
  constructor
  intro f g feqg a b aeqb
  simp_all

@[grewrite]
theorem properPointwiseRelation {α β: Sort u}:
    Proper (Subrel ⟹ Subrel) (@pointwiseRelation α β) where
  proper _ _ h := by
    constructor
    intro f g hp a
    apply h.subrelation
    apply hp

@[grewrite]
theorem equivofeq : Equiv (@Eq α) where
  rfl  := Eq.refl
  symm  := by
    intros
    apply Eq.symm
    assumption
  trans := by
    intros
    apply Eq.trans
    repeat assumption

@[grewrite]
theorem equivofIff : Equiv Iff where
  rfl  := Iff.refl
  symm  := by
    intros
    apply Iff.symm
    assumption
  trans := by
    intros
    apply Iff.trans
    repeat assumption

@[grewrite]
theorem PERProper {r : relation α} : PER r → Proper (r ⟹ r ⟹ Iff) r := by
  intro per
  constructor
  intro a b rab c d rcd
  constructor
  intros
  apply per.trans
  apply per.symm
  assumption
  intros
  apply per.trans
  repeat assumption
  intros
  apply per.trans
  apply per.trans
  repeat assumption
  apply per.symm
  assumption

@[grewrite]
theorem PERProperEq {r : relation α} : PER r → Proper (r ⟹ Eq ⟹ Iff) r := by
  intro per
  constructor
  intro a b rab c d hcd
  apply Iff.intro
  intro rac
  apply per.trans
  apply per.symm
  assumption
  rw [hcd] at rac
  assumption
  intro rbd
  apply per.trans
  assumption
  rw [← hcd] at rbd
  assumption

@[grewrite]
theorem PERProperIff {r : relation α} : PER r → Proper (Eq ⟹ r ⟹ Iff) r := by
  intro per
  constructor
  intro a b hab c d rcd
  apply Iff.intro
  intro rac
  apply per.trans
  rw [← hab]
  repeat assumption
  intro rbd
  rw [hab]
  apply per.trans
  assumption
  apply per.symm
  assumption

@[grewrite]
theorem properFlip : Proper (Rα ⟹ Rβ ⟹ Rγ) f → Proper (Rβ ⟹ Rα ⟹ Rγ) (flip f) := by
  intro pa
  constructor
  rw [respectful]
  intro _ _ h_b
  rw [respectful]
  intro _ _ h_a
  apply pa.proper _ _ h_a _ _ h_b

@[grewrite]
theorem subrelEq : Reflexive R → Subrel Eq R := by
  intro r
  constructor
  rw [Subrelation]
  intro _ _ h
  rw [h]
  apply r.rfl

@[grewrite]
theorem respectfulPER (hr₁ : PER r₁) (hr₂ : PER r₂) : PER (r₁ ⟹ r₂) where
  symm h g hg x y h₁ := by
    apply hr₂.symm
    apply hg
    apply Symmetric.symm
    assumption
  trans f g h fg gh a b rab := by
    apply hr₂.trans
    apply fg
    exact rab
    apply gh
    apply Transitive.trans
    apply Symmetric.symm
    repeat assumption

@[grewrite]
theorem subrelIffImpl: Subrel Iff impl where
  subrelation h := h.mp

@[grewrite]
theorem subrelIffFlipImpl: Subrel Iff (flip impl) where
  subrelation h := h.mpr

@[grewrite]
theorem properAndIff: Proper (Iff ⟹ Iff ⟹ Iff) And :=
  ⟨fun _ _ hx _ _ hy => by simp [hx, hy]⟩

@[grewrite]
theorem properOrIff: Proper (Iff ⟹ Iff ⟹ Iff) Or :=
  ⟨fun _ _ hx _ _ hy => by simp [hx, hy]⟩

@[grewrite]
theorem properNotIff: Proper (Iff ⟹ Iff) Not :=
  ⟨fun _ _ h => by simp [h]⟩
