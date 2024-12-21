import Aesop
import Grw.Eauto
import Grw.AesopRuleset

macro "grw" : attr => `(attr| aesop unsafe 100% apply (rule_sets := [grewrite]))

initialize
  Lean.registerTraceClass `Meta.Tactic.grewrite

@[grw]
abbrev relation (α : Sort u) := α → α → Prop

@[grw]
def impl (α β : Prop) : Prop := α → β

@[grw]
def all (α : Sort u) (p : α -> Prop) :=
  ∀x, p x

@[grw]
def relation.inverse {α : Sort u} (r : relation α) : α → α → Prop :=
λ x y => r y x

postfix:max "⁻¹" => relation.inverse

@[grw]
class Reflexive {α : Sort u} (rel : relation α) where
  rfl : ∀ x, rel x x

@[grw]
class Symmetric {α : Sort u} (rel : relation α) where
  symm : ∀ x y, rel x y → rel⁻¹ x y

@[grw]
class Transitive {α : Sort u} (rel : relation α) where
  trans : ∀ x y z, rel x y → rel y z → rel x z

@[grw]
class PER {α: Sort u} (R: relation α) extends Symmetric R, Transitive R

@[grw]
class Equiv {α: Sort u} (R: relation α) extends PER R, Reflexive R

@[grw]
instance flipReflexive {α : Sort u} {r : relation α} [Reflexive r] : Reflexive r⁻¹ :=
  Reflexive.mk fun x => by
    rw [relation.inverse]
    apply Reflexive.rfl x

@[grw]
instance implReflexive : Reflexive impl :=
  Reflexive.mk fun _ => id

@[grw]
instance implTransitive : Transitive impl :=
  Transitive.mk fun _ _ _ pqr pq => pq ∘ pqr

@[grw]
class Subrel {α : Sort u} (q r : relation α) : Prop where
  subrelation : ∀ x y, q x y → r x y

@[grw]
instance subrelationRefl {α : Sort u} {r : relation α} : Subrel r r :=
  Subrel.mk fun _ _ => id

@[grw]
instance iffImplSubrelation : Subrel Iff impl :=
  Subrel.mk fun _ _ pq hq => propext pq ▸ hq

@[grw]
instance iffInverseImplSubrelation : Subrel Iff impl⁻¹ :=
  Subrel.mk fun _ _ pq hq => propext pq ▸ hq

@[grw]
class Proper {α : Sort u} (r : relation α) (m : α) where
  proper : r m m

@[grw]
instance reflexiveProper {α : Sort u} {r : relation α} [Reflexive r] (x : α) : Proper r x :=
  Proper.mk <| Reflexive.rfl x

@[grw]
def respectful {α : Sort u} {β : Sort v} (r : relation α) (r' : relation β) : relation (α → β) :=
  fun f g => ∀ x y, r x y → r' (f x) (g y)

@[grw]
theorem contrapositive {a b : Prop} :
  (a → b) → ¬ b → ¬ a :=
  fun hab hnb ha => hnb (hab ha)

@[grw]
instance notIffMorphism : Proper (respectful Iff Iff) Not :=
  Proper.mk fun _ _ x => Iff.intro (contrapositive x.mpr) (contrapositive x.mp)

notation:55 r " ⟹ " r' => respectful r r'
notation:55 r " ⟶ " r' => respectful r⁻¹ r'

@[grw]
instance contraposedMorphism : Proper (impl ⟶ impl) Not := by
  apply Proper.mk
  intro a b f na
  rw [relation.inverse, Not] at *
  apply contrapositive (f) (na)

@[grw]
instance transMorphism [Transitive r] : Proper (r ⟶ r ⟹ impl) r := by
  apply Proper.mk
  intro a b iab c d r r'
  rw [relation.inverse] at iab
  apply Transitive.trans
  apply iab
  apply Transitive.trans <;>
  assumption

@[grw]
def pointwiseRelation (α : Sort u) {β : Sort u} (r : relation β) : relation (α → β) :=
  fun f g => ∀ a, r (f a) (g a)

@[grw]
def forallRelation {α: Sort u} {P: α → Sort u}
    (sig: forall a, relation (P a)): relation (forall x, P x) :=
  fun f g => forall a, sig a (f a) (g a)

@[grw]
instance flipProper [mor : Proper (rα ⟹ rβ ⟹ rφ) f] : Proper (rβ ⟹ rα ⟹ rφ) (flip f) := by
  apply Proper.mk
  intro b₁ b₂ rb a₁ a₂ ra
  apply mor.proper
  repeat assumption

@[grw]
instance respectfulSubrelation [rs : Subrel r₂ r₁] [ss : Subrel s₁ s₂] : Subrel (r₁ ⟹ s₁) (r₂ ⟹ s₂) := by
  apply Subrel.mk
  intro f f' p x y rxy
  apply ss.subrelation
  apply p
  exact rs.subrelation x y rxy

@[grw]
instance : Proper (Subrel ⟹ Subrel) (@pointwiseRelation α β) := by
  apply Proper.mk
  intro rb rb' sr
  apply Subrel.mk
  intro f g hfg x
  apply sr.subrelation
  apply hfg

@[grw]
instance subrelationPointwise α [sub : @Subrel β r r'] : Subrel (pointwiseRelation α r) (pointwiseRelation α r') := by
  apply Subrel.mk
  intro f g pr a
  apply sub.subrelation
  apply pr

@[grw]
def relationEquivalence : relation (relation α) :=
  Eq

@[grw]
instance proper (α : Sort u) : Proper (relationEquivalence ⟹ Eq ⟹ Iff) (@Proper α) := by
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

theorem subrelationProper [p : Proper r₁ m] [sr : Subrel r₁ r₂] : Proper r₂ m := Proper.mk (by
  apply sr.subrelation
  apply p.proper)

--@[aesop unsafe 10% apply (rule_sets := [grewrite])]

--instance part [@Proper (α → β) (r ⟹ r') m] [@Proper α r x] : Proper r' (m x) := by
  --sorry

@[grw]
instance properInverse [p : Proper r m] : Proper r⁻¹ m := Proper.mk p.proper

@[grw]
theorem inverseInvol α (r : relation α) : r⁻¹⁻¹ = r := rfl

@[grw]
theorem inverseArrow α (ra : relation α) β (rb : relation β) : (ra ⟹ rb)⁻¹ = ra⁻¹ ⟹ rb⁻¹ := by
  funext f g
  apply propext
  apply Iff.intro <;>
  · intro h x y hra
    apply h
    exact hra

@[grw]
class Normalizes {α} (m m' : relation α) where
  normalizes : m = m'⁻¹

@[grw]
theorem norm1 α r : @Normalizes α r (r⁻¹) := Normalizes.mk rfl

@[grw]
theorem norm2 [n₁ : @Normalizes β r₀ r₁] [n₂ : @Normalizes β u₀ u₁] : Normalizes (r₀ ⟹ u₀) (r₁ ⟹ u₁) := Normalizes.mk (by
  funext f g
  apply propext
  apply Iff.intro <;>
  · simp [n₁.normalizes, n₂.normalizes]
    intro h x y hr
    apply h
    exact hr)

/- Instances Sébastien Michelland added -/

@[grw]
instance subrelationEqRespectfulEqEq {α β: Sort u} : Subrel Eq (@Eq α ⟹ @Eq β) := by
  apply Subrel.mk
  intro f g feqg a b aeqb
  simp_all

@[grw]
instance properPointwiseRelation {α β: Sort u}:
    Proper (Subrel ⟹ Subrel) (@pointwiseRelation α β) where
  proper _ _ h := by
    apply Subrel.mk
    intro f g hp a
    apply h.subrelation
    apply hp

@[grw]
instance: Equiv (@Eq α) where
  rfl  := Eq.refl
  symm  := by
    intros
    apply Eq.symm
    assumption
  trans := by
    intros
    apply Eq.trans
    repeat assumption

@[grw]
instance: Equiv Iff where
  rfl  := Iff.refl
  symm  := by
    intros
    apply Iff.symm
    assumption
  trans := by
    intros
    apply Iff.trans
    repeat assumption

@[grw]
instance {R : relation α} [PER R] : Proper (R ⟹ R ⟹ Iff) R := by
  apply Proper.mk
  intro a b rab c d rcd
  apply Iff.intro
  intros
  apply Transitive.trans
  apply Symmetric.symm
  assumption
  intros
  apply Transitive.trans
  repeat assumption
  intros
  apply Transitive.trans
  apply Transitive.trans
  repeat assumption
  apply Symmetric.symm
  assumption

@[grw]
instance {R : relation α} [PER R] : Proper (R ⟹ Eq ⟹ Iff) R := by
  apply Proper.mk
  intro a b rab c d hcd
  apply Iff.intro
  intro rac
  apply Transitive.trans
  apply Symmetric.symm
  assumption
  rw [hcd] at rac
  assumption
  intro rbd
  apply Transitive.trans
  assumption
  rw [← hcd] at rbd
  assumption

@[grw]
instance {R : relation α} [PER R] : Proper (Eq ⟹ R ⟹ Iff) R := by
  apply Proper.mk
  intro a b hab c d rcd
  apply Iff.intro
  intro rac
  apply Transitive.trans
  rw [← hab]
  repeat assumption
  intro rbd
  rw [hab]
  apply Transitive.trans
  assumption
  apply Symmetric.symm
  assumption

@[grw]
instance properFlip [P: Proper (Rα ⟹ Rβ ⟹ Rγ) f]:
    Proper (Rβ ⟹ Rα ⟹ Rγ) (flip f) where
  proper _ _ h_b _ _ h_a := P.proper _ _ h_a _ _ h_b

@[grw]
instance subrelEq [Reflexive R]: Subrel Eq R where
  subrelation h := by
    intro y heq
    simp_all
    apply Reflexive.rfl

@[grw]
instance respectfulPER [hr₁ : PER r₁] [hr₂ : PER r₂]: PER (r₁ ⟹ r₂) where
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

@[grw]
instance subrelIffImpl: Subrel Iff impl where
  subrelation h := by
    intro g iff
    apply iff.mp

@[grw]
instance subrelIffFlipImpl: Subrel Iff (flip impl) where
  subrelation h := by
    intro g iff
    apply iff.mpr

@[grw]
instance properAndIff: Proper (Iff ⟹ Iff ⟹ Iff) And :=
  ⟨fun _ _ hx _ _ hy => by simp [hx, hy]⟩

@[grw]
instance properOrIff: Proper (Iff ⟹ Iff ⟹ Iff) Or :=
  ⟨fun _ _ hx _ _ hy => by simp [hx, hy]⟩

@[grw]
instance properNotIff: Proper (Iff ⟹ Iff) Not :=
  ⟨fun _ _ h => by simp [h]⟩

eauto_create_db grewrite
eauto_hint reflexiveProper : grewrite
eauto_hint Reflexive.rfl : grewrite
