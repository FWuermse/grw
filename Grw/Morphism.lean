import Aesop

def Relation (α : Sort u) := α → α → Prop

def Impl (α β : Prop) : Prop := α → β

def All (α : Type) (P : α -> Prop) := ∀ x : α, P x

def Relation.inverse {α : Sort u} (r : Relation α) : α → α → Prop :=
λ x y => r y x

postfix:max "⁻¹" => Relation.inverse

class Reflexive {α : Sort u} (rel : Relation α) where
  rfl : ∀ x, rel x x

class Symmetric {α : Sort u} (rel : Relation α) where
  symm : ∀ x y, rel x y → rel⁻¹ x y

class Transitive {α : Sort u} (rel : Relation α) where
  trans : ∀ x y z, rel x y → rel y z → rel x z

class Eqiv {r : Relation α} where
  rel : Reflexive r
  symm : Symmetric r
  trans : Transitive r

instance flipReflexive {α : Sort u} {r : Relation α} [Reflexive r] : Reflexive r⁻¹ :=
  Reflexive.mk fun x => by
    rw [Relation.inverse]
    apply Reflexive.rfl x

instance implReflexive : Reflexive Impl :=
  Reflexive.mk fun _ => id

instance implTransitive : Transitive Impl :=
  Transitive.mk fun _ _ _ pqr pq => pq ∘ pqr

class Subrel {α : Sort u} (q r : Relation α) : Prop where
  subrelation : ∀ x y, q x y → r x y

instance subrelationRefl {α : Sort u} {r : Relation α} : Subrel r r :=
  Subrel.mk fun _ _ => id

instance iffImplSubrelation : Subrel Iff Impl :=
  Subrel.mk fun _ _ pq hq => propext pq ▸ hq

instance iffInverseImplSubrelation : Subrel Iff Impl⁻¹ :=
  Subrel.mk fun _ _ pq hq => propext pq ▸ hq

class Proper {α : Sort u} (r : Relation α) (m : α) where
  proper : r m m

instance reflexiveProper {α : Sort u} {r : Relation α} [Reflexive r] (x : α) : Proper r x :=
  Proper.mk <| Reflexive.rfl x

def respectful {α β : Sort u} (r : Relation α) (r' : Relation β) : Relation (α → β) :=
  fun f g => ∀ x y, r x y → r' (f x) (g y)

theorem contrapositive {a b : Prop} :
  (a → b) → ¬ b → ¬ a :=
  fun hab hnb ha => hnb (hab ha)

instance notIffMorphism : Proper (respectful Iff Iff) Not :=
  Proper.mk fun _ _ x => Iff.intro (contrapositive x.mpr) (contrapositive x.mp)

notation:55 r " ⟹ " r' => respectful r r'
notation:55 r " ⟶ " r' => respectful r⁻¹ r'

instance contraposedMorphism : Proper (Impl ⟶ Impl) Not := by
  apply Proper.mk
  intro a b f na
  rw [Relation.inverse, Not] at *
  apply contrapositive (f) (na)

instance transMorphism [Transitive r] : Proper (r ⟶ r ⟹ Impl) r := by
  apply Proper.mk
  intro a b iab c d r r'
  rw [Relation.inverse] at iab
  apply Transitive.trans
  apply iab
  apply Transitive.trans <;>
  assumption

def pointwiseRelation (α : Sort u) {β : Sort u} (r : Relation β) : Relation (α → β) :=
  fun f g => ∀ a, r (f a) (g a)

def all (α : Type) (p : α -> Prop) :=
  ∀x, p x

instance flipProper [mor : Proper (rα ⟹ rβ ⟹ rφ) f] : Proper (rβ ⟹ rα ⟹ rφ) (flip f) := by
  apply Proper.mk
  intro b₁ b₂ rb a₁ a₂ ra
  apply mor.proper
  repeat assumption

instance respectfulSubrelation [rs : Subrel r₂ r₁] [ss : Subrel s₁ s₂] : Subrel (r₁ ⟹ s₁) (r₂ ⟹ s₂) := by
  apply Subrel.mk
  intro f f' p x y rxy
  apply ss.subrelation
  apply p
  exact rs.subrelation x y rxy

instance : Proper (Subrel ⟹ Subrel) (@pointwiseRelation α β) := by
  apply Proper.mk
  intro rb rb' sr
  apply Subrel.mk
  intro f g hfg x
  apply sr.subrelation
  apply hfg

instance subrelationPointwise α [sub : @Subrel β r r'] : Subrel (pointwiseRelation α r) (pointwiseRelation α r') := by
  apply Subrel.mk
  intro f g pr a
  apply sub.subrelation
  apply pr

universe u v

inductive Tlist : Sort (max u v + 1)
| tnil : Tlist
| tcons : Sort v → Tlist → Tlist

local infix:65 "∶∶" => Tlist.tcons

def arrows (l : Tlist) (r : Sort u) : Sort u := by
match l, r with
| Tlist.tnil, r => exact r
| Tlist.tcons A l', r => exact A → arrows l' r

notation "predicate" l => arrows l (Type (u))

def binaryRelation (A : Type u) : Type (u + 1) :=
  predicate (.tcons A <| .tcons A Tlist.tnil)


def predicateEquivalence {l : Tlist} : binaryRelation (predicate l) :=
  pointwise_lifting Iff l

def relation_equivalence {α : Sort u} : Relation (Relation α) :=
    @predicateEquivalence (_::_::Tnil)

Include relation equivalence
instance Proper α : Proper (relationEquivalence ⟹ eq ⟹ iff) (@Proper A).


/-only apply at the top of the goal with the subrelation flag set to true

theorem subrelationProper [p : Proper r₁ m] [sr : Subrel r₁ r₂] : Proper r₂ m := Proper.mk (by
  apply sr.subrelation
  apply p.proper)
-/

instance properInverse [p : Proper r m] : Proper r⁻¹ m := Proper.mk p.proper

theorem inverseInvol α (r : Relation α) : r⁻¹⁻¹ = r := rfl

theorem inverseArrow α (ra : Relation α) β (rb : Relation β) : (ra ⟹ rb)⁻¹ = ra⁻¹ ⟹ rb⁻¹ := by
  funext f g
  apply propext
  apply Iff.intro <;>
  · intro h x y hra
    apply h
    exact hra

class Normalizes {α} (m m' : Relation α) where
  normalizes : m = m'⁻¹

theorem norm1 α r : @Normalizes α r (r⁻¹) := Normalizes.mk rfl

theorem norm2 [n₁ : @Normalizes β r₀ r₁] [n₂ : @Normalizes β u₀ u₁] : Normalizes (r₀ ⟹ u₀) (r₁ ⟹ u₁) := Normalizes.mk (by
  funext f g
  apply propext
  apply Iff.intro <;>
  · simp [n₁.normalizes, n₂.normalizes]
    intro h x y hr
    apply h
    exact hr)
