/-
  Copyright (c) 2025 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

import Grw.Attribute

open Lean.Order

--attribute [grw] Iff for existing theorems
--set_option trace.Meta.Tactic.grw.hints true

abbrev relation (α : Sort u) := α → α → Prop

class Proper {α : Sort u} (r : relation α) (m : α) where
  proper : r m m

@[grw]
theorem Proper_intro : (h : r m m) → Proper r m := (⟨·⟩)

/--
Every element in the carrier of a reflexive relation is a morphism for this relation. We use a proxy class for this case which is used internally to discharge reflexivity constraints. The `Reflexive` instance will almost always be used, but it won't apply in general to any kind of `Proper (A -> B) _ _` goal, making proof-search much slower. A cleaner solution would be to be able to set different priorities in different hint bases and select a particular hint database for resolution of a type class constraint.
-/

class ProperProxy {α : Sort u} (r : relation α) (m : α) where
  proxy : r m m

@[grw]
theorem ProperProxy_intro : (h : r m m) → Proper r m := (⟨·⟩)

class ReflexiveProxy {α : Sort u} (r : relation α) where
  reflexive_proxy : ∀ x, r x x

@[grw]
theorem ReflexiveProxy_intro : (h : ∀ x, r x x) → ReflexiveProxy r := (⟨·⟩)

@[grw]
theorem eq_proper_proxy (x : α) : ReflexiveProxy r → ProperProxy (@Eq α) x := fun _ => ⟨rfl⟩

/--
Every reflexive relation gives rise to a morphism. If the relation is not determined (is an mvar), then we restrict the solutions to predefined ones (equality, or iff on Prop), using ground instances. If the relation is determined then `ReflexiveProxy` calls back to `Reflexive`.
-/

class Reflexive {α : Sort u} (rel : relation α) where
  rfl : ∀ x, rel x x

@[grw]
theorem reflexive_intro : (h : ∀ x, r x x) → Reflexive r := (⟨·⟩)


@[grw]
theorem reflexive_proper {α : Sort u} {r : relation α} (x : α) : Reflexive r → Proper r x := (⟨·.rfl x⟩)

@[grw]
theorem proper_ProperProxy x : Proper r x → ProperProxy r x := (⟨·.proper⟩)

@[grw]
theorem reflexive_ProperProxy {α : Sort u} {r : relation α} (x : α) : ReflexiveProxy r → ProperProxy r x := (⟨·.reflexive_proxy x⟩)

@[grw]
theorem reflexive_reflexive_proxy {α : Sort u} {r : relation α} : Reflexive r → ReflexiveProxy r := (⟨·.rfl⟩)

/--
The non-dependent version is an instance where we forget dependencies.
-/

def relation.inverse {α : Sort u} (r : relation α) : α → α → Prop :=
λ x y => r y x

postfix:max "⁻¹" => relation.inverse

def respectful {α : Sort u} {β : Sort v} (r : relation α) (r' : relation β) : relation (α → β) :=
  fun f g => ∀ x y, r x y → r' (f x) (g y)

notation:55 r " ⟹ " r' => respectful r r'
notation:55 r " ⟶ " r' => respectful r⁻¹ r'

/--
Non-dependent pointwise lifting
-/

def pointwiseRelation (α : Sort u) {β : Sort u} (r : relation β) : relation (α → β) :=
  fun f g => ∀ a, r (f a) (g a)

/-
We let Lean infer these relations when a default relation should be found on the function space.
-/

/--
Rewrite relation on a given support: declares a relation as a rewrite
   relation for use by the generalized rewriting tactic.
   It helps choosing if a rewrite should be handled
   by the generalized or the regular rewriting tactic using leibniz equality.
   Users can declare an [RewriteRelation A RA] anywhere to declare default
   relations on a given type `A`. This is also done automatically by
   the [Declare Relation A RA] commands. It has no mode declaration:
   it will assign `?A := Prop, ?R := iff` on an entirely unspecified query
   `RewriteRelation ?A ?R`, or any prefered rewrite relation of priority < 2.
-/

class RewriteRelation (rα : relation α) : Prop

@[grw]
theorem RewriteRelation_intro : RewriteRelation α := ⟨⟩

class Symmetric {α : Sort u} (r : relation α) where
  symm : ∀ x y, r x y → r⁻¹ x y

@[grw]
theorem Symmetric_intro : (∀ x y, r x y → r⁻¹ x y) → Symmetric r := (⟨·⟩)

class Transitive {α : Sort u} (r : relation α) where
  trans : ∀ x y z, r x y → r y z → r x z

@[grw]
theorem Transitive_intro : (∀ x y z, r x y → r y z → r x z) → Transitive r := (⟨·⟩)

class PER {α: Sort u} (r: relation α) extends Symmetric r, Transitive r

@[grw]
theorem PER_intro : Symmetric r → Transitive r → PER r := fun _ _ => ⟨⟩

class Equiv {α: Sort u} (R: relation α) extends PER R, Reflexive R

@[grw]
theorem Equiv_intro : PER r → Reflexive r → Equiv r := fun _ _ => ⟨⟩

@[grw]
theorem eq_Reflexive : Reflexive (@Eq α) := ⟨fun _ => rfl⟩

@[grw]
theorem eq_Symmetric : Symmetric (@Eq α) := by
  constructor
  intro x y hxy
  unfold relation.inverse
  simp_all

@[grw]
theorem eq_Transitive : Transitive (@Eq α) := by
  constructor
  simp_all

@[grw 10%]
theorem equivalence_rewrite_relation : Equiv eqα → RewriteRelation eqα := by
  intro eq
  constructor

/--
We let Rocq infer these relations when a default relation should be found on the function space.
-/

@[grw]
theorem rewrite_relation_pointwise {_ : @RewriteRelation β r} : RewriteRelation (@pointwiseRelation α β r) := ⟨⟩

@[grw]
theorem rewrite_relation_eq_dom {_ : @RewriteRelation β r} : RewriteRelation (respectful (@Eq α) r) := ⟨⟩

/--
Pointwise reflexive

TODO: keep the tactics in mind
-/

theorem eq_rewrite_relation {α} : RewriteRelation (@Eq α) := ⟨⟩

@[grw]
def relation_equivalence : relation (relation α) :=
  fun r₁ r₂ => ∀ x y, r₁ x y ↔ r₂ x y

@[grw]
theorem pointwise_pointwise (r : relation β) : relation_equivalence (pointwiseRelation α r) (@Eq α ⟹ r) := by
  unfold relation_equivalence pointwiseRelation respectful
  simp

class Subrel {α : Sort u} (q r : relation α) : Prop where
  subrelation : Subrelation q r

@[grw]
theorem Subrel_intro : Subrelation q r → Subrel q r := (⟨·⟩)

/--
Subrelations induce a morphism on the identity.
-/
@[grw]
theorem subrelation_id_proper : @Subrel α rα rα' → Proper (rα ⟹ rα') id := by
  intro hsr
  constructor
  intro x y rxy
  apply hsr.subrelation rxy

/--
The subrelation property goes through products as usual.
-/
@[grw]
theorem subrelation_respectful : @Subrel α rα' rα → @Subrel β rβ rβ' → Subrel (rα ⟹ rβ) (rα' ⟹ rβ') := by
  intro hα hβ
  constructor
  intro f g hfg a₁ a₂ ha
  apply hβ.subrelation
  apply hfg
  exact hα.subrelation ha

/-
 And of course it is reflexive.
-/
theorem subrelation_refl r : @Subrel α r r := by
  constructor
  intro _ _
  simp

/--
The unconvertible typeclass, to test that two objects of the same type are actually different.
-/
class Unconvertible (α : Sort u) (a b : α) where
  unconvertible : Unit

/--
Proper is itself a covariant morphism for subrelation. We use an unconvertible premise to avoid looping.
-/
@[grw]
theorem subrelation_proper {α : Sort u} {r r' : relation α} {m : α} : Proper r' m → Unconvertible (relation α) r r' → @Subrel α r' r → Proper r m := fun p _ sr => ⟨sr.subrelation p.proper⟩

def impl (α β : Prop) : Prop := α → β

@[grw]
theorem proper_subrelation_proper : Proper (Subrel ⟹ Eq ⟹ impl) (@Proper α) := by
  constructor
  intro ra ra' hra a b eqab p
  rw [← eqab]
  constructor
  apply hra.subrelation
  exact p.proper

@[grw 25%]
theorem pointwise_subrelation α : @Subrel β r r' → Subrel (pointwiseRelation α r) (pointwiseRelation α r') := by
  intro sub
  apply Subrel.mk
  intro f g pr a
  apply sub.subrelation
  apply pr

/-
Essential subrelation instances for iff, impl and pointwise_relation.
-/
@[grw 50%]
theorem iff_impl_subrelation : Subrel Iff impl where
  subrelation h := h.mp

@[grw 50%]
theorem iff_flip_impl_subrelation : Subrel Iff (flip impl) where
  subrelation h := h.mpr

/--
We can build a PER on the Lean function space if we have PERs on the domain and codomain.
-/

@[grw]
theorem respectful_PER (hr₁ : PER r₁) (hr₂ : PER r₂) : PER (r₁ ⟹ r₂) where
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

def complement (r : relation α) : relation α := fun x y => r x y → False

/-
The complement of a relation conserves its proper elements.
-/
@[grw]
theorem complement_proper : @Proper (α → α → Prop) (rα ⟹ rα ⟹ Iff) r → Proper (rα ⟹ rα ⟹ Iff) (complement r) := by
  intro p
  constructor
  intro x x' hx y y' hy
  unfold complement
  rw [p.proper x x' hx y y' hy]

/-
The `flip` too, actually the `flip` instance is a bit more general.
-/
@[grw]
theorem flip_proper : Proper (rα ⟹ rβ ⟹ rφ) f → Proper (rβ ⟹ rα ⟹ rφ) (flip f) := by
  intro mor
  constructor
  intro b₁ b₂ rb a₁ a₂ ra
  apply mor.proper
  repeat assumption

/--
Every Transitive relation gives rise to a binary morphism on [impl], contravariant in the first argument, covariant in the second.
-/
@[grw]
theorem trans_contra_co_morphism : @Transitive α r → Proper (r ⟶ r ⟹ impl) r := by
  intro h
  constructor
  intro x y h₀ x₀ y₀ h₁ h₂
  exact h.trans y x y₀ h₀ (h.trans x x₀ y₀ h₂ h₁)

/-
Proper declarations for partial applications.
-/
@[grw 25%]
theorem trans_contra_inv_impl_morphism {x : α} : @Transitive α r → Proper (r ⟶ flip impl) (r x) := by
  intro tr
  constructor
  intro y z ryz rxz
  exact tr.trans x z y rxz ryz

@[grw 25%]
theorem trans_co_impl_morphism {x : α} : @Transitive α r → Proper (r ⟹ impl) (r x) := by
  intro tr
  constructor
  intro y z h₁ h₂
  exact tr.trans x y z h₂ h₁

@[grw 25%]
theorem trans_sym_co_inv_impl_morphism {x : α} : @PER α r → Proper (r ⟹ flip impl) (r x) := by
  intro pe
  constructor
  intro y z ryz rxz
  exact pe.trans x z y rxz (pe.symm y z ryz)

theorem trans_sym_contra_impl_morphism {x : α} : @PER α r → Proper (r ⟶ impl) (r x) := by
  intro pe
  constructor
  intro y z ryz rxy
  exact pe.trans x y z rxy (pe.symm z y ryz)

@[grw 50%]
theorem per_partial_app_morphism {x : α} : @PER α r → Proper (r ⟹ Iff) (r x) := by
  intro pe
  constructor
  intro y z ryz
  apply Iff.intro
  intro rxy
  exact pe.trans x y z rxy ryz
  intro rxz
  exact pe.trans x z y rxz (pe.symm y z ryz)

/--
Every Transitive relation induces a morphism by "pushing" an `r x y` on the left of an `r x z` proof to get an `r y z` goal.
-/

@[grw 75%]
theorem PER_morphism : @PER α r → Proper (r ⟹ r ⟹ Iff) r := by
  intro pe
  constructor
  intro x x' rxx' y y' ryy'
  apply Iff.intro
  intro rxy
  have rx'y := pe.trans x' x y (pe.symm x x' rxx') rxy
  exact pe.trans x' y y' rx'y ryy'
  intro rx'y'
  have rxy' := pe.trans x x' y' rxx' rx'y'
  exact pe.trans x y' y rxy' (pe.symm y y' ryy')

@[grw]
theorem ymmetric_equiv_flip : @Symmetric α r → relation_equivalence r (flip r) := by
  intro sy
  unfold relation_equivalence
  intros x y
  apply Iff.intro <;>
  . intro h
    apply sy.symm
    exact h

def compose {α β γ} (g : β -> γ) (f : α -> β) :=
  fun x : α => g (f x)

@[grw]
theorem compose_proper (rα : relation α) (rβ : relation β) (rγ : relation γ) : Proper ((rβ ⟹ rγ) ⟹ (rα ⟹ rβ) ⟹ (rα ⟹ rγ)) (@Function.comp α β γ) := by
  constructor
  unfold respectful at *
  unfold Function.comp
  intros f f' hf g g' hg x x' hxx'
  apply hf
  apply hg
  exact hxx'

@[grw]
theorem reflexive_eq_dom_reflexive : @Reflexive β r → Reflexive ((@Eq α) ⟹ r) := by
  intro rf
  unfold respectful
  constructor
  intro f x y heqxy
  rw [heqxy]
  apply rf.rfl

/--
`respectful` is a morphism for relation equivalence.
-/
@[grw]
theorem respectful_morphism : Proper (relation_equivalence ⟹ relation_equivalence ⟹ relation_equivalence) (@respectful α β) := by
  constructor
  intros rα rα' hα rβ rβ' hβ f g
  apply Iff.intro
  · intro hfg x x' h
    specialize hβ (f x) (g x')
    specialize hα x x'
    apply hβ.mp
    apply hfg
    apply hα.mpr
    assumption
  · intro hfg x x' h
    specialize hβ (f x) (g x')
    specialize hα x x'
    apply hβ.mpr
    apply hfg
    apply hα.mp
    assumption

@[grw]
theorem Reflexive_partial_app_morphism : Proper (r ⟹ r') m → ProperProxy r x → Proper r' (m x) := by
  intro p pp
  constructor
  apply p.proper
  apply pp.proxy

@[grw]
theorem flip_respectful : relation_equivalence (flip (r ⟹ r')) (flip r ⟹ flip r') := by
  unfold relation_equivalence
  intros
  unfold flip respectful
  apply Iff.intro <;>
  simp_all

/--
Treating flip: can't make them direct instances as we need at least a `flip` present in the goal.
-/
@[grw]
theorem flip1 : @Subrel α r' r → Subrel (flip (flip r')) r := by
  intro sr
  constructor
  unfold flip
  intro _ _ rxy
  apply sr.subrelation
  exact rxy

@[grw]
theorem flip2 : @Subrel α r r' → Subrel r (flip (flip r')) := by
  intro sr
  constructor
  unfold flip
  intro _ _ rxy
  apply sr.subrelation
  exact rxy

@[grw]
theorem eq_subrelation : @Reflexive α r → Subrel (@Eq α) r := by
  intro rf
  constructor
  intro x y rxy
  rw [rxy]
  apply rf.rfl

@[grw]
theorem proper_flip_proper : @Proper α r m → Proper (flip r) m := by
  intro p
  constructor
  exact p.proper

@[grw]
theorem proper_eq : Proper (@Eq α) x := by
  constructor
  rfl

@[grw]
theorem proper_proper {α : Sort u} : Proper (relation_equivalence ⟹ Eq ⟹ Iff) (@Proper α) := by
  constructor
  intros r₁ r₂ hre p₁ p₂ heq
  apply Iff.intro
  · intro h
    constructor
    replace h := h.proper
    rw [hre p₁ p₁, heq] at h
    exact h
  · intro h
    constructor
    replace h := h.proper
    rw [← hre p₂ p₂, ← heq] at h
    exact h

/-
Special-purpose class to do normalization of signatures w.r.t. flip.
-/
class Normalizes {α} (m m' : relation α) where
  normalizes : relation_equivalence m m'

/-
Current strategy: add `flip` everywhere and reduce using `subrelation` afterwards.
-/
@[grw]
theorem proper_normalizes_proper {m : α} : Normalizes r0 r1 → @Proper α r1 m → Proper r0 m := by
  intro n p
  constructor
  rw [n.normalizes]
  exact p.proper

@[grw]
theorem flip_atom (r : relation α) : Normalizes r (flip (flip r)) := by
  constructor
  unfold flip relation_equivalence
  intro x y
  simp

@[grw]
theorem flip_arrow {α : Sort u} {β : Sort u} {r r''' : relation α} {r' r'' : relation β} : @Normalizes α r (flip r''') → @Normalizes β r' (flip r'') → @Normalizes (α → β) (r ⟹ r') (flip (r''' ⟹ r'')) := by
  intro n1 n2
  constructor
  unfold relation_equivalence respectful flip at *
  intro x x0
  constructor
  . intro h x1 y h0
    have r_eq_r''' := n1.normalizes y x1
    rw [← r_eq_r'''] at h0
    have hr' := h y x1 h0
    have r'_eq_r'' := n2.normalizes (x y) (x0 x1)
    rw [← r'_eq_r'']
    exact hr'
  . intro h y x1 h0
    have r'_eq_r'' := n2.normalizes (x y) (x0 x1)
    rw [r'_eq_r'']
    have r_eq_r''' := n1.normalizes y x1
    rw [r_eq_r'''] at h0
    have hr' := h x1 y h0
    exact hr'

/--
When the relation on the domain is symmetric, we can flip the relation on the codomain. Same for binary functions.
-/
@[grw]
theorem proper_symm_flip : ∀ s : @Symmetric α r₁, ∀ p : @Proper (α → β) (r₁ ⟹ r₂) f, Proper (r₁ ⟹ flip r₂) f := by
  intros s p
  constructor
  intros a b rab
  apply p.proper
  apply s.symm
  exact rab

-- Idk why Coq suddenly uses universal quantifiers for everything but I will follow along.

@[grw]
theorem proper_sym_flip_2 : ∀ s : @Symmetric α r₁, ∀ s' : @Symmetric β r₂, ∀ p : @Proper (α → β → γ) (r₁ ⟹ r₂ ⟹ r₃) f, Proper (r₁ ⟹ r₂ ⟹ flip r₃) f := by
  intros s s' p
  constructor
  intros a b rab c d rcd
  apply p.proper
  apply s.symm
  exact rab
  apply s'.symm
  exact rcd

@[grw]
theorem proper_sym_impl_iff : ∀ s : @Symmetric α r, ∀ p : Proper (r ⟹ impl) f, Proper (r ⟹ Iff) f := by
  intro s p
  constructor
  intro x y rxy
  constructor
  . intro fx
    apply p.proper
    exact rxy
    exact fx
  . intro fy
    apply p.proper
    apply s.symm x y rxy
    exact fy

@[grw]
theorem proper_sym_impl_iff_2 : ∀ _ : @Symmetric α r, ∀ _ : @Symmetric β r', ∀ _ : Proper (r ⟹ r' ⟹ impl) f, Proper (r ⟹ r' ⟹ Iff) f := by
  intros s1 s2 p
  constructor
  intros x x' hxx' y y' hyy'
  constructor
  . intro fxy
    apply p.proper
    . exact hxx'
    . exact hyy'
    . exact fxy
  . intro fx'y'
    apply p.proper
    . exact (s1.symm x x' hxx')
    . exact (s2.symm y y' hyy')
    . exact fx'y'

/-
Section for `Proper` theorems for propositional connectives.
-/

theorem contrapositive {a b : Prop} :
  (a → b) → ¬ b → ¬ a :=
  fun hab hnb ha => hnb (hab ha)

@[grw 75%]
theorem not_impl_morpthism : Proper (impl ⟶ impl) Not := by
  constructor
  intros x y ixy
  apply contrapositive
  exact ixy

@[grw]
theorem not_Iff_morphism : Proper (respectful Iff Iff) Not :=
  Proper.mk fun _ _ x => Iff.intro (contrapositive x.mpr) (contrapositive x.mp)

@[grw 75%]
theorem proper_And_impl : Proper (impl ⟹ impl ⟹ impl) And := by
  constructor
  intro x x' hxx' y y' hyy' h
  constructor
  . exact hxx' h.left
  . exact hyy' h.right

@[grw]
theorem proper_And_Iff : Proper (Iff ⟹ Iff ⟹ Iff) And :=
  ⟨fun _ _ hx _ _ hy => by simp [hx, hy]⟩

@[grw 75%]
theorem proper_Or_impl : Proper (impl ⟹ impl ⟹ impl) Or := by
  constructor
  intro x x' hxx' y y' hyy' h
  cases h with
  | inl hx => exact Or.inl (hxx' hx)
  | inr hy => exact Or.inr (hyy' hy)

@[grw]
theorem proper_Or_Iff : Proper (Iff ⟹ Iff ⟹ Iff) Or :=
  ⟨fun _ _ hx _ _ hy => by simp [hx, hy]⟩

@[grw]
theorem iff_iff_iff_impl_morphism : Proper (Iff ⟹ Iff ⟹ Iff) impl := by
  constructor
  intro x x' hxx' y y' hyy'
  constructor <;>
  . simp [hxx', hyy']

@[grw]
theorem ex_iff_morphism : Proper (pointwiseRelation α Iff ⟹ Iff) (@Exists α) := by
  constructor
  intro f g h
  constructor
  · intro ⟨x, hx⟩
    exact ⟨x, (h x).mp hx⟩
  · intro ⟨x, hx⟩
    exact ⟨x, (h x).mpr hx⟩

@[grw 75%]
theorem ex_impl_morphism : Proper (pointwiseRelation α impl ⟹ impl) (@Exists α) := by
  constructor
  intro f g h
  · intro ⟨x, hx⟩
    exact ⟨x, (h x) hx⟩

@[grw 75%]
theorem ex_flip_impl_morphism : Proper (pointwiseRelation α (flip impl) ⟹ flip impl) (@Exists α) := by
  constructor
  intro f g h
  · intro ⟨x, hx⟩
    exact ⟨x, (h x) hx⟩

def all (α : Sort u) (p : α -> Prop) :=
  ∀x, p x

@[grw]
theorem all_iff_morphism : Proper (pointwiseRelation α Iff ⟹ Iff) (@all α) := by
  constructor
  intro f g h
  constructor
  . intro hall
    intro x
    rw [← h x]
    exact hall x
  . intro hall
    intro x
    rw [h x]
    exact hall x

@[grw 75%]
theorem all_impl_morphism : Proper (pointwiseRelation α impl ⟹ impl) (@all α) := by
  constructor
  intro f g h
  intro hall
  intro x
  apply h x
  apply hall x

@[grw 75%]
theorem all_flip_impl_morphism : Proper (pointwiseRelation α (flip impl) ⟹ flip impl) (@all α) := by
  constructor
  intro f g h
  intro hall
  intro x
  apply h x
  apply hall x

/--
Equivalent points are simultaneously accessible or not.
-/
@[grw]
theorem Acc_pt_morphism : Equiv e → Proper (e ⟹ e ⟹ Iff) r → Proper (e ⟹ Iff) (Acc r) := by
  intros e p
  constructor
  intros x x' exx'
  constructor
  · intro accx'
    induction accx' with
    | intro x'' h ih =>
      apply Acc.intro x'
      intro y hrx
      have ex'x := e.symm x'' x' exx'
      have hequiv := p.proper y y (e.rfl y) x'' x' exx'
      rw [← hequiv] at hrx
      exact h _ hrx
  · intro accx
    induction accx with
    | intro x'' h ih =>
      apply Acc.intro x
      intro y' hrx'
      have ex'x := e.symm x x'' exx'
      have hequiv := p.proper y' y' (e.rfl y') x x'' exx'
      rw [hequiv] at hrx'
      exact h _ hrx'

/--
Equivalent relations have the same accessible points.
-/
@[grw]
theorem Acc_rel_morphism : Proper (relation_equivalence ⟹ Eq ⟹ Iff) (@Acc α) := by
  constructor
  intros R R' hR x x' hx
  subst hx
  apply Iff.intro
  · intro acc
    induction acc with
    | intro x _ ih =>
      apply Acc.intro x
      intros y h
      apply ih
      rw [hR y x]
      exact h
  · intro acc'
    induction acc' with
    | intro x _ ih =>
      apply Acc.intro x
      intros y h
      apply ih
      rw [← hR y x]
      exact h

@[grw]
theorem well_founded_morphism : Proper (relation_equivalence ⟹ Iff) (@WellFounded α) := by
  constructor
  intro r r' h
  apply Iff.intro
  · intro wf
    constructor
    intro x
    induction wf.apply x with
    | intro x' ih' ih =>
      apply Acc.intro
      intro y hyr'
      rw [← h y x'] at hyr'
      exact ih y hyr'
  · intro wf'
    constructor
    intro x
    induction wf'.apply x with
    | intro x' ih' ih =>
      apply Acc.intro
      intro y hyr
      rw [h y x'] at hyr
      exact ih y hyr

/-
Everything below is NOT from the Coq libary but from papers or other implementations.
-/

@[grw]
theorem flip_reflexive {α : Sort u} {r : relation α} : Reflexive r → Reflexive r⁻¹ := by
  intro r
  constructor
  intro x
  rw [relation.inverse]
  apply Reflexive.rfl x

@[grw]
theorem impl_reflexive : Reflexive impl :=
  Reflexive.mk fun _ => id

@[grw]
theorem impl_transitive : Transitive impl :=
  Transitive.mk fun _ _ _ pqr pq => pq ∘ pqr

@[grw]
theorem Iff_impl : Proper (r ⟹ Iff) a → Proper (r ⟹ flip impl) a := by
  intro p
  constructor
  unfold respectful flip impl
  intros x y rxy ay
  apply (p.proper x y rxy).mpr ay

@[grw]
theorem trans_morphism : Transitive r → Proper (r ⟶ r ⟹ impl) r := by
  intro ht
  apply Proper.mk
  intro a b iab c d r r'
  rw [relation.inverse] at iab
  apply ht.trans
  apply iab
  apply ht.trans <;>
  assumption

@[grw]
def forall_relation {α: Sort u} {P: α → Sort u}
    (sig: forall a, relation (P a)): relation (forall x, P x) :=
  fun f g => forall a, sig a (f a) (g a)

@[grw]
theorem respectful_subrelation : Subrel r₂ r₁ → Subrel s₁ s₂ → Subrel (r₁ ⟹ s₁) (r₂ ⟹ s₂) := by
  intro rs ss
  apply Subrel.mk
  intro f f' p x y rxy
  apply ss.subrelation
  apply p
  exact rs.subrelation rxy

@[grw]
theorem proper_pointwise : Proper (Subrel ⟹ Subrel) (@pointwiseRelation α β) := by
  apply Proper.mk
  intro rb rb' sr
  apply Subrel.mk
  intro f g hfg x
  apply sr.subrelation
  apply hfg

@[grw]
theorem subrelation_pointwise α : @Subrel β r r' → Subrel (pointwiseRelation α r) (pointwiseRelation α r') := by
  intro sub
  apply Subrel.mk
  intro f g pr a
  apply sub.subrelation
  apply pr

@[grw]
theorem proper (α : Sort u) : Proper (relation_equivalence ⟹ Eq ⟹ Iff) (@Proper α) := by
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



/-
⚠ Should be covered with previous `subrelation_proper` instance ⚠

only apply at the top of the goal with the subrelation flag set to true

theorem subrelation_proper : Proper r₁ m → Subrel r₁ r₂ → Proper r₂ m := fun p sr => ⟨sr.subrelation p.proper⟩
-/

@[grw 10%]
theorem «partial» (h₁ : Proper (r ⟹ r') m) (h₂ : Proper r x) : Proper r' (m x) := by
  constructor
  replace h₁ := h₁.proper
  replace h₂ := h₂.proper
  rw [respectful] at h₁
  exact h₁ x x h₂

@[grw]
theorem properInverse : Proper r m → Proper r⁻¹ m := fun p => ⟨p.proper⟩

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


/- Instances Sébastien Michelland added -/

@[grw]
theorem subrelation_Eq_respectful_Eq_Eq {α β: Sort u} : Subrel Eq (@Eq α ⟹ @Eq β) := by
  constructor
  intro f g feqg a b aeqb
  simp_all

@[grw]
theorem proper_pointwise_relation {α β: Sort u}:
    Proper (Subrel ⟹ Subrel) (@pointwiseRelation α β) where
  proper _ _ h := by
    constructor
    intro f g hp a
    apply h.subrelation
    apply hp

@[grw]
theorem equiv_of_Eq : Equiv (@Eq α) where
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
theorem equiv_of_Iff : Equiv Iff where
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

@[grw]
theorem PER_proper_Eq {r : relation α} : PER r → Proper (r ⟹ Eq ⟹ Iff) r := by
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

@[grw]
theorem PER_proper_Iff {r : relation α} : PER r → Proper (Eq ⟹ r ⟹ Iff) r := by
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

@[grw]
theorem proper_flip : Proper (Rα ⟹ Rβ ⟹ Rγ) f → Proper (Rβ ⟹ Rα ⟹ Rγ) (flip f) := by
  intro pa
  constructor
  rw [respectful]
  intro _ _ h_b
  rw [respectful]
  intro _ _ h_a
  apply pa.proper _ _ h_a _ _ h_b

@[grw]
theorem subrel_Eq : Reflexive R → Subrel Eq R := by
  intro r
  constructor
  rw [Subrelation]
  intro _ _ h
  rw [h]
  apply r.rfl

@[grw]
theorem proper_Not_Iff : Proper (Iff ⟹ Iff) Not :=
  ⟨fun _ _ h => by simp [h]⟩

initialize
  Lean.registerTraceClass `Meta.Tactic.grewrite
