/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.Subobject.NoetherianObject

/-!
# Noetherian objects form a Serre class

In an abelian category, Noetherian objects are closed under subobjects, quotients,
and extensions. The Noetherian condition is Mathlib's ascending chain condition on
`Subobject`.

For an ascending chain in the middle of a short exact sequence, its intersections
with the first object and its images in the last object stabilize. The short five
lemma then shows that the original chain stabilizes. Comparability of the chain
members is essential to this argument.

The proof uses Joël Riou's Noetherian-object and short-exact-complex APIs in Mathlib.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] {X Y : C}

namespace Subobject

/-- Inverse image along an epimorphism in an abelian category reflects subobject inclusion. -/
lemma pullback_le_pullback_iff_of_epi (f : X ⟶ Y) [Epi f] (A B : Subobject Y) :
    (pullback f).obj A ≤ (pullback f).obj B ↔ A ≤ B := by
  constructor
  · intro h
    have : Epi (pullbackπ f A) :=
      Abelian.epi_fst_of_isLimit A.arrow f (isPullback f A).isLimit
    have : StrongEpi (pullbackπ f A) := strongEpi_of_epi _
    let sq : CommSq (ofLE _ _ h ≫ pullbackπ f B) (pullbackπ f A) B.arrow A.arrow :=
      ⟨by rw [Category.assoc, (isPullback f B).w, ← Category.assoc, ofLE_arrow,
        ← (isPullback f A).w]⟩
    exact le_of_comm sq.lift sq.fac_right
  · intro h
    exact (pullback f).monotone h

end Subobject

/-- An epimorphic image of a Noetherian object in an abelian category is Noetherian. -/
lemma isNoetherianObject_of_epi (p : X ⟶ Y) [Epi p] [IsNoetherianObject X] :
    IsNoetherianObject Y := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro f
  obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherianObject
    ⟨_, (Subobject.pullback p).monotone.comp f.2⟩
  refine ⟨n, fun m hm ↦ ?_⟩
  apply le_antisymm
  · exact (Subobject.pullback_le_pullback_iff_of_epi p _ _).1 (hn m hm).le
  · exact (Subobject.pullback_le_pullback_iff_of_epi p _ _).1 (hn m hm).ge

namespace Subobject

/-- Restrict a short complex to a subobject of its middle object, taking the image
in its last object. -/
private noncomputable def restrictedShortComplex (S : ShortComplex C) (A : Subobject S.X₂) :
    ShortComplex C :=
  ShortComplex.mk (pullbackπ S.f A)
    (factorThruImageSubobject (A.arrow ≫ S.g)) (by
      apply (cancel_mono (imageSubobject (A.arrow ≫ S.g)).arrow).1
      simp only [Category.assoc, imageSubobject_arrow_comp, zero_comp]
      rw [← Category.assoc, (isPullback S.f A).w, Category.assoc, S.zero, comp_zero])

private lemma restrictedShortComplex_shortExact {S : ShortComplex C} (hS : S.ShortExact)
    (A : Subobject S.X₂) : (restrictedShortComplex S A).ShortExact := by
  let T := restrictedShortComplex S A
  have : Mono S.f := hS.mono_f
  have : Mono T.f :=
    PullbackCone.mono_fst_of_is_pullback_of_mono (isPullback S.f A).isLimit
  have : Epi T.g := by dsimp [T, restrictedShortComplex]; infer_instance
  have hker : IsLimit (KernelFork.ofι T.f T.zero) := by
    refine KernelFork.IsLimit.ofι _ _
      (fun {W} (u : W ⟶ (A : C))
        (hu : u ≫ factorThruImageSubobject (A.arrow ≫ S.g) =
          (0 : W ⟶ (imageSubobject (A.arrow ≫ S.g) : C))) ↦ ?_) ?_ ?_
    · refine (isPullback S.f A).lift u
        (hS.fIsKernel.lift (KernelFork.ofι (u ≫ A.arrow) ?_)) ?_
      · calc
          (u ≫ A.arrow) ≫ S.g =
              (u ≫ factorThruImageSubobject (A.arrow ≫ S.g)) ≫
                (imageSubobject (A.arrow ≫ S.g)).arrow := by simp [Category.assoc]
          _ = 0 := by rw [hu, zero_comp]
      · symm
        exact Fork.IsLimit.lift_ι hS.fIsKernel
    · intro W u hu
      exact (isPullback S.f A).lift_fst _ _ _
    · intro W u hu b hb
      apply (cancel_mono T.f).1
      rw [hb]
      exact ((isPullback S.f A).lift_fst _ _ _).symm
  exact { exact := T.exact_of_f_is_kernel hker }

-- Equality of intersections and images detects equality for comparable subobjects.
private lemma eq_of_le_of_pullback_eq_of_image_eq {S : ShortComplex C}
    (hS : S.ShortExact) {A B : Subobject S.X₂} (h : A ≤ B)
    (h₁ : (pullback S.f).obj A = (pullback S.f).obj B)
    (h₃ : imageSubobject (A.arrow ≫ S.g) = imageSubobject (B.arrow ≫ S.g)) :
    A = B := by
  let φ : restrictedShortComplex S A ⟶ restrictedShortComplex S B :=
    { τ₁ := (isoOfEq _ _ h₁).hom
      τ₂ := ofLE A B h
      τ₃ := (isoOfEq _ _ h₃).hom
      comm₁₂ := by
        apply (cancel_mono B.arrow).1
        dsimp only [restrictedShortComplex]
        simp only [Category.assoc, isoOfEq_hom, ofLE_arrow, ofLE_arrow_assoc,
          (isPullback S.f B).w, (isPullback S.f A).w]
      comm₂₃ := by
        apply (cancel_mono (imageSubobject (B.arrow ≫ S.g)).arrow).1
        dsimp only [restrictedShortComplex]
        simp only [Category.assoc, imageSubobject_arrow_comp, isoOfEq_hom,
          ofLE_arrow, ofLE_arrow_assoc] }
  have : IsIso φ.τ₁ := (isoOfEq _ _ h₁).isIso_hom
  have : IsIso φ.τ₃ := (isoOfEq _ _ h₃).isIso_hom
  have : IsIso (ofLE A B h) := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ
    (restrictedShortComplex_shortExact hS A) (restrictedShortComplex_shortExact hS B)
  exact eq_of_comm (asIso (ofLE A B h)) (ofLE_arrow h)

end Subobject

/-- Noetherian objects in an abelian category are closed under quotients. -/
instance : (isNoetherianObject (C := C)).IsClosedUnderQuotients where
  prop_of_epi p _ hX := by
    rw [← isNoetherianObject.is_iff] at hX ⊢
    exact isNoetherianObject_of_epi p

/-- Noetherian objects in an abelian category are closed under extensions. -/
instance : (isNoetherianObject (C := C)).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    rw [← isNoetherianObject.is_iff] at h₁ h₃ ⊢
    change IsNoetherianObject S.X₂
    rw [isNoetherianObject_iff_monotone_chain_condition]
    intro F
    obtain ⟨n₁, hn₁⟩ := monotone_chain_condition_of_isNoetherianObject
      ⟨_, (Subobject.pullback S.f).monotone.comp F.2⟩
    let G : ℕ →o Subobject S.X₃ :=
      { toFun := fun n ↦ imageSubobject ((F n).arrow ≫ S.g)
        monotone' := by
          intro n m hnm
          simpa only [Subobject.ofLE_arrow_assoc] using
            imageSubobject_comp_le (Subobject.ofLE (F n) (F m) (F.monotone hnm))
              ((F m).arrow ≫ S.g) }
    obtain ⟨n₃, hn₃⟩ := monotone_chain_condition_of_isNoetherianObject G
    refine ⟨max n₁ n₃, fun m hm ↦ ?_⟩
    apply Subobject.eq_of_le_of_pullback_eq_of_image_eq hS (F.monotone hm)
    · exact (hn₁ _ (le_max_left n₁ n₃)).symm.trans
        (hn₁ _ ((le_max_left n₁ n₃).trans hm))
    · exact (hn₃ _ (le_max_right n₁ n₃)).symm.trans
        (hn₃ _ ((le_max_right n₁ n₃).trans hm))

/-- Noetherian objects in an abelian category form a Serre class. -/
instance : (isNoetherianObject (C := C)).IsSerreClass where

end CategoryTheory
