/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Johan Commelin, Kim Morrison
-/
/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kim Morrison
-/
/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Jack McKoen
-/
/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.RegularCategory.Basic
public import Mathlib.Order.ModularLattice
public import HomologicalAlgebra.Abelian.NoetherianObject

/-!
# Subobject correspondence and modularity in abelian categories

Pullback along an epimorphism identifies subobjects of its codomain with subobjects of its
domain containing its kernel. In particular, subobjects of a cokernel correspond to the upper
interval above the subobject being quotiented out. These correspondences use the canonical
`CategoryTheory.Subobject` quotient, its pullback functor, and its direct-image functor.

## Main definitions and results

* `CategoryTheory.Abelian.Subobject.epiOrderIso`: correspondence for an epimorphism.
* `CategoryTheory.Abelian.Subobject.cokernelOrderIso`: correspondence for a cokernel.
* The lattice of subobjects of an object in an abelian category is modular.

## References

The statements and construction data follow Jack McKoen's Mathlib formalizations:

* Mathlib, revision `76dc24934373394902ae98311c2b0f3b9e2b77a5`,
  `Mathlib/CategoryTheory/Abelian/Subobject.lean`, by Markus Himmel and Jack McKoen:
  <https://github.com/leanprover-community/mathlib4/blob/76dc24934373394902ae98311c2b0f3b9e2b77a5/Mathlib/CategoryTheory/Abelian/Subobject.lean>.
* Mathlib, revision `5c12595541f246a31351ed23f0815dc008ae9461`,
  `Mathlib/CategoryTheory/Subobject/Limits.lean`, by Bhavik Mehta and Kim Morrison;
  `Mathlib/CategoryTheory/Abelian/Basic.lean`, by Markus Himmel, Johan Commelin and Kim Morrison;
  and `Mathlib/CategoryTheory/Abelian/JordanHolder.lean`, with modularity by Jack McKoen:
  <https://github.com/leanprover-community/mathlib4/tree/5c12595541f246a31351ed23f0815dc008ae9461/Mathlib/CategoryTheory>.
* N. Popescu, *Abelian Categories with Applications to Rings and Modules* (1973), as cited by
  Mathlib's subobject correspondence development.

## Implementation notes

The order correspondences use the `MonoOver` direct-image/pullback adjunction on the
canonical `CategoryTheory.Subobject` quotient. The modularity proof combines the cokernel
correspondence with the imported Frobenius reciprocity theorem. Inclusion reflection along
epimorphisms and the generic `MonoOver` counit comparison API are also imported. No chain
condition or smallness assumption is required.
-/

@[expose] public section

universe v u

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Subobject

variable {C : Type u} [Category.{v} C]

/-- Pullback of the kernel subobject is the kernel subobject of the composite.
This is the generic kernel-pullback statement in Mathlib's subobject limits development. -/
lemma pullback_kernelSubobject [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y) [HasKernel f]
    {W : C} (h : W ⟶ X) [HasPullbacks C] [HasKernel (h ≫ f)] :
    (CategoryTheory.Subobject.pullback h).obj (kernelSubobject f) =
      kernelSubobject (h ≫ f) := by
  simpa only [kernelSubobject, comp_zero] using pullback_equalizer f 0 h

end CategoryTheory.Subobject

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An abelian category is regular, as in Mathlib's abelian-category development. -/
instance (priority := 100) abelianRegular : Regular C := by
  exact
    { hasCoequalizer_of_isKernelPair := inferInstance
      regularEpiIsStableUnderBaseChange := .mk' (fun _ _ _ _ g _ hg ↦ by
        rw [MorphismProperty.regularEpi_iff] at hg ⊢
        exact IsRegularEpiCategory.regularEpiOfEpi _) }

end CategoryTheory.Abelian

namespace CategoryTheory.MonoOver

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The direct-image/pullback counit over an epimorphism in an abelian category is invertible.
This is the counit instance in Mathlib's subobject correspondence development. -/
instance {X Y : C} (f : X ⟶ Y) [Epi f] (Y' : MonoOver Y) :
    IsIso ((existsPullbackAdj f).counit.app Y') := by
  let : Epi ((existsPullbackAdj f).counit.app Y').hom.left :=
    epi_of_epi_fac (factorThruImage_comp_existsPullbackAdj_counit_app_hom_left f Y')
  let : Mono ((existsPullbackAdj f).counit.app Y').hom.left := mono_of_mono_fac (MonoOver.w _)
  rw [isIso_iff_isIso_hom_left]
  apply isIso_of_mono_of_epi

end CategoryTheory.MonoOver

namespace CategoryTheory.Abelian.Subobject

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The categorical image subobject is the kernel subobject of the cokernel projection. -/
lemma imageSubobject_eq_kernelSubobject {X Y : C} (f : X ⟶ Y) :
    imageSubobject f = kernelSubobject (cokernel.π f) := by
  exact
    (CategoryTheory.Subobject.mk_eq_mk_of_comm (kernel.ι (cokernel.π f)) (Limits.image.ι f)
      (imageIsoImage f) (imageIsoImage_hom_comp_image_ι f)).symm

/-- Pullback of a subobject is the kernel subobject of the composite with its cokernel
projection. -/
lemma pullback_eq_kernelSubobject {X Y : C} (f : X ⟶ Y) (Y' : Subobject Y) :
    (CategoryTheory.Subobject.pullback f).obj Y' =
      kernelSubobject (f ≫ cokernel.π Y'.arrow) := by
  rw [← CategoryTheory.Subobject.pullback_kernelSubobject, ← imageSubobject_eq_kernelSubobject,
    imageSubobject_mono, CategoryTheory.Subobject.mk_arrow]

/-- Direct image after pullback along an epimorphism is the original subobject. -/
theorem exists_pullback_eq_self_of_epi {X Y : C} (f : X ⟶ Y) [Epi f]
    (Y' : Subobject Y) :
    (CategoryTheory.Subobject.«exists» f).obj
      ((CategoryTheory.Subobject.pullback f).obj Y') = Y' := by
  exact Quotient.inductionOn' Y' fun _ ↦
    Quotient.sound ⟨asIso ((MonoOver.existsPullbackAdj f).counit.app _)⟩

/-- Pullback after direct image along an epimorphism fixes subobjects containing its kernel. -/
lemma pullback_exists_eq_self_of_epi {X Y : C} (f : X ⟶ Y) [Epi f]
    (X' : Subobject X) (h : kernelSubobject f ≤ X') :
    (CategoryTheory.Subobject.pullback f).obj
      ((CategoryTheory.Subobject.«exists» f).obj X') = X' := by
  let d := epiDesc f (cokernel.π X'.arrow) (by
    rw [← kernelSubobject_arrow' f, ← CategoryTheory.Subobject.ofLE_arrow h]
    simp only [Category.assoc, cokernel.condition, comp_zero])
  have hX' : (CategoryTheory.Subobject.pullback f).obj (kernelSubobject d) = X' := by
    rw [CategoryTheory.Subobject.pullback_kernelSubobject, comp_epiDesc,
      ← imageSubobject_eq_kernelSubobject, imageSubobject_mono, CategoryTheory.Subobject.mk_arrow]
  rw [← hX', exists_pullback_eq_self_of_epi]

/-- Subobjects of the codomain of an epimorphism correspond, by pullback, to subobjects of
its domain containing its kernel. The inverse takes direct image. This is Mathlib's
`epiOrderIso` construction. -/
def epiOrderIso {X Y : C} (f : X ⟶ Y) [Epi f] :
    Subobject Y ≃o Set.Ici (kernelSubobject f) where
  toFun p := ⟨(CategoryTheory.Subobject.pullback f).obj p, by
    rw [pullback_eq_kernelSubobject]
    exact kernelSubobject_comp_le f _⟩
  invFun q := (CategoryTheory.Subobject.«exists» f).obj q.1
  left_inv := by
    intro p
    exact exists_pullback_eq_self_of_epi f p
  right_inv := by
    rintro ⟨q, hq⟩
    exact Subtype.ext (pullback_exists_eq_self_of_epi f q hq)
  map_rel_iff' {p q} :=
    CategoryTheory.Subobject.pullback_le_pullback_iff_of_epi f p q

/-- The underlying subobject of `epiOrderIso f p` is the pullback of `p` along `f`. -/
lemma epiOrderIso_apply {X Y : C} (f : X ⟶ Y) [Epi f] (p : Subobject Y) :
    (epiOrderIso f p : Subobject X) = (CategoryTheory.Subobject.pullback f).obj p := by
  rfl

/-- The inverse of `epiOrderIso f` takes the direct image of the underlying subobject. -/
lemma epiOrderIso_symm_apply {X Y : C} (f : X ⟶ Y) [Epi f]
    (q : Set.Ici (kernelSubobject f)) :
    (epiOrderIso f).symm q = (CategoryTheory.Subobject.«exists» f).obj q.1 := by
  rfl

/-- Subobjects of the cokernel of a subobject correspond, by pullback of the cokernel
projection, to subobjects containing that subobject. The inverse takes direct image.
This is Mathlib's `cokernelOrderIso` construction. -/
def cokernelOrderIso {X : C} (Y : Subobject X) :
    Subobject (cokernel Y.arrow) ≃o Set.Ici Y :=
  (epiOrderIso (cokernel.π Y.arrow)).trans (Set.orderIsoOfEq _ _ (by
    rw [← imageSubobject_eq_kernelSubobject, imageSubobject_mono,
      CategoryTheory.Subobject.mk_arrow]))

/-- The underlying subobject of `cokernelOrderIso Y p` is the pullback of `p` along the
cokernel projection. -/
lemma cokernelOrderIso_apply {X : C} (Y : Subobject X)
    (p : Subobject (cokernel Y.arrow)) :
    (cokernelOrderIso Y p : Subobject X) =
      (CategoryTheory.Subobject.pullback (cokernel.π Y.arrow)).obj p := by
  rfl

/-- The inverse of `cokernelOrderIso Y` takes direct image along the cokernel projection. -/
lemma cokernelOrderIso_symm_apply {X : C} (Y : Subobject X) (q : Set.Ici Y) :
    (cokernelOrderIso Y).symm q =
      (CategoryTheory.Subobject.«exists» (cokernel.π Y.arrow)).obj q.1 := by
  rfl

end CategoryTheory.Abelian.Subobject

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

open Subobject Abelian.Subobject in
/-- The lattice of subobjects of an object in an abelian category is modular.
Statement from Jack McKoen's Mathlib formalization in `Abelian/JordanHolder.lean`
(see the module references). -/
instance (A : C) : IsModularLattice (CategoryTheory.Subobject A) where
  sup_inf_le_assoc_of_le := by
    intro X Y Z hXZ
    suffices (⟨(X ⊔ Y) ⊓ Z, le_inf le_sup_left hXZ⟩ : Set.Ici X) =
      ⟨X ⊔ Y ⊓ Z, (le_sup_left : X ≤ X ⊔ (Y ⊓ Z))⟩ from
      (congrArg Subtype.val this).le
    apply (cokernelOrderIso X).symm.injective
    simp only [cokernelOrderIso_symm_apply]
    have hZ : (Subobject.pullback (cokernel.π X.arrow)).obj
        ((«exists» (cokernel.π X.arrow)).obj Z) = Z := by
      simpa only [cokernelOrderIso_apply, cokernelOrderIso_symm_apply] using
        congrArg Subtype.val ((cokernelOrderIso X).apply_symm_apply ⟨Z, hXZ⟩)
    have hqX : («exists» (cokernel.π X.arrow)).obj X = ⊥ := by
      simpa only [cokernelOrderIso_symm_apply, Set.Ici.coe_bot] using
        (cokernelOrderIso X).symm.map_bot
    calc
      («exists» (cokernel.π X.arrow)).obj ((X ⊔ Y) ⊓ Z) =
          («exists» (cokernel.π X.arrow)).obj (X ⊔ Y) ⊓
            («exists» (cokernel.π X.arrow)).obj Z := by
        rw [← Regular.exists_inf_pullback_eq_exists_inf, hZ]
      _ = («exists» (cokernel.π X.arrow)).obj Y ⊓
          («exists» (cokernel.π X.arrow)).obj Z := by
        rw [(existsPullbackAdj (cokernel.π X.arrow)).gc.l_sup, hqX, bot_sup_eq]
      _ = («exists» (cokernel.π X.arrow)).obj (Y ⊓ Z) := by
        rw [← Regular.exists_inf_pullback_eq_exists_inf, hZ]
      _ = («exists» (cokernel.π X.arrow)).obj (X ⊔ Y ⊓ Z) := by
        rw [(existsPullbackAdj (cokernel.π X.arrow)).gc.l_sup, hqX, bot_sup_eq]

end CategoryTheory
