/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Abelian.Endomorphism
public import HomologicalAlgebra.Abelian.EndomorphismPowers
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Order.Disjoint
public import Mathlib.Order.Filter.AtTopBot.Basic

import Mathlib.Algebra.Group.Commute.Units

/-!
# Fitting decomposition in an abelian category

For an endomorphism of a Noetherian and Artinian object, the kernel and image
subobjects of sufficiently high powers are complementary. For the same powers,
the canonical map `biprod.desc (kernel.ι (f ^ n)) (image.ι (f ^ n))` is an
isomorphism, and `End.imagePowRestriction f n` is invertible. Together with
`End.isNilpotent_kernelPowRestriction` and `End.powRestriction_biprod_desc`,
this gives the nilpotent–invertible decomposition of the endomorphism on one
common positive tail of exponents.

The underlying criterion applies to an endomorphism `g`: write
`e = factorThruImage g` and `m = image.ι g`. If the endomorphism `m ≫ e` of
`image g` is invertible, the canonical map `biprod.desc (kernel.ι g) (image.ι g)`
is an isomorphism. In particular, the kernel and image subobjects are
complementary. Equality of the image subobjects of `g ^ 2` and `g` makes
`m ≫ e` an epimorphism. If `image g` is Noetherian, the Noetherian endomorphism
theorem then gives the decomposition. No chain condition on the ambient object
is needed for this criterion.

The splitting uses image factorization, the public Noetherian endomorphism
theorem, the kernel universal property and Mathlib's
`ShortComplex.Splitting.isoBinaryBiproduct`. Complementarity uses only finite
meets and joins of subobjects. Object and morphism universes are independent.

## References

The eventual complementarity theorem generalizes Mathlib's
`LinearMap.eventually_isCompl_ker_pow_range_pow` in
`Mathlib/RingTheory/Artinian/Module.lean`, authored by Chris Hughes, from modules
over arbitrary rings to objects of an arbitrary abelian category. The proof here
uses categorical image factorization and splitting rather than the module's
elementwise argument.
-/

@[expose] public section

universe v u

noncomputable section

namespace CategoryTheory

open Category Limits Preadditive

variable {C : Type u} [Category.{v} C]

namespace Subobject

/-- If the copairing of two monomorphisms is an isomorphism, their subobjects
are complementary. -/
theorem isCompl_mk_of_isIso_biprod_desc [HasZeroMorphisms C] [HasZeroObject C]
    [HasPullbacks C] [HasImages C] [HasBinaryCoproducts C]
    {A B X : C} [HasBinaryBiproduct A B] (i : A ⟶ X) (j : B ⟶ X)
    [Mono i] [Mono j] [IsIso (biprod.desc i j)] : IsCompl (mk i) (mk j) := by
  refine IsCompl.of_eq ?_ ?_
  · let P : Subobject X := mk i ⊓ mk j
    let a : (P : C) ⟶ A := ofLEMk P i (Subobject.inf_le_left _ _)
    let b : (P : C) ⟶ B := ofLEMk P j (Subobject.inf_le_right _ _)
    have ha : a ≫ i = P.arrow := ofLEMk_comp (Subobject.inf_le_left _ _)
    have hb : b ≫ j = P.arrow := ofLEMk_comp (Subobject.inf_le_right _ _)
    have hab : a ≫ (biprod.inl : A ⟶ A ⊞ B) = b ≫ biprod.inr := by
      apply (cancel_mono (biprod.desc i j)).1
      simp only [Category.assoc, biprod.inl_desc, biprod.inr_desc, ha, hb]
    have ha0 : a = 0 := by
      simpa only [Category.assoc, biprod.inl_fst, biprod.inr_fst,
        Category.comp_id, comp_zero] using
        congrArg (fun t : (P : C) ⟶ A ⊞ B => t ≫ biprod.fst) hab
    have hP : P.arrow = 0 := by rw [← ha, ha0, zero_comp]
    simpa only [mk_arrow] using (mk_eq_bot_iff_zero (f := P.arrow)).2 hP
  · let P : Subobject X := mk i ⊔ mk j
    let a : A ⟶ (P : C) := ofMkLE i P le_sup_left
    let b : B ⟶ (P : C) := ofMkLE j P le_sup_right
    have hab : biprod.desc a b ≫ P.arrow = biprod.desc i j := by
      apply biprod.hom_ext' <;> simp [a, b]
    have htop : imageSubobject (biprod.desc i j) = ⊤ := by
      rw [imageSubobject_mono, mk_eq_top_of_isIso]
    apply top_unique
    rw [← htop]
    exact imageSubobject_le (biprod.desc i j) (biprod.desc a b) hab

end Subobject

section Splitting

variable [Preadditive C] {X : C} (g : End X) [HasKernel g] [HasImage g]
    [HasBinaryBiproduct (kernel g) (image g)]

/-- If the endomorphism induced by an endomorphism on its image is invertible,
the copairing of its kernel and image inclusions is an isomorphism. -/
theorem isIso_biprod_desc_kernel_ι_image_ι_of_isIso
    [IsIso (image.ι g ≫ factorThruImage g)] :
    IsIso (biprod.desc (kernel.ι g) (image.ι g)) := by
  let h : image g ⟶ image g := image.ι g ≫ factorThruImage g
  let r : X ⟶ image g := factorThruImage g ≫ inv h
  have hmr : image.ι g ≫ r = 𝟙 (image g) := by
    dsimp only [r]
    rw [← Category.assoc]
    exact IsIso.hom_inv_id h
  have hke : kernel.ι g ≫ factorThruImage g = 0 := by
    apply (cancel_mono (image.ι g)).1
    simp only [Category.assoc, image.fac, kernel.condition, zero_comp]
  have hkr : kernel.ι g ≫ r = 0 := by
    simp only [r, ← Category.assoc, hke, zero_comp]
  have hrg : (r ≫ image.ι g) ≫ g = g := by
    calc
      (r ≫ image.ι g) ≫ g = r ≫ h ≫ image.ι g := by
        simp only [h, Category.assoc, image.fac]
      _ = g := by simp [r, Category.assoc]
  have hq : (𝟙 X - r ≫ image.ι g) ≫ g = 0 := by
    rw [sub_comp, Category.id_comp, hrg, sub_self]
  let p : X ⟶ kernel g := kernel.lift g (𝟙 X - r ≫ image.ι g) hq
  have hp : p ≫ kernel.ι g = 𝟙 X - r ≫ image.ι g := kernel.lift_ι _ _ _
  have hkp : kernel.ι g ≫ p = 𝟙 (kernel g) := by
    apply (cancel_mono (kernel.ι g)).1
    rw [Category.assoc, hp, comp_sub, Category.comp_id, ← Category.assoc,
      hkr, zero_comp, sub_zero, Category.id_comp]
  have htotal : p ≫ kernel.ι g + r ≫ image.ι g = 𝟙 X := by
    rw [hp, sub_add_cancel]
  let S : ShortComplex C := ShortComplex.mk (kernel.ι g) r hkr
  let s : S.Splitting :=
    { r := p
      s := image.ι g
      f_r := hkp
      s_g := hmr
      id := htotal }
  exact s.isoBinaryBiproduct.isIso_inv

end Splitting

section Complement

variable [Abelian C] {X : C} (g : End X)

/-- An invertible endomorphism on the image gives complementary kernel and image
subobjects of the original object. -/
theorem isCompl_kernelSubobject_imageSubobject_of_isIso
    [IsIso (image.ι g ≫ factorThruImage g)] :
    IsCompl (kernelSubobject g) (imageSubobject g) := by
  let := isIso_biprod_desc_kernel_ι_image_ι_of_isIso g
  exact Subobject.isCompl_mk_of_isIso_biprod_desc (kernel.ι g) (image.ι g)

end Complement

section StableImage

variable {X : C} (g : End X) [HasImage g] [HasImage (g ^ 2)]

/-- Equality of the image subobjects of `g ^ 2` and `g` makes the induced
endomorphism of the image epimorphic, provided the image factorization of
`g ^ 2` has an epimorphic first map. -/
theorem epi_image_ι_comp_factorThruImage_of_imageSubobject_sq_eq
    [Epi (factorThruImage (g ^ 2))]
    (himage : imageSubobject (g ^ 2) = imageSubobject g) :
    Epi (image.ι g ≫ factorThruImage g) := by
  let t : image (g ^ 2) ≅ image g :=
    Subobject.isoOfMkEqMk (image.ι (g ^ 2)) (image.ι g) himage
  have ht : t.hom ≫ image.ι g = image.ι (g ^ 2) :=
    Subobject.ofMkLEMk_comp himage.le
  have hfac : factorThruImage g ≫ (image.ι g ≫ factorThruImage g) =
      factorThruImage (g ^ 2) ≫ t.hom := by
    apply (cancel_mono (image.ι g)).1
    calc
      (factorThruImage g ≫ (image.ι g ≫ factorThruImage g)) ≫ image.ι g =
          g ≫ g := by simp only [Category.assoc, image.fac, image.fac_assoc]
      _ = g ^ 2 := by simp only [pow_two, End.mul_def]
      _ = (factorThruImage (g ^ 2) ≫ t.hom) ≫ image.ι g := by
        rw [Category.assoc, ht, image.fac]
  exact epi_of_epi_fac hfac

end StableImage

section NoetherianImage

variable [Abelian C] {X : C} (g : End X) [IsNoetherianObject (image g)]

/-- If `image g` is Noetherian and the images of `g ^ 2` and `g` agree,
the induced endomorphism of `image g` is invertible. -/
theorem isIso_image_ι_comp_factorThruImage_of_imageSubobject_sq_eq
    (himage : imageSubobject (g ^ 2) = imageSubobject g) :
    IsIso (image.ι g ≫ factorThruImage g) := by
  let := epi_image_ι_comp_factorThruImage_of_imageSubobject_sq_eq g himage
  exact isIso_of_epi_of_isNoetherianObject (image.ι g ≫ factorThruImage g)

/-- A stable image with a Noetherian image object gives the canonical binary
biproduct decomposition into kernel and image. -/
theorem isIso_biprod_desc_kernel_ι_image_ι_of_imageSubobject_sq_eq
    (himage : imageSubobject (g ^ 2) = imageSubobject g) :
    IsIso (biprod.desc (kernel.ι g) (image.ι g)) := by
  let := isIso_image_ι_comp_factorThruImage_of_imageSubobject_sq_eq g himage
  exact isIso_biprod_desc_kernel_ι_image_ι_of_isIso g

/-- A stable image with a Noetherian image object is complementary to the kernel
as a subobject of the original object. -/
theorem isCompl_kernelSubobject_imageSubobject_of_imageSubobject_sq_eq
    (himage : imageSubobject (g ^ 2) = imageSubobject g) :
    IsCompl (kernelSubobject g) (imageSubobject g) := by
  let := isIso_image_ι_comp_factorThruImage_of_imageSubobject_sq_eq g himage
  exact isCompl_kernelSubobject_imageSubobject_of_isIso g

end NoetherianImage

section Fitting

variable [Abelian C] {X : C} [IsNoetherianObject X] [IsArtinianObject X] (f : End X)

private theorem eventually_pos_and_isIso_image_ι_comp_factorThruImage_pow :
    ∀ᶠ n : ℕ in Filter.atTop,
      0 < n ∧ IsIso (image.ι (f ^ n) ≫ factorThruImage (f ^ n)) := by
  obtain ⟨N, hN⟩ := exists_stable_kernelSubobject_imageSubobject_pow f
  refine Filter.eventually_atTop.2 ⟨N + 1, fun n hn ↦ ?_⟩
  have hNn : N ≤ n := le_trans (Nat.le_succ N) hn
  have himage : imageSubobject ((f ^ n) ^ 2) = imageSubobject (f ^ n) := by
    calc
      imageSubobject ((f ^ n) ^ 2) = imageSubobject (f ^ (n + n)) := by
        rw [pow_two, pow_add]
      _ = imageSubobject (f ^ N) :=
        (hN (n + n) (le_trans hNn (Nat.le_add_right n n))).2.symm
      _ = imageSubobject (f ^ n) := (hN n hNn).2
  let : IsNoetherianObject (image (f ^ n)) :=
    isNoetherianObject_of_mono (image.ι (f ^ n))
  exact ⟨lt_of_lt_of_le (Nat.succ_pos N) hn,
    isIso_image_ι_comp_factorThruImage_of_imageSubobject_sq_eq (f ^ n) himage⟩

/-- For an endomorphism of a Noetherian and Artinian object in an abelian category,
the kernel and image subobjects of sufficiently high powers are complementary.

This generalizes `LinearMap.eventually_isCompl_ker_pow_range_pow` from modules
over a ring to objects of an abelian category. -/
theorem eventually_isCompl_kernelSubobject_pow_imageSubobject_pow :
    ∀ᶠ n : ℕ in Filter.atTop,
      IsCompl (kernelSubobject (f ^ n)) (imageSubobject (f ^ n)) := by
  apply (eventually_pos_and_isIso_image_ι_comp_factorThruImage_pow f).mono
  intro n hn
  let := hn.2
  exact isCompl_kernelSubobject_imageSubobject_of_isIso (f ^ n)

/-- For sufficiently high powers of an endomorphism of a Noetherian and Artinian
object, the copairing of the chosen kernel and image inclusions is an isomorphism. -/
theorem eventually_isIso_biprod_desc_kernel_ι_image_ι_pow :
    ∀ᶠ n : ℕ in Filter.atTop,
      IsIso (biprod.desc (kernel.ι (f ^ n)) (image.ι (f ^ n))) := by
  apply (eventually_pos_and_isIso_image_ι_comp_factorThruImage_pow f).mono
  intro n hn
  let := hn.2
  exact isIso_biprod_desc_kernel_ι_image_ι_of_isIso (f ^ n)

namespace End

/-- The canonical restriction of an endomorphism of a Noetherian and Artinian
object to the image of a sufficiently high power is an isomorphism. -/
theorem eventually_isIso_imagePowRestriction :
    ∀ᶠ n : ℕ in Filter.atTop, IsIso (imagePowRestriction f n) := by
  apply (eventually_pos_and_isIso_image_ι_comp_factorThruImage_pow f).mono
  intro n hn
  have hpow : IsIso (imagePowRestriction f n ^ n) := by
    rw [imagePowRestriction_pow_self]
    exact hn.2
  exact (isUnit_iff_isIso _).1 <|
    (isUnit_pow_iff (Nat.ne_of_gt hn.1)).1 ((isUnit_iff_isIso _).2 hpow)

end End

end Fitting

end CategoryTheory
