/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Subobject.ArtinianObject
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.Subobject.NoetherianObject
public import Mathlib.Order.Monotone.Basic

/-!
# Kernels and images of powers of an endomorphism

The kernel subobjects of powers form an ascending chain, and the image subobjects
form a descending chain. The stock Noetherian and Artinian chain conditions give
a common stabilization threshold.

`kernelPowRestriction` and `imagePowRestriction` abbreviate the stock kernel and
image maps induced by the square whose two sides are the endomorphism. Their
inclusion equations characterize them uniquely. Powers satisfy the corresponding
inclusion equations and agree with the stock maps on the powered squares. The
kernel restriction has its specified power zero, without a chain condition.

The restrictions intertwine the endomorphism with the block endomorphism of the
binary biproduct of the kernel and image. An arbitrary intertwiner induces a
natural square for the copairings of the power-kernel and power-image inclusions.
No complementarity or invertibility is asserted here.

An intertwiner from a nilpotent endomorphism to a monomorphic endomorphism is
zero. Dually, an intertwiner from an epimorphic endomorphism to a nilpotent
endomorphism is zero. These statements require only zero morphisms.

Only the relevant kernels, images, image maps and zero morphisms are required;
none of the lemmas requires an abelian category. Object and morphism universes
are independent.

## References

Mathlib's `CategoryTheory.Endomorphism` gives the endomorphism monoid and its
composition convention. `CategoryTheory.Preadditive.Basic` supplies the
endomorphism ring in a preadditive category; the zero used here agrees with
the underlying zero morphism without requiring additivity.
-/

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The zero endomorphism is the zero morphism, without an additivity assumption. -/
instance End.instZero [Limits.HasZeroMorphisms C] (X : C) : Zero (End X) :=
  inferInstanceAs (Zero (X ⟶ X))

/-- The zero of the endomorphism type is its underlying zero morphism. -/
theorem End.zero_def [Limits.HasZeroMorphisms C] {X : C} :
    (0 : End X) = (0 : X ⟶ X) := rfl

/-- An intertwining morphism also intertwines every pair of corresponding powers. -/
@[reassoc]
theorem End.pow_comp_eq_comp_pow {X Y : C} (a : End X) (b : End Y)
    (i : X ⟶ Y) (h : a ≫ i = i ≫ b) (n : ℕ) :
    (a ^ n) ≫ i = i ≫ (b ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      (a ^ (n + 1)) ≫ i = a ≫ ((a ^ n) ≫ i) := by
        simp only [pow_succ, End.mul_def, Category.assoc]
      _ = a ≫ (i ≫ (b ^ n)) := by rw [ih]
      _ = (a ≫ i) ≫ (b ^ n) := (Category.assoc _ _ _).symm
      _ = (i ≫ b) ≫ (b ^ n) := by rw [h]
      _ = i ≫ (b ^ (n + 1)) := by
        simp only [pow_succ, End.mul_def, Category.assoc]

open Limits

namespace End

variable {X : C}

private theorem mono_pow (f : End X) [Mono f] (n : ℕ) : Mono (f ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, End.one_def] using (inferInstance : Mono (𝟙 X))
  | succ n ih =>
    have := ih
    simpa only [pow_succ, End.mul_def] using (inferInstance : Mono (f ≫ (f ^ n)))

private theorem epi_pow (f : End X) [Epi f] (n : ℕ) : Epi (f ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, End.one_def] using (inferInstance : Epi (𝟙 X))
  | succ n ih =>
    have := ih
    simpa only [pow_succ, End.mul_def] using (inferInstance : Epi (f ≫ (f ^ n)))

/-- An intertwiner from a nilpotent endomorphism to a monomorphic endomorphism
is zero. -/
theorem eq_zero_of_isNilpotent_of_mono [HasZeroMorphisms C] {Y : C}
    (f : End X) (g : End Y) (p : X ⟶ Y) (h : f ≫ p = p ≫ g)
    [Mono g] (hf : IsNilpotent f) : p = 0 := by
  obtain ⟨n, hn⟩ := hf
  have := mono_pow g n
  apply (cancel_mono (g ^ n)).1
  simpa only [hn, zero_comp] using (pow_comp_eq_comp_pow f g p h n).symm

/-- An intertwiner from an epimorphic endomorphism to a nilpotent endomorphism
is zero. -/
theorem eq_zero_of_epi_of_isNilpotent [HasZeroMorphisms C] {Y : C}
    (f : End X) (g : End Y) (p : X ⟶ Y) (h : f ≫ p = p ≫ g)
    [Epi f] (hg : IsNilpotent g) : p = 0 := by
  obtain ⟨n, hn⟩ := hg
  have := epi_pow f n
  apply (cancel_epi (f ^ n)).1
  simpa only [hn, comp_zero] using pow_comp_eq_comp_pow f g p h n

/-- The maps on kernels and images induced by an intertwiner make the power
kernel/image copairings natural. Only the displayed kernels, images, image map
and binary biproducts are required. -/
@[reassoc]
theorem pow_biprod_desc_naturality [HasZeroMorphisms C] {Y : C}
    (f : End X) (g : End Y) (p : X ⟶ Y) (h : f ≫ p = p ≫ g) (n : ℕ)
    [HasKernel (f ^ n)] [HasKernel (g ^ n)]
    [HasImage (f ^ n)] [HasImage (g ^ n)]
    [HasImageMap (Arrow.homMk' (f := f ^ n) (g := g ^ n) p p
      (pow_comp_eq_comp_pow f g p h n).symm)]
    [HasBinaryBiproduct (kernel (f ^ n)) (image (f ^ n))]
    [HasBinaryBiproduct (kernel (g ^ n)) (image (g ^ n))] :
    biprod.map (W := kernel (f ^ n)) (X := image (f ^ n))
        (Y := kernel (g ^ n)) (Z := image (g ^ n))
        (kernel.map (f ^ n) (g ^ n) p p (pow_comp_eq_comp_pow f g p h n))
        (image.map (Arrow.homMk' (f := f ^ n) (g := g ^ n) p p
          (pow_comp_eq_comp_pow f g p h n).symm)) ≫
      biprod.desc (kernel.ι (g ^ n)) (image.ι (g ^ n)) =
    biprod.desc (kernel.ι (f ^ n)) (image.ι (f ^ n)) ≫ p := by
  apply biprod.hom_ext'
  · simp only [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc,
      kernel.map, kernel.lift_ι]
  · simp only [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc,
      image.map_homMk'_ι]

section KernelRestriction

variable [HasZeroMorphisms C] (f : End X) (n : ℕ) [HasKernel (f ^ n)]

/-- The restriction of `f` to the kernel of `f ^ n`, constructed by `kernel.map`. -/
noncomputable def kernelPowRestriction : End (kernel (f ^ n)) :=
  kernel.map (f ^ n) (f ^ n) f f
    (by simpa only [End.mul_def] using (pow_mul_comm' f n).symm)

/-- The kernel restriction commutes with the kernel inclusion. -/
@[reassoc (attr := simp)]
theorem kernelPowRestriction_ι :
    kernelPowRestriction f n ≫ kernel.ι (f ^ n) = kernel.ι (f ^ n) ≫ f := by
  simp [kernelPowRestriction, kernel.map]

/-- The inclusion equation uniquely characterizes the kernel restriction. -/
theorem eq_kernelPowRestriction_iff (a : End (kernel (f ^ n))) :
    a = kernelPowRestriction f n ↔ a ≫ kernel.ι (f ^ n) = kernel.ι (f ^ n) ≫ f := by
  constructor
  · rintro rfl
    exact kernelPowRestriction_ι f n
  · intro h
    apply (cancel_mono (kernel.ι (f ^ n))).1
    simpa only [kernelPowRestriction_ι] using h

/-- Powers of the kernel restriction commute with the kernel inclusion. -/
@[reassoc (attr := simp)]
theorem kernelPowRestriction_pow_ι (m : ℕ) :
    (kernelPowRestriction f n ^ m) ≫ kernel.ι (f ^ n) = kernel.ι (f ^ n) ≫ (f ^ m) :=
  End.pow_comp_eq_comp_pow _ _ _ (kernelPowRestriction_ι f n) m

/-- Powers of the kernel restriction are the stock kernel maps on the powered square. -/
theorem kernelPowRestriction_pow (m : ℕ) :
    kernelPowRestriction f n ^ m =
      kernel.map (f ^ n) (f ^ n) (f ^ m) (f ^ m)
        (by simpa only [End.mul_def] using pow_mul_comm f m n) := by
  apply (cancel_mono (kernel.ι (f ^ n))).1
  simp only [kernelPowRestriction_pow_ι, kernel.map, kernel.lift_ι]

/-- The restriction of `f` to the kernel of `f ^ n` has its `n`th power zero. -/
@[simp]
theorem kernelPowRestriction_pow_eq_zero : kernelPowRestriction f n ^ n = 0 := by
  apply (cancel_mono (kernel.ι (f ^ n))).1
  simp only [kernelPowRestriction_pow_ι, kernel.condition, zero_comp]

/-- The restriction to the kernel of a power is nilpotent. -/
theorem isNilpotent_kernelPowRestriction : IsNilpotent (kernelPowRestriction f n) :=
  ⟨n, kernelPowRestriction_pow_eq_zero f n⟩

end KernelRestriction

section ImageRestriction

variable [HasImages C] [HasImageMaps C] (f : End X) (n : ℕ)

/-- The restriction of `f` to the image of `f ^ n`, constructed by `image.map`. -/
noncomputable def imagePowRestriction : End (image (f ^ n)) :=
  image.map (Arrow.homMk' (f := f ^ n) (g := f ^ n) f f
    (by simpa only [End.mul_def] using pow_mul_comm' f n))

/-- The image restriction commutes with the image inclusion. -/
@[reassoc (attr := simp)]
theorem imagePowRestriction_ι :
    imagePowRestriction f n ≫ image.ι (f ^ n) = image.ι (f ^ n) ≫ f := by
  dsimp only [imagePowRestriction]
  exact image.map_ι _

/-- The image factorization also intertwines `f` and its image restriction. -/
@[reassoc (attr := simp)]
theorem factorThruImage_imagePowRestriction :
    factorThruImage (f ^ n) ≫ imagePowRestriction f n = f ≫ factorThruImage (f ^ n) := by
  dsimp only [imagePowRestriction]
  exact image.factor_map (Arrow.homMk' (f := f ^ n) (g := f ^ n) f f
    (by simpa only [End.mul_def] using pow_mul_comm' f n))

/-- The inclusion equation uniquely characterizes the image restriction. -/
theorem eq_imagePowRestriction_iff (b : End (image (f ^ n))) :
    b = imagePowRestriction f n ↔ b ≫ image.ι (f ^ n) = image.ι (f ^ n) ≫ f := by
  constructor
  · rintro rfl
    exact imagePowRestriction_ι f n
  · intro h
    apply (cancel_mono (image.ι (f ^ n))).1
    simpa only [imagePowRestriction_ι] using h

/-- Powers of the image restriction commute with the image inclusion. -/
@[reassoc (attr := simp)]
theorem imagePowRestriction_pow_ι (m : ℕ) :
    (imagePowRestriction f n ^ m) ≫ image.ι (f ^ n) = image.ι (f ^ n) ≫ (f ^ m) :=
  End.pow_comp_eq_comp_pow _ _ _ (imagePowRestriction_ι f n) m

/-- Powers of the image restriction are the stock image maps on the powered square. -/
theorem imagePowRestriction_pow (m : ℕ) :
    imagePowRestriction f n ^ m =
      image.map (Arrow.homMk' (f := f ^ n) (g := f ^ n) (f ^ m) (f ^ m)
        (by simpa only [End.mul_def] using pow_mul_comm f n m)) := by
  apply (cancel_mono (image.ι (f ^ n))).1
  simp only [imagePowRestriction_pow_ι, image.map_homMk'_ι]

/-- The `n`th power of the image restriction is the image inclusion followed by
its factorization map. -/
theorem imagePowRestriction_pow_self :
    imagePowRestriction f n ^ n = image.ι (f ^ n) ≫ factorThruImage (f ^ n) := by
  apply (cancel_mono (image.ι (f ^ n))).1
  simp only [imagePowRestriction_pow_ι, Category.assoc, image.fac]

end ImageRestriction

/-- The block endomorphism of kernel and image intertwines the sum of the inclusions
with the original endomorphism. -/
@[reassoc]
theorem powRestriction_biprod_desc [HasZeroMorphisms C] [HasImages C] [HasImageMaps C]
    (f : End X) (n : ℕ) [HasKernel (f ^ n)]
    [HasBinaryBiproduct (kernel (f ^ n)) (image (f ^ n))] :
    biprod.map (kernelPowRestriction f n) (imagePowRestriction f n) ≫
        biprod.desc (kernel.ι (f ^ n)) (image.ι (f ^ n)) =
      biprod.desc (kernel.ι (f ^ n)) (image.ι (f ^ n)) ≫ f := by
  simpa only [kernelPowRestriction, imagePowRestriction] using
    pow_biprod_desc_naturality f f f rfl n

end End

namespace Limits

variable {X : C}

section PowerChains

/-- Kernel subobjects of powers form an ascending chain. -/
theorem monotone_kernelSubobject_pow [HasZeroMorphisms C] [HasKernels C]
    (f : End X) : Monotone (fun n : ℕ ↦ kernelSubobject (f ^ n)) := by
  apply monotone_nat_of_le_succ
  intro n
  simpa only [pow_succ', End.mul_def] using kernelSubobject_comp_le (f ^ n) f

/-- Image subobjects of powers form a descending chain. -/
theorem antitone_imageSubobject_pow [HasImages C]
    (f : End X) : Antitone (fun n : ℕ ↦ imageSubobject (f ^ n)) := by
  apply antitone_nat_of_succ_le
  intro n
  simpa only [pow_succ, End.mul_def] using imageSubobject_comp_le f (f ^ n)

/-- The ascending kernel chain and descending image chain stabilize at a common
threshold on a Noetherian and Artinian object. -/
theorem exists_stable_kernelSubobject_imageSubobject_pow
    [HasZeroMorphisms C] [HasKernels C] [HasImages C]
    [IsNoetherianObject X] [IsArtinianObject X] (f : End X) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      kernelSubobject (f ^ N) = kernelSubobject (f ^ n) ∧
      imageSubobject (f ^ N) = imageSubobject (f ^ n) := by
  obtain ⟨Nk, hk⟩ := monotone_chain_condition_of_isNoetherianObject
    (⟨fun n ↦ kernelSubobject (f ^ n), monotone_kernelSubobject_pow f⟩ :
      ℕ →o Subobject X)
  obtain ⟨Ni, hi⟩ := antitone_chain_condition_of_isArtinianObject
    (⟨fun n ↦ imageSubobject (f ^ n), antitone_imageSubobject_pow f⟩ :
      ℕ →o (Subobject X)ᵒᵈ)
  refine ⟨max Nk Ni, fun n hn ↦ ⟨?_, ?_⟩⟩
  · exact (hk (max Nk Ni) (le_max_left Nk Ni)).symm.trans
      (hk n (le_trans (le_max_left Nk Ni) hn))
  · exact (hi (max Nk Ni) (le_max_right Nk Ni)).symm.trans
      (hi n (le_trans (le_max_right Nk Ni) hn))

end PowerChains

end Limits

end CategoryTheory
