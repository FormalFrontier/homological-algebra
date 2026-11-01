/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Abelian.EndomorphismPowers
public import HomologicalAlgebra.Abelian.Length

/-!
# Canonical length bounds for powers

Finite height of the subobject lattice bounds stabilization of power kernels
and images. The bound is the natural value of `CategoryTheory.objectLength`;
finiteness is essential because `ENat.toNat` sends infinity to zero.

Kernel stabilization and the nilpotent exponent use zero morphisms and kernels.
Image stabilization uses images and image maps. Neither requires an abelian
category. The bound includes objects of length zero.

## References

The bounds use the canonical subobject height and the power chains in
`HomologicalAlgebra.Abelian.EndomorphismPowers`. Mathlib's
`Nat.stabilises_of_monotone` supplies the bounded-profile stabilization theorem;
propagation of adjacent plateaus is specific to powers.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {X : C}

private theorem subobject_height_ne_top (hX : objectLength X ≠ ⊤) (P : Subobject X) :
    Order.height P ≠ ⊤ :=
  ne_top_of_le_ne_top hX (Order.height_mono (show P ≤ ⊤ from le_top))

private theorem subobject_eq_of_le_of_height_toNat_eq (hX : objectLength X ≠ ⊤)
    {P Q : Subobject X} (hPQ : P ≤ Q)
    (h : (Order.height P).toNat = (Order.height Q).toNat) : P = Q := by
  by_contra hne
  have hlt := Order.height_strictMono (lt_of_le_of_ne hPQ hne)
    (lt_top_iff_ne_top.mpr (subobject_height_ne_top hX P))
  apply hlt.ne
  rw [← ENat.natCast_toNat (subobject_height_ne_top hX P),
    ← ENat.natCast_toNat (subobject_height_ne_top hX Q), h]

namespace Limits

-- Moving one factor of `f` across the universal kernel propagates an adjacent plateau.
private theorem kernelSubobject_pow_eq_succ_of_eq [HasZeroMorphisms C] [HasKernels C]
    (f : End X) {n : ℕ}
    (h : kernelSubobject (f ^ n) = kernelSubobject (f ^ (n + 1))) :
    kernelSubobject (f ^ (n + 1)) = kernelSubobject (f ^ (n + 2)) := by
  apply le_antisymm ((monotone_kernelSubobject_pow f) (Nat.le_succ (n + 1)))
  apply le_kernelSubobject
  have hfac : (kernelSubobject (f ^ (n + 1))).Factors
      ((kernelSubobject (f ^ (n + 2))).arrow ≫ f) := by
    apply kernelSubobject_factors
    rw [Category.assoc, ← End.mul_def, ← pow_succ]
    exact kernelSubobject_arrow_comp (f ^ (n + 2))
  rw [← h] at hfac
  have hz := (kernelSubobject_factors_iff (f ^ n) _).mp hfac
  simpa only [Category.assoc, ← End.mul_def, ← pow_succ] using hz

-- Image maps identify the image of the restricted power without an image-epi assumption.
private theorem imageSubobject_arrow_comp_pow [HasImages C] [HasImageMaps C]
    (f : End X) (n : ℕ) :
    imageSubobject ((imageSubobject (f ^ n)).arrow ≫ f) =
      imageSubobject (f ^ (n + 1)) := by
  let sq : Arrow.mk (f ^ n) ⟶ Arrow.mk (f ^ (n + 1)) :=
    Arrow.homMk' (𝟙 X) f (by
      simpa only [Category.id_comp, End.mul_def] using pow_succ' f n)
  apply le_antisymm
  · exact imageSubobject_le _ (imageSubobjectMap sq) (imageSubobjectMap_arrow sq)
  · have hcomp : f ^ (n + 1) = factorThruImageSubobject (f ^ n) ≫
        ((imageSubobject (f ^ n)).arrow ≫ f) := by
      rw [← Category.assoc, imageSubobject_arrow_comp, pow_succ', End.mul_def]
    rw [hcomp]
    exact imageSubobject_comp_le _ _

private theorem imageSubobject_pow_eq_succ_of_eq [HasImages C] [HasImageMaps C]
    (f : End X) {n : ℕ}
    (h : imageSubobject (f ^ n) = imageSubobject (f ^ (n + 1))) :
    imageSubobject (f ^ (n + 1)) = imageSubobject (f ^ (n + 2)) := by
  have he := congrArg (fun P : Subobject X ↦ imageSubobject (P.arrow ≫ f)) h
  simpa only [imageSubobject_arrow_comp_pow] using he

/-- Power kernels stabilize by the finite canonical object length. -/
theorem kernelSubobject_pow_eq_of_objectLength_le [HasZeroMorphisms C] [HasKernels C]
    (f : End X) (hX : objectLength X ≠ ⊤) {n : ℕ}
    (hn : (objectLength X).toNat ≤ n) :
    kernelSubobject (f ^ n) = kernelSubobject (f ^ (objectLength X).toNat) := by
  let a : ℕ → ℕ := fun m ↦ (Order.height (kernelSubobject (f ^ m))).toNat
  have hmono : Monotone a := fun i j hij ↦
    ENat.toNat_le_toNat (Order.height_mono ((monotone_kernelSubobject_pow f) hij))
      (subobject_height_ne_top hX _)
  have hbound : ∀ m, a m ≤ (objectLength X).toNat := fun m ↦
    ENat.toNat_le_toNat
      (Order.height_mono (show kernelSubobject (f ^ m) ≤ ⊤ from le_top)) hX
  have hstab : ∀ m, a m = a (m + 1) → a (m + 1) = a (m + 2) := by
    intro m hm
    have he := subobject_eq_of_le_of_height_toNat_eq hX
      ((monotone_kernelSubobject_pow f) (Nat.le_succ m)) hm
    exact congrArg (fun P : Subobject X ↦ (Order.height P).toNat)
      (kernelSubobject_pow_eq_succ_of_eq f he)
  exact (subobject_eq_of_le_of_height_toNat_eq hX
    ((monotone_kernelSubobject_pow f) hn)
    (Nat.stabilises_of_monotone hmono hbound hstab hn).symm).symm

/-- Power images stabilize by the finite canonical object length. -/
theorem imageSubobject_pow_eq_of_objectLength_le [HasImages C] [HasImageMaps C]
    (f : End X) (hX : objectLength X ≠ ⊤) {n : ℕ}
    (hn : (objectLength X).toNat ≤ n) :
    imageSubobject (f ^ n) = imageSubobject (f ^ (objectLength X).toNat) := by
  let a : ℕ → ℕ := fun m ↦ (Order.height (imageSubobject (f ^ m))).toNat
  have hanti : Antitone a := fun i j hij ↦
    ENat.toNat_le_toNat (Order.height_mono ((antitone_imageSubobject_pow f) hij))
      (subobject_height_ne_top hX _)
  have hstab : ∀ m, a m = a (m + 1) → a (m + 1) = a (m + 2) := by
    intro m hm
    have he := subobject_eq_of_le_of_height_toNat_eq hX
      ((antitone_imageSubobject_pow f) (Nat.le_succ m)) hm.symm
    exact congrArg (fun P : Subobject X ↦ (Order.height P).toNat)
      (imageSubobject_pow_eq_succ_of_eq f he.symm)
  obtain ⟨k, hk, hstable⟩ := Nat.stabilises_of_antitone hanti hstab
  have hkL : k ≤ (objectLength X).toNat := hk.trans
    (ENat.toNat_le_toNat
      (Order.height_mono (show imageSubobject (f ^ 0) ≤ ⊤ from le_top)) hX)
  exact subobject_eq_of_le_of_height_toNat_eq hX
    ((antitone_imageSubobject_pow f) hn)
    ((hstable n (hkL.trans hn)).trans (hstable _ hkL).symm)

end Limits

namespace End

/-- A nilpotent endomorphism vanishes at the finite canonical object length,
including length zero. No Drazin inverse or chain-condition instances are needed. -/
theorem pow_objectLength_toNat_eq_zero_of_isNilpotent
    [HasZeroMorphisms C] [HasKernels C] (g : End X)
    (hX : objectLength X ≠ ⊤) (hg : IsNilpotent g) :
    g ^ (objectLength X).toNat = 0 := by
  obtain ⟨k, hk⟩ := hg
  have hz : g ^ (k + (objectLength X).toNat) = 0 := by
    simp only [pow_add, End.mul_def, hk, End.zero_def, comp_zero]
  have he := kernelSubobject_pow_eq_of_objectLength_le g hX
    (n := k + (objectLength X).toNat) (by omega)
  have htop : kernelSubobject (g ^ (objectLength X).toNat) = ⊤ := by
    rw [← he, hz, kernelSubobject_zero]
  have hfac : (kernelSubobject (g ^ (objectLength X).toNat)).Factors (𝟙 X) := by
    rw [htop]
    exact Subobject.top_factors _
  simpa only [Category.id_comp] using
    (kernelSubobject_factors_iff (g ^ (objectLength X).toNat) (𝟙 X)).mp hfac

end End

end CategoryTheory
