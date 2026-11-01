/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Abelian.Drazin
public import Mathlib.CategoryTheory.Subobject.Limits

import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Idempotent

/-!
# Kernels, images and the Drazin projector

For an endomorphism `f` of a Noetherian and Artinian object in an abelian
category, the kernel and image subobjects of sufficiently high powers of `f`
are the kernel and image subobjects of `f * drazinInverse f`. The complementary
component `f * (1 - f * drazinInverse f)` is nilpotent.

The statements use the canonical Drazin inverse and the stock kernel and image
subobjects. No stabilization threshold or positive index is supplied as a
hypothesis. Object and morphism universes are independent.

## References

* `HomologicalAlgebra.Abelian.Drazin`, for the canonical Drazin inverse.
* `Mathlib.CategoryTheory.Subobject.Limits`, for kernel and image subobjects.
-/

@[expose] public section

universe v u

namespace CategoryTheory.End

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X : C} [IsNoetherianObject X] [IsArtinianObject X]

private theorem eventually_drazinInverse_pow_factors (f : End X) :
    ∀ᶠ n : ℕ in Filter.atTop,
      n ≠ 0 ∧
      f ^ n * (f * drazinInverse f) = f ^ n ∧
      (f * drazinInverse f) * f ^ n = f ^ n ∧
      f ^ n * drazinInverse f ^ n = f * drazinInverse f ∧
      drazinInverse f ^ n * f ^ n = f * drazinInverse f := by
  obtain ⟨N, hN⟩ := exists_pow_succ_mul_drazinInverse f
  have hNabsorb : f ^ N * (f * drazinInverse f) = f ^ N := by
    rw [← mul_assoc, ← pow_succ, hN]
  have hcomm := commute_drazinInverse f
  have hprojector : Commute f (f * drazinInverse f) :=
    (Commute.refl f).mul_right hcomm
  -- A positive tail permits the idempotent power formula, even when N = 0.
  refine Filter.eventually_atTop.mpr ⟨N + 1, ?_⟩
  intro n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (Nat.succ_pos N) hn)
  have habsorb : f ^ n * (f * drazinInverse f) = f ^ n := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.le_trans (Nat.le_succ N) hn)
    rw [hk, Nat.add_comm N k, pow_add, mul_assoc, hNabsorb]
  have habsorb' : (f * drazinInverse f) * f ^ n = f ^ n :=
    (hprojector.pow_left n).eq.symm.trans habsorb
  have hfactor : f ^ n * drazinInverse f ^ n = f * drazinInverse f := by
    rw [← hcomm.mul_pow n, (isIdempotentElem_mul_drazinInverse f).pow_eq hn0]
  have hfactor' : drazinInverse f ^ n * f ^ n = f * drazinInverse f :=
    (hcomm.pow_pow n n).eq.symm.trans hfactor
  exact ⟨hn0, habsorb, habsorb', hfactor, hfactor'⟩

/-- The kernel subobjects of sufficiently high powers equal the kernel subobject
of the Drazin projector. -/
theorem eventually_kernelSubobject_pow_eq_mul_drazinInverse (f : End X) :
    ∀ᶠ n : ℕ in Filter.atTop,
      kernelSubobject (f ^ n) = kernelSubobject (f * drazinInverse f) := by
  apply (eventually_drazinInverse_pow_factors f).mono
  rintro n ⟨_, habsorb, _, _, hfactor⟩
  apply le_antisymm
  · simpa only [← End.mul_def, hfactor] using
      kernelSubobject_comp_le (f ^ n) (drazinInverse f ^ n)
  · simpa only [← End.mul_def, habsorb] using
      kernelSubobject_comp_le (f * drazinInverse f) (f ^ n)

/-- The image subobjects of sufficiently high powers equal the image subobject
of the Drazin projector. -/
theorem eventually_imageSubobject_pow_eq_mul_drazinInverse (f : End X) :
    ∀ᶠ n : ℕ in Filter.atTop,
      imageSubobject (f ^ n) = imageSubobject (f * drazinInverse f) := by
  apply (eventually_drazinInverse_pow_factors f).mono
  rintro n ⟨_, _, habsorb, hfactor, _⟩
  apply le_antisymm
  · simpa only [← End.mul_def, habsorb] using
      imageSubobject_comp_le (f ^ n) (f * drazinInverse f)
  · simpa only [← End.mul_def, hfactor] using
      imageSubobject_comp_le (drazinInverse f ^ n) (f ^ n)

/-- The component of an endomorphism complementary to its Drazin projector is
nilpotent. -/
theorem isNilpotent_mul_one_sub_mul_drazinInverse (f : End X) :
    IsNilpotent (f * (1 - f * drazinInverse f)) := by
  obtain ⟨n, hn0, habsorb, _, _, _⟩ := (eventually_drazinInverse_pow_factors f).exists
  have hcomm : Commute f (1 - f * drazinInverse f) :=
    (Commute.one_right f).sub_right
      ((Commute.refl f).mul_right (commute_drazinInverse f))
  have hidempotent := (isIdempotentElem_mul_drazinInverse f).one_sub
  refine IsNilpotent.mk _ n ?_
  rw [hcomm.mul_pow n, hidempotent.pow_eq hn0, mul_sub, mul_one, habsorb, sub_self]

end CategoryTheory.End
