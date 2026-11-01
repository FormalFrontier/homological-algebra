/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Abelian.DrazinProjector
public import HomologicalAlgebra.Abelian.EndomorphismPowerLength

/-!
# Effective length bounds for the Drazin projector

For an endomorphism of a Noetherian and Artinian object, power kernels and
images agree with those of the Drazin projector from the canonical object
length onward. The same length bounds the characteristic equation and the
nilpotent complementary component. It is a uniform bound, not necessarily
the least exponent for an individual endomorphism.

The object and morphism universes are independent. Multiplication is the
original multiplication on `CategoryTheory.End`, so `f * g = g ≫ f`.
The zero-length case is included.

## References

These bounds refine the eventual projector comparisons in
`HomologicalAlgebra.Abelian.DrazinProjector`, using the canonical height in
`HomologicalAlgebra.Abelian.Length`.
-/

@[expose] public section

universe u v

namespace CategoryTheory.End

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X : C} [IsNoetherianObject X] [IsArtinianObject X]

/-- From the canonical object length onward, power kernels equal the kernel
of the Drazin projector. -/
theorem kernelSubobject_pow_eq_mul_drazinInverse_of_objectLength_le
    (f : End X) {n : ℕ} (hn : (objectLength X).toNat ≤ n) :
    kernelSubobject (f ^ n) = kernelSubobject (f * drazinInverse f) := by
  have hX : objectLength X ≠ ⊤ :=
    (objectLength_ne_top_iff X).2 ⟨inferInstance, inferInstance⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (eventually_kernelSubobject_pow_eq_mul_drazinInverse f)
  calc
    kernelSubobject (f ^ n) = kernelSubobject (f ^ (objectLength X).toNat) :=
      kernelSubobject_pow_eq_of_objectLength_le f hX hn
    _ = kernelSubobject (f ^ max n N) :=
      (kernelSubobject_pow_eq_of_objectLength_le f hX
        (hn.trans (Nat.le_max_left n N))).symm
    _ = kernelSubobject (f * drazinInverse f) := hN _ (Nat.le_max_right n N)

/-- From the canonical object length onward, power images equal the image
of the Drazin projector. -/
theorem imageSubobject_pow_eq_mul_drazinInverse_of_objectLength_le
    (f : End X) {n : ℕ} (hn : (objectLength X).toNat ≤ n) :
    imageSubobject (f ^ n) = imageSubobject (f * drazinInverse f) := by
  have hX : objectLength X ≠ ⊤ :=
    (objectLength_ne_top_iff X).2 ⟨inferInstance, inferInstance⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (eventually_imageSubobject_pow_eq_mul_drazinInverse f)
  calc
    imageSubobject (f ^ n) = imageSubobject (f ^ (objectLength X).toNat) :=
      imageSubobject_pow_eq_of_objectLength_le f hX hn
    _ = imageSubobject (f ^ max n N) :=
      (imageSubobject_pow_eq_of_objectLength_le f hX
        (hn.trans (Nat.le_max_left n N))).symm
    _ = imageSubobject (f * drazinInverse f) := hN _ (Nat.le_max_right n N)

/-- The canonical object length is a characteristic exponent for the Drazin inverse. -/
theorem pow_objectLength_toNat_succ_mul_drazinInverse (f : End X) :
    f ^ ((objectLength X).toNat + 1) * drazinInverse f =
      f ^ (objectLength X).toNat := by
  have hq : (1 - f * drazinInverse f) ≫ (f * drazinInverse f) = 0 := by
    rw [← End.mul_def, mul_sub, mul_one,
      (isIdempotentElem_mul_drazinInverse f).eq, sub_self]
  have hfactor :
      (kernelSubobject (f ^ (objectLength X).toNat)).Factors
        (1 - f * drazinInverse f) := by
    rw [kernelSubobject_pow_eq_mul_drazinInverse_of_objectLength_le f
      (n := (objectLength X).toNat) le_rfl]
    exact kernelSubobject_factors (f * drazinInverse f) _ hq
  have hz : f ^ (objectLength X).toNat * (1 - f * drazinInverse f) = 0 := by
    simpa only [← End.mul_def] using
      (kernelSubobject_factors_iff (f ^ (objectLength X).toNat) _).1 hfactor
  rw [mul_sub, mul_one, sub_eq_zero] at hz
  simpa only [pow_succ, mul_assoc] using hz.symm

/-- The complementary nilpotent component vanishes at the canonical object length. -/
theorem mul_one_sub_mul_drazinInverse_pow_objectLength_toNat (f : End X) :
    (f * (1 - f * drazinInverse f)) ^ (objectLength X).toNat = 0 := by
  exact pow_objectLength_toNat_eq_zero_of_isNilpotent _
    ((objectLength_ne_top_iff X).2 ⟨inferInstance, inferInstance⟩)
    (isNilpotent_mul_one_sub_mul_drazinInverse f)

end CategoryTheory.End
