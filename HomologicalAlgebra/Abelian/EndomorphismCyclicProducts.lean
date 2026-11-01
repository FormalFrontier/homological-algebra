/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Cyclic products of morphisms

For morphisms `a : X ⟶ Y` and `b : Y ⟶ X`, successor powers of `a ≫ b` are
sandwiches of powers of `b ≫ a`. In a category with zero morphisms, the two
composites are nilpotent simultaneously.

The powers use the canonical endomorphism monoids, whose multiplication is
`p * q = q ≫ p`. The power identity includes exponent zero and needs only a
category; the nilpotence equivalence additionally needs zero morphisms.

## References

The endomorphism structures and nilpotence predicate are Mathlib's
`CategoryTheory.End` and `IsNilpotent`. The related same-object monoid shuffle
is Mathlib's `mul_pow_mul`.
-/

public section

universe v u

namespace CategoryTheory.End

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {X Y : C}

/-- The successor power of a composite is a sandwich of powers of the cyclically
reversed composite. The formula holds for every natural exponent, including zero. -/
theorem comp_pow_succ (a : X ⟶ Y) (b : Y ⟶ X) (n : ℕ) :
    End.of (a ≫ b) ^ (n + 1) = a ≫ (End.of (b ≫ a) ^ n) ≫ b := by
  induction n with
  | zero =>
      simp only [Nat.zero_add, pow_one, pow_zero, End.one_def, Category.id_comp]
  | succ n ih =>
      rw [pow_succ, End.mul_def, ih, pow_succ, End.mul_def]
      simp only [Category.assoc]

/-- For endomorphisms of one object, the sandwich agrees with Mathlib's
`mul_pow_mul b a n` followed by multiplication on the right by `a`. -/
theorem comp_pow_comp_eq_mul_pow_mul (a b : End X) (n : ℕ) :
    End.of (a ≫ (End.of (b ≫ a) ^ n) ≫ b) =
      ((b * a) ^ n * b) * a := by
  simpa only [End.mul_def, Category.assoc] using
    (congrArg (fun c : End X => c * a) (mul_pow_mul b a n)).symm

/-- Cyclically reversed composites are nilpotent simultaneously in a category
with zero morphisms. The zero operations are those of the given zero morphisms. -/
theorem isNilpotent_comp_iff [HasZeroMorphisms C] (a : X ⟶ Y) (b : Y ⟶ X) :
    @IsNilpotent (End X) (inferInstanceAs (Zero (X ⟶ X))) inferInstance (End.of (a ≫ b)) ↔
      @IsNilpotent (End Y) (inferInstanceAs (Zero (Y ⟶ Y))) inferInstance (End.of (b ≫ a)) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    rw [comp_pow_succ b a n, hn, zero_comp, comp_zero]
  · rintro ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    rw [comp_pow_succ a b n, hn, zero_comp, comp_zero]

end CategoryTheory.End
