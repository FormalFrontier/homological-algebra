/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Group.Hom.End
import Mathlib.RingTheory.Nilpotent.Basic

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.RingTheory.Nilpotent.Defs

@[expose] public section

/-!
# The Sylvester equation in a preadditive category

An invertible endomorphism of `X` and a nilpotent endomorphism of `Y` determine
an inhomogeneous Sylvester equation on `X ⟶ Y` with a unique solution.
No biproducts, scalar action or chain conditions on the objects are required.
Nilpotence is existential, so zero and nonminimal power witnesses are included.

## References

This formulation uses Mathlib's preadditive hom groups, categorical invertibility
and nilpotent endomorphisms.
-/

universe u v

namespace CategoryTheory

/-- The inhomogeneous Sylvester equation has a unique solution when its left
endomorphism is invertible and its right endomorphism is nilpotent. The morphism
`h` is arbitrary, and no nilpotence exponent is supplied. -/
theorem existsUnique_sylvester
    {C : Type u} [Category.{v} C] [Preadditive C] {X Y : C}
    (f : X ⟶ X) [IsIso f] (g : End Y) (hg : IsNilpotent g) (h : X ⟶ Y) :
    ∃! u : X ⟶ Y, f ≫ u = h + u ≫ g := by
  let L : AddMonoid.End (X ⟶ Y) := Preadditive.leftComp Y f
  -- Right composition respects the reversed multiplication on categorical End.
  let R : End Y →*₀ AddMonoid.End (X ⟶ Y) :=
    { toFun := fun a => Preadditive.rightComp X a
      map_zero' := by
        ext u
        change u ≫ (0 : Y ⟶ Y) = 0
        simp
      map_one' := by
        ext u
        change u ≫ 𝟙 Y = u
        simp
      map_mul' := by
        intro a b
        ext u
        change u ≫ (b ≫ a) = (u ≫ b) ≫ a
        exact (Category.assoc u b a).symm }
  have hL : IsUnit L := by
    rw [isUnit_iff_exists]
    refine ⟨Preadditive.leftComp Y (inv f), ?_, ?_⟩
    · ext u
      change f ≫ (inv f ≫ u) = u
      simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    · ext u
      change inv f ≫ (f ≫ u) = u
      simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have hR : IsNilpotent (R g) := hg.map R
  have hcomm : Commute (R g) L := by
    change R g * L = L * R g
    ext u
    change (f ≫ u) ≫ g = f ≫ (u ≫ g)
    exact Category.assoc f u g
  have hunit : IsUnit (L + -(R g)) :=
    hR.neg.isUnit_add_left_of_commute hL hcomm.neg_left
  obtain ⟨V, hSV, hVS⟩ := isUnit_iff_exists.mp hunit
  have hsolve (u : X ⟶ Y) :
      (L + -(R g)) u = h ↔ f ≫ u = h + u ≫ g := by
    change f ≫ u + -(u ≫ g) = h ↔ f ≫ u = h + u ≫ g
    simpa only [sub_eq_add_neg] using
      (sub_eq_iff_eq_add : f ≫ u - u ≫ g = h ↔ f ≫ u = h + u ≫ g)
  refine ⟨V h, ?_, ?_⟩
  · apply (hsolve (V h)).mp
    exact congrArg (fun a : AddMonoid.End (X ⟶ Y) => a h) hSV
  · intro u hu
    have hu' := (hsolve u).mpr hu
    have hVu : V ((L + -(R g)) u) = u :=
      congrArg (fun a : AddMonoid.End (X ⟶ Y) => a u) hVS
    calc
      u = V ((L + -(R g)) u) := hVu.symm
      _ = V h := congrArg V hu'

end CategoryTheory
