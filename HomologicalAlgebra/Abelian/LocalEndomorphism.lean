/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Abelian.Fitting
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Nilpotent.Basic

import Mathlib.Algebra.Group.Commute.Units

/-!
# Local endomorphism rings of indecomposable objects

Every endomorphism of an indecomposable Noetherian and Artinian object in an
abelian category is nilpotent or a unit. Consequently its canonical
endomorphism ring is local. The ring need not be commutative, and the object
and morphism universes are independent.

The proof applies indecomposability to the canonical Fitting biproduct of the
kernel and image of a sufficiently high positive power. A zero image makes
that power zero. A zero kernel makes the power monomorphic, hence invertible
by the Artinian endomorphism theorem; a positive power is a unit only if the
endomorphism itself is a unit. Indecomposability also excludes a zero object,
so no separate nontriviality hypothesis on the endomorphism ring is needed.

## References

* The categorical decomposition is supplied by
  `HomologicalAlgebra.Abelian.Fitting`, using its canonical kernel/image copairing.
* The ring-theoretic step reuses `IsNilpotent.isUnit_one_sub` from Oliver Nash's
  Mathlib nilpotent API and `IsLocalRing.of_isUnit_or_isUnit_one_sub_self` from
  Mathlib's local-ring API by Kenny Lau, Chris Hughes and Mario Carneiro.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] {X : C}
    [IsNoetherianObject X] [IsArtinianObject X]

/-- Every endomorphism of an indecomposable Noetherian and Artinian object in
an abelian category is nilpotent or a unit, by the categorical Fitting decomposition. -/
theorem isNilpotent_or_isUnit_of_indecomposable (hX : Indecomposable X) (f : End X) :
    IsNilpotent f ∨ IsUnit f := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (eventually_isIso_biprod_desc_kernel_ι_image_ι_pow f)
  -- A positive exponent is needed to recover a unit from a unit power.
  let n : ℕ := N + 1
  have hn : 0 < n := Nat.succ_pos N
  let : IsIso (biprod.desc (kernel.ι (f ^ n)) (image.ι (f ^ n))) :=
    hN n (Nat.le_succ N)
  let e : X ≅ kernel (f ^ n) ⊞ image (f ^ n) :=
    (asIso (biprod.desc (kernel.ι (f ^ n)) (image.ι (f ^ n)))).symm
  rcases hX.2 _ _ e with hker | himage
  · right
    let : Mono (f ^ n) :=
      Preadditive.mono_of_kernel_zero (f := f ^ n) (hker.eq_of_src _ _)
    have hpow : IsIso (f ^ n) := isIso_of_mono_of_isArtinianObject (f ^ n)
    exact (isUnit_pow_iff (Nat.ne_of_gt hn)).1 ((isUnit_iff_isIso _).2 hpow)
  · left
    refine ⟨n, ?_⟩
    rw [← image.fac (f ^ n), himage.eq_of_src (image.ι (f ^ n)) 0, comp_zero]

/-- The canonical, possibly noncommutative endomorphism ring of an indecomposable
Noetherian and Artinian object in an abelian category is local. -/
theorem isLocalRing_end_of_indecomposable (hX : Indecomposable X) :
    IsLocalRing (End X) := by
  have h10 : (1 : End X) ≠ 0 := by
    intro h
    exact hX.1 ((IsZero.iff_id_eq_zero X).2 h)
  let : Nontrivial (End X) := nontrivial_of_ne 1 0 h10
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro f
  rcases isNilpotent_or_isUnit_of_indecomposable hX f with hnil | hunit
  · exact Or.inr hnil.isUnit_one_sub
  · exact Or.inl hunit

end CategoryTheory
