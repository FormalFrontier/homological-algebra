/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Abelian.FiniteLength
import StableRange.CategoryTheory.Cancellation

/-!
# Cancellation of finite-length summands

A Noetherian and Artinian object in an abelian category cancels from a binary
biproduct. The remaining objects are unrestricted, and the object and morphism
universes are independent. The conclusion asserts existence of an isomorphism,
not a canonical choice.

The argument combines the finite local-endomorphism-ring decomposition with
cancellation of one local-End summand at a time. The empty decomposition includes
zero objects; the endomorphism ring of the entire canceled object need not be local.

## References

* `HomologicalAlgebra.Abelian.FiniteLength`, for finite local-End decomposition.
* `HomologicalAlgebra.Indecomposable.Biproducts` and
  `HomologicalAlgebra.Preadditive.BiproductUniqueness`, for the finite-family
  comparison approach.
* `StableRange.CategoryTheory.Cancellation`, for categorical cancellation of a
  summand with a possibly noncommutative local endomorphism ring.
* Mathlib's biproduct and finite-tuple APIs, for the finite-family comparisons,
  associativity and zero-summand isomorphisms.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

attribute [local instance] Abelian.hasFiniteBiproducts

private theorem cancel_finite_biproduct_of_isLocalRing_end (n : ℕ) :
    ∀ (F : Fin n → C), (∀ i, IsLocalRing (End (F i))) →
      ∀ (Y Z : C), ((⨁ F) ⊞ Y ≅ (⨁ F) ⊞ Z) → Nonempty (Y ≅ Z) := by
  classical
  induction n with
  | zero =>
    intro F _ Y Z e
    have hzero : IsZero (⨁ F) := by
      apply (IsZero.iff_id_eq_zero _).2
      apply biproduct.hom_ext
      intro i
      exact Fin.elim0 i
    exact ⟨isoZeroBiprod (Y := Y) hzero ≪≫ e ≪≫ (isoZeroBiprod (Y := Z) hzero).symm⟩
  | succ n ih =>
    intro F hF Y Z e
    let A : C := F (Fin.last n)
    let G : Fin n → C := Fin.init F
    let T : C := ⨁ G
    let L : Fin 1 → C := fun _ => A
    have h : Fin.append G L = F := by
      simpa only [Fin.append_right_eq_snoc] using Fin.snoc_init_self F
    let s : A ⊞ T ≅ ⨁ F :=
      biprod.braiding' A T ≪≫
        biprod.mapIso (Iso.refl T) (biproductUniqueIso L).symm ≪≫
        biproductAppendIso G L ≪≫
        biproduct.mapIso (fun i => eqToIso (congrFun h i))
    let k (W : C) : (⨁ F) ⊞ W ≅ A ⊞ (T ⊞ W) :=
      biprod.mapIso s.symm (Iso.refl W) ≪≫ biprod.associator A T W
    let : IsLocalRing (End A) := hF (Fin.last n)
    obtain ⟨q⟩ := nonempty_iso_of_biprod_iso_of_isLocalRing_end A (T ⊞ Y) (T ⊞ Z)
      ((k Y).symm ≪≫ e ≪≫ k Z)
    exact ih G (fun i => hF i.castSucc) Y Z q

/-- A Noetherian and Artinian object cancels from a binary biproduct in an abelian
category, without conditions on the remaining objects. This combines finite
local-End decomposition with the local-endomorphism-ring cancellation theorem
in `StableRange.CategoryTheory.Cancellation`. -/
theorem nonempty_iso_of_biprod_iso_of_isNoetherianObject_of_isArtinianObject
    (X Y Z : C) [IsNoetherianObject X] [IsArtinianObject X]
    (e : X ⊞ Y ≅ X ⊞ Z) : Nonempty (Y ≅ Z) := by
  obtain ⟨n, F, hF, ⟨d⟩⟩ := exists_finite_biproduct_isLocalRing_end X
  let c (W : C) : X ⊞ W ≅ (⨁ F) ⊞ W := biprod.mapIso d (Iso.refl W)
  exact cancel_finite_biproduct_of_isLocalRing_end n F hF Y Z ((c Y).symm ≪≫ e ≪≫ c Z)

end CategoryTheory
