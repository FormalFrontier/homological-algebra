/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Abelian.FiniteLength
public import HomologicalAlgebra.Preadditive.FiniteCancellation

/-!
# Cancellation of finite-length summands

A Noetherian and Artinian object in an abelian category cancels from a binary
biproduct. The remaining objects are unrestricted, and the object and morphism
universes are independent. The conclusion asserts existence of an isomorphism,
not a canonical choice.

The argument combines the finite local-endomorphism-ring decomposition with
finite-family cancellation in a preadditive category. The empty decomposition
includes zero objects; the endomorphism ring of the entire canceled object need
not be local.

## References

* `HomologicalAlgebra.Abelian.FiniteLength`, for finite local-End decomposition.
* `HomologicalAlgebra.Preadditive.FiniteCancellation`, for cancellation of a
  finite family of summands with possibly noncommutative local endomorphism rings.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

attribute [local instance] Abelian.hasFiniteBiproducts

/-- A Noetherian and Artinian object cancels from a binary biproduct in an abelian
category, without conditions on the remaining objects. This combines finite
local-End decomposition with
`CategoryTheory.cancel_finite_biproduct_of_isLocalRing_end`. -/
theorem nonempty_iso_of_biprod_iso_of_isNoetherianObject_of_isArtinianObject
    (X Y Z : C) [IsNoetherianObject X] [IsArtinianObject X]
    (e : X ⊞ Y ≅ X ⊞ Z) : Nonempty (Y ≅ Z) := by
  obtain ⟨_, F, hF, ⟨d⟩⟩ := exists_finite_biproduct_isLocalRing_end X
  let : ∀ i, IsLocalRing (End (F i)) := hF
  let c (W : C) : X ⊞ W ≅ (⨁ F) ⊞ W := biprod.mapIso d (Iso.refl W)
  exact cancel_finite_biproduct_of_isLocalRing_end F Y Z ((c Y).symm ≪≫ e ≪≫ c Z)

end CategoryTheory
