/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Indecomposable.Artinian
public import HomologicalAlgebra.Abelian.LocalEndomorphism

/-!
# Finite biproduct decompositions with local endomorphism rings

A Noetherian and Artinian object in an abelian category is isomorphic to a
finite biproduct of objects whose canonical endomorphism rings are local.
The ring structures need not be commutative, and the object and morphism
universes are independent. A zero object has the empty decomposition;
locality excludes zero factors.

The result combines finite indecomposable decomposition with the local
endomorphism-ring criterion. Both chain conditions pass to each factor along
its biproduct injection followed by the inverse of the decomposition isomorphism.

## References

* `HomologicalAlgebra.Indecomposable.Artinian` supplies finite indecomposable existence.
* `HomologicalAlgebra.Abelian.LocalEndomorphism` supplies the local-End criterion.
* Mathlib's object chain-condition inheritance API is due to Joël Riou, with
  Artinian-object work also by Kim Morrison. Its biproduct API is due to
  Kim Morrison and Jakob von Raumer; its abelian finite-biproduct API is due to
  Markus Himmel, Johan Commelin and Kim Morrison.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits

attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Every Noetherian and Artinian object in an abelian category admits a finite
biproduct decomposition with local canonical endomorphism rings on all factors.
This combines finite indecomposable existence with the local-endomorphism criterion. -/
theorem exists_finite_biproduct_isLocalRing_end
    (X : C) [IsNoetherianObject X] [IsArtinianObject X] :
    ∃ n : ℕ, ∃ F : Fin n → C,
      (∀ i, IsLocalRing (End (F i))) ∧ Nonempty (X ≅ ⨁ F) := by
  obtain ⟨n, F, hF, ⟨e⟩⟩ :=
    exists_finite_indecomposable_biproduct_of_isArtinianObject X
  refine ⟨n, F, ?_, ⟨e⟩⟩
  intro i
  have : IsNoetherianObject (F i) :=
    isNoetherianObject_of_mono (biproduct.ι F i ≫ e.inv)
  have : IsArtinianObject (F i) :=
    isArtinianObject_of_mono (biproduct.ι F i ≫ e.inv)
  exact isLocalRing_end_of_indecomposable (hF i)

end CategoryTheory
