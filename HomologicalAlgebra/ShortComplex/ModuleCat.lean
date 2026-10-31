/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Finiteness of homology of module short complexes

Over an arbitrary ring, the canonical homology of a short complex of modules has finite
underlying carrier whenever its middle term does. The end terms and the ring need not
have finite underlying carriers.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.ShortComplex

/-- Homology has finite underlying carrier if the middle term does; end terms may be infinite. -/
instance finite_homology_moduleCat {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{v} R)) [Finite S.X₂] : Finite S.homology := by
  have : Finite S.g.hom.ker :=
    Finite.of_injective (fun x : S.g.hom.ker => (x : S.X₂)) Subtype.val_injective
  have : Finite S.moduleCatLeftHomologyData.H := by
    dsimp [moduleCatLeftHomologyData]
    exact Finite.of_surjective _ S.moduleCatToCycles.range.mkQ_surjective
  exact Finite.of_equiv _
    (((forget (ModuleCat R)).mapIso S.moduleCatHomologyIso).toEquiv.symm)

end CategoryTheory.ShortComplex
