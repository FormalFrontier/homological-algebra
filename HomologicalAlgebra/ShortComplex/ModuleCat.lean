/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cardinality bounds for homology of module short complexes

Over an arbitrary ring, the underlying cardinality of the canonical homology of a short
complex of modules is at most that of its middle term. In particular, homology has finite
underlying carrier whenever its middle term does. The end terms and the ring need not
have finite underlying carriers.

Over an arbitrary ring, canonical homology is an Artinian module if the middle term is.
The ring and module universes are independent, and no conditions on the end terms are needed.

## References

The finite-carrier result uses Mathlib's concrete description of module homology.
The Artinian result uses Mathlib's canonical cycles monomorphism and homology
epimorphism, together with inheritance of module Artinianity under injective and
surjective linear maps.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.ShortComplex

/-- The underlying cardinality of homology is at most that of the middle term. -/
theorem mk_homology_le {R : Type u} [Ring R] (S : ShortComplex (ModuleCat.{v} R)) :
    Cardinal.mk S.homology ≤ Cardinal.mk S.X₂ := by
  calc
    Cardinal.mk S.homology = Cardinal.mk S.moduleCatLeftHomologyData.H :=
      Cardinal.mk_congr (((forget (ModuleCat R)).mapIso S.moduleCatHomologyIso).toEquiv)
    _ ≤ Cardinal.mk S.g.hom.ker := by
      dsimp [moduleCatLeftHomologyData]
      exact Cardinal.mk_le_of_surjective (f := _) S.moduleCatToCycles.range.mkQ_surjective
    _ ≤ Cardinal.mk S.X₂ :=
      Cardinal.mk_le_of_injective (f := fun x : S.g.hom.ker => (x : S.X₂))
        Subtype.val_injective

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

/-- Over an arbitrary ring, canonical homology is an Artinian module if the middle term is.
The ring and module universes are independent, and no conditions on the end terms are needed. -/
theorem isArtinian_homology_moduleCat {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{v} R)) [IsArtinian R S.X₂] :
    IsArtinian R S.homology := by
  have : IsArtinian R S.cycles := by
    apply isArtinian_of_injective S.iCycles.hom
    exact (ModuleCat.mono_iff_injective S.iCycles).mp inferInstance
  apply isArtinian_of_surjective (f := S.homologyπ.hom)
  exact (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance

example :
    let A := ModuleCat.of ℤ ℤ
    let M := ModuleCat.of ℤ (Fin 3 → ZMod 2)
    let S := ShortComplex.mk (0 : A ⟶ M) (0 : M ⟶ A) (CategoryTheory.Limits.zero_comp ..)
    Cardinal.mk S.homology ≤ 8 := by
  dsimp only
  calc
    _ ≤ Cardinal.mk (Fin 3 → ZMod 2) := mk_homology_le _
    _ = 8 := by simp [Cardinal.mk_fintype, ZMod.card]

end CategoryTheory.ShortComplex
