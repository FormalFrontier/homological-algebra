/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import HomologicalAlgebra.Cochain.HomComplexFunctoriality
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# Both Hom-complex contractions on the same nonzero identity cone

The source and target are the same cone of the identity of the integer stalk.
The model is in `ModuleCat.{0} ℤ`: its object and morphism universes differ.
The resulting Hom complex is in `AddCommGrpCat`, not `ModuleCat ℤ`.
Zero-object and biproduct assumptions are supplied only by this concrete model.

We use Joël Riou's Mathlib Hom-complex, single-functor and mapping-cone APIs,
including the identity-cone contraction from `Pretriangulated` (2023).
The left, right and joint homotopies supply degree-minus-one operators.
Their characteristic component equations identify three returned primitives
with the input contraction's cochain, without unfolding the new constructions.
The identity cochain is nonzero but is a boundary; its degree-zero class is zero.
-/

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open CochainComplex CochainComplex.HomComplex

namespace HomologicalAlgebraTest.HomComplexContractibility

noncomputable section

private abbrev P : CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ ℤ)

private abbrev K : CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  CochainComplex.mappingCone (𝟙 P)

private def inputContraction : Homotopy (𝟙 K) (0 : K ⟶ K) :=
  CochainComplex.mappingCone.homotopyToZeroOfId P

private def leftContraction : Homotopy (𝟙 (HomComplex K K)) 0 :=
  homotopyToZeroOfLeft (L := K) inputContraction

private def rightContraction : Homotopy (𝟙 (HomComplex K K)) 0 :=
  homotopyToZeroOfRight (K := K) inputContraction

private def identityCochain : Cochain K K 0 := Cochain.ofHom (𝟙 K)

private def leftPrimitive : Cochain K K (-1) :=
  leftContraction.hom 0 (-1) identityCochain

private def rightPrimitive : Cochain K K (-1) :=
  rightContraction.hom 0 (-1) identityCochain

private def jointPrimitive : Cochain K K (-1) :=
  (prePostcompHomotopy inputContraction inputContraction).hom 0 (-1) identityCochain

private lemma cone_X_zero_not_isZero : ¬ IsZero (K.X 0) := by
  intro hK
  have hP : IsZero (P.X 0) :=
    ((mappingCone.isZero_X_iff (𝟙 P) (0 : ℤ)).mp hK).2
  have hZ : IsZero (ModuleCat.of ℤ ℤ) :=
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (ModuleCat.of ℤ ℤ)).isZero_iff.mp hP
  let : Subsingleton ℤ := ModuleCat.isZero_of_iff_subsingleton.mp hZ
  exact (zero_ne_one : (0 : ℤ) ≠ 1) (Subsingleton.elim 0 1)

private lemma identityChainMap_ne_zero : (𝟙 K : K ⟶ K) ≠ 0 := by
  intro hid
  apply cone_X_zero_not_isZero
  apply (IsZero.iff_id_eq_zero (K.X 0)).mpr
  simpa using congrArg (fun f : K ⟶ K => f.f 0) hid

private lemma identityCochain_ne_zero : identityCochain ≠ 0 := by
  intro hφ
  apply identityChainMap_ne_zero
  apply Cochain.ofHom_injective
  simpa [identityCochain] using hφ

private lemma input_boundary :
    δ (-1) 0 (Cochain.ofHomotopy inputContraction) = identityCochain := by
  simp [identityCochain]

private lemma leftPrimitive_eq_input :
    leftPrimitive = Cochain.ofHomotopy inputContraction := by
  change (homotopyToZeroOfLeft (L := K) inputContraction).hom 0 (-1)
    (Cochain.ofHom (𝟙 K)) = Cochain.ofHomotopy inputContraction
  apply Cochain.ext
  intro p q hpq
  obtain rfl : q = p - 1 := by omega
  simpa [Cochain.ofHomotopy] using
    (homotopyToZeroOfLeft_hom_v (L := K) inputContraction 0
      (Cochain.ofHom (𝟙 K)) p (p - 1) (by omega))

private lemma rightPrimitive_eq_input :
    rightPrimitive = Cochain.ofHomotopy inputContraction := by
  change (homotopyToZeroOfRight (K := K) inputContraction).hom 0 (-1)
    (Cochain.ofHom (𝟙 K)) = Cochain.ofHomotopy inputContraction
  apply Cochain.ext
  intro p q hpq
  obtain rfl : p = q + 1 := by omega
  simpa [Cochain.ofHomotopy] using
    (homotopyToZeroOfRight_hom_v (K := K) inputContraction 0
      (Cochain.ofHom (𝟙 K)) (q + 1) q (by omega))

private lemma jointPrimitive_eq_input :
    jointPrimitive = Cochain.ofHomotopy inputContraction := by
  change (prePostcompHomotopy inputContraction inputContraction).hom 0 (-1)
    (Cochain.ofHom (𝟙 K)) = Cochain.ofHomotopy inputContraction
  apply Cochain.ext
  intro p q hpq
  obtain rfl : q = p - 1 := by omega
  simpa [Cochain.ofHomotopy] using
    (prePostcompHomotopy_hom_v inputContraction inputContraction 0
      (Cochain.ofHom (𝟙 K)) p (p - 1) (by omega))

private lemma returned_primitives_are_boundaries :
    δ (-1) 0 leftPrimitive = identityCochain ∧
      δ (-1) 0 rightPrimitive = identityCochain ∧
      δ (-1) 0 jointPrimitive = identityCochain := by
  rw [leftPrimitive_eq_input, rightPrimitive_eq_input, jointPrimitive_eq_input]
  exact ⟨input_boundary, input_boundary, input_boundary⟩

/-- Nonzero as a cochain, zero as a cohomology class, with returned data as witness. -/
example : identityCochain ≠ 0 ∧
    CohomologyClass.mk (Cocycle.ofHom (𝟙 K)) = 0 := by
  refine ⟨identityCochain_ne_zero, ?_⟩
  apply (CohomologyClass.mk_eq_zero_iff _).mpr
  apply (mem_coboundaries_iff _ (-1) (by omega)).mpr
  exact ⟨leftPrimitive, returned_primitives_are_boundaries.1⟩

example : (HomComplex K K).Acyclic :=
  acyclic_of_homotopy_id_zero_left (L := K) inputContraction

example : (HomComplex K K).Acyclic :=
  acyclic_of_homotopy_id_zero_right (K := K) inputContraction

/- The zero-complex check is secondary to the same nonzero cone above. -/
private abbrev Z : CochainComplex (ModuleCat.{0} ℤ) ℤ := 0

private def zeroInput : Homotopy (𝟙 Z) (0 : Z ⟶ Z) :=
  Homotopy.ofEq (by
    exact (isZero_zero (CochainComplex (ModuleCat.{0} ℤ) ℤ)).eq_of_src _ _)

example (p q : ℤ) (hpq : p + (0 - 1) = q) :
    ((homotopyToZeroOfLeft (L := Z) zeroInput).hom 0 (-1)
      (0 : Cochain Z Z 0)).v p q hpq = 0 ∧
    ((homotopyToZeroOfRight (K := Z) zeroInput).hom 0 (-1)
      (0 : Cochain Z Z 0)).v p q hpq = 0 := by
  constructor
  · exact (homotopyToZeroOfLeft_hom_v (L := Z) zeroInput 0
      (0 : Cochain Z Z 0) p q hpq).trans (by simp)
  · exact (homotopyToZeroOfRight_hom_v (K := Z) zeroInput 0
      (0 : Cochain Z Z 0) p q hpq).trans (by simp)

end

end HomologicalAlgebraTest.HomComplexContractibility
