/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Cochain.HomComplexQuasiIsoCriteria
public import HomologicalAlgebra.Cochain.HomotopyLimits
public import HomologicalAlgebra.Cochain.DiskAdjunctions

/-!
# K-injectivity of products of cochain complexes

A supplied product of integer cochain complexes in an abelian category is
K-injective if and only if every member is K-injective. The family may be empty,
and its index, object, and morphism universes are independent. No boundedness,
termwise injectivity, or exactness of products is assumed.

Each member is a retract of the product. Conversely, every map from an acyclic
complex has null-homotopic projections, which assemble into a null-homotopy into
the product. Evaluation preserves the supplied product because it is a right
adjoint. This does not assert that products of acyclic complexes are acyclic.
-/

@[expose] public section

universe v u w

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A supplied product of integer cochain complexes is K-injective exactly when
all its members are K-injective. -/
lemma isKInjective_pi_iff {ι : Type w} (F : ι → CochainComplex C ℤ) [HasProduct F] :
    IsKInjective (∏ᶜ F) ↔ ∀ i, IsKInjective (F i) := by
  classical
  constructor
  · intro h i
    let _ := h
    exact IsKInjective.of_retract (Pi.ι F i) (Pi.π F i) (by simp)
  · intro h
    let _ : ∀ i, IsKInjective (F i) := h
    let _ : ∀ n : ℤ, PreservesLimit (Discrete.functor F)
        (HomologicalComplex.eval C (ComplexShape.up ℤ) n) := fun n => by
      let _ : PreservesLimitsOfSize.{w, w}
          (HomologicalComplex.eval C (ComplexShape.up ℤ) n) :=
        (diskAdjunction n).rightAdjoint_preservesLimits
      infer_instance
    constructor
    intro A f hA
    apply (Homotopy.nonempty_pi_iff F).mpr
    intro i
    simpa only [zero_comp] using
      IsKInjective.nonempty_homotopy_zero (f ≫ Pi.π F i) hA

end CochainComplex
