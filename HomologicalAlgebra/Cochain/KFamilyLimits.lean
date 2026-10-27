/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Cochain.HomComplexQuasiIsoCriteria
public import HomologicalAlgebra.Cochain.HomotopyLimits
public import HomologicalAlgebra.Cochain.DiskAdjunctions

/-!
# K-projectivity of coproducts and K-injectivity of products

A supplied coproduct of integer cochain complexes in an abelian category is
K-projective if and only if every member is K-projective. Dually, a supplied
product is K-injective if and only if every member is K-injective. The families
may be empty, and their index, object, and morphism universes are independent.
No boundedness, termwise projectivity or injectivity, or exactness of the
(co)products is assumed.

Each member is a retract of the supplied (co)product. Conversely, the member
null-homotopies assemble into a null-homotopy for the (co)product. Evaluation
preserves the supplied coproduct and product because it has both adjoints.
This does not assert that (co)products of acyclic complexes are acyclic.
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

/-- A supplied coproduct of integer cochain complexes is K-projective exactly when
all its members are K-projective. -/
lemma isKProjective_sigma_iff {ι : Type w} (K : ι → CochainComplex C ℤ) [HasCoproduct K] :
    IsKProjective (∐ K) ↔ ∀ i, IsKProjective (K i) := by
  classical
  constructor
  · intro h i
    let _ := h
    exact IsKProjective.of_retract
      (Sigma.ι K i) (retraction (Sigma.ι K i)) (by simp)
  · intro h
    let _ : ∀ i, IsKProjective (K i) := h
    let _ : ∀ n : ℤ, PreservesColimit (Discrete.functor K)
        (HomologicalComplex.eval C (ComplexShape.up ℤ) n) := fun n => by
      let _ : PreservesColimitsOfSize.{w, w}
          (HomologicalComplex.eval C (ComplexShape.up ℤ) n) := inferInstance
      infer_instance
    constructor
    intro A f hA
    apply (Homotopy.nonempty_sigma_iff (F := K) (f := f) (g := 0)).mpr
    intro i
    simpa only [comp_zero] using
      IsKProjective.nonempty_homotopy_zero (Sigma.ι K i ≫ f) hA

end CochainComplex
