/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Cochain.RelativePath

/-!
# Ordinary clients of fixed-arrow relative paths

These examples import the fixed-arrow producer and are re-exported by
`HomologicalAlgebraTest`. Both chosen lifts land in the same object determined by `f`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits CochainComplex.RelativePath

variable {C : Type*} [Category* C] [Preadditive C]
variable [HasBinaryBiproducts C] [HasPullbacks C]
variable {B₁ B A A' : CochainComplex C ℤ}
variable (f : B₁ ⟶ B) (u : A ⟶ B₁) (v : A ⟶ B)
variable (h : Homotopy (u ≫ f) v)
variable (u' : A' ⟶ B₁) (v' : A' ⟶ B)
variable (h' : Homotopy (u' ≫ f) v')

example : sectionMap f ≫ fst f = 𝟙 B₁ ∧ sectionMap f ≫ toTarget f = f := by
  exact ⟨section_fst f, section_toTarget f⟩

example : lift f u v h ≫ fst f = u ∧ lift f u v h ≫ toTarget f = v := by
  exact ⟨lift_fst f u v h, lift_toTarget f u v h⟩

example : lift f u' v' h' ≫ fst f = u' ∧
    lift f u' v' h' ≫ toTarget f = v' := by
  exact ⟨lift_fst f u' v' h', lift_toTarget f u' v' h'⟩

example : (lift f u v h : A ⟶ obj f) ≫ fst f = u ∧
    (lift f u' v' h' : A' ⟶ obj f) ≫ fst f = u' := by
  exact ⟨lift_fst f u v h, lift_fst f u' v' h'⟩

example : lift f u (u ≫ f) (Homotopy.ofEq rfl) ≫ toTarget f = u ≫ f :=
  lift_toTarget f u (u ≫ f) (Homotopy.ofEq rfl)

example (i j : ℤ) :
    (HomologicalComplex.pathObject.π₀CompιHomotopy B hcℤ).hom i j ≫
      (HomologicalComplex.pathObject.π₀ B).f j = 0 :=
  path_hom_π₀ B i j

example (i j : ℤ) : (contraction f).hom i j ≫ (fst f).f j = 0 :=
  contraction_fst_hom f i j

example : (equivalence f).hom = sectionMap f ∧ (equivalence f).inv = fst f :=
  ⟨rfl, rfl⟩
