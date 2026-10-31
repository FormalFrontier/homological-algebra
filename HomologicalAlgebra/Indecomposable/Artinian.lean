/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Indecomposable.Biproducts
public import Mathlib.CategoryTheory.Subobject.ArtinianObject

/-!
# Finite indecomposable decompositions of Artinian objects

An Artinian object in a category with zero morphisms and finite biproducts is
isomorphic to a finite biproduct of indecomposable objects. The proof uses
well-founded induction on its subobjects: a nontrivial binary biproduct split
gives two strictly smaller subobjects. Zero objects have the empty decomposition.

## References

* `Mathlib.CategoryTheory.Subobject.ArtinianObject` supplies the object chain condition.
* `Mathlib.CategoryTheory.Subobject.Basic` supplies strict-subobject comparison.
* `Mathlib.CategoryTheory.Limits.Shapes.Biproducts` supplies finite biproducts.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

attribute [local instance] Limits.hasBinaryBiproducts_of_finite_biproducts

variable {C : Type u} [Category.{v} C]
  [HasZeroMorphisms C] [HasFiniteBiproducts C]

/-- An Artinian object is isomorphic to a finite biproduct of indecomposable objects. -/
theorem exists_finite_indecomposable_biproduct_of_isArtinianObject
    (X : C) [IsArtinianObject X] :
    ∃ n : ℕ, ∃ F : Fin n → C,
      (∀ i, Indecomposable (F i)) ∧ Nonempty (X ≅ ⨁ F) := by
  classical
  have h : ∀ S : Subobject X, ∃ n : ℕ, ∃ F : Fin n → C,
      (∀ i, Indecomposable (F i)) ∧ Nonempty ((S : C) ≅ ⨁ F) := by
    intro S
    induction S using WellFoundedLT.induction with
    | ind S ih =>
      by_cases hzero : IsZero (S : C)
      · refine ⟨0, Fin.elim0, ?_, ?_⟩
        · intro i
          exact Fin.elim0 i
        · refine ⟨hzero.iso ?_⟩
          rw [IsZero.iff_id_eq_zero]
          apply biproduct.hom_ext
          intro i
          exact Fin.elim0 i
      by_cases hind : Indecomposable (S : C)
      · exact ⟨1, fun _ ↦ (S : C), fun _ ↦ hind,
          ⟨(biproductUniqueIso (fun _ : Fin 1 ↦ (S : C))).symm⟩⟩
      have hsplit : ∃ Y Z : C, Nonempty ((S : C) ≅ Y ⊞ Z) ∧
          ¬IsZero Y ∧ ¬IsZero Z := by
        by_contra hsplit
        apply hind
        refine ⟨hzero, ?_⟩
        intro Y Z e
        by_cases hY : IsZero Y
        · exact Or.inl hY
        · right
          by_contra hZ
          exact hsplit ⟨Y, Z, ⟨e⟩, hY, hZ⟩
      obtain ⟨Y, Z, ⟨e⟩, hY, hZ⟩ := hsplit
      let f : Y ⟶ (S : C) := biprod.inl ≫ e.inv
      let g : Z ⟶ (S : C) := biprod.inr ≫ e.inv
      have hf : ¬IsIso f := by
        intro hf
        let : IsIso f := hf
        have hi : IsIso (biprod.inl : Y ⟶ Y ⊞ Z) := by
          have hi' : IsIso (f ≫ e.hom) := inferInstance
          simpa only [f, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hi'
        exact hZ ((biprod.isIso_inl_iff_isZero Y Z).mp hi)
      have hg : ¬IsIso g := by
        intro hg
        let : IsIso g := hg
        have hi : IsIso (biprod.inr : Z ⟶ Y ⊞ Z) := by
          have hi' : IsIso (g ≫ e.hom) := inferInstance
          simpa only [g, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hi'
        exact hY ((biprod.isIso_inr_iff_isZero Y Z).mp hi)
      have hf_lt : Subobject.mk (f ≫ S.arrow) < S := by
        simpa only [Subobject.mk_arrow] using
          (Subobject.mk_lt_mk_of_comm
            (i₁ := f ≫ S.arrow) (i₂ := S.arrow) f rfl hf)
      have hg_lt : Subobject.mk (g ≫ S.arrow) < S := by
        simpa only [Subobject.mk_arrow] using
          (Subobject.mk_lt_mk_of_comm
            (i₁ := g ≫ S.arrow) (i₂ := S.arrow) g rfl hg)
      obtain ⟨m, F, hF, ⟨eF⟩⟩ := ih (Subobject.mk (f ≫ S.arrow)) hf_lt
      obtain ⟨n, G, hG, ⟨eG⟩⟩ := ih (Subobject.mk (g ≫ S.arrow)) hg_lt
      let dY : Y ≅ ⨁ F := (Subobject.underlyingIso (f ≫ S.arrow)).symm ≪≫ eF
      let dZ : Z ≅ ⨁ G := (Subobject.underlyingIso (g ≫ S.arrow)).symm ≪≫ eG
      refine ⟨m + n, Fin.append F G, ?_, ?_⟩
      · intro i
        refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
        · simpa only [Fin.append_left] using hF j
        · simpa only [Fin.append_right] using hG j
      · exact ⟨e ≪≫ biprod.mapIso dY dZ ≪≫ biproductAppendIso F G⟩
  obtain ⟨n, F, hF, ⟨e⟩⟩ := h (Subobject.mk (𝟙 X))
  exact ⟨n, F, hF, ⟨(Subobject.underlyingIso (𝟙 X)).symm ≪≫ e⟩⟩

end CategoryTheory
