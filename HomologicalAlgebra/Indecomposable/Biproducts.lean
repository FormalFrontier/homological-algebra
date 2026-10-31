/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Simple
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Biproducts and indecomposable objects

This module provides transport of indecomposability across isomorphisms, criteria for a
binary biproduct injection to be invertible, and the comparison between the biproduct of
two finite biproducts and the biproduct of the appended family.

## References

The injection criteria use only zero morphisms and binary biproducts. The left-injection
criterion generalizes `CategoryTheory.Biprod.isIso_inl_iff_isZero` in Mathlib's simple-object
API, due to Markus Himmel and Kim Morrison; an agreement theorem is included below.
The finite comparison uses the generic biproduct universal properties from Mathlib's
biproduct API, developed by Kim Morrison and Jakob von Raumer.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

section Binary

variable [HasZeroMorphisms C]

/-- Indecomposability is invariant under isomorphism. -/
theorem indecomposable_iff_of_iso [HasBinaryBiproducts C] {X Y : C} (e : X ≅ Y) :
    Indecomposable X ↔ Indecomposable Y := by
  constructor
  · rintro ⟨hX, h⟩
    exact ⟨fun hY => hX (hY.of_iso e), fun Z W f => h Z W (e ≪≫ f)⟩
  · rintro ⟨hY, h⟩
    exact ⟨fun hX => hY (hX.of_iso e.symm), fun Z W f => h Z W (e.symm ≪≫ f)⟩

namespace Limits

/-- The left injection of a binary biproduct is invertible exactly when the right summand
is zero. No preadditive structure is needed. -/
theorem biprod.isIso_inl_iff_isZero (X Y : C) [HasBinaryBiproduct X Y] :
    IsIso (biprod.inl : X ⟶ X ⊞ Y) ↔ IsZero Y := by
  constructor
  · intro h
    let := h
    have hsnd : (biprod.snd : X ⊞ Y ⟶ Y) = 0 :=
      (cancel_epi (biprod.inl : X ⟶ X ⊞ Y)).1 (by simp only [biprod.inl_snd, comp_zero])
    rw [IsZero.iff_id_eq_zero]
    calc
      𝟙 Y = (biprod.inr : Y ⟶ X ⊞ Y) ≫ biprod.snd := biprod.inr_snd.symm
      _ = 0 := by rw [hsnd, comp_zero]
  · intro h
    change IsIso (isoBiprodZero (X := X) h).hom
    infer_instance

/-- The right injection of a binary biproduct is invertible exactly when the left summand
is zero. No preadditive structure is needed. -/
theorem biprod.isIso_inr_iff_isZero (X Y : C) [HasBinaryBiproduct X Y] :
    IsIso (biprod.inr : Y ⟶ X ⊞ Y) ↔ IsZero X := by
  constructor
  · intro h
    let := h
    have hfst : (biprod.fst : X ⊞ Y ⟶ X) = 0 :=
      (cancel_epi (biprod.inr : Y ⟶ X ⊞ Y)).1 (by simp only [biprod.inr_fst, comp_zero])
    rw [IsZero.iff_id_eq_zero]
    calc
      𝟙 X = (biprod.inl : X ⟶ X ⊞ Y) ≫ biprod.fst := biprod.inl_fst.symm
      _ = 0 := by rw [hfst, comp_zero]
  · intro h
    change IsIso (isoZeroBiprod (Y := Y) h).hom
    infer_instance

end Limits

end Binary

section Preadditive

variable [Preadditive C] [HasBinaryBiproducts C]

/-- Under its original preadditive hypotheses, the generic left-injection criterion agrees
with Mathlib's simple-object criterion. -/
theorem Limits.biprod.isIso_inl_iff_isZero_eq (X Y : C) :
    Limits.biprod.isIso_inl_iff_isZero X Y =
      CategoryTheory.Biprod.isIso_inl_iff_isZero X Y :=
  Subsingleton.elim _ _

end Preadditive

namespace Limits

section Finite

variable [HasZeroMorphisms C] [HasFiniteBiproducts C]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- The binary biproduct of two finite biproducts is the biproduct of their appended family. -/
noncomputable def biproductAppendIso {m n : ℕ} (F : Fin m → C) (G : Fin n → C) :
    ((⨁ F) ⊞ (⨁ G)) ≅ ⨁ (Fin.append F G) where
  hom := biprod.desc
    (biproduct.desc fun i =>
      eqToHom (Fin.append_left F G i).symm ≫
        biproduct.ι (Fin.append F G) (Fin.castAdd n i))
    (biproduct.desc fun i =>
      eqToHom (Fin.append_right F G i).symm ≫
        biproduct.ι (Fin.append F G) (Fin.natAdd m i))
  inv := biproduct.desc (Fin.addCases
    (fun i => eqToHom (Fin.append_left F G i) ≫ biproduct.ι F i ≫ biprod.inl)
    (fun i => eqToHom (Fin.append_right F G i) ≫ biproduct.ι G i ≫ biprod.inr))
  hom_inv_id := by
    apply biprod.hom_ext'
    · apply biproduct.hom_ext'
      intro i
      simp [Category.assoc]
    · apply biproduct.hom_ext'
      intro i
      simp [Category.assoc]
  inv_hom_id := by
    apply biproduct.hom_ext'
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Category.assoc]

/-- The comparison sends each left-family injection to its corresponding injection in the
appended family. -/
@[reassoc (attr := simp)]
theorem biproductAppendIso_inl_hom {m n : ℕ} (F : Fin m → C) (G : Fin n → C) (i : Fin m) :
    biproduct.ι F i ≫ biprod.inl ≫ (biproductAppendIso F G).hom =
      eqToHom (Fin.append_left F G i).symm ≫
        biproduct.ι (Fin.append F G) (Fin.castAdd n i) := by
  simp [biproductAppendIso]

/-- The comparison sends each right-family injection to its corresponding injection in the
appended family. -/
@[reassoc (attr := simp)]
theorem biproductAppendIso_inr_hom {m n : ℕ} (F : Fin m → C) (G : Fin n → C) (i : Fin n) :
    biproduct.ι G i ≫ biprod.inr ≫ (biproductAppendIso F G).hom =
      eqToHom (Fin.append_right F G i).symm ≫
        biproduct.ι (Fin.append F G) (Fin.natAdd m i) := by
  simp [biproductAppendIso]

/-- The inverse comparison recovers each left-family injection. -/
@[reassoc]
theorem biproductAppendIso_ι_left_inv {m n : ℕ} (F : Fin m → C) (G : Fin n → C) (i : Fin m) :
    (eqToHom (Fin.append_left F G i).symm ≫
        biproduct.ι (Fin.append F G) (Fin.castAdd n i)) ≫ (biproductAppendIso F G).inv =
      biproduct.ι F i ≫ biprod.inl := by
  simp [biproductAppendIso, Category.assoc]

/-- The inverse comparison recovers each right-family injection. -/
@[reassoc]
theorem biproductAppendIso_ι_right_inv {m n : ℕ} (F : Fin m → C) (G : Fin n → C) (i : Fin n) :
    (eqToHom (Fin.append_right F G i).symm ≫
        biproduct.ι (Fin.append F G) (Fin.natAdd m i)) ≫ (biproductAppendIso F G).inv =
      biproduct.ι G i ≫ biprod.inr := by
  simp [biproductAppendIso, Category.assoc]

end Finite

end Limits

end CategoryTheory
