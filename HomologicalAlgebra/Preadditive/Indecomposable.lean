/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.Algebra.Group.Idempotent

/-!
# Indecomposability from a local endomorphism ring

In a preadditive category with binary biproducts, an object whose canonical
endomorphism ring is local is indecomposable. The ring need not be commutative,
and no abelian-category or chain-condition hypothesis is required.

The proof uses the two projectors of a supplied biproduct decomposition. They
are idempotents summing to the identity; locality makes one a unit, hence the
identity, so the other summand is zero. Nontriviality of a local ring also
excludes a zero object, without requiring a chosen zero object in the category.

## References

The proof uses Mathlib's preadditive biproduct identities, its noncommutative
local-ring unit criterion, and `IsIdempotentElem.iff_eq_one_of_isUnit`.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- An object with a local canonical endomorphism ring is indecomposable.

The two projectors of any binary biproduct decomposition are idempotents summing
to one. Mathlib's local-ring unit criterion and unit-idempotent lemma force one
to be the identity and the other to vanish. The inherited nontriviality of the
endomorphism ring excludes the zero object. -/
theorem indecomposable_of_isLocalRing_end (X : C) [IsLocalRing (End X)] : Indecomposable X := by
  refine ⟨?_, ?_⟩
  · intro hX
    have h : (1 : End X) = 0 := (IsZero.iff_id_eq_zero X).mp hX
    exact one_ne_zero h
  · intro Y Z e
    let p : End X := e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv
    let q : End X := e.hom ≫ biprod.snd ≫ biprod.inr ≫ e.inv
    have hp : IsIdempotentElem p := by
      simp only [isIdempotentElem_iff, End.mul_def, p, Category.assoc,
        e.inv_hom_id_assoc, biprod.inl_fst_assoc]
    have hq : IsIdempotentElem q := by
      simp only [isIdempotentElem_iff, End.mul_def, q, Category.assoc,
        e.inv_hom_id_assoc, biprod.inr_snd_assoc]
    have hpq : p + q = 1 := by
      rw [End.one_def]
      calc
        p + q = e.hom ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ e.inv := by
          simp only [p, q, Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
        _ = 𝟙 X := by
          rw [biprod.total, Category.id_comp, e.hom_inv_id]
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hpq with hp_unit | hq_unit
    · have hp_one := (IsIdempotentElem.iff_eq_one_of_isUnit hp_unit).mp hp
      have hq_zero : q = 0 := by
        simpa only [hp_one, add_eq_left] using hpq
      right
      apply (IsZero.iff_id_eq_zero Z).mpr
      have h := congrArg (fun f : End X =>
        (biprod.inr : Z ⟶ Y ⊞ Z) ≫ e.inv ≫ f ≫ e.hom ≫ biprod.snd) hq_zero
      simpa [q, Category.assoc, biprod.inr_snd_assoc, biprod.inr_snd] using h
    · have hq_one := (IsIdempotentElem.iff_eq_one_of_isUnit hq_unit).mp hq
      have hp_zero : p = 0 := by
        simpa only [hq_one, add_eq_right] using hpq
      left
      apply (IsZero.iff_id_eq_zero Y).mpr
      have h := congrArg (fun f : End X =>
        (biprod.inl : Y ⟶ Y ⊞ Z) ≫ e.inv ≫ f ≫ e.hom ≫ biprod.fst) hp_zero
      simpa [p, Category.assoc, biprod.inl_fst_assoc, biprod.inl_fst] using h

end CategoryTheory
