/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Cochain.HomComplexQuasiIsoCriteria
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# K-projectivity and K-injectivity of binary biproducts

For integer cochain complexes in an abelian category, a binary biproduct is
K-projective if and only if both summands are K-projective, and it is K-injective
if and only if both summands are K-injective. The object and morphism universes
are independent, and no boundedness or conditions on individual terms are imposed.

The summands are categorical retracts of the biproduct. Conversely, the standard
null-homotopy characterizations of K-projectivity and K-injectivity reduce the
claim to addition of homotopies along the biproduct inclusions and projections.

## References

- N. Spaltenstein, *Resolutions of unbounded complexes*, §1.
- Mathlib's K-projective and K-injective complexes and additive homotopy API.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A binary biproduct of integer cochain complexes is K-projective exactly when
both summands are K-projective. -/
lemma isKProjective_biprod_iff (K L : CochainComplex C ℤ) :
    (K ⊞ L).IsKProjective ↔ K.IsKProjective ∧ L.IsKProjective := by
  constructor
  · intro h
    let _ := h
    exact ⟨IsKProjective.of_retract (biprod.inl : K ⟶ K ⊞ L) biprod.fst (by simp),
      IsKProjective.of_retract (biprod.inr : L ⟶ K ⊞ L) biprod.snd (by simp)⟩
  · rintro ⟨hK, hL⟩
    let _ := hK
    let _ := hL
    constructor
    intro A f hA
    obtain ⟨h₁⟩ := IsKProjective.nonempty_homotopy_zero (biprod.inl ≫ f) hA
    obtain ⟨h₂⟩ := IsKProjective.nonempty_homotopy_zero (biprod.inr ≫ f) hA
    simpa only [comp_zero, add_zero, ← Category.assoc,
      ← Preadditive.add_comp, biprod.total, Category.id_comp] using
      Nonempty.intro ((h₁.compLeft biprod.fst).add (h₂.compLeft biprod.snd))

/-- A binary biproduct of integer cochain complexes is K-injective exactly when
both summands are K-injective. -/
lemma isKInjective_biprod_iff (K L : CochainComplex C ℤ) :
    (K ⊞ L).IsKInjective ↔ K.IsKInjective ∧ L.IsKInjective := by
  constructor
  · intro h
    let _ := h
    exact ⟨IsKInjective.of_retract (biprod.inl : K ⟶ K ⊞ L) biprod.fst (by simp),
      IsKInjective.of_retract (biprod.inr : L ⟶ K ⊞ L) biprod.snd (by simp)⟩
  · rintro ⟨hK, hL⟩
    let _ := hK
    let _ := hL
    constructor
    intro A f hA
    obtain ⟨h₁⟩ := IsKInjective.nonempty_homotopy_zero (f ≫ biprod.fst) hA
    obtain ⟨h₂⟩ := IsKInjective.nonempty_homotopy_zero (f ≫ biprod.snd) hA
    simpa only [zero_comp, add_zero, Category.assoc,
      ← Preadditive.comp_add, biprod.total, Category.comp_id] using
      Nonempty.intro ((h₁.compRight biprod.inl).add (h₂.compRight biprod.inr))

end CochainComplex
