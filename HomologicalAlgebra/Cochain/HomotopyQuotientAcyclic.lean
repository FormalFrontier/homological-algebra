/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Cochain.HomotopyQuotientQuasiIso
public import HomologicalAlgebra.QuasiIsoZero

/-!
# Acyclic K-complexes in the homotopy category

A K-projective cochain complex is exact in every degree if and only if its
image in the canonical homotopy category is zero. The same criterion holds
for K-injective cochain complexes.
-/

@[expose] public section

universe u v

open CategoryTheory Category Limits HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A K-projective cochain complex is acyclic exactly when its image in the
canonical homotopy category is a zero object. -/
lemma IsKProjective.acyclic_iff_isZero_quotient_obj
    (K : CochainComplex C ℤ) [K.IsKProjective] :
    (∀ n : ℤ, K.ExactAt n) ↔
      IsZero ((HomotopyCategory.quotient C (.up ℤ)).obj K) := by
  have hq := IsKProjective.quasiIso_iff_isIso_quotient_map (0 : K ⟶ K)
  rw [Functor.map_zero] at hq
  have he : QuasiIso (0 : K ⟶ K) ↔ ∀ n : ℤ, K.ExactAt n := by
    simpa only [and_self] using (HomologicalComplex.quasiIso_zero_iff_exactAt K K)
  exact he.symm.trans (hq.trans (by
    simpa only [and_self] using (CategoryTheory.Limits.isIso_zero_iff_isZero
      ((HomotopyCategory.quotient C (.up ℤ)).obj K)
      ((HomotopyCategory.quotient C (.up ℤ)).obj K))))

/-- A K-injective cochain complex is acyclic exactly when its image in the
canonical homotopy category is a zero object. -/
lemma IsKInjective.acyclic_iff_isZero_quotient_obj
    (K : CochainComplex C ℤ) [K.IsKInjective] :
    (∀ n : ℤ, K.ExactAt n) ↔
      IsZero ((HomotopyCategory.quotient C (.up ℤ)).obj K) := by
  have hq := IsKInjective.quasiIso_iff_isIso_quotient_map (0 : K ⟶ K)
  rw [Functor.map_zero] at hq
  have he : QuasiIso (0 : K ⟶ K) ↔ ∀ n : ℤ, K.ExactAt n := by
    simpa only [and_self] using (HomologicalComplex.quasiIso_zero_iff_exactAt K K)
  exact he.symm.trans (hq.trans (by
    simpa only [and_self] using (CategoryTheory.Limits.isIso_zero_iff_isZero
      ((HomotopyCategory.quotient C (.up ℤ)).obj K)
      ((HomotopyCategory.quotient C (.up ℤ)).obj K))))

end CochainComplex
