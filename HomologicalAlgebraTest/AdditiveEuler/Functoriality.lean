/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.AdditiveEuler.Functoriality
public import HomologicalAlgebraTest.AdditiveEuler

/-!
# Public clients for exact-sequence and exact-functor Euler identities

The rational line in degree `-1` gives a nonzero, negatively signed value in
`ZMod 3`. The split short exact sequence of complexes below is constructed in
the native category of chain complexes; the mapped examples use its native
exact identity functor and homology comparison.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.AdditiveEuler
open scoped BigOperators ZeroObject

namespace HomologicalAlgebraTest.AdditiveEuler

def negativeSplit : ShortComplex (ChainComplex (FGModuleCat ℚ) ℤ) :=
  ShortComplex.mk (𝟙 rationalNegativeSingle)
    (0 : rationalNegativeSingle ⟶ (0 : ChainComplex (FGModuleCat ℚ) ℤ)) (by simp)

theorem negativeSplit_shortExact : negativeSplit.ShortExact :=
  { exact := (negativeSplit.exact_iff_epi rfl).2 (by dsimp [negativeSplit]; infer_instance)
    mono_f := by dsimp [negativeSplit]; infer_instance
    epi_g := by dsimp [negativeSplit]; infer_instance }

theorem negativeSplit_term_sum :
    (∑ j ∈ Finset.Icc (-1 : ℤ) (-1),
      (Int.negOnePow j : ℤ) • modularLength (negativeSplit.X₂.X j)) =
      (∑ j ∈ Finset.Icc (-1 : ℤ) (-1),
        (Int.negOnePow j : ℤ) • modularLength (negativeSplit.X₁.X j)) +
        ∑ j ∈ Finset.Icc (-1 : ℤ) (-1),
          (Int.negOnePow j : ℤ) • modularLength (negativeSplit.X₃.X j) :=
  term_sum_additive_of_shortExact modularLength modularLength_ses negativeSplit
    negativeSplit_shortExact (-1) (-1)

theorem negativeSplit_nonzero :
    (∑ j ∈ Finset.Icc (-1 : ℤ) (-1),
      (Int.negOnePow j : ℤ) • modularLength (negativeSplit.X₂.X j)) = 2 := by
  change (∑ j ∈ Finset.Icc (-1 : ℤ) (-1),
    (Int.negOnePow j : ℤ) • modularLength (rationalNegativeSingle.X j)) = 2
  exact modularNegativeSingle_term_sum

theorem negativeSplit_homology_sum :
    (∑ j ∈ Finset.Icc (-1 : ℤ) (-1),
      (Int.negOnePow j : ℤ) • modularLength (negativeSplit.X₂.homology j)) =
      (∑ j ∈ Finset.Icc (-1 : ℤ) (-1),
        (Int.negOnePow j : ℤ) • modularLength (negativeSplit.X₁.homology j)) +
        ∑ j ∈ Finset.Icc (-1 : ℤ) (-1),
          (Int.negOnePow j : ℤ) • modularLength (negativeSplit.X₃.homology j) := by
  apply homology_sum_additive_of_shortExact modularLength modularLength_ses
    negativeSplit negativeSplit_shortExact (-1) (-1) (by omega)
  · intro j hj
    exact rationalNegativeSingle_isZero j (by omega)
  · intro j hj
    exact rationalNegativeSingle_isZero j (by omega)
  · intro j _
    change IsZero ((HomologicalComplex.eval (FGModuleCat ℚ)
      (ComplexShape.down ℤ) j).obj (0 : ChainComplex (FGModuleCat ℚ) ℤ))
    exact (HomologicalComplex.eval (FGModuleCat ℚ)
      (ComplexShape.down ℤ) j).map_isZero (isZero_zero _)

theorem identity_negative_homology_sum :
    (∑ j ∈ Finset.Icc (-1 : ℤ) (-1), (Int.negOnePow j : ℤ) •
      modularLength ((((𝟭 (FGModuleCat ℚ)).mapHomologicalComplex
        (ComplexShape.down ℤ)).obj rationalNegativeSingle).homology j)) = 2 := by
  rw [homology_sum_map (𝟭 (FGModuleCat ℚ)) modularLength modularLength_ses
    rationalNegativeSingle (-1) (-1)]
  simpa only [Functor.id_obj] using modularNegativeSingle_homology_sum

theorem identity_negative_euler_sum :
    (∑ j ∈ Finset.Icc (-1 : ℤ) (-1), (Int.negOnePow j : ℤ) •
      modularLength ((𝟭 (FGModuleCat ℚ)).obj (rationalNegativeSingle.X j))) = 2 := by
  have hK : ∀ j, j < (-1 : ℤ) ∨ (-1 : ℤ) < j →
      IsZero (rationalNegativeSingle.X j) := by
    intro j hj
    exact rationalNegativeSingle_isZero j (by omega)
  rw [(euler_map_bounded (𝟭 (FGModuleCat ℚ)) modularLength modularLength_ses
    rationalNegativeSingle (-1) (-1) (by omega) hK).2]
  simpa only [Functor.id_obj] using modularNegativeSingle_homology_sum

end HomologicalAlgebraTest.AdditiveEuler
