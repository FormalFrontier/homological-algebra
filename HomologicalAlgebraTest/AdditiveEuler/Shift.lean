/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.AdditiveEuler.Shift
public import HomologicalAlgebraTest.AdditiveEuler
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Tactic.NormNum

/-!
# Public clients of finite-support and native cochain-shift Euler sums

The rational line in cochain degree `-1` has nonzero signed value `2` in
`ZMod 3`. Shifting it by `1` or `-1` changes its signed value to `1`.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.AdditiveEuler
open scoped BigOperators ZeroObject

namespace HomologicalAlgebraTest.AdditiveEuler

def cochainModularLength (M : FGModuleCat ℚ) : ZMod 3 :=
  Int.castAddHom (ZMod 3) (lengthInvariant ℚ M)

theorem cochainModularLength_ses (S : ShortComplex (FGModuleCat ℚ))
    (hS : S.ShortExact) :
    cochainModularLength S.X₂ =
      cochainModularLength S.X₁ + cochainModularLength S.X₃ :=
  postcompose_ses (lengthInvariant ℚ) (lengthInvariant_ses ℚ)
    (Int.castAddHom (ZMod 3)) S hS

def cochainRationalNegative : CochainComplex (FGModuleCat ℚ) ℤ :=
  (HomologicalComplex.single (FGModuleCat ℚ) (ComplexShape.up ℤ) (-1)).obj
    (FGModuleCat.of ℚ ℚ)

theorem cochainRationalNegative_isZero (j : ℤ) (hj : j ≠ -1) :
    IsZero (cochainRationalNegative.X j) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (-1)
    (FGModuleCat.of ℚ ℚ) j hj

theorem cochainRationalNegative_term_sum :
    (∑ j ∈ Finset.Icc (-1 : ℤ) (-1),
      (Int.negOnePow j : ℤ) • cochainModularLength (cochainRationalNegative.X j)) = 2 := by
  simp only [Finset.Icc_self, Finset.sum_singleton]
  rw [show cochainRationalNegative.X (-1) = FGModuleCat.of ℚ ℚ from
    HomologicalComplex.single_obj_X_self (ComplexShape.up ℤ) (-1) (FGModuleCat.of ℚ ℚ)]
  rw [show cochainModularLength (FGModuleCat.of ℚ ℚ) = (1 : ZMod 3) by
    simp [cochainModularLength, rational_line_length]]
  norm_num; decide

theorem cochainRationalNegative_homology_sum :
    (∑ j ∈ Finset.Icc (-1 : ℤ) (-1),
      (Int.negOnePow j : ℤ) • cochainModularLength (cochainRationalNegative.homology j)) = 2 := by
  have h : cochainModularLength (cochainRationalNegative.homology (-1)) =
      cochainModularLength (cochainRationalNegative.X (-1)) := by
    calc
      _ = cochainModularLength (FGModuleCat.of ℚ ℚ) :=
        invariant_iso cochainModularLength cochainModularLength_ses
          (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ)
            (-1) (FGModuleCat.of ℚ ℚ))
      _ = _ := congrArg cochainModularLength
        (HomologicalComplex.single_obj_X_self (ComplexShape.up ℤ)
          (-1) (FGModuleCat.of ℚ ℚ)).symm
  simp only [Finset.Icc_self, Finset.sum_singleton]
  rw [h]
  simpa only [Finset.Icc_self, Finset.sum_singleton] using
    cochainRationalNegative_term_sum

theorem cochainRationalNegative_enlarged :
    (∑ j ∈ Finset.Icc (-4 : ℤ) 2,
      (Int.negOnePow j : ℤ) • cochainModularLength (cochainRationalNegative.X j)) = 2 := by
  rw [term_sum_eq_of_support cochainModularLength cochainModularLength_ses
    cochainRationalNegative (-4) 2 (-1) (-1)
    (fun j hj => cochainRationalNegative_isZero j (by omega))
    (fun j hj => cochainRationalNegative_isZero j (by omega))]
  exact cochainRationalNegative_term_sum

theorem cochainRationalNegative_positive_support :
    ∀ i, i < (-2 : ℤ) ∨ (-2 : ℤ) < i →
      IsZero ((cochainRationalNegative⟦(1 : ℤ)⟧).X i) := by
  simpa using cochain_shift_term_support cochainRationalNegative (-1) (-1) 1
    (fun j hj => cochainRationalNegative_isZero j (by omega))

theorem cochainRationalNegative_positive_term_sum :
    (∑ i ∈ Finset.Icc (-2 : ℤ) (-2),
      (Int.negOnePow i : ℤ) •
        cochainModularLength ((cochainRationalNegative⟦(1 : ℤ)⟧).X i)) = 1 := by
  have h := cochain_shift_term_sum cochainModularLength cochainRationalNegative (-1) (-1) 1
  norm_num only at h
  rw [h, cochainRationalNegative_term_sum]
  norm_num; decide

theorem cochainRationalNegative_negative_term_sum :
    (∑ i ∈ Finset.Icc (0 : ℤ) 0,
      (Int.negOnePow i : ℤ) •
        cochainModularLength ((cochainRationalNegative⟦(-1 : ℤ)⟧).X i)) = 1 := by
  have h := cochain_shift_term_sum cochainModularLength cochainRationalNegative (-1) (-1) (-1)
  norm_num only at h
  rw [h, cochainRationalNegative_term_sum]
  norm_num; decide

def cochainRationalNegative_positive_homology_iso :
    (cochainRationalNegative⟦(1 : ℤ)⟧).homology (-2) ≅
      cochainRationalNegative.homology (-1) := by
  simpa using cochain_shift_homology_iso cochainRationalNegative 1 (-2)

theorem cochainRationalNegative_positive_homology_comparison :
    cochainModularLength ((cochainRationalNegative⟦(1 : ℤ)⟧).homology (-2)) =
      cochainModularLength (cochainRationalNegative.homology (-1)) :=
  invariant_iso cochainModularLength cochainModularLength_ses
    cochainRationalNegative_positive_homology_iso

theorem cochainRationalNegative_positive_homology_sum :
    (∑ i ∈ Finset.Icc (-2 : ℤ) (-2),
      (Int.negOnePow i : ℤ) •
        cochainModularLength ((cochainRationalNegative⟦(1 : ℤ)⟧).homology i)) = 1 := by
  have h := cochain_shift_homology_sum cochainModularLength cochainModularLength_ses
    cochainRationalNegative (-1) (-1) 1
  norm_num only at h
  rw [h, cochainRationalNegative_homology_sum]
  norm_num; decide

theorem cochainRationalNegative_negative_homology_sum :
    (∑ i ∈ Finset.Icc (0 : ℤ) 0,
      (Int.negOnePow i : ℤ) •
        cochainModularLength ((cochainRationalNegative⟦(-1 : ℤ)⟧).homology i)) = 1 := by
  have h := cochain_shift_homology_sum cochainModularLength cochainModularLength_ses
    cochainRationalNegative (-1) (-1) (-1)
  norm_num only at h
  rw [h, cochainRationalNegative_homology_sum]
  norm_num; decide

theorem empty_interval_support (f : ℤ → ZMod 3)
    (hf : ∀ i, i < 1 ∨ 0 < i → f i = 0) :
    (∑ i ∈ Finset.Icc (1 : ℤ) 0, (Int.negOnePow i : ℤ) • f i) =
      ∑ i ∈ Finset.Icc (-3 : ℤ) 5, (Int.negOnePow i : ℤ) • f i :=
  signed_sum_eq_of_support f 1 0 (-3) 5
    hf (fun i _ => hf i (by omega))

end HomologicalAlgebraTest.AdditiveEuler
