/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.AdditiveEuler.Length
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Public-import tests for additive Euler characteristics

The negative-degree rational line has Euler value `-1`; additive postcomposition
into `ZMod 3` has value `2`, distinct from zero and one.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.AdditiveEuler
open scoped BigOperators ZeroObject

namespace HomologicalAlgebraTest.AdditiveEuler

theorem rational_length_eq_finrank (M : FGModuleCat ℚ) :
    lengthInvariant ℚ M = (Module.finrank ℚ M : ℤ) := by
  simp [lengthInvariant, Module.length_eq_finrank]

theorem rational_line_length :
    lengthInvariant ℚ (FGModuleCat.of ℚ ℚ) = 1 := by
  rw [rational_length_eq_finrank]
  simp

def rationalNegativeSingle : ChainComplex (FGModuleCat ℚ) ℤ :=
  (HomologicalComplex.single (FGModuleCat ℚ) (ComplexShape.down ℤ) (-1)).obj
    (FGModuleCat.of ℚ ℚ)

theorem rationalNegativeSingle_isZero (j : ℤ) (hj : j ≠ -1) :
    IsZero (rationalNegativeSingle.X j) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℤ) (-1)
    (FGModuleCat.of ℚ ℚ) j hj

theorem rationalNegativeSingle_term_sum :
    (∑ j ∈ Finset.Icc (-1 : ℤ) (-1),
      (Int.negOnePow j : ℤ) • lengthInvariant ℚ (rationalNegativeSingle.X j)) = -1 := by
  simp only [Finset.Icc_self, Finset.sum_singleton]
  rw [show rationalNegativeSingle.X (-1) = FGModuleCat.of ℚ ℚ from
    HomologicalComplex.single_obj_X_self (ComplexShape.down ℤ) (-1) (FGModuleCat.of ℚ ℚ)]
  rw [rational_line_length]
  norm_num

theorem rationalNegativeSingle_euler :
    (∑ j ∈ Finset.Icc (-1 : ℤ) (-1),
      (Int.negOnePow j : ℤ) • lengthInvariant ℚ (rationalNegativeSingle.X j)) =
    ∑ j ∈ Finset.Icc (-1 : ℤ) (-1),
      (Int.negOnePow j : ℤ) • lengthInvariant ℚ (rationalNegativeSingle.homology j) := by
  apply euler_eq_homology_of_bounded (lengthInvariant ℚ)
    (lengthInvariant_ses ℚ) rationalNegativeSingle (-1) (-1) (by omega)
  intro j hj
  exact rationalNegativeSingle_isZero j (by omega)

theorem rationalNegativeSingle_homology_sum :
    (∑ j ∈ Finset.Icc (-1 : ℤ) (-1),
      (Int.negOnePow j : ℤ) • lengthInvariant ℚ (rationalNegativeSingle.homology j)) =
      -1 := by
  rw [← rationalNegativeSingle_euler, rationalNegativeSingle_term_sum]

def modularLength (M : FGModuleCat ℚ) : ZMod 3 :=
  Int.castAddHom (ZMod 3) (lengthInvariant ℚ M)

theorem modularLength_ses (S : ShortComplex (FGModuleCat ℚ)) (hS : S.ShortExact) :
    modularLength S.X₂ = modularLength S.X₁ + modularLength S.X₃ :=
  postcompose_ses (lengthInvariant ℚ) (lengthInvariant_ses ℚ)
    (Int.castAddHom (ZMod 3)) S hS

theorem modularNegativeSingle_term_sum :
    (∑ j ∈ Finset.Icc (-1 : ℤ) (-1),
      (Int.negOnePow j : ℤ) • modularLength (rationalNegativeSingle.X j)) = 2 := by
  simp only [Finset.Icc_self, Finset.sum_singleton]
  rw [show rationalNegativeSingle.X (-1) = FGModuleCat.of ℚ ℚ from
    HomologicalComplex.single_obj_X_self (ComplexShape.down ℤ) (-1) (FGModuleCat.of ℚ ℚ)]
  rw [show modularLength (FGModuleCat.of ℚ ℚ) = (1 : ZMod 3) by
    simp [modularLength, rational_line_length]]
  norm_num; decide

theorem modularNegativeSingle_homology_sum :
    (∑ j ∈ Finset.Icc (-1 : ℤ) (-1),
      (Int.negOnePow j : ℤ) • modularLength (rationalNegativeSingle.homology j)) = 2 := by
  rw [← euler_eq_homology_of_bounded modularLength modularLength_ses
    rationalNegativeSingle (-1) (-1) (by omega)
    (fun j hj => rationalNegativeSingle_isZero j (by omega))]
  exact modularNegativeSingle_term_sum

theorem modularNegativeSingle_ne_zero :
    (∑ j ∈ Finset.Icc (-1 : ℤ) (-1),
      (Int.negOnePow j : ℤ) • modularLength (rationalNegativeSingle.X j)) ≠ 0 := by
  rw [modularNegativeSingle_term_sum]
  decide

theorem modularNegativeSingle_ne_one :
    (∑ j ∈ Finset.Icc (-1 : ℤ) (-1),
      (Int.negOnePow j : ℤ) • modularLength (rationalNegativeSingle.X j)) ≠ 1 := by
  rw [modularNegativeSingle_term_sum]
  decide

end HomologicalAlgebraTest.AdditiveEuler
