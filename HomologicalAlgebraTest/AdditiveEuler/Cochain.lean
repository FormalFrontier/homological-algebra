/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.AdditiveEuler.Cochain
public import HomologicalAlgebraTest.AdditiveEuler.Shift
import Mathlib.Tactic.NormNum

/-!
# Native cochain Euler clients

The rational singleton tests a negative signed degree and torsion-valued
invariant. A native two-term cochain complex with identity differential tests
the nonzero outgoing boundary image and full-interval cancellation.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.AdditiveEuler
open scoped BigOperators ZeroObject

namespace HomologicalAlgebraTest.AdditiveEuler

theorem cochain_negative_euler_homology :
    (∑ j ∈ Finset.Icc (-1 : ℤ) (-1),
      (Int.negOnePow j : ℤ) • cochainModularLength
        (cochainRationalNegative.homology j)) = 2 := by
  rw [← cochain_euler_eq_homology_of_bounded cochainModularLength
    cochainModularLength_ses cochainRationalNegative (-1) (-1) (by omega)
    (fun j hj => cochainRationalNegative_isZero j (by omega))]
  exact cochainRationalNegative_term_sum

theorem cochain_shifted_euler_homology :
    (∑ j ∈ Finset.Icc (-2 : ℤ) (-2),
      (Int.negOnePow j : ℤ) • cochainModularLength
        ((cochainRationalNegative⟦(1 : ℤ)⟧).homology j)) = 1 := by
  rw [← cochain_euler_eq_homology_of_bounded cochainModularLength
    cochainModularLength_ses (cochainRationalNegative⟦(1 : ℤ)⟧)
    (-2) (-2) (by omega) cochainRationalNegative_positive_support]
  exact cochainRationalNegative_positive_term_sum

@[expose] def identityTerms (j : ℤ) : FGModuleCat ℚ :=
  if j = 0 ∨ j = 1 then FGModuleCat.of ℚ ℚ else 0

@[expose] def identityDifferential (j : ℤ) : identityTerms j ⟶ identityTerms (j + 1) := by
  classical
  by_cases hj : j = 0
  · subst j
    change FGModuleCat.of ℚ ℚ ⟶ FGModuleCat.of ℚ ℚ
    exact 𝟙 _
  · exact 0

theorem identityDifferential_sq (j : ℤ) :
    identityDifferential j ≫ identityDifferential (j + 1) = 0 := by
  by_cases hj : j = 0
  · subst j
    simp [identityDifferential]
  · simp [identityDifferential, hj]

@[expose] def identityCochain : CochainComplex (FGModuleCat ℚ) ℤ :=
  CochainComplex.of identityTerms identityDifferential identityDifferential_sq

theorem identityCochain_isZero (j : ℤ) (hzero : j ≠ 0) (hone : j ≠ 1) :
    IsZero (identityCochain.X j) := by
  change IsZero (identityTerms j)
  simpa [identityTerms, hzero, hone] using isZero_zero (FGModuleCat ℚ)

theorem identityCochain_d_zero :
    identityCochain.d 0 1 = 𝟙 (FGModuleCat.of ℚ ℚ) := by
  change identityDifferential 0 = 𝟙 (FGModuleCat.of ℚ ℚ)
  rfl

theorem identityCochain_image_nonzero :
    lengthInvariant ℚ (image (identityCochain.d 0 1)) = 1 := by
  have hmono : Mono (identityCochain.d 0 1) := by
    change Mono (identityDifferential 0)
    change Mono (𝟙 (FGModuleCat.of ℚ ℚ))
    infer_instance
  calc
    _ = lengthInvariant ℚ (identityCochain.X 0) :=
      invariant_iso (lengthInvariant ℚ) (lengthInvariant_ses ℚ)
        (imageMonoIsoSource (identityCochain.d 0 1))
    _ = lengthInvariant ℚ (FGModuleCat.of ℚ ℚ) := by
      congr 1
    _ = 1 := rational_line_length

theorem identityCochain_endpoint :
    lengthInvariant ℚ (identityCochain.X 0) =
      lengthInvariant ℚ (identityCochain.homology 0) + 1 := by
  have h := cochain_euler_endpoints (lengthInvariant ℚ) (lengthInvariant_ses ℚ)
    identityCochain 0 0 (by omega)
  have hzero : lengthInvariant ℚ (image (identityCochain.d (-1) 0)) = 0 :=
    image_zero_of_source (lengthInvariant ℚ) (lengthInvariant_ses ℚ) _
      (identityCochain_isZero (-1) (by omega) (by omega))
  simpa [identityCochain_image_nonzero, hzero] using h

theorem identityCochain_incoming_endpoint :
    (-1 : ℤ) • lengthInvariant ℚ (identityCochain.X 1) =
      (-1 : ℤ) • lengthInvariant ℚ (identityCochain.homology 1) +
        (-1 : ℤ) • (1 : ℤ) := by
  have h := cochain_euler_endpoints (lengthInvariant ℚ) (lengthInvariant_ses ℚ)
    identityCochain 1 1 (by omega)
  have hzero : lengthInvariant ℚ (image (identityCochain.d 1 2)) = 0 :=
    image_zero_of_target (lengthInvariant ℚ) (lengthInvariant_ses ℚ) _
      (identityCochain_isZero 2 (by omega) (by omega))
  simpa [identityCochain_image_nonzero, hzero] using h

theorem identityCochain_full_interval :
    (∑ j ∈ Finset.Icc (0 : ℤ) 1,
      (Int.negOnePow j : ℤ) • lengthInvariant ℚ (identityCochain.X j)) = 0 ∧
    (∑ j ∈ Finset.Icc (0 : ℤ) 1,
      (Int.negOnePow j : ℤ) • lengthInvariant ℚ (identityCochain.homology j)) = 0 := by
  have hterms :
      (∑ j ∈ Finset.Icc (0 : ℤ) 1,
        (Int.negOnePow j : ℤ) • lengthInvariant ℚ (identityCochain.X j)) = 0 := by
    norm_num [show Finset.Icc (0 : ℤ) 1 = {0, 1} by decide,
      identityCochain, identityTerms, rational_line_length]
  constructor
  · exact hterms
  · rw [← cochain_euler_eq_homology (lengthInvariant ℚ) (lengthInvariant_ses ℚ)
      identityCochain 0 1 (by omega)
      (by simpa using identityCochain_isZero (-1) (by omega) (by omega))
      (by simpa using identityCochain_isZero 2 (by omega) (by omega))]
    exact hterms

theorem cochain_singleton_quasiIso :
    (∑ j ∈ Finset.Icc (-1 : ℤ) (-1),
      (Int.negOnePow j : ℤ) • cochainModularLength (cochainRationalNegative.X j)) =
      ∑ j ∈ Finset.Icc (-1 : ℤ) (-1),
        (Int.negOnePow j : ℤ) • cochainModularLength (cochainRationalNegative.X j) := by
  exact cochain_euler_quasiIso cochainModularLength cochainModularLength_ses
    cochainRationalNegative cochainRationalNegative (𝟙 _) (-1) (-1) (by omega)
    (fun j hj => cochainRationalNegative_isZero j (by omega))
    (fun j hj => cochainRationalNegative_isZero j (by omega))

end HomologicalAlgebraTest.AdditiveEuler
