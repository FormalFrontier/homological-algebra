/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.AdditiveEuler.HomologySupport
public import HomologicalAlgebra.AdditiveEuler.Shift
public import HomologicalAlgebraTest.AdditiveEuler.Cochain
public import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Tactic.NormNum

/-!
# A nonsplit cochain sequence with nonzero connecting map

The inclusion of a singleton in degree one into the identity-differential
disk, and the projection onto a singleton in degree zero, are degreewise short
exact. Their cohomology has a nonzero connecting isomorphism, so pointwise
homology additivity fails even though the signed interval sum is additive.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.AdditiveEuler
open scoped BigOperators ZeroObject

namespace HomologicalAlgebraTest.AdditiveEuler

private abbrev line : FGModuleCat ℚ := FGModuleCat.of ℚ ℚ

def diskTop : CochainComplex (FGModuleCat ℚ) ℤ :=
  (HomologicalComplex.single (FGModuleCat ℚ) (ComplexShape.up ℤ) 1).obj line

def diskBottom : CochainComplex (FGModuleCat ℚ) ℤ :=
  (HomologicalComplex.single (FGModuleCat ℚ) (ComplexShape.up ℤ) 0).obj line

theorem diskTop_isZero (j : ℤ) (hj : j ≠ 1) : IsZero (diskTop.X j) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 1 line j hj

theorem diskBottom_isZero (j : ℤ) (hj : j ≠ 0) : IsZero (diskBottom.X j) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 line j hj

theorem diskTop_homology_isZero (j : ℤ) (hj : j ≠ 1) :
    IsZero (diskTop.homology j) := by
  unfold diskTop
  exact HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 1 line j hj

theorem diskBottom_homology_isZero (j : ℤ) (hj : j ≠ 0) :
    IsZero (diskBottom.homology j) := by
  unfold diskBottom
  exact HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 line j hj

def diskInclusion : diskTop ⟶ identityCochain :=
  HomologicalComplex.mkHomFromSingle (𝟙 line) (by
    intro j hj
    have hj' : j = 2 := by
      simp only [ComplexShape.up_Rel] at hj
      omega
    subst j
    exact (identityCochain_isZero 2 (by omega) (by omega)).eq_of_tgt _ _)

def diskProjection : identityCochain ⟶ diskBottom :=
  HomologicalComplex.mkHomToSingle (𝟙 line) (by
    intro j hj
    have hj' : j = -1 := by
      simp only [ComplexShape.up_Rel] at hj
      omega
    subst j
    exact (identityCochain_isZero (-1) (by omega) (by omega)).eq_of_src _ _)

def diskSequence : ShortComplex (CochainComplex (FGModuleCat ℚ) ℤ) :=
  ShortComplex.mk diskInclusion diskProjection (by
    apply HomologicalComplex.hom_ext
    intro j
    change diskInclusion.f j ≫ diskProjection.f j = 0
    by_cases hj : j = 1
    · subst j
      exact (diskBottom_isZero 1 (by omega)).eq_of_tgt _ _
    · exact (diskTop_isZero j hj).eq_of_src _ _)

theorem diskSequence_shortExact : diskSequence.ShortExact := by
  apply (HomologicalComplex.shortExact_iff_degreewise_shortExact diskSequence).2
  intro j
  let T := diskSequence.map
    (HomologicalComplex.eval (FGModuleCat ℚ) (ComplexShape.up ℤ) j)
  by_cases hzero : j = 0
  · subst j
    have htop : IsZero T.X₁ := diskTop_isZero 0 (by omega)
    have hg : IsIso T.g := by
      change IsIso (diskProjection.f 0)
      change IsIso ((𝟙 line) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 line).inv)
      infer_instance
    have hzero_f : T.f = 0 := htop.eq_of_src _ _
    exact { exact := (T.exact_iff_mono hzero_f).2 (by infer_instance)
            mono_f := htop.mono _
            epi_g := by infer_instance }
  by_cases hone : j = 1
  · subst j
    have hbottom : IsZero T.X₃ := diskBottom_isZero 1 (by omega)
    have hf : IsIso T.f := by
      change IsIso (diskInclusion.f 1)
      change IsIso ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1 line).hom ≫
        (𝟙 line))
      infer_instance
    have hzero_g : T.g = 0 := hbottom.eq_of_tgt _ _
    exact { exact := (T.exact_iff_epi hzero_g).2 (by infer_instance)
            mono_f := by infer_instance
            epi_g := hbottom.epi _ }
  · have htop : IsZero T.X₁ := diskTop_isZero j hone
    have hdisk : IsZero T.X₂ := identityCochain_isZero j hzero hone
    have hbottom : IsZero T.X₃ := diskBottom_isZero j hzero
    have hzero_f : T.f = 0 := htop.eq_of_src _ _
    exact { exact := (T.exact_iff_mono hzero_f).2 (hdisk.mono _)
            mono_f := htop.mono _
            epi_g := hbottom.epi _ }

theorem identityCochain_acyclic : identityCochain.Acyclic := by
  intro j
  by_cases hzero : j = 0
  · subst j
    apply (identityCochain.exactAt_iff' (-1) 0 1 (by simp) (by simp)).2
    let T := identityCochain.sc' (-1) 0 1
    have hf : T.f = 0 := (identityCochain_isZero (-1) (by omega) (by omega)).eq_of_src _ _
    have hg : IsIso T.g := by
      change IsIso (identityCochain.d 0 1)
      rw [identityCochain_d_zero]
      exact (inferInstance : IsIso (𝟙 line))
    exact (T.exact_iff_mono hf).2 (by infer_instance)
  by_cases hone : j = 1
  · subst j
    apply (identityCochain.exactAt_iff' 0 1 2 (by simp) (by simp)).2
    let T := identityCochain.sc' 0 1 2
    have hg : T.g = 0 := (identityCochain_isZero 2 (by omega) (by omega)).eq_of_tgt _ _
    have hf : IsIso T.f := by
      change IsIso (identityCochain.d 0 1)
      rw [identityCochain_d_zero]
      exact (inferInstance : IsIso (𝟙 line))
    exact (T.exact_iff_epi hg).2 (by infer_instance)
  exact HomologicalComplex.ExactAt.of_isZero (identityCochain_isZero j hzero hone)

theorem diskSequence_delta_isIso : IsIso (diskSequence_shortExact.δ 0 1 (by simp)) :=
  diskSequence_shortExact.isIso_δ 0 1 (by simp)
    ((identityCochain_acyclic 0).isZero_homology)
    ((identityCochain_acyclic 1).isZero_homology)

theorem diskTop_homology_length : lengthInvariant ℚ (diskTop.homology 1) = 1 := by
  unfold diskTop
  rw [invariant_iso (lengthInvariant ℚ) (lengthInvariant_ses ℚ)
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 1 line)]
  exact rational_line_length

theorem diskBottom_homology_length : lengthInvariant ℚ (diskBottom.homology 0) = 1 := by
  unfold diskBottom
  rw [invariant_iso (lengthInvariant ℚ) (lengthInvariant_ses ℚ)
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 line)]
  exact rational_line_length

theorem diskSequence_boundary_length :
    lengthInvariant ℚ (cochain_homology_boundary_image diskSequence
      diskSequence_shortExact 0) = 1 := by
  unfold cochain_homology_boundary_image
  have hmono : Mono (diskSequence_shortExact.δ 0 (0 + 1) (by simp)) :=
    diskSequence_shortExact.mono_δ 0 (0 + 1) (by simp)
      ((identityCochain_acyclic 0).isZero_homology)
  rw [invariant_iso (lengthInvariant ℚ) (lengthInvariant_ses ℚ)
    (@imageMonoIsoSource _ _ _ _
      (diskSequence_shortExact.δ 0 (0 + 1) (by simp)) hmono)]
  change lengthInvariant ℚ (diskBottom.homology 0) = 1
  exact diskBottom_homology_length

theorem diskSequence_pointwise_failure :
    lengthInvariant ℚ (diskSequence.X₂.homology 0) ≠
      lengthInvariant ℚ (diskSequence.X₁.homology 0) +
        lengthInvariant ℚ (diskSequence.X₃.homology 0) := by
  change lengthInvariant ℚ (identityCochain.homology 0) ≠
    lengthInvariant ℚ (diskTop.homology 0) + lengthInvariant ℚ (diskBottom.homology 0)
  have hmid : lengthInvariant ℚ (identityCochain.homology 0) = 0 :=
    invariant_of_isZero (lengthInvariant ℚ) (lengthInvariant_ses ℚ)
      ((identityCochain_acyclic 0).isZero_homology)
  have htop : lengthInvariant ℚ (diskTop.homology 0) = 0 := by
    exact invariant_of_isZero (lengthInvariant ℚ) (lengthInvariant_ses ℚ)
      (diskTop_homology_isZero 0 (by omega))
  rw [hmid, htop, diskBottom_homology_length]
  norm_num

theorem diskSequence_singleton_endpoint :
    lengthInvariant ℚ (diskSequence.X₂.homology 0) =
      lengthInvariant ℚ (diskSequence.X₁.homology 0) +
      lengthInvariant ℚ (diskSequence.X₃.homology 0) -
      lengthInvariant ℚ (cochain_homology_boundary_image diskSequence
        diskSequence_shortExact (-1)) -
      lengthInvariant ℚ (cochain_homology_boundary_image diskSequence
        diskSequence_shortExact 0) := by
  have h := cochain_homology_euler_endpoints (lengthInvariant ℚ)
    (lengthInvariant_ses ℚ) diskSequence diskSequence_shortExact 0 0 (le_refl 0)
  have hsign : (Int.negOnePow (0 : ℤ) : ℤ) = 1 := by norm_num
  simpa only [Finset.Icc_self, Finset.sum_singleton, hsign,
    one_zsmul, zero_sub] using h

theorem diskSequence_singleton_endpoint_correction :
    lengthInvariant ℚ (diskSequence.X₂.homology 0) =
      lengthInvariant ℚ (diskSequence.X₁.homology 0) +
      lengthInvariant ℚ (diskSequence.X₃.homology 0) -
      lengthInvariant ℚ (cochain_homology_boundary_image diskSequence
        diskSequence_shortExact 0) := by
  have hleft : lengthInvariant ℚ (cochain_homology_boundary_image diskSequence
      diskSequence_shortExact (-1)) = 0 := by
    apply image_zero_of_source (lengthInvariant ℚ) (lengthInvariant_ses ℚ) _
    change IsZero (diskBottom.homology (-1))
    exact diskBottom_homology_isZero (-1) (by omega)
  simpa only [hleft, sub_zero] using diskSequence_singleton_endpoint

theorem diskSequence_singleton_numeric : (0 : ℤ) = 1 - 1 := by
  have hmid : lengthInvariant ℚ (diskSequence.X₂.homology 0) = 0 :=
    invariant_of_isZero (lengthInvariant ℚ) (lengthInvariant_ses ℚ)
      ((identityCochain_acyclic 0).isZero_homology)
  have htop : lengthInvariant ℚ (diskSequence.X₁.homology 0) = 0 :=
    invariant_of_isZero (lengthInvariant ℚ) (lengthInvariant_ses ℚ)
      (diskTop_homology_isZero 0 (by omega))
  have hbottom : lengthInvariant ℚ (diskSequence.X₃.homology 0) = 1 := by
    change lengthInvariant ℚ (diskBottom.homology 0) = 1
    exact diskBottom_homology_length
  have h := diskSequence_singleton_endpoint_correction
  rw [hmid, htop, hbottom, diskSequence_boundary_length] at h
  simpa only [zero_add] using h

theorem diskSequence_endpoint_correction :
    (∑ i ∈ Finset.Icc (-1 : ℤ) 0,
      (Int.negOnePow i : ℤ) • lengthInvariant ℚ (diskSequence.X₂.homology i)) =
      (∑ i ∈ Finset.Icc (-1 : ℤ) 0,
        (Int.negOnePow i : ℤ) • lengthInvariant ℚ (diskSequence.X₁.homology i)) +
      (∑ i ∈ Finset.Icc (-1 : ℤ) 0,
        (Int.negOnePow i : ℤ) • lengthInvariant ℚ (diskSequence.X₃.homology i)) -
      (Int.negOnePow (-1 : ℤ) : ℤ) •
        lengthInvariant ℚ (cochain_homology_boundary_image diskSequence
          diskSequence_shortExact (-2)) -
      (Int.negOnePow (0 : ℤ) : ℤ) •
        lengthInvariant ℚ (cochain_homology_boundary_image diskSequence
          diskSequence_shortExact 0) :=
  cochain_homology_euler_endpoints (lengthInvariant ℚ)
    (lengthInvariant_ses ℚ) diskSequence diskSequence_shortExact (-1) 0 (by omega)

theorem diskSequence_homology_additive :
    (∑ i ∈ Finset.Icc (0 : ℤ) 1,
      (Int.negOnePow i : ℤ) • lengthInvariant ℚ (diskSequence.X₂.homology i)) =
      (∑ i ∈ Finset.Icc (0 : ℤ) 1,
        (Int.negOnePow i : ℤ) • lengthInvariant ℚ (diskSequence.X₁.homology i)) +
        (∑ i ∈ Finset.Icc (0 : ℤ) 1,
          (Int.negOnePow i : ℤ) • lengthInvariant ℚ (diskSequence.X₃.homology i)) := by
  have hbelow : IsZero (diskSequence.X₃.homology (0 - 1)) := by
    change IsZero (diskBottom.homology (-1))
    exact diskBottom_homology_isZero (-1) (by omega)
  have habove : IsZero (diskSequence.X₁.homology (1 + 1)) := by
    change IsZero (diskTop.homology 2)
    exact diskTop_homology_isZero 2 (by omega)
  exact cochain_homology_sum_additive_of_endpoints (lengthInvariant ℚ)
    (lengthInvariant_ses ℚ) diskSequence diskSequence_shortExact 0 1 (by omega)
    hbelow habove

theorem diskSequence_homology_additive_supported :
    (∑ i ∈ Finset.Icc (0 : ℤ) 1,
      (Int.negOnePow i : ℤ) • lengthInvariant ℚ (diskSequence.X₂.homology i)) =
      (∑ i ∈ Finset.Icc (0 : ℤ) 1,
        (Int.negOnePow i : ℤ) • lengthInvariant ℚ (diskSequence.X₁.homology i)) +
        (∑ i ∈ Finset.Icc (0 : ℤ) 1,
          (Int.negOnePow i : ℤ) • lengthInvariant ℚ (diskSequence.X₃.homology i)) := by
  exact cochain_homology_sum_additive_of_supported (lengthInvariant ℚ)
    (lengthInvariant_ses ℚ) diskSequence diskSequence_shortExact 0 1 (by omega)
    (by
      apply (diskBottom.isGE_iff 0).2
      intro j hj
      exact HomologicalComplex.ExactAt.of_isZero (diskBottom_isZero j (by omega)))
    (by
      apply (diskTop.isLE_iff 1).2
      intro j hj
      exact HomologicalComplex.ExactAt.of_isZero (diskTop_isZero j (by omega)))

theorem diskSequence_integer_balance : (0 : ℤ) = -1 + 1 := by
  have h := diskSequence_homology_additive
  have hmiddle :
      (∑ i ∈ Finset.Icc (0 : ℤ) 1,
        (Int.negOnePow i : ℤ) • lengthInvariant ℚ (diskSequence.X₂.homology i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    change (Int.negOnePow i : ℤ) • lengthInvariant ℚ (identityCochain.homology i) = 0
    rw [invariant_of_isZero (lengthInvariant ℚ) (lengthInvariant_ses ℚ)
      ((identityCochain_acyclic i).isZero_homology), smul_zero]
  have htopzero : lengthInvariant ℚ (diskTop.homology 0) = 0 :=
    invariant_of_isZero (lengthInvariant ℚ) (lengthInvariant_ses ℚ)
      (diskTop_homology_isZero 0 (by omega))
  have hbottomzero : lengthInvariant ℚ (diskBottom.homology 1) = 0 :=
    invariant_of_isZero (lengthInvariant ℚ) (lengthInvariant_ses ℚ)
      (diskBottom_homology_isZero 1 (by omega))
  have htop :
      (∑ i ∈ Finset.Icc (0 : ℤ) 1,
        (Int.negOnePow i : ℤ) • lengthInvariant ℚ (diskSequence.X₁.homology i)) =
        -1 := by
    change (∑ i ∈ Finset.Icc (0 : ℤ) 1,
      (Int.negOnePow i : ℤ) • lengthInvariant ℚ (diskTop.homology i)) = -1
    rw [show Finset.Icc (0 : ℤ) 1 = {0, 1} by decide]
    simp [htopzero, diskTop_homology_length]
  have hbottom :
      (∑ i ∈ Finset.Icc (0 : ℤ) 1,
        (Int.negOnePow i : ℤ) • lengthInvariant ℚ (diskSequence.X₃.homology i)) =
        1 := by
    change (∑ i ∈ Finset.Icc (0 : ℤ) 1,
      (Int.negOnePow i : ℤ) • lengthInvariant ℚ (diskBottom.homology i)) = 1
    rw [show Finset.Icc (0 : ℤ) 1 = {0, 1} by decide]
    simp [hbottomzero, diskBottom_homology_length]
  rw [hmiddle, htop, hbottom] at h
  exact h

def negativeDiskSequence : ShortComplex (CochainComplex (FGModuleCat ℚ) ℤ) :=
  diskSequence.map (CategoryTheory.shiftFunctor
    (CochainComplex (FGModuleCat ℚ) ℤ) (2 : ℤ))

theorem negativeDiskSequence_shortExact : negativeDiskSequence.ShortExact := by
  exact diskSequence_shortExact.map_of_exact
    (CategoryTheory.shiftFunctor (CochainComplex (FGModuleCat ℚ) ℤ) (2 : ℤ))

def explicitModularLength (M : FGModuleCat ℚ) : ZMod 3 :=
  Int.castAddHom (ZMod 3) (lengthInvariant ℚ M)

private theorem explicitModularLength_ses (S : ShortComplex (FGModuleCat ℚ))
    (hS : S.ShortExact) :
    explicitModularLength S.X₂ = explicitModularLength S.X₁ + explicitModularLength S.X₃ :=
  postcompose_ses (lengthInvariant ℚ) (lengthInvariant_ses ℚ)
    (Int.castAddHom (ZMod 3)) S hS

theorem negativeDiskSequence_homology_additive_modular :
    (∑ i ∈ Finset.Icc (-2 : ℤ) (-1),
      (Int.negOnePow i : ℤ) • explicitModularLength (negativeDiskSequence.X₂.homology i)) =
      (∑ i ∈ Finset.Icc (-2 : ℤ) (-1),
        (Int.negOnePow i : ℤ) • explicitModularLength (negativeDiskSequence.X₁.homology i)) +
        (∑ i ∈ Finset.Icc (-2 : ℤ) (-1),
          (Int.negOnePow i : ℤ) • explicitModularLength (negativeDiskSequence.X₃.homology i)) := by
  have hbelow : negativeDiskSequence.X₃.IsGE (-2) := by
    change (diskBottom⟦(2 : ℤ)⟧).IsGE (-2)
    exact @CochainComplex.isGE_shift (FGModuleCat ℚ) _ _ diskBottom _ 0
      ((diskBottom.isGE_iff 0).2 (fun j hj =>
        HomologicalComplex.ExactAt.of_isZero (diskBottom_isZero j (by omega))))
      2 (-2) (by omega)
  have habove : negativeDiskSequence.X₁.IsLE (-1) := by
    change (diskTop⟦(2 : ℤ)⟧).IsLE (-1)
    exact @CochainComplex.isLE_shift (FGModuleCat ℚ) _ _ diskTop _ 1
      ((diskTop.isLE_iff 1).2 (fun j hj =>
        HomologicalComplex.ExactAt.of_isZero (diskTop_isZero j (by omega))))
      2 (-1) (by omega)
  exact cochain_homology_sum_additive_of_supported explicitModularLength
    explicitModularLength_ses
    negativeDiskSequence negativeDiskSequence_shortExact (-2) (-1) (by omega)
    hbelow habove

private theorem diskTop_explicit_modular_length :
    explicitModularLength (diskTop.homology 1) = 1 := by
  unfold explicitModularLength
  rw [diskTop_homology_length]
  norm_num

private theorem diskBottom_explicit_modular_length :
    explicitModularLength (diskBottom.homology 0) = 1 := by
  unfold explicitModularLength
  rw [diskBottom_homology_length]
  norm_num

theorem negativeDiskSequence_top_sum :
    (∑ i ∈ Finset.Icc (-2 : ℤ) (-1),
      (Int.negOnePow i : ℤ) • explicitModularLength
        (negativeDiskSequence.X₁.homology i)) = 2 := by
  change (∑ i ∈ Finset.Icc (-2 : ℤ) (-1),
    (Int.negOnePow i : ℤ) • explicitModularLength ((diskTop⟦(2 : ℤ)⟧).homology i)) = 2
  have hminus2 : explicitModularLength ((diskTop⟦(2 : ℤ)⟧).homology (-2)) = 0 :=
    invariant_of_isZero explicitModularLength explicitModularLength_ses
      (IsZero.of_iso (diskTop_homology_isZero 0 (by omega))
        (cochain_shift_homology_iso diskTop 2 (-2)))
  have hminus1 : explicitModularLength ((diskTop⟦(2 : ℤ)⟧).homology (-1)) = 1 := by
    have h := invariant_iso explicitModularLength explicitModularLength_ses
      (cochain_shift_homology_iso diskTop 2 (-1))
    have h' : explicitModularLength ((diskTop⟦(2 : ℤ)⟧).homology (-1)) =
        explicitModularLength (diskTop.homology 1) := by
      simpa only [show (-1 : ℤ) + 2 = 1 by omega] using h
    exact h'.trans diskTop_explicit_modular_length
  rw [show Finset.Icc (-2 : ℤ) (-1) = {(-2), (-1)} by decide]
  simp [hminus2, hminus1]
  decide

theorem negativeDiskSequence_bottom_sum :
    (∑ i ∈ Finset.Icc (-2 : ℤ) (-1),
      (Int.negOnePow i : ℤ) • explicitModularLength
        (negativeDiskSequence.X₃.homology i)) = 1 := by
  change (∑ i ∈ Finset.Icc (-2 : ℤ) (-1),
    (Int.negOnePow i : ℤ) • explicitModularLength ((diskBottom⟦(2 : ℤ)⟧).homology i)) = 1
  have hminus2 : explicitModularLength ((diskBottom⟦(2 : ℤ)⟧).homology (-2)) = 1 := by
    have h := invariant_iso explicitModularLength explicitModularLength_ses
      (cochain_shift_homology_iso diskBottom 2 (-2))
    have h' : explicitModularLength ((diskBottom⟦(2 : ℤ)⟧).homology (-2)) =
        explicitModularLength (diskBottom.homology 0) := by
      simpa only [show (-2 : ℤ) + 2 = 0 by omega] using h
    exact h'.trans diskBottom_explicit_modular_length
  have hminus1 : explicitModularLength ((diskBottom⟦(2 : ℤ)⟧).homology (-1)) = 0 :=
    invariant_of_isZero explicitModularLength explicitModularLength_ses
      (IsZero.of_iso (diskBottom_homology_isZero 1 (by omega))
        (cochain_shift_homology_iso diskBottom 2 (-1)))
  rw [show Finset.Icc (-2 : ℤ) (-1) = {(-2), (-1)} by decide]
  simp [hminus2, hminus1]

theorem negativeDiskSequence_middle_sum :
    (∑ i ∈ Finset.Icc (-2 : ℤ) (-1),
      (Int.negOnePow i : ℤ) • explicitModularLength
        (negativeDiskSequence.X₂.homology i)) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hzero : IsZero (negativeDiskSequence.X₂.homology i) := by
    change IsZero ((identityCochain⟦(2 : ℤ)⟧).homology i)
    exact IsZero.of_iso ((identityCochain_acyclic (i + 2)).isZero_homology)
      (cochain_shift_homology_iso identityCochain 2 i)
  rw [invariant_of_isZero explicitModularLength explicitModularLength_ses hzero, smul_zero]

theorem negativeDiskSequence_modular_balance : (0 : ZMod 3) = 2 + 1 := by
  have h := negativeDiskSequence_homology_additive_modular
  rw [negativeDiskSequence_middle_sum, negativeDiskSequence_top_sum,
    negativeDiskSequence_bottom_sum] at h
  exact h

end HomologicalAlgebraTest.AdditiveEuler
