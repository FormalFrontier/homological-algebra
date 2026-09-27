/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.AdditiveEuler.Cochain
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Tactic.Abel

/-!
# Homology-supported cochain Euler additivity

The native cochain long exact sequence gives an image-boundary correction to
short-exact-sequence additivity of signed homology sums. Vanishing *homology*
at the neighboring degrees, rather than vanishing terms, removes the correction.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators ZeroObject

namespace CategoryTheory.AdditiveEuler

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {Γ : Type w} [AddCommGroup Γ]
variable (μ : C → Γ)
variable (hμ : ∀ S : ShortComplex C, S.ShortExact → μ S.X₂ = μ S.X₁ + μ S.X₃)

include hμ

/-- Additivity across an exact pair, with the native image factorizations at
both ends; the pair itself need not be short exact. -/
theorem invariant_exact_pair_images (S : ShortComplex C) (hS : S.Exact) :
    μ S.X₂ = μ (image S.f) + μ (image S.g) := by
  let T : ShortComplex C := ShortComplex.mk (image.ι S.f) (factorThruImage S.g)
    (by
      apply (cancel_mono (image.ι S.g)).1
      simp only [Category.assoc, image.fac, image_ι_comp_eq_zero S.zero, zero_comp])
  have hT : T.ShortExact := by
    have hkernel : IsLimit (KernelFork.ofι T.f T.zero) := by
      refine KernelFork.IsLimit.ofι' _ _ ?_
      intro U t ht
      refine KernelFork.IsLimit.lift' hS.isLimitImage' t ?_
      rw [← image.fac S.g, ← Category.assoc, ht, zero_comp]
    exact { exact := ShortComplex.exact_of_f_is_kernel T hkernel
            mono_f := by dsimp [T]; infer_instance
            epi_g := by dsimp [T]; infer_instance }
  exact hμ T hT

/-- The image of the native connecting homomorphism from degree `i` to `i+1`. -/
@[expose] def cochain_homology_boundary_image (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) (i : ℤ) : C :=
  image (hS.δ i (i + 1) (by simp))

/-- Three consecutive positions of the native long exact sequence give the
image-boundary correction, without a termwise support hypothesis. -/
theorem cochain_homology_local_additivity
    (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact) (i : ℤ) :
    μ (S.X₂.homology i) = μ (S.X₁.homology i) + μ (S.X₃.homology i) -
      μ (cochain_homology_boundary_image S hS (i - 1)) -
      μ (cochain_homology_boundary_image S hS i) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, i = j + 1 := ⟨i - 1, by omega⟩
  simp only [add_sub_cancel_right]
  have h₁ := invariant_exact_pair_images μ hμ _
    (hS.homology_exact₁ j (j + 1) (by simp))
  have h₂ := invariant_exact_pair_images μ hμ _ (hS.homology_exact₂ (j + 1))
  have h₃ := invariant_exact_pair_images μ hμ _
    (hS.homology_exact₃ (j + 1) (j + 1 + 1) (by simp))
  dsimp [cochain_homology_boundary_image] at *
  rw [h₂, h₁, h₃]
  abel

omit hμ

private theorem signed_boundary_interval (β : ℤ → Γ) (a b : ℤ) (hab : a ≤ b) :
    (∑ i ∈ Finset.Icc a b, ((Int.negOnePow i : ℤ) • β (i - 1) +
      (Int.negOnePow i : ℤ) • β i)) =
      (Int.negOnePow a : ℤ) • β (a - 1) +
        (Int.negOnePow b : ℤ) • β b := by
  induction b, hab using Int.leInduction with
  | base => simp [add_comm]
  | succ b hab ih =>
    have hs : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hs, Finset.sum_insert (by simp), ih]
    simp only [Int.negOnePow_succ, Units.val_neg, add_sub_cancel_right, neg_smul]
    abel

include hμ

/-- For `a ≤ b`, the finite signed homology sum differs from additivity by
the incoming and outgoing connecting-map images. -/
theorem cochain_homology_euler_endpoints
    (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
    (a b : ℤ) (hab : a ≤ b) :
    (∑ i ∈ Finset.Icc a b, (Int.negOnePow i : ℤ) • μ (S.X₂.homology i)) =
      (∑ i ∈ Finset.Icc a b, (Int.negOnePow i : ℤ) • μ (S.X₁.homology i)) +
      (∑ i ∈ Finset.Icc a b, (Int.negOnePow i : ℤ) • μ (S.X₃.homology i)) -
      (Int.negOnePow a : ℤ) • μ (cochain_homology_boundary_image S hS (a - 1)) -
      (Int.negOnePow b : ℤ) • μ (cochain_homology_boundary_image S hS b) := by
  have hboundary := signed_boundary_interval
    (fun i => μ (cochain_homology_boundary_image S hS i)) a b hab
  calc
    _ = (∑ i ∈ Finset.Icc a b, (Int.negOnePow i : ℤ) • μ (S.X₁.homology i)) +
          (∑ i ∈ Finset.Icc a b, (Int.negOnePow i : ℤ) • μ (S.X₃.homology i)) -
          (∑ i ∈ Finset.Icc a b, ((Int.negOnePow i : ℤ) •
            μ (cochain_homology_boundary_image S hS (i - 1)) +
            (Int.negOnePow i : ℤ) • μ (cochain_homology_boundary_image S hS i))) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [cochain_homology_local_additivity μ hμ S hS i]
      simp only [smul_add, smul_sub]
      abel
    _ = _ := by rw [hboundary]; abel

/-- Vanishing of just the two neighboring *homology objects* kills the
connecting-map images at the ends of the interval. -/
theorem cochain_homology_sum_additive_of_endpoints
    (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
    (a b : ℤ) (hab : a ≤ b)
    (hbelow : IsZero (S.X₃.homology (a - 1)))
    (habove : IsZero (S.X₁.homology (b + 1))) :
    (∑ i ∈ Finset.Icc a b, (Int.negOnePow i : ℤ) • μ (S.X₂.homology i)) =
      (∑ i ∈ Finset.Icc a b, (Int.negOnePow i : ℤ) • μ (S.X₁.homology i)) +
        (∑ i ∈ Finset.Icc a b, (Int.negOnePow i : ℤ) • μ (S.X₃.homology i)) := by
  rw [cochain_homology_euler_endpoints μ hμ S hS a b hab]
  have hin : μ (cochain_homology_boundary_image S hS (a - 1)) = 0 := by
    apply image_zero_of_source μ hμ _ hbelow
  have hout : μ (cochain_homology_boundary_image S hS b) = 0 := by
    apply image_zero_of_target μ hμ _ habove
  rw [hin, hout]
  simp

/-- Additivity assuming only the native cohomological bounds on the two
outer complexes; no bound on the middle complex or its terms is required. -/
theorem cochain_homology_sum_additive_of_supported
    (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
    (a b : ℤ) (hab : a ≤ b) (hbelow : S.X₃.IsGE a) (habove : S.X₁.IsLE b) :
    (∑ i ∈ Finset.Icc a b, (Int.negOnePow i : ℤ) • μ (S.X₂.homology i)) =
      (∑ i ∈ Finset.Icc a b, (Int.negOnePow i : ℤ) • μ (S.X₁.homology i)) +
        (∑ i ∈ Finset.Icc a b, (Int.negOnePow i : ℤ) • μ (S.X₃.homology i)) := by
  exact cochain_homology_sum_additive_of_endpoints μ hμ S hS a b hab
    (@CochainComplex.isZero_of_isGE C _ _ S.X₃ a (a - 1) (by omega)
      hbelow inferInstance)
    (@CochainComplex.isZero_of_isLE C _ _ S.X₁ b (b + 1) (by omega)
      habove inferInstance)

end CategoryTheory.AdditiveEuler
