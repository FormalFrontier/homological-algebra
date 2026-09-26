/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.EulerCharacteristic
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Tactic.Abel

/-!
# Short-exact-sequence additive Euler characteristic

For an invariant of objects in an abelian category valued in an additive commutative
group, additive on every native short exact sequence, the signed Euler sum on an
integer interval differs from the homology sum by two boundary-image terms.
No finiteness, splitting, or normalization of the invariant is assumed.
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

/-- SES additivity forces the invariant of the zero object to vanish. -/
theorem invariant_zero : μ (0 : C) = 0 := by
  let S : ShortComplex C := ShortComplex.mk (𝟙 (0 : C)) (0 : (0 : C) ⟶ (0 : C))
    (by simp)
  have hS : S.ShortExact :=
    { exact := (S.exact_iff_epi rfl).2 (by dsimp [S]; infer_instance)
      mono_f := by dsimp [S]; infer_instance
      epi_g := by dsimp [S]; infer_instance }
  have h := hμ S hS
  change μ (0 : C) = μ (0 : C) + μ (0 : C) at h
  have h' : μ (0 : C) + 0 = μ (0 : C) + μ (0 : C) := by simpa using h
  exact (add_left_cancel h').symm

/-- SES additivity implies invariance under isomorphism, without a separate normalization axiom. -/
theorem invariant_iso {X Y : C} (e : X ≅ Y) : μ X = μ Y := by
  let S : ShortComplex C := ShortComplex.mk e.hom (0 : Y ⟶ (0 : C)) (by simp)
  have hS : S.ShortExact :=
    { exact := (S.exact_iff_epi rfl).2 (by dsimp [S]; infer_instance)
      mono_f := by dsimp [S]; infer_instance
      epi_g := by dsimp [S]; infer_instance }
  simpa [S, invariant_zero μ hμ] using (hμ S hS).symm

/-- The invariant of any zero object vanishes. -/
theorem invariant_of_isZero {X : C} (hX : IsZero X) : μ X = 0 := by
  rw [invariant_iso μ hμ (hX.iso (isZero_zero C)), invariant_zero μ hμ]

omit hμ

variable (K : ChainComplex C ℤ) (i : ℤ)

theorem cycles_image_zero :
    K.iCycles i ≫ factorThruImage (K.d i (i - 1)) = 0 := by
  apply (cancel_mono (image.ι (K.d i (i - 1)))).1
  simp

def cyclesImageIsKernel :
    IsLimit (KernelFork.ofι (K.iCycles i) (cycles_image_zero K i)) := by
  refine KernelFork.IsLimit.ofι' _ _ ?_
  intro T t ht
  refine KernelFork.IsLimit.lift' (K.cyclesIsKernel i (j := i - 1) (by simp)) t ?_
  rw [← image.fac (K.d i (i - 1)), ← Category.assoc, ht, zero_comp]

/-- The cycles, terms, and outgoing differential image form a native short exact sequence. -/
theorem cycles_image_shortExact :
    (ShortComplex.mk (K.iCycles i) (factorThruImage (K.d i (i - 1)))
      (cycles_image_zero K i)).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (cyclesImageIsKernel K i)

def imageToCycles : image (K.d (i + 1) i) ⟶ K.cycles i :=
  K.liftCycles (image.ι (K.d (i + 1) i)) (i - 1) (by simp) (by
    apply (cancel_epi (factorThruImage (K.d (i + 1) i))).1
    simp)

@[reassoc (attr := simp)]
theorem imageToCycles_iCycles :
    imageToCycles K i ≫ K.iCycles i = image.ι (K.d (i + 1) i) := by
  simp [imageToCycles]

instance imageToCycles_mono : Mono (imageToCycles K i) :=
  mono_of_mono_fac (imageToCycles_iCycles K i)

@[reassoc (attr := simp)]
theorem factorThruImage_imageToCycles :
    factorThruImage (K.d (i + 1) i) ≫ imageToCycles K i = K.toCycles (i + 1) i := by
  apply (cancel_mono (K.iCycles i)).1
  simp

theorem imageToCycles_homologyπ : imageToCycles K i ≫ K.homologyπ i = 0 := by
  apply (cancel_epi (factorThruImage (K.d (i + 1) i))).1
  simp [← Category.assoc]

def imageCyclesIsCokernel :
    IsColimit (CokernelCofork.ofπ (K.homologyπ i) (imageToCycles_homologyπ K i)) := by
  refine CokernelCofork.IsColimit.ofπ' _ _ ?_
  intro T t ht
  refine CokernelCofork.IsColimit.desc'
    (K.homologyIsCokernel (i + 1) (j := i) (by simp)) t ?_
  rw [← factorThruImage_imageToCycles K i, Category.assoc, ht, comp_zero]

/-- The incoming differential image, cycles, and homology form a native short exact sequence. -/
theorem image_cycles_shortExact :
    (ShortComplex.mk (imageToCycles K i) (K.homologyπ i)
      (imageToCycles_homologyπ K i)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (imageCyclesIsCokernel K i)

include hμ

/-- A term's invariant is the homology invariant plus its incoming and outgoing image invariants. -/
theorem local_decomposition :
    μ (K.X i) = μ (K.homology i) + μ (image (K.d (i + 1) i)) +
      μ (image (K.d i (i - 1))) := by
  have h₁ := hμ _ (cycles_image_shortExact K i)
  have h₂ := hμ _ (image_cycles_shortExact K i)
  change μ (K.X i) = μ (K.cycles i) + μ (image (K.d i (i - 1))) at h₁
  change μ (K.cycles i) = μ (image (K.d (i + 1) i)) + μ (K.homology i) at h₂
  rw [h₁, h₂]
  abel

theorem image_zero_of_source {X Y : C} (f : X ⟶ Y) (hX : IsZero X) :
    μ (image f) = 0 :=
  invariant_of_isZero μ hμ (IsZero.of_epi (factorThruImage f) hX)

theorem image_zero_of_target {X Y : C} (f : X ⟶ Y) (hY : IsZero Y) :
    μ (image f) = 0 :=
  invariant_of_isZero μ hμ (IsZero.of_mono (image.ι f) hY)

omit hμ

private theorem signed_boundary_sum (β : ℤ → Γ) (a b : ℤ) (hab : a ≤ b) :
    (∑ j ∈ Finset.Icc a b, ((Int.negOnePow j : ℤ) • β j +
      (Int.negOnePow j : ℤ) • β (j - 1))) =
    (Int.negOnePow b : ℤ) • β b + (Int.negOnePow a : ℤ) • β (a - 1) := by
  induction b, hab using Int.leInduction with
  | base => simp
  | succ b hab ih =>
    have hs : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hs, Finset.sum_insert (by simp), ih]
    simp only [Int.negOnePow_succ, Units.val_neg, add_sub_cancel_right, neg_smul]
    abel

include hμ

/-- The Euler term sum on `[a,b]` is the homology sum plus both boundary-image terms. -/
theorem euler_endpoints (a b : ℤ) (hab : a ≤ b) :
    (∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (K.X j)) =
    (∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (K.homology j)) +
    (Int.negOnePow b : ℤ) • μ (image (K.d (b + 1) b)) +
    (Int.negOnePow a : ℤ) • μ (image (K.d a (a - 1))) := by
  have hprev (j : ℤ) : μ (image (K.d (j - 1 + 1) (j - 1))) =
      μ (image (K.d j (j - 1))) :=
    congrArg (fun t : ℤ => μ (image (K.d t (j - 1)))) (sub_add_cancel j 1)
  have ht : (∑ j ∈ Finset.Icc a b,
      ((Int.negOnePow j : ℤ) • μ (image (K.d (j + 1) j)) +
        (Int.negOnePow j : ℤ) • μ (image (K.d j (j - 1))))) =
      (Int.negOnePow b : ℤ) • μ (image (K.d (b + 1) b)) +
        (Int.negOnePow a : ℤ) • μ (image (K.d a (a - 1))) := by
    simpa only [hprev] using
      signed_boundary_sum (fun j => μ (image (K.d (j + 1) j))) a b hab
  calc
    _ = (∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (K.homology j)) +
        ∑ j ∈ Finset.Icc a b, ((Int.negOnePow j : ℤ) • μ (image (K.d (j + 1) j)) +
          (Int.negOnePow j : ℤ) • μ (image (K.d j (j - 1)))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [local_decomposition μ hμ K j, smul_add, smul_add]
      abel
    _ = _ := by rw [ht]; abel

/-- Adjacent zero terms kill both endpoint images in the finite Euler identity. -/
theorem euler_eq_homology (a b : ℤ) (hab : a ≤ b)
    (hbelow : IsZero (K.X (a - 1))) (habove : IsZero (K.X (b + 1))) :
    (∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (K.X j)) =
    ∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (K.homology j) := by
  rw [euler_endpoints μ hμ K a b hab,
    image_zero_of_source μ hμ _ habove, image_zero_of_target μ hμ _ hbelow]
  simp

/-- For a complex termwise zero outside `[a,b]`, its Euler and homology sums agree. -/
theorem euler_eq_homology_of_bounded (a b : ℤ) (hab : a ≤ b)
    (hK : ∀ j, j < a ∨ b < j → IsZero (K.X j)) :
    (∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (K.X j)) =
    ∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (K.homology j) :=
  euler_eq_homology μ hμ K a b hab (hK _ (Or.inl (by omega)))
    (hK _ (Or.inr (by omega)))

theorem homology_zero_of_term (hK : IsZero (K.X i)) : μ (K.homology i) = 0 :=
  invariant_of_isZero μ hμ (IsZero.of_epi (K.homologyπ i) (IsZero.of_mono (K.iCycles i) hK))

/-- An acyclic complex with adjacent zero terms has zero finite Euler sum. -/
theorem euler_acyclic (a b : ℤ) (hab : a ≤ b)
    (hbelow : IsZero (K.X (a - 1))) (habove : IsZero (K.X (b + 1)))
    (hK : K.Acyclic) :
    (∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (K.X j)) = 0 := by
  rw [euler_eq_homology μ hμ K a b hab hbelow habove]
  apply Finset.sum_eq_zero
  intro j hj
  rw [invariant_of_isZero μ hμ ((hK j).isZero_homology), smul_zero]

/-- A quasi-isomorphism preserves finite Euler sums when both complexes are termwise bounded
in the same interval. -/
theorem euler_quasiIso (L : ChainComplex C ℤ) (φ : K ⟶ L) [QuasiIso φ]
    (a b : ℤ) (hab : a ≤ b)
    (hK : ∀ j, j < a ∨ b < j → IsZero (K.X j))
    (hL : ∀ j, j < a ∨ b < j → IsZero (L.X j)) :
    (∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (K.X j)) =
    ∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (L.X j) := by
  rw [euler_eq_homology_of_bounded μ hμ K a b hab hK,
    euler_eq_homology_of_bounded μ hμ L a b hab hL]
  apply Finset.sum_congr rfl
  intro j hj
  rw [invariant_iso μ hμ (asIso (HomologicalComplex.homologyMap φ j))]

/-- Postcomposing an SES-additive invariant with an additive homomorphism remains SES-additive. -/
theorem postcompose_ses {Δ : Type*} [AddCommGroup Δ] (t : Γ →+ Δ)
    (S : ShortComplex C) (hS : S.ShortExact) :
    t (μ S.X₂) = t (μ S.X₁) + t (μ S.X₃) := by
  rw [hμ S hS, map_add]

end CategoryTheory.AdditiveEuler
