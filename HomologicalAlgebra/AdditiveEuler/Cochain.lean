/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.AdditiveEuler
public import Mathlib.Algebra.Homology.Opposite

/-!
# Finite-interval Euler identities for cochain complexes

Duality transfers the chain Euler identity to native integer-indexed cochain
complexes in an arbitrary abelian category. The invariant takes values in an
arbitrary additive commutative group and is additive on short exact sequences.
Both incoming and outgoing boundary images are retained on a finite interval.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators ZeroObject

namespace CategoryTheory.AdditiveEuler

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {Γ : Type w} [AddCommGroup Γ]
variable (μ : C → Γ)
variable (hμ : ∀ S : ShortComplex C, S.ShortExact → μ S.X₂ = μ S.X₁ + μ S.X₃)

include hμ

private theorem opposite_ses (S : ShortComplex Cᵒᵖ) (hS : S.ShortExact) :
    μ S.X₂.unop = μ S.X₁.unop + μ S.X₃.unop := by
  simpa only [ShortComplex.unop_X₁, ShortComplex.unop_X₂, ShortComplex.unop_X₃,
    add_comm] using hμ S.unop hS.unop

private theorem opposite_image (f : X ⟶ Y) :
    μ (image f.op).unop = μ (image f) :=
  invariant_iso μ hμ (imageOpUnop f)

private theorem opposite_homology (K : CochainComplex C ℤ) (j : ℤ) :
    μ (K.op.homology j).unop = μ (K.homology j) :=
  invariant_iso μ hμ (K.homologyOp j).unop.symm

set_option backward.isDefEq.respectTransparency false

/-- The cochain Euler sum on `[a,b]` has outgoing and incoming boundary images,
at `b` and `a` respectively. -/
theorem cochain_euler_endpoints (K : CochainComplex C ℤ) (a b : ℤ) (hab : a ≤ b) :
    (∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (K.X j)) =
      (∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (K.homology j)) +
        (Int.negOnePow b : ℤ) • μ (image (K.d b (b + 1))) +
        (Int.negOnePow a : ℤ) • μ (image (K.d (a - 1) a)) := by
  have h := euler_endpoints (fun X : Cᵒᵖ => μ X.unop)
    (opposite_ses μ hμ) K.op a b hab
  simp only [HomologicalComplex.op_X, HomologicalComplex.op_d, unop_op] at h
  have hhom :
      (∑ j ∈ Finset.Icc a b,
        (Int.negOnePow j : ℤ) • μ (K.op.homology j).unop) =
      ∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (K.homology j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [opposite_homology μ hμ K j]
  rw [hhom, opposite_image μ hμ (K.d b (b + 1)),
    opposite_image μ hμ (K.d (a - 1) a)] at h
  exact h

set_option backward.isDefEq.respectTransparency true

/-- The cochain Euler sum equals the cohomology sum when the two neighboring
terms vanish. -/
theorem cochain_euler_eq_homology (K : CochainComplex C ℤ) (a b : ℤ) (hab : a ≤ b)
    (hbelow : IsZero (K.X (a - 1))) (habove : IsZero (K.X (b + 1))) :
    (∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (K.X j)) =
      ∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (K.homology j) := by
  rw [cochain_euler_endpoints μ hμ K a b hab,
    image_zero_of_target μ hμ _ habove, image_zero_of_source μ hμ _ hbelow]
  simp

/-- The same Euler equality for a termwise support bound on `[a,b]`. -/
theorem cochain_euler_eq_homology_of_bounded (K : CochainComplex C ℤ)
    (a b : ℤ) (hab : a ≤ b)
    (hK : ∀ j, j < a ∨ b < j → IsZero (K.X j)) :
    (∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (K.X j)) =
      ∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (K.homology j) :=
  cochain_euler_eq_homology μ hμ K a b hab (hK (a - 1) (Or.inl (by omega)))
    (hK (b + 1) (Or.inr (by omega)))

/-- The Euler sum of an acyclic cochain complex with vanishing neighboring
terms is zero. -/
theorem cochain_euler_acyclic (K : CochainComplex C ℤ) (a b : ℤ) (hab : a ≤ b)
    (hbelow : IsZero (K.X (a - 1))) (habove : IsZero (K.X (b + 1)))
    (hK : K.Acyclic) :
    (∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (K.X j)) = 0 := by
  rw [cochain_euler_eq_homology μ hμ K a b hab hbelow habove]
  apply Finset.sum_eq_zero
  intro j hj
  rw [invariant_of_isZero μ hμ ((hK j).isZero_homology), smul_zero]

/-- A quasi-isomorphism preserves the bounded cochain Euler sum when both
complexes are termwise supported in the same interval. -/
theorem cochain_euler_quasiIso (K L : CochainComplex C ℤ) (φ : K ⟶ L) [QuasiIso φ]
    (a b : ℤ) (hab : a ≤ b)
    (hK : ∀ j, j < a ∨ b < j → IsZero (K.X j))
    (hL : ∀ j, j < a ∨ b < j → IsZero (L.X j)) :
    (∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (K.X j)) =
      ∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (L.X j) := by
  rw [cochain_euler_eq_homology_of_bounded μ hμ K a b hab hK,
    cochain_euler_eq_homology_of_bounded μ hμ L a b hab hL]
  apply Finset.sum_congr rfl
  intro j hj
  rw [invariant_iso μ hμ (asIso (HomologicalComplex.homologyMap φ j))]

end CategoryTheory.AdditiveEuler
