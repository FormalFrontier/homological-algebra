/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import HomologicalAlgebra.Homology.ProductTotalAcyclicity
public import Mathlib.Data.ZMod.Basic

/-!
# A non-split integer-module client

The kernel short complex of reduction modulo two supplies a non-split exact
three-term horizontal row. It is repeated with zero vertical maps below.
-/

@[expose] public section

open CategoryTheory CategoryTheory.QuadrantProductTotal

namespace HomologicalAlgebraTest.QuadrantProductTotal

def rowObject (S : ShortComplex (ModuleCat ℤ)) (p : ℕ) : ModuleCat ℤ :=
  if p = 0 then S.X₃ else if p = 1 then S.X₂ else if p = 2 then S.X₁
    else ModuleCat.of ℤ PUnit

def rowDifferential (S : ShortComplex (ModuleCat ℤ)) (i j : ℕ) :
    rowObject S i ⟶ rowObject S j :=
  if h : i = 1 ∧ j = 0 then by
    rcases h with ⟨rfl, rfl⟩
    exact S.g
  else if h : i = 2 ∧ j = 1 then by
    rcases h with ⟨rfl, rfl⟩
    exact S.f
  else 0

def row (S : ShortComplex (ModuleCat ℤ)) :
    HomologicalComplex (ModuleCat ℤ) (ComplexShape.down ℕ) where
  X := rowObject S
  d := rowDifferential S
  shape i j h := by
    have h10 : ¬(i = 1 ∧ j = 0) := by
      intro hij
      rcases hij with ⟨rfl, rfl⟩
      exact h (by change 0 + 1 = 1; decide)
    have h21 : ¬(i = 2 ∧ j = 1) := by
      intro hij
      rcases hij with ⟨rfl, rfl⟩
      exact h (by change 1 + 1 = 2; decide)
    simp [rowDifferential, h10, h21]
  d_comp_d' i j l hij hjl := by
    have h10 : ¬(i = 1 ∧ j = 0) := by
      change j + 1 = i at hij
      change l + 1 = j at hjl
      omega
    by_cases h21 : i = 2 ∧ j = 1
    · rcases h21 with ⟨rfl, rfl⟩
      have hl : l = 0 := by change l + 1 = 1 at hjl; omega
      subst l
      change S.f ≫ S.g = 0
      exact S.zero
    · simp [rowDifferential, h10, h21]

def constantRows (S : ShortComplex (ModuleCat ℤ)) : Bicomplex ℤ :=
  HomologicalComplex.mk (fun _ => row S) (fun _ _ => 0)
    (by intro i j _; rfl) (by intro i j l _ _; simp)

theorem row_acyclic (S : ShortComplex (ModuleCat ℤ)) (hS : S.ShortExact) :
    (row S).Acyclic := by
  intro p
  apply (ShortComplex.moduleCat_exact_iff ((row S).sc p)).mpr
  have hp : (ComplexShape.down ℕ).prev p = p + 1 := by
    apply ComplexShape.prev_eq'
    rfl
  have hn : (ComplexShape.down ℕ).next p = p - 1 := by
    by_cases h0 : p = 0
    · subst p
      apply ComplexShape.next_eq_self'
      intro j hj
      change j + 1 = 0 at hj
      omega
    · apply ComplexShape.next_eq'
      change p - 1 + 1 = p
      omega
  change ∀ x : rowObject S p,
    rowDifferential S p ((ComplexShape.down ℕ).next p) x = 0 →
      ∃ y : rowObject S ((ComplexShape.down ℕ).prev p),
        rowDifferential S ((ComplexShape.down ℕ).prev p) p y = x
  rw [hp, hn]
  cases p with
  | zero =>
    intro x _
    obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g x
    exact ⟨y, hy⟩
  | succ p =>
    cases p with
    | zero =>
      intro x hx
      exact (ShortComplex.moduleCat_exact_iff S).mp hS.exact x hx
    | succ p =>
      cases p with
      | zero =>
        intro x hx
        have hinj := (ModuleCat.mono_iff_injective S.f).mp hS.mono_f
        have hx' : S.f x = 0 := hx
        have hf0 : S.f (0 : S.X₁) = 0 := map_zero _
        have he : x = 0 := hinj (hx'.trans hf0.symm)
        subst x
        exact ⟨0, by simp [rowDifferential]⟩
      | succ p =>
        intro x _
        refine ⟨0, ?_⟩
        change (0 : PUnit) = x
        exact Subsingleton.elim _ _

theorem constantRows_acyclic (S : ShortComplex (ModuleCat ℤ)) (hS : S.ShortExact) :
    (productTotal (constantRows S)).Acyclic :=
  acyclic_productTotal (constantRows S) (fun _ => row_acyclic S hS)

def modTwo : ℤ →ₗ[ℤ] ZMod 2 := (Int.castAddHom (ZMod 2)).toIntLinearMap

theorem modTwo_surjective : Function.Surjective modTwo :=
  ZMod.intCast_surjective

/-- The reduction-mod-two row is short exact, without chosen splittings. -/
theorem modTwo_shortExact : modTwo.shortComplexKer.ShortExact :=
  LinearMap.shortExact_shortComplexKer modTwo_surjective

/-- A concrete non-split native bicomplex whose product total is acyclic. -/
theorem modTwo_productTotal_acyclic :
    (productTotal (constantRows modTwo.shortComplexKer)).Acyclic :=
  constantRows_acyclic _ modTwo_shortExact

example (x : Product (constantRows modTwo.shortComplexKer) 1) :
    (productTotal (constantRows modTwo.shortComplexKer)).d 1 0 x
      (diagonalIndex 0 0) = modTwo (x (diagonalIndex 1 0)) := by
  have h : (0 : ℤ) = 1 - 1 := by decide
  have hz : (diagonalIndex 0 0).1.1 = 0 := rfl
  rw [productTotal_d_apply_zero _ 1 0 h x (diagonalIndex 0 0) hz]
  rfl

theorem modTwo_no_section :
    ¬∃ s : ZMod 2 →ₗ[ℤ] ℤ, modTwo ∘ₗ s = LinearMap.id := by
  rintro ⟨s, hs⟩
  have htwo : (2 : ℤ) • s (1 : ZMod 2) = 0 := by
    rw [← map_smul]
    have hmod : (2 : ℤ) • (1 : ZMod 2) = 0 := by decide
    rw [hmod, map_zero]
  have hzero : s (1 : ZMod 2) = 0 := by
    rw [zsmul_eq_mul] at htwo
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have h : modTwo (s (1 : ZMod 2)) = (1 : ZMod 2) := by
    exact congrArg (fun f : ZMod 2 →ₗ[ℤ] ZMod 2 => f 1) hs
  rw [hzero, map_zero] at h
  norm_num at h

example (K : Bicomplex ℤ) :
    differential K (-1) = horizontalMap K (-1) + verticalMap K (-1) := by
  rw [differential_eq]
  have hs : (Int.negOnePow ((-1 : ℤ) + 1) : ℤ) = 1 := by decide
  rw [hs, one_smul]

example (K : Bicomplex ℤ) :
    differential K 0 = horizontalMap K 0 - verticalMap K 0 := by
  rw [differential_eq]
  have hs : (Int.negOnePow ((0 : ℤ) + 1) : ℤ) = -1 := by decide
  rw [hs, neg_one_smul]
  simp only [sub_eq_add_neg]

example (K : Bicomplex ℤ) :
    differential K 1 = horizontalMap K 1 + verticalMap K 1 := by
  rw [differential_eq]
  have hs : (Int.negOnePow ((1 : ℤ) + 1) : ℤ) = 1 := by decide
  rw [hs, one_smul]

example (x : Product (constantRows modTwo.shortComplexKer) (-1))
    (hx : differential (constantRows modTwo.shortComplexKer) (-1) x = 0) :
    primitive (constantRows modTwo.shortComplexKer)
        (fun _ => row_acyclic _ modTwo_shortExact) (-1) x hx
          (⟨(0, 0), by decide⟩ : Diag 0) = 0 := by
  apply primitive_apply_early
  decide

example : productTotalMap (𝟙 (constantRows modTwo.shortComplexKer)) =
    𝟙 (productTotal (constantRows modTwo.shortComplexKer)) :=
  productTotalMap_id _

end HomologicalAlgebraTest.QuadrantProductTotal
