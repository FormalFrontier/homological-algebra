/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Abelian.SnakeLemma
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# A two-row snake diagram with nonzero exterior terms

The upper row is `ℤ × ℤ → ℤ → ℤ/3ℤ`; the lower row is
`ℤ → ℤ → ℤ/3ℤ × ℤ`. The first upper arrow has a kernel and the last
lower arrow has a cokernel, so neither exterior term may be replaced by zero.
-/

namespace CategoryTheory.ShortComplex.SnakeInput

open CategoryTheory Limits

private def timesThree : ℤ →ₗ[ℤ] ℤ := LinearMap.lsmul ℤ ℤ 3

private def upperFirst : ℤ × ℤ →ₗ[ℤ] ℤ :=
  timesThree.comp (LinearMap.fst ℤ ℤ ℤ)

private def reduction : ℤ →ₗ[ℤ] ZMod 3 :=
  (Int.castAddHom (ZMod 3)).toIntLinearMap

private def lowerLast : ℤ →ₗ[ℤ] ZMod 3 × ℤ :=
  LinearMap.prod reduction 0

private theorem three_eq_zero : (3 : ZMod 3) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd (3 : ℤ) 3).2 (dvd_refl _)

private abbrev upperRow : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.moduleCatMk upperFirst reduction (by
    apply LinearMap.ext
    intro pair
    change ((3 * pair.1 : ℤ) : ZMod 3) = 0
    simp [three_eq_zero])

private abbrev lowerRow : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.moduleCatMk timesThree lowerLast (by
    apply LinearMap.ext
    intro integer
    change (((3 * integer : ℤ) : ZMod 3), (0 : ℤ)) = 0
    ext <;> simp [three_eq_zero])

private abbrev vertical : upperRow ⟶ lowerRow where
  τ₁ := ModuleCat.ofHom upperFirst
  τ₂ := ModuleCat.ofHom timesThree
  τ₃ := 0
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro pair
    change 3 * (3 * pair.1) = 3 * (3 * pair.1)
    rfl
  comm₂₃ := by
    dsimp [upperRow, lowerRow, ShortComplex.moduleCatMk]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro integer
    change (((3 * integer : ℤ) : ZMod 3), (0 : ℤ)) = 0
    ext <;> simp [three_eq_zero]

private theorem upperRow_exact : upperRow.Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  change ∀ integer : ℤ, (integer : ZMod 3) = 0 →
    ∃ pair : ℤ × ℤ, 3 * pair.1 = integer
  intro integer hzero
  obtain ⟨quotient, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd integer 3).mp hzero
  exact ⟨(quotient, 0), rfl⟩

private theorem lowerRow_exact : lowerRow.Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  change ∀ integer : ℤ, ((integer : ZMod 3), (0 : ℤ)) = 0 →
    ∃ quotient : ℤ, 3 * quotient = integer
  intro integer hzero
  have hmod : (integer : ZMod 3) = 0 := by
    simpa using
      congrArg (fun pair : ZMod 3 × ℤ => pair.1) hzero
  obtain ⟨quotient, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd integer 3).mp hmod
  exact ⟨quotient, rfl⟩

/-- An exact-row snake input whose two exterior objects are nonzero. -/
private noncomputable def modThreeInput : ShortComplex.SnakeInput (ModuleCat ℤ) where
  L₀ := kernel vertical
  L₁ := upperRow
  L₂ := lowerRow
  L₃ := cokernel vertical
  v₀₁ := kernel.ι vertical
  v₁₂ := vertical
  v₂₃ := cokernel.π vertical
  h₀ := kernelIsKernel vertical
  h₃ := cokernelIsCokernel vertical
  L₁_exact := upperRow_exact
  epi_L₁_g := by
    change Epi (ModuleCat.ofHom reduction)
    apply (ModuleCat.epi_iff_surjective _).mpr
    change Function.Surjective (reduction : ℤ → ZMod 3)
    intro residue
    exact ⟨(ZMod.cast residue : ℤ), by
      simp [reduction]⟩
  L₂_exact := lowerRow_exact
  mono_L₂_f := by
    change Mono (ModuleCat.ofHom timesThree)
    apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective (timesThree : ℤ → ℤ)
    intro first second h
    have h' : (3 : ℤ) * first = (3 : ℤ) * second := by
      simpa [timesThree] using h
    omega

example : modThreeInput.composableArrowsWithEndpoints.map' 0 1 ≫
    modThreeInput.v₀₁.τ₁ = kernel.ι modThreeInput.L₁.f := by
  simp

example : modThreeInput.v₂₃.τ₃ ≫
    modThreeInput.composableArrowsWithEndpoints.map' 6 7 =
      cokernel.π modThreeInput.L₂.g := by
  simp

/-- The upper-left kernel is nonzero, without assuming the endpoint statements. -/
private theorem modThreeInput_left_nonzero : ¬ IsZero (kernel modThreeInput.L₁.f) := by
  intro h
  have hm : Mono upperRow.f :=
    (Preadditive.mono_iff_isZero_kernel upperRow.f).mpr (by
      simpa only [modThreeInput] using h)
  have hi := (ModuleCat.mono_iff_injective upperRow.f).mp hm
  have heq : (0 : ℤ × ℤ) = (0, 1) :=
    hi (by change (0 : ℤ) = 0; rfl)
  have hfalse : (0 : ℤ) = 1 := congrArg (fun pair : ℤ × ℤ => pair.2) heq
  omega

/-- The lower-right cokernel is nonzero, without assuming the endpoint statements. -/
private theorem modThreeInput_right_nonzero : ¬ IsZero (cokernel modThreeInput.L₂.g) := by
  intro h
  have he : Epi lowerRow.g :=
    (Preadditive.epi_iff_isZero_cokernel lowerRow.g).mpr (by
      simpa only [modThreeInput] using h)
  obtain ⟨integer, hlast⟩ :=
    (ModuleCat.epi_iff_surjective lowerRow.g).mp he ((0 : ZMod 3), (1 : ℤ))
  have hfalse : (0 : ℤ) = 1 := by
    have hlast' := congrArg (fun pair : ZMod 3 × ℤ => pair.2) hlast
    change (0 : ℤ) = 1 at hlast'
    exact hlast'
  omega

example : ¬ IsZero (modThreeInput.composableArrowsWithEndpoints.obj' 0) := by
  simpa using modThreeInput_left_nonzero

example : ¬ IsZero (modThreeInput.composableArrowsWithEndpoints.obj' 7) := by
  rw [modThreeInput.composableArrowsWithEndpoints_obj_seven]
  exact modThreeInput_right_nonzero

/-- A lift of integer residues into the last vertical kernel. -/
private noncomputable def sourceLift :
    ModuleCat.of ℤ ℤ ⟶ modThreeInput.L₀.X₃ :=
  (KernelFork.IsLimit.lift' modThreeInput.h₀τ₃ (ModuleCat.ofHom reduction) (by
    change ModuleCat.ofHom reduction ≫ (0 : upperRow.X₃ ⟶ lowerRow.X₃) = 0
    exact comp_zero)).1

private theorem sourceLift_fac :
    sourceLift ≫ modThreeInput.v₀₁.τ₃ = ModuleCat.ofHom reduction :=
  (KernelFork.IsLimit.lift' modThreeInput.h₀τ₃ (ModuleCat.ofHom reduction) (by
    change ModuleCat.ofHom reduction ≫ (0 : upperRow.X₃ ⟶ lowerRow.X₃) = 0
    exact comp_zero)).2

set_option backward.isDefEq.respectTransparency false in
/-- The existing snake connector carries the chosen class to its positive
cokernel representative. -/
private theorem modThreeInput_connector_positive :
    sourceLift ≫ modThreeInput.δ = modThreeInput.v₂₃.τ₁ := by
  have hsecond : (𝟙 (ModuleCat.of ℤ ℤ)) ≫ modThreeInput.L₁.g =
      sourceLift ≫ modThreeInput.v₀₁.τ₃ := by
    change (𝟙 (ModuleCat.of ℤ ℤ)) ≫ ModuleCat.ofHom reduction =
      sourceLift ≫ modThreeInput.v₀₁.τ₃
    exact (Category.id_comp _).trans sourceLift_fac.symm
  have hfirst : (𝟙 (ModuleCat.of ℤ ℤ)) ≫ modThreeInput.L₂.f =
      (𝟙 (ModuleCat.of ℤ ℤ)) ≫ modThreeInput.v₁₂.τ₂ := by
    rfl
  simpa only [Category.id_comp] using
    modThreeInput.δ_eq sourceLift (𝟙 _) (𝟙 _) hsecond hfirst

private noncomputable def quotientReduction :
    modThreeInput.L₃.X₁ ⟶ ModuleCat.of ℤ (ZMod 3) :=
  (CokernelCofork.IsColimit.desc' modThreeInput.h₃τ₁ (ModuleCat.ofHom reduction) (by
    change upperRow.f ≫ upperRow.g = 0
    exact upperRow.zero)).1

private theorem quotientReduction_fac :
    modThreeInput.v₂₃.τ₁ ≫ quotientReduction = ModuleCat.ofHom reduction :=
  (CokernelCofork.IsColimit.desc' modThreeInput.h₃τ₁ (ModuleCat.ofHom reduction) (by
    change upperRow.f ≫ upperRow.g = 0
    exact upperRow.zero)).2

/-- The positive connector value differs from its negative in `ℤ/3ℤ`. -/
private theorem modThreeInput_connector_not_negative :
    sourceLift ≫ modThreeInput.δ ≠ -modThreeInput.v₂₃.τ₁ := by
  rw [modThreeInput_connector_positive]
  intro heq
  have hcomp := congrArg (fun f => f ≫ quotientReduction) heq
  have hred : (ModuleCat.ofHom reduction : ModuleCat.of ℤ ℤ ⟶
      ModuleCat.of ℤ (ZMod 3)) = -(ModuleCat.ofHom reduction) := by
    rw [Preadditive.neg_comp, quotientReduction_fac] at hcomp
    exact hcomp
  have hvalue := congrArg (fun (f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ (ZMod 3)) =>
    f (1 : ℤ)) hred
  change (1 : ZMod 3) = -(1 : ZMod 3) at hvalue
  exact (show (1 : ZMod 3) ≠ -1 by decide) hvalue

private theorem extended_nontrivial :
    modThreeInput.composableArrowsWithEndpoints.Exact ∧
      ¬ IsZero (kernel modThreeInput.L₁.f) ∧
      ¬ IsZero (cokernel modThreeInput.L₂.g) :=
  ⟨modThreeInput.snake_lemma_with_endpoints,
    modThreeInput_left_nonzero, modThreeInput_right_nonzero⟩

end CategoryTheory.ShortComplex.SnakeInput
