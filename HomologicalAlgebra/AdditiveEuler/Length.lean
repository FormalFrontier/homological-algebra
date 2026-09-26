/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.AdditiveEuler
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.FGModuleCat.Limits
public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite-length short-exact-sequence additive invariant

For a commutative Noetherian Artinian ring, finite length of finitely generated
modules makes the natural length additive as an integer-valued invariant.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators ZeroObject

namespace CategoryTheory.AdditiveEuler

/-- Integer-valued length on finitely generated modules; SES additivity needs the ring hypotheses below. -/
@[expose] def lengthInvariant (R : Type*) [CommRing R] (M : FGModuleCat R) : ℤ :=
  ((Module.length R M).toNat : ℤ)

/-- Finite lengths of finitely generated modules over a commutative Noetherian Artinian ring
make their integer-valued length additive on native short exact sequences. -/
theorem lengthInvariant_ses (R : Type*) [CommRing R] [IsNoetherianRing R]
    [IsArtinianRing R] (S : ShortComplex (FGModuleCat R)) (hS : S.ShortExact) :
    lengthInvariant R S.X₂ = lengthInvariant R S.X₁ + lengthInvariant R S.X₃ := by
  let F := forget₂ (FGModuleCat R) (ModuleCat R)
  have hMapped : (S.map F).ShortExact := hS.map_of_exact F
  have hLength : Module.length R S.X₂ =
      Module.length R S.X₁ + Module.length R S.X₃ := by
    exact Module.length_eq_add_of_exact (S.map F).f.hom (S.map F).g.hom
      hMapped.moduleCat_injective_f hMapped.moduleCat_surjective_g
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hMapped.exact)
  have h₁ : Module.length R S.X₁ ≠ ⊤ := Module.length_ne_top
  have h₃ : Module.length R S.X₃ ≠ ⊤ := Module.length_ne_top
  unfold lengthInvariant
  rw [hLength, ENat.toNat_add h₁ h₃]
  push_cast
  rfl

end CategoryTheory.AdditiveEuler
