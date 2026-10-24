/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.SingleHomology
import HomologicalAlgebra.Cochain.HomComplexQuasiIso

/-!
# The rational stalk as a nonzero K-injective complex

The degree-zero stalk of ℚ over ℤ is K-injective by the standard bounded-below
termwise-injective criterion. Its coefficient injectivity is derived from
divisibility and Baer's criterion, rather than assumed. K-injectivity uses the
canonical definition: maps from acyclic complexes into this stalk are
null-homotopic.

All complexes use the additive structure supplied by the abelian category.
The degree-zero homology is nonzero, as witnessed by the canonical stalk
homology isomorphism with ℚ. Thus the model is neither acyclic nor contractible;
nonzero chain groups alone would not establish this nonvacuity condition.
-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex

namespace CochainComplex

private noncomputable abbrev integerModuleAbelian : Abelian (ModuleCat.{0} ℤ) :=
  inferInstance

private noncomputable abbrev integerModulePreadditive : Preadditive (ModuleCat.{0} ℤ) := by
  let : Abelian (ModuleCat.{0} ℤ) := integerModuleAbelian
  exact Abelian.toPreadditive

attribute [local instance] integerModulePreadditive

private lemma rationalModule_injective : Injective (ModuleCat.of ℤ ℚ) := by
  let : DivisibleBy ℚ ℤ := divisibleByIntOfCharZero
  let : Module.Injective ℤ ℚ := (Module.Baer.of_divisible ℚ).injective
  exact Module.injective_object_of_injective_module ℤ ℚ

private noncomputable def rationalStalk : CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  (single (ModuleCat ℤ) (.up ℤ) (0 : ℤ)).obj (ModuleCat.of ℤ ℚ)

private lemma rationalStalk_isKInjective : rationalStalk.IsKInjective := by
  let : rationalStalk.IsStrictlyGE 0 := by
    dsimp only [rationalStalk]
    infer_instance
  let : ∀ i : ℤ, Injective (rationalStalk.X i) := fun i ↦ by
    by_cases hi : i = 0
    · subst i
      simpa only [rationalStalk, single_obj_X_self] using rationalModule_injective
    · exact (isZero_single_obj_X (.up ℤ) (0 : ℤ) (ModuleCat.of ℤ ℚ) i hi).injective
  exact isKInjective_of_injective rationalStalk 0

example : ¬ IsZero (rationalStalk.homology 0) := by
  intro h
  have hQ : IsZero (ModuleCat.of ℤ ℚ) :=
    IsZero.of_iso h
      (singleObjHomologySelfIso (.up ℤ) (0 : ℤ) (ModuleCat.of ℤ ℚ)).symm
  have := ModuleCat.subsingleton_of_isZero hQ
  exact zero_ne_one (Subsingleton.elim (0 : ℚ) 1)

example {K L : CochainComplex (ModuleCat.{0} ℤ) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (HomComplex.prePostcomp f (𝟙 rationalStalk)) := by
  let : Abelian (ModuleCat.{0} ℤ) := integerModuleAbelian
  let : rationalStalk.IsKInjective := rationalStalk_isKInjective
  exact IsKInjective.quasiIso_prePostcomp rationalStalk f

end CochainComplex
