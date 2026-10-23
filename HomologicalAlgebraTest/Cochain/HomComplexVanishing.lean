/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Cochain.HomComplexVanishing
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Degree-zero Hom-complex vanishing

The contract applies in an arbitrary preadditive category, with independent
object and morphism universes. For the rational stalk ℚ[0], the identity is not
null-homotopic and degree-zero Hom cohomology is nonzero. Zero source and zero
target are conditional boundary cases, not hypotheses of the general result.
-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex

universe v u

namespace CochainComplex

open HomComplex

section

variable {C : Type u} [Category.{v} C] [Preadditive C]


example (K L : CochainComplex C ℤ) (hK : IsZero K) :
    IsZero ((HomComplex K L).homology 0) := by
  apply (HomComplex.isZero_homology_zero_iff K L).mpr
  intro f
  exact ⟨Homotopy.ofEq (hK.eq_of_src f 0)⟩

example (K L : CochainComplex C ℤ) (hL : IsZero L) :
    IsZero ((HomComplex K L).homology 0) := by
  apply (HomComplex.isZero_homology_zero_iff K L).mpr
  intro f
  exact ⟨Homotopy.ofEq (hL.eq_of_tgt f 0)⟩

end

example :
    let K : CochainComplex (ModuleCat ℚ) ℤ :=
      (single (ModuleCat ℚ) (.up ℤ) (0 : ℤ)).obj (ModuleCat.of ℚ ℚ)
    ¬ IsZero ((HomComplex K K).homology 0) ∧
      ¬ (∀ f : K ⟶ K, Nonempty (Homotopy f 0)) := by
  let K : CochainComplex (ModuleCat ℚ) ℤ :=
    (single (ModuleCat ℚ) (.up ℤ) (0 : ℤ)).obj (ModuleCat.of ℚ ℚ)
  change ¬ IsZero ((HomComplex K K).homology 0) ∧
    ¬ (∀ f : K ⟶ K, Nonempty (Homotopy f 0))
  have hnotid : ¬ Nonempty (Homotopy (𝟙 K) 0) := by
    rintro ⟨ho⟩
    have hβ : Cochain.ofHomotopy ho = 0 := by
      apply Cochain.ext
      intro p q hpq
      by_cases hp : p = 0
      · apply (isZero_single_obj_X (.up ℤ) (0 : ℤ) (ModuleCat.of ℚ ℚ) q
          (by omega)).eq_of_tgt
      · apply (isZero_single_obj_X (.up ℤ) (0 : ℤ) (ModuleCat.of ℚ ℚ) p hp).eq_of_src
    have hcochain : Cochain.ofHom (𝟙 K) = 0 := by
      have hh := δ_ofHomotopy ho
      rw [hβ] at hh
      simpa using hh.symm
    have hz₀ : IsZero (K.X 0) := by
      rw [IsZero.iff_id_eq_zero]
      simpa using Cochain.congr_v hcochain (0 : ℤ) 0 (by simp)
    dsimp only [K] at hz₀
    rw [single_obj_X_self] at hz₀
    have := ModuleCat.subsingleton_of_isZero hz₀
    exact zero_ne_one (Subsingleton.elim (0 : ℚ) 1)
  have hnotall : ¬ (∀ f : K ⟶ K, Nonempty (Homotopy f 0)) :=
    fun h ↦ hnotid (h (𝟙 K))
  exact ⟨fun h ↦ hnotall ((HomComplex.isZero_homology_zero_iff K K).mp h), hnotall⟩

end CochainComplex
