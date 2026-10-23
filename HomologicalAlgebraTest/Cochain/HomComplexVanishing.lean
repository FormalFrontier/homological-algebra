/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Cochain.HomComplexVanishing
public import HomologicalAlgebraTest.Cochain.HomComplexFunctoriality
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Hom-complex vanishing and integer stalks

The contract applies in an arbitrary preadditive category, with independent
object and morphism universes. The zero-source case gives acyclicity. For the
rational stalk ℚ[0], the identity is not null-homotopic and degree-zero Hom
cohomology is nonzero.

Let `S_d` be the integer stalk in degree `d`. The same stalks in degrees zero
and one exhibit the shift convention: `H¹ Hom(S₀, S₀) = 0`, whereas
`H¹ Hom(S₀, S₁)` is nonzero. In the latter case degree-zero cohomology vanishes,
but the generator `S₀ ⟶ S₁⟦1⟧` is not null-homotopic, so the Hom complex is not
acyclic.
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

example (K L : CochainComplex C ℤ) (hK : IsZero K) :
    (HomComplex K L).Acyclic := by
  apply (HomComplex.acyclic_iff K L).mpr
  intro n f
  exact ⟨Homotopy.ofEq (hK.eq_of_src f 0)⟩

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

namespace HomologicalAlgebraTest.HomComplexVanishing

open CochainComplex CochainComplex.HomComplex
open HomologicalAlgebraTest.HomComplexFunctoriality

private lemma stalk_homology_isZero (d n : ℤ) (h : n ≠ d) :
    IsZero ((HomComplex (stalk 0) (stalk d)).homology n) := by
  apply (isZero_homology_iff (stalk 0) (stalk d) n).mpr
  intro f
  have hf : f = 0 := by
    apply (Cocycle.equivHomShift (K := stalk 0) (L := stalk d) (n := n)).injective
    apply Subtype.ext
    apply Cochain.ext
    intro p q hpq
    by_cases hp : p = 0
    · subst p
      exact (isZero_single_obj_X (.up ℤ) d Z q (by omega)).eq_of_tgt _ _
    · exact (isZero_single_obj_X (.up ℤ) (0 : ℤ) Z p hp).eq_of_src _ _
  exact ⟨Homotopy.ofEq hf⟩

private lemma stalk_generator_not_null (d : ℤ) :
    ¬ Nonempty (Homotopy
      ((Cocycle.equivHomShift (K := stalk 0) (L := stalk d) (n := d)).symm
        (stalkCocycle d 1)) 0) := by
  intro h
  apply stalkClass_ne_zero d 1 (by norm_num)
  apply (CohomologyClass.toHom_bijective (stalk 0) (stalk d) d).1
  rw [map_zero, stalkClass, CohomologyClass.toHom_mk,
    HomotopyCategory.quotient_map_eq_zero_iff]
  exact h

private lemma stalk_homology_not_isZero (d : ℤ) :
    ¬ IsZero ((HomComplex (stalk 0) (stalk d)).homology d) := by
  intro h
  exact stalk_generator_not_null d
    ((isZero_homology_iff (stalk 0) (stalk d) d).mp h _)

example :
    IsZero ((HomComplex (stalk 0) (stalk 0)).homology 1) ∧
      ¬ IsZero ((HomComplex (stalk 0) (stalk 0)).homology 0) ∧
      IsZero ((HomComplex (stalk 0) (stalk 1)).homology 0) ∧
      ¬ IsZero ((HomComplex (stalk 0) (stalk 1)).homology 1) ∧
      (∃ f : stalk 0 ⟶ (stalk 1)⟦(1 : ℤ)⟧, ¬ Nonempty (Homotopy f 0)) ∧
      ¬ (HomComplex (stalk 0) (stalk 1)).Acyclic := by
  refine ⟨stalk_homology_isZero 0 1 (by norm_num), stalk_homology_not_isZero 0,
    stalk_homology_isZero 1 0 (by norm_num), stalk_homology_not_isZero 1, ?_, ?_⟩
  · exact ⟨(Cocycle.equivHomShift (K := stalk 0) (L := stalk 1) (n := (1 : ℤ))).symm
      (stalkCocycle 1 1), stalk_generator_not_null 1⟩
  · intro h
    exact stalk_generator_not_null 1 ((acyclic_iff (stalk 0) (stalk 1)).mp h 1 _)

end HomologicalAlgebraTest.HomComplexVanishing
