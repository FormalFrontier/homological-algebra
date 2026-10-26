/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Zero maps and quasi-isomorphisms

The zero morphism between two homological complexes is a quasi-isomorphism
exactly when both complexes have zero homology in every degree. Equivalently,
both complexes are exact in every degree.
-/

@[expose] public section

open CategoryTheory Category Limits

universe w v u

namespace HomologicalComplex

variable {J : Type w} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {c : ComplexShape J}

/-- The zero map is a quasi-isomorphism if and only if both its source and
its target have zero homology in every degree. -/
lemma quasiIso_zero_iff_isZero_homology (K L : HomologicalComplex C c)
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] :
    QuasiIso (0 : K ⟶ L) ↔
      (∀ i, IsZero (K.homology i)) ∧ (∀ i, IsZero (L.homology i)) := by
  rw [_root_.quasiIso_iff]
  constructor
  · intro h
    have hzero (i : J) : IsIso (0 : K.homology i ⟶ L.homology i) := by
      have hi := h i
      rw [_root_.quasiIsoAt_iff_isIso_homologyMap] at hi
      simpa using hi
    constructor
    · intro i
      rw [IsZero.iff_id_eq_zero]
      let := hzero i
      apply (cancel_mono (0 : K.homology i ⟶ L.homology i)).mp
      simp
    · intro i
      rw [IsZero.iff_id_eq_zero]
      let := hzero i
      apply (cancel_epi (0 : K.homology i ⟶ L.homology i)).mp
      simp
  · rintro ⟨hK, hL⟩ i
    rw [_root_.quasiIsoAt_iff_isIso_homologyMap]
    have hKId : 𝟙 (K.homology i) = 0 :=
      (IsZero.iff_id_eq_zero (K.homology i)).mp (hK i)
    have hLId : 𝟙 (L.homology i) = 0 :=
      (IsZero.iff_id_eq_zero (L.homology i)).mp (hL i)
    have hIso : IsIso (0 : K.homology i ⟶ L.homology i) := by
      refine ⟨⟨0, ?_, ?_⟩⟩
      · simpa only [zero_comp] using hKId.symm
      · simpa only [zero_comp] using hLId.symm
    simpa using hIso

/-- The zero map is a quasi-isomorphism if and only if its source and target
are both exact in every degree. -/
lemma quasiIso_zero_iff_exactAt (K L : HomologicalComplex C c)
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] :
    QuasiIso (0 : K ⟶ L) ↔ (∀ i, K.ExactAt i) ∧ (∀ i, L.ExactAt i) := by
  simpa only [exactAt_iff_isZero_homology] using
    (quasiIso_zero_iff_isZero_homology K L)

end HomologicalComplex
