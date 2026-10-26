/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Zero maps and quasi-isomorphisms

In a category with zero morphisms, the zero map is an isomorphism exactly
when both objects are zero, without assuming the existence of a zero object.
Applied to homology, the zero map between homological complexes is a
quasi-isomorphism exactly when both complexes have zero homology in every
degree. Equivalently, both complexes are exact in every degree.
-/

@[expose] public section

open CategoryTheory Category Limits

universe w v u

namespace CategoryTheory.Limits

/-- The zero map is an isomorphism exactly when both objects are zero.
No existence hypothesis for a zero object is required. -/
lemma isIso_zero_iff_isZero {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (X Y : C) : IsIso (0 : X ⟶ Y) ↔ IsZero X ∧ IsZero Y := by
  constructor
  · intro h
    have hX : IsZero X := by
      rw [IsZero.iff_id_eq_zero]
      have := h
      apply (cancel_mono (0 : X ⟶ Y)).mp
      simp
    have : HasZeroObject C := CategoryTheory.Limits.IsZero.hasZeroObject hX
    exact (isIsoZero_iff_source_target_isZero X Y).mp h
  · rintro ⟨hX, hY⟩
    have : HasZeroObject C := CategoryTheory.Limits.IsZero.hasZeroObject hX
    exact (isIsoZero_iff_source_target_isZero X Y).mpr ⟨hX, hY⟩

end CategoryTheory.Limits

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
    have hzero (i : J) : IsZero (K.homology i) ∧ IsZero (L.homology i) := by
      rw [← CategoryTheory.Limits.isIso_zero_iff_isZero]
      have hi := h i
      rw [_root_.quasiIsoAt_iff_isIso_homologyMap] at hi
      simpa using hi
    exact ⟨fun i => (hzero i).1, fun i => (hzero i).2⟩
  · rintro ⟨hK, hL⟩ i
    rw [_root_.quasiIsoAt_iff_isIso_homologyMap]
    have hIso : IsIso (0 : K.homology i ⟶ L.homology i) :=
      (CategoryTheory.Limits.isIso_zero_iff_isZero _ _).mpr ⟨hK i, hL i⟩
    simpa using hIso

/-- The zero map is a quasi-isomorphism if and only if its source and target
are both exact in every degree. -/
lemma quasiIso_zero_iff_exactAt (K L : HomologicalComplex C c)
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] :
    QuasiIso (0 : K ⟶ L) ↔ (∀ i, K.ExactAt i) ∧ (∀ i, L.ExactAt i) := by
  simpa only [exactAt_iff_isZero_homology] using
    (quasiIso_zero_iff_isZero_homology K L)

end HomologicalComplex
