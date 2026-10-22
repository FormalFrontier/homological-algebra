/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import HomologicalAlgebra.ChainComplex.Projective
import Mathlib.Algebra.Homology.Single

/-!
# Stalk complexes and the bounded-projective criterion

A stalk on a nonzero projective object gives a canonical application of the
particular-map criterion: its zero endomorphism cannot be a quasi-isomorphism,
although the stalk is homotopy equivalent to itself by the identity. The argument
uses the equality of the forward map with this zero map, not merely the existence
of an objectwise homotopy equivalence. The stalk's lower cutoff is also sharp.
-/

universe v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

private lemma projective_single_term (P : C) [Projective P] (n i : ℤ) :
    Projective (((single C (.down ℤ) n).obj P).X i) := by
  by_cases hi : i = n
  · subst i
    simpa only [single_obj_X_self] using (inferInstance : Projective P)
  · exact (isZero_single_obj_X (.down ℤ) n P i hi).projective

private theorem not_quasiIso_zero_single (P : C) [Projective P]
    (hP : ¬ IsZero P) (n : ℤ) :
    ¬ QuasiIso (0 : (single C (.down ℤ) n).obj P ⟶ (single C (.down ℤ) n).obj P) := by
  let K : ChainComplex C ℤ := (single C (.down ℤ) n).obj P
  let : ∀ i, Projective (K.X i) := fun i ↦ projective_single_term P n i
  have hK (i : ℤ) (hi : i < n) : IsZero (K.X i) :=
    isZero_single_obj_X (.down ℤ) n P i (by lia)
  intro hf
  obtain ⟨e, he⟩ :=
    (quasiIso_iff_of_projective_of_isZero_below n n hK hK (0 : K ⟶ K)).mp hf
  have h := e.homotopyHomInvId.comm n
  have hid : 𝟙 P = 0 := by
    have hidX :
        𝟙 (((single C (.down ℤ) n).obj P).X n) = 0 := by
      simpa [K, he, dNext, prevD] using h.symm
    exact (IsZero.iff_id_eq_zero P).mp
      (((IsZero.iff_id_eq_zero _).mpr hidX).of_iso
        (singleObjXSelf (.down ℤ) n P).symm)
  exact hP ((IsZero.iff_id_eq_zero P).mpr hid)

private theorem not_isZero_below_single_succ (P : C) (hP : ¬ IsZero P) (n : ℤ) :
    ¬ (∀ i, i < n + 1 → IsZero (((single C (.down ℤ) n).obj P).X i)) := by
  intro h
  exact hP ((h n (by lia)).of_iso (singleObjXSelf (.down ℤ) n P).symm)

end ChainComplex
