/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import HomologicalAlgebra.Cochain.DiskProjectivity

/-!
# A projective disk lift and its lower component

An ordinary categorical lift from a projective disk across an epimorphism is
represented by `diskDesc`. The lower-component equation agrees with the
coefficient lifting equation in the same category, without additive hypotheses.
-/

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]
  [HasZeroMorphisms C] [HasZeroObject C]

namespace CochainComplex

example (n : ℤ) (X : C) [Projective X] {K L : CochainComplex C ℤ}
    (p : K ⟶ L) [Epi p] (a : X ⟶ L.X n) :
    ∃ b : X ⟶ K.X n,
      diskDesc n K b ≫ p = diskDesc n L a ∧ b ≫ p.f n = a := by
  let l := Projective.factorThru (diskDesc n L a) p
  have hl : l ≫ p = diskDesc n L a := Projective.factorThru_comp _ _
  refine ⟨diskHomEquiv n X K l, ?_, ?_⟩
  · rw [← diskHomEquiv_symm_apply, Equiv.symm_apply_apply]
    exact hl
  · calc
      diskHomEquiv n X K l ≫ p.f n = diskHomEquiv n X L (l ≫ p) :=
        (diskHomEquiv_naturality_right n X l p).symm
      _ = a := by
        rw [hl, ← diskHomEquiv_symm_apply, Equiv.apply_symm_apply]

end CochainComplex
