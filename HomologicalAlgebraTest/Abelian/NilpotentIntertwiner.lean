/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import HomologicalAlgebra

/-!
# Nilpotent epimorphic endomorphisms

A nilpotent epimorphic endomorphism forces its object to be zero. Only zero
morphisms are needed: no abelian structure or chain condition is assumed.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

example {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {X : C}
    (f : End X) [Epi f] (hf : IsNilpotent f) : IsZero X := by
  apply (IsZero.iff_id_eq_zero X).2
  exact End.eq_zero_of_epi_of_isNilpotent f f (𝟙 X) (by simp) hf
