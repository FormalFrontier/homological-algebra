/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import HomologicalAlgebra.Abelian.NoetherianObject
public import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-!
# Noetherian homology of short complexes

The canonical homology of a short complex in an abelian category is Noetherian
whenever its middle object is Noetherian. Cycles embed in the middle object, and
the homology projection exhibits homology as an epimorphic image of cycles.
-/

@[expose] public section

universe v u

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The homology of a short complex with Noetherian middle object is Noetherian. -/
lemma isNoetherianObject_homology (S : ShortComplex C) [IsNoetherianObject S.X₂] :
    IsNoetherianObject S.homology := by
  have : IsNoetherianObject S.cycles := isNoetherianObject_of_mono S.iCycles
  exact isNoetherianObject_of_epi S.homologyπ

end CategoryTheory.ShortComplex
