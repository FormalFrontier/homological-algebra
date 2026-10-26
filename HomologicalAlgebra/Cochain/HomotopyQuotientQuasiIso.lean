/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Homology.DerivedCategory.KProjective

public import HomologicalAlgebra.Cochain.HomComplexQuasiIsoCriteria

/-!
# Quasi-isomorphisms and the homotopy quotient

Between two K-projective complexes, or between two K-injective complexes,
a cochain map is a quasi-isomorphism if and only if its image in the canonical
homotopy category is an isomorphism.
-/

@[expose] public section

universe u v

open CategoryTheory HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Between K-projective complexes, quasi-isomorphisms are exactly the maps
that become isomorphisms in the canonical homotopy category. -/
lemma IsKProjective.quasiIso_iff_isIso_quotient_map
    {K L : CochainComplex C ℤ} [K.IsKProjective] [L.IsKProjective]
    (q : K ⟶ L) :
    QuasiIso q ↔ IsIso ((HomotopyCategory.quotient C (.up ℤ)).map q) := by
  exact (CochainComplex.IsKProjective.quasiIso_iff q).trans
    (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences q).symm

/-- Between K-injective complexes, quasi-isomorphisms are exactly the maps
that become isomorphisms in the canonical homotopy category. -/
lemma IsKInjective.quasiIso_iff_isIso_quotient_map
    {K L : CochainComplex C ℤ} [K.IsKInjective] [L.IsKInjective]
    (q : K ⟶ L) :
    QuasiIso q ↔ IsIso ((HomotopyCategory.quotient C (.up ℤ)).map q) := by
  exact (CochainComplex.IsKInjective.quasiIso_iff q).trans
    (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences q).symm

end CochainComplex
