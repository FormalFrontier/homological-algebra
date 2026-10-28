/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-!
# Mapping cones of K-projective and K-injective complexes

The canonical mapping cone of any cochain map between two K-projective complexes
is K-projective. Dually, it is K-injective when both endpoints are K-injective.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/- The canonical cone of any map between two K-projective complexes is K-projective. -/
example {K L : CochainComplex C ℤ} (f : K ⟶ L)
    [K.IsKProjective] [L.IsKProjective] : (mappingCone f).IsKProjective := by
  apply (isKProjective_iff_leftOrthogonal (mappingCone f)).2
  exact ((HomotopyCategory.subcategoryAcyclic C).leftOrthogonal).ext_of_isTriangulatedClosed₃
    (mappingCone.triangleh f)
    (HomotopyCategory.mappingCone_triangleh_distinguished f)
    (IsKProjective.leftOrthogonal K) (IsKProjective.leftOrthogonal L)

/- The canonical cone of any map between two K-injective complexes is K-injective. -/
example {K L : CochainComplex C ℤ} (f : K ⟶ L)
    [K.IsKInjective] [L.IsKInjective] : (mappingCone f).IsKInjective := by
  apply (isKInjective_iff_rightOrthogonal (mappingCone f)).2
  exact ((HomotopyCategory.subcategoryAcyclic C).rightOrthogonal).ext_of_isTriangulatedClosed₃
    (mappingCone.triangleh f)
    (HomotopyCategory.mappingCone_triangleh_distinguished f)
    (IsKInjective.rightOrthogonal K) (IsKInjective.rightOrthogonal L)

end CochainComplex
