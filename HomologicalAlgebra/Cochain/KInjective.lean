/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import HomologicalAlgebra.Cochain.HomComplexVanishing

/-!
# K-injectivity and acyclicity of Hom complexes

A cochain complex is K-injective precisely when the canonical complex of morphisms
from every acyclic cochain complex into it is acyclic. The Hom complex takes values
in abelian groups: its terms are products of morphism groups, not products in the
original category.

K-injectivity is stable under integer shifts, so every map from an acyclic
complex to a shifted target is null-homotopic. The Hom-complex vanishing
criterion then gives acyclicity in every degree. Conversely, degree-zero Hom
cohomology detects whether all maps from an acyclic complex are null-homotopic.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, §1.
-/

@[expose] public section

open CategoryTheory Category Limits

universe v u

namespace CochainComplex

open HomComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The canonical complex of morphisms from an acyclic complex into a
K-injective complex is acyclic, in every integer degree. -/
lemma IsKInjective.acyclic_homComplex (K L : CochainComplex C ℤ)
    [L.IsKInjective] (hK : K.Acyclic) : (HomComplex K L).Acyclic := by
  apply (HomComplex.acyclic_iff K L).mpr
  intro n f
  exact IsKInjective.nonempty_homotopy_zero f hK

/-- A cochain complex is K-injective if and only if its canonical
abelian-group-valued Hom complex from every acyclic complex is acyclic.
This is the characterization in Spaltenstein, *Resolutions of unbounded
complexes*, §1. -/
lemma isKInjective_iff_acyclic_homComplex (L : CochainComplex C ℤ) :
    L.IsKInjective ↔ ∀ (K : CochainComplex C ℤ), K.Acyclic →
      (HomComplex K L).Acyclic := by
  refine ⟨fun _ K hK ↦ IsKInjective.acyclic_homComplex K L hK, fun h ↦ ?_⟩
  refine ⟨fun {K} f hK ↦ ?_⟩
  exact (HomComplex.isZero_homology_zero_iff K L).mp
    ((h K hK 0).isZero_homology) f

end CochainComplex
