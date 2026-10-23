/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import HomologicalAlgebra.Cochain.HomComplexVanishing

/-!
# K-projectivity and acyclicity of Hom complexes

A cochain complex is K-projective precisely when its complex of morphisms into
any acyclic cochain complex is acyclic. The Hom complex takes values in abelian
groups, so no products in the original category are required.

The proof uses Mathlib's additive comparisons between Hom-complex cohomology,
cohomology classes of cocycles, and morphisms in the homotopy category. In the
converse, degree-zero cohomology suffices: its vanishing makes every map into
an acyclic complex a coboundary, hence null-homotopic. The acyclic-target
hypothesis is essential: the Hom complex from ℤ[0] to itself has nonzero
cohomology in degree zero.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, §1.
-/

@[expose] public section

open CategoryTheory Category Limits

universe v u

namespace CochainComplex

open HomComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The complex of morphisms from a K-projective complex to an acyclic complex
is acyclic. This recovers the Hom-complex condition in Spaltenstein,
*Resolutions of unbounded complexes*, §1. -/
lemma IsKProjective.acyclic_homComplex (K L : CochainComplex C ℤ)
    [K.IsKProjective] (hL : L.Acyclic) : (HomComplex K L).Acyclic := by
  apply (HomComplex.acyclic_iff K L).mpr
  intro n f
  have hshift : (L⟦n⟧).Acyclic := by
    intro i
    exact ShortComplex.exact_of_iso
      ((shiftShortComplexFunctorIso C n i (n + i) rfl).app L).symm (hL (n + i))
  exact ⟨IsKProjective.homotopyZero f hshift⟩

/-- A cochain complex is K-projective if and only if its abelian-group-valued
Hom complex into every acyclic complex is acyclic. This is the characterization
of K-projectivity in Spaltenstein, *Resolutions of unbounded complexes*, §1. -/
lemma isKProjective_iff_acyclic_homComplex (K : CochainComplex C ℤ) :
    K.IsKProjective ↔ ∀ (L : CochainComplex C ℤ), L.Acyclic →
      (HomComplex K L).Acyclic := by
  refine ⟨fun _ L hL ↦ IsKProjective.acyclic_homComplex K L hL, fun h ↦ ?_⟩
  refine ⟨fun {L} f hL ↦ ?_⟩
  exact (HomComplex.isZero_homology_zero_iff K L).mp
    ((h L hL 0).isZero_homology) f

end CochainComplex
