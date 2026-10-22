/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

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
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  ext x
  change x = 0
  let e := (homologyAddEquiv K L n).trans
    (CohomologyClass.homAddEquiv (K := K) (L := L) (n := n))
  apply e.injective
  obtain ⟨f, hf⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective (e x)
  have hshift : (L⟦n⟧).Acyclic := by
    intro i
    exact ShortComplex.exact_of_iso
      ((shiftShortComplexFunctorIso C n i (n + i) rfl).app L).symm (hL (n + i))
  rw [map_zero, ← hf, HomotopyCategory.eq_of_homotopy f 0
    (IsKProjective.homotopyZero f hshift), Functor.map_zero]

/-- A cochain complex is K-projective if and only if its abelian-group-valued
Hom complex into every acyclic complex is acyclic. This is the characterization
of K-projectivity in Spaltenstein, *Resolutions of unbounded complexes*, §1. -/
lemma isKProjective_iff_acyclic_homComplex (K : CochainComplex C ℤ) :
    K.IsKProjective ↔ ∀ (L : CochainComplex C ℤ), L.Acyclic →
      (HomComplex K L).Acyclic := by
  refine ⟨fun _ L hL ↦ IsKProjective.acyclic_homComplex K L hL, fun h ↦ ?_⟩
  refine ⟨fun {L} f hL ↦ ?_⟩
  have hz := (h L hL 0).isZero_homology
  rw [IsZero.iff_id_eq_zero] at hz
  let e := homologyAddEquiv K L 0
  have hclass : CohomologyClass.mk (Cocycle.ofHom f) = 0 := by
    apply e.symm.injective
    have hx := ConcreteCategory.congr_hom hz
      (e.symm (CohomologyClass.mk (Cocycle.ofHom f)))
    simpa using hx
  obtain ⟨β, hβ⟩ :=
    (mem_coboundaries_iff (Cocycle.ofHom f) (-1) (by simp)).mp
      ((CohomologyClass.mk_eq_zero_iff _).mp hclass)
  exact ⟨(Cochain.equivHomotopy f 0).symm
    ⟨β, by simpa only [Cochain.ofHom_zero, add_zero, Cocycle.ofHom_coe] using hβ.symm⟩⟩

end CochainComplex
