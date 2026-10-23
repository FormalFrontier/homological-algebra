/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-!
# Vanishing of degree-zero Hom-complex cohomology

For integer cochain complexes in a preadditive category, degree-zero cohomology
of the canonical Hom complex vanishes precisely when every cochain map is
null-homotopic. The Hom complex takes values in abelian groups; its terms are
products of morphism groups, so no products or zero object in the original
category are required.

The comparison uses unshifted degree-zero cocycles and cohomology classes.
-/

@[expose] public section

open CategoryTheory Category Limits

universe v u

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Degree-zero cohomology of the canonical Hom complex vanishes if and only if
every morphism of cochain complexes is null-homotopic. This only requires the
ambient category to be preadditive; the homology is computed in abelian groups. -/
lemma isZero_homology_zero_iff (K L : CochainComplex C ℤ) :
    IsZero ((HomComplex K L).homology 0) ↔
      ∀ f : K ⟶ L, Nonempty (Homotopy f 0) := by
  constructor
  · intro hz f
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
  · intro h
    rw [IsZero.iff_id_eq_zero]
    ext x
    change x = 0
    let e := homologyAddEquiv K L 0
    apply e.injective
    rw [map_zero]
    obtain ⟨z, hz⟩ := CohomologyClass.mk_surjective (e x)
    rw [← hz, CohomologyClass.mk_eq_zero_iff]
    apply (mem_coboundaries_iff z (-1) (by simp)).mpr
    obtain ⟨ho⟩ := h (Cocycle.homOf z)
    exact ⟨Cochain.ofHomotopy ho, by
      simp only [δ_ofHomotopy, Cochain.ofHom_zero, sub_zero,
        Cocycle.cochain_ofHom_homOf_eq_coe]⟩

end CochainComplex.HomComplex
