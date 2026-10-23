/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-!
# Vanishing of Hom-complex cohomology

For integer cochain complexes in a preadditive category, degree-`n` cohomology
of the Hom complex vanishes precisely when every map to the target shifted by
`n` is null-homotopic. Consequently, the Hom complex is acyclic precisely when
all such shifted maps are null-homotopic. Its degree-zero specialization uses
unshifted maps, via the zero-shift isomorphism.

The Hom complex takes values in abelian groups; its terms are products of
morphism groups, so no products or zero object in the original category are
required. The proofs use the additive comparisons with cohomology classes and
morphisms in the homotopy category.
-/

@[expose] public section

open CategoryTheory Category Limits

universe v u

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Degree-`n` cohomology of the Hom complex vanishes if and only if every map
to the target shifted by `n` is null-homotopic. Only preadditivity of the ambient
category is required; homology is computed in abelian groups. -/
lemma isZero_homology_iff (K L : CochainComplex C ℤ) (n : ℤ) :
    IsZero ((HomComplex K L).homology n) ↔
      ∀ f : K ⟶ L⟦n⟧, Nonempty (Homotopy f 0) := by
  let Q := HomotopyCategory.quotient C (.up ℤ)
  let e := (homologyAddEquiv K L n).trans
    (CohomologyClass.homAddEquiv (K := K) (L := L) (n := n))
  constructor
  · intro hz f
    rw [← HomotopyCategory.quotient_map_eq_zero_iff]
    change Q.map f = 0
    rw [IsZero.iff_id_eq_zero] at hz
    have hx : e.symm (Q.map f) = 0 := by
      have hh := ConcreteCategory.congr_hom hz (e.symm (Q.map f))
      simpa using hh
    simpa only [AddEquiv.apply_symm_apply, map_zero] using congrArg e hx
  · intro h
    rw [IsZero.iff_id_eq_zero]
    ext x
    change x = 0
    apply e.injective
    obtain ⟨f, hf⟩ := Q.map_surjective (e x)
    rw [map_zero, ← hf, HomotopyCategory.eq_of_homotopy f 0 (h f).some,
      Functor.map_zero]

/-- Degree-zero cohomology of the canonical Hom complex vanishes if and only if
every morphism of cochain complexes is null-homotopic. This only requires the
ambient category to be preadditive; the homology is computed in abelian groups. -/
lemma isZero_homology_zero_iff (K L : CochainComplex C ℤ) :
    IsZero ((HomComplex K L).homology 0) ↔
      ∀ f : K ⟶ L, Nonempty (Homotopy f 0) := by
  let ε := (shiftFunctorZero (CochainComplex C ℤ) ℤ).app L
  constructor
  · intro hz f
    obtain ⟨h⟩ := (isZero_homology_iff K L 0).mp hz (f ≫ ε.inv)
    refine ⟨?_⟩
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, zero_comp]
      using h.compRight ε.hom
  · intro h
    apply (isZero_homology_iff K L 0).mpr
    intro f
    obtain ⟨hf⟩ := h (f ≫ ε.hom)
    refine ⟨?_⟩
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, zero_comp]
      using hf.compRight ε.inv

/-- The Hom complex is acyclic if and only if every map to every integer shift
of the target is null-homotopic. -/
lemma acyclic_iff (K L : CochainComplex C ℤ) :
    (HomComplex K L).Acyclic ↔
      ∀ (n : ℤ) (f : K ⟶ L⟦n⟧), Nonempty (Homotopy f 0) := by
  constructor
  · intro h n
    exact (isZero_homology_iff K L n).mp ((h n).isZero_homology)
  · intro h n
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (isZero_homology_iff K L n).mpr (h n)

end CochainComplex.HomComplex
