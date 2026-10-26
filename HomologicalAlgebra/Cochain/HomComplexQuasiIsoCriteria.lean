/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Cochain.HomComplexQuasiIso
public import HomologicalAlgebra.Cochain.KInjective

/-!
# K-projectivity, K-injectivity, and quasi-isomorphisms

A cochain complex is K-projective if and only if postcomposition by every
quasi-isomorphism induces a quasi-isomorphism on its abelian-group-valued Hom
complex. Dually, it is K-injective if and only if precomposition by every
quasi-isomorphism preserves its Hom complex. The coefficient category is any
abelian category; no boundedness or products in that category are required.

For the converse, the zero endomorphism of an acyclic complex is a
quasi-isomorphism. Its action on Hom-complex cohomology is therefore both zero
and invertible, forcing that cohomology to vanish.

The additive comparisons with homotopy-category morphisms used below follow
Joël Riou's Mathlib formalization (2025, Apache-2.0).

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, §1.
-/

@[expose] public section

open CategoryTheory Category Limits

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A cochain complex is K-projective precisely when its Hom complex sends
every quasi-isomorphism in the target variable to a quasi-isomorphism.

This is the quasi-isomorphism characterization in N. Spaltenstein,
*Resolutions of unbounded complexes*, §1. -/
lemma isKProjective_iff_quasiIso_prePostcomp (K : CochainComplex C ℤ) :
    K.IsKProjective ↔
      ∀ {X Y : CochainComplex C ℤ} (q : X ⟶ Y), QuasiIso q →
        QuasiIso (HomComplex.prePostcomp (𝟙 K) q) := by
  constructor
  · intro hK X Y q hq
    let := hK
    let := hq
    exact IsKProjective.quasiIso_prePostcomp K q
  · intro h
    apply (isKProjective_iff_acyclic_homComplex K).mpr
    intro L hL
    have hzero : QuasiIso (0 : L ⟶ L) := by
      rw [_root_.quasiIso_iff]
      intro n
      rw [_root_.quasiIsoAt_iff_isIso_homologyMap]
      have hz := (hL n).isZero_homology
      rw [IsZero.iff_id_eq_zero] at hz
      refine ⟨⟨0, ?_, ?_⟩⟩ <;> simpa using hz.symm
    have hpost := h (0 : L ⟶ L) hzero
    intro n
    rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
    let φ := HomologicalComplex.homologyMap
      (HomComplex.prePostcomp (𝟙 K) (0 : L ⟶ L)) n
    have hφ : IsIso φ := by
      rw [_root_.quasiIso_iff] at hpost
      have hn := hpost n
      rwa [_root_.quasiIsoAt_iff_isIso_homologyMap] at hn
    let := hφ
    let e := (HomComplex.homologyAddEquiv K L n).trans
      (HomComplex.CohomologyClass.homAddEquiv (K := K) (L := L) (n := n))
    have hφzero : φ = 0 := by
      ext x
      change φ x = 0
      apply e.injective
      rw [map_zero]
      simpa [φ, e] using
        (HomComplex.homologyAddEquiv_naturality (𝟙 K) (0 : L ⟶ L) n x)
    apply (cancel_epi φ).mp
    simp [hφzero]

/-- An integer cochain complex is K-injective if and only if precomposition
by every quasi-isomorphism induces a quasi-isomorphism on its canonical
abelian-group-valued Hom complex.

This is the quasi-isomorphism characterization in N. Spaltenstein,
*Resolutions of unbounded complexes*, §1. -/
lemma isKInjective_iff_quasiIso_prePostcomp (I : CochainComplex C ℤ) :
    I.IsKInjective ↔
      ∀ {K L : CochainComplex C ℤ} (f : K ⟶ L), QuasiIso f →
        QuasiIso (HomComplex.prePostcomp f (𝟙 I)) := by
  constructor
  · intro hI K L f hf
    have : I.IsKInjective := hI
    have : QuasiIso f := hf
    exact IsKInjective.quasiIso_prePostcomp I f
  · intro h
    apply (isKInjective_iff_acyclic_homComplex I).mpr
    intro K hK
    have : QuasiIso (0 : K ⟶ K) := by
      rw [_root_.quasiIso_iff]
      intro n
      rw [_root_.quasiIsoAt_iff_isIso_homologyMap]
      have hId : 𝟙 (K.homology n) = 0 :=
        (IsZero.iff_id_eq_zero (K.homology n)).mp ((hK n).isZero_homology)
      have hIso : IsIso (0 : K.homology n ⟶ K.homology n) := by
        refine ⟨⟨0, ?_, ?_⟩⟩ <;> simpa only [zero_comp] using hId.symm
      simpa using hIso
    have hPrePostcompZero :
        HomComplex.prePostcomp (0 : K ⟶ K) (𝟙 I) = 0 := by
      ext
      simp [HomComplex.prePostcomp]
      rfl
    have hHomZero : QuasiIso
        (0 : HomComplex K I ⟶ HomComplex K I) := by
      simpa only [hPrePostcompZero] using h (0 : K ⟶ K) inferInstance
    rw [_root_.quasiIso_iff] at hHomZero
    intro n
    rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
    have hn := hHomZero n
    rw [_root_.quasiIsoAt_iff_isIso_homologyMap] at hn
    have : IsIso (0 : (HomComplex K I).homology n ⟶
        (HomComplex K I).homology n) := by
      simpa using hn
    apply (cancel_mono (0 : (HomComplex K I).homology n ⟶
      (HomComplex K I).homology n)).mp
    simp

end CochainComplex
