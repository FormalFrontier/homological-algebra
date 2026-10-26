/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Cochain.HomComplexQuasiIso
public import HomologicalAlgebra.Cochain.KInjective
public import HomologicalAlgebra.QuasiIsoZero

/-!
# K-projectivity, K-injectivity, and quasi-isomorphisms

A cochain complex is K-projective if and only if postcomposition by every
quasi-isomorphism induces a quasi-isomorphism on its abelian-group-valued Hom
complex. Dually, it is K-injective if and only if precomposition by every
quasi-isomorphism preserves its Hom complex. The coefficient category is any
abelian category; no boundedness or products in that category are required.
Both properties are preserved by retractions of cochain complexes. This follows
by applying homology to the induced retraction of Hom complexes.

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
    have hzero : QuasiIso (0 : L ⟶ L) :=
      (HomologicalComplex.quasiIso_zero_iff_exactAt L L).mpr ⟨hL, hL⟩
    have hPrePostcompZero :
        HomComplex.prePostcomp (𝟙 K) (0 : L ⟶ L) = 0 := by
      apply HomComplex.prePostcomp_zero_right
    have hHomZero : QuasiIso
        (0 : HomComplex K L ⟶ HomComplex K L) := by
      simpa only [hPrePostcompZero] using h (0 : L ⟶ L) hzero
    exact ((HomologicalComplex.quasiIso_zero_iff_exactAt
      (HomComplex K L) (HomComplex K L)).mp hHomZero).1

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
    have hzero : QuasiIso (0 : K ⟶ K) :=
      (HomologicalComplex.quasiIso_zero_iff_exactAt K K).mpr ⟨hK, hK⟩
    have hPrePostcompZero :
        HomComplex.prePostcomp (0 : K ⟶ K) (𝟙 I) = 0 := by
      apply HomComplex.prePostcomp_zero_left
    have hHomZero : QuasiIso
        (0 : HomComplex K I ⟶ HomComplex K I) := by
      simpa only [hPrePostcompZero] using h (0 : K ⟶ K) hzero
    exact ((HomologicalComplex.quasiIso_zero_iff_exactAt
      (HomComplex K I) (HomComplex K I)).mp hHomZero).1

/-- A retract of a K-projective cochain complex is K-projective. -/
lemma IsKProjective.of_retract {K P : CochainComplex C ℤ} [P.IsKProjective]
    (i : K ⟶ P) (r : P ⟶ K) (h : i ≫ r = 𝟙 K) : K.IsKProjective := by
  apply (isKProjective_iff_acyclic_homComplex K).mpr
  intro L hL
  have hP := (isKProjective_iff_acyclic_homComplex P).mp
    (inferInstance : P.IsKProjective) L hL
  let a : HomComplex K L ⟶ HomComplex P L :=
    HomComplex.prePostcomp r (𝟙 L)
  let b : HomComplex P L ⟶ HomComplex K L :=
    HomComplex.prePostcomp i (𝟙 L)
  have hab : a ≫ b = 𝟙 (HomComplex K L) := by
    dsimp only [a, b]
    rw [← HomComplex.prePostcomp_comp, h]
    simp only [Category.comp_id, HomComplex.prePostcomp_id]
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  have hz : 𝟙 ((HomComplex P L).homology n) = 0 :=
    (IsZero.iff_id_eq_zero _).mp ((hP n).isZero_homology)
  have habn :
      HomologicalComplex.homologyMap a n ≫ HomologicalComplex.homologyMap b n =
        𝟙 ((HomComplex K L).homology n) := by
    rw [← HomologicalComplex.homologyMap_comp, hab,
      HomologicalComplex.homologyMap_id]
  have ha : HomologicalComplex.homologyMap a n = 0 := by
    calc
      HomologicalComplex.homologyMap a n =
          HomologicalComplex.homologyMap a n ≫
            𝟙 ((HomComplex P L).homology n) := by rw [Category.comp_id]
      _ = 0 := by rw [hz, comp_zero]
  rw [← habn, ha, zero_comp]

/-- A retract of a K-injective cochain complex is K-injective. -/
lemma IsKInjective.of_retract {K I : CochainComplex C ℤ} [I.IsKInjective]
    (i : K ⟶ I) (r : I ⟶ K) (hir : i ≫ r = 𝟙 K) :
    K.IsKInjective := by
  apply (isKInjective_iff_acyclic_homComplex K).mpr
  intro L hL
  have hI := (isKInjective_iff_acyclic_homComplex I).mp
    (inferInstance : I.IsKInjective) L hL
  let a : HomComplex L K ⟶ HomComplex L I :=
    HomComplex.prePostcomp (𝟙 L) i
  let b : HomComplex L I ⟶ HomComplex L K :=
    HomComplex.prePostcomp (𝟙 L) r
  have hab : a ≫ b = 𝟙 (HomComplex L K) := by
    dsimp only [a, b]
    rw [← HomComplex.prePostcomp_comp, Category.id_comp, hir,
      HomComplex.prePostcomp_id]
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  have hzero : 𝟙 ((HomComplex L I).homology n) = 0 :=
    (IsZero.iff_id_eq_zero ((HomComplex L I).homology n)).mp
      ((hI n).isZero_homology)
  calc
    𝟙 ((HomComplex L K).homology n) =
        HomologicalComplex.homologyMap a n ≫
          HomologicalComplex.homologyMap b n := by
      rw [← HomologicalComplex.homologyMap_comp, hab,
        HomologicalComplex.homologyMap_id]
    _ = HomologicalComplex.homologyMap a n ≫
        𝟙 ((HomComplex L I).homology n) ≫
          HomologicalComplex.homologyMap b n := by
      simp only [Category.id_comp]
    _ = 0 := by
      rw [hzero]
      simp

end CochainComplex
