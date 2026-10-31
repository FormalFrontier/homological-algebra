/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Cochain.HomComplexQuasiIsoCriteria
public import HomologicalAlgebra.Cochain.HomComplexShift

/-!
# K-objects detected by one Hom-cohomology degree

For any fixed integer `n`, a cochain complex is K-projective precisely when
the `n`-th cohomology of its canonical abelian-group-valued Hom complex into
every acyclic complex vanishes. Dually, K-injectivity is detected by vanishing
in the same fixed degree for Hom complexes from every acyclic complex.

Equivalently, postcomposition by every quasi-isomorphism induces an isomorphism
on degree-`n` Hom cohomology for a K-projective complex, and precomposition
detects K-injectivity. The converses use fixed-degree vanishing on shifted
acyclic tests and the canonical Hom-cohomology shift comparisons; the
preservation criteria supply vanishing by testing zero endomorphisms.
No boundedness, products or projective or injective resolutions in the
coefficient category are required.
-/

@[expose] public section

open CategoryTheory Category Limits

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

private lemma exactAt_shift_of_forall_exactAt
    (A : CochainComplex C ℤ) (s : ℤ) (hA : ∀ k, A.ExactAt k) :
    ∀ k, (A⟦s⟧).ExactAt k := by
  have : QuasiIso (0 : A ⟶ A) :=
    (HomologicalComplex.quasiIso_zero_iff_exactAt A A).mpr ⟨hA, hA⟩
  have hshift : QuasiIso
      (show A⟦s⟧ ⟶ A⟦s⟧ from (0 : A ⟶ A)⟦s⟧') := by
    infer_instance
  have hzeroShift : QuasiIso (0 : A⟦s⟧ ⟶ A⟦s⟧) := by
    simpa using hshift
  exact ((HomologicalComplex.quasiIso_zero_iff_exactAt
    (A⟦s⟧) (A⟦s⟧)).mp hzeroShift).1

/-- K-projectivity is detected by vanishing in one arbitrary fixed degree of
canonical Hom-complex cohomology into every acyclic complex. -/
lemma isKProjective_iff_isZero_homology_homComplex
    (K : CochainComplex C ℤ) (n : ℤ) :
    K.IsKProjective ↔ ∀ (A : CochainComplex C ℤ), A.Acyclic →
      IsZero ((HomComplex K A).homology n) := by
  constructor
  · intro hK A hA
    exact ((isKProjective_iff_acyclic_homComplex K).mp hK A hA n).isZero_homology
  · intro h
    apply (isKProjective_iff_acyclic_homComplex K).mpr
    intro A hA m
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact HomComplex.isZero_homology_of_forall_shift_right K A n
      (fun s ↦ h (A⟦s⟧) (exactAt_shift_of_forall_exactAt A s hA)) m

/-- K-injectivity is detected by vanishing in one arbitrary fixed degree of
canonical Hom-complex cohomology from every acyclic complex. -/
lemma isKInjective_iff_isZero_homology_homComplex
    (I : CochainComplex C ℤ) (n : ℤ) :
    I.IsKInjective ↔ ∀ (A : CochainComplex C ℤ), A.Acyclic →
      IsZero ((HomComplex A I).homology n) := by
  constructor
  · intro hI A hA
    exact ((isKInjective_iff_acyclic_homComplex I).mp hI A hA n).isZero_homology
  · intro h
    apply (isKInjective_iff_acyclic_homComplex I).mpr
    intro A hA m
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact HomComplex.isZero_homology_of_forall_shift_left A I n
      (fun s ↦ h (A⟦s⟧) (exactAt_shift_of_forall_exactAt A s hA)) m

/-- K-projectivity is detected by preservation of one arbitrary fixed degree
of canonical Hom-complex cohomology under every quasi-isomorphism in the target. -/
lemma isKProjective_iff_isIso_homologyMap_prePostcomp
    (K : CochainComplex C ℤ) (n : ℤ) :
    K.IsKProjective ↔
      ∀ {A B : CochainComplex C ℤ} (q : A ⟶ B), QuasiIso q →
        IsIso (HomologicalComplex.homologyMap (HomComplex.prePostcomp (𝟙 K) q) n) := by
  constructor
  · intro hK A B q hq
    have hHom := (isKProjective_iff_quasiIso_prePostcomp K).mp hK q hq
    rw [_root_.quasiIso_iff] at hHom
    have hn := hHom n
    rwa [_root_.quasiIsoAt_iff_isIso_homologyMap] at hn
  · intro h
    apply (isKProjective_iff_isZero_homology_homComplex K n).mpr
    intro A hA
    have hzero : QuasiIso (0 : A ⟶ A) :=
      (HomologicalComplex.quasiIso_zero_iff_exactAt A A).mpr ⟨hA, hA⟩
    have hn := h (0 : A ⟶ A) hzero
    have hPrePostcompZero :
        HomComplex.prePostcomp (𝟙 K) (0 : A ⟶ A) = 0 := by
      apply HomComplex.prePostcomp_zero_right
    rw [hPrePostcompZero] at hn
    have h0 : IsIso (0 : (HomComplex K A).homology n ⟶
        (HomComplex K A).homology n) := by
      simpa using hn
    exact ((CategoryTheory.Limits.isIsoZero_iff_source_target_isZero
      ((HomComplex K A).homology n)
      ((HomComplex K A).homology n)).mp h0).1

/-- K-injectivity is detected by preservation of one arbitrary fixed degree
of canonical Hom-complex cohomology under every quasi-isomorphism in the source. -/
lemma isKInjective_iff_isIso_homologyMap_prePostcomp
    (I : CochainComplex C ℤ) (n : ℤ) :
    I.IsKInjective ↔
      ∀ {A B : CochainComplex C ℤ} (q : A ⟶ B), QuasiIso q →
        IsIso (HomologicalComplex.homologyMap (HomComplex.prePostcomp q (𝟙 I)) n) := by
  constructor
  · intro hI A B q hq
    have hHom := (isKInjective_iff_quasiIso_prePostcomp I).mp hI q hq
    rw [_root_.quasiIso_iff] at hHom
    have hn := hHom n
    rwa [_root_.quasiIsoAt_iff_isIso_homologyMap] at hn
  · intro h
    apply (isKInjective_iff_isZero_homology_homComplex I n).mpr
    intro A hA
    have hzero : QuasiIso (0 : A ⟶ A) :=
      (HomologicalComplex.quasiIso_zero_iff_exactAt A A).mpr ⟨hA, hA⟩
    have hn := h (0 : A ⟶ A) hzero
    have hPrePostcompZero :
        HomComplex.prePostcomp (0 : A ⟶ A) (𝟙 I) = 0 := by
      apply HomComplex.prePostcomp_zero_left
    rw [hPrePostcompZero] at hn
    have h0 : IsIso (0 : (HomComplex A I).homology n ⟶
        (HomComplex A I).homology n) := by
      simpa using hn
    exact ((CategoryTheory.Limits.isIsoZero_iff_source_target_isZero
      ((HomComplex A I).homology n)
      ((HomComplex A I).homology n)).mp h0).1

end CochainComplex
