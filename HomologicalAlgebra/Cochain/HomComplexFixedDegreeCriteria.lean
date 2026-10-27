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
postcomposition by every quasi-isomorphism induces an isomorphism on the
`n`-th cohomology of its canonical abelian-group-valued Hom complex. The dual
criterion detects K-injectivity by precomposition.

The converse tests zero endomorphisms of all shifts of acyclic complexes.
The resulting fixed-degree vanishing detects vanishing in every degree through
the canonical Hom-cohomology shift comparisons. No boundedness, products or
projective or injective resolutions in the coefficient category are required.
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
    apply (isKProjective_iff_acyclic_homComplex K).mpr
    intro A hA m
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    refine HomComplex.isZero_homology_of_forall_shift_right K A n ?_ m
    intro s
    have hs := exactAt_shift_of_forall_exactAt A s hA
    have hzero : QuasiIso (0 : A⟦s⟧ ⟶ A⟦s⟧) :=
      (HomologicalComplex.quasiIso_zero_iff_exactAt (A⟦s⟧) (A⟦s⟧)).mpr ⟨hs, hs⟩
    have hn := h (0 : A⟦s⟧ ⟶ A⟦s⟧) hzero
    have hPrePostcompZero :
        HomComplex.prePostcomp (𝟙 K) (0 : A⟦s⟧ ⟶ A⟦s⟧) = 0 := by
      apply HomComplex.prePostcomp_zero_right
    rw [hPrePostcompZero] at hn
    have h0 : IsIso (0 : (HomComplex K (A⟦s⟧)).homology n ⟶
        (HomComplex K (A⟦s⟧)).homology n) := by
      simpa using hn
    exact ((CategoryTheory.Limits.isIsoZero_iff_source_target_isZero
      ((HomComplex K (A⟦s⟧)).homology n)
      ((HomComplex K (A⟦s⟧)).homology n)).mp h0).1

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
    apply (isKInjective_iff_acyclic_homComplex I).mpr
    intro A hA m
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    refine HomComplex.isZero_homology_of_forall_shift_left A I n ?_ m
    intro s
    have hs := exactAt_shift_of_forall_exactAt A s hA
    have hzero : QuasiIso (0 : A⟦s⟧ ⟶ A⟦s⟧) :=
      (HomologicalComplex.quasiIso_zero_iff_exactAt (A⟦s⟧) (A⟦s⟧)).mpr ⟨hs, hs⟩
    have hn := h (0 : A⟦s⟧ ⟶ A⟦s⟧) hzero
    have hPrePostcompZero :
        HomComplex.prePostcomp (0 : A⟦s⟧ ⟶ A⟦s⟧) (𝟙 I) = 0 := by
      apply HomComplex.prePostcomp_zero_left
    rw [hPrePostcompZero] at hn
    have h0 : IsIso (0 : (HomComplex (A⟦s⟧) I).homology n ⟶
        (HomComplex (A⟦s⟧) I).homology n) := by
      simpa using hn
    exact ((CategoryTheory.Limits.isIsoZero_iff_source_target_isZero
      ((HomComplex (A⟦s⟧) I).homology n)
      ((HomComplex (A⟦s⟧) I).homology n)).mp h0).1

end CochainComplex
