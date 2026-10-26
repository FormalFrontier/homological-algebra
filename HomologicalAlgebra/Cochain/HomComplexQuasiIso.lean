/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.Types.Basic

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import HomologicalAlgebra.Cochain.HomComplexFunctoriality
public import HomologicalAlgebra.Cochain.KProjective

/-!
# Quasi-isomorphism invariance of Hom complexes

Pre- and postcomposition by homotopy equivalences induce a quasi-isomorphism
of Hom complexes over any preadditive category. More generally, it suffices
that both maps become isomorphisms in the homotopy category. These statements
apply to arbitrary integer-indexed complexes and require homology only for
the resulting Hom complexes, which take values in abelian groups.

Postcomposition by a quasi-isomorphism also induces a quasi-isomorphism on the
complex of morphisms from a K-projective complex over an abelian category.
Dually, precomposition by a quasi-isomorphism induces a quasi-isomorphism on
the complex of morphisms to a K-injective complex. The other complexes are
arbitrary. No products in the coefficient category are required.

For quasi-isomorphisms `f : K ⟶ L` and `g : I ⟶ J`, simultaneous
pre- and postcomposition is a quasi-isomorphism under either crossed pair
of hypotheses: `K.IsKProjective` and `I.IsKInjective`, or `L.IsKProjective`
and `J.IsKInjective`. The proofs factor through the Hom complex from `K`
to `I`, or from `L` to `J`, respectively, and reuse the one-variable
statements.

The K-projectivity and K-injectivity formulations follow Spaltenstein. The
Hom-complex model and its additive comparisons with morphisms in the homotopy
and derived categories are Mathlib constructions due to Joël Riou
(2025, Apache-2.0).

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, §1.
-/

@[expose] public section

open CategoryTheory Category

universe v u

namespace CochainComplex

section

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace HomComplex

/-- Pre- and postcomposition by homotopy equivalences induce a quasi-isomorphism
of Hom complexes. The coefficient category need only be preadditive, and all
four integer-indexed complexes may be unbounded. -/
lemma quasiIso_prePostcomp_of_homotopyEquiv
    {K1 K2 L1 L2 : CochainComplex C ℤ}
    (eK : HomotopyEquiv K2 K1) (eL : HomotopyEquiv L1 L2) :
    QuasiIso (prePostcomp eK.hom eL.hom) := by
  classical
  let e : HomotopyEquiv (HomComplex K1 L1) (HomComplex K2 L2) :=
    { hom := prePostcomp eK.hom eL.hom
      inv := prePostcomp eK.inv eL.inv
      homotopyHomInvId := by
        simpa only [prePostcomp_comp, prePostcomp_id] using
          (prePostcompHomotopy eK.homotopyInvHomId eL.homotopyHomInvId)
      homotopyInvHomId := by
        simpa only [prePostcomp_comp, prePostcomp_id] using
          (prePostcompHomotopy eK.homotopyHomInvId eL.homotopyInvHomId) }
  exact e.quasiIso_hom

/-- If both maps become isomorphisms in the homotopy category, their joint
pre- and postcomposition map is a quasi-isomorphism of Hom complexes.
No homology, projectivity, or injectivity assumptions on the coefficient
category or on its complexes are required. -/
lemma quasiIso_prePostcomp_of_isIso_quotient_map
    {K1 K2 L1 L2 : CochainComplex C ℤ}
    (α : K2 ⟶ K1) (β : L1 ⟶ L2)
    [IsIso ((HomotopyCategory.quotient C (.up ℤ)).map α)]
    [IsIso ((HomotopyCategory.quotient C (.up ℤ)).map β)] :
    QuasiIso (prePostcomp α β) := by
  have hα :=
    (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences α).1
      (inferInstance : IsIso ((HomotopyCategory.quotient C (.up ℤ)).map α))
  have hβ :=
    (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences β).1
      (inferInstance : IsIso ((HomotopyCategory.quotient C (.up ℤ)).map β))
  obtain ⟨eK, heK⟩ := hα
  obtain ⟨eL, heL⟩ := hβ
  simpa only [heK, heL] using
    (quasiIso_prePostcomp_of_homotopyEquiv eK eL)

end HomComplex

end

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Postcomposition by a quasi-isomorphism induces a quasi-isomorphism on the
Hom complex from a K-projective complex. This is the quasi-isomorphism-invariance
formulation of K-projectivity in Spaltenstein, *Resolutions of unbounded complexes*, §1.
The proof uses Joël Riou's homotopy- and derived-category comparisons in Mathlib. -/
lemma IsKProjective.quasiIso_prePostcomp (K : CochainComplex C ℤ)
    [K.IsKProjective] {X Y : CochainComplex C ℤ} (q : X ⟶ Y) [QuasiIso q] :
    QuasiIso (HomComplex.prePostcomp (𝟙 K) q) := by
  classical
  let := HasDerivedCategory.standard C
  rw [_root_.quasiIso_iff]
  intro n
  rw [_root_.quasiIsoAt_iff_isIso_homologyMap]
  let h := (HomotopyCategory.quotient C (.up ℤ)).map (q⟦n⟧')
  -- Only the derived image of the shifted map is inverted.
  have hderived : IsIso (DerivedCategory.Qh.map h) := by
    have heq : DerivedCategory.Qh.map h =
        (DerivedCategory.quotientCompQhIso C).hom.app (X⟦n⟧) ≫
          DerivedCategory.Q.map (q⟦n⟧') ≫
          (DerivedCategory.quotientCompQhIso C).inv.app (Y⟦n⟧) := by
      dsimp only [h]
      rw [← Category.assoc, ← DerivedCategory.quotientCompQhIso_hom_naturality]
      simp [Category.assoc]
    rw [heq]
    infer_instance
  -- The derived-Hom square uses functoriality of Qh and arbitrary targets.
  have hpost : Function.Bijective
      (fun g : (HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
          (HomotopyCategory.quotient C (.up ℤ)).obj (X⟦n⟧) => g ≫ h) := by
    let := hderived
    constructor
    · intro g₁ g₂ hg
      apply (IsKProjective.Qh_map_bijective K
        ((HomotopyCategory.quotient C (.up ℤ)).obj (X⟦n⟧))).injective
      apply (cancel_mono (DerivedCategory.Qh.map h)).1
      simpa only [Functor.map_comp] using
        congrArg (fun g => DerivedCategory.Qh.map g) hg
    · intro g
      obtain ⟨f, hf⟩ := (IsKProjective.Qh_map_bijective K
        ((HomotopyCategory.quotient C (.up ℤ)).obj (X⟦n⟧))).surjective
          (DerivedCategory.Qh.map g ≫ inv (DerivedCategory.Qh.map h))
      refine ⟨f, ?_⟩
      apply (IsKProjective.Qh_map_bijective K
        ((HomotopyCategory.quotient C (.up ℤ)).obj (Y⟦n⟧))).injective
      rw [Functor.map_comp, hf]
      simp [Category.assoc]
  let f := HomologicalComplex.homologyMap (HomComplex.prePostcomp (𝟙 K) q) n
  let eX := (HomComplex.homologyAddEquiv K X n).trans
    (HomComplex.CohomologyClass.homAddEquiv (K := K) (L := X) (n := n))
  let eY := (HomComplex.homologyAddEquiv K Y n).trans
    (HomComplex.CohomologyClass.homAddEquiv (K := K) (L := Y) (n := n))
  -- This separate square concerns the actual Hom-complex homology map.
  have hnat (x : (HomComplex K X).homology n) : eY (f x) = eX x ≫ h := by
    calc
      eY (f x) = (HomotopyCategory.quotient C (.up ℤ)).map (𝟙 K) ≫ eX x ≫ h :=
        HomComplex.homologyAddEquiv_naturality (𝟙 K) q n x
      _ = eX x ≫ h := by rw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hb : Function.Bijective (fun x => f x) := by
    constructor
    · intro x y hxy
      apply eX.injective
      apply hpost.injective
      exact (hnat x).symm.trans ((congrArg eY hxy).trans (hnat y))
    · intro y
      obtain ⟨g, hg⟩ := hpost.surjective (eY y)
      obtain ⟨x, hx⟩ := eX.surjective g
      refine ⟨x, eY.injective ?_⟩
      rw [hnat x, hx]
      exact hg
  have : IsIso ((forget AddCommGrpCat).map f) := by
    apply (CategoryTheory.isIso_iff_bijective _).2
    change Function.Bijective (fun x => f x)
    exact hb
  exact CategoryTheory.isIso_of_reflects_iso f (forget AddCommGrpCat)

/-- Precomposition by a quasi-isomorphism induces a quasi-isomorphism on the
Hom complex to a K-injective complex. This is the quasi-isomorphism-invariance
formulation of K-injectivity in Spaltenstein, *Resolutions of unbounded complexes*, §1.
The proof uses Joël Riou's homotopy- and derived-category comparisons in Mathlib. -/
lemma IsKInjective.quasiIso_prePostcomp (I : CochainComplex C ℤ)
    [I.IsKInjective] {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (HomComplex.prePostcomp f (𝟙 I)) := by
  classical
  let := HasDerivedCategory.standard C
  rw [_root_.quasiIso_iff]
  intro n
  rw [_root_.quasiIsoAt_iff_isIso_homologyMap]
  let h := (HomotopyCategory.quotient C (.up ℤ)).map f
  -- The source map is unshifted; only the fixed K-injective target is shifted.
  have hderived : IsIso (DerivedCategory.Qh.map h) := by
    have heq : DerivedCategory.Qh.map h =
        (DerivedCategory.quotientCompQhIso C).hom.app K ≫
          DerivedCategory.Q.map f ≫
          (DerivedCategory.quotientCompQhIso C).inv.app L := by
      dsimp only [h]
      rw [← Category.assoc, ← DerivedCategory.quotientCompQhIso_hom_naturality]
      simp [Category.assoc]
    rw [heq]
    infer_instance
  -- Both comparisons have arbitrary sources and the same K-injective target.
  have hpre : Function.Bijective
      (fun g : (HomotopyCategory.quotient C (.up ℤ)).obj L ⟶
          (HomotopyCategory.quotient C (.up ℤ)).obj (I⟦n⟧) => h ≫ g) := by
    let := hderived
    constructor
    · intro g₁ g₂ hg
      apply (IsKInjective.Qh_map_bijective
        ((HomotopyCategory.quotient C (.up ℤ)).obj L) (I⟦n⟧)).injective
      apply (cancel_epi (DerivedCategory.Qh.map h)).1
      simpa only [Functor.map_comp] using
        congrArg (fun g => DerivedCategory.Qh.map g) hg
    · intro g
      obtain ⟨g', hg'⟩ := (IsKInjective.Qh_map_bijective
        ((HomotopyCategory.quotient C (.up ℤ)).obj L) (I⟦n⟧)).surjective
          (inv (DerivedCategory.Qh.map h) ≫ DerivedCategory.Qh.map g)
      refine ⟨g', ?_⟩
      apply (IsKInjective.Qh_map_bijective
        ((HomotopyCategory.quotient C (.up ℤ)).obj K) (I⟦n⟧)).injective
      rw [Functor.map_comp, hg']
      simp
  let φ := HomologicalComplex.homologyMap (HomComplex.prePostcomp f (𝟙 I)) n
  let eL := (HomComplex.homologyAddEquiv L I n).trans
    (HomComplex.CohomologyClass.homAddEquiv (K := L) (L := I) (n := n))
  let eK := (HomComplex.homologyAddEquiv K I n).trans
    (HomComplex.CohomologyClass.homAddEquiv (K := K) (L := I) (n := n))
  -- The actual cohomology map agrees with precomposition under these comparisons.
  have hnat (x : (HomComplex L I).homology n) : eK (φ x) = h ≫ eL x := by
    have hshift :
        (CategoryTheory.shiftFunctor
          (HomologicalComplex C (ComplexShape.up ℤ)) n).map (𝟙 I) =
        𝟙 ((CategoryTheory.shiftFunctor
          (HomologicalComplex C (ComplexShape.up ℤ)) n).obj I) :=
      (CategoryTheory.shiftFunctor
        (HomologicalComplex C (ComplexShape.up ℤ)) n).map_id I
    have hquot :=
      (HomotopyCategory.quotient C (.up ℤ)).map_id
        ((CategoryTheory.shiftFunctor
          (HomologicalComplex C (ComplexShape.up ℤ)) n).obj I)
    have hnat := HomComplex.homologyAddEquiv_naturality f (𝟙 I) n x
    rw [hshift, hquot, Category.comp_id] at hnat
    exact hnat
  have hb : Function.Bijective (fun x => φ x) := by
    constructor
    · intro x y hxy
      apply eL.injective
      apply hpre.injective
      exact (hnat x).symm.trans ((congrArg eK hxy).trans (hnat y))
    · intro y
      obtain ⟨g, hg⟩ := hpre.surjective (eK y)
      obtain ⟨x, hx⟩ := eL.surjective g
      refine ⟨x, eK.injective ?_⟩
      rw [hnat x, hx]
      exact hg
  have : IsIso ((forget AddCommGrpCat).map φ) := by
    apply (CategoryTheory.isIso_iff_bijective _).2
    change Function.Bijective (fun x => φ x)
    exact hb
  exact CategoryTheory.isIso_of_reflects_iso φ (forget AddCommGrpCat)

/-- Joint pre- and postcomposition by quasi-isomorphisms is a quasi-isomorphism
when `K` is K-projective and `I` is K-injective. The factorization passes through
`HomComplex K I`: first precompose with `f` at the fixed target `I`, then
postcompose with `g` at the fixed source `K`. No projectivity or injectivity
conditions on `L` or `J` are needed. -/
lemma IsKProjective.quasiIso_prePostcomp_of_isKInjective
    {K L I J : CochainComplex C ℤ} [K.IsKProjective] [I.IsKInjective]
    (f : K ⟶ L) (g : I ⟶ J) [QuasiIso f] [QuasiIso g] :
    QuasiIso (HomComplex.prePostcomp f g) := by
  let : QuasiIso (HomComplex.prePostcomp f (𝟙 I)) :=
    IsKInjective.quasiIso_prePostcomp I f
  let : QuasiIso (HomComplex.prePostcomp (𝟙 K) g) :=
    IsKProjective.quasiIso_prePostcomp K g
  simpa only [← HomComplex.prePostcomp_comp, Category.id_comp, Category.comp_id] using
    (inferInstance : QuasiIso
      (HomComplex.prePostcomp f (𝟙 I) ≫ HomComplex.prePostcomp (𝟙 K) g))

/-- Joint pre- and postcomposition by quasi-isomorphisms is a quasi-isomorphism
when `L` is K-projective and `J` is K-injective. The factorization passes through
`HomComplex L J`: first postcompose with `g` at the fixed source `L`, then
precompose with `f` at the fixed target `J`. No projectivity or injectivity
conditions on `K` or `I` are needed. -/
lemma IsKInjective.quasiIso_prePostcomp_of_isKProjective
    {K L I J : CochainComplex C ℤ} [L.IsKProjective] [J.IsKInjective]
    (f : K ⟶ L) (g : I ⟶ J) [QuasiIso f] [QuasiIso g] :
    QuasiIso (HomComplex.prePostcomp f g) := by
  let : QuasiIso (HomComplex.prePostcomp (𝟙 L) g) :=
    IsKProjective.quasiIso_prePostcomp L g
  let : QuasiIso (HomComplex.prePostcomp f (𝟙 J)) :=
    IsKInjective.quasiIso_prePostcomp J f
  simpa only [← HomComplex.prePostcomp_comp, Category.id_comp, Category.comp_id] using
    (inferInstance : QuasiIso
      (HomComplex.prePostcomp (𝟙 L) g ≫ HomComplex.prePostcomp f (𝟙 J)))

end CochainComplex
