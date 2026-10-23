/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.Types.Basic

public import HomologicalAlgebra.Cochain.HomComplexFunctoriality
public import HomologicalAlgebra.Cochain.KProjective

/-!
# Quasi-isomorphism invariance of Hom complexes

Postcomposition by a quasi-isomorphism induces a quasi-isomorphism on the
complex of morphisms from a K-projective complex. The other complexes are
arbitrary. The Hom complex takes values in abelian groups, so no products
in the coefficient category are required.

The K-projectivity formulation follows Spaltenstein. The Hom-complex model
and its additive comparisons with morphisms in the homotopy category are
Mathlib constructions due to Joël Riou.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, §1.
-/

@[expose] public section

open CategoryTheory Category

universe v u

namespace CochainComplex

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

end CochainComplex
