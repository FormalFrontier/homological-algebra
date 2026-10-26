/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import HomologicalAlgebra.Cochain.HomComplexFunctoriality

/-!
# Cohomology of Hom complexes under shifts

For integer cochain complexes over a preadditive category, shifting the target
translates Hom-complex cohomology from degree `n` to degree `n + s`, and shifting
the source translates it to degree `n - s`. The comparisons are characterized
by the canonical shift coherences in the homotopy category and are natural in
both complexes. Vanishing in one fixed degree for all shifts detects vanishing
in every degree.

The Hom complex takes values in abelian groups; no ambient kernels, cokernels,
zero object, boundedness, K-projectivity or K-injectivity are required.

## References

The constructions reuse Mathlib's Hom-complex cohomology comparison with
morphisms in the homotopy category, due to Joël Riou (2025, Apache-2.0).
-/

@[expose] public section

open CategoryTheory Category Limits

universe v u

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

local notation "D" => HomotopyCategory C (ComplexShape.up ℤ)
local notation "Q" => HomotopyCategory.quotient C (ComplexShape.up ℤ)
local notation "S" => CategoryTheory.shiftFunctor (CochainComplex C ℤ)

private noncomputable def homologyHomAddEquiv
    (K L : CochainComplex C ℤ) (n : ℤ) :
    (HomComplex K L).homology n ≃+ ((Q).obj K ⟶ (Q).obj (L⟦n⟧)) :=
  (homologyAddEquiv K L n).trans
    (CohomologyClass.homAddEquiv (K := K) (L := L) (n := n))

private noncomputable def shiftRightAddIso (n s : ℤ) :
    (S s ⋙
      S n) ≅
      S (n + s) :=
  (CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) s n).symm ≪≫
    eqToIso (congrArg (fun j : ℤ => S j)
      (add_comm s n))

private noncomputable def shiftLeftSourceIso (s : ℤ) :
    (S s ⋙ Q ⋙ CategoryTheory.shiftFunctor D (-s)) ≅ Q :=
  Functor.isoWhiskerLeft (S s)
      ((Q).commShiftIso (-s)).symm ≪≫
    Functor.isoWhiskerRight
      ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) s (-s)).symm ≪≫
        eqToIso (congrArg (fun j : ℤ => S j)
          (add_neg_cancel s)) ≪≫ CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ) Q

private noncomputable def shiftLeftTargetIso (n s : ℤ) :
    (S n ⋙ Q ⋙ CategoryTheory.shiftFunctor D (-s)) ≅
      (S (n - s) ⋙ Q) :=
  Functor.isoWhiskerLeft (S n)
      ((Q).commShiftIso (-s)).symm ≪≫
    Functor.isoWhiskerRight
      ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) n (-s)).symm ≪≫
        eqToIso (congrArg (fun j : ℤ => S j)
          (sub_eq_add_neg n s).symm)) Q

/-- Shifting the target by `s` increases the Hom-complex cohomology index
from `n` to `n + s`. The transport uses the canonical shift constraint under
the comparison with morphisms in the homotopy category. -/
noncomputable def homologyShiftRightAddEquiv
    (P A : CochainComplex C ℤ) (n s : ℤ) :
    (HomComplex P (A⟦s⟧)).homology n ≃+
      (HomComplex P A).homology (n + s) := by
  let i := (Q).mapIso
    (((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) s n).symm ≪≫
      eqToIso (congrArg (fun j : ℤ => S j) (add_comm s n))).app A)
  let post : ((Q).obj P ⟶ (Q).obj ((A⟦s⟧)⟦n⟧)) ≃+
      ((Q).obj P ⟶ (Q).obj (A⟦n + s⟧)) :=
    { toFun := fun f => f ≫ i.hom
      invFun := fun f => f ≫ i.inv
      left_inv := by intro f; simp [Category.assoc]
      right_inv := by intro f; simp [Category.assoc]
      map_add' := by intro f g; simp only [Preadditive.add_comp] }
  exact ((homologyAddEquiv P (A⟦s⟧) n).trans
    (CohomologyClass.homAddEquiv (K := P) (L := A⟦s⟧) (n := n))).trans
      (post.trans ((homologyAddEquiv P A (n + s)).trans
        (CohomologyClass.homAddEquiv (K := P) (L := A) (n := n + s))).symm)

/-- Shifting the source by `s` decreases the Hom-complex cohomology index
from `n` to `n - s`. The transport shifts both homotopy-category objects by
`-s` and uses the canonical quotient/shift and shift-action coherences. -/
noncomputable def homologyShiftLeftAddEquiv
    (A I : CochainComplex C ℤ) (n s : ℤ) :
    (HomComplex (A⟦s⟧) I).homology n ≃+
      (HomComplex A I).homology (n - s) := by
  let F := CategoryTheory.shiftFunctor D (-s)
  let α := (Functor.isoWhiskerLeft (S s) ((Q).commShiftIso (-s)).symm ≪≫
    Functor.isoWhiskerRight
      ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) s (-s)).symm ≪≫
        eqToIso (congrArg (fun j : ℤ => S j) (add_neg_cancel s)) ≪≫
          CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ) Q).app A
  let β := (Functor.isoWhiskerLeft (S n) ((Q).commShiftIso (-s)).symm ≪≫
    Functor.isoWhiskerRight
      ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) n (-s)).symm ≪≫
        eqToIso (congrArg (fun j : ℤ => S j) (sub_eq_add_neg n s).symm)) Q).app I
  let transport : ((Q).obj (A⟦s⟧) ⟶ (Q).obj (I⟦n⟧)) ≃+
      ((Q).obj A ⟶ (Q).obj (I⟦n - s⟧)) :=
    { toFun := fun f => α.inv ≫ F.map f ≫ β.hom
      invFun := fun g => F.preimage (α.hom ≫ g ≫ β.inv)
      left_inv := by
        intro f
        apply F.map_injective
        simp [Category.assoc]
      right_inv := by intro g; simp [Category.assoc]
      map_add' := by
        intro f g
        simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp] }
  exact ((homologyAddEquiv (A⟦s⟧) I n).trans
    (CohomologyClass.homAddEquiv (K := A⟦s⟧) (L := I) (n := n))).trans
      (transport.trans ((homologyAddEquiv A I (n - s)).trans
        (CohomologyClass.homAddEquiv (K := A) (L := I) (n := n - s))).symm)

/-- Under the additive homotopy-category comparison, right shift transport
is postcomposition by the quotient image of the canonical shift constraint. -/
lemma homologyShiftRightAddEquiv_homAddEquiv
    (P A : CochainComplex C ℤ) (n s : ℤ)
    (x : (HomComplex P (A⟦s⟧)).homology n) :
    ((homologyAddEquiv P A (n + s)).trans
      (CohomologyClass.homAddEquiv (K := P) (L := A) (n := n + s)))
      (homologyShiftRightAddEquiv P A n s x) =
    ((homologyAddEquiv P (A⟦s⟧) n).trans
      (CohomologyClass.homAddEquiv (K := P) (L := A⟦s⟧) (n := n))) x ≫
      ((Q).mapIso (((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) s n).symm ≪≫
        eqToIso (congrArg (fun j : ℤ => S j)
          (add_comm s n))).app A)).hom := by
  change (homologyHomAddEquiv P A (n + s))
    ((homologyHomAddEquiv P A (n + s)).symm _) = _
  exact (homologyHomAddEquiv P A (n + s)).apply_symm_apply _

/-- Under the additive homotopy-category comparison, left shift transport is
shift by `-s` on morphisms, conjugated by the canonical coherence composites. -/
lemma homologyShiftLeftAddEquiv_homAddEquiv
    (A I : CochainComplex C ℤ) (n s : ℤ)
    (x : (HomComplex (A⟦s⟧) I).homology n) :
    let α := (Functor.isoWhiskerLeft (S s)
        ((Q).commShiftIso (-s)).symm ≪≫
      Functor.isoWhiskerRight
        ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) s (-s)).symm ≪≫
          eqToIso (congrArg (fun j : ℤ => S j)
            (add_neg_cancel s)) ≪≫
          CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ) Q).app A
    let β := (Functor.isoWhiskerLeft (S n)
        ((Q).commShiftIso (-s)).symm ≪≫
      Functor.isoWhiskerRight
        ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) n (-s)).symm ≪≫
          eqToIso (congrArg (fun j : ℤ => S j)
            (sub_eq_add_neg n s).symm)) Q).app I
    ((homologyAddEquiv A I (n - s)).trans
      (CohomologyClass.homAddEquiv (K := A) (L := I) (n := n - s)))
      (homologyShiftLeftAddEquiv A I n s x) =
      α.inv ≫ (CategoryTheory.shiftFunctor D (-s)).map
        (((homologyAddEquiv (A⟦s⟧) I n).trans
          (CohomologyClass.homAddEquiv (K := A⟦s⟧) (L := I) (n := n))) x) ≫
        β.hom := by
  change (homologyHomAddEquiv A I (n - s))
    ((homologyHomAddEquiv A I (n - s)).symm _) = _
  exact (homologyHomAddEquiv A I (n - s)).apply_symm_apply _

/-- Right shift transport is contravariantly natural in the source and
covariantly natural in the target. -/
lemma homologyShiftRightAddEquiv_naturality
    {P P' A A' : CochainComplex C ℤ} (f : P' ⟶ P) (g : A ⟶ A')
    (n s : ℤ) (x : (HomComplex P (A⟦s⟧)).homology n) :
    homologyShiftRightAddEquiv P' A' n s
        (HomologicalComplex.homologyMap (prePostcomp f (g⟦s⟧')) n x) =
      HomologicalComplex.homologyMap (prePostcomp f g) (n + s)
        (homologyShiftRightAddEquiv P A n s x) := by
  let E := homologyHomAddEquiv (C := C)
  let a (L : CochainComplex C ℤ) :=
    ((Q).mapIso ((shiftRightAddIso (C := C) n s).app L)).hom
  have hR (K L : CochainComplex C ℤ)
      (y : (HomComplex K (L⟦s⟧)).homology n) :
      E K L (n + s) (homologyShiftRightAddEquiv K L n s y) =
        E K (L⟦s⟧) n y ≫ a L :=
    homologyShiftRightAddEquiv_homAddEquiv K L n s y
  have ha : (Q).map ((g⟦s⟧')⟦n⟧') ≫ a A' = a A ≫ (Q).map (g⟦n + s⟧') := by
    change (Q).map ((g⟦s⟧')⟦n⟧') ≫
        (Q).map (((shiftRightAddIso (C := C) n s).app A').hom) =
      (Q).map (((shiftRightAddIso (C := C) n s).app A).hom) ≫ (Q).map (g⟦n + s⟧')
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun k => (Q).map k)
      ((shiftRightAddIso (C := C) n s).hom.naturality g)
  apply (E P' A' (n + s)).injective
  calc
    _ = E P' (A'⟦s⟧) n
        (HomologicalComplex.homologyMap (prePostcomp f (g⟦s⟧')) n x) ≫ a A' :=
      hR P' A' _
    _ = ((Q).map f ≫ E P (A⟦s⟧) n x ≫ (Q).map ((g⟦s⟧')⟦n⟧')) ≫ a A' := by
      exact congrArg (fun k => k ≫ a A')
        (homologyAddEquiv_naturality f (g⟦s⟧') n x)
    _ = (Q).map f ≫ (E P (A⟦s⟧) n x ≫ a A) ≫ (Q).map (g⟦n + s⟧') := by
      simp only [Category.assoc]
      rw [ha]
    _ = (Q).map f ≫ E P A (n + s) (homologyShiftRightAddEquiv P A n s x) ≫
        (Q).map (g⟦n + s⟧') := by rw [hR P A x]
    _ = _ := (homologyAddEquiv_naturality f g (n + s)
      (homologyShiftRightAddEquiv P A n s x)).symm

/-- Left shift transport is contravariantly natural in the source and
covariantly natural in the target. -/
lemma homologyShiftLeftAddEquiv_naturality
    {A' A I I' : CochainComplex C ℤ} (a : A' ⟶ A) (b : I ⟶ I')
    (n s : ℤ) (x : (HomComplex (A⟦s⟧) I).homology n) :
    homologyShiftLeftAddEquiv A' I' n s
        (HomologicalComplex.homologyMap (prePostcomp (a⟦s⟧') b) n x) =
      HomologicalComplex.homologyMap (prePostcomp a b) (n - s)
        (homologyShiftLeftAddEquiv A I n s x) := by
  let E := homologyHomAddEquiv (C := C)
  let F := CategoryTheory.shiftFunctor D (-s)
  let α (K : CochainComplex C ℤ) := (shiftLeftSourceIso (C := C) s).app K
  let β (L : CochainComplex C ℤ) := (shiftLeftTargetIso (C := C) n s).app L
  have hL (K L : CochainComplex C ℤ)
      (y : (HomComplex (K⟦s⟧) L).homology n) :
      E K L (n - s) (homologyShiftLeftAddEquiv K L n s y) =
        (α K).inv ≫ F.map (E (K⟦s⟧) L n y) ≫ (β L).hom :=
    homologyShiftLeftAddEquiv_homAddEquiv K L n s y
  have hα : (α A').inv ≫ F.map ((Q).map (a⟦s⟧')) = (Q).map a ≫ (α A).inv :=
    ((shiftLeftSourceIso (C := C) s).inv.naturality a).symm
  have hβ : F.map ((Q).map (b⟦n⟧')) ≫ (β I').hom =
      (β I).hom ≫ (Q).map (b⟦n - s⟧') :=
    (shiftLeftTargetIso (C := C) n s).hom.naturality b
  have ht (f : (Q).obj (A⟦s⟧) ⟶ (Q).obj (I⟦n⟧)) :
      (α A').inv ≫ F.map ((Q).map (a⟦s⟧') ≫ f ≫ (Q).map (b⟦n⟧')) ≫ (β I').hom =
        (Q).map a ≫ ((α A).inv ≫ F.map f ≫ (β I).hom) ≫ (Q).map (b⟦n - s⟧') := by
    simp only [Functor.map_comp]
    calc
      _ = ((α A').inv ≫ F.map ((Q).map (a⟦s⟧'))) ≫ F.map f ≫
          (F.map ((Q).map (b⟦n⟧')) ≫ (β I').hom) := by simp only [Category.assoc]
      _ = ((Q).map a ≫ (α A).inv) ≫ F.map f ≫
          ((β I).hom ≫ (Q).map (b⟦n - s⟧')) := by rw [hα, hβ]
      _ = _ := by simp only [Category.assoc]
  apply (E A' I' (n - s)).injective
  calc
    _ = (α A').inv ≫ F.map
        (E (A'⟦s⟧) I' n
          (HomologicalComplex.homologyMap (prePostcomp (a⟦s⟧') b) n x)) ≫
          (β I').hom := hL A' I' _
    _ = (α A').inv ≫ F.map
        ((Q).map (a⟦s⟧') ≫ E (A⟦s⟧) I n x ≫ (Q).map (b⟦n⟧')) ≫ (β I').hom := by
      exact congrArg (fun k => (α A').inv ≫ F.map k ≫ (β I').hom)
        (homologyAddEquiv_naturality (a⟦s⟧') b n x)
    _ = (Q).map a ≫ ((α A).inv ≫ F.map (E (A⟦s⟧) I n x) ≫ (β I).hom) ≫
        (Q).map (b⟦n - s⟧') := ht _
    _ = (Q).map a ≫ E A I (n - s) (homologyShiftLeftAddEquiv A I n s x) ≫
        (Q).map (b⟦n - s⟧') := by rw [hL A I x]
    _ = _ := (homologyAddEquiv_naturality a b (n - s)
      (homologyShiftLeftAddEquiv A I n s x)).symm

/-- Vanishing in one fixed degree for every target shift implies vanishing
in every degree of the unshifted Hom complex. -/
lemma isZero_homology_of_forall_shift_right
    (P A : CochainComplex C ℤ) (n : ℤ)
    (h : ∀ s : ℤ, IsZero ((HomComplex P (A⟦s⟧)).homology n)) (m : ℤ) :
    IsZero ((HomComplex P A).homology m) := by
  have hdegree : n + (m - n) = m := by rw [add_comm, sub_add_cancel]
  let H := (HomComplex P (A⟦m - n⟧)).homology n
  let e : H ≃+ (HomComplex P A).homology m := by
    exact hdegree ▸ homologyShiftRightAddEquiv P A n (m - n)
  have hzero : 𝟙 H = 0 := (IsZero.iff_id_eq_zero H).mp (h (m - n))
  rw [IsZero.iff_id_eq_zero]
  ext x
  change x = 0
  apply e.symm.injective
  rw [map_zero]
  have hx := congrArg (fun f : H ⟶ H => f (e.symm x)) hzero
  change e.symm x = 0 at hx
  exact hx

/-- Vanishing in one fixed degree for every source shift implies vanishing
in every degree of the unshifted Hom complex. -/
lemma isZero_homology_of_forall_shift_left
    (A I : CochainComplex C ℤ) (n : ℤ)
    (h : ∀ s : ℤ, IsZero ((HomComplex (A⟦s⟧) I).homology n)) (m : ℤ) :
    IsZero ((HomComplex A I).homology m) := by
  have hdegree : n - (n - m) = m := by
    simp [sub_eq_add_neg]
  let H := (HomComplex (A⟦n - m⟧) I).homology n
  let e : H ≃+ (HomComplex A I).homology m := by
    exact hdegree ▸ homologyShiftLeftAddEquiv A I n (n - m)
  have hzero : 𝟙 H = 0 := (IsZero.iff_id_eq_zero H).mp (h (n - m))
  rw [IsZero.iff_id_eq_zero]
  ext x
  change x = 0
  apply e.symm.injective
  rw [map_zero]
  have hx := congrArg (fun f : H ⟶ H => f (e.symm x)) hzero
  change e.symm x = 0 at hx
  exact hx

end CochainComplex.HomComplex
