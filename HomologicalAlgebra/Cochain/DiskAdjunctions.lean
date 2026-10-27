/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import HomologicalAlgebra.Cochain.Disks
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Disk adjunctions for evaluation of cochain complexes

The identity disk is left adjoint to evaluation at its lower degree and right
adjoint to evaluation at its upper degree. In particular, evaluation in every
integer degree is both a left and a right adjoint, without additive hypotheses.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w w'

variable {C : Type u} [Category.{v} C]
  [HasZeroMorphisms C] [HasZeroObject C]

noncomputable section

namespace CochainComplex

theorem diskHomEquiv_naturality_left (n : ℤ) {X Y : C}
    (f : X ⟶ Y) (K : CochainComplex C ℤ) (g : disk n Y ⟶ K) :
    diskHomEquiv n X K ((diskFunctor n).map f ≫ g) =
      f ≫ diskHomEquiv n Y K g := by
  change eqToHom (disk_X_self n X).symm ≫
      ((diskMap n f).f n ≫ g.f n) =
    f ≫ eqToHom (disk_X_self n Y).symm ≫ g.f n
  simp only [diskMap_f_of_support n f n (Or.inl rfl), Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

theorem diskHomEquiv_naturality_right (n : ℤ) (X : C)
    {K L : CochainComplex C ℤ} (f : disk n X ⟶ K) (g : K ⟶ L) :
    diskHomEquiv n X L (f ≫ g) = diskHomEquiv n X K f ≫ g.f n := by
  simp only [diskHomEquiv_apply, HomologicalComplex.comp_f, Category.assoc]

theorem homDiskEquiv_naturality_left (n : ℤ)
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (X : C) (g : L ⟶ disk n X) :
    homDiskEquiv n K X (f ≫ g) = f.f (n + 1) ≫ homDiskEquiv n L X g := by
  simp only [homDiskEquiv_apply, HomologicalComplex.comp_f, Category.assoc]

theorem homDiskEquiv_naturality_right (n : ℤ) (K : CochainComplex C ℤ)
    {X Y : C} (f : K ⟶ disk n X) (g : X ⟶ Y) :
    homDiskEquiv n K Y (f ≫ (diskFunctor n).map g) =
      homDiskEquiv n K X f ≫ g := by
  simp only [homDiskEquiv_apply, HomologicalComplex.comp_f, diskFunctor_map,
    diskMap_f_of_support n g (n + 1) (Or.inr rfl), Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- The identity disk is left adjoint to evaluation at its lower degree. -/
def diskAdjunction (n : ℤ) :
    diskFunctor (C := C) n ⊣ HomologicalComplex.eval C (ComplexShape.up ℤ) n :=
  Adjunction.mkOfHomEquiv {
    homEquiv := diskHomEquiv n
    homEquiv_naturality_left_symm := by
      intro X Y K f g
      change (diskHomEquiv n X K).symm (f ≫ g) =
        (diskFunctor n).map f ≫ (diskHomEquiv n Y K).symm g
      apply (diskHomEquiv n X K).injective
      calc
        _ = f ≫ g := (diskHomEquiv n X K).apply_symm_apply _
        _ = _ := ((diskHomEquiv_naturality_left n f K _).trans
          (congrArg (fun a => f ≫ a) ((diskHomEquiv n Y K).apply_symm_apply g))).symm
    homEquiv_naturality_right := by
      intro X K L f g
      exact diskHomEquiv_naturality_right n X f g }

/-- Evaluation at the upper degree is left adjoint to the identity disk. -/
def evalDiskAdjunction (n : ℤ) :
    HomologicalComplex.eval C (ComplexShape.up ℤ) (n + 1) ⊣ diskFunctor (C := C) n :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun K X => (homDiskEquiv n K X).symm
    homEquiv_naturality_left_symm := by
      intro K L X f g
      exact homDiskEquiv_naturality_left n f X g
    homEquiv_naturality_right := by
      intro K X Y f g
      change (homDiskEquiv n K Y).symm (f ≫ g) =
        (homDiskEquiv n K X).symm f ≫ (diskFunctor n).map g
      apply (homDiskEquiv n K Y).injective
      calc
        _ = f ≫ g := (homDiskEquiv n K Y).apply_symm_apply _
        _ = _ := ((homDiskEquiv_naturality_right n K _ g).trans
          (congrArg (fun a => a ≫ g) ((homDiskEquiv n K X).apply_symm_apply f))).symm }

-- Simplification passes through these equivalences to the existing disk component API.
/-- The disk adjunction uses the existing degree-`n` Hom-equivalence. -/
@[simp] theorem diskAdjunction_homEquiv (n : ℤ) (X : C) (K : CochainComplex C ℤ) :
    (diskAdjunction n).homEquiv X K = diskHomEquiv n X K := by
  rw [diskAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

/-- The upper-degree adjunction uses the inverse of the existing disk Hom-equivalence. -/
@[simp] theorem evalDiskAdjunction_homEquiv (n : ℤ) (K : CochainComplex C ℤ) (X : C) :
    (evalDiskAdjunction n).homEquiv K X = (homDiskEquiv n K X).symm := by
  rw [evalDiskAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

theorem diskAdjunction_homEquiv_apply (n : ℤ) (X : C)
    (K : CochainComplex C ℤ) (f : disk n X ⟶ K) :
    (diskAdjunction n).homEquiv X K f = eqToHom (disk_X_self n X).symm ≫ f.f n := by
  rw [diskAdjunction_homEquiv]
  exact diskHomEquiv_apply n X K f

theorem diskAdjunction_homEquiv_symm_apply (n : ℤ) (X : C)
    (K : CochainComplex C ℤ) (a : X ⟶ K.X n) :
    ((diskAdjunction n).homEquiv X K).symm a = diskDesc n K a := by
  rw [diskAdjunction_homEquiv]
  exact diskHomEquiv_symm_apply n X K a

theorem evalDiskAdjunction_homEquiv_apply (n : ℤ)
    (K : CochainComplex C ℤ) (X : C) (a : K.X (n + 1) ⟶ X) :
    (evalDiskAdjunction n).homEquiv K X a = diskLift n K a := by
  rw [evalDiskAdjunction_homEquiv]
  exact homDiskEquiv_symm_apply n K X a

theorem evalDiskAdjunction_homEquiv_symm_apply (n : ℤ)
    (K : CochainComplex C ℤ) (X : C) (f : K ⟶ disk n X) :
    ((evalDiskAdjunction n).homEquiv K X).symm f =
      f.f (n + 1) ≫ eqToHom (disk_X_succ n X) := by
  rw [evalDiskAdjunction_homEquiv]
  exact homDiskEquiv_apply n K X f

instance eval_isRightAdjoint (m : ℤ) :
    (HomologicalComplex.eval C (ComplexShape.up ℤ) m).IsRightAdjoint :=
  (diskAdjunction m).isRightAdjoint

instance eval_isLeftAdjoint (m : ℤ) :
    (HomologicalComplex.eval C (ComplexShape.up ℤ) m).IsLeftAdjoint := by
  simpa only [sub_add_cancel] using (evalDiskAdjunction (C := C) (m - 1)).isLeftAdjoint

-- The native adjoint-preservation API discharges preservation of each shape.
example (m : ℤ) {J : Type w} [Category.{w'} J] :
    PreservesLimitsOfShape J (HomologicalComplex.eval C (ComplexShape.up ℤ) m) := by
  let : PreservesLimitsOfSize.{w', w}
      (HomologicalComplex.eval C (ComplexShape.up ℤ) m) :=
    (diskAdjunction m).rightAdjoint_preservesLimits
  infer_instance

example (m : ℤ) {J : Type w} [Category.{w'} J] :
    PreservesColimitsOfShape J (HomologicalComplex.eval C (ComplexShape.up ℤ) m) := by
  let : PreservesColimitsOfSize.{w', w}
      (HomologicalComplex.eval C (ComplexShape.up ℤ) m) := by
    simpa only [sub_add_cancel] using
      ((evalDiskAdjunction (C := C) (m - 1)).leftAdjoint_preservesColimits :
        PreservesColimitsOfSize.{w', w}
          (HomologicalComplex.eval C (ComplexShape.up ℤ) (m - 1 + 1)))
  infer_instance

end CochainComplex
