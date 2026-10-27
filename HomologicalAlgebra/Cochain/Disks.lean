/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Tactic

/-!
# Identity disks for cochain complexes

In a category with zero objects and zero morphisms, the identity disk in degrees
`n` and `n + 1` represents morphisms into degree `n` and corepresents morphisms
out of degree `n + 1`. No additive structure or completeness assumption is needed.
The disk functor is fully faithful, and is additive when the category is preadditive.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v

variable {C : Type u} [Category.{v} C]

noncomputable section

namespace CochainComplex

section

variable [HasZeroMorphisms C] [HasZeroObject C]

/-- The identity disk on `X`, supported in degrees `n` and `n + 1`. -/
def disk (n : ℤ) (X : C) : CochainComplex C ℤ where
  X i := if i = n ∨ i = n + 1 then X else 0
  d i j := if h : i = n ∧ j = n + 1 then
    CategoryTheory.eqToHom (by simp [h.1, h.2])
  else 0
  shape i j h := by
    by_cases hd : i = n ∧ j = n + 1
    · exfalso
      apply h
      rcases hd with ⟨rfl, rfl⟩
      rfl
    · simp only [dite_eq_right hd]
  d_comp_d' i j k hij hjk := by
    by_cases hd : i = n ∧ j = n + 1
    · have hd' : ¬ (j = n ∧ k = n + 1) := by
        intro hk
        omega
      simp only [dite_eq_left hd, dite_eq_right hd', CategoryTheory.Limits.comp_zero]
    · simp only [dite_eq_right hd, CategoryTheory.Limits.zero_comp]

@[simp] theorem disk_X_self (n : ℤ) (X : C) :
    (disk n X).X n = X := by simp [disk]

@[simp] theorem disk_X_succ (n : ℤ) (X : C) :
    (disk n X).X (n + 1) = X := by simp [disk]

theorem isZero_disk_X_of_ne (n i : ℤ) (X : C)
    (hi : i ≠ n) (hi' : i ≠ n + 1) : IsZero ((disk n X).X i) := by
  simpa [disk, hi, hi'] using (isZero_zero C)

theorem disk_X_of_support (n i : ℤ) (X : C)
    (hi : i = n ∨ i = n + 1) : (disk n X).X i = X := by
  exact ite_eq_left hi

theorem disk_d_of_support (n i j : ℤ) (X : C)
    (hd : i = n ∧ j = n + 1) :
    (disk n X).d i j = CategoryTheory.eqToHom
      ((disk_X_of_support n i X (Or.inl hd.1)).trans
        (disk_X_of_support n j X (Or.inr hd.2)).symm) := by
  exact dite_eq_left hd

theorem disk_d_of_not_support (n i j : ℤ) (X : C)
    (hd : ¬ (i = n ∧ j = n + 1)) : (disk n X).d i j = 0 := by
  exact dite_eq_right hd

/-- The morphism of identity disks induced by a morphism in the underlying category. -/
def diskMap {X Y : C} (n : ℤ) (f : X ⟶ Y) :
    disk n X ⟶ disk n Y where
  f i := if h : i = n ∨ i = n + 1 then
    CategoryTheory.eqToHom (disk_X_of_support n i X h) ≫ f ≫
      CategoryTheory.eqToHom (disk_X_of_support n i Y h).symm
  else 0
  comm' i j hij := by
    by_cases hd : i = n ∧ j = n + 1
    · have hi : i = n ∨ i = n + 1 := Or.inl hd.1
      have hj : j = n ∨ j = n + 1 := Or.inr hd.2
      simp only [dite_eq_left hi, dite_eq_left hj,
        disk_d_of_support n i j X hd, disk_d_of_support n i j Y hd,
        CategoryTheory.Category.assoc, CategoryTheory.eqToHom_trans_assoc,
        CategoryTheory.eqToHom_trans]
    · simp only [disk_d_of_not_support n i j X hd,
        disk_d_of_not_support n i j Y hd,
        CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]

@[simp] theorem diskMap_f_of_support {X Y : C} (n : ℤ)
    (f : X ⟶ Y) (i : ℤ) (hi : i = n ∨ i = n + 1) :
    (diskMap n f).f i =
      CategoryTheory.eqToHom (disk_X_of_support n i X hi) ≫ f ≫
        CategoryTheory.eqToHom (disk_X_of_support n i Y hi).symm := by
  exact dite_eq_left hi

@[simp] theorem diskMap_f_of_not_support {X Y : C} (n : ℤ)
    (f : X ⟶ Y) (i : ℤ) (hi : ¬ (i = n ∨ i = n + 1)) :
    (diskMap n f).f i = 0 := by
  exact dite_eq_right hi

/-- The functor assigning the identity disk in degrees `n` and `n + 1`. -/
def diskFunctor (n : ℤ) : C ⥤ CochainComplex C ℤ where
  obj X := disk n X
  map f := diskMap n f
  map_id X := by
    ext i
    by_cases hi : i = n ∨ i = n + 1
    · simp only [HomologicalComplex.id_f,
        diskMap_f_of_support n (𝟙 X) i hi,
        CategoryTheory.Category.id_comp, CategoryTheory.eqToHom_trans,
        CategoryTheory.eqToHom_refl]
    · exact (isZero_disk_X_of_ne n i X
        (fun h => hi (Or.inl h)) (fun h => hi (Or.inr h))).eq_of_src _ _
  map_comp f g := by
    ext i
    by_cases hi : i = n ∨ i = n + 1
    · simp only [HomologicalComplex.comp_f,
        diskMap_f_of_support n (f ≫ g) i hi,
        diskMap_f_of_support n f i hi, diskMap_f_of_support n g i hi,
        CategoryTheory.Category.assoc, CategoryTheory.eqToHom_trans_assoc,
        CategoryTheory.eqToHom_refl,
        CategoryTheory.Category.id_comp]
    · exact (isZero_disk_X_of_ne n i _
        (fun h => hi (Or.inl h)) (fun h => hi (Or.inr h))).eq_of_src _ _

@[simp] theorem diskFunctor_obj (n : ℤ) (X : C) :
    (diskFunctor (C := C) n).obj X = disk n X := rfl

@[simp] theorem diskFunctor_map (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    (diskFunctor n).map f = diskMap n f := rfl


instance isIso_disk_d_self_succ (n : ℤ) (X : C) :
    IsIso ((disk n X).d n (n + 1)) := by
  rw [disk_d_of_support n n (n + 1) X ⟨rfl, rfl⟩]
  infer_instance

@[ext] theorem disk_hom_ext {n : ℤ} {X : C} {K : CochainComplex C ℤ}
    {f g : disk n X ⟶ K} (h : f.f n = g.f n) : f = g := by
  ext i
  by_cases hi : i = n
  · subst i
    exact h
  · by_cases hi' : i = n + 1
    · subst i
      apply (cancel_epi ((disk n X).d n (n + 1))).1
      calc
        _ = f.f n ≫ K.d n (n + 1) := by
          exact (f.comm n (n + 1)).symm
        _ = g.f n ≫ K.d n (n + 1) := by rw [h]
        _ = _ := by
          exact g.comm n (n + 1)
    · exact (isZero_disk_X_of_ne n i X hi hi').eq_of_src _ _

@[ext] theorem hom_disk_ext {n : ℤ} {X : C} {K : CochainComplex C ℤ}
    {f g : K ⟶ disk n X} (h : f.f (n + 1) = g.f (n + 1)) : f = g := by
  ext i
  by_cases hi' : i = n + 1
  · subst i
    exact h
  · by_cases hi : i = n
    · subst i
      apply (cancel_mono ((disk n X).d n (n + 1))).1
      calc
        _ = K.d n (n + 1) ≫ f.f (n + 1) := by
          exact f.comm n (n + 1)
        _ = K.d n (n + 1) ≫ g.f (n + 1) := by rw [h]
        _ = _ := by
          exact (g.comm n (n + 1)).symm
    · exact (isZero_disk_X_of_ne n i X hi hi').eq_of_tgt _ _

/-- Extend a morphism into degree `n` to a morphism from the identity disk. -/
def diskDesc {X : C} (n : ℤ) (K : CochainComplex C ℤ)
    (a : X ⟶ K.X n) : disk n X ⟶ K where
  f i := if hi : i = n then
    CategoryTheory.eqToHom (disk_X_of_support n i X (Or.inl hi)) ≫ a ≫
      CategoryTheory.eqToHom (congrArg K.X hi.symm)
  else if hi' : i = n + 1 then
    CategoryTheory.eqToHom (disk_X_of_support n i X (Or.inr hi')) ≫ a ≫
      K.d n (n + 1) ≫ CategoryTheory.eqToHom (congrArg K.X hi'.symm)
  else 0
  comm' i j hij := by
    have hj : j = i + 1 := by
      exact hij.symm
    subst j
    by_cases hi : i = n
    · subst i
      have hs : n + 1 ≠ n := by omega
      simp only [dite_true, dite_eq_right hs,
        disk_d_of_support n n (n + 1) X ⟨rfl, rfl⟩,
        CategoryTheory.Category.assoc, CategoryTheory.eqToHom_trans_assoc,
        CategoryTheory.eqToHom_refl,
        CategoryTheory.Category.comp_id]
    · by_cases hi' : i = n + 1
      · subst i
        have hj0 : n + 1 + 1 ≠ n := by omega
        have hj1 : n + 1 + 1 ≠ n + 1 := by omega
        have hd : ¬ (n + 1 = n ∧ n + 1 + 1 = n + 1) := by omega
        simp only [dite_eq_right hi, dite_eq_right hj0, dite_eq_right hj1,
          dite_true, disk_d_of_not_support n (n + 1) (n + 1 + 1) X hd,
          CategoryTheory.Category.assoc, CategoryTheory.eqToHom_refl,
          CategoryTheory.Category.comp_id,
          K.d_comp_d, CategoryTheory.Limits.comp_zero]
      · have hd : ¬ (i = n ∧ i + 1 = n + 1) := by
          intro h
          exact hi h.1
        simp only [dite_eq_right hi, dite_eq_right hi',
          disk_d_of_not_support n i (i + 1) X hd, CategoryTheory.Limits.zero_comp]

@[simp] theorem diskDesc_f_self {X : C} (n : ℤ)
    (K : CochainComplex C ℤ) (a : X ⟶ K.X n) :
    (diskDesc n K a).f n = CategoryTheory.eqToHom (disk_X_self n X) ≫ a := by
  dsimp only [diskDesc]
  simp only [dite_true, CategoryTheory.eqToHom_refl,
    CategoryTheory.Category.comp_id]

@[simp] theorem diskDesc_f_succ {X : C} (n : ℤ)
    (K : CochainComplex C ℤ) (a : X ⟶ K.X n) :
    (diskDesc n K a).f (n + 1) =
      CategoryTheory.eqToHom (disk_X_succ n X) ≫ a ≫ K.d n (n + 1) := by
  dsimp only [diskDesc]
  have hs : n + 1 ≠ n := by omega
  simp only [dite_eq_right hs, dite_true,
    CategoryTheory.eqToHom_refl, CategoryTheory.Category.comp_id]

@[simp] theorem diskDesc_f_of_ne {X : C} (n : ℤ)
    (K : CochainComplex C ℤ) (a : X ⟶ K.X n) (i : ℤ)
    (hi : i ≠ n) (hi' : i ≠ n + 1) : (diskDesc n K a).f i = 0 := by
  dsimp only [diskDesc]
  simp only [dite_eq_right hi, dite_eq_right hi']

/-- Morphisms from the identity disk correspond to morphisms into degree `n`. -/
def diskHomEquiv (n : ℤ) (X : C) (K : CochainComplex C ℤ) :
    (disk n X ⟶ K) ≃ (X ⟶ K.X n) where
  toFun f := CategoryTheory.eqToHom (disk_X_self n X).symm ≫ f.f n
  invFun a := diskDesc n K a
  left_inv f := by
    apply disk_hom_ext
    simp only [diskDesc_f_self,
      CategoryTheory.eqToHom_trans_assoc, CategoryTheory.eqToHom_refl,
      CategoryTheory.Category.id_comp]
  right_inv a := by
    simp only [diskDesc_f_self,
      CategoryTheory.eqToHom_trans_assoc, CategoryTheory.eqToHom_refl,
      CategoryTheory.Category.id_comp]

@[simp] theorem diskHomEquiv_apply (n : ℤ) (X : C)
    (K : CochainComplex C ℤ) (f : disk n X ⟶ K) :
    diskHomEquiv n X K f = CategoryTheory.eqToHom (disk_X_self n X).symm ≫ f.f n := rfl

@[simp] theorem diskHomEquiv_symm_apply (n : ℤ) (X : C)
    (K : CochainComplex C ℤ) (a : X ⟶ K.X n) :
    (diskHomEquiv n X K).symm a = diskDesc n K a := rfl


/-- The morphism to the identity disk determined by its component in degree `n + 1`. -/
def diskLift {X : C} (n : ℤ) (K : CochainComplex C ℤ)
    (a : K.X (n + 1) ⟶ X) : K ⟶ disk n X where
  f i := if hi : i = n then
    CategoryTheory.eqToHom (congrArg K.X hi) ≫ K.d n (n + 1) ≫ a ≫
      CategoryTheory.eqToHom (disk_X_of_support n i X (Or.inl hi)).symm
  else if hi' : i = n + 1 then
    CategoryTheory.eqToHom (congrArg K.X hi') ≫ a ≫
      CategoryTheory.eqToHom (disk_X_of_support n i X (Or.inr hi')).symm
  else 0
  comm' i j hij := by
    have hj : j = i + 1 := by
      exact hij.symm
    subst j
    by_cases hi : i = n
    · subst i
      have hs : n + 1 ≠ n := by omega
      simp only [dite_eq_left rfl, dite_eq_right hs,
        disk_d_of_support n n (n + 1) X ⟨rfl, rfl⟩,
        CategoryTheory.Category.assoc,
        CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_refl,
        CategoryTheory.Category.id_comp]
    · by_cases hj0 : i + 1 = n
      · subst n
        have hi' : i ≠ i + 1 + 1 := by omega
        have hd : ¬ (i = i + 1 ∧ i + 1 = i + 1 + 1) := by omega
        simp only [dite_eq_left rfl, dite_eq_right hi, dite_eq_right hi',
          disk_d_of_not_support (i + 1) i (i + 1) X hd,
          CategoryTheory.eqToHom_refl, CategoryTheory.Category.id_comp,
          ← CategoryTheory.Category.assoc,
          K.d_comp_d, CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]
      · have hj1 : i + 1 ≠ n + 1 := by omega
        have hd : ¬ (i = n ∧ i + 1 = n + 1) := by
          intro h
          exact hi h.1
        simp only [dite_eq_right hj0, dite_eq_right hj1,
          disk_d_of_not_support n i (i + 1) X hd, CategoryTheory.Limits.comp_zero]

@[simp] theorem diskLift_f_self {X : C} (n : ℤ)
    (K : CochainComplex C ℤ) (a : K.X (n + 1) ⟶ X) :
    (diskLift n K a).f n = K.d n (n + 1) ≫ a ≫
      CategoryTheory.eqToHom (disk_X_self n X).symm := by
  dsimp only [diskLift]
  simp only [dite_eq_left rfl, CategoryTheory.eqToHom_refl,
    CategoryTheory.Category.id_comp]

@[simp] theorem diskLift_f_succ {X : C} (n : ℤ)
    (K : CochainComplex C ℤ) (a : K.X (n + 1) ⟶ X) :
    (diskLift n K a).f (n + 1) = a ≫
      CategoryTheory.eqToHom (disk_X_succ n X).symm := by
  dsimp only [diskLift]
  have hs : n + 1 ≠ n := by omega
  simp only [dite_eq_right hs, dite_eq_left rfl,
    CategoryTheory.eqToHom_refl, CategoryTheory.Category.id_comp]

@[simp] theorem diskLift_f_of_ne {X : C} (n : ℤ)
    (K : CochainComplex C ℤ) (a : K.X (n + 1) ⟶ X) (i : ℤ)
    (hi : i ≠ n) (hi' : i ≠ n + 1) : (diskLift n K a).f i = 0 := by
  dsimp only [diskLift]
  simp only [dite_eq_right hi, dite_eq_right hi']

/-- Morphisms to the identity disk correspond to morphisms out of degree `n + 1`. -/
def homDiskEquiv (n : ℤ) (K : CochainComplex C ℤ) (X : C) :
    (K ⟶ disk n X) ≃ (K.X (n + 1) ⟶ X) where
  toFun f := f.f (n + 1) ≫ CategoryTheory.eqToHom (disk_X_succ n X)
  invFun a := diskLift n K a
  left_inv f := by
    apply hom_disk_ext
    simp only [diskLift_f_succ, CategoryTheory.Category.assoc,
      CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_refl,
      CategoryTheory.Category.comp_id]
  right_inv a := by
    simp only [diskLift_f_succ, CategoryTheory.Category.assoc,
      CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_refl,
      CategoryTheory.Category.comp_id]

@[simp] theorem homDiskEquiv_apply (n : ℤ) (K : CochainComplex C ℤ)
    (X : C) (f : K ⟶ disk n X) :
    homDiskEquiv n K X f = f.f (n + 1) ≫ CategoryTheory.eqToHom (disk_X_succ n X) := rfl

@[simp] theorem homDiskEquiv_symm_apply (n : ℤ) (K : CochainComplex C ℤ)
    (X : C) (a : K.X (n + 1) ⟶ X) :
    (homDiskEquiv n K X).symm a = diskLift n K a := rfl


theorem diskMap_f_self {X Y : C} (n : ℤ) (f : X ⟶ Y) :
    (diskMap n f).f n =
      CategoryTheory.eqToHom (disk_X_self n X) ≫ f ≫
        CategoryTheory.eqToHom (disk_X_self n Y).symm := by
  exact diskMap_f_of_support n f n (Or.inl rfl)

instance diskFunctor_full (n : ℤ) : (diskFunctor (C := C) n).Full where
  map_surjective {X Y} f := by
    dsimp only [diskFunctor_obj, diskFunctor_map] at f ⊢
    refine ⟨CategoryTheory.eqToHom (disk_X_self n X).symm ≫ f.f n ≫
      CategoryTheory.eqToHom (disk_X_self n Y), ?_⟩
    apply disk_hom_ext
    simp only [diskMap_f_self, CategoryTheory.Category.assoc,
      CategoryTheory.eqToHom_trans_assoc, CategoryTheory.eqToHom_trans,
      CategoryTheory.eqToHom_refl, CategoryTheory.Category.id_comp,
      CategoryTheory.Category.comp_id]

instance diskFunctor_faithful (n : ℤ) : (diskFunctor (C := C) n).Faithful where
  map_injective := by
    intro X Y f g h
    have hn := congrArg (fun k : disk n X ⟶ disk n Y => k.f n) h
    change (diskMap n f).f n = (diskMap n g).f n at hn
    rw [diskMap_f_self, diskMap_f_self] at hn
    apply (cancel_mono (CategoryTheory.eqToHom (disk_X_self n Y).symm)).1
    apply (cancel_epi (CategoryTheory.eqToHom (disk_X_self n X))).1
    exact hn

end

section

variable [Preadditive C] [HasZeroObject C]

instance diskFunctor_additive (n : ℤ) :
    (diskFunctor (C := C) n).Additive where
  map_add := by
    intro X Y f g
    apply disk_hom_ext
    change (diskMap n (f + g)).f n =
      (diskMap n f).f n + (diskMap n g).f n
    simp only [diskMap_f_self,
      Preadditive.comp_add, Preadditive.add_comp]

end

end CochainComplex
