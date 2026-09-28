/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Homology.HomotopyFiber
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.HomotopyFiber

/-!
# Relative paths of integer cochain maps

The pullback of a fixed cochain map along the first endpoint of the native path
object has a section and a contraction relative to its first projection.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits Preadditive

namespace HomologicalComplex.cylinder

variable {C : Type*} [Category* C] [Preadditive C]
variable {α : Type*} {c : ComplexShape α} [DecidableRel c.Rel]
variable (K : HomologicalComplex C c) [HasBinaryBiproducts C]

theorem ι₀_comp_πCompι₀Homotopy_hom (hc : ∀ j, ∃ i, c.Rel i j) (i j : α) :
    (ι₀ K).f j ≫ (πCompι₀Homotopy K hc).hom j i = 0 := by
  classical
  by_cases hij : c.Rel i j
  · have hgen : (ι₀ K).f j ≫
        (homotopyCofiber.sndX (biprod.lift (𝟙 K) (-𝟙 K)) j ≫
          (biprod.snd : K ⊞ K ⟶ K).f j ≫ inlX K j i hij) = 0 := by
      simp [ι₀, Category.assoc]
    simpa [πCompι₀Homotopy, πCompι₀Homotopy.nullHomotopy,
      Homotopy.equivSubZero, Homotopy.trans, Homotopy.ofEq,
      Homotopy.nullHomotopy', Homotopy.nullHomotopy, hij] using hgen
  · simp [(πCompι₀Homotopy K hc).zero j i hij]

end HomologicalComplex.cylinder

namespace CochainComplex.RelativePath

attribute [local instance] ComplexShape.decidableRelSymm


variable {C : Type*} [Category* C] [Preadditive C]
variable [HasBinaryBiproducts C]

theorem hcℤ (j : ℤ) : ∃ i, (ComplexShape.up ℤ).Rel j i :=
  ⟨j + 1, ComplexShape.up_mk _ _ rfl⟩

theorem path_hom_π₀ (B : CochainComplex C ℤ) (i j : ℤ) :
    (HomologicalComplex.pathObject.π₀CompιHomotopy B hcℤ).hom i j ≫
      (HomologicalComplex.pathObject.π₀ B).f j = 0 := by
  have h := HomologicalComplex.cylinder.ι₀_comp_πCompι₀Homotopy_hom
    B.op hcℤ i j
  unfold HomologicalComplex.pathObject.π₀CompιHomotopy
    HomologicalComplex.pathObject.π₀
  dsimp only [Homotopy.unop, HomologicalComplex.unopFunctor]
  simp only [Quiver.Hom.unop_op]
  change ((HomologicalComplex.cylinder.πCompι₀Homotopy B.op hcℤ).hom j i).unop ≫
    ((HomologicalComplex.cylinder.ι₀ B.op).f j).unop = 0
  rw [← unop_comp, h, unop_zero]

variable [HasPullbacks C]
variable {B₁ B A : CochainComplex C ℤ}

/-- The ordinary pullback of a fixed arrow along the native path's first endpoint. -/
def obj (f : B₁ ⟶ B) : CochainComplex C ℤ :=
  pullback f (HomologicalComplex.pathObject.π₀ B)

/-- The strict projection back to the domain of the fixed arrow. -/
def fst (f : B₁ ⟶ B) : obj f ⟶ B₁ :=
  pullback.fst f (HomologicalComplex.pathObject.π₀ B)

/-- The strict projection to the native path. -/
def snd (f : B₁ ⟶ B) : obj f ⟶ B.pathObject :=
  pullback.snd f (HomologicalComplex.pathObject.π₀ B)

/-- The target endpoint of a relative path. -/
def toTarget (f : B₁ ⟶ B) : obj f ⟶ B :=
  snd f ≫ HomologicalComplex.pathObject.π₁ B

/-- The diagonal relative path on the fixed arrow. -/
def sectionMap (f : B₁ ⟶ B) : B₁ ⟶ obj f :=
  pullback.lift (𝟙 B₁) (f ≫ HomologicalComplex.pathObject.ι B) (by simp)

@[simp] theorem section_fst (f : B₁ ⟶ B) : sectionMap f ≫ fst f = 𝟙 B₁ :=
  pullback.lift_fst _ _ _

@[simp] theorem section_snd (f : B₁ ⟶ B) :
    sectionMap f ≫ snd f = f ≫ HomologicalComplex.pathObject.ι B :=
  pullback.lift_snd _ _ _

@[simp] theorem section_toTarget (f : B₁ ⟶ B) : sectionMap f ≫ toTarget f = f := by
  unfold sectionMap toTarget snd obj
  rw [← Category.assoc, pullback.lift_snd, Category.assoc,
    HomologicalComplex.pathObject.π₁_ι, Category.comp_id]

theorem fst_comp (f : B₁ ⟶ B) :
    fst f ≫ f = snd f ≫ HomologicalComplex.pathObject.π₀ B :=
  pullback.condition

/-- A chosen homotopy gives a strict lift into the *same* fixed-arrow object. -/
def lift (f : B₁ ⟶ B) (u : A ⟶ B₁) (v : A ⟶ B)
    (h : Homotopy (u ≫ f) v) : A ⟶ obj f :=
  pullback.lift u (HomologicalComplex.pathObject.lift (u ≫ f) v h) (by simp)

@[simp] theorem lift_fst (f : B₁ ⟶ B) (u : A ⟶ B₁) (v : A ⟶ B)
    (h : Homotopy (u ≫ f) v) : lift f u v h ≫ fst f = u :=
  pullback.lift_fst _ _ _

@[simp] theorem lift_toTarget (f : B₁ ⟶ B) (u : A ⟶ B₁) (v : A ⟶ B)
    (h : Homotopy (u ≫ f) v) : lift f u v h ≫ toTarget f = v := by
  unfold lift toTarget snd obj
  rw [← Category.assoc, pullback.lift_snd, HomologicalComplex.pathObject.lift_π₁]

theorem isPullbackAt (f : B₁ ⟶ B) (j : ℤ) :
    IsPullback ((fst f).f j) ((snd f).f j) (f.f j)
      ((HomologicalComplex.pathObject.π₀ B).f j) := by
  exact (IsPullback.of_hasPullback f (HomologicalComplex.pathObject.π₀ B)).map
    (HomologicalComplex.eval C (ComplexShape.up ℤ) j)

def component (f : B₁ ⟶ B) (i j : ℤ) : (obj f).X i ⟶ (obj f).X j :=
  (isPullbackAt f j).lift 0
    ((snd f).f i ≫ (HomologicalComplex.pathObject.π₀CompιHomotopy B hcℤ).hom i j)
    (by simp only [zero_comp, Category.assoc, path_hom_π₀, comp_zero])

private theorem component_fst (f : B₁ ⟶ B) (i j : ℤ) :
    component f i j ≫ (fst f).f j = 0 :=
  (isPullbackAt f j).lift_fst _ _ _

private theorem component_snd (f : B₁ ⟶ B) (i j : ℤ) :
    component f i j ≫ (snd f).f j =
      (snd f).f i ≫ (HomologicalComplex.pathObject.π₀CompιHomotopy B hcℤ).hom i j :=
  (isPullbackAt f j).lift_snd _ _ _

theorem component_zero (f : B₁ ⟶ B) (i j : ℤ)
    (hij : ¬ (ComplexShape.up ℤ).Rel j i) : component f i j = 0 := by
  apply (isPullbackAt f j).hom_ext
  · simp only [component_fst, zero_comp]
  · simp only [component_snd, zero_comp,
      (HomologicalComplex.pathObject.π₀CompιHomotopy B hcℤ).zero i j hij, comp_zero]

private theorem dNext_component_fst (f : B₁ ⟶ B) (i : ℤ) :
    dNext i (component f) ≫ (fst f).f i = 0 := by
  rw [← dNext_comp_right]
  simp only [component_fst]
  exact (dNext i).map_zero

private theorem prevD_component_fst (f : B₁ ⟶ B) (i : ℤ) :
    prevD i (component f) ≫ (fst f).f i = 0 := by
  rw [← prevD_comp_right]
  simp only [component_fst]
  exact (prevD i).map_zero

private theorem dNext_component_snd (f : B₁ ⟶ B) (i : ℤ) :
    dNext i (component f) ≫ (snd f).f i =
      (snd f).f i ≫ dNext i
        (HomologicalComplex.pathObject.π₀CompιHomotopy B hcℤ).hom := by
  rw [← dNext_comp_right]
  simp only [component_snd, dNext_comp_left]

private theorem prevD_component_snd (f : B₁ ⟶ B) (i : ℤ) :
    prevD i (component f) ≫ (snd f).f i =
      (snd f).f i ≫ prevD i
        (HomologicalComplex.pathObject.π₀CompιHomotopy B hcℤ).hom := by
  rw [← prevD_comp_right]
  simp only [component_snd, prevD_comp_left]

/-- The canonical contraction of the fixed-arrow relative path, over its first projection. -/
def contraction (f : B₁ ⟶ B) : Homotopy (fst f ≫ sectionMap f) (𝟙 (obj f)) where
  hom := component f
  zero := component_zero f
  comm i := by
    apply (isPullbackAt f i).hom_ext
    · have hp : fst f ≫ sectionMap f ≫ fst f = fst f := by
        simp only [section_fst, Category.comp_id]
      have hp_i := congrArg (fun k : obj f ⟶ B₁ => k.f i) hp
      simpa only [HomologicalComplex.comp_f, Preadditive.add_comp,
        dNext_component_fst, prevD_component_fst, zero_add,
        HomologicalComplex.id_f, Category.id_comp, Category.assoc] using hp_i
    · have hp : fst f ≫ sectionMap f ≫ snd f =
          snd f ≫ HomologicalComplex.pathObject.π₀ B ≫
            HomologicalComplex.pathObject.ι B := by
        rw [section_snd, ← Category.assoc, fst_comp, Category.assoc]
      have hp_i := congrArg (fun k : obj f ⟶ B.pathObject => k.f i) hp
      calc
        (fst f ≫ sectionMap f).f i ≫ (snd f).f i =
            (snd f).f i ≫
              (HomologicalComplex.pathObject.π₀ B ≫ HomologicalComplex.pathObject.ι B).f i := by
          simpa only [HomologicalComplex.comp_f, Category.assoc] using hp_i
        _ = (dNext i (component f) + prevD i (component f) +
            (𝟙 (obj f) : obj f ⟶ obj f).f i) ≫ (snd f).f i := by
          rw [(HomologicalComplex.pathObject.π₀CompιHomotopy B hcℤ).comm i]
          simp only [Preadditive.comp_add, Preadditive.add_comp,
            dNext_component_snd, prevD_component_snd,
            HomologicalComplex.id_f, Category.id_comp, Category.comp_id]

/-- Each component of the actual contraction vanishes over the first projection. -/
theorem contraction_fst_hom (f : B₁ ⟶ B) (i j : ℤ) :
    (contraction f).hom i j ≫ (fst f).f j = 0 :=
  component_fst f i j

/-- The section and first projection are mutual homotopy inverses. -/
def equivalence (f : B₁ ⟶ B) : HomotopyEquiv B₁ (obj f) where
  hom := sectionMap f
  inv := fst f
  homotopyHomInvId := Homotopy.ofEq (section_fst f)
  homotopyInvHomId := contraction f

/-- The first and target projections are connected by the native endpoint homotopy. -/
def comparison (f : B₁ ⟶ B) : Homotopy (fst f ≫ f) (toTarget f) :=
  (Homotopy.ofEq (fst_comp f)).trans
    ((HomologicalComplex.pathObject.homotopy₀₁ B hcℤ).compLeft (snd f))

end CochainComplex.RelativePath
