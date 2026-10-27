/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Homotopies from coproducts of cochain complexes

Homotopies on the summands of a coproduct of integer cochain complexes assemble
whenever degree evaluation preserves the supplied coproduct. The construction
requires only preadditivity. Its restriction and reconstruction identities
express the universal property on specified homotopy data.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type w}

noncomputable section

namespace Homotopy

/-- Assemble homotopies on the summands of a coproduct of cochain complexes. -/
def sigmaDesc {F : ι → CochainComplex C ℤ} [HasCoproduct F]
    [∀ n : ℤ, PreservesColimit (Discrete.functor F)
      (HomologicalComplex.eval C (ComplexShape.up ℤ) n)]
    {Y : CochainComplex C ℤ} {f g : (∐ F) ⟶ Y}
    (h : ∀ i, Homotopy (Sigma.ι F i ≫ f) (Sigma.ι F i ≫ g)) :
    Homotopy f g := by
  classical
  let H : (a b : ℤ) → (∐ F).X a ⟶ Y.X b := fun a b =>
    (isColimitOfPreserves (HomologicalComplex.eval C (ComplexShape.up ℤ) a)
      (colimit.isColimit (Discrete.functor F))).desc
        { pt := Y.X b
          ι := Discrete.natTrans (fun i => (h i.as).hom a b) }
  have H_fac (i : ι) (a b : ℤ) :
      (Sigma.ι F i).f a ≫ H a b = (h i).hom a b := by
    simpa [H] using
      (isColimitOfPreserves (HomologicalComplex.eval C (ComplexShape.up ℤ) a)
        (colimit.isColimit (Discrete.functor F))).fac
          { pt := Y.X b
            ι := Discrete.natTrans (fun j => (h j.as).hom a b) }
          (Discrete.mk i)
  have H_fac_assoc (i : ι) (a b : ℤ) {T : C} (k : Y.X b ⟶ T) :
      (Sigma.ι F i).f a ≫ H a b ≫ k = (h i).hom a b ≫ k := by
    rw [← Category.assoc, H_fac]
  refine { hom := H, zero := ?_, comm := ?_ }
  · intro a b hab
    apply (isColimitOfPreserves (HomologicalComplex.eval C (ComplexShape.up ℤ) a)
      (colimit.isColimit (Discrete.functor F))).hom_ext
    rintro ⟨i⟩
    simpa using (H_fac i a b).trans ((h i).zero a b hab)
  · intro n
    apply (isColimitOfPreserves (HomologicalComplex.eval C (ComplexShape.up ℤ) n)
      (colimit.isColimit (Discrete.functor F))).hom_ext
    rintro ⟨i⟩
    simpa [fromNext, toPrev, HomologicalComplex.dFrom, Category.assoc,
      H_fac, H_fac_assoc] using (h i).comm n

variable {F : ι → CochainComplex C ℤ} [HasCoproduct F]
  [∀ n : ℤ, PreservesColimit (Discrete.functor F)
    (HomologicalComplex.eval C (ComplexShape.up ℤ) n)]
  {Y : CochainComplex C ℤ} {f g : (∐ F) ⟶ Y}

@[reassoc (attr := simp)]
theorem sigmaDesc_hom (h : ∀ i, Homotopy (Sigma.ι F i ≫ f) (Sigma.ι F i ≫ g))
    (i : ι) (a b : ℤ) :
    (Sigma.ι F i).f a ≫ (sigmaDesc h).hom a b = (h i).hom a b := by
  simpa [sigmaDesc] using
    (isColimitOfPreserves (HomologicalComplex.eval C (ComplexShape.up ℤ) a)
      (colimit.isColimit (Discrete.functor F))).fac
        { pt := Y.X b
          ι := Discrete.natTrans (fun j => (h j.as).hom a b) }
        (Discrete.mk i)

@[simp]
theorem sigmaDesc_compLeft (h : ∀ i, Homotopy (Sigma.ι F i ≫ f) (Sigma.ι F i ≫ g))
    (i : ι) :
    (sigmaDesc h).compLeft (Sigma.ι F i) = h i := by
  ext a b
  exact sigmaDesc_hom h i a b

@[simp]
theorem sigmaDesc_compLeft_self (h : Homotopy f g) :
    sigmaDesc (fun i => h.compLeft (Sigma.ι F i)) = h := by
  ext a b
  apply (isColimitOfPreserves (HomologicalComplex.eval C (ComplexShape.up ℤ) a)
    (colimit.isColimit (Discrete.functor F))).hom_ext
  rintro ⟨i⟩
  simp

/-- A homotopy from a coproduct exists exactly when its restrictions admit homotopies. -/
theorem nonempty_sigma_iff : Nonempty (Homotopy f g) ↔
    ∀ i, Nonempty (Homotopy (Sigma.ι F i ≫ f) (Sigma.ι F i ≫ g)) := by
  constructor
  · rintro ⟨h⟩ i
    exact ⟨h.compLeft (Sigma.ι F i)⟩
  · intro h
    classical
    exact ⟨sigmaDesc (fun i => (h i).some)⟩

end Homotopy
