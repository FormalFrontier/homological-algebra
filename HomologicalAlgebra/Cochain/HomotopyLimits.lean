/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Homotopies and (co)products of cochain complexes

Homotopies assemble from the summands of a coproduct or into the factors of a
product of integer cochain complexes whenever degree evaluation preserves the
supplied (co)product. The constructions require only preadditivity. Restriction
and reconstruction identities give equivalences on specified homotopy data.
For diagonal maps between two families, existence of a homotopy is equivalent
to existence on each component. Only domain evaluation must preserve coproducts,
and only codomain evaluation must preserve products. These diagonal criteria
concern existence, not an equivalence of all homotopy data.
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

/-- Homotopies from a coproduct are equivalent to their restrictions to the summands. -/
def sigmaEquiv : Homotopy f g ≃
    ∀ i, Homotopy (Sigma.ι F i ≫ f) (Sigma.ι F i ≫ g) where
  toFun h i := h.compLeft (Sigma.ι F i)
  invFun := sigmaDesc
  left_inv := sigmaDesc_compLeft_self
  right_inv h := funext (sigmaDesc_compLeft h)

@[simp]
theorem sigmaEquiv_apply (h : Homotopy f g) (i : ι) :
    sigmaEquiv h i = h.compLeft (Sigma.ι F i) := rfl

@[simp]
theorem sigmaEquiv_symm_apply
    (h : ∀ i, Homotopy (Sigma.ι F i ≫ f) (Sigma.ι F i ≫ g)) :
    sigmaEquiv.symm h = sigmaDesc h := rfl

/-- A homotopy from a coproduct exists exactly when its restrictions admit homotopies. -/
theorem nonempty_sigma_iff : Nonempty (Homotopy f g) ↔
    ∀ i, Nonempty (Homotopy (Sigma.ι F i ≫ f) (Sigma.ι F i ≫ g)) := by
  constructor
  · rintro ⟨h⟩ i
    exact ⟨sigmaEquiv h i⟩
  · intro h
    classical
    exact ⟨sigmaEquiv.symm (fun i => (h i).some)⟩

end Homotopy

/-! ## Homotopies into products

Evaluation-preservation identifies the evaluated projections with a product cone. This gives a
homotopy into the supplied product from specified component homotopies, with exact projection
recovery and reconstruction of the complete homotopy data.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Homotopy

universe u₁ v₁ w₁

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
variable {ι : Type w₁}
variable (F : ι → CochainComplex C ℤ) [HasProduct F]
variable [∀ n : ℤ, PreservesLimit (Discrete.functor F)
  (HomologicalComplex.eval C (ComplexShape.up ℤ) n)]
variable {X : CochainComplex C ℤ} {f g : X ⟶ ∏ᶜ F}
variable (h : ∀ i : ι, Homotopy (f ≫ Pi.π F i) (g ≫ Pi.π F i))

/-- Assemble homotopies into a product of cochain complexes when evaluation preserves
that product. -/
noncomputable def piLift : Homotopy f g := by
  let t (a b : ℤ) : X.X a ⟶ (∏ᶜ F).X b :=
    (isLimitOfPreserves (HomologicalComplex.eval C (ComplexShape.up ℤ) b)
      (limit.isLimit (Discrete.functor F))).lift
      { pt := X.X a
        π := Discrete.natTrans (fun i => (h i.as).hom a b) }
  have fac (a b : ℤ) (i : ι) : t a b ≫ (Pi.π F i).f b = (h i).hom a b := by
    exact (isLimitOfPreserves (HomologicalComplex.eval C (ComplexShape.up ℤ) b)
      (limit.isLimit (Discrete.functor F))).fac _ (Discrete.mk i)
  have fac_assoc (a b : ℤ) (i : ι) {W : C} (k : (F i).X b ⟶ W) :
      t a b ≫ (Pi.π F i).f b ≫ k = (h i).hom a b ≫ k := by
    rw [← Category.assoc, fac]
  refine { hom := t, zero := ?_, comm := ?_ }
  · intro a b hab
    apply (isLimitOfPreserves (HomologicalComplex.eval C (ComplexShape.up ℤ) b)
      (limit.isLimit (Discrete.functor F))).hom_ext
    intro i
    calc
      _ = (h i.as).hom a b := fac a b i.as
      _ = 0 := (h i.as).zero a b hab
      _ = _ := by simp
  · intro a
    apply (isLimitOfPreserves (HomologicalComplex.eval C (ComplexShape.up ℤ) a)
      (limit.isLimit (Discrete.functor F))).hom_ext
    intro i
    change f.f a ≫ (Pi.π F i.as).f a =
      (X.d a ((ComplexShape.up ℤ).next a) ≫ t ((ComplexShape.up ℤ).next a) a +
        t a ((ComplexShape.up ℤ).prev a) ≫
          (∏ᶜ F).d ((ComplexShape.up ℤ).prev a) a + g.f a) ≫
        (Pi.π F i.as).f a
    have hi := (h i.as).comm a
    change f.f a ≫ (Pi.π F i.as).f a =
      X.d a ((ComplexShape.up ℤ).next a) ≫
          (h i.as).hom ((ComplexShape.up ℤ).next a) a +
        (h i.as).hom a ((ComplexShape.up ℤ).prev a) ≫
          (F i.as).d ((ComplexShape.up ℤ).prev a) a +
        g.f a ≫ (Pi.π F i.as).f a at hi
    simpa only [Preadditive.add_comp, Category.assoc,
      ← (Pi.π F i.as).comm, fac, fac_assoc] using hi

/-- Projection of an assembled homotopy recovers each specified component. -/
@[reassoc (attr := simp), simp]
theorem piLift_hom (a b : ℤ) (i : ι) :
    (piLift F h).hom a b ≫ (Pi.π F i).f b = (h i).hom a b := by
  exact (isLimitOfPreserves (HomologicalComplex.eval C (ComplexShape.up ℤ) b)
    (limit.isLimit (Discrete.functor F))).fac _ (Discrete.mk i)

/-- Postcomposition by a product projection recovers the specified homotopy data. -/
@[simp]
theorem piLift_compRight (i : ι) :
    (piLift F h).compRight (Pi.π F i) = h i := by
  ext a b
  exact piLift_hom F h a b i

/-- Assembling all projections of a homotopy returns that homotopy. -/
@[simp]
theorem piLift_compRight_self (H : Homotopy f g) :
    piLift F (fun i => H.compRight (Pi.π F i)) = H := by
  ext a b
  apply (isLimitOfPreserves (HomologicalComplex.eval C (ComplexShape.up ℤ) b)
    (limit.isLimit (Discrete.functor F))).hom_ext
  intro i
  change
    (piLift F (fun j => H.compRight (Pi.π F j))).hom a b ≫
        (Pi.π F i.as).f b =
      H.hom a b ≫ (Pi.π F i.as).f b
  exact piLift_hom F (fun j => H.compRight (Pi.π F j)) a b i.as

/-- Restricting homotopies along product projections is an equivalence. -/
noncomputable def piEquiv :
    Homotopy f g ≃ ∀ i : ι, Homotopy (f ≫ Pi.π F i) (g ≫ Pi.π F i) where
  toFun H i := H.compRight (Pi.π F i)
  invFun := piLift F
  left_inv := piLift_compRight_self F
  right_inv k := funext (piLift_compRight F k)

@[simp]
theorem piEquiv_apply (H : Homotopy f g) (i : ι) :
    piEquiv F H i = H.compRight (Pi.π F i) := rfl

@[simp]
theorem piEquiv_symm_apply : (piEquiv F).symm h = piLift F h := rfl

/-- Homotopies into a product exist exactly when all projected homotopies exist. -/
theorem nonempty_pi_iff : Nonempty (Homotopy f g) ↔
    ∀ i : ι, Nonempty (Homotopy (f ≫ Pi.π F i) (g ≫ Pi.π F i)) := by
  constructor
  · rintro ⟨H⟩ i
    exact ⟨piEquiv F H i⟩
  · intro k
    classical
    exact ⟨(piEquiv F).symm (fun i => Classical.choice (k i))⟩

example : ∃ H : Homotopy f g, ∀ i : ι, H.compRight (Pi.π F i) = h i :=
  ⟨piLift F h, piLift_compRight F h⟩

end Homotopy

namespace Homotopy

/-- Diagonal maps between coproducts are homotopic exactly when the component maps are.
Only evaluation on the domain family must preserve the supplied coproduct. This is an
existence criterion, not an equivalence on all homotopy data. -/
theorem nonempty_sigma_map_iff {K L : ι → CochainComplex C ℤ}
    [HasCoproduct K] [HasCoproduct L]
    [∀ n : ℤ, PreservesColimit (Discrete.functor K)
      (HomologicalComplex.eval C (ComplexShape.up ℤ) n)]
    (f g : ∀ i, K i ⟶ L i) :
    Nonempty (Homotopy
      (CategoryTheory.Limits.Sigma.desc (fun i => f i ≫ CategoryTheory.Limits.Sigma.ι L i))
      (CategoryTheory.Limits.Sigma.desc (fun i => g i ≫ CategoryTheory.Limits.Sigma.ι L i))) ↔
      ∀ i, Nonempty (Homotopy (f i) (g i)) := by
  classical
  constructor
  · rintro ⟨H⟩ i
    let p : (∐ L) ⟶ L i := CategoryTheory.Limits.Sigma.desc
      (fun j => if e : j = i then eqToHom (congrArg L e) else 0)
    have hi : Homotopy (f i ≫ CategoryTheory.Limits.Sigma.ι L i)
        (g i ≫ CategoryTheory.Limits.Sigma.ι L i) := by
      simpa using H.compLeft (CategoryTheory.Limits.Sigma.ι K i)
    exact ⟨by simpa [Category.assoc, p] using hi.compRight p⟩
  · intro h
    apply nonempty_sigma_iff.mpr
    intro i
    rcases h i with ⟨hi⟩
    exact ⟨by simpa using hi.compRight (CategoryTheory.Limits.Sigma.ι L i)⟩

/-- Diagonal maps between products are homotopic exactly when the component maps are.
Only evaluation on the codomain family must preserve the supplied product. This is an
existence criterion; off-diagonal homotopy data need not vanish. -/
theorem nonempty_pi_map_iff {K L : ι → CochainComplex C ℤ}
    [HasProduct K] [HasProduct L]
    [∀ n : ℤ, PreservesLimit (Discrete.functor L)
      (HomologicalComplex.eval C (ComplexShape.up ℤ) n)]
    (f g : ∀ i, K i ⟶ L i) :
    Nonempty (Homotopy
      (CategoryTheory.Limits.Pi.lift (fun i => CategoryTheory.Limits.Pi.π K i ≫ f i))
      (CategoryTheory.Limits.Pi.lift (fun i => CategoryTheory.Limits.Pi.π K i ≫ g i))) ↔
      ∀ i, Nonempty (Homotopy (f i) (g i)) := by
  classical
  constructor
  · rintro ⟨H⟩ i
    let q : K i ⟶ ∏ᶜ K := CategoryTheory.Limits.Pi.lift
      (fun j => if e : i = j then eqToHom (congrArg K e) else 0)
    have hi : Homotopy (CategoryTheory.Limits.Pi.π K i ≫ f i)
        (CategoryTheory.Limits.Pi.π K i ≫ g i) := by
      simpa using H.compRight (CategoryTheory.Limits.Pi.π L i)
    exact ⟨by simpa [← Category.assoc, q] using hi.compLeft q⟩
  · intro h
    apply (nonempty_pi_iff L).mpr
    intro i
    rcases h i with ⟨hi⟩
    exact ⟨by simpa using hi.compLeft (CategoryTheory.Limits.Pi.π K i)⟩

/-- A supplied coproduct admits a homotopy from identity to zero exactly when each
summand does, provided degree evaluation preserves that coproduct. -/
theorem nonempty_sigma_id_zero_iff {K : ι → CochainComplex C ℤ}
    [HasCoproduct K]
    [∀ n : ℤ, PreservesColimit (Discrete.functor K)
      (HomologicalComplex.eval C (ComplexShape.up ℤ) n)] :
    Nonempty (Homotopy (𝟙 (∐ K)) 0) ↔
      ∀ i, Nonempty (Homotopy (𝟙 (K i)) 0) := by
  have hid : CategoryTheory.Limits.Sigma.desc
      (fun i => 𝟙 (K i) ≫ CategoryTheory.Limits.Sigma.ι K i) = 𝟙 (∐ K) := by
    apply CategoryTheory.Limits.Sigma.hom_ext
    intro i
    simp
  have hzero : CategoryTheory.Limits.Sigma.desc
      (fun i => (0 : K i ⟶ K i) ≫ CategoryTheory.Limits.Sigma.ι K i) =
      (0 : (∐ K) ⟶ ∐ K) := by
    apply CategoryTheory.Limits.Sigma.hom_ext
    intro i
    simp
  simpa only [hid, hzero] using
    nonempty_sigma_map_iff (fun i => 𝟙 (K i)) (fun i => (0 : K i ⟶ K i))

/-- A supplied product admits a homotopy from identity to zero exactly when each
factor does, provided degree evaluation preserves that product. -/
theorem nonempty_pi_id_zero_iff {K : ι → CochainComplex C ℤ}
    [HasProduct K]
    [∀ n : ℤ, PreservesLimit (Discrete.functor K)
      (HomologicalComplex.eval C (ComplexShape.up ℤ) n)] :
    Nonempty (Homotopy (𝟙 (∏ᶜ K)) 0) ↔
      ∀ i, Nonempty (Homotopy (𝟙 (K i)) 0) := by
  have hid : CategoryTheory.Limits.Pi.lift
      (fun i => CategoryTheory.Limits.Pi.π K i ≫ 𝟙 (K i)) = 𝟙 (∏ᶜ K) := by
    apply CategoryTheory.Limits.Pi.hom_ext
    intro i
    simp
  have hzero : CategoryTheory.Limits.Pi.lift
      (fun i => CategoryTheory.Limits.Pi.π K i ≫ (0 : K i ⟶ K i)) =
      (0 : (∏ᶜ K) ⟶ ∏ᶜ K) := by
    apply CategoryTheory.Limits.Pi.hom_ext
    intro i
    simp
  simpa only [hid, hzero] using
    nonempty_pi_map_iff (fun i => 𝟙 (K i)) (fun i => (0 : K i ⟶ K i))

end Homotopy
