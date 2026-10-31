/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Indecomposable.Biproducts
public import Mathlib.CategoryTheory.Subobject.NoetherianObject
import Mathlib.Order.WellFounded

/-!
# Finite indecomposable decompositions of Noetherian objects

A Noetherian object in a category with zero morphisms and finite biproducts is
isomorphic to a finite biproduct of indecomposable objects. The zero object is
represented by the empty family.

The proof uses two ascending-chain arguments on Mathlib's `Subobject` order.
First, a maximal proper biproduct summand of a nonzero object has an
indecomposable complement. Then a maximal biproduct summand admitting a finite
indecomposable decomposition has zero complement. Throughout, complements are
retained through the specified subobject arrow; a split monomorphism alone is
not used as a substitute for a biproduct decomposition.

## References

* `Mathlib.CategoryTheory.Subobject.NoetherianObject` supplies the chain condition
  and its inheritance along monomorphisms.
* `Mathlib.CategoryTheory.Subobject.Basic` supplies strict-subobject comparison.
* `Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts` supplies the biproduct
  universal properties.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits ZeroObject

attribute [local instance] Limits.hasBinaryBiproducts_of_finite_biproducts

variable {C : Type u} [Category.{v} C]
  [HasZeroMorphisms C] [HasFiniteBiproducts C]

private abbrev CoherentSummand {X : C} (S : Subobject X) : Prop :=
  ∃ T : C, ∃ g : T ⟶ X, IsIso (biprod.desc S.arrow g)

private abbrev FiniteIndecomposableDecomposition (X : C) : Prop :=
  ∃ n : ℕ, ∃ F : Fin n → C,
    (∀ i, Indecomposable (F i)) ∧ Nonempty (X ≅ ⨁ F)

private lemma finite_decomposition_of_iso {X Y : C} (e : X ≅ Y)
    (hY : FiniteIndecomposableDecomposition Y) :
    FiniteIndecomposableDecomposition X := by
  obtain ⟨n, F, hF, ⟨f⟩⟩ := hY
  exact ⟨n, F, hF, ⟨e ≪≫ f⟩⟩

private lemma finite_decomposition_of_isZero {X : C} (hX : IsZero X) :
    FiniteIndecomposableDecomposition X := by
  let F : Fin 0 → C := Fin.elim0
  have hF : IsZero (⨁ F) := by
    rw [IsZero.iff_id_eq_zero]
    apply biproduct.hom_ext
    intro i
    exact Fin.elim0 i
  exact ⟨0, F, (fun i ↦ Fin.elim0 i), ⟨hX.iso hF⟩⟩

private lemma finite_decomposition_of_indecomposable {X : C} (hX : Indecomposable X) :
    FiniteIndecomposableDecomposition X := by
  exact ⟨1, (fun _ ↦ X), (fun _ ↦ hX),
    ⟨(biproductUniqueIso (fun _ : Fin 1 ↦ X)).symm⟩⟩

private lemma finite_decomposition_biprod {X Y : C}
    (hX : FiniteIndecomposableDecomposition X)
    (hY : FiniteIndecomposableDecomposition Y) :
    FiniteIndecomposableDecomposition (X ⊞ Y) := by
  obtain ⟨m, F, hF, ⟨eF⟩⟩ := hX
  obtain ⟨n, G, hG, ⟨eG⟩⟩ := hY
  refine ⟨m + n, Fin.append F G, ?_,
    ⟨biprod.mapIso eF eG ≪≫ biproductAppendIso F G⟩⟩
  intro i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simpa only [Fin.append_left] using hF j
  · simpa only [Fin.append_right] using hG j

/-- A coherent complement vanishes exactly when the specified subobject is the top one. -/
private lemma complement_isZero_iff {X T : C} (S : Subobject X) (g : T ⟶ X)
    [IsIso (biprod.desc S.arrow g)] : IsZero T ↔ S = ⊤ := by
  calc
    IsZero T ↔ IsIso (biprod.inl : (S : C) ⟶ (S : C) ⊞ T) :=
      (biprod.isIso_inl_iff_isZero (S : C) T).symm
    _ ↔ IsIso ((biprod.inl : (S : C) ⟶ (S : C) ⊞ T) ≫
        biprod.desc S.arrow g) :=
      (isIso_comp_right_iff _ _).symm
    _ ↔ IsIso S.arrow := by rw [biprod.inl_desc]
    _ ↔ S = ⊤ := Subobject.isIso_arrow_iff_eq_top S

private lemma zero_summand (X : C) :
    IsZero ((⊥ : Subobject X) : C) ∧
      IsIso (biprod.desc (⊥ : Subobject X).arrow (𝟙 X)) := by
  have h : IsZero ((⊥ : Subobject X) : C) :=
    (isZero_zero C).of_iso Subobject.botCoeIsoZero
  refine ⟨h, ?_⟩
  have hd : biprod.desc (⊥ : Subobject X).arrow (𝟙 X) =
      (isoZeroBiprod h).inv := by
    change biprod.desc (⊥ : Subobject X).arrow (𝟙 X) = biprod.snd
    apply biprod.hom_ext' <;> simp
  rw [hd]
  infer_instance

/-- Replacing an inclusion by the chosen subobject representative preserves its complement. -/
private lemma coherent_of_biprod_iso {A T X : C} (e : (A ⊞ T) ≅ X) :
    ∃ g : T ⟶ X,
      IsIso (biprod.desc (Subobject.mk (biprod.inl ≫ e.hom)).arrow g) := by
  let f : A ⟶ X := biprod.inl ≫ e.hom
  let d : ((Subobject.mk f : C) ⊞ T) ≅ X :=
    biprod.mapIso (Subobject.underlyingIso f) (Iso.refl T) ≪≫ e
  refine ⟨biprod.inr ≫ e.hom, ?_⟩
  have hd : biprod.desc (Subobject.mk f).arrow (biprod.inr ≫ e.hom) = d.hom := by
    apply biprod.hom_ext' <;> simp [d, f]
  rw [hd]
  infer_instance

/-- Adjoining a nonzero factor of a coherent complement strictly enlarges a summand. -/
private lemma enlarge_coherent_summand {X U V : C} (S : Subobject X)
    (e : ((S : C) ⊞ (U ⊞ V)) ≅ X)
    (he : (biprod.inl : (S : C) ⟶ (S : C) ⊞ (U ⊞ V)) ≫ e.hom = S.arrow)
    (hU : ¬ IsZero U) :
    ∃ R : Subobject X, S < R ∧ ∃ g : V ⟶ X,
      IsIso (biprod.desc R.arrow g) ∧ Nonempty ((R : C) ≅ (S : C) ⊞ U) := by
  let d : (((S : C) ⊞ U) ⊞ V) ≅ X := biprod.associator (S : C) U V ≪≫ e
  let f : ((S : C) ⊞ U) ⟶ X := biprod.inl ≫ d.hom
  have hassoc : (biprod.inl : (S : C) ⟶ (S : C) ⊞ U) ≫
      biprod.inl ≫ (biprod.associator (S : C) U V).hom = biprod.inl := by
    apply biprod.hom_ext
    · simp [biprod.associator, Category.assoc]
    · apply biprod.hom_ext <;> simp [biprod.associator, Category.assoc]
  have hfac : (biprod.inl : (S : C) ⟶ (S : C) ⊞ U) ≫ f = S.arrow := by
    calc
      (biprod.inl : (S : C) ⟶ (S : C) ⊞ U) ≫ f =
          (biprod.inl : (S : C) ⟶ (S : C) ⊞ (U ⊞ V)) ≫ e.hom := by
        simpa only [f, d, Iso.trans_hom, Category.assoc] using
          congrArg (fun k ↦ k ≫ e.hom) hassoc
      _ = S.arrow := he
  have hlt : S < Subobject.mk f := by
    have h := Subobject.mk_lt_mk_of_comm
      (biprod.inl : (S : C) ⟶ (S : C) ⊞ U) hfac
      (fun hi ↦ hU ((biprod.isIso_inl_iff_isZero (S : C) U).1 hi))
    simpa only [Subobject.mk_arrow] using h
  obtain ⟨g, hg⟩ := coherent_of_biprod_iso d
  exact ⟨Subobject.mk f, hlt, g, hg, ⟨Subobject.underlyingIso f⟩⟩

/-- A nonzero Noetherian object has a nonzero indecomposable biproduct factor. -/
private lemma exists_indecomposable_summand (X : C) [IsNoetherianObject X]
    (hX : ¬ IsZero X) :
    ∃ Z W : C, Indecomposable Z ∧ Nonempty (X ≅ Z ⊞ W) := by
  classical
  let P : Subobject X → Prop := fun S ↦ S ≠ ⊤ ∧ CoherentSummand S
  have hseed : P ⊥ := by
    obtain ⟨_, hz⟩ := zero_summand X
    let := hz
    exact ⟨(fun h ↦ hX ((complement_isZero_iff (⊥ : Subobject X) (𝟙 X)).2 h)),
      X, 𝟙 X, hz⟩
  obtain ⟨S, hS, hmax⟩ := wellFounded_gt.has_min {S | P S} ⟨⊥, hseed⟩
  obtain ⟨T, g, hg⟩ := hS.2
  let := hg
  have hT : ¬ IsZero T := fun h ↦ hS.1 ((complement_isZero_iff S g).1 h)
  have hind : Indecomposable T := by
    refine ⟨hT, ?_⟩
    intro U V e
    by_cases hU : IsZero U
    · exact Or.inl hU
    by_cases hV : IsZero V
    · exact Or.inr hV
    exfalso
    let d : ((S : C) ⊞ (U ⊞ V)) ≅ X :=
      biprod.mapIso (Iso.refl (S : C)) e.symm ≪≫ asIso (biprod.desc S.arrow g)
    have hd : (biprod.inl : (S : C) ⟶ (S : C) ⊞ (U ⊞ V)) ≫ d.hom =
        S.arrow := by
      simp [d]
    obtain ⟨R, hSR, gR, hgR, _⟩ := enlarge_coherent_summand S d hd hU
    let := hgR
    have hR : P R :=
      ⟨(fun h ↦ hV ((complement_isZero_iff R gR).2 h)), V, gR, hgR⟩
    exact hmax R hR hSR
  exact ⟨T, (S : C), hind,
    ⟨(asIso (biprod.desc S.arrow g)).symm ≪≫ biprod.braiding (S : C) T⟩⟩

/-- A Noetherian object is isomorphic to a finite biproduct of indecomposable objects. -/
theorem exists_finite_indecomposable_biproduct_of_isNoetherianObject
    (X : C) [IsNoetherianObject X] :
    ∃ n : ℕ, ∃ F : Fin n → C,
      (∀ i, Indecomposable (F i)) ∧ Nonempty (X ≅ ⨁ F) := by
  classical
  let P : Subobject X → Prop := fun S ↦
    CoherentSummand S ∧ FiniteIndecomposableDecomposition (S : C)
  have hseed : P ⊥ := by
    obtain ⟨hz, hg⟩ := zero_summand X
    exact ⟨⟨X, 𝟙 X, hg⟩, finite_decomposition_of_isZero hz⟩
  obtain ⟨S, hS, hmax⟩ := wellFounded_gt.has_min {S | P S} ⟨⊥, hseed⟩
  obtain ⟨T, g, hg⟩ := hS.1
  let := hg
  have hT : IsZero T := by
    by_contra hT
    have : Mono g := by
      rw [← biprod.inr_desc S.arrow g]
      infer_instance
    have : IsNoetherianObject T := isNoetherianObject_of_mono g
    obtain ⟨Z, W, hZ, ⟨e⟩⟩ := exists_indecomposable_summand T hT
    let d : ((S : C) ⊞ (Z ⊞ W)) ≅ X :=
      biprod.mapIso (Iso.refl (S : C)) e.symm ≪≫ asIso (biprod.desc S.arrow g)
    have hd : (biprod.inl : (S : C) ⟶ (S : C) ⊞ (Z ⊞ W)) ≫ d.hom =
        S.arrow := by
      simp [d]
    obtain ⟨R, hSR, gR, hgR, ⟨eR⟩⟩ := enlarge_coherent_summand S d hd hZ.1
    have hR : P R := ⟨⟨W, gR, hgR⟩,
      finite_decomposition_of_iso eR
        (finite_decomposition_biprod hS.2 (finite_decomposition_of_indecomposable hZ))⟩
    exact hmax R hR hSR
  have : IsIso S.arrow :=
    (Subobject.isIso_arrow_iff_eq_top S).2 ((complement_isZero_iff S g).1 hT)
  exact finite_decomposition_of_iso (asIso S.arrow).symm hS.2

end CategoryTheory
