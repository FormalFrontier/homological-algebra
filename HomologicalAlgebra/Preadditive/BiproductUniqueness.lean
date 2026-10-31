/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Indecomposable.Biproducts
public import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.CategoryTheory.Preadditive.Mat
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Uniqueness of finite biproduct decompositions

Finite biproduct decompositions whose summands have local endomorphism rings have the
same factors up to a bijection and isomorphism. Only the two displayed biproducts are
required in the original category. The additive envelope supplies partial sums for the
cancellation argument, and its fully faithful embedding reflects the resulting factors.

## References

This is the classical local-endomorphism-ring proof of Krull–Schmidt uniqueness.
The proof uses Kim Morrison's categorical Gaussian elimination and additive envelope in
Mathlib (`CategoryTheory.Preadditive.Biproducts` and `CategoryTheory.Preadditive.Mat`).
The finite-sum unit argument uses Mathlib's local-ring API by Kenny Lau, Chris Hughes
and Mario Carneiro. See also the shared finite-biproduct comparisons in
`HomologicalAlgebra.Indecomposable.Biproducts`.
-/

@[expose] public section

universe u v w w'

namespace CategoryTheory

open Limits Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C]

-- A split nonzero source cannot be a proper summand of an object with local End.
private theorem isIso_of_isUnit_comp {X Y : C} [Nontrivial (End X)]
    [IsLocalRing (End Y)] (a : X ⟶ Y) (b : Y ⟶ X)
    (hab : IsUnit (End.of (a ≫ b))) : IsIso a := by
  let : IsIso (a ≫ b) := (isUnit_iff_isIso _).1 hab
  let r : Y ⟶ X := b ≫ inv (a ≫ b)
  have har : a ≫ r = 𝟙 X := by simp [r, ← Category.assoc]
  let q : End Y := r ≫ a
  have hq : IsIdempotentElem q := by
    change (r ≫ a) ≫ (r ≫ a) = r ≫ a
    calc
      (r ≫ a) ≫ (r ≫ a) = r ≫ (a ≫ r) ≫ a := by simp only [Category.assoc]
      _ = r ≫ a := by rw [har]; simp
  have hq0 : q ≠ 0 := by
    intro h
    have he : (𝟙 X : End X) = 0 := by
      calc
        𝟙 X = a ≫ q ≫ r := by simp [q, ← Category.assoc, har]
        _ = 0 := by rw [h]; simp
    exact (one_ne_zero : (1 : End X) ≠ 0) he
  have hq1 : q = 1 := by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self q with h | h
    · exact (IsIdempotentElem.iff_eq_one_of_isUnit h).1 hq
    · have hc : 1 - q = 1 := (IsIdempotentElem.iff_eq_one_of_isUnit h).1 hq.one_sub
      have hz : q = 0 := by
        have hz' : -q = 0 := add_left_cancel (show (1 : End Y) + -q = 1 + 0 by
          simpa only [sub_eq_add_neg, add_zero] using hc)
        exact neg_eq_zero.mp hz'
      exact (hq0 hz).elim
  exact ⟨⟨r, har, hq1⟩⟩

private theorem exists_isIso_component {n m : ℕ} (Y : Fin n → C) (Z : Fin m → C)
    [HasBiproduct Y] [HasBiproduct Z]
    [∀ i, IsLocalRing (End (Y i))] [∀ j, IsLocalRing (End (Z j))]
    (h : (⨁ Y) ≅ (⨁ Z)) (i : Fin n) :
    ∃ j, IsIso (biproduct.ι Y i ≫ h.hom ≫ biproduct.π Z j) := by
  let a := fun j => biproduct.ι Y i ≫ h.hom ≫ biproduct.π Z j
  let b := fun j => biproduct.ι Z j ≫ h.inv ≫ biproduct.π Y i
  have hs : (∑ j, a j ≫ b j : End (Y i)) = 1 := by
    calc
      (∑ j, a j ≫ b j : End (Y i)) =
          biproduct.ι Y i ≫ h.hom ≫
            (∑ j, biproduct.π Z j ≫ biproduct.ι Z j) ≫ h.inv ≫ biproduct.π Y i := by
        simp only [a, b, comp_sum, sum_comp, Category.assoc]
      _ = 𝟙 (Y i) := by simp
  obtain ⟨j, _, hj⟩ := IsLocalRing.exists_of_isUnit_sum
    (show IsUnit (∑ j ∈ (Finset.univ : Finset (Fin m)), End.of (a j ≫ b j)) by
      rw [hs]
      exact isUnit_one)
  exact ⟨j, isIso_of_isUnit_comp (a j) (b j) hj⟩

section FiniteBiproducts

variable [HasFiniteBiproducts C]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

-- Split the last factor using the shared append comparison, not a second sum construction.
private noncomputable def splitLastIso {n : ℕ} (Y : Fin (n + 1) → C) :
    Y (Fin.last n) ⊞ (⨁ (fun i : Fin n => Y i.castSucc)) ≅ ⨁ Y :=
  biprod.braiding' _ _ ≪≫
    biprod.mapIso (Iso.refl _) (biproductUniqueIso (fun _ : Fin 1 => Y (Fin.last n))).symm ≪≫
    biproductAppendIso (fun i : Fin n => Y i.castSucc) (fun _ : Fin 1 => Y (Fin.last n)) ≪≫
    biproduct.mapIso (fun i => eqToIso (by
      change Fin.append (Fin.init Y) (fun _ : Fin 1 => Y (Fin.last n)) i = Y i
      rw [Fin.append_right_eq_snoc, Fin.snoc_init_self]))

private theorem splitLastIso_inl_hom {n : ℕ} (Y : Fin (n + 1) → C) :
    biprod.inl ≫ (splitLastIso Y).hom = biproduct.ι Y (Fin.last n) := by
  have hsingle : (biproductUniqueIso (fun _ : Fin 1 => Y (Fin.last n))).inv =
      biproduct.ι (fun _ : Fin 1 => Y (Fin.last n)) 0 := by
    apply biproduct.hom_ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [biproductUniqueIso, biproduct.uniqueUpToIso, limitBiconeOfUnique]
  simp only [splitLastIso, Iso.trans_hom, Iso.symm_hom, biprod.mapIso_hom,
    Iso.refl_hom, biproduct.mapIso_hom]
  rw [hsingle]
  simp [biprod.braiding']
  rfl

private theorem splitLastIso_ι_inr_hom {n : ℕ} (Y : Fin (n + 1) → C) (i : Fin n) :
    biproduct.ι (fun i : Fin n => Y i.castSucc) i ≫ biprod.inr ≫ (splitLastIso Y).hom =
      biproduct.ι Y i.castSucc := by
  suffices hs : eqToHom (show Y i.castSucc = Y (Fin.castAdd 1 i) from rfl) ≫
      biproduct.ι Y (Fin.castAdd 1 i) = biproduct.ι Y i.castSucc by
    simpa [splitLastIso, biprod.braiding'] using hs
  change (𝟙 (Y i.castSucc)) ≫ biproduct.ι Y i.castSucc = biproduct.ι Y i.castSucc
  exact Category.id_comp _

private theorem splitLastIso_inv_fst {n : ℕ} (Y : Fin (n + 1) → C) :
    (splitLastIso Y).inv ≫ biprod.fst = biproduct.π Y (Fin.last n) := by
  apply (cancel_epi (splitLastIso Y).hom).1
  simp only [Iso.hom_inv_id_assoc]
  apply biprod.hom_ext'
  · rw [biprod.inl_fst, ← Category.assoc, splitLastIso_inl_hom,
      biproduct.ι_π_self]
  · apply biproduct.hom_ext'
    intro i
    simp only [biprod.inr_fst, comp_zero]
    have hh := congrArg (fun a => a ≫ biproduct.π Y (Fin.last n))
      (splitLastIso_ι_inr_hom Y i)
    rw [biproduct.ι_π_ne Y (Fin.castSucc_ne_last i)] at hh
    exact hh.symm.trans (by rw [Category.assoc, Category.assoc])

private theorem exists_equiv_of_iso_biproduct_fin (n m : ℕ)
    (Y : Fin n → C) (Z : Fin m → C)
    [∀ i, IsLocalRing (End (Y i))] [∀ j, IsLocalRing (End (Z j))]
    (h : (⨁ Y) ≅ (⨁ Z)) :
    ∃ e : Fin n ≃ Fin m, ∀ i, Nonempty (Y i ≅ Z (e i)) := by
  classical
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => exact ⟨Equiv.refl _, fun i => Fin.elim0 i⟩
    | succ m =>
      obtain ⟨i, _⟩ := exists_isIso_component Z Y h.symm (Fin.last m)
      exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨j, hj⟩ := exists_isIso_component Y Z h (Fin.last n)
    cases m with
    | zero => exact Fin.elim0 j
    | succ m =>
      let s : Equiv.Perm (Fin (m + 1)) := Equiv.swap (Fin.last m) j
      let Z' : Fin (m + 1) → C := Z ∘ s
      let k : (⨁ Y) ≅ (⨁ Z') := h ≪≫ (biproduct.reindex s Z).symm
      have hk : IsIso (biproduct.ι Y (Fin.last n) ≫ k.hom ≫
          biproduct.π Z' (Fin.last m)) := by
        have hsj : s (Fin.last m) = j := Equiv.swap_apply_left _ _
        simp only [k, Z', Iso.trans_hom, Iso.symm_hom, biproduct.reindex,
          Category.assoc, biproduct.lift_π]
        change IsIso (biproduct.ι Y (Fin.last n) ≫ h.hom ≫
          biproduct.π Z (s (Fin.last m)))
        rw [hsj]
        exact hj
      let f : Y (Fin.last n) ⊞ (⨁ (fun i : Fin n => Y i.castSucc)) ≅
          Z' (Fin.last m) ⊞ (⨁ (fun i : Fin m => Z' i.castSucc)) :=
        splitLastIso Y ≪≫ k ≪≫ (splitLastIso Z').symm
      have hfentry : biprod.inl ≫ f.hom ≫ biprod.fst =
          biproduct.ι Y (Fin.last n) ≫ k.hom ≫ biproduct.π Z' (Fin.last m) := by
        change biprod.inl ≫ ((splitLastIso Y).hom ≫ k.hom ≫
          (splitLastIso Z').inv) ≫ biprod.fst = _
        calc
          _ = (biprod.inl ≫ (splitLastIso Y).hom) ≫ k.hom ≫
              ((splitLastIso Z').inv ≫ biprod.fst) := by simp only [Category.assoc]
          _ = _ := by rw [splitLastIso_inl_hom, splitLastIso_inv_fst]
      have hf : IsIso (biprod.inl ≫ f.hom ≫ biprod.fst) := by
        rw [hfentry]
        exact hk
      let := hf
      let : ∀ i : Fin n, IsLocalRing (End (Y i.castSucc)) := fun i =>
        inferInstanceAs (IsLocalRing (End (Y i.castSucc)))
      let : ∀ i : Fin m, IsLocalRing (End (Z' i.castSucc)) := fun i =>
        inferInstanceAs (IsLocalRing (End (Z (s i.castSucc))))
      obtain ⟨e, he⟩ := ih m (fun i : Fin n => Y i.castSucc)
        (fun i : Fin m => Z' i.castSucc) (Biprod.isoElim f)
      let t : Fin (n + 1) ≃ Fin (m + 1) :=
        (finSuccEquivLast.trans (Equiv.optionCongr e)).trans finSuccEquivLast.symm
      refine ⟨t.trans s, ?_⟩
      intro i
      induction i using Fin.lastCases with
      | last =>
        have : IsIso (biproduct.ι Y (Fin.last n) ≫ k.hom ≫
            biproduct.π Z' (Fin.last m)) := hk
        let := this
        simpa [t, Z'] using
          (show Nonempty (Y (Fin.last n) ≅ Z' (Fin.last m)) from
            ⟨asIso (biproduct.ι Y (Fin.last n) ≫ k.hom ≫ biproduct.π Z' (Fin.last m))⟩)
      | cast i =>
        simpa [t, Z'] using he i

end FiniteBiproducts

/-- Two finite biproduct decompositions with local canonical endomorphism rings have
isomorphic factors after an equivalence of index types. This is the classical
local-End Krull–Schmidt uniqueness theorem, using Mathlib's Gaussian elimination and
additive envelope. Only the two given biproducts are required in the original
preadditive category. The matching need not be unique, and the supplied total
isomorphism need not be permutation-diagonal. -/
theorem exists_equiv_of_iso_biproduct_of_isLocalRing_end
    {ι : Type w} {κ : Type w'} [Finite ι] [Finite κ]
    (Y : ι → C) (Z : κ → C)
    [HasBiproduct Y] [HasBiproduct Z]
    [∀ i, IsLocalRing (End (Y i))] [∀ j, IsLocalRing (End (Z j))]
    (h : (⨁ Y) ≅ (⨁ Z)) :
    ∃ e : ι ≃ κ, ∀ i, Nonempty (Y i ≅ Z (e i)) := by
  classical
  obtain ⟨n, ⟨eY⟩⟩ := Finite.exists_equiv_fin ι
  obtain ⟨m, ⟨eZ⟩⟩ := Finite.exists_equiv_fin κ
  let Ys : Fin n → C := fun i => Y (eY.symm i)
  let Zs : Fin m → C := fun j => Z (eZ.symm j)
  -- Shrink the two given sums in C before using Type-0 preservation APIs.
  let : HasProduct Ys :=
    hasProduct_of_equiv_of_iso Y Ys eY.symm (fun _ => Iso.refl _)
  let : HasProduct Zs :=
    hasProduct_of_equiv_of_iso Z Zs eZ.symm (fun _ => Iso.refl _)
  let : HasBiproduct Ys := HasBiproduct.of_hasProduct Ys
  let : HasBiproduct Zs := HasBiproduct.of_hasProduct Zs
  let pY (i : ι) : Ys (eY i) ≅ Y i :=
    eqToIso (congrArg Y (eY.symm_apply_apply i))
  let pZ (j : κ) : Zs (eZ j) ≅ Z j :=
    eqToIso (congrArg Z (eZ.symm_apply_apply j))
  let cY : (⨁ Y) ≅ (⨁ Ys) := biproduct.whiskerEquiv eY pY
  let cZ : (⨁ Z) ≅ (⨁ Zs) := biproduct.whiskerEquiv eZ pZ
  let hsmall : (⨁ Ys) ≅ (⨁ Zs) := cY.symm ≪≫ h ≪≫ cZ
  let : ∀ i : Fin n, IsLocalRing (End (Ys i)) := fun i =>
    inferInstanceAs (IsLocalRing (End (Y (eY.symm i))))
  let : ∀ j : Fin m, IsLocalRing (End (Zs j)) := fun j =>
    inferInstanceAs (IsLocalRing (End (Z (eZ.symm j))))
  let E : C ⥤ Mat_ C := Mat_.embedding C
  let hf : E.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful E
  let endEquiv (X : C) : End X ≃+* End (E.obj X) :=
    MulEquiv.toRingEquiv (hf.mulEquivEnd X)
      (fun a b => show E.map (a + b) = E.map a + E.map b from E.map_add)
  let : ∀ i : Fin n, IsLocalRing (End (E.obj (Ys i))) :=
    fun i => (endEquiv (Ys i)).isLocalRing
  let : ∀ j : Fin m, IsLocalRing (End (E.obj (Zs j))) :=
    fun j => (endEquiv (Zs j)).isLocalRing
  let mY : E.obj (⨁ Ys) ≅ (⨁ fun i : Fin n => E.obj (Ys i)) := E.mapBiproduct Ys
  let mZ : E.obj (⨁ Zs) ≅ (⨁ fun j : Fin m => E.obj (Zs j)) := E.mapBiproduct Zs
  let hMat : (⨁ fun i : Fin n => E.obj (Ys i)) ≅
      (⨁ fun j : Fin m => E.obj (Zs j)) :=
    mY.symm ≪≫ E.mapIso hsmall ≪≫ mZ
  obtain ⟨es, hs⟩ := exists_equiv_of_iso_biproduct_fin
    (C := Mat_ C) n m (fun i => E.obj (Ys i)) (fun j => E.obj (Zs j)) hMat
  let e : ι ≃ κ := eY.trans (es.trans eZ.symm)
  refine ⟨e, ?_⟩
  intro i
  obtain ⟨qi⟩ := hs (eY i)
  let qiC : Ys (eY i) ≅ Zs (es (eY i)) := hf.preimageIso qi
  have targetEq : Zs (es (eY i)) = Z (e i) := rfl
  exact ⟨(pY i).symm ≪≫ qiC ≪≫ eqToIso targetEq⟩

end CategoryTheory
