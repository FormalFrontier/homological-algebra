/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.RingTheory.LocalRing.Defs
import HomologicalAlgebra.Indecomposable.Biproducts
import StableRange.CategoryTheory.Cancellation
import Mathlib.CategoryTheory.Preadditive.Mat
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Cancellation of finite biproducts with local endomorphism rings

A finite biproduct of objects with local canonical endomorphism rings cancels
from a binary biproduct in a preadditive category. The remaining objects are
arbitrary. Only the common finite biproduct and the two displayed binary
biproducts are required; no residual subfamily biproducts are assumed to exist.
The object, morphism and finite-index universes are independent.

The local endomorphism rings need not be commutative or division rings.
Locality includes nontriviality, so zero factors are excluded without a separate
hypothesis. The empty family is allowed and gives a zero common summand.
The conclusion asserts existence of an isomorphism, not a canonical choice.

## References

* `StableRange.CategoryTheory.Cancellation`, for cancellation of one common
  summand with local endomorphism ring.
* `HomologicalAlgebra.Indecomposable.Biproducts`, for the finite-family append
  comparison.
* `HomologicalAlgebra.Preadditive.BiproductUniqueness`, for the finite-index
  shrinking and additive-envelope transport approach.
* Mathlib's biproduct and finite-tuple APIs, for associativity, reindexing and
  zero-summand comparisons, and Kim Morrison's additive envelope in
  `CategoryTheory.Preadditive.Mat`.

## Implementation notes

The finite-family induction uses finite biproducts in the additive envelope,
not in the original category. Before applying the embedding, the supplied
common biproduct is reindexed by `Fin n` in the original category, so the
finite-index universe is unrestricted. The fully faithful additive embedding
preserves the supplied sums and reflects the resulting residual isomorphism.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]

section FiniteBiproducts

variable [HasFiniteBiproducts C]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

private theorem cancel_finite_biproduct_of_isLocalRing_end_fin (n : ℕ) :
    ∀ (F : Fin n → C), (∀ i, IsLocalRing (End (F i))) →
      ∀ (Y Z : C), ((⨁ F) ⊞ Y ≅ (⨁ F) ⊞ Z) → Nonempty (Y ≅ Z) := by
  classical
  induction n with
  | zero =>
    intro F _ Y Z e
    have hzero : IsZero (⨁ F) := by
      apply (IsZero.iff_id_eq_zero _).2
      apply biproduct.hom_ext
      intro i
      exact Fin.elim0 i
    exact ⟨isoZeroBiprod (Y := Y) hzero ≪≫ e ≪≫ (isoZeroBiprod (Y := Z) hzero).symm⟩
  | succ n ih =>
    intro F hF Y Z e
    let A : C := F (Fin.last n)
    let G : Fin n → C := Fin.init F
    let T : C := ⨁ G
    let L : Fin 1 → C := fun _ => A
    have h : Fin.append G L = F := by
      simpa only [Fin.append_right_eq_snoc] using Fin.snoc_init_self F
    let s : A ⊞ T ≅ ⨁ F :=
      biprod.braiding' A T ≪≫
        biprod.mapIso (Iso.refl T) (biproductUniqueIso L).symm ≪≫
        biproductAppendIso G L ≪≫
        biproduct.mapIso (fun i => eqToIso (congrFun h i))
    let k (W : C) : (⨁ F) ⊞ W ≅ A ⊞ (T ⊞ W) :=
      biprod.mapIso s.symm (Iso.refl W) ≪≫ biprod.associator A T W
    let : IsLocalRing (End A) := hF (Fin.last n)
    obtain ⟨q⟩ := nonempty_iso_of_biprod_iso_of_isLocalRing_end A (T ⊞ Y) (T ⊞ Z)
      ((k Y).symm ≪≫ e ≪≫ k Z)
    exact ih G (fun i => hF i.castSucc) Y Z q

end FiniteBiproducts

/-- A common finite biproduct of objects with local canonical endomorphism rings
cancels from an isomorphism of binary biproducts with arbitrary remaining objects.
Only the common full biproduct and the two displayed binary biproducts are
required in the preadditive category. The index type may be empty. -/
theorem cancel_finite_biproduct_of_isLocalRing_end
    {ι : Type w} [Finite ι] (F : ι → C) [HasBiproduct F]
    [∀ i, IsLocalRing (End (F i))] (Y Z : C)
    [HasBinaryBiproduct (⨁ F) Y] [HasBinaryBiproduct (⨁ F) Z]
    (e : (⨁ F) ⊞ Y ≅ (⨁ F) ⊞ Z) : Nonempty (Y ≅ Z) := by
  classical
  obtain ⟨n, ⟨s⟩⟩ := Finite.exists_equiv_fin ι
  let Fs : Fin n → C := fun i => F (s.symm i)
  -- Shrink the supplied sum before using the additive envelope's Type-0 indices.
  let : HasProduct Fs :=
    hasProduct_of_equiv_of_iso F Fs s.symm (fun _ => Iso.refl _)
  let : HasBiproduct Fs := HasBiproduct.of_hasProduct Fs
  let p (i : ι) : Fs (s i) ≅ F i :=
    eqToIso (congrArg F (s.symm_apply_apply i))
  let c : (⨁ F) ≅ (⨁ Fs) := biproduct.whiskerEquiv s p
  let : ∀ i : Fin n, IsLocalRing (End (Fs i)) := fun i =>
    inferInstanceAs (IsLocalRing (End (F (s.symm i))))
  let E : C ⥤ Mat_ C := Mat_.embedding C
  let hf : E.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful E
  let endEquiv (X : C) : End X ≃+* End (E.obj X) :=
    MulEquiv.toRingEquiv (hf.mulEquivEnd X) (fun _ _ => E.map_add)
  have hFs : ∀ i : Fin n, IsLocalRing (End (E.obj (Fs i))) :=
    fun i => (endEquiv (Fs i)).isLocalRing
  let : HasBinaryBiproducts (Mat_ C) := hasBinaryBiproducts_of_finite_biproducts _
  let : PreservesBinaryBiproducts E :=
    preservesBinaryBiproducts_of_preservesBiproducts E
  let m : E.obj (⨁ Fs) ≅ (⨁ fun i : Fin n => E.obj (Fs i)) := E.mapBiproduct Fs
  let cMat : E.obj (⨁ F) ≅ (⨁ fun i : Fin n => E.obj (Fs i)) := E.mapIso c ≪≫ m
  let eMat : E.obj (⨁ F) ⊞ E.obj Y ≅ E.obj (⨁ F) ⊞ E.obj Z :=
    (E.mapBiprod (⨁ F) Y).symm ≪≫ E.mapIso e ≪≫ E.mapBiprod (⨁ F) Z
  let hMat : (⨁ fun i : Fin n => E.obj (Fs i)) ⊞ E.obj Y ≅
      (⨁ fun i : Fin n => E.obj (Fs i)) ⊞ E.obj Z :=
    (biprod.mapIso cMat (Iso.refl (E.obj Y))).symm ≪≫ eMat ≪≫
      biprod.mapIso cMat (Iso.refl (E.obj Z))
  obtain ⟨q⟩ := cancel_finite_biproduct_of_isLocalRing_end_fin
    (C := Mat_ C) n (fun i => E.obj (Fs i)) hFs (E.obj Y) (E.obj Z) hMat
  exact ⟨hf.preimageIso q⟩

end CategoryTheory
