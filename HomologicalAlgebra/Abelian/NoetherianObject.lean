/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.NoetherianObject

/-!
# Quotients of Noetherian objects

In an abelian category, inverse image along an epimorphism reflects the order on
subobjects. Consequently, an epimorphic image of a Noetherian object is Noetherian.
The Noetherian condition is Mathlib's ascending chain condition on `Subobject`.
-/

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] {X Y : C}

namespace Subobject

/-- Inverse image along an epimorphism in an abelian category reflects subobject inclusion. -/
lemma pullback_le_pullback_iff_of_epi (f : X ⟶ Y) [Epi f] (A B : Subobject Y) :
    (pullback f).obj A ≤ (pullback f).obj B ↔ A ≤ B := by
  constructor
  · intro h
    have : Epi (pullbackπ f A) :=
      Abelian.epi_fst_of_isLimit A.arrow f (isPullback f A).isLimit
    have : StrongEpi (pullbackπ f A) := strongEpi_of_epi _
    let sq : CommSq (ofLE _ _ h ≫ pullbackπ f B) (pullbackπ f A) B.arrow A.arrow :=
      ⟨by rw [Category.assoc, (isPullback f B).w, ← Category.assoc, ofLE_arrow,
        ← (isPullback f A).w]⟩
    exact le_of_comm sq.lift sq.fac_right
  · intro h
    exact (pullback f).monotone h

end Subobject

/-- An epimorphic image of a Noetherian object in an abelian category is Noetherian. -/
lemma isNoetherianObject_of_epi (p : X ⟶ Y) [Epi p] [IsNoetherianObject X] :
    IsNoetherianObject Y := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro f
  obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherianObject
    ⟨_, (Subobject.pullback p).monotone.comp f.2⟩
  refine ⟨n, fun m hm ↦ ?_⟩
  apply le_antisymm
  · exact (Subobject.pullback_le_pullback_iff_of_epi p _ _).1 (hn m hm).le
  · exact (Subobject.pullback_le_pullback_iff_of_epi p _ _).1 (hn m hm).ge

end CategoryTheory
