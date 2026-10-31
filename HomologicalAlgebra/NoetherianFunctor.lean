/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.CategoryTheory.Subobject.NoetherianObject

/-!
# Noetherian objects and conservative functors

A functor preserving monomorphisms and reflecting isomorphisms reflects
Noetherian objects. The proof uses Mathlib's characterization by eventually
constant chains of monomorphisms: transition maps become isomorphisms after
applying the functor, and hence were already isomorphisms.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- A conservative functor preserving monomorphisms reflects Noetherian objects. -/
lemma isNoetherianObject_of_obj (F : C ⥤ D)
    [F.PreservesMonomorphisms] [F.ReflectsIsomorphisms]
    (X : C) [IsNoetherianObject (F.obj X)] : IsNoetherianObject X := by
  let L : MonoOver X ⥤ MonoOver (F.obj X) :=
    MonoOver.lift (Over.post F) fun A ↦ by
      change Mono (F.map A.arrow)
      infer_instance
  apply (isNoetherianObject_iff_isEventuallyConstant X).2
  intro G
  obtain ⟨n, hn⟩ :=
    (isEventuallyConstant_of_isNoetherianObject (G ⋙ L)).exists_isEventuallyConstantFrom
  refine ⟨n, fun m α ↦ ?_⟩
  apply (MonoOver.isIso_iff_isIso_hom_left (G.map α)).2
  have : IsIso (F.map (G.map α).hom.left) :=
    (MonoOver.isIso_iff_isIso_hom_left ((G ⋙ L).map α)).1 (hn α)
  exact isIso_of_reflects_iso (G.map α).hom.left F

end CategoryTheory.Functor
