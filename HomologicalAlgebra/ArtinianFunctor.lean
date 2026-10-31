/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.CategoryTheory.Subobject.ArtinianObject

/-!
# Artinian objects and conservative functors

A functor preserving monomorphisms and reflecting isomorphisms reflects
Artinian objects. The proof uses Mathlib's characterization by eventually
constant chains in the opposite of the category of monomorphisms into an object.
The opposite is taken at the chain level; no abelian duality is needed.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- A conservative functor preserving monomorphisms reflects Artinian objects. -/
lemma isArtinianObject_of_obj (F : C ⥤ D)
    [F.PreservesMonomorphisms] [F.ReflectsIsomorphisms]
    (X : C) [IsArtinianObject (F.obj X)] : IsArtinianObject X := by
  let L : MonoOver X ⥤ MonoOver (F.obj X) :=
    MonoOver.lift (Over.post F) fun A ↦ by
      change Mono (F.map A.arrow)
      infer_instance
  apply (isArtinianObject_iff_isEventuallyConstant X).2
  intro G
  obtain ⟨n, hn⟩ :=
    (isEventuallyConstant_of_isArtinianObject (G ⋙ L.op)).exists_isEventuallyConstantFrom
  refine ⟨n, fun m α ↦ ?_⟩
  apply (isIso_unop_iff (G.map α)).1
  apply (MonoOver.isIso_iff_isIso_hom_left (G.map α).unop).2
  have h : IsIso ((G ⋙ L.op).map α).unop :=
    (isIso_unop_iff _).2 (hn α)
  have : IsIso (F.map (G.map α).unop.hom.left) :=
    (MonoOver.isIso_iff_isIso_hom_left _).1 h
  exact isIso_of_reflects_iso (G.map α).unop.hom.left F

end CategoryTheory.Functor
