/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import HomologicalAlgebra.ShortComplex.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Noetherian homology of module short complexes

Mathlib's order isomorphism `ModuleCat.subobjectModule` identifies Noetherian
objects in the category of modules with Noetherian modules. Thus homology is a
Noetherian module whenever the middle term is, over an arbitrary ring.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace ModuleCat

/-- A module is a Noetherian object exactly when it is Noetherian as a module. -/
lemma isNoetherianObject_iff {R : Type u} [Ring R] (M : ModuleCat.{v} R) :
    IsNoetherianObject M ↔ IsNoetherian R M := by
  dsimp only [IsNoetherianObject]
  rw [ObjectProperty.is_iff, isNoetherianObject, isNoetherian_iff']
  constructor
  · intro h
    have := h
    exact (subobjectModule M).symm.strictMono.wellFoundedGT
  · intro h
    have := h
    exact (subobjectModule M).strictMono.wellFoundedGT

end ModuleCat

namespace CategoryTheory.ShortComplex

/-- Homology is a Noetherian module if the middle term is Noetherian over the ring. -/
lemma isNoetherian_homology_moduleCat {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{v} R)) [IsNoetherian R S.X₂] :
    IsNoetherian R S.homology := by
  have : IsNoetherianObject S.X₂ :=
    (ModuleCat.isNoetherianObject_iff S.X₂).2 inferInstance
  exact (ModuleCat.isNoetherianObject_iff S.homology).1 (isNoetherianObject_homology S)

end CategoryTheory.ShortComplex
