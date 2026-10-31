/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Abelian.ArtinianObject
public import HomologicalAlgebra.Abelian.NoetherianObject
public import Mathlib.Order.Iterate

/-!
# Endomorphisms of Noetherian and Artinian objects

An epimorphic endomorphism of a Noetherian object in an abelian category is an
isomorphism. Dually, a monomorphic endomorphism of an Artinian object is an
isomorphism. Only the individual object is assumed Noetherian or Artinian.

The Noetherian proof stabilizes the ascending chain of iterated inverse images
of the zero subobject. Epimorphic pullback reflects inclusion, so the stabilized
chain implies that the first inverse image is already zero. This is the
categorical counterpart of the ascending-kernel argument for Noetherian modules
in Mathlib's `IsNoetherian.injective_of_surjective_endomorphism` and
`IsNoetherian.bijective_of_surjective_endomorphism`. The existing
`ModuleCat.isNoetherianObject_iff` in
`HomologicalAlgebra.ShortComplex.ModuleCatNoetherian` identifies the categorical
hypothesis with the module hypothesis over any ring.

## References

* Mathlib's `Mathlib.RingTheory.Noetherian.Orzech`, by Mario Carneiro and Kevin
  Buzzard, formalizes the module results and the ascending-kernel approach.
* Joël Riou's `Mathlib.CategoryTheory.Subobject.NoetherianObject` supplies the
  categorical ascending chain condition.
* Mathlib's subobject pullback and zero-factorization APIs and its balanced
  abelian-category structure supply the categorical cancellation steps.
-/

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] {X : C}

/-- An epimorphic endomorphism of a Noetherian object in an abelian category is
an isomorphism. This generalizes Mathlib's Noetherian-module endomorphism result
by the same ascending-kernel argument, expressed using subobject pullbacks. -/
theorem isIso_of_epi_of_isNoetherianObject [IsNoetherianObject X]
    (f : X ⟶ X) [Epi f] : IsIso f := by
  let P : Subobject X → Subobject X := (Subobject.pullback f).obj
  have hP : Monotone P := (Subobject.pullback f).monotone
  have hPinj : Function.Injective P := by
    intro A B h
    exact le_antisymm
      ((Subobject.pullback_le_pullback_iff_of_epi f A B).1 h.le)
      ((Subobject.pullback_le_pullback_iff_of_epi f B A).1 h.ge)
  let F : ℕ →o Subobject X :=
    ⟨fun n ↦ P^[n] ⊥, hP.monotone_iterate_of_le_map bot_le⟩
  obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherianObject F
  have hbot : P ⊥ = ⊥ := by
    apply hPinj.iterate n
    rw [← Function.iterate_succ_apply]
    exact (hn (n + 1) (Nat.le_succ n)).symm
  have : Mono f := Preadditive.mono_of_cancel_zero f fun g hg ↦ by
    have hfac := (Limits.pullback_factors_iff f (⊥ : Subobject X) g).2
      ((Subobject.bot_factors_iff_zero (g ≫ f)).2 hg)
    change (P ⊥).Factors g at hfac
    rw [hbot] at hfac
    exact (Subobject.bot_factors_iff_zero g).1 hfac
  exact isIso_of_mono_of_epi f

/-- A monomorphic endomorphism of an Artinian object in an abelian category is
an isomorphism, by applying the Noetherian result in the opposite category. -/
theorem isIso_of_mono_of_isArtinianObject [IsArtinianObject X]
    (f : X ⟶ X) [Mono f] : IsIso f := by
  have : IsNoetherianObject (Opposite.op X) :=
    (isArtinianObject_iff_isNoetherianObject_op X).1 inferInstance
  have : IsIso f.op := isIso_of_epi_of_isNoetherianObject f.op
  exact isIso_of_op f

end CategoryTheory
