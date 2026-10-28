/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# K-projectivity and K-injectivity under equivalences

An equivalence between abelian categories preserves and reflects K-projectivity
and K-injectivity of unrestricted integer cochain complexes. The functor on
complexes is `CategoryTheory.Functor.mapHomologicalComplex`. No separate
additivity assumption on the equivalence is needed: preservation of finite
products gives additivity.

The properties and the complex functor are Mathlib's existing definitions.
The object and morphism universes of the two categories are independent.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, §1, for the
  K-projective and K-injective framework.
* Mathlib's K-projective, K-injective, homotopy and equivalence APIs.
-/

@[expose] public section

universe u₁ v₁ u₂ v₂

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D]

private lemma acyclic_map (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [F.PreservesHomology] (A : CochainComplex C ℤ) (hA : A.Acyclic) :
    ((F.mapHomologicalComplex (.up ℤ)).obj A).Acyclic :=
  fun i => (hA i).map F

/-- A categorical equivalence sends K-projective integer cochain complexes to
K-projective complexes. -/
lemma IsKProjective.map (F : C ⥤ D) [F.IsEquivalence]
    (K : CochainComplex C ℤ) [K.IsKProjective] :
    IsKProjective ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  let : F.Additive := Functor.additive_of_preserves_binary_products F
  let E : CochainComplex C ℤ ≌ CochainComplex D ℤ :=
    F.asEquivalence.mapHomologicalComplex (.up ℤ)
  change IsKProjective (E.functor.obj K)
  constructor
  intro A f hA
  let g : K ⟶ E.inverse.obj A := E.toAdjunction.homEquiv K A f
  let ε : E.functor.obj (E.inverse.obj A) ⟶ A := E.toAdjunction.counit.app A
  obtain ⟨h⟩ := IsKProjective.nonempty_homotopy_zero g (acyclic_map F.inv A hA)
  have h' : Homotopy (E.functor.map g) (E.functor.map 0) := F.mapHomotopy h
  have hf : E.functor.map g ≫ ε = f := by
    simpa only [g, ε, Adjunction.homEquiv_counit] using
      (E.toAdjunction.homEquiv K A).symm_apply_apply f
  exact ⟨by simpa only [hf, Functor.map_zero, zero_comp] using h'.compRight ε⟩

/-- A categorical equivalence sends K-injective integer cochain complexes to
K-injective complexes. -/
lemma IsKInjective.map (F : C ⥤ D) [F.IsEquivalence]
    (K : CochainComplex C ℤ) [K.IsKInjective] :
    IsKInjective ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  let : F.Additive := Functor.additive_of_preserves_binary_products F
  let E : CochainComplex C ℤ ≌ CochainComplex D ℤ :=
    F.asEquivalence.mapHomologicalComplex (.up ℤ)
  change IsKInjective (E.functor.obj K)
  constructor
  intro A f hA
  let g : E.inverse.obj A ⟶ K := (E.symm.toAdjunction.homEquiv A K).symm f
  let η : A ⟶ E.functor.obj (E.inverse.obj A) := E.symm.toAdjunction.unit.app A
  obtain ⟨h⟩ := IsKInjective.nonempty_homotopy_zero g (acyclic_map F.inv A hA)
  have h' : Homotopy (E.functor.map g) (E.functor.map 0) := F.mapHomotopy h
  have hf : η ≫ E.functor.map g = f := by
    simpa only [g, η, Adjunction.homEquiv_unit, Equivalence.symm_inverse] using
      (E.symm.toAdjunction.homEquiv A K).apply_symm_apply f
  exact ⟨by simpa only [hf, Functor.map_zero, comp_zero] using h'.compLeft η⟩

/-- An equivalence of abelian categories preserves and reflects K-projectivity
of unrestricted integer cochain complexes. -/
lemma isKProjective_map_iff (F : C ⥤ D) [F.IsEquivalence]
    (K : CochainComplex C ℤ) :
    IsKProjective ((F.mapHomologicalComplex (.up ℤ)).obj K) ↔ IsKProjective K := by
  constructor
  · intro h
    let := h
    have h' : IsKProjective ((F.inv.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj K)) :=
      IsKProjective.map F.inv ((F.mapHomologicalComplex (.up ℤ)).obj K)
    exact (isKProjective_iff_of_iso
      ((F.asEquivalence.mapHomologicalComplex (.up ℤ)).unitIso.app K)).2 h'
  · intro h
    let := h
    exact IsKProjective.map F K

/-- An equivalence of abelian categories preserves and reflects K-injectivity
of unrestricted integer cochain complexes. -/
lemma isKInjective_map_iff (F : C ⥤ D) [F.IsEquivalence]
    (K : CochainComplex C ℤ) :
    IsKInjective ((F.mapHomologicalComplex (.up ℤ)).obj K) ↔ IsKInjective K := by
  constructor
  · intro h
    let := h
    have h' : IsKInjective ((F.inv.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj K)) :=
      IsKInjective.map F.inv ((F.mapHomologicalComplex (.up ℤ)).obj K)
    exact (isKInjective_iff_of_iso
      ((F.asEquivalence.mapHomologicalComplex (.up ℤ)).unitIso.app K)).2 h'
  · intro h
    let := h
    exact IsKInjective.map F K

end CochainComplex
