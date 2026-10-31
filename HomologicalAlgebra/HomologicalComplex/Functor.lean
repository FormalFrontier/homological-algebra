/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Adjunctions on homological complexes

An adjunction between functors preserving zero morphisms induces an adjunction
between their canonical functors on homological complexes of any fixed shape.
Its unit, counit, and hom-set equivalence are computed degreewise. The construction
agrees with the adjunction underlying the corresponding lift of an equivalence.
-/

@[expose] public section

universe vC vD uC uD w

namespace CategoryTheory

open Limits

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  [HasZeroMorphisms C] [HasZeroMorphisms D] {ι : Type w}

namespace Adjunction

variable {F : C ⥤ D} {G : D ⥤ C}
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
  (adj : F ⊣ G) (c : ComplexShape ι)

/-- An adjunction between zero-preserving functors induces an adjunction between
their canonical functors on homological complexes. -/
def mapHomologicalComplex : F.mapHomologicalComplex c ⊣ G.mapHomologicalComplex c where
  unit := (Functor.mapHomologicalComplexIdIso C c).inv ≫
    adj.unit.mapHomologicalComplex c
  counit := adj.counit.mapHomologicalComplex c ≫
    (Functor.mapHomologicalComplexIdIso D c).hom
  left_triangle_components K := by
    apply HomologicalComplex.hom_ext
    intro i
    simp
  right_triangle_components L := by
    apply HomologicalComplex.hom_ext
    intro i
    simp

/-- The unit of the induced adjunction is the base unit in every degree. -/
@[simp]
theorem mapHomologicalComplex_unit_app_f (K : HomologicalComplex C c) (i : ι) :
    ((adj.mapHomologicalComplex c).unit.app K).f i = adj.unit.app (K.X i) := by
  simp [mapHomologicalComplex]

/-- The counit of the induced adjunction is the base counit in every degree. -/
@[simp]
theorem mapHomologicalComplex_counit_app_f (L : HomologicalComplex D c) (i : ι) :
    ((adj.mapHomologicalComplex c).counit.app L).f i = adj.counit.app (L.X i) := by
  simp [mapHomologicalComplex]

/-- Transposing a chain map applies the base hom-set equivalence in every degree. -/
@[simp]
theorem mapHomologicalComplex_homEquiv_apply_f
    (K : HomologicalComplex C c) (L : HomologicalComplex D c)
    (φ : (F.mapHomologicalComplex c).obj K ⟶ L) (i : ι) :
    (((adj.mapHomologicalComplex c).homEquiv K L) φ).f i =
      adj.homEquiv (K.X i) (L.X i) (φ.f i) := by
  simp [Adjunction.homEquiv_unit]

/-- Inverse transposition applies the inverse base hom-set equivalence in every degree. -/
@[simp]
theorem mapHomologicalComplex_homEquiv_symm_apply_f
    (K : HomologicalComplex C c) (L : HomologicalComplex D c)
    (ψ : K ⟶ (G.mapHomologicalComplex c).obj L) (i : ι) :
    (((adj.mapHomologicalComplex c).homEquiv K L).symm ψ).f i =
      (adj.homEquiv (K.X i) (L.X i)).symm (ψ.f i) := by
  simp [Adjunction.homEquiv_counit]

end Adjunction

namespace Equivalence

/-- Lifting an equivalence to homological complexes agrees with lifting its
underlying adjunction. -/
theorem mapHomologicalComplex_toAdjunction (e : C ≌ D)
    [e.functor.PreservesZeroMorphisms] (c : ComplexShape ι) :
    (e.mapHomologicalComplex c).toAdjunction =
      e.toAdjunction.mapHomologicalComplex c := by
  apply Adjunction.ext
  ext K i
  simp [Equivalence.mapHomologicalComplex, Equivalence.toAdjunction]

end Equivalence

end CategoryTheory
