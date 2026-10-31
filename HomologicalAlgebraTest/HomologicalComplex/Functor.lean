/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.HomologicalComplex.Functor

/-!
# Unique transposition of a supplied chain map

The hom-set equivalence on complexes assembles the degreewise transposes of a
supplied chain map, and its component formula characterizes the resulting chain map.
-/

@[expose] public section

universe vC vD uC uD w

open CategoryTheory CategoryTheory.Limits

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  [HasZeroMorphisms C] [HasZeroMorphisms D] {ι : Type w}
  {F : C ⥤ D} {G : D ⥤ C}
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]

example (adj : F ⊣ G) (c : ComplexShape ι)
    (K : HomologicalComplex C c) (L : HomologicalComplex D c)
    (φ : (F.mapHomologicalComplex c).obj K ⟶ L) :
    ∃! ψ : K ⟶ (G.mapHomologicalComplex c).obj L,
      ∀ i : ι, ψ.f i = adj.homEquiv (K.X i) (L.X i) (φ.f i) := by
  refine ⟨(adj.mapHomologicalComplex c).homEquiv K L φ, ?_, ?_⟩
  · intro i
    simp
  · intro ψ hψ
    apply HomologicalComplex.hom_ext
    intro i
    simpa only [Adjunction.mapHomologicalComplex_homEquiv_apply_f] using hψ i
