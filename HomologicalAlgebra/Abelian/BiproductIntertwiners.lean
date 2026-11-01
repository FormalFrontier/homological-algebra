/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Abelian.EndomorphismPowers

/-!
# Intertwiners of binary biproduct endomorphisms

A binary biproduct map is invertible exactly when both of its component maps
are invertible. The biproduct of the resulting component isomorphisms
agrees with the isomorphism associated to the whole map. Only the two displayed
binary biproducts are required.

For block endomorphisms with nilpotent left components, an epimorphic right
source component and a monomorphic right target component, every intertwiner is
the biproduct map of its diagonal components. An invertible intertwiner gives
canonical isomorphisms between the original summands. Their inverses are the
diagonal components of the inverse intertwiner, and their biproduct recovers
the isomorphism associated to the intertwiner.

The category needs only zero morphisms, and its object and morphism universes
are independent.

## References

Mathlib's `CategoryTheory.Limits.Shapes.BinaryBiproducts` supplies the binary
biproduct maps and their isomorphism constructor. The local-pair equivalence
`biprod.isIso_map_iff` consolidates and generalizes
`CategoryTheory.isIso_left_of_isIso_biprod_map` and
`CategoryTheory.isIso_right_of_isIso_biprod_map`, which assume all binary
biproducts exist. `HomologicalAlgebra.Abelian.EndomorphismPowers` supplies the
nilpotent-to-monomorphic and epimorphic-to-nilpotent vanishing results.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace Limits.biprod

variable {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z]

/-- A binary biproduct map is invertible exactly when both component maps are
invertible, assuming only the two binary biproducts in its source and target. -/
theorem isIso_map_iff (f : W ⟶ Y) (g : X ⟶ Z) :
    IsIso (biprod.map f g) ↔ IsIso f ∧ IsIso g := by
  constructor
  · intro h
    have := h
    constructor
    · refine ⟨⟨(biprod.inl : Y ⟶ Y ⊞ Z) ≫ inv (biprod.map f g) ≫
        (biprod.fst : W ⊞ X ⟶ W), ?_, ?_⟩⟩
      · calc
          f ≫ ((biprod.inl : Y ⟶ Y ⊞ Z) ≫ inv (biprod.map f g) ≫
              (biprod.fst : W ⊞ X ⟶ W)) =
              (biprod.inl : W ⟶ W ⊞ X) ≫
                (biprod.map f g ≫ inv (biprod.map f g)) ≫
                  (biprod.fst : W ⊞ X ⟶ W) := by
                    simp only [Category.assoc, biprod.inl_map_assoc]
          _ = 𝟙 W := by
            simp only [IsIso.hom_inv_id, Category.id_comp, biprod.inl_fst]
      · calc
          ((biprod.inl : Y ⟶ Y ⊞ Z) ≫ inv (biprod.map f g) ≫
              (biprod.fst : W ⊞ X ⟶ W)) ≫ f =
              (biprod.inl : Y ⟶ Y ⊞ Z) ≫
                (inv (biprod.map f g) ≫ biprod.map f g) ≫
                  (biprod.fst : Y ⊞ Z ⟶ Y) := by
                    simp only [Category.assoc, biprod.map_fst]
          _ = 𝟙 Y := by
            simp only [IsIso.inv_hom_id, Category.id_comp, biprod.inl_fst]
    · refine ⟨⟨(biprod.inr : Z ⟶ Y ⊞ Z) ≫ inv (biprod.map f g) ≫
        (biprod.snd : W ⊞ X ⟶ X), ?_, ?_⟩⟩
      · calc
          g ≫ ((biprod.inr : Z ⟶ Y ⊞ Z) ≫ inv (biprod.map f g) ≫
              (biprod.snd : W ⊞ X ⟶ X)) =
              (biprod.inr : X ⟶ W ⊞ X) ≫
                (biprod.map f g ≫ inv (biprod.map f g)) ≫
                  (biprod.snd : W ⊞ X ⟶ X) := by
                    simp only [Category.assoc, biprod.inr_map_assoc]
          _ = 𝟙 X := by
            simp only [IsIso.hom_inv_id, Category.id_comp, biprod.inr_snd]
      · calc
          ((biprod.inr : Z ⟶ Y ⊞ Z) ≫ inv (biprod.map f g) ≫
              (biprod.snd : W ⊞ X ⟶ X)) ≫ g =
              (biprod.inr : Z ⟶ Y ⊞ Z) ≫
                (inv (biprod.map f g) ≫ biprod.map f g) ≫
                  (biprod.snd : Y ⊞ Z ⟶ Z) := by
                    simp only [Category.assoc, biprod.map_snd]
          _ = 𝟙 Z := by
            simp only [IsIso.inv_hom_id, Category.id_comp, biprod.inr_snd]
  · rintro ⟨hf, hg⟩
    have := hf
    have := hg
    simpa only [biprod.mapIso_hom, asIso_hom] using
      (inferInstance : IsIso (biprod.mapIso (asIso f) (asIso g)).hom)

/-- The biproduct of the canonical component isomorphisms of an invertible
biproduct map equals the isomorphism associated to that map. -/
theorem mapIso_asIso (f : W ⟶ Y) (g : X ⟶ Z) [IsIso (biprod.map f g)] :
    biprod.mapIso
        (@asIso C _ W Y f
          (((isIso_map_iff f g).mp (inferInstance : IsIso (biprod.map f g))).1))
        (@asIso C _ X Z g
          (((isIso_map_iff f g).mp (inferInstance : IsIso (biprod.map f g))).2)) =
      asIso (biprod.map f g) := by
  apply Iso.ext
  simp only [biprod.mapIso_hom, asIso_hom]

end Limits.biprod

namespace End

variable {N I Nprime Iprime : C}
  [HasBinaryBiproduct N I] [HasBinaryBiproduct Nprime Iprime]

/-- The component from the nilpotent source summand to the monomorphic target
summand of an intertwiner is zero. -/
theorem biprod_inl_comp_snd_eq_zero
    (n : End N) (i : End I) (nprime : End Nprime) (iprime : End Iprime)
    [Mono iprime] (p : N ⊞ I ⟶ Nprime ⊞ Iprime)
    (h : biprod.map n i ≫ p = p ≫ biprod.map nprime iprime)
    (hn : IsNilpotent n) :
    (biprod.inl : N ⟶ N ⊞ I) ≫ p ≫
      (biprod.snd : Nprime ⊞ Iprime ⟶ Iprime) = 0 := by
  refine eq_zero_of_isNilpotent_of_mono n iprime _ ?_ hn
  simpa only [Category.assoc, biprod.inl_map_assoc, biprod.map_snd] using
    congrArg (fun q : N ⊞ I ⟶ Nprime ⊞ Iprime =>
      (biprod.inl : N ⟶ N ⊞ I) ≫ q ≫
        (biprod.snd : Nprime ⊞ Iprime ⟶ Iprime)) h

/-- The component from the epimorphic source summand to the nilpotent target
summand of an intertwiner is zero. -/
theorem biprod_inr_comp_fst_eq_zero
    (n : End N) (i : End I) (nprime : End Nprime) (iprime : End Iprime)
    [Epi i] (p : N ⊞ I ⟶ Nprime ⊞ Iprime)
    (h : biprod.map n i ≫ p = p ≫ biprod.map nprime iprime)
    (hnprime : IsNilpotent nprime) :
    (biprod.inr : I ⟶ N ⊞ I) ≫ p ≫
      (biprod.fst : Nprime ⊞ Iprime ⟶ Nprime) = 0 := by
  refine eq_zero_of_epi_of_isNilpotent i nprime _ ?_ hnprime
  simpa only [Category.assoc, biprod.inr_map_assoc, biprod.map_fst] using
    congrArg (fun q : N ⊞ I ⟶ Nprime ⊞ Iprime =>
      (biprod.inr : I ⟶ N ⊞ I) ≫ q ≫
        (biprod.fst : Nprime ⊞ Iprime ⟶ Nprime)) h

/-- Every intertwiner between block endomorphisms with nilpotent left components,
an epimorphic right source component and a monomorphic right target component is
the biproduct map of its diagonal components. -/
theorem biprod_intertwiner_eq_map
    (n : End N) (i : End I) (nprime : End Nprime) (iprime : End Iprime)
    [Epi i] [Mono iprime] (p : N ⊞ I ⟶ Nprime ⊞ Iprime)
    (h : biprod.map n i ≫ p = p ≫ biprod.map nprime iprime)
    (hn : IsNilpotent n) (hnprime : IsNilpotent nprime) :
    p = biprod.map
      ((biprod.inl : N ⟶ N ⊞ I) ≫ p ≫ (biprod.fst : Nprime ⊞ Iprime ⟶ Nprime))
      ((biprod.inr : I ⟶ N ⊞ I) ≫ p ≫ (biprod.snd : Nprime ⊞ Iprime ⟶ Iprime)) := by
  apply biprod.hom_ext'
  · rw [biprod.inl_map]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.inl_fst, Category.comp_id]
    · simpa only [Category.assoc, biprod.inl_snd, comp_zero] using
        biprod_inl_comp_snd_eq_zero n i nprime iprime p h hn
  · rw [biprod.inr_map]
    apply biprod.hom_ext
    · simpa only [Category.assoc, biprod.inr_fst, comp_zero] using
        biprod_inr_comp_fst_eq_zero n i nprime iprime p h hnprime
    · simp only [Category.assoc, biprod.inr_snd, Category.comp_id]

/-- The canonical isomorphism between the nilpotent summands induced by an
invertible intertwiner of block endomorphisms. -/
noncomputable def biprodLeftIso
    (n : End N) (i : End I) (nprime : End Nprime) (iprime : End Iprime)
    [Epi i] [Mono iprime] (p : N ⊞ I ⟶ Nprime ⊞ Iprime) [IsIso p]
    (h : biprod.map n i ≫ p = p ≫ biprod.map nprime iprime)
    (hn : IsNilpotent n) (hnprime : IsNilpotent nprime) : N ≅ Nprime := by
  have hm : IsIso (biprod.map
      ((biprod.inl : N ⟶ N ⊞ I) ≫ p ≫ (biprod.fst : Nprime ⊞ Iprime ⟶ Nprime))
      ((biprod.inr : I ⟶ N ⊞ I) ≫ p ≫ (biprod.snd : Nprime ⊞ Iprime ⟶ Iprime))) := by
    rw [← biprod_intertwiner_eq_map n i nprime iprime p h hn hnprime]
    infer_instance
  letI : IsIso
      ((biprod.inl : N ⟶ N ⊞ I) ≫ p ≫ (biprod.fst : Nprime ⊞ Iprime ⟶ Nprime)) :=
    ((biprod.isIso_map_iff _ _).mp hm).1
  exact asIso
    ((biprod.inl : N ⟶ N ⊞ I) ≫ p ≫ (biprod.fst : Nprime ⊞ Iprime ⟶ Nprime))

/-- The canonical isomorphism between the right summands induced by an
invertible intertwiner with epimorphic right source and monomorphic right target
endomorphisms and nilpotent left endomorphisms. -/
noncomputable def biprodRightIso
    (n : End N) (i : End I) (nprime : End Nprime) (iprime : End Iprime)
    [Epi i] [Mono iprime] (p : N ⊞ I ⟶ Nprime ⊞ Iprime) [IsIso p]
    (h : biprod.map n i ≫ p = p ≫ biprod.map nprime iprime)
    (hn : IsNilpotent n) (hnprime : IsNilpotent nprime) : I ≅ Iprime := by
  have hm : IsIso (biprod.map
      ((biprod.inl : N ⟶ N ⊞ I) ≫ p ≫ (biprod.fst : Nprime ⊞ Iprime ⟶ Nprime))
      ((biprod.inr : I ⟶ N ⊞ I) ≫ p ≫ (biprod.snd : Nprime ⊞ Iprime ⟶ Iprime))) := by
    rw [← biprod_intertwiner_eq_map n i nprime iprime p h hn hnprime]
    infer_instance
  letI : IsIso
      ((biprod.inr : I ⟶ N ⊞ I) ≫ p ≫ (biprod.snd : Nprime ⊞ Iprime ⟶ Iprime)) :=
    ((biprod.isIso_map_iff _ _).mp hm).2
  exact asIso
    ((biprod.inr : I ⟶ N ⊞ I) ≫ p ≫ (biprod.snd : Nprime ⊞ Iprime ⟶ Iprime))

/-- The forward map of the left summand isomorphism is the left diagonal
component of the intertwiner. -/
@[simp]
theorem biprodLeftIso_hom
    (n : End N) (i : End I) (nprime : End Nprime) (iprime : End Iprime)
    [Epi i] [Mono iprime] (p : N ⊞ I ⟶ Nprime ⊞ Iprime) [IsIso p]
    (h : biprod.map n i ≫ p = p ≫ biprod.map nprime iprime)
    (hn : IsNilpotent n) (hnprime : IsNilpotent nprime) :
    (biprodLeftIso n i nprime iprime p h hn hnprime).hom =
      (biprod.inl : N ⟶ N ⊞ I) ≫ p ≫ (biprod.fst : Nprime ⊞ Iprime ⟶ Nprime) := by
  simp only [biprodLeftIso, asIso_hom]

/-- The forward map of the right summand isomorphism is the right diagonal
component of the intertwiner. -/
@[simp]
theorem biprodRightIso_hom
    (n : End N) (i : End I) (nprime : End Nprime) (iprime : End Iprime)
    [Epi i] [Mono iprime] (p : N ⊞ I ⟶ Nprime ⊞ Iprime) [IsIso p]
    (h : biprod.map n i ≫ p = p ≫ biprod.map nprime iprime)
    (hn : IsNilpotent n) (hnprime : IsNilpotent nprime) :
    (biprodRightIso n i nprime iprime p h hn hnprime).hom =
      (biprod.inr : I ⟶ N ⊞ I) ≫ p ≫ (biprod.snd : Nprime ⊞ Iprime ⟶ Iprime) := by
  simp only [biprodRightIso, asIso_hom]

/-- The biproduct of the two canonical summand isomorphisms equals the
isomorphism associated to the invertible intertwiner. -/
theorem biprod_mapIso_eq_asIso
    (n : End N) (i : End I) (nprime : End Nprime) (iprime : End Iprime)
    [Epi i] [Mono iprime] (p : N ⊞ I ⟶ Nprime ⊞ Iprime) [IsIso p]
    (h : biprod.map n i ≫ p = p ≫ biprod.map nprime iprime)
    (hn : IsNilpotent n) (hnprime : IsNilpotent nprime) :
    biprod.mapIso (biprodLeftIso n i nprime iprime p h hn hnprime)
        (biprodRightIso n i nprime iprime p h hn hnprime) = asIso p := by
  apply Iso.ext
  rw [biprod.mapIso_hom, biprodLeftIso_hom, biprodRightIso_hom, asIso_hom]
  exact (biprod_intertwiner_eq_map n i nprime iprime p h hn hnprime).symm

/-- The inverse of the left summand isomorphism is the left diagonal component
of the inverse intertwiner. -/
@[simp]
theorem biprodLeftIso_inv
    (n : End N) (i : End I) (nprime : End Nprime) (iprime : End Iprime)
    [Epi i] [Mono iprime] (p : N ⊞ I ⟶ Nprime ⊞ Iprime) [IsIso p]
    (h : biprod.map n i ≫ p = p ≫ biprod.map nprime iprime)
    (hn : IsNilpotent n) (hnprime : IsNilpotent nprime) :
    (biprodLeftIso n i nprime iprime p h hn hnprime).inv =
      (biprod.inl : Nprime ⟶ Nprime ⊞ Iprime) ≫ inv p ≫ (biprod.fst : N ⊞ I ⟶ N) := by
  have hinv := congrArg
    (fun e : N ⊞ I ≅ Nprime ⊞ Iprime =>
      (biprod.inl : Nprime ⟶ Nprime ⊞ Iprime) ≫ e.inv ≫ (biprod.fst : N ⊞ I ⟶ N))
    (biprod_mapIso_eq_asIso n i nprime iprime p h hn hnprime)
  simpa only [biprod.mapIso_inv, asIso_inv, Category.assoc, biprod.inl_map_assoc,
    biprod.inl_fst, Category.comp_id] using hinv

/-- The inverse of the right summand isomorphism is the right diagonal component
of the inverse intertwiner. -/
@[simp]
theorem biprodRightIso_inv
    (n : End N) (i : End I) (nprime : End Nprime) (iprime : End Iprime)
    [Epi i] [Mono iprime] (p : N ⊞ I ⟶ Nprime ⊞ Iprime) [IsIso p]
    (h : biprod.map n i ≫ p = p ≫ biprod.map nprime iprime)
    (hn : IsNilpotent n) (hnprime : IsNilpotent nprime) :
    (biprodRightIso n i nprime iprime p h hn hnprime).inv =
      (biprod.inr : Iprime ⟶ Nprime ⊞ Iprime) ≫ inv p ≫ (biprod.snd : N ⊞ I ⟶ I) := by
  have hinv := congrArg
    (fun e : N ⊞ I ≅ Nprime ⊞ Iprime =>
      (biprod.inr : Iprime ⟶ Nprime ⊞ Iprime) ≫ e.inv ≫ (biprod.snd : N ⊞ I ⟶ I))
    (biprod_mapIso_eq_asIso n i nprime iprime p h hn hnprime)
  simpa only [biprod.mapIso_inv, asIso_inv, Category.assoc, biprod.inr_map_assoc,
    biprod.inr_snd, Category.comp_id] using hinv

end End

end CategoryTheory
