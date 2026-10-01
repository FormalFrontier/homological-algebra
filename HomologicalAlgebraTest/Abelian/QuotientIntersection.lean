/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import HomologicalAlgebra.Abelian.QuotientIntersection
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

public section

universe v u

namespace CategoryTheory.Subobject

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {B : C} (L U D : Subobject B) (h : L ≤ U)

private theorem chosen_first_component :
    quotientIntersectionPair L U D h ≫ prod.fst =
      cokernel.map (ofLE (L ⊓ D) U ((inf_le_left L D).trans h)) (ofLE L U h)
        (ofLE (L ⊓ D) L (inf_le_left L D)) (𝟙 _)
        (by simp [ofLE_comp_ofLE]) := by
  exact quotientIntersectionPair_fst L U D h

private theorem chosen_second_component :
    quotientIntersectionPair L U D h ≫ prod.snd =
      cokernel.map (ofLE (L ⊓ D) U ((inf_le_left L D).trans h)) D.arrow
        (ofLE (L ⊓ D) D (inf_le_right L D)) U.arrow
        (by simp [ofLE_arrow]) := by
  exact quotientIntersectionPair_snd L U D h

private theorem aggregate_and_monicity :
    cokernel.π (ofLE (L ⊓ D) U ((inf_le_left L D).trans h)) ≫
      quotientIntersectionPair L U D h =
        prod.lift (cokernel.π (ofLE L U h)) (U.arrow ≫ cokernel.π D.arrow) := by
  have : Mono (quotientIntersectionPair L U D h) := inferInstance
  exact quotientIntersectionPair_fac L U D h

private theorem property_of_two_quotients
    (P : ObjectProperty C) [P.IsClosedUnderSubobjects]
    [P.IsClosedUnderBinaryProducts]
    (hL : P (cokernel (ofLE L U h))) (hD : P (cokernel D.arrow)) :
    P (cokernel (ofLE (L ⊓ D) U ((inf_le_left L D).trans h))) := by
  exact P.prop_of_mono (quotientIntersectionPair L U D h)
    (P.prop_prod _ _ hL hD)

private theorem top_boundary (L U : Subobject B) (h : L ≤ U) :
    Mono (quotientIntersectionPair L U (⊤ : Subobject B) h) := inferInstance

private theorem bot_boundary (L U : Subobject B) (h : L ≤ U) :
    Mono (quotientIntersectionPair L U (⊥ : Subobject B) h) := inferInstance

private theorem bottom_left_boundary (U D : Subobject B) :
    Mono (quotientIntersectionPair (⊥ : Subobject B) U D bot_le) := inferInstance

private theorem equal_left_boundary (U D : Subobject B) :
    Mono (quotientIntersectionPair U U D le_rfl) := inferInstance

private theorem zero_ambient_boundary (L U D : Subobject (⊥_ C)) (h : L ≤ U) :
    Mono (quotientIntersectionPair L U D h) := inferInstance

private theorem representative_transport (D : Subobject B) :
    IsIso ((cokernel.mapIso D.arrow (Subobject.mk D.arrow).arrow
      (Subobject.underlyingIso D.arrow).symm (Iso.refl B)
      (by simp)).hom) := by
  infer_instance

end CategoryTheory.Subobject
