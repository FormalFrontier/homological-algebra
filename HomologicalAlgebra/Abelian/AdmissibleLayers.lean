module

public import HomologicalAlgebra.Abelian.QuotientIntersection
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Category.GaloisConnection

@[expose] public section

/-!
# Admissible layers and their lower-cut reflector

An admissible layer is a nested pair of subobjects `L ≤ U` whose chosen quotient
`U/L` satisfies an object property. The order reverses the lower endpoint and
preserves the upper endpoint. If the property is stable under subobjects and
binary products, and `B/D` satisfies it, intersection with `D` at the lower
endpoint is left adjoint to inclusion of layers whose lower endpoint lies in `D`.

This API needs neither closure under quotients nor an admissibility assumption
on either endpoint. It covers only the lower-cut operation; it does not assert
an upper-cut construction or a comparison with layers in the object `D`.

Original Lean construction: Formalization Worker A; Prism repaired the proof,
exposed its exported data equations and authored the ordinary-import client.
This transfer into Homological Algebra preserves the accepted incubator
mathematical declarations and proofs unchanged. Destination-specific review,
both-root build and complete standard-axiom audit, and maintainer acceptance
are pending as of 2026-09-30.
-/

universe v u

namespace CategoryTheory

open Limits

/-- A nested pair of subobjects with an admissible chosen quotient. -/
structure AdmissibleLayer {C : Type u} [Category.{v} C] [Abelian C]
    (P : ObjectProperty C) (B : C) where
  lower : Subobject B
  upper : Subobject B
  lower_le_upper : lower ≤ upper
  admissible : P (cokernel (Subobject.ofLE lower upper lower_le_upper))

namespace AdmissibleLayer

variable {C : Type u} [Category.{v} C] [Abelian C] {B : C} {P : ObjectProperty C}

/-- Inclusion of layers: the lower endpoint moves backwards, and the upper
endpoint moves forwards. -/
instance : PartialOrder (AdmissibleLayer P B) where
  le x y := y.lower ≤ x.lower ∧ x.upper ≤ y.upper
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ hxy hyz := ⟨hyz.1.trans hxy.1, hxy.2.trans hyz.2⟩
  le_antisymm x y hxy hyx := by
    cases x with
    | mk xLower xUpper xLe xAdmissible =>
      cases y with
      | mk yLower yUpper yLe yAdmissible =>
        have hLower : xLower = yLower := le_antisymm hyx.1 hxy.1
        have hUpper : xUpper = yUpper := le_antisymm hxy.2 hyx.2
        cases hLower
        cases hUpper
        rfl

/-- The full subposet of layers whose lower endpoint is bounded by `D`. -/
abbrev LowerBounded (P : ObjectProperty C) (B : C) (D : Subobject B) :=
  {x : AdmissibleLayer P B // x.lower ≤ D}

/-- Forget the lower-endpoint bound, retaining the underlying layer. -/
def lowerInclusion (D : Subobject B) : LowerBounded P B D → AdmissibleLayer P B :=
  Subtype.val

/-- Inclusion preserves the inherited order, without closure assumptions on
`P` or an admissibility assumption on `B/D`. -/
theorem lowerInclusion_monotone (D : Subobject B) :
    Monotone (lowerInclusion (P := P) D) :=
  fun _ _ h => h

variable [P.IsClosedUnderSubobjects] [P.IsClosedUnderBinaryProducts]

/-- Intersect the lower endpoint with `D`. The actual quotient-pair map
embeds `U/(L ⊓ D)` into `(U/L) × (B/D)`, proving admissibility. -/
noncomputable def lowerCut (D : Subobject B) (hD : P (cokernel D.arrow))
    (x : AdmissibleLayer P B) : LowerBounded P B D :=
  ⟨{ lower := x.lower ⊓ D
     upper := x.upper
     lower_le_upper := (Subobject.inf_le_left x.lower D).trans x.lower_le_upper
     admissible :=
       P.prop_of_mono
         (Subobject.quotientIntersectionPair x.lower x.upper D x.lower_le_upper)
         (P.prop_prod _ _ x.admissible hD) },
   Subobject.inf_le_right x.lower D⟩

@[simp]
theorem lowerCut_lower (D : Subobject B) (hD : P (cokernel D.arrow))
    (x : AdmissibleLayer P B) : (lowerCut D hD x).val.lower = x.lower ⊓ D := rfl

@[simp]
theorem lowerCut_upper (D : Subobject B) (hD : P (cokernel D.arrow))
    (x : AdmissibleLayer P B) : (lowerCut D hD x).val.upper = x.upper := rfl

/-- The defining Galois equivalence: lowering the lower endpoint is left
adjoint, in the layer order, to including lower-bounded layers. -/
theorem lowerCut_galoisConnection (D : Subobject B) (hD : P (cokernel D.arrow)) :
    GaloisConnection (lowerCut (P := P) D hD) (lowerInclusion (P := P) D) := by
  intro x y
  change y.val.lower ≤ x.lower ⊓ D ∧ x.upper ≤ y.val.upper ↔
    y.val.lower ≤ x.lower ∧ x.upper ≤ y.val.upper
  constructor
  · intro h
    exact ⟨h.1.trans (Subobject.inf_le_left x.lower D), h.2⟩
  · intro h
    exact ⟨le_inf h.1 y.property, h.2⟩

/-- The lower-cut map is monotone in the layer order. -/
theorem lowerCut_monotone (D : Subobject B) (hD : P (cokernel D.arrow)) :
    Monotone (lowerCut (P := P) D hD) :=
  (lowerCut_galoisConnection (P := P) D hD).monotone_l

/-- The unit inequality, with the lower endpoint ordered contravariantly. -/
theorem le_lowerInclusion_lowerCut (D : Subobject B) (hD : P (cokernel D.arrow))
    (x : AdmissibleLayer P B) : x ≤ lowerInclusion D (lowerCut D hD x) :=
  (lowerCut_galoisConnection (P := P) D hD).le_u_l x

/-- Cutting a layer already bounded by `D` leaves it unchanged. This is the
reflector identity, not merely an unspecified counit comparison. -/
@[simp]
theorem lowerCut_lowerInclusion (D : Subobject B) (hD : P (cokernel D.arrow))
    (y : LowerBounded P B D) : lowerCut D hD (lowerInclusion D y) = y := by
  apply le_antisymm
  · exact (lowerCut_galoisConnection (P := P) D hD).l_u_le y
  · change y.val.lower ⊓ D ≤ y.val.lower ∧ y.val.upper ≤ y.val.upper
    exact ⟨Subobject.inf_le_left y.val.lower D, le_rfl⟩

/-- The reflector/inclusion adjunction on the thin categories of layers,
obtained from the native adjunction of a Galois connection. -/
noncomputable def lowerCutAdjunction (D : Subobject B) (hD : P (cokernel D.arrow)) :
    (lowerCut_galoisConnection (P := P) D hD).monotone_l.functor ⊣
      (lowerCut_galoisConnection (P := P) D hD).monotone_u.functor :=
  (lowerCut_galoisConnection (P := P) D hD).adjunction

end AdmissibleLayer
end CategoryTheory
