/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Homotopies under fully faithful additive functors

The component and inverse identities below describe Mathlib's
`CategoryTheory.Functor.preimageHomotopy`, which pulls a specified homotopy back
along a fully faithful additive functor. Mapping homotopies is injective already
for faithful additive functors. The existence equivalence specializes to
reflection of identity-to-zero homotopies, expressing contractibility without
requiring a zero object in the ambient category.
-/

@[expose] public section

universe u₁ v₁ u₂ v₂ w

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  {ι : Type w} {c : ComplexShape ι}
  (F : C ⥤ D) [F.Additive]
  {K L : HomologicalComplex C c} {f g : K ⟶ L}

/-- A faithful additive functor maps homotopies injectively. -/
theorem mapHomotopy_injective [F.Faithful] :
    Function.Injective (F.mapHomotopy (f := f) (g := g)) := by
  intro h₁ h₂ e
  ext i j
  exact F.map_injective (congrArg (fun h => h.hom i j) e)

section FullyFaithful

variable [F.Full] [F.Faithful]

/-- Pulling back a homotopy pulls back each of its components. -/
@[simp]
theorem preimageHomotopy_hom
    (h : Homotopy ((F.mapHomologicalComplex c).map f)
      ((F.mapHomologicalComplex c).map g)) (i j : ι) :
    (F.preimageHomotopy h).hom i j = F.preimage (h.hom i j) := rfl

/-- Mapping the preimage of a specified homotopy recovers that homotopy. -/
@[simp]
theorem map_preimageHomotopy
    (h : Homotopy ((F.mapHomologicalComplex c).map f)
      ((F.mapHomologicalComplex c).map g)) :
    F.mapHomotopy (F.preimageHomotopy h) = h := by
  ext i j
  simp

/-- Pulling back the image of a homotopy recovers its original components. -/
@[simp]
theorem preimage_mapHomotopy (h : Homotopy f g) :
    F.preimageHomotopy (F.mapHomotopy h) = h := by
  ext i j
  simp

/-- Fully faithful additive functors preserve and reflect existence of homotopies. -/
theorem nonempty_homotopy_iff :
    Nonempty (Homotopy ((F.mapHomologicalComplex c).map f)
      ((F.mapHomologicalComplex c).map g)) ↔ Nonempty (Homotopy f g) :=
  ⟨fun ⟨h⟩ => ⟨F.preimageHomotopy h⟩, fun ⟨h⟩ => ⟨F.mapHomotopy h⟩⟩

/-- Fully faithful additive functors preserve and reflect contractibility,
expressed by an identity-to-zero homotopy. -/
theorem nonempty_homotopy_id_zero_iff (K : HomologicalComplex C c) :
    Nonempty (Homotopy (𝟙 ((F.mapHomologicalComplex c).obj K)) 0) ↔
      Nonempty (Homotopy (𝟙 K) 0) := by
  simpa only [Functor.map_id, Functor.map_zero] using
    (F.nonempty_homotopy_iff (f := 𝟙 K) (g := 0))

end FullyFaithful

end CategoryTheory.Functor
