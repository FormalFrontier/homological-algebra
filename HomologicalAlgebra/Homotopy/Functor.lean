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
along a fully faithful additive functor. A supplied homotopy equivalence between
images of complexes pulls back to a homotopy equivalence with canonical preimage
maps and homotopies. Mapping and pulling back are inverse on all four fields,
including both supplied homotopies. These constructions reuse Mathlib's canonical
functor on complexes and its mapping and preimage operations on homotopies.

Mapping homotopies is injective already for faithful additive functors. The
existence equivalence specializes to reflection of identity-to-zero homotopies,
expressing contractibility without requiring a zero object in the ambient category.

## References

* Mathlib's `Algebra.Homology.Homotopy` and `Algebra.Homology.HomotopyCategory`,
  originally formalized by Kim Morrison.
-/

@[expose] public section

universe u₁ v₁ u₂ v₂ w

open CategoryTheory

namespace HomotopyEquiv

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {ι : Type w} {c : ComplexShape ι} {K L : HomologicalComplex C c}

/-- Homotopy equivalences are determined by their maps and both homotopy component families. -/
@[ext]
theorem ext {e₁ e₂ : HomotopyEquiv K L}
    (hom : e₁.hom = e₂.hom) (inv : e₁.inv = e₂.inv)
    (homotopyHomInvId : ∀ i j,
      e₁.homotopyHomInvId.hom i j = e₂.homotopyHomInvId.hom i j)
    (homotopyInvHomId : ∀ i j,
      e₁.homotopyInvHomId.hom i j = e₂.homotopyInvHomId.hom i j) : e₁ = e₂ := by
  cases e₁
  cases e₂
  cases hom
  cases inv
  congr 1
  · ext i j
    exact homotopyHomInvId i j
  · ext i j
    exact homotopyInvHomId i j

end HomotopyEquiv

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

private theorem homotopy_cast_hom {f₁ g₁ f₂ g₂ : K ⟶ L}
    (hf : f₁ = f₂) (hg : g₁ = g₂) (h : Homotopy f₁ g₁) (i j : ι) :
    (cast (congrArg₂ Homotopy hf hg) h).hom i j = h.hom i j := by
  cases hf
  cases hg
  rfl

/-- Mapping a homotopy equivalence maps each forward-inverse homotopy component. -/
theorem mapHomotopyEquiv_homotopyHomInvId_hom_eq_map (e : HomotopyEquiv K L) (i j : ι) :
    (F.mapHomotopyEquiv e).homotopyHomInvId.hom i j =
      F.map (e.homotopyHomInvId.hom i j) := by
  dsimp only [mapHomotopyEquiv]
  simpa only [mapHomotopy, eq_mpr_eq_cast, cast_cast] using
    homotopy_cast_hom ((F.mapHomologicalComplex c).map_comp e.hom e.inv)
      ((F.mapHomologicalComplex c).map_id K) (F.mapHomotopy e.homotopyHomInvId) i j

/-- Mapping a homotopy equivalence maps each inverse-forward homotopy component. -/
theorem mapHomotopyEquiv_homotopyInvHomId_hom_eq_map (e : HomotopyEquiv K L) (i j : ι) :
    (F.mapHomotopyEquiv e).homotopyInvHomId.hom i j =
      F.map (e.homotopyInvHomId.hom i j) := by
  dsimp only [mapHomotopyEquiv]
  simpa only [mapHomotopy, eq_mpr_eq_cast, cast_cast] using
    homotopy_cast_hom ((F.mapHomologicalComplex c).map_comp e.inv e.hom)
      ((F.mapHomologicalComplex c).map_id L) (F.mapHomotopy e.homotopyInvHomId) i j

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

/-- Pull a supplied homotopy equivalence back along a fully faithful additive functor.
The maps are the canonical preimages, and both homotopies are pulled back using
Mathlib's `Functor.preimageHomotopy`. -/
@[simps hom inv]
noncomputable def preimageHomotopyEquiv
    (e : HomotopyEquiv ((F.mapHomologicalComplex c).obj K)
      ((F.mapHomologicalComplex c).obj L)) : HomotopyEquiv K L where
  hom := (F.mapHomologicalComplex c).preimage e.hom
  inv := (F.mapHomologicalComplex c).preimage e.inv
  homotopyHomInvId := F.preimageHomotopy
    (((Homotopy.ofEq (by simp)).trans e.homotopyHomInvId).trans
      (Homotopy.ofEq (by simp)))
  homotopyInvHomId := F.preimageHomotopy
    (((Homotopy.ofEq (by simp)).trans e.homotopyInvHomId).trans
      (Homotopy.ofEq (by simp)))

private theorem mapHomologicalComplex_preimage_f
    (φ : (F.mapHomologicalComplex c).obj K ⟶ (F.mapHomologicalComplex c).obj L) (i : ι) :
    ((F.mapHomologicalComplex c).preimage φ).f i = F.preimage (φ.f i) := by
  apply F.map_injective
  calc
    F.map (((F.mapHomologicalComplex c).preimage φ).f i) = φ.f i :=
      congrArg (fun ψ => ψ.f i) ((F.mapHomologicalComplex c).map_preimage φ)
    _ = F.map (F.preimage (φ.f i)) := (F.map_preimage _).symm

/-- The forward map of a pulled-back homotopy equivalence is a preimage in each degree. -/
theorem preimageHomotopyEquiv_hom_f
    (e : HomotopyEquiv ((F.mapHomologicalComplex c).obj K)
      ((F.mapHomologicalComplex c).obj L)) (i : ι) :
    (F.preimageHomotopyEquiv e).hom.f i = F.preimage (e.hom.f i) := by
  simp only [preimageHomotopyEquiv_hom, mapHomologicalComplex_preimage_f]

/-- The inverse map of a pulled-back homotopy equivalence is a preimage in each degree. -/
theorem preimageHomotopyEquiv_inv_f
    (e : HomotopyEquiv ((F.mapHomologicalComplex c).obj K)
      ((F.mapHomologicalComplex c).obj L)) (i : ι) :
    (F.preimageHomotopyEquiv e).inv.f i = F.preimage (e.inv.f i) := by
  simp only [preimageHomotopyEquiv_inv, mapHomologicalComplex_preimage_f]

/-- Pullback preserves the supplied forward-inverse homotopy componentwise. -/
@[simp]
theorem preimageHomotopyEquiv_homotopyHomInvId_hom
    (e : HomotopyEquiv ((F.mapHomologicalComplex c).obj K)
      ((F.mapHomologicalComplex c).obj L)) (i j : ι) :
    (F.preimageHomotopyEquiv e).homotopyHomInvId.hom i j =
      F.preimage (e.homotopyHomInvId.hom i j) := by
  simp [preimageHomotopyEquiv, Homotopy.trans, Homotopy.ofEq]

/-- Pullback preserves the supplied inverse-forward homotopy componentwise. -/
@[simp]
theorem preimageHomotopyEquiv_homotopyInvHomId_hom
    (e : HomotopyEquiv ((F.mapHomologicalComplex c).obj K)
      ((F.mapHomologicalComplex c).obj L)) (i j : ι) :
    (F.preimageHomotopyEquiv e).homotopyInvHomId.hom i j =
      F.preimage (e.homotopyInvHomId.hom i j) := by
  simp [preimageHomotopyEquiv, Homotopy.trans, Homotopy.ofEq]

/-- Mapping a pulled-back homotopy equivalence recovers all of the supplied data. -/
@[simp]
theorem map_preimageHomotopyEquiv
    (e : HomotopyEquiv ((F.mapHomologicalComplex c).obj K)
      ((F.mapHomologicalComplex c).obj L)) :
    F.mapHomotopyEquiv (F.preimageHomotopyEquiv e) = e := by
  apply HomotopyEquiv.ext
  · exact (F.mapHomologicalComplex c).map_preimage e.hom
  · exact (F.mapHomologicalComplex c).map_preimage e.inv
  · intro i j
    simp only [mapHomotopyEquiv_homotopyHomInvId_hom_eq_map,
      preimageHomotopyEquiv_homotopyHomInvId_hom, map_preimage]
  · intro i j
    simp only [mapHomotopyEquiv_homotopyInvHomId_hom_eq_map,
      preimageHomotopyEquiv_homotopyInvHomId_hom, map_preimage]

/-- Pulling back a mapped homotopy equivalence recovers its maps and both homotopies. -/
@[simp]
theorem preimage_mapHomotopyEquiv (e : HomotopyEquiv K L) :
    F.preimageHomotopyEquiv (F.mapHomotopyEquiv e) = e := by
  apply HomotopyEquiv.ext
  · exact (F.mapHomologicalComplex c).preimage_map e.hom
  · exact (F.mapHomologicalComplex c).preimage_map e.inv
  · intro i j
    simp only [preimageHomotopyEquiv_homotopyHomInvId_hom,
      mapHomotopyEquiv_homotopyHomInvId_hom_eq_map, preimage_map]
  · intro i j
    simp only [preimageHomotopyEquiv_homotopyInvHomId_hom,
      mapHomotopyEquiv_homotopyInvHomId_hom_eq_map, preimage_map]

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
