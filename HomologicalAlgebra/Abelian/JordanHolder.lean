/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Jack McKoen
-/
/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Abelian.ArtinianObject
public import HomologicalAlgebra.Abelian.Subobject
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Simple
public import Mathlib.Order.JordanHolder
public import Mathlib.Order.OrderIsoNat

/-!
# Composition series and Jordan–Hölder in abelian categories

The factors of a composition series of canonical subobjects are the cokernels of its
successive inclusions. Covering relations characterize simplicity of these quotient objects.
The second isomorphism theorem interprets the diamond transpositions generating
`JordanHolderLattice.Iso` as isomorphisms of quotient objects.

A Noetherian and Artinian object admits a composition series from bottom to top. For any two
given composition series with the same endpoints, the factors are isomorphic after a bijection
of their index sets. The latter statement does not require chain conditions or exhaustive
endpoints. Object and morphism universes are independent throughout.

## Main definitions and results

* `CompositionSeries.factorObject`: the cokernel of an adjacent subobject inclusion.
* `CategoryTheory.Abelian.Subobject.covBy_iff_cokernel_is_simple`: covers and simple quotients.
* `CategoryTheory.Abelian.Subobject.cokernelSupIsoCokernelInf`: the second isomorphism theorem.
* `CategoryTheory.exists_compositionSeries_of_isNoetherianObject_of_isArtinianObject`:
  existence with both endpoints and simple factors.
* `CompositionSeries.jordan_holder_factorObject`: equal lengths and isomorphic factors.

## References

The covering and quotient-object diamond constructions follow Jack McKoen's Mathlib
formalization at revision `5c12595541f246a31351ed23f0815dc008ae9461`, in
`Mathlib/CategoryTheory/Abelian/Subobject.lean` and
`Mathlib/CategoryTheory/Abelian/JordanHolder.lean`:
<https://github.com/leanprover-community/mathlib4/tree/5c12595541f246a31351ed23f0815dc008ae9461/Mathlib/CategoryTheory/Abelian>.
The covering characterization uses the existing `CategoryTheory.Simple` and
`simple_iff_subobject_isSimpleOrder` interfaces.
The subobject correspondence follows Markus Himmel and Jack McKoen's Mathlib formalization
at revision `76dc24934373394902ae98311c2b0f3b9e2b77a5`, as documented in
`HomologicalAlgebra.Abelian.Subobject`.
The finite-chain existence and Jordan–Hölder interfaces are those of Mathlib revision
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, in `Order/OrderIsoNat.lean` and
`Order/JordanHolder.lean`.

## Implementation notes

`CompositionSeries` is Mathlib's `RelSeries` for the canonical covering-valued
`JordanHolderLattice` instance induced by subobject modularity. No endpoint condition is built
into that type. In particular, a zero object has a length-zero series and an empty factor
family, not a simple zero factor. Quotients use `cokernel` of `Subobject.ofLE`; their projection
and universal property are the existing `cokernel.π` and `cokernel.desc` APIs.
-/

@[expose] public section

universe v u

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Abelian.Subobject

variable {C : Type u} [Category.{v} C] [Abelian C] {X : C}

/-- A subobject covers another precisely when their quotient object is simple.
This is the covering characterization in McKoen's Mathlib formalization, expressed using
`CategoryTheory.Simple`. -/
theorem covBy_iff_cokernel_is_simple {A B : Subobject X} (h : A ≤ B) :
    A ⋖ B ↔ Simple (cokernel (Subobject.ofLE A B h)) := by
  let e : cokernel (Subobject.ofLE A B h) ≅
      cokernel (Subobject.mk (Subobject.ofLE A B h)).arrow :=
    cokernel.mapIso _ _ (Subobject.underlyingIso _).symm (Iso.refl _) (by simp)
  calc
    A ⋖ B ↔ IsCoatom (⟨A, h⟩ : Set.Iic B) := covBy_iff_coatom_Iic h
    _ ↔ IsCoatom (Subobject.mk (Subobject.ofLE A B h)) :=
      ((Subobject.subobjectOrderIso B).symm.isCoatom_iff ⟨A, h⟩).symm
    _ ↔ Simple (cokernel (Subobject.mk (Subobject.ofLE A B h)).arrow) :=
      ((simple_iff_subobject_isSimpleOrder _).trans
        ((cokernelOrderIso _).isSimpleOrder_iff.trans
          Set.isSimpleOrder_Ici_iff_isCoatom)).symm
    _ ↔ Simple (cokernel (Subobject.ofLE A B h)) := (Simple.iff_of_iso e).symm

private theorem eq_zero_of_ofLE_sup_comp_eq_zero {T : C} (A B : Subobject X)
    (q : ((A ⊔ B : Subobject X) : C) ⟶ T)
    (hA : Subobject.ofLE A (A ⊔ B) le_sup_left ≫ q = 0)
    (hB : Subobject.ofLE B (A ⊔ B) le_sup_right ≫ q = 0) : q = 0 := by
  let U : Subobject X := Subobject.mk (kernel.ι q ≫ (A ⊔ B).arrow)
  have hAU : A ≤ U := by
    apply Subobject.le_mk_of_comm
      (kernel.lift q (Subobject.ofLE A (A ⊔ B) le_sup_left) hA)
    simp only [← Category.assoc, kernel.lift_ι, Subobject.ofLE_arrow]
  have hBU : B ≤ U := by
    apply Subobject.le_mk_of_comm
      (kernel.lift q (Subobject.ofLE B (A ⊔ B) le_sup_right) hB)
    simp only [← Category.assoc, kernel.lift_ι, Subobject.ofLE_arrow]
  have h : A ⊔ B ≤ U := sup_le hAU hBU
  let r : ((A ⊔ B : Subobject X) : C) ⟶ kernel q :=
    Subobject.ofLEMk (A ⊔ B) (kernel.ι q ≫ (A ⊔ B).arrow) h
  have hr : r ≫ kernel.ι q = 𝟙 _ := by
    apply (cancel_mono (A ⊔ B).arrow).mp
    simpa only [Category.assoc, Category.id_comp] using (Subobject.ofLEMk_comp h)
  calc
    q = (r ≫ kernel.ι q) ≫ q := by rw [hr, Category.id_comp]
    _ = 0 := by simp

/-- The second isomorphism theorem for subobjects: `(A ⊔ B)/A ≅ B/(A ⊓ B)`.
This is McKoen's `cokernelSupIsoCokernelInf` construction. -/
def cokernelSupIsoCokernelInf (A B : Subobject X) :
    cokernel (Subobject.ofLE A (A ⊔ B) le_sup_left) ≅
      cokernel (Subobject.ofLE (A ⊓ B) B inf_le_right) := by
  let i := Subobject.ofLE A (A ⊔ B) le_sup_left
  let j := Subobject.ofLE B (A ⊔ B) le_sup_right
  let a := Subobject.ofLE (A ⊓ B) A inf_le_left
  let b := Subobject.ofLE (A ⊓ B) B inf_le_right
  have sq : IsPullback b a j i := by
    let sq := Subobject.inf_isPullback A B
    exact (IsPullback.of_isLimit
      (PullbackCone.isLimitOfFactors A.arrow B.arrow (A ⊔ B).arrow
        i j (Subobject.ofLE_arrow le_sup_left) (Subobject.ofLE_arrow le_sup_right)
        sq.cone sq.isLimit)).flip
  let d := cokernel.map b i a j sq.w
  haveI : Mono d := Abelian.mono_cokernel_map_of_isPullback sq
  haveI : Epi (j ≫ cokernel.π i) :=
    Preadditive.epi_of_cancel_zero _ (fun {T} z hz ↦ by
      apply (cancel_epi (cokernel.π i)).mp
      rw [comp_zero]
      apply eq_zero_of_ofLE_sup_comp_eq_zero A B
      · simp [i]
      · simpa only [j, Category.assoc] using hz)
  haveI : Epi d := epi_of_epi_fac (show cokernel.π b ≫ d = j ≫ cokernel.π i by
    simp only [d, cokernel.map, cokernel.π_desc])
  haveI : IsIso d := isIso_of_regularMono_of_epi d (regularMonoOfMono d)
  exact (asIso d).symm

/-- The second-isomorphism comparison sends the quotient map from `B` to the quotient map
of `A ⊓ B ↪ B`. -/
@[reassoc (attr := simp)]
theorem ofLE_π_cokernelSupIsoCokernelInf_hom (A B : Subobject X) :
    Subobject.ofLE B (A ⊔ B) le_sup_right ≫
        cokernel.π (Subobject.ofLE A (A ⊔ B) le_sup_left) ≫
        (cokernelSupIsoCokernelInf A B).hom =
      cokernel.π (Subobject.ofLE (A ⊓ B) B inf_le_right) := by
  have hinv :
      cokernel.π (Subobject.ofLE (A ⊓ B) B inf_le_right) ≫
          (cokernelSupIsoCokernelInf A B).inv =
        Subobject.ofLE B (A ⊔ B) le_sup_right ≫
          cokernel.π (Subobject.ofLE A (A ⊔ B) le_sup_left) := by
    simp only [cokernelSupIsoCokernelInf, Iso.symm_inv, asIso_hom,
      cokernel.map, cokernel.π_desc]
  calc
    _ = (cokernel.π (Subobject.ofLE (A ⊓ B) B inf_le_right) ≫
        (cokernelSupIsoCokernelInf A B).inv) ≫
          (cokernelSupIsoCokernelInf A B).hom := by rw [hinv, Category.assoc]
    _ = _ := by simp

/-- The inverse second-isomorphism comparison has the corresponding quotient-map equation. -/
@[reassoc (attr := simp)]
theorem π_cokernelSupIsoCokernelInf_inv (A B : Subobject X) :
    cokernel.π (Subobject.ofLE (A ⊓ B) B inf_le_right) ≫
        (cokernelSupIsoCokernelInf A B).inv =
      Subobject.ofLE B (A ⊔ B) le_sup_right ≫
        cokernel.π (Subobject.ofLE A (A ⊔ B) le_sup_left) := by
  simp only [cokernelSupIsoCokernelInf, Iso.symm_inv, asIso_hom,
    cokernel.map, cokernel.π_desc]

end CategoryTheory.Abelian.Subobject

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] {X : C}

/-- The diamond-generated Jordan–Hölder relation between ordered pairs of subobjects implies
isomorphism of their quotient objects. This is the ordered-pair form of McKoen's
`Iso.cokernelIso` interpretation, using the existing `JordanHolderLattice.Iso.rel` eliminator. -/
theorem JordanHolderLattice.Iso.nonempty_cokernel_iso
    {A B A' B' : Subobject X}
    (h : _root_.JordanHolderLattice.Iso (A, B) (A', B')) (hAB : A ≤ B) (hAB' : A' ≤ B') :
    Nonempty (cokernel (Subobject.ofLE A B hAB) ≅
      cokernel (Subobject.ofLE A' B' hAB')) := by
  -- Interpret the relation on all pairs, including unordered endpoints.
  let Q (P : Subobject X × Subobject X) : C :=
    cokernel (Subobject.ofLE (P.1 ⊓ P.2) P.2 inf_le_right)
  let τ (U V : Subobject X) (hUV : U ≤ V) :
      Q (U, V) ≅ cokernel (Subobject.ofLE U V hUV) :=
    cokernel.mapIso _ _ (Subobject.isoOfEq _ _ (inf_eq_left.mpr hUV)) (Iso.refl _)
      (by
        apply (cancel_mono V.arrow).1
        simp only [Iso.refl_hom, Category.comp_id, Category.assoc,
          Subobject.isoOfEq_hom, Subobject.ofLE_arrow])
  have hQ : Nonempty (Q (A, B) ≅ Q (A', B')) := by
    refine _root_.JordanHolderLattice.Iso.rel
      (fun P P' ↦ Nonempty (Q P ≅ Q P')) ?_ ?_ ?_ ?_ h
    · exact ⟨Iso.refl _⟩
    · rintro P P' ⟨e⟩
      exact ⟨e.symm⟩
    · rintro P P' P'' ⟨e⟩ ⟨e'⟩
      exact ⟨e ≪≫ e'⟩
    · intro U V _
      exact ⟨τ U (U ⊔ V) le_sup_left ≪≫
        Abelian.Subobject.cokernelSupIsoCokernelInf U V ≪≫
        (τ (U ⊓ V) V inf_le_right).symm⟩
  obtain ⟨e⟩ := hQ
  exact ⟨(τ A B hAB).symm ≪≫ e ≪≫ τ A' B' hAB'⟩

end CategoryTheory

namespace CompositionSeries

variable {C : Type u} [Category.{v} C] [Abelian C] {X : C}

/-- The successive quotient object of a composition series of subobjects. -/
def factorObject (s : CompositionSeries (Subobject X)) (i : Fin s.length) : C :=
  cokernel (Subobject.ofLE (s i.castSucc) (s i.succ) (s.step i).le)

/-- A factor object is the cokernel of the indicated adjacent inclusion. -/
theorem factorObject_apply (s : CompositionSeries (Subobject X)) (i : Fin s.length) :
    factorObject s i =
      cokernel (Subobject.ofLE (s i.castSucc) (s i.succ) (s.step i).le) := by
  rfl

/-- The factor-object isomorphism induced by a commuting square of isomorphisms of
adjacent inclusions. This is the comparison provided by `cokernel.mapIso`. -/
def factorObjectIso {Y : C} (s : CompositionSeries (Subobject X))
    (t : CompositionSeries (Subobject Y)) (i : Fin s.length) (j : Fin t.length)
    (e₀ : (s i.castSucc : C) ≅ (t j.castSucc : C))
    (e₁ : (s i.succ : C) ≅ (t j.succ : C))
    (w : Subobject.ofLE (s i.castSucc) (s i.succ) (s.step i).le ≫ e₁.hom =
      e₀.hom ≫ Subobject.ofLE (t j.castSucc) (t j.succ) (t.step j).le) :
    factorObject s i ≅ factorObject t j := by
  exact cokernel.mapIso _ _ e₀ e₁ w

/-- Transport of factor objects commutes with the quotient projections. -/
-- The reassociated equation simplifies using this projection law.
@[simp, reassoc]
theorem π_factorObjectIso_hom {Y : C} (s : CompositionSeries (Subobject X))
    (t : CompositionSeries (Subobject Y)) (i : Fin s.length) (j : Fin t.length)
    (e₀ : (s i.castSucc : C) ≅ (t j.castSucc : C))
    (e₁ : (s i.succ : C) ≅ (t j.succ : C))
    (w : Subobject.ofLE (s i.castSucc) (s i.succ) (s.step i).le ≫ e₁.hom =
      e₀.hom ≫ Subobject.ofLE (t j.castSucc) (t j.succ) (t.step j).le) :
    cokernel.π (Subobject.ofLE (s i.castSucc) (s i.succ) (s.step i).le) ≫
        (factorObjectIso s t i j e₀ e₁ w).hom =
      e₁.hom ≫ cokernel.π (Subobject.ofLE (t j.castSucc) (t j.succ) (t.step j).le) := by
  simp only [factorObjectIso, cokernel.mapIso_hom, cokernel.map]
  exact cokernel.π_desc _ _ _

/-- Every factor of a composition series of subobjects in an abelian category is simple. -/
theorem simple_factorObject (s : CompositionSeries (Subobject X)) (i : Fin s.length) :
    Simple (factorObject s i) := by
  rw [factorObject_apply]
  exact (Abelian.Subobject.covBy_iff_cokernel_is_simple (s.step i).le).mp (s.step i)

/-- Jordan–Hölder for quotient objects: two composition series with the same head and last
have equal lengths and isomorphic factors after a bijection of the factor indices.
This interprets Mathlib's `CompositionSeries.jordan_holder` by categorical cokernel
isomorphisms, following McKoen's quotient-object diamond construction. -/
theorem jordan_holder_factorObject (s t : CompositionSeries (Subobject X))
    (hhead : s.head = t.head) (hlast : s.last = t.last) :
    s.length = t.length ∧
      ∃ e : Fin s.length ≃ Fin t.length,
        ∀ i, Nonempty (factorObject s i ≅ factorObject t (e i)) := by
  have h := s.jordan_holder t hhead hlast
  refine ⟨h.length_eq, ?_⟩
  obtain ⟨e, he⟩ := h
  refine ⟨e, fun i ↦ ?_⟩
  simpa only [factorObject_apply] using
    CategoryTheory.JordanHolderLattice.Iso.nonempty_cokernel_iso (he i)
      (s.step i).le (t.step (e i)).le

end CompositionSeries

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A Noetherian and Artinian object admits a composition series of subobjects from bottom
to top, with simple quotient objects. The chain comes from Mathlib's
`exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le`; both endpoint equalities are part
of the conclusion. -/
theorem exists_compositionSeries_of_isNoetherianObject_of_isArtinianObject (X : C)
    [IsNoetherianObject X] [IsArtinianObject X] :
    ∃ s : CompositionSeries (Subobject X),
      s.head = ⊥ ∧ s.last = ⊤ ∧ ∀ i, Simple (s.factorObject i) := by
  obtain ⟨f, hf, n, hn, hstep⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le
      (bot_le : (⊥ : Subobject X) ≤ ⊤)
  let s : CompositionSeries (Subobject X) :=
    ⟨n, fun i ↦ f i, fun i ↦ hstep i i.2⟩
  exact ⟨s, hf, hn, fun i ↦ s.simple_factorObject i⟩

end CategoryTheory
