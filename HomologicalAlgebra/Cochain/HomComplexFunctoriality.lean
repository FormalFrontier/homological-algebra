/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-!
# Precomposition and postcomposition on the Hom complex

For integer cochain complexes in a preadditive category, degree-zero
precomposition and postcomposition act on the product of component Hom groups.
The comparison with morphisms in the homotopy category uses the existing
`homologyAddEquiv` and `CohomologyClass.homAddEquiv` without changing their target.
In particular, the postcomposition arrow there is the quotient of the shifted
cochain map, not the shift of its quotient without a comparison isomorphism.

The cochain model, composition operations, and objectwise comparisons are due
to Joël Riou in Mathlib's `HomComplex`, `HomComplexShift`, and
`HomComplexCohomology` modules.
-/

@[expose] public section

open CategoryTheory Category

universe u v

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K K' K'' L L' L'' : CochainComplex C ℤ}

/-- Precomposition in the first variable and postcomposition in the second.
The degree objects are unrestricted product families of cochains. -/
noncomputable def prePostcomp (α : K' ⟶ K) (β : L ⟶ L') :
    HomComplex K L ⟶ HomComplex K' L' where
  f r := AddCommGrpCat.ofHom
    (AddMonoidHom.mk'
      (fun φ : Cochain K L r =>
        ((Cochain.ofHom α).comp φ (zero_add r)).comp
          (Cochain.ofHom β) (add_zero r))
      (by
        intro φ ψ
        rw [Cochain.comp_add, Cochain.add_comp]))
  comm' r s := by
    intro _hrs
    refine AddCommGrpCat.ext (fun (φ : Cochain K L r) => ?_)
    change δ r s
        (((Cochain.ofHom α).comp φ (zero_add r)).comp
          (Cochain.ofHom β) (add_zero r)) =
      ((Cochain.ofHom α).comp (δ r s φ) (zero_add s)).comp
        (Cochain.ofHom β) (add_zero s)
    rw [δ_comp_ofHom, δ_ofHom_comp]

/-- The degree operator is ordinary cochain composition on both sides. -/
lemma prePostcomp_f_apply (α : K' ⟶ K) (β : L ⟶ L') (r : ℤ)
    (φ : Cochain K L r) :
    (prePostcomp α β).f r φ =
      ((Cochain.ofHom α).comp φ (zero_add r)).comp
        (Cochain.ofHom β) (add_zero r) := rfl

/-- Degree-zero precomposition and postcomposition introduce no sign. -/
lemma prePostcomp_f_v (α : K' ⟶ K) (β : L ⟶ L') (r : ℤ)
    (φ : Cochain K L r) (p q : ℤ) (hpq : p + r = q) :
    ((prePostcomp α β).f r φ).v p q hpq = α.f p ≫ φ.v p q hpq ≫ β.f q := by
  simp only [prePostcomp_f_apply, Cochain.comp_zero_cochain_v,
    Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Category.assoc]

/-- The underlying additive homomorphism has the expected component formula. -/
lemma prePostcomp_f_hom_v (α : K' ⟶ K) (β : L ⟶ L') (r : ℤ)
    (φ : Cochain K L r) (p q : ℤ) (hpq : p + r = q) :
    (ConcreteCategory.hom ((prePostcomp α β).f r) φ).v p q hpq =
      α.f p ≫ φ.v p q hpq ≫ β.f q := by
  let m : Cochain K L r →+ Cochain K' L' r :=
    AddMonoidHom.mk'
      (fun ψ : Cochain K L r =>
        ((Cochain.ofHom α).comp ψ (zero_add r)).comp
          (Cochain.ofHom β) (add_zero r))
      (by
        intro ψ χ
        rw [Cochain.comp_add, Cochain.add_comp])
  have hm := congrArg
    (fun k : Cochain K L r →+ Cochain K' L' r => (k φ).v p q hpq)
    (ConcreteCategory.hom_ofHom (C := AddCommGrpCat)
      (X := (HomComplex K L).X r) (Y := (HomComplex K' L').X r) m)
  change (ConcreteCategory.hom ((prePostcomp α β).f r) φ).v p q hpq =
    (((Cochain.ofHom α).comp φ (zero_add r)).comp
      (Cochain.ofHom β) (add_zero r)).v p q hpq at hm
  rw [hm]
  simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Category.assoc]

/-- Identity maps act as the identity on the Hom complex. -/
lemma prePostcomp_id (K L : CochainComplex C ℤ) :
    prePostcomp (𝟙 K) (𝟙 L) = 𝟙 (HomComplex K L) := by
  apply HomologicalComplex.hom_ext
  intro r
  refine AddCommGrpCat.ext (fun (φ : Cochain K L r) => ?_)
  simp only [prePostcomp_f_apply, HomologicalComplex.id_f,
    Cochain.id_comp, Cochain.comp_id]
  exact (ConcreteCategory.id_apply
    (C := AddCommGrpCat) (X := (HomComplex K L).X r) φ).symm

/-- The first variable is contravariant and the second variable is covariant. -/
lemma prePostcomp_comp (α : K' ⟶ K) (β : L ⟶ L')
    (α' : K'' ⟶ K') (β' : L' ⟶ L'') :
    prePostcomp (α' ≫ α) (β ≫ β') = prePostcomp α β ≫ prePostcomp α' β' := by
  apply HomologicalComplex.hom_ext
  intro r
  refine AddCommGrpCat.ext (fun (φ : Cochain K L r) => ?_)
  simp only [HomologicalComplex.comp_f]
  have happ :
      ConcreteCategory.hom
        ((prePostcomp α β).f r ≫ (prePostcomp α' β').f r) φ =
      ConcreteCategory.hom ((prePostcomp α' β').f r)
        (ConcreteCategory.hom ((prePostcomp α β).f r) φ) :=
    ConcreteCategory.comp_apply (C := AddCommGrpCat)
      ((prePostcomp α β).f r) ((prePostcomp α' β').f r) φ
  rw [happ]
  apply Cochain.ext
  intro p q hpq
  have houter :
      (ConcreteCategory.hom ((prePostcomp α' β').f r)
        (ConcreteCategory.hom ((prePostcomp α β).f r) φ)).v p q hpq =
      α'.f p ≫
        (ConcreteCategory.hom ((prePostcomp α β).f r) φ).v p q hpq ≫ β'.f q :=
    prePostcomp_f_hom_v α' β' r
      (ConcreteCategory.hom ((prePostcomp α β).f r) φ) p q hpq
  have hinner :
      (ConcreteCategory.hom ((prePostcomp α β).f r) φ).v p q hpq =
      α.f p ≫ φ.v p q hpq ≫ β.f q :=
    prePostcomp_f_hom_v α β r φ p q hpq
  rw [houter, hinner]
  simp only [prePostcomp_f_hom_v, HomologicalComplex.comp_f, Category.assoc]

/-- Naturality of the homology-to-homotopy-category comparison, with target
`Q.obj (L⟦n⟧)`. -/
theorem homologyAddEquiv_naturality (α : K' ⟶ K) (β : L ⟶ L') (n : ℤ)
    (x : (HomComplex K L).homology n) :
    ((homologyAddEquiv K' L' n).trans
      (CohomologyClass.homAddEquiv (K := K') (L := L') (n := n)))
        (HomologicalComplex.homologyMap (prePostcomp α β) n x) =
      (HomotopyCategory.quotient C (.up ℤ)).map α ≫
        ((homologyAddEquiv K L n).trans
          (CohomologyClass.homAddEquiv (K := K) (L := L) (n := n))) x ≫
        (HomotopyCategory.quotient C (.up ℤ)).map (β⟦n⟧') := by
  classical
  let φ : (HomComplex K L).sc n ⟶ (HomComplex K' L').sc n :=
    (HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℤ) n).map
      (prePostcomp α β)
  let γ : ShortComplex.LeftHomologyMapData φ
      (leftHomologyData K L n) (leftHomologyData K' L' n) :=
    ShortComplex.leftHomologyMapData φ _ _
  have hK (z : Cocycle K L n) :
      γ.φK z = (z.precomp α).postcomp β := by
    apply Cocycle.ext
    exact ConcreteCategory.congr_hom γ.commi z
  have hH (z : Cocycle K L n) :
      γ.φH (CohomologyClass.mk z) =
        CohomologyClass.mk ((z.precomp α).postcomp β) := by
    have hc := ConcreteCategory.congr_hom γ.commπ z
    change γ.φH (CohomologyClass.mk z) =
      CohomologyClass.mk (γ.φK z) at hc
    exact hc.trans (congrArg CohomologyClass.mk (hK z))
  have hmap :
      homologyAddEquiv K' L' n
          (HomologicalComplex.homologyMap (prePostcomp α β) n x) =
        γ.φH (homologyAddEquiv K L n x) := by
    change (HomologicalComplex.homologyMap (prePostcomp α β) n ≫
        (leftHomologyData K' L' n).homologyIso.hom) x =
      ((leftHomologyData K L n).homologyIso.hom ≫ γ.φH) x
    exact ConcreteCategory.congr_hom γ.homologyMap_comm x
  obtain ⟨z, hz⟩ :=
    CohomologyClass.mk_surjective (homologyAddEquiv K L n x)
  change CohomologyClass.homAddEquiv
      (homologyAddEquiv K' L' n
        (HomologicalComplex.homologyMap (prePostcomp α β) n x)) =
    (HomotopyCategory.quotient C (.up ℤ)).map α ≫
      CohomologyClass.homAddEquiv (homologyAddEquiv K L n x) ≫
      (HomotopyCategory.quotient C (.up ℤ)).map (β⟦n⟧')
  rw [hmap, ← hz, hH]
  change CohomologyClass.toHom
      (CohomologyClass.mk ((z.precomp α).postcomp β)) =
    (HomotopyCategory.quotient C (.up ℤ)).map α ≫
      CohomologyClass.toHom (CohomologyClass.mk z) ≫
      (HomotopyCategory.quotient C (.up ℤ)).map (β⟦n⟧')
  simp only [CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_postcomp, Cocycle.equivHomShift_symm_precomp,
    Functor.map_comp, Category.assoc]

end CochainComplex.HomComplex
