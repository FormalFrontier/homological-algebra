/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-!
# Functoriality, homotopy, and contractibility of the Hom complex

For integer cochain complexes in a preadditive category, degree-zero
precomposition and postcomposition act on the product of component Hom groups.
Homotopies in both variables induce a dataful homotopy of these maps, telescoping
first in the source at the initial postcomposition map and then in the target at
the final precomposition map. The explicit degree-minus-one operator has a sign
only in its first summand. A contraction in either variable therefore gives a
contraction of the Hom complex, and hence acyclicity in every integer degree.
These constructions require no boundedness or additional hypotheses on the
input category; the Hom complex takes values in `AddCommGrpCat`.

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

/-- Zero precomposition induces the zero map of Hom complexes. -/
lemma prePostcomp_zero_left (β : L ⟶ L') :
    prePostcomp (0 : K' ⟶ K) β = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  refine AddCommGrpCat.ext (fun (φ : Cochain K L n) => ?_)
  change (((Cochain.ofHom (0 : K' ⟶ K)).comp φ (zero_add n)).comp
    (Cochain.ofHom β) (add_zero n)) = 0
  simp only [Cochain.ofHom_zero, Cochain.zero_comp]

/-- Zero postcomposition induces the zero map of Hom complexes. -/
lemma prePostcomp_zero_right (α : K' ⟶ K) :
    prePostcomp α (0 : L ⟶ L') = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  refine AddCommGrpCat.ext (fun (φ : Cochain K L n) => ?_)
  change (((Cochain.ofHom α).comp φ (zero_add n)).comp
    (Cochain.ofHom (0 : L ⟶ L')) (add_zero n)) = 0
  simp only [Cochain.ofHom_zero, Cochain.comp_zero]

/-- The joint homotopy on the Hom complex, telescoping first in the source
at `β0` and then in the target at `α1`. Its first summand has sign `(-1)^n`. -/
noncomputable def prePostcompHomotopy
    {α0 α1 : K' ⟶ K} {β0 β1 : L ⟶ L'}
    (hα : Homotopy α0 α1) (hβ : Homotopy β0 β1) :
    Homotopy (prePostcomp α0 β0) (prePostcomp α1 β1) := by
  classical
  let homotopyCochain
      (n : ℤ) (φ : Cochain K L n) : Cochain K' L' (n - 1) :=
    n.negOnePow •
      (((Cochain.ofHomotopy hα).comp φ (by omega)).comp
        (Cochain.ofHom β0) (add_zero (n - 1))) +
    (Cochain.ofHom α1).comp
      (φ.comp (Cochain.ofHomotopy hβ) (by omega)) (zero_add (n - 1))
  have homotopyCochain_comm
      (n : ℤ) (φ : Cochain K L n) :
      δ (n - 1) n (homotopyCochain n φ) +
          ((show (n + 1) - 1 = n by omega) ▸
            homotopyCochain (n + 1) (δ n (n + 1) φ)) =
        (prePostcomp α0 β0).f n φ - (prePostcomp α1 β1).f n φ := by
    -- Eliminate the index transport before doing cochain algebra. This is
    -- only equality elimination, and leaves all composition proofs irrelevant.
    have transport (r s : ℤ) (hrs : r - 1 = s) (ψ : Cochain K L r) :
        (hrs ▸ homotopyCochain r ψ) =
          r.negOnePow •
            (((Cochain.ofHomotopy hα).comp ψ (by omega)).comp
              (Cochain.ofHom β0) (add_zero s)) +
          (Cochain.ofHom α1).comp
            (ψ.comp (Cochain.ofHomotopy hβ) (by omega)) (zero_add s) := by
      subst s
      rfl
    rw [transport (n + 1) n (by omega)]
    dsimp only [homotopyCochain]
    rw [δ_add, δ_units_smul, δ_comp_ofHom, δ_ofHom_comp]
    -- The sign in δ_comp is the degree of the SECOND factor.
    rw [δ_comp (Cochain.ofHomotopy hα) φ (by omega)
        0 (n + 1) n (by omega) (by omega) rfl,
      δ_comp φ (Cochain.ofHomotopy hβ) (by omega)
        (n + 1) 0 n (by omega) rfl (by omega)]
    have hsq : n.negOnePow * n.negOnePow = (1 : ℤˣ) := by
      rw [← Int.negOnePow_add, ← two_mul, Int.negOnePow_two_mul]
    have hsqZ : (n.negOnePow : ℤ) * (n.negOnePow : ℤ) = 1 :=
      congrArg (fun a : ℤˣ => (a : ℤ)) hsq
    have hnextZ : ((n + 1).negOnePow : ℤ) = -(n.negOnePow : ℤ) := by
      rw [Int.negOnePow_succ]
      rfl
    -- Expand the unit action to the canonical integer action: no ambient
    -- Linear or Ring hypothesis on C is introduced.
    simp only [δ_ofHomotopy, prePostcomp_f_apply, Int.negOnePow_neg, Int.negOnePow_one,
      Units.smul_def, Units.coe_neg_one, Cochain.add_comp, Cochain.sub_comp,
      Cochain.comp_add, Cochain.comp_sub, Cochain.comp_neg,
      Cochain.smul_comp, smul_add, smul_sub, smul_smul,
      hsqZ, hnextZ, neg_smul, one_smul,
      Cochain.comp_assoc_of_first_is_zero_cochain]
    abel
  let H : ∀ n m : ℤ, AddCommGrpCat.of (Cochain K L n) ⟶
      AddCommGrpCat.of (Cochain K' L' m) :=
    fun n m => if h : m + 1 = n then by
      have hm : m = n - 1 := by omega
      subst m
      exact AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (homotopyCochain n) (by
          intro φ ψ
          simp only [homotopyCochain, Cochain.comp_add, Cochain.add_comp, smul_add]
          abel))
    else 0
  have H_apply (n m : ℤ) (h : m + 1 = n) (φ : Cochain K L n) :
      H n m φ =
        ((by omega : n - 1 = m) ▸ homotopyCochain n φ) := by
    have hm : m = n - 1 := by omega
    subst m
    dsimp only [H]
    rw [dite_eq_left (by omega)]
    rfl
  refine { hom := H, zero := ?_, comm := ?_ }
  · intro n m h
    change ¬ m + 1 = n at h
    dsimp only [H]
    exact dite_eq_right h
  · intro n
    erw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) by rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n by
        change n - 1 + 1 = n
        omega)]
    refine AddCommGrpCat.ext (fun (φ : Cochain K L n) => ?_)
    let ψ0 : Cochain K' L' n := (prePostcomp α0 β0).f n φ
    let ψ1 : Cochain K' L' n := (prePostcomp α1 β1).f n φ
    change ψ0 =
      H (n + 1) n (δ n (n + 1) φ) +
        δ (n - 1) n (H n (n - 1) φ) + ψ1
    rw [H_apply (n + 1) n (by omega), H_apply n (n - 1) (by omega)]
    simpa only [add_comm] using
      (sub_eq_iff_eq_add.mp (homotopyCochain_comm n φ).symm)

/-- The canonical related-degree operator of the joint homotopy. -/
lemma prePostcompHomotopy_hom_apply
    {α0 α1 : K' ⟶ K} {β0 β1 : L ⟶ L'}
    (hα : Homotopy α0 α1) (hβ : Homotopy β0 β1)
    (n : ℤ) (φ : Cochain K L n) :
    (prePostcompHomotopy hα hβ).hom n (n - 1) φ =
      n.negOnePow •
        (((Cochain.ofHomotopy hα).comp φ (by omega)).comp
          (Cochain.ofHom β0) (add_zero (n - 1))) +
      (Cochain.ofHom α1).comp
        (φ.comp (Cochain.ofHomotopy hβ) (by omega))
        (zero_add (n - 1)) := by
  dsimp only [prePostcompHomotopy]
  rw [dite_eq_left (by omega)]
  rfl

/-- The component formula fixes the first-then-second telescoping choice. -/
lemma prePostcompHomotopy_hom_v
    {α0 α1 : K' ⟶ K} {β0 β1 : L ⟶ L'}
    (hα : Homotopy α0 α1) (hβ : Homotopy β0 β1)
    (n : ℤ) (φ : Cochain K L n)
    (p q : ℤ) (hpq : p + (n - 1) = q) :
    ((prePostcompHomotopy hα hβ).hom n (n - 1) φ).v p q hpq =
      n.negOnePow •
        (hα.hom p (p - 1) ≫ φ.v (p - 1) q (by omega) ≫ β0.f q) +
      α1.f p ≫ φ.v p (q + 1) (by omega) ≫ hβ.hom (q + 1) q := by
  rw [prePostcompHomotopy_hom_apply]
  simp only [Cochain.add_v, Units.smul_def, Cochain.smul_v,
    Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  rw [Cochain.comp_v (Cochain.ofHomotopy hα) φ (by omega)
      p (p - 1) q (by omega) (by omega),
    Cochain.comp_v φ (Cochain.ofHomotopy hβ) (by omega)
      p (q + 1) q (by omega) (by omega)]
  simp only [Cochain.ofHomotopy, Cochain.mk_v, Category.assoc]

open CategoryTheory CategoryTheory.Limits

/-- A contraction of the first variable gives a specified contraction of the
Hom complex, with the input-degree sign in its degree operator. -/
noncomputable def homotopyToZeroOfLeft
    (hK : Homotopy (𝟙 K) (0 : K ⟶ K)) :
    Homotopy (𝟙 (HomComplex K L)) 0 := by
  let h := prePostcompHomotopy hK (Homotopy.refl (𝟙 L))
  refine { hom := h.hom, zero := h.zero, comm := ?_ }
  intro n
  simpa only [← prePostcomp_id K L, ← prePostcomp_zero_left (𝟙 L)] using h.comm n

/-- A contraction of the second variable gives a specified contraction of the
Hom complex, with no sign in its degree operator. -/
noncomputable def homotopyToZeroOfRight
    (hL : Homotopy (𝟙 L) (0 : L ⟶ L)) :
    Homotopy (𝟙 (HomComplex K L)) 0 := by
  let h := prePostcompHomotopy (Homotopy.refl (𝟙 K)) hL
  refine { hom := h.hom, zero := h.zero, comm := ?_ }
  intro n
  simpa only [← prePostcomp_id K L, ← prePostcomp_zero_right (𝟙 K)] using h.comm n

/-- The contraction induced from the first variable has the input-degree sign. -/
@[simp]
lemma homotopyToZeroOfLeft_hom_v
    (hK : Homotopy (𝟙 K) (0 : K ⟶ K))
    (n : ℤ) (φ : Cochain K L n)
    (p q : ℤ) (hpq : p + (n - 1) = q) :
    ((homotopyToZeroOfLeft (L := L) hK).hom n (n - 1) φ).v p q hpq =
      n.negOnePow • (hK.hom p (p - 1) ≫ φ.v (p - 1) q (by omega)) := by
  change ((prePostcompHomotopy hK (Homotopy.refl (𝟙 L))).hom
    n (n - 1) φ).v p q hpq = _
  rw [prePostcompHomotopy_hom_v]
  simp only [HomologicalComplex.id_f, HomologicalComplex.zero_f,
    Category.comp_id, CategoryTheory.Limits.zero_comp, add_zero]

/-- The contraction induced from the second variable has no degree sign. -/
@[simp]
lemma homotopyToZeroOfRight_hom_v
    (hL : Homotopy (𝟙 L) (0 : L ⟶ L))
    (n : ℤ) (φ : Cochain K L n)
    (p q : ℤ) (hpq : p + (n - 1) = q) :
    ((homotopyToZeroOfRight (K := K) hL).hom n (n - 1) φ).v p q hpq =
      φ.v p (q + 1) (by omega) ≫ hL.hom (q + 1) q := by
  change ((prePostcompHomotopy (Homotopy.refl (𝟙 K)) hL).hom
    n (n - 1) φ).v p q hpq = _
  have hrefl : (Homotopy.refl (𝟙 K)).hom p (p - 1) = 0 := rfl
  rw [prePostcompHomotopy_hom_v, hrefl]
  simp only [HomologicalComplex.id_f, Category.id_comp,
    CategoryTheory.Limits.zero_comp, smul_zero, zero_add]

/-- In the output category, a specified contraction kills homology in every
integer degree, hence gives acyclicity. -/
private lemma acyclic_of_contraction
    (M : CochainComplex AddCommGrpCat.{v} ℤ)
    (hM : Homotopy (𝟙 M) (0 : M ⟶ M)) : M.Acyclic := by
  intro n
  apply (HomologicalComplex.exactAt_iff_isZero_homology M n).2
  apply (IsZero.iff_id_eq_zero (M.homology n)).2
  simpa only [HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_zero] using hM.homologyMap_eq n

/-- Contractibility of the first variable makes the Hom complex acyclic in
all integer degrees; no homology assumptions on the input category are needed. -/
lemma acyclic_of_homotopy_id_zero_left
    (hK : Homotopy (𝟙 K) (0 : K ⟶ K)) :
    (HomComplex K L).Acyclic :=
  acyclic_of_contraction (HomComplex K L) (homotopyToZeroOfLeft hK)

/-- Contractibility of the second variable makes the Hom complex acyclic in
all integer degrees; no homology assumptions on the input category are needed. -/
lemma acyclic_of_homotopy_id_zero_right
    (hL : Homotopy (𝟙 L) (0 : L ⟶ L)) :
    (HomComplex K L).Acyclic :=
  acyclic_of_contraction (HomComplex K L) (homotopyToZeroOfRight hL)

end CochainComplex.HomComplex
