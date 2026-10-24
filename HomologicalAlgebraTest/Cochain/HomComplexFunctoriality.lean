/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Cochain.HomComplexFunctoriality
public import HomologicalAlgebra.Cochain.HomComplexQuasiIso
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Integer stalks and the component action on the Hom complex

Integer stalks exhibit distinct cohomology classes and multiplication by six
under precomposition by two and postcomposition by three. The positive-degree
example uses a target stalk in degree one, consistent with `(L⟦n⟧).X i = L.X (i+n)`.
The zero complex and the cone of the identity are degenerate boundary cases.
The cone contraction uses Joël Riou's `MappingCone` differential and identity
formulas in Mathlib (2023).
-/

@[expose] public section

open CategoryTheory Category CochainComplex
open CochainComplex.HomComplex

namespace HomologicalAlgebraTest.HomComplexFunctoriality

abbrev Z : AddCommGrpCat := AddCommGrpCat.of ℤ

noncomputable def stalk (n : ℤ) : CochainComplex AddCommGrpCat ℤ :=
  (CochainComplex.singleFunctor AddCommGrpCat n).obj Z

noncomputable def stalkIso (n : ℤ) : (stalk n).X n ≅ Z :=
  HomologicalComplex.singleObjXSelf (.up ℤ) n Z

def times (k : ℤ) : Z ⟶ Z := k • 𝟙 Z

noncomputable def stalkMap (n k : ℤ) : stalk n ⟶ stalk n :=
  (CochainComplex.singleFunctor AddCommGrpCat n).map (times k)

/-- A canonical cocycle with its sole potentially nonzero component equal to `k`. -/
noncomputable def stalkCocycle (n k : ℤ) : Cocycle (stalk 0) (stalk n) n :=
  Cocycle.fromSingleMk (K := stalk n) (p := 0)
    (times k ≫ (stalkIso n).inv) (zero_add n) (n + 1) rfl
    ((HomologicalComplex.isZero_single_obj_X (.up ℤ) n Z (n + 1)
      (by omega)).eq_of_tgt _ _)

noncomputable def stalkClass (n k : ℤ) : CohomologyClass (stalk 0) (stalk n) n :=
  CohomologyClass.mk (stalkCocycle n k)

noncomputable def stalkHomology (n k : ℤ) : (HomComplex (stalk 0) (stalk n)).homology n :=
  (homologyAddEquiv (stalk 0) (stalk n) n).symm (stalkClass n k)

/-- Evaluate the component at the integer generator using the stalk isomorphisms. -/
noncomputable def coefficient {n : ℤ} (φ : Cochain (stalk 0) (stalk n) n) : ℤ :=
  ((stalkIso 0).inv ≫ φ.v 0 n (zero_add n) ≫ (stalkIso n).hom) (1 : ℤ)

example : times 2 (1 : ℤ) = 2 := by simp [times]

private noncomputable def stalkClassHom (n : ℤ) :
    ℤ →+ CohomologyClass (stalk 0) (stalk n) n where
  toFun := stalkClass n
  map_zero' := by
    have hN := Cocycle.fromSingleMk_zero (X := Z) (K := stalk n)
      (p := 0) (q := n) (n := n) (zero_add n) (n + 1) rfl
    have hc : stalkCocycle n 0 = 0 := by
      dsimp only [stalkCocycle]
      simp only [times, zero_zsmul, CategoryTheory.Limits.zero_comp]
      exact hN
    exact (congrArg (CohomologyClass.mk (K := stalk 0) (L := stalk n) (n := n)) hc).trans
      (CohomologyClass.mk_zero (K := stalk 0) (L := stalk n) (n := n))
  map_add' a b := by
    have hN := Cocycle.fromSingleMk_add (X := Z) (K := stalk n)
      (p := 0) (q := n) (n := n)
      (times a ≫ (stalkIso n).inv) (times b ≫ (stalkIso n).inv)
      (zero_add n) (n + 1) rfl
      ((HomologicalComplex.isZero_single_obj_X (.up ℤ) n Z (n + 1)
        (by omega)).eq_of_tgt _ _)
      ((HomologicalComplex.isZero_single_obj_X (.up ℤ) n Z (n + 1)
        (by omega)).eq_of_tgt _ _)
    have hc : stalkCocycle n (a + b) = stalkCocycle n a + stalkCocycle n b := by
      dsimp only [stalkCocycle]
      simp only [times, add_zsmul, Preadditive.add_comp]
      exact hN
    exact (congrArg (CohomologyClass.mk (K := stalk 0) (L := stalk n) (n := n)) hc).trans
      (CohomologyClass.mk_add (stalkCocycle n a) (stalkCocycle n b))

/-- A nonzero integer gives a nonzero cohomology class between integer stalks. -/
lemma stalkClass_ne_zero (n k : ℤ) (hk : k ≠ 0) :
    stalkClass n k ≠ 0 := by
  intro h
  have hb : stalkCocycle n k ∈ coboundaries (stalk 0) (stalk n) n :=
    (CohomologyClass.mk_eq_zero_iff _).mp h
  obtain ⟨g, hg⟩ :=
    (Cocycle.fromSingleMk_mem_coboundaries_iff
      (times k ≫ (stalkIso n).inv) (zero_add n) (n + 1) rfl
      ((HomologicalComplex.isZero_single_obj_X (.up ℤ) n Z (n + 1)
        (by omega)).eq_of_tgt _ _) (n - 1) (by omega)).mp hb
  have hg0 : g = 0 :=
    (HomologicalComplex.isZero_single_obj_X (.up ℤ) n Z (n - 1)
      (by omega)).eq_of_tgt _ _
  rw [hg0, CategoryTheory.Limits.zero_comp] at hg
  have ha : (0 : Z ⟶ Z) = times k := by
    simpa only [CategoryTheory.Limits.zero_comp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id] using congrArg
      (fun f : Z ⟶ (stalk n).X n => f ≫ (stalkIso n).hom) hg
  have he : (0 : ℤ) = k := by
    simpa [times] using congrArg
      (fun f : Z ⟶ Z => ConcreteCategory.hom f (1 : ℤ)) ha
  exact hk he.symm

example : stalkClass 0 1 ≠ stalkClass 0 2 := by
  intro h
  apply stalkClass_ne_zero 0 (1 - 2) (by norm_num)
  change stalkClassHom 0 (1 - 2) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr h

private lemma stalkMap_eq_zsmul (n k : ℤ) :
    stalkMap n k = k • 𝟙 (stalk n) := by
  dsimp only [stalkMap, times, stalk]
  let F := CochainComplex.singleFunctor AddCommGrpCat n
  have hN : F.map (k • 𝟙 Z) = k • 𝟙 (F.obj Z) :=
    (CategoryTheory.Functor.map_zsmul F (f := 𝟙 Z) (r := k)).trans
      (congrArg (fun f : F.obj Z ⟶ F.obj Z => k • f)
        (CategoryTheory.Functor.map_id F Z))
  exact hN

private lemma stalk_action (n a b : ℤ) :
    prePostcomp (stalkMap 0 a) (stalkMap n b) =
      (a * b) • 𝟙 (HomComplex (stalk 0) (stalk n)) := by
  rw [stalkMap_eq_zsmul, stalkMap_eq_zsmul]
  apply HomologicalComplex.hom_ext
  intro r
  refine AddCommGrpCat.ext
    (fun (φ : (HomComplex (stalk 0) (stalk n)).X r) => ?_)
  have hRHS : ConcreteCategory.hom
      (((a * b) • 𝟙 (HomComplex (stalk 0) (stalk n))).f r) φ = (a * b) • φ := by
    simp only [HomologicalComplex.zsmul_f_apply, HomologicalComplex.id_f,
      AddCommGrpCat.hom_zsmul]
    exact (AddMonoidHom.zsmul_apply
      (AddCommGrpCat.Hom.hom (𝟙 ((HomComplex (stalk 0) (stalk n)).X r)))
      (a * b) φ).trans
      (congrArg (fun x : (HomComplex (stalk 0) (stalk n)).X r => (a * b) • x)
        (ConcreteCategory.id_apply (C := AddCommGrpCat) φ))
  rw [hRHS]
  apply Cochain.ext
  intro p q hpq
  have hLHS := prePostcomp_f_hom_v (a • 𝟙 (stalk 0)) (b • 𝟙 (stalk n))
    r φ p q hpq
  rw [hLHS]
  simp only [HomologicalComplex.zsmul_f_apply, HomologicalComplex.id_f]
  rw [Preadditive.zsmul_comp, Category.id_comp, Preadditive.comp_zsmul,
    Category.comp_id, smul_smul]
  let ev : (HomComplex (stalk 0) (stalk n)).X r →+
      ((stalk 0).X p ⟶ (stalk n).X q) :=
    Pi.evalAddMonoidHom
      (fun T : Triplet r => (stalk 0).X T.p ⟶ (stalk n).X T.q) ⟨p, q, hpq⟩
  exact (map_zsmul ev (a * b) φ).symm

/-- Precomposition by two and postcomposition by three send the class of one to six. -/
lemma stalkMap_homology_one : HomologicalComplex.homologyMap
    (prePostcomp (stalkMap 0 2) (stalkMap 0 3)) 0 (stalkHomology 0 1) =
      stalkHomology 0 6 := by
  rw [stalk_action]
  have hmul : (2 * 3 : ℤ) = 6 := by norm_num
  rw [hmul]
  let H := HomComplex (stalk 0) (stalk 0)
  let G := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0
  have hG : G.map ((6 : ℤ) • 𝟙 H) = (6 : ℤ) • 𝟙 (G.obj H) :=
    (CategoryTheory.Functor.map_zsmul G (f := 𝟙 H) (r := (6 : ℤ))).trans
      (congrArg (fun f : G.obj H ⟶ G.obj H => (6 : ℤ) • f)
        (CategoryTheory.Functor.map_id G H))
  have hMap : HomologicalComplex.homologyMap ((6 : ℤ) • 𝟙 H) 0 =
      (6 : ℤ) • 𝟙 (H.homology 0) := hG
  have heval : HomologicalComplex.homologyMap ((6 : ℤ) • 𝟙 H) 0
      (stalkHomology 0 1) = (6 : ℤ) • stalkHomology 0 1 := by
    simpa only [AddCommGrpCat.hom_zsmul, AddMonoidHom.zsmul_apply,
      ConcreteCategory.id_apply] using congrArg
      (fun f : H.homology 0 ⟶ H.homology 0 => ConcreteCategory.hom f (stalkHomology 0 1))
      hMap
  rw [heval]
  apply (homologyAddEquiv (stalk 0) (stalk 0) 0).injective
  simp only [map_zsmul, stalkHomology, AddEquiv.apply_symm_apply]
  change (6 : ℤ) • stalkClassHom 0 1 = stalkClassHom 0 6
  have hc : stalkClassHom 0 ((6 : ℤ) • (1 : ℤ)) =
      (6 : ℤ) • stalkClassHom 0 1 :=
    map_zsmul (stalkClassHom 0) (6 : ℤ) (1 : ℤ)
  have hnum : (6 : ℤ) • (1 : ℤ) = 6 := by norm_num
  rw [hnum] at hc
  exact hc.symm

example :
    ((homologyAddEquiv (stalk 0) (stalk 0) 0).trans
      (CohomologyClass.homAddEquiv (K := stalk 0) (L := stalk 0) (n := 0)))
        (stalkHomology 0 6) =
      (HomotopyCategory.quotient AddCommGrpCat (.up ℤ)).map (stalkMap 0 2) ≫
        ((homologyAddEquiv (stalk 0) (stalk 0) 0).trans
          (CohomologyClass.homAddEquiv (K := stalk 0) (L := stalk 0) (n := 0)))
            (stalkHomology 0 1) ≫
        (HomotopyCategory.quotient AddCommGrpCat (.up ℤ)).map
          ((stalkMap 0 3)⟦(0 : ℤ)⟧') := by
  rw [← stalkMap_homology_one]
  exact homologyAddEquiv_naturality (stalkMap 0 2) (stalkMap 0 3) 0 (stalkHomology 0 1)

example : stalkClass 1 1 ≠ 0 := by
  exact stalkClass_ne_zero 1 1 (by norm_num)

example : coefficient ((prePostcomp (stalkMap 0 2) (stalkMap 1 3)).f 1
    (stalkCocycle 1 1).1) = 6 := by
  rw [stalk_action]
  change coefficient ((6 : ℤ) • (stalkCocycle 1 1).1) = 6
  have hv : (stalkCocycle 1 1).1.v 0 1 (zero_add 1) =
      (stalkIso 0).hom ≫ times 1 ≫ (stalkIso 1).inv :=
    Cochain.fromSingleMk_v (X := Z) (K := stalk 1) (p := 0) (q := 1) (n := 1)
      (times 1 ≫ (stalkIso 1).inv) (zero_add 1)
  have ha : (stalkIso 0).inv ≫
      ((6 : ℤ) • (stalkCocycle 1 1).1).v 0 1 (zero_add 1) ≫ (stalkIso 1).hom =
        (6 : ℤ) • 𝟙 Z := by
    simp only [Cochain.smul_v, hv, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
      Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.comp_id, times, one_zsmul]
  have he := congrArg (fun f : Z ⟶ Z => ConcreteCategory.hom f (1 : ℤ)) ha
  simpa [coefficient, AddCommGrpCat.hom_zsmul,
    AddMonoidHom.zsmul_apply, ConcreteCategory.id_apply] using he

example : Subsingleton ((HomComplex (stalk 0)
    (HomologicalComplex.zero : CochainComplex AddCommGrpCat ℤ)).homology 0) := by
  let L := (HomologicalComplex.zero : CochainComplex AddCommGrpCat ℤ)
  have hz : ∀ x : CohomologyClass (stalk 0) L 0, x = 0 := by
    intro x
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    have hc : z = 0 := by
      apply Subtype.ext
      apply Cochain.ext
      intro p q hpq
      exact (CategoryTheory.Limits.isZero_zero AddCommGrpCat).eq_of_tgt _ _
    simp [hc]
  refine ⟨fun x y => (homologyAddEquiv (stalk 0) L 0).injective ?_⟩
  exact (hz _).trans (hz _).symm

/-- The cone of the identity on the integer stalk is the contractible two-term complex. -/
noncomputable def identityCone : CochainComplex AddCommGrpCat ℤ :=
  CochainComplex.mappingCone (𝟙 (stalk 0))

example : Nonempty (Homotopy (𝟙 identityCone) 0) ∧
    Subsingleton ((HomComplex (stalk 0) identityCone).homology 0) := by
  let s : Cochain identityCone identityCone (-1) :=
    (mappingCone.snd (𝟙 (stalk 0))).comp
      (mappingCone.inl (𝟙 (stalk 0))) (zero_add (-1))
  have hs : δ (-1) 0 s = Cochain.ofHom (𝟙 identityCone) := by
    have hδ := δ_zero_cochain_comp
      (F := CochainComplex.mappingCone (𝟙 (stalk 0))) (G := stalk 0)
      (K := CochainComplex.mappingCone (𝟙 (stalk 0))) (n₂ := (-1))
      (mappingCone.snd (𝟙 (stalk 0))) (mappingCone.inl (𝟙 (stalk 0))) 0 (by norm_num)
    rw [mappingCone.δ_inl, mappingCone.δ_snd, Category.id_comp, Cochain.comp_id] at hδ
    have hn : (-1 : ℤ).negOnePow = (-1 : ℤˣ) := by
      rw [Int.negOnePow_neg, Int.negOnePow_one]
    rw [hn, Cochain.neg_comp, Units.smul_def, Units.coe_neg_one,
      neg_one_smul, neg_neg] at hδ
    have hnative : δ (-1) 0
        ((mappingCone.snd (𝟙 (stalk 0))).comp
          (mappingCone.inl (𝟙 (stalk 0))) (zero_add (-1))) =
          Cochain.ofHom (𝟙 (CochainComplex.mappingCone (𝟙 (stalk 0)))) :=
      hδ.trans ((add_comm _ _).trans (mappingCone.id (𝟙 (stalk 0))))
    simpa only [s, identityCone] using hnative
  have ht : Homotopy (𝟙 identityCone) 0 :=
    (Cochain.equivHomotopy _ _).symm ⟨s, by simpa using hs.symm⟩
  refine ⟨⟨ht⟩, ?_⟩
  have hz : ∀ x : CohomologyClass (stalk 0) identityCone 0, x = 0 := by
    intro x
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    rw [CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (-1) (by norm_num)]
    refine ⟨z.1.comp s (zero_add (-1)), ?_⟩
    rw [δ_zero_cocycle_comp, hs]
    simp
  refine ⟨fun x y => (homologyAddEquiv (stalk 0) identityCone 0).injective ?_⟩
  exact (hz _).trans (hz _).symm

private lemma stalkCocycle_coefficient
    (φ : Cochain (stalk 0) (stalk 0) 0) :
    (stalkCocycle 0 (coefficient φ)).1 = φ := by
  let ψ : Cochain (stalk 0) (stalk 0) 0 := (stalkCocycle 0 (coefficient φ)).1
  suffices h : ψ = φ from h
  apply Cochain.ext
  intro p q hpq
  by_cases hp : p = 0
  · subst p
    have hq : q = 0 := by omega
    subst q
    change ψ.v 0 0 (zero_add 0) = φ.v 0 0 (zero_add 0)
    have hv : ψ.v 0 0 (zero_add 0) =
        (stalkIso 0).hom ≫ times (coefficient φ) ≫ (stalkIso 0).inv :=
      Cochain.fromSingleMk_v (X := Z) (K := stalk 0) (p := 0) (q := 0) (n := 0)
        (times (coefficient φ) ≫ (stalkIso 0).inv) (zero_add 0)
    rw [hv]
    let f : Z ⟶ Z :=
      (stalkIso 0).inv ≫ φ.v 0 0 (zero_add 0) ≫ (stalkIso 0).hom
    have hf : f = times (coefficient φ) := by
      apply AddCommGrpCat.ext
      intro x
      have hx := map_zsmul (AddCommGrpCat.Hom.hom f) x (1 : ℤ)
      simpa [f, coefficient, times, AddCommGrpCat.hom_zsmul,
        AddMonoidHom.zsmul_apply, ConcreteCategory.id_apply, mul_comm] using hx
    have ht := congrArg
      (fun g : Z ⟶ Z => (stalkIso 0).hom ≫ g ≫ (stalkIso 0).inv) hf
    simpa [f, Category.assoc] using ht.symm
  · have hq : q ≠ 0 := by omega
    exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 Z q hq).eq_of_tgt _ _

/-- The degree-zero cohomology of the endomorphism complex of `ℤ[0]` is `ℤ`. -/
private noncomputable def stalkHomologyZeroEquiv :
    (HomComplex (stalk 0) (stalk 0)).homology 0 ≃+ ℤ := by
  refine (homologyAddEquiv (stalk 0) (stalk 0) 0).trans
    (AddEquiv.ofBijective (stalkClassHom 0) ⟨?_, ?_⟩).symm
  · intro a b h
    by_contra hab
    apply stalkClass_ne_zero 0 (a - b) (sub_ne_zero.mpr hab)
    change stalkClassHom 0 (a - b) = 0
    rw [map_sub, h, sub_self]
  · intro x
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    refine ⟨coefficient z.1, ?_⟩
    change CohomologyClass.mk (stalkCocycle 0 (coefficient z.1)) = CohomologyClass.mk z
    exact congrArg (CohomologyClass.mk (K := stalk 0) (L := stalk 0) (n := 0))
      (Subtype.ext (stalkCocycle_coefficient z.1))

/- Both invariance criteria preserve the nonzero identity class on the integer stalk. -/
example :
    QuasiIso (prePostcomp (HomotopyEquiv.refl (stalk 0)).hom
      (HomotopyEquiv.refl (stalk 0)).hom) ∧
    QuasiIso (prePostcomp (𝟙 (stalk 0)) (𝟙 (stalk 0))) ∧
    stalkHomologyZeroEquiv (stalkHomology 0 1) = 1 ∧
    (stalkCocycle 0 1).1 = Cochain.ofHom (𝟙 (stalk 0)) ∧
    HomologicalComplex.homologyMap (prePostcomp (𝟙 (stalk 0)) (𝟙 (stalk 0))) 0
      (stalkHomology 0 1) = stalkHomology 0 1 ∧
    HomologicalComplex.homologyMap (prePostcomp (𝟙 (stalk 0)) (𝟙 (stalk 0))) 0
      (stalkHomology 0 1) ≠ 0 := by
  have hequiv : QuasiIso (prePostcomp (HomotopyEquiv.refl (stalk 0)).hom
      (HomotopyEquiv.refl (stalk 0)).hom) :=
    quasiIso_prePostcomp_of_homotopyEquiv
      (HomotopyEquiv.refl (stalk 0)) (HomotopyEquiv.refl (stalk 0))
  have hquotient : QuasiIso (prePostcomp (𝟙 (stalk 0)) (𝟙 (stalk 0))) :=
    quasiIso_prePostcomp_of_isIso_quotient_map (𝟙 (stalk 0)) (𝟙 (stalk 0))
  have hgenerator : stalkHomologyZeroEquiv (stalkHomology 0 1) = 1 := by
    have hwitness : stalkHomologyZeroEquiv.symm 1 = stalkHomology 0 1 := by
      change (homologyAddEquiv (stalk 0) (stalk 0) 0).symm (stalkClassHom 0 1) =
        (homologyAddEquiv (stalk 0) (stalk 0) 0).symm (stalkClass 0 1)
      rfl
    rw [← hwitness]
    exact stalkHomologyZeroEquiv.apply_symm_apply 1
  have hcoefficient : coefficient (Cochain.ofHom (𝟙 (stalk 0))) = 1 := by
    change ((stalkIso 0).inv ≫ 𝟙 ((stalk 0).X 0) ≫ (stalkIso 0).hom) (1 : ℤ) = 1
    simp
  have hidentity : (stalkCocycle 0 1).1 = Cochain.ofHom (𝟙 (stalk 0)) := by
    simpa only [hcoefficient] using
      stalkCocycle_coefficient (Cochain.ofHom (𝟙 (stalk 0)))
  have hid : prePostcomp (𝟙 (stalk 0)) (𝟙 (stalk 0)) =
      𝟙 (HomComplex (stalk 0) (stalk 0)) := by
    simpa only [stalkMap_eq_zsmul, one_zsmul, one_mul] using stalk_action 0 1 1
  have himage : HomologicalComplex.homologyMap
      (prePostcomp (𝟙 (stalk 0)) (𝟙 (stalk 0))) 0 (stalkHomology 0 1) =
        stalkHomology 0 1 := by
    rw [hid]
    have hMap : HomologicalComplex.homologyMap
        (𝟙 (HomComplex (stalk 0) (stalk 0))) 0 =
          𝟙 ((HomComplex (stalk 0) (stalk 0)).homology 0) :=
      CategoryTheory.Functor.map_id
        (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0)
        (HomComplex (stalk 0) (stalk 0))
    rw [hMap]
    exact ConcreteCategory.id_apply _
  have hnonzero : stalkHomology 0 1 ≠ 0 := by
    intro hz
    have h := hgenerator
    rw [hz, map_zero] at h
    norm_num at h
  exact ⟨hequiv, hquotient, hgenerator, hidentity, himage, by
    rw [himage]
    exact hnonzero⟩

end HomologicalAlgebraTest.HomComplexFunctoriality
