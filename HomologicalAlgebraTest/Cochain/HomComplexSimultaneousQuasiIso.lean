/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import HomologicalAlgebra.Cochain.HomComplexQuasiIso

/-!
# Simultaneous composition from the integer stalk to the rational stalk

Over the category of abelian groups presented as modules over ℤ, the stalk ℤ[0]
is K-projective and the stalk ℚ[0] is K-injective. Negative identity on ℤ[0] and
multiplication by two on ℚ[0] are chain isomorphisms. Both orientations of
simultaneous quasi-isomorphism invariance therefore apply to this pair.

Evaluation at the integer generator identifies the degree-zero homology
of their Hom complex additively with ℚ. Under this identification, canonical
pre- and postcomposition acts by multiplication by minus two. In particular,
the class corresponding to one has nonzero image.
-/

@[expose] public section

open CategoryTheory Category Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex

namespace HomComplexSimultaneousQuasiIso

private noncomputable abbrev integerModuleAbelian : Abelian (ModuleCat.{0} ℤ) :=
  inferInstance

private noncomputable abbrev integerModulePreadditive : Preadditive (ModuleCat.{0} ℤ) := by
  let : Abelian (ModuleCat.{0} ℤ) := integerModuleAbelian
  exact Abelian.toPreadditive

attribute [local instance] integerModulePreadditive

private abbrev Z : ModuleCat.{0} ℤ := ModuleCat.of ℤ ℤ
private abbrev Q : ModuleCat.{0} ℤ := ModuleCat.of ℤ ℚ

private noncomputable def integerStalk : CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) (0 : ℤ)).obj Z

private noncomputable def rationalStalk : CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) (0 : ℤ)).obj Q

private noncomputable def integerStalkIso : integerStalk.X 0 ≅ Z :=
  singleObjXSelf (.up ℤ) (0 : ℤ) Z

private noncomputable def rationalStalkIso : rationalStalk.X 0 ≅ Q :=
  singleObjXSelf (.up ℤ) (0 : ℤ) Q

private lemma integerStalk_isKProjective : integerStalk.IsKProjective := by
  let : integerStalk.IsStrictlyLE 0 := by
    dsimp only [integerStalk]
    infer_instance
  let : ∀ i : ℤ, Projective (integerStalk.X i) := fun i ↦ by
    by_cases hi : i = 0
    · subst i
      exact Projective.of_iso integerStalkIso.symm (inferInstance : Projective Z)
    · exact (isZero_single_obj_X (.up ℤ) (0 : ℤ) Z i hi).projective
  exact isKProjective_of_projective integerStalk 0

private lemma rationalModule_injective : Injective Q := by
  let : DivisibleBy ℚ ℤ := divisibleByIntOfCharZero
  let : Module.Injective ℤ ℚ := (Module.Baer.of_divisible ℚ).injective
  exact Module.injective_object_of_injective_module ℤ ℚ

private lemma rationalStalk_isKInjective : rationalStalk.IsKInjective := by
  let : rationalStalk.IsStrictlyGE 0 := by
    dsimp only [rationalStalk]
    infer_instance
  let : ∀ i : ℤ, Injective (rationalStalk.X i) := fun i ↦ by
    by_cases hi : i = 0
    · subst i
      let : Injective Q := rationalModule_injective
      exact Injective.of_iso rationalStalkIso.symm (inferInstance : Injective Q)
    · exact (isZero_single_obj_X (.up ℤ) (0 : ℤ) Q i hi).injective
  exact isKInjective_of_injective rationalStalk 0

private noncomputable def coefficientMap (q : ℚ) : Z ⟶ Q :=
  ModuleCat.ofHom
    ({ toFun := fun n : ℤ ↦ n • q
       map_add' := fun a b ↦ add_zsmul q a b
       map_smul' := fun a b ↦ by
         change (a * b) • q = a • (b • q)
         exact mul_smul a b q } : ℤ →ₗ[ℤ] ℚ)

private noncomputable def rationalCocycle (q : ℚ) :
    Cocycle integerStalk rationalStalk 0 :=
  Cocycle.fromSingleMk (K := rationalStalk) (p := 0)
    (coefficientMap q ≫ rationalStalkIso.inv) (zero_add 0) 1 rfl
    ((isZero_single_obj_X (.up ℤ) (0 : ℤ) Q 1 (by norm_num)).eq_of_tgt _ _)

private noncomputable def rationalClass (q : ℚ) :
    CohomologyClass integerStalk rationalStalk 0 :=
  CohomologyClass.mk (rationalCocycle q)

private noncomputable def rationalClassHom :
    ℚ →+ CohomologyClass integerStalk rationalStalk 0 where
  toFun := rationalClass
  map_zero' := by
    have hm : coefficientMap 0 = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro n
      change n • (0 : ℚ) = 0
      exact smul_zero n
    have hN := Cocycle.fromSingleMk_zero (X := Z) (K := rationalStalk)
      (p := 0) (q := 0) (n := 0) (zero_add 0) 1 rfl
    have hc : rationalCocycle 0 = 0 := by
      dsimp only [rationalCocycle]
      rw [hm, zero_comp]
      exact hN
    exact (congrArg
      (CohomologyClass.mk (K := integerStalk) (L := rationalStalk) (n := 0)) hc).trans
      (CohomologyClass.mk_zero (K := integerStalk) (L := rationalStalk) (n := 0))
  map_add' a b := by
    have hm : coefficientMap (a + b) = coefficientMap a + coefficientMap b := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro n
      change n • (a + b) = n • a + n • b
      exact smul_add n a b
    have hN := Cocycle.fromSingleMk_add (X := Z) (K := rationalStalk)
      (p := 0) (q := 0) (n := 0)
      (coefficientMap a ≫ rationalStalkIso.inv)
      (coefficientMap b ≫ rationalStalkIso.inv) (zero_add 0) 1 rfl
      ((isZero_single_obj_X (.up ℤ) (0 : ℤ) Q 1 (by norm_num)).eq_of_tgt _ _)
      ((isZero_single_obj_X (.up ℤ) (0 : ℤ) Q 1 (by norm_num)).eq_of_tgt _ _)
    have hc : rationalCocycle (a + b) = rationalCocycle a + rationalCocycle b := by
      dsimp only [rationalCocycle]
      rw [hm, Preadditive.add_comp]
      exact hN
    exact (congrArg
      (CohomologyClass.mk (K := integerStalk) (L := rationalStalk) (n := 0)) hc).trans
      (CohomologyClass.mk_add (rationalCocycle a) (rationalCocycle b))

private lemma rationalClass_ne_zero (q : ℚ) (hq : q ≠ 0) :
    rationalClass q ≠ 0 := by
  intro h
  have hb : rationalCocycle q ∈ coboundaries integerStalk rationalStalk 0 :=
    (CohomologyClass.mk_eq_zero_iff _).mp h
  obtain ⟨g, hg⟩ :=
    (Cocycle.fromSingleMk_mem_coboundaries_iff
      (coefficientMap q ≫ rationalStalkIso.inv) (zero_add 0) 1 rfl
      ((isZero_single_obj_X (.up ℤ) (0 : ℤ) Q 1 (by norm_num)).eq_of_tgt _ _)
      (-1) (by norm_num)).mp hb
  have hg0 : g = 0 :=
    (isZero_single_obj_X (.up ℤ) (0 : ℤ) Q (-1) (by norm_num)).eq_of_tgt _ _
  rw [hg0, zero_comp] at hg
  have ha : (0 : Z ⟶ Q) = coefficientMap q := by
    simpa only [zero_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun f : Z ⟶ rationalStalk.X 0 => f ≫ rationalStalkIso.hom) hg
  have he : (0 : ℚ) = q := by
    simpa [coefficientMap] using
      congrArg (fun f : Z ⟶ Q => ConcreteCategory.hom f (1 : ℤ)) ha
  exact hq he.symm

private noncomputable def coefficient
    (φ : Cochain integerStalk rationalStalk 0) : ℚ :=
  (integerStalkIso.inv ≫ φ.v 0 0 (zero_add 0) ≫ rationalStalkIso.hom) (1 : ℤ)

private lemma rationalCocycle_coefficient
    (φ : Cochain integerStalk rationalStalk 0) :
    (rationalCocycle (coefficient φ)).1 = φ := by
  let ψ : Cochain integerStalk rationalStalk 0 := (rationalCocycle (coefficient φ)).1
  suffices h : ψ = φ from h
  apply Cochain.ext
  intro p q hpq
  by_cases hp : p = 0
  · subst p
    have hq : q = 0 := by omega
    subst q
    change ψ.v 0 0 (zero_add 0) = φ.v 0 0 (zero_add 0)
    have hv : ψ.v 0 0 (zero_add 0) =
        integerStalkIso.hom ≫ coefficientMap (coefficient φ) ≫ rationalStalkIso.inv :=
      Cochain.fromSingleMk_v (X := Z) (K := rationalStalk) (p := 0) (q := 0) (n := 0)
        (coefficientMap (coefficient φ) ≫ rationalStalkIso.inv) (zero_add 0)
    rw [hv]
    let f : Z ⟶ Q :=
      integerStalkIso.inv ≫ φ.v 0 0 (zero_add 0) ≫ rationalStalkIso.hom
    have hf : f = coefficientMap (coefficient φ) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro n
      change f.hom n = n • f.hom (1 : ℤ)
      calc
        f.hom n = f.hom (n • (1 : ℤ)) := by
          simp
        _ = n • f.hom (1 : ℤ) := map_zsmul f.hom n (1 : ℤ)
    have ht := congrArg
      (fun g : Z ⟶ Q => integerStalkIso.hom ≫ g ≫ rationalStalkIso.inv) hf
    simpa [f, Category.assoc] using ht.symm
  · have hq : q ≠ 0 := by omega
    exact (isZero_single_obj_X (.up ℤ) (0 : ℤ) Q q hq).eq_of_tgt _ _

/-- Evaluation at one identifies the degree-zero Hom-complex homology with ℚ. -/
private noncomputable def homologyZeroEquiv :
    (HomComplex integerStalk rationalStalk).homology 0 ≃+ ℚ := by
  refine (homologyAddEquiv integerStalk rationalStalk 0).trans
    (AddEquiv.ofBijective rationalClassHom ⟨?_, ?_⟩).symm
  · intro a b h
    by_contra hab
    apply rationalClass_ne_zero (a - b) (sub_ne_zero.mpr hab)
    change rationalClassHom (a - b) = 0
    rw [map_sub, h, sub_self]
  · intro x
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    refine ⟨coefficient z.1, ?_⟩
    change CohomologyClass.mk (rationalCocycle (coefficient z.1)) = CohomologyClass.mk z
    exact congrArg
      (CohomologyClass.mk (K := integerStalk) (L := rationalStalk) (n := 0))
      (Subtype.ext (rationalCocycle_coefficient z.1))

private noncomputable def negativeIdentityIso : integerStalk ≅ integerStalk where
  hom := -𝟙 integerStalk
  inv := -𝟙 integerStalk
  hom_inv_id := by simp
  inv_hom_id := by simp

private noncomputable def rationalMultiplication (a : ℚ) : Q ⟶ Q :=
  ModuleCat.ofHom
    ({ toFun := fun q : ℚ ↦ a * q
       map_add' := fun b c ↦ mul_add a b c
       map_smul' := fun n q ↦ by
         change a * (n • q) = n • (a * q)
         simp [zsmul_eq_mul, mul_assoc, mul_comm] } : ℚ →ₗ[ℤ] ℚ)

private lemma rationalMultiplication_two :
    rationalMultiplication 2 = (2 : ℤ) • 𝟙 Q := by
  ext q
  change (2 : ℚ) * q = (2 : ℤ) • q
  simp only [two_mul, two_smul]

private noncomputable def rationalDoubleIso : Q ≅ Q where
  hom := rationalMultiplication 2
  inv := rationalMultiplication (1 / 2)
  hom_inv_id := by
    ext q
    change (1 / 2 : ℚ) * ((2 : ℚ) * q) = q
    norm_num [← mul_assoc]
  inv_hom_id := by
    ext q
    change (2 : ℚ) * ((1 / 2 : ℚ) * q) = q
    norm_num [← mul_assoc]

private noncomputable def doublingIso : rationalStalk ≅ rationalStalk :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) (0 : ℤ)).mapIso rationalDoubleIso

private lemma doublingIso_hom : doublingIso.hom = (2 : ℤ) • 𝟙 rationalStalk := by
  let F := CochainComplex.singleFunctor (ModuleCat ℤ) (0 : ℤ)
  change F.map (rationalMultiplication 2) = (2 : ℤ) • 𝟙 (F.obj Q)
  rw [rationalMultiplication_two]
  exact (Functor.map_zsmul F (f := 𝟙 Q) (r := (2 : ℤ))).trans
    (congrArg (fun f : F.obj Q ⟶ F.obj Q => (2 : ℤ) • f) (CategoryTheory.Functor.map_id F Q))

private lemma scalar_action (a b : ℤ) :
    prePostcomp (a • 𝟙 integerStalk) (b • 𝟙 rationalStalk) =
      (a * b) • 𝟙 (HomComplex integerStalk rationalStalk) := by
  apply HomologicalComplex.hom_ext
  intro r
  refine AddCommGrpCat.ext
    (fun (φ : (HomComplex integerStalk rationalStalk).X r) => ?_)
  have hRHS : ConcreteCategory.hom
      (((a * b) • 𝟙 (HomComplex integerStalk rationalStalk)).f r) φ =
        (a * b) • φ := by
    simp only [HomologicalComplex.zsmul_f_apply, HomologicalComplex.id_f,
      AddCommGrpCat.hom_zsmul]
    exact (AddMonoidHom.zsmul_apply
      (AddCommGrpCat.Hom.hom (𝟙 ((HomComplex integerStalk rationalStalk).X r)))
      (a * b) φ).trans
      (congrArg (fun x : (HomComplex integerStalk rationalStalk).X r => (a * b) • x)
        (ConcreteCategory.id_apply (C := AddCommGrpCat) φ))
  rw [hRHS]
  apply Cochain.ext
  intro p q hpq
  have hLHS := prePostcomp_f_hom_v (a • 𝟙 integerStalk) (b • 𝟙 rationalStalk)
    r φ p q hpq
  rw [hLHS]
  simp only [HomologicalComplex.zsmul_f_apply, HomologicalComplex.id_f]
  rw [Preadditive.zsmul_comp, Category.id_comp, Preadditive.comp_zsmul,
    Category.comp_id, smul_smul]
  let ev : (HomComplex integerStalk rationalStalk).X r →+
      (integerStalk.X p ⟶ rationalStalk.X q) :=
    Pi.evalAddMonoidHom
      (fun T : Triplet r => integerStalk.X T.p ⟶ rationalStalk.X T.q) ⟨p, q, hpq⟩
  exact (map_zsmul ev (a * b) φ).symm

private lemma simultaneous_action :
    prePostcomp negativeIdentityIso.hom doublingIso.hom =
      (-2 : ℤ) • 𝟙 (HomComplex integerStalk rationalStalk) := by
  rw [doublingIso_hom]
  change prePostcomp (-𝟙 integerStalk) ((2 : ℤ) • 𝟙 rationalStalk) = _
  simpa only [neg_one_zsmul, neg_mul, one_mul] using scalar_action (-1) 2

private lemma homology_action
    (x : (HomComplex integerStalk rationalStalk).homology 0) :
    homologyZeroEquiv
        (HomologicalComplex.homologyMap
          (prePostcomp negativeIdentityIso.hom doublingIso.hom) 0 x) =
      (-2 : ℚ) * homologyZeroEquiv x := by
  rw [simultaneous_action]
  let H := HomComplex integerStalk rationalStalk
  let G := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0
  have hG : G.map ((-2 : ℤ) • 𝟙 H) = (-2 : ℤ) • 𝟙 (G.obj H) :=
    (Functor.map_zsmul G (f := 𝟙 H) (r := (-2 : ℤ))).trans
      (congrArg (fun f : G.obj H ⟶ G.obj H => (-2 : ℤ) • f) (CategoryTheory.Functor.map_id G H))
  have hMap : HomologicalComplex.homologyMap ((-2 : ℤ) • 𝟙 H) 0 =
      (-2 : ℤ) • 𝟙 (H.homology 0) := hG
  have heval : HomologicalComplex.homologyMap ((-2 : ℤ) • 𝟙 H) 0 x =
      (-2 : ℤ) • x := by
    simpa only [AddCommGrpCat.hom_zsmul, AddMonoidHom.zsmul_apply,
      ConcreteCategory.id_apply] using congrArg
      (fun f : H.homology 0 ⟶ H.homology 0 => ConcreteCategory.hom f x) hMap
  rw [heval, map_zsmul]
  norm_num [zsmul_eq_mul]

example : QuasiIso (prePostcomp negativeIdentityIso.hom doublingIso.hom) := by
  let : Abelian (ModuleCat.{0} ℤ) := integerModuleAbelian
  let : integerStalk.IsKProjective := integerStalk_isKProjective
  let : rationalStalk.IsKInjective := rationalStalk_isKInjective
  exact IsKProjective.quasiIso_prePostcomp_of_isKInjective
    negativeIdentityIso.hom doublingIso.hom

example : QuasiIso (prePostcomp negativeIdentityIso.hom doublingIso.hom) := by
  let : Abelian (ModuleCat.{0} ℤ) := integerModuleAbelian
  let : integerStalk.IsKProjective := integerStalk_isKProjective
  let : rationalStalk.IsKInjective := rationalStalk_isKInjective
  exact IsKInjective.quasiIso_prePostcomp_of_isKProjective
    negativeIdentityIso.hom doublingIso.hom

example :
    (∀ x : (HomComplex integerStalk rationalStalk).homology 0,
      homologyZeroEquiv
          (HomologicalComplex.homologyMap
            (prePostcomp negativeIdentityIso.hom doublingIso.hom) 0 x) =
        (-2 : ℚ) * homologyZeroEquiv x) ∧
    homologyZeroEquiv
        (HomologicalComplex.homologyMap
          (prePostcomp negativeIdentityIso.hom doublingIso.hom) 0
          (homologyZeroEquiv.symm 1)) = (-2 : ℚ) ∧
    HomologicalComplex.homologyMap
        (prePostcomp negativeIdentityIso.hom doublingIso.hom) 0
        (homologyZeroEquiv.symm 1) ≠ 0 := by
  refine ⟨homology_action, ?_, ?_⟩
  · rw [homology_action, AddEquiv.apply_symm_apply, mul_one]
  · intro hz
    have h := homology_action (homologyZeroEquiv.symm 1)
    rw [hz, map_zero, AddEquiv.apply_symm_apply, mul_one] at h
    norm_num at h

end HomComplexSimultaneousQuasiIso
