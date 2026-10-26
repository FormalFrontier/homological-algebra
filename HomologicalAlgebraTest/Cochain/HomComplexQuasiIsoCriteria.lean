/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import HomologicalAlgebra

/-!
# The integer stalk and the universal K-projectivity criterion

The degree-zero integer stalk gives a nonzero standard example of preservation
of quasi-isomorphisms. The zero complex gives the boundary case.
-/

open CategoryTheory Category Limits
open CochainComplex
open scoped ZeroObject

universe v u

noncomputable section

namespace HomologicalAlgebraTest.HomComplexQuasiIsoCriteria

/-- Construct the generator map with one coherent, abstract Module action.
Specializing R to the integers does not reselect an additive-group scalar action. -/
private def generatorMap {R M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] (a : M) : R →ₗ[R] M where
  toFun n := n • a
  map_add' m n := add_smul m n a
  map_smul' c n := by
    change (c * n) • a = c • (n • a)
    exact mul_smul c n a

@[simp] private lemma generatorMap_apply {R M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] (a : M) (n : R) :
    generatorMap (R := R) a n = n • a := rfl

private lemma generatorMap_one {R M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] (a : M) :
    generatorMap (R := R) a 1 = a := by
  simp [generatorMap]

/-- Prove the generator test with the same abstract Module action throughout. -/
private lemma integerLinearMap_ext_one {R M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M]
    (f g : R →ₗ[R] M) (h : f 1 = g 1) : f = g := by
  apply LinearMap.ext
  intro n
  calc
    f n = n • f 1 := by
      simpa only [smul_eq_mul, mul_one] using f.map_smul n (1 : R)
    _ = n • g 1 := congrArg (fun a : M => n • a) h
    _ = g n := by
      simpa only [smul_eq_mul, mul_one] using (g.map_smul n (1 : R)).symm

/-- Construct a lift along a surjection, without a Projective hypothesis. -/
private lemma integer_lift_of_surjective
    {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N]
    (p : M →ₗ[ℤ] N) (hp : Function.Surjective p)
    (f : ℤ →ₗ[ℤ] N) : ∃ g : ℤ →ₗ[ℤ] M, p.comp g = f := by
  obtain ⟨a, ha⟩ := hp (f 1)
  refine ⟨generatorMap a, ?_⟩
  apply integerLinearMap_ext_one
  change p (generatorMap (R := ℤ) a 1) = f 1
  exact (congrArg p (generatorMap_one (R := ℤ) a)).trans ha

/-- The integer module is categorically projective by lifting the generator. -/
private lemma integer_projective : CategoryTheory.Projective (ModuleCat.of ℤ ℤ) := by
  refine ⟨?_⟩
  intro X Y f p hp
  have hsurj : Function.Surjective p :=
    (ModuleCat.epi_iff_surjective p).mp hp
  obtain ⟨g, hg⟩ := integer_lift_of_surjective p.hom hsurj f.hom
  refine ⟨ModuleCat.ofHom g, ?_⟩
  exact congrArg (fun k : ℤ →ₗ[ℤ] Y => ModuleCat.ofHom k) hg

/-- The integer module in degree zero, with every other term and differential zero. -/
private def integerStalk : CochainComplex (ModuleCat ℤ) ℤ where
  X i := if i = 0 then ModuleCat.of ℤ ℤ else (0 : ModuleCat ℤ)
  d _ _ := 0
  shape := by intros; rfl
  d_comp_d' := by intros; simp

@[simp] private lemma integerStalk_X_zero :
    integerStalk.X (0 : ℤ) = ModuleCat.of ℤ ℤ := by
  simp [integerStalk]

private lemma integerStalk_X_ne (i : ℤ) (hi : i ≠ 0) :
    integerStalk.X i = (0 : ModuleCat ℤ) := by
  simp [integerStalk, hi]

@[simp] private lemma integerStalk_d (i j : ℤ) : integerStalk.d i j = 0 := rfl

/-- The zero endomorphism of the integer stalk. -/
private def integerStalk_zeroEnd : integerStalk ⟶ integerStalk := 0

private lemma integerStalk_projective_X (i : ℤ) :
    CategoryTheory.Projective (integerStalk.X i) := by
  by_cases hi : i = 0
  · subst i
    simpa only [integerStalk_X_zero] using integer_projective
  · rw [integerStalk_X_ne i hi]
    refine ⟨?_⟩
    intro X Y f p hp
    refine ⟨0, ?_⟩
    exact (isZero_zero (ModuleCat ℤ)).eq_of_src _ _

private theorem integerStalk_isStrictlyLE_zero :
    integerStalk.IsStrictlyLE (0 : ℤ) := by
  constructor
  intro i hi
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hi 0 rfl
  simpa [integerStalk, hi0] using (isZero_zero (ModuleCat ℤ))

/-- Boundedness and termwise projectivity imply K-projectivity. -/
private theorem integerStalk_isKProjective : integerStalk.IsKProjective := by
  have : integerStalk.IsStrictlyLE (0 : ℤ) := integerStalk_isStrictlyLE_zero
  have (i : ℤ) : Projective (integerStalk.X i) := integerStalk_projective_X i
  exact CochainComplex.isKProjective_of_projective integerStalk (0 : ℤ)

/-- Postcomposition by a quasi-isomorphism preserves the integer-stalk Hom complex. -/
private theorem integerStalk_preserves
    {X Y : CochainComplex (ModuleCat ℤ) ℤ} (q : X ⟶ Y) (hq : QuasiIso q) :
    QuasiIso (HomComplex.prePostcomp (𝟙 integerStalk) q) := by
  have : integerStalk.IsKProjective := integerStalk_isKProjective
  have : QuasiIso q := hq
  exact IsKProjective.quasiIso_prePostcomp integerStalk q

private lemma integerStalk_id_not_nullhomotopic :
    ¬ Nonempty (Homotopy (𝟙 integerStalk) 0) := by
  rintro ⟨h⟩
  have hdNext0 : dNext (0 : ℤ) h.hom = 0 := by
    simp only [dNext, AddMonoidHom.mk'_apply, integerStalk_d, zero_comp]
  have hprevD0 : prevD (0 : ℤ) h.hom = 0 := by
    simp only [prevD, AddMonoidHom.mk'_apply, integerStalk_d, comp_zero]
  have hid0 : (𝟙 (integerStalk.X (0 : ℤ))) = 0 := by
    simpa only [hdNext0, hprevD0, HomologicalComplex.id_f,
      HomologicalComplex.zero_f_apply, zero_add, add_zero]
      using h.comm (0 : ℤ)
  have hid : (𝟙 (ModuleCat.of ℤ ℤ)) = 0 := by
    exact Eq.mp
      (congrArg (fun X : ModuleCat ℤ => (𝟙 X : X ⟶ X) = 0)
        integerStalk_X_zero) hid0
  have h10 : (1 : ℤ) = 0 := by
    simpa using ConcreteCategory.congr_hom hid (1 : ℤ)
  exact one_ne_zero h10

/-- The identity represents a nonzero degree-zero class in the canonical Hom complex. -/
private lemma integerStalk_homComplex_h0_not_isZero :
    ¬ IsZero ((HomComplex integerStalk integerStalk).homology (0 : ℤ)) := by
  intro hz
  exact integerStalk_id_not_nullhomotopic
    ((HomComplex.isZero_homology_zero_iff integerStalk integerStalk).mp hz
      (𝟙 integerStalk))

/-- Quasi-isomorphisms are preserved by Hom from the integer stalk. -/
example {X Y : CochainComplex (ModuleCat ℤ) ℤ} (q : X ⟶ Y) (hq : QuasiIso q) :
    QuasiIso (HomComplex.prePostcomp (𝟙 integerStalk) q) := by
  exact (CochainComplex.isKProjective_iff_quasiIso_prePostcomp
    integerStalk).mp integerStalk_isKProjective q hq

/-- Preservation of quasi-isomorphisms implies K-projectivity of the integer stalk. -/
example : integerStalk.IsKProjective := by
  apply (CochainComplex.isKProjective_iff_quasiIso_prePostcomp integerStalk).mpr
  intro X Y q hq
  exact integerStalk_preserves q hq

/-- The canonical Hom complex has a nonzero degree-zero class. -/
example : ¬ IsZero ((HomComplex integerStalk integerStalk).homology (0 : ℤ)) :=
  integerStalk_homComplex_h0_not_isZero

/-- Unlike the zero-complex boundary case, this zero endomorphism is not a
quasi-isomorphism: it would kill the nonzero identity cohomology class. -/
example : ¬ QuasiIso integerStalk_zeroEnd := by
  intro hq
  let H := HomComplex integerStalk integerStalk
  -- Evaluate the induced cohomology map using naturality.
  have h := integerStalk_preserves integerStalk_zeroEnd hq
  rw [_root_.quasiIso_iff] at h
  have h0 := h (0 : ℤ)
  rw [_root_.quasiIsoAt_iff_isIso_homologyMap] at h0
  let f := HomologicalComplex.homologyMap
    (HomComplex.prePostcomp (𝟙 integerStalk) integerStalk_zeroEnd) (0 : ℤ)
  have hfIso : IsIso f := h0
  let e := (HomComplex.homologyAddEquiv integerStalk integerStalk (0 : ℤ)).trans
    (HomComplex.CohomologyClass.homAddEquiv
      (K := integerStalk) (L := integerStalk) (n := (0 : ℤ)))
  have hf (x : H.homology (0 : ℤ)) : f x = 0 := by
    apply e.injective
    have hn := HomComplex.homologyAddEquiv_naturality
      (𝟙 integerStalk) integerStalk_zeroEnd (0 : ℤ) x
    simpa only [e, f, H, integerStalk_zeroEnd, Functor.map_zero, comp_zero, map_zero] using hn
  apply integerStalk_homComplex_h0_not_isZero
  apply (IsZero.iff_id_eq_zero _).mpr
  ext x
  change x = 0
  have hi := ConcreteCategory.congr_hom (IsIso.inv_hom_id f) x
  change f ((inv f) x) = x at hi
  exact hi.symm.trans (hf ((inv f) x))

/-- Morphisms from the zero complex give an acyclic Hom complex. -/
private lemma zeroHomComplexAcyclic
    {C : Type u} [Category.{v} C] [Abelian C] (L : CochainComplex C ℤ) :
    (HomComplex (0 : CochainComplex C ℤ) L).Acyclic := by
  apply (HomComplex.acyclic_iff (0 : CochainComplex C ℤ) L).mpr
  intro n f
  have hf : f = 0 := (isZero_zero (CochainComplex C ℤ)).eq_of_src f 0
  rw [hf]
  exact ⟨Homotopy.refl 0⟩

/-- The zero complex is K-projective over every abelian category. -/
private lemma zeroKProjective {C : Type u} [Category.{v} C] [Abelian C] :
    (0 : CochainComplex C ℤ).IsKProjective := by
  apply (CochainComplex.isKProjective_iff_acyclic_homComplex
    (0 : CochainComplex C ℤ)).mpr
  intro L _
  exact zeroHomComplexAcyclic L

/-- Postcomposition on Hom complexes from zero has zero cohomology on both sides,
without a quasi-isomorphism hypothesis on the given morphism. -/
private lemma zeroPrePostcompQuasiIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    QuasiIso (HomComplex.prePostcomp (𝟙 (0 : CochainComplex C ℤ)) g) := by
  rw [_root_.quasiIso_iff]
  intro n
  rw [_root_.quasiIsoAt_iff_isIso_homologyMap]
  have hK := (zeroHomComplexAcyclic K n).isZero_homology
  have hL := (zeroHomComplexAcyclic L n).isZero_homology
  refine ⟨⟨0, ?_, ?_⟩⟩
  · exact hK.eq_of_src _ _
  · exact hL.eq_of_src _ _

-- The public forward implication applies to the proved zero model.
example {X Y : CochainComplex AddCommGrpCat ℤ} (q : X ⟶ Y) (hq : QuasiIso q) :
    QuasiIso (HomComplex.prePostcomp
      (𝟙 (0 : CochainComplex AddCommGrpCat ℤ)) q) := by
  exact (CochainComplex.isKProjective_iff_quasiIso_prePostcomp
    (0 : CochainComplex AddCommGrpCat ℤ)).mp zeroKProjective q hq

-- The public converse receives a universal property proved independently.
example : (0 : CochainComplex AddCommGrpCat ℤ).IsKProjective := by
  apply (CochainComplex.isKProjective_iff_quasiIso_prePostcomp
    (0 : CochainComplex AddCommGrpCat ℤ)).mpr
  intro K L q _
  exact zeroPrePostcompQuasiIso q

-- At the zero object, the zero endomorphism is a quasi-isomorphism.
example : QuasiIso (0 : (0 : CochainComplex AddCommGrpCat ℤ) ⟶
    (0 : CochainComplex AddCommGrpCat ℤ)) := by
  have h : (0 : (0 : CochainComplex AddCommGrpCat ℤ) ⟶
      (0 : CochainComplex AddCommGrpCat ℤ)) =
      𝟙 (0 : CochainComplex AddCommGrpCat ℤ) :=
    (isZero_zero (CochainComplex AddCommGrpCat ℤ)).eq_of_src _ _
  rw [h]
  infer_instance

end HomologicalAlgebraTest.HomComplexQuasiIsoCriteria
