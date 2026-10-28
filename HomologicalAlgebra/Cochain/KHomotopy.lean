/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Homotopy retracts of K-projective and K-injective complexes

K-projectivity and K-injectivity descend along a one-sided homotopy retraction
of integer cochain complexes in any abelian category. For maps `f : K ⟶ L` and
`g : L ⟶ K`, only a homotopy from `f ≫ g` to `𝟙 K` is needed; there is no
condition on `g ≫ f`.

The proofs use Mathlib's canonical acyclic-test characterizations of the two
K-properties and its homotopy whiskering operations. A test map for `K` factors
through `L` up to the supplied homotopy, so its null-homotopy follows from the
corresponding property of `L`.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, §1: the K-projective
  and K-injective framework.
* Mathlib's K-projective and K-injective complexes and homotopy API.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A homotopy retract of a K-projective integer cochain complex is K-projective.
Only the composite on the retract is required to be homotopic to the identity. -/
lemma IsKProjective.of_homotopy_retract {K L : CochainComplex C ℤ} [L.IsKProjective]
    (f : K ⟶ L) (g : L ⟶ K) (h : Homotopy (f ≫ g) (𝟙 K)) : K.IsKProjective := by
  constructor
  intro A a hA
  obtain ⟨ha⟩ := IsKProjective.nonempty_homotopy_zero (g ≫ a) hA
  have ha' : Homotopy ((f ≫ g) ≫ a) 0 := by
    simpa only [Category.assoc, comp_zero] using ha.compLeft f
  exact ⟨by simpa only [Category.id_comp] using (h.compRight a).symm.trans ha'⟩

/-- A homotopy retract of a K-injective integer cochain complex is K-injective.
Only the composite on the retract is required to be homotopic to the identity. -/
lemma IsKInjective.of_homotopy_retract {K L : CochainComplex C ℤ} [L.IsKInjective]
    (f : K ⟶ L) (g : L ⟶ K) (h : Homotopy (f ≫ g) (𝟙 K)) : K.IsKInjective := by
  constructor
  intro A a hA
  obtain ⟨ha⟩ := IsKInjective.nonempty_homotopy_zero (a ≫ f) hA
  have ha' : Homotopy (a ≫ (f ≫ g)) 0 := by
    simpa only [Category.assoc, zero_comp] using ha.compRight g
  exact ⟨by simpa only [Category.comp_id] using (h.compLeft a).symm.trans ha'⟩

end CochainComplex

universe u₁ v₁

open CategoryTheory CategoryTheory.Limits HomologicalComplex

@[expose] public section

open scoped ZeroObject in
/-- An integer cochain complex with null-homotopic identity is K-projective. -/
theorem _root_.CochainComplex.isKProjective_of_homotopy_id_zero
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    (K : CochainComplex C ℤ) (h : Homotopy (𝟙 K) 0) : K.IsKProjective := by
  let : CochainComplex.IsKProjective (0 : CochainComplex C ℤ) := by
    let : ∀ n : ℤ, Projective ((0 : CochainComplex C ℤ).X n) := by
      intro n
      let : CategoryTheory.Functor.PreservesZeroMorphisms
          (HomologicalComplex.eval C (ComplexShape.up ℤ) n) := by
        infer_instance
      have h0 : CategoryTheory.Limits.IsZero (0 : CochainComplex C ℤ) := by
        apply CategoryTheory.Limits.isZero_zero
      have hn : CategoryTheory.Limits.IsZero ((0 : CochainComplex C ℤ).X n) := by
        exact CategoryTheory.Functor.map_isZero
          (HomologicalComplex.eval C (ComplexShape.up ℤ) n) h0
      exact CategoryTheory.Limits.IsZero.projective hn
    apply CochainComplex.isKProjective_of_projective
    all_goals exact (0 : ℤ)
  apply CochainComplex.IsKProjective.of_homotopy_retract
    (0 : K ⟶ (0 : CochainComplex C ℤ))
    (0 : (0 : CochainComplex C ℤ) ⟶ K)
  simpa using h.symm

open scoped ZeroObject in
/-- An integer cochain complex with null-homotopic identity is K-injective. -/
theorem _root_.CochainComplex.isKInjective_of_homotopy_id_zero
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    (K : CochainComplex C ℤ) (h : Homotopy (𝟙 K) 0) : K.IsKInjective := by
  let Z : CochainComplex C ℤ := 0
  have hZ : CochainComplex.IsKInjective Z := by
    change CochainComplex.IsKInjective (0 : CochainComplex C ℤ)
    let : ∀ n : ℤ, Injective ((0 : CochainComplex C ℤ).X n) := by
      intro n
      let : CategoryTheory.Functor.PreservesZeroMorphisms
          (HomologicalComplex.eval C (ComplexShape.up ℤ) n) := by
        infer_instance
      have h0 : CategoryTheory.Limits.IsZero (0 : CochainComplex C ℤ) := by
        apply CategoryTheory.Limits.isZero_zero
      have hn : CategoryTheory.Limits.IsZero ((0 : CochainComplex C ℤ).X n) := by
        exact CategoryTheory.Functor.map_isZero
          (HomologicalComplex.eval C (ComplexShape.up ℤ) n) h0
      exact CategoryTheory.Limits.IsZero.injective hn
    apply CochainComplex.isKInjective_of_injective
    all_goals exact (0 : ℤ)
  let : CochainComplex.IsKInjective Z := hZ
  let i : K ⟶ Z := 0
  let p : Z ⟶ K := 0
  have hip : Homotopy (i ≫ p) (𝟙 K) := by
    simpa [i, p] using h.symm
  have hpi : Homotopy (𝟙 K) (i ≫ p) := hip.symm
  solve_by_elim only [hZ, Z, i, p, hip, hpi,
    CochainComplex.IsKInjective.of_homotopy_retract]
