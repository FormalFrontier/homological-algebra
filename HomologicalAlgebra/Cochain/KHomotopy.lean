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
