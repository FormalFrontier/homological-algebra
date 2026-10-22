/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Bounded-below complexes of projective objects

A particular map between bounded-below integer chain complexes of projective objects
is a quasi-isomorphism if and only if it is the forward map of a homotopy equivalence.
The two complexes may have different lower bounds. Bounds concern the terms, not
merely the homology objects.

The proof reindexes by negation using `ComplexShape.embeddingDownIntUpInt` and
applies Mathlib's bounded-projective cochain criterion. For nonnegative chain
complexes, use Mathlib's `ChainComplex.quasiIso_iff_of_projective` directly.

Both projectivity assumptions matter: a projective resolution need not be homotopy
equivalent to its nonprojective degree-zero homology. The lower-support assumptions
also matter: an unbounded acyclic complex of projectives need not be contractible.

## References

This is an integer-chain generalization of Mathlib's
`ChainComplex.quasiIso_iff_of_projective`, following its extension proof and
`CochainComplex.IsKProjective.quasiIso_iff`.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

private lemma isStrictlyLE_extend_of_isZero_below (K : ChainComplex C ℤ) (a : ℤ)
    (hK : ∀ i, i < a → IsZero (K.X i)) :
    CochainComplex.IsStrictlyLE (K.extend ComplexShape.embeddingDownIntUpInt) (-a) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact (hK (-i) (by lia)).of_iso
    (K.extendXIso ComplexShape.embeddingDownIntUpInt (i := -i) (i' := i) (by simp))

/-- A particular map between termwise bounded-below integer chain complexes of
projective objects is a quasi-isomorphism exactly when it is the forward map of a
homotopy equivalence. The lower bounds `a` and `b` are independent.

This is the integer-chain analogue of `ChainComplex.quasiIso_iff_of_projective`,
obtained from `CochainComplex.IsKProjective.quasiIso_iff` by negating degrees. -/
lemma quasiIso_iff_of_projective_of_isZero_below {K L : ChainComplex C ℤ}
    [∀ i, Projective (K.X i)] [∀ i, Projective (L.X i)]
    (a b : ℤ) (hK : ∀ i, i < a → IsZero (K.X i))
    (hL : ∀ i, i < b → IsZero (L.X i)) (f : K ⟶ L) :
    QuasiIso f ↔ homotopyEquivalences C (.down ℤ) f := by
  let : CochainComplex.IsStrictlyLE (K.extend ComplexShape.embeddingDownIntUpInt) (-a) :=
    isStrictlyLE_extend_of_isZero_below K a hK
  let : CochainComplex.IsStrictlyLE (L.extend ComplexShape.embeddingDownIntUpInt) (-b) :=
    isStrictlyLE_extend_of_isZero_below L b hL
  let : CochainComplex.IsKProjective (K.extend ComplexShape.embeddingDownIntUpInt) :=
    CochainComplex.isKProjective_of_projective _ (-a)
  let : CochainComplex.IsKProjective (L.extend ComplexShape.embeddingDownIntUpInt) :=
    CochainComplex.isKProjective_of_projective _ (-b)
  rw [← quasiIso_extendMap_iff _ ComplexShape.embeddingDownIntUpInt,
    CochainComplex.IsKProjective.quasiIso_iff,
    homotopyEquivalences_extendMap_iff]

end ChainComplex
