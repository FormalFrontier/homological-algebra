/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.AdditiveEuler
public import HomologicalAlgebra.AdditiveEuler.Length
public import HomologicalAlgebra.AdditiveEuler.Functoriality
public import HomologicalAlgebra.AdditiveEuler.Shift
public import HomologicalAlgebra.AdditiveEuler.Cochain
public import HomologicalAlgebra.AdditiveEuler.HomologySupport
public import HomologicalAlgebra.Cochain.RelativePath
public import HomologicalAlgebra.Abelian.QuotientIntersection
public import HomologicalAlgebra.Homology.ProductTotalAcyclicity

/-!
# Homological Algebra

The public entry point for reusable additive Euler invariants.
The additive Euler modules provide a generic short-exact-sequence invariant,
its finite-length instance, exact-sequence/exact-functor Euler identities, and
finite-support/native cochain-shift Euler sums, finite-interval cochain Euler identities,
and native long-exact-sequence image-boundary corrections to cohomology additivity.
The cochain relative-path module provides a fixed-arrow pullback of the native
path object, a strict section, chosen-homotopy lifts and a relative contraction.
The abelian quotient-intersection module provides a chosen-cokernel pairing
and its monicity for subobjects L ≤ U and any third subobject D.
The homology module constructs signed quadrant product totals of native bicomplexes
and proves their acyclicity in all integer degrees from acyclic horizontal rows.
-/
