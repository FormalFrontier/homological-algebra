/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebraTest.AdditiveEuler
public import HomologicalAlgebraTest.AdditiveEuler.Functoriality
public import HomologicalAlgebraTest.AdditiveEuler.Shift
public import HomologicalAlgebraTest.AdditiveEuler.Cochain
public import HomologicalAlgebraTest.AdditiveEuler.HomologySupport
public import HomologicalAlgebraTest.Cochain.RelativePath
public import HomologicalAlgebraTest.Abelian.QuotientIntersection
public import HomologicalAlgebraTest.Abelian.AdmissibleLayers
public import HomologicalAlgebraTest.Homology.ProductTotalAcyclicity

/-!
# Public-import client tests

Checks of the additive Euler library through its public imports.
Checks of the fixed-arrow relative-path API through an ordinary producer import.
Checks of the quotient-intersection pairing through an ordinary producer import.
Checks of admissible-layer order, lower cut and reflector through an ordinary import.
Checks of the quadrant product-total API through an ordinary producer import.
-/
