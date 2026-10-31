/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Indecomposable.Artinian
public import HomologicalAlgebra.Indecomposable.Noetherian

/-!
# Finite biproduct decompositions into indecomposable objects

An Artinian object or a Noetherian object in a category with zero morphisms and
finite biproducts is isomorphic to a finite biproduct of indecomposable objects.
The chain condition is imposed on the individual object. No abelian or
preadditive structure is required. A zero object has the empty decomposition.

The proofs use well-founded subobject induction and maximality of biproduct
summands, respectively. Indecomposability, the object chain conditions, and the
biproduct universal properties are supplied by Mathlib. The shared biproduct
module includes isomorphism transport and the finite-family append comparison.

## References

* `Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts`
* `Mathlib.CategoryTheory.Subobject.ArtinianObject`
* `Mathlib.CategoryTheory.Subobject.NoetherianObject`
-/
