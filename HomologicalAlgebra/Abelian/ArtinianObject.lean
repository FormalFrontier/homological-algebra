/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Subobject.ArtinianObject
public import Mathlib.CategoryTheory.Subobject.NoetherianObject

/-!
# Artinian objects and Noetherian opposite objects

Mathlib defines `CategoryTheory.IsArtinianObject` for an arbitrary category and
characterizes it by the descending chain condition on subobjects. In an abelian
category, this module identifies that property with Noetherianity of the opposite
object. The proof transports chain conditions along Mathlib's order isomorphism
`CategoryTheory.Abelian.subobjectIsoSubobjectOp`.

## References

* Mathlib's formalizations in `Mathlib.CategoryTheory.Subobject.ArtinianObject`
  and `Mathlib.CategoryTheory.Subobject.NoetherianObject` provide the object
  predicates and their chain-condition characterizations.
* The subobject order duality is formalized in
  `Mathlib.CategoryTheory.Abelian.Subobject`.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

/-- In an abelian category, an object is Artinian if and only if its opposite is
Noetherian, by Mathlib's order duality for subobjects. -/
theorem isArtinianObject_iff_isNoetherianObject_op [Abelian C] (X : C) :
    IsArtinianObject X ↔ IsNoetherianObject (op X) := by
  rw [isArtinianObject_iff_not_strictAnti, isNoetherianObject_iff_not_strictMono]
  let e := Abelian.subobjectIsoSubobjectOp X
  constructor
  · intro h f hf
    apply h (fun n ↦ e.symm (f n))
    intro i j hij
    exact e.symm.strictMono (hf hij)
  · intro h f hf
    apply h (fun n ↦ e (f n))
    intro i j hij
    exact e.strictMono (hf hij)

end CategoryTheory
