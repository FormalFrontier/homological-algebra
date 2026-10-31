/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Subobject.ArtinianObject
public import Mathlib.CategoryTheory.Subobject.NoetherianObject
public import HomologicalAlgebra.Abelian.NoetherianObject
public import HomologicalAlgebra.Abelian.SerreClass

/-!
# Artinian objects, Noetherian opposite objects, and Serre closure

Mathlib defines `CategoryTheory.IsArtinianObject` for an arbitrary category and
characterizes it by the descending chain condition on subobjects. In an abelian
category, this module identifies that property with Noetherianity of the opposite
object. The proof transports chain conditions along Mathlib's order isomorphism
`CategoryTheory.Abelian.subobjectIsoSubobjectOp`.

It also shows that `CategoryTheory.isArtinianObject` is a Serre class: it contains
zero and is closed under subobjects, quotients, and extensions. This follows by
applying `CategoryTheory.ObjectProperty.IsSerreClass.unop` to the Noetherian Serre
instance in the opposite category and identifying the resulting property using
the Artinian--Noetherian bridge.

## References

* Mathlib's formalizations in `Mathlib.CategoryTheory.Subobject.ArtinianObject`
  and `Mathlib.CategoryTheory.Subobject.NoetherianObject` provide the object
  predicates and their chain-condition characterizations.
* The subobject order duality is formalized in
  `Mathlib.CategoryTheory.Abelian.Subobject`.
* Mathlib's `Mathlib.CategoryTheory.Abelian.SerreClass.Basic`,
  `Mathlib.CategoryTheory.ObjectProperty` APIs, and
  `Mathlib.Algebra.Homology.ShortComplex.ShortExact` supply the Serre closure
  framework and opposite short exact sequences.
* `HomologicalAlgebra.Abelian.NoetherianObject` supplies the Noetherian Serre
  instance reused here; `HomologicalAlgebra.Abelian.SerreClass` supplies the generic
  opposite transport.
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

/-- Artinian objects form a Serre class in an abelian category. -/
instance [Abelian C] : (isArtinianObject (C := C)).IsSerreClass := by
  have hP : isArtinianObject (C := C) =
      (isNoetherianObject (C := Cᵒᵖ)).unop := by
    funext X
    apply propext
    simpa only [IsArtinianObject, IsNoetherianObject, ObjectProperty.is_iff,
      ObjectProperty.unop_iff] using
      (isArtinianObject_iff_isNoetherianObject_op X)
  rw [hP]
  exact ObjectProperty.IsSerreClass.unop (isNoetherianObject (C := Cᵒᵖ))

end CategoryTheory
