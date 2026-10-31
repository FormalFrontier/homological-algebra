/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic

/-!
# Serre classes and opposite categories

A Serre class in an abelian category contains zero and is closed under subobjects,
quotients, and extensions. This module provides
`CategoryTheory.ObjectProperty.IsSerreClass.unop`, which transports a Serre class
from the opposite category to the original category.

Passage to the opposite category exchanges subobjects with quotients and reverses
the endpoints of short exact sequences. Thus extension closure transports with the
two endpoint hypotheses exchanged.

## References

* Mathlib's `Mathlib.CategoryTheory.Abelian.SerreClass.Basic` and
  `Mathlib.CategoryTheory.ObjectProperty.ContainsZero`,
  `Mathlib.CategoryTheory.ObjectProperty.EpiMono`, and
  `Mathlib.CategoryTheory.ObjectProperty.Extensions` supply the Serre closure API.
* Opposite short exact sequences are formalized in
  `Mathlib.Algebra.Homology.ShortComplex.ShortExact`; the abelian opposite category
  is supplied by `Mathlib.CategoryTheory.Abelian.Opposite`.
-/

@[expose] public section

universe v u

namespace CategoryTheory.ObjectProperty

/-- A Serre class on the opposite of an abelian category induces a Serre class on
the original category. Subobjects and quotients are exchanged, and the endpoints
of a short exact sequence are reversed. -/
theorem IsSerreClass.unop {C : Type u} [Category.{v} C] [Abelian C]
    (P : ObjectProperty Cᵒᵖ) [P.IsSerreClass] : P.unop.IsSerreClass where
  toContainsZero := inferInstance
  prop_of_mono f _ h := P.prop_of_epi f.op h
  prop_of_epi f _ h := P.prop_of_mono f.op h
  prop_X₂_of_shortExact hS h₁ h₃ := P.prop_X₂_of_shortExact hS.op h₃ h₁

end CategoryTheory.ObjectProperty
