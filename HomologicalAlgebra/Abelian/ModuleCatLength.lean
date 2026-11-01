/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Abelian.Length
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.RingTheory.Length

/-!
# Object length and module length

The canonical order isomorphism between categorical subobjects and submodules
identifies object length with module length over any ring. The ring and module
carrier universes are independent.

## References

This comparison uses Mathlib's `ModuleCat.subobjectModule` from
`Algebra.Category.ModuleCat.Subobject`, `Order.height_orderIso` from
`Order.KrullDimension`, and `Module.length_eq_height` from `RingTheory.Length`.
-/

@[expose] public section

universe u v

namespace ModuleCat

/-- Categorical object length agrees with module length over any ring. -/
theorem objectLength_eq_moduleLength {R : Type u} [Ring R] (M : ModuleCat.{v} R) :
    CategoryTheory.objectLength M = Module.length R M := by
  rw [CategoryTheory.objectLength_eq_height, Module.length_eq_height]
  simpa only [map_top] using
    (Order.height_orderIso (subobjectModule M) (⊤ : CategoryTheory.Subobject M)).symm

end ModuleCat
