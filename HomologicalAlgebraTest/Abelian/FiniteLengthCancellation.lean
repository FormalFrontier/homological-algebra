/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import HomologicalAlgebra

/-!
# Zero-summand cancellation

Finite-length cancellation includes zero objects, whose endomorphism rings
are not local. The remaining objects are unrestricted.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

example {C : Type u} [Category.{v} C] [Abelian C] (O Y Z : C) (hO : IsZero O)
    (e : O ⊞ Y ≅ O ⊞ Z) : Nonempty (Y ≅ Z) :=
  @CategoryTheory.nonempty_iso_of_biprod_iso_of_isNoetherianObject_of_isArtinianObject.{u, v}
    C _ _ O Y Z (isNoetherianObject_of_isZero hO) (isArtinianObject_of_isZero hO) e
