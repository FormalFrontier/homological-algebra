/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Abelian.NoetherianObject
public import HomologicalAlgebra.Abelian.ArtinianObject
public import HomologicalAlgebra.Abelian.SerreClass
public import Mathlib.CategoryTheory.ObjectProperty.Extensions

/-!
# Noetherian and Artinian binary biproducts

In an abelian category, binary biproducts of Noetherian objects are Noetherian,
and binary biproducts of Artinian objects are Artinian. Each statement uses only
the corresponding chain condition on the two factors. Object and morphism
universes are independent.

## References

These statements use Mathlib's categorical object properties, Noetherian and
Artinian subobject APIs, and extension-to-biproduct interface, together with the
library's categorical Noetherian, Artinian and Serre-class modules.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A binary biproduct of Noetherian objects in an abelian category is Noetherian. -/
instance isNoetherianObject_biprod (X Y : C)
    [IsNoetherianObject X] [IsNoetherianObject Y] : IsNoetherianObject (X ⊞ Y) := by
  exact ObjectProperty.is_of_prop isNoetherianObject
    (ObjectProperty.prop_biprod isNoetherianObject
      (ObjectProperty.prop_of_is isNoetherianObject X)
      (ObjectProperty.prop_of_is isNoetherianObject Y))

/-- A binary biproduct of Artinian objects in an abelian category is Artinian. -/
instance isArtinianObject_biprod (X Y : C)
    [IsArtinianObject X] [IsArtinianObject Y] : IsArtinianObject (X ⊞ Y) := by
  exact ObjectProperty.is_of_prop isArtinianObject
    (ObjectProperty.prop_biprod isArtinianObject
      (ObjectProperty.prop_of_is isArtinianObject X)
      (ObjectProperty.prop_of_is isArtinianObject Y))

end CategoryTheory
