/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import HomologicalAlgebra.Abelian.AdmissibleLayers

/-!
Ordinary-import regression client for admissible lower-cut layers. In particular,
the public endpoint equations are used from outside the producer's module, and
inclusion monotonicity is checked without either closure instance or `P(B/D)`.
Prism authored this ordinary-import client, which imports the producer's
public API without relying on its internal implementation.
-/

universe v u

noncomputable section

namespace CategoryTheory.AdmissibleLayerTest

open Limits AdmissibleLayer

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {P : ObjectProperty C} {B : C} (D : Subobject B)

example : Monotone (lowerInclusion (P := P) D) := lowerInclusion_monotone D

example (x y : AdmissibleLayer P B) :
    x ≤ y ↔ y.lower ≤ x.lower ∧ x.upper ≤ y.upper := Iff.rfl

variable [P.IsClosedUnderSubobjects] [P.IsClosedUnderBinaryProducts]
variable (hD : P (cokernel D.arrow))

example (x : AdmissibleLayer P B) : (lowerCut D hD x).val.lower = x.lower ⊓ D :=
  lowerCut_lower D hD x

example (x : AdmissibleLayer P B) : (lowerCut D hD x).val.upper = x.upper :=
  lowerCut_upper D hD x

example (x : AdmissibleLayer P B) : (lowerCut D hD x).val.lower ≤ D :=
  (lowerCut D hD x).property

example (x : AdmissibleLayer P B) :
    P (cokernel (Subobject.ofLE (lowerCut D hD x).val.lower
      (lowerCut D hD x).val.upper (lowerCut D hD x).val.lower_le_upper)) :=
  (lowerCut D hD x).val.admissible

example (x : AdmissibleLayer P B) (y : LowerBounded P B D) :
    lowerCut D hD x ≤ y ↔ x ≤ lowerInclusion D y :=
  lowerCut_galoisConnection D hD x y

example : Monotone (lowerCut (P := P) D hD) := lowerCut_monotone D hD

example (x : AdmissibleLayer P B) : x ≤ lowerInclusion D (lowerCut D hD x) :=
  le_lowerInclusion_lowerCut D hD x

example (y : LowerBounded P B D) : lowerCut D hD (lowerInclusion D y) = y :=
  lowerCut_lowerInclusion D hD y

example : (lowerCut_galoisConnection (P := P) D hD).monotone_l.functor ⊣
    (lowerCut_galoisConnection (P := P) D hD).monotone_u.functor :=
  lowerCutAdjunction D hD

end CategoryTheory.AdmissibleLayerTest

end
