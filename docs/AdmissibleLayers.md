# Admissible layers and the lower-cut reflector

Import `HomologicalAlgebra.Abelian.AdmissibleLayers` for the focused API, or
`HomologicalAlgebra` for the aggregate library. Declarations are in
`CategoryTheory.AdmissibleLayer` (the layer structure itself is
`CategoryTheory.AdmissibleLayer`). The ordinary-import examples live in
[`HomologicalAlgebraTest/Abelian/AdmissibleLayers.lean`](../HomologicalAlgebraTest/Abelian/AdmissibleLayers.lean).

## Chosen quotients and order

Let `C` be an abelian category, `P : ObjectProperty C`, and `B : C`. A layer
`x : AdmissibleLayer P B` contains subobjects `x.lower = L` and `x.upper = U`
with `x.lower_le_upper : L ≤ U`. Its `x.admissible` is the assertion

```lean
P (cokernel (Subobject.ofLE L U x.lower_le_upper))
```

for the **chosen** quotient `U/L`. Neither endpoint is required to satisfy
`P`. Layers have the partial order

```lean
x ≤ y ↔ y.lower ≤ x.lower ∧ x.upper ≤ y.upper
```

so the lower endpoint moves backwards while the upper endpoint moves forwards.
For `D : Subobject B`, `LowerBounded P B D` is the ordered subtype of layers
whose lower endpoint is at most `D`. The map `lowerInclusion D` forgets that
bound; `lowerInclusion_monotone D` requires **no** closure assumptions on `P`
and no proof about `B/D`.

## Intersecting the lower endpoint

Assume `[P.IsClosedUnderSubobjects]`, `[P.IsClosedUnderBinaryProducts]`, and
`hD : P (cokernel D.arrow)`. Then `lowerCut D hD` sends `(L,U)` to the
lower-bounded layer `(L ⊓ D,U)`. The canonical map

```text
U/(L ⊓ D) ⟶ (U/L) × (B/D)
```

is the actual monomorphism `Subobject.quotientIntersectionPair` supplied by
[`HomologicalAlgebra.Abelian.QuotientIntersection`](QuotientIntersection.md).
The constructor applies `P.prop_prod` to the admissible chosen quotient
`U/L` and `hD`, then `P.prop_of_mono` to this map. It also uses
`L ⊓ D ≤ L ≤ U` and `L ⊓ D ≤ D`. It does **not** require `L ≤ D`, closure
under quotients, or admissibility of `B`, `D`, `L` or `U` separately.

The `[simp]` endpoint equations `lowerCut_lower` and `lowerCut_upper` expose
`L ⊓ D` and `U`. For a lower-bounded `y`, the Galois law is

```lean
lowerCut D hD x ≤ y ↔ x ≤ lowerInclusion D y
```

(`lowerCut_galoisConnection D hD x y`). In the reverse direction, the
bound `y.val.lower ≤ D` converts `y.val.lower ≤ x.lower` into
`y.val.lower ≤ x.lower ⊓ D`. Thus the cut is the **left** adjoint to
inclusion. `lowerCut_monotone` proves monotonicity;
`le_lowerInclusion_lowerCut` is the unit inequality
`x ≤ lowerInclusion D (lowerCut D hD x)`. The `[simp]` equation
`lowerCut_lowerInclusion` proves `lowerCut D hD (lowerInclusion D y) = y`
for every already bounded `y` (the reflector identity).
`lowerCutAdjunction` is the native adjunction between the functors on the
associated thin categories obtained from the same Galois connection.

## Ordinary-import use

The following types and proofs are exercised through an ordinary producer
import by the [client](../HomologicalAlgebraTest/Abelian/AdmissibleLayers.lean):

```lean
module
import HomologicalAlgebra.Abelian.AdmissibleLayers

universe v u
noncomputable section
namespace CategoryTheory.AdmissibleLayerTest
open Limits AdmissibleLayer

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {P : ObjectProperty C} {B : C} (D : Subobject B)

example : Monotone (lowerInclusion (P := P) D) := lowerInclusion_monotone D

variable [P.IsClosedUnderSubobjects] [P.IsClosedUnderBinaryProducts]
variable (hD : P (cokernel D.arrow))

example (x : AdmissibleLayer P B) : (lowerCut D hD x).val.lower = x.lower ⊓ D :=
  lowerCut_lower D hD x

example (x : AdmissibleLayer P B) (y : LowerBounded P B D) :
    lowerCut D hD x ≤ y ↔ x ≤ lowerInclusion D y :=
  lowerCut_galoisConnection D hD x y

example (y : LowerBounded P B D) : lowerCut D hD (lowerInclusion D y) = y :=
  lowerCut_lowerInclusion D hD y

example : (lowerCut_galoisConnection (P := P) D hD).monotone_l.functor ⊣
    (lowerCut_galoisConnection (P := P) D hD).monotone_u.functor :=
  lowerCutAdjunction D hD

end CategoryTheory.AdmissibleLayerTest
end
```

The client also checks the order direction, upper endpoint, lower bound,
actual chosen quotient admissibility, monotonicity of the cut and the unit.
The focused API adds no upper cut, transport to layers in the object `D`,
Q-comma equivalence, filtration, K-theory result or source correspondence.
