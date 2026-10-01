# A quotient–intersection comparison in an abelian category

Let `C` be an abelian category, `B : C`, and `L U D : Subobject B` with
`h : L ≤ U`. There is **no** assumption `L ≤ D`. All subobjects here use
mathlib's chosen representatives; `ofLE X Y h` is the actual morphism from
the representative of `X` to that of `Y`. Put `T = L ⊓ D` and
`j = ofLE T U ((inf_le_left L D).trans h)`. The definition
`CategoryTheory.Subobject.quotientIntersectionPair L U D h` is the map

```text
cokernel j ⟶ cokernel (ofLE L U h) ⨯ cokernel D.arrow
```

whose first projection is exactly the `cokernel.map` of the square
`j ≫ 𝟙 = ofLE T L _ ≫ ofLE L U h`; its second projection is exactly the
`cokernel.map` of `j ≫ U.arrow = ofLE T D _ ≫ D.arrow`. The lemmas
`quotientIntersectionPair_fst` and `quotientIntersectionPair_snd` give these
chosen components, not merely maps between isomorphic quotient objects.
The aggregate equation `quotientIntersectionPair_fac` reads

```text
cokernel.π j ≫ quotientIntersectionPair L U D h =
  prod.lift (cokernel.π (ofLE L U h)) (U.arrow ≫ cokernel.π D.arrow)
```

The instance `mono_quotientIntersectionPair` proves that **this very map** is
monic. It works in any `C : Type u` with `[Category.{v} C] [Abelian C]`;
no extra smallness or module hypothesis is required. The category supplies
products, kernels, cokernels and zero morphisms. Neither individual projection
is asserted monic.

## Proof and usage

The inclusion `j` is the kernel of the displayed product-valued map from
`U`. A morphism annihilated by its first component factors through `L → U`
using normality of that mono; the second component factors its composite with
`U.arrow` through `D → B`. The `L` and `D` lifts agree in `B`, so the pullback
representing `L ⊓ D` gives their common lift through `j`. The cokernel of
this *actual* kernel is canonically isomorphic to the native coimage. Both
inverse maps between the chosen cokernels are verified after their epi
projections. Cancelling the quotient epi identifies the chosen paired map
with the coimage isomorphism followed by mathlib's monic
`Abelian.factorThruCoimage`. This argument does **not** assume that maps into
a quotient lift to ordinary maps into its numerator.

An ordinary-import client can use the map to transfer a property of the two
target quotients to the source. For example, if `P : ObjectProperty C` is
closed under subobjects and binary products, then

```lean
exact P.prop_of_mono (quotientIntersectionPair L U D h)
  (P.prop_prod _ _ hL hD)
```

where `hL : P (cokernel (ofLE L U h))` and
`hD : P (cokernel D.arrow)`. No membership of `L`, `U` or `D`, quotient
closure, extension closure, or Serre hypothesis is used. In this example,
`P.prop_prod` and `P.prop_of_mono` are native mathlib results, not extra
library wrappers. Native `Subobject.inf_isPullback` supplies the intersection
pullback, `Abelian.monoLift` supplies normal-mono lifts, and
`Limits.cokernel.map` and `cokernel.mapIso` supply chosen quotient maps and
representative transport. Native `Abelian.mono_cokernel_map_of_isPullback`
addresses a different, single-component cut-upper map and is not duplicated.

The ordinary-import test checks these laws, the predicate application, the
specializations `D = ⊤`, `D = ⊥`, `L = ⊥`, `L = U`, and an initial/zero
ambient object. It also checks a native quotient isomorphism for changing
the representative of `D`. Such checks do not assert that differently
chosen cokernels are definitionally equal.

## Reproduce and scope

Import `HomologicalAlgebra.Abelian.QuotientIntersection` for the focused
producer or `HomologicalAlgebra` for the public aggregate. The ordinary
client `HomologicalAlgebraTest.Abelian.QuotientIntersection` is included by
`HomologicalAlgebraTest` in the default build. Use this repository's pinned
Lean `leanprover/lean4:v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and full
`lake-manifest.json`. From the destination project root:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake --wfail build
```

Fetch the matching mathlib cache successfully **before** building. Both
producer and client are imported by their corresponding default roots.
A successful build does not replace the complete transitive standard-axiom
audit, including private and generated declarations. Prism wrote the bounded
mathematical exposition and chose the library home. The Formal Frontier
cochain-shift and path contributor authored the original isolated Lean proof
and ordinary client, then performed a separate mathematics-preserving
module-name transfer; the core and LES contributor independently reviewed the
original and destination versions. Prism accepted the code and later edited
lifecycle prose. Release status belongs to the responsible maintainer's
exact-revision records. Original project code uses this repository's
[Apache-2.0 license](../LICENSE); imported mathlib retains independent
upstream authorship and Apache-2.0 credit. No source asset or source-level
correspondence is included.

No Q-comma equivalence, adjunction of layer categories, finite filtration,
Quillen A theorem, dévissage result, or source-level correspondence is
proved or claimed here.
