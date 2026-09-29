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
audit, including private and generated declarations. The isolated incubator
producer/client received their own independent review, acceptance, exact-input
build and audit. The relocated destination subsequently passed its own native
both-root build and complete private/generated standard-axiom audit at
`3c988935e773c51be6387e3fdb8e1e8a755d3704`, received fresh mapped review,
and was accepted and integrated by Prism on September 29, 2026. This is a
dated code-acceptance statement, not an assertion of release approval or
publication. The earlier isolated evidence alone did not certify the renamed
module origins and expanded destination roots.

This mathematical API is source-independent. Prism developed the bounded
original mathematical exposition, which received independent source-side
review. The original Lean implementation and client are by Formalization
Worker B (Hive Task `hive-request-59643abfde1a8dd0ffae0b74aeb5518528184e0a`,
UID `ebab1c52-31bc-4958-a9b9-dd1e2af1f886`); Formalization Worker A
independently reviewed those isolated results (Hive Task
`hive-request-043c1a45f09fcb84652dcb8d6d12ae7b7ea2d2de`, UID
`6fa72f02-d851-498f-aee8-4153f483fbf9`). This module-name transfer is
by a separate Formalization Worker B Task
`hive-request-91a19ea3ef3b49cdeaf5331d2328a9efccb3dea9`, UID
`cff40757-b7f6-4129-a7e7-c0158508e901`, without a new mathematics proof.
Fresh independent destination review was by Worker A (Hive Task
`hive-request-ea32421a8f837416638c6e19b57c629a30246d9a`, UID
`857dea85-e952-4d2e-aa25-cafa0f1c8a70`); Prism authored the subsequent
lifecycle and credit update, with the mathematical content unchanged.
Source code is subject to this repository's Apache-2.0 `LICENSE`; imported
mathlib retains its own Apache-2.0 authorship and credit.

No Q-comma equivalence, adjunction of layer categories, finite filtration,
Quillen A theorem, dévissage result, or source-level correspondence is
proved or claimed here. Code acceptance and integration are distinct from
the responsible maintainer's and reviewer's exact-revision release decisions.
