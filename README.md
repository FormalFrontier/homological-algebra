# Homological Algebra

Reusable finite Euler invariants for chain and cochain complexes in an abelian
category, and fixed-arrow relative paths for integer cochain maps in a
preadditive category with binary biproducts and pullbacks. The library reuses
mathlib's native short exact sequences, homology and path objects; it has no
source-repository or incubator dependency. Authors: Formal Frontier Agents.
It also provides a chosen-cokernel quotient-intersection pairing for arbitrary
abelian categories, independently of the Euler and path APIs.
Admissible subobject layers now expose a lower-cut left adjoint and reflector
under subobject/product closure and admissibility of the chosen quotient `B/D`.
For native quadrant bicomplexes of modules, it constructs unrestricted signed
product totals and proves all-degree acyclicity from acyclic horizontal rows.
For snake inputs in abelian categories, it supplies exterior maps with kernel
and cokernel universal properties and proves the eight-object sequence exact
at its six interior objects, without assuming either exterior object vanishes.
Licensed under Apache-2.0
(see [LICENSE](LICENSE)).

## Headline results

Building on mathlib's abelian categories, native complexes and homology, the
Euler results apply to `μ : C → Γ`, where `C` is abelian and `Γ` is any additive
commutative group, including groups with torsion. Except where a weaker
assumption is noted, `μ` is additive on every native short exact sequence;
its zero and isomorphism laws follow rather than being assumed.

- **Finite Euler identities, with explicit boundary terms.** For a chain or
  cochain complex and a nonempty integer interval `[a,b]`, the signed term sum
  equals the homology sum **plus** both endpoint-image corrections. The chain
  corrections are `+(-1)^b μ(im d(b+1,b))` and
  `+(-1)^a μ(im d(a,a-1))`; for cochains they are
  `+(-1)^b μ(im d(b,b+1))` and `+(-1)^a μ(im d(a-1,a))`.
  Neighboring zero terms remove these corrections, yielding Euler identities
  and acyclic zero under the stated term bounds; quasi-isomorphism invariance
  requires **both** complexes termwise supported in the same interval.
  [Chain theorem](HomologicalAlgebra/AdditiveEuler.lean),
  [cochain theorem](HomologicalAlgebra/AdditiveEuler/Cochain.lean).
- **Additivity and exact-functor transport.** Native short exact sequences
  of chain complexes give additive term sums even for an empty interval; for
  homology sums, all three complexes must instead be termwise supported in
  the same nonempty interval. A functor preserving finite limits and finite
  colimits transports SES-additive invariants and compares mapped homology;
  the finite homology-sum comparison itself needs no support bound.
  [Exact-sequence and functorial results](HomologicalAlgebra/AdditiveEuler/Functoriality.lean).
- **Finite support and native cochain shifts.** Signed sums over intervals
  separately containing the support agree, even for nonnested or empty
  intervals. The native shift by `n` uses degree `i+n`, moves term support
  `[a,b]` to `[a-n,b-n]`, and translates term and homology sums with factor
  `(-1)^n`. Term-sum reindexing needs neither support nor SES additivity;
  homology-sum translation uses isomorphism invariance from additivity but
  not a term-support bound.
  [Support and shift theorems](HomologicalAlgebra/AdditiveEuler/Shift.lean).
- **Homology-bounded cochain LES additivity.** For a short exact cochain
  sequence `0 → A → B → D → 0`, the middle homology Euler sum equals the two
  outer sums **minus** `(-1)^a μ(im δ_(a-1))` and
  `(-1)^b μ(im δ_b)` for the native connecting maps and nonempty `[a,b]`.
  Vanishing of `H^(a-1)(D)` and `H^(b+1)(A)`, or native `D.IsGE a` and
  `A.IsLE b`, removes the corrections without termwise support or a bound
  on the middle complex.
  [Connecting-image results](HomologicalAlgebra/AdditiveEuler/HomologySupport.lean).
- **Finite module length.** For a commutative **Noetherian Artinian** ring,
  integer-valued length of finitely generated modules is additive on native
  short exact sequences, supplying an Euler invariant. The bare definition
  of `lengthInvariant` does not assert this for arbitrary commutative rings.
  [Length instance](HomologicalAlgebra/AdditiveEuler/Length.lean) and
  [nonsplit cochain client](HomologicalAlgebraTest/AdditiveEuler/HomologySupport.lean).
- **Fixed-arrow cochain relative paths.** Under preadditivity, binary
  biproducts and **pullbacks**, the pullback of a fixed arrow `f : B₁ ⟶ B`
  along mathlib's native first path endpoint has a strict section,
  strict endpoint equations for lifts from *chosen* homotopies, and a
  homotopy equivalence to `B₁` whose inverse homotopy vanishes over the
  first projection. The object depends on `f`, not the chosen source or
  homotopy. This is not a quasi-isomorphism instance or a natural-in-arrow
  framework. [Producer](HomologicalAlgebra/Cochain/RelativePath.lean),
  [ordinary-import client](HomologicalAlgebraTest/Cochain/RelativePath.lean),
  [standalone guide](docs/CochainRelativePath.md).
- **Chosen quotient-intersection pairing.** For subobjects `L ≤ U` and any
  `D` of an object in an abelian category, the specified map
  `U/(L ⊓ D) ⟶ (U/L) × (B/D)` is monic. Its two components are the actual
  chosen `cokernel.map` morphisms, with an aggregate equation after the chosen
  cokernel projection. Neither projection is asserted monic, and no `L ≤ D`
  hypothesis is needed. [Producer](HomologicalAlgebra/Abelian/QuotientIntersection.lean),
  [ordinary-import client](HomologicalAlgebraTest/Abelian/QuotientIntersection.lean),
  [standalone guide](docs/QuotientIntersection.md).
- **Admissible layers and lower-cut reflection.** For a property `P` of the
  chosen quotient `U/L`, layers `(L,U)` are ordered with lower endpoint
  reversed and upper endpoint forward. `LowerBounded P B D` admits a
  monotone inclusion without closure hypotheses or `P(B/D)`; if `P` is
  closed under subobjects and binary products and `P (cokernel D.arrow)`,
  intersection `(L,U) ↦ (L ⊓ D,U)` is its **left** adjoint. The canonical
  monomorphism `U/(L ⊓ D) ⟶ (U/L) × (B/D)` proves admissibility without
  `L ≤ D` or quotient closure. The unit, exact reflector identity and native
  thin-category adjunction are public; no upper cut or transport to layers
  in `D` is asserted. [Producer](HomologicalAlgebra/Abelian/AdmissibleLayers.lean),
  [ordinary-import client](HomologicalAlgebraTest/Abelian/AdmissibleLayers.lean),
  [standalone guide](docs/AdmissibleLayers.md).
- **Snake sequence with exterior objects.** For
  `ShortComplex.SnakeInput C` in any abelian category, the two rows are exact,
  the upper second arrow is epic and the lower first arrow is monic. Maps from
  the kernel of the upper first arrow and to the cokernel of the lower second
  arrow exhibit respectively the kernel of the first and cokernel of the last
  middle arrows. Together with the middle six-term identification and four
  middle exactness positions from Mathlib, these prove exactness at all six
  interior objects of the eight-object sequence. A mod-three example proves
  both exterior objects nonzero and distinguishes the positive connector from
  its negative independently of the endpoint exactness theorem; its combined
  exactness example uses that theorem. This generalizes the abelian-group diagram
  in Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, corrected second
  edition, (1.3.1), without identifying the connector with a separate boundary.
  [Producer](HomologicalAlgebra/Abelian/SnakeLemma.lean),
  [ordinary-import client](HomologicalAlgebraTest/Abelian/SnakeLemma.lean).
- **Quadrant product-total acyclicity.** For any `[Ring R]`, a native quadrant
  bicomplex of `ModuleCat R` has an unrestricted diagonal product total
  `productTotal K` in integer degrees `p-r`. Exact horizontal rows at **every**
  `r`, including `p=0`, give `(productTotal K).Acyclic` in **all integer
  degrees**. At target `(r,p)` of degree `k-1` its differential is
  `h(x_(r,p+1)) + (-1)^(k+1) δ(x_(r-1,p))`, with the second term zero at
  `r=0`; the map, identity and composition laws require no row exactness.
  Elementwise chosen lifts are not linear/natural splittings, and the result
  does not assert an arbitrary-unbounded assembly or exact-products axiom.
  [Producer](HomologicalAlgebra/Homology/ProductTotalAcyclicity.lean),
  [ordinary-import client](HomologicalAlgebraTest/Homology/ProductTotalAcyclicity.lean),
  [standalone guide](docs/ProductTotalAcyclicity.md).

The Euler statements concern finite sums, not an infinite Euler construction,
a canonical invariant from homology bounds alone, or a derived-category or
Grothendieck-group API. The relative-path construction has different,
nonabelian hypotheses and does not depend on an Euler invariant.
The abelian quotient-intersection pairing requires only `L ≤ U`, does not
assume ordinary lifting of maps across quotient epis, and does not depend
on the Euler or relative-path constructions.

## Using the library

Import `HomologicalAlgebra` or the focused public modules
`HomologicalAlgebra.AdditiveEuler` and
`HomologicalAlgebra.AdditiveEuler.Length`, or the exact-sequence and exact-functor
extension `HomologicalAlgebra.AdditiveEuler.Functoriality`, the finite-support
and native cochain-shift module `HomologicalAlgebra.AdditiveEuler.Shift`, the
finite-interval cochain Euler module `HomologicalAlgebra.AdditiveEuler.Cochain`,
or the native long-exact-sequence module
`HomologicalAlgebra.AdditiveEuler.HomologySupport`.
For the separate fixed-arrow path API, import
`HomologicalAlgebra.Cochain.RelativePath` (or the aggregate
`HomologicalAlgebra`); see [the guide](docs/CochainRelativePath.md).
For the chosen quotient-intersection pairing, import
`HomologicalAlgebra.Abelian.QuotientIntersection` (or `HomologicalAlgebra`);
the public declarations are in `CategoryTheory.Subobject`. See
[the guide](docs/QuotientIntersection.md) for the exact cokernel squares,
the `quotientIntersectionPair_fac` equation and a native closure client.
For quotient-admissible subobject layers and their lower-cut reflector, import
`HomologicalAlgebra.Abelian.AdmissibleLayers` (or `HomologicalAlgebra`). The
`CategoryTheory.AdmissibleLayer` API builds on that pairing; see
[the guide](docs/AdmissibleLayers.md) for hypotheses and client examples.
For the distinct quadrant product-total API, import
`HomologicalAlgebra.Homology.ProductTotalAcyclicity` (or `HomologicalAlgebra`);
its declarations live in `CategoryTheory.QuadrantProductTotal`. See
[the guide](docs/ProductTotalAcyclicity.md) for signs, row exactness at the
boundary, negative-degree primitives and the ordinary-import client.
For the snake endpoint maps and eight-object exact sequence, import
`HomologicalAlgebra.Abelian.SnakeLemma` (or `HomologicalAlgebra`); its declarations
live in `CategoryTheory.ShortComplex.SnakeInput`. The sequence is exact at its
six interior objects without asserting that either exterior object vanishes.
For the Euler declarations, boundary formulas, support and shift conventions,
and checked examples, see [Finite Euler invariants](docs/AdditiveEuler.md).
The guide distinguishes termwise support from neighboring homology bounds,
including the nonsplit and torsion-valued clients.

### Non-Euler checked examples

`HomologicalAlgebraTest.Cochain.RelativePath`, also built by default, checks
eight ordinary-import examples for two distinct sources/chosen homotopies
into the same fixed-arrow object, strict endpoint equations, the native
path-component law, the relative contraction and literal equivalence maps.
`HomologicalAlgebraTest.Abelian.QuotientIntersection`, also built by default,
checks the chosen components, aggregate equation, monicity and native
subobject/product closure transfer, plus boundary and representative cases.
`HomologicalAlgebraTest.Homology.ProductTotalAcyclicity`, also built by default,
uses zero vertical maps and a nonsplit `ℤ → ZMod 2` row, testing signs at
`-1,0,1`, a negative-degree early primitive and map identity. Its nonsplit
row repeats infinitely often overall, but with zero vertical maps and at most
three nonzero cells on each diagonal. The client does not test infinitely
supported diagonals or nonzero vertical maps.
`HomologicalAlgebraTest.Abelian.SnakeLemma`, also built by default, checks
the endpoint arrow equations and their factorization through an ordinary import;
it independently establishes exact rows, nonzero exterior objects and a
positive connector different from its negative modulo three. Its full
eight-object exactness example uses the proved endpoint theorem.

## Building and checking

Use the repository's pinned `lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`)
and `lake-manifest.json` (mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`). Only mathlib is a direct
Lake dependency, resolved from GitHub. From the project root:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
env LEAN_NUM_THREADS=2 lake exe cache get
env LEAN_NUM_THREADS=2 lake --wfail build
```

The default build elaborates all eleven library modules, both root imports and
the ten public-import test modules. On a host with a matching mathlib cache,
budget seconds to a few minutes and up to 8 GiB memory as *planning estimates*,
not measured peak usage, a minimum, guaranteed requirements or permission
for a particular support profile. `LEAN_NUM_THREADS=2` limits Lean runtime
threading, not aggregate Lake process count or memory. Project-wide elapsed
time and peak memory have not been measured. First-time cache retrieval
downloads thousands of files and varies with network and storage; do not run
a full mathlib source build if the cache fetch fails.

## Provenance and limits

Prism wrote the original Euler, exact-functor, LES, relative-path and
quotient-intersection mathematical expositions, distinct from the original
Lean proof authors. The [contributor credits](CREDITS.md)
distinguish proof, independent mathematical/code review, admissible-layer
repair and documentation contributions and preserve upstream Mathlib notices.
Formal Frontier Agents developed this work with AI assistance.

The work does **not** establish the K₀ presentation,
general homologically-bounded Euler identities, arbitrary-arrow path
naturality, unrestricted long-exact-sequence theory beyond the finite-interval
cochain formula, a derived-category result or completion of a source.

## References

- Charles A. Weibel, *The K-book*, Chapter II, §6: motivates the adapted
  SES-additive formulation and finite Euler argument.
- Jürgen Neukirch, Alexander Schmidt and Kay Wingberg, *Cohomology of Number
  Fields*, corrected second edition, (1.3.1): the abelian-group snake diagram
  motivates the eight-object sequence in arbitrary abelian categories.
- Mathlib's native short exact sequences, homology, shifts and path objects;
  `CategoryTheory.ShortComplex.SnakeInput.snake_lemma` provides the middle
  six-term snake sequence.
