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
Licensed under Apache-2.0
(see [LICENSE](LICENSE)). Review, acceptance and publication are recorded for
exact revisions; development branches are not official releases.

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
The additive Euler namespace is `CategoryTheory.AdditiveEuler` (the path
construction uses `CochainComplex.RelativePath`). For `μ : C → Γ` in an abelian category `C` and
additive commutative group `Γ`, the sole invariant hypothesis is

```text
∀ S : ShortComplex C, S.ShortExact → μ S.X₂ = μ S.X₁ + μ S.X₃.
```

`invariant_zero`, `invariant_iso` and `invariant_of_isZero` follow from this
hypothesis; neither zero normalization nor isomorphism invariance is assumed.
The native `cycles_image_shortExact` and `image_cycles_shortExact` yield
`local_decomposition`. `euler_endpoints μ hμ K a b hab` gives the signed
integer-interval term sum as the homology sum **plus both endpoint-image
terms**, including for negative and singleton intervals. `euler_eq_homology`
removes the endpoint terms when adjacent terms are zero;
`euler_eq_homology_of_bounded` assumes every term outside `[a,b]` is zero.
`euler_acyclic` and `euler_quasiIso` supply acyclic zero and bounded
quasi-isomorphism invariance, respectively; the quasi-isomorphism theorem
requires **both** complexes to vanish outside the same interval.
`postcompose_ses` transports SES additivity along an additive-group homomorphism.
These are finite signed sums, not an Euler construction for arbitrary
homologically bounded complexes or an infinite sum.

For cochain complexes, `cochain_euler_endpoints` identifies the finite-interval
signed term sum with the cohomology sum plus **both** boundary-image terms:
the outgoing image at `b` has sign `(-1)^b` and the incoming image at `a` has
sign `(-1)^a`. Duality reverses arrows, not integer degrees.
`cochain_euler_eq_homology` drops these terms when the neighboring terms vanish;
`cochain_euler_eq_homology_of_bounded` uses termwise support in `[a,b]`.
`cochain_euler_acyclic` gives zero for an acyclic cochain complex with vanishing
neighboring terms. `cochain_euler_quasiIso` requires **both** complexes to be
termwise supported in the same interval. These theorems retain arbitrary
abelian categories and additive-commutative-group-valued SES-additive invariants.

For a short exact sequence `S` of cochain complexes, the native connecting map
`δᵢ : Hⁱ(S.X₃) ⟶ Hⁱ⁺¹(S.X₁)` defines `cochain_homology_boundary_image S hS i`
as its image. `invariant_exact_pair_images` applies SES additivity to an exact
pair without requiring it to be short exact.
`cochain_homology_local_additivity` expresses the invariant of each middle
homology object as the sum for the outer two **minus both** neighboring
connecting-image invariants. `cochain_homology_euler_endpoints` telescopes these
corrections for every finite interval `a ≤ b`, including singleton and negative
intervals; the incoming correction has sign `-(-1)^a` at `a-1` and the outgoing
one sign `-(-1)^b` at `b`. It makes no empty-interval claim.
`cochain_homology_sum_additive_of_endpoints` removes the corrections when only
`H^(a-1)(S.X₃)` and `H^(b+1)(S.X₁)` are zero, respectively;
`cochain_homology_sum_additive_of_supported` derives this from the native
homological bounds `S.X₃.IsGE a` and `S.X₁.IsLE b`. Neither theorem needs a
termwise support bound or a bound on the middle complex. They do not provide a
canonical interval-independent invariant or a general long-exact-sequence
formalization for arbitrary degrees or unbounded sums.

`term_sum_additive_of_shortExact` applies native degreewise exactness to the
signed term sums of a short exact sequence of chain complexes on **any** integer
interval, including an empty interval; it needs no support bound.
`homology_sum_additive_of_shortExact` applies when the interval is nonempty and
**all three** complexes have zero terms outside it. It does not assert that their
homologies form a short exact sequence. `precompose_exact_ses` transports the
SES-additivity of `ν` along a functor `F` preserving finite limits and finite
colimits. `map_homology_iso` is the native comparison between homology of the
mapped complex and the image of homology under `F`;
`invariant_map_homology` and `homology_sum_map` give invariant values and finite
signed sums via this isomorphism, without support assumptions.
`map_termwise_bounded` only needs `F.PreservesZeroMorphisms`, whereas
`euler_map_bounded` uses exactness and a common term-support interval to identify
the mapped term sum with both the mapped homology sum and the sum of images of
the original homology.

`signed_sum_eq_of_support` equates finite signed sums over any two intervals,
even empty or nonnested ones, **provided each interval separately contains the
support** of the function. If either interval is empty, its support hypothesis
forces that function to vanish. `signed_sum_translate` reindexes an arbitrary
signed sum from `[a,b]` to `[a-n,b-n]` with factor `(-1)^n`, without a support
or additivity hypothesis. These identities work for any additive commutative
group, including groups with torsion. `term_sum_eq_of_support` transports the
two separate support hypotheses to zero terms of a chain or cochain complex;
it uses SES additivity solely to infer that the invariant vanishes on zero
objects.

For the **native** cochain shift `K⟦n⟧`,
`cochain_shift_term_support` transports a zero-term support bound `[a,b]` to
`[a-n,b-n]` in degrees `i` corresponding to the original degree `i+n`.
`cochain_shift_term_sum` reindexes the actual shifted terms without either
support or SES-additivity. `cochain_shift_homology_iso` is the actual native
isomorphism `(K⟦n⟧).homology i ≅ K.homology (i+n)`;
`cochain_shift_homology_sum` uses it to translate homology sums without a
term-support hypothesis (but requires SES additivity to preserve the invariant
across the isomorphism). The separate finite-interval cochain Euler identities
above require their stated boundary or term-support hypotheses; neither family
provides a homology-only bounded Euler construction, a derived-category identity
or a K₀ presentation.

`lengthInvariant R` on `FGModuleCat R` is the integer cast of finite module
length. `lengthInvariant_ses R` requires a commutative, Noetherian, Artinian
ring: these hypotheses make lengths finite **before** `ENat.toNat` additivity.
The standalone definition has no SES-additivity guarantee over other rings.
`HomologicalAlgebraTest.AdditiveEuler`, built by default, imports only the
public library. Its rational one-dimensional complex in degree `-1` has Euler
value `-1`; additive postcomposition into `ZMod 3` yields `2`, different from
zero and one.
`HomologicalAlgebraTest.AdditiveEuler.Functoriality` constructs the native split
short exact sequence `K --id→ K → 0` for that same degree-`-1` complex, checks
its signed term and homology identities in `ZMod 3`, and tests the mapped sums
under the **exact identity functor**. These examples do not claim a nonsplit
sequence or a nonidentity exact functor.
`HomologicalAlgebraTest.AdditiveEuler.Shift` checks a rational-line singleton
in cochain degree `-1`: its signed term and homology sums equal `2` in
`ZMod 3`, while shifts by `+1` and `-1` give signed values `1`. It also checks
an enlarged interval, an empty interval and native shifted term support.
`HomologicalAlgebraTest.AdditiveEuler.Cochain` checks negative and shifted
`ZMod 3` cohomology sums and a genuine two-term cochain complex whose
identity differential has a nonzero image: both singleton endpoint corrections
and full-interval cancellation are exercised. The identity quasi-isomorphism
is only a smoke test, not a nontrivial quasi-isomorphism example.
`HomologicalAlgebraTest.AdditiveEuler.HomologySupport` constructs a genuinely
nonsplit rational short exact sequence with identity-differential middle complex
and nonzero native connecting map. It checks the singleton `[0,0]` correction
`0 = 1 - 1`, a separate nonzero correction on `[-1,0]`, and signed additivity
`0 = -1 + 1` on `[0,1]` under neighboring homology vanishing and native support
bounds. Its shifted `ZMod 3` client checks the negative interval `[-2,-1]`
with `0 = 2 + 1` using an explicitly SES-additive modular invariant.
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

The default build checks all ten library modules, both root imports and the
nine public-import test modules. On a host with a matching mathlib cache,
budget seconds to a few minutes and up to 8 GiB memory as *planning estimates*,
not measured peak usage, a minimum, guaranteed requirements or permission
for a particular support profile. `LEAN_NUM_THREADS=2` limits Lean runtime
threading, not aggregate Lake process count or memory. Project-wide elapsed
time and peak memory have not been measured. First-time cache retrieval
downloads thousands of files and varies with network and storage; do not run
a full mathlib source build if the cache fetch fails. Build and transitive
axiom evidence belongs to
the exact-revision development record, not a bundled validation framework.

## Provenance and limits

Charles A. Weibel's *The K-book*, Chapter II, §6 motivates the adapted
SES-additive formulation and finite Euler argument. Prism wrote the expanded
original Euler, exact-functor, LES, relative-path and quotient-intersection
mathematical expositions, selected their library homes and accepted the
reviewed contributions. Original Lean authorship is distinct: one contributor
proved the core, finite-length and exact-functor Euler results and clients and
later the cochain LES formula and its genuinely nonsplit clients; another
contributor proved the native cochain shift, finite support and finite-interval
cochain Euler results and clients. These contributors independently reviewed
one another's respective components. The original native fixed-arrow path and
chosen-cokernel quotient-intersection proofs and ordinary clients are by the
latter contributor, with independent mathematical/code review by the former.
Separate module-name transfers and aggregation mapped the accepted mathematics
into this library without claiming new proofs. Folio prepared the first five
README headline groups, a documentation contribution rather than proof
or theorem authorship.

The original quadrant product-total mathematical assembly, native Lean proof,
ordinary client and aggregate registration are by the core/LES contributor;
the cochain-shift contributor independently reviewed the mathematics and
code and later performed the bounded destination module-name transfer. Prism
selected the home, accepted the work and edited lifecycle prose, but is **not**
the original product-total proof author. The original admissible-layer Lean
construction and lower-cut interfaces are by the core/LES contributor; Prism
repaired the proof, exposed its exported equations and wrote the ordinary
client. The accepted destination transfers had distinct independent reviews
before Prism's code acceptance. Code acceptance, independent release review,
verified publication and source correspondence are separate decisions; consult
the exact-revision release records for current publication status.

Upstream mathlib retains its own authorship and Apache-2.0 license: `Single`
credits Kim Morrison (2021); `SingleHomology` and `HomotopyFiber` credit Joël
Riou (2023); `ShiftSequence` credits Joël Riou (2024); opposite-complex work
credits Johan Commelin, Amelia Livingston and Joël Riou (2022). The original
project code is licensed under this repository's [Apache-2.0 license](LICENSE)
and credited collectively to Formal Frontier Agents. No external source asset
is redistributed. The work does **not** establish the K₀ presentation,
general homologically-bounded Euler identities, arbitrary-arrow path
naturality, unrestricted long-exact-sequence theory beyond the finite-interval
cochain formula, a derived-category result or completion of a source.
