# Homological Algebra

Reusable additive Euler invariants for integer-indexed chain complexes in an
abelian category. The library uses mathlib's native short exact sequences,
images, cycles, homology and quasi-isomorphisms; it has no source-repository or
incubator dependency. Authors: Formal Frontier Agents. Licensed under Apache-2.0
(see [LICENSE](LICENSE)). Review, acceptance and publication are recorded for
exact revisions; development branches are not official releases.

## Using the library

Import `HomologicalAlgebra` or the focused public modules
`HomologicalAlgebra.AdditiveEuler` and
`HomologicalAlgebra.AdditiveEuler.Length`, or the exact-sequence and exact-functor
extension `HomologicalAlgebra.AdditiveEuler.Functoriality`, or the finite-support
and native cochain-shift module `HomologicalAlgebra.AdditiveEuler.Shift`. The namespace is
`CategoryTheory.AdditiveEuler`. For `μ : C → Γ` in an abelian category `C` and
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
across the isomorphism). No cochain Euler–Poincaré identity, derived-category
identity or K₀ presentation follows from these statements.

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

## Building and checking

Use the repository's pinned `lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`)
and `lake-manifest.json` (mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`). Only mathlib is a direct
Lake dependency, resolved from GitHub. From the project root:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
env LEAN_NUM_THREADS=2 lake exe cache get
env LEAN_NUM_THREADS=2 LAKE_JOBS=2 lake --wfail --no-ansi build
```

The default build checks all four library modules, both root imports and the
three public-import test modules. On a host with a matching mathlib cache,
budget seconds to a few minutes and up to 8 GiB memory as *planning estimates*,
not guaranteed requirements. First-time cache retrieval downloads thousands of
files and varies with network and storage; do not run a full mathlib source
build if the cache fetch fails. Build and transitive axiom evidence belongs to
the exact-revision development record, not a bundled validation framework.

## Provenance and limits

The mathematical motivation is Charles A. Weibel, *The K-book*, Chapter II,
§6: its SES-additive function and Euler argument. Prism authored the expanded
original proof exposition, including exact-sequence and exact-functor guidance;
Formalization Worker A developed the core, finite-length and exact-functor Lean
proofs and clients, and independently reviewed the native cochain-shift proof.
Formalization Worker B developed the native cochain-shift Lean proofs and clients
and independently reviewed the exact-sequence/exact-functor component.
The upstream mathlib `Single` development credits Kim Morrison (2021),
`SingleHomology` credits Joël Riou (2023), and `ShiftSequence` credits Joël Riou
(2024). Review and publication of this transfer are separate,
revision-specific decisions. Precise passage correspondence and
source-coverage decisions belong to the source-maintainer record. This library
does **not** claim the K₀ presentation, a homologically-bounded abelian
category, a cochain Euler–Poincaré formula, a derived-category result, a long
exact sequence or completion of a source. The source PDF is
not distributed.

Project contact: [FormalFrontier on GitHub](https://github.com/FormalFrontier).
