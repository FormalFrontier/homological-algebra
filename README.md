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
`HomologicalAlgebra.AdditiveEuler.Length`. The namespace is
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

`lengthInvariant R` on `FGModuleCat R` is the integer cast of finite module
length. `lengthInvariant_ses R` requires a commutative, Noetherian, Artinian
ring: these hypotheses make lengths finite **before** `ENat.toNat` additivity.
The standalone definition has no SES-additivity guarantee over other rings.
`HomologicalAlgebraTest.AdditiveEuler`, built by default, imports only the
public library. Its rational one-dimensional complex in degree `-1` has Euler
value `-1`; additive postcomposition into `ZMod 3` yields `2`, different from
zero and one.

## Building and checking

Use the repository's pinned `lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`)
and `lake-manifest.json` (mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`). Only mathlib is a direct
Lake dependency, resolved from GitHub. From the project root:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
env LEAN_NUM_THREADS=2 lake --wfail build
```

The default build checks the two library modules, both root imports and the
public-import test module. With the matching mathlib cache already available,
this transfer's warning-fatal build took 6 seconds for 2,076 Lake jobs with
`LEAN_NUM_THREADS=2` on the author Task after fetching the full matching cache.
An earlier incubator build of the same mathematical unit also comprised 2,076
jobs; its full elapsed time and peak memory were not measured. For other
comparable cached hosts, budget seconds to a few minutes and up to 8 GiB memory
as *planning estimates*, not guaranteed requirements. First-time cache retrieval
downloads thousands of files and varies with network and storage; do not run
a full mathlib source build if the cache fetch fails. Verification of this
candidate's actual build and transitive axiom audit is recorded in its private
development issue rather than shipped as logs or a custom checker.

## Provenance and limits

The mathematical motivation is Charles A. Weibel, *The K-book*, Chapter II,
§6: its SES-additive function and Euler argument. Prism authored the expanded
original proof exposition; Formalization Worker A developed the native Lean
proof and finite-length/negative-degree clients. This promotion retains their
work and contributor credit. Precise passage correspondence and source-coverage
decisions belong to the source-maintainer record; this release does **not**
claim the K₀ presentation, a homologically-bounded abelian category, a long
exact sequence, an exact-functor/degreewise-SES extension, or completion of a
source. The source PDF is not distributed.

Project contact: [FormalFrontier on GitHub](https://github.com/FormalFrontier).
