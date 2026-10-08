# Finite Euler invariants

Finite signed Euler sums for chain and cochain complexes in an abelian category,
with values in an arbitrary additive commutative group. This includes torsion
coefficients. The formulas below distinguish term-support assumptions from
neighboring homology bounds and retain their endpoint and connecting-image terms.
For the other library results and build instructions, see the [README](../README.md).

## Imports and module navigation

Import `HomologicalAlgebra` for the whole library, or the focused modules below.
The Euler declarations lie in `CategoryTheory.AdditiveEuler`.

| Module | Purpose |
| --- | --- |
| [`HomologicalAlgebra.AdditiveEuler`](../HomologicalAlgebra/AdditiveEuler.lean) | Chain Euler identities and boundary-image corrections. |
| [`HomologicalAlgebra.AdditiveEuler.Cochain`](../HomologicalAlgebra/AdditiveEuler/Cochain.lean) | Cochain Euler identities and boundary-image corrections. |
| [`HomologicalAlgebra.AdditiveEuler.Functoriality`](../HomologicalAlgebra/AdditiveEuler/Functoriality.lean) | Short exact sequences and exact-functor transport. |
| [`HomologicalAlgebra.AdditiveEuler.Shift`](../HomologicalAlgebra/AdditiveEuler/Shift.lean) | Separately supported intervals and cochain shifts. |
| [`HomologicalAlgebra.AdditiveEuler.HomologySupport`](../HomologicalAlgebra/AdditiveEuler/HomologySupport.lean) | Cochain long-exact-sequence connecting-image corrections. |
| [`HomologicalAlgebra.AdditiveEuler.Length`](../HomologicalAlgebra/AdditiveEuler/Length.lean) | Finite module length as an Euler invariant. |

## Invariants and chain Euler identities

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

## Cochain Euler identities

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

## Connecting images and homology bounds

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

## Short exact sequences and functors

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

## Comparing finite intervals

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

## Cochain shifts

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

## Finite module length

`lengthInvariant R` on `FGModuleCat R` is the integer cast of finite module
length. `lengthInvariant_ses R` requires a commutative, Noetherian, Artinian
ring: these hypotheses make lengths finite **before** `ENat.toNat` additivity.
The standalone definition has no SES-additivity guarantee over other rings.

## Checked examples and their limits

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

## Checked-use modules

The examples above import the public library. Their source modules are:

- [Chain Euler examples](../HomologicalAlgebraTest/AdditiveEuler.lean).
- [Exact-sequence and exact-functor examples](../HomologicalAlgebraTest/AdditiveEuler/Functoriality.lean).
- [Support and cochain-shift examples](../HomologicalAlgebraTest/AdditiveEuler/Shift.lean).
- [Cochain boundary-image examples](../HomologicalAlgebraTest/AdditiveEuler/Cochain.lean).
- [Nonsplit LES and homology-bound examples](../HomologicalAlgebraTest/AdditiveEuler/HomologySupport.lean).

## References and credit

Charles A. Weibel, *The K-book*, Chapter II, §6 motivates the SES-additive
formulation and finite Euler argument. These constructions reuse Mathlib's short
exact sequences, homology and shifts. The [contributor credits](../CREDITS.md)
distinguish mathematical expositions from original Lean proof authors and
preserve upstream notices. The library is licensed under [Apache-2.0](../LICENSE).
