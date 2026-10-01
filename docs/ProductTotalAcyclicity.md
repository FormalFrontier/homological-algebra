# Quadrant product totals of bicomplexes

Import `HomologicalAlgebra.Homology.ProductTotalAcyclicity` directly or
`HomologicalAlgebra` for the aggregate library. The declarations live in
`CategoryTheory.QuadrantProductTotal`. For any `[Ring R]`, including
noncommutative rings, the input is the native
`HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℕ) (ComplexShape.down ℕ)`.
There is no separate bicomplex structure or splitting hypothesis.

## Coordinates and signs

`Diag k` consists of `(r,p)` with `p-r=k`; `Product K k` is the **unrestricted**
product of the native modules `(K.X r).X p` over that diagonal. The native
integer-indexed down complex `productTotal K` has this module in degree `k`.
At target `(r,p)` of degree `k-1`, its actual differential is

```text
(Dₖ x)₍ᵣ,ₚ₎ = h(x₍ᵣ,ₚ₊₁₎) + (-1)^(k+1) δ(x₍ᵣ₋₁,ₚ₎).
```

The second term is zero at `r=0`. The scalar is the integral
`Int.negOnePow (k+1)`, not a natural-number parity shortcut: `D₋₁=h+δ`,
`D₀=h-δ`, and `D₁=h+δ`. See `differential_apply_zero`,
`differential_apply_pos`, `productTotal_d_apply_zero` and
`productTotal_d_apply_pos` for coordinate readbacks, and
`differential_square` for the square-zero proof. The horizontal and vertical
maps of the input commute; the sign makes the two mixed terms cancel.

`productTotalMap` sends any native bicomplex morphism to the coordinatewise
chain map. `productTotalMap_id` and `productTotalMap_comp` establish identity
and composition; they do not require exact rows.

## Acyclicity

`acyclic_productTotal K hrow` proves the native `productTotal K` acyclic in
**every integer degree**, assuming exactly
`hrow : ∀ r : ℕ, (K.X r).Acyclic`. This includes exactness at horizontal
degree `p=0`. `row_lift` invokes native module-category short-complex
exactness, choosing a preimage for each element rather than a linear section.
`liftStates` recursively chooses the coordinate lifts and `primitive` assembles
them into the unrestricted product. For negative total degrees the preceding
*existing* primitive coordinate is set to zero; no missing-coordinate cycle
equation is used. No convergence, bounded-support, split-surjection, finite
generation, or extra exact-products hypothesis is required. The chosen
primitive is neither asserted linear nor natural in cycles.

The [ordinary-import client](../HomologicalAlgebraTest/Homology/ProductTotalAcyclicity.lean)
builds a non-split integer-module example: the native kernel short complex of
reduction `ℤ → ZMod 2` is placed in each row, with zero vertical maps. It
proves native row acyclicity, applies `acyclic_productTotal`, rules out a
section of the reduction map, and checks the `-1,0,1` signs, an actual earlier
negative-degree coordinate and map identity. The repeated nonzero nonsplit row gives infinitely many nonzero cells
overall but at most three nonzero cells on each diagonal, with zero vertical
maps. This client does **not** test the stronger shifted three-term example
with infinitely many nonzero cells on each diagonal or nonzero vertical maps.

## Reproduction and rights

Use this repository's pinned Lean `leanprover/lean4:v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and complete
`lake-manifest.json`. From the project root:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
env LEAN_NUM_THREADS=2 lake exe cache get
env LEAN_NUM_THREADS=2 lake --wfail build
```

Fetch the matching mathlib cache successfully **before** building. Both the
[focused producer](../HomologicalAlgebra/Homology/ProductTotalAcyclicity.lean)
and the ordinary client are imported by their respective default roots
`HomologicalAlgebra` and `HomologicalAlgebraTest`. A successful build alone
does not replace the complete transitive standard-axiom audit including
private and generated declarations. The original mathematical assembly,
Lean proof, ordinary client and aggregate registration came from the Formal
Frontier core and LES contributor. The distinct cochain-shift and path
contributor independently reviewed mathematics, Lean code and aggregation,
then performed a separate, mathematics-preserving destination module-name
transfer. Another independent mapped review preceded Prism's code acceptance.
Prism chose the destination home and accepted the work but did not write its
original mathematical or Lean proof. Release decisions belong to the
responsible maintainer's exact-revision records.

Mathlib definitions and lemmas retain their original upstream authorship and
Apache-2.0 licensing; the project code uses this repository's
[Apache-2.0 license](../LICENSE). No source asset is redistributed and no
source-formalization coverage is inferred.
