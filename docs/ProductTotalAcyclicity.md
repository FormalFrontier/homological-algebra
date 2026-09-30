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
negative-degree coordinate and map identity. This minimum client does **not**
test the stronger shifted three-term example with infinitely many nonzero
cells on each diagonal or nonzero vertical maps.

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
private and generated declarations. At transfer preparation on September 30,
2026, this bounded transfer was an unaccepted destination candidate: the earlier
independently
reviewed and accepted mathematical argument and isolated Lean proof do not
certify the renamed destination origins, both roots or a new release. The
destination's CI, independent mapped review, maintainer acceptance and
release/publication were separate pending steps. Exact destination
`d610ea1c86bba786da5d896a3788748ec3d3855c` subsequently passed the native
both-root build and complete private/generated transitive standard-axiom audit,
received fresh independent Worker A mapped review (Hive Task
`hive-request-a0fe9769664de6d1e05e169f29740841a65ec217`, UID
`cb63297a-904b-467d-ba44-c63b12c11516`), and was accepted and integrated by
Prism on September 30, 2026. Prism prepared this documentation lifecycle update
without changing the proof or client. Separate release approval, protected
promotion and verified GitHub publication are not asserted by that code history.

The original mathlib definitions and lemmas retain upstream authorship and
Apache-2.0 licensing; this library's code is governed by its
[Apache-2.0 license](../LICENSE). Formalization Worker A developed the
mathematical assembly (UID `5431f7b8-147a-4c63-b517-a0fcfa0b8021`),
independently reviewed by Worker B (UID
`f1e68d0f-519f-42e6-adca-8518e8b6e999`); Worker A implemented the
isolated Lean proof and client (UID `f09e994a-0323-449d-b61e-09424d9bca27`),
independently reviewed by Worker B (UID
`1038024f-fc62-440a-be8f-17db640f5a59`). Worker A registered the
aggregate API (UID `a7b12f46-1810-48bd-86f1-68655875d540`), with
independent scoped and actual-parent review by Worker B (UIDs
`b186e2c0-ac3f-4aed-b99b-31c5c4c0fd88` and
`37080ebc-1f2a-40d2-8808-921b08fe4f84`). This module-name transfer by
Worker B (UID `0f1065ab-6fce-4f1b-940d-e153e7c5121f`) is not a new proof.
Prism made the home and incubation acceptance decisions, not the original
mathematical or Lean proof. No source-formalization coverage is inferred.
