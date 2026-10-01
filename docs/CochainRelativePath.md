# Fixed-arrow relative paths of integer cochain complexes

Import `HomologicalAlgebra.Cochain.RelativePath` for this API, or import
`HomologicalAlgebra` for the whole library. The ordinary-import client
[`HomologicalAlgebraTest.Cochain.RelativePath`](../HomologicalAlgebraTest/Cochain/RelativePath.lean)
checks the public interface. The [producer](../HomologicalAlgebra/Cochain/RelativePath.lean)
works with mathlib's native path object; it does not construct another path
formalism. All complexes in the fixed-arrow construction are
`CochainComplex C ℤ`, and `≫` composes left to right.

## Hypotheses and the endpoint law

The general cylinder theorem
`HomologicalComplex.cylinder.ι₀_comp_πCompι₀Homotopy_hom` applies to a
complex shape `c : ComplexShape α` in a preadditive category with binary
biproducts and decidable shape relation. It additionally requires
`hc : ∀ j, ∃ i, c.Rel i j`: every degree has an incoming related degree.
For every `i j`, the component of the *specific native* cylinder homotopy
vanishes after precomposition with `ι₀` in degree `j`, even off the relation.
This does not assert an analogous law for arbitrary homotopies.

For integer cochains, `CochainComplex.RelativePath.hcℤ` supplies the requisite
successor in `ComplexShape.up ℤ`. In a preadditive category with binary
biproducts (but **without** requiring pullbacks), `path_hom_π₀ B i j`
dualizes the cylinder law: every component of the actual
`pathObject.π₀CompιHomotopy B hcℤ` satisfies
`T.hom i j ≫ (pathObject.π₀ B).f j = 0`. Its proof uses the complete pinned
mathlib `HomotopyFiber` implementation through `import all` **in the producer**:
native path/homotopy definitions have non-exposed bodies. This is a
version-coupled definitional proof-maintenance point when updating mathlib,
not a separate package dependency or an `import all` requirement for clients.

## The fixed-arrow object and its maps

Add `[HasPullbacks C]` to `[Category* C] [Preadditive C]
[HasBinaryBiproducts C]`. Fix `f : B₁ ⟶ B`. Then
`CochainComplex.RelativePath.obj f := pullback f (pathObject.π₀ B)` is the
**ordinary pullback**, depending on `f` alone. Its projections are
`fst f : obj f ⟶ B₁` and `snd f : obj f ⟶ B.pathObject`; the target endpoint
is `toTarget f := snd f ≫ pathObject.π₁ B`. These equations hold strictly:

```text
sectionMap f ≫ fst f      = 𝟙 B₁
sectionMap f ≫ snd f      = f ≫ pathObject.ι B
sectionMap f ≫ toTarget f = f
fst f ≫ f                 = snd f ≫ pathObject.π₀ B
```

For `u : A ⟶ B₁`, `v : A ⟶ B`, and a **chosen**
`h : Homotopy (u ≫ f) v`, the arrow `lift f u v h : A ⟶ obj f` uses the
native `pathObject.lift`. It obeys strictly
`lift f u v h ≫ fst f = u` and `lift f u v h ≫ toTarget f = v`.
Different sources, maps and chosen homotopies lift into the same `obj f`.
The eight client examples exercise two such sources/homotopies, both endpoint
triangles, a reflexive lift, the native endpoint law, and the equivalence maps.
The lift depends on the *chosen* homotopy; no choice independence is claimed.

The componentwise pullback `isPullbackAt f j` supports
`contraction f : Homotopy (fst f ≫ sectionMap f) (𝟙 (obj f))`.
Its every homotopy component satisfies
`(contraction f).hom i j ≫ (fst f).f j = 0`. Thus
`equivalence f : HomotopyEquiv B₁ (obj f)` has literally
`hom = sectionMap f` and `inv = fst f`; the first inverse law is strict and
the second is this relative contraction. `comparison f` is the native
homotopy from `fst f ≫ f` to `toTarget f`. No arbitrary-arrow naturality,
general pullback-stability or new quasi-isomorphism instance is provided.
For a zero target the pullback is canonically isomorphic to `B₁`, not
definitionally equal to it. There is no derived or K-theoretic comparison.

## Reproduction and provenance

The repository pins Lean `v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`. Fetch the matching
precompiled cache before building both maintained default roots:

```sh
lake exe cache get
lake build HomologicalAlgebra HomologicalAlgebraTest
```

Prism wrote the original mathematical exposition. A distinct Formal Frontier
cochain-shift and path contributor authored the native fixed-arrow construction
and ordinary client; the core and LES contributor independently reviewed the
original mathematics and its bounded destination mapping. The transfer changed
module names without a new proof. Folio wrote the first five README headlines,
not this mathematical proof. Mathlib's path and cylinder constructions retain
their upstream credit and Apache-2.0 license; original project code uses this
repository's Apache-2.0 license. Neither a private source asset nor a
source-coverage decision is part of this library. Release status belongs to
the responsible maintainer's exact-revision records.
