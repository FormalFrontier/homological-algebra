# Homological Algebra

Reusable homological algebra built on Mathlib's native complexes, homology and
homotopies: finite Euler identities, unrestricted Hom complexes and K-objects,
ordinary projective/injective disks and bounded-below projective chains.
It also treats chain conditions, categorical length, finite indecomposable
decompositions and local endomorphism rings, Fitting and Drazin calculus,
abelian quotients and snake sequences, fixed-arrow relative paths, and quadrant
product totals of modules. The families have different hypotheses, detailed below.

## Headline results

- **Uniqueness of finite biproduct factors.** In a preadditive category, two
  finite families with local canonical, possibly noncommutative endomorphism
  rings and isomorphic biproducts have equivalent index types and matching
  isomorphic factors. Only the two given biproducts are needed, with independent
  object, morphism and both index universes; no abelian structure, chain
  conditions or idempotent completeness is assumed. Repeated factors are allowed;
  the matching need not be unique or make the supplied isomorphism diagonal.
  [Statement and module](docs/HeadlineResults.md#uniqueness-of-finite-biproduct-factors).

- **Finite indecomposable decompositions.** An Artinian object, or separately
  a Noetherian object, in a category with zero morphisms and finite biproducts
  is isomorphic to a finite biproduct of nonzero indecomposables; zero has the
  empty decomposition. No preadditivity, abelian structure, second chain condition or
  idempotent completeness is needed; this is existence, not uniqueness.
  [Statements and modules](docs/HeadlineResults.md#finite-indecomposable-decompositions).

- **Finite-length decompositions with local endomorphism rings.** A Noetherian
  **and** Artinian object in any abelian category is isomorphic to a finite
  biproduct with local canonical, possibly noncommutative endomorphism rings
  on its factors. Object and morphism universes are independent; zero has the
  empty decomposition. This asserts existence and locality, not uniqueness.
  Its local-End factors also satisfy the generic uniqueness theorem above.
  [Statement and module](docs/HeadlineResults.md#finite-length-decompositions-with-local-endomorphism-rings).

- **Cancellation of finite-length summands.** In any abelian category, if
  `X` is Noetherian **and** Artinian, `X ⊞ Y ≅ X ⊞ Z` implies
  `Nonempty (Y ≅ Z)` for unrestricted `Y, Z`. No locality of `End X`
  is required; zero is allowed and the isomorphism is not canonical.
  [Statement and module](docs/HeadlineResults.md#cancellation-of-finite-length-summands).

- **Subobject correspondence and modularity.** Canonical subobject lattices
  in any abelian category are modular. Pullback along an epimorphism identifies
  codomain subobjects with domain subobjects containing its kernel, with direct
  image as inverse; the cokernel case is included. No smallness is assumed.
  [Statements and module](docs/HeadlineResults.md#subobject-correspondence-and-modularity).

- **Composition series and Jordan–Hölder.** A Noetherian **and** Artinian
  object in any abelian category has a finite composition series from `⊥`
  to `⊤` with simple quotient factors. Any two given series with equal heads
  and lasts have equal lengths and isomorphic factors after a bijection,
  without chain conditions or bottom/top assumptions for uniqueness.
  [Statements and module](docs/HeadlineResults.md#composition-series-and-jordanhölder).

- **Categorical object length.** In any category, `objectLength X : ℕ∞`
  measures strict steps in the canonical subobject order and is invariant under
  isomorphisms and monotone under monomorphisms. In an abelian category it is
  additive on every short exact sequence, including infinite lengths, and is
  finite exactly for Noetherian **and** Artinian objects. Full composition
  series compute it; over any ring it agrees with `Module.length`, with
  independent scalar and carrier universes.
  [Statements and modules](docs/HeadlineResults.md#categorical-object-length).

- **Fitting decomposition and intertwiners.** For an endomorphism of a
  Noetherian **and** Artinian object in any abelian category, all sufficiently
  high powers have complementary kernels and images, with canonical copairing
  an isomorphism. The original endomorphism has a nilpotent restriction to the
  kernel and an invertible restriction to the image, with a common-tail
  block-intertwining equation. Arbitrary intertwiners between two such objects
  are block diagonal in these canonical coordinates on one common tail.
  Complementarity agrees with linear-map power kernels and ranges over
  arbitrary, possibly noncommutative rings. Separately, generic block-intertwiner
  and mixed-Hom vanishing laws need only zero morphisms and the displayed
  biproducts, nilpotence and mono/epi conditions, not abelian structure.
  [Statements and modules](docs/HeadlineResults.md#fitting-decomposition).

- **Canonical finite-length power bounds.** If `objectLength X ≠ ⊤`, put
  `L = (objectLength X).toNat`. Power kernels stabilize by `L` with zero
  morphisms and kernels; nilpotent endomorphisms satisfy `g ^ L = 0`.
  Power images stabilize by `L` with images and image maps. On a Noetherian
  **and** Artinian object in an abelian category, kernels and images of
  `f ^ n` agree with those of the Drazin projector for every `n ≥ L`;
  `f ^ (L + 1) * drazinInverse f = f ^ L` and
  `(f * (1 - f * drazinInverse f)) ^ L = 0`. Zero length is included;
  these are uniform mathematical bounds, not least exponents or runtime bounds.
  Over any ring, a module of finite composition length `L` has
  `ker (f ^ n) = ker (f ^ L)` for every endomorphism and every `n ≥ L`;
  finite generation alone is not the hypothesis.
  [Equations and hypotheses](docs/HeadlineResults.md#canonical-finite-length-power-bounds).

- **Canonical Drazin inverses.** Every endomorphism of a Noetherian **and**
  Artinian object in an abelian category has a unique commuting Drazin inverse.
  Its characteristic equations, nilpotent and idempotent cases, and
  preservation by arbitrary multiplicative maps and functors are included.
  For preservation both relevant objects must be Noetherian and Artinian;
  functors need not be additive or exact. Intertwiners also intertwine the
  inverses, and taking the inverse respects every natural power, including zero,
  and products of commuting endomorphisms. Double inversion gives the group part
  `f * drazinInverse f * f`, not generally `f`.
  [Equations and hypotheses](docs/HeadlineResults.md#canonical-drazin-inverses).

- **Drazin sums, projectors and perturbations.** On a Noetherian **and**
  Artinian object in an abelian category, mutually annihilating endomorphisms
  in **both** product orders have additive Drazin inverses, also on finite
  supports. A commuting nilpotent perturbation preserves the stable-image
  projector and has an explicit finite geometric inverse formula; the Drazin
  inverse itself generally changes. The projector has the stable power kernel
  and image; `f * (1 - f * drazinInverse f)` is nilpotent, not necessarily
  the complementary idempotent itself. These are conditional laws, not general
  additivity or perturbation invariance of the inverse.
  [Formulas and hypotheses](docs/HeadlineResults.md#drazin-sums-projectors-and-perturbations).

- **Cyclic and triangular Drazin formulas.** Between two Noetherian **and**
  Artinian objects of an abelian category, arbitrary `a : X ⟶ Y`, `b : Y ⟶ X`
  satisfy Cline's cyclic-product formula, with a canonical isomorphism between
  the images of their Drazin projectors. For such `X, Y`, a unit `f : End X`,
  nilpotent `g : End Y` with any witness `g ^ n = 0`, and arbitrary
  `h : X ⟶ Y` give a finite-sum formula for the inverse of
  `Biprod.ofComponents f h 0 g`; no intertwining condition on `h` is imposed.
  The canonical image of its stable-image projector is isomorphic to `X`,
  with the isomorphism's inverse given by a graph map.
  The witness may be zero or nonminimal. Separately, cyclic powers need only
  a category, and cyclic nilpotence only zero morphisms.
  [Cyclic formulas](docs/HeadlineResults.md#cyclic-products-and-projector-images),
  [triangular formula](docs/HeadlineResults.md#triangular-biproduct-formula).

- **Sylvester equation and invariant graphs.** In any preadditive category,
  invertible `f : X ⟶ X`, nilpotent `g : End Y` and arbitrary `h : X ⟶ Y`
  give a unique `u : X ⟶ Y` with `f ≫ u = h + u ≫ g`. No biproducts,
  scalar action or chain conditions are needed; object and morphism universes
  are independent. Under the abelian, Noetherian **and** Artinian triangular
  hypotheses above, this identifies the canonical graph slope, including its
  factor of `f`, and the unique section of the first projection that intertwines
  `f` with the triangular endomorphism.
  [Equation and canonical graph](docs/HeadlineResults.md#sylvester-equation-and-canonical-invariant-graph).

- **Nilpotence in short complexes.** For a compatible endomorphism of a
  short exact complex in any category with zero morphisms, the middle component
  is nilpotent exactly when both outer components are. Exactness alone gives
  the explicit middle exponent `m + n` from outer exponents `m, n`; a monic
  first arrow and an epic second arrow reflect a middle exponent to the left
  and right components, respectively, without changing it. All natural
  exponents, including zero, are allowed; no abelian, additive, splitting or
  chain-condition premise is needed.
  [Statements and module](docs/HeadlineResults.md#nilpotence-in-short-complexes).

- **Local endomorphism rings.** An indecomposable Noetherian **and** Artinian
  object in any abelian category has a local canonical, possibly noncommutative
  endomorphism ring; every endomorphism is nilpotent or a unit.
  Indecomposability excludes zero, with no extra nontriviality premise.
  [Statements and module](docs/HeadlineResults.md#local-endomorphism-rings).

- **Indecomposability from locality.** In any preadditive category with binary
  biproducts, a local canonical ring `End X` implies Mathlib's original
  `Indecomposable X`. No abelian structure, chain conditions, chosen zero
  object or separate nonzero hypothesis is required; the ring may be
  noncommutative.
  [Statement and module](docs/HeadlineResults.md#indecomposability-from-locality).

- **Finite Euler identities.** In an abelian category, an invariant valued in
  any additive commutative group and additive on every native short exact
  sequence gives finite integer-interval Euler identities for chains and
  cochains with explicit endpoint-image corrections. Quasi-isomorphism
  invariance requires both complexes to have term support in the same nonempty
  interval; homology-sum SES additivity for chains requires this of all three
  complexes. Cochain LES additivity instead has connecting-image corrections
  removable by neighboring homology vanishing. Exact-functor transport,
  finite-support and native-shift formulas, and length for finitely generated
  modules over a commutative Noetherian Artinian ring are included.
  [Formulas and hypotheses](docs/HeadlineResults.md#finite-euler-identities),
  [Euler guide](docs/AdditiveEuler.md).

- **Unrestricted Hom complexes and K-objects.** For integer cochains in any
  preadditive category, the canonical Hom complex uses unrestricted products
  of **abelian groups**, not products in the coefficient category. Homotopies
  act in both variables; a contraction in either contracts the Hom complex,
  and degree-`n` cohomology vanishes exactly when every map `K ⟶ L⟦n⟧` is
  null-homotopic. In an **abelian** category, K-projectivity and K-injectivity
  are characterized by acyclicity of Hom complexes against acyclic tests,
  even by vanishing in one fixed degree. They descend along one-sided homotopy
  retracts, are invariant under categorical equivalences, and are detected
  componentwise on supplied coproducts and products, respectively, including
  empty families. Hom-complex quasi-isomorphism criteria, diagonal homotopy
  criteria with evaluation-preservation hypotheses, and canonical preimages
  of supplied homotopy equivalences under fully faithful additive functors
  complement these results; no boundedness or enough-projectives/injectives
  assumption is imposed.
  [Detailed statements and modules](docs/HeadlineResults.md#hom-complexes-and-k-objects),
  [Hom-complex guide](docs/HomComplexHomotopy.md).

- **Ordinary disks and bounded-below projective chains.** In a category with
  zero morphisms and a zero object, an integer cochain identity disk in degrees
  `n,n+1` is ordinarily projective or injective exactly when its coefficient is;
  no preadditivity is required. Separately, in any abelian category, a
  particular map between integer chain complexes with projective terms and
  possibly different termwise lower bounds is a quasi-isomorphism exactly
  when it is the forward map of a homotopy equivalence. There is no upper-bound
  or enough-projectives assumption. Ordinary projectivity is distinct from
  K-projectivity.
  [Statements and modules](docs/HeadlineResults.md#ordinary-disks-and-bounded-below-projective-chains).

- **Chain conditions and homology.** A functor between arbitrary categories
  preserving monomorphisms and reflecting isomorphisms reflects Noetherian and,
  separately, Artinian objects, with four independent universes; fullness and
  faithfulness are not required. In an abelian category, a short complex with
  Noetherian middle object has Noetherian homology. Epimorphic Noetherian and
  monomorphic Artinian endomorphisms are isomorphisms. Both module criteria use
  the original scalar action over any ring, with independent scalar and carrier
  universes. No smallness, well-poweredness, Noetherian-ring or whole-category
  chain condition is assumed. In an abelian category, binary biproducts
  preserve each chain condition separately from that condition on both factors.
  [Statements and modules](docs/HeadlineResults.md#noetherian-objects).

- **Quotients, admissible layers and snake sequences.** In any abelian
  category, for subobjects `L ≤ U` of `B` and any `D`, the chosen-cokernel map
  `U/(L ⊓ D) ⟶ (U/L) × (B/D)` is monic, without `L ≤ D`. Layers admissible
  for a quotient property `P` have reversed lower and forward upper order;
  subobject and binary-product closure and `P(B/D)` make the lower cut
  `(L,U) ↦ (L ⊓ D,U)` **left** adjoint to inclusion of layers with lower
  endpoint at most `D`. Separately, snake inputs with exact rows, epic upper
  second arrow and monic lower first arrow give an eight-object sequence exact
  at all six interior objects.
  Neither exterior object is required to vanish; the four middle exactness
  positions use Mathlib's snake lemma.
  [Statements and modules](docs/HeadlineResults.md#quotients-admissible-layers-and-snake-sequences),
  [quotient guide](docs/QuotientIntersection.md), [layer guide](docs/AdmissibleLayers.md).

- **Fixed-arrow relative paths.** For integer cochains in a preadditive
  category with binary biproducts and **pullbacks**, the pullback of a fixed
  `f : B₁ ⟶ B` along the first native path endpoint has a strict section,
  lifts from chosen homotopies with strict endpoint equations, and a homotopy
  equivalence to `B₁` whose inverse homotopy vanishes over the first projection.
  The object depends only on `f`; no arbitrary-arrow naturality or new
  quasi-isomorphism instance is asserted.
  [Statement and module](docs/HeadlineResults.md#fixed-arrow-relative-paths),
  [relative-path guide](docs/CochainRelativePath.md).

- **Quadrant product totals.** For any ring `R`, native quadrant bicomplexes
  in `ModuleCat.{u} R`, with `R : Type u`, have signed unrestricted product
  totals in integer degrees `p-r`. Acyclic horizontal rows at **every** row
  and horizontal degree, including the boundary `p=0`, imply total acyclicity
  in **all integer degrees**. Chosen elementwise lifts are not linear or
  natural splittings; this is not an arbitrary-unbounded total theorem.
  [Statement and module](docs/HeadlineResults.md#quadrant-product-totals),
  [product-total guide](docs/ProductTotalAcyclicity.md).

The [complete headline catalogue](docs/HeadlineResults.md) retains the individual
results, signs, universe parameters and qualifications. In particular, object
and morphism universes are independent in the general categorical results;
index universes are independent in the family-limit results.

## Using the library

Add the dependency to your `lakefile.toml`:

```toml
[[require]]
name = "homological_algebra"
git = "https://github.com/FormalFrontier/homological-algebra.git"
rev = "main"
```

GitHub `main` contains reviewed releases. Lake resolves it when the dependency
is first added or updated; `lake-manifest.json` keeps the resolved commit until
the next update. Replace `main` with a commit from that history to pin it
explicitly. Use compatible Lean and Mathlib versions in the consuming project.

Import `HomologicalAlgebra` for the aggregate library, or choose a focused import
from the [usage and client guide](docs/Usage.md).
For example, the following excerpt of the existing
[ordinary disk-lifting client](HomologicalAlgebraTest/Cochain/DiskProjectivity.lean)
represents a lift across an epimorphism by `diskDesc` and records its
lower-component equation. The import and full required context are included:

```lean
module

import HomologicalAlgebra.Cochain.DiskProjectivity

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]
  [HasZeroMorphisms C] [HasZeroObject C]

namespace CochainComplex

example (n : ℤ) (X : C) [Projective X] {K L : CochainComplex C ℤ}
    (p : K ⟶ L) [Epi p] (a : X ⟶ L.X n) :
    ∃ b : X ⟶ K.X n,
      diskDesc n K b ≫ p = diskDesc n L a ∧ b ≫ p.f n = a := by
  let l := Projective.factorThru (diskDesc n L a) p
  have hl : l ≫ p = diskDesc n L a := Projective.factorThru_comp _ _
  refine ⟨diskHomEquiv n X K l, ?_, ?_⟩
  · rw [← diskHomEquiv_symm_apply, Equiv.symm_apply_apply]
    exact hl
  · calc
      diskHomEquiv n X K l ≫ p.f n = diskHomEquiv n X L (l ≫ p) :=
        (diskHomEquiv_naturality_right n X l p).symm
      _ = a := by
        rw [hl, ← diskHomEquiv_symm_apply, Equiv.apply_symm_apply]

end CochainComplex
```

## Building and checking

Use the repository's pinned `lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`)
and `lake-manifest.json` (mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`). The direct Lake dependencies are
mathlib and [stable-range](https://github.com/FormalFrontier/stable-range),
resolved from GitHub at the revisions in `lakefile.toml`. From the project root:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
env LEAN_NUM_THREADS=2 lake exe cache get
env LEAN_NUM_THREADS=2 lake --wfail build
```

The default build elaborates both root modules and the library and test modules
they import. On a host with a matching mathlib cache,
budget seconds to a few minutes and up to 8 GiB memory as *planning estimates*,
not measured peak usage, a minimum, guaranteed requirements or permission
for a particular support profile. `LEAN_NUM_THREADS=2` limits Lean runtime
threading, not aggregate Lake process count or memory. Project-wide elapsed
time and peak memory have not been measured. First-time cache retrieval
downloads thousands of files and varies with network and storage; do not run
a full mathlib source build if the cache fetch fails.

## Conventions and limitations

Composition `≫` is in diagrammatic order. The Hom-complex and Euler cochain
shifts use degree `i+n` for the native shift by `n`. Euler sums are finite:
they are not an infinite Euler construction or a canonical invariant from
homology bounds alone. The work does **not** establish the K₀ presentation,
general homologically-bounded Euler identities, arbitrary-arrow path
naturality, unrestricted long-exact-sequence theory beyond the finite-interval
cochain formula, a derived-category result or completion of a source.
See the [catalogue scope](docs/HeadlineResults.md#scope) and individual guides
for construction-specific limits and the [usage guide](docs/Usage.md) for the
scope of the existing examples.

## References

- Charles A. Weibel, *The K-book*, Chapter II, §6: motivates the adapted
  SES-additive formulation and finite Euler argument.
- N. Spaltenstein, *Resolutions of unbounded complexes*, §1: the K-projective
  and K-injective framework.
- Jürgen Neukirch, Alexander Schmidt and Kay Wingberg, *Cohomology of Number
  Fields*, corrected second edition, (1.3.1): the abelian-group snake diagram
  motivates the eight-object sequence in arbitrary abelian categories.
- M. P. Drazin, [*Pseudo-Inverses in Associative Rings and Semigroups*](https://doi.org/10.1080/00029890.1958.11991949)
  (1958): the Drazin inverse terminology.
- Huanyin Chen and Marjan Sheibani Abdolyousefi,
  [*Cline's formula for g-Drazin inverses in a ring*](https://doi.org/10.2298/FIL1908249C),
  Filomat **33**(8) (2019), 2249–2255: a generalized-Drazin ring treatment,
  distinct from the categorical finite-length cyclic-product formulation.
- N. Popescu, *Abelian Categories with Applications to Rings and Modules*
  (1973), cited by Mathlib's subobject correspondence development.
- Mathlib's order-theoretic height, Jordan–Hölder and module-length APIs
  supply the numerical-length framework and module comparison.
- The classical local-endomorphism-ring Krull–Schmidt uniqueness argument;
  Mathlib's categorical Gaussian elimination and additive envelope supply
  the cancellation and completion APIs.
- Mathlib's preadditive biproduct identities, noncommutative local-ring unit
  criterion and unit-idempotent lemma for indecomposability from locality.
- Mathlib's native short exact sequences, homology, shifts and path objects;
  `CategoryTheory.ShortComplex.SnakeInput.snake_lemma` provides the middle
  six-term snake sequence.

## Credits and license

Authors: Formal Frontier Agents. The original project mathematical expositions
and original Lean implementations are distinct contributions; later library
adaptations reuse earlier project interfaces. The [contributor credits](CREDITS.md)
distinguish exposition, proof, adaptation and documentation contributions and
preserve upstream Mathlib notices, including the Hom-complex and comparison
constructions of Joël Riou. Formal Frontier Agents developed this work with
AI assistance.
Licensed under Apache-2.0; see [LICENSE](LICENSE).
