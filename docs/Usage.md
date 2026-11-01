# Using the library

For dependency installation and build commands, see the [README](../README.md).
The [detailed headline results](HeadlineResults.md) state the hypotheses and
scope of each family; the guides below develop individual constructions.

## Imports and guides

Import `HomologicalAlgebra` or the focused public modules
`HomologicalAlgebra.AdditiveEuler` and
`HomologicalAlgebra.AdditiveEuler.Length`, or the exact-sequence and exact-functor
extension `HomologicalAlgebra.AdditiveEuler.Functoriality`, the finite-support
and native cochain-shift module `HomologicalAlgebra.AdditiveEuler.Shift`, the
finite-interval cochain Euler module `HomologicalAlgebra.AdditiveEuler.Cochain`,
or the native long-exact-sequence module
`HomologicalAlgebra.AdditiveEuler.HomologySupport`.
For Hom-complex homotopy invariance and contractions in either variable, use
`HomologicalAlgebra.Cochain.HomComplexFunctoriality`; see
[Hom-complex homotopy and contractibility](HomComplexHomotopy.md).
For ordinary projectivity and injectivity of identity disks, import
`HomologicalAlgebra.Cochain.DiskProjectivity` (or `HomologicalAlgebra`).
For the K-injectivity characterization, import
`HomologicalAlgebra.Cochain.KInjective` (or `HomologicalAlgebra`).
For descent of either K-property along a homotopy retraction, import
`HomologicalAlgebra.Cochain.KHomotopy` (or `HomologicalAlgebra`).
For invariance of both K-properties under an equivalence of abelian categories,
import `HomologicalAlgebra.Cochain.KEquivalence` (or `HomologicalAlgebra`).
For the supplied-coproduct K-projectivity and supplied-product K-injectivity
criteria, import
`HomologicalAlgebra.Cochain.KFamilyLimits` (or `HomologicalAlgebra`).
For the separate fixed-arrow path API, import
`HomologicalAlgebra.Cochain.RelativePath` (or the aggregate
`HomologicalAlgebra`); see [the guide](CochainRelativePath.md).
For the chosen quotient-intersection pairing, import
`HomologicalAlgebra.Abelian.QuotientIntersection` (or `HomologicalAlgebra`);
the public declarations are in `CategoryTheory.Subobject`. See
[the guide](QuotientIntersection.md) for the exact cokernel squares,
the `quotientIntersectionPair_fac` equation and a native closure client.
For quotient-admissible subobject layers and their lower-cut reflector, import
`HomologicalAlgebra.Abelian.AdmissibleLayers` (or `HomologicalAlgebra`). The
`CategoryTheory.AdmissibleLayer` API builds on that pairing; see
[the guide](AdmissibleLayers.md) for hypotheses and client examples.
For the distinct quadrant product-total API, import
`HomologicalAlgebra.Homology.ProductTotalAcyclicity` (or `HomologicalAlgebra`);
its declarations live in `CategoryTheory.QuadrantProductTotal`. See
[the guide](ProductTotalAcyclicity.md) for signs, row exactness at the
boundary, negative-degree primitives and the ordinary-import client.
For finite indecomposable decomposition existence, import
`HomologicalAlgebra.Indecomposable` (or `HomologicalAlgebra`) and use
`CategoryTheory.exists_finite_indecomposable_biproduct_of_isArtinianObject`
or `CategoryTheory.exists_finite_indecomposable_biproduct_of_isNoetherianObject`.
These need only zero morphisms, finite biproducts and the indicated individual
object's chain condition; they return `n : ℕ`, `F : Fin n → C`, indecomposability
of each `F i` and `Nonempty (X ≅ ⨁ F)`. The shared module
`HomologicalAlgebra.Indecomposable.Biproducts` supplies isomorphism transport,
injection criteria and `CategoryTheory.Limits.biproductAppendIso`.
For uniqueness of finite biproduct factors, import
[`HomologicalAlgebra.Preadditive.BiproductUniqueness`](../HomologicalAlgebra/Preadditive/BiproductUniqueness.lean)
(or `HomologicalAlgebra`) and apply
`CategoryTheory.exists_equiv_of_iso_biproduct_of_isLocalRing_end Y Z h`.
Its context is `{C : Type u} [Category.{v} C] [Preadditive C]`,
`{ι : Type w} {κ : Type w'}` with `[Finite ι] [Finite κ]`,
`Y : ι → C`, `Z : κ → C`, `[HasBiproduct Y] [HasBiproduct Z]`,
`[∀ i, IsLocalRing (CategoryTheory.End (Y i))]` and
`[∀ j, IsLocalRing (CategoryTheory.End (Z j))]`. From
`h : (⨁ Y) ≅ (⨁ Z)` it returns
`∃ e : ι ≃ κ, ∀ i, Nonempty (Y i ≅ Z (e i))`.
The canonical rings may be noncommutative, and all four universes are independent.
Only the two displayed biproducts are
assumed, not global finite biproducts, abelian structure, chain conditions or
idempotent completeness. Empty families and repeated factors are allowed;
locality excludes zero factors without an extra premise. The equivalence is
not asserted unique, and `h` need not be permutation-diagonal.
For finite biproduct decompositions with local canonical endomorphism rings,
import [`HomologicalAlgebra.Abelian.FiniteLength`](../HomologicalAlgebra/Abelian/FiniteLength.lean)
(or `HomologicalAlgebra`) and apply
`CategoryTheory.exists_finite_biproduct_isLocalRing_end X`.
For `{C : Type u} [Category.{v} C] [Abelian C]` and
`(X : C) [IsNoetherianObject X] [IsArtinianObject X]`, it returns
`n : ℕ`, `F : Fin n → C`, `∀ i, IsLocalRing (CategoryTheory.End (F i))`
and `Nonempty (X ≅ ⨁ F)`. The canonical rings may be noncommutative,
object and morphism universes are independent, and `Fin 0` gives the empty
decomposition of zero. Abelian structure supplies finite biproducts; no
supplied decomposition or separate nonzero hypothesis is needed. This is an
existence-and-locality result, not a uniqueness theorem.
Its local-End factors can be compared by the generic uniqueness theorem above;
one-sided indecomposable existence alone does not supply locality or uniqueness.
For categorical object length, import
[`HomologicalAlgebra.Abelian.Length`](../HomologicalAlgebra/Abelian/Length.lean)
(or `HomologicalAlgebra`). `CategoryTheory.objectLength X : ℕ∞` is defined
for every object of a category, is invariant under isomorphisms, and is
monotone under monomorphisms. In an abelian category,
`ShortComplex.ShortExact.objectLength_eq_add` is additive even for infinite
lengths and nonsplit short exact sequences. `CategoryTheory.objectLength_ne_top_iff`
identifies finite length with both original object chain conditions; a given
full composition series computes length by `objectLength_compositionSeries`.
Use `objectLength_toNat_eq_add` only with its finite-length hypotheses:
`.toNat` sends infinity to zero. For `ModuleCat.{v} R` over any `R : Type u`
with `[Ring R]`,
[`HomologicalAlgebra.Abelian.ModuleCatLength`](../HomologicalAlgebra/Abelian/ModuleCatLength.lean)
provides `ModuleCat.objectLength_eq_moduleLength`, with independent scalar
and carrier universes. It needs no finite-generation, Noetherian-ring or
Artinian-ring premise. The generic modular-lattice height, coheight and cover-series
results are in
[`HomologicalAlgebra.Order.Length`](../HomologicalAlgebra/Order/Length.lean).
See the [length statements](HeadlineResults.md#categorical-object-length)
for the weaker zero/simple-object criteria and their exact category floors.
For separate binary-biproduct closure instances of Noetherian and Artinian
objects in an abelian category, import
[`HomologicalAlgebra.Abelian.ChainConditions`](../HomologicalAlgebra/Abelian/ChainConditions.lean).
Each instance requires only its own chain condition on both factors.
For reflection of the individual chain conditions, import
`HomologicalAlgebra.NoetherianFunctor` or `HomologicalAlgebra.ArtinianFunctor`
(or `HomologicalAlgebra`), respectively. The declarations
`CategoryTheory.Functor.isNoetherianObject_of_obj` and
`CategoryTheory.Functor.isArtinianObject_of_obj` require preservation of
monomorphisms and reflection of isomorphisms, not fullness or faithfulness.
For the canonical Fitting decomposition, import
`HomologicalAlgebra.Abelian.Fitting` (or `HomologicalAlgebra`). The restrictions
and power-chain API are in `HomologicalAlgebra.Abelian.EndomorphismPowers`;
`HomologicalAlgebra.ModuleCat.Subobject` identifies kernels and images of module
morphisms with the corresponding submodules, including complementarity of power
kernels and images. For arbitrary intertwiners between two Noetherian **and**
Artinian objects of an abelian category, import
[`HomologicalAlgebra.Abelian.FittingNaturality`](../HomologicalAlgebra/Abelian/FittingNaturality.lean).
`CategoryTheory.End.eventually_exists_pow_biprod_desc_iso_naturality` returns
one common tail of canonical copairing isomorphisms in which the intertwiner
is block diagonal. It needs no mono/epi/iso condition on the intertwiner or
extra threshold. The all-exponent square
`CategoryTheory.End.pow_biprod_desc_naturality` and mixed-Hom vanishing laws
are already in `EndomorphismPowers`, under their weaker zero-morphism and
relevant kernel/image/biproduct hypotheses.
For original supplied summands, import
[`HomologicalAlgebra.Abelian.BiproductIntertwiners`](../HomologicalAlgebra/Abelian/BiproductIntertwiners.lean).
In a category with zero morphisms, nilpotent left components, an epic right
source component and a monic right target component force an arbitrary
block intertwiner to be the map of its diagonal corners. If it is invertible,
`CategoryTheory.End.biprodLeftIso` and `biprodRightIso` compare the original
summands, with inverse maps the corners of its inverse. The independent
`CategoryTheory.Limits.biprod.isIso_map_iff` needs only the displayed source
and target biproducts; no preadditivity or global binary biproducts are required.
See the [full block hypotheses](HeadlineResults.md#naturality-and-block-intertwiners).
For rectangular powers and nilpotence, import
[`HomologicalAlgebra.Abelian.EndomorphismCyclicProducts`](../HomologicalAlgebra/Abelian/EndomorphismCyclicProducts.lean).
`CategoryTheory.End.comp_pow_succ` needs only a category, while
`isNilpotent_comp_iff` additionally needs zero morphisms; the two objects
need not be identified. These use stock `End`/Hom operations, not a new
endomorphism type or a preadditive specialization.
For canonical finite object-length stabilization bounds, import
[`HomologicalAlgebra.Abelian.EndomorphismPowerLength`](../HomologicalAlgebra/Abelian/EndomorphismPowerLength.lean).
With `hX : CategoryTheory.objectLength X ≠ ⊤`, use
`CategoryTheory.Limits.kernelSubobject_pow_eq_of_objectLength_le` under zero
morphisms and kernels, or `imageSubobject_pow_eq_of_objectLength_le` under
images and image maps. Both apply for every `n ≥ (objectLength X).toNat`.
`CategoryTheory.End.pow_objectLength_toNat_eq_zero_of_isNilpotent` gives
the same bound on a nilpotent power with zero morphisms and kernels. These
results need no abelian category or supplied chain-condition instances;
finite length is a material premise, and zero length is included.
For the linear-map kernel statement over an arbitrary ring, import
[`HomologicalAlgebra.Abelian.ModuleCatPowerLength`](../HomologicalAlgebra/Abelian/ModuleCatPowerLength.lean).
`Module.End.ker_pow_eq_ker_pow_length_of_le` takes `f : Module.End R M`,
`hM : Module.length R M ≠ ⊤` and `hn : (Module.length R M).toNat ≤ n`, and
identifies `LinearMap.ker (f ^ n)` with the kernel at that finite length.
Here `M` is an additive commutative group with an `R`-module structure; no
commutativity or division hypothesis on `R` is required.
For finite-dimensional modules over a division ring and `n ≥ Module.finrank R M`,
`ModuleCat.subobjectModule_kernelSubobject_pow_eq_ker_pow_finrank_of_le`
compares the categorical power kernel with Mathlib's stabilized kernel through
`ModuleCat.subobjectModule` and `ModuleCat.endRingEquiv`.
The existing Noetherian module criterion is in
`HomologicalAlgebra.ShortComplex.ModuleCatNoetherian`.
For the canonical Drazin inverse, import
[`HomologicalAlgebra.Abelian.Drazin`](../HomologicalAlgebra/Abelian/Drazin.lean)
(or `HomologicalAlgebra`). Its `CategoryTheory.End` API includes
`eq_drazinInverse_iff` and `existsUnique_drazinInverse`; the
[characteristic equations and preservation hypotheses](HeadlineResults.md#canonical-drazin-inverses)
let users work without unfolding the construction.
`CategoryTheory.End.drazinInverse_comp_eq_comp_drazinInverse` transports
intertwining equations along arbitrary morphisms, and
`CategoryTheory.End.drazinInverse_pow` handles every natural power, including zero.
Both intertwined objects must be Noetherian and Artinian; no monic, epic or
invertible-morphism hypothesis is imposed. `Commute.drazinInverse_mul` gives
the product formula for commuting endomorphisms; `drazinInverse_drazinInverse`
returns `f * drazinInverse f * f`, not generally `f`.

The following focused Drazin extensions are also reexported by the aggregate
library. Their inverse operations concern Noetherian **and** Artinian objects
in abelian categories, with independent object and morphism universes:

- [`HomologicalAlgebra.Abelian.DrazinAdditivity`](../HomologicalAlgebra/Abelian/DrazinAdditivity.lean):
  `CategoryTheory.End.drazinInverse_add_of_mul_eq_zero` needs both annihilation
  orders. `drazinInverse_sum s f` needs pairwise annihilation for ordered
  distinct indices in the finite support `s`, not just distinct values or a
  finite whole index type. Empty and singleton supports are included.
- [`HomologicalAlgebra.Abelian.DrazinProjector`](../HomologicalAlgebra/Abelian/DrazinProjector.lean):
  eventual equalities of canonical power-kernel/image subobjects with those
  of `f * drazinInverse f`, and nilpotence of
  `f * (1 - f * drazinInverse f)`. The complementary idempotent alone need
  not be nilpotent; no stabilization threshold is supplied.
- [`HomologicalAlgebra.Abelian.DrazinLength`](../HomologicalAlgebra/Abelian/DrazinLength.lean):
  `kernelSubobject_pow_eq_mul_drazinInverse_of_objectLength_le` and its image
  counterpart apply from `L = (objectLength X).toNat` onward.
  `pow_objectLength_toNat_succ_mul_drazinInverse` and
  `mul_one_sub_mul_drazinInverse_pow_objectLength_toNat` give the
  characteristic and nilpotent-component bounds at `L`. Finiteness follows
  from the two chain conditions; zero length is included. These are uniform
  exponent bounds, not claims about least exponents or computation time.
- [`HomologicalAlgebra.Abelian.DrazinPerturbation`](../HomologicalAlgebra/Abelian/DrazinPerturbation.lean):
  `add_mul_drazinInverse_of_isNilpotent` preserves the projector under a
  **commuting** nilpotent perturbation. `drazinInverse_add_eq_sum_range` uses
  any witness `n ^ m = 0`, with the negative geometric terms
  `(-(drazinInverse f * n)) ^ k * drazinInverse f` for `k < m`.
  A zero witness forces `𝟙 X = 0`; it does not justify dropping commutation
  or asserting that the inverse is unchanged.
- [`HomologicalAlgebra.Abelian.DrazinCyclic`](../HomologicalAlgebra/Abelian/DrazinCyclic.lean):
  `drazinInverse_comp` is Cline's rectangular cyclic-product formula.
  `imageMulDrazinInverseCompIso a b` compares the canonical images of the
  two projectors, with forward map induced by `a` and inverse induced by
  `b ≫ drazinInverse (a ≫ b)`. Its inclusion, stock-image-map and naturality
  equations avoid unfolding the isomorphism. Both objects must have both
  chain conditions; `a` and `b` need not be invertible or split.
- [`HomologicalAlgebra.Abelian.DrazinTriangular`](../HomologicalAlgebra/Abelian/DrazinTriangular.lean):
  `drazinInverse_biprod_triangular f g h hf n hg` assumes `hf : IsUnit f`
  and `hg : g ^ n = 0`, on the two Noetherian and Artinian objects.
  Its constructor is source-first: `Biprod.ofComponents f h 0 g` has
  `h : X ⟶ Y` as second component, and the inverse has second component
  `∑ i ∈ Finset.range n, ((drazinInverse f) ^ (i + 2)) ≫ h ≫ (g ^ i)`.
  There is no commutation or zero assumption on `h`; unlike the perturbation
  formula this sum introduces no minus sign. Any zero or nonminimal witness
  is permitted; `n = 0` forces only `𝟙 Y = 0` and gives an empty sum.
  With the same objects, `hf : IsUnit f` and `hnil : IsNilpotent g`,
  `CategoryTheory.End.imageMulDrazinInverseBiprodTriangularIso f g h hf hnil`
  identifies the canonical image of `P = T * drazinInverse T` with `X`,
  where `T = Biprod.ofComponents f h 0 g`.
  Its `_hom` and `_inv_ι` equations describe the two maps without unfolding
  the chosen image isomorphism. If `q = biprod.inl ≫ drazinInverse T ≫ biprod.snd`,
  the inverse followed by the image inclusion is the graph of `f ≫ q`, not `q`.
  `factorThruImage_comp_imageMulDrazinInverseBiprodTriangularIso_hom`
  turns the canonical factor through this image into `biprod.fst`.
  Under these same abelian and two-object chain-condition hypotheses,
  `eq_comp_inl_drazinInverse_biprod_triangular_snd_iff` recognizes the graph
  slope `u = f ≫ q` by `f ≫ u = h + u ≫ g`.
  `eq_imageMulDrazinInverseBiprodTriangularIso_inv_ι_iff` recognizes the
  inverse graph section by the **pair** of equations
  `k ≫ biprod.fst = 𝟙 X` and `k ≫ T = f ≫ k`; neither can in general
  be dropped. These extra abelian and chain-condition hypotheses belong to
  the Drazin interfaces, not to the standalone Sylvester theorem.

See the [Drazin catalogue](HeadlineResults.md#canonical-drazin-inverses) for
all equations and the distinctions between these conditional laws.

For the **standalone Sylvester equation** in an arbitrary preadditive category,
import [`HomologicalAlgebra.Preadditive.Sylvester`](../HomologicalAlgebra/Preadditive/Sylvester.lean).
`CategoryTheory.existsUnique_sylvester f g hg h` gives the unique solution of
`f ≫ u = h + u ≫ g` for `[IsIso f]`, `hg : IsNilpotent g` and arbitrary
`h : X ⟶ Y`. There is no abelian, biproduct, scalar-action or chain-condition
premise, and no particular nilpotence exponent is supplied. The aggregate
import also exposes this theorem through the triangular module's public import.
See its [equation and graph applications](HeadlineResults.md#sylvester-equation-and-canonical-invariant-graph).

For **nilpotence in short complexes**, import
[`HomologicalAlgebra.ShortComplex.Endomorphism`](../HomologicalAlgebra/ShortComplex/Endomorphism.lean)
(or `HomologicalAlgebra`). In a category with zero morphisms, the four
interfaces in `CategoryTheory.ShortComplex` apply to a compatible
`φ : S ⟶ S`: `middle_pow_add_eq_zero` uses exactness and outer exponents
`m, n` to give exponent `m + n` in the middle;
`left_pow_eq_zero_of_mono` and `right_pow_eq_zero_of_epi` reflect a middle
exponent unchanged under the respective mono/epi hypothesis; and
`ShortExact.isNilpotent_middle_iff` combines these for a short exact complex.
All natural exponents, including zero, are supported. No abelian, additive,
splitting or chain-condition premise is needed. See the
[precise statements](HeadlineResults.md#nilpotence-in-short-complexes).

For cancellation of a Noetherian **and** Artinian summand against unrestricted
remaining objects, import
[`HomologicalAlgebra.Abelian.FiniteLengthCancellation`](../HomologicalAlgebra/Abelian/FiniteLengthCancellation.lean)
(or `HomologicalAlgebra`) and use
`CategoryTheory.nonempty_iso_of_biprod_iso_of_isNoetherianObject_of_isArtinianObject`.
The result is existence of an isomorphism of the remaining objects, not a
canonical choice, and the canceled object's endomorphism ring need not be local.
For canonical subobject correspondence and modularity, import
[`HomologicalAlgebra.Abelian.Subobject`](../HomologicalAlgebra/Abelian/Subobject.lean)
(or `HomologicalAlgebra`); the order isomorphisms `epiOrderIso` and
`cokernelOrderIso` are in `CategoryTheory.Abelian.Subobject`.
For composition-series existence and Jordan–Hölder factor uniqueness, import
[`HomologicalAlgebra.Abelian.JordanHolder`](../HomologicalAlgebra/Abelian/JordanHolder.lean)
(or `HomologicalAlgebra`). Use
`CategoryTheory.exists_compositionSeries_of_isNoetherianObject_of_isArtinianObject`
for existence and `CompositionSeries.jordan_holder_factorObject` to compare
any two given series with equal endpoints; only existence requires both
chain conditions. See the [precise hypotheses](HeadlineResults.md#composition-series-and-jordanhölder).
For the Noetherian and Artinian endomorphism theorems, import
`HomologicalAlgebra.Abelian.Endomorphism` (or `HomologicalAlgebra`).
For the nilpotent-or-unit dichotomy and local endomorphism ring of an
indecomposable Noetherian and Artinian object, import
`HomologicalAlgebra.Abelian.LocalEndomorphism` (or `HomologicalAlgebra`).
Categorical clients can use Mathlib's `CategoryTheory.isUnit_iff_isIso` to
express the unit conclusion as an isomorphism.
For indecomposability from locality in a preadditive category with binary
biproducts, import `HomologicalAlgebra.Preadditive.Indecomposable` (or
`HomologicalAlgebra`) and apply
`CategoryTheory.indecomposable_of_isLocalRing_end X` using the instance
`IsLocalRing (CategoryTheory.End X)` on the canonical endomorphism ring.
This direction needs no Noetherian or Artinian hypotheses.
For the snake endpoint maps and eight-object exact sequence, import
`HomologicalAlgebra.Abelian.SnakeLemma` (or `HomologicalAlgebra`); its declarations
live in `CategoryTheory.ShortComplex.SnakeInput`. The sequence is exact at its
six interior objects without asserting that either exterior object vanishes.
For the Euler declarations, boundary formulas, support and shift conventions,
and checked examples, see [Finite Euler invariants](AdditiveEuler.md).
The guide distinguishes termwise support from neighboring homology bounds,
including the nonsplit and torsion-valued clients.

### Non-Euler checked examples

`HomologicalAlgebraTest.Abelian.NilpotentIntertwiner` imports the aggregate
library and applies `End.eq_zero_of_epi_of_isNilpotent` to the identity
intertwiner: a nilpotent epimorphic endomorphism forces its object to be zero.
The client uses only a category with zero morphisms, with independent object
and morphism universes; no preadditive/abelian structure or chain conditions
are required. It is imported by the default test root. This is an interface
use, not a test of every Fitting or Drazin formula.

`HomologicalAlgebraTest.Abelian.FiniteLengthCancellation` applies the cancellation
theorem to a supplied zero summand, whose endomorphism ring is not local,
with unrestricted remaining objects. It is imported by the default test root.

`HomologicalAlgebraTest.Cochain.DiskProjectivity` checks that an ordinary lift
of a map from a projective disk across a categorical epimorphism is represented
by `diskDesc`, with the corresponding lower-component lifting equation, in
the same arbitrary coefficient category.

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

## Public-module index

[`HomologicalAlgebra`](../HomologicalAlgebra.lean) reexports the
following focused modules. Import a module under its displayed dotted name;
the links lead to its source. The [headline catalogue](HeadlineResults.md)
and guides above state the mathematical hypotheses.

- [`HomologicalAlgebra.Cochain.Disks`](../HomologicalAlgebra/Cochain/Disks.lean).
- [`HomologicalAlgebra.Cochain.DiskAdjunctions`](../HomologicalAlgebra/Cochain/DiskAdjunctions.lean).
- [`HomologicalAlgebra.Cochain.DiskProjectivity`](../HomologicalAlgebra/Cochain/DiskProjectivity.lean).
- [`HomologicalAlgebra.QuasiIsoZero`](../HomologicalAlgebra/QuasiIsoZero.lean).
- [`HomologicalAlgebra.HomologicalComplex.Functor`](../HomologicalAlgebra/HomologicalComplex/Functor.lean).
- [`HomologicalAlgebra.Homotopy.Functor`](../HomologicalAlgebra/Homotopy/Functor.lean).
- [`HomologicalAlgebra.ArtinianFunctor`](../HomologicalAlgebra/ArtinianFunctor.lean).
- [`HomologicalAlgebra.NoetherianFunctor`](../HomologicalAlgebra/NoetherianFunctor.lean).
- [`HomologicalAlgebra.Indecomposable`](../HomologicalAlgebra/Indecomposable.lean).
- [`HomologicalAlgebra.Preadditive.BiproductUniqueness`](../HomologicalAlgebra/Preadditive/BiproductUniqueness.lean).
- [`HomologicalAlgebra.Preadditive.Sylvester`](../HomologicalAlgebra/Preadditive/Sylvester.lean).
- [`HomologicalAlgebra.Cochain.BiproductKCriteria`](../HomologicalAlgebra/Cochain/BiproductKCriteria.lean).
- [`HomologicalAlgebra.Cochain.KFamilyLimits`](../HomologicalAlgebra/Cochain/KFamilyLimits.lean).
- [`HomologicalAlgebra.Cochain.HomotopyLimits`](../HomologicalAlgebra/Cochain/HomotopyLimits.lean).
- [`HomologicalAlgebra.Cochain.HomComplexShift`](../HomologicalAlgebra/Cochain/HomComplexShift.lean).
- [`HomologicalAlgebra.Abelian.AdmissibleLayers`](../HomologicalAlgebra/Abelian/AdmissibleLayers.lean).
- [`HomologicalAlgebra.Abelian.ArtinianObject`](../HomologicalAlgebra/Abelian/ArtinianObject.lean).
- [`HomologicalAlgebra.Abelian.BiproductIntertwiners`](../HomologicalAlgebra/Abelian/BiproductIntertwiners.lean).
- [`HomologicalAlgebra.Abelian.ChainConditions`](../HomologicalAlgebra/Abelian/ChainConditions.lean).
- [`HomologicalAlgebra.Abelian.Drazin`](../HomologicalAlgebra/Abelian/Drazin.lean).
- [`HomologicalAlgebra.Abelian.DrazinAdditivity`](../HomologicalAlgebra/Abelian/DrazinAdditivity.lean).
- [`HomologicalAlgebra.Abelian.DrazinCyclic`](../HomologicalAlgebra/Abelian/DrazinCyclic.lean).
- [`HomologicalAlgebra.Abelian.DrazinLength`](../HomologicalAlgebra/Abelian/DrazinLength.lean).
- [`HomologicalAlgebra.Abelian.DrazinPerturbation`](../HomologicalAlgebra/Abelian/DrazinPerturbation.lean).
- [`HomologicalAlgebra.Abelian.DrazinProjector`](../HomologicalAlgebra/Abelian/DrazinProjector.lean).
- [`HomologicalAlgebra.Abelian.DrazinTriangular`](../HomologicalAlgebra/Abelian/DrazinTriangular.lean).
- [`HomologicalAlgebra.Abelian.Endomorphism`](../HomologicalAlgebra/Abelian/Endomorphism.lean).
- [`HomologicalAlgebra.Abelian.EndomorphismCyclicProducts`](../HomologicalAlgebra/Abelian/EndomorphismCyclicProducts.lean).
- [`HomologicalAlgebra.Abelian.EndomorphismPowerLength`](../HomologicalAlgebra/Abelian/EndomorphismPowerLength.lean).
- [`HomologicalAlgebra.Abelian.EndomorphismPowers`](../HomologicalAlgebra/Abelian/EndomorphismPowers.lean).
- [`HomologicalAlgebra.Abelian.Fitting`](../HomologicalAlgebra/Abelian/Fitting.lean).
- [`HomologicalAlgebra.Abelian.FittingNaturality`](../HomologicalAlgebra/Abelian/FittingNaturality.lean).
- [`HomologicalAlgebra.Abelian.FiniteLength`](../HomologicalAlgebra/Abelian/FiniteLength.lean).
- [`HomologicalAlgebra.Abelian.FiniteLengthCancellation`](../HomologicalAlgebra/Abelian/FiniteLengthCancellation.lean).
- [`HomologicalAlgebra.Abelian.JordanHolder`](../HomologicalAlgebra/Abelian/JordanHolder.lean).
- [`HomologicalAlgebra.Abelian.Length`](../HomologicalAlgebra/Abelian/Length.lean).
- [`HomologicalAlgebra.Abelian.LocalEndomorphism`](../HomologicalAlgebra/Abelian/LocalEndomorphism.lean).
- [`HomologicalAlgebra.Abelian.ModuleCatLength`](../HomologicalAlgebra/Abelian/ModuleCatLength.lean).
- [`HomologicalAlgebra.Abelian.ModuleCatPowerLength`](../HomologicalAlgebra/Abelian/ModuleCatPowerLength.lean).
- [`HomologicalAlgebra.Abelian.QuotientIntersection`](../HomologicalAlgebra/Abelian/QuotientIntersection.lean).
- [`HomologicalAlgebra.Abelian.SerreClass`](../HomologicalAlgebra/Abelian/SerreClass.lean).
- [`HomologicalAlgebra.Abelian.SnakeLemma`](../HomologicalAlgebra/Abelian/SnakeLemma.lean).
- [`HomologicalAlgebra.Abelian.Subobject`](../HomologicalAlgebra/Abelian/Subobject.lean).
- [`HomologicalAlgebra.AdditiveEuler`](../HomologicalAlgebra/AdditiveEuler.lean).
- [`HomologicalAlgebra.AdditiveEuler.Cochain`](../HomologicalAlgebra/AdditiveEuler/Cochain.lean).
- [`HomologicalAlgebra.AdditiveEuler.Functoriality`](../HomologicalAlgebra/AdditiveEuler/Functoriality.lean).
- [`HomologicalAlgebra.AdditiveEuler.HomologySupport`](../HomologicalAlgebra/AdditiveEuler/HomologySupport.lean).
- [`HomologicalAlgebra.AdditiveEuler.Length`](../HomologicalAlgebra/AdditiveEuler/Length.lean).
- [`HomologicalAlgebra.AdditiveEuler.Shift`](../HomologicalAlgebra/AdditiveEuler/Shift.lean).
- [`HomologicalAlgebra.ChainComplex.Projective`](../HomologicalAlgebra/ChainComplex/Projective.lean).
- [`HomologicalAlgebra.Cochain.HomComplexFixedDegreeCriteria`](../HomologicalAlgebra/Cochain/HomComplexFixedDegreeCriteria.lean).
- [`HomologicalAlgebra.Cochain.HomComplexFunctoriality`](../HomologicalAlgebra/Cochain/HomComplexFunctoriality.lean).
- [`HomologicalAlgebra.Cochain.HomComplexQuasiIso`](../HomologicalAlgebra/Cochain/HomComplexQuasiIso.lean).
- [`HomologicalAlgebra.Cochain.HomComplexQuasiIsoCriteria`](../HomologicalAlgebra/Cochain/HomComplexQuasiIsoCriteria.lean).
- [`HomologicalAlgebra.Cochain.HomComplexVanishing`](../HomologicalAlgebra/Cochain/HomComplexVanishing.lean).
- [`HomologicalAlgebra.Cochain.KEquivalence`](../HomologicalAlgebra/Cochain/KEquivalence.lean).
- [`HomologicalAlgebra.Cochain.KInjective`](../HomologicalAlgebra/Cochain/KInjective.lean).
- [`HomologicalAlgebra.Cochain.KHomotopy`](../HomologicalAlgebra/Cochain/KHomotopy.lean).
- [`HomologicalAlgebra.Cochain.KProjective`](../HomologicalAlgebra/Cochain/KProjective.lean).
- [`HomologicalAlgebra.Cochain.RelativePath`](../HomologicalAlgebra/Cochain/RelativePath.lean).
- [`HomologicalAlgebra.Homology.ProductTotalAcyclicity`](../HomologicalAlgebra/Homology/ProductTotalAcyclicity.lean).
- [`HomologicalAlgebra.Cochain.HomotopyQuotientQuasiIso`](../HomologicalAlgebra/Cochain/HomotopyQuotientQuasiIso.lean).
- [`HomologicalAlgebra.Cochain.HomotopyQuotientAcyclic`](../HomologicalAlgebra/Cochain/HomotopyQuotientAcyclic.lean).
- [`HomologicalAlgebra.ModuleCat.Subobject`](../HomologicalAlgebra/ModuleCat/Subobject.lean).
- [`HomologicalAlgebra.Order.Length`](../HomologicalAlgebra/Order/Length.lean).
- [`HomologicalAlgebra.Preadditive.Indecomposable`](../HomologicalAlgebra/Preadditive/Indecomposable.lean).
- [`HomologicalAlgebra.ShortComplex.Endomorphism`](../HomologicalAlgebra/ShortComplex/Endomorphism.lean).
- [`HomologicalAlgebra.ShortComplex.ModuleCat`](../HomologicalAlgebra/ShortComplex/ModuleCat.lean).
- [`HomologicalAlgebra.ShortComplex.ModuleCatNoetherian`](../HomologicalAlgebra/ShortComplex/ModuleCatNoetherian.lean).

The indecomposable-decomposition facade also publicly reexports
[`HomologicalAlgebra.Indecomposable.Artinian`](../HomologicalAlgebra/Indecomposable/Artinian.lean)
and [`HomologicalAlgebra.Indecomposable.Noetherian`](../HomologicalAlgebra/Indecomposable/Noetherian.lean).
Both publicly import the shared
[`HomologicalAlgebra.Indecomposable.Biproducts`](../HomologicalAlgebra/Indecomposable/Biproducts.lean)
API.

## Default-built client index

The default targets in [`lakefile.toml`](../lakefile.toml) include
[`HomologicalAlgebraTest`](../HomologicalAlgebraTest.lean), whose imports are
listed below. The descriptions above and in the construction guides delimit
what the examples exercise; they are not additional generality claims.

- [`HomologicalAlgebraTest.Cochain.HomComplexFixedDegreeCriteria`](../HomologicalAlgebraTest/Cochain/HomComplexFixedDegreeCriteria.lean).
- [`HomologicalAlgebraTest.Cochain.DiskProjectivity`](../HomologicalAlgebraTest/Cochain/DiskProjectivity.lean).
- [`HomologicalAlgebraTest.Abelian.AdmissibleLayers`](../HomologicalAlgebraTest/Abelian/AdmissibleLayers.lean).
- [`HomologicalAlgebraTest.Abelian.FiniteLengthCancellation`](../HomologicalAlgebraTest/Abelian/FiniteLengthCancellation.lean).
- [`HomologicalAlgebraTest.Abelian.NilpotentIntertwiner`](../HomologicalAlgebraTest/Abelian/NilpotentIntertwiner.lean).
- [`HomologicalAlgebraTest.Abelian.QuotientIntersection`](../HomologicalAlgebraTest/Abelian/QuotientIntersection.lean).
- [`HomologicalAlgebraTest.Abelian.SnakeLemma`](../HomologicalAlgebraTest/Abelian/SnakeLemma.lean).
- [`HomologicalAlgebraTest.AdditiveEuler`](../HomologicalAlgebraTest/AdditiveEuler.lean).
- [`HomologicalAlgebraTest.AdditiveEuler.Cochain`](../HomologicalAlgebraTest/AdditiveEuler/Cochain.lean).
- [`HomologicalAlgebraTest.AdditiveEuler.Functoriality`](../HomologicalAlgebraTest/AdditiveEuler/Functoriality.lean).
- [`HomologicalAlgebraTest.AdditiveEuler.HomologySupport`](../HomologicalAlgebraTest/AdditiveEuler/HomologySupport.lean).
- [`HomologicalAlgebraTest.AdditiveEuler.Shift`](../HomologicalAlgebraTest/AdditiveEuler/Shift.lean).
- [`HomologicalAlgebraTest.ChainComplex.Projective`](../HomologicalAlgebraTest/ChainComplex/Projective.lean).
- [`HomologicalAlgebraTest.Cochain.HomComplexContractibility`](../HomologicalAlgebraTest/Cochain/HomComplexContractibility.lean).
- [`HomologicalAlgebraTest.Cochain.HomComplexFunctoriality`](../HomologicalAlgebraTest/Cochain/HomComplexFunctoriality.lean).
- [`HomologicalAlgebraTest.Cochain.HomComplexQuasiIsoCriteria`](../HomologicalAlgebraTest/Cochain/HomComplexQuasiIsoCriteria.lean).
- [`HomologicalAlgebraTest.Cochain.HomComplexVanishing`](../HomologicalAlgebraTest/Cochain/HomComplexVanishing.lean).
- [`HomologicalAlgebraTest.Cochain.KInjective`](../HomologicalAlgebraTest/Cochain/KInjective.lean).
- [`HomologicalAlgebraTest.Cochain.KProjective`](../HomologicalAlgebraTest/Cochain/KProjective.lean).
- [`HomologicalAlgebraTest.Cochain.RelativePath`](../HomologicalAlgebraTest/Cochain/RelativePath.lean).
- [`HomologicalAlgebraTest.Homology.ProductTotalAcyclicity`](../HomologicalAlgebraTest/Homology/ProductTotalAcyclicity.lean).
