# Headline results

Detailed statements, hypotheses and source modules for the library's results.
For a shorter overview, installation and build instructions, see the
[README](../README.md); for imports and example navigation, see
[Using the library](Usage.md).

## Navigation

- [Uniqueness of finite biproduct factors](#uniqueness-of-finite-biproduct-factors).
- [Finite indecomposable decompositions](#finite-indecomposable-decompositions).
- [Finite-length decompositions with local endomorphism rings](#finite-length-decompositions-with-local-endomorphism-rings).
- [Cancellation of finite local-End families](#cancellation-of-finite-local-end-families).
- [Cancellation of finite-length summands](#cancellation-of-finite-length-summands).
- [Subobject correspondence and modularity](#subobject-correspondence-and-modularity).
- [Composition series and Jordan–Hölder](#composition-series-and-jordanhölder).
- [Categorical object length](#categorical-object-length).
- [Fitting decomposition](#fitting-decomposition).
  - [Naturality and block intertwiners](#naturality-and-block-intertwiners).
  - [Cyclic powers and nilpotence](#cyclic-powers-and-nilpotence).
- [Canonical finite-length power bounds](#canonical-finite-length-power-bounds).
- [Canonical Drazin inverses](#canonical-drazin-inverses).
  - [Drazin sums, projectors and perturbations](#drazin-sums-projectors-and-perturbations).
  - [Cyclic products and projector images](#cyclic-products-and-projector-images).
  - [Triangular biproduct formula](#triangular-biproduct-formula).
- [Sylvester equation and canonical invariant graph](#sylvester-equation-and-canonical-invariant-graph).
- [Nilpotence in short complexes](#nilpotence-in-short-complexes).
- [Local endomorphism rings](#local-endomorphism-rings).
- [Indecomposability from locality](#indecomposability-from-locality).
- [Finite Euler identities](#finite-euler-identities).
- [Hom complexes and K-objects](#hom-complexes-and-k-objects).
  - [Homotopy, contraction and vanishing](#homotopy-contraction-and-vanishing).
  - [K-projectivity and K-injectivity](#k-projectivity-and-k-injectivity).
  - [Homotopy limits and supplied equivalences](#homotopy-limits-and-supplied-equivalences).
- [Ordinary disks and bounded-below projective chains](#ordinary-disks-and-bounded-below-projective-chains).
  - [Bounded-below projective integer chains](#bounded-below-projective-integer-chains).
- [Noetherian objects](#noetherian-objects).
- [Quotients, admissible layers and snake sequences](#quotients-admissible-layers-and-snake-sequences).
- [Fixed-arrow relative paths](#fixed-arrow-relative-paths).
- [Quadrant product totals](#quadrant-product-totals).
- [Scope](#scope).

## Uniqueness of finite biproduct factors

- **Uniqueness of finite biproduct factors.** In a preadditive category, two
  finite families with local canonical endomorphism rings and isomorphic
  biproducts admit an equivalence of their index types and componentwise
  isomorphisms. Only the two given biproducts are assumed: no global finite
  biproducts, abelian structure, chain conditions or idempotent completeness
  is required. Object, morphism and both index universes are independent.
  Repeated factors are allowed; the matching itself need not be unique, and
  the supplied total isomorphism need not be permutation-diagonal.
  [Theorem](../HomologicalAlgebra/Preadditive/BiproductUniqueness.lean).

The canonical endomorphism rings may be noncommutative.
Empty finite families are included; locality of each canonical `End` excludes
zero factors without a separate nonzero premise. The theorem returns matching
factors, not a canonical matching or a new decomposition construction. The
proof finds an invertible component using the local-ring finite-sum criterion,
cancels it by categorical Gaussian elimination in the additive envelope, and
reflects the factors through the fully faithful embedding.

### Proof ingredients and references

- The classical local-endomorphism-ring Krull–Schmidt uniqueness argument;
  Mathlib's categorical Gaussian elimination and additive envelope supply
  the cancellation and completion APIs.

## Finite indecomposable decompositions

- **Finite indecomposable decompositions.** An Artinian object, or separately a
  Noetherian object, is isomorphic to a finite biproduct of nonzero
  indecomposable objects in any category with zero morphisms and finite
  biproducts. The zero object has the empty decomposition. Object and morphism
  universes are independent; no abelian or preadditive structure, idempotent
  completeness, second chain condition, or uniqueness hypothesis is required.
  [Existence theorems](../HomologicalAlgebra/Indecomposable.lean) reuse Mathlib's
  indecomposability and chain conditions; the
  [biproduct API](../HomologicalAlgebra/Indecomposable/Biproducts.lean) gives
  isomorphism transport, injection criteria, and a finite-family append comparison.

## Finite-length decompositions with local endomorphism rings

- **Finite-length decompositions with local endomorphism rings.** A Noetherian
  and Artinian object in an abelian category is isomorphic to a finite biproduct
  whose factors have local canonical endomorphism rings, by
  `CategoryTheory.exists_finite_biproduct_isLocalRing_end`. The rings may be
  noncommutative, object and morphism universes are independent, and zero has
  the empty decomposition.
  [Theorem](../HomologicalAlgebra/Abelian/FiniteLength.lean).

These local-End factors satisfy the generic uniqueness theorem above: any two
such decompositions of isomorphic totals admit an index equivalence and
componentwise isomorphisms. This does not make the matching canonical or force
a supplied total isomorphism to be permutation-diagonal.

## Cancellation of finite local-End families

In any preadditive category, let `F : ι → C` be a finite family whose canonical
endomorphism rings `End (F i)` are local, possibly noncommutative rings. Then
`(⨁ F) ⊞ Y ≅ (⨁ F) ⊞ Z` implies `Nonempty (Y ≅ Z)`, by
`CategoryTheory.cancel_finite_biproduct_of_isLocalRing_end`.
Only the common full biproduct `⨁ F` and the two displayed binary biproducts
are required to exist in the original category; partial sums need not exist.
The remaining objects `Y, Z` are arbitrary, with no locality or chain conditions.
The object, morphism and index universes are independent; no abelian structure,
chosen zero object or idempotent completeness is assumed.
[Theorem](../HomologicalAlgebra/Preadditive/FiniteCancellation.lean).

The empty family is included. Locality entails nontriviality of each factor's
endomorphism ring, but the endomorphism ring of the full common sum need not be
local. The conclusion gives existence of an isomorphism, not a canonical
isomorphism or invertibility of the residual block of the supplied map.

The proof reindexes the supplied sum by `Fin n`, transports the common sum and
the two binary totals through Mathlib's fully faithful additive embedding into
`Mat_ C`, and cancels one local-End factor at a time there. Singleton cancellation
uses `StableRange.CategoryTheory.Cancellation` from the
[stable-range library](https://github.com/FormalFrontier/stable-range).
Fully faithful preimage of the resulting isomorphism gives the conclusion in `C`.

## Cancellation of finite-length summands

In an arbitrary abelian category, a Noetherian **and** Artinian object `X`
cancels from a binary biproduct: `X ⊞ Y ≅ X ⊞ Z` implies
`Nonempty (Y ≅ Z)`, by
`CategoryTheory.nonempty_iso_of_biprod_iso_of_isNoetherianObject_of_isArtinianObject`.
The remaining objects `Y, Z` are unrestricted; neither chain conditions nor
local endomorphism rings are required for them. Nor must `End X` be local.
Zero objects are included, object and morphism universes are independent,
and the conclusion asserts existence rather than a canonical isomorphism.
[Theorem](../HomologicalAlgebra/Abelian/FiniteLengthCancellation.lean).

The proof combines finite local-End decomposition with the generic
[finite-family cancellation theorem](#cancellation-of-finite-local-end-families).
It does not require locality of the entire canceled object's endomorphism ring.

## Subobject correspondence and modularity

For every object `A` in an arbitrary abelian category, the canonical
`CategoryTheory.Subobject A` has an `IsModularLattice` instance.
`CategoryTheory.Abelian.Subobject.epiOrderIso` gives the order isomorphism
from subobjects of an epimorphism's codomain to subobjects of its domain
containing its kernel. The forward map is pullback and the inverse is direct
image. `CategoryTheory.Abelian.Subobject.cokernelOrderIso` specializes this
to the upper interval above a subobject and the subobjects of its cokernel.
Object and morphism universes are independent; no `WellPowered`, smallness
or chain-condition hypothesis is needed.
[Theorems](../HomologicalAlgebra/Abelian/Subobject.lean).

## Composition series and Jordan–Hölder

A Noetherian **and** Artinian object in an arbitrary abelian category admits
a finite composition series of canonical subobjects, with head `⊥`, last `⊤`
and simple successive cokernel factors, by
`CategoryTheory.exists_compositionSeries_of_isNoetherianObject_of_isArtinianObject`.
For any two given composition series with equal heads and equal lasts,
`CompositionSeries.jordan_holder_factorObject` gives equality of lengths
and a bijection of factor indices carrying factors to isomorphic quotient
objects. This uniqueness statement needs no chain conditions or bottom/top
assumptions. The zero object has a length-zero series and an empty factor
family, not a simple zero factor. Object and morphism universes are independent;
no smallness hypothesis is imposed.
[Composition-series API](../HomologicalAlgebra/Abelian/JordanHolder.lean).

## Categorical object length

For an object `X` in any category, `CategoryTheory.objectLength X : ℕ∞` is
`Order.height (⊤ : Subobject X)`. It counts strict subobject steps, not vertices
or the number of subobjects; infinity means that finite strict-chain lengths
are unbounded. The definition, isomorphism invariance, subobject formula
`objectLength (P : C) = Order.height P`, and monotonicity under monomorphisms
need only a category, with independent object and morphism universes. No
smallness or well-poweredness premise is imposed.

With only a zero object, `objectLength X = 0` is equivalent to `IsZero X`.
With zero morphisms as well, `objectLength X = 1` is equivalent to `Simple X`.
In an abelian category:

- The length of the cokernel of a subobject inclusion is its coheight,
  and epimorphisms do not increase length.
- Every native short exact sequence `S` satisfies
  `objectLength S.X₂ = objectLength S.X₁ + objectLength S.X₃`, by
  `ShortComplex.ShortExact.objectLength_eq_add`, including infinite lengths
  and nonsplit sequences, without chain conditions.
- `objectLength X ≠ ⊤` is equivalent to
  `IsNoetherianObject X ∧ IsArtinianObject X`. The middle object of a short
  exact sequence has finite length exactly when both end objects do.
  If the middle object has both chain conditions, `objectLength_toNat_eq_add`
  gives natural-number additivity; no separate conditions on the ends are
  assumed. Taking `.toNat` is not a finite-length invariant without a
  finiteness premise, since infinity maps to zero.
- Any given composition series `s : CompositionSeries (Subobject X)` from
  `⊥` to `⊤` computes length: `(s.length : ℕ∞) = objectLength X`. Both
  endpoints are required, but a given full series needs no additional chain
  conditions. Its adjacent-inclusion cokernels are the factors described
  [above](#composition-series-and-jordanhölder).

[Object-length API](../HomologicalAlgebra/Abelian/Length.lean).
Over any possibly noncommutative ring `R : Type u` and `M : ModuleCat.{v} R`,
`ModuleCat.objectLength_eq_moduleLength` gives
`CategoryTheory.objectLength M = Module.length R M`. Scalar and carrier
universes are independent; no Noetherian-ring or Artinian-ring condition is
required. This comparison of `ℕ∞`-valued lengths is distinct from the
integer Euler invariant on finitely generated modules over a commutative
Noetherian Artinian ring.
[Module comparison](../HomologicalAlgebra/Abelian/ModuleCatLength.lean).

The generic order results use Mathlib's height and Jordan–Hölder interfaces.
In a modular lattice with top, `Order.height_top_eq_height_add_coheight`
gives `height ⊤ = height a + coheight a` without bottom or chain conditions.
For a nonempty modular lattice, `FiniteDimensionalOrder` is equivalent to
`WellFoundedLT ∧ WellFoundedGT`; it bounds chain lengths, not the size of the
underlying set. A given bottom-to-top cover series in a bounded modular
lattice computes `height ⊤` by its number of steps, without chain conditions.
[Order-length API](../HomologicalAlgebra/Order/Length.lean).

## Fitting decomposition

- **Fitting decomposition.** For an endomorphism `f` of a Noetherian and
  Artinian object in an arbitrary abelian category, the kernel and image of
  every sufficiently high power `f ^ n` are complementary. The canonical
  copairing of their inclusions is an isomorphism. The restriction of `f` to
  the kernel is nilpotent and its restriction to the image is invertible,
  with the corresponding block-intertwining equation on one common tail.
  Object and morphism universes are independent. The ModuleCat subobject
  comparison transports the complementarity conclusion to kernels and ranges
  of linear-map powers over any ring, without a commutativity hypothesis.
  [Categorical decomposition](../HomologicalAlgebra/Abelian/Fitting.lean),
  [canonical restrictions and powers](../HomologicalAlgebra/Abelian/EndomorphismPowers.lean),
  [module agreement](../HomologicalAlgebra/ModuleCat/Subobject.lean).

### Naturality and block intertwiners

For endomorphisms `f : End X`, `g : End Y` and an arbitrary `p : X ⟶ Y`
with `f ≫ p = p ≫ g`, `End.pow_biprod_desc_naturality` gives a natural square
of power-kernel/image copairings at every `n : ℕ`, including zero. This uses
only zero morphisms, the kernels and images of the two displayed powers,
the image map for the induced square, and the two displayed binary biproducts.
The induced maps are Mathlib's `kernel.map` and `image.map`; no abelian
structure, complementarity, chain conditions or invertibility is assumed.
In schematic notation, if `c_f, c_g` are these copairings and `k_p, i_p`
the induced maps, the equation is
`biprod.map k_p i_p ≫ c_g = c_f ≫ p`.
[Generic naturality](../HomologicalAlgebra/Abelian/EndomorphismPowers.lean).

If both `X` and `Y` are Noetherian **and** Artinian in the same abelian
category, `End.eventually_exists_pow_biprod_desc_iso_naturality` makes both
copairings canonical isomorphisms on one common tail, with invertible image
restrictions. In those coordinates,
`eX.hom ≫ p ≫ eY.inv = biprod.map k_p i_p`: the two off-diagonal corners
vanish. No monomorphism, epimorphism or isomorphism condition on `p`, supplied
splitting or extra stabilization exponent is required. Object and morphism
universes are independent.
[Fitting naturality](../HomologicalAlgebra/Abelian/FittingNaturality.lean).

There are also statements for original, supplied summands, not just canonical
Fitting coordinates. In any category with zero morphisms:

- An intertwiner `f ≫ p = p ≫ g` is zero if `f` is nilpotent and `g` is
  monomorphic, by `End.eq_zero_of_isNilpotent_of_mono`; dually it is zero
  if `f` is epimorphic and `g` nilpotent, by
  `End.eq_zero_of_epi_of_isNilpotent`. These need neither kernels nor images,
  preadditivity, abelian structure nor chain conditions.
- For `p : N ⊞ I ⟶ Nprime ⊞ Iprime` intertwining `biprod.map n i` and
  `biprod.map nprime iprime`, nilpotence of `n` and `nprime`, epicity of `i`
  and monicity of `iprime` force both off-diagonal corners to vanish.
  `End.biprod_intertwiner_eq_map` expresses `p` as the biproduct map of its
  two diagonal corners. The first off-diagonal vanishing needs only
  nilpotence of `n` and monicity of `iprime`; the other needs only epicity
  of `i` and nilpotence of `nprime`, in addition to the intertwining equation.
- If `p` is also invertible, `End.biprodLeftIso` and `End.biprodRightIso`
  give canonical isomorphisms of the original left and right summands.
  Their homs are the diagonal corners of `p`, their inverses the diagonal
  corners of `inv p`, and their `biprod.mapIso` is `asIso p`.
- Independently of these endomorphisms, `biprod.isIso_map_iff` says
  `IsIso (biprod.map f g) ↔ IsIso f ∧ IsIso g`, and `biprod.mapIso_asIso`
  identifies the biproduct of the canonical component isomorphisms with
  `asIso (biprod.map f g)`.

Only the two source/target binary biproducts are assumed, not all binary
biproducts or preadditivity; object and morphism universes are independent.
[Block-intertwiner API](../HomologicalAlgebra/Abelian/BiproductIntertwiners.lean),
[mixed-Hom vanishing](../HomologicalAlgebra/Abelian/EndomorphismPowers.lean).

### Cyclic powers and nilpotence

For arbitrary `a : X ⟶ Y` and `b : Y ⟶ X` in a category,
`End.comp_pow_succ` gives
`(a ≫ b) ^ (n + 1) = a ≫ ((b ≫ a) ^ n) ≫ b` for every `n : ℕ`, including
zero. With zero morphisms, `End.isNilpotent_comp_iff` identifies nilpotence
of the two cyclic products: a zero-power witness on one transfers to the
other with exponent increased by one. No additivity, chain conditions,
invertibility or identification of `X` and `Y` is required. Powers and zero
are the original canonical endomorphism/Hom operations, with
`p * q = q ≫ p`. For same-object maps, `comp_pow_comp_eq_mul_pow_mul`
agrees with Mathlib's monoid shuffle `mul_pow_mul`.
[Cyclic-power API](../HomologicalAlgebra/Abelian/EndomorphismCyclicProducts.lean).

## Canonical finite-length power bounds

Write `L = (CategoryTheory.objectLength X).toNat`. In a category, the explicit
premise `hX : objectLength X ≠ ⊤` gives the following uniform bounds:

- With zero morphisms and kernels, for every `n ≥ L`,
  `kernelSubobject (f ^ n) = kernelSubobject (f ^ L)`.
- With images and image maps, for every `n ≥ L`,
  `imageSubobject (f ^ n) = imageSubobject (f ^ L)`.
- With zero morphisms and kernels, every nilpotent `g : End X` satisfies
  `g ^ L = 0`, by `End.pow_objectLength_toNat_eq_zero_of_isNilpotent`.

These do not require an abelian category or separate Noetherian/Artinian
instances. The finite object-length premise is essential: `.toNat` sends
infinity to zero. The zero-length case is included.
[Power-length bounds](../HomologicalAlgebra/Abelian/EndomorphismPowerLength.lean).

For an `R`-module `M` over an arbitrary, possibly noncommutative ring, assume
`Module.length R M ≠ ⊤` and put `L = (Module.length R M).toNat`. This library
proves `LinearMap.ker (f ^ n) = LinearMap.ker (f ^ L)` for every
`f : Module.End R M` and `n ≥ L`, with independent scalar and carrier
universes. Finite generation alone does not replace finite composition length.
Separately, for a finite-dimensional `M : ModuleCat R` over a division ring
and `g : CategoryTheory.End M`, the canonical subobject-to-submodule
isomorphism sends the categorical kernel of `g ^ n`, for
`n ≥ Module.finrank R M`, to
`LinearMap.ker ((ModuleCat.endRingEquiv M g) ^ Module.finrank R M)`.
This comparison reuses Mathlib's finite-dimensional stabilization theorem;
the arbitrary-ring bound is deduced here from categorical length.
[Module power kernels](../HomologicalAlgebra/Abelian/ModuleCatPowerLength.lean).

For `f : End X` with `X` Noetherian **and** Artinian in an abelian category,
put `D = End.drazinInverse f` and `P = f * D`. Finiteness of `objectLength X`
is then derived from the two chain conditions, not a separate hypothesis.
For every `n ≥ L`, the kernel and image subobjects of `f ^ n` equal those
of `P`, by `kernelSubobject_pow_eq_mul_drazinInverse_of_objectLength_le`
and `imageSubobject_pow_eq_mul_drazinInverse_of_objectLength_le`.
Moreover, `f ^ (L + 1) * D = f ^ L` and
`(f * (1 - P)) ^ L = 0`. These bounds include `L = 0`, may exceed the least
exponent for an individual map, and are mathematical exponent bounds, not
runtime algorithm or resource bounds. Object and morphism universes are
independent.
[Drazin-length bounds](../HomologicalAlgebra/Abelian/DrazinLength.lean).

## Canonical Drazin inverses

For an endomorphism `f : End X` of a Noetherian **and** Artinian object in any
abelian category, `CategoryTheory.End.drazinInverse f` is the unique `g` with
`Commute f g`, `g * f * g = g` and
`∃ n : ℕ, f ^ (n + 1) * g = f ^ n`. Only `g` is unique: the exponent may
be zero and need not be unique. The characteristic interfaces
`eq_drazinInverse_iff` and `existsUnique_drazinInverse` avoid unfolding the
noncomputable construction.

The inverse is zero exactly when `f` is nilpotent, equals `CategoryTheory.inv f`
for isomorphisms, and fixes idempotents. The product `f * drazinInverse f`
is an idempotent projector. The original endomorphism multiplication is
`p * q = q ≫ p`. Object and morphism universes are independent; no
commutativity, nonzero-object or supplied-decomposition hypothesis is needed.
[Value and characteristic API](../HomologicalAlgebra/Abelian/Drazin.lean).

`CategoryTheory.End.map_drazinInverse` gives preservation by arbitrary
multiplicative maps `φ : End X → End Y`, without preservation of one or zero,
when both objects are Noetherian and Artinian in abelian categories. The
source and target object and morphism universes are all independent.
`CategoryTheory.Functor.map_drazinInverse` applies to any functor `F` between
abelian categories when both `X` and `F.obj X` are Noetherian and Artinian;
no additivity or exactness is required.

Intertwiners are preserved too. In the same abelian category, let `f : End X`
and `g : End Y`, with each object Noetherian and Artinian. Every `p : X ⟶ Y`
with `f ≫ p = p ≫ g` satisfies
`drazinInverse f ≫ p = p ≫ drazinInverse g`, by
`CategoryTheory.End.drazinInverse_comp_eq_comp_drazinInverse`.
There is no monomorphism, epimorphism or isomorphism hypothesis on `p`.
In particular, `Commute.drazinInverse_left` says that an endomorphism commuting
with `f` also commutes with its Drazin inverse. For every `n : ℕ`, including zero,
`CategoryTheory.End.drazinInverse_pow` gives
`drazinInverse (f ^ n) = (drazinInverse f) ^ n`.

For commuting `f, g : End X` on such an object, `Commute.drazinInverse_mul`
gives `drazinInverse (f * g) = drazinInverse f * drazinInverse g`.
No commutativity of the whole endomorphism ring is assumed.
`End.drazinInverse_drazinInverse` gives
`drazinInverse (drazinInverse f) = f * drazinInverse f * f`.
Double inversion need not recover `f`: for a nonzero nilpotent input it is
zero. These are part of the same
[Drazin API](../HomologicalAlgebra/Abelian/Drazin.lean).

### Drazin sums, projectors and perturbations

All statements in this subsection concern endomorphisms of a Noetherian
**and** Artinian object in an abelian category, with independent object and
morphism universes and the original multiplication `f * g = g ≫ f`.

**Orthogonal sums.** If `f * g = 0` **and** `g * f = 0`,
`End.drazinInverse_add_of_mul_eq_zero` gives
`drazinInverse (f + g) = drazinInverse f + drazinInverse g`.
For any `ι : Type w`, `s : Finset ι`, and `f : ι → End X`, the premise
`(s : Set ι).Pairwise (fun i j => f i * f j = 0)` gives
`drazinInverse (∑ i ∈ s, f i) = ∑ i ∈ s, drazinInverse (f i)` by
`End.drazinInverse_sum`. This quantifies over ordered distinct supported
indices, so includes **both** product orders; it does not mean merely distinct
values of `f`. It is restricted to `s`, and `ι` need not be finite. Empty and
singleton supports, zero objects, and characteristic exponent zero are
allowed; no positive or common characteristic index is supplied. These are
conditional laws, not global additivity of the inverse.
[Orthogonal-sum API](../HomologicalAlgebra/Abelian/DrazinAdditivity.lean).

**Stable projector subobjects.** For `P = f * drazinInverse f`, the canonical
kernel and image subobjects of all sufficiently high powers `f ^ n` equal
those of `P`. The component `f * (1 - P)` is nilpotent; the complementary
idempotent `1 - P` itself need not be nilpotent. The eventual statements
require no supplied threshold or positive index; the
[length bounds](#canonical-finite-length-power-bounds) make them effective
from the canonical finite object length onward.
[Projector API](../HomologicalAlgebra/Abelian/DrazinProjector.lean).

**Commuting nilpotent perturbations.** Let `f, n : End X` satisfy `Commute f n`
and `IsNilpotent n`. Then `End.add_mul_drazinInverse_of_isNilpotent` gives
`(f + n) * drazinInverse (f + n) = f * drazinInverse f`: it is the stable-image
projector that remains unchanged, not generally the inverse itself.
Every witness `n ^ m = 0` gives the explicit geometric formula
`drazinInverse (f + n) = ∑ k ∈ Finset.range m, (-(drazinInverse f * n)) ^ k * drazinInverse f`,
by `End.drazinInverse_add_eq_sum_range`. The sign, order and truncation are
as displayed. No positivity or minimality of `m`, chosen splitting or
commutativity of the whole ring is required. If `m = 0`, its witness forces
`𝟙 X = 0` and the sum is empty. Commutation of `f` with the nilpotent
perturbation is a material hypothesis.
[Perturbation API](../HomologicalAlgebra/Abelian/DrazinPerturbation.lean).

### Cyclic products and projector images

Let `a : X ⟶ Y` and `b : Y ⟶ X` be arbitrary morphisms between two
Noetherian **and** Artinian objects in the same abelian category. Cline's
formula `End.drazinInverse_comp` gives
`drazinInverse (a ≫ b) = a ≫ (drazinInverse (b ≫ a)) ^ 2 ≫ b`.
The projector identity `End.mul_drazinInverse_comp` is
`drazinInverse (a ≫ b) ≫ (a ≫ b) = a ≫ drazinInverse (b ≫ a) ≫ b`.
Neither invertibility of `a` or `b`, an ambient isomorphism `X ≅ Y`, nor a
supplied splitting is assumed. Both objects carry both chain conditions;
object and morphism universes are independent.

`End.imageMulDrazinInverseCompIso a b` compares the canonical `Limits.image`
objects of the two Drazin projectors. Its forward map is the categorical image
map induced by `a`, and its inverse the one induced by
`b ≫ drazinInverse (a ≫ b)`. The `_hom_ι` and `_inv_ι` equations describe them
after their image inclusions; `_hom_eq_image_map` and `_inv_eq_image_map`
identify the stock image maps. The `_hom_naturality` equation intertwines the
endomorphisms induced by the cyclic products on these images. These are
canonical categorical images, not an identification of the ambient objects.
[Cyclic-product API](../HomologicalAlgebra/Abelian/DrazinCyclic.lean).

The rectangular categorical formula follows the intertwiner and outer-inverse
identities. Huanyin Chen and Marjan Sheibani Abdolyousefi,
[*Cline's formula for g-Drazin inverses in a ring*](https://doi.org/10.2298/FIL1908249C),
Filomat **33**(8) (2019), 2249–2255, treats the generalized-Drazin ring version,
distinct from this finite-length categorical formulation.

### Triangular biproduct formula

In an abelian category, let `X` and `Y` each be Noetherian **and** Artinian,
`f : End X`, `g : End Y`, and `h : X ⟶ Y`. Assume `hf : IsUnit f` and
`hg : g ^ n = 0` for some `n : ℕ`. The source-first constructor
`T = Biprod.ofComponents f h (0 : Y ⟶ X) g` has canonical Drazin inverse
`Biprod.ofComponents (drazinInverse f) s (0 : Y ⟶ X) (0 : End Y)`, where
`s = ∑ i ∈ Finset.range n, ((drazinInverse f) ^ (i + 2)) ≫ h ≫ (g ^ i)`.
This is `End.drazinInverse_biprod_triangular`.

The component `h` is arbitrary: no intertwining or zero-component hypothesis
on it is imposed. The witness need not be minimal or positive. If `n = 0`,
only `𝟙 Y = 0` is forced and the sum is empty; neither `X` nor the ambient
category must be zero. The abelian category supplies the binary biproduct;
its two chain conditions follow from those on the factors by the binary-closure
instances. Object and morphism universes are independent. The formula specifies
the inverse and its four source-first components.
[Triangular API](../HomologicalAlgebra/Abelian/DrazinTriangular.lean).

For the same objects and unit `f`, nilpotence of `g` also gives a graph
factorization of the stable-image projector. Put `P = T * drazinInverse T`,
`q = biprod.inl ≫ drazinInverse T ≫ biprod.snd` and `u = f ≫ q`.
Then `End.mul_drazinInverse_biprod_triangular` gives
`P = End.of (biprod.fst ≫ biprod.lift (𝟙 X) u)`.
The canonical categorical image `Limits.image (End.asHom P)` is isomorphic
to `X` by `End.imageMulDrazinInverseBiprodTriangularIso`. Its forward map is
the image inclusion followed by `biprod.fst`; its inverse followed by the
inclusion is `biprod.lift (𝟙 X) u`. The canonical factor through the image
followed by this isomorphism is `biprod.fst`. The graph component is `f ≫ q`,
not `q`, and this is an isomorphism of the actual image objects, not just
an equality of image subobjects. No intertwining condition on `h` is added.

## Sylvester equation and canonical invariant graph

In any preadditive category, let `f : X ⟶ X` be invertible, let `g : End Y`
be nilpotent, and let `h : X ⟶ Y` be arbitrary. Then
`CategoryTheory.existsUnique_sylvester` gives
`∃! u : X ⟶ Y, f ≫ u = h + u ≫ g`.
Its literal interface uses `[IsIso f]` and `hg : IsNilpotent g`, not a chosen
nilpotence exponent. Object and morphism universes are independent. There is
no biproduct, scalar action, Noetherian, Artinian or finite-length hypothesis.
Zero objects and zero or nonminimal nilpotence witnesses are included; when
`g = 0`, the unique solution is `inv f ≫ h`.
[Sylvester equation](../HomologicalAlgebra/Preadditive/Sylvester.lean).

For the [triangular Drazin situation](#triangular-biproduct-formula), retain
its abelian category, both chain conditions on **each** of `X, Y`, unit `f`
and nilpotent `g`. With the same `T`, `q` and graph slope `u = f ≫ q`,
`End.eq_comp_inl_drazinInverse_biprod_triangular_snd_iff` says that an arbitrary
`v : X ⟶ Y` equals this canonical `u` exactly when
`f ≫ v = h + v ≫ g`. The solution is the graph slope `f ≫ q`, not generally
`q` or `h`.

Write `I = End.imageMulDrazinInverseBiprodTriangularIso f g h hf hg` and let
`ι` be the image inclusion. Then
`End.eq_imageMulDrazinInverseBiprodTriangularIso_inv_ι_iff` characterizes an
arbitrary `k : X ⟶ X ⊞ Y` by
`k = I.inv ≫ ι ↔ k ≫ biprod.fst = 𝟙 X ∧ k ≫ T = f ≫ k`.
Thus the inverse of the canonical image isomorphism followed by inclusion is
the unique normalized section that intertwines `f` and `T`. Both conditions
occur in the criterion: neither can in general be dropped. This is not
uniqueness of an arbitrary section or an arbitrary intertwiner. No extra
condition on `h` is imposed. The general Sylvester theorem itself does not
inherit these extra Drazin hypotheses.
[Graph characterizations](../HomologicalAlgebra/Abelian/DrazinTriangular.lean).

## Nilpotence in short complexes

Let `S` be a short complex in any category with zero morphisms, and let
`φ : S ⟶ S` be an endomorphism of that complex: its three components commute
with the two structure maps. In the namespace `CategoryTheory.ShortComplex`:

- `middle_pow_add_eq_zero hS φ m n h₁ h₃` needs only `hS : S.Exact`.
  If the left component's `m`th power and the right component's `n`th power
  vanish, the middle component's `(m + n)`th power vanishes.
- `left_pow_eq_zero_of_mono φ n h₂` needs only a monic first structure map;
  `right_pow_eq_zero_of_epi φ n h₂` needs only an epic second structure map.
  Each reflects a vanishing middle `n`th power to the indicated outer
  component with the **same** `n`; these two statements do not require
  exactness.
- `ShortExact.isNilpotent_middle_iff hS φ`, for `hS : S.ShortExact`, says
  that the middle component is nilpotent if and only if both outer components
  are. The reverse direction combines their possibly different witnesses
  `m, n` into `m + n`; the forward direction uses the same middle witness
  for both endpoints.

The power equations use `(End.of φ.τ₁ ^ m).asHom = 0` and the analogous
expressions for `τ₂, τ₃`, with the original zero morphisms and canonical
categorical endomorphism powers. Exponents are
arbitrary natural numbers, including zero and nonminimal witnesses; a
zeroth-power equation means the identity of that particular object is zero.
Object and morphism universes are independent. No abelian, preadditive,
finite-length, splitting or separate nonzero-object assumption is imposed.
The exponent bound in general is a sum, not the maximum of the outer bounds.
[Public module](../HomologicalAlgebra/ShortComplex/Endomorphism.lean).

## Local endomorphism rings

- **Local endomorphism rings.** An indecomposable Noetherian and Artinian
  object in an arbitrary abelian category has a local canonical endomorphism
  ring: `CategoryTheory.isLocalRing_end_of_indecomposable`. Every endomorphism
  is nilpotent or a unit, by
  `CategoryTheory.isNilpotent_or_isUnit_of_indecomposable`. The ring may be
  noncommutative, and object and morphism universes are independent.
  Indecomposability already excludes the zero object, so there is no extra
  nontriviality hypothesis. The proof uses the canonical Fitting biproduct
  and Mathlib's nilpotent and local-ring criteria.
  [Theorems](../HomologicalAlgebra/Abelian/LocalEndomorphism.lean).

## Indecomposability from locality

- **Indecomposability from locality.** In any preadditive category with binary
  biproducts, an object with a local canonical endomorphism ring is
  indecomposable, by `CategoryTheory.indecomposable_of_isLocalRing_end`.
  This uses Mathlib's original `Indecomposable` predicate and the possibly
  noncommutative ring `End X`, with independent object and morphism universes.
  No abelian structure, chain conditions, chosen zero object or separate
  nonzero hypothesis is needed. The binary-biproduct assumption is part of
  Mathlib's predicate. The proof uses the two projectors of a decomposition,
  the local-ring unit criterion and the fact that a unit idempotent is one.
  [Theorem](../HomologicalAlgebra/Preadditive/Indecomposable.lean).

## Finite Euler identities

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
  [Chain theorem](../HomologicalAlgebra/AdditiveEuler.lean),
  [cochain theorem](../HomologicalAlgebra/AdditiveEuler/Cochain.lean).

- **Additivity and exact-functor transport.** Native short exact sequences
  of chain complexes give additive term sums even for an empty interval; for
  homology sums, all three complexes must instead be termwise supported in
  the same nonempty interval. A functor preserving finite limits and finite
  colimits transports SES-additive invariants and compares mapped homology;
  the finite homology-sum comparison itself needs no support bound.
  [Exact-sequence and functorial results](../HomologicalAlgebra/AdditiveEuler/Functoriality.lean).

- **Finite support and native cochain shifts.** Signed sums over intervals
  separately containing the support agree, even for nonnested or empty
  intervals. The native shift by `n` uses degree `i+n`, moves term support
  `[a,b]` to `[a-n,b-n]`, and translates term and homology sums with factor
  `(-1)^n`. Term-sum reindexing needs neither support nor SES additivity;
  homology-sum translation uses isomorphism invariance from additivity but
  not a term-support bound.
  [Support and shift theorems](../HomologicalAlgebra/AdditiveEuler/Shift.lean).

- **Homology-bounded cochain LES additivity.** For a short exact cochain
  sequence `0 → A → B → D → 0`, the middle homology Euler sum equals the two
  outer sums **minus** `(-1)^a μ(im δ_(a-1))` and
  `(-1)^b μ(im δ_b)` for the native connecting maps and nonempty `[a,b]`.
  Vanishing of `H^(a-1)(D)` and `H^(b+1)(A)`, or native `D.IsGE a` and
  `A.IsLE b`, removes the corrections without termwise support or a bound
  on the middle complex.
  [Connecting-image results](../HomologicalAlgebra/AdditiveEuler/HomologySupport.lean).

- **Finite module length.** For a commutative **Noetherian Artinian** ring,
  integer-valued length of finitely generated modules is additive on native
  short exact sequences, supplying an Euler invariant. The bare definition
  of `lengthInvariant` does not assert this for arbitrary commutative rings.
  [Length instance](../HomologicalAlgebra/AdditiveEuler/Length.lean) and
  [nonsplit cochain client](../HomologicalAlgebraTest/AdditiveEuler/HomologySupport.lean).

## Hom complexes and K-objects

### Homotopy, contraction and vanishing

- **Hom-complex homotopy invariance and contraction in either variable.**
  For integer cochain complexes `K, L` in `C : Type u` with only
  `Category.{v} C` and `Preadditive C`,
  `CochainComplex.HomComplex.prePostcompHomotopy` returns a joint `Homotopy`
  from homotopies in both inputs. A supplied `Homotopy (𝟙 K) 0` or
  `Homotopy (𝟙 L) 0` gives a `Homotopy (𝟙 (HomComplex K L)) 0`, hence
  acyclicity in every integer degree. Object and morphism universes are
  independent, and the integer-indexed Hom complex uses unrestricted products
  of abelian groups. No boundedness, support, finiteness, projectivity,
  enough-projectives, abelian-category, zero-object, biproduct or additional
  linearity assumptions are needed.
  [Producer](../HomologicalAlgebra/Cochain/HomComplexFunctoriality.lean).

For integer cochain complexes `K, L` in any preadditive category and any
integer `n`, `CochainComplex.HomComplex.isZero_homology_iff` identifies
vanishing of degree-`n` Hom cohomology with null-homotopy of every cochain map
`K ⟶ L⟦n⟧`. The criterion `CochainComplex.HomComplex.acyclic_iff` identifies
acyclicity of the Hom complex with null-homotopy of every such map for every
integer `n`. The degree-zero specialization
`CochainComplex.HomComplex.isZero_homology_zero_iff` identifies vanishing of
degree-zero Hom cohomology with null-homotopy of every unshifted map `K ⟶ L`.
Object and morphism universes are independent; neither an abelian ambient
category nor a zero object is required. The Hom complex is the canonical
complex of abelian groups, not a complex formed using products in the ambient
category. Its degree-zero cohomology is nonzero for the rational stalk ℚ[0]
mapped to itself. [Producer](../HomologicalAlgebra/Cochain/HomComplexVanishing.lean).

For integer cochain complexes in an arbitrary preadditive category,
`CochainComplex.HomComplex.quasiIso_prePostcomp_of_homotopyEquiv` makes
`HomComplex.prePostcomp eK.hom eL.hom` a quasi-isomorphism from the Hom complex
of `(K₁, L₁)` to that of `(K₂, L₂)`, for homotopy equivalences
`eK : HomotopyEquiv K₂ K₁` and `eL : HomotopyEquiv L₁ L₂`.
`CochainComplex.HomComplex.quasiIso_prePostcomp_of_isIso_quotient_map` more
generally applies to `α : K₂ ⟶ K₁` and `β : L₁ ⟶ L₂` whose canonical
homotopy-quotient images are isomorphisms. Object and morphism universes are
independent, with no boundedness or support restrictions, products in the
coefficient category, projectivity, injectivity, or enough-projective/injective
hypotheses. The Hom complex is abelian-group-valued, so its homology requires
neither an abelian coefficient category nor homology in that category. For the
integer stalk ℤ[0], `H⁰(Hom(ℤ[0], ℤ[0])) ≃+ ℤ` sends the identity class to `1`,
so degree-zero Hom cohomology is nonzero.
The theorem `quasiIso_prePostcomp_preimage_of_homotopyEquiv` applies this to
supplied equivalences between images under a fully faithful additive functor,
using their canonical source preimages for both composition maps.
[Producer](../HomologicalAlgebra/Cochain/HomComplexQuasiIso.lean).

### K-projectivity and K-injectivity

For integer cochain complexes in any abelian category,
`CochainComplex.isKProjective_iff_acyclic_homComplex` characterizes K-projectivity
by acyclicity of the abelian-group-valued Hom complex into every acyclic target.
It requires neither boundedness nor degreewise projectivity, and the object and
morphism universes of the category are independent.
[Producer](../HomologicalAlgebra/Cochain/KProjective.lean).

- **K-injectivity via product Hom complexes.** For `C : Type u` with
  `Category.{v} C` and `Abelian C`, object and morphism universes are independent.
  `CochainComplex.isKInjective_iff_acyclic_homComplex` says that an integer cochain
  complex `L` is K-injective if and only if `HomComplex K L` is acyclic for every
  acyclic integer cochain complex `K`. This is the canonical `AddCommGrpCat.{v}`-valued
  product Hom complex, using unrestricted products of abelian groups, not
  products in `C`. No boundedness, conditions on individual terms, or
  enough-projectives/injectives hypotheses are required.
  [Producer](../HomologicalAlgebra/Cochain/KInjective.lean).

- **K-objects detected by one Hom-cohomology degree.** For any fixed `n : ℤ`,
  an integer cochain complex `K` in an arbitrary abelian category is K-projective
  if and only if `IsZero ((HomComplex K A).homology n)` for every acyclic `A`.
  Dually, `I` is K-injective if and only if
  `IsZero ((HomComplex A I).homology n)` for every acyclic `A`. Object and
  morphism universes are independent. The Hom complex is abelian-group-valued;
  no boundedness, products in the coefficient category, or projective or
  injective resolutions are required.
  [Producer](../HomologicalAlgebra/Cochain/HomComplexFixedDegreeCriteria.lean).

- **K-properties of homotopy retracts.** For integer cochain complexes in any
  abelian category `C : Type u` with `Category.{v} C`, K-projectivity and
  K-injectivity descend from `L` to `K` along maps `f : K ⟶ L`, `g : L ⟶ K`
  and a supplied `Homotopy (f ≫ g) (𝟙 K)`, by
  `CochainComplex.IsKProjective.of_homotopy_retract` and
  `CochainComplex.IsKInjective.of_homotopy_retract`. There is no condition on
  `g ≫ f`, nor a strict retraction or homotopy equivalence requirement.
  Object and morphism universes are independent; no boundedness, termwise
  projectivity/injectivity, enough-projectives/injectives or global limit
  assumptions are needed. The strict `of_retract` results are special cases.
  [Producer](../HomologicalAlgebra/Cochain/KHomotopy.lean).

- **K-properties under equivalences.** For abelian categories `C` and `D` and a
  categorical equivalence `F : C ⥤ D`,
  `CochainComplex.isKProjective_map_iff` and
  `CochainComplex.isKInjective_map_iff` identify the corresponding property of
  an unrestricted integer cochain complex `K` with that of
  `(F.mapHomologicalComplex (.up ℤ)).obj K`. The four object and morphism
  universes are independent. No separate additivity, boundedness or
  enough-projectives/injectives assumption is needed.
  [Producer](../HomologicalAlgebra/Cochain/KEquivalence.lean).

- **K-projectivity of arbitrary coproducts.** For integer cochain complexes in
  any abelian category, whenever the particular family `K` has a categorical
  coproduct, `CochainComplex.isKProjective_sigma_iff` identifies K-projectivity
  of `∐ K` with K-projectivity of every `K i`. Object, morphism and indexing
  universes are independent, and empty families are allowed. No global
  coproducts, boundedness, termwise projectivity, exactness of coproducts or
  enough-projectives assumption is required.
  [Producer](../HomologicalAlgebra/Cochain/KFamilyLimits.lean).

- **K-injectivity of arbitrary products.** For integer cochain complexes in any
  abelian category, whenever the particular family `F` has a categorical
  product, `CochainComplex.isKInjective_pi_iff` identifies K-injectivity of
  `∏ᶜ F` with K-injectivity of every `F i`. Object, morphism and indexing
  universes are independent, and empty families are allowed. No global
  products, boundedness, termwise injectivity, exactness of products or
  enough-injectives assumption is required.
  [Producer](../HomologicalAlgebra/Cochain/KFamilyLimits.lean).

For integer cochain complexes in any abelian category, a quasi-isomorphism
`q : X ⟶ Y` induces a quasi-isomorphism
`HomComplex.prePostcomp (𝟙 K) q` whenever `K` is K-projective, by
`CochainComplex.IsKProjective.quasiIso_prePostcomp`. The other complexes `X, Y`
are arbitrary. This applies in all integer degrees with independent object and
morphism universes, without boundedness, enough projectives or injectives, or
products in the coefficient category. This formulation of K-projectivity follows
Spaltenstein, *Resolutions of unbounded complexes*, §1; the proof uses Joël Riou's
Hom-complex, homotopy-category and derived-category comparisons in Mathlib.
[Producer](../HomologicalAlgebra/Cochain/HomComplexQuasiIso.lean).

Dually, for a K-injective complex `I`,
`CochainComplex.IsKInjective.quasiIso_prePostcomp` makes precomposition by any
quasi-isomorphism `f : K ⟶ L` a quasi-isomorphism
`HomComplex L I ⟶ HomComplex K I`. The complexes `K, L` are arbitrary, object
and morphism universes are independent, and there are no boundedness,
enough-injective, or product hypotheses. The rational stalk `ℚ[0]` over `ℤ`
provides a K-injective target with nonzero degree-zero cohomology.

### Homotopy limits and supplied equivalences

- **Diagonal homotopies and coproducts or products.** For arbitrary families of
  integer cochain complexes in a preadditive category, the canonical diagonal
  coproduct maps (respectively product maps) are homotopic if and only if each
  pair of component maps is homotopic. Both family coproducts or products are
  supplied; degree evaluation need only preserve the domain coproduct or the
  codomain product, respectively. In particular, the identity is homotopic to
  zero on the coproduct or product exactly when it is on every component.
  Object, morphism and indexing universes are independent, and empty indexing
  types are allowed. These are existence criteria, not equivalences of all
  homotopy data; no zero object or global limits are assumed.
  [Producer](../HomologicalAlgebra/Cochain/HomotopyLimits.lean).

- **Pulling back supplied homotopy equivalences.** For any complex shape and
  fully faithful additive functor between preadditive categories,
  `CategoryTheory.Functor.preimageHomotopyEquiv` returns a source homotopy
  equivalence from a supplied equivalence between the canonical images.
  Its maps are canonical preimages, and its component formulas and both
  round-trip identities preserve the two supplied homotopies as well.
  Object, morphism and shape-index universes are independent; no essential
  surjectivity, zero object, abelian structure or boundedness is required.
  [Producer](../HomologicalAlgebra/Homotopy/Functor.lean).

## Ordinary disks and bounded-below projective chains

- **Ordinary projectivity and injectivity of identity disks.** For any category
  `C : Type u` with `Category.{v} C`, zero morphisms and a zero object, and any
  `n : ℤ` and `X : C`, `CochainComplex.projective_disk_iff` and
  `CochainComplex.injective_disk_iff` characterize ordinary categorical
  projectivity and injectivity of `disk n X` by the corresponding property of
  `X`. The disk is supported in degrees `n` and `n + 1`, with identity
  differential between them. Object and morphism universes are independent;
  no additive, abelian, boundedness, enough-projectives/injectives, exactness
  or global limit assumptions are needed. These are ordinary
  `CategoryTheory.Projective` and `CategoryTheory.Injective` results, distinct
  from K-projectivity and K-injectivity. The proofs reuse the canonical disk
  adjunctions and Mathlib's general categorical transport.
  [Producer](../HomologicalAlgebra/Cochain/DiskProjectivity.lean).

### Bounded-below projective integer chains

`HomologicalAlgebra.ChainComplex.Projective` provides
`ChainComplex.quasiIso_iff_of_projective_of_isZero_below`. For an abelian category
`C`, integer chain complexes `K, L` with projective terms, independent integers
`a, b`, and termwise zero objects `K.X i` for `i < a` and `L.X i` for `i < b`,
it says that a particular `f : K ⟶ L` is a quasi-isomorphism if and only if
`∃ e : HomotopyEquiv K L, e.hom = f`. There is no bounded-above or
enough-projectives assumption, and object and morphism universes are independent.

The proof uses Mathlib's negation embedding, extension isomorphisms and
bounded-projective cochain criterion; it introduces no new indexing or
boundedness definition. For nonnegative chains use Mathlib's existing
`ChainComplex.quasiIso_iff_of_projective` directly.
The stalk client in `HomologicalAlgebraTest.ChainComplex.Projective` applies the
integer criterion to the zero endomorphism of a stalk on a nonzero projective
object, and records the sharp lower-support cutoff of that stalk.

## Noetherian objects

- **Binary biproduct closure.** In an abelian category,
  `CategoryTheory.isNoetherianObject_biprod` supplies
  `IsNoetherianObject (X ⊞ Y)` from Noetherian `X, Y` alone. Separately,
  `CategoryTheory.isArtinianObject_biprod` supplies the Artinian condition
  from Artinian `X, Y` alone. These are instances of the existing object
  classes, with independent object and morphism universes; no second chain
  condition or extra finite-biproduct assumption is needed.
  [Binary-closure instances](../HomologicalAlgebra/Abelian/ChainConditions.lean).

- **Reflection of Noetherian and Artinian objects.** For categories
  `C : Type u₁` and `D : Type u₂` with `Category.{v₁} C` and `Category.{v₂} D`,
  a functor `F : C ⥤ D` preserving monomorphisms and reflecting isomorphisms
  gives `IsNoetherianObject X` from `IsNoetherianObject (F.obj X)`, and
  separately `IsArtinianObject X` from `IsArtinianObject (F.obj X)`.
  All four universes are independent; no abelian, full, faithful, additive,
  smallness or well-poweredness assumption is required. The arguments reuse
  Mathlib's eventual-constancy criteria for chains in the category of
  monomorphisms into an object and its opposite, respectively, not an embedding
  of all subobjects. The Artinian argument takes the opposite at the chain
  level and needs no abelian duality.
  [`CategoryTheory.Functor.isNoetherianObject_of_obj`](../HomologicalAlgebra/NoetherianFunctor.lean),
  [`CategoryTheory.Functor.isArtinianObject_of_obj`](../HomologicalAlgebra/ArtinianFunctor.lean).

- **Noetherian and Artinian endomorphisms.** In any abelian category
  `C : Type u` with `Category.{v} C`, an epimorphic endomorphism of a
  Noetherian object is an isomorphism, by
  `CategoryTheory.isIso_of_epi_of_isNoetherianObject`. Dually,
  `CategoryTheory.isIso_of_mono_of_isArtinianObject` makes every monomorphic
  endomorphism of an Artinian object an isomorphism. Object and morphism
  universes are independent; there is no smallness, ring, finite-length or
  whole-category Noetherianity assumption. The module/object criteria give
  both special cases for modules over any ring, using the module's original
  scalar action and with independent scalar and carrier universes.
  [Categorical result](../HomologicalAlgebra/Abelian/Endomorphism.lean),
  [Noetherian module criterion](../HomologicalAlgebra/ShortComplex/ModuleCatNoetherian.lean),
  [Artinian module criterion](../HomologicalAlgebra/ModuleCat/Subobject.lean).

- **Noetherian homology.** The homology of a short complex in an abelian
  category is Noetherian whenever its middle object is Noetherian.
  For modules over any ring `R`, a Noetherian middle module gives Noetherian
  homology; no Noetherian-ring assumption is required.
  [Abelian-category theorem](../HomologicalAlgebra/ShortComplex/Noetherian.lean),
  [module theorem](../HomologicalAlgebra/ShortComplex/ModuleCatNoetherian.lean).

## Quotients, admissible layers and snake sequences

- **Chosen quotient-intersection pairing.** For subobjects `L ≤ U` and any
  `D` of an object in an abelian category, the specified map
  `U/(L ⊓ D) ⟶ (U/L) × (B/D)` is monic. Its two components are the actual
  chosen `cokernel.map` morphisms, with an aggregate equation after the chosen
  cokernel projection. Neither projection is asserted monic, and no `L ≤ D`
  hypothesis is needed. [Producer](../HomologicalAlgebra/Abelian/QuotientIntersection.lean),
  [ordinary-import client](../HomologicalAlgebraTest/Abelian/QuotientIntersection.lean),
  [standalone guide](QuotientIntersection.md).

- **Admissible layers and lower-cut reflection.** For a property `P` of the
  chosen quotient `U/L`, layers `(L,U)` are ordered with lower endpoint
  reversed and upper endpoint forward. `LowerBounded P B D` admits a
  monotone inclusion without closure hypotheses or `P(B/D)`; if `P` is
  closed under subobjects and binary products and `P (cokernel D.arrow)`,
  intersection `(L,U) ↦ (L ⊓ D,U)` is its **left** adjoint. The canonical
  monomorphism `U/(L ⊓ D) ⟶ (U/L) × (B/D)` proves admissibility without
  `L ≤ D` or quotient closure. The unit, exact reflector identity and native
  thin-category adjunction are public; no upper cut or transport to layers
  in `D` is asserted. [Producer](../HomologicalAlgebra/Abelian/AdmissibleLayers.lean),
  [ordinary-import client](../HomologicalAlgebraTest/Abelian/AdmissibleLayers.lean),
  [standalone guide](AdmissibleLayers.md).

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
  [Producer](../HomologicalAlgebra/Abelian/SnakeLemma.lean),
  [ordinary-import client](../HomologicalAlgebraTest/Abelian/SnakeLemma.lean).

## Fixed-arrow relative paths

- **Fixed-arrow cochain relative paths.** Under preadditivity, binary
  biproducts and **pullbacks**, the pullback of a fixed arrow `f : B₁ ⟶ B`
  along mathlib's native first path endpoint has a strict section,
  strict endpoint equations for lifts from *chosen* homotopies, and a
  homotopy equivalence to `B₁` whose inverse homotopy vanishes over the
  first projection. The object depends on `f`, not the chosen source or
  homotopy. This is not a quasi-isomorphism instance or a natural-in-arrow
  framework. [Producer](../HomologicalAlgebra/Cochain/RelativePath.lean),
  [ordinary-import client](../HomologicalAlgebraTest/Cochain/RelativePath.lean),
  [standalone guide](CochainRelativePath.md).

## Quadrant product totals

- **Quadrant product-total acyclicity.** For any `[Ring R]`, a native quadrant
  bicomplex of `ModuleCat R` has an unrestricted diagonal product total
  `productTotal K` in integer degrees `p-r`. Exact horizontal rows at **every**
  `r`, including `p=0`, give `(productTotal K).Acyclic` in **all integer
  degrees**. At target `(r,p)` of degree `k-1` its differential is
  `h(x_(r,p+1)) + (-1)^(k+1) δ(x_(r-1,p))`, with the second term zero at
  `r=0`; the map, identity and composition laws require no row exactness.
  Elementwise chosen lifts are not linear/natural splittings, and the result
  does not assert an arbitrary-unbounded assembly or exact-products axiom.
  [Producer](../HomologicalAlgebra/Homology/ProductTotalAcyclicity.lean),
  [ordinary-import client](../HomologicalAlgebraTest/Homology/ProductTotalAcyclicity.lean),
  [standalone guide](ProductTotalAcyclicity.md).

## Scope

The Euler statements concern finite sums, not an infinite Euler construction,
a canonical invariant from homology bounds alone, or a derived-category or
Grothendieck-group API. The relative-path construction has different,
nonabelian hypotheses and does not depend on an Euler invariant.
The abelian quotient-intersection pairing requires only `L ≤ U`, does not
assume ordinary lifting of maps across quotient epis, and does not depend
on the Euler or relative-path constructions.
