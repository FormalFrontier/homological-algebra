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
For snake inputs in abelian categories, it supplies exterior maps with kernel
and cokernel universal properties and proves the eight-object sequence exact
at its six interior objects, without assuming either exterior object vanishes.
Licensed under Apache-2.0
(see [LICENSE](LICENSE)).

## Headline results

- **Noetherian and Artinian binary biproducts.** In any abelian category,
  `CategoryTheory.isNoetherianObject_biprod` gives
  `IsNoetherianObject (X ⊞ Y)` from Noetherian `X` and `Y` alone;
  separately, `CategoryTheory.isArtinianObject_biprod` gives
  `IsArtinianObject (X ⊞ Y)` from Artinian `X` and `Y` alone.
  These are instances of the existing object classes, with independent object
  and morphism universes and no additional finite-biproduct hypothesis.
  [Binary closure](HomologicalAlgebra/Abelian/ChainConditions.lean).

- **Canonical finite-length bounds for endomorphisms.** Write
  `L = (CategoryTheory.objectLength X).toNat`. If `objectLength X ≠ ⊤`,
  power kernels stabilize by `L` in a category with zero morphisms and kernels,
  and every nilpotent endomorphism `g` satisfies `g ^ L = 0`. Power images
  stabilize by `L` in a category with images and image maps.
  For an endomorphism `f` of a Noetherian and Artinian object in an abelian
  category, write `D = CategoryTheory.End.drazinInverse f`. For all `n ≥ L`,
  the kernel and image of `f ^ n` equal those of `f * D`; moreover,
  `f ^ (L + 1) * D = f ^ L` and `(f * (1 - f * D)) ^ L = 0`.
  These uniform bounds include `L = 0` and need not be least for a given map.
  [Power bounds](HomologicalAlgebra/Abelian/EndomorphismPowerLength.lean),
  [Drazin bounds](HomologicalAlgebra/Abelian/DrazinLength.lean).

- **Uniqueness of finite biproduct factors.** In a preadditive category, two
  finite families with local canonical endomorphism rings and isomorphic
  biproducts admit an equivalence of their index types and componentwise
  isomorphisms. Only the two given biproducts are assumed: no global finite
  biproducts, abelian structure, chain conditions or idempotent completeness
  is required. Object, morphism and both index universes are independent.
  Repeated factors are allowed; the matching itself need not be unique, and
  the supplied total isomorphism need not be permutation-diagonal.
  [Theorem](HomologicalAlgebra/Preadditive/BiproductUniqueness.lean).

- **Finite indecomposable decompositions.** An Artinian object, or separately a
  Noetherian object, is isomorphic to a finite biproduct of nonzero
  indecomposable objects in any category with zero morphisms and finite
  biproducts. The zero object has the empty decomposition. Object and morphism
  universes are independent; no abelian or preadditive structure, idempotent
  completeness, second chain condition, or uniqueness hypothesis is required.
  [Existence theorems](HomologicalAlgebra/Indecomposable.lean) reuse Mathlib's
  indecomposability and chain conditions; the
  [biproduct API](HomologicalAlgebra/Indecomposable/Biproducts.lean) gives
  isomorphism transport, injection criteria, and a finite-family append comparison.

- **Finite-length decompositions with local endomorphism rings.** A Noetherian
  and Artinian object in an abelian category is isomorphic to a finite biproduct
  whose factors have local canonical endomorphism rings, by
  `CategoryTheory.exists_finite_biproduct_isLocalRing_end`. The rings may be
  noncommutative, object and morphism universes are independent, and zero has
  the empty decomposition.
  [Theorem](HomologicalAlgebra/Abelian/FiniteLength.lean).

- **Cancellation of finite-length summands.** If `X` is Noetherian and Artinian
  in an abelian category, an isomorphism `X ⊞ Y ≅ X ⊞ Z` implies
  `Nonempty (Y ≅ Z)`. The remaining objects are unrestricted: neither chain
  conditions nor locality of their endomorphism rings is assumed. The
  endomorphism ring of `X` need not be local, zero objects are allowed, and
  object and morphism universes are independent. The conclusion does not
  select a canonical isomorphism.
  [Theorem](HomologicalAlgebra/Abelian/FiniteLengthCancellation.lean).

- **Subobject correspondence and modularity.** For every object `A` in an
  arbitrary abelian category, the canonical `CategoryTheory.Subobject A`
  forms a modular lattice, with the stock `IsModularLattice` instance.
  `CategoryTheory.Abelian.Subobject.epiOrderIso` identifies subobjects of an
  epimorphism's codomain with subobjects of its domain containing its kernel:
  the forward map is pullback and the inverse is direct image.
  `CategoryTheory.Abelian.Subobject.cokernelOrderIso` specializes this
  correspondence to a subobject's cokernel. Object and morphism universes
  are independent; no `WellPowered`, smallness or chain-condition hypotheses
  are required.
  [Theorems](HomologicalAlgebra/Abelian/Subobject.lean).

- **Composition series and Jordan–Hölder.** A Noetherian and Artinian object
  in an arbitrary abelian category admits a finite composition series of
  canonical subobjects, with head `⊥`, last `⊤`, and simple successive
  cokernel factors. For any two given composition series with equal heads
  and equal lasts, the lengths agree and a bijection of factor indices
  carries factors to isomorphic quotient objects. This uniqueness needs no
  chain conditions or bottom/top assumptions. The zero object has length
  zero and an empty factor family. Object and morphism universes are
  independent; no smallness hypotheses are required.
  [Composition-series API](HomologicalAlgebra/Abelian/JordanHolder.lean).

- **Categorical object length and short-exact additivity.** For an object `X`
  in any category, `CategoryTheory.objectLength X : ℕ∞` is the height of the
  largest canonical subobject. It is isomorphism-invariant and monotone under
  monomorphisms. With only a zero object, length zero characterizes zero
  objects; with zero morphisms as well, length one characterizes simple objects.
  In any abelian category, every short exact sequence `0 → A → B → D → 0`
  satisfies `objectLength B = objectLength A + objectLength D`, including
  infinite lengths, with no finiteness or splitting hypothesis. Length is
  finite exactly when the object is both Noetherian and Artinian. A given
  composition series from `⊥` to `⊤` computes length by its number of steps,
  with the canonical adjacent-inclusion cokernels as factors. Object and
  morphism universes are independent; no smallness assumption is needed.
  [Object length and short exact sequences](HomologicalAlgebra/Abelian/Length.lean),
  [modular height and cover series](HomologicalAlgebra/Order/Length.lean).
  Over any ring, categorical length agrees with Mathlib's `Module.length`,
  with independent ring and module universes.
  [Module comparison](HomologicalAlgebra/Abelian/ModuleCatLength.lean).

- **Fitting decomposition.** For an endomorphism `f` of a Noetherian and
  Artinian object in an arbitrary abelian category, the kernel and image of
  every sufficiently high power `f ^ n` are complementary. The canonical
  copairing of their inclusions is an isomorphism. The restriction of `f` to
  the kernel is nilpotent and its restriction to the image is invertible,
  with the corresponding block-intertwining equation on one common tail.
  Object and morphism universes are independent. The ModuleCat subobject
  comparison transports the complementarity conclusion to kernels and ranges
  of linear-map powers over any ring, without a commutativity hypothesis.
  [Categorical decomposition](HomologicalAlgebra/Abelian/Fitting.lean),
  [canonical restrictions and powers](HomologicalAlgebra/Abelian/EndomorphismPowers.lean),
  [module agreement](HomologicalAlgebra/ModuleCat/Subobject.lean).

- **Fitting naturality and mixed-Hom vanishing.** An arbitrary intertwiner
  `p : X ⟶ Y` induces a natural square of power-kernel/image copairings at
  every exponent, given the displayed kernels, images, image map and two
  biproducts. If both objects are Noetherian and Artinian in an abelian
  category, the canonical Fitting isomorphisms put `p` in block-diagonal form
  on one common tail; `p` need not be monic, epic or invertible. In any
  category with zero morphisms, an intertwiner from a nilpotent endomorphism
  to a monomorphic one is zero, and dually from an epimorphic endomorphism
  to a nilpotent one.
  [Naturality](HomologicalAlgebra/Abelian/FittingNaturality.lean),
  [generic copairing and vanishing laws](HomologicalAlgebra/Abelian/EndomorphismPowers.lean).

- **Cyclic powers and nilpotence.** For arbitrary morphisms `a : X ⟶ Y`
  and `b : Y ⟶ X` in a category, the successor-power identity
  `(a ≫ b)^(n+1) = a ≫ ((b ≫ a)^n) ≫ b` holds for every natural `n`,
  including zero. With zero morphisms, the two composites are nilpotent
  simultaneously; a witness exponent transfers with an increase of one.
  No chain condition, additivity, invertibility or identification of the
  objects is required. A same-object operation-value lemma agrees with
  Mathlib's monoid shuffle in the canonical endomorphism monoid.
  [Cyclic-product power API](HomologicalAlgebra/Abelian/EndomorphismCyclicProducts.lean).

- **Block intertwiners and canonical summand isomorphisms.** In a category
  with zero morphisms, `biprod.isIso_map_iff` characterizes invertibility of
  `biprod.map f g` by invertibility of both components; `biprod.mapIso_asIso`
  identifies the biproduct of their canonical isomorphisms with
  `asIso (biprod.map f g)`. Only the source and target binary biproducts are
  required, and object and morphism universes are independent. For
  `p : N ⊞ I ⟶ Nprime ⊞ Iprime` satisfying
  `biprod.map n i ≫ p = p ≫ biprod.map nprime iprime`, nilpotence of `n` and
  `nprime`, epicity of `i` and monicity of `iprime` force both off-diagonal
  corners to vanish and express arbitrary `p` as the map of its diagonal
  corners. If `p` is additionally invertible,
  `CategoryTheory.End.biprodLeftIso` and `CategoryTheory.End.biprodRightIso`
  give canonical isomorphisms `N ≅ Nprime` and `I ≅ Iprime`. Their homs are
  the diagonal corners of `p`, their inverses are the diagonal corners of
  `inv p`, and their `biprod.mapIso` equals `asIso p`. This concerns the
  original four summands, unlike the common-tail canonical power-kernel/image
  Fitting isomorphisms above for Noetherian and Artinian objects in an abelian
  category. The local-pair invertibility criterion generalizes
  Mathlib's reverse implications under global binary biproducts.
  [API](HomologicalAlgebra/Abelian/BiproductIntertwiners.lean).

- **Canonical Drazin inverses.** For an endomorphism `f : End X` of a
  Noetherian and Artinian object in any abelian category,
  `CategoryTheory.End.drazinInverse f` is the unique `g` satisfying
  `Commute f g`, `g * f * g = g` and
  `∃ n : ℕ, f ^ (n + 1) * g = f ^ n`. Only `g` is unique; the exponent
  need not be unique and may be zero. The inverse is zero exactly for
  nilpotent inputs, agrees with `CategoryTheory.inv f` for isomorphisms and
  fixes idempotents. The product `f * drazinInverse f` is an idempotent
  projector. The original endomorphism multiplication is `p * q = q ≫ p`.
  Object and morphism universes are independent, with no nonzero-object or
  commutativity hypothesis and no supplied decomposition.
  Multiplicative maps `φ : End X → End Y`, not necessarily unital or
  zero-preserving, preserve these inverses when both objects are
  Noetherian and Artinian in abelian categories, with independent source
  and target object and morphism universes. In particular, any functor `F`
  between abelian categories preserves them when both `X` and `F.obj X`
  are Noetherian and Artinian; no additivity or exactness is required.
  For `f : End X` and `g : End Y` in the same abelian category, with
  each object Noetherian and Artinian, every `p : X ⟶ Y` satisfying
  `f ≫ p = p ≫ g` also satisfies
  `drazinInverse f ≫ p = p ≫ drazinInverse g`, without requiring `p`
  to be monic, epic or invertible. Endomorphisms commuting with `f` also
  commute with its Drazin inverse. For every `n : ℕ`, including zero,
  `drazinInverse (f ^ n) = (drazinInverse f) ^ n`.
  For commuting `f, g : End X`, `Commute.drazinInverse_mul` gives
  `drazinInverse (f * g) = drazinInverse f * drazinInverse g`.
  The theorem `CategoryTheory.End.drazinInverse_drazinInverse` gives
  `drazinInverse (drazinInverse f) = f * drazinInverse f * f`.
  The double inverse need not equal `f`: it is zero for a nonzero
  nilpotent input.
  [Value and characteristic API](HomologicalAlgebra/Abelian/Drazin.lean).

- **Drazin inverses of orthogonal sums.** For `f, g : End X`, with `X`
  Noetherian and Artinian in an arbitrary abelian category,
  `f * g = 0` and `g * f = 0` imply
  `drazinInverse (f + g) = drazinInverse f + drazinInverse g`.
  For any index type `ι`, support `s : Finset ι` and family `f : ι → End X`,
  if `f i * f j = 0` for every ordered pair of distinct indices `i, j ∈ s`,
  then `drazinInverse (∑ i ∈ s, f i) = ∑ i ∈ s, drazinInverse (f i)`.
  The condition includes both product orders, is restricted to `s` and does
  not discard equal values at distinct indices; `ι` need not be finite.
  Empty and singleton supports and zero objects are allowed. Characteristic
  exponent zero is allowed; no positive or common index is supplied.
  The canonical endomorphism ring may be noncommutative, with
  `f * g = g ≫ f`, and object, morphism and index universes are independent.
  These are conditional laws, not global additivity of `drazinInverse`.
  [Orthogonal-sum theorems](HomologicalAlgebra/Abelian/DrazinAdditivity.lean).

- **Cyclic products and projector images.** For arbitrary `a : X ⟶ Y` and
  `b : Y ⟶ X` between Noetherian and Artinian objects of an abelian category,
  Cline's formula gives
  `drazinInverse (a ≫ b) = a ≫ (drazinInverse (b ≫ a)) ^ 2 ≫ b`.
  The projector `drazinInverse (a ≫ b) ≫ (a ≫ b)` also equals
  `a ≫ drazinInverse (b ≫ a) ≫ b`. The canonical `Limits.image` objects of
  the two projectors are isomorphic: the forward map is induced by `a` and
  its inverse by `b ≫ drazinInverse (a ≫ b)`. Inclusion and image-map
  equations characterize this isomorphism, which intertwines the induced
  cyclic-product endomorphisms. Neither an ambient isomorphism `X ≅ Y` nor
  invertibility or a supplied splitting of `a` or `b` is assumed.
  Object and morphism universes remain independent.
  [Cyclic-product and image-comparison API](HomologicalAlgebra/Abelian/DrazinCyclic.lean).

- **Drazin projectors and stable subobjects.** For an endomorphism `f` of a
  Noetherian and Artinian object in an arbitrary abelian category, the canonical
  kernel and image subobjects of sufficiently high powers `f ^ n` equal those
  of `f * drazinInverse f`. The complementary component
  `f * (1 - f * drazinInverse f)` is nilpotent; the idempotent complement itself
  need not be nilpotent. Object and morphism universes are independent, and
  neither a stabilization threshold nor a positive index is supplied.
  [Projector subobject API](HomologicalAlgebra/Abelian/DrazinProjector.lean).

- **Commuting nilpotent perturbations.** For `f, n : End X` on a Noetherian
  and Artinian object in an abelian category, assume `Commute f n` and nilpotence
  of `n`. The Drazin inverse generally changes, but the stable-image projector
  satisfies `(f + n) * drazinInverse (f + n) = f * drazinInverse f`.
  Any witness `n ^ m = 0` gives the explicit finite geometric formula
  `drazinInverse (f + n) = ∑ k ∈ Finset.range m, (-(drazinInverse f * n)) ^ k * drazinInverse f`.
  No positivity or minimality of `m` is required: a zero witness forces
  `𝟙 X = 0`, and the sum is empty.
  [Perturbation formulas](HomologicalAlgebra/Abelian/DrazinPerturbation.lean).

- **Drazin inverses of triangular biproducts.** For Noetherian and Artinian
  objects `X, Y` in an abelian category, let `f : End X` be a unit and
  `g : End Y` satisfy `g ^ n = 0`. For arbitrary `h : X ⟶ Y`, the
  Drazin inverse of `Biprod.ofComponents f h 0 g` has components
  `drazinInverse f`,
  `∑ i ∈ Finset.range n, ((drazinInverse f) ^ (i + 2)) ≫ h ≫ (g ^ i)`,
  `0` and `0`, in source-first order. No intertwining condition on `h`
  is imposed. The witness may be zero or nonminimal; a zero witness forces
  only `𝟙 Y = 0`. Object and morphism universes are independent.
  [Triangular formula](HomologicalAlgebra/Abelian/DrazinTriangular.lean).

- **Local endomorphism rings.** An indecomposable Noetherian and Artinian
  object in an arbitrary abelian category has a local canonical endomorphism
  ring: `CategoryTheory.isLocalRing_end_of_indecomposable`. Every endomorphism
  is nilpotent or a unit, by
  `CategoryTheory.isNilpotent_or_isUnit_of_indecomposable`. The ring may be
  noncommutative, and object and morphism universes are independent.
  Indecomposability already excludes the zero object, so there is no extra
  nontriviality hypothesis. The proof uses the canonical Fitting biproduct
  and Mathlib's nilpotent and local-ring criteria.
  [Theorems](HomologicalAlgebra/Abelian/LocalEndomorphism.lean).

- **Indecomposability from locality.** In any preadditive category with binary
  biproducts, an object with a local canonical endomorphism ring is
  indecomposable, by `CategoryTheory.indecomposable_of_isLocalRing_end`.
  This uses Mathlib's original `Indecomposable` predicate and the possibly
  noncommutative ring `End X`, with independent object and morphism universes.
  No abelian structure, chain conditions, chosen zero object or separate
  nonzero hypothesis is needed. The binary-biproduct assumption is part of
  Mathlib's predicate. The proof uses the two projectors of a decomposition,
  the local-ring unit criterion and the fact that a unit idempotent is one.
  [Theorem](HomologicalAlgebra/Preadditive/Indecomposable.lean).

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
  [Categorical result](HomologicalAlgebra/Abelian/Endomorphism.lean),
  [Noetherian module criterion](HomologicalAlgebra/ShortComplex/ModuleCatNoetherian.lean),
  [Artinian module criterion](HomologicalAlgebra/ModuleCat/Subobject.lean).

- **Noetherian homology.** The homology of a short complex in an abelian
  category is Noetherian whenever its middle object is Noetherian.
  For modules over any ring `R`, a Noetherian middle module gives Noetherian
  homology; no Noetherian-ring assumption is required.
  [Abelian-category theorem](HomologicalAlgebra/ShortComplex/Noetherian.lean),
  [module theorem](HomologicalAlgebra/ShortComplex/ModuleCatNoetherian.lean).

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
  [Producer](HomologicalAlgebra/Cochain/HomotopyLimits.lean).

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
  [Producer](HomologicalAlgebra/Cochain/DiskProjectivity.lean).

- **Pulling back supplied homotopy equivalences.** For any complex shape and
  fully faithful additive functor between preadditive categories,
  `CategoryTheory.Functor.preimageHomotopyEquiv` returns a source homotopy
  equivalence from a supplied equivalence between the canonical images.
  Its maps are canonical preimages, and its component formulas and both
  round-trip identities preserve the two supplied homotopies as well.
  Object, morphism and shape-index universes are independent; no essential
  surjectivity, zero object, abelian structure or boundedness is required.
  [Producer](HomologicalAlgebra/Homotopy/Functor.lean).

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
  [Producer](HomologicalAlgebra/Cochain/HomComplexFunctoriality.lean).

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
mapped to itself. [Producer](HomologicalAlgebra/Cochain/HomComplexVanishing.lean).

For integer cochain complexes in any abelian category,
`CochainComplex.isKProjective_iff_acyclic_homComplex` characterizes K-projectivity
by acyclicity of the abelian-group-valued Hom complex into every acyclic target.
It requires neither boundedness nor degreewise projectivity, and the object and
morphism universes of the category are independent.
[Producer](HomologicalAlgebra/Cochain/KProjective.lean).

- **K-injectivity via product Hom complexes.** For `C : Type u` with
  `Category.{v} C` and `Abelian C`, object and morphism universes are independent.
  `CochainComplex.isKInjective_iff_acyclic_homComplex` says that an integer cochain
  complex `L` is K-injective if and only if `HomComplex K L` is acyclic for every
  acyclic integer cochain complex `K`. This is the canonical `AddCommGrpCat.{v}`-valued
  product Hom complex, using unrestricted products of abelian groups, not
  products in `C`. No boundedness, conditions on individual terms, or
  enough-projectives/injectives hypotheses are required.
  [Producer](HomologicalAlgebra/Cochain/KInjective.lean).

- **K-objects detected by one Hom-cohomology degree.** For any fixed `n : ℤ`,
  an integer cochain complex `K` in an arbitrary abelian category is K-projective
  if and only if `IsZero ((HomComplex K A).homology n)` for every acyclic `A`.
  Dually, `I` is K-injective if and only if
  `IsZero ((HomComplex A I).homology n)` for every acyclic `A`. Object and
  morphism universes are independent. The Hom complex is abelian-group-valued;
  no boundedness, products in the coefficient category, or projective or
  injective resolutions are required.
  [Producer](HomologicalAlgebra/Cochain/HomComplexFixedDegreeCriteria.lean).

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
  [Producer](HomologicalAlgebra/Cochain/KHomotopy.lean).

- **K-properties under equivalences.** For abelian categories `C` and `D` and a
  categorical equivalence `F : C ⥤ D`,
  `CochainComplex.isKProjective_map_iff` and
  `CochainComplex.isKInjective_map_iff` identify the corresponding property of
  an unrestricted integer cochain complex `K` with that of
  `(F.mapHomologicalComplex (.up ℤ)).obj K`. The four object and morphism
  universes are independent. No separate additivity, boundedness or
  enough-projectives/injectives assumption is needed.
  [Producer](HomologicalAlgebra/Cochain/KEquivalence.lean).

- **K-projectivity of arbitrary coproducts.** For integer cochain complexes in
  any abelian category, whenever the particular family `K` has a categorical
  coproduct, `CochainComplex.isKProjective_sigma_iff` identifies K-projectivity
  of `∐ K` with K-projectivity of every `K i`. Object, morphism and indexing
  universes are independent, and empty families are allowed. No global
  coproducts, boundedness, termwise projectivity, exactness of coproducts or
  enough-projectives assumption is required.
  [Producer](HomologicalAlgebra/Cochain/KFamilyLimits.lean).

- **K-injectivity of arbitrary products.** For integer cochain complexes in any
  abelian category, whenever the particular family `F` has a categorical
  product, `CochainComplex.isKInjective_pi_iff` identifies K-injectivity of
  `∏ᶜ F` with K-injectivity of every `F i`. Object, morphism and indexing
  universes are independent, and empty families are allowed. No global
  products, boundedness, termwise injectivity, exactness of products or
  enough-injectives assumption is required.
  [Producer](HomologicalAlgebra/Cochain/KFamilyLimits.lean).

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
[Producer](HomologicalAlgebra/Cochain/HomComplexQuasiIso.lean).

For integer cochain complexes in any abelian category, a quasi-isomorphism
`q : X ⟶ Y` induces a quasi-isomorphism
`HomComplex.prePostcomp (𝟙 K) q` whenever `K` is K-projective, by
`CochainComplex.IsKProjective.quasiIso_prePostcomp`. The other complexes `X, Y`
are arbitrary. This applies in all integer degrees with independent object and
morphism universes, without boundedness, enough projectives or injectives, or
products in the coefficient category. This formulation of K-projectivity follows
Spaltenstein, *Resolutions of unbounded complexes*, §1; the proof uses Joël Riou's
Hom-complex, homotopy-category and derived-category comparisons in Mathlib.
[Producer](HomologicalAlgebra/Cochain/HomComplexQuasiIso.lean).

Dually, for a K-injective complex `I`,
`CochainComplex.IsKInjective.quasiIso_prePostcomp` makes precomposition by any
quasi-isomorphism `f : K ⟶ L` a quasi-isomorphism
`HomComplex L I ⟶ HomComplex K I`. The complexes `K, L` are arbitrary, object
and morphism universes are independent, and there are no boundedness,
enough-injective, or product hypotheses. The rational stalk `ℚ[0]` over `ℤ`
provides a K-injective target with nonzero degree-zero cohomology.

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
  [Producer](HomologicalAlgebra/Abelian/SnakeLemma.lean),
  [ordinary-import client](HomologicalAlgebraTest/Abelian/SnakeLemma.lean).
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

## Using the library

Import `HomologicalAlgebra` or the focused public modules
`HomologicalAlgebra.AdditiveEuler` and
`HomologicalAlgebra.AdditiveEuler.Length`, or the exact-sequence and exact-functor
extension `HomologicalAlgebra.AdditiveEuler.Functoriality`, the finite-support
and native cochain-shift module `HomologicalAlgebra.AdditiveEuler.Shift`, the
finite-interval cochain Euler module `HomologicalAlgebra.AdditiveEuler.Cochain`,
or the native long-exact-sequence module
`HomologicalAlgebra.AdditiveEuler.HomologySupport`.
For categorical object length and its short-exact formulas, import
`HomologicalAlgebra.Abelian.Length` (or `HomologicalAlgebra`); for agreement
with module length over any ring, import `HomologicalAlgebra.Abelian.ModuleCatLength`.
The generic modular-lattice results are in `HomologicalAlgebra.Order.Length`.
For Hom-complex homotopy invariance and contractions in either variable, use
`HomologicalAlgebra.Cochain.HomComplexFunctoriality`; see
[Hom-complex homotopy and contractibility](docs/HomComplexHomotopy.md).
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
For the canonical Fitting decomposition, import
`HomologicalAlgebra.Abelian.Fitting` (or `HomologicalAlgebra`). The restrictions
and power-chain API are in `HomologicalAlgebra.Abelian.EndomorphismPowers`;
`HomologicalAlgebra.ModuleCat.Subobject` identifies kernels and images of module
morphisms with the corresponding submodules, including complementarity of power
kernels and images. For arbitrary intertwiners and the resulting block-diagonal
Fitting coordinates, import `HomologicalAlgebra.Abelian.FittingNaturality`.
The existing Noetherian criterion is in `HomologicalAlgebra.ShortComplex.ModuleCatNoetherian`.
For rectangular composite powers and nilpotence, import
`HomologicalAlgebra.Abelian.EndomorphismCyclicProducts` (or `HomologicalAlgebra`).
For the canonical Drazin inverse, import
`HomologicalAlgebra.Abelian.Drazin` (or `HomologicalAlgebra`). Its
`CategoryTheory.End` API includes `eq_drazinInverse_iff` and
`existsUnique_drazinInverse`, so the characteristic equations determine the
value without unfolding its noncomputable construction.
For its eventual canonical kernel and image subobjects and the nilpotent
complementary component, import `HomologicalAlgebra.Abelian.DrazinProjector`
(or `HomologicalAlgebra`).
For Cline's cyclic-product identities and the canonical comparison between
Drazin-projector images, import `HomologicalAlgebra.Abelian.DrazinCyclic`
(or `HomologicalAlgebra`).
For cancellation of a Noetherian and Artinian summand against arbitrary
remaining objects, import `HomologicalAlgebra.Abelian.FiniteLengthCancellation`
(or `HomologicalAlgebra`). The proof uses finite local-End decomposition and
one-factor cancellation from the stable-range library.
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
and checked examples, see [Finite Euler invariants](docs/AdditiveEuler.md).
The guide distinguishes termwise support from neighboring homology bounds,
including the nonsplit and torsion-valued clients.

### Non-Euler checked examples

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

## Provenance and limits

Prism wrote the original Euler, exact-functor, LES, relative-path and
quotient-intersection mathematical expositions, distinct from the original
Lean proof authors. The [contributor credits](CREDITS.md)
distinguish proof, independent mathematical/code review, admissible-layer
repair and documentation contributions and preserve upstream Mathlib notices.
Formal Frontier Agents developed this work with AI assistance.

The work does **not** establish the K₀ presentation,
general homologically-bounded Euler identities, arbitrary-arrow path
naturality, unrestricted long-exact-sequence theory beyond the finite-interval
cochain formula, a derived-category result or completion of a source.

## References

- Huanyin Chen and Marjan Sheibani Abdolyousefi,
  [*Cline's formula for g-Drazin inverses in a ring*](https://doi.org/10.2298/FIL1908249C),
  Filomat **33**(8) (2019), 2249–2255: a generalized-Drazin ring treatment of
  the cyclic identity, distinct from the categorical finite-length formulation.
- Charles A. Weibel, *The K-book*, Chapter II, §6: motivates the adapted
  SES-additive formulation and finite Euler argument.
- Jürgen Neukirch, Alexander Schmidt and Kay Wingberg, *Cohomology of Number
  Fields*, corrected second edition, (1.3.1): the abelian-group snake diagram
  motivates the eight-object sequence in arbitrary abelian categories.
- The classical local-endomorphism-ring Krull–Schmidt uniqueness argument;
  Mathlib's categorical Gaussian elimination and additive envelope supply
  the cancellation and completion APIs.
- Mathlib's preadditive biproduct identities, noncommutative local-ring unit
  criterion and unit-idempotent lemma for indecomposability from locality.
- Mathlib's native short exact sequences, homology, shifts and path objects;
  `CategoryTheory.ShortComplex.SnakeInput.snake_lemma` provides the middle
  six-term snake sequence.
