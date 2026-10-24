# Hom-complex homotopy and contractibility in either variable

## Scope and conventions

Let `C : Type u` have `Category.{v} C` and `Preadditive C`, with **independent** universes `u` and `v`. All complexes are unrestricted `ℤ`-indexed cochain complexes. There are no boundedness, support, finiteness, abelian-category, zero-object, biproduct or additional linearity hypotheses.

Mathlib's `CochainComplex.HomComplex K L` is a cochain complex in **`AddCommGrpCat`**, not `ModuleCat ℤ`. Its degree objects are unrestricted product families of morphisms. `Homotopy` below is Mathlib's **root** structure, not a structure in the `HomologicalComplex` namespace and not merely a homotopy-class equality.

The underlying cochain, homotopy, mapping-cone and homology APIs are Mathlib's. The existing homological-algebra operation `prePostcomp`, including its application/component, identity, composition and homology-naturality API, is retained unchanged. In particular,

\[
 (\operatorname{prePostcomp}(\alpha,\beta)\varphi)_{p,q}
   =\alpha_p\,\varphi_{p,q}\,\beta_q.
\]

Composition here is in diagrammatic order, as for `≫`.

The common parameters for the type signatures below are:

```lean
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex.HomComplex
variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K K' L L' : CochainComplex C ℤ}
```

## One dataful joint homotopy

```lean
noncomputable def prePostcompHomotopy
    {α0 α1 : K' ⟶ K} {β0 β1 : L ⟶ L'}
    (hα : Homotopy α0 α1) (hβ : Homotopy β0 β1) :
    Homotopy (prePostcomp α0 β0) (prePostcomp α1 β1)
```

This is one constructor returning a `Homotopy` value. It requires no new maps, wrapper functors or typeclasses. Fix its choice of data by telescoping **the first variable at `β0`, then the second variable at `α1`**, through the intermediate map `prePostcomp α1 β0`:

\[
 \alpha_0\varphi\beta_0-\alpha_1\varphi\beta_1
 = (\alpha_0-\alpha_1)\varphi\beta_0
   +\alpha_1\varphi(\beta_0-\beta_1).
\]

Its degree-`n` to degree-`m` operator is zero unless `m + 1 = n`. On that relation, for `p + m = q`, its component is exactly

\[
 (-1)^n\bigl(h^\alpha_{p,p-1}\,\varphi_{p-1,q}\,(\beta_0)_q\bigr)
 + (\alpha_1)_p\,\varphi_{p,q+1}\,h^\beta_{q+1,q}.
\]

Thus the sign belongs to the **first** summand and uses the input degree `n`. For arbitrary `m`, the related case reduces to `m = n - 1`; the unrelated case is governed by the `Homotopy.zero` field with `¬ (ComplexShape.up ℤ).Rel m n`. No separate off-relation construction is needed.

The characteristic application and component API uses the canonical related degree, without redundant arithmetic hypotheses:

```lean
lemma prePostcompHomotopy_hom_apply
    {α0 α1 : K' ⟶ K} {β0 β1 : L ⟶ L'}
    (hα : Homotopy α0 α1) (hβ : Homotopy β0 β1)
    (n : ℤ) (φ : Cochain K L n) :
    (prePostcompHomotopy hα hβ).hom n (n - 1) φ =
      n.negOnePow •
        (((Cochain.ofHomotopy hα).comp φ (by omega)).comp
          (Cochain.ofHom β0) (add_zero (n - 1))) +
      (Cochain.ofHom α1).comp
        (φ.comp (Cochain.ofHomotopy hβ) (by omega))
        (zero_add (n - 1))

lemma prePostcompHomotopy_hom_v
    {α0 α1 : K' ⟶ K} {β0 β1 : L ⟶ L'}
    (hα : Homotopy α0 α1) (hβ : Homotopy β0 β1)
    (n : ℤ) (φ : Cochain K L n)
    (p q : ℤ) (hpq : p + (n - 1) = q) :
    ((prePostcompHomotopy hα hβ).hom n (n - 1) φ).v p q hpq =
      n.negOnePow •
        (hα.hom p (p - 1) ≫ φ.v (p - 1) q (by omega) ≫ β0.f q) +
      α1.f p ≫ φ.v p (q + 1) (by omega) ≫ hβ.hom (q + 1) q
```

The application lemma describes the entire output cochain; the component lemma exposes its value in `C`. Together with `.zero`, these determine every `.hom n m`, not just its induced map on cohomology. They also distinguish this telescoping choice from the alternative order.

The sign convention is Mathlib's: `δ (Cochain.ofHomotopy h)` is the difference of the endpoint cochains, and its cochain Leibniz rule places the sign on the differential of the first factor according to the degree of the second factor. The unit-valued sign acts through the canonical integer-linearity of every preadditive category; `Units.smul_def` expands this action. Components of `Cochain.ofHomotopy` reduce using `Cochain.mk_v`.

## Zero normalization and the two direct contractions

Separate additivity of `prePostcomp` gives the following zero identities:

```lean
lemma prePostcomp_zero_left (β : L ⟶ L') :
    prePostcomp (0 : K' ⟶ K) β = 0

lemma prePostcomp_zero_right (α : K' ⟶ K) :
    prePostcomp α (0 : L ⟶ L') = 0
```

Supply either contraction as data, in the orientation identity-to-zero:

```lean
noncomputable def homotopyToZeroOfLeft
    (hK : Homotopy (𝟙 K) (0 : K ⟶ K)) :
    Homotopy (𝟙 (HomComplex K L)) 0

noncomputable def homotopyToZeroOfRight
    (hL : Homotopy (𝟙 L) (0 : L ⟶ L)) :
    Homotopy (𝟙 (HomComplex K L)) 0
```

These are direct specializations of `prePostcompHomotopy`: use `(hK, Homotopy.refl (𝟙 L))` on the left and `(Homotopy.refl (𝟙 K), hL)` on the right, normalizing endpoints with the existing `prePostcomp_id` and the zero lemmas. Neither specialization is merely an existence theorem or a deduction from acyclicity. Their component equations are explicit simp-normal forms, so using either returned contraction does not require unfolding its definition:

```lean
lemma homotopyToZeroOfLeft_hom_v
    (hK : Homotopy (𝟙 K) (0 : K ⟶ K))
    (n : ℤ) (φ : Cochain K L n)
    (p q : ℤ) (hpq : p + (n - 1) = q) :
    ((homotopyToZeroOfLeft (L := L) hK).hom n (n - 1) φ).v p q hpq =
      n.negOnePow • (hK.hom p (p - 1) ≫ φ.v (p - 1) q (by omega))

lemma homotopyToZeroOfRight_hom_v
    (hL : Homotopy (𝟙 L) (0 : L ⟶ L))
    (n : ℤ) (φ : Cochain K L n)
    (p q : ℤ) (hpq : p + (n - 1) = q) :
    ((homotopyToZeroOfRight (K := K) hL).hom n (n - 1) φ).v p q hpq =
      φ.v p (q + 1) (by omega) ≫ hL.hom (q + 1) q
```

As with the joint construction, these equations and `.zero` determine the full homotopy data. The left contraction has the sign `(-1)^n`; the right contraction has no sign.

One downstream data use is an explicit primitive: if a degree-`n` cochain `φ` is closed and `H` is either returned contraction, then `ψ = H.hom n (n - 1) φ` satisfies `δ (n - 1) n ψ = φ`. This uses the homotopy equation and provides a particular boundary witness, not just vanishing of a class.

## Acyclicity in every degree

```lean
lemma acyclic_of_homotopy_id_zero_left
    (hK : Homotopy (𝟙 K) (0 : K ⟶ K)) :
    (HomComplex K L).Acyclic

lemma acyclic_of_homotopy_id_zero_right
    (hL : Homotopy (𝟙 L) (0 : L ⟶ L)) :
    (HomComplex K L).Acyclic
```

For each `n`, `Homotopy.homologyMap_eq` applied to the returned contraction identifies the identity and zero endomorphisms of `(HomComplex K L).homology n`. Use `homologyMap_id`, `homologyMap_zero` and `IsZero.iff_id_eq_zero`, then `HomologicalComplex.exactAt_iff_isZero_homology` and the definition of `Acyclic`. Homology exists here because the output category is `AddCommGrpCat`; the input category needs no homology assumptions. This is an all-degree consequence of the supplied data, with no detour through degree-zero cohomology or the homotopy category.

## A single nonzero model for both variables

Work only for this example in `ModuleCat.{0} ℤ`. Put

- `P = (CochainComplex.singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ ℤ)`;
- `K = CochainComplex.mappingCone (𝟙 P)` and **`L = K`**;
- `h = CochainComplex.mappingCone.homotopyToZeroOfId P`, of type `Homotopy (𝟙 K) 0`.

The module category supplies the zero object and binary biproducts needed by the single-complex and mapping-cone constructions. These assumptions are example-only and do not enter any generic signature above. Apply both `homotopyToZeroOfLeft h` and `homotopyToZeroOfRight h` to the same `HomComplex K K`.

This example is genuinely nonzero. `mappingCone.isZero_X_iff` at degree `0` would force `P.X 0` to be zero if `K.X 0` were zero. `HomologicalComplex.singleObjXSelf` identifies `P.X 0` with `ModuleCat.of ℤ ℤ`; `ModuleCat.isZero_of_iff_subsingleton` reduces its being zero to `Subsingleton ℤ`, contradicted by `0 ≠ 1`. Hence `K.X 0` is not zero, its identity is not zero, and neither is `𝟙 K`.

In particular the degree-zero cochain `φ = Cochain.ofHom (𝟙 K)` is **nonzero**, by its degree-zero component (or `Cochain.ofHom_injective` and `Cochain.ofHom_zero`). Nevertheless it is a **boundary**:

\[
 \delta_{-1,0}(\operatorname{Cochain.ofHomotopy}(h))
   =\operatorname{Cochain.ofHom}(\mathrm{id}_K)=\varphi.
\]

Consequently `CohomologyClass.mk (Cocycle.ofHom (𝟙 K)) = 0`, using the boundary/class-zero API. Nonzero here refers to a cochain and a term of the complex, **not** to its degree-zero cohomology class. Both contractions still give acyclicity in every integer degree.

For the zero boundary case in `ModuleCat ℤ`, take `K = L = 0`. The identity of the zero complex is zero, so the zero homotopy supplies either input contraction. Both component equations then reduce to zero. This normalization check does not replace the same-cone nonzero model.
