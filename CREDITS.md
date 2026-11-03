# Credits

Formal Frontier Agents developed this library with AI assistance. Its
[references](README.md#references) identify the mathematical sources and the
prior formalizations on which it builds.

## Project contributions

The original project contributions are credited collectively to Formal Frontier
Agents. Mathematical exposition, original Lean proofs and clients, later library
adaptation, and README documentation are distinct contributions.

The original Euler, exact-functor, LES, relative-path and quotient-intersection
mathematical expositions were written separately from the original Lean proofs.
The core and LES proof contribution comprised the original core, finite-length
and exact-functor Euler proofs and clients, followed by the cochain LES formula
and its genuinely nonsplit clients. A distinct cochain-shift and path proof
contribution comprised the original native cochain shift, finite-support and
finite-interval cochain Euler proofs and clients, and the original fixed-arrow
relative-path and chosen-cokernel quotient-intersection proofs and ordinary
clients.

The original quadrant product-total mathematical assembly, Lean proof and
ordinary client belonged to the core and LES proof contribution, not to the
separate exposition contribution. Later library adaptations of the relative-path,
quotient-intersection and product-total components did not create their original
proofs.

The original admissible-layer Lean construction and lower-cut interfaces were
part of the core and LES contribution. The exposition contribution also included
a later proof repair, the exported equations and the ordinary-import client;
subsequent interface adaptation was separate from those proof contributions.

The README headline groups on ordinary disk projectivity and injectivity,
Hom-complex homotopy invariance and contraction, K-injectivity, homotopy
retracts, arbitrary coproduct K-projectivity, and diagonal homotopies of
coproducts or products were documentation contributions, not authorship of the
corresponding theorems or proofs.

## Prior formalizations and licensing

This library reuses Mathlib's homological algebra, including its native short
exact sequences, homology, shifts, path objects and snake lemma. Nilpotence
across short complexes uses Mathlib's short-complex exactness and monic/epic
cancellation APIs, together with this library's endomorphism-power intertwining
interface; the outer-to-middle exponent bound and short-exact nilpotence
criterion are proved here. Upstream
mathlib retains its own authorship and Apache-2.0 license: `Single` credits
Kim Morrison (2021); `SingleHomology` and `HomotopyFiber` credit Joël Riou
(2023); `ShiftSequence` credits Joël Riou (2024); opposite-complex work credits
Johan Commelin, Amelia Livingston and Joël Riou (2022).
The bounded-below integer-chain criterion follows the extension proof of
Mathlib's `ChainComplex.quasiIso_iff_of_projective` and its K-projective cochain
criterion (`DerivedCategory/KProjective` and `HomotopyCategory/KProjective`,
Joël Riou, 2025), using the complex-extension API (`Embedding/Extend`,
Joël Riou, 2024).

The Hom-complex component operations and homology-to-homotopy-category
comparisons use Joël Riou's `HomComplex` and `HomComplexShift` modules in
Mathlib (2023), and his `HomComplexCohomology` module (2025). The integer-stalk
examples also use his `HomComplexSingle` constructions (2023).

The diagonal homotopy criteria follow the library's homotopy assembly and
restriction approach, using Mathlib's homotopy composition and categorical
coproduct and product universal properties. Their Lean proofs are original
project contributions, not copies of dependency implementations.

Indecomposability from a local endomorphism ring uses Mathlib's binary-biproduct
API (Kim Morrison and Jakob von Raumer, 2019), preadditive biproducts
(Kim Morrison, 2020), preadditive categories (Markus Himmel and Jakob von Raumer,
2020), the local-ring unit criterion
(Kenny Lau, Chris Hughes and Mario Carneiro, 2018), and the unit-idempotent
lemma (Christopher Hoskin, 2022). The categorical endomorphism convention is
from Yury Kudryashov, Kim Morrison and Simon Hudon (2019). The project proof
combines these interfaces without copying a dependency implementation.

The Drazin inverse terminology follows M. P. Drazin,
[Pseudo-Inverses in Associative Rings and Semigroups](https://doi.org/10.1080/00029890.1958.11991949)
(1958). The construction reuses the canonical Fitting decomposition and power
restrictions developed in this library by Formal Frontier Agents.
It uses Mathlib's endomorphism and binary-biproduct APIs credited above and
Yury Kudryashov's `CategoryTheory.Iso.conj` transport.

The cyclic-product Drazin identity is Cline's formula. For its generalized-Drazin
ring version, see Huanyin Chen and Marjan Sheibani Abdolyousefi,
[*Cline's formula for g-Drazin inverses in a ring*](https://doi.org/10.2298/FIL1908249C).
The rectangular categorical finite-length derivation uses the library's
intertwiner and outer-inverse identities and Mathlib's categorical image API.
The triangular stable-image projector and its actual-image graph isomorphism
also reuse Mathlib's canonical image and strong-epimorphism/monomorphism
factorization API, together with the same Drazin and biproduct interfaces.
The preadditive Sylvester equation reuses Mathlib's unit-plus-commuting-nilpotent
criterion on additive endomorphisms of a hom group, with its preadditive
left- and right-composition APIs. Its application to the finite-length
triangular Drazin projector characterizes the graph by the Sylvester equation
and the normalized intertwining-section equations; it does not introduce a
second inverse construction.

Finite biproduct uniqueness follows the classical local-endomorphism-ring
Krull–Schmidt argument. It reuses Kim Morrison's categorical Gaussian
elimination (2020) and additive envelope (2021) formalizations in Mathlib, the
additive-functor API by Adam Topaz and Kim Morrison (2021), and the endomorphism,
local-ring and idempotent APIs credited above. The finite-family append
comparison is reused from this library. The index and fully faithful bridge
also uses the products API by Kim Morrison and Bhavik Mehta, biproduct
preservation by Markus Himmel, finite types by Kyle Miller, and ring
equivalences by Johannes Hölzl, Callum Sutton and Yury Kudryashov. The proof
assembles these APIs without copying an external book passage or a dependency
implementation.

The subobject correspondence, modularity and quotient-object Jordan–Hölder
constructions follow Mathlib formalizations by Jack McKoen, Markus Himmel,
Bhavik Mehta, Kim Morrison and Johan Commelin. The module references in
[`Subobject`](HomologicalAlgebra/Abelian/Subobject.lean) and
[`JordanHolder`](HomologicalAlgebra/Abelian/JordanHolder.lean) identify the
revisions and preserve their upstream notices. The order-theoretic finite-chain
and Jordan–Hölder interfaces are supplied by Mathlib. The mathematical
subobject-correspondence reference is N. Popescu, *Abelian Categories with
Applications to Rings and Modules* (1973), as cited by Mathlib.

The numerical object-length development uses Mathlib's order-theoretic height,
coheight and Jordan–Hölder interfaces, and its canonical subobject order.
The comparison over arbitrary rings uses Mathlib's `ModuleCat.subobjectModule`
and `Module.length_eq_height`. The categorical length and power bounds combine
these interfaces with this library's subobject correspondence and endomorphism
power chains; they are distinct from the integer-valued Euler length invariant.
The finite-module-length power-kernel bound specializes this categorical bound.
Its finite-dimensional comparison uses Mathlib's existing power-kernel
stabilization theorem through the canonical subobject and endomorphism
correspondences.

Finite-family cancellation reuses the
[stable-range library](https://github.com/FormalFrontier/stable-range)
through `StableRange.CategoryTheory.Cancellation`: cancellation of one summand
with a possibly noncommutative local endomorphism ring. The finite-family proof
uses Mathlib's biproduct transport APIs and Kim Morrison's additive envelope,
following this library's finite-biproduct uniqueness approach. Finite-length
summand cancellation combines this result with finite local-End decomposition.
The dependency is pinned
to `70231e01f5383c3882231f244612ded7283e77c8` in `lakefile.toml` and
`lake-manifest.json`.

The original project code is licensed under this repository's
[Apache-2.0 license](LICENSE) and credited collectively to Formal Frontier
Agents. No external source asset is redistributed.
