# Credits

Formal Frontier Agents developed this library with AI assistance. Its
[references](README.md#references) identify the mathematical sources and the
prior Mathlib formalization on which it builds.

## Project contributions

Prism wrote the original Euler, exact-functor, LES, relative-path and
quotient-intersection mathematical expositions, distinct from the original
Lean proofs.

The core and LES contributor wrote the original core, finite-length and
exact-functor Euler proofs and clients, and later the cochain LES formula and
its genuinely nonsplit clients. The distinct cochain-shift and path contributor
wrote the original native cochain shift, finite-support and finite-interval
cochain Euler proofs and clients. These contributors independently reviewed
one another's respective components.

The cochain-shift and path contributor also wrote the original native
fixed-arrow relative-path and chosen-cokernel quotient-intersection proofs and
ordinary clients. The core and LES contributor independently reviewed their
mathematics and code.

The core and LES contributor wrote the original quadrant product-total
mathematical assembly, Lean proof, ordinary client and aggregate registration.
The cochain-shift and path contributor independently reviewed its mathematics
and code. Prism was not the original product-total proof author.

The core and LES contributor wrote the original admissible-layer Lean
construction and lower-cut interfaces. Prism repaired the proof, exposed its
exported equations and wrote its ordinary-import client.

Folio wrote the README headline-result groups on ordinary projectivity and
injectivity of identity disks; Hom-complex homotopy invariance and contraction
in either variable; K-injectivity via product Hom complexes; K-properties of
homotopy retracts; and K-projectivity of arbitrary coproducts.

Gnomon wrote the README headline-result group on diagonal homotopies and
coproducts or products. These are documentation credits, not credits for the
corresponding theorems or proofs.

## Mathlib and licensing

This library reuses Mathlib's homological algebra, including its native short
exact sequences, homology, shifts, path objects and snake lemma. Upstream
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

The original project code is licensed under this repository's
[Apache-2.0 license](LICENSE) and credited collectively to Formal Frontier
Agents. No external source asset is redistributed.
