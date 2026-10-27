/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import HomologicalAlgebra

/-!
# Changing the detecting Hom-cohomology degree

Preservation in one fixed degree implies preservation in any other degree,
in both variables, through the K-object criteria exposed by the public entry point.
-/

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

example (K : CochainComplex C ℤ) (n m : ℤ)
    (h : ∀ {A B : CochainComplex C ℤ} (q : A ⟶ B), QuasiIso q →
      IsIso (HomologicalComplex.homologyMap
        (CochainComplex.HomComplex.prePostcomp (𝟙 K) q) n)) :
    ∀ {A B : CochainComplex C ℤ} (q : A ⟶ B), QuasiIso q →
      IsIso (HomologicalComplex.homologyMap
        (CochainComplex.HomComplex.prePostcomp (𝟙 K) q) m) :=
  (CochainComplex.isKProjective_iff_isIso_homologyMap_prePostcomp K m).mp
    ((CochainComplex.isKProjective_iff_isIso_homologyMap_prePostcomp K n).mpr h)

example (I : CochainComplex C ℤ) (n m : ℤ)
    (h : ∀ {A B : CochainComplex C ℤ} (q : A ⟶ B), QuasiIso q →
      IsIso (HomologicalComplex.homologyMap
        (CochainComplex.HomComplex.prePostcomp q (𝟙 I)) n)) :
    ∀ {A B : CochainComplex C ℤ} (q : A ⟶ B), QuasiIso q →
      IsIso (HomologicalComplex.homologyMap
        (CochainComplex.HomComplex.prePostcomp q (𝟙 I)) m) :=
  (CochainComplex.isKInjective_iff_isIso_homologyMap_prePostcomp I m).mp
    ((CochainComplex.isKInjective_iff_isIso_homologyMap_prePostcomp I n).mpr h)
