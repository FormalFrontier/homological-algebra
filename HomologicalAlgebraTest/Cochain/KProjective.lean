/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import HomologicalAlgebra.Cochain.HomComplexQuasiIso
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# The integer stalk and quasi-isomorphism invariance

The standard complex ℤ[0] is nonzero and satisfies the criterion for every
acyclic integer cochain complex of ℤ-modules. Its K-projectivity is obtained
from the stock bounded-above-projective criterion, not assumed. It also gives
quasi-isomorphism invariance under postcomposition by arbitrary quasi-isomorphisms.

Mathematically, H⁰ Hom(ℤ[0], ℤ[0]) = ℤ, so the Hom complex need not be
acyclic. Reduction in degree zero maps the two-term complex ℤ --2→ ℤ in
degrees -1 and 0 quasi-isomorphically to (ℤ/2)[0], but this map is not a
homotopy equivalence: every map ℤ/2 → ℤ is zero. The examples below quantify
over arbitrary quasi-isomorphisms rather than constructing that two-term complex.
-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex

namespace CochainComplex

example : ¬ IsZero
    ((single (ModuleCat ℤ) (.up ℤ) (0 : ℤ)).obj (ModuleCat.of ℤ ℤ)) := by
  intro h
  have hz : IsZero
      (((single (ModuleCat ℤ) (.up ℤ) (0 : ℤ)).obj (ModuleCat.of ℤ ℤ)).X 0) :=
    (eval (ModuleCat ℤ) (.up ℤ) (0 : ℤ)).map_isZero h
  rw [single_obj_X_self] at hz
  have := ModuleCat.subsingleton_of_isZero hz
  exact zero_ne_one (Subsingleton.elim (0 : ℤ) 1)

private lemma integerStalk_isKProjective :
    CochainComplex.IsKProjective
      ((single (ModuleCat ℤ) (.up ℤ) (0 : ℤ)).obj (ModuleCat.of ℤ ℤ)) := by
  let K : CochainComplex (ModuleCat ℤ) ℤ :=
    (single (ModuleCat ℤ) (.up ℤ) (0 : ℤ)).obj (ModuleCat.of ℤ ℤ)
  let : ∀ i : ℤ, Projective (K.X i) := fun i ↦ by
    by_cases hi : i = 0
    · subst i
      simpa only [K, single_obj_X_self] using
        (inferInstance : Projective (ModuleCat.of ℤ ℤ))
    · exact (isZero_single_obj_X (.up ℤ) (0 : ℤ) (ModuleCat.of ℤ ℤ) i hi).projective
  exact isKProjective_of_projective K 0

example (L : CochainComplex (ModuleCat ℤ) ℤ) (hL : L.Acyclic) :
    (HomComplex ((single (ModuleCat ℤ) (.up ℤ) (0 : ℤ)).obj (ModuleCat.of ℤ ℤ)) L).Acyclic := by
  let K : CochainComplex (ModuleCat ℤ) ℤ :=
    (single (ModuleCat ℤ) (.up ℤ) (0 : ℤ)).obj (ModuleCat.of ℤ ℤ)
  have : K.IsKProjective := integerStalk_isKProjective
  exact (isKProjective_iff_acyclic_homComplex K).mp inferInstance L hL

example {X Y : CochainComplex (ModuleCat ℤ) ℤ} (q : X ⟶ Y) [QuasiIso q] :
    QuasiIso (HomComplex.prePostcomp
      (𝟙 ((single (ModuleCat ℤ) (.up ℤ) (0 : ℤ)).obj (ModuleCat.of ℤ ℤ))) q) := by
  let K : CochainComplex (ModuleCat ℤ) ℤ :=
    (single (ModuleCat ℤ) (.up ℤ) (0 : ℤ)).obj (ModuleCat.of ℤ ℤ)
  have : K.IsKProjective := integerStalk_isKProjective
  exact IsKProjective.quasiIso_prePostcomp K q

end CochainComplex
