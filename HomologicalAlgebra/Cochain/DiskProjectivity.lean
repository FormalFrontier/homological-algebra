/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import HomologicalAlgebra.Cochain.DiskAdjunctions
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Ordinary projectivity and injectivity of cochain disks

An identity disk is projective, respectively injective, precisely when its
coefficient object is. These are the ordinary categorical properties, not
K-projectivity or K-injectivity. Only zero morphisms and a zero object are needed.

The proofs use the canonical disk adjunctions and Mathlib's general
`CategoryTheory.Adjunction.map_projective` and
`CategoryTheory.Adjunction.map_injective` transport. Evaluation has both adjoints
in every integer degree, so the required preservation of epimorphisms and
monomorphisms is derived rather than assumed. Recovering the coefficient uses
upper evaluation for projectivity and lower evaluation for injectivity.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]
  [HasZeroMorphisms C] [HasZeroObject C]

namespace CochainComplex

/-- An identity disk is ordinarily projective if and only if its coefficient is. -/
lemma projective_disk_iff (n : ℤ) (X : C) :
    Projective (disk n X) ↔ Projective X := by
  constructor
  · intro h
    -- This adjoint orientation gives epi preservation of the disk functor.
    let : (diskFunctor (C := C) n).IsLeftAdjoint := (diskAdjunction n).isLeftAdjoint
    have hp : Projective ((disk n X).X (n + 1)) :=
      (evalDiskAdjunction n).map_projective (disk n X) h
    exact Projective.of_iso (eqToIso (disk_X_succ n X)) hp
  · exact (diskAdjunction n).map_projective X

/-- An identity disk is ordinarily injective if and only if its coefficient is. -/
lemma injective_disk_iff (n : ℤ) (X : C) :
    Injective (disk n X) ↔ Injective X := by
  constructor
  · intro h
    -- This adjoint orientation gives mono preservation of the disk functor.
    let : (diskFunctor (C := C) n).IsRightAdjoint := (evalDiskAdjunction n).isRightAdjoint
    have hi : Injective ((disk n X).X n) :=
      (diskAdjunction n).map_injective (disk n X) h
    exact Injective.of_iso (eqToIso (disk_X_self n X)) hi
  · exact (evalDiskAdjunction n).map_injective X

/-- The disk on a projective coefficient is ordinarily projective. -/
instance projective_disk (n : ℤ) (X : C) [Projective X] : Projective (disk n X) :=
  (projective_disk_iff n X).2 inferInstance

/-- The disk on an injective coefficient is ordinarily injective. -/
instance injective_disk (n : ℤ) (X : C) [Injective X] : Injective (disk n X) :=
  (injective_disk_iff n X).2 inferInstance

end CochainComplex
