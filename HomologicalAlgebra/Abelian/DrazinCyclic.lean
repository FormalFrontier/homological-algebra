/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Abelian.Drazin
public import Mathlib.CategoryTheory.Limits.Shapes.Images

/-!
# Drazin inverses of cyclic products

For morphisms `a : X ⟶ Y` and `b : Y ⟶ X` between Noetherian and Artinian
objects of an abelian category, the Drazin inverse of `a ≫ b` is
`a ≫ drazinInverse (b ≫ a) ^ 2 ≫ b`. The associated Drazin projectors have
canonically isomorphic categorical images. The forward map is induced by `a`,
and its inverse is induced by `b ≫ drazinInverse (a ≫ b)`.

The inverse identity is the rectangular categorical finite-length form of
Cline's formula. The reference below treats the generalized-Drazin ring version.
The derivation here uses compatibility with intertwiners and the outer-inverse
identity of the Drazin inverse.

The comparison intertwines the endomorphisms induced on these images by the
two cyclic products. All images and induced maps are those of
`CategoryTheory.Limits`. Multiplication in the canonical endomorphism ring
satisfies `f * g = g ≫ f`.

## References

* Huanyin Chen and Marjan Sheibani Abdolyousefi, *Cline's formula for g-Drazin
  inverses in a ring*, Filomat **33**(8) (2019), 2249–2255,
  [doi:10.2298/FIL1908249C](https://doi.org/10.2298/FIL1908249C).
* `HomologicalAlgebra.Abelian.Drazin` provides the canonical Drazin inverse,
  its characteristic equations and its compatibility with intertwiners.
* `Mathlib.CategoryTheory.Limits.Shapes.Images` provides categorical images
  and the maps induced by commutative squares.
-/

@[expose] public section

universe v u

open CategoryTheory.Limits

namespace CategoryTheory.End

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X : C} [IsNoetherianObject X] [IsArtinianObject X]

variable {Y : C} [IsNoetherianObject Y] [IsArtinianObject Y]

/-- Cline's cyclic-product formula for Drazin inverses, in rectangular categorical
finite-length form. The inverse of a product uses the square of the inverse of
its reversed product. For the generalized-Drazin ring version, see Chen and
Abdolyousefi, *Cline's formula for g-Drazin inverses in a ring*. -/
theorem drazinInverse_comp (a : X ⟶ Y) (b : Y ⟶ X) :
    drazinInverse (a ≫ b) = a ≫ (drazinInverse (b ≫ a) ^ 2) ≫ b := by
  have ha := CategoryTheory.End.drazinInverse_comp_eq_comp_drazinInverse
    (a ≫ b) (b ≫ a) a (Category.assoc a b a)
  have hb := CategoryTheory.End.drazinInverse_comp_eq_comp_drazinInverse
    (b ≫ a) (a ≫ b) b (Category.assoc b a b)
  calc
    drazinInverse (a ≫ b) =
        (drazinInverse (a ≫ b) ≫ a) ≫ (b ≫ drazinInverse (a ≫ b)) := by
      simpa only [CategoryTheory.End.mul_def, Category.assoc] using
        (CategoryTheory.End.drazinInverse_mul_self_mul (a ≫ b)).symm
    _ = (a ≫ drazinInverse (b ≫ a)) ≫ (drazinInverse (b ≫ a) ≫ b) := by
      rw [ha, ← hb]
    _ = a ≫ (drazinInverse (b ≫ a) ^ 2) ≫ b := by
      simp only [pow_two, CategoryTheory.End.mul_def, Category.assoc]

/-- The Drazin projector of a cyclic product factors through the Drazin inverse
of the reversed product. -/
theorem mul_drazinInverse_comp (a : X ⟶ Y) (b : Y ⟶ X) :
    drazinInverse (a ≫ b) ≫ (a ≫ b) = a ≫ drazinInverse (b ≫ a) ≫ b := by
  simpa only [Category.assoc] using
    congrArg (fun k : X ⟶ Y => k ≫ b)
      (CategoryTheory.End.drazinInverse_comp_eq_comp_drazinInverse
        (a ≫ b) (b ≫ a) a (Category.assoc a b a))

/-- The canonical images of the Drazin projectors of two cyclic products are
isomorphic, with forward map induced by `a` and inverse induced by
`b ≫ drazinInverse (a ≫ b)`. -/
noncomputable def imageMulDrazinInverseCompIso (a : X ⟶ Y) (b : Y ⟶ X) :
    Limits.image (drazinInverse (a ≫ b) ≫ (a ≫ b)) ≅
      Limits.image (drazinInverse (b ≫ a) ≫ (b ≫ a)) := by
  have habs {Z : C} (p : Z ⟶ Z) [HasImage p] [Epi (factorThruImage p)]
      (hp : p ≫ p = p) : image.ι p ≫ p = image.ι p := by
    apply (cancel_epi (factorThruImage p)).1
    simpa only [← Category.assoc, image.fac] using hp
  have hda : drazinInverse (a ≫ b) ≫ a = a ≫ drazinInverse (b ≫ a) :=
    drazinInverse_comp_eq_comp_drazinInverse (a ≫ b) (b ≫ a) a
      (Category.assoc a b a)
  have hX : a ≫ (b ≫ drazinInverse (a ≫ b)) =
      drazinInverse (a ≫ b) ≫ (a ≫ b) := by
    simpa only [mul_def, Category.assoc] using
      (commute_drazinInverse (a ≫ b)).eq.symm
  have hY : (b ≫ drazinInverse (a ≫ b)) ≫ a =
      drazinInverse (b ≫ a) ≫ (b ≫ a) := by
    calc
      (b ≫ drazinInverse (a ≫ b)) ≫ a =
          b ≫ (drazinInverse (a ≫ b) ≫ a) := Category.assoc _ _ _
      _ = b ≫ (a ≫ drazinInverse (b ≫ a)) := by rw [hda]
      _ = (b ≫ a) ≫ drazinInverse (b ≫ a) := (Category.assoc _ _ _).symm
      _ = drazinInverse (b ≫ a) ≫ (b ≫ a) := by
        simpa only [mul_def] using (commute_drazinInverse (b ≫ a)).eq.symm
  have hforward : a ≫ (drazinInverse (b ≫ a) ≫ (b ≫ a)) =
      (drazinInverse (a ≫ b) ≫ (a ≫ b)) ≫ a := by
    rw [← hY, ← hX]
    simp only [Category.assoc]
  have hinverse : (b ≫ drazinInverse (a ≫ b)) ≫
        (drazinInverse (a ≫ b) ≫ (a ≫ b)) =
      (drazinInverse (b ≫ a) ≫ (b ≫ a)) ≫
        (b ≫ drazinInverse (a ≫ b)) := by
    rw [← hX, ← hY]
    simp only [Category.assoc]
  have hp : (drazinInverse (a ≫ b) ≫ (a ≫ b)) ≫
        (drazinInverse (a ≫ b) ≫ (a ≫ b)) =
      drazinInverse (a ≫ b) ≫ (a ≫ b) := by
    simpa only [IsIdempotentElem, mul_def] using
      isIdempotentElem_mul_drazinInverse (a ≫ b)
  have hq : (drazinInverse (b ≫ a) ≫ (b ≫ a)) ≫
        (drazinInverse (b ≫ a) ≫ (b ≫ a)) =
      drazinInverse (b ≫ a) ≫ (b ≫ a) := by
    simpa only [IsIdempotentElem, mul_def] using
      isIdempotentElem_mul_drazinInverse (b ≫ a)
  refine
    { hom := image.map (Arrow.homMk' a a hforward)
      inv := image.map (Arrow.homMk' (b ≫ drazinInverse (a ≫ b))
        (b ≫ drazinInverse (a ≫ b)) hinverse)
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply (cancel_mono (image.ι (drazinInverse (a ≫ b) ≫ (a ≫ b)))).1
    rw [Category.assoc, image.map_homMk'_ι,
      ← Category.assoc _ (image.ι (drazinInverse (b ≫ a) ≫ (b ≫ a)))
        (b ≫ drazinInverse (a ≫ b)),
      image.map_homMk'_ι, Category.assoc, hX, Category.id_comp]
    exact habs _ hp
  · apply (cancel_mono (image.ι (drazinInverse (b ≫ a) ≫ (b ≫ a)))).1
    rw [Category.assoc, image.map_homMk'_ι,
      ← Category.assoc _ (image.ι (drazinInverse (a ≫ b) ≫ (a ≫ b))) a,
      image.map_homMk'_ι, Category.assoc, hY, Category.id_comp]
    exact habs _ hq

/-- The forward comparison agrees with `a` after the image inclusion. -/
theorem imageMulDrazinInverseCompIso_hom_ι (a : X ⟶ Y) (b : Y ⟶ X) :
    (imageMulDrazinInverseCompIso a b).hom ≫
        image.ι (drazinInverse (b ≫ a) ≫ (b ≫ a)) =
      image.ι (drazinInverse (a ≫ b) ≫ (a ≫ b)) ≫ a := by
  exact image.map_homMk'_ι _

/-- The inverse comparison agrees with `b ≫ drazinInverse (a ≫ b)` after the
image inclusion. -/
theorem imageMulDrazinInverseCompIso_inv_ι (a : X ⟶ Y) (b : Y ⟶ X) :
    (imageMulDrazinInverseCompIso a b).inv ≫
        image.ι (drazinInverse (a ≫ b) ≫ (a ≫ b)) =
      image.ι (drazinInverse (b ≫ a) ≫ (b ≫ a)) ≫ b ≫
        drazinInverse (a ≫ b) := by
  exact image.map_homMk'_ι _

/-- The forward comparison is the categorical image map induced by the square
with both sides equal to `a`. -/
theorem imageMulDrazinInverseCompIso_hom_eq_image_map (a : X ⟶ Y) (b : Y ⟶ X) :
    (imageMulDrazinInverseCompIso a b).hom =
      image.map (Arrow.homMk' a a
        (by
          have ha := drazinInverse_comp_eq_comp_drazinInverse
            (a ≫ b) (b ≫ a) a (Category.assoc a b a)
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ b ≫ a) ha.symm
        : a ≫ (drazinInverse (b ≫ a) ≫ (b ≫ a)) =
          (drazinInverse (a ≫ b) ≫ (a ≫ b)) ≫ a)) := by
  apply (cancel_mono (image.ι (drazinInverse (b ≫ a) ≫ (b ≫ a)))).1
  rw [imageMulDrazinInverseCompIso_hom_ι, image.map_homMk'_ι]

/-- The inverse comparison is the categorical image map induced by the square
with both sides equal to `b ≫ drazinInverse (a ≫ b)`. -/
theorem imageMulDrazinInverseCompIso_inv_eq_image_map (a : X ⟶ Y) (b : Y ⟶ X) :
    (imageMulDrazinInverseCompIso a b).inv =
      image.map (Arrow.homMk' (b ≫ drazinInverse (a ≫ b))
        (b ≫ drazinInverse (a ≫ b))
        (by
          have hb := drazinInverse_comp_eq_comp_drazinInverse
            (b ≫ a) (a ≫ b) b (Category.assoc b a b)
          have hf : drazinInverse (a ≫ b) ≫ (a ≫ b) =
              (a ≫ b) ≫ drazinInverse (a ≫ b) :=
            (commute_drazinInverse (a ≫ b)).eq
          rw [hf]
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ a ≫ b ≫ drazinInverse (a ≫ b)) hb.symm
        : (b ≫ drazinInverse (a ≫ b)) ≫
            (drazinInverse (a ≫ b) ≫ (a ≫ b)) =
          (drazinInverse (b ≫ a) ≫ (b ≫ a)) ≫
            (b ≫ drazinInverse (a ≫ b)))) := by
  apply (cancel_mono (image.ι (drazinInverse (a ≫ b) ≫ (a ≫ b)))).1
  rw [imageMulDrazinInverseCompIso_inv_ι, image.map_homMk'_ι]

/-- The comparison intertwines the endomorphisms induced by the original
cyclic products on the images of their Drazin projectors. -/
theorem imageMulDrazinInverseCompIso_hom_naturality (a : X ⟶ Y) (b : Y ⟶ X) :
    image.map (Arrow.homMk' (a ≫ b) (a ≫ b)
        (by
          have hf : drazinInverse (a ≫ b) ≫ (a ≫ b) =
              (a ≫ b) ≫ drazinInverse (a ≫ b) :=
            (commute_drazinInverse (a ≫ b)).eq
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ (a ≫ b)) hf.symm
        : (a ≫ b) ≫ (drazinInverse (a ≫ b) ≫ (a ≫ b)) =
          (drazinInverse (a ≫ b) ≫ (a ≫ b)) ≫ (a ≫ b))) ≫
        (imageMulDrazinInverseCompIso a b).hom =
      (imageMulDrazinInverseCompIso a b).hom ≫
        image.map (Arrow.homMk' (b ≫ a) (b ≫ a)
          (by
            have hg : drazinInverse (b ≫ a) ≫ (b ≫ a) =
                (b ≫ a) ≫ drazinInverse (b ≫ a) :=
              (commute_drazinInverse (b ≫ a)).eq
            simpa only [Category.assoc] using
              congrArg (fun k => k ≫ (b ≫ a)) hg.symm
          : (b ≫ a) ≫ (drazinInverse (b ≫ a) ≫ (b ≫ a)) =
            (drazinInverse (b ≫ a) ≫ (b ≫ a)) ≫ (b ≫ a))) := by
  apply (cancel_mono (image.ι (drazinInverse (b ≫ a) ≫ (b ≫ a)))).1
  simp only [Category.assoc]
  rw [imageMulDrazinInverseCompIso_hom_ι]
  rw [← Category.assoc _ (image.ι (drazinInverse (a ≫ b) ≫ (a ≫ b))) a]
  simp only [image.map_homMk'_ι]
  rw [← Category.assoc _ (image.ι (drazinInverse (b ≫ a) ≫ (b ≫ a))) (b ≫ a),
    imageMulDrazinInverseCompIso_hom_ι]
  simp only [Category.assoc]

end CategoryTheory.End
