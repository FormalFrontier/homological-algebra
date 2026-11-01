/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Abelian.Fitting

/-!
# Naturality of the Fitting decomposition

For an intertwiner between endomorphisms of Noetherian and Artinian objects,
the canonical kernel/image copairings of sufficiently high powers are
isomorphisms on one common tail. In these coordinates the intertwiner is the
binary biproduct map of its induced kernel and image maps. Thus its two
off-diagonal coordinates vanish.

The source and target each carry both chain conditions. No splitting or
stabilization exponent is supplied as an assumption. The copairings are the
existing kernel-first, image-second copairings, and the maps on their summands
are Mathlib's `kernel.map` and `image.map`. Object and morphism universes are
independent.

## References

* `HomologicalAlgebra.Abelian.Fitting`, for the canonical kernel/image
  copairing isomorphisms and invertible image restrictions on a stable tail.
* `HomologicalAlgebra.Abelian.EndomorphismPowers`, for the induced power maps
  and the all-exponent copairing naturality law.
* Mathlib's kernel, image and binary-biproduct universal-property APIs in
  `Mathlib.CategoryTheory.Limits.Shapes.Kernels`,
  `Mathlib.CategoryTheory.Limits.Shapes.Images` and
  `Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts`.
-/

@[expose] public section

universe v u

namespace CategoryTheory.End

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- For an intertwiner between endomorphisms of Noetherian and Artinian objects,
the canonical power-kernel/image copairings give isomorphisms on one common tail,
with invertible image restrictions. In these coordinates the intertwiner is the
binary biproduct map of the induced kernel and image maps. -/
theorem eventually_exists_pow_biprod_desc_iso_naturality {X Y : C}
    [IsNoetherianObject X] [IsArtinianObject X]
    [IsNoetherianObject Y] [IsArtinianObject Y]
    (f : End X) (g : End Y) (p : X ⟶ Y) (h : f ≫ p = p ≫ g) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ (eX : kernel (f ^ n) ⊞ image (f ^ n) ≅ X)
        (eY : kernel (g ^ n) ⊞ image (g ^ n) ≅ Y),
        eX.hom = biprod.desc (kernel.ι (f ^ n)) (image.ι (f ^ n)) ∧
        eY.hom = biprod.desc (kernel.ι (g ^ n)) (image.ι (g ^ n)) ∧
        IsIso (imagePowRestriction f n) ∧ IsIso (imagePowRestriction g n) ∧
        eX.hom ≫ p ≫ eY.inv =
          biprod.map
            (W := kernel (f ^ n)) (X := image (f ^ n))
            (Y := kernel (g ^ n)) (Z := image (g ^ n))
            (kernel.map (f ^ n) (g ^ n) p p (pow_comp_eq_comp_pow f g p h n))
            (image.map (Arrow.homMk' (f := f ^ n) (g := g ^ n) p p
              (pow_comp_eq_comp_pow f g p h n).symm)) := by
  filter_upwards [eventually_isIso_biprod_desc_kernel_ι_image_ι_pow f,
    eventually_isIso_biprod_desc_kernel_ι_image_ι_pow g,
    eventually_isIso_imagePowRestriction f,
    eventually_isIso_imagePowRestriction g] with n hX hY hf hg
  let : IsIso (biprod.desc (kernel.ι (f ^ n)) (image.ι (f ^ n))) := hX
  let : IsIso (biprod.desc (kernel.ι (g ^ n)) (image.ι (g ^ n))) := hY
  refine ⟨asIso (biprod.desc (kernel.ι (f ^ n)) (image.ι (f ^ n))),
    asIso (biprod.desc (kernel.ι (g ^ n)) (image.ι (g ^ n))),
    rfl, rfl, hf, hg, ?_⟩
  rw [asIso_hom, asIso_inv]
  simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using
    congrArg (fun q ↦ q ≫ inv (biprod.desc (kernel.ι (g ^ n)) (image.ι (g ^ n))))
      (pow_biprod_desc_naturality f g p h n).symm

end CategoryTheory.End
