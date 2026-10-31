/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Images
public import Mathlib.Algebra.Category.ModuleCat.Subobject

/-!
# Kernel and image subobjects of modules

The order isomorphism `ModuleCat.subobjectModule` identifies categorical kernel and image
subobjects with the kernel and range of a linear map. The endomorphism ring isomorphism
identifies powers, so complementarity of categorical power kernels and images agrees with
complementarity of the corresponding linear-map kernels and ranges.

The kernel and image identifications use the comparison isomorphisms and their compatibility
with the inclusion arrows, so they do not depend on choices of representatives of subobjects.
-/

@[expose] public section

universe u v

open CategoryTheory Limits

namespace ModuleCat

variable {R : Type u} [Ring R]

variable {M N : ModuleCat.{v} R}

/-- The kernel subobject of a module morphism corresponds to the kernel of its linear map. -/
@[simp]
lemma subobjectModule_kernelSubobject (f : M ⟶ N) :
    subobjectModule M (kernelSubobject f) = LinearMap.ker f.hom := by
  apply (subobjectModule M).symm.injective
  rw [OrderIso.symm_apply_apply]
  change kernelSubobject f = Subobject.mk (ofHom (LinearMap.ker f.hom).subtype)
  refine Subobject.eq_mk_of_comm _ (kernelSubobjectIso f ≪≫ kernelIsoKer f) ?_
  simp only [Iso.trans_hom, Category.assoc, kernelIsoKer_hom_ker_subtype,
    kernelSubobject_arrow]

/-- The image subobject of a module morphism corresponds to the range of its linear map. -/
@[simp]
lemma subobjectModule_imageSubobject (f : M ⟶ N) :
    subobjectModule N (imageSubobject f) = LinearMap.range f.hom := by
  apply (subobjectModule N).symm.injective
  rw [OrderIso.symm_apply_apply]
  change imageSubobject f = Subobject.mk (ofHom (LinearMap.range f.hom).subtype)
  refine Subobject.eq_mk_of_comm _ (imageSubobjectIso f ≪≫ imageIsoRange f) ?_
  simp only [Iso.trans_hom, Category.assoc, imageIsoRange_hom_subtype,
    imageSubobject_arrow]

/-- Complementarity of categorical power kernels and images agrees with
complementarity of the kernels and ranges of powers of the linear endomorphism. -/
@[simp]
lemma isCompl_kernelSubobject_pow_imageSubobject_pow_iff (f : End M) (n : ℕ) :
    IsCompl (kernelSubobject (f ^ n)) (imageSubobject (f ^ n)) ↔
      IsCompl (LinearMap.ker (f.hom ^ n)) (LinearMap.range (f.hom ^ n)) := by
  have hpow : (f ^ n).hom = f.hom ^ n := (endRingEquiv M).map_pow f n
  simpa only [subobjectModule_kernelSubobject, subobjectModule_imageSubobject, hpow] using
    ((subobjectModule M).isCompl_iff
      (x := kernelSubobject (f ^ n)) (y := imageSubobject (f ^ n)))

end ModuleCat
