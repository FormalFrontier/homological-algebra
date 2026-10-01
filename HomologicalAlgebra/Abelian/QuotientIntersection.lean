/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Limits

public section

/-!
# Quotients by an intersection

The canonical map from a quotient by `L ⊓ D` into the product of the quotients
by `L` and `D` is monic. The inclusions and cokernels here are the chosen
representatives of subobjects, not abstractly identified quotient objects.
-/

universe v u

namespace CategoryTheory.Subobject

open Limits
noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {B : C} (L U D : Subobject B) (h : L ≤ U)

private abbrev intersectionInclusion : ((L ⊓ D : Subobject B) : C) ⟶ (U : C) :=
  ofLE (L ⊓ D) U ((inf_le_left L D).trans h)

private theorem intersectionInclusion_to_left :
    intersectionInclusion L U D h ≫ 𝟙 (U : C) =
      ofLE (L ⊓ D) L (inf_le_left L D) ≫ ofLE L U h := by
  simp [intersectionInclusion]

private theorem intersectionInclusion_to_right :
    intersectionInclusion L U D h ≫ U.arrow =
      ofLE (L ⊓ D) D (inf_le_right L D) ≫ D.arrow := by
  simp [intersectionInclusion]

/-- The canonical map `U/(L ⊓ D) ⟶ (U/L) × (B/D)` induced by the two chosen
cokernel squares. Only `L ≤ U` is required; in particular `L ≤ D` is not assumed. -/
noncomputable def quotientIntersectionPair :
    cokernel (ofLE (L ⊓ D) U ((inf_le_left L D).trans h)) ⟶
      cokernel (ofLE L U h) ⨯ cokernel D.arrow :=
  prod.lift
    (cokernel.map (ofLE (L ⊓ D) U ((inf_le_left L D).trans h)) (ofLE L U h)
      (ofLE (L ⊓ D) L (inf_le_left L D)) (𝟙 _)
      (intersectionInclusion_to_left L U D h))
    (cokernel.map (ofLE (L ⊓ D) U ((inf_le_left L D).trans h)) D.arrow
      (ofLE (L ⊓ D) D (inf_le_right L D)) U.arrow
      (intersectionInclusion_to_right L U D h))

@[simp]
theorem quotientIntersectionPair_fst :
    quotientIntersectionPair L U D h ≫ prod.fst =
      cokernel.map (ofLE (L ⊓ D) U ((inf_le_left L D).trans h)) (ofLE L U h)
        (ofLE (L ⊓ D) L (inf_le_left L D)) (𝟙 _)
        (by simp [ofLE_comp_ofLE]) := by
  simp [quotientIntersectionPair]

@[simp]
theorem quotientIntersectionPair_snd :
    quotientIntersectionPair L U D h ≫ prod.snd =
      cokernel.map (ofLE (L ⊓ D) U ((inf_le_left L D).trans h)) D.arrow
        (ofLE (L ⊓ D) D (inf_le_right L D)) U.arrow
        (by simp [ofLE_arrow]) := by
  simp [quotientIntersectionPair]

@[reassoc]
theorem quotientIntersectionPair_fac :
    cokernel.π (ofLE (L ⊓ D) U ((inf_le_left L D).trans h)) ≫
      quotientIntersectionPair L U D h =
      prod.lift (cokernel.π (ofLE L U h)) (U.arrow ≫ cokernel.π D.arrow) := by
  apply prod.hom_ext
  · simp [quotientIntersectionPair]
  · simp [quotientIntersectionPair]

private theorem intersectionInclusion_comp_pair :
    intersectionInclusion L U D h ≫
      prod.lift (cokernel.π (ofLE L U h)) (U.arrow ≫ cokernel.π D.arrow) = 0 := by
  apply prod.hom_ext
  · simp only [Category.assoc, prod.lift_fst, zero_comp]
    rw [← Category.comp_id (intersectionInclusion L U D h),
      intersectionInclusion_to_left L U D h, Category.assoc, cokernel.condition, comp_zero]
  · simp only [Category.assoc, prod.lift_snd, zero_comp]
    rw [← Category.assoc, intersectionInclusion_to_right L U D h,
      Category.assoc, cokernel.condition, comp_zero]

private noncomputable def intersectionInclusion_isKernel :
    IsLimit (KernelFork.ofι (intersectionInclusion L U D h)
      (intersectionInclusion_comp_pair L U D h) :
      KernelFork (prod.lift (cokernel.π (ofLE L U h))
        (U.arrow ≫ cokernel.π D.arrow))) := by
  let inclusion := intersectionInclusion L U D h
  let pair := prod.lift (cokernel.π (ofLE L U h)) (U.arrow ≫ cokernel.π D.arrow)
  apply KernelFork.IsLimit.ofι' inclusion
  intro Z morphism vanishing
  have left_zero : morphism ≫ cokernel.π (ofLE L U h) = 0 := by
    have projection := congrArg (· ≫ prod.fst) vanishing
    simpa [pair, Category.assoc] using projection
  have right_zero : (morphism ≫ U.arrow) ≫ cokernel.π D.arrow = 0 := by
    have projection := congrArg (· ≫ prod.snd) vanishing
    simpa [pair, Category.assoc] using projection
  let left := Abelian.monoLift (ofLE L U h) morphism left_zero
  let right := Abelian.monoLift D.arrow (morphism ≫ U.arrow) right_zero
  have agree : left ≫ L.arrow = right ≫ D.arrow := by
    rw [← ofLE_arrow h, ← Category.assoc]
    simp [left, right]
  let lift := (inf_isPullback L D).lift left right agree
  refine ⟨lift, ?_⟩
  apply (cancel_mono U.arrow).1
  calc
    (lift ≫ inclusion) ≫ U.arrow = lift ≫ (L ⊓ D).arrow := by
      simp [inclusion, intersectionInclusion]
    _ = (lift ≫ ofLE (L ⊓ D) L (inf_le_left L D)) ≫ L.arrow := by simp
    _ = left ≫ L.arrow := by simp [lift]
    _ = morphism ≫ U.arrow := by
      calc
        left ≫ L.arrow = (left ≫ ofLE L U h) ≫ U.arrow := by
          rw [Category.assoc, ofLE_arrow]
        _ = morphism ≫ U.arrow := by rw [show left ≫ ofLE L U h = morphism from
          Abelian.monoLift_comp (ofLE L U h) morphism left_zero]

/-- The specified map of chosen cokernels is a monomorphism. -/
instance mono_quotientIntersectionPair : Mono (quotientIntersectionPair L U D h) := by
  let inclusion := intersectionInclusion L U D h
  let pair := prod.lift (cokernel.π (ofLE L U h)) (U.arrow ≫ cokernel.π D.arrow)
  have inclusion_condition : inclusion ≫ pair = 0 :=
    intersectionInclusion_comp_pair L U D h
  have kernelProof : IsLimit (KernelFork.ofι inclusion inclusion_condition :
      KernelFork pair) := intersectionInclusion_isKernel L U D h
  let toKernel := kernel.lift pair inclusion inclusion_condition
  let fromKernel := kernelProof.lift
    (KernelFork.ofι (kernel.ι pair) (kernel.condition pair))
  have toKernel_fac : toKernel ≫ kernel.ι pair = inclusion := kernel.lift_ι _ _ _
  have fromKernel_fac : fromKernel ≫ inclusion = kernel.ι pair := by
    exact kernelProof.fac (KernelFork.ofι (kernel.ι pair) (kernel.condition pair))
      WalkingParallelPair.zero
  have inclusion_zero : inclusion ≫ Abelian.coimage.π pair = 0 := by
    rw [← toKernel_fac, Category.assoc]
    simp [Abelian.coimage.π]
  have kernel_zero : kernel.ι pair ≫ cokernel.π inclusion = 0 := by
    rw [← fromKernel_fac, Category.assoc]
    simp
  let forward := cokernel.desc inclusion (Abelian.coimage.π pair) inclusion_zero
  let backward := cokernel.desc (kernel.ι pair) (cokernel.π inclusion) kernel_zero
  have forward_backward : forward ≫ backward = 𝟙 _ := by
    apply (cancel_epi (cokernel.π inclusion)).1
    simp [forward, backward]
  have backward_forward : backward ≫ forward = 𝟙 _ := by
    apply (cancel_epi (Abelian.coimage.π pair)).1
    simp [forward, backward]
  have forward_isIso : IsIso forward := ⟨backward, forward_backward, backward_forward⟩
  have identification : quotientIntersectionPair L U D h =
      forward ≫ Abelian.factorThruCoimage pair := by
    apply (cancel_epi (cokernel.π inclusion)).1
    simp [forward, pair, inclusion, quotientIntersectionPair_fac]
  rw [identification]
  infer_instance

end

end CategoryTheory.Subobject
