/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Abelian.JordanHolder
public import HomologicalAlgebra.Order.Length
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Numerical length of objects

The length of an object is the ENat-valued height of its largest canonical
subobject. It counts strict subobject steps, rather than subobjects or vertices.
The definition, isomorphism invariance, lower-interval formula and monomorphism
monotonicity apply in any category, with independent object and morphism universes.

In an abelian category, lower and upper subobject intervals identify the lengths
of subobjects and cokernels with height and coheight. Length is additive on short
exact sequences, including infinite lengths. A given full composition series
computes length without additional chain conditions. Finite length is equivalent
to the existing Noetherian and Artinian object conditions.

## References

The numerical invariant follows Mathlib's `Order.KrullDimension`. The series
interpretation uses `Abelian.JordanHolder` and Mathlib's `Order.JordanHolder`;
Mathlib's `RingTheory.Length` provides the module specialization.
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The length of an object is the height of the top of its canonical subobject
order, with value infinity when finite strict chains have unbounded lengths. -/
noncomputable def objectLength (X : C) : ℕ∞ :=
  Order.height (⊤ : Subobject X)

/-- Object length is characterized by the height of the largest subobject. -/
theorem objectLength_eq_height (X : C) :
    objectLength X = Order.height (⊤ : Subobject X) := by
  rfl

/-- Isomorphic objects have the same length in any category. -/
theorem objectLength_iso {X Y : C} (e : X ≅ Y) :
    objectLength X = objectLength Y := by
  rw [objectLength_eq_height, objectLength_eq_height]
  simpa only [OrderIso.map_top] using
    (Order.height_orderIso (Subobject.mapIsoToOrderIso e) (⊤ : Subobject X)).symm

/-- In a category with a zero object, length zero characterizes zero objects. -/
theorem objectLength_eq_zero_iff [Limits.HasZeroObject C] (X : C) :
    objectLength X = 0 ↔ Limits.IsZero X := by
  rw [objectLength_eq_height, Order.height_eq_zero]
  constructor
  · intro h
    have htop : (⊤ : Subobject X) = ⊥ := le_antisymm (h bot_le) le_top
    exact (Limits.isZero_zero C).of_iso
      ((asIso (⊤ : Subobject X).arrow).symm ≪≫
        Subobject.isoOfEq _ _ htop ≪≫ Subobject.botCoeIsoZero)
  · intro hX
    let : Subsingleton (Subobject X) := Subobject.subsingleton_of_isZero hX
    intro P _
    exact le_of_eq (Subsingleton.elim _ _)

/-- In a category with a zero object and zero morphisms, length one characterizes
simple objects. -/
theorem objectLength_eq_one_iff [Limits.HasZeroObject C] [Limits.HasZeroMorphisms C]
    (X : C) : objectLength X = 1 ↔ Simple X := by
  rw [objectLength_eq_height, simple_iff_subobject_isSimpleOrder,
    ← Order.krullDim_eq_one_iff_of_boundedOrder, ← Order.height_top_eq_krullDim]
  exact WithBot.coe_inj.symm

/-- The length of a subobject is its height in the ambient subobject order. -/
theorem objectLength_subobject {X : C} (P : Subobject X) :
    objectLength (P : C) = Order.height P := by
  rw [objectLength_eq_height]
  calc
    Order.height (⊤ : Subobject (P : C)) = Order.height (⊤ : Set.Iic P) := by
      simpa only [OrderIso.map_top] using
        (Order.height_orderIso (Subobject.subobjectOrderIso P) ⊤).symm
    _ = Order.height P := by
      have h := Order.height_eq_krullDim_Iic P
      rw [← Order.height_top_eq_krullDim] at h
      exact WithBot.coe_inj.mp h.symm

/-- Monomorphisms do not decrease object length. -/
theorem objectLength_le_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] :
    objectLength X ≤ objectLength Y := by
  calc
    objectLength X = objectLength (Subobject.mk f : C) :=
      objectLength_iso (Subobject.underlyingIso f).symm
    _ = Order.height (Subobject.mk f) := objectLength_subobject _
    _ ≤ Order.height (⊤ : Subobject Y) := Order.height_mono le_top
    _ = objectLength Y := (objectLength_eq_height Y).symm

section Abelian

variable [Abelian C]

/-- The length of the cokernel of a subobject inclusion is its coheight. -/
theorem objectLength_cokernel {X : C} (P : Subobject X) :
    objectLength (Limits.cokernel P.arrow) = Order.coheight P := by
  apply WithBot.coe_injective (α := ℕ∞)
  rw [objectLength_eq_height, Order.height_top_eq_krullDim,
    Order.krullDim_eq_of_orderIso (Abelian.Subobject.cokernelOrderIso P),
    ← Order.coheight_eq_krullDim_Ici]

/-- Epimorphisms do not increase object length in an abelian category. -/
theorem objectLength_le_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] :
    objectLength Y ≤ objectLength X := by
  let e := Abelian.Subobject.epiOrderIso f
  have he : StrictMono (fun Q : Subobject Y => (e Q : Subobject X)) :=
    fun _ _ h => e.strictMono h
  calc
    objectLength Y = Order.height (⊤ : Subobject Y) := objectLength_eq_height Y
    _ ≤ Order.height (e ⊤ : Subobject X) :=
      Order.height_le_height_apply_of_strictMono _ he _
    _ ≤ Order.height (⊤ : Subobject X) := Order.height_mono le_top
    _ = objectLength X := (objectLength_eq_height X).symm

/-- An object in an abelian category has finite length exactly when it is both
Noetherian and Artinian. -/
theorem objectLength_ne_top_iff (X : C) :
    objectLength X ≠ ⊤ ↔ IsNoetherianObject X ∧ IsArtinianObject X := by
  have hdim : FiniteDimensionalOrder (Subobject X) ↔ objectLength X ≠ ⊤ := by
    rw [Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top,
      ← Order.height_top_eq_krullDim, objectLength_eq_height]
    constructor
    · intro h htop
      exact h.2 (congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) htop)
    · intro h
      exact ⟨WithBot.coe_ne_bot (a := Order.height (⊤ : Subobject X)),
        fun htop => h (WithBot.coe_eq_top.mp htop)⟩
  rw [← hdim, Order.finiteDimensionalOrder_iff_wellFoundedLT_and_wellFoundedGT]
  simp only [IsNoetherianObject, IsArtinianObject, ObjectProperty.is_iff,
    isNoetherianObject, isArtinianObject, and_comm]

/-- A full canonical composition series counts object length by its strict steps.
Both endpoints are required; no chain condition is assumed for a given series. -/
theorem objectLength_compositionSeries {X : C} (s : CompositionSeries (Subobject X))
    (hhead : s.head = ⊥) (hlast : s.last = ⊤) :
    (s.length : ℕ∞) = objectLength X := by
  exact RelSeries.length_eq_height_top s hhead hlast

/-- Object length is additive on every short exact sequence in an abelian category,
without finiteness or splitting assumptions. -/
theorem ShortComplex.ShortExact.objectLength_eq_add {S : ShortComplex C}
    (hS : S.ShortExact) :
    objectLength S.X₂ = objectLength S.X₁ + objectLength S.X₃ := by
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  let e : Limits.cokernel S.f ≅ Limits.cokernel (Subobject.mk S.f).arrow :=
    Limits.cokernel.mapIso _ _ (Subobject.underlyingIso _).symm (Iso.refl _) (by simp)
  let e' : Limits.cokernel S.f ≅ S.X₃ :=
    (Limits.cokernelIsCokernel S.f).coconePointUniqueUpToIso hS.exact.gIsCokernel
  calc
    objectLength S.X₂ = objectLength ((Subobject.mk S.f : Subobject S.X₂) : C) +
        objectLength (Limits.cokernel (Subobject.mk S.f).arrow) := by
      rw [objectLength_subobject, objectLength_cokernel, objectLength_eq_height]
      exact Order.height_top_eq_height_add_coheight _
    _ = objectLength S.X₁ + objectLength S.X₃ := by
      rw [objectLength_iso (Subobject.underlyingIso S.f),
        ← objectLength_iso e, objectLength_iso e']

/-- In a short exact sequence, the middle object has finite length exactly when
both end objects do. -/
theorem ShortComplex.ShortExact.objectLength_ne_top_iff {S : ShortComplex C}
    (hS : S.ShortExact) :
    objectLength S.X₂ ≠ ⊤ ↔ objectLength S.X₁ ≠ ⊤ ∧ objectLength S.X₃ ≠ ⊤ := by
  rw [hS.objectLength_eq_add]
  exact (not_congr ENat.add_eq_top).trans not_or

/-- For a Noetherian and Artinian middle object, ENat length additivity gives Nat
additivity. No separate chain conditions on the end objects are assumed. -/
theorem ShortComplex.ShortExact.objectLength_toNat_eq_add {S : ShortComplex C}
    (hS : S.ShortExact) [IsNoetherianObject S.X₂] [IsArtinianObject S.X₂] :
    (objectLength S.X₂).toNat = (objectLength S.X₁).toNat + (objectLength S.X₃).toNat := by
  have h₂ : objectLength S.X₂ ≠ ⊤ :=
    (CategoryTheory.objectLength_ne_top_iff S.X₂).2 ⟨inferInstance, inferInstance⟩
  obtain ⟨h₁, h₃⟩ := hS.objectLength_ne_top_iff.mp h₂
  rw [hS.objectLength_eq_add, ENat.toNat_add h₁ h₃]

end Abelian

end CategoryTheory
