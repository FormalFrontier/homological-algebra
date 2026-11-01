/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Abelian.EndomorphismPowerLength
public import HomologicalAlgebra.Abelian.ModuleCatLength
public import HomologicalAlgebra.ModuleCat.Subobject
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Power-kernel bounds from module length

For a module over an arbitrary ring, finite module length bounds stabilization
of power kernels. This extends the finite-dimensional division-ring bound.
Under the canonical order isomorphism from categorical subobjects to
submodules, categorical power kernels agree with Mathlib's stabilized
finite-dimensional power kernel.

## References

The comparison uses `ModuleCat.subobjectModule`, `ModuleCat.endRingEquiv`,
`ModuleCat.objectLength_eq_moduleLength`, and `Module.length_eq_finrank`.
The finite-dimensional agreement is with Mathlib's
`Module.End.ker_pow_eq_ker_pow_finrank_of_le`.
-/

@[expose] public section

universe u v

namespace Module.End

open CategoryTheory CategoryTheory.Limits

/-- Over any ring, power kernels stabilize by the finite module length. -/
theorem ker_pow_eq_ker_pow_length_of_le {R : Type u} [Ring R]
    {M : Type v} [AddCommGroup M] [Module R M] (f : Module.End R M)
    (hM : Module.length R M ≠ ⊤) {n : ℕ} (hn : (Module.length R M).toNat ≤ n) :
    LinearMap.ker (f ^ n) = LinearMap.ker (f ^ (Module.length R M).toNat) := by
  let g : CategoryTheory.End (ModuleCat.of R M) :=
    (ModuleCat.endRingEquiv (ModuleCat.of R M)).symm f
  have hg (k : ℕ) : (g ^ k).hom = f ^ k := by
    rw [← ModuleCat.endRingEquiv_apply, map_pow]
    exact congrArg (fun a : Module.End R M ↦ a ^ k)
      ((ModuleCat.endRingEquiv (ModuleCat.of R M)).apply_symm_apply f)
  have h : kernelSubobject (g ^ n) =
      kernelSubobject (g ^ (Module.length R M).toNat) := by
    simpa only [ModuleCat.objectLength_eq_moduleLength] using
      (kernelSubobject_pow_eq_of_objectLength_le (n := n) g
        (by simpa only [ModuleCat.objectLength_eq_moduleLength] using hM)
        (by simpa only [ModuleCat.objectLength_eq_moduleLength] using hn))
  have hle (a b : ℕ) (hab : kernelSubobject (g ^ a) = kernelSubobject (g ^ b)) :
      LinearMap.ker (f ^ a) ≤ LinearMap.ker (f ^ b) := by
    let i : ModuleCat.of R (LinearMap.ker (f ^ a)) ⟶ ModuleCat.of R M :=
      ModuleCat.ofHom (LinearMap.ker (f ^ a)).subtype
    have hi : i ≫ g ^ a = 0 := by
      apply ModuleCat.hom_ext
      ext z
      simpa only [i, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero,
        LinearMap.comp_apply, LinearMap.zero_apply, Submodule.subtype_apply, hg,
        LinearMap.mem_ker] using z.property
    have hi' : i ≫ g ^ b = 0 := by
      apply (kernelSubobject_factors_iff (g ^ b) i).mp
      rw [← hab]
      exact (kernelSubobject_factors_iff (g ^ a) i).mpr hi
    intro x hx
    have hz := congrArg
      (fun j : ModuleCat.of R (LinearMap.ker (f ^ a)) ⟶ ModuleCat.of R M ↦
        j.hom ⟨x, hx⟩) hi'
    simpa only [i, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero,
      LinearMap.comp_apply, LinearMap.zero_apply, Submodule.subtype_apply, hg,
      LinearMap.mem_ker] using hz
  exact le_antisymm (hle _ _ h) (hle _ _ h.symm)

end Module.End

namespace ModuleCat

open CategoryTheory CategoryTheory.Limits

/-- The canonical subobject-to-submodule isomorphism identifies a categorical
power kernel above the dimension bound with Mathlib's finite-dimensional
stabilized kernel, via the canonical endomorphism-ring equivalence. -/
theorem subobjectModule_kernelSubobject_pow_eq_ker_pow_finrank_of_le
    {K : Type u} [DivisionRing K] (M : ModuleCat.{v} K) [FiniteDimensional K M]
    (f : CategoryTheory.End M) {n : ℕ} (hn : Module.finrank K M ≤ n) :
    subobjectModule M (kernelSubobject (f ^ n)) =
      LinearMap.ker ((endRingEquiv M f) ^ Module.finrank K M) := by
  simpa [← endRingEquiv_apply] using
    (Module.End.ker_pow_eq_ker_pow_finrank_of_le (f := endRingEquiv M f) hn)

end ModuleCat
