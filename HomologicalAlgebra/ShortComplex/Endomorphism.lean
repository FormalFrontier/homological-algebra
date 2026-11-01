/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import HomologicalAlgebra.Abelian.EndomorphismPowers

/-!
# Nilpotence in short complexes

For an endomorphism of an exact short complex, vanishing outer powers
with exponents m and n imply vanishing of the middle power m + n.
A monic first arrow and an epic second arrow reflect vanishing powers
to the corresponding outer objects without changing the exponent.
For a short exact complex, middle nilpotence is equivalent to nilpotence
of both outer components. Every exponent is a natural number, including zero.
-/

@[expose] public section

universe v u

namespace CategoryTheory.ShortComplex

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {S : ShortComplex C}

/-- Vanishing outer powers of an endomorphism of an exact short complex
force the middle power with the sum of the exponents to vanish. -/
theorem middle_pow_add_eq_zero (hS : S.Exact) (φ : S ⟶ S) (m n : ℕ)
    (h₁ : (End.of φ.τ₁ ^ m).asHom = (0 : S.X₁ ⟶ S.X₁))
    (h₃ : (End.of φ.τ₃ ^ n).asHom = (0 : S.X₃ ⟶ S.X₃)) :
    (End.of φ.τ₂ ^ (m + n)).asHom = (0 : S.X₂ ⟶ S.X₂) := by
  have hf := End.pow_comp_eq_comp_pow
    (End.of φ.τ₁) (End.of φ.τ₂) S.f φ.comm₁₂ m
  have hg := End.pow_comp_eq_comp_pow
    (End.of φ.τ₂) (End.of φ.τ₃) S.g φ.comm₂₃ n
  have hfm : S.f ≫ (End.of φ.τ₂ ^ m).asHom = 0 := by
    simpa only [h₁, zero_comp] using hf.symm
  have hng : (End.of φ.τ₂ ^ n).asHom ≫ S.g = 0 := by
    simpa only [h₃, comp_zero] using hg
  simpa only [pow_add, End.mul_def] using hS.comp_eq_zero hng hfm

/-- A monic first arrow reflects a vanishing middle power to the left
component with the same exponent. -/
theorem left_pow_eq_zero_of_mono [Mono S.f] (φ : S ⟶ S) (n : ℕ)
    (h₂ : (End.of φ.τ₂ ^ n).asHom = (0 : S.X₂ ⟶ S.X₂)) :
    (End.of φ.τ₁ ^ n).asHom = (0 : S.X₁ ⟶ S.X₁) := by
  apply Mono.right_cancellation (f := S.f)
  simpa only [h₂, comp_zero, zero_comp] using
    End.pow_comp_eq_comp_pow (End.of φ.τ₁) (End.of φ.τ₂) S.f φ.comm₁₂ n

/-- An epic second arrow reflects a vanishing middle power to the right
component with the same exponent. -/
theorem right_pow_eq_zero_of_epi [Epi S.g] (φ : S ⟶ S) (n : ℕ)
    (h₂ : (End.of φ.τ₂ ^ n).asHom = (0 : S.X₂ ⟶ S.X₂)) :
    (End.of φ.τ₃ ^ n).asHom = (0 : S.X₃ ⟶ S.X₃) := by
  apply Epi.left_cancellation (f := S.g)
  simpa only [h₂, zero_comp, comp_zero] using
    (End.pow_comp_eq_comp_pow (End.of φ.τ₂) (End.of φ.τ₃) S.g φ.comm₂₃ n).symm

/-- In a short exact complex, the middle component is nilpotent if and
only if both outer components are nilpotent, for the given zero morphisms. -/
theorem ShortExact.isNilpotent_middle_iff (hS : S.ShortExact) (φ : S ⟶ S) :
    @IsNilpotent (End S.X₂)
      (inferInstanceAs (Zero (S.X₂ ⟶ S.X₂)))
      (inferInstanceAs (Pow (End S.X₂) ℕ)) (End.of φ.τ₂) ↔
    @IsNilpotent (End S.X₁)
      (inferInstanceAs (Zero (S.X₁ ⟶ S.X₁)))
      (inferInstanceAs (Pow (End S.X₁) ℕ)) (End.of φ.τ₁) ∧
    @IsNilpotent (End S.X₃)
      (inferInstanceAs (Zero (S.X₃ ⟶ S.X₃)))
      (inferInstanceAs (Pow (End S.X₃) ℕ)) (End.of φ.τ₃) := by
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨⟨n, left_pow_eq_zero_of_mono φ n hn⟩,
      ⟨n, right_pow_eq_zero_of_epi φ n hn⟩⟩
  · rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
    exact ⟨m + n, middle_pow_add_eq_zero hS.exact φ m n hm hn⟩

end CategoryTheory.ShortComplex
