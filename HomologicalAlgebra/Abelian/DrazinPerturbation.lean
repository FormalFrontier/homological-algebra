/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Abelian.DrazinProjector
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Drazin inverses of commuting nilpotent perturbations

For an endomorphism `f` of a Noetherian and Artinian object in an abelian category,
adding a commuting nilpotent endomorphism `n` generally changes `drazinInverse f`.
The stable-image projector `f * drazinInverse f`, however, remains unchanged.

A witness `n ^ m = 0` gives a finite geometric formula with terms
`(-(drazinInverse f * n)) ^ k * drazinInverse f` for `k` in `Finset.range m`.
The negative sign, factor order and truncation at degree `m - 1` are those of the
nilpotent geometric inverse. The witness need not be minimal or positive:
`m = 0` forces `𝟙 X = 0`, and the empty sum is zero.

The projector is not its complement `1 - f * drazinInverse f`. That complement
need not be nilpotent; the existing nilpotent component is
`f * (1 - f * drazinInverse f)`.

The formulation uses this library's canonical Drazin characterization and projector
API, together with Mathlib's noncommutative nilpotent algebra and finite geometric
sums. No commutativity of the whole endomorphism ring or chosen splitting is needed.
-/

@[expose] public section

universe u v

namespace CategoryTheory.End

open scoped BigOperators

variable {C : Type u} [Category.{v} C] [Abelian C] {X : C}
  [IsNoetherianObject X] [IsArtinianObject X]

private theorem mul_drazinInverse_sum_support (f n : End X) (m : ℕ) :
    (f * drazinInverse f) *
        (∑ k ∈ Finset.range m, (-(drazinInverse f * n)) ^ k * drazinInverse f) =
      ∑ k ∈ Finset.range m, (-(drazinInverse f * n)) ^ k * drazinInverse f := by
  have hd : (f * drazinInverse f) * drazinInverse f = drazinInverse f := by
    rw [(commute_drazinInverse f).eq]
    exact drazinInverse_mul_self_mul f
  have hx : (f * drazinInverse f) * (-(drazinInverse f * n)) =
      -(drazinInverse f * n) := by
    rw [mul_neg, ← mul_assoc, hd]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  cases k with
  | zero => simpa only [pow_zero, one_mul] using hd
  | succ k =>
      calc
        (f * drazinInverse f) *
            ((-(drazinInverse f * n)) ^ (k + 1) * drazinInverse f) =
            ((f * drazinInverse f) * (-(drazinInverse f * n))) *
              ((-(drazinInverse f * n)) ^ k * drazinInverse f) := by
          simp only [pow_succ', mul_assoc]
        _ = (-(drazinInverse f * n)) *
            ((-(drazinInverse f * n)) ^ k * drazinInverse f) := by rw [hx]
        _ = (-(drazinInverse f * n)) ^ (k + 1) * drazinInverse f := by
          rw [pow_succ', mul_assoc]

private theorem commute_add_sum_drazinInverse (f n : End X) (hfn : Commute f n)
    (m : ℕ) :
    Commute (f + n)
      (∑ k ∈ Finset.range m, (-(drazinInverse f * n)) ^ k * drazinInverse f) := by
  have hdn : Commute (drazinInverse f) n := hfn.drazinInverse_left
  have hhd : Commute (f + n) (drazinInverse f) :=
    (commute_drazinInverse f).add_left hdn.symm
  have hhn : Commute (f + n) n := hfn.add_left (Commute.refl n)
  have hhx : Commute (f + n) (-(drazinInverse f * n)) :=
    (hhd.mul_right hhn).neg_right
  refine Commute.sum_right (Finset.range m)
    (fun k => (-(drazinInverse f * n)) ^ k * drazinInverse f) (f + n) ?_
  intro k _
  exact (hhx.pow_right k).mul_right hhd

private theorem add_mul_sum_drazinInverse_eq (f n : End X) (hfn : Commute f n)
    (m : ℕ) (hn : n ^ m = 0) :
    (f + n) *
        (∑ k ∈ Finset.range m, (-(drazinInverse f * n)) ^ k * drazinInverse f) =
      f * drazinInverse f := by
  have hdn : Commute (drazinInverse f) n := hfn.drazinInverse_left
  have hpow : (drazinInverse f * n) ^ m = 0 := by
    rw [hdn.mul_pow, hn, mul_zero]
  have hneg : (-(drazinInverse f * n)) ^ m = 0 := by
    rw [neg_pow, hpow, mul_zero]
  have hgeom : (1 + drazinInverse f * n) *
      (∑ k ∈ Finset.range m, (-(drazinInverse f * n)) ^ k) = 1 := by
    simpa only [sub_neg_eq_add, hneg, sub_zero] using
      (mul_neg_geom_sum (-(drazinInverse f * n)) m)
  have hdx : Commute (drazinInverse f) (-(drazinInverse f * n)) :=
    ((Commute.refl (drazinInverse f)).mul_right hdn).neg_right
  have hds : Commute (drazinInverse f)
      (∑ k ∈ Finset.range m, (-(drazinInverse f * n)) ^ k) := by
    refine Commute.sum_right (Finset.range m)
      (fun k => (-(drazinInverse f * n)) ^ k) (drazinInverse f) ?_
    intro k _
    exact hdx.pow_right k
  have hd : (f * drazinInverse f) * drazinInverse f = drazinInverse f := by
    rw [(commute_drazinInverse f).eq]
    exact drazinInverse_mul_self_mul f
  have hex : (f * drazinInverse f) * (drazinInverse f * n) =
      drazinInverse f * n := by
    rw [← mul_assoc, hd]
  calc
    (f + n) *
        (∑ k ∈ Finset.range m, (-(drazinInverse f * n)) ^ k * drazinInverse f) =
        (f + n) *
          ((∑ k ∈ Finset.range m, (-(drazinInverse f * n)) ^ k) * drazinInverse f) := by
      rw [Finset.sum_mul]
    _ = (f + n) *
        (drazinInverse f * (∑ k ∈ Finset.range m, (-(drazinInverse f * n)) ^ k)) := by
      rw [← hds.eq]
    _ = (f * drazinInverse f + drazinInverse f * n) *
        (∑ k ∈ Finset.range m, (-(drazinInverse f * n)) ^ k) := by
      rw [← mul_assoc, add_mul, ← hdn.eq]
    _ = ((f * drazinInverse f) * (1 + drazinInverse f * n)) *
        (∑ k ∈ Finset.range m, (-(drazinInverse f * n)) ^ k) := by
      rw [mul_add, mul_one, hex]
    _ = (f * drazinInverse f) *
        ((1 + drazinInverse f * n) *
          (∑ k ∈ Finset.range m, (-(drazinInverse f * n)) ^ k)) := mul_assoc _ _ _
    _ = f * drazinInverse f := by rw [hgeom, mul_one]

private theorem exists_pow_add_mul_complement_eq_zero (f n : End X) (hfn : Commute f n)
    (hn : IsNilpotent n) : ∃ r : ℕ, (f + n) ^ r * (1 - f * drazinInverse f) = 0 := by
  let q : End X := 1 - f * drazinInverse f
  have hfd := commute_drazinInverse f
  have hdn : Commute (drazinInverse f) n := hfn.drazinInverse_left
  have hfq : Commute f q :=
    (Commute.one_right f).sub_right ((Commute.refl f).mul_right hfd)
  have hnq : Commute n q :=
    (Commute.one_right n).sub_right (hfn.symm.mul_right hdn.symm)
  have he := isIdempotentElem_mul_drazinInverse f
  have hq : IsIdempotentElem q := by
    dsimp only [q]
    rw [IsIdempotentElem, mul_sub, mul_one, sub_mul, one_mul, he.eq, sub_self, sub_zero]
  have hcomm : Commute (f * q) (n * q) :=
    (hfn.mul_left hnq.symm).mul_right (hfq.mul_left (Commute.refl q))
  have hhq : Commute (f + n) q := hfq.add_left hnq
  have hnil : IsNilpotent ((f + n) * q) := by
    rw [add_mul]
    exact hcomm.isNilpotent_add (isNilpotent_mul_one_sub_mul_drazinInverse f)
      (hnq.isNilpotent_mul_right hn)
  obtain ⟨k, hk⟩ := hnil
  refine ⟨k + 1, ?_⟩
  change (f + n) ^ (k + 1) * q = 0
  calc
    (f + n) ^ (k + 1) * q = ((f + n) * q) ^ (k + 1) := by
      rw [hhq.mul_pow, hq.pow_succ_eq k]
    _ = 0 := by rw [pow_succ, hk, zero_mul]

/-- Adding a commuting nilpotent endomorphism gives this finite geometric formula
for the canonical Drazin inverse. The hypothesis `n ^ m = 0` is the only nilpotency
witness required, with no minimality or positivity condition. The range is empty
when `m = 0`, in which case `𝟙 X = 0`. -/
theorem drazinInverse_add_eq_sum_range (f n : End X) (hfn : Commute f n) (m : ℕ)
    (hn : n ^ m = 0) :
    drazinInverse (f + n) =
      ∑ k ∈ Finset.range m, (-(drazinInverse f * n)) ^ k * drazinInverse f := by
  let s : End X :=
    ∑ k ∈ Finset.range m, (-(drazinInverse f * n)) ^ k * drazinInverse f
  have hsComm : Commute (f + n) s := commute_add_sum_drazinInverse f n hfn m
  have hsMul : (f + n) * s = f * drazinInverse f :=
    add_mul_sum_drazinInverse_eq f n hfn m hn
  have hsSupport : (f * drazinInverse f) * s = s :=
    mul_drazinInverse_sum_support f n m
  obtain ⟨r, hr⟩ := exists_pow_add_mul_complement_eq_zero f n hfn ⟨m, hn⟩
  have hrSupport : (f + n) ^ r * (f * drazinInverse f) = (f + n) ^ r := by
    rw [mul_sub, mul_one] at hr
    exact (sub_eq_zero.mp hr).symm
  apply Eq.symm
  apply (eq_drazinInverse_iff (f + n) s).2
  refine ⟨hsComm, ?_, ⟨r, ?_⟩⟩
  · calc
      s * (f + n) * s = ((f + n) * s) * s := by rw [← hsComm.eq]
      _ = (f * drazinInverse f) * s := by rw [hsMul]
      _ = s := hsSupport
  · calc
      (f + n) ^ (r + 1) * s = (f + n) ^ r * ((f + n) * s) := by
        rw [pow_succ, mul_assoc]
      _ = (f + n) ^ r * (f * drazinInverse f) := by rw [hsMul]
      _ = (f + n) ^ r := hrSupport

/-- A commuting nilpotent perturbation preserves the stable-image projector
`f * drazinInverse f`, although the Drazin inverse itself generally changes.
This is the projector, not its complementary idempotent. -/
theorem add_mul_drazinInverse_of_isNilpotent (f n : End X) (hfn : Commute f n)
    (hn : IsNilpotent n) :
    (f + n) * drazinInverse (f + n) = f * drazinInverse f := by
  obtain ⟨m, hm⟩ := hn
  rw [drazinInverse_add_eq_sum_range f n hfn m hm]
  exact add_mul_sum_drazinInverse_eq f n hfn m hm

end CategoryTheory.End
