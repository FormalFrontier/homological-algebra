/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Abelian.Drazin
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Logic.Pairwise

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum

/-!
# Drazin inverses of orthogonal sums

For endomorphisms of a Noetherian and Artinian object in an abelian category,
the canonical Drazin inverse preserves sums whose distinct summands annihilate
each other in both orders. Multiplication is that of the canonical endomorphism
ring: `f * g = g ≫ f`.

`End.drazinInverse_add_of_mul_eq_zero` gives the binary formula with both
zero-product hypotheses. `End.drazinInverse_sum` gives the finite-support formula.
Its pairwise hypothesis is restricted to the support and quantifies over ordered
distinct indices, so it includes both product orders. Empty and singleton supports
are included; the index type need not be finite.

## References

* `HomologicalAlgebra.Abelian.Drazin` provides the canonical Drazin inverse and
  its characteristic equations.
* `Mathlib.Algebra.BigOperators.Group.Finset.Defs` provides finite sums and their
  notation; `Mathlib.Logic.Pairwise` provides pairwise relations on sets.
* `Mathlib.Data.Nat.Choose.Sum` provides the binomial theorem for commuting
  elements of a possibly noncommutative semiring.
-/

@[expose] public section

universe v u w

namespace CategoryTheory.End

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X : C} [IsNoetherianObject X] [IsArtinianObject X]

/-- The Drazin inverse of a sum of mutually annihilating endomorphisms is the sum
of their Drazin inverses. Both product orders are required. -/
theorem drazinInverse_add_of_mul_eq_zero (f g : End X) (hfg : f * g = 0)
    (hgf : g * f = 0) :
    drazinInverse (f + g) = drazinInverse f + drazinInverse g := by
  -- Intertwining with zero transfers each ordered annihilation to the inverses.
  have hzero (a b : End X) (hab : a * b = 0) :
      drazinInverse a * b = 0 ∧ a * drazinInverse b = 0 := by
    constructor
    · have h := drazinInverse_comp_eq_comp_drazinInverse (0 : End X) a b
        (by simpa only [← mul_def, mul_zero] using hab.symm)
      simpa only [← mul_def, drazinInverse_zero, mul_zero] using h.symm
    · have h := drazinInverse_comp_eq_comp_drazinInverse b (0 : End X) a
        (by simpa only [← mul_def, zero_mul] using hab)
      simpa only [← mul_def, drazinInverse_zero, zero_mul] using h
  obtain ⟨hdfg, hfdg⟩ := hzero f g hfg
  obtain ⟨hdgf, hgdf⟩ := hzero g f hgf
  have hcomm : Commute f g := by
    change f * g = g * f
    rw [hfg, hgf]
  -- In the binomial expansion only the two endpoints survive, provided n > 0.
  have hpow (n : ℕ) (hn : 0 < n) : (f + g) ^ n = f ^ n + g ^ n := by
    rw [hcomm.add_pow n]
    calc
      (∑ m ∈ Finset.range (n + 1), f ^ m * g ^ (n - m) * (n.choose m : End X)) =
          f ^ n * g ^ (n - n) * (n.choose n : End X) +
            f ^ 0 * g ^ (n - 0) * (n.choose 0 : End X) := by
        apply Finset.sum_eq_add_of_mem n 0
        · exact Finset.mem_range.mpr (Nat.lt_succ_self n)
        · exact Finset.mem_range.mpr (Nat.zero_lt_succ n)
        · exact Nat.ne_of_gt hn
        · intro m hm hmn
          have hfm : f ^ m * g = 0 :=
            pow_mul_eq_zero_of_le (Nat.one_le_iff_ne_zero.mpr hmn.2)
              (by simpa only [pow_one] using hfg)
          have hlt : m < n :=
            lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hm)) hmn.1
          have hgm : g ^ (n - m) * f ^ m = 0 :=
            pow_mul_eq_zero_of_le (Nat.sub_pos_of_lt hlt)
              (by simpa only [pow_one, (hcomm.pow_left m).eq] using hfm)
          rw [(hcomm.pow_pow m (n - m)).eq, hgm, zero_mul]
      _ = f ^ n + g ^ n := by
        simp only [Nat.sub_self, Nat.sub_zero, pow_zero, one_mul, mul_one,
          Nat.choose_self, Nat.choose_zero_right, Nat.cast_one]
  apply ((eq_drazinInverse_iff (f + g) (drazinInverse f + drazinInverse g)).2 ?_).symm
  refine ⟨?_, ?_, ?_⟩
  · change (f + g) * (drazinInverse f + drazinInverse g) =
        (drazinInverse f + drazinInverse g) * (f + g)
    simp only [add_mul, mul_add, hfdg, hgdf, hdfg, hdgf, add_zero, zero_add]
    rw [(commute_drazinInverse f).eq, (commute_drazinInverse g).eq]
  · calc
      (drazinInverse f + drazinInverse g) * (f + g) *
          (drazinInverse f + drazinInverse g) =
          (drazinInverse f * f + drazinInverse g * g) *
            (drazinInverse f + drazinInverse g) := by
        simp only [add_mul, mul_add, hdfg, hdgf, add_zero, zero_add]
      _ = drazinInverse f * f * drazinInverse f +
          drazinInverse g * g * drazinInverse g := by
        simp only [mul_add, add_mul, mul_assoc, hfdg, hgdf, mul_zero, add_zero, zero_add]
      _ = drazinInverse f + drazinInverse g := by
        rw [drazinInverse_mul_self_mul, drazinInverse_mul_self_mul]
  · obtain ⟨nf, hf⟩ := exists_pow_succ_mul_drazinInverse f
    obtain ⟨ng, hg⟩ := exists_pow_succ_mul_drazinInverse g
    -- The common index is positive even when either characteristic witness is zero.
    let N := nf + ng + 1
    have hN : 0 < N := Nat.succ_pos _
    have hfN : f ^ (N + 1) * drazinInverse f = f ^ N := by
      simpa only [N, ← mul_assoc, ← pow_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using congrArg (fun z : End X => f ^ (ng + 1) * z) hf
    have hgN : g ^ (N + 1) * drazinInverse g = g ^ N := by
      simpa only [N, ← mul_assoc, ← pow_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using congrArg (fun z : End X => g ^ (nf + 1) * z) hg
    have hfgN : f ^ (N + 1) * drazinInverse g = 0 :=
      pow_mul_eq_zero_of_le (Nat.succ_le_succ (Nat.zero_le N))
        (by simpa only [pow_one] using hfdg)
    have hgfN : g ^ (N + 1) * drazinInverse f = 0 :=
      pow_mul_eq_zero_of_le (Nat.succ_le_succ (Nat.zero_le N))
        (by simpa only [pow_one] using hgdf)
    refine ⟨N, ?_⟩
    rw [hpow (N + 1) (Nat.succ_pos N), hpow N hN, add_mul, mul_add, mul_add,
      hfN, hfgN, hgfN, hgN, add_zero, zero_add]

/-- The Drazin inverse preserves a finite sum when distinct supported summands
annihilate each other in both orders. The pairwise condition is on indices in `s`,
not on all indices or on distinct values of the family. -/
theorem drazinInverse_sum {ι : Type w} (s : Finset ι) (f : ι → End X)
    (h : (s : Set ι).Pairwise (fun i j => f i * f j = 0)) :
    drazinInverse (∑ i ∈ s, f i) = ∑ i ∈ s, drazinInverse (f i) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp only [Finset.sum_empty, drazinInverse_zero]
  | @insert a s ha ih =>
      intro h
      have hs : (s : Set ι).Pairwise (fun i j => f i * f j = 0) := by
        intro i hi j hj hij
        exact h (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj) hij
      have hleft : f a * (∑ i ∈ s, f i) = 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_eq_zero
        intro i hi
        exact h (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi)
          (ne_of_mem_of_not_mem hi ha).symm
      have hright : (∑ i ∈ s, f i) * f a = 0 := by
        rw [Finset.sum_mul]
        apply Finset.sum_eq_zero
        intro i hi
        exact h (Finset.mem_insert_of_mem hi) (Finset.mem_insert_self a s)
          (ne_of_mem_of_not_mem hi ha)
      rw [Finset.sum_insert ha, drazinInverse_add_of_mul_eq_zero _ _ hleft hright,
        ih hs, Finset.sum_insert ha]

end CategoryTheory.End
