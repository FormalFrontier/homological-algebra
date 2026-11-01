/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Order.JordanHolder
public import Mathlib.Order.KrullDimension

/-!
# Length in modular lattices

Height and coheight measure strict steps in finite chains, with value infinity when
these lengths are unbounded. In a modular lattice with a top element, their sum at
any element is the height of top. A cover series from bottom to top measures this
height by its number of steps.

Finite-dimensionality uses `FiniteDimensionalOrder`, not finiteness of the underlying
set. The two chain conditions use `WellFoundedLT` and `WellFoundedGT`.

## References

This development follows the height and series interfaces of Mathlib's
`Order.KrullDimension` and `Order.JordanHolder`. Mathlib's `RingTheory.Length`
provides the submodule-lattice specialization.
-/

@[expose] public section

universe u

namespace Order

/-- At every element of a modular lattice with top, height plus coheight is the
height of top. No bottom element or chain condition is required. -/
theorem height_top_eq_height_add_coheight {L : Type u} [Lattice L] [OrderTop L]
    [IsModularLattice L] (a : L) :
    height (⊤ : L) = height a + coheight a := by
  apply le_antisymm
  · by_cases h : height a + coheight a = ⊤
    · rw [h]
      exact le_top
    have hha : height a ≠ ⊤ := fun ha ↦ h (by simp [ha])
    have hca : coheight a ≠ ⊤ := fun ha ↦ h (by simp [ha])
    have htop : height (⊤ : Set.Ici a) = coheight a :=
      WithBot.coe_inj.mp ((height_top_eq_krullDim (α := Set.Ici a)).trans
        (coheight_eq_krullDim_Ici a).symm)
    let g (x : L) : Set.Ici a := ⟨x ⊔ a, le_sup_right⟩
    have hinf (x : L) : height (x ⊓ a) < ⊤ :=
      (height_mono inf_le_right).trans_lt hha.lt_top
    have hg (x : L) : height (g x) < ⊤ :=
      (height_mono (show g x ≤ ⊤ from le_top)).trans_lt (htop.symm ▸ hca.lt_top)
    let f (x : L) : ℕ∞ := height (x ⊓ a) + height (g x)
    -- Modularity makes at least one of the two projections strictly increase.
    have hf : StrictMono f := by
      intro x y hxy
      have hp := strictMono_inf_prod_sup (z := a) hxy
      by_cases heq : x ⊓ a = y ⊓ a
      · have hsup : g x < g y :=
          lt_of_le_not_ge hp.le.2 fun hrev ↦ hp.not_ge ⟨heq.ge, hrev⟩
        exact ENat.add_lt_add_of_le_of_lt (hinf x).ne
          (height_mono hp.le.1) (height_strictMono hsup (hg x))
      · exact ENat.add_lt_add_of_lt_of_le (hg x).ne
          (height_strictMono (lt_of_le_of_ne hp.le.1 heq) (hinf x))
          (height_mono (show g x ≤ g y from hp.le.2))
    have hgtop : g (⊤ : L) = ⊤ := by
      apply Subtype.ext
      simp [g]
    simpa [f, hgtop, htop] using height_le_height_apply_of_strictMono f hf (⊤ : L)
  · apply WithBot.coe_le_coe.mp
    have hle : height a + coheight a ≤ ⨆ x : L, height x + coheight x :=
      le_iSup (fun x : L ↦ height x + coheight x) a
    calc
      ((height a + coheight a : ℕ∞) : WithBot ℕ∞) ≤
          ↑(⨆ x : L, height x + coheight x) := WithBot.coe_mono hle
      _ = krullDim L := krullDim_eq_iSup_height_add_coheight_of_nonempty.symm
      _ = ↑(height (⊤ : L)) := height_top_eq_krullDim.symm

private lemma height_Iic {L : Type u} [Preorder L] (b : L) (a : Set.Iic b) :
    height a = height (a : L) := by
  apply height_eq_of_strictMono (fun x : Set.Iic b ↦ (x : L)) (fun _ _ h ↦ h)
  intro x y hy
  exact ⟨⟨y, hy.le.trans x.property⟩, hy, rfl⟩

private lemma height_eq_add_one_of_covBy {L : Type u} [Lattice L]
    [IsModularLattice L] {a b : L} (h : a ⋖ b) :
    height b = height a + 1 := by
  let a' : Set.Iic b := ⟨a, h.le⟩
  have hc : coheight a' = 1 := by
    apply le_antisymm
    · apply (coheight_le_coe_iff (n := 1)).mpr
      intro y hy
      rcases h.eq_or_eq hy.le y.property with heq | heq
      · exact (hy.ne (Subtype.ext heq.symm)).elim
      · have hytop : y = ⊤ := Subtype.ext heq
        simp [hytop]
    · simpa using coheight_add_one_le (show a' < ⊤ from h.lt)
  have htop : ((⊤ : Set.Iic b) : L) = b := rfl
  have ha : (a' : L) = a := rfl
  simpa only [height_Iic, hc, htop, ha] using height_top_eq_height_add_coheight a'

private lemma height_last_eq_height_head_add_length {L : Type u} [Lattice L]
    [IsModularLattice L] (s : RelSeries {(a, b) : L × L | a ⋖ b}) :
    height s.last = height s.head + s.length := by
  induction s using RelSeries.inductionOn with
  | singleton x => simp
  | cons s x hx ih =>
    rw [RelSeries.last_cons, RelSeries.head_cons, RelSeries.cons_length, ih,
      height_eq_add_one_of_covBy hx, Nat.cast_add, Nat.cast_one]
    ac_rfl

/-- A nonempty modular lattice has bounded lengths of strict chains exactly when
both strict order relations are well-founded. -/
theorem finiteDimensionalOrder_iff_wellFoundedLT_and_wellFoundedGT {L : Type u}
    [Lattice L] [IsModularLattice L] [Nonempty L] :
    FiniteDimensionalOrder L ↔ WellFoundedLT L ∧ WellFoundedGT L := by
  constructor
  · intro h
    let := h
    exact ⟨⟨SetRel.IsWellFounded.of_finiteDimensional {(a, b) : L × L | a < b}⟩,
      ⟨SetRel.IsWellFounded.inv_of_finiteDimensional {(a, b) : L × L | a < b}⟩⟩
  · rintro ⟨hLT, hGT⟩
    let := hLT
    let := hGT
    obtain ⟨f, hmin, n, hmax, hstep⟩ :=
      exists_covBy_seq_of_wellFoundedLT_wellFoundedGT L
    let s : RelSeries {(a, b) : L × L | a ⋖ b} :=
      ⟨n, fun i ↦ f i, fun i ↦ hstep i i.isLt⟩
    let p : LTSeries L := ⟨n, fun i ↦ f i, fun i ↦ (hstep i i.isLt).lt⟩
    have hs : height s.last = (s.length : ℕ∞) := by
      rw [height_last_eq_height_head_add_length]
      have hh : height s.head = 0 := by
        apply height_eq_zero.mpr
        change IsMin (f 0)
        exact hmin
      simp [hh]
    refine ⟨⟨p, fun q ↦ ?_⟩⟩
    apply ENat.natCast_le_natCast.mp
    calc
      (q.length : ℕ∞) ≤ height s.last := length_le_height (by
        change q.last ≤ f n
        exact le_sup_left.trans (hmax le_sup_right))
      _ = (p.length : ℕ∞) := hs

end Order

namespace RelSeries

/-- A full bottom-to-top cover series in a bounded modular lattice has length equal
to the height of top. No chain condition is assumed for a given series. -/
theorem length_eq_height_top {L : Type u} [Lattice L] [BoundedOrder L]
    [IsModularLattice L] (s : RelSeries {(a, b) : L × L | a ⋖ b})
    (hhead : s.head = ⊥) (hlast : s.last = ⊤) :
    (s.length : ℕ∞) = Order.height (⊤ : L) := by
  simpa [hhead, hlast] using (Order.height_last_eq_height_head_add_length s).symm

end RelSeries
