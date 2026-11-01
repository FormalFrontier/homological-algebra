/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Abelian.Fitting
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.RingTheory.Nilpotent.Defs

import Mathlib.Algebra.Group.Commute.Hom
import Mathlib.CategoryTheory.Conj

/-!
# Drazin inverses of finite-length endomorphisms

An endomorphism `f` of a Noetherian and Artinian object in an abelian category
has a unique Drazin inverse `g`: it commutes with `f`, satisfies `g * f * g = g`,
and satisfies `f ^ (n + 1) * g = f ^ n` for some natural number `n`.
Only `g` is unique; the exponent need not be unique and may be zero.

`End.drazinInverse` constructs this endomorphism. Its characteristic equations
and `End.eq_drazinInverse_iff` let users work without unfolding the construction.
It is zero exactly for nilpotent inputs, agrees with the ordinary inverse of an
isomorphism, fixes idempotents, and gives the idempotent `f * End.drazinInverse f`.
No nonzero-object or commutativity hypothesis is needed. Object and morphism
universes are independent.

`End.map_drazinInverse` shows preservation by multiplicative maps, without
unit preservation. `Functor.map_drazinInverse` specializes this to functors
whose source and image objects are Noetherian and Artinian.

`End.drazinInverse_comp_eq_comp_drazinInverse` expresses compatibility with
arbitrary intertwining morphisms. `Commute.drazinInverse_left` gives preservation
of commutation, and `End.drazinInverse_pow` gives compatibility with every natural
power, including zero.

The Fitting decomposition splits a sufficiently high power into its kernel and
image, with nilpotent kernel restriction and invertible image restriction. The
Drazin inverse is zero on the kernel part and the inverse restriction on the
image part. Multiplication in the canonical endomorphism ring satisfies
`f * g = g ≫ f`.

## References

M. P. Drazin, *Pseudo-Inverses in Associative Rings and Semigroups*,
The American Mathematical Monthly 65 (1958), 506–514,
[doi:10.1080/00029890.1958.11991949](https://doi.org/10.1080/00029890.1958.11991949),
gives the inverse terminology.

The construction follows the Fitting decomposition formalized in
`HomologicalAlgebra.Abelian.Fitting` and the canonical restrictions in
`HomologicalAlgebra.Abelian.EndomorphismPowers`. Mathlib supplies the canonical
endomorphism ring and transport by isomorphisms through `CategoryTheory.Iso.conj`.
-/

@[expose] public section

universe u v w u' v'

namespace CategoryTheory.End

private theorem pow_succ_mul_pow_eq_of_outer_inverse {M : Type w} [Monoid M]
    {a b : M} (hab : Commute a b) (hb : b * a * b = b) (r : ℕ) :
    b ^ (r + 1) * a ^ r = b := by
  induction r with
  | zero => simp only [Nat.zero_add, pow_one, pow_zero, mul_one]
  | succ r ih =>
    calc
      b ^ (r + 1 + 1) * a ^ (r + 1) = b * (b ^ (r + 1) * a ^ r) * a := by
        rw [pow_succ' b (r + 1), pow_succ a r]
        simp only [mul_assoc]
      _ = b * b * a := by rw [ih]
      _ = b * a * b := hab.symm.right_comm b
      _ = b := hb

private theorem pow_succ_mul_eq_of_le {M : Type w} [Monoid M]
    {a b : M} {n N : ℕ} (h : a ^ (n + 1) * b = a ^ n) (hn : n ≤ N) :
    a ^ (N + 1) * b = a ^ N := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  calc
    a ^ (n + r + 1) * b = a ^ (r + (n + 1)) * b := by
      rw [Nat.add_assoc, Nat.add_left_comm n r 1]
    _ = a ^ r * (a ^ (n + 1) * b) := by rw [pow_add, mul_assoc]
    _ = a ^ r * a ^ n := by rw [h]
    _ = a ^ (n + r) := by rw [← pow_add, Nat.add_comm r n]

private theorem drazinInverse_unique {M : Type w} [Monoid M] {a b c : M}
    (hab : Commute a b) (hb : b * a * b = b)
    (hbn : ∃ n : ℕ, a ^ (n + 1) * b = a ^ n)
    (hac : Commute a c) (hc : c * a * c = c)
    (hcn : ∃ n : ℕ, a ^ (n + 1) * c = a ^ n) : b = c := by
  obtain ⟨n, hn⟩ := hbn
  obtain ⟨m, hm⟩ := hcn
  let N := max n m
  have hbN : a ^ (N + 1) * b = a ^ N :=
    pow_succ_mul_eq_of_le hn (Nat.le_max_left n m)
  have hcN : a ^ (N + 1) * c = a ^ N :=
    pow_succ_mul_eq_of_le hm (Nat.le_max_right n m)
  have hb_abs : b ^ (N + 1) * a ^ N = b :=
    pow_succ_mul_pow_eq_of_outer_inverse hab hb N
  have hc_abs : a ^ N * c ^ (N + 1) = c :=
    (hac.pow_pow N (N + 1)).eq.trans
      (pow_succ_mul_pow_eq_of_outer_inverse hac hc N)
  -- Compare through the ordered product `b * a * c`, without commuting `b` and `c`.
  calc
    b = b ^ (N + 1) * a ^ N := hb_abs.symm
    _ = b ^ (N + 1) * (a ^ (N + 1) * c) := by rw [hcN]
    _ = (b ^ (N + 1) * a ^ N) * a * c := by
      rw [pow_succ a N]
      simp only [mul_assoc]
    _ = b * a * c := by rw [hb_abs]
    _ = b * a * (a ^ N * c ^ (N + 1)) := by rw [hc_abs]
    _ = (b * a ^ (N + 1)) * c ^ (N + 1) := by
      rw [pow_succ' a N]
      simp only [mul_assoc]
    _ = a ^ N * c ^ (N + 1) := by rw [← (hab.pow_left (N + 1)).eq, hbN]
    _ = c := hc_abs

variable {C : Type u} [Category.{v} C] {X : C}

open Limits

private theorem biprod_map_mul [HasZeroMorphisms C] {K I : C}
    [HasBinaryBiproduct K I] (a a' : End K) (b b' : End I) :
    End.of (biprod.map a b) * End.of (biprod.map a' b') =
      End.of (biprod.map (a * a') (b * b')) := by
  apply biprod.hom_ext' <;>
    simp only [End.mul_def, Category.assoc, biprod.inl_map, biprod.inl_map_assoc,
      biprod.inr_map, biprod.inr_map_assoc]

private theorem biprod_map_pow [HasZeroMorphisms C] {K I : C}
    [HasBinaryBiproduct K I] (a : End K) (b : End I) (n : ℕ) :
    End.of (biprod.map a b) ^ n =
      End.of (biprod.map (a ^ n) (b ^ n)) := by
  induction n with
  | zero =>
    apply biprod.hom_ext' <;>
      simp only [pow_zero, End.one_def, Category.comp_id, Category.id_comp,
        biprod.inl_map, biprod.inr_map]
  | succ n ih =>
    simp only [pow_succ, ih, biprod_map_mul]

private theorem exists_drazinInverse [Abelian C] [IsNoetherianObject X] [IsArtinianObject X]
    (f : End X) :
    ∃ g : End X, Commute f g ∧ g * f * g = g ∧
      ∃ n : ℕ, f ^ (n + 1) * g = f ^ n := by
  classical
  -- Intersect the two tails first, then take a positive exponent in their common tail.
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 <|
    (eventually_isIso_biprod_desc_kernel_ι_image_ι_pow f).and
      (eventually_isIso_imagePowRestriction f)
  let N := N₀ + 1
  obtain ⟨hδ, hb⟩ := hN₀ N (Nat.le_succ N₀)
  let K := kernel (f ^ N)
  let I := image (f ^ N)
  let a : End K := kernelPowRestriction f N
  let b : End I := imagePowRestriction f N
  let δ : K ⊞ I ⟶ X := biprod.desc (kernel.ι (f ^ N)) (image.ι (f ^ N))
  let _ : IsIso δ := hδ
  let _ : IsIso b := hb
  let Δ : K ⊞ I ≅ X := asIso δ
  let A : End (K ⊞ I) := biprod.map a b
  let D : End (K ⊞ I) := biprod.map 0 (CategoryTheory.inv b)
  have hAδ : A ≫ Δ.hom = Δ.hom ≫ f := powRestriction_biprod_desc f N
  have hA : Δ.conj A = f := by
    rw [Iso.conj_apply, hAδ, Iso.inv_hom_id_assoc]
  have ha : a ^ N = 0 := kernelPowRestriction_pow_eq_zero f N
  have hbc : b * End.of (CategoryTheory.inv b) = 1 := by
    simp only [End.mul_def, End.one_def, IsIso.inv_hom_id]
  have hcb : End.of (CategoryTheory.inv b) * b = 1 := by
    simp only [End.mul_def, End.one_def, IsIso.hom_inv_id]
  have hAD : A * D = D * A := by
    dsimp only [A, D]
    rw [biprod_map_mul, biprod_map_mul]
    simp only [mul_zero, zero_mul, hbc, hcb]
  have hDAD : D * A * D = D := by
    dsimp only [A, D]
    rw [biprod_map_mul, biprod_map_mul]
    simp only [zero_mul, mul_zero, hcb, one_mul]
  have hbpow : b ^ (N + 1) * End.of (CategoryTheory.inv b) = b ^ N := by
    rw [pow_succ, mul_assoc, hbc, mul_one]
  have hpow : A ^ (N + 1) * D = A ^ N := by
    dsimp only [A, D]
    rw [biprod_map_pow, biprod_map_mul, biprod_map_pow, mul_zero, hbpow, ha]
  refine ⟨Δ.conj D, ?_, ?_, N, ?_⟩
  · change f * Δ.conj D = Δ.conj D * f
    calc
      f * Δ.conj D = Δ.conj (A * D) := by rw [map_mul, hA]
      _ = Δ.conj (D * A) := congrArg Δ.conj hAD
      _ = Δ.conj D * f := by rw [map_mul, hA]
  · calc
      Δ.conj D * f * Δ.conj D = Δ.conj (D * A * D) := by
        simp only [map_mul, hA]
      _ = Δ.conj D := congrArg Δ.conj hDAD
  · calc
      f ^ (N + 1) * Δ.conj D = Δ.conj (A ^ (N + 1) * D) := by
        simp only [map_mul, Iso.conj_pow, hA]
      _ = Δ.conj (A ^ N) := congrArg Δ.conj hpow
      _ = f ^ N := by rw [Iso.conj_pow, hA]

/-- The Drazin inverse of an endomorphism of a Noetherian and Artinian object. -/
noncomputable def drazinInverse [Abelian C] [IsNoetherianObject X] [IsArtinianObject X]
    (f : End X) : End X :=
  Classical.choose (show ∃ g : End X, Commute f g ∧ g * f * g = g ∧
    ∃ n : ℕ, f ^ (n + 1) * g = f ^ n from by exact exists_drazinInverse f)

private theorem drazinInverse_spec [Abelian C] [IsNoetherianObject X] [IsArtinianObject X]
    (f : End X) :
    Commute f (drazinInverse f) ∧
      drazinInverse f * f * drazinInverse f = drazinInverse f ∧
      ∃ n : ℕ, f ^ (n + 1) * drazinInverse f = f ^ n := by
  simpa only [drazinInverse] using Classical.choose_spec (exists_drazinInverse f)

/-- An endomorphism commutes with its Drazin inverse. -/
theorem commute_drazinInverse [Abelian C] [IsNoetherianObject X] [IsArtinianObject X]
    (f : End X) : Commute f (drazinInverse f) := by
  exact (drazinInverse_spec f).1

/-- The Drazin inverse is an outer inverse of the original endomorphism. -/
theorem drazinInverse_mul_self_mul [Abelian C] [IsNoetherianObject X] [IsArtinianObject X]
    (f : End X) :
    drazinInverse f * f * drazinInverse f = drazinInverse f := by
  exact (drazinInverse_spec f).2.1

/-- The Drazin inverse is an outer inverse under categorical composition. -/
@[simp]
theorem drazinInverse_comp_self_comp [Abelian C] [IsNoetherianObject X] [IsArtinianObject X]
    (f : End X) :
    drazinInverse f ≫ f ≫ drazinInverse f = drazinInverse f := by
  simpa only [End.mul_def, Category.assoc] using drazinInverse_mul_self_mul f

/-- Some power of an endomorphism is recovered by multiplying the next power
by its Drazin inverse. The exponent is allowed to be zero. -/
theorem exists_pow_succ_mul_drazinInverse [Abelian C] [IsNoetherianObject X] [IsArtinianObject X]
    (f : End X) :
    ∃ n : ℕ, f ^ (n + 1) * drazinInverse f = f ^ n := by
  exact (drazinInverse_spec f).2.2

/-- An endomorphism equals the Drazin inverse precisely when it satisfies the
commutation, outer-inverse and eventual-power equations. -/
theorem eq_drazinInverse_iff [Abelian C] [IsNoetherianObject X] [IsArtinianObject X]
    (f g : End X) :
    g = drazinInverse f ↔
      Commute f g ∧ g * f * g = g ∧ ∃ n : ℕ, f ^ (n + 1) * g = f ^ n := by
  constructor
  · rintro rfl
    exact drazinInverse_spec f
  · rintro ⟨hfg, hg, hn⟩
    exact drazinInverse_unique hfg hg hn (commute_drazinInverse f)
      (drazinInverse_mul_self_mul f) (exists_pow_succ_mul_drazinInverse f)

/-- Every endomorphism of a Noetherian and Artinian object has a unique Drazin
inverse. Uniqueness concerns the inverse, not the exponent in the power equation.
The inverse terminology is that of M. P. Drazin's
"Pseudo-Inverses in Associative Rings and Semigroups" (1958); existence here
follows from the Fitting decomposition. -/
theorem existsUnique_drazinInverse [Abelian C] [IsNoetherianObject X] [IsArtinianObject X]
    (f : End X) :
    ∃! g : End X, Commute f g ∧ g * f * g = g ∧
      ∃ n : ℕ, f ^ (n + 1) * g = f ^ n := by
  refine ⟨drazinInverse f, ?_, ?_⟩
  · exact ⟨commute_drazinInverse f, drazinInverse_mul_self_mul f,
      exists_pow_succ_mul_drazinInverse f⟩
  · intro g hg
    exact (eq_drazinInverse_iff f g).2 hg

/-- The Drazin inverse is zero exactly when the endomorphism is nilpotent. -/
theorem drazinInverse_eq_zero_iff [Abelian C] [IsNoetherianObject X] [IsArtinianObject X]
    (f : End X) :
    drazinInverse f = 0 ↔ IsNilpotent f := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := exists_pow_succ_mul_drazinInverse f
    exact ⟨n, by simpa only [h, mul_zero] using hn.symm⟩
  · rintro ⟨n, hn⟩
    symm
    refine (eq_drazinInverse_iff f 0).2 ⟨?_, ?_, n, ?_⟩
    · change f * 0 = 0 * f
      simp only [mul_zero, zero_mul]
    · simp only [zero_mul, mul_zero]
    · simpa only [mul_zero] using hn.symm

/-- The zero endomorphism has zero Drazin inverse, including on a zero object. -/
@[simp]
theorem drazinInverse_zero [Abelian C] [IsNoetherianObject X] [IsArtinianObject X] :
    drazinInverse (0 : End X) = 0 := by
  exact (drazinInverse_eq_zero_iff (0 : End X)).2 ⟨1, pow_one _⟩

/-- For an isomorphism, the Drazin inverse is its ordinary categorical inverse. -/
theorem drazinInverse_eq_inv [Abelian C] [IsNoetherianObject X] [IsArtinianObject X]
    (f : End X) [IsIso f] :
    drazinInverse f = CategoryTheory.inv f := by
  have hfi : f * End.of (CategoryTheory.inv f) = 1 := by
    simpa only [mul_def, one_def] using CategoryTheory.IsIso.inv_hom_id f
  have hif : End.of (CategoryTheory.inv f) * f = 1 := by
    simpa only [mul_def, one_def] using CategoryTheory.IsIso.hom_inv_id f
  symm
  refine (eq_drazinInverse_iff f (CategoryTheory.inv f)).2 ⟨?_, ?_, 0, ?_⟩
  · exact (commute_iff_eq _ _).2 (hfi.trans hif.symm)
  · rw [hif, one_mul]
  · simpa only [Nat.zero_add, pow_one, pow_zero] using hfi

/-- An idempotent endomorphism is its own Drazin inverse. -/
theorem drazinInverse_of_isIdempotentElem [Abelian C] [IsNoetherianObject X] [IsArtinianObject X]
    (f : End X) (hf : IsIdempotentElem f) :
    drazinInverse f = f := by
  symm
  refine (eq_drazinInverse_iff f f).2 ⟨Commute.refl f, ?_, 1, ?_⟩
  · rw [hf.eq, hf.eq]
  · rw [hf.pow_succ_eq 1, pow_one, hf.eq]

/-- Multiplying an endomorphism by its Drazin inverse gives an idempotent. -/
theorem isIdempotentElem_mul_drazinInverse [Abelian C] [IsNoetherianObject X] [IsArtinianObject X]
    (f : End X) :
    IsIdempotentElem (f * drazinInverse f) := by
  change (f * drazinInverse f) * (f * drazinInverse f) = f * drazinInverse f
  calc
    (f * drazinInverse f) * (f * drazinInverse f) =
        f * (drazinInverse f * f * drazinInverse f) := by simp only [mul_assoc]
    _ = f * drazinInverse f := by rw [drazinInverse_mul_self_mul]

/-- An intertwining morphism also intertwines the corresponding Drazin inverses. -/
@[reassoc]
theorem drazinInverse_comp_eq_comp_drazinInverse [Abelian C] {Y : C}
    [IsNoetherianObject X] [IsArtinianObject X]
    [IsNoetherianObject Y] [IsArtinianObject Y]
    (f : End X) (g : End Y) (p : X ⟶ Y) (h : f ≫ p = p ≫ g) :
    drazinInverse f ≫ p = p ≫ drazinInverse g := by
  let b : End X := drazinInverse f
  let c : End Y := drazinInverse g
  have hfb : Commute f b := commute_drazinInverse f
  have hgc : Commute g c := commute_drazinInverse g
  obtain ⟨n, hn⟩ := exists_pow_succ_mul_drazinInverse f
  obtain ⟨m, hm⟩ := exists_pow_succ_mul_drazinInverse g
  let N := max n m
  have hfN : b ≫ f ^ (N + 1) = f ^ N := by
    simpa only [End.mul_def] using
      (pow_succ_mul_eq_of_le hn (Nat.le_max_left n m))
  have hgN : (g ^ (N + 1)) ≫ c = g ^ N := by
    have hcN : g ^ (N + 1) * c = g ^ N :=
      pow_succ_mul_eq_of_le hm (Nat.le_max_right n m)
    simpa only [End.mul_def] using ((hgc.pow_left (N + 1)).eq.symm.trans hcN)
  have hb_abs : (b ^ (N + 1)) ≫ f ^ N = b := by
    have hb : b ^ (N + 1) * f ^ N = b :=
      pow_succ_mul_pow_eq_of_outer_inverse hfb (drazinInverse_mul_self_mul f) N
    simpa only [End.mul_def] using ((hfb.pow_pow N (N + 1)).eq.trans hb)
  have hc_abs : (g ^ N) ≫ c ^ (N + 1) = c := by
    simpa only [End.mul_def] using
      (pow_succ_mul_pow_eq_of_outer_inverse hgc (drazinInverse_mul_self_mul g) N)
  have hpN := pow_comp_eq_comp_pow f g p h N
  have hpS := pow_comp_eq_comp_pow f g p h (N + 1)
  change b ≫ p = p ≫ c
  -- Compare through `b ≫ f ≫ p ≫ c`, without commuting across the mixed Hom.
  calc
    b ≫ p = (b ^ (N + 1)) ≫ (f ^ N) ≫ p := by
      rw [← Category.assoc, hb_abs]
    _ = (b ^ (N + 1)) ≫ p ≫ g ^ N := by rw [hpN]
    _ = (b ^ (N + 1)) ≫ p ≫ ((g ^ (N + 1)) ≫ c) := by rw [hgN]
    _ = (b ^ (N + 1)) ≫ (p ≫ g ^ (N + 1)) ≫ c := by
      simp only [Category.assoc]
    _ = (b ^ (N + 1)) ≫ ((f ^ (N + 1)) ≫ p) ≫ c := by rw [hpS]
    _ = ((b ^ (N + 1)) ≫ f ^ N) ≫ f ≫ p ≫ c := by
      simp only [pow_succ' f N, End.mul_def, Category.assoc]
    _ = b ≫ f ≫ p ≫ c := by rw [hb_abs]
    _ = b ≫ f ≫ p ≫ ((g ^ N) ≫ c ^ (N + 1)) := by rw [hc_abs]
    _ = b ≫ f ≫ (p ≫ g ^ N) ≫ c ^ (N + 1) := by
      simp only [Category.assoc]
    _ = b ≫ f ≫ ((f ^ N) ≫ p) ≫ c ^ (N + 1) := by rw [hpN]
    _ = (b ≫ f ^ (N + 1)) ≫ p ≫ c ^ (N + 1) := by
      simp only [pow_succ f N, End.mul_def, Category.assoc]
    _ = ((f ^ N) ≫ p) ≫ c ^ (N + 1) := by rw [hfN, Category.assoc]
    _ = p ≫ (g ^ N) ≫ c ^ (N + 1) := by rw [hpN, Category.assoc]
    _ = p ≫ c := by rw [hc_abs]

/-- The Drazin inverse commutes with every endomorphism commuting with the original
endomorphism. -/
theorem _root_.Commute.drazinInverse_left [Abelian C] [IsNoetherianObject X]
    [IsArtinianObject X] {f h : End X} (hfh : Commute f h) :
    Commute (drazinInverse f) h := by
  apply (commute_iff_eq _ _).2
  simpa only [End.mul_def] using
    (drazinInverse_comp_eq_comp_drazinInverse f f h
      (by simpa only [End.mul_def] using hfh.eq.symm)).symm

/-- Drazin inversion commutes with every natural power, including the zeroth power. -/
@[simp]
theorem drazinInverse_pow [Abelian C] [IsNoetherianObject X] [IsArtinianObject X]
    (f : End X) (n : ℕ) :
    drazinInverse (f ^ n) = drazinInverse f ^ n := by
  have h : Commute f (drazinInverse f) := commute_drazinInverse f
  symm
  refine (eq_drazinInverse_iff (f ^ n) (drazinInverse f ^ n)).2
    ⟨h.pow_pow n n, ?_, ?_⟩
  · rw [← h.symm.mul_pow n,
      ← ((Commute.refl (drazinInverse f)).mul_left h).mul_pow n,
      drazinInverse_mul_self_mul]
  · obtain ⟨k, hk⟩ := exists_pow_succ_mul_drazinInverse f
    refine ⟨k, ?_⟩
    calc
      (f ^ n) ^ (k + 1) * drazinInverse f ^ n =
          (f ^ (k + 1)) ^ n * drazinInverse f ^ n := by
        rw [pow_right_comm f n (k + 1)]
      _ = (f ^ (k + 1) * drazinInverse f) ^ n :=
        ((h.pow_left (k + 1)).mul_pow n).symm
      _ = (f ^ k) ^ n := by rw [hk]
      _ = (f ^ n) ^ k := pow_right_comm f k n

/-- The Drazin inverse of a product of commuting endomorphisms is the product
of their Drazin inverses. -/
theorem _root_.Commute.drazinInverse_mul [Abelian C] [IsNoetherianObject X]
    [IsArtinianObject X] {f g : End X} (hfg : Commute f g) :
    End.drazinInverse (f * g) = End.drazinInverse f * End.drazinInverse g := by
  let b : End X := drazinInverse f
  let d : End X := drazinInverse g
  have hfb : Commute f b := commute_drazinInverse f
  have hgd : Commute g d := commute_drazinInverse g
  have hbg : Commute b g := hfg.drazinInverse_left
  have hfd : Commute f d := hfg.symm.drazinInverse_left.symm
  have hbd : Commute b d := hfd.drazinInverse_left
  have hb : b * f * b = b := drazinInverse_mul_self_mul f
  have hd : d * g * d = d := drazinInverse_mul_self_mul g
  symm
  refine (eq_drazinInverse_iff (f * g) (b * d)).2 ⟨?_, ?_, ?_⟩
  · exact (hfb.mul_right hfd).mul_left (hbg.symm.mul_right hgd)
  · calc
      (b * d) * (f * g) * (b * d) =
          (b * f) * (d * g) * (b * d) := by
        rw [hfd.symm.mul_mul_mul_comm b g]
      _ = (b * f * b) * (d * g * d) :=
        (hbd.mul_right hbg).symm.mul_mul_mul_comm (b * f) d
      _ = b * d := by rw [hb, hd]
  · obtain ⟨n, hn⟩ := exists_pow_succ_mul_drazinInverse f
    obtain ⟨m, hm⟩ := exists_pow_succ_mul_drazinInverse g
    let N := max n m
    have hfN : f ^ (N + 1) * b = f ^ N :=
      pow_succ_mul_eq_of_le hn (Nat.le_max_left n m)
    have hgN : g ^ (N + 1) * d = g ^ N :=
      pow_succ_mul_eq_of_le hm (Nat.le_max_right n m)
    refine ⟨N, ?_⟩
    calc
      (f * g) ^ (N + 1) * (b * d) =
          (f ^ (N + 1) * g ^ (N + 1)) * (b * d) := by
        rw [hfg.mul_pow (N + 1)]
      _ = (f ^ (N + 1) * b) * (g ^ (N + 1) * d) :=
        (hbg.symm.pow_left (N + 1)).mul_mul_mul_comm (f ^ (N + 1)) d
      _ = f ^ N * g ^ N := by rw [hfN, hgN]
      _ = (f * g) ^ N := (hfg.mul_pow N).symm

/-- Double Drazin inversion recovers the group part `f * End.drazinInverse f * f`. -/
theorem drazinInverse_drazinInverse [Abelian C] [IsNoetherianObject X] [IsArtinianObject X]
    (f : End X) :
    End.drazinInverse (End.drazinInverse f) = f * End.drazinInverse f * f := by
  let b : End X := drazinInverse f
  have hfb : Commute f b := commute_drazinInverse f
  have hb : b * f * b = b := drazinInverse_mul_self_mul f
  symm
  refine (eq_drazinInverse_iff b (f * b * f)).2 ⟨?_, ?_, 1, ?_⟩
  · exact (hfb.symm.mul_right (Commute.refl b)).mul_right hfb.symm
  · calc
      (f * b * f) * b * (f * b * f) =
          f * (b * f * b) * (f * b * f) := by simp only [mul_assoc]
      _ = f * b * (f * b * f) := by rw [hb]
      _ = f * (b * f * b) * f := by simp only [mul_assoc]
      _ = f * b * f := by rw [hb]
  · have hbbf : b ^ (1 + 1) * f = b := by
      simpa only [pow_one] using
        (pow_succ_mul_pow_eq_of_outer_inverse hfb hb 1)
    calc
      b ^ (1 + 1) * (f * b * f) =
          (b ^ (1 + 1) * f) * b * f := by simp only [mul_assoc]
      _ = b * b * f := by rw [hbbf]
      _ = b * f * b := hfb.symm.right_comm b
      _ = b ^ 1 := by rw [hb, pow_one]

/-- Multiplicative maps between endomorphism monoids of Noetherian and Artinian
objects preserve Drazin inverses; preservation of the identity is not required. -/
@[simp]
theorem map_drazinInverse {D : Type u'} [Category.{v'} D] [Abelian C] [Abelian D]
    {Y : D} [IsNoetherianObject X] [IsArtinianObject X]
    [IsNoetherianObject Y] [IsArtinianObject Y]
    {Φ : Type w} [FunLike Φ (End X) (End Y)] [MulHomClass Φ (End X) (End Y)]
    (φ : Φ) (f : End X) :
    φ (drazinInverse f) = drazinInverse (φ f) := by
  refine (eq_drazinInverse_iff (φ f) (φ (drazinInverse f))).2 ⟨?_, ?_, ?_⟩
  · exact (commute_drazinInverse f).map φ
  · simpa only [map_mul] using congrArg φ (drazinInverse_mul_self_mul f)
  · obtain ⟨n, hn⟩ := exists_pow_succ_mul_drazinInverse f
    -- Raise the witness so that both powers are positive before applying the map.
    have hn' : f ^ (n + 1 + 1) * drazinInverse f = f ^ (n + 1) :=
      pow_succ_mul_eq_of_le hn (Nat.le_succ n)
    have hpow (k : ℕ) : φ (f ^ (k + 1)) = (φ f) ^ (k + 1) := by
      induction k with
      | zero => simp only [Nat.zero_add, pow_one]
      | succ k ih =>
        calc
          φ (f ^ (k + 1 + 1)) = φ (f ^ (k + 1)) * φ f := by
            rw [pow_succ, map_mul]
          _ = (φ f) ^ (k + 1) * φ f := by rw [ih]
          _ = (φ f) ^ (k + 1 + 1) := (pow_succ (φ f) (k + 1)).symm
    refine ⟨n + 1, ?_⟩
    simpa only [map_mul, hpow] using congrArg φ hn'

end CategoryTheory.End

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- Functors preserve Drazin inverses whenever the source object and its image
are both Noetherian and Artinian. -/
@[simp]
theorem map_drazinInverse [Abelian C] [Abelian D] (F : C ⥤ D) {X : C}
    [IsNoetherianObject X] [IsArtinianObject X]
    [IsNoetherianObject (F.obj X)] [IsArtinianObject (F.obj X)]
    (f : End X) :
    F.map (End.drazinInverse f) = End.drazinInverse (F.map f) := by
  exact End.map_drazinInverse (F.mapEnd X) f

end CategoryTheory.Functor
