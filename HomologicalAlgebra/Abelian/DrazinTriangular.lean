/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.Abelian.ChainConditions
public import HomologicalAlgebra.Abelian.Drazin
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Preadditive.Biproducts

@[expose] public section

/-!
# Drazin inverses of triangular biproduct endomorphisms

For a unit endomorphism `f` and a nilpotent endomorphism `g`, the canonical Drazin
inverse of the triangular biproduct endomorphism with arbitrary component `h`
is given by a finite sum. The constructor `Biprod.ofComponents f h 0 g` uses
source-first order, so `h : X ⟶ Y` is its second component.

The formula allows every zero-power witness `g ^ n = 0`, including `n = 0`.
In that case `𝟙 Y = 0` and the sum is empty; neither `X` nor the ambient category
is required to be zero.

## References

This formulation reuses the canonical Drazin API of
`HomologicalAlgebra.Abelian.Drazin` and Mathlib's preadditive biproduct constructor
`CategoryTheory.Biprod.ofComponents`.
-/

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.End

private lemma eq_sum_range_pow_comp_of_eq_add_comp
    {C : Type u} [Category.{v} C] [Preadditive C] {X Y : C}
    (a : End X) (g : End Y) (c b : X ⟶ Y)
    (hb : b = c + (a ≫ b ≫ g)) (n : ℕ) (hg : g ^ n = 0) :
    b = ∑ i ∈ Finset.range n, (a ^ i) ≫ c ≫ (g ^ i) := by
  have h (m : ℕ) :
      b = (∑ i ∈ Finset.range m, (a ^ i) ≫ c ≫ (g ^ i)) +
        (a ^ m) ≫ b ≫ (g ^ m) := by
    induction m with
    | zero => simp
    | succ m ih =>
      calc
        b = (∑ i ∈ Finset.range m, (a ^ i) ≫ c ≫ (g ^ i)) +
            (a ^ m) ≫ b ≫ (g ^ m) := ih
        _ = (∑ i ∈ Finset.range m, (a ^ i) ≫ c ≫ (g ^ i)) +
            (a ^ m) ≫ (c + (a ≫ b ≫ g)) ≫ (g ^ m) := by rw [← hb]
        _ = ((∑ i ∈ Finset.range m, (a ^ i) ≫ c ≫ (g ^ i)) +
            (a ^ m) ≫ c ≫ (g ^ m)) +
            (a ^ (m + 1)) ≫ b ≫ (g ^ (m + 1)) := by
          simp only [pow_succ' a m, pow_succ g m, End.mul_def,
            Preadditive.comp_add, Preadditive.add_comp, Category.assoc, add_assoc]
        _ = (∑ i ∈ Finset.range (m + 1), (a ^ i) ≫ c ≫ (g ^ i)) +
            (a ^ (m + 1)) ≫ b ≫ (g ^ (m + 1)) := by
          rw [Finset.sum_range_succ]
  simpa [hg] using h n

variable {C : Type u} [Category.{v} C] [Abelian C]
  {X Y : C}
  [IsNoetherianObject X] [IsArtinianObject X]
  [IsNoetherianObject Y] [IsArtinianObject Y]

/-- The canonical Drazin inverse of a triangular biproduct endomorphism with unit
first diagonal component and nilpotent second diagonal component. The component
`h` is arbitrary, and the zero-power witness `n` need not be positive or minimal. -/
theorem drazinInverse_biprod_triangular
    (f : End X) (g : End Y) (h : X ⟶ Y)
    (hf : IsUnit f) (n : ℕ) (hg : g ^ n = 0) :
    drazinInverse (Biprod.ofComponents f h (0 : Y ⟶ X) g) =
      Biprod.ofComponents (drazinInverse f)
        (∑ i ∈ Finset.range n, ((drazinInverse f) ^ (i + 2)) ≫ h ≫ (g ^ i))
        (0 : Y ⟶ X) (0 : End Y) := by
  let T : End (X ⊞ Y) := Biprod.ofComponents f h (0 : Y ⟶ X) g
  let a : End X := drazinInverse f
  let k : End (X ⊞ Y) := drazinInverse T
  let b : X ⟶ Y := (biprod.inl : X ⟶ X ⊞ Y) ≫ k ≫ biprod.snd
  -- Naturality determines the first column and the second source row of the inverse.
  have hDg : drazinInverse g = 0 := (drazinInverse_eq_zero_iff g).2 ⟨n, hg⟩
  have hkfst : k ≫ biprod.fst = biprod.fst ≫ a :=
    drazinInverse_comp_eq_comp_drazinInverse T f biprod.fst (by simp [T])
  have hinrk : (biprod.inr : Y ⟶ X ⊞ Y) ≫ k = 0 := by
    have hgk := drazinInverse_comp_eq_comp_drazinInverse g T biprod.inr (by simp [T])
    simpa only [hDg, zero_comp] using hgk.symm
  have h11 : (biprod.inl : X ⟶ X ⊞ Y) ≫ k ≫ biprod.fst = a := by
    simpa only [← Category.assoc, biprod.inl_fst, Category.id_comp] using
      congrArg (fun p : X ⊞ Y ⟶ X => (biprod.inl : X ⟶ X ⊞ Y) ≫ p) hkfst
  have h21 : (biprod.inr : Y ⟶ X ⊞ Y) ≫ k ≫ biprod.fst = 0 := by
    rw [← Category.assoc, hinrk, zero_comp]
  have h22 : (biprod.inr : Y ⟶ X ⊞ Y) ≫ k ≫ biprod.snd = 0 := by
    rw [← Category.assoc, hinrk, zero_comp]
  have hk : k = Biprod.ofComponents a b (0 : Y ⟶ X) (0 : End Y) := by
    calc
      k = Biprod.ofComponents
          ((biprod.inl : X ⟶ X ⊞ Y) ≫ k ≫ biprod.fst) b
          ((biprod.inr : Y ⟶ X ⊞ Y) ≫ k ≫ biprod.fst)
          ((biprod.inr : Y ⟶ X ⊞ Y) ≫ k ≫ biprod.snd) :=
        (Biprod.ofComponents_eq k).symm
      _ = Biprod.ofComponents a b (0 : Y ⟶ X) (0 : End Y) := by rw [h11, h21, h22]
  -- The remaining component of canonical commutation is an affine recurrence.
  have hcomm : k ≫ T = T ≫ k := (commute_drazinInverse T).eq
  have hfb : f ≫ b = a ≫ h + b ≫ g := by
    have hc := congrArg (fun p : End (X ⊞ Y) =>
      (biprod.inl : X ⟶ X ⊞ Y) ≫ p ≫ biprod.snd) hcomm
    simpa [T, hk, Biprod.ofComponents_comp, Category.assoc,
      Preadditive.add_comp, Preadditive.comp_add, biprod.inl_fst,
      biprod.inl_snd, biprod.inr_fst, biprod.inr_snd] using hc.symm
  have haf : a ≫ f = 𝟙 X := by
    have hfIso : IsIso f := (isUnit_iff_isIso f).mp hf
    change drazinInverse f ≫ f = 𝟙 X
    rw [@drazinInverse_eq_inv _ _ _ _ _ _ f hfIso]
    exact @IsIso.inv_hom_id _ _ _ _ f hfIso
  have hb : b = (a ^ 2) ≫ h + a ≫ b ≫ g := by
    simpa only [Preadditive.comp_add, ← Category.assoc, haf,
      Category.id_comp, pow_two, End.mul_def] using
      congrArg (fun p : X ⟶ Y => a ≫ p) hfb
  have hbsum : b = ∑ i ∈ Finset.range n, (a ^ (i + 2)) ≫ h ≫ (g ^ i) := by
    calc
      b = ∑ i ∈ Finset.range n, (a ^ i) ≫ ((a ^ 2) ≫ h) ≫ (g ^ i) :=
        eq_sum_range_pow_comp_of_eq_add_comp a g ((a ^ 2) ≫ h) b hb n hg
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Nat.add_comm i 2, pow_add, End.mul_def]
        simp only [Category.assoc]
  change k = Biprod.ofComponents a
    (∑ i ∈ Finset.range n, (a ^ (i + 2)) ≫ h ≫ (g ^ i)) (0 : Y ⟶ X) (0 : End Y)
  rw [hk, hbsum]

/-- The stable-image projector of a triangular biproduct endomorphism is the
projection onto its first factor followed by the graph of the canonical off-diagonal
component. No intertwining condition is imposed on `h`. -/
theorem mul_drazinInverse_biprod_triangular
    (f : End X) (g : End Y) (h : X ⟶ Y)
    (hf : IsUnit f) (hg : IsNilpotent g) :
    End.of (CategoryTheory.Biprod.ofComponents f h (0 : Y ⟶ X) g) *
        drazinInverse
          (End.of (CategoryTheory.Biprod.ofComponents f h (0 : Y ⟶ X) g)) =
      End.of (biprod.fst ≫ biprod.lift (𝟙 X)
        (f ≫ (biprod.inl : X ⟶ X ⊞ Y) ≫
          drazinInverse
            (End.of (CategoryTheory.Biprod.ofComponents f h (0 : Y ⟶ X) g)) ≫
          (biprod.snd : X ⊞ Y ⟶ Y))) := by
  obtain ⟨n, hn⟩ := hg
  let T : End (X ⊞ Y) := Biprod.ofComponents f h (0 : Y ⟶ X) g
  let a : End X := drazinInverse f
  let k : End (X ⊞ Y) := drazinInverse T
  let b : X ⟶ Y := (biprod.inl : X ⟶ X ⊞ Y) ≫ k ≫ biprod.snd
  have hvalue : k = Biprod.ofComponents a
      (∑ i ∈ Finset.range n, (a ^ (i + 2)) ≫ h ≫ (g ^ i))
      (0 : Y ⟶ X) (0 : End Y) :=
    drazinInverse_biprod_triangular f g h hf n hn
  have hk : k = Biprod.ofComponents a b (0 : Y ⟶ X) (0 : End Y) := by
    dsimp only [b]
    simp only [hvalue, Biprod.ofComponents_snd, biprod.inl_fst_assoc, comp_zero, add_zero]
  have hfa : f ≫ a = 𝟙 X := by
    have hfIso : IsIso f := (isUnit_iff_isIso f).mp hf
    change f ≫ drazinInverse f = 𝟙 X
    rw [@drazinInverse_eq_inv _ _ _ _ _ _ f hfIso]
    exact @IsIso.hom_inv_id _ _ _ _ f hfIso
  change k ≫ T = biprod.fst ≫ biprod.lift (𝟙 X) (f ≫ b)
  calc
    k ≫ T = T ≫ k := (commute_drazinInverse T).eq
    _ = biprod.fst ≫ biprod.lift (𝟙 X) (f ≫ b) := by
      rw [hk]
      dsimp only [T]
      rw [Biprod.ofComponents_comp]
      apply biprod.hom_ext <;>
        simp only [Biprod.ofComponents_fst, Biprod.ofComponents_snd,
          comp_zero, zero_comp, add_zero, hfa, Category.assoc,
          biprod.lift_fst, biprod.lift_snd, Category.comp_id]

/-- The image of the stable-image projector of a triangular biproduct endomorphism
is isomorphic to its unit diagonal factor. The inverse embeds that factor as the
graph of the canonical off-diagonal component. -/
noncomputable def imageMulDrazinInverseBiprodTriangularIso
    (f : End X) (g : End Y) (h : X ⟶ Y)
    (hf : IsUnit f) (hg : IsNilpotent g) :
    image
      (End.asHom
        (End.of (CategoryTheory.Biprod.ofComponents f h (0 : Y ⟶ X) g) *
          drazinInverse
            (End.of (CategoryTheory.Biprod.ofComponents f h (0 : Y ⟶ X) g)))) ≅ X := by
  letI : StrongEpi (biprod.fst : X ⊞ Y ⟶ X) := by
    infer_instance
  letI : Mono (biprod.lift (𝟙 X)
      (f ≫ (biprod.inl : X ⟶ X ⊞ Y) ≫
        drazinInverse
          (End.of (CategoryTheory.Biprod.ofComponents f h (0 : Y ⟶ X) g)) ≫
        (biprod.snd : X ⊞ Y ⟶ Y))) := by
    exact biprod.mono_lift_of_mono_left _ _
  exact (image.isoStrongEpiMono
    (biprod.fst : X ⊞ Y ⟶ X)
    (biprod.lift (𝟙 X)
      (f ≫ (biprod.inl : X ⟶ X ⊞ Y) ≫
        drazinInverse
          (End.of (CategoryTheory.Biprod.ofComponents f h (0 : Y ⟶ X) g)) ≫
        (biprod.snd : X ⊞ Y ⟶ Y)))
    (by exact (mul_drazinInverse_biprod_triangular f g h hf hg).symm)).symm

/-- The image isomorphism is the image inclusion followed by the first biproduct
projection. -/
@[simp]
theorem imageMulDrazinInverseBiprodTriangularIso_hom
    (f : End X) (g : End Y) (h : X ⟶ Y)
    (hf : IsUnit f) (hg : IsNilpotent g) :
    (imageMulDrazinInverseBiprodTriangularIso f g h hf hg).hom =
      image.ι
          (End.asHom
            (End.of (CategoryTheory.Biprod.ofComponents f h (0 : Y ⟶ X) g) *
              drazinInverse
                (End.of (CategoryTheory.Biprod.ofComponents f h (0 : Y ⟶ X) g)))) ≫
        (biprod.fst : X ⊞ Y ⟶ X) := by
  have hi :
      (imageMulDrazinInverseBiprodTriangularIso f g h hf hg).hom ≫
          biprod.lift (𝟙 X)
            (f ≫ (biprod.inl : X ⟶ X ⊞ Y) ≫
              drazinInverse
                (End.of (CategoryTheory.Biprod.ofComponents f h (0 : Y ⟶ X) g)) ≫
              (biprod.snd : X ⊞ Y ⟶ Y)) =
        image.ι
          (End.asHom
            (End.of (CategoryTheory.Biprod.ofComponents f h (0 : Y ⟶ X) g) *
              drazinInverse
                (End.of (CategoryTheory.Biprod.ofComponents f h (0 : Y ⟶ X) g)))) := by
    simp only [imageMulDrazinInverseBiprodTriangularIso, Iso.symm_hom,
      image.isoStrongEpiMono_inv_comp_mono]
  simpa only [Category.assoc, biprod.lift_fst, Category.comp_id] using
    congrArg (fun k => k ≫ (biprod.fst : X ⊞ Y ⟶ X)) hi

/-- The inverse image isomorphism, followed by the image inclusion, is the graph
of the canonical off-diagonal component. -/
@[reassoc]
theorem imageMulDrazinInverseBiprodTriangularIso_inv_ι
    (f : End X) (g : End Y) (h : X ⟶ Y)
    (hf : IsUnit f) (hg : IsNilpotent g) :
    (imageMulDrazinInverseBiprodTriangularIso f g h hf hg).inv ≫
        image.ι
          (End.asHom
            (End.of (CategoryTheory.Biprod.ofComponents f h (0 : Y ⟶ X) g) *
              drazinInverse
                (End.of (CategoryTheory.Biprod.ofComponents f h (0 : Y ⟶ X) g)))) =
      biprod.lift (𝟙 X)
        (f ≫ (biprod.inl : X ⟶ X ⊞ Y) ≫
          drazinInverse
            (End.of (CategoryTheory.Biprod.ofComponents f h (0 : Y ⟶ X) g)) ≫
          (biprod.snd : X ⊞ Y ⟶ Y)) := by
  simp only [imageMulDrazinInverseBiprodTriangularIso, Iso.symm_inv,
    image.isoStrongEpiMono_hom_comp_ι]

/-- The canonical factor through the projector image becomes the first biproduct
projection under the image isomorphism. -/
@[reassoc]
theorem factorThruImage_comp_imageMulDrazinInverseBiprodTriangularIso_hom
    (f : End X) (g : End Y) (h : X ⟶ Y)
    (hf : IsUnit f) (hg : IsNilpotent g) :
    factorThruImage
        (End.asHom
          (End.of (CategoryTheory.Biprod.ofComponents f h (0 : Y ⟶ X) g) *
            drazinInverse
              (End.of (CategoryTheory.Biprod.ofComponents f h (0 : Y ⟶ X) g)))) ≫
      (imageMulDrazinInverseBiprodTriangularIso f g h hf hg).hom =
        (biprod.fst : X ⊞ Y ⟶ X) := by
  rw [imageMulDrazinInverseBiprodTriangularIso_hom, ← Category.assoc, image.fac,
    mul_drazinInverse_biprod_triangular f g h hf hg]
  simp only [End.asHom, End.of, Category.assoc, biprod.lift_fst, Category.comp_id]

end CategoryTheory.End
