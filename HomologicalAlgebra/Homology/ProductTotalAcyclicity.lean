module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# Product totals of quadrant bicomplexes

The horizontal maps of the native bicomplex lower `p` and its commuting vertical maps
raise `r`. A total degree is `p-r`. Diagonals are unrestricted products, not the
coproducts underlying `HomologicalComplex.total`.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.QuadrantProductTotal

universe u

variable {R : Type u} [Ring R]

/-- A bicomplex with horizontal index `p` and vertical index `r`. -/
abbrev Bicomplex (R : Type u) [Ring R] :=
  HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.down ℕ)

/-- Indices `(r,p)` on the integral diagonal `p-r=k`. -/
abbrev Diag (k : ℤ) := {pr : ℕ × ℕ // (pr.2 : ℤ) - (pr.1 : ℤ) = k}

/-- The first row present on an integral diagonal. -/
def firstRow (k : ℤ) : ℕ := (-k).toNat

/-- The first column present on an integral diagonal. -/
def firstColumn (k : ℤ) : ℕ := k.toNat

/-- Enumerate a diagonal by its position after the first row. -/
def diagonalIndex (k : ℤ) (n : ℕ) : Diag k :=
  ⟨(firstRow k + n, firstColumn k + n), by
    dsimp [Diag, firstRow, firstColumn]
    omega⟩

/-- Enumerate the primitive coordinates corresponding to a target diagonal. -/
abbrev primitiveIndex (k : ℤ) (n : ℕ) : Diag (k + 1) :=
  ⟨(firstRow k + n, firstColumn k + n + 1), by
    dsimp [Diag, firstRow, firstColumn]
    omega⟩

theorem diagonalIndex_surjective (k : ℤ) (i : Diag k) :
    diagonalIndex k (i.1.1 - firstRow k) = i := by
  have hi := i.2
  apply Subtype.ext
  apply Prod.ext
  · dsimp [diagonalIndex, firstRow]
    omega
  · dsimp [diagonalIndex, firstRow, firstColumn]
    omega

theorem primitiveIndex_of_row (k : ℤ) (i : Diag (k + 1))
    (hi : firstRow k ≤ i.1.1) :
    primitiveIndex k (i.1.1 - firstRow k) = i := by
  have h := i.2
  apply Subtype.ext
  apply Prod.ext
  · dsimp [primitiveIndex]
    omega
  · dsimp [primitiveIndex, firstRow, firstColumn]
    dsimp [firstRow] at hi
    omega

/-- The genuine cycle-equation coordinate between two enumerated rows. -/
def cycleIndex (k : ℤ) (n : ℕ) : Diag (k - 1) :=
  ⟨(firstRow k + n + 1, firstColumn k + n), by
    dsimp [Diag, firstRow, firstColumn]
    omega⟩

/-- The unrestricted product of modules on one diagonal. -/
abbrev Product (K : Bicomplex R) (k : ℤ) :=
  ∀ i : Diag k, (K.X i.1.1).X i.1.2

/-- The module underlying one degree of the product total. -/
abbrev degree (K : Bicomplex R) (k : ℤ) : ModuleCat.{u} R :=
  ModuleCat.of R (Product K k)

/-- The horizontal source of the coordinate at `i`. -/
def horizontalIndex {k : ℤ} (i : Diag (k - 1)) : Diag k :=
  ⟨(i.1.1, i.1.2 + 1), by have hi := i.2; dsimp [Diag] at hi ⊢; omega⟩

/-- The vertical source when the output row is positive. -/
def verticalIndex {k : ℤ} (i : Diag (k - 1)) (hi : 0 < i.1.1) : Diag k :=
  ⟨(i.1.1 - 1, i.1.2), by have h := i.2; dsimp [Diag] at h ⊢; omega⟩

theorem cycleIndex_horizontal (k : ℤ) (n : ℕ) :
    horizontalIndex (cycleIndex k n) = diagonalIndex k (n + 1) := by
  apply Subtype.ext
  apply Prod.ext <;> dsimp [horizontalIndex, cycleIndex, diagonalIndex] <;> omega

theorem cycleIndex_vertical (k : ℤ) (n : ℕ)
    (h : 0 < (cycleIndex k n).1.1) :
    verticalIndex (cycleIndex k n) h = diagonalIndex k n := by
  apply Subtype.ext
  apply Prod.ext
  · dsimp [verticalIndex, cycleIndex, diagonalIndex]
  · rfl

def horizontal (K : Bicomplex R) (k : ℤ) (i : Diag (k - 1)) :
    Product K k →ₗ[R] (K.X i.1.1).X i.1.2 :=
  ((K.X i.1.1).d (i.1.2 + 1) i.1.2).hom ∘ₗ LinearMap.proj (horizontalIndex i)

def vertical (K : Bicomplex R) (k : ℤ) (i : Diag (k - 1)) :
    Product K k →ₗ[R] (K.X i.1.1).X i.1.2 :=
  if hi : 0 < i.1.1 then
    ((K.d (i.1.1 - 1) i.1.1).f i.1.2).hom ∘ₗ LinearMap.proj (verticalIndex i hi)
  else 0

/-- Coordinatewise horizontal component of the differential. -/
def horizontalMap (K : Bicomplex R) (k : ℤ) : Product K k →ₗ[R] Product K (k - 1) :=
  LinearMap.pi (horizontal K k)

/-- Coordinatewise vertical component, extended by zero at row zero. -/
def verticalMap (K : Bicomplex R) (k : ℤ) : Product K k →ₗ[R] Product K (k - 1) :=
  LinearMap.pi (vertical K k)

@[simp] theorem horizontalMap_apply (K : Bicomplex R) (k : ℤ)
    (x : Product K k) (i : Diag (k - 1)) :
    horizontalMap K k x i =
      (K.X i.1.1).d (i.1.2 + 1) i.1.2 (x (horizontalIndex i)) := by
  rfl

@[simp] theorem verticalMap_apply_zero (K : Bicomplex R) (k : ℤ)
    (x : Product K k) (i : Diag (k - 1)) (hi : i.1.1 = 0) :
    verticalMap K k x i = 0 := by
  simp [verticalMap, vertical, hi]

theorem verticalMap_apply_pos (K : Bicomplex R) (k : ℤ)
    (x : Product K k) (i : Diag (k - 1)) (hi : 0 < i.1.1) :
    verticalMap K k x i =
      (K.d (i.1.1 - 1) i.1.1).f i.1.2 (x (verticalIndex i hi)) := by
  simp [verticalMap, vertical, hi]
  rfl

/-- The two-term total differential; the integer sign works for negative degrees. -/
def differential (K : Bicomplex R) (k : ℤ) : Product K k →ₗ[R] Product K (k - 1) :=
  LinearMap.pi fun i => horizontal K k i + ((Int.negOnePow (k + 1) : ℤ) • vertical K k i)

theorem differential_eq (K : Bicomplex R) (k : ℤ) :
    differential K k = horizontalMap K k +
      (Int.negOnePow (k + 1) : ℤ) • verticalMap K k := by
  ext x i
  rfl

/-- At row zero, the vertical input is absent. -/
@[simp] theorem differential_apply_zero (K : Bicomplex R) (k : ℤ)
    (x : Product K k) (i : Diag (k - 1)) (hi : i.1.1 = 0) :
    differential K k x i = (K.X i.1.1).d (i.1.2 + 1) i.1.2 (x (horizontalIndex i)) := by
  simp [differential, horizontal, vertical, hi]
  rfl

/-- At positive rows, both horizontal and vertical terms are present. -/
theorem differential_apply_pos (K : Bicomplex R) (k : ℤ)
    (x : Product K k) (i : Diag (k - 1)) (hi : 0 < i.1.1) :
    differential K k x i =
      (K.X i.1.1).d (i.1.2 + 1) i.1.2 (x (horizontalIndex i)) +
        (Int.negOnePow (k + 1) : ℤ) •
          (K.d (i.1.1 - 1) i.1.1).f i.1.2 (x (verticalIndex i hi)) := by
  simp [differential, horizontal, vertical, hi]
  rfl

theorem horizontal_square (K : Bicomplex R) (k : ℤ) :
    horizontalMap K (k - 1) ∘ₗ horizontalMap K k = 0 := by
  ext x i
  change (K.X i.1.1).d (i.1.2 + 1) i.1.2
    ((K.X i.1.1).d (i.1.2 + 1 + 1) (i.1.2 + 1)
      (x (horizontalIndex (horizontalIndex i)))) = 0
  have hs := congrArg ModuleCat.Hom.hom
    ((K.X i.1.1).d_comp_d (i.1.2 + 1 + 1) (i.1.2 + 1) i.1.2)
  have hs' := congrArg (fun f => f (x (horizontalIndex (horizontalIndex i)))) hs
  change (K.X i.1.1).d (i.1.2 + 1) i.1.2
    ((K.X i.1.1).d (i.1.2 + 1 + 1) (i.1.2 + 1)
      (x (horizontalIndex (horizontalIndex i)))) = 0 at hs'
  exact hs'

theorem vertical_square (K : Bicomplex R) (k : ℤ) :
    verticalMap K (k - 1) ∘ₗ verticalMap K k = 0 := by
  ext x i
  change verticalMap K (k - 1) (verticalMap K k x) i = 0
  by_cases h0 : i.1.1 = 0
  · simp [verticalMap, vertical, h0]
  by_cases h1 : i.1.1 = 1
  · have h : 0 < i.1.1 := by omega
    have hz : (verticalIndex i h).1.1 = 0 := by dsimp [verticalIndex]; omega
    rw [verticalMap_apply_pos K (k - 1) _ i h]
    rw [verticalMap_apply_zero K k x (verticalIndex i h) hz]
    change ((K.d (i.1.1 - 1) i.1.1).f i.1.2).hom 0 = 0
    exact map_zero _
  have h : 0 < i.1.1 := by omega
  have hv : 0 < (verticalIndex i h).1.1 := by dsimp [verticalIndex]; omega
  rw [verticalMap_apply_pos K (k - 1) _ i h,
    verticalMap_apply_pos K k x (verticalIndex i h) hv]
  change (K.d (i.1.1 - 1) i.1.1).f i.1.2
    ((K.d ((i.1.1 - 1) - 1) (i.1.1 - 1)).f i.1.2
      (x (verticalIndex (verticalIndex i h) hv))) = 0
  have hs := K.d_f_comp_d_f ((i.1.1 - 1) - 1) (i.1.1 - 1) i.1.1 i.1.2
  have hs' := congrArg ModuleCat.Hom.hom hs
  have hs'' := congrArg (fun f => f (x (verticalIndex (verticalIndex i h) hv))) hs'
  change (K.d (i.1.1 - 1) i.1.1).f i.1.2
    ((K.d ((i.1.1 - 1) - 1) (i.1.1 - 1)).f i.1.2
      (x (verticalIndex (verticalIndex i h) hv))) = 0 at hs''
  exact hs''

theorem horizontal_vertical_comm (K : Bicomplex R) (k : ℤ) :
    horizontalMap K (k - 1) ∘ₗ verticalMap K k =
      verticalMap K (k - 1) ∘ₗ horizontalMap K k := by
  ext x i
  change horizontalMap K (k - 1) (verticalMap K k x) i =
    verticalMap K (k - 1) (horizontalMap K k x) i
  by_cases h0 : i.1.1 = 0
  · rw [horizontalMap_apply, verticalMap_apply_zero K k x (horizontalIndex i)
        (by simpa [horizontalIndex] using h0),
      verticalMap_apply_zero K (k - 1) _ i h0]
    change ((K.X i.1.1).d (i.1.2 + 1) i.1.2).hom 0 = 0
    exact map_zero _
  have h : 0 < i.1.1 := by omega
  have hh : 0 < (horizontalIndex i).1.1 := by dsimp [horizontalIndex]; omega
  rw [horizontalMap_apply, verticalMap_apply_pos K k x (horizontalIndex i) hh,
    verticalMap_apply_pos K (k - 1) _ i h,
    horizontalMap_apply K k x (verticalIndex i h)]
  have hs := K.d_comm (i.1.1 - 1) i.1.1 (i.1.2 + 1) i.1.2
  have hs' := congrArg ModuleCat.Hom.hom hs
  have hs'' := congrArg
    (fun f => f (x (verticalIndex (horizontalIndex i) hh))) hs'
  change (K.X i.1.1).d (i.1.2 + 1) i.1.2
    ((K.d (i.1.1 - 1) i.1.1).f (i.1.2 + 1)
      (x (verticalIndex (horizontalIndex i) hh))) =
    (K.d (i.1.1 - 1) i.1.1).f i.1.2
      ((K.X (i.1.1 - 1)).d (i.1.2 + 1) i.1.2
        (x (verticalIndex (horizontalIndex i) hh))) at hs''
  exact hs''

theorem differential_square (K : Bicomplex R) (k : ℤ) :
    differential K (k - 1) ∘ₗ differential K k = 0 := by
  have hs : (Int.negOnePow ((k - 1) + 1) : ℤ) =
      -(Int.negOnePow (k + 1) : ℤ) := by
    have h : (Int.negOnePow (k + 1) : ℤ) = -(Int.negOnePow k : ℤ) := by
      simpa using congrArg (fun unit : ℤˣ => (unit : ℤ)) (Int.negOnePow_succ k)
    rw [show k - 1 + 1 = k by omega]
    omega
  simp [differential_eq, LinearMap.add_comp, LinearMap.comp_add,
    LinearMap.smul_comp, LinearMap.comp_smul,
    horizontal_square, vertical_square, horizontal_vertical_comm]
  have hs' : (Int.negOnePow k : ℤ) = -(Int.negOnePow (k + 1) : ℤ) := by
    simpa only [show k - 1 + 1 = k by omega] using hs
  rw [hs']
  simp

/-- The native integer-indexed chain complex of unrestricted diagonal products. -/
def productTotal (K : Bicomplex R) :
    HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℤ) := by
  refine HomologicalComplex.mk (degree K) (fun i j => ?_) ?_ ?_
  · exact if h : j + 1 = i then by
        have hj : j = i - 1 := by omega
        subst j
        exact ModuleCat.ofHom (differential K i)
      else 0
  · intro i j h
    have hj : j + 1 ≠ i := by
      intro heq
      apply h
      exact heq
    simp [hj]
  · intro i j l hij hjl
    have hj : j = i - 1 := by dsimp [ComplexShape.down, ComplexShape.down'] at hij; omega
    have hl : l = j - 1 := by dsimp [ComplexShape.down, ComplexShape.down'] at hjl; omega
    subst l
    subst j
    have hc : ModuleCat.ofHom (differential K i) ≫
        ModuleCat.ofHom (differential K (i - 1)) = 0 := by
      rw [← ModuleCat.ofHom_comp, differential_square]
      rfl
    simp only [show i - 1 + 1 = i by omega,
      show i - 1 - 1 + 1 = i - 1 by omega]
    exact hc

/-- Coordinatewise map of diagonal products induced by a bicomplex morphism. -/
def mapDegree {K L : Bicomplex R} (φ : K ⟶ L) (k : ℤ) :
    Product K k →ₗ[R] Product L k :=
  LinearMap.pi fun i => ((φ.f i.1.1).f i.1.2).hom ∘ₗ LinearMap.proj i

@[simp] theorem mapDegree_apply {K L : Bicomplex R} (φ : K ⟶ L) (k : ℤ)
    (x : Product K k) (i : Diag k) :
    mapDegree φ k x i = (φ.f i.1.1).f i.1.2 (x i) := by
  rfl

theorem map_horizontal {K L : Bicomplex R} (φ : K ⟶ L) (k : ℤ) :
    horizontalMap L k ∘ₗ mapDegree φ k =
      mapDegree φ (k - 1) ∘ₗ horizontalMap K k := by
  ext x i
  change horizontalMap L k (mapDegree φ k x) i =
    mapDegree φ (k - 1) (horizontalMap K k x) i
  rw [horizontalMap_apply, mapDegree_apply, mapDegree_apply, horizontalMap_apply]
  have hs := congrArg ModuleCat.Hom.hom ((φ.f i.1.1).comm (i.1.2 + 1) i.1.2)
  have h := congrArg (fun f => f (x (horizontalIndex i))) hs
  change (L.X i.1.1).d (i.1.2 + 1) i.1.2
    ((φ.f i.1.1).f (i.1.2 + 1) (x (horizontalIndex i))) =
    (φ.f i.1.1).f i.1.2
      ((K.X i.1.1).d (i.1.2 + 1) i.1.2 (x (horizontalIndex i))) at h
  exact h

theorem map_vertical {K L : Bicomplex R} (φ : K ⟶ L) (k : ℤ) :
    verticalMap L k ∘ₗ mapDegree φ k =
      mapDegree φ (k - 1) ∘ₗ verticalMap K k := by
  ext x i
  change verticalMap L k (mapDegree φ k x) i =
    mapDegree φ (k - 1) (verticalMap K k x) i
  by_cases hz : i.1.1 = 0
  · rw [verticalMap_apply_zero L k _ i hz,
      mapDegree_apply φ (k - 1) _ i, verticalMap_apply_zero K k x i hz]
    change 0 = ((φ.f i.1.1).f i.1.2).hom 0
    exact (map_zero _).symm
  have hr : 0 < i.1.1 := by omega
  rw [verticalMap_apply_pos L k _ i hr, mapDegree_apply φ k x (verticalIndex i hr),
    mapDegree_apply φ (k - 1) _ i, verticalMap_apply_pos K k x i hr]
  have hs := congrArg ModuleCat.Hom.hom (HomologicalComplex₂.comm_f φ
    (i.1.1 - 1) i.1.1 i.1.2)
  have h := congrArg (fun f => f (x (verticalIndex i hr))) hs
  change (L.d (i.1.1 - 1) i.1.1).f i.1.2
    ((φ.f (i.1.1 - 1)).f i.1.2 (x (verticalIndex i hr))) =
    (φ.f i.1.1).f i.1.2
      ((K.d (i.1.1 - 1) i.1.1).f i.1.2 (x (verticalIndex i hr))) at h
  exact h

theorem map_differential {K L : Bicomplex R} (φ : K ⟶ L) (k : ℤ) :
    differential L k ∘ₗ mapDegree φ k =
      mapDegree φ (k - 1) ∘ₗ differential K k := by
  simp [differential_eq, LinearMap.add_comp, LinearMap.comp_add,
    LinearMap.smul_comp, LinearMap.comp_smul, map_horizontal, map_vertical]

@[simp] theorem productTotal_d (K : Bicomplex R) (k : ℤ) :
    (productTotal K).d k (k - 1) = ModuleCat.ofHom (differential K k) := by
  simp [productTotal, show k - 1 + 1 = k by omega]

/-- Horizontal source of a coordinate in a native differential. -/
def nextHorizontalIndex (i j : ℤ) (h : j = i - 1) (t : Diag j) : Diag i :=
  ⟨(t.1.1, t.1.2 + 1), by have ht := t.2; dsimp [Diag] at ht ⊢; omega⟩

/-- Vertical source of a positive-row coordinate in a native differential. -/
def nextVerticalIndex (i j : ℤ) (h : j = i - 1) (t : Diag j)
    (ht : 0 < t.1.1) : Diag i :=
  ⟨(t.1.1 - 1, t.1.2), by have hh := t.2; dsimp [Diag] at hh ⊢; omega⟩

@[simp] theorem productTotal_d_apply_zero (K : Bicomplex R) (i j : ℤ)
    (hj : j = i - 1) (x : Product K i) (t : Diag j) (ht : t.1.1 = 0) :
    (productTotal K).d i j x t =
      (K.X t.1.1).d (t.1.2 + 1) t.1.2 (x (nextHorizontalIndex i j hj t)) := by
  subst j
  rw [productTotal_d]
  change differential K i x t = _
  rw [differential_apply_zero K i x t ht]
  rfl

theorem productTotal_d_apply_pos (K : Bicomplex R) (i j : ℤ)
    (hj : j = i - 1) (x : Product K i) (t : Diag j) (ht : 0 < t.1.1) :
    (productTotal K).d i j x t =
      (K.X t.1.1).d (t.1.2 + 1) t.1.2 (x (nextHorizontalIndex i j hj t)) +
        (Int.negOnePow (i + 1) : ℤ) •
          (K.d (t.1.1 - 1) t.1.1).f t.1.2 (x (nextVerticalIndex i j hj t ht)) := by
  subst j
  rw [productTotal_d]
  change differential K i x t = _
  rw [differential_apply_pos K i x t ht]
  rfl

/-- A bicomplex morphism induces a coordinatewise chain map on product totals. -/
def productTotalMap {K L : Bicomplex R} (φ : K ⟶ L) :
    productTotal K ⟶ productTotal L where
  f k := ModuleCat.ofHom (mapDegree φ k)
  comm' i j hij := by
    have hj : j = i - 1 := by
      change j + 1 = i at hij
      omega
    subst j
    simp only [productTotal_d]
    apply ModuleCat.hom_ext
    change differential L i ∘ₗ mapDegree φ i =
      mapDegree φ (i - 1) ∘ₗ differential K i
    exact map_differential φ i

@[simp] theorem productTotalMap_f {K L : Bicomplex R} (φ : K ⟶ L) (k : ℤ) :
    (productTotalMap φ).f k = ModuleCat.ofHom (mapDegree φ k) := rfl

@[simp] theorem mapDegree_id (K : Bicomplex R) (k : ℤ) :
    mapDegree (𝟙 K) k = LinearMap.id := by
  ext x i
  rfl

@[simp] theorem mapDegree_comp {K L M : Bicomplex R} (φ : K ⟶ L) (ψ : L ⟶ M)
    (k : ℤ) :
    mapDegree (φ ≫ ψ) k = mapDegree ψ k ∘ₗ mapDegree φ k := by
  ext x i
  rfl

@[simp] theorem productTotalMap_id (K : Bicomplex R) :
    productTotalMap (𝟙 K) = 𝟙 (productTotal K) := by
  apply HomologicalComplex.Hom.ext
  funext k
  change ModuleCat.ofHom (mapDegree (𝟙 K) k) = 𝟙 _
  rw [mapDegree_id, ModuleCat.ofHom_id]

@[simp] theorem productTotalMap_comp {K L M : Bicomplex R}
    (φ : K ⟶ L) (ψ : L ⟶ M) :
    productTotalMap (φ ≫ ψ) = productTotalMap φ ≫ productTotalMap ψ := by
  apply HomologicalComplex.Hom.ext
  funext k
  change ModuleCat.ofHom (mapDegree (φ ≫ ψ) k) =
    ModuleCat.ofHom (mapDegree φ k) ≫ ModuleCat.ofHom (mapDegree ψ k)
  rw [mapDegree_comp, ← ModuleCat.ofHom_comp]

/-- Elementwise lifting at every horizontal position, including `p=0`. -/
theorem row_lift (K : Bicomplex R) (hrow : ∀ r : ℕ, (K.X r).Acyclic)
    (r p : ℕ) (z : (K.X r).X p)
    (hz : (K.X r).d p (p - 1) z = 0) :
    ∃ w : (K.X r).X (p + 1), (K.X r).d (p + 1) p w = z := by
  have hp : (ComplexShape.down ℕ).prev p = p + 1 := by
    apply ComplexShape.prev_eq'
    change p + 1 = p + 1
    rfl
  have hn : (ComplexShape.down ℕ).next p = p - 1 := by
    by_cases hp0 : p = 0
    · subst p
      apply ComplexShape.next_eq_self'
      intro j hj
      change j + 1 = 0 at hj
      omega
    · apply ComplexShape.next_eq'
      change p - 1 + 1 = p
      omega
  have he := (ShortComplex.moduleCat_exact_iff ((K.X r).sc p)).mp (hrow r p)
  change ∀ a : (K.X r).X p,
    (K.X r).d p ((ComplexShape.down ℕ).next p) a = 0 →
    ∃ b : (K.X r).X ((ComplexShape.down ℕ).prev p),
      (K.X r).d ((ComplexShape.down ℕ).prev p) p b = a at he
  rw [hp, hn] at he
  exact he z hz

theorem cycle_equation (K : Bicomplex R) (k : ℤ)
    (x : Product K k) (hx : differential K k x = 0)
    (i : Diag (k - 1)) (hi : 0 < i.1.1) :
    (K.X i.1.1).d (i.1.2 + 1) i.1.2 (x (horizontalIndex i)) =
      (Int.negOnePow k : ℤ) •
        (K.d (i.1.1 - 1) i.1.1).f i.1.2 (x (verticalIndex i hi)) := by
  have hc := congrFun hx i
  rw [differential_apply_pos K k x i hi] at hc
  change (K.X i.1.1).d (i.1.2 + 1) i.1.2 (x (horizontalIndex i)) +
    (Int.negOnePow (k + 1) : ℤ) •
      (K.d (i.1.1 - 1) i.1.1).f i.1.2 (x (verticalIndex i hi)) = 0 at hc
  have hs : (Int.negOnePow (k + 1) : ℤ) = -(Int.negOnePow k : ℤ) := by
    simpa using congrArg (fun unit : ℤˣ => (unit : ℤ)) (Int.negOnePow_succ k)
  rw [hs, neg_smul] at hc
  apply eq_of_sub_eq_zero
  simpa only [sub_eq_add_neg] using hc

theorem horizontal_at_zero (K : Bicomplex R) (r p : ℕ)
    (hp : p = 0) (z : (K.X r).X p) : (K.X r).d p (p - 1) z = 0 := by
  subst p
  have hs : (K.X r).d 0 0 = 0 :=
    (K.X r).shape 0 0 (by change ¬0 + 1 = 0; omega)
  rw [Nat.zero_sub, hs]
  rfl

theorem first_kernel (K : Bicomplex R) (k : ℤ)
    (x : Product K k) (hx : differential K k x = 0) :
    (K.X (firstRow k)).d (firstColumn k) (firstColumn k - 1)
      (x (diagonalIndex k 0)) = 0 := by
  cases k with
  | negSucc n =>
    exact horizontal_at_zero K (firstRow (Int.negSucc n))
      (firstColumn (Int.negSucc n)) rfl (x (diagonalIndex (Int.negSucc n) 0))
  | ofNat n =>
    cases n with
    | zero =>
      exact horizontal_at_zero K (firstRow 0) (firstColumn 0)
        rfl (x (diagonalIndex 0 0))
    | succ n =>
      let i : Diag ((Int.ofNat (n + 1)) - 1) := ⟨(0, n), by
        dsimp [Diag]
        omega⟩
      have h := congrFun hx i
      rw [differential_apply_zero K _ x i (by rfl)] at h
      exact h

theorem residual_kernel (K : Bicomplex R) (r p : ℕ)
    (s : ℤ) (current : (K.X r).X p) (following : (K.X (r + 1)).X (p + 1))
    (lift : (K.X r).X (p + 1))
    (hcycle : (K.X (r + 1)).d (p + 1) p following =
      s • (K.d r (r + 1)).f p current)
    (hinv : (K.d r (r + 1)).f p
      (current - (K.X r).d (p + 1) p lift) = 0) :
    (K.X (r + 1)).d (p + 1) p
      (following - s • (K.d r (r + 1)).f (p + 1) lift) = 0 := by
  have hc := congrArg ModuleCat.Hom.hom (K.d_comm r (r + 1) (p + 1) p)
  have hc' := congrArg (fun f => f lift) hc
  change (K.X (r + 1)).d (p + 1) p ((K.d r (r + 1)).f (p + 1) lift) =
    (K.d r (r + 1)).f p ((K.X r).d (p + 1) p lift) at hc'
  simp only [map_sub, map_zsmul, hcycle, hc']
  rw [← smul_sub, ← map_sub, hinv]
  simp

theorem vertical_square_apply (K : Bicomplex R) (r p : ℕ)
    (b : (K.X r).X p) :
    (K.d (r + 1) (r + 2)).f p ((K.d r (r + 1)).f p b) = 0 := by
  have hs := K.d_f_comp_d_f r (r + 1) (r + 2) p
  have hs' := congrArg ModuleCat.Hom.hom hs
  have hs'' := congrArg (fun f => f b) hs'
  change (K.d (r + 1) (r + 2)).f p ((K.d r (r + 1)).f p b) = 0 at hs''
  exact hs''

theorem cycle_equation_step (K : Bicomplex R) (k : ℤ)
    (x : Product K k) (hx : differential K k x = 0) (n : ℕ) :
    (K.X (firstRow k + n + 1)).d (firstColumn k + n + 1) (firstColumn k + n)
      (x (diagonalIndex k (n + 1))) =
        (Int.negOnePow k : ℤ) •
          (K.d (firstRow k + n) (firstRow k + n + 1)).f (firstColumn k + n)
            (x (diagonalIndex k n)) := by
  let i := cycleIndex k n
  have hi : 0 < i.1.1 := by dsimp [i, cycleIndex]; omega
  exact cycle_equation K k x hx i hi

/-- An elementwise horizontal lift with the invariant needed at the next row. -/
abbrev coordinate (K : Bicomplex R) (k : ℤ) (x : Product K k) (n : ℕ) :
    (K.X (firstRow k + n)).X (firstColumn k + n) :=
  x (diagonalIndex k n)

abbrev LiftState (K : Bicomplex R) (k : ℤ) (x : Product K k) (n : ℕ) :=
  {b : (K.X (firstRow k + n)).X (firstColumn k + n + 1) //
    (K.d (firstRow k + n) (firstRow k + n + 1)).f (firstColumn k + n)
      (coordinate K k x n -
        (K.X (firstRow k + n)).d (firstColumn k + n + 1)
          (firstColumn k + n) b) = 0}

theorem initialState_exists (K : Bicomplex R)
    (hrow : ∀ r : ℕ, (K.X r).Acyclic) (k : ℤ)
    (x : Product K k) (hx : differential K k x = 0) :
    ∃ b : LiftState K k x 0,
      (K.X (firstRow k)).d (firstColumn k + 1) (firstColumn k) b.1 =
        x (diagonalIndex k 0) := by
  obtain ⟨b, hb⟩ := row_lift K hrow (firstRow k) (firstColumn k)
    (x (diagonalIndex k 0)) (first_kernel K k x hx)
  refine ⟨⟨b, ?_⟩, hb⟩
  change (K.d (firstRow k) (firstRow k + 1)).f (firstColumn k)
    (coordinate K k x 0 -
      (K.X (firstRow k)).d (firstColumn k + 1) (firstColumn k) b) = 0
  rw [hb, sub_self]
  exact map_zero _

theorem nextState_exists (K : Bicomplex R)
    (hrow : ∀ r : ℕ, (K.X r).Acyclic) (k : ℤ)
    (x : Product K k) (hx : differential K k x = 0) (n : ℕ)
    (state : LiftState K k x n) :
    ∃ next : LiftState K k x (n + 1),
      (K.X (firstRow k + n + 1)).d (firstColumn k + n + 1 + 1)
          (firstColumn k + n + 1) next.1 =
        coordinate K k x (n + 1) -
          (Int.negOnePow k : ℤ) •
            (K.d (firstRow k + n) (firstRow k + n + 1)).f
              (firstColumn k + n + 1) state.1 := by
  let r := firstRow k + n
  let p := firstColumn k + n
  let s := (Int.negOnePow k : ℤ)
  have hc : (K.X (r + 1)).d (p + 1) p (coordinate K k x (n + 1)) =
      s • (K.d r (r + 1)).f p (coordinate K k x n) :=
    cycle_equation_step K k x hx n
  have hi : (K.d r (r + 1)).f p
      (coordinate K k x n - (K.X r).d (p + 1) p state.1) = 0 :=
    state.2
  have hz := residual_kernel K r p s (coordinate K k x n)
    (coordinate K k x (n + 1)) state.1 hc hi
  obtain ⟨next, hn⟩ := row_lift K hrow (r + 1) (p + 1)
    (coordinate K k x (n + 1) - s • (K.d r (r + 1)).f (p + 1) state.1) hz
  refine ⟨⟨next, ?_⟩, hn⟩
  change (K.d (r + 1) (r + 2)).f (p + 1)
    (coordinate K k x (n + 1) - (K.X (r + 1)).d (p + 2) (p + 1) next) = 0
  rw [hn]
  have ht : coordinate K k x (n + 1) -
      (coordinate K k x (n + 1) - s • (K.d r (r + 1)).f (p + 1) state.1) =
      s • (K.d r (r + 1)).f (p + 1) state.1 := by
    abel
  rw [ht, map_zsmul, vertical_square_apply]
  simp

/-- Successive elementwise lifts; these choices are not linear or natural in cycles. -/
noncomputable def liftStates (K : Bicomplex R)
    (hrow : ∀ r : ℕ, (K.X r).Acyclic) (k : ℤ)
    (x : Product K k) (hx : differential K k x = 0) (n : ℕ) :
    LiftState K k x n :=
  Nat.rec (Classical.choose (initialState_exists K hrow k x hx))
    (fun n state => Classical.choose (nextState_exists K hrow k x hx n state)) n

theorem liftStates_first (K : Bicomplex R)
    (hrow : ∀ r : ℕ, (K.X r).Acyclic) (k : ℤ)
    (x : Product K k) (hx : differential K k x = 0) :
    (K.X (firstRow k)).d (firstColumn k + 1) (firstColumn k)
      (liftStates K hrow k x hx 0).1 = x (diagonalIndex k 0) := by
  exact Classical.choose_spec (initialState_exists K hrow k x hx)

theorem liftStates_step (K : Bicomplex R)
    (hrow : ∀ r : ℕ, (K.X r).Acyclic) (k : ℤ)
    (x : Product K k) (hx : differential K k x = 0) (n : ℕ) :
    (K.X (firstRow k + n + 1)).d (firstColumn k + n + 1 + 1)
        (firstColumn k + n + 1) (liftStates K hrow k x hx (n + 1)).1 =
      coordinate K k x (n + 1) -
        (Int.negOnePow k : ℤ) •
          (K.d (firstRow k + n) (firstRow k + n + 1)).f
            (firstColumn k + n + 1) (liftStates K hrow k x hx n).1 := by
  exact Classical.choose_spec
    (nextState_exists K hrow k x hx n (liftStates K hrow k x hx n))

/-- Assemble all chosen lifts, setting every earlier (actual) primitive coordinate to zero. -/
noncomputable def primitive (K : Bicomplex R)
    (hrow : ∀ r : ℕ, (K.X r).Acyclic) (k : ℤ)
    (x : Product K k) (hx : differential K k x = 0) : Product K (k + 1) :=
  fun i => if h : firstRow k ≤ i.1.1 then
    (primitiveIndex_of_row k i h) ▸
      (liftStates K hrow k x hx (i.1.1 - firstRow k)).1
    else 0

theorem primitive_apply_index (K : Bicomplex R)
    (hrow : ∀ r : ℕ, (K.X r).Acyclic) (k : ℤ)
    (x : Product K k) (hx : differential K k x = 0) (n : ℕ) :
    primitive K hrow k x hx (primitiveIndex k n) =
      (liftStates K hrow k x hx n).1 := by
  unfold primitive
  have h : firstRow k ≤ (primitiveIndex k n).1.1 := by
    dsimp [primitiveIndex]
    omega
  simp only [dite_eq_left h]
  let m := (primitiveIndex k n).1.1 - firstRow k
  have hm : m = n := by dsimp [m, primitiveIndex]; omega
  have he : primitiveIndex k m = primitiveIndex k n :=
    primitiveIndex_of_row k (primitiveIndex k n) h
  change Eq.ndrec (motive := fun i : Diag (k + 1) => ↥((K.X i.1.1).X i.1.2))
    (liftStates K hrow k x hx m).1 he = (liftStates K hrow k x hx n).1
  have aux (a b : ℕ) (hab : a = b) (hidx : primitiveIndex k a = primitiveIndex k b) :
      Eq.ndrec (motive := fun i : Diag (k + 1) => ↥((K.X i.1.1).X i.1.2))
        (liftStates K hrow k x hx a).1 hidx = (liftStates K hrow k x hx b).1 := by
    subst b
    have he' : hidx = rfl := Subsingleton.elim _ _
    rw [he']
  exact aux m n hm he

theorem primitive_apply_early (K : Bicomplex R)
    (hrow : ∀ r : ℕ, (K.X r).Acyclic) (k : ℤ)
    (x : Product K k) (hx : differential K k x = 0)
    (i : Diag (k + 1)) (hi : i.1.1 < firstRow k) :
    primitive K hrow k x hx i = 0 := by
  simp [primitive, show ¬firstRow k ≤ i.1.1 by omega]

theorem nextHorizontalIndex_diag (k : ℤ) (n : ℕ)
    (h : k = (k + 1) - 1) :
    nextHorizontalIndex (k + 1) k h (diagonalIndex k n) = primitiveIndex k n := rfl

theorem nextVerticalIndex_diag_succ (k : ℤ) (n : ℕ)
    (h : k = (k + 1) - 1)
    (hn : 0 < (diagonalIndex k (n + 1)).1.1) :
    nextVerticalIndex (k + 1) k h (diagonalIndex k (n + 1)) hn =
      primitiveIndex k n := rfl

theorem nextVerticalIndex_diag_first_early (k : ℤ)
    (h : k = (k + 1) - 1)
    (hn : 0 < (diagonalIndex k 0).1.1) :
    (nextVerticalIndex (k + 1) k h (diagonalIndex k 0) hn).1.1 < firstRow k := by
  dsimp [nextVerticalIndex, diagonalIndex] at hn ⊢
  omega

/-- Each chosen primitive has exactly the prescribed boundary at every diagonal coordinate. -/
theorem primitive_boundary_index (K : Bicomplex R)
    (hrow : ∀ r : ℕ, (K.X r).Acyclic) (k : ℤ)
    (x : Product K k) (hx : differential K k x = 0) (n : ℕ) :
    (productTotal K).d (k + 1) k (primitive K hrow k x hx) (diagonalIndex k n) =
      x (diagonalIndex k n) := by
  have hk : k = (k + 1) - 1 := by omega
  cases n with
  | zero =>
    by_cases hz : firstRow k = 0
    · have hzero : (diagonalIndex k 0).1.1 = 0 := hz
      rw [productTotal_d_apply_zero K (k + 1) k hk _ _ hzero]
      change (K.X (firstRow k)).d (firstColumn k + 1) (firstColumn k)
        (primitive K hrow k x hx (primitiveIndex k 0)) = x (diagonalIndex k 0)
      rw [primitive_apply_index]
      exact liftStates_first K hrow k x hx
    · have hpos : 0 < (diagonalIndex k 0).1.1 := by
        dsimp [diagonalIndex]
        omega
      have hearly := primitive_apply_early K hrow k x hx
        (nextVerticalIndex (k + 1) k hk (diagonalIndex k 0) hpos)
        (nextVerticalIndex_diag_first_early k hk hpos)
      rw [productTotal_d_apply_pos K (k + 1) k hk _ _ hpos]
      change (K.X (firstRow k)).d (firstColumn k + 1) (firstColumn k)
          (primitive K hrow k x hx (primitiveIndex k 0)) +
        (Int.negOnePow ((k + 1) + 1) : ℤ) •
          (K.d (firstRow k - 1) (firstRow k)).f (firstColumn k)
            (primitive K hrow k x hx
              (nextVerticalIndex (k + 1) k hk (diagonalIndex k 0) hpos)) =
        x (diagonalIndex k 0)
      rw [primitive_apply_index, hearly]
      change (K.X (firstRow k)).d (firstColumn k + 1) (firstColumn k)
          (liftStates K hrow k x hx 0).1 +
        (Int.negOnePow ((k + 1) + 1) : ℤ) •
          (K.d (firstRow k - 1) (firstRow k)).f (firstColumn k) 0 =
        x (diagonalIndex k 0)
      simp only [map_zero, smul_zero, add_zero]
      exact liftStates_first K hrow k x hx
  | succ n =>
    have hpos : 0 < (diagonalIndex k (n + 1)).1.1 := by
      dsimp [diagonalIndex]
      omega
    rw [productTotal_d_apply_pos K (k + 1) k hk _ _ hpos]
    change (K.X (firstRow k + n + 1)).d
        (firstColumn k + n + 1 + 1) (firstColumn k + n + 1)
          (primitive K hrow k x hx (primitiveIndex k (n + 1))) +
        (Int.negOnePow ((k + 1) + 1) : ℤ) •
          (K.d (firstRow k + n) (firstRow k + n + 1)).f
            (firstColumn k + n + 1)
              (primitive K hrow k x hx (primitiveIndex k n)) =
      x (diagonalIndex k (n + 1))
    rw [primitive_apply_index, primitive_apply_index]
    have hs : (Int.negOnePow ((k + 1) + 1) : ℤ) =
        (Int.negOnePow k : ℤ) := by
      have h1 : (Int.negOnePow ((k + 1) + 1) : ℤ) =
          -(Int.negOnePow (k + 1) : ℤ) := by
        simpa using congrArg (fun unit : ℤˣ => (unit : ℤ)) (Int.negOnePow_succ (k + 1))
      have h2 : (Int.negOnePow (k + 1) : ℤ) =
          -(Int.negOnePow k : ℤ) := by
        simpa using congrArg (fun unit : ℤˣ => (unit : ℤ)) (Int.negOnePow_succ k)
      rw [h1, h2]
      simp
    rw [hs, liftStates_step]
    abel

/-- A quadrant bicomplex with acyclic horizontal rows has an acyclic unrestricted
product total in every integer degree. The chosen elementwise lifts are not natural. -/
theorem acyclic_productTotal (K : Bicomplex R)
    (hrow : ∀ r : ℕ, (K.X r).Acyclic) : (productTotal K).Acyclic := by
  intro k
  apply (ShortComplex.moduleCat_exact_iff ((productTotal K).sc k)).mpr
  have hp : (ComplexShape.down ℤ).prev k = k + 1 := by
    apply ComplexShape.prev_eq'
    change k + 1 = k + 1
    rfl
  have hn : (ComplexShape.down ℤ).next k = k - 1 := by
    apply ComplexShape.next_eq'
    change k - 1 + 1 = k
    omega
  change ∀ x : Product K k,
    (productTotal K).d k ((ComplexShape.down ℤ).next k) x = 0 →
      ∃ y : Product K ((ComplexShape.down ℤ).prev k),
        (productTotal K).d ((ComplexShape.down ℤ).prev k) k y = x
  rw [hp, hn]
  intro x hx
  have hcycle : differential K k x = 0 := by
    rw [productTotal_d] at hx
    exact hx
  refine ⟨primitive K hrow k x hcycle, ?_⟩
  funext i
  rw [← diagonalIndex_surjective k i]
  exact primitive_boundary_index K hrow k x hcycle (i.1.1 - firstRow k)

end CategoryTheory.QuadrantProductTotal
