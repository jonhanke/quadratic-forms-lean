/-
# Kitaoka 1993, Section 2.1: proofs of Lemma 2.1.1 and of the Iwasawa decomposition

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §2.1, p. 34.

**Proves**
* `lemma211` (Lemma 2.1.1): $N = N_{1/2} N_{\mathbb Z}$, i.e. every real upper unitriangular matrix $x$ can be
  written $x = z y$ with $z$ upper unitriangular with all entries above the diagonal of absolute value at most
  $1/2$, and $y$ an upper unitriangular matrix with integer entries.  The proof reduces the entries of
  $x w$ ($w$ integral unitriangular) diagonal by diagonal: if the entries at distance at most $d$ above the
  diagonal are already in $[-1/2, 1/2]$, then multiplying on the right by $1 + C$, where $C$ has the integer
  $-\mathrm{round}(z_{ij})$ at the positions $j - i = d + 1$, fixes the entries at distance $d + 1$ and does
  not change the closer ones.  Finally $y = w^{-1}$, which is again integral unitriangular since
  $\det w = 1$.
* `iwasawaDecomposition`: every $g \in \mathrm{GL}_m(\mathbb R)$ is $g = k a n$ with $k$ orthogonal, $a$ positive
  diagonal and $n$ upper unitriangular.  The proof applies Mathlib's LDL decomposition to the positive definite
  matrix $S = {}^t g g = L D\,{}^t L$, rescales the columns of $L$ so that the triangular factor has diagonal
  $1$, takes $a$ to be the square root of the resulting diagonal, and sets $k = g (a n)^{-1}$, which is
  orthogonal because ${}^t k k = 1$.
-/
import QuadFormsKB.Literature.Kitaoka.Ch2Reduction
import Mathlib.Algebra.Order.Star.Real

open Matrix

noncomputable section

namespace QuadFormsKB.Kitaoka.Reduction

/-- A square matrix over a ring is *upper unitriangular* (`UTri`): zero strictly below the diagonal and $1$ on the
diagonal. This is `unitri` for real matrices (`mem_unitri_iff`), but is usable over any ring. -/
def UTri {R : Type*} [Zero R] [One R] {m : ℕ} (w : Matrix (Fin m) (Fin m) R) : Prop :=
  (∀ i j, j < i → w i j = 0) ∧ ∀ i, w i i = 1

theorem mem_unitri_iff {m : ℕ} (n : Matrix (Fin m) (Fin m) ℝ) : n ∈ unitri m ↔ UTri n :=
  ⟨fun h => ⟨fun i j hij => h.1 hij, h.2⟩, fun h => ⟨fun i j hij => h.1 i j hij, h.2⟩⟩

theorem UTri.one {R : Type*} [Semiring R] {m : ℕ} : UTri (1 : Matrix (Fin m) (Fin m) R) :=
  ⟨fun i j h => Matrix.one_apply_ne h.ne', fun i => by simp⟩

theorem UTri.mul {R : Type*} [Semiring R] {m : ℕ} {A B : Matrix (Fin m) (Fin m) R}
    (hA : UTri A) (hB : UTri B) : UTri (A * B) := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · rw [hA.1 i k hk, zero_mul]
    · rw [hB.1 k j (lt_of_lt_of_le hji hk), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hA.2, hB.2, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hA.1 i k h, zero_mul]
      · rw [hB.1 k i h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h

theorem UTri.map_cast {m : ℕ} {w : Matrix (Fin m) (Fin m) ℤ} (hw : UTri w) :
    UTri (w.map (Int.cast : ℤ → ℝ)) :=
  ⟨fun i j h => by simp [hw.1 i j h], fun i => by simp [hw.2 i]⟩

/-- The inverse of an integral upper unitriangular matrix is integral upper unitriangular. -/
theorem UTri.exists_inv {m : ℕ} {w : Matrix (Fin m) (Fin m) ℤ} (hw : UTri w) :
    ∃ y : Matrix (Fin m) (Fin m) ℤ, UTri y ∧ w * y = 1 := by
  have hup : w.BlockTriangular id := fun i j hij => hw.1 i j hij
  have hdet : w.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (M := w) hup]
    simp [hw.2]
  have hunit : IsUnit w.det := by rw [hdet]; exact isUnit_one
  haveI : Invertible w := Matrix.invertibleOfIsUnitDet w hunit
  have hyup : w⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hup
  have hmul : w * w⁻¹ = 1 := Matrix.mul_nonsing_inv w hunit
  refine ⟨w⁻¹, ⟨fun i j h => hyup h, fun i => ?_⟩, hmul⟩
  have h1 : (w * w⁻¹) i i = w⁻¹ i i := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hw.2, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hw.1 i k h, zero_mul]
      · rw [hyup h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [← h1, hmul]; simp

theorem map_cast_mul' {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) :
    (A * B).map (Int.cast : ℤ → ℝ) = A.map Int.cast * B.map Int.cast := by
  ext i j; simp [Matrix.mul_apply]

theorem map_cast_add' {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) :
    (A + B).map (Int.cast : ℤ → ℝ) = A.map Int.cast + B.map Int.cast := by
  ext i j; simp

theorem map_cast_one' {m : ℕ} : (1 : Matrix (Fin m) (Fin m) ℤ).map (Int.cast : ℤ → ℝ) = 1 := by
  ext i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]

/-- One step of the diagonal-by-diagonal reduction: if the entries of $x w$ at distance at most $d$ above the
diagonal are in $[-1/2, 1/2]$, there is an integral unitriangular $w'$ for which this holds up to distance
$d + 1$. -/
theorem lemma211_step {m : ℕ} (x : Matrix (Fin m) (Fin m) ℝ) (hx : UTri x) (d : ℕ)
    (w : Matrix (Fin m) (Fin m) ℤ) (hw : UTri w)
    (hd : ∀ i j : Fin m, i < j → j.val ≤ i.val + d → |(x * w.map (Int.cast : ℤ → ℝ)) i j| ≤ 1 / 2) :
    ∃ w' : Matrix (Fin m) (Fin m) ℤ, UTri w' ∧
      ∀ i j : Fin m, i < j → j.val ≤ i.val + (d + 1) →
        |(x * w'.map (Int.cast : ℤ → ℝ)) i j| ≤ 1 / 2 := by
  set z : Matrix (Fin m) (Fin m) ℝ := x * w.map (Int.cast : ℤ → ℝ) with hz
  have hzU : UTri z := hx.mul hw.map_cast
  let C : Matrix (Fin m) (Fin m) ℤ :=
    Matrix.of fun i j => if j.val = i.val + (d + 1) then -round (z i j) else 0
  have hC : ∀ i j, j ≤ i → C i j = 0 := by
    intro i j hji
    have : j.val ≤ i.val := hji
    simp only [C, Matrix.of_apply]
    rw [if_neg]; omega
  have hCU : UTri (1 + C) := by
    refine ⟨fun i j h => ?_, fun i => ?_⟩
    · rw [Matrix.add_apply, hC i j h.le, Matrix.one_apply_ne h.ne']; simp
    · rw [Matrix.add_apply, hC i i le_rfl]; simp
  refine ⟨w * (1 + C), hw.mul hCU, ?_⟩
  have hmap : x * (w * (1 + C)).map (Int.cast : ℤ → ℝ) = z * (1 + C.map (Int.cast : ℤ → ℝ)) := by
    rw [map_cast_mul', map_cast_add', map_cast_one', hz, Matrix.mul_assoc]
  intro i j hij hjd
  rw [hmap, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  by_cases h : j.val = i.val + (d + 1)
  · have hs : (z * C.map (Int.cast : ℤ → ℝ)) i j = -(round (z i j) : ℝ) := by
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · simp [C, h, hzU.2 i]
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with h' | h'
        · rw [hzU.1 i k h', zero_mul]
        · have hk' : i.val < k.val := h'
          have : C k j = 0 := by
            simp only [C, Matrix.of_apply]
            rw [if_neg]; omega
          simp [this]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hs, ← sub_eq_add_neg]
    exact abs_sub_round _
  · have hs : (z * C.map (Int.cast : ℤ → ℝ)) i j = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      rcases lt_or_ge k i with h' | h'
      · rw [hzU.1 i k h', zero_mul]
      · have hk' : i.val ≤ k.val := h'
        have : C k j = 0 := by
          simp only [C, Matrix.of_apply]
          rw [if_neg]; omega
        simp [this]
    rw [hs, add_zero]
    exact hd i j hij (by omega)

/-- **Kitaoka 1993, Lemma 2.1.1** (p. 34): $N = N_{1/2} N_{\mathbb Z}$. Every real upper unitriangular matrix
$x$ is $x = z y$ with $z \in N_{1/2}$ (entries above the diagonal of absolute value at most $1/2$) and $y$ an
integral upper unitriangular matrix. Proof: reduce $x w$ diagonal by diagonal by right multiplication with
integral unitriangular matrices (rounding to the nearest integer), then take $y = w^{-1}$, integral because
$\det w = 1$. -/
@[kb "kitaoka1993" "§2.1, Lemma 2.1.1, p. 34"]
theorem lemma211 : Lemma211 := by
  intro m x hx
  have hxU : UTri x := (mem_unitri_iff x).1 hx
  have key : ∀ d : ℕ, ∃ w : Matrix (Fin m) (Fin m) ℤ, UTri w ∧
      ∀ i j : Fin m, i < j → j.val ≤ i.val + d →
        |(x * w.map (Int.cast : ℤ → ℝ)) i j| ≤ 1 / 2 := by
    intro d
    induction d with
    | zero =>
      refine ⟨1, UTri.one, fun i j hij hjd => ?_⟩
      exfalso
      have : i.val < j.val := hij
      omega
    | succ d ih =>
      obtain ⟨w, hw, hd⟩ := ih
      exact lemma211_step x hxU d w hw hd
  obtain ⟨w, hw, hb⟩ := key m
  obtain ⟨y, hy, hwy⟩ := hw.exists_inv
  refine ⟨x * w.map (Int.cast : ℤ → ℝ),
    ⟨(mem_unitri_iff _).2 (hxU.mul hw.map_cast), fun i j hij => hb i j hij ?_⟩, y,
    (mem_unitri_iff _).2 hy.map_cast, ?_⟩
  · have := j.isLt; omega
  · rw [Matrix.mul_assoc, ← map_cast_mul', hwy, map_cast_one', Matrix.mul_one]

/-- **The Iwasawa decomposition** (Kitaoka 1993, §2.1, p. 34): every $g \in \mathrm{GL}_m(\mathbb R)$ is
$g = k a n$ with $k$ orthogonal, $a$ positive diagonal, $n$ upper unitriangular. Proof: LDL-decompose the
positive definite matrix ${}^t g g = L D\,{}^t L$, normalise the diagonal of ${}^t L$ to $1$ to get $n$, put
$a = \sqrt{\cdot}$ of the resulting diagonal, and $k = g (a n)^{-1}$, for which ${}^t k k = 1$. -/
@[kb "kitaoka1993" "§2.1, p. 34 (Iwasawa decomposition g = kan)"]
theorem iwasawaDecomposition : IwasawaDecomposition := by
  intro m g
  classical
  have hGu : IsUnit (g : Matrix (Fin m) (Fin m) ℝ) := g.isUnit
  generalize (g : Matrix (Fin m) (Fin m) ℝ) = G at hGu ⊢
  have hS : (Gᵀ * G).PosDef := by
    have := Matrix.PosDef.conjTranspose_mul_self G (Matrix.mulVec_injective_iff_isUnit.mpr hGu)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  -- Step A: the LDL decomposition
  obtain ⟨L, d, hLlow, hLd, hdpos, hLD⟩ : ∃ (L : Matrix (Fin m) (Fin m) ℝ) (d : Fin m → ℝ),
      (∀ i j, i < j → L i j = 0) ∧ (∀ i, L i i ≠ 0) ∧ (∀ i, 0 < d i) ∧
        L * diagonal d * Lᵀ = Gᵀ * G := by
    have hlow : (LDL.lower hS).IsLowerTriangular := LDL.isLowerTriangular_lower hS
    have hMu : IsUnit (LDL.lowerInv hS) := by
      haveI := LDL.invertibleLowerInv hS
      exact isUnit_of_invertible _
    have hMd : IsUnit (LDL.lowerInv hS).det := (Matrix.isUnit_iff_isUnit_det _).mp hMu
    refine ⟨LDL.lower hS, LDL.diagEntries hS, fun i j h => hlow h, ?_, ?_, ?_⟩
    · have h1 : LDL.lower hS * LDL.lowerInv hS = 1 := Matrix.nonsing_inv_mul _ hMd
      have h2 := congrArg Matrix.det h1
      rw [Matrix.det_mul, Matrix.det_one] at h2
      have h3 : (LDL.lower hS).det ≠ 0 := left_ne_zero_of_mul_eq_one h2
      rw [Matrix.det_of_isLowerTriangular _ hlow] at h3
      intro i hi
      exact h3 (Finset.prod_eq_zero (Finset.mem_univ i) hi)
    · have hDpos : (LDL.diag hS).PosDef := by
        rw [LDL.diag_eq_lowerInv_conj]
        exact hS.mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff_isUnit.mpr hMu)
      intro i
      have := hDpos.diag_pos (i := i)
      simpa [LDL.diag] using this
    · have := LDL.lower_conj_diag hS
      simp only [LDL.diag, Matrix.conjTranspose_eq_transpose_of_trivial] at this
      exact this
  -- Step B: normalise
  have he : ∀ i, 0 < L i i ^ 2 * d i := by
    intro i
    have h1 := hLd i
    have h2 := hdpos i
    positivity
  let c : Fin m → ℝ := fun i => (L i i)⁻¹
  let s : Fin m → ℝ := fun i => Real.sqrt (L i i ^ 2 * d i)
  have hspos : ∀ i, 0 < s i := fun i => Real.sqrt_pos.mpr (he i)
  let n : Matrix (Fin m) (Fin m) ℝ := diagonal c * Lᵀ
  let a : Matrix (Fin m) (Fin m) ℝ := diagonal s
  have hn : UTri n := by
    refine ⟨fun i j h => ?_, fun i => ?_⟩
    · simp [n, Matrix.diagonal_mul, hLlow j i h]
    · simp [n, c, Matrix.diagonal_mul, hLd i]
  have hdiag : diagonal c * diagonal s * diagonal s * diagonal c = diagonal d := by
    simp only [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    have hs : s i * s i = L i i ^ 2 * d i := Real.mul_self_sqrt (he i).le
    have h1 := hLd i
    calc c i * s i * s i * c i = c i * (s i * s i) * c i := by ring
      _ = d i := by rw [hs]; simp only [c]; field_simp
  have hS' : Gᵀ * G = (a * n)ᵀ * (a * n) := by
    rw [← hLD, ← hdiag]
    simp only [n, a, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
      Matrix.mul_assoc]
  have hdet : (a * n).det ≠ 0 := by
    have h2 : (Gᵀ * G).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit).ne_zero
    intro h0
    apply h2
    rw [hS', Matrix.det_mul, Matrix.det_transpose, h0]; simp
  have hdetU : IsUnit (a * n).det := isUnit_iff_ne_zero.mpr hdet
  have h1 : (a * n) * (a * n)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdetU
  have h2 : ((a * n)⁻¹)ᵀ * (a * n)ᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  have hk : (G * (a * n)⁻¹)ᵀ * (G * (a * n)⁻¹) = 1 := by
    calc (G * (a * n)⁻¹)ᵀ * (G * (a * n)⁻¹)
        = ((a * n)⁻¹)ᵀ * (Gᵀ * G) * (a * n)⁻¹ := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hS', ← Matrix.mul_assoc, h2, Matrix.one_mul, h1]
  refine ⟨G * (a * n)⁻¹, ?_, a, ⟨s, hspos, rfl⟩, n, (mem_unitri_iff n).2 hn, ?_⟩
  · exact (Matrix.mem_orthogonalGroup_iff' (Fin m) ℝ).mpr hk
  · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ hdetU]

end QuadFormsKB.Kitaoka.Reduction
