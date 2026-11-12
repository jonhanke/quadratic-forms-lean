/-
# Kitaoka 1993, Section 2.1: proof of Theorem 2.1.2 (comparison of $a[n]$ with $a$ on Siegel's domain)

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §2.1, Theorem 2.1.2, p. 37 (printed page).

**Proves** `theorem212 : Theorem212`: for $t, u > 0$ there are constants $c_1, c_2 > 0$, depending only on $m, t, u$,
with $c_1\, a[x] \le p[x] \le c_2\, a[x]$ for $p = a[n] = {}^t n\,a\,n$, $a \in A_t$, $n \in N_u$ and all
$x \in \mathbb R^m$ (so in particular for $x = e_i$, giving $c_1 a_i \le p_{ii} \le c_2 a_i$).

**Proof.** Write $a = \mathrm{diag}(a_0, \dots, a_{m-1})$, so $p[x] = a[nx]$.
1. *Ratios.* From $a_i/a_{i+1} \le t$ we get $a_i \le T^{j-i} a_j \le T^m a_j$ for $i \le j$, where $T = \max(1, t)$.
2. *Upper bound* (`upper_bound`). If $w$ is any matrix with $w_{ij}^2 a_i \le C a_j$ for all $i, j$, then
   by Cauchy–Schwarz $(wx)_i^2 \le m \sum_j w_{ij}^2 x_j^2$, hence
   $$a[wx] = \sum_i a_i (wx)_i^2 \le m \sum_{i,j} C a_j x_j^2 = m^2 C\, a[x].$$
   For $w = n$ upper unitriangular with $|n_{ij}| \le u$ the hypothesis holds with $C = \max(1,u)^2 T^m$.
3. *Lower bound.* $w = n^{-1}$ is again upper unitriangular, and its entries satisfy $|w_{ij}| \le R^{j-i}$ with
   $R = \max(1, mu)$ (strong induction on $j - i$ from $0 = (nw)_{ij}$, i.e.
   $w_{ij} = -\sum_{i < k \le j} n_{ik} w_{kj}$). So step 2 applies to $w$, and
   $a[x] = a[w(nx)] \le c'\, a[nx]$, i.e. $c_1 = 1/c'$.
4. *Diagonal.* $p_{ii} = p[e_i]$ and $a_{ii} = a[e_i]$.
-/
import QuadFormsKB.Literature.Kitaoka.Ch2ReductionProofs
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Ring.Finset

open Matrix Finset

noncomputable section

namespace QuadFormsKB.Kitaoka.Reduction

variable {m : ℕ}

/-- $x^{\mathsf T}({}^t n\,A\,n)x = (nx)^{\mathsf T} A (nx)$. -/
theorem quad_conj (A n : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ) :
    x ⬝ᵥ ((nᵀ * A * n) *ᵥ x) = (n *ᵥ x) ⬝ᵥ (A *ᵥ (n *ᵥ x)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-- The diagonal entry as a quadratic form value. -/
theorem single_quad (M : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) :
    (Pi.single i (1 : ℝ) : Fin m → ℝ) ⬝ᵥ (M *ᵥ Pi.single i 1) = M i i := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem quad_diagonal (α x : Fin m → ℝ) : x ⬝ᵥ (diagonal α *ᵥ x) = ∑ i, α i * x i ^ 2 := by
  simp [dotProduct, mulVec_diagonal, pow_two]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Upper bound for the quadratic form of a matrix `w` with `w_ij² α_i ≤ C α_j`. -/
theorem upper_bound (α : Fin m → ℝ) (hα : ∀ i, 0 < α i) (w : Matrix (Fin m) (Fin m) ℝ) (C : ℝ)
    (hC : ∀ i j, w i j ^ 2 * α i ≤ C * α j) (x : Fin m → ℝ) :
    (w *ᵥ x) ⬝ᵥ (diagonal α *ᵥ (w *ᵥ x)) ≤ (m : ℝ) ^ 2 * C * (x ⬝ᵥ (diagonal α *ᵥ x)) := by
  rw [quad_diagonal, quad_diagonal]
  have h1 : ∀ i, α i * (w *ᵥ x) i ^ 2 ≤ m * ∑ j, C * α j * x j ^ 2 := by
    intro i
    have hcs : (w *ᵥ x) i ^ 2 ≤ m * ∑ j, (w i j * x j) ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin m))) (f := fun j => w i j * x j)
      simpa [Matrix.mulVec, dotProduct] using this
    calc α i * (w *ᵥ x) i ^ 2 ≤ α i * (m * ∑ j, (w i j * x j) ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (hα i).le
      _ = m * ∑ j, (w i j ^ 2 * α i) * x j ^ 2 := by
          rw [mul_left_comm]; congr 1
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ m * ∑ j, C * α j * x j ^ 2 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_right (hC i j) (sq_nonneg _)
  calc ∑ i, α i * (w *ᵥ x) i ^ 2 ≤ ∑ _i : Fin m, (m : ℝ) * ∑ j, C * α j * x j ^ 2 :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = (m : ℝ) ^ 2 * C * ∑ j, α j * x j ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

/-- Ratios along the diagonal: `α i ≤ T^(j-i) α j`. -/
theorem ratio_bound (α : Fin m → ℝ) (hα : ∀ i, 0 < α i) (t : ℝ)
    (hr : ∀ i j : Fin m, j.val = i.val + 1 → α i / α j ≤ t) :
    ∀ d : ℕ, ∀ i j : Fin m, j.val = i.val + d → α i ≤ (max 1 t) ^ d * α j := by
  intro d
  induction d with
  | zero =>
    intro i j h
    have : i = j := Fin.ext (by simpa using h.symm)
    subst this; simp
  | succ d ih =>
    intro i j h
    have hk : i.val + 1 < m := by have := j.isLt; omega
    let k : Fin m := ⟨i.val + 1, hk⟩
    have h1 : α i ≤ max 1 t * α k := by
      have := hr i k rfl
      rw [div_le_iff₀ (hα k)] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hα k).le)
    have h2 : α k ≤ (max 1 t) ^ d * α j := ih k j (by simp only [k]; omega)
    calc α i ≤ max 1 t * α k := h1
      _ ≤ max 1 t * ((max 1 t) ^ d * α j) :=
          mul_le_mul_of_nonneg_left h2 (zero_le_one.trans (le_max_left _ _))
      _ = (max 1 t) ^ (d + 1) * α j := by ring

/-- Entrywise coefficient bound for an upper triangular matrix. -/
theorem coef_bound (α : Fin m → ℝ) (hα : ∀ i, 0 < α i) (t : ℝ)
    (hr : ∀ i j : Fin m, j.val = i.val + 1 → α i / α j ≤ t) (w : Matrix (Fin m) (Fin m) ℝ)
    (hw : ∀ i j, j < i → w i j = 0) (B : ℝ) (hB : ∀ i j, w i j ^ 2 ≤ B) (i j : Fin m) :
    w i j ^ 2 * α i ≤ B * (max 1 t) ^ m * α j := by
  rcases lt_or_ge j i with h | h
  · rw [hw i j h]
    have hB0 : 0 ≤ B := (sq_nonneg _).trans (hB i j)
    have hT0 : 0 < (max 1 t) := lt_max_of_lt_left one_pos
    have h0 : 0 ≤ B * (max 1 t) ^ m * α j := by have := hα j; positivity
    simpa using h0
  · have hT : (1 : ℝ) ≤ max 1 t := le_max_left _ _
    have h1 : α i ≤ (max 1 t) ^ m * α j := by
      refine (ratio_bound α hα t hr (j.val - i.val) i j (by have : i.val ≤ j.val := h; omega)).trans ?_
      refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT ?_) (hα j).le
      have := j.isLt; omega
    have hB0 : 0 ≤ B := (sq_nonneg _).trans (hB i j)
    calc w i j ^ 2 * α i ≤ B * α i := mul_le_mul_of_nonneg_right (hB i j) (hα i).le
      _ ≤ B * ((max 1 t) ^ m * α j) := mul_le_mul_of_nonneg_left h1 hB0
      _ = B * (max 1 t) ^ m * α j := by ring

/-- The inverse of a real upper unitriangular matrix. -/
theorem UTri.exists_inv_real {w : Matrix (Fin m) (Fin m) ℝ} (hw : UTri w) :
    ∃ y : Matrix (Fin m) (Fin m) ℝ, UTri y ∧ w * y = 1 := by
  have hup : w.BlockTriangular id := fun i j hij => hw.1 i j hij
  have hdet : w.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (M := w) hup]
    simp [hw.2]
  have hunit : IsUnit w.det := by rw [hdet]; exact isUnit_one
  have : Invertible w := Matrix.invertibleOfIsUnitDet w hunit
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

/-- Entries of the inverse of an upper unitriangular matrix with entries bounded by `u`. -/
theorem inv_entry_bound {n w : Matrix (Fin m) (Fin m) ℝ} (hn : UTri n) (hw : UTri w) (hnw : n * w = 1)
    (u : ℝ) (hu : 0 ≤ u) (hnu : ∀ i j, i < j → |n i j| ≤ u) :
    ∀ d : ℕ, ∀ i j : Fin m, j.val = i.val + d → |w i j| ≤ (max 1 (u * m)) ^ d := by
  set R : ℝ := max 1 (u * m) with hR
  have hR1 : 1 ≤ R := le_max_left _ _
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro i j hij
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      have : i = j := Fin.ext (by simpa using hij.symm)
      subst this; simp [hw.2]
    · have hsum : ∑ k, n i k * w k j = 0 := by
        have := congrFun (congrFun hnw i) j
        rw [Matrix.mul_apply, Matrix.one_apply_ne] at this
        · exact this
        · intro h; subst h; omega
      have hsplit : w i j = - ∑ k ∈ univ.erase i, n i k * w k j := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hn.2, one_mul] at hsum
        linarith
      have hterm : ∀ k ∈ univ.erase i, |n i k * w k j| ≤ u * R ^ (d - 1) := by
        intro k hk
        have hki : k ≠ i := Finset.ne_of_mem_erase hk
        rw [abs_mul]
        rcases lt_or_gt_of_ne hki with h | h
        · rw [hn.1 i k h]; simp only [abs_zero, zero_mul]; positivity
        · rcases lt_or_ge j k with h2 | h2
          · rw [hw.1 k j h2]; simp only [abs_zero, mul_zero]; positivity
          · have hk1 : |w k j| ≤ R ^ (j.val - k.val) := by
              have hkj : k.val ≤ j.val := h2
              have hik : i.val < k.val := h
              exact ih (j.val - k.val) (by omega) k j (by omega)
            have hk2 : R ^ (j.val - k.val) ≤ R ^ (d - 1) :=
              pow_le_pow_right₀ hR1 (by have : i.val < k.val := h; omega)
            exact mul_le_mul (hnu i k h) (hk1.trans hk2) (abs_nonneg _) hu
      calc |w i j| = |∑ k ∈ univ.erase i, n i k * w k j| := by rw [hsplit, abs_neg]
        _ ≤ ∑ k ∈ univ.erase i, |n i k * w k j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k ∈ univ.erase i, u * R ^ (d - 1) := Finset.sum_le_sum hterm
        _ = ((m - 1 : ℕ) : ℝ) * (u * R ^ (d - 1)) := by
            rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
        _ ≤ (m : ℝ) * (u * R ^ (d - 1)) := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le m 1)
              (mul_nonneg hu (pow_nonneg (zero_le_one.trans hR1) _))
        _ = (u * m) * R ^ (d - 1) := by ring
        _ ≤ R * R ^ (d - 1) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (zero_le_one.trans hR1) _)
        _ = R ^ d := by
            rw [← pow_succ' R (d - 1)]; congr 1; omega

/-- **Kitaoka 1993, Theorem 2.1.2** (p. 37): for $t, u > 0$ there are constants $c_1, c_2 > 0$ depending only on
$m$, $t$, $u$ such that $c_1\, a[x] \le p[x] \le c_2\, a[x]$ for all $x \in \mathbb R^m$ whenever
$p = {}^t n\,a\,n$ with $a \in A_t$, $n \in N_u$; in particular $c_1 a_i \le p_{ii} \le c_2 a_i$. The constants
are $c_2 = m^2 \max(1,u)^2 T^m + 1$ and $c_1 = 1/(m^2 W^2 T^m + 1)$, where $T = \max(1,t)$ and
$W = R^m$, $R = \max(1, mu)$. Unconditional. -/
@[kb "kitaoka1993" "§2.1, Thm. 2.1.2, p. 37"]
theorem theorem212 : Theorem212 := by
  intro m t u ht hu
  set T : ℝ := max 1 t with hT
  set U : ℝ := max 1 u with hU
  set R : ℝ := max 1 (u * m) with hR
  have hT1 : 1 ≤ T := le_max_left _ _
  have hU1 : 1 ≤ U := le_max_left _ _
  have hR1 : 1 ≤ R := le_max_left _ _
  have hTm : 0 < T ^ m := by positivity
  set W : ℝ := R ^ m with hW
  have hW0 : 0 ≤ W := by positivity
  set C₂ : ℝ := (m : ℝ) ^ 2 * (U ^ 2 * T ^ m) + 1 with hC₂
  set C₁ : ℝ := (m : ℝ) ^ 2 * (W ^ 2 * T ^ m) + 1 with hC₁
  have hC₂0 : 0 < C₂ := by positivity
  have hC₁0 : 0 < C₁ := by positivity
  refine ⟨1 / C₁, C₂, by positivity, hC₂0, ?_⟩
  rintro a ⟨α, hα, hr, rfl⟩ n hn
  have hnU : UTri n := (mem_unitri_iff n).1 hn.1
  have hnu : ∀ i j, i < j → |n i j| ≤ u := hn.2
  obtain ⟨w, hwU, hnw⟩ := UTri.exists_inv_real hnU
  have hwn : w * n = 1 := mul_eq_one_comm.1 hnw
  -- coefficient bounds
  have hnB : ∀ i j, n i j ^ 2 ≤ U ^ 2 := by
    intro i j
    have : |n i j| ≤ U := by
      rcases lt_trichotomy i j with h | h | h
      · exact (hnu i j h).trans (le_max_right _ _)
      · subst h; rw [hnU.2]; simpa using hU1
      · rw [hnU.1 i j h]; simp; linarith
    exact sq_le_sq' (abs_le.1 this).1 (abs_le.1 this).2
  have hwB : ∀ i j, w i j ^ 2 ≤ W ^ 2 := by
    intro i j
    have : |w i j| ≤ W := by
      rcases lt_or_ge j i with h | h
      · rw [hwU.1 i j h]; simp; exact hW0
      · refine (inv_entry_bound hnU hwU hnw u hu.le hnu (j.val - i.val) i j
          (by have : i.val ≤ j.val := h; omega)).trans ?_
        exact pow_le_pow_right₀ hR1 (by have := j.isLt; omega)
    exact sq_le_sq' (abs_le.1 this).1 (abs_le.1 this).2
  have hr' : ∀ i j : Fin m, j.val = i.val + 1 → α i / α j ≤ t := hr
  have hup : ∀ x : Fin m → ℝ,
      (n *ᵥ x) ⬝ᵥ (diagonal α *ᵥ (n *ᵥ x)) ≤ (m : ℝ) ^ 2 * (U ^ 2 * T ^ m) * (x ⬝ᵥ (diagonal α *ᵥ x)) :=
    fun x => by
      have := upper_bound α hα n (U ^ 2 * T ^ m)
        (fun i j => by
          have := coef_bound α hα t hr' n (fun i j h => hnU.1 i j h) (U ^ 2) hnB i j
          simpa [mul_assoc] using this) x
      simpa [mul_assoc] using this
  have hlow : ∀ x : Fin m → ℝ,
      x ⬝ᵥ (diagonal α *ᵥ x) ≤ (m : ℝ) ^ 2 * (W ^ 2 * T ^ m) * ((n *ᵥ x) ⬝ᵥ (diagonal α *ᵥ (n *ᵥ x))) :=
    fun x => by
      have := upper_bound α hα w (W ^ 2 * T ^ m)
        (fun i j => by
          have := coef_bound α hα t hr' w (fun i j h => hwU.1 i j h) (W ^ 2) hwB i j
          simpa [mul_assoc] using this) (n *ᵥ x)
      rw [mulVec_mulVec, hwn, one_mulVec] at this
      exact this
  have hnonneg : ∀ x : Fin m → ℝ, 0 ≤ x ⬝ᵥ (diagonal α *ᵥ x) := fun x => by
    rw [quad_diagonal]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hα i).le (sq_nonneg _)
  have hgen : ∀ x : Fin m → ℝ,
      1 / C₁ * (x ⬝ᵥ (diagonal α *ᵥ x)) ≤ x ⬝ᵥ ((nᵀ * diagonal α * n) *ᵥ x) ∧
        x ⬝ᵥ ((nᵀ * diagonal α * n) *ᵥ x) ≤ C₂ * (x ⬝ᵥ (diagonal α *ᵥ x)) := by
    intro x
    rw [quad_conj]
    have h0 := hnonneg x
    have h0' := hnonneg (n *ᵥ x)
    constructor
    · rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hC₁0]
      have := hlow x
      nlinarith
    · have := hup x
      nlinarith
  refine ⟨fun x _ => hgen x, fun i => ?_⟩
  have h := hgen (Pi.single i 1)
  rw [single_quad, single_quad] at h
  simpa using h

end QuadFormsKB.Kitaoka.Reduction
