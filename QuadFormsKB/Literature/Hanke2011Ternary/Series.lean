/-
# Hanke 2011 (ternary masses): formal power series helpers

J. Hanke, *Explicit formulas for masses of ternary quadratic lattices of varying determinant over number fields*,
arXiv:1109.1054 (bib key `hanke2011ternary`).

The local Dirichlet series of the paper are formal power series in $X := q^{-s}$ (Lemmas 3.1, 3.2, 6.1, 6.2). This
file has the two tools the paper's proofs use:

* `spread k φ` $= \sum_{m \ge 0} \varphi(m) X^{km}$, and the geometric series
  `spread_geom_mul`: $\big(\sum_m c^m X^{km}\big)(1 - cX^k) = 1$;
* `spread_mul_mk`: the "Ferrers diagram" reindexing of the paper's identity (7): a sum over pairs $(a, d)$ weighted by
  $X^{ka+d}$ is the product of the two one-variable series.
-/
import Mathlib
import QuadFormsKB.Citation

namespace QuadFormsKB.Hanke2011Ternary

open PowerSeries Finset

/-- **Spread series** $\sum_{m \ge 0} \varphi(m) X^{km}$ (the coefficient of $X^n$ is $\varphi(n/k)$ if $k \mid n$,
and $0$ otherwise). For $k = 1$ it is `PowerSeries.mk φ`. -/
noncomputable def spread (k : ℕ) (φ : ℕ → ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => if k ∣ n then φ (n / k) else 0

theorem coeff_spread (k : ℕ) (φ : ℕ → ℚ) (n : ℕ) :
    coeff n (spread k φ) = if k ∣ n then φ (n / k) else 0 := by
  simp [spread]

theorem spread_one (φ : ℕ → ℚ) : spread 1 φ = PowerSeries.mk φ := by
  ext n; simp [spread]

/-- **Geometric series:** $\big(\sum_{m\ge0} c^m X^{km}\big)\,(1 - cX^k) = 1$ for $k \ge 1$. -/
theorem spread_geom_mul (k : ℕ) (hk : 0 < k) (c : ℚ) :
    spread k (fun m => c ^ m) * (1 - C c * X ^ k) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, mul_comm (C c), ← mul_assoc, coeff_mul_C, coeff_mul_X_pow',
    coeff_spread, coeff_spread, coeff_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.not_le.mpr hk]
  · have hn0 : n ≠ 0 := by omega
    by_cases hkn : k ∣ n
    · obtain ⟨m, rfl⟩ := hkn
      have hm : 1 ≤ m := by rcases m with _ | m <;> simp_all
      have hle : k ≤ k * m := Nat.le_mul_of_pos_right k hm
      have e : k * m - k = k * (m - 1) := by rw [Nat.mul_sub, mul_one]
      simp only [dvd_mul_right, hle, e, Nat.mul_div_cancel_left _ hk, hn0, ite_true, ite_false]
      rw [← pow_succ, Nat.sub_add_cancel hm, sub_self]
    · by_cases hle : k ≤ n
      · have hd : ¬ k ∣ n - k := fun hd => hkn ((Nat.dvd_sub_iff_left hle (dvd_refl k)).mp hd)
        simp [hkn, hd, hn0, hle]
      · simp [hkn, hn0, hle]

/-- **Ferrers reindexing** (the step behind the paper's identity (7)):
$$\Big(\sum_{a} \varphi(a) X^{ka}\Big)\Big(\sum_d \psi(d) X^d\Big)
  = \sum_{n} \Big(\sum_{0 \le a,\ ka \le n} \varphi(a)\,\psi(n - ka)\Big) X^n.$$ -/
theorem spread_mul_mk (k : ℕ) (hk : 0 < k) (φ ψ : ℕ → ℚ) :
    spread k φ * PowerSeries.mk ψ =
      PowerSeries.mk fun n => ∑ a ∈ (range (n + 1)).filter (fun a => k * a ≤ n), φ a * ψ (n - k * a) := by
  ext n
  rw [coeff_mul, coeff_mk, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_spread, coeff_mk, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun a => k * a) (fun i => i / k) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_range] at ha ⊢
    exact ⟨by omega, dvd_mul_right k a⟩
  · intro i hi
    simp only [mem_filter, mem_range] at hi ⊢
    obtain ⟨hi, m, rfl⟩ := hi
    rw [Nat.mul_div_cancel_left _ hk]
    exact ⟨by nlinarith, by omega⟩
  · intro a _
    simp [Nat.mul_div_cancel_left _ hk]
  · intro i hi
    simp only [mem_filter] at hi
    exact Nat.mul_div_cancel' hi.2
  · intro a _
    simp [Nat.mul_div_cancel_left _ hk]

/-- `spread k` is additive in `φ`. -/
theorem spread_add (k : ℕ) (φ ψ : ℕ → ℚ) : spread k (φ + ψ) = spread k φ + spread k ψ := by
  ext n; simp only [coeff_spread, map_add, Pi.add_apply]; split_ifs <;> simp

/-- `spread k` commutes with scalars. -/
theorem spread_smul (k : ℕ) (c : ℚ) (φ : ℕ → ℚ) : spread k (fun m => c * φ m) = C c * spread k φ := by
  ext n; simp only [coeff_spread, coeff_C_mul]; split_ifs <;> simp

/-- The spread of the indicator of $0$ is $1$. -/
theorem spread_single_zero (k : ℕ) (hk : 0 < k) : spread k (fun m => if m = 0 then 1 else 0) = 1 := by
  ext n
  rw [coeff_spread, coeff_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : n ≠ 0 := by omega
    have : n / k ≠ 0 ∨ ¬ k ∣ n := by
      by_cases h1 : k ∣ n
      · left; obtain ⟨m, rfl⟩ := h1; rw [Nat.mul_div_cancel_left _ hk]; rintro rfl; simp at hn0
      · right; exact h1
    rcases this with h | h <;> simp [h, hn0]

/-- Respreading: $\sum_a [j \mid a]\,\varphi(a/j) X^{ka} = \sum_m \varphi(m) X^{kjm}$. -/
theorem spread_spread (k j : ℕ) (hk : 0 < k) (hj : 0 < j) (φ : ℕ → ℚ) :
    spread k (fun a => if j ∣ a then φ (a / j) else 0) = spread (k * j) φ := by
  ext n
  simp only [coeff_spread]
  by_cases h1 : k ∣ n
  · obtain ⟨a, rfl⟩ := h1
    rw [if_pos (dvd_mul_right k a), Nat.mul_div_cancel_left _ hk]
    by_cases h2 : j ∣ a
    · obtain ⟨m, rfl⟩ := h2
      rw [if_pos (dvd_mul_right j m), if_pos ⟨m, by ring⟩, Nat.mul_div_cancel_left _ hj,
        show k * (j * m) = (k * j) * m by ring, Nat.mul_div_cancel_left _ (Nat.mul_pos hk hj)]
    · rw [if_neg h2, if_neg]
      rintro ⟨m, hm⟩
      exact h2 ⟨m, by rw [mul_assoc] at hm; exact Nat.eq_of_mul_eq_mul_left hk hm⟩
  · rw [if_neg h1, if_neg]
    rintro ⟨m, rfl⟩
    exact h1 ⟨j * m, by ring⟩

/-- Shifting: $\sum_{a \ge 1} \varphi(a-1) X^{ka} = X^k \sum_m \varphi(m) X^{km}$. -/
theorem spread_shift (k : ℕ) (hk : 0 < k) (φ : ℕ → ℚ) :
    spread k (fun a => if a = 0 then 0 else φ (a - 1)) = X ^ k * spread k φ := by
  ext n
  rw [coeff_X_pow_mul', coeff_spread, coeff_spread]
  by_cases h1 : k ∣ n
  · obtain ⟨a, rfl⟩ := h1
    rw [if_pos (dvd_mul_right k a), Nat.mul_div_cancel_left _ hk]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [Nat.not_le.mpr (show 0 < k from hk)]
    · have hle : k ≤ k * a := Nat.le_mul_of_pos_right k ha
      have e : k * a - k = k * (a - 1) := by rw [Nat.mul_sub, mul_one]
      rw [if_neg (by omega), if_pos hle, e, if_pos (dvd_mul_right k _), Nat.mul_div_cancel_left _ hk]
  · rw [if_neg h1]
    split_ifs with hle hd
    · exact absurd ((Nat.dvd_sub_iff_left hle (dvd_refl k)).mp hd) h1
    · rfl
    · rfl

/-- Removing the constant term: $\sum_{a \ge 1} \varphi(a) X^{ka} = \sum_a \varphi(a)X^{ka} - \varphi(0)$. -/
theorem spread_sub_const (k : ℕ) (φ : ℕ → ℚ) :
    spread k (fun a => if a = 0 then 0 else φ a) = spread k φ - C (φ 0) := by
  ext n
  rw [map_sub, coeff_spread, coeff_spread, coeff_C]
  by_cases h1 : k ∣ n
  · rw [if_pos h1, if_pos h1]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · by_cases h0 : n / k = 0
      · rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp at h1; omega
        · obtain ⟨m, rfl⟩ := h1
          rw [Nat.mul_div_cancel_left _ hk] at h0
          subst h0; simp at hn
      · rw [if_neg h0, if_neg (by omega), sub_zero]
  · rw [if_neg h1, if_neg h1]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact absurd (dvd_zero k) h1
    · rw [if_neg (by omega), sub_zero]

/-- A sum over the pairs $(a, b)$ with $a + b = \nu$, $a \le b$, as a sum over $a$ with $2a \le \nu$. -/
theorem sum_antidiagonal_le (ν : ℕ) (f : ℕ → ℕ → ℚ) :
    ∑ ab ∈ (antidiagonal ν).filter (fun ab => ab.1 ≤ ab.2), f ab.1 ab.2 =
      ∑ a ∈ (range (ν + 1)).filter (fun a => 2 * a ≤ ν), f a (a + (ν - 2 * a)) := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun a ha => ?_
  simp only [mem_range] at ha
  by_cases h : 2 * a ≤ ν
  · rw [if_pos (by omega), if_pos h, show a + (ν - 2 * a) = ν - a by omega]
  · rw [if_neg (by omega), if_neg h]

/-- **Ferrers reindexing over pairs $a \le b$**: if $f(a, a+d) = \varphi(a)\psi(d)$ then
$\sum_\nu \big(\sum_{a+b=\nu,\ a\le b} f(a,b)\big)X^\nu = \big(\sum_a\varphi(a)X^{2a}\big)\big(\sum_d\psi(d)X^d\big)$. -/
theorem mk_sum_le_eq (f : ℕ → ℕ → ℚ) (φ ψ : ℕ → ℚ) (h : ∀ a d, f a (a + d) = φ a * ψ d) :
    PowerSeries.mk (fun ν => ∑ ab ∈ (antidiagonal ν).filter (fun ab => ab.1 ≤ ab.2), f ab.1 ab.2) =
      spread 2 φ * PowerSeries.mk ψ := by
  rw [spread_mul_mk 2 (by norm_num)]
  congr 1; funext ν
  rw [sum_antidiagonal_le]
  exact Finset.sum_congr rfl fun a _ => h a _

end QuadFormsKB.Hanke2011Ternary
