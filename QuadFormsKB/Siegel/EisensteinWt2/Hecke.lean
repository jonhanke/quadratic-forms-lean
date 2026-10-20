/-
# Weight-2 Eisenstein series via Hecke's trick: the analytic core

For a weight $w(c, d)$ that is $N$-periodic in both variables, the Hecke-regularized series
$$H_w(z, s) = \sum_{(c,d) \in \mathbb{Z}^2} w(c,d)\,(cz + d)^{-2}\,|cz+d|^{-2s} \qquad (s > 0)$$
converges absolutely. This file proves the estimates that let $s \to 0^+$ be taken inside the sum, for the
two kinds of cancellation that occur (*Hecke's trick*, Diamond–Shurman §4.6 / Miyake §7.2 [unverified locators]):

* **inner cancellation** (`RowSystem.tendsto`): if every row $d \mapsto w(c, d)$ has mean zero over a period, then
  $H_w(z, s) \to \sum_c\sum_d w(c,d)(cz+d)^{-2}$ (iterated sum, $c$ outer);
* **outer cancellation** (`tendsto_outer`, in `EisensteinWt2/Lattice.lean`): if $w(c, d) = a(c)$ with $a$ of mean
  zero, the same holds.

The method is elementary: summation by parts against the bounded periodic partial sums of the weight
(`norm_tsum_mul_le_of_mean_zero`), the difference bound
$|f_s(b) - f_s(a)| \le 4\max(1,\rho^{-2})\,|b-a|\,(|a|^{-3} + |b|^{-3})$ for $f_s(u) = u^{-2}|u|^{-2s}$
(`norm_fs_sub_le`), which is uniform in $s \in [0, 1]$, and Tannery's theorem (dominated convergence for series).
No Fourier analysis is needed.
-/
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.Analysis.Normed.Group.Tannery

open Complex Filter Topology

namespace QuadFormsKB.Siegel.EisensteinWt2


/-- The Hecke-regularized summand $f_s(u) = u^{-2}\,|u|^{-2s}$ (with $f_s(0) = 0$). -/
noncomputable def fs (s : ℝ) (u : ℂ) : ℂ := (u ^ 2)⁻¹ * ((‖u‖ ^ (-2 * s) : ℝ) : ℂ)

lemma fs_zero_left (u : ℂ) : fs 0 u = (u ^ 2)⁻¹ := by simp [fs]

/-- Elementary inequality: for $0 < p \le q$ and $0 \le \alpha \le 2$,
$p^{-\alpha} - q^{-\alpha} \le 2(q - p)p^{-\alpha}/q$. -/
lemma rpow_neg_sub_le {p q α : ℝ} (hp : 0 < p) (hpq : p ≤ q) (_hα0 : 0 ≤ α) (hα2 : α ≤ 2) :
    p ^ (-α) - q ^ (-α) ≤ 2 * (q - p) * p ^ (-α) / q := by
  have hq : 0 < q := hp.trans_le hpq
  set t := p / q with ht
  have ht0 : 0 < t := div_pos hp hq
  have ht1 : t ≤ 1 := (div_le_one hq).2 hpq
  have hqα : q ^ (-α) = p ^ (-α) * t ^ α := by
    rw [ht, Real.div_rpow hp.le hq.le, Real.rpow_neg hp.le, Real.rpow_neg hq.le]
    field_simp
  have key : 1 - t ^ α ≤ 2 * (1 - t) := by
    rcases le_total α 1 with h | h
    · have : t ≤ t ^ α := by
        simpa using Real.rpow_le_rpow_of_exponent_ge ht0 ht1 h
      linarith
    · have hb := one_add_mul_self_le_rpow_one_add (s := t - 1) (by linarith) h
      rw [show 1 + (t - 1) = t by ring] at hb
      nlinarith
  have h1t : 1 - t = (q - p) / q := by rw [ht]; field_simp
  have hpα : 0 ≤ p ^ (-α) := Real.rpow_nonneg hp.le _
  rw [hqα]
  calc p ^ (-α) - p ^ (-α) * t ^ α = p ^ (-α) * (1 - t ^ α) := by ring
    _ ≤ p ^ (-α) * (2 * (1 - t)) := mul_le_mul_of_nonneg_left key hpα
    _ = 2 * (q - p) * p ^ (-α) / q := by rw [h1t]; field_simp

lemma rpow_neg_le_max {x ρ s : ℝ} (hρ : 0 < ρ) (hx : ρ ≤ x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    x ^ (-2 * s) ≤ max 1 (ρ ^ (-2 : ℝ)) := by
  have hx0 : 0 < x := hρ.trans_le hx
  rcases le_total 1 x with h | h
  · exact le_max_of_le_left (Real.rpow_le_one_of_one_le_of_nonpos h (by linarith))
  · refine le_max_of_le_right ?_
    calc x ^ (-2 * s) ≤ x ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hx0 h (by linarith)
      _ ≤ ρ ^ (-2 : ℝ) := Real.rpow_le_rpow_of_nonpos hρ hx (by norm_num)

lemma norm_fs_le {u : ℂ} {ρ s : ℝ} (hρ : 0 < ρ) (hu : ρ ≤ ‖u‖) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖fs s u‖ ≤ max 1 (ρ ^ (-2 : ℝ)) * ‖u‖ ^ (-2 : ℝ) := by
  have hu0 : 0 < ‖u‖ := hρ.trans_le hu
  rw [fs, norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg
    (Real.rpow_nonneg (norm_nonneg _) _), Real.rpow_neg hu0.le, Real.rpow_two, mul_comm]
  gcongr
  exact rpow_neg_le_max hρ hu hs0 hs1

/-- The key difference bound: for $|a|, |b| \ge \rho > 0$ and $0 \le s \le 1$,
$|f_s(b) - f_s(a)| \le 4\max(1, \rho^{-2})\,|b - a|\,(|a|^{-3} + |b|^{-3})$. -/
lemma norm_fs_sub_le {a b : ℂ} {ρ s : ℝ} (hρ : 0 < ρ) (ha : ρ ≤ ‖a‖) (hb : ρ ≤ ‖b‖)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖fs s b - fs s a‖ ≤ 4 * max 1 (ρ ^ (-2 : ℝ)) * ‖b - a‖ * (‖a‖ ^ (-3 : ℝ) + ‖b‖ ^ (-3 : ℝ)) := by
  set K := max 1 (ρ ^ (-2 : ℝ)) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have ha0 : 0 < ‖a‖ := hρ.trans_le ha
  have hb0 : 0 < ‖b‖ := hρ.trans_le hb
  have ha0' : a ≠ 0 := norm_pos_iff.mp ha0
  have hb0' : b ≠ 0 := norm_pos_iff.mp hb0
  set m := min ‖a‖ ‖b‖ with hm
  set M := max ‖a‖ ‖b‖ with hM
  have hm0 : 0 < m := lt_min ha0 hb0
  have hmM : m ≤ M := min_le_max
  have hm3 : m ^ (-3 : ℝ) ≤ ‖a‖ ^ (-3 : ℝ) + ‖b‖ ^ (-3 : ℝ) := by
    rcases min_choice ‖a‖ ‖b‖ with h | h <;> rw [hm, h]
    · linarith [Real.rpow_nonneg hb0.le (-3 : ℝ)]
    · linarith [Real.rpow_nonneg ha0.le (-3 : ℝ)]
  have hm3' : m ^ (-3 : ℝ) = (m ^ 3)⁻¹ := by
    rw [Real.rpow_neg hm0.le]; norm_cast
  -- the two pieces
  have hsplit : fs s b - fs s a = ((b ^ 2)⁻¹ - (a ^ 2)⁻¹) * ((‖b‖ ^ (-2 * s) : ℝ) : ℂ) +
      (a ^ 2)⁻¹ * (((‖b‖ ^ (-2 * s) - ‖a‖ ^ (-2 * s) : ℝ)) : ℂ) := by
    simp only [fs]; push_cast; ring
  have hbK : ‖b‖ ^ (-2 * s) ≤ K := rpow_neg_le_max hρ hb hs0 hs1
  have hmK : m ^ (-2 * s) ≤ K := rpow_neg_le_max hρ (le_min ha hb) hs0 hs1
  -- piece 1
  have h1 : ‖(b ^ 2)⁻¹ - (a ^ 2)⁻¹‖ ≤ 2 * ‖b - a‖ * (m ^ 3)⁻¹ := by
    have he : (b ^ 2)⁻¹ - (a ^ 2)⁻¹ = (a - b) * (a + b) / (a ^ 2 * b ^ 2) := by
      field_simp; ring
    rw [he, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_sub_rev a b]
    have hab : ‖a + b‖ ≤ 2 * M := by
      calc ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
        _ ≤ M + M := add_le_add (le_max_left _ _) (le_max_right _ _)
        _ = 2 * M := by ring
    have hmMab : m * M = ‖a‖ * ‖b‖ := by
      rcases le_total ‖a‖ ‖b‖ with h | h
      · rw [hm, hM, min_eq_left h, max_eq_right h]
      · rw [hm, hM, min_eq_right h, max_eq_left h, mul_comm]
    have hM0 : 0 < M := hm0.trans_le hmM
    have hab2 : ‖a‖ ^ 2 * ‖b‖ ^ 2 = (m * M) ^ 2 := by rw [hmMab]; ring
    rw [hab2, div_le_iff₀ (by positivity)]
    calc ‖b - a‖ * ‖a + b‖ ≤ ‖b - a‖ * (2 * M) := by gcongr
      _ = 2 * ‖b - a‖ * (m ^ 3)⁻¹ * (m ^ 3 * M) := by field_simp
      _ ≤ 2 * ‖b - a‖ * (m ^ 3)⁻¹ * (m * M) ^ 2 := by
          gcongr
          nlinarith [mul_le_mul_of_nonneg_left hmM (by positivity : (0:ℝ) ≤ m ^ 2 * M)]
  -- piece 2
  have h2 : |‖b‖ ^ (-2 * s) - ‖a‖ ^ (-2 * s)| ≤ 2 * ‖b - a‖ * K / M := by
    have hα0 : 0 ≤ 2 * s := by linarith
    have hα2 : 2 * s ≤ 2 := by linarith
    have hdist : |‖b‖ - ‖a‖| ≤ ‖b - a‖ := abs_norm_sub_norm_le b a
    rcases le_total ‖a‖ ‖b‖ with h | h
    · have hmeq : m = ‖a‖ := min_eq_left h
      have hMeq : M = ‖b‖ := max_eq_right h
      have hr := rpow_neg_sub_le ha0 h hα0 hα2
      have hmono : ‖b‖ ^ (-(2 * s)) ≤ ‖a‖ ^ (-(2 * s)) :=
        Real.rpow_le_rpow_of_nonpos ha0 h (by linarith)
      rw [show -2 * s = -(2 * s) by ring, abs_sub_comm, abs_of_nonneg (by linarith)]
      rw [hmeq] at hmK; rw [hMeq]
      rw [show -2 * s = -(2 * s) by ring] at hmK
      calc ‖a‖ ^ (-(2 * s)) - ‖b‖ ^ (-(2 * s)) ≤ 2 * (‖b‖ - ‖a‖) * ‖a‖ ^ (-(2 * s)) / ‖b‖ := hr
        _ ≤ 2 * ‖b - a‖ * K / ‖b‖ := by
          gcongr
          · nlinarith [abs_le.mp hdist]
    · have hmeq : m = ‖b‖ := min_eq_right h
      have hMeq : M = ‖a‖ := max_eq_left h
      have hr := rpow_neg_sub_le hb0 h hα0 hα2
      have hmono : ‖a‖ ^ (-(2 * s)) ≤ ‖b‖ ^ (-(2 * s)) :=
        Real.rpow_le_rpow_of_nonpos hb0 h (by linarith)
      rw [show -2 * s = -(2 * s) by ring, abs_of_nonneg (by linarith)]
      rw [hmeq] at hmK; rw [hMeq]
      rw [show -2 * s = -(2 * s) by ring] at hmK
      calc ‖b‖ ^ (-(2 * s)) - ‖a‖ ^ (-(2 * s)) ≤ 2 * (‖a‖ - ‖b‖) * ‖b‖ ^ (-(2 * s)) / ‖a‖ := hr
        _ ≤ 2 * ‖b - a‖ * K / ‖a‖ := by
          gcongr
          · have := abs_le.mp hdist; linarith
  have hM0 : 0 < M := hm0.trans_le hmM
  have haM : (‖a‖ ^ 2)⁻¹ / M ≤ (m ^ 3)⁻¹ := by
    rw [div_le_iff₀ hM0]
    have hma : m ≤ ‖a‖ := min_le_left _ _
    have : m ^ 2 ≤ ‖a‖ ^ 2 := pow_le_pow_left₀ hm0.le hma 2
    calc (‖a‖ ^ 2)⁻¹ ≤ (m ^ 2)⁻¹ := inv_anti₀ (by positivity) this
      _ = (m ^ 3)⁻¹ * m := by field_simp
      _ ≤ (m ^ 3)⁻¹ * M := by gcongr
  rw [hsplit]
  calc ‖((b ^ 2)⁻¹ - (a ^ 2)⁻¹) * ((‖b‖ ^ (-2 * s) : ℝ) : ℂ) +
        (a ^ 2)⁻¹ * (((‖b‖ ^ (-2 * s) - ‖a‖ ^ (-2 * s) : ℝ)) : ℂ)‖
      ≤ ‖(b ^ 2)⁻¹ - (a ^ 2)⁻¹‖ * ‖b‖ ^ (-2 * s) +
        (‖a‖ ^ 2)⁻¹ * |‖b‖ ^ (-2 * s) - ‖a‖ ^ (-2 * s)| := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, norm_inv, norm_pow,
          Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), Real.norm_eq_abs]
    _ ≤ 2 * ‖b - a‖ * (m ^ 3)⁻¹ * K + (‖a‖ ^ 2)⁻¹ * (2 * ‖b - a‖ * K / M) := by
        gcongr
    _ = 2 * ‖b - a‖ * K * (m ^ 3)⁻¹ + 2 * ‖b - a‖ * K * ((‖a‖ ^ 2)⁻¹ / M) := by ring
    _ ≤ 2 * ‖b - a‖ * K * (m ^ 3)⁻¹ + 2 * ‖b - a‖ * K * (m ^ 3)⁻¹ := by gcongr
    _ = 4 * K * ‖b - a‖ * m ^ (-3 : ℝ) := by rw [hm3']; ring
    _ ≤ 4 * K * ‖b - a‖ * (‖a‖ ^ (-3 : ℝ) + ‖b‖ ^ (-3 : ℝ)) := by gcongr



section Abel

variable {N : ℕ} [NeZero N] {β : ℤ → ℂ}

/-- Partial sums $\Omega(k) = \sum_{0 \le j < (k \bmod N)}\beta(j)$ of an $N$-periodic sequence. -/
noncomputable def partialPer (N : ℕ) (β : ℤ → ℂ) (k : ℤ) : ℂ :=
  ∑ j ∈ Finset.range (k % (N : ℤ)).toNat, β j

lemma partialPer_succ (hper : ∀ k, β (k + N) = β k) (hmean : ∑ r ∈ Finset.range N, β r = 0)
    (k : ℤ) : partialPer N β (k + 1) - partialPer N β k = β k := by
  have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h0 : 0 ≤ k % (N : ℤ) := Int.emod_nonneg _ hN.ne'
  have hlt : k % (N : ℤ) < N := Int.emod_lt_of_pos _ hN
  set r := (k % (N : ℤ)).toNat with hr
  have hrk : (r : ℤ) = k % N := Int.toNat_of_nonneg h0
  have hP : Function.Periodic β (N : ℤ) := hper
  have hβ : β k = β r := by
    have := (hP.int_mul (k / N)) (k % N)
    rw [hrk, ← this]; congr 1; rw [mul_comm, add_comm]; exact (Int.mul_ediv_add_emod k N).symm
  have hk1 : (k + 1) % (N : ℤ) = (k % N + 1) % N := (Int.emod_add_emod k N 1).symm
  rw [hβ]
  rcases lt_or_eq_of_le (show k % (N : ℤ) + 1 ≤ N by omega) with h | h
  · have : (k + 1) % (N : ℤ) = k % N + 1 := by rw [hk1]; exact Int.emod_eq_of_lt (by omega) h
    have ht : ((k + 1) % (N : ℤ)).toNat = r + 1 := by omega
    simp only [partialPer, ht, Finset.sum_range_succ, ← hr]
    ring
  · have : (k + 1) % (N : ℤ) = 0 := by rw [hk1, h, Int.emod_self]
    have hrN : r + 1 = N := by omega
    simp only [partialPer, this, Int.toNat_zero, Finset.range_zero, Finset.sum_empty, ← hr]
    rw [← hrN, Finset.sum_range_succ] at hmean
    linear_combination (-1 : ℂ) * hmean

lemma norm_partialPer_le {B : ℝ} (hB : ∀ k, ‖β k‖ ≤ B) (k : ℤ) : ‖partialPer N β k‖ ≤ N * B := by
  have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hlt : k % (N : ℤ) < N := Int.emod_lt_of_pos _ hN
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hr : (k % (N : ℤ)).toNat ≤ N := by omega
  calc ‖partialPer N β k‖ ≤ ∑ j ∈ Finset.range (k % (N : ℤ)).toNat, ‖β j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (k % (N : ℤ)).toNat, B := Finset.sum_le_sum fun j _ => hB j
    _ = (k % (N : ℤ)).toNat * B := by simp
    _ ≤ N * B := by gcongr

/-- **Summation by parts** (identity form): $\sum_k\beta(k)g(k) = \sum_k\Omega(k)\,(g(k-1) - g(k))$. -/
lemma tsum_mul_eq_partialPer (hper : ∀ k, β (k + N) = β k)
    (hmean : ∑ r ∈ Finset.range N, β r = 0) {B : ℝ} (hB : ∀ k, ‖β k‖ ≤ B) {g : ℤ → ℂ}
    (hg : Summable g) :
    ∑' k, β k * g k = ∑' k, partialPer N β k * (g (k - 1) - g k) := by
  set Ω := partialPer N β
  have hΩ := norm_partialPer_le (N := N) hB
  have hbd : ∀ (a h : ℤ → ℂ), (∀ k, ‖a k‖ ≤ N * B) → Summable h → Summable fun k => a k * h k :=
    fun a h ha hh => Summable.of_norm_bounded (hh.norm.mul_left (N * B)) fun k => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (ha k) (norm_nonneg _)
  have hg1 : Summable fun k => g (k - 1) :=
    (Equiv.subRight (1 : ℤ)).summable_iff.mpr hg
  have hshift : ∑' k, Ω (k + 1) * g k = ∑' k, Ω k * g (k - 1) := by
    rw [← (Equiv.subRight (1 : ℤ)).tsum_eq]
    simp
  have e1 : ∑' k, β k * g k = ∑' k, (Ω (k + 1) * g k - Ω k * g k) := tsum_congr fun k => by
    rw [← sub_mul, partialPer_succ hper hmean]
  rw [e1, Summable.tsum_sub (hbd (fun k => Ω (k + 1)) g (fun k => hΩ (k + 1)) hg)
    (hbd Ω g hΩ hg), hshift, ← Summable.tsum_sub (hbd Ω _ hΩ hg1) (hbd Ω g hΩ hg)]
  exact tsum_congr fun k => by ring

/-- **Summation by parts for a periodic mean-zero weight:** if $\beta$ is $N$-periodic with
$\sum_{r=0}^{N-1}\beta(r) = 0$ and $|\beta| \le B$, then
$\left|\sum_k\beta(k)g(k)\right| \le NB\sum_k|g(k+1) - g(k)|$. -/
lemma norm_tsum_mul_le_of_mean_zero (hper : ∀ k, β (k + N) = β k)
    (hmean : ∑ r ∈ Finset.range N, β r = 0) {B : ℝ} (hB : ∀ k, ‖β k‖ ≤ B) {g : ℤ → ℂ}
    (hg : Summable g) (hΔ : Summable fun k => ‖g (k + 1) - g k‖) :
    ‖∑' k, β k * g k‖ ≤ N * B * ∑' k, ‖g (k + 1) - g k‖ := by
  have hΩ := norm_partialPer_le (N := N) hB
  have heq := tsum_mul_eq_partialPer hper hmean hB hg
  have hΔ' : Summable fun k => ‖g (k - 1) - g k‖ := by
    refine ((Equiv.subRight (1 : ℤ)).summable_iff.mpr hΔ).congr fun k => ?_
    simp [norm_sub_rev]
  have hre : ∑' k, ‖g (k + 1) - g k‖ = ∑' k, ‖g (k - 1) - g k‖ := by
    rw [← (Equiv.subRight (1 : ℤ)).tsum_eq]; simp [norm_sub_rev]
  rw [heq, hre]
  refine tsum_of_norm_bounded (hΔ'.hasSum.mul_left (N * B)) fun k => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hΩ k) (norm_nonneg _)

end Abel


section RowSystem

lemma fs_zero_of_eq {u : ℂ} (hu : u = 0) (s : ℝ) : fs s u = 0 := by simp [fs, hu]

lemma tendsto_fs (u : ℂ) : Tendsto (fun s => fs s u) (𝓝[>] 0) (𝓝 (fs 0 u)) := by
  by_cases hu : u = 0
  · simp [fs_zero_of_eq hu]
  · have hc : ContinuousAt (fun s : ℝ => ‖u‖ ^ (-2 * s)) 0 :=
      ((Real.continuousAt_const_rpow (norm_ne_zero_iff.mpr hu)).comp
        (continuous_const.mul continuous_id).continuousAt)
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    exact (tendsto_const_nhds.mul ((continuous_ofReal.tendsto _).comp hc))

/-- A *lattice row system*: values $L(i, j) \in \mathbb{C}$ with constant step $L(i, j+1) = L(i,j) + \tau$,
all nonzero values of norm $\ge \rho$, and the summability facts needed for the Hecke limit. -/
structure RowSystem (L : ℤ → ℤ → ℂ) (τ : ℂ) (ρ : ℝ) : Prop where
  step : ∀ i j, L i (j + 1) = L i j + τ
  rho_pos : 0 < ρ
  ge_rho : ∀ i j, L i j ≠ 0 → ρ ≤ ‖L i j‖
  ne_zero : ∀ i j, i ≠ 0 → L i j ≠ 0
  summable3 : Summable fun p : ℤ × ℤ => ‖L p.1 p.2‖ ^ (-3 : ℝ)
  summable2 : ∀ i, Summable fun j => ‖L i j‖ ^ (-2 : ℝ)

variable {L : ℤ → ℤ → ℂ} {τ : ℂ} {ρ : ℝ} {N : ℕ} [NeZero N] {v : ℤ → ℤ → ℂ} {B : ℝ}

lemma RowSystem.norm_fs_le' (hL : RowSystem L τ ρ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (i j : ℤ) :
    ‖fs s (L i j)‖ ≤ max 1 (ρ ^ (-2 : ℝ)) * ‖L i j‖ ^ (-2 : ℝ) := by
  by_cases h : L i j = 0
  · rw [fs_zero_of_eq h, norm_zero]; positivity
  · exact norm_fs_le hL.rho_pos (hL.ge_rho i j h) hs0 hs1

lemma RowSystem.summable_fs (hL : RowSystem L τ ρ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (i : ℤ)
    (hB : ∀ i j, ‖v i j‖ ≤ B) :
    Summable fun j => v i j * fs s (L i j) := by
  refine Summable.of_norm_bounded (((hL.summable2 i).mul_left (max 1 (ρ ^ (-2 : ℝ)))).mul_left B)
    fun j => ?_
  rw [norm_mul]
  exact mul_le_mul (hB i j) (hL.norm_fs_le' hs0 hs1 i j) (norm_nonneg _)
    ((norm_nonneg _).trans (hB i j))

lemma RowSystem.summable3_row (hL : RowSystem L τ ρ) (i : ℤ) :
    Summable fun j => ‖L i j‖ ^ (-3 : ℝ) :=
  hL.summable3.prod_factor i

lemma RowSystem.norm_sub_le (hL : RowSystem L τ ρ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {i : ℤ}
    (hi : i ≠ 0) (j : ℤ) :
    ‖fs s (L i (j + 1)) - fs s (L i j)‖ ≤
      4 * max 1 (ρ ^ (-2 : ℝ)) * ‖τ‖ * (‖L i j‖ ^ (-3 : ℝ) + ‖L i (j + 1)‖ ^ (-3 : ℝ)) := by
  have h := norm_fs_sub_le hL.rho_pos (hL.ge_rho i j (hL.ne_zero i j hi))
    (hL.ge_rho i (j + 1) (hL.ne_zero i _ hi)) hs0 hs1
  rw [hL.step i j]
  rw [hL.step i j, add_sub_cancel_left] at h
  exact h

/-- The row bound used for dominated convergence. -/
noncomputable def RowSystem.bound (L : ℤ → ℤ → ℂ) (τ : ℂ) (ρ : ℝ) (N : ℕ) (B : ℝ) (i : ℤ) : ℝ :=
  if i = 0 then B * (max 1 (ρ ^ (-2 : ℝ)) * ∑' j, ‖L 0 j‖ ^ (-2 : ℝ))
  else N * B * (4 * max 1 (ρ ^ (-2 : ℝ)) * ‖τ‖ * (2 * ∑' j, ‖L i j‖ ^ (-3 : ℝ)))

lemma RowSystem.norm_row_le (hL : RowSystem L τ ρ) (hper : ∀ i j, v i (j + N) = v i j)
    (hmean : ∀ i, ∑ r ∈ Finset.range N, v i r = 0) (hB : ∀ i j, ‖v i j‖ ≤ B)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (i : ℤ) :
    ‖∑' j, v i j * fs s (L i j)‖ ≤ RowSystem.bound L τ ρ N B i := by
  set K := max 1 (ρ ^ (-2 : ℝ))
  by_cases hi : i = 0
  · subst hi
    simp only [RowSystem.bound, ite_true]
    refine tsum_of_norm_bounded (((hL.summable2 0).hasSum.mul_left K).mul_left B) fun j => ?_
    rw [norm_mul]
    exact mul_le_mul (hB 0 j) (hL.norm_fs_le' hs0 hs1 0 j) (norm_nonneg _)
      ((norm_nonneg _).trans (hB 0 j))
  · simp only [RowSystem.bound, hi, ite_false]
    have hsum3 := hL.summable3_row i
    have hsum3' : Summable fun j => ‖L i (j + 1)‖ ^ (-3 : ℝ) :=
      (Equiv.addRight (1 : ℤ)).summable_iff.mpr hsum3
    have hΔsum : Summable fun j => 4 * K * ‖τ‖ * (‖L i j‖ ^ (-3 : ℝ) + ‖L i (j + 1)‖ ^ (-3 : ℝ)) :=
      (hsum3.add hsum3').mul_left _
    have hΔ : Summable fun j => ‖fs s (L i (j + 1)) - fs s (L i j)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hL.norm_sub_le hs0 hs1 hi) hΔsum
    have hg : Summable fun j => fs s (L i j) :=
      Summable.of_norm_bounded ((hL.summable2 i).mul_left K) (hL.norm_fs_le' hs0 hs1 i)
    refine (norm_tsum_mul_le_of_mean_zero (hper i) (hmean i) (hB i) hg hΔ).trans ?_
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
    gcongr
    calc ∑' j, ‖fs s (L i (j + 1)) - fs s (L i j)‖
        ≤ ∑' j, 4 * K * ‖τ‖ * (‖L i j‖ ^ (-3 : ℝ) + ‖L i (j + 1)‖ ^ (-3 : ℝ)) :=
          hΔ.tsum_le_tsum (hL.norm_sub_le hs0 hs1 hi) hΔsum
      _ = 4 * K * ‖τ‖ * (2 * ∑' j, ‖L i j‖ ^ (-3 : ℝ)) := by
          rw [tsum_mul_left, hsum3.tsum_add hsum3']
          congr 1
          have : ∑' j, ‖L i (j + 1)‖ ^ (-3 : ℝ) = ∑' j, ‖L i j‖ ^ (-3 : ℝ) :=
            (Equiv.addRight (1 : ℤ)).tsum_eq (fun j => ‖L i j‖ ^ (-3 : ℝ))
          rw [this]; ring

omit [NeZero N] in
lemma RowSystem.summable_bound (hL : RowSystem L τ ρ) :
    Summable (RowSystem.bound L τ ρ N B) := by
  have h : Summable fun i => N * B * (4 * max 1 (ρ ^ (-2 : ℝ)) * ‖τ‖ * (2 * ∑' j, ‖L i j‖ ^ (-3 : ℝ))) :=
    ((hL.summable3.prod.mul_left 2).mul_left _).mul_left _
  refine (h.update 0 (B * (max 1 (ρ ^ (-2 : ℝ)) * ∑' j, ‖L 0 j‖ ^ (-2 : ℝ)))).congr fun i => ?_
  by_cases hi : i = 0
  · subst hi; simp [RowSystem.bound]
  · simp [RowSystem.bound, hi]

/-- **Hecke limit along rows with mean-zero weights.** -/
theorem RowSystem.tendsto (hL : RowSystem L τ ρ) (hper : ∀ i j, v i (j + N) = v i j)
    (hmean : ∀ i, ∑ r ∈ Finset.range N, v i r = 0) (hB : ∀ i j, ‖v i j‖ ≤ B) :
    Tendsto (fun s => ∑' i, ∑' j, v i j * fs s (L i j)) (𝓝[>] 0)
      (𝓝 (∑' i, ∑' j, v i j * fs 0 (L i j))) := by
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 ≤ s ∧ s ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact ⟨hs.1.le, hs.2.le⟩
  refine tendsto_tsum_of_dominated_convergence (bound := RowSystem.bound L τ ρ N B)
    hL.summable_bound (fun i => ?_) ?_
  · -- each row converges
    set K := max 1 (ρ ^ (-2 : ℝ))
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun j => B * (K * ‖L i j‖ ^ (-2 : ℝ))) (((hL.summable2 i).mul_left K).mul_left B)
      (fun j => (tendsto_fs (L i j)).const_mul _) ?_
    filter_upwards [hev] with s hs
    intro j
    rw [norm_mul]
    exact mul_le_mul (hB i j) (hL.norm_fs_le' hs.1 hs.2 i j) (norm_nonneg _)
      ((norm_nonneg _).trans (hB i j))
  · filter_upwards [hev] with s hs
    exact fun i => hL.norm_row_le hper hmean hB hs.1 hs.2 i

lemma RowSystem.summable_rows (hL : RowSystem L τ ρ) (hper : ∀ i j, v i (j + N) = v i j)
    (hmean : ∀ i, ∑ r ∈ Finset.range N, v i r = 0) (hB : ∀ i j, ‖v i j‖ ≤ B) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Summable fun i => ∑' j, v i j * fs s (L i j) :=
  Summable.of_norm_bounded hL.summable_bound (hL.norm_row_le hper hmean hB hs0 hs1)


end RowSystem

end QuadFormsKB.Siegel.EisensteinWt2
