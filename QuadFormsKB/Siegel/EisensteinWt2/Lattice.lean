/-
# Weight-2 Eisenstein series via Hecke's trick: the lattice $\mathbb{Z}z + \mathbb{Z}$

Specializes the analytic core (`EisensteinWt2/Hecke.lean`) to the lattice points $cz + d$, $z \in \mathbb{H}$, and
proves the *outer cancellation* limit `tendsto_outer`: for an $N$-periodic $a : \mathbb{Z} \to \mathbb{C}$ of mean zero,
$$\sum_c a(c)\sum_d (cz+d)^{-2}|cz+d|^{-2s} \longrightarrow \sum_c a(c)\sum_d (cz+d)^{-2} \qquad (s \to 0^+).$$
The decay $\bigl|\sum_d (cz+d)^{-2}\bigr| \le C e^{-2\pi|c|\operatorname{Im}z}$ (`norm_e2Row_le`) comes from Mathlib's
Lipschitz formula `EisensteinSeries.qExpansion_identity`.
-/
import QuadFormsKB.Siegel.EisensteinWt2.Hecke

open Complex Filter Topology
open scoped Real UpperHalfPlane

namespace QuadFormsKB.Siegel.EisensteinWt2

section Lattice

variable (z : ℍ)

lemma one_le_norm_fin2 {x : Fin 2 → ℤ} (hx : x ≠ 0) : (1 : ℝ) ≤ ‖x‖ := by
  rw [EisensteinSeries.norm_eq_max_natAbs]
  have : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext fun i => by fin_cases i <;> simp [h.1, h.2])
  rcases this with h | h
  · exact_mod_cast le_max_of_le_left (Int.natAbs_pos.mpr h)
  · exact_mod_cast le_max_of_le_right (Int.natAbs_pos.mpr h)

lemma r_le_norm_lat {c d : ℤ} (h : (c : ℂ) * z + d ≠ 0) :
    EisensteinSeries.r z ≤ ‖(c : ℂ) * z + d‖ := by
  have hx : (![c, d] : Fin 2 → ℤ) ≠ 0 := by
    intro hx
    apply h
    have h0 := congr_fun hx 0
    have h1 := congr_fun hx 1
    simp only [Matrix.cons_val_zero, Pi.zero_apply, Matrix.cons_val_one] at h0 h1
    simp [h0, h1]
  have h1 := EisensteinSeries.r_mul_max_le z hx
  have h2 := one_le_norm_fin2 hx
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1
  nlinarith [EisensteinSeries.r_pos z]

lemma lat_ne_zero {c : ℤ} (hc : c ≠ 0) (d : ℤ) : (c : ℂ) * z + d ≠ 0 := by
  intro h
  have := congr_arg Complex.im h
  simp only [add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero, UpperHalfPlane.coe_im, zero_im] at this
  rcases mul_eq_zero.mp this with h' | h'
  · exact hc (by exact_mod_cast h')
  · exact (ne_of_gt z.im_pos) h'

lemma summable_lat_rpow {t : ℝ} (ht : 2 < t) :
    Summable fun p : ℤ × ℤ => ‖(p.1 : ℂ) * z + p.2‖ ^ (-t) := by
  have h : Summable fun x : Fin 2 → ℤ => ‖(x 0 : ℂ) * z + x 1‖ ^ (-t) :=
    Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
      (fun x => EisensteinSeries.summand_bound z (by linarith) x)
      ((EisensteinSeries.summable_one_div_norm_rpow ht).mul_left _)
  rw [← (finTwoArrowEquiv ℤ).symm.summable_iff] at h
  exact h.congr fun p => by simp [finTwoArrowEquiv]

lemma norm_inv_zpow_two (u : ℂ) : ‖(u ^ (2 : ℤ))⁻¹‖ = ‖u‖ ^ (-2 : ℝ) := by
  rw [norm_inv, norm_zpow, Real.rpow_neg (norm_nonneg _)]
  norm_cast

lemma summable_lat_row_two (c : ℤ) : Summable fun d : ℤ => ‖(c : ℂ) * z + d‖ ^ (-2 : ℝ) :=
  ((EisensteinSeries.linear_right_summable z c (k := 2) le_rfl).norm).congr fun _ =>
    norm_inv_zpow_two _

lemma summable_lat_col_two (d : ℤ) : Summable fun c : ℤ => ‖(c : ℂ) * z + d‖ ^ (-2 : ℝ) :=
  ((EisensteinSeries.linear_left_summable (UpperHalfPlane.ne_zero z) d (k := 2) le_rfl).norm).congr
    fun _ => norm_inv_zpow_two _

/-- The rows $d \mapsto cz + d$ of the lattice form a `RowSystem` with step $1$. -/
lemma rowSystem_lat : RowSystem (fun c d : ℤ => (c : ℂ) * z + d) 1 (EisensteinSeries.r z) where
  step i j := by push_cast; ring
  rho_pos := EisensteinSeries.r_pos z
  ge_rho i j h := r_le_norm_lat z h
  ne_zero i j hi := lat_ne_zero z hi j
  summable3 := summable_lat_rpow z (by norm_num)
  summable2 := summable_lat_row_two z

/-- **Pointwise row limit:** for a sequence $\ell$ of complex numbers whose nonzero entries have norm $\ge\rho$ and with
$\sum|\ell_j|^{-2} < \infty$, and bounded weights $v$, $\sum_j v_jf_s(\ell_j) \to \sum_j v_j\ell_j^{-2}$ as $s \to 0^+$. -/
lemma tendsto_tsum_fs {ℓ : ℤ → ℂ} {ρ B : ℝ} (hρ : 0 < ρ) (hge : ∀ j, ℓ j ≠ 0 → ρ ≤ ‖ℓ j‖)
    (h2 : Summable fun j => ‖ℓ j‖ ^ (-2 : ℝ)) {v : ℤ → ℂ} (hB : ∀ j, ‖v j‖ ≤ B) :
    Tendsto (fun s => ∑' j, v j * fs s (ℓ j)) (𝓝[>] 0) (𝓝 (∑' j, v j * fs 0 (ℓ j))) := by
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 ≤ s ∧ s ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact ⟨hs.1.le, hs.2.le⟩
  set K := max 1 (ρ ^ (-2 : ℝ))
  refine tendsto_tsum_of_dominated_convergence (bound := fun j => B * (K * ‖ℓ j‖ ^ (-2 : ℝ)))
    ((h2.mul_left K).mul_left B) (fun j => (tendsto_fs (ℓ j)).const_mul _) ?_
  filter_upwards [hev] with s hs
  intro j
  rw [norm_mul]
  refine mul_le_mul (hB j) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hB j))
  by_cases h : ℓ j = 0
  · rw [fs_zero_of_eq h, norm_zero]; positivity
  · exact norm_fs_le hρ (hge j h) hs.1 hs.2

lemma norm_fs_le_rpow {s : ℝ} (_hs : 0 ≤ s) (u : ℂ) : ‖fs s u‖ ≤ ‖u‖ ^ (-(2 + 2 * s)) := by
  by_cases hu : u = 0
  · rw [fs_zero_of_eq hu, norm_zero]; positivity
  · have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
    rw [fs, norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg
      (Real.rpow_nonneg (norm_nonneg _) _), show -(2 + 2 * s) = -2 + -2 * s by ring,
      Real.rpow_add hu0, Real.rpow_neg hu0.le (2 : ℝ), Real.rpow_two]

/-! ### The row sums $\sum_d (cz+d)^{-2}$ and their decay -/

/-- The row sum $R_s(c) = \sum_d f_s(cz + d)$. -/
noncomputable def rowSum (s : ℝ) (c : ℤ) : ℂ := ∑' d : ℤ, fs s ((c : ℂ) * z + d)

lemma rowSum_neg (s : ℝ) (c : ℤ) : rowSum z s (-c) = rowSum z s c := by
  rw [rowSum, rowSum, ← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun d => ?_
  simp only [Equiv.neg_apply, Int.cast_neg, fs]
  rw [show (-(c : ℂ) * z + -(d : ℂ)) = -((c : ℂ) * z + d) by ring, norm_neg, neg_sq]

/-- The norm of $e^{2\pi i n z}$. -/
lemma norm_cexp_two_pi_mul (n : ℕ) :
    ‖cexp (2 * π * I * (n * (z : ℂ)))‖ = Real.exp (-2 * π * z.im) ^ n := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp [mul_re, mul_im]
  ring

lemma exp_neg_two_pi_lt_one : Real.exp (-2 * π * z.im) < 1 :=
  Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, z.im_pos])

/-- **Lipschitz formula for a row:** $\sum_d (nz + d)^{-2} = (-2\pi i)^2\sum_{k \ge 0}k\,e^{2\pi i k n z}$. -/
lemma rowSum_zero_natCast {n : ℕ} (hn : 0 < n) :
    rowSum z 0 n = (-2 * π * I) ^ 2 * ∑' k : ℕ, (k : ℂ) * cexp (2 * π * I * (n * (z : ℂ))) ^ k := by
  have hw : 0 < ((n : ℂ) * z).im := by
    simp only [mul_im, natCast_re, UpperHalfPlane.coe_im, natCast_im, UpperHalfPlane.coe_re, zero_mul,
      add_zero]
    exact mul_pos (by exact_mod_cast hn) z.im_pos
  have h := EisensteinSeries.qExpansion_identity (k := 1) le_rfl ⟨(n : ℂ) * z, hw⟩
  simp only [Nat.factorial_one, Nat.cast_one, div_one, pow_one] at h
  rw [rowSum]
  simp only [fs_zero_left]
  convert h using 2
  · ext d; simp [one_div]

/-- **Exponential decay of the row sums:** for $c \ne 0$,
$\bigl|\sum_d (cz+d)^{-2}\bigr| \le \dfrac{4\pi^2}{(1-x)^2}\,x^{|c|}$, $x = e^{-2\pi\operatorname{Im}z}$. -/
lemma norm_rowSum_zero_le {c : ℤ} (hc : c ≠ 0) :
    ‖rowSum z 0 c‖ ≤ 4 * π ^ 2 / (1 - Real.exp (-2 * π * z.im)) ^ 2 *
      Real.exp (-2 * π * z.im) ^ c.natAbs := by
  set x₁ := Real.exp (-2 * π * z.im)
  have hx₁ : x₁ < 1 := exp_neg_two_pi_lt_one z
  have hx₁0 : 0 < x₁ := Real.exp_pos _
  have key : ∀ n : ℕ, 0 < n → ‖rowSum z 0 n‖ ≤ 4 * π ^ 2 / (1 - x₁) ^ 2 * x₁ ^ n := by
    intro n hn
    rw [rowSum_zero_natCast z hn]
    set q := cexp (2 * π * I * (n * (z : ℂ)))
    have hq : ‖q‖ = x₁ ^ n := norm_cexp_two_pi_mul z n
    have hxn : x₁ ^ n < 1 := pow_lt_one₀ hx₁0.le hx₁ hn.ne'
    have hxn0 : 0 ≤ x₁ ^ n := by positivity
    have hgeo : HasSum (fun k : ℕ => (k : ℝ) * (x₁ ^ n) ^ k) (x₁ ^ n / (1 - x₁ ^ n) ^ 2) := by
      have hs : Summable (fun k : ℕ => (k : ℝ) * (x₁ ^ n) ^ k) := by
        simpa using summable_pow_mul_geometric_of_norm_lt_one 1
          (by rwa [Real.norm_of_nonneg hxn0])
      have := tsum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := x₁ ^ n)
        (by rwa [Real.norm_of_nonneg hxn0])
      rw [← this]; exact hs.hasSum
    have h1 : ‖∑' k : ℕ, (k : ℂ) * q ^ k‖ ≤ x₁ ^ n / (1 - x₁ ^ n) ^ 2 :=
      tsum_of_norm_bounded hgeo fun k => by
        rw [norm_mul, norm_pow, hq, Complex.norm_natCast]
    have h2 : x₁ ^ n / (1 - x₁ ^ n) ^ 2 ≤ x₁ ^ n / (1 - x₁) ^ 2 := by
      apply div_le_div_of_nonneg_left hxn0 (by nlinarith)
      have : x₁ ^ n ≤ x₁ := pow_le_of_le_one hx₁0.le hx₁.le hn.ne'
      nlinarith
    have hnorm : ‖(-2 * π * I : ℂ) ^ 2‖ = 4 * π ^ 2 := by
      rw [norm_pow, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real,
        Complex.norm_I, Real.norm_of_nonneg Real.pi_pos.le]
      ring
    rw [norm_mul, hnorm]
    calc 4 * π ^ 2 * ‖∑' k : ℕ, (k : ℂ) * q ^ k‖ ≤ 4 * π ^ 2 * (x₁ ^ n / (1 - x₁) ^ 2) := by
          gcongr; exact h1.trans h2
      _ = _ := by ring
  have hca : rowSum z 0 c = rowSum z 0 (c.natAbs : ℤ) := by
    rcases Int.natAbs_eq c with h | h
    · conv_lhs => rw [h]
    · conv_lhs => rw [h, rowSum_neg]
  rw [hca]; exact key _ (Int.natAbs_pos.mpr hc)

lemma summable_geom_natAbs {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    Summable fun c : ℤ => x ^ c.natAbs := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa using summable_geometric_of_lt_one hx0 hx
  · simpa using summable_geometric_of_lt_one hx0 hx

lemma summable_rowSum_zero : Summable (rowSum z 0) := by
  set x₁ := Real.exp (-2 * π * z.im)
  have hs := (summable_geom_natAbs (Real.exp_pos (-2 * π * z.im)).le (exp_neg_two_pi_lt_one z)).mul_left
    (4 * π ^ 2 / (1 - x₁) ^ 2)
  refine Summable.of_norm_bounded_eventually hs ?_
  rw [Filter.eventually_cofinite]
  refine (Set.finite_singleton (0 : ℤ)).subset fun c hc => ?_
  by_contra h
  exact hc (norm_rowSum_zero_le z h)

lemma norm_rowSum_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (c : ℤ) :
    ‖rowSum z s c‖ ≤ max 1 (EisensteinSeries.r z ^ (-2 : ℝ)) *
      ∑' d : ℤ, ‖(c : ℂ) * z + d‖ ^ (-2 : ℝ) := by
  rw [rowSum, ← tsum_mul_left]
  refine tsum_of_norm_bounded ((summable_lat_row_two z c).mul_left _).hasSum fun d => ?_
  by_cases h : (c : ℂ) * z + d = 0
  · rw [fs_zero_of_eq h, norm_zero]; positivity
  · exact norm_fs_le (EisensteinSeries.r_pos z) (r_le_norm_lat z h) hs0 hs1

lemma summable_rowSum {s : ℝ} (hs : 0 < s) : Summable (rowSum z s) := by
  have h := (summable_lat_rpow z (t := 2 + 2 * s) (by linarith)).prod
  refine Summable.of_norm_bounded h fun c => ?_
  rw [rowSum]
  exact tsum_of_norm_bounded ((summable_lat_rpow z (t := 2 + 2 * s) (by linarith)).prod_factor c).hasSum
    fun d => norm_fs_le_rpow hs.le _

lemma tendsto_rowSum (c : ℤ) : Tendsto (fun s => rowSum z s c) (𝓝[>] 0) (𝓝 (rowSum z 0 c)) := by
  have h := tendsto_tsum_fs (ℓ := fun d : ℤ => (c : ℂ) * z + d) (B := 1) (EisensteinSeries.r_pos z)
    (fun d h => r_le_norm_lat z h) (summable_lat_row_two z c) (v := fun _ => 1) (fun _ => by simp)
  simpa [rowSum] using h

/-! ### Outer cancellation -/

variable {N : ℕ} [NeZero N] {a : ℤ → ℂ} {B : ℝ}

/-- **Hecke limit with outer cancellation.** For $a$ $N$-periodic of mean zero over a period,
$\sum_c a(c)\sum_d f_s(cz+d) \to \sum_c a(c)\sum_d (cz+d)^{-2}$ as $s \to 0^+$. -/
theorem tendsto_outer (hper : ∀ c, a (c + N) = a c) (hmean : ∑ r ∈ Finset.range N, a r = 0)
    (hB : ∀ c, ‖a c‖ ≤ B) :
    Tendsto (fun s => ∑' c, a c * rowSum z s c) (𝓝[>] 0) (𝓝 (∑' c, a c * rowSum z 0 c)) := by
  set Ω := partialPer N a
  have hΩ := norm_partialPer_le (N := N) hB
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set K := max 1 (EisensteinSeries.r z ^ (-2 : ℝ))
  set S2 : ℤ → ℝ := fun c => ∑' d : ℤ, ‖(c : ℂ) * z + d‖ ^ (-2 : ℝ)
  set S3 : ℤ → ℝ := fun c => ∑' d : ℤ, ‖(c : ℂ) * z + d‖ ^ (-3 : ℝ)
  have hS3 : Summable S3 := (summable_lat_rpow z (t := 3) (by norm_num)).prod
  have hS3' : Summable fun c => S3 (c - 1) := (Equiv.subRight (1 : ℤ)).summable_iff.mpr hS3
  set D : ℤ → ℝ := fun c => 4 * K * ‖(z : ℂ)‖ * (S3 c + S3 (c - 1)) +
    (if c = 0 ∨ c = 1 then K * (S2 (c - 1) + S2 c) else 0)
  have hD : Summable D := by
    refine (((hS3.add hS3').mul_left _).add (summable_of_ne_finset_zero (s := {0, 1}) ?_))
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    simp [hc.1, hc.2]
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact ⟨hs.1, hs.2.le⟩
  -- the difference bound
  have hdiff : ∀ s, 0 ≤ s → s ≤ 1 → ∀ c, ‖rowSum z s (c - 1) - rowSum z s c‖ ≤ D c := by
    intro s hs0 hs1 c
    have hsum : ∀ c' : ℤ, Summable fun d : ℤ => fs s ((c' : ℂ) * z + d) := fun c' =>
      Summable.of_norm_bounded ((summable_lat_row_two z c').mul_left K) fun d => by
        by_cases h : (c' : ℂ) * z + d = 0
        · rw [fs_zero_of_eq h, norm_zero]; positivity
        · exact norm_fs_le (EisensteinSeries.r_pos z) (r_le_norm_lat z h) hs0 hs1
    by_cases hc : c = 0 ∨ c = 1
    · have h1 := norm_rowSum_le z hs0 hs1 (c - 1)
      have h2 := norm_rowSum_le z hs0 hs1 c
      have : 0 ≤ 4 * K * ‖(z : ℂ)‖ * (S3 c + S3 (c - 1)) := by
        have : 0 ≤ S3 c := tsum_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
        have : 0 ≤ S3 (c - 1) := tsum_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
        have : 0 ≤ K := zero_le_one.trans (le_max_left _ _)
        positivity
      simp only [D, hc, ite_true]
      calc ‖rowSum z s (c - 1) - rowSum z s c‖ ≤ ‖rowSum z s (c - 1)‖ + ‖rowSum z s c‖ :=
            norm_sub_le _ _
        _ ≤ K * S2 (c - 1) + K * S2 c := add_le_add h1 h2
        _ ≤ _ := by linarith
    · push Not at hc
      have hc0 : c ≠ 0 := hc.1
      have hc1 : c - 1 ≠ 0 := sub_ne_zero.mpr hc.2
      simp only [D, show ¬(c = 0 ∨ c = 1) by tauto, ite_false, add_zero]
      rw [rowSum, rowSum, ← (hsum (c - 1)).tsum_sub (hsum c)]
      have hb : ∀ d : ℤ, ‖fs s (((c - 1 : ℤ) : ℂ) * z + d) - fs s ((c : ℂ) * z + d)‖ ≤
          4 * K * ‖(z : ℂ)‖ * (‖(c : ℂ) * z + d‖ ^ (-3 : ℝ) + ‖((c - 1 : ℤ) : ℂ) * z + d‖ ^ (-3 : ℝ)) := by
        intro d
        have := norm_fs_sub_le (EisensteinSeries.r_pos z) (r_le_norm_lat z (lat_ne_zero z hc0 d))
          (r_le_norm_lat z (lat_ne_zero z hc1 d)) hs0 hs1
        rwa [show ((c - 1 : ℤ) : ℂ) * z + d - ((c : ℂ) * z + d) = -z by push_cast; ring,
          norm_neg] at this
      have hs3c := (summable_lat_rpow z (t := 3) (by norm_num)).prod_factor c
      have hs3c1 := (summable_lat_rpow z (t := 3) (by norm_num)).prod_factor (c - 1)
      refine tsum_of_norm_bounded ?_ hb
      have := ((hs3c.hasSum.add hs3c1.hasSum).mul_left (4 * K * ‖(z : ℂ)‖))
      simpa [S3] using this
  -- Abel transform at each s
  have habel : ∀ s, (s = 0 ∨ 0 < s) → ∑' c, a c * rowSum z s c =
      ∑' c, Ω c * (rowSum z s (c - 1) - rowSum z s c) := by
    intro s hs
    have hg : Summable (rowSum z s) := by
      rcases hs with rfl | hs
      · exact summable_rowSum_zero z
      · exact summable_rowSum z hs
    exact tsum_mul_eq_partialPer hper hmean hB hg
  rw [habel 0 (Or.inl rfl)]
  have hlim : Tendsto (fun s => ∑' c, Ω c * (rowSum z s (c - 1) - rowSum z s c)) (𝓝[>] 0)
      (𝓝 (∑' c, Ω c * (rowSum z 0 (c - 1) - rowSum z 0 c))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun c => N * B * D c) (hD.mul_left _)
      (fun c => ((tendsto_rowSum z (c - 1)).sub (tendsto_rowSum z c)).const_mul _) ?_
    filter_upwards [hev] with s hs
    intro c
    rw [norm_mul]
    exact mul_le_mul (hΩ c) (hdiff s hs.1.le hs.2 c) (norm_nonneg _) (by positivity)
  refine hlim.congr' ?_
  filter_upwards [hev] with s hs
  exact (habel s (Or.inr hs.1)).symm

end Lattice

end QuadFormsKB.Siegel.EisensteinWt2
