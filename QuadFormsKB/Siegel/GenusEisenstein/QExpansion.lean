/-
# The $q$-expansion of $E_W$ for $T$-invariant even weights
For $W : (\mathbb{Z}/N)^2 \to \mathbb{C}$ with $W(x, y + x) = W(x, y)$ (`IsTInv`) and $W(-x,-y) = W(x,y)$ (`IsEvenW`):
$$E_W(\tau) = \sum_{n \ge 0} e_W(n)q^n, \quad e_W(n) = [n = 0]\sum_d\frac{W(0,d)}{d^2}
  - 8\pi^2 n\sum_{c \ge 1}\frac{\hat W(c, n)}{c^2}, \quad \hat W(c, n) = \sum_{r < c}W(c, r)\,e\Big(\frac{nr}{c}\Big)$$
(`hasSum_eis2`, coefficients `eisCoeff`, `rowFC`). Row $c$ is expanded with period $c$ in $d$ (Lipschitz, `row_expansion`),
so only integral powers of $q$ occur. The interchange of the sums over $c$ and $n$ is justified by
`rowFC_eq_zero`: $\hat W(c, n) = 0$ unless $c \mid nN$ ($W(c,\cdot)$ has period $\gcd(c, N)$).
-/
import QuadFormsKB.Siegel.GenusEisenstein.Construction

open Complex Filter Topology ModularForm
open UpperHalfPlane hiding I
open scoped MatrixGroups Real Manifold

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Siegel.GenusEis

open EisensteinWt2

variable {N : ℕ} [NeZero N]

/-- $T$-invariance of a weight: $W(x, y + x) = W(x, y)$. -/
def IsTInv (W : ZMod N → ZMod N → ℂ) : Prop := ∀ x y : ZMod N, W x (y + x) = W x y

/-- Evenness of a weight: $W(-x, -y) = W(x, y)$. -/
def IsEvenW (W : ZMod N → ZMod N → ℂ) : Prop := ∀ x y : ZMod N, W (-x) (-y) = W x y

/-- $\hat W(c, n) = \sum_{r < c}W(c, r)\,e(nr/c)$. -/
noncomputable def rowFC (W : ZMod N → ZMod N → ℂ) (c n : ℕ) : ℂ :=
  ∑ r : Fin c, wt W c ((r : ℕ) : ℤ) * cexp (2 * π * I * ((n : ℂ) * (r : ℕ) / c))

lemma wt_add_self {W : ZMod N → ZMod N → ℂ} (hT : IsTInv W) (c d : ℤ) : wt W c (d + c) = wt W c d := by
  simp only [wt]; push_cast; exact hT _ _

lemma cexp_two_pi_I_int (k : ℤ) : cexp (2 * π * I * k) = 1 := by
  rw [Complex.exp_eq_one_iff]; exact ⟨k, by ring⟩

/-- Shifting a full period window: $\sum_{d < c}F(d + t) = \sum_{d < c}F(d)$ for $c$-periodic $F$. -/
lemma sum_range_shift {F : ℕ → ℂ} {c : ℕ} (hF : ∀ d, F (d + c) = F d) (t : ℕ) :
    ∑ d ∈ Finset.range c, F (d + t) = ∑ d ∈ Finset.range c, F d := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 := Finset.sum_range_succ' (fun d => F (d + t)) c
    have h2 := Finset.sum_range_succ (fun d => F (d + t)) c
    have h3 : F (c + t) = F (0 + t) := by rw [zero_add, add_comm]; exact hF t
    have h4 : ∑ d ∈ Finset.range c, F (d + (t + 1)) = ∑ d ∈ Finset.range c, F (d + 1 + t) :=
      Finset.sum_congr rfl fun d _ => by ring_nf
    rw [h4, ← ih]
    have := h1.symm.trans h2
    rw [h3] at this
    linear_combination this

/-- **$\hat W(c, n) = 0$ unless $c \mid nN$.** -/
theorem rowFC_eq_zero {W : ZMod N → ZMod N → ℂ} (hT : IsTInv W) {c n : ℕ} (hc : 0 < c)
    (hcn : ¬ c ∣ n * N) : rowFC W c n = 0 := by
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  set F : ℕ → ℂ := fun d => wt W c (d : ℤ) * cexp (2 * π * I * ((n : ℂ) * d / c)) with hF
  have hrow : rowFC W c n = ∑ d ∈ Finset.range c, F d := by
    rw [rowFC, Fin.sum_univ_eq_sum_range (fun d => F d)]
  have hper : ∀ d, F (d + c) = F d := by
    intro d
    simp only [hF]
    push_cast
    rw [wt_add_self hT]
    congr 1
    rw [show 2 * π * I * ((n : ℂ) * ((d : ℂ) + c) / c) = 2 * π * I * ((n : ℂ) * d / c) + 2 * π * I * ((n : ℤ) : ℂ) by
      push_cast; field_simp, Complex.exp_add, cexp_two_pi_I_int, mul_one]
  set g := Nat.gcd c N with hg
  -- `wt W c` has period `g`
  have hpc : Function.Periodic (fun d : ℤ => wt W c d) (c : ℤ) := fun d => wt_add_self hT c d
  have hpN : Function.Periodic (fun d : ℤ => wt W c d) (N : ℤ) := fun d => wt_add_N_right W c d
  have hpg : Function.Periodic (fun d : ℤ => wt W c d) (g : ℤ) := by
    have := (hpc.int_mul (Nat.gcdA c N)).add_period (hpN.int_mul (Nat.gcdB c N))
    rw [hg, Nat.gcd_eq_gcd_ab]
    rwa [mul_comm _ (c : ℤ), mul_comm _ (N : ℤ)] at this
  have hshift : ∀ d : ℕ, F (d + g) = F d * cexp (2 * π * I * ((n : ℂ) * g / c)) := by
    intro d
    simp only [hF]
    push_cast
    have h := hpg (d : ℤ)
    simp only at h
    rw [h, mul_assoc (wt W (c : ℤ) (d : ℤ)), ← Complex.exp_add]
    congr 2; ring
  have key := sum_range_shift hper g
  simp_rw [hshift, ← Finset.sum_mul] at key
  rw [hrow]
  have hne : cexp (2 * π * I * ((n : ℂ) * g / c)) ≠ 1 := by
    intro h1
    rw [Complex.exp_eq_one_iff] at h1
    obtain ⟨k, hk⟩ := h1
    have : (n : ℂ) * g = k * c := by
      have h2 : 2 * π * I * ((n : ℂ) * g / c) = 2 * π * I * k := by rw [hk]; ring
      have h3 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
      have := mul_left_cancel₀ h3 h2
      field_simp at this; linear_combination this
    have h' : ((n : ℤ) * g) = k * c := by exact_mod_cast this
    have hdiv : (c : ℤ) ∣ (n : ℤ) * g := ⟨k, by rw [h']; ring⟩
    apply hcn
    have : c ∣ n * g := by exact_mod_cast hdiv
    exact this.trans (Nat.mul_dvd_mul_left n (Nat.gcd_dvd_right c N))
  have := sub_eq_zero.mpr key
  rw [← mul_sub_one] at this
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hne

/-- $\|\hat W(c, n)\| \le c\,B_W$. -/
lemma norm_rowFC_le (W : ZMod N → ZMod N → ℂ) (c n : ℕ) : ‖rowFC W c n‖ ≤ c * wtBound W := by
  rw [rowFC]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ r : Fin c, ‖wt W c ((r : ℕ) : ℤ) * cexp (2 * π * I * ((n : ℂ) * (r : ℕ) / c))‖ ≤ wtBound W := by
    intro r
    rw [norm_mul]
    have he : ‖cexp (2 * π * I * ((n : ℂ) * (r : ℕ) / c))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [he, mul_one]; exact norm_wt_le W _ _
  calc ∑ r : Fin c, _ ≤ ∑ _r : Fin c, wtBound W := Finset.sum_le_sum fun r _ => this r
    _ = c * wtBound W := by simp

/-- The coefficient $a_W(c, n) = -4\pi^2c^{-2}\,n\,\hat W(c, n)$ of $q^n$ in row $c$. -/
noncomputable def rowCoeff (W : ZMod N → ZMod N → ℂ) (c n : ℕ) : ℂ :=
  (-4 * (π : ℂ) ^ 2) / (c : ℂ) ^ 2 * n * rowFC W c n

lemma norm_rowCoeff_le {W : ZMod N → ZMod N → ℂ} (hT : IsTInv W) (c n : ℕ) (hc : 0 < c) :
    ‖rowCoeff W c n‖ ≤ 4 * π ^ 2 * wtBound W * N * (n : ℝ) ^ 2 * (((c : ℝ) ^ 2)⁻¹) := by
  have hB : 0 ≤ wtBound W := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  by_cases hd : c ∣ n * N
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [rowCoeff]
    have hle : (c : ℝ) ≤ n * N := by
      exact_mod_cast Nat.le_of_dvd (Nat.mul_pos hn (Nat.pos_of_ne_zero (NeZero.ne N))) hd
    rw [rowCoeff, norm_mul, norm_mul, norm_div, norm_mul, norm_neg, norm_pow, norm_pow, Complex.norm_natCast,
      Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have h1 := norm_rowFC_le W c n
    norm_num
    calc 4 * π ^ 2 / (c : ℝ) ^ 2 * n * ‖rowFC W c n‖ ≤ 4 * π ^ 2 / (c : ℝ) ^ 2 * n * (c * wtBound W) := by
          gcongr
      _ = 4 * π ^ 2 * wtBound W * n * c * ((c : ℝ) ^ 2)⁻¹ := by field_simp
      _ ≤ 4 * π ^ 2 * wtBound W * n * (n * N) * ((c : ℝ) ^ 2)⁻¹ := by gcongr
      _ = _ := by ring
  · rw [rowCoeff, rowFC_eq_zero hT hc hd, mul_zero, norm_zero]
    positivity

lemma norm_cexp_tau_lt_one (τ : ℍ) : ‖cexp (2 * π * I * τ)‖ < 1 := by
  rw [norm_cexp_two_pi_I]
  have := τ.im_pos
  have hp := Real.pi_pos
  exact Real.exp_lt_one_iff.mpr (by simp only [UpperHalfPlane.coe_im]; nlinarith)

/-- **Row $c \ge 1$ of $E_W$ as a $q$-series:** $\sum_d W(c, d)(c\tau + d)^{-2} = \sum_n a_W(c, n)q^n$. -/
theorem hasSum_rowW {W : ZMod N → ZMod N → ℂ} (hT : IsTInv W) {c : ℕ} (hc : 0 < c) (τ : ℍ) :
    HasSum (fun n : ℕ => rowCoeff W c n * cexp (2 * π * I * τ) ^ n) (rowW W c τ) := by
  have : NeZero c := ⟨hc.ne'⟩
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  set q := cexp (2 * π * I * τ) with hq
  have hrow : rowW W c τ = ∑' d : ℤ, wt W c d * (((c : ℂ) * τ + d) ^ 2)⁻¹ := by
    simp only [rowW, Int.cast_natCast]
  rw [hrow, row_expansion (M := c) (β := fun d => wt W c d) (fun d => wt_add_self hT c d)
    (fun d => norm_wt_le W c d) hc τ]
  have hX : ∀ (r : Fin c) (n : ℕ), cexp (2 * π * I * (((c : ℂ) * τ + (r : ℕ)) / c)) ^ n =
      q ^ n * cexp (2 * π * I * ((n : ℂ) * (r : ℕ) / c)) := by
    intro r n
    rw [hq, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1; field_simp
  have hgeo : ∀ r : Fin c, HasSum (fun n : ℕ => (n : ℂ) * cexp (2 * π * I * (((c : ℂ) * τ + (r : ℕ)) / c)) ^ n)
      (∑' n : ℕ, (n : ℂ) * cexp (2 * π * I * (((c : ℂ) * τ + (r : ℕ)) / c)) ^ n) := by
    intro r
    have hnorm : ‖cexp (2 * π * I * (((c : ℂ) * τ + (r : ℕ)) / c))‖ < 1 := by
      have h1 := hX r 1
      rw [pow_one, pow_one] at h1
      rw [h1, norm_mul]
      have : ‖cexp (2 * π * I * (((1 : ℕ) : ℂ) * (r : ℕ) / c))‖ = 1 := by
        rw [Complex.norm_exp]; simp
      rw [this, mul_one, hq]; exact norm_cexp_tau_lt_one τ
    exact (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable.hasSum
  have hs := (hasSum_sum fun r (_ : r ∈ Finset.univ) => (hgeo r).mul_left ((fun d : ℤ => wt W c d) r)).mul_left
    ((-2 * π * I) ^ 2 / (c : ℂ) ^ 2)
  refine hs.congr_fun fun n => ?_
  simp only [rowCoeff, rowFC, hX]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have : (-2 * (π : ℂ) * I) ^ 2 = -4 * (π : ℂ) ^ 2 := by ring_nf; rw [I_sq]; ring
  rw [this]
  ring

lemma rowW_neg {W : ZMod N → ZMod N → ℂ} (he : IsEvenW W) (c : ℤ) (w : ℂ) : rowW W (-c) w = rowW W c w := by
  simp only [rowW]
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun d => ?_
  simp only [Equiv.neg_apply, wt]
  push_cast
  rw [he]
  congr 2
  ring

lemma summable_rowW (W : ZMod N → ZMod N → ℂ) (τ : ℍ) : Summable fun c : ℤ => rowW W c τ := by
  refine Summable.of_norm_bounded
    ((summable_rowBound (N := N) (B := wtBound W) τ.im_pos).update 0 ‖rowW W 0 τ‖) fun c => ?_
  by_cases hc : c = 0
  · subst hc; simp
  · simp only [Function.update_of_ne hc]
    exact norm_rowW_le W hc τ

/-- $E_W = $ row $0$ $+ 2\sum_{c \ge 1}$ row $c$ (evenness). -/
lemma eis2_eq_rows {W : ZMod N → ZMod N → ℂ} (he : IsEvenW W) (τ : ℍ) :
    eis2 W τ = rowW W 0 τ + 2 * ∑' c : ℕ+, rowW W ((c : ℕ) : ℤ) τ := by
  rw [eis2_eq_tsum_rowW, tsum_int_eq_zero_add_two_mul_tsum_pnat (fun c => rowW_neg he c τ) (summable_rowW W τ),
    nsmul_eq_mul]
  push_cast
  rfl

/-- **The $q$-coefficients of $E_W$:** $e_W(n) = [n = 0]\,\mathrm{row}_0 + 2\sum_{c \ge 1}a_W(c, n)$. -/
noncomputable def eisCoeff (W : ZMod N → ZMod N → ℂ) (n : ℕ) : ℂ :=
  (if n = 0 then rowW W 0 0 else 0) + 2 * ∑' c : ℕ+, rowCoeff W c n

lemma summable_rowCoeff_prod {W : ZMod N → ZMod N → ℂ} (hT : IsTInv W) (τ : ℍ) :
    Summable fun p : ℕ+ × ℕ => rowCoeff W p.1 p.2 * cexp (2 * π * I * τ) ^ p.2 := by
  set x := ‖cexp (2 * π * I * τ)‖
  have hx : x < 1 := norm_cexp_tau_lt_one τ
  have hs1 : Summable fun c : ℕ+ => (((c : ℕ) : ℝ) ^ 2)⁻¹ := summable_pnat_inv_sq
  have hs2 : Summable fun n : ℕ => (n : ℝ) ^ 2 * x ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 2 (by rwa [Real.norm_of_nonneg (norm_nonneg _)])
  refine Summable.of_norm_bounded (((hs1.mul_of_nonneg hs2 (fun _ => by positivity)
    (fun _ => by positivity))).mul_left (4 * π ^ 2 * wtBound W * N)) fun p => ?_
  rw [norm_mul, norm_pow]
  have h := norm_rowCoeff_le hT p.1 p.2 p.1.pos
  calc ‖rowCoeff W p.1 p.2‖ * x ^ p.2 ≤
        (4 * π ^ 2 * wtBound W * N * (p.2 : ℝ) ^ 2 * ((((p.1 : ℕ) : ℝ) ^ 2)⁻¹)) * x ^ p.2 := by
        gcongr
    _ = _ := by ring

/-- **The $q$-expansion of $E_W$** for $T$-invariant even $W$. -/
theorem hasSum_eis2 {W : ZMod N → ZMod N → ℂ} (hT : IsTInv W) (he : IsEvenW W) (τ : ℍ) :
    HasSum (fun n : ℕ => eisCoeff W n * cexp (2 * π * I * τ) ^ n) (eis2 W τ) := by
  set q := cexp (2 * π * I * τ)
  have hsum := summable_rowCoeff_prod hT τ
  -- rows: summing over `n` first
  have hrows : ∀ c : ℕ+, ∑' n : ℕ, rowCoeff W c n * q ^ n = rowW W ((c : ℕ) : ℤ) τ := fun c =>
    (hasSum_rowW hT c.pos τ).tsum_eq
  have hA : HasSum (fun c : ℕ+ => ∑' n : ℕ, rowCoeff W c n * q ^ n) (∑' p : ℕ+ × ℕ, rowCoeff W p.1 p.2 * q ^ p.2) :=
    hsum.hasSum.prod_fiberwise fun c => (hsum.prod_factor c).hasSum
  have hB : HasSum (fun n : ℕ => ∑' c : ℕ+, rowCoeff W c n * q ^ n)
      (∑' p : ℕ+ × ℕ, rowCoeff W p.1 p.2 * q ^ p.2) := by
    have hsw : Summable fun p : ℕ × ℕ+ => rowCoeff W p.2 p.1 * q ^ p.1 :=
      (Equiv.prodComm ℕ ℕ+).summable_iff.mpr hsum
    have := hsw.hasSum.prod_fiberwise fun n => (hsw.prod_factor n).hasSum
    rw [← (Equiv.prodComm ℕ ℕ+).tsum_eq]
    simpa using this
  have hpos : ∑' c : ℕ+, rowW W ((c : ℕ) : ℤ) τ = ∑' p : ℕ+ × ℕ, rowCoeff W p.1 p.2 * q ^ p.2 := by
    rw [← hA.tsum_eq]; exact (tsum_congr hrows).symm
  rw [eis2_eq_rows he, hpos]
  have h0 : HasSum (fun n : ℕ => (if n = 0 then rowW W 0 0 else 0) * q ^ n) (rowW W 0 τ) := by
    rw [rowW_zero W τ 0]
    convert hasSum_ite_eq 0 (rowW W 0 0) using 1
    ext n; split_ifs with h <;> simp [h]
  refine (h0.add (hB.mul_left 2)).congr_fun fun n => ?_
  simp only [eisCoeff, tsum_mul_right]
  ring

end QuadFormsKB.Siegel.GenusEis
