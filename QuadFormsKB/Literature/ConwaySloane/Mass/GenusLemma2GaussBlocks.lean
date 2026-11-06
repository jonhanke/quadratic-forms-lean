/-
# Conway–Sloane, LDL IV, §11, Lemma 2 at $p = 2$: Gauss sums of the blocks
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemma2GaussBase

set_option linter.unusedSectionVars false

open Matrix QuadFormsKB QuadFormsKB.Analysis QuadFormsKB.Cassels Finset

namespace QuadFormsKB.ConwaySloane.Mass.Gauss2

theorem norm_two : ‖(2 : ℚ_[2])‖ = 1 / 2 := by
  have := Padic.norm_p (p := 2)
  simpa using this

theorem zi_nat (n : ℕ) : ‖(n : ℚ_[2])‖ ≤ 1 := by
  have := Padic.norm_int_le_one (p := 2) (n : ℤ)
  simpa using this

theorem zi_int (n : ℤ) : ‖(n : ℚ_[2])‖ ≤ 1 := Padic.norm_int_le_one n

theorem zi_add {a b : ℚ_[2]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

theorem zi_sub {a b : ℚ_[2]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]; exact zi_add ha (by rwa [norm_neg])

theorem zi_mul {a b : ℚ_[2]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb

theorem zi_pow {a : ℚ_[2]} (ha : ‖a‖ ≤ 1) (n : ℕ) : ‖a ^ n‖ ≤ 1 := by
  rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha

theorem zi_two : ‖(2 : ℚ_[2])‖ ≤ 1 := by rw [norm_two]; norm_num

theorem zi_neg {a : ℚ_[2]} (ha : ‖a‖ ≤ 1) : ‖-a‖ ≤ 1 := by rwa [norm_neg]

theorem zi_one : ‖(1 : ℚ_[2])‖ ≤ 1 := by simp

theorem ch_two_mul {a : ℚ_[2]} (ha : ‖a‖ ≤ 1) : ch (2 * a) = 1 := by
  apply ch_eq_one
  have : (2 * a) / 2 = a := by field_simp
  rwa [this]

theorem ch_add_two_mul (x : ℚ_[2]) {a : ℚ_[2]} (ha : ‖a‖ ≤ 1) : ch (x + 2 * a) = ch x := by
  rw [ch_add, ch_two_mul ha, mul_one]

theorem ch_nat_mul (n : ℕ) (x : ℚ_[2]) : ch ((n : ℚ_[2]) * x) = ch x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, ch_add, ih, pow_succ]

theorem ch_one : ch 1 = -1 := by
  have hr : Analysis.IsPFrac 2 (1 / 2 : ℚ) := ⟨1, 1, by simp⟩
  have h := psiP_pFrac hr
  unfold ch
  have : ((1 : ℚ_[2]) / 2) = (((1 / 2 : ℚ)) : ℚ_[2]) := by push_cast; rfl
  rw [this, h, Real.fourierChar_apply', Circle.coe_exp]
  have e : (((2 * Real.pi * (-((1 / 2 : ℚ) : ℝ)) : ℝ) : ℂ)) * Complex.I = -(Real.pi * Complex.I) := by
    push_cast; ring
  rw [e, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num

theorem zeta8_def_val : zeta8 = Complex.exp (↑(2 * Real.pi * (-(1/8 : ℝ))) * Complex.I) := by
  have hr : Analysis.IsPFrac 2 (1 / 8 : ℚ) := ⟨1, 3, by norm_num⟩
  have h := psiP_pFrac hr
  unfold zeta8 ch
  have : ((1 : ℚ_[2]) / 4 / 2) = (((1 / 8 : ℚ)) : ℚ_[2]) := by push_cast; ring
  rw [this, h, Real.fourierChar_apply', Circle.coe_exp]
  push_cast; ring_nf

theorem zeta8_eq : zeta8 = ((Real.sqrt 2 : ℂ) / 2) - ((Real.sqrt 2 : ℂ) / 2) * Complex.I := by
  have hx : 2 * Real.pi * (-(1/8 : ℝ)) = -(Real.pi / 4) := by ring
  apply Complex.ext
  · rw [zeta8_def_val, Complex.exp_ofReal_mul_I_re, hx, Real.cos_neg, Real.cos_pi_div_four]
    simp
  · rw [zeta8_def_val, Complex.exp_ofReal_mul_I_im, hx, Real.sin_neg, Real.sin_pi_div_four]
    simp

theorem sqrt2_sq : ((Real.sqrt 2 : ℂ)) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow]; simp

theorem I_sq : Complex.I ^ 2 = -1 := Complex.I_sq

theorem zeta8_sq : zeta8 ^ 2 = -Complex.I := by
  rw [zeta8_eq]
  linear_combination ((1 - 2 * Complex.I + Complex.I ^ 2) / 4) * sqrt2_sq + (1 / 2) * I_sq

theorem zeta8_pow_four : zeta8 ^ 4 = -1 := by
  rw [show 4 = 2 * 2 by rfl, pow_mul, zeta8_sq]; simp

theorem zeta8_pow_eight : zeta8 ^ 8 = 1 := by
  rw [show 8 = 4 * 2 by rfl, pow_mul, zeta8_pow_four]; simp

theorem norm_zeta8 : ‖zeta8‖ = 1 := by
  unfold zeta8 ch; exact Circle.norm_coe _

theorem zeta8_ne_zero : zeta8 ≠ 0 := by
  intro h; have := norm_zeta8; rw [h] at this; simp at this

theorem zeta8_pow_ne_one {k : ℕ} (h1 : 0 < k) (h8 : k < 8) : zeta8 ^ k ≠ 1 := by
  intro hk
  have hg := pow_gcd_eq_one.mpr ⟨hk, zeta8_pow_eight⟩
  have hne1 : zeta8 ≠ 1 := by
    intro h; rw [h] at hg
    have := zeta8_sq; rw [h] at this; simp at this
    have := congrArg Complex.im this; simp at this
  interval_cases k <;> norm_num at hg
  · exact hne1 hg
  · rcases hg with h | h <;>
      (have := zeta8_sq; rw [h] at this; have := congrArg Complex.im this; simp at this)
  · exact hne1 hg
  · have := zeta8_pow_four; rw [hg] at this; norm_num at this
  · exact hne1 hg
  · rcases hg with h | h <;>
      (have := zeta8_sq; rw [h] at this; have := congrArg Complex.im this; simp at this)
  · exact hne1 hg

theorem zeta8_pow_inj {a b : ℕ} (ha : a < 8) (hb : b < 8) (h : zeta8 ^ a = zeta8 ^ b) : a = b := by
  have key : ∀ a b : ℕ, a < b → b < 8 → zeta8 ^ a = zeta8 ^ b → False := by
    intro a b hab hb h
    have : zeta8 ^ (b - a) = 1 := by
      have h2 : zeta8 ^ a * zeta8 ^ (b - a) = zeta8 ^ a * 1 := by
        rw [← pow_add, Nat.add_sub_cancel' hab.le, mul_one, h]
      exact mul_left_cancel₀ (pow_ne_zero _ zeta8_ne_zero) h2
    exact zeta8_pow_ne_one (by omega) (by omega) this
  rcases lt_trichotomy a b with h' | h' | h'
  · exact (key a b h' hb h).elim
  · exact h'
  · exact (key b a h' ha h.symm).elim

theorem ch_quarter (k : ℕ) : ch ((k : ℚ_[2]) / 4) = zeta8 ^ k := by
  have := ch_nat_mul k (1 / 4)
  rw [mul_one_div] at this
  rw [this]; rfl

theorem ch_natCast' (n : ℕ) : ch (n : ℚ_[2]) = (-1) ^ n := by
  have := ch_nat_mul n 1
  rw [mul_one, ch_one] at this; exact this

theorem zeta_pow_mod (n : ℕ) : zeta8 ^ (n % 8) = zeta8 ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 8, pow_add, pow_mul, zeta8_pow_eight, one_pow, mul_one]

/-- $\zeta_8^a$ for $a \in \mathbb Z/8$. -/
noncomputable def zpw (a : ZMod 8) : ℂ := zeta8 ^ a.val

theorem zpw_add (a b : ZMod 8) : zpw (a + b) = zpw a * zpw b := by
  unfold zpw; rw [ZMod.val_add, zeta_pow_mod, pow_add]

theorem zpw_nat (n : ℕ) : zpw (n : ZMod 8) = zeta8 ^ n := by
  unfold zpw; rw [ZMod.val_natCast, zeta_pow_mod]

theorem sum_range_mul_periodic (f : ℕ → ℂ) (N : ℕ) (hf : ∀ x, f (x + N) = f x) (k : ℕ) :
    ∑ x ∈ range (N * k), f x = k * ∑ x ∈ range N, f x := by
  have hp : ∀ k x, f (N * k + x) = f x := by
    intro k; induction k with
    | zero => intro x; simp
    | succ k ih => intro x; rw [Nat.mul_succ, add_assoc, add_comm N, ← add_assoc, hf, ih]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp only [hp]; push_cast; ring

theorem sum1 (g : ℕ → ℂ) (N : ℕ) :
    ∑ f : Fin 1 → Fin N, g (f 0) = ∑ x ∈ range N, g x := by
  rw [← Fin.sum_univ_eq_sum_range (fun x => g x) N]
  exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin N)) _ _ (fun f => rfl)

theorem sum2 (g : ℕ → ℕ → ℂ) (N : ℕ) :
    ∑ f : Fin 2 → Fin N, g (f 0) (f 1) = ∑ x ∈ range N, ∑ y ∈ range N, g x y := by
  have h := Fintype.sum_equiv (piFinTwoEquiv (fun _ : Fin 2 => Fin N))
    (fun f : Fin 2 → Fin N => g (f 0) (f 1)) (fun p : Fin N × Fin N => g p.1 p.2) (fun f => rfl)
  rw [h, Fintype.sum_prod_type]
  rw [← Fin.sum_univ_eq_sum_range (fun x => ∑ y ∈ range N, g x y) N]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact Fin.sum_univ_eq_sum_range (fun y => g x y) N

theorem qv_one (a : ℚ_[2]) (v : Fin 1 → ℚ_[2]) : qv (!![a] : Matrix (Fin 1) (Fin 1) ℚ_[2]) v = v 0 * (a * v 0) := by
  simp [qv, dotProduct, Matrix.mulVec, Fin.sum_univ_one]

theorem blockGauss_sq_eq (e u : ℤ) (he : 0 ≤ e) (hu0 : u ≠ 0) (m : ℕ) :
    blockGauss (.sq e u) m = ∑ x ∈ range (2 ^ e.toNat),
      ch ((2 : ℚ_[2]) ^ m * ((x : ℚ_[2]) * (x * ((2 : ℚ_[2]) ^ e.toNat * u)⁻¹))) := by
  unfold blockGauss
  have h2 : (2 : ℚ_[2]) ^ e.toNat * u ≠ 0 := mul_ne_zero (pow_ne_zero _ two_ne_zero) (by exact_mod_cast hu0)
  have hinv : (DyBlock.sq e u).mat⁻¹ = !![((2 : ℚ_[2]) ^ e.toNat * u)⁻¹] := by
    apply Matrix.inv_eq_right_inv
    show !![(2 : ℚ_[2]) ^ e * u] * !![((2 : ℚ_[2]) ^ e.toNat * u)⁻¹] = 1
    rw [TwoAdic.zpow_eq_pow_toNat he]
    have hu' : (u : ℚ_[2]) ≠ 0 := by exact_mod_cast hu0
    ext i j; fin_cases i; fin_cases j; simp; field_simp
  rw [hinv]
  have := sum1 (fun x => ch ((2 : ℚ_[2]) ^ m * ((x : ℚ_[2]) * (x * ((2 : ℚ_[2]) ^ e.toNat * u)⁻¹)))) (2 ^ e.toNat)
  rw [← this]
  refine Finset.sum_congr rfl fun f _ => ?_
  show ch ((2 : ℚ_[2]) ^ m * qv (!![((2 : ℚ_[2]) ^ e.toNat * u)⁻¹] : Matrix (Fin 1) (Fin 1) ℚ_[2])
    (natVec (N := fun _ => 2 ^ e.toNat) f)) = _
  rw [qv_one]
  simp only [natVec]
  push_cast
  rw [mul_comm (((2 : ℚ_[2]) ^ e.toNat * u)⁻¹)]

/-! ### The one-variable sums -/

/-- $S_j(w) = \sum_{x < 2^j} \mathrm{ch}(w x^2 / 2^j)$. -/
noncomputable def Ssum (w : ℚ_[2]) (j : ℕ) : ℂ :=
  ∑ x ∈ range (2 ^ j), ch (w * ((x : ℚ_[2]) * x) / 2 ^ j)

theorem ch_w_nat {w : ℚ_[2]} (hw1 : ‖(w - 1) / 2‖ ≤ 1) (n : ℕ) : ch (w * n) = (-1) ^ n := by
  have : w * n = n + 2 * ((w - 1) / 2 * n) := by ring
  rw [this, ch_add_two_mul _ (zi_mul hw1 (zi_nat n)), ch_natCast']

theorem even_sum (g : ℕ → ℂ) (K : ℕ) :
    ∑ x ∈ range (2 * K), g x * (1 + (-1) ^ x) = 2 * ∑ z ∈ range K, g (2 * z) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih, sum_range_succ]
    simp [pow_succ, pow_mul]
    ring

theorem Ssum_rec {w : ℚ_[2]} (hw0 : ‖w‖ ≤ 1) (hw1 : ‖(w - 1) / 2‖ ≤ 1) (i : ℕ) :
    Ssum w (i + 3) = 2 * Ssum w (i + 1) := by
  unfold Ssum
  have e1 : 2 ^ (i + 3) = 2 ^ (i + 2) + 2 ^ (i + 2) := by ring
  have hshift : ∀ x : ℕ, ch (w * (((2 ^ (i + 2) + x : ℕ) : ℚ_[2]) * ((2 ^ (i + 2) + x : ℕ) : ℚ_[2])) / 2 ^ (i + 3))
      = ch (w * ((x : ℚ_[2]) * x) / 2 ^ (i + 3)) * (-1) ^ x := by
    intro x
    push_cast
    have : w * (((2 : ℚ_[2]) ^ (i + 2) + x) * ((2 : ℚ_[2]) ^ (i + 2) + x)) / 2 ^ (i + 3)
        = w * ((x : ℚ_[2]) * x) / 2 ^ (i + 3) + w * x + 2 * (w * 2 ^ i) := by
      field_simp; ring
    rw [this, ch_add_two_mul _ (zi_mul hw0 (zi_pow zi_two i)), ch_add, ch_w_nat hw1 x]
  rw [e1, sum_range_add]
  simp_rw [hshift]
  rw [← sum_add_distrib]
  have := even_sum (fun x : ℕ => ch (w * ((x : ℚ_[2]) * x) / 2 ^ (i + 3))) (2 ^ (i + 1))
  rw [show 2 * 2 ^ (i + 1) = 2 ^ (i + 2) by ring] at this
  simp only [mul_add, mul_one] at this
  rw [this]
  congr 1
  apply sum_congr rfl
  intro z _
  congr 1
  push_cast
  field_simp
  ring

theorem norm_div_two_pow (a : ℚ_[2]) (k : ℕ) : ‖a / 2 ^ k‖ = ‖a‖ * 2 ^ k := by
  rw [norm_div, norm_pow, norm_two, one_div, inv_pow, div_inv_eq_mul]

theorem w_facts {w : ℚ_[2]} {c : ℕ} (hc : c = 1 ∨ c = 3 ∨ c = 5 ∨ c = 7) (hw : ‖w - c‖ ≤ 1 / 8) :
    ‖w‖ ≤ 1 ∧ ‖(w - 1) / 2‖ ≤ 1 := by
  have hz : ‖w - c‖ ≤ 1 := hw.trans (by norm_num)
  constructor
  · have : w = (w - c) + c := by ring
    rw [this]; exact zi_add hz (zi_nat c)
  · obtain ⟨d, hd⟩ : ∃ d : ℕ, c = 2 * d + 1 := by
      rcases hc with h | h | h | h
      exacts [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩]
    have : (w - 1) / 2 = (w - c) / 2 ^ 1 + d := by
      rw [hd]; push_cast; field_simp; ring
    rw [this]
    refine zi_add ?_ (zi_nat d)
    rw [norm_div_two_pow]; linarith

theorem ch_w_half {w : ℚ_[2]} {c : ℕ} (hw : ‖w - c‖ ≤ 1 / 8) : ch (w / 2) = zeta8 ^ (2 * c) := by
  rw [← ch_quarter]
  have : w / 2 = ((2 * c : ℕ) : ℚ_[2]) / 4 + 2 * ((w - c) / 2 ^ 2) := by push_cast; field_simp; ring
  rw [this, ch_add_two_mul]
  rw [norm_div_two_pow]; linarith

theorem ch_w_quarter {w : ℚ_[2]} {c : ℕ} (hw : ‖w - c‖ ≤ 1 / 8) : ch (w / 4) = zeta8 ^ c := by
  rw [← ch_quarter]
  have : w / 4 = (c : ℚ_[2]) / 4 + 2 * ((w - c) / 2 ^ 3) := by field_simp; ring
  rw [this, ch_add_two_mul]
  rw [norm_div_two_pow]; linarith

theorem Ssum_one (w : ℚ_[2]) : Ssum w 1 = 1 + ch (w / 2) := by
  simp [Ssum, sum_range_succ]

theorem Ssum_two {w : ℚ_[2]} (hw0 : ‖w‖ ≤ 1) (hw1 : ‖(w - 1) / 2‖ ≤ 1) : Ssum w 2 = 2 * ch (w / 4) := by
  have h2 : ch (w * ((2 : ℚ_[2]) * 2) / 2 ^ 2) = -1 := by
    have := ch_w_nat hw1 1
    rw [Nat.cast_one, mul_one] at this
    rw [show w * ((2 : ℚ_[2]) * 2) / 2 ^ 2 = w by first | ring | field_simp, this]; norm_num
  have h3 : ch (w * ((3 : ℚ_[2]) * 3) / 2 ^ 2) = ch (w / 4) := by
    have : w * ((3 : ℚ_[2]) * 3) / 2 ^ 2 = w / 4 + 2 * w := by field_simp; ring
    rw [this, ch_add_two_mul _ hw0]
  unfold Ssum
  simp only [Nat.reducePow, sum_range_succ, range_zero, sum_empty]
  push_cast
  rw [h2, h3]
  norm_num
  ring

theorem pow_red (n m : ℕ) (h : n % 8 = m) : zeta8 ^ n = zeta8 ^ m := by
  rw [← zeta_pow_mod, h]

theorem one_add_zeta_sq : 1 + zeta8 ^ 2 = (Real.sqrt 2 : ℂ) * zeta8 := by
  rw [zeta8_sq, zeta8_eq]
  linear_combination (-(1 - Complex.I) / 2) * sqrt2_sq

theorem one_add_zeta_six : 1 + zeta8 ^ 6 = (Real.sqrt 2 : ℂ) * zeta8 ^ 7 := by
  have h6 : zeta8 ^ 6 = Complex.I := by
    rw [show 6 = 4 + 2 by rfl, pow_add, zeta8_pow_four, zeta8_sq]; ring
  have h7 : zeta8 ^ 7 = zeta8 * Complex.I := by
    rw [show 7 = 6 + 1 by rfl, pow_add, h6]; ring
  rw [h6, h7, zeta8_eq]
  linear_combination (-(Complex.I - Complex.I ^ 2) / 2) * sqrt2_sq + I_sq

/-- The phase of $S_j$ for the unit $\equiv c \pmod 8$. -/
def ph (c j : ℕ) : ZMod 8 := (c : ZMod 8) + 4 * (j : ZMod 8) * (if c = 3 ∨ c = 5 then 1 else 0)

theorem ph_add_two (c j : ℕ) : ph c (j + 2) = ph c j := by
  unfold ph; push_cast
  have h8 : (8 : ZMod 8) = 0 := by decide
  linear_combination (if c = 3 ∨ c = 5 then (1 : ZMod 8) else 0) * h8

theorem ph_two (c : ℕ) : ph c 2 = (c : ZMod 8) := by
  unfold ph; push_cast
  have h8 : (8 : ZMod 8) = 0 := by decide
  linear_combination (if c = 3 ∨ c = 5 then (1 : ZMod 8) else 0) * h8

theorem Ssum_form {w : ℚ_[2]} {c : ℕ} (hc : c = 1 ∨ c = 3 ∨ c = 5 ∨ c = 7) (hw : ‖w - c‖ ≤ 1 / 8) :
    ∀ j, 1 ≤ j → ∃ r : ℝ, 0 < r ∧ Ssum w j = r * zpw (ph c j) := by
  obtain ⟨hw0, hw1⟩ := w_facts hc hw
  have base1 : ∃ r : ℝ, 0 < r ∧ Ssum w 1 = r * zpw (ph c 1) := by
    rw [Ssum_one, ch_w_half hw]
    refine ⟨Real.sqrt 2, by positivity, ?_⟩
    rcases hc with rfl | rfl | rfl | rfl
    · have : ph 1 1 = ((1 : ℕ) : ZMod 8) := by unfold ph; decide
      rw [this, zpw_nat]; simpa using one_add_zeta_sq
    · have : ph 3 1 = ((7 : ℕ) : ZMod 8) := by unfold ph; decide
      rw [this, zpw_nat]; exact one_add_zeta_six
    · have : ph 5 1 = ((1 : ℕ) : ZMod 8) := by unfold ph; decide
      rw [this, zpw_nat, pow_red (2 * 5) 2 (by norm_num)]; simpa using one_add_zeta_sq
    · have : ph 7 1 = ((7 : ℕ) : ZMod 8) := by unfold ph; decide
      rw [this, zpw_nat, pow_red (2 * 7) 6 (by norm_num)]; exact one_add_zeta_six
  have base2 : ∃ r : ℝ, 0 < r ∧ Ssum w 2 = r * zpw (ph c 2) := by
    refine ⟨2, by norm_num, ?_⟩
    rw [Ssum_two hw0 hw1, ch_w_quarter hw, ph_two, zpw_nat]; push_cast; ring
  have key : ∀ i, (∃ r : ℝ, 0 < r ∧ Ssum w (i + 1) = r * zpw (ph c (i + 1))) ∧
      (∃ r : ℝ, 0 < r ∧ Ssum w (i + 2) = r * zpw (ph c (i + 2))) := by
    intro i
    induction i with
    | zero => exact ⟨base1, base2⟩
    | succ i ih =>
      refine ⟨ih.2, ?_⟩
      obtain ⟨r, hr, h⟩ := ih.1
      refine ⟨2 * r, by positivity, ?_⟩
      show Ssum w (i + 3) = _
      rw [Ssum_rec hw0 hw1, h, show i + 1 + 2 = (i + 1) + 2 from rfl, ph_add_two]
      push_cast; ring
  intro j hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  exact (key i).1

/-! ### The odd blocks -/

theorem norm_nat_odd {c : ℕ} (hc : Odd c) : ‖(c : ℚ_[2])‖ = 1 := by
  have := TwoAdic.norm_intCast_odd (u := (c : ℤ)) (by exact_mod_cast hc)
  simpa using this

theorem odd_of_four {c : ℕ} (hc : c = 1 ∨ c = 3 ∨ c = 5 ∨ c = 7) : Odd c := by
  rcases hc with rfl | rfl | rfl | rfl <;> decide

theorem zi_inv_nat {c : ℕ} (hc : c = 1 ∨ c = 3 ∨ c = 5 ∨ c = 7) : ‖(c : ℚ_[2])⁻¹‖ ≤ 1 := by
  rw [norm_inv, norm_nat_odd (odd_of_four hc)]; simp

theorem inv_close {c : ℕ} (hc : c = 1 ∨ c = 3 ∨ c = 5 ∨ c = 7) :
    ‖(c : ℚ_[2])⁻¹ - c‖ ≤ 1 / 8 := by
  have hn : ‖(c : ℚ_[2])‖ = 1 := norm_nat_odd (odd_of_four hc)
  have hc0 : (c : ℚ_[2]) ≠ 0 := by intro h; rw [h] at hn; simp at hn
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (c : ℚ_[2])⁻¹ - c = -(2 ^ 3 * k) * (c : ℚ_[2])⁻¹ := by
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by push_cast; field_simp; norm_num⟩
    · exact ⟨3, by push_cast; field_simp; norm_num⟩
    · exact ⟨6, by push_cast; field_simp; norm_num⟩
  rw [hk, norm_mul, norm_neg, norm_mul, norm_inv, hn, norm_pow, norm_two]
  have := zi_nat k
  norm_num
  nlinarith [norm_nonneg (k : ℚ_[2])]

theorem neg_one_pow_mul_self (x : ℕ) : ((-1 : ℂ)) ^ (x * x) = (-1) ^ x := by
  rcases Nat.even_or_odd x with h | h
  · rw [(h.mul_right x).neg_one_pow, h.neg_one_pow]
  · rw [(h.mul h).neg_one_pow, h.neg_one_pow]

theorem sum_alt (K : ℕ) : ∑ x ∈ range (2 * K), ((-1 : ℂ)) ^ x = 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih]
    simp [pow_succ, pow_mul]

theorem sq_lt {c : ℕ} (hc : c = 1 ∨ c = 3 ∨ c = 5 ∨ c = 7) (E m : ℕ) (h : E < m) :
    ∑ x ∈ range (2 ^ E), ch ((2 : ℚ_[2]) ^ m * ((x : ℚ_[2]) * (x * ((2 : ℚ_[2]) ^ E * c)⁻¹)))
      = (2 : ℂ) ^ E := by
  obtain ⟨d, hd⟩ : ∃ d, m = E + d + 1 := ⟨m - E - 1, by omega⟩
  have hc0 : (c : ℚ_[2]) ≠ 0 := by
    have := norm_nat_odd (odd_of_four hc); intro h; rw [h] at this; simp at this
  have : ∀ x ∈ range (2 ^ E),
      ch ((2 : ℚ_[2]) ^ m * ((x : ℚ_[2]) * (x * ((2 : ℚ_[2]) ^ E * c)⁻¹))) = 1 := by
    intro x _
    have e : (2 : ℚ_[2]) ^ m * ((x : ℚ_[2]) * (x * ((2 : ℚ_[2]) ^ E * c)⁻¹))
        = 2 * (2 ^ d * ((x : ℚ_[2]) * x * (c : ℚ_[2])⁻¹)) := by
      rw [hd]; field_simp; ring
    rw [e, ch_two_mul]
    exact zi_mul (zi_pow zi_two d) (zi_mul (zi_mul (zi_nat x) (zi_nat x)) (zi_inv_nat hc))
  rw [Finset.sum_congr rfl this]
  simp

theorem sq_zero0 {c : ℕ} : ∑ x ∈ range (2 ^ 0), ch ((2 : ℚ_[2]) ^ 0 * ((x : ℚ_[2]) * (x * ((2 : ℚ_[2]) ^ 0 * c)⁻¹)))
      = 1 := by
  simp

theorem sq_eq_zero_sum {c : ℕ} (hc : c = 1 ∨ c = 3 ∨ c = 5 ∨ c = 7) (E : ℕ) (hE : 1 ≤ E) :
    ∑ x ∈ range (2 ^ E), ch ((2 : ℚ_[2]) ^ E * ((x : ℚ_[2]) * (x * ((2 : ℚ_[2]) ^ E * c)⁻¹))) = 0 := by
  obtain ⟨hw0, hw1⟩ := w_facts hc (inv_close hc)
  have hc0 : (c : ℚ_[2]) ≠ 0 := by
    have := norm_nat_odd (odd_of_four hc); intro h; rw [h] at this; simp at this
  have : ∀ x ∈ range (2 ^ E),
      ch ((2 : ℚ_[2]) ^ E * ((x : ℚ_[2]) * (x * ((2 : ℚ_[2]) ^ E * c)⁻¹))) = (-1) ^ x := by
    intro x _
    have e : (2 : ℚ_[2]) ^ E * ((x : ℚ_[2]) * (x * ((2 : ℚ_[2]) ^ E * c)⁻¹))
        = (c : ℚ_[2])⁻¹ * ((x * x : ℕ) : ℚ_[2]) := by
      push_cast; field_simp
    rw [e, ch_w_nat hw1, neg_one_pow_mul_self]
  rw [Finset.sum_congr rfl this]
  obtain ⟨K, hK⟩ : ∃ K, 2 ^ E = 2 * K := ⟨2 ^ (E - 1), by
    rw [← pow_succ']; congr 1; omega⟩
  rw [hK]; exact sum_alt K

theorem sq_gt {c : ℕ} (hc : c = 1 ∨ c = 3 ∨ c = 5 ∨ c = 7) (E m : ℕ) (h : m < E) :
    ∃ r : ℝ, 0 < r ∧
      ∑ x ∈ range (2 ^ E), ch ((2 : ℚ_[2]) ^ m * ((x : ℚ_[2]) * (x * ((2 : ℚ_[2]) ^ E * c)⁻¹)))
        = r * zpw (ph c (E - m)) := by
  obtain ⟨i, hi⟩ : ∃ i, E - m = i + 1 := ⟨E - m - 1, by omega⟩
  have hEm : E = m + (i + 1) := by omega
  obtain ⟨hw0, hw1⟩ := w_facts hc (inv_close hc)
  have hc0 : (c : ℚ_[2]) ≠ 0 := by
    have := norm_nat_odd (odd_of_four hc); intro h; rw [h] at this; simp at this
  set w : ℚ_[2] := (c : ℚ_[2])⁻¹ with hwdef
  set f : ℕ → ℂ := fun x => ch (w * ((x : ℚ_[2]) * x) / 2 ^ (i + 1)) with hf
  have hterm : ∀ x : ℕ, ch ((2 : ℚ_[2]) ^ m * ((x : ℚ_[2]) * (x * ((2 : ℚ_[2]) ^ E * c)⁻¹))) = f x := by
    intro x
    simp only [hf, hwdef]
    congr 1
    rw [hEm]; field_simp; ring
  have hper : ∀ x, f (x + 2 ^ (i + 1)) = f x := by
    intro x
    simp only [hf]
    have e : w * (((x + 2 ^ (i + 1) : ℕ) : ℚ_[2]) * ((x + 2 ^ (i + 1) : ℕ) : ℚ_[2])) / 2 ^ (i + 1)
        = w * ((x : ℚ_[2]) * x) / 2 ^ (i + 1) + 2 * (w * x + w * 2 ^ i) := by
      push_cast; field_simp; ring
    rw [e, ch_add_two_mul]
    exact zi_add (zi_mul hw0 (zi_nat x)) (zi_mul hw0 (zi_pow zi_two i))
  simp_rw [hterm]
  have hpow : 2 ^ E = 2 ^ (i + 1) * 2 ^ m := by rw [hEm]; ring
  rw [hpow, sum_range_mul_periodic f _ hper]
  obtain ⟨r, hr, hS⟩ := Ssum_form hc (by simpa [hwdef] using inv_close hc) (i + 1) (by omega)
  refine ⟨2 ^ m * r, by positivity, ?_⟩
  have : ∑ x ∈ range (2 ^ (i + 1)), f x = Ssum w (i + 1) := rfl
  rw [this, hS, hi]; push_cast; ring

theorem sq_param {e u : ℤ} (hv : (DyBlock.sq e u).Valid) :
    ∃ c : ℕ, (c = 1 ∨ c = 3 ∨ c = 5 ∨ c = 7) ∧ u = c := by
  rcases hv with rfl | rfl | rfl | rfl
  exacts [⟨1, by simp, rfl⟩, ⟨3, by simp, rfl⟩, ⟨5, by simp, rfl⟩, ⟨7, by simp, rfl⟩]

theorem blockGauss_sq_nat (e : ℤ) {c : ℕ} (hc : c = 1 ∨ c = 3 ∨ c = 5 ∨ c = 7) (he : 0 ≤ e) (m : ℕ) :
    blockGauss (.sq e (c : ℤ)) m = ∑ x ∈ range (2 ^ e.toNat),
      ch ((2 : ℚ_[2]) ^ m * ((x : ℚ_[2]) * (x * ((2 : ℚ_[2]) ^ e.toNat * c)⁻¹))) := by
  have hu0 : (c : ℤ) ≠ 0 := by
    have := odd_of_four hc; have := this.pos; omega
  rw [blockGauss_sq_eq e c he hu0 m]
  simp only [Int.cast_natCast]

/-- The block Gauss sum vanishes for an odd block at the scale 2^m, m ≥ 1. -/
theorem blockGauss_sq_eq_zero (e u : ℤ) (hv : (DyBlock.sq e u).Valid) (he : 0 ≤ e) {m : ℕ} (hm : 1 ≤ m)
    (hem : bex (DyBlock.sq e u) = m) : blockGauss (DyBlock.sq e u) m = 0 := by
  obtain ⟨c, hc, rfl⟩ := sq_param (u := u) hv
  rw [blockGauss_sq_nat e hc he]
  have : e.toNat = m := hem
  rw [this]
  exact sq_eq_zero_sum hc m hm

theorem blockPhase_sq_pos {e : ℤ} {c : ℕ} (hc : c = 1 ∨ c = 3 ∨ c = 5 ∨ c = 7) {m : ℕ}
    (h : m < bex (DyBlock.sq e (c : ℤ))) : blockPhase (DyBlock.sq e (c : ℤ)) m = ph c (bex (DyBlock.sq e (c : ℤ)) - m) := by
  unfold blockPhase
  rw [if_pos h]
  unfold ph
  have : signInd (blockSign (DyBlock.sq e (c : ℤ))) = if c = 3 ∨ c = 5 then 1 else 0 := by
    show signInd (jacobiTwo (c : ℤ)) = _
    clear h
    rcases hc with rfl | rfl | rfl | rfl <;> decide
  rw [this]
  rfl

theorem blockGauss_eq_sq (e : ℤ) {c : ℕ} (hc : c = 1 ∨ c = 3 ∨ c = 5 ∨ c = 7) (he : 0 ≤ e) (m : ℕ)
    (h : ¬ (bex (DyBlock.sq e (c : ℤ)) = m ∧ 1 ≤ m)) :
    ∃ r : ℝ, 0 < r ∧ blockGauss (DyBlock.sq e (c : ℤ)) m
      = (r : ℂ) * zeta8 ^ (blockPhase (DyBlock.sq e (c : ℤ)) m).val := by
  rw [blockGauss_sq_nat e hc he]
  have hb : bex (DyBlock.sq e (c : ℤ)) = e.toNat := rfl
  rcases lt_trichotomy e.toNat m with hlt | heq | hgt
  · rw [sq_lt hc _ _ hlt]
    refine ⟨2 ^ e.toNat, by positivity, ?_⟩
    have : blockPhase (DyBlock.sq e (c : ℤ)) m = 0 := by
      unfold blockPhase; rw [if_neg]; rw [hb]; omega
    rw [this]; simp
  · have hm0 : m = 0 := by
      by_contra hne
      exact h ⟨by rw [hb]; exact heq, by omega⟩
    subst hm0
    have : e.toNat = 0 := heq
    rw [this, sq_zero0]
    refine ⟨1, by norm_num, ?_⟩
    have : blockPhase (DyBlock.sq e (c : ℤ)) 0 = 0 := by
      unfold blockPhase; rw [if_neg]; rw [hb, ‹e.toNat = 0›]; omega
    rw [this]; simp
  · obtain ⟨r, hr, hS⟩ := sq_gt hc e.toNat m hgt
    refine ⟨r, hr, ?_⟩
    rw [hS, blockPhase_sq_pos hc (by rw [hb]; exact hgt), hb]
    rfl

/-! ### Two-variable sums -/

theorem sum2_periodic (g : ℕ → ℕ → ℂ) (N : ℕ) (hx : ∀ x y, g (x + N) y = g x y)
    (hy : ∀ x y, g x (y + N) = g x y) (k : ℕ) :
    ∑ x ∈ range (N * k), ∑ y ∈ range (N * k), g x y
      = (k : ℂ) ^ 2 * ∑ x ∈ range N, ∑ y ∈ range N, g x y := by
  have h1 : ∀ x, ∑ y ∈ range (N * k), g x y = k * ∑ y ∈ range N, g x y :=
    fun x => sum_range_mul_periodic (g x) N (hy x) k
  simp_rw [h1]
  rw [← mul_sum]
  have h2 := sum_range_mul_periodic (fun x => ∑ y ∈ range N, g x y) N
    (fun x => sum_congr rfl fun y _ => hx x y) k
  rw [h2]; ring

theorem sum2_double (g : ℕ → ℕ → ℂ) (M : ℕ) :
    ∑ x ∈ range (M + M), ∑ y ∈ range (M + M), g x y
      = ∑ x ∈ range M, ∑ y ∈ range M, (g x y + g (M + x) y + g x (M + y) + g (M + x) (M + y)) := by
  have h1 : ∀ x, ∑ y ∈ range (M + M), g x y = ∑ y ∈ range M, g x y + ∑ y ∈ range M, g x (M + y) :=
    fun x => sum_range_add (g x) M M
  rw [sum_range_add]
  simp_rw [h1]
  simp only [sum_add_distrib]
  ring

theorem quad_rec (g : ℕ → ℕ → ℂ) (K : ℕ) (hs : ∀ x y, g x y = g y x)
    (h1 : ∀ x y, g (2 * K + x) y = g x y * (-1) ^ y) :
    ∑ x ∈ range (2 * K + 2 * K), ∑ y ∈ range (2 * K + 2 * K), g x y
      = 4 * ∑ a ∈ range K, ∑ b ∈ range K, g (2 * a) (2 * b) := by
  have h2 : ∀ x y, g x (2 * K + y) = g x y * (-1) ^ x := by
    intro x y; rw [hs x, h1, hs]
  have h3 : ∀ x y, g (2 * K + x) (2 * K + y) = g x y * (-1) ^ x * (-1) ^ y := by
    intro x y
    rw [h1, h2, pow_add, pow_mul]; simp
  have e : ∀ x y, (g x y + g (2 * K + x) y + g x (2 * K + y) + g (2 * K + x) (2 * K + y))
      = g x y * (1 + (-1) ^ x) * (1 + (-1) ^ y) := by
    intro x y; rw [h1, h2, h3]; ring
  rw [sum2_double g (2 * K)]
  simp_rw [e]
  have inner : ∀ x, ∑ y ∈ range (2 * K), g x y * (1 + (-1) ^ x) * (1 + (-1) ^ y)
      = (2 * ∑ b ∈ range K, g x (2 * b)) * (1 + (-1) ^ x) := by
    intro x
    have := even_sum (fun y => g x y * (1 + (-1) ^ x)) K
    rw [this, ← sum_mul]; ring
  simp_rw [inner]
  have := even_sum (fun x => 2 * ∑ b ∈ range K, g x (2 * b)) K
  rw [this, ← mul_sum]; ring

/-- $H_j = \sum_{x,y<2^j}\mathrm{ch}(2xy/2^j)$. -/
noncomputable def Hs (j : ℕ) : ℂ :=
  ∑ x ∈ range (2 ^ j), ∑ y ∈ range (2 ^ j), ch (2 * ((x : ℚ_[2]) * y) / 2 ^ j)

theorem Hs_rec (j : ℕ) : Hs (j + 2) = 4 * Hs j := by
  unfold Hs
  have := quad_rec (fun x y : ℕ => ch (2 * ((x : ℚ_[2]) * y) / 2 ^ (j + 2))) (2 ^ j)
    (fun x y => by simp only [mul_comm (x : ℚ_[2])])
    (fun x y => by
      have e : 2 * (((2 * 2 ^ j + x : ℕ) : ℚ_[2]) * y) / 2 ^ (j + 2)
          = 2 * ((x : ℚ_[2]) * y) / 2 ^ (j + 2) + (y : ℕ) := by
        push_cast; field_simp; ring
      rw [e, ch_add, ch_natCast'])
  rw [show 2 ^ (j + 2) = 2 * 2 ^ j + 2 * 2 ^ j by ring, this]
  congr 1
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  congr 1
  push_cast; field_simp; ring

theorem Hs_val (j : ℕ) : Hs j = 2 ^ j := by
  have key : ∀ i, Hs i = 2 ^ i ∧ Hs (i + 1) = 2 ^ (i + 1) := by
    intro i
    induction i with
    | zero =>
      refine ⟨by simp [Hs], ?_⟩
      simp [Hs, sum_range_succ, ch_one]
      norm_num
    | succ i ih =>
      refine ⟨ih.2, ?_⟩
      rw [show i + 1 + 1 = i + 2 from rfl, Hs_rec, ih.1]; ring
  exact (key j).1

/-- $E_j = \sum_{x,y<2^j}\mathrm{ch}(2(x^2-xy+y^2)/(3\cdot 2^j))$. -/
noncomputable def Es (j : ℕ) : ℂ :=
  ∑ x ∈ range (2 ^ j), ∑ y ∈ range (2 ^ j),
    ch ((3 : ℚ_[2])⁻¹ * (2 * ((x : ℚ_[2]) * x - x * y + y * y)) / 2 ^ j)

theorem zi_inv_three : ‖(3 : ℚ_[2])⁻¹‖ ≤ 1 := by
  simpa using zi_inv_nat (c := 3) (by norm_num)

theorem ch_inv_three : ch ((3 : ℚ_[2])⁻¹) = -1 := by
  have hw := w_facts (c := 3) (w := ((3 : ℕ) : ℚ_[2])⁻¹) (by norm_num) (inv_close (c := 3) (by norm_num))
  have := ch_w_nat hw.2 1
  simpa using this

theorem Es_rec (j : ℕ) : Es (j + 2) = 4 * Es j := by
  unfold Es
  have := quad_rec
    (fun x y : ℕ => ch ((3 : ℚ_[2])⁻¹ * (2 * ((x : ℚ_[2]) * x - x * y + y * y)) / 2 ^ (j + 2))) (2 ^ j)
    (fun x y => by simp only [mul_comm (x : ℚ_[2])]; congr 2; ring)
    (fun x y => by
      have e : (3 : ℚ_[2])⁻¹ * (2 * ((((2 * 2 ^ j + x : ℕ) : ℚ_[2]) * ((2 * 2 ^ j + x : ℕ) : ℚ_[2]))
            - ((2 * 2 ^ j + x : ℕ) : ℚ_[2]) * y + y * y)) / 2 ^ (j + 2)
          = (3 : ℚ_[2])⁻¹ * (2 * ((x : ℚ_[2]) * x - x * y + y * y)) / 2 ^ (j + 2) + (y : ℕ)
            + 2 * ((3 : ℚ_[2])⁻¹ * (x + 2 ^ j - 2 * y)) := by
        push_cast; field_simp; ring
      rw [e, ch_add_two_mul _ (zi_mul zi_inv_three
        (zi_sub (zi_add (zi_nat x) (zi_pow zi_two j)) (zi_mul zi_two (zi_nat y)))), ch_add, ch_natCast'])
  rw [show 2 ^ (j + 2) = 2 * 2 ^ j + 2 * 2 ^ j by ring, this]
  congr 1
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  congr 1
  push_cast; field_simp; ring

theorem Es_val (j : ℕ) : Es j = (-1) ^ j * 2 ^ j := by
  have key : ∀ i, Es i = (-1) ^ i * 2 ^ i ∧ Es (i + 1) = (-1) ^ (i + 1) * 2 ^ (i + 1) := by
    intro i
    induction i with
    | zero =>
      refine ⟨by simp [Es], ?_⟩
      simp [Es, sum_range_succ, ch_inv_three]
      norm_num
    | succ i ih =>
      refine ⟨ih.2, ?_⟩
      rw [show i + 1 + 1 = i + 2 from rfl, Es_rec, ih.1]; ring
  exact (key j).1

/-! ### The binary blocks -/

theorem qv_two (M : Matrix (Fin 2) (Fin 2) ℚ_[2]) (v : Fin 2 → ℚ_[2]) :
    qv M v = v 0 * (M 0 0 * v 0 + M 0 1 * v 1) + v 1 * (M 1 0 * v 0 + M 1 1 * v 1) := by
  simp [qv, dotProduct, Matrix.mulVec, Fin.sum_univ_two]

theorem blockGauss_hyp_eq (e : ℤ) (he : 0 ≤ e) (m : ℕ) :
    blockGauss (.hyp e) m = ∑ x ∈ range (2 ^ e.toNat), ∑ y ∈ range (2 ^ e.toNat),
      ch ((2 : ℚ_[2]) ^ m * (((2 : ℚ_[2]) ^ e.toNat)⁻¹ * (2 * ((x : ℚ_[2]) * y)))) := by
  unfold blockGauss
  have hinv : (DyBlock.hyp e).mat⁻¹ =
      (((2 : ℚ_[2]) ^ e.toNat)⁻¹) • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2]) := by
    apply Matrix.inv_eq_right_inv
    show ((2 : ℚ_[2]) ^ e • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2])) *
      (((2 : ℚ_[2]) ^ e.toNat)⁻¹ • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2])) = 1
    rw [TwoAdic.zpow_eq_pow_toNat he]
    have h2 : (2 : ℚ_[2]) ^ e.toNat ≠ 0 := pow_ne_zero _ two_ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
  rw [hinv]
  rw [← sum2 (fun x y => ch ((2 : ℚ_[2]) ^ m * (((2 : ℚ_[2]) ^ e.toNat)⁻¹ * (2 * ((x : ℚ_[2]) * y)))))
    (2 ^ e.toNat)]
  refine sum_congr rfl fun f _ => ?_
  show ch ((2 : ℚ_[2]) ^ m * qv (((2 : ℚ_[2]) ^ e.toNat)⁻¹ • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2]))
    (natVec (N := fun _ => 2 ^ e.toNat) f)) = _
  rw [qv_two]
  congr 1
  simp [natVec]
  ring

theorem blockGauss_ell_eq (e : ℤ) (he : 0 ≤ e) (m : ℕ) :
    blockGauss (.ell e) m = ∑ x ∈ range (2 ^ e.toNat), ∑ y ∈ range (2 ^ e.toNat),
      ch ((2 : ℚ_[2]) ^ m * (((2 : ℚ_[2]) ^ e.toNat)⁻¹ *
        ((3 : ℚ_[2])⁻¹ * (2 * ((x : ℚ_[2]) * x - x * y + y * y))))) := by
  unfold blockGauss
  have hinv : (DyBlock.ell e).mat⁻¹ =
      (((2 : ℚ_[2]) ^ e.toNat)⁻¹) • (!![2 * (3 : ℚ_[2])⁻¹, -(3 : ℚ_[2])⁻¹; -(3 : ℚ_[2])⁻¹, 2 * (3 : ℚ_[2])⁻¹] :
        Matrix (Fin 2) (Fin 2) ℚ_[2]) := by
    apply Matrix.inv_eq_right_inv
    show ((2 : ℚ_[2]) ^ e • (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ_[2])) *
      (((2 : ℚ_[2]) ^ e.toNat)⁻¹ • (!![2 * (3 : ℚ_[2])⁻¹, -(3 : ℚ_[2])⁻¹; -(3 : ℚ_[2])⁻¹, 2 * (3 : ℚ_[2])⁻¹] :
        Matrix (Fin 2) (Fin 2) ℚ_[2])) = 1
    rw [TwoAdic.zpow_eq_pow_toNat he]
    have h2 : (2 : ℚ_[2]) ^ e.toNat ≠ 0 := pow_ne_zero _ two_ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> norm_num
  rw [hinv]
  rw [← sum2 (fun x y => ch ((2 : ℚ_[2]) ^ m * (((2 : ℚ_[2]) ^ e.toNat)⁻¹ *
        ((3 : ℚ_[2])⁻¹ * (2 * ((x : ℚ_[2]) * x - x * y + y * y))))))
    (2 ^ e.toNat)]
  refine sum_congr rfl fun f _ => ?_
  show ch ((2 : ℚ_[2]) ^ m * qv (((2 : ℚ_[2]) ^ e.toNat)⁻¹ •
    (!![2 * (3 : ℚ_[2])⁻¹, -(3 : ℚ_[2])⁻¹; -(3 : ℚ_[2])⁻¹, 2 * (3 : ℚ_[2])⁻¹] : Matrix (Fin 2) (Fin 2) ℚ_[2]))
    (natVec (N := fun _ => 2 ^ e.toNat) f)) = _
  rw [qv_two]
  congr 1
  simp [natVec]
  ring

theorem hyp_le (E m : ℕ) (h : E ≤ m) :
    ∑ x ∈ range (2 ^ E), ∑ y ∈ range (2 ^ E),
      ch ((2 : ℚ_[2]) ^ m * (((2 : ℚ_[2]) ^ E)⁻¹ * (2 * ((x : ℚ_[2]) * y)))) = ((2 : ℂ) ^ E) ^ 2 := by
  obtain ⟨d, hd⟩ : ∃ d, m = E + d := ⟨m - E, by omega⟩
  have : ∀ x ∈ range (2 ^ E), ∀ y ∈ range (2 ^ E),
      ch ((2 : ℚ_[2]) ^ m * (((2 : ℚ_[2]) ^ E)⁻¹ * (2 * ((x : ℚ_[2]) * y)))) = 1 := by
    intro x _ y _
    have e : (2 : ℚ_[2]) ^ m * (((2 : ℚ_[2]) ^ E)⁻¹ * (2 * ((x : ℚ_[2]) * y)))
        = 2 * (2 ^ d * ((x : ℚ_[2]) * y)) := by
      rw [hd]; field_simp; ring
    rw [e, ch_two_mul]
    exact zi_mul (zi_pow zi_two d) (zi_mul (zi_nat x) (zi_nat y))
  rw [sum_congr rfl fun x hx => sum_congr rfl (this x hx)]
  simp
  ring

theorem hyp_gt (E m : ℕ) (h : m < E) :
    ∑ x ∈ range (2 ^ E), ∑ y ∈ range (2 ^ E),
      ch ((2 : ℚ_[2]) ^ m * (((2 : ℚ_[2]) ^ E)⁻¹ * (2 * ((x : ℚ_[2]) * y))))
      = ((2 : ℂ) ^ m) ^ 2 * 2 ^ (E - m) := by
  obtain ⟨j, hj⟩ : ∃ j, E = m + j := ⟨E - m, by omega⟩
  subst hj
  rw [Nat.add_sub_cancel_left]
  set g : ℕ → ℕ → ℂ := fun x y => ch (2 * ((x : ℚ_[2]) * y) / 2 ^ j) with hg
  have hterm : ∀ x y : ℕ, ch ((2 : ℚ_[2]) ^ m * (((2 : ℚ_[2]) ^ (m + j))⁻¹ * (2 * ((x : ℚ_[2]) * y)))) = g x y := by
    intro x y
    simp only [hg]; congr 1
    rw [pow_add]; field_simp
  simp_rw [hterm]
  have hx : ∀ x y, g (x + 2 ^ j) y = g x y := by
    intro x y
    simp only [hg]
    have e : 2 * (((x + 2 ^ j : ℕ) : ℚ_[2]) * y) / 2 ^ j = 2 * ((x : ℚ_[2]) * y) / 2 ^ j + 2 * (y : ℕ) := by
      push_cast; field_simp
    rw [e, ch_add_two_mul _ (zi_nat y)]
  have hy : ∀ x y, g x (y + 2 ^ j) = g x y := by
    intro x y
    simp only [hg]
    have e : 2 * ((x : ℚ_[2]) * ((y + 2 ^ j : ℕ) : ℚ_[2])) / 2 ^ j = 2 * ((x : ℚ_[2]) * y) / 2 ^ j + 2 * (x : ℕ) := by
      push_cast; field_simp
    rw [e, ch_add_two_mul _ (zi_nat x)]
  rw [show 2 ^ (m + j) = 2 ^ j * 2 ^ m by ring, sum2_periodic g _ hx hy]
  have : ∑ x ∈ range (2 ^ j), ∑ y ∈ range (2 ^ j), g x y = Hs j := rfl
  rw [this, Hs_val]; push_cast; ring

theorem ell_le (E m : ℕ) (h : E ≤ m) :
    ∑ x ∈ range (2 ^ E), ∑ y ∈ range (2 ^ E),
      ch ((2 : ℚ_[2]) ^ m * (((2 : ℚ_[2]) ^ E)⁻¹ *
        ((3 : ℚ_[2])⁻¹ * (2 * ((x : ℚ_[2]) * x - x * y + y * y))))) = ((2 : ℂ) ^ E) ^ 2 := by
  obtain ⟨d, hd⟩ : ∃ d, m = E + d := ⟨m - E, by omega⟩
  have : ∀ x ∈ range (2 ^ E), ∀ y ∈ range (2 ^ E),
      ch ((2 : ℚ_[2]) ^ m * (((2 : ℚ_[2]) ^ E)⁻¹ *
        ((3 : ℚ_[2])⁻¹ * (2 * ((x : ℚ_[2]) * x - x * y + y * y))))) = 1 := by
    intro x _ y _
    have e : (2 : ℚ_[2]) ^ m * (((2 : ℚ_[2]) ^ E)⁻¹ * ((3 : ℚ_[2])⁻¹ * (2 * ((x : ℚ_[2]) * x - x * y + y * y))))
        = 2 * (2 ^ d * ((3 : ℚ_[2])⁻¹ * ((x : ℚ_[2]) * x - x * y + y * y))) := by
      rw [hd]; field_simp; ring
    rw [e, ch_two_mul]
    exact zi_mul (zi_pow zi_two d) (zi_mul zi_inv_three
      (zi_add (zi_sub (zi_mul (zi_nat x) (zi_nat x)) (zi_mul (zi_nat x) (zi_nat y))) (zi_mul (zi_nat y) (zi_nat y))))
  rw [sum_congr rfl fun x hx => sum_congr rfl (this x hx)]
  simp
  ring

theorem ell_gt (E m : ℕ) (h : m < E) :
    ∑ x ∈ range (2 ^ E), ∑ y ∈ range (2 ^ E),
      ch ((2 : ℚ_[2]) ^ m * (((2 : ℚ_[2]) ^ E)⁻¹ *
        ((3 : ℚ_[2])⁻¹ * (2 * ((x : ℚ_[2]) * x - x * y + y * y)))))
      = ((2 : ℂ) ^ m) ^ 2 * ((-1) ^ (E - m) * 2 ^ (E - m)) := by
  obtain ⟨j, hj⟩ : ∃ j, E = m + j := ⟨E - m, by omega⟩
  subst hj
  rw [Nat.add_sub_cancel_left]
  set g : ℕ → ℕ → ℂ := fun x y =>
    ch ((3 : ℚ_[2])⁻¹ * (2 * ((x : ℚ_[2]) * x - x * y + y * y)) / 2 ^ j) with hg
  have hterm : ∀ x y : ℕ, ch ((2 : ℚ_[2]) ^ m * (((2 : ℚ_[2]) ^ (m + j))⁻¹ *
      ((3 : ℚ_[2])⁻¹ * (2 * ((x : ℚ_[2]) * x - x * y + y * y))))) = g x y := by
    intro x y
    simp only [hg]; congr 1
    rw [pow_add]; field_simp
  simp_rw [hterm]
  have hx : ∀ x y, g (x + 2 ^ j) y = g x y := by
    intro x y
    simp only [hg]
    have e : (3 : ℚ_[2])⁻¹ * (2 * ((((x + 2 ^ j : ℕ) : ℚ_[2])) * ((x + 2 ^ j : ℕ) : ℚ_[2])
          - ((x + 2 ^ j : ℕ) : ℚ_[2]) * y + y * y)) / 2 ^ j
        = (3 : ℚ_[2])⁻¹ * (2 * ((x : ℚ_[2]) * x - x * y + y * y)) / 2 ^ j
          + 2 * ((3 : ℚ_[2])⁻¹ * (2 * x + 2 ^ j - y)) := by
      push_cast; field_simp; ring
    rw [e, ch_add_two_mul _ (zi_mul zi_inv_three
      (zi_sub (zi_add (zi_mul zi_two (zi_nat x)) (zi_pow zi_two j)) (zi_nat y)))]
  have hy : ∀ x y, g x (y + 2 ^ j) = g x y := by
    intro x y
    simp only [hg]
    have e : (3 : ℚ_[2])⁻¹ * (2 * ((x : ℚ_[2]) * x - x * ((y + 2 ^ j : ℕ) : ℚ_[2])
          + ((y + 2 ^ j : ℕ) : ℚ_[2]) * ((y + 2 ^ j : ℕ) : ℚ_[2]))) / 2 ^ j
        = (3 : ℚ_[2])⁻¹ * (2 * ((x : ℚ_[2]) * x - x * y + y * y)) / 2 ^ j
          + 2 * ((3 : ℚ_[2])⁻¹ * (2 * y + 2 ^ j - x)) := by
      push_cast; field_simp; ring
    rw [e, ch_add_two_mul _ (zi_mul zi_inv_three
      (zi_sub (zi_add (zi_mul zi_two (zi_nat y)) (zi_pow zi_two j)) (zi_nat x)))]
  rw [show 2 ^ (m + j) = 2 ^ j * 2 ^ m by ring, sum2_periodic g _ hx hy]
  have : ∑ x ∈ range (2 ^ j), ∑ y ∈ range (2 ^ j), g x y = Es j := rfl
  rw [this, Es_val]; push_cast; ring

theorem zpw_zero : zpw 0 = 1 := by simp [zpw]

theorem zpw_four : zpw 4 = -1 := by
  simpa [zeta8_pow_four] using zpw_nat 4

theorem zpw_four_mul (j : ℕ) : zpw (4 * (j : ZMod 8)) = (-1) ^ j := by
  induction j with
  | zero => simp [zpw_zero]
  | succ j ih =>
    rw [Nat.cast_succ, mul_add, mul_one, zpw_add, ih, zpw_four, pow_succ]

theorem blockPhase_hyp (e : ℤ) (m : ℕ) : blockPhase (DyBlock.hyp e) m = 0 := by
  unfold blockPhase
  split_ifs <;> simp [blockOddity, blockSign, signInd]

theorem blockPhase_ell_le (e : ℤ) (m : ℕ) (h : ¬ m < bex (DyBlock.ell e)) :
    blockPhase (DyBlock.ell e) m = 0 := by
  unfold blockPhase; rw [if_neg h]

theorem blockPhase_ell_gt (e : ℤ) (m : ℕ) (h : m < bex (DyBlock.ell e)) :
    blockPhase (DyBlock.ell e) m = 4 * ((bex (DyBlock.ell e) - m : ℕ) : ZMod 8) := by
  unfold blockPhase; rw [if_pos h]
  simp [blockOddity, blockSign, signInd]

/-- Otherwise it is a positive real multiple of zeta8 ^ blockPhase. -/
theorem blockGauss_eq (b : DyBlock) (hv : b.Valid) (he : 0 ≤ blockExp b) (m : ℕ)
    (h : ¬ (IsSqBlock b ∧ bex b = m ∧ 1 ≤ m)) :
    ∃ r : ℝ, 0 < r ∧ blockGauss b m = (r : ℂ) * zeta8 ^ (blockPhase b m).val := by
  cases b with
  | sq e u =>
    obtain ⟨c, hc, rfl⟩ := sq_param hv
    exact blockGauss_eq_sq e hc he m (fun ⟨a, b⟩ => h ⟨trivial, a, b⟩)
  | hyp e =>
    have he' : 0 ≤ e := he
    rw [blockGauss_hyp_eq e he' m, blockPhase_hyp]
    by_cases hle : e.toNat ≤ m
    · rw [hyp_le _ _ hle]
      refine ⟨((2 : ℝ) ^ e.toNat) ^ 2, by positivity, ?_⟩
      simp
    · rw [hyp_gt _ _ (by omega)]
      refine ⟨((2 : ℝ) ^ m) ^ 2 * 2 ^ (e.toNat - m), by positivity, ?_⟩
      simp
  | ell e =>
    have he' : 0 ≤ e := he
    rw [blockGauss_ell_eq e he' m]
    have hb : bex (DyBlock.ell e) = e.toNat := rfl
    by_cases hle : e.toNat ≤ m
    · rw [ell_le _ _ hle, blockPhase_ell_le e m (by rw [hb]; omega)]
      refine ⟨((2 : ℝ) ^ e.toNat) ^ 2, by positivity, ?_⟩
      simp
    · rw [ell_gt _ _ (by omega), blockPhase_ell_gt e m (by rw [hb]; omega)]
      refine ⟨((2 : ℝ) ^ m) ^ 2 * 2 ^ (e.toNat - m), by positivity, ?_⟩
      show _ = _ * zpw _
      rw [hb, zpw_four_mul]
      push_cast; ring

end QuadFormsKB.ConwaySloane.Mass.Gauss2
