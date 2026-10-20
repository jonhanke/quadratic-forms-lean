/-
# Local zeta functions at good places: Weil's Lemma 4.3.2 and the convergence factors

**Layer:** local, at a finite place $v$ of a number field with $v \nmid 2$ and $L_v$ unimodular ($\pi \nmid \det H_Q$, $H_Q$ the
Hessian $= 2\cdot$Gram). Notation and measures as in `LocalZeta.lean`: $q = N(v)$, $X = q^{-s}$, $s \ge 0$ real,
$\nu$ any translation-invariant measure on $F_v$ finite on compacts, $dx = \nu^{\otimes n}$, $c = \nu(\mathcal O_v)$
($c = 1$ for `haarV`, $c = N(\mathfrak d_v)^{-1/2}$ for `selfDualV`).

**Results.**
* `aSeq_one_good`, `cSeq_good`: $a_1 = N_1/q^n$ and $c_j = (N_1 - 1)q^{1-n}q^{-j}$ for $j \ge 1$, where $N_1 = r_\mathfrak p(0)$ is
  the number of zeros of $Q \bmod \mathfrak p$ in $\mathbb F_q^n$ (Hanke's Table 1, `DVR.card_mod_pi_of_unimodular`):
  $N_1 = q^{n-1} + \varepsilon(q-1)q^{m-1}$ for $n = 2m$, $N_1 = q^{n-1}$ for $n$ odd; $\varepsilon = \chi((-1)^m\det)$ (`DVR.chiDisc`).
  (Hensel: every non-zero solution mod $\mathfrak p$ lifts, Hanke's Lemma 3.4 with $K_0 = 1$.)
* **`zetaInt_good_even`, `zetaInt_good_odd`** (**Weil's Lemma 4.3.2**, p. 89, here proved at *every* $v \nmid 2\det$):
  $$Z_v(s) = c^n\,\frac{(1 - q^{-1})(1 - \varepsilon q^{-m})}{(1 - q^{-1-s})(1 - \varepsilon q^{-m-s})}\quad(n = 2m),\qquad
    Z_v(s) = c^n\,\frac{(1 - q^{-1})(1 - q^{-n-s})}{(1 - q^{-1-s})(1 - q^{-n-2s})}\quad(n \text{ odd}).$$
  Weil's $Z_\mathfrak p = (1 - q^{-1})^{-1}Z_v$ with $c = 1$ (his $d'x$ carries the convergence factor $1 - q^{-1}$), so these are
  exactly his formulas $(1-\varepsilon q^{-m'})(1-q^{-s-1})^{-1}(1-\varepsilon q^{-s-m'})^{-1}$ and $(1-q^{-s-m})(1-q^{-s-1})^{-1}(1-q^{-2s-m})^{-1}$.
* **`abs_zetaRatio_sub_one_le`** (**the convergence factors**, Weil §4.3, Lemma 4.3.1 and the products in §§4.4–4.5, pp. 88–89, 93–94,
  107): with $\lambda_v(s) = (1 - q^{-1})/(1 - q^{-1-s}) = \zeta_v(1+s)/\zeta_v(1)$ and $\nu$ = `haarV`, for every real $s \ge 0$,
  $$\Big|\frac{Z_v(s)}{\lambda_v(s)} - 1\Big| \le 2\,q^{-\lfloor n/2\rfloor};\quad\text{in particular } \le 2q^{-2} \text{ for } n \ge 4.$$
  This is the uniform bound that makes $\prod_v Z_v(s)/\lambda_v(s)$ converge absolutely and uniformly in $s \ge 0$:
  $\sum_v q_v^{-2} < \infty$. (Weil needs $m > 4$ for other reasons, the spheres of Lemma 4.5.1; the multiplicative bound itself
  holds for $n \ge 4$.)
* `zetaRatio_good_even`, `zetaRatio_good_odd`: the exact values $Z_v/\lambda_v = (1-\varepsilon q^{-m})/(1-\varepsilon q^{-m-s})$ resp.
  $(1-q^{-n-s})/(1-q^{-n-2s})$ (Weil's "$\zeta_k(s+1)\zeta_k(s+m')^{\pm}\ldots$" factorization, pp. 93–94).

Sources: A. Weil, *Adeles and Algebraic Groups* (1982), §4.3, Lemmas 4.3.1–4.3.2, pp. 88–90; §4.5, pp. 101–107;
Hanke 2004, Table 1, p. 363 and Lemma 3.4, p. 361.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.LocalZeta
import QuadFormsKB.Tamagawa.LocalIdentity

open IsDedekindDomain NumberField MeasureTheory WithZero Filter Topology
open QuadFormsKB.Analysis

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.LocalZeta

open QuadFormsKB.LocalDensity

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "πv" => LocalDensity.NF.π v
local notation "qv" => ((DVR.q (v.adicCompletionIntegers F) : ℕ) : ℝ)

variable {n : ℕ}

/-! ### Unimodular, non-dyadic: level $1$ and Hensel from level $1$ -/

/-- At $\pi \nmid 2\det H_Q$, $\pi^0$ is a local level (Hanke's $\mathfrak p \nmid N$): $W = (\det H)^{-1}\operatorname{adj}H$. -/
lemma isLocalLevel_zero_of_unimodular (Q : QuadForm 𝔬 n) (h2 : ¬ πv ∣ 2) (hdet : ¬ πv ∣ Q.hessian.det) :
    DVR.IsLocalLevel Q πv 0 := by
  have hu : IsUnit Q.hessian.det := DVR.dvr_isUnit_of_not_dvd (NF.irreducible_π v) hdet
  have h2u : IsUnit (2 : 𝔬) := DVR.dvr_isUnit_of_not_dvd (NF.irreducible_π v) h2
  refine ⟨(hu.unit⁻¹ : 𝔬ˣ).val • Q.hessian.adjugate, ?_, ?_, fun i => ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, pow_zero, one_smul]
    rw [show ((hu.unit⁻¹ : 𝔬ˣ) : 𝔬) * Q.hessian.det = 1 from hu.val_inv_mul, one_smul]
  · rw [Matrix.transpose_smul, Matrix.adjugate_transpose, DVR.hessian_transpose]
  · exact h2u.dvd

lemma levelExp_eq_zero_of_unimodular (Q : QuadForm 𝔬 n) (h2 : ¬ πv ∣ 2) (hdet : ¬ πv ∣ Q.hessian.det) :
    DVR.levelExp Q πv = 0 := by
  have h := isLocalLevel_zero_of_unimodular v Q h2 hdet
  have := (DVR.isLocalLevel_iff_levelExp_le ⟨0, h⟩ 0).mp h
  omega

lemma he_zero (h2 : ¬ πv ∣ 2) : πv ^ 0 ∣ 2 ∧ ¬ πv ^ (0 + 1) ∣ 2 := ⟨by simp, by simpa using h2⟩

lemma depthLevel_eq_one (Q : QuadForm 𝔬 n) (h2 : ¬ πv ∣ 2) (hdet : ¬ πv ∣ Q.hessian.det) :
    DVR.depthLevel Q πv 0 = 1 := by
  rw [DVR.depthLevel, levelExp_eq_zero_of_unimodular v Q h2 hdet]

/-- Mod $\mathfrak p$ the only Zero-type vector is $0$, so the Zero-type count of $0$ mod $\mathfrak p$ is $1$. -/
lemma repCountOf_zeroType_one (Q : QuadForm 𝔬 n) :
    DVR.repCountOf Q πv 1 0 (DVR.IsZeroType πv 1) = 1 := by
  rw [DVR.repCountOf, Nat.card_eq_one_iff_exists]
  refine ⟨⟨0, by simp [QuadForm.evalIn], fun i => dvd_zero _⟩, fun ⟨x, _, hx⟩ => ?_⟩
  have hπ0 : (Ideal.Quotient.mk (Ideal.span {πv ^ 1}) πv) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]; exact Ideal.mem_span_singleton_self _
  have : x = 0 := funext fun i => by
    obtain ⟨y, hy⟩ := hx i
    rw [hy, hπ0, zero_mul]; rfl
  subst this; rfl

/-- **$N_1$:** the number of zeros of $Q \bmod \mathfrak p$ in $(\mathcal O_v/\mathfrak p)^n$. -/
abbrev N1 (Q : QuadForm 𝔬 n) : ℕ := DVR.repCount Q πv 1 0

lemma cSeq_one_good (Q : QuadForm 𝔬 n) :
    cSeq v Q 1 = ((N1 v Q : ℚ) - 1) / (DVR.q 𝔬 : ℚ) ^ n := by
  have h := DVR.repCount_eq_zero_add_nonZero Q πv (NF.irreducible_π v) 1 0
  rw [repCountOf_zeroType_one] at h
  rw [cSeq, one_mul, N1, h]
  push_cast; ring

/-- **The primitive part at a good place:** $c_j = (N_1 - 1)\,q^{1-n}\,q^{-j}$ for $j \ge 1$. -/
theorem cSeq_good (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) (h2 : ¬ πv ∣ 2)
    (hdet : ¬ πv ∣ Q.hessian.det) (j : ℕ) (hj : 1 ≤ j) :
    cSeq v Q j = ((N1 v Q : ℚ) - 1) / (DVR.q 𝔬 : ℚ) ^ n * (DVR.q 𝔬 : ℚ) * ((DVR.q 𝔬 : ℚ)⁻¹) ^ j := by
  have := cSeq_geom v Q hQ hn 0 (he_zero v h2) j (by rw [depthLevel_eq_one v Q h2 hdet]; exact hj)
  rw [this, depthLevel_eq_one v Q h2 hdet, cSeq_one_good, pow_one]

lemma aSeq_one_good (Q : QuadForm 𝔬 n) : aSeq v Q 1 = (N1 v Q : ℚ) / (DVR.q 𝔬 : ℚ) ^ n := by
  rw [aSeq, one_mul]

/-! ### The closed form -/

/-- **The good-place identity in terms of $N_1$** ($\pi \nmid 2\det H_Q$, $n \ge 1$, $s \ge 0$, $X = q^{-s}$, $\rho = q^{-1}$):
$$Z_v(s)(1-\rho X)(1 - q^{-n}X^2) = c^n\Big[(1-\rho X)\big(d_0 + d_1X\big) + (N_1-1)q^{1-n}(1-\rho)\rho^2X^2\Big],$$
$d_0 = 1 - N_1q^{-n}$, $d_1 = N_1q^{-n} - (N_1-1)q^{-n-1} - q^{-n}$. -/
theorem zetaInt_good_N1 (ν : Measure (v.adicCompletion F)) [SigmaFinite ν] [Measure.IsAddRightInvariant ν]
    [IsFiniteMeasureOnCompacts ν] (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) (h2 : ¬ πv ∣ 2)
    (hdet : ¬ πv ∣ Q.hessian.det) {s : ℝ} (hs : 0 ≤ s) :
    (1 - qv⁻¹ * qv ^ (-s)) * ((1 - (qv ^ n)⁻¹ * (qv ^ (-s)) ^ 2) * zetaInt v ν Q s) =
      ν.real (latticeV v 0) ^ n * ((1 - qv⁻¹ * qv ^ (-s)) *
        ((1 - (N1 v Q : ℝ) / qv ^ n) + qv ^ (-s) * ((N1 v Q : ℝ) / qv ^ n - ((N1 v Q : ℝ) - 1) / qv ^ n * qv⁻¹
          - (qv ^ n)⁻¹)) +
        ((N1 v Q : ℝ) - 1) / qv ^ n * qv * (1 - qv⁻¹) * (qv⁻¹ * qv ^ (-s)) ^ 2) := by
  have hq1 : (1 : ℝ) < qv := by exact_mod_cast (q_ge_two v)
  have hq0 : (0 : ℝ) < qv := by linarith
  set c := ν.real (latticeV v 0) ^ n
  set X : ℝ := qv ^ (-s)
  have hX1 : X ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1.le (by linarith)
  have hX0 : 0 < X := Real.rpow_pos_of_pos hq0 _
  set γ : ℝ := ((N1 v Q : ℝ) - 1) / qv ^ n * qv
  have hc : ∀ j, 1 ≤ j → (cSeq v Q j : ℝ) = γ * qv⁻¹ ^ j := by
    intro j hj
    rw [cSeq_good v Q hQ hn h2 hdet j hj]; push_cast; ring
  have ha : ∀ j, 2 ≤ j → (aSeq v Q j : ℝ) = γ * qv⁻¹ ^ j + (qv ^ n)⁻¹ * aSeq v Q (j - 2) := by
    intro j hj
    rw [aSeq_rec v Q j hj]; push_cast; rw [hc j (by omega)]
  have key := series_rational (fun j => c * ((aSeq v Q j : ℝ) - aSeq v Q (j + 1))) X qv⁻¹
    (c * (γ * (1 - qv⁻¹))) (qv ^ n)⁻¹ (zetaInt v ν Q s) 2 le_rfl (hasSum_zetaInt v ν Q hQ hn hs)
    (by
      rw [abs_of_nonneg (by positivity)]
      calc qv⁻¹ * X ≤ qv⁻¹ * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact inv_lt_one_of_one_lt₀ hq1)
    (by
      intro j hj
      rw [ha j hj, ha (j + 1) (by omega), show j + 1 - 2 = j - 2 + 1 by omega]
      ring)
  rw [key]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_mul, pow_one,
    show ¬ (2 ≤ 0) by omega, show ¬ (2 ≤ 1) by omega, ite_false, mul_zero, sub_zero]
  have h0 : (aSeq v Q 0 : ℝ) = 1 := aSeq_zero v Q
  have h1 : (aSeq v Q 1 : ℝ) = (N1 v Q : ℝ) / qv ^ n := by rw [aSeq_one_good]; push_cast; ring
  have h2' : (aSeq v Q 2 : ℝ) = γ * qv⁻¹ ^ 2 + (qv ^ n)⁻¹ := by
    rw [ha 2 le_rfl, show 2 - 2 = 0 by rfl, h0, mul_one]
  rw [h0, h1, show (1 + 1 : ℕ) = 2 from rfl, h2']
  simp only [γ]
  have : qv ≠ 0 := hq0.ne'
  field_simp
  ring

/-- **Weil's Lemma 4.3.2, even rank** (p. 89; proved at every $v \nmid 2\det H_Q$): for $n = 2m$, $m \ge 1$, and real $s \ge 0$,
$$Z_v(s) = \nu(\mathcal O_v)^n\,\frac{(1 - q^{-1})(1 - \varepsilon q^{-m})}{(1 - q^{-1}q^{-s})(1 - \varepsilon q^{-m}q^{-s})},
  \qquad \varepsilon = \chi\big((-1)^m\det(H_Q/2)\big) = \pm 1\ (\texttt{DVR.chiDisc}).$$ -/
@[kb "weil1982" "§4.3, Lemma 4.3.2, p. 89 (δ = 1, m = 2m')"]
theorem zetaInt_good_even (ν : Measure (v.adicCompletion F)) [SigmaFinite ν] [Measure.IsAddRightInvariant ν]
    [IsFiniteMeasureOnCompacts ν] (m : ℕ) (hm : 1 ≤ m) (Q : QuadForm 𝔬 (2 * m)) (h2 : ¬ πv ∣ 2)
    (hdet : ¬ πv ∣ Q.hessian.det) {s : ℝ} (hs : 0 ≤ s) :
    zetaInt v ν Q s = ν.real (latticeV v 0) ^ (2 * m) *
      ((1 - qv⁻¹) * (1 - (DVR.chiDisc Q : ℝ) * (qv ^ m)⁻¹) /
        ((1 - qv⁻¹ * qv ^ (-s)) * (1 - (DVR.chiDisc Q : ℝ) * (qv ^ m)⁻¹ * qv ^ (-s)))) := by
  have hQ : Q.Nondegenerate := fun h => hdet (h ▸ dvd_zero _)
  have hq1 : (1 : ℝ) < qv := by exact_mod_cast (q_ge_two v)
  have hq0 : (0 : ℝ) < qv := by linarith
  have hX1 : qv ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1.le (by linarith)
  have hX0 : 0 < qv ^ (-s) := Real.rpow_pos_of_pos hq0 _
  have key := zetaInt_good_N1 v ν Q hQ (by omega) h2 hdet hs
  have hN := ((DVR.card_mod_pi_of_unimodular Q πv (NF.irreducible_π v) h2 hdet (by omega) 1
    (fun h => (NF.irreducible_π v).not_isUnit (isUnit_of_dvd_one h))).1 (even_two_mul m)).1
  have hN' : (N1 v Q : ℝ) = qv ^ (2 * m - 1) + (DVR.chiDisc Q : ℝ) * (qv - 1) * qv ^ (2 * m / 2 - 1) := by
    exact_mod_cast hN
  rw [show 2 * m / 2 - 1 = m - 1 by omega] at hN'
  have hε := DVR.chiDisc_sq (NF.irreducible_π v) h2 hdet
  set ε : ℝ := ((DVR.chiDisc Q : ℤ) : ℝ)
  set X := qv ^ (-s)
  set c := ν.real (latticeV v 0) ^ (2 * m)
  have hρX : qv⁻¹ * X < 1 := by
    calc qv⁻¹ * X ≤ qv⁻¹ * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact inv_lt_one_of_one_lt₀ hq1
  have hqm : 1 < qv ^ m := one_lt_pow₀ hq1 (by omega)
  have hεX : 1 - ε * (qv ^ m)⁻¹ * X ≠ 0 := by
    have : |ε * (qv ^ m)⁻¹ * X| < 1 := by
      have hε1 : |ε| = 1 := by
        have : |ε| ^ 2 = 1 := by rw [sq_abs]; exact hε
        nlinarith [abs_nonneg ε]
      rw [abs_mul, abs_mul, hε1, one_mul, abs_of_pos (inv_pos.mpr (by linarith)), abs_of_pos hX0]
      calc (qv ^ m)⁻¹ * X ≤ (qv ^ m)⁻¹ * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact inv_lt_one_of_one_lt₀ hqm
    intro h; have h' := (abs_lt.mp this).2; linarith
  have hρ : 1 - qv⁻¹ * X ≠ 0 := by linarith
  have hX2 : 1 - (qv ^ (2 * m))⁻¹ * X ^ 2 ≠ 0 := by
    have : (qv ^ (2 * m))⁻¹ * X ^ 2 < 1 := by
      have h1 : (qv ^ (2 * m))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq1 (by omega))
      have h2 : X ^ 2 ≤ 1 := pow_le_one₀ hX0.le hX1
      nlinarith [inv_pos.mpr (show (0 : ℝ) < qv ^ (2 * m) by positivity)]
    linarith
  have hfac : 1 - (qv ^ (2 * m))⁻¹ * X ^ 2 = (1 - ε * (qv ^ m)⁻¹ * X) * (1 + ε * (qv ^ m)⁻¹ * X) := by
    rw [pow_mul', ← inv_pow]
    linear_combination ((qv ^ m)⁻¹ ^ 2 * X ^ 2) * hε
  have hB' : 1 + ε * (qv ^ m)⁻¹ * X ≠ 0 := fun h => hX2 (by rw [hfac, h, mul_zero])
  have hεc : ε = 1 ∨ ε = -1 := mul_self_eq_one_iff.mp (by rw [← sq]; exact hε)
  rw [← mul_div_assoc, eq_div_iff (mul_ne_zero hρ hεX)]
  apply mul_right_cancel₀ hB'
  rw [show zetaInt v ν Q s * ((1 - qv⁻¹ * X) * (1 - ε * (qv ^ m)⁻¹ * X)) * (1 + ε * (qv ^ m)⁻¹ * X) =
      (1 - qv⁻¹ * X) * ((1 - (qv ^ (2 * m))⁻¹ * X ^ 2) * zetaInt v ν Q s) by rw [hfac]; ring, key, hN']
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, show k + 1 - 1 = k by omega]
  have hq0' : qv ≠ 0 := hq0.ne'
  rcases hεc with h | h <;> rw [h] <;> field_simp <;> ring

/-- **Weil's Lemma 4.3.2, odd rank** (p. 89; proved at every $v \nmid 2\det H_Q$): for $n = 2m+1$ and real $s \ge 0$,
$$Z_v(s) = \nu(\mathcal O_v)^n\,\frac{(1 - q^{-1})(1 - q^{-n}q^{-s})}{(1 - q^{-1}q^{-s})(1 - q^{-n}q^{-2s})}.$$ -/
@[kb "weil1982" "§4.3, Lemma 4.3.2, p. 89 (δ = 1, m odd)"]
theorem zetaInt_good_odd (ν : Measure (v.adicCompletion F)) [SigmaFinite ν] [Measure.IsAddRightInvariant ν]
    [IsFiniteMeasureOnCompacts ν] (m : ℕ) (Q : QuadForm 𝔬 (2 * m + 1)) (h2 : ¬ πv ∣ 2)
    (hdet : ¬ πv ∣ Q.hessian.det) {s : ℝ} (hs : 0 ≤ s) :
    zetaInt v ν Q s = ν.real (latticeV v 0) ^ (2 * m + 1) *
      ((1 - qv⁻¹) * (1 - (qv ^ (2 * m + 1))⁻¹ * qv ^ (-s)) /
        ((1 - qv⁻¹ * qv ^ (-s)) * (1 - (qv ^ (2 * m + 1))⁻¹ * (qv ^ (-s)) ^ 2))) := by
  have hQ : Q.Nondegenerate := fun h => hdet (h ▸ dvd_zero _)
  have hq1 : (1 : ℝ) < qv := by exact_mod_cast (q_ge_two v)
  have hq0 : (0 : ℝ) < qv := by linarith
  have hX1 : qv ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1.le (by linarith)
  have hX0 : 0 < qv ^ (-s) := Real.rpow_pos_of_pos hq0 _
  have key := zetaInt_good_N1 v ν Q hQ (by omega) h2 hdet hs
  have hN := ((DVR.card_mod_pi_of_unimodular Q πv (NF.irreducible_π v) h2 hdet (by omega) 1
    (fun h => (NF.irreducible_π v).not_isUnit (isUnit_of_dvd_one h))).2 (odd_two_mul_add_one m)).1
  have hN' : (N1 v Q : ℝ) = qv ^ (2 * m) := by
    have e : 2 * m + 1 - 1 = 2 * m := by omega
    rw [e] at hN; exact_mod_cast hN
  set X := qv ^ (-s)
  have hρX : qv⁻¹ * X < 1 := by
    calc qv⁻¹ * X ≤ qv⁻¹ * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact inv_lt_one_of_one_lt₀ hq1
  have hρ : 1 - qv⁻¹ * X ≠ 0 := by linarith
  have hX2 : 1 - (qv ^ (2 * m + 1))⁻¹ * X ^ 2 ≠ 0 := by
    have : (qv ^ (2 * m + 1))⁻¹ * X ^ 2 < 1 := by
      have h1 : (qv ^ (2 * m + 1))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq1 (by omega))
      have h2 : X ^ 2 ≤ 1 := pow_le_one₀ hX0.le hX1
      nlinarith [inv_pos.mpr (show (0 : ℝ) < qv ^ (2 * m + 1) by positivity)]
    linarith
  rw [← mul_div_assoc, eq_div_iff (mul_ne_zero hρ hX2),
    show zetaInt v ν Q s * ((1 - qv⁻¹ * X) * (1 - (qv ^ (2 * m + 1))⁻¹ * X ^ 2)) =
      (1 - qv⁻¹ * X) * ((1 - (qv ^ (2 * m + 1))⁻¹ * X ^ 2) * zetaInt v ν Q s) by ring, key, hN']
  have hq0' : qv ≠ 0 := hq0.ne'
  field_simp
  ring

/-! ### The convergence factors -/

/-- **The normalizing factor** $\lambda_v(s) = \dfrac{1 - q^{-1}}{1 - q^{-1-s}} = \dfrac{\zeta_v(1+s)}{\zeta_v(1)}$, $\zeta_v(s) = (1-q^{-s})^{-1}$
(Weil's convergence factor $1 - q^{-1}$ of Lemma 4.3.1, pp. 88–89, times the local factor of $\zeta_k(s+1)$, pp. 93–94). -/
def lambdaV (s : ℝ) : ℝ := (1 - qv⁻¹) / (1 - qv⁻¹ * qv ^ (-s))

lemma bound_even_aux (ε a X : ℝ) (hε : ε = 1 ∨ ε = -1) (ha0 : 0 < a) (ha : a ≤ 1 / 2) (hX0 : 0 ≤ X)
    (hX1 : X ≤ 1) : |(1 - ε * a) / (1 - ε * a * X) - 1| ≤ 2 * a := by
  have hD : 0 < 1 - ε * a * X := by rcases hε with rfl | rfl <;> nlinarith
  have hD2 : 1 / 2 ≤ 1 - ε * a * X := by rcases hε with rfl | rfl <;> nlinarith
  rw [div_sub_one hD.ne', abs_div, abs_of_pos hD, div_le_iff₀ hD, abs_le]
  rcases hε with rfl | rfl <;> constructor <;> nlinarith

lemma bound_odd_aux (b X : ℝ) (hb0 : 0 < b) (hb : b ≤ 1 / 2) (hX0 : 0 ≤ X) (hX1 : X ≤ 1) :
    |(1 - b * X) / (1 - b * X ^ 2) - 1| ≤ 2 * b := by
  have hX2 : X ^ 2 ≤ 1 := pow_le_one₀ hX0 hX1
  have hD : 0 < 1 - b * X ^ 2 := by nlinarith
  have hD2 : 1 / 2 ≤ 1 - b * X ^ 2 := by nlinarith
  rw [div_sub_one hD.ne', abs_div, abs_of_pos hD, div_le_iff₀ hD, abs_le]
  constructor <;> nlinarith [sq_nonneg X, mul_nonneg hX0 (sub_nonneg.mpr hX1)]

lemma one_sub_rho_ne (s : ℝ) (hs : 0 ≤ s) : 1 - qv⁻¹ * qv ^ (-s) ≠ 0 := by
  have hq1 : (1 : ℝ) < qv := by exact_mod_cast (q_ge_two v)
  have hX1 : qv ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1.le (by linarith)
  have : qv⁻¹ * qv ^ (-s) < 1 := by
    calc qv⁻¹ * qv ^ (-s) ≤ qv⁻¹ * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact inv_lt_one_of_one_lt₀ hq1
  linarith

lemma lambdaV_ne_zero (s : ℝ) (hs : 0 ≤ s) : lambdaV v s ≠ 0 := by
  have hq1 : (1 : ℝ) < qv := by exact_mod_cast (q_ge_two v)
  exact div_ne_zero (sub_ne_zero.mpr (inv_lt_one_of_one_lt₀ hq1).ne') (one_sub_rho_ne v s hs)

/-- **$Z_v/\lambda_v$ at a good place, even rank** ($\nu$ = `haarV`): $\dfrac{Z_v(s)}{\lambda_v(s)} = \dfrac{1-\varepsilon q^{-m}}{1-\varepsilon q^{-m-s}}$. -/
theorem zetaRatio_good_even (m : ℕ) (hm : 1 ≤ m) (Q : QuadForm 𝔬 (2 * m)) (h2 : ¬ πv ∣ 2)
    (hdet : ¬ πv ∣ Q.hessian.det) {s : ℝ} (hs : 0 ≤ s) :
    zetaInt v (haarV v) Q s / lambdaV v s =
      (1 - (DVR.chiDisc Q : ℝ) * (qv ^ m)⁻¹) / (1 - (DVR.chiDisc Q : ℝ) * (qv ^ m)⁻¹ * qv ^ (-s)) := by
  have hq1 : (1 : ℝ) < qv := by exact_mod_cast (q_ge_two v)
  rw [zetaInt_good_even v (haarV v) m hm Q h2 hdet hs, haarV_real_O, one_pow, one_mul, lambdaV]
  have h1 : 1 - qv⁻¹ ≠ 0 := sub_ne_zero.mpr (inv_lt_one_of_one_lt₀ hq1).ne'
  have h2' := one_sub_rho_ne v s hs
  have hX1 : qv ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1.le (by linarith)
  have hX0 : 0 < qv ^ (-s) := Real.rpow_pos_of_pos (by linarith) _
  have hE : 1 - (DVR.chiDisc Q : ℝ) * (qv ^ m)⁻¹ * qv ^ (-s) ≠ 0 := by
    have hε := DVR.chiDisc_sq (NF.irreducible_π v) h2 hdet
    have ha : (qv ^ m)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq1 (by omega))
    have ha0 : 0 < (qv ^ m)⁻¹ := inv_pos.mpr (by positivity)
    rcases mul_self_eq_one_iff.mp (show ((DVR.chiDisc Q : ℤ) : ℝ) * (DVR.chiDisc Q : ℤ) = 1 by
      rw [← sq]; exact hε) with h | h <;> rw [h] <;> nlinarith
  have key : ∀ A B D E : ℝ, A ≠ 0 → D ≠ 0 → E ≠ 0 → A * B / (D * E) / (A / D) = B / E := by
    intro A B D E hA hD hE; field_simp
  exact key _ _ _ _ h1 h2' hE

/-- **$Z_v/\lambda_v$ at a good place, odd rank** ($\nu$ = `haarV`): $\dfrac{Z_v(s)}{\lambda_v(s)} = \dfrac{1-q^{-n-s}}{1-q^{-n-2s}}$. -/
theorem zetaRatio_good_odd (m : ℕ) (Q : QuadForm 𝔬 (2 * m + 1)) (h2 : ¬ πv ∣ 2)
    (hdet : ¬ πv ∣ Q.hessian.det) {s : ℝ} (hs : 0 ≤ s) :
    zetaInt v (haarV v) Q s / lambdaV v s =
      (1 - (qv ^ (2 * m + 1))⁻¹ * qv ^ (-s)) / (1 - (qv ^ (2 * m + 1))⁻¹ * (qv ^ (-s)) ^ 2) := by
  have hq1 : (1 : ℝ) < qv := by exact_mod_cast (q_ge_two v)
  rw [zetaInt_good_odd v (haarV v) m Q h2 hdet hs, haarV_real_O, one_pow, one_mul, lambdaV]
  have h1 : 1 - qv⁻¹ ≠ 0 := sub_ne_zero.mpr (inv_lt_one_of_one_lt₀ hq1).ne'
  have h2' := one_sub_rho_ne v s hs
  have hX1 : qv ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1.le (by linarith)
  have hX0 : 0 < qv ^ (-s) := Real.rpow_pos_of_pos (by linarith) _
  have hE : 1 - (qv ^ (2 * m + 1))⁻¹ * (qv ^ (-s)) ^ 2 ≠ 0 := by
    have ha : (qv ^ (2 * m + 1))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq1 (by omega))
    have ha0 : 0 < (qv ^ (2 * m + 1))⁻¹ := inv_pos.mpr (by positivity)
    have : (qv ^ (-s)) ^ 2 ≤ 1 := pow_le_one₀ hX0.le hX1
    nlinarith
  have key : ∀ A B D E : ℝ, A ≠ 0 → D ≠ 0 → E ≠ 0 → A * B / (D * E) / (A / D) = B / E := by
    intro A B D E hA hD hE; field_simp
  exact key _ _ _ _ h1 h2' hE

/-- **The convergence-factor bound at good places** (Weil 1982, §4.3, Lemma 4.3.1, pp. 88–89, and the absolute convergence of the
products in §§4.4–4.5, pp. 93–94, 107): for $v \nmid 2\det H_Q$, $n \ge 2$, $\nu$ = `haarV` and **every** real $s \ge 0$,
$$\Big|\frac{Z_v(s)}{\lambda_v(s)} - 1\Big| \le 2\,q^{-\lfloor n/2\rfloor},\qquad \lambda_v(s) = \frac{1-q^{-1}}{1-q^{-1-s}}.$$
For $n \ge 4$ the right side is $\le 2q^{-2}$ (`abs_zetaRatio_sub_one_le_two`), so $\sum_v |Z_v/\lambda_v - 1| < \infty$ uniformly in
$s \ge 0$: the Euler product $\prod_v Z_v(s)/\lambda_v(s)$ converges absolutely and uniformly on $s \ge 0$. -/
@[kb "weil1982" "§4.3, Lemma 4.3.1, pp. 88–89; §4.5, p. 107 (1 - q^{-m'} < e(p) < 1 + q^{-m'})"]
theorem abs_zetaRatio_sub_one_le (Q : QuadForm 𝔬 n) (hn : 2 ≤ n) (h2 : ¬ πv ∣ 2)
    (hdet : ¬ πv ∣ Q.hessian.det) {s : ℝ} (hs : 0 ≤ s) :
    |zetaInt v (haarV v) Q s / lambdaV v s - 1| ≤ 2 * (qv ^ (n / 2))⁻¹ := by
  have hq2 : (2 : ℝ) ≤ qv := by exact_mod_cast (q_ge_two v)
  have hq1 : (1 : ℝ) < qv := by linarith
  have hq0 : (0 : ℝ) < qv := by linarith
  have hX1 : qv ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1.le (by linarith)
  have hX0 : 0 < qv ^ (-s) := Real.rpow_pos_of_pos hq0 _
  have hhalf : ∀ k : ℕ, 1 ≤ k → (qv ^ k)⁻¹ ≤ 1 / 2 := by
    intro k hk
    rw [inv_le_comm₀ (by positivity) (by norm_num), one_div, inv_inv]
    calc (2 : ℝ) ≤ qv := hq2
      _ = qv ^ 1 := (pow_one _).symm
      _ ≤ qv ^ k := pow_le_pow_right₀ hq1.le hk
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [zetaRatio_good_even v m (by omega) Q h2 hdet hs, show 2 * m / 2 = m by omega]
    have hε := DVR.chiDisc_sq (NF.irreducible_π v) h2 hdet
    exact bound_even_aux _ _ _ (mul_self_eq_one_iff.mp (by rw [← sq]; exact hε)) (by positivity)
      (hhalf m (by omega)) hX0.le hX1
  · rw [zetaRatio_good_odd v m Q h2 hdet hs, show (2 * m + 1) / 2 = m by omega]
    have hb := bound_odd_aux _ _ (inv_pos.mpr (show (0 : ℝ) < qv ^ (2 * m + 1) by positivity))
      (hhalf _ (by omega)) hX0.le hX1
    refine hb.trans (mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity)
      (pow_le_pow_right₀ hq1.le (by omega))) (by norm_num))

/-- **The bound in the form used for the Euler product** ($n \ge 4$, in particular Weil's $m > 4$):
$|Z_v(s)/\lambda_v(s) - 1| \le 2q^{-2}$ for all real $s \ge 0$, at every $v \nmid 2\det H_Q$. -/
@[kb "weil1982" "§4.5, §4.5, p. 101 and p. 107 (m > 4, so m' ≥ 2)"]
theorem abs_zetaRatio_sub_one_le_two (Q : QuadForm 𝔬 n) (hn : 4 ≤ n) (h2 : ¬ πv ∣ 2)
    (hdet : ¬ πv ∣ Q.hessian.det) {s : ℝ} (hs : 0 ≤ s) :
    |zetaInt v (haarV v) Q s / lambdaV v s - 1| ≤ 2 * (qv ^ 2)⁻¹ := by
  have hq1 : (1 : ℝ) ≤ qv := by exact_mod_cast (show 1 ≤ DVR.q 𝔬 by have := q_ge_two v; omega)
  refine (abs_zetaRatio_sub_one_le v Q (by omega) h2 hdet hs).trans
    (mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (pow_le_pow_right₀ hq1 (by omega))) (by norm_num))

end QuadFormsKB.LocalZeta
