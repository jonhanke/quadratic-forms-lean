/-
# The Euler product of the local zeta functions
**Layer:** number field; the local factors are those defined in (`LocalZeta.lean`, `LocalZetaGood.lean`), and only the
Euler-product
assembly is global.

**Setting.** $F$ a number field, $Q$ = `QuadForm (𝓞 F) n` nondegenerate, $n \ge 4$ (Weil needs $m > 4$ for the
induction, Lemma 4.5.1, p. 101; the Euler product itself needs only $n \ge 4$). For a finite place $v$,
$Q_v = Q \otimes \mathcal O_v$ (`NF.Qp v Q`), $q_v = N\mathfrak p_v$, $L_v = \mathcal O_v^n$, $\Phi_v = \mathbf 1_{L_v}$, and
$dx_v$ the **standard** Haar measure on $F_v^n$ (`haarV`, $\operatorname{vol}(\mathcal O_v) = 1$; Weil's $(dx)_\mathfrak p$, p. 89).
Real $s \ge 0$ only.

**The local factors.**
* `zetaStd Q v s` $= Z_v(s) = \int_{L_v}|Q(x)|_v^s\,dx_v$ (the `zetaInt` with `haarV`); $Z_v(0) = 1$.
* `zetaWeil Q v s` $= Z_v(s)/(1-q_v^{-1})$: **Weil's** $Z_\mathfrak p(s)$ of §4.3, (1)–(2), p. 89, for the measure
  $d'x_v = (1-q_v^{-1})^{-1}dx_v$ with Weil's convergence factor $1 - q_v^{-1}$ (Lemma 4.3.1, p. 88).
* `zetaRatio Q v s` $= Z_v(s)/\lambda_v(s)$, $\lambda_v(s) = (1-q_v^{-1})/(1-q_v^{-1-s})$ (the `lambdaV`), so that
  $$\text{Weil's } Z_\mathfrak p(s) = \zeta_v(1+s)\cdot\frac{Z_v(s)}{\lambda_v(s)},\qquad \zeta_v(s) = (1-q_v^{-s})^{-1}
  \qquad(\texttt{zetaWeil\_eq}).$$

**Results.**
* `continuousOn_zetaInt`: $s \mapsto Z_v(s)$ is continuous on $[0,\infty)$ (every finite place, any $\nu$).
* `abs_zetaRatio_sub_one_le_normP`: $|Z_v/\lambda_v - 1| \le 2N\mathfrak p_v^{-2}$ for $v \nmid 2\det H_Q$, all
  $s \ge 0$.
* `multipliable_zetaRatio`: $\prod_v Z_v(s)/\lambda_v(s)$ converges absolutely for every $s \ge 0$.
* **`hasProd_zetaWeil`** (**the Euler product**, Weil §4.5, p. 106 and pp. 107–108): for real $s > 0$,
  $$\prod_v Z_\mathfrak p(s) = \zeta_F(1+s)\cdot\prod_v\frac{Z_v(s)}{\lambda_v(s)},$$
  absolutely convergent (unconditional `HasProd` over all finite places).
* **`abs_log_zetaRatio_le`, `summable_logBound`** (**the Weierstrass M-test**): $|\log(Z_v/\lambda_v)(s)| \le u_v$ for all
  $s \in [0,1]$ with $\sum_v u_v < \infty$ ($u_v = 4N\mathfrak p_v^{-2}$ at good places).
* **`continuousOn_zetaRatioProd`**, **`tendsto_zetaRatioProd_zero`**: $R(s) = \prod_v Z_v(s)/\lambda_v(s)$ is continuous on
  $[0,1]$ and $R(s) \to R(0) = 1$ as $s \to 0^+$ ($Z_v(0) = 1 = \lambda_v(0)$).
* `prod_selfDual_vol`: $\prod_v\operatorname{vol}_{\mathrm{sd}}(L_v) = \prod_v N(\mathfrak d_v)^{-n/2} = |d_F|^{-n/2}$ for the self-dual
  measures `selfDualV`.

The global zeta integral, the archimedean factor and the residue at $s = 0$ are in `ZetaResidue.lean`.

Sources: A. Weil, *Adeles and Algebraic Groups* (1982), §4.3 (pp. 88–91), §4.4 (pp. 93–94), §4.5 (pp. 101–108).
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.LocalZetaGood
import QuadFormsKB.Analysis.NFEulerProduct
import QuadFormsKB.Analysis.DifferentLocal
import QuadFormsKB.Siegel.NFMainTerm

open IsDedekindDomain NumberField MeasureTheory WithZero Filter Topology
open QuadFormsKB.Analysis

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.LocalZeta

open QuadFormsKB.LocalDensity

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "𝔬" => v.adicCompletionIntegers F

/-- **Continuity of the local zeta function** on $[0,\infty)$ (every finite place, dyadic included, any $\nu$): from the
generating series `hasSum_zetaInt`, whose terms $q^{-js}\,\nu(\mathcal O_v)^n(a_j - a_{j+1})$ are bounded by their values at
$s = 0$, a summable sequence (Weierstrass M-test). -/
theorem continuousOn_zetaInt (ν : Measure (v.adicCompletion F)) [SigmaFinite ν] [Measure.IsAddRightInvariant ν]
    [IsFiniteMeasureOnCompacts ν] (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) :
    ContinuousOn (fun s => zetaInt v ν Q s) (Set.Ici 0) := by
  have hq1 : (1 : ℝ) ≤ DVR.q 𝔬 := by exact_mod_cast (show 1 ≤ DVR.q 𝔬 by have := q_ge_two v; omega)
  have hq0 : (0 : ℝ) < DVR.q 𝔬 := by linarith
  set d : ℕ → ℝ := fun j => ν.real (latticeV v 0) ^ n * ((aSeq v Q j : ℝ) - aSeq v Q (j + 1)) with hd
  have hd0 : ∀ j, 0 ≤ d j := fun j => mul_nonneg (pow_nonneg measureReal_nonneg _)
    (sub_nonneg.mpr (aSeq_antitone v Q (Nat.le_succ j)))
  have hsum0 : Summable d := by
    have := (hasSum_zetaInt v ν Q hQ hn le_rfl).summable
    simpa [Real.rpow_zero] using this
  have hcont : ContinuousOn (fun s : ℝ => ∑' j, ((DVR.q 𝔬 : ℝ) ^ (-s)) ^ j * d j) (Set.Ici (0 : ℝ)) := by
    refine continuousOn_tsum (u := d) (fun j => ?_) hsum0 fun j s hs => ?_
    · exact (((continuous_const.rpow continuous_neg fun _ => Or.inl hq0.ne').pow j).mul
        continuous_const).continuousOn
    · have hX0 : 0 ≤ (DVR.q 𝔬 : ℝ) ^ (-s) := Real.rpow_nonneg hq0.le _
      have hX1 : (DVR.q 𝔬 : ℝ) ^ (-s) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hq1 (by simp only [Set.mem_Ici] at hs; linarith)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hX0 _) (hd0 j))]
      exact mul_le_of_le_one_left (hd0 j) (pow_le_one₀ hX0 hX1)
  refine hcont.congr fun s hs => ?_
  exact ((hasSum_zetaInt v ν Q hQ hn hs).tsum_eq).symm

/-- $\lambda_v(s) > 0$ for $s \ge 0$. -/
lemma lambdaV_pos (s : ℝ) (hs : 0 ≤ s) : 0 < lambdaV v s := by
  have hq1 : (1 : ℝ) < ((DVR.q 𝔬 : ℕ) : ℝ) := by exact_mod_cast (q_ge_two v)
  have hX1 : ((DVR.q 𝔬 : ℕ) : ℝ) ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1.le (by linarith)
  have hi : ((DVR.q 𝔬 : ℕ) : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
  have hi0 : 0 < ((DVR.q 𝔬 : ℕ) : ℝ)⁻¹ := inv_pos.mpr (by linarith)
  refine div_pos (by linarith) ?_
  nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ ((DVR.q 𝔬 : ℕ) : ℝ) by linarith) (-s)]

/-- $\lambda_v(0) = 1$. -/
lemma lambdaV_zero : lambdaV v 0 = 1 := by
  have hq1 : (1 : ℝ) < ((DVR.q 𝔬 : ℕ) : ℝ) := by exact_mod_cast (q_ge_two v)
  have : 1 - ((DVR.q 𝔬 : ℕ) : ℝ)⁻¹ ≠ 0 := sub_ne_zero.mpr (inv_lt_one_of_one_lt₀ hq1).ne'
  simp [lambdaV, div_self this]

/-- $s \mapsto \lambda_v(s)$ is continuous on $[0,\infty)$. -/
lemma continuousOn_lambdaV : ContinuousOn (fun s => lambdaV v s) (Set.Ici 0) := by
  have hq0 : (0 : ℝ) < ((DVR.q 𝔬 : ℕ) : ℝ) := by exact_mod_cast (q_pos v)
  refine continuousOn_const.div (continuousOn_const.sub (continuousOn_const.mul
    (continuous_const.rpow continuous_neg fun _ => Or.inl hq0.ne').continuousOn)) fun s hs => ?_
  exact one_sub_rho_ne v s hs

end QuadFormsKB.LocalZeta

namespace QuadFormsKB.GlobalZeta

open QuadFormsKB.LocalDensity QuadFormsKB.LocalZeta QuadFormsKB.NFEuler

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- $q_v = |\mathcal O_v/\mathfrak p_v|$ as a real number. -/
local notation "qv" v => ((DVR.q (HeightOneSpectrum.adicCompletionIntegers F v) : ℕ) : ℝ)

/-! ### The local factors of a global form -/

/-- **The standard local zeta function of a global form** at a finite place $v$:
$$Z_v(s) = \int_{\mathcal O_v^n}|Q(x)|_v^s\,dx_v,$$
$Q_v = Q \otimes \mathcal O_v$ (`NF.Qp`), $dx_v$ the standard Haar measure (`haarV`, $\operatorname{vol}(\mathcal O_v) = 1$). -/
@[kb "weil1982" "§4.3, (2), p. 89 (the integral with (dx)_p)"]
def zetaStd (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) (s : ℝ) : ℝ :=
  zetaInt v (haarV v) (NF.Qp v Q) s

/-- **Weil's local zeta function** (Weil 1982, §4.3, (1)–(2), p. 89): $Z_\mathfrak p(s) = \int|Q(x)|_v^s\Phi_v(x)\,d'x_v =
Z_v(s)/(1 - q_v^{-1})$, for the local measure $d'x_v = (1-q_v^{-1})^{-1}dx_v$ derived from the gauge form
$dx_0\cdots dx_{n-1}$ and Weil's convergence factor $1 - q_v^{-1}$ (Lemma 4.3.1, p. 88). -/
@[kb "weil1982" "§4.3, (1)–(2), p. 89 (Z_p with d'x)"]
def zetaWeil (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) (s : ℝ) : ℝ :=
  zetaStd Q v s / (1 - (qv v)⁻¹)

/-- **The normalized local factor** $Z_v(s)/\lambda_v(s)$, $\lambda_v(s) = (1-q_v^{-1})/(1-q_v^{-1-s})$ (`lambdaV`). -/
def zetaRatio (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) (s : ℝ) : ℝ :=
  zetaStd Q v s / lambdaV v s

/-- **The good places** of $Q$: $v \nmid 2\det H_Q$, i.e. $2\det H_Q \notin \mathfrak p_v$. -/
def IsGoodPlace (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  2 * Q.hessian.det ∉ v.asIdeal

/-- All but finitely many places are good. -/
theorem finite_not_isGoodPlace (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) :
    {v : HeightOneSpectrum (𝓞 F) | ¬ IsGoodPlace Q v}.Finite := by
  have h2 : (2 : 𝓞 F) ≠ 0 := two_ne_zero
  simpa [IsGoodPlace] using Siegel.finite_mem_asIdeal (mul_ne_zero h2 hQ)

lemma isGoodPlace_cofinite (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) :
    ∀ᶠ v in cofinite, IsGoodPlace Q v := by
  simpa using finite_not_isGoodPlace Q hQ

lemma not_dvd_of_isGoodPlace {Q : QuadForm (𝓞 F) n} {v : HeightOneSpectrum (𝓞 F)} (h : IsGoodPlace Q v) :
    ¬ NF.π v ∣ 2 ∧ ¬ NF.π v ∣ (NF.Qp v Q).hessian.det := by
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := fun h' => h (v.asIdeal.mul_mem_right _ h')
  have hd : Q.hessian.det ∉ v.asIdeal := fun h' => h (v.asIdeal.mul_mem_left _ h')
  exact ⟨NF.π_not_dvd_two v h2, NF.π_not_dvd_det v Q hd⟩

lemma qv_eq (v : HeightOneSpectrum (𝓞 F)) : (qv v) = (normP v : ℝ) := by
  rw [NF.q_completion]

lemma one_lt_qv (v : HeightOneSpectrum (𝓞 F)) : (1 : ℝ) < qv v := by exact_mod_cast (q_ge_two v)

/-- $Z_v(0) = 1$ (`zetaInt_zero`; $\operatorname{vol}(L_v) = 1$). -/
theorem zetaStd_zero (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) : zetaStd Q v 0 = 1 := by
  rw [zetaStd, zetaInt_zero, haarV_real_O, one_pow]

theorem zetaStd_pos (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) (v : HeightOneSpectrum (𝓞 F))
    {s : ℝ} (hs : 0 ≤ s) : 0 < zetaStd Q v s :=
  zetaInt_pos v (haarV v) (by rw [haarV_real_O]; exact one_pos) _ (NF.nondegenerate_Qp v hQ) hn hs

theorem zetaRatio_pos (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) (v : HeightOneSpectrum (𝓞 F))
    {s : ℝ} (hs : 0 ≤ s) : 0 < zetaRatio Q v s :=
  div_pos (zetaStd_pos Q hQ hn v hs) (lambdaV_pos v s hs)

theorem zetaRatio_zero (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) : zetaRatio Q v 0 = 1 := by
  rw [zetaRatio, zetaStd_zero, lambdaV_zero, div_one]

theorem continuousOn_zetaRatio (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n)
    (v : HeightOneSpectrum (𝓞 F)) : ContinuousOn (fun s => zetaRatio Q v s) (Set.Ici 0) :=
  (continuousOn_zetaInt v (haarV v) _ (NF.nondegenerate_Qp v hQ) hn).div (continuousOn_lambdaV v)
    fun s hs => lambdaV_ne_zero v s hs

/-- **The bound in terms of $N\mathfrak p_v$** (Weil 1982, §4.5, p. 107, $1 - q^{-m'} < e(\mathfrak p) < 1 + q^{-m'}$,
$m' \ge 2$):
at a good place, for $n \ge 4$ and all $s \ge 0$, $|Z_v(s)/\lambda_v(s) - 1| \le 2N\mathfrak p_v^{-2}$. -/
theorem abs_zetaRatio_sub_one_le_normP (Q : QuadForm (𝓞 F) n) (hn : 4 ≤ n) {v : HeightOneSpectrum (𝓞 F)}
    (hv : IsGoodPlace Q v) {s : ℝ} (hs : 0 ≤ s) :
    |zetaRatio Q v s - 1| ≤ 2 * (normP v : ℝ) ^ (-(2 : ℝ)) := by
  obtain ⟨h2, hd⟩ := not_dvd_of_isGoodPlace hv
  have h := abs_zetaRatio_sub_one_le_two v (NF.Qp v Q) hn h2 hd hs
  rw [qv_eq] at h
  rw [zetaRatio, zetaStd, Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two]
  exact h

/-- **Absolute convergence of $\prod_v Z_v(s)/\lambda_v(s)$** for every real $s \ge 0$ ($n \ge 4$; Weil 1982, §4.5,
p. 108, "the infinite product ... is absolutely convergent"): from `abs_zetaRatio_sub_one_le_normP` and
$\sum_\mathfrak p N\mathfrak p^{-2} < \infty$. -/
@[kb "weil1982" "§4.5, p. 108 (absolute convergence of the product, m > 4)"]
theorem multipliable_zetaRatio (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 4 ≤ n) {s : ℝ}
    (hs : 0 ≤ s) : Multipliable fun v => zetaRatio Q v s :=
  multipliable_of_abs_sub_one_le _ (C := 2) (σ := 2) (by norm_num)
    ((isGoodPlace_cofinite Q hQ).mono fun _ hv => abs_zetaRatio_sub_one_le_normP Q hn hv hs)

lemma normP_rpow_neg_one_add (v : HeightOneSpectrum (𝓞 F)) (s : ℝ) :
    (normP v : ℝ) ^ (-(1 + s)) = (qv v)⁻¹ * (qv v) ^ (-s) := by
  have h0 : (0 : ℝ) < normP v := by exact_mod_cast (show 0 < normP v by have := two_le_normP v; omega)
  rw [qv_eq, neg_add, Real.rpow_add h0, Real.rpow_neg_one]

/-- **Weil's local factor as $\zeta_v(1+s)\cdot Z_v/\lambda_v$** (Weil 1982, §4.4, pp. 93–94, and §4.5, p. 108): for $s \ge 0$,
$$Z_\mathfrak p(s) = \frac{Z_v(s)}{1-q_v^{-1}} = \frac{Z_v(s)}{\lambda_v(s)}\cdot(1 - N\mathfrak p_v^{-1-s})^{-1}.$$ -/
theorem zetaWeil_eq (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) {s : ℝ} (hs : 0 ≤ s) :
    zetaWeil Q v s = zetaRatio Q v s * (1 - (normP v : ℝ) ^ (-(1 + s)))⁻¹ := by
  have h1 : 1 - (qv v)⁻¹ ≠ 0 := sub_ne_zero.mpr (inv_lt_one_of_one_lt₀ (one_lt_qv v)).ne'
  have h2 := one_sub_rho_ne v s hs
  rw [normP_rpow_neg_one_add, zetaWeil, zetaRatio, lambdaV]
  have key : ∀ Z A B : ℝ, A ≠ 0 → B ≠ 0 → Z / A = Z / (A / B) * B⁻¹ := by
    intro Z A B hA hB; field_simp
  exact key _ _ _ h1 h2

/-- **The Euler product of Weil's local zeta functions** (Weil 1982, §4.5, pp. 106–108; the multiplicative
calculation): for real $s > 0$ and $n \ge 4$,
$$\prod_v Z_\mathfrak p(s) = \zeta_F(1+s)\prod_v\frac{Z_v(s)}{\lambda_v(s)},$$
the product over all finite places converging unconditionally (`HasProd`). Here $\zeta_F$ = `dedekindZetaR F`
($= \operatorname{Re}$ of Mathlib's `dedekindZeta`, real for real argument $> 1$) and
$\prod_v(1-N\mathfrak p_v^{-1-s})^{-1} = \zeta_F(1+s)$ (`hasProd_dedekindZeta`). -/
@[kb "weil1982" "§4.5, pp. 106–108 (the multiplicative calculation)"]
theorem hasProd_zetaWeil (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 4 ≤ n) {s : ℝ} (hs : 0 < s) :
    HasProd (fun v => zetaWeil Q v s) (dedekindZetaR F (1 + s) * ∏' v, zetaRatio Q v s) := by
  have h := (multipliable_zetaRatio Q hQ hn hs.le).hasProd.mul (hasProd_dedekindZeta (F := F)
    (show 1 < 1 + s by linarith))
  rw [mul_comm]
  exact h.congr_fun fun v => zetaWeil_eq Q v hs.le

/-! ### The Weierstrass M-test on $[0,1]$ -/

lemma abs_log_le_two_mul {x : ℝ} (hx : |x - 1| ≤ 1 / 2) : |Real.log x| ≤ 2 * |x - 1| := by
  have hx0 : 1 / 2 ≤ x := by linarith [(abs_le.mp hx).1]
  have hxp : 0 < x := by linarith
  have hu := Real.log_le_sub_one_of_pos hxp
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hxp)
  rw [Real.log_inv] at hl
  have hinv : x⁻¹ - 1 ≤ 2 * |x - 1| := by
    rw [inv_eq_one_div, div_sub_one hxp.ne', div_le_iff₀ hxp]
    cases abs_cases (x - 1) <;> nlinarith
  rw [abs_le]; constructor
  · linarith
  · linarith [le_abs_self (x - 1), abs_nonneg (x - 1)]

/-- At a good place: $|\log(Z_v/\lambda_v)(s)| \le 4N\mathfrak p_v^{-2}$ for all $s \ge 0$. -/
theorem abs_log_zetaRatio_le_good (Q : QuadForm (𝓞 F) n) (hn : 4 ≤ n) {v : HeightOneSpectrum (𝓞 F)}
    (hv : IsGoodPlace Q v) {s : ℝ} (hs : 0 ≤ s) :
    |Real.log (zetaRatio Q v s)| ≤ 4 * (normP v : ℝ) ^ (-(2 : ℝ)) := by
  have h := abs_zetaRatio_sub_one_le_normP Q hn hv hs
  have hN : (2 : ℝ) ≤ normP v := by exact_mod_cast two_le_normP v
  have hb : 2 * (normP v : ℝ) ^ (-(2 : ℝ)) ≤ 1 / 2 := by
    rw [Real.rpow_neg (by linarith), Real.rpow_two]
    have : (4 : ℝ) ≤ (normP v : ℝ) ^ 2 := by nlinarith
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]; linarith
  calc |Real.log (zetaRatio Q v s)| ≤ 2 * |zetaRatio Q v s - 1| := abs_log_le_two_mul (h.trans hb)
    _ ≤ 2 * (2 * (normP v : ℝ) ^ (-(2 : ℝ))) := by gcongr
    _ = _ := by ring

open Classical in
/-- **The majorant of the M-test**: $u_v = 4N\mathfrak p_v^{-2}$, plus, at the finitely many bad places, a bound $C_v$ for the
continuous function $|\log(Z_v/\lambda_v)|$ on the compact $[0,1]$. -/
def logBound (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  4 * (normP v : ℝ) ^ (-(2 : ℝ)) +
    if h : ∃ C, ∀ s ∈ Set.Icc (0 : ℝ) 1, |Real.log (zetaRatio Q v s)| ≤ C then
      (if IsGoodPlace Q v then 0 else max h.choose 0) else 0

lemma exists_bound_log (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ C, ∀ s ∈ Set.Icc (0 : ℝ) 1, |Real.log (zetaRatio Q v s)| ≤ C := by
  have hc : ContinuousOn (fun s => Real.log (zetaRatio Q v s)) (Set.Icc 0 1) :=
    ((continuousOn_zetaRatio Q hQ hn v).mono Set.Icc_subset_Ici_self).log fun s hs =>
      (zetaRatio_pos Q hQ hn v hs.1).ne'
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact ⟨C, fun s hs => by simpa [Real.norm_eq_abs] using hC s hs⟩

/-- **The M-test bound**: $|\log(Z_v/\lambda_v)(s)| \le u_v$ for every place $v$ and every $s \in [0,1]$. -/
theorem abs_log_zetaRatio_le (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 4 ≤ n)
    (v : HeightOneSpectrum (𝓞 F)) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    |Real.log (zetaRatio Q v s)| ≤ logBound Q v := by
  classical
  have hex := exists_bound_log Q hQ (by omega) v
  have h4 : 0 ≤ 4 * (normP v : ℝ) ^ (-(2 : ℝ)) := by positivity
  unfold logBound
  rw [dif_pos hex]
  by_cases hv : IsGoodPlace Q v
  · simp only [hv, ite_true, add_zero]; exact abs_log_zetaRatio_le_good Q hn hv hs.1
  · simp only [hv, ite_false]
    exact (hex.choose_spec s hs).trans ((le_max_left _ _).trans (le_add_of_nonneg_left h4))

/-- **$\sum_v u_v < \infty$** (the M-test majorant is summable): $\sum_\mathfrak p N\mathfrak p^{-2} < \infty$, and the correction
terms vanish outside the finite set of bad places. -/
theorem summable_logBound (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) : Summable (logBound Q) := by
  classical
  refine ((summable_normP_rpow (F := F) (σ := 2) (by norm_num)).mul_left 4).add ?_
  refine summable_of_ne_finset_zero (s := (finite_not_isGoodPlace Q hQ).toFinset) fun v hv => ?_
  have hv' : IsGoodPlace Q v := by simpa using hv
  split_ifs <;> rfl

/-- **$R(s) = \prod_v Z_v(s)/\lambda_v(s)$** (`tprod`; for $n \ge 4$ and $s \ge 0$ the product converges absolutely,
`multipliable_zetaRatio`). -/
def zetaRatioProd (Q : QuadForm (𝓞 F) n) (s : ℝ) : ℝ := ∏' v, zetaRatio Q v s

/-- On $[0,1]$: $R(s) = \exp\sum_v\log(Z_v/\lambda_v)(s)$. -/
theorem zetaRatioProd_eq_exp (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 4 ≤ n) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    zetaRatioProd Q s = Real.exp (∑' v, Real.log (zetaRatio Q v s)) := by
  have hsum : Summable fun v => Real.log (zetaRatio Q v s) :=
    Summable.of_norm_bounded (summable_logBound Q hQ) fun v => by
      rw [Real.norm_eq_abs]; exact abs_log_zetaRatio_le Q hQ hn v hs
  exact (Real.hasProd_of_hasSum_log (fun v => zetaRatio_pos Q hQ (by omega) v hs.1) hsum.hasSum).tprod_eq

/-- **Uniform convergence and continuity of $\prod_v Z_v/\lambda_v$ on $[0,1]$** (Weil 1982, §4.5, p. 108: the product is
bounded between $\prod(1 - q^{-m'})$ and $\prod(1 + q^{-m'})$ uniformly in $s$): by the M-test
(`abs_log_zetaRatio_le`, `summable_logBound`) the series $\sum_v\log(Z_v/\lambda_v)(s)$ converges uniformly on $[0,1]$ to a
continuous function. -/
@[kb "weil1982" "§4.5, p. 108 (uniform bounds for the product, m' ≥ 2)"]
theorem continuousOn_zetaRatioProd (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 4 ≤ n) :
    ContinuousOn (zetaRatioProd Q) (Set.Icc 0 1) := by
  have hL : ContinuousOn (fun s => ∑' v, Real.log (zetaRatio Q v s)) (Set.Icc 0 1) :=
    continuousOn_tsum (fun v => ((continuousOn_zetaRatio Q hQ (by omega) v).mono
      Set.Icc_subset_Ici_self).log fun s hs => (zetaRatio_pos Q hQ (by omega) v hs.1).ne')
      (summable_logBound Q hQ) fun v s hs => by
        rw [Real.norm_eq_abs]; exact abs_log_zetaRatio_le Q hQ hn v hs
  exact (Real.continuous_exp.comp_continuousOn hL).congr fun s hs => zetaRatioProd_eq_exp Q hQ hn hs

/-- $R(0) = \prod_v Z_v(0)/\lambda_v(0) = 1$. -/
theorem zetaRatioProd_zero (Q : QuadForm (𝓞 F) n) : zetaRatioProd Q 0 = 1 := by
  simp [zetaRatioProd, zetaRatio_zero]

/-- **$\prod_v Z_v(s)/\lambda_v(s) \to 1$ as $s \to 0^+$** ($n \ge 4$). -/
theorem tendsto_zetaRatioProd_zero (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 4 ≤ n) :
    Tendsto (zetaRatioProd Q) (𝓝[>] 0) (𝓝 1) := by
  have h : Tendsto (zetaRatioProd Q) (𝓝[Set.Icc 0 1] 0) (𝓝 (zetaRatioProd Q 0)) :=
    (continuousOn_zetaRatioProd Q hQ hn) 0 ⟨le_rfl, zero_le_one⟩
  rw [zetaRatioProd_zero] at h
  exact h.mono_left (nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem ⟨le_rfl, zero_lt_one⟩))

end QuadFormsKB.GlobalZeta
