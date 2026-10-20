/-
# Local spherical factors at the finite places

**Layer:** local, a finite place $v$ of a number field $F$; notation and measures as in `LocalZeta.lean` ($F_v$,
$\mathcal O_v$, $\pi$, $q = N(v)$, $L_v = \mathcal O_v^n$, $\nu$ = `haarV` with $\operatorname{vol}(\mathcal O_v) = 1$).
$Q$ is a nondegenerate quadratic form over $\mathcal O_v$ (`QuadForm 𝔬 n`), $d_j = a_j - a_{j+1} =
\operatorname{vol}\{x \in L_v : \operatorname{ord}_v Q(x) = j\}$ (the level sets, `real_levelSet`).

**Results.**
* `hasSum_setIntegral_level`: for a measurable $A \subseteq F_v^n$ and $s \ge 0$,
  $\int_{L_v\cap A}|Q(x)|_v^s\,dx = \sum_j q^{-js}\operatorname{vol}(\{\operatorname{ord}Q = j\}\cap A)$.
* `genSeries Q Y` $= G(Y) = \sum_j Y^j d_j$ for $|Y| \le 1$ (so $Z_v(s) = G(q^{-s})$), and at a good place
  ($v \nmid 2\det H_Q$) the **closed forms for every $|Y| \le 1$** (`genSeries_good_even`, `genSeries_good_odd`), which give the
  **twisted** factors: $G(-q^{-s}) = \sum_j(-1)^jq^{-js}d_j$ is the local factor of the integral of $|Q|^s\lambda(Q(x))$ for an
  unramified quadratic character $\lambda$ with $\lambda(\pi) = -1$ (Weil 1982, §4.4, p. 93, the factors $\lambda_\mathfrak p(t) =
  \lambda(\mathfrak p)^r$ for $|t|_\mathfrak p = q^{-r}$).
* `abs_genRatio_sub_one_le`: $|G(Y)(1-q^{-1}Y)/(1-q^{-1}) - 1| \le 4q^{-\lfloor n/2\rfloor}$ for $|Y| \le 1$.

Sources: A. Weil, *Adeles and Algebraic Groups* (1982), §4.3, Lemma 4.3.2, pp. 89–90; §4.4, p. 93; §4.5, Lemma 4.5.2, p. 103.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.SphericalZeta

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

/-! ### Series over the levels, restricted to a measurable set -/

/-- **The level series on a subset** (every finite place, any $\nu$): for $A$ measurable and $s \ge 0$,
$$\int_{L_v\cap A}|Q(x)|_v^s\,d\nu^{\otimes n} = \sum_{j\ge0}(q^{-s})^j\,\nu^{\otimes n}(\{x\in L_v:\operatorname{ord}_vQ(x) = j\}\cap A).$$ -/
theorem hasSum_setIntegral_level (ν : Measure (v.adicCompletion F)) [SigmaFinite ν] [Measure.IsAddRightInvariant ν]
    [IsFiniteMeasureOnCompacts ν] (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n)
    {A : Set (Fin n → Fv)} (hA : MeasurableSet A) {s : ℝ} (hs : 0 ≤ s) :
    HasSum (fun j : ℕ => ((DVR.q 𝔬 : ℝ) ^ (-s)) ^ j *
      (Measure.pi fun _ : Fin n => ν).real (levelSet v Q j ∩ A))
      (∫ x in latL v n ∩ A, ‖Q.evalIn Fv x‖ ^ s ∂(Measure.pi fun _ : Fin n => ν)) := by
  set μ := Measure.pi fun _ : Fin n => ν
  have hq0 : (0 : ℝ) < DVR.q 𝔬 := by exact_mod_cast q_pos v
  have hLfin : μ (latL v n) ≠ ⊤ := by
    rw [measure_latL]; exact ENNReal.pow_ne_top (isCompact_latticeV v 0).measure_lt_top.ne
  have hcont : Continuous fun x : Fin n → Fv => Q.evalIn Fv x := by
    unfold QuadForm.evalIn
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by
      split_ifs <;> fun_prop
  have hmeas : Measurable fun x : Fin n → Fv => ‖Q.evalIn Fv x‖ ^ s :=
    (continuous_norm.comp hcont).measurable.pow_const s
  have hU : (⋃ j, levelSet v Q j ∩ A) = (latL v n \ nullCone v Q) ∩ A := by
    rw [← Set.iUnion_inter, iUnion_levelSet]
  have hint : IntegrableOn (fun x : Fin n → Fv => ‖Q.evalIn Fv x‖ ^ s) (⋃ j, levelSet v Q j ∩ A) μ := by
    rw [hU]
    refine (Measure.integrableOn_of_bounded (M := 1) hLfin hmeas.aestronglyMeasurable ?_).mono_set
      (fun x hx => hx.1.1)
    refine (ae_restrict_iff' (measurableSet_latL v)).mpr (Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_one (norm_nonneg _) (norm_le_one_of_valued v (valued_evalIn_le_one v Q hx)) hs
  have hdisj : Pairwise (Function.onFun Disjoint fun j => levelSet v Q j ∩ A) := fun i j hij =>
    (levelSet_disjoint v Q hij).mono Set.inter_subset_left Set.inter_subset_left
  have h := hasSum_integral_iUnion (fun j => (measurableSet_levelSet v Q j).inter hA) hdisj hint
  have e1 : ∫ x in ⋃ j, levelSet v Q j ∩ A, ‖Q.evalIn Fv x‖ ^ s ∂μ =
      ∫ x in latL v n ∩ A, ‖Q.evalIn Fv x‖ ^ s ∂μ := by
    rw [hU]
    refine setIntegral_congr_set ?_
    have h0 : μ (nullCone v Q) = 0 := measure_nullCone v ν Q hQ hn
    have : (latL v n \ nullCone v Q) ∩ A =ᵐ[μ] latL v n ∩ A := by
      rw [Set.sdiff_inter_right_comm]
      exact sdiff_null_ae_eq_self h0
    exact this
  rw [e1] at h
  convert h using 1
  funext j
  rw [setIntegral_congr_fun ((measurableSet_levelSet v Q j).inter hA)
    (g := fun _ => ((DVR.q 𝔬 : ℝ) ^ (-s)) ^ j) (fun x hx => by
      simp only
      rw [norm_evalIn_of_mem_diff v Q j hx.1, rpow_inv_pow _ hq0]),
    setIntegral_const, smul_eq_mul, mul_comm]

/-! ### The generating series $G(Y) = \sum_j Y^j d_j$ -/

/-- $d_j = a_j - a_{j+1} = \operatorname{vol}\{x \in L_v : \operatorname{ord}_vQ(x) = j\}$ (standard Haar measure). -/
def dSeq (Q : QuadForm 𝔬 n) (j : ℕ) : ℝ := (aSeq v Q j : ℝ) - aSeq v Q (j + 1)

lemma dSeq_nonneg (Q : QuadForm 𝔬 n) (j : ℕ) : 0 ≤ dSeq v Q j :=
  sub_nonneg.mpr (aSeq_antitone v Q (Nat.le_succ j))

lemma dSeq_eq_real_levelSet (Q : QuadForm 𝔬 n) (j : ℕ) :
    dSeq v Q j = (Measure.pi fun _ : Fin n => haarV v).real (levelSet v Q j) := by
  rw [real_levelSet, haarV_real_O, one_pow, one_mul, dSeq]

lemma hasSum_dSeq (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) : HasSum (dSeq v Q) 1 := by
  have ht := tendsto_aSeq v Q hQ hn
  have hsum : ∀ N, ∑ j ∈ Finset.range N, dSeq v Q j = 1 - aSeq v Q N := by
    intro N
    induction N with
    | zero => simp [aSeq_zero]
    | succ N ih => rw [Finset.sum_range_succ, ih, dSeq]; ring
  have hlim : Tendsto (fun N => ∑ j ∈ Finset.range N, dSeq v Q j) atTop (𝓝 1) := by
    simp_rw [hsum]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub ht
  exact (hasSum_iff_tendsto_nat_of_nonneg (dSeq_nonneg v Q) 1).mpr hlim

lemma summable_dSeq (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) : Summable (dSeq v Q) :=
  (hasSum_dSeq v Q hQ hn).summable

lemma summable_pow_mul_dSeq (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) {Y : ℝ} (hY : |Y| ≤ 1) :
    Summable fun j => Y ^ j * dSeq v Q j := by
  refine Summable.of_norm_bounded (summable_dSeq v Q hQ hn) fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (dSeq_nonneg v Q j)]
  exact mul_le_of_le_one_left (dSeq_nonneg v Q j) (pow_le_one₀ (abs_nonneg _) hY)

/-- **The generating series** $G(Y) = \sum_{j\ge0}Y^jd_j$ ($|Y| \le 1$). $G(q^{-s}) = Z_v(s)$ (standard Haar measure). -/
def genSeries (Q : QuadForm 𝔬 n) (Y : ℝ) : ℝ := ∑' j, Y ^ j * dSeq v Q j

lemma genSeries_eq_zetaInt (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) {s : ℝ} (hs : 0 ≤ s) :
    genSeries v Q ((DVR.q 𝔬 : ℝ) ^ (-s)) = zetaInt v (haarV v) Q s := by
  have h := hasSum_zetaInt v (haarV v) Q hQ hn hs
  rw [haarV_real_O, one_pow] at h
  simp only [one_mul] at h
  exact h.tsum_eq

/-- **The good-place identity for $G(Y)$, any $|Y| \le 1$** (the algebra of `zetaInt_good_N1`, with $q^{-s}$ replaced by
$Y$): with $\rho = q^{-1}$, $\gamma = (N_1 - 1)q^{1-n}$,
$$(1-\rho Y)(1-q^{-n}Y^2)G(Y) = (1-\rho Y)(d_0 + d_1Y) + \gamma(1-\rho)(\rho Y)^2.$$ -/
theorem genSeries_good_N1 (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) (h2 : ¬ πv ∣ 2)
    (hdet : ¬ πv ∣ Q.hessian.det) {Y : ℝ} (hY : |Y| ≤ 1) :
    (1 - qv⁻¹ * Y) * ((1 - (qv ^ n)⁻¹ * Y ^ 2) * genSeries v Q Y) =
      (1 - qv⁻¹ * Y) *
        ((1 - (N1 v Q : ℝ) / qv ^ n) + Y * ((N1 v Q : ℝ) / qv ^ n - ((N1 v Q : ℝ) - 1) / qv ^ n * qv⁻¹
          - (qv ^ n)⁻¹)) +
        ((N1 v Q : ℝ) - 1) / qv ^ n * qv * (1 - qv⁻¹) * (qv⁻¹ * Y) ^ 2 := by
  have hq1 : (1 : ℝ) < qv := by exact_mod_cast (q_ge_two v)
  have hq0 : (0 : ℝ) < qv := by linarith
  set γ : ℝ := ((N1 v Q : ℝ) - 1) / qv ^ n * qv
  have hc : ∀ j, 1 ≤ j → (cSeq v Q j : ℝ) = γ * qv⁻¹ ^ j := by
    intro j hj
    rw [cSeq_good v Q hQ hn h2 hdet j hj]; push_cast; ring
  have ha : ∀ j, 2 ≤ j → (aSeq v Q j : ℝ) = γ * qv⁻¹ ^ j + (qv ^ n)⁻¹ * aSeq v Q (j - 2) := by
    intro j hj
    rw [aSeq_rec v Q j hj]; push_cast; rw [hc j (by omega)]
  have hS : HasSum (fun j => Y ^ j * dSeq v Q j) (genSeries v Q Y) :=
    (summable_pow_mul_dSeq v Q hQ hn hY).hasSum
  have key := series_rational (dSeq v Q) Y qv⁻¹ (γ * (1 - qv⁻¹)) (qv ^ n)⁻¹ (genSeries v Q Y) 2 le_rfl hS
    (by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hq0)]
      calc qv⁻¹ * |Y| ≤ qv⁻¹ * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact inv_lt_one_of_one_lt₀ hq1)
    (by
      intro j hj
      simp only [dSeq]
      rw [ha j hj, ha (j + 1) (by omega), show j + 1 - 2 = j - 2 + 1 by omega]
      ring)
  rw [key]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_mul, pow_one,
    show ¬ (2 ≤ 0) by omega, show ¬ (2 ≤ 1) by omega, ite_false, mul_zero, sub_zero, dSeq]
  have h0 : (aSeq v Q 0 : ℝ) = 1 := aSeq_zero v Q
  have h1 : (aSeq v Q 1 : ℝ) = (N1 v Q : ℝ) / qv ^ n := by rw [aSeq_one_good]; push_cast; ring
  have h2' : (aSeq v Q 2 : ℝ) = γ * qv⁻¹ ^ 2 + (qv ^ n)⁻¹ := by
    rw [ha 2 le_rfl, show 2 - 2 = 0 by rfl, h0, mul_one]
  rw [h0, h1, show (1 + 1 : ℕ) = 2 from rfl, h2']
  simp only [γ]
  have : qv ≠ 0 := hq0.ne'
  field_simp
  ring

lemma abs_le_one_aux {a Y : ℝ} (ha0 : 0 ≤ a) (ha : a < 1) (hY : |Y| ≤ 1) : |a * Y| < 1 := by
  rw [abs_mul, abs_of_nonneg ha0]
  calc a * |Y| ≤ a * 1 := by gcongr
    _ < 1 := by rw [mul_one]; exact ha

/-- **The closed form of $G(Y)$, even rank, any $|Y| \le 1$** (Weil's Lemma 4.3.2, p. 89, as a rational function of $Y = q^{-s}$,
here evaluated also at $Y = -q^{-s}$): for $n = 2m$, $m \ge 1$, $v \nmid 2\det H_Q$,
$$G(Y) = \frac{(1-q^{-1})(1-\varepsilon q^{-m})}{(1-q^{-1}Y)(1-\varepsilon q^{-m}Y)},\qquad \varepsilon = \texttt{DVR.chiDisc}\ Q.$$ -/
theorem genSeries_good_even (m : ℕ) (hm : 1 ≤ m) (Q : QuadForm 𝔬 (2 * m)) (h2 : ¬ πv ∣ 2)
    (hdet : ¬ πv ∣ Q.hessian.det) {Y : ℝ} (hY : |Y| ≤ 1) :
    genSeries v Q Y = (1 - qv⁻¹) * (1 - (DVR.chiDisc Q : ℝ) * (qv ^ m)⁻¹) /
        ((1 - qv⁻¹ * Y) * (1 - (DVR.chiDisc Q : ℝ) * (qv ^ m)⁻¹ * Y)) := by
  have hQ : Q.Nondegenerate := fun h => hdet (h ▸ dvd_zero _)
  have hq1 : (1 : ℝ) < qv := by exact_mod_cast (q_ge_two v)
  have hq0 : (0 : ℝ) < qv := by linarith
  have key := genSeries_good_N1 v Q hQ (by omega) h2 hdet hY
  have hN := ((DVR.card_mod_pi_of_unimodular Q πv (NF.irreducible_π v) h2 hdet (by omega) 1
    (fun h => (NF.irreducible_π v).not_isUnit (isUnit_of_dvd_one h))).1 (even_two_mul m)).1
  have hN' : (N1 v Q : ℝ) = qv ^ (2 * m - 1) + (DVR.chiDisc Q : ℝ) * (qv - 1) * qv ^ (2 * m / 2 - 1) := by
    exact_mod_cast hN
  rw [show 2 * m / 2 - 1 = m - 1 by omega] at hN'
  have hε := DVR.chiDisc_sq (NF.irreducible_π v) h2 hdet
  set ε : ℝ := ((DVR.chiDisc Q : ℤ) : ℝ)
  have hε1 : |ε| = 1 := by
    have : |ε| ^ 2 = 1 := by rw [sq_abs]; exact hε
    nlinarith [abs_nonneg ε]
  have hqm : 1 < qv ^ m := one_lt_pow₀ hq1 (by omega)
  have hρY : |qv⁻¹ * Y| < 1 := abs_le_one_aux (inv_pos.mpr hq0).le (inv_lt_one_of_one_lt₀ hq1) hY
  have hρ : 1 - qv⁻¹ * Y ≠ 0 := by
    intro h; have := (abs_lt.mp hρY).2; linarith
  have hεY : 1 - ε * (qv ^ m)⁻¹ * Y ≠ 0 := by
    have : |ε * (qv ^ m)⁻¹ * Y| < 1 := by
      rw [mul_assoc, abs_mul, hε1, one_mul]
      exact abs_le_one_aux (inv_pos.mpr (by linarith)).le (inv_lt_one_of_one_lt₀ hqm) hY
    intro h; have h' := (abs_lt.mp this).2; linarith
  have hY2 : Y ^ 2 ≤ 1 := by rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) hY
  have hX2 : 1 - (qv ^ (2 * m))⁻¹ * Y ^ 2 ≠ 0 := by
    have : (qv ^ (2 * m))⁻¹ * Y ^ 2 < 1 := by
      have h1 : (qv ^ (2 * m))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq1 (by omega))
      nlinarith [inv_pos.mpr (show (0 : ℝ) < qv ^ (2 * m) by positivity), sq_nonneg Y]
    linarith
  have hfac : 1 - (qv ^ (2 * m))⁻¹ * Y ^ 2 = (1 - ε * (qv ^ m)⁻¹ * Y) * (1 + ε * (qv ^ m)⁻¹ * Y) := by
    rw [pow_mul', ← inv_pow]
    linear_combination ((qv ^ m)⁻¹ ^ 2 * Y ^ 2) * hε
  have hB' : 1 + ε * (qv ^ m)⁻¹ * Y ≠ 0 := fun h => hX2 (by rw [hfac, h, mul_zero])
  have hεc : ε = 1 ∨ ε = -1 := mul_self_eq_one_iff.mp (by rw [← sq]; exact hε)
  rw [eq_div_iff (mul_ne_zero hρ hεY)]
  apply mul_right_cancel₀ hB'
  rw [show genSeries v Q Y * ((1 - qv⁻¹ * Y) * (1 - ε * (qv ^ m)⁻¹ * Y)) * (1 + ε * (qv ^ m)⁻¹ * Y) =
      (1 - qv⁻¹ * Y) * ((1 - (qv ^ (2 * m))⁻¹ * Y ^ 2) * genSeries v Q Y) by rw [hfac]; ring, key, hN']
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, show k + 1 - 1 = k by omega]
  have hq0' : qv ≠ 0 := hq0.ne'
  rcases hεc with h | h <;> rw [h] <;> field_simp <;> ring

/-- **The closed form of $G(Y)$, odd rank, any $|Y| \le 1$**: for $n = 2m+1$ and $v \nmid 2\det H_Q$,
$$G(Y) = \frac{(1-q^{-1})(1-q^{-n}Y)}{(1-q^{-1}Y)(1-q^{-n}Y^2)}.$$ -/
theorem genSeries_good_odd (m : ℕ) (Q : QuadForm 𝔬 (2 * m + 1)) (h2 : ¬ πv ∣ 2)
    (hdet : ¬ πv ∣ Q.hessian.det) {Y : ℝ} (hY : |Y| ≤ 1) :
    genSeries v Q Y = (1 - qv⁻¹) * (1 - (qv ^ (2 * m + 1))⁻¹ * Y) /
        ((1 - qv⁻¹ * Y) * (1 - (qv ^ (2 * m + 1))⁻¹ * Y ^ 2)) := by
  have hQ : Q.Nondegenerate := fun h => hdet (h ▸ dvd_zero _)
  have hq1 : (1 : ℝ) < qv := by exact_mod_cast (q_ge_two v)
  have hq0 : (0 : ℝ) < qv := by linarith
  have key := genSeries_good_N1 v Q hQ (by omega) h2 hdet hY
  have hN := ((DVR.card_mod_pi_of_unimodular Q πv (NF.irreducible_π v) h2 hdet (by omega) 1
    (fun h => (NF.irreducible_π v).not_isUnit (isUnit_of_dvd_one h))).2 (odd_two_mul_add_one m)).1
  have hN' : (N1 v Q : ℝ) = qv ^ (2 * m) := by
    have e : 2 * m + 1 - 1 = 2 * m := by omega
    rw [e] at hN; exact_mod_cast hN
  have hρY : |qv⁻¹ * Y| < 1 := abs_le_one_aux (inv_pos.mpr hq0).le (inv_lt_one_of_one_lt₀ hq1) hY
  have hρ : 1 - qv⁻¹ * Y ≠ 0 := by
    intro h; have := (abs_lt.mp hρY).2; linarith
  have hY2 : Y ^ 2 ≤ 1 := by rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) hY
  have hX2 : 1 - (qv ^ (2 * m + 1))⁻¹ * Y ^ 2 ≠ 0 := by
    have : (qv ^ (2 * m + 1))⁻¹ * Y ^ 2 < 1 := by
      have h1 : (qv ^ (2 * m + 1))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq1 (by omega))
      nlinarith [inv_pos.mpr (show (0 : ℝ) < qv ^ (2 * m + 1) by positivity), sq_nonneg Y]
    linarith
  rw [eq_div_iff (mul_ne_zero hρ hX2),
    show genSeries v Q Y * ((1 - qv⁻¹ * Y) * (1 - (qv ^ (2 * m + 1))⁻¹ * Y ^ 2)) =
      (1 - qv⁻¹ * Y) * ((1 - (qv ^ (2 * m + 1))⁻¹ * Y ^ 2) * genSeries v Q Y) by ring, key, hN']
  have hq0' : qv ≠ 0 := hq0.ne'
  field_simp
  ring

lemma bound_even_aux' (ε a Y : ℝ) (hε : ε = 1 ∨ ε = -1) (ha0 : 0 < a) (ha : a ≤ 1 / 2) (hY : |Y| ≤ 1) :
    |(1 - ε * a) / (1 - ε * a * Y) - 1| ≤ 4 * a := by
  obtain ⟨hY1, hY2⟩ := abs_le.mp hY
  have hD : 0 < 1 - ε * a * Y := by rcases hε with rfl | rfl <;> nlinarith
  have hD2 : 1 / 2 ≤ 1 - ε * a * Y := by rcases hε with rfl | rfl <;> nlinarith
  rw [div_sub_one hD.ne', abs_div, abs_of_pos hD, div_le_iff₀ hD, abs_le]
  rcases hε with rfl | rfl <;> constructor <;> nlinarith

lemma bound_odd_aux' (b Y : ℝ) (hb0 : 0 < b) (hb : b ≤ 1 / 2) (hY : |Y| ≤ 1) :
    |(1 - b * Y) / (1 - b * Y ^ 2) - 1| ≤ 4 * b := by
  obtain ⟨hY1, hY2⟩ := abs_le.mp hY
  have hX2 : Y ^ 2 ≤ 1 := by nlinarith
  have hD : 0 < 1 - b * Y ^ 2 := by nlinarith
  have hD2 : 1 / 2 ≤ 1 - b * Y ^ 2 := by nlinarith
  rw [div_sub_one hD.ne', abs_div, abs_of_pos hD, div_le_iff₀ hD, abs_le]
  constructor <;> nlinarith [sq_nonneg Y, sq_nonneg (Y + 1), sq_nonneg (Y - 1)]

/-- **The normalized generating series** $R(Y) = G(Y)(1-q^{-1}Y)/(1-q^{-1})$. At $Y = q^{-s}$ this is the $Z_v/\lambda_v$;
at $Y = -q^{-s}$ it is the normalized twisted factor. -/
def genRatio (Q : QuadForm 𝔬 n) (Y : ℝ) : ℝ := genSeries v Q Y * (1 - qv⁻¹ * Y) / (1 - qv⁻¹)

/-- **The uniform bound at good places, any $|Y| \le 1$** ($n \ge 2$): $|R(Y) - 1| \le 4q^{-\lfloor n/2\rfloor}$. -/
theorem abs_genRatio_sub_one_le (Q : QuadForm 𝔬 n) (hn : 2 ≤ n) (h2 : ¬ πv ∣ 2)
    (hdet : ¬ πv ∣ Q.hessian.det) {Y : ℝ} (hY : |Y| ≤ 1) :
    |genRatio v Q Y - 1| ≤ 4 * (qv ^ (n / 2))⁻¹ := by
  have hq2 : (2 : ℝ) ≤ qv := by exact_mod_cast (q_ge_two v)
  have hq1 : (1 : ℝ) < qv := by linarith
  have hq0 : (0 : ℝ) < qv := by linarith
  have h1 : 1 - qv⁻¹ ≠ 0 := sub_ne_zero.mpr (inv_lt_one_of_one_lt₀ hq1).ne'
  have hρY : |qv⁻¹ * Y| < 1 := abs_le_one_aux (inv_pos.mpr hq0).le (inv_lt_one_of_one_lt₀ hq1) hY
  have hρ : 1 - qv⁻¹ * Y ≠ 0 := by
    intro h; have := (abs_lt.mp hρY).2; linarith
  have hhalf : ∀ k : ℕ, 1 ≤ k → (qv ^ k)⁻¹ ≤ 1 / 2 := by
    intro k hk
    rw [inv_le_comm₀ (by positivity) (by norm_num), one_div, inv_inv]
    calc (2 : ℝ) ≤ qv := hq2
      _ = qv ^ 1 := (pow_one _).symm
      _ ≤ qv ^ k := pow_le_pow_right₀ hq1.le hk
  have hqY : qv - Y ≠ 0 := by
    obtain ⟨-, hY2⟩ := abs_le.mp hY; intro h; linarith
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hε := DVR.chiDisc_sq (NF.irreducible_π v) h2 hdet
    have hεc : ((DVR.chiDisc Q : ℤ) : ℝ) = 1 ∨ ((DVR.chiDisc Q : ℤ) : ℝ) = -1 :=
      mul_self_eq_one_iff.mp (by rw [← sq]; exact hε)
    have hE : 1 - (DVR.chiDisc Q : ℝ) * (qv ^ m)⁻¹ * Y ≠ 0 := by
      have hm1 := hhalf m (by omega)
      obtain ⟨hY1, hY2⟩ := abs_le.mp hY
      have : 0 < (qv ^ m)⁻¹ := inv_pos.mpr (by positivity)
      rcases hεc with h | h <;> rw [h] <;> nlinarith
    have e : genRatio v Q Y = (1 - (DVR.chiDisc Q : ℝ) * (qv ^ m)⁻¹) /
        (1 - (DVR.chiDisc Q : ℝ) * (qv ^ m)⁻¹ * Y) := by
      rw [genRatio, genSeries_good_even v m (by omega) Q h2 hdet hY]
      field_simp
    rw [e, show 2 * m / 2 = m by omega]
    exact bound_even_aux' _ _ _ hεc (by positivity) (hhalf m (by omega)) hY
  · have hY2 : Y ^ 2 ≤ 1 := by rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) hY
    have hE : 1 - (qv ^ (2 * m + 1))⁻¹ * Y ^ 2 ≠ 0 := by
      have := hhalf (2 * m + 1) (by omega)
      have : 0 < (qv ^ (2 * m + 1))⁻¹ := inv_pos.mpr (by positivity)
      nlinarith
    have e : genRatio v Q Y = (1 - (qv ^ (2 * m + 1))⁻¹ * Y) / (1 - (qv ^ (2 * m + 1))⁻¹ * Y ^ 2) := by
      rw [genRatio, genSeries_good_odd v m Q h2 hdet hY]
      field_simp
    rw [e, show (2 * m + 1) / 2 = m by omega]
    have hb := bound_odd_aux' _ _ (inv_pos.mpr (show (0 : ℝ) < qv ^ (2 * m + 1) by positivity))
      (hhalf _ (by omega)) hY
    refine hb.trans (mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity)
      (pow_le_pow_right₀ hq1.le (by omega))) (by norm_num))

/-! ### Square classes of units at a non-dyadic place -/

section SqUnits

local notation "𝔽" => IsLocalRing.ResidueField 𝔬
local notation "res" => IsLocalRing.residue 𝔬

lemma valued_le_one_of_O (z : 𝔬) : Valued.v (z : Fv) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp z.2

lemma valued_eq_one_of_isUnit {z : 𝔬} (hz : IsUnit z) : Valued.v (z : Fv) = 1 := by
  obtain ⟨u, rfl⟩ := hz
  have h1 := valued_le_one_of_O v (u : 𝔬)
  have h2 := valued_le_one_of_O v ((u⁻¹ : 𝔬ˣ) : 𝔬)
  have h3 : Valued.v ((u : 𝔬) : Fv) * Valued.v (((u⁻¹ : 𝔬ˣ) : 𝔬) : Fv) = 1 := by
    rw [← map_mul, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, map_one]
  by_contra h
  have hlt : Valued.v ((u : 𝔬) : Fv) < 1 := lt_of_le_of_ne h1 h
  have : Valued.v ((u : 𝔬) : Fv) * Valued.v (((u⁻¹ : 𝔬ˣ) : 𝔬) : Fv) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  rw [h3] at this; exact lt_irrefl _ this

/-- **The local square theorem at a non-dyadic place**, in $\mathcal O_v$: if $\pi \nmid 2$ and $u \equiv 1 \bmod \pi$, then
$u = a^2$ with $a \in \mathcal O_v$ (from `HN.isSquare_of_valued_sub_one_lt`, $v(u - 1) < 1 = v(4)$). -/
theorem exists_sq_of_dvd_sub_one (h2 : ¬ πv ∣ 2) {u : 𝔬} (hu : πv ∣ u - 1) : ∃ a : 𝔬, u = a ^ 2 := by
  have h4 : Valued.v ((4 : 𝔬) : Fv) = 1 := by
    have h2u : IsUnit (2 : 𝔬) := DVR.dvr_isUnit_of_not_dvd (NF.irreducible_π v) h2
    have : (4 : 𝔬) = 2 * 2 := by norm_num
    exact valued_eq_one_of_isUnit v (this ▸ h2u.mul h2u)
  have hle : Valued.v (((u - 1 : 𝔬)) : Fv) ≤ exp (-(1 : ℤ)) := by
    rw [← pow_one πv] at hu
    exact (NF.mem_span_π_pow v 1 _).mp (Ideal.mem_span_singleton.mpr hu)
  have hlt : Valued.v ((u : Fv) - 1) < Valued.v ((4 : 𝔬) : Fv) := by
    rw [h4]
    have : ((u - 1 : 𝔬) : Fv) = (u : Fv) - 1 := rfl
    rw [← this]
    exact lt_of_le_of_lt hle (by rw [← exp_zero, exp_lt_exp]; omega)
  have h4' : ((4 : 𝔬) : Fv) = (4 : Fv) := rfl
  rw [h4'] at hlt
  obtain ⟨z, hz⟩ := HN.isSquare_of_valued_sub_one_lt v (u : Fv) hlt
  have hz1 : Valued.v z ≤ 1 := by
    have hu1 := valued_le_one_of_O v u
    rw [hz, map_mul] at hu1
    by_contra h
    have h' : 1 < Valued.v z := lt_of_not_ge h
    have : 1 < Valued.v z * Valued.v z := one_lt_mul h'.le h'
    exact absurd (lt_of_lt_of_le this hu1) (lt_irrefl _)
  refine ⟨⟨z, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hz1⟩, ?_⟩
  apply Subtype.ext
  show (u : Fv) = z ^ 2
  rw [hz, sq]

/-- A unit whose residue is a square is a square of a unit. -/
theorem exists_sq_of_residue_isSquare (h2 : ¬ πv ∣ 2) {u : 𝔬} (hu : IsUnit u) (hsq : IsSquare (res u)) :
    ∃ a : 𝔬, IsUnit a ∧ u = a ^ 2 := by
  obtain ⟨rb, hr⟩ := hsq
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective rb
  have hr0 : res r ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hr
    exact (IsLocalRing.residue_ne_zero_iff_isUnit u).mpr hu hr
  have hrU : IsUnit r := (IsLocalRing.residue_ne_zero_iff_isUnit r).mp hr0
  obtain ⟨ri, hri⟩ := hrU.exists_right_inv
  have hdiv : πv ∣ u * ri ^ 2 - 1 := by
    rw [← DVR.residue_eq_zero_iff_dvd (NF.irreducible_π v), map_sub, map_mul, map_pow, hr, map_one]
    have : res r * res ri = 1 := by rw [← map_mul, hri, map_one]
    linear_combination (res r * res ri + 1) * this
  obtain ⟨b, hb⟩ := exists_sq_of_dvd_sub_one v h2 hdiv
  have hriU : IsUnit ri := IsUnit.of_mul_eq_one_right r hri
  have hbU : IsUnit b := by
    have : IsUnit (b * b) := by rw [← sq, ← hb]; exact hu.mul (hriU.pow 2)
    exact isUnit_of_mul_isUnit_left this
  refine ⟨r * b, hrU.mul hbU, ?_⟩
  calc u = u * ri ^ 2 * r ^ 2 := by
        rw [mul_assoc, ← mul_pow, mul_comm ri r, hri, one_pow, mul_one]
    _ = (r * b) ^ 2 := by rw [hb]; ring

/-- **Two square classes of units at a non-dyadic place:** there is a unit $\varepsilon$ which is not a square, and every unit
$u$ is a square or $\varepsilon$ times a square (via the residue field $\mathbb F_q$, $q$ odd, and `exists_sq_of_residue_isSquare`). -/
theorem exists_nonsq_unit (h2 : ¬ πv ∣ 2) :
    ∃ ε : 𝔬, IsUnit ε ∧ (∀ a : 𝔬, ε ≠ a ^ 2) ∧
      ∀ u : 𝔬, IsUnit u → (∃ a : 𝔬, IsUnit a ∧ u = a ^ 2) ∨ (∃ a : 𝔬, IsUnit a ∧ ε * u = a ^ 2) := by
  classical
  letI : Fintype 𝔽 := Fintype.ofFinite _
  have hch := DVR.ringChar_residueField_ne_two (NF.irreducible_π v) h2
  obtain ⟨e, he⟩ := FiniteField.exists_nonsquare hch
  obtain ⟨ε, rfl⟩ := IsLocalRing.residue_surjective e
  have he0 : res ε ≠ 0 := fun h => he (h ▸ IsSquare.zero)
  have hεU : IsUnit ε := (IsLocalRing.residue_ne_zero_iff_isUnit ε).mp he0
  refine ⟨ε, hεU, fun a ha => he ⟨res a, by rw [ha, map_pow, sq]⟩, fun u hu => ?_⟩
  have hu0 : res u ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit u).mpr hu
  by_cases hs : IsSquare (res u)
  · exact Or.inl (exists_sq_of_residue_isSquare v h2 hu hs)
  · right
    refine exists_sq_of_residue_isSquare v h2 (hεU.mul hu) ?_
    have h1 : quadraticChar 𝔽 (res ε) = -1 := (quadraticChar_neg_one_iff_not_isSquare).mpr he
    have h2' : quadraticChar 𝔽 (res u) = -1 := (quadraticChar_neg_one_iff_not_isSquare).mpr hs
    have : quadraticChar 𝔽 (res (ε * u)) = 1 := by
      rw [map_mul, map_mul (quadraticChar 𝔽), h1, h2']; norm_num
    exact (quadraticChar_one_iff_isSquare (by rw [map_mul]; exact mul_ne_zero he0 hu0)).mp this

end SqUnits

/-! ### Square-class sets at a level -/

section Classes

open Classical

/-- **The class set** $C_j(w) = \{x \in L_v : Q(x) \in \pi^j w\,\mathcal O_v^{\times2}\}$ ($w$ a unit). -/
def clsSet (Q : QuadForm 𝔬 n) (j : ℕ) (w : 𝔬) : Set (Fin n → Fv) :=
  {x | x ∈ latL v n ∧ ∃ a : 𝔬, IsUnit a ∧ Q.evalIn Fv x = ((πv ^ j * w * a ^ 2 : 𝔬) : Fv)}

/-- The residues $\pi^jwa^2 \bmod \pi^{j+1}$, $a$ a unit. -/
noncomputable def clsRes (j : ℕ) (w : 𝔬) : Finset (RQ v (j + 1)) :=
  haveI := DVR.finite_quot_pow πv (NF.irreducible_π v) (j + 1)
  haveI : Fintype (RQ v (j + 1)) := Fintype.ofFinite _
  Finset.univ.filter fun t => ∃ a : 𝔬, IsUnit a ∧ Ideal.Quotient.mk _ (πv ^ j * w * a ^ 2) = t

lemma mem_clsRes {j : ℕ} {w : 𝔬} {t : RQ v (j + 1)} :
    t ∈ clsRes v j w ↔ ∃ a : 𝔬, IsUnit a ∧ Ideal.Quotient.mk _ (πv ^ j * w * a ^ 2) = t := by
  simp [clsRes]

lemma mem_congSet_iff_mk (Q : QuadForm 𝔬 n) {x : Fin n → Fv} (hx : x ∈ latL v n) (t : 𝔬) (k : ℕ) :
    x ∈ congSet v Q (t : Fv) k ↔
      Ideal.Quotient.mk (Ideal.span {πv ^ k}) (Q.eval (toO v x hx)) = Ideal.Quotient.mk _ t := by
  show x ∈ latL v n ∧ Valued.v (Q.evalIn Fv x - (t : Fv)) ≤ exp (-(k : ℤ)) ↔ _
  rw [evalIn_toO v Q x hx, ← valued_sub_le_iff_mk_eq]
  exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩

theorem clsSet_eq_biUnion (Q : QuadForm 𝔬 n) (h2 : ¬ πv ∣ 2) (j : ℕ) {w : 𝔬} (hw : IsUnit w) :
    clsSet v Q j w = ⋃ t ∈ clsRes v j w, congSet v Q ((Quotient.out t : 𝔬) : Fv) (j + 1) := by
  ext x
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨hx, a, ha, hQ⟩
    refine ⟨Ideal.Quotient.mk _ (πv ^ j * w * a ^ 2), (mem_clsRes v).mpr ⟨a, ha, rfl⟩, ?_⟩
    rw [mem_congSet_iff_mk v Q hx, Ideal.Quotient.mk_out]
    congr 1
    apply Subtype.ext
    rw [← evalIn_toO v Q x hx]; exact hQ
  · rintro ⟨t, ht, hxt⟩
    have hx : x ∈ latL v n := hxt.1
    obtain ⟨a, ha, rfl⟩ := (mem_clsRes v).mp ht
    rw [mem_congSet_iff_mk v Q hx, Ideal.Quotient.mk_out, Ideal.Quotient.eq,
      Ideal.mem_span_singleton] at hxt
    obtain ⟨c, hc⟩ := hxt
    set z := Q.eval (toO v x hx)
    obtain ⟨ui, hui⟩ := (hw.mul (ha.pow 2)).exists_right_inv
    have hdiv : πv ∣ (1 + πv * c * ui) - 1 := ⟨c * ui, by ring⟩
    obtain ⟨d, hd⟩ := exists_sq_of_dvd_sub_one v h2 hdiv
    have hdU : IsUnit d := by
      have h1 : IsUnit (1 + πv * c * ui) := by
        rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
        have : IsLocalRing.residue 𝔬 (πv * c * ui) = 0 := by
          rw [DVR.residue_eq_zero_iff_dvd (NF.irreducible_π v)]; exact ⟨c * ui, by ring⟩
        rw [map_add, this, map_one, add_zero]; exact one_ne_zero
      rw [hd] at h1; exact isUnit_of_mul_isUnit_left (by rw [← sq]; exact h1)
    refine ⟨hx, a * d, ha.mul hdU, ?_⟩
    rw [evalIn_toO v Q x hx]
    congr 1
    have hz : z = πv ^ j * w * a ^ 2 + πv ^ (j + 1) * c := by rw [← hc]; ring
    calc z = πv ^ j * w * a ^ 2 * (1 + πv * c * ui) := by
          linear_combination hz - πv ^ (j + 1) * c * hui
      _ = πv ^ j * w * (a * d) ^ 2 := by rw [hd]; ring

lemma congSet_out_disjoint (Q : QuadForm 𝔬 n) {k : ℕ} {t t' : RQ v k} (h : t ≠ t') :
    Disjoint (congSet v Q ((Quotient.out t : 𝔬) : Fv) k) (congSet v Q ((Quotient.out t' : 𝔬) : Fv) k) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have hL : x ∈ latL v n := hx.1
  rw [mem_congSet_iff_mk v Q hL, Ideal.Quotient.mk_out] at hx hx'
  exact h (hx.symm.trans hx')

lemma repCount_out_clsRes (Q : QuadForm 𝔬 n) {j : ℕ} {w : 𝔬} {t : RQ v (j + 1)} (ht : t ∈ clsRes v j w) :
    DVR.repCount Q πv (j + 1) (Quotient.out t) = DVR.repCount Q πv (j + 1) (πv ^ j * w) := by
  obtain ⟨a, ha, rfl⟩ := (mem_clsRes v).mp ht
  have hdvd : πv ^ (j + 1) ∣ Quotient.out (Ideal.Quotient.mk (Ideal.span {πv ^ (j + 1)}) (πv ^ j * w * a ^ 2)) -
      πv ^ j * w * a ^ 2 := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
  rw [DVR.repCount_congr_mod Q πv (j + 1) hdvd, show πv ^ j * w * a ^ 2 = a ^ 2 * (πv ^ j * w) by ring,
    DVR.repCount_mul_sq_unit Q πv (j + 1) ha]

/-- **The volume of a class set** ($v \nmid 2$, $w$ a unit):
$\operatorname{vol}(C_j(w)) = |R_j(w)|\cdot r_{\pi^{j+1}}(\pi^jw)\cdot q^{-(j+1)n}$, $R_j(w)$ the residues $\pi^jwa^2 \bmod \pi^{j+1}$. -/
theorem real_clsSet (Q : QuadForm 𝔬 n) (h2 : ¬ πv ∣ 2) (j : ℕ) {w : 𝔬} (hw : IsUnit w) :
    (Measure.pi fun _ : Fin n => haarV v).real (clsSet v Q j w) =
      (clsRes v j w).card * (DVR.repCount Q πv (j + 1) (πv ^ j * w) : ℝ) * ((qv ^ (j + 1))⁻¹) ^ n := by
  rw [clsSet_eq_biUnion v Q h2 j hw, Measure.real, measure_biUnion_finset]
  · rw [ENNReal.toReal_sum]
    · have hterm : ∀ t ∈ clsRes v j w, ((Measure.pi fun _ : Fin n => haarV v)
          (congSet v Q ((Quotient.out t : 𝔬) : Fv) (j + 1))).toReal =
          (DVR.repCount Q πv (j + 1) (πv ^ j * w) : ℝ) * ((qv ^ (j + 1))⁻¹) ^ n := by
        intro t ht
        rw [volume_congSet, repCount_out_clsRes v Q ht, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ← Measure.real, real_latticeV_eq, haarV_real_O, one_mul]
        simp
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
      ring
    · intro t _
      rw [volume_congSet]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.pow_ne_top (isCompact_latticeV v _).measure_lt_top.ne)
  · intro t _ t' _ h
    exact congSet_out_disjoint v Q h
  · intro t _
    exact measurableSet_congSet v Q _ _

lemma mem_congSet_zero_iff (Q : QuadForm 𝔬 n) {x : Fin n → Fv} (hx : x ∈ latL v n) (k : ℕ) :
    x ∈ congSet v Q ((0 : 𝔬) : Fv) k ↔ πv ^ k ∣ Q.eval (toO v x hx) := by
  rw [mem_congSet_iff_mk v Q hx, Ideal.Quotient.eq, sub_zero, Ideal.mem_span_singleton]

lemma mem_levelSet_iff (Q : QuadForm 𝔬 n) {x : Fin n → Fv} (hx : x ∈ latL v n) (j : ℕ) :
    x ∈ levelSet v Q j ↔ πv ^ j ∣ Q.eval (toO v x hx) ∧ ¬ πv ^ (j + 1) ∣ Q.eval (toO v x hx) := by
  rw [levelSet, Set.mem_sdiff, mem_congSet_zero_iff v Q hx, mem_congSet_zero_iff v Q hx]

lemma clsSet_subset_latL (Q : QuadForm 𝔬 n) (j : ℕ) (w : 𝔬) : clsSet v Q j w ⊆ latL v n := fun _ hx => hx.1

lemma eval_toO_of_mem_clsSet (Q : QuadForm 𝔬 n) {j : ℕ} {w : 𝔬} {x : Fin n → Fv} (hx : x ∈ clsSet v Q j w) :
    ∃ a : 𝔬, IsUnit a ∧ Q.eval (toO v x hx.1) = πv ^ j * w * a ^ 2 := by
  obtain ⟨hL, a, ha, hQ⟩ := hx
  refine ⟨a, ha, Subtype.ext ?_⟩
  rw [← evalIn_toO v Q x hL]; exact hQ

lemma clsSet_subset_levelSet (Q : QuadForm 𝔬 n) (j : ℕ) {w : 𝔬} (hw : IsUnit w) :
    clsSet v Q j w ⊆ levelSet v Q j := by
  intro x hx
  obtain ⟨a, ha, he⟩ := eval_toO_of_mem_clsSet v Q hx
  rw [mem_levelSet_iff v Q hx.1, he, mul_assoc]
  exact ⟨dvd_mul_right _ _, DVR.dvr_not_pow_succ_dvd (NF.irreducible_π v) (hw.mul (ha.pow 2)) j⟩

/-- **The level set splits into the two square classes** ($v \nmid 2$, $w$ a unit, $\varepsilon$ a non-square unit):
$\{x \in L_v : \operatorname{ord}Q(x) = j\} = C_j(w) \sqcup C_j(\varepsilon w)$. -/
theorem levelSet_eq_union (Q : QuadForm 𝔬 n) (h2 : ¬ πv ∣ 2) (j : ℕ) {w ε : 𝔬} (hw : IsUnit w)
    (hε : IsUnit ε) (hεsq : ∀ a : 𝔬, ε ≠ a ^ 2)
    (hdich : ∀ u : 𝔬, IsUnit u → (∃ a : 𝔬, IsUnit a ∧ u = a ^ 2) ∨ (∃ a : 𝔬, IsUnit a ∧ ε * u = a ^ 2)) :
    levelSet v Q j = clsSet v Q j w ∪ clsSet v Q j (ε * w) ∧
      Disjoint (clsSet v Q j w) (clsSet v Q j (ε * w)) := by
  obtain ⟨wi, hwi⟩ := hw.exists_right_inv
  obtain ⟨εi, hεi⟩ := hε.exists_right_inv
  have hwiU : IsUnit wi := IsUnit.of_mul_eq_one_right w hwi
  have hεiU : IsUnit εi := IsUnit.of_mul_eq_one_right ε hεi
  constructor
  · ext x
    constructor
    · intro hx
      have hL : x ∈ latL v n := hx.1.1
      obtain ⟨h1, h2'⟩ := (mem_levelSet_iff v Q hL j).mp hx
      obtain ⟨u, hu, huU⟩ := DVR.dvr_exact (NF.irreducible_π v) h1 h2'
      rcases hdich (u * wi) (huU.mul hwiU) with ⟨a, ha, hua⟩ | ⟨a, ha, hua⟩
      · left
        refine ⟨hL, a, ha, ?_⟩
        rw [evalIn_toO v Q x hL, hu]
        congr 1
        linear_combination (πv ^ j * w) * hua - πv ^ j * u * hwi
      · right
        refine ⟨hL, a * εi, ha.mul hεiU, ?_⟩
        rw [evalIn_toO v Q x hL, hu]
        congr 1
        linear_combination (πv ^ j * ε * w * εi ^ 2) * hua - πv ^ j * u * (ε * εi) ^ 2 * hwi -
          πv ^ j * u * (1 + ε * εi) * hεi
    · rintro (hx | hx)
      · exact clsSet_subset_levelSet v Q j hw hx
      · exact clsSet_subset_levelSet v Q j (hε.mul hw) hx
  · rw [Set.disjoint_left]
    intro x hx hx'
    obtain ⟨a, ha, he⟩ := eval_toO_of_mem_clsSet v Q hx
    obtain ⟨b, hb, he'⟩ := eval_toO_of_mem_clsSet v Q hx'
    obtain ⟨bi, hbi⟩ := hb.exists_right_inv
    have hπ0 : πv ^ j ≠ 0 := pow_ne_zero _ (NF.irreducible_π v).ne_zero
    have hw0 : w ≠ 0 := hw.ne_zero
    have e1 : w * a ^ 2 = ε * w * b ^ 2 := by
      have := he.symm.trans he'
      rw [mul_assoc, mul_assoc (πv ^ j)] at this
      exact mul_left_cancel₀ hπ0 this
    apply hεsq (a * bi)
    have e2 : a ^ 2 = ε * b ^ 2 := by
      have : w * a ^ 2 = w * (ε * b ^ 2) := by rw [e1]; ring
      exact mul_left_cancel₀ hw0 this
    calc ε = ε * (b * bi) ^ 2 := by rw [hbi, one_pow, mul_one]
      _ = (a * bi) ^ 2 := by rw [mul_pow, mul_pow, ← mul_assoc, ← e2]

lemma card_clsRes_mul (j : ℕ) {w ε : 𝔬} (hε : IsUnit ε) :
    (clsRes v j (ε * w)).card = (clsRes v j w).card := by
  have hεq : IsUnit (Ideal.Quotient.mk (Ideal.span {πv ^ (j + 1)}) ε) := hε.map _
  have hinj : Function.Injective fun t : RQ v (j + 1) => Ideal.Quotient.mk (Ideal.span {πv ^ (j + 1)}) ε * t :=
    fun a b h => hεq.mul_left_cancel h
  have : clsRes v j (ε * w) = (clsRes v j w).image fun t => Ideal.Quotient.mk (Ideal.span {πv ^ (j + 1)}) ε * t := by
    ext t
    simp only [mem_clsRes, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨_, ⟨a, ha, rfl⟩, by rw [← map_mul]; congr 1; ring⟩
    · rintro ⟨t', ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, by rw [← map_mul]; congr 1; ring⟩
  rw [this, Finset.card_image_of_injective _ hinj]

/-- The count $r_{\pi^{j+1}}(\pi^jw)$ (as a real number). -/
noncomputable def rc (Q : QuadForm 𝔬 n) (j : ℕ) (w : 𝔬) : ℝ := (DVR.repCount Q πv (j + 1) (πv ^ j * w) : ℝ)

/-- **Hensel at level $\ge 1$** ($v \nmid 2\det H_Q$, $w, w'$ units): the primitive parts of $r_{\pi^{j+1}}(\pi^jw)$ and
$r_{\pi^{j+1}}(\pi^jw')$ agree for $j \ge 1$ (Hanke's Lemma 3.4, `DVR.repCountOf_nonZero_congr`), and the imprimitive parts are
$0$ ($j = 1$) or $q^nr_{\pi^{j-1}}(\pi^{j-2}w)$ ($j \ge 2$). Hence $r(\pi^jw) - r(\pi^jw') = q^n(r(\pi^{j-2}w) - r(\pi^{j-2}w'))$ for
$j \ge 2$ and $= 0$ for $j = 1$, and $r(\pi^jw) \ge q^nr(\pi^{j-2}w)$. -/
theorem rc_step (Q : QuadForm 𝔬 n) (h2 : ¬ πv ∣ 2) (hdet : ¬ πv ∣ Q.hessian.det) {w w' : 𝔬}
    (hw : IsUnit w) (hw' : IsUnit w') (j : ℕ) (hj : 1 ≤ j) :
    ∃ A : ℝ, 0 ≤ A ∧ rc v Q j w = A + (if 2 ≤ j then (qv) ^ n * rc v Q (j - 2) w else 0) ∧
      rc v Q j w' = A + (if 2 ≤ j then (qv) ^ n * rc v Q (j - 2) w' else 0) := by
  classical
  have hQ : Q.Nondegenerate := fun h => hdet (h ▸ dvd_zero _)
  have hπ := NF.irreducible_π v
  have h20 : (2 : 𝔬) ≠ 0 := two_ne_zero_O v
  have hcong : DVR.repCountOf Q πv (j + 1) (πv ^ j * w) (fun x => ¬ DVR.IsZeroType πv (j + 1) x) =
      DVR.repCountOf Q πv (j + 1) (πv ^ j * w') (fun x => ¬ DVR.IsZeroType πv (j + 1) x) := by
    refine DVR.repCountOf_nonZero_congr Q hQ πv hπ h20 0 (he_zero v h2) ?_ (j + 1)
    rw [depthLevel_eq_one v Q h2 hdet, pow_one]
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact ⟨πv ^ k * (w - w'), by ring⟩
  have hzero : ∀ u : 𝔬, IsUnit u → (DVR.repCountOf Q πv (j + 1) (πv ^ j * u) (DVR.IsZeroType πv (j + 1)) : ℝ) =
      if 2 ≤ j then (qv) ^ n * rc v Q (j - 2) u else 0 := by
    intro u hu
    split_ifs with hj2
    · rw [DVR.repCountZero_eq Q πv hπ (πv ^ j * u) (πv ^ (j - 2) * u)
        (by rw [← mul_assoc, ← pow_add]; congr 2; omega) (j + 1) (by omega), rc,
        show j + 1 - 2 = j - 2 + 1 by omega]
      push_cast; rfl
    · have hj1 : j = 1 := by omega
      subst hj1
      rw [DVR.repCountOf_zeroType_eq_zero Q πv (le_refl 2)]
      · simp
      · rw [pow_one]
        rintro ⟨c, hc⟩
        have hu' : u = πv * c := mul_left_cancel₀ hπ.ne_zero (by rw [hc]; ring)
        exact DVR.dvr_not_dvd_of_isUnit hπ hu ⟨c, hu'⟩
  refine ⟨(DVR.repCountOf Q πv (j + 1) (πv ^ j * w) (fun x => ¬ DVR.IsZeroType πv (j + 1) x) : ℝ),
    Nat.cast_nonneg _, ?_, ?_⟩
  · rw [rc, DVR.repCount_eq_zero_add_nonZero Q πv hπ, Nat.cast_add, hzero w hw]; ring
  · rw [rc, DVR.repCount_eq_zero_add_nonZero Q πv hπ, Nat.cast_add, hzero w' hw', hcong]; ring

lemma rc_nonneg (Q : QuadForm 𝔬 n) (j : ℕ) (w : 𝔬) : 0 ≤ rc v Q j w := Nat.cast_nonneg _

/-- At odd levels the two square classes have the same counts ($v \nmid 2\det H_Q$). -/
theorem rc_odd_eq (Q : QuadForm 𝔬 n) (h2 : ¬ πv ∣ 2) (hdet : ¬ πv ∣ Q.hessian.det) {w w' : 𝔬}
    (hw : IsUnit w) (hw' : IsUnit w') (k : ℕ) : rc v Q (2 * k + 1) w = rc v Q (2 * k + 1) w' := by
  induction k with
  | zero =>
    obtain ⟨A, -, h1, h1'⟩ := rc_step v Q h2 hdet hw hw' 1 le_rfl
    simp only [show ¬ (2 ≤ 1) by omega, ite_false] at h1 h1'
    rw [h1, h1']
  | succ k ih =>
    obtain ⟨A, -, h1, h1'⟩ := rc_step v Q h2 hdet hw hw' (2 * (k + 1) + 1) (by omega)
    simp only [show 2 ≤ 2 * (k + 1) + 1 by omega, ite_true, show 2 * (k + 1) + 1 - 2 = 2 * k + 1 by omega]
      at h1 h1'
    rw [h1, h1', ih]

/-- **Relative discrepancy of the two square classes is inherited from level $0$** ($v \nmid 2\det H_Q$): if
$|r(w) - r(w')| \le \theta(r(w) + r(w'))$ at level $0$ then the same holds at every level $j$. -/
theorem abs_rc_sub_le (Q : QuadForm 𝔬 n) (h2 : ¬ πv ∣ 2) (hdet : ¬ πv ∣ Q.hessian.det) {w w' : 𝔬}
    (hw : IsUnit w) (hw' : IsUnit w') {θ : ℝ} (hθ : 0 ≤ θ)
    (h0 : |rc v Q 0 w - rc v Q 0 w'| ≤ θ * (rc v Q 0 w + rc v Q 0 w')) (j : ℕ) :
    |rc v Q j w - rc v Q j w'| ≤ θ * (rc v Q j w + rc v Q j w') := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.lt_or_ge j 2 with hj | hj
    · interval_cases j
      · exact h0
      · rw [show (1 : ℕ) = 2 * 0 + 1 from rfl, rc_odd_eq v Q h2 hdet hw hw' 0, sub_self, abs_zero]
        exact mul_nonneg hθ (add_nonneg (rc_nonneg v Q _ _) (rc_nonneg v Q _ _))
    · obtain ⟨A, hA, h1, h1'⟩ := rc_step v Q h2 hdet hw hw' j (by omega)
      simp only [show 2 ≤ j from hj, ite_true] at h1 h1'
      have ih' := ih (j - 2) (by omega)
      have hq : (0 : ℝ) ≤ qv ^ n := by positivity
      rw [h1, h1']
      calc |A + qv ^ n * rc v Q (j - 2) w - (A + qv ^ n * rc v Q (j - 2) w')|
          = qv ^ n * |rc v Q (j - 2) w - rc v Q (j - 2) w'| := by
            rw [show A + qv ^ n * rc v Q (j - 2) w - (A + qv ^ n * rc v Q (j - 2) w') =
              qv ^ n * (rc v Q (j - 2) w - rc v Q (j - 2) w') by ring, abs_mul, abs_of_nonneg hq]
        _ ≤ qv ^ n * (θ * (rc v Q (j - 2) w + rc v Q (j - 2) w')) := mul_le_mul_of_nonneg_left ih' hq
        _ ≤ θ * (A + qv ^ n * rc v Q (j - 2) w + (A + qv ^ n * rc v Q (j - 2) w')) := by
            nlinarith [mul_nonneg hθ hA]

/-- **Level $0$: the two unit square classes** ($v \nmid 2\det H_Q$, $n \ge 3$, $w, w'$ units): by Table 1 (Hanke 2004, p. 363),
$r_\pi(u) = q^{n-1} - \varepsilon q^{n/2-1}$ ($n$ even, independent of $u$) or $q^{n-1} \pm q^{(n-1)/2}$ ($n$ odd), so
$|r_\pi(w) - r_\pi(w')| \le 2q^{-\lfloor(n-1)/2\rfloor}(r_\pi(w) + r_\pi(w'))$. -/
theorem abs_rc_zero_sub_le (Q : QuadForm 𝔬 n) (hn : 3 ≤ n) (h2 : ¬ πv ∣ 2) (hdet : ¬ πv ∣ Q.hessian.det)
    {w w' : 𝔬} (hw : IsUnit w) (hw' : IsUnit w') :
    |rc v Q 0 w - rc v Q 0 w'| ≤ 2 * (qv ^ ((n - 1) / 2))⁻¹ * (rc v Q 0 w + rc v Q 0 w') := by
  classical
  letI : Fintype (IsLocalRing.ResidueField 𝔬) := Fintype.ofFinite _
  have hπ := NF.irreducible_π v
  have hq3 : (3 : ℝ) ≤ qv := by exact_mod_cast DVR.three_le_q hπ h2
  have hT := DVR.card_mod_pi_of_unimodular Q πv hπ h2 hdet (by omega) w
    (DVR.dvr_not_dvd_of_isUnit hπ hw)
  have hT' := DVR.card_mod_pi_of_unimodular Q πv hπ h2 hdet (by omega) w'
    (DVR.dvr_not_dvd_of_isUnit hπ hw')
  have e0 : ∀ u : 𝔬, rc v Q 0 u = (DVR.repCount Q πv 1 u : ℝ) := fun u => by
    rw [rc, pow_zero, one_mul]
  rw [e0, e0]
  have hθ : 0 ≤ 2 * (qv ^ ((n - 1) / 2))⁻¹ := by positivity
  rcases Nat.even_or_odd n with he | ho
  · have h1 := (hT.1 he).2
    have h1' := (hT'.1 he).2
    have : (DVR.repCount Q πv 1 w : ℝ) = DVR.repCount Q πv 1 w' := by
      have : (DVR.repCount Q πv 1 w : ℤ) = DVR.repCount Q πv 1 w' := by rw [h1, h1']
      exact_mod_cast this
    rw [this, sub_self, abs_zero]
    exact mul_nonneg hθ (by positivity)
  · have h1 := (hT.2 ho).2
    have h1' := (hT'.2 ho).2
    have hc : ∀ u : 𝔬, (DVR.chiDiscT Q u : ℝ) = 1 ∨ (DVR.chiDiscT Q u : ℝ) = -1 ∨ (DVR.chiDiscT Q u : ℝ) = 0 := by
      intro u
      rcases quadraticChar_isQuadratic (IsLocalRing.ResidueField 𝔬)
        ((-1) ^ ((n - 1) / 2) * DVR.resGramDet Q * IsLocalRing.residue 𝔬 u) with h | h | h <;>
        simp [DVR.chiDiscT, h]
    have hr : ∀ u : 𝔬, (DVR.repCount Q πv 1 u : ℝ) = qv ^ (n - 1) + (DVR.chiDiscT Q u : ℝ) * qv ^ ((n - 1) / 2) →
        |(DVR.chiDiscT Q u : ℝ)| ≤ 1 := by
      intro u _
      rcases hc u with h | h | h <;> rw [h] <;> norm_num
    have e1 : (DVR.repCount Q πv 1 w : ℝ) = qv ^ (n - 1) + (DVR.chiDiscT Q w : ℝ) * qv ^ ((n - 1) / 2) := by
      exact_mod_cast h1
    have e1' : (DVR.repCount Q πv 1 w' : ℝ) = qv ^ (n - 1) + (DVR.chiDiscT Q w' : ℝ) * qv ^ ((n - 1) / 2) := by
      exact_mod_cast h1'
    have c1 := hr w e1
    have c1' := hr w' e1'
    set a : ℝ := qv ^ ((n - 1) / 2)
    have hA : qv ^ (n - 1) = a * a := by
      obtain ⟨k, rfl⟩ := ho
      simp only [a, show 2 * k + 1 - 1 = 2 * k by omega, show 2 * k / 2 = k by omega]
      rw [pow_mul', sq]
    have ha3 : 3 ≤ a := by
      have : 1 ≤ (n - 1) / 2 := by omega
      calc (3 : ℝ) ≤ qv := hq3
        _ = qv ^ 1 := (pow_one _).symm
        _ ≤ a := pow_le_pow_right₀ (by linarith) this
    rw [e1, e1', hA]
    set c := (DVR.chiDiscT Q w : ℝ)
    set c' := (DVR.chiDiscT Q w' : ℝ)
    have ha0 : 0 < a := by linarith
    rw [show a * a + c * a - (a * a + c' * a) = (c - c') * a by ring, abs_mul, abs_of_pos ha0]
    have hcc : |c - c'| ≤ 2 := by
      calc |c - c'| ≤ |c| + |c'| := abs_sub _ _
        _ ≤ 2 := by linarith
    obtain ⟨hc1, hc2⟩ := abs_le.mp c1
    obtain ⟨hc1', hc2'⟩ := abs_le.mp c1'
    rw [show 2 * a⁻¹ * (a * a + c * a + (a * a + c' * a)) = 2 * (2 * a + c + c') by field_simp; ring]
    nlinarith

end Classes

/-! ### The bridge from square classes of $F_v$ to the class sets -/

/-- **Square classes are open** in $F_v$ ($\rho \ne 0$): by the local square theorem, $t$ close to $t_0 = \rho y_0^2$ has
$t/t_0$ a square. -/
theorem isOpen_sqClass {ρ : Fv} (hρ : ρ ≠ 0) : IsOpen (SphericalZeta.sqClass ρ) := by
  rw [Metric.isOpen_iff]
  rintro t₀ ⟨y₀, hy₀, rfl⟩
  have ht0 : ρ * y₀ ^ 2 ≠ 0 := mul_ne_zero hρ (pow_ne_zero 2 hy₀)
  have h4 : (0 : ℝ) < ‖(4 : Fv)‖ := norm_pos_iff.mpr (by norm_num)
  refine ⟨‖(4 : Fv)‖ * ‖ρ * y₀ ^ 2‖, mul_pos h4 (norm_pos_iff.mpr ht0), fun t ht => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at ht
  have hq : ‖t / (ρ * y₀ ^ 2) - 1‖ < ‖(4 : Fv)‖ := by
    rw [show t / (ρ * y₀ ^ 2) - 1 = (t - ρ * y₀ ^ 2) / (ρ * y₀ ^ 2) by field_simp, norm_div,
      div_lt_iff₀ (norm_pos_iff.mpr ht0)]
    exact ht
  obtain ⟨z, hz⟩ := HN.isSquare_of_valued_sub_one_lt v _ ((Valued.toNormedField.norm_lt_iff).mp hq)
  have hz0 : z ≠ 0 := by
    rintro rfl
    have h0 : t / (ρ * y₀ ^ 2) = 0 := by rw [hz, mul_zero]
    rw [h0, zero_sub, norm_neg, norm_one] at hq
    have h41 : ‖(4 : Fv)‖ ≤ 1 := norm_le_one_of_valued v (valued_le_one_of_O v (4 : 𝔬))
    linarith
  refine ⟨y₀ * z, mul_ne_zero hy₀ hz0, ?_⟩
  have : t = (t / (ρ * y₀ ^ 2)) * (ρ * y₀ ^ 2) := by field_simp
  rw [this, hz]; ring

lemma isUnit_of_valued_eq_one {z : 𝔬} (hz : Valued.v (z : Fv) = 1) : IsUnit z := by
  have hz0 : (z : Fv) ≠ 0 := by intro h; rw [h, map_zero] at hz; exact zero_ne_one hz
  have hinv : Valued.v ((z : Fv)⁻¹) ≤ 1 := by rw [map_inv₀, hz, inv_one]
  refine ⟨⟨z, ⟨(z : Fv)⁻¹, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hinv⟩,
    Subtype.ext (mul_inv_cancel₀ hz0), Subtype.ext (inv_mul_cancel₀ hz0)⟩, rfl⟩

lemma valued_π_zpow (m : ℤ) : Valued.v ((πv : Fv) ^ m) = exp (-m) := by
  rw [map_zpow₀, NF.valued_π, ← exp_zsmul]; congr 1; simp

lemma exists_zpow_mul_unit {y : Fv} (hy : y ≠ 0) :
    ∃ m : ℤ, ∃ a : 𝔬, IsUnit a ∧ y = (πv : Fv) ^ m * (a : Fv) := by
  have hv : Valued.v y ≠ 0 := (Valued.v).ne_zero_iff.mpr hy
  set L := WithZero.log (Valued.v y)
  have hπ0 : (πv : Fv) ≠ 0 := by
    intro h; have := NF.valued_π v; rw [h, map_zero] at this; exact WithZero.zero_ne_coe this
  have hval : Valued.v (y * (πv : Fv) ^ L) = 1 := by
    rw [map_mul, valued_π_zpow, ← WithZero.exp_log hv, ← exp_add]; simp [L]
  refine ⟨-L, ⟨y * (πv : Fv) ^ L, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hval.le⟩,
    isUnit_of_valued_eq_one v hval, ?_⟩
  show y = (πv : Fv) ^ (-L) * (y * (πv : Fv) ^ L)
  rw [zpow_neg, ← mul_assoc, mul_comm _ y, mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hπ0), mul_one]

/-- **The bridge** ($v \nmid 2$, $j_0 \in \{0,1\}$, $w$ a unit): inside the level set $\{\operatorname{ord}Q = j\}$, the square class
$\pi^{j_0}wF_v^{\times2}$ is the class set $C_j(w)$ when $j \equiv j_0 \pmod 2$ and is empty otherwise. -/
theorem levelSet_inter_sqClass (Q : QuadForm 𝔬 n) (j₀ : ℕ) (hj₀ : j₀ < 2) {w : 𝔬} (hw : IsUnit w) (j : ℕ) :
    levelSet v Q j ∩ Q.evalIn Fv ⁻¹' SphericalZeta.sqClass ((πv ^ j₀ * w : 𝔬) : Fv) =
      if j % 2 = j₀ then clsSet v Q j w else ∅ := by
  have hπ0 : (πv : Fv) ≠ 0 := by
    intro h; have := NF.valued_π v; rw [h, map_zero] at this; exact WithZero.zero_ne_coe this
  have hw1 : Valued.v (w : Fv) = 1 := valued_eq_one_of_isUnit v hw
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨hx, y, hy0, hy⟩
    have hL : x ∈ latL v n := hx.1.1
    obtain ⟨h1, h2'⟩ := (mem_levelSet_iff v Q hL j).mp hx
    obtain ⟨u, hu, huU⟩ := DVR.dvr_exact (NF.irreducible_π v) h1 h2'
    obtain ⟨m, a, ha, rfl⟩ := exists_zpow_mul_unit v hy0
    have hu1 : Valued.v (u : Fv) = 1 := valued_eq_one_of_isUnit v huU
    have ha1 : Valued.v (a : Fv) = 1 := valued_eq_one_of_isUnit v ha
    have hQx : Q.evalIn Fv x = (πv : Fv) ^ j * (u : Fv) := by
      rw [evalIn_toO v Q x hL, hu]; push_cast; rfl
    have hy' : (πv : Fv) ^ j * (u : Fv) = (πv : Fv) ^ j₀ * (w : Fv) * ((πv : Fv) ^ m * (a : Fv)) ^ 2 := by
      rw [← hQx, hy]; push_cast; ring
    -- compare valuations
    have hval := congrArg Valued.v hy'
    simp only [map_mul, map_pow, NF.valued_π, hu1, hw1, ha1, valued_π_zpow, mul_one] at hval
    rw [← exp_nsmul, ← exp_nsmul, ← exp_nsmul, ← exp_add, exp_inj] at hval
    simp only [nsmul_eq_mul, mul_neg, mul_one] at hval
    push_cast at hval
    have hm : 0 ≤ m := by omega
    have hpar : j % 2 = j₀ := by omega
    simp only [hpar, ↓reduceIte]
    obtain ⟨k, hk⟩ : ∃ k : ℕ, m = (k : ℤ) := ⟨m.toNat, by omega⟩
    have hjk : j = j₀ + 2 * k := by omega
    refine ⟨hL, a, ha, ?_⟩
    rw [hy, hk, zpow_natCast, hjk]
    push_cast
    ring
  · intro hx
    split_ifs at hx with hpar
    · refine ⟨clsSet_subset_levelSet v Q j hw hx, ?_⟩
      obtain ⟨hL, a, ha, hQ⟩ := hx
      obtain ⟨k, hk⟩ : ∃ k, j = j₀ + 2 * k := ⟨j / 2, by omega⟩
      have ha0 : (a : Fv) ≠ 0 := by
        intro h; have := valued_eq_one_of_isUnit v ha; rw [h, map_zero] at this; exact zero_ne_one this
      refine ⟨(πv : Fv) ^ k * (a : Fv), mul_ne_zero (pow_ne_zero _ hπ0) ha0, ?_⟩
      rw [hQ, hk]; push_cast; ring
    · exact absurd hx (Set.notMem_empty x)

/-! ### Weil's bound $1 - q^{-m'} < e(\mathfrak p) < 1 + q^{-m'}$ (p. 107) -/

lemma measurableSet_clsSet (Q : QuadForm 𝔬 n) (h2 : ¬ πv ∣ 2) (j : ℕ) {w : 𝔬} (hw : IsUnit w) :
    MeasurableSet (clsSet v Q j w) := by
  rw [clsSet_eq_biUnion v Q h2 j hw]
  exact Finset.measurableSet_biUnion _ fun t _ => measurableSet_congSet v Q _ _

lemma measurableSet_preimage_sqClass (Q : QuadForm 𝔬 n) {ρ : Fv} (hρ : ρ ≠ 0) :
    MeasurableSet (Q.evalIn Fv ⁻¹' SphericalZeta.sqClass ρ) := by
  have hcont : Continuous fun x : Fin n → Fv => Q.evalIn Fv x := by
    unfold QuadForm.evalIn
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by
      split_ifs <;> fun_prop
  exact ((isOpen_sqClass v hρ).preimage hcont).measurableSet

/-- **The termwise bound** ($v \nmid 2\det H_Q$, $n \ge 3$, $w$ a unit, $j \equiv j_0$): with $d_j = \operatorname{vol}\{\operatorname{ord}Q = j\}$,
$|2\operatorname{vol}(C_j(w)) - d_j| \le 2q^{-\lfloor(n-1)/2\rfloor}d_j$. -/
theorem abs_two_clsSet_sub_le (Q : QuadForm 𝔬 n) (hn : 3 ≤ n) (h2 : ¬ πv ∣ 2)
    (hdet : ¬ πv ∣ Q.hessian.det) {w : 𝔬} (hw : IsUnit w) (j : ℕ) :
    |2 * (Measure.pi fun _ : Fin n => haarV v).real (clsSet v Q j w) - dSeq v Q j| ≤
      2 * (qv ^ ((n - 1) / 2))⁻¹ * dSeq v Q j := by
  obtain ⟨ε, hε, hεsq, hdich⟩ := exists_nonsq_unit v h2
  obtain ⟨hU, hD⟩ := levelSet_eq_union v Q h2 j hw hε hεsq hdich
  have hεw : IsUnit (ε * w) := hε.mul hw
  have hd : dSeq v Q j = (Measure.pi fun _ : Fin n => haarV v).real (clsSet v Q j w) +
      (Measure.pi fun _ : Fin n => haarV v).real (clsSet v Q j (ε * w)) := by
    have hf : ∀ u, (Measure.pi fun _ : Fin n => haarV v) (clsSet v Q j u) ≠ ⊤ := fun u =>
      measure_ne_top_of_subset (fun x hx => hx.1) (measure_latL_haar_ne_top v)
    rw [dSeq_eq_real_levelSet, hU, measureReal_union hD (measurableSet_clsSet v Q h2 j hεw) (hf w) (hf _)]
  have hθ := abs_rc_sub_le v Q h2 hdet hw hεw (by positivity) (abs_rc_zero_sub_le v Q hn h2 hdet hw hεw) j
  set c : ℝ := ((clsRes v j w).card : ℝ) * ((qv ^ (j + 1))⁻¹) ^ n with hcdef
  have hc : 0 ≤ c := by positivity
  have e1 : (Measure.pi fun _ : Fin n => haarV v).real (clsSet v Q j w) = c * rc v Q j w := by
    rw [real_clsSet v Q h2 j hw, rc, hcdef]; ring
  have e2 : (Measure.pi fun _ : Fin n => haarV v).real (clsSet v Q j (ε * w)) = c * rc v Q j (ε * w) := by
    rw [real_clsSet v Q h2 j hεw, rc, card_clsRes_mul v j hε, hcdef]; ring
  rw [hd, e1, e2]
  calc |2 * (c * rc v Q j w) - (c * rc v Q j w + c * rc v Q j (ε * w))|
      = c * |rc v Q j w - rc v Q j (ε * w)| := by
        rw [show 2 * (c * rc v Q j w) - (c * rc v Q j w + c * rc v Q j (ε * w)) =
          c * (rc v Q j w - rc v Q j (ε * w)) by ring, abs_mul, abs_of_nonneg hc]
    _ ≤ c * (2 * (qv ^ ((n - 1) / 2))⁻¹ * (rc v Q j w + rc v Q j (ε * w))) :=
        mul_le_mul_of_nonneg_left hθ hc
    _ = _ := by ring

/-- **The parity series** $P_{j_0}(Y) = \sum_{j\equiv j_0 \bmod 2}Y^jd_j$. With $Y = q^{-s}$, $(1-q^{-1})^{-1}P_{j_0}$ is Weil's
$H_\mathfrak p$-restricted integral $\int_{F(x)\in\pi^{j_0}k_\mathfrak p^{\times2}U_\mathfrak p}|F|^s\Phi_\mathfrak p\,d'x$ (p. 106, $H_\mathfrak p = k_\mathfrak p^{\times2}U_\mathfrak p$). -/
def parSeries (Q : QuadForm 𝔬 n) (j₀ : ℕ) (Y : ℝ) : ℝ := ∑' j, if j % 2 = j₀ then Y ^ j * dSeq v Q j else 0

lemma hasSum_parSeries (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) (j₀ : ℕ) {Y : ℝ}
    (hY : |Y| ≤ 1) : HasSum (fun j => if j % 2 = j₀ then Y ^ j * dSeq v Q j else 0) (parSeries v Q j₀ Y) := by
  refine (Summable.of_norm_bounded (summable_dSeq v Q hQ hn) fun j => ?_).hasSum
  split_ifs
  · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (dSeq_nonneg v Q j)]
    exact mul_le_of_le_one_left (dSeq_nonneg v Q j) (pow_le_one₀ (abs_nonneg _) hY)
  · simp [dSeq_nonneg v Q j]

lemma parSeries_nonneg (Q : QuadForm 𝔬 n) (j₀ : ℕ) {Y : ℝ} (hY : 0 ≤ Y) : 0 ≤ parSeries v Q j₀ Y :=
  tsum_nonneg fun j => by split_ifs <;> [exact mul_nonneg (pow_nonneg hY _) (dSeq_nonneg v Q j); exact le_rfl]

/-- **Weil's bound $1 - q^{-m'} < e(\mathfrak p) < 1 + q^{-m'}$ in additive form** (Weil 1982, §4.5, p. 107; Lemma 4.5.2, p. 103):
at $v \nmid 2\det H_Q$, $n \ge 3$, $\rho = \pi^{j_0}w$ ($j_0 \in \{0,1\}$, $w$ a unit), $s \ge 0$, $X = q^{-s}$,
$$\Big|2\int_{x\in L_v,\ Q(x)\in\rho F_v^{\times2}}|Q(x)|^s\,dx - P_{j_0}(X)\Big| \le 2q^{-\lfloor(n-1)/2\rfloor}P_{j_0}(X).$$
Since $T(\rho)_v \to \{Q \in \rho F_v^{\times2}\}$ is two-to-one, the left integral is Weil's $\int_{T(\rho)}$, and $P_{j_0}(X)$ is his
$\int_{F(x)\in H_\mathfrak p\rho}$: the ratio (7) is $e(\mathfrak p) = 1 + O(q^{-\lfloor(n-1)/2\rfloor})$, and $= 1$ for $j_0 = 1$ or $n$ even. -/
@[kb "weil1982" "§4.5, (7) and the bound 1 - q^{-m'} < θ(p) < 1 + q^{-m'}, p. 107; Lemma 4.5.2, p. 103"]
theorem abs_two_sphInt_sub_le (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (h2 : ¬ πv ∣ 2)
    (hdet : ¬ πv ∣ Q.hessian.det) (j₀ : ℕ) (hj₀ : j₀ < 2) {w : 𝔬} (hw : IsUnit w) {s : ℝ} (hs : 0 ≤ s) :
    |2 * ∫ x in latL v n ∩ Q.evalIn Fv ⁻¹' SphericalZeta.sqClass ((πv ^ j₀ * w : 𝔬) : Fv),
        ‖Q.evalIn Fv x‖ ^ s ∂(Measure.pi fun _ : Fin n => haarV v) - parSeries v Q j₀ ((DVR.q 𝔬 : ℝ) ^ (-s))| ≤
      2 * (qv ^ ((n - 1) / 2))⁻¹ * parSeries v Q j₀ ((DVR.q 𝔬 : ℝ) ^ (-s)) := by
  set X : ℝ := (DVR.q 𝔬 : ℝ) ^ (-s)
  set θ : ℝ := 2 * (qv ^ ((n - 1) / 2))⁻¹
  have hq1 : (1 : ℝ) < qv := by exact_mod_cast (q_ge_two v)
  have hX0 : 0 < X := Real.rpow_pos_of_pos (by linarith) _
  have hX1 : X ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1.le (by linarith)
  have hXa : |X| ≤ 1 := by rw [abs_of_pos hX0]; exact hX1
  have hθ : 0 ≤ θ := by positivity
  have hρ : ((πv ^ j₀ * w : 𝔬) : Fv) ≠ 0 := by
    have : πv ^ j₀ * w ≠ 0 := mul_ne_zero (pow_ne_zero _ (NF.irreducible_π v).ne_zero) hw.ne_zero
    exact_mod_cast this
  have hA := measurableSet_preimage_sqClass v Q hρ
  have H1 := hasSum_setIntegral_level v (haarV v) Q hQ (by omega) hA hs
  simp_rw [levelSet_inter_sqClass v Q j₀ hj₀ hw] at H1
  have H2 := hasSum_parSeries v Q hQ (by omega) j₀ hXa
  have H := (H1.mul_left 2).sub H2
  set g : ℕ → ℝ := fun j => θ * (if j % 2 = j₀ then X ^ j * dSeq v Q j else 0)
  have Hg : HasSum g (θ * parSeries v Q j₀ X) := H2.mul_left θ
  have hb : ∀ j, |2 * (X ^ j * (Measure.pi fun _ : Fin n => haarV v).real
      (if j % 2 = j₀ then clsSet v Q j w else ∅)) - (if j % 2 = j₀ then X ^ j * dSeq v Q j else 0)| ≤ g j := by
    intro j
    simp only [g]
    split_ifs
    · rw [show 2 * (X ^ j * (Measure.pi fun _ : Fin n => haarV v).real (clsSet v Q j w)) - X ^ j * dSeq v Q j =
        X ^ j * (2 * (Measure.pi fun _ : Fin n => haarV v).real (clsSet v Q j w) - dSeq v Q j) by ring,
        abs_mul, abs_of_nonneg (pow_nonneg hX0.le _)]
      calc X ^ j * |2 * (Measure.pi fun _ : Fin n => haarV v).real (clsSet v Q j w) - dSeq v Q j|
          ≤ X ^ j * (θ * dSeq v Q j) :=
            mul_le_mul_of_nonneg_left (abs_two_clsSet_sub_le v Q hn h2 hdet hw j) (pow_nonneg hX0.le _)
        _ = θ * (X ^ j * dSeq v Q j) := by ring
    · simp
  rw [abs_le]
  constructor
  · have := hasSum_le (fun j => (neg_le_of_abs_le (hb j))) Hg.neg H
    linarith
  · exact hasSum_le (fun j => le_of_abs_le (hb j)) H Hg

/-! ### Parity series: identities and bounds at good places -/

lemma parSeries_add (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) {Y : ℝ} (hY : |Y| ≤ 1) :
    parSeries v Q 0 Y + parSeries v Q 1 Y = genSeries v Q Y := by
  have h := (hasSum_parSeries v Q hQ hn 0 hY).add (hasSum_parSeries v Q hQ hn 1 hY)
  refine (h.unique ?_)
  have hs : HasSum (fun j => Y ^ j * dSeq v Q j) (genSeries v Q Y) := (summable_pow_mul_dSeq v Q hQ hn hY).hasSum
  convert hs using 1
  funext j
  rcases Nat.mod_two_eq_zero_or_one j with h0 | h1
  · simp [h0]
  · simp [h1]

lemma parSeries_sub (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) {Y : ℝ} (hY : |Y| ≤ 1) :
    parSeries v Q 0 Y - parSeries v Q 1 Y = genSeries v Q (-Y) := by
  have hY' : |-Y| ≤ 1 := by rwa [abs_neg]
  have h := (hasSum_parSeries v Q hQ hn 0 hY).sub (hasSum_parSeries v Q hQ hn 1 hY)
  refine (h.unique ?_)
  have hs : HasSum (fun j => (-Y) ^ j * dSeq v Q j) (genSeries v Q (-Y)) :=
    (summable_pow_mul_dSeq v Q hQ hn hY').hasSum
  convert hs using 1
  funext j
  rcases Nat.mod_two_eq_zero_or_one j with h0 | h1
  · have he : Even j := Nat.even_iff.mpr h0
    simp [h0, he.neg_pow]
  · have ho : Odd j := Nat.odd_iff.mpr h1
    simp [h1, ho.neg_pow]

/-- **The twisted combination** $P_0 + cP_1 = G(cY)$ for $c = \pm1$. -/
lemma parSeries_add_mul (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) {Y : ℝ} (hY : |Y| ≤ 1)
    {c : ℝ} (hc : c = 1 ∨ c = -1) :
    parSeries v Q 0 Y + c * parSeries v Q 1 Y = genSeries v Q (c * Y) := by
  rcases hc with rfl | rfl
  · rw [one_mul, one_mul, parSeries_add v Q hQ hn hY]
  · rw [neg_one_mul, neg_one_mul, ← sub_eq_add_neg, parSeries_sub v Q hQ hn hY]

lemma parSeries_nonneg' (Q : QuadForm 𝔬 n) (j₀ : ℕ) {Y : ℝ} (hY : 0 ≤ Y) : 0 ≤ parSeries v Q j₀ Y :=
  parSeries_nonneg v Q j₀ hY

lemma dSeq_zero (Q : QuadForm 𝔬 n) : dSeq v Q 0 = 1 - aSeq v Q 1 := by
  rw [dSeq, aSeq_zero]

lemma parSeries_zero_ge (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) {Y : ℝ} (hY0 : 0 ≤ Y)
    (hY : Y ≤ 1) : dSeq v Q 0 ≤ parSeries v Q 0 Y := by
  have hYa : |Y| ≤ 1 := by rw [abs_of_nonneg hY0]; exact hY
  have h := hasSum_parSeries v Q hQ hn 0 hYa
  have := sum_le_hasSum (Finset.range 1) (fun j _ => by
    split_ifs <;> [exact mul_nonneg (pow_nonneg hY0 _) (dSeq_nonneg v Q j); exact le_rfl]) h
  simpa using this

/-- $P_1(Y) \le Y\,a_1$ for $0 \le Y \le 1$ ($\sum_{j\ge1}d_j = a_1$). -/
lemma parSeries_one_le (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) {Y : ℝ} (hY0 : 0 ≤ Y)
    (hY : Y ≤ 1) : parSeries v Q 1 Y ≤ Y * aSeq v Q 1 := by
  have hYa : |Y| ≤ 1 := by rw [abs_of_nonneg hY0]; exact hY
  have h := hasSum_parSeries v Q hQ hn 1 hYa
  -- Σ_{j ≥ 1} d_j = a_1
  have hd := hasSum_dSeq v Q hQ hn
  have hd1 : HasSum (fun j => dSeq v Q (j + 1)) (aSeq v Q 1) := by
    have := (hasSum_nat_add_iff' 1).mpr hd
    simpa [dSeq_zero] using this
  have hb : HasSum (fun j => Y * (if j = 0 then 0 else dSeq v Q j)) (Y * aSeq v Q 1) := by
    refine HasSum.mul_left Y ?_
    rw [← hasSum_nat_add_iff' 1]
    simpa using hd1
  refine hasSum_le (fun j => ?_) h hb
  split_ifs with h1 h0
  · subst h0; simp at h1
  · rw [mul_comm Y]
    exact mul_le_mul_of_nonneg_right (by
      calc Y ^ j ≤ Y ^ 1 := pow_le_pow_of_le_one hY0 hY (by omega)
        _ = Y := pow_one Y) (dSeq_nonneg v Q j) |>.trans (by rw [mul_comm])
  · simp
  · exact mul_nonneg hY0 (dSeq_nonneg v Q j)

/-- Real-algebra lemma for the even-parity factor: if $|R_1 - 1|, |R_2 - 1| \le \delta$, $0 \le \rho \le 1/3$, $0 \le Y \le 1$, then
$\big|\tfrac12\big(\tfrac{R_1}{1-\rho Y} + \tfrac{R_2}{1+\rho Y}\big) - 1\big| \le 2\delta + 2\rho^2$. -/
lemma abs_avg_sub_one_le {R₁ R₂ δ ρ Y : ℝ} (h1 : |R₁ - 1| ≤ δ) (h2 : |R₂ - 1| ≤ δ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 3)
    (hY0 : 0 ≤ Y) (hY : Y ≤ 1) :
    |(R₁ / (1 - ρ * Y) + R₂ / (1 + ρ * Y)) / 2 - 1| ≤ 2 * δ + 2 * ρ ^ 2 := by
  have hρY : ρ * Y ≤ 1 / 3 := by nlinarith
  have hρY0 : 0 ≤ ρ * Y := mul_nonneg hρ0 hY0
  have hd1 : 0 < 1 - ρ * Y := by linarith
  have hd2 : 0 < 1 + ρ * Y := by linarith
  have e : (R₁ / (1 - ρ * Y) + R₂ / (1 + ρ * Y)) / 2 - 1 =
      ((R₁ - 1) * (1 + ρ * Y) + (R₂ - 1) * (1 - ρ * Y) + 2 * (ρ * Y) ^ 2) / (2 * ((1 - ρ * Y) * (1 + ρ * Y))) := by
    field_simp; ring
  have hD : 0 < 2 * ((1 - ρ * Y) * (1 + ρ * Y)) := by have := mul_pos hd1 hd2; linarith
  rw [e, abs_div, abs_of_pos hD, div_le_iff₀ hD]
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) h1
  have t1 : |(R₁ - 1) * (1 + ρ * Y)| ≤ δ * (1 + ρ * Y) := by
    rw [abs_mul, abs_of_pos hd2]; exact mul_le_mul_of_nonneg_right h1 hd2.le
  have t2 : |(R₂ - 1) * (1 - ρ * Y)| ≤ δ * (1 - ρ * Y) := by
    rw [abs_mul, abs_of_pos hd1]; exact mul_le_mul_of_nonneg_right h2 hd1.le
  have t3 : |2 * (ρ * Y) ^ 2| ≤ 2 * ρ ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    have : (ρ * Y) ^ 2 ≤ ρ ^ 2 := by
      rw [mul_pow]; exact mul_le_of_le_one_right (sq_nonneg ρ) (by nlinarith)
    linarith
  calc |(R₁ - 1) * (1 + ρ * Y) + (R₂ - 1) * (1 - ρ * Y) + 2 * (ρ * Y) ^ 2|
      ≤ |(R₁ - 1) * (1 + ρ * Y)| + |(R₂ - 1) * (1 - ρ * Y)| + |2 * (ρ * Y) ^ 2| := abs_add_three _ _ _
    _ ≤ δ * (1 + ρ * Y) + δ * (1 - ρ * Y) + 2 * ρ ^ 2 := by linarith
    _ ≤ (2 * δ + 2 * ρ ^ 2) * (2 * ((1 - ρ * Y) * (1 + ρ * Y))) := by
        have : (1 - ρ * Y) * (1 + ρ * Y) ≥ 8 / 9 := by nlinarith
        nlinarith

/-- **The even-parity factor at a good place** ($n \ge 4$, $0 \le Y \le 1$):
$|P_0(Y)/(1 - q^{-1}) - 1| \le 10\,q^{-2}$. -/
theorem abs_parSeries_zero_sub_one_le (Q : QuadForm 𝔬 n) (hn : 4 ≤ n) (h2 : ¬ πv ∣ 2)
    (hdet : ¬ πv ∣ Q.hessian.det) {Y : ℝ} (hY0 : 0 ≤ Y) (hY : Y ≤ 1) :
    |parSeries v Q 0 Y / (1 - qv⁻¹) - 1| ≤ 10 * (qv ^ 2)⁻¹ := by
  have hQ : Q.Nondegenerate := fun h => hdet (h ▸ dvd_zero _)
  have hq3 : (3 : ℝ) ≤ qv := by
    haveI : Fintype (IsLocalRing.ResidueField 𝔬) := Fintype.ofFinite _
    exact_mod_cast DVR.three_le_q (NF.irreducible_π v) h2
  have hq0 : (0 : ℝ) < qv := by linarith
  have hYa : |Y| ≤ 1 := by rw [abs_of_nonneg hY0]; exact hY
  have hYa' : |-Y| ≤ 1 := by rwa [abs_neg]
  have hρ : qv⁻¹ ≤ 1 / 3 := by rw [inv_le_comm₀ hq0 (by norm_num)]; linarith
  have h1q : 1 - qv⁻¹ ≠ 0 := by have := inv_pos.mpr hq0; linarith
  have hpow : (qv ^ (n / 2))⁻¹ ≤ (qv ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith) (by omega))
  have hR1 : |genRatio v Q Y - 1| ≤ 4 * (qv ^ 2)⁻¹ :=
    (abs_genRatio_sub_one_le v Q (by omega) h2 hdet hYa).trans (by linarith)
  have hR2 : |genRatio v Q (-Y) - 1| ≤ 4 * (qv ^ 2)⁻¹ :=
    (abs_genRatio_sub_one_le v Q (by omega) h2 hdet hYa').trans (by linarith)
  have hG : ∀ Z : ℝ, |Z| ≤ 1 → genSeries v Q Z = (1 - qv⁻¹) * genRatio v Q Z / (1 - qv⁻¹ * Z) := by
    intro Z hZ
    have hZ' : 1 - qv⁻¹ * Z ≠ 0 := by
      have := abs_le_one_aux (inv_pos.mpr hq0).le (by linarith : qv⁻¹ < 1) hZ
      intro h; have := (abs_lt.mp this).2; linarith
    have hq0' : qv ≠ 0 := hq0.ne'
    have hq1' : qv - 1 ≠ 0 := by linarith
    have hqZ : qv - Z ≠ 0 := by have := (abs_le.mp hZ).2; linarith
    rw [genRatio]; field_simp
  have hP0 : parSeries v Q 0 Y / (1 - qv⁻¹) =
      (genRatio v Q Y / (1 - qv⁻¹ * Y) + genRatio v Q (-Y) / (1 + qv⁻¹ * Y)) / 2 := by
    have h1 := parSeries_add v Q hQ (by omega) hYa
    have h2' := parSeries_sub v Q hQ (by omega) hYa
    have : parSeries v Q 0 Y = (genSeries v Q Y + genSeries v Q (-Y)) / 2 := by linarith
    rw [this, hG Y hYa, hG (-Y) hYa', show 1 - qv⁻¹ * -Y = 1 + qv⁻¹ * Y by ring]
    have hq0' : qv ≠ 0 := hq0.ne'
    have hm : 1 - qv⁻¹ * Y ≠ 0 := by
      have : qv⁻¹ * Y ≤ 1 / 3 := by nlinarith [inv_pos.mpr hq0]
      linarith
    have hp : 1 + qv⁻¹ * Y ≠ 0 := by
      have : 0 ≤ qv⁻¹ * Y := mul_nonneg (inv_pos.mpr hq0).le hY0
      linarith
    have hq1' : qv - 1 ≠ 0 := by linarith
    have hqY : qv - Y ≠ 0 := by linarith
    have hqY' : qv + Y ≠ 0 := by linarith
    field_simp
  rw [hP0]
  have := abs_avg_sub_one_le hR1 hR2 (inv_pos.mpr hq0).le hρ hY0 hY
  calc _ ≤ 2 * (4 * (qv ^ 2)⁻¹) + 2 * (qv⁻¹) ^ 2 := this
    _ = 10 * (qv ^ 2)⁻¹ := by rw [inv_pow]; ring

lemma aSeq_one_le (Q : QuadForm 𝔬 n) (hn : 2 ≤ n) (h2 : ¬ πv ∣ 2) (hdet : ¬ πv ∣ Q.hessian.det) :
    (aSeq v Q 1 : ℝ) ≤ 2 * qv⁻¹ := by
  classical
  haveI : Fintype (IsLocalRing.ResidueField 𝔬) := Fintype.ofFinite _
  have hq1 : (1 : ℝ) < qv := by exact_mod_cast (q_ge_two v)
  have hq0 : (0 : ℝ) < qv := by linarith
  rw [aSeq_one_good]; push_cast
  have hT := DVR.card_mod_pi_of_unimodular Q πv (NF.irreducible_π v) h2 hdet (by omega) 1
    (fun h => (NF.irreducible_π v).not_isUnit (isUnit_of_dvd_one h))
  rw [div_le_iff₀ (by positivity)]
  have hqn : qv ^ n = qv * qv ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  rcases Nat.even_or_odd n with he | ho
  · have h := (hT.1 he).1
    have hε := DVR.chiDisc_sq (NF.irreducible_π v) h2 hdet
    have hN : (N1 v Q : ℝ) = qv ^ (n - 1) + (DVR.chiDisc Q : ℝ) * (qv - 1) * qv ^ (n / 2 - 1) := by
      exact_mod_cast h
    have hεle : (DVR.chiDisc Q : ℝ) ≤ 1 := by nlinarith [sq_nonneg ((DVR.chiDisc Q : ℝ) - 1)]
    have hpow : qv ^ (n / 2 - 1) * qv ≤ qv ^ (n - 1) := by
      rw [← pow_succ]; exact pow_le_pow_right₀ hq1.le (by omega)
    rw [hN, hqn]
    have : (DVR.chiDisc Q : ℝ) * (qv - 1) * qv ^ (n / 2 - 1) ≤ (qv - 1) * qv ^ (n / 2 - 1) := by
      have : 0 ≤ (qv - 1) * qv ^ (n / 2 - 1) := by positivity
      nlinarith
    have h3 : (qv - 1) * qv ^ (n / 2 - 1) ≤ qv ^ (n - 1) := by nlinarith [pow_pos hq0 (n / 2 - 1)]
    field_simp
    nlinarith
  · have h := (hT.2 ho).1
    have hN : (N1 v Q : ℝ) = qv ^ (n - 1) := by exact_mod_cast h
    rw [hN, hqn]
    field_simp
    nlinarith [pow_pos hq0 (n - 1)]

/-- **The odd-parity factor is small** at a good place ($n \ge 2$, $0 \le Y \le 1$): $P_1(Y) \le 2q^{-1}Y$. -/
theorem parSeries_one_le_good (Q : QuadForm 𝔬 n) (hn : 2 ≤ n) (h2 : ¬ πv ∣ 2)
    (hdet : ¬ πv ∣ Q.hessian.det) {Y : ℝ} (hY0 : 0 ≤ Y) (hY : Y ≤ 1) :
    parSeries v Q 1 Y ≤ 2 * qv⁻¹ * Y := by
  have hQ : Q.Nondegenerate := fun h => hdet (h ▸ dvd_zero _)
  calc parSeries v Q 1 Y ≤ Y * aSeq v Q 1 := parSeries_one_le v Q hQ (by omega) hY0 hY
    _ ≤ Y * (2 * qv⁻¹) := mul_le_mul_of_nonneg_left (aSeq_one_le v Q hn h2 hdet) hY0
    _ = 2 * qv⁻¹ * Y := by ring

/-- $P_0(Y) \ge d_0 \ge 1/3$ at a good place ($n \ge 2$). -/
theorem parSeries_zero_ge_third (Q : QuadForm 𝔬 n) (hn : 2 ≤ n) (h2 : ¬ πv ∣ 2)
    (hdet : ¬ πv ∣ Q.hessian.det) {Y : ℝ} (hY0 : 0 ≤ Y) (hY : Y ≤ 1) : 1 / 3 ≤ parSeries v Q 0 Y := by
  have hQ : Q.Nondegenerate := fun h => hdet (h ▸ dvd_zero _)
  have hq3 : (3 : ℝ) ≤ qv := by
    haveI : Fintype (IsLocalRing.ResidueField 𝔬) := Fintype.ofFinite _
    exact_mod_cast DVR.three_le_q (NF.irreducible_π v) h2
  have ha := aSeq_one_le v Q hn h2 hdet
  have : 2 * qv⁻¹ ≤ 2 / 3 := by
    rw [mul_comm, ← div_eq_inv_mul, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  calc (1 : ℝ) / 3 ≤ dSeq v Q 0 := by rw [dSeq_zero]; linarith
    _ ≤ _ := parSeries_zero_ge v Q hQ (by omega) hY0 hY

end QuadFormsKB.LocalZeta
