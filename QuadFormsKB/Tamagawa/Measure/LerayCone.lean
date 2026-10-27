import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.GlobalZeta

/-!
# The cone Euler product at the finite places

The null cone $C^\circ_v = \{Q = 0\} \smallsetminus \{0\}$ of $V_v = F_v^n$ carries the Leray measure $dx/dQ$ (homogeneous of
degree $n - 2$). Its volume on the **primitive** vectors $L_v \smallsetminus \pi L_v$ of $L_v = \mathcal O_v^n$ is the
`coneFactor`
$$\gamma_v(Q) = \lim_{j\to\infty} q_v^{\,j}\,c_j(Q_v),\qquad c_j = r^*_{\mathfrak p^j}(0)/q^{jn}$$
(the `cSeq`: the thickened volume
$\mathrm{vol}\{x \in L_v \smallsetminus \pi L_v : Q(x) \in \mathfrak p^j\}/\mathrm{vol}(\mathfrak p^j)$,
standard Haar measure). The lemma `cSeq_geom` makes the sequence eventually constant, so the limit exists at **every**
finite place (dyadic included). At a good place $v \nmid 2\det H_Q$,
$$\gamma_v = (N_1 - 1)\,q^{1-n},\qquad N_1 = \#\{x \in \mathbb F_q^n : \bar Q(x) = 0\},$$
which is $1 - q^{1-n}$ for $n$ odd and $1 - q^{1-n} + \varepsilon(q-1)q^{-n/2}$ for $n$ even
(this is $1 - q^{1-n} + \eta(q^{1-n/2} - q^{-n/2})$, now proved).

**Headline** (`multipliable_coneFactor`): for $n \ge 5$ the Euler product $\prod_v\gamma_v(Q)$ converges absolutely; the bound
$|\gamma_v - 1| \le 2N\mathfrak p_v^{-2}$ holds at every good place. The threshold is sharp: $n = 4$ gives
$|\gamma_v - 1| \approx q^{-1}$ for $\varepsilon = \pm 1$ (compare $\zeta_F(1)$). The full cone volume of $L_v$ is
$\gamma_v/(1 - q_v^{2-n})$ (homogeneity of degree $n - 2$); that series converges too (`multipliable_coneTotal`).
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology
open QuadFormsKB.LocalDensity QuadFormsKB.LocalZeta QuadFormsKB.GlobalZeta QuadFormsKB.NFEuler

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.LerayCone

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

local notation "qv" v => ((DVR.q (HeightOneSpectrum.adicCompletionIntegers F v) : ℕ) : ℝ)

/-- **The primitive cone factor** $\gamma_v(Q) = \lim_j q_v^j c_j(Q_v)$: the Leray volume of the primitive vectors of $L_v$ on the
null cone (standard Haar measure, $\mathrm{vol}(\mathcal O_v) = 1$). -/
def coneFactor (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  limUnder atTop fun j : ℕ => (cSeq v (NF.Qp v Q) j : ℝ) * (qv v) ^ j

/-- The sequence $q^jc_j$ is eventually constant (`cSeq_geom`), so it converges. -/
theorem exists_tendsto_coneSeq (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ c : ℝ, (∀ᶠ j : ℕ in atTop, (cSeq v (NF.Qp v Q) j : ℝ) * (qv v) ^ j = c) := by
  obtain ⟨e, he⟩ := DVR.exists_pow_dvd_not_dvd (NF.π v) (NF.irreducible_π v) (two_ne_zero_O v)
  have hQv := NF.nondegenerate_Qp v hQ
  set K := DVR.depthLevel (NF.Qp v Q) (NF.π v) e
  have hq0 : (0 : ℝ) < qv v := by exact_mod_cast q_pos v
  refine ⟨(cSeq v (NF.Qp v Q) K : ℝ) * (qv v) ^ K, Filter.eventually_atTop.mpr ⟨K, fun j hj => ?_⟩⟩
  have h := cSeq_geom v (NF.Qp v Q) hQv hn e he j hj
  have h' : (cSeq v (NF.Qp v Q) j : ℝ) =
      (cSeq v (NF.Qp v Q) K : ℝ) * (qv v) ^ K * ((qv v)⁻¹) ^ j := by
    rw [h]; push_cast; rfl
  rw [h', mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hq0.ne'), mul_one]

theorem tendsto_coneFactor (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n)
    (v : HeightOneSpectrum (𝓞 F)) :
    Tendsto (fun j : ℕ => (cSeq v (NF.Qp v Q) j : ℝ) * (qv v) ^ j) atTop (𝓝 (coneFactor Q v)) := by
  obtain ⟨c, hc⟩ := exists_tendsto_coneSeq Q hQ hn v
  have : Tendsto (fun j : ℕ => (cSeq v (NF.Qp v Q) j : ℝ) * (qv v) ^ j) atTop (𝓝 c) :=
    tendsto_const_nhds.congr' (hc.mono fun j hj => hj.symm)
  rw [coneFactor, this.limUnder_eq]
  exact this

theorem eventually_coneSeq_eq (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∀ᶠ j : ℕ in atTop, (cSeq v (NF.Qp v Q) j : ℝ) * (qv v) ^ j = coneFactor Q v := by
  obtain ⟨c, hc⟩ := exists_tendsto_coneSeq Q hQ hn v
  have h1 : Tendsto (fun j : ℕ => (cSeq v (NF.Qp v Q) j : ℝ) * (qv v) ^ j) atTop (𝓝 c) :=
    tendsto_const_nhds.congr' (hc.mono fun j hj => hj.symm)
  have : c = coneFactor Q v := tendsto_nhds_unique h1 (tendsto_coneFactor Q hQ hn v)
  exact hc.mono fun j hj => hj.trans this

theorem coneFactor_nonneg (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n)
    (v : HeightOneSpectrum (𝓞 F)) : 0 ≤ coneFactor Q v := by
  obtain ⟨j, hj⟩ := (eventually_coneSeq_eq Q hQ hn v).exists
  rw [← hj]
  have hq0 : (0 : ℝ) < qv v := by exact_mod_cast q_pos v
  have : (0 : ℝ) ≤ (cSeq v (NF.Qp v Q) j : ℝ) := by
    unfold cSeq; push_cast; positivity
  positivity

/-- **The good-place value** $\gamma_v = (N_1 - 1)q^{1-n}$. -/
theorem coneFactor_good (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n)
    {v : HeightOneSpectrum (𝓞 F)} (hv : IsGoodPlace Q v) :
    coneFactor Q v = ((N1 v (NF.Qp v Q) : ℝ) - 1) / (qv v) ^ (n - 1) := by
  obtain ⟨h2, hd⟩ := not_dvd_of_isGoodPlace hv
  have hQv := NF.nondegenerate_Qp v hQ
  have hq0 : (0 : ℝ) < qv v := by exact_mod_cast q_pos v
  have hev : ∀ᶠ j : ℕ in atTop, (cSeq v (NF.Qp v Q) j : ℝ) * (qv v) ^ j =
      ((N1 v (NF.Qp v Q) : ℝ) - 1) / (qv v) ^ (n - 1) := by
    refine Filter.eventually_atTop.mpr ⟨1, fun j hj => ?_⟩
    rw [cSeq_good v (NF.Qp v Q) hQv hn h2 hd j hj]
    push_cast
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, inv_pow, pow_succ]
    field_simp
  have hlim : Tendsto (fun j : ℕ => (cSeq v (NF.Qp v Q) j : ℝ) * (qv v) ^ j) atTop
      (𝓝 (((N1 v (NF.Qp v Q) : ℝ) - 1) / (qv v) ^ (n - 1))) :=
    tendsto_const_nhds.congr' (hev.mono fun j hj => hj.symm)
  exact tendsto_nhds_unique (tendsto_coneFactor Q hQ hn v) hlim

/-- **The good-place bound** ($n \ge 5$): $|\gamma_v - 1| \le 2N\mathfrak p_v^{-2}$ at every $v \nmid 2\det H_Q$. -/
theorem abs_coneFactor_sub_one_le (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 5 ≤ n)
    {v : HeightOneSpectrum (𝓞 F)} (hv : IsGoodPlace Q v) :
    |coneFactor Q v - 1| ≤ 2 * (normP v : ℝ) ^ (-(2 : ℝ)) := by
  obtain ⟨h2, hd⟩ := not_dvd_of_isGoodPlace hv
  have hQv := NF.nondegenerate_Qp v hQ
  have hq2 : (2 : ℝ) ≤ qv v := by exact_mod_cast q_ge_two v
  have hq0 : (0 : ℝ) < qv v := by linarith
  have hnorm : (normP v : ℝ) ^ (-(2 : ℝ)) = ((qv v) ^ 2)⁻¹ := by
    rw [← qv_eq, Real.rpow_neg hq0.le, Real.rpow_two]
  rw [hnorm, coneFactor_good Q hQ (by omega) hv]
  have hN1e : ∀ m, n = 2 * m → (N1 v (NF.Qp v Q) : ℝ) =
      (qv v) ^ (2 * m - 1) + (DVR.chiDisc (NF.Qp v Q) : ℝ) * ((qv v) - 1) * (qv v) ^ (m - 1) := by
    intro m hm
    subst hm
    have hN := ((DVR.card_mod_pi_of_unimodular (NF.Qp v Q) (NF.π v) (NF.irreducible_π v) h2 hd (by omega) 1
      (fun h => (NF.irreducible_π v).not_isUnit (isUnit_of_dvd_one h))).1 (even_two_mul m)).1
    have hN' : (N1 v (NF.Qp v Q) : ℝ) =
        (qv v) ^ (2 * m - 1) + (DVR.chiDisc (NF.Qp v Q) : ℝ) * ((qv v) - 1) * (qv v) ^ (2 * m / 2 - 1) := by
      exact_mod_cast hN
    rwa [show 2 * m / 2 - 1 = m - 1 by omega] at hN'
  have hN1o : ∀ m, n = 2 * m + 1 → (N1 v (NF.Qp v Q) : ℝ) = (qv v) ^ (2 * m) := by
    intro m hm
    subst hm
    have hN := ((DVR.card_mod_pi_of_unimodular (NF.Qp v Q) (NF.π v) (NF.irreducible_π v) h2 hd (by omega) 1
      (fun h => (NF.irreducible_π v).not_isUnit (isUnit_of_dvd_one h))).2 (odd_two_mul_add_one m)).1
    have e : 2 * m + 1 - 1 = 2 * m := by omega
    rw [e] at hN; exact_mod_cast hN
  have hε := DVR.chiDisc_sq (NF.irreducible_π v) h2 hd
  generalize hεdef : ((DVR.chiDisc (NF.Qp v Q) : ℤ) : ℝ) = ε at hN1e hε
  generalize hNdef : (N1 v (NF.Qp v Q) : ℝ) = N at hN1e hN1o ⊢
  set q : ℝ := qv v with hqdef
  have hpos : ∀ k : ℕ, 0 < q ^ k := fun k => pow_pos hq0 k
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have key : ∀ k : ℕ, 1 ≤ k → 1 ≤ q ^ k := fun k _ => one_le_pow₀ hq1
  have hinv2 : ((q) ^ 2)⁻¹ ≤ 2 * ((q) ^ 2)⁻¹ := by
    have : 0 < ((q) ^ 2)⁻¹ := inv_pos.mpr (hpos 2)
    linarith
  refine le_trans ?_ hinv2
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · -- n = 2m even, m ≥ 3
    have hN' := hN1e m rfl
    have hεc : ε = 1 ∨ ε = -1 := mul_self_eq_one_iff.mp (by rw [← sq]; exact hε)
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
    rw [hN']
    have e1 : 2 * (k + 3) - 1 = 2 * k + 5 := by omega
    have e2 : k + 3 - 1 = k + 2 := by omega
    rw [e1, e2]
    have hqk : 0 < q ^ (2 * k + 5) := hpos _
    have hA : 1 ≤ q ^ (k + 2) := key _ (by omega)
    have hB : q ^ (2 * k + 5) = q ^ (k + 3) * q ^ (k + 2) := by ring
    have hq3 : q ^ (k + 3) = q * q ^ (k + 2) := by ring
    have expr : (q ^ (2 * k + 5) + ε * (q - 1) * q ^ (k + 2) - 1) / q ^ (2 * k + 5) - 1 =
        (ε * (q - 1) * q ^ (k + 2) - 1) / q ^ (2 * k + 5) := by
      field_simp; ring
    rw [expr, abs_div, abs_of_pos hqk, div_le_iff₀ hqk]
    have hnum : |ε * (q - 1) * q ^ (k + 2) - 1| ≤ (q - 1) * q ^ (k + 2) + 1 := by
      calc |ε * (q - 1) * q ^ (k + 2) - 1| ≤ |ε * (q - 1) * q ^ (k + 2)| + |(1 : ℝ)| := abs_sub _ _
        _ = (q - 1) * q ^ (k + 2) + 1 := by
          have hε1 : |ε| = 1 := by rcases hεc with h | h <;> rw [h] <;> simp
          rw [abs_mul, abs_mul, hε1, one_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ q - 1),
            abs_of_pos (hpos (k + 2)), abs_one]
    refine hnum.trans ?_
    have : ((q) ^ 2)⁻¹ * q ^ (2 * k + 5) = q ^ (2 * k + 3) := by
      rw [show 2 * k + 5 = 2 + (2 * k + 3) by ring, pow_add]; field_simp
    rw [this]
    have hh : q ^ (2 * k + 3) = q ^ (k + 1) * q ^ (k + 2) := by ring
    rw [hh]
    have hq1' : q ^ (k + 1) ≥ q := by
      calc q ^ (k + 1) = q ^ k * q := pow_succ _ _
        _ ≥ 1 * q := by gcongr; exact one_le_pow₀ hq1
        _ = q := one_mul _
    nlinarith [hpos (k + 2), hA]
  · -- n = 2m + 1 odd, m ≥ 2
    have hN' := hN1o m rfl
    rw [hN', show 2 * m + 1 - 1 = 2 * m by omega]
    have hqm : 0 < q ^ (2 * m) := hpos _
    have expr : (q ^ (2 * m) - 1) / q ^ (2 * m) - 1 = -(q ^ (2 * m))⁻¹ := by
      field_simp; ring
    rw [expr, abs_neg, abs_of_pos (inv_pos.mpr hqm)]
    exact inv_anti₀ (hpos 2) (pow_le_pow_right₀ hq1 (by omega))

/-- **The cone Euler product converges absolutely for $n \ge 5$** ($I_C < \infty \iff$ the cone Euler
product converges, iff $m > 4$; Weil §4.5 p. 108 for the analogous product of the zeta functions). -/
@[kb "weil1982" "§4.5, p. 108 and §2.4 (cone term converges, m > 4) [unverified]"]
theorem multipliable_coneFactor (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 5 ≤ n) :
    Multipliable (coneFactor Q) :=
  multipliable_of_abs_sub_one_le _ (C := 2) (σ := 2) (by norm_num)
    ((isGoodPlace_cofinite Q hQ).mono fun _ hv => abs_coneFactor_sub_one_le Q hQ hn hv)

/-- Absolute convergence in the form $\sum_v |\gamma_v - 1| < \infty$. -/
theorem summable_abs_coneFactor_sub_one (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 5 ≤ n) :
    Summable fun v => |coneFactor Q v - 1| :=
  Summable.of_norm_bounded_eventually ((summable_normP_rpow (F := F) (σ := 2) (by norm_num)).mul_left 2)
    ((isGoodPlace_cofinite Q hQ).mono fun _ hv => by
      rw [Real.norm_eq_abs, abs_abs]; exact abs_coneFactor_sub_one_le Q hQ hn hv)

/-- **The full cone volume of $L_v$**: the primitive factor times the homogeneity series
$\sum_{i \ge 0} q^{-(n-2)i} = (1 - q^{2-n})^{-1}$. -/
def coneTotal (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  coneFactor Q v * (1 - ((qv v) ^ (n - 2))⁻¹)⁻¹

theorem multipliable_homogeneity (hn : 4 ≤ n) :
    Multipliable fun v : HeightOneSpectrum (𝓞 F) => (1 - ((qv v) ^ (n - 2))⁻¹)⁻¹ := by
  refine multipliable_of_abs_sub_one_le _ (C := 4) (σ := 2) (by norm_num) (Filter.Eventually.of_forall fun v => ?_)
  have hq2 : (2 : ℝ) ≤ qv v := by exact_mod_cast q_ge_two v
  have hq0 : (0 : ℝ) < qv v := by linarith
  have hnorm : (normP v : ℝ) ^ (-(2 : ℝ)) = ((qv v) ^ 2)⁻¹ := by
    rw [← qv_eq, Real.rpow_neg hq0.le, Real.rpow_two]
  rw [hnorm]
  set q : ℝ := qv v
  set x : ℝ := (q ^ (n - 2))⁻¹ with hx
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hx0 : 0 < x := inv_pos.mpr (pow_pos hq0 _)
  have hxle : x ≤ ((q) ^ 2)⁻¹ := inv_anti₀ (pow_pos hq0 2) (pow_le_pow_right₀ hq1 (by omega))
  have hq4 : ((q) ^ 2)⁻¹ ≤ 1 / 4 := by
    rw [inv_eq_one_div]; apply one_div_le_one_div_of_le (by norm_num); nlinarith
  have h1x : 0 < 1 - x := by linarith
  have : (1 - x)⁻¹ - 1 = x / (1 - x) := by field_simp; ring
  rw [this, abs_of_pos (div_pos hx0 h1x), div_le_iff₀ h1x]
  nlinarith [inv_pos.mpr (pow_pos hq0 2)]

theorem multipliable_coneTotal (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 5 ≤ n) :
    Multipliable (coneTotal Q) :=
  (multipliable_coneFactor Q hQ hn).mul (multipliable_homogeneity (F := F) (n := n) (by omega))

end QuadFormsKB.Tamagawa.Measure.LerayCone
