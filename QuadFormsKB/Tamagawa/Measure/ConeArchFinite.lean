import QuadFormsKB.Tamagawa.Measure.ConeComplexOrbit

/-!
# Finiteness of the archimedean cone measure

For $Q = \langle c\rangle\perp\langle -c\rangle\perp Q'$ (`coneForm c Q'`, $c \ne 0$, $Q'$ nondegenerate in $k \ge 1$
variables) over $\mathbb R$ or $\mathbb C$, let $\sigma_C$ = `sigCone hc` be the Leray measure of the punctured cone
$C^\circ = \{z : Q(z) = 0,\ z \ne 0\}$ (`ConeRealOrbit.lean`, `ConeComplexOrbit.lean`). It is a priori only a measure,
sigma-finite and $SO(Q)$-invariant, homogeneous of degree $d$ ($d = k$ over $\mathbb R$, $d = 2k$ over $\mathbb C$,
since $|a|_{\mathbb C} = |a|^2$). This file proves that it is **finite on bounded sets** and that Gaussians are
**integrable**: writing $\|z\|$ for the sup norm on $K^{k+2}$ and $B_R = \{z \in C^\circ : \|z\| \le R\}$,

* `sigCone_closedBall_lt_top`: $\sigma_C(B_R) < \infty$ for every $R$;
* `sigCone_closedBall_eq`: $\sigma_C(B_R) = R^{d}\,\sigma_C(B_1)$ for $R > 0$ (explicit homogeneous bound);
* `lintegral_sigCone_gaussian_lt_top`: if $0 \le \Phi(z) \le C e^{-a\|z\|^2}$ on $C^\circ$ ($a > 0$, $C \ge 0$) then
  $\int_{C^\circ}\Phi\,d\sigma_C < \infty$. This makes the cone integral $I_C(\Phi_\infty)$ finite for Gaussian test
  functions $\Phi_\infty$ (a Gaussian of a positive majorant is bounded by $Ce^{-a\|z\|^2}$).

**Proof.** (a) On $\{\|z\| \le R,\ |z_0| \ge \delta\}$ the cone measure is controlled directly by
`lintegral_sigCone`: $q = z_0$ runs over $\delta \le |q| \le R$, and $y = z'/z_0$ lies in the ball of radius $R/\delta$
of the sphere $S'_{-c}$, which has finite measure. (b) The annulus $\{r \le \|z\| \le R\} \cap C^\circ$ is the
trace of a compact set; by `cone_cover` and compactness there is $\delta > 0$ such that for each of its points some $g$
in the finite list `coneList` has $|(gz)_0| \ge \delta$; by $SO(Q)$-invariance (`map_smul_sigCone`, $k \ge 1$) each
piece is the preimage under $g$ of a set as in (a). (c) The ball is the union of the dyadic annuli
$2^{-j}\{1/2 \le \|z\| \le 1\}$, whose measures are $2^{-jd}\sigma_C(\text{annulus})$ by homogeneity
(`map_coneScale_sigCone`), a convergent geometric series ($d \ge 1$). (d) For the Gaussian, split into the unit ball
and the shells $2^j \le \|z\| < 2^{j+1}$; the shell $j$ contributes at most $C e^{-a4^j}\,2^{(j+1)d}\,\sigma_C(B_1)$,
and $\sum_j 2^{(j+1)d}e^{-a4^j} < \infty$ (bound $e^{t} \ge t^{d+1}/(d+1)!$).

The exponent of the Gaussian is written `-(a * ‖z‖ ^ 2)`, i.e. $e^{-a\|z\|^2}$. The measurability of $\Phi$ is not
needed (upper Lebesgue integrals). Steps (b)-(d) are proved once, abstractly (`measure_annulus_lt_top`,
`measure_ball_one_lt_top`, `lintegral_gaussian_lt_top_abstract`), and instantiated at the real place
(namespace `ConeReal`) and the complex place (namespace `ConeComplex`).
-/

open MeasureTheory Measure Matrix Set Filter Topology
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.ConeArchFinite

/-! ### Abstract part: annuli, dyadic decomposition, Gaussian shells -/

section Abstract

variable {X ι : Type*} [MeasurableSpace X]

/-- **Finiteness on an annulus from finiteness on cutoffs**: let $\mu$ be a measure on $X$, $N, p : X \to \mathbb R$
measurable, and $(\varphi_i)_{i \in s}$ a finite family of measurable $\mu$-preserving maps such that
(`hD`) $\mu\{N \le C,\ p \ge \delta\} < \infty$ for $\delta > 0$, (`hcov`) on each annulus $r \le N \le R$ ($r > 0$) some
$\varphi_i$ has $p \circ \varphi_i \ge \delta$ for a uniform $\delta > 0$, (`hbd`) each $\varphi_i$ is bounded for $N$
on each annulus. Then $\mu\{r \le N \le R\} < \infty$. -/
theorem measure_annulus_lt_top (μ : Measure X) (N p : X → ℝ) (hN : Measurable N) (hp : Measurable p)
    {s : Set ι} (hs : s.Finite) (φ : ι → X → X) (hφm : ∀ i, Measurable (φ i))
    (hφ : ∀ i ∈ s, μ.map (φ i) = μ)
    (hD : ∀ C δ : ℝ, 0 < δ → μ {w | N w ≤ C ∧ δ ≤ p w} < ⊤)
    (hcov : ∀ r R : ℝ, 0 < r →
      ∃ δ, 0 < δ ∧ ∀ x, r ≤ N x → N x ≤ R → ∃ i ∈ s, δ ≤ p (φ i x))
    (hbd : ∀ r R : ℝ, 0 < r → ∀ i ∈ s, ∃ C, ∀ x, r ≤ N x → N x ≤ R → N (φ i x) ≤ C)
    {r R : ℝ} (hr : 0 < r) : μ {x | r ≤ N x ∧ N x ≤ R} < ⊤ := by
  obtain ⟨δ, hδ, hc⟩ := hcov r R hr
  have hsub : {x | r ≤ N x ∧ N x ≤ R} ⊆
      ⋃ i ∈ s, {x | r ≤ N x ∧ N x ≤ R ∧ δ ≤ p (φ i x)} := by
    intro x hx
    obtain ⟨i, hi, h⟩ := hc x hx.1 hx.2
    exact mem_biUnion hi ⟨hx.1, hx.2, h⟩
  refine lt_of_le_of_lt (measure_mono hsub) ?_
  refine lt_top_iff_ne_top.mpr (measure_biUnion_lt_top hs fun i hi => ?_).ne
  obtain ⟨C, hC⟩ := hbd r R hr i hi
  have hDm : MeasurableSet {w | N w ≤ C ∧ δ ≤ p w} :=
    (measurableSet_le hN measurable_const).inter (measurableSet_le measurable_const hp)
  have hsub' : {x | r ≤ N x ∧ N x ≤ R ∧ δ ≤ p (φ i x)} ⊆ φ i ⁻¹' {w | N w ≤ C ∧ δ ≤ p w} :=
    fun x hx => ⟨hC x hx.1 hx.2.1, hx.2.2⟩
  refine lt_of_le_of_lt (measure_mono hsub') ?_
  rw [← Measure.map_apply (hφm i) hDm, hφ i hi]
  exact hD C δ hδ

/-- **Homogeneous growth of balls**: if $\mu(t^{-1}A) = t^{-d}\mu(A)$ and $N(t\cdot x) = tN(x)$ for the dilations
$t \cdot$ ($t > 0$), then $\mu\{N \le R\} = R^d\mu\{N \le 1\}$. -/
theorem measure_ball_scale (μ : Measure X) (N : X → ℝ) (sc : (t : ℝ) → 0 < t → X → X) (d : ℕ)
    (hNsc : ∀ t (ht : 0 < t) x, N (sc t ht x) = t * N x)
    (hμ : ∀ t (ht : 0 < t) A, MeasurableSet A →
      μ (sc t ht ⁻¹' A) = ENNReal.ofReal ((t⁻¹) ^ d) * μ A)
    (hN : Measurable N) {R : ℝ} (hR : 0 < R) :
    μ {x | N x ≤ R} = ENNReal.ofReal (R ^ d) * μ {x | N x ≤ 1} := by
  have h := hμ R⁻¹ (inv_pos.mpr hR) {x | N x ≤ 1} (measurableSet_le hN measurable_const)
  rw [inv_inv] at h
  have e : sc R⁻¹ (inv_pos.mpr hR) ⁻¹' {x | N x ≤ 1} = {x | N x ≤ R} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, hNsc _ (inv_pos.mpr hR)]
    rw [← div_eq_inv_mul, div_le_one hR]
  rw [e] at h
  exact h

/-- **The unit ball from the unit annulus** (dyadic decomposition): in the setting of `measure_ball_scale`, if
$N > 0$ everywhere, $d \ge 1$ and $\mu\{1/2 \le N \le 1\} < \infty$, then $\mu\{N \le 1\} < \infty$, since
$\{N \le 1\} = \bigcup_j 2^{-j}\{1/2 \le N \le 1\}$ and $\mu(2^{-j}A) = 2^{-jd}\mu(A)$. -/
theorem measure_ball_one_lt_top (μ : Measure X) (N : X → ℝ) (sc : (t : ℝ) → 0 < t → X → X) (d : ℕ)
    (hNsc : ∀ t (ht : 0 < t) x, N (sc t ht x) = t * N x)
    (hμ : ∀ t (ht : 0 < t) A, MeasurableSet A →
      μ (sc t ht ⁻¹' A) = ENNReal.ofReal ((t⁻¹) ^ d) * μ A)
    (hN : Measurable N) (hd : 1 ≤ d) (hpos : ∀ x, 0 < N x)
    (hA : μ {x | 1 / 2 ≤ N x ∧ N x ≤ 1} < ⊤) : μ {x | N x ≤ 1} < ⊤ := by
  set A0 : Set X := {x | 1 / 2 ≤ N x ∧ N x ≤ 1} with hA0
  have hA0m : MeasurableSet A0 :=
    (measurableSet_le measurable_const hN).inter (measurableSet_le hN measurable_const)
  have hcov : {x | N x ≤ 1} ⊆ ⋃ j : ℕ, sc ((2 : ℝ) ^ j) (by positivity) ⁻¹' A0 := by
    intro x hx
    obtain ⟨n, h1, h2⟩ := exists_nat_pow_near_of_lt_one (hpos x) hx
      (show (0 : ℝ) < 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
    refine mem_iUnion.mpr ⟨n, ?_⟩
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    simp only [mem_preimage, hA0, mem_ofPred_eq, hNsc _ h2n]
    constructor
    · have : (1 / 2 : ℝ) ^ (n + 1) = 1 / 2 * (2 ^ n)⁻¹ := by
        rw [pow_succ, one_div, inv_pow, mul_comm]
      rw [this] at h1
      have := mul_lt_mul_of_pos_left h1 h2n
      rw [mul_comm (1 / 2 : ℝ), ← mul_assoc, mul_inv_cancel₀ h2n.ne', one_mul] at this
      linarith
    · have : (1 / 2 : ℝ) ^ n = (2 ^ n)⁻¹ := by rw [one_div, inv_pow]
      rw [this] at h2
      calc (2 : ℝ) ^ n * N x ≤ 2 ^ n * (2 ^ n)⁻¹ := mul_le_mul_of_nonneg_left h2 h2n.le
        _ = 1 := mul_inv_cancel₀ h2n.ne'
  set ρ : ℝ≥0∞ := ENNReal.ofReal (((2 : ℝ)⁻¹) ^ d) with hρ
  have hρ1 : ρ < 1 := by
    rw [hρ, ← ENNReal.ofReal_one]
    refine (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr ?_
    exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hterm : ∀ j : ℕ, μ (sc ((2 : ℝ) ^ j) (by positivity) ⁻¹' A0) = ρ ^ j * μ A0 := by
    intro j
    rw [hμ _ (by positivity) A0 hA0m, hρ, ← ENNReal.ofReal_pow (by positivity)]
    congr 2
    rw [inv_pow, inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm]
  calc μ {x | N x ≤ 1} ≤ μ (⋃ j : ℕ, sc ((2 : ℝ) ^ j) (by positivity) ⁻¹' A0) := measure_mono hcov
    _ ≤ ∑' j : ℕ, μ (sc ((2 : ℝ) ^ j) (by positivity) ⁻¹' A0) := measure_iUnion_le _
    _ = (∑' j : ℕ, ρ ^ j) * μ A0 := by
        simp_rw [hterm]; rw [ENNReal.tsum_mul_right]
    _ < ⊤ := by
        rw [ENNReal.tsum_geometric]
        exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (tsub_pos_of_lt hρ1)) hA

/-- **The shell estimate**: $C e^{-a4^j}\,(2^{j+1})^d \le K r^j$ with $K = C2^d(d+1)!/a^{d+1}$ and
$r = 2^d/4^{d+1} < 1$ (from $e^t \ge t^{d+1}/(d+1)!$). -/
theorem gaussian_shell_bound {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (d j : ℕ) :
    C * Real.exp (-(a * ((2 : ℝ) ^ j) ^ 2)) * ((2 : ℝ) ^ (j + 1)) ^ d ≤
      (C * 2 ^ d * ((d + 1).factorial : ℝ) / a ^ (d + 1)) * ((2 : ℝ) ^ d / 4 ^ (d + 1)) ^ j := by
  have h4 : ((2 : ℝ) ^ j) ^ 2 = 4 ^ j := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4]
  have ht : 0 < a * (4 : ℝ) ^ j := by positivity
  have hexp : Real.exp (-(a * (4 : ℝ) ^ j)) ≤
      ((d + 1).factorial : ℝ) / (a * (4 : ℝ) ^ j) ^ (d + 1) := by
    have h := Real.pow_div_factorial_le_exp (a * (4 : ℝ) ^ j) ht.le (d + 1)
    rw [Real.exp_neg]
    have hp : 0 < (a * (4 : ℝ) ^ j) ^ (d + 1) / ((d + 1).factorial : ℝ) := by positivity
    calc (Real.exp (a * 4 ^ j))⁻¹ ≤ ((a * (4 : ℝ) ^ j) ^ (d + 1) / ((d + 1).factorial : ℝ))⁻¹ :=
          inv_anti₀ hp h
      _ = _ := inv_div _ _
  have hW : (0 : ℝ) ≤ ((2 : ℝ) ^ (j + 1)) ^ d := by positivity
  calc C * Real.exp (-(a * (4 : ℝ) ^ j)) * ((2 : ℝ) ^ (j + 1)) ^ d
      ≤ C * (((d + 1).factorial : ℝ) / (a * (4 : ℝ) ^ j) ^ (d + 1)) * ((2 : ℝ) ^ (j + 1)) ^ d := by
        gcongr
    _ = _ := by
        have e1 : ((2 : ℝ) ^ (j + 1)) ^ d = 2 ^ d * (2 ^ d) ^ j := by
          rw [pow_succ, mul_pow, ← pow_mul, ← pow_mul, mul_comm d j, mul_comm]
        have e2 : ((4 : ℝ) ^ j) ^ (d + 1) = (4 ^ (d + 1)) ^ j := by
          rw [← pow_mul, ← pow_mul, mul_comm]
        rw [e1, mul_pow, e2, div_pow]
        field_simp

/-- **Gaussian integrability from homogeneous growth of balls**: if $\mu\{N \le R\} = R^d\mu\{N \le 1\}$ for $R > 0$
with $\mu\{N \le 1\} < \infty$, and $\Phi \le Ce^{-aN^2}$ ($a > 0$, $C \ge 0$), then $\int\Phi\,d\mu < \infty$. -/
theorem lintegral_gaussian_lt_top_abstract (μ : Measure X) (N : X → ℝ)
    (hN : Measurable N) (d : ℕ)
    (hball : ∀ R : ℝ, 0 < R → μ {x | N x ≤ R} = ENNReal.ofReal (R ^ d) * μ {x | N x ≤ 1})
    (hm : μ {x | N x ≤ 1} < ⊤) {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (Φ : X → ℝ≥0∞)
    (hΦ : ∀ x, Φ x ≤ ENNReal.ofReal (C * Real.exp (-(a * N x ^ 2)))) :
    ∫⁻ x, Φ x ∂μ < ⊤ := by
  set m1 : ℝ≥0∞ := μ {x | N x ≤ 1} with hm1
  set S : Set X := {x | N x ≤ 1} with hS
  have hSm : MeasurableSet S := measurableSet_le hN measurable_const
  set T : ℕ → Set X := fun j => {x | (2 : ℝ) ^ j ≤ N x ∧ N x < 2 ^ (j + 1)} with hT
  have hTm : ∀ j, MeasurableSet (T j) := fun j =>
    (measurableSet_le measurable_const hN).inter (measurableSet_lt hN measurable_const)
  have hTcov : Sᶜ ⊆ ⋃ j, T j := by
    intro x hx
    have hx1 : 1 ≤ N x := le_of_lt (not_le.mp hx)
    obtain ⟨n, h1, h2⟩ := exists_nat_pow_near hx1 (one_lt_two : (1 : ℝ) < 2)
    exact mem_iUnion.mpr ⟨n, h1, h2⟩
  set K : ℝ := C * 2 ^ d * ((d + 1).factorial : ℝ) / a ^ (d + 1) with hK
  set r : ℝ := (2 : ℝ) ^ d / 4 ^ (d + 1) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hr, div_lt_one (by positivity), pow_succ]
    have : (2 : ℝ) ^ d ≤ 4 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
    have h4 : (0 : ℝ) < 4 ^ d := by positivity
    nlinarith
  have hshell : ∀ j : ℕ, ∫⁻ x in T j, Φ x ∂μ ≤ ENNReal.ofReal K * ENNReal.ofReal r ^ j * m1 := by
    intro j
    have hb : ∀ x ∈ T j, Φ x ≤ ENNReal.ofReal (C * Real.exp (-(a * ((2 : ℝ) ^ j) ^ 2))) := by
      intro x hx
      refine (hΦ x).trans (ENNReal.ofReal_le_ofReal ?_)
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
      have : ((2 : ℝ) ^ j) ^ 2 ≤ N x ^ 2 :=
        pow_le_pow_left₀ (by positivity) hx.1 2
      nlinarith
    calc ∫⁻ x in T j, Φ x ∂μ
        ≤ ∫⁻ x in T j, ENNReal.ofReal (C * Real.exp (-(a * ((2 : ℝ) ^ j) ^ 2))) ∂μ :=
          setLIntegral_mono' (hTm j) hb
      _ = ENNReal.ofReal (C * Real.exp (-(a * ((2 : ℝ) ^ j) ^ 2))) * μ (T j) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (C * Real.exp (-(a * ((2 : ℝ) ^ j) ^ 2))) *
            (ENNReal.ofReal (((2 : ℝ) ^ (j + 1)) ^ d) * m1) := by
          gcongr
          rw [← hball _ (by positivity)]
          exact measure_mono fun x hx => (hx.2).le
      _ = ENNReal.ofReal (C * Real.exp (-(a * ((2 : ℝ) ^ j) ^ 2)) * ((2 : ℝ) ^ (j + 1)) ^ d) * m1 := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (K * r ^ j) * m1 :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (gaussian_shell_bound ha hC d j)) le_rfl
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hr0]
  have h1 : ∫⁻ x in S, Φ x ∂μ ≤ ENNReal.ofReal C * m1 := by
    calc ∫⁻ x in S, Φ x ∂μ ≤ ∫⁻ x in S, ENNReal.ofReal C ∂μ := by
          refine setLIntegral_mono' hSm fun x _ => (hΦ x).trans (ENNReal.ofReal_le_ofReal ?_)
          have : Real.exp (-(a * N x ^ 2)) ≤ 1 := by
            rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg (N x)]
          nlinarith
      _ = _ := setLIntegral_const _ _
  have hρ : ENNReal.ofReal r < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr hr1
  calc ∫⁻ x, Φ x ∂μ = ∫⁻ x in S, Φ x ∂μ + ∫⁻ x in Sᶜ, Φ x ∂μ := (lintegral_add_compl _ hSm).symm
    _ ≤ ENNReal.ofReal C * m1 + ∑' j : ℕ, ENNReal.ofReal K * ENNReal.ofReal r ^ j * m1 := by
        gcongr
        calc ∫⁻ x in Sᶜ, Φ x ∂μ ≤ ∫⁻ x in ⋃ j, T j, Φ x ∂μ := lintegral_mono_set hTcov
          _ ≤ ∑' j, ∫⁻ x in T j, Φ x ∂μ := lintegral_iUnion_le _ _
          _ ≤ _ := ENNReal.tsum_le_tsum hshell
    _ < ⊤ := by
        refine ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hm, ?_⟩
        rw [ENNReal.tsum_mul_right]
        refine ENNReal.mul_lt_top ?_ hm
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.inv_lt_top.mpr (tsub_pos_of_lt hρ))

end Abstract

/-! ### Compactness lemmas -/

/-- **Uniform non-vanishing on a compact set**: if finitely many continuous maps $f_i$ have no common zero on a
compact $S$, then $\max_i\|f_i\| \ge \delta$ on $S$ for some $\delta > 0$. -/
theorem exists_delta_of_compact {E V ι : Type*} [TopologicalSpace E] [NormedAddCommGroup V]
    {S : Set E} (hS : IsCompact S) (s : Finset ι) (f : ι → E → V) (hf : ∀ i, Continuous (f i))
    (h : ∀ x ∈ S, ∃ i ∈ s, f i x ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, ∃ i ∈ s, δ ≤ ‖f i x‖ := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun x hx => absurd hx (notMem_empty x)⟩
  set g : E → ℝ := fun x => ∑ i ∈ s, ‖f i x‖ with hg
  have hgc : Continuous g := continuous_finsetSum _ fun i _ => (hf i).norm
  obtain ⟨x₀, hx₀, hmin⟩ := hS.exists_isMinOn hne hgc.continuousOn
  obtain ⟨i₀, hi₀, hne₀⟩ := h x₀ hx₀
  have hs : s.Nonempty := ⟨i₀, hi₀⟩
  have hg0 : 0 < g x₀ :=
    Finset.sum_pos' (fun i _ => norm_nonneg _) ⟨i₀, hi₀, norm_pos_iff.mpr hne₀⟩
  refine ⟨g x₀ / s.card, div_pos hg0 (Nat.cast_pos.mpr hs.card_pos), fun x hx => ?_⟩
  have hle : ∑ _i ∈ s, g x₀ / s.card ≤ ∑ i ∈ s, ‖f i x‖ := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_pos.mpr hs.card_pos).ne']
    exact hmin hx
  exact Finset.exists_le_of_sum_le hs hle

/-- The set $\{v : r \le \|v\| \le R,\ f(v) = 0\}$ is compact for continuous $f$ on a proper normed space. -/
theorem isCompact_annulus_zeroLocus {E : Type*} [NormedAddCommGroup E] [ProperSpace E] {W : Type*}
    [TopologicalSpace W] [T2Space W] [Zero W] {f : E → W} (hf : Continuous f) (r R : ℝ) :
    IsCompact {v : E | r ≤ ‖v‖ ∧ ‖v‖ ≤ R ∧ f v = 0} := by
  refine (isCompact_closedBall (0 : E) R).of_isClosed_subset ?_ ?_
  · exact (isClosed_le continuous_const continuous_norm).inter
      ((isClosed_le continuous_norm continuous_const).inter (isClosed_eq hf continuous_const))
  · intro v hv
    simpa using hv.2.1

end QuadFormsKB.Tamagawa.Measure.ConeArchFinite


/-! ### The real place -/

namespace QuadFormsKB.Tamagawa.Measure.ConeReal

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.ArchVol QuadFormsKB.Tamagawa.ArchSOMeasure
open QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.SphereLeray
open QuadFormsKB.Tamagawa.Measure.OrbitalReal QuadFormsKB.Tamagawa.Measure.ConeAlgebra
open QuadFormsKB.Tamagawa.Measure.ConeArchFinite

variable {k : ℕ} {c : ℝ} {Q' : QuadForm ℝ k}

theorem rhoK_zero : rhoK k 0 = 0 := by simp [rhoK]

/-- On $\delta \le |q| \le C$ the radial density $|q|^{k-1}$ is at most $C^k/\delta$. -/
theorem rhoK_le {q C δ : ℝ} (hδ : 0 < δ) (hq : δ ≤ |q|) (hqC : |q| ≤ C) :
    rhoK k q ≤ ENNReal.ofReal (C ^ k / δ) := by
  unfold rhoK
  refine ENNReal.ofReal_le_ofReal ?_
  have hq0 : 0 < |q| := lt_of_lt_of_le hδ hq
  exact div_le_div₀ (pow_nonneg (hq0.le.trans hqC) k) (pow_le_pow_left₀ hq0.le hqC k) hδ hq

/-- If $q(1, y)$ lies in the sup-norm ball of radius $C$ and $|q| \ge \delta > 0$ then $|q| \le C$ and
$\|y\| \le C/\delta$. -/
theorem norm_le_of_coneVec {q C δ : ℝ} {y : Fin (k + 1) → ℝ} (hδ : 0 < δ) (hq : δ ≤ |q|)
    (h : ‖coneVec q y‖ ≤ C) : |q| ≤ C ∧ ‖y‖ ≤ C / δ := by
  have h0 : |q| ≤ C := by
    have := norm_le_pi_norm (coneVec q y) 0
    rw [coneVec_zero, Real.norm_eq_abs] at this
    exact this.trans h
  refine ⟨h0, ?_⟩
  have hC : 0 ≤ C / δ := div_nonneg ((abs_nonneg q).trans h0) hδ.le
  refine (pi_norm_le_iff_of_nonneg hC).mpr fun i => ?_
  have h1 := norm_le_pi_norm (coneVec q y) i.succ
  rw [coneVec_succ, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs] at h1
  rw [Real.norm_eq_abs, le_div_iff₀ hδ]
  have h2 : |y i| * δ ≤ |y i| * |q| := mul_le_mul_of_nonneg_left hq (abs_nonneg _)
  nlinarith [h1.trans h]

/-- **Step (a): the cone measure of a cutoff region is finite.** For every $C$ and $\delta > 0$,
$\sigma_C\{z \in C^\circ : \|z\| \le C,\ |z_0| \ge \delta\} < \infty$ (from `lintegral_sigCone` and the finiteness of
the sphere measure of bounded sets, `nu_bounded_lt_top`). -/
theorem sigCone_cutoff_lt_top (hc : c ≠ 0) (C δ : ℝ) (hδ : 0 < δ) :
    sigCone (Q' := Q') hc {z | ‖(z : Fin (k + 1 + 1) → ℝ)‖ ≤ C ∧ δ ≤ ‖(z : Fin (k + 1 + 1) → ℝ) 0‖} < ⊤ := by
  have := sigmaFinite_sig (Q := Qm c Q') (neg_ne_zero.mpr hc)
  set D : Set (ConeT (coneForm c Q')) :=
    {z | ‖(z : Fin (k + 1 + 1) → ℝ)‖ ≤ C ∧ δ ≤ ‖(z : Fin (k + 1 + 1) → ℝ) 0‖} with hD
  have hDm : MeasurableSet D :=
    (measurableSet_le (continuous_norm.comp continuous_subtype_val).measurable measurable_const).inter
      (measurableSet_le measurable_const
        (continuous_norm.comp ((continuous_apply 0).comp continuous_subtype_val)).measurable)
  have hF : Measurable (D.indicator (1 : ConeT (coneForm c Q') → ℝ≥0∞)) := measurable_one.indicator hDm
  rw [← lintegral_indicator_one hDm, lintegral_sigCone hc hF]
  set K : ℝ≥0∞ := sig (Qm c Q') (-c) {y : Sph (Qm c Q') (-c) | ‖(y : Fin (k + 1) → ℝ)‖ ≤ C / δ} with hK
  have hKt : K < ⊤ := by
    have := nu_bounded_lt_top (Q := Qm c Q') (neg_ne_zero.mpr hc) (C / δ)
    rw [hK, sig, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top this
  have hKm : MeasurableSet {y : Sph (Qm c Q') (-c) | ‖(y : Fin (k + 1) → ℝ)‖ ≤ C / δ} :=
    measurableSet_le (continuous_norm.comp continuous_subtype_val).measurable measurable_const
  have hpt : ∀ q : ℝ, rhoK k q * ∫⁻ y, D.indicator (1 : ConeT (coneForm c Q') → ℝ≥0∞)
        (coneMap hc (q, y)) ∂sig (Qm c Q') (-c) ≤
      (Metric.closedBall (0 : ℝ) C).indicator (fun _ => ENNReal.ofReal (C ^ k / δ) * K) q := by
    intro q
    by_cases hq : q = 0
    · subst hq; rw [rhoK_zero, zero_mul]; exact zero_le
    have hmemD : ∀ y : Sph (Qm c Q') (-c), coneMap hc (q, y) ∈ D →
        δ ≤ |q| ∧ |q| ≤ C ∧ ‖(y : Fin (k + 1) → ℝ)‖ ≤ C / δ := by
      intro y hy
      have h1 : ‖(coneMap hc (q, y) : Fin (k + 1 + 1) → ℝ)‖ ≤ C := hy.1
      have h2 : δ ≤ ‖(coneMap hc (q, y) : Fin (k + 1 + 1) → ℝ) 0‖ := hy.2
      rw [coe_coneMap hc hq] at h1 h2
      rw [coneVec_zero, Real.norm_eq_abs] at h2
      exact ⟨h2, norm_le_of_coneVec hδ h2 h1⟩
    by_cases hgood : δ ≤ |q| ∧ |q| ≤ C
    · have hmem : q ∈ Metric.closedBall (0 : ℝ) C := by
        rw [mem_closedBall_zero_iff, Real.norm_eq_abs]; exact hgood.2
      rw [indicator_of_mem hmem]
      refine mul_le_mul' (rhoK_le hδ hgood.1 hgood.2) ?_
      calc ∫⁻ y, D.indicator (1 : ConeT (coneForm c Q') → ℝ≥0∞) (coneMap hc (q, y)) ∂sig (Qm c Q') (-c)
          ≤ ∫⁻ y, {y : Sph (Qm c Q') (-c) | ‖(y : Fin (k + 1) → ℝ)‖ ≤ C / δ}.indicator
              (1 : Sph (Qm c Q') (-c) → ℝ≥0∞) y ∂sig (Qm c Q') (-c) := by
            refine lintegral_mono fun y => ?_
            by_cases hy : coneMap hc (q, y) ∈ D
            · rw [indicator_of_mem hy, indicator_of_mem (show y ∈ _ from (hmemD y hy).2.2)]
              simp
            · rw [indicator_of_notMem hy]; exact zero_le
        _ = K := lintegral_indicator_one hKm
    · have h0 : ∀ y : Sph (Qm c Q') (-c),
          D.indicator (1 : ConeT (coneForm c Q') → ℝ≥0∞) (coneMap hc (q, y)) = 0 := fun y =>
        indicator_of_notMem (fun hy => hgood ⟨(hmemD y hy).1, (hmemD y hy).2.1⟩) _
      simp only [h0, lintegral_zero, mul_zero]; exact zero_le
  calc ∫⁻ q, rhoK k q * ∫⁻ y, D.indicator (1 : ConeT (coneForm c Q') → ℝ≥0∞) (coneMap hc (q, y))
        ∂sig (Qm c Q') (-c)
      ≤ ∫⁻ q, (Metric.closedBall (0 : ℝ) C).indicator (fun _ => ENNReal.ofReal (C ^ k / δ) * K) q :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (C ^ k / δ) * K * volume (Metric.closedBall (0 : ℝ) C) :=
        lintegral_indicator_const Metric.isClosed_closedBall.measurableSet _
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKt) measure_closedBall_lt_top

/-- **Step (b): the cone measure of an annulus is finite** ($k \ge 1$): for $r > 0$,
$\sigma_C\{z \in C^\circ : r \le \|z\| \le R\} < \infty$. Compactness of the annulus in $Q = 0$ and `cone_cover` give
$\delta > 0$ with $|(gz)_0| \ge \delta$ for some $g$ of the finite list `coneList`; then $SO(Q)$-invariance reduces to
`sigCone_cutoff_lt_top`. -/
theorem sigCone_annulus_lt_top (hc : c ≠ 0) (hQ': gramDetR Q' ≠ 0) (hk : 1 ≤ k) {r R : ℝ} (hr : 0 < r) :
    sigCone (Q' := Q') hc {z | r ≤ ‖(z : Fin (k + 1 + 1) → ℝ)‖ ∧ ‖(z : Fin (k + 1 + 1) → ℝ)‖ ≤ R} < ⊤ := by
  classical
  have hNm : Measurable fun z : ConeT (coneForm c Q') => ‖(z : Fin (k + 1 + 1) → ℝ)‖ :=
    (continuous_norm.comp continuous_subtype_val).measurable
  have hpm : Measurable fun z : ConeT (coneForm c Q') => ‖(z : Fin (k + 1 + 1) → ℝ) 0‖ :=
    (continuous_norm.comp ((continuous_apply 0).comp continuous_subtype_val)).measurable
  have hcont : ∀ g : ArchSO (coneForm c Q'), Continuous fun v : Fin (k + 1 + 1) → ℝ =>
      ArchSOInst.mat _ g *ᵥ v := fun g => continuous_const.matrix_mulVec continuous_id
  refine measure_annulus_lt_top (sigCone (Q' := Q') hc) (fun z : ConeT (coneForm c Q') => ‖(z : Fin (k + 1 + 1) → ℝ)‖)
    (fun z : ConeT (coneForm c Q') => ‖(z : Fin (k + 1 + 1) → ℝ) 0‖) hNm hpm (s := {g | g ∈ coneList hc hQ'})
    (List.finite_toSet _) (fun g z => g • z) measurable_smul_cone
    (fun g _ => map_smul_sigCone hc hQ' hk g) (fun C δ hδ => sigCone_cutoff_lt_top hc C δ hδ) ?_ ?_ hr
  · intro r R hr
    obtain ⟨δ, hδ, h⟩ := exists_delta_of_compact
      (isCompact_annulus_zeroLocus (continuous_eval_real (coneForm c Q')) r R)
      (coneList hc hQ').toFinset (fun g v => (ArchSOInst.mat _ g *ᵥ v) 0)
      (fun g => (continuous_apply 0).comp (hcont g)) (by
        rintro v ⟨hv1, hv2, hv3⟩
        have hv0 : v ≠ 0 := by
          rintro rfl
          rw [norm_zero] at hv1
          linarith
        obtain ⟨g, hg, hg0⟩ := cone_cover hc hQ' (⟨v, hv3, hv0⟩ : ConeT (coneForm c Q'))
        exact ⟨g, List.mem_toFinset.mpr hg, hg0⟩)
    refine ⟨δ, hδ, fun z hz1 hz2 => ?_⟩
    obtain ⟨g, hg, hδg⟩ := h (z : Fin (k + 1 + 1) → ℝ) ⟨hz1, hz2, z.2.1⟩
    exact ⟨g, List.mem_toFinset.mp hg, hδg⟩
  · intro r R hr g _
    obtain ⟨C, hC⟩ := (isCompact_annulus_zeroLocus (continuous_eval_real (coneForm c Q')) r R).exists_bound_of_continuousOn
      (hcont g).continuousOn
    exact ⟨C, fun z hz1 hz2 => hC (z : Fin (k + 1 + 1) → ℝ) ⟨hz1, hz2, z.2.1⟩⟩

theorem norm_coneScale {t : ℝ} (ht : 0 < t) (z : ConeT (coneForm c Q')) :
    ‖(coneScale (Q' := Q') (c := c) ht.ne' z : Fin (k + 1 + 1) → ℝ)‖ = t * ‖(z : Fin (k + 1 + 1) → ℝ)‖ := by
  show ‖t • (z : Fin (k + 1 + 1) → ℝ)‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]

theorem sigCone_preimage_coneScale (hc : c ≠ 0) {t : ℝ} (ht : 0 < t) {A : Set (ConeT (coneForm c Q'))}
    (hA : MeasurableSet A) :
    sigCone (Q' := Q') hc (coneScale (Q' := Q') (c := c) ht.ne' ⁻¹' A) =
      ENNReal.ofReal ((t⁻¹) ^ k) * sigCone hc A := by
  rw [← Measure.map_apply (measurable_coneScale ht.ne') hA, map_coneScale_sigCone hc ht.ne',
    Measure.smul_apply, smul_eq_mul, abs_of_pos ht]

/-- **Homogeneous bound for balls** (real place): $\sigma_C(B_R) = R^k\,\sigma_C(B_1)$ for $R > 0$, where
$B_R = \{z \in C^\circ : \|z\| \le R\}$ (sup norm). -/
@[kb "weil1982" "§2.2 (homogeneity of the Leray form on the cone, ball growth) [unverified]"]
theorem sigCone_closedBall_eq (hc : c ≠ 0) {R : ℝ} (hR : 0 < R) :
    sigCone (Q' := Q') hc {z | ‖(z : Fin (k + 1 + 1) → ℝ)‖ ≤ R} =
      ENNReal.ofReal (R ^ k) * sigCone (Q' := Q') hc {z | ‖(z : Fin (k + 1 + 1) → ℝ)‖ ≤ 1} :=
  measure_ball_scale (sigCone (Q' := Q') hc) (fun z : ConeT (coneForm c Q') => ‖(z : Fin (k + 1 + 1) → ℝ)‖)
    (fun t ht => coneScale (Q' := Q') (c := c) ht.ne') k
    (fun t ht z => norm_coneScale (Q' := Q') (c := c) ht z)
    (fun t ht A hA => sigCone_preimage_coneScale hc ht hA)
    (continuous_norm.comp continuous_subtype_val).measurable hR

/-- **The unit ball of the cone has finite measure** (real place, $k \ge 1$), by the dyadic decomposition into
the annuli $2^{-j}\{1/2 \le \|z\| \le 1\}$ and homogeneity of degree $k \ge 1$. -/
theorem sigCone_closedBall_one_lt_top (hc : c ≠ 0) (hQ': gramDetR Q' ≠ 0) (hk : 1 ≤ k) :
    sigCone (Q' := Q') hc {z | ‖(z : Fin (k + 1 + 1) → ℝ)‖ ≤ 1} < ⊤ :=
  measure_ball_one_lt_top (sigCone (Q' := Q') hc) (fun z : ConeT (coneForm c Q') => ‖(z : Fin (k + 1 + 1) → ℝ)‖)
    (fun t ht => coneScale (Q' := Q') (c := c) ht.ne') k
    (fun t ht z => norm_coneScale (Q' := Q') (c := c) ht z)
    (fun t ht A hA => sigCone_preimage_coneScale hc ht hA)
    (continuous_norm.comp continuous_subtype_val).measurable hk
    (fun z => norm_pos_iff.mpr z.2.2) (sigCone_annulus_lt_top hc hQ' hk (by norm_num))

/-- **Finiteness of the cone measure on bounded sets** (real place): for $c \ne 0$, $Q'$ nondegenerate in $k \ge 1$
variables and every $R$, $\sigma_C\{z \in C^\circ : \|z\| \le R\} < \infty$ (sup norm). -/
@[kb "weil1982" "§2.2 (local finiteness of the Leray measure of the cone) [unverified]"]
theorem sigCone_closedBall_lt_top (hc : c ≠ 0) (hQ': gramDetR Q' ≠ 0) (hk : 1 ≤ k) (R : ℝ) :
    sigCone (Q' := Q') hc {z | ‖(z : Fin (k + 1 + 1) → ℝ)‖ ≤ R} < ⊤ := by
  have h1 := sigCone_closedBall_one_lt_top hc hQ' hk
  rcases le_or_gt R 1 with hR | hR
  · exact lt_of_le_of_lt (measure_mono fun z hz => le_trans hz hR) h1
  · rw [sigCone_closedBall_eq hc (zero_lt_one.trans hR)]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h1

/-- **Gaussian integrability on the cone** (real place): if $0 \le \Phi(z) \le C e^{-a\|z\|^2}$ on $C^\circ$ with
$a > 0$, $C \ge 0$, then $\int_{C^\circ}\Phi\,d\sigma_C < \infty$. (Measurability of $\Phi$ is not needed.) -/
@[kb "weil1982" "§2.2 (convergence of the cone integral for Schwartz-Bruhat test functions) [unverified]"]
theorem lintegral_sigCone_gaussian_lt_top (hc : c ≠ 0) (hQ': gramDetR Q' ≠ 0) (hk : 1 ≤ k) {a C : ℝ} (ha : 0 < a)
    (hC : 0 ≤ C) (Φ : ConeT (coneForm c Q') → ℝ≥0∞)
    (hΦ : ∀ z, Φ z ≤ ENNReal.ofReal (C * Real.exp (-(a * ‖(z : Fin (k + 1 + 1) → ℝ)‖ ^ 2)))) :
    ∫⁻ z, Φ z ∂sigCone (Q' := Q') hc < ⊤ :=
  lintegral_gaussian_lt_top_abstract (sigCone (Q' := Q') hc) (fun z : ConeT (coneForm c Q') => ‖(z : Fin (k + 1 + 1) → ℝ)‖)
    (continuous_norm.comp continuous_subtype_val).measurable k (fun R hR => sigCone_closedBall_eq hc hR)
    (sigCone_closedBall_one_lt_top hc hQ' hk) ha hC Φ hΦ

/-- **Gaussian integrability, ambient version** (real place): for $\Phi$ on the ambient space $\mathbb R^{k+2}$ with
$\Phi(z) \le C e^{-a\|z\|^2}$ everywhere (or on $C^\circ$), $\int_{C^\circ}\Phi(z)\,d\sigma_C < \infty$. -/
theorem lintegral_sigCone_gaussian_ambient_lt_top (hc : c ≠ 0) (hQ': gramDetR Q' ≠ 0) (hk : 1 ≤ k) {a C : ℝ} (ha : 0 < a)
    (hC : 0 ≤ C) (Φ : (Fin (k + 1 + 1) → ℝ) → ℝ≥0∞)
    (hΦ : ∀ z : Fin (k + 1 + 1) → ℝ, Φ z ≤ ENNReal.ofReal (C * Real.exp (-(a * ‖z‖ ^ 2)))) :
    ∫⁻ z : ConeT (coneForm c Q'), Φ z ∂sigCone (Q' := Q') hc < ⊤ :=
  lintegral_sigCone_gaussian_lt_top hc hQ' hk ha hC (fun z => Φ z) fun z => hΦ z

end QuadFormsKB.Tamagawa.Measure.ConeReal


/-! ### The complex place -/

namespace QuadFormsKB.Tamagawa.Measure.ConeComplex

open QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.ArchVol
open QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.Measure.SphereLerayC
open QuadFormsKB.Tamagawa.Measure.OrbitalComplex QuadFormsKB.Tamagawa.Measure.ConeAlgebra
open QuadFormsKB.Tamagawa.Measure.ConeArchFinite

variable {k : ℕ} {c : ℂ} {Q' : QuadForm ℂ k}

/-- The radial density $|q|_{\mathbb C}^{k-1} = |q|^{2k}/|q|^2$ as the ofReal of a real number. -/
theorem rhoK_eq (q : ℂ) : rhoK k q = ENNReal.ofReal (‖q‖ ^ (2 * k) / ‖q‖ ^ 2) := by
  rw [rhoK, ← ENNReal.ofReal_coe_nnreal]
  congr 1

theorem rhoK_zero : rhoK k 0 = 0 := by simp [rhoK_eq]

/-- On $\delta \le |q| \le C$ the radial density $|q|_{\mathbb C}^{k-1}$ is at most $C^{2k}/\delta^2$. -/
theorem rhoK_le {q : ℂ} {C δ : ℝ} (hδ : 0 < δ) (hq : δ ≤ ‖q‖) (hqC : ‖q‖ ≤ C) :
    rhoK k q ≤ ENNReal.ofReal (C ^ (2 * k) / δ ^ 2) := by
  rw [rhoK_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  have hq0 : 0 < ‖q‖ := lt_of_lt_of_le hδ hq
  exact div_le_div₀ (pow_nonneg (hq0.le.trans hqC) _) (pow_le_pow_left₀ hq0.le hqC _)
    (pow_pos hδ 2) (pow_le_pow_left₀ hδ.le hq 2)

/-- If $q(1, y)$ lies in the sup-norm ball of radius $C$ and $|q| \ge \delta > 0$ then $|q| \le C$ and
$\|y\| \le C/\delta$. -/
theorem norm_le_of_coneVec {q : ℂ} {C δ : ℝ} {y : Fin (k + 1) → ℂ} (hδ : 0 < δ) (hq : δ ≤ ‖q‖)
    (h : ‖coneVec q y‖ ≤ C) : ‖q‖ ≤ C ∧ ‖y‖ ≤ C / δ := by
  have h0 : ‖q‖ ≤ C := by
    have := norm_le_pi_norm (coneVec q y) 0
    rw [coneVec_zero] at this
    exact this.trans h
  refine ⟨h0, ?_⟩
  have hC : 0 ≤ C / δ := div_nonneg ((norm_nonneg q).trans h0) hδ.le
  refine (pi_norm_le_iff_of_nonneg hC).mpr fun i => ?_
  have h1 := norm_le_pi_norm (coneVec q y) i.succ
  rw [coneVec_succ, norm_mul] at h1
  rw [le_div_iff₀ hδ]
  have h2 : ‖y i‖ * δ ≤ ‖y i‖ * ‖q‖ := mul_le_mul_of_nonneg_left hq (norm_nonneg _)
  nlinarith [h1.trans h]

/-- **Step (a): the cone measure of a cutoff region is finite** (complex place). For every $C$ and $\delta > 0$,
$\sigma_C\{z \in C^\circ : \|z\| \le C,\ |z_0| \ge \delta\} < \infty$ (from `lintegral_sigCone` and the finiteness of
the complex sphere measure of bounded sets, `nuC_ballS_lt_top`). -/
theorem sigCone_cutoff_lt_top (hc : c ≠ 0) (C δ : ℝ) (hδ : 0 < δ) :
    sigCone (Q' := Q') hc {z | ‖(z : Fin (k + 1 + 1) → ℂ)‖ ≤ C ∧ δ ≤ ‖(z : Fin (k + 1 + 1) → ℂ) 0‖} < ⊤ := by
  have := sigmaFinite_sigC (Q := QmC c Q') (neg_ne_zero.mpr hc) (by omega)
  set D : Set (ConeT (coneForm c Q')) :=
    {z | ‖(z : Fin (k + 1 + 1) → ℂ)‖ ≤ C ∧ δ ≤ ‖(z : Fin (k + 1 + 1) → ℂ) 0‖} with hD
  have hDm : MeasurableSet D :=
    (measurableSet_le (continuous_norm.comp continuous_subtype_val).measurable measurable_const).inter
      (measurableSet_le measurable_const
        (continuous_norm.comp ((continuous_apply 0).comp continuous_subtype_val)).measurable)
  have hF : Measurable (D.indicator (1 : ConeT (coneForm c Q') → ℝ≥0∞)) := measurable_one.indicator hDm
  rw [← lintegral_indicator_one hDm, lintegral_sigCone hc hF]
  set K : ℝ≥0∞ := sigC (QmC c Q') (-c) {y : SphC (QmC c Q') (-c) | ‖(y : Fin (k + 1) → ℂ)‖ ≤ C / δ} with hK
  have hKt : K < ⊤ := by
    have := nuC_ballS_lt_top (Q := QmC c Q') (neg_ne_zero.mpr hc) (by omega) (C / δ)
    rw [hK, sigC, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top this
  have hKm : MeasurableSet {y : SphC (QmC c Q') (-c) | ‖(y : Fin (k + 1) → ℂ)‖ ≤ C / δ} :=
    measurableSet_le (continuous_norm.comp continuous_subtype_val).measurable measurable_const
  have hpt : ∀ q : ℂ, rhoK k q * ∫⁻ y, D.indicator (1 : ConeT (coneForm c Q') → ℝ≥0∞)
        (coneMap hc (q, y)) ∂sigC (QmC c Q') (-c) ≤
      (Metric.closedBall (0 : ℂ) C).indicator (fun _ => ENNReal.ofReal (C ^ (2 * k) / δ ^ 2) * K) q := by
    intro q
    by_cases hq : q = 0
    · subst hq; rw [rhoK_zero, zero_mul]; exact zero_le
    have hmemD : ∀ y : SphC (QmC c Q') (-c), coneMap hc (q, y) ∈ D →
        δ ≤ ‖q‖ ∧ ‖q‖ ≤ C ∧ ‖(y : Fin (k + 1) → ℂ)‖ ≤ C / δ := by
      intro y hy
      have h1 : ‖(coneMap hc (q, y) : Fin (k + 1 + 1) → ℂ)‖ ≤ C := hy.1
      have h2 : δ ≤ ‖(coneMap hc (q, y) : Fin (k + 1 + 1) → ℂ) 0‖ := hy.2
      rw [coe_coneMap hc hq] at h1 h2
      rw [coneVec_zero] at h2
      exact ⟨h2, norm_le_of_coneVec hδ h2 h1⟩
    by_cases hgood : δ ≤ ‖q‖ ∧ ‖q‖ ≤ C
    · have hmem : q ∈ Metric.closedBall (0 : ℂ) C := by
        rw [mem_closedBall_zero_iff]; exact hgood.2
      rw [indicator_of_mem hmem]
      refine mul_le_mul' (rhoK_le hδ hgood.1 hgood.2) ?_
      calc ∫⁻ y, D.indicator (1 : ConeT (coneForm c Q') → ℝ≥0∞) (coneMap hc (q, y)) ∂sigC (QmC c Q') (-c)
          ≤ ∫⁻ y, {y : SphC (QmC c Q') (-c) | ‖(y : Fin (k + 1) → ℂ)‖ ≤ C / δ}.indicator
              (1 : SphC (QmC c Q') (-c) → ℝ≥0∞) y ∂sigC (QmC c Q') (-c) := by
            refine lintegral_mono fun y => ?_
            by_cases hy : coneMap hc (q, y) ∈ D
            · rw [indicator_of_mem hy, indicator_of_mem (show y ∈ _ from (hmemD y hy).2.2)]
              simp
            · rw [indicator_of_notMem hy]; exact zero_le
        _ = K := lintegral_indicator_one hKm
    · have h0 : ∀ y : SphC (QmC c Q') (-c),
          D.indicator (1 : ConeT (coneForm c Q') → ℝ≥0∞) (coneMap hc (q, y)) = 0 := fun y =>
        indicator_of_notMem (fun hy => hgood ⟨(hmemD y hy).1, (hmemD y hy).2.1⟩) _
      simp only [h0, lintegral_zero, mul_zero]; exact zero_le
  calc ∫⁻ q, rhoK k q * ∫⁻ y, D.indicator (1 : ConeT (coneForm c Q') → ℝ≥0∞) (coneMap hc (q, y))
        ∂sigC (QmC c Q') (-c)
      ≤ ∫⁻ q, (Metric.closedBall (0 : ℂ) C).indicator
          (fun _ => ENNReal.ofReal (C ^ (2 * k) / δ ^ 2) * K) q := lintegral_mono hpt
    _ = ENNReal.ofReal (C ^ (2 * k) / δ ^ 2) * K * volume (Metric.closedBall (0 : ℂ) C) :=
        lintegral_indicator_const Metric.isClosed_closedBall.measurableSet _
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKt) measure_closedBall_lt_top

/-- **Step (b): the cone measure of an annulus is finite** (complex place, $k \ge 1$): for $r > 0$,
$\sigma_C\{z \in C^\circ : r \le \|z\| \le R\} < \infty$ (compactness, `cone_cover`, $SO(Q)(\mathbb C)$-invariance
and `sigCone_cutoff_lt_top`). -/
theorem sigCone_annulus_lt_top (hc : c ≠ 0) (hQ' : gramDetC Q' ≠ 0) (hk : 1 ≤ k) {r R : ℝ} (hr : 0 < r) :
    sigCone (Q' := Q') hc {z | r ≤ ‖(z : Fin (k + 1 + 1) → ℂ)‖ ∧ ‖(z : Fin (k + 1 + 1) → ℂ)‖ ≤ R} < ⊤ := by
  classical
  have hNm : Measurable fun z : ConeT (coneForm c Q') => ‖(z : Fin (k + 1 + 1) → ℂ)‖ :=
    (continuous_norm.comp continuous_subtype_val).measurable
  have hpm : Measurable fun z : ConeT (coneForm c Q') => ‖(z : Fin (k + 1 + 1) → ℂ) 0‖ :=
    (continuous_norm.comp ((continuous_apply 0).comp continuous_subtype_val)).measurable
  have hcont : ∀ g : ArchSOC (coneForm c Q'), Continuous fun v : Fin (k + 1 + 1) → ℂ =>
      ArchSOC.mat _ g *ᵥ v := fun g => continuous_const.matrix_mulVec continuous_id
  refine measure_annulus_lt_top (sigCone (Q' := Q') hc) (fun z : ConeT (coneForm c Q') => ‖(z : Fin (k + 1 + 1) → ℂ)‖)
    (fun z : ConeT (coneForm c Q') => ‖(z : Fin (k + 1 + 1) → ℂ) 0‖) hNm hpm (s := {g | g ∈ coneList hc hQ'})
    (List.finite_toSet _) (fun g z => g • z) measurable_smul_cone
    (fun g _ => map_smul_sigCone hc hQ' hk g) (fun C δ hδ => sigCone_cutoff_lt_top hc C δ hδ) ?_ ?_ hr
  · intro r R hr
    obtain ⟨δ, hδ, h⟩ := exists_delta_of_compact
      (isCompact_annulus_zeroLocus (continuous_evalC (coneForm c Q')) r R)
      (coneList hc hQ').toFinset (fun g v => (ArchSOC.mat _ g *ᵥ v) 0)
      (fun g => (continuous_apply 0).comp (hcont g)) (by
        rintro v ⟨hv1, hv2, hv3⟩
        have hv0 : v ≠ 0 := by
          rintro rfl
          rw [norm_zero] at hv1
          linarith
        obtain ⟨g, hg, hg0⟩ := cone_cover hc hQ' (⟨v, hv3, hv0⟩ : ConeT (coneForm c Q'))
        exact ⟨g, List.mem_toFinset.mpr hg, hg0⟩)
    refine ⟨δ, hδ, fun z hz1 hz2 => ?_⟩
    obtain ⟨g, hg, hδg⟩ := h (z : Fin (k + 1 + 1) → ℂ) ⟨hz1, hz2, z.2.1⟩
    exact ⟨g, List.mem_toFinset.mp hg, hδg⟩
  · intro r R hr g _
    obtain ⟨C, hC⟩ := (isCompact_annulus_zeroLocus (continuous_evalC (coneForm c Q')) r R).exists_bound_of_continuousOn
      (hcont g).continuousOn
    exact ⟨C, fun z hz1 hz2 => hC (z : Fin (k + 1 + 1) → ℂ) ⟨hz1, hz2, z.2.1⟩⟩

theorem norm_coneScale {t : ℝ} (ht : 0 < t) (z : ConeT (coneForm c Q')) :
    ‖(coneScale (Q' := Q') (c := c) (a := (t : ℂ)) (Complex.ofReal_ne_zero.mpr ht.ne') z :
      Fin (k + 1 + 1) → ℂ)‖ = t * ‖(z : Fin (k + 1 + 1) → ℂ)‖ := by
  show ‖(t : ℂ) • (z : Fin (k + 1 + 1) → ℂ)‖ = _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]

theorem sigCone_preimage_coneScale (hc : c ≠ 0) {t : ℝ} (ht : 0 < t) {A : Set (ConeT (coneForm c Q'))}
    (hA : MeasurableSet A) :
    sigCone (Q' := Q') hc
        (coneScale (Q' := Q') (c := c) (a := (t : ℂ)) (Complex.ofReal_ne_zero.mpr ht.ne') ⁻¹' A) =
      ENNReal.ofReal ((t⁻¹) ^ (2 * k)) * sigCone hc A := by
  rw [← Measure.map_apply (measurable_coneScale (Complex.ofReal_ne_zero.mpr ht.ne')) hA,
    map_coneScale_sigCone hc (Complex.ofReal_ne_zero.mpr ht.ne'), Measure.smul_apply, smul_eq_mul,
    ← ENNReal.ofReal_coe_nnreal]
  congr 2
  push_cast
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]

/-- **Homogeneous bound for balls** (complex place): $\sigma_C(B_R) = R^{2k}\,\sigma_C(B_1)$ for $R > 0$, where
$B_R = \{z \in C^\circ : \|z\| \le R\}$ (sup norm); the exponent is $2k$ because $|a|_{\mathbb C} = |a|^2$. -/
@[kb "weil1982" "§2.2 (homogeneity of the Leray form on the cone, ball growth) [unverified]"]
theorem sigCone_closedBall_eq (hc : c ≠ 0) {R : ℝ} (hR : 0 < R) :
    sigCone (Q' := Q') hc {z | ‖(z : Fin (k + 1 + 1) → ℂ)‖ ≤ R} =
      ENNReal.ofReal (R ^ (2 * k)) * sigCone (Q' := Q') hc {z | ‖(z : Fin (k + 1 + 1) → ℂ)‖ ≤ 1} :=
  measure_ball_scale (sigCone (Q' := Q') hc) (fun z : ConeT (coneForm c Q') => ‖(z : Fin (k + 1 + 1) → ℂ)‖)
    (fun t ht => coneScale (Q' := Q') (c := c) (a := (t : ℂ)) (Complex.ofReal_ne_zero.mpr ht.ne'))
    (2 * k) (fun t ht z => norm_coneScale (Q' := Q') (c := c) ht z)
    (fun t ht A hA => sigCone_preimage_coneScale hc ht hA)
    (continuous_norm.comp continuous_subtype_val).measurable hR

/-- **The unit ball of the cone has finite measure** (complex place, $k \ge 1$), by the dyadic decomposition into
the annuli $2^{-j}\{1/2 \le \|z\| \le 1\}$ and homogeneity of degree $2k \ge 1$. -/
theorem sigCone_closedBall_one_lt_top (hc : c ≠ 0) (hQ' : gramDetC Q' ≠ 0) (hk : 1 ≤ k) :
    sigCone (Q' := Q') hc {z | ‖(z : Fin (k + 1 + 1) → ℂ)‖ ≤ 1} < ⊤ :=
  measure_ball_one_lt_top (sigCone (Q' := Q') hc) (fun z : ConeT (coneForm c Q') => ‖(z : Fin (k + 1 + 1) → ℂ)‖)
    (fun t ht => coneScale (Q' := Q') (c := c) (a := (t : ℂ)) (Complex.ofReal_ne_zero.mpr ht.ne'))
    (2 * k) (fun t ht z => norm_coneScale (Q' := Q') (c := c) ht z)
    (fun t ht A hA => sigCone_preimage_coneScale hc ht hA)
    (continuous_norm.comp continuous_subtype_val).measurable (by omega)
    (fun z => norm_pos_iff.mpr z.2.2) (sigCone_annulus_lt_top hc hQ' hk (by norm_num))

/-- **Finiteness of the cone measure on bounded sets** (complex place): for $c \ne 0$, $Q'$ nondegenerate in
$k \ge 1$ variables and every $R$, $\sigma_C\{z \in C^\circ : \|z\| \le R\} < \infty$ (sup norm). -/
@[kb "weil1982" "§2.2 (local finiteness of the Leray measure of the cone) [unverified]"]
theorem sigCone_closedBall_lt_top (hc : c ≠ 0) (hQ' : gramDetC Q' ≠ 0) (hk : 1 ≤ k) (R : ℝ) :
    sigCone (Q' := Q') hc {z | ‖(z : Fin (k + 1 + 1) → ℂ)‖ ≤ R} < ⊤ := by
  have h1 := sigCone_closedBall_one_lt_top hc hQ' hk
  rcases le_or_gt R 1 with hR | hR
  · exact lt_of_le_of_lt (measure_mono fun z hz => le_trans hz hR) h1
  · rw [sigCone_closedBall_eq hc (zero_lt_one.trans hR)]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h1

/-- **Gaussian integrability on the cone** (complex place): if $0 \le \Phi(z) \le C e^{-a\|z\|^2}$ on $C^\circ$ with
$a > 0$, $C \ge 0$, then $\int_{C^\circ}\Phi\,d\sigma_C < \infty$. (Measurability of $\Phi$ is not needed.) -/
@[kb "weil1982" "§2.2 (convergence of the cone integral for Schwartz-Bruhat test functions) [unverified]"]
theorem lintegral_sigCone_gaussian_lt_top (hc : c ≠ 0) (hQ' : gramDetC Q' ≠ 0) (hk : 1 ≤ k) {a C : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (Φ : ConeT (coneForm c Q') → ℝ≥0∞)
    (hΦ : ∀ z, Φ z ≤ ENNReal.ofReal (C * Real.exp (-(a * ‖(z : Fin (k + 1 + 1) → ℂ)‖ ^ 2)))) :
    ∫⁻ z, Φ z ∂sigCone (Q' := Q') hc < ⊤ :=
  lintegral_gaussian_lt_top_abstract (sigCone (Q' := Q') hc) (fun z : ConeT (coneForm c Q') => ‖(z : Fin (k + 1 + 1) → ℂ)‖)
    (continuous_norm.comp continuous_subtype_val).measurable (2 * k)
    (fun R hR => sigCone_closedBall_eq hc hR) (sigCone_closedBall_one_lt_top hc hQ' hk) ha hC Φ hΦ

/-- **Gaussian integrability, ambient version** (complex place): for $\Phi$ on the ambient space $\mathbb C^{k+2}$ with
$\Phi(z) \le C e^{-a\|z\|^2}$ everywhere (or on $C^\circ$), $\int_{C^\circ}\Phi(z)\,d\sigma_C < \infty$. -/
theorem lintegral_sigCone_gaussian_ambient_lt_top (hc : c ≠ 0) (hQ' : gramDetC Q' ≠ 0) (hk : 1 ≤ k)
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (Φ : (Fin (k + 1 + 1) → ℂ) → ℝ≥0∞)
    (hΦ : ∀ z : Fin (k + 1 + 1) → ℂ, Φ z ≤ ENNReal.ofReal (C * Real.exp (-(a * ‖z‖ ^ 2)))) :
    ∫⁻ z : ConeT (coneForm c Q'), Φ z ∂sigCone (Q' := Q') hc < ⊤ :=
  lintegral_sigCone_gaussian_lt_top hc hQ' hk ha hC (fun z => Φ z) fun z => hΦ z

end QuadFormsKB.Tamagawa.Measure.ConeComplex
