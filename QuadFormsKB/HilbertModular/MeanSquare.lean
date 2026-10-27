/-
# Hilbert modular forms VIII: Parseval, the mean-square bound and Hecke's bound

Setting of `FourierInversion.lean` ($f$ holomorphic on $\mathbb{H}^\iota$, periodic for $\Lambda = \bigoplus_j\mathbb{Z}b_j$, coefficients
$a_\nu$ = `qCoeff`, $\nu$ in the dual lattice $\{\nu_n\}$). $N(y) = \prod_vy_v$.

* **Parseval at height $y$** (`hasSum_sq_coeff`):
  $\sum_n|c_{\nu_n}(y)|^2 = \int_{(0,1]^J}|f(x(t) + iy)|^2\,dt$, i.e. $\sum_\nu|a_\nu|^2e^{-4\pi\langle\nu, y\rangle} = \operatorname{covol}(\Lambda)^{-1}\int_{\mathbb{R}^\iota/\Lambda}|f(x+iy)|^2dx$
  (Mathlib's `UnitAddTorus.hasSum_sq_mFourierCoeff`). Hence $\sum_\nu|a_\nu|^2e^{-4\pi\langle\nu,y\rangle} \le \sup_x|f(x+iy)|^2$
  (`tsum_sq_coeff_le`).
* **Mean square** (`tsum_sq_qCoeff_le`, mirroring Mathlib's level-one
  `ModularFormClass.hasSum_norm_sq_qExpansion_coeff_mul_exp`): if $|f(z)| \le C\,N(\operatorname{Im}z)^{-k/2}$ on $\mathbb{H}^\iota$ then
  $$\sum_\nu|a_\nu|^2e^{-4\pi\langle\nu, y\rangle} \le C^2N(y)^{-k}\qquad(y > 0).$$
* **Partial sums** (`sum_sq_qCoeff_le`, cf. Mathlib's `CuspFormClass.exists_sum_range_norm_sq_qExpansion_coeff_le_of_mem_strictPeriods`):
  for $X > 0$ and any finite set of $\nu$ with $\sum_v\nu_v \le X$ (for $F$: $\operatorname{Tr}\nu \le X$),
  $\sum|a_\nu|^2 \le e^{4\pi}C^2X^{dk}$, $d = |\iota|$ (take $y = X^{-1}\mathbf 1$).
* **Hecke's bound** (`norm_qCoeff_le_hecke`): for $\nu \gg 0$, $|a_\nu| \le C\,e^{2\pi d}\,N(\nu)^{k/2}$ (take $y_v = 1/\nu_v$).

The hypothesis $|f(z)| \le C\,N(\operatorname{Im}z)^{-k/2}$ (`hbound`) holds for Hilbert cusp forms of parallel weight $k$
($f(z)N(\operatorname{Im}z)^{k/2}$ is $\Gamma$-invariant and bounded). This is proved in `CuspBound.lean` (C5b, reduction theory and
Siegel sets at finitely many cusps: `exists_norm_le_of_mem_cuspFormSpace`, `exists_norm_le_of_mem_cuspFormChar`), which also
states the corollaries of this file for $f \in S_k(\Gamma_0(\mathfrak N), \chi)$ without growth hypothesis
(`sum_sq_qCoeff_le_trace_of_cuspFormChar`, `norm_qCoeff_le_hecke_norm_of_cuspFormChar`).

Sources: Hecke's estimate, e.g. Garrett, *Holomorphic Hilbert Modular Forms* (1990), Ch. 1 [unverified]; Freitag,
*Hilbert Modular Forms* (1990), Ch. I [unverified].
-/
import QuadFormsKB.HilbertModular.KoecherBounded

open MeasureTheory Set Filter Topology Complex UpperHalfPlane UnitAddTorus
open scoped Real nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

variable {ι : Type*} [Fintype ι] {J : Type*} [Fintype J]

section Parseval

/-- The Haar probability measure on $\mathbb{R}/\mathbb{Z}$, as in Mathlib's torus Fourier theory. -/
noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- **Parseval at height $y$**: $\sum_n|c_{\nu_n}(y)|^2 = \int_{(0,1]^J}|f(x(t) + iy)|^2\,dt$. -/
@[kb "garrett1990" "Ch. 1, Fourier expansions of Hilbert modular forms [unverified]"]
theorem hasSum_sq_coeff {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)} (hf : Continuous f)
    (hper : IsLatticePeriodic f b) {y : ι → ℝ} (hy : ∀ v, 0 < y v) :
    HasSum (fun n => ‖coeff f b (dualVec b n) y‖ ^ 2)
      (∫ t in unitCube J, ‖f (ptXY (b.equivFun.symm t) y)‖ ^ 2) := by
  set g := torusFunC hf hper hy
  have h := hasSum_sq_mFourierCoeff (g.toLp 2 volume ℂ)
  simp only [mFourierCoeff_toLp] at h
  have hint : ∫ t, ‖(g.toLp 2 volume ℂ) t‖ ^ 2 = ∫ t, ‖g t‖ ^ 2 :=
    integral_congr_ae ((ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume g).mono fun t ht => by
      simp only [ht])
  rw [hint, integral_preimage (fun t => ‖g t‖ ^ 2) 0] at h
  have hs : {x : J → ℝ | ∀ i, x i ∈ Ioc ((0 : J → ℝ) i) ((0 : J → ℝ) i + 1)} = unitCube J := by
    ext t; simp [unitCube]
  rw [hs] at h
  have hc : ∀ n, mFourierCoeff g n = coeff f b (dualVec b n) y := fun n =>
    (coeff_eq_mFourierCoeff hper hy n).symm
  simp only [hc] at h
  convert h using 1
  refine setIntegral_congr_fun measurableSet_unitCube fun t _ => ?_
  change _ = ‖torusFun f b y (torusMk t)‖ ^ 2
  rw [torusFun_mk hper hy]

end Parseval

/-- **Bessel/Parseval bound**: if $|f(x + iy)| \le B$ for all $x$, then $\sum_n|c_{\nu_n}(y)|^2 \le B^2$. -/
theorem tsum_sq_coeff_le {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)} (hf : Continuous f)
    (hper : IsLatticePeriodic f b) {y : ι → ℝ} (hy : ∀ v, 0 < y v) {B : ℝ}
    (hB : ∀ x, ‖f (ptXY x y)‖ ≤ B) :
    Summable (fun n => ‖coeff f b (dualVec b n) y‖ ^ 2) ∧
      ∑' n, ‖coeff f b (dualVec b n) y‖ ^ 2 ≤ B ^ 2 := by
  have h := hasSum_sq_coeff hf hper hy
  refine ⟨h.summable, h.tsum_eq ▸ ?_⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hle : ∫ t in unitCube J, ‖f (ptXY (b.equivFun.symm t) y)‖ ^ 2 ≤
      ∫ t in unitCube J, B ^ 2 := by
    refine setIntegral_mono_on ?_ (integrableOn_const (by rw [volume_unitCube]; simp))
      measurableSet_unitCube fun t _ => pow_le_pow_left₀ (norm_nonneg _) (hB _) 2
    exact (((continuous_ptXY hy hf).comp
      (b.equivFun.symm : (J → ℝ) →ₗ[ℝ] (ι → ℝ)).continuous_of_finiteDimensional).norm.pow
        2).continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)
        |>.mono_set unitCube_subset
  refine hle.trans (le_of_eq ?_)
  rw [setIntegral_const, measureReal_def, volume_unitCube]
  simp

/-- $|c_\nu(y)|^2 = |a_\nu|^2e^{-4\pi\langle\nu, y\rangle}$. -/
lemma sq_norm_coeff [DecidableEq ι] {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)}
    {ν : ι → ℝ} (hf : IsHolomorphic f) (hper : IsLatticePeriodic f b) (hν : IsDual b ν)
    {y : ι → ℝ} (hy : ∀ v, 0 < y v) :
    ‖coeff f b ν y‖ ^ 2 = ‖qCoeff f b ν‖ ^ 2 * Real.exp (-4 * π * pair ν y) := by
  rw [coeff_eq_qCoeff hf hper hν hy, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- **The mean-square bound** (Parseval). If $|f(z)| \le C\,N(\operatorname{Im}z)^{-k/2}$ on $\mathbb{H}^\iota$ ($N(y) = \prod_vy_v$), then for
every $y > 0$ the series $\sum_n|a_{\nu_n}|^2e^{-4\pi\langle\nu_n, y\rangle}$ converges and is at most $C^2N(y)^{-k}$.

Parameters: `hf` (holomorphy), `hper` (periodicity), `k` (the weight, real), `C`, `hbound` (the growth bound), `y`, `hy`. -/
@[kb "garrett1990" "Ch. 1, Hecke's estimate [unverified]"]
theorem tsum_sq_qCoeff_le [DecidableEq ι] {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)}
    (hf : IsHolomorphic f) (hper : IsLatticePeriodic f b) {k C : ℝ}
    (hbound : ∀ z : ι → ℍ, ‖f z‖ ≤ C * (∏ v, (z v).im) ^ (-k / 2)) {y : ι → ℝ}
    (hy : ∀ v, 0 < y v) :
    Summable (fun n => ‖qCoeff f b (dualVec b n)‖ ^ 2 * Real.exp (-4 * π * pair (dualVec b n) y)) ∧
      ∑' n, ‖qCoeff f b (dualVec b n)‖ ^ 2 * Real.exp (-4 * π * pair (dualVec b n) y) ≤
        C ^ 2 * (∏ v, y v) ^ (-k) := by
  have hN : 0 < ∏ v, y v := Finset.prod_pos fun v _ => hy v
  have hB : ∀ x, ‖f (ptXY x y)‖ ≤ C * (∏ v, y v) ^ (-k / 2) := by
    intro x
    have := hbound (ptXY x y)
    have him : ∀ v, (ptXY x y v).im = y v := fun v => congrFun (imVec_ptXY hy) v
    simpa only [him] using this
  obtain ⟨hs, hle⟩ := tsum_sq_coeff_le hf.1 hper hy hB
  simp only [sq_norm_coeff hf hper (isDual_dualVec b _) hy] at hs hle
  refine ⟨hs, hle.trans (le_of_eq ?_)⟩
  rw [mul_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
  norm_num

/-- **Partial sums of $|a_\nu|^2$** (cf. Mathlib's
`CuspFormClass.exists_sum_range_norm_sq_qExpansion_coeff_le_of_mem_strictPeriods`). Under the growth bound of
`tsum_sq_qCoeff_le`, for $X > 0$ and every finite set $S$ of $n$ with $\sum_v(\nu_n)_v \le X$ (for $F$: $\operatorname{Tr}\nu \le X$),
$\sum_{n\in S}|a_{\nu_n}|^2 \le e^{4\pi}C^2X^{dk}$, $d = |\iota|$. -/
@[kb "garrett1990" "Ch. 1, Hecke's estimate [unverified]"]
theorem sum_sq_qCoeff_le [DecidableEq ι] {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)}
    (hf : IsHolomorphic f) (hper : IsLatticePeriodic f b) {k C : ℝ}
    (hbound : ∀ z : ι → ℍ, ‖f z‖ ≤ C * (∏ v, (z v).im) ^ (-k / 2)) {X : ℝ} (hX : 0 < X)
    (S : Finset (J → ℤ)) (hS : ∀ n ∈ S, pair (dualVec b n) 1 ≤ X) :
    ∑ n ∈ S, ‖qCoeff f b (dualVec b n)‖ ^ 2 ≤
      Real.exp (4 * π) * C ^ 2 * X ^ ((Fintype.card ι : ℝ) * k) := by
  set y : ι → ℝ := fun _ => X⁻¹
  have hy : ∀ v, 0 < y v := fun _ => inv_pos.mpr hX
  obtain ⟨hs, hle⟩ := tsum_sq_qCoeff_le hf hper hbound hy
  have hN : (∏ v, y v) ^ (-k) = X ^ ((Fintype.card ι : ℝ) * k) := by
    rw [Finset.prod_const, Finset.card_univ, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      Real.inv_rpow hX.le, ← Real.rpow_neg hX.le]
    congr 1; ring
  have hterm : ∀ n ∈ S, ‖qCoeff f b (dualVec b n)‖ ^ 2 ≤ Real.exp (4 * π) *
      (‖qCoeff f b (dualVec b n)‖ ^ 2 * Real.exp (-4 * π * pair (dualVec b n) y)) := by
    intro n hn
    have hp : pair (dualVec b n) y = X⁻¹ * pair (dualVec b n) 1 := by
      rw [show y = X⁻¹ • (1 : ι → ℝ) by funext v; simp [y], pair_smul]
    have h1 : X⁻¹ * pair (dualVec b n) 1 ≤ 1 := by
      rw [inv_mul_le_iff₀ hX, mul_one]; exact hS n hn
    rw [mul_left_comm, ← Real.exp_add]
    refine le_mul_of_one_le_right (by positivity) (Real.one_le_exp_iff.mpr ?_)
    rw [hp]; nlinarith [Real.pi_pos]
  calc ∑ n ∈ S, ‖qCoeff f b (dualVec b n)‖ ^ 2
      ≤ ∑ n ∈ S, Real.exp (4 * π) * (‖qCoeff f b (dualVec b n)‖ ^ 2 *
          Real.exp (-4 * π * pair (dualVec b n) y)) := Finset.sum_le_sum hterm
    _ = Real.exp (4 * π) * ∑ n ∈ S, ‖qCoeff f b (dualVec b n)‖ ^ 2 *
          Real.exp (-4 * π * pair (dualVec b n) y) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (4 * π) * (C ^ 2 * (∏ v, y v) ^ (-k)) := by
        refine mul_le_mul_of_nonneg_left ((hs.sum_le_tsum S fun n _ => by positivity).trans hle)
          (by positivity)
    _ = Real.exp (4 * π) * C ^ 2 * X ^ ((Fintype.card ι : ℝ) * k) := by rw [hN, mul_assoc]

/-- **Hecke's bound** $|a_\nu| \le C\,e^{2\pi d}N(\nu)^{k/2}$ for totally positive $\nu$ ($N(\nu) = \prod_v\nu_v$, $d = |\iota|$),
under the growth bound $|f(z)| \le C\,N(\operatorname{Im}z)^{-k/2}$. -/
@[kb "garrett1990" "Ch. 1, Hecke's estimate [unverified]"]
theorem norm_qCoeff_le_hecke [DecidableEq ι] {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)}
    (hf : IsHolomorphic f) (hper : IsLatticePeriodic f b) {k C : ℝ}
    (hbound : ∀ z : ι → ℍ, ‖f z‖ ≤ C * (∏ v, (z v).im) ^ (-k / 2)) (n : J → ℤ)
    (hpos : ∀ v, 0 < dualVec b n v) :
    ‖qCoeff f b (dualVec b n)‖ ≤
      C * Real.exp (2 * π * Fintype.card ι) * (∏ v, dualVec b n v) ^ (k / 2) := by
  set ν := dualVec b n
  set y : ι → ℝ := fun v => (ν v)⁻¹
  have hy : ∀ v, 0 < y v := fun v => inv_pos.mpr (hpos v)
  obtain ⟨hs, hle⟩ := tsum_sq_qCoeff_le hf hper hbound hy
  have h1 := (hs.le_tsum n fun m _ => by positivity).trans hle
  have hp : pair ν y = Fintype.card ι := by
    simp only [pair, y, mul_inv_cancel₀ (hpos _).ne', Finset.sum_const, Finset.card_univ]
    simp
  have hNν : 0 < ∏ v, ν v := Finset.prod_pos fun v _ => hpos v
  have hNy : (∏ v, y v) ^ (-k) = (∏ v, ν v) ^ k := by
    rw [Finset.prod_inv_distrib, Real.inv_rpow hNν.le, ← Real.rpow_neg hNν.le, neg_neg]
  rw [hp, hNy] at h1
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (hbound (ptXY 0 1))
    exact nonneg_of_mul_nonneg_left this (Real.rpow_pos_of_pos
      (Finset.prod_pos fun v _ => (ptXY 0 1 v).im_pos) _)
  have h2 : ‖qCoeff f b ν‖ ^ 2 ≤
      (C * Real.exp (2 * π * Fintype.card ι) * (∏ v, ν v) ^ (k / 2)) ^ 2 := by
    have he : Real.exp (-4 * π * Fintype.card ι) * Real.exp (2 * π * Fintype.card ι) ^ 2 = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; simp; ring_nf
    have hr : ((∏ v, ν v) ^ (k / 2)) ^ 2 = (∏ v, ν v) ^ k := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNν.le]; norm_num
    calc ‖qCoeff f b ν‖ ^ 2 = ‖qCoeff f b ν‖ ^ 2 * Real.exp (-4 * π * Fintype.card ι) *
          Real.exp (2 * π * Fintype.card ι) ^ 2 := by rw [mul_assoc, he, mul_one]
      _ ≤ C ^ 2 * (∏ v, ν v) ^ k * Real.exp (2 * π * Fintype.card ι) ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by rw [mul_pow, mul_pow, hr]; ring
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero |>.mp h2

/-! ### Over a totally real field -/

section TotallyReal

open NumberField

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-- **Mean square over $F$.** Let $f$ be holomorphic on $\mathbb{H}^d$, periodic for a fractional ideal $I$, with
$|f(z)| \le C\,N(\operatorname{Im}z)^{-k/2}$. For $X > 0$ and a finite set $S$ of $\nu \in I^\vee$ (written $\nu = $ `dualElt I n`) with
$\operatorname{Tr}_{F/\mathbb{Q}}\nu \le X$: $\sum_{\nu\in S}|a_\nu|^2 \le e^{4\pi}C^2X^{dk}$. -/
theorem sum_sq_qCoeff_le_trace (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) {f : (InfinitePlace F → ℍ) → ℂ}
    (hf : IsHolomorphic f) (hper : IsLatticePeriodic f (koecherBasis I)) {k C : ℝ}
    (hbound : ∀ z : InfinitePlace F → ℍ, ‖f z‖ ≤ C * (∏ v, (z v).im) ^ (-k / 2)) {X : ℝ}
    (hX : 0 < X) (S : Finset (Fin (Module.finrank ℚ F) → ℤ))
    (hS : ∀ n ∈ S, ((Algebra.trace ℚ F (QuadFormsKB.Analysis.dualElt I n) : ℚ) : ℝ) ≤ X) :
    ∑ n ∈ S, ‖qCoeff f (koecherBasis I) (realVec (QuadFormsKB.Analysis.dualElt I n))‖ ^ 2 ≤
      Real.exp (4 * π) * C ^ 2 * X ^ ((Fintype.card (InfinitePlace F) : ℝ) * k) := by
  classical
  have h := sum_sq_qCoeff_le hf hper hbound hX S fun n hn => by
    rw [dualVec_koecherBasis, pair]
    refine le_trans (le_of_eq ?_) (hS n hn)
    rw [← sum_realEmb]
    simp [realVec]
  simpa only [dualVec_koecherBasis] using h

/-- **Hecke's bound over $F$**: under the hypotheses of `sum_sq_qCoeff_le_trace`, for totally positive $\nu \in I^\vee$,
$|a_\nu| \le C\,e^{2\pi d}\,N_{F/\mathbb{Q}}(\nu)^{k/2}$. -/
@[kb "garrett1990" "Ch. 1, Hecke's estimate [unverified]"]
theorem norm_qCoeff_le_hecke_norm (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) {f : (InfinitePlace F → ℍ) → ℂ}
    (hf : IsHolomorphic f) (hper : IsLatticePeriodic f (koecherBasis I)) {k C : ℝ}
    (hbound : ∀ z : InfinitePlace F → ℍ, ‖f z‖ ≤ C * (∏ v, (z v).im) ^ (-k / 2))
    (n : Fin (Module.finrank ℚ F) → ℤ)
    (hpos : ∀ v, 0 < realEmb F v (QuadFormsKB.Analysis.dualElt I n)) :
    ‖qCoeff f (koecherBasis I) (realVec (QuadFormsKB.Analysis.dualElt I n))‖ ≤
      C * Real.exp (2 * π * Fintype.card (InfinitePlace F)) *
        |((Algebra.norm ℚ (QuadFormsKB.Analysis.dualElt I n) : ℚ) : ℝ)| ^ (k / 2) := by
  classical
  have h := norm_qCoeff_le_hecke hf hper hbound n (by
    intro v; rw [dualVec_koecherBasis]; exact hpos v)
  rw [dualVec_koecherBasis] at h
  convert h using 3
  rw [← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hm : v.mult = 1 := by simp [InfinitePlace.mult, IsTotallyReal.isReal v]
  rw [hm, pow_one, ← abs_realEmb, abs_of_pos (hpos v)]
  rfl

end TotallyReal

end QuadFormsKB.HilbertModular
