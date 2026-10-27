/-
# The $T(\pi^2)$ relations for the Eisenstein coefficients over $F$

**Setting.** $F$ totally real, $Q_0$ a totally positive definite form over $\mathcal O_F$ in $n = 2k$ variables, $k \ge 3$, $E_Q$ = `eisQ Q₀ k`,
$a_\mu(E_Q)$ = `qCoeff (eisQ Q₀ k) (oBasis F) (realVec μ)` its $\mu$-th Fourier coefficient
($\mu \in \mathfrak d^{-1}$), $\pi$ a prime element of $\mathcal O_F$ with $\pi \nmid 2\det H$ ($H$ the Hessian of
$Q_0$), $q = N(\pi)$, $\chi_\pi$ = `Nbr.chiPi` and $\lambda_\pi = q^{n-2} + \chi_\pi q^{k-1} + 1$ (`heckeEigen`).

**Main theorem** (`eisHeckeRel_eisQ`, and `eisHeckeRel_eisQ_of_pid` for $\mathcal O_F$ a PID): `EisHeckeRel Q₀ (eisQ Q₀ k)`, i.e.
$$a_{\pi^2\mu}(E_Q) = \lambda_\pi\,a_\mu(E_Q)\qquad(\mu \in \mathfrak d^{-1}\ \text{a } \pi\text{-unit}),$$
with $m_E = 1$. This was a named input of the Hecke–Kneser argument; it is now a theorem. The proof is prime by prime:

* $\mu \in \mathfrak d^{-1}\setminus\mathcal O_F$: **the singular series vanishes** (`SingularNF.singSeries_eq_zero_of_not_int`): every
  truncation $S_c(\mu)$ with $c \in \mathfrak d$ is $0$, since $(Q(r) - \mu)/c \in \mathfrak d^{-1}$ would force $Q(r) - \mu \in c\,\mathfrak d^{-1} \subseteq \mathcal O_F$.
  So $a_\mu = a_{\pi^2\mu} = 0$ ($\pi^2\mu \notin \mathcal O_F$ too, `mem_int_of_sq_mul`).
* $\mu = \nu \in \mathcal O_F$ not totally positive: $a_\nu = a_{\pi^2\nu} = 0$ (the archimedean factor `lipCoeff` vanishes; $\pi^2$ is
  totally positive).
* $\nu \in \mathcal O_F$ totally positive: by the coefficient formula for $E_Q$, $a_\nu = |d_F|^{-(n-1)/2}\,\beta_\infty(\nu)\prod_\mathfrak p\beta_\mathfrak p(\nu)$
  (`eisQ_coeff_eq_discr_mul_aENF`). Along the square class (`Siegel.aENF_mul_sq_uncond`, Hanke 2004 pp. 369–370):
  - $\beta_\infty(\pi^2\nu) = N(\pi)^{2(k-1)}\beta_\infty(\nu)$ ($\beta_w(t) \propto t^{k-1}$ at each real place);
  - $\beta_\mathfrak q(\pi^2\nu) = \beta_\mathfrak q(\nu)$ for $\mathfrak q \ne (\pi)$ ($\pi$ is a $\mathfrak q$-unit; `Siegel.localDensityNF_mul_sq_of_not_mem`);
  - at $\mathfrak p = (\pi)$, (5.8) gives $q^{n-2}\beta_\pi(\pi^2\nu)/\beta_\pi(\nu) = C\,q^{n-2} + 1 - C$, and Table 2 at a good prime
    with $\pi \nmid \nu$, $n$ even, gives $C = X/(X - \chi_\pi)$, $X = q^{k-1}$ (`NF.table2_even_unit_of_unimodular`). With
    $\chi_\pi^2 = 1$: $C(X^2 - 1) + 1 = X^2 + \chi_\pi X + 1 = \lambda_\pi$ (`sqShiftFactorNF_good_unit`).

Over $\mathbb Q$, $n = 4$, this is the classical computation of `Siegel/GenusEisenstein/EisCoeff.lean`.

**Also:** `exists_isThetaLevelF` — every $Q_0$ has a nonzero theta level, $\mathfrak N = (2\det H\cdot N(\mathfrak d))$.

Sources: Siegel, Ann. Math. 36 (1935), 38 (1937) [unverified]; Hanke 2004, (5.3), (5.8), Table 2, pp. 368–370 (with the
corrected constant $|d_F|^{-(n-1)/2}$); Shimura, Duke Math. J. 45 (1978), §3 [unverified]; Eichler 1952 [unverified].
-/
import QuadFormsKB.HilbertModular.EisensteinSiegelNF
import QuadFormsKB.HilbertModular.SiegelHecke
import QuadFormsKB.Tamagawa.LocalIdentity
import QuadFormsKB.LocalDensity.NFLocalGeneral
import QuadFormsKB.LocalDensity.NFDepth

open Complex NumberField Filter Topology IsDedekindDomain Matrix
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

/-! ### The singular series vanishes off $\mathcal O_F$ -/

namespace QuadFormsKB.SiegelWeil.SingularNF

open QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

/-- $\mathfrak d\cdot\mathfrak d^{-1} \subseteq \mathcal O_F$: for $\delta \in \mathfrak d$ and $w \in \mathfrak d^{-1}$, $\delta w \in \mathcal O_F$. -/
lemma exists_int_of_mem_dif {δ : 𝓞 F} (hδ : δ ∈ dif F) {w : F} (hw : w ∈ invDifferent F) :
    ∃ b : 𝓞 F, ιO b = ιO δ * w := by
  have hd0 : ((dif F : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact dif_ne_bot
  rw [invDifferent_eq_inv_dif, FractionalIdeal.mem_inv_iff hd0] at hw
  have := hw (ιO δ) ((FractionalIdeal.mem_coeIdeal _).mpr ⟨δ, hδ, rfl⟩)
  obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).mp this
  exact ⟨b, by rw [hb, mul_comm]⟩

/-- **The truncated singular series vanishes at non-integers** ($c \in \mathfrak d$, $c \ne 0$, $\mu \in \mathfrak d^{-1}\setminus\mathcal O_F$):
$S_c(\mu) = N(c)^{-n}\sum_r\sum_de(\operatorname{Tr}\tilde d(Q(\tilde r) - \mu)/c) = 0$, because $(Q(\tilde r) - \mu)/c \in \mathfrak d^{-1}$ would give
$Q(\tilde r) - \mu \in c\,\mathfrak d^{-1} \subseteq \mathcal O_F$. -/
theorem ssTrunc_eq_zero_of_not_int (Q : QuadForm (𝓞 F) n) {c : 𝓞 F} (hc : c ≠ 0) (hcd : c ∈ dif F)
    {μ : F} (hμ : μ ∈ invDifferent F) (hμO : ¬ ∃ b : 𝓞 F, ιO b = μ) : ssTrunc Q c μ = 0 := by
  classical
  haveI := finite_quot_span hc
  letI : Fintype (𝓞 F ⧸ Ideal.span {c}) := Fintype.ofFinite _
  have hc' := algebraMap_ne_zero hc
  unfold ssTrunc gAvg
  simp only [finsum_eq_sum_of_fintype, mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm : ∀ (r : Fin n → 𝓞 F ⧸ Ideal.span {c}) (d : 𝓞 F ⧸ Ideal.span {c}),
      eTr (ιO (Quotient.out d) / ιO c * ιO (Q.eval (liftV r))) *
        eTr (-(μ * (ιO (Quotient.out d) / ιO c))) =
      eTr (ιO (Quotient.out d) * (ιO (Q.eval (liftV r)) - μ) / ιO c) := by
    intro r d
    rw [← eTr_add]
    congr 1
    field_simp; ring
  simp_rw [hterm]
  have hsum : ∀ r : Fin n → 𝓞 F ⧸ Ideal.span {c},
      ∑ d : 𝓞 F ⧸ Ideal.span {c}, eTr (ιO (Quotient.out d) * (ιO (Q.eval (liftV r)) - μ) / ιO c) = 0 := by
    intro r
    have hy : ιO (Q.eval (liftV r)) - μ ∈ invDifferent F :=
      Submodule.sub_mem _ (algebraMap_mem_invDifferent _) hμ
    have h := sum_eTr_div hc hy
    rw [finsum_eq_sum_of_fintype] at h
    rw [h]
    split_ifs with hmem
    swap; · rfl
    exfalso
    obtain ⟨b, hb⟩ := exists_int_of_mem_dif hcd hmem
    apply hμO
    refine ⟨Q.eval (liftV r) - b, ?_⟩
    rw [map_sub, hb]
    field_simp
    ring
  simp_rw [hsum]
  simp

/-- **The singular series vanishes off $\mathcal O_F$** ($\mu \in \mathfrak d^{-1}\setminus\mathcal O_F$, the series absolutely convergent):
$\mathfrak S_Q(\mu) = 0$. It is the limit of the truncations $S_{X!}(\mu)$ (dominated convergence), which vanish once $N(\mathfrak d) \mid X!$
(`ssTrunc_eq_zero_of_not_int`). Equivalently: the local density at a prime where $\mu$ is not integral is $0$. -/
@[kb "siegel1935" "the singular series vanishes at non-integral μ ∈ 𝔡⁻¹ [unverified]"]
theorem singSeries_eq_zero_of_not_int (Q : QuadForm (𝓞 F) n) {μ : F} (hμ : μ ∈ invDifferent F)
    (hμO : ¬ ∃ b : 𝓞 F, ιO b = μ) (hsum : Summable fun x => ‖ssFun Q μ x‖) : singSeries Q μ = 0 := by
  set f := ssFun Q μ
  have hlim : Tendsto (fun X : ℕ => ∑' x, (Set.range (jmap (cX F X))).indicator f x) atTop
      (𝓝 (singSeries Q μ)) := by
    refine tendsto_tsum_of_dominated_convergence hsum (fun x => ?_) (Eventually.of_forall fun X x => ?_)
    · refine tendsto_const_nhds.congr' ?_
      set u := Quotient.out x
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {den u}))
      set M := Ideal.absNorm (Ideal.span {den u})
      have hM : 0 < M := Nat.pos_of_ne_zero (by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact span_ne_bot (den_ne_zero u))
      filter_upwards [eventually_ge_atTop M] with X hX
      obtain ⟨k, hk⟩ := Nat.dvd_factorial hM hX
      have hden : IsDen (cX F X) u := by
        have := isDen_mul (isDen_mul (isDen_den u) t) (k : 𝓞 F)
        rwa [show den u * t * (k : 𝓞 F) = cX F X by rw [cX, hk, Nat.cast_mul, ← ht]; ring] at this
      have hmem : x ∈ Set.range (jmap (cX F X)) := by
        have := mk_mem_range_jmap (cX_ne_zero X) hden
        rwa [QuotientAddGroup.out_eq'] at this
      simp only [Set.indicator_of_mem hmem]
      rfl
    · by_cases h : x ∈ Set.range (jmap (cX F X))
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, norm_zero]; exact norm_nonneg _
  have hzero : ∀ᶠ X in atTop, ∑' x, (Set.range (jmap (cX F X))).indicator f x = 0 := by
    set D := Ideal.absNorm (dif F)
    have hD : 0 < D := Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact dif_ne_bot)
    filter_upwards [eventually_ge_atTop D] with X hX
    rw [← ssTrunc_eq_tsum_indicator Q (cX_ne_zero X) hμ]
    refine ssTrunc_eq_zero_of_not_int Q (cX_ne_zero X) ?_ hμ hμO
    obtain ⟨k, hk⟩ := Nat.dvd_factorial hD hX
    rw [cX, hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hzero.mono fun X hX => hX.symm))

end QuadFormsKB.SiegelWeil.SingularNF

/-! ### The local factor at $\pi$: $q^{n-2}\beta_\pi(\pi^2\nu)/\beta_\pi(\nu) = \lambda_\pi$ -/

namespace QuadFormsKB.HilbertModular

open QuadFormsKB.Lattices QuadFormsKB.Lattices.Nbr QuadFormsKB.LocalDensity

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

section Local

variable {π : 𝓞 F} (hπ : Prime π)
include hπ

/-- A prime ideal containing the prime element $\pi$ is $(\pi)$. -/
lemma eq_hosOf_of_mem {v : HeightOneSpectrum (𝓞 F)} (h : π ∈ v.asIdeal) : v = hosOf hπ := by
  have hle : Ideal.span {π} ≤ v.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr h
  have := (isMaximal_span hπ).eq_of_le v.isPrime.ne_top hle
  exact HeightOneSpectrum.ext this.symm

/-- $\mathrm{ord}_{(\pi)}(\pi) = 1$. -/
lemma ordNF_hosOf_self : QuadFormsKB.Siegel.ordNF (hosOf hπ) π = 1 := by
  obtain ⟨h1, h2⟩ := QuadFormsKB.Siegel.mem_pow_ordNF (hosOf hπ) hπ.ne_zero
  rw [hosOf_asIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1 h2
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · apply h2
    rw [show QuadFormsKB.Siegel.ordNF (hosOf hπ) π = 0 by omega]; simp
  · apply hπ.not_isUnit
    obtain ⟨t, ht⟩ := (pow_dvd_pow π (show 2 ≤ QuadFormsKB.Siegel.ordNF (hosOf hπ) π by omega)).trans h1
    refine IsUnit.of_mul_eq_one (b := t) ?_
    have h0 := hπ.ne_zero
    apply mul_left_cancel₀ h0
    rw [mul_one]
    calc π * (π * t) = π ^ 2 * t := by ring
      _ = π := ht.symm

/-- **The local factor at a good prime** ($n = 2k \ge 4$, $\pi \nmid 2\det H$, $\pi \nmid \nu$): with $q = N(\pi)$, $\chi_\pi$ = `chiPi`,
$$F_\pi(\nu, 1) = q^{n-2}\frac{\beta_\pi(\pi^2\nu)}{\beta_\pi(\nu)} = q^{n-2} + \chi_\pi q^{k-1} + 1.$$
Proof: (5.8) gives $F_\pi = C\,q^{n-2} + 1 - C$ (`Siegel.sqShiftFactorNF_eq_localConst`), Table 2 gives $C = X/(X - \chi_\pi)$, $X = q^{k-1}$
(`NF.table2_even_unit_of_unimodular`), and $\chi_\pi^2 = 1$ (`DVR.chiDisc_sq`). -/
@[kb "hanke2004" "(5.8) + Table 2, p. 370: the T(𝔭²) eigenvalue of the local density at a good prime"]
theorem sqShiftFactorNF_good_unit {Q₀ : QuadForm (𝓞 F) n} (hQnd : Q₀.Nondegenerate) {k : ℕ} (hn : n = 2 * k)
    (hk : 2 ≤ k) (h2 : ¬ π ∣ 2) (hdet : ¬ π ∣ Q₀.hessian.det) {ν : 𝓞 F} (hν0 : ν ≠ 0) (hνπ : ¬ π ∣ ν) :
    QuadFormsKB.Siegel.sqShiftFactorNF Q₀ ν (hosOf hπ) 1 =
      (nm π : ℝ) ^ (n - 2) + (chiPi Q₀ hπ : ℝ) * (nm π : ℝ) ^ (n / 2 - 1) + 1 := by
  set v := hosOf hπ
  have h2' : (2 : 𝓞 F) ∉ v.asIdeal := two_not_mem hπ h2
  have hdet' : Q₀.hessian.det ∉ v.asIdeal := det_not_mem hπ hdet
  have hN : NF.NotDvdLevel v Q₀ := (NF.notDvdLevel_iff v Q₀ h2').mpr hdet'
  have hνv : ν ∉ v.asIdeal := by rw [hosOf_asIdeal, Ideal.mem_span_singleton]; exact hνπ
  have hloc := NF.isLocallyRepresentedAt_of_unimodular v Q₀ h2' hN (by omega) ν
  have hlev : NF.levelExp v Q₀ = 0 := (DVR.levelExp_eq_zero_iff ⟨0, hN⟩).mpr hN
  have hst : NF.IsPStable v Q₀ ν :=
    NF.isPStable_of_mem_nondyadic v Q₀ hQnd h2' (by rw [hlev, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top) hloc
  rw [QuadFormsKB.Siegel.sqShiftFactorNF_eq_localConst Q₀ hQnd (by omega) v ν hν0 hst 1,
    NF.table2_even_unit_of_unimodular v Q₀ h2' hN (by omega) ⟨k, by omega⟩ ν hνv]
  have hχ : (DVR.chiDisc (NF.Qp v Q₀) : ℝ) ^ 2 = 1 :=
    DVR.chiDisc_sq (NF.irreducible_π v) (NF.π_not_dvd_two v h2') (NF.π_not_dvd_det_of_notDvdLevel v Q₀ h2' hN)
  have hq : (Ideal.absNorm v.asIdeal : ℝ) = (nm π : ℝ) := rfl
  change _ = _ + (DVR.chiDisc (NF.Qp v Q₀) : ℝ) * _ + 1
  rw [hq]
  generalize (DVR.chiDisc (NF.Qp v Q₀) : ℝ) = χ at hχ ⊢
  have hn1 : (n - 2) / 2 = k - 1 := by omega
  have hn2 : n / 2 - 1 = k - 1 := by omega
  have hn3 : (n - 2) * 1 = n - 2 := by omega
  have hn4 : n - 2 = 2 * (k - 1) := by omega
  rw [hn1, hn2, hn3, hn4]
  set X : ℝ := (nm π : ℝ) ^ (k - 1)
  have hq2 : (2 : ℝ) ≤ nm π := by
    exact QuadFormsKB.Siegel.two_le_normP_real v
  have hX : 2 ≤ X := le_trans hq2 (le_self_pow₀ (by linarith) (by omega))
  have hχ1 : χ ≤ 1 := by nlinarith
  have hXχ : X - χ ≠ 0 := by intro h; linarith
  have hXX : (nm π : ℝ) ^ (2 * (k - 1)) = X ^ 2 := by rw [← pow_mul, mul_comm]
  rw [hXX]
  field_simp
  linear_combination X * hχ

end Local

/-! ### `aENF` along $\pi^2$ -/

local notation "ιO" => algebraMap (𝓞 F) F

/-- **Hanke's local product along $\pi^2$ at a good prime** ($F$ totally real, $n = 2k \ge 4$, $\pi \nmid 2\det H$, $\pi \nmid \nu$, $\nu$
nonnegative at every real place):
$$\mathrm{aENF}(\nu\pi^2) = \lambda_\pi\,\mathrm{aENF}(\nu),\qquad \lambda_\pi = q^{n-2} + \chi_\pi q^{k-1} + 1.$$
Prime by prime (`Siegel.aENF_mul_sq_uncond` with $S = \{(\pi)\}$): $\beta_\infty(\nu\pi^2) = N(\pi)^{n-2}\beta_\infty(\nu)$,
$\beta_\mathfrak q(\nu\pi^2) = \beta_\mathfrak q(\nu)$ at $\mathfrak q \ne (\pi)$ (a unit square), and `sqShiftFactorNF_good_unit` at $(\pi)$. -/
@[kb "hanke2004" "Thm 5.4 at one good prime, n even: a_E(νπ²) = (q^{n-2} + χ q^{k-1} + 1) a_E(ν)"]
theorem aENF_mul_pi_sq [IsTotallyReal F] {Q₀ : QuadForm (𝓞 F) n} (hQnd : Q₀.Nondegenerate) {k : ℕ}
    (hn : n = 2 * k) (hk : 2 ≤ k) {π : 𝓞 F} (hπ : Prime π) (h2 : ¬ π ∣ 2) (hdet : ¬ π ∣ Q₀.hessian.det)
    {ν : 𝓞 F} (hν0 : ν ≠ 0) (hνπ : ¬ π ∣ ν)
    (hT : ∀ w : QuadFormsKB.Siegel.RealPlace F, 0 ≤ QuadFormsKB.Siegel.realEmb w ν) :
    QuadFormsKB.Siegel.aENF Q₀ (ν * π ^ 2) = QuadFormsKB.Siegel.aENF Q₀ ν *
      ((nm π : ℝ) ^ (n - 2) + (chiPi Q₀ hπ : ℝ) * (nm π : ℝ) ^ (n / 2 - 1) + 1) := by
  set v := hosOf hπ
  have h2' : (2 : 𝓞 F) ∉ v.asIdeal := two_not_mem hπ h2
  have hN : NF.NotDvdLevel v Q₀ := (NF.notDvdLevel_iff v Q₀ h2').mpr (det_not_mem hπ hdet)
  have hloc := NF.isLocallyRepresentedAt_of_unimodular v Q₀ h2' hN (by omega) ν
  rw [QuadFormsKB.Siegel.aENF_mul_sq_uncond hQnd (by omega) hν0 hT hπ.ne_zero (S := {v})
    (fun w hw hm => hw (Finset.mem_singleton.mpr (eq_hosOf_of_mem hπ hm)))
    (fun w hw => by
      rw [Finset.mem_singleton.mp hw]
      exact (QuadFormsKB.Siegel.localDensityNF_pos v Q₀ hQnd hν0 hloc).ne'),
    Finset.prod_singleton, ordNF_hosOf_self hπ, sqShiftFactorNF_good_unit hπ hQnd hn hk h2 hdet hν0 hνπ]

/-! ### `EisHeckeRel` for $E_Q$ -/

section Rel

variable [IsTotallyReal F] {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ} (hn : n = 2 * k)
  {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥) (hfree : GenusFree (formF Q₀) stdLat)

lemma realEmb_sq_mul_pos_iff {π : 𝓞 F} (hπ : π ≠ 0) (μ : F) (v : InfinitePlace F) :
    0 < realEmb F v ((π : F) ^ 2 * μ) ↔ 0 < realEmb F v μ := by
  have hπ' : realEmb F v (π : F) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (realEmb_injective F v)]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr hπ
  rw [map_mul, map_pow]
  exact ⟨fun h => pos_of_mul_pos_right h (by positivity), fun h => by positivity⟩

lemma lipCoeff_sq_mul {π : 𝓞 F} (hπ : π ≠ 0) {μ : F} (h : ¬ ∀ v, 0 < realEmb F v μ) :
    lipCoeff k (realVec ((π : F) ^ 2 * μ)) = 0 := by
  rw [lipCoeff, ite_eq_right_iff]
  intro h'
  exact absurd (fun v => (realEmb_sq_mul_pos_iff hπ μ v).mp (h' v)) h

lemma lipCoeff_of_not_pos {μ : F} (h : ¬ ∀ v, 0 < realEmb F v μ) : lipCoeff k (realVec μ) = 0 := by
  rw [lipCoeff, ite_eq_right_iff]
  exact fun h' => absurd h' h

lemma not_dvd_of_isUnitAt {π ν : 𝓞 F} (hu : IsUnitAt π (ιO ν)) : ¬ π ∣ ν := by
  rintro ⟨t, rfl⟩
  obtain ⟨x, y, hx, -, hxy⟩ := hu
  apply hx
  refine ⟨t * y, FaithfulSMul.algebraMap_injective (𝓞 F) F ?_⟩
  have hxy' : ιO (π * t) * ιO y = ιO x := hxy
  rw [← hxy', map_mul, map_mul, map_mul]; ring

lemma ne_zero_of_isUnitAt {π : 𝓞 F} {μ : F} (hu : IsUnitAt π μ) : μ ≠ 0 := by
  rintro rfl
  obtain ⟨x, y, hx, -, hxy⟩ := hu
  apply hx
  rw [zero_mul, eq_comm, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)] at hxy
  rw [hxy]; exact dvd_zero π

/-- A $\pi$-unit $\nu$ with $\pi^2\nu \in \mathcal O_F$ is in $\mathcal O_F$ (any Dedekind $\mathcal O_F$; `mem_int_of_sq_mul` without
the PID hypothesis): $(y) \mid (\pi)^2(x)$ and $(y) + (\pi) = (1)$ give $(y) \mid (x)$. -/
lemma mem_int_of_sq_mul' {π : 𝓞 F} (hπ : Prime π) {ν : F} (hν : IsUnitAt π ν) {ν' : 𝓞 F}
    (h : (ν' : F) = (π : F) ^ 2 * ν) : ∃ t : 𝓞 F, (t : F) = ν := by
  obtain ⟨x, y, hx, hy, hxy⟩ := hν
  have hy0 : (y : F) ≠ 0 := by
    intro h0; apply hy
    rw [show y = 0 from FaithfulSMul.algebraMap_injective (𝓞 F) F (by rw [map_zero]; exact h0)]
    exact dvd_zero π
  have e : ν' * y = π ^ 2 * x := by
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    have h1 : algebraMap (𝓞 F) F ν' = algebraMap (𝓞 F) F π ^ 2 * ν := h
    have h2 : ν * algebraMap (𝓞 F) F y = algebraMap (𝓞 F) F x := hxy
    rw [map_mul, map_mul, map_pow, h1, mul_assoc, h2]
  have hcop : IsCoprime (Ideal.span {y}) (Ideal.span {π}) := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    have heq := (isMaximal_span hπ).eq_of_le hne (le_sup_right (a := Ideal.span {y}))
    apply hy
    rw [← Ideal.mem_span_singleton, heq]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self y)
  have hdvd : Ideal.span {y} ∣ Ideal.span {π} ^ 2 * Ideal.span {x} := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_dvd_span_singleton_iff_dvd]
    exact ⟨ν', by rw [← e]; ring⟩
  have := (hcop.pow_right (n := 2)).dvd_of_dvd_mul_left hdvd
  rw [Ideal.span_singleton_dvd_span_singleton_iff_dvd] at this
  obtain ⟨t, rfl⟩ := this
  refine ⟨t, ?_⟩
  apply mul_left_cancel₀ hy0
  have h2 : ν * algebraMap (𝓞 F) F y = algebraMap (𝓞 F) F (y * t) := hxy
  change algebraMap (𝓞 F) F y * algebraMap (𝓞 F) F t = algebraMap (𝓞 F) F y * ν
  rw [mul_comm (algebraMap (𝓞 F) F y) ν, h2, map_mul]

include hQ hn hlev h𝔑 hfree in
/-- **The $T(\pi^2)$ relations for the coefficients of $E_Q$** ($F$ totally real, $Q_0$ totally positive definite, $n = 2k \ge 6$, theta
level $\mathfrak N$, free genus): `EisHeckeRel Q₀ (eisQ Q₀ k)` with $m_E = 1$, i.e. for every prime $\pi \nmid 2\det H$ and every
$\pi$-unit $\mu \in \mathfrak d^{-1}$,
$$a_{\pi^2\mu}(E_Q) = (q^{n-2} + \chi_\pi q^{k-1} + 1)\,a_\mu(E_Q).$$
Proof prime by prime (the coefficient formula for $E_Q$, `aENF_mul_pi_sq`; $a_\mu = 0$ for $\mu \notin \mathcal O_F$
or $\mu \not\gg 0$). -/
@[kb "siegel1935" "T(𝔭²) relations for the Eisenstein coefficients over F [unverified]; cassels1978 App. B, §5, p. 388 (Eichler's description of Hecke operators)"]
theorem eisHeckeRel_eisQ (hk : 3 ≤ k) : EisHeckeRel Q₀ (eisQ Q₀ k) := by
  classical
  refine ⟨1, one_pos, fun π hπ _ h2 hdet m hu => ?_⟩
  have hπ0 := hπ.ne_zero
  have hQ' := isTotPosGram_Q₀ hQ
  have hQnd : Q₀.Nondegenerate := det_hessian_ne_zero hQ'
  obtain ⟨m', hm'⟩ := exists_dualElt_mul (π ^ 2) m
  have hm'' : (π : F) ^ 2 * oDual m = oDual m' := by rw [oDual, oDual, hm']; push_cast; rfl
  have hμ0 := ne_zero_of_isUnitAt hu
  have hm0 : m ≠ 0 := by rintro rfl; exact hμ0 oDual_zero
  have hm'0 : m' ≠ 0 := by
    rintro rfl
    rw [oDual_zero] at hm''
    exact mul_ne_zero (pow_ne_zero 2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr hπ0))
      hμ0 hm''
  change qCoeff (eisQ Q₀ k) (oBasis F) (realVec ((π : F) ^ 2 * oDual m)) =
    heckeEigen Q₀ hπ * qCoeff (eisQ Q₀ k) (oBasis F) (realVec (oDual m))
  by_cases hint : ∃ ν : 𝓞 F, ιO ν = oDual m
  · obtain ⟨ν, hν⟩ := hint
    have hνπ : ¬ π ∣ ν := not_dvd_of_isUnitAt (by rw [hν]; exact hu)
    have hν0 : ν ≠ 0 := by rintro rfl; exact hμ0 (by rw [← oDual, ← hν, map_zero])
    have he : (π : F) ^ 2 * oDual m = ιO (ν * π ^ 2) := by rw [← hν, map_mul, map_pow]; ring
    by_cases hpos : ∀ v, 0 < realEmb F v (ιO ν)
    · have hpos' : ∀ v, 0 < realEmb F v (ιO (ν * π ^ 2)) := fun v => by
        rw [← he, realEmb_sq_mul_pos_iff hπ0, ← hν]; exact hpos v
      rw [he, ← hν, eisQ_coeff_eq_discr_mul_aENF hQ hn hlev h𝔑 hfree hk hpos',
        eisQ_coeff_eq_discr_mul_aENF hQ hn hlev h𝔑 hfree hk hpos,
        aENF_mul_pi_sq hQnd hn (by omega) hπ h2 hdet hν0 hνπ
          (fun w => by obtain ⟨v, h⟩ := w; rw [siegel_realEmb_eq]; exact (hpos v).le), heckeEigen]
      push_cast
      ring
    · rw [hm'', ← dualVec_oBasis, ← dualVec_oBasis, qCoeff_eisQ hQ hn hlev h𝔑 hfree hk hm'0,
        qCoeff_eisQ hQ hn hlev h𝔑 hfree hk hm0, eisQCoeff, eisQCoeff, ← hm'', lipCoeff_sq_mul hπ0
          (by rw [← hν]; exact hpos), ← hν, lipCoeff_of_not_pos hpos]
      simp
  · have hsum := fun μ => (eisQ_qexp hQ hn hlev h𝔑 hfree hk (fun _ => UpperHalfPlane.I)).2.1 μ
    have hint' : ¬ ∃ ν : 𝓞 F, ιO ν = oDual m' := by
      rintro ⟨ν', hν'⟩
      exact hint (mem_int_of_sq_mul' hπ hu (hν'.trans hm''.symm))
    rw [hm'', ← dualVec_oBasis, ← dualVec_oBasis, qCoeff_eisQ hQ hn hlev h𝔑 hfree hk hm'0,
      qCoeff_eisQ hQ hn hlev h𝔑 hfree hk hm0, eisQCoeff, eisQCoeff,
      SiegelWeil.SingularNF.singSeries_eq_zero_of_not_int Q₀ (oDual_mem m) hint (hsum _),
      SiegelWeil.SingularNF.singSeries_eq_zero_of_not_int Q₀ (oDual_mem m') hint' (hsum _)]
    simp

end Rel

/-- **The $T(\pi^2)$ relations for $E_Q$, class number one** ($\mathcal O_F$ a PID; no freeness hypothesis): `eisHeckeRel_eisQ` with the
genus free by `genusFree_of_isPrincipalIdealRing`. -/
@[kb "siegel1935" "T(𝔭²) relations for the Eisenstein coefficients over F, h_F = 1 [unverified]"]
theorem eisHeckeRel_eisQ_of_pid [IsTotallyReal F] [IsPrincipalIdealRing (𝓞 F)] {Q₀ : QuadForm (𝓞 F) n}
    (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ} (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑)
    (h𝔑 : 𝔑 ≠ ⊥) (hk : 3 ≤ k) : EisHeckeRel Q₀ (eisQ Q₀ k) :=
  eisHeckeRel_eisQ hQ hn hlev h𝔑 (genusFree_of_isPrincipalIdealRing _ _) hk

/-! ### Every form has a theta level -/

/-- **Every totally positive form over $\mathcal O_F$ has a nonzero theta level**: $\mathfrak N = (2\det H\cdot N(\mathfrak d))$ is one
(`IsThetaLevelF`). Indeed $2\det H\cdot Q^\#(y) = y^{\mathsf T}\operatorname{adj}(H)\,y$ (`qDual_eq`), and for $\delta \in \mathfrak d$ and
$y \in (\mathfrak d^{-1})^n$, $\delta\,y^{\mathsf T}\operatorname{adj}(H)\,y = \sum_{i,j}(\delta y_i)\operatorname{adj}(H)_{ij}y_j \in \mathcal O_F\cdot\mathfrak d^{-1} = \mathfrak d^{-1}$. -/
@[kb "shimura1973" "§2: a theta level exists (𝔑 = 2 det H · N(𝔡))"]
theorem exists_isThetaLevelF [IsTotallyReal F] {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) :
    ∃ 𝔑 : Ideal (𝓞 F), 𝔑 ≠ ⊥ ∧ IsThetaLevelF Q 𝔑 := by
  classical
  set δ : 𝓞 F := ((Ideal.absNorm (SiegelWeil.SingularNF.dif F) : ℕ) : 𝓞 F)
  have hδ : δ ∈ SiegelWeil.SingularNF.dif F := Ideal.absNorm_mem _
  have hδ0 : δ ≠ 0 := by
    rw [Ne, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff]; exact SiegelWeil.SingularNF.dif_ne_bot
  have hdet := det_hessian_ne_zero hQ
  have hc0 : 2 * Q.hessian.det * δ ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hdet) hδ0
  refine ⟨Ideal.span {2 * Q.hessian.det * δ}, by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hc0, ?_⟩
  intro ν hν y hy
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hν
  have hdetF : (hessF Q).det = ιO Q.hessian.det := by
    rw [hessF, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hdetF0 : (hessF Q).det ≠ 0 := hessF_det_ne_zero hQ
  set A : Matrix (Fin n) (Fin n) F := (Q.hessian.adjugate).map ιO
  have hadj : (hessF Q).adjugate = A := by
    rw [hessF, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]; rfl
  have key : ιO (t * (2 * Q.hessian.det * δ)) * qDual Q y = ιO t * (ιO δ * (y ⬝ᵥ A *ᵥ y)) := by
    rw [qDual_eq hQ, Matrix.inv_def, hadj, Ring.inverse_eq_inv', smul_mulVec, dotProduct_smul, smul_eq_mul]
    simp only [map_mul, map_ofNat]
    rw [← hdetF]
    field_simp
  rw [key]
  refine algebraMap_mul_mem_invDifferent t ?_
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨b, hb⟩ := SiegelWeil.SingularNF.exists_int_of_mem_dif hδ (hy i)
  have e : ιO δ * (y i * (A i j * y j)) = ιO (b * Q.hessian.adjugate i j) * y j := by
    rw [map_mul, hb]; simp only [A, Matrix.map_apply]; ring
  rw [e]
  exact algebraMap_mul_mem_invDifferent _ (hy j)

end QuadFormsKB.HilbertModular
