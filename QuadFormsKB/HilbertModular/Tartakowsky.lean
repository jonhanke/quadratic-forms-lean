/-
# Tartakowsky's theorem over a totally real field, even rank $n \ge 6$, via Hecke's bound

**Setting.** $F$ totally real with $\mathcal O_F$ a PID ($h_F = 1$; $F = \mathbb Q$ included), $Q_0$ a totally positive definite quadratic
form over $\mathcal O_F$ in $n = 2k \ge 6$ variables, $r_{Q_0}(\nu) = \#\{x \in \mathcal O_F^n : Q_0(x) = \nu\}$ (`repNumF`),
$a_E(\nu) = \beta_\infty(\nu)\prod_\mathfrak p\beta_\mathfrak p(\nu)$ (`Siegel.aENF`), $D_F = |d_F|^{-(n-1)/2}$.

**The single-lattice decomposition** (no genus average and no Siegel formula needed): $\theta_{Q_0} - E_Q$ is a cusp form of
weight $k$ (`thetaLatt_sub_eisQ_mem_cuspFormChar`), the $\nu$-th coefficient of $\theta_{Q_0}$ is $r_{Q_0}(\nu)$
(`qCoeff_thetaQ`) and that of $E_Q$ is $D_F\,a_E(\nu)$ (`eisQ_coeff_eq_discr_mul_aENF_of_pid`). Hecke's bound for Hilbert cusp
forms (`norm_qCoeff_le_hecke_norm_of_cuspFormChar`) then gives

* `exists_abs_repNumF_sub_le` (**Hecke's bound for $r_{Q_0} - D_Fa_E$**, unconditional): there is $C$ with
  $|r_{Q_0}(\nu) - D_F\,a_E(\nu)| \le C\,N(\nu)^{k/2}$ for every totally positive $\nu \in \mathcal O_F$.

Since $a_E(\nu)$ grows like $N(\nu)^{k-1}$ on locally represented $\nu$ and $k - 1 > k/2$ for $k \ge 3$, this decides representability
for $N(\nu)$ large (`represents_of_aENF_ge`). The constant is not explicit (Hecke's bound comes from a supremum over
$\mathbb H^d$).

Sources: Hecke, Analytische Arithmetik der positiven quadratischen Formen (1940) [unverified]; Garrett, *Holomorphic Hilbert
Modular Forms* (1990), Ch. 1 (Hecke's estimate) [unverified]; Tartakowsky (1929) [unverified]; Hanke 2004, Thm 6.4, p. 382.
-/
import QuadFormsKB.HilbertModular.SiegelFormulaNF
import QuadFormsKB.HilbertModular.CuspBound
import QuadFormsKB.HilbertModular.EisensteinSiegelNF
import QuadFormsKB.Siegel.NFDyadicGoodUncond
import QuadFormsKB.Siegel.StableSquareClasses

open Complex NumberField Filter IsDedekindDomain
open scoped Real nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.HilbertModular

open QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [IsPrincipalIdealRing (𝓞 F)] {n : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F
local notation "I1" => (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)

/-- $\theta_{\mathcal O_F^n} = \theta_{Q_0}$ (the lattice theta series of the standard lattice is the form theta series). -/
lemma thetaLatt_intVec (Q₀ : QuadForm (𝓞 F) n) :
    thetaLatt (formF Q₀) (intVec : Submodule (𝓞 F) (Fin n → F)) = thetaQ Q₀ := by
  have h := thetaLatt_latOf (formF Q₀) 1 (isIntegral_latOf_one Q₀)
  rw [gramZ_one] at h
  rwa [latOf_one] at h

/-- **Hecke's bound for $r_{Q_0}(\nu) - D_F\,a_E(\nu)$** ($F$ totally real, $h_F = 1$, $Q_0$ totally positive definite in $n = 2k \ge 6$
variables; unconditional): there is $C \ge 0$ such that for every totally positive $\nu \in \mathcal O_F$
$$\big|r_{Q_0}(\nu) - |d_F|^{-(n-1)/2}\,a_E(\nu)\big| \le C\,|N_{F/\mathbb Q}(\nu)|^{k/2}.$$
$C$ is not explicit. -/
@[kb "garrett1990" "Ch. 1, Hecke's estimate, applied to θ_Q − E_Q over F [unverified]"]
theorem exists_abs_repNumF_sub_le {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ}
    (hn : n = 2 * k) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : 𝓞 F, (∀ v, 0 < realEmb F v (ιO ν)) →
      |(repNumF Q₀ ν : ℝ) - (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (n - 1) * QuadFormsKB.Siegel.aENF Q₀ ν| ≤
        C * |((Algebra.norm ℚ (ιO ν) : ℚ) : ℝ)| ^ ((k : ℝ) / 2) := by
  classical
  have hpos := isTotPosGram_Q₀ hQ
  obtain ⟨𝔑, h𝔑, hlev⟩ := exists_isThetaLevelF hpos
  have hfree := genusFree_of_isPrincipalIdealRing (formF Q₀) (stdLat (F := F) (n := n))
  have hc := thetaLatt_sub_eisQ_mem_cuspFormChar hQ hn hlev h𝔑 hk hfree stdLat
    (SameGenus.refl (formF Q₀) _)
  rw [show (stdLat (F := F) (n := n)).1 = intVec from rfl, thetaLatt_intVec] at hc
  obtain ⟨C₀, hC₀⟩ := norm_qCoeff_le_hecke_norm_of_cuspFormChar h𝔑 hc
  set C : ℝ := max C₀ 0 * Real.exp (2 * π * Fintype.card (InfinitePlace F))
  refine ⟨C, by positivity, fun ν hν => ?_⟩
  have hθ := thetaQ_mem_modularFormChar' hpos hn hlev h𝔑
  have hE := eisQ_mem_modularFormChar hQ hn hlev h𝔑 hk hfree
  have hθper : IsLatticePeriodic (thetaQ Q₀) (koecherBasis I1) := isLatticePeriodic_of_mem_modularFormChar hθ
  have hEper : IsLatticePeriodic (eisQ Q₀ k) (koecherBasis I1) := isLatticePeriodic_of_mem_modularFormChar hE
  have h1 := hC₀ (mOf ν) (by rw [dualElt_mOf]; exact hν)
  rw [← dualVec_koecherBasis, qCoeff_sub hθ.1.2.1 hE.1.2.1 hθper hEper, dualVec_koecherBasis,
    qCoeff_thetaQ hpos hθper, thetaCoeffQ_mOf, dualElt_mOf,
    eisQ_coeff_eq_discr_mul_aENF_of_pid hQ hn hlev h𝔑 hk hν] at h1
  have e : ((repNumF Q₀ ν : ℂ) - (((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (n - 1) *
      QuadFormsKB.Siegel.aENF Q₀ ν : ℝ) : ℂ)) =
      (((repNumF Q₀ ν : ℝ) - (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (n - 1) * QuadFormsKB.Siegel.aENF Q₀ ν : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs] at h1
  refine h1.trans ?_
  have hN : 0 ≤ |((Algebra.norm ℚ (ιO ν) : ℚ) : ℝ)| ^ ((k : ℝ) / 2) := by positivity
  have hk' : ((k : ℤ) : ℝ) / 2 = (k : ℝ) / 2 := by push_cast; rfl
  have he : 0 ≤ Real.exp (2 * π * Fintype.card (InfinitePlace F)) := (Real.exp_pos _).le
  rw [hk']
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) he) hN

end QuadFormsKB.HilbertModular

/-! ### The main term $a_E(\nu) \gg N(\nu)^{k-1}$ on locally represented $\nu$ -/

namespace QuadFormsKB.Siegel

open LocalDensity NFEuler

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

local notation "N𝔭" v => (Ideal.absNorm (HeightOneSpectrum.asIdeal v) : ℝ)

/-- **Input (local, per bad prime): a gap at $0$ for the local density** at $\mathfrak p$. There is $c_\mathfrak p > 0$ such that every
$m \ne 0$ with $\beta_\mathfrak p(m) > 0$ (i.e. $m$ locally represented at $\mathfrak p$, `NF.IsLocallyRepresentedAt`) has
$\beta_\mathfrak p(m) \ge c_\mathfrak p$.

This is the local core of Hanke 2004, Thm 5.7(c) for $n \ge 5$ (every $\mathfrak p$ is isotropic): with $m = \varpi^{2\nu}T'$, $T'$ bad-reduced,
(5.11) gives $\beta_\mathfrak p(m) \ge C'_\mathfrak p(T')\beta_\mathfrak p(T') > 0$, and both factors take finitely many values on bad-reduced $T'$
(local constancy, `NF.localDensity_congr`; cf. `finite_badFactorNF_image`). It is used only at the finitely many $\mathfrak p \mid 2\det H$;
at the other primes `localDensityNF_good_ge` gives the explicit bound $\beta_\mathfrak p(m) \ge (1 - N\mathfrak p^{-2})^3$. **Proved** for
$n \ge 5$ at every prime (`localDensityGapNF_of_five_le`, `HilbertModular/TartakowskyUncond.lean`; DVR core `DVR.exists_localDensity_gap`).

Fields:
- `exists_le`: there is $c > 0$ with $c \le \beta_\mathfrak p(m)$ for every $m \ne 0$ such that $0 < \beta_\mathfrak p(m)$. -/
@[kb "hanke2004" "Thm 5.7(c), p. 373 (local factor at p | 2 det H, n ≥ 5; via (5.11) and B_T finite)"]
structure LocalDensityGapNF (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) : Prop where
  exists_le : ∃ c : ℝ, 0 < c ∧ ∀ m : 𝓞 F, m ≠ 0 → 0 < NF.localDensity v Q m → c ≤ NF.localDensity v Q m

/-- $|\chi_D| \le 1$: the quadratic character takes the values $0, \pm1$. -/
lemma chiDisc_cases (v : HeightOneSpectrum (𝓞 F)) (Q : QuadForm (𝓞 F) n) :
    ((DVR.chiDisc (NF.Qp v Q) : ℤ) : ℝ) = 0 ∨ ((DVR.chiDisc (NF.Qp v Q) : ℤ) : ℝ) = 1 ∨
      ((DVR.chiDisc (NF.Qp v Q) : ℤ) : ℝ) = -1 := by
  unfold DVR.chiDisc
  rcases (quadraticChar_isQuadratic _) ((-1) ^ (n / 2) * DVR.resGramDet (NF.Qp v Q)) with h | h | h <;>
    simp [h]

open Classical in
/-- **The good-prime factor, $n = 2k \ge 6$** (Table 1 / L10 over $F$, `NF.localDensity_ge_even_of_unimodular`): at $\mathfrak p \nmid 2\det H$ and
for every $m \ne 0$, with $q = N\mathfrak p$,
$$\beta_\mathfrak p(m) \ge (1 - q^{-2})\cdot\begin{cases}(1 - q^{-2})^2 & m \in \mathfrak p,\\ 1 & m \notin \mathfrak p.\end{cases}$$
*Proof:* $1 - \chi q^{-k} \ge 1 - q^{-2}$, and $\frac{X-1}{X+1} \ge (1 - X^{-1})^2 \ge (1 - q^{-2})^2$ for $X = q^{k-1} \ge q^2$. -/
theorem localDensityNF_good_ge {Q : QuadForm (𝓞 F) n} {k : ℕ} (hn : n = 2 * k) (hk : 3 ≤ k)
    {v : HeightOneSpectrum (𝓞 F)} (hG : IsGoodPrimeNF Q v) {m : 𝓞 F} (hm : m ≠ 0) :
    (1 - (N𝔭 v) ^ (-(2 : ℝ))) * (if m ∈ v.asIdeal then (1 - (N𝔭 v) ^ (-(2 : ℝ))) ^ 2 else 1) ≤
      NF.localDensity v Q m := by
  classical
  have hN := notDvdLevel_of_isGoodPrimeNF v hG
  have h := NF.localDensity_ge_even_of_unimodular v Q hG.1 hN (by omega) (by rw [hn]; exact even_two_mul k) m hm
  have hq : (2 : ℝ) ≤ N𝔭 v := two_le_normP_real v
  have hr : (N𝔭 v) ^ (-(2 : ℝ)) = 1 / (N𝔭 v) ^ 2 := by
    rw [Real.rpow_neg (by linarith), Real.rpow_two, one_div]
  rw [hr]
  set q : ℝ := N𝔭 v with hqdef
  have hq0 : 0 < q := by linarith
  have hq2 : 1 / q ^ 2 ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hA0 : 0 ≤ 1 - 1 / q ^ 2 := by linarith [hq2]
  have hkq : 1 / q ^ (n / 2) ≤ 1 / q ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by linarith) (by omega))
  have hkq0 : 0 ≤ 1 / q ^ (n / 2) := by positivity
  have hA : 1 - 1 / q ^ 2 ≤ 1 - ((DVR.chiDisc (NF.Qp v Q) : ℤ) : ℝ) / q ^ (n / 2) := by
    have hq2' : 0 ≤ 1 / q ^ 2 := by positivity
    rcases chiDisc_cases v Q with hc | hc | hc <;> rw [hc]
    · rw [zero_div]; linarith
    · linarith
    · rw [neg_div]; linarith
  set X : ℝ := q ^ ((n - 2) / 2) with hX
  have hXq : q ^ 2 ≤ X := pow_le_pow_right₀ (by linarith) (by omega)
  have hX0 : 0 < X := by positivity
  have hX1 : 1 / X ≤ 1 / q ^ 2 := one_div_le_one_div_of_le (by positivity) hXq
  have hB : (if m ∈ v.asIdeal then (1 - 1 / q ^ 2) ^ 2 else 1) ≤
      (if DVR.chiDisc (NF.Qp v Q) = -1 ∧ m ∈ v.asIdeal then (X - 1) / (X + 1) else 1) := by
    by_cases hmv : m ∈ v.asIdeal
    · simp only [hmv, ↓reduceIte, and_true]
      split_ifs
      · have h1 : (1 - 1 / q ^ 2) ^ 2 ≤ (1 - 1 / X) ^ 2 :=
          pow_le_pow_left₀ hA0 (by linarith) 2
        have h2 : (1 - 1 / X) ^ 2 ≤ (X - 1) / (X + 1) := by
          rw [le_div_iff₀ (by linarith)]
          have : (1 - 1 / X) ^ 2 * (X + 1) = (X - 1) * (1 - 1 / X ^ 2) * (X / X) := by
            field_simp; ring
          rw [this, div_self hX0.ne', mul_one]
          have : 0 ≤ X - 1 := by nlinarith
          have : 0 ≤ 1 / X ^ 2 := by positivity
          nlinarith
        exact h1.trans h2
      · nlinarith
    · simp [hmv]
  have hB0 : 0 ≤ (if m ∈ v.asIdeal then (1 - 1 / q ^ 2) ^ 2 else (1 : ℝ)) := by
    split_ifs <;> positivity
  have hC0 : 0 ≤ 1 - ((DVR.chiDisc (NF.Qp v Q) : ℤ) : ℝ) / q ^ (n / 2) := hA0.trans hA
  exact (mul_le_mul hA hB hB0 hC0).trans h

/-- **The main-term lower bound $a_E(\nu) \ge \kappa\,N(\nu)^{k-1}$** ($F$ totally real, $Q$ totally positive definite in $n = 2k \ge 6$
variables, `LocalDensityGapNF` at the primes $\mathfrak p \mid 2\det H$): there is $\kappa > 0$ such that every totally nonnegative
$\nu \ne 0$ with $\beta_\mathfrak p(\nu) > 0$ at every $\mathfrak p \mid 2\det H$ has
$$a_E(\nu) = \beta_\infty(\nu)\prod_\mathfrak p\beta_\mathfrak p(\nu) \ge \kappa\,|N_{F/\mathbb Q}(\nu)|^{k-1}.$$
Explicitly $\kappa = c_\infty(6/\pi^2)^{3d}\prod_{\mathfrak p \mid 2\det H}c_\mathfrak p$ ($c_\infty$ of `betaInfNF_eq_norm`, $c_\mathfrak p$ of
`LocalDensityGapNF`, $d = [F:\mathbb Q]$): one $(6/\pi^2)^d$ from the good primes not dividing $\nu$ (`le_eulerProductNF_uncond`), two from
the good primes dividing $\nu$ (`localDensityNF_good_ge`). Hanke 2004, Thm 5.7(c), p. 373 ($n \ge 5$; here $n$ even), with every prime
isotropic so that $(m)_{\mathrm{Aniso}} = 1$. -/
@[kb "hanke2004" "Thm 5.7(c), p. 373 (n even ≥ 6, global lower bound a_E(ν) ≫ N(ν)^{k-1}, over F)"]
theorem aENF_ge_of_gap [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef Q) (hQnd : Q.Nondegenerate)
    {k : ℕ} (hn : n = 2 * k) (hk : 3 ≤ k) (hgap : ∀ v ∈ badPrimesNF Q, LocalDensityGapNF Q v) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ν : 𝓞 F, ν ≠ 0 → (∀ w : RealPlace F, 0 ≤ realEmb w (ν : F)) →
      (∀ v ∈ badPrimesNF Q, 0 < NF.localDensity v Q ν) →
      κ * |((Algebra.norm ℚ (ν : F) : ℚ) : ℝ)| ^ ((k : ℝ) - 1) ≤ aENF Q ν := by
  classical
  choose! c hc0 hcle using fun v hv => (hgap v hv).exists_le
  set cinf : ℝ := ∏ w : RealPlace F, n * unitBallVol n * gramDetNF Q w ^ (-(1 / 2 : ℝ)) / 2 with hcinf
  have hω : 0 < unitBallVol n := by rw [unitBallVol_eq (by omega)]; positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hcinf0 : 0 < cinf := Finset.prod_pos fun w _ => by
    have := Real.rpow_pos_of_pos (gramDetNF_pos hQ w) (-(1 / 2 : ℝ))
    positivity
  set z : ℝ := (6 / Real.pi ^ 2) ^ Module.finrank ℚ F with hzdef
  have hz : 0 < z := by positivity
  have hcB : 0 < ∏ v ∈ badPrimesNF Q, c v := Finset.prod_pos fun v hv => hc0 v hv
  refine ⟨cinf * z ^ 3 * ∏ v ∈ badPrimesNF Q, c v, by positivity, fun ν hν0 hνpos hloc => ?_⟩
  set A := badPrimesNF Q
  set A' := primesDividing ν
  set g : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    if v ∈ A' then (1 - (N𝔭 v) ^ (-(2 : ℝ))) ^ 2 else 1 with hg
  have hE := le_eulerProductNF_uncond hQnd (by omega) hν0 A A' g (fun v _ => by
      simp only [hg]; split_ifs <;> positivity) (fun v hv => by simp only [hg]; simp [hv])
    (fun v hv => by
      have hG : IsGoodPrimeNF Q v := by
        by_contra h; exact hv ((mem_badPrimesNF hQnd).2 h)
      have := localDensityNF_good_ge hn hk hG hν0
      simp only [hg, A', mem_primesDividing hν0]
      exact this)
  -- the good factors dividing `ν`
  have hgood : z ^ 2 ≤ ∏ v ∈ A' \ A, g v := by
    have h1 : ∏ v ∈ A' \ A, g v = (∏ v ∈ A' \ A, (1 - (N𝔭 v) ^ (-(2 : ℝ)))) ^ 2 := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun v hv => ?_
      simp only [hg]; simp [(Finset.mem_sdiff.1 hv).1]
    rw [h1]
    exact pow_le_pow_left₀ hz.le (six_div_pi_sq_pow_le_prod (F := F) (A' \ A)) 2
  -- the bad factors
  have hbad : (∏ v ∈ A, c v) ≤ ∏ v ∈ A, NF.localDensity v Q ν :=
    Finset.prod_le_prod₀ (fun v hv => (hc0 v hv).le) (fun v hv => hcle v hv ν hν0 (hloc v hv))
  have hP : z * (∏ v ∈ A, c v) * z ^ 2 ≤ eulerProductNF Q ν := by
    refine le_trans ?_ hE
    have h0 : 0 ≤ ∏ v ∈ A, c v := hcB.le
    have h1 : 0 ≤ (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * ∏ v ∈ A, NF.localDensity v Q ν :=
      mul_nonneg hz.le (h0.trans hbad)
    calc z * (∏ v ∈ A, c v) * z ^ 2 ≤ (z * ∏ v ∈ A, NF.localDensity v Q ν) * z ^ 2 := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left hgood h1
  -- the archimedean factor
  have hB := betaInfNF_eq_norm Q hνpos
  have hexp : ((n : ℝ) - 2) / 2 = (k : ℝ) - 1 := by rw [hn]; push_cast; ring
  rw [hexp, ← hcinf, Rat.cast_abs] at hB
  rw [aENF, aEWithNF, hB]
  have hN0 : 0 ≤ |((Algebra.norm ℚ (ν : F) : ℚ) : ℝ)| ^ ((k : ℝ) - 1) := by positivity
  calc cinf * z ^ 3 * (∏ v ∈ A, c v) * |((Algebra.norm ℚ (ν : F) : ℚ) : ℝ)| ^ ((k : ℝ) - 1)
      = cinf * |((Algebra.norm ℚ (ν : F) : ℚ) : ℝ)| ^ ((k : ℝ) - 1) * (z * (∏ v ∈ A, c v) * z ^ 2) := by
        ring
    _ ≤ cinf * |((Algebra.norm ℚ (ν : F) : ℚ) : ℝ)| ^ ((k : ℝ) - 1) * eulerProductNF Q ν := by
        gcongr

end QuadFormsKB.Siegel

/-! ### Tartakowsky's theorem over $F$ -/

namespace QuadFormsKB.HilbertModular

open QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

/-- **Locally represented $\Rightarrow \beta_\mathfrak p > 0$ over $F$** (Hanke 2004, Def. 5.2, p. 368; the DVR statement
`DVR.localDensity_pos_of_isLocallyRepresentedAt` at the completion). -/
theorem localDensityNF_pos_of_isLocallyRepresentedAt (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    {Q : QuadForm (𝓞 F) n} (hQ : Q.Nondegenerate) {m : 𝓞 F} (hm : m ≠ 0)
    (h : LocalDensity.NF.IsLocallyRepresentedAt v Q m) : 0 < LocalDensity.NF.localDensity v Q m := by
  rw [LocalDensity.NF.localDensity_eq_completion]
  exact LocalDensity.DVR.localDensity_pos_of_isLocallyRepresentedAt _ (LocalDensity.NF.nondegenerate_Qp v hQ) _
    (LocalDensity.NF.irreducible_π v) (LocalDensity.NF.two_ne_zero' v) _ (LocalDensity.NF.ι_ne_zero v hm)
    ((LocalDensity.NF.isLocallyRepresentedAt_iff v Q m).1 h)

variable [IsPrincipalIdealRing (𝓞 F)]

/-- **Tartakowsky's theorem over $F$, even rank $n \ge 6$, via Hecke's bound — core form** (bad-prime densities positive). Let $F$ be
totally real with $h_F = 1$ and $Q_0$ totally positive definite over $\mathcal O_F$ in $n = 2k \ge 6$ variables, with the local input
`LocalDensityGapNF` at every $\mathfrak p \mid 2\det H$. Then there is $M_0$ such that every totally positive $\nu \in \mathcal O_F$ with
$\beta_\mathfrak p(\nu) > 0$ at every $\mathfrak p \mid 2\det H$ and $|N_{F/\mathbb Q}(\nu)| \ge M_0$ is represented by $Q_0$ over $\mathcal O_F$.
$M_0$ exists but is not explicit (Hecke's constant). -/
@[kb "hanke2004" "Thm 6.4, p. 382 (n even ≥ 6), over F with h_F = 1, Hecke's bound; core form"]
theorem exists_eval_eq_of_localDensity_pos {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ}
    (hn : n = 2 * k) (hk : 3 ≤ k)
    (hgap : ∀ v ∈ QuadFormsKB.Siegel.badPrimesNF Q₀, QuadFormsKB.Siegel.LocalDensityGapNF Q₀ v) :
    ∃ M₀ : ℝ, ∀ ν : 𝓞 F, (∀ v, 0 < realEmb F v (ιO ν)) →
      (∀ v ∈ QuadFormsKB.Siegel.badPrimesNF Q₀, 0 < LocalDensity.NF.localDensity v Q₀ ν) →
      M₀ ≤ |((Algebra.norm ℚ (ιO ν) : ℚ) : ℝ)| → ∃ x : Fin n → 𝓞 F, Q₀.eval x = ν := by
  have hpos := isTotPosGram_Q₀ hQ
  have hQnd : Q₀.Nondegenerate := det_hessian_ne_zero hpos
  obtain ⟨κ, hκ, hlow⟩ := QuadFormsKB.Siegel.aENF_ge_of_gap Q₀ (siegel_isTotallyPosDef hpos) hQnd hn hk hgap
  obtain ⟨C, hC0, hC⟩ := exists_abs_repNumF_sub_le hQ hn hk
  set D : ℝ := (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (n - 1) with hD
  have hD0 : 0 < D := by
    have : (0 : ℝ) < |(discr F : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero F)
    positivity
  set e : ℝ := (k : ℝ) / 2 - 1 with he
  have he0 : 0 < e := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    rw [he]; linarith
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.1 ((tendsto_rpow_atTop he0).eventually_gt_atTop (C / (D * κ)))
  refine ⟨max M₁ 1, fun ν hν hloc hN => ?_⟩
  set N : ℝ := |((Algebra.norm ℚ (ιO ν) : ℚ) : ℝ)| with hNdef
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hν0 : ν ≠ 0 := by
    rintro rfl
    have := hν (Classical.arbitrary _)
    simp at this
  have hE := hlow ν hν0 (fun w => (hν w.1).le) hloc
  have hc := hC ν hν
  have hbig : C / (D * κ) < N ^ e := hM₁ N ((le_max_left _ _).trans hN)
  have hsplit : N ^ ((k : ℝ) - 1) = N ^ ((k : ℝ) / 2) * N ^ e := by
    rw [← Real.rpow_add hN0, he]; ring_nf
  have hx : 0 < N ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos hN0 _
  have h1 : C < D * κ * N ^ e := by
    rw [div_lt_iff₀ (by positivity)] at hbig; linarith
  have key : C * N ^ ((k : ℝ) / 2) < D * (κ * N ^ ((k : ℝ) - 1)) := by
    rw [hsplit]; nlinarith
  have hE' : D * (κ * N ^ ((k : ℝ) - 1)) ≤ D * QuadFormsKB.Siegel.aENF Q₀ ν :=
    mul_le_mul_of_nonneg_left hE hD0.le
  have hr : (0 : ℝ) < repNumF Q₀ ν := by
    have := (abs_le.1 hc).1
    linarith
  have hr' : 0 < repNumF Q₀ ν := by exact_mod_cast hr
  rw [repNumF, Nat.card_pos_iff] at hr'
  obtain ⟨⟨x, hx⟩, -⟩ := hr'
  exact ⟨x, hx⟩

/-- **Tartakowsky's theorem over a totally real field with $h_F = 1$, even rank $n \ge 6$** (Hanke 2004, Thm 6.4, p. 382, $n$ even, over
$F$; Tartakowsky 1929 over $\mathbb Q$), unconditional except for the named local input `LocalDensityGapNF` at the finitely many
$\mathfrak p \mid 2\det H$: there is $M_0$ such that every totally positive $\nu \in \mathcal O_F$ that is locally represented at every
prime (`NF.IsLocallyRepresentedAt`) and has $|N_{F/\mathbb Q}(\nu)| \ge M_0$ is represented by $Q_0$:
$$\exists M_0\ \forall \nu \gg 0:\ \big(\forall \mathfrak p,\ \nu \text{ loc. rep. at } \mathfrak p\big) \wedge |N(\nu)| \ge M_0 \Rightarrow
  \exists x \in \mathcal O_F^n,\ Q_0(x) = \nu.$$
For $n \ge 5$ every $\mathfrak p$ is isotropic, so Hanke's condition "bounded divisibility at the anisotropic primes" is vacuous.

*Proof:* Hecke's bound $|r_{Q_0}(\nu) - D_Fa_E(\nu)| \le C N(\nu)^{k/2}$ (`exists_abs_repNumF_sub_le`) against
$a_E(\nu) \ge \kappa N(\nu)^{k-1}$ (`Siegel.aENF_ge_of_gap`), $k - 1 > k/2$. *Non-explicit:* $M_0$ depends on Hecke's constant $C$ (a
supremum of $N(\operatorname{Im}z)^{k/2}|\theta_{Q_0} - E_Q|$ over $\mathbb H^d$). Deligne's bound (the cited (4.8), `thm_6_4_even`) would give an
explicit threshold. -/
@[kb "hanke2004" "Thm 6.4, p. 382 (n even ≥ 6), over F with h_F = 1, via Hecke's bound (non-explicit constant)"]
theorem tartakowsky_nf {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ}
    (hn : n = 2 * k) (hk : 3 ≤ k)
    (hgap : ∀ v ∈ QuadFormsKB.Siegel.badPrimesNF Q₀, QuadFormsKB.Siegel.LocalDensityGapNF Q₀ v) :
    ∃ M₀ : ℝ, ∀ ν : 𝓞 F, (∀ v, 0 < realEmb F v (ιO ν)) →
      (∀ v, LocalDensity.NF.IsLocallyRepresentedAt v Q₀ ν) →
      M₀ ≤ |((Algebra.norm ℚ (ιO ν) : ℚ) : ℝ)| → ∃ x : Fin n → 𝓞 F, Q₀.eval x = ν := by
  obtain ⟨M₀, h⟩ := exists_eval_eq_of_localDensity_pos hQ hn hk hgap
  refine ⟨M₀, fun ν hν hloc hN => h ν hν (fun v _ => ?_) hN⟩
  have hν0 : ν ≠ 0 := by
    rintro rfl
    have := hν (Classical.arbitrary _)
    simp at this
  exact localDensityNF_pos_of_isLocallyRepresentedAt v (det_hessian_ne_zero (isTotPosGram_Q₀ hQ)) hν0 (hloc v)

end QuadFormsKB.HilbertModular
