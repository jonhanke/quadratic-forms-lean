/-
# Siegel's formula in rank one: the correct statement

**Layer:** forms $Q_0 = \langle c\rangle$ over $\mathcal O_F$, $F$ a number field (totally real in the intended use), the
standard lattice $L = \mathcal O_F$, and the represented number $m = c$.

**Warning (rank one).** `SiegelFormulaAt` and `siegelProduct` are **not** meaningful at
$N = 1$. The good local densities are
$\beta_\mathfrak p(\langle c\rangle, m) = 1 + \bigl(\tfrac{cm}{\mathfrak p}\bigr)$,
which is $2$ (not $1 + O(N\mathfrak p^{-2})$) at almost every prime when $m = cs^2$; so
$\prod_\mathfrak p\beta_\mathfrak p(m)$ diverges to $+\infty$ exactly when $m$ is
represented, and Mathlib's `tprod` returns its junk value $1$. Over $\mathbb Z$ this is proved
(`Siegel.RankOne.no_siegel_formula_rank_one`: the genus average is $2$ while $\prod_p\beta_p$ has no value). Over
$\mathbb Q$ with the objects this is `not_siegelFormulaAt_rankOne_int` ($\neg$`SiegelFormulaAt` for $\langle a\rangle$
at $m = a$). Over $\mathcal O_F$ the same
argument applies (the factors are $2$ at all good primes, `siegelDensity_rankOne_good`) but needs infinitely many primes of $\mathcal O_F$; not formalized. The
cause is Weil's: $SO_1$ is trivial, $\tau(SO_1) = 1$ (not $2$), and $O_1 = \{\pm1\}$ has the extra component.

**The correct rank-one formula (this file).** Normalize every place by Siegel's $\varepsilon = \frac12$ for $r = n$
($\alpha_v = \frac12\beta_v$; at $\mathfrak p$ it is `NF.siegelDensity`):
$$\mathcal S_1(c) = \prod_{\sigma : F \to \mathbb C}\frac{\beta_\sigma(c)}{2}\cdot\prod_\mathfrak p\frac{\beta_\mathfrak p(c)}{2}
\quad(\text{a finite product}),$$
$\beta_\sigma(c)$ = `archRepDensity 1 ‖σ c‖ (detGram Q₀ σ)` and $\beta_\mathfrak p$ = `NF.localDensity`. Then
* `siegelProductOne_self`: $\mathcal S_1(c) = 1$ (the product formula for $2c$; this is $\mu_{\mathrm{Tam}}(K_{SO}) = 1$,
  `TauSOOne.tamagawaK_rankOne_eq_one`);
* `repMass_rankOne_self`: $\mathrm{repMass}(\mathcal O_F, c) = r(c)/|O| = 1$ with $r(c) = \#\{\pm1\} = 2$;
* **`siegelFormulaOne_self`**: $\mathrm{repMass}(\mathcal O_F, c) = \mathrm{Mass}(\mathcal O_F)\cdot\bigl(2\,\mathcal S_1(c)\bigr)$, i.e. the genus
  average is $r_{\mathrm{gen}}(c) = 2 = |O_1(F)|\cdot\mathcal S_1(c)$ (Siegel's constant is $|O(V)(F)|/2\cdot$ the
  normalized product; here $\mathrm{Mass} = \frac12$, `RankOne.mass_rankOne`).
Over $\mathbb Q$ the statement for $\langle a\rangle$ over $\mathbb Z$ is `siegelFormulaOne_int_self`.

*Scope.* This file treats the number $m = c$ (the form's own value). **The general represented number $m = cs^2$** (the DVR count
$\#\{x \bmod \pi^k : x^2 \equiv s^2\}$, $\beta_\mathfrak p(\langle c\rangle, cs^2) = 2N\mathfrak p^{v_\mathfrak p(2cs)}$, and the product formula for $2cs$) is in
`SiegelRankOneGeneral.lean` (`siegelFormulaOne_sq`, `siegelProductOne_sq`, and over $\mathbb Z$ `siegelFormulaOne_int` for every $m \ge 1$,
with the value $0$ when $m \notin c\,\mathbb Z^2$); the divergence dichotomy over $\mathbb Z$ is `Siegel.RankOne.siegel_rank_one_dichotomy`.
-/
import QuadFormsKB.Tamagawa.TauSOOne
import QuadFormsKB.Tamagawa.MassInduction
import QuadFormsKB.Tamagawa.RatBridge
import QuadFormsKB.Siegel.RankOne
import QuadFormsKB.Siegel.RankOneDensity

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

namespace QuadFormsKB.Tamagawa.SiegelRankOne

open Lattices QuadFormsKB.LocalDensity

variable {F : Type} [Field F] [NumberField F]

local notation "QFof" Q₀ => QuadForm.map (algebraMap (𝓞 F) F) Q₀

/-- **The normalized rank-one Siegel product at the number $m$** (every place carries Siegel's $\varepsilon = \frac12$):
$$\mathcal S_1(m) = \prod_{\sigma}\frac{\beta_\sigma(m)}{2}\cdot\prod_\mathfrak p\frac{\beta_\mathfrak p(m)}{2}.$$
The finite factors are $1$ off the bad primes when $m = c$ (so `tprod` is a finite product); it replaces the
`siegelProduct`, which is degenerate at $N = 1$. -/
@[kb "siegel1935" "Hauptsatz, n = 1 (ε = 1/2 at every place) [unverified]"]
def siegelProductOne (Q₀ : QuadForm (𝓞 F) 1) (m : 𝓞 F) : ℝ :=
  (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 1 ‖σ (algebraMap (𝓞 F) F m)‖ (detGram Q₀ σ) / 2) *
    ∏' v : HeightOneSpectrum (𝓞 F), NF.localDensity v Q₀ m / 2


/-- A one-variable form over $\mathcal O_F$ is $\langle c\rangle$. -/
theorem eq_unary (Q₀ : QuadForm (𝓞 F) 1) : Q₀ = LocalDensity.DVR.unary (Q₀.coeff 0 0) := by
  ext i j
  fin_cases i; fin_cases j
  simp [LocalDensity.DVR.unary, QuadForm.diag]

/-- **The normalized local factor is the Siegel density:** $\beta_\mathfrak p(Q_0, c)/2 = \alpha_\mathfrak p(Q_0, Q_0)$ for
$Q_0 = \langle c\rangle$ (`NF.localDensityForm_unary`, $\varepsilon = \frac12$ since $n = r = 1$). -/
theorem localDensity_div_two_eq_siegelDensity (Q₀ : QuadForm (𝓞 F) 1) (v : HeightOneSpectrum (𝓞 F)) :
    NF.localDensity v Q₀ (Q₀.coeff 0 0) / 2 = NF.siegelDensity v Q₀ Q₀ := by
  conv_rhs => rw [NF.siegelDensity, if_pos rfl]
  conv_rhs => rw [show NF.localDensityForm v Q₀ Q₀ = NF.localDensityForm v Q₀ (LocalDensity.DVR.unary (Q₀.coeff 0 0)) by
    rw [← eq_unary Q₀]]
  rw [NF.localDensityForm_unary]
  ring

/-- $\beta_\sigma(c)/2 = 1/(2\,|\sigma c|)$ in rank one: $\pi^{1/2}/\Gamma(1/2) = 1$ and $\|\sigma c\|^{-1/2}\|\sigma c\|^{-1/2}
= \|\sigma c\|^{-1}$ (`detGram_rankOne`). -/
theorem archRepDensity_rankOne_self (Q₀ : QuadForm (𝓞 F) 1) (hc : Q₀.coeff 0 0 ≠ 0) (σ : F →ₐ[ℚ] ℂ) :
    archRepDensity 1 ‖σ (algebraMap (𝓞 F) F (Q₀.coeff 0 0))‖ (detGram Q₀ σ) / 2 = 1 / (2 * detGram Q₀ σ) := by
  have hd := TauSOOne.detGram_rankOne Q₀ σ
  have hpos : 0 < ‖σ ((Q₀.coeff 0 0 : 𝓞 F) : F)‖ := by
    rw [norm_pos_iff, map_ne_zero]; exact_mod_cast hc
  have hcoe : (algebraMap (𝓞 F) F) (Q₀.coeff 0 0) = ((Q₀.coeff 0 0 : 𝓞 F) : F) := rfl
  rw [hcoe, hd, archRepDensity]
  have h1 : Real.pi ^ (((1 : ℕ) : ℝ) / 2) / Real.Gamma (((1 : ℕ) : ℝ) / 2) = 1 := by
    have : Real.pi ^ (((1 : ℕ) : ℝ) / 2) = Real.sqrt Real.pi := by
      rw [Real.sqrt_eq_rpow]; norm_num
    rw [this]; norm_num [Real.Gamma_one_half_eq]
    exact Real.sqrt_ne_zero'.mpr Real.pi_pos
  set a := ‖σ ((Q₀.coeff 0 0 : 𝓞 F) : F)‖
  have h2 : a ^ ((((1 : ℕ) : ℝ) - 2) / 2) * a ^ (-(1 / 2 : ℝ)) = a⁻¹ := by
    rw [← Real.rpow_add hpos, ← Real.rpow_neg_one]; congr 1; norm_num
  rw [mul_assoc, h2] at *
  rw [h1] at *
  field_simp

/-- **$\mathcal S_1(c) = \mu_{\mathrm{Tam}}(K_{SO})$**: the normalized rank-one product at $m = c$ is `tamagawaK`. -/
theorem siegelProductOne_self_eq_tamagawaK (Q₀ : QuadForm (𝓞 F) 1) (hQ : Q₀.Nondegenerate) :
    siegelProductOne Q₀ (Q₀.coeff 0 0) = tamagawaK Q₀ := by
  have hc : Q₀.coeff 0 0 ≠ 0 := by
    intro h0; apply hQ; rw [TauSOOne.hessian_det_rankOne, h0, mul_zero]
  rw [siegelProductOne, tamagawaK]
  simp only [RankOne.archVolSO_one, Finset.prod_congr rfl fun σ _ => archRepDensity_rankOne_self Q₀ hc σ,
    localDensity_div_two_eq_siegelDensity]
  norm_num

/-- **$\mathcal S_1(c) = 1$.** -/
@[kb "weil1982" "§3.7, τ(SO_1) = 1 [unverified]"]
theorem siegelProductOne_self (Q₀ : QuadForm (𝓞 F) 1) (hQ : Q₀.Nondegenerate) :
    siegelProductOne Q₀ (Q₀.coeff 0 0) = 1 := by
  rw [siegelProductOne_self_eq_tamagawaK Q₀ hQ, TauSOOne.tamagawaK_rankOne_eq_one Q₀ hQ]

/-! ### The representation number and the genus average -/

theorem eval_rankOne (Q₀ : QuadForm (𝓞 F) 1) (x : Fin 1 → F) :
    (QFof Q₀).eval x = algebraMap (𝓞 F) F (Q₀.coeff 0 0) * x 0 ^ 2 := by
  simp [QuadForm.eval, QuadForm.evalIn, QuadForm.map]; ring

/-- **$r_{\mathcal O_F}(c) = 2$ for $Q_0 = \langle c\rangle$:** the solutions of $c\,x^2 = c$ in $\mathcal O_F$ are $x = \pm1$. -/
theorem repCount_rankOne_self (Q₀ : QuadForm (𝓞 F) 1) (hc : Q₀.coeff 0 0 ≠ 0) :
    Tamagawa.repCount (QFof Q₀) (stdLat F 1) (algebraMap (𝓞 F) F (Q₀.coeff 0 0)) = 2 := by
  have hcF : algebraMap (𝓞 F) F (Q₀.coeff 0 0) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hc
  have hset : {v : Fin 1 → F | v ∈ (stdLat F 1).1 ∧ (QFof Q₀).eval v = algebraMap (𝓞 F) F (Q₀.coeff 0 0)} =
      {fun _ => 1, fun _ => -1} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      rw [eval_rankOne] at h
      have h1 : v 0 ^ 2 = 1 := by
        have : algebraMap (𝓞 F) F (Q₀.coeff 0 0) * (v 0 ^ 2 - 1) = 0 := by linear_combination h
        rcases mul_eq_zero.mp this with h0 | h0
        · exact absurd h0 hcF
        · exact sub_eq_zero.mp h0
      have h3 : (v 0 - 1) * (v 0 + 1) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp h3 with h2 | h2
      · left; funext i; fin_cases i; simpa [sub_eq_zero] using h2
      · right; funext i; fin_cases i; simpa [add_eq_zero_iff_eq_neg] using h2
    · rintro (rfl | rfl)
      · exact ⟨fun i => ⟨1, by simp⟩, by rw [eval_rankOne]; simp⟩
      · exact ⟨fun i => ⟨-1, by simp⟩, by rw [eval_rankOne]; simp⟩
  unfold Tamagawa.repCount
  have : Nat.card {v : Fin 1 → F // v ∈ (stdLat F 1).1 ∧ (QFof Q₀).eval v = algebraMap (𝓞 F) F (Q₀.coeff 0 0)} =
      Set.ncard {v : Fin 1 → F | v ∈ (stdLat F 1).1 ∧ (QFof Q₀).eval v = algebraMap (𝓞 F) F (Q₀.coeff 0 0)} :=
    Nat.card_coe_set_eq _
  rw [this, hset, Set.ncard_pair]
  intro h
  have := congrFun h 0
  norm_num at this

/-- **$\mathrm{repMass}(\mathcal O_F, c) = 1$** (rank one: one class, $|O| = 2$, $r(c) = 2$). -/
theorem repMass_rankOne_self (Q₀ : QuadForm (𝓞 F) 1) (hc : Q₀.coeff 0 0 ≠ 0) :
    repMass (QFof Q₀) (stdLat F 1) (algebraMap (𝓞 F) F (Q₀.coeff 0 0)) = 1 := by
  have hc' : (QFof Q₀).coeff 0 0 ≠ 0 := by simpa [QuadForm.map] using hc
  rw [repMass, RankOne.genusClasses_rankOne hc', finsum_mem_singleton]
  change ((Tamagawa.repCount (QFof Q₀) (stdLat F 1) _ : ℕ) : ℝ) / (Nat.card (autLat (QFof Q₀) (stdLat F 1).1) : ℝ) = 1
  rw [repCount_rankOne_self Q₀ hc, RankOne.card_autLat_rankOne hc']
  norm_num

/-- **Siegel's formula in rank one, at the number $c$ (KB conventions, correct form).** For $Q_0 = \langle c\rangle$ over $\mathcal O_F$
(nondegenerate, i.e. $c \ne 0$; no positivity needed, $F$ any number field):
$$\mathrm{repMass}(\mathcal O_F, c) = \mathrm{Mass}(\mathcal O_F)\cdot\bigl(2\,\mathcal S_1(c)\bigr),$$
i.e. the genus average $r_{\mathrm{gen}}(c) = 2 = |O_1(F)|\cdot\mathcal S_1(c)$ with $\mathcal S_1(c) = 1$ the normalized product
(`siegelProductOne`). **Not** `SiegelFormulaAt`, which is degenerate at $N = 1$ (see the file header). -/
@[kb "siegel1935" "Hauptsatz, n = 1 (ε = 1/2, trivial SO_1) [unverified]"]
theorem siegelFormulaOne_self (Q₀ : QuadForm (𝓞 F) 1) (hQ : Q₀.Nondegenerate) :
    repMass (QFof Q₀) (stdLat F 1) (algebraMap (𝓞 F) F (Q₀.coeff 0 0)) =
      mass (QFof Q₀) (stdLat F 1) * (2 * siegelProductOne Q₀ (Q₀.coeff 0 0)) := by
  have hc : Q₀.coeff 0 0 ≠ 0 := by
    intro h0; apply hQ; rw [TauSOOne.hessian_det_rankOne, h0, mul_zero]
  have hc' : (QFof Q₀).coeff 0 0 ≠ 0 := by simpa [QuadForm.map] using hc
  rw [repMass_rankOne_self Q₀ hc, RankOne.mass_rankOne hc', siegelProductOne_self Q₀ hQ]
  norm_num

/-- **The genus average in rank one:** $r_{\mathrm{gen}}(c) = \mathrm{repMass}/\mathrm{Mass} = 2\,\mathcal S_1(c)$. -/
theorem genusAverage_rankOne_self (Q₀ : QuadForm (𝓞 F) 1) (hQ : Q₀.Nondegenerate) :
    repMass (QFof Q₀) (stdLat F 1) (algebraMap (𝓞 F) F (Q₀.coeff 0 0)) /
      mass (QFof Q₀) (stdLat F 1) = 2 * siegelProductOne Q₀ (Q₀.coeff 0 0) := by
  have hc : Q₀.coeff 0 0 ≠ 0 := by
    intro h0; apply hQ; rw [TauSOOne.hessian_det_rankOne, h0, mul_zero]
  have hc' : (QFof Q₀).coeff 0 0 ≠ 0 := by simpa [QuadForm.map] using hc
  rw [siegelFormulaOne_self Q₀ hQ, RankOne.mass_rankOne hc']
  ring

/-! ### Over $\mathbb Q$: the form $\langle a\rangle$ over $\mathbb Z$ -/

/-- $\langle a\rangle$ is positive definite over $\mathbb Z$ for $a > 0$. -/
theorem posDef_unary {a : ℤ} (ha : 0 < a) : IntQF.PosDef (QuadFormsKB.Siegel.RankOne.unary a) := by
  intro x hx
  rw [QuadFormsKB.Siegel.RankOne.eval_unary]
  have : x 0 ≠ 0 := by
    intro h0; apply hx; funext i; fin_cases i; simpa using h0
  positivity

/-- **Siegel's formula in rank one over $\mathbb Z$, at the number $a$** (Hanke's genus average of `QuadFormsKB.Siegel.genusRepAvg`,
$a > 0$): $r_{\mathrm{gen}}(\langle a\rangle, a) = 2 = 2\,\mathcal S_1(a)$, where $\mathcal S_1$ is the normalized product of
`siegelProductOne` for $\langle a\rangle \otimes \mathcal O_{\mathbb Q}$ (so $\mathcal S_1 = 1$). The literal
$a_E(a) = \beta_\infty\prod_p\beta_p$ is false here (`QuadFormsKB.Siegel.RankOne.no_siegel_formula_rank_one`). -/
@[kb "siegel1935" "Hauptsatz, n = 1 over ℤ (ε = 1/2, trivial SO_1) [unverified]"]
theorem siegelFormulaOne_int_self {a : ℤ} (ha : 0 < a) :
    QuadFormsKB.Siegel.genusRepAvg (QuadFormsKB.Siegel.RankOne.unary a) a =
      2 * siegelProductOne (RatBridge.up (QuadFormsKB.Siegel.RankOne.unary a)) (a : 𝓞 ℚ) := by
  have hpd := posDef_unary ha
  have hQ : (RatBridge.up (QuadFormsKB.Siegel.RankOne.unary a)).Nondegenerate := by
    rw [QuadForm.Nondegenerate, TauSOOne.hessian_det_rankOne]
    simp [QuadForm.map, QuadFormsKB.Siegel.RankOne.unary, QuadForm.diag]
    exact ha.ne'
  have h := genusAverage_rankOne_self (RatBridge.up (QuadFormsKB.Siegel.RankOne.unary a)) hQ
  have hcoef : (RatBridge.up (QuadFormsKB.Siegel.RankOne.unary a)).coeff 0 0 = (a : 𝓞 ℚ) := by
    simp [QuadForm.map, QuadFormsKB.Siegel.RankOne.unary, QuadForm.diag]
  rw [QuadFormsKB.Siegel.genusRepAvg, RatBridge.mass_rat _ hpd, RatBridge.repMass_rat _ hpd]
  rw [hcoef] at h
  simpa using h

/-! ### The literal `SiegelFormulaAt` is false at $N = 1$ (over $\mathbb Q$) -/

/-- $\beta_\infty(\langle a\rangle, a) = 1/a$ (Hanke's (5.5) at $n = 1$: $\omega_1 = 2$, $D = a$). -/
theorem betaInf_unary_self {a : ℤ} (ha : 0 < a) :
    QuadFormsKB.Siegel.betaInf (QuadFormsKB.Siegel.RankOne.unary a) a = 1 / a := by
  have hD : QuadFormsKB.Siegel.gramDet (QuadFormsKB.Siegel.RankOne.unary a) = a := by
    simp [QuadFormsKB.Siegel.gramDet, QuadForm.hessian, QuadFormsKB.Siegel.RankOne.unary, QuadForm.diag]
  have hω : QuadFormsKB.Siegel.unitBallVol 1 = 2 := by
    rw [QuadFormsKB.Siegel.unitBallVol_eq le_rfl]
    have : Real.Gamma (((1 : ℕ) : ℝ) / 2 + 1) = Real.sqrt Real.pi / 2 := by
      rw [Real.Gamma_add_one (by norm_num)]; norm_num [Real.Gamma_one_half_eq]; ring
    rw [this]
    have : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
    simp
    field_simp
  have hpos : (0 : ℝ) < a := by exact_mod_cast ha
  rw [QuadFormsKB.Siegel.betaInf, hD, hω]
  have h2 : (a : ℝ) ^ (-(1 / 2 : ℝ)) * (a : ℝ) ^ ((((1 : ℕ) : ℝ) - 2) / 2) = (a : ℝ)⁻¹ := by
    rw [← Real.rpow_add hpos, ← Real.rpow_neg_one]; congr 1; norm_num
  calc _ = (a : ℝ) ^ (-(1 / 2 : ℝ)) * (a : ℝ) ^ ((((1 : ℕ) : ℝ) - 2) / 2) := by push_cast; ring
    _ = 1 / a := by rw [h2]; simp

/-- **`SiegelFormulaAt` is false at $N = 1$** (over $\mathbb Q$, $Q_0 = \langle a\rangle$, $m = a \ge 1$): the Euler
factors are $\beta_p(a) = 2p^{v_p(2a)}\ge 2$ so the product is not multipliable, `tprod` is $1$,
`siegelProduct` $= \beta_\infty(a) = 1/a$, and the formula would read
$1 = \frac12\cdot\frac1a$. Use `siegelFormulaOne_self` instead. -/
theorem not_siegelFormulaAt_rankOne_int {a : ℤ} (ha : 0 < a) :
    ¬ SiegelFormulaAt (RatBridge.up (QuadFormsKB.Siegel.RankOne.unary a)) (a : 𝓞 ℚ) := by
  intro h
  have hpd := posDef_unary ha
  have hs := RatBridge.siegelProduct_up (QuadFormsKB.Siegel.RankOne.unary a) hpd le_rfl (m := a) ha
  have hnm : ¬ Multipliable (QuadFormsKB.Siegel.eulerFactor (QuadFormsKB.Siegel.RankOne.unary a) a) := by
    have := QuadFormsKB.Siegel.RankOne.not_multipliable_eulerFactor (a := a) (k := 1) ha.ne' one_ne_zero
    simpa using this
  have hae : QuadFormsKB.Siegel.aE (QuadFormsKB.Siegel.RankOne.unary a) a = 1 / a := by
    rw [QuadFormsKB.Siegel.aE, QuadFormsKB.Siegel.aEWith, QuadFormsKB.Siegel.eulerProduct,
      tprod_eq_one_of_not_multipliable hnm, mul_one, betaInf_unary_self ha]
  have hQ : (RatBridge.up (QuadFormsKB.Siegel.RankOne.unary a)).Nondegenerate := by
    rw [QuadForm.Nondegenerate, TauSOOne.hessian_det_rankOne]
    simp [QuadForm.map, QuadFormsKB.Siegel.RankOne.unary, QuadForm.diag]
    exact ha.ne'
  have hcoef : (RatBridge.up (QuadFormsKB.Siegel.RankOne.unary a)).coeff 0 0 = (a : 𝓞 ℚ) := by
    simp [QuadForm.map, QuadFormsKB.Siegel.RankOne.unary, QuadForm.diag]
  have h1 := h.repMass_eq
  have h2 := genusAverage_rankOne_self (RatBridge.up (QuadFormsKB.Siegel.RankOne.unary a)) hQ
  have hS := siegelProductOne_self (RatBridge.up (QuadFormsKB.Siegel.RankOne.unary a)) hQ
  rw [hS] at h2
  rw [hcoef] at h2
  have hM := RankOne.mass_rankOne (RankOne.coeff_ne_zero_of_nondegenerate _ hQ)
    (stdLat ℚ 1)
  rw [hM] at h1 h2
  rw [hs, hae] at h1
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hpos : (0 : ℝ) < a := by linarith
  field_simp at h2 h1
  nlinarith

end QuadFormsKB.Tamagawa.SiegelRankOne
