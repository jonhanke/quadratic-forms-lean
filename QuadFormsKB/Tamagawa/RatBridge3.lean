import QuadFormsKB.Tamagawa.SiegelRank3
import QuadFormsKB.Tamagawa.RatBridge

/-!
# Rank-3 Siegel formula over $\mathbb Q$: the bridge to Hanke's `SiegelFormula3`

**Layer:** positive definite ternary forms `Q : QuadForm ℤ 3` (Hanke's objects, `Siegel.SiegelFormula3 Q P` with an
explicit value $P(m)$ of the conditionally convergent Euler product) and their base change $Q\otimes\mathcal O_{\mathbb Q}$
(`RatBridge.up Q`) with the rank-3 statement `SiegelFormulaAt3` over a number field.

**Results (proved).**
* `HilbertModular.siegelProductWith_eq_discr_mul_aEWithNF`: for $F$ totally real and $Q_0$ totally positive definite,
  `siegelProductWith Q₀ m P` $= |d_F|^{-(N-1)/2}\cdot$ `Siegel.aEWithNF Q₀ m P` for every value $P$ (the archimedean half of
  `siegelProduct_eq_discr_mul_aENF`, with $P$ free).
* `Siegel.eulerProductReg3 Q m`: the regularized value of $\prod_p\beta_p(m)$ (regularized by $L(1,\chi_m)$),
  defined through
  $Q\otimes\mathcal O_{\mathbb Q}$: $L(1,\chi_m)\prod_p\beta_p(m)(1-\chi_m(p)/p)$.
* `RatBridge3.siegelProduct3_up`: `siegelProduct3 (up Q) m = Siegel.aEWith Q m (eulerProductReg3 Q m)`.
* **Bridge** `RatBridge3.siegelFormula3_iff_siegelFormulaAt3`: Hanke's `SiegelFormula3 Q (eulerProductReg3 Q)` holds iff
  `SiegelFormulaAt3 (up Q) m` holds for every integer $m \ge 1$; and `siegelFormulaAt3_of_siegelFormula3`.

The natural-order identification $P(m) = $ `eulerProductReg3 Q m` (`IsEulerProductValue`, which Hanke's rank-3 corollaries
`thm_5_4_genus3`, `thm_5_7_a_genus`, … assume) is in `RatHeadline3` (via `EulerOne.tendsto_prod_primesBelow`).
-/

open NumberField Matrix IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.HilbertModular

open QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

local notation "ιO" => algebraMap (𝓞 F) F

open Classical in
/-- **The archimedean factors are `Siegel.betaInfNF`:** for $Q_0$ totally positive definite and $m \gg 0$,
$\prod_{\sigma : F\to\mathbb C}$ `archRepDensity N |σ(m)| (detGram Q₀ σ)` $= \beta_\infty^F(m)$ (the argument of
`siegelProduct_eq_discr_mul_aENF`). -/
theorem archProd_eq_betaInfNF {N : ℕ} {Q : QuadForm (𝓞 F) N} (hQ : IsTotPosGram (gramF Q)) (hN : 1 ≤ N)
    {m : 𝓞 F} (hm : ∀ v, 0 < realEmb F v (ιO m)) :
    ∏ σ : F →ₐ[ℚ] ℂ, QuadFormsKB.Tamagawa.archRepDensity N ‖σ (ιO m)‖ (QuadFormsKB.Tamagawa.detGram Q σ) =
      QuadFormsKB.Siegel.betaInfNF Q (ιO m) := by
  set G : InfinitePlace F → ℝ := fun w => QuadFormsKB.Tamagawa.archRepDensity N (w (ιO m))
    (w (ιO Q.hessian.det / 2 ^ N))
  have h1 : ∏ σ : F →ₐ[ℚ] ℂ, QuadFormsKB.Tamagawa.archRepDensity N ‖σ (ιO m)‖
      (QuadFormsKB.Tamagawa.detGram Q σ) = ∏ φ : F →+* ℂ, G (InfinitePlace.mk φ) := by
    rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ : F →+* ℂ => G (InfinitePlace.mk φ))
      (fun σ => QuadFormsKB.Tamagawa.archRepDensity N ‖σ (ιO m)‖ (QuadFormsKB.Tamagawa.detGram Q σ))]
    intro φ
    simp only [G, QuadFormsKB.Tamagawa.detGram, InfinitePlace.apply, RingHom.equivRatAlgHom_apply]
    rfl
  have h2 : ∏ φ : F →+* ℂ, G (InfinitePlace.mk φ) = ∏ w : InfinitePlace F, G w ^ w.mult := by
    rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ => G (InfinitePlace.mk φ))]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [Finset.prod_congr rfl fun φ hφ => by rw [(Finset.mem_filter.mp hφ).2], Finset.prod_const,
      InfinitePlace.card_filter_mk_eq]
  rw [h1, h2, QuadFormsKB.Siegel.betaInfNF, Fintype.prod_equiv
    (Equiv.subtypeUnivEquiv fun v => IsTotallyReal.isReal v)
    (fun w : QuadFormsKB.Siegel.RealPlace F => QuadFormsKB.Siegel.betaInfAt Q w (ιO m))
    (fun v => QuadFormsKB.Siegel.betaInfAt Q ⟨v, IsTotallyReal.isReal v⟩ (ιO m)) (fun w => rfl)]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hmult : w.mult = 1 := by simp [InfinitePlace.mult, IsTotallyReal.isReal w]
  rw [hmult, pow_one]
  simp only [G, QuadFormsKB.Tamagawa.archRepDensity, QuadFormsKB.Siegel.betaInfAt, gramDetNF_eq,
    siegel_realEmb_eq]
  have hw1 : w (ιO m) = realEmb F w (ιO m) := by rw [← abs_realEmb, abs_of_pos (hm w)]
  have hhalf : ∀ x : F, (1 / 2 : F) ^ N * x = x / 2 ^ N := fun x => by
    rw [one_div, inv_pow, div_eq_mul_inv, mul_comm]
  have hdet : ((gramF Q).map (realEmb F w)).det = w (ιO Q.hessian.det / 2 ^ N) := by
    have hp := (hQ w).det_pos
    rw [det_gramF_map, hhalf] at hp ⊢
    rw [← abs_realEmb, abs_of_pos hp]
  rw [hw1, ← hdet, ← n_mul_unitBallVol_div_two' hN]
  ring

/-- **The local side with a free value $P$:** `siegelProductWith Q₀ m P` $= |d_F|^{-(N-1)/2}\cdot$ `aEWithNF Q₀ m P`. -/
theorem siegelProductWith_eq_discr_mul_aEWithNF {N : ℕ} {Q : QuadForm (𝓞 F) N} (hQ : IsTotPosGram (gramF Q))
    (hN : 1 ≤ N) {m : 𝓞 F} (hm : ∀ v, 0 < realEmb F v (ιO m)) (P : ℝ) :
    QuadFormsKB.Tamagawa.siegelProductWith Q m P =
      (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (N - 1) * QuadFormsKB.Siegel.aEWithNF Q m P := by
  have hfac : |(discr F : ℝ)| ^ (-((N : ℝ) - 1) / 2) = (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (N - 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (abs_nonneg _), ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    rw [Nat.cast_sub hN]; push_cast; ring
  rw [QuadFormsKB.Tamagawa.siegelProductWith, hfac, archProd_eq_betaInfNF hQ hN hm, QuadFormsKB.Siegel.aEWithNF]
  ring

end QuadFormsKB.HilbertModular

namespace QuadFormsKB.Siegel

open QuadFormsKB.Tamagawa

/-- **The regularized value of $\prod_p\beta_p(m)$ for a ternary form over $\mathbb Z$** (regularized by $L(1,\chi_m)$):
$$P_{\mathrm{reg}}(m) = L(1,\chi_m)\prod_p\beta_p(m)\Bigl(1-\frac{\chi_m(p)}{p}\Bigr),\qquad \chi_m(p) = \Bigl(\frac{-2\det H\cdot m}{p}\Bigr)\ (p \nmid 2\det H),$$
computed through $Q\otimes\mathcal O_{\mathbb Q}$ (`RegProd.regProd` of `chiTern` and `NF.localDensity`; the primes of
$\mathcal O_{\mathbb Q}$ are the rational primes and `NF.localDensity_rat` gives $\beta_\mathfrak p = \beta_p$). The value to use as
$P$ in `SiegelFormula3` (`RatBridge3.siegelFormula3_iff_siegelFormulaAt3`). -/
@[kb "siegel1935" "Hauptsatz, n = 3, over ℚ (regularized Euler product) [unverified]"]
def eulerProductReg3 (Q : QuadForm ℤ 3) (m : ℤ) : ℝ :=
  RegProd.regProd (chiTern (RatBridge.up Q) (m : 𝓞 ℚ)) 1
    fun v => LocalDensity.NF.localDensity v (RatBridge.up Q) (m : 𝓞 ℚ)

end QuadFormsKB.Siegel

namespace QuadFormsKB.Tamagawa.RatBridge3

open QuadFormsKB.Lattices QuadFormsKB.HilbertModular RatBridge

variable (Q : QuadForm ℤ 3)

/-- **The rank-3 Siegel product over $\mathbb Q$ is Hanke's $\beta_\infty(m)\cdot P_{\mathrm{reg}}(m)$**: for $Q$ positive definite
and $m \ge 1$, `siegelProduct3 (up Q) m = Siegel.aEWith Q m (eulerProductReg3 Q m)` ($|d_{\mathbb Q}| = 1$, one real place). -/
theorem siegelProduct3_up (hQ : IntQF.PosDef Q) {m : ℤ} (hm : 1 ≤ m) :
    siegelProduct3 (up Q) (m : 𝓞 ℚ) = Siegel.aEWith Q m (Siegel.eulerProductReg3 Q m) := by
  have hpd := (isTotallyPosDef_up_iff Q).mpr hQ
  rw [siegelProduct3, siegelProductWith_eq_discr_mul_aEWithNF (isTotPosGram_Q₀ hpd) (by norm_num)
    (realEmb_intCast_pos hm), discrFactor_rat, one_mul]
  exact Siegel.aEWithNF_rat Q m _

/-- **Bridge: Hanke's rank-3 input is the regularized `SiegelFormulaAt3`** ($F = \mathbb Q$): for $Q$ positive definite
ternary over $\mathbb Z$, `Siegel.SiegelFormula3 Q (eulerProductReg3 Q)` ($r_{\mathrm{Gen}(Q)}(m) = \beta_\infty(m)P_{\mathrm{reg}}(m)$
for all $m \ge 1$) holds iff `SiegelFormulaAt3 (up Q) m` holds for every integer $m \ge 1$ (`mass_rat`, `repMass_rat`,
`siegelProduct3_up`). -/
@[kb "siegel1935" "Hauptsatz, n = 3, over ℚ: Hanke's form ⟺ SiegelFormulaAt3 [unverified]"]
theorem siegelFormula3_iff_siegelFormulaAt3 (hQ : IntQF.PosDef Q) :
    Siegel.SiegelFormula3 Q (Siegel.eulerProductReg3 Q) ↔ ∀ m : ℤ, 1 ≤ m → SiegelFormulaAt3 (up Q) (m : 𝓞 ℚ) := by
  have hpd := (isTotallyPosDef_up_iff Q).mpr hQ
  have hpos : 0 < Lattices.mass (formF (up Q)) (stdLat ℚ 3) := mass_pos hpd _ (isIntegral_stdLat (up Q))
  have key : ∀ m : ℤ, 1 ≤ m → (Siegel.genusRepAvg Q m = Siegel.aEWith Q m (Siegel.eulerProductReg3 Q m) ↔
      SiegelFormulaAt3 (up Q) (m : 𝓞 ℚ)) := by
    intro m hm
    rw [Siegel.genusRepAvg, mass_rat Q hQ, repMass_rat Q hQ, div_eq_iff hpos.ne', ← siegelProduct3_up Q hQ hm]
    constructor
    · intro h; exact ⟨by rw [map_intCast, h, mul_comm]⟩
    · intro h; have := h.repMass_eq; rw [map_intCast] at this; rw [mul_comm]; exact this
  exact ⟨fun h m hm => (key m hm).mp (h.genusRepAvg_eq m hm), fun h => ⟨fun m hm => (key m hm).mpr (h m hm)⟩⟩

/-- **`SiegelFormulaAt3` over $\mathbb Q$ from Hanke's regularized input**, for every totally positive $m$. -/
theorem siegelFormulaAt3_of_siegelFormula3 {Q₀ : QuadForm (𝓞 ℚ) 3} (hpd : IsTotallyPosDef (formF Q₀))
    (hS : Siegel.SiegelFormula3 (down Q₀) (Siegel.eulerProductReg3 (down Q₀))) {m : 𝓞 ℚ}
    (hm : ∀ v : InfinitePlace ℚ, 0 < realEmb ℚ v (algebraMap (𝓞 ℚ) ℚ m)) : SiegelFormulaAt3 Q₀ m := by
  obtain ⟨k, hk, rfl⟩ := exists_int_of_pos hm
  have h := (siegelFormula3_iff_siegelFormulaAt3 (down Q₀) (posDef_down hpd)).mp hS k hk
  rwa [up_down] at h

end QuadFormsKB.Tamagawa.RatBridge3
