/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.SiegelLatRank2
import QuadFormsKB.Tamagawa.SiegelRank3NF

/-!
# Natural-order Euler products for every genus, ranks 2 and 3
**Layer:** $F$ a totally real number field (any class number), $Q_0$ a totally positive definite form over $\mathcal O_F$ in $2$ or
$3$ variables, $L$ **any** lattice on $(F^N, Q_0)$ with $Q_0$ integral on $L$ (any Steinitz class), $m \in \mathcal O_F$ totally
positive.

**Proves** (the lattice versions of `siegelFormulaAt3_natural_nf` and `siegelFormulaAt2_natural_nf`):
* **`siegelFormulaAt3Lat_natural`**: given `NaturalOrderEulerOne (chiTern Q₀ m)`, the partial products
  $\prod_{N\mathfrak p\le X}\beta_\mathfrak p(L, m)$ converge to the regularized value
  $L_F(1,\chi_m)\prod_\mathfrak p\beta_\mathfrak p(L,m)(1-\chi_m(\mathfrak p)/N\mathfrak p)$ used in `siegelProduct3Lat`, and
  `SiegelFormulaAt3Lat Q₀ L m` holds.
* **`siegelFormulaAt2Lat_natural`**: given `NaturalOrderEulerOne (chiP · Q)`, the partial products
  $\prod_{N\mathfrak p\le X}\beta_\mathfrak p(L, m)$ converge to $L_F(1,\chi_Q)^{-1}\prod_\mathfrak p\beta_\mathfrak p(L,m)
  (1-\chi_Q(\mathfrak p)/N\mathfrak p)^{-1}$ (`siegelProduct2RegLat`), and `SiegelFormulaAt2Lat Q L m` holds.

**Route.** The correction factors are those of $\mathcal O_F^N$ (the characters depend on $Q_0$ and $m$ only); $\beta_\mathfrak p(L, m) =
\beta_\mathfrak p(\mathcal O_F^N, m)$ wherever $L_\mathfrak p = \mathfrak o_\mathfrak p^N$ (`latBeta_eq_of_loc_std`), i.e. at all but finitely many
primes. So the absolute convergence of the corrected product transfers from $\mathcal O_F^N$ (rank 3: the eventual bound
$|\beta(1-\chi/N\mathfrak p) - 1| \le N\mathfrak p^{-2}$; rank 2: finite multiplicative support, or a zero factor when $m$ is not represented
over $F$), and `hasProd_normOrder_regProd` / its rank-2 twin give the natural order.

The only input is `NaturalOrderEulerOne` (already classified: a prime ideal theorem for the quadratic character over $F$,
convention-level; a theorem over $\mathbb Q$).

Source: Siegel 1935, Hauptsatz; Hanke 2004, (5.3), p. 368 (natural order) [unverified locators for $F$].
-/

open NumberField IsDedekindDomain Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.SiegelLat

open QuadFormsKB.Lattices QuadFormsKB.LocalDensity QuadFormsKB.QuadForm QuadFormsKB.HilbertModular QuadFormsKB.NFEuler
open QuadFormsKB.RegProd

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-- $\beta_\mathfrak p(L, m) = \beta_\mathfrak p(\mathcal O_F^N, m)$ for all but finitely many $\mathfrak p$. -/
theorem latBeta_eventually_eq_localDensity {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (L : Lat F N)
    (hLi : Lattices.IsIntegral (formF Q₀) L.1) (m : 𝓞 F) :
    ∀ᶠ v in cofinite, latBeta v Q₀ L m = NF.localDensity v Q₀ m := by
  filter_upwards [loc_eventually_std L.2] with v hv
  exact latBeta_eq_of_loc_std v Q₀ L hLi hv m

/-! ### Rank 3 -/

/-- **The corrected rank-3 product of an arbitrary lattice converges absolutely:**
$\prod_\mathfrak p\beta_\mathfrak p(L,m)(1-\chi_m(\mathfrak p)/N\mathfrak p)$ is unconditionally multipliable (its factors are
$1 - N\mathfrak p^{-2}$ outside the finitely many $\mathfrak p \mid 2m\det H$ with $L_\mathfrak p \ne \mathfrak o_\mathfrak p^3$). -/
theorem multipliable_latBeta_mul_chiTern {Q₀ : QuadForm (𝓞 F) 3} (hQ : Q₀.Nondegenerate) (L : Lat F 3)
    (hLi : Lattices.IsIntegral (formF Q₀) L.1) {m : 𝓞 F} (hm : m ≠ 0) :
    Multipliable fun v => latBeta v Q₀ L m * (1 - chiTern Q₀ m v / (normP v : ℝ)) ^ (1 : ℤ) := by
  refine multipliable_of_abs_sub_one_le _ (C := 1) (σ := 2) (by norm_num) ?_
  filter_upwards [(Siegel.finite_mem_asIdeal (two_mul_det_mul_ne_zero' hQ hm)).eventually_cofinite_notMem,
    latBeta_eventually_eq_localDensity Q₀ L hLi m] with v hv hβ
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_right _ h))
  have hd : Q₀.hessian.det ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_left _ h))
  have hmv : m ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_left _ h)
  have hm2 : m ∉ v.asIdeal ^ 2 := fun h => hmv (Ideal.pow_le_self two_ne_zero h)
  rw [hβ, zpow_one, localDensity_mul_one_sub_chiTern Q₀ m v ⟨h2, hd⟩ hm2]
  have hN : (2 : ℝ) ≤ (normP v : ℝ) := by exact_mod_cast two_le_normP v
  rw [show (1 : ℝ) - 1 / (normP v : ℝ) ^ 2 - 1 = -(1 / (normP v : ℝ) ^ 2) by ring, abs_neg,
    abs_of_pos (by positivity), one_mul, Real.rpow_neg (by linarith), Real.rpow_two, one_div]

/-- **Siegel's formula in rank 3 for every genus, natural order** (Siegel 1935, Hauptsatz; Hanke 2004, (5.3), p. 368, over $F$):
given `NaturalOrderEulerOne (chiTern Q₀ m)` (prime ideal theorem for $\chi_m$; convention input), for every lattice $L$ with $Q_0$
integral on $L$, $\lim_X\prod_{N\mathfrak p\le X}\beta_\mathfrak p(L, m)$ is the regularized value in `siegelProduct3Lat`, and
`SiegelFormulaAt3Lat Q₀ L m`. -/
@[kb "hanke2004" "(5.3), p. 368 (n = 3, natural order), every genus, over a totally real field"]
theorem siegelFormulaAt3Lat_natural (Q₀ : QuadForm (𝓞 F) 3) (hpd : IsTotallyPosDef (formF Q₀))
    (L : Lat F 3) (hLi : Lattices.IsIntegral (formF Q₀) L.1) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (hN : NaturalOrderEulerOne (chiTern Q₀ m)) :
    HasProd (fun v => latBeta v Q₀ L m) (regProd (chiTern Q₀ m) 1 fun v => latBeta v Q₀ L m) (normOrder F) ∧
      SiegelFormulaAt3Lat Q₀ L m := by
  refine ⟨?_, siegelFormulaAt3Lat_totallyReal Q₀ hpd L hLi hm⟩
  have hQ : Q₀.Nondegenerate := nondegenerate_of_isTotallyPosDef hpd
  have hm0 : m ≠ 0 := by
    rintro rfl
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
    simpa using hm v
  have hmul := multipliable_latBeta_mul_chiTern hQ L hLi hm0
  simp only [zpow_one] at hmul
  exact hasProd_normOrder_regProd hN (fun v => abs_chiTern_le v Q₀ m) hmul.hasProd

/-! ### Rank 2 -/

/-- **The corrected rank-2 product of an arbitrary lattice converges unconditionally:** finite multiplicative support when $m$ is
represented over $F$ (that of $\mathcal O_F^2$, `two_mul_tamagawaKReg_mul_repMass_frame2`, changed at finitely many primes), a zero
factor otherwise (`exists_latBeta_eq_zero_of_not_rep`). -/
theorem exists_hasProd_latBeta_mul_chiP (Q : QuadForm (𝓞 F) 2) (hpd : IsTotallyPosDef (formF Q))
    (L : Lat F 2) (hLi : Lattices.IsIntegral (formF Q) L.1) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    ∃ P, HasProd (fun v => latBeta v Q L m * (1 - chiP v Q / (normP v : ℝ)) ^ (-1 : ℤ)) P := by
  by_cases h : ∃ ξ, (formF Q).eval ξ = algebraMap (𝓞 F) F m
  · obtain ⟨ξ, hξ⟩ := h
    have hρ : algebraMap (𝓞 F) F m ≠ 0 :=
      (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (ne_zero_of_totallyPos hm)
    obtain ⟨fr⟩ := exists_adaptedFrame (n := 1) (formF Q) hξ hρ
    have hstd := (two_mul_tamagawaKReg_mul_repMass_frame2 Q hpd hm fr).2
    have hfin : Function.HasFiniteMulSupport
        fun v => latBeta v Q L m * (1 - chiP v Q / (normP v : ℝ)) ^ (-1 : ℤ) := by
      have hS := Filter.eventually_cofinite.mp (latBeta_eventually_eq_localDensity Q L hLi m)
      refine (hstd.union hS).subset fun v hv => ?_
      by_contra hc
      simp only [Set.mem_union, Function.mem_mulSupport, Set.mem_ofPred_eq, not_or, not_not] at hc
      apply hv
      show latBeta v Q L m * _ = 1
      rw [hc.2]; exact hc.1
    exact ⟨_, (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hfin).hasProd⟩
  · obtain ⟨v, h0⟩ := exists_latBeta_eq_zero_of_not_rep (n := 1) Q hpd L hLi hm h
    exact ⟨0, hasProd_zero_of_exists_eq_zero ⟨v, by simp only [h0, zero_mul]⟩⟩

/-- **Siegel's formula in rank 2 for every genus, natural order** (Siegel 1935, Hauptsatz, $n = 2$, over $F$): given
`NaturalOrderEulerOne (chiP · Q)` (prime ideal theorem for $\chi_Q$; convention input), for every lattice $L$ with $Q$ integral on
$L$, $\lim_X\prod_{N\mathfrak p\le X}\beta_\mathfrak p(L, m)$ is the regularized value
$L_F(1,\chi_Q)^{-1}\prod_\mathfrak p\beta_\mathfrak p(L,m)(1-\chi_Q(\mathfrak p)/N\mathfrak p)^{-1}$ in `siegelProduct2RegLat`, and
`SiegelFormulaAt2Lat Q L m`. -/
@[kb "siegel1935" "Hauptsatz, n = 2 (natural order), every genus, over a totally real field [unverified]"]
theorem siegelFormulaAt2Lat_natural (Q : QuadForm (𝓞 F) 2) (hpd : IsTotallyPosDef (formF Q))
    (L : Lat F 2) (hLi : Lattices.IsIntegral (formF Q) L.1) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (hN : NaturalOrderEulerOne fun v => chiP v Q) :
    HasProd (fun v => latBeta v Q L m) (regProd (fun v => chiP v Q) (-1) fun v => latBeta v Q L m) (normOrder F) ∧
      SiegelFormulaAt2Lat Q L m := by
  refine ⟨?_, siegelFormulaAt2Lat_totallyReal Q hpd L hLi hm⟩
  set χ : HeightOneSpectrum (𝓞 F) → ℝ := fun v => chiP v Q
  set β : HeightOneSpectrum (𝓞 F) → ℝ := fun v => latBeta v Q L m
  obtain ⟨P, hP⟩ := exists_hasProd_latBeta_mul_chiP Q hpd L hLi hm
  obtain ⟨hL0, -⟩ := lOne_chiP_binary hpd
  have hinv := hasProd_zpow hN.hasProd hL0.ne' (-1)
  have h := hP.normOrder.mul hinv
  have e : regProd χ (-1) β = P * LOne χ ^ (-1 : ℤ) := by
    simp only [regProd, χ, β, hP.tprod_eq]; ring
  rw [e]
  refine h.congr_fun fun v => ?_
  have hl : 1 - χ v / (normP v : ℝ) ≠ 0 := (one_sub_div_pos (abs_chiP_le Q v) v).ne'
  simp only [_root_.zpow_neg_one, inv_inv]
  rw [mul_assoc, inv_mul_cancel₀ hl, mul_one]

end QuadFormsKB.Tamagawa.SiegelLat
