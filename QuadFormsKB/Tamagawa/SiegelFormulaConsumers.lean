import QuadFormsKB.Tamagawa.TernaryRamDyadicLocal
import QuadFormsKB.Siegel.HeckeBound
import QuadFormsKB.Siegel.StableSquareClasses

/-!
# Hanke's §5–§6 genus statements without the input `SiegelFormula`

The corollaries of Siegel's formula in `Siegel/Formula.lean`, `Siegel/GlobalLowerBound.lean`,
`Siegel/StableSquareClasses.lean` and `Siegel/MainResults.lean` take `SiegelFormula Q` as a hypothesis. It is a theorem
for every positive definite integral form in $n \ge 4$ variables (`Tamagawa.siegelFormula_int_all_ranks_uncond`), the
scope of all of them. This file states them with the input discharged:

* unconditional: Thm 5.4 (`thm_5_4_genus_uncond`), (5.13) (`eq_5_13_genus_uncond`), Thm 5.7(b), (c)
  (`thm_5_7_b_genus_uncond`, `thm_5_7_c_even_genus_uncond`, `thm_5_7_c_odd_genus_uncond`), the global lower bound behind
  $\hat\Lambda_4$ (`hglob_four_uncond`, `hglob_four_min_uncond`) and $r_Q(m) = a_E(m) + c(m)$
  (`repNum_eq_aE_add_genusCuspCoeff_uncond`);
* Thm 6.3, Remark 6.5.1 and Thm 6.4 ($n$ odd) with `SiegelFormula` and `ThetaSplit` discharged (`thm_6_3_cusp`,
  `thm_6_3_F4_cusp`, `thm_6_4_even_cusp`, `thm_6_4_odd_cusp`), for the coefficients $c$ = `genusCuspCoeff` of
  $\Theta_Q - \Theta_{\mathrm{Gen}(Q)}$. These remain conditional on the cusp-form bounds `CuspBound` (Deligne's exponent)
  and `CuspBoundUniform` (Hanke's Assumption 4.4), which are open.

For $n = 3$ (`SiegelFormula3`) the unconditional versions are in `Tamagawa/RatHeadline3Uncond.lean`.
-/

namespace QuadFormsKB.Siegel

open LocalDensity

variable {n : ℕ}

/-- `SiegelFormula Q` for $Q$ positive definite in $n \ge 4$ variables (`Tamagawa.siegelFormula_int_all_ranks_uncond`). -/
theorem siegelFormula_of_posDef (Q : IntQF n) (hQ : IntQF.PosDef Q) (hn : 4 ≤ n) : SiegelFormula Q :=
  Tamagawa.siegelFormula_int_all_ranks_uncond hn Q hQ

/-- **$r_Q(m) = a_E(m) + c(m)$, unconditionally** (Hanke 2004, (4.3) with (5.3)): for $Q$ positive definite in $n \ge 4$
variables and $m \ge 1$, $r_Q(m) = \beta_\infty(m)\prod_p\beta_p(m) + c(m)$ with $c$ = `genusCuspCoeff` the coefficients of
$\Theta_Q - \Theta_{\mathrm{Gen}(Q)}$. -/
@[kb "hanke2004" "(4.3) with (5.3), pp. 365, 368"]
theorem repNum_eq_aE_add_genusCuspCoeff_uncond {Q : IntQF n} (hQ : IntQF.PosDef Q) (hn : 4 ≤ n) {m : ℕ}
    (hm : 1 ≤ m) : (repNum Q m : ℝ) = aE Q m + genusCuspCoeff Q m :=
  repNum_eq_aE_add_genusCuspCoeff (siegelFormula_of_posDef Q hQ hn) hm

open Classical in
/-- **Theorem 5.4** (Hanke 2004, p. 369) for the genus average, unconditionally: for $Q$ positive definite in $n \ge 4$
variables, $S$ a finite set of primes, $T' > 0$ $p$-stable at every $p \in S$ and $m' = \prod_{p \in S}p^{\nu_p}$,
$$a_E(T'(m')^2) = a_E(T')\prod_{p \in S \cap \mathrm{Iso}}\Big[C_p(T') + \frac{1 - C_p(T')}{p^{(n-2)\nu_p}}\Big]
  \big((m')_{\mathrm{Iso}}\big)^{n-2}.$$ `thm_5_4_genus` with `SiegelFormula` discharged. -/
@[kb "hanke2004" "Thm 5.4, p. 369"]
theorem thm_5_4_genus_uncond (Q : IntQF n) (hQ : IntQF.PosDef Q) (hn : 4 ≤ n)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin n)) {T : ℤ} (hT : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (ν : ℕ → ℕ) :
    genusRepAvg Q (T * sqPart S ν ^ 2) = genusRepAvg Q T *
      (∏ p ∈ S.filter (IsIsotropicPrime Q),
        (localConstC Q p T + (1 - localConstC Q p T) / (p : ℝ) ^ ((n - 2) * ν p))) *
      (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (n - 2) :=
  thm_5_4_genus Q (siegelFormula_of_posDef Q hQ hn) hQ.nondegenerate hn hS S₀ hT hst ν

open Classical in
/-- **(5.13)** (Hanke 2004, p. 373) for the genus average, unconditionally: for $Q$ positive definite in $n \ge 4$
variables, $a_E(T'(m')^2) \ge a_E(T')\,((m')_{\mathrm{Iso}})^{n-2}\prod_{p \in S \cap \mathrm{Iso}}C'_p(T')$.
`eq_5_13_genus` with `SiegelFormula` discharged. -/
@[kb "hanke2004" "(5.13), p. 373"]
theorem eq_5_13_genus_uncond (Q : IntQF n) (hQ : IntQF.PosDef Q) (hn : 4 ≤ n)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin n)) {T : ℤ} (hT : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (ν : ℕ → ℕ) :
    genusRepAvg Q T * (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (n - 2) *
        ∏ p ∈ S.filter (IsIsotropicPrime Q), localConstC' Q p T ≤
      genusRepAvg Q (T * sqPart S ν ^ 2) :=
  eq_5_13_genus Q (siegelFormula_of_posDef Q hQ hn) hQ hn hS S₀ hT hst ν

open Classical in
/-- **Theorem 5.7(b)** (Hanke 2004, p. 373) for the genus average, $n = 4$, ratio form, unconditionally.
`thm_5_7_b_genus` with `SiegelFormula` discharged. -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (ratio form)"]
theorem thm_5_7_b_genus_uncond (Q : IntQF 4) (hQ : IntQF.PosDef Q) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin 4)) {T : ℤ} (hT : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T)
    (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ) :
    genusRepAvg Q T * (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ 2 *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) *
        ∏ p ∈ (S.filter (IsGoodPrime Q)).filter
            (fun p => jacobiSym Q.hessian.det p = -1 ∧ ¬ (p : ℤ) ∣ T),
          (1 + 1 / (p : ℝ))⁻¹ ≤
      genusRepAvg Q (T * sqPart S ν ^ 2) :=
  thm_5_7_b_genus Q (siegelFormula_of_posDef Q hQ le_rfl) hQ hS S₀ hT hst hT2 ν

open Classical in
/-- **Theorem 5.7(c), $n \ge 4$ even** (Hanke 2004, p. 373) for the genus average, ratio form, unconditionally.
`thm_5_7_c_even_genus` with `SiegelFormula` discharged. -/
@[kb "hanke2004" "Thm 5.7(b),(c), p. 373 (ratio form, n even)"]
theorem thm_5_7_c_even_genus_uncond (Q : IntQF n) (hQ : IntQF.PosDef Q)
    (hn : 4 ≤ n) (heven : Even n) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin n))
    {T : ℤ} (hT : 0 < T) (hst : ∀ p ∈ S, IsPStable Q S₀ p T)
    (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ) :
    genusRepAvg Q T * (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (n - 2) *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) *
        ∏ p ∈ (S.filter (IsGoodPrime Q)).filter
            (fun p => jacobiSym ((-1) ^ (n / 2) * Q.hessian.det) p = -1 ∧ ¬ (p : ℤ) ∣ T),
          (p : ℝ) ^ ((n - 2) / 2) / ((p : ℝ) ^ ((n - 2) / 2) + 1) ≤
      genusRepAvg Q (T * sqPart S ν ^ 2) :=
  thm_5_7_c_even_genus Q (siegelFormula_of_posDef Q hQ hn) hQ hn heven hS S₀ hT hst hT2 ν

open Classical in
/-- **Theorem 5.7(c), $n \ge 5$ odd** (Hanke 2004, p. 373) for the genus average, ratio form, unconditionally.
`thm_5_7_c_odd_genus` with `SiegelFormula` discharged. -/
@[kb "hanke2004" "Thm 5.7(c), p. 373 (ratio form, n odd)"]
theorem thm_5_7_c_odd_genus_uncond (Q : IntQF n) (hQ : IntQF.PosDef Q)
    (hn : 4 ≤ n) (hodd : Odd n) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin n))
    {T : ℤ} (hT : 0 < T) (hst : ∀ p ∈ S, IsPStable Q S₀ p T)
    (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ) :
    genusRepAvg Q T * (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (n - 2) *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) *
        ∏ p ∈ (S.filter (IsGoodPrime Q)).filter (fun p : ℕ => ¬ (p : ℤ) ∣ T ∧
            jacobiSym ((-1) ^ ((n - 1) / 2) * (2 * Q.hessian.det) * T) p = 1),
          (1 - 1 / (p : ℝ) ^ ((n - 1) / 2)) / (1 - 1 / (p : ℝ) ^ (n - 2)) ≤
      genusRepAvg Q (T * sqPart S ν ^ 2) :=
  thm_5_7_c_odd_genus Q (siegelFormula_of_posDef Q hQ hn) hQ hn hodd hS S₀ hT hst hT2 ν

open Classical in
/-- **The global lower bound behind $\hat\Lambda_4$, unconditionally** (Hanke 2004, Thm 5.7(b), p. 373): for $Q$ positive
definite quaternary, $S$ a finite set of primes and $T' \ge 1$,
$$\hat\Lambda_4(S, T')\,(T')_{\mathrm{Iso}}\prod_{\substack{p \mid T'\ \mathrm{good}\\ \chi(p) = -1}}\frac{p-1}{p+1}
  \;\le\; a_E(T')\prod_{p \in S \cap \mathrm{Iso},\ p\ \mathrm{bad}}C'_p(T').$$ `hglob_four` with `SiegelFormula`
discharged. -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (global bound, n = 4)"]
theorem hglob_four_uncond (Q : IntQF 4) (hQ : IntQF.PosDef Q) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) {T : ℕ} (hT : 0 < T) :
    lambdaHat4 Q S T * isoPart Q T *
        ∏ p ∈ T.primeFactors.filter (fun p => IsGoodPrime Q p ∧ jacobiSym Q.hessian.det p = -1),
          ((p : ℝ) - 1) / ((p : ℝ) + 1) ≤
      genusRepAvg Q T *
        ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T :=
  hglob_four Q hQ (siegelFormula_of_posDef Q hQ le_rfl) hS hT

open Classical in
/-- **Theorem 5.7(b) over $\mathbb{Q}$, global form with the minimum over $B_{\mathbb T}$, unconditionally**: for $Q$
positive definite quaternary, $S$ a finite set of primes and $T' \in \mathcal T$ (positive, bad-reduced),
$$\hat\Lambda_4^{\min}(\mathcal T)\,(T')_{\mathrm{Iso}}\prod_{\substack{p \mid T'\ \mathrm{good}\\ \chi(p) = -1}}\frac{p-1}{p+1}
  \le a_E(T')\prod_{p \in S \cap \mathrm{Iso},\ p\ \mathrm{bad}}C'_p(T').$$ `hglob_four_min` with `SiegelFormula`
discharged. -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (global, min over B_T, over Q)"]
theorem hglob_four_min_uncond (Q : IntQF 4) (hQ : IntQF.PosDef Q) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) {𝒯 : Set ℕ} (h𝒯 : ∀ T ∈ 𝒯, 0 < T ∧ IsBadReduced Q T) {T : ℕ} (hT : T ∈ 𝒯) :
    lambdaHat4Min Q 𝒯 * isoPart Q T *
        ∏ p ∈ T.primeFactors.filter (fun p => IsGoodPrime Q p ∧ jacobiSym Q.hessian.det p = -1),
          ((p : ℝ) - 1) / ((p : ℝ) + 1) ≤
      genusRepAvg Q T *
        ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T :=
  hglob_four_min Q hQ (siegelFormula_of_posDef Q hQ le_rfl) hS h𝒯 hT

open Classical in
/-- **Theorem 6.3** (Hanke 2004, p. 381) **conditional on the cusp-form bound only**: `thm_6_3` with `SiegelFormula` and
`ThetaSplit` discharged, for $c$ = `genusCuspCoeff Q` (the coefficients of $\Theta_Q - \Theta_{\mathrm{Gen}(Q)}$). For $Q$
positive definite quaternary, if $|c(m)| \le C\,\tau(m)\,m^{1/2}$ (`CuspBound`, Deligne's exponent), then under the
hypotheses of `thm_6_3` on $m = T'(m')^2$ and the global bound `hglob`, $Q$ represents $m$ whenever
$$\frac{C}{\Lambda}\,\tau((m)_{\mathrm{Aniso}})\sqrt{(m)_{\mathrm{Aniso}}} < \frac{\sqrt{(m)_{\mathrm{Iso}}}}{\tau((m)_{\mathrm{Iso}})}
  \prod_{\substack{p \mid m\ \mathrm{good}\\ \chi(p) = -1}}\frac{p-1}{p+1}.$$ -/
@[kb "hanke2004" "Thm 6.3, p. 381 (modulo (4.8))"]
theorem thm_6_3_cusp (Q : IntQF 4) (hQ : IntQF.PosDef Q) {C : ℝ}
    (hCB : CuspBound (genusCuspCoeff Q) (1 / 2) C)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin 4)) {T : ℕ} (hT : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T)
    (ν : ℕ → ℕ) (hν : ∀ p ∈ S, 1 ≤ ν p) {Λ : ℝ} (hΛ : 0 < Λ)
    (hglob : Λ * isoPart Q T *
        ∏ p ∈ T.primeFactors.filter (fun p => IsGoodPrime Q p ∧ jacobiSym Q.hessian.det p = -1),
          ((p : ℝ) - 1) / ((p : ℝ) + 1) ≤
      genusRepAvg Q T *
        ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T)
    {m : ℕ} (hm : m = T * (∏ p ∈ S, p ^ ν p) ^ 2)
    (hbound : C / Λ * divCount (anisoPart Q m) * √(anisoPart Q m : ℝ) <
      √(isoPart Q m : ℝ) / divCount (isoPart Q m) *
        ∏ p ∈ m.primeFactors.filter (fun p => IsGoodPrime Q p ∧ jacobiSym Q.hessian.det p = -1),
          ((p : ℝ) - 1) / ((p : ℝ) + 1)) :
    IntQF.Represents Q m :=
  thm_6_3 Q hQ (siegelFormula_of_posDef Q hQ le_rfl) (thetaSplit_genusCuspCoeff Q) hCB hS S₀ hT hst hT2 ν hν hΛ
    hglob hm hbound

open Classical in
/-- **Remark 6.5.1 with Theorem 6.3** (Hanke 2004, p. 383) **conditional on the cusp-form bound only**: `thm_6_3_F4` with
`SiegelFormula` and `ThetaSplit` discharged, for $c$ = `genusCuspCoeff Q`. If $|c(m)| \le C\,\tau(m)\,m^{1/2}$
(`CuspBound`) and $m = (m)_{\mathrm{Iso}}$, then under the hypotheses of `thm_6_3_cusp`, $Q$ represents $m$ as soon as
$F_4(m) > C/\Lambda$. -/
@[kb "hanke2004" "Remark 6.5.1, p. 383; Thm 6.3, p. 381 (modulo (4.8))"]
theorem thm_6_3_F4_cusp (Q : IntQF 4) (hQ : IntQF.PosDef Q) {C : ℝ}
    (hCB : CuspBound (genusCuspCoeff Q) (1 / 2) C)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin 4)) {T : ℕ} (hT : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T)
    (ν : ℕ → ℕ) (hν : ∀ p ∈ S, 1 ≤ ν p) {Λ : ℝ} (hΛ : 0 < Λ)
    (hglob : Λ * isoPart Q T *
        ∏ p ∈ T.primeFactors.filter (fun p => IsGoodPrime Q p ∧ jacobiSym Q.hessian.det p = -1),
          ((p : ℝ) - 1) / ((p : ℝ) + 1) ≤
      genusRepAvg Q T *
        ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T)
    {m : ℕ} (hm : m = T * (∏ p ∈ S, p ^ ν p) ^ 2) (hiso : isoPart Q m = m)
    (hbound : C / Λ < F4 Q.hessian.det.natAbs
      (fun p : ℕ => if p = 2 then (0 : ℤ) else jacobiSym Q.hessian.det p) m) :
    IntQF.Represents Q m :=
  thm_6_3_F4 Q hQ (siegelFormula_of_posDef Q hQ le_rfl) (thetaSplit_genusCuspCoeff Q) hCB hS S₀ hT hst hT2 ν hν
    hΛ hglob hm hiso hbound

open Classical in
/-- **Theorem 6.4, $n$ even** (Hanke 2004, p. 382) **conditional on the cusp-form bound only**: `thm_6_4_even` with
`SiegelFormula` and `ThetaSplit` discharged, for $c$ = `genusCuspCoeff Q`. For $Q$ positive definite in $n \ge 5$
variables, $n$ even, if $|c(m)| \le C\,\tau(m)\,m^{(n-2)/4}$ (`CuspBound`, Deligne's exponent), then under the hypotheses
of `thm_6_4_even` on $m = T'(m')^2$ and the global bound `hglob`, $Q$ represents $m$ whenever
$m^{(n-2)/4}/\tau(m) > C/\Lambda$. (With Hecke's exponent and no cusp-form input: `thm_6_4_even_uncond`.) -/
@[kb "hanke2004" "Thm 6.4, p. 382 (n even, modulo (4.8))"]
theorem thm_6_4_even_cusp (Q : IntQF n) (hQ : IntQF.PosDef Q) (hn : 5 ≤ n) (heven : Even n) {C : ℝ}
    (hCB : CuspBound (genusCuspCoeff Q) (((n : ℝ) - 2) / 4) C)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hIso : ∀ p ∈ S, IsIsotropicPrime Q p)
    (S₀ : Finset (Fin n)) {T : ℕ} (hT : 0 < T) (hst : ∀ p ∈ S, IsPStable Q S₀ p T)
    (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ) {Λ : ℝ} (hΛ : 0 < Λ)
    (hglob : Λ * (T : ℝ) ^ ((n - 2) / 2) ≤ genusRepAvg Q T *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) *
        ∏ p ∈ (S.filter (IsGoodPrime Q)).filter
            (fun p => jacobiSym ((-1) ^ (n / 2) * Q.hessian.det) p = -1 ∧ ¬ (p : ℤ) ∣ T),
          (p : ℝ) ^ ((n - 2) / 2) / ((p : ℝ) ^ ((n - 2) / 2) + 1))
    {m : ℕ} (hm : m = T * (∏ p ∈ S, p ^ ν p) ^ 2)
    (hbound : C / Λ < (m : ℝ) ^ (((n : ℝ) - 2) / 4) / divCount m) :
    IntQF.Represents Q m :=
  thm_6_4_even Q hQ hn heven (siegelFormula_of_posDef Q hQ (by omega)) (thetaSplit_genusCuspCoeff Q) hCB hS hIso
    S₀ hT hst hT2 ν hΛ hglob hm hbound

open Classical in
/-- **Theorem 6.4, $n$ odd** (Hanke 2004, p. 382) **conditional on Hanke's Assumption 4.4 only**: `thm_6_4_odd` with
`SiegelFormula` and `ThetaSplit` discharged, for $c$ = `genusCuspCoeff Q`. For $Q$ positive definite in $n \ge 5$
variables, $n$ odd, if $|c(tm_0^2)| \le B\,t^{(n-1)/4-\eta+\varepsilon'}\tau(m_0)^2m_0^{(n-2)/2}$ (`CuspBoundUniform`), then
under the hypotheses of `thm_6_4_odd` on $m = T'(m')^2 = tm_0^2$ and the global bound `hglob`, $Q$ represents $m$
whenever $$\frac{t^{(n-3)/4+\eta-\varepsilon'}\,m_0^{(n-2)/2}}{\tau(m_0)^2} > \frac{B}{\Lambda}.$$ -/
@[kb "hanke2004" "Thm 6.4, p. 382 (n odd, modulo Assumption 4.4)"]
theorem thm_6_4_odd_cusp (Q : IntQF n) (hQ : IntQF.PosDef Q) (hn : 5 ≤ n) (hodd : Odd n) {B η ε' : ℝ}
    (hCB : CuspBoundUniform (genusCuspCoeff Q) (((n : ℝ) - 2) / 2) (((n : ℝ) - 1) / 4 - η + ε') B)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hIso : ∀ p ∈ S, IsIsotropicPrime Q p)
    (S₀ : Finset (Fin n)) {T : ℕ} (hT : 0 < T) (hst : ∀ p ∈ S, IsPStable Q S₀ p T)
    (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ) {Λ : ℝ} (hΛ : 0 < Λ)
    (hglob : Λ * (T : ℝ) ^ (((n : ℝ) - 2) / 2) ≤ genusRepAvg Q T *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) *
        ∏ p ∈ (S.filter (IsGoodPrime Q)).filter (fun p : ℕ => ¬ (p : ℤ) ∣ T ∧
            jacobiSym ((-1) ^ ((n - 1) / 2) * (2 * Q.hessian.det) * T) p = 1),
          (1 - 1 / (p : ℝ) ^ ((n - 1) / 2)) / (1 - 1 / (p : ℝ) ^ (n - 2)))
    {m : ℕ} (hm : m = T * (∏ p ∈ S, p ^ ν p) ^ 2) {t m₀ : ℕ} (ht : Squarefree t)
    (hmt : m = t * m₀ ^ 2)
    (hbound : B / Λ < (t : ℝ) ^ (((n : ℝ) - 3) / 4 + η - ε') * (m₀ : ℝ) ^ (((n : ℝ) - 2) / 2) /
      (divCount m₀ : ℝ) ^ 2) :
    IntQF.Represents Q m :=
  thm_6_4_odd Q hQ hn hodd (siegelFormula_of_posDef Q hQ (by omega)) (thetaSplit_genusCuspCoeff Q) hCB hS hIso
    S₀ hT hst hT2 ν hΛ hglob hm ht hmt hbound

end QuadFormsKB.Siegel
