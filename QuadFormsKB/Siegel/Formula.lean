/-
# Siegel's formula as a cited input, and its consequences

**Inputs (hypothesis structures, not proved):**
- `SiegelFormula Q`: $a_E(m) = \beta_\infty(m)\prod_p\beta_p(m)$ (`genusRepAvg Q m = aE Q m`) for all $m \ge 1$; Siegel's
  Hauptsatz (Siegel 1935), Hanke 2004 (5.3), p. 368. Use for $n \ge 4$.
- `SiegelFormula3 Q P`: the same with the Euler product replaced by a chosen value $P(m)$
  (`genusRepAvg Q m = aEWith Q m (P m)`), for $n = 3$ where the product converges only conditionally and the
  convention is undecided.

**Conditional corollaries** (one-line transfers of `Siegel/MainTerm.lean`): Thm 5.4, (5.13) and Thm 5.7(a)–(c) in
ratio form for the genus average $a_E(m)$ itself.
-/
import QuadFormsKB.Siegel.MainTerm

namespace QuadFormsKB.Siegel

open LocalDensity

variable {n : ℕ}

/-- **Input: Siegel's formula** (Siegel 1935, Hauptsatz [unverified]; Hanke 2004, (5.3), p. 368): for every $m \ge 1$
the genus average of representation numbers equals the product of the local densities,
$$a_E(m) = \frac{1}{\mathrm{Mass}(Q)}\sum_{[Q'] \in \mathrm{Gen}(Q)}\frac{r_{Q'}(m)}{|\mathrm{Aut}(Q')|}
  = \beta_\infty(m)\prod_p\beta_p(m).$$

Field:
- `genusRepAvg_eq`: `genusRepAvg Q m = aE Q m` for all integers $m \ge 1$.

*Scope:* Siegel's theorem asserts this for $Q$ positive definite with $n \ge 3$ (for $n \ge 3$ Siegel's factor
$\varepsilon$ is $1$); the genus then has finitely many classes (`GenusFinite Q`), so `genusRepAvg` is a genuine finite
average. Use this structure for $n \ge 4$ only (for $n = 3$ see `SiegelFormula3`). With $\mathrm{GL}_n(\mathbb{Z})$-classes and
weights $1/|\mathrm{Aut}(Q')|$, $\mathrm{Aut} \le \mathrm{GL}_n(\mathbb{Z})$ (the convention used here): the genus average is the same
for $\mathrm{GL}$- and $\mathrm{SL}$-classes, since passing to $\mathrm{SL}$-classes and proper automorphism groups doubles the
weight of every $\mathrm{GL}$-class. `aE` uses Mathlib's unconditional product (`tprod`), which is the intended value
only for $n \ge 4$ (`multipliable_eulerFactor`). Not proved here. For the sum of four squares this is the AWS input
`FourSquaresInputs.siegel` (`fourSquaresInputs_siegel_iff`). -/
@[kb "siegel1935" "Hauptsatz [unverified]; cassels1978 App. B, (3.13), p. 378"]
structure SiegelFormula (Q : QuadForm ℤ n) : Prop where
  genusRepAvg_eq : ∀ m : ℤ, 1 ≤ m → genusRepAvg Q m = aE Q m

/-- **Input: Siegel's formula relative to a chosen value of the Euler product** (for $n = 3$; Siegel 1935,
Hauptsatz [unverified]; Hanke 2004, (5.3), p. 368): for every $m \ge 1$,
$$a_E(m) = \beta_\infty(m)\cdot P(m),$$
where $P(m)$ stands for $\prod_p\beta_p(m)$.

Field:
- `genusRepAvg_eq`: `genusRepAvg Q m = aEWith Q m (P m)` for all integers $m \ge 1$.

*Role:* for $n = 3$ the Euler product converges only conditionally and the convention is not decided:
$P(m)$ could be the natural-order limit (`IsEulerProductValue Q m (P m)`, Siegel's convention [unverified]) or a
regularized value ($L(1,\chi)$ times finitely many factors). Statements using this input add their hypothesis on
$P$ explicitly (the corollaries below assume the natural-order limit at the values used). -/
@[kb "siegel1935" "Hauptsatz [unverified]"]
structure SiegelFormula3 (Q : QuadForm ℤ n) (P : ℤ → ℝ) : Prop where
  genusRepAvg_eq : ∀ m : ℤ, 1 ≤ m → genusRepAvg Q m = aEWith Q m (P m)

/-- For $n \ge 4$, `SiegelFormula` is `SiegelFormula3` with $P(m) = \prod_p\beta_p(m)$ (`eulerProduct`). -/
theorem siegelFormula_iff (Q : QuadForm ℤ n) :
    SiegelFormula Q ↔ SiegelFormula3 Q (eulerProduct Q) :=
  ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩

theorem one_le_mul_sqPart {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (ν : ℕ → ℕ) {T : ℤ} (hT : 0 < T) :
    1 ≤ T * sqPart S ν ^ 2 :=
  mul_pos hT (pow_pos (sqPart_pos hS ν) 2)

/-! ### Conditional corollaries: the genus average $a_E(m)$ -/

/-- **The ratio identity for $a_E$** (under Siegel's formula, $n \ge 4$):
$a_E(T'(m')^2) = a_E(T')\prod_{p \in S}F_p(T', \nu_p)$ (`aE_mul_sq`). -/
theorem genusRepAvg_mul_sq (Q : QuadForm ℤ n) (hSF : SiegelFormula Q) (hQ : Q.Nondegenerate)
    (hn : 4 ≤ n) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (ν : ℕ → ℕ) {T : ℤ} (hT : 0 < T)
    (hβ : ∀ p ∈ S, localDensity Q p T ≠ 0) :
    genusRepAvg Q (T * sqPart S ν ^ 2) =
      genusRepAvg Q T * ∏ p ∈ S, sqShiftFactor Q T p (ν p) := by
  rw [hSF.1 _ (one_le_mul_sqPart hS ν hT), hSF.1 _ hT, aE_mul_sq Q hQ hn hS ν hT hβ]

open Classical in
/-- **Theorem 5.4** (Hanke 2004, p. 369) for the genus average, $n \ge 4$, under Siegel's formula:
$$a_E(T'(m')^2) = a_E(T')\prod_{p \in S \cap \mathrm{Iso}}\Big[C_p(T') + \frac{1 - C_p(T')}{q^{(n-2)\nu_p}}\Big]
  \big((m')_{\mathrm{Iso}}\big)^{n-2}$$ (`thm_5_4_aE`). -/
@[kb "hanke2004" "Thm 5.4, p. 369"]
theorem thm_5_4_genus (Q : QuadForm ℤ n) (hSF : SiegelFormula Q) (hQ : Q.Nondegenerate) (hn : 4 ≤ n)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin n)) {T : ℤ} (hT : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (ν : ℕ → ℕ) :
    genusRepAvg Q (T * sqPart S ν ^ 2) = genusRepAvg Q T *
      (∏ p ∈ S.filter (IsIsotropicPrime Q),
        (localConstC Q p T + (1 - localConstC Q p T) / (p : ℝ) ^ ((n - 2) * ν p))) *
      (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (n - 2) := by
  rw [hSF.1 _ (one_le_mul_sqPart hS ν hT), hSF.1 _ hT, thm_5_4_aE Q hQ hn hS S₀ hT hst ν]

open Classical in
/-- **Theorem 5.4** (Hanke 2004, p. 369) for the genus average, $n = 3$ (any $n \ge 3$), under Siegel's formula relative
to $P$, when $P$ is the natural-order value of the Euler product at $T'$ and at $m = T'(m')^2$ (`thm_5_4`). -/
@[kb "hanke2004" "Thm 5.4, p. 369"]
theorem thm_5_4_genus3 (Q : QuadForm ℤ n) {P : ℤ → ℝ} (hSF : SiegelFormula3 Q P)
    (hQ : Q.Nondegenerate) (hn : 3 ≤ n) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (S₀ : Finset (Fin n)) {T : ℤ} (hT : 0 < T) (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (ν : ℕ → ℕ)
    (hP : IsEulerProductValue Q T (P T))
    (hPm : IsEulerProductValue Q (T * sqPart S ν ^ 2) (P (T * sqPart S ν ^ 2))) :
    genusRepAvg Q (T * sqPart S ν ^ 2) = genusRepAvg Q T *
      (∏ p ∈ S.filter (IsIsotropicPrime Q),
        (localConstC Q p T + (1 - localConstC Q p T) / (p : ℝ) ^ ((n - 2) * ν p))) *
      (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (n - 2) := by
  rw [hSF.1 _ (one_le_mul_sqPart hS ν hT), hSF.1 _ hT, thm_5_4 Q hQ hn hS S₀ hT hst ν hP hPm]

open Classical in
/-- **(5.13)** (Hanke 2004, p. 373) for the genus average, $n \ge 4$, under Siegel's formula:
$a_E(m) \ge a_E(T')\,((m')_{\mathrm{Iso}})^{n-2}\prod_{p \in S \cap \mathrm{Iso}}C'_p(T')$ (`eq_5_13_aE`). -/
@[kb "hanke2004" "(5.13), p. 373"]
theorem eq_5_13_genus (Q : IntQF n) (hSF : SiegelFormula Q) (hQ : IntQF.PosDef Q) (hn : 4 ≤ n)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin n)) {T : ℤ} (hT : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (ν : ℕ → ℕ) :
    genusRepAvg Q T * (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (n - 2) *
        ∏ p ∈ S.filter (IsIsotropicPrime Q), localConstC' Q p T ≤
      genusRepAvg Q (T * sqPart S ν ^ 2) := by
  rw [hSF.1 _ (one_le_mul_sqPart hS ν hT), hSF.1 _ hT]
  exact eq_5_13_aE Q hQ hn hS S₀ hT hst ν

open Classical in
/-- **Theorem 5.7(a), first part** (Hanke 2004, p. 372) for the genus average, $n = 3$, under Siegel's formula relative
to $P$ (natural-order values at $T'$ and $m$): $a_E(m) \ge \Lambda_3(T')\,N((m')_{\mathrm{Iso}})$ with
$\Lambda_3(T') = a_E(T')\prod_{p \in S \cap \mathrm{Iso},\ p \text{ bad}}C'_p(T')$ (`thm_5_7_a`). -/
@[kb "hanke2004" "Thm 5.7(a), p. 372 (first part)"]
theorem thm_5_7_a_genus (Q : IntQF 3) {P : ℤ → ℝ} (hSF : SiegelFormula3 Q P)
    (hQ : IntQF.PosDef Q) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin 3)) {T : ℤ}
    (hT : 0 < T) (hst : ∀ p ∈ S, IsPStable Q S₀ p T)
    (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ)
    (hP : IsEulerProductValue Q T (P T))
    (hPm : IsEulerProductValue Q (T * sqPart S ν ^ 2) (P (T * sqPart S ν ^ 2))) :
    genusRepAvg Q T *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) *
        ∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p ≤
      genusRepAvg Q (T * sqPart S ν ^ 2) := by
  rw [hSF.1 _ (one_le_mul_sqPart hS ν hT), hSF.1 _ hT]
  exact thm_5_7_a Q hQ hS S₀ hT hst hT2 ν hP hPm

open Classical in
/-- **Theorem 5.7(b)** (Hanke 2004, p. 373) for the genus average, $n = 4$, under Siegel's formula, ratio form
(`thm_5_7_b`). -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (ratio form)"]
theorem thm_5_7_b_genus (Q : IntQF 4) (hSF : SiegelFormula Q) (hQ : IntQF.PosDef Q) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin 4)) {T : ℤ} (hT : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T)
    (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ) :
    genusRepAvg Q T * (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ 2 *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) *
        ∏ p ∈ (S.filter (IsGoodPrime Q)).filter
            (fun p => jacobiSym Q.hessian.det p = -1 ∧ ¬ (p : ℤ) ∣ T),
          (1 + 1 / (p : ℝ))⁻¹ ≤
      genusRepAvg Q (T * sqPart S ν ^ 2) := by
  rw [hSF.1 _ (one_le_mul_sqPart hS ν hT), hSF.1 _ hT]
  exact thm_5_7_b Q hQ hS S₀ hT hst hT2 ν

open Classical in
/-- **Theorem 5.7(c), $n \ge 4$ even** (Hanke 2004, p. 373) for the genus average, under Siegel's formula, ratio form
(`thm_5_7_c_even`). -/
@[kb "hanke2004" "Thm 5.7(b),(c), p. 373 (ratio form, n even)"]
theorem thm_5_7_c_even_genus (Q : IntQF n) (hSF : SiegelFormula Q) (hQ : IntQF.PosDef Q)
    (hn : 4 ≤ n) (heven : Even n) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin n))
    {T : ℤ} (hT : 0 < T) (hst : ∀ p ∈ S, IsPStable Q S₀ p T)
    (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ) :
    genusRepAvg Q T * (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (n - 2) *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) *
        ∏ p ∈ (S.filter (IsGoodPrime Q)).filter
            (fun p => jacobiSym ((-1) ^ (n / 2) * Q.hessian.det) p = -1 ∧ ¬ (p : ℤ) ∣ T),
          (p : ℝ) ^ ((n - 2) / 2) / ((p : ℝ) ^ ((n - 2) / 2) + 1) ≤
      genusRepAvg Q (T * sqPart S ν ^ 2) := by
  rw [hSF.1 _ (one_le_mul_sqPart hS ν hT), hSF.1 _ hT]
  exact thm_5_7_c_even Q hQ hn heven hS S₀ hT hst hT2 ν

open Classical in
/-- **Theorem 5.7(c), $n \ge 5$ odd** (Hanke 2004, p. 373) for the genus average, under Siegel's formula, ratio form
(`thm_5_7_c_odd`). -/
@[kb "hanke2004" "Thm 5.7(c), p. 373 (ratio form, n odd)"]
theorem thm_5_7_c_odd_genus (Q : IntQF n) (hSF : SiegelFormula Q) (hQ : IntQF.PosDef Q)
    (hn : 4 ≤ n) (hodd : Odd n) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin n))
    {T : ℤ} (hT : 0 < T) (hst : ∀ p ∈ S, IsPStable Q S₀ p T)
    (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ) :
    genusRepAvg Q T * (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (n - 2) *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) *
        ∏ p ∈ (S.filter (IsGoodPrime Q)).filter (fun p : ℕ => ¬ (p : ℤ) ∣ T ∧
            jacobiSym ((-1) ^ ((n - 1) / 2) * (2 * Q.hessian.det) * T) p = 1),
          (1 - 1 / (p : ℝ) ^ ((n - 1) / 2)) / (1 - 1 / (p : ℝ) ^ (n - 2)) ≤
      genusRepAvg Q (T * sqPart S ν ^ 2) := by
  rw [hSF.1 _ (one_le_mul_sqPart hS ν hT), hSF.1 _ hT]
  exact thm_5_7_c_odd Q hQ hn hodd hS S₀ hT hst hT2 ν

end QuadFormsKB.Siegel
