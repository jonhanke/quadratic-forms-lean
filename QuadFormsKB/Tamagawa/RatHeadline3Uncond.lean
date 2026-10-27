import QuadFormsKB.Tamagawa.RatHeadline3
import QuadFormsKB.Tamagawa.TernaryRamDyadicLocal

/-!
# Rank-3 Siegel over ℚ, unconditional

`RatHeadline3` proved the ℚ rank-3 headline and Hanke's rank-3 corollaries conditional only on
`TernaryTamagawaTwo ℚ`; `TernaryRamDyadicLocal` proved `TernaryTamagawaTwo F` for every totally real `F` with
`𝓞 F` a PID (`QuatOrder.ternaryTamagawaTwo_pid`). This file instantiates the former with the latter.
-/

open NumberField

namespace QuadFormsKB.Tamagawa.RatHeadline3

open QuadFormsKB.Lattices NFEuler RegProd LocalDensity QuadForm QuadFormsKB.HilbertModular RatBridge
open QuadFormsKB.Binary QuadFormsKB.Tamagawa.BinaryTauRat
open QuadFormsKB.Siegel (SiegelFormula3 eulerProductReg3 IsEulerProductValue genusRepAvg aEWith)

/-- **τ(SO(V)) = 2 for every positive definite ternary space over ℚ**, unconditionally. -/
theorem ternaryTamagawaTwo_rat : TernaryTamagawaTwo ℚ := QuatOrder.ternaryTamagawaTwo_pid

/-- **Siegel's formula for every positive definite ternary form over ℤ**, unconditionally
(`siegelFormula3_rat` with the `TernaryTamagawaTwo ℚ`). -/
@[kb "siegel1935" "Hauptsatz, n = 3 (regularized Euler product), unconditional [unverified]"]
theorem siegelFormula3_rat_uncond (Q : QuadForm ℤ 3) (hQ : IntQF.PosDef Q) :
    SiegelFormula3 Q (eulerProductReg3 Q) :=
  siegelFormula3_rat ternaryTamagawaTwo_rat Q hQ

/-- **Siegel's formula for ternary forms over $\mathbb Z$ in the natural order of the primes** (Hanke 2004, (5.3) with $n = 3$,
Siegel's convention), unconditional: for every positive definite ternary $Q$ and $m \ge 1$ the
partial products $\prod_{p \le X}\beta_p(m)$ converge, to the regularized value $P_{\mathrm{reg}}(m)$
(`eulerProductReg3`), and
$$a_E(m) = \beta_\infty(m)\cdot\lim_{X\to\infty}\prod_{p\le X}\beta_p(m).$$
The limit is unique, so the formula holds with *any* $P$ satisfying `IsEulerProductValue Q m P`
(`genusRepAvg_eq_aEWith_of_isEulerProductValue`). -/
@[kb "siegel1935" "Hauptsatz, n = 3, natural-order Euler product (unconditional) [unverified]"]
theorem siegelFormula3_natural_rat_uncond (Q : QuadForm ℤ 3) (hQ : IntQF.PosDef Q) {m : ℤ}
    (hm : 1 ≤ m) :
    ∃ P : ℝ, IsEulerProductValue Q m P ∧ genusRepAvg Q m = aEWith Q m P :=
  siegelFormula3_natural_rat ternaryTamagawaTwo_rat (Q := Q) (hQ := hQ) (m := m) (hm := hm)

/-- **The conjunction of the two ingredients of the headline:** Hanke's `SiegelFormula3` with $P = P_{\mathrm{reg}}$ and the
natural-order identification at every $m \ge 1$. This is the form that the rank-3 corollaries consume. -/
theorem siegelFormula3_and_natural_rat_uncond (Q : QuadForm ℤ 3) (hQ : IntQF.PosDef Q) :
    SiegelFormula3 Q (eulerProductReg3 Q) ∧ ∀ m : ℤ, 1 ≤ m → IsEulerProductValue Q m (eulerProductReg3 Q m) :=
  siegelFormula3_and_natural_rat ternaryTamagawaTwo_rat (Q := Q) (hQ := hQ)

open QuadFormsKB.Siegel in
open Classical in
/-- **Theorem 5.4** (Hanke 2004, p. 369) for the genus average, $n = 3$, **unconditional**
(`thm_5_4_genus3` with $P = P_{\mathrm{reg}}$; the Siegel formula and the natural-order hypotheses are discharged). -/
@[kb "hanke2004" "Thm 5.4, p. 369"]
theorem thm_5_4_genus3_rat_uncond (Q : QuadForm ℤ 3) (hQ : IntQF.PosDef Q)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin 3)) {T : ℤ} (hT0 : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (ν : ℕ → ℕ) :
    genusRepAvg Q (T * sqPart S ν ^ 2) = genusRepAvg Q T *
      (∏ p ∈ S.filter (IsIsotropicPrime Q),
        (localConstC Q p T + (1 - localConstC Q p T) / (p : ℝ) ^ ((3 - 2) * ν p))) *
      (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (3 - 2) :=
  thm_5_4_genus3_rat ternaryTamagawaTwo_rat (Q := Q) (hQ := hQ) (S := S) (hS := hS) (S₀ := S₀) (T := T) (hT0 := hT0) (hst := hst) (ν := ν)

open QuadFormsKB.Siegel in
open Classical in
/-- **Theorem 5.7(a), first part** (Hanke 2004, p. 372) for the genus average, $n = 3$, unconditional (`thm_5_7_a_genus` discharged). -/
@[kb "hanke2004" "Thm 5.7(a), p. 372 (first part)"]
theorem thm_5_7_a_genus_rat_uncond (Q : IntQF 3) (hQ : IntQF.PosDef Q)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin 3)) {T : ℤ}
    (hT0 : 0 < T) (hst : ∀ p ∈ S, IsPStable Q S₀ p T)
    (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ) :
    genusRepAvg Q T *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) *
        ∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p ≤
      genusRepAvg Q (T * sqPart S ν ^ 2) :=
  thm_5_7_a_genus_rat ternaryTamagawaTwo_rat (Q := Q) (hQ := hQ) (S := S) (hS := hS) (S₀ := S₀) (T := T) (hT0 := hT0) (hst := hst) (hT2 := hT2) (ν := ν)

open QuadFormsKB.Siegel in
open Classical in
/-- **Theorem 5.7(a), first part, in $\mathbb N$** (square-class form), unconditional
(`thm_5_7_a_genus_nat` discharged). -/
@[kb "hanke2004" "Thm 5.7(a), p. 372 (first part)"]
theorem thm_5_7_a_genus_nat_rat_uncond (Q : IntQF 3) (hQ : IntQF.PosDef Q)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin 3))
    {T : ℕ} (hT0 : 0 < T) (hst : ∀ p ∈ S, IsPStable Q S₀ p T)
    (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ) {m : ℕ}
    (hm : m = T * (∏ p ∈ S, p ^ ν p) ^ 2) :
    genusRepAvg Q T *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) *
        ∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p ≤ genusRepAvg Q m :=
  thm_5_7_a_genus_nat_rat ternaryTamagawaTwo_rat (Q := Q) (hQ := hQ) (S := S) (hS := hS) (S₀ := S₀) (T := T) (hT0 := hT0) (hst := hst) (hT2 := hT2) (ν := ν) (m := m) (hm := hm)

open QuadFormsKB.Siegel in
open Classical in
/-- **Theorem 6.1, first case** (Hanke 2004, p. 380) for positive definite ternary forms over $\mathbb Z$, unconditional and the stated analytic hypotheses (`thm_6_1` with Siegel's formula and the natural-order Euler
products discharged; the remaining hypotheses are those of `thm_6_1`: theta decomposition, the cusp bound, `hH`, `hbound`). -/
@[kb "hanke2004" "Thm 6.1, p. 380 (first case)"]
theorem thm_6_1_rat_uncond (Q : IntQF 3) (hQ : IntQF.PosDef Q)
    {aH c : ℕ → ℝ} (hTS : ThetaSplit Q aH c) {t : ℕ} {C : ℝ}
    (hCB : CuspBoundSqClass c t (1 / 2) C)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin 3)) {T : ℕ} (hT0 : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T)
    (ν : ℕ → ℕ) {s : ℕ} (hTts : T = t * s ^ 2)
    {m m₀ : ℕ} (hm : m = T * (∏ p ∈ S, p ^ ν p) ^ 2) (hm₀ : m₀ = s * ∏ p ∈ S, p ^ ν p) {K : ℝ}
    (hpos : 0 < min (genusRepAvg Q T *
        ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) K)
    (hH : 0 ≤ aH m ∨
      K * ∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p ≤ genusRepAvg Q m + aH m)
    (hbound : C * isoPart Q s / min (genusRepAvg Q T *
          ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
            localConstC' Q p T) K *
        (divCount (anisoPart Q m₀) : ℝ) ^ 2 * √(anisoPart Q m₀ : ℝ) <
      √(isoPart Q m₀ : ℝ) / (divCount (isoPart Q m₀) : ℝ) ^ 2) :
    IntQF.Represents Q m :=
  thm_6_1_rat ternaryTamagawaTwo_rat (Q := Q) (hQ := hQ) (aH := aH) (c := c) (hTS := hTS) (t := t) (C := C) (hCB := hCB) (S := S) (hS := hS) (S₀ := S₀) (T := T) (hT0 := hT0) (hst := hst) (hT2 := hT2) (ν := ν) (s := s) (hTts := hTts) (m := m) (m₀ := m₀) (hm := hm) (hm₀ := hm₀) (K := K) (hpos := hpos) (hH := hH) (hbound := hbound)

open QuadFormsKB.Siegel in
open Classical in
/-- **Theorem 6.2** (Hanke 2004, p. 381) for positive definite ternary forms over $\mathbb Z$, unconditional and the stated analytic hypotheses (`thm_6_2` with Siegel's formula and the natural-order Euler
products discharged; remaining hypotheses: theta decomposition, uniform cusp bound, `hglob`, `hbound`). -/
@[kb "hanke2004" "Thm 6.2, p. 381"]
theorem thm_6_2_rat_uncond (Q : IntQF 3) (hQ : IntQF.PosDef Q)
    {aH c : ℕ → ℝ} (hTS : ThetaSplit Q aH c) {B η ε ε' : ℝ}
    (hCB : CuspBoundUniform c (1 / 2) (1 / 2 - η + ε') B)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin 3)) {T : ℕ} (hT0 : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T)
    (ν : ℕ → ℕ) {t s : ℕ} (ht : Squarefree t) (hTts : T = t * s ^ 2)
    (hspin : ¬ IsSpinorSquareClass aH t) {Λ : ℝ} (hΛ : 0 < Λ)
    (hglob : Λ * (t : ℝ) ^ (1 / 2 - ε) * isoPart Q s ≤ genusRepAvg Q T *
        ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T)
    {m m₀ : ℕ} (hm : m = T * (∏ p ∈ S, p ^ ν p) ^ 2) (hm₀ : m₀ = s * ∏ p ∈ S, p ^ ν p)
    (hbound : B / Λ * (divCount (anisoPart Q m₀) : ℝ) ^ 2 * √(anisoPart Q m₀ : ℝ) <
      (t : ℝ) ^ (η - (ε + ε')) * √(isoPart Q m₀ : ℝ) / (divCount (isoPart Q m₀) : ℝ) ^ 2) :
    IntQF.Represents Q m :=
  thm_6_2_rat ternaryTamagawaTwo_rat (Q := Q) (hQ := hQ) (aH := aH) (c := c) (hTS := hTS) (B := B) (η := η) (ε := ε) (ε' := ε') (hCB := hCB) (S := S) (hS := hS) (S₀ := S₀) (T := T) (hT0 := hT0) (hst := hst) (hT2 := hT2) (ν := ν) (t := t) (s := s) (ht := ht) (hTts := hTts) (hspin := hspin) (Λ := Λ) (hΛ := hΛ) (hglob := hglob) (m := m) (m₀ := m₀) (hm := hm) (hm₀ := hm₀) (hbound := hbound)

open QuadFormsKB.Siegel in
/-- **Gauss's $r_3$, Siegel's formula for $x^2+y^2+z^2$** (class number one, `genusClasses_sumSq`), unconditional: for $m \ge 1$,
$$r_3(m) = \#\{(x,y,z) \in \mathbb Z^3 : x^2+y^2+z^2 = m\} = \beta_\infty(m)\cdot P_{\mathrm{reg}}(m),\qquad
P_{\mathrm{reg}}(m) = \lim_{X\to\infty}\prod_{p \le X}\beta_p(m),$$
$\beta_\infty$ = `betaInf` (for $I_3$: $\frac{3\omega_3}{2}\sqrt m = 2\pi\sqrt m$, not evaluated here). -/
@[kb "siegel1935" "Hauptsatz for x²+y²+z² (Gauss's r_3), unconditional [unverified]"]
theorem repNum_sumSq_three_rat_uncond {m : ℤ} (hm : 1 ≤ m) :
    ∃ P : ℝ, IsEulerProductValue (sumSq 3) m P ∧ (repNum (sumSq 3) m : ℝ) = betaInf (sumSq 3) m * P :=
  repNum_sumSq_three_rat ternaryTamagawaTwo_rat (m := m) (hm := hm)

end QuadFormsKB.Tamagawa.RatHeadline3
