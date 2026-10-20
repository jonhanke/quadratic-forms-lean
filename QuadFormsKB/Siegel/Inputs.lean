/-
# Siegel's formula: the analytic inputs of Hanke 2004 §4

Hanke's §6 (pp. 380–383) combines three ingredients to decide when $r_Q(m) > 0$:
1. the decomposition of the theta series into an Eisenstein part, (for $n = 3$) a part $H$ with non-cuspidal
   Shimura lift, and a cusp form, (4.3)/(4.4), p. 365, with the Eisenstein coefficients equal to the genus average
   $a_E(m)$ of (4.5), p. 366;
2. upper bounds for the cusp-form coefficients, (4.8)–(4.10), p. 367 (Deligne; Assumption 4.4 for odd $n$);
3. lower bounds for $a_E(m)$ (§5; in this repo `Siegel/MainTerm.lean`, `Siegel/Formula.lean`).

Modular forms of (half-)integral weight on $\Gamma_0(N)$ are not available here, so 1 and 2 are stated as
**hypothesis structures about the coefficient sequences** (not proved):

| Input | Statement | Source |
|---|---|---|
| `ThetaSplit Q a_H c` | $r_Q(m) = a_E(m) + a_H(m) + c(m)$ for $m \ge 1$; $a_H = 0$ unless $n = 3$; $a_H$ supported on finitely many square classes | (4.3), (4.4), p. 365; (4.5), p. 366 |
| `CuspBound c α C` | $\lvert c(m)\rvert \le C\,\tau(m)\,m^{\alpha}$ for $m \ge 1$ | (4.8), p. 367, with $\alpha = (k-1)/2 = (n-2)/4$, $C = \sum_i\lvert\gamma_i\rvert$ |
| `CuspBoundSqClass c t α C` | $\lvert c(tm_0^2)\rvert \le C\,\tau(m_0)^2 m_0^{\alpha}$ for $m_0 \ge 1$ | (4.9), p. 367, with $\alpha = (n-2)/2$, $C = \sum_i\lvert\gamma_i\rvert$ for $g = \mathrm{Shi}(f, t)$ |
| `CuspBoundUniform c α β C` | $\lvert c(tm_0^2)\rvert \le C\,t^{\beta}\tau(m_0)^2 m_0^{\alpha}$ for squarefree $t \ge 1$, $m_0 \ge 1$ | (4.10), p. 367 (Assumption 4.4), with $\beta = (n-1)/4 - \eta + \varepsilon'$, $C = B_{\varepsilon'}\sum_k\lvert\delta_k\rvert$ |

The link to the analytic object is `hasSum_theta_split`: under `ThetaSplit`,
$\Theta_Q(z) = 1 + \sum_{m \ge 1}(a_E(m) + a_H(m) + c(m))e(mz)$ (from `hasSum_theta`).

Also defined here: the divisor count $\tau$ (`divCount`), the isotropic and anisotropic parts $(m)_{\mathrm{Iso}}$,
$(m)_{\mathrm{Aniso}}$ (`isoPart`, `anisoPart`), and the basic bridge `represents_of_abs_lt`:
$|c(m)| < a_E(m) + a_H(m) \Rightarrow m$ is represented by $Q$.
-/
import QuadFormsKB.Siegel.Formula
import QuadFormsKB.Siegel.Theta

open Complex

namespace QuadFormsKB.Siegel

open LocalDensity

variable {n : ℕ}

/-! ### The divisor count $\tau(m)$ -/

/-- **The number of divisors** $\tau(m) = \#\{d \in \mathbb{N} : d \mid m\}$ of $m \ge 1$ (Hanke's $\tau$ in (4.8)–(4.10)).
*Edge case:* $\tau(0) = 0$ (Mathlib's `Nat.divisors 0 = ∅`). -/
def divCount (m : ℕ) : ℕ := m.divisors.card

/-- $\tau$ is multiplicative: $\tau(ab) = \tau(a)\tau(b)$ for coprime $a, b$. -/
theorem divCount_mul {a b : ℕ} (h : Nat.Coprime a b) : divCount (a * b) = divCount a * divCount b :=
  Nat.Coprime.card_divisors_mul h

/-- $\tau(p^k) = k + 1$ for a prime $p$. -/
theorem divCount_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : divCount (p ^ k) = k + 1 := by
  rw [divCount, Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

theorem divCount_pos {m : ℕ} (hm : m ≠ 0) : 0 < divCount m :=
  Finset.card_pos.2 ⟨1, Nat.one_mem_divisors.2 hm⟩

/-! ### Isotropic and anisotropic parts -/

open Classical in
/-- **The isotropic part** $(m)_{\mathrm{Iso}} = \prod_{p \mid m,\ Q \text{ isotropic over } \mathbb{Q}_p} p^{\mathrm{ord}_p(m)}$
of $m \ge 1$ (Hanke 2004, notation of Thms 5.4, 5.7 and §6; "Iso" = the primes where $Q$ is isotropic,
`IsIsotropicPrime`). *Edge case:* $(0)_{\mathrm{Iso}} = 1$. -/
noncomputable def isoPart (Q : QuadForm ℤ n) (m : ℕ) : ℕ :=
  m.factorization.prod fun p k => if IsIsotropicPrime Q p then p ^ k else 1

open Classical in
/-- **The anisotropic part** $(m)_{\mathrm{Aniso}} = \prod_{p \mid m,\ Q \text{ anisotropic over } \mathbb{Q}_p} p^{\mathrm{ord}_p(m)}$
of $m \ge 1$, so that $m = (m)_{\mathrm{Iso}}(m)_{\mathrm{Aniso}}$ (`isoPart_mul_anisoPart`). *Edge case:* $(0)_{\mathrm{Aniso}} = 1$. -/
noncomputable def anisoPart (Q : QuadForm ℤ n) (m : ℕ) : ℕ :=
  m.factorization.prod fun p k => if IsIsotropicPrime Q p then 1 else p ^ k

theorem isoPart_mul (Q : QuadForm ℤ n) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    isoPart Q (a * b) = isoPart Q a * isoPart Q b := by
  classical
  unfold isoPart
  rw [Nat.factorization_mul ha hb, Finsupp.prod_add_index']
  · intro p; simp
  · intro p k₁ k₂; split_ifs <;> simp [pow_add]

theorem anisoPart_mul (Q : QuadForm ℤ n) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    anisoPart Q (a * b) = anisoPart Q a * anisoPart Q b := by
  classical
  unfold anisoPart
  rw [Nat.factorization_mul ha hb, Finsupp.prod_add_index']
  · intro p; simp
  · intro p k₁ k₂; split_ifs <;> simp [pow_add]

/-- $m = (m)_{\mathrm{Iso}}\,(m)_{\mathrm{Aniso}}$ for $m \ne 0$. -/
theorem isoPart_mul_anisoPart (Q : QuadForm ℤ n) {m : ℕ} (hm : m ≠ 0) :
    isoPart Q m * anisoPart Q m = m := by
  classical
  unfold isoPart anisoPart
  rw [← Finsupp.prod_mul]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hm]
  refine Finsupp.prod_congr fun p _ => ?_
  split_ifs <;> simp

theorem isoPart_pos (Q : QuadForm ℤ n) (m : ℕ) : 0 < isoPart Q m := by
  classical
  unfold isoPart Finsupp.prod
  refine Finset.prod_pos fun p hp => ?_
  have : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
  dsimp only
  split_ifs
  · exact pow_pos this.pos _
  · exact one_pos

theorem anisoPart_pos (Q : QuadForm ℤ n) (m : ℕ) : 0 < anisoPart Q m := by
  classical
  unfold anisoPart Finsupp.prod
  refine Finset.prod_pos fun p hp => ?_
  have : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
  dsimp only
  split_ifs
  · exact one_pos
  · exact pow_pos this.pos _

/-- $(m)_{\mathrm{Iso}}$ and $(m)_{\mathrm{Aniso}}$ are coprime. -/
theorem coprime_isoPart_anisoPart (Q : QuadForm ℤ n) (m : ℕ) :
    Nat.Coprime (isoPart Q m) (anisoPart Q m) := by
  classical
  unfold isoPart anisoPart Finsupp.prod
  refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun q hq => ?_
  have hp' : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
  have hq' : q.Prime := Nat.prime_of_mem_primeFactors (by simpa using hq)
  by_cases hIp : IsIsotropicPrime Q p
  · by_cases hIq : IsIsotropicPrime Q q
    · simp [hIq]
    · have hne : p ≠ q := by rintro rfl; exact hIq hIp
      simp only [hIp, hIq, ite_true, ite_false]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp' hq').2 hne)
  · simp [hIp]

/-- $(p^k)_{\mathrm{Iso}} = p^k$ if $Q$ is isotropic at $p$, and $1$ otherwise. -/
theorem isoPart_prime_pow (Q : QuadForm ℤ n) {p : ℕ} (hp : p.Prime) (k : ℕ) [Decidable (IsIsotropicPrime Q p)] :
    isoPart Q (p ^ k) = if IsIsotropicPrime Q p then p ^ k else 1 := by
  classical
  unfold isoPart
  rw [hp.factorization_pow, Finsupp.prod_single_index (by simp)]
  congr 1

open Classical in
/-- $\big(\prod_{p \in S}p^{\nu_p}\big)_{\mathrm{Iso}} = \prod_{p \in S \cap \mathrm{Iso}}p^{\nu_p}$ for a finite set $S$ of primes. -/
theorem isoPart_prod_pow (Q : QuadForm ℤ n) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (ν : ℕ → ℕ) :
    isoPart Q (∏ p ∈ S, p ^ ν p) = ∏ p ∈ S.filter (IsIsotropicPrime Q), p ^ ν p := by
  rw [Finset.prod_filter]
  induction S using Finset.induction_on with
  | empty => simp [isoPart]
  | insert a S ha ih =>
    have hS' : ∀ p ∈ S, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have ha' : a.Prime := hS a (Finset.mem_insert_self a S)
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      isoPart_mul Q (pow_ne_zero _ ha'.ne_zero)
        (Finset.prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ (hS' p hp).ne_zero),
      ih hS', isoPart_prime_pow Q ha']

/-! ### The analytic inputs -/

/-- **Input: the decomposition of the theta series** (Hanke 2004, (4.3) and (4.4), p. 365, with (4.5), p. 366).
For $n \ge 4$, $\Theta_Q = E + f$ with $E(z) = \sum_{m \ge 0}a_E(m)e(mz)$ Eisenstein and $f$ a cusp form; for $n = 3$,
$\Theta_Q = E + H + f$ with $H(z) = \sum_{m > 0}a_H(m)e(mz) \in U(N, \chi)$ (the span of the forms (4.2), whose Shimura lifts
are not cuspidal) and $f \in U^\perp(N, \chi)$. The Eisenstein coefficients are the genus average $a_E(m)$ of (4.5)
(`genusRepAvg`, Siegel). Here the cusp-form coefficients are an abstract sequence $c(m)$; their only property used
is a coefficient bound (`CuspBound`, `CuspBoundSqClass`, `CuspBoundUniform`).

Parameters: `aH`, `c` $: \mathbb{N} \to \mathbb{R}$, the coefficients $a_H(m)$ and $c(m)$ (= Hanke's $a(m)$, the coefficients of $f$).

Fields:
- `repNum_eq`: $r_Q(m) = a_E(m) + a_H(m) + c(m)$ for every integer $m \ge 1$ (comparing coefficients of $e(mz)$).
- `aH_eq_zero`: if $n \ne 3$ then $a_H(m) = 0$ for all $m$ ((4.3): no $H$ for $n \ge 4$).
- `aH_finite_squareClasses`: there is a finite set $\{t_1, \dots, t_r\}$ such that $a_H(m) \ne 0$ only if
  $m \in t_i\mathbb{Z}^2$ for some $i$ (p. 365: "there are only finitely many $t\mathbb{Z}^2$ on which the Fourier
  coefficients of $U(N, \chi)$ are nonzero").

*Not included:* the constant term ($r_Q(0) = 1 = a_E(0)$, see `hasSum_theta_split`), modularity of $E$, $H$, $f$
(not available in Mathlib for $\Gamma_0(N)$ and half-integral weight), and $|a_H(m)| \le a_E(m)$ (Lemma 5.8(a), from
(4.6) and Kneser–Hsia), which the conditional statements below do not need. -/
@[kb "hanke2004" "(4.3), (4.4), p. 365; (4.5), p. 366"]
structure ThetaSplit (Q : QuadForm ℤ n) (aH c : ℕ → ℝ) : Prop where
  repNum_eq : ∀ m : ℕ, 1 ≤ m → (repNum Q m : ℝ) = genusRepAvg Q m + aH m + c m
  aH_eq_zero : n ≠ 3 → ∀ m, aH m = 0
  aH_finite_squareClasses : ∃ ts : Finset ℕ, ∀ m, aH m ≠ 0 → ∃ t ∈ ts, ∃ k : ℕ, m = t * k ^ 2

/-- **A spinor square class** (Hanke 2004, Def. 4.3, p. 366): $t\mathbb{Z}^2$ is a spinor square class for the
coefficients $a_H$ if $a_H(tk^2) \ne 0$ for some $k$. -/
@[kb "hanke2004" "Def. 4.3, p. 366"]
def IsSpinorSquareClass (aH : ℕ → ℝ) (t : ℕ) : Prop := ∃ k : ℕ, aH (t * k ^ 2) ≠ 0

/-- **Input: the coefficient bound (4.8)** (Hanke 2004, p. 367): $|c(m)| \le C\,\tau(m)\,m^{\alpha}$ for every $m \ge 1$.

For a cusp form $f = \sum_i\gamma_ig_i$ of integral weight $k$ on $\Gamma_0(N)$ ((4.7), $g_i$ eigenforms normalized
with first nonzero coefficient $1$), the theory of newforms and Deligne's bound give (4.8) with $\alpha = (k-1)/2$ and
$C = \sum_i|\gamma_i|$. For $\Theta_Q$ with $n$ even, $k = n/2$ and $\alpha = (n-2)/4$ (so $\alpha = 1/2$ for $n = 4$).

Fields:
- `abs_le`: $|c(m)| \le C\,\tau(m)\,m^{\alpha}$ for all integers $m \ge 1$ ($\tau$ = `divCount`, $m^\alpha$ = `Real.rpow`). -/
@[kb "hanke2004" "(4.8), p. 367"]
structure CuspBound (c : ℕ → ℝ) (α C : ℝ) : Prop where
  abs_le : ∀ m : ℕ, 1 ≤ m → |c m| ≤ C * divCount m * (m : ℝ) ^ α

/-- **Input: the coefficient bound (4.9) in a fixed square class** (Hanke 2004, p. 367):
$|c(tm_0^2)| \le C\,\tau(m_0)^2\,m_0^{\alpha}$ for every $m_0 \ge 1$.

For $n \ge 3$ odd and $f = \sum_k\delta_kf_k$ of weight $n/2$ ($f \in U^\perp(N,\chi)$ when $n = 3$), with $t$
squarefree fixed, Möbius inversion of the Shimura lift $\mathrm{Shi}(f, t) = \sum_i\gamma_ig_i$ and Deligne's bound give
this with $\alpha = (n-2)/2$ and $C = \sum_i|\gamma_i|$ (the $\gamma_i$ of $g = \mathrm{Shi}(f, t)$).

Fields:
- `abs_le`: $|c(tm_0^2)| \le C\,\tau(m_0)^2\,m_0^{\alpha}$ for all integers $m_0 \ge 1$. -/
@[kb "hanke2004" "(4.9), p. 367"]
structure CuspBoundSqClass (c : ℕ → ℝ) (t : ℕ) (α C : ℝ) : Prop where
  abs_le : ∀ m₀ : ℕ, 1 ≤ m₀ → |c (t * m₀ ^ 2)| ≤ C * (divCount m₀ : ℝ) ^ 2 * (m₀ : ℝ) ^ α

/-- **Input: the coefficient bound (4.10), uniform in the square class** (Hanke 2004, p. 367, under Assumption 4.4,
p. 366): $|c(tm_0^2)| \le C\,t^{\beta}\,\tau(m_0)^2\,m_0^{\alpha}$ for all squarefree $t \ge 1$ and all $m_0 \ge 1$.

Assumption 4.4 ($n \ge 3$ odd): every Hecke eigenform $f_k$ of weight $n/2$ with $\langle f_k, f_k\rangle = 1$ has
$|a_k(t)| < B_{\varepsilon'}t^{(n-1)/4 - \eta + \varepsilon'}$ for squarefree $t > 0$, some $\varepsilon' > 0$, $0 \le \eta \le 1/4$
(best known $\eta = 1/12$, Conrey–Iwaniec, constant not explicit). With $\gamma_i = \delta_ka_k(t)$ in (4.9) this gives
(4.10): $\alpha = (n-2)/2$, $\beta = (n-1)/4 - \eta + \varepsilon'$, $C = B_{\varepsilon'}\sum_k|\delta_k|$.

Fields:
- `abs_le`: $|c(tm_0^2)| \le C\,t^{\beta}\,\tau(m_0)^2\,m_0^{\alpha}$ for all squarefree integers $t \ge 1$ and all $m_0 \ge 1$. -/
@[kb "hanke2004" "(4.10), p. 367; Assumption 4.4, p. 366"]
structure CuspBoundUniform (c : ℕ → ℝ) (α β C : ℝ) : Prop where
  abs_le : ∀ t m₀ : ℕ, Squarefree t → 1 ≤ t → 1 ≤ m₀ →
    |c (t * m₀ ^ 2)| ≤ C * (t : ℝ) ^ β * (divCount m₀ : ℝ) ^ 2 * (m₀ : ℝ) ^ α

/-! ### Link to the theta series -/

/-- $r_Q(0) = 1$ for $Q$ positive definite (only $\vec{x} = 0$ has $Q(\vec{x}) = 0$). -/
theorem repNum_zero {Q : IntQF n} (hQ : Q.PosDef) : repNum Q 0 = 1 := by
  have : repSet Q 0 = {0} := by
    ext x
    simp only [repSet, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra hne
      have := hQ x hne
      omega
    · rintro rfl
      simp [QuadForm.evalIn]
  rw [repNum, this, Nat.card_unique]

/-- **The $q$-expansion of $\Theta_Q$ under `ThetaSplit`** (Hanke 2004, (1.1), (4.3)/(4.4)): for $Q$ positive definite and
$\operatorname{Im} z > 0$,
$$\Theta_Q(z) = 1 + \sum_{m \ge 1}\big(a_E(m) + a_H(m) + c(m)\big)e(mz).$$ -/
theorem hasSum_theta_split {Q : IntQF n} (hQ : Q.PosDef) {aH c : ℕ → ℝ} (h : ThetaSplit Q aH c)
    {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun m : ℕ => (((if m = 0 then 1 else genusRepAvg Q m + aH m + c m : ℝ)) : ℂ) *
      cexp (2 * Real.pi * I * z * m)) (theta Q z) := by
  convert hasSum_theta hQ hz using 2 with m
  split_ifs with hm
  · subst hm; simp [repNum_zero hQ]
  · rw [← h.repNum_eq m (Nat.one_le_iff_ne_zero.2 hm)]; push_cast; rfl

/-! ### The bridge: $a_E(m) + a_H(m) > |c(m)| \Rightarrow m$ is represented -/

/-- **The basic bridge** (Hanke 2004, §6: "solving to ensure $a_E(m) > |a(m)|$", proofs of Thms 6.1–6.4): under
`ThetaSplit`, if $m \ge 1$ and $|c(m)| < a_E(m) + a_H(m)$, then $r_Q(m) > 0$. -/
theorem repNum_pos_of_abs_lt {Q : QuadForm ℤ n} {aH c : ℕ → ℝ} (h : ThetaSplit Q aH c) {m : ℕ}
    (hm : 1 ≤ m) (hlt : |c m| < genusRepAvg Q m + aH m) : 0 < repNum Q m := by
  have h1 := h.repNum_eq m hm
  have h2 := neg_abs_le (c m)
  have : (0 : ℝ) < repNum Q m := by rw [h1]; linarith
  exact_mod_cast this

/-- $r_Q(m) > 0$ means $m$ is represented by $Q$. -/
theorem represents_of_repNum_pos {Q : QuadForm ℤ n} {m : ℤ} (h : 0 < repNum Q m) :
    IntQF.Represents Q m := by
  obtain ⟨⟨x, hx⟩, _⟩ := Nat.card_pos_iff.1 h
  exact ⟨x, hx⟩

/-- **The basic bridge, as representability:** under `ThetaSplit`, $m \ge 1$ and $|c(m)| < a_E(m) + a_H(m)$ imply that
$Q$ represents $m$. -/
@[kb "hanke2004" "§6, p. 380 (proof scheme of Thms 6.1–6.4)"]
theorem represents_of_abs_lt {Q : QuadForm ℤ n} {aH c : ℕ → ℝ} (h : ThetaSplit Q aH c) {m : ℕ}
    (hm : 1 ≤ m) (hlt : |c m| < genusRepAvg Q m + aH m) : IntQF.Represents Q m :=
  represents_of_repNum_pos (repNum_pos_of_abs_lt h hm hlt)

/-- For $n \ne 3$ (no $a_H$): $|c(m)| < a_E(m) \Rightarrow Q$ represents $m$. -/
theorem represents_of_abs_lt_aE {Q : QuadForm ℤ n} {aH c : ℕ → ℝ} (h : ThetaSplit Q aH c)
    (hn : n ≠ 3) {m : ℕ} (hm : 1 ≤ m) (hlt : |c m| < genusRepAvg Q m) : IntQF.Represents Q m :=
  represents_of_abs_lt h hm (by rw [h.aH_eq_zero hn m, add_zero]; exact hlt)

end QuadFormsKB.Siegel
