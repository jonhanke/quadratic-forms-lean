/-
# Moreno–Wagstaff 2005, Chapters 6–8: definitions and statements

**Source.** C. J. Moreno and S. S. Wagstaff Jr., *Sums of Squares of Integers* (2005), Chapter 6 ("Counting
representations as sums of squares"), §7.11 (squares in arithmetic progression) and Chapter 8
("Applications"). Locators give **printed** pages (printed = pdf page − 13).

**Notation.** $r_s(n)$ is `Siegel.repNum (Siegel.sumSq s) n`. The book's normalized Gauss-sum term
$A_m(n) = \sum_{h \bmod m,\ (h, m) = 1} (S_{h,m}/m)^s e^{-2\pi i n h/m}$ is this library's
`Siegel.SingularSeries.ssTerm (Siegel.sumSq s) n m` (for $Q = x_0^2 + \dots + x_{s-1}^2$ the $n$-ary Gauss sum
of `ssTerm` is $S_{h,m}^s$).

**Contents.**
* Chapter 6: `singularSeriesSq` ($\rho_s(n)$, (6.17)), `Theorem61` (Hardy), `gaussSumMW` ($S(h, k)$),
  `Theorem65` (evaluation of the Gauss sum), `Theorem66` (multiplicativity), `Lemma61`,
  `IsFundamentalDiscrMW` and `Theorem67` (fundamental discriminants), `Corollary61` (Deligne-type error terms).
* §7.11: `Theorem77` (as printed, false without $x < z$; see the erratum), `Theorem77Corrected`, `Corollary74`.
* Chapter 8: `Theorem81` (factoring from two representations, mathematical core), `Theorem82` (Gauss),
  `Theorem83` (Jacobsthal), `IsSumPosSq`, `Theorem84` (Pall), `IsSumDistinctSq`, `SpragueTheorem`,
  `Theorem85` (multiplicative property of the redundancy function).
-/
import QuadFormsKB.Literature.MorenoWagstaff.Ch2Statements
import QuadFormsKB.Siegel.SingularSeries
import Mathlib.NumberTheory.FundamentalDiscriminant
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

open Complex

namespace QuadFormsKB.MorenoWagstaff

open QuadFormsKB.Siegel

/-! ### Chapter 6 -/

/-- **The singular series $\rho_s(n)$** (Moreno–Wagstaff (6.17), p. 188):
$\rho_s(n) = \frac{n^{s/2-1}\pi^{s/2}}{\Gamma(s/2)} \sum_{m \ge 1} A_m(n)$, with
$A_m(n) = \sum_{h \bmod m,\ (h,m)=1} (S_{h,m}/m)^s e^{-2\pi i n h/m}$ the term `SingularSeries.ssTerm` of this
library (`ssTerm _ _ 0 = 0`, so the sum over $m \in \mathbb N$ is the book's sum over $m \ge 1$). The series
converges absolutely for $s \ge 5$; for other $s$ the `tsum` is $0$ unless the terms are summable, so the
statements below use $s \ge 5$. -/
@[kb "morenowagstaff2005" "(6.17), singular series rho_s(n), p. 188"]
noncomputable def singularSeriesSq (s n : ℕ) : ℂ :=
  (((n : ℝ) ^ ((s : ℝ) / 2 - 1) * Real.pi ^ ((s : ℝ) / 2) / Real.Gamma ((s : ℝ) / 2) : ℝ) : ℂ) *
    ∑' m : ℕ, SingularSeries.ssTerm (sumSq s) n m

/-- **Moreno–Wagstaff, Theorem 6.1** (Hardy; p. 189, cited): $r_s(n) = \rho_s(n)$ for $s = 5, 6, 7, 8$ and every
$n \ge 1$; for $s > 8$, $r_s(n) = \rho_s(n) + O(n^{s/4})$ (implied constant depending on $s$). -/
@[kb "morenowagstaff2005" "Theorem 6.1, p. 189"]
def Theorem61 : Prop :=
  (∀ s n : ℕ, 5 ≤ s → s ≤ 8 → 0 < n → (repNum (sumSq s) n : ℂ) = singularSeriesSq s n) ∧
  (∀ s : ℕ, 8 < s → ∃ C : ℝ, ∀ n : ℕ, 0 < n →
    ‖(repNum (sumSq s) n : ℂ) - singularSeriesSq s n‖ ≤ C * (n : ℝ) ^ ((s : ℝ) / 4))

/-- **The Gauss sum $S(h, k)$** (Moreno–Wagstaff §6.4, pp. 188 and 201): $S(h, k) = \sum_{j=1}^{k} e^{2\pi i h j^2/k}$
for integers $h$ and $k \ge 1$ (the book's $S_{h,k}$). -/
@[kb "morenowagstaff2005" "§6.4, Gauss sum S(h, k), p. 201"]
noncomputable def gaussSumMW (h : ℤ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 k, cexp (2 * Real.pi * I * h * (j : ℂ) ^ 2 / k)

/-- **Moreno–Wagstaff, Theorem 6.5** (evaluation of the Gauss sum; p. 199): for every positive integer $n$,
$\sum_{j=1}^{n} e^{-2\pi i j^2/n} = \frac{1 + i^n}{1 + i}\sqrt n$. (Checked by hand for $n = 1, 2, 3, 4$.) -/
@[kb "morenowagstaff2005" "Theorem 6.5, p. 199"]
def Theorem65 : Prop :=
  ∀ n : ℕ, 0 < n →
    ∑ j ∈ Finset.Icc 1 n, cexp (-(2 * Real.pi * I * (j : ℂ) ^ 2 / n)) = (1 + I ^ n) / (1 + I) * Real.sqrt n

/-- **Moreno–Wagstaff, Theorem 6.6** (p. 201): if $k_1, k_2$ are coprime positive integers and $h$ is coprime to
both, then $S(h k_2, k_1)\,S(h k_1, k_2) = S(h, k_1 k_2)$.

*Update:* the coprimality of $h$ with $k_1, k_2$ is not needed (the proof `theorem66` does not use it). -/
@[kb "morenowagstaff2005" "Theorem 6.6, p. 201"]
def Theorem66 : Prop :=
  ∀ (k₁ k₂ : ℕ) (h : ℤ), 0 < k₁ → 0 < k₂ → k₁.Coprime k₂ → IsCoprime h k₁ → IsCoprime h k₂ →
    gaussSumMW (h * k₂) k₁ * gaussSumMW (h * k₁) k₂ = gaussSumMW h (k₁ * k₂)

/-- **Moreno–Wagstaff, Lemma 6.1** (p. 201): for coprime positive integers $k, k'$, as $j$ runs through the
residues mod $k$ and $j'$ through the residues mod $k'$, $k j' + k' j$ runs through the residues mod $k k'$:
the map $(j, j') \mapsto k j' + k' j$ from $\mathbb Z/k \times \mathbb Z/k'$ to $\mathbb Z/kk'$ (on the
representatives $0 \le j < k$, $0 \le j' < k'$) is a bijection. -/
@[kb "morenowagstaff2005" "Lemma 6.1, p. 201"]
def Lemma61 : Prop :=
  ∀ k k' : ℕ, 0 < k → 0 < k' → k.Coprime k' →
    Function.Bijective (fun p : Fin k × Fin k' => ((k * p.2.val + k' * p.1.val : ℕ) : ZMod (k * k')))

/-- **Fundamental discriminant, book convention** (Moreno–Wagstaff §6.4, p. 229): $d \equiv 0, 1 \pmod 4$,
**not a perfect square**, not divisible by the square of an odd prime, and odd or $\equiv 8, 12 \pmod{16}$.
This is Mathlib's `Int.IsFundamentalDiscr` (the same arithmetic conditions, which accept $d = 1$) together
with the book's extra condition that $d$ is not a square. -/
@[kb "morenowagstaff2005" "§6.4, fundamental discriminant, p. 229"]
def IsFundamentalDiscrMW (d : ℤ) : Prop := Int.IsFundamentalDiscr d ∧ ¬ IsSquare d

/-- **Moreno–Wagstaff, Theorem 6.7** (Landau; p. 230): every integer $d \equiv 0, 1 \pmod 4$ that is not a square
is uniquely $d = f m^2$ with $m$ a positive integer and $f$ a fundamental discriminant. -/
@[kb "morenowagstaff2005" "Theorem 6.7, p. 230"]
def Theorem67 : Prop :=
  ∀ d : ℤ, (d % 4 = 0 ∨ d % 4 = 1) → ¬ IsSquare d →
    ∃! fm : ℤ × ℕ, 0 < fm.2 ∧ IsFundamentalDiscrMW fm.1 ∧ d = fm.1 * (fm.2 : ℤ) ^ 2

/-- **Moreno–Wagstaff, Corollary 6.1** (p. 235, from Theorems 6.8 and 6.9, i.e. Hecke theory with Deligne's
bound and Shimura's correspondence): for even $s$, $r_s(p^\ell) = \rho_s(p^\ell) + O(p^{\ell(s/4 - 1/2)})$
uniformly in odd primes $p$ and $\ell \ge 1$, the constant depending only on $s$; for odd $s$ and squarefree
odd $t$, $r_s(t p^{2\ell}) = \rho_s(t p^{2\ell}) + O(p^{2\ell(s/4-1/2)})$ for odd primes $p \nmid t$, the constant
depending only on $s$ and $t$. Stated here for $s \ge 5$ (where $\rho_s$ is an absolutely convergent series). -/
@[kb "morenowagstaff2005" "Corollary 6.1, p. 235"]
def Corollary61 : Prop :=
  (∀ s : ℕ, 5 ≤ s → Even s → ∃ C : ℝ, ∀ p ℓ : ℕ, p.Prime → p ≠ 2 → 1 ≤ ℓ →
    ‖(repNum (sumSq s) ((p : ℤ) ^ ℓ) : ℂ) - singularSeriesSq s (p ^ ℓ)‖ ≤
      C * (p : ℝ) ^ ((ℓ : ℝ) * ((s : ℝ) / 4 - 1 / 2))) ∧
  (∀ s t : ℕ, 5 ≤ s → Odd s → Squarefree t → Odd t → ∃ C : ℝ, ∀ p ℓ : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ t →
    1 ≤ ℓ →
    ‖(repNum (sumSq s) ((t * p ^ (2 * ℓ) : ℕ) : ℤ) : ℂ) - singularSeriesSq s (t * p ^ (2 * ℓ))‖ ≤
      C * (p : ℝ) ^ (2 * (ℓ : ℝ) * ((s : ℝ) / 4 - 1 / 2)))

/-! ### §7.11: three squares in arithmetic progression -/

/-- **Moreno–Wagstaff, Theorem 7.7, as printed** (p. 314): if $(x, y, z)$ is a primitive solution of
$x^2 + z^2 = 2y^2$ in positive integers, there are coprime integers $r > s > 0$ of opposite parity with
$x = |r^2 - s^2 - 2rs|$, $y = r^2 + s^2$, $z = r^2 - s^2 + 2rs$.

*Erratum (missing hypothesis):* false as printed. $(x, y, z) = (1, 1, 1)$ and $(7, 5, 1)$ are primitive
solutions, but $r^2 - s^2 + 2rs \ge 7$ for $r > s > 0$; the proof assumes $0 < x < y < z$. The correct
statement adds $x < z$ (`Theorem77Corrected`). -/
@[kb "morenowagstaff2005" "Theorem 7.7 (as printed), p. 314"]
def Theorem77 : Prop :=
  ∀ x y z : ℤ, 0 < x → 0 < y → 0 < z → x ^ 2 + z ^ 2 = 2 * y ^ 2 → Int.gcd (Int.gcd x y) z = 1 →
    ∃ r s : ℤ, 0 < s ∧ s < r ∧ IsCoprime r s ∧ ¬ (r ≡ s [ZMOD 2]) ∧
      x = |r ^ 2 - s ^ 2 - 2 * r * s| ∧ y = r ^ 2 + s ^ 2 ∧ z = r ^ 2 - s ^ 2 + 2 * r * s

/-- **Moreno–Wagstaff, Theorem 7.7, corrected** (p. 314): with the hypothesis $x < z$ that the proof uses. -/
@[kb "morenowagstaff2005" "Theorem 7.7 (with x < z), p. 314"]
def Theorem77Corrected : Prop :=
  ∀ x y z : ℤ, 0 < x → x < z → x ^ 2 + z ^ 2 = 2 * y ^ 2 → 0 < y → Int.gcd (Int.gcd x y) z = 1 →
    ∃ r s : ℤ, 0 < s ∧ s < r ∧ IsCoprime r s ∧ ¬ (r ≡ s [ZMOD 2]) ∧
      x = |r ^ 2 - s ^ 2 - 2 * r * s| ∧ y = r ^ 2 + s ^ 2 ∧ z = r ^ 2 - s ^ 2 + 2 * r * s

/-- **Moreno–Wagstaff, Corollary 7.4** (p. 315): the arithmetic progressions $x^2 < y^2 < z^2$ of three squares
of positive integers are exactly $x = k|r^2 - s^2 - 2rs|$, $y = k(r^2 + s^2)$, $z = k(r^2 - s^2 + 2rs)$ with
$r > s > 0$ coprime of opposite parity and $k \ge 1$. -/
@[kb "morenowagstaff2005" "Corollary 7.4, p. 315"]
def Corollary74 : Prop :=
  ∀ x y z : ℤ, 0 < x → 0 < y → 0 < z →
    ((x ^ 2 < y ^ 2 ∧ y ^ 2 < z ^ 2 ∧ y ^ 2 - x ^ 2 = z ^ 2 - y ^ 2) ↔
      ∃ r s k : ℤ, 0 < s ∧ s < r ∧ IsCoprime r s ∧ ¬ (r ≡ s [ZMOD 2]) ∧ 0 < k ∧
        x = k * |r ^ 2 - s ^ 2 - 2 * r * s| ∧ y = k * (r ^ 2 + s ^ 2) ∧ z = k * (r ^ 2 - s ^ 2 + 2 * r * s))

/-! ### Chapter 8 -/

/-- **Moreno–Wagstaff, Theorem 8.1** (factoring integers; p. 318), mathematical core. The book's theorem asserts
a polynomial-time algorithm finding a proper factor of $n$ from two distinct representations
$n = a^2 + b^2 = c^2 + d^2$; its proof reduces to $a, b, c, d > 0$, $\gcd(a, b) = \gcd(c, d) = 1$ (otherwise a gcd
or $\sqrt n$ is a proper factor) and shows that then **both** $\gcd(ad + bc, n)$ and $\gcd(ad - bc, n)$ are proper
factors of $n$. That claim is stated here; the complexity statement (gcds are computable in polynomial time)
is not formalized. -/
@[kb "morenowagstaff2005" "Theorem 8.1, p. 318"]
def Theorem81 : Prop :=
  ∀ n a b c d : ℕ, 0 < a → 0 < b → 0 < c → 0 < d → n = a ^ 2 + b ^ 2 → n = c ^ 2 + d ^ 2 →
    a.Coprime b → c.Coprime d → ¬ (a = c ∧ b = d) → ¬ (a = d ∧ b = c) →
    (1 < Nat.gcd (a * d + b * c) n ∧ Nat.gcd (a * d + b * c) n < n) ∧
    (1 < Int.gcd ((a * d : ℤ) - b * c) n ∧ Int.gcd ((a * d : ℤ) - b * c) n < n)

/-- **Moreno–Wagstaff, Theorem 8.2** (Gauss; p. 322, cited): for a prime $p = 4k + 1$ written $p = a^2 + b^2$ with
$a \equiv 1 \pmod 4$, $a \equiv \tfrac12\binom{2k}{k} \pmod p$ (and $|a| < p/2$), i.e. $2a \equiv \binom{2k}{k}$. -/
@[kb "morenowagstaff2005" "Theorem 8.2, p. 322"]
def Theorem82 : Prop :=
  ∀ (p : ℕ) (a b : ℤ), p.Prime → p % 4 = 1 → (p : ℤ) = a ^ 2 + b ^ 2 → a ≡ 1 [ZMOD 4] →
    2 * a ≡ ((2 * ((p - 1) / 4)).choose ((p - 1) / 4) : ℤ) [ZMOD p] ∧ 2 * |a| < p

/-- **Moreno–Wagstaff, Theorem 8.3** (Jacobsthal; p. 322, cited): for a prime $p = 4k + 1$ written $p = a^2 + b^2$
with $a \equiv 1 \pmod 4$, $a = -\sum_{j=1}^{(p-1)/2} \left(\frac{j}{p}\right)\left(\frac{j^2+1}{p}\right)$. -/
@[kb "morenowagstaff2005" "Theorem 8.3, p. 322"]
def Theorem83 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (a b : ℤ), p % 4 = 1 → (p : ℤ) = a ^ 2 + b ^ 2 → a ≡ 1 [ZMOD 4] →
    a = -∑ j ∈ Finset.Icc (1 : ℤ) ((p - 1) / 2), legendreSym p j * legendreSym p (j ^ 2 + 1)

/-- $n$ is a sum of $s$ **positive** squares (Moreno–Wagstaff §8.4, p. 328). -/
@[kb "morenowagstaff2005" "§8.4, sum of s positive squares, p. 328"]
def IsSumPosSq (s n : ℕ) : Prop := ∃ x : Fin s → ℕ, (∀ i, 0 < x i) ∧ ∑ i, x i ^ 2 = n

/-- **Moreno–Wagstaff, Theorem 8.4** (Pall; p. 328, cited): let $B = \{1, 2, 4, 5, 7, 10, 13\}$. For $s \ge 6$ a
positive integer $n$ is a sum of $s$ positive squares unless $n \in \{1, \dots, s-1\}$ or $n = s + b$, $b \in B$;
for $s = 5$ the same with $b \in B \cup \{28\}$; for $s = 4$ the same with $b \in B \cup \{25, 37\}$, and also
excepting $n = 4^e n_1$, $n_1 \in \{2, 6, 14\}$. (Checked by computer for $n < 400$, $4 \le s \le 11$.) -/
@[kb "morenowagstaff2005" "Theorem 8.4, p. 328"]
def Theorem84 : Prop :=
  let B : Finset ℕ := {1, 2, 4, 5, 7, 10, 13}
  (∀ s n : ℕ, 6 ≤ s → 0 < n → (IsSumPosSq s n ↔ ¬ (n < s ∨ ∃ b ∈ B, n = s + b))) ∧
  (∀ n : ℕ, 0 < n → (IsSumPosSq 5 n ↔ ¬ (n < 5 ∨ ∃ b ∈ insert 28 B, n = 5 + b))) ∧
  (∀ n : ℕ, 0 < n → (IsSumPosSq 4 n ↔
    ¬ (n < 4 ∨ (∃ b ∈ insert 25 (insert 37 B), n = 4 + b) ∨
      ∃ e : ℕ, ∃ n₁ ∈ ({2, 6, 14} : Finset ℕ), n = 4 ^ e * n₁)))

/-- $n$ is a sum of **distinct** positive squares (Moreno–Wagstaff §8.4, p. 328); the empty sum gives $0$. -/
@[kb "morenowagstaff2005" "§8.4, sum of distinct squares, p. 328"]
def IsSumDistinctSq (n : ℕ) : Prop := ∃ S : Finset ℕ, (∀ k ∈ S, 0 < k) ∧ ∑ k ∈ S, k ^ 2 = n

/-- **Sprague's theorem** (Moreno–Wagstaff §8.4, p. 328, cited): a positive integer is a sum of distinct squares
unless it is one of $2, 3, 6, 7, 8, 11, 12, 15, 18, 19, 22, 23, 24, 27, 28, 31, 32, 33, 43, 44, 47, 48, 60, 67,
72, 76, 92, 96, 108, 112, 128$; in particular every integer $> 128$ is.

*Erratum:* the book says "exactly 32 integers, 2, 3, 6, 7, 8, 11, …, 128"; the list has **31** entries
(computed; also OEIS A001422). -/
@[kb "morenowagstaff2005" "§8.4, Sprague's theorem, p. 328"]
def SpragueTheorem : Prop :=
  ∀ n : ℕ, 0 < n → (IsSumDistinctSq n ↔ n ∉ ({2, 3, 6, 7, 8, 11, 12, 15, 18, 19, 22, 23, 24, 27, 28, 31, 32,
    33, 43, 44, 47, 48, 60, 67, 72, 76, 92, 96, 108, 112, 128} : Finset ℕ))

/-- **Moreno–Wagstaff, Theorem 8.5** (multiplicative property of the redundancy function $\mu_5$; p. 339): with
$\mu_5(m) = (m^2 + \delta) \bmod n$, if $A = 2(n - \delta) = w^2 + x^2 = y^2 + z^2$ then
$\mu_5(w)\mu_5(y) \equiv \mu_5(x)\mu_5(z) \pmod n$. (The book also assumes $0 < w, x, y, z < \sqrt n$, which only
serves to make $\mu_5$ the redundancy function of the signature scheme; the congruence holds without it.) -/
@[kb "morenowagstaff2005" "Theorem 8.5, p. 339"]
def Theorem85 : Prop :=
  ∀ n δ w x y z : ℤ, 2 * (n - δ) = w ^ 2 + x ^ 2 → 2 * (n - δ) = y ^ 2 + z ^ 2 →
    (w ^ 2 + δ) % n * ((y ^ 2 + δ) % n) ≡ (x ^ 2 + δ) % n * ((z ^ 2 + δ) % n) [ZMOD n]

end QuadFormsKB.MorenoWagstaff
