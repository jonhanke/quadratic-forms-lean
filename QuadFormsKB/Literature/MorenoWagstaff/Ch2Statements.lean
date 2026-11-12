/-
# Moreno–Wagstaff 2005, Chapter 2: definitions and statements

**Source.** C. J. Moreno and S. S. Wagstaff Jr., *Sums of Squares of Integers* (Chapman & Hall/CRC, 2005),
Chapter 2 ("Elementary methods for sums of squares and polygonal numbers"). Page numbers in the `@[kb]`
locators are the book's **printed** pages.

**Notation.** The book's $r_k(n)$ (number of $\vec x \in \mathbb Z^k$ with $x_0^2 + \dots + x_{k-1}^2 = n$) is
`Siegel.repNum (Siegel.sumSq k) n` throughout (`Siegel.repNum`, `Siegel.sumSq` are this library's
representation number and sum-of-squares form; $r_k(0) = 1$ holds since the only solution is $\vec x = 0$).
The divisor sum $\sigma(n) = \sigma_1(n)$ is Mathlib's `ArithmeticFunction.sigma 1`, the polygonal numbers are
`polygonal` below, and the book's pentagonal numbers $(3s^2+s)/2$ ($s \in \mathbb Z$) are Mathlib's
`pentagonal (-s)` (Mathlib writes $\mathrm{pentagonal}(k) = k(3k-1)/2$).

**Contents.**
* Definitions: `polygonal` (2.d1), `omega3` (Definition 2.1), `hurwitzTriples` (Definition 2.2, the book's
  $H(m)$), `oddSqRep` (2.d6, $\rho_k(m)$), the five partition sets `liouvilleA` … `liouvilleE` and the
  sums `liouvilleS`, `liouvilleW`, `liouvilleU`, `liouvilleT`, `liouvilleT₁`, `liouvilleT₂` of §2.3,
  `phiCount` (Lemma 2.6), `IsOddIn₁`, `IsEvenIn₂₃`, `IsOddIn₂₃` (2.d3, parity in a subset of variables).
* Statements (`def … : Prop`; proofs, where found, are in the companion files listed in
  `MorenoWagstaff/All.lean`): `Theorem21`, `Theorem22` (Liouville's fundamental identities), `Theorem23`,
  `Theorem24` (recursions for $\omega$ and $\sigma$), `Theorem25` (two squares), `Corollary21`, `Theorem26`
  (Jacobi, the book's two-case form), `Lemma25`, `Remark21`, `Corollary23`, `Lemma26`, `Theorem28`,
  `Theorem29` (Cauchy), `Lemma27` (Cauchy's lemma), `Theorem210` (Legendre–Nathanson).
-/
import QuadFormsKB.Siegel.FourSquaresJacobi
import QuadFormsKB.Tamagawa.Classical.BinaryJacobi
import QuadFormsKB.Literature.Classical.SumsOfSquares
import Mathlib.Combinatorics.Enumerative.Pentagonal.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

open scoped ArithmeticFunction.sigma

namespace QuadFormsKB.MorenoWagstaff

open QuadFormsKB.Siegel

/-! ### Polygonal numbers, $\omega$, $H(m)$, $\rho_k(m)$ -/

/-- **The $n$-th $r$-gonal number** $p^{(r)}_n = n + (r-2)\,\frac{n(n-1)}{2}$ (Moreno–Wagstaff §2.1, p. 12):
the sum of the first $n$ terms of the arithmetic progression with first term $1$ and common difference
$r - 2$; $p^{(r)}_0 = 0$. The book uses $r \ge 3$ (for $r = 3$, triangular numbers $n(n+1)/2$; for
$r = 4$, squares). Here `polygonal r n` is defined for every natural number `r ≥ 2` by the same formula. -/
@[kb "morenowagstaff2005" "§2.1, polygonal numbers p_n^{(r)}, p. 12"]
def polygonal (r n : ℕ) : ℕ := n + (r - 2) * (n * (n - 1) / 2)

/-- **Moreno–Wagstaff, Definition 2.1** (p. 20): for a positive integer $m$,
$\omega(m) = \#\{d \mid m : d \equiv 1 \pmod 3\} - \#\{d \mid m : d \equiv 2 \pmod 3\}$
(positive divisors $d$). The value at $m = 0$ is $0$ (Mathlib's `Nat.divisors 0 = ∅`). -/
@[kb "morenowagstaff2005" "Definition 2.1, p. 20"]
def omega3 (m : ℕ) : ℤ :=
  ((m.divisors.filter (fun d => d % 3 = 1)).card : ℤ) - ((m.divisors.filter (fun d => d % 3 = 2)).card : ℤ)

/-- **Moreno–Wagstaff, Definition 2.2** (p. 49): $H(m)$ is the number of integer triples $(a, b, c)$ with
$m = 4ac - b^2$, $0 < b$, $b < 2a$, $b < 2c$ and $b$ odd. (The set is finite, as the book shows on p. 49;
`Nat.card` would give $0$ on an infinite set.) This is the book's normalization ($H(3) = 1$, Example 2.1),
not the weighted Hurwitz class number (which gives $1/3$ at $3$). -/
@[kb "morenowagstaff2005" "Definition 2.2, p. 49"]
noncomputable def hurwitzTriples (m : ℤ) : ℕ :=
  Nat.card {t : ℤ × ℤ × ℤ // m = 4 * t.1 * t.2.2 - t.2.1 ^ 2 ∧ 0 < t.2.1 ∧ t.2.1 < 2 * t.1 ∧
    t.2.1 < 2 * t.2.2 ∧ Odd t.2.1}

/-- **$\rho_k(m)$** (Moreno–Wagstaff §2.9, p. 43): the number of ordered $k$-tuples $(x_0, \dots, x_{k-1})$ of
odd positive integers with $x_0^2 + \dots + x_{k-1}^2 = m$. -/
@[kb "morenowagstaff2005" "§2.9, rho_k(m), p. 43"]
noncomputable def oddSqRep (k : ℕ) (m : ℤ) : ℕ :=
  Nat.card {x : Fin k → ℤ // (∀ i, 0 < x i ∧ Odd (x i)) ∧ ∑ i, x i ^ 2 = m}

/-! ### Lemmas 2.1–2.3 (statements; proofs in `Ch2Lemmas.lean`) -/

/-- **Moreno–Wagstaff, Lemma 2.1** (p. 13): an odd positive integer $n$ is a square iff $\sigma(n)$ is odd. -/
@[kb "morenowagstaff2005" "Lemma 2.1, p. 13"]
def Lemma21 : Prop := ∀ n : ℕ, Odd n → (IsSquare n ↔ Odd (σ 1 n))

/-- **Moreno–Wagstaff, Lemma 2.2** (p. 13): squares are $0, 1 \bmod 4$ and $0, 1, 4 \bmod 8$; sums of two squares
are $0, 1, 2 \bmod 4$ and $0, 1, 2, 4, 5 \bmod 8$; sums of three squares are not $7 \bmod 8$. -/
@[kb "morenowagstaff2005" "Lemma 2.2, p. 13"]
def Lemma22 : Prop :=
  (∀ x : ℤ, x ^ 2 % 4 ∈ ({0, 1} : Finset ℤ)) ∧
  (∀ x y : ℤ, (x ^ 2 + y ^ 2) % 4 ∈ ({0, 1, 2} : Finset ℤ)) ∧
  (∀ x : ℤ, x ^ 2 % 8 ∈ ({0, 1, 4} : Finset ℤ)) ∧
  (∀ x y : ℤ, (x ^ 2 + y ^ 2) % 8 ∈ ({0, 1, 2, 4, 5} : Finset ℤ)) ∧
  (∀ x y z : ℤ, (x ^ 2 + y ^ 2 + z ^ 2) % 8 ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset ℤ))

/-- **Moreno–Wagstaff, Lemma 2.3** (p. 13): $r_3(4n) = r_3(n)$ and $r_2(2n) = r_2(n)$ for every $n \ge 0$. -/
@[kb "morenowagstaff2005" "Lemma 2.3, p. 13"]
def Lemma23 : Prop :=
  ∀ n : ℕ, repNum (sumSq 3) (4 * n) = repNum (sumSq 3) n ∧ repNum (sumSq 2) (2 * n) = repNum (sumSq 2) n

/-! ### §2.3: Liouville's two fundamental identities -/

/-- **Parity in a subset of variables** (Moreno–Wagstaff §2.3, p. 14): $F(x, y, z)$ is an *odd function of $x$*
if $F(-x, y, z) = -F(x, y, z)$ for all integers $x, y, z$. -/
@[kb "morenowagstaff2005" "§2.3, odd function of x, p. 14"]
def IsOddIn₁ {M : Type*} [Neg M] (F : ℤ → ℤ → ℤ → M) : Prop := ∀ x y z, F (-x) y z = -F x y z

/-- $F(x, y, z)$ is an *even function of $y, z$* (Moreno–Wagstaff §2.3, p. 14): $F(x, -y, -z) = F(x, y, z)$. -/
@[kb "morenowagstaff2005" "§2.3, even function of y, z, p. 14"]
def IsEvenIn₂₃ {M : Type*} (F : ℤ → ℤ → ℤ → M) : Prop := ∀ x y z, F x (-y) (-z) = F x y z

/-- $F(x, y, z)$ is an *odd function of $y, z$* (Moreno–Wagstaff §2.3, p. 14): $F(x, -y, -z) = -F(x, y, z)$. -/
@[kb "morenowagstaff2005" "§2.3, odd function of y, z, p. 14"]
def IsOddIn₂₃ {M : Type*} [Neg M] (F : ℤ → ℤ → ℤ → M) : Prop := ∀ x y z, F x (-y) (-z) = -F x y z

/-- **Partition (a)** of Moreno–Wagstaff §2.3 (p. 15): triples $(i, d, \delta)$ with $i \in \mathbb Z$, $d, \delta > 0$
and $n = \lambda i^2 + \mu i + (\lambda\delta + \mu) d$. Partition (b) is `liouvilleA λ (-μ) n`. -/
@[kb "morenowagstaff2005" "§2.3, partitions (a), (b), p. 15"]
def liouvilleA (lam mu : ℝ) (n : ℕ) : Set (ℤ × ℤ × ℤ) :=
  {p | 0 < p.2.1 ∧ 0 < p.2.2 ∧
    (n : ℝ) = lam * (p.1 : ℝ) ^ 2 + mu * p.1 + (lam * p.2.2 + mu) * p.2.1}

/-- **Partition (c)** (p. 15): triples $(h, \Delta, \Delta')$ with $h \in \mathbb Z$, $\Delta, \Delta' > 0$ and
$n = \lambda h^2 + \mu h + \lambda \Delta\Delta'$. -/
@[kb "morenowagstaff2005" "§2.3, partition (c), p. 15"]
def liouvilleC (lam mu : ℝ) (n : ℕ) : Set (ℤ × ℤ × ℤ) :=
  {p | 0 < p.2.1 ∧ 0 < p.2.2 ∧ (n : ℝ) = lam * (p.1 : ℝ) ^ 2 + mu * p.1 + lam * p.2.1 * p.2.2}

/-- **Partition (d)** (p. 15): pairs $(\Delta, \Delta')$ of positive integers of the same parity with
$n = \lambda\left(\frac{\Delta+\Delta'}{2}\right)^2 + \mu\,\frac{\Delta-\Delta'}{2}$. -/
@[kb "morenowagstaff2005" "§2.3, partition (d), p. 15"]
def liouvilleD (lam mu : ℝ) (n : ℕ) : Set (ℤ × ℤ) :=
  {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 ≡ p.2 [ZMOD 2] ∧
    (n : ℝ) = lam * (((p.1 + p.2 : ℤ) : ℝ) / 2) ^ 2 + mu * (((p.1 - p.2 : ℤ) : ℝ) / 2)}

/-- **Partition (e)** (p. 15): integers $s$ with $n = \lambda s^2 + \mu s$. -/
@[kb "morenowagstaff2005" "§2.3, partition (e), p. 15"]
def liouvilleE (lam mu : ℝ) (n : ℕ) : Set ℤ := {s | (n : ℝ) = lam * (s : ℝ) ^ 2 + mu * s}

/-- **The sum $S$** of §2.3 (p. 15): $S = \sum_{(a)} F(\delta - 2i,\ d + i,\ 2d + 2i - \delta)$; the book's $S'$ is
`liouvilleS F λ (-μ) n` (the same summand over partition (b)). All five partition sets are finite when
$\lambda > |\mu|$ (p. 15); the sums are `finsum`s over them. -/
@[kb "morenowagstaff2005" "§2.3, the sums S and S', p. 15"]
noncomputable def liouvilleS {M : Type*} [AddCommMonoid M] (F : ℤ → ℤ → ℤ → M) (lam mu : ℝ) (n : ℕ) : M :=
  ∑ᶠ p ∈ liouvilleA lam mu n, F (p.2.2 - 2 * p.1) (p.2.1 + p.1) (2 * p.2.1 + 2 * p.1 - p.2.2)

/-- **The sum $W$** of §2.3 (p. 15): $W = \sum_{(c)} F(\Delta + \Delta',\ h,\ \Delta - \Delta')$. -/
@[kb "morenowagstaff2005" "§2.3, the sum W, p. 15"]
noncomputable def liouvilleW {M : Type*} [AddCommMonoid M] (F : ℤ → ℤ → ℤ → M) (lam mu : ℝ) (n : ℕ) : M :=
  ∑ᶠ p ∈ liouvilleC lam mu n, F (p.2.1 + p.2.2) p.1 (p.2.1 - p.2.2)

/-- **The sum $U$** of §2.3 (p. 15): $U = \sum_{(d)} F\!\left(\Delta + \Delta',\ \frac{\Delta - \Delta'}{2},\ \Delta - \Delta'\right)$
(the middle argument is an integer since $\Delta \equiv \Delta' \pmod 2$). -/
@[kb "morenowagstaff2005" "§2.3, the sum U, p. 15"]
noncomputable def liouvilleU {M : Type*} [AddCommMonoid M] (F : ℤ → ℤ → ℤ → M) (lam mu : ℝ) (n : ℕ) : M :=
  ∑ᶠ p ∈ liouvilleD lam mu n, F (p.1 + p.2) ((p.1 - p.2) / 2) (p.1 - p.2)

/-- The inner sum of $T$: $\sum_{j=1}^{2|s|-1} F(2|s| - j,\ |s|,\ 2|s| - j)$. -/
def liouvilleTTerm {M : Type*} [AddCommMonoid M] (F : ℤ → ℤ → ℤ → M) (s : ℤ) : M :=
  ∑ j ∈ Finset.Icc (1 : ℤ) (2 * |s| - 1), F (2 * |s| - j) |s| (2 * |s| - j)

/-- **The sum $T$** of §2.3 (p. 15): $T = \sum_{(e)} \sum_{j=1}^{2|s|-1} F(2|s| - j,\ |s|,\ 2|s| - j)$. -/
@[kb "morenowagstaff2005" "§2.3, the sum T, p. 15"]
noncomputable def liouvilleT {M : Type*} [AddCommMonoid M] (F : ℤ → ℤ → ℤ → M) (lam mu : ℝ) (n : ℕ) : M :=
  ∑ᶠ s ∈ liouvilleE lam mu n, liouvilleTTerm F s

/-- **The sum $T_1$** of Theorem 2.2 (p. 18): the part of $T$ with $s$ a positive solution of
$n = \lambda s^2 + \mu s$. The book's $T_2$ is `liouvilleT₁ F λ (-μ) n`. -/
@[kb "morenowagstaff2005" "Theorem 2.2, the sums T_1 and T_2, p. 18"]
noncomputable def liouvilleT₁ {M : Type*} [AddCommMonoid M] (F : ℤ → ℤ → ℤ → M) (lam mu : ℝ) (n : ℕ) : M :=
  ∑ᶠ s ∈ liouvilleE lam mu n ∩ {s | 0 < s}, liouvilleTTerm F s

/-- **Moreno–Wagstaff, Theorem 2.1** (First Fundamental Identity, Liouville; p. 15): let $\lambda, \mu$ be real
with $\lambda > |\mu|$ and let $F : \mathbb Z^3 \to \mathbb R$ be an odd function of $x$ and an even function of
$(y, z)$. Then for every positive integer $n$, $S + S' = T + W - U$. -/
@[kb "morenowagstaff2005" "Theorem 2.1, p. 15"]
def Theorem21 : Prop :=
  ∀ (lam mu : ℝ), |mu| < lam → ∀ F : ℤ → ℤ → ℤ → ℝ, IsOddIn₁ F → IsEvenIn₂₃ F → ∀ n : ℕ, 0 < n →
    liouvilleS F lam mu n + liouvilleS F lam (-mu) n =
      liouvilleT F lam mu n + liouvilleW F lam mu n - liouvilleU F lam mu n

/-- **Moreno–Wagstaff, Theorem 2.2** (Second Fundamental Identity; p. 18): with the notation of Theorem 2.1, if
$F$ is an odd function of $x$ and an odd function of $(y, z)$, then $S - S' = T_1 - T_2 + W - U$ for every
positive integer $n$. -/
@[kb "morenowagstaff2005" "Theorem 2.2, p. 18"]
def Theorem22 : Prop :=
  ∀ (lam mu : ℝ), |mu| < lam → ∀ F : ℤ → ℤ → ℤ → ℝ, IsOddIn₁ F → IsOddIn₂₃ F → ∀ n : ℕ, 0 < n →
    liouvilleS F lam mu n - liouvilleS F lam (-mu) n =
      liouvilleT₁ F lam mu n - liouvilleT₁ F lam (-mu) n + liouvilleW F lam mu n - liouvilleU F lam mu n

/-! ### §2.4: Euler's recurrences -/

/-- The integers $i$ with $(3i^2 + i)/2 < n$ (a finite set, contained in $[-n, n]$). -/
def pentIdx (n : ℕ) : Finset ℤ := (Finset.Icc (-(n : ℤ)) n).filter (fun i => pentagonal (-i) < n)

/-- **Moreno–Wagstaff, Theorem 2.3** (Recursion formula for $\omega$; p. 20): for every positive integer $n$,
$\sum_{i \in \mathbb Z,\ (3i^2+i)/2 < n} (-1)^i\, \omega\!\left(n - \frac{3i^2+i}{2}\right)$ is $0$ if $n$ is not a
pentagonal number $(3s^2+s)/2$ ($s \in \mathbb Z$), and is $(-1)^s s$ if $n = (3s^2+s)/2$. -/
@[kb "morenowagstaff2005" "Theorem 2.3, p. 20"]
def Theorem23 : Prop :=
  ∀ n : ℕ, 0 < n →
    let L := ∑ i ∈ pentIdx n, (-1 : ℤ) ^ i.natAbs * omega3 (n - pentagonal (-i))
    ((∀ s : ℤ, pentagonal (-s) ≠ n) → L = 0) ∧ (∀ s : ℤ, pentagonal (-s) = n → L = (-1) ^ s.natAbs * s)

/-- **Moreno–Wagstaff, Theorem 2.4** (Euler's recurrence for $\sigma$; p. 22): for every positive integer $n$,
$\sum_{(3i^2+i)/2 < n} (-1)^i\, \sigma\!\left(n - \frac{3i^2+i}{2}\right)$ is $0$ if $n$ is not pentagonal and
$(-1)^{s-1} n$ if $n = (3s^2+s)/2$. -/
@[kb "morenowagstaff2005" "Theorem 2.4, p. 22"]
def Theorem24 : Prop :=
  ∀ n : ℕ, 0 < n →
    let L := ∑ i ∈ pentIdx n, (-1 : ℤ) ^ i.natAbs * (σ 1 (n - pentagonal (-i)) : ℤ)
    ((∀ s : ℤ, pentagonal (-s) ≠ n) → L = 0) ∧
      (∀ s : ℤ, pentagonal (-s) = n → L = (-1) ^ (s.natAbs + 1) * n)

/-! ### §2.6–2.7: two and four squares -/

/-- **Moreno–Wagstaff, Theorem 2.5** (Sums of two squares, Gauss; p. 27), first and third displays: for $n \ge 1$,
$r_2(n) = 4 \sum_{d \mid n,\ d \text{ odd}} (-1)^{(d-1)/2} = 4\,(\#\{d \mid n : d \equiv 1 \bmod 4\} - \#\{d \mid n : d \equiv 3 \bmod 4\})$;
and the prime-power table: for $p$ prime and $e \ge 0$, $r_2(p^e) = 4$ if $p = 2$ or ($p \equiv 3 \bmod 4$, $e$ even),
$4(e+1)$ if $p \equiv 1 \bmod 4$, and $0$ if $p \equiv 3 \bmod 4$ and $e$ odd. -/
@[kb "morenowagstaff2005" "Theorem 2.5, p. 27"]
def Theorem25 : Prop :=
  (∀ n : ℕ, 0 < n →
    (repNum (sumSq 2) n : ℤ) = 4 * ∑ d ∈ n.divisors.filter Odd, (-1 : ℤ) ^ ((d - 1) / 2) ∧
    (repNum (sumSq 2) n : ℤ) = 4 * (((n.divisors.filter (· % 4 = 1)).card : ℤ) -
      (n.divisors.filter (· % 4 = 3)).card)) ∧
  (∀ p e : ℕ, p.Prime →
    repNum (sumSq 2) ((p : ℤ) ^ e) =
      if p = 2 ∨ (p % 4 = 3 ∧ Even e) then 4 else if p % 4 = 1 then 4 * (e + 1) else 0)

/-- **Moreno–Wagstaff, Theorem 2.5** (p. 27), second display (the $\tau$-product form): write
$n = 2^\gamma \prod p_i^{\alpha_i} \prod q_j^{\beta_j}$ with $p_i \equiv 1$, $q_j \equiv 3 \pmod 4$. Then
$r_2(n) = 4\,\tau\!\left(\prod p_i^{\alpha_i}\right)$ if every $\beta_j$ is even, and $r_2(n) = 0$ otherwise.
Here $\prod p_i^{\alpha_i}$ is written as the product over the primes $p \equiv 1 \bmod 4$ of $p^{v_p(n)}$
and $\tau$ is the number of divisors. -/
@[kb "morenowagstaff2005" "Theorem 2.5 (tau form), p. 27"]
def Theorem25Tau : Prop :=
  ∀ n : ℕ, 0 < n →
    repNum (sumSq 2) n =
      if ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (n.factorization q) then
        4 * (∏ p ∈ n.primeFactors.filter (· % 4 = 1), p ^ n.factorization p).divisors.card
      else 0

/-- **Moreno–Wagstaff, Corollary 2.1** (p. 28): a prime $p \equiv 1 \pmod 4$ is $x^2 + y^2$ for **unique** positive
integers $x, y$ with $x$ odd and $y$ even. -/
@[kb "morenowagstaff2005" "Corollary 2.1, p. 28"]
def Corollary21 : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 1 →
    ∃! xy : ℕ × ℕ, 0 < xy.1 ∧ 0 < xy.2 ∧ Odd xy.1 ∧ Even xy.2 ∧ p = xy.1 ^ 2 + xy.2 ^ 2

/-- **Moreno–Wagstaff, Corollary 2.2** (p. 28): a positive integer has at least as many divisors $\equiv 1 \pmod 4$
as divisors $\equiv 3 \pmod 4$. -/
@[kb "morenowagstaff2005" "Corollary 2.2, p. 28"]
def Corollary22 : Prop :=
  ∀ n : ℕ, 0 < n → (n.divisors.filter (· % 4 = 3)).card ≤ (n.divisors.filter (· % 4 = 1)).card

/-- **Moreno–Wagstaff, Theorem 2.6** (Jacobi; p. 29): for $n \ge 1$, $r_4(n) = 8\sigma(n)$ if $n$ is odd and
$r_4(n) = 24\sigma(m)$ if $n$ is even, $m$ its largest odd divisor (`ordCompl[2] n`, i.e. $n / 2^{v_2(n)}$). -/
@[kb "morenowagstaff2005" "Theorem 2.6, p. 29"]
def Theorem26 : Prop :=
  ∀ n : ℕ, 0 < n →
    repNum (sumSq 4) n = if Odd n then 8 * σ 1 n else 24 * σ 1 (ordCompl[2] n)

/-- **Moreno–Wagstaff, Lemma 2.5** (p. 29): for $n \ge 1$, $r_4(2n) = 3 r_4(n)$ if $n$ is odd and
$r_4(2n) = r_4(n)$ if $n$ is even. -/
@[kb "morenowagstaff2005" "Lemma 2.5, p. 29"]
def Lemma25 : Prop :=
  ∀ n : ℕ, 0 < n →
    repNum (sumSq 4) (2 * n) = if Odd n then 3 * repNum (sumSq 4) n else repNum (sumSq 4) n

/-- **Moreno–Wagstaff, §2.7, multiplicativity of $r_4/8$** (p. 33): $f_4(n) = r_4(n)/r_4(1) = r_4(n)/8$ is a
multiplicative function: $r_4(mn)\,r_4(1) = r_4(m)\,r_4(n)$ for coprime $m, n$. -/
@[kb "morenowagstaff2005" "§2.7, r_4(n)/8 multiplicative, p. 33"]
def R4Multiplicative : Prop :=
  ∀ m n : ℕ, m.Coprime n → repNum (sumSq 4) (m * n) * 8 = repNum (sumSq 4) m * repNum (sumSq 4) n

/-- **Moreno–Wagstaff, Remark 2.1** (p. 33): for odd $m \ge 1$, $4m$ is a sum of four squares of odd integers
in $16\sigma(m)$ ways (ordered, signed), and of four odd positive integers in $\sigma(m)$ ways. -/
@[kb "morenowagstaff2005" "Remark 2.1, p. 33"]
def Remark21 : Prop :=
  ∀ m : ℕ, Odd m →
    Nat.card {x : Fin 4 → ℤ // (∀ i, Odd (x i)) ∧ ∑ i, x i ^ 2 = 4 * (m : ℤ)} = 16 * σ 1 m ∧
    oddSqRep 4 (4 * m) = σ 1 m

/-! ### §2.9–2.10: three squares -/

/-- **Moreno–Wagstaff, Corollary 2.3** (p. 43): every positive integer is a sum of three triangular numbers
$\frac{x(x+1)}{2}$, $x \ge 0$. -/
@[kb "morenowagstaff2005" "Corollary 2.3, p. 43"]
def Corollary23 : Prop :=
  ∀ n : ℕ, 0 < n → ∃ x y z : ℕ, n = x * (x + 1) / 2 + y * (y + 1) / 2 + z * (z + 1) / 2

/-- **The count $\varphi(a, b, \alpha, \beta, m)$ of Lemma 2.6** (p. 48): the number of integer solutions $(x, y)$ of
$ax + by = m$ with $|x| < b$, $y > a$, $x \equiv \alpha$, $y \equiv \beta \pmod 2$ and $y \not\equiv a \pmod{2a}$ (printed "$y \not\equiv a$"; the machine-read text drops the slash). -/
@[kb "morenowagstaff2005" "Lemma 2.6, the count phi, p. 48"]
noncomputable def phiCount (a b α β m : ℤ) : ℕ :=
  Nat.card {xy : ℤ × ℤ // a * xy.1 + b * xy.2 = m ∧ |xy.1| < b ∧ a < xy.2 ∧ xy.1 ≡ α [ZMOD 2] ∧
    xy.2 ≡ β [ZMOD 2] ∧ ¬ xy.2 ≡ a [ZMOD 2 * a]}

/-- **Moreno–Wagstaff, Lemma 2.6** (p. 48): for positive integers $a, b$, every integer $m$ and
$\alpha, \beta \in \{0, 1\}$, $\varphi(a, b, \alpha, \beta, m) = \varphi(b, a, \beta, \alpha, m)$. -/
@[kb "morenowagstaff2005" "Lemma 2.6, p. 48"]
def Lemma26 : Prop :=
  ∀ a b m α β : ℤ, 0 < a → 0 < b → α ∈ ({0, 1} : Set ℤ) → β ∈ ({0, 1} : Set ℤ) →
    phiCount a b α β m = phiCount b a β α m

/-- **Moreno–Wagstaff, Theorem 2.8** (Gauss, *Disquisitiones* Art. 291; p. 50): for every positive integer
$k \equiv 3 \pmod 8$, $\rho_3(k) = H(k)$, and therefore $r_3(k) = 8H(k)$. -/
@[kb "morenowagstaff2005" "Theorem 2.8, p. 50"]
def Theorem28 : Prop :=
  ∀ k : ℕ, k % 8 = 3 → oddSqRep 3 k = hurwitzTriples k ∧ repNum (sumSq 3) k = 8 * hurwitzTriples k

/-! ### §2.11: polygonal numbers -/

/-- **Moreno–Wagstaff, Theorem 2.9** (Cauchy's polygonal number theorem; p. 54): for integers $m \ge 3$ and
$n \ge 1$ there are $t, u, v, w \ge 0$ and $0 \le r \le m - 2$ with
$n = p^{(m+2)}_t + p^{(m+2)}_u + p^{(m+2)}_v + p^{(m+2)}_w + r$, where
$p^{(m+2)}_t = t + m\,\frac{t^2 - t}{2}$. So $n$ is a sum of $m + 2$ polygonal numbers of order $m + 2$, at most
four of them different from $0$ and $1$. -/
@[kb "morenowagstaff2005" "Theorem 2.9, p. 54"]
def Theorem29 : Prop :=
  ∀ m n : ℕ, 3 ≤ m → 0 < n → ∃ t u v w r : ℕ, r ≤ m - 2 ∧
    n = polygonal (m + 2) t + polygonal (m + 2) u + polygonal (m + 2) v + polygonal (m + 2) w + r

/-- **Moreno–Wagstaff, Lemma 2.7** (Cauchy's lemma; p. 55): for odd positive integers $k, s$ with $s^2 < 4k$
and $3k < s^2 + 2s + 4$ there are nonnegative integers $t, u, v, w$ with $k = t^2 + u^2 + v^2 + w^2$ and
$s = t + u + v + w$. -/
@[kb "morenowagstaff2005" "Lemma 2.7, p. 55"]
def Lemma27 : Prop :=
  ∀ k s : ℕ, Odd k → Odd s → s ^ 2 < 4 * k → 3 * k < s ^ 2 + 2 * s + 4 →
    ∃ t u v w : ℕ, k = t ^ 2 + u ^ 2 + v ^ 2 + w ^ 2 ∧ s = t + u + v + w

/-- **Moreno–Wagstaff, Theorem 2.10** (Legendre, in Nathanson's form; p. 57, cited, not proved in the book):
let $m \ge 3$. If $m$ is even, every integer $n \ge 28 m^3$ is a sum of five polygonal numbers of order $m + 2$,
at least one of which is $0$ or $1$; if $m$ is odd, every integer $n \ge 28 m^3$ is a sum of four polygonal
numbers of order $m + 2$. -/
@[kb "morenowagstaff2005" "Theorem 2.10, p. 57"]
def Theorem210 : Prop :=
  ∀ m n : ℕ, 3 ≤ m → 28 * m ^ 3 ≤ n →
    (Even m → ∃ t u v w x : ℕ, x ≤ 1 ∧
      n = polygonal (m + 2) t + polygonal (m + 2) u + polygonal (m + 2) v + polygonal (m + 2) w +
        polygonal (m + 2) x) ∧
    (Odd m → ∃ t u v w : ℕ,
      n = polygonal (m + 2) t + polygonal (m + 2) u + polygonal (m + 2) v + polygonal (m + 2) w)

end QuadFormsKB.MorenoWagstaff
