/-
# Conway–Sloane, Ch. 15, §4: $p$-adic numbers, the extended gcd and Jacobi–Legendre symbol

**Source.** J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §4
(printed pp. 367–370; key `conwaysloane1999`; printed page = PDF page of the chapter file + 351).

**Defines**
* `padicMetric` ($d_p(x,y)$, §4.1, p. 367) as `padicNorm p (x - y)`;
* `extGcd` ((14), p. 368): the greatest common divisor of two nonzero integers with $-1$ treated as a prime,
  written exactly as the book does (a sign $(-1)^{\min(a,\alpha)}$ times a product over the odd and even primes);
* `ExtCoprime`: $(n,\nu) = 1$;
* `extJacobi` (§4.3, p. 368): the extended Jacobi–Legendre symbol $\left(\frac{\nu}{n}\right)$, defined for
  $(n,\nu)=1$ (and $0$ otherwise, a convention of this file).

**Proves**
* `padicMetric_five_two_fiftytwo`, `padicMetric_three_inv27_zero`: $d_5(2,52) = 1/25$, $d_3(1/27, 0) = 27$;
* `padicMetric_eq_zpow`: $d_p(x,y) = p^{-k}$ with $p^k$ the exact power of $p$ in $x - y$;
* `extGcd_eq`: $(n,\nu) = \gcd(n,\nu)$, with a minus sign exactly when both are negative; `extCoprime_iff`;
* `not_extCoprime_of_neg`: two negative numbers are never coprime (§4.3);
* `extJacobi_of_pos_odd`, `extJacobi_two`, `extJacobi_eq`: comparison with Mathlib's `jacobiSym` and `ZMod.χ₈`;
  `extJacobi_mul`: multiplicativity in $n$;
* `extJacobi_reciprocity`: the law of quadratic reciprocity on p. 369, via Mathlib's `jacobiSym.quadratic_reciprocity_if`,
  in the *corrected* form (exception on the odd parts); `extJacobi_reciprocity_printed_of_odd` is the law as printed
  for odd $n, \nu$; `PrintedReciprocity` is the law exactly as printed and `not_printedReciprocity` refutes it
  ($\nu = 7$, $n = 6$). **Erratum**: the printed exception "$n \equiv \nu \equiv -1 \pmod 4$"
  must read "the odd parts of $n$ and $\nu$ are both $\equiv -1 \pmod 4$" when $n$ or $\nu$ is even.

**Theorem 2 (§4.4, pp. 369–370).** Restated (`theorem2_odd`, `theorem2_dyadic`) from the library's
`Cassels.exists_canonical` and `Cassels.exists_dyadic_decomp`, for *nonsingular* forms over $\mathbb Q_p$ up to
$\mathbb Z_p$-equivalence. The book's statement also covers singular forms; that case is *not* formalized.

**Deviations.** The factor $\left(\frac{\nu}{-1}\right) = 1$ is not written (it is $1$ by the book whenever the symbol is
defined); $\left(\frac{\nu}{2}\right)$ is Mathlib's `ZMod.χ₈` on $\nu \bmod 8$, which equals the book's $\pm1$ for odd $\nu$.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.LocalGlobal.ConwaySloane
import QuadFormsKB.Literature.Cassels.Ch8.CanonicalExists
import QuadFormsKB.Literature.Cassels.Ch8.Dyadic

namespace QuadFormsKB
namespace ConwaySloane
namespace PAdic

open Matrix

/-! ### §4.1: the $p$-adic metric -/

/-- **The $p$-adic metric** $d_p(x,y) = 1/p^k$, where $p^k$ is the exact power of $p$ in $x - y$ (and $0$ for
$x = y$): this is `padicNorm p (x - y)` (Conway–Sloane, §4.1, p. 367). -/
@[kb "conwaysloane1999" "Ch. 15, §4.1, p. 367"]
def padicMetric (p : ℕ) [Fact p.Prime] (x y : ℚ) : ℚ := padicNorm p (x - y)

/-- For $x \ne y$, $d_p(x,y) = p^{-k}$ with $k = v_p(x-y)$ (the exponent of the exact power of $p$). -/
@[kb "conwaysloane1999" "Ch. 15, §4.1, p. 367"]
theorem padicMetric_eq_zpow (p : ℕ) [Fact p.Prime] {x y : ℚ} (h : x ≠ y) :
    padicMetric p x y = (p : ℚ) ^ (-padicValRat p (x - y)) :=
  padicNorm.eq_zpow_of_nonzero (sub_ne_zero.2 h)

instance factPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The first example of §4.1: $d_5(2, 52) = 1/25$. -/
@[kb "conwaysloane1999" "Ch. 15, §4.1, p. 367"]
theorem padicMetric_five_two_fiftytwo : padicMetric 5 2 52 = 1 / 25 := by
  rw [padicMetric, padicNorm.eq_zpow_of_nonzero (by norm_num)]
  have h : padicValRat 5 ((2 : ℚ) - 52) = 2 := by
    have h : ((2 : ℚ) - 52) = ((-50 : ℤ) : ℚ) := by norm_num
    rw [h, padicValRat.of_int]
    have : padicValInt 5 (-50) = 2 := by
      have h50 : (50 : ℕ) = 5 ^ 2 * 2 := by norm_num
      rw [padicValInt, Int.natAbs_neg]
      change padicValNat 5 50 = 2
      rw [h50, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [this]; rfl
  rw [h]; norm_num

/-- The second example of §4.1: $d_3(1/27, 0) = 27$. -/
@[kb "conwaysloane1999" "Ch. 15, §4.1, p. 367"]
theorem padicMetric_three_inv27_zero : padicMetric 3 (1 / 27) 0 = 27 := by
  rw [padicMetric, sub_zero, padicNorm.eq_zpow_of_nonzero (by norm_num)]
  have h : padicValRat 3 ((1 : ℚ) / 27) = -3 := by
    have h : ((1 : ℚ) / 27) = ((3 : ℚ) ^ 3)⁻¹ := by norm_num
    have h3 : padicValRat 3 (3 : ℚ) = 1 := by
      exact_mod_cast padicValRat.self (p := 3) (by norm_num)
    rw [h, padicValRat.inv, padicValRat.pow (q := (3 : ℚ)), h3]
    norm_num
  rw [h]; norm_num

/-! ### §4.3: the extended greatest common divisor (14) -/

/-- The exponent $a \in \{0,1\}$ of $-1$ in $n = (-1)^a 2^b 3^c \cdots$. -/
def negExp (n : ℤ) : ℕ := if n < 0 then 1 else 0

/-- **The extended greatest common divisor (14)** (Conway–Sloane, §4.3, p. 368): for nonzero integers
$n = (-1)^a 2^b 3^c \cdots$ and $\nu = (-1)^\alpha 2^\beta 3^\gamma \cdots$ (here $a, \alpha \in \{0,1\}$ is `negExp`),
$(n,\nu) = (-1)^{\min(a,\alpha)} 2^{\min(b,\beta)} 3^{\min(c,\gamma)} \cdots$. The product runs over the primes dividing
$n$ or $\nu$; the exponent of $p$ in $n$ is `n.natAbs.factorization p`. (For $n$ or $\nu$ zero the value is the
formula's value and has no meaning in the book.) -/
@[kb "conwaysloane1999" "Ch. 15, §4.3, (14), p. 368"]
def extGcd (n ν : ℤ) : ℤ :=
  (-1) ^ min (negExp n) (negExp ν) *
    ∏ p ∈ n.natAbs.primeFactors ∪ ν.natAbs.primeFactors,
      (p : ℤ) ^ min (n.natAbs.factorization p) (ν.natAbs.factorization p)

/-- The positive part of `extGcd` is the ordinary gcd. -/
theorem prod_min_factorization_eq_gcd {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∏ p ∈ a.primeFactors ∪ b.primeFactors, p ^ min (a.factorization p) (b.factorization p) =
      Nat.gcd a b := by
  have hg : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left ha
  have hf : ∀ p, min (a.factorization p) (b.factorization p) = (Nat.gcd a b).factorization p := by
    intro p; rw [Nat.factorization_gcd ha hb]; rfl
  simp_rw [hf]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hg]
  rw [Finsupp.prod, Nat.support_factorization]
  refine (Finset.prod_subset ?_ ?_).symm
  · intro p hp
    rcases Nat.mem_primeFactors.1 hp with ⟨h1, h2, -⟩
    exact Finset.mem_union_left _ (Nat.mem_primeFactors.2 ⟨h1, h2.trans (Nat.gcd_dvd_left a b), ha⟩)
  · intro p _ hp
    have : (Nat.gcd a b).factorization p = 0 := by
      by_contra h
      exact hp (by rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.2 h)
    rw [this, pow_zero]

/-- **(14) is the usual gcd, with a minus sign exactly when both numbers are negative.** -/
@[kb "conwaysloane1999" "Ch. 15, §4.3, (14), p. 368"]
theorem extGcd_eq {n ν : ℤ} (hn : n ≠ 0) (hν : ν ≠ 0) :
    extGcd n ν = if n < 0 ∧ ν < 0 then -(Int.gcd n ν : ℤ) else (Int.gcd n ν : ℤ) := by
  have h := prod_min_factorization_eq_gcd (Int.natAbs_ne_zero.2 hn) (Int.natAbs_ne_zero.2 hν)
  have h' : (∏ p ∈ n.natAbs.primeFactors ∪ ν.natAbs.primeFactors,
      (p : ℤ) ^ min (n.natAbs.factorization p) (ν.natAbs.factorization p)) = (Int.gcd n ν : ℤ) := by
    have := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at this
    exact this
  rw [extGcd, h']
  by_cases h1 : n < 0 <;> by_cases h2 : ν < 0 <;> simp [negExp, h1, h2]

/-- Coprimality in the extended sense: $(n,\nu) = 1$ for nonzero $n, \nu$. -/
@[kb "conwaysloane1999" "Ch. 15, §4.3, (14), p. 368"]
def ExtCoprime (n ν : ℤ) : Prop := n ≠ 0 ∧ ν ≠ 0 ∧ extGcd n ν = 1

/-- $(n,\nu) = 1$ iff the integers are nonzero, not both negative, and coprime in the usual sense. -/
@[kb "conwaysloane1999" "Ch. 15, §4.3, (14), p. 368"]
theorem extCoprime_iff {n ν : ℤ} :
    ExtCoprime n ν ↔ n ≠ 0 ∧ ν ≠ 0 ∧ ¬ (n < 0 ∧ ν < 0) ∧ Int.gcd n ν = 1 := by
  constructor
  · rintro ⟨hn, hν, h⟩
    rw [extGcd_eq hn hν] at h
    by_cases hb : n < 0 ∧ ν < 0
    · rw [if_pos hb] at h
      have := Int.natCast_nonneg (Int.gcd n ν)
      omega
    · rw [if_neg hb] at h
      exact ⟨hn, hν, hb, by exact_mod_cast h⟩
  · rintro ⟨hn, hν, hb, hg⟩
    refine ⟨hn, hν, ?_⟩
    rw [extGcd_eq hn hν, if_neg hb, hg]; rfl

/-- **Two negative numbers are never coprime** (Conway–Sloane, §4.3, p. 368): $(n,\nu) \ne 1$ if $n, \nu < 0$. -/
@[kb "conwaysloane1999" "Ch. 15, §4.3, p. 368"]
theorem not_extCoprime_of_neg {n ν : ℤ} (hn : n < 0) (hν : ν < 0) : ¬ ExtCoprime n ν := by
  rw [extCoprime_iff]; rintro ⟨-, -, h, -⟩; exact h ⟨hn, hν⟩

theorem ExtCoprime.symm {n ν : ℤ} (h : ExtCoprime n ν) : ExtCoprime ν n := by
  rw [extCoprime_iff] at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h2, h1, fun h => h3 ⟨h.2, h.1⟩, by rwa [Int.gcd_comm]⟩

/-! ### §4.3: the extended Jacobi–Legendre symbol -/

open scoped Classical in
/-- **The extended Jacobi–Legendre symbol** $\left(\frac{\nu}{n}\right)$ (Conway–Sloane, §4.3, p. 368), for
$(n,\nu) = 1$ (`ExtCoprime n ν`; the value is $0$ outside this range, a convention of this file). For
$n = (-1)^a 2^b 3^c \cdots$ it is $\left(\frac{\nu}{-1}\right)^a \left(\frac{\nu}{2}\right)^b \left(\frac{\nu}{3}\right)^c \cdots$
with $\left(\frac{\nu}{-1}\right) = 1$ (so that factor is omitted), $\left(\frac{\nu}{2}\right) = \pm1$ as
$\nu \equiv \pm1, \pm3 \pmod 8$ (`ZMod.χ₈`), and $\left(\frac{\nu}{p}\right)$ the Legendre symbol for odd primes $p$
(Mathlib's `jacobiSym ν p`, which equals `legendreSym p ν`). -/
@[kb "conwaysloane1999" "Ch. 15, §4.3, p. 368"]
noncomputable def extJacobi (ν n : ℤ) : ℤ :=
  if ExtCoprime n ν then
    ZMod.χ₈ (ν : ZMod 8) ^ n.natAbs.factorization 2 *
      (n.natAbs.factorization.erase 2).prod fun p k => jacobiSym ν p ^ k
  else 0

theorem jacobiSym_mul_right_coprime (ν : ℤ) (x y : ℕ) (h : Nat.Coprime x y) :
    jacobiSym ν (x * y) = jacobiSym ν x * jacobiSym ν y := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · rw [Nat.coprime_zero_left] at h; subst h; simp
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · rw [Nat.coprime_zero_right] at h; subst h; simp
  haveI : NeZero x := ⟨hx.ne'⟩
  haveI : NeZero y := ⟨hy.ne'⟩
  exact jacobiSym.mul_right ν x y

/-- The symbol for $n \ne 0$ in closed form: $\left(\frac{\nu}{n}\right) = \chi_8(\nu)^{b}\,\left(\frac{\nu}{n'}\right)$
with $n = \pm 2^b n'$, $n'$ odd, using Mathlib's Jacobi symbol for the odd part $n'$. -/
@[kb "conwaysloane1999" "Ch. 15, §4.3, p. 368"]
theorem extJacobi_eq {n ν : ℤ} (h : ExtCoprime n ν) :
    extJacobi ν n = ZMod.χ₈ (ν : ZMod 8) ^ n.natAbs.factorization 2 *
      jacobiSym ν (n.natAbs / 2 ^ n.natAbs.factorization 2) := by
  rw [extJacobi, if_pos h]
  congr 1
  have hN : n.natAbs ≠ 0 := Int.natAbs_ne_zero.2 h.1
  have hO : n.natAbs / 2 ^ n.natAbs.factorization 2 ≠ 0 :=
    (Nat.ordCompl_pos 2 hN).ne'
  have := Nat.multiplicative_factorization (fun m => jacobiSym ν m)
    (fun x y hxy => jacobiSym_mul_right_coprime ν x y hxy) (jacobiSym.one_right ν) hO
  rw [Nat.factorization_ordCompl] at this
  simp_rw [jacobiSym.pow_right] at this
  exact this.symm

/-- **Comparison with Mathlib, odd positive $n$:** for $n$ odd, positive and prime to $\nu$ the extended symbol is
Mathlib's Jacobi symbol `jacobiSym ν n`. -/
@[kb "conwaysloane1999" "Ch. 15, §4.3, p. 368"]
theorem extJacobi_of_odd {N : ℕ} {ν : ℤ} (hN : N % 2 = 1) (h : ExtCoprime (N : ℤ) ν) :
    extJacobi ν N = jacobiSym ν N := by
  rw [extJacobi_eq h, Int.natAbs_natCast,
    Nat.factorization_eq_zero_of_not_dvd (by omega)]
  simp

/-- **Comparison with Mathlib, $n = 2$:** $\left(\frac{\nu}{2}\right) = \chi_8(\nu)$ for odd $\nu$. -/
@[kb "conwaysloane1999" "Ch. 15, §4.3, p. 368"]
theorem extJacobi_two {ν : ℤ} (h : ExtCoprime 2 ν) :
    extJacobi ν 2 = ZMod.χ₈ (ν : ZMod 8) := by
  rw [extJacobi_eq h]
  have h1 : (2 : ℤ).natAbs = 2 := rfl
  have h2 : 2 / 2 ^ 1 = 1 := by norm_num
  rw [h1, Nat.Prime.factorization_self Nat.prime_two, h2, jacobiSym.one_right, pow_one, mul_one]

/-- The book's $\left(\frac{\nu}{2}\right)$ ($\pm1$ as $\nu \equiv \pm1, \pm3 \pmod 8$) is the library's `twoChar`
(`LocalGlobal/ConwaySloane.lean`) and Mathlib's `ZMod.χ₈` on odd residues. -/
theorem twoChar_eq_χ₈ : ∀ r : ZMod 8, OddRes r → twoChar r = ZMod.χ₈ r := by
  intro r hr
  rcases hr with rfl | rfl | rfl | rfl <;> decide

/-- Multiplicativity in $n$ ($\left(\frac{\nu}{n_1n_2}\right) = \left(\frac{\nu}{n_1}\right)\left(\frac{\nu}{n_2}\right)$
for $n_1, n_2$ prime to $\nu$; §4.3, p. 368). -/
@[kb "conwaysloane1999" "Ch. 15, §4.3, p. 368"]
theorem extJacobi_mul {n₁ n₂ ν : ℤ} (h₁ : ExtCoprime n₁ ν) (h₂ : ExtCoprime n₂ ν) :
    ExtCoprime (n₁ * n₂) ν ∧ extJacobi ν (n₁ * n₂) = extJacobi ν n₁ * extJacobi ν n₂ := by
  have hc : ExtCoprime (n₁ * n₂) ν := by
    rw [extCoprime_iff] at h₁ h₂ ⊢
    obtain ⟨a1, b1, c1, d1⟩ := h₁
    obtain ⟨a2, b2, c2, d2⟩ := h₂
    refine ⟨mul_ne_zero a1 a2, b1, ?_, ?_⟩
    · rintro ⟨h3, h4⟩
      have p1 : 0 < n₁ := lt_of_le_of_ne (not_lt.1 fun h => c1 ⟨h, h4⟩) (Ne.symm a1)
      have p2 : 0 < n₂ := lt_of_le_of_ne (not_lt.1 fun h => c2 ⟨h, h4⟩) (Ne.symm a2)
      nlinarith
    · rw [← Int.isCoprime_iff_gcd_eq_one] at d1 d2 ⊢
      exact d1.mul_left d2
  refine ⟨hc, ?_⟩
  rw [extJacobi_eq hc, extJacobi_eq h₁, extJacobi_eq h₂]
  have e1 : n₁.natAbs ≠ 0 := Int.natAbs_ne_zero.2 h₁.1
  have e2 : n₂.natAbs ≠ 0 := Int.natAbs_ne_zero.2 h₂.1
  rw [Int.natAbs_mul, Nat.factorization_mul e1 e2, Finsupp.add_apply]
  simp only [pow_add]
  have hd1 : 2 ^ n₁.natAbs.factorization 2 ∣ n₁.natAbs := Nat.ordProj_dvd _ _
  have hd2 : 2 ^ n₂.natAbs.factorization 2 ∣ n₂.natAbs := Nat.ordProj_dvd _ _
  rw [← Nat.div_mul_div_comm hd1 hd2]
  have o1 : n₁.natAbs / 2 ^ n₁.natAbs.factorization 2 ≠ 0 := (Nat.ordCompl_pos 2 e1).ne'
  have o2 : n₂.natAbs / 2 ^ n₂.natAbs.factorization 2 ≠ 0 := (Nat.ordCompl_pos 2 e2).ne'
  haveI : NeZero (n₁.natAbs / 2 ^ n₁.natAbs.factorization 2) := ⟨o1⟩
  haveI : NeZero (n₂.natAbs / 2 ^ n₂.natAbs.factorization 2) := ⟨o2⟩
  rw [jacobiSym.mul_right]
  ring

/-! ### Quadratic reciprocity for the extended symbol -/

/-- The odd part of $n$ with its sign: $n = 2^b \cdot n'$, $n'$ odd. -/
def oddPartZ (n : ℤ) : ℤ := n.sign * ((n.natAbs / 2 ^ n.natAbs.factorization 2 : ℕ) : ℤ)

theorem oddPartZ_natAbs {n : ℤ} (hn : n ≠ 0) :
    (oddPartZ n).natAbs = n.natAbs / 2 ^ n.natAbs.factorization 2 := by
  have : n.sign.natAbs = 1 := by
    rcases lt_or_gt_of_ne hn with h | h
    · simp [Int.sign_eq_neg_one_of_neg h]
    · simp [Int.sign_eq_one_of_pos h]
  simp only [oddPartZ, Int.natAbs_mul, this, one_mul, Int.natAbs_natCast]

theorem two_pow_mul_oddPartZ {n : ℤ} (hn : n ≠ 0) : (2 : ℤ) ^ n.natAbs.factorization 2 * oddPartZ n = n := by
  have h := Nat.ordProj_mul_ordCompl_eq_self n.natAbs 2
  have h' : (2 : ℤ) ^ n.natAbs.factorization 2 * ((n.natAbs / 2 ^ n.natAbs.factorization 2 : ℕ) : ℤ) =
      n.natAbs := by exact_mod_cast h
  calc (2 : ℤ) ^ n.natAbs.factorization 2 * oddPartZ n
      = n.sign * ((2 : ℤ) ^ n.natAbs.factorization 2 *
          ((n.natAbs / 2 ^ n.natAbs.factorization 2 : ℕ) : ℤ)) := by rw [oddPartZ]; ring
    _ = n := by rw [h', Int.sign_mul_natAbs]

theorem oddPartZ_odd {n : ℤ} (hn : n ≠ 0) : (oddPartZ n) % 2 = 1 := by
  have h1 := oddPartZ_natAbs hn
  have h2 : ¬ 2 ∣ n.natAbs / 2 ^ n.natAbs.factorization 2 :=
    Nat.not_dvd_ordCompl Nat.prime_two (Int.natAbs_ne_zero.2 hn)
  have : (oddPartZ n).natAbs % 2 = 1 := by rw [h1]; omega
  omega

theorem oddPartZ_neg_iff {n : ℤ} (hn : n ≠ 0) : oddPartZ n < 0 ↔ n < 0 := by
  have h := two_pow_mul_oddPartZ hn
  have hp : (0 : ℤ) < 2 ^ n.natAbs.factorization 2 := by positivity
  constructor
  · intro h1; rw [← h]; exact mul_neg_of_pos_of_neg hp h1
  · intro h1; by_contra h2; push_neg at h2; have := mul_nonneg hp.le h2; omega

theorem oddPartZ_of_odd {n : ℤ} (h : n % 2 = 1) : oddPartZ n = n := by
  have hn : n ≠ 0 := by omega
  have : n.natAbs.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by omega)
  have h2 := two_pow_mul_oddPartZ hn
  rwa [this, pow_zero, one_mul] at h2

/-- Reciprocity for Jacobi symbols of odd integers (signs allowed, not both negative). -/
theorem jacobi_recip_odd {x y : ℤ} (hx : x % 2 = 1) (hy : y % 2 = 1) (hneg : ¬ (x < 0 ∧ y < 0)) :
    jacobiSym x y.natAbs = (if x % 4 = 3 ∧ y % 4 = 3 then -1 else 1) * jacobiSym y x.natAbs := by
  obtain ⟨X, rfl | rfl⟩ : ∃ X : ℕ, x = X ∨ x = -X := ⟨x.natAbs, Int.natAbs_eq x⟩ <;>
  obtain ⟨Y, rfl | rfl⟩ : ∃ Y : ℕ, y = Y ∨ y = -Y := ⟨y.natAbs, Int.natAbs_eq y⟩
  · have hab := jacobiSym.quadratic_reciprocity_if (a := X) (b := Y) (by omega) (by omega)
    simp only [Int.natAbs_natCast]
    split_ifs at hab ⊢ <;> omega
  · have hab := jacobiSym.quadratic_reciprocity_if (a := X) (b := Y) (by omega) (by omega)
    simp only [Int.natAbs_natCast, Int.natAbs_neg, jacobiSym.neg _ (Nat.odd_iff.2 (show X % 2 = 1 by omega))]
    rcases Nat.odd_mod_four_iff.mp (show X % 2 = 1 by omega) with h1 | h1
    · rw [ZMod.χ₄_nat_one_mod_four h1]; split_ifs at hab ⊢ <;> omega
    · rw [ZMod.χ₄_nat_three_mod_four h1]; split_ifs at hab ⊢ <;> omega
  · have hab := jacobiSym.quadratic_reciprocity_if (a := X) (b := Y) (by omega) (by omega)
    simp only [Int.natAbs_natCast, Int.natAbs_neg, jacobiSym.neg _ (Nat.odd_iff.2 (show Y % 2 = 1 by omega))]
    rcases Nat.odd_mod_four_iff.mp (show Y % 2 = 1 by omega) with h1 | h1
    · rw [ZMod.χ₄_nat_one_mod_four h1]; split_ifs at hab ⊢ <;> omega
    · rw [ZMod.χ₄_nat_three_mod_four h1]; split_ifs at hab ⊢ <;> omega
  · exact absurd ⟨by omega, by omega⟩ hneg

/-- The key case of reciprocity: $\nu$ odd. -/
theorem extJacobi_reciprocity_aux {n ν : ℤ} (h : ExtCoprime n ν) (hν : ν % 2 = 1) :
    extJacobi ν n = (if ν % 4 = 3 ∧ oddPartZ n % 4 = 3 then -1 else 1) * extJacobi n ν := by
  have hn := h.1
  have h' := h.symm
  have hneg := (extCoprime_iff.1 h).2.2.1
  rw [extJacobi_eq h, extJacobi_eq h']
  have hv : ν.natAbs.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by omega)
  simp only [hv, pow_zero, one_mul, Nat.div_one]
  have e := two_pow_mul_oddPartZ hn
  have hM : ν.natAbs % 2 = 1 := by omega
  have hχ : ZMod.χ₈ ((ν.natAbs : ℕ) : ZMod 8) = ZMod.χ₈ (ν : ZMod 8) := by
    rw [ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₈_int_eq_if_mod_eight]
    split_ifs <;> omega
  have hJn : jacobiSym n ν.natAbs =
      ZMod.χ₈ (ν : ZMod 8) ^ n.natAbs.factorization 2 * jacobiSym (oddPartZ n) ν.natAbs := by
    calc jacobiSym n ν.natAbs
        = jacobiSym ((2 : ℤ) ^ n.natAbs.factorization 2 * oddPartZ n) ν.natAbs := by rw [e]
      _ = _ := by
        rw [jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym.at_two (Nat.odd_iff.2 hM)]
        rw [hχ]
  have hrec := jacobi_recip_odd (x := ν) (y := oddPartZ n) hν (oddPartZ_odd hn)
    (by rintro ⟨h1, h2⟩; exact hneg ⟨(oddPartZ_neg_iff hn).1 h2, h1⟩)
  rw [oddPartZ_natAbs hn] at hrec
  rw [hrec, hJn]
  ring

/-- **Quadratic reciprocity for the extended symbol** (Conway–Sloane, §4.3, p. 369, *corrected*): for $(n,\nu) = 1$,
$\left(\frac{\nu}{n}\right) = \left(\frac{n}{\nu}\right)$ unless the odd parts $n', \nu'$ (with sign; $n = 2^b n'$) of $n$
and $\nu$ are both $\equiv -1 \pmod 4$, when the two symbols are negatives of each other.

*Erratum:* the book states the exception as "$n$ and $\nu$ both $\equiv -1 \pmod 4$". That is the same when $n$ and
$\nu$ are odd (`extJacobi_reciprocity_printed_of_odd`), but false in general: for $\nu = 7$, $n = 6$ one has
$\left(\frac{7}{6}\right) = 1$ and $\left(\frac{6}{7}\right) = -1$ though $6 \not\equiv -1 \pmod 4$
(`not_printedReciprocity`). The statement here uses the odd parts. -/
@[kb "conwaysloane1999" "Ch. 15, §4.3, p. 369 (reciprocity law; corrected: exception on odd parts)"]
theorem extJacobi_reciprocity {n ν : ℤ} (h : ExtCoprime n ν) :
    extJacobi ν n = (if oddPartZ n % 4 = 3 ∧ oddPartZ ν % 4 = 3 then -1 else 1) * extJacobi n ν := by
  have hn := h.1
  have hν := h.2.1
  have hg := (extCoprime_iff.1 h).2.2.2
  by_cases hodd : ν % 2 = 1
  · have key := extJacobi_reciprocity_aux h hodd
    rw [oddPartZ_of_odd hodd]
    by_cases c : ν % 4 = 3 ∧ oddPartZ n % 4 = 3
    · rw [if_pos c] at key
      rw [if_pos (show oddPartZ n % 4 = 3 ∧ ν % 4 = 3 from ⟨c.2, c.1⟩), key]
    · rw [if_neg c] at key
      rw [if_neg (show ¬ (oddPartZ n % 4 = 3 ∧ ν % 4 = 3) from fun hh => c ⟨hh.2, hh.1⟩), key]
  · have hodd' : n % 2 = 1 := by
      by_contra hc
      have h2n : (2 : ℤ) ∣ n := by omega
      have h2ν : (2 : ℤ) ∣ ν := by omega
      have := Int.dvd_gcd h2n h2ν
      rw [hg] at this
      norm_num at this
    have key := extJacobi_reciprocity_aux h.symm hodd'
    rw [oddPartZ_of_odd hodd']
    by_cases c : n % 4 = 3 ∧ oddPartZ ν % 4 = 3
    · rw [if_pos c] at key
      rw [if_pos c]; linarith
    · rw [if_neg c] at key
      rw [if_neg c]; linarith

/-- **The reciprocity law exactly as printed** (§4.3, p. 369): $\left(\frac{\nu}{n}\right) = \left(\frac{n}{\nu}\right)$
unless $n \equiv \nu \equiv -1 \pmod 4$, in which case they are negatives. -/
@[kb "conwaysloane1999" "Ch. 15, §4.3, p. 369 (reciprocity law as printed)"]
def PrintedReciprocity : Prop :=
  ∀ n ν : ℤ, ExtCoprime n ν →
    extJacobi ν n = (if n % 4 = 3 ∧ ν % 4 = 3 then -1 else 1) * extJacobi n ν

/-- The printed law holds for odd $n$ and $\nu$ (a consequence of `extJacobi_reciprocity`). -/
@[kb "conwaysloane1999" "Ch. 15, §4.3, p. 369 (reciprocity law as printed, n and ν odd)"]
theorem extJacobi_reciprocity_printed_of_odd {n ν : ℤ} (h : ExtCoprime n ν) (hn : n % 2 = 1) (hν : ν % 2 = 1) :
    extJacobi ν n = (if n % 4 = 3 ∧ ν % 4 = 3 then -1 else 1) * extJacobi n ν := by
  have := extJacobi_reciprocity h
  rwa [oddPartZ_of_odd hn, oddPartZ_of_odd hν] at this

/-- **Erratum:** the reciprocity law as printed is false for even $n$ (or $\nu$): $\nu = 7$, $n = 6$ gives
$\left(\frac{7}{6}\right) = 1$, $\left(\frac{6}{7}\right) = -1$, while $6 \not\equiv -1 \pmod 4$. -/
@[kb "conwaysloane1999" "Ch. 15, §4.3, p. 369 (reciprocity law as printed: counterexample n = 6, ν = 7)"]
theorem not_printedReciprocity : ¬ PrintedReciprocity := by
  intro hP
  have hc : ExtCoprime 6 7 := extCoprime_iff.2 ⟨by norm_num, by norm_num, by norm_num, by decide⟩
  have f6 : (6 : ℕ).factorization 2 = 1 := by
    have : (6 : ℕ) = 2 ^ 1 * 3 := by norm_num
    rw [this, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 3 by norm_num)]
  have h1 : extJacobi 7 6 = 1 := by
    rw [extJacobi_eq hc]
    have : (6 : ℤ).natAbs = 6 := rfl
    rw [this, f6]
    have h3 : jacobiSym 7 (6 / 2 ^ 1) = 1 := by norm_num
    rw [h3]
    have : ZMod.χ₈ ((7 : ℤ) : ZMod 8) = 1 := by decide
    simpa using this
  have h2 : extJacobi 6 7 = -1 := by
    have := extJacobi_of_odd (N := 7) (ν := 6) (by norm_num) (by simpa using hc.symm)
    simp only [Nat.cast_ofNat] at this
    rw [this]; norm_num
  have := hP 6 7 hc
  rw [h1, h2] at this
  norm_num at this

/-! ### §4.4: Theorem 2 (diagonalization over $\mathbb Z_p$), nonsingular case -/

/-- **Theorem 2, $p \ne 2$** (Conway–Sloane, §4.4, pp. 369–370), *nonsingular forms only*: a nonsingular symmetric
form over $\mathbb Q_p$ is $\mathbb Z_p$-equivalent to a diagonal one. (Restated from Cassels' canonical form
`Cassels.exists_canonical`, whose hypothesis is an arbitrary $p$-adic unit non-square $r$; the book's statement
also covers singular integral forms, which is *not* formalized.) -/
@[kb "conwaysloane1999" "Ch. 15, §4.4, Thm. 2, pp. 369–370 (p odd, nonsingular forms)"]
theorem theorem2_odd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {r : ℚ_[p]} (hr1 : ‖r‖ = 1) (hr : ¬ IsSquare r)
    {n : ℕ} (F : Matrix (Fin n) (Fin n) ℚ_[p]) (hF : Fᵀ = F) (hdet : F.det ≠ 0) :
    ∃ d : Fin n → ℚ_[p], Cassels.ZpEquiv F (Matrix.diagonal d) := by
  obtain ⟨D, -, h, hz⟩ := Cassels.exists_canonical hp2 hr1 hr F hF hdet
  exact ⟨_, hz⟩

/-- **Theorem 2, $p = 2$** (Conway–Sloane, §4.4, pp. 369–370), *nonsingular forms only*: a nonsingular form over
$\mathbb Q_2$ is $\mathbb Z_2$-equivalent to a direct sum of the blocks $2^e u x^2$ ($u$ a unit) and $2^e\cdot 2xy$,
$2^e(2x^2 + 2xy + 2y^2)$ (`Cassels.exists_dyadic_decomp`; the book writes the blocks as $(qx)$ and
$\begin{pmatrix} qa & qb\\ qb & qc\end{pmatrix}$). The statement for singular integral forms is not formalized. -/
@[kb "conwaysloane1999" "Ch. 15, §4.4, Thm. 2, pp. 369–370 (p = 2, nonsingular forms)"]
theorem theorem2_dyadic {n : ℕ} (F : Matrix (Fin n) (Fin n) ℚ_[2]) (hF : Fᵀ = F) (hdet : F.det ≠ 0) :
    ∃ D : List Cassels.DyBlock, (∀ b ∈ D, b.Valid) ∧ ∃ h : Cassels.dyDim D = n,
      Cassels.ZpEquiv F ((Cassels.dyMat D).submatrix (Fin.cast h.symm) (Fin.cast h.symm)) :=
  Cassels.exists_dyadic_decomp F hF hdet

end PAdic
end ConwaySloane
end QuadFormsKB
