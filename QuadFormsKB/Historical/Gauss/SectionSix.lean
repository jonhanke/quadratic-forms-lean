import QuadFormsKB.Historical.Gauss.Forms
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Gauss, *Disquisitiones Arithmeticae*, Section VI (applications): the congruence $v^2 \equiv -D \pmod M$

ids: (Art. 155, 327 end) (Art. 331),
(Art. 332) (Art. 333).

Gauss's forms are $(a, b, c) = a x^2 + 2 b x y + c y^2$ (`gaussForm`) of determinant $b^2 - a c$ (`gaussDet`).
A number $r$ is a *residue* of $M$ (`IsResidueMod`) when $x^2 \equiv r \pmod M$ has an integer solution.

**Proved**, unconditionally:

* `art155_value_sq`, `art155_value_mul_left`, `art155_value_mul_right` (Art. 155): the value
  $v = \mu (m b + n c) - \nu (m a + n b)$ attached to a proper representation $M = (a, b, c)(m, n)$ with
  $\mu m + \nu n = 1$ satisfies $v^2 \equiv b^2 - ac$, $v m \equiv m b + n c$, $v n \equiv -(m a + n b) \pmod M$,
  for arbitrary integers (no definiteness, no primality);
* `art331_prime_residue` and `art331_prime_legendreSym` (Art. 331): a residue of $M$ prime to $M$ is a residue of
  every prime divisor of $M$; Gauss's example $997331 = 127 \cdot 7853$ (`art331_example_factorization`,
  `art331_example_residues`).  *Dropped:* the claim that the six residues exclude every odd prime below $998$
  except $127$ (the kernel evaluation over all primes was too heavy; the Euler-criterion lemma
  `legendreSym_eq_neg_one_of_pow` for per-prime checks is kept);
* `art332_neg_mul_modEq` etc. (Art. 332), the eight decompositions of $997331$ (`art332_decompositions`) and the
  misprint in the last line of the 1801 edition (`art332_misprint`);
* Art. 333: `art333_prime_power_solvable_iff`, `art333_prime_power_card`, `art333_prime_power_pm` (prime power
  modulus: solvable iff $-D$ is a quadratic residue of $p$, then exactly the two solutions $\pm v$, proved by Hensel
  lifting); `art333_solvable_iff`, `art333_card` (general odd modulus: solvable iff solvable modulo each prime
  power, then exactly $2^\mu$ solutions, by the Chinese remainder theorem), and `art333_gcd` (the greatest common
  divisor of $M$ and $R - R'$).

**Generality.** Positivity of $D$ is irrelevant: everything is stated for an arbitrary integer $r$ (Gauss's $-D$)
prime to $M$.  Counts are numbers of elements of `ZMod M`, i.e. of solutions modulo $M$.

**Not proved / differs from the source.** Nothing is omitted.  Gauss's $\mu$ (the number of prime factors of $M$) is
`M.primeFactors.card`.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary

/-! ### Art. 155 -/

/-- **The value $v$ of Art. 155** for a proper representation: for $(a, b, c)$, a representation
$(m, n)$ and integers $\mu, \nu$ with $\mu m + \nu n = 1$,
$$v = \mu (m b + n c) - \nu (m a + n b).$$ -/
def art155Value (a b c m n μ ν : ℤ) : ℤ := μ * (m * b + n * c) - ν * (m * a + n * b)

/-- **$v^2 \equiv b^2 - ac \pmod M$** (*Disq. Arith.* Art. 155 and the end of Art. 327):
if $M = a m^2 + 2 b m n + c n^2$ is a value of Gauss's form $(a, b, c)$ (of determinant $b^2 - ac = -D$) at a
proper representation, and $\mu m + \nu n = 1$, then $v = \mu (m b + n c) - \nu (m a + n b)$ satisfies
$v^2 \equiv b^2 - ac \pmod M$.  Proved for arbitrary integers $a, b, c, m, n, \mu, \nu$: no definiteness or
primality is needed.  (Properness of the representation, $\gcd(m, n) = 1$, is exactly the existence of $\mu, \nu$.) -/
@[kb "gauss1801" "Art. 155"]
theorem art155_value_sq (a b c m n μ ν : ℤ) (h : μ * m + ν * n = 1) :
    (art155Value a b c m n μ ν) ^ 2 ≡ gaussDet a b c [ZMOD (gaussForm a b c).eval m n] := by
  rw [eval_gaussForm, Int.modEq_iff_dvd]
  refine ⟨-(μ ^ 2 * c - 2 * μ * ν * b + ν ^ 2 * a), ?_⟩
  unfold art155Value gaussDet
  linear_combination (-(b ^ 2 - a * c) * (μ * m + ν * n + 1)) * h

/-- **$v m \equiv m b + n c \pmod M$**: the division-free form of "$v \equiv (m b + n c)/m$" (the historical sources; *Disq. Arith.* Art. 155).  Valid for arbitrary integers. -/
@[kb "gauss1801" "Art. 155"]
theorem art155_value_mul_left (a b c m n μ ν : ℤ) (h : μ * m + ν * n = 1) :
    (art155Value a b c m n μ ν) * m ≡ m * b + n * c [ZMOD (gaussForm a b c).eval m n] := by
  rw [eval_gaussForm, Int.modEq_iff_dvd]
  refine ⟨ν, ?_⟩
  unfold art155Value
  linear_combination (-(m * b + n * c)) * h

/-- **$v n \equiv -(m a + n b) \pmod M$**: the division-free form of "$v \equiv -(m a + n b)/n$" (the historical sources; *Disq. Arith.* Art. 155).  Valid for arbitrary integers. -/
@[kb "gauss1801" "Art. 155"]
theorem art155_value_mul_right (a b c m n μ ν : ℤ) (h : μ * m + ν * n = 1) :
    (art155Value a b c m n μ ν) * n ≡ -(m * a + n * b) [ZMOD (gaussForm a b c).eval m n] := by
  rw [eval_gaussForm, Int.modEq_iff_dvd]
  refine ⟨-μ, ?_⟩
  unfold art155Value
  linear_combination ((m * a + n * b)) * h

/-! ### Art. 331 -/

/-- **Residue of a modulus** (*Disq. Arith.* Art. 96 and 331): $r$ is a residue of $M$ when
$x^2 \equiv r \pmod M$ has an integer solution $x$. -/
def IsResidueMod (M r : ℤ) : Prop := ∃ x : ℤ, x ^ 2 ≡ r [ZMOD M]

private lemma not_dvd_of_isCoprime {r M : ℤ} {p : ℕ} (hp : p.Prime) (hr : IsCoprime r M)
    (hpM : (p : ℤ) ∣ M) : ¬ (p : ℤ) ∣ r := by
  intro h
  obtain ⟨u, w, huw⟩ := hr
  have h1 : (p : ℤ) ∣ 1 := huw ▸ dvd_add (dvd_mul_of_dvd_right h _) (dvd_mul_of_dvd_right hpM _)
  have h2 : p ∣ 1 := by exact_mod_cast h1
  exact hp.not_dvd_one h2

/-- **A residue of $M$ is a residue of each prime divisor** (*Disq. Arith.* Art. 331):
if $r$ is a residue of $M$ and $p \mid M$, then $r$ is a residue of $p$.  (This needs no hypothesis on $r$.) -/
@[kb "gauss1801" "Art. 331"]
theorem art331_prime_residue {M r : ℤ} (h : IsResidueMod M r) {p : ℕ} (hpM : (p : ℤ) ∣ M) :
    IsResidueMod p r := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, Int.ModEq.of_dvd hpM hx⟩

/-- **Art. 331, Legendre symbol form** (*Disq. Arith.* Art. 331): if $r$ is a residue of
$M$ and prime to $M$, then for every odd prime $p \mid M$ the Legendre symbol $\left(\frac{r}{p}\right) = 1$, i.e.
$r$ is a quadratic residue of $p$ (and in particular no prime factor of $M$ has $r$ as a non-residue). -/
@[kb "gauss1801" "Art. 331"]
theorem art331_prime_legendreSym {M r : ℤ} (h : IsResidueMod M r) (hr : IsCoprime r M) {p : ℕ}
    [hf : Fact p.Prime] (hpM : (p : ℤ) ∣ M) : legendreSym p r = 1 := by
  have hp : p.Prime := hf.out
  obtain ⟨x, hx⟩ := art331_prime_residue h hpM
  have hne : (r : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact not_dvd_of_isCoprime hp hr hpM
  rw [legendreSym.eq_one_iff p hne]
  refine ⟨x, ?_⟩
  have := (ZMod.intCast_eq_intCast_iff _ _ p).2 hx
  push_cast at this
  rw [← this]; ring

/-- **Gauss's example, factorization** (*Disq. Arith.* Art. 331): $997331 = 127 \cdot 7853$ with $127$ and
$7853$ prime. -/
@[kb "gauss1801" "Art. 331"]
theorem art331_example_factorization : Nat.Prime 127 ∧ Nat.Prime 7853 ∧ 127 * 7853 = 997331 := by
  norm_num

/-- **Gauss's six residues of $997331$** (*Disq. Arith.* Art. 331): $-6, 13, -14, 17, 37, -53$. -/
def art331Residues : List ℤ := [-6, 13, -14, 17, 37, -53]

/-- **The six numbers are residues of $997331$** (*Disq. Arith.* Art. 331), with explicit square roots
$234050^2 \equiv -6$, $102396^2 \equiv 13$, $160316^2 \equiv -14$, $35294^2 \equiv 17$, $2996^2 \equiv 37$,
$116643^2 \equiv -53 \pmod{997331}$. -/
@[kb "gauss1801" "Art. 331"]
theorem art331_example_residues : ∀ r ∈ art331Residues, IsResidueMod 997331 r := by
  intro r hr
  simp only [art331Residues, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨234050, by decide +kernel⟩
  · exact ⟨102396, by decide +kernel⟩
  · exact ⟨160316, by decide +kernel⟩
  · exact ⟨35294, by decide +kernel⟩
  · exact ⟨2996, by decide +kernel⟩
  · exact ⟨116643, by decide +kernel⟩

/-- Euler's criterion, in a form the kernel can evaluate: if $p \nmid r$ and
$(r \bmod p)^{\lfloor p/2 \rfloor} \equiv p - 1$ then $\left(\frac{r}{p}\right) = -1$. -/
theorem legendreSym_eq_neg_one_of_pow {p : ℕ} [hf : Fact p.Prime] (hp2 : p ≠ 2) {r : ℤ}
    (hr : ¬ (p : ℤ) ∣ r) (h : ((r % p).toNat ^ (p / 2)) % p = p - 1) : legendreSym p r = -1 := by
  have hp : p.Prime := hf.out
  haveI : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
  have ha0 : (r : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hr
  have hpow := legendreSym.eq_pow p r
  have hcast : (r : ZMod p) = (((r % p).toNat : ℕ) : ZMod p) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.ne_zero)),
      ZMod.intCast_mod]
  have hm1 : (r : ZMod p) ^ (p / 2) = -1 := by
    rw [hcast, ← Nat.cast_pow, ← ZMod.natCast_mod, h, Nat.cast_sub hp.one_le, ZMod.natCast_self]
    simp
  rcases legendreSym.eq_one_or_neg_one p ha0 with h1 | h1
  · rw [h1, hm1] at hpow
    exact absurd (by simpa using hpow) (ZMod.neg_one_ne_one).symm
  · exact h1

/-! ### Art. 332 -/

/-- **$-ab \equiv a^2 \equiv b^2 \pmod M$ when $a + b = kM$** (*Disq. Arith.* Art. 332):
the first congruence. -/
@[kb "gauss1801" "Art. 332"]
theorem art332_neg_mul_modEq (M k a b : ℤ) (h : k * M = a + b) : -(a * b) ≡ a ^ 2 [ZMOD M] := by
  rw [Int.modEq_iff_dvd]
  exact ⟨a * k, by linear_combination (-a) * h⟩

/-- **$a^2 \equiv b^2 \pmod M$ when $a + b = kM$** (*Disq. Arith.* Art. 332). -/
@[kb "gauss1801" "Art. 332"]
theorem art332_sq_modEq (M k a b : ℤ) (h : k * M = a + b) : a ^ 2 ≡ b ^ 2 [ZMOD M] := by
  rw [Int.modEq_iff_dvd]
  exact ⟨(b - a) * k, by linear_combination (-(b - a)) * h⟩

/-- **$a k^2$ a residue and $k$ prime to $M$ imply $a$ a residue** (the historical sources;
*Disq. Arith.* Art. 332). -/
@[kb "gauss1801" "Art. 332"]
theorem art332_residue_of_mul_sq {M a k : ℤ} (hk : IsCoprime k M) (h : IsResidueMod M (a * k ^ 2)) :
    IsResidueMod M a := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨u, w, huw⟩ := hk
  have hku : k * u ≡ 1 [ZMOD M] := by
    rw [Int.modEq_iff_dvd]; exact ⟨w, by linear_combination -huw⟩
  refine ⟨x * u, ?_⟩
  calc (x * u) ^ 2 = x ^ 2 * u ^ 2 := by ring
    _ ≡ a * k ^ 2 * u ^ 2 [ZMOD M] := hx.mul_right _
    _ = a * (k * u) ^ 2 := by ring
    _ ≡ a * 1 ^ 2 [ZMOD M] := (hku.pow 2).mul_left _
    _ = a := by ring

/-- **The product of two residues is a residue** (*Disq. Arith.* Art. 332). -/
@[kb "gauss1801" "Art. 332"]
theorem art332_residue_mul {M r s : ℤ} (hr : IsResidueMod M r) (hs : IsResidueMod M s) :
    IsResidueMod M (r * s) := by
  obtain ⟨x, hx⟩ := hr
  obtain ⟨y, hy⟩ := hs
  exact ⟨x * y, by rw [mul_pow]; exact hx.mul hy⟩

/-- **Gauss's eight decompositions of $997331$** (*Disq. Arith.* Art. 332), each of the
form $a k^2 \pm (\text{product})$ giving $997331$.  The last line is as printed in Werke I
($11 \cdot 301^2 + 5 \cdot 12^2$). -/
@[kb "gauss1801" "Art. 332"]
theorem art332_decompositions :
    999 ^ 2 - 2 * 5 * 67 = 997331 ∧ 994 ^ 2 + 5 * 11 * 13 ^ 2 = 997331 ∧
    2 * 706 ^ 2 + 3 * 17 * 3 ^ 2 = 997331 ∧ 3 * 575 ^ 2 + 11 * 31 * 4 ^ 2 = 997331 ∧
    3 * 577 ^ 2 - 7 * 13 * 4 ^ 2 = 997331 ∧ 3 * 578 ^ 2 - 7 * 19 * 37 = 997331 ∧
    11 * 299 ^ 2 + 2 * 3 * 5 * 29 * 4 ^ 2 = 997331 ∧ 11 * 301 ^ 2 + 5 * 12 ^ 2 = 997331 := by
  norm_num

/-- **Erratum (misprint in the 1801 edition of Art. 332)** : the last decomposition is printed there as
$11 \cdot 301^2 + 5 \cdot 11^2$, which is not $997331$; the correct term is $5 \cdot 12^2$ (as in Werke I). -/
@[kb "gauss1801" "Art. 332"]
theorem art332_misprint : 11 * 301 ^ 2 + 5 * 11 ^ 2 ≠ 997331 := by norm_num

/-! ### Art. 333 -/

section Art333

open Finset
open scoped Classical

private lemma isUnit_intCast_of_isCoprime {r : ℤ} {n : ℕ} (h : IsCoprime r (n : ℤ)) :
    IsUnit (r : ZMod n) := by
  obtain ⟨u, w, huw⟩ := h
  have := congrArg (Int.cast : ℤ → ZMod n) huw
  push_cast [ZMod.natCast_self] at this
  exact IsUnit.of_mul_eq_one (u : ZMod n) (by rw [mul_comm]; simpa using this)

private lemma isCoprime_pow_of_not_dvd {p : ℕ} (hp : p.Prime) {r : ℤ} (hr : ¬ (p : ℤ) ∣ r) (e : ℕ) :
    IsCoprime r ((p ^ e : ℕ) : ℤ) := by
  have h := ((Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd).2 hr
  push_cast
  exact h.symm.pow_right

private lemma two_ne_zero_zmod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)

private lemma isUnit_of_castHom_ne_zero {p e : ℕ} [Fact p.Prime] (he : 0 < e) {y : ZMod (p ^ e)}
    (hy : ZMod.castHom (dvd_pow_self p he.ne') (ZMod p) y ≠ 0) : IsUnit y := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, y = n := ⟨y.val, (ZMod.natCast_zmod_val y).symm⟩
  rw [map_natCast] at hy
  rw [ZMod.isUnit_iff_coprime]
  have : ¬ p ∣ n := fun h => hy ((ZMod.natCast_eq_zero_iff _ _).2 h)
  exact (((Nat.Prime.coprime_iff_not_dvd Fact.out).2 this).pow_left e).symm

/-- In $\mathbb{Z}/p^e$ ($p$ odd), $x^2 = v^2$ with $v$ prime to $p$ forces $x = \pm v$. -/
private lemma eq_or_eq_neg_of_sq_eq_sq {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 0 < e)
    {x v : ZMod (p ^ e)} (hv : ZMod.castHom (dvd_pow_self p he.ne') (ZMod p) v ≠ 0)
    (h : x ^ 2 = v ^ 2) : x = v ∨ x = -v := by
  set π := ZMod.castHom (dvd_pow_self p he.ne') (ZMod p) with hπ
  have hprod : (x - v) * (x + v) = 0 := by linear_combination h
  by_cases h1 : π (x - v) = 0
  · left
    have h3 : π (x + v) ≠ 0 := by
      have : π (x + v) = π (x - v) + 2 * π v := by simp only [map_add, map_sub]; ring
      rw [this, h1, zero_add]; exact mul_ne_zero (two_ne_zero_zmod hp2) hv
    have h4 : x - v = 0 := ((isUnit_of_castHom_ne_zero he h3).mul_left_eq_zero).1 hprod
    exact sub_eq_zero.1 h4
  · right
    have h4 : x + v = 0 := ((isUnit_of_castHom_ne_zero he h1).mul_right_eq_zero).1 hprod
    exact eq_neg_of_add_eq_zero_left h4

private lemma hensel_step {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {r v : ℤ} (e : ℕ)
    (hr : ¬ (p : ℤ) ∣ r) (hv : (p : ℤ) ^ (e + 1) ∣ v ^ 2 - r) :
    ∃ v' : ℤ, (p : ℤ) ^ (e + 2) ∣ v' ^ 2 - r := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨s, hs⟩ := hv
  have hpv : ¬ (p : ℤ) ∣ 2 * v := by
    intro h
    rcases hpZ.dvd_or_dvd h with h2 | h2
    · have : p ∣ 2 := by exact_mod_cast h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
    · apply hr
      have h3 : (p : ℤ) ∣ v ^ 2 - r := by
        rw [hs]; exact dvd_mul_of_dvd_left (dvd_pow_self _ (Nat.succ_ne_zero e)) _
      have h4 : (p : ℤ) ∣ v ^ 2 := dvd_pow h2 two_ne_zero
      simpa using (dvd_sub h4 h3)
  obtain ⟨z, w, hzw⟩ : IsCoprime (p : ℤ) (2 * v) := hpZ.irreducible.coprime_iff_not_dvd.2 hpv
  refine ⟨v + (-s * w) * (p : ℤ) ^ (e + 1), ⟨s * z + (s * w) ^ 2 * (p : ℤ) ^ e, ?_⟩⟩
  linear_combination hs - ((p : ℤ) ^ (e + 1) * s) * hzw

private lemma hensel_lift {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {r : ℤ} (hr : ¬ (p : ℤ) ∣ r) (x : ℤ)
    (hx : (p : ℤ) ∣ x ^ 2 - r) : ∀ e : ℕ, ∃ v : ℤ, (p : ℤ) ^ (e + 1) ∣ v ^ 2 - r
  | 0 => ⟨x, by simpa using hx⟩
  | e + 1 => by
    obtain ⟨v, hv⟩ := hensel_lift hp hp2 hr x hx e
    exact hensel_step hp hp2 e hr hv

private lemma exists_sqrt_iff {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 0 < e) {r : ℤ}
    (hr : ¬ (p : ℤ) ∣ r) :
    (∃ x : ZMod (p ^ e), x ^ 2 = (r : ZMod (p ^ e))) ↔ IsSquare (r : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨ZMod.castHom (dvd_pow_self p he.ne') (ZMod p) x, ?_⟩
    have := congrArg (ZMod.castHom (dvd_pow_self p he.ne') (ZMod p)) hx
    rw [map_pow, map_intCast] at this
    rw [← this]; ring
  · rintro ⟨y, hy⟩
    obtain ⟨Y, rfl⟩ := ZMod.intCast_surjective y
    have hY : (p : ℤ) ∣ Y ^ 2 - r := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hy]; ring
    obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
    obtain ⟨v, hv⟩ := hensel_lift hp hp2 hr Y hY e'
    refine ⟨(v : ZMod (p ^ (e' + 1))), ?_⟩
    have : (v : ZMod (p ^ (e' + 1))) ^ 2 - r = 0 := by
      rw [← Int.cast_pow, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast hv
    exact sub_eq_zero.1 this

private lemma card_sqrt {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 0 < e) {r : ℤ}
    (hr : ¬ (p : ℤ) ∣ r) :
    Nat.card {x : ZMod (p ^ e) // x ^ 2 = (r : ZMod (p ^ e))} =
      if IsSquare (r : ZMod p) then 2 else 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hne : (r : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hr
  split_ifs with hl
  · obtain ⟨v, hv⟩ := (exists_sqrt_iff hp hp2 he hr).2 hl
    have hπv : ZMod.castHom (dvd_pow_self p he.ne') (ZMod p) v ≠ 0 := by
      intro h0
      have := congrArg (ZMod.castHom (dvd_pow_self p he.ne') (ZMod p)) hv
      rw [map_pow, map_intCast, h0] at this
      exact hne (by simpa using this.symm)
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨v, hv⟩, ⟨-v, by rw [neg_sq]; exact hv⟩, ?_, ?_⟩
    · intro h
      have h' : v = -v := congrArg Subtype.val h
      have h2 : v + v = 0 := by nth_rewrite 2 [h']; ring
      have := congrArg (ZMod.castHom (dvd_pow_self p he.ne') (ZMod p)) h2
      rw [map_add, map_zero, ← two_mul] at this
      exact mul_ne_zero (two_ne_zero_zmod hp2) hπv this
    · ext ⟨z, hz⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true, Subtype.mk.injEq]
      exact eq_or_eq_neg_of_sq_eq_sq hp2 he hπv (hz.trans hv.symm)
  · rw [Nat.card_eq_zero]
    left
    refine ⟨fun ⟨x, hx⟩ => hl ?_⟩
    exact (exists_sqrt_iff hp hp2 he hr).1 ⟨x, hx⟩

/-- **Art. 333 (i), solvability** (*Disq. Arith.* Art. 333): for an odd prime $p$,
$e \ge 1$ and $r$ prime to $p$ (Gauss's $r = -D$, $D$ prime to $M = p^e$), the congruence $v^2 \equiv r \pmod{p^e}$
is solvable iff $r$ is a quadratic residue of $p$ (`IsSquare (r : ZMod p)`, equivalently
$\left(\frac{r}{p}\right) = 1$, see `art333_prime_power_legendreSym`).  Proved by Hensel lifting.
Valid for every integer $r$ prime to $p$ (positivity of $D$ is irrelevant). -/
@[kb "gauss1801" "Art. 333"]
theorem art333_prime_power_solvable_iff {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 0 < e) {r : ℤ}
    (hr : ¬ (p : ℤ) ∣ r) : (∃ v : ℤ, v ^ 2 ≡ r [ZMOD ((p ^ e : ℕ) : ℤ)]) ↔ IsSquare (r : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← exists_sqrt_iff hp hp2 he hr]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, by have := (ZMod.intCast_eq_intCast_iff _ _ _).2 hv; push_cast at this; exact this⟩
  · rintro ⟨x, hx⟩
    obtain ⟨v, rfl⟩ := ZMod.intCast_surjective x
    exact ⟨v, (ZMod.intCast_eq_intCast_iff _ _ _).1 (by push_cast; exact hx)⟩

/-- **Art. 333 (i), the number of solutions** (*Disq. Arith.* Art. 333): for an odd prime
$p$, $e \ge 1$ and $r$ prime to $p$, the congruence $v^2 \equiv r \pmod{p^e}$ has exactly $2$ solutions in
`ZMod (p ^ e)` when $r$ is a quadratic residue of $p$ and none otherwise. -/
@[kb "gauss1801" "Art. 333"]
theorem art333_prime_power_card {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 0 < e) {r : ℤ}
    (hr : ¬ (p : ℤ) ∣ r) :
    Nat.card {x : ZMod (p ^ e) // x ^ 2 = (r : ZMod (p ^ e))} =
      if IsSquare (r : ZMod p) then 2 else 0 :=
  card_sqrt hp hp2 he hr

/-- **Art. 333 (i), Legendre symbol form**: for $p$ prime and $r$ prime to $p$,
$r$ is a quadratic residue of $p$ (`IsSquare (r : ZMod p)`) iff $\left(\frac{r}{p}\right) = 1$. -/
theorem art333_prime_power_legendreSym {p : ℕ} [Fact p.Prime] {r : ℤ} (hr : ¬ (p : ℤ) ∣ r) :
    legendreSym p r = 1 ↔ IsSquare (r : ZMod p) := by
  have hne : (r : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hr
  exact legendreSym.eq_one_iff p hne

/-- **Art. 333 (i), the two solutions are $\pm v$** (*Disq. Arith.* Art. 333): if
$v^2 = r$ in `ZMod (p ^ e)` with $r$ prime to the odd prime $p$, then the solutions of $x^2 = r$ are exactly
$x = v$ and $x = -v$, and $v \ne -v$. -/
@[kb "gauss1801" "Art. 333"]
theorem art333_prime_power_pm {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 0 < e) {r : ℤ}
    (hr : ¬ (p : ℤ) ∣ r) {v : ZMod (p ^ e)} (hv : v ^ 2 = (r : ZMod (p ^ e))) :
    (∀ x : ZMod (p ^ e), x ^ 2 = (r : ZMod (p ^ e)) ↔ x = v ∨ x = -v) ∧ v ≠ -v := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hne : (r : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hr
  have hπv : ZMod.castHom (dvd_pow_self p he.ne') (ZMod p) v ≠ 0 := by
    intro h0
    have := congrArg (ZMod.castHom (dvd_pow_self p he.ne') (ZMod p)) hv
    rw [map_pow, map_intCast, h0] at this
    exact hne (by simpa using this.symm)
  refine ⟨fun x => ⟨fun hx => eq_or_eq_neg_of_sq_eq_sq hp2 he hπv (hx.trans hv.symm), ?_⟩, ?_⟩
  · rintro (rfl | rfl)
    · exact hv
    · rw [neg_sq]; exact hv
  · intro h'
    have h2 : v + v = 0 := by nth_rewrite 2 [h']; ring
    have := congrArg (ZMod.castHom (dvd_pow_self p he.ne') (ZMod p)) h2
    rw [map_add, map_zero, ← two_mul] at this
    exact mul_ne_zero (two_ne_zero_zmod hp2) hπv this

/-- **The set of square roots modulo $M$** of $r$ in `ZMod M`: $\{v \in \mathbb{Z}/M : v^2 = r\}$ (Gauss's
solutions of $v^2 \equiv r \pmod M$, counted modulo $M$). -/
def sqrtSet (M : ℕ) [NeZero M] (r : ZMod M) : Finset (ZMod M) := univ.filter fun v => v ^ 2 = r

theorem card_sqrtSet (M : ℕ) [NeZero M] (r : ZMod M) :
    (sqrtSet M r).card = Nat.card {v : ZMod M // v ^ 2 = r} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; rfl

private lemma prod_pf {M : ℕ} (hM : M ≠ 0) :
    ∏ p ∈ M.primeFactors, p ^ M.factorization p = M := by
  exact (Nat.prod_primeFactors_pow_factorization hM).symm

private lemma prod_pow_factorization {M : ℕ} (hM : M ≠ 0) :
    ∏ i : M.primeFactors, (i : ℕ) ^ M.factorization i = M := by
  rw [Finset.prod_coe_sort M.primeFactors (fun p => p ^ M.factorization p)]
  exact prod_pf hM

private lemma pf_facts {M : ℕ} (hM : Odd M) {p : ℕ} (hp : p ∈ M.primeFactors) :
    p.Prime ∧ p ≠ 2 ∧ 0 < M.factorization p ∧ (p : ℤ) ∣ (M : ℤ) := by
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hd := Nat.dvd_of_mem_primeFactors hp
  refine ⟨hpr, ?_, hpr.factorization_pos_of_dvd hM.pos.ne' hd, by exact_mod_cast hd⟩
  rintro rfl
  exact (Nat.not_even_iff_odd.2 hM) (even_iff_two_dvd.2 hd)

private lemma solvable_zmod_iff (n : ℕ) (r : ℤ) :
    (∃ v : ℤ, v ^ 2 ≡ r [ZMOD (n : ℤ)]) ↔ ∃ x : ZMod n, x ^ 2 = (r : ZMod n) := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, by have := (ZMod.intCast_eq_intCast_iff _ _ _).2 hv; push_cast at this; exact this⟩
  · rintro ⟨x, hx⟩
    obtain ⟨v, rfl⟩ := ZMod.intCast_surjective x
    exact ⟨v, (ZMod.intCast_eq_intCast_iff _ _ _).1 (by push_cast; exact hx)⟩

/-- **Art. 333 (ii), the number of solutions** (*Disq. Arith.* Art. 333): for an odd
modulus $M = \prod p_i^{e_i}$ with $\mu$ distinct prime factors (`M.primeFactors.card`) and an integer $r$ (Gauss's
$-D$) prime to $M$, the congruence $v^2 \equiv r \pmod M$ has exactly $2^\mu$ solutions in `ZMod M` if
$r$ is a quadratic residue of every $p_i$ (`IsSquare (r : ZMod p)`), and none otherwise.  Proved with the Chinese
remainder theorem (`ZMod.prodEquivPi`) and the prime power case.  Valid for every integer $r$ prime to $M$. -/
@[kb "gauss1801" "Art. 333"]
theorem art333_card {M : ℕ} (hM : Odd M) {r : ℤ} (hr : IsCoprime r (M : ℤ)) :
    Nat.card {v : ZMod M // v ^ 2 = (r : ZMod M)} =
      if ∀ p ∈ M.primeFactors, IsSquare (r : ZMod p) then 2 ^ M.primeFactors.card else 0 := by
  have hM0 : M ≠ 0 := hM.pos.ne'
  set S := M.primeFactors with hS
  let a : S → ℕ := fun i => (i : ℕ) ^ M.factorization i
  have hprod : ∏ i, a i = M := prod_pow_factorization hM0
  have hcop : Pairwise (Function.onFun Nat.Coprime a) := by
    intro i j hij
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors i.2)
      (Nat.prime_of_mem_primeFactors j.2)).2 (fun h => hij (Subtype.ext h)))
  let φ : ZMod M ≃+* ∀ i, ZMod (a i) := (ZMod.ringEquivCongr hprod.symm).trans (ZMod.prodEquivPi a hcop)
  have hφr : φ (r : ZMod M) = fun i => (r : ZMod (a i)) := by
    rw [map_intCast φ r]; funext i; simp
  have e1 : {v : ZMod M // v ^ 2 = (r : ZMod M)} ≃ {w : ∀ i, ZMod (a i) // w ^ 2 = fun i => (r : ZMod (a i))} :=
    Equiv.subtypeEquiv φ.toEquiv (fun v => by
      rw [← hφr]
      simp only [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
      rw [← map_pow]; exact (φ.injective.eq_iff).symm)
  have e2 : {w : ∀ i, ZMod (a i) // w ^ 2 = fun i => (r : ZMod (a i))} ≃
      ∀ i, {x : ZMod (a i) // x ^ 2 = (r : ZMod (a i))} :=
    (Equiv.subtypeEquivRight (fun w => by simp only [funext_iff]; rfl)).trans Equiv.subtypePiEquivPi
  rw [Nat.card_congr (e1.trans e2), Nat.card_pi]
  have hi : ∀ i : S, Nat.card {x : ZMod (a i) // x ^ 2 = (r : ZMod (a i))} =
      if IsSquare (r : ZMod (i : ℕ)) then 2 else 0 := by
    intro i
    obtain ⟨hpr, hp2', hpos, hdvd⟩ := pf_facts hM i.2
    exact card_sqrt hpr hp2' hpos (not_dvd_of_isCoprime hpr hr hdvd)
  rw [Finset.prod_congr rfl (fun i _ => hi i)]
  by_cases hall : ∀ p ∈ S, IsSquare (r : ZMod p)
  · rw [if_pos hall, Finset.prod_congr rfl (fun (i : S) _ => if_pos (hall (i : ℕ) i.2))]
    simp
  · rw [if_neg hall]
    push_neg at hall
    obtain ⟨p, hp, hne⟩ := hall
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨p, hp⟩ : S)) (if_neg hne)

/-- **Art. 333 (ii), the number of solutions, as a finite set**: the same count with
`Finset.card` of `sqrtSet M r` $= \{v \in \mathbb{Z}/M : v^2 = r\}$. -/
@[kb "gauss1801" "Art. 333"]
theorem art333_card_sqrtSet {M : ℕ} (hM : Odd M) {r : ℤ} (hr : IsCoprime r (M : ℤ)) :
    haveI : NeZero M := ⟨hM.pos.ne'⟩
    (sqrtSet M (r : ZMod M)).card =
      if ∀ p ∈ M.primeFactors, IsSquare (r : ZMod p) then 2 ^ M.primeFactors.card else 0 := by
  haveI : NeZero M := ⟨hM.pos.ne'⟩
  rw [card_sqrtSet]; exact art333_card hM hr

/-- **Art. 333 (ii), solvability** (*Disq. Arith.* Art. 333): for odd $M$ and $r$ prime
to $M$, $v^2 \equiv r \pmod M$ is solvable iff $v^2 \equiv r \pmod{p^{e}}$ is solvable for every prime power
$p^{e} \,\|\, M$ (`e = M.factorization p`).  Valid for every integer $r$ prime to $M$. -/
@[kb "gauss1801" "Art. 333"]
theorem art333_solvable_iff {M : ℕ} (hM : Odd M) {r : ℤ} (hr : IsCoprime r (M : ℤ)) :
    (∃ v : ℤ, v ^ 2 ≡ r [ZMOD (M : ℤ)]) ↔
      ∀ p ∈ M.primeFactors, ∃ v : ℤ, v ^ 2 ≡ r [ZMOD ((p ^ M.factorization p : ℕ) : ℤ)] := by
  haveI : NeZero M := ⟨hM.pos.ne'⟩
  have key : (∀ p ∈ M.primeFactors, IsSquare (r : ZMod p)) ↔
      ∀ p ∈ M.primeFactors, ∃ v : ℤ, v ^ 2 ≡ r [ZMOD ((p ^ M.factorization p : ℕ) : ℤ)] := by
    refine forall₂_congr fun p hp => ?_
    obtain ⟨hpr, hp2', hpos, hdvd⟩ := pf_facts hM hp
    exact (art333_prime_power_solvable_iff hpr hp2' hpos (not_dvd_of_isCoprime hpr hr hdvd)).symm
  rw [← key, solvable_zmod_iff]
  have h1 : (∃ x : ZMod M, x ^ 2 = (r : ZMod M)) ↔ 0 < Nat.card {v : ZMod M // v ^ 2 = (r : ZMod M)} := by
    rw [Nat.card_pos_iff]
    constructor
    · rintro ⟨x, hx⟩; exact ⟨⟨⟨x, hx⟩⟩, inferInstance⟩
    · rintro ⟨⟨⟨x, hx⟩⟩, _⟩; exact ⟨x, hx⟩
  rw [h1, art333_card hM hr]
  constructor
  · intro hpos
    by_contra h
    rw [if_neg h] at hpos
    exact lt_irrefl _ hpos
  · intro h
    rw [if_pos h]; positivity

/-- **Local dichotomy** for two solutions $R, R'$ of $v^2 \equiv r \pmod{p^e}$ ($p$ odd, $p \nmid r$):
$R \equiv R'$ or $R \equiv -R' \pmod{p^e}$. -/
private lemma dichotomy {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 0 < e) {r R R' : ℤ}
    (hr : ¬ (p : ℤ) ∣ r) (h1 : R ^ 2 ≡ r [ZMOD ((p ^ e : ℕ) : ℤ)])
    (h2 : R' ^ 2 ≡ r [ZMOD ((p ^ e : ℕ) : ℤ)]) :
    R ≡ R' [ZMOD ((p ^ e : ℕ) : ℤ)] ∨ R ≡ -R' [ZMOD ((p ^ e : ℕ) : ℤ)] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hne : (r : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hr
  have a := (ZMod.intCast_eq_intCast_iff _ _ _).2 h1
  have b := (ZMod.intCast_eq_intCast_iff _ _ _).2 h2
  push_cast at a b
  have hx : (R' : ZMod (p ^ e)) ^ 2 = (R : ZMod (p ^ e)) ^ 2 := b.trans a.symm
  have hπR : ZMod.castHom (dvd_pow_self p he.ne') (ZMod p) (R : ZMod (p ^ e)) ≠ 0 := by
    intro h0
    have := congrArg (ZMod.castHom (dvd_pow_self p he.ne') (ZMod p)) a
    rw [map_pow, h0, map_intCast] at this
    exact hne (by simpa using this.symm)
  rcases eq_or_eq_neg_of_sq_eq_sq hp2 he hπR hx with h | h
  · left
    exact (ZMod.intCast_eq_intCast_iff _ _ _).1 h.symm
  · right
    refine (ZMod.intCast_eq_intCast_iff _ _ _).1 ?_
    push_cast
    rw [h]; ring

open scoped Classical in
/-- **Art. 333 (ii), the greatest common divisor of $M$ and $R - R'$** (the historical sources;
*Disq. Arith.* Art. 333): for odd $M = \prod p_i^{e_i}$, $r$ prime to $M$ and two integers $R, R'$ with
$R^2 \equiv R'^2 \equiv r \pmod M$, $\gcd(M, R - R')$ is the product of those $p_i^{e_i}$ for which
$R \equiv R' \pmod{p_i^{e_i}}$. -/
@[kb "gauss1801" "Art. 333"]
theorem art333_gcd {M : ℕ} (hM : Odd M) {r : ℤ} (hr : IsCoprime r (M : ℤ)) {R R' : ℤ}
    (hR : R ^ 2 ≡ r [ZMOD (M : ℤ)]) (hR' : R' ^ 2 ≡ r [ZMOD (M : ℤ)]) :
    Int.gcd (M : ℤ) (R - R') =
      ∏ p ∈ M.primeFactors.filter (fun p => R ≡ R' [ZMOD ((p ^ M.factorization p : ℕ) : ℤ)]),
        p ^ M.factorization p := by
  have hM0 : M ≠ 0 := hM.pos.ne'
  set P : ℕ → Prop := fun p => R ≡ R' [ZMOD ((p ^ M.factorization p : ℕ) : ℤ)] with hP
  set N : ℕ := ∏ p ∈ M.primeFactors.filter P, p ^ M.factorization p with hN
  set N' : ℕ := ∏ p ∈ M.primeFactors.filter (fun p => ¬ P p), p ^ M.factorization p with hN'
  have hsplit : N * N' = M := by
    rw [hN, hN', Finset.prod_filter_mul_prod_filter_not]; exact prod_pf hM0
  have hdich : ∀ p ∈ M.primeFactors, P p ∨
      R ≡ -R' [ZMOD ((p ^ M.factorization p : ℕ) : ℤ)] := by
    intro p hp
    obtain ⟨hpr, hp2', hpos, hdvd⟩ := pf_facts hM hp
    have hpe : ((p ^ M.factorization p : ℕ) : ℤ) ∣ (M : ℤ) := by
      exact_mod_cast Nat.ordProj_dvd M p
    exact dichotomy hpr hp2' hpos (not_dvd_of_isCoprime hpr hr hdvd) (Int.ModEq.of_dvd hpe hR)
      (Int.ModEq.of_dvd hpe hR')
  have hdvdR : ∀ p ∈ M.primeFactors.filter P, ((p ^ M.factorization p : ℕ) : ℤ) ∣ R - R' := by
    intro p hp
    have := (Int.modEq_iff_dvd.1 (Finset.mem_filter.1 hp).2)
    exact (dvd_sub_comm).1 this
  apply Nat.dvd_antisymm
  · -- the gcd divides N
    have hcopN' : IsCoprime (R - R') (N' : ℤ) := by
      rw [hN']
      push_cast
      refine IsCoprime.prod_right fun p hp => ?_
      obtain ⟨hpm, hnP⟩ := Finset.mem_filter.1 hp
      obtain ⟨hpr, hp2', hpos, hdvd⟩ := pf_facts hM hpm
      refine isCoprime_pow_of_not_dvd hpr ?_ _ |>.symm.symm
      intro hpd
      have hneg := (hdich p hpm).resolve_left hnP
      have h1 : (p : ℤ) ∣ -R' - R := (Dvd.dvd.trans (by exact_mod_cast dvd_pow_self p hpos.ne')
        (Int.modEq_iff_dvd.1 hneg))
      have h2 : (p : ℤ) ∣ 2 * R := by
        have h1' : (p : ℤ) ∣ R + R' := by
          have := (dvd_neg).2 h1
          rwa [show -(-R' - R) = R + R' by ring] at this
        have := dvd_add hpd h1'
        rwa [show R - R' + (R + R') = 2 * R by ring] at this
      have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpr
      have h3 : (p : ℤ) ∣ R := by
        rcases hpZ.dvd_or_dvd h2 with h4 | h4
        · have : p ∣ 2 := by exact_mod_cast h4
          exact absurd ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).1 this) hp2'
        · exact h4
      have h5 : (p : ℤ) ∣ r - R ^ 2 := dvd_trans hdvd (Int.modEq_iff_dvd.1 hR)
      exact not_dvd_of_isCoprime hpr hr hdvd (by simpa using dvd_add h5 (dvd_pow h3 two_ne_zero))
    have hg : Nat.Coprime (Int.gcd (M : ℤ) (R - R')) N' := by
      rw [← Nat.isCoprime_iff_coprime]
      exact hcopN'.of_isCoprime_of_dvd_left (Int.gcd_dvd_right (M : ℤ) (R - R'))
    have hgM : Int.gcd (M : ℤ) (R - R') ∣ N * N' := by
      rw [hsplit]; exact Int.natCast_dvd_natCast.1 (Int.gcd_dvd_left (M : ℤ) (R - R'))
    exact hg.dvd_of_dvd_mul_right hgM
  · -- N divides the gcd
    have hNM : (N : ℤ) ∣ (M : ℤ) := by rw [← hsplit]; push_cast; exact dvd_mul_right _ _
    have hNd : (N : ℤ) ∣ R - R' := by
      rw [hN]; push_cast
      refine Finset.prod_dvd_of_coprime ?_ hdvdR
      intro p hp q hq hpq
      have hpq' := Finset.mem_filter.1 hp
      have hqq' := Finset.mem_filter.1 hq
      exact Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow _ _
        ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hpq'.1)
          (Nat.prime_of_mem_primeFactors hqq'.1)).2 hpq))
    exact Int.natCast_dvd_natCast.1 (Int.dvd_coe_gcd hNM hNd)

end Art333

end QuadFormsKB.Historical.Gauss
