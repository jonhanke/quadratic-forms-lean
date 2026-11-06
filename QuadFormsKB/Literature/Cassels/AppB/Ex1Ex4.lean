/-
# Cassels, Appendix B, Examples 1 and 4

Cassels, *Rational Quadratic Forms* (1978), Appendix B (*Analytic methods*), Examples, p. 389.

**Source statements (paraphrased).** *Example 1.* In the notation of Theorem 2.1, for a fundamental discriminant $D < 0$,
$2\,(2 - (D/2))\,h(D) = w\sum_{r=1}^{[|D|/2]}(D/r)$, where $h(D)$ is the number of classes of primitive forms and $w = 6, 4, 2$
for $D = -3, -4$, otherwise (Theorem 2.1 (i) is $2|D|h(D) = w\sum_{0<r<|D|}(D/r)\,r$ up to the sign discussed in
`finite_sum_class_number_neg`). *Example 4.* For a fundamental discriminant $D$ the Gauss sum
$\sum_{r \bmod |D|}(D/r)\,e(r/|D|)$, $e(x) = e^{2\pi i x}$, is $\pm\sqrt D$ if $D > 0$ and $\pm i\sqrt{|D|}$ if $D < 0$ (this is
(2.20) of the text except for the sign).

**Conventions.** $D$ is a fundamental discriminant, `IsQuadDisc D` (so $D \ne 1$); $|D|$ is `D.natAbs`; $(D/r)$ is the
Kronecker character `kroneckerChar D` (complex valued, a Dirichlet character modulo $|D|$) or its integer values
`kronZ D`; the residue of a natural number $r$ is its image in `ZMod |D|`. $h(D)$ is `NumberField.classNumber (QField D)`
(equal to the number of proper classes of primitive positive definite forms, `Binary.card_slClasses`), $w$ is
`properAutomorphCount D`. Sums over $0 < r < |D|$ are over `Finset.Ioo 0 D.natAbs`, over $1 \le r \le [|D|/2]$ over
`Finset.Icc 1 (D.natAbs / 2)`; $e(r/|D|)$ is `Complex.exp (2 * π * I * r / |D|)`. Indices are the book's (no shift).

**Formalized.**

* *Example 4* (**proved**, unconditional): `kroneckerGauss_sq` ($g^2 = D$) and `kroneckerGauss_eq_pm_sqrt` ($g = \pm\sqrt D$,
  resp. $\pm i\sqrt{|D|}$), `kroneckerGauss_eq_pm_gaussConst` ($g = \pm$ the constant of (2.20)). The proof does not follow the
  book's hint (reduction by Example 2 to prime discriminants and Example 3 for odd primes, a direct computation for
  $-4, \pm 8$) but uses the general facts $|g|^2 = |D|$ for a primitive character and $\bar g = \chi(-1) g$ for a real one:
  `kroneckerChar_isPrimitive` ($\chi_D$ is primitive of conductor $|D|$, from explicit units $u \equiv 1 \bmod |D|/q$
  with $\chi_D(u) = -1$ for each prime $q \mid D$, by quadratic reciprocity for the Jacobi symbol), `kronZ_neg_one`
  ($\chi_D(-1) = \operatorname{sign} D$) and `gaussSum_mul_star_of_real`. As a by-product `kroneckerGaussSum_of_sign` shows that the
  library's named statement `KroneckerGaussSum D` ((2.20) for all $m$) follows from its case $m = 1$ with the sign $+$; so what
  is still assumed in (2.20) is only the sign (Gauss's theorem).
* *Example 1* (**proved**, conditional on the named input `KroneckerGaussSum D` for the analytic step):
  the elementary identity `sum_kronZ_identity` / `sum_kronZ_eq_div`,
  $(2 - (D/2))\sum_{0<r<|D|}(D/r)\,r = -|D|\sum_{r \le |D|/2}(D/r)$ (unconditional; uses only $\chi_D(-1) = -1$,
  multiplicativity and, for even $D$, $\chi_D(1 + |D|/2) = -1$, `half_shift`), Theorem 2.1 (i) in finite-sum form
  `finite_sum_class_number_neg` (conditional on `KroneckerGaussSum D`: Dirichlet's class number formula
  `classNumberFormula_neg`, Lemma 2.3 `lemma_2_3_neg`, and an Abel-type limit theorem `abel_dirichlet` identifying the sum
  of the series with $L(1, \chi_D)$), and `class_number_half_sum` (Example 1).

**Numerical check** (Python, class numbers from reduced forms): the three identities $2|D|h = -w\sum(D/r)r$,
$2(2 - (D/2))h = w\sum_{r \le |D|/2}(D/r)$ and $(2 - (D/2))\sum(D/r)r = -|D|\sum_{r \le |D|/2}(D/r)$ hold for all fundamental
$-400 < D < 0$ (e.g. $D = -3, -4, -7, -8, -15, -20, -23, -24, -84$ with $h = 1, 1, 1, 1, 2, 2, 3, 2, 4$).
-/
import QuadFormsKB.Literature.Cassels.AppB.Sec2Lemmas

open Filter Topology
open QuadFormsKB.Binary

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels

/-! ### Ramification of the Kronecker character at each prime dividing $D$

For every prime $q \mid |D|$ we exhibit a natural number $u \equiv 1 \pmod{|D|/q}$ with $\chi_D(u) = -1$ (so $\chi_D$
does not factor through the modulus $|D|/q$), by evaluating Jacobi symbols with quadratic reciprocity. These give the
primitivity of $\chi_D$ (`kroneckerChar_isPrimitive`). -/

/-- Helper: the Jacobi symbol $(-1/u) = 1$ for $u \equiv 1 \pmod 4$. Argument: `u` the (odd) lower entry, `h` that
$u \equiv 1 \pmod 4$. -/
lemma jac_neg_one_of_mod4_one {u : ℕ} (h : u % 4 = 1) : jacobiSym (-1) u = 1 := by
  have h2 : u % 2 ≠ 0 := by omega
  rw [jacobiSym.at_neg_one (by rw [Nat.odd_iff]; omega), ZMod.χ₄_nat_eq_if_mod_four]
  simp [h2, h]

/-- Helper: the Jacobi symbol $(-1/u) = -1$ for $u \equiv 3 \pmod 4$. Argument: `u` the lower entry, `h` that
$u \equiv 3 \pmod 4$. -/
lemma jac_neg_one_of_mod4_three {u : ℕ} (h : u % 4 = 3) : jacobiSym (-1) u = -1 := by
  have h2 : u % 2 ≠ 0 := by omega
  have h1 : u % 4 ≠ 1 := by omega
  rw [jacobiSym.at_neg_one (by rw [Nat.odd_iff]; omega), ZMod.χ₄_nat_eq_if_mod_four]
  simp [h2, h1]

/-- Helper: the Jacobi symbol $(u/N) = 1$ when $u \equiv 1 \pmod N$. Arguments: `u` the upper entry, `N` the lower
entry, `h` the congruence. -/
lemma jac_of_modEq_one {u N : ℕ} (h : u ≡ 1 [MOD N]) : jacobiSym (u : ℤ) N = 1 := by
  rw [← jacobiSym.one_left N]
  apply jacobiSym.mod_left'
  have := h
  unfold Nat.ModEq at this
  rw [← Int.natCast_mod, this]
  simp

/-- Helper: the Jacobi (= Legendre) symbol $(u/q) = -1$ if $u$ reduces modulo the prime $q$ to a non-square. Arguments:
`q` the (odd) prime, `b` a non-square residue modulo $q$ (`hb`), `u` a natural number with $u \equiv b \pmod q$
(`hu`, $b$ read as its representative `b.val`). -/
lemma jac_nonres (q : ℕ) [hq : Fact q.Prime] (b : ZMod q) (hb : ¬ IsSquare b) (u : ℕ)
    (hu : u ≡ b.val [MOD q]) : jacobiSym (u : ℤ) q = -1 := by
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym]
  have : ((u : ℤ) : ZMod q) = b := by
    rw [Int.cast_natCast]
    rw [← ZMod.natCast_zmod_val b, ZMod.natCast_eq_natCast_iff]
    simpa using hu
  rw [this]
  exact quadraticChar_neg_one_iff_not_isSquare.mpr hb

/-- Helper: **ramification at an odd prime when $D \equiv 1 \pmod 4$.** For a prime $q \mid |D|$ there is a natural
number $u \equiv 1 \pmod{|D|/q}$ with $\chi_D(u) = -1$. Arguments: `D` the fundamental discriminant, `h` that
$D \equiv 1 \pmod 4$, `q` the prime and `hq` that it divides $|D|$. Proof: $|D|$ is squarefree and odd; choose $u$ by the
Chinese remainder theorem with $u \equiv 1 \pmod{|D|/q}$ and $u$ a non-square modulo $q$; then
$\chi_D(u) = (u/q)(u/(|D|/q)) = -1$. -/
theorem ramified_one {D : ℤ} [IsQuadDisc D] (h : D % 4 = 1) (q : ℕ) [Fact q.Prime] (hq : q ∣ D.natAbs) :
    ∃ u : ℕ, u ≡ 1 [MOD D.natAbs / q] ∧ kronZ D (u : ZMod D.natAbs) = -1 := by
  have hsq : Squarefree D.natAbs := Int.squarefree_natAbs.mpr (by
    rcases Int.isFundamentalDiscr_iff_squarefree.mp (IsQuadDisc.fund (D := D)) with ⟨_, h⟩ | ⟨h0, _⟩
    · exact h
    · omega)
  obtain ⟨N', hN'⟩ := hq
  have hodd := natAbs_odd_of_one h
  have hq2 : q ≠ 2 := by
    rintro rfl
    rw [hN'] at hodd
    exact absurd (Nat.odd_mul.mp hodd).1 (by decide)
  have hN'0 : N' ≠ 0 := by
    rintro rfl
    have := three_le_natAbs (D := D)
    omega
  have hcop : Nat.Coprime N' q := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out)]
    rintro ⟨k, hk⟩
    rw [hk] at hN'
    have : q * q ∣ D.natAbs := ⟨k, by rw [hN']; ring⟩
    have := hsq q this
    exact (Fact.out : q.Prime).one_lt.ne' (Nat.isUnit_iff.mp this)
  have : ¬ ringChar (ZMod q) = 2 := by rw [ZMod.ringChar_zmod_n]; exact hq2
  obtain ⟨b, hb⟩ := FiniteField.exists_nonsquare this
  obtain ⟨u, hu1, hu2⟩ := Nat.chineseRemainder hcop 1 b.val
  refine ⟨u, ?_, ?_⟩
  · rw [hN', Nat.mul_div_cancel_left _ (Fact.out : q.Prime).pos]; exact hu1
  · rw [kronZ_natCast_of_one h]
    have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    have : NeZero N' := ⟨hN'0⟩
    rw [hN', jacobiSym.mul_right, jac_nonres q b hb u hu2, jac_of_modEq_one hu1, mul_one]

/-- Helper: the Jacobi symbol $(a/u) = 1$ when $u$ is odd and $u \equiv 1 \pmod{4a}$ (periodicity of the symbol in the
lower entry, Mathlib's `jacobiSym.mod_right`). Arguments: `a` the positive upper entry, `u` the odd lower entry, `h` the
congruence. -/
lemma jac_of_modEq_one' {u a : ℕ} (ha : 0 < a) (hu : Odd u) (h : u ≡ 1 [MOD 4 * a]) :
    jacobiSym (a : ℤ) u = 1 := by
  rw [jacobiSym.mod_right _ hu, Int.natAbs_natCast]
  unfold Nat.ModEq at h
  rw [h, Nat.mod_eq_of_lt (by omega : 1 < 4 * a)]
  exact jacobiSym.one_right _

/-- Helper: for $4 \mid D$ and $n$ odd, $\chi_D(n) = (D/4 \,/\, n)$ (Jacobi symbol; restatement of
`kronZ_natCast_of_zero`). Arguments: `D` the fundamental discriminant, `h` that $4 \mid D$, `n` an odd natural number. -/
theorem kronZ_zero_odd {D : ℤ} [IsQuadDisc D] (h : D % 4 = 0) {n : ℕ} (hn : Odd n) :
    kronZ D (n : ZMod D.natAbs) = jacobiSym (D / 4) n := kronZ_natCast_of_zero h hn

/-- Helper: the facts about a fundamental discriminant $D = 4m$ used below: $|D| = 4|m|$, $|m|$ squarefree,
$m \equiv 2, 3 \pmod 4$ and $m \ne 0$. Arguments: `D` the fundamental discriminant, `h` that $4 \mid D$. -/
theorem zero_case_facts {D : ℤ} [IsQuadDisc D] (h : D % 4 = 0) :
    D.natAbs = 4 * (D / 4).natAbs ∧ Squarefree (D / 4).natAbs ∧ (D / 4 % 4 = 2 ∨ D / 4 % 4 = 3) ∧
      0 < (D / 4).natAbs := by
  have hN : D.natAbs = 4 * (D / 4).natAbs := by omega
  rcases Int.isFundamentalDiscr_iff_squarefree.mp (IsQuadDisc.fund (D := D)) with ⟨h1, _⟩ | ⟨_, hsq, hm⟩
  · omega
  · exact ⟨hN, Int.squarefree_natAbs.mpr hsq, hm, by omega⟩

/-- Helper: **ramification at an odd prime when $4 \mid D$.** For an odd prime $q \mid |D|$ there is a natural number
$u \equiv 1 \pmod{|D|/q}$ with $\chi_D(u) = -1$. Arguments: `D` the fundamental discriminant, `h` that $4 \mid D$, `q` the
prime, `hq2` that $q \ne 2$, `hq` that $q \mid |D|$. Proof: write $|D/4| = q a_1$; take $u \equiv 1 \pmod{4a_1}$ and a
non-square modulo $q$; then $u \equiv 1 \pmod 4$, so by quadratic reciprocity $\chi_D(u) = (D/4\,/\,u) = (q/u) = (u/q) = -1$. -/
theorem ramified_zero_odd {D : ℤ} [IsQuadDisc D] (h : D % 4 = 0) (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (hq : q ∣ D.natAbs) :
    ∃ u : ℕ, u ≡ 1 [MOD D.natAbs / q] ∧ kronZ D (u : ZMod D.natAbs) = -1 := by
  obtain ⟨hN, hsq, hm, hapos⟩ := zero_case_facts h
  have hqp : q.Prime := Fact.out
  set a := (D / 4).natAbs with ha
  have hqa : q ∣ a := by
    rw [hN] at hq
    rcases (Nat.Prime.dvd_mul hqp).mp hq with h4 | h4
    · exfalso
      have : q ∣ 2 ^ 2 := by simpa using h4
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow this))
    · exact h4
  obtain ⟨a1, ha1⟩ := hqa
  have ha1pos : 0 < a1 := by
    rcases Nat.eq_zero_or_pos a1 with h0 | h0
    · rw [h0] at ha1; omega
    · exact h0
  have hqa1 : ¬ q ∣ a1 := by
    rintro ⟨k, hk⟩
    have : q * q ∣ a := ⟨k, by rw [ha1, hk]; ring⟩
    have := hsq q this
    exact hqp.one_lt.ne' (Nat.isUnit_iff.mp this)
  have hcop : Nat.Coprime (4 * a1) q := by
    rw [Nat.coprime_comm, hqp.coprime_iff_not_dvd]
    intro hd
    rcases (Nat.Prime.dvd_mul hqp).mp hd with h4 | h4
    · have : q ∣ 2 ^ 2 := by simpa using h4
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow this))
    · exact hqa1 h4
  have : ¬ ringChar (ZMod q) = 2 := by rw [ZMod.ringChar_zmod_n]; exact hq2
  obtain ⟨b, hb⟩ := FiniteField.exists_nonsquare this
  obtain ⟨u, hu1, hu2⟩ := Nat.chineseRemainder hcop 1 b.val
  have hNq : D.natAbs / q = 4 * a1 := by
    rw [hN, ha1]
    rw [show 4 * (q * a1) = q * (4 * a1) by ring]
    exact Nat.mul_div_cancel_left _ hqp.pos
  have hu4 : u % 4 = 1 := by
    have := Nat.ModEq.of_dvd (dvd_mul_right 4 a1) hu1
    unfold Nat.ModEq at this
    omega
  have huodd : Odd u := by rw [Nat.odd_iff]; omega
  refine ⟨u, by rw [hNq]; exact hu1, ?_⟩
  rw [kronZ_zero_odd h huodd]
  have hJa1 : jacobiSym (a1 : ℤ) u = 1 := jac_of_modEq_one' ha1pos huodd hu1
  have hJq : jacobiSym (q : ℤ) u = -1 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four' (hqp.odd_of_ne_two hq2) hu4]
    exact jac_nonres q b hb u hu2
  have hJa : jacobiSym (a : ℤ) u = -1 := by
    rw [ha1, Nat.cast_mul, jacobiSym.mul_left, hJq, hJa1]; ring
  rcases Int.natAbs_eq (D / 4) with hm1 | hm1
  · rw [hm1]; exact hJa
  · rw [hm1, ← neg_one_mul, jacobiSym.mul_left, jac_neg_one_of_mod4_one hu4, hJa]; ring

/-- Helper: $1 + nk \equiv 1 \pmod n$. Arguments: `n` the modulus, `k` the multiplier. -/
lemma modEq_one_add_mul (n k : ℕ) : 1 + n * k ≡ 1 [MOD n] := by
  unfold Nat.ModEq
  rw [Nat.add_mul_mod_self_left]

/-- Helper: **ramification at the prime $2$ when $4 \mid D$.** $\chi_D(1 + |D|/2) = -1$, where $|D|/2 = 2|D/4|$.
Argument: `D` the fundamental discriminant, `h` that $4 \mid D$. Proof: if $D/4 = \pm a$ is odd, $u = 1 + 2a \equiv 3
\pmod 4$ and quadratic reciprocity gives $-1$; if $D/4 = \pm 2a'$ with $a'$ odd, $u = 1 + 4a' \equiv 5 \pmod 8$, so
$(2/u) = -1$ and $(a'/u) = (u/a') = 1$. -/
theorem half_shift {D : ℤ} [IsQuadDisc D] (h : D % 4 = 0) :
    kronZ D (((1 + 2 * (D / 4).natAbs : ℕ)) : ZMod D.natAbs) = -1 := by
  obtain ⟨hN, hsq, hm, hapos⟩ := zero_case_facts h
  set a := (D / 4).natAbs with ha
  rcases hm with hm2 | hm3
  · -- `D / 4 ≡ 2 (mod 4)`: `a = 2 a'` with `a'` odd, `|D| = 8 a'`
    obtain ⟨a', ha'⟩ : ∃ a', a = 2 * a' := ⟨a / 2, by omega⟩
    have ha'odd : a' % 2 = 1 := by omega
    have ha'pos : 0 < a' := by omega
    have hNh : D.natAbs / 2 = 4 * a' := by omega
    have hu1 : 1 + 4 * a' * 1 ≡ 1 [MOD 4 * a'] := modEq_one_add_mul _ _
    set u := 1 + 4 * a' * 1 with hu
    have hu8 : u % 8 = 5 := by omega
    have hu4 : u % 4 = 1 := by omega
    have huodd : Odd u := by rw [Nat.odd_iff]; omega
    have hueq : 1 + 2 * a = u := by omega
    rw [hueq, kronZ_zero_odd h huodd]
    have hJ2 : jacobiSym 2 u = -1 := by
      rw [jacobiSym.at_two huodd, ZMod.χ₈_nat_eq_if_mod_eight]
      have h1 : u % 2 ≠ 0 := by omega
      have h2 : ¬ (u % 8 = 1 ∨ u % 8 = 7) := by omega
      simp [h1, h2]
    have hJa' : jacobiSym (a' : ℤ) u = 1 := by
      rw [jacobiSym.quadratic_reciprocity_one_mod_four' (by rw [Nat.odd_iff]; exact ha'odd) hu4]
      exact jac_of_modEq_one (Nat.ModEq.of_dvd (dvd_mul_left a' 4) hu1)
    have hJa : jacobiSym (a : ℤ) u = -1 := by
      rw [ha', Nat.cast_mul, jacobiSym.mul_left, hJa']
      simp [hJ2]
    rcases Int.natAbs_eq (D / 4) with hm1 | hm1
    · rw [hm1]; exact hJa
    · rw [hm1, ← neg_one_mul, jacobiSym.mul_left, jac_neg_one_of_mod4_one hu4, hJa]; ring
  · -- `D / 4 ≡ 3 (mod 4)`: `a` odd, `|D| = 4 a`
    have hNh : D.natAbs / 2 = 2 * a := by omega
    have hu1 : 1 + 2 * a * 1 ≡ 1 [MOD 2 * a] := modEq_one_add_mul _ _
    have haodd : a % 2 = 1 := by omega
    set u := 1 + 2 * a * 1 with hu
    have hu4 : u % 4 = 3 := by omega
    have huodd : Odd u := by rw [Nat.odd_iff]; omega
    have hueq : 1 + 2 * a = u := by omega
    rw [hueq, kronZ_zero_odd h huodd]
    have hua : u ≡ 1 [MOD a] := Nat.ModEq.of_dvd (dvd_mul_left a 2) hu1
    rcases Int.natAbs_eq (D / 4) with hm1 | hm1
    · have ha4 : a % 4 = 3 := by omega
      rw [hm1, jacobiSym.quadratic_reciprocity_three_mod_four ha4 hu4, jac_of_modEq_one hua]
    · have ha4 : a % 4 = 1 := by omega
      rw [hm1, ← neg_one_mul, jacobiSym.mul_left, jac_neg_one_of_mod4_three hu4,
        jacobiSym.quadratic_reciprocity_one_mod_four ha4 huodd, jac_of_modEq_one hua]
      ring

/-- Helper: **ramification at the prime $2$ when $4 \mid D$**, in the form needed for primitivity: there is
$u \equiv 1 \pmod{|D|/2}$ with $\chi_D(u) = -1$ (namely $u = 1 + |D|/2$, `half_shift`). Arguments: `D` the fundamental
discriminant, `h` that $4 \mid D$. -/
theorem ramified_zero_two {D : ℤ} [IsQuadDisc D] (h : D % 4 = 0) :
    ∃ u : ℕ, u ≡ 1 [MOD D.natAbs / 2] ∧ kronZ D (u : ZMod D.natAbs) = -1 := by
  obtain ⟨hN, hsq, hm, hapos⟩ := zero_case_facts h
  refine ⟨1 + 2 * (D / 4).natAbs, ?_, half_shift h⟩
  have : D.natAbs / 2 = 2 * (D / 4).natAbs := by omega
  rw [this]
  simp

/-- Helper: for odd $a$ and $n \equiv 3 \pmod 4$ with $n \equiv -1 \pmod a$, the Jacobi symbol $(a/n) = 1$ (quadratic
reciprocity). Arguments: `a` the odd upper entry (`ha`), `n` the lower entry with `hn : n % 4 = 3`, `hdvd` that
$a \mid n + 1$. -/
lemma jac_pos_of_neg_one {a n : ℕ} (ha : a % 2 = 1) (hn : n % 4 = 3) (hdvd : a ∣ n + 1) :
    jacobiSym (a : ℤ) n = 1 := by
  have hnodd : Odd n := by rw [Nat.odd_iff]; omega
  have haodd : Odd a := by rw [Nat.odd_iff]; exact ha
  have hJ : jacobiSym (n : ℤ) a = jacobiSym (-1) a := by
    apply jacobiSym.mod_left'
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    apply Int.emod_eq_zero_of_dvd
    have : (a : ℤ) ∣ ((n + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hdvd
    simpa using this
  rcases (by omega : a % 4 = 1 ∨ a % 4 = 3) with h1 | h3
  · rw [jacobiSym.quadratic_reciprocity_one_mod_four h1 hnodd, hJ, jac_neg_one_of_mod4_one h1]
  · rw [jacobiSym.quadratic_reciprocity_three_mod_four h3 hn, hJ, jac_neg_one_of_mod4_three h3]
    ring

/-- **The sign of the Kronecker character:** $\chi_D(-1) = \operatorname{sign}(D)$, i.e. $(D/{-1}) = 1$ for $D > 0$ and
$-1$ for $D < 0$ (Cassels, Ch. 14, Ex. 2, used for Lemma 2.3 as a consequence of (2.20)). Here proved directly from the
definition by evaluating a Jacobi symbol at $|D| - 1 \equiv -1 \pmod{|D|}$ with quadratic reciprocity. Argument: `D` the
fundamental discriminant; $-1$ is read in $\mathbb Z/|D|$. Unconditional. -/
theorem kronZ_neg_one {D : ℤ} [IsQuadDisc D] : kronZ D (-1) = Int.sign D := by
  have h3 := three_le_natAbs (D := D)
  have hcast : ((D.natAbs - 1 : ℕ) : ZMod D.natAbs) = -1 := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]; simp
  rw [← hcast]
  by_cases h : D % 4 = 1
  · rw [kronZ_natCast_of_one h]
    have : jacobiSym ((D.natAbs - 1 : ℕ) : ℤ) D.natAbs = jacobiSym (-1) D.natAbs := by
      apply jacobiSym.mod_left'
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
      apply Int.emod_eq_zero_of_dvd
      rw [Nat.cast_sub (by omega)]
      simp
    rw [this, jacobiSym.at_neg_one (natAbs_odd_of_one h), ZMod.χ₄_nat_eq_if_mod_four]
    rcases lt_or_gt_of_ne (by omega : D ≠ 0) with hneg | hpos
    · rw [Int.sign_eq_neg_one_of_neg hneg]
      have h2 : D.natAbs % 2 ≠ 0 := by omega
      have h4 : D.natAbs % 4 ≠ 1 := by omega
      simp [h2, h4]
    · rw [Int.sign_eq_one_of_pos hpos]
      have h2 : D.natAbs % 2 ≠ 0 := by omega
      have h4 : D.natAbs % 4 = 1 := by omega
      simp [h2, h4]
  · have h0 : D % 4 = 0 := by have := (IsQuadDisc.fund (D := D)).1; omega
    obtain ⟨hN, hsq, hm, hapos⟩ := zero_case_facts h0
    set a := (D / 4).natAbs with ha
    have hn4 : (D.natAbs - 1) % 4 = 3 := by omega
    have hnodd : Odd (D.natAbs - 1) := by rw [Nat.odd_iff]; omega
    rw [kronZ_zero_odd h0 hnodd]
    -- the symbol for the positive odd part
    have key : ∀ b : ℕ, b % 2 = 1 → b ∣ D.natAbs → jacobiSym (b : ℤ) (D.natAbs - 1) = 1 := by
      intro b hb hbd
      apply jac_pos_of_neg_one hb hn4
      rwa [Nat.sub_add_cancel (by omega)]
    have hsgn : ∀ b : ℕ, b % 2 = 1 → b ∣ D.natAbs → jacobiSym (-(b : ℤ)) (D.natAbs - 1) = -1 := by
      intro b hb hbd
      rw [← neg_one_mul, jacobiSym.mul_left, jac_neg_one_of_mod4_three hn4, key b hb hbd]; ring
    rcases hm with hm2 | hm3
    · obtain ⟨a', ha'⟩ : ∃ a', a = 2 * a' := ⟨a / 2, by omega⟩
      have ha'odd : a' % 2 = 1 := by omega
      have hn8 : (D.natAbs - 1) % 8 = 7 := by omega
      have hJ2 : jacobiSym 2 (D.natAbs - 1) = 1 := by
        rw [jacobiSym.at_two hnodd, ZMod.χ₈_nat_eq_if_mod_eight]
        have h1 : (D.natAbs - 1) % 2 ≠ 0 := by omega
        simp [h1, hn8]
      have hd : a' ∣ D.natAbs := ⟨4 * 2, by omega⟩
      have hm1' : D / 4 = (a : ℤ) ∨ D / 4 = -(a : ℤ) := by rw [ha]; exact Int.natAbs_eq (D / 4)
      rcases hm1' with hm1 | hm1
      · rw [hm1, ha', Nat.cast_mul, Nat.cast_ofNat, jacobiSym.mul_left, hJ2, key a' ha'odd hd,
          Int.sign_eq_one_of_pos (by omega)]
        simp
      · rw [hm1, ha', Nat.cast_mul, Nat.cast_ofNat, neg_mul_eq_mul_neg, jacobiSym.mul_left, hJ2, hsgn a' ha'odd hd,
          Int.sign_eq_neg_one_of_neg (by omega)]
        simp
    · have haodd : a % 2 = 1 := by omega
      have hd : a ∣ D.natAbs := ⟨4, by omega⟩
      have hm1' : D / 4 = (a : ℤ) ∨ D / 4 = -(a : ℤ) := by rw [ha]; exact Int.natAbs_eq (D / 4)
      rcases hm1' with hm1 | hm1
      · rw [hm1, key a haodd hd, Int.sign_eq_one_of_pos (by omega)]
      · rw [hm1, hsgn a haodd hd, Int.sign_eq_neg_one_of_neg (by omega)]

/-- Helper: **ramification of $\chi_D$ at every prime $q \mid D$**: there is $u \equiv 1 \pmod{|D|/q}$ with
$\chi_D(u) = -1$. Arguments: `D` the fundamental discriminant, `q` the prime, `hq` that $q \mid |D|$ (cases
`ramified_one`, `ramified_zero_odd`, `ramified_zero_two`). -/
theorem ramified_all {D : ℤ} [IsQuadDisc D] (q : ℕ) [Fact q.Prime] (hq : q ∣ D.natAbs) :
    ∃ u : ℕ, u ≡ 1 [MOD D.natAbs / q] ∧ kronZ D (u : ZMod D.natAbs) = -1 := by
  by_cases h : D % 4 = 1
  · exact ramified_one h q hq
  · have h0 : D % 4 = 0 := by have := (IsQuadDisc.fund (D := D)).1; omega
    by_cases hq2 : q = 2
    · subst hq2
      exact ramified_zero_two h0
    · exact ramified_zero_odd h0 q hq2 hq

/-- **The Kronecker character of a fundamental discriminant is primitive of conductor $|D|$** (this is where "$D$
fundamental" enters: it is the step the library's Kronecker character construction lacked). Argument: `D` the
fundamental discriminant. Proof: if the conductor were a proper divisor of $|D|$, the character would factor through
$|D|/q$ for a prime $q$, contradicting the unit $u \equiv 1 \pmod{|D|/q}$ with $\chi_D(u) = -1$ of `ramified_all`.
Unconditional. -/
@[kb "cassels1978" "App. B, Ex. 4, p. 389 (χ_D is primitive of conductor |D|; used for the Gauss sum)"]
theorem kroneckerChar_isPrimitive {D : ℤ} [IsQuadDisc D] : (kroneckerChar D).IsPrimitive := by
  have : NeZero D.natAbs := ⟨by have := three_le_natAbs (D := D); omega⟩
  by_contra hne
  have hc : (kroneckerChar D).conductor ∣ D.natAbs := DirichletCharacter.conductor_dvd_level _
  have hFc := DirichletCharacter.factorsThrough_conductor (kroneckerChar D)
  have hne' : (kroneckerChar D).conductor ≠ D.natAbs := hne
  generalize (kroneckerChar D).conductor = c at hc hFc hne'
  obtain ⟨k, hk⟩ := hc
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact hne' (by omega)
  obtain ⟨q, hq, k', hk'⟩ := Nat.exists_prime_and_dvd hk1
  have := Fact.mk hq
  have hNq : D.natAbs / q = c * k' := by
    rw [hk, hk', show c * (q * k') = q * (c * k') by ring]
    exact Nat.mul_div_cancel_left _ hq.pos
  have hqN : q ∣ D.natAbs := ⟨c * k', by rw [hk, hk']; ring⟩
  have hdvd : D.natAbs / q ∣ D.natAbs := Nat.div_dvd_of_dvd hqN
  have hF : (kroneckerChar D).FactorsThrough (D.natAbs / q) :=
    DirichletCharacter.FactorsThrough.mono _ hFc
      (by rw [hNq]; exact dvd_mul_right _ _) hdvd
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hdvd] at hF
  obtain ⟨u, hu1, hu2⟩ := ramified_all q hqN
  have hunit : IsUnit (u : ZMod D.natAbs) := by
    by_contra hnu
    have := kronZ_nonunit (D := D) _ hnu
    omega
  have hmem : hunit.unit ∈ (ZMod.unitsMap hdvd).ker := by
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [ZMod.unitsMap_def, Units.coe_map]
    simp only [MonoidHom.coe_ofClass, IsUnit.unit_spec, Units.val_one]
    rw [map_natCast]
    rw [show (1 : ZMod (D.natAbs / q)) = ((1 : ℕ) : ZMod (D.natAbs / q)) by simp, ZMod.natCast_eq_natCast_iff]
    exact hu1
  have h3 := congrArg Units.val (MonoidHom.mem_ker.mp (hF hmem))
  rw [MulChar.coe_toUnitHom, Units.val_one, IsUnit.unit_spec, kroneckerChar_apply, hu2] at h3
  norm_num at h3

/-- Helper: a character whose values at units square to $1$ is its own inverse. Arguments: `N` the modulus, `χ` the
character modulo $N$, `hsq` the squaring condition on units. -/
lemma real_char_inv {N : ℕ} (χ : DirichletCharacter ℂ N) (hsq : ∀ u : (ZMod N)ˣ, χ u * χ u = 1) :
    χ⁻¹ = χ := by
  refine MulChar.ext' (fun x => ?_)
  rw [MulChar.inv_apply_eq_inv']
  by_cases hx : IsUnit x
  · have := hsq hx.unit
    rw [IsUnit.unit_spec] at this
    exact inv_eq_of_mul_eq_one_right this
  · rw [MulChar.map_nonunit χ hx]; simp

/-- Helper: $g \bar g = N$ for the Gauss sum $g = \sum_{x \bmod N}\chi(x)e(x/N)$ of a primitive real character $\chi$
modulo $N$. Arguments: `N` the modulus ($N \ge 1$), `χ` the character, `hprim` that it is primitive (conductor $N$),
`hreal` that its values are real, `hsq` that it squares to $1$ at units. Proof: Parseval over the shifts
$e_a(x) = e(ax/N)$ computed in two ways (primitivity makes $g(\chi, e_a) = \bar\chi(a)\,g$, Mathlib's
`gaussSum_mulShift_of_isPrimitive`). -/
theorem gaussSum_mul_star_of_real {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hprim : χ.IsPrimitive) (hreal : ∀ x, star (χ x) = χ x)
    (hsq : ∀ u : (ZMod N)ˣ, χ u * χ u = 1) :
    gaussSum χ ZMod.stdAddChar * star (gaussSum χ ZMod.stdAddChar) = N := by
  classical
  set e : AddChar (ZMod N) ℂ := ZMod.stdAddChar with he
  set g := gaussSum χ e with hg
  have hχχ : ∀ x : ZMod N, χ x * χ x = if IsUnit x then 1 else 0 := by
    intro x
    by_cases hx : IsUnit x
    · rw [ite_eq_left hx]
      have := hsq hx.unit
      simpa using this
    · rw [ite_eq_right hx, MulChar.map_nonunit χ hx]; simp
  have hinv : χ⁻¹ = χ := real_char_inv χ hsq
  have hA : ∀ a : ZMod N, gaussSum χ (e.mulShift a) * star (gaussSum χ (e.mulShift a)) =
      (if IsUnit a then 1 else 0) * (g * star g) := by
    intro a
    rw [gaussSum_mulShift_of_isPrimitive e hprim a, hinv, star_mul', hreal, ← hχχ a]
    ring
  have hstar : ∀ z : ZMod N, star (e z) = e (-z) := by
    intro z
    rw [AddChar.map_neg_eq_conj]; rfl
  have hC : ∑ a : ZMod N, gaussSum χ (e.mulShift a) * star (gaussSum χ (e.mulShift a)) =
      N * ∑ x : ZMod N, χ x * χ x := by
    have h1 : ∀ a : ZMod N, gaussSum χ (e.mulShift a) * star (gaussSum χ (e.mulShift a)) =
        ∑ x : ZMod N, ∑ y : ZMod N, χ x * χ y * e (a * (x - y)) := by
      intro a
      unfold gaussSum
      simp only [AddChar.mulShift_apply]
      rw [star_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
      rw [star_mul', hreal, hstar]
      calc χ x * e (a * x) * (χ y * e (-(a * y))) = χ x * χ y * (e (a * x) * e (-(a * y))) := by ring
        _ = χ x * χ y * e (a * (x - y)) := by
          rw [← AddChar.map_add_eq_mul]; congr 2; ring
    have h2 : ∀ x y : ZMod N, ∑ a : ZMod N, χ x * χ y * e (a * (x - y)) =
        if x = y then χ x * χ x * N else 0 := by
      intro x y
      rw [← Finset.mul_sum, AddChar.sum_mulShift (x - y) (ZMod.isPrimitive_stdAddChar N)]
      by_cases hxy : x = y
      · subst hxy; simp [ZMod.card]
      · have : x - y ≠ 0 := sub_ne_zero.mpr hxy
        simp [hxy, this]
    calc ∑ a : ZMod N, gaussSum χ (e.mulShift a) * star (gaussSum χ (e.mulShift a))
        = ∑ a : ZMod N, ∑ x : ZMod N, ∑ y : ZMod N, χ x * χ y * e (a * (x - y)) :=
          Finset.sum_congr rfl (fun a _ => h1 a)
      _ = ∑ x : ZMod N, ∑ a : ZMod N, ∑ y : ZMod N, χ x * χ y * e (a * (x - y)) := Finset.sum_comm
      _ = ∑ x : ZMod N, ∑ y : ZMod N, ∑ a : ZMod N, χ x * χ y * e (a * (x - y)) :=
          Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
      _ = ∑ x : ZMod N, χ x * χ x * N := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          simp_rw [h2 x]
          simp
      _ = N * ∑ x : ZMod N, χ x * χ x := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun x _ => by ring)
  have hc : (∑ x : ZMod N, χ x * χ x) = ∑ a : ZMod N, (if IsUnit a then (1 : ℂ) else 0) :=
    Finset.sum_congr rfl (fun x _ => hχχ x)
  have hcpos : (∑ a : ZMod N, (if IsUnit a then (1 : ℂ) else 0)) ≠ 0 := by
    rw [Finset.sum_boole]
    have : 0 < (Finset.univ.filter (fun a : ZMod N => IsUnit a)).card :=
      Finset.card_pos.mpr ⟨1, by simp⟩
    exact_mod_cast this.ne'
  have hB : ∑ a : ZMod N, gaussSum χ (e.mulShift a) * star (gaussSum χ (e.mulShift a)) =
      (∑ a : ZMod N, (if IsUnit a then (1 : ℂ) else 0)) * (g * star g) := by
    rw [Finset.sum_congr rfl (fun a _ => hA a), ← Finset.sum_mul]
  rw [hB, hc] at hC
  have := mul_left_cancel₀ hcpos (hC.trans (mul_comm _ _))
  exact this

section GaussD

variable {D : ℤ} [IsQuadDisc D]

/-- Helper: the Kronecker character is real valued, $\overline{\chi_D(x)} = \chi_D(x)$. Argument: `x` a residue modulo
$|D|$. -/
lemma kroneckerChar_star (x : ZMod D.natAbs) : star (kroneckerChar D x) = kroneckerChar D x := by
  rw [kroneckerChar_apply]; simp

/-- Helper: the Kronecker character squares to $1$ at units, $\chi_D(u)^2 = 1$. Argument: `u` a unit modulo $|D|$. -/
lemma kroneckerChar_sq_unit (u : (ZMod D.natAbs)ˣ) : kroneckerChar D u * kroneckerChar D u = 1 := by
  have h : IsUnit (kronZ D (u : ZMod D.natAbs)) := u.isUnit.map (kronMulChar D)
  rcases Int.isUnit_iff.mp h with h | h <;> simp [kroneckerChar_apply, h]

/-- Helper: $\chi_D(-1) = \operatorname{sign}(D)$ as a complex number (`kronZ_neg_one`). -/
lemma kroneckerChar_neg_one : kroneckerChar D (-1) = ((Int.sign D : ℤ) : ℂ) := by
  rw [kroneckerChar_apply, kronZ_neg_one]

omit [IsQuadDisc D] in
/-- Helper: $D = \operatorname{sign}(D)\,|D|$ in $\mathbb C$. Argument: `D` an integer. -/
lemma sign_mul_natAbs_complex : ((Int.sign D : ℤ) : ℂ) * (D.natAbs : ℂ) = (D : ℂ) := by
  have h := congrArg (fun z : ℤ => (z : ℂ)) (Int.sign_mul_natAbs D)
  simp only [Int.cast_mul, Int.cast_natCast] at h
  exact h

/-- Helper: $\operatorname{sign}(D)^2 = 1$ in $\mathbb C$ for a fundamental discriminant $D$ (as $\chi_D(-1)^2 = 1$). -/
lemma sign_sq_complex : ((Int.sign D : ℤ) : ℂ) * ((Int.sign D : ℤ) : ℂ) = 1 := by
  have h := kroneckerChar_sq_unit (D := D) (-1)
  rw [Units.val_neg, Units.val_one, kroneckerChar_neg_one] at h
  exact h

/-- Helper: the square of Mathlib's Gauss sum $g = \sum_{x \in \mathbb Z/|D|}\chi_D(x)\,e(x/|D|)$ (`gaussSum` with the
standard additive character `ZMod.stdAddChar`) equals $D$. Arguments: `D` the fundamental discriminant, and the (derivable)
instance that $|D| \ne 0$. See `kroneckerGauss_sq` for the form with the sum over $0 \le r < |D|$. -/
theorem gaussSum_kroneckerChar_sq [NeZero D.natAbs] :
    gaussSum (kroneckerChar D) ZMod.stdAddChar ^ 2 = (D : ℂ) := by
  have hprim := kroneckerChar_isPrimitive (D := D)
  have h1 := gaussSum_mul_star_of_real (kroneckerChar D) hprim kroneckerChar_star kroneckerChar_sq_unit
  have hinv := real_char_inv (kroneckerChar D) kroneckerChar_sq_unit
  set g := gaussSum (kroneckerChar D) ZMod.stdAddChar with hg
  have hstar : star g = ((Int.sign D : ℤ) : ℂ) * g := by
    rw [hg, star_gaussSum_eq, hinv, AddChar.inv_mulShift, gaussSum_mulShift_of_isPrimitive _ hprim, hinv,
      kroneckerChar_neg_one]
  rw [hstar] at h1
  have hs := sign_sq_complex (D := D)
  calc g ^ 2 = ((Int.sign D : ℤ) : ℂ) * (g * (((Int.sign D : ℤ) : ℂ) * g)) := by
        linear_combination (-(g ^ 2)) * hs
    _ = ((Int.sign D : ℤ) : ℂ) * (D.natAbs : ℂ) := by rw [h1]
    _ = (D : ℂ) := sign_mul_natAbs_complex

/-- Helper: Mathlib's Gauss sum over $\mathbb Z/|D|$ is the sum over $0 \le r < |D|$ of $\chi_D(r)\,e^{2\pi i r/|D|}$.
Argument: `D` the fundamental discriminant (and the instance $|D| \ne 0$). -/
theorem gaussSum_kroneckerChar_eq_range [NeZero D.natAbs] :
    gaussSum (kroneckerChar D) ZMod.stdAddChar =
      ∑ r ∈ Finset.range D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) / (D.natAbs : ℂ)) := by
  unfold gaussSum
  refine Finset.sum_nbij' (fun x => x.val) (fun r => (r : ZMod D.natAbs)) ?_ ?_ ?_ ?_ ?_
  · intro x _; simpa using ZMod.val_lt x
  · intro r _; simp
  · intro x _; simp
  · intro r hr; simpa using ZMod.val_natCast_of_lt (Finset.mem_range.mp hr)
  · intro x _
    have e1 : ZMod.stdAddChar x = Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) / (D.natAbs : ℂ)) := by
      have := ZMod.stdAddChar_coe (N := D.natAbs) (x.val : ℤ)
      rw [Int.cast_natCast, ZMod.natCast_zmod_val] at this
      rw [this]; push_cast; rfl
    rw [e1, ZMod.natCast_zmod_val]

end GaussD

/-! ### The elementary identity of Example 1

Pure combinatorics of a function $f : \mathbb N \to \mathbb Z$ (later $f(r) = (D/r)$) on $0 \le r < N$: with
$f(N - r) = -f(r)$, multiplicativity and $f(2)^2 = 1$ (odd $N$), or $f(r + N/2) = -f(r)$ and $f(2) = 0$ (even $N$),
$(2 - f(2))\sum_{r<N} r f(r) = -N\sum_{r \le N/2} f(r)$. -/

/-- Helper: splitting $\sum_{r < 2n+1} g(r)$ into the even and odd indices. Arguments: `g` the summand, `n` the
half-length. -/
lemma sum_range_parity (g : ℕ → ℤ) (n : ℕ) :
    ∑ r ∈ Finset.range (2 * n + 1), g r =
      g 0 + ∑ s ∈ Finset.range n, g (2 * (s + 1)) + ∑ s ∈ Finset.range n, g (2 * s + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e1 : 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 := by ring
    have e2 : 2 * n + 1 + 1 = 2 * (n + 1) := by ring
    rw [e1, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ _ n,
      Finset.sum_range_succ _ n, e2]
    ring

/-- Helper: the elementary identity for an odd length $N = 2n + 1$:
$(2 - f(2))\sum_{r<N} f(r)\,r = -N\sum_{s<n} f(s+1)$. Arguments: `N`, `n` with `hN : N = 2 * n + 1`; `f` the function;
`hrefl` that $f(N - r) = -f(r)$ for $r \le N$; `hmul` multiplicativity; `h0` that $f(0) = 0$; `hsq` that $f(2)^2 = 1$.
Proof: the reflection $r \mapsto N - r$ gives $S = 2P - NT$ and the split into even and odd $r$ (odd $r$ are
$N - 2u$) gives $S = 4f(2)P - f(2)NT$, for $S = \sum f(r)r$, $P = \sum_{s<n} f(s+1)(s+1)$, $T = \sum_{s<n} f(s+1)$. -/
theorem elem_odd (N n : ℕ) (hN : N = 2 * n + 1) (f : ℕ → ℤ)
    (hrefl : ∀ r, r ≤ N → f (N - r) = - f r)
    (hmul : ∀ a b, f (a * b) = f a * f b) (h0 : f 0 = 0) (hsq : f 2 * f 2 = 1) :
    (2 - f 2) * ∑ r ∈ Finset.range N, f r * (r : ℤ) =
      - (N : ℤ) * ∑ s ∈ Finset.range n, f (s + 1) := by
  subst hN
  set S := ∑ r ∈ Finset.range (2 * n + 1), f r * (r : ℤ) with hS
  set P := ∑ s ∈ Finset.range n, f (s + 1) * ((s + 1 : ℕ) : ℤ) with hP
  set T := ∑ s ∈ Finset.range n, f (s + 1) with hT
  set N : ℤ := ((2 * n + 1 : ℕ) : ℤ) with hN
  -- (E1) reflection
  have E1 : S = 2 * P - N * T := by
    have hsplit : ∑ r ∈ Finset.range (2 * n + 1), f r * (r : ℤ) =
        ∑ r ∈ Finset.range (n + 1), f r * (r : ℤ) +
          ∑ x ∈ Finset.range n, f (n + 1 + x) * ((n + 1 + x : ℕ) : ℤ) := by
      rw [show 2 * n + 1 = (n + 1) + n by ring, Finset.sum_range_add]
    have h1 : ∑ r ∈ Finset.range (n + 1), f r * (r : ℤ) = P := by
      rw [Finset.sum_range_succ']
      simp [hP, h0]
    have hterm : ∀ j ∈ Finset.range n, f (n + 1 + (n - 1 - j)) * ((n + 1 + (n - 1 - j) : ℕ) : ℤ) =
        f (j + 1) * ((j + 1 : ℕ) : ℤ) - N * f (j + 1) := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have e : n + 1 + (n - 1 - j) = 2 * n + 1 - (j + 1) := by omega
      rw [e, hrefl (j + 1) (by omega), Nat.cast_sub (by omega)]
      ring
    have h2 : ∑ x ∈ Finset.range n, f (n + 1 + x) * ((n + 1 + x : ℕ) : ℤ) = P - N * T := by
      calc ∑ x ∈ Finset.range n, f (n + 1 + x) * ((n + 1 + x : ℕ) : ℤ)
          = ∑ j ∈ Finset.range n, f (n + 1 + (n - 1 - j)) * ((n + 1 + (n - 1 - j) : ℕ) : ℤ) :=
            (Finset.sum_range_reflect (fun x => f (n + 1 + x) * ((n + 1 + x : ℕ) : ℤ)) n).symm
        _ = ∑ j ∈ Finset.range n, (f (j + 1) * ((j + 1 : ℕ) : ℤ) - N * f (j + 1)) :=
            Finset.sum_congr rfl hterm
        _ = P - N * T := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hS, hsplit, h1, h2]; ring
  -- (E2) parity
  have E2 : S = 4 * f 2 * P - f 2 * N * T := by
    have hp := sum_range_parity (fun r => f r * (r : ℤ)) n
    simp only [h0, Nat.cast_zero, mul_zero, zero_add] at hp
    have hev : ∑ s ∈ Finset.range n, f (2 * (s + 1)) * ((2 * (s + 1) : ℕ) : ℤ) = 2 * f 2 * P := by
      rw [hP, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [hmul]; push_cast; ring
    have hterm : ∀ j ∈ Finset.range n,
        f (2 * (n - 1 - j) + 1) * ((2 * (n - 1 - j) + 1 : ℕ) : ℤ) =
          f 2 * (2 * (f (j + 1) * ((j + 1 : ℕ) : ℤ))) - f 2 * N * f (j + 1) := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have e : 2 * (n - 1 - j) + 1 = 2 * n + 1 - 2 * (j + 1) := by omega
      rw [e, hrefl (2 * (j + 1)) (by omega), hmul, Nat.cast_sub (by omega)]
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      ring
    have hodd : ∑ s ∈ Finset.range n, f (2 * s + 1) * ((2 * s + 1 : ℕ) : ℤ) =
        2 * f 2 * P - f 2 * N * T := by
      calc ∑ s ∈ Finset.range n, f (2 * s + 1) * ((2 * s + 1 : ℕ) : ℤ)
          = ∑ j ∈ Finset.range n, f (2 * (n - 1 - j) + 1) * ((2 * (n - 1 - j) + 1 : ℕ) : ℤ) :=
            (Finset.sum_range_reflect (fun s => f (2 * s + 1) * ((2 * s + 1 : ℕ) : ℤ)) n).symm
        _ = ∑ j ∈ Finset.range n, (f 2 * (2 * (f (j + 1) * ((j + 1 : ℕ) : ℤ))) - f 2 * N * f (j + 1)) :=
            Finset.sum_congr rfl hterm
        _ = 2 * f 2 * P - f 2 * N * T := by
            have hA : ∑ j ∈ Finset.range n, f 2 * (2 * (f (j + 1) * ((j + 1 : ℕ) : ℤ))) = 2 * f 2 * P := by
              rw [hP, Finset.mul_sum]
              exact Finset.sum_congr rfl (fun j _ => by ring)
            have hB : ∑ j ∈ Finset.range n, f 2 * N * f (j + 1) = f 2 * N * T := by
              rw [hT, Finset.mul_sum]
            rw [Finset.sum_sub_distrib, hA, hB]
    rw [hS, hp, hev, hodd]; ring
  linear_combination (-(f 2)) * E2 + (2 * f 2 * f 2) * E1 - (2 * S + N * T) * hsq

/-- Helper: the elementary identity for an even length $N = 2n$ when $f(r + n) = -f(r)$ and $f(2) = 0$:
$(2 - f(2))\sum_{r<N} f(r)\,r = -N\sum_{s<n} f(s+1)$. Arguments: `N`, `n` with `hN : N = 2 * n`; `f` the function;
`hshift` that $f(r + n) = -f(r)$; `h0` that $f(0) = 0$; `h2` that $f(2) = 0$. -/
theorem elem_even (N n : ℕ) (hN : N = 2 * n) (f : ℕ → ℤ) (hshift : ∀ r, f (r + n) = - f r)
    (h0 : f 0 = 0) (h2 : f 2 = 0) :
    (2 - f 2) * ∑ r ∈ Finset.range N, f r * (r : ℤ) =
      - (N : ℤ) * ∑ s ∈ Finset.range n, f (s + 1) := by
  subst hN
  have hT : ∑ s ∈ Finset.range n, f (s + 1) = ∑ x ∈ Finset.range n, f x := by
    have h1 := Finset.sum_range_succ' f n
    have h3 := Finset.sum_range_succ f n
    have hn : f n = 0 := by
      have := hshift 0
      rw [zero_add, h0] at this
      simpa using this
    rw [h0] at h1
    rw [hn] at h3
    linarith
  rw [hT, h2, show 2 * n = n + n by ring, Finset.sum_range_add]
  have : ∀ x ∈ Finset.range n, f (n + x) * ((n + x : ℕ) : ℤ) = - (f x * (n : ℤ)) - f x * (x : ℤ) := by
    intro x _
    rw [add_comm n x, hshift]
    push_cast
    ring
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul]
  push_cast
  ring

section Elementary

variable {D : ℤ} [IsQuadDisc D]

/-- Helper: `Σ_{1 ≤ r ≤ n} g r = Σ_{s < n} g (s + 1)`. -/
lemma sum_Icc_one_eq_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) (n : ℕ) :
    ∑ r ∈ Finset.Icc 1 n, g r = ∑ s ∈ Finset.range n, g (s + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- Helper: reflection `χ_D(|D| - r) = -χ_D(r)` for `D < 0` and `r ≤ |D|`. -/
theorem kronZ_reflect_neg (hD : D < 0) {r : ℕ} (hr : r ≤ D.natAbs) :
    kronZ D ((D.natAbs - r : ℕ) : ZMod D.natAbs) = - kronZ D (r : ZMod D.natAbs) := by
  rw [Nat.cast_sub hr, ZMod.natCast_self, zero_sub, ← neg_one_mul, kronZ_mul, kronZ_neg_one,
    Int.sign_eq_neg_one_of_neg hD]
  ring

/-- Helper: `χ_D(0) = 0`. -/
theorem kronZ_zero' : kronZ D ((0 : ℕ) : ZMod D.natAbs) = 0 := by
  have h3 := three_le_natAbs (D := D)
  have : NeZero D.natAbs := ⟨by omega⟩
  have : Nontrivial (ZMod D.natAbs) := ZMod.nontrivial_iff.mpr (by omega)
  rw [Nat.cast_zero]
  exact kronZ_nonunit 0 not_isUnit_zero

/-- **Elementary identity behind Example 1** (no analysis): for a fundamental discriminant $D < 0$,
$$(2 - (D/2))\sum_{0<r<|D|}(D/r)\,r = -|D|\sum_{r=1}^{[|D|/2]}(D/r).$$
Both sides are integers; $(D/r)$ is `kronZ D r`. Uses only $\chi_D(-1) = -1$, multiplicativity, and (for even $D$)
$\chi_D(1 + |D|/2) = -1$. Arguments: `D` the fundamental discriminant, `hD : D < 0`. -/
@[kb "cassels1978" "App. B, Ex. 1, p. 389 (the elementary step, polynomial form; unconditional)"]
theorem sum_kronZ_identity (hD : D < 0) :
    (2 - kronZ D (2 : ZMod D.natAbs)) * ∑ r ∈ Finset.Ioo 0 D.natAbs, kronZ D (r : ZMod D.natAbs) * (r : ℤ) =
      - (D.natAbs : ℤ) * ∑ r ∈ Finset.Icc 1 (D.natAbs / 2), kronZ D (r : ZMod D.natAbs) := by
  have h3 := three_le_natAbs (D := D)
  set f : ℕ → ℤ := fun r => kronZ D (r : ZMod D.natAbs) with hf
  have hmul : ∀ a b, f (a * b) = f a * f b := fun a b => by
    simp only [hf]; rw [Nat.cast_mul, kronZ_mul]
  have h0 : f 0 = 0 := kronZ_zero'
  have hrefl : ∀ r, r ≤ D.natAbs → f (D.natAbs - r) = - f r := fun r hr => kronZ_reflect_neg hD hr
  have h2 : kronZ D (2 : ZMod D.natAbs) = f 2 := by simp [hf]
  have hS : ∑ r ∈ Finset.Ioo 0 D.natAbs, kronZ D (r : ZMod D.natAbs) * (r : ℤ) =
      ∑ r ∈ Finset.range D.natAbs, f r * (r : ℤ) := by
    have hr : Finset.range D.natAbs = insert 0 (Finset.Ioo 0 D.natAbs) := by
      ext x; simp; omega
    rw [hr, Finset.sum_insert (by simp)]
    simp [hf]
  have hT : ∑ r ∈ Finset.Icc 1 (D.natAbs / 2), kronZ D (r : ZMod D.natAbs) =
      ∑ s ∈ Finset.range (D.natAbs / 2), f (s + 1) := sum_Icc_one_eq_range f _
  rw [h2, hS, hT]
  by_cases h : D % 4 = 1
  · obtain ⟨n, hn⟩ := natAbs_odd_of_one h
    have hsq : f 2 * f 2 = 1 := by
      have := kronZ_two (D := D)
      rw [← h2]
      rw [this]
      split_ifs <;> norm_num
    have := elem_odd D.natAbs n hn f hrefl hmul h0 hsq
    rw [show D.natAbs / 2 = n by omega]
    exact this
  · have h0' : D % 4 = 0 := by have := (IsQuadDisc.fund (D := D)).1; omega
    obtain ⟨hN, hsqf, hm, hapos⟩ := zero_case_facts h0'
    have hf2 : f 2 = 0 := by
      rw [← h2, kronZ_two]; simp [h]
    have hshift : ∀ r, f (r + 2 * (D / 4).natAbs) = - f r := by
      intro r
      rcases Nat.even_or_odd' r with ⟨k, hk | hk⟩
      · -- even `r = 2k`
        have e1 : f r = 0 := by rw [hk, hmul, hf2, zero_mul]
        have e2 : f (r + 2 * (D / 4).natAbs) = 0 := by
          rw [show r + 2 * (D / 4).natAbs = 2 * (k + (D / 4).natAbs) by omega, hmul, hf2, zero_mul]
        rw [e1, e2]; simp
      · -- odd `r = 2k+1`: `r (1 + 2a) = r + 2a + N k`
        have hkey : r * (1 + 2 * (D / 4).natAbs) = (r + 2 * (D / 4).natAbs) + D.natAbs * k := by
          rw [hN, hk]; ring
        have : f (r + 2 * (D / 4).natAbs) = f (r * (1 + 2 * (D / 4).natAbs)) := by
          simp only [hf]
          rw [hkey]
          congr 1
          rw [Nat.cast_add (r + 2 * (D / 4).natAbs) (D.natAbs * k), Nat.cast_mul D.natAbs k,
            ZMod.natCast_self, zero_mul, add_zero]
        rw [this, hmul]
        have hh := half_shift h0'
        simp only [hf]
        rw [hh]; ring
    have := elem_even D.natAbs (2 * (D / 4).natAbs) (by omega) f hshift h0 hf2
    rw [show D.natAbs / 2 = 2 * (D / 4).natAbs by omega]
    exact this

end Elementary

/-! ### Abel's limit theorem for Dirichlet series -/

section Abel

/-- Helper: the weight $(m+1)^{-t}$ ($m \in \mathbb N$, $t \in \mathbb R$) of a Dirichlet series with the index shifted
by one. -/
noncomputable def abelG (t : ℝ) (m : ℕ) : ℝ := ((m : ℝ) + 1) ^ (-t)

/-- Helper: the Abel weights $(m+1)^{-t} - (m+2)^{-t}$. -/
noncomputable def abelW (t : ℝ) (m : ℕ) : ℝ := abelG t m - abelG t (m + 1)

/-- Helper: $1^{-t} = 1$. -/
lemma abelG_zero (t : ℝ) : abelG t 0 = 1 := by simp [abelG]

/-- Helper: the weights are positive. -/
lemma abelG_pos (t : ℝ) (m : ℕ) : 0 < abelG t m :=
  Real.rpow_pos_of_pos (by positivity) _

/-- Helper: for $t > 0$ the weights are at most $1$. -/
lemma abelG_le_one {t : ℝ} (ht : 0 < t) (m : ℕ) : abelG t m ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]) (by linarith)

/-- Helper: for $t > 0$ the Abel weights are nonnegative (the weights are decreasing in $m$). -/
lemma abelW_nonneg {t : ℝ} (ht : 0 < t) (m : ℕ) : 0 ≤ abelW t m := by
  unfold abelW abelG
  have : ((((m + 1 : ℕ)) : ℝ) + 1) ^ (-t) ≤ ((m : ℝ) + 1) ^ (-t) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith) (by linarith)
  linarith

/-- Helper: the Abel weights telescope, $\sum_{m<n} w_m = 1 - (n+1)^{-t}$. -/
lemma abelW_sum (t : ℝ) (n : ℕ) : ∑ m ∈ Finset.range n, abelW t m = 1 - abelG t n := by
  induction n with
  | zero => simp [abelG_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    unfold abelW
    ring

/-- Helper: the Abel weights sum to at most $1$. -/
lemma abelW_sum_le (t : ℝ) (n : ℕ) : ∑ m ∈ Finset.range n, abelW t m ≤ 1 := by
  rw [abelW_sum]; linarith [abelG_pos t n]

/-- Helper: Abel's summation identity. For $B_k = \sum_{j<k}\beta_j$ and $D_k = B_k - S$,
$\sum_{m \le n}\beta_m\,(m+1)^{-t} - S = \sum_{m<n} D_{m+1} w_m + D_{n+1}(n+1)^{-t}$. -/
lemma abel_identity (β : ℕ → ℂ) (S : ℂ) (t : ℝ) (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), β m * (abelG t m : ℝ) - S =
      ∑ m ∈ Finset.range n, ((∑ j ∈ Finset.range (m + 1), β j) - S) * (abelW t m : ℝ) +
        ((∑ j ∈ Finset.range (n + 1), β j) - S) * (abelG t n : ℝ) := by
  induction n with
  | zero => simp [abelG_zero]
  | succ n ih =>
    simp only [Finset.sum_range_succ] at ih ⊢
    unfold abelW at ih ⊢
    push_cast at ih ⊢
    linear_combination ih

/-- Helper: summability of the weighted series for $t > 0$ when $\|\beta_m\| \le 1/(m+1)$. -/
lemma abel_summable (β : ℕ → ℂ) (hβ : ∀ m, ‖β m‖ ≤ 1 / ((m : ℝ) + 1)) {t : ℝ} (ht : 0 < t) :
    Summable (fun m : ℕ => β m * (abelG t m : ℝ)) := by
  refine Summable.of_norm_bounded (g := fun m : ℕ => ((m : ℝ) + 1) ^ (-(1 + t))) ?_ ?_
  · have h := Real.summable_nat_rpow.mpr (by linarith : -(1 + t) < -1)
    have h2 := (summable_nat_add_iff 1).mpr h
    refine h2.congr (fun n => ?_)
    push_cast
    rfl
  · intro m
    have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (abelG_pos t m)]
    have : ((m : ℝ) + 1) ^ (-(1 + t)) = 1 / ((m : ℝ) + 1) * abelG t m := by
      rw [show -(1 + t) = -1 + -t by ring, Real.rpow_add hpos, Real.rpow_neg_one]
      simp [abelG]
    rw [this]
    exact mul_le_mul_of_nonneg_right (hβ m) (abelG_pos t m).le

/-- Helper: **Abel's limit theorem for Dirichlet series.** If $\sum_{j<n}\beta_j \to S$ as $n \to \infty$ and
$\|\beta_m\| \le 1/(m+1)$, then $\sum_{m \ge 0}\beta_m\,(m+1)^{-t} \to S$ as $t \to 0^+$. (With
$\beta_m = a(m+1)/(m+1)$ this says: if $\sum a(m)/m$ converges, the Dirichlet series $\sum a(m)m^{-s}$ tends to
the sum as $s \to 1^+$.) Proof: Abel's summation identity `abel_identity`, then an $\varepsilon$-argument: the tail
$m \ge M_0$ contributes at most $\varepsilon$ because the weights are nonnegative with sum at most $1$, and the
finitely many terms $m < M_0$ tend to $0$ because each weight $w_m(t) \to 0$ as $t \to 0$. -/
theorem abel_dirichlet (β : ℕ → ℂ) (hβ : ∀ m, ‖β m‖ ≤ 1 / ((m : ℝ) + 1)) (S : ℂ)
    (h : Tendsto (fun n => ∑ j ∈ Finset.range n, β j) atTop (𝓝 S)) :
    Tendsto (fun t : ℝ => ∑' m : ℕ, β m * (abelG t m : ℝ)) (𝓝[>] 0) (𝓝 S) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨M0, hM0⟩ := (Metric.tendsto_atTop.mp h) (ε / 4) (by positivity)
  have hD : ∀ k, M0 ≤ k → ‖(∑ j ∈ Finset.range k, β j) - S‖ ≤ ε / 4 := by
    intro k hk
    have := hM0 k hk
    rw [dist_eq_norm] at this
    exact this.le
  -- the finite sum tends to zero
  have hfin : Tendsto (fun t : ℝ => ∑ m ∈ Finset.range M0,
      ‖(∑ j ∈ Finset.range (m + 1), β j) - S‖ * abelW t m) (𝓝[>] 0) (𝓝 0) := by
    have hw : ∀ m : ℕ, Tendsto (fun t : ℝ => abelW t m) (𝓝[>] 0) (𝓝 0) := by
      intro m
      have hc : Continuous (fun t : ℝ => abelW t m) := by
        unfold abelW abelG
        have hp1 : ((m : ℝ) + 1) ≠ 0 := by positivity
        have hp2 : (((m + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
        exact ((Real.continuous_const_rpow hp1).comp continuous_neg).sub
          ((Real.continuous_const_rpow hp2).comp continuous_neg)
      have h0 : abelW 0 m = 0 := by simp [abelW, abelG]
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      rwa [h0] at this
    have := tendsto_finsetSum (Finset.range M0) (fun m _ =>
      (hw m).const_mul ‖(∑ j ∈ Finset.range (m + 1), β j) - S‖)
    simpa using this
  filter_upwards [(hfin.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4))),
    self_mem_nhdsWithin] with t ht0 htpos
  have htpos : 0 < t := htpos
  show dist (∑' m : ℕ, β m * (abelG t m : ℝ)) S < ε
  rw [dist_eq_norm]
  -- bound the partial sums
  have hpart : ∀ n, M0 ≤ n → ‖∑ m ∈ Finset.range (n + 1), β m * (abelG t m : ℝ) - S‖ ≤
      (∑ m ∈ Finset.range M0, ‖(∑ j ∈ Finset.range (m + 1), β j) - S‖ * abelW t m) + ε / 2 := by
    intro n hn
    rw [abel_identity]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖∑ m ∈ Finset.range n, ((∑ j ∈ Finset.range (m + 1), β j) - S) * (abelW t m : ℝ)‖ ≤
        (∑ m ∈ Finset.range M0, ‖(∑ j ∈ Finset.range (m + 1), β j) - S‖ * abelW t m) + ε / 4 := by
      refine (norm_sum_le _ _).trans ?_
      rw [← Finset.sum_range_add_sum_Ico _ hn]
      have hterm : ∀ m ∈ Finset.range n, ‖((∑ j ∈ Finset.range (m + 1), β j) - S) * (abelW t m : ℝ)‖ =
          ‖(∑ j ∈ Finset.range (m + 1), β j) - S‖ * abelW t m := by
        intro m _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (abelW_nonneg htpos m)]
      have hterm' : ∀ m ∈ Finset.range M0, ‖((∑ j ∈ Finset.range (m + 1), β j) - S) * (abelW t m : ℝ)‖ =
          ‖(∑ j ∈ Finset.range (m + 1), β j) - S‖ * abelW t m :=
        fun m hm => hterm m (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hm) hn))
      rw [Finset.sum_congr rfl hterm']
      gcongr
      calc ∑ m ∈ Finset.Ico M0 n, ‖((∑ j ∈ Finset.range (m + 1), β j) - S) * (abelW t m : ℝ)‖
          ≤ ∑ m ∈ Finset.Ico M0 n, (ε / 4) * abelW t m := by
            refine Finset.sum_le_sum (fun m hm => ?_)
            have hm' := Finset.mem_Ico.mp hm
            rw [hterm m (Finset.mem_range.mpr hm'.2)]
            exact mul_le_mul_of_nonneg_right (hD (m + 1) (by omega)) (abelW_nonneg htpos m)
        _ = (ε / 4) * ∑ m ∈ Finset.Ico M0 n, abelW t m := by rw [Finset.mul_sum]
        _ ≤ (ε / 4) * 1 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            refine le_trans ?_ (abelW_sum_le t n)
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (fun m hm => Finset.mem_range.mpr (Finset.mem_Ico.mp hm).2)
              (fun m _ _ => abelW_nonneg htpos m)
        _ = ε / 4 := by ring
    have h2 : ‖((∑ j ∈ Finset.range (n + 1), β j) - S) * (abelG t n : ℝ)‖ ≤ ε / 4 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (abelG_pos t n)]
      calc ‖(∑ j ∈ Finset.range (n + 1), β j) - S‖ * abelG t n ≤ (ε / 4) * 1 :=
            mul_le_mul (hD (n + 1) (by omega)) (abelG_le_one htpos n) (abelG_pos t n).le (by positivity)
        _ = ε / 4 := by ring
    linarith
  have hlim : Tendsto (fun n : ℕ => ∑ m ∈ Finset.range (n + 1), β m * (abelG t m : ℝ) - S) atTop
      (𝓝 ((∑' m : ℕ, β m * (abelG t m : ℝ)) - S)) := by
    have h1 := (abel_summable β hβ htpos).hasSum.tendsto_sum_nat
    have h2 := (tendsto_add_atTop_iff_nat 1).mpr h1
    exact h2.sub_const S
  have := le_of_tendsto (hlim.norm) (eventually_atTop.mpr ⟨M0, hpart⟩)
  linarith

end Abel

/-! ### From the partial sums of $\sum \chi_D(m)/m$ to $L(1, \chi_D)$ -/

section Bridge

variable {D : ℤ} [IsQuadDisc D]

/-- Helper: the coefficient $\beta_m = \chi_D(m+1)/(m+1)$ of the series $\sum_{m \ge 1}\chi_D(m)/m$, indexed from
$m = 0$ (the shift of $m \ge 1$ by one). -/
noncomputable def kronCoeff (D : ℤ) [IsQuadDisc D] (m : ℕ) : ℂ :=
  kroneckerChar D ((m + 1 : ℕ) : ZMod D.natAbs) / ((m : ℂ) + 1)

/-- Helper: $|\chi_D(x)| \le 1$ (the values are $0, \pm 1$). -/
lemma kroneckerChar_norm_le_one (x : ZMod D.natAbs) : ‖kroneckerChar D x‖ ≤ 1 := by
  by_cases hx : IsUnit x
  · have h : IsUnit (kronZ D x) := hx.map (kronMulChar D)
    rcases Int.isUnit_iff.mp h with h | h <;> simp [kroneckerChar_apply, h]
  · rw [kroneckerChar_apply, kronZ_nonunit x hx]; simp

/-- Helper: $\|\beta_m\| \le 1/(m+1)$. -/
lemma kronCoeff_norm_le (m : ℕ) : ‖kronCoeff D m‖ ≤ 1 / ((m : ℝ) + 1) := by
  unfold kronCoeff
  rw [norm_div, show ((m : ℂ) + 1) = (((m + 1 : ℕ)) : ℂ) by push_cast; ring, Complex.norm_natCast]
  push_cast
  exact div_le_div_of_nonneg_right (kroneckerChar_norm_le_one _) (by positivity)

/-- Helper: the partial sums of $\beta$ are those of $\sum_{m \ge 1}\chi_D(m)/m$. -/
lemma kronCoeff_partial (n : ℕ) :
    ∑ j ∈ Finset.range n, kronCoeff D j =
      ∑ m ∈ Finset.Icc 1 n, kroneckerChar D (m : ZMod D.natAbs) / (m : ℂ) := by
  rw [sum_Icc_one_eq_range]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold kronCoeff
  push_cast
  rfl

/-- Helper: for real $s > 1$ the $L$-series $\sum_n \chi_D(n)n^{-s}$ is the Dirichlet series $\sum_m \beta_m (m+1)^{-(s-1)}$
of Abel's theorem. -/
lemma LSeries_kronecker_eq_abel {s : ℝ} (hs : 1 < s) :
    LSeries (fun n : ℕ => kroneckerChar D n) (s : ℂ) =
      ∑' m : ℕ, kronCoeff D m * (abelG (s - 1) m : ℝ) := by
  have hterm : ∀ m : ℕ, LSeries.term (fun n : ℕ => kroneckerChar D n) (s : ℂ) (m + 1) =
      kronCoeff D m * (abelG (s - 1) m : ℝ) := by
    intro m
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero m)]
    unfold kronCoeff abelG
    have hx : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hxc : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast hx.ne'
    have e1 : (((m + 1 : ℕ)) : ℂ) ^ (s : ℂ) = ((m : ℂ) + 1) * ((((m : ℝ) + 1) ^ (s - 1) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hx.le]
      push_cast
      rw [show (s : ℂ) = 1 + ((s : ℂ) - 1) by ring, Complex.cpow_add _ _ hxc, Complex.cpow_one]
      ring_nf
    have hy : (0 : ℝ) < ((m : ℝ) + 1) ^ (s - 1) := Real.rpow_pos_of_pos hx _
    have hyc : ((((m : ℝ) + 1) ^ (s - 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    rw [e1, Real.rpow_neg hx.le, Complex.ofReal_inv]
    push_cast
    field_simp
  have hsum : Summable (fun m : ℕ => LSeries.term (fun n : ℕ => kroneckerChar D n) (s : ℂ) (m + 1)) :=
    (abel_summable (kronCoeff D) kronCoeff_norm_le (by linarith : 0 < s - 1)).congr (fun m => (hterm m).symm)
  rw [LSeries, tsum_eq_zero_add' hsum, LSeries.term_zero, zero_add]
  exact tsum_congr hterm

/-- Helper: if the partial sums of $\sum_{m \ge 1}\chi_D(m)/m$ converge to $V$, then $L(s, \chi_D) \to V$ as $s \to 1^+$
(Abel's limit theorem). -/
theorem tendsto_LSeries_of_partial_sums (V : ℂ)
    (h : Tendsto (fun K : ℕ => ∑ m ∈ Finset.Icc 1 K, kroneckerChar D (m : ZMod D.natAbs) / (m : ℂ)) atTop (𝓝 V)) :
    Tendsto (fun s : ℝ => LSeries (fun n : ℕ => kroneckerChar D n) (s : ℂ)) (𝓝[>] 1) (𝓝 V) := by
  have h' : Tendsto (fun n => ∑ j ∈ Finset.range n, kronCoeff D j) atTop (𝓝 V) := by
    simpa [kronCoeff_partial] using h
  have hab := abel_dirichlet (kronCoeff D) kronCoeff_norm_le V h'
  have hmap : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous (fun s : ℝ => s - 1) := by fun_prop
      have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with s hs
      show 0 < s - 1
      exact sub_pos.mpr (Set.mem_Ioi.mp hs)
  refine (hab.comp hmap).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (LSeries_kronecker_eq_abel hs).symm

end Bridge

section Thm21

open NumberField

variable {D : ℤ} [IsQuadDisc D]

/-- Helper: the number of roots of unity $w$ of $\mathbb Q(\sqrt D)$ ($D < 0$) is the book's $w$ =
`properAutomorphCount D`. -/
lemma torsionOrder_cast (hD : D < 0) :
    ((NumberField.Units.torsionOrder (QField D) : ℕ) : ℝ) = (properAutomorphCount D : ℝ) := by
  have h := torsionOrder_of_neg hD
  have h' : NumberField.Units.torsionOrder (QField D) = properAutomorphCount D := by
    rw [h]; unfold properAutomorphCount; split_ifs <;> rfl
  rw [h']

/-- **Cassels, Appendix B, Theorem 2.1 (i), finite-sum form (p. 371), for $D < 0$, conditional on the Gauss sum (2.20).**
For a fundamental discriminant $D < 0$,
$$2\,|D|\,h(D) = -\,w\sum_{0<r<|D|}(D/r)\,r,$$
with $h(D)$ = `classNumber (QField D)` (the number of classes of primitive positive definite forms of discriminant $D$,
`Binary.card_slClasses`), $w$ = `properAutomorphCount D` $= 6, 4, 2$ for $D = -3$, $-4$, otherwise, and $(D/r)$ the
Kronecker symbol `kronZ D r`. Arguments: `D` the fundamental discriminant (`IsQuadDisc D`), `G` the Gauss sum (2.20)
(`KroneckerGaussSum D`, the named input, as in `lemma_2_3_neg`), `hD : D < 0`. The sum runs over $r = 1, \dots, |D| - 1$.

*Erratum (see `lemma_2_3_neg`):* the minus sign on the right is not in the machine-read text of the book; with it the
statement is true (for $D = -4$: $8 = -4\cdot(-2)$).

Proof: the series $\sum_m (D/m)/m$ has the value $-\pi|D|^{-3/2}\sum_{0<r<|D|}(D/r)r$ (`lemma_2_3_neg`), and also
the value $L(1, \chi_D)$ (Abel's limit theorem, `tendsto_LSeries_of_partial_sums`, and the limit of the $L$-series as
$s \to 1^+$), which is $2\pi h/(w\sqrt{|D|})$ (`classNumberFormula_neg`). -/
@[kb "cassels1978" "App. B, Thm. 2.1 (i), p. 371 (finite-sum form; conditional on the Gauss sum (2.20))"]
theorem finite_sum_class_number_neg (G : KroneckerGaussSum D) (hD : D < 0) :
    2 * (D.natAbs : ℝ) * (NumberField.classNumber (QField D) : ℝ) =
      -(properAutomorphCount D : ℝ) * ∑ r ∈ Finset.Ioo 0 D.natAbs,
        (kronZ D (r : ZMod D.natAbs) : ℝ) * (r : ℝ) := by
  have h1 := lemma_2_3_neg G hD
  set V : ℝ := -Real.pi / |(D : ℝ)| ^ (3 / 2 : ℝ) * ∑ r ∈ Finset.Ioo 0 D.natAbs,
    (kronZ D (r : ZMod D.natAbs) : ℝ) * (r : ℝ) with hV
  have hc : Tendsto (fun K : ℕ => ∑ m ∈ Finset.Icc 1 K, kroneckerChar D (m : ZMod D.natAbs) / (m : ℂ))
      atTop (𝓝 (V : ℂ)) := by
    have := (Complex.continuous_ofReal.tendsto V).comp h1
    refine this.congr (fun K => ?_)
    exact lemma23_series_cast K
  have h2 := tendsto_nhds_unique tendsto_LSeries_kronecker (tendsto_LSeries_of_partial_sums (V : ℂ) hc)
  have h3 := classNumberFormula_neg hD
  rw [LFunction_kronecker_one] at h3
  have h4 : ((V : ℝ) : ℂ) = ((2 * Real.pi * NumberField.classNumber (QField D) /
      (((NumberField.Units.torsionOrder (QField D) : ℕ) : ℝ) * Real.sqrt |(D : ℝ)|) : ℝ) : ℂ) := by
    rw [← h2]; exact h3
  have h5 := Complex.ofReal_injective h4
  rw [torsionOrder_cast hD] at h5
  have hNpos : (0 : ℝ) < |(D : ℝ)| := by
    rw [abs_pos]; intro h; have := three_le_natAbs (D := D); simp at h; omega
  have hNR : (D.natAbs : ℝ) = |(D : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hsq : 0 < Real.sqrt |(D : ℝ)| := Real.sqrt_pos.mpr hNpos
  have hw : (0 : ℝ) < (properAutomorphCount D : ℝ) := by
    unfold properAutomorphCount; split_ifs <;> norm_num
  have h32 : |(D : ℝ)| ^ (3 / 2 : ℝ) = |(D : ℝ)| * Real.sqrt |(D : ℝ)| := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hNpos, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hV, h32] at h5
  rw [hNR]
  set Sr := ∑ r ∈ Finset.Ioo 0 D.natAbs, (kronZ D (r : ZMod D.natAbs) : ℝ) * (r : ℝ)
  set w : ℝ := (properAutomorphCount D : ℝ)
  set h : ℝ := (NumberField.classNumber (QField D) : ℝ)
  set N : ℝ := |(D : ℝ)|
  set q : ℝ := Real.sqrt N
  have hpi := Real.pi_pos
  field_simp at h5
  nlinarith [h5, hpi]

end Thm21

/-! ### Example 4: the Gauss sum of $(D/\cdot)$ -/

section Ex4

variable {D : ℤ} [IsQuadDisc D]

/-- **Cassels, Appendix B, Example 4 (p. 389), squared form.** For a fundamental discriminant $D$ (`IsQuadDisc D`),
the Gauss sum $g = \sum_{r \bmod |D|}(D/r)\,e(r/|D|)$, $e(x) = e^{2\pi i x}$, satisfies $g^2 = D$. Here $(D/r)$ is
the Kronecker character `kroneckerChar D` and the sum is over the residues $r = 0, \dots, |D|-1$ (the terms with $r$
not prime to $D$ vanish). Argument: `D` the fundamental discriminant. Equivalent to $g = \pm\sqrt D$ ($D > 0$) and
$g = \pm i\sqrt{|D|}$ ($D < 0$): see `kroneckerGauss_eq_pm_sqrt`. Unconditional.

*Proof* (not the book's hint, which reduces by Example 2 to prime discriminants and uses Example 3): the character
$\chi_D$ is primitive of conductor $|D|$ (`kroneckerChar_isPrimitive`: for each prime $q \mid D$ an explicit unit
$u \equiv 1 \bmod |D|/q$ with $\chi_D(u) = -1$, by quadratic reciprocity for the Jacobi symbol), so Mathlib's
`gaussSum_mulShift_of_isPrimitive` gives $\sum_{a \bmod |D|}|g(\chi_D, e_a)|^2 = \varphi(|D|)\,|g|^2$, while
Parseval gives $|D|\varphi(|D|)$; hence $|g|^2 = |D|$. As $\chi_D$ is real, $\bar g = \chi_D(-1)\,g$, and
$\chi_D(-1) = \operatorname{sign} D$ (`kronZ_neg_one`), so $g^2 = \operatorname{sign}(D)|D| = D$. -/
@[kb "cassels1978" "App. B, Ex. 4, p. 389 (the Gauss sum of (D/·) is ±√D)"]
theorem kroneckerGauss_sq :
    (∑ r ∈ Finset.range D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
      Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) / (D.natAbs : ℂ))) ^ 2 = (D : ℂ) := by
  have : NeZero D.natAbs := ⟨by have := three_le_natAbs (D := D); omega⟩
  rw [← gaussSum_kroneckerChar_eq_range]
  exact gaussSum_kroneckerChar_sq

/-- **Cassels, Appendix B, Example 4 (p. 389), as printed.** The Gauss sum $g = \sum_{r \bmod |D|}(D/r)\,e(r/|D|)$ of a
fundamental discriminant $D$ is $\pm\sqrt D$ if $D > 0$ and $\pm i\sqrt{|D|}$ if $D < 0$. Arguments: `D` the
fundamental discriminant; the sum is as in `kroneckerGauss_sq`. This is (2.20) at $m = 1$ except for the sign
(`kroneckerGauss_eq_pm_gaussConst`). Unconditional; the sign is Gauss's theorem and is *not* determined here. -/
@[kb "cassels1978" "App. B, Ex. 4, p. 389 (the Gauss sum of (D/·) is ±√D, ±i√|D|)"]
theorem kroneckerGauss_eq_pm_sqrt :
    (0 < D →
      (∑ r ∈ Finset.range D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
          Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) / (D.natAbs : ℂ)) = (Real.sqrt (D : ℝ) : ℂ) ∨
        ∑ r ∈ Finset.range D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
          Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) / (D.natAbs : ℂ)) = -(Real.sqrt (D : ℝ) : ℂ))) ∧
    (D < 0 →
      (∑ r ∈ Finset.range D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
          Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) / (D.natAbs : ℂ)) =
            (Real.sqrt |(D : ℝ)| : ℂ) * Complex.I ∨
        ∑ r ∈ Finset.range D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
          Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) / (D.natAbs : ℂ)) =
            -((Real.sqrt |(D : ℝ)| : ℂ) * Complex.I))) := by
  have hsq := kroneckerGauss_sq (D := D)
  set g := ∑ r ∈ Finset.range D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
    Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) / (D.natAbs : ℂ)) with hg
  refine ⟨fun hD => ?_, fun hD => ?_⟩
  · have h : ((Real.sqrt (D : ℝ) : ℝ) : ℂ) ^ 2 = (D : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by exact_mod_cast hD.le)]
      simp
    exact sq_eq_sq_iff_eq_or_eq_neg.mp (hsq.trans h.symm)
  · have hNpos : (0 : ℝ) ≤ |(D : ℝ)| := abs_nonneg _
    have h : (((Real.sqrt |(D : ℝ)| : ℝ) : ℂ) * Complex.I) ^ 2 = (D : ℂ) := by
      rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt hNpos, Complex.I_sq,
        abs_of_neg (by exact_mod_cast hD)]
      simp
    exact sq_eq_sq_iff_eq_or_eq_neg.mp (hsq.trans h.symm)

/-- **Example 4 in terms of the constant of (2.20).** The Gauss sum $g = \sum_{r \bmod |D|}(D/r)\,e(r/|D|)$ equals
$\pm$ `gaussConst D`, where `gaussConst D` is $\sqrt D$ ($D > 0$) or $i\sqrt{|D|}$ ($D < 0$), the constant on the right
of Cassels' (2.20). Thus (2.20) at $m = 1$ holds up to the sign. Argument: `D` the fundamental discriminant. -/
@[kb "cassels1978" "App. B, Ex. 4, p. 389 (the Gauss sum is ± the constant of (2.20), i.e. (2.20) at m = 1 up to sign)"]
theorem kroneckerGauss_eq_pm_gaussConst :
    (∑ r ∈ Finset.range D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) / (D.natAbs : ℂ))) = gaussConst D ∨
      (∑ r ∈ Finset.range D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) / (D.natAbs : ℂ))) = -gaussConst D := by
  have h := kroneckerGauss_eq_pm_sqrt (D := D)
  by_cases hD : 0 < D
  · have hc : gaussConst D = (Real.sqrt |(D : ℝ)| : ℝ) := by simp [gaussConst, hD]
    rw [hc, abs_of_pos (by exact_mod_cast hD)]
    exact h.1 hD
  · have hD' : D < 0 := by
      rcases lt_trichotomy D 0 with h1 | h1 | h1
      · exact h1
      · exfalso; have := three_le_natAbs (D := D); rw [h1] at this; simp at this
      · exact absurd h1 hD
    have hc : gaussConst D = (Real.sqrt |(D : ℝ)| : ℝ) * Complex.I := by simp [gaussConst, hD]
    rw [hc]
    exact h.2 hD'

/-- **The Gauss sum (2.20) of Cassels is equivalent to its sign.** If the Gauss sum $g = \sum_{r \bmod |D|}(D/r)e(r/|D|)$
equals `gaussConst D` (the sign in Example 4 is $+$), then the full statement `KroneckerGaussSum D` (all $m \in \mathbb Z$)
holds. (By `kroneckerGauss_eq_pm_gaussConst` the sum is $\pm$ `gaussConst D`, so what remains of (2.20) is the sign, Gauss's
theorem; the dependence on $m$ is proved from primitivity of $\chi_D$.) Argument: `hsign` the displayed equality at
$m = 1$. -/
@[kb "cassels1978" "App. B, §2, (2.20), p. 374 (the named statement KroneckerGaussSum reduces to the sign of the Gauss sum)"]
theorem kroneckerGaussSum_of_sign
    (hsign : (∑ r ∈ Finset.range D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) / (D.natAbs : ℂ))) = gaussConst D) :
    KroneckerGaussSum D := by
  have : NeZero D.natAbs := ⟨by have := three_le_natAbs (D := D); omega⟩
  refine ⟨fun m => ?_⟩
  have hprim := kroneckerChar_isPrimitive (D := D)
  have h1 := gaussSum_mulShift_of_isPrimitive (ZMod.stdAddChar : AddChar (ZMod D.natAbs) ℂ) hprim (m : ZMod D.natAbs)
  have hinv := real_char_inv (kroneckerChar D) kroneckerChar_sq_unit
  rw [hinv, gaussSum_kroneckerChar_eq_range, hsign] at h1
  rw [← h1]
  unfold gaussSum
  refine Finset.sum_nbij' (fun r => (r : ZMod D.natAbs)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · intro r _; simp
  · intro x _; simpa using ZMod.val_lt x
  · intro r hr; simpa using ZMod.val_natCast_of_lt (Finset.mem_range.mp hr)
  · intro x _; simp
  · intro r _
    have e1 : (ZMod.stdAddChar : AddChar (ZMod D.natAbs) ℂ).mulShift (m : ZMod D.natAbs) (r : ZMod D.natAbs) =
        Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * (m : ℂ)) / (D.natAbs : ℂ)) := by
      rw [AddChar.mulShift_apply]
      have := ZMod.stdAddChar_coe (N := D.natAbs) ((m : ℤ) * (r : ℤ))
      push_cast at this
      rw [this]
      congr 2
      ring
    rw [e1]

end Ex4

/-! ### Example 1: the class number as a sum over $r \le |D|/2$ -/

section Ex1

variable {D : ℤ} [IsQuadDisc D]

/-- Helper: $(D/2) \in \{-1, 0, 1\}$. -/
lemma kronZ_two_cases : kronZ D (2 : ZMod D.natAbs) = 1 ∨ kronZ D (2 : ZMod D.natAbs) = 0 ∨
    kronZ D (2 : ZMod D.natAbs) = -1 := by
  rw [kronZ_two]
  split_ifs <;> simp

/-- **The elementary identity of Example 1, division form (unconditional).** For a fundamental discriminant $D < 0$,
$$\sum_{0<r<|D|}(D/r)\,r = -\frac{|D|}{2 - (D/2)}\sum_{r=1}^{[|D|/2]}(D/r),$$
an identity of rational numbers ($2 - (D/2) \in \{1, 2, 3\}$ is never $0$). Here $(D/r)$ is `kronZ D r` and $(D/2)$ is
`kronZ D 2` ($1, -1, 0$ as $D \equiv 1, 5 \pmod 8$, $D$ even). Arguments: `D` the fundamental discriminant, `hD : D < 0`.
It uses only $\chi_D(-1) = -1$, multiplicativity of $\chi_D$ and, for even $D$, $\chi_D(1 + |D|/2) = -1$
(`sum_kronZ_identity`, the polynomial form). Checked numerically for all fundamental $-400 < D < 0$. -/
@[kb "cassels1978" "App. B, Ex. 1, p. 389 (the elementary step, division form; unconditional)"]
theorem sum_kronZ_eq_div (hD : D < 0) :
    ∑ r ∈ Finset.Ioo 0 D.natAbs, (kronZ D (r : ZMod D.natAbs) : ℚ) * (r : ℚ) =
      -(D.natAbs : ℚ) / (2 - (kronZ D (2 : ZMod D.natAbs) : ℚ)) *
        ∑ r ∈ Finset.Icc 1 (D.natAbs / 2), (kronZ D (r : ZMod D.natAbs) : ℚ) := by
  have h := sum_kronZ_identity hD
  have hne : (2 - (kronZ D (2 : ZMod D.natAbs) : ℚ)) ≠ 0 := by
    rcases kronZ_two_cases (D := D) with h | h | h <;> rw [h] <;> norm_num
  have h' : (2 - (kronZ D (2 : ZMod D.natAbs) : ℚ)) *
      ∑ r ∈ Finset.Ioo 0 D.natAbs, (kronZ D (r : ZMod D.natAbs) : ℚ) * (r : ℚ) =
      -(D.natAbs : ℚ) * ∑ r ∈ Finset.Icc 1 (D.natAbs / 2), (kronZ D (r : ZMod D.natAbs) : ℚ) := by
    exact_mod_cast h
  rw [div_mul_eq_mul_div, eq_div_iff hne, mul_comm]
  exact h'

/-- **Cassels, Appendix B, Example 1 (p. 389), conditional on the Gauss sum (2.20).** For a fundamental discriminant
$D < 0$,
$$2\,\bigl(2 - (D/2)\bigr)\,h(D) = w\sum_{r=1}^{[|D|/2]}(D/r),$$
in the notation of Theorem 2.1: $h(D)$ = `classNumber (QField D)` (the number of classes of primitive positive definite
forms of discriminant $D$), $w$ = `properAutomorphCount D` $= 6, 4, 2$ for $D = -3$, $-4$, otherwise, $(D/r)$ the Kronecker
symbol `kronZ D r` and $(D/2)$ = `kronZ D 2`. Arguments: `D` the fundamental discriminant (`IsQuadDisc D`), `G` the
Gauss sum (2.20) (`KroneckerGaussSum D`, a **named input**: the library does not prove (2.20), whose sign is Gauss's
theorem; see `kroneckerGaussSum_of_sign`), `hD : D < 0`. An identity of integers.

Proof: Theorem 2.1 (i) in finite-sum form (`finite_sum_class_number_neg`, which is conditional on `G`) and the
unconditional elementary identity `sum_kronZ_identity`. -/
@[kb "cassels1978" "App. B, Ex. 1, p. 389 (conditional on the Gauss sum (2.20))"]
theorem class_number_half_sum (G : KroneckerGaussSum D) (hD : D < 0) :
    2 * (2 - kronZ D (2 : ZMod D.natAbs)) * (NumberField.classNumber (QField D) : ℤ) =
      (properAutomorphCount D : ℤ) *
        ∑ r ∈ Finset.Icc 1 (D.natAbs / 2), kronZ D (r : ZMod D.natAbs) := by
  have h1 := finite_sum_class_number_neg G hD
  have h2 := sum_kronZ_identity hD
  have h1' : 2 * (D.natAbs : ℤ) * (NumberField.classNumber (QField D) : ℤ) =
      -(properAutomorphCount D : ℤ) * ∑ r ∈ Finset.Ioo 0 D.natAbs,
        kronZ D (r : ZMod D.natAbs) * (r : ℤ) := by
    have h : ((2 * (D.natAbs : ℤ) * (NumberField.classNumber (QField D) : ℤ) : ℤ) : ℝ) =
        ((-(properAutomorphCount D : ℤ) * ∑ r ∈ Finset.Ioo 0 D.natAbs,
          kronZ D (r : ZMod D.natAbs) * (r : ℤ) : ℤ) : ℝ) := by
      push_cast
      rw [Nat.cast_natAbs, Int.cast_abs] at h1
      exact h1
    exact Int.cast_injective h
  have hN : (D.natAbs : ℤ) ≠ 0 := by
    have := three_le_natAbs (D := D); omega
  refine mul_left_cancel₀ hN ?_
  linear_combination (2 - kronZ D (2 : ZMod D.natAbs)) * h1' - (properAutomorphCount D : ℤ) * h2

end Ex1

end QuadFormsKB.Cassels
