/-
# Cassels, Chapter 11, §7 and §9: where Theorem 1.6 and Theorem 7.1 fail

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11: p. 228 (the forms (7.4), due to Watson),
p. 235 (Theorem 1.6 fails for $n = 3$ and, without "primitively", for $n = 4$; example (9.1)), p. 252 (Example 6).

**Conventions.** Indices are 0-based (`Fin n`, variables $x_0, \dots, x_{n-1}$); Cassels' $x_1, \dots, x_n$ are
$x_0, \dots, x_{n-1}$ here. $Q$ denotes a form. A vector over $\mathbb Z$ is primitive when the greatest common divisor
of its coordinates is $1$ (`PrimRepZ`), a vector over $\mathbb Z_p$ when some coordinate is a unit (`PrimRepZp`).

**What is formalized.**
* `tartakowskyFailsAtThree_holds`: Theorem 1.6 fails for $n = 3$, *proved* unconditionally with the form
  $Q = x_0^2 + x_1^2 + 16x_2^2$ of Example 6 and the numbers $m^2$, $m \equiv 3 \pmod 4$. (Cassels deduces this from
  Lemma 7.1 and Note 2 to Theorem 7.1; the Example 6 route needs only elementary congruences and Chapter 9,
  Theorem 5.1, via `Ch11Ex4.ex6_genus_primRep`.) The local half goes through the genus: a form $Q'$ of the genus of $Q$
  primitively represents $m^2$ over $\mathbb Z$, hence over each $\mathbb Z_p$, and $Q \sim Q'$ over $\mathbb Z_p$
  (`primRepZp_of_sameGenus`).
* `tartakowskyUnprimitiveFailsAtFour_holds`: Theorem 1.6 fails for $n = 4$ without "primitively", *proved* with the
  form $x_0^2 + x_1^2 + 13(x_2^2 + x_3^2)$ and the numbers $3 \cdot 4^m$; see the erratum below.
* `ex7_primRep_four`: (7.4): $f_2$ represents $4$ primitively over $\mathbb Z$ and $f_1$ does not (unconditional);
  `theorem71_fails_ternary`: Theorem 7.1 fails for $n = 3$, conditional on the named statement `Ch11Ex4.Ex7Classes`
  (only its field `sameGenus` is used).

*Erratum (example (9.1), p. 235).* The printed form is $f_0 = x_1^2 + x_2^2 + 5(x_3^3 + x_4^2)$; the exponent in $x_3^3$ is
a misprint for $x_3^2$ (the form is quadratic and the argument uses $5(a_3^2 + a_4^2)$). Moreover, even with this
correction, the claim "for $m > 0$ the number $3 \cdot 2^{2m}$ is not represented over $\mathbb Z$" is false: the
descent "all $a_i$ are even" fails at $m = 1$, because $f_0(1,1,1,1) = 12 = 3 \cdot 4$ (all $a_i$ odd gives
$f_0 \equiv 1 + 1 + 5 + 5 \equiv 4 \pmod 8$, which is the residue of $12$); hence $f_0(2^{m-1}, \dots, 2^{m-1}) = 3 \cdot 4^m$
for every $m \ge 1$ (`cassels91Printed_represents`). Numerically $3$ is the only positive integer not represented by
$f_0$ (checked up to $400$), so the printed form cannot give infinitely many counterexamples. *Correction:* replace $5$
by $13$: for $f = x_0^2 + x_1^2 + 13(x_2^2 + x_3^2)$ the same argument works ($13 \equiv 5 \pmod 8$, so the all-odd case
gives $\equiv 4 \pmod 8$, which occurs only for $m = 1$, where the value $12 < 28 = f(\pm 1, \pm 1, \pm 1, \pm 1)$ excludes
it), and $3 \cdot 4^m$ is represented over every $\mathbb Z_p$ for every $m \ge 0$ (the vector
$(1, 1, 2/13, 3/13)$ for $p \ne 13$, using $13 = 2^2 + 3^2$, and $(w, 0, 0, 0)$ with $w^2 = 3$ for $p = 13$, since $3$ is
a square modulo $13$), and the form is anisotropic over $\mathbb Q_2$ since $-13 \equiv 3 \pmod 4$. Numerically
$3, 12, 48, 192, \dots$ are not represented by $f$ (checked up to $800$).
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec9
import QuadFormsKB.Literature.Cassels.Ch11Examples4

open Matrix QuadFormsKB.Siegel QuadFormsKB.Cassels QuadFormsKB.Cassels.Ch11Ex4

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11Failures

/-! ### Transfer of primitive representations along the genus -/

/-- **Helper: an integral primitive representation gives a $p$-adic one.** If $\gcd(x) = 1$ and $Q(x) = a$ over
$\mathbb Z$, then the image of $x$ in $\mathbb Z_p^n$ has a unit coordinate and $Q(x) = a$ there. Arguments: `p` the
prime, `Q` the form, `a` the represented integer, `h` the primitive representation over $\mathbb Z$. -/
theorem primRepZp_of_primRepZ {n : ℕ} (p : ℕ) [Fact p.Prime] {Q : QuadForm ℤ n} {a : ℤ} (h : PrimRepZ Q a) :
    PrimRepZp p Q a := by
  obtain ⟨x, hx, hxa⟩ := h
  rw [primRepZp_iff]
  refine ⟨fun i => Int.castRingHom ℤ_[p] (x i), ?_, ?_⟩
  · by_contra hne
    push Not at hne
    have hd : ∀ i, (p : ℤ) ∣ x i := fun i => by
      by_contra hd
      exact hne i (by simpa using (isUnit_intCast_padic (p := p) (x i)).mpr hd)
    have h1 : (p : ℤ) ∣ Finset.univ.gcd x := Finset.dvd_gcd fun i _ => hd i
    rw [hx] at h1
    have h2 := Int.eq_one_of_dvd_one (by positivity) h1
    have h3 := (Fact.out : p.Prime).one_lt
    omega
  · rw [← map_eval_eq, hxa]
    simp

/-- **Helper: equivalence over $\mathbb Z_p$ transfers primitive representations.** If $Q$ and $Q'$ are in the same genus
(in particular equivalent over $\mathbb Z_p$) and $Q'$ primitively represents $a$ over $\mathbb Z$, then $Q$
primitively represents $a$ over $\mathbb Z_p$. Arguments: `p` the prime, `h` that $Q$, $Q'$ are in the same genus, `hQ'`
the primitive representation of `a` by $Q'$ over $\mathbb Z$. -/
theorem primRepZp_of_sameGenus {n : ℕ} (p : ℕ) [Fact p.Prime] {Q Q' : QuadForm ℤ n} (h : SameGenus Q Q') {a : ℤ}
    (hQ' : PrimRepZ Q' a) : PrimRepZp p Q a := by
  obtain ⟨g, hg⟩ := h.1 p
  have h1 := primRepZp_of_primRepZ p hQ'
  rw [primRepZp_iff] at h1 ⊢
  obtain ⟨y, hy, hya⟩ := h1
  refine ⟨g.val *ᵥ y, exists_unit_mulVec p (N := (g⁻¹).val) (Units.inv_mul g) hy, ?_⟩
  rw [hg, hya]

/-! ### Theorem 1.6 fails for $n = 3$ -/

/-- **Helper: $x_0^2 + x_1^2 + 16x_2^2$ is positive definite** in the sense of `IntQF.PosDef`. -/
theorem posDef_ex6f : IntQF.PosDef ex6f := by
  intro x hx
  rw [eval_ex6f]
  by_contra hle
  push Not at hle
  have h0 : x 0 ^ 2 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  have h1 : x 1 ^ 2 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  have h2 : x 2 ^ 2 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  apply hx
  funext i
  fin_cases i
  · exact pow_eq_zero_iff (two_ne_zero) |>.mp h0
  · exact pow_eq_zero_iff (two_ne_zero) |>.mp h1
  · exact pow_eq_zero_iff (two_ne_zero) |>.mp h2

/-- **Theorem 1.6 fails for $n = 3$** (Cassels, Ch. 11, p. 235; also Ch. 11, (7.4), p. 228), proved. The positive
definite form $Q = x_0^2 + x_1^2 + 16x_2^2$ (`ex6f`, Example 6, p. 252) has the property that for every $N$ there is an
integer $a = m^2 \ge N$ ($m \equiv 3 \pmod 4$) primitively represented by $Q$ over every $\mathbb Z_p$ but not over
$\mathbb Z$. *Proof.* Not over $\mathbb Z$: a primitive representation of an odd square $m^2$ forces $m \equiv 1 \pmod 4$
(`ex6f_mod_four`). Over $\mathbb Z_p$: by Chapter 9, Theorem 5.1 (`ex6_genus_primRep`) some form of the genus of $Q$
primitively represents $m^2$ over $\mathbb Z$, hence over $\mathbb Z_p$, and it is equivalent to $Q$ over $\mathbb Z_p$
(`primRepZp_of_sameGenus`). Unconditional. -/
@[kb "cassels1978" "Ch. 11, p. 235: Thm. 1.6 fails for n = 3 (proved with Ex. 6 forms; Ch. 11, (7.4), p. 228)"]
theorem tartakowskyFailsAtThree_holds : TartakowskyFailsAtThree := by
  refine ⟨ex6f, posDef_ex6f, fun N => ?_⟩
  have hN := le_max_left N 0
  have hN0 := le_max_right N 0
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m = 4 * max N 0 + 3 := ⟨_, rfl⟩
  have hm0 : 0 < m := by omega
  refine ⟨m ^ 2, by nlinarith, fun p hp => ?_, ?_⟩
  · obtain ⟨f', hf', x, hx, hxe⟩ := ex6_genus_primRep m hm0 (by omega)
    exact primRepZp_of_sameGenus p hf' ⟨x, hx, hxe⟩
  · rintro ⟨x, hx, h⟩
    have := ex6f_mod_four m hm0 (by omega) x hx h
    omega

/-! ### The forms (7.4): Theorem 7.1 fails for $n = 3$ -/

/-- **(7.4) of Cassels, Ch. 11, p. 228 (Watson): $f_2$ represents $4$ primitively, $f_1$ does not.** Here
$f_1 = x_0^2 + x_0x_1 + x_1^2 + 9x_2^2$ (`ex7f`) and $f_2 = x_0^2 + 3(x_1^2 + x_1x_2 + x_2^2)$ (`ex7g`); Cassels' $x_1,
x_2, x_3$ are $x_0, x_1, x_2$ here. First component: $f_2(1,1,0) = 4$ with $\gcd = 1$. Second component: a primitive
representation of $4m^2$, $m = 1$, by $f_1$ would force $m \equiv 2 \pmod 3$ (`ex7f_mod_three`). Unconditional. -/
@[kb "cassels1978" "Ch. 11, (7.4), p. 228 (f₂ represents 4 primitively, f₁ does not)"]
theorem ex7_primRep_four : PrimRepZ ex7g 4 ∧ ¬ PrimRepZ ex7f 4 := by
  refine ⟨⟨![1, 1, 0], by simp [Fin.univ_succ, Finset.gcd_insert], by rw [eval_ex7g]; simp⟩, ?_⟩
  rintro ⟨x, hx, h⟩
  have := ex7f_mod_three 1 one_pos (by norm_num) (by norm_num) x hx (by rw [h]; norm_num)
  omega

/-- **Theorem 7.1 fails for $n = 3$** (Cassels, Ch. 11, p. 228, after (7.4)): the integer $4$ is primitively represented
by $f_1 = x_0^2 + x_0x_1 + x_1^2 + 9x_2^2$ over every $\mathbb Z_p$, yet no form integrally equivalent to $f_1$ (in
particular, no form properly equivalent to $f_1$) primitively represents $4$ over $\mathbb Z$. *Conditional* on the
named statement `Ex7Classes` of Example 7 (i), p. 252, of which only the field `sameGenus` ($f_2$ is in the genus of
$f_1$) is used: then $4$ is primitively represented by $f_2$ over $\mathbb Z$ (`ex7_primRep_four`), hence over
$\mathbb Z_p$, hence by $f_1$ over $\mathbb Z_p$ (`primRepZp_of_sameGenus`). The second half is unconditional
(`ex7_primRep_four` and `primRepZ_of_isometricGL`). Argument `hcl`: the named statement. -/
@[kb "cassels1978" "Ch. 11, (7.4), p. 228 (Thm. 7.1 fails for n = 3; conditional on Ex7Classes)"]
theorem theorem71_fails_ternary (hcl : Ex7Classes) :
    (∀ (p : ℕ) [Fact p.Prime], PrimRepZp p ex7f 4) ∧ ∀ f' : QuadForm ℤ 3, IntEquiv ex7f f' → ¬ PrimRepZ f' 4 := by
  refine ⟨fun p _ => primRepZp_of_sameGenus p hcl.sameGenus ex7_primRep_four.1, fun f' h hf' => ?_⟩
  exact ex7_primRep_four.2 (primRepZ_of_isometricGL h hf')

/-! ### Example (9.1): Theorem 1.6 fails for $n = 4$ without "primitively" -/

/-- The form $x_0^2 + x_1^2 + 5(x_2^2 + x_3^2)$ as printed (with the misprint $x_3^3$ corrected), example (9.1),
Ch. 11, p. 235. See the erratum in the module docstring: this form does *not* have the printed property. -/
def cassels91Printed : QuadForm ℤ 4 := QuadForm.diag ![1, 1, 5, 5]

/-- The corrected form $x_0^2 + x_1^2 + 13(x_2^2 + x_3^2)$ for example (9.1), Ch. 11, p. 235 (the coefficient $5$ of the
book is replaced by $13$; see the erratum in the module docstring). -/
def cassels91 : QuadForm ℤ 4 := QuadForm.diag ![1, 1, 13, 13]

/-- Helper: the value of `cassels91Printed` at an integer vector `x`. -/
theorem eval_cassels91Printed (x : Fin 4 → ℤ) :
    cassels91Printed.eval x = x 0 ^ 2 + x 1 ^ 2 + 5 * x 2 ^ 2 + 5 * x 3 ^ 2 := by
  simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_four, cassels91Printed, QuadForm.diag, Matrix.diagonal_apply]
  ring

/-- Helper: the value of `cassels91` at an integer vector `x`. -/
theorem eval_cassels91 (x : Fin 4 → ℤ) :
    cassels91.eval x = x 0 ^ 2 + x 1 ^ 2 + 13 * x 2 ^ 2 + 13 * x 3 ^ 2 := by
  simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_four, cassels91, QuadForm.diag, Matrix.diagonal_apply]
  ring

/-- Helper: the value of `cassels91` at a vector over $\mathbb Z_p$. -/
theorem evalIn_cassels91 (p : ℕ) [Fact p.Prime] (x : Fin 4 → ℤ_[p]) :
    cassels91.evalIn ℤ_[p] x = x 0 ^ 2 + x 1 ^ 2 + 13 * x 2 ^ 2 + 13 * x 3 ^ 2 := by
  simp [QuadForm.evalIn, Fin.sum_univ_four, cassels91, QuadForm.diag, Matrix.diagonal_apply]
  ring

/-- **Erratum witness for (9.1)** (Cassels, Ch. 11, p. 235): the printed form $x_0^2 + x_1^2 + 5(x_2^2 + x_3^2)$
represents $3 \cdot 4^m$ over $\mathbb Z$ for every $m \ge 1$ (the vector $(2^{m-1}, 2^{m-1}, 2^{m-1}, 2^{m-1})$), so the
printed claim "not represented over $\mathbb Z$ for $m > 0$" is false. Argument `m`: the exponent, $m \ge 1$. -/
theorem cassels91Printed_represents (m : ℕ) (hm : 1 ≤ m) :
    ∃ x : Fin 4 → ℤ, cassels91Printed.eval x = 3 * 4 ^ m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine ⟨fun _ => 2 ^ k, ?_⟩
  rw [eval_cassels91Printed, show (4 : ℤ) = 2 * 2 by norm_num, mul_pow]
  ring

/-- Helper: $x_0^2 + x_1^2 + 13x_2^2 + 13x_3^2$ is positive definite. -/
theorem posDef_cassels91 : IntQF.PosDef cassels91 := by
  intro x hx
  rw [eval_cassels91]
  by_contra hle
  push Not at hle
  have h0 : x 0 ^ 2 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)]
  have h1 : x 1 ^ 2 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)]
  have h2 : x 2 ^ 2 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)]
  have h3 : x 3 ^ 2 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)]
  apply hx
  funext i
  fin_cases i
  · exact pow_eq_zero_iff (two_ne_zero) |>.mp h0
  · exact pow_eq_zero_iff (two_ne_zero) |>.mp h1
  · exact pow_eq_zero_iff (two_ne_zero) |>.mp h2
  · exact pow_eq_zero_iff (two_ne_zero) |>.mp h3

/-- Helper: $3$ is represented by `cassels91` over $\mathbb Z_p$ for every prime $p$: by $(1, 1, 2/13, 3/13)$ if
$p \ne 13$ (as $13 (2^2 + 3^2)/13^2 = 1$) and by $(w, 0, 0, 0)$, $w^2 = 3$, if $p = 13$ ($4^2 \equiv 3 \pmod{13}$). -/
theorem cassels91_three_local (p : ℕ) [Fact p.Prime] :
    ∃ x : Fin 4 → ℤ_[p], x 0 ^ 2 + x 1 ^ 2 + 13 * x 2 ^ 2 + 13 * x 3 ^ 2 = 3 := by
  by_cases hp : p = 13
  · subst hp
    obtain ⟨w, -, hw⟩ := sqrt_unit_of_cong 13 (by norm_num) 3 4 (by norm_num) (by norm_num)
    refine ⟨![w, 0, 0, 0], ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_three]
    push_cast at hw
    linear_combination hw
  · have hnd : ¬ (p : ℤ) ∣ 13 := by
      intro hd
      have h1 : p ∣ 13 := by exact_mod_cast hd
      exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by norm_num)).mp h1)
    obtain ⟨u, hu⟩ := (isUnit_intCast_padic (p := p) 13).mpr hnd
    have hinv : (13 : ℤ_[p]) * ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
      have : ((13 : ℤ) : ℤ_[p]) = (u : ℤ_[p]) := hu.symm
      push_cast at this
      rw [this]
      simp
    refine ⟨![1, 1, 2 * ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), 3 * ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p])], ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_three]
    linear_combination (13 * ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) + 1) * hinv

/-- **Example (9.1), local half** (Cassels, Ch. 11, p. 235): for every $m \ge 0$ and every prime $p$, the integer
$3 \cdot 2^{2m}$ is represented by $x_0^2 + x_1^2 + 13(x_2^2 + x_3^2)$ (`cassels91`, the corrected form; the book has $5$
in place of $13$, see the erratum) over $\mathbb Z_p$: multiply a representation of $3$ (`cassels91_three_local`) by $2^m$.
Arguments: `m` the exponent, `p` the prime. -/
@[kb "cassels1978" "Ch. 11, (9.1), p. 235 (local representations; corrected form)"]
theorem cassels91_represents_local (m : ℕ) (p : ℕ) [Fact p.Prime] :
    cassels91.RepresentsIn ℤ_[p] (3 * 4 ^ m) := by
  obtain ⟨x, hx⟩ := cassels91_three_local p
  refine ⟨fun i => (2 : ℤ_[p]) ^ m * x i, ?_⟩
  rw [evalIn_cassels91]
  have e : (4 : ℤ_[p]) ^ m = ((2 : ℤ_[p]) ^ m) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  simp only [map_mul, map_pow, map_ofNat]
  rw [e]
  linear_combination ((2 : ℤ_[p]) ^ m) ^ 2 * hx

/-- Helper: an integer $x_i$ with $x_i^2 \cdot$ weights summing to $0 \bmod 8$ in `cassels91` is even in every
coordinate: if $x_0^2 + x_1^2 + 13x_2^2 + 13x_3^2 \equiv 0 \pmod 8$ then all four $x_i$ are even. -/
theorem cassels91_all_even (x : Fin 4 → ℤ) (k : ℤ) (h : cassels91.eval x = 8 * k) : ∀ i, x i % 2 = 0 := by
  rw [eval_cassels91] at h
  have h0 := sq_mod_eight (x 0)
  have h1 := sq_mod_eight (x 1)
  have h2 := sq_mod_eight (x 2)
  have h3 := sq_mod_eight (x 3)
  intro i
  fin_cases i <;> simp <;> omega

/-- Helper: $3$ and $12$ are not values of `cassels91` on integer vectors. -/
theorem cassels91_ne_small (a b c d : ℤ) (h : a ^ 2 + b ^ 2 + 13 * c ^ 2 + 13 * d ^ 2 = 3 ∨
    a ^ 2 + b ^ 2 + 13 * c ^ 2 + 13 * d ^ 2 = 12) : False := by
  have ha := sq_nonneg a
  have hb := sq_nonneg b
  have hc := sq_nonneg c
  have hd := sq_nonneg d
  have hc0 : c ^ 2 = 0 := by omega
  have hd0 : d ^ 2 = 0 := by omega
  have hc' : c = 0 := pow_eq_zero_iff two_ne_zero |>.mp hc0
  have hd' : d = 0 := pow_eq_zero_iff two_ne_zero |>.mp hd0
  subst hc' hd'
  have ha3 : a ^ 2 ≤ 4 ^ 2 := by rcases h with h | h <;> nlinarith
  have hb3 : b ^ 2 ≤ 4 ^ 2 := by rcases h with h | h <;> nlinarith
  obtain ⟨ha1, ha2⟩ := abs_le_of_sq_le_sq' ha3 (by norm_num)
  obtain ⟨hb1, hb2⟩ := abs_le_of_sq_le_sq' hb3 (by norm_num)
  interval_cases a <;> interval_cases b <;> omega

/-- **Example (9.1), global half** (Cassels, Ch. 11, p. 235): for every $m \ge 0$ the integer $3 \cdot 2^{2m}$ is *not*
represented over $\mathbb Z$ by $x_0^2 + x_1^2 + 13(x_2^2 + x_3^2)$ (`cassels91`, the corrected form; the printed form
with $5$ represents $3 \cdot 4^m$ for $m \ge 1$, `cassels91Printed_represents`). *Proof* (Cassels' descent). For
$m \ge 2$ a representation has $f \equiv 0 \pmod{16}$, so all coordinates are even (mod $8$ computation, as
$13 \equiv 5 \pmod 8$) and halving gives a representation of $3 \cdot 4^{m-1}$; the cases $m = 0, 1$ ($3$ and $12$) are
excluded by size. Argument `m`: the exponent. -/
@[kb "cassels1978" "Ch. 11, (9.1), p. 235 (no integral representation; corrected form)"]
theorem cassels91_not_represented (m : ℕ) : ¬ ∃ x : Fin 4 → ℤ, cassels91.eval x = 3 * 4 ^ m := by
  induction m with
  | zero =>
    rintro ⟨x, h⟩
    rw [eval_cassels91] at h
    exact cassels91_ne_small _ _ _ _ (Or.inl (by simpa using h))
  | succ m ih =>
    rintro ⟨x, h⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [eval_cassels91] at h
      exact cassels91_ne_small _ _ _ _ (Or.inr (by simpa using h))
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have h8 : cassels91.eval x = 8 * (6 * 4 ^ k) := by rw [h]; ring
      have hev := cassels91_all_even x _ h8
      obtain ⟨y, hy⟩ : ∃ y : Fin 4 → ℤ, x = fun i => 2 * y i :=
        ⟨fun i => x i / 2, funext fun i => by have := hev i; simp only; omega⟩
      apply ih
      refine ⟨y, ?_⟩
      subst hy
      rw [eval_cassels91] at h ⊢
      have : 4 * (y 0 ^ 2 + y 1 ^ 2 + 13 * y 2 ^ 2 + 13 * y 3 ^ 2) = 4 * (3 * 4 ^ (k + 1)) := by
        linear_combination h
      linarith

/-- **Theorem 1.6 fails for $n = 4$ if "primitively" is omitted** (Cassels, Ch. 11, p. 235, example (9.1)), proved: there is
a positive definite quaternary form (here $x_0^2 + x_1^2 + 13(x_2^2 + x_3^2)$, see the erratum) such that for every $N$ there
is an integer $a = 3 \cdot 4^N \ge N$ represented over every $\mathbb Z_p$ but not over $\mathbb Z$. Unconditional. -/
@[kb "cassels1978" "Ch. 11, (9.1), p. 235: Thm. 1.6 fails for n = 4 without 'primitively' (proved; corrected form)"]
theorem tartakowskyUnprimitiveFailsAtFour_holds : TartakowskyUnprimitiveFailsAtFour := by
  refine ⟨cassels91, posDef_cassels91, fun N => ?_⟩
  refine ⟨3 * 4 ^ N.toNat, ?_, fun p hp => ?_, ?_⟩
  · have h1 : (N.toNat : ℤ) < 4 ^ N.toNat := by exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 4)
    have h2 : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
    have h3 : (0 : ℤ) < 4 ^ N.toNat := by positivity
    omega
  · have := hp
    exact cassels91_represents_local N.toNat p
  · exact cassels91_not_represented N.toNat

end QuadFormsKB.Cassels.Ch11Failures
