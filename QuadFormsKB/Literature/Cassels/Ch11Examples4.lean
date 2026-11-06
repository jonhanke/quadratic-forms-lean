/-
# Cassels, Chapter 11, Examples 3-7 and 9 (pp. 251-253): genera, spinor genera, and primitive representations

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, Examples 3, 4, 5, 6, 7 and 9 at the end of the
chapter (pp. 251-253). The book's variables $x, y, z, t$ are $x_0, x_1, x_2, x_3$ here (0-based `Fin n` indices; Cassels'
$b_1, \dots, b_n$ of Example 4 are the columns $0, \dots, n-1$ of a basis matrix). Capital $Q$ is the quadratic form of a
general statement; the examples' forms are `QuadForm ℤ n`. *Reading of the scan:* the form of Example 3 is garbled in the
machine text; it is $f = x^2 + 5y^2 - 25z^2$ (determinant $-125$ is that of $g = -x^2 + 5y^2 + 25z^2$); in
Example 7 (ii) the condition "$2 \nmid m$" is read as $m$ odd and the two cases of the statement are $m \equiv 1, 2
\pmod 3$ (see `ex7_primRep_iff`).

**Proved (unconditionally).**
* Example 3: the explicit proper equivalence $f(T\vec x) = g(\vec x)$ (`ex3_properIntEquiv`), found by computer search;
  hence $g$ is in the genus of $f$ (`ex3_sameGenus`).
* Example 4, the inclusion "$\supseteq$": the squares and the products $\phi(b_1)\phi(b_j)$ lie in $\theta(\Lambda_p)$
  (`ex4_closure_le`).
* Example 6 (iv), necessity: an odd square $m^2$, $m > 0$, primitively represented by $f = x^2 + y^2 + 16z^2$ forces
  $m \equiv 1 \pmod 4$ (`ex6f_mod_four`), by $g = (x-y)^2 + (x+y+z)^2 + 4z^2$ forces $m \equiv 3 \pmod 4$
  (`ex6g_mod_four`); hence "never by both" (`ex6_not_both`) and $f \not\sim g$ (`ex6_not_intEquiv`). Elementary: a prime
  $\equiv 3 \pmod 4$ divides a sum of two squares to an even power.
* Example 7 (ii)/(iii), the part "without spinor genera" (the hint of (iii)): for $m > 0$ odd, $3 \nmid m$, a primitive
  representation of $4m^2$ by $f = x^2 + xy + y^2 + 9z^2$ forces $m \equiv 2$ (`ex7f_mod_three`), by
  $g = x^2 + 3(y^2 + yz + z^2)$ forces $m \equiv 1 \pmod 3$ (`ex7g_mod_three`); for $m = 3m'$ the primitive
  representations force $m' \equiv 1$ (`ex7f_three_dvd`) resp. $m' \equiv 2 \pmod 3$ (`ex7g_three_dvd`); hence "never by
  both" for every odd $m > 0$ (`ex7_not_both`) and $f \not\sim g$ (`ex7_not_intEquiv`). The key fact is that a prime $\equiv 2 \pmod 3$ (also $2$) is inert in
  $\mathbb Z[\omega]$ and divides $x^2 + xy + y^2$ only to an even power.

**Conditional on named statements.** Each named statement is a `structure ... : Prop` with a faithful formulation and the
content of the book's claim; nothing is assumed as an axiom.
* `Ex6Classes` (Example 6 (i), (iii)): the genus of $f$ has exactly the two classes of $f$ and $g$. With it,
  `ex6_primRep_iff` proves Example 6 (iv): $m^2$ is primitively represented by $f$ iff $m \equiv 1 \pmod 4$ and by $g$ iff
  $m \equiv 3 \pmod 4$ (the existence half uses Chapter 9, Theorem 5.1 with the local vector $(m, 0, 0)$ at $p = 2$), and
  `ex6_primRep_exactly_one` gives "precisely one".
* `Ex7Classes` (Example 7 (i)): the genus of $f$ has exactly the two classes of $f$ and $g$. With it, `ex7_primRep_iff`
  proves the existence halves of Example 7 (ii), (iii) (local vectors $(1, 1, w/3)$ at $2$, $(2m, 0, 0)$ at $3$).
* `Ex3OneClass`: the genus of $x^2 + 5y^2 - 25z^2$ has one class (and then `Ex3OneClass.intEquiv`).

**Named statements, nothing derived from them here.** `Ex4Statement` (the other inclusion of Example 4), `Ex5Statement`
(Example 5, class numbers $2$ and $1$), `Ex6SpinorGenera` (Example 6 (i), (ii): $P = \{2\}$, $|G| = 2$, two spinor genera,
$g(w) = 1$ iff $w \equiv 1 \pmod 4$), `Ex7SpinorGenera` (Example 7 (i), number of spinor genera), `Ex9Statement`
(Example 9: more than one spinor genus; the three classes, found by computer: see its docstring).

**Not formalized.** Example 8 (not assigned here). The library lacks the local spinor norm groups of non-unimodular
$\mathbb Z_p$-lattices (beyond Example 4's easy inclusion) and at $p = 2$ beyond the ranges of Lemma 3.8, so the group $G$
of (3.15) cannot be computed for these forms; and it lacks the reduction theory needed to enumerate classes of ternary and
quaternary positive definite forms. Numerical checks (Python, class enumeration by Minkowski-reduced Hessians with local
counts as genus proxy): the genus of $f$ in Example 6 has the two classes $f$, $g$ (determinant-$128$ Hessians, $9$ classes
in all); in Example 7 the two classes $f$, $g$ (determinant-$54$ Hessians, $5$ classes in all); in Example 9 the three classes
of `ex9f`, `ex9f₂`, `ex9f₃`.
-/
import QuadFormsKB.Literature.Cassels.Ch11Examples
import QuadFormsKB.Literature.Cassels.Ch11Sec4Group
import QuadFormsKB.Literature.Cassels.Ch11Sec3Local
import QuadFormsKB.Literature.OMeara.Sec102Spn

open Matrix NumberField IsDedekindDomain QuadFormsKB.Siegel

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11Ex4

/-- Helper: a prime `p ≡ 2 (mod 3)` dividing `x² + x y + y²` divides `x` and `y` (the prime is inert in `ℤ[ω]`). -/
theorem dvd_of_dvd_norm_eisenstein (p : ℕ) (hp : p.Prime) (hp3 : p % 3 = 2) (x y : ℤ)
    (h : (p : ℤ) ∣ x ^ 2 + x * y + y ^ 2) : (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y := by
  have : Fact p.Prime := ⟨hp⟩
  have h0 : ((x ^ 2 + x * y + y ^ 2 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h
  push_cast at h0
  by_cases hy : (y : ZMod p) = 0
  · rw [hy] at h0
    have hx : (x : ZMod p) = 0 := by simpa using h0
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hx, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hy⟩
  · exfalso
    set w : ZMod p := (x : ZMod p) / (y : ZMod p) with hw
    have hw2 : w ^ 2 + w + 1 = 0 := by
      rw [hw]; field_simp; linear_combination h0
    have hw3 : w ^ 3 = 1 := by linear_combination (w - 1) * hw2
    have hw1 : w ≠ 1 := by
      intro h1
      rw [h1] at hw2
      have h3 : ((3 : ℕ) : ZMod p) = 0 := by norm_num at hw2 ⊢; linear_combination hw2
      have : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h3
      have hp3' : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp this
      omega
    have hw0 : w ≠ 0 := by
      intro h0'; rw [h0'] at hw3; simp at hw3
    have hord : orderOf w = 3 := orderOf_eq_prime hw3 hw1
    have hd := ZMod.orderOf_dvd_card_sub_one hw0
    rw [hord] at hd
    have := hp.two_le
    omega

/-- Helper: a prime `p ≡ 3 (mod 4)` dividing `x² + y²` divides `x` and `y`. -/
theorem dvd_of_dvd_sumsq (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 3) (x y : ℤ)
    (h : (p : ℤ) ∣ x ^ 2 + y ^ 2) : (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y := by
  have : Fact p.Prime := ⟨hp⟩
  have h0 : ((x ^ 2 + y ^ 2 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h
  push_cast at h0
  by_cases hy : (y : ZMod p) = 0
  · rw [hy] at h0
    have hx : (x : ZMod p) = 0 := by simpa using h0
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hx, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hy⟩
  · exfalso
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (x := (x : ZMod p)) (y := (y : ZMod p)) hy (by linear_combination h0) hp4

/-- Helper: descent. -/
theorem even_padicValInt_of_descent (p : ℕ) (hp : p.Prime) (F : ℤ → ℤ → ℤ)
    (hF : ∀ x y, F ((p : ℤ) * x) ((p : ℤ) * y) = (p : ℤ) ^ 2 * F x y)
    (hdiv : ∀ x y, (p : ℤ) ∣ F x y → (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y) :
    ∀ (n : ℕ) (x y : ℤ), (F x y).natAbs = n → F x y ≠ 0 → Even (padicValInt p (F x y)) := by
  have : Fact p.Prime := ⟨hp⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y hn h0
    by_cases hd : (p : ℤ) ∣ F x y
    · obtain ⟨⟨x', rfl⟩, ⟨y', rfl⟩⟩ := hdiv x y hd
      rw [hF] at hn h0 ⊢
      have hp0 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
      have hF0 : F x' y' ≠ 0 := fun h => h0 (by rw [h, mul_zero])
      have hlt : (F x' y').natAbs < n := by
        rw [← hn, Int.natAbs_mul]
        have h1 : 1 < (p : ℤ).natAbs ^ 2 := by
          simp only [Int.natAbs_natCast]
          exact Nat.one_lt_pow two_ne_zero hp.one_lt
        have h2 : 0 < (F x' y').natAbs := Int.natAbs_pos.mpr hF0
        simp only [Int.natAbs_pow, Int.natAbs_natCast] at *
        nlinarith
      have := ih _ hlt x' y' rfl hF0
      rw [padicValInt.mul hp0 hF0]
      have e : padicValInt p ((p : ℤ) ^ 2) = 2 := by
        have : padicValInt p (p : ℤ) = 1 := padicValInt_self
        rw [pow_two, padicValInt.mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hp.ne_zero), this]
      rw [e]
      exact (even_two).add this
    · have : padicValInt p (F x y) = 0 := by
        unfold padicValInt
        exact padicValNat.eq_zero_of_not_dvd (fun hh => hd (Int.natCast_dvd.mpr hh))
      rw [this]; exact ⟨0, rfl⟩

/-- Helper: product formula for the residue of `a` modulo `q`. -/
theorem zmod_eq_one_of_even_valuations (q : ℕ) (a : ℕ) (ha : 0 < a)
    (h : ∀ p : ℕ, p.Prime → p ∣ a →
      (p : ZMod q) = 1 ∨ ((p : ZMod q) = -1 ∧ Even (padicValNat p a))) : (a : ZMod q) = 1 := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self ha.ne']
  unfold Finsupp.prod
  push_cast
  apply Finset.prod_eq_one
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hdvd := Nat.dvd_of_mem_primeFactors hp
  rcases h p hpp hdvd with h1 | ⟨h1, h2⟩
  · rw [h1, one_pow]
  · rw [h1, Nat.factorization_def a hpp]
    exact h2.neg_one_pow

/-- Helper: valuations of the factors. -/
theorem even_padicValNat_of_mul (p : ℕ) (hp : p.Prime) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : Even (padicValNat p (a * b))) (hnot : ¬ (p ∣ a ∧ p ∣ b)) : Even (padicValNat p a) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [padicValNat.mul ha.ne' hb.ne'] at hab
  by_cases hpb : p ∣ b
  · have : ¬ p ∣ a := fun h => hnot ⟨h, hpb⟩
    rw [padicValNat.eq_zero_of_not_dvd this]; exact ⟨0, rfl⟩
  · rw [padicValNat.eq_zero_of_not_dvd hpb, add_zero] at hab
    exact hab

/-- Helper: `a b = x² + x y + y²`, `a` prime to 3, no prime `≡ 2 (mod 3)` dividing both: `a ≡ 1 (mod 3)`. -/
theorem mod_three_of_norm (x y : ℤ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : ((a * b : ℕ) : ℤ) = x ^ 2 + x * y + y ^ 2) (h3 : ¬ 3 ∣ a)
    (hcop : ∀ p : ℕ, p.Prime → p % 3 = 2 → p ∣ a → p ∣ b → False) : a % 3 = 1 := by
  have hN : x ^ 2 + x * y + y ^ 2 ≠ 0 := by rw [← hab]; exact_mod_cast (Nat.mul_pos ha hb).ne'
  have key := (zmod_eq_one_of_even_valuations 3 a ha (fun p hp hpa => ?_))
  · have := (ZMod.natCast_eq_natCast_iff' a 1 3).mp (by simpa using key)
    simpa using this
  · have hp3 : p % 3 = 1 ∨ p % 3 = 2 := by
      have : p % 3 ≠ 0 := fun h0 => h3 (by
        have : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp this
        subst this; exact hpa)
      omega
    rcases hp3 with h1 | h2
    · left
      rw [← ZMod.natCast_mod p 3, h1]; simp
    · right
      refine ⟨?_, ?_⟩
      · rw [← ZMod.natCast_mod p 3, h2]; decide
      · have hev := even_padicValInt_of_descent p hp (fun x y => x ^ 2 + x * y + y ^ 2)
          (fun x y => by ring) (fun x y h => dvd_of_dvd_norm_eisenstein p hp h2 x y h)
          _ x y rfl hN
        have e : padicValInt p (x ^ 2 + x * y + y ^ 2) = padicValNat p (a * b) := by
          rw [← hab]; exact padicValInt.of_nat
        simp only [e] at hev
        exact even_padicValNat_of_mul p hp a b ha hb hev (fun ⟨h1, h2'⟩ => hcop p hp h2 h1 h2')

/-- Helper: `a b = x² + y²`, `a` odd, no prime `≡ 3 (mod 4)` dividing both: `a ≡ 1 (mod 4)`. -/
theorem mod_four_of_sumsq (x y : ℤ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : ((a * b : ℕ) : ℤ) = x ^ 2 + y ^ 2) (h2 : a % 2 = 1)
    (hcop : ∀ p : ℕ, p.Prime → p % 4 = 3 → p ∣ a → p ∣ b → False) : a % 4 = 1 := by
  have hN : x ^ 2 + y ^ 2 ≠ 0 := by rw [← hab]; exact_mod_cast (Nat.mul_pos ha hb).ne'
  have key := (zmod_eq_one_of_even_valuations 4 a ha (fun p hp hpa => ?_))
  · have := (ZMod.natCast_eq_natCast_iff' a 1 4).mp (by simpa using key)
    simpa using this
  · have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by
      have : p % 2 = 1 := by
        rcases hp.eq_two_or_odd with h | h
        · subst h; omega
        · exact h
      omega
    rcases hp4 with h1 | h3
    · left
      rw [← ZMod.natCast_mod p 4, h1]; simp
    · right
      refine ⟨?_, ?_⟩
      · rw [← ZMod.natCast_mod p 4, h3]; decide
      · have hev := even_padicValInt_of_descent p hp (fun x y => x ^ 2 + y ^ 2)
          (fun x y => by ring) (fun x y h => dvd_of_dvd_sumsq p hp h3 x y h)
          _ x y rfl hN
        have e : padicValInt p (x ^ 2 + y ^ 2) = padicValNat p (a * b) := by
          rw [← hab]; exact padicValInt.of_nat
        simp only [e] at hev
        exact even_padicValNat_of_mul p hp a b ha hb hev (fun ⟨h1, h2'⟩ => hcop p hp h3 h1 h2')

/-! ### Example 3: an explicit equivalence -/

/-- The form $x_0^2 + 5x_1^2 - 25x_2^2$ of Example 3 (Ch. 11, p. 251). -/
def ex3f : QuadForm ℤ 3 := QuadForm.diag ![1, 5, -25]

/-- The form $-x_0^2 + 5x_1^2 + 25x_2^2$ of Example 3 (Ch. 11, p. 251). -/
def ex3g : QuadForm ℤ 3 := QuadForm.diag ![-1, 5, 25]

/-- Helper: values of $x_0^2 + 5x_1^2 - 25x_2^2$. -/
theorem eval_ex3f (x : Fin 3 → ℤ) : ex3f.eval x = x 0 ^ 2 + 5 * x 1 ^ 2 - 25 * x 2 ^ 2 := by
  simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_three, ex3f, QuadForm.diag, Matrix.diagonal_apply]
  ring

/-- Helper: values of $-x_0^2 + 5x_1^2 + 25x_2^2$. -/
theorem eval_ex3g (x : Fin 3 → ℤ) : ex3g.eval x = -x 0 ^ 2 + 5 * x 1 ^ 2 + 25 * x 2 ^ 2 := by
  simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_three, ex3g, QuadForm.diag, Matrix.diagonal_apply]
  ring

/-- Helper: the substitution matrix of Example 3, with columns $(2,2,1)$, $(-5,-4,-2)$, $(0,-5,-2)$ (pairwise orthogonal
for $x_0^2 + 5x_1^2 - 25x_2^2$, with values $-1, 5, 25$), found by computer search; determinant $1$. -/
def ex3T : GL (Fin 3) ℤ :=
  ⟨!![2, -5, 0; 2, -4, -5; 1, -2, -2], !![-2, -10, 25; -1, -4, 10; 0, -1, 2],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

/-- **Cassels, Ch. 11, Example 3** (p. 251), the explicit equivalence: *find an equivalence* between
$f = x^2 + 5y^2 - 25z^2$ and $g = -x^2 + 5y^2 + 25z^2$ (variables $x, y, z$ are $x_0, x_1, x_2$). The matrix `ex3T`
(columns $(2,2,1)$, $(-5,-4,-2)$, $(0,-5,-2)$) has determinant $1$ and satisfies $f(T\vec x) = g(\vec x)$, so the forms
are properly integrally equivalent. (Found by a computer search for pairwise orthogonal vectors of $f$-values
$-1, 5, 25$; this is the "deduce" half of the example, once the genus of $f$ is known to have one class.) -/
@[kb "cassels1978" "Ch. 11, Ex. 3, p. 251 (explicit equivalence)"]
theorem ex3_properIntEquiv : ProperIntEquiv ex3f ex3g := by
  refine ⟨ex3T, ?_, fun x => ?_⟩
  · simp [ex3T, Matrix.det_fin_three]
  · rw [eval_ex3f, eval_ex3g]
    simp [ex3T, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring

/-! ### The forms of Examples 6 and 7 -/

/-- The form $f = x_0^2 + x_1^2 + 16x_2^2$ of Example 6 (Ch. 11, p. 252). -/
def ex6f : QuadForm ℤ 3 := QuadForm.diag ![1, 1, 16]

/-- The form $g = (x_0 - x_1)^2 + (x_0 + x_1 + x_2)^2 + 4x_2^2 = 2x_0^2 + 2x_1^2 + 5x_2^2 + 2x_0x_2 + 2x_1x_2$ of
Example 6 (Ch. 11, p. 252). -/
def ex6g : QuadForm ℤ 3 := QuadForm.ofUpper ![![2, 0, 2], ![0, 2, 2], ![0, 0, 5]]

/-- The form $f = x_0^2 + x_0x_1 + x_1^2 + 9x_2^2$ of Example 7 (Ch. 11, p. 252). -/
def ex7f : QuadForm ℤ 3 := QuadForm.ofUpper ![![1, 1, 0], ![0, 1, 0], ![0, 0, 9]]

/-- The form $g = x_0^2 + 3(x_1^2 + x_1x_2 + x_2^2)$ of Example 7 (Ch. 11, p. 252). -/
def ex7g : QuadForm ℤ 3 := QuadForm.ofUpper ![![1, 0, 0], ![0, 3, 3], ![0, 0, 3]]

/-- Helper: values of $f = x_0^2 + x_1^2 + 16x_2^2$. -/
theorem eval_ex6f (x : Fin 3 → ℤ) : ex6f.eval x = x 0 ^ 2 + x 1 ^ 2 + 16 * x 2 ^ 2 := by
  simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_three, ex6f, QuadForm.diag, Matrix.diagonal_apply]
  ring

/-- Helper: values of $g$ of Example 6, as $(x_0 - x_1)^2 + (x_0 + x_1 + x_2)^2 + 4x_2^2$. -/
theorem eval_ex6g (x : Fin 3 → ℤ) :
    ex6g.eval x = (x 0 - x 1) ^ 2 + (x 0 + x 1 + x 2) ^ 2 + 4 * x 2 ^ 2 := by
  simp [QuadForm.eval, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_three, ex6g]
  ring

/-- Helper: values of $f = x_0^2 + x_0x_1 + x_1^2 + 9x_2^2$. -/
theorem eval_ex7f (x : Fin 3 → ℤ) : ex7f.eval x = x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2 + 9 * x 2 ^ 2 := by
  simp [QuadForm.eval, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_three, ex7f]
  ring

/-- Helper: values of $g = x_0^2 + 3(x_1^2 + x_1x_2 + x_2^2)$. -/
theorem eval_ex7g (x : Fin 3 → ℤ) : ex7g.eval x = x 0 ^ 2 + 3 * (x 1 ^ 2 + x 1 * x 2 + x 2 ^ 2) := by
  simp [QuadForm.eval, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_three, ex7g]
  ring

/-! ### Elementary helpers for the representation conditions -/

/-- Helper: a primitive integer vector of length $3$ has a coordinate prime to each prime $p$. -/
theorem not_all_dvd (x : Fin 3 → ℤ) (hx : Finset.univ.gcd x = 1) (p : ℕ) (hp : p.Prime)
    (h0 : (p : ℤ) ∣ x 0) (h1 : (p : ℤ) ∣ x 1) (h2 : (p : ℤ) ∣ x 2) : False := by
  obtain ⟨i, hi⟩ := exists_not_dvd_of_gcd x hx p (fun hu => by
    have := Int.isUnit_iff.mp hu
    have := hp.two_le
    omega)
  fin_cases i
  · exact hi h0
  · exact hi h1
  · exact hi h2

/-- Helper: an odd prime dividing $2^k z$ divides $z$. -/
theorem dvd_of_dvd_two_pow_mul (p : ℕ) (hp : p.Prime) (hodd : p % 2 = 1) (k : ℕ) (z : ℤ)
    (h : (p : ℤ) ∣ 2 ^ k * z) : (p : ℤ) ∣ z := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpz.dvd_or_dvd h with h1 | h1
  · exfalso
    have h2 : p ∣ 2 ^ k := by exact_mod_cast h1
    have := hp.dvd_of_dvd_pow h2
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
    omega
  · exact h1

/-- Helper: a prime $p \equiv 2 \pmod 3$ other than $2$ dividing $6z$ divides $z$. -/
theorem dvd_of_dvd_six_mul (p : ℕ) (hp : p.Prime) (hp3 : p % 3 = 2) (hp2 : p ≠ 2) (z : ℤ)
    (h : (p : ℤ) ∣ 6 * z) : (p : ℤ) ∣ z := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpz.dvd_or_dvd h with h1 | h1
  · exfalso
    have h2 : p ∣ 2 * 3 := by exact_mod_cast h1
    rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
      omega
  · exact h1

/-- Helper: a prime $p \equiv 2 \pmod 3$ dividing $3N$ divides $N$. -/
theorem dvd_of_dvd_three_mul (p : ℕ) (hp : p.Prime) (hp3 : p % 3 = 2) (z : ℤ) (h : (p : ℤ) ∣ 3 * z) :
    (p : ℤ) ∣ z := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpz.dvd_or_dvd h with h1 | h1
  · exfalso
    have h2 : p ∣ 3 := by exact_mod_cast h1
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h2
    omega
  · exact h1

/-- Helper: if $ab \ge 0$, $a, b \ne 0$ and $a + b > 0$ then $a, b > 0$. -/
theorem pos_of_mul_nonneg' {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : 0 ≤ a * b) (hs : 0 < a + b) :
    0 < a ∧ 0 < b := by
  have h : 0 < a * b := lt_of_le_of_ne hab (Ne.symm (mul_ne_zero ha hb))
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with h1 | h1
  · exact h1
  · omega

/-- Helper: a sum of two squares with even sum of the bases is even. -/
theorem sq_add_sq_even (u v : ℤ) (h : (u + v) % 2 = 0) : (u ^ 2 + v ^ 2) % 2 = 0 := by
  have h1 : u % 2 = v % 2 := by omega
  rcases Int.emod_two_eq_zero_or_one u with h2 | h2 <;>
    simp [pow_two, Int.add_emod, Int.mul_emod, h2, ← h1]

/-- Helper: divisibility of the integer cast of a natural number. -/
theorem natCast_dvd_int {p a : ℕ} {z : ℤ} (h : p ∣ a) (ha : (a : ℤ) = z) : (p : ℤ) ∣ z := by
  rw [← ha]; exact_mod_cast h

/-! ### Example 6 (iv): necessary conditions for primitive representation of odd squares -/

/-- **Example 6 (iv), necessity for $f$.** If an odd square $m^2$ ($m > 0$) is represented primitively by
$f = x_0^2 + x_1^2 + 16x_2^2$ (the gcd of the coordinates is $1$), then $m \equiv 1 \pmod 4$. *Proof (elementary, no
spinor genera):* $x_0^2 + x_1^2 = (m - 4x_2)(m + 4x_2)$ with both factors positive and odd; no prime
$\equiv 3 \pmod 4$ divides both (it would divide all of $x_0, x_1, x_2$); a prime $\equiv 3 \pmod 4$ divides a sum of two
squares to an even power, so $m - 4x_2 \equiv 1 \pmod 4$. Arguments: `m` the positive odd integer, `x` the coordinate
vector, `hx` its primitivity, `h` the representation. -/
@[kb "cassels1978" "Ch. 11, Ex. 6 (iv), p. 252 (necessity for f)"]
theorem ex6f_mod_four (m : ℤ) (hm0 : 0 < m) (hm2 : m % 2 = 1) (x : Fin 3 → ℤ) (hx : Finset.univ.gcd x = 1)
    (h : ex6f.eval x = m ^ 2) : m % 4 = 1 := by
  rw [eval_ex6f] at h
  have hab : (m - 4 * x 2) * (m + 4 * x 2) = x 0 ^ 2 + x 1 ^ 2 := by linear_combination (-1 : ℤ) * h
  have ha0 : m - 4 * x 2 ≠ 0 := by omega
  have hb0 : m + 4 * x 2 ≠ 0 := by omega
  have hnn : 0 ≤ (m - 4 * x 2) * (m + 4 * x 2) := by rw [hab]; positivity
  obtain ⟨hapos, hbpos⟩ := pos_of_mul_nonneg' ha0 hb0 hnn (by omega)
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le hapos.le
  obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le hbpos.le
  have hab' : ((a * b : ℕ) : ℤ) = x 0 ^ 2 + x 1 ^ 2 := by push_cast; rw [← ha, ← hb]; exact hab
  have key := mod_four_of_sumsq (x 0) (x 1) a b (by omega) (by omega) hab' (by omega) ?_
  · omega
  · intro p hp hp4 hpa hpb
    have hpa' : (p : ℤ) ∣ m - 4 * x 2 := natCast_dvd_int hpa ha.symm
    have hpb' : (p : ℤ) ∣ m + 4 * x 2 := natCast_dvd_int hpb hb.symm
    have hodd : p % 2 = 1 := by omega
    have hdiv : (p : ℤ) ∣ x 0 ^ 2 + x 1 ^ 2 := by rw [← hab]; exact dvd_mul_of_dvd_left hpa' _
    obtain ⟨hX, hY⟩ := dvd_of_dvd_sumsq p hp hp4 _ _ hdiv
    have h2m : (p : ℤ) ∣ 2 ^ 1 * m := by
      have := dvd_add hpa' hpb'
      convert this using 1; ring
    have h8Z : (p : ℤ) ∣ 2 ^ 3 * x 2 := by
      have := dvd_sub hpb' hpa'
      convert this using 1; ring
    exact not_all_dvd x hx p hp hX hY (dvd_of_dvd_two_pow_mul p hp hodd 3 _ h8Z)

/-- **Example 6 (iv), necessity for $g$.** If an odd square $m^2$ ($m > 0$) is represented primitively by
$g = (x_0 - x_1)^2 + (x_0 + x_1 + x_2)^2 + 4x_2^2$, then $m \equiv 3 \pmod 4$. *Proof:* with $u = x_0 - x_1$,
$v = x_0 + x_1 + x_2$ one has $u^2 + v^2 = (m - 2x_2)(m + 2x_2)$, the factors are positive, odd, and have no common prime
factor $\equiv 3 \pmod 4$ (it would divide $u, v, x_2$, hence $x_0, x_1, x_2$); so $m - 2x_2 \equiv 1 \pmod 4$; and $x_2$ is
odd because $u^2 + v^2$ is odd while $u + v = 2x_0 + x_2$. Arguments as in `ex6f_mod_four`. -/
@[kb "cassels1978" "Ch. 11, Ex. 6 (iv), p. 252 (necessity for g)"]
theorem ex6g_mod_four (m : ℤ) (hm0 : 0 < m) (hm2 : m % 2 = 1) (x : Fin 3 → ℤ) (hx : Finset.univ.gcd x = 1)
    (h : ex6g.eval x = m ^ 2) : m % 4 = 3 := by
  rw [eval_ex6g] at h
  have hab : (m - 2 * x 2) * (m + 2 * x 2) = (x 0 - x 1) ^ 2 + (x 0 + x 1 + x 2) ^ 2 := by
    linear_combination (-1 : ℤ) * h
  have ha0 : m - 2 * x 2 ≠ 0 := by omega
  have hb0 : m + 2 * x 2 ≠ 0 := by omega
  have hnn : 0 ≤ (m - 2 * x 2) * (m + 2 * x 2) := by rw [hab]; positivity
  obtain ⟨hapos, hbpos⟩ := pos_of_mul_nonneg' ha0 hb0 hnn (by omega)
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le hapos.le
  obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le hbpos.le
  have hab' : ((a * b : ℕ) : ℤ) = (x 0 - x 1) ^ 2 + (x 0 + x 1 + x 2) ^ 2 := by
    push_cast; rw [← ha, ← hb]; exact hab
  have key := mod_four_of_sumsq (x 0 - x 1) (x 0 + x 1 + x 2) a b (by omega) (by omega) hab' (by omega) ?_
  · -- `x 2` is odd
    have hodd : (((m - 2 * x 2) * (m + 2 * x 2)) % 2) = 1 := by
      have e1 : (m - 2 * x 2) % 2 = 1 := by omega
      have e2 : (m + 2 * x 2) % 2 = 1 := by omega
      simp [Int.mul_emod, e1, e2]
    by_contra hcon
    have hz : x 2 % 2 = 0 := by
      by_contra hz
      have : x 2 % 2 = 1 := by omega
      omega
    have := sq_add_sq_even (x 0 - x 1) (x 0 + x 1 + x 2) (by omega)
    rw [← hab] at this
    omega
  · intro p hp hp4 hpa hpb
    have hpa' : (p : ℤ) ∣ m - 2 * x 2 := natCast_dvd_int hpa ha.symm
    have hpb' : (p : ℤ) ∣ m + 2 * x 2 := natCast_dvd_int hpb hb.symm
    have hodd : p % 2 = 1 := by omega
    have hdiv : (p : ℤ) ∣ (x 0 - x 1) ^ 2 + (x 0 + x 1 + x 2) ^ 2 := by
      rw [← hab]; exact dvd_mul_of_dvd_left hpa' _
    obtain ⟨hu, hv⟩ := dvd_of_dvd_sumsq p hp hp4 _ _ hdiv
    have h2m : (p : ℤ) ∣ 2 ^ 1 * m := by
      have := dvd_add hpa' hpb'
      convert this using 1; ring
    have h4Z : (p : ℤ) ∣ 2 ^ 2 * x 2 := by
      have := dvd_sub hpb' hpa'
      convert this using 1; ring
    have hZ := dvd_of_dvd_two_pow_mul p hp hodd 2 _ h4Z
    have h2X : (p : ℤ) ∣ 2 ^ 1 * x 0 := by
      have := dvd_add hu (dvd_sub hv hZ)
      convert this using 1; ring
    have h2Y : (p : ℤ) ∣ 2 ^ 1 * x 1 := by
      have := dvd_sub (dvd_sub hv hZ) hu
      convert this using 1; ring
    exact not_all_dvd x hx p hp (dvd_of_dvd_two_pow_mul p hp hodd 1 _ h2X)
      (dvd_of_dvd_two_pow_mul p hp hodd 1 _ h2Y) hZ

/-! ### Example 7 (ii), (iii): necessary conditions for primitive representation of $4m^2$ -/

/-- **Example 7 (ii)/(iii), necessity for $f$** (the elementary argument of the hint). If $4m^2$ ($m > 0$ odd, $3 \nmid m$)
is represented primitively by $f = x_0^2 + x_0x_1 + x_1^2 + 9x_2^2$, then $m \equiv 2 \pmod 3$. *Proof (Cassels' hint):*
$x_0^2 + x_0x_1 + x_1^2 = (2m - 3x_2)(2m + 3x_2)$; both factors are positive and prime to $3$; a prime
$p \equiv 2 \pmod 3$ (including $p = 2$) divides $x_0^2 + x_0x_1 + x_1^2$ only to an even power (it is inert in
$\mathbb Z[\omega]$) and cannot divide both factors (it would divide $x_0, x_1, x_2$); so $2m - 3x_2 \equiv 1 \pmod 3$,
i.e. $m \equiv 2 \pmod 3$. The hypothesis $3 \nmid m$ is the case distinction of the statement (the book says "if
$m \equiv 2$" and "if $m \equiv 1 \pmod 3$"). Arguments: `m` the integer, `hm0` its positivity, `hm2` its oddness,
`hm3` that $3 \nmid m$, `x` the vector, `hx` its primitivity, `h` the representation. -/
@[kb "cassels1978" "Ch. 11, Ex. 7 (ii)/(iii), p. 252 (necessity for f)"]
theorem ex7f_mod_three (m : ℤ) (hm0 : 0 < m) (hm2 : m % 2 = 1) (hm3 : m % 3 ≠ 0) (x : Fin 3 → ℤ)
    (hx : Finset.univ.gcd x = 1) (h : ex7f.eval x = 4 * m ^ 2) : m % 3 = 2 := by
  rw [eval_ex7f] at h
  have hab : (2 * m - 3 * x 2) * (2 * m + 3 * x 2) = x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2 := by
    linear_combination (-1 : ℤ) * h
  have ha0 : 2 * m - 3 * x 2 ≠ 0 := by omega
  have hb0 : 2 * m + 3 * x 2 ≠ 0 := by omega
  have hnn : 0 ≤ (2 * m - 3 * x 2) * (2 * m + 3 * x 2) := by
    rw [hab]; nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0), sq_nonneg (x 1)]
  obtain ⟨hapos, hbpos⟩ := pos_of_mul_nonneg' ha0 hb0 hnn (by omega)
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le hapos.le
  obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le hbpos.le
  have hab' : ((a * b : ℕ) : ℤ) = x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2 := by
    push_cast; rw [← ha, ← hb]; exact hab
  have key := mod_three_of_norm (x 0) (x 1) a b (by omega) (by omega) hab' (by omega) ?_
  · omega
  · intro p hp hp3 hpa hpb
    have hpa' : (p : ℤ) ∣ 2 * m - 3 * x 2 := natCast_dvd_int hpa ha.symm
    have hpb' : (p : ℤ) ∣ 2 * m + 3 * x 2 := natCast_dvd_int hpb hb.symm
    have hdiv : (p : ℤ) ∣ x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2 := by
      rw [← hab]; exact dvd_mul_of_dvd_left hpa' _
    obtain ⟨hX, hY⟩ := dvd_of_dvd_norm_eisenstein p hp hp3 _ _ hdiv
    have hZ : (p : ℤ) ∣ x 2 := by
      by_cases hp2 : p = 2
      · subst hp2
        have h2 : (2 : ℤ) ∣ 2 * m - 3 * x 2 := by exact_mod_cast hpa'
        have h3 : (2 : ℤ) ∣ x 2 := by omega
        exact_mod_cast h3
      · have h6 : (p : ℤ) ∣ 6 * x 2 := by
          have := dvd_sub hpb' hpa'
          convert this using 1; ring
        exact dvd_of_dvd_six_mul p hp hp3 hp2 _ h6
    exact not_all_dvd x hx p hp hX hY hZ

/-- **Example 7 (ii)/(iii), necessity for $g$.** If $4m^2$ ($m > 0$ odd, $3 \nmid m$) is represented primitively by
$g = x_0^2 + 3(x_1^2 + x_1x_2 + x_2^2)$, then $m \equiv 1 \pmod 3$. *Proof:* $(2m - x_0)(2m + x_0) =
3(x_1^2 + x_1x_2 + x_2^2)$ with both factors positive; exactly one of them is divisible by $3$; the other one is the
cofactor of a norm and, since no prime $\equiv 2 \pmod 3$ divides both factors (it would divide all of $x_0, x_1, x_2$),
is $\equiv 1 \pmod 3$; as it is $\equiv m \pmod 3$, $m \equiv 1 \pmod 3$. Arguments as in `ex7f_mod_three`. -/
@[kb "cassels1978" "Ch. 11, Ex. 7 (ii)/(iii), p. 252 (necessity for g)"]
theorem ex7g_mod_three (m : ℤ) (hm0 : 0 < m) (hm2 : m % 2 = 1) (hm3 : m % 3 ≠ 0) (x : Fin 3 → ℤ)
    (hx : Finset.univ.gcd x = 1) (h : ex7g.eval x = 4 * m ^ 2) : m % 3 = 1 := by
  rw [eval_ex7g] at h
  have hab : (2 * m - x 0) * (2 * m + x 0) = 3 * (x 1 ^ 2 + x 1 * x 2 + x 2 ^ 2) := by
    linear_combination (-1 : ℤ) * h
  have hNpos : 0 < x 1 ^ 2 + x 1 * x 2 + x 2 ^ 2 := by
    by_contra hle
    push Not at hle
    have hz2 : x 2 ^ 2 = 0 := by nlinarith [sq_nonneg (2 * x 1 + x 2), sq_nonneg (x 2)]
    have hz : x 2 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hz2
    have hy2 : x 1 ^ 2 = 0 := by rw [hz] at hle; nlinarith [sq_nonneg (x 1)]
    have hy : x 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hy2
    have hX2 : (2 : ℤ) ∣ x 0 ^ 2 := ⟨2 * m ^ 2, by rw [hy, hz] at h; nlinarith⟩
    have hX : (2 : ℤ) ∣ x 0 := Int.prime_two.dvd_of_dvd_pow hX2
    exact not_all_dvd x hx 2 Nat.prime_two (by exact_mod_cast hX) (by rw [hy]; simp) (by rw [hz]; simp)
  have hpos : 0 < (2 * m - x 0) * (2 * m + x 0) := by rw [hab]; omega
  have ha0 : 2 * m - x 0 ≠ 0 := left_ne_zero_of_mul hpos.ne'
  have hb0 : 2 * m + x 0 ≠ 0 := right_ne_zero_of_mul hpos.ne'
  obtain ⟨hapos, hbpos⟩ := pos_of_mul_nonneg' ha0 hb0 hpos.le (by omega)
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le hapos.le
  obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le hbpos.le
  have hab' : ((a * b : ℕ) : ℤ) = 3 * (x 1 ^ 2 + x 1 * x 2 + x 2 ^ 2) := by
    push_cast; rw [← ha, ← hb]; exact hab
  have hcop0 : ∀ p : ℕ, p.Prime → p % 3 = 2 → (p : ℤ) ∣ 2 * m - x 0 → (p : ℤ) ∣ 2 * m + x 0 → False := by
    intro p hp hp3 hpa hpb
    have hdiv3 : (p : ℤ) ∣ 3 * (x 1 ^ 2 + x 1 * x 2 + x 2 ^ 2) := by
      rw [← hab]; exact dvd_mul_of_dvd_left hpa _
    obtain ⟨hY, hZ⟩ := dvd_of_dvd_norm_eisenstein p hp hp3 _ _ (dvd_of_dvd_three_mul p hp hp3 _ hdiv3)
    have hX : (p : ℤ) ∣ x 0 := by
      by_cases hp2 : p = 2
      · subst hp2
        have h2 : (2 : ℤ) ∣ 2 * m - x 0 := by exact_mod_cast hpa
        have h3 : (2 : ℤ) ∣ x 0 := by omega
        exact_mod_cast h3
      · have hodd : p % 2 = 1 := by
          rcases hp.eq_two_or_odd with h' | h'
          · exact absurd h' hp2
          · exact h'
        have h2X : (p : ℤ) ∣ 2 ^ 1 * x 0 := by
          have := dvd_sub hpb hpa
          convert this using 1; ring
        exact dvd_of_dvd_two_pow_mul p hp hodd 1 _ h2X
    exact not_all_dvd x hx p hp hX hY hZ
  have h3ab : 3 ∣ a * b := by
    have : (3 : ℤ) ∣ ((a * b : ℕ) : ℤ) := ⟨_, hab'⟩
    exact_mod_cast this
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3ab with h3a | h3b
  · obtain ⟨a', rfl⟩ := h3a
    have ha'pos : 0 < a' := by omega
    have hba' : ((b * a' : ℕ) : ℤ) = x 1 ^ 2 + x 1 * x 2 + x 2 ^ 2 := by
      push_cast at hab' ⊢; linarith
    have key := mod_three_of_norm (x 1) (x 2) b a' (by omega) ha'pos hba' (by omega) ?_
    · omega
    · intro p hp hp3 hpb hpa'
      exact hcop0 p hp hp3 (natCast_dvd_int (Dvd.dvd.mul_left hpa' 3) ha.symm) (natCast_dvd_int hpb hb.symm)
  · obtain ⟨b', rfl⟩ := h3b
    have hb'pos : 0 < b' := by omega
    have hab'' : ((a * b' : ℕ) : ℤ) = x 1 ^ 2 + x 1 * x 2 + x 2 ^ 2 := by
      push_cast at hab' ⊢; linarith
    have key := mod_three_of_norm (x 1) (x 2) a b' (by omega) hb'pos hab'' (by omega) ?_
    · omega
    · intro p hp hp3 hpa hpb'
      exact hcop0 p hp hp3 (natCast_dvd_int hpa ha.symm) (natCast_dvd_int (Dvd.dvd.mul_left hpb' 3) hb.symm)

/-- "Never by both" for $3 \nmid m$ (`ex7f_mod_three` gives $m \equiv 2$, `ex7g_mod_three` gives $m \equiv 1 \pmod 3$).
The general statement for all odd $m > 0$ is `ex7_not_both`. -/
theorem ex7_not_both_of_not_dvd_three (m : ℤ) (hm0 : 0 < m) (hm2 : m % 2 = 1) (hm3 : m % 3 ≠ 0) :
    ¬ ((∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex7f.eval x = 4 * m ^ 2) ∧
      (∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex7g.eval x = 4 * m ^ 2)) := by
  rintro ⟨⟨x, hx, h⟩, ⟨y, hy, h'⟩⟩
  have h1 := ex7f_mod_three m hm0 hm2 hm3 x hx h
  have h2 := ex7g_mod_three m hm0 hm2 hm3 y hy h'
  omega

/-- Helper: if $9 \mid a^2 + ab + b^2$ then $3 \mid a$ and $3 \mid b$. -/
theorem three_dvd_of_nine_dvd_norm (a b : ℤ) (h : (9 : ℤ) ∣ a ^ 2 + a * b + b ^ 2) : 3 ∣ a ∧ 3 ∣ b := by
  have h3 : (3 : ℤ) ∣ (a - b) ^ 2 := by
    have e : (a - b) ^ 2 = (a ^ 2 + a * b + b ^ 2) - 3 * (a * b) := by ring
    rw [e]; exact dvd_sub (dvd_trans (by norm_num) h) (dvd_mul_right _ _)
  obtain ⟨k, hk⟩ := Int.prime_three.dvd_of_dvd_pow h3
  have h9 : (3 : ℤ) * 3 ∣ 3 * (a * b) := by
    have e : 3 * (a * b) = (a ^ 2 + a * b + b ^ 2) - (a - b) ^ 2 := by ring
    rw [e, hk]; exact dvd_sub (by simpa using h) ⟨k ^ 2, by ring⟩
  have h4 : (3 : ℤ) ∣ a * b := (mul_dvd_mul_iff_left (by norm_num : (3 : ℤ) ≠ 0)).mp h9
  rcases Int.prime_three.dvd_or_dvd h4 with ha | hb
  · exact ⟨ha, by omega⟩
  · exact ⟨by omega, hb⟩

/-- Helper: $a^2 + ab + b^2 = 0$ forces $a = b = 0$. -/
theorem norm_eq_zero_eisenstein (a b : ℤ) (h : a ^ 2 + a * b + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  have hb : b ^ 2 = 0 := by nlinarith [sq_nonneg (2 * a + b), sq_nonneg b]
  have hb0 : b = 0 := pow_eq_zero_iff two_ne_zero |>.mp hb
  subst hb0
  have : a ^ 2 = 0 := by simpa using h
  exact ⟨pow_eq_zero_iff two_ne_zero |>.mp this, rfl⟩

/-- **Example 7 (ii), the case $3 \mid m$ for $f$.** If $m = 3m'$ with $m' > 0$ odd and $4m^2$ is represented primitively
by $f = x_0^2 + x_0x_1 + x_1^2 + 9x_2^2$, then $m' \equiv 1 \pmod 3$. *Proof:* mod $9$ forces $3 \mid x_0, x_1$,
$x_0 = 3u$, $x_1 = 3v$, and $4m'^2 = u^2 + uv + v^2 + x_2^2$ with $3 \nmid x_2$ (primitivity); mod $3$ this gives
$3 \nmid m'$ and $3 \mid u^2 + uv + v^2 = (2m' - x_2)(2m' + x_2)$; exactly one factor is divisible by $3$, the other
is $\equiv 1 \pmod 3$ by the inert-prime argument (`mod_three_of_norm`), whence $m' \equiv 1 \pmod 3$. -/
theorem ex7f_three_dvd (m' : ℤ) (hm0 : 0 < m') (hm2 : m' % 2 = 1) (x : Fin 3 → ℤ)
    (hx : Finset.univ.gcd x = 1) (h : ex7f.eval x = 4 * (3 * m') ^ 2) : m' % 3 = 1 := by
  rw [eval_ex7f] at h
  have h9 : (9 : ℤ) ∣ x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2 := ⟨4 * m' ^ 2 - x 2 ^ 2, by linear_combination h⟩
  obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := three_dvd_of_nine_dvd_norm _ _ h9
  have hz3 : ¬ (3 : ℤ) ∣ x 2 := fun hz =>
    not_all_dvd x hx 3 Nat.prime_three (by exact_mod_cast (show (3 : ℤ) ∣ x 0 from ⟨u, hu⟩))
      (by exact_mod_cast (show (3 : ℤ) ∣ x 1 from ⟨v, hv⟩)) (by exact_mod_cast hz)
  have E : 4 * m' ^ 2 = u ^ 2 + u * v + v ^ 2 + x 2 ^ 2 := by
    have h' : (9 : ℤ) * (4 * m' ^ 2) = 9 * (u ^ 2 + u * v + v ^ 2 + x 2 ^ 2) := by
      rw [hu, hv] at h; linear_combination (-1 : ℤ) * h
    exact mul_left_cancel₀ (by norm_num) h'
  have hmod : ¬ (3 : ℤ) ∣ m' ∧ (3 : ℤ) ∣ (u ^ 2 + u * v + v ^ 2) := by
    have hc : ((4 * m' ^ 2 : ℤ) : ZMod 3) = ((u ^ 2 + u * v + v ^ 2 + x 2 ^ 2 : ℤ) : ZMod 3) := by rw [E]
    push_cast at hc
    have key : ∀ (m u v z : ZMod 3), 4 * m ^ 2 = u ^ 2 + u * v + v ^ 2 + z ^ 2 → z ≠ 0 →
        m ≠ 0 ∧ u ^ 2 + u * v + v ^ 2 = 0 := by decide
    have hz0 : ((x 2 : ℤ) : ZMod 3) ≠ 0 := fun h0 =>
      hz3 (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h0)
    obtain ⟨h1, h2⟩ := key _ _ _ _ hc hz0
    refine ⟨fun hd => h1 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (by exact_mod_cast hd)), ?_⟩
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (u ^ 2 + u * v + v ^ 2) 3).mp (by push_cast; exact h2)
    exact_mod_cast this
  obtain ⟨hm3, h3N⟩ := hmod
  have hab : (2 * m' - x 2) * (2 * m' + x 2) = u ^ 2 + u * v + v ^ 2 := by linear_combination E
  have hcop0 : ∀ p : ℕ, p.Prime → p % 3 = 2 → (p : ℤ) ∣ 2 * m' - x 2 → (p : ℤ) ∣ 2 * m' + x 2 → False := by
    intro p hp hp3 hpa hpb
    have hdiv : (p : ℤ) ∣ u ^ 2 + u * v + v ^ 2 := by rw [← hab]; exact dvd_mul_of_dvd_left hpa _
    obtain ⟨hU, hV⟩ := dvd_of_dvd_norm_eisenstein p hp hp3 _ _ hdiv
    have hZ : (p : ℤ) ∣ x 2 := by
      by_cases hp2 : p = 2
      · subst hp2
        have h2 : (2 : ℤ) ∣ 2 * m' - x 2 := by exact_mod_cast hpa
        have h3 : (2 : ℤ) ∣ x 2 := by omega
        exact_mod_cast h3
      · have hodd : p % 2 = 1 := by
          rcases hp.eq_two_or_odd with h' | h'
          · exact absurd h' hp2
          · exact h'
        have h2z : (p : ℤ) ∣ 2 ^ 1 * x 2 := by
          have := dvd_sub hpb hpa
          convert this using 1; ring
        exact dvd_of_dvd_two_pow_mul p hp hodd 1 _ h2z
    exact not_all_dvd x hx p hp (by rw [hu]; exact Dvd.dvd.mul_left hU 3)
      (by rw [hv]; exact Dvd.dvd.mul_left hV 3) hZ
  have hnn : 0 ≤ (2 * m' - x 2) * (2 * m' + x 2) := by
    rw [hab]; nlinarith [sq_nonneg (u + v), sq_nonneg u, sq_nonneg v]
  have hzero : (2 * m' - x 2) * (2 * m' + x 2) = 0 → False := by
    intro h0
    rw [hab] at h0
    obtain ⟨hu0, hv0⟩ := norm_eq_zero_eisenstein u v h0
    have hne : (2 * m' - x 2) = 0 ∨ (2 * m' + x 2) = 0 := by
      rcases mul_eq_zero.mp (by rw [hab]; exact h0) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
    have h2z : (2 : ℤ) ∣ x 2 := by omega
    exact not_all_dvd x hx 2 Nat.prime_two (by rw [hu, hu0]; simp) (by rw [hv, hv0]; simp)
      (by exact_mod_cast h2z)
  have ha0 : 2 * m' - x 2 ≠ 0 := fun h0 => hzero (by rw [h0, zero_mul])
  have hb0 : 2 * m' + x 2 ≠ 0 := fun h0 => hzero (by rw [h0, mul_zero])
  obtain ⟨hapos, hbpos⟩ := pos_of_mul_nonneg' ha0 hb0 hnn (by omega)
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le hapos.le
  obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le hbpos.le
  have hab' : ((a * b : ℕ) : ℤ) = u ^ 2 + u * v + v ^ 2 := by
    push_cast; rw [← ha, ← hb]; exact hab
  have h3ab : 3 ∣ a * b := by
    have : (3 : ℤ) ∣ ((a * b : ℕ) : ℤ) := by rw [hab']; exact h3N
    exact_mod_cast this
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3ab with h3a | h3b
  · have hba : ((b * a : ℕ) : ℤ) = u ^ 2 + u * v + v ^ 2 := by rw [mul_comm]; exact hab'
    have key := mod_three_of_norm u v b a (by omega) (by omega) hba (by omega) ?_
    · omega
    · intro p hp hp3 hpb hpa
      exact hcop0 p hp hp3 (natCast_dvd_int hpa ha.symm) (natCast_dvd_int hpb hb.symm)
  · have key := mod_three_of_norm u v a b (by omega) (by omega) hab' (by omega) ?_
    · omega
    · intro p hp hp3 hpa hpb
      exact hcop0 p hp hp3 (natCast_dvd_int hpa ha.symm) (natCast_dvd_int hpb hb.symm)

/-- **Example 7 (ii), the case $3 \mid m$ for $g$.** If $m = 3m'$ with $m' > 0$ odd and $4m^2$ is represented primitively
by $g = x_0^2 + 3(x_1^2 + x_1x_2 + x_2^2)$, then $m' \equiv 2 \pmod 3$. *Proof:* $x_0 = 3w$, $x_1 = x_2 + 3s$,
$3 \nmid x_2$, and $w^2 + x_2^2 + 3x_2s + 3s^2 = 4m'^2$; mod $3$ gives $3 \mid w$, $3 \nmid m'$; the right side is
$(2m' - w)(2m' + w) = M^2 + MS + S^2$ with $M = x_2 + s$, $S = s$; both factors are $\equiv 2m' \pmod 3$ and the first is
$\equiv 1 \pmod 3$ by `mod_three_of_norm`, whence $m' \equiv 2 \pmod 3$. -/
theorem ex7g_three_dvd (m' : ℤ) (hm0 : 0 < m') (hm2 : m' % 2 = 1) (x : Fin 3 → ℤ)
    (hx : Finset.univ.gcd x = 1) (h : ex7g.eval x = 4 * (3 * m') ^ 2) : m' % 3 = 2 := by
  rw [eval_ex7g] at h
  have hX : (3 : ℤ) ∣ x 0 := by
    have : (3 : ℤ) ∣ x 0 ^ 2 := ⟨12 * m' ^ 2 - (x 1 ^ 2 + x 1 * x 2 + x 2 ^ 2), by linear_combination h⟩
    exact Int.prime_three.dvd_of_dvd_pow this
  obtain ⟨w, hw⟩ := hX
  have h' : 3 * (x 1 ^ 2 + x 1 * x 2 + x 2 ^ 2) + 9 * w ^ 2 = 36 * m' ^ 2 := by
    rw [hw] at h; linear_combination h
  have h3 : (3 : ℤ) ∣ (x 1 - x 2) ^ 2 := by
    have e : 3 * (x 1 - x 2) ^ 2 = 3 * (3 * (4 * m' ^ 2 - w ^ 2 - x 1 * x 2)) := by linear_combination h'
    exact ⟨4 * m' ^ 2 - w ^ 2 - x 1 * x 2, mul_left_cancel₀ (by norm_num : (3 : ℤ) ≠ 0) e⟩
  obtain ⟨s, hs⟩ := Int.prime_three.dvd_of_dvd_pow h3
  have hY : x 1 = x 2 + 3 * s := by omega
  have hY3 : ¬ (3 : ℤ) ∣ x 1 := fun hy =>
    not_all_dvd x hx 3 Nat.prime_three (by exact_mod_cast (show (3 : ℤ) ∣ x 0 from ⟨w, hw⟩))
      (by exact_mod_cast hy) (by exact_mod_cast (show (3 : ℤ) ∣ x 2 by omega))
  have hZ3 : ¬ (3 : ℤ) ∣ x 2 := by omega
  have E : w ^ 2 + x 2 ^ 2 + 3 * x 2 * s + 3 * s ^ 2 = 4 * m' ^ 2 := by
    have e : (9 : ℤ) * (w ^ 2 + x 2 ^ 2 + 3 * x 2 * s + 3 * s ^ 2) = 9 * (4 * m' ^ 2) := by
      rw [hY] at h'; linear_combination h'
    exact mul_left_cancel₀ (by norm_num) e
  have hmod : (3 : ℤ) ∣ w ∧ ¬ (3 : ℤ) ∣ m' := by
    have hc : ((w ^ 2 + x 2 ^ 2 + 3 * x 2 * s + 3 * s ^ 2 : ℤ) : ZMod 3) = ((4 * m' ^ 2 : ℤ) : ZMod 3) := by
      rw [E]
    push_cast at hc
    have key : ∀ (w z s m : ZMod 3), w ^ 2 + z ^ 2 + 3 * z * s + 3 * s ^ 2 = 4 * m ^ 2 → z ≠ 0 →
        w = 0 ∧ m ≠ 0 := by decide
    have hz0 : ((x 2 : ℤ) : ZMod 3) ≠ 0 := fun h0 =>
      hZ3 (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h0)
    obtain ⟨h1, h2⟩ := key _ _ _ _ hc hz0
    refine ⟨by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd w 3).mp h1,
      fun hd => h2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (by exact_mod_cast hd))⟩
  obtain ⟨hw3, hm3⟩ := hmod
  have hab : (2 * m' - w) * (2 * m' + w) = (x 2 + s) ^ 2 + (x 2 + s) * s + s ^ 2 := by
    linear_combination (-1 : ℤ) * E
  have hcop0 : ∀ p : ℕ, p.Prime → p % 3 = 2 → (p : ℤ) ∣ 2 * m' - w → (p : ℤ) ∣ 2 * m' + w → False := by
    intro p hp hp3 hpa hpb
    have hdiv : (p : ℤ) ∣ (x 2 + s) ^ 2 + (x 2 + s) * s + s ^ 2 := by
      rw [← hab]; exact dvd_mul_of_dvd_left hpa _
    obtain ⟨hM, hS⟩ := dvd_of_dvd_norm_eisenstein p hp hp3 _ _ hdiv
    have hZ : (p : ℤ) ∣ x 2 := by
      have := dvd_sub hM hS; simpa using this
    have hW : (p : ℤ) ∣ w := by
      by_cases hp2 : p = 2
      · subst hp2
        have h2 : (2 : ℤ) ∣ 2 * m' - w := by exact_mod_cast hpa
        have h3 : (2 : ℤ) ∣ w := by omega
        exact_mod_cast h3
      · have hodd : p % 2 = 1 := by
          rcases hp.eq_two_or_odd with h' | h'
          · exact absurd h' hp2
          · exact h'
        have h2w : (p : ℤ) ∣ 2 ^ 1 * w := by
          have := dvd_sub hpb hpa
          convert this using 1; ring
        exact dvd_of_dvd_two_pow_mul p hp hodd 1 _ h2w
    have hX : (p : ℤ) ∣ x 0 := by rw [hw]; exact Dvd.dvd.mul_left hW 3
    have hY' : (p : ℤ) ∣ x 1 := by rw [hY]; exact dvd_add hZ (Dvd.dvd.mul_left hS 3)
    exact not_all_dvd x hx p hp hX hY' hZ
  have hnn : 0 ≤ (2 * m' - w) * (2 * m' + w) := by
    rw [hab]; nlinarith [sq_nonneg (x 2 + s + s), sq_nonneg (x 2 + s), sq_nonneg s]
  have hzero : (2 * m' - w) * (2 * m' + w) = 0 → False := by
    intro h0
    rw [hab] at h0
    obtain ⟨hM0, hS0⟩ := norm_eq_zero_eisenstein _ _ h0
    omega
  have ha0 : 2 * m' - w ≠ 0 := fun h0 => hzero (by rw [h0, zero_mul])
  have hb0 : 2 * m' + w ≠ 0 := fun h0 => hzero (by rw [h0, mul_zero])
  obtain ⟨hapos, hbpos⟩ := pos_of_mul_nonneg' ha0 hb0 hnn (by omega)
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le hapos.le
  obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le hbpos.le
  have hab' : ((a * b : ℕ) : ℤ) = (x 2 + s) ^ 2 + (x 2 + s) * s + s ^ 2 := by
    push_cast; rw [← ha, ← hb]; exact hab
  have key := mod_three_of_norm (x 2 + s) s a b (by omega) (by omega) hab' (by omega) ?_
  · omega
  · intro p hp hp3 hpa hpb
    exact hcop0 p hp hp3 (natCast_dvd_int hpa ha.symm) (natCast_dvd_int hpb hb.symm)

/-- **Cassels, Ch. 11, Example 7 (ii), "never by both"**, for *every* odd $m > 0$: $4m^2$ is not represented primitively by
both $f = x^2 + xy + y^2 + 9z^2$ and $g = x^2 + 3(y^2 + yz + z^2)$. For $3 \nmid m$ this is
`ex7_not_both_of_not_dvd_three` ($m \equiv 2$ versus $m \equiv 1 \pmod 3$); for $m = 3m'$ it is `ex7f_three_dvd`
($m' \equiv 1$) versus `ex7g_three_dvd` ($m' \equiv 2 \pmod 3$). Unconditional. Arguments: `m` the positive odd integer. -/
@[kb "cassels1978" "Ch. 11, Ex. 7 (ii), p. 252 (never by both, all odd m)"]
theorem ex7_not_both (m : ℤ) (hm0 : 0 < m) (hm2 : m % 2 = 1) :
    ¬ ((∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex7f.eval x = 4 * m ^ 2) ∧
      (∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex7g.eval x = 4 * m ^ 2)) := by
  by_cases hm3 : m % 3 = 0
  · obtain ⟨m', rfl⟩ : ∃ m' : ℤ, m = 3 * m' := ⟨m / 3, by omega⟩
    rintro ⟨⟨x, hx, h⟩, ⟨y, hy, h'⟩⟩
    have h1 := ex7f_three_dvd m' (by omega) (by omega) x hx h
    have h2 := ex7g_three_dvd m' (by omega) (by omega) y hy h'
    omega
  · exact ex7_not_both_of_not_dvd_three m hm0 hm2 hm3

/-! ### Transport of primitive representations, and genera with prescribed classes -/

/-- Helper: primitive representations are transported along integral equivalence: if $Q(T\vec x) = Q'(\vec x)$ for
some $T \in \mathrm{GL}_3(\mathbb Z)$ and $Q'$ represents $a$ primitively, so does $Q$ (the image vector $T\vec x$ is
again primitive since $T$ is invertible over $\mathbb Z$). -/
theorem primRep_of_intEquiv {Q Q' : QuadForm ℤ 3} (h : IntEquiv Q Q') {a : ℤ}
    (hx : ∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ Q'.eval x = a) :
    ∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ Q.eval x = a := by
  obtain ⟨x, hx1, hxa⟩ := hx
  obtain ⟨g, hg⟩ := h
  refine ⟨g.val *ᵥ x, ?_, by rw [hg, hxa]⟩
  have hdvd : Finset.univ.gcd (g.val *ᵥ x) ∣ Finset.univ.gcd x := by
    refine Finset.dvd_gcd fun i _ => ?_
    have e : x = (g⁻¹ : GL (Fin 3) ℤ).val *ᵥ (g.val *ᵥ x) := by
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    have e' : x i = ∑ j, (g⁻¹ : GL (Fin 3) ℤ).val i j * (g.val *ᵥ x) j := congrFun e i
    rw [e']
    exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_left (Finset.gcd_dvd (Finset.mem_univ j)) _
  rw [hx1] at hdvd
  exact Int.eq_one_of_dvd_one (Int.nonneg_of_normalize_eq_self Finset.normalize_gcd) hdvd

/-- Helper: a genus with exactly one class (`Set.ncard` of the set of classes is $1$) consists of the class of the
given form: every form of the genus is integrally equivalent to it. -/
theorem intEquiv_of_ncard_genusClasses_eq_one {Q : QuadForm ℤ 3} (h : (genusClasses Q).ncard = 1)
    (Q' : QuadForm ℤ 3) (hQ' : SameGenus Q Q') : IntEquiv Q Q' := by
  obtain ⟨c, hc⟩ := Set.ncard_eq_one.mp h
  have h1 := classOf_self_mem_genusClasses Q
  have h2 := classOf_mem_genusClasses_iff.mpr hQ'
  rw [hc, Set.mem_singleton_iff] at h1 h2
  exact classOf_eq_classOf_iff.mp (h1.trans h2.symm)

/-- Helper: a genus with exactly two classes (`Set.ncard` of the set of classes is $2$), containing the inequivalent
forms $Q$ and $Q_2$, consists of exactly the classes of $Q$ and $Q_2$. -/
theorem intEquiv_or_of_ncard_genusClasses_eq_two {Q Q₂ : QuadForm ℤ 3} (h : (genusClasses Q).ncard = 2)
    (h₂ : SameGenus Q Q₂) (hne : ¬ IntEquiv Q Q₂) (Q' : QuadForm ℤ 3) (hQ' : SameGenus Q Q') :
    IntEquiv Q Q' ∨ IntEquiv Q₂ Q' := by
  have hfin : (genusClasses Q).Finite := Set.finite_of_ncard_ne_zero (by omega)
  have hsub : ({classOf Q, classOf Q₂} : Set (QClass 3)) ⊆ genusClasses Q := by
    intro c hc
    rcases hc with rfl | rfl
    · exact classOf_self_mem_genusClasses Q
    · exact classOf_mem_genusClasses_iff.mpr h₂
  have hne' : classOf Q ≠ classOf Q₂ := fun he => hne (classOf_eq_classOf_iff.mp he)
  have hcard : (genusClasses Q).ncard ≤ ({classOf Q, classOf Q₂} : Set (QClass 3)).ncard := by
    rw [Set.ncard_pair hne', h]
  have heq := (Set.eq_of_subset_of_ncard_le hsub hcard hfin).symm
  have hmem : classOf Q' ∈ ({classOf Q, classOf Q₂} : Set (QClass 3)) := by
    rw [← heq]; exact classOf_mem_genusClasses_iff.mpr hQ'
  rcases hmem with h1 | h1
  · exact Or.inl (classOf_eq_classOf_iff.mp h1.symm)
  · exact Or.inr (classOf_eq_classOf_iff.mp h1.symm)

/-! ### Example 3: the genus of $f$ has one class -/

/-- **Cassels, Ch. 11, Example 3** (p. 251), named statement: *$f = x^2 + 5y^2 - 25z^2$ is in a genus of one class*,
i.e. the set of classes (`genusClasses`) of forms of the genus of `ex3f` has exactly one element. *Not proved:* here
$\det = -125$ and $5^3 \mid \det$, so Theorem 1.5 (the method of `ex1_properIntEquiv_of_sameGenus`) does not apply
directly. The natural route (not printed in the book) is to show that the genus is one spinor genus, via the group $G$ of
(3.15) and the local spinor norm groups, and then use Theorem 1.4 (an indefinite spinor genus is one class). A full proof
needs the local spinor norm group of the $\mathbb Z_5$-lattice of Jordan type $\langle 1\rangle \perp \langle 5\rangle \perp
\langle 25\rangle$ (for which Example 4, `Ex4Statement`, is the tool; its easy half is `ex4_closure_le`) and the $2$-adic
one, then the evaluation of $G$. The equivalence with $g = -x^2 + 5y^2 + 25z^2$ is proved unconditionally
(`ex3_properIntEquiv`); the consequence "$g$ is in the genus of $f$" is `ex3_sameGenus`. -/
@[kb "cassels1978" "Ch. 11, Ex. 3, p. 251 (genus of one class)"]
structure Ex3OneClass : Prop where
  /-- The genus of $f$ has exactly one class. -/
  holds : (genusClasses ex3f).ncard = 1

/-- The forms $f$ and $g$ of Example 3 are in the same genus (they are equivalent, `ex3_properIntEquiv`). -/
theorem ex3_sameGenus : SameGenus ex3f ex3g := ex3_properIntEquiv.intEquiv.sameGenus

/-- **Example 3, the deduction** (p. 251): *deduce that $f$ is integrally equivalent to $g$*: given that the genus of
$f$ has one class (`Ex3OneClass`), the form $g$ of the genus is equivalent to $f$. (Unconditionally, the equivalence is
`ex3_properIntEquiv`.) -/
theorem Ex3OneClass.intEquiv (h : Ex3OneClass) : IntEquiv ex3f ex3g :=
  intEquiv_of_ncard_genusClasses_eq_one h.holds ex3g ex3_sameGenus

/-! ### Examples 6 and 7: the genus statements (named) and the representation theorem -/

/-- Helper: $f = x_0^2 + x_1^2 + 16x_2^2$ evaluated over any commutative ring after base change from $\mathbb Z$. -/
theorem eval_map_ex6f {R : Type*} [CommRing R] (x : Fin 3 → R) :
    (ex6f.map (Int.castRingHom R)).eval x = x 0 ^ 2 + x 1 ^ 2 + 16 * x 2 ^ 2 := by
  simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_three, ex6f, QuadForm.diag, QuadForm.map,
    Matrix.diagonal_apply]
  ring

/-- Helper: $f = x_0^2 + x_1^2 + 16x_2^2$ evaluated over a field containing $\mathbb Z$. -/
theorem evalIn_ex6f {K : Type*} [Field K] [Algebra ℤ K] (x : Fin 3 → K) :
    ex6f.evalIn K x = x 0 ^ 2 + x 1 ^ 2 + 16 * x 2 ^ 2 := by
  simp [QuadForm.evalIn, Fin.sum_univ_three, ex6f, QuadForm.diag, Matrix.diagonal_apply]
  ring

/-- Helper: the Hessian determinant of $f = x_0^2 + x_1^2 + 16x_2^2$ is $128$. -/
theorem hessian_det_ex6f : ex6f.hessian.det = 128 := by
  rw [ex6f, hessian_diag, det_diagonal, Fin.prod_univ_three]
  simp

/-- Helper: $x_0^2 + x_0x_1 + x_1^2 + 9x_2^2$ evaluated over any commutative ring after base change from $\mathbb Z$. -/
theorem eval_map_ex7f {R : Type*} [CommRing R] (x : Fin 3 → R) :
    (ex7f.map (Int.castRingHom R)).eval x = x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2 + 9 * x 2 ^ 2 := by
  simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_three, ex7f, QuadForm.ofUpper, QuadForm.map]
  ring

/-- Helper: $x_0^2 + x_0x_1 + x_1^2 + 9x_2^2$ evaluated over a field containing $\mathbb Z$. -/
theorem evalIn_ex7f {K : Type*} [Field K] [Algebra ℤ K] (x : Fin 3 → K) :
    ex7f.evalIn K x = x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2 + 9 * x 2 ^ 2 := by
  simp [QuadForm.evalIn, Fin.sum_univ_three, ex7f, QuadForm.ofUpper]
  ring

/-- Helper: the Hessian determinant of $f = x_0^2 + x_0x_1 + x_1^2 + 9x_2^2$ is $54$. -/
theorem hessian_det_ex7f : ex7f.hessian.det = 54 := by
  have : ex7f.hessian = !![2, 1, 0; 1, 2, 0; 0, 0, 18] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [QuadForm.hessian, ex7f, QuadForm.ofUpper]
  rw [this, det_fin_three]; simp

/-- Helper: a prime dividing $128 = 2^7$ is $2$. -/
theorem prime_dvd_128 (p : ℕ) (hp : p.Prime) (h : p ∣ 128) : p = 2 := by
  have h' : p ∣ 2 ^ 7 := by norm_num; exact h
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h')

/-- Helper: a prime dividing $54 = 2 \cdot 3^3$ is $2$ or $3$. -/
theorem prime_dvd_54 (p : ℕ) (hp : p.Prime) (h : p ∣ 54) : p = 2 ∨ p = 3 := by
  have h' : p ∣ 2 * 3 ^ 3 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h2 | h3
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3))

/-! ### Example 6 (iv): the genus of $f$ is $\{f, g\}$, hence $m^2$ is primitively represented by exactly one -/

/-- **Cassels, Ch. 11, Example 6 (i) (iii)** (p. 252), named statement for the class content: *the genus of
$f = x^2 + y^2 + 16z^2$ consists of two spinor genera, those of $f$ and of $g = (x - y)^2 + (x + y + z)^2 + 4z^2$, and
each of them has precisely one class*. As far as classes are concerned this says: $g$ is in the genus of $f$
(`sameGenus`) and the genus has exactly two classes (`two_classes`, counted by `Set.ncard`, which is $0$ for an infinite
set); the classes are then those of $f$ and of $g$ since $f$ and $g$ are not equivalent (`ex6_not_intEquiv`, proved
from Example 6 (iv)). *Proved* in `Ch11Ex6Classes.lean` (`ex6Classes_holds`: Minkowski reduction and a finite check). The original note: a full proof needs either the enumeration of all positive definite ternary
classes of determinant $16$ (the "heroic" way of the hint, by the reduction theory of Chapter 9, which the library
does not have for ternary forms) or the technique of Theorem 8.4, Corollary 2 with a chain of lattices with
$I(\Lambda_j, \Lambda_{j+1}) = 3$ (neighbors), together with the computation of the group $G$ (`Ex6SpinorGenera`).
Numerical check: all $9$ classes of determinant-$128$ Hessians (Minkowski-reduced enumeration) fall into the genus of
$f$ (same representation counts modulo $8$, $16$, $9$, $27$) exactly twice, with representatives $f$ and $g$.
The inclusion of `sameGenus` as a field is needed: `ncard = 2` alone does not say which classes occur. -/
@[kb "cassels1978" "Ch. 11, Ex. 6 (i), (iii), p. 252 (classes in the genus)"]
structure Ex6Classes : Prop where
  /-- $g$ is in the genus of $f$. -/
  sameGenus : SameGenus ex6f ex6g
  /-- The genus of $f$ has exactly two classes. -/
  two_classes : (genusClasses ex6f).ncard = 2

/-- **Example 6 (iv), necessity, "never both"**: an odd square $m^2$, $m > 0$, is never primitively represented by both
$f$ and $g$ (`ex6f_mod_four` and `ex6g_mod_four`). Unconditional. -/
@[kb "cassels1978" "Ch. 11, Ex. 6 (iv), p. 252 (at most one of f, g)"]
theorem ex6_not_both (m : ℤ) (hm0 : 0 < m) (hm2 : m % 2 = 1) :
    ¬ ((∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex6f.eval x = m ^ 2) ∧
      (∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex6g.eval x = m ^ 2)) := by
  rintro ⟨⟨x, hx, h⟩, ⟨y, hy, h'⟩⟩
  have h1 := ex6f_mod_four m hm0 hm2 x hx h
  have h2 := ex6g_mod_four m hm0 hm2 y hy h'
  omega

/-- The forms $f$ and $g$ of Example 6 are not integrally equivalent (the odd square $1$ is primitively represented by
$f$, but a primitive representation by $g$ would force $1 \equiv 3 \pmod 4$). -/
theorem ex6_not_intEquiv : ¬ IntEquiv ex6f ex6g := by
  intro h
  have h1 : ∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex6f.eval x = 1 ^ 2 :=
    ⟨![1, 0, 0], by simp [Fin.univ_succ, Finset.gcd_insert], by rw [eval_ex6f]; simp⟩
  obtain ⟨x, hx, hxe⟩ := primRep_of_intEquiv (IsometricGL.symm h : IntEquiv ex6g ex6f) h1
  have := ex6g_mod_four 1 one_pos (by norm_num) x hx hxe
  omega

/-- Helper: every form in the genus of $f$ is equivalent to $f$ or to $g$ (Example 6, given `Ex6Classes`). -/
theorem Ex6Classes.classes (h : Ex6Classes) (f' : QuadForm ℤ 3) (hf' : SameGenus ex6f f') :
    IntEquiv ex6f f' ∨ IntEquiv ex6g f' :=
  intEquiv_or_of_ncard_genusClasses_eq_two h.two_classes h.sameGenus ex6_not_intEquiv f' hf'

/-- Helper: $2$-adic primitive representation of an odd square by $f$: the vector $(m, 0, 0)$. -/
theorem ex6_local_two (m : ℤ) (hm2 : m % 2 = 1) :
    ∃ x : Fin 3 → ℤ_[2], (∃ i, IsUnit (x i)) ∧ (ex6f.map (Int.castRingHom ℤ_[2])).eval x = m ^ 2 := by
  refine ⟨![(m : ℤ_[2]), 0, 0], ⟨0, ?_⟩, ?_⟩
  · simpa using (isUnit_intCast_padic (p := 2) m).mpr (by omega)
  · rw [eval_map_ex6f]
    simp

/-- Helper: the genus of $f$ contains a form representing the odd square $m^2$ primitively (Chapter 9, Theorem 5.1;
the only local condition is at $p = 2 \mid 128 = \det H$). -/
theorem ex6_genus_primRep (m : ℤ) (hm0 : 0 < m) (hm2 : m % 2 = 1) :
    ∃ f' : QuadForm ℤ 3, SameGenus ex6f f' ∧ ∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ f'.eval x = m ^ 2 := by
  refine exists_sameGenus_primRep ex6f (by norm_num) (by rw [hessian_det_ex6f]; norm_num) (a := m ^ 2)
    (by positivity) ⟨![(m : ℝ), 0, 0], by rw [evalIn_ex6f]; simp⟩ ?_
  intro p _ hc
  have hp2 : p = 2 := by
    rcases hc with h | h | ⟨h, -⟩
    · exact h
    · rw [hessian_det_ex6f] at h
      exact prime_dvd_128 p Fact.out (by exact_mod_cast h)
    · omega
  subst hp2
  exact ex6_local_two m hm2

/-- **Cassels, Ch. 11, Example 6 (iv)** (p. 252): *every odd square $m^2$ is primitively representable by precisely one
of $f = x^2 + y^2 + 16z^2$, $g = (x - y)^2 + (x + y + z)^2 + 4z^2$; indeed it is representable by $f$ or $g$ according
as $m \equiv 1$ or $m \equiv 3 \pmod 4$, where $m > 0$.* Conditional on the class content of (i), (iii)
(`Ex6Classes`, named); the necessity half (`ex6f_mod_four`, `ex6g_mod_four`) is unconditional and elementary.
Sufficiency: by Chapter 9, Theorem 5.1 (`exists_sameGenus_primRep`) some form of the genus of $f$ represents $m^2$
primitively (locally: $(m, 0, 0)$ at $p = 2$), that form is equivalent to $f$ or to $g$, and the congruence
conditions exclude the wrong one. Arguments: `hcl` the class content, `m` the positive odd integer. -/
@[kb "cassels1978" "Ch. 11, Ex. 6 (iv), p. 252"]
theorem ex6_primRep_iff (hcl : Ex6Classes) (m : ℤ) (hm0 : 0 < m) (hm2 : m % 2 = 1) :
    ((∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex6f.eval x = m ^ 2) ↔ m % 4 = 1) ∧
      ((∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex6g.eval x = m ^ 2) ↔ m % 4 = 3) := by
  obtain ⟨f', hg, hrep⟩ := ex6_genus_primRep m hm0 hm2
  have hex : (∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex6f.eval x = m ^ 2) ∨
      (∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex6g.eval x = m ^ 2) := by
    rcases hcl.classes f' hg with he | he
    · exact Or.inl (primRep_of_intEquiv he hrep)
    · exact Or.inr (primRep_of_intEquiv he hrep)
  constructor
  · constructor
    · rintro ⟨x, hx, h⟩
      exact ex6f_mod_four m hm0 hm2 x hx h
    · intro h4
      rcases hex with hf | ⟨x, hx, h⟩
      · exact hf
      · have := ex6g_mod_four m hm0 hm2 x hx h
        omega
  · constructor
    · rintro ⟨x, hx, h⟩
      exact ex6g_mod_four m hm0 hm2 x hx h
    · intro h4
      rcases hex with ⟨x, hx, h⟩ | hg'
      · have := ex6f_mod_four m hm0 hm2 x hx h
        omega
      · exact hg'

/-- **Example 6 (iv), "precisely one"**: under `Ex6Classes`, an odd square $m^2$, $m > 0$, is primitively represented
by $f$ or by $g$, and not by both. -/
theorem ex6_primRep_exactly_one (hcl : Ex6Classes) (m : ℤ) (hm0 : 0 < m) (hm2 : m % 2 = 1) :
    ((∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex6f.eval x = m ^ 2) ∨
      (∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex6g.eval x = m ^ 2)) ∧
    ¬ ((∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex6f.eval x = m ^ 2) ∧
      (∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex6g.eval x = m ^ 2)) := by
  have h := ex6_primRep_iff hcl m hm0 hm2
  refine ⟨?_, ex6_not_both m hm0 hm2⟩
  by_cases h4 : m % 4 = 1
  · exact Or.inl (h.1.mpr h4)
  · exact Or.inr (h.2.mpr (by omega))

/-! ### Example 6 (i), (ii): the group $G$ and the number of spinor genera (named) -/

/-- **Cassels, Ch. 11, Example 6 (i), (ii)** (p. 252), named statement for the spinor-genus content, for the lattice
$\mathbb Z^3$ with the form $f = x^2 + y^2 + 16z^2$ (`ex6f`, over $\mathbb Q$) and a prime `v₂` of $\mathbb Q$ over $2$:
(i) the set $P$ of (3.15) can be taken to be $\{2\}$ (field `unitsAway`: for every prime $v \ne v_2$ the local spinor
norm group is $\theta(\Lambda_v) = U_v(\mathbb Q_v^\times)^2$, condition (3.7)), the group $G$ of (3.15) has order $2$
(`orderG`), and so the genus consists of two spinor genera (`spinorGenusNumber`, the number $g^+$ of proper spinor
genera, which are Cassels' spinor genera); (ii) in the notation of Theorem 4.1, $g(w) \in G$ ($g$ = `casselsg`,
(4.5)) for an odd positive integer $w$ is the identity precisely when $w \equiv 1 \pmod 4$ (`g_odd`). *Not proved.*
A full proof needs: (a) the spinor norm group $\theta(\Lambda_2)$ of the $2$-adic lattice $\langle 1\rangle \perp \langle 1
\rangle \perp \langle 16\rangle$ (the library has dyadic spinor norm computations only in the ranges of Lemmas 3.8 and
the dyadic lemmas of `Ch11Sec3Dyadic.lean`, not for this lattice), (b) at odd $p$, Lemma 3.3 for the unimodular lattices
($p \nmid 128$, `mem_localSpinorNormGroup_iff_of_unimodular`), (c) the identification of $G$ with the quotient of
$\mathbb Q_2^\times$ by the image of $S \cdot T$ and the evaluation of $g(w)$ for odd positive $w$, which gives the
criterion $w \equiv 1 \pmod 4$. Fields' arguments: `v₂` is a prime of $\mathbb Q$ with `primesEquiv v₂ = 2`; `w` the odd
positive integer, `hw` its positivity. -/
@[kb "cassels1978" "Ch. 11, Ex. 6 (i), (ii), p. 252 (P = {2}, |G| = 2, g(w) = 1 iff w ≡ 1 mod 4)"]
structure Ex6SpinorGenera : Prop where
  /-- (i) The genus of $f$ consists of two (proper) spinor genera. -/
  spinorGenusNumber : Lattices.properSpinorGenusNumber (ex6f.map (Int.castRingHom ℚ))
    (Lattices.stdLat : Lattices.Lat ℚ 3) = 2
  /-- (i) $P = \{2\}$ satisfies (3.7): away from $2$, $\theta(\Lambda_v) = U_v(\mathbb Q_v^\times)^2$. -/
  unitsAway : ∀ v₂ : HeightOneSpectrum (𝓞 ℚ), (Rat.HeightOneSpectrum.primesEquiv v₂ : ℕ) = 2 →
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ v₂ → ∀ a : (v.adicCompletion ℚ)ˣ,
      a ∈ Lattices.localSpinorNormGroup (ex6f.map (Int.castRingHom ℚ))
          (Lattices.nondegenerate_map_of_det_ne_zero ex6f (by rw [hessian_det_ex6f]; norm_num)) v
          (Lattices.stdLat : Lattices.Lat ℚ 3) ↔
        Lattices.IsUnitSqClass v (Lattices.SqClass.mk a)
  /-- (i) The group $G = R/ST$ of (3.15) for $P = \{2\}$ has order $2$. -/
  orderG : ∀ v₂ : HeightOneSpectrum (𝓞 ℚ), (Rat.HeightOneSpectrum.primesEquiv v₂ : ℕ) = 2 →
    Nat.card (Lattices.CasselsG (ex6f.map (Int.castRingHom ℚ))
      (Lattices.nondegenerate_map_of_det_ne_zero ex6f (by rw [hessian_det_ex6f]; norm_num))
      (Lattices.stdLat : Lattices.Lat ℚ 3) {v₂}) = 2
  /-- (ii) $g(w)$ is the identity of $G$ exactly when $w \equiv 1 \pmod 4$, for odd positive $w$. -/
  g_odd : ∀ v₂ : HeightOneSpectrum (𝓞 ℚ), (Rat.HeightOneSpectrum.primesEquiv v₂ : ℕ) = 2 →
    ∀ (w : ℕ) (hw : 0 < w), w % 2 = 1 →
      (Lattices.casselsg (ex6f.map (Int.castRingHom ℚ))
        (Lattices.nondegenerate_map_of_det_ne_zero ex6f (by rw [hessian_det_ex6f]; norm_num))
        (Lattices.stdLat : Lattices.Lat ℚ 3) {v₂} (Units.mk0 (w : ℚ) (by exact_mod_cast hw.ne')) = 1 ↔
        w % 4 = 1)

/-! ### Example 7: the forms $x^2 + xy + y^2 + 9z^2$ and $x^2 + 3(y^2 + yz + z^2)$ -/

/-- Helper: $2$-adic primitive representation of $4m^2$ ($m$ odd) by $f = x_0^2 + x_0x_1 + x_1^2 + 9x_2^2$: the vector
$(1, 1, w/3)$ where $w^2 = 4m^2 - 3$ ($4m^2 - 3 \equiv 1 \pmod 8$ is a $2$-adic square). -/
theorem ex7_local_two (m : ℤ) (hm2 : m % 2 = 1) :
    ∃ x : Fin 3 → ℤ_[2], (∃ i, IsUnit (x i)) ∧ (ex7f.map (Int.castRingHom ℤ_[2])).eval x = ((4 * m ^ 2 : ℤ) : ℤ_[2]) := by
  have hc : (4 * m ^ 2 - 3) % 8 = 1 := by
    have := (sq_mod_eight_parity m).1 hm2
    omega
  obtain ⟨w, hw, hww⟩ := two_adic_sq _ hc
  obtain ⟨u, hu⟩ := (isUnit_intCast_padic (p := 2) 3).mpr (by norm_num)
  refine ⟨![1, 1, w * ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2])], ⟨0, by simp⟩, ?_⟩
  rw [eval_map_ex7f]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  have hinv : ((3 : ℤ) : ℤ_[2]) * ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by rw [← hu]; simp
  push_cast at hww hinv ⊢
  linear_combination ((3 * ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) ^ 2) * hww +
    ((3 * ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) + 1) * (4 * (m : ℤ_[2]) ^ 2 - 3)) * hinv

/-- Helper: $3$-adic primitive representation of $4m^2$ ($3 \nmid m$) by $f$: the vector $(2m, 0, 0)$. -/
theorem ex7_local_three (m : ℤ) (hm3 : m % 3 ≠ 0) :
    ∃ x : Fin 3 → ℤ_[3], (∃ i, IsUnit (x i)) ∧ (ex7f.map (Int.castRingHom ℤ_[3])).eval x = ((4 * m ^ 2 : ℤ) : ℤ_[3]) := by
  refine ⟨![((2 * m : ℤ) : ℤ_[3]), 0, 0], ⟨0, ?_⟩, ?_⟩
  · simpa using (isUnit_intCast_padic (p := 3) (2 * m)).mpr (by omega)
  · rw [eval_map_ex7f]
    simp
    ring

/-- **Cassels, Ch. 11, Example 7 (i)** (p. 252), named statement for the class content: *$f = x^2 + xy + y^2 + 9z^2$ and
$g = x^2 + 3(y^2 + yz + z^2)$ represent the two spinor genera of a genus, and each spinor genus consists of a single
class*. As far as classes are concerned: $g$ is in the genus of $f$ (`sameGenus`) and the genus has exactly two classes
(`two_classes`); the classes are those of $f$ and of $g$ since $f$, $g$ are inequivalent (`ex7_not_intEquiv`, proved).
*Proved* in `Ch11Ex7Classes.lean` (`ex7Classes_holds`: Minkowski reduction and a finite check). The original note: the classes of determinant-$27$ (Gram) ternaries need the reduction theory of Chapter 9 for ternary
forms, or the spinor-genus computation of `Ex7SpinorGenera` plus a neighbor argument as for Example 6. Numerical check:
the $5$ classes of positive ternary Hessians of determinant $54$ (Minkowski-reduced enumeration) contain exactly two in
the genus of $f$ (same representation counts modulo $8$, $16$, $9$, $27$), represented by $f$ and $g$. -/
@[kb "cassels1978" "Ch. 11, Ex. 7 (i), p. 252 (classes in the genus)"]
structure Ex7Classes : Prop where
  /-- $g$ is in the genus of $f$. -/
  sameGenus : SameGenus ex7f ex7g
  /-- The genus of $f$ has exactly two classes. -/
  two_classes : (genusClasses ex7f).ncard = 2

/-- **Cassels, Ch. 11, Example 7 (i)** (p. 252), named statement for the number of spinor genera: the genus of
$f = x^2 + xy + y^2 + 9z^2$ (the lattice $\mathbb Z^3$ with `ex7f` over $\mathbb Q$) consists of two (proper) spinor
genera. *Not proved:* needs the local spinor norm groups at $p = 2, 3$ and the group $G$ of (3.15) as in
`Ex6SpinorGenera`. -/
@[kb "cassels1978" "Ch. 11, Ex. 7 (i), p. 252 (two spinor genera)"]
structure Ex7SpinorGenera : Prop where
  /-- The genus of $f$ consists of two (proper) spinor genera. -/
  spinorGenusNumber : Lattices.properSpinorGenusNumber (ex7f.map (Int.castRingHom ℚ))
    (Lattices.stdLat : Lattices.Lat ℚ 3) = 2

/-- The forms $f$ and $g$ of Example 7 are not integrally equivalent: $100 = 4 \cdot 5^2 = f(9, 1, 1)$ is a primitive
value of $f$, but $5 \equiv 2 \pmod 3$ excludes a primitive representation by $g$ (`ex7g_mod_three`). -/
theorem ex7_not_intEquiv : ¬ IntEquiv ex7f ex7g := by
  intro h
  have h1 : ∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex7f.eval x = 4 * 5 ^ 2 :=
    ⟨![9, 1, 1], by simp [Fin.univ_succ, Finset.gcd_insert], by rw [eval_ex7f]; simp⟩
  obtain ⟨x, hx, hxe⟩ := primRep_of_intEquiv (IsometricGL.symm h : IntEquiv ex7g ex7f) h1
  have := ex7g_mod_three 5 (by norm_num) (by norm_num) (by norm_num) x hx hxe
  omega

/-- Helper: every form in the genus of $f$ is equivalent to $f$ or to $g$ (Example 7, given `Ex7Classes`). -/
theorem Ex7Classes.classes (h : Ex7Classes) (f' : QuadForm ℤ 3) (hf' : SameGenus ex7f f') :
    IntEquiv ex7f f' ∨ IntEquiv ex7g f' :=
  intEquiv_or_of_ncard_genusClasses_eq_two h.two_classes h.sameGenus ex7_not_intEquiv f' hf'

/-- Helper: the genus of $f$ contains a form representing $4m^2$ primitively ($m > 0$ odd, $3 \nmid m$); Chapter 9,
Theorem 5.1, with the local conditions at $p \mid 54 = \det H$, i.e. $p = 2, 3$. -/
theorem ex7_genus_primRep (m : ℤ) (hm0 : 0 < m) (hm2 : m % 2 = 1) (hm3 : m % 3 ≠ 0) :
    ∃ f' : QuadForm ℤ 3, SameGenus ex7f f' ∧
      ∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ f'.eval x = 4 * m ^ 2 := by
  refine exists_sameGenus_primRep ex7f (by norm_num) (by rw [hessian_det_ex7f]; norm_num) (a := 4 * m ^ 2)
    (by positivity) ⟨![(2 * m : ℝ), 0, 0], by rw [evalIn_ex7f]; simp; ring⟩ ?_
  intro p _ hc
  have hp23 : p = 2 ∨ p = 3 := by
    rcases hc with h | h | ⟨h, -⟩
    · exact Or.inl h
    · rw [hessian_det_ex7f] at h
      exact prime_dvd_54 p Fact.out (by exact_mod_cast h)
    · omega
  rcases hp23 with rfl | rfl
  · exact ex7_local_two m hm2
  · exact ex7_local_three m hm3

/-- **Cassels, Ch. 11, Example 7 (ii)** (p. 252) and **(iii)** (the part not using spinor genera): *$4m^2$ for an
integer $m > 0$, $2 \nmid m$, is representable primitively by $f$ if $m \equiv 2 \pmod 3$ and by $g$ if
$m \equiv 1 \pmod 3$, but never by both.* The congruence conditions are necessary (unconditional, by the elementary
argument of the hint of (iii): `ex7f_mod_three`, `ex7g_mod_three`, hence "never by both", `ex7_not_both`); the
existence is conditional on the class content of (i) (`Ex7Classes`, named): by Chapter 9, Theorem 5.1 some form of
the genus of $f$ represents $4m^2$ primitively (local vectors $(1, 1, w/3)$ at $2$ and $(2m, 0, 0)$ at $3$), and
it is equivalent to $f$ or $g$. This iff is stated for $3 \nmid m$ (the two cases $m \equiv 1, 2 \pmod 3$ of the book).
"Never by both" holds for *all* odd $m > 0$ (`ex7_not_both`, unconditional). For $m = 3m'$ the iff is not true as
an "represented by neither" statement: numerically $f$ represents $4m^2$ primitively for $m = 3, 21, 39$ and $g$ for
$m = 15, 33$, while $m = 9, 27$ are represented by neither; proved are only the necessary conditions
`ex7f_three_dvd` ($m' \equiv 1 \pmod 3$ for $f$) and `ex7g_three_dvd` ($m' \equiv 2 \pmod 3$ for $g$). Arguments: `hcl`
the class content, `m` the positive odd integer prime to $3$. -/
@[kb "cassels1978" "Ch. 11, Ex. 7 (ii), (iii), p. 252"]
theorem ex7_primRep_iff (hcl : Ex7Classes) (m : ℤ) (hm0 : 0 < m) (hm2 : m % 2 = 1) (hm3 : m % 3 ≠ 0) :
    ((∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex7f.eval x = 4 * m ^ 2) ↔ m % 3 = 2) ∧
      ((∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex7g.eval x = 4 * m ^ 2) ↔ m % 3 = 1) := by
  obtain ⟨f', hg, hrep⟩ := ex7_genus_primRep m hm0 hm2 hm3
  have hex : (∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex7f.eval x = 4 * m ^ 2) ∨
      (∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex7g.eval x = 4 * m ^ 2) := by
    rcases hcl.classes f' hg with he | he
    · exact Or.inl (primRep_of_intEquiv he hrep)
    · exact Or.inr (primRep_of_intEquiv he hrep)
  constructor
  · constructor
    · rintro ⟨x, hx, h⟩
      exact ex7f_mod_three m hm0 hm2 hm3 x hx h
    · intro h3
      rcases hex with hf | ⟨x, hx, h⟩
      · exact hf
      · have := ex7g_mod_three m hm0 hm2 hm3 x hx h
        omega
  · constructor
    · rintro ⟨x, hx, h⟩
      exact ex7g_mod_three m hm0 hm2 hm3 x hx h
    · intro h3
      rcases hex with ⟨x, hx, h⟩ | hg'
      · have := ex7f_mod_three m hm0 hm2 hm3 x hx h
        omega
      · exact hg'

/-! ### Example 4: generators of the local spinor norm group -/

section Ex4

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- Helper: the symmetry $\tau_{b_i}$ in a basis vector $b_i$ of an orthogonal basis of $L_\mathfrak p$ stabilizes
$L_\mathfrak p$ ($\mathfrak p \nmid 2$, $Q(b_i) \ne 0$). Arguments: `Q` the form, `v` the prime, `h2` that $\mathfrak p \nmid 2$,
`L` the lattice, `γ` a basis of $L_\mathfrak p$ (columns), `hγ` that it is one, `horth` that it is orthogonal, `i` the
index, `hQi` that $Q(b_i) \ne 0$. -/
theorem ex4_symm_mem_locStab (Q : QuadForm F n) (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal)
    (L : Lattices.Lat F n) (γ : GL (Fin n) (v.adicCompletion F))
    (hγ : Lattices.loc v L.1 = Lattices.locAct v γ (Lattices.std v))
    (horth : ∀ k l, k ≠ l → Lattices.locGram Q v γ k l = 0) (i : Fin n)
    (hQi : Q.evalIn (v.adicCompletion F) (γ.val *ᵥ Pi.single i 1) ≠ 0) :
    Lattices.symm Q (v.adicCompletion F) (γ.val *ᵥ Pi.single i 1) ∈ Lattices.locStabV Q v L := by
  have h2v := Lattices.valued_two (v := v) h2
  have hxM : γ.val *ᵥ Pi.single i 1 ∈ Lattices.loc v L.1 := by
    rw [hγ, Lattices.mem_locAct]; exact ⟨_, Lattices.single_mem_std i (by simp), rfl⟩
  show Lattices.locAct v (Lattices.symm Q (v.adicCompletion F) (γ.val *ᵥ Pi.single i 1) :
    GL (Fin n) (v.adicCompletion F)) (Lattices.loc v L.1) = Lattices.loc v L.1
  refine Lattices.locAct_symm_eq hxM hQi fun y hy => ?_
  rw [hγ, Lattices.mem_locAct] at hy
  obtain ⟨d, hd, rfl⟩ := hy
  have hG : 2 * Q.evalIn (v.adicCompletion F) (γ.val *ᵥ Pi.single i 1) = Lattices.locGram Q v γ i i := by
    rw [Lattices.two_mul_evalIn_eq, Lattices.locGram_apply_eq]
  have hv : Valued.v (Q.evalIn (v.adicCompletion F) (γ.val *ᵥ Pi.single i 1)) =
      Valued.v (Lattices.locGram Q v γ i i) := by
    rw [← hG, map_mul, h2v, one_mul]
  rw [Lattices.qbil_mulVec_locGram, single_dotProduct, Lattices.locGram_mulVec_diag horth, one_mul, hv, map_mul]
  have hd' := (Lattices.mem_std_iff).mp hd i
  calc _ ≤ Valued.v (Lattices.locGram Q v γ i i) * 1 := mul_le_mul' le_rfl hd'
    _ = _ := mul_one _

/-- Helper: $2Q(b_i)$ is the diagonal entry $G_{ii}$ of the Gram matrix. -/
theorem ex4_two_mul_eval (Q : QuadForm F n) (v : HeightOneSpectrum (𝓞 F)) (γ : GL (Fin n) (v.adicCompletion F))
    (i : Fin n) : 2 * Q.evalIn (v.adicCompletion F) (γ.val *ᵥ Pi.single i 1) = Lattices.locGram Q v γ i i := by
  rw [Lattices.two_mul_evalIn_eq, Lattices.locGram_apply_eq]

/-- **The generators of Example 4**: the subgroup of $F_\mathfrak p^\times$ generated by the squares
$(F_\mathfrak p^\times)^2$ and the products $\phi(b_{i_0})\phi(b_j)$ ($j \ne i_0$) of values of the form $Q$ at the
vectors $b_j = \gamma e_j$ (the columns of `γ`) of a basis of $L_\mathfrak p$. Cassels' $b_1$ is $b_{i_0}$ ($i_0 = 0$ in
`Ex4Statement`; the book's $b_j$, $1 \le j \le n$, are `γ` applied to the standard vectors $e_0, \dots, e_{n-1}$ here). -/
def ex4Gens (Q : QuadForm F n) (v : HeightOneSpectrum (𝓞 F)) (γ : GL (Fin n) (v.adicCompletion F))
    (i₀ : Fin n) : Set (v.adicCompletion F)ˣ :=
  {u | ∃ w : (v.adicCompletion F)ˣ, u = w ^ 2} ∪
    {u | ∃ j : Fin n, j ≠ i₀ ∧ (u : v.adicCompletion F) =
      Q.evalIn (v.adicCompletion F) (γ.val *ᵥ Pi.single i₀ 1) *
        Q.evalIn (v.adicCompletion F) (γ.val *ᵥ Pi.single j 1)}

/-- **Example 4, the easy inclusion** ("$\supseteq$"): for an orthogonal basis of $L_\mathfrak p$ ($\mathfrak p \nmid 2$)
the squares and the products $\phi(b_{i_0})\phi(b_j)$ lie in $\theta(L_\mathfrak p)$, because $\tau_{b_{i_0}}\tau_{b_j}
\in O^+(L_\mathfrak p)$ has spinor norm $\phi(b_{i_0})\phi(b_j)$. (No hypothesis on the values $|\phi(b_j)|$ is needed
for this inclusion.) Arguments: `Q` the nondegenerate form (`hQ`), `v` the prime with `h2` ($\mathfrak p \nmid 2$), `L` the
lattice with orthogonal basis `γ` (`hγ`, `horth`), `i₀` the index of $b_1$. -/
@[kb "cassels1978" "Ch. 11, Ex. 4, p. 252 (inclusion of the generated group)"]
theorem ex4_closure_le (Q : QuadForm F n) (hQ : Q.Nondegenerate) (v : HeightOneSpectrum (𝓞 F))
    (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (L : Lattices.Lat F n) (γ : GL (Fin n) (v.adicCompletion F))
    (hγ : Lattices.loc v L.1 = Lattices.locAct v γ (Lattices.std v))
    (horth : ∀ k l, k ≠ l → Lattices.locGram Q v γ k l = 0) (i₀ : Fin n) :
    Subgroup.closure (ex4Gens Q v γ i₀) ≤ Lattices.localSpinorNormGroup Q hQ v L := by
  have hne : ∀ k, Q.evalIn (v.adicCompletion F) (γ.val *ᵥ Pi.single k 1) ≠ 0 := fun k h0 =>
    Lattices.locGram_ne_zero_of_diag hQ horth k (by rw [← ex4_two_mul_eval, h0, mul_zero])
  rw [Subgroup.closure_le]
  rintro u (⟨w, rfl⟩ | ⟨j, hj, hu⟩)
  · show w ^ 2 ∈ Lattices.localSpinorNormGroup Q hQ v L
    rw [Lattices.localSpinorNormGroup, Subgroup.mem_comap, map_pow, sq, Lattices.SqClass.mul_self]
    exact Subgroup.one_mem _
  · show u ∈ Lattices.localSpinorNormGroup Q hQ v L
    refine Lattices.mem_localSpinorNormGroup_of_symm_pair hQ L (hne i₀) (hne j)
      (ex4_symm_mem_locStab Q v h2 L γ hγ horth i₀ (hne i₀))
      (ex4_symm_mem_locStab Q v h2 L γ hγ horth j (hne j)) u ?_
    rw [← hu, Lattices.sqClassOf_of_ne_zero u.ne_zero]
    exact congrArg Lattices.SqClass.mk (Units.ext rfl)

end Ex4

/-- **Cassels, Ch. 11, Example 4** (p. 252), named statement: *let $p > 2$ be prime and $\Lambda_p$ an $n$-dimensional
$\mathbb Z_p$-lattice with a normal (orthogonal) basis $b_j$ ($1 \le j \le n$) such that the $\lvert\phi(b_j)\rvert_p$ are
distinct. Show that $\theta(\Lambda_p)$ is generated as a group by $(\mathbb Q_p^\times)^2$ and the $\phi(b_1)\phi(b_j)$
($1 < j \le n$).* Formalized over $\mathbb Q$ (Cassels' setting): a nondegenerate form `Q` on $\mathbb Q^n$ ($n > 0$), a
lattice `L`, a prime `v` not over $2$, an orthogonal basis of $L_p$ (columns of `γ`, `horth`) whose values
$Q(b_j)$ have pairwise different absolute values (`hdist`); then $\theta(L_p)$ (`localSpinorNormGroup`) is the subgroup
generated by `ex4Gens` with $b_1 = b_0$ (first column of `γ`; indices are shifted to 0-based). *Proved:* the inclusion
$\supseteq$ (`ex4_closure_le`). *Not proved:* the inclusion $\subseteq$. A full proof needs the Chapter 8, Lemma 3.3,
Corollary 1 factorization of $O(\Lambda_p)$ into symmetries $\tau_x$ ($x \in \Lambda_p$ primitive with $\tau_x \Lambda_p =
\Lambda_p$) for non-unimodular lattices with a normal basis (the library has it, `mem_closure_unitSymmSet`, only for
unit-norm orthogonal bases), followed by the computation that $\phi(x)$ lies in $\phi(b_j)(\mathbb Z_p^\times)^2$ for
the index $j$ at which $\lvert\phi(b_j)\rvert_p$ is smallest on the support of $x$ (distinct absolute values make this
index unique, and Hensel's lemma gives the square). -/
@[kb "cassels1978" "Ch. 11, Ex. 4, p. 252"]
structure Ex4Statement : Prop where
  /-- The generation statement, for every nondegenerate rational form, odd prime `v`, lattice `L`, orthogonal basis `γ`
  of `L` at `v` with pairwise distinct absolute values $\lvert Q(b_j)\rvert_v$. -/
  holds : ∀ (n : ℕ) (hn : 0 < n) (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (v : HeightOneSpectrum (𝓞 ℚ)),
    (2 : 𝓞 ℚ) ∉ v.asIdeal → ∀ (L : Lattices.Lat ℚ n) (γ : GL (Fin n) (v.adicCompletion ℚ)),
    Lattices.loc v L.1 = Lattices.locAct v γ (Lattices.std v) →
    (∀ k l, k ≠ l → Lattices.locGram Q v γ k l = 0) →
    (∀ i j, i ≠ j → Valued.v (Q.evalIn (v.adicCompletion ℚ) (γ.val *ᵥ Pi.single i 1)) ≠
      Valued.v (Q.evalIn (v.adicCompletion ℚ) (γ.val *ᵥ Pi.single j 1))) →
    Lattices.localSpinorNormGroup Q hQ v L = Subgroup.closure (ex4Gens Q v γ ⟨0, hn⟩)

/-! ### Example 5: the forms $x^2 + py^2 - p^2z^2$ -/

/-- The form $x_0^2 + p\,x_1^2 - p^2x_2^2$ of Example 5 (Ch. 11, p. 252), for a natural number `p` (a prime $p > 2$ in the
statement). -/
def ex5Form (p : ℕ) : QuadForm ℤ 3 := QuadForm.diag ![1, (p : ℤ), -((p : ℤ) ^ 2)]

/-- **Cassels, Ch. 11, Example 5** (p. 252), named statement: *for a prime $p > 2$, $x^2 + py^2 - p^2z^2$ is in a genus of
$2$ classes if $p \equiv 1 \pmod 8$, but otherwise in a genus of $1$ class.* The number of classes of the genus is the
`Set.ncard` of `genusClasses`. *Not proved.* A full proof needs, as for Example 3, the local spinor norm groups of the
$\mathbb Z_p$-lattice $\langle 1\rangle \perp \langle p\rangle \perp \langle -p^2\rangle$ (this is where Example 4 enters:
the values $1, p, -p^2$ have pairwise distinct absolute values, so $\theta(\Lambda_p)$ is generated by the squares and the
products of the first value with the others), the $2$-adic spinor norm group, and the computation of the group $G$ of
(3.15) (the number of spinor genera of the genus), and then that an indefinite spinor genus is one class (Theorem 1.4)
when there is one spinor genus, and the count of classes when there are two. Fields: `two_classes` for $p \equiv 1 \pmod 8$,
`one_class` for the other odd primes. -/
@[kb "cassels1978" "Ch. 11, Ex. 5, p. 252"]
structure Ex5Statement : Prop where
  /-- For $p \equiv 1 \pmod 8$ the genus has two classes. -/
  two_classes : ∀ p : ℕ, p.Prime → p ≠ 2 → p % 8 = 1 → (genusClasses (ex5Form p)).ncard = 2
  /-- For the other odd primes $p$ the genus has one class. -/
  one_class : ∀ p : ℕ, p.Prime → p ≠ 2 → p % 8 ≠ 1 → (genusClasses (ex5Form p)).ncard = 1

/-! ### Example 9: a quaternary genus with more than one spinor genus -/

/-- The form $f = x_0^2 + x_0x_1 + 7x_1^2 + 3(x_2^2 + x_2x_3 + x_3^2)$ of Example 9 (Ch. 11, p. 253). -/
def ex9f : QuadForm ℤ 4 := QuadForm.ofUpper ![![1, 1, 0, 0], ![0, 7, 0, 0], ![0, 0, 3, 3], ![0, 0, 0, 3]]

/-- The form $x_0^2 + x_0x_1 + x_1^2 + 9(x_2^2 + x_2x_3 + x_3^2)$, the second class of the genus of `ex9f` (*reconstruction*). -/
def ex9f₂ : QuadForm ℤ 4 := QuadForm.ofUpper ![![1, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 9, 9], ![0, 0, 0, 9]]

/-- The form $3x_0^2 + 3x_1^2 + 4x_2^2 + 4x_3^2 - 3x_0x_1 - 3x_0x_2 - 3x_0x_3 - x_2x_3$ (Hessian rows
$(6,-3,-3,-3)$, $(-3,6,0,0)$, $(-3,0,8,-1)$, $(-3,0,-1,8)$), the third class of the genus of `ex9f` (*reconstruction*). -/
def ex9f₃ : QuadForm ℤ 4 :=
  QuadForm.ofUpper ![![3, -3, -3, -3], ![0, 3, 0, 0], ![0, 0, 4, -1], ![0, 0, 0, 4]]

/-- **Cassels, Ch. 11, Example 9** (p. 253), named statement: *the genus of
$f = x^2 + xy + 7y^2 + 3(z^2 + zt + t^2)$ contains more than one spinor genus; determine all the classes in the genus*
[Watson 1960, p. 114]. Fields: `moreThanOneSpinorGenus` ($g^+ > 1$, the number of proper spinor genera); the
*reconstructed answer* to "determine all the classes": the genus has exactly the three classes of `ex9f`, `ex9f₂`,
`ex9f₃` (`sameGenus₂`, `sameGenus₃`, `classes`, and the three pairwise inequivalences `not_equiv₁₂`, `not_equiv₁₃`,
`not_equiv₂₃`). *Reconstruction, not from the book (which asks the reader to determine the classes):* found by computer.
Enumeration of all positive definite quaternary Hessians of determinant $729$ that are Minkowski-reduced
(diagonal $\prod h_{ii} \le 4 \cdot 729$, $\lvert h_{ij}\rvert \le h_{ii}/2$ for $i < j$): $2072$ matrices; $104$ of them have the
same representation counts as `ex9f` modulo $8$ and $9$ (all three representatives also modulo $16$ and $27$, and
the same discriminant quadratic form as `ex9f`); every one of the $104$ is isometric (by an exhaustive search for
bases among short vectors) to one of the three, and the three are pairwise non-isometric (different numbers of
vectors of norm $1$: $2$, $6$, $0$). *Not proved.* A full proof needs the classification of the genus (reduction
theory or neighbors for quaternary forms) and the computation of $g^+$ via the group $G$ of (3.15) at $P = \{2, 3\}$. -/
@[kb "cassels1978" "Ch. 11, Ex. 9, p. 253"]
structure Ex9Statement : Prop where
  /-- The genus of $f$ contains more than one (proper) spinor genus. -/
  moreThanOneSpinorGenus : 1 < Lattices.properSpinorGenusNumber (ex9f.map (Int.castRingHom ℚ))
    (Lattices.stdLat : Lattices.Lat ℚ 4)
  /-- `ex9f₂` is in the genus of `ex9f`. -/
  sameGenus₂ : SameGenus ex9f ex9f₂
  /-- `ex9f₃` is in the genus of `ex9f`. -/
  sameGenus₃ : SameGenus ex9f ex9f₃
  /-- `ex9f` and `ex9f₂` are not integrally equivalent. -/
  not_equiv₁₂ : ¬ IntEquiv ex9f ex9f₂
  /-- `ex9f` and `ex9f₃` are not integrally equivalent. -/
  not_equiv₁₃ : ¬ IntEquiv ex9f ex9f₃
  /-- `ex9f₂` and `ex9f₃` are not integrally equivalent. -/
  not_equiv₂₃ : ¬ IntEquiv ex9f₂ ex9f₃
  /-- Every form of the genus of `ex9f` is equivalent to one of the three. -/
  classes : ∀ h : QuadForm ℤ 4, SameGenus ex9f h → IntEquiv ex9f h ∨ IntEquiv ex9f₂ h ∨ IntEquiv ex9f₃ h

end QuadFormsKB.Cassels.Ch11Ex4
