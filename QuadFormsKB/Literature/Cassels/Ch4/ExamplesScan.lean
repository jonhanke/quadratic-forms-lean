/-
# Cassels, Chapter 4, Examples 1, 2 and 4 (p. 66), recovered from the page image

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 4, *Examples*, Ex. 1, 2 and 4, p. 66. The
machine-read text of these exercises is illegible; the statements were transcribed from the page image.
Cassels' "primes" include $p = \infty$ ($\mathbb Q_\infty = \mathbb R$); every exercise is answered at
the finite primes (`..._padic`) and at the real place (`..._real`).

**Conventions.** Variables $x_1, \dots, x_n$ of the book are $x_0, \dots, x_{n-1}$ here (`Fin n`). A form is
`QuadForm.diag ![a₀, …, a_{n-1}]` ($= \sum_i a_i x_i^2$); for rational coefficients isotropy and equivalence
over $\mathbb Q_p$ or $\mathbb R$ are `IsotropicIn` and `IsometricIn`. Cassels' $c_p(f) = \prod_{i<j}(a_i, a_j)_p$
is `PadicClass.hasseVec` (`hasseInvariant` for rational coefficients). The variable `p` is an arbitrary prime.

**Formalized (all proved, no assumptions).**
* Ex. 1 (i): $5x_1^2 - x_2^2 - 3x_3^2$ is isotropic over $\mathbb Q_p$ iff $p \ne 3, 5$ (`ex1_i_padic`), and over
  $\mathbb R$ (`ex1_i_real`).
* Ex. 1 (ii): $x_1^2 + x_2^2 + 7x_3^2 + 5x_4^2$ is isotropic over $\mathbb Q_p$ for every prime $p$
  (`ex1_ii_padic`) and anisotropic over $\mathbb R$ (`ex1_ii_real`).
* Ex. 2 (i): $3x_1^2 + 7x_2^2 \sim x_1^2 + 84x_2^2$ over $\mathbb Q_p$ iff $p \ne 2, 7$ (`ex2_i_padic`); over
  $\mathbb R$ always (`ex2_i_real`).
* Ex. 2 (ii): $x_1^2 - 3x_2^2 + 15x_3^2 \sim 3x_1^2 - 5x_2^2 + 3x_3^2$ over $\mathbb Q_p$ iff $p \ne 2, 5$
  (`ex2_ii_padic`); over $\mathbb R$ always (`ex2_ii_real`).
* Ex. 2 (iii): $x_1^2 - 5x_2^2 + 3x_3^2 - 7x_4^2 \sim x_1^2 - x_2^2 + x_3^2 - x_4^2$ over $\mathbb Q_p$ iff $105$
  is a square in $\mathbb Q_p$ (`ex2_iii_padic`): always for $p = 2$ (`ex2_iii_two`), never for $p = 3, 5, 7$
  (`ex2_iii_three_five_seven`), and for the other primes iff $105$ is a quadratic residue (`ex2_iii_padic_residue`);
  over $\mathbb R$ always (`ex2_iii_real`).
* Ex. 4: for $m \in \mathbb Q_p^{\times}$, $m \ne -1$ (any element of $\mathbb Q_p$), $c_p((m+1)(x_1^2 + x_2^2 + x_3^2)
  + m x_4^2) = 1$ (`ex4_hasse`); for $p \ne \infty$ this form is equivalent to $x_1^2 + x_2^2 + x_3^2 +
  m(m+1)x_4^2$ (`ex4_padic`); over $\mathbb R$ the two forms are equivalent iff $m > -1$ (`ex4_real`).

**Method.** Equivalence is decided by Cassels' Theorem 1.1 (`isometric_padic_iff_invariants`: determinant modulo
squares and Hasse invariant), and Hilbert symbols of small integers are evaluated by: no primitive solution
modulo $p^k$ (value $-1$), an explicit $p$-adic solution via Hensel's lemma for squares (value $1$), and
symbols of units at odd primes (value $1$). Isotropy of ternary forms uses $(a, b)_p = 1 \iff \langle a, b, -1\rangle$
isotropic. Over $\mathbb R$ the equivalences are explicit diagonal scalings.

**Reconstructed.** The statements of Ex. 1, 2, 4 were transcribed from the page image by the person running this
task; the answers (which primes) are computed here, not taken from the book.
-/
import QuadFormsKB.Literature.Cassels.Ch6.ExamplesScan
import QuadFormsKB.Literature.Cassels.Ch4.Invariants

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels.Ch4Scan

open QuadFormsKB QuadForm PadicClass Matrix

/-- Helper: an integer prime to $p$ is a unit of $\mathbb Z_p$. -/
theorem isUnit_intCast (p : ℕ) [Fact p.Prime] (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) : IsUnit (u : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hu ?_)
  exact (PadicInt.norm_int_lt_one_iff_dvd u).1 h

/-- Helper: an integer $u \equiv 1 \pmod 8$ is a square in $\mathbb Q_2$. -/
theorem isSquare_two_of_mod_eight (u : ℤ) (hu : u % 8 = 1) : IsSquare (u : ℚ_[2]) := by
  have hnd : ¬ ((2 : ℕ) : ℤ) ∣ u := by omega
  have hU := isUnit_intCast 2 u hnd
  have key := (HilbertLocal.isSquare_two_adic_unit_iff hU.unit).2 (by
    obtain ⟨q, hq⟩ : ∃ q : ℤ, u = 8 * q + 1 := ⟨u / 8, by omega⟩
    show PadicInt.toZModPow 3 (u : ℤ_[2]) = 1
    rw [hq]
    push_cast
    simp only [map_add, map_mul, map_one, map_ofNat, map_intCast]
    have h8 : (8 : ZMod (2 ^ 3)) = 0 := by decide
    rw [h8]
    simp)
  simpa using key

/-- Helper: an integer $u$ prime to the odd prime $p$ is a square in $\mathbb Q_p$ if and only if its residue is a
square modulo $p$. -/
theorem isSquare_odd_iff_residue (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) :
    IsSquare (u : ℚ_[p]) ↔ IsSquare (u : ZMod p) := by
  have hU := isUnit_intCast p u hu
  have key := HilbertLocal.isSquare_unit_iff hp2 hU.unit
  simpa using key

/-- Helper: an integer $u$ prime to the odd prime $p$ whose residue is a square modulo $p$ is a square in
$\mathbb Q_p$. -/
theorem isSquare_odd_of_residue (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (u : ℤ) (hu : ¬ (p : ℤ) ∣ u)
    (hs : IsSquare (u : ZMod p)) : IsSquare (u : ℚ_[p]) :=
  (isSquare_odd_iff_residue p hp2 u hu).2 hs

/-- Helper: if a diagonal ternary form $\langle a, b, c\rangle$ with integer coefficients has no zero modulo
$p^k$ among the triples with a coordinate prime to $p$, it is anisotropic over $\mathbb Q_p$. Arguments: the prime
$p$, the exponent $k$, the coefficients $a, b, c$, and the finite check `h`. -/
theorem not_isotropic_diag3_of_mod (p : ℕ) [Fact p.Prime] (k : ℕ) (a b c : ℤ)
    (h : ∀ x y z : ZMod (p ^ k), (x.val.Coprime (p ^ k) ∨ y.val.Coprime (p ^ k) ∨ z.val.Coprime (p ^ k)) →
      (a : ZMod (p ^ k)) * x ^ 2 + b * y ^ 2 + c * z ^ 2 ≠ 0) :
    ¬ (QuadForm.diag ![(a : ℚ), b, c]).IsotropicIn ℚ_[p] := by
  refine Cassels.Ch6.Scan.not_isotropic_of_primitive p _ (fun z ⟨i, hi⟩ hz => ?_)
  rw [QuadForm.evalIn_diag] at hz
  simp [Fin.sum_univ_three] at hz
  have hz' : (a : ℤ_[p]) * z 0 ^ 2 + b * z 1 ^ 2 + c * z 2 ^ 2 = 0 :=
    PadicInt.coe_eq_zero.1 (by push_cast; exact hz)
  have h2 := congrArg (PadicInt.toZModPow k) hz'
  simp only [map_add, map_mul, map_pow, map_zero, map_intCast] at h2
  refine h _ _ _ ?_ h2
  have hc := Cassels.Ch6.Scan.coprime_of_isUnit p k hi
  fin_cases i
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr hc)


/-! ### Hilbert symbols of small integers -/

/-- Helper: a primitive-vector check modulo $p^k$ shows that the Hilbert symbol $(a, b)_p$ of two integers is
$-1$ (no solution of $z^2 = a x^2 + b y^2$ with a coordinate prime to $p$ modulo $p^k$). Arguments: the prime
$p$, the exponent $k$, the integers $a, b$, and the finite check `h`. -/
theorem hs_neg_one_of_mod (p : ℕ) [Fact p.Prime] (k : ℕ) (a b : ℤ)
    (h : ∀ x y z : ZMod (p ^ k), (x.val.Coprime (p ^ k) ∨ y.val.Coprime (p ^ k) ∨ z.val.Coprime (p ^ k)) →
      (a : ZMod (p ^ k)) * x ^ 2 + b * y ^ 2 + (-1) * z ^ 2 ≠ 0) :
    hilbertSymbol ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p]) = -1 := by
  have h1 := not_isotropic_diag3_of_mod p k a b (-1) (by simpa using h)
  push_cast at h1
  have hiff := hilbertSymbol_eq_one_iff_isotropic ℚ_[p] (a : ℚ) (b : ℚ)
  have e : ∀ c : ℤ, algebraMap ℚ ℚ_[p] (c : ℚ) = (c : ℚ_[p]) := fun c => by simp
  rw [e, e] at hiff
  rcases hs_pm (K := ℚ_[p]) (a : ℚ_[p]) (b : ℚ_[p]) with h2 | h2
  · exact absurd (hiff.1 h2) h1
  · exact h2

/-- Helper: for an odd prime $p$ and integers $a, b$ prime to $p$, $(a, b)_p = 1$. -/
theorem hs_eq_one_of_not_dvd (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a b : ℤ) (ha : ¬ (p : ℤ) ∣ a)
    (hb : ¬ (p : ℤ) ∣ b) : hilbertSymbol ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p]) = 1 := by
  have ha0 : (a : ℚ) ≠ 0 := by
    rintro h; apply ha; have : a = 0 := by exact_mod_cast h
    rw [this]; exact dvd_zero _
  have hb0 : (b : ℚ) ≠ 0 := by
    rintro h; apply hb; have : b = 0 := by exact_mod_cast h
    rw [this]; exact dvd_zero _
  have hv : ∀ z : ℤ, ¬ (p : ℤ) ∣ z → padicValRat p (z : ℚ) = 0 := fun z h => by
    rw [padicValRat.of_int]; simp [padicValInt.eq_zero_of_not_dvd h]
  have := HilbertLocal.hilbert_eq_one_of_padicValRat hp2 (a : ℚ) (b : ℚ) ha0 hb0 (hv a ha) (hv b hb)
  simpa [RatPlace.hilbert] using this

/-- Helper: a nonzero solution of $z^2 = a x^2 + b y^2$ in $K$ gives $(a, b)_K = 1$. -/
theorem hs_eq_one_of_solution {K : Type*} [Field K] (a b x y z : K) (hne : (x, y, z) ≠ 0)
    (h : z ^ 2 = a * x ^ 2 + b * y ^ 2) : hilbertSymbol K a b = 1 := by
  unfold hilbertSymbol
  split_ifs with hc
  · rfl
  · exact absurd ⟨x, y, z, hne, h⟩ hc

/-- Helper: a prime $p$ different from the prime $q$ does not divide $q$. -/
theorem not_dvd_prime (p : ℕ) [Fact p.Prime] (q : ℕ) (hq : q.Prime) (h : p ≠ q) : ¬ (p : ℤ) ∣ (q : ℤ) := by
  intro hd
  exact h ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hq).1 (by exact_mod_cast hd))

/-- Helper: if the prime $p$ divides neither $a$ nor $b$, it does not divide $ab$. -/
theorem not_dvd_mul (p : ℕ) [hp : Fact p.Prime] {a b : ℤ} (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b) :
    ¬ (p : ℤ) ∣ a * b := fun h =>
  ((Nat.prime_iff_prime_int.mp hp.out).dvd_or_dvd h).elim ha hb

/-- Helper: a prime that does not divide $a$ does not divide $-a$. -/
theorem not_dvd_neg (p : ℕ) {a : ℤ} (h : ¬ (p : ℤ) ∣ a) : ¬ (p : ℤ) ∣ -a := fun h' => h ((dvd_neg).1 h')

/-- Helper: an odd valuation at $p$ rules out squares: if $v_p(n)$ is odd then $n$ is not a square in
$\mathbb Q_p$. -/
theorem not_isSquare_of_odd_val (p : ℕ) [Fact p.Prime] (n : ℤ) (h : padicValInt p n % 2 = 1) :
    ¬ IsSquare (n : ℚ_[p]) := by
  rintro ⟨r, hr⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    have hn : n = 0 := by simpa using hr
    subst hn; simp at h
  have := congrArg Padic.valuation hr
  rw [Padic.valuation_intCast, Padic.valuation_mul hr0 hr0] at this
  omega


/-- Helper: the Hilbert symbol $(a, b)_p = 1$ of two integers gives an isotropic ternary form
$\langle a, b, -1\rangle$ over $\mathbb Q_p$. -/
theorem iso_of_hs (p : ℕ) [Fact p.Prime] (a b : ℤ)
    (h : hilbertSymbol ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p]) = 1) :
    (QuadForm.diag ![(a : ℚ), (b : ℚ), -1]).IsotropicIn ℚ_[p] := by
  have hiff := hilbertSymbol_eq_one_iff_isotropic ℚ_[p] (a : ℚ) (b : ℚ)
  have e : ∀ c : ℤ, algebraMap ℚ ℚ_[p] (c : ℚ) = (c : ℚ_[p]) := fun c => by simp
  rw [e, e] at hiff
  exact hiff.1 h

/-- Helper: swapping the last two coefficients of a diagonal ternary form does not change isotropy over $K$. -/
theorem isotropic_diag3_swap (K : Type*) [Field K] [CharZero K] (a b c : ℚ) :
    (QuadForm.diag ![a, b, c]).IsotropicIn K ↔ (QuadForm.diag ![a, c, b]).IsotropicIn K := by
  have key : ∀ a b c : ℚ, (QuadForm.diag ![a, b, c]).IsotropicIn K →
      (QuadForm.diag ![a, c, b]).IsotropicIn K := by
    rintro a b c ⟨x, hx, h⟩
    refine ⟨![x 0, x 2, x 1], fun h0 => hx ?_, ?_⟩
    · have e0 := congrFun h0 0
      have e1 := congrFun h0 1
      have e2 := congrFun h0 2
      simp at e0 e1 e2
      funext i; fin_cases i <;> simp [e0, e1, e2]
    · rw [QuadForm.evalIn_diag] at h ⊢
      simp [Fin.sum_univ_three] at h ⊢
      linear_combination h
  exact ⟨key a b c, key a c b⟩

/-- Helper: a quaternary diagonal form $\langle a, b, c, d\rangle$ is isotropic over $K$ if the ternary form
$\langle a, b, c\rangle$ is (put the fourth coordinate equal to $0$). -/
theorem isotropic_diag4_of_left (K : Type*) [Field K] [CharZero K] (a b c d : ℚ)
    (h : (QuadForm.diag ![a, b, c]).IsotropicIn K) : (QuadForm.diag ![a, b, c, d]).IsotropicIn K := by
  obtain ⟨x, hx, h⟩ := h
  refine ⟨![x 0, x 1, x 2, 0], fun h0 => hx ?_, ?_⟩
  · have e0 := congrFun h0 0
    have e1 := congrFun h0 1
    have e2 := congrFun h0 2
    simp at e0 e1 e2
    funext i; fin_cases i <;> simp [e0, e1, e2]
  · rw [QuadForm.evalIn_diag] at h ⊢
    simp [Fin.sum_univ_three, Fin.sum_univ_four] at h ⊢
    linear_combination h

/-- Helper: a quaternary diagonal form $\langle a, b, c, d\rangle$ is isotropic over $K$ if the ternary form
$\langle a, b, d\rangle$ is (put the third coordinate equal to $0$). -/
theorem isotropic_diag4_of_skip (K : Type*) [Field K] [CharZero K] (a b c d : ℚ)
    (h : (QuadForm.diag ![a, b, d]).IsotropicIn K) : (QuadForm.diag ![a, b, c, d]).IsotropicIn K := by
  obtain ⟨x, hx, h⟩ := h
  refine ⟨![x 0, x 1, 0, x 2], fun h0 => hx ?_, ?_⟩
  · have e0 := congrFun h0 0
    have e1 := congrFun h0 1
    have e3 := congrFun h0 3
    simp at e0 e1 e3
    funext i; fin_cases i <;> simp [e0, e1, e3]
  · rw [QuadForm.evalIn_diag] at h ⊢
    simp [Fin.sum_univ_three, Fin.sum_univ_four] at h ⊢
    linear_combination h

/-! ### Example 1 -/

/-- **Cassels, Ch. 4, Ex. 1 (i), $p \ne \infty$ (p. 66).** *For which primes $p$ is $5x_1^2 - x_2^2 - 3x_3^2$
isotropic over $\mathbb Q_p$?* Answer: exactly for $p \ne 3, 5$ (and, by `ex1_i_real`, also over
$\mathbb R$; it is anisotropic at exactly two places, $3$ and $5$, as Hilbert's product formula requires of a
ternary form). Here $x_0, x_1, x_2$ are Cassels' $x_1, x_2, x_3$ and $p$ is any prime. Proof: for $p = 3, 5$ no
primitive vector is a zero modulo $p^2$; for odd $p \ne 3, 5$ the Hilbert symbol $(5, -3)_p$ of two units is
$1$; for $p = 2$ the vector $(1, 2, \sqrt{-7})$ is a zero. -/
@[kb "cassels1978" "Ch. 4, Ex. 1 (i) (p ≠ ∞), p. 66"]
theorem ex1_i_padic (p : ℕ) [Fact p.Prime] :
    (QuadForm.diag ![(5 : ℚ), -1, -3]).IsotropicIn ℚ_[p] ↔ p ≠ 3 ∧ p ≠ 5 := by
  constructor
  · intro hiso
    constructor
    · rintro rfl
      exact not_isotropic_diag3_of_mod 3 2 5 (-1) (-3) (by decide) (by simpa using hiso)
    · rintro rfl
      exact not_isotropic_diag3_of_mod 5 2 5 (-1) (-3) (by decide) (by simpa using hiso)
  · rintro ⟨h3, h5⟩
    have hs : hilbertSymbol ℚ_[p] ((5 : ℤ) : ℚ_[p]) (((-3 : ℤ)) : ℚ_[p]) = 1 := by
      by_cases hp2 : p = 2
      · subst hp2
        obtain ⟨r, hr⟩ := isSquare_two_of_mod_eight (-7) (by norm_num)
        refine hs_eq_one_of_solution _ _ 1 2 r (by simp [Prod.ext_iff]) ?_
        push_cast at hr ⊢
        linear_combination (-1) * hr
      · exact hs_eq_one_of_not_dvd p hp2 5 (-3) (not_dvd_prime p 5 (by norm_num) h5)
          (not_dvd_neg p (not_dvd_prime p 3 Nat.prime_three h3))
    have := iso_of_hs p 5 (-3) hs
    push_cast at this
    exact (isotropic_diag3_swap ℚ_[p] 5 (-3) (-1)).1 this


/-- **Cassels, Ch. 4, Ex. 1 (i), $p = \infty$ (p. 66).** Over $\mathbb R$ the form $5x_1^2 - x_2^2 - 3x_3^2$ is
isotropic: it is indefinite, with the zero $(1, \sqrt 5, 0)$. -/
@[kb "cassels1978" "Ch. 4, Ex. 1 (i) (p = ∞), p. 66"]
theorem ex1_i_real : (QuadForm.diag ![(5 : ℚ), -1, -3]).IsotropicIn ℝ := by
  refine ⟨![1, Real.sqrt 5, 0], fun h => by simpa using congrFun h 0, ?_⟩
  rw [QuadForm.evalIn_diag]
  simp [Fin.sum_univ_three]

/-- **Cassels, Ch. 4, Ex. 1 (ii), $p \ne \infty$ (p. 66).** *For which primes $p$ is
$x_1^2 + x_2^2 + 7x_3^2 + 5x_4^2$ isotropic over $\mathbb Q_p$?* Answer: for **every** prime $p$ (the form is
anisotropic only over $\mathbb R$, `ex1_ii_real`). Here $x_0, \dots, x_3$ are Cassels' $x_1, \dots, x_4$.
Proof: for $p = 2$ the vector $(\sqrt{-7}, 0, 1, 0)$ is a zero; for odd $p \ne 7$ the ternary subform
$\langle 1, 1, 7\rangle$ of units is isotropic ($(-1, -7)_p = 1$), and for $p = 7$ so is
$\langle 1, 1, 5\rangle$ ($(-1, -5)_7 = 1$). -/
@[kb "cassels1978" "Ch. 4, Ex. 1 (ii) (p ≠ ∞), p. 66"]
theorem ex1_ii_padic (p : ℕ) [Fact p.Prime] :
    (QuadForm.diag ![(1 : ℚ), 1, 7, 5]).IsotropicIn ℚ_[p] := by
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨r, hr⟩ := isSquare_two_of_mod_eight (-7) (by norm_num)
    refine ⟨![r, 0, 1, 0], fun h => by simpa using congrFun h 2, ?_⟩
    rw [QuadForm.evalIn_diag]
    simp [Fin.sum_univ_four]
    push_cast at hr
    linear_combination (-1) * hr
  · have h1 : ¬ (p : ℤ) ∣ 1 := (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).not_dvd_one
    have key : ∀ c : ℤ, ¬ (p : ℤ) ∣ c → (QuadForm.diag ![(1 : ℚ), 1, (c : ℚ)]).IsotropicIn ℚ_[p] := by
      intro c hc
      have hs := hs_eq_one_of_not_dvd p hp2 (-1) (-c) (not_dvd_neg p h1) (not_dvd_neg p hc)
      have hc0 : (c : ℚ) ≠ 0 := by
        rintro h0; apply hc; have : c = 0 := by exact_mod_cast h0
        rw [this]; exact dvd_zero _
      refine (HM3.isotropic_diag_three_iff ℚ_[p] 1 1 c one_ne_zero one_ne_zero hc0).2 ?_
      simpa using hs
    by_cases hp7 : p = 7
    · subst hp7
      exact isotropic_diag4_of_skip ℚ_[7] 1 1 7 5 (by simpa using key 5 (not_dvd_prime 7 5 (by norm_num) (by norm_num)))
    · exact isotropic_diag4_of_left ℚ_[p] 1 1 7 5 (by simpa using key 7 (not_dvd_prime p 7 (by norm_num) hp7))

/-- **Cassels, Ch. 4, Ex. 1 (ii), $p = \infty$ (p. 66).** Over $\mathbb R$ the positive definite form
$x_1^2 + x_2^2 + 7x_3^2 + 5x_4^2$ is anisotropic. -/
@[kb "cassels1978" "Ch. 4, Ex. 1 (ii) (p = ∞), p. 66"]
theorem ex1_ii_real : ¬ (QuadForm.diag ![(1 : ℚ), 1, 7, 5]).IsotropicIn ℝ := by
  rintro ⟨x, hx, h⟩
  rw [QuadForm.evalIn_diag] at h
  simp [Fin.sum_univ_four] at h
  apply hx
  have h0 : x 0 ^ 2 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)]
  have h1 : x 1 ^ 2 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)]
  have h2 : x 2 ^ 2 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)]
  have h3 : x 3 ^ 2 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)]
  funext i; fin_cases i
  · exact pow_eq_zero_iff (two_ne_zero) |>.1 h0
  · exact pow_eq_zero_iff (two_ne_zero) |>.1 h1
  · exact pow_eq_zero_iff (two_ne_zero) |>.1 h2
  · exact pow_eq_zero_iff (two_ne_zero) |>.1 h3


/-! ### Example 2 -/

/-- Helper: the Hasse invariant $\prod_{i<j}(a_i, a_j)_K$ of a binary diagonal form. -/
theorem hasseInvariant_two (K : Type*) [Field K] [CharZero K] (a b : ℚ) :
    hasseInvariant K ![a, b] = hilbertSymbol K (algebraMap ℚ K a) (algebraMap ℚ K b) := by
  simp [hasseInvariant, Fin.prod_univ_two]

/-- Helper: the Hasse invariant of a ternary diagonal form. -/
theorem hasseInvariant_three (K : Type*) [Field K] [CharZero K] (a b c : ℚ) :
    hasseInvariant K ![a, b, c] = hilbertSymbol K (algebraMap ℚ K a) (algebraMap ℚ K b) *
      hilbertSymbol K (algebraMap ℚ K a) (algebraMap ℚ K c) *
        hilbertSymbol K (algebraMap ℚ K b) (algebraMap ℚ K c) := by
  simp [hasseInvariant, Fin.prod_univ_three]

/-- Helper: the Hasse invariant of a quaternary diagonal form. -/
theorem hasseInvariant_four (K : Type*) [Field K] [CharZero K] (a b c d : ℚ) :
    hasseInvariant K ![a, b, c, d] = hilbertSymbol K (algebraMap ℚ K a) (algebraMap ℚ K b) *
      hilbertSymbol K (algebraMap ℚ K a) (algebraMap ℚ K c) *
        hilbertSymbol K (algebraMap ℚ K a) (algebraMap ℚ K d) *
          hilbertSymbol K (algebraMap ℚ K b) (algebraMap ℚ K c) *
            hilbertSymbol K (algebraMap ℚ K b) (algebraMap ℚ K d) *
              hilbertSymbol K (algebraMap ℚ K c) (algebraMap ℚ K d) := by
  simp only [hasseInvariant, Fin.prod_univ_four]
  simp [mul_assoc]

/-- Helper: two diagonal forms over a subfield $F$ of $\mathbb R$ whose coefficients have pairwise positive
products $a_i b_i > 0$ are equivalent over $\mathbb R$ (scale the $i$th variable by $\sqrt{b_i / a_i}$). -/
theorem isometricIn_real_of_pos {F : Type*} [Field F] [Algebra F ℝ] {n : ℕ} (a b : Fin n → F)
    (h : ∀ i, 0 < algebraMap F ℝ (a i) * algebraMap F ℝ (b i)) :
    (QuadForm.diag a).IsometricIn ℝ (QuadForm.diag b) := by
  have ha : ∀ i, algebraMap F ℝ (a i) ≠ 0 := fun i h0 => by
    have := h i; rw [h0] at this; simp at this
  have hq : ∀ i, 0 < algebraMap F ℝ (b i) / algebraMap F ℝ (a i) := fun i => by
    have e : algebraMap F ℝ (b i) / algebraMap F ℝ (a i) =
        (algebraMap F ℝ (a i) * algebraMap F ℝ (b i)) / algebraMap F ℝ (a i) ^ 2 := by
      field_simp [ha i]
    rw [e]
    have := ha i
    have := h i
    positivity
  refine ⟨Matrix.diagonal fun i => Real.sqrt (algebraMap F ℝ (b i) / algebraMap F ℝ (a i)), ?_, fun x => ?_⟩
  · rw [Matrix.det_diagonal]
    refine isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => (Real.sqrt_pos.2 (hq i)).ne')
  · rw [QuadForm.evalIn_diag, QuadForm.evalIn_diag]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_diagonal, mul_pow, Real.sq_sqrt (hq i).le]
    field_simp [ha i]

/-- Helper: the Hilbert symbol $(3, 7)_p$ equals $1$ exactly for $p \ne 2, 7$. -/
theorem hs_three_seven (p : ℕ) [Fact p.Prime] :
    hilbertSymbol ℚ_[p] 3 7 = 1 ↔ p ≠ 2 ∧ p ≠ 7 := by
  by_cases h2 : p = 2
  · subst h2
    have := hs_neg_one_of_mod 2 3 3 7 (by decide)
    simp at this
    simp [this]
  by_cases h7 : p = 7
  · subst h7
    have := hs_neg_one_of_mod 7 2 3 7 (by decide +kernel)
    simp at this
    simp [this]
  by_cases h3 : p = 3
  · subst h3
    have hsq : IsSquare ((7 : ℤ) : ℚ_[3]) :=
      isSquare_odd_of_residue 3 (by norm_num) 7 (by norm_num) (by decide +revert : IsSquare ((7 : ℤ) : ZMod 3))
    have := hs_of_isSquare (3 : ℚ_[3]) ((7 : ℤ) : ℚ_[3]) (by norm_num) hsq
    simp at this
    simp [this, h2, h7]
  · have := hs_eq_one_of_not_dvd p h2 3 7 (not_dvd_prime p 3 Nat.prime_three h3)
      (not_dvd_prime p 7 (by norm_num) h7)
    simp at this
    simp [this, h2, h7]

/-- **Cassels, Ch. 4, Ex. 2 (i), $p \ne \infty$ (p. 66).** *For which primes $p$ are $3x_1^2 + 7x_2^2$ and
$x_1^2 + 84x_2^2$ equivalent over $\mathbb Q_p$?* Answer: exactly for $p \ne 2, 7$ (and over $\mathbb R$ always,
`ex2_i_real`). Proof: the determinants $21$ and $84 = 4 \cdot 21$ agree modulo squares, so by Cassels'
Theorem 1.1 the forms are equivalent iff the Hasse invariants agree: $(3, 7)_p = (1, 84)_p = 1$. This holds
exactly when $p \ne 2, 7$: $(3, 7)_2 = -1$ (both $\equiv 3 \bmod 4$), $(3, 7)_7 = \left(\frac 37\right) = -1$,
$(3, 7)_3 = 1$ since $7 \equiv 1 \bmod 3$ is a square in $\mathbb Q_3$, and the symbol of two units is $1$ at
the other odd primes. -/
@[kb "cassels1978" "Ch. 4, Ex. 2 (i) (p ≠ ∞), p. 66"]
theorem ex2_i_padic (p : ℕ) [Fact p.Prime] :
    (QuadForm.diag ![(3 : ℚ), 7]).IsometricIn ℚ_[p] (QuadForm.diag ![(1 : ℚ), 84]) ↔ p ≠ 2 ∧ p ≠ 7 := by
  rw [isometric_padic_iff_invariants p _ _ (fun i => by fin_cases i <;> norm_num)
    (fun i => by fin_cases i <;> norm_num), ← hs_three_seven]
  rw [hasseInvariant_two, hasseInvariant_two]
  simp only [map_ofNat, map_one, hs_one_left]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨1 / 2, by norm_num, ?_⟩, h⟩
    simp [Fin.prod_univ_two]
    norm_num

/-- **Cassels, Ch. 4, Ex. 2 (i), $p = \infty$ (p. 66).** The positive definite forms $3x_1^2 + 7x_2^2$ and
$x_1^2 + 84x_2^2$ are equivalent over $\mathbb R$. -/
@[kb "cassels1978" "Ch. 4, Ex. 2 (i) (p = ∞), p. 66"]
theorem ex2_i_real :
    (QuadForm.diag ![(3 : ℚ), 7]).IsometricIn ℝ (QuadForm.diag ![(1 : ℚ), 84]) :=
  isometricIn_real_of_pos _ _ (fun i => by fin_cases i <;> norm_num)


/-- Helper: the Hilbert symbol $(-3, 15)_p$ equals $1$ exactly for $p \ne 3, 5$. -/
theorem hs_neg_three_fifteen (p : ℕ) [Fact p.Prime] :
    hilbertSymbol ℚ_[p] (-3) 15 = 1 ↔ p ≠ 3 ∧ p ≠ 5 := by
  by_cases h3 : p = 3
  · subst h3
    have := hs_neg_one_of_mod 3 2 (-3) 15 (by decide)
    simp at this
    simp [this]
  by_cases h5 : p = 5
  · subst h5
    have := hs_neg_one_of_mod 5 2 (-3) 15 (by decide)
    simp at this
    simp [this]
  by_cases h2 : p = 2
  · subst h2
    obtain ⟨r, hr⟩ := isSquare_two_of_mod_eight 57 (by norm_num)
    have := hs_eq_one_of_solution (-3 : ℚ_[2]) 15 1 2 r (by simp [Prod.ext_iff]) (by
      push_cast at hr; linear_combination (-1) * hr)
    simp [this]
  · have := hs_eq_one_of_not_dvd p h2 (-3) 15 (not_dvd_neg p (not_dvd_prime p 3 Nat.prime_three h3))
      (not_dvd_mul p (not_dvd_prime p 3 Nat.prime_three h3) (not_dvd_prime p 5 (by norm_num) h5))
    simp at this
    simp [this, h3, h5]

/-- Helper: the Hilbert symbol $(3, 3)_p$ equals $1$ exactly for $p \ne 2, 3$. -/
theorem hs_three_three (p : ℕ) [Fact p.Prime] :
    hilbertSymbol ℚ_[p] 3 3 = 1 ↔ p ≠ 2 ∧ p ≠ 3 := by
  by_cases h2 : p = 2
  · subst h2
    have := hs_neg_one_of_mod 2 3 3 3 (by decide)
    simp at this
    simp [this]
  by_cases h3 : p = 3
  · subst h3
    have := hs_neg_one_of_mod 3 2 3 3 (by decide)
    simp at this
    simp [this]
  · have := hs_eq_one_of_not_dvd p h2 3 3 (not_dvd_prime p 3 Nat.prime_three h3)
      (not_dvd_prime p 3 Nat.prime_three h3)
    simp at this
    simp [this, h2, h3]

/-- **Cassels, Ch. 4, Ex. 2 (ii), $p \ne \infty$ (p. 66).** *For which primes $p$ are
$x_1^2 - 3x_2^2 + 15x_3^2$ and $3x_1^2 - 5x_2^2 + 3x_3^2$ equivalent over $\mathbb Q_p$?* Answer: exactly for
$p \ne 2, 5$ (and over $\mathbb R$ always, `ex2_ii_real`). Proof: both determinants are $-45$; the Hasse
invariants are $(-3, 15)_p$ and $(3, -5)_p (3, 3)_p (-5, 3)_p = (3, 3)_p$, and $(-3, 15)_p = (3, 3)_p$ exactly
when $p \ne 2, 5$: at $p = 2$ they are $1$ and $-1$, at $p = 3$ both are $-1$, at $p = 5$ they are $-1$ and $1$,
and at every other prime both are $1$. -/
@[kb "cassels1978" "Ch. 4, Ex. 2 (ii) (p ≠ ∞), p. 66"]
theorem ex2_ii_padic (p : ℕ) [Fact p.Prime] :
    (QuadForm.diag ![(1 : ℚ), -3, 15]).IsometricIn ℚ_[p] (QuadForm.diag ![(3 : ℚ), -5, 3]) ↔
      p ≠ 2 ∧ p ≠ 5 := by
  rw [isometric_padic_iff_invariants p _ _ (fun i => by fin_cases i <;> norm_num)
    (fun i => by fin_cases i <;> norm_num), hasseInvariant_three, hasseInvariant_three]
  simp only [map_ofNat, map_neg, map_one, hs_one_left, one_mul]
  have hcomm := hilbertSymbol_comm ℚ_[p] (-5) 3
  have hsq : hilbertSymbol ℚ_[p] 3 (-5) * hilbertSymbol ℚ_[p] 3 (-5) = 1 := by
    rcases hs_pm (K := ℚ_[p]) 3 (-5) with h | h <;> rw [h] <;> norm_num
  have hB : hilbertSymbol ℚ_[p] 3 (-5) * hilbertSymbol ℚ_[p] 3 3 * hilbertSymbol ℚ_[p] (-5) 3 =
      hilbertSymbol ℚ_[p] 3 3 := by
    rw [hcomm]; linear_combination (hilbertSymbol ℚ_[p] 3 3) * hsq
  rw [hB]
  have hd : SameSquareClass ℚ_[p] (∏ i, (![(1 : ℚ), -3, 15] : Fin 3 → ℚ) i)
      (∏ i, (![(3 : ℚ), -5, 3] : Fin 3 → ℚ) i) :=
    ⟨1, one_ne_zero, by simp [Fin.prod_univ_three]; norm_num⟩
  have hA := hs_neg_three_fifteen p
  have hB' := hs_three_three p
  have hpmA := hs_pm (K := ℚ_[p]) (-3) 15
  have hpmB := hs_pm (K := ℚ_[p]) 3 3
  constructor
  · rintro ⟨-, h⟩
    by_cases h2 : p = 2
    · subst h2
      have a1 := hA.2 ⟨by norm_num, by norm_num⟩
      have b1 : ¬ hilbertSymbol ℚ_[2] 3 3 = 1 := fun hh => by have := hB'.1 hh; simp at this
      rw [a1] at h
      rcases hpmB with hh | hh
      · exact absurd hh b1
      · rw [hh] at h; norm_num at h
    · refine ⟨h2, fun h5 => ?_⟩
      subst h5
      have a1 : ¬ hilbertSymbol ℚ_[5] (-3) 15 = 1 := fun hh => by have := hA.1 hh; simp at this
      have b1 := hB'.2 ⟨by norm_num, by norm_num⟩
      rw [b1] at h
      rcases hpmA with hh | hh
      · exact a1 hh
      · rw [hh] at h; norm_num at h
  · rintro ⟨h2, h5⟩
    refine ⟨hd, ?_⟩
    by_cases h3 : p = 3
    · have a1 : ¬ hilbertSymbol ℚ_[p] (-3) 15 = 1 := fun hh => (hA.1 hh).1 h3
      have b1 : ¬ hilbertSymbol ℚ_[p] 3 3 = 1 := fun hh => (hB'.1 hh).2 h3
      rcases hpmA with ha | ha
      · exact absurd ha a1
      · rcases hpmB with hb | hb
        · exact absurd hb b1
        · rw [ha, hb]
    · rw [hA.2 ⟨h3, h5⟩, hB'.2 ⟨h2, h3⟩]

/-- **Cassels, Ch. 4, Ex. 2 (ii), $p = \infty$ (p. 66).** The forms $x_1^2 - 3x_2^2 + 15x_3^2$ and
$3x_1^2 - 5x_2^2 + 3x_3^2$ (both of signature $(2, 1)$) are equivalent over $\mathbb R$. -/
@[kb "cassels1978" "Ch. 4, Ex. 2 (ii) (p = ∞), p. 66"]
theorem ex2_ii_real :
    (QuadForm.diag ![(1 : ℚ), -3, 15]).IsometricIn ℝ (QuadForm.diag ![(3 : ℚ), -5, 3]) :=
  isometricIn_real_of_pos _ _ (fun i => by fin_cases i <;> norm_num)


/-- Helper: $v_p(105)$ is odd for $p = 3, 5, 7$ (it is $1$). -/
theorem odd_val_105 (p : ℕ) [hp : Fact p.Prime] (h : p = 3 ∨ p = 5 ∨ p = 7) : padicValInt p 105 % 2 = 1 := by
  have key : ∀ m : ℤ, (105 : ℤ) = p * m → ¬ (p : ℤ) ∣ m → padicValInt p 105 = 1 := by
    intro m hm hnd
    have hm0 : m ≠ 0 := fun h0 => hnd (h0 ▸ dvd_zero _)
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    rw [hm, padicValInt.mul hp0 hm0, padicValInt.eq_zero_of_not_dvd hnd]
    simp [padicValInt, hp.out.one_lt]
  rcases h with rfl | rfl | rfl
  · rw [key 35 (by norm_num) (by norm_num)]
  · rw [key 21 (by norm_num) (by norm_num)]
  · rw [key 15 (by norm_num) (by norm_num)]

/-- Helper: if $105$ is a square in $\mathbb Q_p$ then $(-5, 3)_p (-5, -7)_p (3, -7)_p = (-1, -1)_p$, i.e. the
Hasse invariants of $\langle 1, -5, 3, -7\rangle$ and $\langle 1, -1, 1, -1\rangle$ agree. At $p = 2$ the values
are $-1 \cdot 1 \cdot 1$ and $-1$; at $p = 3, 5, 7$ the hypothesis is false; at all other primes every symbol is
$1$. -/
theorem hasse_iii_of_square (p : ℕ) [Fact p.Prime] (hsq : IsSquare (105 : ℚ_[p])) :
    hilbertSymbol ℚ_[p] (-5) 3 * hilbertSymbol ℚ_[p] (-5) (-7) * hilbertSymbol ℚ_[p] 3 (-7) =
      hilbertSymbol ℚ_[p] (-1) (-1) := by
  by_cases h2 : p = 2
  · subst h2
    have a1 := hs_neg_one_of_mod 2 3 (-5) 3 (by decide)
    have c1 := hs_neg_one_of_mod 2 3 (-1) (-1) (by decide)
    have hs7 : IsSquare (((-7 : ℤ)) : ℚ_[2]) := isSquare_two_of_mod_eight (-7) (by norm_num)
    have b1 := hs_of_isSquare (-5 : ℚ_[2]) ((-7 : ℤ) : ℚ_[2]) (by norm_num) hs7
    have d1 := hs_of_isSquare (3 : ℚ_[2]) ((-7 : ℤ) : ℚ_[2]) (by norm_num) hs7
    simp at a1 b1 c1 d1
    rw [a1, b1, c1, d1]; norm_num
  · by_cases h357 : p = 3 ∨ p = 5 ∨ p = 7
    · exact absurd (by exact_mod_cast hsq) (not_isSquare_of_odd_val p 105 (odd_val_105 p h357))
    · push Not at h357
      obtain ⟨h3, h5, h7⟩ := h357
      have n3 := not_dvd_prime p 3 Nat.prime_three h3
      have n5 := not_dvd_prime p 5 (by norm_num) h5
      have n7 := not_dvd_prime p 7 (by norm_num) h7
      have n1 : ¬ (p : ℤ) ∣ 1 := (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).not_dvd_one
      have a1 := hs_eq_one_of_not_dvd p h2 (-5) 3 (not_dvd_neg p n5) n3
      have b1 := hs_eq_one_of_not_dvd p h2 (-5) (-7) (not_dvd_neg p n5) (not_dvd_neg p n7)
      have d1 := hs_eq_one_of_not_dvd p h2 3 (-7) n3 (not_dvd_neg p n7)
      have c1 := hs_eq_one_of_not_dvd p h2 (-1) (-1) (not_dvd_neg p n1) (not_dvd_neg p n1)
      simp at a1 b1 c1 d1
      rw [a1, b1, c1, d1]; norm_num

/-- **Cassels, Ch. 4, Ex. 2 (iii), $p \ne \infty$ (p. 66).** *For which primes $p$ are
$x_1^2 - 5x_2^2 + 3x_3^2 - 7x_4^2$ and $x_1^2 - x_2^2 + x_3^2 - x_4^2$ equivalent over $\mathbb Q_p$?* Answer:
exactly when $105$ is a square in $\mathbb Q_p$ (and over $\mathbb R$ always, `ex2_iii_real`). Concretely
(`ex2_iii_two`, `ex2_iii_padic_residue`): for $p = 2$ always ($105 \equiv 1 \bmod 8$); never for $p = 3, 5, 7$
($105$ has valuation $1$); for every other prime iff $105$ is a quadratic residue modulo $p$ (for example
$p = 13$ yes, $p = 11$ no). Proof: the determinants are $105$ and $1$, so they agree modulo squares iff $105$ is
a square; and then the Hasse invariants agree (`hasse_iii_of_square`). -/
@[kb "cassels1978" "Ch. 4, Ex. 2 (iii) (p ≠ ∞), p. 66"]
theorem ex2_iii_padic (p : ℕ) [Fact p.Prime] :
    (QuadForm.diag ![(1 : ℚ), -5, 3, -7]).IsometricIn ℚ_[p] (QuadForm.diag ![(1 : ℚ), -1, 1, -1]) ↔
      IsSquare (105 : ℚ_[p]) := by
  rw [isometric_padic_iff_invariants p _ _ (fun i => by fin_cases i <;> norm_num)
    (fun i => by fin_cases i <;> norm_num), hasseInvariant_four, hasseInvariant_four]
  have e1 : ∏ i, (![(1 : ℚ), -5, 3, -7] : Fin 4 → ℚ) i = 105 := by
    simp [Fin.prod_univ_four]; norm_num
  have e2 : ∏ i, (![(1 : ℚ), -1, 1, -1] : Fin 4 → ℚ) i = 1 := by
    simp [Fin.prod_univ_four]
  have hsc : SameSquareClass ℚ_[p] (∏ i, (![(1 : ℚ), -5, 3, -7] : Fin 4 → ℚ) i)
      (∏ i, (![(1 : ℚ), -1, 1, -1] : Fin 4 → ℚ) i) ↔ IsSquare (105 : ℚ_[p]) := by
    rw [e1, e2]
    unfold SameSquareClass
    simp only [map_ofNat, map_one, mul_one]
    constructor
    · rintro ⟨t, -, ht⟩
      exact ⟨t, by rw [ht]; ring⟩
    · rintro ⟨r, hr⟩
      refine ⟨r, fun h0 => ?_, by rw [hr]; ring⟩
      rw [h0] at hr
      norm_num at hr
  rw [hsc]
  refine ⟨fun h => h.1, fun hsq => ⟨hsq, ?_⟩⟩
  simp only [map_ofNat, map_neg, map_one, hs_one_left, hilbertSymbol_one_right, one_mul, mul_one]
  exact hasse_iii_of_square p hsq

/-- **Cassels, Ch. 4, Ex. 2 (iii), the prime $2$.** The two forms of `ex2_iii_padic` are equivalent over
$\mathbb Q_2$, since $105 \equiv 1 \pmod 8$ is a square in $\mathbb Q_2$. -/
@[kb "cassels1978" "Ch. 4, Ex. 2 (iii) (p = 2), p. 66"]
theorem ex2_iii_two :
    (QuadForm.diag ![(1 : ℚ), -5, 3, -7]).IsometricIn ℚ_[2] (QuadForm.diag ![(1 : ℚ), -1, 1, -1]) := by
  have := Fact.mk Nat.prime_two
  refine (ex2_iii_padic 2).2 ?_
  simpa using isSquare_two_of_mod_eight 105 (by norm_num)

/-- **Cassels, Ch. 4, Ex. 2 (iii), the odd primes $\ne 3, 5, 7$.** For a prime $p \ne 2, 3, 5, 7$ the forms are
equivalent over $\mathbb Q_p$ if and only if $105$ is a square modulo $p$. For $p = 3, 5, 7$ they are never
equivalent (`ex2_iii_three_five_seven`). -/
@[kb "cassels1978" "Ch. 4, Ex. 2 (iii) (odd p ≠ 3, 5, 7), p. 66"]
theorem ex2_iii_padic_residue (p : ℕ) [Fact p.Prime] (h2 : p ≠ 2) (h3 : p ≠ 3) (h5 : p ≠ 5) (h7 : p ≠ 7) :
    (QuadForm.diag ![(1 : ℚ), -5, 3, -7]).IsometricIn ℚ_[p] (QuadForm.diag ![(1 : ℚ), -1, 1, -1]) ↔
      IsSquare ((105 : ℤ) : ZMod p) := by
  rw [ex2_iii_padic, ← isSquare_odd_iff_residue p h2 105 (not_dvd_mul p
    (not_dvd_mul p (not_dvd_prime p 3 Nat.prime_three h3) (not_dvd_prime p 5 (by norm_num) h5))
    (not_dvd_prime p 7 (by norm_num) h7))]
  simp

/-- **Cassels, Ch. 4, Ex. 2 (iii), $p = 3, 5, 7$.** The forms are not equivalent over $\mathbb Q_p$ for
$p \in \{3, 5, 7\}$: the determinants $105$ and $1$ differ by a non-square. -/
@[kb "cassels1978" "Ch. 4, Ex. 2 (iii) (p = 3, 5, 7), p. 66"]
theorem ex2_iii_three_five_seven (p : ℕ) [Fact p.Prime] (h : p = 3 ∨ p = 5 ∨ p = 7) :
    ¬ (QuadForm.diag ![(1 : ℚ), -5, 3, -7]).IsometricIn ℚ_[p] (QuadForm.diag ![(1 : ℚ), -1, 1, -1]) := by
  rw [ex2_iii_padic]
  intro hsq
  exact not_isSquare_of_odd_val p 105 (odd_val_105 p h) (by exact_mod_cast hsq)

/-- **Cassels, Ch. 4, Ex. 2 (iii), $p = \infty$ (p. 66).** The forms $x_1^2 - 5x_2^2 + 3x_3^2 - 7x_4^2$ and
$x_1^2 - x_2^2 + x_3^2 - x_4^2$ (both of signature $(2, 2)$) are equivalent over $\mathbb R$. -/
@[kb "cassels1978" "Ch. 4, Ex. 2 (iii) (p = ∞), p. 66"]
theorem ex2_iii_real :
    (QuadForm.diag ![(1 : ℚ), -5, 3, -7]).IsometricIn ℝ (QuadForm.diag ![(1 : ℚ), -1, 1, -1]) :=
  isometricIn_real_of_pos _ _ (fun i => by fin_cases i <;> norm_num)


/-! ### Example 4 -/

/-- Helper: $c(f) = 1$ for $f = (m+1)(x_0^2 + x_1^2 + x_2^2) + m x_3^2$ over any field $K$ satisfying the
local Hilbert symbol axioms `LocalHilbertField` (for example $\mathbb Q_p$), for $m, m + 1 \in K^{\times}$.
Proof: $c(f) = (m+1, m+1)^3 (m+1, m)^3 = (m+1, -m)^3$ and $(m+1, -m) = 1$ because $z^2 = (m+1)x^2 - m y^2$
has the solution $x = y = z = 1$. -/
theorem hasseVec_ex4_gen {K : Type*} [Field K] [CharZero K] (hK : LocalHilbertField K) (m : K) (hm : m ≠ 0)
    (hm1 : m + 1 ≠ 0) : hasseVec ![m + 1, m + 1, m + 1, m] = 1 := by
  have hsol : hilbertSymbol K (m + 1) (-m) = 1 :=
    hs_eq_one_of_solution _ _ 1 1 1 (by simp [Prod.ext_iff]) (by ring)
  have hmul : hilbertSymbol K (m + 1) (m + 1) * hilbertSymbol K (m + 1) m = 1 := by
    rw [hK.self hm1, ← hK.mul_right hm1 (by norm_num) hm]
    rw [show (-1 : K) * m = -m by ring]
    exact hsol
  have h4 : hasseVec ![m + 1, m + 1, m + 1, m] =
      (hilbertSymbol K (m + 1) (m + 1) * hilbertSymbol K (m + 1) m) ^ 3 := by
    simp [hasseVec, Fin.prod_univ_four]
    ring
  rw [h4, hmul]; norm_num

/-- **Cassels, Ch. 4, Ex. 4 (first statement, p. 66).** For $m \in \mathbb Q_p^{\times}$ with $m \ne -1$
(here $m$ is an arbitrary element of $\mathbb Q_p$, not only a rational) and
$f = (m+1)(x_0^2 + x_1^2 + x_2^2) + m x_3^2$ (Cassels' $x_1, \dots, x_4$), the Hasse invariant is
$c_p(f) = 1$. Proof: `hasseVec_ex4_gen`, which reduces to $(m+1, -m)_p = 1$ (Chapter 3, Ex. 9; here the solution
$x = y = z = 1$ of $z^2 = (m+1)x^2 - my^2$). The hypothesis $m \ne 0$ is part of "$m \in \mathbb Q_p^{\times}$". -/
@[kb "cassels1978" "Ch. 4, Ex. 4 (c_p(f) = 1), p. 66"]
theorem ex4_hasse (p : ℕ) [Fact p.Prime] (m : ℚ_[p]) (hm : m ≠ 0) (hm1 : m ≠ -1) :
    hasseVec ![m + 1, m + 1, m + 1, m] = 1 :=
  hasseVec_ex4_gen (localHilbertField_padic p) m hm (fun h => hm1 (by linear_combination h))

/-- **Cassels, Ch. 4, Ex. 4 (equivalence, $p \ne \infty$, p. 66).** For $m \in \mathbb Q_p^{\times}$ with
$m \ne -1$, the form $(m+1)(x_0^2 + x_1^2 + x_2^2) + m x_3^2$ is equivalent over $\mathbb Q_p$ to
$x_0^2 + x_1^2 + x_2^2 + m(m+1)x_3^2$. Proof: the determinants $(m+1)^3 m$ and $m(m+1)$ agree modulo squares,
and both Hasse invariants are $1$ (`ex4_hasse`, and the second form has $1$ in three positions); apply
Theorem 1.1. -/
@[kb "cassels1978" "Ch. 4, Ex. 4 (equivalence, p ≠ ∞), p. 66"]
theorem ex4_padic (p : ℕ) [Fact p.Prime] (m : ℚ_[p]) (hm : m ≠ 0) (hm1 : m ≠ -1) :
    (diag ![m + 1, m + 1, m + 1, m]).IsometricIn ℚ_[p] (diag ![1, 1, 1, m * (m + 1)]) := by
  have hK := localHilbertField_padic p
  have hm1' : m + 1 ≠ 0 := fun h => hm1 (by linear_combination h)
  rw [isometric_iff_invariants hK (fun i => by fin_cases i <;> simp [hm, hm1'])
    (fun i => by fin_cases i <;> simp [hm, hm1'])]
  refine ⟨⟨1 / (m + 1), by simp [hm1'], ?_⟩, ?_⟩
  · simp [Fin.prod_univ_four]
    field_simp
  · rw [ex4_hasse p m hm hm1]
    simp [hasseVec, Fin.prod_univ_four, hs_one_left]

/-- **Cassels, Ch. 4, Ex. 4 ("What happens for $p = \infty$?", p. 66).** For real $m \ne 0, -1$ the forms
$(m+1)(x_0^2 + x_1^2 + x_2^2) + m x_3^2$ and $x_0^2 + x_1^2 + x_2^2 + m(m+1)x_3^2$ are equivalent over
$\mathbb R$ if and only if $m > -1$. Proof: for $m > -1$ the coefficients have matching signs
($m + 1 > 0$; $m \cdot m(m+1) > 0$). For $m < -1$ the first form is negative definite, while the second
represents $1$. -/
@[kb "cassels1978" "Ch. 4, Ex. 4 (p = ∞), p. 66"]
theorem ex4_real (m : ℝ) (hm : m ≠ 0) (hm1 : m ≠ -1) :
    (diag ![m + 1, m + 1, m + 1, m]).IsometricIn ℝ (diag ![1, 1, 1, m * (m + 1)]) ↔ -1 < m := by
  constructor
  · intro h
    by_contra hneg
    have hlt : m < -1 := lt_of_le_of_ne (not_lt.1 hneg) hm1
    have hr : (diag ![m + 1, m + 1, m + 1, m]).RepresentsIn ℝ 1 := by
      refine representsIn_of_isometricIn ℝ h ?_
      rw [representsIn_diag_iff]
      exact ⟨![1, 0, 0, 0], by simp [Fin.sum_univ_four]⟩
    rw [representsIn_diag_iff] at hr
    obtain ⟨z, hz⟩ := hr
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hz
    nlinarith [sq_nonneg (z 0), sq_nonneg (z 1), sq_nonneg (z 2), sq_nonneg (z 3)]
  · intro hgt
    refine isometricIn_real_of_pos _ _ (fun i => ?_)
    have h1 : 0 < m + 1 := by linarith
    have h2 : 0 < m * m := mul_self_pos.2 hm
    fin_cases i
    · simpa using h1
    · simpa using h1
    · simpa using h1
    · simp
      nlinarith

end QuadFormsKB.Cassels.Ch4Scan
