import QuadFormsKB.Literature.Cassels.AppB.Ex5Schur
import QuadFormsKB.Literature.Cassels.AppB.Ex1Ex4
import QuadFormsKB.Literature.Cassels.AppB.Ex2

/-!
# Cassels, Appendix B, §2: the Gauss sum (2.20) of a fundamental discriminant, proved

Cassels, *Rational Quadratic Forms* (1978), Appendix B (*Analytic methods*), §2, formula (2.20), p. 374, which the book
"assumes as known" (see also Example 5, p. 390).

**Statement.** For a fundamental discriminant $D \ne 1$ (`IsQuadDisc D`) and every integer $m$,
$\sum_{0 \le r < |D|}\chi_D(r)\,e^{2\pi i r m/|D|} = \chi_D(m)\cdot\sqrt D$ if $D > 0$ and $\chi_D(m)\cdot i\sqrt{|D|}$
if $D < 0$ (`KroneckerGaussSum D`, constant `gaussConst D`).

**Conventions.** $\chi_D$ is `kroneckerChar D`, a Dirichlet character modulo $|D|$ (`D.natAbs`); Jacobi symbols
$(a/n)$ are Mathlib's `jacobiSym a n`; $e(x) = e^{2\pi i x}$; sums over $0 \le r < |D|$ are over `Finset.range D.natAbs`.
No index shift is involved.

**Formalized (all proved, unconditional).**

* `kroneckerGaussSum_holds`: (2.20) itself, the named statement `KroneckerGaussSum D` of `Sec2Lemmas.lean`.
* `gauss_sum_sign`: the sign of the Gauss sum at $m = 1$; with `kroneckerGaussSum_of_sign` (`Ex1Ex4.lean`: the dependence on
  $m$ from primitivity of $\chi_D$) this gives (2.20).
* `jacChar` (Jacobi character modulo $n$), `gauss_jacChar_aux` (its Gauss sum for odd squarefree $n$, by induction on
  the number of prime factors from Example 2, quadratic reciprocity and the sign of Schur, Example 5), `gauss_sum_odd`
  ($D \equiv 1 \pmod 4$), `gauss_sum_even_a`, `gauss_sum_even_b1`, `gauss_sum_even_b2` ($D = -4E, 8E, -8E$).
* Unconditional versions of the consequences that were conditional on (2.20): Lemma 2.3
  (`lemma_2_3_pos_unconditional`, `lemma_2_3_neg_unconditional`), Theorem 2.1 (i) in finite-sum form
  (`finite_sum_class_number_neg_unconditional`) and Example 1 (`class_number_half_sum_unconditional`).

**Route.** The book's hint (reduce by Example 2 to prime discriminants $p^*$, $-4$, $\pm8$) is followed, except that the
reduction is done on the odd squarefree modulus rather than on the discriminant (every odd factor with its Jacobi
character), and the even part is split off once.

No erratum was found in (2.20) itself (the printed "$D = 0$" in the second case of the constant is a misprint for
$D < 0$, noted at `gaussConst`).
-/

open Complex
open QuadFormsKB.Binary

namespace QuadFormsKB.Cassels

/-- Helper: the Jacobi symbol $J(\cdot \mid n)$ of the canonical representative of a residue. -/
theorem jac_val_eq {n : ℕ} [NeZero n] (x : ZMod n) (r : ℤ) (h : (r : ZMod n) = x) :
    jacobiSym (x.val : ℤ) n = jacobiSym r n := by
  subst h
  apply jacobiSym.mod_left'
  rw [ZMod.val_intCast, Int.emod_emod_of_dvd _ dvd_rfl]

/-- Helper: the Jacobi symbol $x \mapsto (x/n)$ as a complex-valued multiplicative character on $\mathbb Z/n$. -/
noncomputable def jacChar (n : ℕ) [NeZero n] : MulChar (ZMod n) ℂ where
  toFun x := ((jacobiSym (x.val : ℤ) n : ℤ) : ℂ)
  map_one' := by
    rw [jac_val_eq (1 : ZMod n) 1 (by simp)]
    simp
  map_mul' x y := by
    have hx : (((x.val : ℤ)) : ZMod n) = x := by simp
    have hy : (((y.val : ℤ)) : ZMod n) = y := by simp
    rw [jac_val_eq (x * y) ((x.val : ℤ) * y.val) (by simp), jacobiSym.mul_left]
    push_cast; rfl
  map_nonunit' x hx := by
    have hN0 : n ≠ 0 := NeZero.ne n
    rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime] at hx
    rw [(jacobiSym.eq_zero_iff).mpr ⟨hN0, by rwa [Int.gcd_natCast_natCast]⟩]
    simp

/-- Helper: `jacChar n` at the residue of an integer $r$ is the Jacobi symbol $(r/n)$. -/
theorem jacChar_intCast {n : ℕ} [NeZero n] (r : ℤ) : jacChar n (r : ZMod n) = (jacobiSym r n : ℂ) := by
  show ((jacobiSym (((r : ZMod n)).val : ℤ) n : ℤ) : ℂ) = _
  rw [jac_val_eq _ r rfl]

/-- Helper: `jacChar n` at the residue of a natural number $k$ is the Jacobi symbol $(k/n)$. -/
theorem jacChar_natCast {n : ℕ} [NeZero n] (k : ℕ) : jacChar n (k : ZMod n) = (jacobiSym k n : ℂ) := by
  have := jacChar_intCast (n := n) (k : ℤ)
  simpa using this

/-- Helper: for a prime $p$ the character `jacChar p` is the Legendre character `quadDir p`. -/
theorem jacChar_prime (p : ℕ) [hp : Fact p.Prime] : jacChar p = quadDir p := by
  ext x
  show ((jacobiSym ((x : ZMod p).val : ℤ) p : ℤ) : ℂ) = ((quadraticChar (ZMod p) (x : ZMod p) : ℤ) : ℂ)
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  congr 2
  unfold legendreSym
  simp

/-- Helper: Mathlib's Gauss sum over $\mathbb Z/N$ is the sum over $0 \le r < N$ of
$\chi(r)\,e^{2\pi i r/N}$. Arguments: `N` the modulus, `χ` the character. -/
theorem gaussSum_eq_range {N : ℕ} [NeZero N] (χ : MulChar (ZMod N) ℂ) :
    gaussSum χ ZMod.stdAddChar =
      ∑ r ∈ Finset.range N, χ (r : ZMod N) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) / (N : ℂ)) := by
  unfold gaussSum
  refine Finset.sum_nbij' (fun x => x.val) (fun r => (r : ZMod N)) ?_ ?_ ?_ ?_ ?_
  · intro x _; simpa using ZMod.val_lt x
  · intro r _; simp
  · intro x _; simp
  · intro r hr; simpa using ZMod.val_natCast_of_lt (Finset.mem_range.mp hr)
  · intro x _
    have e1 : ZMod.stdAddChar x = Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) / (N : ℂ)) := by
      have := ZMod.stdAddChar_coe (N := N) (x.val : ℤ)
      rw [Int.cast_natCast, ZMod.natCast_zmod_val] at this
      rw [this]; push_cast; rfl
    rw [e1, ZMod.natCast_zmod_val]

/-- Helper: the product of the two Jacobi symbols $(m/p)(p/m)$ for coprime odd naturals, in the reciprocity form
$(p/m) = \pm(m/p)$. -/
theorem jac_recip {p m : ℕ} (hp : p % 2 = 1) (hm : m % 2 = 1) (hc : Nat.Coprime p m) :
    jacobiSym m p * jacobiSym p m = if p % 4 = 3 ∧ m % 4 = 3 then -1 else 1 := by
  have h := jacobiSym.quadratic_reciprocity_if hp hm
  have hg : (m : ℤ).gcd p = 1 := by rw [Int.gcd_natCast_natCast]; exact hc.symm
  have hs : jacobiSym m p * jacobiSym m p = 1 := by
    rcases jacobiSym.eq_one_or_neg_one hg with h1 | h1 <;> rw [h1] <;> norm_num
  rw [← h]
  split_ifs
  · linear_combination -hs
  · linear_combination hs

/-- Helper: the Gauss sum $\sum_{r}(r/n)\,e(r/n)$ of the Jacobi character of an odd squarefree $n$ is $\sqrt n$ for
$n \equiv 1 \pmod 4$ and $i\sqrt n$ for $n \equiv 3 \pmod 4$ (induction on the number of prime factors, with Example 2 and
quadratic reciprocity; the prime case is `gauss_sum_tau`). Arguments: `n` the modulus (`hn : 0 < n`), `hodd` that it is
odd, and the squarefreeness hypothesis. -/
theorem gauss_jacChar_aux : ∀ (n : ℕ) (hn : 0 < n), n % 2 = 1 → Squarefree n →
    @casselsGauss n ⟨hn.ne'⟩ (@jacChar n ⟨hn.ne'⟩) =
      if n % 4 = 1 then ((Real.sqrt n : ℝ) : ℂ) else Complex.I * ((Real.sqrt n : ℝ) : ℂ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn hodd hsq
  have : NeZero n := ⟨hn.ne'⟩
  by_cases h1 : n = 1
  · subst h1
    rw [casselsGauss_eq_gaussSum, gaussSum_eq_range]
    simp [jacChar_natCast]
  · obtain ⟨p, m, hp, hnm⟩ : ∃ p m : ℕ, p.Prime ∧ n = p * m :=
      ⟨n.minFac, n / n.minFac, Nat.minFac_prime h1, (Nat.mul_div_cancel' (Nat.minFac_dvd n)).symm⟩
    subst hnm
    have : Fact p.Prime := ⟨hp⟩
    have hm0 : 0 < m := Nat.pos_of_ne_zero (fun h => by simp [h] at hn)
    have : NeZero m := ⟨hm0.ne'⟩
    have : NeZero p := ⟨hp.ne_zero⟩
    have hpodd : p % 2 = 1 := by
      have := Nat.mul_mod p m 2; rcases Nat.mod_two_eq_zero_or_one p with h | h
      · rw [h] at this; simp at this; omega
      · exact h
    have hmodd : m % 2 = 1 := by
      have := Nat.mul_mod p m 2; rcases Nat.mod_two_eq_zero_or_one m with h | h
      · rw [h] at this; simp at this; omega
      · exact h
    have hcop : Nat.Coprime p m := Nat.coprime_of_squarefree_mul hsq
    have hmlt : m < p * m := by
      have := hp.two_le; nlinarith
    have hgm := ih m hmlt hm0 hmodd (Squarefree.of_mul_right hsq)
    have hgp : casselsGauss (jacChar p) =
        if p % 4 = 1 then ((Real.sqrt p : ℝ) : ℂ) else Complex.I * ((Real.sqrt p : ℝ) : ℂ) := by
      rw [jacChar_prime, casselsGauss_eq_gaussSum]
      exact gauss_sum_tau p (by omega)
    have hfac : ∀ r : ℤ, jacChar (p * m) (r : ZMod (p * m)) =
        jacChar p (r : ZMod p) * jacChar m (r : ZMod m) := by
      intro r
      rw [jacChar_intCast, jacChar_intCast, jacChar_intCast, jacobiSym.mul_right]
      push_cast; rfl
    have hmul := casselsGauss_mul hcop (jacChar (p * m)) (jacChar p) (jacChar m) hfac
    have hrec := jac_recip hpodd hmodd hcop
    have e1 : jacChar p (m : ZMod p) = (jacobiSym m p : ℂ) := jacChar_natCast m
    have e2 : jacChar m (p : ZMod m) = (jacobiSym p m : ℂ) := jacChar_natCast p
    have ha : (jacobiSym m p : ℂ) * (jacobiSym p m : ℂ) = if p % 4 = 3 ∧ m % 4 = 3 then -1 else 1 := by
      exact_mod_cast hrec
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have hsq2 : ((Real.sqrt (p * m : ℕ) : ℝ) : ℂ) = ((Real.sqrt p : ℝ) : ℂ) * ((Real.sqrt m : ℝ) : ℂ) := by
      rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg p)]; push_cast; rfl
    rw [hmul, hgp, hgm, e1, e2, hsq2]
    have hpm4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    have hmm4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
    rcases hpm4 with h4 | h4 <;> rcases hmm4 with h5 | h5
    · have h6 : (p * m) % 4 = 1 := by rw [Nat.mul_mod, h4, h5]
      have n1 : ¬ (p % 4 = 3 ∧ m % 4 = 3) := by omega
      rw [if_pos h4, if_pos h5, if_pos h6]
      rw [if_neg n1] at ha
      linear_combination (((Real.sqrt p : ℝ) : ℂ) * ((Real.sqrt m : ℝ) : ℂ)) * ha
    · have h6 : (p * m) % 4 = 3 := by rw [Nat.mul_mod, h4, h5]
      have n1 : ¬ (p % 4 = 3 ∧ m % 4 = 3) := by omega
      rw [if_pos h4, if_neg (by omega : ¬ m % 4 = 1), if_neg (by omega : ¬ (p * m) % 4 = 1)]
      rw [if_neg n1] at ha
      linear_combination (Complex.I * ((Real.sqrt p : ℝ) : ℂ) * ((Real.sqrt m : ℝ) : ℂ)) * ha
    · have h6 : (p * m) % 4 = 3 := by rw [Nat.mul_mod, h4, h5]
      have n1 : ¬ (p % 4 = 3 ∧ m % 4 = 3) := by omega
      rw [if_neg (by omega : ¬ p % 4 = 1), if_pos h5, if_neg (by omega : ¬ (p * m) % 4 = 1)]
      rw [if_neg n1] at ha
      linear_combination (Complex.I * ((Real.sqrt p : ℝ) : ℂ) * ((Real.sqrt m : ℝ) : ℂ)) * ha
    · have h6 : (p * m) % 4 = 1 := by rw [Nat.mul_mod, h4, h5]
      rw [if_neg (by omega : ¬ p % 4 = 1), if_neg (by omega : ¬ m % 4 = 1), if_pos h6]
      rw [if_pos ⟨h4, h5⟩] at ha
      linear_combination (Complex.I * Complex.I * ((Real.sqrt p : ℝ) : ℂ) * ((Real.sqrt m : ℝ) : ℂ)) * ha - (((Real.sqrt p : ℝ) : ℂ) * ((Real.sqrt m : ℝ) : ℂ)) * hI

/-- Helper: $\mathrm{gaussConst}\,D = \sqrt{|D|}$ for $D > 0$. -/
theorem gaussConst_of_pos {D : ℤ} (hD : 0 < D) : gaussConst D = ((Real.sqrt (D.natAbs : ℝ) : ℝ) : ℂ) := by
  simp [gaussConst, hD, Nat.cast_natAbs]

/-- Helper: $\mathrm{gaussConst}\,D = i\sqrt{|D|}$ for $D < 0$. -/
theorem gaussConst_of_neg {D : ℤ} (hD : D < 0) :
    gaussConst D = Complex.I * ((Real.sqrt (D.natAbs : ℝ) : ℝ) : ℂ) := by
  rw [mul_comm]
  simp [gaussConst, not_lt.mpr hD.le, Nat.cast_natAbs]

/-- Helper: for $D \equiv 1 \pmod 4$ the Kronecker character is the Jacobi character modulo $|D|$. -/
theorem kroneckerChar_eq_jacChar {D : ℤ} [IsQuadDisc D] (h : D % 4 = 1) :
    kroneckerChar D = @jacChar D.natAbs ⟨by have := three_le_natAbs (D := D); omega⟩ := by
  ext x
  rw [kroneckerChar_apply, kronZ, if_pos h]
  rfl

/-- Helper: the Gauss sum (2.20) at $m = 1$ for $D \equiv 1 \pmod 4$. -/
theorem gauss_sum_odd {D : ℤ} [hD : IsQuadDisc D] (h : D % 4 = 1) :
    ∑ r ∈ Finset.range D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
      Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) / (D.natAbs : ℂ)) = gaussConst D := by
  have h3 := three_le_natAbs (D := D)
  have : NeZero D.natAbs := ⟨by omega⟩
  have hsq : Squarefree D.natAbs := by
    rcases Int.isFundamentalDiscr_iff_squarefree.mp hD.fund with ⟨_, h2⟩ | ⟨h2, _⟩
    · exact Int.squarefree_natAbs.mpr h2
    · omega
  rw [← gaussSum_eq_range, kroneckerChar_eq_jacChar h, ← casselsGauss_eq_gaussSum]
  refine (gauss_jacChar_aux D.natAbs (by omega) (by omega) hsq).trans ?_
  by_cases hpos : 0 < D
  · rw [if_pos (by omega), gaussConst_of_pos hpos]
  · have hneg : D < 0 := by omega
    rw [if_neg (by omega), gaussConst_of_neg hneg]

/-- Helper: Gauss sum of a product of characters, for characters evaluated at natural numbers. -/
theorem casselsGauss_mul_nat {N l n : ℕ} [NeZero N] [NeZero l] [NeZero n] (hN : N = l * n)
    (hc : l.Coprime n) (χ : MulChar (ZMod N) ℂ) (ψ : MulChar (ZMod l) ℂ) (φ : MulChar (ZMod n) ℂ)
    (hfac : ∀ k : ℕ, χ (k : ZMod N) = ψ (k : ZMod l) * φ (k : ZMod n)) :
    casselsGauss χ = ψ (n : ZMod l) * φ (l : ZMod n) * (casselsGauss ψ * casselsGauss φ) := by
  subst hN
  apply casselsGauss_mul hc χ ψ φ
  intro r
  set k := (r : ZMod (l * n)).val
  have hk : (r : ZMod (l * n)) = (k : ZMod (l * n)) := (ZMod.natCast_zmod_val _).symm
  have h1 : (r : ZMod l) = (k : ZMod l) := by
    have := congrArg (ZMod.castHom (dvd_mul_right l n) (ZMod l)) hk
    simpa using this
  have h2 : (r : ZMod n) = (k : ZMod n) := by
    have := congrArg (ZMod.castHom (dvd_mul_left n l) (ZMod n)) hk
    simpa using this
  rw [hk, h1, h2]
  exact hfac k

/-- Helper: quadratic reciprocity in the form $(E/k) = (k/|E|)$ for $E \equiv 1 \pmod 4$ and odd $k$. -/
theorem jac_recip_int {E : ℤ} (hE : E % 4 = 1) {k : ℕ} (hk : k % 2 = 1) :
    jacobiSym E k = jacobiSym k E.natAbs := by
  have hko : Odd k := Nat.odd_iff.mpr hk
  rcases lt_trichotomy E 0 with h | h | h
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, E = -(n : ℤ) := ⟨E.natAbs, by omega⟩
    have hn4 : n % 4 = 3 := by omega
    have hna : E.natAbs = n := by omega
    rw [hna, hn, jacobiSym.neg _ hko]
    have := jacobiSym.quadratic_reciprocity_if (a := k) (b := n) hk (by omega)
    rw [← this, ZMod.χ₄_nat_eq_if_mod_four]
    rcases Nat.odd_mod_four_iff.mp hk with h1 | h1 <;> simp [h1, hn4, show ¬ (k % 2 = 0) by omega]
  · omega
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, E = (n : ℤ) := ⟨E.natAbs, by omega⟩
    have hna : E.natAbs = n := by omega
    rw [hna, hn]
    exact (jacobiSym.quadratic_reciprocity_one_mod_four' hko (by omega)).symm

/-- Helper: values of the Kronecker character of an even fundamental discriminant at natural numbers. -/
theorem kroneckerChar_even_apply {D : ℤ} [IsQuadDisc D] (h : D % 4 = 0) (k : ℕ) :
    kroneckerChar D (k : ZMod D.natAbs) = if k % 2 = 1 then (jacobiSym (D / 4) k : ℂ) else 0 := by
  have h3 := three_le_natAbs (D := D)
  have : NeZero D.natAbs := ⟨by omega⟩
  rw [kroneckerChar_apply]
  split_ifs with hk
  · rw [kronZ_natCast_of_zero h (Nat.odd_iff.mpr hk)]
  · rw [kronZ, if_neg (by omega), ZMod.val_natCast, if_neg]
    · simp
    · rw [odd_mod_natAbs_iff (by omega) k, Nat.odd_iff]; exact hk

/-- Helper: factorization of the Kronecker character of an even fundamental discriminant $D = d_1 E$ into a character
$\psi$ modulo the $2$-part and the Jacobi character modulo $|E|$. -/
theorem even_hfac {D : ℤ} [IsQuadDisc D] (h : D % 4 = 0) {E c1 : ℤ} (hE : E % 4 = 1) (hc : D / 4 = c1 * E)
    {l : ℕ} [NeZero l] (ψ : MulChar (ZMod l) ℂ) (he : ∀ k : ℕ, k % 2 = 0 → ψ (k : ZMod l) = 0)
    (ho : ∀ k : ℕ, k % 2 = 1 → ψ (k : ZMod l) = (jacobiSym c1 k : ℂ)) [NeZero E.natAbs] (k : ℕ) :
    kroneckerChar D (k : ZMod D.natAbs) = ψ (k : ZMod l) * jacChar E.natAbs (k : ZMod E.natAbs) := by
  rw [kroneckerChar_even_apply h]
  by_cases hk : k % 2 = 1
  · rw [if_pos hk, ho k hk, jacChar_natCast, hc, jacobiSym.mul_left, jac_recip_int hE hk]
    push_cast; rfl
  · rw [if_neg hk, he k (by omega), zero_mul]

/-- Helper: $e^{2\pi i k/N} = (e^{2\pi i/N})^k$. -/
theorem exp_div_pow (N k : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (N : ℂ)) = Complex.exp (2 * Real.pi * Complex.I / (N : ℂ)) ^ k := by
  rw [← Complex.exp_nat_mul]; congr 1; ring

/-- Helper: $e^{2\pi i/8} = \frac{\sqrt2}{2}(1 + i)$. -/
theorem exp_eighth : Complex.exp (2 * Real.pi * Complex.I / ((8 : ℕ) : ℂ)) =
    ((Real.sqrt 2 : ℝ) : ℂ) / 2 * (1 + Complex.I) := by
  have : (2 * Real.pi * Complex.I / ((8 : ℕ) : ℂ)) = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  push_cast; ring

/-- Helper: the character $\left(\frac{-4}{\cdot}\right)$ modulo $4$, complex valued. -/
noncomputable def psi4 : MulChar (ZMod 4) ℂ := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

/-- Helper: the character $\left(\frac{8}{\cdot}\right)$ modulo $8$, complex valued. -/
noncomputable def psi8 : MulChar (ZMod 8) ℂ := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)

/-- Helper: the character $\left(\frac{-8}{\cdot}\right)$ modulo $8$, complex valued. -/
noncomputable def psi8' : MulChar (ZMod 8) ℂ := ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ)

/-- Helper: $\sqrt2$ as a complex number. -/
noncomputable abbrev sqrt2C : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)

/-- Helper: $(\sqrt2)^2 = 2$ in $\mathbb C$. -/
theorem sqrt2C_sq : sqrt2C ^ 2 = 2 := by
  unfold sqrt2C
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- Helper: the primitive eighth root of unity $\zeta = \frac{\sqrt2}{2}(1+i)$ and its powers. -/
noncomputable abbrev zeta8 : ℂ := sqrt2C / 2 * (1 + Complex.I)

/-- Helper: $\zeta^2 = i$ for $\zeta = e^{2\pi i/8}$ (`zeta8`). -/
theorem zeta8_sq : zeta8 ^ 2 = Complex.I := by
  have ha := sqrt2C_sq
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  unfold zeta8
  linear_combination ((1 + Complex.I) ^ 2 / 4) * ha + (1 / 2) * hI

/-- Helper: $\zeta^3 = i\zeta$. -/
theorem zeta8_pow3 : zeta8 ^ 3 = Complex.I * zeta8 := by
  linear_combination zeta8 * zeta8_sq

/-- Helper: $\zeta^5 = -\zeta$. -/
theorem zeta8_pow5 : zeta8 ^ 5 = -zeta8 := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (zeta8 * (zeta8 ^ 2 + Complex.I)) * zeta8_sq + zeta8 * hI

/-- Helper: $\zeta^7 = -i\zeta$. -/
theorem zeta8_pow7 : zeta8 ^ 7 = -(Complex.I * zeta8) := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (zeta8 * (zeta8 ^ 4 + zeta8 ^ 2 * Complex.I + Complex.I ^ 2)) * zeta8_sq + (zeta8 * Complex.I) * hI

/-- Helper: the Gauss sum $\tau(\chi_8, 8) = 2\sqrt2$ of the character $\left(\frac{8}{\cdot}\right)$ (`psi8`). -/
theorem casselsGauss_psi8 : casselsGauss psi8 = 2 * sqrt2C := by
  rw [casselsGauss_eq_gaussSum, gaussSum_eq_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, psi8, MulChar.ringHomComp_apply,
    ZMod.χ₈_nat_eq_if_mod_eight, exp_div_pow, exp_eighth]
  norm_num
  change zeta8 + -zeta8 ^ 3 + -zeta8 ^ 5 + zeta8 ^ 7 = _
  rw [zeta8_pow3, zeta8_pow5, zeta8_pow7]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  unfold zeta8
  linear_combination (-sqrt2C) * hI

/-- Helper: the Gauss sum $\tau(\chi_{-8}, 8) = 2\sqrt2\, i$ of the character $\left(\frac{-8}{\cdot}\right)$ (`psi8'`). -/
theorem casselsGauss_psi8' : casselsGauss psi8' = 2 * sqrt2C * Complex.I := by
  rw [casselsGauss_eq_gaussSum, gaussSum_eq_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, psi8', MulChar.ringHomComp_apply,
    ZMod.χ₈'_nat_eq_if_mod_eight, exp_div_pow, exp_eighth]
  norm_num
  change zeta8 + zeta8 ^ 3 + -zeta8 ^ 5 + -zeta8 ^ 7 = _
  rw [zeta8_pow3, zeta8_pow5, zeta8_pow7]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  unfold zeta8
  linear_combination sqrt2C * hI

/-- Helper: $e^{2\pi i/4} = i$. -/
theorem exp_quarter : Complex.exp (2 * Real.pi * Complex.I / ((4 : ℕ) : ℂ)) = Complex.I := by
  rw [show 2 * Real.pi * Complex.I / ((4 : ℕ) : ℂ) = (Real.pi : ℂ) / 2 * Complex.I by push_cast; ring]
  exact Complex.exp_pi_div_two_mul_I

/-- Helper: the Gauss sum $\tau(\chi_{-4}, 4) = 2i$ of the character $\left(\frac{-4}{\cdot}\right)$ (`psi4`). -/
theorem casselsGauss_psi4 : casselsGauss psi4 = 2 * Complex.I := by
  rw [casselsGauss_eq_gaussSum, gaussSum_eq_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, psi4, MulChar.ringHomComp_apply,
    ZMod.χ₄_nat_eq_if_mod_four, exp_div_pow, exp_quarter]
  norm_num
  ring

/-- Helper: `psi4` vanishes at even residues. Argument: `k` the natural number, `hk` that it is even. -/
theorem psi4_even (k : ℕ) (hk : k % 2 = 0) : psi4 (k : ZMod 4) = 0 := by
  rw [psi4, MulChar.ringHomComp_apply, ZMod.χ₄_nat_eq_if_mod_four, if_pos hk]; simp

/-- Helper: `psi4` at an odd $k$ is the Jacobi symbol $(-1/k)$. Argument: `k`, `hk` that it is odd. -/
theorem psi4_odd (k : ℕ) (hk : k % 2 = 1) : psi4 (k : ZMod 4) = (jacobiSym (-1) k : ℂ) := by
  rw [jacobiSym.at_neg_one (Nat.odd_iff.mpr hk)]
  simp [psi4]

/-- Helper: `psi8` vanishes at even residues. Argument: `k`, `hk` that it is even. -/
theorem psi8_even (k : ℕ) (hk : k % 2 = 0) : psi8 (k : ZMod 8) = 0 := by
  rw [psi8, MulChar.ringHomComp_apply, ZMod.χ₈_nat_eq_if_mod_eight, if_pos hk]; simp

/-- Helper: `psi8` at an odd $k$ is the Jacobi symbol $(2/k)$. Argument: `k`, `hk` that it is odd. -/
theorem psi8_odd (k : ℕ) (hk : k % 2 = 1) : psi8 (k : ZMod 8) = (jacobiSym 2 k : ℂ) := by
  rw [jacobiSym.at_two (Nat.odd_iff.mpr hk)]
  simp [psi8]

/-- Helper: `psi8'` vanishes at even residues. Argument: `k`, `hk` that it is even. -/
theorem psi8'_even (k : ℕ) (hk : k % 2 = 0) : psi8' (k : ZMod 8) = 0 := by
  rw [psi8', MulChar.ringHomComp_apply, ZMod.χ₈'_nat_eq_if_mod_eight, if_pos hk]; simp

/-- Helper: `psi8'` at an odd $k$ is the Jacobi symbol $(-2/k)$. Argument: `k`, `hk` that it is odd. -/
theorem psi8'_odd (k : ℕ) (hk : k % 2 = 1) : psi8' (k : ZMod 8) = (jacobiSym (-2) k : ℂ) := by
  rw [jacobiSym.at_neg_two (Nat.odd_iff.mpr hk)]
  simp [psi8']

/-- Helper: the core of the even case: the Gauss sum of $\chi_D$ for $D = d_1 E$ in terms of the two factors. -/
theorem even_core {D : ℤ} [IsQuadDisc D] (h : D % 4 = 0) {E c1 : ℤ} {n l : ℕ} [NeZero n] [NeZero l]
    (hE : E % 4 = 1) (hc : D / 4 = c1 * E) (hn : E.natAbs = n) (ψ : MulChar (ZMod l) ℂ)
    (he : ∀ k : ℕ, k % 2 = 0 → ψ (k : ZMod l) = 0)
    (ho : ∀ k : ℕ, k % 2 = 1 → ψ (k : ZMod l) = (jacobiSym c1 k : ℂ))
    (hDn : D.natAbs = l * n) (hcop : l.Coprime n) :
    ∑ r ∈ Finset.range D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
      Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) / (D.natAbs : ℂ)) =
    ψ (n : ZMod l) * jacChar n (l : ZMod n) * (casselsGauss ψ * casselsGauss (jacChar n)) := by
  have h3 := three_le_natAbs (D := D)
  have : NeZero D.natAbs := ⟨by omega⟩
  subst hn
  rw [← gaussSum_eq_range, ← casselsGauss_eq_gaussSum]
  exact casselsGauss_mul_nat hDn hcop _ ψ _ (fun k => even_hfac h hE hc ψ he ho k)

/-- Helper: $2^e$ is coprime to an odd $n$. Arguments: `e` the exponent, `n` the odd number (`h`). -/
theorem coprime_pow_two_of_odd (e n : ℕ) (h : n % 2 = 1) : Nat.Coprime (2 ^ e) n :=
  Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr h))

/-- Helper: $(2/n)^2 = 1$ for odd $n$. Arguments: `n` the odd lower entry (`h`). -/
theorem jac_two_sq (n : ℕ) (h : n % 2 = 1) : jacobiSym 2 n * jacobiSym 2 n = 1 := by
  have hc : Nat.Coprime 2 n := Nat.coprime_two_left.mpr (Nat.odd_iff.mpr h)
  have hg : (2 : ℤ).gcd n = 1 := by simpa using Int.gcd_natCast_natCast 2 n ▸ hc
  rcases jacobiSym.eq_one_or_neg_one hg with h1 | h1 <;> rw [h1] <;> norm_num

/-- Helper: $(4/n) = 1$ for odd $n$. Arguments: `n` the odd lower entry (`h`). -/
theorem jac_four (n : ℕ) (h : n % 2 = 1) : jacobiSym 4 n = 1 := by
  rw [show (4 : ℤ) = 2 * 2 by norm_num, jacobiSym.mul_left]
  exact jac_two_sq n h

/-- Helper: $(8/n) = (2/n)$ for odd $n$. Arguments: `n` the odd lower entry (`h`). -/
theorem jac_eight (n : ℕ) (h : n % 2 = 1) : jacobiSym 8 n = jacobiSym 2 n := by
  rw [show (8 : ℤ) = 2 * (2 * 2) by norm_num, jacobiSym.mul_left, jacobiSym.mul_left, jac_two_sq n h, mul_one]

/-- Helper: $(-2/n) = (-1/n)(2/n)$. Argument: `n` the lower entry. -/
theorem jac_neg_two (n : ℕ) : jacobiSym (-2) n = jacobiSym (-1) n * jacobiSym 2 n := by
  rw [show (-2 : ℤ) = -1 * 2 by norm_num, jacobiSym.mul_left]

/-- Helper: $(-1/n) = 1$ if $n \equiv 1 \pmod 4$ and $-1$ otherwise, for odd $n$. Arguments: `n`, `h` oddness. -/
theorem jac_neg_one_val (n : ℕ) (h : n % 2 = 1) :
    jacobiSym (-1) n = if n % 4 = 1 then 1 else -1 := by
  rw [jacobiSym.at_neg_one (Nat.odd_iff.mpr h), ZMod.χ₄_nat_eq_if_mod_four]
  rcases Nat.odd_mod_four_iff.mp h with h1 | h1 <;> simp [h1, show ¬ (n % 2 = 0) by omega]

/-- Helper: $\sqrt{4n} = 2\sqrt n$ in $\mathbb C$. Argument: `n` a natural number. -/
theorem sqrt_four_mul (n : ℕ) : ((Real.sqrt ((4 * n : ℕ) : ℝ) : ℝ) : ℂ) = 2 * ((Real.sqrt n : ℝ) : ℂ) := by
  push_cast
  rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  push_cast; ring

/-- Helper: $\sqrt{8n} = 2\sqrt2\sqrt n$ in $\mathbb C$. Argument: `n` a natural number. -/
theorem sqrt_eight_mul (n : ℕ) :
    ((Real.sqrt ((8 * n : ℕ) : ℝ) : ℝ) : ℂ) = 2 * sqrt2C * ((Real.sqrt n : ℝ) : ℂ) := by
  push_cast
  rw [Real.sqrt_mul (by norm_num), show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]
  push_cast; unfold sqrt2C; ring

/-- Helper: (2.20) at $m=1$ for $D = 4c$ with $c \equiv 3 \pmod 4$ squarefree, i.e. $D = -4E$, $E \equiv 1 \pmod 4$. Arguments: `D` the fundamental discriminant, `h` that $4 \mid D$, `hsqf` that $D/4$ is squarefree, `h3` that $D/4 \equiv 3 \pmod 4$. -/
theorem gauss_sum_even_a {D : ℤ} [IsQuadDisc D] (h : D % 4 = 0) (hsqf : Squarefree (D / 4))
    (h3 : D / 4 % 4 = 3) :
    ∑ r ∈ Finset.range D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
      Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) / (D.natAbs : ℂ)) = gaussConst D := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (-(D / 4)).natAbs = n := ⟨_, rfl⟩
  have hnodd : n % 2 = 1 := by omega
  have hsqn : Squarefree n := by
    rw [← hn, Int.natAbs_neg]; exact Int.squarefree_natAbs.mpr hsqf
  have : NeZero n := ⟨by omega⟩
  have hDn : D.natAbs = 4 * n := by omega
  have hcop : Nat.Coprime 4 n := by simpa using coprime_pow_two_of_odd 2 n hnodd
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  rw [even_core h (E := -(D / 4)) (c1 := -1) (by omega) (by ring) hn psi4 psi4_even psi4_odd hDn hcop,
    casselsGauss_psi4, psi4_odd n hnodd, jacChar_natCast, Nat.cast_ofNat, jac_four n hnodd,
    jac_neg_one_val n hnodd, gauss_jacChar_aux n (by omega) hnodd hsqn]
  by_cases hn1 : n % 4 = 1
  · rw [gaussConst_of_neg (by omega), hDn, sqrt_four_mul]
    simp only [hn1, ↓reduceIte]
    push_cast; ring
  · rw [gaussConst_of_pos (by omega), hDn, sqrt_four_mul]
    simp only [hn1, ↓reduceIte]
    push_cast
    linear_combination (-2 * ((Real.sqrt n : ℝ) : ℂ)) * hI

/-- Helper: (2.20) at $m=1$ for $D = 8E$ with $E \equiv 1 \pmod 4$ squarefree. Arguments: `D`, `h`, `hsqf` as in `gauss_sum_even_a`, `h2` that $D/4 \equiv 2 \pmod 4$, `h1` that $D/8 \equiv 1 \pmod 4$. -/
theorem gauss_sum_even_b1 {D : ℤ} [IsQuadDisc D] (h : D % 4 = 0) (hsqf : Squarefree (D / 4))
    (h2 : D / 4 % 4 = 2) (h1 : D / 4 / 2 % 4 = 1) :
    ∑ r ∈ Finset.range D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
      Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) / (D.natAbs : ℂ)) = gaussConst D := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (D / 4 / 2).natAbs = n := ⟨_, rfl⟩
  have hnodd : n % 2 = 1 := by omega
  have hsqn : Squarefree n := by
    rw [← hn]
    refine Int.squarefree_natAbs.mpr (Squarefree.of_mul_right (n := (D / 4 / 2)) (m := 2) ?_)
    rwa [show 2 * (D / 4 / 2) = D / 4 by omega]
  have : NeZero n := ⟨by omega⟩
  have hDn : D.natAbs = 8 * n := by omega
  have hcop : Nat.Coprime 8 n := by simpa using coprime_pow_two_of_odd 3 n hnodd
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hu : (jacobiSym 2 n : ℂ) * (jacobiSym 2 n : ℂ) = 1 := by exact_mod_cast jac_two_sq n hnodd
  rw [even_core h (E := D / 4 / 2) (c1 := 2) (by omega) (by omega) hn psi8 psi8_even psi8_odd hDn hcop,
    casselsGauss_psi8, psi8_odd n hnodd, jacChar_natCast, Nat.cast_ofNat, jac_eight n hnodd,
    hu, one_mul, gauss_jacChar_aux n (by omega) hnodd hsqn]
  by_cases hn1 : n % 4 = 1
  · rw [gaussConst_of_pos (by omega), hDn, sqrt_eight_mul]
    simp only [hn1, ↓reduceIte]
  · rw [gaussConst_of_neg (by omega), hDn, sqrt_eight_mul]
    simp only [hn1, ↓reduceIte]
    ring

/-- Helper: (2.20) at $m=1$ for $D = -8E$ with $E \equiv 1 \pmod 4$ squarefree. Arguments: `D`, `h`, `hsqf` as in `gauss_sum_even_a`, `h2` that $D/4 \equiv 2 \pmod 4$, `h1` that $D/8 \equiv 3 \pmod 4$. -/
theorem gauss_sum_even_b2 {D : ℤ} [IsQuadDisc D] (h : D % 4 = 0) (hsqf : Squarefree (D / 4))
    (h2 : D / 4 % 4 = 2) (h1 : D / 4 / 2 % 4 = 3) :
    ∑ r ∈ Finset.range D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
      Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) / (D.natAbs : ℂ)) = gaussConst D := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (-(D / 4 / 2)).natAbs = n := ⟨_, rfl⟩
  have hnodd : n % 2 = 1 := by omega
  have hsqn : Squarefree n := by
    rw [← hn, Int.natAbs_neg]
    refine Int.squarefree_natAbs.mpr (Squarefree.of_mul_right (n := (D / 4 / 2)) (m := 2) ?_)
    rwa [show 2 * (D / 4 / 2) = D / 4 by omega]
  have : NeZero n := ⟨by omega⟩
  have hDn : D.natAbs = 8 * n := by omega
  have hcop : Nat.Coprime 8 n := by simpa using coprime_pow_two_of_odd 3 n hnodd
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hu : (jacobiSym 2 n : ℂ) * (jacobiSym 2 n : ℂ) = 1 := by exact_mod_cast jac_two_sq n hnodd
  rw [even_core h (E := -(D / 4 / 2)) (c1 := -2) (by omega) (by omega) hn psi8' psi8'_even psi8'_odd hDn hcop,
    casselsGauss_psi8', psi8'_odd n hnodd, jacChar_natCast, Nat.cast_ofNat, jac_eight n hnodd,
    jac_neg_two, jac_neg_one_val n hnodd, gauss_jacChar_aux n (by omega) hnodd hsqn]
  by_cases hn1 : n % 4 = 1
  · rw [gaussConst_of_neg (by omega), hDn, sqrt_eight_mul]
    simp only [hn1, ↓reduceIte]
    push_cast
    linear_combination (2 * sqrt2C * Complex.I * ((Real.sqrt n : ℝ) : ℂ)) * hu
  · rw [gaussConst_of_pos (by omega), hDn, sqrt_eight_mul]
    simp only [hn1, ↓reduceIte]
    push_cast
    linear_combination (-2 * sqrt2C * ((Real.sqrt n : ℝ) : ℂ) * Complex.I ^ 2) * hu
      - (2 * sqrt2C * ((Real.sqrt n : ℝ) : ℂ)) * hI

/-- Helper: the Gauss sum (2.20) at $m = 1$ for every fundamental discriminant. -/
theorem gauss_sum_sign (D : ℤ) [hD : IsQuadDisc D] :
    ∑ r ∈ Finset.range D.natAbs, kroneckerChar D (r : ZMod D.natAbs) *
      Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) / (D.natAbs : ℂ)) = gaussConst D := by
  rcases Int.isFundamentalDiscr_iff_squarefree.mp hD.fund with ⟨h1, _⟩ | ⟨h0, hsqf, hc4⟩
  · exact gauss_sum_odd h1
  · rcases hc4 with h2 | h3
    · rcases (by omega : D / 4 / 2 % 4 = 1 ∨ D / 4 / 2 % 4 = 3) with h | h
      · exact gauss_sum_even_b1 h0 hsqf h2 h
      · exact gauss_sum_even_b2 h0 hsqf h2 h
    · exact gauss_sum_even_a h0 hsqf h3

/-- **Cassels' Gauss sum (2.20) of a fundamental discriminant, proved** (p. 374; the book "assumes it as known"). For
every fundamental discriminant $D \ne 1$ (`IsQuadDisc D`), the named statement `KroneckerGaussSum D` holds:
$\sum_{0 \le r < |D|}\chi_D(r)\,e^{2\pi i r m/|D|} = \chi_D(m)\cdot\sqrt D$ ($D > 0$) or $\chi_D(m)\cdot i\sqrt{|D|}$
($D < 0$), for all integers $m$. Argument: `D` the fundamental discriminant. Unconditional.

Proof: the dependence on $m$ and the reduction to the sign are `kroneckerGaussSum_of_sign`; the sign $+$ at $m = 1$ is
`gauss_sum_sign`. For $D \equiv 1 \pmod 4$, $\chi_D$ is the Jacobi character modulo $|D|$ (squarefree, odd), and its Gauss
sum is computed by induction on the number of prime factors: Example 2 (`casselsGauss_mul`) gives
$\tau(\chi, lm) = (m/l)(l/m)\,\tau(\chi_l)\tau(\chi_m)$, quadratic reciprocity gives $(m/l)(l/m) = -1$ exactly when
$l \equiv m \equiv 3 \pmod 4$ (matching $i\cdot i = -1$), and the prime case is Schur's sign (`gauss_sum_tau`, Example 5).
For even $D = d_1E$ with $d_1 \in \{-4, 8, -8\}$ and $E \equiv 1 \pmod 4$, the same product formula is applied with
$\psi$ the character modulo $|d_1|$ (Mathlib's `ZMod.χ₄`, `χ₈`, `χ₈'`, whose Gauss sums $2i$, $2\sqrt2$, $2\sqrt2\,i$ are
computed directly) and the Jacobi character modulo $|E|$, using $(E/k) = (k/|E|)$ for odd $k$. -/
@[kb "cassels1978" "App. B, §2, (2.20), p. 374 (the Gauss sum of a fundamental discriminant, proved)"]
theorem kroneckerGaussSum_holds (D : ℤ) [IsQuadDisc D] : KroneckerGaussSum D :=
  kroneckerGaussSum_of_sign (gauss_sum_sign D)

/-- **Cassels, Appendix B, §2, Lemma 2.3, $D > 0$ (p. 374), unconditional.** For a fundamental discriminant $D > 0$
(`IsQuadDisc D`), with $(D/m)$ the Kronecker symbol `kronZ D m`,
$$\sum_{m \ge 1}\frac{(D/m)}{m} = -\frac{1}{\sqrt D}\sum_{0 < r < D}(D/r)\,\log\sin\frac{\pi r}{D},$$
as the limit of the partial sums over $1 \le m \le K$, $K \to \infty$. Arguments: `D` the fundamental discriminant,
`hD : 0 < D`. This is `lemma_2_3_pos` with its assumed Gauss sum (2.20) replaced by `kroneckerGaussSum_holds`. -/
@[kb "cassels1978" "App. B, §2, Lemma 2.3 (D > 0), p. 374 (unconditional)"]
theorem lemma_2_3_pos_unconditional (D : ℤ) [IsQuadDisc D] (hD : 0 < D) :
    Filter.Tendsto (fun K : ℕ => ∑ m ∈ Finset.Icc 1 K, (kronZ D (m : ZMod D.natAbs) : ℝ) / (m : ℝ))
      Filter.atTop
      (nhds (-(Real.sqrt (D : ℝ))⁻¹ * ∑ r ∈ Finset.Ioo 0 D.natAbs,
        (kronZ D (r : ZMod D.natAbs) : ℝ) * Real.log (Real.sin (Real.pi * r / D)))) :=
  lemma_2_3_pos (kroneckerGaussSum_holds D) hD

/-- **Cassels, Appendix B, §2, Lemma 2.3, $D < 0$ (p. 374), unconditional.** For a fundamental discriminant $D < 0$,
$$\sum_{m \ge 1}\frac{(D/m)}{m} = -\frac{\pi}{|D|^{3/2}}\sum_{0 < r < |D|}(D/r)\,r$$
(with the minus sign, see the erratum in `lemma_2_3_neg`). Arguments: `D` the fundamental discriminant, `hD : D < 0`.
This is `lemma_2_3_neg` with `kroneckerGaussSum_holds`. -/
@[kb "cassels1978" "App. B, §2, Lemma 2.3 (D < 0), p. 374 (unconditional)"]
theorem lemma_2_3_neg_unconditional (D : ℤ) [IsQuadDisc D] (hD : D < 0) :
    Filter.Tendsto (fun K : ℕ => ∑ m ∈ Finset.Icc 1 K, (kronZ D (m : ZMod D.natAbs) : ℝ) / (m : ℝ))
      Filter.atTop
      (nhds (-Real.pi / |(D : ℝ)| ^ (3 / 2 : ℝ) * ∑ r ∈ Finset.Ioo 0 D.natAbs,
        (kronZ D (r : ZMod D.natAbs) : ℝ) * r)) :=
  lemma_2_3_neg (kroneckerGaussSum_holds D) hD

/-- **Cassels, Appendix B, Theorem 2.1 (i), finite-sum form (p. 371), unconditional.** For a fundamental
discriminant $D < 0$, $2|D|\,h(D) = -w\sum_{0<r<|D|}(D/r)\,r$, with $h(D)$ the class number of the quadratic field
`QField D`, $w$ = `properAutomorphCount D`. Arguments: `D` the fundamental discriminant, `hD : D < 0`. This is
`finite_sum_class_number_neg` with `kroneckerGaussSum_holds`. -/
@[kb "cassels1978" "App. B, Thm. 2.1 (i), p. 371 (finite-sum form, unconditional)"]
theorem finite_sum_class_number_neg_unconditional (D : ℤ) [IsQuadDisc D] (hD : D < 0) :
    2 * (D.natAbs : ℝ) * (NumberField.classNumber (QField D) : ℝ) =
      -(properAutomorphCount D : ℝ) * ∑ r ∈ Finset.Ioo 0 D.natAbs,
        (kronZ D (r : ZMod D.natAbs) : ℝ) * (r : ℝ) :=
  finite_sum_class_number_neg (kroneckerGaussSum_holds D) hD

/-- **Cassels, Appendix B, Example 1 (p. 389), unconditional.** For a fundamental discriminant $D < 0$,
$2\,(2 - (D/2))\,h(D) = w\sum_{r=1}^{[|D|/2]}(D/r)$, in the notation of `class_number_half_sum`. Arguments:
`D` the fundamental discriminant, `hD : D < 0`. This is `class_number_half_sum` with `kroneckerGaussSum_holds`. -/
@[kb "cassels1978" "App. B, Ex. 1, p. 389 (unconditional)"]
theorem class_number_half_sum_unconditional (D : ℤ) [IsQuadDisc D] (hD : D < 0) :
    2 * (2 - kronZ D (2 : ZMod D.natAbs)) * (NumberField.classNumber (QField D) : ℤ) =
      (properAutomorphCount D : ℤ) *
        ∑ r ∈ Finset.Icc 1 (D.natAbs / 2), kronZ D (r : ZMod D.natAbs) :=
  class_number_half_sum (kroneckerGaussSum_holds D) hD

end QuadFormsKB.Cassels
