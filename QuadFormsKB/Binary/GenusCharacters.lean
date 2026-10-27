import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Defs.Binary
import QuadFormsKB.Binary.KroneckerChar
import QuadFormsKB.Equiv.Binary

/-!
# Gauss's genus characters for binary quadratic forms

Let $D$ be a fundamental discriminant ($D \ne 1$, `IsQuadDisc D`) and $f = [a, b, c] = ax^2 + bxy + cy^2$ a
**primitive** integral binary form ($\gcd(a, b, c) = 1$, `Primitive`) of discriminant $D = b^2 - 4ac$.

**The assigned characters.** For each prime $p \mid D$ there is a character $\psi_p = $ `genusChar D p` on integers
prime to $p$:

* $p$ odd: $\psi_p(m) = \left(\frac{m}{p}\right)$ (Legendre symbol);
* $p = 2$ (so $D = 4d$, $d \equiv 2, 3 \pmod 4$): $\psi_2 = \delta = \chi_{-4}$ if $d \equiv 3 \pmod 4$
  ($D \equiv 12, 28 \pmod{32}$), $\psi_2 = \varepsilon = \chi_8$ if $d \equiv 2 \pmod 8$ ($D \equiv 8 \pmod{32}$), and
  $\psi_2 = \delta\varepsilon = \chi_{-8}$ if $d \equiv 6 \pmod 8$ ($D \equiv 24 \pmod{32}$). Here
  $\delta(m) = (-1)^{(m-1)/2}$ and $\varepsilon(m) = (-1)^{(m^2-1)/8}$ for odd $m$ (Mathlib's `ZMod.χ₄`, `ZMod.χ₈`,
  `ZMod.χ₈'`).

**Well-definedness (`genusChar_eval_eq_formChar`).** The genus character of $f$ at $p \mid D$ is
$\chi_p(f) = \psi_p(a)$ if $p \nmid a$ and $\psi_p(c)$ otherwise (`formChar`; $p$ cannot divide both, since $f$ is
primitive). Then $\psi_p(m) = \chi_p(f)$ for **every** value $m = f(x, y)$ prime to $p$. The proof is local at
$p$: from $4af(x, y) = (2ax + by)^2 - Dy^2$ and $p \mid D$, the product $a\,m$ is a square times a unit that
$\psi_p$ kills (mod $p$ for odd $p$; mod $8$ for $p = 2$, where $am = (ax + \tfrac b2 y)^2 - \tfrac D4 y^2$).

**The product relation (`prod_formChar_eq_one`).** For positive definite $f$,
$$\prod_{p \mid D} \chi_p(f) = 1 .$$
For $m > 0$ prime to $D$, $\prod_{p \mid D}\psi_p(m) = \chi_D(m)$, the Kronecker character
(`prod_genusChar_eq_kronZ`, by quadratic reciprocity for the Jacobi symbol); and $\chi_D(m) = 1$ whenever $f$
represents $m$ primitively and $\gcd(m, D) = 1$ (`kronZ_eq_one_of_primRep`: every prime $q \mid m$ splits, because
$D \equiv b'^2 \pmod{4m}$ for an equivalent form $[m, b', c']$).

Sources: Gauss, *Disquisitiones Arithmeticae*, §§229–233 (the characters of a form); Cox, *Primes of the Form
$x^2 + ny^2$*, §3.B (Lemma 3.17, Theorem 3.15) and §6.A; Buell, *Binary Quadratic Forms*, Ch. 4; Cassels, *Rational
Quadratic Forms*, Ch. 14, §3, pp. 339–340, and §5, p. 344 (Cassels describes the $\mathbb{Z}_p$-classes by the units they
represent and names the characters $\chi_p$ only in §5; his Ch. 14 forms are non-classical, $D = b^2 - 4ac = -4d(f)$, (1.5),
p. 331, with proper classes).
-/

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Binary

open BinQF

/-! ### Primitive forms -/

/-- **A primitive binary form:** $\gcd(a, b, c) = 1$ for $f = ax^2 + bxy + cy^2$
(equivalently, no prime divides all three coefficients: `primitive_iff`). -/
@[kb "buell1989" "Ch. 1"]
def Primitive (f : BinQF) : Prop := Int.gcd f.a (Int.gcd f.b f.c) = 1

/-- **Primitive iff no prime divides all of $a, b, c$.** -/
theorem primitive_iff (f : BinQF) :
    Primitive f ↔ ∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ∣ f.a ∧ (p : ℤ) ∣ f.b ∧ (p : ℤ) ∣ f.c) := by
  constructor
  · rintro hf p hp ⟨ha, hb, hc⟩
    have h1 : (p : ℤ) ∣ (Int.gcd f.a (Int.gcd f.b f.c) : ℤ) :=
      Int.dvd_coe_gcd ha (Int.dvd_coe_gcd hb hc)
    rw [hf, Nat.cast_one] at h1
    exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1)
  · intro h
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    refine h p hp ⟨?_, ?_, ?_⟩
    · exact Int.dvd_trans (Int.natCast_dvd_natCast.mpr hpd) (Int.gcd_dvd_left _ _)
    · exact Int.dvd_trans (Int.natCast_dvd_natCast.mpr hpd)
        (Int.dvd_trans (Int.gcd_dvd_right _ _) (Int.gcd_dvd_left _ _))
    · exact Int.dvd_trans (Int.natCast_dvd_natCast.mpr hpd)
        (Int.dvd_trans (Int.gcd_dvd_right _ _) (Int.gcd_dvd_right _ _))

/-! ### Completing the square -/

/-- **Completing the square:** $4a\,f(x, y) = (2ax + by)^2 - D y^2$ with $D = b^2 - 4ac$. -/
theorem four_a_mul_eval (f : BinQF) (x y : ℤ) :
    4 * f.a * f.eval x y = (2 * f.a * x + f.b * y) ^ 2 - f.disc * y ^ 2 := by
  rw [eval_eq, disc]; ring

/-- **Completing the square in $y$:** $4c\,f(x, y) = (2cy + bx)^2 - D x^2$. -/
theorem four_c_mul_eval (f : BinQF) (x y : ℤ) :
    4 * f.c * f.eval x y = (2 * f.c * y + f.b * x) ^ 2 - f.disc * x ^ 2 := by
  rw [eval_eq, disc]; ring

/-- **Completing the square, $b = 2b'$ even:** $a\,f(x, y) = (ax + b'y)^2 - (b'^2 - ac)\,y^2$, and
$D/4 = b'^2 - ac$. -/
theorem a_mul_eval_of_even (f : BinQF) {b' : ℤ} (hb : f.b = 2 * b') (x y : ℤ) :
    f.a * f.eval x y = (f.a * x + b' * y) ^ 2 - (b' ^ 2 - f.a * f.c) * y ^ 2 := by
  rw [eval_eq, hb]; ring

/-- **Completing the square in $y$, $b = 2b'$ even:** $c\,f(x, y) = (cy + b'x)^2 - (b'^2 - ac)\,x^2$. -/
theorem c_mul_eval_of_even (f : BinQF) {b' : ℤ} (hb : f.b = 2 * b') (x y : ℤ) :
    f.c * f.eval x y = (f.c * y + b' * x) ^ 2 - (b' ^ 2 - f.a * f.c) * x ^ 2 := by
  rw [eval_eq, hb]; ring

/-! ### Facts about fundamental discriminants -/

variable {D : ℤ}

/-- For a fundamental discriminant, either $D \equiv 1 \pmod 4$, or $D = 4d$ with $d \equiv 2, 3 \pmod 4$,
i.e. $D \equiv 8, 12, 24, 28 \pmod{32}$. -/
theorem fund_cases [hD : IsQuadDisc D] :
    D % 4 = 1 ∨ D % 32 = 8 ∨ D % 32 = 24 ∨ D % 32 = 12 ∨ D % 32 = 28 := by
  rcases Int.isFundamentalDiscr_iff_squarefree.mp hD.fund with ⟨h, -⟩ | ⟨h0, -, h23⟩
  · exact Or.inl h
  · right; omega

/-- $2 \mid D$ iff $4 \mid D$ for a discriminant ($D \equiv 0, 1 \pmod 4$). -/
theorem two_dvd_iff_of_fund [hD : IsQuadDisc D] : (2 : ℤ) ∣ D ↔ D % 32 = 8 ∨ D % 32 = 24 ∨ D % 32 = 12 ∨
    D % 32 = 28 := by
  have := fund_cases (D := D); omega

/-- An odd prime divides a fundamental discriminant at most once (squarefree odd part). -/
theorem odd_prime_sq_not_dvd [hD : IsQuadDisc D] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ (p : ℤ) ^ 2 ∣ D :=
  hD.fund.2.2 p hp (hp.odd_of_ne_two hp2)

/-! ### The characters $\psi_p$ -/

/-- **The assigned character $\psi_p$ of discriminant $D$ at the prime $p$**, evaluated at $m \in \mathbb{Z}$:
* $p \neq 2$: $\psi_p(m) = \left(\frac{m}{p}\right)$, the Legendre (= Jacobi) symbol;
* $p = 2$: $\psi_2(m) = \varepsilon(m) = \chi_8(m)$ if $D \equiv 8 \pmod{32}$; $\psi_2(m) = \delta\varepsilon(m) =
  \chi_{-8}(m)$ if $D \equiv 24 \pmod{32}$; otherwise $\psi_2(m) = \delta(m) = \chi_{-4}(m)$ (used when
  $D \equiv 12, 28 \pmod{32}$).

Here $\delta(m) = (-1)^{(m-1)/2}$ and $\varepsilon(m) = (-1)^{(m^2-1)/8}$ for odd $m$, and all three vanish at even
$m$ (`ZMod.χ₄`, `ZMod.χ₈`, `ZMod.χ₈'`). $\psi_p$ is used only for primes $p \mid D$; it is multiplicative
(`genusChar_mul`), depends only on $m \bmod p$ ($\bmod 8$ for $p = 2$; `genusChar_congr`), and is $\pm 1$ on integers
prime to $p$ (`genusChar_sq`). Source: Gauss, *Disq. Arith.* §§229–231 (the characters $R_p$, $1,4$; $3,4$; $1,8$;
$3,8$; $5,8$; $7,8$); Cox, §3.B (Theorem 3.15, the assigned characters); Buell, §4.1. -/
@[kb "cox2013" "§3.B, Thm. 3.15 [unverified]"]
def genusChar (D : ℤ) (p : ℕ) (m : ℤ) : ℤ :=
  if p = 2 then
    (if D % 32 = 8 then ZMod.χ₈ (m : ZMod 8)
      else if D % 32 = 24 then ZMod.χ₈' (m : ZMod 8) else ZMod.χ₄ (m : ZMod 4))
  else jacobiSym m p

/-- **$\psi_p$ is multiplicative:** $\psi_p(mn) = \psi_p(m)\psi_p(n)$. -/
theorem genusChar_mul (D : ℤ) (p : ℕ) (m n : ℤ) :
    genusChar D p (m * n) = genusChar D p m * genusChar D p n := by
  unfold genusChar
  split_ifs <;> simp [Int.cast_mul, map_mul, jacobiSym.mul_left]

/-- **The modulus of $\psi_p$:** $8$ for $p = 2$, $p$ otherwise. -/
def charMod (p : ℕ) : ℕ := if p = 2 then 8 else p

/-- **$\psi_p$ depends only on $m \bmod p$** ($m \bmod 8$ for $p = 2$). -/
theorem genusChar_congr (D : ℤ) (p : ℕ) {m m' : ℤ} (h : (charMod p : ℤ) ∣ m - m') :
    genusChar D p m = genusChar D p m' := by
  unfold genusChar charMod at *
  by_cases hp : p = 2
  · subst hp
    simp only [ite_true] at h ⊢
    have h' : (8 : ℤ) ∣ m' - m := by
      have : (8 : ℤ) ∣ m - m' := by exact_mod_cast h
      rw [← dvd_neg, neg_sub]; exact this
    have h8 : (m : ZMod 8) = (m' : ZMod 8) :=
      ((ZMod.intCast_eq_intCast_iff_dvd_sub m m' 8).mpr (by exact_mod_cast h'))
    have h4 : (m : ZMod 4) = (m' : ZMod 4) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub m m' 4).mpr
        (by push_cast; exact (show (4 : ℤ) ∣ 8 by norm_num).trans h')
    rw [h8, h4]
  · simp only [hp, ite_false] at h ⊢
    exact jacobiSym.mod_left' (Int.modEq_iff_dvd.mpr h).symm

/-- $\gcd(m, p) = 1$ for a prime $p \nmid m$. -/
theorem int_gcd_eq_one_of_not_dvd {p : ℕ} (hp : p.Prime) {m : ℤ} (hm : ¬ (p : ℤ) ∣ m) :
    m.gcd p = 1 := by
  show Nat.gcd m.natAbs (p : ℤ).natAbs = 1
  rw [Int.natAbs_natCast]
  exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr
    (fun h => hm (Int.natCast_dvd.mpr h)))

/-- **$\psi_p(m) = \pm 1$ for $p \nmid m$:** $\psi_p(m)^2 = 1$. -/
theorem genusChar_sq (D : ℤ) {p : ℕ} (hp : p.Prime) {m : ℤ} (hm : ¬ (p : ℤ) ∣ m) :
    genusChar D p m ^ 2 = 1 := by
  unfold genusChar
  by_cases hp2 : p = 2
  · subst hp2
    have hodd : m % 2 = 1 := by omega
    simp only [ite_true]
    split_ifs
    · rw [ZMod.χ₈_int_eq_if_mod_eight]; split_ifs <;> omega
    · rw [ZMod.χ₈'_int_eq_if_mod_eight]; split_ifs <;> omega
    · rw [ZMod.χ₄_int_eq_if_mod_four]; split_ifs <;> omega
  · simp only [hp2, ite_false]
    exact jacobiSym.sq_one (int_gcd_eq_one_of_not_dvd hp hm)

/-- **From $\psi_p(rm) = 1$ to $\psi_p(m) = \psi_p(r)$** for $p \nmid r$. -/
theorem genusChar_eq_of_mul_eq_one (D : ℤ) {p : ℕ} (hp : p.Prime) {r m : ℤ} (hr : ¬ (p : ℤ) ∣ r)
    (h : genusChar D p (r * m) = 1) : genusChar D p m = genusChar D p r := by
  rw [genusChar_mul] at h
  have h2 := genusChar_sq D hp hr
  calc genusChar D p m = genusChar D p r ^ 2 * genusChar D p m := by rw [h2, one_mul]
    _ = genusChar D p r * (genusChar D p r * genusChar D p m) := by ring
    _ = genusChar D p r := by rw [h, mul_one]

/-! ### The local key lemmas -/

/-- **Odd $p \mid D$:** $\psi_p(X^2 - DY^2) = 1$ whenever $p \nmid X^2 - DY^2$ (the value is $\equiv X^2$, a nonzero
square, mod $p$). -/
theorem genusChar_sq_sub_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpD : (p : ℤ) ∣ D) (X Y : ℤ)
    (h : ¬ (p : ℤ) ∣ X ^ 2 - D * Y ^ 2) : genusChar D p (X ^ 2 - D * Y ^ 2) = 1 := by
  have hc : genusChar D p (X ^ 2 - D * Y ^ 2) = genusChar D p (X ^ 2) := by
    apply genusChar_congr
    simp only [charMod, hp2, ite_false, sub_sub_cancel_left]
    exact (dvd_neg).mpr (dvd_mul_of_dvd_left hpD _)
  have hX : ¬ (p : ℤ) ∣ X := by
    intro hX
    apply h
    exact dvd_sub (dvd_pow hX two_ne_zero) (dvd_mul_of_dvd_left hpD _)
  rw [hc]
  unfold genusChar
  simp only [hp2, ite_false]
  exact jacobiSym.sq_one' (int_gcd_eq_one_of_not_dvd hp hX)

theorem zmod8_cast_eq_of_emod {n : ℤ} {r : ℕ} (h : n % 8 = r) : (n : ZMod 8) = r := by
  rw [show (r : ZMod 8) = ((r : ℤ) : ZMod 8) by simp, ZMod.intCast_eq_intCast_iff']; push_cast; omega

theorem zmod4_cast_eq_of_emod {n : ℤ} {r : ℕ} (h : n % 4 = r) : (n : ZMod 4) = r := by
  rw [show (r : ZMod 4) = ((r : ℤ) : ZMod 4) by simp, ZMod.intCast_eq_intCast_iff']; push_cast; omega

/-- **$p = 2 \mid D$:** $\psi_2(X^2 - \tfrac D4 Y^2) = 1$ whenever $X^2 - \tfrac D4 Y^2$ is odd (a finite check
mod $8$). -/
theorem genusChar_sq_sub_two [IsQuadDisc D] (h2D : (2 : ℤ) ∣ D) (X Y : ℤ)
    (h : ¬ (2 : ℤ) ∣ X ^ 2 - D / 4 * Y ^ 2) : genusChar D 2 (X ^ 2 - D / 4 * Y ^ 2) = 1 := by
  have hc := (two_dvd_iff_of_fund (D := D)).mp h2D
  unfold genusChar
  simp only [ite_true]
  have hne : ∀ z : ℤ, ¬ (2 : ℤ) ∣ z → ZMod.χ₈ (z : ZMod 8) ≠ 0 ∧ ZMod.χ₈' (z : ZMod 8) ≠ 0 ∧
      ZMod.χ₄ (z : ZMod 4) ≠ 0 := by
    intro z hz
    refine ⟨?_, ?_, ?_⟩
    · rw [ZMod.χ₈_int_eq_if_mod_eight]; split_ifs <;> omega
    · rw [ZMod.χ₈'_int_eq_if_mod_eight]; split_ifs <;> omega
    · rw [ZMod.χ₄_int_eq_if_mod_four]; split_ifs <;> omega
  obtain ⟨n1, n2, n3⟩ := hne _ h
  generalize hdd : D / 4 = d at n1 n2 n3 ⊢
  split_ifs with h8 h24
  · have hd : (d : ZMod 8) = 2 := zmod8_cast_eq_of_emod (r := 2) (by omega)
    have e : ((X ^ 2 - d * Y ^ 2 : ℤ) : ZMod 8) = (X : ZMod 8) ^ 2 - 2 * (Y : ZMod 8) ^ 2 := by
      push_cast; rw [hd]
    have key : ∀ x y : ZMod 8, ZMod.χ₈ (x ^ 2 - 2 * y ^ 2) = 1 ∨ ZMod.χ₈ (x ^ 2 - 2 * y ^ 2) = 0 := by
      decide
    rw [e] at n1 ⊢
    exact (key _ _).resolve_right n1
  · have hd : (d : ZMod 8) = 6 := zmod8_cast_eq_of_emod (r := 6) (by omega)
    have e : ((X ^ 2 - d * Y ^ 2 : ℤ) : ZMod 8) = (X : ZMod 8) ^ 2 - 6 * (Y : ZMod 8) ^ 2 := by
      push_cast; rw [hd]
    have key : ∀ x y : ZMod 8, ZMod.χ₈' (x ^ 2 - 6 * y ^ 2) = 1 ∨ ZMod.χ₈' (x ^ 2 - 6 * y ^ 2) = 0 := by
      decide
    rw [e] at n2 ⊢
    exact (key _ _).resolve_right n2
  · have hd : (d : ZMod 4) = 3 := zmod4_cast_eq_of_emod (r := 3) (by omega)
    have e : ((X ^ 2 - d * Y ^ 2 : ℤ) : ZMod 4) = (X : ZMod 4) ^ 2 - 3 * (Y : ZMod 4) ^ 2 := by
      push_cast; rw [hd]
    have key : ∀ x y : ZMod 4, ZMod.χ₄ (x ^ 2 - 3 * y ^ 2) = 1 ∨ ZMod.χ₄ (x ^ 2 - 3 * y ^ 2) = 0 := by
      decide
    rw [e] at n3 ⊢
    exact (key _ _).resolve_right n3

/-! ### The genus characters of a form, and their well-definedness -/

/-- $\gcd$-free divisibility: a prime dividing a product divides a factor. -/
theorem int_prime_dvd_mul {p : ℕ} (hp : p.Prime) {x y : ℤ} (h : (p : ℤ) ∣ x * y) :
    (p : ℤ) ∣ x ∨ (p : ℤ) ∣ y :=
  (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h

/-- A prime dividing $x^2$ divides $x$. -/
theorem int_prime_dvd_of_dvd_sq {p : ℕ} (hp : p.Prime) {x : ℤ} (h : (p : ℤ) ∣ x ^ 2) : (p : ℤ) ∣ x :=
  (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow h

/-- **The coefficient read by the genus character at $p$:** $a$ if $p \nmid a$, else $c$. For a primitive form
and $p \mid D$ it is prime to $p$ (`not_dvd_charCoeff`). -/
def charCoeff (f : BinQF) (p : ℕ) : ℤ := if (p : ℤ) ∣ f.a then f.c else f.a

/-- For a primitive form and a prime $p \mid D$, $p$ does not divide both $a$ and $c$ (else $p \mid b^2 = D + 4ac$,
so $p \mid \gcd(a, b, c)$). -/
theorem not_dvd_charCoeff {f : BinQF} (hf : Primitive f) {p : ℕ} (hp : p.Prime) (hpD : (p : ℤ) ∣ f.disc) :
    ¬ (p : ℤ) ∣ charCoeff f p := by
  unfold charCoeff
  split_ifs with ha
  · intro hc
    have hb2 : (p : ℤ) ∣ f.b ^ 2 := by
      have : f.b ^ 2 = f.disc + 4 * f.a * f.c := by rw [disc]; ring
      rw [this]
      exact dvd_add hpD (dvd_mul_of_dvd_right hc _)
    exact (primitive_iff f).mp hf p hp ⟨ha, int_prime_dvd_of_dvd_sq hp hb2, hc⟩
  · exact ha

/-- **The genus character of a form** $f$ at a prime $p$:
$$\chi_p(f) = \psi_p(a) \text{ if } p \nmid a, \qquad \chi_p(f) = \psi_p(c) \text{ if } p \mid a,$$
with $\psi_p = $ `genusChar (disc f) p`. For primitive $f$ and $p \mid D$ this is $\psi_p(m)$ for **every** value
$m = f(x, y)$ prime to $p$ (`genusChar_eval_eq_formChar`), so it is Gauss's character of the form. Source: Gauss,
*Disq. Arith.* §229; Cox, §3.B (Lemma 3.17 and the definition of the assigned characters). -/
@[kb "cox2013" "§3.B, Lemma 3.17 [unverified]"]
def formChar (f : BinQF) (p : ℕ) : ℤ := genusChar f.disc p (charCoeff f p)

/-- **The genus characters are well defined** (Gauss, *Disq. Arith.* §229; Cox, Lemma 3.17): let $f$ be primitive
of fundamental discriminant $D$ and $p \mid D$ prime. For **every** value $m = f(x, y)$ with $p \nmid m$,
$$\psi_p(m) = \chi_p(f),$$
so $\psi_p$ takes a single value on the integers prime to $p$ represented by $f$.

The proof is local at $p$. With $r = $ `charCoeff f p` ($a$ or $c$, prime to $p$): for odd $p$,
$4rm = X^2 - DY^2 \equiv X^2 \pmod p$ is a nonzero square mod $p$; for $p = 2$, $b = 2b'$ and
$rm = X^2 - \tfrac D4 Y^2$ is odd, and $\psi_2$ is $1$ on such values (a check mod $8$). Either way
$\psi_p(rm) = 1$, so $\psi_p(m) = \psi_p(r)$. -/
@[kb "gauss1801" "§229 [unverified]"]
theorem genusChar_eval_eq_formChar [IsQuadDisc D] {f : BinQF} (hf : Primitive f) (hD : f.disc = D)
    {p : ℕ} (hp : p.Prime) (hpD : (p : ℤ) ∣ D) (x y : ℤ) (hm : ¬ (p : ℤ) ∣ f.eval x y) :
    genusChar D p (f.eval x y) = formChar f p := by
  have hr := not_dvd_charCoeff hf hp (hD ▸ hpD)
  unfold formChar
  rw [hD]
  apply genusChar_eq_of_mul_eq_one D hp hr
  have hrm : ¬ (p : ℤ) ∣ charCoeff f p * f.eval x y := fun h =>
    (int_prime_dvd_mul hp h).elim hr hm
  by_cases hp2 : p = 2
  · subst hp2
    have h2D : (2 : ℤ) ∣ D := by exact_mod_cast hpD
    have hb : (2 : ℤ) ∣ f.b := by
      have : f.b ^ 2 = D + 4 * f.a * f.c := by rw [← hD, disc]; ring
      have h2 : (2 : ℤ) ∣ f.b ^ 2 := by
        rw [this]; exact dvd_add h2D (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by norm_num) _) _)
      exact int_prime_dvd_of_dvd_sq (p := 2) Nat.prime_two (by exact_mod_cast h2)
    obtain ⟨b', hb'⟩ := hb
    have hd4 : D / 4 = b' ^ 2 - f.a * f.c := by
      rw [← hD, disc, hb']
      rw [show (2 * b') ^ 2 - 4 * f.a * f.c = 4 * (b' ^ 2 - f.a * f.c) by ring]
      exact Int.mul_ediv_cancel_left _ (by norm_num)
    push_cast at hrm
    unfold charCoeff at hrm ⊢
    split_ifs at hrm ⊢
    · rw [c_mul_eval_of_even f hb', ← hd4] at hrm ⊢
      exact genusChar_sq_sub_two h2D _ _ hrm
    · rw [a_mul_eval_of_even f hb', ← hd4] at hrm ⊢
      exact genusChar_sq_sub_two h2D _ _ hrm
  · have h4 : genusChar D p 4 = 1 := by
      unfold genusChar
      simp only [hp2, ite_false]
      exact jacobiSym.at_four (hp.odd_of_ne_two hp2)
    have hp4 : ¬ (p : ℤ) ∣ 4 := by
      intro h
      have h' : p ∣ 4 := by exact_mod_cast h
      have : p ∣ 2 ^ 2 := by norm_num; exact h'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this))
    have key : genusChar D p (4 * (charCoeff f p * f.eval x y)) = 1 := by
      have h4rm : ¬ (p : ℤ) ∣ 4 * (charCoeff f p * f.eval x y) := fun h =>
        (int_prime_dvd_mul hp h).elim hp4 hrm
      unfold charCoeff at h4rm ⊢
      split_ifs at h4rm ⊢
      · rw [← mul_assoc, four_c_mul_eval, hD] at h4rm ⊢
        exact genusChar_sq_sub_odd hp hp2 hpD _ _ h4rm
      · rw [← mul_assoc, four_a_mul_eval, hD] at h4rm ⊢
        exact genusChar_sq_sub_odd hp hp2 hpD _ _ h4rm
    rwa [genusChar_mul, h4, one_mul] at key

/-! ### The product of the characters: the Kronecker character -/

/-- **The Jacobi symbol is multiplicative in the lower entry over a finite set of nonzero naturals:**
$\left(\frac{a}{\prod_{p \in s} p}\right) = \prod_{p \in s}\left(\frac{a}{p}\right)$. -/
theorem jacobiSym_prod_right (a : ℤ) (s : Finset ℕ) (hs : ∀ p ∈ s, p ≠ 0) :
    jacobiSym a (∏ p ∈ s, p) = ∏ p ∈ s, jacobiSym a p := by
  induction s using Finset.induction_on with
  | empty => simp [jacobiSym.one_right]
  | insert q s hq ih =>
    rw [Finset.prod_insert hq, Finset.prod_insert hq,
      jacobiSym.mul_right' a (hs q (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr fun p hp => hs p (Finset.mem_insert_of_mem hp)),
      ih fun p hp => hs p (Finset.mem_insert_of_mem hp)]

/-- **Quadratic reciprocity for odd naturals**, as a sign:
$\left(\frac{k}{m}\right) = \epsilon\left(\frac{m}{k}\right)$ with $\epsilon = -1$ iff $k \equiv m \equiv 3 \pmod 4$. -/
theorem jacobiSym_nat_recip {k m : ℕ} (hk : Odd k) (hm : Odd m) :
    jacobiSym k m = (if k % 4 = 3 ∧ m % 4 = 3 then -1 else 1) * jacobiSym m k := by
  have hk4 : k % 4 = 1 ∨ k % 4 = 3 := by rcases hk with ⟨t, rfl⟩; omega
  have hm4 : m % 4 = 1 ∨ m % 4 = 3 := by rcases hm with ⟨t, rfl⟩; omega
  rcases hk4 with h1 | h1
  · rw [ite_eq_right (by omega), one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h1 hm]
  · rcases hm4 with h2 | h2
    · rw [ite_eq_right (by omega), one_mul, jacobiSym.quadratic_reciprocity_one_mod_four' hk h2]
    · rw [ite_eq_left ⟨h1, h2⟩, jacobiSym.quadratic_reciprocity_three_mod_four h1 h2]; ring

/-- The odd primes dividing $D$ have $\psi_p(m) = \left(\frac{m}{p}\right)$. -/
theorem genusChar_of_ne_two (D : ℤ) {p : ℕ} (hp2 : p ≠ 2) (m : ℤ) : genusChar D p m = jacobiSym m p := by
  simp [genusChar, hp2]

/-- **The product of the assigned characters is the Kronecker character** (Cox, Theorem 3.15 and Exercise 3.12;
Buell §4.1): for a fundamental discriminant $D$ and $m \ge 1$ prime to $D$,
$$\prod_{p \mid D}\psi_p(m) = \chi_D(m),$$
$\chi_D = $ `kronZ D` the Kronecker character (`kroneckerChar`). For $D \equiv 1 \pmod 4$ this is
$\left(\frac{m}{|D|}\right) = \prod_{p \mid D}\left(\frac{m}{p}\right)$ ($|D|$ squarefree); for $D = 4d$ it is
$\left(\frac{d}{m}\right) = \psi_2(m)\left(\frac{m}{k}\right)$ with $k$ the odd part of $|d|$, by quadratic reciprocity
and its supplements. -/
@[kb "cox2013" "§3.B, Thm. 3.15 [unverified]"]
theorem prod_genusChar_eq_kronZ [hD : IsQuadDisc D] (m : ℕ) (hm : Nat.Coprime m D.natAbs) :
    ∏ p ∈ D.natAbs.primeFactors, genusChar D p m = kronZ D (m : ZMod D.natAbs) := by
  rcases Int.isFundamentalDiscr_iff_squarefree.mp hD.fund with ⟨h1, hsq⟩ | ⟨h0, hsq, h23⟩
  · -- `D ≡ 1 (mod 4)`: all prime factors are odd
    rw [kronZ_natCast_of_one h1]
    have hsq' : Squarefree D.natAbs := Int.squarefree_natAbs.mpr hsq
    conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hsq']
    rw [jacobiSym_prod_right _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero)]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp2 : p ≠ 2 := by
      rintro rfl
      have := Nat.dvd_of_mem_primeFactors hp
      have : (2 : ℤ) ∣ D := Int.natAbs_dvd_natAbs.mp (by simpa using this)
      omega
    exact genusChar_of_ne_two D hp2 _
  · -- `D = 4d`, `d ≡ 2, 3 (mod 4)` squarefree
    set d := D / 4 with hd
    have hD4 : D = 4 * d := by omega
    have hmodd : Odd m := by
      rw [Nat.odd_iff]
      by_contra h
      have h2m : 2 ∣ m := by omega
      have h2D : 2 ∣ D.natAbs := ⟨2 * d.natAbs, by rw [hD4, Int.natAbs_mul]; norm_num; ring⟩
      exact absurd (Nat.dvd_gcd h2m h2D) (by rw [hm]; norm_num)
    rw [kronZ_natCast_of_zero h0 hmodd]
    -- the odd part `k` of `|d|`, with `d = ±k` or `d = ±2k`
    obtain ⟨k, e, hk, he, hdk, hDk⟩ : ∃ k e : ℕ, Odd k ∧ (e = 0 ∨ e = 1) ∧
        (d = 2 ^ e * k ∨ d = -(2 ^ e * k)) ∧ D.natAbs = 2 ^ (e + 2) * k := by
      rcases h23 with h2 | h3
      · refine ⟨(d / 2).natAbs, 1, ?_, Or.inr rfl, ?_, ?_⟩
        · rw [Nat.odd_iff]; omega
        · omega
        · omega
      · refine ⟨d.natAbs, 0, ?_, Or.inl rfl, ?_, ?_⟩
        · rw [Nat.odd_iff]; omega
        · omega
        · omega
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk
    have hsqk : Squarefree k := by
      have : Squarefree d.natAbs := Int.squarefree_natAbs.mpr hsq
      exact this.squarefree_of_dvd ⟨2 ^ e, by rcases hdk with h | h <;> rw [h] <;> simp [Int.natAbs_mul,
        Int.natAbs_pow] <;> ring⟩
    have hpf : D.natAbs.primeFactors = insert 2 k.primeFactors := by
      rw [hDk, Nat.primeFactors_mul (by positivity) hk0, Nat.primeFactors_pow _ (by omega),
        Nat.prime_two.primeFactors]
      rfl
    have h2k : 2 ∉ k.primeFactors := by
      intro h
      have := Nat.dvd_of_mem_primeFactors h
      rw [Nat.odd_iff] at hk; omega
    rw [hpf, Finset.prod_insert h2k]
    have hodd_part : ∏ p ∈ k.primeFactors, genusChar D p m = jacobiSym m k := by
      conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hsqk]
      rw [jacobiSym_prod_right _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero)]
      refine Finset.prod_congr rfl fun p hp => genusChar_of_ne_two D ?_ _
      rintro rfl; exact h2k hp
    rw [hodd_part]
    -- now `ψ₂(m) J(m | k) = J(d | m)`
    have hrec := jacobiSym_nat_recip hk hmodd
    have hm8 : ((m : ℤ) : ZMod 8) = (m : ZMod 8) := Int.cast_natCast m
    have hm4 : ((m : ℤ) : ZMod 4) = (m : ZMod 4) := Int.cast_natCast m
    simp only [genusChar, ite_true, hm8, hm4]
    rw [ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₈'_nat_eq_if_mod_eight, ZMod.χ₄_nat_eq_if_mod_four]
    have hm2 : m % 2 = 1 := Nat.odd_iff.mp hmodd
    have hm8' : m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by omega
    have hk4 : k % 4 = 1 ∨ k % 4 = 3 := by rw [Nat.odd_iff] at hk; omega
    rcases he with rfl | rfl
    · -- `d = ±k` odd, `ψ₂ = χ₄`
      have hD32 : D % 32 ≠ 8 ∧ D % 32 ≠ 24 := by omega
      rw [ite_eq_right hD32.1, ite_eq_right hD32.2]
      rcases hdk with hdk | hdk <;> simp only [pow_zero, one_mul] at hdk <;> rw [← hd, hdk]
      · rw [hrec]
        split_ifs <;> omega
      · rw [show (-(k : ℤ)) = -1 * (k : ℤ) by ring, jacobiSym.mul_left, jacobiSym.at_neg_one hmodd, ZMod.χ₄_nat_eq_if_mod_four,
          hrec]
        split_ifs <;> omega
    · -- `d = ±2k`, `ψ₂ = χ₈` or `χ₈'`
      rcases hdk with hdk | hdk <;> simp only [pow_one] at hdk <;> rw [← hd, hdk]
      · rw [jacobiSym.mul_left,
          jacobiSym.at_two hmodd, ZMod.χ₈_nat_eq_if_mod_eight, hrec]
        split_ifs <;> omega
      · rw [show (-(2 * (k : ℤ))) = -2 * (k : ℤ) by ring, jacobiSym.mul_left,
          jacobiSym.at_neg_two hmodd, ZMod.χ₈'_nat_eq_if_mod_eight, hrec]
        split_ifs <;> omega

/-! ### Primitive representations -/

/-- **A primitive representation can be moved to the first coefficient:** if $\gcd(x, y) = 1$, there are $r, s$
with $xs - ry = 1$, and the $\mathrm{SL}_2(\mathbb{Z})$-substitution $\begin{pmatrix} x & r \\ y & s\end{pmatrix}$ takes
$f$ to a form with first coefficient $f(x, y)$. -/
theorem exists_subst_a_eq (f : BinQF) {x y : ℤ} (hxy : IsCoprime x y) :
    ∃ r s : ℤ, x * s - r * y = 1 ∧ (subst x r y s f).a = f.eval x y := by
  obtain ⟨u, v, huv⟩ := hxy
  refine ⟨-v, u, by linear_combination huv, ?_⟩
  simp only [subst, a_mk, eval_eq]

/-- **Primitive forms represent integers prime to any $N \ne 0$, primitively** (Cox, Lemma 2.25 [unverified]; Buell, Ch. 1):
there are coprime $x, y > 0$ with $p \nmid f(x, y)$ for every prime $p \mid N$. Explicitly, $x$ is the product of the
primes $p \mid N$ with $p \mid a$, $p \nmid c$, and $y$ the product of the primes $p \mid N$ with $p \nmid a$; then
$f(x, y) \equiv ax^2$, $cy^2$ or $bxy \not\equiv 0 \pmod p$ (no Chinese remainder theorem needed). -/
@[kb "cox2013" "§2.A, Lemma 2.25 [unverified]; cassels1978 Ch. 14, Lemma 2.1, p. 334"]
theorem exists_coprime_value {f : BinQF} (hf : Primitive f) {N : ℕ} (hN : N ≠ 0) :
    ∃ x y : ℤ, 0 < x ∧ 0 < y ∧ IsCoprime x y ∧
      ∀ p : ℕ, p.Prime → p ∣ N → ¬ (p : ℤ) ∣ f.eval x y := by
  classical
  set S₁ := N.primeFactors.filter (fun p : ℕ => (p : ℤ) ∣ f.a ∧ ¬ (p : ℤ) ∣ f.c)
  set S₂ := N.primeFactors.filter (fun p : ℕ => ¬ (p : ℤ) ∣ f.a)
  set x : ℕ := ∏ p ∈ S₁, p
  set y : ℕ := ∏ p ∈ S₂, p
  have hx0 : 0 < x := Finset.prod_pos fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
  have hy0 : 0 < y := Finset.prod_pos fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
  -- a prime divides a product of distinct primes iff it is one of them
  have hdvd : ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime) → ∀ q : ℕ, q.Prime →
      ((q : ℤ) ∣ ((∏ p ∈ S, p : ℕ) : ℤ) ↔ q ∈ S) := by
    intro S hS q hq
    rw [Int.natCast_dvd_natCast, (Nat.prime_iff.mp hq).dvd_finsetProd_iff]
    constructor
    · rintro ⟨p, hp, hqp⟩
      rwa [(Nat.prime_dvd_prime_iff_eq hq (hS p hp)).mp hqp]
    · intro h; exact ⟨q, h, dvd_refl _⟩
  have hS₁ : ∀ p ∈ S₁, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hS₂ : ∀ p ∈ S₂, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  refine ⟨x, y, by exact_mod_cast hx0, by exact_mod_cast hy0, ?_, ?_⟩
  · rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun q hq => ?_
    refine (Nat.coprime_primes (hS₁ p hp) (hS₂ q hq)).mpr ?_
    rintro rfl
    exact (Finset.mem_filter.mp hq).2 (Finset.mem_filter.mp hp).2.1
  · intro q hq hqN hdiv
    have hqN' : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqN, hN⟩
    have hev := eval_eq f x y
    by_cases ha : (q : ℤ) ∣ f.a
    · have hqy : ¬ (q : ℤ) ∣ (y : ℤ) := by
        rw [hdvd S₂ hS₂ q hq]; intro h; exact (Finset.mem_filter.mp h).2 ha
      by_cases hc : (q : ℤ) ∣ f.c
      · -- `q | a, c`: then `q ∤ b, x, y` and `f(x,y) ≡ bxy`
        have hqx : ¬ (q : ℤ) ∣ (x : ℤ) := by
          rw [hdvd S₁ hS₁ q hq]; intro h; exact (Finset.mem_filter.mp h).2.2 hc
        have hb : ¬ (q : ℤ) ∣ f.b := fun hb => (primitive_iff f).mp hf q hq ⟨ha, hb, hc⟩
        have : (q : ℤ) ∣ f.b * x * y := by
          have e : f.b * x * y = f.eval x y - f.a * x ^ 2 - f.c * y ^ 2 := by rw [hev]; ring
          rw [e]
          exact dvd_sub (dvd_sub hdiv (dvd_mul_of_dvd_left ha _)) (dvd_mul_of_dvd_left hc _)
        rcases int_prime_dvd_mul hq this with h | h
        · exact (int_prime_dvd_mul hq h).elim hb hqx
        · exact hqy h
      · -- `q | a`, `q ∤ c`: then `q | x`, `q ∤ y`, `f(x,y) ≡ cy²`
        have hqx : (q : ℤ) ∣ (x : ℤ) := by
          rw [hdvd S₁ hS₁ q hq]; exact Finset.mem_filter.mpr ⟨hqN', ha, hc⟩
        have : (q : ℤ) ∣ f.c * y ^ 2 := by
          have e : f.c * y ^ 2 = f.eval x y - (f.a * x ^ 2 + f.b * x * y) := by rw [hev]; ring
          rw [e]
          exact dvd_sub hdiv (dvd_add (dvd_mul_of_dvd_right (dvd_pow hqx two_ne_zero) _)
            (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hqx _) _))
        rcases int_prime_dvd_mul hq this with h | h
        · exact hc h
        · exact hqy (int_prime_dvd_of_dvd_sq hq h)
    · -- `q ∤ a`: then `q | y`, `q ∤ x`, `f(x,y) ≡ ax²`
      have hqy : (q : ℤ) ∣ (y : ℤ) := by
        rw [hdvd S₂ hS₂ q hq]; exact Finset.mem_filter.mpr ⟨hqN', ha⟩
      have hqx : ¬ (q : ℤ) ∣ (x : ℤ) := by
        rw [hdvd S₁ hS₁ q hq]; intro h; exact ha (Finset.mem_filter.mp h).2.1
      have : (q : ℤ) ∣ f.a * x ^ 2 := by
        have e : f.a * x ^ 2 = f.eval x y - (f.b * x * y + f.c * y ^ 2) := by rw [hev]; ring
        rw [e]
        exact dvd_sub hdiv (dvd_add (dvd_mul_of_dvd_right hqy _)
          (dvd_mul_of_dvd_right (dvd_pow hqy two_ne_zero) _))
      rcases int_prime_dvd_mul hq this with h | h
      · exact ha h
      · exact hqx (int_prime_dvd_of_dvd_sq hq h)

/-- **Primitively represented integers prime to $D$ have $\chi_D(m) = 1$** (Cox, Lemma 2.5 and Corollary 2.6):
if $f(x, y) = m \ge 1$ with $\gcd(x, y) = 1$ and $\gcd(m, D) = 1$, then $\chi_D(m) = 1$. Moving the representation
to the first coefficient gives $D = b'^2 - 4mc'$, so every prime $q \mid m$ splits: $\left(\frac Dq\right) = 1$ for
odd $q$, and $D \equiv 1 \pmod 8$ if $q = 2$ (`kronZ_odd_prime`, `kronZ_two`). -/
@[kb "cox2013" "§2.A, Lemma 2.5 [unverified]"]
theorem kronZ_eq_one_of_primRep [IsQuadDisc D] {f : BinQF} (hD : f.disc = D) {x y : ℤ} (hxy : IsCoprime x y)
    {m : ℕ} (hm : f.eval x y = m) (hm0 : 0 < m) (hcop : Nat.Coprime m D.natAbs) :
    kronZ D (m : ZMod D.natAbs) = 1 := by
  obtain ⟨r, s, hdet, ha⟩ := exists_subst_a_eq f hxy
  set g := subst x r y s f
  have hgD : g.disc = D := by rw [disc_subst_of_det _ _ _ _ _ (by rw [hdet]; norm_num), hD]
  have hDg : D = g.b ^ 2 - 4 * m * g.c := by rw [← hgD, disc, ha, hm]
  have key : ∀ n : ℕ, n ∣ m → kronZ D (n : ZMod D.natAbs) = 1 := by
    intro n
    induction n using Nat.recOnMul with
    | zero => intro h; exact absurd (Nat.eq_zero_of_zero_dvd h) hm0.ne'
    | one => intro _; simpa using kronZ_one (D := D)
    | prime q hq =>
      intro hqm
      have hqD : ¬ (q : ℤ) ∣ D := by
        intro h
        have : q ∣ D.natAbs := Int.natCast_dvd.mp h
        exact hq.one_lt.ne' (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hqm this))
      have hq4m : (q : ℤ) ∣ 4 * m * g.c :=
        dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (by exact_mod_cast hqm) _) _
      by_cases hq2 : q = 2
      · subst hq2
        have hDodd : D % 2 = 1 := by omega
        have hb : g.b % 2 = 1 := by
          rcases Int.emod_two_eq_zero_or_one g.b with h | h
          · exfalso
            have : (2 : ℤ) ∣ g.b ^ 2 := dvd_pow (Int.dvd_of_emod_eq_zero h) two_ne_zero
            omega
          · exact h
        have h8 : (8 : ℤ) ∣ 4 * m * g.c := by
          obtain ⟨t, ht⟩ := hqm
          exact ⟨t * g.c, by rw [ht]; push_cast; ring⟩
        have hb8 : g.b ^ 2 % 8 = 1 := by
          have : g.b % 8 = 1 ∨ g.b % 8 = 3 ∨ g.b % 8 = 5 ∨ g.b % 8 = 7 := by omega
          rcases this with h | h | h | h <;>
            simp [pow_two, Int.mul_emod, h]
        have hD8 : D % 8 = 1 := by omega
        have := kronZ_two (D := D)
        rw [ite_eq_left (by omega), ite_eq_left hD8] at this
        exact_mod_cast this
      · have : Fact q.Prime := ⟨hq⟩
        have hcong : D % (q : ℤ) = g.b ^ 2 % q :=
          Int.modEq_iff_dvd.mpr (by rw [hDg, sub_sub_cancel]; exact hq4m)
        rw [kronZ_odd_prime q hq2, legendreSym.mod, hcong, ← legendreSym.mod]
        apply legendreSym.sq_one'
        intro h0
        apply hqD
        rw [hDg]
        exact dvd_sub (dvd_pow ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0) two_ne_zero) hq4m
    | mul a b iha ihb =>
      intro hab
      rw [Nat.cast_mul, kronZ_mul, iha (dvd_trans (dvd_mul_right a b) hab),
        ihb (dvd_trans (dvd_mul_left b a) hab), mul_one]
  exact key m (dvd_refl m)

/-- **The product relation for the genus characters** (Gauss, *Disq. Arith.* §§261–262, the half of the
characters' combinations that cannot occur; Cox, Theorem 3.15 and Exercise 3.12): for a primitive positive definite
form $f$ of fundamental discriminant $D$,
$$\prod_{p \mid D} \chi_p(f) = 1 .$$
Choose $m = f(x, y) > 0$ with $\gcd(x, y) = 1$ and $\gcd(m, D) = 1$ (`exists_coprime_value`); then
$\prod_p \chi_p(f) = \prod_p \psi_p(m) = \chi_D(m) = 1$ (`prod_genusChar_eq_kronZ`, `kronZ_eq_one_of_primRep`). -/
@[kb "gauss1801" "§261 [unverified]"]
theorem prod_formChar_eq_one [IsQuadDisc D] {f : BinQF} (hf : Primitive f) (hD : f.disc = D)
    (hpos : f.PosDef') : ∏ p ∈ D.natAbs.primeFactors, formChar f p = 1 := by
  have hN : D.natAbs ≠ 0 := by have := three_le_natAbs (D := D); omega
  obtain ⟨x, y, hx, hy, hxy, hcop⟩ := exists_coprime_value hf hN
  have hpd : f.PosDef := (posDef_iff_posDef' f).mpr hpos
  have hm0 : 0 < f.eval x y := hpd x y (by intro h; simp at h; omega)
  set m := (f.eval x y).toNat with hmdef
  have hm : f.eval x y = m := by omega
  have hmcop : Nat.Coprime m D.natAbs := by
    refine Nat.coprime_of_dvd fun q hq hqm hqD => hcop q hq hqD ?_
    rw [hm]; exact_mod_cast hqm
  rw [← kronZ_eq_one_of_primRep hD hxy hm (by omega) hmcop, ← prod_genusChar_eq_kronZ m hmcop]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpD : (p : ℤ) ∣ D := Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hp)
  rw [← hm, genusChar_eval_eq_formChar hf hD hpp hpD x y (hcop p hpp (Nat.dvd_of_mem_primeFactors hp))]

end QuadFormsKB.Binary
