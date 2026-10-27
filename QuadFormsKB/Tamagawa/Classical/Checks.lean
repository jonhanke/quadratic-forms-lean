/-
# Classical special cases over $\mathbb Q$: numerical checks

**Layer:** $\mathbb Z$ (finite computations, kernel `decide`).

Independent numerical checks, for small $m$, of the classical formulas proved in `Ternary.lean` and `Binary.lean`
(they check the formulas, not the proofs):
* **Gauss** (`gauss_three_squares`): $w(D)\,r_3(m) = 24\,h(D)$ ($m\equiv1,2\pmod4$, $D = -4m$), $= 48\,h(D)$ ($m\equiv3\pmod8$,
  $D = -m$), $r_3(m) = 0$ ($m\equiv7\pmod8$), for squarefree $m\le 30$, with $h(D)$ the number of reduced primitive
  positive definite forms of discriminant $D$ (`hRed`, equal to the class number of $\mathbb Q(\sqrt D)$ for fundamental $D$)
  and $w(-4) = 4$, $w(-3) = 6$, $w(D) = 2$ otherwise (`checks_gauss`);
* **Dirichlet for $x_0^2+x_1^2$** (`dirichlet_sumTwoSq`, the genus being one class with unit group of order $4$):
  $r_2(m) = 4\sum_{d\mid m}\chi_{-4}(d)$ for $1\le m\le 40$ (`checks_two_squares`);
* **Dirichlet for $x_0^2-2x_1^2$** (`dirichlet_pell2`, one class): the number of solutions of $x_0^2-2x_1^2 = m$ modulo the
  norm-one units $\pm(3+2\sqrt2)^k$, counted in the fundamental domain $x_0>0$, $0\le x_1$, $3x_1<2x_0$, is
  $\sum_{d\mid m}\chi_8(d)$ for $1\le m\le 40$ (`checks_pell2`).
-/
import Mathlib

namespace QuadFormsKB.Tamagawa.Classical.Checks

/-- $r_3(m) = \#\{x\in\mathbb Z^3 : x_0^2+x_1^2+x_2^2 = m\}$, by enumeration of $[-\lfloor\sqrt m\rfloor, \lfloor\sqrt m\rfloor]^3$. -/
def r3 (m : ℕ) : ℕ :=
  ((Finset.Icc (-(Nat.sqrt m : ℤ)) (Nat.sqrt m) ×ˢ Finset.Icc (-(Nat.sqrt m : ℤ)) (Nat.sqrt m) ×ˢ
    Finset.Icc (-(Nat.sqrt m : ℤ)) (Nat.sqrt m)).filter
    fun x => x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = (m : ℤ)).card

/-- $r_2(m) = \#\{x\in\mathbb Z^2 : x_0^2+x_1^2 = m\}$. -/
def r2 (m : ℕ) : ℕ :=
  ((Finset.Icc (-(Nat.sqrt m : ℤ)) (Nat.sqrt m) ×ˢ Finset.Icc (-(Nat.sqrt m : ℤ)) (Nat.sqrt m)).filter fun x => x.1 ^ 2 + x.2 ^ 2 = (m : ℤ)).card

/-- The number of reduced primitive positive definite forms $ax^2+bxy+cy^2$ of discriminant $D<0$:
$|b|\le a\le c$, $b\ge0$ if $|b| = a$ or $a = c$, $\gcd(a,b,c) = 1$. -/
def hRed (D : ℤ) : ℕ :=
  ((Finset.Icc (1 : ℤ) (Nat.sqrt D.natAbs) ×ˢ
      Finset.Icc (-(Nat.sqrt D.natAbs : ℤ)) (Nat.sqrt D.natAbs)).filter fun ab =>
    let a := ab.1; let b := ab.2
    (b ^ 2 - D) % (4 * a) = 0 ∧
      (let c := (b ^ 2 - D) / (4 * a)
       |b| ≤ a ∧ a ≤ c ∧ (|b| = a ∨ a = c → 0 ≤ b) ∧ Int.gcd (Int.gcd a b) c = 1)).card

/-- The number of roots of unity of $\mathbb Q(\sqrt D)$, $D < 0$. -/
def wD (D : ℤ) : ℕ := if D = -4 then 4 else if D = -3 then 6 else 2

/-- $\sum_{d\mid m}\chi(d)$ for a function $\chi$ on $\mathbb N$. -/
def divSum (χ : ℕ → ℤ) (m : ℕ) : ℤ := ∑ d ∈ m.divisors, χ d

/-- $\chi_{-4}$ on $\mathbb N$. -/
def chi4 (d : ℕ) : ℤ := if d % 4 = 1 then 1 else if d % 4 = 3 then -1 else 0

/-- $\chi_8$ on $\mathbb N$. -/
def chi8 (d : ℕ) : ℤ := if d % 8 = 1 ∨ d % 8 = 7 then 1 else if d % 8 = 3 ∨ d % 8 = 5 then -1 else 0

/-- The solutions of $x_0^2 - 2x_1^2 = m$ in the fundamental domain $x_0 > 0$, $0\le x_1$, $3x_1 < 2x_0$ of the norm-one
units ($x_0 < 3\sqrt m$ there, since $x_0^2 - 2x_1^2 > x_0^2/9$). -/
def pellOrbits (m : ℕ) : ℕ :=
  ((Finset.Icc (1 : ℤ) (3 * Nat.sqrt m + 3) ×ˢ Finset.Icc (0 : ℤ) (3 * Nat.sqrt m + 3)).filter fun x =>
    3 * x.2 < 2 * x.1 ∧ x.1 ^ 2 - 2 * x.2 ^ 2 = (m : ℤ)).card

/-- The classical right side of Gauss's formula, times $w(D)$. -/
def gaussRHS (m : ℕ) : ℕ :=
  if m % 4 = 1 ∨ m % 4 = 2 then 24 * hRed (-4 * (m : ℤ))
  else if m % 8 = 3 then 48 * hRed (-(m : ℤ)) else 0

/-- The discriminant of $\mathbb Q(\sqrt{-m})$, $m$ squarefree. -/
def gD (m : ℕ) : ℤ := if m % 4 = 3 then -(m : ℤ) else -4 * (m : ℤ)

set_option maxRecDepth 100000 in
/-- **Gauss's formula, numerically**, squarefree $1\le m\le 30$. -/
theorem checks_gauss : ∀ m ∈ ((Finset.Icc 1 30).filter Squarefree), wD (gD m) * r3 m = gaussRHS m := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **Jacobi/Dirichlet for $x_0^2 + x_1^2$, numerically**, $1\le m\le 40$. -/
theorem checks_two_squares : ∀ m ∈ Finset.Icc 1 40, (r2 m : ℤ) = 4 * divSum chi4 m := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **Dirichlet for $x_0^2 - 2x_1^2$, numerically**, $1\le m\le 40$. -/
theorem checks_pell2 : ∀ m ∈ Finset.Icc 1 40, (pellOrbits m : ℤ) = divSum chi8 m := by
  decide +kernel

end QuadFormsKB.Tamagawa.Classical.Checks
