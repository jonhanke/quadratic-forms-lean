/-
# Ramanujan's exact exceptional sets for $x^2 + y^2 + z^2 + n u^2$ and $2(x^2 + y^2 + z^2) + n u^2$

**Library** `QuadFormsKB.Historical.Ramanujan` (historical library, not imported by `QuadFormsKB`).  Targets, Ramanujan, *On the expression of a number in the form
$ax^2 + by^2 + cz^2 + du^2$* (1917), §§ 5-8, *Collected Papers* (1927) No. 20:

* : when the exceptional set of $x^2 + y^2 + z^2 + n u^2$ is finite, it is given exactly by five
  rules according to the class of $n$ (`RamanujanExceptionalSets`, **stated**).
* : for odd $n$, the numbers not represented by $2(x^2 + y^2 + z^2) + n u^2$ are exactly those of
  four families (`RamanujanExceptionalSetsTwo`, **stated**).

Both statements are as recorded in the historical sources (the second with the reading of (iv) that the computation and § 8's
proof give, the printed condition on $\kappa$ being garbled in the text recognition). Both readings were checked by computer: no mismatch for $n \le 70$ (all $N \le 40n$).
They are not proved here: the proofs go through Ramanujan's case analysis with the ternary laws of § 3, several of
which are only stated (`Ternary113`, `Ternary115`, ...).
-/
import QuadFormsKB.Historical.Ramanujan.Papers

namespace QuadFormsKB.Historical.Ramanujan

/-- $N = 4^{\kappa}(8\nu + 7)$ for some $\nu \ge 0$. -/
def Is4Pow87 (κ N : ℕ) : Prop := ∃ ν : ℕ, N = 4 ^ κ * (8 * ν + 7)

/-- The exceptional set of $x^2 + y^2 + z^2 + n u^2$ predicted by Ramanujan, for the classes of $n$
where it is finite: the numbers $4^{\lambda}(8\mu + 7)$ below $n$, together with
* nothing more if $n \equiv 2 \pmod 4$ or $n \in \{1, 9, 17, 25, 4, 36, 68, 100\}$;
* the numbers $4(8\mu + 7)$ between $n$ and $4n$ if $n \equiv 5 \pmod 8$;
* the numbers $4^2(8\mu + 7)$ between $n$ and $4n$ if $n \equiv 20 \pmod{32}$;
* the numbers $n + 4^{\kappa}(8\nu + 7)$ between $n$ and $4n$ if $n \equiv 3 \pmod 4$, with $\kappa = 1$ for
  $n \equiv 3 \pmod 8$ and $\kappa \ge 2$ for $n \equiv 7 \pmod 8$;
* the numbers $n + 4^{\kappa}(8\nu + 7)$ between $n$ and $4n$ if $n \equiv 12 \pmod{16}$, with $\kappa = 2$ for
  $n = 4(8k + 3)$ and $\kappa > 2$ for $n = 4(8k + 7)$.
"Below" and "between" are strict. -/
def ramanujanExc (n N : ℕ) : Prop :=
  (IsExc 4 8 7 N ∧ N < n) ∨
    (n % 8 = 5 ∧ Is4Pow87 1 N ∧ n < N ∧ N < 4 * n) ∨
    (n % 32 = 20 ∧ Is4Pow87 2 N ∧ n < N ∧ N < 4 * n) ∨
    (n % 8 = 3 ∧ n < N ∧ N < 4 * n ∧ Is4Pow87 1 (N - n)) ∨
    (n % 8 = 7 ∧ n < N ∧ N < 4 * n ∧ ∃ κ ≥ 2, Is4Pow87 κ (N - n)) ∨
    (n % 32 = 12 ∧ n < N ∧ N < 4 * n ∧ Is4Pow87 2 (N - n)) ∨
    (n % 32 = 28 ∧ n < N ∧ N < 4 * n ∧ ∃ κ > 2, Is4Pow87 κ (N - n))

/-- The classes of $n$ for which Ramanujan determines a finite exceptional set. -/
def RamanujanFiniteClass (n : ℕ) : Prop :=
  n % 4 = 2 ∨ n ∈ ({1, 9, 17, 25, 4, 36, 68, 100} : Finset ℕ) ∨ n % 8 = 5 ∨ n % 32 = 20 ∨ n % 4 = 3 ∨
    n % 16 = 12

/-- **Stated** (Ramanujan 1917, §§ 5-7, *Collected Papers* No. 20): for every $n$ in
one of the classes of `RamanujanFiniteClass`, a positive integer $N$ is not represented by
$x^2 + y^2 + z^2 + n u^2$ iff it is in Ramanujan's exceptional set `ramanujanExc n N`. -/
@[kb "ramanujan1927" "No. 20, §§ 5-7, pp. 172-176 [unverified locator]"]
def RamanujanExceptionalSets : Prop :=
  ∀ n : ℕ, RamanujanFiniteClass n → ∀ N : ℕ, 0 < N → (¬ Rep4 1 1 1 n N ↔ ramanujanExc n N)

/-- The numbers not represented by $2(x^2 + y^2 + z^2) + n u^2$, $n$ odd, according to Ramanujan:
(i) odd $N < n$; (ii) $4^{\lambda}(16\mu + 14) < 4n$; (iii) $n + 4^{\lambda}(16\mu + 14)$ between $n$ and $9n$;
(iv) numbers between $9n$ and $25n$ of the form $c n + 4^{\kappa}(16\nu + 14)$ with $c = 1$ if $n \equiv 1 \pmod 4$,
$c = 9$ if $n \equiv 3 \pmod 4$, and $\kappa = 2$ for $n \equiv 3, 5 \pmod 8$, $\kappa \ge 3$ for
$n \equiv 1, 7 \pmod 8$. -/
def ramanujanExcTwo (n N : ℕ) : Prop :=
  (Odd N ∧ N < n) ∨ (IsExc 4 16 14 N ∧ N < 4 * n) ∨ (n < N ∧ N < 9 * n ∧ IsExc 4 16 14 (N - n)) ∨
    (9 * n < N ∧ N < 25 * n ∧
      ∃ κ ν : ℕ, N = (if n % 4 = 1 then 1 else 9) * n + 4 ^ κ * (16 * ν + 14) ∧
        (if n % 8 = 3 ∨ n % 8 = 5 then κ = 2 else 3 ≤ κ))

/-- **Stated** (Ramanujan 1917, § 8, *Collected Papers* No. 20): for odd $n$, a
positive integer $N$ is not represented by $2x^2 + 2y^2 + 2z^2 + n u^2$ iff it is in `ramanujanExcTwo n N`. -/
@[kb "ramanujan1927" "No. 20, § 8 [unverified locator]"]
def RamanujanExceptionalSetsTwo : Prop :=
  ∀ n : ℕ, Odd n → ∀ N : ℕ, 0 < N → (¬ Rep4 2 2 2 n N ↔ ramanujanExcTwo n N)

end QuadFormsKB.Historical.Ramanujan
