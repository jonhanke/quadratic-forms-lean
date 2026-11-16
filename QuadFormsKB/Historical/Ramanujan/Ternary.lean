/-
# Ramanujan's ternary exception laws (1917, § 3)

**Library** `QuadFormsKB.Historical.Ramanujan` (historical library, not imported by `QuadFormsKB`).  Target
:

* (Ramanujan, *On the expression of a number in the form $ax^2 + by^2 + cz^2 + du^2$*, Proc. Cambridge
  Philos. Soc. 19 (1917); *Collected Papers* (1927), No. 20, § 3, (3.1)–(3.71), p. 171; occurrence
  `ramanujan1927-papers:p20.s3.1`): a number $N \ge 0$ is **not** of the form
  * $x^2 + y^2 + z^2$ exactly when $N = 4^\lambda(8\mu + 7)$ (Legendre, Gauss): `ternary_111`, **wrapper** of
    `Grosswald.legendre_three_squares`;
  * $x^2 + y^2 + 2z^2$ exactly when $N = 4^\lambda(16\mu + 14)$ (Lebesgue): `ternary_112`, **proved**
    ($N = x^2 + y^2 + 2z^2$ iff $2N$ is a sum of three squares);
  * $x^2 + 2y^2 + 2z^2$ exactly when $N = 4^\lambda(8\mu + 7)$: `ternary_122`, **proved**
    ($x^2 + 2y^2 + 2z^2 = x^2 + (y + z)^2 + (y - z)^2$);
  * $x^2 + 2y^2 + 4z^2$ exactly when $N = 4^\lambda(16\mu + 14)$: `ternary_124`, **proved** (from the two above);
  * $x^2 + y^2 + 3z^2$ exactly when $N = 9^\lambda(9\mu + 6)$ (Dirichlet): `Ternary113`, **stated**;
  * $x^2 + 2y^2 + 3z^2$ exactly when $N = 4^\lambda(16\mu + 10)$: `Ternary123`, **stated**;
  * $x^2 + 2y^2 + 5z^2$ exactly when $N = 25^\lambda(25\mu + 10)$ or $25^\lambda(25\mu + 15)$: `Ternary125`, **stated**.

  The conjunction of the seven laws is `RamanujanTernaryExceptions`; it is **proved equivalent** to the conjunction of
  the three stated laws (`ramanujanTernaryExceptions_iff`). *Why the three are out of reach here:* the four proved laws
  reduce to Legendre's three-squares theorem (proved in this library through Hasse–Minkowski and the
  Davenport–Cassels lemma, `ThreeSquares.three_squares_of_not_form`); the forms $x^2 + y^2 + 3z^2$, $x^2 + 2y^2 + 3z^2$,
  $x^2 + 2y^2 + 5z^2$ do not satisfy the Davenport–Cassels hypothesis, and the classical proofs (Dirichlet; Dickson's
  *Studies* (1930), ch. V) need the one-class-in-the-genus property of each form with its local representation
  conditions, which is not formalized for ternary forms here. Each stated law was checked numerically for every
  $N \le 3000$ (the historical sources checked $N \le 60000$).

**Conventions.** $\lambda, \mu \ge 0$; $x, y, z \in \mathbb Z$; Ramanujan's coefficients $(a, b, c)$ are the arguments
of `Rep3 a b c`.
-/
import QuadFormsKB.Literature.Classical.SumsOfSquares

namespace QuadFormsKB.Historical.Ramanujan

/-- **$N$ is represented by $ax^2 + by^2 + cz^2$:** $ax^2 + by^2 + cz^2 = N$ for some $x, y, z \in \mathbb Z$. -/
def Rep3 (a b c N : ℕ) : Prop := ∃ x y z : ℤ, (a : ℤ) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = N

/-- **$N$ lies in the exception class $q^\lambda(r\mu + s)$:** $N = q^\lambda(r\mu + s)$ for some $\lambda, \mu \in \mathbb N$. -/
def IsExc (q r s N : ℕ) : Prop := ∃ l m : ℕ, N = q ^ l * (r * m + s)


/-- Sums of three integer squares are the same as sums of three natural squares: $a^2+b^2+c^2=N$ over $\mathbb Z$ iff over $\mathbb N$. -/
private theorem sq3_iff_nat (N : ℕ) :
    (∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = N) ↔ ∃ a b c : ℕ, a ^ 2 + b ^ 2 + c ^ 2 = N := by
  constructor
  · rintro ⟨a, b, c, h⟩
    refine ⟨a.natAbs, b.natAbs, c.natAbs, ?_⟩
    have h' : ((a.natAbs ^ 2 + b.natAbs ^ 2 + c.natAbs ^ 2 : ℕ) : ℤ) = N := by
      push_cast
      simpa [sq_abs] using h
    exact_mod_cast h'
  · rintro ⟨a, b, c, h⟩
    exact ⟨a, b, c, by exact_mod_cast h⟩

/-- $\mathrm{Rep3}(1,1,1,N)$ iff $N=a^2+b^2+c^2$ over $\mathbb Z$. -/
private theorem rep3_111_iff (N : ℕ) : Rep3 1 1 1 N ↔ ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = N := by
  unfold Rep3
  simp

/-- Squares have the parity of the base: $a^2 \equiv a \pmod 2$. -/
private theorem sq_mod_two (a : ℤ) : a ^ 2 % 2 = a % 2 := by
  rcases Int.emod_two_eq_zero_or_one a with h | h <;> simp [pow_two, Int.mul_emod, h]

/-- $2N$ is of the form $4^\lambda(8\mu+7)$ iff $N$ is of the form $4^\lambda(16\mu+14)$. -/
private theorem exc_double (N : ℕ) : IsExc 4 8 7 (2 * N) ↔ IsExc 4 16 14 N := by
  constructor
  · rintro ⟨l, m, h⟩
    cases l with
    | zero => simp at h; omega
    | succ l =>
      refine ⟨l, m, ?_⟩
      rw [pow_succ] at h
      linarith
  · rintro ⟨l, m, h⟩
    refine ⟨l + 1, m, ?_⟩
    rw [pow_succ, h]
    ring

/-- Parity pairing: if $c$ is even and $a+b$ even and $a^2+b^2+c^2=2N$ then $N=x^2+y^2+2z^2$. -/
private theorem rep112_aux (a b c : ℤ) (N : ℕ) (hc : c % 2 = 0) (hab : (a + b) % 2 = 0)
    (h : a ^ 2 + b ^ 2 + c ^ 2 = 2 * N) : Rep3 1 1 2 N := by
  obtain ⟨k, hk⟩ : ∃ k, a + b = 2 * k := ⟨(a + b) / 2, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, c = 2 * j := ⟨c / 2, by omega⟩
  have ha : a = 2 * k - b := by omega
  subst ha hj
  exact ⟨k, k - b, j, by push_cast; linarith⟩

/-- Parity pairing for $x^2+2y^2+2z^2$: $b+c$ even and $a^2+b^2+c^2=N$ gives $N=x^2+2y^2+2z^2$. -/
private theorem rep122_aux (a b c : ℤ) (N : ℕ) (hbc : (b + c) % 2 = 0)
    (h : a ^ 2 + b ^ 2 + c ^ 2 = N) : Rep3 1 2 2 N := by
  obtain ⟨k, hk⟩ : ∃ k, b + c = 2 * k := ⟨(b + c) / 2, by omega⟩
  have hc : c = 2 * k - b := by omega
  subst hc
  exact ⟨a, k, b - k, by push_cast; linarith⟩

/-- Parity pairing for $x^2+2y^2+4z^2$: $p+q$ even and $2(p^2+q^2+r^2)=N$ gives $N=x^2+2y^2+4z^2$. -/
private theorem rep124_aux (p q r : ℤ) (N : ℕ) (hpq : (p + q) % 2 = 0)
    (h : 2 * (p ^ 2 + q ^ 2 + r ^ 2) = N) : Rep3 1 2 4 N := by
  obtain ⟨s, hs⟩ : ∃ s, p + q = 2 * s := ⟨(p + q) / 2, by omega⟩
  have hq : q = 2 * s - p := by omega
  subst hq
  exact ⟨2 * s, r, p - s, by push_cast; linarith⟩

/-- $N=x^2+y^2+2z^2$ iff $2N$ is a sum of three integer squares. -/
private theorem rep112_iff (N : ℕ) : Rep3 1 1 2 N ↔ ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = ((2 * N : ℕ) : ℤ) := by
  constructor
  · rintro ⟨x, y, z, h⟩
    refine ⟨x + y, x - y, 2 * z, ?_⟩
    push_cast at h ⊢
    linarith
  · rintro ⟨a, b, c, h⟩
    push_cast at h
    have ha := sq_mod_two a
    have hb := sq_mod_two b
    have hc := sq_mod_two c
    have : (c % 2 = 0 ∧ (a + b) % 2 = 0) ∨ (a % 2 = 0 ∧ (b + c) % 2 = 0) ∨
        (b % 2 = 0 ∧ (a + c) % 2 = 0) := by omega
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact rep112_aux a b c N h1 h2 h
    · exact rep112_aux b c a N h1 h2 (by linarith)
    · exact rep112_aux a c b N h1 h2 (by linarith)

/-- $N=x^2+2y^2+2z^2$ iff $N$ is a sum of three integer squares. -/
private theorem rep122_iff (N : ℕ) : Rep3 1 2 2 N ↔ ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = N := by
  constructor
  · rintro ⟨x, y, z, h⟩
    refine ⟨x, y + z, y - z, ?_⟩
    push_cast at h
    linarith
  · rintro ⟨a, b, c, h⟩
    have : (b + c) % 2 = 0 ∨ (a + b) % 2 = 0 ∨ (a + c) % 2 = 0 := by omega
    rcases this with h1 | h1 | h1
    · exact rep122_aux a b c N h1 h
    · exact rep122_aux c a b N h1 (by linarith)
    · exact rep122_aux b a c N h1 (by linarith)

/-- Three of any $u,v,z$ include two of equal parity. -/
private theorem rep124_of_112 (N : ℕ) (h : Rep3 1 1 2 N) : Rep3 1 2 4 N := by
  obtain ⟨x, y, z, h⟩ := h
  push_cast at h
  by_cases hy : y % 2 = 0
  · obtain ⟨j, rfl⟩ : ∃ j, y = 2 * j := ⟨y / 2, by omega⟩
    exact ⟨x, z, j, by push_cast; linarith⟩
  by_cases hx : x % 2 = 0
  · obtain ⟨j, rfl⟩ : ∃ j, x = 2 * j := ⟨x / 2, by omega⟩
    exact ⟨y, z, j, by push_cast; linarith⟩
  obtain ⟨k, hk⟩ : ∃ k, x + y = 2 * k := ⟨(x + y) / 2, by omega⟩
  have hx' : x = 2 * k - y := by omega
  subst hx'
  have h2 : 2 * (k ^ 2 + (k - y) ^ 2 + z ^ 2) = N := by linarith
  have : (k + (k - y)) % 2 = 0 ∨ (k + z) % 2 = 0 ∨ ((k - y) + z) % 2 = 0 := by omega
  rcases this with h1 | h1 | h1
  · exact rep124_aux k (k - y) z N h1 h2
  · exact rep124_aux k z (k - y) N h1 (by linarith)
  · exact rep124_aux (k - y) z k N h1 (by linarith)

/-- $x^2+2y^2+4z^2=x^2+(2z)^2+2y^2$. -/
private theorem rep112_of_124 (N : ℕ) (h : Rep3 1 2 4 N) : Rep3 1 1 2 N := by
  obtain ⟨x, y, z, h⟩ := h
  exact ⟨x, 2 * z, y, by push_cast at h ⊢; linarith⟩

/-- **Legendre–Gauss** (first law; Ramanujan (3.1), credited there to Cauchy): $N$ is
$x^2 + y^2 + z^2$ iff $N$ is not $4^\lambda(8\mu + 7)$. **Wrapper** of `Grosswald.legendre_three_squares`. -/
@[kb "ramanujan1917" "§ 3, (3.1), Collected Papers p. 171 (occurrence ramanujan1927-papers:p20.s3.1)"]
theorem ternary_111 (N : ℕ) : Rep3 1 1 1 N ↔ ¬ IsExc 4 8 7 N := by
  rw [rep3_111_iff, sq3_iff_nat]
  have := QuadFormsKB.Grosswald.legendre_three_squares N
  exact this

/-- **Lebesgue** (second law): $N$ is $x^2 + y^2 + 2z^2$ iff $N$ is not
$4^\lambda(16\mu + 14)$. -/
@[kb "ramanujan1917" "§ 3, Collected Papers p. 171 (occurrence ramanujan1927-papers:p20.s3.1)"]
theorem ternary_112 (N : ℕ) : Rep3 1 1 2 N ↔ ¬ IsExc 4 16 14 N := by
  rw [rep112_iff, sq3_iff_nat, QuadFormsKB.Grosswald.legendre_three_squares]
  exact not_congr (exc_double N)

/-- fourth law: $N$ is $x^2 + 2y^2 + 2z^2$ iff $N$ is not $4^\lambda(8\mu + 7)$. -/
@[kb "ramanujan1917" "§ 3, Collected Papers p. 171 (occurrence ramanujan1927-papers:p20.s3.1)"]
theorem ternary_122 (N : ℕ) : Rep3 1 2 2 N ↔ ¬ IsExc 4 8 7 N := by
  rw [rep122_iff, sq3_iff_nat]
  exact QuadFormsKB.Grosswald.legendre_three_squares N

/-- sixth law: $N$ is $x^2 + 2y^2 + 4z^2$ iff $N$ is not $4^\lambda(16\mu + 14)$. -/
@[kb "ramanujan1917" "§ 3, Collected Papers p. 171 (occurrence ramanujan1927-papers:p20.s3.1)"]
theorem ternary_124 (N : ℕ) : Rep3 1 2 4 N ↔ ¬ IsExc 4 16 14 N := by
  rw [← ternary_112]
  exact ⟨rep112_of_124 N, rep124_of_112 N⟩

/-- **Dirichlet's law for $x^2 + y^2 + 3z^2$** (third law): $N$ is $x^2 + y^2 + 3z^2$ iff
$N$ is not $9^\lambda(9\mu + 6)$. **Stated** (see the module docstring for why). -/
@[kb "ramanujan1917" "§ 3, Collected Papers p. 171 (occurrence ramanujan1927-papers:p20.s3.1)"]
def Ternary113 : Prop := ∀ N : ℕ, Rep3 1 1 3 N ↔ ¬ IsExc 9 9 6 N

/-- fifth law: $N$ is $x^2 + 2y^2 + 3z^2$ iff $N$ is not $4^\lambda(16\mu + 10)$.
**Stated.** -/
@[kb "ramanujan1917" "§ 3, Collected Papers p. 171 (occurrence ramanujan1927-papers:p20.s3.1)"]
def Ternary123 : Prop := ∀ N : ℕ, Rep3 1 2 3 N ↔ ¬ IsExc 4 16 10 N

/-- seventh law: $N$ is $x^2 + 2y^2 + 5z^2$ iff $N$ is neither $25^\lambda(25\mu + 10)$
nor $25^\lambda(25\mu + 15)$. **Stated.** -/
@[kb "ramanujan1917" "§ 3, Collected Papers p. 171 (occurrence ramanujan1927-papers:p20.s3.1)"]
def Ternary125 : Prop := ∀ N : ℕ, Rep3 1 2 5 N ↔ ¬ (IsExc 25 25 10 N ∨ IsExc 25 25 15 N)

/-- **Ramanujan's seven ternary exception laws**, as one proposition. -/
@[kb "ramanujan1917" "§ 3, (3.1)–(3.71), Collected Papers p. 171 (occurrence ramanujan1927-papers:p20.s3.1)"]
def RamanujanTernaryExceptions : Prop :=
  (∀ N : ℕ, Rep3 1 1 1 N ↔ ¬ IsExc 4 8 7 N) ∧ (∀ N : ℕ, Rep3 1 1 2 N ↔ ¬ IsExc 4 16 14 N) ∧ Ternary113 ∧
    (∀ N : ℕ, Rep3 1 2 2 N ↔ ¬ IsExc 4 8 7 N) ∧ Ternary123 ∧ (∀ N : ℕ, Rep3 1 2 4 N ↔ ¬ IsExc 4 16 14 N) ∧
    Ternary125

/-- **Four of the seven laws are proved:** `RamanujanTernaryExceptions` holds iff the three laws for
$x^2 + y^2 + 3z^2$, $x^2 + 2y^2 + 3z^2$, $x^2 + 2y^2 + 5z^2$ hold. -/
theorem ramanujanTernaryExceptions_iff :
    RamanujanTernaryExceptions ↔ Ternary113 ∧ Ternary123 ∧ Ternary125 := by
  constructor
  · rintro ⟨-, -, h3, -, h5, -, h7⟩
    exact ⟨h3, h5, h7⟩
  · rintro ⟨h3, h5, h7⟩
    exact ⟨ternary_111, ternary_112, h3, ternary_122, h5, ternary_124, h7⟩

end QuadFormsKB.Historical.Ramanujan
