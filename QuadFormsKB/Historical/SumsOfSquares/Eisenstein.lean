/-
# Eisenstein's finite-sum formulas for three, seven and ten squares (stated)

**Library** `QuadFormsKB.Historical.SumsOfSquares` (historical library, not imported by `QuadFormsKB`). Targets taken from the historical sources. Each statement below is a named
`Prop`, **stated, not proved** and assumed nowhere; each was checked numerically for every admissible argument $\le 400$
(by brute-force counts). Reasons they are out of reach here are recorded in the docstrings.

* (Eisenstein, *Note sur la représentation d'un nombre par la somme de cinq carrés*, J. reine angew.
  Math. 35 (1847), 368; occurrence `eisenstein1847-cinq-carres:p368.3`) and (the same, reported by
  Dickson, *History* II, ch. VII, p. 263, fn. 25, `dickson1920-history2:p263.2`, for *proper* representations):
  `EisensteinThreeSquares`, `DicksonThreeSquaresProper`; their equivalence is **proved**
  (`dicksonThreeSquaresProper_iff`), since for squarefree $m$ every representation is proper.
* (Eisenstein, *Lehrsätze*, J. reine angew.
  Math. 39 (1850), 180–182, occurrences `eisenstein1850-lehrsaetze:p180.1`–`p180.4`) and (Dickson,
  *History* II, ch. IX, p. 305, fn. 4, `dickson1920-history2:p305.4`): `EisensteinSevenSquares`.
* (*Lehrsätze*, `eisenstein1850-lehrsaetze:p180.5`): `EisensteinPrimeSquares`.
* (Eisenstein, *Mathematische Abhandlungen* (1847), 6. *Neue Theoreme der höhern Arithmetik*,
  p. 195, `eisenstein1847-abhandlungen:p195.5`): `EisensteinTenSquares`.

**Conventions.** $r_s(m) = \#\{\vec x \in \mathbb Z^s : x_0^2 + \dots + x_{s-1}^2 = m\}$ (ordered, signed: Eisenstein's
$\varphi$, $\psi$, $\chi$); $\bigl(\frac\mu m\bigr)$ is Jacobi's symbol (Mathlib's `jacobiSym`, $0$ when
$\gcd(\mu, m) > 1$). Eisenstein's variables $x_1, \dots, x_s$ are `x 0, …, x (s-1)` here.
-/
import QuadFormsKB.Citation
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Algebra.Squarefree.Basic

namespace QuadFormsKB.Historical.SumsOfSquares

/-- **$r_s(m)$**, the number of $\vec x \in \mathbb Z^s$ with $x_0^2 + \dots + x_{s-1}^2 = m$. -/
noncomputable def sqRep (s m : ℕ) : ℕ := Nat.card {x : Fin s → ℤ // ∑ i, x i ^ 2 = m}

/-- **Proper representations** $\varphi_s(m)$: those $\vec x$ with $\gcd(x_0, \dots, x_{s-1}) = 1$ (every common divisor
is a unit). -/
noncomputable def sqRepProper (s m : ℕ) : ℕ :=
  Nat.card {x : Fin s → ℤ // ∑ i, x i ^ 2 = m ∧ ∀ d : ℤ, (∀ i, d ∣ x i) → IsUnit d}

/-- $\sum_{\mu = a}^{b}\bigl(\frac\mu m\bigr)\mu^j$ (Jacobi symbol), an integer. -/
def jacobiPowerSum (m a b j : ℕ) : ℤ := ∑ μ ∈ Finset.Icc a b, jacobiSym μ m * (μ : ℤ) ^ j

/-! ### Three squares -/

/-- **Eisenstein's three-squares formulas** (Eisenstein, J. reine angew. Math. 35 (1847),
368, "from Dirichlet's researches"): for odd squarefree $m \ge 3$,
$$r_3(m) = 24\sum_{\mu=1}^{(m-1)/4}\Bigl(\frac\mu m\Bigr)\ (m \equiv 1 \bmod 4),\qquad
  r_3(m) = 8\sum_{\mu=1}^{(m-1)/2}\Bigl(\frac\mu m\Bigr)\ (m \equiv 3 \bmod 8).$$
**Stated.** *Why out of reach here:* the library proves $r_3(m) = \frac{24}{\pi}\sqrt m\,L(1,\chi_D)$ and Gauss's
class-number form (`Tamagawa.Classical.repNum_sumSq_three_LOne`, `gauss_three_squares`); the missing step is
Dirichlet's evaluation of $L(1, \chi)$ for an odd character as a finite partial sum of the character (the class number
formula in finite form), which is in neither Mathlib nor this library. -/
@[kb "eisenstein1847cinq" "p. 368 (occurrence eisenstein1847-cinq-carres:p368.3)"]
def EisensteinThreeSquares : Prop :=
  ∀ m : ℕ, 3 ≤ m → Odd m → Squarefree m →
    (m % 4 = 1 → (sqRep 3 m : ℤ) = 24 * jacobiPowerSum m 1 ((m - 1) / 4) 0) ∧
    (m % 8 = 3 → (sqRep 3 m : ℤ) = 8 * jacobiPowerSum m 1 ((m - 1) / 2) 0)

/-- **Eisenstein's formulas for proper representations by three squares, as reported by Dickson** (the historical sources; Dickson, *History* II, ch. VII, p. 263, fn. 25): for squarefree $m > 1$, the number $\varphi(m)$ of
proper representations of $m$ by $x^2 + y^2 + z^2$ is $24\sum_{s=1}^{[m/4]}\bigl(\frac sm\bigr)$ for
$m \equiv 1 \pmod 4$ and $8\sum_{s=1}^{[m/2]}\bigl(\frac sm\bigr)$ for $m \equiv 3 \pmod 8$. **Stated**; equivalent to
`EisensteinThreeSquares` (`dicksonThreeSquaresProper_iff`). -/
@[kb "dickson1920" "ch. VII, p. 263, fn. 25 (occurrence dickson1920-history2:p263.2)"]
def DicksonThreeSquaresProper : Prop :=
  ∀ m : ℕ, 1 < m → Squarefree m →
    (m % 4 = 1 → (sqRepProper 3 m : ℤ) = 24 * jacobiPowerSum m 1 (m / 4) 0) ∧
    (m % 8 = 3 → (sqRepProper 3 m : ℤ) = 8 * jacobiPowerSum m 1 (m / 2) 0)

/-- **For squarefree $m$ every representation by a sum of squares is proper:** if $d \mid x_i$ for all $i$ then
$d^2 \mid m$, so $d$ is a unit. -/
theorem sqRepProper_eq_sqRep_of_squarefree (s m : ℕ) (hm : Squarefree m) : sqRepProper s m = sqRep s m := by
  unfold sqRepProper sqRep
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ⟨fun h => h.1, fun h => ⟨h, fun d hd => ?_⟩⟩)
  have hsq : d * d ∣ (m : ℤ) := by
    rw [← h]
    exact Finset.dvd_sum fun i _ => by rw [sq]; exact mul_dvd_mul (hd i) (hd i)
  exact (Int.squarefree_natCast.mpr hm) d hsq

/-- `DicksonThreeSquaresProper` ⟺ `EisensteinThreeSquares` (⟺ ). -/
theorem dicksonThreeSquaresProper_iff : DicksonThreeSquaresProper ↔ EisensteinThreeSquares := by
  have h4 : ∀ m : ℕ, m % 4 = 1 → m / 4 = (m - 1) / 4 := fun m h => by omega
  have h2 : ∀ m : ℕ, m % 8 = 3 → m / 2 = (m - 1) / 2 := fun m h => by omega
  constructor
  · intro H m hm _ hsf
    obtain ⟨H1, H2⟩ := H m (by omega) hsf
    rw [sqRepProper_eq_sqRep_of_squarefree 3 m hsf] at H1 H2
    exact ⟨fun h => by rw [H1 h, h4 m h], fun h => by rw [H2 h, h2 m h]⟩
  · intro H m hm hsf
    have hodd : Odd m ∨ m % 4 ≠ 1 ∧ m % 8 ≠ 3 := by
      rcases Nat.even_or_odd m with he | ho
      · right; obtain ⟨k, rfl⟩ := he; omega
      · left; exact ho
    rw [sqRepProper_eq_sqRep_of_squarefree 3 m hsf]
    rcases hodd with ho | ⟨n1, n3⟩
    · by_cases h3 : 3 ≤ m
      · obtain ⟨H1, H2⟩ := H m h3 ho hsf
        exact ⟨fun h => by rw [H1 h, h4 m h], fun h => by rw [H2 h, h2 m h]⟩
      · have : m = 2 ∨ m = 1 := by omega
        rcases this with rfl | rfl <;> exact ⟨fun h => by omega, fun h => by omega⟩
    · exact ⟨fun h => absurd h n1, fun h => absurd h n3⟩

/-! ### Seven squares (–00622) -/

/-- **Eisenstein's seven-squares formulas** (the historical sources ($m \equiv 7$) ($m \equiv 3$),
($m \equiv 5$) ($m \equiv 1 \bmod 8$), and Dickson's report ;
Eisenstein, *Lehrsätze*, J. reine angew. Math. 39 (1850), 180): for odd squarefree $m > 1$, with $\mu$ running over
$0 < \mu < m/2$ unless said otherwise,
* $m \equiv 7 \pmod 8$: $r_7(m) = -592\sum\bigl(\frac\mu m\bigr)\mu^2$;
* $m \equiv 3 \pmod 8$: $r_7(m) = 280\bigl\{\tfrac13m^2\sum\bigl(\frac\mu m\bigr) - 2\sum\bigl(\frac\mu m\bigr)\mu^2\bigr\}$;
* $m \equiv 5 \pmod 8$: $r_7(m) = 28\sum_{\mu\ \mathrm{odd} < m}(-1)^{(\mu-1)/2}\bigl(\frac\mu m\bigr)\mu(2m-\mu)
  = -28\sum(-1)^\mu\bigl(\frac\mu m\bigr)(m^2 - 4\mu^2)$;
* $m \equiv 1 \pmod 8$: the same first formula, and $r_7(m) = +28\sum(-1)^\mu\bigl(\frac\mu m\bigr)(m^2 - 4\mu^2)$.

(The $m \equiv 3$ case is stated multiplied by $3$, to stay in $\mathbb Z$.) **Stated.** *Why out of reach here:* the
Euler-product form of $r_7(m)$ for squarefree $m$ is **proved** (`seven_squares_squarefree`:
$r_7(m) = c_7(m)\pi^{-3}m^{5/2}\sum_{\mu\ \mathrm{odd}}\bigl(\frac{-m}{\mu}\bigr)\mu^{-3}$); the missing step is the
evaluation of $L(3, \chi)$ for an odd quadratic character as a finite character sum (generalized Bernoulli numbers and
Gauss sums), which is in neither Mathlib nor this library. -/
@[kb "eisenstein1850" "p. 180 (occurrences eisenstein1850-lehrsaetze:p180.1–p180.4); dickson1920 ch. IX, p. 305, fn. 4"]
def EisensteinSevenSquares : Prop :=
  ∀ m : ℕ, 1 < m → Odd m → Squarefree m →
    (m % 8 = 7 → (sqRep 7 m : ℤ) = -592 * jacobiPowerSum m 1 ((m - 1) / 2) 2) ∧
    (m % 8 = 3 → 3 * (sqRep 7 m : ℤ) =
      280 * ((m : ℤ) ^ 2 * jacobiPowerSum m 1 ((m - 1) / 2) 0 - 6 * jacobiPowerSum m 1 ((m - 1) / 2) 2)) ∧
    ((m % 8 = 1 ∨ m % 8 = 5) → (sqRep 7 m : ℤ) =
      28 * ∑ μ ∈ (Finset.range m).filter Odd,
        (-1) ^ ((μ - 1) / 2) * jacobiSym μ m * ((μ : ℤ) * (2 * m - μ))) ∧
    (m % 8 = 5 → (sqRep 7 m : ℤ) =
      -28 * ∑ μ ∈ Finset.Icc 1 ((m - 1) / 2), (-1) ^ μ * jacobiSym μ m * ((m : ℤ) ^ 2 - 4 * μ ^ 2)) ∧
    (m % 8 = 1 → (sqRep 7 m : ℤ) =
      28 * ∑ μ ∈ Finset.Icc 1 ((m - 1) / 2), (-1) ^ μ * jacobiSym μ m * ((m : ℤ) ^ 2 - 4 * μ ^ 2))

/-! ### Primes -/

/-- **Eisenstein's special cases for a prime** (*Lehrsätze*, p. 180, item (5)): for an odd
prime $p$ let $R$, $N$ be the quadratic residues and non-residues in $(0, p/2)$. Then
$r_3(p) = 8(\#R - \#N)$ for $p \equiv 3 \pmod 8$; $r_5(p) = -80(\sum R - \sum N)$ for $p \equiv 1 \pmod 8$;
$r_5(p) = -112(\sum R - \sum N)$ for $p \equiv 5 \pmod 8$; $r_7(p) = -592(\sum R^2 - \sum N^2)$ for $p \equiv 7 \pmod 8$.
Here $\sum_{\mu \in R}\mu^j - \sum_{\mu \in N}\mu^j = \sum_{0<\mu<p/2}\bigl(\frac\mu p\bigr)\mu^j$. **Stated**, out of reach
for the reason given at `EisensteinSevenSquares` (finite evaluation of $L(1,\chi)$, $L(2,\chi)$, $L(3,\chi)$); the
$r_3$ and $r_7$ cases are special cases of `EisensteinThreeSquares` and `EisensteinSevenSquares`. -/
@[kb "eisenstein1850" "p. 180 (occurrence eisenstein1850-lehrsaetze:p180.5)"]
def EisensteinPrimeSquares : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 →
    (p % 8 = 3 → (sqRep 3 p : ℤ) = 8 * jacobiPowerSum p 1 ((p - 1) / 2) 0) ∧
    (p % 8 = 1 → (sqRep 5 p : ℤ) = -80 * jacobiPowerSum p 1 ((p - 1) / 2) 1) ∧
    (p % 8 = 5 → (sqRep 5 p : ℤ) = -112 * jacobiPowerSum p 1 ((p - 1) / 2) 1) ∧
    (p % 8 = 7 → (sqRep 7 p : ℤ) = -592 * jacobiPowerSum p 1 ((p - 1) / 2) 2)

/-! ### Ten squares -/

/-- **Eisenstein's ten-squares formula** (Eisenstein, *Mathematische Abhandlungen*
(1847), 6. *Neue Theoreme der höhern Arithmetik*, p. 195): for $m \equiv 3 \pmod 4$,
$$r_{10}(m) = 12\Bigl(\sum_{d \mid m,\ d \equiv 3 (4)} d^4 - \sum_{d \mid m,\ d \equiv 1 (4)} d^4\Bigr).$$
**Stated.** *Why out of reach here:* the genus of $x_0^2 + \dots + x_9^2$ has more than one class
(`Siegel.exists_repNum_ne_genusRepAvg_sumSq`), so Siegel's formula gives only the genus average; the formula needs the
vanishing at $m \equiv 3 \pmod 4$ of the cusp-form part of $\theta^{10}$ (weight 5 with character), not available. -/
@[kb "eisenstein1847" "6. Neue Theoreme der höhern Arithmetik, p. 195 (occurrence eisenstein1847-abhandlungen:p195.5)"]
def EisensteinTenSquares : Prop :=
  ∀ m : ℕ, m % 4 = 3 →
    (sqRep 10 m : ℤ) = 12 * (∑ d ∈ m.divisors.filter (· % 4 = 3), (d : ℤ) ^ 4 -
      ∑ d ∈ m.divisors.filter (· % 4 = 1), (d : ℤ) ^ 4)

end QuadFormsKB.Historical.SumsOfSquares
