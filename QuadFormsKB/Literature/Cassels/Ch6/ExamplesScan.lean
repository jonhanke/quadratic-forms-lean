/-
# Cassels, Chapter 6, Examples 1-5 (the parts recovered from the page images)

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 6, *Examples*, Ex. 1-5, pp. 99-100
(statements transcribed from the page images of the scan, then paraphrased here).

**Conventions.** Forms are `QuadForm ℚ n` (`RatQF n`); "equivalent over $K$" is
`QuadForm.IsometricIn K` (an invertible substitution $\vec x \mapsto P\vec x$ over $K$ with
$Q(P\vec x) = Q'(\vec x)$); the orthogonal sum is `QuadForm.orthSum`. Indices are 0-based, so Cassels' variables
$x_1, \dots, x_n$ are $x_0, \dots, x_{n-1}$ here, and $\langle a_0, \dots, a_{n-1}\rangle$ is `QuadForm.diag`.
$(a,b)_p$ is `RatPlace.hilbert (RatPlace.finite p) a b`; $\varepsilon_p$ is `RatPlace.hasseSerre`
(Cassels' $c_p$).

**Formalized, with the answers.**
* Example 1: which of four rational forms are isotropic. (i) $x_0^2 + x_1^2 - 15(x_2^2 + x_3^2)$:
  **anisotropic** (`ex1_i`); (ii) $3x_0^2 + 2x_1^2 - 7x_2^2$: **anisotropic** (`ex1_ii`);
  (iii) $3x_0^2 + 2x_1^2 - 11x_2^2$: **isotropic**, zero $(39, 34, 25)$ (`ex1_iii`); (iv)
  $3x_0^2 + 2x_1^2 - 7x_2^2 + 2x_1x_2 + 2x_2x_0 + 2x_0x_1$: **anisotropic** (`ex1_iv`).
* Example 2: whether three pairs of forms are equivalent over $\mathbb Q$. (i) $x_0^2 - 15x_1^2$ and
  $3x_0^2 - 5x_1^2$: **not equivalent** (`ex2_i`); (ii) $x_0^2 - 82x_1^2$ and $2x_0^2 - 41x_1^2$:
  **equivalent**, explicit matrix $\frac13\begin{pmatrix}10 & 41\\ 1 & 5\end{pmatrix}$; this item is proved as
  `QuadFormsKB.Cassels.Ch6.ex2_ii` in `Literature/Cassels/Ch6/Examples.lean` and is not repeated here;
  (iii) $x_0^2 + x_1^2 + 16x_2^2$ and $2x_0^2 + 2x_1^2 + 5x_2^2 - 2x_1x_2 - 2x_0x_2$: **equivalent**, explicit
  matrix (`ex2_iii`).
* Example 3: let $C$ be the set of rationals $c$ such that $f = 42x_0^2 - 20x_1^2 + 15x_2^2 - 18x_3^2$ is
  equivalent over $\mathbb Q$ to $c(x_0^2 + 7x_1^2) + g(x_2, x_3)$ for some binary rational form $g$ (depending
  on $c$); show that $bC$ is a subgroup of $\mathbb Q^\times$ for some $b$, and describe $C$ completely.
  **Answer** (`ex3_description`, `ex3_subgroup`): $C = \{c \in \mathbb Q^\times : (c,-7)_p = -1 \text{ for }
  p = 5, \ (c,-7)_p = 1 \text{ for all other primes } p \equiv 1 \pmod 4\}$ (no condition at $2$, at primes
  $p \equiv 3 \pmod 4$, or at $\infty$); $C$ is the coset $5H$ where
  $H = \{u : (u,-7)_p = 1 \ \forall p \equiv 1 \pmod 4\}$ is a subgroup, so $b = 5$ works (and $5 \in C$,
  `ex3_five_mem`). Reason: $d(f) = 7$ modulo squares, so $g \cong a\langle 1, 1\rangle$, and the Hasse
  invariants force $(a,-1)_p = \varepsilon_p(f)\,(c,-7)_p$; this is only a condition where $-1$ is a square
  ($p \equiv 1 \pmod 4$), and $\varepsilon_p(f) = -1$ exactly at $p = 5$ among those primes.
* Example 4: $\langle 1,1,1,1\rangle$ and $b\langle 1,1,1,1\rangle$ are equivalent for every rational $b > 0$
  (`ex4`, by Euler's four-square identity; Cassels' hint uses the local-global principle).
* Example 5: for which rational $m$ are $(m+1)(x_0^2 + x_1^2 + x_2^2) + m x_3^2$ and
  $x_0^2 + x_1^2 + x_2^2 + m(m+1)x_3^2$ equivalent over $\mathbb Q$? **Answer** (`ex5`): exactly for
  $m > -1$ (for $m = 0$ both are $x_0^2 + x_1^2 + x_2^2$; for $m \le -1$ the first form takes no positive value
  but the second represents $1$; for $m > -1$, $m \ne 0$, the determinants differ by $(m+1)^2$ and all
  Hasse invariants are $1$ because $(m+1, -m)_v = 1$, so the forms are equivalent over every completion).

**Not formalized here / reconstructed.** Nothing is left as a named statement in this file; every item above
is proved. No erratum was found for these examples. The scan's printed hints are not reproduced.
-/
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski
import QuadFormsKB.Literature.LocalGlobal.HasseConventions
import QuadFormsKB.Literature.LocalGlobal.LocalClassificationNF
import QuadFormsKB.Literature.LocalGlobal.PrescribedSymbols
import QuadFormsKB.Literature.Cassels.Ch6.Ex8
import QuadFormsKB.Literature.Cassels.Ch6.Examples

namespace QuadFormsKB.Cassels.Ch6.Scan

open QuadFormsKB Matrix

/-- Helper: scale a nonzero $p$-adic vector to a primitive integral vector: there are $c \ne 0$ and
$z \in \mathbb Z_p^n$ with some coordinate a unit and $x = c\,z$. -/
theorem exists_primitive (p : ℕ) [Fact p.Prime] {n : ℕ} (x : Fin n → ℚ_[p]) (hx : x ≠ 0) :
    ∃ (c : ℚ_[p]) (z : Fin n → ℤ_[p]), c ≠ 0 ∧ (∃ i, IsUnit (z i)) ∧
      ∀ i, x i = c * (z i : ℚ_[p]) := by
  classical
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    by_contra h
    apply hx; funext i
    exact absurd ⟨i, Finset.mem_univ i⟩ h
  obtain ⟨i0, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => ‖x i‖) hne
  have h0 : x i0 ≠ 0 := by
    intro h0; apply hx; funext i
    have := hmax i (Finset.mem_univ i)
    rw [h0, norm_zero] at this
    simpa using this
  have hn0 : 0 < ‖x i0‖ := norm_pos_iff.2 h0
  have hle : ∀ i, ‖x i / x i0‖ ≤ 1 := fun i => by
    rw [norm_div]; exact (div_le_one hn0).2 (hmax i (Finset.mem_univ i))
  refine ⟨x i0, fun i => ⟨x i / x i0, (PadicInt.mem_subring_iff p).2 (hle i)⟩, h0, ⟨i0, ?_⟩, fun i => ?_⟩
  · refine PadicInt.isUnit_iff.2 ?_
    show ‖x i0 / x i0‖ = 1
    rw [div_self h0, norm_one]
  · show x i = x i0 * (x i / x i0)
    field_simp

/-- Helper: a unit of $\mathbb Z_p$ stays a unit modulo $p^k$, i.e. its representative is coprime to $p^k$. -/
theorem coprime_of_isUnit (p : ℕ) [Fact p.Prime] (k : ℕ) {z : ℤ_[p]} (h : IsUnit z) :
    ((PadicInt.toZModPow k z : ZMod (p ^ k)).val).Coprime (p ^ k) := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
  exact h.map _

/-- Helper: if a rational form $Q$ takes no zero value at a primitive integral vector, it is anisotropic over
$\mathbb Q_p$ (here $Q$ is evaluated at the image of $z \in \mathbb Z_p^n$ in $\mathbb Q_p^n$). -/
theorem not_isotropic_of_primitive (p : ℕ) [Fact p.Prime] {n : ℕ} (Q : RatQF n)
    (h : ∀ z : Fin n → ℤ_[p], (∃ i, IsUnit (z i)) → Q.evalIn ℚ_[p] (fun i => (z i : ℚ_[p])) ≠ 0) :
    ¬ Q.IsotropicIn ℚ_[p] := by
  rintro ⟨x, hx0, hx⟩
  obtain ⟨c, z, hc, hz, hxz⟩ := exists_primitive p x hx0
  have hxe : x = c • (fun i => (z i : ℚ_[p])) := funext fun i => by simp [hxz]
  rw [hxe, QuadForm.evalIn_smul] at hx
  exact h z hz ((mul_eq_zero.1 hx).resolve_left (pow_ne_zero 2 hc))

section Ex3Ex5

open RatPlace

/-! ### Helpers for Examples 3 and 5: Hilbert symbols and Hasse invariants -/

/-- Helper: rational diagonal forms with the same number $r$ of negative entries are equivalent over $\mathbb R$
($a, b$ the diagonals, all entries nonzero; Sylvester's law of inertia and its converse). -/
theorem isometricIn_real_of_negCount {n : ℕ} (a b : Fin n → ℚ) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (h : negCount a = negCount b) : (QuadForm.diag a).IsometricIn ℝ (QuadForm.diag b) := by
  rw [isometricIn_cast]
  have ha' : ∀ i, algebraMap ℚ ℝ (a i) ≠ 0 := fun i => by simpa using ha i
  have hb' : ∀ i, algebraMap ℚ ℝ (b i) ≠ 0 := fun i => by simpa using hb i
  rw [LocalClassNF.isometric_real_vec_iff _ _ ha' hb']
  have : ∀ c : Fin n → ℚ, HasseIsoNF.negCountR (fun i => algebraMap ℚ ℝ (c i)) = negCount c := by
    intro c
    simp [HasseIsoNF.negCountR, negCount]
  rw [this, this]; exact h

/-- Helper: $(1, a)_v = 1$ at every place $v$. -/
theorem hilbert_one_left (v : RatPlace) (a : ℚ) : v.hilbert 1 a = 1 := by
  cases v <;> simp only [RatPlace.hilbert, Rat.cast_one] <;> exact PadicClass.hs_one_left _

/-- Helper: $(a, 1)_v = 1$ at every place $v$. -/
theorem hilbert_one_right (v : RatPlace) (a : ℚ) : v.hilbert a 1 = 1 := by
  rw [RatPlace.hilbert_comm]; exact hilbert_one_left v a

/-- Helper: the Hasse invariant of $\langle c, 7c, a, b\rangle$ when $ab = s^2$ is a nonzero square:
$\varepsilon_v = (c,-7)_v\,(a,-1)_v$ (here $c, a, b, s \in \mathbb Q^\times$ and $v$ is any place). -/
theorem hasse_c7ab (v : RatPlace) (c a b s : ℚ) (hc : c ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0)
    (hab : a * b = s ^ 2) :
    v.hasseSerre ![c, 7 * c, a, b] = v.hilbert c (-7) * v.hilbert a (-1) := by
  have h7 : (7 : ℚ) * c ≠ 0 := mul_ne_zero (by norm_num) hc
  have h1 : v.hilbert c a * v.hilbert c b = 1 := by
    rw [← RatPlace.hilbert_mul_right v c a b hc ha hb, hab, RatPlace.hilbert_sq_right v c s hs]
  have h2 : v.hilbert (7 * c) a * v.hilbert (7 * c) b = 1 := by
    rw [← RatPlace.hilbert_mul_right v _ a b h7 ha hb, hab, RatPlace.hilbert_sq_right v _ s hs]
  have h3 : v.hilbert a b * v.hilbert a (-1) = 1 := by
    have : v.hilbert a (a * b) = 1 := by rw [hab, RatPlace.hilbert_sq_right v a s hs]
    rw [RatPlace.hilbert_mul_right v a a b ha ha hb, RatPlace.hilbert_self v a ha] at this
    rw [mul_comm]; exact this
  have h4 : v.hilbert c (7 * c) = v.hilbert c (-7) := by
    rw [RatPlace.hilbert_mul_right v c 7 c hc (by norm_num) hc, RatPlace.hilbert_self v c hc,
      ← RatPlace.hilbert_mul_right v c 7 (-1) hc (by norm_num) (by norm_num)]
    norm_num
  simp only [RatPlace.hasseSerre, Fin.prod_univ_four]
  simp
  rw [h4]
  rcases RatPlace.hilbert_pm v c a with e1 | e1 <;> rcases RatPlace.hilbert_pm v c b with e2 | e2 <;>
    rcases RatPlace.hilbert_pm v (7 * c) a with e3 | e3 <;> rcases RatPlace.hilbert_pm v (7 * c) b with e4 | e4 <;>
    rcases RatPlace.hilbert_pm v a b with e5 | e5 <;> rcases RatPlace.hilbert_pm v a (-1) with e6 | e6 <;>
    simp_all

/-- Helper: $(m+1, -m)_v = 1$ at every place $v$ (the conic $z^2 = (m+1)x^2 - m y^2$ has the solution
$(1,1,1)$); here $m \in \mathbb Q$. -/
theorem hilbert_succ_neg (v : RatPlace) (m : ℚ) : v.hilbert (m + 1) (-m) = 1 := by
  cases v <;> simp only [RatPlace.hilbert, hilbertSymbol] <;> split_ifs with h
  all_goals first | rfl | exact absurd ⟨1, 1, 1, by simp, by push_cast; ring⟩ h

/-- Helper: for an odd prime $p$, $-1$ is a square in $\mathbb Q_p$ iff $p \not\equiv 3 \pmod 4$. -/
theorem isSquare_neg_one_padic_iff (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    IsSquare (-1 : ℚ_[p]) ↔ p % 4 ≠ 3 := by
  have h := HilbertLocal.isSquare_unit_iff hp2 (-1 : ℤ_[p]ˣ)
  have e1 : (((-1 : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = -1 := by simp
  have e2 : PadicInt.toZMod (((-1 : ℤ_[p]ˣ) : ℤ_[p])) = -1 := by simp
  rw [e1, e2] at h
  rw [h]
  exact ZMod.exists_sq_eq_neg_one_iff

/-- Helper: $-1$ is not a square in $\mathbb Q_2$ (a zero of $x^2+y^2$ would be a primitive zero, impossible
modulo $4$). -/
theorem not_isSquare_neg_one_two : ¬ IsSquare (-1 : ℚ_[2]) := by
  rintro ⟨s, hs⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hiso : (QuadForm.diag ![(1 : ℚ), 1]).IsotropicIn ℚ_[2] := by
    refine ⟨![s, 1], fun h0 => by simpa using congrFun h0 1, ?_⟩
    rw [QuadForm.evalIn_diag]
    simp [Fin.sum_univ_two]
    linear_combination -hs
  refine not_isotropic_of_primitive 2 _ (fun z ⟨i, hi⟩ hz => ?_) hiso
  rw [QuadForm.evalIn_diag] at hz
  simp [Fin.sum_univ_two] at hz
  have hz' : z 0 ^ 2 + z 1 ^ 2 = 0 := PadicInt.coe_eq_zero.1 (by push_cast; exact hz)
  have h2 := congrArg (PadicInt.toZModPow 2) hz'
  simp only [map_add, map_pow, map_zero] at h2
  have key : ∀ a b : ZMod (2 ^ 2), (a.val.Coprime (2 ^ 2) ∨ b.val.Coprime (2 ^ 2)) → a ^ 2 + b ^ 2 ≠ 0 := by
    decide
  refine key _ _ ?_ h2
  have hc := coprime_of_isUnit 2 2 hi
  fin_cases i
  · exact Or.inl hc
  · exact Or.inr hc

/-- Helper: at a prime $p \equiv 1 \pmod 4$, $(-1, x)_p = 1$ for every rational $x$ ($-1$ is a square in
$\mathbb Q_p$). -/
theorem hilbert_neg_one_of_mod_four (p : Nat.Primes) (hp : p.1 % 4 = 1) (x : ℚ) :
    (RatPlace.finite p).hilbert (-1) x = 1 := by
  have : Fact p.1.Prime := ⟨p.2⟩
  have hp2 : p.1 ≠ 2 := by omega
  obtain ⟨s, hs⟩ := (isSquare_neg_one_padic_iff p.1 hp2).2 (by omega)
  simp only [RatPlace.hilbert, hilbertSymbol]
  split_ifs with h
  · rfl
  · exact absurd ⟨1, 0, s, by simp, by push_cast; linear_combination -hs⟩ h

/-- Helper: over $\mathbb R$ there is $x \ne 0$ with $(-1, x)_{\mathbb R} = -1$. -/
theorem local_neg_one_infinite :
    ∃ x : ℝ, x ≠ 0 ∧ hilbertSymbol ℝ (algebraMap ℚ ℝ (-1)) x = -1 := by
  refine ⟨algebraMap ℚ ℝ (-1), by simp, ?_⟩
  have := hilbert_infinite_eq (-1) (-1) (by norm_num) (by norm_num)
  simpa [RatPlace.hilbert] using this

/-- Helper: over $\mathbb Q_q$, $q \not\equiv 1 \pmod 4$ prime, there is $x \ne 0$ with $(-1, x)_q = -1$
($-1$ is not a square there). -/
theorem local_neg_one_finite (q : ℕ) [hq' : Fact q.Prime] (hv : q % 4 ≠ 1) :
    ∃ x : ℚ_[q], x ≠ 0 ∧ hilbertSymbol ℚ_[q] (algebraMap ℚ ℚ_[q] (-1)) x = -1 := by
  have hq : q.Prime := hq'.out
  have hns : ¬ IsSquare (-1 : ℚ_[q]) := by
    by_cases h2 : q = 2
    · subst h2; exact not_isSquare_neg_one_two
    · rw [isSquare_neg_one_padic_iff q h2]
      have hodd := hq.eq_two_or_odd
      omega
  obtain ⟨x, hx0, hx⟩ := PadicClass.padic_exists_neg_one (p := q) (-1) (by simp) hns
  exact ⟨x, hx0, by simpa using hx⟩

/-- Helper: a $\pm 1$-valued function on the places of $\mathbb Q$ with finite multiplicative support and
product $1$ takes the value $-1$ at finitely many places, an even number of them. -/
theorem even_of_finprod (η : RatPlace → ℤ) (hη : ∀ v, η v = 1 ∨ η v = -1)
    (hfin : Function.HasFiniteMulSupport η) (hprod : ∏ᶠ v : RatPlace, η v = 1) :
    {v : RatPlace | η v = -1}.Finite ∧ Even {v : RatPlace | η v = -1}.ncard := by
  have hms : Function.mulSupport η = {v | η v = -1} := by
    ext v
    rcases hη v with h | h <;> simp [Function.mem_mulSupport, h]
  have hF : {v | η v = -1}.Finite := by rw [← hms]; exact hfin
  refine ⟨hF, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hF.toFinset) (by rw [hms]; simp)] at hprod
  rw [Finset.prod_congr rfl (fun v hv => (by simpa using hv : η v = -1))] at hprod
  rw [Finset.prod_const, neg_one_pow_eq_one_iff_even (by decide)] at hprod
  rw [Set.ncard_eq_toFinset_card _ hF]
  exact hprod

/-- Helper (Serre III, Thm. 4 for the single element $-1$): given signs $\eta_v \in \{\pm1\}$, equal to $-1$ at an
even finite set of places and equal to $1$ at every prime $p \equiv 1 \pmod 4$ (where $-1$ is a square), there
is a rational $a \ne 0$ with $(-1, a)_v = \eta_v$ at every place $v$. -/
theorem exists_neg_one_symbols (η : RatPlace → ℤ) (hη : ∀ v, η v = 1 ∨ η v = -1)
    (hfin : {v : RatPlace | η v = -1}.Finite) (hev : Even {v : RatPlace | η v = -1}.ncard)
    (hp : ∀ p : Nat.Primes, p.1 % 4 = 1 → η (RatPlace.finite p) = 1) :
    ∃ a : ℚ, a ≠ 0 ∧ ∀ v : RatPlace, v.hilbert (-1) a = η v := by
  obtain ⟨a, ha, h⟩ := Prescribed.exists_rat_prescribed_hilbert (ι := Unit) (fun _ => (-1 : ℚ))
    (fun _ => by norm_num) (fun _ v => η v) (fun _ v => hη v) (by simpa using hfin)
    (fun _ => hev) (fun v => by
      by_cases h1 : η v = 1
      · cases v with
        | infinite =>
          exact ⟨1, one_ne_zero, fun _ => by rw [h1, hilbertSymbol_comm]; exact PadicClass.hs_one_left _⟩
        | finite p =>
          have : Fact p.1.Prime := ⟨p.2⟩
          exact ⟨1, one_ne_zero, fun _ => by rw [h1, hilbertSymbol_comm]; exact PadicClass.hs_one_left _⟩
      · have h2 : η v = -1 := (hη v).resolve_left h1
        cases v with
        | infinite =>
          obtain ⟨x, hx0, hx⟩ := local_neg_one_infinite
          exact ⟨x, hx0, fun _ => by rw [hx, h2]⟩
        | finite p =>
          have : Fact p.1.Prime := ⟨p.2⟩
          have h4 : p.1 % 4 ≠ 1 := fun h4 => h1 (hp p h4)
          obtain ⟨x, hx0, hx⟩ := local_neg_one_finite p.1 h4
          exact ⟨x, hx0, fun _ => by rw [hx, h2]⟩)
  exact ⟨a, ha, fun v => h () v⟩

/-- Helper: $(a, b)_p = -1$ if $a x^2 + b y^2 - z^2$ has no zero modulo $p^k$ at a vector with a coordinate prime
to $p$ ($a, b$ integers, $p$ a prime of `Nat.Primes`): then the conic has no $p$-adic point. -/
theorem rat_hilbert_neg_one_of_primitive (p : Nat.Primes) (k : ℕ) (a b : ℤ)
    (h : ∀ x y z : ZMod (p.1 ^ k), (x.val.Coprime (p.1 ^ k) ∨ y.val.Coprime (p.1 ^ k) ∨ z.val.Coprime (p.1 ^ k)) →
      (a : ZMod (p.1 ^ k)) * x ^ 2 + (b : ZMod (p.1 ^ k)) * y ^ 2 + (-1) * z ^ 2 ≠ 0) :
    (RatPlace.finite p).hilbert (a : ℚ) (b : ℚ) = -1 := by
  have : Fact p.1.Prime := ⟨p.2⟩
  rcases RatPlace.hilbert_pm (RatPlace.finite p) (a : ℚ) (b : ℚ) with h1 | h1
  swap; · exact h1
  exfalso
  have h1' : hilbertSymbol ℚ_[p.1] (algebraMap ℚ ℚ_[p.1] (a : ℚ)) (algebraMap ℚ ℚ_[p.1] (b : ℚ)) = 1 := by
    simpa [RatPlace.hilbert] using h1
  have hiso := (hilbertSymbol_eq_one_iff_isotropic ℚ_[p.1] (a : ℚ) (b : ℚ)).1 h1'
  refine not_isotropic_of_primitive p.1 _ (fun z ⟨i, hi⟩ hz => ?_) hiso
  rw [QuadForm.evalIn_diag] at hz
  simp [Fin.sum_univ_three] at hz
  have hz' : (a : ℤ_[p.1]) * z 0 ^ 2 + (b : ℤ_[p.1]) * z 1 ^ 2 + (-1) * z 2 ^ 2 = 0 :=
    PadicInt.coe_eq_zero.1 (by push_cast; linear_combination hz)
  have h2 := congrArg (PadicInt.toZModPow k) hz'
  simp only [map_add, map_neg, map_mul, map_pow, map_zero, map_intCast, map_one] at h2
  refine h _ _ _ ?_ h2
  have hc := coprime_of_isUnit p.1 k hi
  fin_cases i
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr hc)

/-- The prime $5$ as an element of `Nat.Primes`. -/
def p5 : Nat.Primes := ⟨5, by norm_num⟩

/-- Helper: $(42, -20)_5 = -1$. -/
theorem h5_a : (RatPlace.finite p5).hilbert 42 (-20) = -1 := by
  have key : ∀ x y z : ZMod (5 ^ 2), (x.val.Coprime (5 ^ 2) ∨ y.val.Coprime (5 ^ 2) ∨ z.val.Coprime (5 ^ 2)) →
      ((42 : ℤ) : ZMod (5 ^ 2)) * x ^ 2 + ((-20 : ℤ) : ZMod (5 ^ 2)) * y ^ 2 + (-1) * z ^ 2 ≠ 0 := by decide
  simpa using rat_hilbert_neg_one_of_primitive p5 2 42 (-20) key

/-- Helper: $(42, 15)_5 = -1$. -/
theorem h5_b : (RatPlace.finite p5).hilbert 42 15 = -1 := by
  have key : ∀ x y z : ZMod (5 ^ 2), (x.val.Coprime (5 ^ 2) ∨ y.val.Coprime (5 ^ 2) ∨ z.val.Coprime (5 ^ 2)) →
      ((42 : ℤ) : ZMod (5 ^ 2)) * x ^ 2 + ((15 : ℤ) : ZMod (5 ^ 2)) * y ^ 2 + (-1) * z ^ 2 ≠ 0 := by decide
  simpa using rat_hilbert_neg_one_of_primitive p5 2 42 15 key

/-- Helper: $(-20, 15)_5 = -1$. -/
theorem h5_c : (RatPlace.finite p5).hilbert (-20) 15 = -1 := by
  have key : ∀ x y z : ZMod (5 ^ 2), (x.val.Coprime (5 ^ 2) ∨ y.val.Coprime (5 ^ 2) ∨ z.val.Coprime (5 ^ 2)) →
      ((-20 : ℤ) : ZMod (5 ^ 2)) * x ^ 2 + ((15 : ℤ) : ZMod (5 ^ 2)) * y ^ 2 + (-1) * z ^ 2 ≠ 0 := by decide
  simpa using rat_hilbert_neg_one_of_primitive p5 2 (-20) 15 key

/-- Helper: $(-20, -18)_5 = -1$. -/
theorem h5_d : (RatPlace.finite p5).hilbert (-20) (-18) = -1 := by
  have key : ∀ x y z : ZMod (5 ^ 2), (x.val.Coprime (5 ^ 2) ∨ y.val.Coprime (5 ^ 2) ∨ z.val.Coprime (5 ^ 2)) →
      ((-20 : ℤ) : ZMod (5 ^ 2)) * x ^ 2 + ((-18 : ℤ) : ZMod (5 ^ 2)) * y ^ 2 + (-1) * z ^ 2 ≠ 0 := by decide
  simpa using rat_hilbert_neg_one_of_primitive p5 2 (-20) (-18) key

/-- Helper: $(15, -18)_5 = -1$. -/
theorem h5_e : (RatPlace.finite p5).hilbert 15 (-18) = -1 := by
  have key : ∀ x y z : ZMod (5 ^ 2), (x.val.Coprime (5 ^ 2) ∨ y.val.Coprime (5 ^ 2) ∨ z.val.Coprime (5 ^ 2)) →
      ((15 : ℤ) : ZMod (5 ^ 2)) * x ^ 2 + ((-18 : ℤ) : ZMod (5 ^ 2)) * y ^ 2 + (-1) * z ^ 2 ≠ 0 := by decide
  simpa using rat_hilbert_neg_one_of_primitive p5 2 15 (-18) key

/-- Helper: $(5, -7)_5 = -1$. -/
theorem h5_f : (RatPlace.finite p5).hilbert 5 (-7) = -1 := by
  have key : ∀ x y z : ZMod (5 ^ 2), (x.val.Coprime (5 ^ 2) ∨ y.val.Coprime (5 ^ 2) ∨ z.val.Coprime (5 ^ 2)) →
      ((5 : ℤ) : ZMod (5 ^ 2)) * x ^ 2 + ((-7 : ℤ) : ZMod (5 ^ 2)) * y ^ 2 + (-1) * z ^ 2 ≠ 0 := by decide
  simpa using rat_hilbert_neg_one_of_primitive p5 2 5 (-7) key

/-- Helper: an integer $n$ prime to $p$ has $p$-adic valuation $0$ (as a rational number). -/
theorem padicValRat_int_of_not_dvd (p : ℕ) [Fact p.Prime] (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) :
    padicValRat p (n : ℚ) = 0 := by
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hn]; rfl

/-- Helper: $(42, -18)_5 = 1$ (both are $5$-adic units). -/
theorem h5_g : (RatPlace.finite p5).hilbert 42 (-18) = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact HilbertLocal.hilbert_eq_one_of_padicValRat (p := 5) (by norm_num) 42 (-18) (by norm_num) (by norm_num)
    (by simpa using padicValRat_int_of_not_dvd 5 42 (by norm_num))
    (by simpa using padicValRat_int_of_not_dvd 5 (-18) (by norm_num))

/-- Helper: the Hasse invariant of $\langle 42, -20, 15, -18\rangle$ at $5$ is $-1$ (five of the six Hilbert
symbols are $-1$). -/
theorem eps5 : (RatPlace.finite p5).hasseSerre ![42, -20, 15, -18] = -1 := by
  simp only [RatPlace.hasseSerre, Fin.prod_univ_four]
  simp
  rw [h5_a, h5_b, h5_c, h5_d, h5_e, h5_g]
  norm_num

/-- Helper: a prime $p \equiv 1 \pmod 4$, $p \ne 5$, divides none of $42, 20, 15, 18$ (as natural numbers). -/
theorem not_dvd_F (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 1) (h5 : p ≠ 5) (n : ℕ)
    (hn : n = 42 ∨ n = 20 ∨ n = 15 ∨ n = 18) : ¬ p ∣ n := by
  intro hd
  have hle : p ≤ n := Nat.le_of_dvd (by omega) hd
  have : p ≤ 42 := by omega
  interval_cases p <;> first | omega | (norm_num at hp)

/-- Helper: the Hasse invariant of $\langle 42, -20, 15, -18\rangle$ at a prime $p \equiv 1 \pmod 4$,
$p \ne 5$, is $1$ (all four entries are $p$-adic units). -/
theorem eps_F_other (p : Nat.Primes) (h4 : p.1 % 4 = 1) (h5 : p.1 ≠ 5) :
    (RatPlace.finite p).hasseSerre ![42, -20, 15, -18] = 1 := by
  have : Fact p.1.Prime := ⟨p.2⟩
  have hp2 : p.1 ≠ 2 := by omega
  have hv : ∀ n : ℤ, (n = 42 ∨ n = -20 ∨ n = 15 ∨ n = -18) → padicValRat p.1 (n : ℚ) = 0 := by
    intro n hn
    apply padicValRat_int_of_not_dvd
    intro hd
    have hd' : p.1 ∣ n.natAbs := by exact_mod_cast Int.natCast_dvd.1 hd
    refine not_dvd_F p.1 p.2 h4 h5 n.natAbs ?_ hd'
    rcases hn with rfl | rfl | rfl | rfl <;> simp
  have key : ∀ a b : ℚ, a ≠ 0 → b ≠ 0 → padicValRat p.1 a = 0 → padicValRat p.1 b = 0 →
      (RatPlace.finite p).hilbert a b = 1 := fun a b ha hb h1 h2 =>
    HilbertLocal.hilbert_eq_one_of_padicValRat hp2 a b ha hb h1 h2
  have v1 : padicValRat p.1 (42 : ℚ) = 0 := by simpa using hv 42 (by simp)
  have v2 : padicValRat p.1 (-20 : ℚ) = 0 := by simpa using hv (-20) (by simp)
  have v3 : padicValRat p.1 (15 : ℚ) = 0 := by simpa using hv 15 (by simp)
  have v4 : padicValRat p.1 (-18 : ℚ) = 0 := by simpa using hv (-18) (by simp)
  simp only [RatPlace.hasseSerre, Fin.prod_univ_four]
  simp
  rw [key 42 (-20) (by norm_num) (by norm_num) v1 v2, key 42 15 (by norm_num) (by norm_num) v1 v3,
    key 42 (-18) (by norm_num) (by norm_num) v1 v4, key (-20) 15 (by norm_num) (by norm_num) v2 v3,
    key (-20) (-18) (by norm_num) (by norm_num) v2 v4, key 15 (-18) (by norm_num) (by norm_num) v3 v4]
  norm_num

/-- Helper: the Hasse invariant of $\langle 42, -20, 15, -18\rangle$ at the real place is $-1$ (two negative
entries, hence one pair of negatives). -/
theorem eps_F_infinite : RatPlace.infinite.hasseSerre ![42, -20, 15, -18] = -1 := by
  have e1 : RatPlace.infinite.hilbert 42 (-20) = 1 := by
    rw [hilbert_infinite_eq _ _ (by norm_num) (by norm_num)]; norm_num
  have e2 : RatPlace.infinite.hilbert 42 15 = 1 := by
    rw [hilbert_infinite_eq _ _ (by norm_num) (by norm_num)]; norm_num
  have e3 : RatPlace.infinite.hilbert 42 (-18) = 1 := by
    rw [hilbert_infinite_eq _ _ (by norm_num) (by norm_num)]; norm_num
  have e4 : RatPlace.infinite.hilbert (-20) 15 = 1 := by
    rw [hilbert_infinite_eq _ _ (by norm_num) (by norm_num)]; norm_num
  have e5 : RatPlace.infinite.hilbert (-20) (-18) = -1 := by
    rw [hilbert_infinite_eq _ _ (by norm_num) (by norm_num)]; norm_num
  have e6 : RatPlace.infinite.hilbert 15 (-18) = 1 := by
    rw [hilbert_infinite_eq _ _ (by norm_num) (by norm_num)]; norm_num
  simp only [RatPlace.hasseSerre, Fin.prod_univ_four]
  simp
  rw [e1, e2, e3, e4, e5, e6]
  norm_num

/-- Helper: $(5, -7)_p$ for a prime $p \equiv 1 \pmod 4$ is $-1$ at $p = 5$ and $1$ otherwise. -/
theorem hilbert_five_neg_seven (p : Nat.Primes) (h4 : p.1 % 4 = 1) :
    (RatPlace.finite p).hilbert 5 (-7) = if p.1 = 5 then -1 else 1 := by
  by_cases h5 : p.1 = 5
  · have : p = p5 := Subtype.ext h5
    subst this
    simp only [h5, ↓reduceIte]
    exact h5_f
  · simp only [h5, ↓reduceIte]
    have : Fact p.1.Prime := ⟨p.2⟩
    have hp2 : p.1 ≠ 2 := by omega
    refine HilbertLocal.hilbert_eq_one_of_padicValRat hp2 5 (-7) (by norm_num) (by norm_num) ?_ ?_
    · simpa using padicValRat_int_of_not_dvd p.1 5 (fun hd => h5 (by
        have : p.1 ∣ 5 := by exact_mod_cast hd
        exact (Nat.prime_dvd_prime_iff_eq p.2 (by norm_num)).1 this))
    · simpa using padicValRat_int_of_not_dvd p.1 (-7) (fun hd => by
        have : p.1 ∣ 7 := by
          have := (Int.natCast_dvd.1 hd)
          simpa using this
        have := (Nat.prime_dvd_prime_iff_eq p.2 (by norm_num)).1 this
        omega)

/-! ### Helpers for Example 3: the orthogonal sum of binary forms -/

/-- Helper: values of the orthogonal sum of two binary forms, as a form in four variables. -/
theorem evalIn_orthSum_two (K : Type) [Field K] [CharZero K] (Q₁ Q₂ : QuadForm ℚ 2) (x : Fin 4 → K) :
    (QuadForm.orthSum Q₁ Q₂).evalIn K x = Q₁.evalIn K ![x 0, x 1] + Q₂.evalIn K ![x 2, x 3] := by
  rw [QuadForm.evalIn_orthSum]
  congr 2 <;> funext a <;> fin_cases a <;> rfl

/-- Helper: the values of the binary form $c\,(y_0^2 + 7y_1^2)$ (`c • diag ![1, 7]`) over $K$. -/
theorem evalIn_smul_diag (K : Type) [Field K] [CharZero K] (c : ℚ) (y : Fin 2 → K) :
    (c • QuadForm.diag ![(1 : ℚ), 7]).evalIn K y = algebraMap ℚ K c * (y 0 ^ 2 + 7 * y 1 ^ 2) := by
  simp [QuadForm.evalIn, Fin.sum_univ_two, QuadForm.diag, Matrix.diagonal_apply]
  ring

/-- Helper: the block matrix $\mathrm{diag}(1, 1, R)$ for a $2 \times 2$ matrix $R$. -/
def blk (R : Matrix (Fin 2) (Fin 2) ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, R 0 0, R 0 1; 0, 0, R 1 0, R 1 1]

/-- Helper: $\det\,\mathrm{blk}(R) = \det R$. -/
theorem det_blk (R : Matrix (Fin 2) (Fin 2) ℚ) : (blk R).det = R.det := by
  rw [Matrix.det_fin_two]
  simp [blk, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  ring

/-- Helper: $\mathrm{blk}(R)\vec x = (x_0, x_1, R(x_2, x_3))$. -/
theorem blk_mulVec (R : Matrix (Fin 2) (Fin 2) ℚ) (x : Fin 4 → ℚ) :
    (blk R *ᵥ x) = ![x 0, x 1, (R *ᵥ ![x 2, x 3]) 0, (R *ᵥ ![x 2, x 3]) 1] := by
  funext i
  fin_cases i <;> simp [blk, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Helper: if the binary forms satisfy $g' \cong g$ then $A \perp g' \cong A \perp g$ for every binary form
$A$ (over $\mathbb Q$). -/
theorem isometric_orthSum_right (A g g' : QuadForm ℚ 2) (h : g'.IsometricIn ℚ g) :
    (QuadForm.orthSum A g').IsometricIn ℚ (QuadForm.orthSum A g) := by
  obtain ⟨R, hR, hRg⟩ := h
  refine ⟨blk R, ?_, fun x => ?_⟩
  · rw [det_blk]; exact hR
  · rw [evalIn_orthSum_two, evalIn_orthSum_two, blk_mulVec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [← hRg]
    rfl

/-- Helper: $c\,(x_0^2 + 7x_1^2) \perp \langle d_0, d_1\rangle$ is the diagonal form $\langle c, 7c, d_0, d_1\rangle$
(over $\mathbb Q$, for $c \in \mathbb Q$ and $d : \{0,1\} \to \mathbb Q$). -/
theorem orthSum_iso_diag (c : ℚ) (d : Fin 2 → ℚ) :
    (QuadForm.orthSum (c • QuadForm.diag ![(1 : ℚ), 7]) (QuadForm.diag d)).IsometricIn ℚ
      (QuadForm.diag ![c, 7 * c, d 0, d 1]) := by
  refine ⟨1, by simp, fun x => ?_⟩
  rw [Matrix.one_mulVec, evalIn_orthSum_two, evalIn_smul_diag, QuadForm.evalIn_diag, QuadForm.evalIn_diag]
  simp [Fin.sum_univ_two, Fin.sum_univ_four]
  ring

/-- Helper: Serre's Hasse invariant takes the values $\pm 1$. -/
theorem hasseSerre_pm (v : RatPlace) {n : ℕ} (a : Fin n → ℚ) : v.hasseSerre a = 1 ∨ v.hasseSerre a = -1 :=
  Cassels.Ch6.ex9_hasse_pm v a

/-- Helper: necessary conditions for $c \in C$ (Example 3): if $f \cong c(x_0^2 + 7x_1^2) \perp g$ for a binary
form $g$, then $c \ne 0$ and $(c,-7)_p = -1$ at $p = 5$, $= 1$ at the other primes $p \equiv 1 \pmod 4$. -/
theorem ex3_necessary (c : ℚ) (g : QuadForm ℚ 2)
    (hg : (QuadForm.diag ![(42 : ℚ), -20, 15, -18]).IsometricIn ℚ
      (QuadForm.orthSum (c • QuadForm.diag ![(1 : ℚ), 7]) g)) :
    c ≠ 0 ∧ ∀ p : Nat.Primes, p.1 % 4 = 1 →
      (RatPlace.finite p).hilbert c (-7) = if p.1 = 5 then -1 else 1 := by
  obtain ⟨d, hd⟩ := Cassels.Ch6.exists_isometric_diag_any g
  have h4 := QuadForm.isometricIn_trans ℚ hg
    (QuadForm.isometricIn_trans ℚ (isometric_orthSum_right _ (QuadForm.diag d) g hd) (orthSum_iso_diag c d))
  obtain ⟨t, ht, hdet⟩ := sameSq_gen (K := ℚ) _ _ h4
  simp only [Fin.prod_univ_four, Rat.cast_id] at hdet
  simp at hdet
  have hrhs : t ^ 2 * (42 * 20 * 15 * 18) ≠ 0 := by
    have : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
    positivity
  have hc : c ≠ 0 := by
    rintro rfl; apply hrhs; rw [← hdet]; ring
  have hd0 : d 0 ≠ 0 := by
    intro h0; apply hrhs; rw [← hdet, h0]; ring
  have hd1 : d 1 ≠ 0 := by
    intro h0; apply hrhs; rw [← hdet, h0]; ring
  refine ⟨hc, fun p hp => ?_⟩
  have hs : 180 * t / c ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) ht) hc
  have hab : d 0 * d 1 = (180 * t / c) ^ 2 := by
    field_simp
    linear_combination (1 / 7 : ℚ) * hdet
  have hb : ∀ i, (![c, 7 * c, d 0, d 1] : Fin 4 → ℚ) i ≠ 0 := by
    intro i; fin_cases i <;> simp [hc, hd0, hd1]
  have hF : ∀ i, (![42, -20, 15, -18] : Fin 4 → ℚ) i ≠ 0 := by
    intro i; fin_cases i <;> simp
  have hloc : (RatPlace.finite p).atPlace
      (fun K _ _ => (QuadForm.diag ![(42 : ℚ), -20, 15, -18]).IsometricIn K
        (QuadForm.diag ![c, 7 * c, d 0, d 1])) := by
    have : Fact p.1.Prime := ⟨p.2⟩
    exact FieldGen.isometricIn_of_base ℚ_[p.1] h4
  have hh := RatPlace.hasseSerre_isometric (RatPlace.finite p) _ _ hF hb hloc
  rw [hasse_c7ab _ c (d 0) (d 1) _ hc hd0 hd1 hs hab, RatPlace.hilbert_comm _ (d 0) (-1),
    hilbert_neg_one_of_mod_four p hp, mul_one] at hh
  by_cases h5 : p.1 = 5
  · have : p = p5 := Subtype.ext h5
    subst this
    simp only [h5, ↓reduceIte]
    rw [← hh, eps5]
  · simp only [h5, ↓reduceIte]
    rw [← hh, eps_F_other p hp h5]

/-- Helper: sufficient conditions for $c \in C$ (Example 3): if $c \ne 0$ and $(c,-7)_p = -1$ at $p = 5$,
$= 1$ at the other primes $p \equiv 1 \pmod 4$, then $f \cong c(x_0^2 + 7x_1^2) \perp g$ for a binary form $g$
(namely $g = a\langle 1, 1\rangle$ with $a$ a rational number with $(a,-1)_v = \varepsilon_v(f)\,(c,-7)_v$ for all
places $v$, which exists by `exists_neg_one_symbols`). -/
theorem ex3_sufficient (c : ℚ) (hc : c ≠ 0)
    (hh : ∀ p : Nat.Primes, p.1 % 4 = 1 →
      (RatPlace.finite p).hilbert c (-7) = if p.1 = 5 then -1 else 1) :
    ∃ g : QuadForm ℚ 2, (QuadForm.diag ![(42 : ℚ), -20, 15, -18]).IsometricIn ℚ
      (QuadForm.orthSum (c • QuadForm.diag ![(1 : ℚ), 7]) g) := by
  have hF : ∀ i, (![42, -20, 15, -18] : Fin 4 → ℚ) i ≠ 0 := by
    intro i; fin_cases i <;> simp
  set η : RatPlace → ℤ := fun v => v.hasseSerre ![42, -20, 15, -18] * v.hilbert c (-7) with hηdef
  have hη : ∀ v, η v = 1 ∨ η v = -1 := fun v => by
    rcases hasseSerre_pm v ![(42 : ℚ), -20, 15, -18] with h1 | h1 <;>
      rcases RatPlace.hilbert_pm v c (-7) with h2 | h2 <;> simp [hηdef, h1, h2]
  obtain ⟨hF1, hF2⟩ := hasseSerre_product_formula ![(42 : ℚ), -20, 15, -18] hF
  obtain ⟨hH1, hH2⟩ := finprod_hilbert c (-7) hc (by norm_num)
  have hfin : Function.HasFiniteMulSupport η :=
    Set.Finite.subset (Set.Finite.union hF1 hH1) (Function.mulSupport_mul _ _)
  have hprod : ∏ᶠ v, η v = 1 := by
    simp only [hηdef]; rw [finprod_mul_distrib hF1 hH1, hF2, hH2]; rfl
  obtain ⟨hfin', hev⟩ := even_of_finprod η hη hfin hprod
  have hp : ∀ p : Nat.Primes, p.1 % 4 = 1 → η (RatPlace.finite p) = 1 := by
    intro p h4
    simp only [hηdef]
    rw [hh p h4]
    by_cases h5 : p.1 = 5
    · have : p = p5 := Subtype.ext h5
      subst this
      simp only [h5, ↓reduceIte]
      rw [eps5]; norm_num
    · simp only [h5, ↓reduceIte]
      rw [eps_F_other p h4 h5]; norm_num
  obtain ⟨a, ha0, ha⟩ := exists_neg_one_symbols η hη hfin' hev hp
  have hb : ∀ i, (![c, 7 * c, a, a] : Fin 4 → ℚ) i ≠ 0 := by
    intro i; fin_cases i <;> simp [hc, ha0]
  have hEps : ∀ v : RatPlace, v.hasseSerre ![c, 7 * c, a, a] = v.hasseSerre ![42, -20, 15, -18] := by
    intro v
    rw [hasse_c7ab v c a a a hc ha0 ha0 ha0 (by ring), RatPlace.hilbert_comm v a (-1), ha v]
    simp only [hηdef]
    rcases hasseSerre_pm v ![(42 : ℚ), -20, 15, -18] with h1 | h1 <;>
      rcases RatPlace.hilbert_pm v c (-7) with h2 | h2 <;> simp [h1, h2]
  have hiso : (QuadForm.diag ![(42 : ℚ), -20, 15, -18]).IsometricIn ℚ
      (QuadForm.diag ![c, 7 * c, a, a]) := by
    rw [isometric_iff_everywhere _ _ (QuadForm.nondegenerate_diag hF) (QuadForm.nondegenerate_diag hb)]
    intro v
    cases v with
    | infinite =>
      show (QuadForm.diag _).IsometricIn ℝ (QuadForm.diag _)
      refine isometricIn_real_of_negCount _ _ hF hb ?_
      have h1 := ha RatPlace.infinite
      simp only [hηdef, eps_F_infinite] at h1
      have e1 : RatPlace.infinite.hilbert (-1) a = if a < 0 then -1 else 1 := by
        rw [hilbert_infinite_eq _ _ (by norm_num) ha0]; by_cases h : a < 0 <;> simp [h]
      have e2 : RatPlace.infinite.hilbert c (-7) = if c < 0 then -1 else 1 := by
        rw [hilbert_infinite_eq _ _ hc (by norm_num)]; by_cases h : c < 0 <;> simp [h]
      rw [e1, e2] at h1
      rcases lt_or_gt_of_ne hc with hcn | hcp <;> rcases lt_or_gt_of_ne ha0 with han | hap
      · simp [hcn, han] at h1
      · have h7 : 7 * c < 0 := by linarith
        simp only [negCount, Fin.sum_univ_four]
        simp [hcn, h7, not_lt.2 hap.le, show ¬ ((42 : ℚ) < 0) by norm_num,
          show ¬ ((15 : ℚ) < 0) by norm_num]
      · have h7 : ¬ 7 * c < 0 := by linarith
        simp only [negCount, Fin.sum_univ_four]
        simp [not_lt.2 hcp.le, h7, han, show ¬ ((42 : ℚ) < 0) by norm_num,
          show ¬ ((15 : ℚ) < 0) by norm_num]
      · simp [not_lt.2 hcp.le, not_lt.2 hap.le] at h1
    | finite p =>
      have : Fact p.1.Prime := ⟨p.2⟩
      show (QuadForm.diag _).IsometricIn ℚ_[p.1] (QuadForm.diag _)
      rw [isometric_padic_iff p.1 _ _ hF hb]
      refine ⟨?_, ?_⟩
      · refine ⟨algebraMap ℚ ℚ_[p.1] (180 / (c * a)),
          (map_ne_zero _).2 (div_ne_zero (by norm_num) (mul_ne_zero hc ha0)), ?_⟩
        have hq : (∏ i, (![42, -20, 15, -18] : Fin 4 → ℚ) i) =
            (180 / (c * a)) ^ 2 * ∏ i, (![c, 7 * c, a, a] : Fin 4 → ℚ) i := by
          simp only [Fin.prod_univ_four]
          simp
          field_simp
          ring
        rw [hq]; simp
      · rw [← RatPlace.hasseSerre_finite p, ← RatPlace.hasseSerre_finite p]
        exact (hEps _).symm
  exact ⟨QuadForm.diag ![a, a],
    QuadForm.isometricIn_trans ℚ hiso (QuadForm.isometricIn_symm ℚ (orthSum_iso_diag c ![a, a]))⟩

end Ex3Ex5

end QuadFormsKB.Cassels.Ch6.Scan

namespace QuadFormsKB.Cassels.Ch6

open QuadFormsKB Matrix Scan

/-- **Cassels, Ch. 6, Example 1 (i)**: *determine which of the following forms are isotropic over $\mathbb Q$:
$x_1^2 + x_2^2 - 15(x_3^2 + x_4^2)$.* It is **anisotropic**: over $\mathbb Q_3$, where $-1$ is a non-square modulo $3$,
a primitive zero would give $x_0 \equiv x_1 \equiv 0 \pmod 3$ and then $x_2 \equiv x_3 \equiv 0$. (Here
$x_0, \dots, x_3$ are Cassels' $x_1, \dots, x_4$.) -/
@[kb "cassels1978" "Ch. 6, Ex. 1 (i), p. 99"]
theorem ex1_i : ¬ (QuadForm.diag ![(1 : ℚ), 1, -15, -15]).IsotropicIn ℚ := by
  intro h
  have h3 := (isotropic_everywhere_of_isotropic _ h) (RatPlace.finite ⟨3, Nat.prime_three⟩)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine not_isotropic_of_primitive 3 _ (fun z ⟨i, hi⟩ hz => ?_) h3
  rw [QuadForm.evalIn_diag] at hz
  simp [Fin.sum_univ_four] at hz
  have hz' : z 0 ^ 2 + z 1 ^ 2 + -(15 * z 2 ^ 2) + -(15 * z 3 ^ 2) = 0 :=
    PadicInt.coe_eq_zero.1 (by push_cast; exact hz)
  have h2 := congrArg (PadicInt.toZModPow 2) hz'
  simp only [map_add, map_neg, map_mul, map_pow, map_zero, map_ofNat] at h2
  have key : ∀ a b c d : ZMod (3 ^ 2), (a.val.Coprime (3 ^ 2) ∨ b.val.Coprime (3 ^ 2) ∨
      c.val.Coprime (3 ^ 2) ∨ d.val.Coprime (3 ^ 2)) →
      a ^ 2 + b ^ 2 + -(15 * c ^ 2) + -(15 * d ^ 2) ≠ 0 := by decide
  refine key _ _ _ _ ?_ h2
  have hc := coprime_of_isUnit 3 2 hi
  fin_cases i
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr (Or.inl hc))
  · exact Or.inr (Or.inr (Or.inr hc))

/-- **Cassels, Ch. 6, Example 1 (ii)**: *$3x_1^2 + 2x_2^2 - 7x_3^2$ is isotropic over $\mathbb Q$ or not*: it is
**anisotropic** (no primitive $3$-adic zero: modulo $3$ the equation forces $x_1 \equiv x_2 \equiv x_0$-type
congruences, and modulo $9$ it has no primitive solution). -/
@[kb "cassels1978" "Ch. 6, Ex. 1 (ii), p. 99"]
theorem ex1_ii : ¬ (QuadForm.diag ![(3 : ℚ), 2, -7]).IsotropicIn ℚ := by
  intro h
  have h3 := (isotropic_everywhere_of_isotropic _ h) (RatPlace.finite ⟨3, Nat.prime_three⟩)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine not_isotropic_of_primitive 3 _ (fun z ⟨i, hi⟩ hz => ?_) h3
  rw [QuadForm.evalIn_diag] at hz
  simp [Fin.sum_univ_three] at hz
  have hz' : 3 * z 0 ^ 2 + 2 * z 1 ^ 2 + -(7 * z 2 ^ 2) = 0 :=
    PadicInt.coe_eq_zero.1 (by push_cast; exact hz)
  have h2 := congrArg (PadicInt.toZModPow 2) hz'
  simp only [map_add, map_neg, map_mul, map_pow, map_zero, map_ofNat] at h2
  have key : ∀ a b c : ZMod (3 ^ 2), (a.val.Coprime (3 ^ 2) ∨ b.val.Coprime (3 ^ 2) ∨
      c.val.Coprime (3 ^ 2)) → 3 * a ^ 2 + 2 * b ^ 2 + -(7 * c ^ 2) ≠ 0 := by decide
  refine key _ _ _ ?_ h2
  have hc := coprime_of_isUnit 3 2 hi
  fin_cases i
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr hc)

/-- **Cassels, Ch. 6, Example 1 (iii)**: *$3x_1^2 + 2x_2^2 - 11x_3^2$ is isotropic over $\mathbb Q$*: it has the
nontrivial zero $(39, 34, 25)$ ($3 \cdot 39^2 + 2 \cdot 34^2 = 6875 = 11 \cdot 25^2$). -/
@[kb "cassels1978" "Ch. 6, Ex. 1 (iii), p. 99"]
theorem ex1_iii : (QuadForm.diag ![(3 : ℚ), 2, -11]).IsotropicIn ℚ := by
  refine ⟨![39, 34, 25], fun h => by simpa using congrFun h 0, ?_⟩
  rw [QuadForm.evalIn_diag]
  simp [Fin.sum_univ_three]
  norm_num

/-- **Cassels, Ch. 6, Example 1 (iv)**: *$3x_1^2 + 2x_2^2 - 7x_3^2 + 2x_2x_3 + 2x_3x_1 + 2x_1x_2$ is isotropic
over $\mathbb Q$ or not*: it is **anisotropic** (no primitive $2$-adic zero modulo $8$). The form is
`QuadForm.ofUpper` with coefficients $c_{00} = 3$, $c_{11} = 2$, $c_{22} = -7$, $c_{01} = c_{02} = c_{12} = 2$ (in
the variables $x_0, x_1, x_2$). -/
@[kb "cassels1978" "Ch. 6, Ex. 1 (iv), p. 99"]
theorem ex1_iv : ¬ (QuadForm.ofUpper ![![(3 : ℚ), 2, 2], ![0, 2, 2], ![0, 0, -7]]).IsotropicIn ℚ := by
  intro h
  have h3 := (isotropic_everywhere_of_isotropic _ h) (RatPlace.finite ⟨2, Nat.prime_two⟩)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine not_isotropic_of_primitive 2 _ (fun z ⟨i, hi⟩ hz => ?_) h3
  simp [QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_three] at hz
  have hz' : 3 * z 0 * z 0 + 2 * z 0 * z 1 + 2 * z 0 * z 2 + (2 * z 1 * z 1 + 2 * z 1 * z 2) +
      -(7 * z 2 * z 2) = 0 := PadicInt.coe_eq_zero.1 (by push_cast; exact hz)
  have h2 := congrArg (PadicInt.toZModPow 3) hz'
  simp only [map_add, map_neg, map_mul, map_pow, map_zero, map_ofNat] at h2
  have key : ∀ a b c : ZMod (2 ^ 3), (a.val.Coprime (2 ^ 3) ∨ b.val.Coprime (2 ^ 3) ∨
      c.val.Coprime (2 ^ 3)) →
      3 * a * a + 2 * a * b + 2 * a * c + (2 * b * b + 2 * b * c) + -(7 * c * c) ≠ 0 := by decide
  refine key _ _ _ ?_ h2
  have hc := coprime_of_isUnit 2 3 hi
  fin_cases i
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr hc)

/-- **Cassels, Ch. 6, Example 2 (i)**: *determine whether $x_1^2 - 15x_2^2$ and $3x_1^2 - 5x_2^2$ are equivalent
over $\mathbb Q$*: they are **not**. Both have determinant $-15$, but $3x_1^2 - 5x_2^2$ represents $3$ while
$x_0^2 - 15x_1^2 = 3$ has no solution over $\mathbb Q_5$ (it would give a primitive zero of
$x_0^2 - 15x_1^2 - 3x_2^2$, impossible modulo $25$). -/
@[kb "cassels1978" "Ch. 6, Ex. 2 (i), p. 100"]
theorem ex2_i : ¬ (QuadForm.diag ![(1 : ℚ), -15]).IsometricIn ℚ (QuadForm.diag ![(3 : ℚ), -5]) := by
  intro h
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 := FieldGen.isometricIn_of_base ℚ_[5] h
  have hr : (QuadForm.diag ![(1 : ℚ), -15]).RepresentsIn ℚ_[5] 3 :=
    QuadForm.representsIn_of_isometricIn ℚ_[5] h5 ⟨![1, 0], by
      rw [QuadForm.evalIn_diag]; simp [Fin.sum_univ_two]⟩
  obtain ⟨y, hy⟩ := hr
  rw [QuadForm.evalIn_diag] at hy
  simp [Fin.sum_univ_two] at hy
  have hiso : (QuadForm.diag ![(1 : ℚ), -15, -3]).IsotropicIn ℚ_[5] := by
    refine ⟨![y 0, y 1, 1], fun h0 => by simpa using congrFun h0 2, ?_⟩
    rw [QuadForm.evalIn_diag]
    simp [Fin.sum_univ_three]
    linear_combination hy
  refine not_isotropic_of_primitive 5 _ (fun z ⟨i, hi⟩ hz => ?_) hiso
  rw [QuadForm.evalIn_diag] at hz
  simp [Fin.sum_univ_three] at hz
  have hz' : z 0 ^ 2 + -(15 * z 1 ^ 2) + -(3 * z 2 ^ 2) = 0 :=
    PadicInt.coe_eq_zero.1 (by push_cast; exact hz)
  have h2 := congrArg (PadicInt.toZModPow 2) hz'
  simp only [map_add, map_neg, map_mul, map_pow, map_zero, map_ofNat] at h2
  have key : ∀ a b c : ZMod (5 ^ 2), (a.val.Coprime (5 ^ 2) ∨ b.val.Coprime (5 ^ 2) ∨
      c.val.Coprime (5 ^ 2)) → a ^ 2 + -(15 * b ^ 2) + -(3 * c ^ 2) ≠ 0 := by decide
  refine key _ _ _ ?_ h2
  have hc := coprime_of_isUnit 5 2 hi
  fin_cases i
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr hc)

/-- **Cassels, Ch. 6, Example 2 (iii)**: *$x_1^2 + x_2^2 + 16x_3^2$ and $2x_1^2 + 2x_2^2 + 5x_3^2 - 2x_2x_3 -
2x_1x_3$ are equivalent over $\mathbb Q$, with an explicit equivalence*: the substitution
$P = \begin{pmatrix} 1 & 1 & -1 \\ 1 & -1 & 0 \\ 0 & 0 & \tfrac12 \end{pmatrix}$ ($\det P = -1$) takes the first form
to the second. The second form is `QuadForm.ofUpper` with $c_{00} = c_{11} = 2$, $c_{22} = 5$, $c_{12} = c_{02} = -2$,
$c_{01} = 0$ (variables $x_0, x_1, x_2$). -/
@[kb "cassels1978" "Ch. 6, Ex. 2 (iii), p. 100"]
theorem ex2_iii :
    (QuadForm.diag ![(1 : ℚ), 1, 16]).IsometricIn ℚ
        (QuadForm.ofUpper ![![(2 : ℚ), 0, -2], ![0, 2, -2], ![0, 0, 5]]) ∧
      ∀ x : Fin 3 → ℚ, (QuadForm.diag ![(1 : ℚ), 1, 16]).eval (!![1, 1, -1; 1, -1, 0; 0, 0, 1 / 2] *ᵥ x) =
        (QuadForm.ofUpper ![![(2 : ℚ), 0, -2], ![0, 2, -2], ![0, 0, 5]]).eval x := by
  have key : ∀ x : Fin 3 → ℚ, (QuadForm.diag ![(1 : ℚ), 1, 16]).eval (!![1, 1, -1; 1, -1, 0; 0, 0, 1 / 2] *ᵥ x) =
      (QuadForm.ofUpper ![![(2 : ℚ), 0, -2], ![0, 2, -2], ![0, 0, 5]]).eval x := by
    intro x
    unfold QuadForm.eval
    rw [QuadForm.evalIn_diag]
    simp [QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_three, Matrix.mulVec, dotProduct]
    ring
  refine ⟨⟨!![1, 1, -1; 1, -1, 0; 0, 0, 1 / 2], ?_, key⟩, key⟩
  rw [Matrix.det_fin_three]
  simp
  norm_num

/-- Helper: every positive rational is a sum of four squares of rationals (Lagrange's four-square theorem applied to
$mn$ for $b = m/n$, divided by $n^2$). -/
theorem exists_sum_four_sq_rat (b : ℚ) (hb : 0 < b) : ∃ a c d e : ℚ, a ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 = b := by
  obtain ⟨w0, w1, w2, w3, h⟩ := Nat.sum_four_squares (b.num.toNat * b.den)
  have hn : (b.num.toNat : ℤ) = b.num := Int.toNat_of_nonneg (Rat.num_nonneg.2 hb.le)
  have hq : ((b.num.toNat * b.den : ℕ) : ℚ) = b.num * b.den := by
    rw [Nat.cast_mul]
    congr 1
    exact_mod_cast hn
  have hd : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_nz
  refine ⟨w0 / b.den, w1 / b.den, w2 / b.den, w3 / b.den, ?_⟩
  have h' : ((w0 : ℚ) ^ 2 + w1 ^ 2 + w2 ^ 2 + w3 ^ 2) = b.num * b.den := by
    rw [← hq, ← h]; push_cast; ring
  have hbd : b * b.den = b.num := Rat.mul_den_eq_num b
  field_simp
  rw [h']
  linear_combination (-(b.den : ℚ)) * hbd

/-- Helper: the matrix of left multiplication by the quaternion $a + b\mathrm i + c\mathrm j + d\mathrm k$ in the basis
$1, \mathrm i, \mathrm j, \mathrm k$. Its transpose times itself is $(a^2 + b^2 + c^2 + d^2)$ times the identity
(Euler's four-square identity). -/
def quatMat (a b c d : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![a, -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a]

/-- Helper: $\mathrm{quatMat}(a,b,c,d)^{t}\,\mathrm{quatMat}(a,b,c,d) = (a^2 + b^2 + c^2 + d^2) I$. -/
theorem quatMat_transpose_mul (a b c d : ℚ) :
    (quatMat a b c d)ᵀ * quatMat a b c d = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • (1 : Matrix (Fin 4) (Fin 4) ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatMat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, Matrix.one_apply] <;> ring

/-- **Cassels, Ch. 6, Example 4**: *show that $x_1^2 + x_2^2 + x_3^2 + x_4^2$ and $b(x_1^2 + x_2^2 + x_3^2 + x_4^2)$
are rationally equivalent for every rational $b > 0$.* Proof: write $b = a^2 + c^2 + d^2 + e^2$ with rational
$a, c, d, e$ (Lagrange); left multiplication by the quaternion $a + c\mathrm i + d\mathrm j + e\mathrm k$ multiplies the
sum of four squares by $b$ (Euler's identity) and has determinant $b^2 \ne 0$. (Cassels' hint is to use the
local-global principle and the example of Chapter 4, Ex. 3; this explicit equivalence is an alternative proof.) -/
@[kb "cassels1978" "Ch. 6, Ex. 4, p. 100"]
theorem ex4 (b : ℚ) (hb : 0 < b) :
    (QuadForm.diag ![(1 : ℚ), 1, 1, 1]).IsometricIn ℚ (QuadForm.diag ![b, b, b, b]) := by
  obtain ⟨a, c, d, e, hs⟩ := exists_sum_four_sq_rat b hb
  refine ⟨quatMat a c d e, ?_, fun x => ?_⟩
  · have h := congrArg Matrix.det (quatMat_transpose_mul a c d e)
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one, mul_one, hs] at h
    simp only [Fintype.card_fin] at h
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, mul_zero] at h
    exact (pow_ne_zero 4 hb.ne') h.symm
  · rw [QuadForm.evalIn_diag, QuadForm.evalIn_diag]
    simp [Fin.sum_univ_four, Matrix.mulVec, dotProduct, quatMat]
    rw [← hs]
    ring

/-- **The set $C$ of Cassels, Ch. 6, Example 3**: the rationals $c$ such that
$42x_0^2 - 20x_1^2 + 15x_2^2 - 18x_3^2$ is equivalent over $\mathbb Q$ to
$c\,(x_0^2 + 7x_1^2) + g(x_2, x_3)$ for some binary rational form $g$ (depending on $c$). Here $g$ is an
arbitrary binary form `g : QuadForm ℚ 2` (it is forced to be regular), the sum is the orthogonal sum
`QuadForm.orthSum` ($x_0, x_1$ in the first summand, $x_2, x_3$ in the second; Cassels' variables
$x_1, \dots, x_4$ are $x_0, \dots, x_3$ here), and `c • Q` is the form $c\,Q$. -/
def ex3C : Set ℚ :=
  {c | ∃ g : QuadForm ℚ 2, (QuadForm.diag ![(42 : ℚ), -20, 15, -18]).IsometricIn ℚ
    (QuadForm.orthSum (c • QuadForm.diag ![(1 : ℚ), 7]) g)}

/-- **Cassels, Ch. 6, Example 3 (complete description of $C$)**: $c \in C$ iff $c \ne 0$ and, for every prime
$p \equiv 1 \pmod 4$, the Hilbert symbol $(c, -7)_p$ equals $-1$ at $p = 5$ and $1$ at every other such $p$.
(Equivalently, $c$ is a local norm from $\mathbb Q_p(\sqrt{-7})$ at every prime $p \equiv 1 \pmod 4$ except
$5$, where it is not a norm; there is no condition at $2$, at the primes $p \equiv 3 \pmod 4$ or at
$\infty$.) *Proof.* The determinant of $f$ is $7$ modulo squares, so $f \cong \langle c, 7c\rangle \perp g$
forces $g \cong \langle a, b\rangle$ with $ab$ a square, i.e. $g \cong a\langle 1, 1\rangle$ (Witt cancellation
and the classification of rational forms by the local invariants); comparing the Hasse invariants
$\varepsilon_v(f)$ and $(c,-7)_v\,(a,-1)_v$ leaves a condition only where $-1$ is a square (primes
$p \equiv 1 \pmod 4$), where $(a,-1)_p = 1$, and $\varepsilon_p(f) = -1$ exactly at $p = 5$ among these
primes. Conversely the prescribed values $(a,-1)_v = \varepsilon_v(f)\,(c,-7)_v$ are realized by a rational $a$
(Serre III, Thm. 4: rationals with prescribed Hilbert symbols), and the local-global principle for equivalence
(`isometric_iff_everywhere`) gives $f \cong \langle c, 7c, a, a\rangle$. -/
@[kb "cassels1978" "Ch. 6, Ex. 3, p. 100 (description of C)"]
theorem ex3_description :
    ex3C = {c : ℚ | c ≠ 0 ∧ ∀ p : Nat.Primes, p.1 % 4 = 1 →
      (RatPlace.finite p).hilbert c (-7) = if p.1 = 5 then -1 else 1} := by
  ext c
  constructor
  · rintro ⟨g, hg⟩
    exact ex3_necessary c g hg
  · rintro ⟨hc, hh⟩
    exact ex3_sufficient c hc hh

/-- **Cassels, Ch. 6, Example 3 (the subgroup claim)**: with $b = 5$ the set $bC = \{bc : c \in C\}$ is a subgroup
of $\mathbb Q^\times$, namely the group of $u \in \mathbb Q^\times$ with $(u, -7)_p = 1$ for all primes
$p \equiv 1 \pmod 4$. Stated as: there are $b \in \mathbb Q^\times$ and a subgroup $H$ of $\mathbb Q^\times$ whose
underlying set of rationals is $bC$. -/
@[kb "cassels1978" "Ch. 6, Ex. 3, p. 100 (bC is a subgroup)"]
theorem ex3_subgroup : ∃ (b : ℚˣ) (H : Subgroup ℚˣ),
    {x : ℚ | ∃ c ∈ ex3C, x = (b : ℚ) * c} = {x : ℚ | ∃ u ∈ H, (u : ℚ) = x} := by
  let H : Subgroup ℚˣ :=
    { carrier := {u | ∀ p : Nat.Primes, p.1 % 4 = 1 → (RatPlace.finite p).hilbert (u : ℚ) (-7) = 1}
      mul_mem' := fun {u w} hu hw p h4 => by
        rw [Units.val_mul, HilbertLocal.RatPlace.hilbert_mul_left _ _ _ _ u.ne_zero w.ne_zero (by norm_num),
          hu p h4, hw p h4]
        norm_num
      one_mem' := fun p _ => by simpa using hilbert_one_left (RatPlace.finite p) (-7)
      inv_mem' := fun {u} hu p h4 => by
        have h := HilbertLocal.RatPlace.hilbert_mul_left (RatPlace.finite p) (u : ℚ) ((u⁻¹ : ℚˣ) : ℚ) (-7)
          u.ne_zero (u⁻¹).ne_zero (by norm_num)
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, hilbert_one_left, hu p h4] at h
        rw [one_mul] at h
        exact h.symm }
  refine ⟨Units.mk0 5 (by norm_num), H, ?_⟩
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [ex3_description] at hc
    obtain ⟨hc0, hcp⟩ := hc
    refine ⟨Units.mk0 (5 * c) (mul_ne_zero (by norm_num) hc0), fun p h4 => ?_, rfl⟩
    show (RatPlace.finite p).hilbert (5 * c) (-7) = 1
    rw [HilbertLocal.RatPlace.hilbert_mul_left _ _ _ _ (by norm_num) hc0 (by norm_num),
      hilbert_five_neg_seven p h4, hcp p h4]
    split_ifs <;> norm_num
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w : ℚ, w = (u : ℚ) / 5 := ⟨_, rfl⟩
    have hw0 : w ≠ 0 := by rw [hw]; exact div_ne_zero u.ne_zero (by norm_num)
    have hu5 : (u : ℚ) = 5 * w := by rw [hw]; ring
    refine ⟨w, ?_, by simp [hu5]⟩
    rw [ex3_description]
    refine ⟨hw0, fun p h4 => ?_⟩
    have h := hu p h4
    rw [hu5, HilbertLocal.RatPlace.hilbert_mul_left _ _ _ _ (by norm_num) hw0 (by norm_num),
      hilbert_five_neg_seven p h4] at h
    rcases RatPlace.hilbert_pm (RatPlace.finite p) w (-7) with h' | h' <;> rw [h'] at h ⊢ <;>
      split_ifs at h ⊢ <;> simp_all

/-- **Cassels, Ch. 6, Example 3 (a member of $C$)**: $5 \in C$, i.e. $f$ is equivalent over $\mathbb Q$ to
$5(x_0^2 + 7x_1^2) + g(x_2, x_3)$ for some binary rational form $g$. -/
@[kb "cassels1978" "Ch. 6, Ex. 3, p. 100 (5 lies in C)"]
theorem ex3_five_mem : (5 : ℚ) ∈ ex3C := by
  rw [ex3_description]
  exact ⟨by norm_num, fun p h4 => hilbert_five_neg_seven p h4⟩

/-- Helper for Example 5: the two forms are equivalent over $\mathbb Q$ when $m > -1$ and $m \ne 0$ (equal
determinants up to the square $(m+1)^2$, all Hasse invariants equal to $1$, same signature). -/
theorem ex5_pos (m : ℚ) (hm : -1 < m) (hm0 : m ≠ 0) :
    (QuadForm.diag ![m + 1, m + 1, m + 1, m]).IsometricIn ℚ (QuadForm.diag ![1, 1, 1, m * (m + 1)]) := by
  have hu : 0 < m + 1 := by linarith
  have hu0 : m + 1 ≠ 0 := hu.ne'
  have ha : ∀ i, (![m + 1, m + 1, m + 1, m] : Fin 4 → ℚ) i ≠ 0 := by
    intro i; fin_cases i <;> simp [hu0, hm0]
  have hb : ∀ i, (![1, 1, 1, m * (m + 1)] : Fin 4 → ℚ) i ≠ 0 := by
    intro i; fin_cases i <;> simp [hu0, hm0]
  rw [isometric_iff_everywhere _ _ (QuadForm.nondegenerate_diag ha) (QuadForm.nondegenerate_diag hb)]
  have hdet : ∀ (K : Type) [Field K] [CharZero K], ∃ t : K, t ≠ 0 ∧
      algebraMap ℚ K (∏ i, (![m + 1, m + 1, m + 1, m] : Fin 4 → ℚ) i) =
        t ^ 2 * algebraMap ℚ K (∏ i, (![1, 1, 1, m * (m + 1)] : Fin 4 → ℚ) i) := by
    intro K _ _
    refine ⟨algebraMap ℚ K (m + 1), (map_ne_zero _).2 hu0, ?_⟩
    simp only [Fin.prod_univ_four]
    simp
    ring
  have hasse : ∀ v : RatPlace, v.hasseSerre ![m + 1, m + 1, m + 1, m] = 1 ∧
      v.hasseSerre ![1, 1, 1, m * (m + 1)] = 1 := by
    intro v
    constructor
    · have h1 := hilbert_succ_neg v m
      have h2 : v.hilbert (m + 1) (m + 1) * v.hilbert (m + 1) m = 1 := by
        rw [RatPlace.hilbert_self v _ hu0, ← RatPlace.hilbert_mul_right v _ (-1) m hu0 (by norm_num) hm0]
        simpa using h1
      simp only [RatPlace.hasseSerre, Fin.prod_univ_four]
      simp
      rcases RatPlace.hilbert_pm v (m + 1) (m + 1) with e1 | e1 <;>
        rcases RatPlace.hilbert_pm v (m + 1) m with e2 | e2 <;> simp_all
    · simp only [RatPlace.hasseSerre, Fin.prod_univ_four]
      simp [hilbert_one_left, hilbert_one_right]
  intro v
  cases v with
  | infinite =>
    refine isometricIn_real_of_negCount _ _ ha hb ?_
    by_cases hpos : 0 < m
    · have : 0 < m * (m + 1) := mul_pos hpos hu
      simp only [negCount, Fin.sum_univ_four]
      simp [not_lt.2 hu.le, not_lt.2 hpos.le, not_lt.2 this.le, show ¬ ((1 : ℚ) < 0) by norm_num]
    · have hneg : m < 0 := lt_of_le_of_ne (not_lt.1 hpos) hm0
      have : m * (m + 1) < 0 := mul_neg_of_neg_of_pos hneg hu
      simp only [negCount, Fin.sum_univ_four]
      simp [not_lt.2 hu.le, hneg, this, show ¬ ((1 : ℚ) < 0) by norm_num]
  | finite p =>
    have : Fact p.1.Prime := ⟨p.2⟩
    show (QuadForm.diag _).IsometricIn ℚ_[p.1] (QuadForm.diag _)
    rw [isometric_padic_iff p.1 _ _ ha hb]
    refine ⟨?_, ?_⟩
    · exact hdet ℚ_[p.1]
    · rw [← RatPlace.hasseSerre_finite p, ← RatPlace.hasseSerre_finite p, (hasse _).1, (hasse _).2]

/-- **Cassels, Ch. 6, Example 5**: *for what rational $m$ are $(m+1)(x_0^2 + x_1^2 + x_2^2) + m x_3^2$ and
$x_0^2 + x_1^2 + x_2^2 + m(m+1)x_3^2$ equivalent over $\mathbb Q$?* Exactly when $m > -1$. (For $m = 0$ both forms
are $x_0^2 + x_1^2 + x_2^2$; for $m \le -1$ the first form is negative semidefinite while the second represents
$1$; for $m > -1$, $m \ne 0$, see `ex5_pos`.) The forms may be degenerate ($m = 0$), so no regularity is assumed. -/
@[kb "cassels1978" "Ch. 6, Ex. 5, p. 100"]
theorem ex5 (m : ℚ) :
    (QuadForm.diag ![m + 1, m + 1, m + 1, m]).IsometricIn ℚ (QuadForm.diag ![1, 1, 1, m * (m + 1)]) ↔
      -1 < m := by
  constructor
  · intro h
    by_contra hm
    push Not at hm
    obtain ⟨P, -, hP⟩ := h
    have h1 := hP (![1, 0, 0, 0] : Fin 4 → ℚ)
    rw [QuadForm.evalIn_diag, QuadForm.evalIn_diag] at h1
    simp [Fin.sum_univ_four] at h1
    nlinarith [sq_nonneg ((P *ᵥ (![1, 0, 0, 0] : Fin 4 → ℚ)) 0), sq_nonneg ((P *ᵥ (![1, 0, 0, 0] : Fin 4 → ℚ)) 1),
      sq_nonneg ((P *ᵥ (![1, 0, 0, 0] : Fin 4 → ℚ)) 2), sq_nonneg ((P *ᵥ (![1, 0, 0, 0] : Fin 4 → ℚ)) 3)]
  · intro hm
    by_cases hm0 : m = 0
    · subst hm0
      have : (![(0 : ℚ) + 1, 0 + 1, 0 + 1, 0] : Fin 4 → ℚ) = ![1, 1, 1, 0 * (0 + 1)] := by
        ext i; fin_cases i <;> simp
      rw [this]
      exact QuadForm.isometricIn_refl ℚ _
    · exact ex5_pos m hm hm0

end QuadFormsKB.Cassels.Ch6
