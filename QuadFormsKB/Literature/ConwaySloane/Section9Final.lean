/-
# Conway–Sloane, Ch. 15, §9.7: Theorems 19, 20 (c), (d), 21

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.7, pp. 393–395
(`conwaysloane1999`).

**Layer.** As in `Section9Theorems.lean` and `Section9Main.lean`: a form is its symmetric integer Gram matrix $A$,
$d = \det A$, `csQ A` the rational form, $\Lambda = \mathbb Z^n$, $P$ a finite set of primes containing those dividing
$2d$; the $2$-adic inputs are the local determinant bounds of `Section9DyadicPatterns.lean`.

**Proves**
* **Theorem 20 (c)** (`theorem20c`, (41)): if $2$ is intractable, $4^{\binom n2} \mid 4^{[n/2]}d$.
* `theorem21_small`: Theorem 21 for $n \le 2$ (for $n \le 1$ no form is indefinite; for $n = 2$, $d \ne -1$ by
  `not_moreThanOneClass_of_det_eq_neg_one`, so a prime $p \mid d$ gives $k = 4p$).
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Main
import QuadFormsKB.Literature.ConwaySloane.Section9DyadicPatterns
import QuadFormsKB.Literature.ConwaySloane.Section9Binary

open NumberField IsDedekindDomain WithZero Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

variable {n : ℕ}

/-- From a $2$-adic bound on $\det H$ of $\mathbb Z_2^n$ ($\det H = 2^n\det A$) to $2^m \mid \det A$. -/
theorem two_pow_dvd_det_of_valued {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : primeOf v = 2) (m : ℕ)
    (h : Valued.v (locGram (csQ A) v 1).det ≤ exp (-((m + n : ℕ) : ℤ))) : (2 : ℤ) ^ m ∣ A.det := by
  rw [locGram_one_int_det, valued_intCast_le_iff, hessian_det_csForm hA] at h
  have h' : ((primeOf v : ℕ) : ℤ) = 2 := by rw [hv]; norm_num
  rw [show ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) = 2 from h', pow_add, mul_comm] at h
  exact (mul_dvd_mul_iff_left (pow_ne_zero n two_ne_zero)).mp h

theorem div_two_le_choose_two (n : ℕ) : n / 2 ≤ n.choose 2 := by
  rw [Nat.choose_two_right]
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · apply Nat.div_le_div_right
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    nlinarith

/-- `4^{[n/2]} · 2^{2C - 2[n/2]} = 4^C`. -/
theorem four_pow_choose_eq (n : ℕ) :
    (4 : ℤ) ^ n.choose 2 = 4 ^ (n / 2) * 2 ^ (2 * n.choose 2 - 2 * (n / 2)) := by
  have h := div_two_le_choose_two n
  rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, ← pow_add]
  congr 1; omega

/-- `4^{[n/2]} · 2^{3C - 2[n/2]} = 8^C`. -/
theorem eight_pow_choose_eq (n : ℕ) :
    (8 : ℤ) ^ n.choose 2 = 4 ^ (n / 2) * 2 ^ (3 * n.choose 2 - 2 * (n / 2)) := by
  have h := div_two_le_choose_two n
  rw [show (8 : ℤ) = 2 ^ 3 by norm_num, show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, ← pow_add]
  congr 1; omega

/-- **Conway–Sloane, Theorem 20 (c)** (§9.7, p. 394, (41)): *if $2$ is an intractable prime then $4^{[n/2]}d$ is
divisible by $4^{\binom n2}$.* Here "intractable" is `IsTractable` for the place of $2$ in $P$; Conway–Sloane assume
$f$ indefinite, which is not needed. *Proof* (the book's, via the algorithm of §9.5): an intractable $2$ has a
non-automorphous unit, so the form is $2$-adically diagonal and no three powers of $2$ in the diagonal lie in a range
$2^t, \dots, 2^{t+3}$; the explicit root vectors are in `Section9DyadicPatterns.lean`
(`valued_det_le_of_not_units_mem_two_cs`). -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, Thm. 20 (c), (41), p. 394"]
theorem theorem20c {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hd : A.det ≠ 0)
    (P : Finset (HeightOneSpectrum (𝓞 ℚ))) (p : P) (hp2 : primeOf p.1 = 2)
    (hnt : ¬ IsTractable (csQ A) (csQ_nondegenerate hA hd) stdLat P p) :
    (4 : ℤ) ^ n.choose 2 ∣ 4 ^ (n / 2) * A.det := by
  have h2 : (2 : 𝓞 ℚ) ∈ p.1.asIdeal := (two_mem_iff_natGenerator p.1).mpr hp2
  have hdet := valued_det_le_of_not_units_mem_two_cs (csQ_nondegenerate hA hd) h2 stdLat
    (by convert hint_std (Cassels.Ch8Ex2.gramForm A) p.1)
    (not_units_mem_of_not_isTractable hnt) 1 (loc_std_eq_locAct_one p.1)
  have := two_pow_dvd_det_of_valued hA hp2 _ hdet
  rw [four_pow_choose_eq]
  exact mul_dvd_mul_left _ this

/-- **Theorem 21 for $n \le 2$** (Conway–Sloane, proof of Thm. 21, p. 395: "If the dimension is 2 the assertion is
trivial. For certainly $d \ne \pm1$, or else there is only one class in the genus. Therefore some prime $p \ge 2$ divides
$d$, and (43) holds with $k = 4p$"). For $n \le 1$ no nonsingular form is indefinite. -/
theorem theorem21_small (hn : n ≤ 2) {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hd : A.det ≠ 0)
    (hind : IsIndefinite (csQ A)) (h : MoreThanOneClass A) :
    ∃ k : ℕ, ¬ IsSquare k ∧ (k % 4 = 0 ∨ k % 4 = 1) ∧ (k : ℤ) ^ (n.choose 2) ∣ 4 ^ (n / 2) * A.det := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · exact absurd hind (not_isIndefinite_of_le_one (by omega) A hd)
  obtain rfl : n = 2 := le_antisymm hn h2
  have hneg := det_neg_of_isIndefinite A hA hd hind
  have hne1 : A.det ≠ -1 := fun e => not_moreThanOneClass_of_det_eq_neg_one A hA e h
  have habs : A.det.natAbs ≠ 1 := by omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd habs
  refine ⟨4 * p, not_isSquare_four_mul_prime hp, Or.inl (Nat.mul_mod_right 4 _), ?_⟩
  have hpd' : (p : ℤ) ∣ A.det := Int.natCast_dvd.mpr hpd
  simp only [Nat.choose_self, pow_one, show (2 : ℕ) / 2 = 1 from rfl]
  push_cast
  exact mul_dvd_mul_left 4 hpd'

end QuadFormsKB.ConwaySloane
