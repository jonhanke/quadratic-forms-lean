/-
# Moreno–Wagstaff 2005, Remark 6.5: the singular series $\rho_{2k}(n)$ for even $k$, and $\rho_8$

**Source.** C. J. Moreno and S. S. Wagstaff Jr., *Sums of Squares of Integers* (2005), Remark 6.5, (6.23), p. 196
(printed page), and (6.4), p. 186.

* `Remark65Even` (stated): for even $k \ge 4$ and $n \ge 1$,
  $$\rho_{2k}(n) = \frac{2k}{(2^k - 1)\,|B_k|}\sum_{d \mid n} d^{k-1}(-1)^{(d + k/2)(n/d - 1)},$$
  with $B_k$ the Bernoulli number (Mathlib's `bernoulli`; for even $k$ it agrees with the book's convention $B_1 = +\frac12$
  of Remark 6.2, which only affects $B_1$). The machine-read text of the book drops the exponent in $2^k - 1$; the
  printed page has $2^k - 1$ (checked on the scan). Stated for $k \ge 4$, where $\rho_{2k}$ is an absolutely convergent
  series (`summable_ssTerm_sumSq`).
* `remark65_eight` (proved, unconditional): the case $k = 4$, $\rho_8(n) = 16\sum_{d \mid n} d^3(-1)^{(d+2)(n/d-1)}$,
  from $r_8 = \rho_8$ (`theorem61_small`) and Jacobi's formula (6.4) (`repNum_sumSq_eight`).
* `remark65Even_four`: the instance $k = 4$ of `Remark65Even`.

The general even case (Theorem 6.3) needs the evaluation of the dyadic factor (Lemmas 6.3, 6.5) and is not proved.
-/
import QuadFormsKB.Literature.MorenoWagstaff.Wave2.Hardy
import QuadFormsKB.Literature.MorenoWagstaff.Wave2.EightSquares
import Mathlib.NumberTheory.Bernoulli

namespace QuadFormsKB.MorenoWagstaff

open QuadFormsKB.Siegel

/-- **Moreno–Wagstaff, Remark 6.5, (6.23)** (p. 196), for even $k \ge 4$ and every $n \ge 1$:
$\rho_{2k}(n) = \dfrac{2k}{(2^k - 1)|B_k|}\sum_{d \mid n} d^{k-1}(-1)^{(d + k/2)(n/d - 1)}$, where $\rho_s$ is
`singularSeriesSq` and $B_k$ = `bernoulli k`. Stated; proved for $k = 4$ (`remark65Even_four`). -/
@[kb "morenowagstaff2005" "Remark 6.5, (6.23), p. 196"]
def Remark65Even : Prop :=
  ∀ k n : ℕ, Even k → 4 ≤ k → 0 < n →
    singularSeriesSq (2 * k) n =
      (2 * k : ℂ) / ((2 ^ k - 1) * |(bernoulli k : ℝ)|) *
        ∑ d ∈ n.divisors, (d : ℂ) ^ (k - 1) * (-1 : ℂ) ^ ((d + k / 2) * (n / d - 1))

/-- $(-1)^{(d+2)(n/d-1)} = (-1)^{n+d}$ for $d \mid n$. -/
lemma neg_one_pow_eight_aux {n d : ℕ} (hd : d ∣ n) (hn : 0 < n) :
    (-1 : ℂ) ^ ((d + 2) * (n / d - 1)) = (-1 : ℂ) ^ (n + d) := by
  obtain ⟨e, rfl⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_mul_pos_right hn
  have he0 : 0 < e := Nat.pos_of_mul_pos_left hn
  rw [Nat.mul_div_cancel_left e hd0]
  rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := d * e + d)]
  congr 1
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [Nat.add_mod, Nat.mul_mod, Nat.add_mod d 2]
  rcases Nat.mod_two_eq_zero_or_one d with h | h <;> rcases Nat.mod_two_eq_zero_or_one e' with h' | h' <;>
    simp [h, h', Nat.mul_mod, Nat.add_mod, Nat.mul_add, Nat.add_mul]

/-- **Moreno–Wagstaff, Remark 6.5 for $s = 8$** (p. 196): $\rho_8(n) = 16\sum_{d \mid n} d^3(-1)^{(d+2)(n/d-1)}$ for
$n \ge 1$. Unconditional: $\rho_8 = r_8$ (Theorem 6.1) and Jacobi's eight-squares formula (6.4). -/
@[kb "morenowagstaff2005" "Remark 6.5, (6.23) for s = 8, p. 196"]
theorem remark65_eight {n : ℕ} (hn : 0 < n) :
    singularSeriesSq 8 n = 16 * ∑ d ∈ n.divisors, (d : ℂ) ^ 3 * (-1 : ℂ) ^ ((d + 2) * (n / d - 1)) := by
  rw [← theorem61_small (by norm_num) le_rfl hn]
  have h := repNum_sumSq_eight hn
  have h' : (repNum (sumSq 8) n : ℂ) = ((16 * ∑ d ∈ n.divisors, (-1 : ℤ) ^ (n + d) * (d : ℤ) ^ 3 : ℤ) : ℂ) := by
    rw [← h]; norm_cast
  rw [h']
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [neg_one_pow_eight_aux (Nat.dvd_of_mem_divisors hd) hn]
  ring

/-- The instance $k = 4$ of `Remark65Even`: $\frac{2k}{(2^k-1)|B_k|} = \frac{8}{15 \cdot \frac1{30}} = 16$. -/
theorem remark65Even_four (n : ℕ) (hn : 0 < n) :
    singularSeriesSq (2 * 4) n =
      (2 * 4 : ℂ) / ((2 ^ 4 - 1) * |(bernoulli 4 : ℝ)|) *
        ∑ d ∈ n.divisors, (d : ℂ) ^ (4 - 1) * (-1 : ℂ) ^ ((d + 4 / 2) * (n / d - 1)) := by
  have hB : (bernoulli 4 : ℝ) = -1 / 30 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]; push_cast; ring
  rw [hB, show (2 * 4 : ℕ) = 8 from rfl, remark65_eight hn]
  norm_num

end QuadFormsKB.MorenoWagstaff
