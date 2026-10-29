/-
# Cassels, Chapter 3, Lemma 1.5: $p$-adic digit expansions

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 3, Lemma 1.5, p. 39.

**Statement** (`padic_digits`): every $\alpha \in \mathbb Z_p$ (`ℤ_[p]`) is uniquely of the form
$\alpha = \sum_{j \ge 0} a_j p^{j}$ with digits $a_j \in \{0, 1, \dots, p - 1\}$ (`Fin p`); the series converges in
$\mathbb Z_p$ (`HasSum`).

**Proof.** Existence: $a_0$ is the representative of $\alpha$ modulo $p$ in $\{0, \dots, p-1\}$ (Mathlib's
`PadicInt.zmodRepr`), $\alpha = a_0 + p\alpha_1$, and recursively (`Digits.seq`, `Digits.digit`); then
$\alpha - \sum_{j<N} a_jp^{j} = p^{N}\alpha_N$ (`Digits.partial_eq`) has norm $\le p^{-N}$. Uniqueness: if
$\sum a_jp^{j} = \sum b_jp^{j}$ then the natural numbers $\sum_{j<N} a_jp^{j}$ and $\sum_{j<N} b_jp^{j}$, both $< p^{N}$,
are congruent modulo $p^{N}$ (the tails are divisible by $p^{N}$ in $\mathbb Z_p$), hence equal for all $N$, which forces
$a_N = b_N$.
-/
import Mathlib
import QuadFormsKB.Citation

open Filter Topology

namespace QuadFormsKB.Cassels

namespace Digits

variable {p : ℕ} [hp : Fact p.Prime]

/-- $x = r + p y$ with $r \in \{0, \dots, p-1\}$ the residue of $x$. -/
theorem exists_next (x : ℤ_[p]) : ∃ y : ℤ_[p], x = (PadicInt.zmodRepr x : ℤ_[p]) + p * y := by
  have h := PadicInt.sub_zmodRepr_mem x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨y, hy⟩ := h
  exact ⟨y, by rw [mul_comm, hy]; ring⟩

/-- The quotient $(x - r)/p$. -/
noncomputable def next (x : ℤ_[p]) : ℤ_[p] := Classical.choose (exists_next x)

/-- $x = r(x) + p \cdot \mathrm{next}(x)$. -/
theorem next_spec (x : ℤ_[p]) : x = (PadicInt.zmodRepr x : ℤ_[p]) + p * next x :=
  Classical.choose_spec (exists_next x)

/-- $\alpha_n$: $\alpha_0 = \alpha$, $\alpha_{n+1} = (\alpha_n - a_n)/p$. -/
noncomputable def seq (α : ℤ_[p]) (n : ℕ) : ℤ_[p] := next^[n] α

/-- The $j$-th digit $a_j$ of $\alpha$. -/
noncomputable def digit (α : ℤ_[p]) (j : ℕ) : Fin p := ⟨PadicInt.zmodRepr (seq α j), PadicInt.zmodRepr_lt_p _⟩

/-- $\alpha = \sum_{j<N} a_j p^{j} + p^{N}\alpha_N$. -/
theorem partial_eq (α : ℤ_[p]) (N : ℕ) :
    α = ∑ j ∈ Finset.range N, ((digit α j : ℕ) : ℤ_[p]) * p ^ j + p ^ N * seq α N := by
  induction N with
  | zero => simp [seq]
  | succ N ih =>
    have h := next_spec (seq α N)
    have hs : seq α (N + 1) = next (seq α N) := Function.iterate_succ_apply' next N α
    rw [Finset.sum_range_succ, hs]
    conv_lhs => rw [ih, h]
    simp only [digit]
    ring

/-- $\lvert a_j p^{j}\rvert_p \le p^{-j}$. -/
theorem norm_digit_term_le (a : ℕ → Fin p) (j : ℕ) : ‖((a j : ℕ) : ℤ_[p]) * p ^ j‖ ≤ (p : ℝ) ^ (-(j : ℤ)) := by
  rw [norm_mul, norm_pow, PadicInt.norm_p, inv_pow, zpow_neg, zpow_natCast]
  exact mul_le_of_le_one_left (by positivity) (PadicInt.norm_le_one _)

/-- Every digit series converges. -/
theorem summable_digits (a : ℕ → Fin p) : Summable fun j => ((a j : ℕ) : ℤ_[p]) * p ^ j := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (norm_digit_term_le a) ?_
  have : Tendsto (fun j : ℕ => ((p : ℝ)⁻¹) ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt))
  simpa [zpow_neg, zpow_natCast, inv_pow] using this

/-- The digit series of $\alpha$ sums to $\alpha$. -/
theorem hasSum_digit (α : ℤ_[p]) : HasSum (fun j => ((digit α j : ℕ) : ℤ_[p]) * p ^ j) α := by
  have hs := (summable_digits (digit α)).hasSum
  have h1 := hs.tendsto_sum_nat
  have h2 : Tendsto (fun N => ∑ j ∈ Finset.range N, ((digit α j : ℕ) : ℤ_[p]) * p ^ j) atTop (𝓝 α) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (g := fun N => (p : ℝ)⁻¹ ^ N) (fun _ => norm_nonneg _) (fun N => ?_) ?_
    · have := partial_eq α N
      rw [show ∑ j ∈ Finset.range N, ((digit α j : ℕ) : ℤ_[p]) * p ^ j - α = -(p ^ N * seq α N) by
        linear_combination -this, norm_neg, norm_mul, norm_pow, PadicInt.norm_p]
      exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt))
  rw [tendsto_nhds_unique h1 h2] at hs
  exact hs

/-- The natural number $\sum_{j < N} a_j p^j$. -/
def natSum (a : ℕ → Fin p) (N : ℕ) : ℕ := ∑ j ∈ Finset.range N, (a j : ℕ) * p ^ j

omit hp in
/-- $\sum_{j<N} a_j p^{j} < p^{N}$. -/
theorem natSum_lt (a : ℕ → Fin p) (N : ℕ) : natSum a N < p ^ N := by
  induction N with
  | zero => simp [natSum]
  | succ N ih =>
    rw [natSum, Finset.sum_range_succ, ← natSum, pow_succ]
    have := (a N).2
    nlinarith

/-- If $\sum a_jp^{j} = \alpha$ then $\lvert\alpha - \sum_{j<N} a_jp^{j}\rvert_p \le p^{-N}$. -/
theorem norm_sub_natSum_le (a : ℕ → Fin p) {α : ℤ_[p]}
    (h : HasSum (fun j => ((a j : ℕ) : ℤ_[p]) * p ^ j) α) (N : ℕ) :
    ‖α - (natSum a N : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(N : ℤ)) := by
  have h1 := (hasSum_nat_add_iff' N).mpr h
  have h2 := (summable_digits (fun j => a (j + N))).hasSum.mul_left ((p : ℤ_[p]) ^ N)
  have h3 : (fun j => ((a (j + N) : ℕ) : ℤ_[p]) * p ^ (j + N)) =
      fun j => (p : ℤ_[p]) ^ N * (((a (j + N) : ℕ) : ℤ_[p]) * p ^ j) := by
    funext j; ring
  rw [h3] at h1
  have := h1.unique h2
  have hc : (natSum a N : ℤ_[p]) = ∑ j ∈ Finset.range N, ((a j : ℕ) : ℤ_[p]) * p ^ j := by
    simp [natSum]
  rw [hc, this, norm_mul, norm_pow, PadicInt.norm_p, zpow_neg, zpow_natCast, inv_pow]
  exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)

/-- Two digit expansions of the same $\alpha$ have equal partial sums. -/
theorem natSum_eq_of_hasSum {a b : ℕ → Fin p} {α : ℤ_[p]}
    (ha : HasSum (fun j => ((a j : ℕ) : ℤ_[p]) * p ^ j) α)
    (hb : HasSum (fun j => ((b j : ℕ) : ℤ_[p]) * p ^ j) α) (N : ℕ) : natSum a N = natSum b N := by
  have h1 := norm_sub_natSum_le a ha N
  have h2 := norm_sub_natSum_le b hb N
  have h3 : ‖(((natSum b N : ℤ) - natSum a N : ℤ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(N : ℤ)) := by
    have : (((natSum b N : ℤ) - natSum a N : ℤ) : ℤ_[p]) = (α - natSum a N) - (α - natSum b N) := by
      push_cast; ring
    rw [this, sub_eq_add_neg]
    refine (PadicInt.nonarchimedean _ _).trans (max_le h1 ?_)
    rw [norm_neg]; exact h2
  have hd := PadicInt.norm_int_le_pow_iff_dvd.mp h3
  have hla : (natSum a N : ℤ) < (p : ℤ) ^ N := by exact_mod_cast natSum_lt a N
  have hlb : (natSum b N : ℤ) < (p : ℤ) ^ N := by exact_mod_cast natSum_lt b N
  have : ((natSum b N : ℤ) - natSum a N) = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd hd
    rw [abs_lt]; constructor <;> omega
  omega

/-- Uniqueness of digit expansions. -/
theorem digits_unique {a b : ℕ → Fin p} {α : ℤ_[p]}
    (ha : HasSum (fun j => ((a j : ℕ) : ℤ_[p]) * p ^ j) α)
    (hb : HasSum (fun j => ((b j : ℕ) : ℤ_[p]) * p ^ j) α) : a = b := by
  funext N
  have h1 := natSum_eq_of_hasSum ha hb (N + 1)
  have h0 := natSum_eq_of_hasSum ha hb N
  simp only [natSum, Finset.sum_range_succ] at h1
  rw [← natSum, ← natSum, h0] at h1
  have := Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos N) (Nat.add_left_cancel h1)
  exact Fin.ext this

end Digits

/-- **Cassels, Ch. 3, Lemma 1.5.** Every $\alpha \in \mathbb Z_p$ can be written uniquely as a convergent series
$\alpha = \sum_{j \ge 0} a_j p^{j}$ with $a_j \in \{0, 1, \dots, p-1\}$. -/
@[kb "cassels1978" "Ch. 3, Lemma 1.5, p. 39"]
theorem padic_digits {p : ℕ} [Fact p.Prime] (α : ℤ_[p]) :
    ∃! a : ℕ → Fin p, HasSum (fun j => ((a j : ℕ) : ℤ_[p]) * p ^ j) α :=
  ⟨Digits.digit α, Digits.hasSum_digit α, fun _ hb => Digits.digits_unique hb (Digits.hasSum_digit α)⟩

end QuadFormsKB.Cassels
