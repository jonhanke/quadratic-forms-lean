/-
# Cassels, Chapter 6, §10: the diagonalization (10.4) in the proof of Bruck–Ryser

**Source.** Cassels, *Rational Quadratic Forms*, Ch. 6, §10, proof of Lemma 10.1, p. 92. For a projective plane of
order $n$ with $N = n^2 + n + 1$ points, (10.3) gives the form
$g(\vec x) = (n+1)\sum_j x_j^2 + \sum_{i \ne j} x_ix_j = n\sum_j x_j^2 + \bigl(\sum_j x_j\bigr)^2$ in $N$ variables
(`Cassels.Ch6.sum_sq_lines`). Cassels diagonalizes it by the new variables (10.4) $y_1 = x_2 + \dots + x_N$,
$y_j = x_j + n^{-1}x_1$ ($j > 1$), finding $g$ rationally equivalent to $h(\vec y) = y_1^2 + n\sum_{j>1} y_j^2$. (The
machine-read text of (10.4) is garbled; read from the page image. `Ch6/Sec10.lean` proves Lemma 10.1 with another
orthogonal basis.)

**Conventions.** Indices 0-based: Cassels' $x_1, \dots, x_N$ are `x 0, …, x m` with $N = m + 1$, $m = n^2 + n$; his
$y_1$ is $\sum_{j} x_{j+1}$ and his $y_{j+1}$ is $x_{j+1} + x_0/n$ ($0 \le j < m$).

**Proves.**
* `bruck_ryser_diag` (10.4): the identity $g(\vec x) = y_1^2 + n\sum_{j>1}y_j^2$;
* `bruck_ryser_diag_injective`: the substitution $\vec x \mapsto \vec y$ is injective (so invertible), hence $g$ and $h$
  are rationally equivalent.
-/
import Mathlib
import QuadFormsKB.Citation

namespace QuadFormsKB.Cassels.Ch6

open Finset

/-- **Cassels, Ch. 6, §10, (10.4), p. 92**: for a positive integer $n$ (the order of the plane), $m = n^2 + n$ (so
$N = m + 1$ variables) and $\vec x \in \mathbb Q^{m+1}$,
$$n\sum_i x_i^2 + \Bigl(\sum_i x_i\Bigr)^2 = y_1^2 + n\sum_{j>1} y_j^2,\qquad y_1 = \sum_{j \ge 1} x_j,\quad
y_j = x_j + x_0/n,$$
i.e. Cassels' form $g$ of (10.3) becomes $h(\vec y) = y_1^2 + n\sum_{j>1}y_j^2$ in the variables (10.4). -/
@[kb "cassels1978" "Ch. 6, §10, (10.4), p. 92"]
theorem bruck_ryser_diag (n : ℕ) (hn : 0 < n) (x : Fin (n ^ 2 + n + 1) → ℚ) :
    n * ∑ i, x i ^ 2 + (∑ i, x i) ^ 2 =
      (∑ j : Fin (n ^ 2 + n), x j.succ) ^ 2 + n * ∑ j : Fin (n ^ 2 + n), (x j.succ + x 0 / n) ^ 2 := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ (fun i => x i)]
  have hexp : ∑ j : Fin (n ^ 2 + n), (x j.succ + x 0 / n) ^ 2 =
      ∑ j : Fin (n ^ 2 + n), x j.succ ^ 2 + 2 * (x 0 / n) * ∑ j : Fin (n ^ 2 + n), x j.succ +
        ((n ^ 2 + n : ℕ) : ℚ) * (x 0 / n) ^ 2 := by
    rw [sum_congr rfl (fun j _ => (by ring : (x j.succ + x 0 / n) ^ 2 =
      x j.succ ^ 2 + 2 * (x 0 / n) * x j.succ + (x 0 / n) ^ 2))]
    simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hexp]
  push_cast
  field_simp
  ring

/-- **Cassels, Ch. 6, §10, (10.4), p. 92** (the substitution is invertible): with $n > 0$ and $m = n^2 + n$, the linear
map $\vec x \mapsto \vec y$ of (10.4) ($y_1 = \sum_{j\ge1}x_j$, $y_{j} = x_j + x_0/n$ for $j \ge 1$) is injective, so $g$
and $h$ are rationally equivalent. -/
@[kb "cassels1978" "Ch. 6, §10, (10.4), p. 92 (the substitution is invertible)"]
theorem bruck_ryser_diag_injective (n : ℕ) (hn : 0 < n) (x : Fin (n ^ 2 + n + 1) → ℚ)
    (h1 : ∑ j : Fin (n ^ 2 + n), x j.succ = 0) (h2 : ∀ j : Fin (n ^ 2 + n), x j.succ + x 0 / n = 0) : x = 0 := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hxj : ∀ j : Fin (n ^ 2 + n), x j.succ = -(x 0 / n) := fun j => by linarith [h2 j]
  have hsum : ∑ j : Fin (n ^ 2 + n), x j.succ = ((n ^ 2 + n : ℕ) : ℚ) * -(x 0 / n) := by
    simp [hxj, sum_const, card_univ]
  rw [h1] at hsum
  have hm : ((n ^ 2 + n : ℕ) : ℚ) ≠ 0 := by positivity
  have h0 : x 0 = 0 := by
    have : x 0 / n = 0 := by
      have := (mul_eq_zero.1 hsum.symm).resolve_left hm
      linarith
    rcases div_eq_zero_iff.1 this with h | h
    · exact h
    · exact absurd h hn'
  funext i
  refine Fin.cases h0 (fun j => ?_) i
  simp [hxj j, h0]

end QuadFormsKB.Cassels.Ch6
