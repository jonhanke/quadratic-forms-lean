/-
# Cassels, Chapter 6: supplementary items

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 6 (key `cassels1978`).

**Conventions.** Indices are 0-based (`Fin n`, variables $x_0, \dots, x_{n-1}$); Cassels' $a_1, \dots, a_n$ are
`a 0`, ..., `a (n-1)`. In §8, $n = m + 2$. Forms are written as symmetric integral matrices ($F$, `qv F x`
$= \sum_{i,j} F_{ij}x_ix_j$, `bv F x y` $= \sum_{i,j} F_{ij}x_iy_j$) or as rational forms $Q$ (`RatQF n`).

**Formalized and proved.**
* `kneser_zero_printed`: Cassels' (8.8)–(8.10) for Kneser's form (`kneser`, in `Sec8.lean`): the first coordinate of a
  nonzero zero is nonzero, the explicit expression (8.8) of the last coordinate, the sum of squares (8.9) and the final
  bound (8.10), for integers $b \ge 3$ ("$b$ a large positive integer").
* `kneser_middle_bound_false`: the middle expression of (8.10) is false (erratum, with a numerical counterexample).
* `constant_two_not_enough`: the constant $4$ in Corollary 1 to Theorem 4.1 cannot be replaced by $2$
  ($x_0^2 + x_1^2 - px_2^2$ with $p \equiv 1 \pmod 4$ prime).
* `aubry_new_zero`: the new zero $f(\vec b)\vec a - 2f(\vec a, \vec b)\vec b$ in the proof of Lemma 8.1.
* `isotropic_scale_invariant`: isotropy (over every field of characteristic $0$, in particular $\mathbb Q$,
  $\mathbb R$, $\mathbb Q_p$) depends only on the isometry class and is unchanged by $Q \mapsto cQ$ (Ch. 6, §2).
* `legendre_descent_identity`: the polynomial identity of Legendre's descent (Ch. 6, Notes).

**Source of (8.8)–(8.10).** The formulas are garbled in the machine-read text; they are stated here as printed on the
page image (p. 87), with $\lambda_j = a_j - ba_{j-1}$ in Cassels' indexing. The middle expression of (8.10) is false
(`kneser_middle_bound_false`); the final bound holds (`kneser_zero_printed`).
-/
import QuadFormsKB.Literature.Cassels.Ch6.Sec8
import QuadFormsKB.Literature.Cassels.Ch6.Sec4

namespace QuadFormsKB.Cassels.Ch6

section KneserPrinted

variable {m : ℕ}

/-- Helper: unrolling the recursion $g_{k+1} = \lambda_k + bg_k$, where $\lambda_k = g_{k+1} - bg_k$:
$g_k = \sum_{j<k} b^{k-1-j}(g_{j+1} - bg_j) + b^kg_0$. Here $b$ is the multiplier, $g$ any sequence of integers
and $k$ the index. -/
lemma kneser_unroll (b : ℤ) (g : ℕ → ℤ) (k : ℕ) :
    g k = ∑ j ∈ Finset.range k, b ^ (k - 1 - j) * (g (j + 1) - b * g j) + b ^ k * g 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h1 : ∑ j ∈ Finset.range k, b ^ (k + 1 - 1 - j) * (g (j + 1) - b * g j) =
        b * ∑ j ∈ Finset.range k, b ^ (k - 1 - j) * (g (j + 1) - b * g j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.mp hj
      have : k + 1 - 1 - j = (k - 1 - j) + 1 := by omega
      rw [this, pow_succ]
      ring
    rw [h1]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    linear_combination b * ih

/-- Helper: the geometric sum $(b-1)\sum_{j=0}^{m} b^{m-j} = b^{m+1} - 1$, summed over `Fin (m + 1)`. -/
lemma geom_fin (b : ℤ) (m : ℕ) :
    (∑ j : Fin (m + 1), b ^ (m - j.val)) * (b - 1) = b ^ (m + 1) - 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => b ^ (m - k)) (m + 1)]
  have := Finset.sum_range_reflect (fun k => b ^ k) (m + 1)
  simp only [Nat.add_sub_cancel] at this
  rw [this]
  exact geom_sum_mul b (m + 1)

/-- **Cassels, Ch. 6, §8, (8.8)–(8.10), p. 87 (as printed, final bound).** Let $b \ge 3$ be an integer (Cassels:
"$b$ a large positive integer"; the argument uses $b \ge 3$) and let $\vec a \in \mathbb Z^{m+2}$, $\vec a \ne 0$,
be a zero of Kneser's form (8.6), $f(\vec x) = x_0^2 - \sum_{j=0}^{m}(x_{j+1} - bx_j)^2$ (`kneser m b`). Write
$\lambda_j = a_{j+1} - ba_j$ for $0 \le j \le m$ (Cassels' $\lambda_{j+2} = a_{j+2} - ba_{j+1}$, 1-based). Then
1. $a_0 \ne 0$;
2. (8.8) $a_{m+1} = \sum_{j=0}^{m} b^{m-j}\lambda_j + b^{m+1}a_0$;
3. (8.9) $\sum_{j=0}^{m}\lambda_j^2 = a_0^2$;
4. (8.10, final bound) $b^{m+1} - b^m \le \lvert a_{m+1}\rvert$ (Cassels' $b^{n-1} - b^{n-2}$ with $n = m+2$).

The middle expression of (8.10) is false in general, see `kneser_middle_bound_false`. Arguments: `b` the multiplier,
`hb` the hypothesis $b \ge 3$, `a` the zero, `ha` that it is nonzero, `hz` that it is a zero of `kneser m b`. -/
@[kb "cassels1978" "Ch. 6, §8, (8.8)–(8.10), p. 87 (as printed, final bound)"]
theorem kneser_zero_printed (b : ℤ) (hb : 3 ≤ b) (a : Fin (m + 2) → ℤ) (ha : a ≠ 0)
    (hz : qv (kneser m b) a = 0) :
    a 0 ≠ 0 ∧
    a (Fin.last (m + 1)) = ∑ j : Fin (m + 1), b ^ (m - j.val) * (a j.succ - b * a j.castSucc)
        + b ^ (m + 1) * a 0 ∧
    ∑ j : Fin (m + 1), (a j.succ - b * a j.castSucc) ^ 2 = a 0 ^ 2 ∧
    b ^ (m + 1) - b ^ m ≤ |a (Fin.last (m + 1))| := by
  have hsum : ∑ j : Fin (m + 1), (a j.succ - b * a j.castSucc) ^ 2 = a 0 ^ 2 := by
    have hq := qv_kneser b a
    rw [hz] at hq
    linarith
  have hL : ∀ j : Fin (m + 1), |a j.succ - b * a j.castSucc| ≤ |a 0| := by
    intro j
    have : (a j.succ - b * a j.castSucc) ^ 2 ≤ a 0 ^ 2 := by
      rw [← hsum]
      exact Finset.single_le_sum (f := fun j : Fin (m + 1) => (a j.succ - b * a j.castSucc) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    exact sq_le_sq.mp this
  set g : ℕ → ℤ := fun k => if h : k < m + 2 then a ⟨k, h⟩ else 0 with hgdef
  have hg : ∀ k (hk : k < m + 2), g k = a ⟨k, hk⟩ := fun k hk => by simp [hgdef, hk]
  have hgL : ∀ j : Fin (m + 1), g (j.val + 1) - b * g j.val = a j.succ - b * a j.castSucc := by
    intro j
    rw [hg (j.val + 1) (by omega), hg j.val (by omega)]
    rfl
  have h88 : a (Fin.last (m + 1)) = ∑ j : Fin (m + 1), b ^ (m - j.val) * (a j.succ - b * a j.castSucc)
      + b ^ (m + 1) * a 0 := by
    have h := kneser_unroll b g (m + 1)
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => b ^ (m + 1 - 1 - j) * (g (j + 1) - b * g j)) (m + 1)] at h
    simp only [Nat.add_sub_cancel] at h
    have e1 : g (m + 1) = a (Fin.last (m + 1)) := hg (m + 1) (by omega)
    have e2 : g 0 = a 0 := hg 0 (by omega)
    rw [e1, e2] at h
    rw [h]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [hgL j]
  have ha0 : a 0 ≠ 0 := by
    intro h0
    apply ha
    have hL0 : ∀ j : Fin (m + 1), a j.succ - b * a j.castSucc = 0 := by
      intro j
      have h1 := hL j
      rw [h0, abs_zero] at h1
      exact abs_nonpos_iff.mp h1
    have hall : ∀ k (hk : k < m + 2), a ⟨k, hk⟩ = 0 := by
      intro k hk
      rw [← hg k hk, kneser_unroll b g k]
      have e2 : g 0 = 0 := by rw [hg 0 (by omega)]; exact h0
      rw [e2, mul_zero, add_zero]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj' := Finset.mem_range.mp hj
      rw [show g (j + 1) - b * g j = 0 from by
        rw [show j = (⟨j, by omega⟩ : Fin (m + 1)).val from rfl, hgL ⟨j, by omega⟩]
        exact hL0 _]
      simp
    funext i
    exact hall i.val i.isLt
  refine ⟨ha0, h88, hsum, ?_⟩
  -- the final bound
  set T : ℤ := ∑ j : Fin (m + 1), b ^ (m - j.val) * (a j.succ - b * a j.castSucc) with hT
  have hlow : b ^ (m + 1) * |a 0| - |T| ≤ |a (Fin.last (m + 1))| := by
    have h := abs_sub_abs_le_abs_sub (b ^ (m + 1) * a 0) (-T)
    rw [abs_neg, sub_neg_eq_add, abs_mul, abs_of_nonneg (by positivity : 0 ≤ b ^ (m + 1))] at h
    have e : |a (Fin.last (m + 1))| = |b ^ (m + 1) * a 0 + T| := by rw [h88, add_comm]
    rw [e]
    exact h
  have hT1 : |T| ≤ ∑ j : Fin (m + 1), b ^ (m - j.val) * |a j.succ - b * a j.castSucc| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ b ^ (m - j.val))]
  have hb0 : (0 : ℤ) ≤ b := by omega
  have hpm : b ^ m ≤ b ^ (m + 1) := pow_le_pow_right₀ (by omega) (by omega)
  have h0 : 1 ≤ |a 0| := Int.one_le_abs ha0
  rcases eq_or_lt_of_le h0 with h1 | h2
  · -- |a 0| = 1
    have hT2 : |T| ≤ b ^ m := by
      refine le_trans hT1 ?_
      have : ∀ j : Fin (m + 1), b ^ (m - j.val) * |a j.succ - b * a j.castSucc| ≤
          b ^ m * (a j.succ - b * a j.castSucc) ^ 2 := by
        intro j
        have e1 : |a j.succ - b * a j.castSucc| ≤ (a j.succ - b * a j.castSucc) ^ 2 := by
          have := Int.le_self_sq |a j.succ - b * a j.castSucc|
          rwa [sq_abs] at this
        have e2 : b ^ (m - j.val) ≤ b ^ m := pow_le_pow_right₀ (by omega) (Nat.sub_le _ _)
        have e3 : 0 ≤ |a j.succ - b * a j.castSucc| := abs_nonneg _
        have e4 : 0 ≤ b ^ m := by positivity
        exact le_trans (mul_le_mul e2 e1 e3 e4) (le_refl _)
      refine le_trans (Finset.sum_le_sum fun j _ => this j) (le_of_eq ?_)
      rw [← Finset.mul_sum, hsum]
      have : a 0 ^ 2 = 1 := by rw [← sq_abs, ← h1]; norm_num
      rw [this, mul_one]
    rw [← h1] at hlow
    linarith
  · -- |a 0| ≥ 2
    have h2' : 2 ≤ |a 0| := by omega
    have hS := geom_fin b m
    set S : ℤ := ∑ j : Fin (m + 1), b ^ (m - j.val) with hSdef
    have hSnn : 0 ≤ S := Finset.sum_nonneg fun j _ => by positivity
    have hS2 : 2 * S ≤ b ^ (m + 1) := by nlinarith
    have hT2 : |T| ≤ |a 0| * S := by
      refine le_trans hT1 ?_
      rw [hSdef, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      have := mul_le_mul_of_nonneg_left (hL j) (by positivity : 0 ≤ b ^ (m - j.val))
      linarith
    have hP : 0 ≤ b ^ (m + 1) := by positivity
    have hA : 0 ≤ |a 0| := abs_nonneg _
    have hbm : 0 ≤ b ^ m := by positivity
    have h3 : 2 * (b ^ (m + 1) - S) ≥ b ^ (m + 1) := by linarith
    have h4 : 2 * (b ^ (m + 1) - S) ≤ |a 0| * (b ^ (m + 1) - S) :=
      mul_le_mul_of_nonneg_right h2' (by linarith)
    nlinarith

end KneserPrinted

/-- **Cassels, Ch. 6, §8, (8.10), p. 87 (erratum: the middle inequality fails).** *Erratum:* the middle expression
$-\lvert a_1\rvert b^{n-2} + \lvert a_1\rvert b^{n-1}$ of (8.10) is not a lower bound for $\lvert a_n\rvert$ (Cassels'
1-based indices; $a_1$ is `a 0`). For $m = 1$ ($n = 3$), $b = 3$ and $\vec a = (13, 27, 76)$ we have
`qv (kneser 1 3) a = 0` ($13^2 - (27-39)^2 - (76-81)^2 = 169 - 144 - 25 = 0$) but
$\lvert a_2\rvert = 76 < 78 = -\lvert a_0\rvert\cdot 3 + \lvert a_0\rvert\cdot 3^2$. Confirmed by direct computation in
Lean. The final bound $b^{n-1} - b^{n-2} \le \lvert a_n\rvert$ of (8.10) still holds (`kneser_zero_printed`); the
printed chain breaks because $\lvert a_n\rvert \ge \lvert a_1\rvert b^{n-1} - \sum_j \lvert\lambda_j\rvert b^{n-j}$ and
the sum is not bounded by $\lvert a_1\rvert b^{n-2}$ when $\lvert a_1\rvert \ge 2$. -/
@[kb "cassels1978" "Ch. 6, §8, (8.10), p. 87 (erratum: the middle inequality fails)"]
theorem kneser_middle_bound_false :
    qv (kneser 1 3) ![13, 27, 76] = 0 ∧
    |(![13, 27, 76] : Fin 3 → ℤ) 2| <
      -|(![13, 27, 76] : Fin 3 → ℤ) 0| * 3 ^ 1 + |(![13, 27, 76] : Fin 3 → ℤ) 0| * 3 ^ 2 := by
  constructor
  · rw [qv_kneser]
    simp [Fin.sum_univ_succ]
  · simp

/-- **Cassels, Ch. 6, §4, p. 82 (the constant $4$ in Corollary 1 to Theorem 4.1 cannot be replaced by $2$).** Let $p$
be a prime with $p \equiv 1 \pmod 4$ and $\vec a = (1, 1, -p)$, i.e. $g = x_0^2 + x_1^2 - px_2^2$. Then
* $\vec a$ satisfies the hypotheses of `legendre` (squarefree product, and conditions (i), (ii), (iii) exactly as
  there);
* there is a nonzero integral zero $\vec b$ of $g$;
* every nonzero integral zero $\vec b$ satisfies $2\lvert a_0a_1a_2\rvert \le \sum_i \lvert a_i\rvert b_i^2$, so no
  nonzero zero has $\sum_i\lvert a_i\rvert b_i^2 < 2\lvert a_0a_1a_2\rvert$, although
  $4\lvert a_0a_1a_2\rvert$ would be the bound of `legendre_small_zero`. -/
@[kb "cassels1978" "Ch. 6, §4, p. 82 (the 4 in Cor. 1 cannot be replaced by 2: x₁² + x₂² − px₃², p ≡ 1 mod 4)"]
theorem constant_two_not_enough (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 1) :
    (Squarefree ((![1, 1, -(p : ℤ)] : Fin 3 → ℤ) 0 * (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) 1 *
        (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) 2) ∧
      (∀ q : ℕ, q.Prime → q ≠ 2 → ∀ j : Fin 3, (q : ℤ) ∣ (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) j →
        ∃ r : ℤ, (q : ℤ) ∣ (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) (j + 1) * r ^ 2 +
          (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) (j + 2)) ∧
      (∀ j : Fin 3, (2 : ℤ) ∣ (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) j → ∃ s : ℤ, (s = 0 ∨ s = 1) ∧
        (8 : ℤ) ∣ (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) (j + 1) + (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) (j + 2) +
          s * (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) j) ∧
      (¬ (2 : ℤ) ∣ (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) 0 * (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) 1 *
          (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) 2 →
        ∃ j : Fin 3, (4 : ℤ) ∣ (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) j +
          (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) (j + 1))) ∧
    (∃ b : Fin 3 → ℤ, b ≠ 0 ∧ ∑ i, (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) i * b i ^ 2 = 0) ∧
    ∀ b : Fin 3 → ℤ, b ≠ 0 → ∑ i, (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) i * b i ^ 2 = 0 →
      2 * |(![1, 1, -(p : ℤ)] : Fin 3 → ℤ) 0 * (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) 1 *
          (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) 2| ≤
        ∑ i, |(![1, 1, -(p : ℤ)] : Fin 3 → ℤ) i| * b i ^ 2 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpodd : p ≠ 2 := by rintro rfl; omega
  have hprod : (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) 0 * (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) 1 *
      (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) 2 = -(p : ℤ) := by simp
  have hsq : Squarefree (-(p : ℤ)) := by
    intro x hx
    exact (Int.squarefree_natCast.mpr hp.squarefree) x ((dvd_neg).mp hx)
  have hi : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ j : Fin 3, (q : ℤ) ∣ (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) j →
      ∃ r : ℤ, (q : ℤ) ∣ (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) (j + 1) * r ^ 2 +
        (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) (j + 2) := by
    intro q hq hq2 j hj
    fin_cases j
    · simp at hj
      exact absurd (Int.natCast_dvd_natCast.mp (by simpa using hj) |> Nat.dvd_one.mp) hq.ne_one
    · simp at hj
      exact absurd (Int.natCast_dvd_natCast.mp (by simpa using hj) |> Nat.dvd_one.mp) hq.ne_one
    · have hqp : q = p := by
        simp at hj
        have : q ∣ p := Int.natCast_dvd_natCast.mp hj
        exact (Nat.prime_dvd_prime_iff_eq hq hp).mp this
      subst hqp
      have : Fact q.Prime := ⟨hq⟩
      obtain ⟨y, hy⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : q % 4 ≠ 3)
      refine ⟨(y.val : ℤ), ?_⟩
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp
      rw [sq, ← hy]
      ring
  have hii : ∀ j : Fin 3, (2 : ℤ) ∣ (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) j → ∃ s : ℤ, (s = 0 ∨ s = 1) ∧
      (8 : ℤ) ∣ (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) (j + 1) + (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) (j + 2) +
        s * (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) j := by
    intro j hj
    exfalso
    have hodd : ¬ (2 : ℤ) ∣ (p : ℤ) := by
      intro h
      have : 2 ∣ p := Int.natCast_dvd_natCast.mp h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this
      omega
    fin_cases j <;> simp at hj <;> omega
  have hiii : ¬ (2 : ℤ) ∣ (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) 0 * (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) 1 *
      (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) 2 →
      ∃ j : Fin 3, (4 : ℤ) ∣ (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) j +
        (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) (j + 1) := by
    intro _
    refine ⟨1, ?_⟩
    simp
    omega
  have hsq' : Squarefree ((![1, 1, -(p : ℤ)] : Fin 3 → ℤ) 0 * (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) 1 *
      (![1, 1, -(p : ℤ)] : Fin 3 → ℤ) 2) := by rw [hprod]; exact hsq
  refine ⟨⟨hsq', hi, hii, hiii⟩, legendre _ hsq' hi hii hiii, ?_⟩
  intro b hb hz
  rw [hprod]
  simp only [Fin.sum_univ_three] at hz ⊢
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hz ⊢
  rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℤ) ≤ p)]
  simp only [abs_one, one_mul] at *
  have hb2 : b 2 ≠ 0 := by
    intro h2
    apply hb
    rw [h2] at hz
    have h0 : b 0 = 0 := by nlinarith [sq_nonneg (b 0), sq_nonneg (b 1)]
    have h1 : b 1 = 0 := by nlinarith [sq_nonneg (b 0), sq_nonneg (b 1)]
    funext i
    fin_cases i <;> simp [h0, h1, h2]
  have : 1 ≤ b 2 ^ 2 := by
    have := Int.one_le_abs hb2
    nlinarith [sq_abs (b 2)]
  have hpz : (0 : ℤ) ≤ p := by positivity
  nlinarith

/-- **Cassels, Ch. 6, §8, proof of Lemma 8.1, pp. 87–89 (the new zero $\vec a^* = f(\vec b)\vec a - 2f(\vec a,
\vec b)\vec b$).** Over a commutative ring $R$, let $F$ be a symmetric $n \times n$ matrix, `qv F` the form
$f(\vec x) = \sum F_{ij}x_ix_j$ and `bv F` the bilinear form $f(\vec x, \vec y) = \sum F_{ij}x_iy_j$. If
$f(\vec a) = 0$, then $\vec a^* = f(\vec b)\vec a - 2f(\vec a, \vec b)\vec b$ satisfies $f(\vec a^*) = 0$, for every
$\vec b$. Arguments: `F` the symmetric matrix (`hF`), `a` the zero (`ha`), `b` any vector. -/
@[kb "cassels1978" "Ch. 6, §8, proof of Lemma 8.1, pp. 87–89 (the new zero a* = f(b)a − 2f(a,b)b)"]
theorem aubry_new_zero {R : Type*} [CommRing R] {n : ℕ} (F : Matrix (Fin n) (Fin n) R)
    (hF : ∀ i j, F i j = F j i) (a b : Fin n → R) (ha : qv F a = 0) :
    qv F (qv F b • a - (2 * bv F a b) • b) = 0 := by
  have h := qv_comb F hF (qv F b) (-(2 * bv F a b)) a b
  rw [neg_smul, ← sub_eq_add_neg] at h
  rw [h, ha]
  ring

section Isotropy

open QuadFormsKB

/-- Helper: the value of the scaled form $cQ$ over a field $K \supseteq \mathbb Q$ is $c\,Q(\vec x)$. Arguments: `K` the
field, `Q` the rational form, `c` the scalar, `x` the vector over `K`. -/
lemma evalIn_smul_form {n : ℕ} (K : Type*) [Field K] [CharZero K] (Q : RatQF n) (c : ℚ)
    (x : Fin n → K) : (c • Q).evalIn K x = algebraMap ℚ K c * Q.evalIn K x := by
  unfold QuadForm.evalIn
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · simp only [QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul, map_mul]
    ring
  · simp

/-- **Cassels, Ch. 6, §2, p. 78 (whether Theorem 1.1 holds for $f$ depends only on the class of $f$, and is unchanged
by $f \mapsto af$).** Let $Q$ be a rational quadratic form in $n$ variables, $K$ a field of characteristic $0$ (for
instance $\mathbb Q$, $\mathbb R$ or $\mathbb Q_p$, so the statement holds at every place) and $c \in \mathbb Q$,
$c \ne 0$. Then
1. $cQ$ is isotropic over $K$ if and only if $Q$ is;
2. if $Q'$ is isometric to $Q$ over $K$ (`QuadForm.IsometricIn`; in particular over $\mathbb Q$ and then over every $K$),
   then $Q$ is isotropic over $K$ if and only if $Q'$ is.

Combined with the Hasse–Minkowski theorem, "$Q$ is isotropic at every place" and "$Q$ is isotropic over $\mathbb Q$" are
therefore properties of the class of $Q$ up to scaling. Part 2 is `QuadFormsKB.HM3.isotropicIn_iff_of_isometricIn`. -/
@[kb "cassels1978" "Ch. 6, §2, p. 78 (isotropy depends only on the class of f and is unchanged by f ↦ af)"]
theorem isotropic_scale_invariant {n : ℕ} (K : Type*) [Field K] [CharZero K] (Q : RatQF n) (c : ℚ)
    (hc : c ≠ 0) :
    ((c • Q).IsotropicIn K ↔ Q.IsotropicIn K) ∧
    ∀ Q' : RatQF n, Q.IsometricIn K Q' → (Q.IsotropicIn K ↔ Q'.IsotropicIn K) := by
  refine ⟨?_, fun Q' h => HM3.isotropicIn_iff_of_isometricIn K h⟩
  have hc' : algebraMap ℚ K c ≠ 0 := by
    intro h
    exact hc ((algebraMap ℚ K).injective (by rw [h, map_zero]))
  constructor
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, ?_⟩
    rw [evalIn_smul_form] at h
    exact (mul_eq_zero.mp h).resolve_left hc'
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, ?_⟩
    rw [evalIn_smul_form, h, mul_zero]

end Isotropy

/-- **Cassels, Ch. 6, Notes, p. 97 (the identity of Legendre's descent).** Over a commutative ring, if
$a_1r^2 + a_2 = a_3A_3$ then
$$(a_1rx_1 - a_2x_2)^2 + a_1a_2(x_1 + rx_2)^2 + A_3(a_3x_3)^2 = a_3A_3\,(a_1x_1^2 + a_2x_2^2 + a_3x_3^2),$$
i.e. with $X_1 = a_1rx_1 - a_2x_2$, $X_2 = x_1 + rx_2$, $X_3 = a_3x_3$, $A_2 = a_1a_2$ the form
$X_1^2 + A_2X_2^2 + A_3X_3^2$ is $a_3A_3$ times $a_1x_1^2 + a_2x_2^2 + a_3x_3^2$. Cassels' 1-based names are kept for
these scalars (they are not `Fin`-indexed): `a₁ a₂ a₃` the coefficients, `r` the multiplier, `A₃` the new coefficient,
`x₁ x₂ x₃` the variables, `h` the hypothesis. -/
@[kb "cassels1978" "Ch. 6, Notes, p. 97 (the identity of Legendre's descent)"]
theorem legendre_descent_identity {R : Type*} [CommRing R] (a₁ a₂ a₃ A₃ r x₁ x₂ x₃ : R)
    (h : a₁ * r ^ 2 + a₂ = a₃ * A₃) :
    (a₁ * r * x₁ - a₂ * x₂) ^ 2 + (a₁ * a₂) * (x₁ + r * x₂) ^ 2 + A₃ * (a₃ * x₃) ^ 2 =
      a₃ * A₃ * (a₁ * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2) := by
  linear_combination (a₁ * x₁ ^ 2 + a₂ * x₂ ^ 2) * h

end QuadFormsKB.Cassels.Ch6
