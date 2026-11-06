/-
# Cassels, Chapter 6, §8: Kneser's example, the exponent in Lemma 8.1 is best possible

**Setting.** As for `aubry` (Cassels, Ch. 6, Lemma 8.1, in `Ch5/Minkowski.lean`): an integral form
$f(\vec x) = \sum_{i,j} f_{ij}x_ix_j$ is given by its symmetric matrix $F = (f_{ij})$ (`qv F x`), and
$F = \sum_{i,j}\lvert f_{ij}\rvert$ by abuse of notation. Here $n = m + 2$ variables $x_0, \dots, x_{m+1}$ (Cassels:
$x_1, \dots, x_n$).

**Proves** (Cassels, *Rational Quadratic Forms*, Chapter 6, §8, Note to Lemma 8.1, p. 87)
* Kneser's form (8.6) $f(\vec x) = x_0^2 - \sum_{j=1}^{n-1}(x_j - bx_{j-1})^2$ (`kneser`, `qv_kneser`);
* (8.7): $F = (n-1)b^2 + 2(n-1)b + n - 2$ for $b \ge 1$ (`kneser_coeffSum`);
* it is isotropic (`kneser_isotropic`), and every nonzero integral zero has $\max_j\lvert a_j\rvert \ge b^{n-1}/2$ for
  $b \ge 3$ ((8.8)–(8.10), `kneser_large`);
* hence the exponent $(n-1)/2$ of Lemma 8.1 cannot be improved (`aubry_exponent_sharp`).

*Erratum (8.7):* the scan prints $F = n + 2(n-1)b + (n-1)b^2$. The sum of the absolute values of the coefficients of
(8.6) is $n - 2 + 2(n-1)b + (n-1)b^2$ for $b \ge 1$ (the coefficient of $x_1^2$, Cassels' indexing, is $1 - b^2$, of
absolute value $b^2 - 1$, not $b^2 + 1$). The printed value is an upper bound, which is all the argument needs.
The formulas (8.8)–(8.10) are garbled in the machine-read text; the page image shows them, and they are stated as
printed in `kneser_zero_printed` (`Ch6/Supplement.lean`; the middle expression of (8.10) is false, see the erratum
there). The argument used here: $a_0 \ne 0$,
$A_j = a_j - ba_{j-1}$ satisfies $\sum_j A_j^2 = a_0^2$, hence $\lvert A_j\rvert \le \lvert a_0\rvert$ and
$\lvert a_{n-1}\rvert \ge \lvert a_0\rvert\,(b^{n-1} - b^{n-2} - \cdots - 1)$.
-/
import QuadFormsKB.Literature.Cassels.Ch5.Minkowski

namespace QuadFormsKB.Cassels.Ch6

variable {m : ℕ}

/-- **Kneser's form**, Cassels, Ch. 6, (8.6), p. 87: the symmetric integral matrix of
$f(\vec x) = x_0^2 - \sum_{j=0}^{m}(x_{j+1} - bx_j)^2$ in $m + 2$ variables: diagonal entries $1 - b^2$ (at $0$),
$-(1 + b^2)$ (at $1, \dots, m$) and $-1$ (at $m + 1$); entries $b$ next to the diagonal; $0$ elsewhere. -/
def kneser (m : ℕ) (b : ℤ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℤ :=
  Matrix.of fun i j =>
    if i = j then (if i.val = 0 then 1 - b ^ 2 else if i.val = m + 1 then -1 else -(1 + b ^ 2))
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then b else 0

/-- Sum over pairs with `j = i + 1` is the sum over `k` of the `(k, k+1)` terms. -/
lemma kneser_sum_up (g h : Fin (m + 2) → ℤ) :
    ∑ i, ∑ j, (if i.val + 1 = j.val then g i * h j else 0) =
      ∑ k : Fin (m + 1), g k.castSucc * h k.succ := by
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ k : Fin (m + 1), ∑ j : Fin (m + 2),
      (if (k.castSucc).val + 1 = j.val then g k.castSucc * h j else 0) = g k.castSucc * h k.succ := by
    intro k
    rw [Finset.sum_eq_single k.succ]
    · simp
    · intro j _ hj
      rw [ite_eq_right_iff]
      intro h
      exact absurd (Fin.ext (by simp at h ⊢; omega)) hj
    · simp
  have h2 : ∑ j : Fin (m + 2),
      (if (Fin.last (m + 1)).val + 1 = j.val then g (Fin.last _) * h j else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [ite_eq_right_iff]
    intro h
    have := j.isLt
    simp at h
    omega
  simp only [h1, h2, add_zero]

/-- Sum over pairs with `i = j + 1` is the sum over `k` of the `(k+1, k)` terms. -/
lemma kneser_sum_down (g h : Fin (m + 2) → ℤ) :
    ∑ i, ∑ j, (if j.val + 1 = i.val then g i * h j else 0) =
      ∑ k : Fin (m + 1), g k.succ * h k.castSucc := by
  rw [Fin.sum_univ_succ]
  have h1 : ∀ k : Fin (m + 1), ∑ j : Fin (m + 2),
      (if j.val + 1 = (k.succ).val then g k.succ * h j else 0) = g k.succ * h k.castSucc := by
    intro k
    rw [Finset.sum_eq_single k.castSucc]
    · simp
    · intro j _ hj
      rw [ite_eq_right_iff]
      intro h
      exact absurd (Fin.ext (by simp at h ⊢; omega)) hj
    · simp
  have h2 : ∑ j : Fin (m + 2), (if j.val + 1 = (0 : Fin (m + 2)).val then g 0 * h j else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [ite_eq_right_iff]
    intro h
    simp at h
  simp only [h1, h2, zero_add]

/-- **Cassels, Ch. 6, (8.6), p. 87**: Kneser's form is $f(\vec x) = x_0^2 - \sum_{j=0}^{m}(x_{j+1} - bx_j)^2$. -/
@[kb "cassels1978" "Ch. 6, §8, (8.6), p. 87"]
theorem qv_kneser (b : ℤ) (x : Fin (m + 2) → ℤ) :
    qv (kneser m b) x = x 0 ^ 2 - ∑ j : Fin (m + 1), (x j.succ - b * x j.castSucc) ^ 2 := by
  have key : ∀ i j : Fin (m + 2), kneser m b i j * x i * x j =
      (if i = j then (-(1 + b ^ 2) + (if i = 0 then 2 else 0) + (if i = Fin.last _ then b ^ 2 else 0))
        * x i * x j else 0)
      + (if i.val + 1 = j.val then b * x i * x j else 0)
      + (if j.val + 1 = i.val then b * x i * x j else 0) := by
    intro i j
    simp only [kneser, Matrix.of_apply, Fin.ext_iff, Fin.val_zero, Fin.val_last]
    split_ifs <;> first | ring1 | (exfalso; omega)
  have e1 : ∑ i, ∑ j, (if i.val + 1 = j.val then b * x i * x j else 0) =
      ∑ k : Fin (m + 1), b * x k.castSucc * x k.succ := kneser_sum_up (fun i => b * x i) x
  have e2 : ∑ i, ∑ j, (if j.val + 1 = i.val then b * x i * x j else 0) =
      ∑ k : Fin (m + 1), b * x k.succ * x k.castSucc := kneser_sum_down (fun i => b * x i) x
  have hd : ∀ i : Fin (m + 2), (-(1 + b ^ 2) + (if i = 0 then 2 else 0) + (if i = Fin.last _ then b ^ 2 else 0))
      * x i * x i = -(1 + b ^ 2) * x i ^ 2 + (if i = 0 then 2 * x 0 ^ 2 else 0)
        + (if i = Fin.last _ then b ^ 2 * x (Fin.last _) ^ 2 else 0) := by
    intro i
    by_cases h0 : i = 0 <;> by_cases hl : i = Fin.last _ <;> simp [h0, hl] <;> ring
  have e0 : ∑ i, ∑ j, (if i = j then (-(1 + b ^ 2) + (if i = 0 then 2 else 0)
      + (if i = Fin.last _ then b ^ 2 else 0)) * x i * x j else 0) =
      -(1 + b ^ 2) * ∑ i, x i ^ 2 + 2 * x 0 ^ 2 + b ^ 2 * x (Fin.last _) ^ 2 := by
    have : ∀ i : Fin (m + 2), ∑ j, (if i = j then (-(1 + b ^ 2) + (if i = 0 then 2 else 0)
      + (if i = Fin.last _ then b ^ 2 else 0)) * x i * x j else 0) =
      (-(1 + b ^ 2) + (if i = 0 then 2 else 0) + (if i = Fin.last _ then b ^ 2 else 0))
        * x i * x i := by
      intro i
      simp
    simp only [this, hd, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hS0 : ∑ k : Fin (m + 1), x k.succ ^ 2 = ∑ i, x i ^ 2 - x 0 ^ 2 := by
    rw [Fin.sum_univ_succ (fun i => x i ^ 2)]
    ring
  have hSl : ∑ k : Fin (m + 1), x k.castSucc ^ 2 = ∑ i, x i ^ 2 - x (Fin.last _) ^ 2 := by
    rw [Fin.sum_univ_castSucc (fun i => x i ^ 2)]
    ring
  have hR : ∑ j : Fin (m + 1), (x j.succ - b * x j.castSucc) ^ 2 =
      ∑ k : Fin (m + 1), x k.succ ^ 2 - 2 * ∑ k : Fin (m + 1), b * x k.succ * x k.castSucc
        + b ^ 2 * ∑ k : Fin (m + 1), x k.castSucc ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hP : ∑ k : Fin (m + 1), b * x k.castSucc * x k.succ =
      ∑ k : Fin (m + 1), b * x k.succ * x k.castSucc :=
    Finset.sum_congr rfl fun k _ => by ring
  unfold qv
  simp only [key, Finset.sum_add_distrib]
  rw [e0, e1, e2, hR, hS0, hSl, hP]
  ring

/-- Elementary: `|kneser m b i j|` as a sum of indicator pieces (for `b ≥ 1`). -/
lemma kneser_abs_entry (b : ℤ) (hb : 1 ≤ b) (i j : Fin (m + 2)) :
    |kneser m b i j| = (if i = j then ((1 + b ^ 2) + (if i = 0 then -2 else 0)
      + (if i = Fin.last _ then -b ^ 2 else 0)) else 0)
      + (if i.val + 1 = j.val then b else 0) + (if j.val + 1 = i.val then b else 0) := by
  have hb2 : 1 ≤ b ^ 2 := by nlinarith
  simp only [kneser, Matrix.of_apply, Fin.ext_iff, Fin.val_zero, Fin.val_last]
  split_ifs <;> first
    | (exfalso; omega)
    | ring1
    | (rw [abs_of_nonneg (by nlinarith)]; ring1)
    | (rw [abs_of_nonpos (by nlinarith)]; ring1)

/-- **Cassels, Ch. 6, (8.7), p. 87** (corrected, see the module docstring): for $b \ge 1$ the sum of the absolute
values of the coefficients of Kneser's form in $n = m + 2$ variables is $(n-1)b^2 + 2(n-1)b + n - 2$. -/
@[kb "cassels1978" "Ch. 6, §8, (8.7), p. 87 (corrected)"]
theorem kneser_coeffSum (b : ℤ) (hb : 1 ≤ b) :
    ∑ i, ∑ j, |kneser m b i j| = (m + 1) * b ^ 2 + 2 * (m + 1) * b + m := by
  have e1 : ∑ i : Fin (m + 2), ∑ j : Fin (m + 2), (if i.val + 1 = j.val then b else 0) =
      (m + 1) * b := by
    simpa using kneser_sum_up (fun _ => b) (fun _ => (1 : ℤ))
  have e2 : ∑ i : Fin (m + 2), ∑ j : Fin (m + 2), (if j.val + 1 = i.val then b else 0) =
      (m + 1) * b := by
    simpa using kneser_sum_down (fun _ => b) (fun _ => (1 : ℤ))
  have e0 : ∑ i : Fin (m + 2), ∑ j : Fin (m + 2), (if i = j then ((1 + b ^ 2) +
      (if i = 0 then -2 else 0) + (if i = Fin.last _ then -b ^ 2 else 0)) else 0) =
      (m + 2) * (1 + b ^ 2) - 2 - b ^ 2 := by
    simp [Finset.sum_add_distrib]
    ring
  simp only [kneser_abs_entry b hb, Finset.sum_add_distrib]
  rw [e0, e1, e2]
  ring

/-- Kneser's form is isotropic: $(1, b + 1, b(b+1), \dots, b^{m}(b + 1))$ is a zero. -/
@[kb "cassels1978" "Ch. 6, §8, (8.6), p. 87 (the form is isotropic)"]
theorem kneser_isotropic (b : ℤ) : ∃ a : Fin (m + 2) → ℤ, a ≠ 0 ∧ qv (kneser m b) a = 0 := by
  refine ⟨Fin.cons 1 (fun j : Fin (m + 1) => b ^ j.val * (b + 1)), ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp at this
  · rw [qv_kneser, Fin.sum_univ_succ]
    simp
    apply Finset.sum_eq_zero
    intro x _
    rw [pow_succ]
    ring

/-- **Cassels, Ch. 6, (8.8)–(8.10), p. 87**: for $b \ge 3$, every nonzero integral zero $\vec a$ of Kneser's form in
$n = m + 2$ variables has a coordinate with $2\lvert a_j\rvert \ge b^{n-1}$ (namely $j = n - 1$). -/
@[kb "cassels1978" "Ch. 6, §8, (8.8)–(8.10), p. 87"]
theorem kneser_large (b : ℤ) (hb : 3 ≤ b) (a : Fin (m + 2) → ℤ) (ha : a ≠ 0) (hz : qv (kneser m b) a = 0) :
    b ^ (m + 1) ≤ 2 * |a (Fin.last (m + 1))| := by
  have hq := qv_kneser b a
  rw [hz] at hq
  have hsum : ∑ j : Fin (m + 1), (a j.succ - b * a j.castSucc) ^ 2 = a 0 ^ 2 := by linarith
  have hA : ∀ j : Fin (m + 1), |a j.succ - b * a j.castSucc| ≤ |a 0| := by
    intro j
    have : (a j.succ - b * a j.castSucc) ^ 2 ≤ a 0 ^ 2 := by
      rw [← hsum]
      exact Finset.single_le_sum (f := fun j : Fin (m + 1) => (a j.succ - b * a j.castSucc) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    exact sq_le_sq.mp this
  have ha0 : a 0 ≠ 0 := by
    intro h0
    apply ha
    have hz' : ∀ j : Fin (m + 1), a j.succ = b * a j.castSucc := by
      intro j
      have h1 := hA j
      rw [h0, abs_zero] at h1
      have := abs_nonpos_iff.mp h1
      linarith
    have hall : ∀ k (hk : k < m + 2), a ⟨k, hk⟩ = 0 := by
      intro k
      induction k with
      | zero => intro hk; exact h0
      | succ k ih =>
        intro hk
        have h1 := hz' ⟨k, by omega⟩
        change a ⟨k + 1, hk⟩ = b * a ⟨k, by omega⟩ at h1
        rw [h1, ih (by omega)]
        simp
    funext i
    exact hall i.val i.isLt
  have inv : ∀ k (hk : k < m + 2), (b - 1) * |a ⟨k, hk⟩| ≥ |a 0| * ((b - 2) * b ^ k + 1) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h1 : (⟨0, hk⟩ : Fin (m + 2)) = 0 := rfl
      rw [h1, pow_zero]
      nlinarith [abs_nonneg (a 0)]
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := hA ⟨k, by omega⟩
      change |a ⟨k + 1, hk⟩ - b * a ⟨k, by omega⟩| ≤ |a 0| at h2
      have h3 : b * |a ⟨k, by omega⟩| - |a 0| ≤ |a ⟨k + 1, hk⟩| := by
        have h4 := abs_sub_abs_le_abs_sub (b * a ⟨k, by omega⟩) (a ⟨k + 1, hk⟩)
        rw [abs_mul, abs_of_nonneg (by omega : 0 ≤ b), abs_sub_comm] at h4
        linarith
      have h4 := mul_le_mul_of_nonneg_left h3 (by omega : (0 : ℤ) ≤ b - 1)
      have h5 := mul_le_mul_of_nonneg_left h1 (by omega : (0 : ℤ) ≤ b)
      rw [pow_succ]
      nlinarith
  have h1 := inv (m + 1) (by omega)
  have hP : 0 ≤ b ^ (m + 1) := by positivity
  have h0 : 1 ≤ |a 0| := Int.one_le_abs ha0
  have h6 : |a 0| * ((b - 2) * b ^ (m + 1) + 1) ≥ (b - 2) * b ^ (m + 1) + 1 := by
    have : 0 ≤ (b - 2) * b ^ (m + 1) + 1 := by nlinarith
    nlinarith
  have h7 : (b - 1) * b ^ (m + 1) ≤ (b - 1) * (2 * |a (Fin.last (m + 1))|) := by
    have h8 : (b - 1) * |a ⟨m + 1, by omega⟩| ≥ (b - 2) * b ^ (m + 1) + 1 := le_trans h6 h1
    have h9 : (b - 3) * b ^ (m + 1) ≥ 0 := mul_nonneg (by omega) hP
    change _ ≤ (b - 1) * (2 * |a ⟨m + 1, by omega⟩|)
    nlinarith
  exact le_of_mul_le_mul_left h7 (by omega)

/-- **Cassels, Ch. 6, Note to Lemma 8.1, p. 87** (Kneser): *the exponent $(n-1)/2$ in Lemma 8.1 cannot be improved*:
for $n \ge 2$, every exponent $\gamma < (n-1)/2$ and every constant $C$ there is an isotropic integral form (Kneser's
form (8.6) with $b$ large) all of whose nonzero integral zeros $\vec a$ have $\max_j\lvert a_j\rvert > CF^\gamma$. -/
@[kb "cassels1978" "Ch. 6, §8, Note to Lemma 8.1, p. 87 (the exponent cannot be improved)"]
theorem aubry_exponent_sharp (γ : ℝ) (hγ : γ < ((m + 2 : ℕ) - 1 : ℝ) / 2) (C : ℝ) :
    ∃ F : Matrix (Fin (m + 2)) (Fin (m + 2)) ℤ, (∀ i j, F i j = F j i) ∧ F ≠ 0 ∧
      (∃ a : Fin (m + 2) → ℤ, a ≠ 0 ∧ qv F a = 0) ∧
      ∀ a : Fin (m + 2) → ℤ, a ≠ 0 → qv F a = 0 →
        ∃ j, C * (∑ i, ∑ k, |(F i k : ℝ)|) ^ γ < |(a j : ℝ)| := by
  have hm : 2 * γ < (m : ℝ) + 1 := by push_cast at hγ; linarith
  have hγ' : 2 * max γ 0 < (m : ℝ) + 1 := by
    rcases max_cases γ 0 with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hC' : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hK : 0 < (4 * ((m : ℝ) + 1)) := by positivity
  have he : 0 < ((m : ℝ) + 1) - 2 * max γ 0 := by linarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop he).eventually_gt_atTop (2 * max C 1 * (4 * ((m : ℝ) + 1)) ^ max γ 0))
  have hbx : max N 3 ≤ ((⌈max N 3⌉ : ℤ) : ℝ) := Int.le_ceil _
  have hb3 : (3 : ℤ) ≤ ⌈max N 3⌉ := by
    have : (3 : ℝ) ≤ ((⌈max N 3⌉ : ℤ) : ℝ) := le_trans (le_max_right _ _) hbx
    exact_mod_cast this
  generalize ⌈max N 3⌉ = b at hbx hb3
  have hb3r : (3 : ℝ) ≤ b := by exact_mod_cast hb3
  have hbpos : (0 : ℝ) < b := by linarith
  have hbe := hN b (le_trans (le_max_left _ _) hbx)
  refine ⟨kneser m b, ?_, ?_, kneser_isotropic b, ?_⟩
  · intro i j
    by_cases h : i = j
    · rw [h]
    · simp [kneser, h, Ne.symm h, or_comm]
  · intro h
    have h00 : kneser m b 0 0 = 1 - b ^ 2 := by simp [kneser]
    have := congrFun (congrFun h 0) 0
    rw [h00] at this
    simp only [Matrix.zero_apply] at this
    nlinarith
  · intro a ha hz
    refine ⟨Fin.last _, ?_⟩
    have hl := kneser_large b hb3 a ha hz
    have hl' : (b : ℝ) ^ (m + 1) ≤ 2 * |(a (Fin.last _) : ℝ)| := by
      have := (Int.cast_le (R := ℝ)).mpr hl
      push_cast at this
      exact this
    have hS := kneser_coeffSum (m := m) b (by omega)
    have hS' := congrArg (Int.cast : ℤ → ℝ) hS
    push_cast at hS'
    rw [hS']
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    have hS1 : 1 ≤ ((m : ℝ) + 1) * (b : ℝ) ^ 2 + 2 * ((m : ℝ) + 1) * b + m := by nlinarith
    have hS2 : ((m : ℝ) + 1) * (b : ℝ) ^ 2 + 2 * ((m : ℝ) + 1) * b + m
        ≤ (4 * ((m : ℝ) + 1)) * (b : ℝ) ^ 2 := by nlinarith
    generalize ((m : ℝ) + 1) * (b : ℝ) ^ 2 + 2 * ((m : ℝ) + 1) * b + m = S at hS1 hS2 ⊢
    have hSpos : 0 < S := by linarith
    have t1 : C * S ^ γ ≤ max C 1 * S ^ γ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hSpos.le _)
    have t2 : S ^ γ ≤ S ^ max γ 0 := Real.rpow_le_rpow_of_exponent_le hS1 (le_max_left _ _)
    have t3 : S ^ max γ 0 ≤ (4 * ((m : ℝ) + 1) * (b : ℝ) ^ 2) ^ max γ 0 :=
      Real.rpow_le_rpow hSpos.le hS2 (le_max_right _ _)
    have t4 : (4 * ((m : ℝ) + 1) * (b : ℝ) ^ 2) ^ max γ 0
        = (4 * ((m : ℝ) + 1)) ^ max γ 0 * (b : ℝ) ^ (2 * max γ 0) := by
      rw [Real.mul_rpow hK.le (by positivity)]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hbpos.le]
      norm_num
    have t5 : (b : ℝ) ^ (m + 1) = (b : ℝ) ^ (2 * max γ 0) * (b : ℝ) ^ (((m : ℝ) + 1) - 2 * max γ 0) := by
      rw [← Real.rpow_add hbpos, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    have tpos : 0 < (b : ℝ) ^ (2 * max γ 0) := Real.rpow_pos_of_pos hbpos _
    have t6 := mul_lt_mul_of_pos_left hbe tpos
    have t7 : max C 1 * S ^ γ ≤ max C 1 * ((4 * ((m : ℝ) + 1)) ^ max γ 0 * (b : ℝ) ^ (2 * max γ 0)) := by
      apply mul_le_mul_of_nonneg_left _ hC'.le
      rw [← t4]
      exact le_trans t2 t3
    nlinarith

end QuadFormsKB.Cassels.Ch6
