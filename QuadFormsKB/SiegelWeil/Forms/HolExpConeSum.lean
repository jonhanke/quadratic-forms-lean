import Mathlib

/-!
# Exponential sums over the dual cone

**Layer:** pure analysis/combinatorics input for the Fourier expansion of holomorphic Siegel Eisenstein series.

**Results.**
* `summable_exp_dualCone`: if a set $K\subseteq\mathbb R^\iota$ contains the sup-norm ball of radius $\varepsilon>0$ about $y$, and $c>0$,
  then
  $$\sum_{n\in\mathbb Z^\iota,\ n\cdot z\ge 0\ \forall z\in K} e^{-c\,n\cdot y} < \infty.$$
  Indeed, for $n$ in the dual cone, taking $z=y-\varepsilon(\operatorname{sign}n_i)_i\in K$ gives
  $n\cdot y\ge\varepsilon\sum_i|n_i|$, so the term is at most $\prod_i e^{-c\varepsilon|n_i|}$.
* `nonneg_of_forall_pos_add`: if $0\le a+\varepsilon b$ for all $\varepsilon>0$, then $0\le a$.

Sources: elementary; no external source.
-/

namespace QuadFormsKB.SiegelWeil.Forms.HolExp

private theorem summable_prod_fin' {α : Type*} {φ : α → ℝ} (h0 : ∀ x, 0 ≤ φ x) (hs : Summable φ) :
    ∀ n : ℕ, Summable fun x : Fin n → α => ∏ i, φ (x i)
  | 0 => by simpa using (Summable.of_finite (f := fun _ : Fin 0 → α => (1 : ℝ)))
  | n + 1 => by
      have ih := summable_prod_fin' h0 hs n
      have h := Summable.mul_of_nonneg hs ih h0 (fun x => Finset.prod_nonneg fun i _ => h0 _)
      refine ((Fin.consEquiv (fun _ : Fin (n + 1) => α)).summable_iff).mp ?_
      refine h.congr fun p => ?_
      simp only [Function.comp, Fin.prod_univ_succ]
      rfl

private theorem summable_prod_pi' {α : Type*} {ι : Type*} [Fintype ι] {φ : α → ℝ}
    (h0 : ∀ x, 0 ≤ φ x) (hs : Summable φ) : Summable fun x : ι → α => ∏ i, φ (x i) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ((Equiv.arrowCongr e (Equiv.refl α)).symm.summable_iff).mp ?_
  refine (summable_prod_fin' h0 hs (Fintype.card ι)).congr fun x => ?_
  simp only [Function.comp]
  rw [← e.prod_comp]
  simp [Equiv.arrowCongr]

private theorem summable_exp_abs_int {a : ℝ} (ha : 0 < a) :
    Summable fun k : ℤ => Real.exp (-a * |(k : ℝ)|) := by
  have hr : Real.exp (-a) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hg : Summable fun n : ℕ => Real.exp (-a) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le hr
  have key : ∀ n : ℕ, Real.exp (-a * |((n : ℤ) : ℝ)|) = Real.exp (-a) ^ n := by
    intro n
    rw [← Real.exp_nat_mul]; congr 1; simp [abs_of_nonneg]; ring
  refine Summable.of_nat_of_neg ?_ ?_
  · exact hg.congr fun n => (key n).symm
  · refine hg.congr fun n => ?_
    rw [← key n]; simp

open Classical in
/-- Exponential sums over the integer points of the dual cone converge. -/
theorem summable_exp_dualCone {ι : Type*} [Fintype ι] {K : Set (ι → ℝ)} {y : ι → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hball : ∀ z : ι → ℝ, (∀ i, |z i - y i| ≤ ε) → z ∈ K) {c : ℝ} (hc : 0 < c) :
    Summable fun n : ι → ℤ =>
      if (∀ z ∈ K, 0 ≤ ∑ i, (n i : ℝ) * z i) then Real.exp (-c * ∑ i, (n i : ℝ) * y i) else 0 := by
  classical
  have hs := summable_prod_pi' (ι := ι) (fun k : ℤ => (Real.exp_pos (-(c * ε) * |(k : ℝ)|)).le)
    (summable_exp_abs_int (mul_pos hc hε))
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · split_ifs <;> positivity
  · rw [← Real.exp_sum]
    split_ifs with h
    · apply Real.exp_le_exp.mpr
      set z : ι → ℝ := fun i => y i - ε * (if 0 ≤ n i then 1 else -1) with hz
      have hzK : z ∈ K := by
        apply hball
        intro i
        simp only [hz]
        split_ifs <;> simp [abs_of_pos hε]
      have h1 := h z hzK
      have h2 : ∑ i, (n i : ℝ) * z i = ∑ i, (n i : ℝ) * y i - ε * ∑ i, |(n i : ℝ)| := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hz]
        by_cases hi : 0 ≤ n i
        · have : (0 : ℝ) ≤ n i := by exact_mod_cast hi
          simp [hi, abs_of_nonneg this]; ring
        · have : (n i : ℝ) < 0 := by exact_mod_cast not_le.mp hi
          simp [hi, abs_of_neg this]; ring
      have h3 : ∑ i, -(c * ε) * |(n i : ℝ)| = -(c * ε * ∑ i, |(n i : ℝ)|) := by
        rw [← Finset.mul_sum]; ring
      rw [h3]
      have : ε * ∑ i, |(n i : ℝ)| ≤ ∑ i, (n i : ℝ) * y i := by linarith
      nlinarith
    · exact (Real.exp_pos _).le

/-- If $0\le a+\varepsilon b$ for every $\varepsilon>0$, then $0\le a$. -/
theorem nonneg_of_forall_pos_add {a b : ℝ} (h : ∀ ε : ℝ, 0 < ε → 0 ≤ a + ε * b) : 0 ≤ a := by
  by_contra ha
  replace ha := not_le.mp ha
  have hp : 0 < 2 * |b| + 1 := by positivity
  have h1 := h (-a / (2 * |b| + 1)) (div_pos (by linarith) hp)
  have h2 : -a / (2 * |b| + 1) * b ≤ -a / 2 := by
    have hb : b ≤ |b| := le_abs_self b
    have : -a / (2 * |b| + 1) * b ≤ -a / (2 * |b| + 1) * |b| :=
      mul_le_mul_of_nonneg_left hb (div_pos (by linarith) hp).le
    have h3 : -a / (2 * |b| + 1) * |b| ≤ -a / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hp (by norm_num)]
      nlinarith [abs_nonneg b]
    linarith
  linarith

end QuadFormsKB.SiegelWeil.Forms.HolExp
