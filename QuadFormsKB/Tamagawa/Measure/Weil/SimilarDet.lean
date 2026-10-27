import QuadFormsKB.Tamagawa.Measure.LerayUnimodular
import QuadFormsKB.Tamagawa.Measure.LerayUnimodularC

/-!
# Similar forms: the Jacobian $c^{n(n+1)/2}\det(b)^{n+1}$ of the coefficient map $q \mapsto c\,(q\circ b)$

The determinant of the congruence action `act b` on the (weighted) coefficient
coordinates of real and complex quadratic forms is $\det(b)^{n+1}$ (`LerayReal.det_act`, `LerayComplex.det_act`, in
`LerayUnimodular.lean`, `LerayUnimodularC.lean`). This file adds:
* `Weil.two_mul_sum_UIdx`, **`Weil.card_UIdx`**: $|\{(i,j) : 0 \le i \le j < n\}| = n(n+1)/2$; `Weil.sum_UIdx_slots`;
* `Weil.det_smul_UIdx`: $\det(r f) = r^{n(n+1)/2}\det f$ on the coefficient space;
* **`LerayReal.det_smul_act`**, **`LerayComplex.det_smul_act`**: $\det(c\cdot\mathrm{act}\,b) = c^{n(n+1)/2}\det(b)^{n+1}$.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open Matrix QuadFormsKB.Tamagawa.ArchVol

namespace QuadFormsKB.Tamagawa.Measure.Weil

variable {n : ℕ} {K : Type*} [Field K] [CharZero K]

/-! ### Counting upper index pairs -/

/-- **Symmetric sums over upper index pairs.** For $f$ symmetric on $\{0,\dots,n-1\}^2$,
$2\sum_{i \le j} f(i,j) = \sum_{i,j} f(i,j) + \sum_i f(i,i)$. -/
theorem two_mul_sum_UIdx (f : Fin n × Fin n → ℕ) (hf : ∀ q, f q.swap = f q) :
    2 * ∑ p : UIdx n, f p.1 = ∑ q, f q + ∑ a, f (a, a) := by
  have h1 : ∑ p : UIdx n, f p.1 = ∑ q : Fin n × Fin n, if q.1 ≤ q.2 then f q else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter fun q : Fin n × Fin n => q.1 ≤ q.2)
      (by simp) f).symm
  have h2 : ∑ q : Fin n × Fin n, (if q.1 ≤ q.2 then f q else 0)
      = ∑ q : Fin n × Fin n, (if q.1 < q.2 then f q else 0)
        + ∑ q : Fin n × Fin n, (if q.1 = q.2 then f q else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rcases lt_trichotomy q.1 q.2 with h | h | h
    · simp [h, h.le, h.ne]
    · simp [h]
    · simp [not_le.mpr h, not_lt.mpr h.le, h.ne']
  have h3 : ∑ q : Fin n × Fin n, (if q.1 ≤ q.2 then 0 else f q)
      = ∑ q : Fin n × Fin n, (if q.1 < q.2 then f q else 0) := by
    rw [← Equiv.sum_comp (Equiv.prodComm (Fin n) (Fin n))]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, hf q]
    by_cases h : q.1 < q.2
    · simp [h, not_le.mpr h]
    · simp [h, not_lt.mp h]
  have h4 : ∑ q : Fin n × Fin n, f q
      = ∑ q : Fin n × Fin n, (if q.1 ≤ q.2 then f q else 0)
        + ∑ q : Fin n × Fin n, (if q.1 ≤ q.2 then 0 else f q) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> simp
  have h5 : ∑ q : Fin n × Fin n, (if q.1 = q.2 then f q else 0) = ∑ a, f (a, a) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp
  rw [h1, h4, h3, h2, h5]; ring

/-- **The number of upper index pairs** is $n(n+1)/2$. -/
theorem card_UIdx (n : ℕ) : Fintype.card (UIdx n) = n * (n + 1) / 2 := by
  have := two_mul_sum_UIdx (n := n) (fun _ => 1) (fun _ => rfl)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, Fintype.card_prod,
    Fintype.card_fin] at this
  symm
  exact Nat.div_eq_of_eq_mul_left (by norm_num) (by linarith)

/-- Each index $i$ occurs in $n+1$ slots of the upper pairs:
$\#\{p : p_1 = i\} + \#\{p : p_2 = i\} = n+1$. -/
theorem sum_UIdx_slots (i : Fin n) :
    ∑ p : UIdx n, ((if p.1.1 = i then 1 else 0) + (if p.1.2 = i then 1 else 0)) = n + 1 := by
  have := two_mul_sum_UIdx (n := n) (fun q => (if q.1 = i then 1 else 0) + (if q.2 = i then 1 else 0))
    (fun q => by simp [add_comm])
  have hA : ∑ q : Fin n × Fin n, ((if q.1 = i then 1 else 0) + (if q.2 = i then 1 else 0)) = 2 * n := by
    rw [Fintype.sum_prod_type]
    simp [Finset.sum_add_distrib, apply_ite Finset.card]
    ring
  have hB : ∑ a : Fin n, ((if (a, a).1 = i then 1 else 0) + (if (a, a).2 = i then 1 else 0)) = 2 := by
    simp [Finset.sum_add_distrib]
  rw [hA, hB] at this
  omega

/-- **Scalar multiples:** $\det(r \cdot f) = r^{n(n+1)/2}\det f$ on $K^{\mathrm{UIdx}\,n}$. -/
theorem det_smul_UIdx (r : K) (f : (UIdx n → K) →ₗ[K] (UIdx n → K)) :
    LinearMap.det (r • f) = r ^ (n * (n + 1) / 2) * LinearMap.det f := by
  rw [LinearMap.det_smul, Module.finrank_fintype_fun_eq_card, card_UIdx]

end QuadFormsKB.Tamagawa.Measure.Weil

namespace QuadFormsKB.Tamagawa.Measure.LerayReal

open QuadFormsKB.Tamagawa.Measure.Weil

variable {n : ℕ}

/-- $\det(r \cdot \mathrm{act}\,b) = r^{n(n+1)/2}\det(b)^{n+1}$. -/
theorem det_smul_act (r : ℝ) (b : Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.det (r • act b) = r ^ (n * (n + 1) / 2) * b.det ^ (n + 1) := by
  rw [det_smul_UIdx, det_act]

end QuadFormsKB.Tamagawa.Measure.LerayReal

namespace QuadFormsKB.Tamagawa.Measure.LerayComplex

open QuadFormsKB.Tamagawa.Measure.Weil

variable {n : ℕ}

/-- $\det(r \cdot \mathrm{act}\,b) = r^{n(n+1)/2}\det(b)^{n+1}$. -/
theorem det_smul_act (r : ℂ) (b : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det (r • act b) = r ^ (n * (n + 1) / 2) * b.det ^ (n + 1) := by
  rw [det_smul_UIdx, det_act]

end QuadFormsKB.Tamagawa.Measure.LerayComplex
