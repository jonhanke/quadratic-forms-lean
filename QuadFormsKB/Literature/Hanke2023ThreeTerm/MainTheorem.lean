import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2023ThreeTerm.Reduction
import QuadFormsKB.Literature.Hanke2023ThreeTerm.Irrational
import QuadFormsKB.Literature.Hanke2023ThreeTerm.NonTrivialRelation

/-!
# Saha–Hanke, Theorem 1.1: all three-term linear relations among binary theta series

Source: R. Saha and J. Hanke, *On three-term linear relations for theta series of positive-definite
binary quadratic forms*, arXiv:2307.00747v1 (bib key `hanke2023threeterm`), Theorem 1.1, p. 2,
with its proof in §5–§6.

If $Q_1, Q_2, Q_3$ are positive definite integral binary forms and $\alpha_1 \theta_{Q_1} +
\alpha_2 \theta_{Q_2} + \alpha_3 \theta_{Q_3} = 0$ with $\alpha_i \in \mathbb{R}$, then up to
reordering exactly one of the following holds:
1. (degenerate) all $\alpha_i = 0$;
2. (trivial 2-term) $\alpha_1 = -\alpha_2 \ne 0$, $\alpha_3 = 0$, $Q_1 \sim_{\mathbb{Z}} Q_2$;
3. (trivial 3-term) all $\alpha_i \ne 0$, $\alpha_1 + \alpha_2 + \alpha_3 = 0$,
   $Q_1 \sim_{\mathbb{Z}} Q_2 \sim_{\mathbb{Z}} Q_3$;
4. (non-trivial) $6\alpha_1 = 3\alpha_2 = -2\alpha_3 \ne 0$ and $Q_1 \sim c(x^2+xy+y^2)$,
   $Q_2 \sim 4c(x^2+xy+y^2)$, $Q_3 \sim c(x^2+3y^2)$ for some integer $c > 0$.

Indices are 0-based here: $Q_1, Q_2, Q_3$ are `Q 0`, `Q 1`, `Q 2`.

## Status
* Proved: the reduction to normalized rational relations (Lemma 5.1, Remark 5.4), Lemma 3.3, the
  cases $a + b = 1$ (§6.1) and $a + b \ge 4$ (Lemma 6.4), the non-trivial relation (Lemma 6.2),
  and the assembly below.
* `RefinementResults`: the statement of the computer results of §6.2 ($a + b = 2$) and §6.3
  ($a + b = 3$), obtained in the source by running the Extended Refinement Algorithm in SageMath.
  They are proved in `RefinementProof.lean` (`refinementResults`) by a case tree checked by `omega`;
  `theorem_1_1_of_refinement` here takes them as a hypothesis, `theorem_1_1` there is unconditional.
-/

namespace QuadFormsKB.Hanke2023ThreeTerm

open QuadFormsKB QuadFormsKB.Siegel

/-- **The results of §6.2 and §6.3, as a statement** (proved: `refinementResults`) (the Extended Refinement Algorithm
runs for $a + b = 2$ and $a + b = 3$). For reduced integral binary forms $Q_1, Q_2, Q_3$:
* §6.2: if $\frac12 \theta_{Q_1} + \frac12 \theta_{Q_2} = \theta_{Q_3}$ then $Q_1 = Q_2 = Q_3$;
* §6.3: if $\frac13 \theta_{Q_1} + \frac23 \theta_{Q_2} = \theta_{Q_3}$ then either
  $Q_1 = Q_2 = Q_3$, or $(Q_1, Q_2, Q_3) = (c(x^2+xy+y^2), 4c(x^2+xy+y^2), c(x^2+3y^2))$ for some
  integer $c > 0$ (the ray $\mathbb{R}_{\ge 0}\vec v$ found at iteration 4).

The source establishes these by computer (SageMath implementation of §5.3; tables on pp. 16–17).
*Update (proof gap):* for $a + b = 3$ the table shows three non-empty refined
cones remaining after the 13th iteration (`MAX_ITERATIONS`), and the text only analyzes the unique
non-empty cone after iteration 4; it does not say why the remaining cones contain no other
solutions. The statement itself is correct: `refinementResults` (`RefinementProof.lean`) proves it with a case tree
whose every leaf is checked by Lean. Theta relations are coefficientwise (`ThetaRelation3`). -/
@[kb "hanke2023threeterm" "§6.2 and §6.3, pp. 16–17"]
structure RefinementResults : Prop where
  ab11 : ∀ {Q₁ Q₂ Q₃ : BinQF}, IsReduced Q₁ → IsReduced Q₂ → IsReduced Q₃ →
    ThetaRelation3 Q₁ Q₂ Q₃ (1 / 2) (1 / 2) (-1) → Q₁ = Q₂ ∧ Q₂ = Q₃
  ab12 : ∀ {Q₁ Q₂ Q₃ : BinQF}, IsReduced Q₁ → IsReduced Q₂ → IsReduced Q₃ →
    ThetaRelation3 Q₁ Q₂ Q₃ (1 / 3) (2 / 3) (-1) →
      (Q₁ = Q₂ ∧ Q₂ = Q₃) ∨
        ∃ c : ℤ, 0 < c ∧ Q₁ = formE c ∧ Q₂ = formE (4 * c) ∧ Q₃ = formF c

/-- Case 1 of Theorem 1.1 (degenerate solutions): all $\alpha_i = 0$. -/
def IsDegenerate (α : Fin 3 → ℝ) : Prop := ∀ i, α i = 0

/-- Case 2 of Theorem 1.1 (trivial 2-term solutions): $\alpha_1 = -\alpha_2 \ne 0$, $\alpha_3 = 0$,
$Q_1 \sim_{\mathbb{Z}} Q_2$ ($Q_3$ arbitrary). -/
def IsTrivialTwoTerm (Q : Fin 3 → BinQF) (α : Fin 3 → ℝ) : Prop :=
  α 0 = -α 1 ∧ α 0 ≠ 0 ∧ α 2 = 0 ∧ IntEquiv (Q 0) (Q 1)

/-- Case 3 of Theorem 1.1 (trivial 3-term solutions): all $\alpha_i \ne 0$, $\sum \alpha_i = 0$,
$Q_1 \sim_{\mathbb{Z}} Q_2 \sim_{\mathbb{Z}} Q_3$. -/
def IsTrivialThreeTerm (Q : Fin 3 → BinQF) (α : Fin 3 → ℝ) : Prop :=
  (∀ i, α i ≠ 0) ∧ α 0 + α 1 + α 2 = 0 ∧ IntEquiv (Q 0) (Q 1) ∧ IntEquiv (Q 1) (Q 2)

/-- Case 4 of Theorem 1.1 (non-trivial 3-term solutions): $6\alpha_1 = 3\alpha_2 = -2\alpha_3 \ne 0$,
$Q_1 \sim_{\mathbb{Z}} c(x^2+xy+y^2)$, $Q_2 \sim_{\mathbb{Z}} 4c(x^2+xy+y^2)$,
$Q_3 \sim_{\mathbb{Z}} c(x^2+3y^2)$ for some integer $c > 0$. -/
def IsNonTrivial (Q : Fin 3 → BinQF) (α : Fin 3 → ℝ) : Prop :=
  6 * α 0 = 3 * α 1 ∧ 3 * α 1 = -2 * α 2 ∧ α 0 ≠ 0 ∧
    ∃ c : ℤ, 0 < c ∧ IntEquiv (Q 0) (formE c) ∧ IntEquiv (Q 1) (formE (4 * c)) ∧
      IntEquiv (Q 2) (formF c)

/-- One of the four cases of Theorem 1.1. -/
def SolutionType (Q : Fin 3 → BinQF) (α : Fin 3 → ℝ) : Prop :=
  IsDegenerate α ∨ IsTrivialTwoTerm Q α ∨ IsTrivialThreeTerm Q α ∨ IsNonTrivial Q α

/-- The relation $\sum_i \alpha_i r_{Q_i}(m) = 0$ for all $m$, indexed by `Fin 3`. -/
def Rel (Q : Fin 3 → BinQF) (α : Fin 3 → ℝ) : Prop :=
  ∀ m : ℕ, ∑ i, α i * repNum (Q i) m = 0

lemma rel_iff (Q : Fin 3 → BinQF) (α : Fin 3 → ℝ) :
    Rel Q α ↔ ThetaRelation3 (Q 0) (Q 1) (Q 2) (α 0) (α 1) (α 2) := by
  simp [Rel, ThetaRelation3, Fin.sum_univ_three]

lemma rel_perm (Q : Fin 3 → BinQF) (α : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) (h : Rel Q α) :
    Rel (Q ∘ σ) (α ∘ σ) := fun m => by
  simpa using (Equiv.sum_comp σ (fun i => α i * repNum (Q i) m)).trans (h m)

/-- All three forms equivalent and all coefficients non-zero: case 3. -/
lemma case3_of {Q : Fin 3 → BinQF} {α : Fin 3 → ℝ} (hs : α 0 + α 1 + α 2 = 0)
    (h0 : α 0 ≠ 0) (h1 : α 1 ≠ 0) (h2 : α 2 ≠ 0) {R : BinQF}
    (e0 : IntEquiv (Q 0) R) (e1 : IntEquiv (Q 1) R) (e2 : IntEquiv (Q 2) R) :
    SolutionType Q α :=
  Or.inr (Or.inr (Or.inl ⟨fun i => by fin_cases i <;> assumption, hs, e0.trans e1.symm,
    e1.trans e2.symm⟩))

/-- Case analysis with the "isolated" coefficient in position 2: $\alpha_3 \ne 0$ and
$\alpha_1 \alpha_3 \le 0$, $\alpha_2 \alpha_3 \le 0$. -/
theorem core (hR : RefinementResults) (Q : Fin 3 → BinQF) (hQ : ∀ i, IntQF.PosDef (Q i))
    (α : Fin 3 → ℝ) (h : Rel Q α) (hs : α 0 + α 1 + α 2 = 0) (h2 : α 2 ≠ 0)
    (h02 : α 0 * α 2 ≤ 0) (h12 : α 1 * α 2 ≤ 0) :
    ∃ σ : Equiv.Perm (Fin 3), SolutionType (Q ∘ σ) (α ∘ σ) := by
  classical
  -- reduced representatives
  choose R hRred hQR using fun i => exists_reduced_equiv (hQ i)
  have hrR : ∀ i m, repNum (Q i) m = repNum (R i) m := fun i m => repNum_eq_of_intEquiv (hQR i) m
  have hRel : ∀ m : ℕ, α 0 * repNum (R 0) m + α 1 * repNum (R 1) m + α 2 * repNum (R 2) m = 0 :=
    fun m => by have := h m; simp only [Fin.sum_univ_three, hrR] at this; exact this
  -- the normalized coefficient q = -α₀/α₂ ∈ [0, 1]
  set q : ℝ := -α 0 / α 2 with hqdef
  have hα0 : α 0 = -q * α 2 := by rw [hqdef]; field_simp
  have hα1 : α 1 = -(1 - q) * α 2 := by linear_combination hs - hα0
  have hq0 : 0 ≤ q := by
    rw [hqdef, neg_div, neg_nonneg, div_nonpos_iff]
    rcases lt_or_gt_of_ne h2 with h | h
    · left; exact ⟨by nlinarith, h.le⟩
    · right; exact ⟨by nlinarith, h.le⟩
  have hq1 : q ≤ 1 := by
    have e : α 1 * α 2 = -((1 - q) * (α 2 * α 2)) := by rw [hα1]; ring
    have hp : 0 < α 2 * α 2 := mul_self_pos.2 h2
    by_contra hc; push Not at hc
    have : (1 - q) * (α 2 * α 2) < 0 := mul_neg_of_neg_of_pos (by linarith) hp
    linarith
  -- the normalized relation q r₀ + (1 - q) r₁ = r₂ for the reduced forms
  have hnorm : ∀ m : ℕ, q * repNum (R 0) m + (1 - q) * repNum (R 1) m = repNum (R 2) m := by
    intro m
    have := hRel m
    rw [hα0, hα1] at this
    have : α 2 * (q * repNum (R 0) m + (1 - q) * repNum (R 1) m - repNum (R 2) m) = 0 := by
      linear_combination -this
    have := (mul_eq_zero.1 this).resolve_left h2
    linarith
  by_cases hrat : ∃ r : ℚ, (r : ℝ) = q
  swap
  · -- irrational ratio: Lemma 5.1 gives equal theta series, so all forms are equivalent
    push Not at hrat
    have hirr : HasIrrationalRatio (α 0) (α 1) (α 2) := by
      refine ⟨0, 2, h2, ?_⟩
      intro ⟨r, hr⟩
      apply hrat (-r)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons] at hr
      push_cast; rw [hr, hqdef]; ring
    obtain ⟨e01, e12⟩ := irrational_three_term (hQ 0) (hQ 1) (hQ 2)
      ((rel_iff Q α).1 h) hirr
    have hq0' : q ≠ 0 := fun h0 => hrat 0 (by simp [h0])
    have hq1' : q ≠ 1 := fun h1 => hrat 1 (by simp [h1])
    have R01 : R 0 = R 2 := reduced_eq_of_theta_eq (hRred 0) (hRred 2) fun m => by
      rw [← hrR, ← hrR, e01, e12]
    have R12 : R 1 = R 2 := reduced_eq_of_theta_eq (hRred 1) (hRred 2) fun m => by
      rw [← hrR, ← hrR, e12]
    refine ⟨1, ?_⟩
    simp only [Equiv.Perm.coe_one, Function.comp_id]
    refine case3_of hs ?_ ?_ h2 (hQR 0 |>.trans (R01 ▸ IsometricGL.refl _))
      (hQR 1 |>.trans (R12 ▸ IsometricGL.refl _)) (hQR 2)
    · rw [hα0]; exact mul_ne_zero (neg_ne_zero.2 hq0') h2
    · rw [hα1]; exact mul_ne_zero (neg_ne_zero.2 (sub_ne_zero.2 hq1'.symm)) h2
  obtain ⟨r, hr⟩ := hrat
  -- write r = a / (a + b) with a, b coprime naturals
  have hr0 : 0 ≤ r := by exact_mod_cast hr ▸ hq0
  set a : ℕ := r.num.toNat with ha
  set n : ℕ := r.den with hn
  have hnum : (r.num : ℤ) = a := by rw [ha]; exact (Int.toNat_of_nonneg (Rat.num_nonneg.2 hr0)).symm
  have han : a ≤ n := by
    have hr1 : r ≤ 1 := by exact_mod_cast hr ▸ hq1
    have := Rat.num_le_denom_iff.2 hr1
    omega
  set b : ℕ := n - a with hb
  have hab : a + b = n := by omega
  have hnpos : 0 < n := r.den_pos
  have hcop : Nat.Coprime a b := by
    have hc : Nat.Coprime a n := by
      have h1 := r.reduced
      have h2 : r.num.natAbs = a := by omega
      rw [h2] at h1; exact h1
    rw [hb]
    exact Nat.coprime_sub_self_right han |>.2 hc
  have hqab : q = (a : ℝ) / (a + b) := by
    rw [← hr]
    have : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by exact_mod_cast (Rat.num_div_den r).symm
    rw [this, hnum, ← hn]; push_cast; rw [← hab]; push_cast; ring_nf
  have h1q : 1 - q = (b : ℝ) / (a + b) := by
    have hpos : (0 : ℝ) < a + b := by exact_mod_cast (show 0 < a + b by omega)
    rw [hqab]; field_simp; ring
  have hthR : ThetaRelation3 (R 0) (R 1) (R 2) ((a : ℝ) / (a + b)) ((b : ℝ) / (a + b)) (-1) :=
    fun m => by rw [← hqab, ← h1q]; linarith [hnorm m]
  have hα0' : α 0 = -((a : ℝ) / (a + b)) * α 2 := by rw [hα0, hqab]
  have hα1' : α 1 = -((b : ℝ) / (a + b)) * α 2 := by rw [hα1, h1q]
  have eqR : ∀ {i j : Fin 3}, R i = R j → IntEquiv (Q i) (Q j) := fun {i j} e =>
    (hQR i).trans (e ▸ (hQR j).symm)
  rcases (show n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with hn1 | hn2 | hn3 | hn4
  · -- a + b = 1: a two-term relation
    rcases (show (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) by omega) with ⟨ha1, hb0⟩ | ⟨ha0, hb1⟩
    · have e : ∀ m : ℕ, repNum (R 0) m = repNum (R 2) m := fun m => by
        have := hthR m; rw [ha1, hb0] at this; push_cast at this; norm_num at this
        exact_mod_cast (by linarith : (repNum (R 0) m : ℝ) = repNum (R 2) m)
      have R02 := reduced_eq_of_theta_eq (hRred 0) (hRred 2) e
      have a0 : α 0 = -α 2 := by rw [hα0']; rw [ha1, hb0]; push_cast; ring
      have a1 : α 1 = 0 := by rw [hα1']; rw [ha1, hb0]; push_cast; ring
      refine ⟨Equiv.swap 1 2, Or.inr (Or.inl ?_)⟩
      simp only [IsTrivialTwoTerm, Function.comp_apply, Equiv.swap_apply_def]
      norm_num
      exact ⟨a0, by rw [a0]; exact neg_ne_zero.2 h2, a1, eqR R02⟩
    · have e : ∀ m : ℕ, repNum (R 1) m = repNum (R 2) m := fun m => by
        have := hthR m; rw [ha0, hb1] at this; push_cast at this; norm_num at this
        exact_mod_cast (by linarith : (repNum (R 1) m : ℝ) = repNum (R 2) m)
      have R12 := reduced_eq_of_theta_eq (hRred 1) (hRred 2) e
      have a0 : α 0 = 0 := by rw [hα0']; rw [ha0, hb1]; push_cast; ring
      have a1 : α 1 = -α 2 := by rw [hα1']; rw [ha0, hb1]; push_cast; ring
      refine ⟨Equiv.swap 0 2 * Equiv.swap 0 1, Or.inr (Or.inl ?_)⟩
      simp only [IsTrivialTwoTerm, Function.comp_apply, Equiv.Perm.mul_apply,
        Equiv.swap_apply_def]
      norm_num
      exact ⟨a1, by rw [a1]; exact neg_ne_zero.2 h2, a0, eqR R12⟩
  · -- a + b = 2: (a, b) = (1, 1), the computer result of §6.2
    have ha1 : a = 1 := by
      rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with h | h | h
      · rw [h, show b = 2 by omega] at hcop; norm_num at hcop
      · exact h
      · rw [h, show b = 0 by omega] at hcop; norm_num at hcop
    have hb1 : b = 1 := by omega
    have hrel : ThetaRelation3 (R 0) (R 1) (R 2) (1 / 2) (1 / 2) (-1) := fun m => by
      have := hthR m; rw [ha1, hb1] at this; push_cast at this; norm_num at this ⊢; linarith
    obtain ⟨e01, e12⟩ := hR.ab11 (hRred 0) (hRred 1) (hRred 2) hrel
    refine ⟨1, ?_⟩
    simp only [Equiv.Perm.coe_one, Function.comp_id]
    refine case3_of hs ?_ ?_ h2 (eqR (e01.trans e12)) (eqR e12) (IsometricGL.refl _)
    · rw [hα0', ha1, hb1]; push_cast; norm_num; exact h2
    · rw [hα1', ha1, hb1]; push_cast; norm_num; exact h2
  · -- a + b = 3: (a, b) = (1, 2) or (2, 1), the computer result of §6.3
    rcases (show (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) by
      rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 by omega) with h | h | h | h
      · rw [h, show b = 3 by omega] at hcop; norm_num at hcop
      · left; omega
      · right; omega
      · rw [h, show b = 0 by omega] at hcop; norm_num at hcop) with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have hrel : ThetaRelation3 (R 0) (R 1) (R 2) (1 / 3) (2 / 3) (-1) := fun m => by
        have := hthR m; rw [ha, hb] at this; push_cast at this; norm_num at this ⊢; linarith
      have a0 : α 0 = -(1 / 3) * α 2 := by rw [hα0', ha, hb]; push_cast; norm_num
      have a1 : α 1 = -(2 / 3) * α 2 := by rw [hα1', ha, hb]; push_cast; norm_num
      rcases hR.ab12 (hRred 0) (hRred 1) (hRred 2) hrel with ⟨e01, e12⟩ | ⟨c, hc, e0, e1, e2⟩
      · refine ⟨1, ?_⟩
        simp only [Equiv.Perm.coe_one, Function.comp_id]
        refine case3_of hs ?_ ?_ h2 (eqR (e01.trans e12)) (eqR e12) (IsometricGL.refl _)
        · rw [a0]; exact mul_ne_zero (by norm_num) h2
        · rw [a1]; exact mul_ne_zero (by norm_num) h2
      · refine ⟨1, Or.inr (Or.inr (Or.inr ?_))⟩
        simp only [IsNonTrivial, Equiv.Perm.coe_one, Function.comp_id]
        refine ⟨by rw [a0, a1]; ring, by rw [a1]; ring, by rw [a0]; exact mul_ne_zero (by norm_num) h2,
          c, hc, e0 ▸ hQR 0, e1 ▸ hQR 1, e2 ▸ hQR 2⟩
    · have hrel : ThetaRelation3 (R 1) (R 0) (R 2) (1 / 3) (2 / 3) (-1) := fun m => by
        have := hthR m; rw [ha, hb] at this; push_cast at this; norm_num at this ⊢; linarith
      have a0 : α 0 = -(2 / 3) * α 2 := by rw [hα0', ha, hb]; push_cast; norm_num
      have a1 : α 1 = -(1 / 3) * α 2 := by rw [hα1', ha, hb]; push_cast; norm_num
      rcases hR.ab12 (hRred 1) (hRred 0) (hRred 2) hrel with ⟨e10, e02⟩ | ⟨c, hc, e1, e0, e2⟩
      · refine ⟨1, ?_⟩
        simp only [Equiv.Perm.coe_one, Function.comp_id]
        refine case3_of hs ?_ ?_ h2 (eqR e02) (eqR (e10.trans e02)) (IsometricGL.refl _)
        · rw [a0]; exact mul_ne_zero (by norm_num) h2
        · rw [a1]; exact mul_ne_zero (by norm_num) h2
      · refine ⟨Equiv.swap 0 1, Or.inr (Or.inr (Or.inr ?_))⟩
        simp only [IsNonTrivial, Function.comp_apply, Equiv.swap_apply_def]
        norm_num
        refine ⟨by rw [a0, a1]; ring, by rw [a0]; ring, by rw [a1]; exact mul_ne_zero (by norm_num) h2,
          c, hc, e1 ▸ hQR 1, e0 ▸ hQR 0, e2 ▸ hQR 2⟩
  · -- a + b ≥ 4: Lemma 6.4
    have hab4 : 4 ≤ a + b := by omega
    have ha1 : 1 ≤ a := by
      by_contra h0; push Not at h0
      have : a = 0 := by omega
      rw [this, Nat.coprime_zero_left] at hcop; omega
    have hb1 : 1 ≤ b := by
      by_contra h0; push Not at h0
      have : b = 0 := by omega
      rw [this, Nat.coprime_zero_right] at hcop; omega
    obtain ⟨e01, e12⟩ := reduced_diagonal_of_ge_four hcop hab4 (hRred 0) (hRred 1) (hRred 2) hthR
    have hpos : (0 : ℝ) < a + b := by exact_mod_cast (show 0 < a + b by omega)
    refine ⟨1, ?_⟩
    simp only [Equiv.Perm.coe_one, Function.comp_id]
    refine case3_of hs ?_ ?_ h2 (eqR (e01.trans e12)) (eqR e12) (IsometricGL.refl _)
    · rw [hα0']
      refine mul_ne_zero (neg_ne_zero.2 (div_ne_zero ?_ hpos.ne')) h2
      exact_mod_cast (show a ≠ 0 by omega)
    · rw [hα1']
      refine mul_ne_zero (neg_ne_zero.2 (div_ne_zero ?_ hpos.ne')) h2
      exact_mod_cast (show b ≠ 0 by omega)

lemma isolated_aux {x y z : ℝ} (hs : x + y + z = 0) (hx : x ^ 2 ≤ z ^ 2) (hy : y ^ 2 ≤ z ^ 2)
    (hne : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) : z ≠ 0 ∧ x * z ≤ 0 ∧ y * z ≤ 0 := by
  have hz : z ≠ 0 := by
    intro h0
    rw [h0] at hx hy
    have : x = 0 := by nlinarith [sq_nonneg x]
    have : y = 0 := by nlinarith [sq_nonneg y]
    rcases hne with h | h | h <;> contradiction
  refine ⟨hz, ?_, ?_⟩
  · have : y = -x - z := by linarith
    rw [this] at hy; nlinarith [sq_nonneg x]
  · have : x = -y - z := by linarith
    rw [this] at hx; nlinarith [sq_nonneg y]

/-- Three reals with sum $0$, not all $0$: some $\alpha_k \ne 0$ has sign opposite (weakly) to
both others (take $k$ with $\alpha_k^2$ maximal). -/
lemma exists_isolated (α : Fin 3 → ℝ) (hs : α 0 + α 1 + α 2 = 0) (hne : ¬ ∀ i, α i = 0) :
    (α 2 ≠ 0 ∧ α 0 * α 2 ≤ 0 ∧ α 1 * α 2 ≤ 0) ∨ (α 0 ≠ 0 ∧ α 2 * α 0 ≤ 0 ∧ α 1 * α 0 ≤ 0) ∨
      (α 1 ≠ 0 ∧ α 0 * α 1 ≤ 0 ∧ α 2 * α 1 ≤ 0) := by
  have hne' : α 0 ≠ 0 ∨ α 1 ≠ 0 ∨ α 2 ≠ 0 := by
    by_contra h; push Not at h; exact hne fun i => by fin_cases i <;> simp [h.1, h.2.1, h.2.2]
  rcases le_total (α 0 ^ 2) (α 2 ^ 2) with h02 | h02 <;>
    rcases le_total (α 1 ^ 2) (α 2 ^ 2) with h12 | h12
  · exact Or.inl (isolated_aux hs h02 h12 hne')
  · -- α 1 is maximal
    exact Or.inr (Or.inr (isolated_aux (x := α 0) (y := α 2) (by linarith) (h02.trans h12) h12
      (by tauto)))
  · rcases le_total (α 1 ^ 2) (α 0 ^ 2) with h10 | h10
    · exact Or.inr (Or.inl (isolated_aux (x := α 2) (y := α 1) (by linarith) h02 h10
        (by tauto)))
    · exact Or.inr (Or.inr (isolated_aux (x := α 0) (y := α 2) (by linarith) h10
        (h02.trans h10) (by tauto)))
  · rcases le_total (α 1 ^ 2) (α 0 ^ 2) with h10 | h10
    · exact Or.inr (Or.inl (isolated_aux (x := α 2) (y := α 1) (by linarith) h02 h10
        (by tauto)))
    · exact Or.inr (Or.inr (isolated_aux (x := α 0) (y := α 2) (by linarith) h10 h12
        (by tauto)))

/-- **Theorem 1.1 (three-term linear relations among binary theta series).** Let
$Q_1, Q_2, Q_3$ (`Q 0`, `Q 1`, `Q 2`) be positive definite integral binary quadratic forms and
$\alpha_1, \alpha_2, \alpha_3 \in \mathbb{R}$ with $\alpha_1 \theta_{Q_1} + \alpha_2 \theta_{Q_2} +
\alpha_3 \theta_{Q_3} = 0$ (coefficientwise). Then, after reordering the indices by some
permutation $\sigma$, one of the four cases holds: degenerate, trivial 2-term, trivial 3-term, or
the non-trivial relation $\frac13 \theta_{Q_1} + \frac23 \theta_{Q_2} = \theta_{Q_3}$ with
$Q_1 \sim c(x^2+xy+y^2)$, $Q_2 \sim 4c(x^2+xy+y^2)$, $Q_3 \sim c(x^2+3y^2)$
(`SolutionType`). That at most one case holds is `solutionType_exclusive`.

Here from `RefinementResults` (the results for $a + b \in \{2, 3\}$, which the source obtains by
computer); `RefinementResults` is proved (`refinementResults`, `RefinementProof.lean`), and the unconditional
form is `theorem_1_1` there. -/
theorem theorem_1_1_of_refinement (hR : RefinementResults) (Q : Fin 3 → BinQF) (hQ : ∀ i, IntQF.PosDef (Q i))
    (α : Fin 3 → ℝ) (h : ThetaRelation3 (Q 0) (Q 1) (Q 2) (α 0) (α 1) (α 2)) :
    ∃ σ : Equiv.Perm (Fin 3), SolutionType (Q ∘ σ) (α ∘ σ) := by
  have hrel := (rel_iff Q α).2 h
  have hs : α 0 + α 1 + α 2 = 0 := by
    have := h 0
    simpa [repNum_zero (hQ 0), repNum_zero (hQ 1), repNum_zero (hQ 2)] using this
  by_cases hz : ∀ i, α i = 0
  · exact ⟨1, Or.inl fun i => by simp [hz i]⟩
  rcases exists_isolated α hs hz with ⟨h2, h02, h12⟩ | ⟨h0, h20, h10⟩ | ⟨h1, h01, h21⟩
  · exact core hR Q hQ α hrel hs h2 h02 h12
  · -- isolated index 0: move it to position 2
    obtain ⟨σ, hσ⟩ := core hR (Q ∘ Equiv.swap 0 2) (fun i => hQ _) (α ∘ Equiv.swap 0 2)
      (rel_perm Q α _ hrel) (by simp [Equiv.swap_apply_def]; linarith)
      (by simpa [Equiv.swap_apply_def] using h0)
      (by simpa [Equiv.swap_apply_def] using h20)
      (by simpa [Equiv.swap_apply_def] using h10)
    exact ⟨Equiv.swap 0 2 * σ, by simpa [Function.comp_assoc] using hσ⟩
  · obtain ⟨σ, hσ⟩ := core hR (Q ∘ Equiv.swap 1 2) (fun i => hQ _) (α ∘ Equiv.swap 1 2)
      (rel_perm Q α _ hrel) (by simp [Equiv.swap_apply_def]; linarith)
      (by simpa [Equiv.swap_apply_def] using h1)
      (by simpa [Equiv.swap_apply_def] using h01)
      (by simpa [Equiv.swap_apply_def] using h21)
    exact ⟨Equiv.swap 1 2 * σ, by simpa [Function.comp_assoc] using hσ⟩

end QuadFormsKB.Hanke2023ThreeTerm
