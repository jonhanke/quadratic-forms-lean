/-
# Hanke 2005, §4.2: the coefficient ball of $\varphi_v$ in block coordinates

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

For $X = (X_1\mid X_2)$ ($X_1$ the first $q$ columns, $X_2$ the last $r$), the condition
$\|\Phi(X) - c_\varphi\|_\infty\le\varepsilon$ of the Leray limit (coefficient coordinates) splits into the three block
conditions ${}^tX_1\varphi X_1\in\mathrm{boxD}_q(\varepsilon)$, ${}^tX_1\varphi X_2\in\mathrm{box}_{12}(\varepsilon)$ and
$-{}^tX_2\varphi X_2\in\mathrm{boxD}_r(\varepsilon)$ (`mem_closedBall_iff_boxes`); and a symmetric matrix with
$|M_{ij} - \delta_{ij}|\le\varepsilon < 1/r$ is positive definite (`posDef_of_near_one`).
-/
import QuadFormsKB.Literature.Hanke2005.ArchChartReal
import QuadFormsKB.Literature.Hanke2005.ArchInnerReal

open MeasureTheory Matrix Set
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchReal

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa.ArchVol

variable {q r : ℕ}

/-! ### Splitting the upper index pairs of `Fin (q + r)` -/

/-- $(a, b)\mapsto(a, b)$, both in the first block. -/
def e11 (p : UIdx q) : UIdx (q + r) := ⟨(Fin.castAdd r p.1.1, Fin.castAdd r p.1.2),
  Fin.le_iff_val_le_val.mpr (by simp only [Fin.coe_castAdd]; exact Fin.le_iff_val_le_val.mp p.2)⟩

/-- $(a, c)\mapsto(a, q + c)$. -/
def e12 (a : Fin q) (c : Fin r) : UIdx (q + r) := ⟨(Fin.castAdd r a, Fin.natAdd q c),
  Fin.le_iff_val_le_val.mpr (by simp only [Fin.coe_castAdd, Fin.coe_natAdd]; have := a.isLt; omega)⟩

/-- $(c, d)\mapsto(q + c, q + d)$, both in the second block. -/
def e22 (p : UIdx r) : UIdx (q + r) := ⟨(Fin.natAdd q p.1.1, Fin.natAdd q p.1.2),
  Fin.le_iff_val_le_val.mpr (by simp only [Fin.coe_natAdd]; have := Fin.le_iff_val_le_val.mp p.2; omega)⟩

theorem forall_UIdx_add {P : UIdx (q + r) → Prop} :
    (∀ p, P p) ↔ (∀ p : UIdx q, P (e11 p)) ∧ (∀ a c, P (e12 a c)) ∧ (∀ p : UIdx r, P (e22 p)) := by
  refine ⟨fun h => ⟨fun p => h _, fun a c => h _, fun p => h _⟩, fun ⟨h1, h2, h3⟩ p => ?_⟩
  obtain ⟨⟨i, j⟩, hij⟩ := p
  revert hij
  refine Fin.addCases (fun a => ?_) (fun c => ?_) i <;> refine Fin.addCases (fun b => ?_) (fun d => ?_) j
  · intro hij; dsimp only at hij
    exact h1 ⟨(a, b), show a ≤ b from Fin.le_iff_val_le_val.mpr (by
      have h' := Fin.le_iff_val_le_val.mp hij; simp only [Fin.coe_castAdd] at h'; exact h')⟩
  · intro hij; exact h2 a d
  · intro hij; exfalso; dsimp only at hij
    have := Fin.le_iff_val_le_val.mp hij; simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
    have := b.isLt; omega
  · intro hij; dsimp only at hij
    exact h3 ⟨(c, d), show c ≤ d from Fin.le_iff_val_le_val.mpr (by
      have h' := Fin.le_iff_val_le_val.mp hij; simp only [Fin.coe_natAdd] at h'; omega)⟩

theorem wt_e11 (p : UIdx q) : wt (e11 (r := r) p) = wt p := by
  simp [wt, e11, Fin.castAdd_inj]

theorem wt_e12 (a : Fin q) (c : Fin r) : wt (e12 a c) = 2 := by
  have : (Fin.castAdd r a) ≠ Fin.natAdd q c := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  simp [wt, e12, this]

theorem wt_e22 (p : UIdx r) : wt (e22 (q := q) p) = wt p := by
  simp [wt, e22, Fin.natAdd_inj]

/-! ### The ball in block coordinates -/

theorem phiR_eq_phiQR (r t : ℕ) : phiR r t = phiQR (r + t) r := rfl

theorem gramMatrixR_phiQ' (r t : ℕ) : gramMatrixR (phiQ r t) = phiQR (r + t) r := gramMatrixR_phiQ

theorem phiQR_apply (i j : Fin (q + r)) : phiQR q r i j = if i = j then sgnQR q r i else 0 := by
  simp [phiQR, diagonal_apply]

/-- **The coefficient ball in block coordinates.** -/
theorem mem_closedBall_iff_boxes {r t : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (X1 : Fin (r + t) → Fin (r + t + r) → ℝ)
    (X2 : Fin r → Fin (r + t + r) → ℝ) :
    pullCoeff (phiQ r t) (Fin.append X1 X2) ∈ Metric.closedBall (coeffU (phiQ r t)) ε ↔
      gramH (phiQR (r + t) r) X1 ∈ boxD (r + t) ε ∧
        (fun a c => X1 a ⬝ᵥ (phiQR (r + t) r *ᵥ X2 c)) ∈ box12 (r + t) r ε ∧
        gramH (-phiQR (r + t) r) X2 ∈ boxD r ε := by
  rw [Metric.mem_closedBall, dist_pi_le_iff hε, pullCoeff_eq, coeffU_eq, gramMatrixR_phiQ', forall_UIdx_add]
  simp only [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (wt_pos _)]
  have key : ∀ (w x y : ℝ), 0 < w → (w * |x - y| ≤ ε ↔ |x - y| ≤ ε / w) := fun w x y hw => by
    rw [le_div_iff₀ hw, mul_comm]
  refine and_congr ?_ (and_congr ?_ ?_)
  · rw [mem_boxD]
    refine forall_congr' fun p => ?_
    rw [key _ _ _ (wt_pos _), wt_e11]
    simp only [e11, Fin.append_left, gramH, phiQR_apply, Fin.castAdd_inj, idU]
    by_cases h : p.1.1 = p.1.2 <;> simp [h, sgnQR]
  · simp only [box12, Set.mem_setOf_eq]
    refine forall_congr' fun a => forall_congr' fun c => ?_
    rw [key _ _ _ (wt_pos _), wt_e12]
    have : (Fin.castAdd r a : Fin (r + t + r)) ≠ Fin.natAdd (r + t) c := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    simp only [e12, Fin.append_left, Fin.append_right, phiQR_apply, this, if_false, sub_zero]
  · rw [mem_boxD]
    refine forall_congr' fun p => ?_
    rw [key _ _ _ (wt_pos _), wt_e22]
    simp only [e22, Fin.append_right, gramH, phiQR_apply, Fin.natAdd_inj, idU, Matrix.neg_mulVec,
      dotProduct_neg]
    by_cases h : p.1.1 = p.1.2
    · simp only [h, if_true, sgnQR, Fin.addCases_right]
      rw [show -(X2 p.1.2 ⬝ᵥ (phiQR (r + t) r *ᵥ X2 p.1.2)) - 1 = -((X2 p.1.2 ⬝ᵥ (phiQR (r + t) r *ᵥ X2 p.1.2)) - -1)
        by ring, abs_neg]
    · simp [h]

/-! ### Near the identity a symmetric matrix is positive definite -/

theorem posDef_of_near_one {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ} (hM : Mᵀ = M) {ε : ℝ}
    (hε : ε * k < 1) (h : ∀ i j, |M i j - (1 : Matrix (Fin k) (Fin k) ℝ) i j| ≤ ε) : M.PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hM]
  · simp only [star_trivial]
    obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := by
      by_contra hc; push Not at hc; exact hx (funext hc)
    have hε0 : 0 ≤ ε := (abs_nonneg _).trans (h i₀ i₀)
    have hsplit : x ⬝ᵥ (M *ᵥ x) = x ⬝ᵥ x + x ⬝ᵥ ((M - 1) *ᵥ x) := by
      rw [sub_mulVec, one_mulVec, dotProduct_sub]; ring
    have hbound : |x ⬝ᵥ ((M - 1) *ᵥ x)| ≤ ε * (∑ i, |x i|) ^ 2 := by
      simp only [dotProduct, mulVec, Matrix.sub_apply]
      calc |∑ i, x i * ∑ j, (M i j - (1 : Matrix (Fin k) (Fin k) ℝ) i j) * x j|
          ≤ ∑ i, |x i| * ∑ j, ε * |x j| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            rw [abs_mul]
            refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun j _ => ?_)) (abs_nonneg _)
            rw [abs_mul]; exact mul_le_mul_of_nonneg_right (h i j) (abs_nonneg _)
        _ = ε * (∑ i, |x i|) ^ 2 := by
            simp_rw [← Finset.mul_sum]
            rw [← Finset.sum_mul]; ring
    have hcs : (∑ i, |x i|) ^ 2 ≤ k * (x ⬝ᵥ x) := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |x i|)
      simpa [dotProduct, Finset.card_univ, sq_abs, ← sq] using this
    have hpos : 0 < x ⬝ᵥ x := by simpa using (dotProduct_star_self_pos_iff (v := x)).mpr hx
    have h1 : ε * (∑ i, |x i|) ^ 2 ≤ ε * k * (x ⬝ᵥ x) := by
      calc ε * (∑ i, |x i|) ^ 2 ≤ ε * (k * (x ⬝ᵥ x)) := mul_le_mul_of_nonneg_left hcs hε0
        _ = ε * k * (x ⬝ᵥ x) := by ring
    have h2 := neg_abs_le (x ⬝ᵥ ((M - 1) *ᵥ x))
    rw [hsplit]
    nlinarith

end QuadFormsKB.Hanke2005.ArchReal
