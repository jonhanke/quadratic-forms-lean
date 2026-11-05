/-
# Coordinates on real symmetric matrices: the trace pairing and the off-diagonal weight

**Layer:** coordinates on the space of real symmetric $r \times r$ matrices, indexed by the upper pairs
$\{(i,j) : 0 \le i \le j < r\}$ (`UIdx r`); indices are 0-based.

**Results.**
* `cU` ($c_{ij}$): the weight $c_{ii} = 1$ and $c_{ij} = 2$ for $i < j$.
* `prod_cU`: $\prod_{i \le j} c_{ij} = 2^{r(r-1)/2}$.
* `sum_sym_eq_sum_UIdx`: for a symmetric array $f$, $\sum_{a,b} f_{ab} = \sum_{i \le j} c_{ij} f_{ij}$.
* `trace_symU_symU`: for symmetric matrices with upper coordinates $t$ and $b$,
  $$\operatorname{tr}(t\,b) = \sum_{i \le j} c_{ij}\,t_{ij}\,b_{ij}.$$
* `scaleU`, `integral_comp_scaleU`, `integrable_comp_scaleU_iff`: the coordinatewise scaling
  $b \mapsto (c_{ij} b_{ij})$ multiplies Lebesgue measure on $\mathbb R^{\{i \le j\}}$ by $2^{-r(r-1)/2}$:
  $$\int F(c \cdot b)\,db = 2^{-r(r-1)/2}\int F(u)\,du,$$
  and $F \circ \text{scaleU}$ is integrable exactly when $F$ is.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarDet

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Matrix Set
open QuadFormsKB.Tamagawa.ArchVol

namespace QuadFormsKB.SiegelWeil.Forms.ArchR

/-- **The off-diagonal weight** $c_{ij}$ of an upper pair: $1$ on the diagonal ($i = j$), $2$ off it ($i < j$). -/
def cU {r : ℕ} (p : UIdx r) : ℝ := if p.1.1 = p.1.2 then 1 else 2

/-- The weight $c_{ij}$ is positive. -/
theorem cU_pos {r : ℕ} (p : UIdx r) : 0 < cU p := by
  unfold cU; split_ifs <;> norm_num

/-- The natural-number identity $r(r+1)/2 - r = r(r-1)/2$. -/
theorem tri_sub (r : ℕ) : r * (r + 1) / 2 - r = r * (r - 1) / 2 := by
  rcases r with _ | r
  · simp
  · have h : (r + 1) * (r + 1 + 1) = (r + 1) * (r + 1 - 1) + 2 * (r + 1) := by
      simp only [Nat.add_sub_cancel]; ring
    rw [h, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    omega

/-- **Product of the weights:** $\prod_{i \le j} c_{ij} = 2^{r(r-1)/2}$. -/
theorem prod_cU (r : ℕ) : ∏ p : UIdx r, cU p = 2 ^ (r * (r - 1) / 2) := by
  have h1 : ∀ p : UIdx r, cU p = if p.1.1 = p.1.2 then 1 else 2 := fun _ => rfl
  simp only [h1]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  have hc : (Finset.univ.filter fun p : UIdx r => ¬ p.1.1 = p.1.2).card
      + (Finset.univ.filter fun p : UIdx r => p.1.1 = p.1.2).card = r * (r + 1) / 2 := by
    rw [add_comm, Finset.card_filter_add_card_filter_not (s := Finset.univ)]
    rw [Finset.card_univ, QuadFormsKB.Tamagawa.Measure.Weil.card_UIdx]
  have hd : (Finset.univ.filter fun p : UIdx r => p.1.1 = p.1.2).card = r := by
    have : (Finset.univ.filter fun p : UIdx r => p.1.1 = p.1.2).card
        = (Finset.univ : Finset (Fin r)).card := by
      refine Finset.card_bij (fun p _ => p.1.1) (fun p _ => Finset.mem_univ _) ?_ ?_
      · intro p hp q hq h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
        exact Subtype.ext (Prod.ext h (hp.symm.trans (h.trans hq)))
      · intro a _
        exact ⟨⟨(a, a), le_rfl⟩, by simp, rfl⟩
    simpa using this
  rw [← tri_sub]
  omega

/-- **Symmetric double sums in upper coordinates:** for a symmetric array $f$,
$\sum_{a,b} f_{ab} = \sum_{i \le j} c_{ij} f_{ij}$. -/
theorem sum_sym_eq_sum_UIdx {r : ℕ} {f : Fin r → Fin r → ℂ} (hf : ∀ a b, f a b = f b a) :
    ∑ a, ∑ b, f a b = ∑ p : UIdx r, (cU p : ℂ) * f p.1.1 p.1.2 := by
  have h1 : ∀ g : Fin r × Fin r → ℂ, ∑ p : UIdx r, g p.1
      = ∑ q : Fin r × Fin r, if q.1 ≤ q.2 then g q else 0 := by
    intro g
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter fun q : Fin r × Fin r => q.1 ≤ q.2)
      (by simp) g).symm
  have hL : ∑ a, ∑ b, f a b = ∑ q : Fin r × Fin r, f q.1 q.2 := by
    rw [Fintype.sum_prod_type]
  have h2 : ∑ q : Fin r × Fin r, f q.1 q.2
      = ∑ q : Fin r × Fin r, (if q.1 ≤ q.2 then f q.1 q.2 else 0)
        + ∑ q : Fin r × Fin r, (if q.2 < q.1 then f q.1 q.2 else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases h : q.1 ≤ q.2
    · simp [h, not_lt.mpr h]
    · simp [h, not_le.mp h]
  have h3 : ∑ q : Fin r × Fin r, (if q.2 < q.1 then f q.1 q.2 else 0)
      = ∑ q : Fin r × Fin r, (if q.1 < q.2 then f q.1 q.2 else 0) := by
    rw [← (Equiv.prodComm (Fin r) (Fin r)).sum_comp]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    by_cases h : q.1 < q.2
    · simp only [h, ite_true]; exact hf _ _
    · simp only [h, ite_false]
  have h4 : ∑ p : UIdx r, (cU p : ℂ) * f p.1.1 p.1.2
      = ∑ p : UIdx r, (fun q : Fin r × Fin r =>
          ((if q.1 = q.2 then (1 : ℂ) else 2) * f q.1 q.2)) p.1 := by
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : p.1.1 = p.1.2 <;> simp [cU, h]
  rw [hL, h2, h3, h4,
    h1 (fun q : Fin r × Fin r => (if q.1 = q.2 then (1 : ℂ) else 2) * f q.1 q.2),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rcases lt_trichotomy q.1 q.2 with h | h | h
  · simp [h, h.le, h.ne]; ring
  · simp [h]
  · simp [not_le.mpr h, not_lt.mpr h.le]

/-- Symmetric matrices from upper coordinates are symmetric: $t_{ji} = t_{ij}$. -/
theorem symU_swap {r : ℕ} (t : UIdx r → ℝ) (i j : Fin r) : symU t j i = symU t i j := by
  unfold symU
  simp only [Matrix.of_apply]
  by_cases h : i ≤ j
  · by_cases h' : j ≤ i
    · have : i = j := le_antisymm h h'
      subst this; rfl
    · simp [h, h']
  · have h' : j ≤ i := le_of_not_ge h
    simp [h, h']

/-- **The trace pairing in coordinates:** $\operatorname{tr}(t\,b) = \sum_{i \le j} c_{ij} t_{ij} b_{ij}$ for
symmetric matrices with upper coordinates $t$ and $b$. -/
theorem trace_symU_symU {r : ℕ} (t b : UIdx r → ℝ) :
    ∑ i, ∑ j, ((symU t i j : ℝ) : ℂ) * ((symU b j i : ℝ) : ℂ)
      = ∑ p, (t p : ℂ) * ((cU p * b p : ℝ) : ℂ) := by
  rw [sum_sym_eq_sum_UIdx (f := fun i j => ((symU t i j : ℝ) : ℂ) * ((symU b j i : ℝ) : ℂ))]
  · refine Finset.sum_congr rfl fun p _ => ?_
    have h1 : symU t p.1.1 p.1.2 = t p := by
      simp [symU, p.2]
    have h2 : symU b p.1.2 p.1.1 = b p := by
      rw [symU_swap]; simp [symU, p.2]
    simp only [h1, h2]
    push_cast
    ring
  · intro a b'
    rw [symU_swap t b' a, symU_swap b a b']

/-- **The coordinate scaling** $b \mapsto (c_{ij} b_{ij})_{i \le j}$ on $\mathbb R^{\{i \le j\}}$. -/
def scaleU (r : ℕ) : (UIdx r → ℝ) → (UIdx r → ℝ) := fun b p => cU p * b p

/-- `scaleU r` as a measurable equivalence (a product of nonzero one-dimensional scalings). -/
def scaleUEquiv (r : ℕ) : (UIdx r → ℝ) ≃ᵐ (UIdx r → ℝ) :=
  MeasurableEquiv.piCongrRight fun p => (Homeomorph.mulLeft₀ (cU p) (cU_pos p).ne').toMeasurableEquiv

/-- The equivalence `scaleUEquiv` is the function `scaleU`. -/
theorem scaleUEquiv_apply (r : ℕ) : ⇑(scaleUEquiv r) = scaleU r := rfl

/-- `scaleU r` is the linear map of the diagonal matrix with entries $c_{ij}$. -/
theorem scaleU_eq_toLin (r : ℕ) :
    scaleU r = ⇑(Matrix.toLin' (Matrix.diagonal (fun p : UIdx r => cU p))) := by
  funext b p
  simp [scaleU, Matrix.mulVec_diagonal]

/-- **Lebesgue measure under the scaling:** the push-forward of Lebesgue measure by `scaleU r` is
$2^{-r(r-1)/2}$ times Lebesgue measure. -/
theorem map_scaleU (r : ℕ) :
    Measure.map (scaleU r) volume
      = ENNReal.ofReal (((2 : ℝ) ^ (r * (r - 1) / 2))⁻¹) • (volume : Measure (UIdx r → ℝ)) := by
  have hdet : (Matrix.diagonal (fun p : UIdx r => cU p)).det = 2 ^ (r * (r - 1) / 2) := by
    rw [Matrix.det_diagonal, prod_cU]
  have hne : (Matrix.diagonal (fun p : UIdx r => cU p)).det ≠ 0 := by
    rw [hdet]; positivity
  rw [scaleU_eq_toLin, Real.map_matrix_volume_pi_eq_smul_volume_pi hne, hdet]
  congr 2
  rw [abs_of_pos (by positivity)]

/-- **Change of variables for the scaling:** $\int F(c \cdot b)\,db = 2^{-r(r-1)/2}\int F(u)\,du$. -/
theorem integral_comp_scaleU {r : ℕ} (F : (UIdx r → ℝ) → ℂ) :
    ∫ b, F (scaleU r b) = (((2 : ℝ) ^ (r * (r - 1) / 2))⁻¹ : ℝ) • ∫ u, F u := by
  have h := (scaleUEquiv r).measurableEmbedding.integral_map (μ := volume) F
  rw [scaleUEquiv_apply, map_scaleU, integral_smul_measure] at h
  rw [← h]
  rw [ENNReal.toReal_ofReal (by positivity)]

/-- **Integrability under the scaling:** $F \circ \mathrm{scaleU}$ is integrable iff $F$ is. -/
theorem integrable_comp_scaleU_iff {r : ℕ} {F : (UIdx r → ℝ) → ℂ} :
    MeasureTheory.Integrable (fun b => F (scaleU r b)) ↔ MeasureTheory.Integrable F := by
  have h := (scaleUEquiv r).measurableEmbedding.integrable_map_iff (μ := volume) (g := F)
  rw [scaleUEquiv_apply, map_scaleU] at h
  have hc : ENNReal.ofReal (((2 : ℝ) ^ (r * (r - 1) / 2))⁻¹) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  rw [Function.comp_def] at h
  rw [← h]
  exact integrable_smul_measure hc ENNReal.ofReal_ne_top

end QuadFormsKB.SiegelWeil.Forms.ArchR
