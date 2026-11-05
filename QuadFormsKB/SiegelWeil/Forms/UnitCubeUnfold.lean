/-
# Unfolding integrals over the unit cube

Let $J$ be a finite index set and $C = (0,1]^J \subset \mathbb{R}^J$ the half-open unit cube.  The
translates $C + n$, $n \in \mathbb{Z}^J$, are pairwise disjoint and cover $\mathbb{R}^J$.  Hence:

* every $x \in \mathbb{R}^J$ has an integer translate in $C$ (`exists_int_add_mem_unitCube`);
* for measurable $f \ge 0$:
  $\sum_{n \in \mathbb{Z}^J} \int_C f(t+n)\,dt = \int_{\mathbb{R}^J} f$ (`lintegral_unitCube_unfold`);
* for integrable $h : \mathbb{R}^J \to \mathbb{C}$, the family $n \mapsto \int_C h(t+n)\,dt$ is summable
  with sum $\int_{\mathbb{R}^J} h$ (`hasSum_integral_unitCube_unfold`), and likewise for $\|h\|$
  (`summable_integral_norm_unitCube`).
-/
import QuadFormsKB.HilbertModular.QExpansion
open MeasureTheory Set
set_option linter.unusedSectionVars false
noncomputable section
namespace QuadFormsKB.SiegelWeil.Forms
open QuadFormsKB.HilbertModular

variable {J : Type*} [Fintype J]

/-- Every real vector has an integer translate in the half-open unit cube $(0,1]^J$. -/
theorem exists_int_add_mem_unitCube (x : J → ℝ) :
    ∃ n : J → ℤ, x + (fun j => (n j : ℝ)) ∈ unitCube J := by
  refine ⟨fun j => -(⌈x j⌉ - 1), fun j => ?_⟩
  simp only [Pi.add_apply, Int.cast_neg, Int.cast_sub, Int.cast_one, mem_Ioc]
  have h1 := Int.ceil_lt_add_one (x j)
  have h2 := Int.le_ceil (x j)
  constructor <;> linarith

/-- The translate region $S_n = \{x \mid x - n \in C\}$. -/
private def cell (n : J → ℤ) : Set (J → ℝ) :=
  (fun x => x - (fun j => (n j : ℝ))) ⁻¹' unitCube J

private lemma measurableSet_cell (n : J → ℤ) : MeasurableSet (cell n) :=
  (measurable_id.sub_const _) (measurableSet_unitCube)

private lemma pairwise_disjoint_cell : Pairwise (Function.onFun Disjoint (cell (J := J))) := by
  intro m n hmn
  rw [Function.onFun, Set.disjoint_left]
  intro x hm hn
  apply hmn
  funext j
  have a := hm j
  have b := hn j
  simp only [Pi.sub_apply, mem_Ioc] at a b
  have h1 : ((m j : ℤ) : ℝ) < (n j : ℝ) + 1 := by linarith [a.1, a.2, b.1, b.2]
  have h2 : ((n j : ℤ) : ℝ) < (m j : ℝ) + 1 := by linarith [a.1, a.2, b.1, b.2]
  have h1' : m j < n j + 1 := by exact_mod_cast h1
  have h2' : n j < m j + 1 := by exact_mod_cast h2
  omega

private lemma iUnion_cell : ⋃ n : J → ℤ, cell n = univ := by
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨n, hn⟩ := exists_int_add_mem_unitCube x
  refine mem_iUnion.2 ⟨fun j => -n j, ?_⟩
  have e : (x - fun j => (((-n j : ℤ)) : ℝ)) = x + fun j => (n j : ℝ) := by
    funext j; simp [sub_eq_add_neg]
  show (x - fun j => (((-n j : ℤ)) : ℝ)) ∈ unitCube J
  rw [e]; exact hn

private lemma setLIntegral_cell (f : (J → ℝ) → ENNReal) (hf : Measurable f) (n : J → ℤ) :
    ∫⁻ x in cell n, f x = ∫⁻ t in unitCube J, f (t + fun j => (n j : ℝ)) := by
  have hmp := measurePreserving_sub_right (volume : Measure (J → ℝ)) (fun j => (n j : ℝ))
  have := hmp.setLIntegral_comp_preimage measurableSet_unitCube
    (f := fun y => f (y + fun j => (n j : ℝ))) (hf.comp (measurable_id.add_const _))
  simpa [cell] using this

private lemma setIntegral_cell (h : (J → ℝ) → ℂ) (n : J → ℤ) :
    ∫ x in cell n, h x = ∫ t in unitCube J, h (t + fun j => (n j : ℝ)) := by
  have hmp := measurePreserving_sub_right (volume : Measure (J → ℝ)) (fun j => (n j : ℝ))
  have := hmp.setIntegral_preimage_emb (Homeomorph.subRight (fun j => (n j : ℝ))).measurableEmbedding
    (fun y => h (y + fun j => (n j : ℝ))) (unitCube J)
  simpa [cell] using this

/-- Unfolding for nonnegative measurable functions:
$\sum_{n\in\mathbb{Z}^J}\int_C f(t+n)\,dt=\int f$. -/
theorem lintegral_unitCube_unfold (f : (J → ℝ) → ENNReal) (hf : Measurable f) :
    ∑' n : J → ℤ, ∫⁻ t in unitCube J, f (t + fun j => (n j : ℝ)) = ∫⁻ t, f t := by
  have h := lintegral_iUnion (μ := volume) (f := f) measurableSet_cell
    pairwise_disjoint_cell
  rw [iUnion_cell, Measure.restrict_univ] at h
  rw [h]
  exact tsum_congr fun n => (setLIntegral_cell f hf n).symm

/-- Unfolding for integrable complex functions: $n\mapsto\int_C h(t+n)\,dt$ has sum $\int h$. -/
theorem hasSum_integral_unitCube_unfold (h : (J → ℝ) → ℂ) (hh : Integrable h) :
    HasSum (fun n : J → ℤ => ∫ t in unitCube J, h (t + fun j => (n j : ℝ))) (∫ t, h t) := by
  have := hasSum_integral_iUnion (μ := volume) (f := h) measurableSet_cell
    pairwise_disjoint_cell (by rw [iUnion_cell]; exact hh.integrableOn)
  rw [iUnion_cell, Measure.restrict_univ] at this
  simpa only [setIntegral_cell] using this

/-- The norms $n\mapsto\int_C \|h(t+n)\|\,dt$ are summable for integrable $h$. -/
theorem summable_integral_norm_unitCube (h : (J → ℝ) → ℂ) (hh : Integrable h) :
    Summable (fun n : J → ℤ => ∫ t in unitCube J, ‖h (t + fun j => (n j : ℝ))‖) := by
  have := hasSum_integral_unitCube_unfold (fun t => ((‖h t‖ : ℝ) : ℂ))
    (hh.norm.ofReal (𝕜 := ℂ))
  refine Complex.summable_ofReal.1 ?_
  convert this.summable using 2 with n
  exact (integral_ofReal (𝕜 := ℂ)).symm

end QuadFormsKB.SiegelWeil.Forms
