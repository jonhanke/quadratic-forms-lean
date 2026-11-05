/-
# Hanke 2005, Lemma A7: push-forwards of product measures

Auxiliary measure theory for the fibration identity of Lemma A7 for products of places: if each factor map
$F_i$ pushes $\mu_i$ forward to $c_i\,\nu_i$, then the product map pushes $\bigotimes_i\mu_i$ forward to
$\big(\prod_ic_i\big)\bigotimes_i\nu_i$.

**Proves**
* `map_pi_eq_smul_pi`: $(\prod_i F_i)_*\bigotimes_i\mu_i = \big(\prod_ic_i\big)\bigotimes_i\nu_i$ for finitely many factors;
* `map_prod_eq_smul_prod`: the binary version $(F_1\times F_2)_*(\mu_1\otimes\mu_2) = c_1c_2\,(\nu_1\otimes\nu_2)$.
-/
import Mathlib
import QuadFormsKB.Citation

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace QuadFormsKB.Hanke2005

/-- **Product of push-forward identities** (the fibration identity of Lemma A7 for products of places):
if $(F_i)_*\mu_i = c_i\,\nu_i$ with $c_i\ne\infty$ for every $i$ in a finite index set, then
$(x\mapsto(F_i(x_i))_i)_*\bigotimes_i\mu_i = \big(\prod_ic_i\big)\bigotimes_i\nu_i$. -/
theorem map_pi_eq_smul_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {X Y : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)] {μ : ∀ i, Measure (X i)}
    [∀ i, SigmaFinite (μ i)] {ν : ∀ i, Measure (Y i)} [∀ i, SigmaFinite (ν i)] {F : ∀ i, X i → Y i}
    (hF : ∀ i, Measurable (F i)) {c : ι → ℝ≥0∞} (hc : ∀ i, c i ≠ ⊤)
    (h : ∀ i, (μ i).map (F i) = c i • ν i) :
    (Measure.pi μ).map (fun x i => F i (x i)) = (∏ i, c i) • Measure.pi ν := by
  have hsf : ∀ i, SigmaFinite (c i • ν i) := fun i => by
    rw [← ENNReal.coe_toNNReal (hc i), ← ENNReal.smul_def]
    infer_instance
  rw [Measure.pi_map_pi (hμ := fun i => by rw [h i]; exact hsf i) (fun i => (hF i).aemeasurable)]
  simp only [h]
  refine Measure.pi_eq (μ := fun i => c i • ν i) (μ' := (∏ i, c i) • Measure.pi ν) ?_
  intro s _
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

set_option linter.unusedVariables false in
/-- **Binary version**: if $(F_1)_*\mu_1 = c_1\nu_1$ and $(F_2)_*\mu_2 = c_2\nu_2$ with $c_1, c_2\ne\infty$, then
$(F_1\times F_2)_*(\mu_1\otimes\mu_2) = c_1c_2\,(\nu_1\otimes\nu_2)$. -/
theorem map_prod_eq_smul_prod {X₁ Y₁ X₂ Y₂ : Type*} [MeasurableSpace X₁] [MeasurableSpace Y₁]
    [MeasurableSpace X₂] [MeasurableSpace Y₂] {μ₁ : Measure X₁} {μ₂ : Measure X₂}
    [SigmaFinite μ₁] [SigmaFinite μ₂] {ν₁ : Measure Y₁} {ν₂ : Measure Y₂} [SigmaFinite ν₁]
    [SigmaFinite ν₂] {F₁ : X₁ → Y₁} {F₂ : X₂ → Y₂} (h₁ : Measurable F₁) (h₂ : Measurable F₂)
    {c₁ c₂ : ℝ≥0∞} (hc₁ : c₁ ≠ ⊤) (hc₂ : c₂ ≠ ⊤) (e₁ : μ₁.map F₁ = c₁ • ν₁)
    (e₂ : μ₂.map F₂ = c₂ • ν₂) :
    (μ₁.prod μ₂).map (Prod.map F₁ F₂) = (c₁ * c₂) • (ν₁.prod ν₂) := by
  rw [← Measure.map_prod_map μ₁ μ₂ h₁ h₂, e₁, e₂, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul]

end QuadFormsKB.Hanke2005
