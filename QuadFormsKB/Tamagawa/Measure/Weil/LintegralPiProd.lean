import Mathlib

/-!
# Tonelli for products over a finite product measure

**Generic, Mathlib-only (upstreamable).** For σ-finite measures $\mu_i$ on finitely many spaces $X_i$ and measurable
$f_i : X_i\to[0,\infty]$,
$$\int^-\prod_i f_i(x_i)\,d\Big(\prod_i\mu_i\Big)(x) = \prod_i\int^- f_i\,d\mu_i$$
(**`lintegral_pi_prod`**; Mathlib has the Bochner version `MeasureTheory.integral_fintype_prod_eq_prod`).
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

universe u

theorem lintegral_pi_prod_fin :
    ∀ (n : ℕ) {α : Fin n → Type u} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
      (f : ∀ i, α i → ℝ≥0∞), (∀ i, Measurable (f i)) →
      ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ y, f i y ∂μ i
  | 0, α, _, μ, _, f, _ => by
    simp only [Finset.univ_eq_empty, Finset.prod_empty, lintegral_const, one_mul]
    rw [Measure.pi_univ]; simp
  | n + 1, α, _, μ, _, f, hf => by
    have hmp := measurePreserving_piFinSuccAbove μ 0
    set e := MeasurableEquiv.piFinSuccAbove α 0
    have hg : (fun x : ∀ i, α i => ∏ i, f i (x i)) =
        (fun z : α 0 × (∀ j : Fin n, α (Fin.succAbove 0 j)) => f 0 z.1 * ∏ j, f (Fin.succAbove 0 j) (z.2 j)) ∘ e := by
      funext x
      simp only [Function.comp_apply, e, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv,
        Fin.prod_univ_succAbove _ 0]
      rfl
    set G := fun z : α 0 × (∀ j : Fin n, α (Fin.succAbove 0 j)) => f 0 z.1 * ∏ j, f (Fin.succAbove 0 j) (z.2 j)
    calc ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∫⁻ x, G (e x) ∂Measure.pi μ := by rw [hg]; rfl
      _ = ∫⁻ z, G z ∂(Measure.pi μ).map e := (lintegral_map_equiv G e).symm
      _ = ∫⁻ z, G z ∂((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) := by rw [hmp.map_eq]
      _ = (∫⁻ y, f 0 y ∂μ 0) * ∫⁻ z, ∏ j, f (Fin.succAbove 0 j) (z j) ∂Measure.pi fun j => μ (Fin.succAbove 0 j) :=
          lintegral_prod_mul (hf 0).aemeasurable
            (Finset.measurable_prod _ fun j _ => (hf _).comp (measurable_pi_apply j)).aemeasurable
      _ = ∏ i, ∫⁻ y, f i y ∂μ i := by
          rw [lintegral_pi_prod_fin n (fun j => μ (Fin.succAbove 0 j)) (fun j => f (Fin.succAbove 0 j))
            (fun j => hf _), Fin.prod_univ_succAbove (fun i => ∫⁻ y, f i y ∂μ i) 0]

/-- **Tonelli for a product of functions over `Measure.pi`.** -/
theorem lintegral_pi_prod {ι : Type*} [Fintype ι] {α : ι → Type u} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (f : ∀ i, α i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ y, f i y ∂μ i := by
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hmp := measurePreserving_piCongrLeft μ e
  rw [← hmp.map_eq, lintegral_map_equiv (fun x : ∀ i, α i => ∏ i, f i (x i))]
  have h1 : (fun y : ∀ i', α (e i') => ∏ i, f i (MeasurableEquiv.piCongrLeft α e y i)) =
      fun y => ∏ i', f (e i') (y i') := by
    funext y
    rw [← e.prod_comp]
    refine Finset.prod_congr rfl fun i' _ => ?_
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  rw [h1, lintegral_pi_prod_fin _ (fun i' => μ (e i')) (fun i' => f (e i')) (fun i' => hf _)]
  exact e.prod_comp (fun i => ∫⁻ y, f i y ∂μ i)

end QuadFormsKB.Tamagawa.Measure.Weil
