/-
# Hanke 2005, §4: splitting Lebesgue measure along `Fin.append`

Auxiliary measure-theory lemmas for the archimedean volume computations of §4.2 (`ArchVolumeReal.lean`).

**Proves**
* `measurePreserving_finAppend`: $(x, y)\mapsto$ `Fin.append x y` is measure preserving
  $(V^q\times V^r, \mathrm{vol}\otimes\mathrm{vol})\to(V^{q+r}, \mathrm{vol})$;
* `lintegral_finAppend`: $\int_{V^{q+r}}G = \int_{V^r}\int_{V^q}G(\mathrm{append}(x, y))\,dx\,dy$ (Tonelli).
-/
import Mathlib

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchReal

variable {V : Type*} [MeasureSpace V] [SigmaFinite (volume : Measure V)]

/-- `Fin.append` as a measurable equivalence $V^q\times V^r\simeq V^{q+r}$. -/
def finAppendEquiv (q r : ℕ) (V : Type*) [MeasurableSpace V] : (Fin q → V) × (Fin r → V) ≃ᵐ (Fin (q + r) → V) :=
  (MeasurableEquiv.sumPiEquivProdPi fun _ : Fin q ⊕ Fin r => V).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => V) finSumFinEquiv)

omit [SigmaFinite (volume : Measure V)] in
theorem finAppendEquiv_apply (q r : ℕ) (x : Fin q → V) (y : Fin r → V) :
    finAppendEquiv q r V (x, y) = Fin.append x y := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simp only [finAppendEquiv, MeasurableEquiv.trans_apply, Fin.append_left]
    rw [show Fin.castAdd r a = finSumFinEquiv (Sum.inl a) from rfl, MeasurableEquiv.piCongrLeft_apply_apply]
    rfl
  · simp only [finAppendEquiv, MeasurableEquiv.trans_apply, Fin.append_right]
    rw [show Fin.natAdd q b = finSumFinEquiv (Sum.inr b) from rfl, MeasurableEquiv.piCongrLeft_apply_apply]
    rfl

theorem measurePreserving_finAppend (q r : ℕ) :
    MeasurePreserving (finAppendEquiv q r V) volume volume :=
  (volume_measurePreserving_sumPiEquivProdPi_symm fun _ : Fin q ⊕ Fin r => V).trans
    (volume_measurePreserving_piCongrLeft (fun _ => V) finSumFinEquiv)

/-- **Tonelli along `Fin.append`**: $\int_{V^{q+r}}G = \int_{V^r}\int_{V^q}G(\mathrm{append}(x, y))$. -/
theorem lintegral_finAppend {q r : ℕ} {G : (Fin (q + r) → V) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ X, G X = ∫⁻ y : Fin r → V, ∫⁻ x : Fin q → V, G (Fin.append x y) := by
  rw [← (measurePreserving_finAppend q r).lintegral_comp hG]
  rw [show (volume : Measure ((Fin q → V) × (Fin r → V))) = volume.prod volume from rfl,
    lintegral_prod_symm (fun z => G (finAppendEquiv q r V z)) (hG.comp (finAppendEquiv q r V).measurable).aemeasurable]
  simp only [finAppendEquiv_apply]

/-- **Tonelli along a family of `Fin.append`s**:
$\int_{(V^{q+r})^k}G = \int_{(V^r)^k}\int_{(V^q)^k}G\big((\mathrm{append}(x_a, y_a))_a\big)$. -/
theorem lintegral_pi_finAppend {k q r : ℕ} {G : (Fin k → Fin (q + r) → V) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ X, G X = ∫⁻ y : Fin k → Fin r → V, ∫⁻ x : Fin k → Fin q → V, G (fun a => Fin.append (x a) (y a)) := by
  have h1 : MeasurePreserving (fun (Y : Fin k → (Fin q → V) × (Fin r → V)) a => finAppendEquiv q r V (Y a))
      volume volume :=
    measurePreserving_pi _ _ fun _ => measurePreserving_finAppend q r
  have h2 := (volume_measurePreserving_arrowProdEquivProdArrow (Fin q → V) (Fin r → V) (Fin k)).symm
  have h3 := h1.comp h2
  have hm : Measurable (fun (Y : Fin k → (Fin q → V) × (Fin r → V)) a => finAppendEquiv q r V (Y a)) :=
    h1.measurable
  rw [← h3.lintegral_comp hG]
  rw [show (volume : Measure ((Fin k → Fin q → V) × (Fin k → Fin r → V))) = volume.prod volume from rfl,
    lintegral_prod_symm (fun z => G (((fun (Y : Fin k → (Fin q → V) × (Fin r → V)) a =>
      finAppendEquiv q r V (Y a)) ∘ (MeasurableEquiv.arrowProdEquivProdArrow (Fin q → V) (Fin r → V) (Fin k)).symm) z))
      (hG.comp h3.measurable).aemeasurable]
  congr 1; funext y; congr 1; funext x
  simp only [Function.comp]
  congr 1; funext a
  rw [← finAppendEquiv_apply]
  rfl

end QuadFormsKB.Hanke2005.ArchReal
