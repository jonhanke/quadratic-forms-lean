import Mathlib
import QuadFormsKB.Citation

/-!
# Transporting a local orbital identity along a change of coordinates

**Generic, Mathlib-only.** The local orbital identities are stated for the split form
$\langle m_0\rangle\perp Q'$ at $e_0$ with a particular section. This file moves such an identity to another group $G_0$ with
another section, in **set form**:

Let $\varphi : G_0\to G_1$ be a measurable bijective homomorphism with $\varphi_*\mu_0 = a\,\mu_1$, $\psi : X_1\to X_0$ a
measurable bijection of the spheres with $\psi_*\sigma_1 = b\,\sigma_0$, and suppose
$\mu_1 = c_1\,\mathrm{orb}_*(\sigma_1\otimes\mu')$ with $\mathrm{orb}(x, h) = s_1(x)\,\iota_1(h)$ injective. If our section
$s_0$ and embedding $\iota_0$ satisfy $\varphi(\iota_0 h) = \iota_1 h$ and $\varphi(s_0(\psi x)) = s_1(x)\,\iota_1(\kappa(x))$ for a
measurable $\kappa : X_1\to H$, then (**`measure_mul_image_eq`**)
$$\mu_0\big(\{s_0(y)\,\iota_0(h) : y\in A,\ h\in B\}\big) = a\,b\,c_1\,\sigma_0(A)\,\mu'(B)$$
for all measurable $A\subseteq X_0$, $B\subseteq H$ (left invariance of $\mu'$ absorbs $\kappa$).
-/

open MeasureTheory Measure Set
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

variable {G₀ G₁ H X₀ X₁ : Type*} [Group G₀] [Group G₁] [Group H]
  [MeasurableSpace G₀] [MeasurableSpace G₁] [MeasurableSpace H] [MeasurableSpace X₀] [MeasurableSpace X₁]
  [MeasurableMul₂ H] [MeasurableInv H]

/-- The set $s(A)\,\iota(B) = \{s(y)\iota(h) : y\in A, h\in B\}$. -/
def secMulImage {X G : Type*} [Mul G] (s : X → G) (ι : H → G) (A : Set X) (B : Set H) : Set G :=
  {g | ∃ y ∈ A, ∃ h ∈ B, g = s y * ι h}

/-- **Transport of a local orbital identity, set form.** -/
theorem measure_mul_image_eq (φ : G₀ →* G₁) (hφinj : Function.Injective φ) (hφm : Measurable φ)
    (μ₀ : Measure G₀) (μ₁ : Measure G₁) (a : ℝ≥0∞) (hφμ : μ₀.map φ = a • μ₁)
    (ψ : X₁ ≃ᵐ X₀) (σ₀ : Measure X₀) (σ₁ : Measure X₁) (b : ℝ≥0∞) (hψσ : σ₁.map ψ = b • σ₀)
    (μ' : Measure H) [SFinite σ₁] [SFinite μ'] [μ'.IsMulLeftInvariant]
    (s₁ : X₁ → G₁) (ι₁ : H →* G₁) (hι₁ : Function.Injective ι₁)
    (horb : Function.Injective fun p : X₁ × H => s₁ p.1 * ι₁ p.2)
    (horbm : Measurable fun p : X₁ × H => s₁ p.1 * ι₁ p.2)
    (c₁ : ℝ≥0∞) (hfib : μ₁ = c₁ • (σ₁.prod μ').map (fun p : X₁ × H => s₁ p.1 * ι₁ p.2))
    (s₀ : X₀ → G₀) (ι₀ : H → G₀) (hι : ∀ h, φ (ι₀ h) = ι₁ h)
    (κ : X₁ → H) (hκ : Measurable κ) (hs : ∀ x, φ (s₀ (ψ x)) = s₁ x * ι₁ (κ x))
    {A : Set X₀} (hA : MeasurableSet A) {B : Set H} (hB : MeasurableSet B)
    (hE : MeasurableSet (secMulImage s₀ ι₀ A B)) (hφE : MeasurableSet (φ '' secMulImage s₀ ι₀ A B)) :
    μ₀ (secMulImage s₀ ι₀ A B) = a * b * c₁ * σ₀ A * μ' B := by
  set E := secMulImage s₀ ι₀ A B
  have h1 : μ₀ E = a * μ₁ (φ '' E) := by
    have := congrArg (fun m : Measure G₁ => m (φ '' E)) hφμ
    simp only [Measure.smul_apply, smul_eq_mul] at this
    rw [← this, Measure.map_apply hφm hφE, hφinj.preimage_image]
  -- the preimage of `φ(E)` under the orbit map
  set W : Set (X₁ × H) := {p | ψ p.1 ∈ A ∧ (κ p.1)⁻¹ * p.2 ∈ B}
  have hW : MeasurableSet W :=
    (ψ.measurable.comp measurable_fst hA).inter
      ((((hκ.comp measurable_fst).inv).mul measurable_snd) hB)
  have hpre : (fun p : X₁ × H => s₁ p.1 * ι₁ p.2) ⁻¹' (φ '' E) = W := by
    ext ⟨x, h'⟩
    simp only [mem_preimage, mem_image, W, mem_setOf_eq]
    constructor
    · rintro ⟨g, ⟨y, hy, h, hh, rfl⟩, hg⟩
      rw [map_mul, hι] at hg
      obtain ⟨x', rfl⟩ := ψ.surjective y
      rw [hs, mul_assoc, ← map_mul] at hg
      have := @horb (x', κ x' * h) (x, h') hg
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, e⟩ := this
      refine ⟨hy, ?_⟩
      rw [← e, inv_mul_cancel_left]; exact hh
    · rintro ⟨hy, hh⟩
      refine ⟨s₀ (ψ x) * ι₀ ((κ x)⁻¹ * h'), ⟨ψ x, hy, _, hh, rfl⟩, ?_⟩
      rw [map_mul, hs, hι, mul_assoc, ← map_mul, mul_inv_cancel_left]
  have h2 : μ₁ (φ '' E) = c₁ * σ₀ A * b * μ' B := by
    rw [hfib, Measure.smul_apply, Measure.map_apply horbm hφE, hpre, smul_eq_mul]
    rw [Measure.prod_apply hW]
    have hsec : ∀ x : X₁, μ' (Prod.mk x ⁻¹' W) = (ψ ⁻¹' A).indicator (fun _ => μ' B) x := by
      intro x
      by_cases hx : ψ x ∈ A
      · rw [indicator_of_mem (show x ∈ ψ ⁻¹' A from hx)]
        have : Prod.mk x ⁻¹' W = (fun h => (κ x)⁻¹ * h) ⁻¹' B := by
          ext h; simp [W, hx]
        rw [this, measure_preimage_mul]
      · rw [indicator_of_notMem (show x ∉ ψ ⁻¹' A from hx)]
        have : Prod.mk x ⁻¹' W = ∅ := by ext h; simp [W, hx]
        rw [this, measure_empty]
    simp_rw [hsec]
    rw [lintegral_indicator (ψ.measurable hA), setLIntegral_const]
    have hσ : σ₁ (ψ ⁻¹' A) = b * σ₀ A := by
      have := congrArg (fun m : Measure X₀ => m A) hψσ
      simp only [Measure.smul_apply, smul_eq_mul] at this
      rw [← this, Measure.map_apply ψ.measurable hA]
    rw [hσ]; ring
  rw [h1, h2]; ring

end QuadFormsKB.Tamagawa.Measure.Weil

end
