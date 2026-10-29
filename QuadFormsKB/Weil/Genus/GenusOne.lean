/-
# Genus one: the $\mathrm{Sp}_2$ model is the $\mathrm{SL}_2$ model

**Layer:** abstract local model (`LocalData K`, any model).

Along $M_{n\times1}(K) \cong K^n$, $X \mapsto (X_{i0})_i$ (`colEquiv`), the genus-one operators of
`Weil/Genus/Model.lean` are the operators `opNf`, `opMf`, `opWf` of `Weil/Model.lean`:
$$\omega_1(n(b)) = \omega(n(b_{00})),\qquad \omega_1(m(t)) = \omega(m(t)),\qquad \omega_1(w) = \omega(w)$$
(`opNg_genusOne`, `opMg_genusOne`, `opWg_genusOne`), and **the representation `weilRepSp` of $\mathrm{Sp}_2(k)$ (with
the presentation proved for $g = 1$, `siegelPresentation_one`, and `isGLModel_one`) is the representation `weilRep`
of $\mathrm{SL}_2(k)$** under $\mathrm{Sp}_2(k) \cong \mathrm{SL}_2(k)$ (`sp1ToSL2`): `weilRepSp_genusOne`.

Sources: Kudla, *Notes on the local theta correspondence* (1996), §I.1 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Genus.Model

open MeasureTheory Matrix
open scoped MatrixGroups

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep.Genus

open WeilRep WeilRep.LocalData

variable {K : Type*} [CommRing K] [MeasurableSpace K] {D : LocalData K} {m : ℕ} {a : Fin (2 * m) → Kˣ}

/-- $M_{n\times1}(K) \cong K^n$, $X \mapsto (X_{i0})_i$. -/
def colEquiv : PtG m 1 K ≃ (Fin (2 * m) → K) where
  toFun X i := X i 0
  invFun x i _ := x i
  left_inv X := by ext i j; fin_cases j; rfl
  right_inv x := rfl

@[simp] lemma colEquiv_apply (X : PtG m 1 K) (i : Fin (2 * m)) : colEquiv X i = X i 0 := rfl

@[simp] lemma colEquiv_symm_apply (x : Fin (2 * m) → K) (i : Fin (2 * m)) (j : Fin 1) :
    colEquiv.symm x i j = x i := rfl

/-- **$\omega_1(n(b)) = \omega(n(b_{00}))$.** -/
@[kb "kudla1996" "§I.1 (genus one) [unverified]"]
theorem opNg_genusOne (B : Matrix (Fin 1) (Fin 1) K) (Φ : PtG m 1 K → ℂ) (X : PtG m 1 K) :
    opNg D a B Φ X = D.opNf a (B 0 0) (Φ ∘ colEquiv.symm) (colEquiv X) := by
  have h : trace (B * QX a X) = B 0 0 * Qform a (colEquiv X) := by
    simp [trace, Matrix.mul_apply, Qform, QX, Finset.mul_sum, Matrix.diagonal_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h2 : (Φ ∘ colEquiv.symm) (colEquiv X) = Φ X := by simp
  rw [opNg, opNf, h, h2]

/-- **$\omega_1(m(t)) = \omega(m(t))$.** -/
@[kb "kudla1996" "§I.1 (genus one) [unverified]"]
theorem opMg_genusOne (t : Kˣ) (Φ : PtG m 1 K → ℂ) (X : PtG m 1 K) :
    opMg D a (diagGL fun _ => t) Φ X = D.opMf a t (Φ ∘ colEquiv.symm) (colEquiv X) := by
  have hdet : ((diagGL fun _ : Fin 1 => t : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K).det = (t : K) := by
    simp [diagGL_coe]
  have h2 : (Φ ∘ colEquiv.symm) (fun i => (t : K) * colEquiv X i) = Φ (X * ((diagGL fun _ : Fin 1 => t :
      GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K)) := by
    simp only [Function.comp]
    congr 1
    ext i j
    fin_cases j
    simp [diagGL_coe, mul_comm]
  rw [opMg, opMf, hdet, h2]

/-- **$\omega_1(w) = \omega(w)$.** -/
@[kb "kudla1996" "§I.1 (genus one) [unverified]"]
theorem opWg_genusOne [SigmaFinite D.μ] (Φ : PtG m 1 K → ℂ) (Y : PtG m 1 K) :
    opWg D a Φ Y = D.opWf a (Φ ∘ colEquiv.symm) (colEquiv Y) := by
  let e : PtG m 1 K ≃ᵐ (Fin (2 * m) → K) :=
    MeasurableEquiv.piCongrRight (fun _ => MeasurableEquiv.funUnique (Fin 1) K)
  have hmp : MeasurePreserving e (muG D m 1) (D.muN (2 * m)) :=
    measurePreserving_pi _ _ (fun _ => measurePreserving_funUnique D.μ (Fin 1))
  have he : ∀ X, e X = colEquiv X := fun X => rfl
  have hI := hmp.integral_comp'
    (fun x => (Φ ∘ colEquiv.symm) x * (D.ψ (Bform a x (colEquiv Y)) : ℂ))
  rw [opWf, opWg, ← hI]
  simp only [pow_one, he]
  congr 2
  ext X
  have hB : BX a X Y = Bform a (colEquiv X) (colEquiv Y) := by
    simp [BX, Bform]
  simp [hB]

lemma comp_colEquiv_mem {Φ : PtG m 1 K → ℂ} (hΦ : Φ ∈ Sg D m 1) : Φ ∘ colEquiv.symm ∈ D.Sn (2 * m) := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    have : ptG f ∘ colEquiv.symm = ptensor (fun i => f i 0) := by
      ext x; simp [ptG, ptensor]
    rw [this]
    exact ptensor_mem_Sn (fun i => hf i 0)
  | zero => exact zero_mem _
  | add x z _ _ hx hz => exact add_mem hx hz
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

/-- **Genus one: `weilRepSp` is `weilRep`.** For a model `D`, a field $k$ with $2 \ne 0$ and $\iota : k \to K$, the
representation of $\mathrm{Sp}_2(k)$ on $S(V^1)$ (presentation `siegelPresentation_one`, interface `isGLModel_one`)
agrees, along $M_{n\times1}(K) \cong K^n$ and $\mathrm{Sp}_2(k) \cong \mathrm{SL}_2(k)$, with the $\mathrm{SL}_2$ Weil
representation `weilRep` of `Weil/Model.lean`. -/
@[kb "kudla1996" "§I.1 (the Weil representation of $\\mathrm{SL}_2 = \\mathrm{Sp}_2$) [unverified]"]
theorem weilRepSp_genusOne (hD : D.IsModel) {k : Type*} [Field k] (ι : k →+* K) (h2 : (2 : k) ≠ 0)
    (γ : Sp 1 k) (Φ : Sg D m 1) :
    ((weilRepSp hD (isGLModel_one (a := a) hD) ι siegelPresentation_one h2 γ Φ : Sg D m 1) : PtG m 1 K → ℂ) ∘
        colEquiv.symm =
      ((weilRep hD (a := a) ι (sp1ToSL2 γ) ⟨(Φ : PtG m 1 K → ℂ) ∘ colEquiv.symm, comp_colEquiv_mem Φ.2⟩ :
        D.Sn (2 * m)) : (Fin (2 * m) → K) → ℂ) := by
  classical
  set ρ₁ := weilRepSp hD (isGLModel_one (a := a) hD) ι siegelPresentation_one h2 with hρ₁
  set ρ := weilRep hD (a := a) ι with hρ
  let P : Sp 1 k → Prop := fun γ => ∀ Φ : Sg D m 1,
    ((ρ₁ γ Φ : Sg D m 1) : PtG m 1 K → ℂ) ∘ colEquiv.symm =
      ((ρ (sp1ToSL2 γ) ⟨(Φ : PtG m 1 K → ℂ) ∘ colEquiv.symm, comp_colEquiv_mem Φ.2⟩ :
        D.Sn (2 * m)) : (Fin (2 * m) → K) → ℂ)
  have hmul : ∀ γ δ, P γ → P δ → P (γ * δ) := by
    intro γ δ hγ hδ Φ
    have e1 : ((ρ₁ (γ * δ) Φ : Sg D m 1) : PtG m 1 K → ℂ) = ((ρ₁ γ (ρ₁ δ Φ) : Sg D m 1) : PtG m 1 K → ℂ) := by
      rw [map_mul, Module.End.mul_apply]
    rw [e1, hγ (ρ₁ δ Φ), map_mul, map_mul, Module.End.mul_apply]
    congr 2
    exact Subtype.ext (hδ Φ)
  have hN : ∀ (B : Matrix (Fin 1) (Fin 1) k) (hB : Bᵀ = B), P (spN B hB) := by
    intro B hB Φ
    rw [hρ₁, weilRepSp_spN, sp1ToSL2_spN, hρ, weilRep_nMat]
    simp only [endN_apply _ ι hB, opN_apply]
    ext x
    rw [Function.comp_apply, opNg_genusOne]
    simp
  have hM : ∀ t : kˣ, P (spM (gl1 t)) := by
    intro t Φ
    rw [hρ₁, weilRepSp_spM, sp1ToSL2_spM, hρ, weilRep_mMat]
    have : Matrix.GeneralLinearGroup.map ι (gl1 t) = diagGL (fun _ : Fin 1 => Units.map (ι : k →* K) t) := by
      ext i j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst hi hj
      simp [diagGL_coe]
    ext x
    simp only [endM_apply, this, opM_apply]
    rw [Function.comp_apply, opMg_genusOne]
    simp
  have hW : P spW := by
    intro Φ
    rw [hρ₁, weilRepSp_spW, sp1ToSL2_spW, hρ, weilRep_wMat]
    have := hD.toIsOps.sigmaFinite
    ext x
    simp only [endW_apply, opW_apply]
    rw [Function.comp_apply, opWg_genusOne]
    simp
  have hsymm : ∀ s : k, (!![s] : Matrix (Fin 1) (Fin 1) k)ᵀ = !![s] := fun s => by
    ext i j; fin_cases i; fin_cases j; rfl
  have hNs : ∀ s : k, P (spN (!![s] : Matrix (Fin 1) (Fin 1) k) (hsymm s)) := fun s => hN _ _
  have hNeq : ∀ s : k, sp1ToSL2 (spN (!![s] : Matrix (Fin 1) (Fin 1) k) (hsymm s)) = nMat s := fun s => by
    rw [sp1ToSL2_spN]; rfl
  suffices hP : P γ from hP Φ
  by_cases hc : ((sp1ToSL2 γ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0
  · have h := eq_cell_of_c_eq_zero (sp1ToSL2 γ) hc
    have hγ : γ = spM (gl1 (Units.mk0 _ (a_ne_zero_of_c_eq_zero hc))) *
        spN (!![((sp1ToSL2 γ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 0 1 /
          ((sp1ToSL2 γ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 0 0] : Matrix (Fin 1) (Fin 1) k) (hsymm _) :=
      sp1ToSL2_injective (by rw [map_mul, sp1ToSL2_spM, hNeq]; exact h)
    rw [hγ]
    exact hmul _ _ (hM _) (hNs _)
  · have h := eq_cell_of_c_ne_zero (sp1ToSL2 γ) hc
    have hγ : γ = spN (!![((sp1ToSL2 γ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 0 0 /
          ((sp1ToSL2 γ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0] : Matrix (Fin 1) (Fin 1) k) (hsymm _) *
        spM (gl1 (Units.mk0 _ (unit_ne_zero_aux hc))) * spW *
        spN (!![((sp1ToSL2 γ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 1 /
          ((sp1ToSL2 γ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0] : Matrix (Fin 1) (Fin 1) k) (hsymm _) :=
      sp1ToSL2_injective (by rw [map_mul, map_mul, map_mul, sp1ToSL2_spM, sp1ToSL2_spW, hNeq, hNeq]; exact h)
    rw [hγ]
    exact hmul _ _ (hmul _ _ (hmul _ _ (hNs _) (hM _)) hW) (hNs _)

end QuadFormsKB.WeilRep.Genus
