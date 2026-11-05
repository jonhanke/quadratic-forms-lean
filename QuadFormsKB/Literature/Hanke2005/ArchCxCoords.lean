/-
# Hanke 2005, §4.3: Lebesgue measure in the coordinates $(Y, u, \sigma)$

Auxiliary measure theory for `ArchVolumeComplex.lean`: the coordinate point $p\in M_n(\mathbb C)$ of `ArchCxParam.lean` is
a permutation of the real coordinates $(Y_{ij})$, $(u_{ik})_{i>k}$, $(\sigma_{ij})_{i\le j}$, so Lebesgue measure on
$M_n(\mathbb C)$ is the product of the Lebesgue measures in these coordinates (`measurePreserving_pOf`), and transposition
preserves Lebesgue measure on $M_n(\mathbb R)$ (`measurePreserving_transpose`).
-/
import QuadFormsKB.Literature.Hanke2005.ArchCxParam

open MeasureTheory Matrix Set

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchCx

open QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.ArchVol

variable {n : ℕ}

/-- Uncurrying preserves Lebesgue measure. -/
theorem measurePreserving_uncurry (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurePreserving (fun f : ι → κ → ℝ => fun q : ι × κ => f q.1 q.2) volume volume := by
  have hm : Measurable (fun f : ι → κ → ℝ => fun q : ι × κ => f q.1 q.2) :=
    measurable_pi_iff.mpr fun q => (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
  refine ⟨hm, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have : (fun f : ι → κ → ℝ => fun q : ι × κ => f q.1 q.2) ⁻¹' univ.pi s =
      univ.pi fun i => univ.pi fun j => s (i, j) := by
    ext f; simp [Set.mem_pi, Prod.forall]
  rw [this, volume_pi_pi]
  simp_rw [volume_pi_pi]
  rw [← Finset.prod_product', ← Finset.univ_product_univ]

/-- The uncurrying as a measurable equivalence. -/
def uncurryE (ι κ : Type*) : (ι → κ → ℝ) ≃ᵐ (ι × κ → ℝ) := (MeasurableEquiv.curry ι κ ℝ).symm

theorem uncurryE_apply (ι κ : Type*) (f : ι → κ → ℝ) (q : ι × κ) : uncurryE ι κ f q = f q.1 q.2 := rfl

theorem measurePreserving_uncurryE (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurePreserving (uncurryE ι κ) volume volume := measurePreserving_uncurry ι κ

/-- Transposition preserves Lebesgue measure on $M_n(\mathbb R)$. -/
theorem measurePreserving_transpose :
    MeasurePreserving (fun B : Fin n → Fin n → ℝ => fun i j => B j i) volume volume := by
  have h1 := measurePreserving_uncurryE (Fin n) (Fin n)
  have h2 := volume_measurePreserving_piCongrLeft (fun _ : Fin n × Fin n => ℝ) (Equiv.prodComm (Fin n) (Fin n))
  have h3 := (measurePreserving_uncurryE (Fin n) (Fin n)).symm
  have := (h3.comp h2).comp h1
  convert this using 1
  funext B i j
  simp only [Function.comp_apply]
  rw [show (uncurryE (Fin n) (Fin n)).symm _ i j = _ from rfl]
  simp [uncurryE, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, MeasurableEquiv.curry]

/-! ### The coordinate permutation -/

/-- $\mathrm{LIdx}\sqcup\mathrm{UIdx}\simeq\mathrm{Fin}\,n\times\mathrm{Fin}\,n$ (strictly lower and upper-with-diagonal positions). -/
def idxE (n : ℕ) : LIdx n ⊕ UIdx n ≃ Fin n × Fin n :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivRight fun _ : Fin n × Fin n => (not_lt).symm)).trans
    (Equiv.sumCompl fun q : Fin n × Fin n => q.2 < q.1)

/-- The real matrix with lower coordinates $w_1$ (below the diagonal) and upper coordinates $w_2$. -/
def vE (n : ℕ) : (LIdx n → ℝ) × (UIdx n → ℝ) ≃ᵐ (Fin n → Fin n → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : LIdx n ⊕ UIdx n => ℝ)).symm.trans
    ((MeasurableEquiv.piCongrLeft (fun _ => ℝ) (idxE n)).trans (MeasurableEquiv.curry (Fin n) (Fin n) ℝ))

theorem measurePreserving_vE : MeasurePreserving (vE n) volume volume :=
  ((volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : LIdx n ⊕ UIdx n => ℝ)).trans
    (volume_measurePreserving_piCongrLeft (fun _ => ℝ) (idxE n))).trans
    (measurePreserving_uncurryE (Fin n) (Fin n)).symm

theorem vE_apply_lt (w : (LIdx n → ℝ) × (UIdx n → ℝ)) {i j : Fin n} (h : j < i) :
    vE n w i j = w.1 ⟨(i, j), h⟩ := by
  simp only [vE, MeasurableEquiv.trans_apply]
  change (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (idxE n) _) (i, j) = _
  exact MeasurableEquiv.piCongrLeft_apply_apply (e := idxE n) (β := fun _ => ℝ) _ (Sum.inl ⟨(i, j), h⟩)

theorem vE_apply_le (w : (LIdx n → ℝ) × (UIdx n → ℝ)) {i j : Fin n} (h : i ≤ j) :
    vE n w i j = w.2 ⟨(i, j), h⟩ := by
  simp only [vE, MeasurableEquiv.trans_apply]
  change (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (idxE n) _) (i, j) = _
  exact MeasurableEquiv.piCongrLeft_apply_apply (e := idxE n) (β := fun _ => ℝ) _ (Sum.inr ⟨(i, j), h⟩)

theorem lowerOf_vE (w : (LIdx n → ℝ) × (UIdx n → ℝ)) : lowerOf (vE n w) = w.1 := by
  funext q; exact vE_apply_lt w q.2

theorem upperOf_vE (w : (LIdx n → ℝ) × (UIdx n → ℝ)) : upperOf (vE n w) = w.2 := by
  funext q; exact vE_apply_le w q.2

/-- Real and imaginary parts: $(Y, V)\mapsto Y + iV$ entrywise. -/
def cE (n : ℕ) : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) ≃ᵐ (Fin n → Fin n → ℂ) :=
  (MeasurableEquiv.arrowProdEquivProdArrow (Fin n → ℝ) (Fin n → ℝ) (Fin n)).symm.trans
    ((MeasurableEquiv.piCongrRight fun _ => (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)).symm).trans
      (MeasurableEquiv.piCongrRight fun _ => MeasurableEquiv.piCongrRight fun _ =>
        Complex.measurableEquivRealProd.symm))

theorem cE_apply (x : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ)) (i j : Fin n) :
    cE n x i j = ⟨x.1 i j, x.2 i j⟩ := rfl

theorem measurePreserving_cE : MeasurePreserving (cE n) volume volume := by
  refine ((volume_measurePreserving_arrowProdEquivProdArrow (Fin n → ℝ) (Fin n → ℝ) (Fin n)).symm).trans
    ((measurePreserving_pi _ _ fun _ =>
      (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)).symm).trans ?_)
  exact measurePreserving_pi _ _ fun _ => measurePreserving_pi _ _ fun _ =>
    Complex.volume_preserving_equiv_real_prod.symm

/-- **The coordinate point** $p(Y, w)$ with $\operatorname{Re}p = Y$ and $\operatorname{Im}p$ = `vE w`. -/
def pE (n : ℕ) : (Fin n → Fin n → ℝ) × ((LIdx n → ℝ) × (UIdx n → ℝ)) ≃ᵐ (Fin n → Fin n → ℂ) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (vE n)).trans (cE n)

theorem measurePreserving_pE : MeasurePreserving (pE n) volume volume :=
  ((MeasurePreserving.id volume).prod measurePreserving_vE).trans measurePreserving_cE

theorem pY_pE (x : (Fin n → Fin n → ℝ) × ((LIdx n → ℝ) × (UIdx n → ℝ))) : pY (pE n x) = Matrix.of x.1 := rfl

theorem pV_pE (x : (Fin n → Fin n → ℝ) × ((LIdx n → ℝ) × (UIdx n → ℝ))) : pV (pE n x) = Matrix.of (vE n x.2) := rfl

theorem pu_pE (x : (Fin n → Fin n → ℝ) × ((LIdx n → ℝ) × (UIdx n → ℝ))) : pu (pE n x) = skewOf x.2.1 := by
  rw [pu, pV_pE]; exact congrArg skewOf (lowerOf_vE x.2)

theorem ps_pE (x : (Fin n → Fin n → ℝ) × ((LIdx n → ℝ) × (UIdx n → ℝ))) : ps (pE n x) = symU x.2.2 := by
  rw [ps, pV_pE]; exact congrArg symU (upperOf_vE x.2)

end QuadFormsKB.Hanke2005.ArchCx
