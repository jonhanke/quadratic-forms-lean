/-
# Hanke 2005, §4.3: the Leray regions in the coordinates $(u, Y, \sigma)$

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Proves** (for $\varepsilon$ small, $\bar B_\varepsilon(c_Q)\subseteq h(W)$)
* `image_psi_Om`: the Leray region $\{X : \operatorname{Re}\det X > 0,\ \Phi(X)\in\bar B_\varepsilon(c_Q)\}$ is the image under
  $\Psi$ of the coordinate set $\Omega_\varepsilon$ (`Om`): $u\in Z_{\mathbb C}$, $c(T, \sigma)\in W$, $h(c)\in\bar B_\varepsilon$,
  $\operatorname{Re}\det\Psi > 0$;
* `injOn_psi_Om`: $\Psi$ is injective on $\Omega_\varepsilon$; `measurableSet_Om`.
-/
import QuadFormsKB.Literature.Hanke2005.ArchCxTest
import QuadFormsKB.Literature.Hanke2005.ArchCxCoords

open MeasureTheory Matrix Complex Set

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchCx

open QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.ArchVol

variable {n : ℕ}

/-- $c(p) = c(T, \sigma)$ with $T = {}^tY(1 - {}^tuu)Y$. -/
def cP (p : Fin n → Fin n → ℂ) : UIdx n → ℂ := cOf (tT (pu p) (pY p)) (ps p)

/-- **The coordinate set** $\Omega_\varepsilon$. -/
def Om (n : ℕ) (ε : ℝ) : Set (Fin n → Fin n → ℂ) :=
  {p | pu p ∈ ZC n ∧ cP p ∈ Wc n ∧ hmap (cP p) ∈ Metric.closedBall (coeffUC (sumSqC n)) ε ∧
    0 < (psiM (pu p) (pY p) (ps p)).det.re}

theorem pu_skew (p : Fin n → Fin n → ℂ) : (pu p)ᵀ = -pu p := skewOf_transpose _

theorem ps_symm (p : Fin n → Fin n → ℂ) : (ps p)ᵀ = ps p := symU_transpose' _

theorem cT_cP (p : Fin n → Fin n → ℂ) : cT (cP p) = tT (pu p) (pY p) := cT_cOf _ (tT_transpose _ _)

theorem cS_cP (p : Fin n → Fin n → ℂ) : cS (cP p) = ps p := cS_cOf _ (ps_symm p)

theorem phi_psi (p : Fin n → Fin n → ℂ) : phi (sumSqC n) (ofCols (psi p)) = hmap (cP p) :=
  phi_psiM (pu_skew p) (ps_symm p)

theorem reM_one_sub_I (u : Matrix (Fin n) (Fin n) ℝ) : reM (1 - I • cplx u) = 1 := by
  ext i j; by_cases h : i = j <;> simp [reM, cplx, one_apply, h]

theorem imM_one_sub_I (u : Matrix (Fin n) (Fin n) ℝ) : imM (1 - I • cplx u) = -u := by
  ext i j; by_cases h : i = j <;> simp [imM, cplx, one_apply, h]

theorem reM_imM_one_sub_mul (u Y : Matrix (Fin n) (Fin n) ℝ) :
    reM ((1 - I • cplx u) * cplx Y) = Y ∧ imM ((1 - I • cplx u) * cplx Y) = -(u * Y) := by
  rw [reM_mul, imM_mul, reM_one_sub_I, imM_one_sub_I, reM_cplx, imM_cplx]
  constructor
  · simp
  · simp

theorem p_ext {p p' : Fin n → Fin n → ℂ} (hY : pY p = pY p') (hu : pu p = pu p') (hs : ps p = ps p') :
    p = p' := by
  funext i j
  apply Complex.ext
  · exact congrFun (congrFun hY i) j
  · by_cases h : j < i
    · have e : ∀ q : Fin n → Fin n → ℂ, pu q i j = (q i j).im := fun q => by
        simp [pu, skewOf, lowerOf, pV, h]
      rw [← e, ← e, hu]
    · have h' : i ≤ j := not_lt.mp h
      have e : ∀ q : Fin n → Fin n → ℂ, ps q i j = (q i j).im := fun q => by
        simp [ps, symU, upperOf, pV, h']
      rw [← e, ← e, hs]

/-- $Y$ is invertible when $T$ is positive definite. -/
theorem det_ne_zero_of_PDU {u Y : Matrix (Fin n) (Fin n) ℝ}
    (hT : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (tT u Y *ᵥ x)) : Y.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hYv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have := hT v hv
  rw [tT, ← mulVec_mulVec, ← mulVec_mulVec, hYv, mulVec_zero, mulVec_zero, dotProduct_zero] at this
  exact lt_irrefl _ this

theorem PDU_cP {p : Fin n → Fin n → ℂ} (hp : cP p ∈ Wc n) :
    ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (tT (pu p) (pY p) *ᵥ x) := by
  intro x hx
  have := PDU_of_Wc hp x hx
  rwa [symU_re_eq_cT, cT_cP] at this

theorem injOn_psi_Om (ε : ℝ) : InjOn psi (Om n ε) := by
  intro p hp p' hp' he
  have hA : psiM (pu p) (pY p) (ps p) = psiM (pu p') (pY p') (ps p') := by
    have := congrArg ofCols he; simpa [psi, ofCols_cols] using this
  have hc : cP p = cP p' := by
    have h1 := phi_psi p
    have h2 := phi_psi p'
    rw [show ofCols (psi p) = psiM (pu p) (pY p) (ps p) from rfl, hA] at h1
    rw [show ofCols (psi p') = psiM (pu p') (pY p') (ps p') from rfl] at h2
    rw [← gc_hmap hp.2.1, ← gc_hmap hp'.2.1, ← h1, h2]
  have hs : ps p = ps p' := by rw [← cS_cP, hc, cS_cP]
  have hd : (1 - I • cplx (ps p)).det ≠ 0 := by
    have := det_ne_zero_of_Wc hp.2.1; rwa [cS_cP] at this
  have hB : (1 - I • cplx (pu p)) * cplx (pY p) = (1 - I • cplx (pu p')) * cplx (pY p') := by
    have hu' : IsUnit (1 - I • cplx (ps p)).det := isUnit_iff_ne_zero.mpr hd
    have e := congrArg (fun M => M * (1 - I • cplx (ps p))⁻¹) hA
    simp only [psiM, ← hs, Matrix.mul_assoc, mul_nonsing_inv _ hu', Matrix.mul_one] at e
    exact e
  have hY : pY p = pY p' := by
    rw [← (reM_imM_one_sub_mul (pu p) (pY p)).1, hB, (reM_imM_one_sub_mul _ _).1]
  have hdY : (pY p).det ≠ 0 := det_ne_zero_of_PDU (PDU_cP hp.2.1)
  have huY : pu p * pY p = pu p' * pY p := by
    have := congrArg imM hB
    rw [(reM_imM_one_sub_mul _ _).2, (reM_imM_one_sub_mul _ _).2, ← hY] at this
    exact neg_injective this
  have hu : pu p = pu p' := by
    have hU : IsUnit (pY p).det := isUnit_iff_ne_zero.mpr hdY
    have := congrArg (fun M => M * (pY p)⁻¹) huY
    simpa only [Matrix.mul_assoc, mul_nonsing_inv _ hU, Matrix.mul_one] using this
  exact p_ext hY hu hs

theorem continuous_pV : Continuous (pV : (Fin n → Fin n → ℂ) → Matrix (Fin n) (Fin n) ℝ) :=
  continuous_pi fun i => continuous_pi fun j =>
    Complex.continuous_im.comp ((continuous_apply j).comp (continuous_apply i))

theorem continuous_pY : Continuous (pY : (Fin n → Fin n → ℂ) → Matrix (Fin n) (Fin n) ℝ) :=
  continuous_pi fun i => continuous_pi fun j =>
    Complex.continuous_re.comp ((continuous_apply j).comp (continuous_apply i))

theorem continuous_upperOf : Continuous (upperOf : Matrix (Fin n) (Fin n) ℝ → UIdx n → ℝ) :=
  continuous_pi fun _ => (continuous_apply _).comp (continuous_apply _)

theorem continuous_symU : Continuous (symU : (UIdx n → ℝ) → Matrix (Fin n) (Fin n) ℝ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [symU, of_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_apply _

theorem continuous_pu : Continuous (pu : (Fin n → Fin n → ℂ) → Matrix (Fin n) (Fin n) ℝ) :=
  continuous_skewOf.comp (continuous_lowerOf.comp continuous_pV)

theorem continuous_ps : Continuous (ps : (Fin n → Fin n → ℂ) → Matrix (Fin n) (Fin n) ℝ) :=
  continuous_symU.comp (continuous_upperOf.comp continuous_pV)

theorem continuous_cOf : Continuous fun q : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ => cOf q.1 q.2 := by
  refine continuous_pi fun r => ?_
  have h1 : Continuous fun q : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ => q.1 r.1.1 r.1.2 :=
    (continuous_apply r.1.2).comp ((continuous_apply r.1.1).comp continuous_fst)
  have h2 : Continuous fun q : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ => q.2 r.1.1 r.1.2 :=
    (continuous_apply r.1.2).comp ((continuous_apply r.1.1).comp continuous_snd)
  have e : (fun q : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ => cOf q.1 q.2 r) =
      fun q => ((q.1 r.1.1 r.1.2 : ℝ) : ℂ) + ((q.2 r.1.1 r.1.2 : ℝ) : ℂ) * I := by
    funext q; exact Complex.mk_eq_add_mul_I _ _
  rw [e]
  exact (Complex.continuous_ofReal.comp h1).add ((Complex.continuous_ofReal.comp h2).mul continuous_const)

theorem continuous_tT : Continuous fun q : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ => tT q.1 q.2 :=
  (continuous_snd.matrix_transpose.matrix_mul (continuous_const.sub
    (continuous_fst.matrix_transpose.matrix_mul continuous_fst))).matrix_mul continuous_snd

theorem continuous_cP : Continuous (cP : (Fin n → Fin n → ℂ) → UIdx n → ℂ) :=
  continuous_cOf.comp ((continuous_tT.comp (continuous_pu.prodMk continuous_pY)).prodMk continuous_ps)

theorem continuous_psiM' : Continuous fun p : Fin n → Fin n → ℂ => psiM (pu p) (pY p) (ps p) := by
  unfold psiM
  exact ((continuous_const.sub ((continuous_cplx.comp continuous_pu).const_smul I)).mul
    (continuous_cplx.comp continuous_pY)).mul
    (continuous_const.sub ((continuous_cplx.comp continuous_ps).const_smul I))

theorem measurableSet_Om (ε : ℝ) : MeasurableSet (Om n ε) := by
  have h1 : MeasurableSet {p : Fin n → Fin n → ℂ | pu p ∈ ZC n} := by
    have : {p : Fin n → Fin n → ℂ | pu p ∈ ZC n} = (fun p => lowerOf (pV p)) ⁻¹' (skewOf ⁻¹' ZC n) := rfl
    rw [this]
    exact (continuous_lowerOf.comp continuous_pV).measurable measurableSet_skewOf_ZC
  have h2 : MeasurableSet {p : Fin n → Fin n → ℂ | cP p ∈ Wc n} :=
    continuous_cP.measurable isOpen_Wc.measurableSet
  have h3 : MeasurableSet {p : Fin n → Fin n → ℂ | hmap (cP p) ∈ Metric.closedBall (coeffUC (sumSqC n)) ε} :=
    (continuous_hmap.comp continuous_cP).measurable Metric.isClosed_closedBall.measurableSet
  have h4 : MeasurableSet {p : Fin n → Fin n → ℂ | 0 < (psiM (pu p) (pY p) (ps p)).det.re} :=
    measurableSet_lt measurable_const (Complex.continuous_re.comp continuous_psiM'.matrix_det).measurable
  exact h1.inter (h2.inter (h3.inter h4))

/-- **The Leray region is $\Psi(\Omega_\varepsilon)$** for $\bar B_\varepsilon(c_Q)\subseteq h(W)$. -/
theorem image_psi_Om {ε : ℝ} (hε : Metric.closedBall (coeffUC (sumSqC n)) ε ⊆ hmap '' Wc n) :
    psi '' Om n ε = lerayRegionC (sumSqC n) ε := by
  ext X
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨hp.2.2.2, ?_⟩
    rw [phi_psi]; exact hp.2.2.1
  · rintro ⟨hdet, hX⟩
    have hN := hε hX
    set c := gc n (phi (sumSqC n) (ofCols X))
    have hcW : c ∈ Wc n := gc_mem hN
    have hc : hmap c = phi (sumSqC n) (ofCols X) := hmap_gc hN
    have hT := PDU_of_Wc hcW
    have hd := det_ne_zero_of_Wc hcW
    set u := uOfc (ofCols X) c
    set Y := reM (aOf (ofCols X) c)
    have hus : uᵀ = -u := uOfc_skew hc hT hd
    set x : (Fin n → Fin n → ℝ) × ((LIdx n → ℝ) × (UIdx n → ℝ)) := (fun i j => Y i j, (lowerOf u, upperOf (cS c)))
    have hpu : pu (pE n x) = u := by rw [pu_pE]; exact skewOf_lowerOf hus
    have hps : ps (pE n x) = cS c := by rw [ps_pE]; exact symU_upperOf (cS_transpose c)
    have hpY : pY (pE n x) = Y := by rw [pY_pE]; rfl
    have hpsi : psiM (pu (pE n x)) (pY (pE n x)) (ps (pE n x)) = ofCols X := by
      rw [hpu, hpY, hps]; exact (X_eq_psiM hc hT hd).symm
    have hcP : cP (pE n x) = c := by
      rw [cP, hpu, hpY, hps, tT_uOfc hc hT hd, cOf_cT_cS]
    refine ⟨pE n x, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hpu]; exact uOfc_mem_ZC hc hT hd
    · rw [hcP]; exact hcW
    · rw [hcP, hc]; exact hX
    · rw [hpsi]; exact hdet
    · show cols (psiM (pu (pE n x)) (pY (pE n x)) (ps (pE n x))) = X
      rw [hpsi, cols_ofCols]

end QuadFormsKB.Hanke2005.ArchCx
