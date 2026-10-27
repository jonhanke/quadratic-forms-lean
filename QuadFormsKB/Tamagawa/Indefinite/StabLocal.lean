/-
# The stabilizer measures in closed form, at every split frame

**Layer:** real and complex analysis on $SO(Q)(\mathbb R)$ and $SO(Q)(\mathbb C)$ (the Leray measures; the real and
complex
fibrations at a point of the quadric).

`ArchConj.lean` (real) and `ArchConjC.lean` (complex) define the measure $\mu_{H_y}$ on the stabilizer of a point $y$
of the quadric
$\{Q = c\}$ from a *chosen* split frame $P$ at $y$ ($Pe_0 = y$, $Q\circ P = \langle c\rangle\perp Q'$), as
$(\kappa_P|\det P|)^{-1}(h\mapsto P\,\mathrm{diag}(1,h)\,P^{-1})_*\mu_{Q'}$, where the Haar constant $\kappa_P$ (`haarConst`) is
obtained from the uniqueness of Haar measure. This file computes $\kappa_P$ and shows that the result does not depend on
the split frame.

**Proves** (unconditional, standard axioms only)
* `stabMeasure_unique`: in a fibration identity $\mu_A = c\cdot\mathrm{coord}_*(\sigma\otimes\nu)$ at one point $y$
  ($0 < c < \infty$, $\sigma\ne0$ σ-finite), the right-invariant stabilizer measure $\nu$ is determined by $\mu_A$, $\sigma$
  and $c$ (the pointwise form of `ArchFibration.μH_eq`);
* `SplitFrame.haarConst_eq`: $\kappa_P = |\det P|^{-(N+1)}$, $N = m+1$ (the Leray conjugation law
  `map_lerayMeasure_conjSO'`);
* **`realStabMeasure_eq_splitFrame`**: for **every** split frame $P$ at $y$,
  $$\mu_{H_y} = |\det P|^{N}\,(h\mapsto P\,\mathrm{diag}(1,h)\,P^{-1})_*\mu_{Q'_P};$$
* the complex versions `SplitFrameC.haarConst_eq` ($\kappa_P = \|\det P\|^{-2(N+1)}$) and
  **`complexStabMeasure_eq_splitFrame`** ($\mu_{H_y} = \|\det P\|^{2N}(h\mapsto P\,\mathrm{diag}(1,h)\,P^{-1})_*\mu_{Q'_P}$).
-/
import QuadFormsKB.Tamagawa.Indefinite.ArchUnique
import QuadFormsKB.Tamagawa.Indefinite.ArchConjC
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarArchReal
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarArchComplex

open MeasureTheory Measure Matrix MulAction Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.ArchSOMeasure
open QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.Measure.LerayComplex

/-! ### Uniqueness of the stabilizer measure at one point -/

section Unique

variable {A : Type*} [Group A] [MeasurableSpace A] [MeasurableMul₂ A] [MeasurableInv A]
  {Y : Type*} [MulAction A Y] {T : Type*} [MeasurableSpace T]

/-- **The stabilizer measure in a fibration identity is unique** (at one point $y$): if
$\mu_A = c\cdot\mathrm{coord}_*(\sigma\otimes\nu) = c\cdot\mathrm{coord}'_*(\sigma\otimes\nu')$ for two orbit coordinates at
$y$, with $0 < c < \infty$, $\sigma\ne0$ σ-finite and $\nu$ right invariant, then $\nu = \nu'$. -/
theorem stabMeasure_unique {μA : Measure A} {σ : Measure T} [SigmaFinite σ] {τ : T → Y} {y : Y} {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hct : c ≠ ⊤) (hσ : σ ≠ 0) (C C' : OrbitCoord (stabilizer A y).subtype τ y)
    (ν ν' : Measure (stabilizer A y)) [SigmaFinite ν] [SigmaFinite ν'] [ν.IsMulRightInvariant]
    (h : μA = c • (σ.prod ν).map C.coord) (h' : μA = c • (σ.prod ν').map C'.coord) : ν = ν' := by
  haveI := measurableMul_subgroup (stabilizer A y)
  haveI : MeasurableMul₂ (stabilizer A y) :=
    ⟨(measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd) |>.subtype_mk⟩
  obtain ⟨u, hu, hCu⟩ := orbitCoord_exists_skew C C'
  have hskew : (C.coord : T × stabilizer A y → A) = C'.coord ∘ fun p : T × stabilizer A y => (p.1, p.2 * u p.1) :=
    funext fun p => hCu p.1 p.2
  have hm : Measurable fun p : T × stabilizer A y => (p.1, p.2 * u p.1) :=
    measurable_fst.prodMk (measurable_snd.mul (hu.comp measurable_fst))
  have hmap : (σ.prod ν).map C.coord = (σ.prod ν).map C'.coord := by
    rw [hskew, ← Measure.map_map C'.coord.measurable hm, map_prod_skew σ ν hu]
  have h1 : c • (σ.prod ν).map C'.coord = c • (σ.prod ν').map C'.coord := by
    rw [← hmap, ← h, ← h']
  have h2 : (σ.prod ν).map C'.coord = (σ.prod ν').map C'.coord := by
    ext s hs
    have := congrArg (fun ν : Measure A => ν s) h1
    simp only [Measure.smul_apply, smul_eq_mul] at this
    exact (ENNReal.mul_right_inj hc0 hct).mp this
  have h3 : σ.prod ν = σ.prod ν' := by
    have := congrArg (fun ν => ν.map C'.coord.symm) h2
    simpa only [MeasurableEquiv.map_symm_map] using this
  obtain ⟨k, hk⟩ : ∃ k, σ (spanningSets σ k) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hσ
    rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets σ]
    exact measure_iUnion_null hall
  have hkt := measure_spanningSets_lt_top σ k
  ext E hE
  have := congrArg (fun ν : Measure (T × stabilizer A y) => ν (spanningSets σ k ×ˢ E)) h3
  simp only [Measure.prod_prod] at this
  exact (ENNReal.mul_right_inj hk hkt.ne).mp this

end Unique

/-! ### Real places -/

section Real

open QuadFormsKB.Tamagawa.Measure.SphereLeray QuadFormsKB.Tamagawa.Measure.OrbitalReal

variable {m : ℕ} {Q : QuadForm ℝ (m + 1)} {c : ℝ} {y : Fin (m + 1) → ℝ}

namespace SplitFrame

variable (F : SplitFrame Q c y)

/-- **The Haar constant of a split frame**: $\kappa_P = |\det P|^{-(m+2)}$. -/
theorem haarConst_eq (hc : c ≠ 0) (hQ : gramDetR Q ≠ 0) :
    ((F.haarConst hc hQ : ℝ≥0) : ℝ≥0∞) =
      (ENNReal.ofReal (|(F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det| ^ (m + 2)))⁻¹ := by
  have hQ' := F.gramDetR_Q' hQ
  have hQ1 := gramDetR_splitForm_ne_zero hc hQ'
  have hH : (splitForm c F.Q').hessian = (1 : ℝ) • ((F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)ᵀ * Q.hessian *
      (F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) := by
    rw [one_smul]; exact F.hess
  have hmap := map_lerayMeasure_conjSO' F.P 1 hH one_ne_zero hQ hQ1
  have hinv : ∀ g, F.conj (conjSO F.P 1 hH one_ne_zero g) = g := fun g => by
    have h : ArchSOInst.mat Q (F.conj (conjSO F.P 1 hH one_ne_zero g)) = ArchSOInst.mat Q g := by
      rw [mat_conj, conjSO_mat, ← Matrix.mul_assoc, ← Matrix.mul_assoc, P_mul_P_inv, Matrix.one_mul,
        Matrix.mul_assoc, P_mul_P_inv, Matrix.mul_one]
    exact Subtype.ext (Units.ext h)
  haveI := isHaarMeasure_lerayMeasure hQ
  set D := ENNReal.ofReal (|(1 : ℝ)| ^ ((m + 1) * (m + 1 + 1) / 2) *
    |(F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det| ^ (m + 1 + 1)) with hD
  have hconj := congrArg (fun μ => μ.map F.conj) hmap
  have hmc : Measurable (conjSO F.P 1 hH one_ne_zero) := (conjSO F.P 1 hH one_ne_zero).continuous_toFun.measurable
  rw [Measure.map_map F.continuous_conj.measurable hmc,
    Measure.map_smul _ F.continuous_conj.measurable.aemeasurable, F.map_conj_lerayMeasure hc hQ] at hconj
  have hid : (F.conj ∘ conjSO F.P 1 hH one_ne_zero) = id := funext hinv
  rw [hid, Measure.map_id] at hconj
  obtain ⟨k, hk⟩ : ∃ k, lerayMeasure Q hQ (spanningSets (lerayMeasure Q hQ) k) ≠ 0 := by
    by_contra hall
    push Not at hall
    have : lerayMeasure Q hQ = 0 := by
      rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets (lerayMeasure Q hQ)]
      exact measure_iUnion_null hall
    exact (isHaarMeasure_lerayMeasure hQ).toIsOpenPosMeasure.open_pos univ isOpen_univ univ_nonempty
      (by simp [this])
  have hkt := measure_spanningSets_lt_top (lerayMeasure Q hQ) k
  have h1 := congrArg (fun μ => μ (spanningSets (lerayMeasure Q hQ) k)) hconj
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def] at h1
  have h2 : (F.haarConst hc hQ : ℝ≥0∞) * D = 1 := by
    have h3 : lerayMeasure Q hQ (spanningSets (lerayMeasure Q hQ) k) * ((F.haarConst hc hQ : ℝ≥0∞) * D) =
        lerayMeasure Q hQ (spanningSets (lerayMeasure Q hQ) k) * 1 := by
      rw [mul_one]
      calc _ = D * (↑(F.haarConst hc hQ) * (lerayMeasure Q hQ) (spanningSets (lerayMeasure Q hQ) k)) := by ring
        _ = _ := h1.symm
    exact (ENNReal.mul_right_inj hk hkt.ne).mp h3
  rw [ENNReal.eq_inv_of_mul_eq_one_left h2, hD]
  simp

/-- **The real stabilizer measure at a split frame, in closed form**:
$\mu_{H_y} = |\det P|^{m+1}\,(h\mapsto P\,\mathrm{diag}(1,h)\,P^{-1})_*\mu_{Q'}$. -/
theorem stabMeasure_eq (hc : c ≠ 0) (hQ : gramDetR Q ≠ 0) :
    F.stabMeasure hc hQ = ENNReal.ofReal (|(F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det| ^ (m + 1)) •
      (lerayMeasure F.Q' (F.gramDetR_Q' hQ)).map F.stabHom := by
  have hd0 : ENNReal.ofReal |(F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det| ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (abs_pos.mpr (det_GL_ne_zero F.P))).ne'
  have hpow : ENNReal.ofReal (|(F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det| ^ (m + 2)) =
      ENNReal.ofReal |(F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det| *
        ENNReal.ofReal (|(F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det| ^ (m + 1)) := by
    rw [← ENNReal.ofReal_mul (abs_nonneg _), ← pow_succ']
  have hp0 : ENNReal.ofReal (|(F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det| ^ (m + 1)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (pow_pos (abs_pos.mpr (det_GL_ne_zero F.P)) _)).ne'
  unfold SplitFrame.stabMeasure
  rw [haarConst_eq F hc hQ, inv_inv, hpow, mul_comm (ENNReal.ofReal _) (ENNReal.ofReal _), mul_assoc,
    ENNReal.mul_inv_cancel hd0 ENNReal.ofReal_ne_top, mul_one]

end SplitFrame

/-- **The real stabilizer measure does not depend on the split frame**: for every split frame $P$ at $y$ (so
$Q(y) = c$), `realStabMeasure` (defined with the chosen frame `frameAt`) is
$|\det P|^{m+1}\,(h\mapsto P\,\mathrm{diag}(1,h)\,P^{-1})_*\mu_{Q'_P}$. -/
theorem realStabMeasure_eq_splitFrame (hm : 1 ≤ m) (hQ : gramDetR Q ≠ 0) (hc : c ≠ 0) (F : SplitFrame Q c y) :
    realStabMeasure Q hQ hc y = ENNReal.ofReal (|(F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det| ^ (m + 1)) •
      (lerayMeasure F.Q' (F.gramDetR_Q' hQ)).map F.stabHom := by
  have hn1 : (1 : ℕ) ≤ m + 1 := by omega
  rw [← F.stabMeasure_eq hc hQ]
  haveI := sigmaFinite_sig (Q := Q) hc
  haveI := F.sigmaFinite_stabMeasure hc hQ
  haveI := F.isMulRightInvariant_stabMeasure hc hQ
  have hy : y ∈ sph Q c := F.eval_y
  have hk0 : ENNReal.ofReal ((|2 * c| ^ m)⁻¹) ≠ 0 := (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos (abs_pos.mpr
    (mul_ne_zero two_ne_zero hc)) m))).ne'
  have hF := frameAt Q hc hy
  set F' := frameAt Q hc hy with hF'
  haveI := F'.sigmaFinite_stabMeasure hc hQ
  haveI := F'.isMulRightInvariant_stabMeasure hc hQ
  have hσ : sig Q c ≠ 0 := by
    intro h0
    have := F.lerayMeasure_eq_map_coord hc hm hQ
    rw [h0, Measure.zero_prod, Measure.map_zero, smul_zero] at this
    exact (isHaarMeasure_lerayMeasure hQ).toIsOpenPosMeasure.open_pos univ isOpen_univ univ_nonempty
      (by simp [this])
  have := stabMeasure_unique (σ := sig Q c) (y := y) (c := ENNReal.ofReal ((|2 * c| ^ m)⁻¹)) hk0
    ENNReal.ofReal_ne_top hσ (F'.coord hc hm hQ) (F.coord hc hm hQ) (F'.stabMeasure hc hQ) (F.stabMeasure hc hQ)
    (F'.lerayMeasure_eq_map_coord hc hm hQ) (F.lerayMeasure_eq_map_coord hc hm hQ)
  rw [realStabMeasure, dite_eq_left_of_eq_true (eq_true hy)]
  exact this

end Real

/-! ### Complex places -/

section Complex

open QuadFormsKB.Tamagawa.Measure.SphereLerayC QuadFormsKB.Tamagawa.Measure.OrbitalComplex

variable {m : ℕ} {Q : QuadForm ℂ (m + 1)} {c : ℂ} {y : Fin (m + 1) → ℂ}

namespace SplitFrameC

variable (F : SplitFrameC Q c y)

/-- **The Haar constant of a complex split frame**: $\kappa_P = \|\det P\|^{-2(m+2)}$. -/
theorem haarConst_eq (hc : c ≠ 0) (hQ : gramDetC Q ≠ 0) :
    ((F.haarConst hc hQ : ℝ≥0) : ℝ≥0∞) =
      (ENNReal.ofReal (‖(F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).det‖ ^ (2 * (m + 2))))⁻¹ := by
  have hQ' := F.gramDetC_Q' hQ
  have hQ1 := gramDetC_splitForm_ne_zero hc hQ'
  have hmap := map_lerayMeasureC_conjSOC' F.P 1 F.hessC one_ne_zero hQ hQ1
  have hinv : ∀ g, F.conj hc (conjSOC F.P 1 F.hessC one_ne_zero g) = g := fun g =>
    (conjSOC F.P 1 F.hessC one_ne_zero).symm_apply_apply g
  haveI := isHaarMeasure_lerayMeasureC hQ
  set D := ENNReal.ofReal (‖(1 : ℂ)‖ ^ (2 * ((m + 1) * (m + 1 + 1) / 2)) *
    ‖(F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).det‖ ^ (2 * (m + 1 + 1))) with hD
  have hconj := congrArg (fun μ => μ.map (F.conj hc)) hmap
  have hmc : Measurable (conjSOC F.P 1 F.hessC one_ne_zero) :=
    (conjSOC F.P 1 F.hessC one_ne_zero).continuous_toFun.measurable
  rw [Measure.map_map (F.continuous_conj hc).measurable hmc,
    Measure.map_smul _ (F.continuous_conj hc).measurable.aemeasurable, F.map_conj_lerayMeasureC hc hQ] at hconj
  have hid : (F.conj hc ∘ conjSOC F.P 1 F.hessC one_ne_zero) = id := funext hinv
  rw [hid, Measure.map_id] at hconj
  obtain ⟨k, hk⟩ : ∃ k, lerayMeasureC Q hQ (spanningSets (lerayMeasureC Q hQ) k) ≠ 0 := by
    by_contra hall
    push Not at hall
    have : lerayMeasureC Q hQ = 0 := by
      rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets (lerayMeasureC Q hQ)]
      exact measure_iUnion_null hall
    exact (isHaarMeasure_lerayMeasureC hQ).toIsOpenPosMeasure.open_pos univ isOpen_univ univ_nonempty
      (by simp [this])
  have hkt := measure_spanningSets_lt_top (lerayMeasureC Q hQ) k
  have h1 := congrArg (fun μ => μ (spanningSets (lerayMeasureC Q hQ) k)) hconj
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def] at h1
  have h2 : (F.haarConst hc hQ : ℝ≥0∞) * D = 1 := by
    have h3 : lerayMeasureC Q hQ (spanningSets (lerayMeasureC Q hQ) k) * ((F.haarConst hc hQ : ℝ≥0∞) * D) =
        lerayMeasureC Q hQ (spanningSets (lerayMeasureC Q hQ) k) * 1 := by
      rw [mul_one]
      calc _ = D * (↑(F.haarConst hc hQ) * (lerayMeasureC Q hQ) (spanningSets (lerayMeasureC Q hQ) k)) := by ring
        _ = _ := h1.symm
    exact (ENNReal.mul_right_inj hk hkt.ne).mp h3
  rw [ENNReal.eq_inv_of_mul_eq_one_left h2, hD]
  simp

/-- **The complex stabilizer measure at a split frame, in closed form**:
$\mu_{H_y} = \|\det P\|^{2(m+1)}\,(h\mapsto P\,\mathrm{diag}(1,h)\,P^{-1})_*\mu_{Q'}$. -/
theorem stabMeasure_eq (hc : c ≠ 0) (hQ : gramDetC Q ≠ 0) :
    F.stabMeasure hc hQ = ENNReal.ofReal (‖(F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).det‖ ^ (2 * (m + 1))) •
      (lerayMeasureC F.Q' (F.gramDetC_Q' hQ)).map (F.stabHom hc) := by
  have hj : F.jac = ENNReal.ofReal (‖(F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).det‖ ^ 2) := by
    unfold jac
    rw [← ENNReal.ofReal_coe_nnreal]
    simp
  have hpow : ENNReal.ofReal (‖(F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).det‖ ^ (2 * (m + 2))) =
      F.jac * ENNReal.ofReal (‖(F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).det‖ ^ (2 * (m + 1))) := by
    rw [hj, ← ENNReal.ofReal_mul (by positivity), ← pow_add]
    congr 2; ring
  unfold SplitFrameC.stabMeasure
  rw [haarConst_eq F hc hQ, inv_inv, hpow, mul_comm F.jac, mul_assoc,
    ENNReal.mul_inv_cancel F.jac_ne_zero F.jac_ne_top, mul_one]

end SplitFrameC

/-- **The complex stabilizer measure does not depend on the split frame**: for every split frame $P$ at $y$,
`complexStabMeasure` (defined with the chosen frame `frameAtC`) is
$\|\det P\|^{2(m+1)}\,(h\mapsto P\,\mathrm{diag}(1,h)\,P^{-1})_*\mu_{Q'_P}$. -/
theorem complexStabMeasure_eq_splitFrame (hm : 1 ≤ m) (hQ : gramDetC Q ≠ 0) (hc : c ≠ 0) (F : SplitFrameC Q c y) :
    complexStabMeasure Q hQ hc y =
      ENNReal.ofReal (‖(F.P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).det‖ ^ (2 * (m + 1))) •
        (lerayMeasureC F.Q' (F.gramDetC_Q' hQ)).map (F.stabHom hc) := by
  have hn1 : (1 : ℕ) ≤ m + 1 := by omega
  rw [← F.stabMeasure_eq hc hQ]
  haveI := sigmaFinite_sigC (Q := Q) hc hn1
  haveI := F.sigmaFinite_stabMeasure hc hQ
  haveI := F.isMulRightInvariant_stabMeasure hc hQ
  have hy : y ∈ sphC Q c := F.eval_y
  have hk0 : (((‖2 * c‖₊ ^ (2 * m))⁻¹ : ℝ≥0) : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ (nnnorm_ne_zero_iff.mpr (mul_ne_zero two_ne_zero hc))))
  set F' := frameAtC Q hc hy with hF'
  haveI := F'.sigmaFinite_stabMeasure hc hQ
  haveI := F'.isMulRightInvariant_stabMeasure hc hQ
  have hσ : sigC Q c ≠ 0 := by
    intro h0
    have := F.lerayMeasureC_eq_map_coord hc hm hQ
    rw [h0, Measure.zero_prod, Measure.map_zero, smul_zero] at this
    exact (isHaarMeasure_lerayMeasureC hQ).toIsOpenPosMeasure.open_pos univ isOpen_univ univ_nonempty
      (by simp [this])
  have := stabMeasure_unique (σ := sigC Q c) (y := y) (c := (((‖2 * c‖₊ ^ (2 * m))⁻¹ : ℝ≥0) : ℝ≥0∞)) hk0
    ENNReal.coe_ne_top hσ (F'.coord hc hm hQ) (F.coord hc hm hQ) (F'.stabMeasure hc hQ) (F.stabMeasure hc hQ)
    (F'.lerayMeasureC_eq_map_coord hc hm hQ) (F.lerayMeasureC_eq_map_coord hc hm hQ)
  rw [complexStabMeasure, dite_eq_left_of_eq_true (eq_true hy)]
  exact this

end Complex

end QuadFormsKB.Tamagawa.Indefinite
