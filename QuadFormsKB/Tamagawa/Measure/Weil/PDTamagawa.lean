import QuadFormsKB.Tamagawa.Measure.Weil.PDFinRatio
import QuadFormsKB.Tamagawa.OrbitalEuler
import QuadFormsKB.Tamagawa.Measure.Weil.PDArchMass

/-!
# $\tau(PD^\times)$ for Weil's quotient measure: the product formula $r_\infty r_f = 1$

**Layer:** $F$ a number field, $a, b \in \mathcal O_F\setminus 0$, $D = \mathbb H[F,a,b]$, $Q_0 = \langle -a,-b,ab\rangle$.

**Proves**
* `rF_toReal_eq_finprod`: $r_f = \mathrm{vol}(\hat{\mathcal O})^3\prod_v|8a^3b^3|_v = |d_F|^{-3/2}\prod_v|8a^3b^3|_v$
  (from `rF_toReal`; every finite place, with the product over all places $v$);
* `tamagawaNumberTwoAdelic_iff_tauPD` (any $F$, any $D$): with Weil's finite quotient measure `muPDFin`, the
  equivalence `TamagawaNumberTwoAdelic` $\iff\tau(PD^\times) = 2$ holds for every archimedean measure satisfying the
  archimedean comparison (only that comparison is a hypothesis);
* totally definite $D$ over a totally real $F$: `cI` (Weil's quotient mass $\prod_w\mathrm{vol}(D_w^\times/\mathbb R^\times) =
  \prod_w\pi^2/(\sigma_w(a)\sigma_w(b))$, `PDArchMass.lean`), `muPDInf` (the Haar measure of total mass $c_I$ on
  $PD^\times(F_\infty)$, `muPDInf_univ`), `map_muPDInf`, `muArchTamSO_univ` ($c_F\prod_w\pi^2/(8\sigma_w(a)^4\sigma_w(b)^4)$),
  **`rI_mul_rF`** (Weil's product formula $r_\infty r_f = 1$, via `finprod_norm_eq`) and
  **`tauPD_eq_two_of_definite`**: $\mathrm{covol}(PD^\times(F)\backslash PD^\times(\mathbb A), \mu_\infty\times\mu_f) = 2$
  unconditionally (`covolume_pd_eq_two_of_definite` with all hypotheses discharged; no Fujisaki).

*Scope note.* $c_I$ is computed from Weil's local archimedean gauge measures $\operatorname{nrd}_w^{-2}dx_w$ and
$|t|^{-1}dt$ in the coordinates $1,i,j,k$ (Lebesgue), which are the place-by-place factors of `omegaQuatInf`
and the archimedean idele measure; the identification of `omegaQuatInf` on product sets with $\prod_w$ of these
local measures is bookkeeping not formalized here.
-/

open MeasureTheory Matrix Quaternion NumberField IsDedekindDomain WithZero Set Filter
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.QuatZeta

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}

local notation "Q₀" => pureFormO a b

/-- The global constant $c = 8a^3b^3$ of Weil's Thm 2.3.1 for $PD^\times \cong SO(D^0)$. -/
abbrev cWeil (a b : 𝓞 F) : 𝓞 F := 8 * a ^ 3 * b ^ 3

theorem cWeil_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : cWeil a b ≠ 0 := by
  unfold cWeil
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ ha)) (pow_ne_zero _ hb)

theorem valued_cWeil (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (algebraMap F (v.adicCompletion F) ((cWeil a b : 𝓞 F) : F)) =
      exp (-((3 * (sExp v + eExp a ha v + eExp b hb v) : ℕ) : ℤ)) := by
  have h8 : ((cWeil a b : 𝓞 F) : F) = 2 ^ 3 * (a : F) ^ 3 * (b : F) ^ 3 := by
    rw [show ((cWeil a b : 𝓞 F) : F) = algebraMap (𝓞 F) F (8 * a ^ 3 * b ^ 3) from rfl]
    simp only [map_mul, map_pow, map_ofNat]; norm_num
  rw [h8]
  simp only [map_mul, map_pow, map_ofNat, valued_two_eq, valued_eExp a ha, valued_eExp b hb,
    ← WithZero.exp_nsmul, ← WithZero.exp_add]
  congr 1; push_cast; ring

/-- **$r_f$ as a product over all finite places:** $r_f = \mathrm{vol}(\hat{\mathcal O})^3\prod_v|8a^3b^3|_v$. -/
theorem rF_toReal_eq_finprod (ha : a ≠ 0) (hb : b ≠ 0) :
    (rF a b).toReal = ohatVol F ^ 3 *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (v.adicCompletion F) ((cWeil a b : 𝓞 F) : F)‖ := by
  set S := badSet ha hb
  set ν : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (Analysis.selfDualV v).real (Analysis.latticeV v 0)
  set N : HeightOneSpectrum (𝓞 F) → ℝ := fun v => ‖algebraMap F (v.adicCompletion F) ((cWeil a b : 𝓞 F) : F)‖
  set e : HeightOneSpectrum (𝓞 F) → ℕ := fun v => 3 * (sExp v + eExp a ha v + eExp b hb v)
  have hN : ∀ v, N v = ((LocalDensity.DVR.q (v.adicCompletionIntegers F) : ℝ) ^ e v)⁻¹ := by
    intro v
    have h := valued_cWeil ha hb v
    rw [← coe_ι] at h
    obtain ⟨h1, h2⟩ := pow_dvd_of_valued h
    simp only [N]
    rw [← coe_ι]
    exact QuadFormsKB.Tamagawa.norm_coe_of_pow_dvd v h1 h2
  have hoff : ∀ v ∉ S, ν v = 1 ∧ e v = 0 := by
    intro v hv
    obtain ⟨h2, hav, hbv, hvol, -⟩ := goodPlace_of_not_mem_badSet ha hb hv
    refine ⟨hvol, ?_⟩
    have hs : sExp v = 0 := by
      have := (valued_two_eq v).symm.trans h2
      rw [← WithZero.exp_zero, WithZero.exp_inj] at this; omega
    have hea : eExp a ha v = 0 := by
      have := (valued_eExp a ha v).symm.trans hav
      rw [← WithZero.exp_zero, WithZero.exp_inj] at this; omega
    have heb : eExp b hb v = 0 := by
      have := (valued_eExp b hb v).symm.trans hbv
      rw [← WithZero.exp_zero, WithZero.exp_inj] at this; omega
    simp only [e, hs, hea, heb]
  have hfinν : Function.HasFiniteMulSupport ν := mulSupport_volO_real_finite (F := F)
  have hfinN : Function.HasFiniteMulSupport N := (S.finite_toSet).subset fun v hv => by
    by_contra h
    exact (Function.mem_mulSupport.mp hv) (by rw [hN, (hoff v h).2, pow_zero, inv_one])
  have hfin3 : Function.HasFiniteMulSupport (fun i => ν i ^ 3) := hfinν.pow 3
  rw [rF_toReal ha hb, ohatVol_eq_finprod, finprod_pow hfinν,
    ← finprod_mul_distrib (f := fun i => ν i ^ 3) (g := N) hfin3 hfinN,
    finprod_eq_prod_of_mulSupport_subset _ (s := S) (fun v hv => by
      by_contra h
      apply Function.mem_mulSupport.mp hv
      simp only [(hoff v h).1, one_pow, one_mul, hN, (hoff v h).2, pow_zero, inv_one])]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [hN, div_eq_mul_inv]


/-! ### General $D/F$: the finite side is unconditional -/

/-- **`TamagawaNumberTwoAdelic` $\iff\tau(PD^\times) = 2$ with the finite quotient measure fixed** (any number field, any
quaternion algebra $(a,b)_F$): for every left-invariant s-finite $\mu_\infty$ on $PD^\times(F_\infty)$ whose image is
$r_\infty\cdot\mu^{\mathrm{Tam}}_\infty$ with $r_\infty r_f = 1$, Weil's quotient measure `muPDFin` on $PD^\times(\mathbb A_f)$
satisfies the hypothesis hF unconditionally (`map_muPDFin`); only the archimedean comparison remains a hypothesis.
For totally definite $D$ over totally real $F$ the archimedean comparison is `map_muPDInf` + `rI_mul_rF`. -/
@[kb "weil1982" "§2.3, Thm 2.3.1; §3.7(a), p. 63; Thm 3.2.1, p. 43"]
theorem tamagawaNumberTwoAdelic_iff_tauPD (ha : a ≠ 0) (hb : b ≠ 0) (μI : Measure (PDInf a b)) [SFinite μI]
    [μI.IsMulLeftInvariant] {rInf : ℝ≥0∞}
    (hI : μI.map (pdInfEquiv a b ha hb) = rInf • muArchTamSO Q₀ (nondegenerate_pureFormO a b ha hb))
    (hr : rInf * rF a b = 1) :
    TamagawaNumberTwoAdelic Q₀ (nondegenerate_pureFormO a b ha hb) ↔
      covolume (pdGammaSplit a b ha hb) (PDInf a b × PDFin a b) (μI.prod (muPDFin ha hb)) = 2 :=
  tamagawaNumberTwoAdelic_iff_covolume_pd a b ha hb _ μI (muPDFin ha hb) hI (map_muPDFin ha hb) hr

/-! ### The archimedean side for a totally definite $D$ over a totally real $F$ -/

section Definite

open scoped Classical

open NumberField.InfinitePlace QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.Measure.LerayArch

theorem archVolSO_three {d : ℝ} (hd : 0 < d) : QuadFormsKB.Tamagawa.archVolSO 3 d = Real.pi ^ 2 / (8 * d ^ 2) := by
  unfold QuadFormsKB.Tamagawa.archVolSO
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  norm_num
  have h1 : Real.Gamma (1 / 2) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
  have h3 : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), h1]; ring
  have hp1 : Real.pi ^ (1 / 2 : ℝ) = Real.sqrt Real.pi := (Real.sqrt_eq_rpow Real.pi).symm
  have hp3 : Real.pi ^ (3 / 2 : ℝ) = Real.pi * Real.sqrt Real.pi := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add Real.pi_pos, Real.rpow_one, hp1]
  have hs : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [hp1, h1, hp3, h3]
  have hsq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  field_simp
  nlinarith [hsq]

/-- The real embedding at a real place $w$. -/
abbrev sigW (w : {w : InfinitePlace F // w.IsReal}) : F →+* ℝ := embedding_of_isReal w.2

theorem eval_QRe_pureFormO (w : {w : InfinitePlace F // w.IsReal}) (x : Fin 3 → ℝ) :
    (QRe (pureFormO a b) w).eval x = sigW w (-(a : F)) * x 0 ^ 2 + sigW w (-(b : F)) * x 1 ^ 2 +
      sigW w ((a : F) * b) * x 2 ^ 2 := by
  simp [QRe, QuadForm.eval, QuadForm.evalIn, QuadForm.map, pureFormO, QuadForm.diag, Matrix.diagonal,
    Fin.sum_univ_three]
  ring

theorem gramDetR_QRe_pureFormO (w : {w : InfinitePlace F // w.IsReal}) :
    gramDetR (QRe (pureFormO a b) w) = (sigW w (a : F)) ^ 2 * (sigW w (b : F)) ^ 2 := by
  simp [gramDetR, QRe, QuadForm.hessian, QuadForm.map, pureFormO, QuadForm.diag, Matrix.det_fin_three,
    Matrix.diagonal]
  ring

/-- For $\langle -a,-b,ab\rangle$ positive definite at $w$: $\sigma_w(a), \sigma_w(b) < 0$. -/
theorem sigW_neg_of_posDef {w : {w : InfinitePlace F // w.IsReal}} (h : IsPosDefR (QRe (pureFormO a b) w)) :
    sigW w (a : F) < 0 ∧ sigW w (b : F) < 0 := by
  have h0 := h (Pi.single 0 1) (by simp)
  have h1 := h (Pi.single 1 1) (by simp)
  rw [eval_QRe_pureFormO] at h0 h1
  simp at h0 h1
  exact ⟨by linarith, by linarith⟩

variable [IsTotallyReal F]

variable (a b) in
/-- **Weil's quotient mass of $PD^\times(F_\infty) = \prod_w D_w^\times/\mathbb R^\times$** (totally real $F$): the product of
the local masses `cArch` (`cArch_eq`: $\pi^2/(\sigma_w(a)\sigma_w(b))$ at each definite place). -/
def cI : ℝ := ∏ w : {w : InfinitePlace F // w.IsReal}, cArch (sigW w (a : F)) (sigW w (b : F))

theorem cI_eq (hpos : ∀ w : {w : InfinitePlace F // w.IsReal}, sigW w (a : F) < 0 ∧ sigW w (b : F) < 0) :
    cI a b = ∏ w : {w : InfinitePlace F // w.IsReal}, Real.pi ^ 2 / (sigW w (a : F) * sigW w (b : F)) :=
  Finset.prod_congr rfl fun w _ => cArch_eq (hpos w).1 (hpos w).2

/-- **The total Tamagawa mass of $G_\infty = \prod_w SO(Q^{\sigma_w})(\mathbb R)$** (definite):
$c_F\prod_w\mathrm{vol}_{\mathrm{Leray}}(SO(Q^{\sigma_w})(\mathbb R))$. -/
theorem muArchTamSO_univ (ha : a ≠ 0) (hb : b ≠ 0) (hpd : IsTotallyPosDef (QuadFormsKB.HilbertModular.formF Q₀)) :
    muArchTamSO Q₀ (nondegenerate_pureFormO a b ha hb) Set.univ =
      ENNReal.ofReal (cF F 3) * ∏ w : {w : InfinitePlace F // w.IsReal},
        ENNReal.ofReal (QuadFormsKB.Tamagawa.archVolSO 3 (gramDetR (QRe Q₀ w))) := by
  have hQ := nondegenerate_pureFormO a b ha hb
  have : ∀ w, Fact (IsPosDefR (QRe Q₀ w)) := fun w => ⟨isPosDefR_QRe Q₀ hQ hpd w⟩
  have hC : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => (not_isComplex_iff_isReal.mpr (IsTotallyReal.isReal w.1)) w.2⟩
  have hsf : ∀ w, SigmaFinite (lerayMeasure (QRe Q₀ w) (gramDetR_QRe_ne_zero Q₀ hQ w)) := fun w => by
    have := isHaarMeasure_lerayMeasure (gramDetR_QRe_ne_zero Q₀ hQ w); infer_instance
  have hsfC : ∀ i : {w : InfinitePlace F // w.IsComplex},
      SigmaFinite (LerayComplex.lerayMeasureC (QCx Q₀ i) (gramDetC_QCx_ne_zero Q₀ hQ i)) :=
    fun i => isEmptyElim i
  rw [muArchTamSO, Measure.smul_apply, smul_eq_mul, muArchNF, muArchLeray, ← Set.univ_prod_univ,
    Measure.prod_prod, Measure.pi_univ, Measure.pi_univ,
    Finset.univ_eq_empty (α := {w : InfinitePlace F // w.IsComplex}), Finset.prod_empty, mul_one]
  congr 1
  exact Finset.prod_congr rfl fun w _ => lerayMeasure_univ _ (by norm_num)

/-- $\prod_\sigma\|\sigma x\| = \prod_w|\sigma_w(x)|$ for totally real $F$. -/
theorem prod_norm_embeddings_eq_prod_sigW (x : F) :
    ∏ σ : F →ₐ[ℚ] ℂ, ‖σ x‖ = ∏ w : {w : InfinitePlace F // w.IsReal}, |sigW w x| := by
  refine Fintype.prod_equiv realPlaceEquiv _ _ fun σ => ?_
  rw [sigW, embedding_realPlaceEquiv rfl, ← realEmb_apply, Complex.norm_real, Real.norm_eq_abs]

theorem ohatVol_pow_three : ohatVol F ^ 3 = cF F 3 := by
  have hd : 0 < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero (K := F))
  rw [ohatVol, cF, Real.sqrt_eq_rpow, ← Real.rpow_neg hd.le, ← Real.rpow_natCast, ← Real.rpow_mul hd.le]
  norm_num

theorem muArchTamSO_univ_toReal (ha : a ≠ 0) (hb : b ≠ 0)
    (hpd : IsTotallyPosDef (QuadFormsKB.HilbertModular.formF Q₀)) :
    (muArchTamSO Q₀ (nondegenerate_pureFormO a b ha hb) Set.univ).toReal =
      cF F 3 * ∏ w : {w : InfinitePlace F // w.IsReal},
        Real.pi ^ 2 / (8 * ((sigW w (a : F)) ^ 2 * (sigW w (b : F)) ^ 2) ^ 2) := by
  have hQ := nondegenerate_pureFormO a b ha hb
  have hpos := fun w => sigW_neg_of_posDef (a := a) (b := b) (isPosDefR_QRe Q₀ hQ hpd w)
  rw [muArchTamSO_univ ha hb hpd, ENNReal.toReal_mul, ENNReal.toReal_ofReal cF_nonneg, ENNReal.toReal_prod]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  have hd : 0 < (sigW w (a : F)) ^ 2 * (sigW w (b : F)) ^ 2 := by
    have := (hpos w).1.ne; have := (hpos w).2.ne; positivity
  rw [gramDetR_QRe_pureFormO, archVolSO_three hd, ENNReal.toReal_ofReal (by positivity)]

theorem muArchTamSO_univ_pos (ha : a ≠ 0) (hb : b ≠ 0)
    (hpd : IsTotallyPosDef (QuadFormsKB.HilbertModular.formF Q₀)) :
    0 < (muArchTamSO Q₀ (nondegenerate_pureFormO a b ha hb) Set.univ).toReal := by
  have hQ := nondegenerate_pureFormO a b ha hb
  have hpos := fun w => sigW_neg_of_posDef (a := a) (b := b) (isPosDefR_QRe Q₀ hQ hpd w)
  rw [muArchTamSO_univ_toReal ha hb hpd]
  have hcF : 0 < cF F 3 := by
    rw [← ohatVol_pow_three]; exact pow_pos ohatVol_pos 3
  refine mul_pos hcF (Finset.prod_pos fun w _ => div_pos (pow_pos Real.pi_pos 2) ?_)
  have := (hpos w).1.ne; have := (hpos w).2.ne
  positivity

variable (a b) in
/-- **The archimedean ratio** $r_\infty = c_I/\mu^{\mathrm{Tam}}_\infty(G_\infty)$. -/
def rI (ha : a ≠ 0) (hb : b ≠ 0) : ℝ≥0∞ :=
  ENNReal.ofReal (cI a b) / muArchTamSO Q₀ (nondegenerate_pureFormO a b ha hb) Set.univ

/-- **Weil's quotient measure on $PD^\times(F_\infty)$** (totally definite $D$, totally real $F$): the Haar measure of total
mass $c_I = \prod_w\mathrm{vol}(D_w^\times/\mathbb R^\times)$ (`muPDInf_univ`), realized on the compact group
$PD^\times(F_\infty)$ as a multiple of the transport of $\mu^{\mathrm{Tam}}_\infty$. -/
@[kb "weil1982" "§2.3, p. 21; §3.7(a), p. 63"]
def muPDInf (ha : a ≠ 0) (hb : b ≠ 0) : Measure (PDInf a b) :=
  rI a b ha hb • (muArchTamSO Q₀ (nondegenerate_pureFormO a b ha hb)).map (pdInfEquiv a b ha hb).symm

theorem measurable_pdInfEquiv (ha : a ≠ 0) (hb : b ≠ 0) :
    Measurable (⇑(pdInfEquiv a b ha hb) : PDInf a b → GInfSO Q₀) := (map_continuous _).measurable

theorem measurable_pdInfEquiv_symm (ha : a ≠ 0) (hb : b ≠ 0) :
    Measurable (⇑(pdInfEquiv a b ha hb).symm : GInfSO Q₀ → PDInf a b) := (map_continuous _).measurable

theorem map_muPDInf (ha : a ≠ 0) (hb : b ≠ 0) :
    (muPDInf ha hb).map (pdInfEquiv a b ha hb) = rI a b ha hb • muArchTamSO Q₀ (nondegenerate_pureFormO a b ha hb) := by
  rw [muPDInf, Measure.map_smul,
    Measure.map_map (measurable_pdInfEquiv ha hb) (measurable_pdInfEquiv_symm ha hb)]
  · congr 1
    convert Measure.map_id
    funext x
    simp
  · exact (measurable_pdInfEquiv ha hb).aemeasurable

instance (ha : a ≠ 0) (hb : b ≠ 0) : SFinite (muPDInf ha hb) := by
  unfold muPDInf; infer_instance

instance (ha : a ≠ 0) (hb : b ≠ 0) : (muPDInf ha hb).IsMulLeftInvariant := by
  unfold muPDInf
  have := isMulLeftInvariant_map (μ := muArchTamSO Q₀ (nondegenerate_pureFormO a b ha hb))
    (pdInfEquiv a b ha hb).symm.toMulEquiv.toMonoidHom.toMulHom (measurable_pdInfEquiv_symm ha hb)
    (pdInfEquiv a b ha hb).symm.surjective
  have : (Measure.map (⇑(pdInfEquiv a b ha hb).symm)
    (muArchTamSO Q₀ (nondegenerate_pureFormO a b ha hb))).IsMulLeftInvariant := this
  infer_instance

/-- **The normalization of `muPDInf`:** total mass $c_I$. -/
theorem muPDInf_univ (ha : a ≠ 0) (hb : b ≠ 0) (hpd : IsTotallyPosDef (QuadFormsKB.HilbertModular.formF Q₀)) :
    muPDInf ha hb Set.univ = ENNReal.ofReal (cI a b) := by
  have h0 := muArchTamSO_univ_pos ha hb hpd
  have hM0 : muArchTamSO Q₀ (nondegenerate_pureFormO a b ha hb) Set.univ ≠ 0 := fun h => by
    rw [h, ENNReal.toReal_zero] at h0; exact lt_irrefl _ h0
  have hMt : muArchTamSO Q₀ (nondegenerate_pureFormO a b ha hb) Set.univ ≠ ⊤ := fun h => by
    rw [h, ENNReal.toReal_top] at h0; exact lt_irrefl _ h0
  rw [muPDInf, Measure.smul_apply, Measure.map_apply (measurable_pdInfEquiv_symm ha hb) MeasurableSet.univ,
    Set.preimage_univ, smul_eq_mul, rI, ENNReal.div_mul_cancel hM0 hMt]

/-- **Weil's product formula for $PD^\times \cong SO(D^0)$** (totally definite $D$, totally real $F$): $r_\infty r_f = 1$.
The local ratios are $|8a^3b^3|_v\,\mathrm{vol}(\mathfrak o_v)^3$ at the finite places and $|8a^3b^3|_w$ at the real places
(times $c_F = |d_F|^{-3/2}$), and $\prod_v|8a^3b^3|_v = 1$ (OrbitalEuler's `finprod_norm_eq`). -/
@[kb "weil1982" "§2.3, Thm 2.3.1 (product formula for local ratios) [unverified]"]
theorem rI_mul_rF (ha : a ≠ 0) (hb : b ≠ 0) (hpd : IsTotallyPosDef (QuadFormsKB.HilbertModular.formF Q₀)) :
    rI a b ha hb * rF a b = 1 := by
  have hQ := nondegenerate_pureFormO a b ha hb
  have hpos := fun w => sigW_neg_of_posDef (a := a) (b := b) (isPosDefR_QRe Q₀ hQ hpd w)
  have h0 := muArchTamSO_univ_pos ha hb hpd
  set M := muArchTamSO Q₀ hQ Set.univ
  have hM0 : M ≠ 0 := fun h => by rw [h, ENNReal.toReal_zero] at h0; exact lt_irrefl _ h0
  have hMt : M ≠ ⊤ := fun h => by rw [h, ENNReal.toReal_top] at h0; exact lt_irrefl _ h0
  -- the real identity `c_I r_f = M`
  have hc : (cWeil a b : F) ≠ 0 := by exact_mod_cast cWeil_ne_zero ha hb
  have key : cI a b * (rF a b).toReal = M.toReal := by
    rw [rF_toReal_eq_finprod ha hb, QuadFormsKB.Tamagawa.finprod_norm_eq _ hc,
      prod_norm_embeddings_eq_prod_sigW, muArchTamSO_univ_toReal ha hb hpd, cI_eq hpos, ohatVol_pow_three,
      ← Finset.prod_inv_distrib]
    rw [show (∏ w : {w : InfinitePlace F // w.IsReal}, Real.pi ^ 2 / (sigW w (a : F) * sigW w (b : F))) *
        (cF F 3 * ∏ w : {w : InfinitePlace F // w.IsReal}, |sigW w ((cWeil a b : 𝓞 F) : F)|⁻¹) =
        cF F 3 * ∏ w : {w : InfinitePlace F // w.IsReal},
          (Real.pi ^ 2 / (sigW w (a : F) * sigW w (b : F)) * |sigW w ((cWeil a b : 𝓞 F) : F)|⁻¹) by
      rw [Finset.prod_mul_distrib]; ring]
    congr 1
    refine Finset.prod_congr rfl fun w _ => ?_
    have hA := (hpos w).1
    have hB := (hpos w).2
    have hcw : sigW w ((cWeil a b : 𝓞 F) : F) = 8 * (sigW w (a : F)) ^ 3 * (sigW w (b : F)) ^ 3 := by
      rw [show ((cWeil a b : 𝓞 F) : F) = 8 * (a : F) ^ 3 * (b : F) ^ 3 by
        rw [show ((cWeil a b : 𝓞 F) : F) = algebraMap (𝓞 F) F (8 * a ^ 3 * b ^ 3) from rfl]
        simp only [map_mul, map_pow, map_ofNat]]
      simp only [map_mul, map_pow, map_ofNat]
    have hpos8 : 0 < 8 * (sigW w (a : F)) ^ 3 * (sigW w (b : F)) ^ 3 := by
      have : 0 < sigW w (a : F) * sigW w (b : F) := mul_pos_of_neg_of_neg hA hB
      nlinarith [pow_pos this 3]
    rw [hcw, abs_of_pos hpos8]
    have hA0 : sigW w (a : F) ≠ 0 := hA.ne
    have hB0 : sigW w (b : F) ≠ 0 := hB.ne
    field_simp
  have hrF := rF_ne_top ha hb
  have hcI : 0 ≤ cI a b := by
    rw [cI_eq hpos]; exact Finset.prod_nonneg fun w _ => (div_pos (pow_pos Real.pi_pos 2)
      (mul_pos_of_neg_of_neg (hpos w).1 (hpos w).2)).le
  rw [rI, div_eq_mul_inv, mul_comm (ENNReal.ofReal (cI a b)), mul_assoc,
    show ENNReal.ofReal (cI a b) * rF a b = M by
      rw [← ENNReal.ofReal_toReal hrF, ← ENNReal.ofReal_mul hcI, key, ENNReal.ofReal_toReal hMt],
    ENNReal.inv_mul_cancel hM0 hMt]

/-- **$\tau(PD^\times) = 2$ for Weil's quotient Tamagawa measure, unconditionally** ($D = (a,b)_F$ totally definite over a
totally real field $F$): the covolume of $PD^\times(F)$ in $PD^\times(\mathbb A) = PD^\times(F_\infty)\times PD^\times(\mathbb A_f)$
for `muPDInf` $\times$ `muPDFin` is $2$. `covolume_pd_eq_two_of_definite` with the hypotheses discharged by
`map_muPDInf`, `map_muPDFin` and the product formula `rI_mul_rF`. No Fujisaki, no zeta function of $D$. -/
@[kb "weil1982" "Thm 3.2.1, p. 43; §3.7(a), p. 63; Thm 2.3.1 [unverified]"]
theorem tauPD_eq_two_of_definite (ha : a ≠ 0) (hb : b ≠ 0)
    (hpd : IsTotallyPosDef (QuadFormsKB.HilbertModular.formF Q₀)) :
    covolume (pdGammaSplit a b ha hb) (PDInf a b × PDFin a b) ((muPDInf ha hb).prod (muPDFin ha hb)) = 2 :=
  covolume_pd_eq_two_of_definite a b ha hb (nondegenerate_pureFormO a b ha hb) hpd (muPDInf ha hb) (muPDFin ha hb)
    (map_muPDInf ha hb) (map_muPDFin ha hb) (rI_mul_rF ha hb hpd)

end Definite

end QuadFormsKB.Tamagawa.Measure.Weil
