import QuadFormsKB.Tamagawa.Measure.Weil.SimilarArchGlobal
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryIsoSimilar

/-!
# Equivalent forms over $F$: the archimedean group, measure and character

**Layer:** a number field $F$, $Q_0, Q_1$ forms over $\mathcal O_F$ in $n$ variables, and $P\in GL_n(F)$ with
$H_{Q_1} = P^{\mathsf T}H_{Q_0}P$ over $F$ (the relation is given directly on the Hessians). This is the
$F$-rational version (with $c=1$) of `SimilarArchGlobal.lean`, used for changes of frame data.

**Defines**
* `equivConjInf P hP : GInfSO Q₀ ≃ₜ* GInfSO Q₁`: the product over all archimedean places of the conjugations
  $g\mapsto P_w^{-1}gP_w$ (`LerayReal.conjSO`, `LerayComplex.conjSOC` with $c=1$), $P_w=\sigma_w(P)$.

**Proves**
* `hessian_QRe_equivF`, `hessian_QCx_equivF`: $H_1^{w} = P_w^{\mathsf T}H_0^{w}P_w$ at each archimedean place;
* **`map_muArchTamSO_equivConjInf`**:
  $(\mathrm{conj})_*\mu^{\mathrm{Tam}}_\infty(Q_0) = \prod_{w\mid\infty}w(\det P)^{(n+1)n_w}\cdot\mu^{\mathrm{Tam}}_\infty(Q_1)$,
  $n_w\in\{1,2\}$ the multiplicity of $w$;
* `isIsoVec_equivF`, **`isoCharInf_equivConjInf`** (binary case): $\chi_{P^{-1}e}(P^{-1}gP)=\chi_e(g)$ at infinity.

Indices are 0-based. Source: Weil 1982, §2.2.1, §2.3.
-/

open MeasureTheory Measure Matrix
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace QuadFormsKB.Tamagawa.Measure.LerayArch
  QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex
  QuadFormsKB.Tamagawa.ArchSOMeasure

section Main

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {Q₀ Q₁ : QuadForm (𝓞 F) n} (P : GL (Fin n) F)
  (hP : (Q₁.map (algebraMap (𝓞 F) F)).hessian =
    (P : Matrix (Fin n) (Fin n) F)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian * (P : Matrix (Fin n) (Fin n) F))

include hP in
/-- The Hessian relation $H_1 = 1\cdot P_\sigma^{\mathsf T}H_0P_\sigma$ after any ring map $\sigma : F\to S$. -/
theorem equivF_hessian_map_gen {S : Type*} [CommRing S] (σ : F →+* S) :
    (((Q₁.map (algebraMap (𝓞 F) F)).map σ).hessian) = (1 : S) •
      (((Matrix.GeneralLinearGroup.map σ P : GL (Fin n) S) : Matrix (Fin n) (Fin n) S)ᵀ *
        (((Q₀.map (algebraMap (𝓞 F) F)).map σ).hessian) *
        ((Matrix.GeneralLinearGroup.map σ P : GL (Fin n) S) : Matrix (Fin n) (Fin n) S)) := by
  rw [Siegel.hessian_map_NF σ, hP, Siegel.hessian_map_NF σ, one_smul]
  show _ = (((P : Matrix (Fin n) (Fin n) F).map σ)ᵀ * _ * (P : Matrix (Fin n) (Fin n) F).map σ)
  rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]

include hP in
/-- The Hessian relation at a real place: $H_1^{w} = P_w^{\mathsf T}H_0^{w}P_w$ (with the scalar $1$). -/
theorem hessian_QRe_equivF (w : {w : InfinitePlace F // w.IsReal}) :
    (QRe Q₁ w).hessian = (1 : ℝ) •
      (((Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) P : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ *
        (QRe Q₀ w).hessian *
        ((Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) P : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) :=
  equivF_hessian_map_gen P hP _

include hP in
/-- The Hessian relation at a complex place: $H_1^{w} = P_w^{\mathsf T}H_0^{w}P_w$ (with the scalar $1$). -/
theorem hessian_QCx_equivF (w : {w : InfinitePlace F // w.IsComplex}) :
    (QCx Q₁ w).hessian = (1 : ℂ) •
      (((Matrix.GeneralLinearGroup.map w.1.embedding P : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ *
        (QCx Q₀ w).hessian *
        ((Matrix.GeneralLinearGroup.map w.1.embedding P : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) :=
  equivF_hessian_map_gen P hP _

/-- **The conjugation isomorphism $G_\infty(Q_0)\cong G_\infty(Q_1)$**, $g\mapsto P_w^{-1}gP_w$ at every
archimedean place $w$, where $H_{Q_1}=P^{\mathsf T}H_{Q_0}P$ over $F$. -/
def equivConjInf : GInfSO Q₀ ≃ₜ* GInfSO Q₁ :=
  simProdCongr
    (simPiCongr fun w : {w : InfinitePlace F // w.IsReal} =>
      conjSO (Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) P) 1
        (hessian_QRe_equivF P hP w) one_ne_zero)
    (simPiCongr fun w : {w : InfinitePlace F // w.IsComplex} =>
      conjSOC (Matrix.GeneralLinearGroup.map w.1.embedding P) 1
        (hessian_QCx_equivF P hP w) one_ne_zero)

/-- The real components of `equivConjInf`. -/
theorem equivConjInf_fst (g : GInfSO Q₀) (w : {w : InfinitePlace F // w.IsReal}) :
    (equivConjInf P hP g).1 w = conjSO (Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) P) 1
      (hessian_QRe_equivF P hP w) one_ne_zero (g.1 w) := rfl

/-- The complex components of `equivConjInf`. -/
theorem equivConjInf_snd (g : GInfSO Q₀) (w : {w : InfinitePlace F // w.IsComplex}) :
    (equivConjInf P hP g).2 w = conjSOC (Matrix.GeneralLinearGroup.map w.1.embedding P) 1
      (hessian_QCx_equivF P hP w) one_ne_zero (g.2 w) := rfl

/-- The determinant of the image of $P$ under a ring map is the image of $\det P$. -/
theorem equivF_det_embed {S : Type*} [Field S] (σ : F →+* S) :
    ((Matrix.GeneralLinearGroup.map σ P : GL (Fin n) S) : Matrix (Fin n) (Fin n) S).det =
      σ (P : Matrix (Fin n) (Fin n) F).det := by
  show (((P : Matrix (Fin n) (Fin n) F).map σ)).det = _
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]

/-- The real-place Jacobian factor: $|1|^{n(n+1)/2}\,|\det P_w|^{n+1} = w(\det P)^{(n+1)\cdot n_w}$. -/
theorem equivF_factor_real (w : {w : InfinitePlace F // w.IsReal}) :
    |(1 : ℝ)| ^ (n * (n + 1) / 2) *
        |((Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) P : GL (Fin n) ℝ) :
          Matrix (Fin n) (Fin n) ℝ).det| ^ (n + 1) =
      w.1 (P : Matrix (Fin n) (Fin n) F).det ^ ((n + 1) * w.1.mult) := by
  have h : ∀ x : F, |embedding_of_isReal w.2 x| = w.1 x := fun x => by
    rw [← Real.norm_eq_abs, norm_embedding_of_isReal]
  rw [equivF_det_embed, mult_isReal, mul_one, h]
  simp

/-- The complex-place Jacobian factor: $\|1\|^{n(n+1)}\,\|\det P_w\|^{2(n+1)} = w(\det P)^{(n+1)\cdot n_w}$. -/
theorem equivF_factor_complex (w : {w : InfinitePlace F // w.IsComplex}) :
    ‖(1 : ℂ)‖ ^ (2 * (n * (n + 1) / 2)) *
        ‖((Matrix.GeneralLinearGroup.map w.1.embedding P : GL (Fin n) ℂ) :
          Matrix (Fin n) (Fin n) ℂ).det‖ ^ (2 * (n + 1)) =
      w.1 (P : Matrix (Fin n) (Fin n) F).det ^ ((n + 1) * w.1.mult) := by
  have h : ∀ x : F, ‖w.1.embedding x‖ = w.1 x := fun x => norm_embedding_eq _ _
  rw [equivF_det_embed, mult_isComplex, h, mul_comm (n + 1) 2]
  simp

open Classical in
/-- **The archimedean Tamagawa measures of equivalent forms**:
$(\mathrm{conj})_*\mu^{\mathrm{Tam}}_\infty(Q_0)=\prod_{w\mid\infty}w(\det P)^{(n+1)n_w}\cdot\mu^{\mathrm{Tam}}_\infty(Q_1)$. -/
theorem map_muArchTamSO_equivConjInf (hQ₀ : Q₀.Nondegenerate) (hQ₁ : Q₁.Nondegenerate) :
    (muArchTamSO Q₀ hQ₀).map (equivConjInf P hP) =
      ENNReal.ofReal (∏ w : InfinitePlace F, w (P : Matrix (Fin n) (Fin n) F).det ^ ((n + 1) * w.mult)) •
        muArchTamSO Q₁ hQ₁ := by
  have hf : ⇑(equivConjInf P hP) = Prod.map
      (fun (g : ∀ w, ArchSO (QRe Q₀ w)) w =>
        conjSO (Q := QRe Q₀ w) (Q' := QRe Q₁ w) (Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) P) 1
          (hessian_QRe_equivF P hP w) one_ne_zero (g w))
      (fun (g : ∀ w, ArchSOC (QCx Q₀ w)) w =>
        conjSOC (Q := QCx Q₀ w) (Q' := QCx Q₁ w) (Matrix.GeneralLinearGroup.map w.1.embedding P) 1
          (hessian_QCx_equivF P hP w) one_ne_zero (g w)) :=
    funext fun g => Prod.ext (funext fun w => equivConjInf_fst P hP g w) (funext fun w => equivConjInf_snd P hP g w)
  have hmeas : Measurable (equivConjInf (Q₀ := Q₀) P hP) := (equivConjInf (Q₀ := Q₀) P hP).continuous.measurable
  unfold muArchTamSO muArchNF muArchLeray
  rw [Measure.map_smul]
  swap
  · exact hmeas.aemeasurable
  rw [hf]
  have m1 : ∀ w : {w : InfinitePlace F // w.IsReal},
      Measurable (conjSO (Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) P) 1
          (hessian_QRe_equivF P hP w) one_ne_zero) :=
    fun w => (conjSO _ _ (hessian_QRe_equivF (Q₀ := Q₀) P hP w) one_ne_zero).continuous.measurable
  have m2 : ∀ w : {w : InfinitePlace F // w.IsComplex},
      Measurable (conjSOC (Matrix.GeneralLinearGroup.map w.1.embedding P) 1
          (hessian_QCx_equivF P hP w) one_ne_zero) :=
    fun w => (conjSOC _ _ (hessian_QCx_equivF (Q₀ := Q₀) P hP w) one_ne_zero).continuous.measurable
  have M1 : Measurable (fun (g : ∀ w, ArchSO (QRe Q₀ w)) w =>
        conjSO (Q := QRe Q₀ w) (Q' := QRe Q₁ w) (Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) P) 1
          (hessian_QRe_equivF P hP w) one_ne_zero (g w)) :=
    measurable_pi_iff.2 fun w => (m1 w).comp (measurable_pi_apply w)
  have M2 : Measurable (fun (g : ∀ w, ArchSOC (QCx Q₀ w)) w =>
        conjSOC (Q := QCx Q₀ w) (Q' := QCx Q₁ w) (Matrix.GeneralLinearGroup.map w.1.embedding P) 1
          (hessian_QCx_equivF P hP w) one_ne_zero (g w)) :=
    measurable_pi_iff.2 fun w => (m2 w).comp (measurable_pi_apply w)
  rw [← Measure.map_prod_map _ _ M1 M2]
  have S1 : ∀ w : {w : InfinitePlace F // w.IsReal}, SigmaFinite ((lerayMeasure (QRe Q₀ w)
      (gramDetR_QRe_ne_zero Q₀ hQ₀ w)).map
      (conjSO (Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) P) 1
          (hessian_QRe_equivF P hP w) one_ne_zero)) := fun w =>
    (conjSO _ _ (hessian_QRe_equivF (Q₀ := Q₀) P hP w) one_ne_zero).toHomeomorph.measurableEmbedding.sigmaFinite_map
  have S2 : ∀ w : {w : InfinitePlace F // w.IsComplex}, SigmaFinite ((lerayMeasureC (QCx Q₀ w)
      (gramDetC_QCx_ne_zero Q₀ hQ₀ w)).map
      (conjSOC (Matrix.GeneralLinearGroup.map w.1.embedding P) 1
          (hessian_QCx_equivF P hP w) one_ne_zero)) := fun w =>
    (conjSOC _ _ (hessian_QCx_equivF (Q₀ := Q₀) P hP w) one_ne_zero).toHomeomorph.measurableEmbedding.sigmaFinite_map
  rw [Measure.pi_map_pi (fun w => (m1 w).aemeasurable), Measure.pi_map_pi (fun w => (m2 w).aemeasurable)]
  have e1 := fun w : {w : InfinitePlace F // w.IsReal} =>
    map_lerayMeasure_conjSO' (Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) P) 1
      (hessian_QRe_equivF P hP w) one_ne_zero
      (gramDetR_QRe_ne_zero Q₀ hQ₀ w) (gramDetR_QRe_ne_zero _ hQ₁ w)
  have e2 := fun w : {w : InfinitePlace F // w.IsComplex} =>
    map_lerayMeasureC_conjSOC' (Matrix.GeneralLinearGroup.map w.1.embedding P) 1
      (hessian_QCx_equivF P hP w) one_ne_zero
      (gramDetC_QCx_ne_zero Q₀ hQ₀ w) (gramDetC_QCx_ne_zero _ hQ₁ w)
  simp only [equivF_factor_real P, equivF_factor_complex P] at e1 e2
  rw [congrArg Measure.pi (funext e1), congrArg Measure.pi (funext e2)]
  rw [sim_pi_smul (fun w : {w : InfinitePlace F // w.IsReal} =>
      lerayMeasure (QRe Q₁ w) (gramDetR_QRe_ne_zero _ hQ₁ w))
      (fun w => w.1 (P : Matrix (Fin n) (Fin n) F).det ^ ((n + 1) * w.1.mult)) (fun _ => by positivity),
    sim_pi_smul (fun w : {w : InfinitePlace F // w.IsComplex} =>
      lerayMeasureC (QCx Q₁ w) (gramDetC_QCx_ne_zero _ hQ₁ w))
      (fun w => w.1 (P : Matrix (Fin n) (Fin n) F).det ^ ((n + 1) * w.1.mult)) (fun _ => by positivity),
    Measure.prod_smul_left, Measure.prod_smul_right]
  simp only [smul_smul]
  rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => by positivity),
    sim_prod_places (fun w => w (P : Matrix (Fin n) (Fin n) F).det ^ ((n + 1) * w.mult)), mul_comm]

end Main

section Char

variable {F : Type} [Field F] [NumberField F] {Q₀ Q₁ : QuadForm (𝓞 F) 2} (P : GL (Fin 2) F)
  (hP : (Q₁.map (algebraMap (𝓞 F) F)).hessian =
    (P : Matrix (Fin 2) (Fin 2) F)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian * (P : Matrix (Fin 2) (Fin 2) F))

include hP in
/-- **The isotropic vector of an equivalent form**: if $Q_0(e)=0$ then $Q_1(P^{-1}e)=Q_0(e)=0$. -/
theorem isIsoVec_equivF {e : Fin 2 → F} (he : IsIsoVec Q₀ e) :
    IsIsoVec Q₁ (((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ e) := by
  have hPe : (P : Matrix (Fin 2) (Fin 2) F) *ᵥ (((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ e) = e := by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  refine ⟨fun h0 => he.1 ?_, ?_⟩
  · rw [← hPe, h0, mulVec_zero]
  · rw [qF_eq_zero_iff_hessian, hP, ← mulVec_mulVec, ← mulVec_mulVec, hPe, dotProduct_mulVec, vecMul_transpose,
      hPe, (qF_eq_zero_iff_hessian Q₀ e).mp he.2]

/-- **The characters at infinity of equivalent forms correspond**:
$\chi_{P^{-1}e}(P^{-1}gP)=\chi_e(g)$. -/
theorem isoCharInf_equivConjInf (hQ₀ : Q₀.Nondegenerate) (hQ₁ : Q₁.Nondegenerate) {e : Fin 2 → F}
    (he : IsIsoVec Q₀ e) (g : GInfSO Q₀) :
    isoCharInf hQ₁ (isIsoVec_equivF P hP he) (equivConjInf P hP g) = isoCharInf hQ₀ he g := by
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · change eigVal _ _ ((ArchSO.incl _ ((equivConjInf P hP g).1 w) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      eigVal _ e ((ArchSO.incl _ (g.1 w) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
    rw [equivConjInf_fst]
    exact eigVal_conj _ _ he.1 (isoCharR_spec hQ₀ he w (g.1 w))
  · change eigVal _ _ (ArchSOC.mat _ ((equivConjInf P hP g).2 w)) = eigVal _ e (ArchSOC.mat _ (g.2 w))
    rw [equivConjInf_snd, conjSOC_mat]
    exact eigVal_conj _ _ he.1 (isoCharC_spec hQ₀ he w (g.2 w))

end Char

end QuadFormsKB.Tamagawa.Measure.Weil
