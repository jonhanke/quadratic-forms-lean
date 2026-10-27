import QuadFormsKB.Tamagawa.Measure.Weil.SimilarLocal
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarArchReal
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarArchComplex
import QuadFormsKB.Tamagawa.Measure.Weil.MuTamSO

/-!
# Similar forms: the archimedean group and measure

**Layer:** a number field $F$, $Q_0$ a nondegenerate form over $\mathcal O_F$, $G\in M_n(\mathcal O_F)$ with
$\det G \ne 0$, $c \in \mathcal O_F\setminus 0$, and $Q_1 = c\,(Q_0\circ G)$ (`simForm`).

**Defines**
* `simConjInf hc hG : GInfSO Q₀ ≃ₜ* GInfSO (simForm Q₀ c G)`: the product over all archimedean places of the
  conjugations $g\mapsto G_w^{-1}gG_w$ (`LerayReal.conjSO`, `LerayComplex.conjSOC`), $G_w = \sigma_w(G)$.

**Proves**
* `hessian_QRe_simForm`, `hessian_QCx_simForm`: the Hessian relation $H_1^{w} = \sigma_w(c)\,G_w^{\mathsf T}H_0^{w}G_w$;
* **`map_muArchTamSO_simConjInf`**:
  $(\mathrm{conj})_*\mu^{\mathrm{Tam}}_\infty(Q_0) = \prod_{w\mid\infty}|\delta|_w^{\,n_w}\cdot\mu^{\mathrm{Tam}}_\infty(Q_1)$,
  $\delta = c^{n(n+1)/2}\det(G)^{n+1}$ (`simJac`), $n_w\in\{1,2\}$ the multiplicity of $w$.

Source: Weil 1982, §2.2.1, §2.3.
-/

open MeasureTheory Measure Matrix
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace QuadFormsKB.Tamagawa.Measure.LerayArch
  QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex
  QuadFormsKB.Tamagawa.ArchSOMeasure

/-! ### Generic measure lemmas -/

theorem sim_pi_smul {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) :
    Measure.pi (fun i => ENNReal.ofReal (r i) • μ i) =
      ENNReal.ofReal (∏ i, r i) • Measure.pi μ := by
  have : ∀ i, SigmaFinite (ENNReal.ofReal (r i) • μ i) := fun i => by
    have : ENNReal.ofReal (r i) • μ i = (r i).toNNReal • μ i := by
      ext s hs; simp [ENNReal.ofReal]
    rw [this]; infer_instance
  refine (Measure.pi_eq fun s hs => ?_)
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, Finset.prod_mul_distrib]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hr i)]

/-- Product of continuous multiplicative equivalences over an index type. -/
def simPiCongr {ι : Type*} {A B : ι → Type*} [∀ i, Mul (A i)] [∀ i, Mul (B i)]
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)] (e : ∀ i, A i ≃ₜ* B i) :
    (∀ i, A i) ≃ₜ* (∀ i, B i) :=
  ContinuousMulEquiv.mk' (Homeomorph.piCongrRight fun i => (e i).toHomeomorph) (fun x y => by
    funext i; exact map_mul (e i) (x i) (y i))

/-- Binary product of continuous multiplicative equivalences. -/
def simProdCongr {A B C D : Type*} [Mul A] [Mul B] [Mul C] [Mul D]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
    (e : A ≃ₜ* B) (f : C ≃ₜ* D) : (A × C) ≃ₜ* (B × D) :=
  ContinuousMulEquiv.mk' (e.toHomeomorph.prodCongr f.toHomeomorph) (fun x y => by
    ext
    · exact map_mul e x.1 y.1
    · exact map_mul f x.2 y.2)

section Main

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {Q₀ : QuadForm (𝓞 F) n} {c : 𝓞 F}
  {G : Matrix (Fin n) (Fin n) (𝓞 F)}

theorem sim_hessian_map_gen {S : Type*} [CommRing S] (σ : F →+* S) (hG : G.det ≠ 0) :
    (((simForm Q₀ c G).map (algebraMap (𝓞 F) F)).map σ).hessian = σ (c : F) •
      (((Matrix.GeneralLinearGroup.map σ (LatChange.glF G hG) : GL (Fin n) S) : Matrix (Fin n) (Fin n) S)ᵀ *
        (((Q₀.map (algebraMap (𝓞 F) F)).map σ).hessian) *
        ((Matrix.GeneralLinearGroup.map σ (LatChange.glF G hG) : GL (Fin n) S) : Matrix (Fin n) (Fin n) S)) := by
  rw [Siegel.hessian_map_NF σ, hessian_simForm hG, Siegel.hessian_map_NF σ]
  show _ = σ (c : F) • (((((LatChange.glF G hG : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)).map σ)ᵀ * _ *
    (((LatChange.glF G hG : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)).map σ)
  rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem hessian_QRe_simForm (hG : G.det ≠ 0) (w : {w : InfinitePlace F // w.IsReal}) :
    (QRe (simForm Q₀ c G) w).hessian = (embedding_of_isReal w.2 (c : F)) •
      (((Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) (LatChange.glF G hG) : GL (Fin n) ℝ) :
          Matrix (Fin n) (Fin n) ℝ)ᵀ * (QRe Q₀ w).hessian *
        ((Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) (LatChange.glF G hG) : GL (Fin n) ℝ) :
          Matrix (Fin n) (Fin n) ℝ)) :=
  sim_hessian_map_gen _ hG

theorem hessian_QCx_simForm (hG : G.det ≠ 0) (w : {w : InfinitePlace F // w.IsComplex}) :
    (QCx (simForm Q₀ c G) w).hessian = (w.1.embedding (c : F)) •
      (((Matrix.GeneralLinearGroup.map w.1.embedding (LatChange.glF G hG) : GL (Fin n) ℂ) :
          Matrix (Fin n) (Fin n) ℂ)ᵀ * (QCx Q₀ w).hessian *
        ((Matrix.GeneralLinearGroup.map w.1.embedding (LatChange.glF G hG) : GL (Fin n) ℂ) :
          Matrix (Fin n) (Fin n) ℂ)) :=
  sim_hessian_map_gen _ hG

theorem sim_embed_ne_zero {S : Type*} [Field S] (σ : F →+* S) (hc : c ≠ 0) : σ (c : F) ≠ 0 :=
  (map_ne_zero σ).2 (coe_ne_zero_of_ne_zero hc)

/-- **The conjugation isomorphism $G_\infty(Q_0) \cong G_\infty(Q_1)$**, $Q_1 = c\,(Q_0\circ G)$, the product of
`LerayReal.conjSO` and `LerayComplex.conjSOC` over the archimedean places ($G_w = \sigma_w(G)$, $c_w = \sigma_w(c)$). -/
def simConjInf (hc : c ≠ 0) (hG : G.det ≠ 0) : GInfSO Q₀ ≃ₜ* GInfSO (simForm Q₀ c G) :=
  simProdCongr
    (simPiCongr fun w : {w : InfinitePlace F // w.IsReal} =>
      conjSO (Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) (LatChange.glF G hG))
        (embedding_of_isReal w.2 (c : F)) (hessian_QRe_simForm hG w) (sim_embed_ne_zero _ hc))
    (simPiCongr fun w : {w : InfinitePlace F // w.IsComplex} =>
      conjSOC (Matrix.GeneralLinearGroup.map w.1.embedding (LatChange.glF G hG))
        (w.1.embedding (c : F)) (hessian_QCx_simForm hG w) (sim_embed_ne_zero _ hc))

theorem simConjInf_fst (hc : c ≠ 0) (hG : G.det ≠ 0) (g : GInfSO Q₀) (w : {w : InfinitePlace F // w.IsReal}) :
    (simConjInf hc hG g).1 w =
      conjSO (Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) (LatChange.glF G hG))
        (embedding_of_isReal w.2 (c : F)) (hessian_QRe_simForm hG w) (sim_embed_ne_zero _ hc) (g.1 w) := rfl

theorem simConjInf_snd (hc : c ≠ 0) (hG : G.det ≠ 0) (g : GInfSO Q₀) (w : {w : InfinitePlace F // w.IsComplex}) :
    (simConjInf hc hG g).2 w =
      conjSOC (Matrix.GeneralLinearGroup.map w.1.embedding (LatChange.glF G hG))
        (w.1.embedding (c : F)) (hessian_QCx_simForm hG w) (sim_embed_ne_zero _ hc) (g.2 w) := rfl

theorem sim_det_embed {S : Type*} [Field S] (σ : F →+* S) (hG : G.det ≠ 0) :
    ((Matrix.GeneralLinearGroup.map σ (LatChange.glF G hG) : GL (Fin n) S) : Matrix (Fin n) (Fin n) S).det =
      σ (algebraMap (𝓞 F) F G.det) := by
  show (((G.map (algebraMap (𝓞 F) F)).map σ)).det = _
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

theorem sim_factor_real (hG : G.det ≠ 0) (w : {w : InfinitePlace F // w.IsReal}) :
    |embedding_of_isReal w.2 (c : F)| ^ (n * (n + 1) / 2) *
        |((Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) (LatChange.glF G hG) : GL (Fin n) ℝ) :
          Matrix (Fin n) (Fin n) ℝ).det| ^ (n + 1) =
      w.1 (algebraMap (𝓞 F) F (simJac c G)) ^ (w.1.mult) := by
  have h : ∀ x : F, |embedding_of_isReal w.2 x| = w.1 x := fun x => by
    rw [← Real.norm_eq_abs, norm_embedding_of_isReal]
  rw [sim_det_embed, mult_isReal, pow_one]
  simp only [simJac, map_mul, map_pow, h]

theorem sim_factor_complex (hG : G.det ≠ 0) (w : {w : InfinitePlace F // w.IsComplex}) :
    ‖w.1.embedding (c : F)‖ ^ (2 * (n * (n + 1) / 2)) *
        ‖((Matrix.GeneralLinearGroup.map w.1.embedding (LatChange.glF G hG) : GL (Fin n) ℂ) :
          Matrix (Fin n) (Fin n) ℂ).det‖ ^ (2 * (n + 1)) =
      w.1 (algebraMap (𝓞 F) F (simJac c G)) ^ (w.1.mult) := by
  have h : ∀ x : F, ‖w.1.embedding x‖ = w.1 x := fun x => norm_embedding_eq _ _
  rw [sim_det_embed, mult_isComplex]
  simp only [simJac, map_mul, map_pow, h]
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 (n * (n + 1) / 2), mul_comm 2 (n + 1)]

open Classical in
theorem sim_prod_places (f : InfinitePlace F → ℝ) :
    (∏ w : {w : InfinitePlace F // w.IsReal}, f w.1) * (∏ w : {w : InfinitePlace F // w.IsComplex}, f w.1) =
      ∏ w : InfinitePlace F, f w := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace F => w.IsReal) f]
  congr 1
  exact Fintype.prod_equiv (Equiv.subtypeEquivRight fun w => not_isReal_iff_isComplex).symm _ _ (fun _ => rfl)

open Classical in
theorem map_muArchTamSO_simConjInf (hQ : Q₀.Nondegenerate) (hc : c ≠ 0) (hG : G.det ≠ 0) :
    (muArchTamSO Q₀ hQ).map (simConjInf hc hG) =
      ENNReal.ofReal (∏ w : InfinitePlace F, w (algebraMap (𝓞 F) F (simJac c G)) ^ w.mult) •
        muArchTamSO (simForm Q₀ c G) (nondegenerate_simForm hQ hc hG) := by
  have hf : ⇑(simConjInf hc hG) = Prod.map
      (fun (g : ∀ w, ArchSO (QRe Q₀ w)) w =>
        conjSO (Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) (LatChange.glF G hG))
          (embedding_of_isReal w.2 (c : F)) (hessian_QRe_simForm hG w) (sim_embed_ne_zero _ hc) (g w))
      (fun (g : ∀ w, ArchSOC (QCx Q₀ w)) w =>
        conjSOC (Matrix.GeneralLinearGroup.map w.1.embedding (LatChange.glF G hG))
          (w.1.embedding (c : F)) (hessian_QCx_simForm hG w) (sim_embed_ne_zero _ hc) (g w)) := rfl
  have hmeas : Measurable (simConjInf (Q₀ := Q₀) hc hG) := (simConjInf (Q₀ := Q₀) hc hG).continuous.measurable
  unfold muArchTamSO muArchNF muArchLeray
  rw [Measure.map_smul]
  swap
  · exact hmeas.aemeasurable
  rw [hf]
  have m1 : ∀ w : {w : InfinitePlace F // w.IsReal},
      Measurable (conjSO (Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) (LatChange.glF G hG))
        (embedding_of_isReal w.2 (c : F)) (hessian_QRe_simForm hG w) (sim_embed_ne_zero _ hc)) :=
    fun w => (conjSO _ _ (hessian_QRe_simForm (Q₀ := Q₀) hG w) (sim_embed_ne_zero _ hc)).continuous.measurable
  have m2 : ∀ w : {w : InfinitePlace F // w.IsComplex},
      Measurable (conjSOC (Matrix.GeneralLinearGroup.map w.1.embedding (LatChange.glF G hG))
        (w.1.embedding (c : F)) (hessian_QCx_simForm hG w) (sim_embed_ne_zero _ hc)) :=
    fun w => (conjSOC _ _ (hessian_QCx_simForm (Q₀ := Q₀) hG w) (sim_embed_ne_zero _ hc)).continuous.measurable
  have M1 : Measurable (fun (g : ∀ w, ArchSO (QRe Q₀ w)) w =>
        conjSO (Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) (LatChange.glF G hG))
          (embedding_of_isReal w.2 (c : F)) (hessian_QRe_simForm hG w) (sim_embed_ne_zero _ hc) (g w)) :=
    measurable_pi_iff.2 fun w => (m1 w).comp (measurable_pi_apply w)
  have M2 : Measurable (fun (g : ∀ w, ArchSOC (QCx Q₀ w)) w =>
        conjSOC (Matrix.GeneralLinearGroup.map w.1.embedding (LatChange.glF G hG))
          (w.1.embedding (c : F)) (hessian_QCx_simForm hG w) (sim_embed_ne_zero _ hc) (g w)) :=
    measurable_pi_iff.2 fun w => (m2 w).comp (measurable_pi_apply w)
  rw [← Measure.map_prod_map _ _ M1 M2]
  have S1 : ∀ w : {w : InfinitePlace F // w.IsReal}, SigmaFinite ((lerayMeasure (QRe Q₀ w)
      (gramDetR_QRe_ne_zero Q₀ hQ w)).map
      (conjSO (Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) (LatChange.glF G hG))
        (embedding_of_isReal w.2 (c : F)) (hessian_QRe_simForm hG w) (sim_embed_ne_zero _ hc))) := fun w =>
    (conjSO _ _ (hessian_QRe_simForm (Q₀ := Q₀) hG w)
      (sim_embed_ne_zero _ hc)).toHomeomorph.measurableEmbedding.sigmaFinite_map
  have S2 : ∀ w : {w : InfinitePlace F // w.IsComplex}, SigmaFinite ((lerayMeasureC (QCx Q₀ w)
      (gramDetC_QCx_ne_zero Q₀ hQ w)).map
      (conjSOC (Matrix.GeneralLinearGroup.map w.1.embedding (LatChange.glF G hG))
        (w.1.embedding (c : F)) (hessian_QCx_simForm hG w) (sim_embed_ne_zero _ hc))) := fun w =>
    (conjSOC _ _ (hessian_QCx_simForm (Q₀ := Q₀) hG w)
      (sim_embed_ne_zero _ hc)).toHomeomorph.measurableEmbedding.sigmaFinite_map
  rw [Measure.pi_map_pi (fun w => (m1 w).aemeasurable), Measure.pi_map_pi (fun w => (m2 w).aemeasurable)]
  have hQ' := nondegenerate_simForm hQ hc hG
  have e1 := fun w : {w : InfinitePlace F // w.IsReal} =>
    map_lerayMeasure_conjSO' (Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) (LatChange.glF G hG))
      (embedding_of_isReal w.2 (c : F)) (hessian_QRe_simForm hG w) (sim_embed_ne_zero _ hc)
      (gramDetR_QRe_ne_zero Q₀ hQ w) (gramDetR_QRe_ne_zero _ hQ' w)
  have e2 := fun w : {w : InfinitePlace F // w.IsComplex} =>
    map_lerayMeasureC_conjSOC' (Matrix.GeneralLinearGroup.map w.1.embedding (LatChange.glF G hG))
      (w.1.embedding (c : F)) (hessian_QCx_simForm hG w) (sim_embed_ne_zero _ hc)
      (gramDetC_QCx_ne_zero Q₀ hQ w) (gramDetC_QCx_ne_zero _ hQ' w)
  simp only [sim_factor_real hG, sim_factor_complex hG] at e1 e2
  rw [congrArg Measure.pi (funext e1), congrArg Measure.pi (funext e2)]
  rw [sim_pi_smul (fun w : {w : InfinitePlace F // w.IsReal} =>
      lerayMeasure (QRe (simForm Q₀ c G) w) (gramDetR_QRe_ne_zero _ hQ' w))
      (fun w => w.1 (algebraMap (𝓞 F) F (simJac c G)) ^ w.1.mult) (fun _ => by positivity),
    sim_pi_smul (fun w : {w : InfinitePlace F // w.IsComplex} =>
      lerayMeasureC (QCx (simForm Q₀ c G) w) (gramDetC_QCx_ne_zero _ hQ' w))
      (fun w => w.1 (algebraMap (𝓞 F) F (simJac c G)) ^ w.1.mult) (fun _ => by positivity),
    Measure.prod_smul_left, Measure.prod_smul_right]
  simp only [smul_smul]
  rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => by positivity),
    sim_prod_places (fun w => w (algebraMap (𝓞 F) F (simJac c G)) ^ w.mult), mul_comm]

end Main

end QuadFormsKB.Tamagawa.Measure.Weil
