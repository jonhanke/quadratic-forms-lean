/-
# The archimedean density is the archimedean Whittaker integral, at every real place of a totally real field
**Layer:** global over a totally real number field $F$; archimedean bookkeeping (translation between the real-embedding
coordinates of `ArchWhittakerR.lean` and the algebraic data $Q_0$, $T_0$ over $\mathcal O_F$).

**Setting.** $F$ totally real, $Q_0 = \sum_{i<2m}b_ix_i^2$ and $T_0$ (in $r$ variables) totally positive definite over $\mathcal O_F$,
$\sigma : F \to \mathbb C$ an embedding with real embedding $\rho_\sigma$ (`Tamagawa.Measure.realEmb`). All indices are 0-based.
`tSigma T₀ σ` is the vector of upper coordinates $(\rho_\sigma(T_{0,G})_{ij})_{0\le i\le j<r}$ of the Gram matrix $T_{0,G} = \tfrac12H_{T_0}$.

**Definitions.** `tSigma`.

**Results.**
* `symU_tSigma`, `PDU_tSigma`, `det_symU_tSigma`: `tSigma` is the Gram matrix of $\sigma(T_0)$, it is positive definite, and its
  determinant is `Tamagawa.detGram T₀ σ`;
* `s_pos`, `prod_s`: $\rho_\sigma(b_i) > 0$ and $\prod_i\rho_\sigma(b_i) = $ `Tamagawa.detGram (diag b) σ`;
* **`archDensityForm_eq_archWhittaker`**: for $m > r$ and every $Z \in \mathbb H_r$,
  $$\beta_\sigma(Q_0, T_0) = e^{-2\pi i\operatorname{tr}(\sigma(T_0)Z)}\int_{\mathrm{Sym}_r(\mathbb R)}G_{\sigma(S)}(Z + B)\,e^{-2\pi i\operatorname{tr}(\sigma(T_0)B)}\,dB;$$
* **`thetaGenR_coeff_eq_whittaker_all_places`**: the headline $a(T_0) = \prod_\sigma W_{T_0,\sigma}\cdot\prod_{v<\infty}W_{T_0,v}$ up to the
  archimedean Weil constants $(\gamma_{V,\infty}c_{B,\infty})^r$, with every archimedean factor the Whittaker integral
  $W_{T_0,\sigma}(g_Z)$ (times the character $e^{-2\pi i\operatorname{tr}(\sigma(T_0)Z)}$) instead of Siegel's density, for every family of points
  $Z_\sigma \in \mathbb H_r$.

**Range.** $m > r$ (i.e. $N = 2m > 2r$), Siegel's sharp range, inherited from `ArchR.archWhittakerR_eq` (Hua's integral,
`ArchHua.lean`).

Sources: Weil, *Sur la formule de Siegel dans la théorie des groupes classiques*, Acta Math. 113 (1965) [unverified]; Siegel, *Über die
analytische Theorie der quadratischen Formen*, Ann. of Math. 36 (1935) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.ThetaR
import QuadFormsKB.SiegelWeil.Forms.ArchWhittakerR
import QuadFormsKB.Tamagawa.Measure.AdelicSO
import QuadFormsKB.Citation

open Matrix NumberField Complex IsDedekindDomain
open QuadFormsKB.HilbertModular QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Frames
open QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchVol QuadFormsKB.WeilRep.Genus
open scoped Real

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {m r : ℕ}

/-- **Upper coordinates of $\sigma(T_0)$:** the entries $(\sigma(T_{0,G}))_{ij}$, $0 \le i \le j < r$, of the Gram matrix
$T_{0,G} = \tfrac12H_{T_0}$ of $T_0$ at the real embedding $\rho_\sigma$ (`realEmb`), as a point of $\mathbb R^{\mathrm{UIdx}\,r}$. -/
def tSigma (T₀ : QuadForm (𝓞 F) r) (σ : F →ₐ[ℚ] ℂ) : UIdx r → ℝ :=
  fun p => realEmb σ (gramT (T₀.map (algebraMap (𝓞 F) F)) p.1.1 p.1.2)

/-- **The symmetric matrix of `tSigma`** is the Gram matrix of $T_0$ at $\rho_\sigma$ (the Gram matrix is symmetric,
`gramT_transpose`). -/
lemma symU_tSigma (T₀ : QuadForm (𝓞 F) r) (σ : F →ₐ[ℚ] ℂ) :
    symU (tSigma T₀ σ) = (gramT (T₀.map (algebraMap (𝓞 F) F))).map (realEmb σ) := by
  ext i j
  simp only [symU, tSigma, Matrix.of_apply, Matrix.map_apply]
  split_ifs with h
  · rfl
  · have := congrFun (congrFun (gramT_transpose (T₀.map (algebraMap (𝓞 F) F))) i) j
    simp only [Matrix.transpose_apply] at this
    rw [this]

/-- **Real form via its Gram matrix:** $R(y) = y^{\mathsf T}(\tfrac12H_R)y$ (the real case of `eval_eq_gramT`). -/
lemma eval_real_eq (R : QuadForm ℝ r) (y : Fin r → ℝ) :
    R.eval y = y ⬝ᵥ ((1 / 2 : ℝ) • R.hessian) *ᵥ y := by
  rw [QuadForm.eval, QuadForm.evalIn_eq_dotProduct, QuadForm.hessian, smul_mulVec, dotProduct_smul,
    add_mulVec, dotProduct_add]
  have hm : R.coeff.map (algebraMap ℝ ℝ) = R.coeff := by ext; simp
  rw [hm]
  have : y ⬝ᵥ R.coeffᵀ *ᵥ y = y ⬝ᵥ R.coeff *ᵥ y := by
    rw [mulVec_transpose, dotProduct_comm, dotProduct_mulVec]
  rw [this, smul_eq_mul]
  ring

/-- **The Gram matrix of the real form $T_{0,\sigma}$** (`T₀.map (realEmb σ ∘ algebraMap)`) is the image of the Gram matrix of $T_0$
under $\rho_\sigma$. -/
lemma gram_real (T₀ : QuadForm (𝓞 F) r) (σ : F →ₐ[ℚ] ℂ) :
    (1 / 2 : ℝ) • (T₀.map ((realEmb σ).comp (algebraMap (𝓞 F) F))).hessian =
      (gramT (T₀.map (algebraMap (𝓞 F) F))).map (realEmb σ) := by
  have h1 : T₀.map ((realEmb σ).comp (algebraMap (𝓞 F) F)) =
      (T₀.map (algebraMap (𝓞 F) F)).map (realEmb σ) := by
    simp [QuadForm.map, Matrix.map_map]
  rw [h1, QuadFormsKB.Siegel.hessian_map_NF, gramT]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_div₀, map_one, map_ofNat]

/-- **Positivity of `tSigma`:** for $T_0$ totally positive definite, $\sigma(T_0)$ is a positive definite real symmetric matrix
(`PDU`), from `isPosDefR_map` and the Gram matrix of the real form. -/
lemma PDU_tSigma (T₀ : QuadForm (𝓞 F) r) (hT₀ : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F)))
    (σ : F →ₐ[ℚ] ℂ) : PDU (tSigma T₀ σ) := by
  intro x hx
  have h := isPosDefR_map T₀ (realEmb σ)
    (QuadFormsKB.Tamagawa.nondegenerate_of_map hT₀.nondegenerate) hT₀ x hx
  rw [eval_real_eq, gram_real] at h
  rw [symU_tSigma]
  exact h

/-- **Determinant of `tSigma`:** $\det\sigma(T_{0,G}) = \lvert\sigma(\det H_{T_0}/2^r)\rvert$ (`Tamagawa.detGram`); the real number
$\rho_\sigma(\det H_{T_0}/2^r)$ is positive, being the determinant of a positive definite matrix. -/
lemma det_symU_tSigma (T₀ : QuadForm (𝓞 F) r) (hT₀ : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F)))
    (σ : F →ₐ[ℚ] ℂ) : (symU (tSigma T₀ σ)).det = Tamagawa.detGram T₀ σ := by
  have hpos := (ArchR.densRect_of_piv r r (tSigma T₀ σ) le_rfl
    (piv_of_PDU r _ (PDU_tSigma T₀ hT₀ σ))).1
  have hd : (symU (tSigma T₀ σ)).det = realEmb σ (algebraMap (𝓞 F) F T₀.hessian.det / 2 ^ r) := by
    have e1 := RingHom.map_det (realEmb σ) (gramT (T₀.map (algebraMap (𝓞 F) F)))
    have e2 := RingHom.map_det (algebraMap (𝓞 F) F) T₀.hessian
    simp only [RingHom.mapMatrix_apply] at e1 e2
    rw [symU_tSigma, ← e1, gramT, Matrix.det_smul, QuadFormsKB.Siegel.hessian_map_NF, ← e2,
      Fintype.card_fin]
    congr 1
    rw [one_div, inv_pow]; ring
  rw [hd] at hpos ⊢
  unfold Tamagawa.detGram
  rw [← realEmb_apply, Complex.norm_real, Real.norm_of_nonneg hpos.le]

/-- **Positivity of the diagonal coefficients:** for $Q_0 = \sum_ib_ix_i^2$ totally positive definite, $\rho_\sigma(b_i) > 0$
(evaluate at the basis vector $e_i$). -/
lemma s_pos (b : Fin (2 * m) → 𝓞 F) (hpd : IsTotallyPosDef ((QuadForm.diag b).map (algebraMap (𝓞 F) F)))
    (σ : F →ₐ[ℚ] ℂ) (i : Fin (2 * m)) : 0 < realEmb σ (algebraMap (𝓞 F) F (b i)) := by
  have h := hpd (Pi.single i 1) (by simp) σ
  have e : ((QuadForm.diag b).map (algebraMap (𝓞 F) F)).eval (Pi.single i 1) = algebraMap (𝓞 F) F (b i) := by
    simp [QuadForm.eval, QuadForm.evalIn, QuadForm.map, QuadForm.diag, Matrix.diagonal_apply, Pi.single_apply]
    rw [Finset.sum_eq_single i (fun x _ hx => by simp [hx]) (by simp)]
    rw [Finset.sum_eq_single i (fun x _ hx => by simp [hx]) (by simp)]
    simp
  rw [e, ← realEmb_apply] at h
  exact_mod_cast h

/-- **The determinant of the diagonal form:** $\prod_i\rho_\sigma(b_i) = \mathrm{detGram}(Q_0,\sigma) =
\lvert\sigma(\det H_{Q_0}/2^n)\rvert$, as $H_{Q_0} = \operatorname{diag}(2b_i)$. -/
lemma prod_s (b : Fin (2 * m) → 𝓞 F) (hpd : IsTotallyPosDef ((QuadForm.diag b).map (algebraMap (𝓞 F) F)))
    (σ : F →ₐ[ℚ] ℂ) :
    ∏ i, realEmb σ (algebraMap (𝓞 F) F (b i)) = Tamagawa.detGram (QuadForm.diag b) σ := by
  have hH : (QuadForm.diag b).hessian = Matrix.diagonal fun i => 2 * b i := by
    ext i j
    simp [QuadForm.hessian, QuadForm.diag, Matrix.diagonal_apply, eq_comm]
    by_cases h : i = j <;> simp [h, mul_comm, map_ofNat]; ring
  have hpos : 0 < ∏ i, realEmb σ (algebraMap (𝓞 F) F (b i)) := Finset.prod_pos fun i _ => s_pos b hpd σ i
  have hd : ∏ i, realEmb σ (algebraMap (𝓞 F) F (b i)) =
      realEmb σ (algebraMap (𝓞 F) F (QuadForm.diag b).hessian.det / 2 ^ (2 * m)) := by
    rw [hH, Matrix.det_diagonal, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    simp only [map_mul, map_prod, map_pow, map_ofNat]
    rw [mul_div_cancel_left₀ _ (pow_ne_zero _ two_ne_zero), map_prod]
  unfold Tamagawa.detGram
  rw [← realEmb_apply, Complex.norm_real, ← hd, Real.norm_of_nonneg hpos.le]

open QuadFormsKB.Analysis QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData QuadFormsKB.Tamagawa

/-- **Siegel's archimedean density is the archimedean Whittaker integral** (degree $r$, one real place, any $Z_\sigma \in \mathbb H_r$):
for $Q_0 = \sum_{i<2m}b_ix_i^2$ and $T_0$ totally positive definite over $\mathcal O_F$ and $m > r$,
$$\beta_\sigma(Q_0, T_0) = e^{-2\pi i\operatorname{tr}(\sigma(T_0)Z_\sigma)}\int_{\mathrm{Sym}_r(\mathbb R)}G_{\sigma(S)}(Z_\sigma + B)\,
e^{-2\pi i\operatorname{tr}(\sigma(T_0)B)}\,dB,$$
$\beta_\sigma$ = `Tamagawa.Frames.archDensityForm` at $(\mathrm{detGram}(Q_0,\sigma), \mathrm{detGram}(T_0,\sigma))$, $S = \operatorname{diag}(\rho_\sigma(b_i))$.
*Proof:* `ArchR.archWhittakerR_eq` with $T = \sigma(T_0)$ positive definite (`PDU_tSigma`), `prod_s`, `det_symU_tSigma`, and
$e^{-x}e^{x} = 1$. -/
theorem archDensityForm_eq_archWhittaker (b : Fin (2 * m) → 𝓞 F)
    (hpd : IsTotallyPosDef ((QuadForm.diag b).map (algebraMap (𝓞 F) F)))
    (T₀ : QuadForm (𝓞 F) r) (hT₀ : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F)))
    (σ : F →ₐ[ℚ] ℂ) (hk : r < m) {Zσ : Matrix (Fin r) (Fin r) ℂ} (hZ : Zσ ∈ WeilRep.Genus.siegelH r) :
    (Tamagawa.Frames.archDensityForm (2 * m) r (Tamagawa.detGram (QuadForm.diag b) σ)
        (Tamagawa.detGram T₀ σ) : ℂ) =
      cexp (-2 * π * I * ArchR.trU (tSigma T₀ σ) Zσ) *
      ∫ B : UIdx r → ℝ, ArchR.gaussR (fun i => realEmb σ (algebraMap (𝓞 F) F (b i))) (Zσ + cR (symU B)) *
        cexp (-2 * π * I * ArchR.trU (tSigma T₀ σ) (cR (symU B))) := by
  rw [ArchR.archWhittakerR_eq hk (s_pos b hpd σ) hZ]
  simp only [PDU_tSigma T₀ hT₀ σ, ↓reduceIte]
  rw [prod_s b hpd σ, det_symU_tSigma T₀ hT₀ σ, ← mul_assoc, mul_comm (cexp _), mul_assoc, ← Complex.exp_add]
  simp

/-- **The Fourier coefficients of the genus average of the degree-$r$ theta series, every factor a Whittaker integral** (unconditional
for $m > r$). Under the hypotheses of `thetaGenR_hasSum_whittaker`, for every family $Z_\sigma \in \mathbb H_r$ ($\sigma : F \to \mathbb C$)
$$a(T_0) = \prod_\sigma\Big(e^{-2\pi i\operatorname{tr}(\sigma(T_0)Z_\sigma)}\int_{\mathrm{Sym}_r(\mathbb R)}G_{\sigma(S)}(Z_\sigma + B)\,
e^{-2\pi i\operatorname{tr}(\sigma(T_0)B)}dB\Big)\cdot(\gamma_{V,\infty}c_{B,\infty})^r\prod_{v<\infty}W_{T_0,v}(\mathbf 1_{L_v^r}),$$
$a(T_0) = \mathrm{repMassT}/\mathrm{Mass}$ the coefficient of $e_{T_0}$. *Proof:* `thetaGenR_hasSum_whittaker` with each
$\beta_\sigma$ replaced via `archDensityForm_eq_archWhittaker`. -/
@[kb "weil1965" "Ch. II–IV (Siegel–Weil identity of degree $r$, Fourier coefficients of full rank, all places) [unverified]"]
theorem thetaGenR_coeff_eq_whittaker_all_places (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hr : 1 ≤ r)
    (hrN : r + 3 ≤ 2 * m) (hk : r < m)
    (hpd : IsTotallyPosDef ((QuadForm.diag b).map (algebraMap (𝓞 F) F)))
    (T₀ : QuadForm (𝓞 F) r) (hT₀ : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F)))
    (Z' : (F →ₐ[ℚ] ℂ) → Matrix (Fin r) (Fin r) ℂ) (hZ' : ∀ σ, Z' σ ∈ WeilRep.Genus.siegelH r) :
    ((repMassT ((QuadForm.diag b).map (algebraMap (𝓞 F) F)) (Tamagawa.stdLat F (2 * m))
          (T₀.map (algebraMap (𝓞 F) F)) /
          mass ((QuadForm.diag b).map (algebraMap (𝓞 F) F)) (Tamagawa.stdLat F (2 * m)) : ℝ) : ℂ) =
        (∏ σ : F →ₐ[ℚ] ℂ, (cexp (-2 * π * I * ArchR.trU (tSigma T₀ σ) (Z' σ)) *
          ∫ B : UIdx r → ℝ, ArchR.gaussR (fun i => realEmb σ (algebraMap (𝓞 F) F (b i))) (Z' σ + cR (symU B)) *
            cexp (-2 * π * I * ArchR.trU (tSigma T₀ σ) (cR (symU B))))) *
          (((localDataInf (F := F)).gammaV (aInf (unitsOfInt b hb)) *
              (localDataInf (F := F)).cB (aInf (unitsOfInt b hb))) ^ r *
            ∏' v : HeightOneSpectrum (𝓞 F), whittakerR v (aOfInt v b hb)
              ((LocalDensity.NF.Qp v T₀).map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)))) := by
  obtain ⟨σ₀⟩ : Nonempty (F →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have hZ0 : (fun _ : InfinitePlace F => Z' σ₀) ∈ siegelHF F r := fun _ => hZ' σ₀
  rw [(thetaGenR_hasSum_whittaker b hb hr hrN hpd hZ0).2 T₀ hT₀, Complex.ofReal_prod]
  congr 1
  refine Finset.prod_congr rfl fun σ _ => ?_
  exact archDensityForm_eq_archWhittaker b hpd T₀ hT₀ σ hk (hZ' σ)

end QuadFormsKB.SiegelWeil.Forms
