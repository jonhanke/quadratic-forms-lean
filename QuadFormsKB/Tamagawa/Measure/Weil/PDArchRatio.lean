import QuadFormsKB.Tamagawa.Measure.Weil.PDArchTamagawa
import QuadFormsKB.Tamagawa.Measure.Weil.PDTamagawa

/-!
# $\tau(PD^\times)$ transported to $SO(D^0)$ for every division algebra over every number field

**Layer:** $F$ a number field, $a, b \in \mathcal O_F\setminus 0$, $D = (a,b)_F$ a division algebra of any signature,
$Q_0 = \langle -a,-b,ab\rangle$.

**Proves**
* `rF_toReal_eq_kInf` (the product formula, Weil's Thm 2.3.1): $r_f = K_\infty$, where $K_\infty$ is the
  archimedean Haar constant of `haarConst_eq`. Indeed $r_f = c_F\prod_v|8a^3b^3|_v = c_F\prod_w|8a^3b^3|_w^{-1}$
  (`finprod_norm_eq`) $= K_\infty$.
* `muPD_map_pdSplit`: Weil's measure `muPD` on $PD^\times(\mathbb A)$ is $K_\infty^{-1}(\nu_\infty\times\mu_{PD,f})$,
  with no hypotheses.
* **`covolume_muTam_pureForm`**: for a division algebra $D$ over a number field $F$,
  $$\operatorname{vol}\big(SO(V)(F)\backslash SO(V)(\mathbb A),\ \texttt{muTam}\big) = 2.$$
* **`tamagawaNumberTwoAdelic_pureForm`**: `TamagawaNumberTwoAdelic` for $\langle-a,-b,ab\rangle$ over every number
  field (every signature: definite and indefinite, complex places allowed), with no hypotheses;
  `tamagawaNumberTwoAdelic_pureForm_of_totallyReal` is its totally real case (name kept).
* `muTamWeil_eq_muTam`, `covolume_muTamWeil_pureForm`: the former separate measure `muTamWeil` is now `muTam`.

*The normalization at complex places.* Weil's gauge measure uses $|dz\wedge d\bar z| = 2\,dx\,dy$ per complex
coordinate, the self-dual measure for the trace pairing, the same normalization as $c_F = |d_F|^{-3/2}$ and as the
adelic measures `omegaQuatInf`, `omegaInf`. The complex Leray measure `LerayComplex.lerayMeasureC` uses the real
Lebesgue measures on $M_3(\mathbb C)$ and on the coefficient space; for $SO_3$ (a quotient of a 9-dimensional by a
6-dimensional measure) the two differ by $2^{9-6} = 8$ per complex place, and `muArchTamSO` includes this factor
(`cxWeil`). *Update (2026-10-22):* before that factor was added, `muTam` gave covolume $2/8^{r_2}$, so
`TamagawaNumberTwoAdelic` held only for totally real $F$, and Weil's normalization was a separate measure
`muTamWeil` $= 8^{r_2}\,\texttt{muTam}$.
-/

open MeasureTheory Set NumberField IsDedekindDomain NumberField.InfinitePlace Quaternion
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.QuatZeta QuadFormsKB.Siegel QuadFormsKB.Tamagawa.ArchSOMeasure

open scoped Classical

variable {F : Type} [Field F] [NumberField F] (a b : 𝓞 F)

local notation "Q₀" => pureFormO a b

/-! ### The product formula $r_f = 2^{3r_2}K_\infty$ -/

/-- The archimedean norm of $x \in F$ split over the places: $\|x\|_\infty = \prod_{w\ \mathrm{real}}|\sigma_w x|
\prod_{w\ \mathrm{complex}}\|\sigma_w x\|^2$ (every number field). -/
theorem norm_mixedEmbedding_eq_real_complex (x : F) :
    mixedEmbedding.norm (mixedEmbedding F x) =
      (∏ w : {w : InfinitePlace F // w.IsReal}, |sR w x|) * ∏ w : {w : InfinitePlace F // w.IsComplex}, ‖sC w x‖ ^ 2 := by
  rw [mixedEmbedding.norm_apply, prod_eq_prod_mul_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isReal, pow_one, mixedEmbedding.normAtPlace_apply, ← norm_embedding_of_isReal w.2, Real.norm_eq_abs]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isComplex, mixedEmbedding.normAtPlace_apply, ← norm_embedding_eq]

/-- **The product formula** over every number field: $\prod_v|x|_v = \|x\|_\infty^{-1}$ for $x \in F^\times$
(`WeilRep.prod_modulus_eq_one`). -/
theorem finprod_norm_eq_inv_real_complex (x : F) (hx : x ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (v.adicCompletion F) x‖ =
      ((∏ w : {w : InfinitePlace F // w.IsReal}, |sR w x|) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, ‖sC w x‖ ^ 2)⁻¹ := by
  have h := WeilRep.prod_modulus_eq_one (F := F) hx
  have hm : ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) x) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (v.adicCompletion F) x‖ :=
    finprod_congr fun v => WeilRep.modK_eq_norm v ((map_ne_zero _).mpr hx)
  rw [hm, norm_mixedEmbedding_eq_real_complex] at h
  exact eq_inv_of_mul_eq_one_right h

theorem cF_three_eq : ohatVol F ^ 3 = cF F 3 := by
  have hd : 0 < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero (K := F))
  rw [ohatVol, cF, Real.sqrt_eq_rpow, ← Real.rpow_neg hd.le, ← Real.rpow_natCast, ← Real.rpow_mul hd.le]
  norm_num

theorem kInf_pos (ha : a ≠ 0) (hb : b ≠ 0) : 0 < kInf F a b := by
  have ha' : (a : F) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : F) ≠ 0 := by exact_mod_cast hb
  have hcF : 0 < cF F 3 := by
    have hd : 0 < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero (K := F))
    exact Real.rpow_pos_of_pos hd _
  unfold kInf
  refine mul_pos (mul_pos hcF (Finset.prod_pos fun w _ => ?_)) (Finset.prod_pos fun w _ => ?_)
  · have h1 : sR w (a : F) ≠ 0 := (map_ne_zero _).mpr ha'
    have h2 : sR w (b : F) ≠ 0 := (map_ne_zero _).mpr hb'
    positivity
  · have h1 : sC w (a : F) ≠ 0 := (map_ne_zero _).mpr ha'
    have h2 : sC w (b : F) ≠ 0 := (map_ne_zero _).mpr hb'
    positivity

/-- **The product formula for $PD^\times \cong SO(D^0)$** (Weil, Thm 2.3.1), every number field and every quaternion
algebra: $r_f = K_\infty$. The finite ratio is $c_F\prod_v|8a^3b^3|_v$ (`rF_toReal_eq_finprod`), the product
over the finite places is $\big(\prod_\sigma\|\sigma(8a^3b^3)\|\big)^{-1}$ (`finprod_norm_eq`), and $K_\infty$ has the
archimedean factors $|8a^3b^3|_w^{-1}$. -/
@[kb "weil1982" "§2.3, Thm 2.3.1 (product formula for local ratios) [unverified]"]
theorem rF_toReal_eq_kInf (ha : a ≠ 0) (hb : b ≠ 0) :
    (rF a b).toReal = kInf F a b := by
  have ha' : (a : F) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : F) ≠ 0 := by exact_mod_cast hb
  have hc : (cWeil a b : F) ≠ 0 := by exact_mod_cast cWeil_ne_zero ha hb
  have hcw : ((cWeil a b : 𝓞 F) : F) = 8 * (a : F) ^ 3 * (b : F) ^ 3 := by
    rw [show ((cWeil a b : 𝓞 F) : F) = algebraMap (𝓞 F) F (8 * a ^ 3 * b ^ 3) from rfl]
    simp only [map_mul, map_pow, map_ofNat]
  rw [rF_toReal_eq_finprod ha hb, finprod_norm_eq_inv_real_complex _ hc, cF_three_eq, kInf, hcw]
  have hR : ∀ w : {w : InfinitePlace F // w.IsReal}, |sR w (8 * (a : F) ^ 3 * (b : F) ^ 3)| =
      8 * |sR w (a : F)| ^ 3 * |sR w (b : F)| ^ 3 := fun w => by
    simp only [map_mul, map_pow, map_ofNat, abs_mul, abs_pow]; norm_num
  have hC : ∀ w : {w : InfinitePlace F // w.IsComplex}, ‖sC w (8 * (a : F) ^ 3 * (b : F) ^ 3)‖ ^ 2 =
      (8 * ‖sC w (a : F)‖ ^ 3 * ‖sC w (b : F)‖ ^ 3) ^ 2 := fun w => by
    simp only [map_mul, map_pow, map_ofNat, norm_mul, norm_pow]; norm_num
  simp_rw [hR, hC]
  rw [mul_inv, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib, mul_assoc]
  simp only [one_div]

/-! ### Weil's measure `muPD`, explicitly -/

/-- The Haar constant $c$ of `nuRef_map_eq_smul_muPD` is nonzero. -/
theorem haarConst_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) (c : ℝ≥0)
    (hc : (nuRef ha hb).map (pdSplit a b ha hb).symm =
      (c : ℝ≥0∞) • muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha) (by simpa using hb)) :
    (c : ℝ≥0∞) ≠ 0 := by
  have h := haarConst_eq a b ha hb c hc
  have hp := kInf_pos a b ha hb
  rw [← h] at hp
  exact_mod_cast hp.ne'

/-- **Weil's measure on $PD^\times(\mathbb A)$ in the split coordinates** (every number field, every signature, every
quaternion algebra $(a,b)_F$): $(\mathrm{split})_*\mu_{PD} = K_\infty^{-1}\,(\nu_\infty\times\mu_{PD,f})$, with
$\nu_\infty$ the transport of $\mu^{\mathrm{Tam}}_\infty$ and $\mu_{PD,f}$ = `muPDFin`. -/
@[kb "weil1982" "§2.3, p. 21; §3.7(a), p. 63"]
theorem muPD_map_pdSplit (ha : a ≠ 0) (hb : b ≠ 0) :
    (muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha) (by simpa using hb)).map
      (pdSplit a b ha hb) = (ENNReal.ofReal (kInf F a b))⁻¹ • nuRef ha hb := by
  obtain ⟨c, hc⟩ := nuRef_map_eq_smul_muPD ha hb
  have hc0 := haarConst_ne_zero a b ha hb c hc
  have hK : ENNReal.ofReal (kInf F a b) = (c : ℝ≥0∞) := by
    rw [← haarConst_eq a b ha hb c hc, ENNReal.ofReal_coe_nnreal]
  rw [hK]
  have h1 : (nuRef ha hb) = ((nuRef ha hb).map (pdSplit a b ha hb).symm).map (pdSplit a b ha hb) := by
    rw [Measure.map_map (map_continuous (pdSplit a b ha hb)).measurable
      (map_continuous (pdSplit a b ha hb).symm).measurable]
    convert (Measure.map_id).symm
    funext x; simp
  rw [h1, hc, Measure.map_smul _ (map_continuous (pdSplit a b ha hb)).measurable.aemeasurable, smul_smul, ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top, one_smul]

/-! ### The covolume of $SO(V)(F)$ for `muTam` -/

/-- **From $\tau(PD^\times) = 2$ to the covolume of $SO(V)(F)$ for `muTam`** (every quaternion algebra $D = (a,b)_F$,
split or not, every number field with $r_2$ complex places, every signature): if Weil's measure `muPD` gives
$PD^\times(F)\backslash PD^\times(\mathbb A)$ volume $2$, then `muTam` gives $SO(V)(F)\backslash SO(V)(\mathbb A)$ volume
$2$. `muPD_map_pdSplit` and the product formula `rF_toReal_eq_kInf` identify the transport of `muTam` with
$\mu_{PD}$ (`covolume_pd_eq_covolume_muTam`). -/
@[kb "weil1982" "§2.3, Thm 2.3.1; §3.7(a), p. 63"]
theorem covolume_muTam_pureForm_of_covolume_muPD (ha : a ≠ 0) (hb : b ≠ 0)
    (hPD : covolume (pdGamma a b) (PDAdele a b)
      (muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha) (by simpa using hb)) = 2) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ (nondegenerate_pureFormO a b ha hb) fun _ => 1) = 2 := by
  have hQ := nondegenerate_pureFormO a b ha hb
  have ha0' : (a : F) ≠ 0 := by simpa using ha
  have hb0' : (b : F) ≠ 0 := by simpa using hb
  have hH := isHaarMeasure_muPD (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0'
  have := countable_pdGamma a b
  set ν := (muArchTamSO Q₀ hQ).map (pdInfEquiv a b ha hb).symm
  set r := rF a b
  have hr0 : r ≠ 0 := rF_ne_zero ha hb
  have hrt : r ≠ ⊤ := rF_ne_top ha hb
  have hνI : ν.IsMulLeftInvariant :=
    isMulLeftInvariant_map (μ := muArchTamSO Q₀ hQ) (pdInfEquiv a b ha hb).symm.toMulEquiv.toMonoidHom.toMulHom
      (pdInfEquiv a b ha hb).symm.continuous.measurable (pdInfEquiv a b ha hb).symm.surjective
  have hνmap : ν.map (pdInfEquiv a b ha hb) = muArchTamSO Q₀ hQ := by
    rw [Measure.map_map (map_continuous (pdInfEquiv a b ha hb)).measurable
      (map_continuous (pdInfEquiv a b ha hb).symm).measurable]
    convert Measure.map_id
    funext x; simp
  have hI : (r⁻¹ • ν).map (pdInfEquiv a b ha hb) = r⁻¹ • muArchTamSO Q₀ hQ := by
    rw [Measure.map_smul _ (map_continuous (pdInfEquiv a b ha hb)).measurable.aemeasurable, hνmap]
  have hrr : r⁻¹ * r = 1 := ENNReal.inv_mul_cancel hr0 hrt
  have htrans := covolume_pd_eq_covolume_muTam a b ha hb hQ (r⁻¹ • ν) (muPDFin ha hb) hI (map_muPDFin ha hb) hrr
  rw [← htrans, Measure.prod_smul_left]
  -- the product measure is `K_∞ ⁻¹`-rescaled `muPD`
  set K := ENNReal.ofReal (kInf F a b)
  have hK0 : K ≠ 0 := by simp only [K, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact kInf_pos a b ha hb
  have hKt : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsplit : (K • muPD (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0').map (pdSplit a b ha hb) =
      ν.prod (muPDFin ha hb) := by
    rw [Measure.map_smul _ (map_continuous (pdSplit a b ha hb)).measurable.aemeasurable, muPD_map_pdSplit a b ha hb, smul_smul, ENNReal.mul_inv_cancel hK0 hKt, one_smul, nuRef]
  have := isMulLeftInvariant_nuRef ha hb
  have hcov := covolume_eq_of_map (pdGamma a b) (pdGammaSplit a b ha hb) (pdSplit a b ha hb).toMulEquiv
    (pdSplit a b ha hb).continuous.measurable (pdSplit a b ha hb).symm.continuous.measurable rfl _ _ hsplit
  have : (ν.prod (muPDFin ha hb)).IsMulLeftInvariant := by unfold nuRef at this; exact this
  rw [covolume_smul _ _ (ENNReal.inv_ne_zero.mpr hrt), ← hcov, covolume_smul _ _ hK0,
    hPD]
  -- `r⁻¹ * (K * 2) = 2`, from `r = K`
  have hrK : r = K := by
    rw [← ENNReal.ofReal_toReal hrt, rF_toReal_eq_kInf a b ha hb]
  rw [hrK, ← mul_assoc, ENNReal.inv_mul_cancel hK0 hKt, one_mul]

/-- **The covolume of $SO(V)(F)$ in $SO(V)(\mathbb A)$ for `muTam`** ($V = D^0$, $D = (a,b)_F$ a division algebra over
every number field $F$, every signature): it is $2$, unconditionally. $\tau(PD^\times) = 2$
for `muPD` (`tamagawa_PD_division`) and `covolume_muTam_pureForm_of_covolume_muPD`. -/
@[kb "weil1982" "Thm 3.2.1, p. 43; §2.3, Thm 2.3.1; §3.7(a), p. 63"]
theorem covolume_muTam_pureForm (ha : a ≠ 0) (hb : b ≠ 0)
    (hdiv : ∀ ξ : ℍ[F,(a : F),(b : F)], ξ ≠ 0 → IsUnit ξ) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ (nondegenerate_pureFormO a b ha hb) fun _ => 1) = 2 :=
  covolume_muTam_pureForm_of_covolume_muPD a b ha hb (tamagawa_PD_division a b ha hb hdiv)

/-- **`TamagawaNumberTwoAdelic` for $\langle-a,-b,ab\rangle$ over every number field, every signature**
($D = (a,b)_F$ a division algebra; definite or indefinite at each real place, complex places allowed): unconditional. -/
@[kb "weil1982" "Thm 3.2.1, p. 43; §2.3, Thm 2.3.1; §3.7(a), p. 63; Thm 3.7.1 (m = 3), p. 65"]
theorem tamagawaNumberTwoAdelic_pureForm (ha : a ≠ 0) (hb : b ≠ 0)
    (hdiv : ∀ ξ : ℍ[F,(a : F),(b : F)], ξ ≠ 0 → IsUnit ξ) :
    TamagawaNumberTwoAdelic Q₀ (nondegenerate_pureFormO a b ha hb) :=
  covolume_muTam_pureForm a b ha hb hdiv

/-- **`TamagawaNumberTwoAdelic` for $\langle-a,-b,ab\rangle$ over every totally real field, every signature**
($D = (a,b)_F$ a division algebra): the totally real case of `tamagawaNumberTwoAdelic_pureForm` (name kept). -/
@[kb "weil1982" "Thm 3.2.1, p. 43; §2.3, Thm 2.3.1; §3.7(a), p. 63; Thm 3.7.1 (m = 3), p. 65"]
theorem tamagawaNumberTwoAdelic_pureForm_of_totallyReal [IsTotallyReal F] (ha : a ≠ 0) (hb : b ≠ 0)
    (hdiv : ∀ ξ : ℍ[F,(a : F),(b : F)], ξ ≠ 0 → IsUnit ξ) :
    TamagawaNumberTwoAdelic Q₀ (nondegenerate_pureFormO a b ha hb) :=
  tamagawaNumberTwoAdelic_pureForm a b ha hb hdiv

/-! ### Weil's normalization at the complex places -/

section WeilNorm

variable {n : ℕ} (Q : QuadForm (𝓞 F) n)

/-- **The former name of Weil's Tamagawa measure** with $\lambda_v = 1$: now `muTam` itself carries Weil's
normalization $|dz\wedge d\bar z| = 2\,dx\,dy$ at the complex places (`cxWeil`), so `muTamWeil` is `muTam` with
$\lambda_v = 1$ (`muTamWeil_eq_muTam`); kept so that the name stays stable. -/
@[kb "weil1982" "§2.2 (gauge forms, |dz∧dz̄| at complex places), §2.3, p. 21 [unverified]"]
def muTamWeil (hQ : Q.Nondegenerate) : Measure (SOAdele Q) :=
  muTam Q hQ fun _ => 1

theorem muTamWeil_eq_muTam (hQ : Q.Nondegenerate) : muTamWeil Q hQ = muTam Q hQ fun _ => 1 := rfl

end WeilNorm

/-- **$\tau(SO(V)) = 2$ for every ternary space $D^0$ of a division algebra over every number field, every signature**,
for `muTamWeil` $=$ `muTam` (unconditional; the same statement as `covolume_muTam_pureForm`). -/
@[kb "weil1982" "Thm 3.2.1, p. 43; §2.3, Thm 2.3.1; §3.7(a), p. 63; Thm 3.7.1 (m = 3), p. 65"]
theorem covolume_muTamWeil_pureForm (ha : a ≠ 0) (hb : b ≠ 0)
    (hdiv : ∀ ξ : ℍ[F,(a : F),(b : F)], ξ ≠ 0 → IsUnit ξ) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTamWeil Q₀ (nondegenerate_pureFormO a b ha hb)) = 2 :=
  covolume_muTam_pureForm a b ha hb hdiv

end QuadFormsKB.Tamagawa.Measure.Weil
