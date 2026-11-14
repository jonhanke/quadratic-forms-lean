import QuadFormsKB.Tamagawa.Measure.Weil.SLnSiegel
import QuadFormsKB.Tamagawa.Measure.Weil.TauTwoAnisotropicGauss
import QuadFormsKB.Tamagawa.Measure.Weil.SL2Tamagawa

/-!
# The Tamagawa number of $\mathrm{SL}_n$ over a number field is $1$

$F$ a number field, $\mu_n$ = `muSL F (n - 1)` the Tamagawa measure of $\mathrm{SL}_n(\mathbb A_F)$ (fibration measure
of Weil 1982, Thm 2.4.3, `SLnInduct.lean`), $\tau_n = \operatorname{vol}(\mathrm{SL}_n(\mathbb A_F)/\mathrm{SL}_n(F))$
(`tauSL`).

**`tamagawa_SLn`**: $\tau(\mathrm{SL}_n) = 1$ for every $n\ge1$ and every number field $F$.

*Proof* (Siegel–Weil; for $n = 2$ this is `tamagawa_SL2`). Induction on $n$, $\tau_1 = 1$. For
$\Phi = G\otimes\mathbf 1_{\hat{\mathcal O}^n}$ (`gaussTest`) and an idele $z$ with $\rho = \|z\|^n > 1$ (archimedean
components $2$, finite components $1$), the adelic Poisson formula (`glTheta_poisson_dual`) for the pair
$M = zg$, $M' = z^{-1}g^*$, $g^* = (g^{-1})^{\mathsf T}$ ($M'^{\mathsf T}M = 1$) gives, for every
$g\in\mathrm{SL}_n(\mathbb A_F)$,
$$\rho\sum_{\xi\in F^n}\Phi(zg\xi) = \mu_f(\hat{\mathcal O}^n)\sum_{\eta\in F^n}\Psi(z^{-1}g^*\eta),$$
$\Psi = G\otimes\mathbf 1_{\hat{\mathfrak d}^{-1,n}}$. Integrate over a fundamental domain $D$: the terms $\xi = 0$ give
$\tau_n$, Siegel's mean value theorem (`lintegral_tsum_mulVec_eqN`) the rest (for the right side after the
measure-preserving involution $g\mapsto g^*$, `map_starSL`, which maps $D$ to another fundamental domain). With
$\int\Phi(zy)\,dy = \rho^{-1}c$, $\int\Psi(z^{-1}y)\,dy = \rho c^{-1}$, $c = \mu_f(\hat{\mathcal O}^n)\le1$:
$$\rho\tau_n + c\,\tau_{n-1} = c\,\tau_n + \rho\,\tau_{n-1},\qquad\text{i.e. } (\rho - c)(\tau_n - \tau_{n-1}) = 0,$$
so $\tau_n = \tau_{n-1}$.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology NumberField.mixedEmbedding Matrix
open scoped ENNReal NNReal Classical MatrixGroups

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil.SLn

noncomputable section

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

local notation "V" => mixedSpace F
local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### Gaussian integrals on $\mathbb A_F^n$ -/

theorem integrable_gV_fin (n : ℕ) : Integrable (gV (F := F) (ι := Fin n)) (muInfVec F (Fin n)) := by
  have h := (gaussV F (Fin n)).integrable (μ := muInfVec F (Fin n))
  refine (h.norm).congr (Eventually.of_forall fun y => ?_)
  simp only [gaussV_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gV_pos _)]

theorem lintegral_ofReal_gV (n : ℕ) : ∫⁻ z, ENNReal.ofReal (gV z) ∂muInfVec F (Fin n) = 1 := by
  have h1 : ∫ y, gV y ∂muInfVec F (Fin n) = 1 := by
    have h := fourierV_gaussV (F := F) (ι := Fin n) 0
    simp only [map_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one, gV_zero, Complex.ofReal_one] at h
    simp_rw [gaussV_apply] at h
    rw [integral_complex_ofReal] at h
    exact_mod_cast h
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp, ← h1,
    ofReal_integral_eq_lintegral_ofReal (integrable_gV_fin n) (Eventually.of_forall fun y => (gV_pos y).le)]

theorem lintegral_muAddVec_split {n : ℕ} (a : (Fin n → V) → ℝ≥0∞) (b : (Fin n → AF) → ℝ≥0∞)
    (ha : Measurable a) (hb : Measurable b) :
    ∫⁻ y, a (fun i => (y i).1) * b (fun i => (y i).2) ∂muAddVec F (Fin n) =
      (∫⁻ x, a x ∂muInfVec F (Fin n)) * ∫⁻ x, b x ∂muFinVec F (Fin n) := by
  have hp := measurePreserving_arrowProd (F := F) (ι := Fin n)
  have : (fun y : AdeleSpace F (Fin n) => a (fun i => (y i).1) * b (fun i => (y i).2)) =
      (fun p : (Fin n → V) × (Fin n → AF) => a p.1 * b p.2) ∘
        (MeasurableEquiv.arrowProdEquivProdArrow (mixedSpace F) AF (Fin n)) := rfl
  rw [this]
  show ∫⁻ y, (fun p : (Fin n → V) × (Fin n → AF) => a p.1 * b p.2)
    (MeasurableEquiv.arrowProdEquivProdArrow (mixedSpace F) AF (Fin n) y) ∂muAddVec F (Fin n) = _
  rw [hp.lintegral_comp (f := fun p : (Fin n → V) × (Fin n → AF) => a p.1 * b p.2)
      ((ha.comp measurable_fst).mul (hb.comp measurable_snd)),
    lintegral_prod_mul ha.aemeasurable hb.aemeasurable]

theorem measurable_gV_fin (n : ℕ) : Measurable (gV (F := F) (ι := Fin n)) :=
  (continuous_finset_prod _ fun i _ => continuous_gR.comp (continuous_apply i)).measurable

theorem measurableSet_OHatVec' (n : ℕ) : MeasurableSet (OHatVec : Set (Fin n → AF)) :=
  MeasurableSet.univ_pi fun _ => measurableSet_OHat

theorem lintegral_gaussTest (n : ℕ) :
    ∫⁻ y, gaussTest F n y ∂muAddVec F (Fin n) = muFinVec F (Fin n) OHatVec := by
  have : gaussTest F n = fun y => ENNReal.ofReal (gV fun i => (y i).1) *
      (OHatVec : Set (Fin n → AF)).indicator 1 (fun i => (y i).2) := by
    funext y; rw [gaussTest, mul_comm]; rfl
  simp only [this]
  rw [lintegral_muAddVec_split (fun x => ENNReal.ofReal (gV x)) ((OHatVec : Set (Fin n → AF)).indicator 1)
    (ENNReal.measurable_ofReal.comp (measurable_gV_fin n))
    (measurable_one.indicator (measurableSet_OHatVec' n)), lintegral_ofReal_gV,
    one_mul, lintegral_indicator_one (measurableSet_OHatVec' n)]

theorem lintegral_gaussDualTest (n : ℕ) :
    ∫⁻ y, gaussDualTest F n y ∂muAddVec F (Fin n) = muFinVec F (Fin n) {c | ∀ i, c i ∈ DHat} := by
  have : gaussDualTest F n = fun y => ENNReal.ofReal (gV fun i => (y i).1) *
      {c : Fin n → AF | ∀ i, c i ∈ DHat}.indicator 1 (fun i => (y i).2) := by
    funext y; rw [gaussDualTest, mul_comm]; rfl
  simp only [this]
  rw [lintegral_muAddVec_split (fun x => ENNReal.ofReal (gV x)) ({c : Fin n → AF | ∀ i, c i ∈ DHat}.indicator 1)
    (ENNReal.measurable_ofReal.comp (measurable_gV_fin n))
    (measurable_one.indicator measurableSet_DHatVec), lintegral_ofReal_gV,
    one_mul, lintegral_indicator_one measurableSet_DHatVec]

theorem muFinVec_OHatVec_le_one (n : ℕ) : muFinVec F (Fin n) OHatVec ≤ 1 := by
  rw [muFinVec_OHatVec, muFin_OHat]
  refine Finset.prod_le_one fun _ _ => ?_
  rw [ENNReal.ofReal_le_one, ohatVol]
  refine inv_le_one_of_one_le₀ ?_
  rw [Real.one_le_sqrt]
  have h := discr_ne_zero F
  have : (1 : ℤ) ≤ |discr F| := Int.one_le_abs h
  exact_mod_cast this

theorem muFinVec_OHatVec_ne_top (n : ℕ) : muFinVec F (Fin n) OHatVec ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (muFinVec_OHatVec_le_one n)

/-! ### The involution $g\mapsto g^* = (g^{-1})^{\mathsf T}$ -/

section Star

variable {R S : Type*} [CommRing R] [CommRing S] {m : ℕ}

/-- The transpose in $\mathrm{SL}_m(R)$. -/
def trSL (g : SpecialLinearGroup (Fin m) R) : SpecialLinearGroup (Fin m) R :=
  ⟨(g : Matrix (Fin m) (Fin m) R)ᵀ, by rw [det_transpose, g.2]⟩

theorem trSL_mul (g h : SpecialLinearGroup (Fin m) R) : trSL (g * h) = trSL h * trSL g :=
  Subtype.ext (transpose_mul _ _)

theorem trSL_trSL (g : SpecialLinearGroup (Fin m) R) : trSL (trSL g) = g := Subtype.ext (transpose_transpose _)

theorem trSL_one : trSL (1 : SpecialLinearGroup (Fin m) R) = 1 := Subtype.ext transpose_one

theorem trSL_inv (g : SpecialLinearGroup (Fin m) R) : trSL g⁻¹ = (trSL g)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← trSL_mul, mul_inv_cancel, trSL_one]

/-- **The involution** $g^* = (g^{-1})^{\mathsf T}$, an automorphism of $\mathrm{SL}_m(R)$. -/
def starSL : SpecialLinearGroup (Fin m) R →* SpecialLinearGroup (Fin m) R where
  toFun g := trSL g⁻¹
  map_one' := by rw [inv_one, trSL_one]
  map_mul' g h := by rw [_root_.mul_inv_rev, trSL_mul]

theorem starSL_apply (g : SpecialLinearGroup (Fin m) R) : starSL g = trSL g⁻¹ := rfl

theorem starSL_starSL (g : SpecialLinearGroup (Fin m) R) : starSL (starSL g) = g := by
  rw [starSL_apply, starSL_apply, ← trSL_inv, inv_inv, trSL_trSL]

theorem starSL_map (f : R →+* S) (g : SpecialLinearGroup (Fin m) R) :
    starSL (SpecialLinearGroup.map f g) = SpecialLinearGroup.map f (starSL g) := by
  rw [starSL_apply, starSL_apply, ← map_inv]
  exact Subtype.ext Matrix.transpose_map.symm

theorem coe_starSL_transpose (g : SpecialLinearGroup (Fin m) R) :
    ((starSL g : SpecialLinearGroup (Fin m) R) : Matrix (Fin m) (Fin m) R)ᵀ =
      ((g⁻¹ : SpecialLinearGroup (Fin m) R) : Matrix (Fin m) (Fin m) R) :=
  transpose_transpose _

end Star

theorem measurable_starSL {m : ℕ} : Measurable (starSL : SLnA F (Fin m) → SLnA F (Fin m)) := by
  refine measurable_SLnA_iff.mpr fun r c => ?_
  exact (measurable_SLnA_entry c r).comp measurable_inv

theorem slnEmb_starSL {m : ℕ} (γ : SpecialLinearGroup (Fin m) F) :
    slnEmb F (Fin m) (starSL γ) = starSL (slnEmb F (Fin m) γ) :=
  (starSL_map (diagRing F) γ).symm

/-- **The involution $g\mapsto g^*$ preserves the Tamagawa measure.** -/
theorem map_starSL (k : ℕ) : (muSL F k).map starSL = muSL F k := by
  obtain ⟨U, -, h0, ht⟩ := OrbitSection.exists_pos_lt_top (X := SLnA F (Fin (k + 1))) (muSL F k) (good_muSL k).ne_zero
  exact map_involution_eq h0 ht starSL measurable_starSL starSL_starSL

/-- $g\mapsto g^*$ maps exact fundamental domains of $G_{\mathbb A}/G_k$ to exact fundamental domains. -/
theorem existsUnique_starSL_preimage {m : ℕ} {D : Set (SLnA F (Fin m))}
    (hD : ∀ g : SLnA F (Fin m), ∃! γ : SpecialLinearGroup (Fin m) F, γ • g ∈ D) (g : SLnA F (Fin m)) :
    ∃! γ : SpecialLinearGroup (Fin m) F, γ • g ∈ starSL ⁻¹' D := by
  have hst : ∀ γ : SpecialLinearGroup (Fin m) F, starSL (γ • g) = starSL γ • starSL g := by
    intro γ
    rw [slnRight_smul_def, slnRight_smul_def, map_mul, map_inv, slnEmb_starSL]
  obtain ⟨γ₀, h₀, hu⟩ := hD (starSL g)
  refine ⟨starSL γ₀, ?_, fun γ hγ => ?_⟩
  · show starSL (starSL γ₀ • g) ∈ D
    rw [hst, starSL_starSL]; exact h₀
  · have : starSL γ ∈ {γ : SpecialLinearGroup (Fin m) F | γ • starSL g ∈ D} := by
      show starSL γ • starSL g ∈ D
      rw [← hst]; exact hγ
    rw [← hu _ this, starSL_starSL]

/-! ### The idele $z$ -/

variable (F) in
/-- The idele with archimedean components $2$ and finite components $1$. -/
def zIdele : (Adeles F)ˣ := MulEquiv.prodUnits.symm (twoU (F := F), 1)

theorem one_lt_ideleNorm_zIdele : 1 < ideleNorm F (zIdele F) := by
  have hinf : infPart (zIdele F) = twoU := Units.ext rfl
  have hfin : finPart (zIdele F) = 1 := Units.ext rfl
  rw [ideleNorm, hinf, hfin]
  have h1 : ∀ v, (modAt (1 : AFˣ) v : ℝ) = 1 := fun v => by
    have : unitAt (1 : AFˣ) v = 1 := Units.ext rfl
    rw [modAt, this, map_one]; rfl
  simp only [h1, finprod_one, mul_one]
  rw [← distribHaarChar_mixedSpace]
  have := modInf_twoU (F := F)
  rw [modInf] at this
  rw [this]
  exact one_lt_pow₀ one_lt_two (Module.finrank_pos (R := ℚ) (M := F)).ne'

/-! ### The adelic Poisson formula for $\mathrm{SL}_n$ -/

/-- $M = z\,g$. -/
def pairMz {n : ℕ} (z : (Adeles F)ˣ) (g : SLnA F (Fin n)) : GL (Fin n) (Adeles F) :=
  GeneralLinearGroup.scalar (Fin n) z * SpecialLinearGroup.toGL g

/-- $M' = z^{-1}g^*$. -/
def pairMz' {n : ℕ} (z : (Adeles F)ˣ) (g : SLnA F (Fin n)) : GL (Fin n) (Adeles F) :=
  GeneralLinearGroup.scalar (Fin n) z⁻¹ * SpecialLinearGroup.toGL (starSL g)

theorem coe_pairMz {n : ℕ} (z : (Adeles F)ˣ) (g : SLnA F (Fin n)) :
    (pairMz z g : Matrix (Fin n) (Fin n) (Adeles F)) = (z : Adeles F) • (g : Matrix (Fin n) (Fin n) (Adeles F)) := by
  rw [pairMz, Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_mul_eq_smul]; rfl

theorem coe_pairMz' {n : ℕ} (z : (Adeles F)ˣ) (g : SLnA F (Fin n)) :
    (pairMz' z g : Matrix (Fin n) (Fin n) (Adeles F)) =
      ((z⁻¹ : (Adeles F)ˣ) : Adeles F) • (starSL g : Matrix (Fin n) (Fin n) (Adeles F)) := by
  rw [pairMz', Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_mul_eq_smul]; rfl

theorem pairMz'_transpose_mul {n : ℕ} (z : (Adeles F)ˣ) (g : SLnA F (Fin n)) :
    (pairMz' z g : Matrix (Fin n) (Fin n) (Adeles F))ᵀ * pairMz z g = 1 := by
  have e : ((g⁻¹ : SLnA F (Fin n)) : Matrix (Fin n) (Fin n) (Adeles F)) * (g : Matrix (Fin n) (Fin n) (Adeles F)) =
      1 := congrArg Subtype.val (inv_mul_cancel g)
  rw [coe_pairMz', coe_pairMz, transpose_smul, coe_starSL_transpose, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, e, Units.inv_mul, one_smul]

theorem ideleNorm_det_scalar {n : ℕ} (z : (Adeles F)ˣ) :
    ideleNorm F (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) z)) = ideleNorm F z ^ n := by
  rw [GeneralLinearGroup.det_scalar, Fintype.card_fin, ← coe_ideleNormHom, map_pow, NNReal.coe_pow,
    coe_ideleNormHom]

theorem det_toGL_SL {n : ℕ} (g : SLnA F (Fin n)) : GeneralLinearGroup.det (SpecialLinearGroup.toGL g) = 1 :=
  Units.ext (by rw [SpecialLinearGroup.coeToGL_det])

theorem ideleNorm_det_pairMz {n : ℕ} (z : (Adeles F)ˣ) (g : SLnA F (Fin n)) :
    ideleNorm F (GeneralLinearGroup.det (pairMz z g)) = ideleNorm F z ^ n := by
  rw [pairMz, map_mul, det_toGL_SL, mul_one, ideleNorm_det_scalar]

/-- **The adelic Poisson formula on $\mathrm{SL}_n(\mathbb A_F)$**: for every $g$,
$\|z\|^n\sum_{\xi\in F^n}\Phi(zg\xi) = \mu_f(\hat{\mathcal O}^n)\sum_{\eta\in F^n}\Psi(z^{-1}g^*\eta)$. -/
@[kb "weil1982" "§2.1, Poisson formula on X_A [unverified page]; Siegel–Weil argument for SL_n"]
theorem poisson_SLn {n : ℕ} (z : (Adeles F)ˣ) (g : SLnA F (Fin n)) :
    ENNReal.ofReal (ideleNorm F z ^ n) * ∑' ξ : Fin n → F,
        gaussTest F n (z • ((g : Matrix (Fin n) (Fin n) (Adeles F)) *ᵥ diagVec F (Fin n) ξ)) =
      muFinVec F (Fin n) OHatVec * ∑' η : Fin n → F,
        gaussDualTest F n (z⁻¹ • ((starSL g : Matrix (Fin n) (Fin n) (Adeles F)) *ᵥ diagVec F (Fin n) η)) := by
  have h := glTheta_poisson_dual (pairMz'_transpose_mul z g)
  rw [ideleNorm_det_pairMz] at h
  have hL : glTheta (pairMz z g) (OHatVecSub F (Fin n)) = ∑' ξ : Fin n → F,
      gaussTest F n (z • ((g : Matrix (Fin n) (Fin n) (Adeles F)) *ᵥ diagVec F (Fin n) ξ)) := by
    refine tsum_congr fun ξ => ?_
    rw [← gaussTest_mulVec, coe_pairMz, Matrix.smul_mulVec]; rfl
  have hR : glTheta (pairMz' z g) (DHatVecSub F (Fin n)) = ∑' η : Fin n → F,
      gaussDualTest F n (z⁻¹ • ((starSL g : Matrix (Fin n) (Fin n) (Adeles F)) *ᵥ diagVec F (Fin n) η)) := by
    refine tsum_congr fun η => ?_
    rw [← gaussDualTest_mulVec, coe_pairMz', Matrix.smul_mulVec]; rfl
  rw [hL, hR] at h
  exact h

/-! ### Integrating the Poisson formula over $G_{\mathbb A}/G_k$ -/

theorem tsum_split_zeroN (f : (Fin (k + 2) → F) → ℝ≥0∞) :
    ∑' ξ : Fin (k + 2) → F, f ξ = f 0 + ∑' ξ : NZ F k, f ξ.1 := by
  rw [ENNReal.tsum_eq_add_tsum_ite 0]
  congr 1
  show _ = ∑' ξ : ({ξ : Fin (k + 2) → F | ξ ≠ 0} : Set (Fin (k + 2) → F)), f ξ
  rw [tsum_subtype]
  refine tsum_congr fun ξ => ?_
  by_cases h : ξ = 0
  · rw [if_pos h, Set.indicator_of_notMem (show ξ ∉ {ξ : Fin (k + 2) → F | ξ ≠ 0} from fun h' => h' h)]
  · rw [if_neg h, Set.indicator_of_mem (show ξ ∈ {ξ : Fin (k + 2) → F | ξ ≠ 0} from h)]

theorem measurable_SLnA_mulVec {m : ℕ} (v : AdeleSpace F (Fin m)) :
    Measurable fun g : SLnA F (Fin m) => (g : Matrix (Fin m) (Fin m) (Adeles F)) *ᵥ v :=
  measurable_pi_iff.mpr fun i => by
    simp only [mulVec, dotProduct]
    exact Finset.measurable_sum _ fun j _ => (measurable_SLnA_entry i j).mul_const _

theorem measurable_units_smul {n : ℕ} (u : (Adeles F)ˣ) :
    Measurable fun y : AdeleSpace F (Fin n) => u • y :=
  (continuous_const_smul u).measurable

/-- $\int f(uy)\,dy = \|u\|^{-n}\int f\,dy$ on $\mathbb A_F^n$. -/
theorem lintegral_comp_units_smul {n : ℕ} (u : (Adeles F)ˣ) (f : AdeleSpace F (Fin n) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y, f (u • y) ∂muAddVec F (Fin n) =
      ENNReal.ofReal (ideleNorm F u ^ n)⁻¹ * ∫⁻ y, f y ∂muAddVec F (Fin n) := by
  have h := map_mulVec_muAddVec (F := F) (ι := Fin n) (GeneralLinearGroup.scalar (Fin n) u)
  rw [ideleNorm_det_scalar] at h
  have e : (fun y : AdeleSpace F (Fin n) => u • y) =
      ((GeneralLinearGroup.scalar (Fin n) u : GL (Fin n) (Adeles F)) : Matrix (Fin n) (Fin n) (Adeles F)).mulVec := by
    funext y i
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, mulVec_diagonal]
    rfl
  rw [← lintegral_map hf (measurable_units_smul u), e, h, lintegral_smul_measure, smul_eq_mul]

/-- **The integrated Poisson identity** on $\mathrm{SL}_n(\mathbb A_F)$, $n = k + 2$: for every exact fundamental domain
$D$, with $\tau = \mu_n(D)$, $\tau' = \tau_{n-1}$, $\rho = \|z\|^n$, $c = \mu_f(\hat{\mathcal O}^n)$:
$\rho\,(\tau + \tau'\rho^{-1}c) = c\,(\tau + \tau'\,\|z^{-1}\|^{-n}\,\mu_f(\hat{\mathfrak d}^{-1,n}))$. -/
theorem integrated_identity_SLn {D : Set (SLnA F (Fin (k + 2)))} (hDm : MeasurableSet D)
    (hD : ∀ g : SLnA F (Fin (k + 2)), ∃! γ : SpecialLinearGroup (Fin (k + 2)) F, γ • g ∈ D) :
    ENNReal.ofReal (ideleNorm F (zIdele F) ^ (k + 2)) *
        (muSL F (k + 1) D + tauSL F k * (ENNReal.ofReal (ideleNorm F (zIdele F) ^ (k + 2))⁻¹ *
          muFinVec F (Fin (k + 2)) OHatVec)) =
      muFinVec F (Fin (k + 2)) OHatVec * (muSL F (k + 1) D + tauSL F k *
        (ENNReal.ofReal (ideleNorm F (zIdele F)⁻¹ ^ (k + 2))⁻¹ *
          muFinVec F (Fin (k + 2)) {c | ∀ i, c i ∈ DHat})) := by
  set z := zIdele F
  set Φ : AdeleSpace F (Fin (k + 2)) → ℝ≥0∞ := fun y => gaussTest F (k + 2) (z • y)
  set Ψ : AdeleSpace F (Fin (k + 2)) → ℝ≥0∞ := fun y => gaussDualTest F (k + 2) (z⁻¹ • y)
  have hΦm : Measurable Φ := measurable_gaussTest.comp (measurable_units_smul z)
  have hΨm : Measurable Ψ := measurable_gaussDualTest.comp (measurable_units_smul z⁻¹)
  have hΦ0 : Φ 0 = 1 := by simp only [Φ, smul_zero, gaussTest_zero, ENNReal.ofReal_one]
  have hΨ0 : Ψ 0 = 1 := by simp only [Ψ, smul_zero, gaussDualTest_zero]
  have hFD : IsFundamentalDomain (SpecialLinearGroup (Fin (k + 2)) F) D (muSL F (k + 1)) :=
    IsFundamentalDomain.mk' hDm.nullMeasurableSet hD
  have hFD' : IsFundamentalDomain (SpecialLinearGroup (Fin (k + 2)) F) (starSL ⁻¹' D) (muSL F (k + 1)) :=
    IsFundamentalDomain.mk' (hDm.preimage measurable_starSL).nullMeasurableSet (existsUnique_starSL_preimage hD)
  -- the pointwise identity
  set S1 : SLnA F (Fin (k + 2)) → ℝ≥0∞ := fun g => ∑' ξ : NZ F k,
    Φ ((g : Matrix (Fin (k + 2)) (Fin (k + 2)) (Adeles F)) *ᵥ diagVec F (Fin (k + 2)) ξ.1)
  set S2 : SLnA F (Fin (k + 2)) → ℝ≥0∞ := fun g => ∑' η : NZ F k,
    Ψ ((g : Matrix (Fin (k + 2)) (Fin (k + 2)) (Adeles F)) *ᵥ diagVec F (Fin (k + 2)) η.1)
  have hpt : ∀ g : SLnA F (Fin (k + 2)), ENNReal.ofReal (ideleNorm F z ^ (k + 2)) * (1 + S1 g) =
      muFinVec F (Fin (k + 2)) OHatVec * (1 + S2 (starSL g)) := by
    intro g
    have h := poisson_SLn z g
    rw [tsum_split_zeroN (fun ξ => Φ ((g : Matrix (Fin (k + 2)) (Fin (k + 2)) (Adeles F)) *ᵥ diagVec F (Fin (k + 2)) ξ)),
      tsum_split_zeroN (fun η => Ψ ((starSL g : Matrix (Fin (k + 2)) (Fin (k + 2)) (Adeles F)) *ᵥ diagVec F (Fin (k + 2)) η))] at h
    simpa only [map_zero, mulVec_zero, hΦ0, hΨ0] using h
  have hS2m : Measurable S2 := Measurable.ennreal_tsum fun η => hΨm.comp (measurable_SLnA_mulVec _)
  have hstar : MeasurePreserving (starSL : SLnA F (Fin (k + 2)) → SLnA F (Fin (k + 2))) (muSL F (k + 1)) (muSL F (k + 1)) :=
    ⟨measurable_starSL, map_starSL (k + 1)⟩
  have hpre : starSL ⁻¹' (starSL ⁻¹' D) = D := by
    ext g; simp only [Set.mem_preimage, starSL_starSL]
  have hint := congrArg (fun φ : SLnA F (Fin (k + 2)) → ℝ≥0∞ => ∫⁻ g in D, φ g ∂muSL F (k + 1)) (funext hpt)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ (muFinVec_OHatVec_ne_top (k + 2)),
    lintegral_add_left measurable_const, lintegral_add_left measurable_const, setLIntegral_const,
    one_mul, lintegral_tsum_mulVec_eqN hFD Φ hΦm] at hint
  have h2 : ∫⁻ g in D, S2 (starSL g) ∂muSL F (k + 1) = tauSL F k * ∫⁻ y, Ψ y ∂muAddVec F (Fin (k + 2)) := by
    rw [← hpre, hstar.setLIntegral_comp_preimage (hDm.preimage measurable_starSL) hS2m]
    exact lintegral_tsum_mulVec_eqN hFD' Ψ hΨm
  rw [h2, lintegral_comp_units_smul z _ measurable_gaussTest, lintegral_gaussTest,
    lintegral_comp_units_smul z⁻¹ _ measurable_gaussDualTest, lintegral_gaussDualTest] at hint
  exact hint

theorem ideleNorm_inv (u : (Adeles F)ˣ) : ideleNorm F u⁻¹ = (ideleNorm F u)⁻¹ := by
  have h := ideleNorm_mul (F := F) u u⁻¹
  rw [mul_inv_cancel, ideleNorm_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem muFinVec_OHatVec_ne_zero (n : ℕ) : muFinVec F (Fin n) OHatVec ≠ 0 := by
  rw [muFinVec_OHatVec, muFin_OHat]
  exact Finset.prod_ne_zero_iff.mpr fun _ _ => by simpa using ohatVol_pos (F := F)

/-- **The induction step** $\tau(\mathrm{SL}_{k+2}) = \tau(\mathrm{SL}_{k+1})$. -/
theorem tauSL_succ (k : ℕ) : tauSL F (k + 1) = tauSL F k := by
  obtain ⟨D, hDm, hD⟩ := exists_measurableSet_forall_existsUnique_right' (F := F) (ι := Fin (k + 2))
  have hFD : IsFundamentalDomain (SpecialLinearGroup (Fin (k + 2)) F) D (muSL F (k + 1)) :=
    IsFundamentalDomain.mk' hDm.nullMeasurableSet hD
  have hE := integrated_identity_SLn hDm hD
  rw [tauSL_eq hFD]
  have hτ := (tauSL_pos_lt_top (F := F) (k + 1)).2
  rw [tauSL_eq hFD] at hτ
  have hτ' := (tauSL_pos_lt_top (F := F) k).2
  set τ := muSL F (k + 1) D
  set τ' := tauSL F k
  set c := muFinVec F (Fin (k + 2)) OHatVec
  set d := muFinVec F (Fin (k + 2)) {c | ∀ i, c i ∈ DHat}
  set r := ideleNorm F (zIdele F) ^ (k + 2)
  have hr1 : 1 < r := one_lt_pow₀ one_lt_ideleNorm_zIdele (by omega)
  have hr0 : 0 < r := lt_trans zero_lt_one hr1
  have hrinv : ideleNorm F (zIdele F)⁻¹ ^ (k + 2) = r⁻¹ := by rw [ideleNorm_inv, inv_pow]
  rw [hrinv, inv_inv] at hE
  have hc0 := muFinVec_OHatVec_ne_zero (F := F) (k + 2)
  have hct := muFinVec_OHatVec_ne_top (F := F) (k + 2)
  have hcd : c * d = 1 := muFinVec_OHatVec_mul_DHatVec
  have hdt : d ≠ ∞ := by
    intro h; rw [h, ENNReal.mul_top hc0] at hcd; exact ENNReal.top_ne_one hcd
  have hc1 : c.toReal ≤ 1 := by
    have := muFinVec_OHatVec_le_one (F := F) (k + 2)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  have hcdR : c.toReal * d.toReal = 1 := by
    rw [← ENNReal.toReal_mul, hcd, ENNReal.toReal_one]
  -- pass to real numbers
  have hR := congrArg ENNReal.toReal hE
  have f1 : ENNReal.ofReal r⁻¹ * c ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hct
  have f2 : ENNReal.ofReal r * d ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hdt
  rw [ENNReal.toReal_mul, ENNReal.toReal_add hτ.ne (ENNReal.mul_ne_top hτ'.ne f1), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hr0.le, ENNReal.toReal_ofReal (inv_nonneg.mpr hr0.le),
    ENNReal.toReal_mul, ENNReal.toReal_add hτ.ne (ENNReal.mul_ne_top hτ'.ne f2), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hr0.le] at hR
  -- `(r - c)(τ - τ') = 0`
  have key : (r - c.toReal) * (τ.toReal - τ'.toReal) = 0 := by
    have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0.ne'
    linear_combination hR + τ'.toReal * r * hcdR - τ'.toReal * c.toReal * hrr
  have hne : r - c.toReal ≠ 0 := by linarith
  have ht : τ.toReal = τ'.toReal := by
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hne
    · linarith
  rw [← ENNReal.ofReal_toReal hτ.ne, ← ENNReal.ofReal_toReal hτ'.ne, ht]

/-- **The Tamagawa number of $\mathrm{SL}_n$ over a number field is $1$**: for every $n = k + 1\ge1$ and every
number field $F$, $\operatorname{vol}(\mathrm{SL}_n(\mathbb A_F)/\mathrm{SL}_n(F)) = 1$ for the Tamagawa measure
`muSL F k` (Weil's fibration measure $\omega_{\mathrm{SL}_n} = dy\wedge\omega_{\mathrm{SL}_{n-1}}\wedge dc$ with self-dual
additive measures). Unconditional. -/
@[kb "weil1982" "Ch. III (τ(SL_n) = 1) [unverified locator]; §2.4, Lemma 2.4.2, Thm 2.4.3; Siegel's mean value theorem and the adelic Poisson formula (the n = 2 proof of tamagawa_SL2, by induction on n)"]
theorem tamagawa_SLn : ∀ k : ℕ,
    covolume (SpecialLinearGroup (Fin (k + 1)) F) (SLnA F (Fin (k + 1))) (muSL F k) = 1
  | 0 => tauSL_zero
  | k + 1 => (tauSL_succ k).trans (tamagawa_SLn k)

end

end QuadFormsKB.Tamagawa.Measure.Weil.SLn
