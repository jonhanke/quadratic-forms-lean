import QuadFormsKB.Tamagawa.Measure.Weil.SphericalUnfoldAdelic
import QuadFormsKB.Tamagawa.Measure.Weil.IdeleClassVolume
import QuadFormsKB.Tamagawa.SphericalResidueNF

/-!
# $\tau(SO(V)) = 2$ for anisotropic $V$ of dimension $m\ge5$ from dimension $m-1$

$F$ a number field, $Q_0$ a nondegenerate form over $\mathcal O_F$ in $m = k+1$ variables with $Q = Q_0\otimes F$
**anisotropic** ($Q(\xi) = 0\Rightarrow\xi = 0$), $G = SO(V)$ with Weil's measure $\mu$ = `muTam Q₀ hQ 1`. This file carries
out Steps 2 and 4 (Weil 1982, §4.5, pp. 108–109; lattice analogue) on top of the unfolding:

* **Step 2 (Tate split).** With the $g$-twisted Poisson formula on $V_{\mathbb A}$ (`AdelicThetaPoisson`, **input**:
  $\|z\|^m\sum_{\xi\in V(F)}\Phi(z\,g^{-1}\xi) = \sum_{\xi}\hat\Phi(z^{-1}g^{-1}\xi)$) and anisotropy
  ($V(F) = \{0\}\sqcup\{Q\ne0\}$), the part $\|z\|\le1$ of the inner integral of $Z^+$ is
  $$\Phi(0)\frac{\rho_F}{m+2s} + \mathrm{lo}(g, s) = \hat\Phi(0)\frac{\rho_F}{2s} + J(g, s),\qquad
    0\le J(g,s)\le\mathrm{inner}_{\hat\Phi}(g, 1)$$
  (`lo_add_eq`, `J_le_inner`), using $\operatorname{vol}(F^\times\backslash\mathbb A^1) = \rho_F$ in the form
  `lintegral_ideleFD_norm` and the inversion invariance of the idele measure.
* **Step 4 (finiteness by positivity, exhaustion).** `measure_fundamentalDomain_lt_top`: if $Z^+(s_0) < \infty$ for one
  $s_0 > 0$ with $2s_0\Phi(0) < m\hat\Phi(0)$, then $\operatorname{vol}(SO(V)(F)\backslash SO(V)(\mathbb A)) < \infty$. No decay
  estimate and no reduction theory: integrate over $E\subseteq D$ with $\mu(E) < \infty$ and exhaust.
* **The residue.** `tendsto_mul_adelicZetaPlus`: then $sZ^+(s)\to\operatorname{vol}\cdot\rho_F\hat\Phi(0)/2$ as $s\to0^+$ (the
  outer terms are bounded by $Z^+_\Phi(1) + Z^+_{\hat\Phi}(1)$, monotonicity only).
* **The comparison.** **`tamagawaNumberTwoAdelic_of_anisotropic`**: with the fibration, the induction hypothesis
  (`AdelicComplementTauTwo`, dimension $m-1$), the identification of the adelic spherical integrals with the Euler
  products (`AdelicSphericalEuler`, **input**) and their vanishing at non-represented classes (`NonrepresentedVanish`,
  **input**), the multiplicative residue gives $sZ^+(s)\to\rho_F\hat\Phi(0)$, hence **$\tau(SO(V)) = 2$**.
* **The induction.** `anisotropicTauTwo_of_inputs`: from the base case $m = 4$ (`AnisotropicTauTwo F 4`, input) and the
  per-dimension inputs (`AdelicStepInputs`), $\tau = 2$ for every anisotropic form of dimension $\ge5$ over $F$.

The factor bookkeeping is Weil's: $Z^+(s) = \sum_\rho Z(s,\rho)$ (no $\frac12$ left), and the residue of $Z^+$ is
$\rho_F\tau\hat\Phi(0)/2$ (Weil p. 109: "the residue of $Z(s)$ at $s = 0$ turns out to be $\rho_k\tau(G)/2$").
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure QuadFormsKB.SphericalZeta
  QuadFormsKB.SphericalNF QuadFormsKB.GlobalZeta QuadFormsKB.Siegel

variable {F : Type} [Field F] [NumberField F]

/-! ### Integrals over $\mathbb A^\times/F^\times$ of functions of the norm -/

theorem ideleNorm_diag_mul (l : diagUnitsSub F) (z : (Adeles F)ˣ) :
    ideleNorm F ((l : (Adeles F)ˣ) * z) = ideleNorm F z := by
  obtain ⟨_, a, rfl⟩ := l
  simp only [ideleNorm_mul, ideleNorm_diagUnits, one_mul]

theorem tsum_ideleWeight'_diag (z : (Adeles F)ˣ) :
    ∑' l : diagUnitsSub F, ideleWeight' ((l : (Adeles F)ˣ) * z) = 1 := by
  rw [← (unitsEquivDiag (F := F)).tsum_eq]
  exact tsum_ideleWeight' z

/-- **Integrals of functions of the norm over a fundamental domain of $F^\times$** (Weil 1982, Thm 3.1.1 (iii), p. 41,
for $D = k$; $\operatorname{vol}(F^\times\backslash\mathbb A^1) = \rho_F$): for every fundamental domain $D_M$ of
$F^\times$ in $\mathbb A^\times$ and measurable $h\ge0$,
$$\int_{D_M}h(\|z\|)\,d\nu(z) = \rho_F\int_{\mathbb R}h(e^t)\,dt.$$ -/
@[kb "weil1982" "Thm 3.1.1 (iii), p. 41 (D = k: vol(𝔸^1/k^×) = ρ_k); §2.1.3, pp. 12–13 (dt/t)"]
theorem lintegral_ideleFD_norm {DM : Set (Adeles F)ˣ} (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F))
    {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ z in DM, h (ideleNorm F z) ∂tamIdeles F =
      ENNReal.ofReal (dedekindZeta_residue F) * ∫⁻ t, h (Real.exp t) := by
  have hf : Measurable fun g : (Adeles F)ˣ => ideleWeight' g * h (ideleNorm F g) :=
    measurable_ideleWeight'.mul (hh.comp continuous_ideleNorm.measurable)
  have h1 : ∀ z : (Adeles F)ˣ, h (ideleNorm F z) =
      ∑' l : diagUnitsSub F, ideleWeight' (l • z) * h (ideleNorm F (l • z)) := by
    intro z
    have : ∀ l : diagUnitsSub F, ideleWeight' (l • z) * h (ideleNorm F (l • z)) =
        ideleWeight' ((l : (Adeles F)ˣ) * z) * h (ideleNorm F z) := fun l => by
      rw [Subgroup.smul_def, smul_eq_mul, ideleNorm_diag_mul]
    rw [tsum_congr this, ENNReal.tsum_mul_right, tsum_ideleWeight'_diag, one_mul]
  rw [lintegral_congr fun z => h1 z, lintegral_quotient_eq hDM hf]
  have he : ((ideleSplit F) : (Adeles F)ˣ → ideleOne F × Multiplicative ℝ) =
      (ideleSplit F).toHomeomorph.toMeasurableEquiv := rfl
  have hmeas : Measurable fun p : ideleOne F × Multiplicative ℝ =>
      ideleWeight' ((ideleSplit F).symm p) * h (ideleNorm F ((ideleSplit F).symm p)) :=
    hf.comp (ideleSplit F).symm.continuous.measurable
  have h2 : ∫⁻ g, ideleWeight' g * h (ideleNorm F g) ∂tamIdeles F =
      ∫⁻ p, ideleWeight' ((ideleSplit F).symm p) * h (ideleNorm F ((ideleSplit F).symm p))
        ∂(tamIdeles F).map (ideleSplit F) := by
    rw [he, lintegral_map_equiv]
    refine lintegral_congr fun g => ?_
    change _ = ideleWeight' ((ideleSplit F).symm (ideleSplit F g)) *
      h (ideleNorm F ((ideleSplit F).symm (ideleSplit F g)))
    rw [(ideleSplit F).symm_apply_apply]
  rw [h2, map_ideleSplit_tamIdeles, lintegral_prod_symm _ hmeas.aemeasurable]
  have h3 : ∀ t : Multiplicative ℝ, ∫⁻ a, ideleWeight' ((ideleSplit F).symm (a, t)) *
      h (ideleNorm F ((ideleSplit F).symm (a, t))) ∂muIdeleOne F =
      h (Real.exp (Multiplicative.toAdd t)) * ENNReal.ofReal (dedekindZeta_residue F) := by
    intro t
    have hval : ∀ a : ideleOne F, ideleWeight' ((ideleSplit F).symm (a, t)) *
        h (ideleNorm F ((ideleSplit F).symm (a, t))) =
        ideleWeight' ((a : (Adeles F)ˣ) * normSectionHom F t) * h (Real.exp (Multiplicative.toAdd t)) := by
      intro a
      rw [ideleSplit_symm_apply, ideleNorm_mul, mem_ideleOne.mp a.2, one_mul, ideleNorm_normSectionHom]
    have hm : Measurable fun a : ideleOne F => ideleWeight' ((a : (Adeles F)ˣ) * normSectionHom F t) :=
      measurable_ideleWeight'.comp ((continuous_subtype_val.mul continuous_const).measurable)
    rw [lintegral_congr hval, lintegral_mul_const _ hm, lintegral_ideleWeight'_mul,
      ← muIdeleClass_univ isFundamentalDomain_ideleClassFD, muIdeleClass_univ_eq_residue, mul_comm]
  rw [lintegral_congr h3]
  have hmt : Measurable (Multiplicative.toAdd : Multiplicative ℝ → ℝ) := fun _ hs => hs
  have hm2 : Measurable fun t : Multiplicative ℝ => h (Real.exp (Multiplicative.toAdd t)) :=
    hh.comp (Real.measurable_exp.comp hmt)
  rw [lintegral_mul_const _ hm2, mul_comm]
  congr 1
  rw [dtt, lintegral_map hm2 (show Measurable (Multiplicative.ofAdd : ℝ → Multiplicative ℝ) from fun _ hs => hs)]
  rfl

/-- $\int_{D_M,\ \|z\|\le1}\|z\|^a\,d\nu(z) = \rho_F/a$ for $a > 0$. -/
theorem lintegral_ideleFD_le_one_rpow {DM : Set (Adeles F)ˣ}
    (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F)) {a : ℝ} (ha : 0 < a) :
    ∫⁻ z in DM, (Iic (1 : ℝ)).indicator (fun t => ENNReal.ofReal (t ^ a)) (ideleNorm F z) ∂tamIdeles F =
      ENNReal.ofReal (dedekindZeta_residue F / a) := by
  have hm : Measurable ((Iic (1 : ℝ)).indicator fun t => ENNReal.ofReal (t ^ a)) :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const a)).indicator measurableSet_Iic
  rw [lintegral_ideleFD_norm hDM hm]
  have hpt : ∀ t : ℝ, (Iic (1 : ℝ)).indicator (fun t => ENNReal.ofReal (t ^ a)) (Real.exp t) =
      (Iic (0 : ℝ)).indicator (fun t => ENNReal.ofReal (Real.exp (a * t))) t := by
    intro t
    by_cases ht : t ≤ 0
    · rw [indicator_of_mem (show Real.exp t ∈ Iic (1 : ℝ) from Real.exp_le_one_iff.mpr ht),
        indicator_of_mem (show t ∈ Iic (0 : ℝ) from ht), ← Real.exp_mul, mul_comm]
    · rw [indicator_of_notMem (show Real.exp t ∉ Iic (1 : ℝ) from fun h => ht (Real.exp_le_one_iff.mp h)),
        indicator_of_notMem (show t ∉ Iic (0 : ℝ) from ht)]
  rw [lintegral_congr hpt, lintegral_indicator measurableSet_Iic,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Iic ha 0)
      (Eventually.of_forall fun t => (Real.exp_pos _).le),
    integral_exp_mul_Iic ha 0, mul_zero, Real.exp_zero, ← ENNReal.ofReal_mul (dedekindZeta_residue_pos F).le]
  congr 1
  ring

/-- The idele measure is inversion invariant. -/
instance : (tamIdeles F).IsInvInvariant := by
  haveI : (tamIdeles F).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  exact Measure.IsHaarMeasure.isInvInvariant_of_regular _

/-! ### Anisotropy and the theta sum -/

variable {n : ℕ}

/-- **$Q$ is anisotropic over $F$**: $Q(\xi) = 0$ only for $\xi = 0$. -/
def AnisotropicF (Q₀ : QuadForm (𝓞 F) n) : Prop := ∀ ξ : Fin n → F, qF Q₀ ξ = 0 → ξ = 0

/-- $g\cdot0 = 0$. -/
theorem soAdele_smul_zero (Q₀ : QuadForm (𝓞 F) n) (g : SOAdele Q₀) : g • (0 : AdeleSpace F (Fin n)) = 0 := by
  have := smul_smul_adele Q₀ g 0 0
  simpa using this

open Classical in
/-- The theta sum over $Q(\xi)\ne0$: $\theta(g, z) = \sum_{Q(\xi)\ne0}\Phi(z\,g^{-1}\xi)$. -/
def thetaNZ (Q₀ : QuadForm (𝓞 F) n) (Φ : AdeleSpace F (Fin n) → ℝ≥0∞) (g : SOAdele Q₀) (z : (Adeles F)ˣ) : ℝ≥0∞ :=
  ∑' ξ : Fin n → F, (if qF Q₀ ξ ≠ 0 then Φ (z • g⁻¹ • diagVec F (Fin n) ξ) else 0)

theorem measurable_thetaNZ (Q₀ : QuadForm (𝓞 F) n) {Φ : AdeleSpace F (Fin n) → ℝ≥0∞} (hΦ : Measurable Φ)
    (g : SOAdele Q₀) : Measurable (thetaNZ Q₀ Φ g) := by
  refine Measurable.ennreal_tsum fun ξ => ?_
  split_ifs
  · exact hΦ.comp (measurable_units_smul.comp (measurable_id.prodMk measurable_const))
  · exact measurable_const

/-- For anisotropic $Q$: $\sum_{\xi\in V(F)}\Phi(z\,g^{-1}\xi) = \Phi(0) + \theta(g, z)$. -/
theorem tsum_theta_eq {Q₀ : QuadForm (𝓞 F) n} (haniso : AnisotropicF Q₀) (Φ : AdeleSpace F (Fin n) → ℝ≥0∞)
    (g : SOAdele Q₀) (z : (Adeles F)ˣ) :
    ∑' ξ : Fin n → F, Φ (z • g⁻¹ • diagVec F (Fin n) ξ) = Φ 0 + thetaNZ Q₀ Φ g z := by
  classical
  rw [ENNReal.tsum_eq_add_tsum_ite (0 : Fin n → F), map_zero, soAdele_smul_zero, smul_zero, thetaNZ]
  congr 1
  refine tsum_congr fun ξ => ?_
  by_cases h : ξ = 0
  · subst h
    have h0 : qF Q₀ 0 = 0 := by simpa using qF_smul Q₀ 0 0
    simp [h0]
  · have hq : qF Q₀ ξ ≠ 0 := fun hq => h (haniso ξ hq)
    rw [if_neg h, if_pos hq]

/-- $\theta(g,\lambda z) = \theta(g, z)$ for $\lambda\in F^\times$. -/
theorem thetaNZ_diag_mul (Q₀ : QuadForm (𝓞 F) n) (Φ : AdeleSpace F (Fin n) → ℝ≥0∞) (g : SOAdele Q₀)
    (l : diagUnitsSub F) (z : (Adeles F)ˣ) : thetaNZ Q₀ Φ g ((l : (Adeles F)ˣ) * z) = thetaNZ Q₀ Φ g z := by
  classical
  obtain ⟨_, a, rfl⟩ := l
  rw [thetaNZ, thetaNZ]
  conv_rhs => rw [← (MulAction.toPerm a : Equiv.Perm (Fin n → F)).tsum_eq]
  refine tsum_congr fun ξ => ?_
  have hq : qF Q₀ ((a : F) • ξ) ≠ 0 ↔ qF Q₀ ξ ≠ 0 := by
    rw [qF_smul]; simp [a.ne_zero]
  show (if qF Q₀ ξ ≠ 0 then Φ ((diagUnits F a * z) • g⁻¹ • diagVec F (Fin n) ξ) else 0) =
    (if qF Q₀ ((a : F) • ξ) ≠ 0 then Φ (z • g⁻¹ • diagVec F (Fin n) ((a : F) • ξ)) else 0)
  rw [diagVec_units_smul, smul_units_comm, smul_smul, mul_comm z]
  exact if_congr hq.symm rfl rfl

/-! ### Step 2: the Tate split -/

/-- **The $g$-twisted Poisson formula on $V_{\mathbb A}$** (**input**; Weil 1982, §4.4, p. 95 / Thm 2.2.? [unverified]; Step 2):
for every $g\in SO(V)(\mathbb A)$ and idele $z$,
$$\|z\|^n\sum_{\xi\in V(F)}\Phi(z\,g^{-1}\xi) = \sum_{\xi\in V(F)}\hat\Phi(z^{-1}g^{-1}\xi).$$
This is Poisson summation for the lattice $V(F)\subset V_{\mathbb A}$ and the automorphism $A = z\,g^{-1}$
($|\det A| = \|z\|^n$, and the $B_Q$-adjoint of $g^{-1}$ is $g$, so $A^{*-1} = z^{-1}g^{-1}$), with $\hat\Phi$ the Fourier
transform for $\psi(B_Q(x, y))$ and the $B_Q$-self-dual measure. Fields: `poisson`. -/
@[kb "weil1982" "§4.5, p. 108–109 (Poisson formula on X_A applied to Φ(z g⁻¹ ·)) [unverified page]"]
structure AdelicThetaPoisson (Q₀ : QuadForm (𝓞 F) n) (Φ Φh : AdeleSpace F (Fin n) → ℝ≥0∞) : Prop where
  /-- The twisted Poisson formula. -/
  poisson : ∀ (g : SOAdele Q₀) (z : (Adeles F)ˣ),
    ENNReal.ofReal (ideleNorm F z ^ (n : ℝ)) * ∑' ξ : Fin n → F, Φ (z • g⁻¹ • diagVec F (Fin n) ξ) =
      ∑' ξ : Fin n → F, Φh (z⁻¹ • g⁻¹ • diagVec F (Fin n) ξ)

/-- **Pointwise Tate split**: $\|z\|^{n+2s}(\Phi(0) + \theta_\Phi(g,z)) = \|z\|^{2s}(\hat\Phi(0) + \theta_{\hat\Phi}(g,z^{-1}))$. -/
theorem zetaWeight_mul_theta {Q₀ : QuadForm (𝓞 F) n} (haniso : AnisotropicF Q₀) {Φ Φh : AdeleSpace F (Fin n) → ℝ≥0∞}
    (hP : AdelicThetaPoisson Q₀ Φ Φh) (s : ℝ) (g : SOAdele Q₀) (z : (Adeles F)ˣ) :
    zetaWeight s n z * (Φ 0 + thetaNZ Q₀ Φ g z) =
      ENNReal.ofReal (ideleNorm F z ^ (2 * s)) * (Φh 0 + thetaNZ Q₀ Φh g z⁻¹) := by
  rw [← tsum_theta_eq haniso, ← tsum_theta_eq haniso, ← hP.poisson g z, zetaWeight,
    show (n : ℝ) + 2 * s = 2 * s + n by ring, Real.rpow_add (ideleNorm_pos z),
    ENNReal.ofReal_mul (Real.rpow_nonneg (ideleNorm_pos z).le _), mul_assoc]

variable {Q₀ : QuadForm (𝓞 F) n} {DM : Set (Adeles F)ˣ}

/-- The set $\{\|z\|\le1\}$. -/
def normLeOne (F : Type) [Field F] [NumberField F] : Set (Adeles F)ˣ := {z | ideleNorm F z ≤ 1}

theorem measurableSet_normLeOne : MeasurableSet (normLeOne F) :=
  measurableSet_le continuous_ideleNorm.measurable measurable_const

/-- The part $\|z\|\le1$ of the inner integral. -/
def loInner (Q₀ : QuadForm (𝓞 F) n) (Φ : AdeleSpace F (Fin n) → ℝ≥0∞) (DM : Set (Adeles F)ˣ) (s : ℝ)
    (g : SOAdele Q₀) : ℝ≥0∞ :=
  ∫⁻ z in DM, (normLeOne F).indicator (fun z => zetaWeight s n z * thetaNZ Q₀ Φ g z) z ∂tamIdeles F

/-- The part $\|z\| > 1$ of the inner integral. -/
def hiInner (Q₀ : QuadForm (𝓞 F) n) (Φ : AdeleSpace F (Fin n) → ℝ≥0∞) (DM : Set (Adeles F)ˣ) (s : ℝ)
    (g : SOAdele Q₀) : ℝ≥0∞ :=
  ∫⁻ z in DM, (normLeOne F)ᶜ.indicator (fun z => zetaWeight s n z * thetaNZ Q₀ Φ g z) z ∂tamIdeles F

/-- The dual remainder $J(g,s) = \int_{D_M,\ \|z\|\le1}\|z\|^{2s}\theta_{\hat\Phi}(g, z^{-1})\,d\nu$. -/
def dualRem (Q₀ : QuadForm (𝓞 F) n) (Φh : AdeleSpace F (Fin n) → ℝ≥0∞) (DM : Set (Adeles F)ˣ) (s : ℝ)
    (g : SOAdele Q₀) : ℝ≥0∞ :=
  ∫⁻ z in DM, (normLeOne F).indicator
    (fun z => ENNReal.ofReal (ideleNorm F z ^ (2 * s)) * thetaNZ Q₀ Φh g z⁻¹) z ∂tamIdeles F

theorem adelicInner_eq_lo_add_hi {Φ : AdeleSpace F (Fin n) → ℝ≥0∞} (hΦ : Measurable Φ) (s : ℝ) (g : SOAdele Q₀) :
    adelicInner Q₀ Φ DM s g = loInner Q₀ Φ DM s g + hiInner Q₀ Φ DM s g := by
  have hm : Measurable fun z => (normLeOne F).indicator (fun z => zetaWeight s n z * thetaNZ Q₀ Φ g z) z :=
    ((measurable_zetaWeight s n).mul (measurable_thetaNZ Q₀ hΦ g)).indicator measurableSet_normLeOne
  rw [adelicInner, loInner, hiInner]
  refine (lintegral_congr fun z => ?_).trans (lintegral_add_left hm _)
  rw [indicator_self_add_compl_apply]
  rfl

theorem indicator_rpow_eq (a : ℝ) (z : (Adeles F)ˣ) :
    (normLeOne F).indicator (fun z => ENNReal.ofReal (ideleNorm F z ^ a)) z =
      (Iic (1 : ℝ)).indicator (fun t => ENNReal.ofReal (t ^ a)) (ideleNorm F z) := by
  by_cases h : ideleNorm F z ≤ 1
  · rw [indicator_of_mem (show z ∈ normLeOne F from h), indicator_of_mem (show ideleNorm F z ∈ Iic 1 from h)]
  · rw [indicator_of_notMem (show z ∉ normLeOne F from h), indicator_of_notMem (show ideleNorm F z ∉ Iic 1 from h)]

/-- **The Tate split of the part $\|z\|\le1$** (Weil 1982, §4.5, p. 109, (5)): for $s > 0$,
$$\Phi(0)\frac{\rho_F}{n+2s} + \mathrm{lo}(g,s) = \hat\Phi(0)\frac{\rho_F}{2s} + J(g,s).$$ -/
@[kb "weil1982" "§4.5, p. 109 (split of ∫_{|z|≤1} by Poisson; residue terms)"]
theorem lo_add_eq (haniso : AnisotropicF Q₀) {Φ Φh : AdeleSpace F (Fin n) → ℝ≥0∞} (hΦ : Measurable Φ)
    (hΦh : Measurable Φh) (hP : AdelicThetaPoisson Q₀ Φ Φh)
    (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F)) {s : ℝ} (hs : 0 < s) (g : SOAdele Q₀) :
    Φ 0 * ENNReal.ofReal (dedekindZeta_residue F / (n + 2 * s)) + loInner Q₀ Φ DM s g =
      Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s)) + dualRem Q₀ Φh DM s g := by
  have hw := lintegral_ideleFD_le_one_rpow hDM (a := n + 2 * s) (by positivity)
  have hw2 := lintegral_ideleFD_le_one_rpow hDM (a := 2 * s) (by positivity)
  simp_rw [← indicator_rpow_eq] at hw hw2
  have hmw : ∀ a : ℝ, Measurable fun z : (Adeles F)ˣ => ENNReal.ofReal (ideleNorm F z ^ a) := fun a =>
    ENNReal.measurable_ofReal.comp (continuous_ideleNorm.measurable.pow_const a)
  rw [← hw, ← hw2, ← lintegral_const_mul _ ((hmw _).indicator measurableSet_normLeOne),
    ← lintegral_const_mul _ ((hmw _).indicator measurableSet_normLeOne), loInner, dualRem]
  have hm1 : Measurable fun z => Φ 0 * (normLeOne F).indicator
      (fun z => ENNReal.ofReal (ideleNorm F z ^ ((n : ℝ) + 2 * s))) z :=
    measurable_const.mul ((hmw _).indicator measurableSet_normLeOne)
  have hm2 : Measurable fun z => Φh 0 * (normLeOne F).indicator
      (fun z => ENNReal.ofReal (ideleNorm F z ^ (2 * s))) z :=
    measurable_const.mul ((hmw _).indicator measurableSet_normLeOne)
  rw [← lintegral_add_left hm1, ← lintegral_add_left hm2]
  refine lintegral_congr fun z => ?_
  by_cases h : z ∈ normLeOne F
  · simp only [indicator_of_mem h]
    have := zetaWeight_mul_theta haniso hP s g z
    rw [mul_add, mul_add] at this
    rw [zetaWeight] at this ⊢
    rw [mul_comm (Φ 0), mul_comm (Φh 0)]
    exact this
  · simp [indicator_of_notMem h]

/-- The inversion carries a fundamental domain of $F^\times$ to one. -/
theorem isFundamentalDomain_inv_preimage (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F)) :
    IsFundamentalDomain (diagUnitsSub F) (Inv.inv ⁻¹' DM) (tamIdeles F) := by
  refine hDM.preimage_of_equiv (Measure.measurePreserving_inv (tamIdeles F)).quasiMeasurePreserving
    (e := fun l => l⁻¹) inv_involutive.bijective fun l z => ?_
  show ((l⁻¹ : diagUnitsSub F) • z)⁻¹ = l • z⁻¹
  rw [Subgroup.smul_def, Subgroup.smul_def, smul_eq_mul, smul_eq_mul, mul_inv_rev, Subgroup.coe_inv, inv_inv,
    mul_comm]

/-- **$J(g, s)\le\mathrm{inner}_{\hat\Phi}(g, 1)$** for $s\ge0$ (inversion $z\mapsto z^{-1}$ and independence of the
fundamental domain). -/
theorem dualRem_le_adelicInner {Φh : AdeleSpace F (Fin n) → ℝ≥0∞} (hΦh : Measurable Φh)
    (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F)) {s : ℝ} (hs : 0 ≤ s) (g : SOAdele Q₀) :
    dualRem Q₀ Φh DM s g ≤ adelicInner Q₀ Φh DM 1 g := by
  have hSm : MeasurableSet {z : (Adeles F)ˣ | 1 ≤ ideleNorm F z} :=
    measurableSet_le measurable_const continuous_ideleNorm.measurable
  have h1 : dualRem Q₀ Φh DM s g ≤
      ∫⁻ z in DM, {z : (Adeles F)ˣ | 1 ≤ ideleNorm F z}.indicator (thetaNZ Q₀ Φh g) z⁻¹ ∂tamIdeles F := by
    refine lintegral_mono fun z => ?_
    by_cases h : z ∈ normLeOne F
    · rw [indicator_of_mem h]
      have hz : 1 ≤ ideleNorm F z⁻¹ := by
        rw [ideleNorm_inv]; exact (one_le_inv₀ (ideleNorm_pos z)).mpr h
      rw [indicator_of_mem (show z⁻¹ ∈ {z : (Adeles F)ˣ | 1 ≤ ideleNorm F z} from hz)]
      calc ENNReal.ofReal (ideleNorm F z ^ (2 * s)) * thetaNZ Q₀ Φh g z⁻¹ ≤ 1 * thetaNZ Q₀ Φh g z⁻¹ := by
            gcongr
            exact ENNReal.ofReal_le_one.mpr (Real.rpow_le_one (ideleNorm_pos z).le h (by positivity))
        _ = _ := one_mul _
    · rw [indicator_of_notMem h]; exact zero_le
  have h2 : ∫⁻ z in DM, {z : (Adeles F)ˣ | 1 ≤ ideleNorm F z}.indicator (thetaNZ Q₀ Φh g) z⁻¹ ∂tamIdeles F =
      ∫⁻ z in Inv.inv ⁻¹' DM, {z : (Adeles F)ˣ | 1 ≤ ideleNorm F z}.indicator (thetaNZ Q₀ Φh g) z
        ∂tamIdeles F := by
    have := (Measure.measurePreserving_inv (tamIdeles F)).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.inv (Adeles F)ˣ).measurableEmbedding
      ({z : (Adeles F)ˣ | 1 ≤ ideleNorm F z}.indicator (thetaNZ Q₀ Φh g)) (Inv.inv ⁻¹' DM)
    simpa [preimage_preimage] using this
  have h3 : ∫⁻ z in Inv.inv ⁻¹' DM, {z : (Adeles F)ˣ | 1 ≤ ideleNorm F z}.indicator (thetaNZ Q₀ Φh g) z
        ∂tamIdeles F =
      ∫⁻ z in DM, {z : (Adeles F)ˣ | 1 ≤ ideleNorm F z}.indicator (thetaNZ Q₀ Φh g) z ∂tamIdeles F := by
    refine (isFundamentalDomain_inv_preimage hDM).setLIntegral_eq hDM _ fun l z => ?_
    simp only [Subgroup.smul_def, smul_eq_mul, indicator_apply, mem_setOf_eq, ideleNorm_diag_mul,
      thetaNZ_diag_mul]
  have h4 : ∫⁻ z in DM, {z : (Adeles F)ˣ | 1 ≤ ideleNorm F z}.indicator (thetaNZ Q₀ Φh g) z ∂tamIdeles F ≤
      adelicInner Q₀ Φh DM 1 g := by
    refine lintegral_mono fun z => ?_
    by_cases h : 1 ≤ ideleNorm F z
    · rw [indicator_of_mem (show z ∈ {z : (Adeles F)ˣ | 1 ≤ ideleNorm F z} from h)]
      calc thetaNZ Q₀ Φh g z = 1 * thetaNZ Q₀ Φh g z := (one_mul _).symm
        _ ≤ zetaWeight 1 n z * thetaNZ Q₀ Φh g z := by
            gcongr
            exact ENNReal.one_le_ofReal.mpr (Real.one_le_rpow h (by positivity))
    · rw [indicator_of_notMem (show z ∉ {z : (Adeles F)ˣ | 1 ≤ ideleNorm F z} from h)]; exact zero_le
  exact h1.trans (h2.le.trans (h3.le.trans h4))

/-- **$\mathrm{hi}(g, s)\le\mathrm{inner}(g, 1)$** for $s\le1$ ($\|z\|^{n+2s}\le\|z\|^{n+2}$ on $\|z\|>1$). -/
theorem hiInner_le {Φ : AdeleSpace F (Fin n) → ℝ≥0∞} {s : ℝ} (hs : s ≤ 1) (g : SOAdele Q₀) :
    hiInner Q₀ Φ DM s g ≤ adelicInner Q₀ Φ DM 1 g := by
  refine lintegral_mono fun z => ?_
  by_cases h : z ∈ (normLeOne F)ᶜ
  · rw [indicator_of_mem h]
    have h1 : 1 ≤ ideleNorm F z := le_of_lt (not_le.mp h)
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le h1 (by linarith))) le_rfl
  · rw [indicator_of_notMem h]; exact zero_le

theorem loInner_le_adelicInner {Φ : AdeleSpace F (Fin n) → ℝ≥0∞} (hΦ : Measurable Φ) (s : ℝ) (g : SOAdele Q₀) :
    loInner Q₀ Φ DM s g ≤ adelicInner Q₀ Φ DM s g := by
  rw [adelicInner_eq_lo_add_hi hΦ]; exact le_self_add

/-! ### Step 4: finiteness by positivity -/

section Global

variable {hQ : Q₀.Nondegenerate} {D : Set (SOAdele Q₀)}

/-- The $E$-form of the Step 4 inequality: for every $E\subseteq D$ and $s > 0$,
$\mu(E)\,\hat\Phi(0)\frac{\rho_F}{2s}\le\mu(E)\,\Phi(0)\frac{\rho_F}{n+2s} + Z^+(s)$. -/
theorem measure_mul_le_of_subset (haniso : AnisotropicF Q₀) {Φ Φh : AdeleSpace F (Fin n) → ℝ≥0∞}
    (hΦ : Measurable Φ) (hΦh : Measurable Φh) (hP : AdelicThetaPoisson Q₀ Φ Φh)
    (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F)) {s : ℝ} (hs : 0 < s) {E : Set (SOAdele Q₀)}
    (hE : E ⊆ D) :
    muTam Q₀ hQ 1 E * (Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s))) ≤
      muTam Q₀ hQ 1 E * (Φ 0 * ENNReal.ofReal (dedekindZeta_residue F / (n + 2 * s))) +
        adelicZetaPlus Q₀ hQ Φ D DM s := by
  set μ := muTam Q₀ hQ 1
  calc μ E * (Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s)))
      = ∫⁻ _ in E, Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s)) ∂μ := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ g in E, (Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s)) + dualRem Q₀ Φh DM s g) ∂μ :=
        lintegral_mono fun g => le_self_add
    _ = ∫⁻ g in E, (Φ 0 * ENNReal.ofReal (dedekindZeta_residue F / (n + 2 * s)) + loInner Q₀ Φ DM s g) ∂μ :=
        lintegral_congr fun g => (lo_add_eq haniso hΦ hΦh hP hDM hs g).symm
    _ = μ E * (Φ 0 * ENNReal.ofReal (dedekindZeta_residue F / (n + 2 * s))) + ∫⁻ g in E, loInner Q₀ Φ DM s g ∂μ := by
        rw [lintegral_add_left measurable_const, setLIntegral_const, mul_comm]
    _ ≤ _ := by
        gcongr
        exact (lintegral_mono fun g => loInner_le_adelicInner hΦ s g).trans (lintegral_mono_set hE)

/-- **Step 4: $\operatorname{vol}(SO(V)(F)\backslash SO(V)(\mathbb A)) < \infty$ by positivity** (no decay
estimates, no reduction theory): for anisotropic $Q$, if $\Phi(0) = a\ge0$, $\hat\Phi(0) = b > 0$ and
$Z^+(s_0) < \infty$ for one $s_0 > 0$ with $2s_0a < nb$, then $\mu(D) < \infty$. -/
@[kb "weil1982" "§4.5, p. 109 (finiteness of τ(G) from the convergence of Z⁺)"]
theorem measure_fundamentalDomain_lt_top (haniso : AnisotropicF Q₀) {Φ Φh : AdeleSpace F (Fin n) → ℝ≥0∞}
    (hΦ : Measurable Φ) (hΦh : Measurable Φh) (hP : AdelicThetaPoisson Q₀ Φ Φh)
    (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hΦ0 : Φ 0 = ENNReal.ofReal a) (hΦh0 : Φh 0 = ENNReal.ofReal b) {s₀ : ℝ} (hs₀ : 0 < s₀)
    (hsb : 2 * s₀ * a < n * b) (hfin : adelicZetaPlus Q₀ hQ Φ D DM s₀ ≠ ⊤) :
    muTam Q₀ hQ 1 D < ⊤ := by
  have hρ := dedekindZeta_residue_pos F
  have key := fun (E : Set (SOAdele Q₀)) (hE : E ⊆ D) =>
    measure_mul_le_of_subset (hQ := hQ) haniso hΦ hΦh hP hDM hs₀ hE
  have hn0 : (0 : ℝ) < n + 2 * s₀ := by positivity
  have hAeq : Φ 0 * ENNReal.ofReal (dedekindZeta_residue F / (n + 2 * s₀)) =
      ENNReal.ofReal (a * (dedekindZeta_residue F / (n + 2 * s₀))) := by
    rw [hΦ0, ← ENNReal.ofReal_mul ha]
  have hBeq : Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s₀)) =
      ENNReal.ofReal (b * (dedekindZeta_residue F / (2 * s₀))) := by
    rw [hΦh0, ← ENNReal.ofReal_mul hb.le]
  generalize hA : Φ 0 * ENNReal.ofReal (dedekindZeta_residue F / (n + 2 * s₀)) = A at key hAeq
  generalize hB : Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s₀)) = B at key hBeq
  generalize hZ : adelicZetaPlus Q₀ hQ Φ D DM s₀ = Z at key hfin
  have hAB : A < B := by
    rw [hAeq, hBeq, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    rw [mul_div_assoc', mul_div_assoc', div_lt_div_iff₀ hn0 (by positivity)]
    have h1 : a * (2 * s₀) < b * (n + 2 * s₀) := by nlinarith [mul_pos hb hs₀]
    nlinarith [mul_lt_mul_of_pos_left h1 hρ]
  have hAt : A ≠ ⊤ := by rw [hAeq]; exact ENNReal.ofReal_ne_top
  have hBA : B - A ≠ 0 := (tsub_pos_of_lt hAB).ne'
  have hbound : ∀ E ⊆ D, muTam Q₀ hQ 1 E < ⊤ → muTam Q₀ hQ 1 E ≤ Z / (B - A) := by
    intro E hE hEt
    have k1 := key E hE
    have hsplit : muTam Q₀ hQ 1 E * B = muTam Q₀ hQ 1 E * A + muTam Q₀ hQ 1 E * (B - A) := by
      rw [← mul_add, add_tsub_cancel_of_le hAB.le]
    rw [hsplit] at k1
    have k2 : muTam Q₀ hQ 1 E * (B - A) ≤ Z :=
      (ENNReal.add_le_add_iff_left (ENNReal.mul_ne_top hEt.ne hAt)).mp k1
    exact (ENNReal.le_div_iff_mul_le (Or.inl hBA) (Or.inr hfin)).mpr k2
  have hU : D = ⋃ i, D ∩ spanningSets (muTam Q₀ hQ 1) i := by
    rw [← inter_iUnion, iUnion_spanningSets, inter_univ]
  have hmono : Monotone fun i => D ∩ spanningSets (muTam Q₀ hQ 1) i := fun i j hij =>
    inter_subset_inter_right _ (monotone_spanningSets _ hij)
  have hle : muTam Q₀ hQ 1 D ≤ Z / (B - A) := by
    rw [hU, hmono.measure_iUnion]
    exact iSup_le fun i => hbound _ inter_subset_left
      ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top _ i))
  exact hle.trans_lt (ENNReal.div_lt_top hfin hBA)

/-! ### The residue of $Z^+$ -/

/-- **$\lim_{s\to0^+}sZ^+(s) = \operatorname{vol}\cdot\rho_F\hat\Phi(0)/2$** once the volume is finite (Step 4;
Weil 1982, §4.5, p. 109): the outer terms are bounded by $Z^+_\Phi(1) + Z^+_{\hat\Phi}(1)$ (monotonicity only). -/
@[kb "weil1982" "§4.5, p. 109 (residue of Z⁺ at s = 0 is ρ_kτ(G)Φ̂(0)/2)"]
theorem tendsto_mul_adelicZetaPlus (hn : 1 ≤ n) (haniso : AnisotropicF Q₀) {Φ Φh : AdeleSpace F (Fin n) → ℝ≥0∞}
    (hΦ : Measurable Φ) (hΦh : Measurable Φh) (hP : AdelicThetaPoisson Q₀ Φ Φh)
    (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hΦ0 : Φ 0 = ENNReal.ofReal a) (hΦh0 : Φh 0 = ENNReal.ofReal b) (hDfin : muTam Q₀ hQ 1 D ≠ ⊤)
    (hC : adelicZetaPlus Q₀ hQ Φh D DM 1 + adelicZetaPlus Q₀ hQ Φ D DM 1 ≠ ⊤)
    (hmeas : Measurable (adelicInner Q₀ Φh DM 1)) :
    Tendsto (fun s => s * (adelicZetaPlus Q₀ hQ Φ D DM s).toReal) (𝓝[>] 0)
      (𝓝 ((muTam Q₀ hQ 1 D).toReal * (dedekindZeta_residue F * b) / 2)) := by
  have hρ := dedekindZeta_residue_pos F
  have hlow : ∀ s, 0 < s → muTam Q₀ hQ 1 D * (Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s))) ≤
      adelicZetaPlus Q₀ hQ Φ D DM s +
        muTam Q₀ hQ 1 D * (Φ 0 * ENNReal.ofReal (dedekindZeta_residue F / (n + 2 * s))) := fun s hs => by
    rw [add_comm]; exact measure_mul_le_of_subset haniso hΦ hΦh hP hDM hs subset_rfl
  have hup : ∀ s, 0 < s → s ≤ 1 → adelicZetaPlus Q₀ hQ Φ D DM s ≤
      muTam Q₀ hQ 1 D * (Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s))) +
        (adelicZetaPlus Q₀ hQ Φh D DM 1 + adelicZetaPlus Q₀ hQ Φ D DM 1) := fun s hs hs1 => by
    rw [adelicZetaPlus_eq_lintegral_inner]
    calc ∫⁻ g in D, adelicInner Q₀ Φ DM s g ∂muTam Q₀ hQ 1
        = ∫⁻ g in D, (loInner Q₀ Φ DM s g + hiInner Q₀ Φ DM s g) ∂muTam Q₀ hQ 1 :=
          lintegral_congr fun g => adelicInner_eq_lo_add_hi hΦ s g
      _ ≤ ∫⁻ g in D, (Φ 0 * ENNReal.ofReal (dedekindZeta_residue F / (n + 2 * s)) + loInner Q₀ Φ DM s g +
          hiInner Q₀ Φ DM s g) ∂muTam Q₀ hQ 1 := lintegral_mono fun g => by gcongr; exact le_add_self
      _ = ∫⁻ g in D, (Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s)) + dualRem Q₀ Φh DM s g +
          hiInner Q₀ Φ DM s g) ∂muTam Q₀ hQ 1 :=
          lintegral_congr fun g => by rw [lo_add_eq haniso hΦ hΦh hP hDM hs g]
      _ ≤ ∫⁻ g in D, (Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s)) +
          (adelicInner Q₀ Φh DM 1 g + adelicInner Q₀ Φ DM 1 g)) ∂muTam Q₀ hQ 1 := lintegral_mono fun g => by
            rw [add_assoc]; gcongr
            · exact dualRem_le_adelicInner hΦh hDM hs.le g
            · exact hiInner_le hs1 g
      _ = muTam Q₀ hQ 1 D * (Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s))) +
          (adelicZetaPlus Q₀ hQ Φh D DM 1 + adelicZetaPlus Q₀ hQ Φ D DM 1) := by
          rw [lintegral_add_left measurable_const, setLIntegral_const, lintegral_add_left hmeas, mul_comm]
          rfl
  have hV0 : 0 ≤ (muTam Q₀ hQ 1 D).toReal := ENNReal.toReal_nonneg
  have hBr : ∀ s, 0 < s → (muTam Q₀ hQ 1 D * (Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s)))).toReal =
      (muTam Q₀ hQ 1 D).toReal * (b * (dedekindZeta_residue F / (2 * s))) := fun s hs => by
    rw [hΦh0, ← ENNReal.ofReal_mul hb.le, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hAr : ∀ s, 0 < s →
      (muTam Q₀ hQ 1 D * (Φ 0 * ENNReal.ofReal (dedekindZeta_residue F / (n + 2 * s)))).toReal =
      (muTam Q₀ hQ 1 D).toReal * (a * (dedekindZeta_residue F / (n + 2 * s))) := fun s hs => by
    rw [hΦ0, ← ENNReal.ofReal_mul ha, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hBt : ∀ s, muTam Q₀ hQ 1 D * (Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s))) ≠ ⊤ := fun s => by
    rw [hΦh0]; exact ENNReal.mul_ne_top hDfin (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have hAt : ∀ s, muTam Q₀ hQ 1 D * (Φ 0 * ENNReal.ofReal (dedekindZeta_residue F / (n + 2 * s))) ≠ ⊤ := fun s => by
    rw [hΦ0]; exact ENNReal.mul_ne_top hDfin (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have hZt : ∀ s, 0 < s → s ≤ 1 → adelicZetaPlus Q₀ hQ Φ D DM s ≠ ⊤ := fun s hs hs1 =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hBt s, hC⟩) (hup s hs hs1)
  have hupR : ∀ s, 0 < s → s ≤ 1 → s * (adelicZetaPlus Q₀ hQ Φ D DM s).toReal ≤
      (muTam Q₀ hQ 1 D).toReal * (dedekindZeta_residue F * b) / 2 +
        s * (adelicZetaPlus Q₀ hQ Φh D DM 1 + adelicZetaPlus Q₀ hQ Φ D DM 1).toReal := fun s hs hs1 => by
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hBt s, hC⟩) (hup s hs hs1)
    rw [ENNReal.toReal_add (hBt s) hC, hBr s hs] at h
    calc s * (adelicZetaPlus Q₀ hQ Φ D DM s).toReal ≤ s * ((muTam Q₀ hQ 1 D).toReal *
          (b * (dedekindZeta_residue F / (2 * s))) +
          (adelicZetaPlus Q₀ hQ Φh D DM 1 + adelicZetaPlus Q₀ hQ Φ D DM 1).toReal) := by gcongr
      _ = _ := by field_simp
  have hlowR : ∀ s, 0 < s → s ≤ 1 → (muTam Q₀ hQ 1 D).toReal * (dedekindZeta_residue F * b) / 2 -
      s * ((muTam Q₀ hQ 1 D).toReal * (a * (dedekindZeta_residue F / (n + 2 * s)))) ≤
        s * (adelicZetaPlus Q₀ hQ Φ D DM s).toReal := fun s hs hs1 => by
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hZt s hs hs1, hAt s⟩) (hlow s hs)
    rw [ENNReal.toReal_add (hZt s hs hs1) (hAt s), hBr s hs, hAr s hs] at h
    have e : (muTam Q₀ hQ 1 D).toReal * (dedekindZeta_residue F * b) / 2 =
        s * ((muTam Q₀ hQ 1 D).toReal * (b * (dedekindZeta_residue F / (2 * s)))) := by field_simp
    rw [e, ← mul_sub]
    gcongr
    linarith
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s ≤ 1 :=
    Filter.eventually_of_mem (Ioc_mem_nhdsGT zero_lt_one) fun s hs => ⟨hs.1, hs.2⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlowT : Tendsto (fun s : ℝ => (muTam Q₀ hQ 1 D).toReal * (dedekindZeta_residue F * b) / 2 -
      s * ((muTam Q₀ hQ 1 D).toReal * (a * (dedekindZeta_residue F / (n + 2 * s))))) (𝓝[>] 0)
      (𝓝 ((muTam Q₀ hQ 1 D).toReal * (dedekindZeta_residue F * b) / 2)) := by
    have hc : ContinuousAt (fun s : ℝ => (muTam Q₀ hQ 1 D).toReal * (dedekindZeta_residue F * b) / 2 -
        s * ((muTam Q₀ hQ 1 D).toReal * (a * (dedekindZeta_residue F / (n + 2 * s))))) 0 := by
      refine continuousAt_const.sub (continuousAt_id.mul (continuousAt_const.mul (continuousAt_const.mul
        (continuousAt_const.div (continuousAt_const.add (continuousAt_const.mul continuousAt_id)) ?_))))
      simp only [id, mul_zero, add_zero]; exact hnpos.ne'
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have hupT : Tendsto (fun s : ℝ => (muTam Q₀ hQ 1 D).toReal * (dedekindZeta_residue F * b) / 2 +
      s * (adelicZetaPlus Q₀ hQ Φh D DM 1 + adelicZetaPlus Q₀ hQ Φ D DM 1).toReal) (𝓝[>] 0)
      (𝓝 ((muTam Q₀ hQ 1 D).toReal * (dedekindZeta_residue F * b) / 2)) := by
    have hc : ContinuousAt (fun s : ℝ => (muTam Q₀ hQ 1 D).toReal * (dedekindZeta_residue F * b) / 2 +
        s * (adelicZetaPlus Q₀ hQ Φh D DM 1 + adelicZetaPlus Q₀ hQ Φ D DM 1).toReal) 0 := by fun_prop
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowT hupT
    (hev.mono fun s hs => hlowR s hs.1 hs.2) (hev.mono fun s hs => hupR s hs.1 hs.2)

end Global

/-! ### The comparison with the multiplicative side -/

variable {k : ℕ}

/-- **The adelic spherical integrals are the Euler products** (**input**; Weil 1982, §4.5, (1), p. 102, and p. 109):
for every represented class $c$ and $s > 0$,
$$Z(s, c) = \kappa\cdot Z^{\mathrm{NF}}(s,\rho_c)\quad(\texttt{sphericalZetaAtNF}),$$
for archimedean data $\Phi_r$ (real places), $\Psi$ (complex places) and a constant $\kappa$ (the normalization of the
measure on $\mathbb A_F^m$). It is the product decomposition of $\sigma_c$ into the local Leray measures
over the restricted product, applied to $\Phi = \Phi_\infty\otimes\mathbf 1_{\hat L}$. Field: `eq`. -/
@[kb "weil1982" "§4.5, (1), p. 102 (Z(s,ρ) as a product of local factors); p. 109"]
structure AdelicSphericalEuler {Q₀ : QuadForm (𝓞 F) (k + 1)} (S : AdelicSphereFamily Q₀)
    (Φ : AdeleSpace F (Fin (k + 1)) → ℝ≥0∞) (Φr : RealPlace F → (Fin (k + 1) → ℝ) → ℝ)
    (Ψ : ComplexPlace F → (Fin (k + 1) → ℂ) → ℝ) (κ : ℝ) : Prop where
  /-- The identification, every represented class, every $s > 0$. -/
  eq : ∀ (c : RepClasses Q₀) (s : ℝ), 0 < s →
    adelicSphZeta (S.data c) Φ s = ENNReal.ofReal (κ * sphericalZetaAtNF Q₀ Φr Ψ (repρ c) s)

/-- **The Euler product vanishes at the classes not represented over $F$** (**input**; Hasse–Minkowski: a class not
represented over $F$ is not represented at some place, where the local factor is $0$). Field: `vanish`. -/
@[kb "omeara1963" "§66, 66:1, p. 187 (Hasse–Minkowski)"]
structure NonrepresentedVanish (Q₀ : QuadForm (𝓞 F) (k + 1)) (Φr : RealPlace F → (Fin (k + 1) → ℝ) → ℝ)
    (Ψ : ComplexPlace F → (Fin (k + 1) → ℂ) → ℝ) : Prop where
  /-- The vanishing. -/
  vanish : ∀ c : SqClasses F, (¬ ∃ η : Fin (k + 1) → F, qF Q₀ η = ((Quotient.out c : Fˣ) : F)) →
    ∀ s : ℝ, 0 < s → sphericalZetaAtNF Q₀ Φr Ψ ((Quotient.out c : Fˣ) : F) s = 0

/-- **The data and inputs of Weil's induction step for one form** $Q_0$ in $m = k+1$ variables, any signature,
isotropic or not (the part of `AdelicWeilData` that does not mention anisotropy): the sphere family with
its fibration, the test function $\Phi$ and its transform $\hat\Phi$ with the twisted Poisson formula, the values
$\Phi(0) = a$, $\hat\Phi(0) = b > 0$, and the Euler-product identifications for $\Phi$ (with $b = \kappa\int\Phi_\infty$, i.e.
$\hat\Phi(0) = \int_{V_{\mathbb A}}\Phi$) and for $\hat\Phi$. The named inputs among the fields are `fib`, `poisson`, `euler`,
`vanish`, `eulerHat`; the rest are data and elementary conditions. Fields: `S`, `fib`, `Φ`, `Φh`, `measurable_Φ`,
`measurable_Φh`, `poisson`, `a`, `b`, `a_nonneg`, `b_pos`, `Φ_zero`, `Φh_zero`, `Φr`, `Ψ`, `κ`, `euler`, `κ_nonneg`, `b_eq`,
`archTest`, `Φr_nonneg`, `archTestC`, `Ψ_nonneg`, `vanish`, `Φhr`, `Ψh`, `κh`, `eulerHat`, `κh_nonneg`, `Φhr_nonneg`,
`Ψh_nonneg`. -/
structure AdelicWeilCore (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate) where
  /-- The sphere family. -/
  S : AdelicSphereFamily Q₀
  /-- Weil's fibration over each sphere (input). -/
  fib : S.Fibration hQ
  /-- The test function $\Phi$. -/
  Φ : AdeleSpace F (Fin (k + 1)) → ℝ≥0∞
  /-- Its Fourier transform $\hat\Phi$. -/
  Φh : AdeleSpace F (Fin (k + 1)) → ℝ≥0∞
  measurable_Φ : Measurable Φ
  measurable_Φh : Measurable Φh
  /-- The twisted Poisson formula (input). -/
  poisson : AdelicThetaPoisson Q₀ Φ Φh
  /-- $\Phi(0)$. -/
  a : ℝ
  /-- $\hat\Phi(0)$. -/
  b : ℝ
  a_nonneg : 0 ≤ a
  b_pos : 0 < b
  Φ_zero : Φ 0 = ENNReal.ofReal a
  Φh_zero : Φh 0 = ENNReal.ofReal b
  /-- Real-place data of $\Phi$. -/
  Φr : RealPlace F → (Fin (k + 1) → ℝ) → ℝ
  /-- Complex-place data of $\Phi$. -/
  Ψ : ComplexPlace F → (Fin (k + 1) → ℂ) → ℝ
  /-- The measure constant for $\Phi$. -/
  κ : ℝ
  /-- The Euler-product identification for $\Phi$ (input). -/
  euler : AdelicSphericalEuler S Φ Φr Ψ κ
  κ_nonneg : 0 ≤ κ
  /-- $\hat\Phi(0) = \int_{V_{\mathbb A}}\Phi = \kappa\cdot$ `phiIntegralNF`. -/
  b_eq : b = κ * phiIntegralNF Φr Ψ
  archTest : IsArchTestFn Q₀ Φr
  Φr_nonneg : ∀ w x, 0 ≤ Φr w x
  archTestC : IsArchTestFnC Q₀ Ψ
  Ψ_nonneg : ∀ w x, 0 ≤ Ψ w x
  /-- Vanishing at non-represented classes (input). -/
  vanish : NonrepresentedVanish Q₀ Φr Ψ
  /-- Real-place data of $\hat\Phi$. -/
  Φhr : RealPlace F → (Fin (k + 1) → ℝ) → ℝ
  /-- Complex-place data of $\hat\Phi$. -/
  Ψh : ComplexPlace F → (Fin (k + 1) → ℂ) → ℝ
  /-- The measure constant for $\hat\Phi$. -/
  κh : ℝ
  /-- The Euler-product identification for $\hat\Phi$ (input). -/
  eulerHat : AdelicSphericalEuler S Φh Φhr Ψh κh
  κh_nonneg : 0 ≤ κh
  Φhr_nonneg : ∀ w x, 0 ≤ Φhr w x
  Ψh_nonneg : ∀ w x, 0 ≤ Ψh w x

/-- **The data and inputs of Weil's induction step for one anisotropic form**: `AdelicWeilCore` together with
anisotropic complements. Fields: those of `AdelicWeilCore` and `aniso'`. -/
structure AdelicWeilData (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate) extends AdelicWeilCore Q₀ hQ where
  /-- The complements are anisotropic. -/
  aniso' : ∀ c, AnisotropicF (S.Q' c)

theorem sphericalZetaAtNF_nonneg' (Q₀ : QuadForm (𝓞 F) n) {Φr : RealPlace F → (Fin n → ℝ) → ℝ}
    (hΦr : ∀ w x, 0 ≤ Φr w x) {Ψ : ComplexPlace F → (Fin n → ℂ) → ℝ} (hΨ : ∀ w x, 0 ≤ Ψ w x) (ρ : F) (s : ℝ) :
    0 ≤ sphericalZetaAtNF Q₀ Φr Ψ ρ s :=
  mul_nonneg (sphericalZetaAt_nonneg Q₀ hΦr ρ s)
    (Finset.prod_nonneg fun w _ => mul_nonneg zero_le_two (cplxZetaAt_nonneg Q₀ w (hΨ w) s))

variable {Q₀ : QuadForm (𝓞 F) (k + 1)} {hQ : Q₀.Nondegenerate}

/-- With the vanishing input: $\sum_{c\ \mathrm{represented}}Z(s,c) = \kappa\,Z^{\mathrm{NF}}(s)$ (`sphericalZetaNF`,
the sum over all square classes). -/
theorem tsum_adelicSphZeta_eq (hk : 4 ≤ k) {S : AdelicSphereFamily Q₀} {Φ : AdeleSpace F (Fin (k + 1)) → ℝ≥0∞}
    {Φr Ψ} {κ : ℝ} (hE : AdelicSphericalEuler S Φ Φr Ψ κ) (hκ : 0 ≤ κ) (hQ : Q₀.Nondegenerate)
    (hΦr : ∀ w x, 0 ≤ Φr w x) (hΨ : ∀ w x, 0 ≤ Ψ w x) (hvan : NonrepresentedVanish Q₀ Φr Ψ) {s : ℝ} (hs : 0 < s) :
    ∑' c, adelicSphZeta (S.data c) Φ s = ENNReal.ofReal (κ * sphericalZetaNF Q₀ Φr Ψ s) := by
  have hsum := (summable_sphericalZetaAtNF Q₀ hQ (by omega) hΦr Ψ hs).mul_left κ
  have hnn : ∀ c : SqClasses F, 0 ≤ κ * sphericalZetaAtNF Q₀ Φr Ψ ((Quotient.out c : Fˣ) : F) s :=
    fun c => mul_nonneg hκ (sphericalZetaAtNF_nonneg' Q₀ hΦr hΨ _ s)
  simp_rw [hE.eq _ s hs]
  set f : SqClasses F → ℝ≥0∞ := fun c => ENNReal.ofReal (κ * sphericalZetaAtNF Q₀ Φr Ψ ((Quotient.out c : Fˣ) : F) s)
  have hsupp : Function.support f ⊆ {c | ∃ η : Fin (k + 1) → F, qF Q₀ η = ((Quotient.out c : Fˣ) : F)} := by
    intro c hc
    by_contra h
    exact hc (by simp [f, hvan.vanish c h s hs])
  have h1 : ∑' c : RepClasses Q₀, ENNReal.ofReal (κ * sphericalZetaAtNF Q₀ Φr Ψ (repρ c) s) = ∑' c, f c :=
    tsum_subtype_eq_of_support_subset hsupp
  rw [h1, ← ENNReal.ofReal_tsum_of_nonneg hnn hsum, tsum_mul_left, sphericalZetaNF]

/-- **$Z^+(s) < \infty$ for $s > 0$** (Step 1): for a
nondegenerate $Q_0$ in $m = k+1\ge5$ variables over a number field $F$ (any signature), given the fibration, the
induction hypothesis `AdelicComplementTauTwo` (dimension $m-1$) and the Euler-product identification
`AdelicSphericalEuler` (input), $Z^+(s) = \sum_cZ(s,c)\le\kappa\sum_{c\in F^\times/F^{\times2}}Z^{\mathrm{NF}}(s,\rho_c) < \infty$
by the summability over all square classes. No vanishing input is needed for the bound. -/
@[kb "weil1982" "§4.5, p. 109 (Z⁺(s) = Z(s) converges for Re s > 0) [unverified page]"]
theorem adelicZetaPlus_lt_top (hk : 4 ≤ k) (S : AdelicSphereFamily Q₀) (hS : S.Fibration hQ)
    (hτ : AdelicComplementTauTwo S) {Φ : AdeleSpace F (Fin (k + 1)) → ℝ≥0∞} (hΦ : Measurable Φ)
    {Φr : RealPlace F → (Fin (k + 1) → ℝ) → ℝ} {Ψ : ComplexPlace F → (Fin (k + 1) → ℂ) → ℝ} {κ : ℝ}
    (hE : AdelicSphericalEuler S Φ Φr Ψ κ) (hκ : 0 ≤ κ) (hΦr : ∀ w x, 0 ≤ Φr w x) (hΨ : ∀ w x, 0 ≤ Ψ w x)
    {D : Set (SOAdele Q₀)} (hD : IsFundamentalDomain (GammaSOAdele Q₀) D (muTam Q₀ hQ 1))
    {DM : Set (Adeles F)ˣ} (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F)) {s : ℝ} (hs : 0 < s) :
    adelicZetaPlus Q₀ hQ Φ D DM s < ⊤ := by
  rw [adelicZetaPlus_eq_tsum_of_complementTauTwo (by omega) S hS hτ hΦ hD hDM s]
  simp_rw [hE.eq _ s hs]
  have hsum := (summable_sphericalZetaAtNF Q₀ hQ (by omega) hΦr Ψ hs).mul_left κ
  have hnn : ∀ c : SqClasses F, 0 ≤ κ * sphericalZetaAtNF Q₀ Φr Ψ ((Quotient.out c : Fˣ) : F) s :=
    fun c => mul_nonneg hκ (sphericalZetaAtNF_nonneg' Q₀ hΦr hΨ _ s)
  refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := ∑' c : SqClasses F,
    κ * sphericalZetaAtNF Q₀ Φr Ψ ((Quotient.out c : Fˣ) : F) s))
  rw [ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
    (fun c => ENNReal.ofReal (κ * sphericalZetaAtNF Q₀ Φr Ψ ((Quotient.out c : Fˣ) : F) s))

/-- **$\tau(SO(V)) = 2$ for anisotropic $V$ of dimension $m = k+1\ge5$, from the induction hypothesis in dimension $m-1$**
(Weil 1982, §4.5, pp. 108–109, the induction step). Inputs: the named inputs bundled in
`W : AdelicWeilCore Q₀ hQ` (anisotropy of the complements is not needed here) and the induction hypothesis
`AdelicComplementTauTwo W.S`. -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(G) = 2 by comparing the residues of Z(s) at s = 0)"]
theorem tamagawaNumberTwoAdelic_of_anisotropic (hk : 4 ≤ k) (haniso : AnisotropicF Q₀) (W : AdelicWeilCore Q₀ hQ)
    (hτ : AdelicComplementTauTwo W.S) : TamagawaNumberTwoAdelic Q₀ hQ := by
  have hρ := dedekindZeta_residue_pos F
  obtain ⟨D, hD⟩ := (hasFundamentalDomain_GammaSOAdele Q₀ (muTam Q₀ hQ 1)).ExistsIsFundamentalDomain
  obtain ⟨DM, hDM⟩ := exists_isFundamentalDomain_ideles (tamIdeles F)
  have hk1 : 1 ≤ k := by omega
  -- the multiplicative side
  have hZ : ∀ s, 0 < s → adelicZetaPlus Q₀ hQ W.Φ D DM s = ENNReal.ofReal (W.κ * sphericalZetaNF Q₀ W.Φr W.Ψ s) :=
    fun s hs => by
      rw [adelicZetaPlus_eq_tsum_of_complementTauTwo hk1 W.S W.fib hτ W.measurable_Φ hD hDM s]
      exact tsum_adelicSphZeta_eq hk W.euler W.κ_nonneg hQ W.Φr_nonneg W.Ψ_nonneg W.vanish hs
  have hZh : adelicZetaPlus Q₀ hQ W.Φh D DM 1 ≠ ⊤ :=
    (adelicZetaPlus_lt_top hk W.S W.fib hτ W.measurable_Φh W.eulerHat W.κh_nonneg W.Φhr_nonneg W.Ψh_nonneg hD hDM
      one_pos).ne
  -- Step 4: finite volume
  set s₀ : ℝ := (k + 1) * W.b / (4 * (W.a + 1)) with hs₀
  have ha1 : 0 < W.a + 1 := by linarith [W.a_nonneg]
  have hs₀pos : 0 < s₀ := by have := W.b_pos; positivity
  have hsb : 2 * s₀ * W.a < ((k + 1 : ℕ) : ℝ) * W.b := by
    rw [hs₀]; push_cast
    have hb := W.b_pos
    have hkb : 0 < ((k : ℝ) + 1) * W.b := by positivity
    rw [show 2 * ((↑k + 1) * W.b / (4 * (W.a + 1))) * W.a = ((↑k + 1) * W.b) * (W.a / (2 * (W.a + 1))) by
      field_simp; ring]
    have : W.a / (2 * (W.a + 1)) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [W.a_nonneg]
    nlinarith
  have hDfin : muTam Q₀ hQ 1 D < ⊤ := measure_fundamentalDomain_lt_top haniso W.measurable_Φ W.measurable_Φh W.poisson hDM
    W.a_nonneg W.b_pos W.Φ_zero W.Φh_zero hs₀pos hsb (by rw [hZ s₀ hs₀pos]; exact ENNReal.ofReal_ne_top)
  -- the additive residue
  have hC : adelicZetaPlus Q₀ hQ W.Φh D DM 1 + adelicZetaPlus Q₀ hQ W.Φ D DM 1 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hZh, by rw [hZ 1 one_pos]; exact ENNReal.ofReal_ne_top⟩
  have hadd := tendsto_mul_adelicZetaPlus (by omega) haniso W.measurable_Φ W.measurable_Φh W.poisson hDM
    W.a_nonneg W.b_pos W.Φ_zero W.Φh_zero hDfin.ne hC
    (W.fib.measurable_adelicInner hk1 W.measurable_Φh hDM 1)
  -- the multiplicative residue
  have hmul : Tendsto (fun s => s * (adelicZetaPlus Q₀ hQ W.Φ D DM s).toReal) (𝓝[>] 0) (𝓝 (dedekindZeta_residue F * W.b)) := by
    have h := (tendsto_mul_sphericalZetaNF_zero_of_nonneg Q₀ hQ (by omega) W.archTest W.Φr_nonneg
      W.archTestC).const_mul W.κ
    rw [W.b_eq]
    refine (h.congr' ?_).trans (by rw [show W.κ * (dedekindZeta_residue F * phiIntegralNF W.Φr W.Ψ) = dedekindZeta_residue F * (W.κ * phiIntegralNF W.Φr W.Ψ)
      by ring])
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hnn : 0 ≤ W.κ * sphericalZetaNF Q₀ W.Φr W.Ψ s := mul_nonneg W.κ_nonneg (by
      unfold sphericalZetaNF; exact tsum_nonneg fun c => sphericalZetaAtNF_nonneg' Q₀ W.Φr_nonneg W.Ψ_nonneg _ s)
    rw [hZ s hs, ENNReal.toReal_ofReal hnn]
    ring
  have heq := tendsto_nhds_unique hadd hmul
  have hV : (muTam Q₀ hQ 1 D).toReal = 2 := by
    have hbpos := W.b_pos
    have : (muTam Q₀ hQ 1 D).toReal * (dedekindZeta_residue F * W.b) = 2 * (dedekindZeta_residue F * W.b) := by linarith
    exact mul_right_cancel₀ (by positivity) this
  show covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ 1) = 2
  rw [covolume_muTam_eq Q₀ hQ _ hD]
  show muTam Q₀ hQ 1 D = 2
  rw [← ENNReal.ofReal_toReal hDfin.ne, hV]
  simp

/-! ### The induction -/

/-- **$\tau = 2$ for all anisotropic forms of dimension $m$ over $F$** (target statement). -/
def AnisotropicTauTwo (F : Type) [Field F] [NumberField F] (m : ℕ) : Prop :=
  ∀ (Q₀ : QuadForm (𝓞 F) m) (hQ : Q₀.Nondegenerate), AnisotropicF Q₀ → TamagawaNumberTwoAdelic Q₀ hQ

/-- **The base case $m = 4$** (**input**; anisotropic quaternary forms). Field: `tau_two`. -/
@[kb "weil1982" "§4.5 (induction base, dim 4) [unverified page]"]
structure AnisotropicTauTwoBase (F : Type) [Field F] [NumberField F] (m : ℕ) : Prop where
  /-- $\tau = 2$ in dimension $m$. -/
  tau_two : AnisotropicTauTwo F m

/-- **Weil's per-dimension inputs** (**input**): every anisotropic nondegenerate form in $k+1$ variables carries
`AdelicWeilData`. Field: `data`. -/
@[kb "weil1982" "§4.5, pp. 108–109 (inputs of the induction step) [unverified page]"]
structure AdelicStepInputs (F : Type) [Field F] [NumberField F] (k : ℕ) : Prop where
  /-- The data for each anisotropic form. -/
  data : ∀ (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate), AnisotropicF Q₀ → Nonempty (AdelicWeilData Q₀ hQ)

/-- **Weil's induction for anisotropic forms**: from the base case $m = 4$ and the
per-dimension inputs, $\tau(SO(V)) = 2$ for every anisotropic $V$ of dimension $m\ge5$ over the number field $F$. -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(SO) = 2 by induction on dim)"]
theorem anisotropicTauTwo_of_inputs (base : AnisotropicTauTwoBase F 4)
    (step : ∀ k, 4 ≤ k → AdelicStepInputs F k) : ∀ m, 5 ≤ m → AnisotropicTauTwo F m := by
  have key : ∀ k, 4 ≤ k → AnisotropicTauTwo F k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact base.tau_two
    | succ k hk ih =>
      intro Q₀ hQ haniso
      obtain ⟨W⟩ := (step k hk).data Q₀ hQ haniso
      exact tamagawaNumberTwoAdelic_of_anisotropic hk haniso W.toAdelicWeilCore
        ⟨fun c => ih (W.S.Q' c) (W.S.hQ' c) (W.aniso' c)⟩
  intro m hm
  exact key m (by omega)

end QuadFormsKB.Tamagawa.Measure.Weil
