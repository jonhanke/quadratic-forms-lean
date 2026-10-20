import QuadFormsKB.Tamagawa.Measure.Weil.QuatZetaFinite
import QuadFormsKB.Tamagawa.ArchTestFn

/-!
# The zeta integral of $\mathbb H[F,a,b]$, multiplicatively, and its residue

$a, b\in\mathcal O_F\setminus0$, $\mathbb H = \mathbb H[F,a,b]$, any number field, any signature. `tamQuat` is Weil's measure
$\omega_\infty\times\prod_v\lambda_v^{-1}\omega_v$ on $(\mathbb H\otimes\mathbb A)^\times$ (no factor $\rho_F^{-1}$).

**Test functions.** $\Phi = \Phi_\infty\otimes\mathbf 1_{\hat\Lambda}$ on $\mathbb H_{\mathbb A}$, in the coordinates $1,i,j,k$
(`quatTestFn`): $\Phi_\infty : F_\infty^4\to[0,\infty]$ measurable with $\int\Phi_\infty < \infty$ and
$\int\Phi_\infty\|\operatorname{nrd}\|_\infty < \infty$ (stated as two `lintegral` hypotheses; every Gaussian and every
non-negative Schwartz function qualifies), $\hat\Lambda = \hat{\mathcal O}\langle1,i,j,k\rangle$.

* **`quatZeta Φ s`** $=\int_{(\mathbb H\otimes\mathbb A)^\times}\Phi(x)\,\|\operatorname{nrd}x\|_{\mathbb A}^s\,d\mu(x)$ (Weil's $Z_\Phi(s)$,
  AAG §3.1, (2), p. 36, in the variable $s$ with $\omega = \|\operatorname{nrd}\|^{-2}dx$: pole at $s = 2$).
* **`quatZeta_eq_mul`**: $Z_\Phi(s) = Z_\infty(s)\cdot Z_f(s)$ (the two factors of `tamQuat` and
  $\|\operatorname{nrd}x\|_{\mathbb A} = \|\operatorname{nrd}x_\infty\|_\infty\|\operatorname{nrd}x_f\|_f$, `ideleNorm_nrdUnit`).
* **`quatInfZeta_eq_coord`**: $Z_\infty(s) = \int_{F_\infty^4}\Phi_\infty(z)\,\|\operatorname{nrd}z\|_\infty^{s-2}\,dz$ for $s > 2$;
  **`tendsto_quatInfZeta`**: $Z_\infty(s)\to\int\Phi_\infty$ as $s\to2^+$ (dominated convergence; the null cone
  $\{\|\operatorname{nrd}\|_\infty = 0\}$ is Lebesgue-null by the line argument of `ArchTest.measure_eq_zero_of_lines`, every
  signature and complex places included).
* **`tendsto_mul_quatZeta`** (**Weil's multiplicative residue**, AAG §3.1, p. 38):
  $$\lim_{s\to2^+}(s-2)\,Z_\Phi(s) = \rho_F\cdot|d_F|^{-2}\int_{F_\infty^4}\Phi_\infty = \rho_F\int_{\mathbb H_{\mathbb A}}\Phi\,dx,$$
  $dx$ the coordinate self-dual measure ($\operatorname{vol}(\hat\Lambda) = |d_F|^{-2}$).
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology Set NumberField.mixedEmbedding
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

set_option synthInstance.maxHeartbeats 400000

/-! ### The archimedean factor -/

section Arch

variable (a b : F)

/-- $\|t\|_\infty = |\det_{\mathbb R}(t\cdot)|$ on $F_\infty$. -/
def absDetInf (t : mixedSpace F) : ℝ := |LinearMap.det (LinearMap.mulLeft ℝ t)|

theorem absDetInf_mul (s t : mixedSpace F) : absDetInf (s * t) = absDetInf s * absDetInf t := by
  rw [absDetInf, absDetInf, absDetInf, LinearMap.mulLeft_mul, LinearMap.det_comp, abs_mul]

theorem absDetInf_nonneg (t : mixedSpace F) : 0 ≤ absDetInf t := abs_nonneg _

theorem continuous_absDetInf : Continuous (absDetInf (F := F)) := continuous_abs_det_mulLeft

theorem isUnit_of_absDetInf_ne_zero {t : mixedSpace F} (h : absDetInf t ≠ 0) : IsUnit t := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ t) ≠ 0 := fun h0 => h (by simp [absDetInf, h0])
  have hu : IsUnit (LinearMap.mulLeft ℝ t) :=
    (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨y, hy⟩ := (Module.End.isUnit_iff _).mp hu |>.surjective 1
  exact isUnit_iff_exists_inv.mpr ⟨y, hy⟩

/-- $\|\operatorname{nrd}z\|_\infty$ in the coordinates $z\in F_\infty^4$. -/
def nrdNormW (z : Fin 4 → mixedSpace F) : ℝ := absDetInf (nrdForm (mixedEmbedding F a) (mixedEmbedding F b) z)

theorem continuous_nrdNormW : Continuous (nrdNormW a b) :=
  continuous_absDetInf.comp (by unfold nrdForm; fun_prop)

theorem nrdInf_eq_nrdForm (x : QuatInf a b) :
    nrdInf a b x = nrdForm (mixedEmbedding F a) (mixedEmbedding F b) (quatInfCoord a b x) := by
  have hc : quatInfCoord a b x = ![x.re, x.imI, x.imJ, x.imK] := by
    funext i; fin_cases i <;> rfl
  rw [hc]
  simp only [nrdInf, nrdForm, QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star]
  simp
  ring

/-- **The archimedean zeta integral** $Z_\infty(s) = \int_{(\mathbb H\otimes F_\infty)^\times}\Phi_\infty(x)\,
\|\operatorname{nrd}x\|_\infty^s\,\omega_\infty(x)$. -/
def quatInfZeta (Φ : (Fin 4 → mixedSpace F) → ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, Φ (quatInfCoord a b (u : QuatInf a b)) * ENNReal.ofReal (absDetInf (nrdInf a b (u : QuatInf a b))) ^ s
    ∂omegaQuatInf a b

theorem distribHaarChar_quatInf_inv (u : (QuatInf a b)ˣ) :
    (distribHaarChar (QuatInf a b) u⁻¹ : ℝ≥0∞) = (ENNReal.ofReal (absDetInf (nrdInf a b (u : QuatInf a b))) ^ 2)⁻¹ := by
  have h := distribHaarChar_quatInf a b u⁻¹
  rw [inv_inv, sq, LinearMap.mulLeft_mul, LinearMap.det_comp, abs_mul] at h
  have hpos : 0 < absDetInf (nrdInf a b (u : QuatInf a b)) := by
    rw [absDetInf, abs_pos]
    exact det_mulLeft_ne_zero_of_isUnit ((isUnit_iff_isUnit_nrdInf a b _).mp u.isUnit)
  rw [← ENNReal.ofReal_coe_nnreal, h, ← ENNReal.ofReal_pow hpos.le, ← ENNReal.ofReal_inv_of_pos (by positivity)]
  congr 1
  rw [absDetInf, sq]

/-- **$Z_\infty$ in coordinates**: for $s > 2$, $Z_\infty(s) = \int_{F_\infty^4}\Phi_\infty(z)\,\|\operatorname{nrd}z\|_\infty^{s-2}\,dz$
($dz$ = `muInfVec`, the coordinate measure). -/
theorem quatInfZeta_eq_coord {Φ : (Fin 4 → mixedSpace F) → ℝ≥0∞} (hΦ : Measurable Φ) {s : ℝ} (hs : 2 < s) :
    quatInfZeta a b Φ s = ∫⁻ z, Φ z * ENNReal.ofReal (nrdNormW a b z ^ (s - 2)) ∂muInfVec F (Fin 4) := by
  set G : QuatInf a b → ℝ≥0∞ := fun x => Φ (quatInfCoord a b x) *
    ENNReal.ofReal (absDetInf (nrdInf a b x) ^ (s - 2)) with hG
  have hnm : Measurable fun x : QuatInf a b => absDetInf (nrdInf a b x) :=
    (continuous_absDetInf.comp (continuous_nrdInf a b)).measurable
  have hGm : Measurable G :=
    (hΦ.comp (continuous_quatInfCoord a b).measurable).mul (ENNReal.measurable_ofReal.comp (hnm.pow_const _))
  have hval := isOpenEmbedding_val_quatInf a b
  have he := hval.measurableEmbedding
  have h1 : quatInfZeta a b Φ s = ∫⁻ u : (QuatInf a b)ˣ, G u ∂((quatInfVol a b).comap Units.val) := by
    rw [quatInfZeta, omegaQuatInf, unitsHaar, lintegral_withDensity_eq_lintegral_mul]
    · refine lintegral_congr fun u => ?_
      simp only [Pi.mul_apply, hG]
      rw [distribHaarChar_quatInf_inv]
      exact inv_sq_mul_eq (absDetInf_nonneg _) hs _
    · exact measurable_distribHaarChar_inv (continuous_distribHaarChar_quatInf a b)
    · exact ((hΦ.comp (continuous_quatInfCoord a b).measurable).comp Units.continuous_val.measurable).mul
        (((ENNReal.measurable_ofReal.comp hnm).pow_const s).comp Units.continuous_val.measurable)
  have h2 : ∫⁻ u : (QuatInf a b)ˣ, G u ∂((quatInfVol a b).comap Units.val) = ∫⁻ x, G x ∂quatInfVol a b := by
    rw [← lintegral_map hGm Units.continuous_val.measurable, he.map_comap]
    refine setLIntegral_eq_of_support_subset fun x hx => ?_
    by_contra hxr
    apply hx
    have h0 : absDetInf (nrdInf a b x) = 0 := by
      by_contra hn
      exact hxr ⟨((isUnit_iff_isUnit_nrdInf a b x).mpr (isUnit_of_absDetInf_ne_zero hn)).unit, rfl⟩
    simp only [hG, h0, Real.zero_rpow (show s - 2 ≠ 0 by linarith), ENNReal.ofReal_zero, mul_zero]
  rw [h1, h2]
  change ∫⁻ x, G x ∂((muInfVec F (Fin 4)).map (quatInfCLE a b).symm) = _
  rw [lintegral_map hGm (quatInfCLE a b).symm.continuous.measurable]
  refine lintegral_congr fun z => ?_
  simp only [hG, nrdNormW]
  have hc : quatInfCoord a b ((quatInfCLE a b).symm z) = z := (quatInfCLE a b).apply_symm_apply z
  rw [nrdInf_eq_nrdForm, show quatInfCoord a b ((quatInfCLE a b).symm z) = z from hc]

/-! ### The null cone of $\|\operatorname{nrd}\|_\infty$ and continuity of $Z_\infty$ at $s = 2$ -/

theorem finite_quad_roots {K : Type*} [Field K] (α β : K) : {t : K | (t + α) ^ 2 + β = 0}.Finite := by
  open Polynomial in
  have hm : ((X + C α) ^ 2 + C β : K[X]).Monic := by
    refine (monic_X_add_C α).pow 2 |>.add_of_left ?_
    refine degree_C_le.trans_lt ?_
    rw [degree_pow, degree_X_add_C]; norm_num
  refine (finite_setOfPred_isRoot hm.ne_zero).subset fun t ht => ?_
  simp only [mem_ofPred_eq] at ht ⊢
  simp [IsRoot, ht]

/-- The coordinate vector of $1\in\mathbb H$, $e_0 = (1,0,0,0)\in F_\infty^4$. -/
def eZero : Fin 4 → mixedSpace F := Pi.single 0 1

theorem absDetInf_eq_zero_iff (y : mixedSpace F) : absDetInf y = 0 ↔ (∃ w, y.1 w = 0) ∨ ∃ w, y.2 w = 0 := by
  rw [absDetInf, abs_eq_zero, det_mulLeft_mixedSpace, mul_eq_zero, Finset.prod_eq_zero_iff, Finset.prod_eq_zero_iff]
  simp

/-- **The null cone of $\|\operatorname{nrd}\|_\infty$ is Lebesgue-null** on $F_\infty^4$, for every $a, b$ and every
signature: along each line $x + te_0$ the components of $\operatorname{nrd}(x+te_0) = (x_0+t)^2 + \cdots$ vanish for at
most two values of $t$ (`ArchTest.measure_eq_zero_of_lines`). -/
theorem muInfVec_nrdNormW_eq_zero : muInfVec F (Fin 4) {z | nrdNormW a b z = 0} = 0 := by
  have hN : MeasurableSet {z : Fin 4 → mixedSpace F | nrdNormW a b z = 0} :=
    measurableSet_eq_fun (continuous_nrdNormW a b).measurable measurable_const
  refine ArchTest.measure_eq_zero_of_lines (muInfVec F (Fin 4)) hN eZero fun x => ?_
  refine Set.Finite.measure_zero ?_ _
  have hcomp : ∀ t : ℝ, nrdForm (mixedEmbedding F a) (mixedEmbedding F b) (x + t • eZero) =
      ((x 0 + algebraMap ℝ (mixedSpace F) t) ^ 2 - mixedEmbedding F a * x 1 ^ 2 - mixedEmbedding F b * x 2 ^ 2 +
        mixedEmbedding F a * mixedEmbedding F b * x 3 ^ 2) := by
    intro t
    simp only [nrdForm, eZero, Pi.add_apply, Pi.smul_apply, Pi.single_apply]
    simp [Algebra.algebraMap_eq_smul_one]
  set y := mixedEmbedding F a * x 1 ^ 2 + mixedEmbedding F b * x 2 ^ 2 -
    mixedEmbedding F a * mixedEmbedding F b * x 3 ^ 2 with hy
  have hreal : ∀ w, {t : ℝ | ((x 0).1 w + t) ^ 2 + (-(y.1 w)) = 0}.Finite := fun w => by
    have := finite_quad_roots ((x 0).1 w) (-(y.1 w))
    refine this.subset fun t ht => ?_
    simp only [mem_ofPred_eq] at ht ⊢; linarith [ht]
  have hcplx : ∀ w, {t : ℝ | (((t : ℂ) + (x 0).2 w) ^ 2 + (-(y.2 w))) = 0}.Finite := fun w =>
    (finite_quad_roots ((x 0).2 w) (-(y.2 w))).preimage Complex.ofReal_injective.injOn
  refine ((Set.finite_iUnion hreal).union (Set.finite_iUnion hcplx)).subset fun t ht => ?_
  simp only [mem_ofPred_eq, nrdNormW, hcomp, absDetInf_eq_zero_iff] at ht
  simp only [mem_union, mem_iUnion, mem_ofPred_eq]
  rcases ht with ⟨w, hw⟩ | ⟨w, hw⟩
  · left; refine ⟨w, ?_⟩
    simp only [Prod.fst_add, Prod.fst_sub, Prod.fst_mul, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Prod.pow_fst,
      Pi.pow_apply] at hw
    simp only [hy, Prod.fst_add, Prod.fst_sub, Prod.fst_mul, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Prod.pow_fst,
      Pi.pow_apply]
    have : (algebraMap ℝ (mixedSpace F) t).1 w = t := by simp [Algebra.algebraMap_eq_smul_one]
    rw [this] at hw
    linear_combination hw
  · right; refine ⟨w, ?_⟩
    simp only [Prod.snd_add, Prod.snd_sub, Prod.snd_mul, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Prod.pow_snd,
      Pi.pow_apply] at hw
    simp only [hy, Prod.snd_add, Prod.snd_sub, Prod.snd_mul, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Prod.pow_snd,
      Pi.pow_apply]
    have : (algebraMap ℝ (mixedSpace F) t).2 w = (t : ℂ) := by simp [Algebra.algebraMap_eq_smul_one]
    rw [this] at hw
    linear_combination hw

theorem ae_nrdNormW_ne_zero : ∀ᵐ z ∂muInfVec F (Fin 4), nrdNormW a b z ≠ 0 :=
  measure_eq_zero_iff_ae_notMem.mp (muInfVec_nrdNormW_eq_zero a b)

theorem rpow_le_one_add' {t s : ℝ} (ht : 0 ≤ t) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : t ^ s ≤ 1 + t :=
  GlobalZeta.rpow_le_one_add ht ⟨hs0, hs1⟩

/-- $Z_\infty(s)\le\int\Phi_\infty(1 + \|\operatorname{nrd}\|_\infty)$ for $2 < s\le3$. -/
theorem quatInfZeta_le {Φ : (Fin 4 → mixedSpace F) → ℝ≥0∞} (hΦ : Measurable Φ) {s : ℝ} (hs : 2 < s) (hs3 : s ≤ 3) :
    quatInfZeta a b Φ s ≤ ∫⁻ z, Φ z * ENNReal.ofReal (1 + nrdNormW a b z) ∂muInfVec F (Fin 4) := by
  rw [quatInfZeta_eq_coord a b hΦ hs]
  refine lintegral_mono fun z => mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
  exact rpow_le_one_add' (absDetInf_nonneg _) (by linarith) (by linarith)

/-- **Continuity of $Z_\infty$ at the pole**: $Z_\infty(s)\to\int\Phi_\infty$ as $s\to2^+$, for $\Phi_\infty$ with
$\int\Phi_\infty(1+\|\operatorname{nrd}\|_\infty) < \infty$. -/
theorem tendsto_quatInfZeta {Φ : (Fin 4 → mixedSpace F) → ℝ≥0∞} (hΦ : Measurable Φ)
    (hfin : ∫⁻ z, Φ z * ENNReal.ofReal (1 + nrdNormW a b z) ∂muInfVec F (Fin 4) ≠ ⊤) :
    Tendsto (quatInfZeta a b Φ) (𝓝[>] 2) (𝓝 (∫⁻ z, Φ z ∂muInfVec F (Fin 4))) := by
  have hev : ∀ᶠ s in 𝓝[>] (2 : ℝ), s < 3 := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (show (2 : ℝ) < 3 by norm_num))] with s hs using hs
  have hev2 : ∀ᶠ s in 𝓝[>] (2 : ℝ), 2 < s := self_mem_nhdsWithin
  have h := tendsto_lintegral_filter_of_dominated_convergence
    (F := fun s z => Φ z * ENNReal.ofReal (nrdNormW a b z ^ (s - 2))) (l := 𝓝[>] (2 : ℝ))
    (μ := muInfVec F (Fin 4)) (f := Φ) (fun z => Φ z * ENNReal.ofReal (1 + nrdNormW a b z))
    (Eventually.of_forall fun s => hΦ.mul (ENNReal.measurable_ofReal.comp
      ((continuous_nrdNormW a b).measurable.pow_const _)))
    (by
      filter_upwards [hev, hev2] with s hs3 hs2
      exact Eventually.of_forall fun z => mul_le_mul_right (ENNReal.ofReal_le_ofReal
        (rpow_le_one_add' (absDetInf_nonneg _) (by linarith) (by linarith))) _)
    hfin
    (by
      filter_upwards [ae_nrdNormW_ne_zero a b] with z hz
      have h1 : Tendsto (fun s : ℝ => nrdNormW a b z ^ (s - 2)) (𝓝[>] 2) (𝓝 (nrdNormW a b z ^ ((2 : ℝ) - 2))) :=
        ((Real.continuousAt_const_rpow hz).tendsto.comp
          ((continuous_id.sub continuous_const).tendsto 2)).mono_left nhdsWithin_le_nhds
      rw [sub_self, Real.rpow_zero] at h1
      have h2 := (ENNReal.continuous_ofReal.tendsto _).comp h1
      rw [ENNReal.ofReal_one] at h2
      have h3 := ENNReal.Tendsto.const_mul h2 (Or.inl one_ne_zero) (a := Φ z)
      rw [mul_one] at h3
      exact h3)
  refine h.congr' ?_
  filter_upwards [hev2] with s hs
  exact (quatInfZeta_eq_coord a b hΦ hs).symm

end Arch

/-! ### The global zeta integral -/

section Global

variable (a b : F)

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-- **The test function** $\Phi = \Phi_\infty\otimes\mathbf 1_{\hat\Lambda}$ on $\mathbb H_{\mathbb A}$ in the coordinates $1,i,j,k$:
$\Phi(x) = \Phi_\infty(x_\infty)\cdot\mathbf 1[x_f\in\hat{\mathcal O}^4]$. -/
def quatTestFn (Φ : (Fin 4 → mixedSpace F) → ℝ≥0∞) (x : QuatAdele a b) : ℝ≥0∞ :=
  Φ (fun i => (quatCoord a b x i).1) * (Set.pi univ fun _ => (OHat : Set AF)).indicator (fun _ => (1 : ℝ≥0∞))
    (fun i => (quatCoord a b x i).2)

/-- **Weil's zeta integral of $\mathbb H$** (AAG §3.1, (2), p. 36):
$Z_\Phi(s) = \int_{(\mathbb H\otimes\mathbb A)^\times}\Phi(x)\,\|\operatorname{nrd}x\|_{\mathbb A}^s\,d\mu(x)$, $\mu$ = `tamQuat`. -/
@[kb "weil1982" "§3.1, (2), p. 36 (the zeta function Z_Φ(s) of a simple algebra, A = ℍ)"]
def quatZeta (Φ : (Fin 4 → mixedSpace F) → ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, quatTestFn a b Φ (x : QuatAdele a b) * ENNReal.ofReal (ideleNorm F (nrdUnit x)) ^ s ∂tamQuat a b

theorem quatUnitsEquiv_fst_val (x : (QuatAdele a b)ˣ) :
    (((quatUnitsEquiv a b x).1 : (QuatInf a b)ˣ) : QuatInf a b) = (quatAdeleRingEquiv a b (x : QuatAdele a b)).1 :=
  rfl

theorem quatUnitsEquiv_snd_val (x : (QuatAdele a b)ˣ) :
    (((quatUnitsEquiv a b x).2 : (QuatFin a b)ˣ) : QuatFin a b) = (quatAdeleRingEquiv a b (x : QuatAdele a b)).2 :=
  rfl

theorem quatCoord_fst (x : QuatAdele a b) :
    (fun i => (quatCoord a b x i).1) = quatInfCoord a b (quatAdeleRingEquiv a b x).1 := by
  funext i; fin_cases i <;> rfl

theorem quatCoord_snd (x : QuatAdele a b) :
    (fun i => (quatCoord a b x i).2) = quatFinCoord a b (quatAdeleRingEquiv a b x).2 := by
  funext i; fin_cases i <;> rfl

theorem quatTestFn_eq (Φ : (Fin 4 → mixedSpace F) → ℝ≥0∞) (x : QuatAdele a b) :
    quatTestFn a b Φ x = Φ (quatInfCoord a b (quatAdeleRingEquiv a b x).1) *
      (lamHat a b).indicator (fun _ => (1 : ℝ≥0∞)) (quatAdeleRingEquiv a b x).2 := by
  rw [quatTestFn, quatCoord_fst, quatCoord_snd, lamHat_eq]
  rfl

theorem infPart_nrdUnit (x : (QuatAdele a b)ˣ) :
    ((infPart (nrdUnit x) : (mixedSpace F)ˣ) : mixedSpace F) = nrdInf a b (quatAdeleRingEquiv a b (x : QuatAdele a b)).1 := by
  change ((x : QuatAdele a b) * star (x : QuatAdele a b)).re.1 = _
  simp [nrdInf, QuaternionAlgebra.re_mul, quatAdeleRingEquiv]

theorem finPart_nrdUnit_apply (x : (QuatAdele a b)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ((finPart (nrdUnit x) : AFˣ) : AF) v = nrdLoc _ _ (projQ a b v (quatAdeleRingEquiv a b (x : QuatAdele a b)).2) := by
  change ((x : QuatAdele a b) * star (x : QuatAdele a b)).re.2 v = _
  simp only [nrdLoc, QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, projQ_re, projQ_imI, projQ_imJ, projQ_imK]
  simp [quatAdeleRingEquiv, diag_snd]
  rfl

/-- **$\|\operatorname{nrd}x\|_{\mathbb A} = \|\operatorname{nrd}x_\infty\|_\infty\cdot\|\operatorname{nrd}x_f\|_f$.** -/
theorem ideleNorm_nrdUnit (x : (QuatAdele a b)ˣ) :
    ideleNorm F (nrdUnit x) = absDetInf (nrdInf a b (quatAdeleRingEquiv a b (x : QuatAdele a b)).1) *
      normFinQ a b (quatUnitsEquiv a b x).2 := by
  rw [ideleNorm, absDetInf, infPart_nrdUnit, normFinQ]
  congr 1
  refine finprod_congr fun v => ?_
  rw [modAt, distribHaarChar_adic_eq_norm, unitAt_val, finPart_nrdUnit_apply]
  rfl

theorem measurable_quatTestFn {Φ : (Fin 4 → mixedSpace F) → ℝ≥0∞} (hΦ : Measurable Φ) :
    Measurable fun x : (QuatAdele a b)ˣ => quatTestFn a b Φ (x : QuatAdele a b) := by
  refine (hΦ.comp ?_).mul ((measurable_const.indicator (MeasurableSet.univ_pi fun _ => measurableSet_OHat)).comp ?_)
  · exact measurable_pi_iff.mpr fun i => (continuous_fst.comp ((continuous_apply i).comp
      ((continuous_quatCoord a b).comp Units.continuous_val))).measurable
  · exact measurable_pi_iff.mpr fun i => (continuous_snd.comp ((continuous_apply i).comp
      ((continuous_quatCoord a b).comp Units.continuous_val))).measurable

theorem measurable_ideleNorm_nrdUnit : Measurable fun x : (QuatAdele a b)ˣ => ideleNorm F (nrdUnit x) := by
  have h : (fun x : (QuatAdele a b)ˣ => ideleNorm F (nrdUnit x)) = fun x => Real.sqrt (quatNormSqHom a b x : ℝ) := by
    funext x
    rw [coe_quatNormSqHom, Real.sqrt_sq (ideleNorm_pos _).le]
  rw [h]
  exact (Real.continuous_sqrt.comp (NNReal.continuous_coe.comp (continuous_quatNormSqHom a b))).measurable

/-- **The zeta integral factors**: $Z_\Phi(s) = Z_\infty(s)\,Z_f(s)$ for $s\ge0$ (Tonelli on
$(\mathbb H\otimes\mathbb A)^\times\cong(\mathbb H\otimes F_\infty)^\times\times(\mathbb H\otimes\mathbb A_f)^\times$). -/
theorem quatZeta_eq_mul {Φ : (Fin 4 → mixedSpace F) → ℝ≥0∞} (hΦ : Measurable Φ) {s : ℝ} (hs : 0 ≤ s) :
    quatZeta a b Φ s = quatInfZeta a b Φ s * quatFinZeta a b s := by
  set e := quatUnitsEquiv a b
  set A : (QuatInf a b)ˣ → ℝ≥0∞ := fun u => Φ (quatInfCoord a b (u : QuatInf a b)) *
    ENNReal.ofReal (absDetInf (nrdInf a b (u : QuatInf a b))) ^ s with hA
  set B : (QuatFin a b)ˣ → ℝ≥0∞ := quatFinIntegrand a b s
  have hAm : Measurable A := (hΦ.comp ((continuous_quatInfCoord a b).comp Units.continuous_val).measurable).mul
    ((ENNReal.measurable_ofReal.comp ((continuous_absDetInf.comp ((continuous_nrdInf a b).comp
      Units.continuous_val)).measurable)).pow_const s)
  have hfm : Measurable fun x : (QuatAdele a b)ˣ =>
      quatTestFn a b Φ (x : QuatAdele a b) * ENNReal.ofReal (ideleNorm F (nrdUnit x)) ^ s :=
    (measurable_quatTestFn a b hΦ).mul ((ENNReal.measurable_ofReal.comp (measurable_ideleNorm_nrdUnit a b)).pow_const s)
  have hpt : ∀ x : (QuatAdele a b)ˣ, quatTestFn a b Φ (x : QuatAdele a b) * ENNReal.ofReal (ideleNorm F (nrdUnit x)) ^ s =
      A (e x).1 * B (e x).2 := by
    intro x
    simp only [hA, B, quatFinIntegrand]
    rw [quatTestFn_eq, ideleNorm_nrdUnit, ENNReal.ofReal_mul (absDetInf_nonneg _), ENNReal.mul_rpow_of_nonneg _ _ hs,
      quatUnitsEquiv_fst_val, quatUnitsEquiv_snd_val]
    ring
  have hB : Measurable B := by
    have hind : (fun z : (QuatFin a b)ˣ => (lamHat a b).indicator (fun _ => (1 : ℝ≥0∞)) (z : QuatFin a b)) =
        (Units.val ⁻¹' lamHat a b).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext z; rfl
    have hn : Measurable (normFinQ a b) := by
      have h2 : ∀ z : (QuatFin a b)ˣ, normFinQ a b z =
          ideleNorm F (nrdUnit ((quatUnitsEquiv a b).symm (1, z))) := by
        intro z
        rw [ideleNorm_nrdUnit, ← quatUnitsEquiv_fst_val, (quatUnitsEquiv a b).apply_symm_apply]
        simp [absDetInf, nrdInf]
      rw [show normFinQ a b = fun z => ideleNorm F (nrdUnit ((quatUnitsEquiv a b).symm (1, z))) from funext h2]
      exact (measurable_ideleNorm_nrdUnit a b).comp ((map_continuous (quatUnitsEquiv a b).symm).comp
        (continuous_const.prodMk continuous_id)).measurable
    have hm1 : Measurable fun z : (QuatFin a b)ˣ => (lamHat a b).indicator (fun _ => (1 : ℝ≥0∞)) (z : QuatFin a b) := by
      rw [hind]
      exact measurable_const.indicator ((isOpen_lamHat a b).preimage Units.continuous_val).measurableSet
    exact hm1.mul ((ENNReal.measurable_ofReal.comp hn).pow_const s)
  rw [quatZeta, tamQuat, lintegral_map hfm (map_continuous (quatUnitsEquiv a b).symm).measurable]
  have : ∀ p : (QuatInf a b)ˣ × (QuatFin a b)ˣ, quatTestFn a b Φ ((e.symm p : (QuatAdele a b)ˣ) : QuatAdele a b) *
      ENNReal.ofReal (ideleNorm F (nrdUnit (e.symm p))) ^ s = A p.1 * B p.2 := by
    intro p; rw [hpt, e.apply_symm_apply]
  refine (lintegral_congr fun p => this p).trans ?_
  have : SFinite (muFinQuat a b) := by unfold muFinQuat; infer_instance
  exact lintegral_prod_mul hAm.aemeasurable hB.aemeasurable

/-- **Weil's multiplicative residue for $\mathbb H$** (AAG §3.1, p. 38): for $a, b\in\mathcal O_F\setminus0$ and $\Phi_\infty$
measurable with $\int\Phi_\infty(1+\|\operatorname{nrd}\|_\infty) < \infty$,
$$\lim_{s\to2^+}(s-2)\,Z_\Phi(s) = \rho_F\cdot|d_F|^{-2}\int_{F_\infty^4}\Phi_\infty\,dz = \rho_F\int_{\mathbb H_{\mathbb A}}\Phi\,dx.$$ -/
@[kb "weil1982" "§3.1, pp. 36-38 (multiplicative calculation; residue ρ_k∫Φ at the pole), A = ℍ"]
theorem tendsto_mul_quatZeta {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0) {Φ : (Fin 4 → mixedSpace F) → ℝ≥0∞}
    (hΦ : Measurable Φ)
    (hfin : ∫⁻ z, Φ z * ENNReal.ofReal (1 + nrdNormW (a : F) (b : F) z) ∂muInfVec F (Fin 4) ≠ ⊤) :
    Tendsto (fun s => (s - 2) * (quatZeta (a : F) (b : F) Φ s).toReal) (𝓝[>] 2)
      (𝓝 (dedekindZeta_residue F * (|(NumberField.discr F : ℝ)| ^ (-(4 : ℝ) / 2) *
        (∫⁻ z, Φ z ∂muInfVec F (Fin 4)).toReal))) := by
  have hI : ∫⁻ z, Φ z ∂muInfVec F (Fin 4) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin (lintegral_mono fun z => ?_)
    have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + nrdNormW (a : F) (b : F) z) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (absDetInf_nonneg _))
    calc Φ z = Φ z * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_right h1 _
  have h1 := (ENNReal.tendsto_toReal hI).comp (tendsto_quatInfZeta (a : F) (b : F) hΦ hfin)
  have h2 := tendsto_mul_quatFinZeta ha0 hb0
  have h3 := h1.mul h2
  rw [show dedekindZeta_residue F * (|(NumberField.discr F : ℝ)| ^ (-(4 : ℝ) / 2) *
    (∫⁻ z, Φ z ∂muInfVec F (Fin 4)).toReal) = (∫⁻ z, Φ z ∂muInfVec F (Fin 4)).toReal *
      (|(NumberField.discr F : ℝ)| ^ (-(4 : ℝ) / 2) * dedekindZeta_residue F) by ring]
  refine h3.congr' (eventually_nhdsWithin_of_forall fun s hs => ?_)
  simp only [Function.comp_apply]
  rw [quatZeta_eq_mul _ _ hΦ (by linarith [show (2 : ℝ) < s from hs]), ENNReal.toReal_mul]
  ring

end Global

end

end QuadFormsKB.Tamagawa.Measure.Weil
