import QuadFormsKB.Tamagawa.Measure.Weil.QuatPoisson

/-!
# The theta sum over $\mathbb H^\times$ and the bound on the dual remainder

* **`tsum_right_eq_quatTheta_star`**: the sum produced by unfolding over $\mathbb H^\times$ acting on the left,
  $\sum_{\xi\in\mathbb H}\Phi(\xi x)$, equals $S(\bar x) = \sum_\xi\Phi(\bar x\xi)$ (the Gaussian test function is invariant
  under the canonical involution).
* **`quatDualRem_le`** (abstract form): if $L_0\subseteq L_U$ and $K(M)\le K$, the dual remainder of the lattice
  $cM\,L_U$ is at most the theta tail $\sum_{0\ne\zeta\in L_0^\vee}e^{-\pi q(\zeta)/(c^2K)}$ (the map $\eta\mapsto(cM)^{\mathsf T}\eta$
  embeds $(cML_U)^\vee$ into $L_0^\vee$, and $q((cM)^{\mathsf T}\eta)\le c^2K\,q(\eta)$).
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology Set NumberField.mixedEmbedding Matrix
open scoped ENNReal NNReal Quaternion Pointwise Classical Real

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

set_option synthInstance.maxHeartbeats 400000

local notation "V" => mixedSpace F
local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### Invariance under the canonical involution -/

section Star

variable {a b : F}

theorem gR_neg (m : V) : gR (-m) = gR m := by
  simp [gR, neg_sq]

theorem quatTestFn_star (y : QuatAdele a b) : quatTestFn a b gaussPhi (star y) = quatTestFn a b gaussPhi y := by
  have hc : ∀ i, quatCoord a b (star y) i = (if i = 0 then quatCoord a b y i else -quatCoord a b y i) := by
    intro i; fin_cases i
    · show (star y).re = y.re; simp
    · show (star y).imI = -y.imI; simp
    · show (star y).imJ = -y.imJ; simp
    · show (star y).imK = -y.imK; simp
  unfold quatTestFn gaussPhi
  congr 1
  · congr 1
    simp only [gV, Fin.prod_univ_four, hc]
    simp [Prod.fst_neg, gR_neg]
  · have hmem : (fun i => (quatCoord a b (star y) i).2) ∈ Set.pi univ (fun _ => (OHat : Set AF)) ↔
        (fun i => (quatCoord a b y i).2) ∈ Set.pi univ (fun _ => (OHat : Set AF)) := by
      simp only [Set.mem_pi, mem_univ, true_imp_iff, hc]
      refine forall_congr' fun i => ?_
      split_ifs
      · rfl
      · rw [Prod.snd_neg]
        exact ⟨fun h => by simpa using neg_mem_OHat h, neg_mem_OHat⟩
    by_cases h : (fun i => (quatCoord a b y i).2) ∈ Set.pi univ (fun _ => (OHat : Set AF))
    · rw [indicator_of_mem h, indicator_of_mem (hmem.mpr h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (hmem.mp h'))]

/-- **The left-unfolded theta sum is $S(\bar x)$**: $\sum_{\xi\in\mathbb H}\Phi(\xi x) = \sum_{\xi\in\mathbb H}\Phi(\bar x\xi)$. -/
theorem tsum_right_eq_quatTheta_star (x : (QuatAdele a b)ˣ) :
    ∑' ξ : ℍ[F,a,b], quatTestFn a b gaussPhi (quatDiagRing a b ξ * (x : QuatAdele a b)) =
      quatTheta a b (quatStarUnit x) := by
  rw [quatTheta, ← (starAddEquiv (R := ℍ[F,a,b])).toEquiv.tsum_eq]
  refine tsum_congr fun ξ => ?_
  rw [← quatTestFn_star, star_mul]
  simp [quatStarUnit, quatDiagRing_star]

end Star

/-! ### The dual remainder of a twisted lattice -/

section Remainder

theorem matK_transpose_smul (c : ℝ) (M : Matrix (Fin 4) (Fin 4) V) :
    matK ((c • M).transpose) = c ^ 2 * matK M := by
  rw [matK_transpose, matK_smul]

/-- **The dual remainder of $cML_U$ is dominated by a theta tail of $L_0\subseteq L_U$.** -/
theorem dualRem_le (U : AddSubgroup (Fin 4 → AF)) (L₀ : Submodule ℤ (Fin 4 → mixedSpace F))
    (hL₀ : L₀ ≤ adelicLat U) (M N : Matrix (Fin 4) (Fin 4) V) (hMN : M * N = 1) {c : ℝ} (hc : 0 < c)
    {K : ℝ} (hK : 0 < K) (hMK : matK M ≤ K) :
    ∑' η : {η : Fin 4 → V | ∀ w ∈ adelicLat U, ∃ n : ℤ, betaV F (Fin 4) η ((c • M) *ᵥ w) = n},
        (if (η : Fin 4 → V) = 0 then 0 else gaussPhi (η : Fin 4 → V)) ≤
      ∑' ζ : (betaV F (Fin 4)).dualSubmodule L₀, (if (ζ : Fin 4 → V) = 0 then 0 else
        ENNReal.ofReal (Real.exp (-π * (1 / c ^ 2) * qV (ζ : Fin 4 → V) / K))) := by
  set S := {η : Fin 4 → V | ∀ w ∈ adelicLat U, ∃ n : ℤ, betaV F (Fin 4) η ((c • M) *ᵥ w) = n}
  set T := (c • M).transpose
  have hmem : ∀ η ∈ S, T *ᵥ η ∈ (betaV F (Fin 4)).dualSubmodule L₀ := by
    intro η hη
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro w hw
    obtain ⟨n, hn⟩ := hη w (hL₀ hw)
    refine Submodule.mem_one.mpr ⟨n, ?_⟩
    rw [show algebraMap ℤ ℝ n = (n : ℝ) by simp, ← hn, betaV_isSymm.eq, betaV_mulVec, betaV_isSymm.eq]
  have hTinj : Function.Injective (T *ᵥ ·) := by
    intro η η' h
    have hNM : N * M = 1 := mul_eq_one_comm.mp hMN
    have hinv : (c⁻¹ • N).transpose * T = 1 := by
      simp only [T, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.transpose_mul, hMN,
        Matrix.transpose_one, smul_smul, inv_mul_cancel₀ hc.ne', mul_inv_cancel₀ hc.ne', one_smul]
    have := congrArg ((c⁻¹ • N).transpose *ᵥ ·) h
    simpa only [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] using this
  set f : S → (betaV F (Fin 4)).dualSubmodule L₀ := fun η => ⟨T *ᵥ (η : Fin 4 → V), hmem η η.2⟩
  have hf : Function.Injective f := fun η η' h => Subtype.ext (hTinj (congrArg Subtype.val h))
  set g : (betaV F (Fin 4)).dualSubmodule L₀ → ℝ≥0∞ := fun ζ => if (ζ : Fin 4 → V) = 0 then 0 else
    ENNReal.ofReal (Real.exp (-π * (1 / c ^ 2) * qV (ζ : Fin 4 → V) / K))
  refine le_trans (ENNReal.tsum_le_tsum fun η => ?_) (ENNReal.tsum_comp_le_tsum_of_injective hf g)
  by_cases h0 : (η : Fin 4 → V) = 0
  · simp only [h0, ↓reduceIte]; exact bot_le
  · simp only [h0, ↓reduceIte]
    have hf0 : ((f η : (betaV F (Fin 4)).dualSubmodule L₀) : Fin 4 → V) ≠ 0 := by
      intro h; apply h0
      have : T *ᵥ (η : Fin 4 → V) = T *ᵥ 0 := by rw [Matrix.mulVec_zero]; exact h
      exact hTinj this
    simp only [g, hf0, ↓reduceIte, gaussPhi, gV_eq_exp]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have hq := qV_mulVec_le T (η : Fin 4 → V)
    rw [matK_transpose_smul] at hq
    have hq0 := qV_nonneg (η : Fin 4 → V)
    have hle : qV (T *ᵥ (η : Fin 4 → V)) ≤ c ^ 2 * K * qV (η : Fin 4 → V) :=
      hq.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMK (sq_nonneg c)) hq0)
    have hc2 : 0 < c ^ 2 := by positivity
    have h1 : (1 / c ^ 2) * qV (T *ᵥ (η : Fin 4 → V)) / K ≤ qV (η : Fin 4 → V) := by
      rw [div_le_iff₀ hK, one_div, inv_mul_le_iff₀ hc2]
      linarith [hle]
    have h2 : -π * (1 / c ^ 2) * qV (T *ᵥ (η : Fin 4 → V)) / K =
        -π * ((1 / c ^ 2) * qV (T *ᵥ (η : Fin 4 → V)) / K) := by ring
    rw [h2]
    nlinarith [Real.pi_pos]

end Remainder

/-! ### The central section and the uniform bound -/

section Uniform

variable {a b : F}

theorem adelicLat_mono {U U' : AddSubgroup (Fin 4 → AF)} (h : U ≤ U') : adelicLat U ≤ adelicLat U' := by
  rintro _ ⟨ξ, hξ, rfl⟩
  exact ⟨ξ, h hξ, rfl⟩

/-- $d\hat{\mathcal O}^4$. -/
def dOHat (d : ℕ) : AddSubgroup (Fin 4 → AF) :=
  AddSubgroup.pi univ fun _ => (OHatSub (F := F)).map (AddMonoidHom.mulLeft (d : AF))

theorem mem_dOHat {d : ℕ} {c : Fin 4 → AF} : c ∈ dOHat d ↔ ∀ i, ∃ x ∈ OHat, (d : AF) * x = c i := by
  simp [dOHat, AddSubgroup.mem_pi]
  rfl

theorem dOHat_upper (d : ℕ) : ∀ c ∈ dOHat (F := F) d, ∀ i, ((1 : ℕ) : AF) * c i ∈ OHat := by
  intro c hc i
  obtain ⟨x, hx, hxc⟩ := mem_dOHat.mp hc i
  rw [Nat.cast_one, one_mul, ← hxc]; exact natCast_mul_mem_OHat hx d

theorem dOHat_lower (d : ℕ) : ∀ ξ : Fin 4 → 𝓞 F, jFin F (Fin 4) (fun i => (d : F) * (ξ i : F)) ∈ dOHat d := by
  intro ξ
  refine mem_dOHat.mpr fun i => ⟨algebraMap F AF (ξ i), (algebraMap_mem_OHat_iff _).mpr ⟨ξ i, rfl⟩, ?_⟩
  simp

variable (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
  (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)

include ha hb in
theorem dOHat_le_quatUf {d : ℕ} {w : (QuatFin a b)ˣ} (hw : (d : QuatFin a b) * (w : QuatFin a b) ∈ lamHat a b) :
    dOHat d ≤ quatUf w := by
  intro c hc
  choose x hx hxc using mem_dOHat.mp hc
  rw [mem_quatUf]
  have hsymm : (quatFinCoord a b).symm c = (d : QuatFin a b) * (quatFinCoord a b).symm x := by
    rw [natCast_mul_quatFin]
    ext <;> simp [quatFinCoord_symm_re, quatFinCoord_symm_imI, quatFinCoord_symm_imJ, quatFinCoord_symm_imK, hxc]
  rw [hsymm, ← mul_assoc, ← (Nat.cast_commute d (w : QuatFin a b)).eq]
  exact mul_mem_lamHat ha hb hw ((mem_lamHat_symm_iff x).mpr hx)

end Uniform

/-! ### The central section -/

section Section

variable {a b : F}

variable (F) in
/-- The archimedean scale of the central section: $c(s) = (e^{s/2})^{1/[F:\mathbb Q]}$. -/
def sectionScale (s : Multiplicative ℝ) : ℝ := Real.exp (Multiplicative.toAdd s / 2) ^ ((Module.finrank ℚ F : ℝ)⁻¹)

theorem sectionScale_pos (s : Multiplicative ℝ) : 0 < sectionScale F s := Real.rpow_pos_of_pos (Real.exp_pos _) _

theorem quatSectionHom_val (s : Multiplicative ℝ) :
    ((quatSectionHom a b s : (QuatAdele a b)ˣ) : QuatAdele a b) =
      algebraMap (Adeles F) (QuatAdele a b) (normSection F (Real.exp (Multiplicative.toAdd s / 2)) (Real.exp_pos _)) :=
  rfl

theorem star_quatSectionHom (s : Multiplicative ℝ) :
    star ((quatSectionHom a b s : (QuatAdele a b)ˣ) : QuatAdele a b) = quatSectionHom a b s := by
  rw [quatSectionHom_val, QuaternionAlgebra.coe_algebraMap, QuaternionAlgebra.star_coe]

theorem quatStarUnit_mul_section (y : (QuatAdele a b)ˣ) (s : Multiplicative ℝ) :
    quatStarUnit (y * quatSectionHom a b s) = quatSectionHom a b s * quatStarUnit y := by
  refine Units.ext ?_
  change star ((y : QuatAdele a b) * (quatSectionHom a b s : QuatAdele a b)) = _
  rw [star_mul, star_quatSectionHom]
  rfl

theorem uFin_quatSectionHom (s : Multiplicative ℝ) : uFin (quatSectionHom a b s) = 1 :=
  Units.ext (QuaternionAlgebra.ext rfl rfl rfl rfl)

theorem normSection_fst (t : ℝ) (ht : 0 < t) :
    ((normSection F t ht : (Adeles F)ˣ) : Adeles F).1 =
      algebraMap ℝ (mixedSpace F) (t ^ ((Module.finrank ℚ F : ℝ)⁻¹)) := by
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · change t ^ ((Module.finrank ℚ F : ℝ)⁻¹) = _
    simp [Algebra.algebraMap_eq_smul_one]
  · change ((t ^ ((Module.finrank ℚ F : ℝ)⁻¹) : ℝ) : ℂ) = _
    simp [Algebra.algebraMap_eq_smul_one]

theorem uInf_quatSectionHom (s : Multiplicative ℝ) :
    ((uInf (quatSectionHom a b s) : (QuatInf a b)ˣ) : QuatInf a b) =
      algebraMap (mixedSpace F) (QuatInf a b) (algebraMap ℝ (mixedSpace F) (sectionScale F s)) := by
  rw [sectionScale, ← normSection_fst _ (Real.exp_pos _)]
  exact QuaternionAlgebra.ext rfl rfl rfl rfl

theorem lmInf_algebraMap_mul (m : mixedSpace F) (z : QuatInf a b) :
    lmInf (algebraMap (mixedSpace F) (QuatInf a b) m * z) = m • lmInf z := by
  rw [lmInf_mul]
  have : lmInf (algebraMap (mixedSpace F) (QuatInf a b) m) = algebraMap (mixedSpace F) _ m := by
    unfold lmInf
    exact AlgHom.commutes _ m
  rw [this, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]

theorem smul_matrix_algebraMap (c : ℝ) (M : Matrix (Fin 4) (Fin 4) (mixedSpace F)) :
    (algebraMap ℝ (mixedSpace F) c) • M = c • M := by
  exact algebraMap_smul (mixedSpace F) c M

end Section

/-! ### The uniform bound on the dual remainder -/

section Bound

variable {a b : F}

theorem continuous_lmInf : Continuous (lmInf (a := a) (b := b)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold lmInf
  simp_rw [Algebra.leftMulMatrix_eq_repr_mul]
  exact (continuous_apply i).comp ((continuous_quatInfCoord a b).comp (continuous_id.mul continuous_const))

theorem continuous_matK : Continuous (matK (F := F) (ι := Fin 4)) := by
  unfold matK
  fun_prop

theorem continuous_quatStarUnit : Continuous (quatStarUnit (a := a) (b := b)) := by
  refine Units.continuous_iff.mpr ⟨(continuous_star_quat a b).comp Units.continuous_val, ?_⟩
  exact (continuous_star_quat a b).comp Units.continuous_coe_inv

theorem continuous_uInf_val : Continuous fun x : (QuatAdele a b)ˣ => ((uInf x : (QuatInf a b)ˣ) : QuatInf a b) :=
  continuous_fst.comp ((continuous_quatAdeleRingEquiv a b).comp Units.continuous_val)

theorem continuous_uFin : Continuous fun x : (QuatAdele a b)ˣ => uFin x :=
  continuous_snd.comp (quatUnitsEquiv a b).continuous

theorem uFin_mul (x y : (QuatAdele a b)ˣ) : uFin (x * y) = uFin x * uFin y := by
  simp only [uFin, map_mul, Prod.snd_mul]

theorem uInf_mul (x y : (QuatAdele a b)ˣ) : uInf (x * y) = uInf x * uInf y := by
  simp only [uInf, map_mul, Prod.fst_mul]

variable (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
  (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)

theorem sectionScale_le_one {s : Multiplicative ℝ} (hs : Multiplicative.toAdd s ≤ 0) : sectionScale F s ≤ 1 := by
  refine Real.rpow_le_one (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith)) ?_
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

/-- `dualRem_le` for a matrix given as $M' = cM$. -/
theorem dualRem_le' (U : AddSubgroup (Fin 4 → AF)) (L₀ : Submodule ℤ (Fin 4 → mixedSpace F))
    (hL₀ : L₀ ≤ adelicLat U) (M' M N : Matrix (Fin 4) (Fin 4) V) {c : ℝ} (hM' : M' = c • M) (hMN : M * N = 1)
    (hc : 0 < c) {K : ℝ} (hK : 0 < K) (hMK : matK M ≤ K) :
    ∑' η : {η : Fin 4 → V | ∀ w ∈ adelicLat U, ∃ n : ℤ, betaV F (Fin 4) η (M' *ᵥ w) = n},
        (if (η : Fin 4 → V) = 0 then 0 else gaussPhi (η : Fin 4 → V)) ≤
      ∑' ζ : (betaV F (Fin 4)).dualSubmodule L₀, (if (ζ : Fin 4 → V) = 0 then 0 else
        ENNReal.ofReal (Real.exp (-π * (1 / c ^ 2) * qV (ζ : Fin 4 → V) / K))) := by
  subst hM'
  exact dualRem_le U L₀ hL₀ M N hMN hc hK hMK

theorem lmInf_uInf_section (s : Multiplicative ℝ) (ybar : (QuatAdele a b)ˣ) :
    lmInf ((uInf (quatSectionHom a b s * ybar) : (QuatInf a b)ˣ) : QuatInf a b) =
      sectionScale F s • lmInf ((uInf ybar : (QuatInf a b)ˣ) : QuatInf a b) := by
  rw [uInf_mul, Units.val_mul, uInf_quatSectionHom, lmInf_algebraMap_mul, smul_matrix_algebraMap]

theorem uFin_section (s : Multiplicative ℝ) (ybar : (QuatAdele a b)ˣ) :
    uFin (quatSectionHom a b s * ybar) = uFin ybar := by
  rw [uFin_mul, uFin_quatSectionHom, one_mul]

/-- The bound for one $\bar y$ and one $s$, given the auxiliary lattice $L_0$ and the matrix bound $K$. -/
theorem quatDualRem_section_le (L₀ : Submodule ℤ (Fin 4 → mixedSpace F)) (s : Multiplicative ℝ)
    (ybar : (QuatAdele a b)ˣ) (hL₀ : L₀ ≤ adelicLat (quatUf (uFin ybar))) {K : ℝ} (hK : 0 < K)
    (hMK : matK (lmInf ((uInf ybar : (QuatInf a b)ˣ) : QuatInf a b)) ≤ K) :
    quatDualRem (quatSectionHom a b s * ybar) ≤
      ∑' ζ : (betaV F (Fin 4)).dualSubmodule L₀, (if (ζ : Fin 4 → V) = 0 then 0 else
        ENNReal.ofReal (Real.exp (-π * (1 / sectionScale F s ^ 2) * qV (ζ : Fin 4 → V) / K))) := by
  have hMN : lmInf ((uInf ybar : (QuatInf a b)ˣ) : QuatInf a b) *
      lmInf (((uInf ybar)⁻¹ : (QuatInf a b)ˣ) : QuatInf a b) = 1 := by
    rw [← lmInf_mul, Units.mul_inv, lmInf_one]
  have hL₀' : L₀ ≤ adelicLat (quatUf (uFin (quatSectionHom a b s * ybar))) := by rw [uFin_section]; exact hL₀
  unfold quatDualRem quatDualSet
  exact dualRem_le' _ _ hL₀' _ _ _ (lmInf_uInf_section s ybar) hMN (sectionScale_pos s) hK hMK

include ha hb in
/-- **The uniform theta bound**: for a compact $C\subseteq\mathbb H_{\mathbb A}^1$ there are $0\le\delta < 1$ and $\Theta < \infty$
with $R(s(t)\,\bar y)\le\delta^{c(t)^{-2}-1}\Theta$ for all $y\in C$ and $\log t\le0$ ($c(t)$ the archimedean scale of the
central section $s(t)$). -/
theorem exists_quatDualRem_bound {C : Set (quatOne a b)} (hC : IsCompact C) :
    ∃ δ : ℝ, 0 ≤ δ ∧ δ < 1 ∧ ∃ Θ : ℝ≥0∞, Θ ≠ ⊤ ∧ ∀ y ∈ C, ∀ s : Multiplicative ℝ, Multiplicative.toAdd s ≤ 0 →
      quatDualRem (quatSectionHom a b s * quatStarUnit (y : (QuatAdele a b)ˣ)) ≤
        ENNReal.ofReal (δ ^ (1 / sectionScale F s ^ 2 - 1)) * Θ := by
  obtain ⟨d, hd0, hd⟩ := exists_nat_mul_mem_lamHat (hC.image (continuous_uFin.comp
    (continuous_quatStarUnit.comp continuous_subtype_val)))
  have : DiscreteTopology (adelicLat (dOHat (F := F) d)) :=
    discreteTopology_adelicLat (dOHat d) one_ne_zero (dOHat_upper d)
  have : IsZLattice ℝ (adelicLat (dOHat (F := F) d)) := isZLattice_adelicLat (dOHat d) hd0 (dOHat_lower d)
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn (continuous_matK.comp (continuous_lmInf.comp
    (continuous_uInf_val.comp (continuous_quatStarUnit.comp continuous_subtype_val)))).continuousOn
  have hK : (0 : ℝ) < max B 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨δ, hδ0, hδ1, Θ, hΘ, hbound⟩ := theta_tail_bound (adelicLat (dOHat (F := F) d)) hK
  refine ⟨δ, hδ0, hδ1, Θ, hΘ, fun y hy s hs => ?_⟩
  have hMK : matK (lmInf ((uInf (quatStarUnit (y : (QuatAdele a b)ˣ)) : (QuatInf a b)ˣ) : QuatInf a b)) ≤ max B 1 :=
    (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hB y hy).trans (le_max_left _ _))
  have hL₀ := adelicLat_mono (dOHat_le_quatUf ha hb (hd _ ⟨y, hy, rfl⟩).1)
  refine (quatDualRem_section_le _ s _ hL₀ hK hMK).trans ?_
  have hc := sectionScale_pos (F := F) s
  have hl : 1 ≤ 1 / sectionScale F s ^ 2 := by
    rw [le_div_iff₀ (by positivity), one_mul]
    exact pow_le_one₀ hc.le (sectionScale_le_one hs)
  exact hbound (1 / sectionScale F s ^ 2) hl

end Bound

end

end QuadFormsKB.Tamagawa.Measure.Weil
