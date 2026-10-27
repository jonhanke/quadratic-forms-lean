import QuadFormsKB.Tamagawa.Measure.Weil.BinaryIsotropic

/-!
# The hyperbolic plane: $SO(H)\cong\mathbb G_m$ on adelic points

For $H = x_0x_1$ over $\mathcal O_F$: `hypEquiv : \mathbb A_F^\times \cong SO(H)(\mathbb A)` ($t\mapsto\mathrm{diag}(t,t^{-1})$ at every
place, a topological group isomorphism, inverse to `isoChar`), carrying $F^\times$ onto $SO(H)(F)$
(`map_diagUnitsSub_hypEquiv`), $\hat{\mathcal O}^\times$ onto $SO(\hat{\mathcal O}^2)$ (`hypFinEquiv_preimage_KSO`), and the
Tamagawa measure of $\mathbb A_f^\times$ onto $\operatorname{vol}(\hat{\mathcal O}^\times)\,\mu_f$ (`map_muFinUnits_hypFinEquiv`;
Siegel's density $\alpha_v(H,H) = \lambda_v$ at every $v$, `siegelDensity_hypForm`). Indices are 0-based.
-/

open MeasureTheory Measure Set Topology Matrix Filter
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa QuadFormsKB.QuadForm QuadFormsKB.Siegel QuadFormsKB.Tamagawa.ArchSOMeasure
  QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F : Type} [Field F] [NumberField F]

/-! ### The form and its isotropic vectors -/

variable (F) in
/-- **The hyperbolic plane** $H(x_0,x_1) = x_0x_1$ over $\mathcal O_F$. -/
abbrev hypForm : QuadForm (𝓞 F) 2 := QuadFormsKB.LocalDensity.DVR.hyperbolic (𝓞 F)

theorem hessian_hypForm_det : (hypForm F).hessian.det = -1 := by
  simp [hypForm, QuadFormsKB.LocalDensity.DVR.hyperbolic, QuadForm.hessian, QuadForm.ofUpper, Matrix.det_fin_two]

theorem nondegenerate_hypForm : (hypForm F).Nondegenerate := by
  unfold QuadForm.Nondegenerate
  rw [hessian_hypForm_det]; exact neg_ne_zero.mpr one_ne_zero

variable (F) in
/-- The isotropic vector $e = (1,0)$ of the hyperbolic plane. -/
def hypE : Fin 2 → F := ![1, 0]

theorem isIsoVec_hypE : IsIsoVec (hypForm F) (hypE (F := F)) := by
  refine ⟨?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp [hypE] at this
  · simp [qF, hypE, hypForm, QuadFormsKB.LocalDensity.DVR.hyperbolic, QuadForm.eval, QuadForm.evalIn,
      QuadForm.ofUpper, QuadForm.map, Fin.sum_univ_two]

theorem isIsoVec_hypE' : IsIsoVec (hypForm F) (![0, 1] : Fin 2 → F) := by
  refine ⟨?_, ?_⟩
  · intro h
    have := congrFun h 1
    simp at this
  · simp [qF, hypForm, QuadFormsKB.LocalDensity.DVR.hyperbolic, QuadForm.eval, QuadForm.evalIn,
      QuadForm.ofUpper, QuadForm.map, Fin.sum_univ_two]

/-! ### Local description: $SO(H)(K) = \{\mathrm{diag}(t,t^{-1})\}$ -/

section Local

/-- The Hessian matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ of the hyperbolic plane. -/
def hypH (K : Type*) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

theorem hessian_hypForm_map {K : Type*} [Field K] (ι : F →+* K) :
    ((hypForm F).map (algebraMap (𝓞 F) F)).hessian.map ι = hypH K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hypH, hypForm, QuadFormsKB.LocalDensity.DVR.hyperbolic, QuadForm.hessian, QuadForm.ofUpper, QuadForm.map]

variable {K : Type*} [Field K]

/-- $\mathrm{diag}(t,t^{-1})\in\mathrm{GL}_2(K)$. -/
def hypDiagGL (t : Kˣ) : GL (Fin 2) K where
  val := !![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)]
  inv := !![((t⁻¹ : Kˣ) : K), 0; 0, (t : K)]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem hypDiagGL_val (t : Kˣ) :
    ((hypDiagGL t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)] := rfl

/-- $t\mapsto\mathrm{diag}(t,t^{-1})$. -/
def hypDiagGLHom : Kˣ →* GL (Fin 2) K where
  toFun := hypDiagGL
  map_one' := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' t s := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem hypDiagGL_injective : Function.Injective (hypDiagGL (K := K)) := fun t s h => by
  have := congrFun (congrFun (congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) h) 0) 0
  exact Units.ext (by simpa using this)

theorem diagMat_conj (t : Kˣ) :
    ((hypDiagGL t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ * hypH K * (hypDiagGL t : GL (Fin 2) K) = hypH K := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hypH, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

theorem diagMat_det (t : Kˣ) : ((hypDiagGL t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  simp [Matrix.det_fin_two]

/-- **An element of $SO(H)(K)$ is $\mathrm{diag}(t,t^{-1})$**: $M_{01} = M_{10} = 0$, $M_{00}M_{11} = 1$. -/
theorem entries_of_hess [CharZero K] {M : Matrix (Fin 2) (Fin 2) K} (h : Mᵀ * hypH K * M = hypH K)
    (hd : M.det = 1) : M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 0 0 * M 1 1 = 1 := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h11 := congrFun (congrFun h 1) 1
  simp [hypH, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] at h00 h01 h11
  rw [Matrix.det_fin_two] at hd
  have e1 : M 0 0 * M 1 1 = 1 := by
    have : (2 : K) * (M 0 0 * M 1 1) = 2 * 1 := by linear_combination h01 + hd
    exact mul_left_cancel₀ two_ne_zero this
  have n0 : M 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one e1
  have n1 : M 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one e1
  refine ⟨?_, ?_, e1⟩
  · have : M 1 1 * M 0 1 = 0 := by linear_combination h11 / 2
    exact (mul_eq_zero.mp this).resolve_left n1
  · have : M 0 0 * M 1 0 = 0 := by linear_combination h00 / 2
    exact (mul_eq_zero.mp this).resolve_left n0

theorem eq_diagGL_of_hess [CharZero K] {g : GL (Fin 2) K}
    (h : (g : Matrix (Fin 2) (Fin 2) K)ᵀ * hypH K * g = hypH K) (hd : (g : Matrix (Fin 2) (Fin 2) K).det = 1) :
    ∃ t : Kˣ, hypDiagGL t = g ∧ (t : K) = (g : Matrix (Fin 2) (Fin 2) K) 0 0 := by
  obtain ⟨h01, h10, h2⟩ := entries_of_hess h hd
  have n0 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one h2
  refine ⟨Units.mk0 _ n0, ?_, rfl⟩
  ext i j
  have h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = ((g : Matrix (Fin 2) (Fin 2) K) 0 0)⁻¹ :=
    eq_inv_of_mul_eq_one_right h2
  fin_cases i <;> fin_cases j <;> simp [h01, h10, h11]

/-- $\mathrm{eigVal}$ on $\iota(e)$, $e = (1,0)$, is the $(0,0)$ entry. -/
theorem eigVal_hypE (ι : F →+* K) (M : Matrix (Fin 2) (Fin 2) K) : eigVal ι (hypE F) M = M 0 0 := by
  have hi : isoIdx (hypE F) = 0 := by simp [isoIdx, hypE]
  rw [eigVal, hi]
  simp [hypE, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end Local

/-! ### Topological isomorphisms $K^\times\cong SO(H)(K)$ at every place -/

section Equiv

variable {K : Type*} [Field K] [TopologicalSpace K]

omit [TopologicalSpace K] in
theorem exists_diagGL_of_hess [CharZero K] {g : GL (Fin 2) K}
    (h : (g : Matrix (Fin 2) (Fin 2) K)ᵀ * hypH K * g = hypH K) (hd : (g : Matrix (Fin 2) (Fin 2) K).det = 1) :
    ∃ t : Kˣ, hypDiagGL t = g :=
  (eq_diagGL_of_hess h hd).imp fun _ h => h.1

theorem continuous_diagGL [IsTopologicalRing K] : Continuous (hypDiagGL (K := K)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [hypDiagGL, -Units.val_inv_eq_inv_val] <;>
      first | exact continuous_const | exact (Units.continuous_val (M := K)) | exact (Units.continuous_coe_inv (M := K))
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [hypDiagGL, -Units.val_inv_eq_inv_val] <;>
      first | exact continuous_const | exact (Units.continuous_val (M := K)) | exact (Units.continuous_coe_inv (M := K))

theorem continuous_of_diagGL_eq {X : Type*} [TopologicalSpace X] {f : X → Kˣ} {G : X → GL (Fin 2) K}
    (hG : Continuous G) (h : ∀ x, hypDiagGL (f x) = G x) : Continuous f := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have : (Units.val ∘ f) = fun x => ((G x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 := by
      funext x; rw [← h x]; rfl
    rw [this]; exact (Units.continuous_val.comp hG).matrix_elem 0 0
  · have : (fun x => (((f x)⁻¹ : Kˣ) : K)) = fun x => ((G x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 := by
      funext x; rw [← h x]; rfl
    rw [this]; exact (Units.continuous_val.comp hG).matrix_elem 1 1

/-- **A group $G$ whose image in $\mathrm{GL}_2(K)$ (inducing inclusion) is exactly $\{\mathrm{diag}(t,t^{-1})\}$ is
$K^\times$ as a topological group.** -/
def diagEquivOfIncl [IsTopologicalRing K] {G : Type*} [Group G] [TopologicalSpace G] (incl : G →* GL (Fin 2) K)
    (hinj : Function.Injective incl) (hind : Topology.IsInducing incl) (φ : Kˣ →* G)
    (hφ : ∀ t, incl (φ t) = hypDiagGL t) (hrange : ∀ g : G, ∃ t : Kˣ, hypDiagGL t = incl g) : Kˣ ≃ₜ* G :=
  let hφinj : Function.Injective φ := fun t s h => hypDiagGL_injective (by rw [← hφ, ← hφ, h])
  let hsurj : Function.Surjective φ := fun g => by
    obtain ⟨t, ht⟩ := hrange g
    exact ⟨t, hinj (by rw [hφ, ht])⟩
  let e : Kˣ ≃* G := MulEquiv.ofBijective φ ⟨hφinj, hsurj⟩
  { e with
    continuous_toFun := hind.continuous_iff.mpr (by
      convert continuous_diagGL (K := K) using 1
      exact funext hφ)
    continuous_invFun := continuous_of_diagGL_eq hind.continuous (fun g => by
      rw [← hφ]; exact congrArg incl (e.apply_symm_apply g)) }

theorem diagEquivOfIncl_apply [IsTopologicalRing K] {G : Type*} [Group G] [TopologicalSpace G] (incl : G →* GL (Fin 2) K)
    (hinj : Function.Injective incl) (hind : Topology.IsInducing incl) (φ : Kˣ →* G)
    (hφ : ∀ t, incl (φ t) = hypDiagGL t) (hrange : ∀ g : G, ∃ t : Kˣ, hypDiagGL t = incl g) (t : Kˣ) :
    diagEquivOfIncl incl hinj hind φ hφ hrange t = φ t := rfl

end Equiv

section Places

local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (hypForm F)
local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! #### finite places -/

theorem hypDiagGL_mem_orthGroup (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    hypDiagGL t ∈ orthGroup QF (v.adicCompletion F) :=
  (mem_orthGroup QF).mpr (by rw [hessian_hypForm_map]; exact diagMat_conj t)

/-- $t\mapsto\mathrm{diag}(t,t^{-1})$, $F_v^\times\to SO(H)(F_v)$. -/
def hypSOV (v : HeightOneSpectrum (𝓞 F)) : (v.adicCompletion F)ˣ →* soSub QF (v.adicCompletion F) :=
  (hypDiagGLHom.codRestrict (orthGroup QF (v.adicCompletion F)) (hypDiagGL_mem_orthGroup v)).codRestrict
    (soSub QF (v.adicCompletion F)) fun t => mem_soSub.mpr (diagMat_det t)

/-- The inclusion $SO(H)(F_v)\to\mathrm{GL}_2(F_v)$. -/
def hypInclV (v : HeightOneSpectrum (𝓞 F)) : soSub QF (v.adicCompletion F) →* GL (Fin 2) (v.adicCompletion F) :=
  (orthGroup QF (v.adicCompletion F)).subtype.comp (soSub QF (v.adicCompletion F)).subtype

/-- **$F_v^\times\cong SO(H)(F_v)$**, $t\mapsto\mathrm{diag}(t,t^{-1})$. -/
def hypEquivV (v : HeightOneSpectrum (𝓞 F)) : (v.adicCompletion F)ˣ ≃ₜ* soSub QF (v.adicCompletion F) :=
  diagEquivOfIncl (hypInclV v) (Subtype.val_injective.comp Subtype.val_injective)
    (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal) (hypSOV v) (fun _ => rfl)
    (fun g => exists_diagGL_of_hess (by
      have := (hessian_of_mem_soSub v g).1
      rw [hessian_hypForm_map] at this; exact this) (hessian_of_mem_soSub v g).2)

theorem hypEquivV_apply (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    ((hypEquivV v t : soSub QF (v.adicCompletion F)) : orthGroup QF (v.adicCompletion F)) =
      ⟨hypDiagGL t, hypDiagGL_mem_orthGroup v t⟩ := rfl

theorem omat_hypEquivV (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    omat ((hypEquivV v t : soSub QF (v.adicCompletion F)) : orthGroup QF (v.adicCompletion F)) =
      !![(t : v.adicCompletion F), 0; 0, ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)] := rfl

theorem isoCharV_hypEquivV (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    isoCharV nondegenerate_hypForm (isIsoVec_hypE (F := F)) v (hypEquivV v t) = (t : v.adicCompletion F) := by
  show eigVal _ _ _ = _
  rw [eigVal_hypE, omat_hypEquivV]; rfl

/-! #### real places -/

theorem hypDiagGL_mem_soReal (w : {w : InfinitePlace F // w.IsReal}) (t : ℝˣ) :
    hypDiagGL t ∈ soReal (QRe (hypForm F) w) := by
  rw [mem_soReal_iff, QRe, hessian_map_NF, hessian_hypForm_map]
  exact ⟨diagMat_conj t, diagMat_det t⟩

/-- $t\mapsto\mathrm{diag}(t,t^{-1})$, $\mathbb R^\times\to SO(H^{\sigma_w})(\mathbb R)$. -/
def hypSOR (w : {w : InfinitePlace F // w.IsReal}) : ℝˣ →* ArchSO (QRe (hypForm F) w) :=
  (hypDiagGLHom.codRestrict (soReal (QRe (hypForm F) w)) (hypDiagGL_mem_soReal w) :)

/-- **$\mathbb R^\times\cong SO(H^{\sigma_w})(\mathbb R)$**. -/
def hypEquivR (w : {w : InfinitePlace F // w.IsReal}) : ℝˣ ≃ₜ* ArchSO (QRe (hypForm F) w) :=
  diagEquivOfIncl (ArchSO.incl _) Subtype.val_injective Topology.IsInducing.subtypeVal (hypSOR w) (fun _ => rfl)
    (fun g => exists_diagGL_of_hess (by
      have := (hessian_of_mem_soReal (Q₀ := hypForm F) w g).1
      rw [hessian_hypForm_map] at this; exact this) (hessian_of_mem_soReal (Q₀ := hypForm F) w g).2)

theorem isoCharR_hypEquivR (w : {w : InfinitePlace F // w.IsReal}) (t : ℝˣ) :
    isoCharR nondegenerate_hypForm (isIsoVec_hypE (F := F)) w (hypEquivR w t) = (t : ℝ) := by
  show eigVal _ _ _ = _
  rw [eigVal_hypE]; rfl

/-! #### complex places -/

theorem hypDiagGL_mem_soC (w : {w : InfinitePlace F // w.IsComplex}) (t : ℂˣ) :
    hypDiagGL t ∈ soC (QCx (hypForm F) w) := by
  rw [mem_soC_iff, gramC, QCx, hessian_map_NF, hessian_hypForm_map]
  refine ⟨?_, diagMat_det t⟩
  rw [Matrix.mul_smul, Matrix.smul_mul, diagMat_conj]

/-- $t\mapsto\mathrm{diag}(t,t^{-1})$, $\mathbb C^\times\to SO(H^{\tau_w})(\mathbb C)$. -/
def hypSOC (w : {w : InfinitePlace F // w.IsComplex}) : ℂˣ →* ArchSOC (QCx (hypForm F) w) :=
  (hypDiagGLHom.codRestrict (soC (QCx (hypForm F) w)) (hypDiagGL_mem_soC w) :)

/-- **$\mathbb C^\times\cong SO(H^{\tau_w})(\mathbb C)$**. -/
def hypEquivC (w : {w : InfinitePlace F // w.IsComplex}) : ℂˣ ≃ₜ* ArchSOC (QCx (hypForm F) w) :=
  diagEquivOfIncl (ArchSOC.incl _) Subtype.val_injective Topology.IsInducing.subtypeVal (hypSOC w) (fun _ => rfl)
    (fun g => exists_diagGL_of_hess (by
      have := (hessian_of_mem_soC (Q₀ := hypForm F) w g).1
      rw [hessian_hypForm_map] at this; exact this) (hessian_of_mem_soC (Q₀ := hypForm F) w g).2)

theorem isoCharC_hypEquivC (w : {w : InfinitePlace F // w.IsComplex}) (t : ℂˣ) :
    isoCharC nondegenerate_hypForm (isIsoVec_hypE (F := F)) w (hypEquivC w t) = (t : ℂ) := by
  show eigVal _ _ _ = _
  rw [eigVal_hypE]; rfl

end Places

/-! ### The archimedean isomorphism $F_\infty^\times\cong SO(H)(F_\infty)$ -/

section Inf

/-- Product of continuous isomorphisms. -/
def prodCME {M₁ M₂ N₁ N₂ : Type*} [Monoid M₁] [Monoid M₂] [Monoid N₁] [Monoid N₂] [TopologicalSpace M₁]
    [TopologicalSpace M₂] [TopologicalSpace N₁] [TopologicalSpace N₂] (e₁ : M₁ ≃ₜ* N₁) (e₂ : M₂ ≃ₜ* N₂) :
    (M₁ × M₂) ≃ₜ* (N₁ × N₂) :=
  { MulEquiv.prodCongr e₁.toMulEquiv e₂.toMulEquiv with
    continuous_toFun := (e₁.continuous.comp continuous_fst).prodMk (e₂.continuous.comp continuous_snd)
    continuous_invFun := (e₁.symm.continuous.comp continuous_fst).prodMk (e₂.symm.continuous.comp continuous_snd) }

/-- Pi of continuous isomorphisms. -/
def piCME {ι : Type*} {M N : ι → Type*} [∀ i, Monoid (M i)] [∀ i, Monoid (N i)] [∀ i, TopologicalSpace (M i)]
    [∀ i, TopologicalSpace (N i)] (e : ∀ i, M i ≃ₜ* N i) : (∀ i, M i) ≃ₜ* ∀ i, N i :=
  { MulEquiv.piCongrRight (fun i => (e i).toMulEquiv) with
    continuous_toFun := continuous_pi fun i => (e i).continuous.comp (continuous_apply i)
    continuous_invFun := continuous_pi fun i => (e i).symm.continuous.comp (continuous_apply i) }

/-- $(M\times N)^\times\cong M^\times\times N^\times$ as topological groups. -/
def unitsProdCME (M N : Type*) [Monoid M] [Monoid N] [TopologicalSpace M] [TopologicalSpace N] :
    (M × N)ˣ ≃ₜ* Mˣ × Nˣ :=
  { MulEquiv.prodUnits with
    continuous_toFun := Homeomorph.prodUnits.continuous
    continuous_invFun := Homeomorph.prodUnits.symm.continuous }

variable (F) in
/-- **$F_\infty^\times\cong SO(H)(F_\infty)$** (topological groups): $t\mapsto(\mathrm{diag}(t_w,t_w^{-1}))_w$ at the real
and complex places. -/
def hypInfEquiv : (mixedEmbedding.mixedSpace F)ˣ ≃ₜ* GInfSO (hypForm F) :=
  (unitsProdCME _ _).trans
    ((prodCME ContinuousMulEquiv.piUnits ContinuousMulEquiv.piUnits).trans
      (prodCME (piCME fun w => hypEquivR w) (piCME fun w => hypEquivC w)))

/-- **$\chi_e\circ\Phi_\infty = \mathrm{id}$**: the eigenvalue of $\mathrm{diag}(t_w,t_w^{-1})$ on $e = (1,0)$ is $t_w$. -/
theorem isoCharInf_hypInfEquiv (t : (mixedEmbedding.mixedSpace F)ˣ) :
    isoCharInf nondegenerate_hypForm (isIsoVec_hypE (F := F)) (hypInfEquiv F t) =
      (t : mixedEmbedding.mixedSpace F) :=
  Prod.ext (funext fun w => isoCharR_hypEquivR w _) (funext fun w => isoCharC_hypEquivC w _)

end Inf

/-! ### The finite isomorphism $\mathbb A_f^\times\cong SO(H)(\mathbb A_f)$ -/

section Fin

local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (hypForm F)
local notation "AF" => FiniteAdeleRing (𝓞 F) F

theorem mem_std_two (v : HeightOneSpectrum (𝓞 F)) (y : Fin 2 → v.adicCompletion F) :
    y ∈ (std v : Submodule (v.adicCompletionIntegers F) (Fin 2 → v.adicCompletion F)) ↔
      ∀ i, Valued.v (y i) ≤ 1 := by
  rw [std, mem_ball]; simp

theorem hypEquivV_mulVec_mem_std (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ)
    (h1 : Valued.v (t : v.adicCompletion F) ≤ 1) (h2 : Valued.v ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≤ 1)
    (y : Fin 2 → v.adicCompletion F)
    (hy : y ∈ (std v : Submodule (v.adicCompletionIntegers F) (Fin 2 → v.adicCompletion F))) :
    omat ((hypEquivV v t : soSub QF (v.adicCompletion F)) : orthGroup QF (v.adicCompletion F)) *ᵥ y ∈
      (std v : Submodule (v.adicCompletionIntegers F) (Fin 2 → v.adicCompletion F)) := by
  rw [mem_std_two] at hy ⊢
  intro i
  have e0 : (omat ((hypEquivV v t : soSub QF (v.adicCompletion F)) : orthGroup QF (v.adicCompletion F)) *ᵥ y) 0 =
      (t : v.adicCompletion F) * y 0 := by
    simp [omat_hypEquivV, mulVec, dotProduct, Fin.sum_univ_two]
  have e1 : (omat ((hypEquivV v t : soSub QF (v.adicCompletion F)) : orthGroup QF (v.adicCompletion F)) *ᵥ y) 1 =
      ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y 1 := by
    simp [omat_hypEquivV, mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases i
  · show Valued.v ((omat _ *ᵥ y) 0) ≤ 1
    rw [e0, map_mul]; exact mul_le_one' h1 (hy 0)
  · show Valued.v ((omat _ *ᵥ y) 1) ≤ 1
    rw [e1, map_mul]; exact mul_le_one' h2 (hy 1)

/-- **$\mathrm{diag}(t,t^{-1})\in SO(\mathfrak o_v^2)$ iff $t\in\mathfrak o_v^\times$.** -/
theorem hypEquivV_mem_stdStab_iff (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    ((hypEquivV v t : soSub QF (v.adicCompletion F)) : orthGroup QF (v.adicCompletion F)) ∈ stdStab QF v ↔
      Valued.v (t : v.adicCompletion F) ≤ 1 ∧ Valued.v ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≤ 1 := by
  constructor
  · intro h
    exact ⟨entry_le_one_of_mem_stdStab v h 0 0, entry_le_one_of_mem_stdStab v h 1 1⟩
  · rintro ⟨h1, h2⟩
    refine mem_stdStab_of_mulVec v _ (fun y hy => hypEquivV_mulVec_mem_std v t h1 h2 y hy) (fun y hy => ?_)
    have : ((hypEquivV v t : soSub QF (v.adicCompletion F)) : orthGroup QF (v.adicCompletion F))⁻¹ =
        ((hypEquivV v t⁻¹ : soSub QF (v.adicCompletion F)) : orthGroup QF (v.adicCompletion F)) := by
      rw [← Subgroup.coe_inv, ← map_inv]
    rw [this]
    exact hypEquivV_mulVec_mem_std v t⁻¹ h2 (by simpa using h1) y hy

theorem eventually_hypEquivV_mem_stdStab (t : AFˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ((hypEquivV v (unitAt t v) : soSub QF (v.adicCompletion F)) : orthGroup QF (v.adicCompletion F)) ∈
        stdStab QF v := by
  filter_upwards [(t : AF).2, ((t⁻¹ : AFˣ) : AF).2] with v h1 h2
  exact (hypEquivV_mem_stdStab_iff v _).mpr
    ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) ..).mp h1,
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) ..).mp h2⟩

/-- **$\mathbb A_f^\times\to SO(H)(\mathbb A_f)$**, $t\mapsto(\mathrm{diag}(t_v,t_v^{-1}))_v$. -/
def hypFinHom : AFˣ →* SOAf (hypForm F) where
  toFun t := ⟨⟨fun v => ((hypEquivV v (unitAt t v) : soSub QF (v.adicCompletion F)) :
      orthGroup QF (v.adicCompletion F)), eventually_hypEquivV_mem_stdStab t⟩,
    fun v => (hypEquivV v (unitAt t v)).2⟩
  map_one' := by
    ext v : 2
    have : unitAt (1 : AFˣ) v = 1 := Units.ext rfl
    show ((hypEquivV v (unitAt (1 : AFˣ) v) : soSub QF (v.adicCompletion F)) : orthGroup QF (v.adicCompletion F)) = 1
    rw [this, map_one]; rfl
  map_mul' g h := by
    ext v : 2
    show ((hypEquivV v (unitAt (g * h) v) : soSub QF (v.adicCompletion F)) : orthGroup QF (v.adicCompletion F)) = _
    rw [unitAt_mul, map_mul]; rfl

@[simp] theorem hypFinHom_apply (t : AFˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ((hypFinHom t : SOAf (hypForm F)) : OAf QF) v =
      ((hypEquivV v (unitAt t v) : soSub QF (v.adicCompletion F)) : orthGroup QF (v.adicCompletion F)) := rfl

theorem continuous_unitAt' (v : HeightOneSpectrum (𝓞 F)) : Continuous fun t : AFˣ => unitAt t v :=
  Units.continuous_iff.mpr ⟨(RestrictedProduct.continuous_eval v).comp Units.continuous_val,
    (RestrictedProduct.continuous_eval v).comp Units.continuous_coe_inv⟩

theorem continuous_hypEquivV_unitAt (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun t : AFˣ =>
      ((hypEquivV v (unitAt t v) : soSub QF (v.adicCompletion F)) : orthGroup QF (v.adicCompletion F)) :=
  continuous_subtype_val.comp ((hypEquivV v).continuous.comp (continuous_unitAt' v))

theorem mem_stdStab_of_mem_OHatUnits {t : AFˣ} (ht : t ∈ OHatUnits F) (v : HeightOneSpectrum (𝓞 F)) :
    ((hypEquivV v (unitAt t v) : soSub QF (v.adicCompletion F)) : orthGroup QF (v.adicCompletion F)) ∈
      stdStab QF v :=
  (hypEquivV_mem_stdStab_iff v _).mpr
    ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) ..).mp (ht.1 v),
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) ..).mp (ht.2 v)⟩

/-- **`hypFinHom` is continuous**: on the open subgroup $\hat{\mathcal O}^\times$ it factors through
$\prod_vO(\mathfrak o_v^2)$, where the restricted product topology is the product topology. -/
theorem continuous_hypFinHom : Continuous (hypFinHom (F := F)) := by
  refine continuous_of_continuousAt_one _ ?_
  have hU : (OHatUnits F : Set AFˣ) ∈ 𝓝 (1 : AFˣ) := isOpen_OHatUnits.mem_nhds (OHatUnits F).one_mem
  let g : OHatUnits F → ∀ v, (stdStab QF v : Set (orthGroup QF (v.adicCompletion F))) :=
    fun t v => ⟨_, mem_stdStab_of_mem_OHatUnits t.2 v⟩
  have hg : Continuous g := continuous_pi fun v =>
    ((continuous_hypEquivV_unitAt v).comp continuous_subtype_val).subtype_mk _
  have hcomp : Continuous fun t : OHatUnits F => ((hypFinHom t.1 : SOAf (hypForm F)) : OAf QF) := by
    have := (RestrictedProduct.isEmbedding_structureMap
      (R := fun v : HeightOneSpectrum (𝓞 F) => orthGroup QF (v.adicCompletion F))
      (A := fun v => (stdStab QF v : Set (orthGroup QF (v.adicCompletion F)))) (𝓕 := cofinite)).continuous.comp hg
    refine this.congr fun t => ?_
    ext v : 1
    rfl
  have hon : ContinuousOn (fun t => ((hypFinHom t : SOAf (hypForm F)) : OAf QF)) (OHatUnits F) :=
    continuousOn_iff_continuous_domRestrict.2 hcomp
  exact (Topology.IsInducing.subtypeVal.continuousAt_iff).2 (hon.continuousAt hU)

theorem hypFinHom_injective : Function.Injective (hypFinHom (F := F)) := fun t s h => by
  have hv : ∀ v, unitAt t v = unitAt s v := fun v =>
    (hypEquivV v).injective (Subtype.ext (congrArg (fun g : SOAf (hypForm F) => ((g : OAf QF) v)) h))
  exact Units.ext (Subtype.ext (funext fun v => congrArg Units.val (hv v)))

theorem hypFinHom_surjective : Function.Surjective (hypFinHom (F := F)) := fun g => by
  let tv : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ := fun v => (hypEquivV v).symm (finComp g v)
  have hint : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      Valued.v ((tv v : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≤ 1 ∧
        Valued.v (((tv v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≤ 1 := by
    filter_upwards [(g : OAf QF).2] with v hv
    have hv' : ((g : OAf QF) v : orthGroup QF (v.adicCompletion F)) ∈ stdStab QF v := hv
    refine (hypEquivV_mem_stdStab_iff v _).mp ?_
    rw [show hypEquivV v (tv v) = finComp g v from (hypEquivV v).apply_symm_apply _]
    exact hv'
  let x : AF := mkAF (fun v => (tv v : v.adicCompletion F)) (by
    filter_upwards [hint] with v hv
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) ..).mpr hv.1)
  let y : AF := mkAF (fun v => ((tv v)⁻¹ : (v.adicCompletion F)ˣ)) (by
    filter_upwards [hint] with v hv
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) ..).mpr hv.2)
  have hxy : x * y = 1 := Subtype.ext (funext fun v => (tv v).mul_inv)
  have hyx : y * x = 1 := Subtype.ext (funext fun v => (tv v).inv_mul)
  refine ⟨⟨x, y, hxy, hyx⟩, ?_⟩
  ext v : 2
  have hu : unitAt (⟨x, y, hxy, hyx⟩ : AFˣ) v = tv v := Units.ext rfl
  show ((hypEquivV v (unitAt (⟨x, y, hxy, hyx⟩ : AFˣ) v) : soSub QF (v.adicCompletion F)) :
    orthGroup QF (v.adicCompletion F)) = _
  rw [hu]
  exact congrArg Subtype.val ((hypEquivV v).apply_symm_apply (finComp g v))

instance : LocallyCompactSpace (SOAf (hypForm F)) :=
  (isClosed_soAf QF).isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- The group isomorphism $\mathbb A_f^\times\cong SO(H)(\mathbb A_f)$. -/
def hypFinMulEquiv : AFˣ ≃* SOAf (hypForm F) := MulEquiv.ofBijective hypFinHom ⟨hypFinHom_injective, hypFinHom_surjective⟩

variable (F) in
/-- **$\mathbb A_f^\times\cong SO(H)(\mathbb A_f)$ as topological groups**, $t\mapsto(\mathrm{diag}(t_v,t_v^{-1}))_v$ (continuity of
the inverse by the open mapping theorem). -/
def hypFinEquiv : AFˣ ≃ₜ* SOAf (hypForm F) :=
  { hypFinMulEquiv with
    continuous_toFun := continuous_hypFinHom
    continuous_invFun := ((hypFinMulEquiv (F := F)).toEquiv.toHomeomorphOfContinuousOpen continuous_hypFinHom
      (MonoidHom.isOpenMap_of_sigmaCompact _ hypFinHom_surjective continuous_hypFinHom)).symm.continuous }

theorem hypFinEquiv_apply (t : AFˣ) : hypFinEquiv F t = hypFinHom t := rfl

/-- **$\chi_e\circ\Phi_f = \mathrm{id}$**. -/
theorem isoCharFin_hypFinEquiv (t : AFˣ) :
    isoCharFin nondegenerate_hypForm (isIsoVec_hypE (F := F)) (hypFinEquiv F t) = (t : AF) :=
  Subtype.ext (funext fun v => isoCharV_hypEquivV v (unitAt t v))

theorem mem_KSO_iff (g : SOAf (hypForm F)) : g ∈ KSO (hypForm F) ↔ ∀ v, (g : OAf QF) v ∈ stdStab QF v :=
  Set.ext_iff.mp (coe_locStab_std QF) (g : OAf QF)

/-- **$\mathrm{diag}(t,t^{-1})\in SO(\hat{\mathcal O}^2)$ iff $t\in\hat{\mathcal O}^\times$.** -/
theorem hypFinEquiv_preimage_KSO : hypFinEquiv F ⁻¹' (KSO (hypForm F) : Set (SOAf (hypForm F))) = OHatUnits F := by
  ext t
  rw [Set.mem_preimage, SetLike.mem_coe, mem_KSO_iff]
  constructor
  · intro h
    refine ⟨fun v => ?_, fun v => ?_⟩
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) ..).mpr ((hypEquivV_mem_stdStab_iff v _).mp (h v)).1
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) ..).mpr ((hypEquivV_mem_stdStab_iff v _).mp (h v)).2
  · intro ht v
    exact mem_stdStab_of_mem_OHatUnits ht v

end Fin

/-! ### The adelic isomorphism $\mathbb A_F^\times\cong SO(H)(\mathbb A)$ -/

section Adele

variable (F) in
/-- **$\mathbb A_F^\times\cong SO(H)(\mathbb A)$ as topological groups**: `idelesEquiv` followed by `hypInfEquiv` $\times$
`hypFinEquiv`; $t\mapsto\mathrm{diag}(t,t^{-1})$ at every place. -/
@[kb "weil1982" "§2.4 [unverified] (G_m ≅ SO(hyperbolic plane)); omeara1963 §42 [unverified]"]
def hypEquiv : (Adeles F)ˣ ≃ₜ* SOAdele (hypForm F) :=
  (idelesEquiv F).trans (prodCME (hypInfEquiv F) (hypFinEquiv F))

/-- **$\chi_e\circ\Phi = \mathrm{id}$** for $e = (1,0)$. -/
theorem isoChar_hypEquiv (t : (Adeles F)ˣ) :
    isoChar nondegenerate_hypForm (isIsoVec_hypE (F := F)) (hypEquiv F t) = t := by
  refine Units.ext ?_
  rw [isoChar_val]
  exact Prod.ext (isoCharInf_hypInfEquiv (infPart t)) (isoCharFin_hypFinEquiv (finPart t))

/-- **$\Phi\circ\chi_e = \mathrm{id}$**: $\chi_e$ is the inverse of `hypEquiv`. -/
theorem hypEquiv_isoChar (g : SOAdele (hypForm F)) :
    hypEquiv F (isoChar nondegenerate_hypForm (isIsoVec_hypE (F := F)) g) = g := by
  obtain ⟨t, rfl⟩ := (hypEquiv F).surjective g
  rw [isoChar_hypEquiv]

end Adele

/-! ### Global points -/

section Global

local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (hypForm F)

theorem hypDiagGL_mem_orthGroup_F (t : Fˣ) : hypDiagGL t ∈ orthGroup QF F :=
  (mem_orthGroup QF).mpr (by rw [hessian_hypForm_map (algebraMap F F)]; exact diagMat_conj t)

/-- $\xi\mapsto\mathrm{diag}(\xi,\xi^{-1})$, $F^\times\to SO(H)(F)$. -/
def hypSOF : Fˣ →* soSub QF F :=
  (hypDiagGLHom.codRestrict (orthGroup QF F) hypDiagGL_mem_orthGroup_F).codRestrict (soSub QF F)
    fun t => mem_soSub.mpr (diagMat_det t)

theorem hypSOF_surjective : Function.Surjective (hypSOF (F := F)) := fun g => by
  have h := (mem_orthGroup QF).mp (g : orthGroup QF F).2
  rw [hessian_hypForm_map (algebraMap F F)] at h
  obtain ⟨t, ht⟩ := exists_diagGL_of_hess h (mem_soSub.mp g.2)
  exact ⟨t, Subtype.ext (Subtype.ext ht)⟩

/-- The character $\chi_e$ of the diagonal point $\mathrm{diag}(\xi,\xi^{-1})\in SO(H)(F)$ is $\xi\in F^\times\le\mathbb A_F^\times$. -/
theorem isoChar_diagSOAdele (ξ : Fˣ) :
    isoChar nondegenerate_hypForm (isIsoVec_hypE (F := F)) (diagSOAdele (hypForm F) (hypSOF ξ)) = diagUnits F ξ := by
  refine Units.ext ?_
  rw [isoChar_val, diagUnits_val]
  refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) (Subtype.ext (funext fun v => ?_))
  · show eigVal _ _ _ = _
    rw [eigVal_hypE]; rfl
  · show eigVal _ _ _ = _
    rw [eigVal_hypE]; rfl
  · show eigVal _ _ _ = _
    rw [eigVal_hypE]; rfl

theorem hypEquiv_diagUnits (ξ : Fˣ) : hypEquiv F (diagUnits F ξ) = diagSOAdele (hypForm F) (hypSOF ξ) := by
  rw [← isoChar_diagSOAdele ξ, hypEquiv_isoChar]

/-- **Global points:** $\Phi(F^\times) = SO(H)(F)$, i.e. `hypEquiv` carries the diagonal $F^\times\le\mathbb A_F^\times$ onto
`GammaSOAdele` (every $\gamma\in SO(H)(F)$ is $\mathrm{diag}(\xi,\xi^{-1})$, `hypSOF_surjective`). -/
theorem map_diagUnitsSub_hypEquiv :
    (diagUnitsSub F).map (hypEquiv F).toMulEquiv.toMonoidHom = GammaSOAdele (hypForm F) := by
  ext x
  constructor
  · rintro ⟨_, ⟨ξ, rfl⟩, rfl⟩
    exact ⟨hypSOF ξ, (hypEquiv_diagUnits ξ).symm⟩
  · rintro ⟨γ, rfl⟩
    obtain ⟨ξ, rfl⟩ := hypSOF_surjective γ
    exact ⟨_, ⟨ξ, rfl⟩, hypEquiv_diagUnits ξ⟩

end Global

/-! ### The finite measure: $\lambda_v = \alpha_v(H,H)$, so $\mu_f(SO(\hat{\mathcal O}^2)) = 1$ -/

section Measure

/-- **Siegel's local density of the hyperbolic plane at every finite place** (dyadic included):
$\alpha_v(H,H) = \tfrac12\cdot\frac{2(q-1)}{q} = 1 - N(v)^{-1}$ (`DVR.localDensityForm_hyperbolic`). -/
theorem siegelDensity_hypForm (v : HeightOneSpectrum (𝓞 F)) :
    LocalDensity.NF.siegelDensity v (hypForm F) (hypForm F) = 1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  have hq : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := lt_trans zero_lt_one (one_lt_absNorm v)
  have hQp : LocalDensity.NF.Qp v (hypForm F) =
      QuadFormsKB.LocalDensity.DVR.hyperbolic (v.adicCompletionIntegers F) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LocalDensity.NF.Qp, hypForm, QuadFormsKB.LocalDensity.DVR.hyperbolic, QuadForm.map, QuadForm.ofUpper]
  unfold LocalDensity.NF.siegelDensity
  simp only [↓reduceIte]
  rw [LocalDensity.NF.localDensityForm_eq_completion, hQp,
    QuadFormsKB.LocalDensity.DVR.localDensityForm_hyperbolic _ (LocalDensity.NF.irreducible_π v),
    LocalDensity.NF.q_completion]
  field_simp

/-- **$\lambda_v = \alpha_v(H,H)$, hence the finite factor is $1$.** -/
theorem finFactor_hypForm : finFactor (hypForm F) lamV = 1 := by
  rw [finFactor_eq _ nondegenerate_hypForm lamV_pos]
  have : ∀ v : HeightOneSpectrum (𝓞 F),
      LocalDensity.NF.siegelDensity v (hypForm F) (hypForm F) / lamV v = 1 := fun v => by
    rw [siegelDensity_hypForm]; exact div_self (lamV_pos v).ne'
  simp [this]

instance : IsMulLeftInvariant ((muFinUnits F).map (hypFinEquiv F)) :=
  isMulLeftInvariant_map (hypFinEquiv F).toMulEquiv.toMonoidHom.toMulHom (hypFinEquiv F).continuous.measurable
    (hypFinEquiv F).surjective

/-- **The Tamagawa measure of $\mathbb G_m(\mathbb A_f)$ is the transport of $\mu_f$ on $SO(H)(\mathbb A_f)$**
(up to the constant $\operatorname{vol}(\hat{\mathcal O}^\times)$): both are left Haar measures, with values
$\operatorname{vol}(\hat{\mathcal O}^\times)$ and $\operatorname{vol}(\hat{\mathcal O}^\times)\cdot 1$ on $SO(\hat{\mathcal O}^2)$. -/
theorem map_muFinUnits_hypFinEquiv :
    (muFinUnits F).map (hypFinEquiv F) = ENNReal.ofReal (ohatVol F) • QuadFormsKB.Tamagawa.Measure.muFin (hypForm F) lamV := by
  have : SigmaFinite ((muFinUnits F).map (hypFinEquiv F)) :=
    (hypFinEquiv F).toHomeomorph.toMeasurableEquiv.sigmaFinite_map
  have hmeas : Measurable (hypFinEquiv F) := (hypFinEquiv F).continuous.measurable
  have hval : ((muFinUnits F).map (hypFinEquiv F)) (KSO (hypForm F) : Set (SOAf (hypForm F))) =
      ENNReal.ofReal (ohatVol F) := by
    rw [Measure.map_apply hmeas (isOpen_KSO _).measurableSet]
    rw [hypFinEquiv_preimage_KSO]
    exact muFinUnits_OHatUnits
  refine (eq_haarNorm (isCompact_KSO (hypForm F)) (isOpen_KSO _) ((muFinUnits F).map (hypFinEquiv F))
    (by rw [hval]; exact ENNReal.ofReal_ne_top)).trans ?_
  rw [hval]
  unfold QuadFormsKB.Tamagawa.Measure.muFin
  rw [finFactor_hypForm, Real.toNNReal_one]
  unfold haarNorm
  rw [one_smul, ENNReal.smul_def, ENNReal.coe_toNNReal ENNReal.ofReal_ne_top]

end Measure

end QuadFormsKB.Tamagawa.Measure.Weil
