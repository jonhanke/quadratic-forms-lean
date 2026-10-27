import QuadFormsKB.Tamagawa.Measure.Weil.BasisPoisson
import QuadFormsKB.Tamagawa.Measure.Weil.SL2Approx

/-!
# Poisson summation on $F_\infty^2$ for the lattices $M\mathcal O_F^2$, $M\in\mathrm{SL}_2(F_\infty)$


$F$ any number field, $V = F_\infty$ (Mathlib's mixed space), $W = V^2$ with the measure $\mu = \mu_\infty^2$
(`muInfVec`, self-dual) and the trace pairing $\beta(y, z) = \sum_i\operatorname{Tr}_\infty(y_iz_i)$ (`betaW`).

**`poisson_SL2Inf`**: for $M\in M_2(V)$ with $\det M = 1$, $M^* = (\operatorname{adj}M)^{\mathsf T}$ and a Schwartz function
$f$ on $W$,
$$\sum_{\xi\in\mathcal O_F^2} f(M\xi) = |d_F|^{-1}\sum_{\eta\in(\mathfrak d^{-1})^2}\hat f(M^*\eta),\qquad
  \hat f(z) = \int_W f(y)\,e(\beta(y, z))\,d\mu(y),$$
($\mathfrak d^{-1}$ = `FractionalIdeal.dual ℤ ℚ 1`, the inverse different). *Proof:* `poisson_basis` for the basis
$M(b\oplus b)$ ($b$ a $\mathbb Z$-basis of $\mathcal O_F$) with the $\beta$-dual basis $M^*(b^\vee\oplus b^\vee)$
($\beta(My, M^*z) = \beta(y, z)$, `betaW_mulVec`); the covolume is $\mu(P_{b\oplus b}) = \operatorname{vol}(P_b)^2 = |d_F|$
(`selfDual_covolume_idealLattice`), unchanged by $M$ since $\det M = 1$ (`map_mulVec_muInfVec`).
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology NumberField.mixedEmbedding
open scoped ENNReal NNReal Pointwise Classical MatrixGroups nonZeroDivisors FourierTransform

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "V" => mixedSpace F
local notation "FI" => FractionalIdeal (𝓞 F)⁰ F

/-! ### The trace pairing on $V^2$ -/

variable (F) in
/-- $\beta(y, z) = \sum_i\operatorname{Tr}_\infty(y_iz_i)$ on $V^2$. -/
def betaW : (Fin 2 → V) →ₗ[ℝ] (Fin 2 → V) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y z => ∑ i, Analysis.traceInf (y i * z i))
    (fun y₁ y₂ z => by simp only [Pi.add_apply, add_mul, Analysis.traceInf_add, Finset.sum_add_distrib])
    (fun c y z => by simp only [Pi.smul_apply, smul_mul_assoc, Analysis.traceInf_smul, Finset.mul_sum, smul_eq_mul])
    (fun y z₁ z₂ => by simp only [Pi.add_apply, mul_add, Analysis.traceInf_add, Finset.sum_add_distrib])
    (fun c y z => by simp only [Pi.smul_apply, mul_smul_comm, Analysis.traceInf_smul, Finset.mul_sum, smul_eq_mul])

theorem betaW_apply (y z : Fin 2 → V) : betaW F y z = ∑ i, Analysis.traceInf (y i * z i) := rfl

/-- $M^* = (\operatorname{adj}M)^{\mathsf T}$ ($= (M^{-1})^{\mathsf T}$ when $\det M = 1$). -/
def starM (M : Matrix (Fin 2) (Fin 2) V) : Matrix (Fin 2) (Fin 2) V := Matrix.transpose M.adjugate

theorem traceInf_sum_fin2 (g : Fin 2 → V) : ∑ i, Analysis.traceInf (g i) = Analysis.traceInf (∑ i, g i) :=
  (map_sum Analysis.traceInfL g Finset.univ).symm

theorem traceInf_zero' : Analysis.traceInf (0 : V) = 0 := by
  have := Analysis.traceInf_smul (F := F) 0 0
  rwa [zero_smul, zero_mul] at this

theorem betaW_mulVec {M : Matrix (Fin 2) (Fin 2) V} (hM : M.det = 1) (y z : Fin 2 → V) :
    betaW F (M.mulVec y) ((starM M).mulVec z) = betaW F y z := by
  have key : ∑ i, M.mulVec y i * (starM M).mulVec z i = ∑ i, y i * z i := by
    have : dotProduct (M.mulVec y) ((starM M).mulVec z) = dotProduct y z := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, starM,
        ← Matrix.transpose_mul, Matrix.adjugate_mul, hM, one_smul, Matrix.transpose_one, Matrix.vecMul_one]
    simpa [dotProduct] using this
  rw [betaW_apply, betaW_apply, traceInf_sum_fin2, traceInf_sum_fin2, key]

/-! ### Bases -/

/-- The unit fractional ideal. -/
abbrev I₁ : FIˣ := 1

local notation "n" => Module.finrank ℚ F

/-- The basis $b\oplus b$ of $V^2$ ($b$ a $\mathbb Z$-basis of $\mathcal O_F$). -/
def basis₀ : Module.Basis (Σ _ : Fin 2, Fin n) ℝ (Fin 2 → V) :=
  Pi.basis fun _ => Analysis.bR (I₁ (F := F))

/-- Its $\beta$-dual family $b^\vee\oplus b^\vee$. -/
def dual₀ (σ : Σ _ : Fin 2, Fin n) : Fin 2 → V :=
  Pi.single σ.1 (mixedEmbedding F ((Analysis.bq (I₁ (F := F))).traceDual σ.2))

theorem basis₀_apply (σ : Σ _ : Fin 2, Fin n) :
    basis₀ σ = Pi.single σ.1 (Analysis.bR (I₁ (F := F)) σ.2) := by
  rw [basis₀, Pi.basis_apply]

theorem betaW_basis₀_dual₀ (σ τ : Σ _ : Fin 2, Fin n) :
    betaW F (basis₀ σ) (dual₀ τ) = if σ = τ then 1 else 0 := by
  rw [betaW_apply, basis₀_apply, dual₀]
  obtain ⟨i, k⟩ := σ
  obtain ⟨i', k'⟩ := τ
  rw [Fin.sum_univ_two]
  have hloc : ∀ l : Fin 2, Analysis.traceInf ((Pi.single i (Analysis.bR (I₁ (F := F)) k) : Fin 2 → V) l *
      (Pi.single i' (mixedEmbedding F ((Analysis.bq (I₁ (F := F))).traceDual k')) : Fin 2 → V) l) =
      if l = i ∧ l = i' then (if k = k' then 1 else 0) else 0 := by
    intro l
    by_cases h1 : l = i <;> by_cases h2 : l = i'
    · subst h1; subst h2
      rw [Pi.single_eq_same, Pi.single_eq_same, Analysis.bR_apply, ← map_mul,
        Analysis.traceInf_mixedEmbedding, Module.Basis.trace_mul_traceDual]
      split_ifs <;> simp_all
    · subst h1
      rw [Pi.single_eq_of_ne h2, mul_zero, traceInf_zero']
      simp [h2]
    · rw [Pi.single_eq_of_ne h1, zero_mul, traceInf_zero']
      simp [h1]
    · rw [Pi.single_eq_of_ne h1, zero_mul, traceInf_zero']
      simp [h1]
  rw [hloc, hloc]
  by_cases hi : i = i' <;> by_cases hk : k = k'
  · subst hi; subst hk; fin_cases i <;> simp
  · subst hi; fin_cases i <;> simp [hk]
  · have : (⟨i, k⟩ : Σ _ : Fin 2, Fin n) ≠ ⟨i', k'⟩ := fun h => hi (congrArg Sigma.fst h)
    fin_cases i <;> fin_cases i' <;> simp_all
  · have : (⟨i, k⟩ : Σ _ : Fin 2, Fin n) ≠ ⟨i', k'⟩ := fun h => hi (congrArg Sigma.fst h)
    fin_cases i <;> fin_cases i' <;> simp_all


/-! ### The twisted basis $M(b\oplus b)$ and its dual -/

/-- $y\mapsto My$ as an $\mathbb R$-linear automorphism of $V^2$ ($\det M = 1$). -/
def mulVecEquiv (M : Matrix (Fin 2) (Fin 2) V) (hM : M.det = 1) : (Fin 2 → V) ≃ₗ[ℝ] (Fin 2 → V) :=
  LinearEquiv.ofLinear ((Matrix.mulVecLin M).restrictScalars ℝ) ((Matrix.mulVecLin M.adjugate).restrictScalars ℝ)
    (LinearMap.ext fun y => by
      show M.mulVec (M.adjugate.mulVec y) = y
      rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, hM, one_smul, Matrix.one_mulVec])
    (LinearMap.ext fun y => by
      show M.adjugate.mulVec (M.mulVec y) = y
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, hM, one_smul, Matrix.one_mulVec])

theorem mulVecEquiv_apply (M : Matrix (Fin 2) (Fin 2) V) (hM : M.det = 1) (y : Fin 2 → V) :
    mulVecEquiv M hM y = M.mulVec y := rfl

/-- The index set of $b\oplus b$, enumerated. -/
abbrev Nidx : ℕ := Fintype.card (Σ _ : Fin 2, Fin n)

/-- The enumeration. -/
def eIdx : (Σ _ : Fin 2, Fin n) ≃ Fin (Nidx (F := F)) := Fintype.equivFin _

/-- The basis $M(b\oplus b)$ of $V^2$. -/
def basisM (M : Matrix (Fin 2) (Fin 2) V) (hM : M.det = 1) : Module.Basis (Fin (Nidx (F := F))) ℝ (Fin 2 → V) :=
  ((basis₀ (F := F)).reindex eIdx).map (mulVecEquiv M hM)

/-- The $\beta$-dual family $M^*(b^\vee\oplus b^\vee)$. -/
def dualM (M : Matrix (Fin 2) (Fin 2) V) (j : Fin (Nidx (F := F))) : Fin 2 → V :=
  (starM M).mulVec (dual₀ (eIdx.symm j))

theorem basisM_apply (M : Matrix (Fin 2) (Fin 2) V) (hM : M.det = 1) (j : Fin (Nidx (F := F))) :
    basisM M hM j = M.mulVec (basis₀ (eIdx.symm j)) := by
  rw [basisM, Module.Basis.map_apply, Module.Basis.reindex_apply, mulVecEquiv_apply]

theorem betaW_basisM_dualM (M : Matrix (Fin 2) (Fin 2) V) (hM : M.det = 1) (j j' : Fin (Nidx (F := F))) :
    betaW F (basisM M hM j) (dualM M j') = if j = j' then 1 else 0 := by
  rw [basisM_apply, dualM, betaW_mulVec hM, betaW_basis₀_dual₀]
  simp only [EmbeddingLike.apply_eq_iff_eq]

/-! ### The covolume -/

theorem parallelepiped_piBasis :
    ((basis₀ (F := F)).parallelepiped : Set (Fin 2 → V)) =
      Set.univ.pi fun _ => ((Analysis.bR (I₁ (F := F))).parallelepiped : Set V) := by
  simp only [Module.Basis.coe_parallelepiped]
  ext x
  simp only [mem_parallelepiped_iff, Set.mem_univ_pi]
  constructor
  · rintro ⟨t, ht, rfl⟩ i
    refine ⟨fun k => t ⟨i, k⟩, ⟨fun k => ht.1 ⟨i, k⟩, fun k => ht.2 ⟨i, k⟩⟩, ?_⟩
    rw [Finset.sum_apply, Fintype.sum_sigma]
    simp only [basis₀_apply, Pi.smul_apply]
    rw [Fin.sum_univ_two]
    fin_cases i <;> simp [Pi.single_apply]
  · intro h
    choose t ht hx using h
    refine ⟨fun σ => t σ.1 σ.2, ⟨fun σ => (ht σ.1).1 σ.2, fun σ => (ht σ.1).2 σ.2⟩, ?_⟩
    funext i
    rw [hx i, Finset.sum_apply, Fintype.sum_sigma]
    simp only [basis₀_apply, Pi.smul_apply]
    rw [Fin.sum_univ_two]
    fin_cases i <;> simp [Pi.single_apply]

theorem volume_parallelepiped_bR :
    (volume : Measure V) ((Analysis.bR (I₁ (F := F))).parallelepiped : Set V) =
      ENNReal.ofReal (ZLattice.covolume (idealLattice F (I₁ (F := F)))) := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (fundamentalDomain_idealLattice F I₁),
    measureReal_def, ENNReal.ofReal_toReal ((ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne),
    Module.Basis.coe_parallelepiped,
    ← measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped (Analysis.bR (I₁ (F := F))) volume),
    Analysis.bR, ZSpan.fundamentalDomain_reindex]

theorem selfDualInf_parallelepiped_bR :
    Analysis.selfDualInf ((Analysis.bR (I₁ (F := F))).parallelepiped : Set V) =
      ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) := by
  rw [Analysis.selfDualInf, Measure.smul_apply, volume_parallelepiped_bR, ENNReal.smul_def, smul_eq_mul]
  have h := Analysis.selfDual_covolume_idealLattice (F := F) I₁
  rw [show ((I₁ (F := F) : FI)) = 1 from rfl, FractionalIdeal.absNorm_one, Rat.cast_one, one_mul] at h
  rw [← h, ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp

/-- **The covolume of $M\mathcal O_F^2$ for the self-dual measure is $|d_F|$.** -/
theorem muInfVec_parallelepiped_basisM (M : Matrix (Fin 2) (Fin 2) V) (hM : M.det = 1) :
    muInfVec F (Fin 2) ((basisM M hM).parallelepiped : Set (Fin 2 → V)) = ENNReal.ofReal |(discr F : ℝ)| := by
  rw [basisM, Module.Basis.parallelepiped_map, Module.Basis.parallelepiped_reindex]
  simp only [TopologicalSpace.PositiveCompacts.coe_map]
  have himg : (mulVecEquiv M hM) '' ((basis₀ (F := F)).parallelepiped : Set (Fin 2 → V)) =
      (M.adjugate).mulVec ⁻¹' ((basis₀ (F := F)).parallelepiped : Set (Fin 2 → V)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [Set.mem_preimage, mulVecEquiv_apply, Matrix.mulVec_mulVec, Matrix.adjugate_mul, hM, one_smul,
        Matrix.one_mulVec]
      exact hx
    · intro hy
      refine ⟨M.adjugate.mulVec y, hy, ?_⟩
      rw [mulVecEquiv_apply, Matrix.mulVec_mulVec, Matrix.mul_adjugate, hM, one_smul, Matrix.one_mulVec]
  have hdetadj : M.adjugate.det = 1 := by
    rw [Matrix.det_adjugate, hM, one_pow]
  have hmap := map_mulVec_muInfVec (F := F) M.adjugate (by rw [hdetadj]; exact isUnit_one)
  rw [hdetadj] at hmap
  have h1 : |LinearMap.det (LinearMap.mulLeft ℝ (1 : V))| = 1 := by
    rw [show LinearMap.mulLeft ℝ (1 : V) = LinearMap.id from LinearMap.ext fun x => one_mul x,
      LinearMap.det_id, abs_one]
  rw [h1, inv_one, ENNReal.ofReal_one, one_smul] at hmap
  have hmeas : MeasurableSet ((basis₀ (F := F)).parallelepiped : Set (Fin 2 → V)) :=
    (basis₀ (F := F)).parallelepiped.isCompact.measurableSet
  have hmv : Measurable (M.adjugate).mulVec :=
    (show Continuous fun x : Fin 2 → V => (M.adjugate).mulVec x from
      continuous_const.matrix_mulVec continuous_id).measurable
  rw [himg, ← Measure.map_apply hmv hmeas, hmap, parallelepiped_piBasis, muInfVec, Measure.pi_pi,
    Fin.prod_univ_two, selfDualInf_parallelepiped_bR, ← ENNReal.ofReal_mul (by positivity),
    Real.mul_self_sqrt (abs_nonneg _)]


/-! ### Poisson summation for $M\mathcal O_F^2$ -/

variable (F) in
/-- The Fourier transform on $V^2$ for the trace pairing and the self-dual measure. -/
def fourierW (f : (Fin 2 → V) → ℂ) (z : Fin 2 → V) : ℂ :=
  ∫ y, f y * ((𝐞 (betaW F y z) : Circle) : ℂ) ∂muInfVec F (Fin 2)

/-- $\mathbb Z^N\cong\mathcal O_F^2$. -/
def latEquiv2 : (Fin (Nidx (F := F)) → ℤ) ≃ (Fin 2 → (((I₁ (F := F) : FI)) : Set F)) :=
  ((Equiv.arrowCongr eIdx (Equiv.refl ℤ)).symm.trans (Equiv.piCurry fun _ _ => ℤ)).trans
    (Equiv.piCongrRight fun _ => Analysis.latEquiv I₁)

/-- $\mathbb Z^N\cong(\mathfrak d^{-1})^2$. -/
def dualEquiv2 : (Fin (Nidx (F := F)) → ℤ) ≃
    (Fin 2 → ((FractionalIdeal.dual ℤ ℚ ((I₁ (F := F) : FI)) : FI) : Set F)) :=
  ((Equiv.arrowCongr eIdx (Equiv.refl ℤ)).symm.trans (Equiv.piCurry fun _ _ => ℤ)).trans
    (Equiv.piCongrRight fun _ => Analysis.dualEquiv I₁)

theorem latEquiv2_apply (k : Fin (Nidx (F := F)) → ℤ) (i : Fin 2) :
    ((latEquiv2 k i : (((I₁ (F := F) : FI)) : Set F)) : F) =
      Analysis.latElt I₁ (fun k' => k (eIdx ⟨i, k'⟩)) := by
  rw [← Analysis.latEquiv_coe]
  rfl

theorem dualEquiv2_apply (m : Fin (Nidx (F := F)) → ℤ) (i : Fin 2) :
    ((dualEquiv2 m i : ((FractionalIdeal.dual ℤ ℚ ((I₁ (F := F) : FI)) : FI) : Set F)) : F) =
      Analysis.dualElt I₁ (fun k' => m (eIdx ⟨i, k'⟩)) := by
  rw [← Analysis.dualEquiv_coe]
  rfl

theorem sum_smul_bR (k : Fin n → ℤ) :
    ∑ j, (k j : ℝ) • Analysis.bR (I₁ (F := F)) j = mixedEmbedding F (Analysis.latElt I₁ k) := by
  rw [Analysis.latElt, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Analysis.bR_apply, map_mul, map_intCast, Int.cast_smul_eq_zsmul, zsmul_eq_mul]

theorem sum_smul_traceDual (m : Fin n → ℤ) :
    ∑ j, (m j : ℝ) • mixedEmbedding F ((Analysis.bq (I₁ (F := F))).traceDual j) =
      mixedEmbedding F (Analysis.dualElt I₁ m) := by
  rw [Analysis.dualElt, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_intCast, Int.cast_smul_eq_zsmul, zsmul_eq_mul]

theorem sum_sigma_single {X : Type*} [AddCommMonoid X] (g : (Σ _ : Fin 2, Fin n) → X) (i : Fin 2) :
    (∑ σ, (Pi.single σ.1 (g σ) : Fin 2 → X)) i = ∑ k : Fin n, g ⟨i, k⟩ := by
  rw [Finset.sum_apply, Fintype.sum_sigma, Fin.sum_univ_two]
  fin_cases i <;> simp [Pi.single_apply]

theorem sum_smul_basisM (M : Matrix (Fin 2) (Fin 2) V) (hM : M.det = 1) (k : Fin (Nidx (F := F)) → ℤ) :
    ∑ j, (k j : ℝ) • basisM M hM j = M.mulVec (fun i => mixedEmbedding F (latEquiv2 k i)) := by
  have h1 : ∑ j, (k j : ℝ) • basisM M hM j = mulVecEquiv M hM (∑ j, (k j : ℝ) • basis₀ (eIdx.symm j)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, basisM_apply, mulVecEquiv_apply]
  rw [h1, mulVecEquiv_apply]
  congr 1
  rw [← Equiv.sum_comp eIdx (fun j => (k j : ℝ) • basis₀ (eIdx.symm j))]
  funext i
  simp only [Equiv.symm_apply_apply, basis₀_apply]
  have : ∑ σ : Σ _ : Fin 2, Fin n, (k (eIdx σ) : ℝ) • (Pi.single σ.1 (Analysis.bR (I₁ (F := F)) σ.2) : Fin 2 → V) =
      ∑ σ : Σ _ : Fin 2, Fin n, (Pi.single σ.1 ((k (eIdx σ) : ℝ) • Analysis.bR (I₁ (F := F)) σ.2) : Fin 2 → V) :=
    Finset.sum_congr rfl fun σ _ => (Pi.single_smul' _ _ _).symm
  rw [this, sum_sigma_single, latEquiv2_apply, ← sum_smul_bR]

theorem sum_smul_dualM (M : Matrix (Fin 2) (Fin 2) V) (m : Fin (Nidx (F := F)) → ℤ) :
    ∑ j, (m j : ℝ) • dualM M j = (starM M).mulVec (fun i => mixedEmbedding F (dualEquiv2 m i)) := by
  have h1 : ∑ j, (m j : ℝ) • dualM M j = (starM M).mulVec (∑ j, (m j : ℝ) • dual₀ (eIdx.symm j)) := by
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dualM, Matrix.mulVec_smul]
  rw [h1]
  congr 1
  rw [← Equiv.sum_comp eIdx (fun j => (m j : ℝ) • dual₀ (eIdx.symm j))]
  funext i
  simp only [Equiv.symm_apply_apply, dual₀]
  have : ∑ σ : Σ _ : Fin 2, Fin n, (m (eIdx σ) : ℝ) •
      (Pi.single σ.1 (mixedEmbedding F ((Analysis.bq (I₁ (F := F))).traceDual σ.2)) : Fin 2 → V) =
      ∑ σ : Σ _ : Fin 2, Fin n, (Pi.single σ.1 ((m (eIdx σ) : ℝ) •
        mixedEmbedding F ((Analysis.bq (I₁ (F := F))).traceDual σ.2)) : Fin 2 → V) :=
    Finset.sum_congr rfl fun σ _ => (Pi.single_smul' _ _ _).symm
  rw [this, sum_sigma_single, dualEquiv2_apply, ← sum_smul_traceDual]

/-- **Poisson summation on $F_\infty^2$ for $M\mathcal O_F^2$, $\det M = 1$.** -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.2 (Poisson summation) [unverified]"]
theorem poisson_SL2Inf (M : Matrix (Fin 2) (Fin 2) V) (hM : M.det = 1) (f : SchwartzMap (Fin 2 → V) ℂ) :
    ∑' ξ : Fin 2 → (((I₁ (F := F) : FI)) : Set F), f (M.mulVec fun i => mixedEmbedding F (ξ i)) =
      ((|(discr F : ℝ)|)⁻¹ : ℝ) * ∑' η : Fin 2 → ((FractionalIdeal.dual ℤ ℚ ((I₁ (F := F) : FI)) : FI) : Set F),
        fourierW F f ((starM M).mulVec fun i => mixedEmbedding F (η i)) := by
  have h := poisson_basis (muInfVec F (Fin 2)) (basisM M hM) (betaW F) (dualM M) (betaW_basisM_dualM M hM) f 0
  rw [muInfVec_parallelepiped_basisM, ENNReal.toReal_ofReal (abs_nonneg _)] at h
  simp only [zero_add, map_zero, LinearMap.zero_apply, neg_zero, AddChar.map_zero_eq_one,
    Circle.coe_one, mul_one] at h
  rw [← latEquiv2.tsum_eq, ← dualEquiv2.tsum_eq]
  simp_rw [← sum_smul_basisM M hM, ← sum_smul_dualM M]
  rw [h]
  rfl


/-- The lattice sum over $M\mathcal O_F^2$ of a Schwartz function converges absolutely. -/
theorem summable_SL2Inf (M : Matrix (Fin 2) (Fin 2) V) (hM : M.det = 1) (f : SchwartzMap (Fin 2 → V) ℂ) :
    Summable fun ξ : Fin 2 → (((I₁ (F := F) : FI)) : Set F) =>
      ‖f (M.mulVec fun i => mixedEmbedding F (ξ i))‖ := by
  rw [← latEquiv2.summable_iff]
  have h := summable_basis (basisM M hM) f
  simp_rw [sum_smul_basisM M hM] at h
  exact h

end

end QuadFormsKB.Tamagawa.Measure.Weil
