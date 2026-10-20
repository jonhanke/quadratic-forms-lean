import QuadFormsKB.Tamagawa.Measure.Weil.SL2Gauss

/-!
# The Tamagawa number of $\mathrm{SL}_2$ over a number field is $1$

$F$ any number field, $\mu_T$ the fibration (Tamagawa) measure on $\mathrm{SL}_2(\mathbb A_F)$ (`SL2Measure.lean`).

**`tamagawa_SL2`**: `covolume (SL(2, F)) (SL2A F) (muT F) = 1`, i.e. $\tau(\mathrm{SL}_2) = \operatorname{vol}(\mathrm{SL}_2(\mathbb A_F)/\mathrm{SL}_2(F)) = 1$.

*Proof* (Siegel–Weil): for the test function $\Phi_u = G_u\otimes\mathbf 1_{\hat{\mathcal O}^2}$
($G_u$ a scaled Gaussian on $F_\infty^2$) and its dual $\Psi_u = |d_F|^{-1}\hat G_u\otimes\mathbf 1_{(\mathfrak d^{-1}\hat{\mathcal O})^2}$,
the **adelic Poisson formula** $\sum_{\xi\in F^2}\Phi_u(g\xi) = \sum_{\eta\in F^2}\Psi_u(g^*\eta)$, $g^* = (\operatorname{adj}g)^{\mathsf T}$,
holds for every $g\in\mathrm{SL}_2(\mathbb A_F)$ (`poisson_adelic`): by strong approximation (`exists_mul_slEmb_inv_mem_K`)
one may take $g_f\in\mathrm{SL}_2(\hat{\mathcal O})$, and then both sides are the archimedean lattice sums of
`poisson_SL2Inf`. Integrating over a fundamental domain $D$ with Siegel's mean value theorem
(`lintegral_tsum_mulVec_eq`, and $g^* = wgw^{-1}$) gives
$\tau + \int\Phi_u = \Psi_u(0)\,\tau + \int\Psi_u$, with $\int\Phi_u = \Psi_u(0) = |d_F|^{-1}\Delta(u)^{-2}$ and
$\int\Psi_u$ independent of $u$. Two values of $u$ ($\Delta(u)\ne\Delta(u')$) force $\tau = 1$.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology NumberField.mixedEmbedding
open QuadFormsKB.WeilRep
open scoped ENNReal NNReal Pointwise Classical MatrixGroups FourierTransform nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "V" => mixedSpace F
local notation "AF" => FiniteAdeleRing (𝓞 F) F
local notation "FI" => FractionalIdeal (𝓞 F)⁰ F

/-! ### Archimedean and finite parts of matrices -/

/-- The archimedean part of $g$, a matrix over $F_\infty$. -/
def infMat (g : SL2A F) : Matrix (Fin 2) (Fin 2) V := fun i j => (gA g i j).1

theorem infMat_det (g : SL2A F) : (infMat g).det = 1 := by
  have h := congrArg Prod.fst (gA_det g)
  rw [Matrix.det_fin_two]
  exact h

theorem mulVec_fst (g : SL2A F) (y : AdeleSpace F (Fin 2)) (i : Fin 2) :
    ((g : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec y i).1 = (infMat g).mulVec (fun j => (y j).1) i := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, infMat, gA]

theorem mulVec_snd (g : SL2A F) (y : AdeleSpace F (Fin 2)) (i : Fin 2) :
    ((g : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec y i).2 =
      (gA g i 0).2 * (y 0).2 + (gA g i 1).2 * (y 1).2 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, gA]

/-- $g^* = (\operatorname{adj}g)^{\mathsf T}$ in $\mathrm{SL}_2(\mathbb A_F)$. -/
def starSL (g : SL2A F) : SL2A F :=
  ⟨Matrix.transpose (g : Matrix (Fin 2) (Fin 2) (Adeles F)).adjugate, by
    rw [Matrix.det_transpose, Matrix.det_adjugate, g.2, one_pow]⟩

theorem starSL_mul (g h : SL2A F) : starSL (g * h) = starSL g * starSL h := by
  refine Subtype.ext ?_
  show Matrix.transpose ((g : Matrix (Fin 2) (Fin 2) (Adeles F)) * h).adjugate =
    Matrix.transpose (g : Matrix (Fin 2) (Fin 2) (Adeles F)).adjugate *
      Matrix.transpose (h : Matrix (Fin 2) (Fin 2) (Adeles F)).adjugate
  rw [Matrix.adjugate_mul_distrib, Matrix.transpose_mul]

theorem infMat_starSL (g : SL2A F) : infMat (starSL g) = starM (infMat g) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [infMat, starSL, starM, gA, Matrix.adjugate_fin_two, Matrix.transpose_apply]

theorem starSL_mem_KSub {g : SL2A F} (hg : g ∈ KSub F) : starSL g ∈ KSub F := by
  intro i j
  have h := hg
  simp only [mem_KSub] at h
  fin_cases i <;> fin_cases j <;> simp [starSL, gA, Matrix.adjugate_fin_two, Matrix.transpose_apply]
  · exact h 1 1
  · exact neg_mem_OHat (h 1 0)
  · exact neg_mem_OHat (h 0 1)
  · exact h 0 0

/-- $\overline{\gamma}^{\,*}$ for $\gamma\in\mathrm{SL}_2(F)$. -/
def starF (γ : SL(2, F)) : SL(2, F) :=
  ⟨Matrix.transpose (γ : Matrix (Fin 2) (Fin 2) F).adjugate, by
    rw [Matrix.det_transpose, Matrix.det_adjugate, γ.2, one_pow]⟩

theorem starSL_slEmb (γ : SL(2, F)) : starSL (slEmb F γ) = slEmb F (starF γ) := by
  refine Subtype.ext ?_
  show Matrix.transpose ((γ : Matrix (Fin 2) (Fin 2) F).map (diagRing F)).adjugate =
    (Matrix.transpose (γ : Matrix (Fin 2) (Fin 2) F).adjugate).map (diagRing F)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_adjugate, RingHom.mapMatrix_apply, Matrix.transpose_map]

/-- $(g\gamma)\,\xi = g\,(\gamma\xi)$ on $F^2$. -/
theorem mul_slEmb_mulVec_diagVec (g : SL2A F) (γ : SL(2, F)) (ξ : Fin 2 → F) :
    ((g * slEmb F γ : SL2A F) : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec (diagVec F (Fin 2) ξ) =
      (g : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec
        (diagVec F (Fin 2) ((γ : Matrix (Fin 2) (Fin 2) F).mulVec ξ)) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, diagVec_mulVec]

/-- Reindexing a sum over $F^2$ by $\xi\mapsto\gamma\xi$. -/
theorem tsum_mulVec_reindex {X : Type*} [AddCommMonoid X] [TopologicalSpace X] (γ : SL(2, F))
    (f : (Fin 2 → F) → X) :
    ∑' ξ : Fin 2 → F, f ((γ : Matrix (Fin 2) (Fin 2) F).mulVec ξ) = ∑' ξ, f ξ := by
  let e : (Fin 2 → F) ≃ (Fin 2 → F) :=
    { toFun := fun ξ => (γ : Matrix (Fin 2) (Fin 2) F).mulVec ξ
      invFun := fun ξ => ((γ⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec ξ
      left_inv := fun ξ => by
        simp only [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
      right_inv := fun ξ => by
        simp only [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] }
  exact e.tsum_eq f

/-! ### $\mathfrak d^{-1}\hat{\mathcal O}$ -/

/-- $\mathfrak d^{-1}\hat{\mathcal O} = \{a : v(a_v)\le\exp(d_v)\ \forall v\}$. -/
def DHat : Set AF := {a | ∀ v, Valued.v (a v) ≤ WithZero.exp (Analysis.diffExp v : ℤ)}

theorem add_mem_DHat {x y : AF} (hx : x ∈ DHat) (hy : y ∈ DHat) : x + y ∈ DHat :=
  fun v => (Valuation.map_add _ _ _).trans (max_le (hx v) (hy v))

theorem mul_mem_DHat {k x : AF} (hk : k ∈ OHat) (hx : x ∈ DHat) : k * x ∈ DHat := fun v => by
  show Valued.v (k v * x v) ≤ _
  rw [Valuation.map_mul]
  calc Valued.v (k v) * Valued.v (x v) ≤ 1 * Valued.v (x v) := mul_le_mul_left (hk v) _
    _ = _ := one_mul _
    _ ≤ _ := hx v

theorem zero_mem_DHat : (0 : AF) ∈ DHat := fun v => by
  show Valued.v (0 : v.adicCompletion F) ≤ _
  rw [map_zero]; exact zero_le'

theorem algebraMap_mem_DHat_iff (η : F) :
    algebraMap F AF η ∈ DHat ↔ η ∈ FractionalIdeal.dual ℤ ℚ (1 : FI) := by
  rw [Analysis.mem_dual_one_iff]
  rfl

theorem algebraMap_mem_OHat_iff' (ξ : F) : algebraMap F AF ξ ∈ OHat ↔ ξ ∈ (1 : FI) := by
  rw [algebraMap_mem_OHat_iff, FractionalIdeal.mem_one_iff]
  rfl

/-- For $h\in\mathrm{SL}_2(F_\infty)\times\mathrm{SL}_2(\hat{\mathcal O})$: $h\xi\in\hat{\mathcal O}^2\iff\xi\in\mathcal O_F^2$. -/
theorem mulVec_mem_OHat_iff {h : SL2A F} (hh : h ∈ KSub F) (ξ : Fin 2 → F) :
    (∀ i, (((h : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec (diagVec F (Fin 2) ξ)) i).2 ∈ OHat) ↔
      ∀ i, ξ i ∈ (1 : FI) := by
  simp_rw [← algebraMap_mem_OHat_iff']
  constructor
  · intro H i
    have hinv := inv_mem hh
    have : diagVec F (Fin 2) ξ = ((h⁻¹ : SL2A F) : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec
        ((h : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec (diagVec F (Fin 2) ξ)) := by
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    have h2 := congrArg (fun y => (y i).2) this
    simp only [diagVec_apply, diag_snd] at h2
    rw [h2, mulVec_snd]
    exact add_mem_OHat (mul_mem_OHat (hinv i 0) (H 0)) (mul_mem_OHat (hinv i 1) (H 1))
  · intro H i
    rw [mulVec_snd]
    exact add_mem_OHat (mul_mem_OHat (hh i 0) (H 0)) (mul_mem_OHat (hh i 1) (H 1))

/-- The same for $\mathfrak d^{-1}$. -/
theorem mulVec_mem_DHat_iff {h : SL2A F} (hh : h ∈ KSub F) (η : Fin 2 → F) :
    (∀ i, (((h : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec (diagVec F (Fin 2) η)) i).2 ∈ DHat) ↔
      ∀ i, η i ∈ FractionalIdeal.dual ℤ ℚ (1 : FI) := by
  simp_rw [← algebraMap_mem_DHat_iff]
  constructor
  · intro H i
    have hinv := inv_mem hh
    have : diagVec F (Fin 2) η = ((h⁻¹ : SL2A F) : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec
        ((h : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec (diagVec F (Fin 2) η)) := by
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    have h2 := congrArg (fun y => (y i).2) this
    simp only [diagVec_apply, diag_snd] at h2
    rw [h2, mulVec_snd]
    exact add_mem_DHat (mul_mem_DHat (hinv i 0) (H 0)) (mul_mem_DHat (hinv i 1) (H 1))
  · intro H i
    rw [mulVec_snd]
    exact add_mem_DHat (mul_mem_DHat (hh i 0) (H 0)) (mul_mem_DHat (hh i 1) (H 1))


/-! ### The test functions and the adelic Poisson formula -/

/-- $\Phi_u = G_u\otimes\mathbf 1_{\hat{\mathcal O}^2}$ on $\mathbb A_F^2$ (values in $[0,\infty]$). -/
def PhiA (u : Vˣ) (y : AdeleSpace F (Fin 2)) : ℝ≥0∞ :=
  if ∀ i, (y i).2 ∈ OHat then ENNReal.ofReal (gaussWR u fun i => (y i).1) else 0

/-- $\Psi_u = |d_F|^{-1}\hat G_u\otimes\mathbf 1_{(\mathfrak d^{-1}\hat{\mathcal O})^2}$. -/
def PsiA (u : Vˣ) (y : AdeleSpace F (Fin 2)) : ℝ≥0∞ :=
  if ∀ i, (y i).2 ∈ DHat then ENNReal.ofReal (|(discr F : ℝ)|⁻¹ * gaussWHat u fun i => (y i).1) else 0

theorem diagVec_fst (ξ : Fin 2 → F) : (fun i => (diagVec F (Fin 2) ξ i).1) = fun i => mixedEmbedding F (ξ i) := rfl

/-- Converting a sum over $F^2$ restricted to $L^2$ into a sum over $L^2$. -/
theorem tsum_ite_forall_mem (S : Set F) (f : (Fin 2 → F) → ℝ≥0∞) :
    ∑' ξ : Fin 2 → F, (if ∀ i, ξ i ∈ S then f ξ else 0) = ∑' ξ : Fin 2 → S, f fun i => (ξ i : F) := by
  have h1 : ∑' ξ : Fin 2 → F, (if ∀ i, ξ i ∈ S then f ξ else 0) =
      ∑' x : {ξ : Fin 2 → F // ∀ i, ξ i ∈ S}, f x := by
    rw [← tsum_subtype_eq_of_support_subset (s := {ξ : Fin 2 → F | ∀ i, ξ i ∈ S})]
    · exact tsum_congr fun x => if_pos x.2
    · intro ξ hξ
      by_contra h
      exact hξ (if_neg h)
  rw [h1]
  let e : {ξ : Fin 2 → F // ∀ i, ξ i ∈ S} ≃ (Fin 2 → S) := Equiv.subtypePiEquivPi
  rw [← e.symm.tsum_eq]
  rfl

/-- **The adelic Poisson formula on the lattice side** for $h\in\mathrm{SL}_2(F_\infty)\times\mathrm{SL}_2(\hat{\mathcal O})$. -/
theorem poisson_adelic_K (u : Vˣ) {h : SL2A F} (hh : h ∈ KSub F) :
    ∑' ξ : Fin 2 → F, PhiA u ((h : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec (diagVec F (Fin 2) ξ)) =
      ∑' η : Fin 2 → F, PsiA u ((starSL h : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec (diagVec F (Fin 2) η)) := by
  set M := infMat h
  have hM := infMat_det h
  -- the two sides as lattice sums
  have hL : ∀ ξ : Fin 2 → F, PhiA u ((h : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec (diagVec F (Fin 2) ξ)) =
      if ∀ i, ξ i ∈ (((I₁ (F := F) : FI)) : Set F) then
        ENNReal.ofReal (gaussWR u (M.mulVec fun i => mixedEmbedding F (ξ i))) else 0 := by
    intro ξ
    unfold PhiA
    by_cases hξ : ∀ i, ξ i ∈ (((I₁ (F := F) : FI)) : Set F)
    · rw [if_pos ((mulVec_mem_OHat_iff hh ξ).mpr hξ), if_pos hξ]
      congr 2
    · rw [if_neg (fun h' => hξ ((mulVec_mem_OHat_iff hh ξ).mp h')), if_neg hξ]
  have hR : ∀ η : Fin 2 → F, PsiA u ((starSL h : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec
        (diagVec F (Fin 2) η)) =
      if ∀ i, η i ∈ ((FractionalIdeal.dual ℤ ℚ ((I₁ (F := F) : FI)) : FI) : Set F) then
        ENNReal.ofReal (|(discr F : ℝ)|⁻¹ * gaussWHat u ((starM M).mulVec fun i => mixedEmbedding F (η i)))
      else 0 := by
    intro η
    unfold PsiA
    by_cases hη : ∀ i, η i ∈ ((FractionalIdeal.dual ℤ ℚ ((I₁ (F := F) : FI)) : FI) : Set F)
    · rw [if_pos ((mulVec_mem_DHat_iff (starSL_mem_KSub hh) η).mpr hη), if_pos hη]
      congr 3
      funext i
      rw [mulVec_fst, diagVec_fst, infMat_starSL]
    · rw [if_neg (fun h' => hη ((mulVec_mem_DHat_iff (starSL_mem_KSub hh) η).mp h')), if_neg hη]
  simp_rw [hL, hR]
  rw [tsum_ite_forall_mem, tsum_ite_forall_mem]
  -- the complex Poisson identity
  have hP := poisson_SL2Inf M hM (gaussW u)
  simp_rw [gaussW_apply, fourierW_gaussW] at hP
  set a : (Fin 2 → (((I₁ (F := F) : FI)) : Set F)) → ℝ :=
    fun ξ => gaussWR u (M.mulVec fun i => mixedEmbedding F (ξ i : F))
  set b : (Fin 2 → ((FractionalIdeal.dual ℤ ℚ ((I₁ (F := F) : FI)) : FI) : Set F)) → ℝ :=
    fun η => gaussWHat u ((starM M).mulVec fun i => mixedEmbedding F (η i : F))
  have ha0 : ∀ ξ, 0 ≤ a ξ := fun ξ => (gaussWR_pos _ _).le
  have hb0 : ∀ η, 0 ≤ b η := fun η => (gaussWHat_pos _ _).le
  have hsa : Summable a := by
    have := summable_SL2Inf M hM (gaussW u)
    simp_rw [gaussW_apply, Complex.norm_real, Real.norm_eq_abs] at this
    exact this.congr fun ξ => abs_of_pos (gaussWR_pos _ _)
  have hreal : ∑' ξ, a ξ = |(discr F : ℝ)|⁻¹ * ∑' η, b η := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_tsum, Complex.ofReal_mul, Complex.ofReal_tsum]
    exact hP
  have hpos : 0 < ∑' ξ, a ξ := by
    let z0 : Fin 2 → (((I₁ (F := F) : FI)) : Set F) :=
      fun _ => ⟨0, (FractionalIdeal.mem_one_iff _).mpr ⟨0, by simp⟩⟩
    have h0 : a z0 = 1 := by
      simp only [a, z0, map_zero]
      have : (fun _ : Fin 2 => (0 : V)) = 0 := rfl
      rw [this, Matrix.mulVec_zero, gaussWR_zero]
    calc (0 : ℝ) < a z0 := by rw [h0]; exact one_pos
      _ ≤ ∑' ξ, a ξ := hsa.le_tsum z0 fun ξ _ => ha0 ξ
  have hsb : Summable b := by
    by_contra hns
    rw [tsum_eq_zero_of_not_summable hns, mul_zero] at hreal
    exact hpos.ne' hreal
  have hd : 0 ≤ |(discr F : ℝ)|⁻¹ := inv_nonneg.mpr (abs_nonneg _)
  rw [ENNReal.ofReal_tsum_of_nonneg ha0 hsa |>.symm]
  rw [show (fun η => ENNReal.ofReal (|(discr F : ℝ)|⁻¹ * b η)) = fun η => ENNReal.ofReal (|(discr F : ℝ)|⁻¹ * b η)
    from rfl, ← ENNReal.ofReal_tsum_of_nonneg (fun η => mul_nonneg hd (hb0 η)) (hsb.mul_left _), tsum_mul_left,
    hreal]

/-- **The adelic Poisson formula** $\sum_{\xi\in F^2}\Phi_u(g\xi) = \sum_{\eta\in F^2}\Psi_u(g^*\eta)$ for every
$g\in\mathrm{SL}_2(\mathbb A_F)$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), Thm 4.2.1 (adelic Poisson) [unverified]"]
theorem poisson_adelic (u : Vˣ) (g : SL2A F) :
    ∑' ξ : Fin 2 → F, PhiA u ((g : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec (diagVec F (Fin 2) ξ)) =
      ∑' η : Fin 2 → F, PsiA u ((starSL g : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec (diagVec F (Fin 2) η)) := by
  obtain ⟨γ, hγ⟩ := exists_mul_slEmb_inv_mem_K g
  set h := g * (slEmb F γ)⁻¹
  have hg : g = h * slEmb F γ := by simp [h]
  rw [hg, starSL_mul, starSL_slEmb]
  simp_rw [mul_slEmb_mulVec_diagVec]
  rw [tsum_mulVec_reindex γ (fun ξ => PhiA u ((h : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec
      (diagVec F (Fin 2) ξ))),
    tsum_mulVec_reindex (starF γ) (fun η => PsiA u ((starSL h : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec
      (diagVec F (Fin 2) η)))]
  exact poisson_adelic_K u hγ


/-! ### Measurability and integrals of the test functions -/

theorem measurableSet_DHat : MeasurableSet (DHat (F := F)) := by
  have : (DHat (F := F)) = ⋂ v, (fun a : AF => a v) ⁻¹'
      (Analysis.latticeV v (-(Analysis.diffExp v : ℤ)) : Set (v.adicCompletion F)) := by
    ext a
    simp only [DHat, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe,
      Analysis.mem_latticeV, neg_neg]
  rw [this]
  exact MeasurableSet.iInter fun v => (Analysis.measurableSet_latticeV v _).preimage
    (measurable_finiteAdele_eval v)

theorem continuous_gR : Continuous (gR (F := F)) := by
  unfold gR
  fun_prop

theorem measurable_gaussWR (u : Vˣ) : Measurable (gaussWR (F := F) u) := by
  unfold gaussWR
  have h0 : Continuous fun y : Fin 2 → V => (u : V) * y 0 := continuous_const.mul (continuous_apply 0)
  have h1 : Continuous fun y : Fin 2 → V => (u : V) * y 1 := continuous_const.mul (continuous_apply 1)
  exact ((continuous_gR.comp h0).mul (continuous_gR.comp h1)).measurable

theorem gaussWHat_eq (u : Vˣ) (z : Fin 2 → V) : gaussWHat u z = (modInf u)⁻¹ ^ 2 * gaussWR u⁻¹ z := rfl

theorem measurable_gaussWHat (u : Vˣ) : Measurable (gaussWHat (F := F) u) := by
  have : gaussWHat (F := F) u = fun z => (modInf u)⁻¹ ^ 2 * gaussWR u⁻¹ z := funext (gaussWHat_eq u)
  rw [this]
  exact measurable_const.mul (measurable_gaussWR _)

theorem measurable_infPart : Measurable fun y : AdeleSpace F (Fin 2) => fun i => (y i).1 :=
  measurable_pi_iff.mpr fun i => measurable_fst.comp (measurable_pi_apply i)

theorem measurableSet_forall_snd {S : Set AF} (hS : MeasurableSet S) :
    MeasurableSet {y : AdeleSpace F (Fin 2) | ∀ i, (y i).2 ∈ S} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => hS.preimage (measurable_snd.comp (measurable_pi_apply i))

theorem measurable_PhiA (u : Vˣ) : Measurable (PhiA (F := F) u) :=
  Measurable.ite (measurableSet_forall_snd measurableSet_OHat)
    (ENNReal.measurable_ofReal.comp ((measurable_gaussWR u).comp measurable_infPart)) measurable_const

theorem measurable_PsiA (u : Vˣ) : Measurable (PsiA (F := F) u) :=
  Measurable.ite (measurableSet_forall_snd measurableSet_DHat)
    (ENNReal.measurable_ofReal.comp (measurable_const.mul ((measurable_gaussWHat u).comp measurable_infPart)))
    measurable_const

/-- $\int_{\mathbb A^2}(a\otimes b) = \int a\cdot\int b$ for the self-dual measure. -/
theorem lintegral_muAddVec_prod (a : (Fin 2 → V) → ℝ≥0∞) (b : (Fin 2 → AF) → ℝ≥0∞) (ha : Measurable a)
    (hb : Measurable b) :
    ∫⁻ y, a (fun i => (y i).1) * b (fun i => (y i).2) ∂muAddVec F (Fin 2) =
      (∫⁻ x, a x ∂muInfVec F (Fin 2)) * ∫⁻ x, b x ∂muFinVec F (Fin 2) := by
  have hp := measurePreserving_arrowProd (F := F) (ι := Fin 2)
  have : (fun y : AdeleSpace F (Fin 2) => a (fun i => (y i).1) * b (fun i => (y i).2)) =
      (fun p : (Fin 2 → V) × (Fin 2 → AF) => a p.1 * b p.2) ∘
        (MeasurableEquiv.arrowProdEquivProdArrow (mixedSpace F) AF (Fin 2)) := rfl
  rw [this]
  show ∫⁻ y, (fun p : (Fin 2 → V) × (Fin 2 → AF) => a p.1 * b p.2)
    (MeasurableEquiv.arrowProdEquivProdArrow (mixedSpace F) AF (Fin 2) y) ∂muAddVec F (Fin 2) = _
  rw [hp.lintegral_comp (f := fun p : (Fin 2 → V) × (Fin 2 → AF) => a p.1 * b p.2)
      ((ha.comp measurable_fst).mul (hb.comp measurable_snd)),
    lintegral_prod_mul ha.aemeasurable hb.aemeasurable]

theorem integrable_gaussWR (u : Vˣ) : Integrable (gaussWR (F := F) u) (muInfVec F (Fin 2)) := by
  have h := (gaussW (F := F) u).integrable (μ := muInfVec F (Fin 2))
  have h' : Integrable (fun y => (gaussWR u y : ℂ)) (muInfVec F (Fin 2)) := by
    convert h using 1
    funext y
    exact (gaussW_apply u y).symm
  simpa using h'.re

theorem lintegral_ofReal_gaussWR (u : Vˣ) :
    ∫⁻ x, ENNReal.ofReal (gaussWR u x) ∂muInfVec F (Fin 2) = ENNReal.ofReal ((modInf u)⁻¹ ^ 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gaussWR u)
    (Filter.Eventually.of_forall fun x => (gaussWR_pos u x).le)]
  congr 1
  have h := integral_gaussW (F := F) u
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

theorem lintegral_ofReal_gaussWHat (u : Vˣ) :
    ∫⁻ x, ENNReal.ofReal (gaussWHat u x) ∂muInfVec F (Fin 2) = 1 := by
  have hi : Integrable (gaussWHat (F := F) u) (muInfVec F (Fin 2)) := by
    have : gaussWHat (F := F) u = fun z => (modInf u)⁻¹ ^ 2 * gaussWR u⁻¹ z := funext (gaussWHat_eq u)
    rw [this]
    exact (integrable_gaussWR _).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun x => (gaussWHat_pos u x).le)]
  have h := integral_gaussWHat (F := F) u
  rw [integral_complex_ofReal] at h
  have h' : ∫ z, gaussWHat u z ∂muInfVec F (Fin 2) = 1 := by exact_mod_cast h
  rw [h', ENNReal.ofReal_one]

theorem muFinVec_OHat2 :
    muFinVec F (Fin 2) {x | ∀ i, x i ∈ OHat} = ENNReal.ofReal (|(discr F : ℝ)|⁻¹) := by
  have : {x : Fin 2 → AF | ∀ i, x i ∈ OHat} = Set.univ.pi fun _ => OHat := by
    ext x; simp
  rw [this, muFinVec, Measure.pi_pi, Fin.prod_univ_two, muFin_OHat, ← ENNReal.ofReal_mul (ohatVol_pos.le),
    ohatVol, ← mul_inv, Real.mul_self_sqrt (abs_nonneg _)]

/-- $\int\Phi_u = |d_F|^{-1}\Delta(u)^{-2}$. -/
theorem lintegral_PhiA (u : Vˣ) :
    ∫⁻ y, PhiA u y ∂muAddVec F (Fin 2) = ENNReal.ofReal (|(discr F : ℝ)|⁻¹ * (modInf u)⁻¹ ^ 2) := by
  have : PhiA (F := F) u = fun y => ENNReal.ofReal (gaussWR u (fun i => (y i).1)) *
      ({x : Fin 2 → AF | ∀ i, x i ∈ OHat}.indicator 1 (fun i => (y i).2)) := by
    funext y
    unfold PhiA
    by_cases h : ∀ i, (y i).2 ∈ OHat
    · rw [if_pos h, Set.indicator_of_mem (show (fun i => (y i).2) ∈ {x : Fin 2 → AF | ∀ i, x i ∈ OHat} from h),
        Pi.one_apply, mul_one]
    · rw [if_neg h, Set.indicator_of_notMem (show (fun i => (y i).2) ∉ {x : Fin 2 → AF | ∀ i, x i ∈ OHat} from h),
        mul_zero]
  have hS : MeasurableSet {x : Fin 2 → AF | ∀ i, x i ∈ OHat} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_OHat.preimage (measurable_pi_apply i)
  simp only [this]
  rw [lintegral_muAddVec_prod (fun x => ENNReal.ofReal (gaussWR u x))
    ({x : Fin 2 → AF | ∀ i, x i ∈ OHat}.indicator 1) (ENNReal.measurable_ofReal.comp (measurable_gaussWR u))
    (measurable_one.indicator hS), lintegral_ofReal_gaussWR, lintegral_indicator_one hS, muFinVec_OHat2,
    ← ENNReal.ofReal_mul (by positivity), mul_comm]

variable (F) in
/-- $\int\Psi_u$, independent of $u$. -/
def AConst : ℝ≥0∞ := ENNReal.ofReal (|(discr F : ℝ)|⁻¹) * muFinVec F (Fin 2) {x | ∀ i, x i ∈ DHat}

theorem lintegral_PsiA (u : Vˣ) : ∫⁻ y, PsiA u y ∂muAddVec F (Fin 2) = AConst F := by
  have : PsiA (F := F) u = fun y => ENNReal.ofReal (|(discr F : ℝ)|⁻¹) *
      ENNReal.ofReal (gaussWHat u (fun i => (y i).1)) *
      ({x : Fin 2 → AF | ∀ i, x i ∈ DHat}.indicator 1 (fun i => (y i).2)) := by
    funext y
    unfold PsiA
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (abs_nonneg _))]
    by_cases h : ∀ i, (y i).2 ∈ DHat
    · rw [if_pos h, Set.indicator_of_mem (show (fun i => (y i).2) ∈ {x : Fin 2 → AF | ∀ i, x i ∈ DHat} from h),
        Pi.one_apply, mul_one]
    · rw [if_neg h, Set.indicator_of_notMem (show (fun i => (y i).2) ∉ {x : Fin 2 → AF | ∀ i, x i ∈ DHat} from h),
        mul_zero]
  have hS : MeasurableSet {x : Fin 2 → AF | ∀ i, x i ∈ DHat} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_DHat.preimage (measurable_pi_apply i)
  have hfin : Measurable fun y : AdeleSpace F (Fin 2) => fun i => (y i).2 :=
    measurable_pi_iff.mpr fun i => measurable_snd.comp (measurable_pi_apply i)
  have hm : Measurable fun y : AdeleSpace F (Fin 2) => ENNReal.ofReal (gaussWHat u fun i => (y i).1) *
      {x : Fin 2 → AF | ∀ i, x i ∈ DHat}.indicator 1 fun i => (y i).2 :=
    (ENNReal.measurable_ofReal.comp ((measurable_gaussWHat u).comp measurable_infPart)).mul
      ((measurable_one.indicator hS).comp hfin)
  simp_rw [this, mul_assoc]
  rw [lintegral_const_mul _ hm,
    lintegral_muAddVec_prod (fun x => ENNReal.ofReal (gaussWHat u x)) _
      (ENNReal.measurable_ofReal.comp (measurable_gaussWHat u)) (measurable_one.indicator hS),
    lintegral_ofReal_gaussWHat, one_mul, lintegral_indicator_one hS, AConst]


/-! ### Integrating the Poisson formula over $G_{\mathbb A}/G_k$ -/

theorem tsum_split_zero (f : (Fin 2 → F) → ℝ≥0∞) :
    ∑' ξ : Fin 2 → F, f ξ = f 0 + ∑' ξ : NZVec F, f ξ.1 := by
  rw [ENNReal.tsum_eq_add_tsum_ite 0]
  congr 1
  show _ = ∑' ξ : ({ξ : Fin 2 → F | ξ ≠ 0} : Set (Fin 2 → F)), f ξ
  rw [tsum_subtype]
  refine tsum_congr fun ξ => ?_
  by_cases h : ξ = 0
  · rw [if_pos h, Set.indicator_of_notMem (show ξ ∉ {ξ : Fin 2 → F | ξ ≠ 0} from fun h' => h' h)]
  · rw [if_neg h, Set.indicator_of_mem (show ξ ∈ {ξ : Fin 2 → F | ξ ≠ 0} from h)]

theorem diagVec_zero : diagVec F (Fin 2) 0 = 0 := map_zero _

/-- $g^* = wgw^{-1}$. -/
theorem starSL_eq_conj (g : SL2A F) :
    starSL g = slEmb F wMat * g * (slEmb F wMat)⁻¹ := by
  have hW : ((slEmb F wMat : SL2A F) : Matrix (Fin 2) (Fin 2) (Adeles F)) = !![0, 1; -1, 0] := by
    change (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F).map (diagRing F) = _
    refine funext fun i => funext fun j => ?_
    fin_cases i <;> fin_cases j <;> simp
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    hW]
  show Matrix.transpose (g : Matrix (Fin 2) (Fin 2) (Adeles F)).adjugate = _
  refine funext fun i => funext fun j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.vecMul,
      dotProduct]

theorem starSL_mulVec (g : SL2A F) (η : Fin 2 → F) :
    (starSL g : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec (diagVec F (Fin 2) η) =
      (slEmb F wMat : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec ((g : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec
        (diagVec F (Fin 2) (((wMat⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec η))) := by
  rw [starSL_eq_conj, diagVec_mulVec, map_inv, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- **The integrated Poisson identity**: $\tau + c_u = c_u\tau + A$ with $c_u = |d_F|^{-1}\Delta(u)^{-2}$. -/
theorem integrated_identity (u : Vˣ) {D : Set (SL2A F)} (hD : IsFundamentalDomain (SL(2, F)) D (muT F)) :
    muT F D + ENNReal.ofReal (|(discr F : ℝ)|⁻¹ * (modInf u)⁻¹ ^ 2) =
      ENNReal.ofReal (|(discr F : ℝ)|⁻¹ * (modInf u)⁻¹ ^ 2) * muT F D + AConst F := by
  set W : SL2A F := slEmb F wMat
  have hPhi0 : PhiA u 0 = 1 := by
    simp only [PhiA, Pi.zero_apply, Prod.snd_zero, Prod.fst_zero]
    rw [if_pos (fun _ => zero_mem_OHat)]
    have : (fun _ : Fin 2 => (0 : V)) = 0 := rfl
    rw [this, gaussWR_zero, ENNReal.ofReal_one]
  have hPsi0 : PsiA u 0 = ENNReal.ofReal (|(discr F : ℝ)|⁻¹ * (modInf u)⁻¹ ^ 2) := by
    simp only [PsiA, Pi.zero_apply, Prod.snd_zero, Prod.fst_zero]
    rw [if_pos (fun _ => zero_mem_DHat)]
    have : (fun _ : Fin 2 => (0 : V)) = 0 := rfl
    rw [this, gaussWHat_zero]
  -- the two sides, split at `ξ = 0`
  have hL : ∀ g : SL2A F, ∑' ξ : Fin 2 → F, PhiA u ((g : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec
      (diagVec F (Fin 2) ξ)) = 1 + ∑' ξ : NZVec F, PhiA u ((g : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec
        (diagVec F (Fin 2) ξ.1)) := by
    intro g
    rw [tsum_split_zero, diagVec_zero, Matrix.mulVec_zero, hPhi0]
  have hR : ∀ g : SL2A F, ∑' η : Fin 2 → F, PsiA u ((starSL g : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec
      (diagVec F (Fin 2) η)) = ENNReal.ofReal (|(discr F : ℝ)|⁻¹ * (modInf u)⁻¹ ^ 2) +
        ∑' η : NZVec F, (fun y => PsiA u ((W : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec y))
          ((g : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec (diagVec F (Fin 2) η.1)) := by
    intro g
    rw [tsum_split_zero, diagVec_zero, Matrix.mulVec_zero, hPsi0]
    congr 1
    simp_rw [starSL_mulVec]
    have := (MulAction.toPerm (wMat⁻¹ : SL(2, F)) : Equiv.Perm (NZVec F)).tsum_eq
      (fun η : NZVec F => PsiA u ((W : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec
        ((g : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec (diagVec F (Fin 2) η.1))))
    rw [← this]
    rfl
  have hPm := measurable_PhiA (F := F) u
  have hWm : Measurable fun y : AdeleSpace F (Fin 2) => (W : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec y :=
    (show Continuous fun y : AdeleSpace F (Fin 2) => (W : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec y from
      continuous_const.matrix_mulVec continuous_id).measurable
  have hPsim : Measurable fun y => PsiA u ((W : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec y) :=
    (measurable_PsiA u).comp hWm
  have hint := congrArg (fun φ : SL2A F → ℝ≥0∞ => ∫⁻ g in D, φ g ∂muT F)
    (funext fun g => (hL g).symm.trans ((poisson_adelic u g).trans (hR g)))
  simp only at hint
  rw [lintegral_add_left measurable_const, lintegral_add_left measurable_const, setLIntegral_const,
    setLIntegral_const, one_mul, lintegral_tsum_mulVec_eq hD _ hPm, lintegral_tsum_mulVec_eq hD _ hPsim,
    lintegral_PhiA] at hint
  have hWpres : ∫⁻ y, PsiA u ((W : Matrix (Fin 2) (Fin 2) (Adeles F)).mulVec y) ∂muAddVec F (Fin 2) =
      ∫⁻ y, PsiA u y ∂muAddVec F (Fin 2) := by
    rw [← lintegral_map (measurable_PsiA u) hWm, map_mulVec_SL2A]
  rw [hWpres, lintegral_PsiA] at hint
  exact hint


/-! ### $\tau(\mathrm{SL}_2) = 1$ -/

/-- The unit $2\in F_\infty^\times$. -/
def twoU : Vˣ := Units.map (algebraMap ℝ V).toMonoidHom (Units.mk0 2 two_ne_zero)

theorem modInf_one : modInf (1 : Vˣ) = 1 := by
  rw [modInf, map_one, NNReal.coe_one]

theorem modInf_twoU : modInf (twoU (F := F)) = 2 ^ Module.finrank ℚ F := by
  rw [modInf, distribHaarChar_mixedSpace]
  have h : LinearMap.mulLeft ℝ ((twoU (F := F) : Vˣ) : V) = (2 : ℝ) • LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    simp [twoU, Algebra.smul_def]
  rw [h, LinearMap.det_smul, LinearMap.det_id, mul_one, mixedEmbedding.finrank, abs_of_pos (by positivity)]

theorem modInf_twoU_ne_one : modInf (twoU (F := F)) ≠ 1 := by
  rw [modInf_twoU]
  exact (one_lt_pow₀ one_lt_two (Module.finrank_pos (R := ℚ) (M := F)).ne').ne'

/-- **The Tamagawa number of $\mathrm{SL}_2$ over any number field is $1$**: Weil's
$\operatorname{vol}(\mathrm{SL}_2(\mathbb A_F)/\mathrm{SL}_2(F)) = 1$ for the Tamagawa measure $\mu_T$ (the fibration
measure $\mu_T = \Psi_*(dy|_P\otimes dx)$ of AAG Thm 2.4.3 for $\mathrm{SL}_2\to\mathbb A^2\setminus0$ with fibre
$N\cong\mathbb G_a$, both factors self-dual). -/
@[kb "weil1982" "§3.3 / Ch. III (τ(SL_n) = 1) [unverified locator]"]
theorem tamagawa_SL2 : covolume (SL(2, F)) (SL2A F) (muT F) = 1 := by
  obtain ⟨D, hDm, hD⟩ := exists_measurableSet_forall_existsUnique_right (F := F)
  have hFD : IsFundamentalDomain (SL(2, F)) D (muT F) := IsFundamentalDomain.mk' hDm.nullMeasurableSet hD
  rw [hFD.covolume_eq_volume]
  have h1 := integrated_identity (1 : Vˣ) hFD
  have h2 := integrated_identity (twoU (F := F)) hFD
  rw [modInf_one, inv_one, one_pow, mul_one] at h1
  have hτ := (muT_fundDomain_lt_top hFD).ne
  set τ := muT F D
  set A := AConst F
  set d := |(discr F : ℝ)|⁻¹
  set m := (modInf (twoU (F := F)))⁻¹ ^ 2
  have hd0 : 0 ≤ d := inv_nonneg.mpr (abs_nonneg _)
  have hdpos : 0 < d := inv_pos.mpr (abs_pos.mpr (by exact_mod_cast discr_ne_zero F))
  have hm0 : 0 ≤ m := by positivity
  have hA : A ≠ ⊤ := by
    intro hAt
    rw [hAt, add_top] at h1
    exact (ENNReal.add_ne_top.mpr ⟨hτ, ENNReal.ofReal_ne_top⟩) h1
  have r1 := congrArg ENNReal.toReal h1
  have r2 := congrArg ENNReal.toReal h2
  rw [ENNReal.toReal_add hτ ENNReal.ofReal_ne_top, ENNReal.toReal_add (ENNReal.mul_ne_top
    ENNReal.ofReal_ne_top hτ) hA, ENNReal.toReal_mul, ENNReal.toReal_ofReal hd0] at r1
  rw [ENNReal.toReal_add hτ ENNReal.ofReal_ne_top, ENNReal.toReal_add (ENNReal.mul_ne_top
    ENNReal.ofReal_ne_top hτ) hA, ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hd0 hm0)] at r2
  have hm1 : m ≠ 1 := by
    intro h
    have hpos := modInf_pos (twoU (F := F))
    have : (modInf (twoU (F := F)))⁻¹ = 1 := by
      exact (pow_eq_one_iff_of_nonneg (inv_nonneg.mpr hpos.le) two_ne_zero).mp h
    exact modInf_twoU_ne_one (inv_eq_one.mp this)
  have ht : τ.toReal = 1 := by
    have hdiff : (d - d * m) * (τ.toReal - 1) = 0 := by linear_combination r2 - r1
    rcases mul_eq_zero.mp hdiff with h | h
    · exfalso
      have : d * (1 - m) = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h' | h'
      · exact hdpos.ne' h'
      · exact hm1 (by linarith)
    · linarith
  rw [← ENNReal.ofReal_toReal hτ, ht, ENNReal.ofReal_one]

end

end QuadFormsKB.Tamagawa.Measure.Weil
