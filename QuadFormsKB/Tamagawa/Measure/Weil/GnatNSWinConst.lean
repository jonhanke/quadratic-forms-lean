/-
# Local constants — $\prod_{w\mid v}q_w^{e_w} = q_v^2$ and $c_v^2\,|4d|_v = 1$

**Layer:** a number field $F$, $K = F(\delta)$ with basis $b = (1,\delta)$, $\delta^2 = d$, a finite place $v$ of $F$ (any:
split, inert, ramified, dyadic); $\Phi$ = `localPi b v` $: F_v^2\to\prod_{w\mid v}K_w$, $c_v$ = `localConst b v`
($\Phi_*dx^{\otimes2} = c_v\prod_w\mu_w$).

* **`volVN_preimage_mulVec`**: $\mathrm{vol}(M^{-1}S) = |\det M|_v^{-1}\mathrm{vol}(S)$ on $F_v^2$ (`glHaarChar`).
* **`prod_q_pow_ramE`**: $\prod_{w\mid v}q_w^{e_w} = q_v^2$ (scale $\Phi^{-1}(\prod_w\mathcal O_w)$ by a uniformizer of $F_v$).
* **`localConst_sq_mul`**: $c_v^2\,|4d|_v = 1$, i.e. $c_v = |\det(\operatorname{Tr}(b_ib_j))|_v^{-1/2}$ at every finite place,
  by lattice duality ($\Phi^{-1}(\prod_w\mathfrak p_w^{-d_w})$ is the trace dual of $\Phi^{-1}(\prod_w\mathcal O_w) = A\mathcal O_v^2$).

Source: Tate's thesis, Cassels–Fröhlich Ch. XV §2.2 (self-dual measures, $\operatorname{vol}(L)\operatorname{vol}(L^\perp)=1$)
[unverified]; Neukirch, *Algebraic Number Theory*, III.2 (discriminant and different) [unverified].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSWinUnits

open MeasureTheory Set Function Topology NumberField IsDedekindDomain WithZero Matrix
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa LerayPadic LocalDensity QuadFormsKB.Quat.Gnat

section Scaling

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

instance : (volVN (ι := Fin 2) v).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

/-- **$\mathrm{vol}(M^{-1}S) = |\det M|_v^{-1}\mathrm{vol}(S)$** on $F_v^2$. -/
theorem volVN_preimage_mulVec (M : GL (Fin 2) Fv) {S : Set (Fin 2 → Fv)} (hS : MeasurableSet S) :
    volVN (ι := Fin 2) v ((M : Matrix (Fin 2) (Fin 2) Fv).mulVec ⁻¹' S) =
      (ENNReal.ofReal ‖(GeneralLinearGroup.det M : Fv)‖)⁻¹ * volVN (ι := Fin 2) v S := by
  have h := map_mulVec_eq_glHaarChar_inv (volVN (ι := Fin 2) v) M
  have hm : Measurable (M : Matrix (Fin 2) (Fin 2) Fv).mulVec := (Continuous.matrix_mulVec continuous_const
    continuous_id).measurable
  rw [← Measure.map_apply hm hS, h, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, glHaarChar_eq_of_field]
  congr 1
  have hne : distribHaarChar Fv (GeneralLinearGroup.det M) ≠ 0 := by
    intro h0
    have h1 := distribHaarChar_adic_eq_norm v (GeneralLinearGroup.det M)
    rw [h0, NNReal.coe_zero] at h1
    exact (norm_ne_zero_iff.2 (GeneralLinearGroup.det M).ne_zero) h1.symm
  rw [ENNReal.coe_inv hne, ← distribHaarChar_adic_eq_norm, ENNReal.ofReal_coe_nnreal]

theorem norm_of_valued_exp {x : Fv} {k : ℤ} (hx : Valued.v x = exp (-k)) : ‖x‖ = (DVR.q 𝔬 : ℝ) ^ (-k) := by
  have hx0 : x ≠ 0 := by rintro rfl; rw [map_zero] at hx; exact exp_ne_zero hx.symm
  rw [QuadFormsKB.LocalZeta.norm_eq_absNorm_pow v hx0, hx, log_exp, NF.q_completion]

end Scaling

section Ramification

variable {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] [Algebra F K] {d : 𝓞 F}
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem localPi_smul_apply (r : Fv) (c : Fin 2 → Fv) (w : PlaceSet (K := K) v) :
    localPi bK v (r • c) w = localRingHom v w.1 w.2 r * localPi bK v c w := by
  rw [map_smul]; rfl

theorem volVN_preimage_localPi {X : Set (PlaceProd (K := K) v)} (hX : MeasurableSet X) :
    volVN (ι := Fin 2) v (localPiCLE bK v ⁻¹' X) = (localConst bK v : ℝ≥0∞) * placeMeasure (K := K) v X := by
  have h := map_volVN_localPi bK v
  rw [← Measure.map_apply (localPiCLE bK v).continuous.measurable hX, h, Measure.smul_apply]
  rfl

theorem placeMeasure_pi_latticeV (k : PlaceSet (K := K) v → ℤ) :
    placeMeasure (K := K) v (Set.pi Set.univ fun w => (Analysis.latticeV w.1 (k w) : Set (w.1.adicCompletion K))) =
      ∏ w, Analysis.selfDualV w.1 (Analysis.latticeV w.1 (k w)) := by
  unfold placeMeasure; rw [Measure.pi_pi]

theorem measurableSet_pi_latticeV (k : PlaceSet (K := K) v → ℤ) :
    MeasurableSet (Set.pi Set.univ fun w : PlaceSet (K := K) v =>
      (Analysis.latticeV w.1 (k w) : Set (w.1.adicCompletion K))) :=
  MeasurableSet.univ_pi fun w => QuadFormsKB.Analysis.measurableSet_latticeV w.1 _

include hb₀ hb₁ in
/-- **$\prod_{w\mid v}q_w^{e_w} = q_v^2$** (the local degree, $\sum_{w\mid v}e_wf_w = 2$, in measure form). -/
theorem prod_q_pow_ramE :
    ∏ w : PlaceSet (K := K) v, (DVR.q (w.1.adicCompletionIntegers K) : ℝ) ^ ramE v w.1 =
      (DVR.q 𝔬 : ℝ) ^ 2 := by
  set s := algebraMap F Fv (unifF v : F)
  have hs := valued_unifF v
  have hs0 : s ≠ 0 := by intro h; rw [show algebraMap F Fv (unifF v : F) = s from rfl, h, map_zero] at hs
                         exact exp_ne_zero hs.symm
  set M : GL (Fin 2) Fv := GeneralLinearGroup.mkOfDetNeZero (s⁻¹ • (1 : Matrix (Fin 2) (Fin 2) Fv))
    (by rw [det_smul, det_one, mul_one]; exact pow_ne_zero _ (inv_ne_zero hs0))
  have hM : (M : Matrix (Fin 2) (Fin 2) Fv) = s⁻¹ • 1 := rfl
  set X0 := Set.pi Set.univ fun w : PlaceSet (K := K) v => (Analysis.latticeV w.1 0 : Set (w.1.adicCompletion K))
  set X1 := Set.pi Set.univ fun w : PlaceSet (K := K) v =>
    (Analysis.latticeV w.1 (ramE v w.1 : ℤ) : Set (w.1.adicCompletion K))
  have hpre : (M : Matrix (Fin 2) (Fin 2) Fv).mulVec ⁻¹' (localPiCLE bK v ⁻¹' X0) = localPiCLE bK v ⁻¹' X1 := by
    ext c
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, SetLike.mem_coe,
      QuadFormsKB.Analysis.mem_latticeV, localPiCLE_apply, hM, Matrix.smul_mulVec, Matrix.one_mulVec]
    refine forall_congr' fun w => ?_
    simp only [Set.mem_univ, true_implies, SetLike.mem_coe, QuadFormsKB.Analysis.mem_latticeV]
    have hsw : Valued.v (localRingHom v w.1 w.2 s) = exp (-(ramE v w.1 : ℤ)) := valued_localRingHom_unifF v w.1 w.2
    rw [localPi_smul_apply, map_mul, map_inv₀, map_inv₀, hsw]
    generalize Valued.v (localPi bK v c w) = x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · obtain ⟨k, rfl⟩ : ∃ k, x = exp k := ⟨log x, (exp_log hx).symm⟩
      rw [← WithZero.exp_neg, ← exp_add, exp_le_exp, exp_le_exp]; omega
  have h1 := volVN_preimage_mulVec v M (measurableSet_pi_latticeV v (fun _ => 0) |>.preimage
    (localPiCLE bK v).continuous.measurable)
  rw [hpre, volVN_preimage_localPi, volVN_preimage_localPi] at h1
  rotate_left
  · exact measurableSet_pi_latticeV v _
  · exact measurableSet_pi_latticeV v _
  rw [placeMeasure_pi_latticeV, placeMeasure_pi_latticeV] at h1
  have hdet : ‖(GeneralLinearGroup.det M : Fv)‖ = (DVR.q 𝔬 : ℝ) ^ 2 := by
    rw [GeneralLinearGroup.val_det_apply, hM, det_smul, det_one, mul_one, Fintype.card_fin, norm_pow, norm_inv,
      norm_of_valued_exp v (k := 1) (by rw [hs]), _root_.zpow_neg_one, inv_inv]
  rw [hdet] at h1
  have h2 := congrArg ENNReal.toReal h1
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (DVR.q 𝔬 : ℝ) ^ 2),
    ENNReal.toReal_prod, ENNReal.coe_toReal] at h2
  have hnat : ∀ w : PlaceSet (K := K) v, (Analysis.selfDualV w.1 (Analysis.latticeV w.1 ((ramE v w.1 : ℕ) : ℤ))).toReal
      = (Analysis.selfDualV w.1 (Analysis.latticeV w.1 0)).toReal / (DVR.q (w.1.adicCompletionIntegers K) : ℝ) ^ ramE v w.1 := by
    intro w
    rw [selfDualV_latticeV_nat, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  simp only [hnat, Finset.prod_div_distrib] at h2
  have hc : (0 : ℝ) < (localConst bK v : ℝ) := localConst_pos bK v
  have hV : (0 : ℝ) < ∏ w : PlaceSet (K := K) v, (Analysis.selfDualV w.1 (Analysis.latticeV w.1 0)).toReal :=
    Finset.prod_pos fun w _ => ENNReal.toReal_pos (selfDualV_latticeV_ne_zero w.1 0) (selfDualV_latticeV_ne_top w.1 0)
  have hQ : (0 : ℝ) < ∏ w : PlaceSet (K := K) v, (DVR.q (w.1.adicCompletionIntegers K) : ℝ) ^ ramE v w.1 :=
    Finset.prod_pos fun w _ => pow_pos (by exact_mod_cast DVR.q_pos (R := w.1.adicCompletionIntegers K)) _
  have hq : (0 : ℝ) < (DVR.q 𝔬 : ℝ) := by exact_mod_cast DVR.q_pos (R := 𝔬)
  set C := (localConst bK v : ℝ)
  set V := ∏ w : PlaceSet (K := K) v, (Analysis.selfDualV w.1 (Analysis.latticeV w.1 0)).toReal
  set Q := ∏ w : PlaceSet (K := K) v, (DVR.q (w.1.adicCompletionIntegers K) : ℝ) ^ ramE v w.1
  have h3 : C * V * Q⁻¹ = C * V * ((DVR.q 𝔬 : ℝ) ^ 2)⁻¹ := by
    rw [div_eq_mul_inv] at h2; linear_combination h2
  have hCV : C * V ≠ 0 := (mul_pos hc hV).ne'
  have h4 := mul_left_cancel₀ hCV h3
  exact (inv_inj.1 h4)

end Ramification

section IntBasis

variable {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] [Algebra F K] {d : 𝓞 F}
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {v : HeightOneSpectrum (𝓞 F)}

local notation "Fv" => v.adicCompletion F
local notation "E" => QE (algebraMap F (v.adicCompletion F) (d : F))

theorem PL.add' {k : ℤ} {z z' : E} (h : PL hb₁ v k z) (h' : PL hb₁ v k z') : PL hb₁ v k (z + z') := fun w => by
  rw [map_add]; exact (Valuation.map_add _ _ _).trans (max_le (h w) (h' w))

theorem PL.mul' {k k' : ℤ} {z z' : E} (h : PL hb₁ v k z) (h' : PL hb₁ v k' z') : PL hb₁ v (k + k') (z * z') :=
  fun w => by
    rw [map_mul, map_mul]
    calc _ ≤ exp (-((ramE v w.1 : ℤ) * k)) * exp (-((ramE v w.1 : ℤ) * k')) := mul_le_mul' (h w) (h' w)
      _ = _ := by rw [← exp_add]; congr 1; ring

theorem PL.neg' {k : ℤ} {z : E} (h : PL hb₁ v k z) : PL hb₁ v k (-z) := fun w => by
  rw [map_neg, Valuation.map_neg]; exact h w

include hb₀ in
theorem pl_algebraMap_iff (x : Fv) : PL hb₁ v 0 (algebraMap Fv E x) ↔ Valued.v x ≤ 1 := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := exists_place_over hb₀ hb₁ v (K := K)
    have := h ⟨w, hw⟩
    rw [qlh_algebraMap, mul_zero] at this
    have h2 := valued_le_of_localRingHom v w hw (k := 0) (by rwa [mul_zero])
    simpa using h2
  · intro h
    exact pl_of_cl hb₀ hb₁ (CL.algebraMap (by simpa using h))

include hb₀ in
/-- **The integers of $E$** (elements integral at every $w\mid v$) **have an $\mathcal O_v$-basis** $(1, x_0 + \pi^{-k}\delta)$. -/
theorem exists_basis_pl : ∃ (x₀ : Fv) (k : ℕ), ∀ z : E, PL hb₁ v 0 z ↔
    ∃ t0 t1 : Fv, Valued.v t0 ≤ 1 ∧ Valued.v t1 ≤ 1 ∧
      z = ⟨t0 + t1 * x₀, t1 * algebraMap F Fv (unifF v : F) ^ (-(k : ℤ))⟩ := by
  classical
  obtain ⟨c₀, hc₀⟩ := exists_pl_cl hb₀ hb₁ (v := v) (K := K)
  set π := algebraMap F Fv (unifF v : F)
  have hπ : Valued.v π = exp (-1) := valued_unifF v
  have hπ0 : π ≠ 0 := by intro h; rw [h, map_zero] at hπ; exact exp_ne_zero hπ.symm
  have hδ : PL hb₁ v 0 (⟨0, 1⟩ : E) := pl_of_cl hb₀ hb₁ ⟨by simp, by simp⟩
  have hsmul : ∀ {c : Fv} {z : E}, Valued.v c ≤ 1 → PL hb₁ v 0 z → PL hb₁ v 0 (algebraMap Fv E c * z) :=
    fun hc hz => by have := ((pl_algebraMap_iff hb₀ hb₁ _).2 hc).mul' hb₁ hz; rwa [zero_add] at this
  set P : Finset ℕ := (Finset.range (c₀ + 1)).filter (fun j : ℕ => ∃ x : Fv, PL hb₁ v 0 (⟨x, π ^ (-(j : ℤ))⟩ : E))
  have hP0 : 0 ∈ P := Finset.mem_filter.2 ⟨by simp, 0, by simpa using hδ⟩
  set kk : ℕ := P.max' ⟨0, hP0⟩
  obtain ⟨x₀, hx₀'⟩ := (Finset.mem_filter.1 (P.max'_mem ⟨0, hP0⟩)).2
  have hx₀ : PL hb₁ v 0 (⟨x₀, π ^ (-(kk : ℤ))⟩ : E) := hx₀'
  refine ⟨x₀, kk, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · -- the second coordinate has valuation `≤ q^k`
    have hbd : Valued.v z.im ≤ exp (c₀ : ℤ) := by have := (hc₀ 0 z hz).2; simpa using this
    have him : Valued.v (z.im * π ^ (kk : ℤ)) ≤ 1 := by
      by_cases h0 : z.im = 0
      · rw [h0, zero_mul, map_zero]; exact zero_le
      obtain ⟨j, hj⟩ := QuadFormsKB.Lattices.exists_valued_eq_exp v h0
      rw [hj, exp_le_exp] at hbd
      rw [map_mul, map_zpow₀, hj, hπ, ← WithZero.exp_zsmul, ← exp_add, ← exp_zero, exp_le_exp]
      by_contra hjk
      push Not at hjk
      have hj0 : 0 ≤ j := by simp at hjk; omega
      set u := z.im * π ^ j
      have hu : Valued.v u = 1 := by
        rw [map_mul, map_zpow₀, hj, hπ, ← WithZero.exp_zsmul, ← exp_add]; simp
      have hu0 : u ≠ 0 := by intro h; rw [h, map_zero] at hu; exact zero_ne_one hu
      have hz' := hsmul (c := u⁻¹) (by rw [map_inv₀, hu, inv_one]) hz
      have hmem : j.toNat ∈ P := by
        refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), u⁻¹ * z.re, ?_⟩
        convert hz' using 1
        refine QuadraticAlgebra.ext ?_ ?_
        · simp
        · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im,
            zero_mul, add_zero, mul_zero]
          rw [Int.toNat_of_nonneg hj0, show u = z.im * π ^ j from rfl, mul_inv, _root_.zpow_neg]
          field_simp
      have := P.le_max' _ hmem
      simp at hjk; omega
    set t1 := z.im * π ^ (kk : ℤ)
    have hz2 := hz.add' hb₁ (hsmul (c := -t1) (by rw [Valuation.map_neg]; exact him) hx₀)
    have hre : PL hb₁ v 0 (algebraMap Fv E (z.re - t1 * x₀)) := by
      convert hz2 using 1
      refine QuadraticAlgebra.ext ?_ ?_
      · simp only [QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, QuadraticAlgebra.re_add,
          QuadraticAlgebra.re_mul, QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, mul_zero, zero_mul, add_zero]
        ring
      · simp only [QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, QuadraticAlgebra.re_add,
          QuadraticAlgebra.re_mul, QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, mul_zero, zero_mul, add_zero]
        simp only [t1, _root_.zpow_neg, zpow_natCast]; field_simp; ring
    refine ⟨z.re - t1 * x₀, t1, (pl_algebraMap_iff hb₀ hb₁ _).1 hre, him, ?_⟩
    refine QuadraticAlgebra.ext ?_ ?_
    · show z.re = z.re - t1 * x₀ + t1 * x₀; ring
    · show z.im = t1 * π ^ (-(kk : ℤ))
      simp only [t1, _root_.zpow_neg, zpow_natCast]; field_simp
  · rintro ⟨t0, t1, h0, h1, rfl⟩
    have := ((pl_algebraMap_iff hb₀ hb₁ t0).2 h0).add' hb₁ (hsmul h1 hx₀)
    convert this using 1
    refine QuadraticAlgebra.ext ?_ ?_
    · simp only [QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, QuadraticAlgebra.re_add,
        QuadraticAlgebra.re_mul, QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, mul_zero, zero_mul, add_zero]
    · simp only [QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, QuadraticAlgebra.re_add,
        QuadraticAlgebra.re_mul, QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, mul_zero, zero_mul, add_zero,
        zero_add]

end IntBasis

section LocalConst

variable {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] [Algebra F K] {d : 𝓞 F}
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "E" => QE (algebraMap F (v.adicCompletion F) (d : F))

/-- Standard duality on $F_v^2$: $u\in(\mathfrak p_v^{-d_v})^2$ iff $\psi_v(\sum_lu_lt_l) = 1$ for all $t\in\mathcal O_v^2$. -/
theorem mem_dualLat_iff_std (u : Fin 2 → Fv) :
    u ∈ dualLat (ι := Fin 2) v ↔ ∀ t ∈ intLat (ι := Fin 2) v, Analysis.psiV v (∑ l, u l * t l) = 1 := by
  classical
  constructor
  · intro h t ht
    rw [psiV_prod_eq]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [mul_comm]
    exact (Analysis.mem_invDiffV_iff v _).mpr (h j) _ (ht j)
  · intro h j
    rw [← Analysis.mem_invDiffV_iff]
    intro x hx
    have hy : (Pi.single j x : Fin 2 → Fv) ∈ intLat (ι := Fin 2) v := by
      intro i
      by_cases hi : i = j
      · subst hi; simpa using hx
      · simp [Pi.single_eq_of_ne hi]
    have := h _ hy
    rw [psiV_prod_eq, Finset.prod_eq_single j] at this
    · rw [mul_comm]; simpa using this
    · intro i _ hi; simp [Pi.single_eq_of_ne hi]
    · simp

include hb₀ in
theorem mem_intPlace_iff_pl (c : Fin 2 → Fv) :
    localPiCLE bK v c ∈ intPlace (K := K) v ↔ PL hb₁ v 0 (⟨c 0, c 1⟩ : E) := by
  refine forall_congr' fun w => ?_
  rw [localPiCLE_apply, mul_zero, neg_zero, exp_zero, qlh_apply, quadLocalHom_eq_localPi hb₀ hb₁]
  have : (![(⟨c 0, c 1⟩ : E).re, (⟨c 0, c 1⟩ : E).im] : Fin 2 → Fv) = c := by
    funext i; fin_cases i <;> rfl
  rw [this]

/-- The matrix $A = \begin{pmatrix}1 & x_0\\ 0 & \pi^{-k}\end{pmatrix}$ of the integral basis. -/
def matA (x₀ : Fv) (k : ℕ) : Matrix (Fin 2) (Fin 2) Fv := !![1, x₀; 0, algebraMap F Fv (unifF v : F) ^ (-(k : ℤ))]

theorem det_matA (x₀ : Fv) (k : ℕ) : (matA v x₀ k).det = algebraMap F Fv (unifF v : F) ^ (-(k : ℤ)) := by
  simp [matA, Matrix.det_fin_two]

theorem det_matA_ne_zero (x₀ : Fv) (k : ℕ) : (matA v x₀ k).det ≠ 0 := by
  rw [det_matA]
  refine zpow_ne_zero _ ?_
  intro h; have := valued_unifF v; rw [h, map_zero] at this; exact exp_ne_zero this.symm

theorem matA_mulVec (x₀ : Fv) (k : ℕ) (t : Fin 2 → Fv) :
    matA v x₀ k *ᵥ t = ![t 0 + t 1 * x₀, t 1 * algebraMap F Fv (unifF v : F) ^ (-(k : ℤ))] := by
  funext i; fin_cases i <;> simp [matA, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

include hb₀ in
/-- **$\Phi^{-1}(\prod_w\mathcal O_w) = A\,\mathcal O_v^2$.** -/
theorem preimage_intPlace_eq {x₀ : Fv} {k : ℕ}
    (hb : ∀ z : E, PL hb₁ v 0 z ↔ ∃ t0 t1 : Fv, Valued.v t0 ≤ 1 ∧ Valued.v t1 ≤ 1 ∧
      z = ⟨t0 + t1 * x₀, t1 * algebraMap F Fv (unifF v : F) ^ (-(k : ℤ))⟩) :
    localPiCLE bK v ⁻¹' intPlace (K := K) v =
      ((GeneralLinearGroup.mkOfDetNeZero (matA v x₀ k) (det_matA_ne_zero v x₀ k))⁻¹ :
        GL (Fin 2) Fv).val.mulVec ⁻¹' intLat (ι := Fin 2) v := by
  set Ag := GeneralLinearGroup.mkOfDetNeZero (matA v x₀ k) (det_matA_ne_zero v x₀ k)
  have hA : (Ag : Matrix (Fin 2) (Fin 2) Fv) = matA v x₀ k := rfl
  have h1 : (Ag : Matrix (Fin 2) (Fin 2) Fv) * ((Ag⁻¹ : GL (Fin 2) Fv) : Matrix (Fin 2) (Fin 2) Fv) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : ((Ag⁻¹ : GL (Fin 2) Fv) : Matrix (Fin 2) (Fin 2) Fv) * (Ag : Matrix (Fin 2) (Fin 2) Fv) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  ext c
  rw [Set.mem_preimage, mem_intPlace_iff_pl hb₀ hb₁, hb, Set.mem_preimage]
  constructor
  · rintro ⟨t0, t1, h0, h1', he⟩
    have hc : c = matA v x₀ k *ᵥ ![t0, t1] := by
      rw [matA_mulVec]; funext i; fin_cases i
      · exact congrArg QuadraticAlgebra.re he
      · exact congrArg QuadraticAlgebra.im he
    rw [hc, ← hA, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
    intro i; fin_cases i
    · exact h0
    · exact h1'
  · intro ht
    set t := ((Ag⁻¹ : GL (Fin 2) Fv) : Matrix (Fin 2) (Fin 2) Fv) *ᵥ c
    have hc : c = matA v x₀ k *ᵥ t := by
      rw [← hA, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    refine ⟨t 0, t 1, ht 0, ht 1, ?_⟩
    have := congrArg (fun f => (f 0, f 1)) hc
    rw [matA_mulVec] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    exact QuadraticAlgebra.ext (Prod.mk.inj this).1 (Prod.mk.inj this).2

theorem sum_gram_matA (G A : Matrix (Fin 2) (Fin 2) Fv) (hG : ∀ i j, G i j = G j i) (c' t : Fin 2 → Fv) :
    ∑ i, ∑ j, c' i * G i j * (A *ᵥ t) j = ∑ l, ((Aᵀ * G) *ᵥ c') l * t l := by
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  rw [hG 1 0]; ring

theorem sum_trace_matA (A : Matrix (Fin 2) (Fin 2) Fv) (c' t : Fin 2 → Fv) :
    ∑ i, ∑ j, c' i * algebraMap F Fv (Algebra.traceMatrix F bK i j) * (A *ᵥ t) j =
      ∑ l, ((Aᵀ * gramV bK v) *ᵥ c') l * t l :=
  sum_gram_matA v (gramV bK v) A (fun i j => gramV_symm bK v i j) c' t

include hb₀ in
/-- **$\Phi^{-1}(\prod_w\mathfrak p_w^{-d_w}) = (A^TG)^{-1}(\mathfrak p_v^{-d_v})^2$** ($G$ the trace Gram matrix). -/
theorem preimage_dualPlace_eq {A : Matrix (Fin 2) (Fin 2) Fv}
    (hS : ∀ c, localPiCLE bK v c ∈ intPlace (K := K) v ↔ ∃ t ∈ intLat (ι := Fin 2) v, c = A *ᵥ t) :
    localPiCLE bK v ⁻¹' dualPlace (K := K) v = (Aᵀ * gramV bK v).mulVec ⁻¹' dualLat (ι := Fin 2) v := by
  classical
  ext c'
  rw [Set.mem_preimage, Set.mem_preimage, mem_dualPlace_iff, mem_dualLat_iff_std]
  constructor
  · intro h t ht
    have := h (localPiCLE bK v (A *ᵥ t)) ((hS _).2 ⟨t, ht, rfl⟩)
    rw [localPiCLE_apply, localPiCLE_apply, pairing_localPi, sum_trace_matA] at this
    exact this
  · intro h y hy
    obtain ⟨c, rfl⟩ := localPi_surjective bK v y
    obtain ⟨t, ht, rfl⟩ := (hS c).1 hy
    have := h t ht
    rw [localPiCLE_apply, pairing_localPi, sum_trace_matA]
    exact this

theorem measurableSet_intLat : MeasurableSet (intLat (ι := Fin 2) v) := by
  rw [intLat_eq_pi]; exact MeasurableSet.univ_pi fun _ => QuadFormsKB.Analysis.measurableSet_latticeV v _

theorem measurableSet_dualLat : MeasurableSet (dualLat (ι := Fin 2) v) := by
  rw [dualLat_eq_pi]; exact MeasurableSet.univ_pi fun _ => QuadFormsKB.Analysis.measurableSet_latticeV v _

theorem measurableSet_intPlace : MeasurableSet (intPlace (K := K) v) := by
  rw [intPlace_eq_pi]; exact MeasurableSet.univ_pi fun w => QuadFormsKB.Analysis.measurableSet_latticeV w.1 _

theorem measurableSet_dualPlace : MeasurableSet (dualPlace (K := K) v) := by
  rw [dualPlace_eq_pi]; exact MeasurableSet.univ_pi fun w => QuadFormsKB.Analysis.measurableSet_latticeV w.1 _

theorem det_gramV_eq : (gramV bK v).det = algebraMap F Fv (Algebra.discr F bK) := by
  rw [Algebra.discr_def, gramV, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

theorem volVN_real_preimage (M : GL (Fin 2) Fv) {S : Set (Fin 2 → Fv)} (hS : MeasurableSet S) :
    (volVN (ι := Fin 2) v).real ((M : Matrix (Fin 2) (Fin 2) Fv).mulVec ⁻¹' S) =
      ‖(GeneralLinearGroup.det M : Fv)‖⁻¹ * (volVN (ι := Fin 2) v).real S := by
  rw [Measure.real, volVN_preimage_mulVec v M hS, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (norm_nonneg _)]; rfl

include hb₀ hb₁ in
/-- **$c_v^2\,|4d|_v = 1$**: the local constant of the base change for the basis $(1,\delta)$ at **every** finite place. -/
theorem localConst_sq_mul_norm :
    (localConst bK v : ℝ) ^ 2 * ‖algebraMap F Fv (4 * (d : F))‖ = 1 := by
  obtain ⟨x₀, k, hb⟩ := exists_basis_pl hb₀ hb₁ (v := v)
  set Ag := GeneralLinearGroup.mkOfDetNeZero (matA v x₀ k) (det_matA_ne_zero v x₀ k)
  have hA : (Ag : Matrix (Fin 2) (Fin 2) Fv) = matA v x₀ k := rfl
  have h1 : (Ag : Matrix (Fin 2) (Fin 2) Fv) * ((Ag⁻¹ : GL (Fin 2) Fv) : Matrix (Fin 2) (Fin 2) Fv) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : ((Ag⁻¹ : GL (Fin 2) Fv) : Matrix (Fin 2) (Fin 2) Fv) * (Ag : Matrix (Fin 2) (Fin 2) Fv) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hSeq := preimage_intPlace_eq hb₀ hb₁ v hb
  have hS : ∀ c, localPiCLE bK v c ∈ intPlace (K := K) v ↔ ∃ t ∈ intLat (ι := Fin 2) v, c = matA v x₀ k *ᵥ t := by
    intro c
    rw [← Set.mem_preimage, hSeq, Set.mem_preimage]
    constructor
    · intro ht
      refine ⟨_, ht, ?_⟩
      show c = (Ag : Matrix (Fin 2) (Fin 2) Fv) *ᵥ (((Ag⁻¹ : GL (Fin 2) Fv) : Matrix (Fin 2) (Fin 2) Fv) *ᵥ c)
      rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    · rintro ⟨t, ht, rfl⟩
      show ((Ag⁻¹ : GL (Fin 2) Fv) : Matrix (Fin 2) (Fin 2) Fv) *ᵥ ((Ag : Matrix (Fin 2) (Fin 2) Fv) *ᵥ t) ∈ _
      rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]; exact ht
  have hS'eq := preimage_dualPlace_eq hb₀ v hS
  have hdisc := discr_basisOneDelta hb₀ hb₁
  have hd0 : (d : F) ≠ 0 := d_ne_zero_of_basis hb₁
  have h4d : (4 * (d : F)) ≠ 0 := mul_ne_zero (by norm_num) hd0
  have hdG : (gramV bK v).det ≠ 0 := by
    rw [det_gramV_eq, hdisc, map_ne_zero_iff _ (algebraMap F Fv).injective]; exact h4d
  have hdB : ((matA v x₀ k)ᵀ * gramV bK v).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_transpose]; exact mul_ne_zero (det_matA_ne_zero v x₀ k) hdG
  set Bg := GeneralLinearGroup.mkOfDetNeZero ((matA v x₀ k)ᵀ * gramV bK v) hdB
  -- volumes
  have e1 := volVN_real_preimage v (Ag⁻¹) (measurableSet_intLat v)
  have e2 := volVN_real_preimage v Bg (measurableSet_dualLat v)
  rw [← hSeq] at e1
  rw [show ((Bg : GL (Fin 2) Fv) : Matrix (Fin 2) (Fin 2) Fv) = (matA v x₀ k)ᵀ * gramV bK v from rfl, ← hS'eq] at e2
  have e3 : (volVN (ι := Fin 2) v).real (localPiCLE bK v ⁻¹' intPlace (K := K) v) =
      (localConst bK v : ℝ) * (placeMeasure (K := K) v).real (intPlace v) := by
    rw [Measure.real, volVN_preimage_localPi (bK := bK) v (measurableSet_intPlace v), ENNReal.toReal_mul]; rfl
  have e4 : (volVN (ι := Fin 2) v).real (localPiCLE bK v ⁻¹' dualPlace (K := K) v) =
      (localConst bK v : ℝ) * (placeMeasure (K := K) v).real (dualPlace v) := by
    rw [Measure.real, volVN_preimage_localPi (bK := bK) v (measurableSet_dualPlace v), ENNReal.toReal_mul]; rfl
  have hp := place_mul_place_dual (K := K) v
  have hv := vol_mul_vol_dual (ι := Fin 2) (k := F) v
  have hdetA : (GeneralLinearGroup.det (Ag⁻¹) : Fv) = (matA v x₀ k).det⁻¹ := by
    rw [map_inv, Units.val_inv_eq_inv_val, GeneralLinearGroup.val_det_apply]; rfl
  have hdetB : (GeneralLinearGroup.det Bg : Fv) = (matA v x₀ k).det * (gramV bK v).det := by
    rw [GeneralLinearGroup.val_det_apply]
    show ((matA v x₀ k)ᵀ * gramV bK v).det = _
    rw [Matrix.det_mul, Matrix.det_transpose]
  rw [hdetA] at e1
  rw [hdetB] at e2
  rw [e3] at e1
  rw [e4] at e2
  have hnA : ‖(matA v x₀ k).det‖ ≠ 0 := norm_ne_zero_iff.2 (det_matA_ne_zero v x₀ k)
  have hnG : ‖(gramV bK v).det‖ ≠ 0 := norm_ne_zero_iff.2 hdG
  have key : (localConst bK v : ℝ) ^ 2 * ((placeMeasure (K := K) v).real (intPlace v) *
      (placeMeasure (K := K) v).real (dualPlace v)) =
      ‖(gramV bK v).det‖⁻¹ * ((volVN (ι := Fin 2) v).real (intLat v) * (volVN (ι := Fin 2) v).real (dualLat v)) := by
    calc _ = ((localConst bK v : ℝ) * (placeMeasure (K := K) v).real (intPlace v)) *
          ((localConst bK v : ℝ) * (placeMeasure (K := K) v).real (dualPlace v)) := by ring
      _ = _ := by
        rw [e1, e2, norm_inv, inv_inv, norm_mul, mul_inv]
        field_simp
  rw [hp, hv, mul_one, mul_one] at key
  rw [det_gramV_eq, hdisc] at key
  rw [key]
  exact inv_mul_cancel₀ (by rw [Ne, norm_eq_zero, map_eq_zero_iff _ (algebraMap F Fv).injective]; exact h4d)

end LocalConst

end QuadFormsKB.Tamagawa.Measure.Weil
