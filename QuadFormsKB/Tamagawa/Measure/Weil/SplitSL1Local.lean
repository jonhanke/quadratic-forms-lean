import QuadFormsKB.Tamagawa.Measure.Weil.SplitSL1Arch
import QuadFormsKB.Tamagawa.Measure.Weil.QuatLocalVolume
import QuadFormsKB.Tamagawa.Measure.Weil.GLScaling

/-!
# The finite local factors of the box, for split $D$

$F$ a number field, $v$ a finite place, $F_v\supseteq\mathcal O_v$ with the self-dual measure, $q = N(v)$.

* **`pi_selfDualV_glUnits`**: $\operatorname{vol}\{X\in M_2(\mathcal O_v) : \det X\in\mathcal O_v^\times\} =
  (1 - q^{-1})(1 - q^{-2})\operatorname{vol}(\mathcal O_v)^4$ ($\#\mathrm{GL}_2(\mathbb F_q) = (q^2 - 1)(q^2 - q)$,
  Mathlib's `Matrix.card_GL_field`, and the reduction lemma `pi_selfDualV_res`).
-/

open MeasureTheory Measure Set NumberField IsDedekindDomain
open scoped ENNReal NNReal Classical

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Kv" => v.adicCompletion F
local notation "Ov" => v.adicCompletionIntegers F
local notation "kv" => IsLocalRing.ResidueField (v.adicCompletionIntegers F)

/-- The residue map is multiplicative and additive on $\mathcal O_v$. -/
theorem resV_det {c : Fin 4 → Kv} (hc : ∀ i, c i ∈ Ov) :
    resV v (c 0 * c 3 - c 1 * c 2) = resV v (c 0) * resV v (c 3) - resV v (c 1) * resV v (c 2) := by
  have hd : c 0 * c 3 - c 1 * c 2 ∈ Ov :=
    sub_mem (mul_mem (hc 0) (hc 3)) (mul_mem (hc 1) (hc 2))
  rw [resV_of_mem v hd, resV_of_mem v (hc 0), resV_of_mem v (hc 1), resV_of_mem v (hc 2), resV_of_mem v (hc 3),
    ← map_mul, ← map_mul, ← map_sub]
  rfl

/-- $\#\{r\in\mathbb F_q^4 : r_0r_3 - r_1r_2\ne0\} = \#\mathrm{GL}_2(\mathbb F_q) = (q^2 - 1)(q^2 - q)$. -/
theorem card_det_ne_zero {k : Type*} [Field k] [Fintype k] [DecidableEq k] :
    ((Finset.univ.filter fun r : Fin 4 → k => r 0 * r 3 - r 1 * r 2 ≠ 0).card : ℝ) =
      ((Fintype.card k : ℝ) ^ 2 - 1) * ((Fintype.card k : ℝ) ^ 2 - Fintype.card k) := by
  let e : {r : Fin 4 → k // r 0 * r 3 - r 1 * r 2 ≠ 0} ≃ Matrix.GeneralLinearGroup (Fin 2) k :=
    { toFun := fun r => Matrix.GeneralLinearGroup.mkOfDetNeZero !![r.1 0, r.1 1; r.1 2, r.1 3]
        (by rw [Matrix.det_fin_two_of]; exact r.2)
      invFun := fun M => ⟨![(M : Matrix (Fin 2) (Fin 2) k) 0 0, (M : Matrix (Fin 2) (Fin 2) k) 0 1,
        (M : Matrix (Fin 2) (Fin 2) k) 1 0, (M : Matrix (Fin 2) (Fin 2) k) 1 1], by
          have := M.det_ne_zero
          rw [Matrix.det_fin_two] at this
          simpa using this⟩
      left_inv := fun r => by
        apply Subtype.ext; funext i; fin_cases i <;> rfl
      right_inv := fun M => by
        apply Units.ext
        refine Matrix.ext fun i j => ?_
        fin_cases i <;> fin_cases j <;> rfl }
  have hcard := Matrix.card_GL_field (𝔽 := k) (n := 2)
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype] at hcard
  rw [hcard, Fin.prod_univ_two]
  have hk : 1 ≤ Fintype.card k := Fintype.card_pos
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  rw [Nat.cast_mul, Nat.cast_sub (Nat.one_le_pow _ _ hk), Nat.cast_sub (Nat.le_self_pow two_ne_zero _)]
  push_cast
  ring

theorem selfDualV_latticeV_one' :
    Analysis.selfDualV v (Analysis.latticeV v 1) = ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) * volO v :=
  selfDualV_latticeV_one v

/-- **$\operatorname{vol}\{X\in M_2(\mathcal O_v) : \det X\in\mathcal O_v^\times\} =
(1 - q^{-1})(1 - q^{-2})\operatorname{vol}(\mathcal O_v)^4$.** -/
theorem pi_selfDualV_glUnits :
    Measure.pi (fun _ : Fin 4 => Analysis.selfDualV v)
        {c | (∀ i, c i ∈ Ov) ∧ Valued.v (c 0 * c 3 - c 1 * c 2) = 1} =
      ENNReal.ofReal ((1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) * (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ 2)⁻¹)) *
        volO v ^ 4 := by
  let _ : Fintype kv := Fintype.ofFinite kv
  have hset : {c : Fin 4 → Kv | (∀ i, c i ∈ Ov) ∧ Valued.v (c 0 * c 3 - c 1 * c 2) = 1} =
      {c | (∀ i, c i ∈ Ov) ∧ (fun r : Fin 4 → kv => r 0 * r 3 - r 1 * r 2 ≠ 0) fun i => resV v (c i)} := by
    ext c
    simp only [Set.mem_ofPred_eq]
    refine and_congr_right fun hc => ?_
    have hd : c 0 * c 3 - c 1 * c 2 ∈ Ov :=
      sub_mem (mul_mem (hc 0) (hc 3)) (mul_mem (hc 1) (hc 2))
    rw [← resV_det v hc, resV_of_mem v hd]
    exact valued_eq_one_iff_residue_ne_zero v ⟨_, hd⟩
  rw [hset, pi_selfDualV_res v (fun r : Fin 4 → kv => r 0 * r 3 - r 1 * r 2 ≠ 0), selfDualV_latticeV_one]
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ)
  have hq : (Fintype.card kv : ℝ) = q := card_residueField_eq v
  have hq0 : q ≠ 0 := by have := one_lt_absNorm v; positivity
  have hcard := card_det_ne_zero (k := kv)
  rw [hq] at hcard
  rw [mul_pow, ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  have key : ∀ N : ℝ, N = (q ^ 2 - 1) * (q ^ 2 - q) → N * q⁻¹ ^ 4 = (1 - q⁻¹) * (1 - (q ^ 2)⁻¹) := by
    intro N hN; rw [hN]; field_simp
  exact key _ (by convert hcard using 3; ext r; simp)

/-! ### $\Phi_v$ and $U_v = \Phi_v^{-1}\mathrm{GL}_2(\mathcal O_v)$ -/

section LocalPhi

variable {a b x y : F} (h : x ^ 2 - a * y ^ 2 = b)

include h in
theorem split_v : (algebraMap F Kv x) ^ 2 - (algebraMap F Kv a) * (algebraMap F Kv y) ^ 2 = algebraMap F Kv b := by
  simp only [← map_pow, ← map_mul, ← map_sub, h]

/-- $\Phi_v : \mathbb H[F_v,a,b]\to M_2(F_v)$. -/
def phiV : QuatV a b v →ₐ[Kv] Matrix (Fin 2) (Fin 2) Kv :=
  quatMatHom (algebraMap F Kv a) (algebraMap F Kv b) (algebraMap F Kv x) (algebraMap F Kv y) (split_v v h)

variable (a x y) in
/-- The matrix of $\Phi_v$ in coordinates. -/
def JV : Matrix (Fin 4) (Fin 4) Kv :=
  !![1, 0, algebraMap F Kv x, algebraMap F Kv a * algebraMap F Kv y;
    0, algebraMap F Kv a, -(algebraMap F Kv a * algebraMap F Kv y), -(algebraMap F Kv a * algebraMap F Kv x);
    0, 1, algebraMap F Kv y, algebraMap F Kv x;
    1, 0, -(algebraMap F Kv x), -(algebraMap F Kv a * algebraMap F Kv y)]

theorem phiV_symm_coord (c : Fin 4 → Kv) :
    phiV v h ((quatLocCLE _ _).symm c) = vecToMat ((JV v a x y).mulVec c) := by
  have hq : (quatLocCLE (algebraMap F Kv a) (algebraMap F Kv b)).symm c = ⟨c 0, c 1, c 2, c 3⟩ := rfl
  rw [phiV, hq, quatMatHom_apply]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [vecToMat, JV, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

include h in
theorem det_JV : (JV v a x y).det = 4 * algebraMap F Kv a * algebraMap F Kv b := by
  rw [← split_v v h, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, JV, Fin.succAbove, Matrix.submatrix]
  ring

theorem det_phiV (q : QuatV a b v) : (phiV v h q).det = nrdLoc _ _ q := det_quatMatHom _ _ _ _ _ q

/-- $X\in M_2(\mathcal O_v)$. -/
def IntMV (X : Matrix (Fin 2) (Fin 2) Kv) : Prop := ∀ i j, X i j ∈ Ov

/-- **$U_v = \Phi_v^{-1}\mathrm{GL}_2(\mathcal O_v)$**. -/
def UV : Set (QuatV a b v)ˣ :=
  {u | IntMV v (phiV v h (u : QuatV a b v)) ∧ IntMV v (phiV v h ((u⁻¹ : (QuatV a b v)ˣ) : QuatV a b v))}

theorem intMV_det {X : Matrix (Fin 2) (Fin 2) Kv} (hX : IntMV v X) : X.det ∈ Ov := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hX 0 0) (hX 1 1)) (mul_mem (hX 0 1) (hX 1 0))

/-- $u\in U_v$ iff $\Phi_v(u)\in M_2(\mathcal O_v)$ and $|\det\Phi_v(u)|_v = 1$. -/
theorem mem_UV_iff (u : (QuatV a b v)ˣ) :
    u ∈ UV v h ↔ IntMV v (phiV v h (u : QuatV a b v)) ∧ Valued.v (phiV v h (u : QuatV a b v)).det = 1 := by
  set X := phiV v h (u : QuatV a b v)
  set Y := phiV v h ((u⁻¹ : (QuatV a b v)ˣ) : QuatV a b v)
  have hXY : X * Y = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hdet : X.det * Y.det = 1 := by rw [← Matrix.det_mul, hXY, Matrix.det_one]
  constructor
  · rintro ⟨hX, hY⟩
    refine ⟨hX, ?_⟩
    have h1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (intMV_det v hX)
    have h2 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (intMV_det v hY)
    have h3 : Valued.v X.det * Valued.v Y.det = 1 := by rw [← map_mul, hdet, map_one]
    by_contra hne
    have hlt : Valued.v X.det < 1 := lt_of_le_of_ne h1 hne
    have : Valued.v X.det * Valued.v Y.det < 1 :=
      lt_of_lt_of_le (mul_lt_one_of_lt_of_le hlt h2) le_rfl
    rw [h3] at this
    exact lt_irrefl _ this
  · rintro ⟨hX, hv⟩
    refine ⟨hX, ?_⟩
    have hd0 : X.det ≠ 0 := fun h0 => by rw [h0, map_zero] at hv; exact zero_ne_one hv
    have hYeq : Y = X⁻¹ := (Matrix.inv_eq_right_inv hXY).symm
    have hdi : X.det⁻¹ ∈ Ov := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]
    intro i j
    show Y i j ∈ Ov
    rw [hYeq, Matrix.inv_def, Matrix.adjugate_fin_two]
    have hR : Ring.inverse X.det = X.det⁻¹ := congrFun Ring.inverse_eq_inv' X.det
    rw [hR]
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Fin.zero_eta, Fin.isValue,
        Fin.mk_one]
    · exact mul_mem hdi (hX 1 1)
    · exact mul_mem hdi (neg_mem (hX 0 1))
    · exact mul_mem hdi (neg_mem (hX 1 0))
    · exact mul_mem hdi (hX 0 0)

theorem continuous_phiV : Continuous (phiV v h : QuatV a b v → Matrix (Fin 2) (Fin 2) Kv) := by
  have he : (phiV v h : QuatV a b v → Matrix (Fin 2) (Fin 2) Kv) =
      (fun c => vecToMat ((JV v a x y).mulVec c)) ∘ (quatLocCLE (algebraMap F Kv a) (algebraMap F Kv b)) := by
    funext q
    simp only [Function.comp_apply]
    rw [← phiV_symm_coord, ContinuousLinearEquiv.symm_apply_apply]
  rw [he]
  refine Continuous.comp ?_ (quatLocCLE _ _).continuous
  have hm : Continuous fun c : Fin 4 → Kv => (JV v a x y).mulVec c := continuous_const.matrix_mulVec continuous_id
  have hv : Continuous (vecToMat (R := Kv)) :=
    continuous_pi fun i => continuous_pi fun j => by fin_cases i <;> fin_cases j <;> exact continuous_apply _
  exact hv.comp hm

set_option maxHeartbeats 1000000 in
/-- **The local quaternion factor of the box**: $\omega_v(U_v) = |4ab|_v^{-1}(1 - q^{-1})(1 - q^{-2})
\operatorname{vol}(\mathcal O_v)^4$. -/
theorem omegaQuatV_UV (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    omegaQuatV v a b (UV v h) = (modK v (4 * algebraMap F Kv a * algebraMap F Kv b))⁻¹ *
      (ENNReal.ofReal ((1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) * (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ 2)⁻¹)) *
        volO v ^ 4) := by
  set S : Set (Fin 4 → Kv) := {c | (∀ i, c i ∈ Ov) ∧ Valued.v (c 0 * c 3 - c 1 * c 2) = 1} with hS
  set T : Set (Fin 4 → Kv) := (JV v a x y).mulVec ⁻¹' S with hT
  have hOm : MeasurableSet {c : Fin 4 → Kv | ∀ i, c i ∈ Ov} := by
    have : {c : Fin 4 → Kv | ∀ i, c i ∈ Ov} = Set.pi univ fun _ => (Ov : Set Kv) := by ext c; simp
    rw [this]
    exact MeasurableSet.univ_pi fun _ => (isOpen_adicCompletionIntegers v).measurableSet
  have hSm : MeasurableSet S := by
    refine hOm.inter ((measurableSet_unitsV v).preimage ?_)
    exact (Continuous.measurable (by fun_prop))
  have hmv : Measurable (JV v a x y).mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  have hTm : MeasurableSet T := hmv hSm
  -- `Δ = 1` on `U_v`
  have h1 : ∀ u ∈ UV v h, distribHaarChar (QuatV a b v) u = 1 := by
    intro u hu
    have hv := ((mem_UV_iff v h u).1 hu).2
    rw [det_phiV] at hv
    have hu' : nrdLocUnit _ _ u ∈ unitsVSub v := hv
    rw [distribHaarChar_quatLoc, distribHaarChar_eq_one_of_mem_unitsVSub hu', one_pow]
  have hUm : MeasurableSet (UV v h) := by
    have hc : Continuous fun u : (QuatV a b v)ˣ => phiV v h (u : QuatV a b v) :=
      (continuous_phiV v h).comp Units.continuous_val
    have hci : Continuous fun u : (QuatV a b v)ˣ => phiV v h ((u⁻¹ : (QuatV a b v)ˣ) : QuatV a b v) :=
      (continuous_phiV v h).comp Units.continuous_coe_inv
    have hint : ∀ {f : (QuatV a b v)ˣ → Matrix (Fin 2) (Fin 2) Kv}, Continuous f →
        MeasurableSet {u | IntMV v (f u)} := by
      intro f hf
      have : {u | IntMV v (f u)} = ⋂ i, ⋂ j, (fun u => f u i j) ⁻¹' (Ov : Set Kv) := by
        ext u; simp [IntMV, Set.mem_iInter]
      rw [this]
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
        ((continuous_apply j).comp ((continuous_apply i).comp hf)).measurable
          (isOpen_adicCompletionIntegers v).measurableSet
    exact (hint hc).inter (hint hci)
  rw [omegaQuatV, omegaQuatLoc, unitsHaar_apply_of_forall_eq_one (isOpenEmbedding_val_quatLoc _ _)
    (continuous_distribHaarChar_quatLoc _ _ (continuous_distribHaarChar_adic v)) _ hUm h1]
  -- the image in coordinates
  have himg : Units.val '' UV v h = quatLocCoord _ _ ⁻¹' T := by
    ext q
    simp only [Set.mem_image, Set.mem_preimage, hT, hS, Set.mem_ofPred_eq]
    have hcoord : (JV v a x y).mulVec (quatLocCoord _ _ q) = ![(phiV v h q) 0 0, (phiV v h q) 0 1,
        (phiV v h q) 1 0, (phiV v h q) 1 1] := by
      have := phiV_symm_coord v h (quatLocCoord _ _ q)
      have hq : (quatLocCLE (algebraMap F Kv a) (algebraMap F Kv b)).symm (quatLocCoord _ _ q) = q :=
        (quatLocCoord _ _).symm_apply_apply q
      rw [hq] at this
      rw [this]
      funext i; fin_cases i <;> rfl
    rw [hcoord]
    have hdetq : (phiV v h q).det = (phiV v h q) 0 0 * (phiV v h q) 1 1 - (phiV v h q) 0 1 * (phiV v h q) 1 0 :=
      Matrix.det_fin_two _
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨hX, hv⟩ := (mem_UV_iff v h u).1 hu
      refine ⟨fun i => ?_, ?_⟩
      · fin_cases i
        exacts [hX 0 0, hX 0 1, hX 1 0, hX 1 1]
      · simpa [hdetq] using hv
    · rintro ⟨hX, hv⟩
      have hX' : IntMV v (phiV v h q) := by
        intro i j; fin_cases i <;> fin_cases j
        exacts [hX 0, hX 1, hX 2, hX 3]
      have hv' : Valued.v (phiV v h q).det = 1 := by simpa [hdetq] using hv
      have hn0 : nrdLoc _ _ q ≠ 0 := by
        rw [← det_phiV v h]; intro h0; rw [h0, map_zero] at hv'; exact zero_ne_one hv'
      obtain ⟨u, rfl⟩ := (isUnit_iff_nrdLoc_ne_zero _ _ q).mpr hn0
      exact ⟨u, (mem_UV_iff v h u).2 ⟨hX', hv'⟩, rfl⟩
  rw [himg, quatLocVol, Measure.map_apply (quatLocCLE _ _).symm.continuous.measurable
    (hTm.preimage (continuous_quatLocCoord _ _).measurable)]
  have hpre : ((quatLocCLE (algebraMap F Kv a) (algebraMap F Kv b)).symm ⁻¹' (quatLocCoord _ _ ⁻¹' T)) = T := by
    ext c
    simp only [Set.mem_preimage]
    change (quatLocCoord _ _) ((quatLocCoord _ _).symm c) ∈ T ↔ c ∈ T
    rw [LinearEquiv.apply_symm_apply]
  rw [hpre]
  -- the linear change of variables
  have hJ : IsUnit (JV v a x y).det := by
    rw [det_JV v h]
    have h4 : (4 : Kv) ≠ 0 := by
      rw [show (4 : Kv) = algebraMap F Kv 4 from (map_ofNat _ 4).symm]
      exact (map_ne_zero _).2 (by norm_num)
    exact isUnit_iff_ne_zero.2 (mul_ne_zero (mul_ne_zero h4 ((map_ne_zero _).2 ha0)) ((map_ne_zero _).2 hb0))
  set M : Matrix.GeneralLinearGroup (Fin 4) Kv := Matrix.GeneralLinearGroup.mkOfDetNeZero (JV v a x y)
    (isUnit_iff_ne_zero.1 hJ)
  have : (Measure.pi fun _ : Fin 4 => Analysis.selfDualV v).Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hmap := map_mulVec_eq_glHaarChar_inv (Measure.pi fun _ : Fin 4 => Analysis.selfDualV v) M
  have hT' : (Measure.pi fun _ : Fin 4 => Analysis.selfDualV v) T =
      ((Measure.pi fun _ : Fin 4 => Analysis.selfDualV v).map (JV v a x y).mulVec) S :=
    (Measure.map_apply hmv hSm).symm
  rw [hT']
  change ((Measure.pi fun _ : Fin 4 => Analysis.selfDualV v).map (M : Matrix (Fin 4) (Fin 4) Kv).mulVec) S = _
  rw [hmap, Measure.smul_apply, glHaarChar_eq_of_field, ENNReal.smul_def, smul_eq_mul, pi_selfDualV_glUnits]
  congr 1
  have hdetM : (Matrix.GeneralLinearGroup.det M : Kv) = 4 * algebraMap F Kv a * algebraMap F Kv b := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]; exact det_JV v h
  have hne : (4 * algebraMap F Kv a * algebraMap F Kv b) ≠ 0 := isUnit_iff_ne_zero.1 (by rw [← det_JV v h]; exact hJ)
  have hu : Matrix.GeneralLinearGroup.det M = unitsHomeomorphNeZero.symm ⟨_, hne⟩ :=
    Units.ext (by rw [coe_unitsHomeomorphNeZero_symm v]; exact hdetM)
  rw [modK_of_ne_zero v hne, hu, ENNReal.coe_inv distribHaarChar_pos.ne']

/-- At a good place ($2, a, b$ units, $x, y$ integral), $\Phi_v(q)\in M_2(\mathcal O_v)$ iff $q\in\Lambda_v$. -/
theorem mem_lamLoc_iff_intMV (h2 : Valued.v (2 : Kv) = 1) (hav : Valued.v (algebraMap F Kv a) = 1)
    (hbv : Valued.v (algebraMap F Kv b) = 1) (hx : algebraMap F Kv x ∈ Ov) (hy : algebraMap F Kv y ∈ Ov)
    (q : QuatV a b v) : q ∈ lamLoc a b v ↔ IntMV v (phiV v h q) := by
  have haO : algebraMap F Kv a ∈ Ov := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hav.le
  constructor
  · rintro ⟨h0, h1, h2', h3⟩
    intro i j
    rw [phiV, quatMatHom_apply]
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    · exact add_mem (add_mem h0 (mul_mem h2' hx)) (mul_mem h3 (mul_mem haO hy))
    · exact sub_mem (sub_mem (mul_mem h1 haO) (mul_mem h2' (mul_mem haO hy))) (mul_mem h3 (mul_mem haO hx))
    · exact add_mem (add_mem h1 (mul_mem h2' hy)) (mul_mem h3 hx)
    · exact sub_mem (sub_mem h0 (mul_mem h2' hx)) (mul_mem h3 (mul_mem haO hy))
  · intro hX
    have hne : ∀ c : Kv, Valued.v c = 1 → c ≠ 0 := fun c hc h0 => by rw [h0, map_zero] at hc; exact zero_ne_one hc
    let _ : Invertible (2 : Kv) := invertibleOfNonzero (hne _ h2)
    let _ : Invertible (algebraMap F Kv a) := invertibleOfNonzero (hne _ hav)
    let _ : Invertible (algebraMap F Kv b) := invertibleOfNonzero (hne _ hbv)
    have hinvO : ∀ c : Kv, Valued.v c = 1 → c⁻¹ ∈ Ov := fun c hc => by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hc, inv_one]
    have i2 : (⅟2 : Kv) ∈ Ov := by rw [invOf_eq_inv]; exact hinvO _ h2
    have ia : (⅟(algebraMap F Kv a) : Kv) ∈ Ov := by rw [invOf_eq_inv]; exact hinvO _ hav
    have ib : (⅟(algebraMap F Kv b) : Kv) ∈ Ov := by rw [invOf_eq_inv]; exact hinvO _ hbv
    have hq := quatMatInv_quatMatHom (algebraMap F Kv a) (algebraMap F Kv b) (algebraMap F Kv x)
      (algebraMap F Kv y) (split_v v h) q
    rw [← hq]
    set m := quatMatHom (algebraMap F Kv a) (algebraMap F Kv b) (algebraMap F Kv x) (algebraMap F Kv y)
      (split_v v h) q
    have hm : ∀ i j, m i j ∈ Ov := hX
    have hP : ⅟2 * (m 0 0 - m 1 1) ∈ Ov := mul_mem i2 (sub_mem (hm 0 0) (hm 1 1))
    have hQ : ⅟2 * (m 1 0 - ⅟(algebraMap F Kv a) * m 0 1) ∈ Ov :=
      mul_mem i2 (sub_mem (hm 1 0) (mul_mem ia (hm 0 1)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact mul_mem i2 (add_mem (hm 0 0) (hm 1 1))
    · exact mul_mem i2 (add_mem (hm 1 0) (mul_mem ia (hm 0 1)))
    · exact mul_mem ib (sub_mem (mul_mem hx hP) (mul_mem (mul_mem haO hy) hQ))
    · exact mul_mem ib (sub_mem (mul_mem hx hQ) (mul_mem hy hP))

/-- **At a good place, $U_v = \Lambda_v^\times$.** -/
theorem UV_eq_lamLocUnits (h2 : Valued.v (2 : Kv) = 1) (hav : Valued.v (algebraMap F Kv a) = 1)
    (hbv : Valued.v (algebraMap F Kv b) = 1) (hx : algebraMap F Kv x ∈ Ov) (hy : algebraMap F Kv y ∈ Ov) :
    UV v h = lamLocUnits a b v := by
  ext u
  simp only [UV, lamLocUnits, Set.mem_ofPred_eq, mem_lamLoc_iff_intMV v h h2 hav hbv hx hy]

end LocalPhi

end QuadFormsKB.Tamagawa.Measure.Weil
