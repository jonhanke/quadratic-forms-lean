import QuadFormsKB.Tamagawa.Measure.Weil.QuatLocalVolume
import QuadFormsKB.Analysis.NFEulerProduct
import QuadFormsKB.Literature.LocalGlobal.NumberFieldLocal

/-!
# The canonical Tamagawa measure on $(\mathbb H\otimes\mathbb A_f)^\times$

$\mathbb H = \mathbb H[F,a,b]$ with $a, b\in F^\times$ integral at every finite place (so the standard order
$\Lambda = \mathcal O_F\langle1,i,j,k\rangle$ is an order, maximal at every $v\nmid 2ab$), $\lambda_v = 1 - N(v)^{-1}$
(Weil's convergence factors, the same as for $\mathbb G_m$: `lamV`), $\omega_v = \|\operatorname{nrd}x\|_v^{-2}dx_v$
(`omegaQuatV`, $dx_v$ the self-dual coordinate measure).

* `quatLocalFactor a b v` $=\lambda_v^{-1}\omega_v(\Lambda_v^\times)\in(0,\infty)$; at almost every $v$ it is
  $1 - N(v)^{-2}$ (`quatLocalFactor_good`, from `lamV_inv_mul_omegaQuatV_good`), so the Euler product
  $\prod_v\lambda_v^{-1}\omega_v(\Lambda_v^\times)$ converges absolutely (**`multipliable_quatLocalFactor`**) to a positive
  number `quatHatVol a b` (**`quatHatVol_pos`**).
* **`muFinQuat a b`**: the Haar measure on $(\mathbb H\otimes\mathbb A_f)^\times$ with
  $\mu(\hat\Lambda^\times) = \prod_v\lambda_v^{-1}\omega_v(\Lambda_v^\times)$ (**`muFinQuat_lamHatUnits`**): Weil's
  $\prod_v\lambda_v^{-1}\omega_v$.
* **Chart lemma** (**`muFinQuat_quatBox`**, **`muFinQuat_quatBox_weil`**): for $U_v\subseteq(\mathbb H\otimes F_v)^\times$
  ($v\in S$) measurable with $\omega_v(U_v) < \infty$,
  $\mu(\prod_{v\in S}U_v\times\prod_{v\notin S}\Lambda_v^\times) = \prod_v\lambda_v^{-1}\omega_v(U_v')$ with $U_v' = U_v$
  ($v\in S$), $\Lambda_v^\times$ ($v\notin S$): the measure is $\prod_v\lambda_v^{-1}\omega_v$ on the charts.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Quaternion Pointwise Classical

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

set_option synthInstance.maxHeartbeats 400000

variable (a b : F)

/-! ### The local factors $\lambda_v^{-1}\omega_v(\Lambda_v^\times)$ -/

theorem omegaQuatV_lamLocUnits_ne_top (v : HeightOneSpectrum (𝓞 F)) : omegaQuatV v a b (lamLocUnits a b v) ≠ ⊤ :=
  (isCompact_lamLocUnits a b v).measure_lt_top.ne

theorem omegaQuatV_lamLocUnits_ne_zero (v : HeightOneSpectrum (𝓞 F)) : omegaQuatV v a b (lamLocUnits a b v) ≠ 0 :=
  (isOpen_lamLocUnits a b v).measure_ne_zero _ ⟨1, one_mem_lamLocUnits a b v⟩

/-- $\lambda_v^{-1}\omega_v(\Lambda_v^\times)$, a positive real number. -/
def quatLocalFactor (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (ENNReal.ofReal (lamV v)⁻¹ * omegaQuatV v a b (lamLocUnits a b v)).toReal

theorem ofReal_quatLocalFactor (v : HeightOneSpectrum (𝓞 F)) :
    ENNReal.ofReal (quatLocalFactor a b v) = ENNReal.ofReal (lamV v)⁻¹ * omegaQuatV v a b (lamLocUnits a b v) :=
  ENNReal.ofReal_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (omegaQuatV_lamLocUnits_ne_top a b v))

theorem quatLocalFactor_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < quatLocalFactor a b v :=
  ENNReal.toReal_pos (mul_ne_zero (by simpa using lamV_pos v) (omegaQuatV_lamLocUnits_ne_zero a b v))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (omegaQuatV_lamLocUnits_ne_top a b v))

variable {a b}

/-- At almost every finite place: $v\nmid2$, $a, b\in\mathcal O_v^\times$ and $\operatorname{vol}(\mathcal O_v) = 1$. -/
theorem eventually_good_place (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Valued.v (2 : v.adicCompletion F) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) a) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) b) = 1 ∧
      (Analysis.selfDualV v).real (Analysis.latticeV v 0) = 1 := by
  have hbad := NFLocal.finite_bad_places_nf 2 ![a, b] (fun i => by fin_cases i <;> simp [ha0, hb0])
  have hvol := mulSupport_volO_real_finite (F := F)
  refine Filter.mem_of_superset (hbad.union hvol).compl_mem_cofinite fun v hv => ?_
  simp only [mem_compl_iff, mem_union, mem_ofPred_eq, not_or, not_exists, Function.mem_mulSupport,
    not_not] at hv
  obtain ⟨⟨h2, hab⟩, hvol⟩ := hv
  have hval : ∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  refine ⟨?_, ?_, ?_, hvol⟩
  · have : (2 : v.adicCompletion F) = algebraMap F (v.adicCompletion F) 2 := (map_ofNat _ 2).symm
    rw [this, hval, show (2 : F) = algebraMap (𝓞 F) F 2 from (map_ofNat _ 2).symm,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact le_antisymm (v.intValuation_le_one 2) (not_lt.mp fun h => h2 ((v.intValuation_lt_one_iff_mem 2).mp h))
  · rw [hval]; exact hab 0
  · rw [hval]; exact hab 1

variable (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
  (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)

include ha hb in
/-- **At almost every place, $\lambda_v^{-1}\omega_v(\Lambda_v^\times) = 1 - N(v)^{-2}$.** -/
theorem quatLocalFactor_good (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      quatLocalFactor a b v = 1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ 2)⁻¹ := by
  refine (eventually_good_place ha0 hb0).mono fun v ⟨h2, hav, hbv, hvol⟩ => ?_
  have hq : 1 < (Ideal.absNorm v.asIdeal : ℝ) := one_lt_absNorm v
  rw [quatLocalFactor, lamV_inv_mul_omegaQuatV_good ha hb h2 hav hbv, volO_eq_ofReal, hvol, ENNReal.ofReal_one,
    one_pow, mul_one, ENNReal.toReal_ofReal]
  have : ((Ideal.absNorm v.asIdeal : ℝ) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hq.le)
  linarith

include ha hb in
theorem abs_quatLocalFactor_sub_one_le (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      |quatLocalFactor a b v - 1| ≤ 1 * (NFEuler.normP v : ℝ) ^ (-(2 : ℝ)) := by
  refine (quatLocalFactor_good ha hb ha0 hb0).mono fun v hv => ?_
  rw [hv, one_mul, Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two, sub_sub_cancel_left, abs_neg,
    abs_of_nonneg (by positivity)]

include ha hb in
/-- **The Euler product $\prod_v\lambda_v^{-1}\omega_v(\Lambda_v^\times)$ converges absolutely.** -/
theorem multipliable_quatLocalFactor (ha0 : a ≠ 0) (hb0 : b ≠ 0) : Multipliable (quatLocalFactor a b) :=
  NFEuler.multipliable_of_abs_sub_one_le _ (by norm_num) (abs_quatLocalFactor_sub_one_le ha hb ha0 hb0)

variable (a b) in
/-- $\prod_v\lambda_v^{-1}\omega_v(\Lambda_v^\times)$. -/
def quatHatVol : ℝ := ∏' v, quatLocalFactor a b v

include ha hb in
theorem quatHatVol_pos (ha0 : a ≠ 0) (hb0 : b ≠ 0) : 0 < quatHatVol a b :=
  lt_of_le_of_ne (tprod_nonneg fun v => (quatLocalFactor_pos a b v).le)
    (NFEuler.tprod_ne_zero_of_abs_sub_one_le _ (by norm_num) (abs_quatLocalFactor_sub_one_le ha hb ha0 hb0)
      fun v => (quatLocalFactor_pos a b v).ne').symm

/-! ### The Haar measure $\prod_v\lambda_v^{-1}\omega_v$ on $(\mathbb H\otimes\mathbb A_f)^\times$ -/

variable (a b) in
/-- $\hat\Lambda^\times$ as a positive compact. -/
def lamHatCompacts : TopologicalSpace.PositiveCompacts (QuatFin a b)ˣ where
  carrier := lamHatUnits a b
  isCompact' := isCompact_lamHatUnits a b
  interior_nonempty' := ⟨1, by rw [(isOpen_lamHatUnits a b).interior_eq]; exact one_mem_lamHatUnits a b⟩

variable (a b) in
/-- **The Tamagawa measure $\prod_v\lambda_v^{-1}\omega_v$ on $(\mathbb H\otimes\mathbb A_f)^\times$**: the Haar measure with
$\mu(\hat\Lambda^\times) = \prod_v\lambda_v^{-1}\omega_v(\Lambda_v^\times)$. -/
def muFinQuat : Measure (QuatFin a b)ˣ := ENNReal.ofReal (quatHatVol a b) • Measure.haarMeasure (lamHatCompacts a b)

include ha hb in
theorem isHaarMeasure_muFinQuat (ha0 : a ≠ 0) (hb0 : b ≠ 0) : (muFinQuat a b).IsHaarMeasure :=
  Measure.IsHaarMeasure.smul _ (by simp [quatHatVol_pos ha hb ha0 hb0]) ENNReal.ofReal_ne_top

/-- **Normalization**: $\mu(\hat\Lambda^\times) = \prod_v\lambda_v^{-1}\omega_v(\Lambda_v^\times)$. -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure ∏_v λ_v^{-1}ω_v; A = ℍ) [unverified page for A = ℍ]"]
theorem muFinQuat_lamHatUnits : muFinQuat a b (lamHatUnits a b) = ENNReal.ofReal (quatHatVol a b) := by
  rw [muFinQuat, Measure.smul_apply, smul_eq_mul]
  have := Measure.haarMeasure_self (K₀ := lamHatCompacts a b)
  change ENNReal.ofReal (quatHatVol a b) * Measure.haarMeasure (lamHatCompacts a b) (lamHatCompacts a b : Set _) = _
  rw [this, mul_one]

/-! ### The chart lemma -/

variable (a b) in
/-- The box $\prod_{v\in S}U_v\times\prod_{v\notin S}\Lambda_v^\times\subseteq(\mathbb H\otimes\mathbb A_f)^\times$. -/
def quatBox (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (QuatV a b v)ˣ) :
    Set (QuatFin a b)ˣ :=
  (quatChart a b).chartBox S U

theorem measurableSet_quatBox (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (QuatV a b v)ˣ) (hU : ∀ v ∈ S, MeasurableSet (U v)) :
    MeasurableSet (quatBox a b S U) :=
  (quatChart a b).measurableSet_chartBox (continuous_unitAtQ a b) S U hU

include ha hb in
/-- **The chart lemma on $(\mathbb H\otimes\mathbb A_f)^\times$**: $\mu(\prod_{v\in S}U_v\times\prod_{v\notin S}\Lambda_v^\times)
= \mu(\hat\Lambda^\times)\prod_{v\in S}\omega_v(U_v)/\omega_v(\Lambda_v^\times)$. -/
@[kb "weil1982" "§2.3, p. 21 (the measure ∏_v λ_v^{-1}ω_v on the charts)"]
theorem muFinQuat_quatBox (ha0 : a ≠ 0) (hb0 : b ≠ 0) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (QuatV a b v)ˣ) (hU : ∀ v ∈ S, MeasurableSet (U v))
    (hUf : ∀ v ∈ S, omegaQuatV v a b (U v) ≠ ⊤) :
    muFinQuat a b (quatBox a b S U) =
      ENNReal.ofReal (quatHatVol a b) * ∏ v ∈ S, omegaQuatV v a b (U v) / omegaQuatV v a b (lamLocUnits a b v) := by
  have := isHaarMeasure_muFinQuat ha hb ha0 hb0
  have h0 := chartBox_empty_quatChart a b
  have hK : muFinQuat a b ((quatChart a b).chartBox ∅ fun v => (quatChart a b).K v) ≠ ⊤ := by
    rw [h0, muFinQuat_lamHatUnits]; exact ENNReal.ofReal_ne_top
  have := (quatChart a b).measure_chartBox (continuous_unitAtQ a b) (muFinQuat a b) (fun v => omegaQuatV v a b)
    (omegaQuatV_lamLocUnits_ne_top a b) hK S U hU hUf
  rw [quatBox, this, h0, muFinQuat_lamHatUnits]
  rfl

include ha hb in
/-- **Weil's form of the chart lemma**: $\mu(\prod_{v\in S}U_v\times\prod_{v\notin S}\Lambda_v^\times) =
\prod_v\lambda_v^{-1}\omega_v(U'_v)$ (a convergent product), $U'_v = U_v$ for $v\in S$ and $\Lambda_v^\times$ otherwise.
Thus `muFinQuat` is Weil's $\prod_v\lambda_v^{-1}\omega_v$. -/
@[kb "weil1982" "§2.3, p. 21 (the measure ∏_v λ_v^{-1}ω_v on the charts)"]
theorem muFinQuat_quatBox_weil (ha0 : a ≠ 0) (hb0 : b ≠ 0) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (QuatV a b v)ˣ) (hU : ∀ v ∈ S, MeasurableSet (U v))
    (hUf : ∀ v ∈ S, omegaQuatV v a b (U v) ≠ ⊤) :
    muFinQuat a b (quatBox a b S U) = ENNReal.ofReal (∏' v, (ENNReal.ofReal (lamV v)⁻¹ *
      omegaQuatV v a b (if v ∈ S then U v else lamLocUnits a b v)).toReal) := by
  set f := quatLocalFactor a b
  set fS : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (ENNReal.ofReal (lamV v)⁻¹ *
      omegaQuatV v a b (if v ∈ S then U v else lamLocUnits a b v)).toReal
  set g : HeightOneSpectrum (𝓞 F) → ℝ := fun v => if v ∈ S then fS v / f v else 1
  have hfg : fS = f * g := by
    funext v
    simp only [Pi.mul_apply, g]
    split_ifs with hv
    · rw [mul_div_cancel₀ _ (quatLocalFactor_pos a b v).ne']
    · simp only [mul_one, fS, f, quatLocalFactor, hv, ite_false]
  have hg : Multipliable g := multipliable_of_hasFiniteMulSupport ((Finset.finite_toSet S).subset fun v hv => by
    by_contra h; rw [Finset.mem_coe] at h; exact hv (by simp [g, h]))
  have hgS : ∏' v, g v = ∏ v ∈ S, fS v / f v := by
    rw [tprod_eq_prod (s := S) fun v hv => by simp [g, hv]]
    exact Finset.prod_congr rfl fun v hv => by simp [g, hv]
  rw [hfg, show tprod (f * g) = ∏' v, (f v * g v) from rfl,
    (multipliable_quatLocalFactor ha hb ha0 hb0).tprod_mul hg, hgS, muFinQuat_quatBox ha hb ha0 hb0 S U hU hUf,
    show (∏' v, quatLocalFactor a b v) = quatHatVol a b from rfl, ENNReal.ofReal_mul (quatHatVol_pos ha hb ha0 hb0).le]
  congr 1
  rw [ENNReal.ofReal_prod_of_nonneg fun v _ => div_nonneg ENNReal.toReal_nonneg (quatLocalFactor_pos a b v).le]
  refine Finset.prod_congr rfl fun v hv => ?_
  have hfin : ENNReal.ofReal (lamV v)⁻¹ * omegaQuatV v a b (U v) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hUf v hv)
  rw [ENNReal.ofReal_div_of_pos (quatLocalFactor_pos a b v), ofReal_quatLocalFactor]
  simp only [hv, ite_true]
  rw [ENNReal.ofReal_toReal hfin, ENNReal.mul_div_mul_left _ _ (by simpa using lamV_pos v) ENNReal.ofReal_ne_top]

end

end QuadFormsKB.Tamagawa.Measure.Weil
