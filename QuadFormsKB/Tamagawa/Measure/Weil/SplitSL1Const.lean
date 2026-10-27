import QuadFormsKB.Tamagawa.Measure.Weil.SplitSL1FinGlobal

/-!
# The constants of the box computation, for split $D$

* `normInf_mul_prod_modK`: the product formula $|\xi|_\infty\prod_v|\xi|_v = 1$ for $\xi\in F^\times$, in the form used
  here (`ideleNorm_diagUnits`).
* **`normInf_inv_mul_muFinQuat_finQuatBox`**: $|4ab|_\infty^{-1}\,\mu_f(\mathrm{finQuatBox}) = \mu_f(\hat{\mathcal O}^\times)\cdot
  \prod_v|\omega|_v(\mathrm{SL}_2(\mathcal O_v))$; the local Jacobians $|4ab|_v^{-1}$ cancel against $|4ab|_\infty^{-1}$.
-/

open MeasureTheory Measure Set NumberField NumberField.mixedEmbedding IsDedekindDomain Filter
open scoped ENNReal NNReal Classical

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-- **The product formula** $|\xi|_\infty\prod_{v\in S}|\xi|_v = 1$ for $\xi\in F^\times$ and $S$ containing every finite
place where $\xi$ is not a unit. -/
theorem normInf_mul_prod_modK {ξ : F} (hξ : ξ ≠ 0) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∉ S, Valued.v (algebraMap F (v.adicCompletion F) ξ) = 1) :
    normInf (mixedEmbedding F ξ) * ∏ v ∈ S, modK v (algebraMap F (v.adicCompletion F) ξ) = 1 := by
  set g : (Adeles F)ˣ := diagUnits F (Units.mk0 ξ hξ)
  have hpf := ideleNorm_diagUnits (F := F) (Units.mk0 ξ hξ)
  rw [ideleNorm] at hpf
  have hinf : ((infPart g : (mixedSpace F)ˣ) : mixedSpace F) = mixedEmbedding F ξ := rfl
  have hmod : ∀ v, (modAt (finPart g) v : ℝ≥0∞) = modK v (algebraMap F (v.adicCompletion F) ξ) := by
    intro v
    have hne : algebraMap F (v.adicCompletion F) ξ ≠ 0 := (map_ne_zero _).2 hξ
    rw [modAt, modK_of_ne_zero v hne]
    congr 2
    exact Units.ext (by rw [coe_unitsHomeomorphNeZero_symm v]; rfl)
  have hone : ∀ v ∉ S, (modAt (finPart g) v : ℝ) = 1 := by
    intro v hv
    have hu : unitAt (finPart g) v ∈ unitsVSub v := hS v hv
    rw [modAt, distribHaarChar_eq_one_of_mem_unitsVSub hu, NNReal.coe_one]
  rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ (fun v hv => by
    by_contra h; exact hv (hone v h)), hinf] at hpf
  have h1 : normInf (mixedEmbedding F ξ) * ∏ v ∈ S, (modAt (finPart g) v : ℝ≥0∞) = 1 := by
    rw [normInf, ← ENNReal.ofReal_one, ← hpf, ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    rw [ENNReal.ofReal_prod_of_nonneg fun v _ => NNReal.coe_nonneg _]
    exact Finset.prod_congr rfl fun v _ => (ENNReal.ofReal_coe_nnreal).symm
  simpa only [hmod] using h1

/-- $\operatorname{ofReal}(\prod_i f_i) = \prod_i\operatorname{ofReal}(f_i)$ for a multipliable nonnegative family. -/
theorem ofReal_tprod_of_nonneg {ι : Type*} {f : ι → ℝ} (h0 : ∀ i, 0 ≤ f i) (hf : Multipliable f) :
    ENNReal.ofReal (∏' i, f i) = ∏' i, ENNReal.ofReal (f i) := by
  have h := hf.hasProd
  have h' : HasProd (fun i => ENNReal.ofReal (f i)) (ENNReal.ofReal (∏' i, f i)) := by
    unfold HasProd at h ⊢
    refine ((ENNReal.continuous_ofReal.tendsto _).comp h).congr fun s => ?_
    simp only [Function.comp_apply]
    rw [ENNReal.ofReal_prod_of_nonneg fun i _ => h0 i]
  exact h'.tprod_eq.symm

section Box

variable {a b x y : F} (h : x ^ 2 - a * y ^ 2 = b)
  (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
  (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)
  (ha0 : a ≠ 0) (hb0 : b ≠ 0)

theorem algebraMap_four_ab (v : HeightOneSpectrum (𝓞 F)) :
    algebraMap F (v.adicCompletion F) (4 * a * b) =
      4 * algebraMap F (v.adicCompletion F) a * algebraMap F (v.adicCompletion F) b := by
  rw [map_mul, map_mul, map_ofNat]

theorem mixedEmbedding_four_ab :
    mixedEmbedding F (4 * a * b) = 4 * mixedEmbedding F a * mixedEmbedding F b := by
  rw [map_mul, map_mul, map_ofNat]

include ha0 hb0 in
/-- The local factor $\lambda_v^{-1}\omega_v(U_v) = |4ab|_v^{-1}(1 - q^{-2})\operatorname{vol}(\mathcal O_v)^4$. -/
theorem lamV_inv_mul_omegaQuatV_UV (v : HeightOneSpectrum (𝓞 F)) :
    ENNReal.ofReal (lamV v)⁻¹ * omegaQuatV v a b (UV v h) =
      ENNReal.ofReal (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹ ^ 2) *
        ((modK v (algebraMap F (v.adicCompletion F) (4 * a * b)))⁻¹ * volO v ^ 4) := by
  rw [omegaQuatV_UV v h ha0 hb0, algebraMap_four_ab]
  have hl := lamV_pos v
  have hq : (1 : ℝ) - ((Ideal.absNorm v.asIdeal : ℝ) ^ 2)⁻¹ = 1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹ ^ 2 := by
    rw [inv_pow]
  have h2 : ENNReal.ofReal (lamV v)⁻¹ * ENNReal.ofReal ((1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) *
      (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ 2)⁻¹)) = ENNReal.ofReal (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹ ^ 2) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hl.le), ← mul_assoc, lamV, inv_mul_cancel₀ (by rw [← lamV]; exact hl.ne'),
      one_mul, hq]
  calc ENNReal.ofReal (lamV v)⁻¹ * ((modK v (4 * algebraMap F (v.adicCompletion F) a *
        algebraMap F (v.adicCompletion F) b))⁻¹ * (ENNReal.ofReal ((1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) *
        (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ 2)⁻¹)) * volO v ^ 4))
      = (ENNReal.ofReal (lamV v)⁻¹ * ENNReal.ofReal ((1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) *
          (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ 2)⁻¹))) * ((modK v (4 * algebraMap F (v.adicCompletion F) a *
          algebraMap F (v.adicCompletion F) b))⁻¹ * volO v ^ 4) := by ring
    _ = _ := by rw [h2]

/-- The finite set of places where $4ab$ is not a unit or $\operatorname{vol}(\mathcal O_v)\ne1$. -/
def constPlaces : Finset (HeightOneSpectrum (𝓞 F)) :=
  badPlaces (x := x) (y := y) ha0 hb0 ∪ (mulSupport_volO_real_finite (F := F)).toFinset

include ha0 hb0 in
theorem valued_four_ab_of_not_mem {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ constPlaces (x := x) (y := y) ha0 hb0) :
    Valued.v (algebraMap F (v.adicCompletion F) (4 * a * b)) = 1 := by
  have hv' : v ∉ badPlaces (x := x) (y := y) ha0 hb0 := fun h' => hv (Finset.mem_union_left _ h')
  obtain ⟨h2, hav, hbv, -, -⟩ := isGoodPlace_of_not_mem_badPlaces ha0 hb0 hv'
  rw [algebraMap_four_ab, map_mul, map_mul, hav, hbv, mul_one, mul_one,
    show (4 : v.adicCompletion F) = 2 * 2 by norm_num, map_mul, h2, mul_one]

include ha0 hb0 in
theorem volO_eq_one_of_not_mem {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ constPlaces (x := x) (y := y) ha0 hb0) :
    volO v = 1 := by
  have hv' : v ∉ (mulSupport_volO_real_finite (F := F)).toFinset := fun h' => hv (Finset.mem_union_right _ h')
  rw [Set.Finite.mem_toFinset, Function.mem_mulSupport, not_not] at hv'
  rw [volO_eq_ofReal, hv', ENNReal.ofReal_one]

set_option maxHeartbeats 2000000 in
include h ha hb ha0 hb0 in
/-- **The constants match**: $|4ab|_\infty^{-1}\,\mu_f(\mathrm{finQuatBox}) = \mu_f(\hat{\mathcal O}^\times)\cdot
\prod_v|\omega|_v(\mathrm{SL}_2(\mathcal O_v))$ (the product formula cancels the Jacobians $|4ab|_v$). -/
theorem normInf_inv_mul_muFinQuat_finQuatBox :
    (normInf (4 * mixedEmbedding F a * mixedEmbedding F b))⁻¹ * muFinQuat a b (finQuatBox h) =
      muFinUnits F (OHatUnits F) * finFactorSL2 F := by
  set S := constPlaces (x := x) (y := y) ha0 hb0 with hS
  set T : HeightOneSpectrum (𝓞 F) → ℝ≥0∞ := fun v => ENNReal.ofReal (lamV v)⁻¹ * omegaQuatV v a b (UV v h)
    with hT
  set A : HeightOneSpectrum (𝓞 F) → ℝ≥0∞ := fun v => ENNReal.ofReal (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹ ^ 2)
  set B : HeightOneSpectrum (𝓞 F) → ℝ≥0∞ := fun v =>
    (modK v (algebraMap F (v.adicCompletion F) (4 * a * b)))⁻¹ * volO v ^ 4
  have hTAB : ∀ v : HeightOneSpectrum (𝓞 F), T v = A v * B v := fun v => lamV_inv_mul_omegaQuatV_UV h ha0 hb0 v
  have hne : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) (4 * a * b) ≠ 0 := fun v => by
    rw [algebraMap_four_ab]; exact four_ab_ne_zero v ha0 hb0
  have hmd0 : ∀ v : HeightOneSpectrum (𝓞 F), modK v (algebraMap F (v.adicCompletion F) (4 * a * b)) ≠ 0 := fun v =>
    (hyp_adic v).md_ne_zero _ (isUnit_iff_ne_zero.2 (hne v))
  have hmdT : ∀ v : HeightOneSpectrum (𝓞 F), modK v (algebraMap F (v.adicCompletion F) (4 * a * b)) ≠ ⊤ := fun v =>
    (hyp_adic v).md_ne_top _ (isUnit_iff_ne_zero.2 (hne v))
  have hBT : ∀ v : HeightOneSpectrum (𝓞 F), B v ≠ ⊤ := fun v =>
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (hmd0 v)) (ENNReal.pow_ne_top (volO_ne_top v))
  have hAT : ∀ v : HeightOneSpectrum (𝓞 F), A v ≠ ⊤ := fun v => ENNReal.ofReal_ne_top
  have hTT : ∀ v : HeightOneSpectrum (𝓞 F), T v ≠ ⊤ := fun v => by rw [hTAB]; exact ENNReal.mul_ne_top (hAT v) (hBT v)
  have hA1 : ∀ v : HeightOneSpectrum (𝓞 F), A v ≤ 1 := fun v =>
    ENNReal.ofReal_le_one.2 (by nlinarith [sq_nonneg ((Ideal.absNorm v.asIdeal : ℝ)⁻¹)])
  have hB1 : ∀ v ∉ S, B v = 1 := by
    intro v hv
    have hu : (unitsHomeomorphNeZero.symm ⟨_, hne v⟩ : (v.adicCompletion F)ˣ) ∈ unitsVSub v := by
      change Valued.v ((unitsHomeomorphNeZero.symm ⟨_, hne v⟩ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1
      rw [coe_unitsHomeomorphNeZero_symm v]
      exact valued_four_ab_of_not_mem ha0 hb0 hv
    simp only [B, modK_of_ne_zero v (hne v), distribHaarChar_eq_one_of_mem_unitsVSub hu, ENNReal.coe_one, inv_one,
      one_mul, volO_eq_one_of_not_mem ha0 hb0 hv, one_pow]
  have hBS : ∏ v ∈ S, B v ≠ ⊤ := ENNReal.prod_ne_top fun v _ => hBT v
  -- `μ_f(finQuatBox)` as an `ℝ≥0∞`-valued product
  have hmult : Multipliable fun v => (T v).toReal := by
    set f := quatLocalFactor a b
    set g : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (T v).toReal / f v
    have hfg : (fun v => (T v).toReal) = f * g := by
      funext v
      simp only [Pi.mul_apply, g]
      rw [mul_div_cancel₀ _ (quatLocalFactor_pos a b v).ne']
    have hg : Multipliable g := by
      refine multipliable_of_hasFiniteMulSupport ?_
      refine (Finset.finite_toSet (badPlaces (x := x) (y := y) ha0 hb0)).subset fun v hv => ?_
      by_contra hvS
      apply hv
      simp only [g, hT]
      rw [UV_eq_of_not_mem_badPlaces h ha0 hb0 hvS, ← ofReal_quatLocalFactor,
        ENNReal.toReal_ofReal (quatLocalFactor_pos a b v).le, div_self (quatLocalFactor_pos a b v).ne']
    rw [hfg]
    exact (multipliable_quatLocalFactor ha hb ha0 hb0).mul hg
  have hfin : muFinQuat a b (finQuatBox h) = ∏' v, T v := by
    rw [muFinQuat_finQuatBox h ha hb ha0 hb0, ofReal_tprod_of_nonneg (fun v => ENNReal.toReal_nonneg) hmult]
    exact tprod_congr fun v => ENNReal.ofReal_toReal (hTT v)
  rw [hfin]
  simp_rw [hTAB]
  rw [tprod_mul_of_eq_one_off hA1 S hB1 hBS]
  -- the product formula
  have hpf := normInf_mul_prod_modK (ξ := 4 * a * b) (mul_ne_zero (mul_ne_zero (by norm_num) ha0) hb0) S
    fun v hv => valued_four_ab_of_not_mem ha0 hb0 hv
  rw [mixedEmbedding_four_ab] at hpf
  have hinv : (normInf (4 * mixedEmbedding F a * mixedEmbedding F b))⁻¹ =
      ∏ v ∈ S, modK v (algebraMap F (v.adicCompletion F) (4 * a * b)) := by
    rw [ENNReal.eq_inv_of_mul_eq_one_left hpf, inv_inv]
  have hvol : ∏ v ∈ S, volO v ^ 4 = ENNReal.ofReal (ohatVol F) ^ 4 := by
    rw [ohatVol_eq_finprod, finprod_eq_prod_of_mulSupport_subset (s := S) _ (fun v hv => by
      by_contra h'
      have := volO_eq_one_of_not_mem ha0 hb0 h'
      rw [volO_eq_ofReal] at this
      exact hv (ENNReal.ofReal_eq_one.1 this)),
      ENNReal.ofReal_prod_of_nonneg (fun v _ => measureReal_nonneg), ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun v _ => by rw [volO_eq_ofReal]
  have hBprod : (normInf (4 * mixedEmbedding F a * mixedEmbedding F b))⁻¹ * ∏ v ∈ S, B v =
      ENNReal.ofReal (ohatVol F) ^ 4 := by
    rw [hinv, ← Finset.prod_mul_distrib, ← hvol]
    refine Finset.prod_congr rfl fun v _ => ?_
    simp only [B]
    rw [← mul_assoc, ENNReal.mul_inv_cancel (hmd0 v) (hmdT v), one_mul]
  rw [← mul_assoc, hBprod, muFinUnits_OHatUnits, finFactorSL2]
  ring

end Box

end QuadFormsKB.Tamagawa.Measure.Weil
