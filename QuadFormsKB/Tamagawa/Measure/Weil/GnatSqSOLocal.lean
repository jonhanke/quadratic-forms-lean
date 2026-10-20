/-
# The $SO$ side: local volumes for $\langle1,-a,-b,ab\rangle$ and $\langle-a,-b,ab\rangle$

**Layer:** a number field $F$, a finite place $v$, $a, b\in\mathcal O_F\setminus0$.

* **`congSub_le_soSub`**: $K_m\subseteq SO(V)(F_v)$ for $m > s_v$ ($\det\equiv1\bmod\pi^m$ and $\det = \pm1$); hence
  **`muLocSO_congSub`**: $\mu^{SO}_v(K_m) = \mu_v(K_m)$ (any nondegenerate $Q_0$).
* **`siegelDensity_qSq`**: at $v\nmid2ab$, $\alpha_v(\langle1,-a,-b,ab\rangle) = \alpha_v(\langle-a,-b,ab\rangle)^2 = (1-q^{-2})^2$
  (`localDensityForm_self_even` with $\chi = 1$: the discriminant $a^2b^2$ is a square; `muLocSO_soStabSO_ternary`).
* **`omegaV_nU`**: $\omega_v(1+\pi^k\mathfrak o_v) = \mathrm{vol}(\pi^k\mathfrak o_v)$ ($k\ge1$).

Source: Weil 1982, §2.2 [unverified page]; Kitaoka 1993, §5.6 [unverified].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqCombine

open Matrix NumberField IsDedekindDomain WithZero MeasureTheory Set
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices LerayPadic LocalDensity

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "πv" => LocalDensity.NF.π v

/-- **$K_m\subseteq SO(V)(F_v)$** for $m > s_v$. -/
theorem congSub_le_soSub {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) {s m : ℕ}
    (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) (hsm : s < m) (hm : 1 ≤ m) {g : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv}
    (hg : g ∈ congSub v Q₀ m hm) : g ∈ soSub (Q₀.map (algebraMap (𝓞 F) F)) Fv := by
  have hd := valued_det_sub_one_le v ((mem_congSub v Q₀).1 hg)
  rcases det_eq_one_or_neg_one _ (Measure.nondegenerate_QF Q₀ hQ) g with h | h
  · exact h
  · exfalso
    rw [h, show (-1 : Fv) - 1 = -2 by ring, Valuation.map_neg, hs, exp_le_exp] at hd
    omega

/-- **$\mu^{SO}_v(K_m) = \mu_v(K_m)$** ($m > s_v$). -/
theorem muLocSO_congSub {n : ℕ} (hn : 0 < n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) {s m : ℕ}
    (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) (hsm : s < m) (hm : 1 ≤ m) :
    Measure.muLocSO v Q₀ 1 (Subtype.val ⁻¹' (congSub v Q₀ m hm : Set (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv))) =
      Measure.muLoc v Q₀ 1 (congSub v Q₀ m hm : Set _) := by
  rw [Measure.muLocSO_eq_comap v Q₀ hQ hn one_pos, (Measure.measurableEmbedding_soSub v Q₀ hQ).comap_apply]
  congr 1
  rw [Set.image_preimage_eq_inter_range, Subtype.range_coe, Set.inter_eq_left]
  exact fun g hg => congSub_le_soSub v Q₀ hQ hs hsm hm hg

theorem not_dvd_of_valued_eq_one {z : 𝔬} (h : Valued.v (z : Fv) = 1) : ¬ πv ∣ z := by
  have := (pow_dvd_of_valued (v := v) (e := 0) (by rw [h]; rfl)).2
  simpa using this

/-- **The good-place density of $\langle1,-a,-b,ab\rangle$** ($|2ab|_v = 1$): $\alpha_v = (1 - q^{-2})^2$. -/
theorem siegelDensity_qSq_good {a b : 𝓞 F} (h2 : Valued.v (2 : Fv) = 1)
    (ha : Valued.v (algebraMap F Fv (a : F)) = 1) (hb : Valued.v (algebraMap F Fv (b : F)) = 1) :
    NF.siegelDensity v (qSq a b) (qSq a b) = (1 - ((DVR.q 𝔬 : ℝ) ^ 2)⁻¹) ^ 2 := by
  classical
  let _ : Fintype (IsLocalRing.ResidueField 𝔬) := Fintype.ofFinite _
  have h2' : ¬ πv ∣ (2 : 𝔬) := not_dvd_of_valued_eq_one v (by rw [show ((2 : 𝔬) : Fv) = 2 by push_cast; rfl]; exact h2)
  have hι : ∀ x : 𝓞 F, ((NF.ι v x : 𝔬) : Fv) = algebraMap F Fv (x : F) := coe_ι
  have hres : ∀ z : 𝔬, ¬ πv ∣ z → IsLocalRing.residue 𝔬 z ≠ 0 := by
    intro z hz h0
    rw [IsLocalRing.residue_eq_zero_iff, (NF.irreducible_π v).maximalIdeal_eq, Ideal.mem_span_singleton] at h0
    exact hz h0
  have hab : ¬ πv ∣ (NF.ι v a * NF.ι v b) := by
    refine not_dvd_of_valued_eq_one v ?_
    push_cast; rw [hι, hι, map_mul, ha, hb, mul_one]
  have e : (NF.Qp v (qSq a b)).hessian.det = 2 ^ 4 * (NF.ι v a * NF.ι v b) ^ 2 := by
    rw [hessian_Qp_qSq, Matrix.det_diagonal, Fin.prod_univ_four]
    norm_num [Matrix.vecHead, Matrix.vecTail]
    rw [map_ofNat]; ring
  have hdet : ¬ πv ∣ (NF.Qp v (qSq a b)).hessian.det := by
    rw [e]
    refine not_dvd_of_valued_eq_one v ?_
    push_cast
    rw [map_mul, map_pow, map_pow, show ((2 : 𝔬) : Fv) = 2 by push_cast; rfl, h2, hι, hι, map_mul, ha, hb]
    norm_num
  have h2r : (2 : IsLocalRing.ResidueField 𝔬) ≠ 0 := by
    have := hres 2 h2'; rwa [map_ofNat] at this
  have hχ : DVR.chiDisc (NF.Qp v (qSq a b)) = 1 := by
    unfold DVR.chiDisc DVR.resGramDet
    have hr : IsLocalRing.residue 𝔬 (2 ^ 4 * (NF.ι v a * NF.ι v b) ^ 2) / 2 ^ 4 =
        (IsLocalRing.residue 𝔬 (NF.ι v a * NF.ι v b)) ^ 2 := by
      rw [map_mul, map_pow, map_pow, map_ofNat, mul_div_cancel_left₀ _ (pow_ne_zero 4 h2r)]
    rw [e, hr, show (4 : ℕ) / 2 = 2 by rfl, neg_one_sq, one_mul]
    exact quadraticChar_sq_one' (hres _ hab)
  rw [NF.siegelDensity, if_pos rfl, NF.localDensityForm_eq_completion,
    DVR.localDensityForm_self_even πv 2 (by norm_num) _ (NF.irreducible_π v) h2' hdet, hχ]
  simp only [Int.cast_one, one_mul, show 2 - 1 = 1 by rfl, Finset.range_one, Finset.prod_singleton]
  ring

/-- **The good-place density of $\langle-a,-b,ab\rangle$** ($|2ab|_v = 1$): $\alpha_v = 1 - q^{-2}$. -/
theorem siegelDensity_pureFormO_good {a b : 𝓞 F} (h2 : Valued.v (2 : Fv) = 1)
    (ha : Valued.v (algebraMap F Fv (a : F)) = 1) (hb : Valued.v (algebraMap F Fv (b : F)) = 1) :
    NF.siegelDensity v (QuatZeta.pureFormO a b) (QuatZeta.pureFormO a b) = 1 - ((DVR.q 𝔬 : ℝ) ^ 2)⁻¹ := by
  have h2' : ¬ πv ∣ (2 : 𝔬) := not_dvd_of_valued_eq_one v (by rw [show ((2 : 𝔬) : Fv) = 2 by push_cast; rfl]; exact h2)
  have hι : ∀ x : 𝓞 F, ((NF.ι v x : 𝔬) : Fv) = algebraMap F Fv (x : F) := coe_ι
  have e : (NF.Qp v (QuatZeta.pureFormO a b)).hessian.det = 2 ^ 3 * (NF.ι v a * NF.ι v b) ^ 2 := by
    rw [hessian_Qp_pureFormO, Matrix.det_diagonal, Fin.prod_univ_three]
    norm_num [Matrix.vecHead, Matrix.vecTail]
    rw [map_ofNat]; ring
  have hdet : ¬ πv ∣ (NF.Qp v (QuatZeta.pureFormO a b)).hessian.det := by
    rw [e]
    refine not_dvd_of_valued_eq_one v ?_
    push_cast
    rw [map_mul, map_pow, map_pow, show ((2 : 𝔬) : Fv) = 2 by push_cast; rfl, h2, hι, hι, map_mul, ha, hb]
    norm_num
  have h := muLocSO_soStabSO_ternary v (QuatZeta.pureFormO a b) h2' hdet
  rw [Measure.muLocSO_soStabSO, div_one] at h
  have hpos := siegelDensity_self_pos' (QuatZeta.pureFormO a b) (nondegenerate_pureFormO a b
    (fun h0 => by rw [h0] at ha; simp at ha) (fun h0 => by rw [h0] at hb; simp at hb)) v
  have hq : (0 : ℝ) ≤ 1 - ((DVR.q 𝔬 : ℝ) ^ 2)⁻¹ := by
    have h1 : (1 : ℝ) ≤ (DVR.q 𝔬 : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast (DVR.q_pos (R := 𝔬)))
    have := inv_le_one_of_one_le₀ h1
    linarith
  exact (ENNReal.ofReal_eq_ofReal_iff hpos.le hq).1 h

/-- **$\omega_v(1+\pi^k\mathfrak o_v) = \mathrm{vol}(\pi^k\mathfrak o_v)$** ($k\ge1$). -/
theorem omegaV_oneAdd {k : ℕ} (hk : 1 ≤ k) :
    omegaV v {r : Fvˣ | Valued.v ((r : Fv) - 1) ≤ exp (-(k : ℤ))} =
      Analysis.selfDualV v (Analysis.latticeV v (k : ℤ)) := by
  set A : Set Fvˣ := {r : Fvˣ | Valued.v ((r : Fv) - 1) ≤ exp (-(k : ℤ))}
  have hA : A = Units.val ⁻¹' ((fun x => x - 1) ⁻¹' (Analysis.latticeV v (k : ℤ) : Set Fv)) := by
    ext r; simp [A, Analysis.mem_latticeV]
  have hAm : MeasurableSet A := by
    rw [hA]
    exact ((Analysis.measurableSet_latticeV v _).preimage (measurable_id.sub_const 1)).preimage
      Units.continuous_val.measurable
  have h1 : ∀ u ∈ A, distribHaarChar Fv u = 1 := fun u hu =>
    distribHaarChar_eq_one_of_mem_unitsVSub (valued_eq_one_of_sub_one_lt v (valued_lt_one_of_le_exp v hk hu))
  rw [omegaV, unitsHaar_apply_of_forall_eq_one (isOpenEmbedding_val_adic v) (continuous_distribHaarChar_adic v) _ hAm h1]
  have himg : Units.val '' A = (fun x => x - 1) ⁻¹' (Analysis.latticeV v (k : ℤ) : Set Fv) := by
    rw [hA]
    ext x
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hx
      have hx0 : x ≠ 0 := by
        intro h0
        have : Valued.v (x - 1) < 1 := valued_lt_one_of_le_exp v hk hx
        rw [h0, zero_sub, Valuation.map_neg, map_one] at this; exact lt_irrefl _ this
      exact ⟨Units.mk0 x hx0, hx, rfl⟩
  rw [himg, show (fun x : Fv => x - 1) ⁻¹' (Analysis.latticeV v (k : ℤ) : Set Fv) =
    (fun x => (-1 : Fv) + x) ⁻¹' (Analysis.latticeV v (k : ℤ) : Set Fv) by ext x; simp [neg_add_eq_sub],
    measure_preimage_add]

end QuadFormsKB.Tamagawa.Measure.Weil
