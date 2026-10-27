import QuadFormsKB.Tamagawa.Measure.Weil.SplitSL1Const

/-!
# $\tau(\mathrm{SL}_1(D)) = 1$ for split $D$

**Layer:** $F$ a number field, $a, b\in\mathcal O_F\setminus 0$, $x, y\in F$ with $x^2 - ay^2 = b$.

* `quatBoxX_eq_prod`: the box $X = \Phi^{-1}(\text{`boxM W`})$ is $\{u_\infty\in\Phi_\infty^{-1}W\}\times\mathrm{finQuatBox}$, so
  `tamQuat_quatBoxX`: $\mathrm{tamQuat}(X) = \omega_\infty(\Phi_\infty^{-1}W)\,\mu_f(\mathrm{finQuatBox})$.
-/

open MeasureTheory Measure Set NumberField NumberField.mixedEmbedding IsDedekindDomain Filter
open scoped ENNReal NNReal Classical

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

section Glue

variable {a b x y : F} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (h : x ^ 2 - a * y ^ 2 = b)

theorem archM_quatAdeleMatEquiv (u : (QuatAdele a b)ˣ) :
    archM (quatAdeleMatEquiv ha0 hb0 h (u : QuatAdele a b)) =
      phiInf h (((quatUnitsEquiv a b u).1 : (QuatInf a b)ˣ) : QuatInf a b) := by
  rw [quatAdeleMatEquiv_apply, phiInf, quatMatHom_apply]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> rfl

theorem snd_quatAdeleMatEquiv (q : QuatAdele a b) (i j : Fin 2) :
    (quatAdeleMatEquiv ha0 hb0 h q i j).2 = phiFin h ((quatAdeleRingEquiv a b q).2) i j := by
  rw [quatAdeleMatEquiv_apply, phiFin, quatMatHom_apply]
  fin_cases i <;> fin_cases j <;> rfl

/-- **The box is a product** $\{u_\infty\in\Phi_\infty^{-1}W\}\times\mathrm{finQuatBox}$. -/
theorem quatBoxX_eq_prod (W : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F))) :
    quatBoxX ha0 hb0 h W = quatUnitsEquiv a b ⁻¹'
      ({w : (QuatInf a b)ˣ | phiInf h (w : QuatInf a b) ∈ W} ×ˢ finQuatBox h) := by
  ext u
  have h2 : ∀ q : QuatAdele a b, FinInt (quatAdeleMatEquiv ha0 hb0 h q) ↔
      ∀ i j, phiFin h ((quatAdeleRingEquiv a b q).2) i j ∈ OHat := fun q => by
    simp only [FinInt, snd_quatAdeleMatEquiv]
  have hinv : (((quatUnitsEquiv a b u).2⁻¹ : (QuatFin a b)ˣ) : QuatFin a b) =
      (quatAdeleRingEquiv a b ((u⁻¹ : (QuatAdele a b)ˣ) : QuatAdele a b)).2 := by
    rw [← Prod.snd_inv, ← map_inv]; rfl
  simp only [quatBoxX, boxM, Set.mem_preimage, Set.mem_prod, Set.mem_ofPred_eq, coe_matUnitsEquiv, finQuatBox,
    ← map_inv, h2, archM_quatAdeleMatEquiv, hinv]
  constructor
  · rintro ⟨h1, h3, h4⟩; exact ⟨h4, h1, h3⟩
  · rintro ⟨h4, h1, h3⟩; exact ⟨h1, h3, h4⟩

/-- $\mathrm{tamQuat}(X) = \omega_\infty(\Phi_\infty^{-1}W)\cdot\mu_f(\mathrm{finQuatBox})$. -/
theorem tamQuat_quatBoxX (W : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F))) :
    tamQuat a b (quatBoxX ha0 hb0 h W) =
      omegaQuatInf a b {w : (QuatInf a b)ˣ | phiInf h (w : QuatInf a b) ∈ W} * muFinQuat a b (finQuatBox h) := by
  rw [quatBoxX_eq_prod, tamQuat_prod]

end Glue

/-! ### The archimedean set $W = \sigma(T)\cdot V$ -/

/-- $|\omega|_\infty$ is carried by $\{\det = 1\}$. -/
theorem muGaugeInf_inter_det {S : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F))} (hS : MeasurableSet S) :
    muGaugeInf F S = muGaugeInf F (S ∩ {Y | Y.det = 1}) := by
  have hD : MeasurableSet {Y : Matrix (Fin 2) (Fin 2) (mixedSpace F) | Y.det = 1} :=
    (isClosed_eq (continuous_id.matrix_det) continuous_const).measurableSet
  rw [muGaugeInf_apply hS, muGaugeInf_apply (hS.inter hD)]
  refine lintegral_congr fun a' => ?_
  by_cases ha : IsUnit a'
  · rw [Set.indicator_of_mem (show a' ∈ {x : mixedSpace F | IsUnit x} from ha),
      Set.indicator_of_mem (show a' ∈ {x : mixedSpace F | IsUnit x} from ha)]
    congr 1
    refine lintegral_congr fun c => lintegral_congr fun b' => ?_
    have hdet : (!![a', b'; c, (1 + c * b') * a'⁻¹] : Matrix (Fin 2) (Fin 2) (mixedSpace F)).det = 1 := by
      rw [Matrix.det_fin_two_of]
      calc a' * ((1 + c * b') * a'⁻¹) - b' * c = (1 + c * b') * (a' * a'⁻¹) - b' * c := by ring
        _ = 1 := by rw [mixedSpace_mul_inv_cancel ha]; ring
    simp only [Set.indicator, Set.mem_inter_iff, Set.mem_ofPred_eq, hdet, and_true]
  · rw [Set.indicator_of_notMem (show a' ∉ {x : mixedSpace F | IsUnit x} from ha),
      Set.indicator_of_notMem (show a' ∉ {x : mixedSpace F | IsUnit x} from ha)]

/-- $W = \{X : \det X\in T,\ \operatorname{diag}(1,\det X^{-1})X\in V\}$, $V$ = `slNbhdInf`. -/
def splitBoxW (T : Set (mixedSpace F)) : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F)) :=
  {X | X.det ∈ T ∧ !![1, 0; 0, X.det⁻¹] * X ∈ slNbhdInf F}

theorem isUnit_of_norm_sub_one_lt {z : mixedSpace F} (hz : ‖z - 1‖ < 1 / 2) : IsUnit z := by
  rw [isUnit_mixedSpace_iff]
  constructor
  · intro w h0
    have h1 : ‖(z - 1).1 w‖ ≤ ‖z - 1‖ := (norm_le_pi_norm (z - 1).1 w).trans (norm_fst_le _)
    have : (z - 1).1 w = -1 := by simp [h0]
    rw [this, norm_neg, norm_one] at h1
    linarith
  · intro w h0
    have h1 : ‖(z - 1).2 w‖ ≤ ‖z - 1‖ := (norm_le_pi_norm (z - 1).2 w).trans (norm_snd_le _)
    have : (z - 1).2 w = -1 := by simp [h0]
    rw [this, norm_neg, norm_one] at h1
    linarith

theorem mem_splitBoxW_chart {T : Set (mixedSpace F)} (hT : ∀ t ∈ T, IsUnit t) {X : Matrix (Fin 2) (Fin 2) (mixedSpace F)}
    (hX : X ∈ splitBoxW T) : IsUnit (X 0 0) ∧ IsUnit X.det := by
  refine ⟨?_, hT _ hX.1⟩
  have h00 : (!![1, 0; 0, X.det⁻¹] * X) 0 0 = X 0 0 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have := hX.2.1
  rw [h00] at this
  exact isUnit_of_norm_sub_one_lt this

theorem measurableSet_splitBoxW {T : Set (mixedSpace F)} (hT : MeasurableSet T) : MeasurableSet (splitBoxW T) := by
  have hdet : Measurable fun X : Matrix (Fin 2) (Fin 2) (mixedSpace F) => X.det :=
    (continuous_id.matrix_det).measurable
  have hX : ∀ k l, Measurable fun X : Matrix (Fin 2) (Fin 2) (mixedSpace F) => X k l :=
    fun k l => (measurable_pi_apply l).comp (measurable_pi_apply k)
  have hm : Measurable fun X : Matrix (Fin 2) (Fin 2) (mixedSpace F) => !![1, 0; 0, X.det⁻¹] * X := by
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
      exact (measurable_const.mul (hX 0 j)).add (measurable_const.mul (hX 1 j))
    · simp only [Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
      exact (measurable_const.mul (hX 0 j)).add ((measurable_inv_mixedSpace.comp hdet).mul (hX 1 j))
  exact (hdet hT).inter (hm measurableSet_slNbhdInf)

/-- **The fibres of $W$**: $|\omega|_\infty\{Y : \sigma(t)Y\in W\} = \mathbf 1_T(t)\,|\omega|_\infty(V)$. -/
theorem muGaugeInf_fibre_splitBoxW {T : Set (mixedSpace F)} (hT : MeasurableSet T) (t : (mixedSpace F)ˣ) :
    muGaugeInf F {Y | !![1, 0; 0, (t : mixedSpace F)] * Y ∈ splitBoxW T} =
      T.indicator (fun _ => muGaugeInf F (slNbhdInf F)) (t : mixedSpace F) := by
  have hS : MeasurableSet {Y : Matrix (Fin 2) (Fin 2) (mixedSpace F) | !![1, 0; 0, (t : mixedSpace F)] * Y ∈ splitBoxW T} :=
    (measurableSet_splitBoxW hT).preimage (continuous_const.matrix_mul continuous_id).measurable
  have hset : {Y : Matrix (Fin 2) (Fin 2) (mixedSpace F) | !![1, 0; 0, (t : mixedSpace F)] * Y ∈ splitBoxW T} ∩
      {Y | Y.det = 1} = (if (t : mixedSpace F) ∈ T then slNbhdInf F else ∅) ∩ {Y | Y.det = 1} := by
    ext Y
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, splitBoxW]
    constructor
    · rintro ⟨⟨h1, h2⟩, hd⟩
      refine ⟨?_, hd⟩
      have hdt : (!![1, 0; 0, (t : mixedSpace F)] * Y).det = t := by
        rw [Matrix.det_mul, hd, mul_one, Matrix.det_fin_two_of]; ring
      rw [hdt] at h1 h2
      rw [if_pos h1]
      have e : !![1, 0; 0, (t : mixedSpace F)⁻¹] * (!![1, 0; 0, (t : mixedSpace F)] * Y) = Y := by
        rw [← mul_assoc]
        have : !![1, 0; 0, (t : mixedSpace F)⁻¹] * !![1, 0; 0, (t : mixedSpace F)] = 1 := by
          refine Matrix.ext fun i j => ?_
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm _ (t : mixedSpace F),
              mixedSpace_mul_inv_cancel t.isUnit]
        rw [this, one_mul]
      rwa [e] at h2
    · rintro ⟨h1, hd⟩
      have hdt : (!![1, 0; 0, (t : mixedSpace F)] * Y).det = t := by
        rw [Matrix.det_mul, hd, mul_one, Matrix.det_fin_two_of]; ring
      by_cases ht : (t : mixedSpace F) ∈ T
      · rw [if_pos ht] at h1
        refine ⟨⟨by rw [hdt]; exact ht, ?_⟩, hd⟩
        rw [hdt]
        have e : !![1, 0; 0, (t : mixedSpace F)⁻¹] * (!![1, 0; 0, (t : mixedSpace F)] * Y) = Y := by
          rw [← mul_assoc]
          have : !![1, 0; 0, (t : mixedSpace F)⁻¹] * !![1, 0; 0, (t : mixedSpace F)] = 1 := by
            refine Matrix.ext fun i j => ?_
            fin_cases i <;> fin_cases j <;>
              simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm _ (t : mixedSpace F),
                mixedSpace_mul_inv_cancel t.isUnit]
          rw [this, one_mul]
        rw [e]; exact h1
      · rw [if_neg ht] at h1; exact absurd h1 (Set.notMem_empty _)
  rw [muGaugeInf_inter_det hS, hset]
  by_cases ht : (t : mixedSpace F) ∈ T
  · rw [if_pos ht, Set.indicator_of_mem ht, ← muGaugeInf_inter_det measurableSet_slNbhdInf]
  · rw [if_neg ht, Set.indicator_of_notMem ht, Set.empty_inter, measure_empty]

/-! ### $\psi_*\mu_{\mathrm{SL}_1} = \mu_T$ and $\tau(\mathrm{SL}_1(D)) = 1$ -/

set_option maxHeartbeats 4000000 in
/-- **For split $D = \mathbb H[F,a,b]$ ($b = x^2 - ay^2$), Weil's Tamagawa measure of $\mathrm{SL}_1(D)$ is the
measure $\mu_T$ of $\mathrm{SL}_2$**: $\psi_*\mu_{\mathrm{SL}_1} = \mu_T$, $\psi$ = `sl1SplitEquiv`. Proof: both fibred
measures over $\operatorname{nrd} = \det$ agree on the box $X = \Phi^{-1}\{g : g_f\in\mathrm{GL}_2(\hat{\mathcal O}),
g_\infty\in W\}$ (local fibrations at every place, the Jacobian $4ab$ of $\Phi$ cancelled by the product formula), and
`map_muSL1_eq_muT_of_box`. -/
@[kb "weil1982" "§2.4, Thm 2.4.4 (Tamagawa measures in an exact sequence); §3.7 (τ(SL₁(D)) = 1) [unverified page for §3.7]"]
theorem map_muSL1_eq_muT_of_split {x y : F} (a b : 𝓞 F) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (h : x ^ 2 - (a : F) * y ^ 2 = (b : F)) :
    (muSL1 (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)).map
      (sl1SplitEquiv (by simpa using ha0) (by simpa using hb0) h) = muT F := by
  have ha0' : (a : F) ≠ 0 := by simpa using ha0
  have hb0' : (b : F) ≠ 0 := by simpa using hb0
  obtain ⟨K⟩ := (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts (mixedSpace F)ˣ))
  set T : Set (mixedSpace F) := Units.val '' (K : Set (mixedSpace F)ˣ) with hTdef
  have hTc : IsCompact T := K.isCompact.image Units.continuous_val
  have hTm : MeasurableSet T := hTc.isClosed.measurableSet
  have hTu : ∀ t ∈ T, IsUnit t := by rintro _ ⟨u, -, rfl⟩; exact u.isUnit
  have hW := measurableSet_splitBoxW hTm
  have hWu : ∀ X ∈ splitBoxW T, IsUnit (X 0 0) ∧ IsUnit X.det := fun X hX => mem_splitBoxW_chart hTu hX
  have hfib := fibMeas_quatBoxX ha0' hb0' h hW
  have hA2 := lintegral_omegaInf_muGaugeInf (F := F) hW
  have htam := tamQuat_quatBoxX ha0' hb0' h (splitBoxW T)
  have hA1 := omegaQuatInf_phiInf h ha0' hb0' hW hWu
  have hC := normInf_inv_mul_muFinQuat_finQuatBox h (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0'
  -- the fibre integral
  have hG : ∫⁻ t, muGaugeInf F {Y | !![1, 0; 0, ((t : (mixedSpace F)ˣ) : mixedSpace F)] * Y ∈ splitBoxW T}
      ∂omegaInf F = omegaInf F K * muGaugeInf F (slNbhdInf F) := by
    have hind : ∀ t : (mixedSpace F)ˣ, muGaugeInf F {Y | !![1, 0; 0, (t : mixedSpace F)] * Y ∈ splitBoxW T} =
        (K : Set (mixedSpace F)ˣ).indicator (fun _ => muGaugeInf F (slNbhdInf F)) t := by
      intro t
      rw [muGaugeInf_fibre_splitBoxW hTm]
      by_cases ht : t ∈ (K : Set (mixedSpace F)ˣ)
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (show (t : mixedSpace F) ∈ T from ⟨t, ht, rfl⟩)]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem]
        rintro ⟨u, hu, hut⟩
        exact ht (Units.ext hut ▸ hu)
    simp_rw [hind]
    rw [lintegral_indicator_const K.isCompact.isClosed.measurableSet, mul_comm]
  -- `tamQuat X = fibMeas X`
  have heq : tamQuat (a : F) (b : F) (quatBoxX ha0' hb0' h (splitBoxW T)) =
      NormalFib.fibMeas (nrdPos (a : F) (b : F)) (nrdPos_surjective ha0' hb0') (muPosA (a : F) (b : F))
        (muTP ha0' hb0' h) (quatBoxX ha0' hb0' h (splitBoxW T)) := by
    rw [htam, hA1, hfib, ← hA2, ← hC]
    ring
  -- positivity and finiteness, from the fibre side
  have hsl := haar_slNbhd_pos_lt_top (muT F)
  rw [slNbhd_eq, muT_box_gauge measurableSet_slNbhdInf] at hsl
  have hK0 : omegaInf F K ≠ 0 := (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have hKT : omegaInf F K ≠ ∞ := K.isCompact.measure_lt_top.ne
  have hU0 : muFinUnits F (OHatUnits F) ≠ 0 := by
    rw [muFinUnits_OHatUnits]; exact (ENNReal.ofReal_pos.2 ohatVol_pos).ne'
  have hUT : muFinUnits F (OHatUnits F) ≠ ∞ := by rw [muFinUnits_OHatUnits]; exact ENNReal.ofReal_ne_top
  have hval : NormalFib.fibMeas (nrdPos (a : F) (b : F)) (nrdPos_surjective ha0' hb0') (muPosA (a : F) (b : F))
        (muTP ha0' hb0' h) (quatBoxX ha0' hb0' h (splitBoxW T)) =
      muFinUnits F (OHatUnits F) * (muGaugeInf F (slNbhdInf F) * finFactorSL2 F) * omegaInf F K := by
    rw [hfib, hG]; ring
  have h0 : tamQuat (a : F) (b : F) (quatBoxX ha0' hb0' h (splitBoxW T)) ≠ 0 := by
    rw [heq, hval]; exact mul_ne_zero (mul_ne_zero hU0 hsl.1) hK0
  have htop : tamQuat (a : F) (b : F) (quatBoxX ha0' hb0' h (splitBoxW T)) ≠ ∞ := by
    rw [heq, hval]; exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hUT hsl.2) hKT
  exact map_muSL1_eq_muT_of_box (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0' h h0 htop heq.symm

/-- **$\tau(\mathrm{SL}_1(D)) = 1$ for split $D$** (unconditional). -/
@[kb "weil1982" "§3.7 (τ(SL₁(D)) = 1, here τ(SL₂) = 1) [unverified page]"]
theorem tamagawa_SL1_split {x y : F} (a b : 𝓞 F) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (h : x ^ 2 - (a : F) * y ^ 2 = (b : F)) :
    covolume (SL1F (a : F) (b : F)) (SL1A (a : F) (b : F))
      (muSL1 (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)) = 1 :=
  covolume_muSL1_eq_one_of_map_eq_muT ha0 hb0 h (map_muSL1_eq_muT_of_split a b ha0 hb0 h)

set_option maxHeartbeats 2000000 in
/-- **The input `TauSL1EqOne` holds for every quaternion algebra** $\mathbb H[F,a,b]$ over every number field: by
the residue computation for division algebras and by `tamagawa_SL1_split` otherwise. -/
@[kb "weil1982" "§3.7 (τ(SL₁(D)) = 1) [unverified page]"]
theorem tauSL1EqOne (a b : 𝓞 F) : TauSL1EqOne a b := by
  by_cases hdiv : ∀ ξ : QuaternionAlgebra F (a : F) 0 (b : F), ξ ≠ 0 → IsUnit ξ
  · exact tauSL1EqOne_of_division a b hdiv
  · refine ⟨fun ha0 hb0 => ?_⟩
    obtain ⟨x, y, h⟩ := exists_norm_eq_of_not_division (a : F) (b : F) two_ne_zero (by simpa using ha0)
      (by simpa using hb0) hdiv
    exact tamagawa_SL1_split a b ha0 hb0 h

end QuadFormsKB.Tamagawa.Measure.Weil
