/-
# $\mu_P(\Phi^{-1}K')$ in terms of $\mu^{SO(D^0)}_{\mathrm{Tam}}$ and local volumes

**Layer:** a totally real number field $F$, $a, b\in\mathcal O_F\setminus0$ with $-a, -b\gg0$; $S$, $m_v$ as in `GnatSqImage.lean`
with moreover $s_v < m_v$.

* **`tamQuat_XE_eq`**: $\mathrm{tamQuat}(X_E) = \mu_{\mathrm{SL}_1}(E_S\cap\mathrm{SL}_1)\cdot\omega_\infty(\mathrm{BInf})\cdot\mu_f(N_E)$
  (the reduced-norm fibration `fibMeas_nrdPos` with constant fibres, and `nrd_image_ES`).
* **`muP_boxK_mul`**:
  $$\mu_P(\Phi^{-1}K')\cdot\mu_f(N_E)\cdot\mu_{D^\times}(H_S^{\mathrm f}) = \mu_{PD}(\operatorname{pd}H_S)^2\cdot\mu_{D^\times}(E_S^{\mathrm f})\cdot
  \mu_f(\hat{\mathcal O}^\times),$$
  from `muP_sqS0` ($P\cong\mathrm{SL}_1\rtimes PD^\times$), `tamQuat_sqX` and the two boxes $X_H$, $X_E$ (the archimedean shell
  $\omega_{D^\times,\infty}(\mathrm{Sh})$ and $\omega_\infty(\mathrm{BInf})$ cancel).

Source: Weil 1982, §2.4, Thm 2.4.4; §3.7 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqSL1

open Matrix NumberField NumberField.InfinitePlace IsDedekindDomain WithZero MeasureTheory Set Filter Function
open scoped ENNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices LerayPadic

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a b : 𝓞 F}
  (S : Finset (HeightOneSpectrum (𝓞 F))) (m : HeightOneSpectrum (𝓞 F) → ℕ) (hm1 : ∀ v, 1 ≤ m v)

include hm1 in
set_option maxHeartbeats 1600000 in
/-- **The reduced-norm fibration on $X_E$.** -/
theorem tamQuat_XE_eq (ha : a ≠ 0) (hb : b ≠ 0)
    (hS : ∀ v ∉ S, Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1)
    (hsm : ∀ v ∈ S, sExp v < m v) :
    tamQuat (a : F) (b : F) (sqX (ES a b S m) Bset) =
      muSL1N ha hb {x : (nrdHom (a : F) (b : F)).ker | (x : (QuatAdele (a : F) (b : F))ˣ) ∈ ES a b S m} *
        (omegaInf F BInf * muFinUnits F (NE S m)) := by
  have ha' : (a : F) ≠ 0 := by simpa using ha
  have hb' : (b : F) ≠ 0 := by simpa using hb
  have := isHaarMeasure_muSL1P (valued_coe_le_one a) (valued_coe_le_one b) ha' hb'
  have hEo : IsOpen (ES a b S m : Set (QuatAdele (a : F) (b : F))ˣ) :=
    (isOpen_econgS S m hm1).preimage (continuous_quatFinPart a b)
  have hXm : MeasurableSet (sqX (ES a b S m) Bset) := measurableSet_sqX _ hEo measurableSet_Bset
  have hNm : MeasurableSet (idelesEquiv F ⁻¹' ((BInf (F := F)) ×ˢ NE S m)) :=
    (measurableSet_BInf.prod (measurableSet_ideleBox S _ fun v _ => measurableSet_nU m v)).preimage
      (idelesEquiv F).continuous.measurable
  set X : Set (posA (a : F) (b : F)) := Subtype.val ⁻¹' (idelesEquiv F ⁻¹' ((BInf (F := F)) ×ˢ NE S m)) with hX
  have hXmeas : MeasurableSet X := hNm.preimage measurable_subtype_coe
  have himg := nrd_image_ES S m hm1 hS hsm (a := a) (b := b)
  have hcE : muSL1P (valued_coe_le_one a) (valued_coe_le_one b) ha' hb'
      {k : (nrdPos (a : F) (b : F)).ker | (k : (QuatAdele (a : F) (b : F))ˣ) ∈ ES a b S m} =
      muSL1N ha hb {x : (nrdHom (a : F) (b : F)).ker | (x : (QuatAdele (a : F) (b : F))ˣ) ∈ ES a b S m} := by
    exact (muSL1P_eq_muSL1 ha hb _ hEo.measurableSet).trans (muSL1N_eq_muSL1 ha hb _ hEo.measurableSet).symm
  rw [← fibMeas_nrdPos (valued_coe_le_one a) (valued_coe_le_one b) ha' hb', ← tamIdeles_prod]
  rw [fibMeas_apply_of_kern _ _ measurable_nrdPos _ _ hXm hXmeas
    (muSL1P (valued_coe_le_one a) (valued_coe_le_one b) ha' hb'
      {k : (nrdPos (a : F) (b : F)).ker | (k : (QuatAdele (a : F) (b : F))ˣ) ∈ ES a b S m}) ?_ ?_, hcE]
  · congr 1
    rw [muPosA, measurableEmbedding_posA.comap_apply]
    congr 1
    ext t
    constructor
    · rintro ⟨q, hq, rfl⟩; exact hq
    · intro h
      have h' := h
      rw [← himg] at h'
      obtain ⟨⟨x, -, hx⟩, -⟩ := h'
      exact ⟨⟨t, hx ▸ nrdUnit_pos_of_ramified x⟩, h, rfl⟩
  · intro q hq
    have hq' : (q : (Adeles F)ˣ) ∈ nrdUnit '' (ES a b S m : Set (QuatAdele (a : F) (b : F))ˣ) ∩ Bset := by
      rw [himg]; exact hq
    obtain ⟨⟨x, hx, hxq⟩, hB⟩ := hq'
    refine ⟨x, Subtype.ext hxq, ?_⟩
    rw [NormalFib.fibK_apply _ _ _ hXm]
    refine Eq.trans ?_ (muSL1P_eq_muSL1 ha hb _ hEo.measurableSet).symm
    rw [muSL1P, Measure.map_apply (map_continuous (kerPosEquiv (a : F) (b : F)).symm).measurable
        (hXm.preimage (NormalFib.measurable_mul_val _ _))]
    congr 1
    ext z
    simp only [mem_preimage, sqX, mem_setOf_eq, coe_kerPosEquiv_symm, SetLike.mem_coe]
    rw [(ES a b S m).mul_mem_cancel_left hx, nrdUnit_mul, mem_SL1A.1 z.2, mul_one, hxq]
    exact and_iff_left hB
  · intro x hx
    rw [NormalFib.fibK_apply _ _ _ hXm]
    convert measure_empty (μ := muSL1P (valued_coe_le_one a) (valued_coe_le_one b) ha' hb')
    ext k
    simp only [mem_preimage, sqX, mem_setOf_eq, mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2⟩
    apply hx
    have : (nrdPos (a : F) (b : F) x : (Adeles F)ˣ) ∈ nrdUnit '' (ES a b S m : Set (QuatAdele (a : F) (b : F))ˣ) ∩ Bset := by
      refine ⟨⟨_, h1, ?_⟩, ?_⟩
      · rw [coe_nrdPos, nrdUnit_mul, mem_ker_nrdPos.1 k.2, mul_one]
      · rwa [nrdUnit_mul, mem_ker_nrdPos.1 k.2, mul_one] at h2
    rw [himg] at this
    exact this

theorem finPart_nrd_mem_OHat (x : (QuatAdele (a : F) (b : F))ˣ)
    (hx : ∀ v, unitAtA (a : F) (b : F) v x ∈ lamLocUnits (a : F) (b : F) v) :
    finPart (nrdUnit x) ∈ OHatUnits F := by
  rw [finPart_mem_OHatUnits_iff]
  intro v
  rw [← nrd_unitAtA, ← nrdLoc_eq_nrd]
  exact ((mem_lamLocUnits_iff (fun w => valued_algebraMap_le_one a w) (fun w => valued_algebraMap_le_one b w) _).1
    (hx v)).2

include hm1 in
set_option maxHeartbeats 1600000 in
/-- **$\mu_P(\Phi^{-1}K')\cdot\mu_f(N_E)\cdot\mu_{D^\times}(H_S^{\mathrm f}) = \mu_{PD}(\operatorname{pd}H_S)^2\cdot
\mu_{D^\times}(E_S^{\mathrm f})\cdot\mu_f(\hat{\mathcal O}^\times)$** (totally definite $D$). -/
@[kb "weil1982" "§2.4, Thm 2.4.4; §3.7, p. 65 [unverified page]"]
theorem muP_boxK_mul (ha : a ≠ 0) (hb : b ≠ 0) (hna : IsTotallyPos (-(a : F))) (hnb : IsTotallyPos (-(b : F)))
    (hS : ∀ v ∉ S, Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1)
    (hmS : ∀ v ∈ S, 2 * sExp v < m v ∧ sExp v + eExp a ha v ≤ m v) :
    (gnatSqO ha hb).muP (muSq ha hb) (sqPEquiv ha hb ⁻¹' boxK S m hm1) * muFinUnits F (NE S m) *
        muFinQuat (a : F) (b : F) (quatCongS a b S m hm1) =
      muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha) (by simpa using hb)
          (pdMk (a : F) (b : F) '' (HS a b S m hm1 : Set (QuatAdele (a : F) (b : F))ˣ)) ^ 2 *
        muFinQuat (a : F) (b : F) (econgS a b S m) * muFinUnits F (OHatUnits F) := by
  have hdiv := hdiv_of_totallyNeg (F := F) (a := (a : F)) (b := (b : F))
    (fun w hw => emb_neg_of_isTotallyPos_neg hna w hw) (fun w hw => emb_neg_of_isTotallyPos_neg hnb w hw)
  have hsm : ∀ v ∈ S, sExp v < m v := fun v hv => by have := (hmS v hv).1; have := hm1 v; omega
  have hHo : IsOpen (HS a b S m hm1 : Set (QuatAdele (a : F) (b : F))ˣ) :=
    (isOpen_quatCongS S m hm1).preimage (continuous_quatFinPart a b)
  have hEo : IsOpen (ES a b S m : Set (QuatAdele (a : F) (b : F))ˣ) :=
    (isOpen_econgS S m hm1).preimage (continuous_quatFinPart a b)
  have hU0 : muFinUnits F (OHatUnits F) ≠ 0 := by
    rw [muFinUnits_OHatUnits]; exact (ENNReal.ofReal_pos.mpr ohatVol_pos).ne'
  have hUt : muFinUnits F (OHatUnits F) ≠ ∞ := by rw [muFinUnits_OHatUnits]; exact ENNReal.ofReal_ne_top
  set W := omegaInf F (BInf (F := F))
  set U := muFinUnits F (OHatUnits F)
  have hW0 : W ≠ 0 := omegaInf_BInf_ne_zero
  have hWt : W ≠ ∞ := omegaInf_BInf_ne_top
  -- the centre fibre constant
  have hc : ∀ β ∈ HS a b S m hm1, tamIdeles F {u | quatScalar _ _ u ∈ HS a b S m hm1 ∧ u ^ 2 * nrdUnit β ∈ Bset} =
      W * U := by
    intro β hβ
    have hset : {u | quatScalar _ _ u ∈ HS a b S m hm1 ∧ u ^ 2 * nrdUnit β ∈ Bset} =
        {u | finPart u ∈ OHatUnits F ∧ u ^ 2 * nrdUnit β ∈ Bset} := by
      ext u; simp only [mem_setOf_eq, quatScalar_mem_HS_iff S m hm1 ha]
    rw [hset]
    refine tamIdeles_sq_mem_Bset _ (fun w => ?_) (finPart_nrd_mem_OHat β ((mem_HS a b S m hm1).1 hβ).1)
    exact nrdUnit_pos_of_ramified β w.1 w.2 ⟨emb_neg_of_isTotallyPos_neg hna w.1 w.2,
      emb_neg_of_isTotallyPos_neg hnb w.1 w.2⟩
  have h1 := muP_sqS0 ha hb (HS a b S m hm1) (ES a b S m) (HS_normalizes_ES a b S m hm1) hdiv hHo hEo
    measurableSet_Bset (mul_ne_zero hW0 hU0) (ENNReal.mul_ne_top hWt hUt) hc
  rw [← sqPEquiv_preimage_boxK ha hb S m hm1 hS hmS] at h1
  have h2 := tamQuat_sqX ha hb (HS a b S m hm1) hHo measurableSet_Bset (W * U) hc
  have h3 : tamQuat (a : F) (b : F) (sqX (HS a b S m hm1) Bset) =
      omegaQuatInf (a : F) (b : F) (Sh a b) * muFinQuat (a : F) (b : F) (quatCongS a b S m hm1) := by
    rw [sqX_HS_eq, tamQuat_prod]
  have h4 : tamQuat (a : F) (b : F) (sqX (ES a b S m) Bset) =
      omegaQuatInf (a : F) (b : F) (Sh a b) * muFinQuat (a : F) (b : F) (econgS a b S m) := by
    rw [sqX_ES_eq, tamQuat_prod]
  have h5 := tamQuat_XE_eq S m hm1 ha hb hS hsm
  set P := (gnatSqO ha hb).muP (muSq ha hb) (sqPEquiv ha hb ⁻¹' boxK S m hm1)
  set M := muSL1N ha hb {x : (nrdHom (a : F) (b : F)).ker | (x : (QuatAdele (a : F) (b : F))ˣ) ∈ ES a b S m}
  set D := muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha) (by simpa using hb)
    (pdMk (a : F) (b : F) '' (HS a b S m hm1 : Set (QuatAdele (a : F) (b : F))ˣ))
  set N := muFinUnits F (NE S m)
  set qH := muFinQuat (a : F) (b : F) (quatCongS a b S m hm1)
  set qE := muFinQuat (a : F) (b : F) (econgS a b S m)
  set Ω := omegaQuatInf (a : F) (b : F) (Sh a b)
  have e2 : Ω * qH = W * U * D := h3.symm.trans h2
  have e5 : Ω * qE = M * (W * N) := h4.symm.trans h5
  refine (ENNReal.mul_right_inj hW0 hWt).1 ?_
  calc W * (P * N * qH) = D * qH * (M * (W * N)) := by rw [h1]; ring
    _ = D * qE * (Ω * qH) := by rw [← e5]; ring
    _ = W * (D ^ 2 * qE * U) := by rw [e2]; ring

end QuadFormsKB.Tamagawa.Measure.Weil

end
