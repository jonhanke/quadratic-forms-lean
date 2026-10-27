import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqArchP
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSSL1

/-!
# The $\mathrm{SL}_1$ factor of the non-square model on a cone test set

**Layer:** $F$ any number field, $D = \mathbb H[F,a,b]$ any quaternion algebra. The analogue of `muSL1N_Eset_mul` with the finite
part `econgS` (norm image `NE S m`) replaced by the congruence subgroup `quatCongS` (norm image `NH a b S m hm1`).

* **`Hcone`**: $\{x : x_w\in\mathrm{cone}(T_w,A_w)\ \forall w\mid\infty,\ x_f\in\texttt{quatCongS}\}$.
* **`muSL1N_Hcone_mul`**:
  $\mu_{\mathrm{SL}_1}(H\cap\mathrm{SL}_1)\cdot\omega_\infty(N)\,\mu_f(N_H) = \omega^{D^\times}_\infty(Y)\cdot\mu_{D^\times}(\texttt{quatCongS})$.
-/

open MeasureTheory Measure Set Function NumberField NumberField.InfinitePlace NumberField.mixedEmbedding IsDedekindDomain WithZero
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure.ArchPolar LerayPadic

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}
  (S : Finset (HeightOneSpectrum (𝓞 F))) (m : HeightOneSpectrum (𝓞 F) → ℕ) (hm1 : ∀ v, 1 ≤ m v)
  (TR : {w : InfinitePlace F // w.IsReal} → Set ℝ)
  (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (SphereLeray.Sph (QRe (qSq a b) w) 1))
  (TC : {w : InfinitePlace F // w.IsComplex} → Set ℂˣ)
  (AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (SphereLerayC.SphC (QCx (qSq a b) w) 1))

/-- **The test set** $H = \{x : x_\infty\in Y,\ x_f\in\texttt{quatCongS}\}$. -/
def Hcone : Set (QuatAdele (a : F) (b : F))ˣ :=
  quatUnitsEquiv (a : F) (b : F) ⁻¹'
    (archCone (a := (a : F)) (b := (b : F)) (fun w => QRe (qSq a b) w) (fun w => QCx (qSq a b) w) TR AR TC AC ×ˢ
      (quatCongS a b S m hm1 : Set (QuatFin (a : F) (b : F))ˣ))

theorem mem_Hcone {x : (QuatAdele (a : F) (b : F))ˣ} :
    x ∈ Hcone S m hm1 TR AR TC AC ↔
      (∀ w, qVec ((unitAtR (a : F) (b : F) w x : (HRe a b w)ˣ) : HRe a b w) ∈ coneR (QRe (qSq a b) w) (TR w) (AR w)) ∧
      (∀ w, qVec ((unitAtC (a : F) (b : F) w x : (HCx a b w)ˣ) : HCx a b w) ∈ coneC (QCx (qSq a b) w) (TC w) (AC w)) ∧
      quatFinPart a b x ∈ quatCongS a b S m hm1 := by
  simp only [qVec_unitAtR, qVec_unitAtC]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

theorem measurableSet_Hcone (hTRm : ∀ w, MeasurableSet (TR w)) (hARm : ∀ w, MeasurableSet (AR w))
    (hTCm : ∀ w, MeasurableSet (TC w)) (hTh : ∀ w, TC w ⊆ SphereLerayC.halfU) (hACm : ∀ w, MeasurableSet (AC w)) :
    MeasurableSet (Hcone S m hm1 TR AR TC AC) :=
  (((measurableSet_archConeSet (a := (a : F)) (b := (b : F)) _ _ TR AR TC AC hTRm hARm hTCm hTh hACm).preimage
    Units.continuous_val.measurable).prod (isOpen_quatCongS S m hm1).measurableSet).preimage
      (quatUnitsEquiv (a : F) (b : F)).continuous.measurable

theorem finPart_nrd_mem_NH {x : (QuatAdele (a : F) (b : F))ˣ}
    (hx : x ∈ HS a b S m hm1) : finPart (nrdUnit x) ∈ NH a b S m hm1 := by
  have hx' := (mem_HS a b S m hm1).1 hx
  intro v
  have hval : ((unitAt (finPart (nrdUnit x)) v : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      nrdLoc _ _ ((unitAtA (a : F) (b : F) v x : (QuatV (a : F) (b : F) v)ˣ) : QuatV (a : F) (b : F) v) := by
    rw [nrdLoc_eq_nrd, nrd_unitAtA]; rfl
  split_ifs with hv
  · refine ⟨unitAtA (a : F) (b : F) v x, hx'.2 v hv, Units.ext ?_⟩
    rw [nrdLocUnit_val, ← hval]
  · show Valued.v ((unitAt (finPart (nrdUnit x)) v : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1
    rw [hval]
    exact ((mem_lamLocUnits_iff (fun w => valued_algebraMap_le_one a w)
      (fun w => valued_algebraMap_le_one b w) _).1 (hx'.1 v)).2

theorem exists_local_cong
    (hS : ∀ v ∉ S, Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1)
    (t : (Adeles F)ˣ) (hfin : finPart t ∈ NH a b S m hm1) :
    ∃ y : ∀ v : HeightOneSpectrum (𝓞 F), (QuatV (a : F) (b : F) v)ˣ,
      (∀ v, y v ∈ lamLocUnits (a : F) (b : F) v) ∧
      (∀ v, nrdLoc _ _ ((y v : (QuatV (a : F) (b : F) v)ˣ) : QuatV (a : F) (b : F) v) = (t : Adeles F).2 v) ∧
      (∀ v ∈ S, y v ∈ lamCong v a b (m v) (hm1 v)) := by
  have hloc : ∀ v, ∃ y : (QuatV (a : F) (b : F) v)ˣ, y ∈ lamLocUnits (a : F) (b : F) v ∧
      nrdLoc _ _ (y : QuatV (a : F) (b : F) v) = (t : Adeles F).2 v ∧ (v ∈ S → y ∈ lamCong v a b (m v) (hm1 v)) := by
    intro v
    have h := hfin v
    by_cases hv : v ∈ S
    · rw [if_pos hv] at h
      obtain ⟨y, hy, hyt⟩ := h
      refine ⟨y, lamCong_subset m hm1 v hy, ?_, fun _ => hy⟩
      rw [← nrdLocUnit_val, hyt]; rfl
    · rw [if_neg hv] at h
      obtain ⟨y, hy, hyt⟩ := exists_lamLocUnits_nrd v (a := a) (b := b) (hS v hv).1 (hS v hv).2.1
        (show Valued.v ((t : Adeles F).2 v) = 1 from h)
      exact ⟨y, hy, hyt, fun h' => absurd h' hv⟩
  choose y hyL hyt hyS using hloc
  exact ⟨y, hyL, hyt, hyS⟩

/-- **The reduced norm of the test set** lies in $N\times N_H$. -/
theorem nrd_mem_of_mem_Hcone {x : (QuatAdele (a : F) (b : F))ˣ}
    (hx : x ∈ Hcone S m hm1 TR AR TC AC) :
    nrdUnit x ∈ idelesEquiv F ⁻¹' (nrdShell F TR TC ×ˢ NH a b S m hm1) := by
  obtain ⟨hR, hC, hf⟩ := (mem_Hcone S m hm1 TR AR TC AC).1 hx
  refine ⟨⟨fun w => ?_, fun w => ?_⟩, finPart_nrd_mem_NH S m hm1 hf⟩
  · obtain ⟨⟨t, p⟩, ⟨ht, -⟩, hp⟩ := hR w
    refine ⟨t, ht, ?_⟩
    change Real.exp (2 * t) = ((nrdUnit x : (Adeles F)ˣ) : Adeles F).1.1 w
    rw [← eval_qVec_unitAtR, ← hp, SphereLeray.eval_pol, mul_one]
  · obtain ⟨⟨β, p⟩, ⟨hβ, -⟩, hp⟩ := hC w
    refine ⟨β, ⟨β, hβ, rfl⟩, ?_⟩
    change (β : ℂ) ^ 2 = ((nrdUnit x : (Adeles F)ˣ) : Adeles F).1.2 w
    rw [← eval_qVec_unitAtC, ← hp, SphereLerayC.eval_polC, mul_one]

set_option maxHeartbeats 1600000 in
/-- **The reduced-norm fibration of `tamQuat` on the test set `Hcone`**:
$\mu_{\mathrm{SL}_1}(H\cap\mathrm{SL}_1)\cdot\omega_\infty(N)\,\mu_f(N_H) = \omega^{D^\times}_\infty(Y)\cdot\mu_{D^\times}(\texttt{quatCongS})$
(every number field, every quaternion algebra). -/
theorem muSL1N_Hcone_mul (ha : a ≠ 0) (hb : b ≠ 0)
    (hS : ∀ v ∉ S, Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1)
    (hTRm : ∀ w, MeasurableSet (TR w)) (hARm : ∀ w, MeasurableSet (AR w))
    (hTCm : ∀ w, MeasurableSet (TC w)) (hTh : ∀ w, TC w ⊆ SphereLerayC.halfU) (hACm : ∀ w, MeasurableSet (AC w))
    (h0 : ∀ w, (0 : ℝ) ∈ TR w) (h1 : ∀ w, (1 : ℂˣ) ∈ TC w) :
    muSL1N ha hb {x : (nrdHom (a : F) (b : F)).ker | (x : (QuatAdele (a : F) (b : F))ˣ) ∈ Hcone S m hm1 TR AR TC AC} *
        (omegaInf F (nrdShell F TR TC) * muFinUnits F (NH a b S m hm1)) =
      omegaQuatInf (a : F) (b : F)
          (archCone (a := (a : F)) (b := (b : F)) (fun w => QRe (qSq a b) w) (fun w => QCx (qSq a b) w) TR AR TC AC) *
        muFinQuat (a : F) (b : F) (quatCongS a b S m hm1) := by
  have ha' : (a : F) ≠ 0 := by simpa using ha
  have hb' : (b : F) ≠ 0 := by simpa using hb
  have := isHaarMeasure_muSL1P (valued_coe_le_one a) (valued_coe_le_one b) ha' hb'
  have hEm := measurableSet_Hcone S m hm1 TR AR TC AC hTRm hARm hTCm hTh hACm
  have hNm : MeasurableSet (idelesEquiv F ⁻¹' (nrdShell F TR TC ×ˢ NH a b S m hm1)) :=
    (((measurableSet_shellSet (F := F) hTRm hTCm hTh).preimage Units.continuous_val.measurable).prod
      (measurableSet_NH m hm1 (S := S))).preimage (idelesEquiv F).continuous.measurable
  set X : Set (posA (a : F) (b : F)) := Subtype.val ⁻¹' (idelesEquiv F ⁻¹' (nrdShell F TR TC ×ˢ NH a b S m hm1)) with hX
  have hXmeas : MeasurableSet X := hNm.preimage measurable_subtype_coe
  have hkey : ∀ q ∈ X, ∃ x₀ : (QuatAdele (a : F) (b : F))ˣ, nrdPos (a : F) (b : F) x₀ = q ∧
      ∀ k : (QuatAdele (a : F) (b : F))ˣ, nrdUnit k = 1 →
        (x₀ * k ∈ Hcone S m hm1 TR AR TC AC ↔ k ∈ Hcone S m hm1 TR AR TC AC) := by
    intro q hq
    obtain ⟨⟨hqR, hqC⟩, hqf⟩ := hq
    choose s hs hs' using hqR
    choose β hβ using hqC
    obtain ⟨y, hyL, hyt, hyS⟩ := exists_local_cong S m hm1 hS (q : (Adeles F)ˣ) hqf
    set βR : ∀ w : {w : InfinitePlace F // w.IsReal}, (HRe a b w)ˣ := fun w =>
      Units.map (algebraMap ℝ (HRe a b w)).toMonoidHom (Units.mk0 (Real.exp (s w)) (Real.exp_pos _).ne')
    have hβ0 : ∀ w, ((β w : ℂ)) ≠ 0 := fun w => by
      obtain ⟨⟨γ, -, hγ⟩, -⟩ := hβ w; rw [← hγ]; exact γ.ne_zero
    set βC : ∀ w : {w : InfinitePlace F // w.IsComplex}, (HCx a b w)ˣ := fun w =>
      Units.map (algebraMap ℂ (HCx a b w)).toMonoidHom (Units.mk0 (β w) (hβ0 w))
    refine ⟨mkAdeleUnit (a : F) (b : F) βR βC y (Filter.Eventually.of_forall hyL), Subtype.ext ?_, fun k hk => ?_⟩
    · refine nrdUnit_mkAdeleUnit_eq_gen _ βR βC y _ (fun w => ?_) (fun w => ?_) hyt
      · change nrd (algebraMap ℝ (HRe a b w) (Real.exp (s w))) = _
        rw [nrd_algebraMap_quat]
        exact (by rw [← Real.exp_nat_mul]; push_cast; ring_nf : Real.exp (s w) ^ 2 = Real.exp (2 * s w)).trans (hs' w)
      · change nrd (algebraMap ℂ (HCx a b w) (β w)) = _
        rw [nrd_algebraMap_quat]; exact (hβ w).2
    · rw [mem_Hcone, mem_Hcone]
      refine and_congr (forall_congr' fun w => ?_) (and_congr (forall_congr' fun w => ?_) ?_)
      · rw [map_mul, unitAtR_mkAdeleUnit, Units.val_mul]
        change qVec (algebraMap ℝ (HRe a b w) (Real.exp (s w)) * _) ∈ _ ↔ _
        rw [qVec_algebraMap_mul]
        have e1 := mem_coneR_smul_iff (A := AR w) (hs w) (sphPtOfR w k hk)
        have e2 := mem_coneR_smul_iff (A := AR w) (h0 w) (sphPtOfR w k hk)
        rw [Real.exp_zero, one_smul] at e2
        exact e1.trans e2.symm
      · rw [map_mul, unitAtC_mkAdeleUnit, Units.val_mul]
        change qVec (algebraMap ℂ (HCx a b w) (β w) * _) ∈ _ ↔ _
        rw [qVec_algebraMap_mul]
        obtain ⟨⟨γ, hγT, hγ⟩, -⟩ := hβ w
        have hβw : (β w : ℂ) = (γ : ℂ) := hγ.symm
        have e1 := mem_coneC_iff (QCx (qSq a b) w) (A := AC w) (hTh w) (hTh w hγT) (sphPtOfC w k hk)
        have e2 := mem_coneC_iff (QCx (qSq a b) w) (A := AC w) (hTh w) (hTh w (h1 w)) (sphPtOfC w k hk)
        rw [Units.val_one, one_smul] at e2
        rw [hβw]
        exact (e1.trans (and_iff_right hγT)).trans ((and_iff_right (h1 w)).symm.trans e2.symm)
      · rw [map_mul]
        have hx₀ : quatFinPart a b (mkAdeleUnit (a : F) (b : F) βR βC y (Filter.Eventually.of_forall hyL)) ∈
            quatCongS a b S m hm1 := by
          rw [mem_quatCongS]
          refine ⟨fun v => ?_, fun v hv => ?_⟩
          · change unitAtA _ _ v _ ∈ _; rw [unitAtA_mkAdeleUnit]; exact hyL v
          · change unitAtA _ _ v _ ∈ _; rw [unitAtA_mkAdeleUnit]; exact hyS v hv
        exact (quatCongS a b S m hm1).mul_mem_cancel_left hx₀
  have hcE : muSL1P (valued_coe_le_one a) (valued_coe_le_one b) ha' hb'
      {k : (nrdPos (a : F) (b : F)).ker | (k : (QuatAdele (a : F) (b : F))ˣ) ∈ Hcone S m hm1 TR AR TC AC} =
      muSL1N ha hb {x : (nrdHom (a : F) (b : F)).ker | (x : (QuatAdele (a : F) (b : F))ˣ) ∈ Hcone S m hm1 TR AR TC AC} :=
    (muSL1P_eq_muSL1 ha hb _ hEm).trans (muSL1N_eq_muSL1 ha hb _ hEm).symm
  have hT : tamQuat (a : F) (b : F) (Hcone S m hm1 TR AR TC AC) =
      omegaQuatInf (a : F) (b : F)
          (archCone (a := (a : F)) (b := (b : F)) (fun w => QRe (qSq a b) w) (fun w => QCx (qSq a b) w) TR AR TC AC) *
        muFinQuat (a : F) (b : F) (quatCongS a b S m hm1) := tamQuat_prod _ _
  rw [← hT, ← tamIdeles_prod, ← fibMeas_nrdPos (valued_coe_le_one a) (valued_coe_le_one b) ha' hb']
  rw [fibMeas_apply_of_kern _ _ measurable_nrdPos _ _ hEm hXmeas
    (muSL1P (valued_coe_le_one a) (valued_coe_le_one b) ha' hb'
      {k : (nrdPos (a : F) (b : F)).ker | (k : (QuatAdele (a : F) (b : F))ˣ) ∈ Hcone S m hm1 TR AR TC AC}) ?_ ?_, hcE]
  · congr 1
    symm
    rw [muPosA, measurableEmbedding_posA.comap_apply]
    congr 1
    ext t
    constructor
    · rintro ⟨q, hq, rfl⟩; exact hq
    · intro h
      have hR : ∀ w, ((idelesEquiv F t).1 : mixedSpace F).1 w ∈ (fun s : ℝ => Real.exp (2 * s)) '' TR w := h.1.1
      have hpos : t ∈ posA (a : F) (b : F) := fun w hw _ => by
        obtain ⟨s, -, hs⟩ := hR ⟨w, hw⟩
        change 0 < ((t : Adeles F)).1.1 ⟨w, hw⟩
        rw [show ((t : Adeles F)).1.1 ⟨w, hw⟩ = Real.exp (2 * s) from hs.symm]
        exact Real.exp_pos _
      exact ⟨⟨t, hpos⟩, h, rfl⟩
  · intro q hq
    obtain ⟨x₀, hx₀, hk⟩ := hkey q hq
    refine ⟨x₀, hx₀, ?_⟩
    rw [NormalFib.fibK_apply _ _ _ hEm]
    congr 1
    ext k
    exact hk k ((mem_ker_nrdPos).1 k.2)
  · intro x hx
    rw [NormalFib.fibK_apply _ _ _ hEm]
    convert measure_empty (μ := muSL1P (valued_coe_le_one a) (valued_coe_le_one b) ha' hb')
    ext k
    simp only [mem_preimage, mem_empty_iff_false, iff_false]
    intro hxk
    apply hx
    have h := nrd_mem_of_mem_Hcone S m hm1 TR AR TC AC hxk
    rw [nrdUnit_mul, mem_ker_nrdPos.1 k.2, mul_one] at h
    exact h

end QuadFormsKB.Tamagawa.Measure.Weil

end
