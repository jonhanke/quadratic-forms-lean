/-
# $\mu_{\mathrm{SL}_1}(H_S\cap\mathrm{SL}_1)$ from the two fibrations of `tamQuat`

**Layer:** a totally real number field $L$ (used below for $L = K = F(\sqrt d)$), $\alpha,\beta\in\mathcal O_L\setminus0$ with
$-\alpha,-\beta\gg0$ ($D' = (\alpha,\beta)_L$ totally definite), a finite set $S$ of places and levels $m_w$;
$H_S = \{x : x_w\in\Lambda_w^\times\ (w\notin S),\ x_w\in\Lambda^{(m_w)}_w\ (w\in S)\}$ (`HS`).

* **`nL`**: $\operatorname{nrd}(\Lambda^{(m_w)}_w)\subseteq L_w^\times$; **`NH`** = `ideleBox S nL`.
* **`nrd_image_HS`**: $\operatorname{nrd}(H_S)\cap\mathrm{Bset} = \{t : t_\infty\in\mathrm{BInf},\ t_f\in N_H\}$.
* **`tamQuat_XH_eq`** (reduced-norm fibration): $\mathrm{tamQuat}(X_H) = \mu_{\mathrm{SL}_1}(H_S\cap\mathrm{SL}_1)\cdot\omega_\infty(\mathrm{BInf})\,\mu_f(N_H)$.
* **`muSL1N_HS_mul`** (with the centre fibration `tamQuat_sqX`):
  $$\mu_{\mathrm{SL}_1}(H_S\cap\mathrm{SL}_1)\cdot\mu_f(N_H) = \mu_f(\hat{\mathcal O}^\times)\cdot\mu_{PD}(\operatorname{pd}H_S),$$
  so $\mu_{\mathrm{SL}_1}(H_S\cap\mathrm{SL}_1)$ is expressed through the measure $\mu_{PD}$ and local volumes only (the archimedean shell of
  $(D'\otimes L_\infty)^\times$ cancels).

Source: Weil 1982, §2.4, Thm 2.4.4; §3.7 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSHaar

open Matrix NumberField NumberField.InfinitePlace IsDedekindDomain WithZero MeasureTheory Set Filter Function
open scoped ENNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices LerayPadic

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}
  (S : Finset (HeightOneSpectrum (𝓞 F))) (m : HeightOneSpectrum (𝓞 F) → ℕ) (hm1 : ∀ v, 1 ≤ m v)

/-! ### The reduced-norm image of $\Lambda^{(m)}_v$ -/

variable (a b) in
/-- $\operatorname{nrd}(\Lambda^{(m_v)}_v)\subseteq F_v^\times$. -/
def nL (v : HeightOneSpectrum (𝓞 F)) : Set (v.adicCompletion F)ˣ :=
  nrdLocUnit _ _ '' (lamCong v a b (m v) (hm1 v) : Set (QuatV (a : F) (b : F) v)ˣ)

theorem lamCong_subset (v : HeightOneSpectrum (𝓞 F)) :
    (lamCong v a b (m v) (hm1 v) : Set (QuatV (a : F) (b : F) v)ˣ) ⊆ lamLocUnits (a : F) (b : F) v :=
  fun _ hx => (Subgroup.mem_inf.1 hx).2

theorem isCompact_lamCong (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (lamCong v a b (m v) (hm1 v) : Set (QuatV (a : F) (b : F) v)ˣ) :=
  (isCompact_lamLocUnits _ _ v).of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ (isOpen_lamCong v (m v) (hm1 v))) (lamCong_subset m hm1 v)

theorem measurableSet_nL (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (nL a b m hm1 v) :=
  ((isCompact_lamCong m hm1 v).image (continuous_nrdLocUnit _ _)).isClosed.measurableSet

theorem nL_subset (v : HeightOneSpectrum (𝓞 F)) : nL a b m hm1 v ⊆ unitsVSub v := by
  rintro _ ⟨y, hy, rfl⟩
  have := ((mem_lamLocUnits_iff (fun w => valued_algebraMap_le_one a w) (fun w => valued_algebraMap_le_one b w) y).1
    (lamCong_subset m hm1 v hy)).2
  exact this

variable (a b) in
/-- $N_H = \{t_f : t_v\in\mathcal O_v^\times\ (v\notin S),\ t_v\in\operatorname{nrd}\Lambda^{(m_v)}_v\ (v\in S)\}$. -/
def NH : Set (FiniteAdeleRing (𝓞 F) F)ˣ := ideleBox S (nL a b m hm1)

theorem NH_subset_OHatUnits : NH a b S m hm1 ⊆ (OHatUnits F : Set (FiniteAdeleRing (𝓞 F) F)ˣ) := by
  intro g hg
  rw [← ideleBox_empty (nL a b m hm1)]
  intro v
  have := hg v
  simp only [Finset.notMem_empty, ite_false]
  split_ifs at this with hv
  · exact nL_subset m hm1 v this
  · exact this

theorem measurableSet_NH : MeasurableSet (NH a b S m hm1) :=
  measurableSet_ideleBox S _ fun v _ => measurableSet_nL m hm1 v

/-! ### The reduced-norm image of $H_S$ -/

/-- **$\operatorname{nrd}(H_S)\cap\mathrm{Bset} = \{t : t_\infty\in\mathrm{BInf},\ t_f\in N_H\}$.** -/
theorem nrd_image_HS [IsTotallyReal F]
    (hS : ∀ v ∉ S, Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1) :
    nrdUnit '' (HS a b S m hm1 : Set (QuatAdele (a : F) (b : F))ˣ) ∩ Bset =
      idelesEquiv F ⁻¹' ((BInf (F := F)) ×ˢ NH a b S m hm1) := by
  have := isEmpty_complex (F := F)
  ext t
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hB⟩
    have hx' := (mem_HS a b S m hm1).1 hx
    refine ⟨(hB : _).1, fun v => ?_⟩
    have hval : ((unitAt ((idelesEquiv F) (nrdUnit x)).2 v : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        nrdLoc _ _ ((unitAtA (a : F) (b : F) v x : (QuatV (a : F) (b : F) v)ˣ) : QuatV (a : F) (b : F) v) := by
      rw [nrdLoc_eq_nrd, nrd_unitAtA]; rfl
    split_ifs with hv
    · refine ⟨unitAtA (a : F) (b : F) v x, hx'.2 v hv, Units.ext ?_⟩
      rw [nrdLocUnit_val, ← hval]
    · show Valued.v ((unitAt ((idelesEquiv F) (nrdUnit x)).2 v : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1
      rw [hval]
      exact ((mem_lamLocUnits_iff (fun w => valued_algebraMap_le_one a w)
        (fun w => valued_algebraMap_le_one b w) _).1 (hx'.1 v)).2
  · rintro ⟨hinf, hfin⟩
    have hloc : ∀ v, ∃ y : (QuatV (a : F) (b : F) v)ˣ, y ∈ lamLocUnits (a : F) (b : F) v ∧
        nrdLoc _ _ (y : QuatV (a : F) (b : F) v) = (t : Adeles F).2 v ∧
          (v ∈ S → y ∈ lamCong v a b (m v) (hm1 v)) := by
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
    have htw : ∀ w, 0 < (t : Adeles F).1.1 w := fun w => lt_of_lt_of_le one_pos (hinf w).1
    set βR : ∀ w : {w : InfinitePlace F // w.IsReal},
        (ℍ[ℝ, embedding_of_isReal w.2 (a : F), embedding_of_isReal w.2 (b : F)])ˣ := fun w =>
      Units.map (algebraMap ℝ _).toMonoidHom (Units.mk0 (Real.sqrt ((t : Adeles F).1.1 w))
        (Real.sqrt_pos.2 (htw w)).ne')
    refine ⟨⟨mkAdeleUnit (a : F) (b : F) βR (fun w => isEmptyElim w) y (Eventually.of_forall hyL), ?_, ?_⟩, ?_⟩
    · rw [SetLike.mem_coe, mem_HS]
      refine ⟨fun v => by rw [unitAtA_mkAdeleUnit]; exact hyL v, fun v hv => ?_⟩
      rw [unitAtA_mkAdeleUnit]; exact hyS v hv
    · refine nrdUnit_mkAdeleUnit_eq t βR _ y _ (fun w => ?_) hyt
      rw [nrd_scalarR, Units.val_mk0, Real.sq_sqrt (htw w).le]
    · exact ⟨hinf, NH_subset_OHatUnits S m hm1 hfin⟩

/-! ### The reduced-norm fibration on $X_H$ -/

set_option maxHeartbeats 1600000 in
/-- **The reduced-norm fibration on $X_H$.** -/
theorem tamQuat_XH_eq [IsTotallyReal F] (ha : a ≠ 0) (hb : b ≠ 0)
    (hS : ∀ v ∉ S, Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1) :
    tamQuat (a : F) (b : F) (sqX (HS a b S m hm1) Bset) =
      muSL1N ha hb {x : (nrdHom (a : F) (b : F)).ker | (x : (QuatAdele (a : F) (b : F))ˣ) ∈ HS a b S m hm1} *
        (omegaInf F BInf * muFinUnits F (NH a b S m hm1)) := by
  have ha' : (a : F) ≠ 0 := by simpa using ha
  have hb' : (b : F) ≠ 0 := by simpa using hb
  have := isHaarMeasure_muSL1P (valued_coe_le_one a) (valued_coe_le_one b) ha' hb'
  have hHo : IsOpen (HS a b S m hm1 : Set (QuatAdele (a : F) (b : F))ˣ) :=
    (isOpen_quatCongS S m hm1).preimage (continuous_quatFinPart a b)
  have hXm : MeasurableSet (sqX (HS a b S m hm1) Bset) := measurableSet_sqX _ hHo measurableSet_Bset
  have hNm : MeasurableSet (idelesEquiv F ⁻¹' ((BInf (F := F)) ×ˢ NH a b S m hm1)) :=
    (measurableSet_BInf.prod (measurableSet_NH S m hm1)).preimage (idelesEquiv F).continuous.measurable
  set X : Set (posA (a : F) (b : F)) := Subtype.val ⁻¹' (idelesEquiv F ⁻¹' ((BInf (F := F)) ×ˢ NH a b S m hm1))
    with hX
  have hXmeas : MeasurableSet X := hNm.preimage measurable_subtype_coe
  have himg := nrd_image_HS S m hm1 hS (a := a) (b := b)
  have hcE : muSL1P (valued_coe_le_one a) (valued_coe_le_one b) ha' hb'
      {k : (nrdPos (a : F) (b : F)).ker | (k : (QuatAdele (a : F) (b : F))ˣ) ∈ HS a b S m hm1} =
      muSL1N ha hb {x : (nrdHom (a : F) (b : F)).ker | (x : (QuatAdele (a : F) (b : F))ˣ) ∈ HS a b S m hm1} := by
    exact (muSL1P_eq_muSL1 ha hb _ hHo.measurableSet).trans (muSL1N_eq_muSL1 ha hb _ hHo.measurableSet).symm
  rw [← fibMeas_nrdPos (valued_coe_le_one a) (valued_coe_le_one b) ha' hb', ← tamIdeles_prod]
  rw [fibMeas_apply_of_kern _ _ measurable_nrdPos _ _ hXm hXmeas
    (muSL1P (valued_coe_le_one a) (valued_coe_le_one b) ha' hb'
      {k : (nrdPos (a : F) (b : F)).ker | (k : (QuatAdele (a : F) (b : F))ˣ) ∈ HS a b S m hm1}) ?_ ?_, hcE]
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
    have hq' : (q : (Adeles F)ˣ) ∈ nrdUnit '' (HS a b S m hm1 : Set (QuatAdele (a : F) (b : F))ˣ) ∩ Bset := by
      rw [himg]; exact hq
    obtain ⟨⟨x, hx, hxq⟩, hB⟩ := hq'
    refine ⟨x, Subtype.ext hxq, ?_⟩
    rw [NormalFib.fibK_apply _ _ _ hXm]
    refine Eq.trans ?_ (muSL1P_eq_muSL1 ha hb _ hHo.measurableSet).symm
    rw [muSL1P, Measure.map_apply (map_continuous (kerPosEquiv (a : F) (b : F)).symm).measurable
        (hXm.preimage (NormalFib.measurable_mul_val _ _))]
    congr 1
    ext z
    simp only [mem_preimage, sqX, mem_setOf_eq, coe_kerPosEquiv_symm, SetLike.mem_coe]
    rw [(HS a b S m hm1).mul_mem_cancel_left hx, nrdUnit_mul, mem_SL1A.1 z.2, mul_one, hxq]
    exact and_iff_left hB
  · intro x hx
    rw [NormalFib.fibK_apply _ _ _ hXm]
    convert measure_empty (μ := muSL1P (valued_coe_le_one a) (valued_coe_le_one b) ha' hb')
    ext k
    simp only [mem_preimage, sqX, mem_setOf_eq, mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2⟩
    apply hx
    have : (nrdPos (a : F) (b : F) x : (Adeles F)ˣ) ∈
        nrdUnit '' (HS a b S m hm1 : Set (QuatAdele (a : F) (b : F))ˣ) ∩ Bset := by
      refine ⟨⟨_, h1, ?_⟩, ?_⟩
      · rw [coe_nrdPos, nrdUnit_mul, mem_ker_nrdPos.1 k.2, mul_one]
      · rwa [nrdUnit_mul, mem_ker_nrdPos.1 k.2, mul_one] at h2
    rw [himg] at this
    exact this

/-! ### Both fibrations together -/

set_option maxHeartbeats 1600000 in
/-- **$\mu_{\mathrm{SL}_1}(H_S\cap\mathrm{SL}_1)\cdot\mu_f(N_H) = \mu_f(\hat{\mathcal O}^\times)\cdot\mu_{PD}(\operatorname{pd}H_S)$** (totally
definite $D$ over a totally real field). -/
@[kb "weil1982" "§2.4, Thm 2.4.4; §3.7 [unverified page]"]
theorem muSL1N_HS_mul [IsTotallyReal F] (ha : a ≠ 0) (hb : b ≠ 0) (hna : IsTotallyPos (-(a : F)))
    (hnb : IsTotallyPos (-(b : F)))
    (hS : ∀ v ∉ S, Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1) :
    muSL1N ha hb {x : (nrdHom (a : F) (b : F)).ker | (x : (QuatAdele (a : F) (b : F))ˣ) ∈ HS a b S m hm1} *
        muFinUnits F (NH a b S m hm1) =
      muFinUnits F (OHatUnits F) *
        muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha) (by simpa using hb)
          (pdMk (a : F) (b : F) '' (HS a b S m hm1 : Set (QuatAdele (a : F) (b : F))ˣ)) := by
  have hHo : IsOpen (HS a b S m hm1 : Set (QuatAdele (a : F) (b : F))ˣ) :=
    (isOpen_quatCongS S m hm1).preimage (continuous_quatFinPart a b)
  set W := omegaInf F (BInf (F := F))
  set U := muFinUnits F (OHatUnits F)
  have hW0 : W ≠ 0 := omegaInf_BInf_ne_zero
  have hWt : W ≠ ∞ := omegaInf_BInf_ne_top
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
  have h2 := tamQuat_sqX ha hb (HS a b S m hm1) hHo measurableSet_Bset (W * U) hc
  have h5 := tamQuat_XH_eq S m hm1 ha hb hS
  refine (ENNReal.mul_right_inj hW0 hWt).1 ?_
  calc W * (_ * muFinUnits F (NH a b S m hm1)) = tamQuat (a : F) (b : F) (sqX (HS a b S m hm1) Bset) := by
        rw [h5]; ring
    _ = _ := by rw [h2]; ring

end QuadFormsKB.Tamagawa.Measure.Weil

end
