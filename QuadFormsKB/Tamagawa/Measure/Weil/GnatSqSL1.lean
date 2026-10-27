/-
# The $\mathrm{SL}_1$ factor $\mu_{\mathrm{SL}_1}(E_S\cap\mathrm{SL}_1)$

**Layer:** a totally real number field $F$, $a, b\in\mathcal O_F\setminus0$ with $-a, -b\gg0$ ($D$ totally definite), $S$, $m_v$
as in `GnatSqImage.lean` with moreover $s_v < m_v$.

* `Sh` $\subseteq(D\otimes F_\infty)^\times$: $\operatorname{nrd}x_w\in[1,e^2)$ at every real place; for $x$ with integral finite part,
  $\operatorname{nrd}x\in$ `Bset` iff $x_\infty\in$ `Sh` (`nrd_mem_Bset_iff`), so $X_H = \{x\in H_S : \operatorname{nrd}x\in\mathrm{Bset}\}$ and
  $X_E$ are boxes for `tamQuat` (`tamQuat_XS`).
* **`nrd_image_ES`**: $\operatorname{nrd}(E_S)\cap\mathrm{Bset} = \{t : t_\infty\in\mathrm{BInf},\ t_f\in N_E\}$,
  $N_E = \{t_f : t_v\in\mathfrak o_v^\times\ (v\notin S),\ t_v\in1+\pi^{m_v+s_v}\mathfrak o_v\ (v\in S)\}$ (good places: `exists_sq_sub_mul_sq_eq`; bad places: `exists_sq_eq_near_one`; archimedean: $\sqrt t_w$).
* **`tamQuat_XE_eq`** (the reduced-norm fibration, `fibMeas_nrdPos`): $\mathrm{tamQuat}(X_E) = \mu_{\mathrm{SL}_1}(E_S\cap\mathrm{SL}_1)\cdot
  \omega_\infty(\mathrm{BInf})\cdot\mu_f(N_E)$.

Source: Weil 1982, §2.4, Thm 2.4.4 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqShell
import QuadFormsKB.Tamagawa.Measure.Weil.NrdSurjective

open Matrix NumberField NumberField.InfinitePlace IsDedekindDomain WithZero MeasureTheory Set Filter Function
open scoped ENNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices LerayPadic

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}

/-! ### The archimedean shell of $(D\otimes F_\infty)^\times$ -/

variable (a b) in
/-- $\{x_\infty : \operatorname{nrd}x_w\in[1,e^2)\ \forall w\}$. -/
def Sh : Set (QuatInf (a : F) (b : F))ˣ :=
  {y | ∀ w : {w : InfinitePlace F // w.IsReal},
    nrd ((unitAtR (a : F) (b : F) w ((quatUnitsEquiv (a : F) (b : F)).symm (y, 1)) :
      (ℍ[ℝ, embedding_of_isReal w.2 (a : F), embedding_of_isReal w.2 (b : F)])ˣ) :
        ℍ[ℝ, embedding_of_isReal w.2 (a : F), embedding_of_isReal w.2 (b : F)]) ∈ Ico 1 (Real.exp 2)}

theorem unitAtR_eq_inf (x : (QuatAdele (a : F) (b : F))ˣ) (w : {w : InfinitePlace F // w.IsReal}) :
    unitAtR (a : F) (b : F) w x =
      unitAtR (a : F) (b : F) w ((quatUnitsEquiv (a : F) (b : F)).symm ((quatUnitsEquiv (a : F) (b : F) x).1, 1)) := by
  change Units.map (projR _ _ w).toMonoidHom (quatUnitsEquiv _ _ x).1 =
    Units.map (projR _ _ w).toMonoidHom (quatUnitsEquiv _ _ ((quatUnitsEquiv _ _).symm _)).1
  rw [ContinuousMulEquiv.apply_symm_apply]

/-- For $x$ with $x_v\in\Lambda_v^\times$ at every finite $v$: $\operatorname{nrd}x\in\mathrm{Bset}\iff x_\infty\in\mathrm{Sh}$. -/
theorem nrd_mem_Bset_iff (x : (QuatAdele (a : F) (b : F))ˣ)
    (hx : ∀ v, unitAtA (a : F) (b : F) v x ∈ lamLocUnits (a : F) (b : F) v) :
    nrdUnit x ∈ Bset ↔ (quatUnitsEquiv (a : F) (b : F) x).1 ∈ Sh a b := by
  have hfin : finPart (nrdUnit x) ∈ OHatUnits F := by
    refine ⟨fun v => ?_, fun v => ?_⟩
    · change ((nrdUnit x : (Adeles F)ˣ) : Adeles F).2 v ∈ v.adicCompletionIntegers F
      rw [← nrd_unitAtA, ← nrdLoc_eq_nrd]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
        ((mem_lamLocUnits_iff (fun w => valued_algebraMap_le_one a w) (fun w => valued_algebraMap_le_one b w) _).1
          (hx v)).2.le
    · rw [show (finPart (nrdUnit x))⁻¹ = finPart (nrdUnit x⁻¹) by
        rw [show nrdUnit x⁻¹ = (nrdUnit x)⁻¹ from map_inv (nrdHom (a : F) (b : F)) x]
        unfold finPart; rw [map_inv]]
      change ((nrdUnit x⁻¹ : (Adeles F)ˣ) : Adeles F).2 v ∈ v.adicCompletionIntegers F
      have hxi : unitAtA (a : F) (b : F) v x⁻¹ ∈ lamLocUnits (a : F) (b : F) v := by
        rw [map_inv]; exact ⟨(hx v).2, by rw [inv_inv]; exact (hx v).1⟩
      rw [← nrd_unitAtA, ← nrdLoc_eq_nrd]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
        ((mem_lamLocUnits_iff (fun w => valued_algebraMap_le_one a w) (fun w => valued_algebraMap_le_one b w) _).1
          hxi).2.le
  simp only [Bset, mem_preimage, mem_prod, idelesEquiv_apply, SetLike.mem_coe]
  rw [and_iff_left hfin]
  simp only [BInf, Sh, mem_setOf_eq]
  refine forall_congr' fun w => ?_
  rw [← unitAtR_eq_inf, nrd_unitAtR]
  rfl

/-! ### The boxes $X_H$, $X_E$ -/

section Boxes

variable (S : Finset (HeightOneSpectrum (𝓞 F))) (m : HeightOneSpectrum (𝓞 F) → ℕ) (hm1 : ∀ v, 1 ≤ m v)

theorem quatCongS_eq_quatBox [DecidablePred (· ∈ S)] :
    (quatCongS a b S m hm1 : Set (QuatFin (a : F) (b : F))ˣ) =
      quatBox (a : F) (b : F) S (fun v => (lamCong v a b (m v) (hm1 v) : Set (QuatV (a : F) (b : F) v)ˣ)) := by
  ext u
  rw [SetLike.mem_coe, mem_quatCongS]
  simp only [quatBox, ChartData.chartBox, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩ v
    change unitAtQ _ _ v u ∈ (if v ∈ S then _ else lamLocUnits (a : F) (b : F) v)
    split_ifs with hv
    · exact h2 v hv
    · exact h1 v
  · intro h
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · have := h v
      change unitAtQ _ _ v u ∈ (if v ∈ S then _ else lamLocUnits (a : F) (b : F) v) at this
      split_ifs at this with hv
      · exact this.2
      · exact this
    · have := h v
      change unitAtQ _ _ v u ∈ (if v ∈ S then _ else lamLocUnits (a : F) (b : F) v) at this
      rwa [if_pos hv] at this

theorem econgS_eq_quatBox [DecidablePred (· ∈ S)] :
    (econgS a b S m : Set (QuatFin (a : F) (b : F))ˣ) =
      quatBox (a : F) (b : F) S (fun v => (oneAddCong v a b (m v) : Set (QuatV (a : F) (b : F) v)ˣ)) := by
  ext u
  rw [SetLike.mem_coe, mem_econgS]
  simp only [quatBox, ChartData.chartBox, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩ v
    change unitAtQ _ _ v u ∈ (if v ∈ S then _ else lamLocUnits (a : F) (b : F) v)
    split_ifs with hv
    · exact h2 v hv
    · exact h1 v
  · intro h
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · have := h v
      change unitAtQ _ _ v u ∈ (if v ∈ S then _ else lamLocUnits (a : F) (b : F) v) at this
      split_ifs at this with hv
      · exact this.1
      · exact this
    · have := h v
      change unitAtQ _ _ v u ∈ (if v ∈ S then _ else lamLocUnits (a : F) (b : F) v) at this
      rwa [if_pos hv] at this

theorem sqX_HS_eq : sqX (HS a b S m hm1) Bset =
    quatUnitsEquiv (a : F) (b : F) ⁻¹' (Sh a b ×ˢ (quatCongS a b S m hm1 : Set (QuatFin (a : F) (b : F))ˣ)) := by
  ext x
  simp only [sqX, mem_setOf_eq, mem_preimage, mem_prod, SetLike.mem_coe]
  constructor
  · rintro ⟨hx, hB⟩
    exact ⟨(nrd_mem_Bset_iff x ((mem_HS a b S m hm1).1 hx).1).1 hB, hx⟩
  · rintro ⟨hSh, hx⟩
    exact ⟨hx, (nrd_mem_Bset_iff x ((mem_HS a b S m hm1).1 hx).1).2 hSh⟩

theorem sqX_ES_eq : sqX (ES a b S m) Bset =
    quatUnitsEquiv (a : F) (b : F) ⁻¹' (Sh a b ×ˢ (econgS a b S m : Set (QuatFin (a : F) (b : F))ˣ)) := by
  ext x
  simp only [sqX, mem_setOf_eq, mem_preimage, mem_prod, SetLike.mem_coe]
  constructor
  · rintro ⟨hx, hB⟩
    exact ⟨(nrd_mem_Bset_iff x ((mem_ES a b S m).1 hx).1).1 hB, hx⟩
  · rintro ⟨hSh, hx⟩
    exact ⟨hx, (nrd_mem_Bset_iff x ((mem_ES a b S m).1 hx).1).2 hSh⟩

end Boxes

/-! ### Local reduced norms -/

section LocalNrd

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- The scalar unit $r\in F_v^\times\subseteq(D\otimes F_v)^\times$. -/
abbrev scalV (r : Fvˣ) : (QuatV (a : F) (b : F) v)ˣ := Units.map (algebraMap Fv (QuatV (a : F) (b : F) v)).toMonoidHom r

theorem nrdLoc_scalV (r : Fvˣ) : nrdLoc _ _ ((scalV v r : (QuatV (a : F) (b : F) v)ˣ) : QuatV (a : F) (b : F) v) =
    (r : Fv) ^ 2 := by
  have hc : quatLocCoord _ _ ((scalV v r : (QuatV (a : F) (b : F) v)ˣ) : QuatV (a : F) (b : F) v) =
      ![(r : Fv), 0, 0, 0] := by
    ext i; fin_cases i <;> rfl
  rw [nrdLoc_eq_nrdForm, hc, nrdForm]; simp

/-- **Good places**: every unit is the reduced norm of an element of $\Lambda_v^\times$ ($|2ab|_v = 1$). -/
theorem exists_lamLocUnits_nrd (h2 : Valued.v (2 : Fv) = 1) (hav : Valued.v (algebraMap F Fv (a : F)) = 1)
    {t : Fv} (ht : Valued.v t = 1) :
    ∃ y : (QuatV (a : F) (b : F) v)ˣ, y ∈ lamLocUnits (a : F) (b : F) v ∧
      nrdLoc _ _ (y : QuatV (a : F) (b : F) v) = t := by
  obtain ⟨x, z, hx, hz, hxz⟩ := exists_sq_sub_mul_sq_eq v h2 hav ht
  set q : QuatV (a : F) (b : F) v := ⟨x, z, 0, 0⟩
  have hq : nrdLoc _ _ q = t := by
    rw [nrdLoc_eq_nrdForm, ← hxz]
    have hc : quatLocCoord _ _ q = ![x, z, 0, 0] := by ext i; fin_cases i <;> rfl
    rw [hc, nrdForm]; simp
  have hq0 : nrdLoc _ _ q ≠ 0 := by rw [hq]; intro h; rw [h, map_zero] at ht; exact zero_ne_one ht
  obtain ⟨y, hy⟩ := (isUnit_iff_nrdLoc_ne_zero _ _ q).2 hq0
  refine ⟨y, ?_, by rw [hy, hq]⟩
  rw [mem_lamLocUnits_iff (fun w => valued_algebraMap_le_one a w) (fun w => valued_algebraMap_le_one b w), hy, hq]
  refine ⟨?_, ht⟩
  simp only [lamLoc, mem_setOf_eq, HeightOneSpectrum.mem_adicCompletionIntegers, q]
  exact ⟨hx, hz, by simp, by simp⟩

/-- **Bad places**: every $t\in1+\pi^{m+s}\mathfrak o_v$ is the reduced norm of a scalar in $1+\pi^m\Lambda_v$ ($s < m$). -/
theorem exists_oneAddCong_nrd {s m : ℕ} (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) (hsm : s < m) {t : Fv}
    (ht : Valued.v (t - 1) ≤ exp (-((m + s : ℕ) : ℤ))) :
    ∃ y : (QuatV (a : F) (b : F) v)ˣ, y ∈ oneAddCong v a b m ∧ nrdLoc _ _ (y : QuatV (a : F) (b : F) v) = t := by
  obtain ⟨r, hr, hr1⟩ := exists_sq_eq_near_one v hs hsm ht
  have hr0 : r ≠ 0 := by
    intro h0; rw [h0, zero_sub, Valuation.map_neg, map_one] at hr1
    exact absurd hr1 (by rw [← exp_zero, exp_le_exp]; omega)
  refine ⟨scalV v (Units.mk0 r hr0), ?_, by rw [nrdLoc_scalV, Units.val_mk0, hr]⟩
  rw [mem_oneAddCong_iff v a b (by omega)]
  have e : ((scalV v (Units.mk0 r hr0) : (QuatV (a : F) (b : F) v)ˣ) : QuatV (a : F) (b : F) v) - 1 =
      algebraMap Fv (QuatV (a : F) (b : F) v) (r - 1) := by
    simp [scalV, map_sub]
  rw [e]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hr1]

end LocalNrd

/-! ### The reduced-norm image of $E_S$ -/

section NrdImage

variable (S : Finset (HeightOneSpectrum (𝓞 F))) (m : HeightOneSpectrum (𝓞 F) → ℕ) (hm1 : ∀ v, 1 ≤ m v)

/-- The local sets $1+\pi^{m_v+s_v}\mathfrak o_v$. -/
def nU (v : HeightOneSpectrum (𝓞 F)) : Set (v.adicCompletion F)ˣ :=
  {r | Valued.v ((r : v.adicCompletion F) - 1) ≤ exp (-((m v + sExp v : ℕ) : ℤ))}

/-- $N_E = \{t_f : t_v\in\mathfrak o_v^\times\ (v\notin S),\ t_v\in1+\pi^{m_v+s_v}\mathfrak o_v\ (v\in S)\}$. -/
def NE : Set (FiniteAdeleRing (𝓞 F) F)ˣ := ideleBox S (nU m)

theorem measurableSet_nU (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (nU m v) := by
  have : nU m v = Units.val ⁻¹' ((fun x => x - 1) ⁻¹' (Analysis.latticeV v ((m v + sExp v : ℕ) : ℤ) :
      Set (v.adicCompletion F))) := by
    ext r; simp [nU, Analysis.mem_latticeV]
  rw [this]
  exact ((Analysis.measurableSet_latticeV v _).preimage (measurable_id.sub_const 1)).preimage
    Units.continuous_val.measurable

theorem nU_subset (v : HeightOneSpectrum (𝓞 F)) (hv : 1 ≤ m v) : nU m v ⊆ unitsVSub v := fun r hr =>
  valued_eq_one_of_sub_one_lt v (valued_lt_one_of_le_exp v (by omega) hr)

include hm1 in
theorem NE_subset_OHatUnits : NE S m ⊆ (OHatUnits F : Set (FiniteAdeleRing (𝓞 F) F)ˣ) := by
  intro g hg
  rw [← ideleBox_empty (nU m)]
  intro v
  have := hg v
  simp only [Finset.notMem_empty, ite_false]
  split_ifs at this with hv
  · exact nU_subset m v (hm1 v) this
  · exact this

theorem nrdUnit_mkAdeleUnit_eq [IsTotallyReal F] (t : (Adeles F)ˣ)
    (βR : ∀ w : {w : InfinitePlace F // w.IsReal},
      (ℍ[ℝ, embedding_of_isReal w.2 (a : F), embedding_of_isReal w.2 (b : F)])ˣ)
    (βC : ∀ w : {w : InfinitePlace F // w.IsComplex}, (ℍ[ℂ, w.1.embedding (a : F), w.1.embedding (b : F)])ˣ)
    (β : ∀ v : HeightOneSpectrum (𝓞 F), (QuatV (a : F) (b : F) v)ˣ) (hev)
    (hR : ∀ w, nrd ((βR w : (ℍ[ℝ, embedding_of_isReal w.2 (a : F), embedding_of_isReal w.2 (b : F)])ˣ) :
      ℍ[ℝ, embedding_of_isReal w.2 (a : F), embedding_of_isReal w.2 (b : F)]) = (t : Adeles F).1.1 w)
    (hF : ∀ v, nrdLoc _ _ ((β v : (QuatV (a : F) (b : F) v)ˣ) : QuatV (a : F) (b : F) v) = (t : Adeles F).2 v) :
    nrdUnit (mkAdeleUnit (a : F) (b : F) βR βC β hev) = t := by
  have := isEmpty_complex (F := F)
  apply Units.ext
  refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => isEmptyElim w)) (Subtype.ext (funext fun v => ?_))
  · rw [← nrd_unitAtR, unitAtR_mkAdeleUnit, hR]
  · change ((nrdUnit _ : (Adeles F)ˣ) : Adeles F).2 v = (t : Adeles F).2 v
    rw [← nrd_unitAtA, unitAtA_mkAdeleUnit, ← nrdLoc_eq_nrd, hF]

theorem nrd_scalarR (w : {w : InfinitePlace F // w.IsReal}) (c : ℝˣ) :
    nrd (((Units.map (algebraMap ℝ (ℍ[ℝ, embedding_of_isReal w.2 (a : F), embedding_of_isReal w.2 (b : F)])).toMonoidHom c :
      (ℍ[ℝ, embedding_of_isReal w.2 (a : F), embedding_of_isReal w.2 (b : F)])ˣ)) :
        ℍ[ℝ, embedding_of_isReal w.2 (a : F), embedding_of_isReal w.2 (b : F)]) = (c : ℝ) ^ 2 := by
  change nrd (algebraMap ℝ _ (c : ℝ)) = _
  simp [nrd, QuaternionAlgebra.algebraMap_eq]

include hm1 in
/-- **$\operatorname{nrd}(E_S)\cap\mathrm{Bset} = \{t : t_\infty\in\mathrm{BInf},\ t_f\in N_E\}$.** -/
theorem nrd_image_ES [IsTotallyReal F]
    (hS : ∀ v ∉ S, Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1)
    (hsm : ∀ v ∈ S, sExp v < m v) :
    nrdUnit '' (ES a b S m : Set (QuatAdele (a : F) (b : F))ˣ) ∩ Bset =
      idelesEquiv F ⁻¹' ((BInf (F := F)) ×ˢ NE S m) := by
  have := isEmpty_complex (F := F)
  ext t
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hB⟩
    have hx' := (mem_ES a b S m).1 hx
    refine ⟨(hB : _).1, fun v => ?_⟩
    have hval : ((unitAt ((idelesEquiv F) (nrdUnit x)).2 v : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        nrdLoc _ _ ((unitAtA (a : F) (b : F) v x : (QuatV (a : F) (b : F) v)ˣ) : QuatV (a : F) (b : F) v) := by
      rw [nrdLoc_eq_nrd, nrd_unitAtA]; rfl
    split_ifs with hv
    · show Valued.v (((unitAt ((idelesEquiv F) (nrdUnit x)).2 v : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1) ≤ _
      rw [hval]
      exact valued_nrdLoc_sub_one_le v a b (valued_two_eq v) (hsm v hv).le (hx'.2 v hv)
    · show Valued.v ((unitAt ((idelesEquiv F) (nrdUnit x)).2 v : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1
      rw [hval]
      exact ((mem_lamLocUnits_iff (fun w => valued_algebraMap_le_one a w)
        (fun w => valued_algebraMap_le_one b w) _).1 (hx'.1 v)).2
  · rintro ⟨hinf, hfin⟩
    have hloc : ∀ v, ∃ y : (QuatV (a : F) (b : F) v)ˣ, y ∈ lamLocUnits (a : F) (b : F) v ∧
        nrdLoc _ _ (y : QuatV (a : F) (b : F) v) = (t : Adeles F).2 v ∧ (v ∈ S → y ∈ oneAddCong v a b (m v)) := by
      intro v
      have h := hfin v
      by_cases hv : v ∈ S
      · rw [if_pos hv] at h
        obtain ⟨y, hy, hyt⟩ := exists_oneAddCong_nrd v (a := a) (b := b) (valued_two_eq v) (hsm v hv)
          (show Valued.v ((t : Adeles F).2 v - 1) ≤ _ from h)
        exact ⟨y, hy.1, hyt, fun _ => hy⟩
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
    · rw [SetLike.mem_coe, mem_ES]
      refine ⟨fun v => by rw [unitAtA_mkAdeleUnit]; exact hyL v, fun v hv => ?_⟩
      rw [unitAtA_mkAdeleUnit]; exact hyS v hv
    · refine nrdUnit_mkAdeleUnit_eq t βR _ y _ (fun w => ?_) hyt
      rw [nrd_scalarR, Units.val_mk0, Real.sq_sqrt (htw w).le]
    · exact ⟨hinf, NE_subset_OHatUnits S m hm1 hfin⟩

end NrdImage

/-! ### Scalars in $H_S$ -/

section Scalars

variable (S : Finset (HeightOneSpectrum (𝓞 F))) (m : HeightOneSpectrum (𝓞 F) → ℕ) (hm1 : ∀ v, 1 ≤ m v)

theorem unitAtA_quatScalar_val (c : (Adeles F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ((unitAtA (a : F) (b : F) v (quatScalar (a : F) (b : F) c) : (QuatV (a : F) (b : F) v)ˣ) :
      QuatV (a : F) (b : F) v) = ⟨(c : Adeles F).2 v, 0, 0, 0⟩ := by
  rw [unitAtA_val]
  ext <;> simp [val_quatScalar] <;> rfl

theorem quatScalar_mem_lamLocUnits_iff (c : (Adeles F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    unitAtA (a : F) (b : F) v (quatScalar (a : F) (b : F) c) ∈ lamLocUnits (a : F) (b : F) v ↔
      Valued.v ((c : Adeles F).2 v) = 1 := by
  rw [mem_lamLocUnits_iff (fun w => valued_algebraMap_le_one a w) (fun w => valued_algebraMap_le_one b w),
    unitAtA_quatScalar_val]
  have hn : nrdLoc (algebraMap F (v.adicCompletion F) (a : F)) (algebraMap F (v.adicCompletion F) (b : F))
      (⟨(c : Adeles F).2 v, 0, 0, 0⟩ : QuatV (a : F) (b : F) v) = ((c : Adeles F).2 v) ^ 2 := by
    rw [nrdLoc_eq_nrdForm]
    have hc : quatLocCoord _ _ (⟨(c : Adeles F).2 v, 0, 0, 0⟩ : QuatV (a : F) (b : F) v) =
        ![(c : Adeles F).2 v, 0, 0, 0] := by ext i; fin_cases i <;> rfl
    rw [hc, nrdForm]; simp
  rw [hn, map_pow]
  simp only [lamLoc, mem_setOf_eq, HeightOneSpectrum.mem_adicCompletionIntegers, map_zero, zero_le', and_true]
  constructor
  · rintro ⟨-, h⟩; exact (pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 h
  · intro h; exact ⟨h.le, by rw [h, one_pow]⟩

theorem finPart_mem_OHatUnits_iff (c : (Adeles F)ˣ) :
    finPart c ∈ OHatUnits F ↔ ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((c : Adeles F).2 v) = 1 := by
  rw [← SetLike.mem_coe, ← ideleBox_empty (fun v => unitsVSub v)]
  simp only [ideleBox, Finset.notMem_empty, ite_false, mem_ofPred_eq]
  rfl

/-- **A scalar lies in $H_S$ iff its finite part is in $\hat{\mathcal O}^\times$.** -/
theorem quatScalar_mem_HS_iff (ha : a ≠ 0) (c : (Adeles F)ˣ) :
    quatScalar (a : F) (b : F) c ∈ HS a b S m hm1 ↔ finPart c ∈ OHatUnits F := by
  have hA : (a : F) ≠ 0 := by exact_mod_cast ha
  rw [mem_HS, finPart_mem_OHatUnits_iff]
  constructor
  · rintro ⟨h1, -⟩ v; exact (quatScalar_mem_lamLocUnits_iff c v).1 (h1 v)
  · intro h
    refine ⟨fun v => (quatScalar_mem_lamLocUnits_iff c v).2 (h v), fun v _ => ⟨?_, (quatScalar_mem_lamLocUnits_iff c v).2 (h v)⟩⟩
    show conjOrth _ (hQF a b) (unitAtA (a : F) (b : F) v (quatScalar (a : F) (b : F) c)) ∈ congSub v _ (m v) (hm1 v)
    rw [(conjOrth_eq_one_iff _ (hQF a b) hA _).2 (unitAtA_quatScalar_mem c v)]
    exact Subgroup.one_mem _

end Scalars

end QuadFormsKB.Tamagawa.Measure.Weil

end
