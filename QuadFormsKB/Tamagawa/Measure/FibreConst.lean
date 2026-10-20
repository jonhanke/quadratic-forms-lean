import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.Measure.FibreLeray
import QuadFormsKB.Tamagawa.Measure.FibreDecomp

/-!
# The constant in the group-level fibre form at a finite place
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology WithZero Matrix
open scoped ENNReal NNReal
open QuadFormsKB QuadFormsKB.Analysis QuadFormsKB.LocalDensity QuadFormsKB.Tamagawa QuadFormsKB.Lattices
open QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.LerayFinite

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.FibreConst

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F

/-- **The orbital identity on `O(L_v)`** (the `O` version of `localOrbitalIdentity_measure`): with `muLoc` on both
orthogonal groups, `W·μ_G(O(L))·|2m|^n = μ_H(O(L'))·σ_m(L_v)`. -/
@[kb "weil1982" "§3.4 (local orbital identity on O(L_v)) [unverified]"]
theorem localOrbitalIdentity_orth (m₀ : 𝓞 F) (hm : m₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) n) (hQ' : Q₀'.Nondegenerate)
    (hn : 1 ≤ n) :
    locTypeSum v (algebraMap (𝓞 F) F m₀) (Q₀'.map (algebraMap (𝓞 F) F)) *
        (muLoc v (splitForm m₀ Q₀') 1 (stdStab ((splitForm m₀ Q₀').map (algebraMap (𝓞 F) F)) v :
          Set (orthGroup ((splitForm m₀ Q₀').map (algebraMap (𝓞 F) F)) Fv))).toReal * absTwoM v m₀ ^ n =
      (muLoc v Q₀' 1 (stdStab (Q₀'.map (algebraMap (𝓞 F) F)) v :
          Set (orthGroup (Q₀'.map (algebraMap (𝓞 F) F)) Fv))).toReal *
        (lerayMeasure v (haarV v) (NF.Qp v (splitForm m₀ Q₀')) (NF.nondegenerate_Qp v (by
            rw [QuadForm.Nondegenerate, det_hessian_splitForm]
            exact mul_ne_zero (mul_ne_zero two_ne_zero hm) hQ'))
          ((NF.ι v m₀ : v.adicCompletionIntegers F) : v.adicCompletion F) (LocalZeta.latL v (n + 1))).toReal := by
  have hQ : (splitForm m₀ Q₀').Nondegenerate := by
    rw [QuadForm.Nondegenerate, det_hessian_splitForm]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hm) hQ'
  have h := LerayFinite.localOrbitalIdentity_measure v m₀ hm Q₀' hQ'
  have hα : 0 < NF.siegelDensity v (splitForm m₀ Q₀') (splitForm m₀ Q₀') := siegelDensity_pos v _ hQ
  have hα' : 0 < NF.siegelDensity v Q₀' Q₀' := siegelDensity_pos v _ hQ'
  have hn' : 0 < n := hn
  have hs : (muLoc v (splitForm m₀ Q₀') 1 (stdStab ((splitForm m₀ Q₀').map (algebraMap (𝓞 F) F)) v :
          Set (orthGroup ((splitForm m₀ Q₀').map (algebraMap (𝓞 F) F)) Fv))).toReal =
      2 * NF.siegelDensity v (splitForm m₀ Q₀') (splitForm m₀ Q₀') := by
    have e := measure_subgroup_eq_relIndex_mul (muLoc v (splitForm m₀ Q₀') 1)
      (isOpen_soStab v (splitForm m₀ Q₀') hQ) (A := stdStab ((splitForm m₀ Q₀').map (algebraMap (𝓞 F) F)) v)
      (inf_le_right : soStab v (splitForm m₀ Q₀') ≤ _)
      (by rw [relIndex_soStab v _ hQ (by omega)]; norm_num)
    rw [relIndex_soStab v _ hQ (by omega), muLoc_soStab v _ hQ (by omega) one_pos] at e
    rw [e]
    simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal hα.le, div_one]
  have hs' : (muLoc v Q₀' 1 (stdStab (Q₀'.map (algebraMap (𝓞 F) F)) v :
          Set (orthGroup (Q₀'.map (algebraMap (𝓞 F) F)) Fv))).toReal = 2 * NF.siegelDensity v Q₀' Q₀' := by
    have e := measure_subgroup_eq_relIndex_mul (muLoc v Q₀' 1)
      (isOpen_soStab v Q₀' hQ') (A := stdStab (Q₀'.map (algebraMap (𝓞 F) F)) v)
      (inf_le_right : soStab v Q₀' ≤ _)
      (by rw [relIndex_soStab v _ hQ' hn']; norm_num)
    rw [relIndex_soStab v _ hQ' hn', muLoc_soStab v _ hQ' hn' one_pos] at e
    rw [e]
    simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal hα'.le, div_one]
  rw [hs, hs']
  rw [muLocSO_soStabSO, muLocSO_soStabSO, div_one, div_one, ENNReal.toReal_ofReal hα.le, ENNReal.toReal_ofReal hα'.le] at h
  linear_combination 2 * h

section Unimod

variable {N : ℕ} (Q : QuadForm F N)

/-- **Unimodularity of `O(V)(F_v)` on `O(L_v)`:** `μ(h K h⁻¹) = μ(K)` for the Haar measure `muLoc`. -/
theorem muLoc_conj_stdStab (Q₀ : QuadForm (𝓞 F) N) (hQ₀ : Q₀.Nondegenerate)
    (h : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv) :
    muLoc v Q₀ 1 (((stdStab (Q₀.map (algebraMap (𝓞 F) F)) v).map (MulAut.conj h).toMonoidHom :
        Subgroup (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv)) : Set _) =
      muLoc v Q₀ 1 (stdStab (Q₀.map (algebraMap (𝓞 F) F)) v : Set _) := by
  have hQQ := nondegenerate_QF Q₀ hQ₀
  have hmod := modRatio_eq_one v (Q₀.map (algebraMap (𝓞 F) F)) hQQ h
  unfold modRatio at hmod
  have hc : Commens (stdStab (Q₀.map (algebraMap (𝓞 F) F)) v) ((stdStab (Q₀.map (algebraMap (𝓞 F) F)) v).map (MulAut.conj h).toMonoidHom) := by
    rw [stdStab_map_conj, stdStab_eq_stabLat]
    have := commens_std v (Q₀.map (algebraMap (𝓞 F) F)) 1 h
    rw [map_one, locAct_one] at this
    exact this
  have hopen : IsOpen (((stdStab (Q₀.map (algebraMap (𝓞 F) F)) v).map (MulAut.conj h).toMonoidHom : Subgroup _) : Set (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv)) := by
    have : ((stdStab (Q₀.map (algebraMap (𝓞 F) F)) v).map (MulAut.conj h).toMonoidHom : Set (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv)) =
        (fun x => h⁻¹ * x * h) ⁻¹' (stdStab (Q₀.map (algebraMap (𝓞 F) F)) v : Set (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv)) := by
      ext x
      simp only [Subgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have : h⁻¹ * (h * y * h⁻¹) * h = y := by group
        rw [this]; exact hy
      · intro hx; exact ⟨h⁻¹ * x * h, hx, by group⟩
    rw [this]
    exact (isOpen_stdStab v (Q₀.map (algebraMap (𝓞 F) F))).preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have e := measure_toReal_eq_relRatio_mul (muLoc v Q₀ 1) (isOpen_stdStab v (Q₀.map (algebraMap (𝓞 F) F))) hopen hc.1 hc.2
  rw [hmod, one_mul] at e
  have hfin1 : muLoc v Q₀ 1 (stdStab (Q₀.map (algebraMap (𝓞 F) F)) v : Set _) ≠ ∞ := (isCompact_stdStab v (Q₀.map (algebraMap (𝓞 F) F))).measure_lt_top.ne
  have hfin2 : muLoc v Q₀ 1 (((stdStab (Q₀.map (algebraMap (𝓞 F) F)) v).map (MulAut.conj h).toMonoidHom : Subgroup _) : Set _) ≠ ∞ := by
    have : IsCompact (((stdStab (Q₀.map (algebraMap (𝓞 F) F)) v).map (MulAut.conj h).toMonoidHom : Subgroup _) : Set (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv)) := by
      have : ((stdStab (Q₀.map (algebraMap (𝓞 F) F)) v).map (MulAut.conj h).toMonoidHom : Set (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv)) =
          (fun x => h * x * h⁻¹) '' (stdStab (Q₀.map (algebraMap (𝓞 F) F)) v : Set (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv)) := by
        ext x
        simp [Subgroup.coe_map, MulAut.conj_apply]
      rw [this]
      exact (isCompact_stdStab v (Q₀.map (algebraMap (𝓞 F) F))).image ((continuous_const.mul continuous_id).mul continuous_const)
    exact this.measure_lt_top.ne
  exact (ENNReal.toReal_eq_toReal_iff' hfin2 hfin1).1 e.symm

end Unimod

section Assembly

open FibreDecomp

variable (m₀ : 𝓞 F) (hm : m₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) n) (hQ' : Q₀'.Nondegenerate) (hn : 1 ≤ n)

theorem hQ0 (hm : m₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) : (splitForm m₀ Q₀').Nondegenerate := by
  rw [QuadForm.Nondegenerate, det_hessian_splitForm]
  exact mul_ne_zero (mul_ne_zero two_ne_zero hm) hQ'

/-- The Leray measure on the quadric `{Q = m}`. -/
abbrev nuS : Measure (FibreO.sphereSet v (QQ m₀ Q₀') (mm m₀)) :=
  FibreLeray.sphereMeasure v (splitForm m₀ Q₀') (hQ0 m₀ Q₀' hm hQ') (mm m₀)

/-- The lattice points of the quadric. -/
def Pset : Set (FibreO.sphereSet v (QQ m₀ Q₀') (mm m₀)) := {y | (y : Fin (n + 1) → Fv) ∈ std v}

theorem mem_std_iff (x : Fin (n + 1) → Fv) : x ∈ std v ↔ x ∈ LocalZeta.latL v (n + 1) := by
  simp [LocalZeta.latL, mem_ball]

theorem nuS_Pset : nuS v m₀ hm Q₀' hQ' (Pset v m₀ Q₀') =
    lerayMeasure v (haarV v) (NF.Qp v (splitForm m₀ Q₀')) (NF.nondegenerate_Qp v (hQ0 m₀ Q₀' hm hQ'))
      ((NF.ι v m₀ : v.adicCompletionIntegers F) : v.adicCompletion F) (LocalZeta.latL v (n + 1)) := by
  have hrho : algebraMap F Fv (mm m₀) = ((NF.ι v m₀ : v.adicCompletionIntegers F) : v.adicCompletion F) := rfl
  unfold nuS FibreLeray.sphereMeasure
  rw [(MeasurableEmbedding.subtype_coe (FibreLeray.measurableSet_sphereSet v (splitForm m₀ Q₀') (mm m₀))).comap_apply]
  have himg : Subtype.val '' Pset v m₀ Q₀' =
      LocalZeta.latL v (n + 1) ∩ FibreLeray.sphereV v (splitForm m₀ Q₀') (algebraMap F Fv (mm m₀)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(mem_std_iff v _).1 hy, ?_⟩
      rw [← FibreLeray.sphereSet_eq]; exact y.2
    · rintro ⟨h1, h2⟩
      refine ⟨⟨x, by rw [FibreLeray.sphereSet_eq]; exact h2⟩, (mem_std_iff v _).2 h1, rfl⟩
  rw [himg, measure_inter_conull (FibreLeray.sig_sph_compl v (splitForm m₀ Q₀') (hQ0 m₀ Q₀' hm hQ') _), hrho]

/-- The `K`-orbit of a point of the quadric. -/
def Korb (x : FibreO.sphereSet v (QQ m₀ Q₀') (mm m₀)) : Set (FibreO.sphereSet v (QQ m₀ Q₀') (mm m₀)) :=
  {y | ∃ κ ∈ stdStab (QQ m₀ Q₀') v, κ • x = y}

theorem measurableSet_Korb (x : FibreO.sphereSet v (QQ m₀ Q₀') (mm m₀)) :
    MeasurableSet (Korb v m₀ Q₀' x) := by
  have hc : Continuous fun g : orthGroup (QQ m₀ Q₀') Fv => g • x := by
    refine Continuous.subtype_mk ?_ _
    exact (Units.continuous_val.comp continuous_subtype_val).matrix_mulVec continuous_const
  have : Korb v m₀ Q₀' x = (fun g : orthGroup (QQ m₀ Q₀') Fv => g • x) '' (stdStab (QQ m₀ Q₀') v : Set _) := by
    ext y; simp [Korb, eq_comm]
  rw [this]
  exact ((isCompact_stdStab v (QQ m₀ Q₀')).image hc).isClosed.measurableSet

section ConjK

variable (g : orthGroup (QQ m₀ Q₀') (v.adicCompletion F))

theorem isOpen_conjK : IsOpen ((conjK v m₀ Q₀' g : Subgroup _) : Set (orthGroup (QQ m₀ Q₀') Fv)) := by
  have : ((conjK v m₀ Q₀' g : Subgroup _) : Set (orthGroup (QQ m₀ Q₀') Fv)) =
      (fun x => g * x * g⁻¹) ⁻¹' (stdStab (QQ m₀ Q₀') v : Set (orthGroup (QQ m₀ Q₀') Fv)) := by
    ext x
    simp only [conjK, Subgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y := by group
      rw [this]; exact hy
    · intro hx; exact ⟨g * x * g⁻¹, hx, by group⟩
  rw [this]
  exact (isOpen_stdStab v (QQ m₀ Q₀')).preimage ((continuous_const.mul continuous_id).mul continuous_const)

theorem isCompact_conjK : IsCompact ((conjK v m₀ Q₀' g : Subgroup _) : Set (orthGroup (QQ m₀ Q₀') Fv)) := by
  have : ((conjK v m₀ Q₀' g : Subgroup _) : Set (orthGroup (QQ m₀ Q₀') Fv)) =
      (fun x => g⁻¹ * x * g⁻¹⁻¹) '' (stdStab (QQ m₀ Q₀') v : Set (orthGroup (QQ m₀ Q₀') Fv)) := by
    ext x
    simp [conjK, Subgroup.coe_map, MulAut.conj_apply]
  rw [this]
  exact (isCompact_stdStab v (QQ m₀ Q₀')).image ((continuous_const.mul continuous_id).mul continuous_const)

theorem muG_conjK (hm : m₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) : muLoc v (splitForm m₀ Q₀') 1 ((conjK v m₀ Q₀' g : Subgroup _) : Set _) =
    muLoc v (splitForm m₀ Q₀') 1 (stdStab (QQ m₀ Q₀') v : Set _) :=
  muLoc_conj_stdStab v (splitForm m₀ Q₀') (hQ0 m₀ Q₀' hm hQ') g⁻¹

theorem orbitSetU_conjK :
    FibreO.orbitSetU v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') (mm_ne m₀ hm) (QQ'_nondeg Q₀' hQ') hn
        (conjK v m₀ Q₀' g) =
      (fun y => g • y) ⁻¹' Korb v m₀ Q₀' (g • (sect v m₀ hm Q₀' hQ' hn).base) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hu
    refine ⟨k, hk, ?_⟩
    simp [mul_smul]
  · rintro ⟨κ, hκ, hx⟩
    refine ⟨g⁻¹ * κ * g, Subgroup.mem_map.2 ⟨κ, hκ, by simp⟩, ?_⟩
    have : (g⁻¹ * κ * g) • (sect v m₀ hm Q₀' hQ' hn).base = x := by
      rw [mul_smul, mul_smul, inv_smul_eq_iff]
      exact hx
    exact this

end ConjK

theorem stdStab_mulVec_mem {N : ℕ} (Q : QuadForm F N) {κ : orthGroup Q Fv} (hκ : κ ∈ stdStab Q v)
    {x : Fin N → Fv} (hx : x ∈ std v) : (κ : GL (Fin N) Fv).val *ᵥ x ∈ std v := by
  have h : (κ : GL (Fin N) Fv).val *ᵥ x ∈ locAct v (κ : GL (Fin N) Fv) (std v) := mem_locAct.2 ⟨x, hx, rfl⟩
  have hκ' : locAct v (κ : GL (Fin N) Fv) (std v) = std v := hκ
  rwa [hκ'] at h

theorem Korb_subset_Pset {x : FibreO.sphereSet v (QQ m₀ Q₀') (mm m₀)} (hx : (x : Fin (n + 1) → Fv) ∈ std v) :
    Korb v m₀ Q₀' x ⊆ Pset v m₀ Q₀' := by
  rintro _ ⟨κ, hκ, rfl⟩
  exact stdStab_mulVec_mem v (QQ m₀ Q₀') hκ hx

@[kb "weil1982" "§2.4 Thm 2.4.3 p. 25; §3.4 (local fibration, constant |2m|^n) [unverified]"]
theorem fibre_constant :
    ((nuS v m₀ hm Q₀' hQ').prod (muLoc v Q₀' 1)).map
        (FibreO.orb v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') (mm_ne m₀ hm) (QQ'_nondeg Q₀' hQ') hn) =
      ENNReal.ofReal (absTwoM v m₀ ^ n) • muLoc v (splitForm m₀ Q₀') 1 := by
  obtain ⟨Tp, hT, γ, w, hL, hdisj, hcov, hw, hsum⟩ := exists_orbit_decomp v m₀ hm Q₀' hQ' hn
  have hQ := hQ0 m₀ Q₀' hm hQ'
  haveI hGH : (muLoc v (splitForm m₀ Q₀') 1).IsHaarMeasure := isHaarMeasure_muLoc v _ hQ one_pos
  haveI hHH : (muLoc v Q₀' 1).IsHaarMeasure := isHaarMeasure_muLoc v _ hQ' one_pos
  set K := stdStab (QQ m₀ Q₀') v with hKdef
  set K' := stdStab (QQ' Q₀') v with hK'def
  set S := sect v m₀ hm Q₀' hQ' hn with hSdef
  have hK0 : muLoc v (splitForm m₀ Q₀') 1 (K : Set _) ≠ 0 :=
    (isOpen_stdStab v (QQ m₀ Q₀')).measure_pos _ ⟨1, K.one_mem⟩ |>.ne'
  have hKt : muLoc v (splitForm m₀ Q₀') 1 (K : Set _) ≠ ∞ := (isCompact_stdStab v (QQ m₀ Q₀')).measure_lt_top.ne
  have hfib := FibreO.map_orb_eq_smul v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') (mm_ne m₀ hm) (QQ'_nondeg Q₀' hQ') hn
    (nuS v m₀ hm Q₀' hQ') (muLoc v Q₀' 1) (muLoc v (splitForm m₀ Q₀') 1) hK0 hKt
  -- the finite volume of the lattice points
  have hPfin : nuS v m₀ hm Q₀' hQ' (Pset v m₀ Q₀') ≠ ∞ := by
    rw [nuS_Pset v m₀ hm Q₀' hQ',
      lerayMeasure_latL v (haarV v) (NF.Qp v (splitForm m₀ Q₀')) (NF.nondegenerate_Qp v hQ) (n := n + 1) (by omega)
        (NF.ι v m₀) (NF.ι_ne_zero v hm)]
    exact ENNReal.ofReal_ne_top
  set Φ := ((nuS v m₀ hm Q₀' hQ').prod (muLoc v Q₀' 1)).map
    (FibreO.orb v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') (mm_ne m₀ hm) (QQ'_nondeg Q₀' hQ') hn) with hΦ
  set c := Φ K / muLoc v (splitForm m₀ Q₀') 1 (K : Set _) with hc
  have hmeasUt : ∀ t, MeasurableSet ((conjK v m₀ Q₀' (γ t) : Subgroup _) : Set (orthGroup (QQ m₀ Q₀') Fv)) :=
    fun t => (isOpen_conjK v m₀ Q₀' (γ t)).measurableSet
  have hOmeas : ∀ t, MeasurableSet (FibreO.orbitSetU v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') (mm_ne m₀ hm)
      (QQ'_nondeg Q₀' hQ') hn (conjK v m₀ Q₀' (γ t))) := fun t => by
    rw [orbitSetU_conjK v m₀ hm Q₀' hQ' hn (γ t)]
    exact (S.measurable_const_smul (γ t)) (measurableSet_Korb v m₀ Q₀' _)
  have hX : ∀ t, Φ ((conjK v m₀ Q₀' (γ t) : Subgroup _) : Set _) =
      nuS v m₀ hm Q₀' hQ' (Korb v m₀ Q₀' (γ t • S.base)) *
        muLoc v Q₀' 1 (FibreO.iota v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') ⁻¹'
          ((conjK v m₀ Q₀' (γ t) : Subgroup _) : Set _)) := by
    intro t
    rw [hΦ, FibreO.map_orb_subgroup v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') (mm_ne m₀ hm) (QQ'_nondeg Q₀' hQ') hn
      (nuS v m₀ hm Q₀' hQ') (muLoc v Q₀' 1) (conjK v m₀ Q₀' (γ t)) (hmeasUt t) (hOmeas t),
      orbitSetU_conjK v m₀ hm Q₀' hQ' hn (γ t),
      SMulInvariantMeasure.measure_preimage_smul (γ t) (measurableSet_Korb v m₀ Q₀' _)]
  have hXc : ∀ t, Φ ((conjK v m₀ Q₀' (γ t) : Subgroup _) : Set _) =
      c * muLoc v (splitForm m₀ Q₀') 1 (K : Set _) := by
    intro t
    rw [hfib]
    simp only [Measure.smul_apply, smul_eq_mul, muG_conjK v m₀ Q₀' (γ t) hm hQ']
    rfl
  -- the types are nonempty
  obtain ⟨t0⟩ : Nonempty Tp := by
    obtain ⟨t, -⟩ := hcov S.base (e₀_mem_std v)
    exact ⟨t⟩
  have hiotaCE := FibreO.isClosedEmbedding_iota v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') (mm_ne m₀ hm)
    (QQ'_nondeg Q₀' hQ') hn
  set ι := FibreO.iota v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') with hι
  -- finiteness / positivity
  have hNfin : ∀ t, nuS v m₀ hm Q₀' hQ' (Korb v m₀ Q₀' (γ t • S.base)) ≠ ∞ := fun t =>
    ne_top_of_le_ne_top hPfin (measure_mono (Korb_subset_Pset v m₀ Q₀' (hL t)))
  have hBopen : ∀ t, IsOpen (ι ⁻¹' ((conjK v m₀ Q₀' (γ t) : Subgroup _) : Set (orthGroup (QQ m₀ Q₀') Fv))) :=
    fun t => (isOpen_conjK v m₀ Q₀' (γ t)).preimage hiotaCE.continuous
  have hbfin : ∀ t, muLoc v Q₀' 1 (ι ⁻¹' ((conjK v m₀ Q₀' (γ t) : Subgroup _) : Set (orthGroup (QQ m₀ Q₀') Fv))) ≠ ∞ :=
    fun t => (hiotaCE.isCompact_preimage (isCompact_conjK v m₀ Q₀' (γ t))).measure_lt_top.ne
  have hbpos : ∀ t, muLoc v Q₀' 1 (ι ⁻¹' ((conjK v m₀ Q₀' (γ t) : Subgroup _) : Set (orthGroup (QQ m₀ Q₀') Fv))) ≠ 0 :=
    fun t => ((hBopen t).measure_pos _ ⟨1, by
      show ι 1 ∈ conjK v m₀ Q₀' (γ t)
      rw [map_one]; exact Subgroup.one_mem _⟩).ne'
  have hcfin : c ≠ ∞ := by
    intro hcinf
    have := (hXc t0).symm.trans (hX t0)
    rw [hcinf, ENNReal.top_mul hK0] at this
    exact ENNReal.mul_ne_top (hNfin t0) (hbfin t0) this.symm
  -- the real-number bookkeeping
  have hK'0 : muLoc v Q₀' 1 (K' : Set _) ≠ 0 :=
    ((isOpen_stdStab v (QQ' Q₀')).measure_pos _ ⟨1, K'.one_mem⟩).ne'
  have hK't : muLoc v Q₀' 1 (K' : Set _) ≠ ∞ := (isCompact_stdStab v (QQ' Q₀')).measure_lt_top.ne
  have ha_pos : 0 < (muLoc v (splitForm m₀ Q₀') 1 (K : Set _)).toReal := ENNReal.toReal_pos hK0 hKt
  have hb_pos : 0 < (muLoc v Q₀' 1 (K' : Set _)).toReal := ENNReal.toReal_pos hK'0 hK't
  have hbt_pos : ∀ t, 0 < (muLoc v Q₀' 1 (ι ⁻¹' ((conjK v m₀ Q₀' (γ t) : Subgroup _) :
      Set (orthGroup (QQ m₀ Q₀') Fv)))).toReal := fun t => ENNReal.toReal_pos (hbpos t) (hbfin t)
  have hrel : ∀ t, c.toReal * (muLoc v (splitForm m₀ Q₀') 1 (K : Set _)).toReal =
      (nuS v m₀ hm Q₀' hQ' (Korb v m₀ Q₀' (γ t • S.base))).toReal *
        (muLoc v Q₀' 1 (ι ⁻¹' ((conjK v m₀ Q₀' (γ t) : Subgroup _) : Set (orthGroup (QQ m₀ Q₀') Fv)))).toReal := by
    intro t
    have := congrArg ENNReal.toReal ((hXc t).symm.trans (hX t))
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul] at this
  have hwt : ∀ t, (muLoc v Q₀' 1 (K' : Set _)).toReal = w t *
      (muLoc v Q₀' 1 (ι ⁻¹' ((conjK v m₀ Q₀' (γ t) : Subgroup _) : Set (orthGroup (QQ m₀ Q₀') Fv)))).toReal := by
    intro t
    have := measure_toReal_eq_relRatio_mul (muLoc v Q₀' 1) (isOpen_stdStab v (QQ' Q₀')) (hBopen t)
      (hw t).1.1 (hw t).1.2
    rw [(hw t).2]
    exact this
  -- the lattice points are the disjoint union of the K-orbits
  have hUnion : Pset v m₀ Q₀' = ⋃ t, Korb v m₀ Q₀' (γ t • S.base) := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨t, κ, hκ, hκy⟩ := hcov y hy
      exact Set.mem_iUnion.2 ⟨t, κ, hκ, hκy⟩
    · exact Set.iUnion_subset fun t => Korb_subset_Pset v m₀ Q₀' (hL t)
  have hDisj : Pairwise (Function.onFun Disjoint fun t => Korb v m₀ Q₀' (γ t • S.base)) := by
    intro t t' htt'
    rw [Function.onFun, Set.disjoint_left]
    rintro y ⟨κ, hκ, rfl⟩ ⟨κ', hκ', hκκ⟩
    apply htt'
    refine hdisj t t' (κ'⁻¹ * κ) (K.mul_mem (K.inv_mem hκ') hκ) ?_
    rw [mul_smul, ← hκκ, inv_smul_smul]
  have hsumN : (nuS v m₀ hm Q₀' hQ' (Pset v m₀ Q₀')).toReal =
      ∑ t, (nuS v m₀ hm Q₀' hQ' (Korb v m₀ Q₀' (γ t • S.base))).toReal := by
    rw [hUnion, measure_iUnion hDisj (fun t => measurableSet_Korb v m₀ Q₀' _), tsum_fintype,
      ENNReal.toReal_sum (fun t _ => hNfin t)]
  -- the orbital identity
  have hid := localOrbitalIdentity_orth v m₀ hm Q₀' hQ' hn
  rw [← nuS_Pset v m₀ hm Q₀' hQ', hsumN] at hid
  have hwpos : ∀ t, 0 < w t := fun t => by
    have h1 := hwt t
    have h2 := hbt_pos t
    by_contra h
    push Not at h
    nlinarith
  have hWpos : 0 < ∑ t, w t := Finset.sum_pos (fun t _ => hwpos t) ⟨t0, Finset.mem_univ _⟩
  have hN : ∀ t, (nuS v m₀ hm Q₀' hQ' (Korb v m₀ Q₀' (γ t • S.base))).toReal *
      (muLoc v Q₀' 1 (K' : Set _)).toReal =
      c.toReal * (muLoc v (splitForm m₀ Q₀') 1 (K : Set _)).toReal * w t := fun t => by
    rw [hwt t]
    linear_combination (w t) * (hrel t).symm
  have hsumNb : (∑ t, (nuS v m₀ hm Q₀' hQ' (Korb v m₀ Q₀' (γ t • S.base))).toReal) *
      (muLoc v Q₀' 1 (K' : Set _)).toReal =
      c.toReal * (muLoc v (splitForm m₀ Q₀') 1 (K : Set _)).toReal * ∑ t, w t := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => hN t
  rw [← hsum] at hid
  have hC : c.toReal = absTwoM v m₀ ^ n := by
    have h0 : (∑ t, w t) * (muLoc v (splitForm m₀ Q₀') 1 (K : Set _)).toReal * (absTwoM v m₀ ^ n - c.toReal) = 0 := by
      linear_combination hid + hsumNb
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h (mul_pos hWpos ha_pos).ne'
    · linarith
  rw [hfib]
  congr 1
  rw [← ENNReal.ofReal_toReal hcfin, hC]

end Assembly

end QuadFormsKB.Tamagawa.Measure.FibreConst
