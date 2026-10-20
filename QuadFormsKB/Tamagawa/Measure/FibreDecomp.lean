import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.Measure.FibreO
import QuadFormsKB.Tamagawa.LocalUnimodular
import QuadFormsKB.Tamagawa.LocalOrbitalBad

/-!
# The `K`-orbits on the lattice points of the quadric are the local types
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology WithZero Matrix MulAction
open scoped ENNReal NNReal
open QuadFormsKB QuadFormsKB.Analysis QuadFormsKB.LocalDensity QuadFormsKB.Tamagawa QuadFormsKB.Lattices
open QuadFormsKB.Tamagawa.Measure

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.FibreDecomp

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F

/-- The form `Q = (⟨m₀⟩ ⊥ Q₀')⊗F`. -/
abbrev QQ (m₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n) : QuadForm F (n + 1) :=
  (splitForm m₀ Q₀').map (algebraMap (𝓞 F) F)

/-- The form `Q' = Q₀'⊗F`. -/
abbrev QQ' (Q₀' : QuadForm (𝓞 F) n) : QuadForm F n := Q₀'.map (algebraMap (𝓞 F) F)

/-- `m = m₀` in `F`. -/
abbrev mm (m₀ : 𝓞 F) : F := algebraMap (𝓞 F) F m₀

theorem hEE (m₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n) : QQ m₀ Q₀' = splitForm (mm m₀) (QQ' Q₀') :=
  map_splitForm _ _ _

theorem mm_ne (m₀ : 𝓞 F) (hm : m₀ ≠ 0) : mm m₀ ≠ 0 :=
  (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hm

theorem QQ'_nondeg (Q₀' : QuadForm (𝓞 F) n) (hQ' : Q₀'.Nondegenerate) : (QQ' Q₀').Nondegenerate :=
  nondegenerate_QF Q₀' hQ'

section Types

theorem hQ0' (m₀ : 𝓞 F) (hm : m₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) n) (hQ' : Q₀'.Nondegenerate) : (splitForm m₀ Q₀').Nondegenerate := by
  rw [QuadForm.Nondegenerate, det_hessian_splitForm]
  exact mul_ne_zero (mul_ne_zero two_ne_zero hm) hQ'

theorem hsplitF (m₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n) : splitForm (mm m₀) (QQ' Q₀') = QQ m₀ Q₀' := (hEE m₀ Q₀').symm

theorem hQo (m₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n) : IsIntModel v (splitForm (mm m₀) (QQ' Q₀')) (NF.Qp v (splitForm m₀ Q₀')) := fun y => by
  rw [hsplitF m₀ Q₀']; exact evalIn_coe_o v _ y

theorem hmoF (m₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n) : (((NF.ι v m₀ : v.adicCompletionIntegers F)) : v.adicCompletion F) =
    algebraMap F (v.adicCompletion F) (mm m₀) := by
  have := hQo v m₀ Q₀' (e₀ : Fin (n + 1) → v.adicCompletionIntegers F)
  rw [coe_e₀_o, evalIn_splitForm_e₀] at this
  have he₀ : (NF.Qp v (splitForm m₀ Q₀')).eval (e₀ : Fin (n + 1) → v.adicCompletionIntegers F) = NF.ι v m₀ := by
    rw [show NF.Qp v (splitForm m₀ Q₀') = splitForm (NF.ι v m₀) (NF.Qp v Q₀') from map_splitForm _ _ _]
    exact eval_splitForm_e₀' _ _
  rw [he₀] at this
  exact this.symm

/-- **Finitely many local types.** -/
theorem locTypes_finite (m₀ : 𝓞 F) (hm : m₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) n) (hQ' : Q₀'.Nondegenerate) :
    Finite (LocTypes v (mm m₀) (QQ' Q₀')) := by
  classical
  set mF := mm m₀
  set QF' := QQ' Q₀'
  set Qo := NF.Qp v (splitForm m₀ Q₀')
  set mo := NF.ι v m₀
  have hmF : mF ≠ 0 := mm_ne m₀ hm
  have hQ := hQ0' m₀ hm Q₀' hQ'
  have hQnd : Qo.Nondegenerate := NF.nondegenerate_Qp v hQ
  have hmo : mo ≠ 0 := NF.ι_ne_zero v hm
  have hπ := NF.irreducible_π v
  have h2 : (2 : v.adicCompletionIntegers F) ≠ 0 := NF.two_ne_zero' v
  have h4 : (4 : v.adicCompletionIntegers F) ≠ 0 := by
    rw [show (4 : v.adicCompletionIntegers F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  obtain ⟨f, hf, hf'⟩ := DVR.exists_pow_dvd_not_dvd (NF.π v) hπ (mul_ne_zero h4 hmo)
  set ρ := intRep v (splitForm mF QF')
  choose x σ h hx hσ hσx hloc using fun t : LocTypes v mF QF' =>
    exists_type_data v mF QF' hmF (hQo v m₀ Q₀') (hmoF v m₀ Q₀') (locRep v mF QF' t)
  set g : LocTypes v mF QF' → orthGroup (splitForm mF QF') (v.adicCompletion F) :=
    fun t => orthEmb mF QF' (v.adicCompletion F) (h t) * σ t
  have hginv : ∀ t, ((g t)⁻¹ : orthGroup (splitForm mF QF') (v.adicCompletion F)).val.val *ᵥ
      (e₀ : Fin (n + 1) → v.adicCompletion F) = fun i => (x t i : v.adicCompletion F) := by
    intro t
    have hσi : (σ t)⁻¹ = σ t := inv_eq_of_mul_eq_one_right (hσ t)
    simp only [g, _root_.mul_inv_rev, hσi, Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, ← map_inv,
      orthEmb_mulVec_e₀, hσx]
  have := DVR.finite_vec (ι := Fin (n + 1)) (NF.π v) hπ (f + 1)
  refine Finite.of_injective (fun t => DVR.redI (NF.π v) (f + 1) (x t)) fun t t' htt => ?_
  have hdv := (DVR.redI_eq_iff _ _ _ _).mp htt
  have hQa : Qo.eval (x t) = mo := hx t
  have hQa' : Qo.eval (x t') = mo := hx t'
  obtain ⟨T, hT, hTa, -⟩ := exists_openMat hπ Qo hmo hf hf' (s := f + 1) le_rfl hQa hQa'
    (fun i => by rw [← dvd_neg, neg_sub]; exact hdv i)
  obtain ⟨τ, hτ⟩ := exists_intRep_eq v (hQo v m₀ Q₀') hQnd T hT
  have hκ₂ : ρ τ *ᵥ x t = x t' := by rw [hτ, hTa]
  have hmem := mem_orbit_of_stdStab v mF QF' hmF (locRep v mF QF' t) (locRep v mF QF' t') (g t) (g t')
    (hloc t) (hloc t') τ (by rw [hginv, hginv, ← coe_intRep_mulVec, hκ₂])
  have : (Quotient.mk'' (locRep v mF QF' t') : LocTypes v mF QF') = Quotient.mk'' (locRep v mF QF' t) :=
    Quotient.sound' hmem
  rw [locRep_mk, locRep_mk] at this
  exact this.symm

end Types

section Bridge

/-- The identification `O(⟨m⟩ ⊥ Q') = O(Q)` of the two descriptions of the form. -/
def ofS (m₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n) :
    orthGroup (splitForm (mm m₀) (QQ' Q₀')) (v.adicCompletion F) →* orthGroup (QQ m₀ Q₀') (v.adicCompletion F) :=
  Subgroup.inclusion (FibreO.orthGroup_le_of_eq v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀'))

theorem ofS_coe (m₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n) (g : orthGroup (splitForm (mm m₀) (QQ' Q₀')) (v.adicCompletion F)) :
    ((ofS v m₀ Q₀' g : orthGroup (QQ m₀ Q₀') (v.adicCompletion F)) : GL (Fin (n + 1)) (v.adicCompletion F)) =
      (g : GL (Fin (n + 1)) (v.adicCompletion F)) := by
  simp [ofS]

/-- The inverse identification. -/
def toS (m₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n) :
    orthGroup (QQ m₀ Q₀') (v.adicCompletion F) →* orthGroup (splitForm (mm m₀) (QQ' Q₀')) (v.adicCompletion F) :=
  Subgroup.inclusion (fun _ hg => FibreO.mem_orth_of_eq' v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') hg)

theorem toS_coe (m₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n) (g : orthGroup (QQ m₀ Q₀') (v.adicCompletion F)) :
    ((toS v m₀ Q₀' g : orthGroup (splitForm (mm m₀) (QQ' Q₀')) (v.adicCompletion F)) :
      GL (Fin (n + 1)) (v.adicCompletion F)) = (g : GL (Fin (n + 1)) (v.adicCompletion F)) := by
  simp [toS]

end Bridge

section Decomp

variable (m₀ : 𝓞 F) (hm : m₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) n) (hQ' : Q₀'.Nondegenerate) (hn : 1 ≤ n)

/-- The orbit section of `O(V)(F_v)` on the quadric. -/
abbrev sect : Weil.OrbitSection (orthGroup (QQ m₀ Q₀') Fv) (FibreO.sphereSet v (QQ m₀ Q₀') (mm m₀)) :=
  FibreO.orbitSection v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀') (mm_ne m₀ hm) (QQ'_nondeg Q₀' hQ') hn

/-- `g⁻¹ K g`, `K = O(L_v)`. -/
abbrev conjK (g : orthGroup (QQ m₀ Q₀') Fv) : Subgroup (orthGroup (QQ m₀ Q₀') Fv) :=
  (stdStab (QQ m₀ Q₀') v).map (MulAut.conj g⁻¹).toMonoidHom

/-- `ι : O(Q') → O(Q)`. -/
abbrev iotaP : orthGroup (QQ' Q₀') Fv →* orthGroup (QQ m₀ Q₀') Fv :=
  FibreO.iota v (QQ m₀ Q₀') (mm m₀) (QQ' Q₀') (hEE m₀ Q₀')

theorem mem_conjK_iff (g x : orthGroup (QQ m₀ Q₀') Fv) :
    x ∈ conjK v m₀ Q₀' g ↔ g * x * g⁻¹ ∈ stdStab (QQ m₀ Q₀') v := by
  simp only [conjK, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y := by group
    rw [this]; exact hy
  · intro hx; exact ⟨g * x * g⁻¹, hx, by group⟩

theorem commens_std_stab (M : LocCompSet v (mm m₀) (QQ' Q₀')) :
    Commens (stdStab (QQ' Q₀') v) (stabilizer (orthGroup (QQ' Q₀') Fv) M) := by
  set ψ : orthGroup (QQ' Q₀') Fv →* GL (Fin (n + 1)) Fv :=
    (orthGroup (splitForm (mm m₀) (QQ' Q₀')) Fv).subtype.comp (orthEmb (mm m₀) (QQ' Q₀') Fv)
  have hstab : ∀ N : LocCompSet v (mm m₀) (QQ' Q₀'),
      stabilizer (orthGroup (QQ' Q₀') Fv) N = stabLat v ψ N.1 := by
    intro N
    ext g
    rw [mem_stabilizer_iff]
    constructor
    · intro hg; exact congrArg Subtype.val hg
    · intro hg; exact Subtype.ext hg
  have hlat : ∀ N : LocCompSet v (mm m₀) (QQ' Q₀'), N.1.IsLattice Fv := by
    intro N
    obtain ⟨g, hg⟩ := N.2.1
    rw [← hg]; exact locAct_isLattice _ (std_isLattice v)
  have hK₀ : stdStab (QQ' Q₀') v = stabLat v ψ (locStdPt v (mm m₀) (QQ' Q₀')).1 := by
    rw [← hstab, stabilizer_locStdPt]
  rw [hK₀, hstab]
  exact commens_stabLat v ψ (hlat _) (hlat _)

/-- **The `K`-orbits on `{Q = m} ∩ L_v` are the local types.** -/
@[kb "weil1982" "§3.4 (K-orbits on lattice points = local types) [unverified]"]
theorem exists_orbit_decomp :
    ∃ (Tp : Type) (_ : Fintype Tp) (γ : Tp → orthGroup (QQ m₀ Q₀') Fv) (w : Tp → ℝ),
      (∀ t, ((γ t • (sect v m₀ hm Q₀' hQ' hn).base : FibreO.sphereSet v (QQ m₀ Q₀') (mm m₀)) :
        Fin (n + 1) → Fv) ∈ std v) ∧
      (∀ t t' (κ : orthGroup (QQ m₀ Q₀') Fv), κ ∈ stdStab (QQ m₀ Q₀') v →
        κ • (γ t • (sect v m₀ hm Q₀' hQ' hn).base) = γ t' • (sect v m₀ hm Q₀' hQ' hn).base → t = t') ∧
      (∀ y : FibreO.sphereSet v (QQ m₀ Q₀') (mm m₀), (y : Fin (n + 1) → Fv) ∈ std v →
        ∃ t, ∃ κ ∈ stdStab (QQ m₀ Q₀') v, κ • (γ t • (sect v m₀ hm Q₀' hQ' hn).base) = y) ∧
      (∀ t, Commens (stdStab (QQ' Q₀') v) ((conjK v m₀ Q₀' (γ t)).comap (iotaP v m₀ Q₀')) ∧
        w t = relRatio (stdStab (QQ' Q₀') v) ((conjK v m₀ Q₀' (γ t)).comap (iotaP v m₀ Q₀'))) ∧
      ∑ t, w t = locTypeSum v (mm m₀) (QQ' Q₀') := by
  classical
  set mF := mm m₀
  set QF' := QQ' Q₀'
  have hmF : mF ≠ 0 := mm_ne m₀ hm
  have hfin := locTypes_finite v m₀ hm Q₀' hQ'
  letI : Fintype (LocTypes v mF QF') := Fintype.ofFinite _
  choose x σ h hx hσ hσx hloc using fun t : LocTypes v mF QF' =>
    exists_type_data v mF QF' hmF (hQo v m₀ Q₀') (hmoF v m₀ Q₀') (locRep v mF QF' t)
  set g : LocTypes v mF QF' → orthGroup (splitForm mF QF') (v.adicCompletion F) :=
    fun t => orthEmb mF QF' (v.adicCompletion F) (h t) * σ t with hgdef
  have hginv : ∀ t, ((g t)⁻¹ : orthGroup (splitForm mF QF') (v.adicCompletion F)).val.val *ᵥ
      (e₀ : Fin (n + 1) → v.adicCompletion F) = fun i => (x t i : v.adicCompletion F) := by
    intro t
    have hσi : (σ t)⁻¹ = σ t := inv_eq_of_mul_eq_one_right (hσ t)
    simp only [hgdef, _root_.mul_inv_rev, hσi, Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, ← map_inv,
      orthEmb_mulVec_e₀, hσx]
  refine ⟨LocTypes v mF QF', inferInstance, fun t => ofS v m₀ Q₀' (g t)⁻¹, fun t => locWeight v mF QF' (locRep v mF QF' t),
    ?_, ?_, ?_, ?_, ?_⟩
  · -- the points lie in the lattice
    intro t
    rw [FibreO.smul_base_val, ofS_coe, hginv t]
    exact coe_mem_std v (x t)
  · -- disjointness of the orbits
    intro t t' κ hκ hκe
    have hvec := congrArg Subtype.val hκe
    rw [FibreO.smul_val, FibreO.smul_base_val, FibreO.smul_base_val, ofS_coe, ofS_coe] at hvec
    have hκS : toS v m₀ Q₀' κ ∈ stdStab (splitForm mF QF') v := by
      show locAct v ((toS v m₀ Q₀' κ : orthGroup (splitForm mF QF') Fv) : GL (Fin (n + 1)) Fv) (std v) = std v
      rw [toS_coe]; exact hκ
    have hmem := mem_orbit_of_stdStab v mF QF' hmF (locRep v mF QF' t) (locRep v mF QF' t') (g t) (g t')
      (hloc t) (hloc t') ⟨toS v m₀ Q₀' κ, hκS⟩ (by
        show ((toS v m₀ Q₀' κ : orthGroup (splitForm mF QF') Fv) : GL (Fin (n + 1)) Fv).val *ᵥ _ = _
        rw [toS_coe]; exact hvec)
    have : (Quotient.mk'' (locRep v mF QF' t') : LocTypes v mF QF') = Quotient.mk'' (locRep v mF QF' t) :=
      Quotient.sound' hmem
    rw [locRep_mk, locRep_mk] at this
    exact this.symm
  · -- every lattice point is in the orbit of some `x_t`
    intro y hy
    have hQy : (splitForm mF QF').evalIn (v.adicCompletion F) (y : Fin (n + 1) → Fv) =
        algebraMap F (v.adicCompletion F) mF := by
      rw [hsplitF m₀ Q₀']; exact y.2
    obtain ⟨σy, hσy, hσye⟩ := exists_inv_e₀ v mF QF' hmF _ hQy
    have hystd : (σy : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) ∈ std v := by
      rw [hσye]; exact hy
    set M := sigmaPt v mF QF' σy hσy hystd
    set t : LocTypes v mF QF' := Quotient.mk'' M
    obtain ⟨h', hh'⟩ : locRep v mF QF' t ∈ MulAction.orbit (orthGroup QF' (v.adicCompletion F)) M :=
      Quotient.exact' (locRep_mk v mF QF' t)
    set φ := orthEmb mF QF' (v.adicCompletion F)
    set κo : orthGroup (splitForm mF QF') (v.adicCompletion F) := σy * (φ h')⁻¹ * g t with hκo
    have hσyσy : locAct v (σy : GL (Fin (n + 1)) Fv) (locAct v (σy : GL (Fin (n + 1)) Fv) (std v)) = std v :=
      locAct_sigma_sigma v mF QF' σy hσy _
    have hκK : κo ∈ stdStab (splitForm mF QF') v := by
      show locAct v (κo : GL (Fin (n + 1)) Fv) (std v) = std v
      have h1 : locAct v ((g t : orthGroup _ _) : GL (Fin (n + 1)) Fv) (std v) =
          locAct v ((φ h' : orthGroup _ _) : GL (Fin (n + 1)) Fv)
            (locAct v (σy : GL (Fin (n + 1)) Fv) (std v)) := by
        rw [hloc t, ← hh']; rfl
      simp only [hκo, Subgroup.coe_mul, Subgroup.coe_inv, locAct_mul]
      rw [h1, locAct_inv_locAct, hσyσy]
    refine ⟨t, ofS v m₀ Q₀' κo, ?_, ?_⟩
    · show locAct v ((ofS v m₀ Q₀' κo : orthGroup (QQ m₀ Q₀') Fv) : GL (Fin (n + 1)) Fv) (std v) = std v
      rw [ofS_coe]; exact hκK
    · apply Subtype.ext
      rw [FibreO.smul_val, FibreO.smul_base_val, ofS_coe, ofS_coe]
      have hgx : ((g t : orthGroup (splitForm mF QF') Fv) : GL (Fin (n + 1)) Fv).val *ᵥ
          ((((g t)⁻¹ : orthGroup (splitForm mF QF') Fv) : GL (Fin (n + 1)) Fv).val *ᵥ
            (e₀ : Fin (n + 1) → Fv)) = e₀ := by
        rw [mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; simp
      have hinvfix : (((φ h' : orthGroup _ _) : GL (Fin (n + 1)) Fv)⁻¹).val *ᵥ (e₀ : Fin (n + 1) → Fv) = e₀ := by
        conv_lhs => rw [← orthEmb_mulVec_e₀ mF QF' _ h']
        rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel]; simp
      simp only [Subgroup.coe_inv] at hgx
      simp only [hκo, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, ← mulVec_mulVec, hgx]
      rw [hinvfix, hσye]
  · -- the weights
    intro t
    have hset : (conjK v m₀ Q₀' (ofS v m₀ Q₀' (g t)⁻¹)).comap (iotaP v m₀ Q₀') =
        stabilizer (orthGroup QF' Fv) (locRep v mF QF' t) := by
      ext h'
      rw [Subgroup.mem_comap, mem_conjK_iff, mem_stabilizer_iff]
      show _ ∈ stdStab (QQ m₀ Q₀') v ↔ _
      have hM : (locRep v mF QF' t).1 = locAct v ((g t : orthGroup (splitForm mF QF') Fv) : GL (Fin (n + 1)) Fv) (std v) :=
        (hloc t).symm
      have hcoe : ((ofS v m₀ Q₀' (g t)⁻¹ * iotaP v m₀ Q₀' h' * (ofS v m₀ Q₀' (g t)⁻¹)⁻¹ :
          orthGroup (QQ m₀ Q₀') Fv) : GL (Fin (n + 1)) Fv) =
          ((g t : orthGroup (splitForm mF QF') Fv) : GL (Fin (n + 1)) Fv)⁻¹ *
            (orthEmb mF QF' Fv h' : GL (Fin (n + 1)) Fv) *
            ((g t : orthGroup (splitForm mF QF') Fv) : GL (Fin (n + 1)) Fv) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, ofS_coe, FibreO.iota_coe, inv_inv]
        rfl
      show locAct v ((_ : orthGroup (QQ m₀ Q₀') Fv) : GL (Fin (n + 1)) Fv) (std v) = std v ↔ _
      rw [hcoe, locAct_mul, locAct_mul, locAct_eq_iff, inv_inv, ← hM]
      constructor
      · intro hL
        exact Subtype.ext (by rw [LocCompSet.smul_val]; exact hL)
      · intro hL
        have := congrArg Subtype.val hL
        rw [LocCompSet.smul_val] at this
        exact this
    rw [hset]
    exact ⟨commens_std_stab v m₀ Q₀' _, rfl⟩
  · rw [locTypeSum, finsum_eq_sum_of_fintype]

end Decomp

end QuadFormsKB.Tamagawa.Measure.FibreDecomp
