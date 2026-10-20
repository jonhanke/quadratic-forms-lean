/-
# $\mu_{PD}(\operatorname{pd}(H_S)) = \mu^{SO(D^0)}_{\mathrm{Tam}}(G_\infty\times\mathrm{box})$

**Layer:** a totally real number field $F$, $a, b\in\mathcal O_F\setminus0$ with $\langle-a,-b,ab\rangle$ totally positive definite;
$S$, $m_v$ as in `GnatSqImage.lean`.

* **`coe_map_quatCongS`**: $c(H_S^{\mathrm{fin}}) = \prod_{v\in S}K_{m_v}\times\prod_{v\notin S}SO(L^0_v)$ inside $SO(D^0)(\mathbb A_f)$
  (`coe_map_quatCong` for an arbitrary finite $S$ off which $|2ab|_v = 1$, and arbitrary admissible levels).
* **`muPD_pdMk_HS`**: $\mu_{PD}(\operatorname{pd}(H_S)) = \mu^{\langle-a,-b,ab\rangle}_{\mathrm{Tam}}(G_\infty\times\mathrm{box})$, from
  `map_muPD_pdAdeleEquiv`.

Source: Weil 1982, §3.7(a), p. 63 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqImage
import QuadFormsKB.Tamagawa.Measure.Weil.PDMeasureEq

open Matrix NumberField NumberField.InfinitePlace IsDedekindDomain WithZero MeasureTheory Set Filter Function
open scoped ENNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices LerayPadic

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}

local notation "Q₃" => QuatZeta.pureFormO a b
local notation "QF₃" => QuadForm.map (algebraMap (𝓞 F) F) (QuatZeta.pureFormO a b)

theorem isOpen_oneAddCong (v : HeightOneSpectrum (𝓞 F)) (a b : 𝓞 F) {m : ℕ} (hm : 1 ≤ m) :
    IsOpen (oneAddCong v a b m : Set (QuatV (a : F) (b : F) v)ˣ) := by
  set L : Set (v.adicCompletion F) := (Analysis.latticeV v (m : ℤ) : Set (v.adicCompletion F))
  set L1 : Set (v.adicCompletion F) := (fun x => x - 1) ⁻¹' L
  have hLo : IsOpen L := LerayPadic.isOpen_latticeV v m
  have hL1o : IsOpen L1 := hLo.preimage (continuous_id.sub continuous_const)
  set T : Set (Fin 4 → v.adicCompletion F) := Set.univ.pi ![L1, L, L, L]
  have hT : ∀ x : QuatV (a : F) (b : F) v, quatLocCoord _ _ x ∈ T ↔ QSmall (exp (-(m : ℤ))) (x - 1) := by
    intro x
    simp only [T, Set.mem_univ_pi, Fin.forall_fin_succ, IsEmpty.forall_iff, and_true]
    simp [QuaternionAlgebra.linearEquivTuple, QSmall, L1, L, Analysis.mem_latticeV]
    tauto
  have hset : (oneAddCong v a b m : Set (QuatV (a : F) (b : F) v)ˣ) =
      Units.val ⁻¹' (quatLocCoord _ _ ⁻¹' T) := by
    ext u; simp only [SetLike.mem_coe, Set.mem_preimage, hT, mem_oneAddCong_iff v a b hm]
  have hTo : IsOpen T := isOpen_set_pi (Set.finite_univ) fun i _ => by
    fin_cases i
    · exact hL1o
    · exact hLo
    · exact hLo
    · exact hLo
  rw [hset]
  exact (hTo.preimage (continuous_quatLocCoord _ _)).preimage Units.continuous_val

section Box

variable (ha : a ≠ 0) (hb : b ≠ 0) (S : Finset (HeightOneSpectrum (𝓞 F)))
  (m : HeightOneSpectrum (𝓞 F) → ℕ) (hm1 : ∀ v, 1 ≤ m v)

theorem isOpen_quatCongS : IsOpen (quatCongS a b S m hm1 : Set (QuatFin (a : F) (b : F))ˣ) := by
  rw [quatCongS, Subgroup.coe_inf]
  refine (isOpen_lamHatUnits (a : F) (b : F)).inter ?_
  simp only [Subgroup.coe_iInf]
  exact isOpen_biInter_finset fun v _ => (isOpen_lamCong v (m v) (hm1 v)).preimage (continuous_unitAtQ _ _ v)

include hm1 in
theorem isOpen_econgS : IsOpen (econgS a b S m : Set (QuatFin (a : F) (b : F))ˣ) := by
  rw [econgS, Subgroup.coe_inf]
  refine (isOpen_lamHatUnits (a : F) (b : F)).inter ?_
  simp only [Subgroup.coe_iInf]
  refine isOpen_biInter_finset fun v _ => ?_
  exact (isOpen_oneAddCong v a b (hm1 v)).preimage (continuous_unitAtQ _ _ v)

/-- The local sets $K_{m_v}\subseteq SO(D^0)(F_v)$. -/
def congSO3S (v : HeightOneSpectrum (𝓞 F)) : Set (Measure.SOv v Q₃) :=
  Subtype.val ⁻¹' (congSub v Q₃ (m v) (hm1 v) : Set (orthGroup QF₃ (v.adicCompletion F)))

include hb in
/-- **$c(H_S) = \prod_{v\in S}K_{m_v}\times\prod_{v\notin S}SO(L^0_v)$.** -/
theorem coe_map_quatCongS
    (hS : ∀ v ∉ S, Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1)
    (hmS : ∀ v ∈ S, 2 * sExp v < m v ∧ sExp v + eExp a ha v ≤ m v) :
    ((quatCongS a b S m hm1).map (conjFin a b) : Set (SOAf Q₃)) =
      QuadFormsKB.Tamagawa.Measure.boxSO Q₃ S (congSO3S m hm1) := by
  have hA : (a : F) ≠ 0 := by exact_mod_cast ha
  have hB : (b : F) ≠ 0 := by exact_mod_cast hb
  ext g
  simp only [SetLike.mem_coe, Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨hu1, hu2⟩ := (mem_quatCongS a b S m hm1).1 hu
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · exact (hu2 v hv).1
    · exact conjOrth_mem_stdStab v (hQF a b) (intA a v) (intA b v) (hu1 v)
  · rintro ⟨hSg, hnS⟩
    have hlift : ∀ v, ∃ β : (QuatV (a : F) (b : F) v)ˣ, conjOrth QF₃ (hQF a b) β = (g : OAf QF₃) v ∧
        β ∈ lamLocUnits (a : F) (b : F) v ∧ (v ∈ S → β ∈ lamCong v a b (m v) (hm1 v)) := by
      intro v
      by_cases hv : v ∈ S
      · have hg : (g : OAf QF₃) v ∈ LerayPadic.congSub v Q₃ (m v) (hm1 v) := hSg v hv
        rw [← map_lamCong v a b ha hb (valued_two_eq v) (valued_eExp a ha v) (hmS v hv).1 (hmS v hv).2
          (hm1 v)] at hg
        obtain ⟨β, hβ, hβg⟩ := hg
        exact ⟨β, hβg, hβ.2, fun _ => hβ⟩
      · obtain ⟨h2, hav, hbv⟩ := hS v hv
        have hst : (g : OAf QF₃) v ∈ stdStab QF₃ v := hnS v hv
        obtain ⟨α, hα⟩ := conjSOK_surjective (K := v.adicCompletion F) QF₃ (hQF a b) hA hB ⟨(g : OAf QF₃) v, g.2 v⟩
        have hαg : conjOrth QF₃ (hQF a b) α = (g : OAf QF₃) v := congrArg Subtype.val hα
        have hint : ∀ i j, Valued.v (((conjGL α : GL (Fin 3) (v.adicCompletion F)) :
            Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) i j) ≤ 1 := by
          intro i j
          have := entry_le_one_of_mem_stdStab v hst i j
          rwa [← hαg] at this
        obtain ⟨r, hr⟩ := exists_smul_mem_lamLocUnits v (intA a) (intA b) h2 hav hbv α hint
        refine ⟨_, ?_, hr, fun h => absurd h hv⟩
        rw [← hαg]
        ext : 2
        exact congrArg Units.val (conjGL_smul α r)
    choose β hβg hβL hβS using hlift
    obtain ⟨α, hα⟩ := exists_quatFin_of_local (a : F) (b : F) β hβL
    refine ⟨α, (mem_quatCongS a b S m hm1).2 ⟨fun v => by rw [hα]; exact hβL v,
      fun v hv => by rw [hα]; exact hβS v hv⟩, ?_⟩
    ext v : 2
    rw [conjFin_apply, hα, hβg]

theorem pdAdeleEquiv_preimage_box
    (hS : ∀ v ∉ S, Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1)
    (hmS : ∀ v ∈ S, 2 * sExp v < m v ∧ sExp v + eExp a ha v ≤ m v) :
    pdAdeleEquiv a b ha hb ⁻¹' (univ ×ˢ QuadFormsKB.Tamagawa.Measure.boxSO Q₃ S (congSO3S m hm1)) =
      pdMk (a : F) (b : F) '' (HS a b S m hm1 : Set (QuatAdele (a : F) (b : F))ˣ) := by
  rw [← coe_map_quatCongS ha hb S m hm1 hS hmS]
  ext q
  obtain ⟨x, rfl⟩ := pdMk_surjective (a : F) (b : F) q
  rw [mem_preimage, show pdMk (a : F) (b : F) x = (QuotientGroup.mk x : PDAdele a b) from rfl, pdAdeleEquiv_mk,
    conjAdele_apply, mem_prod]
  simp only [mem_univ, true_and, SetLike.mem_coe, Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, hux⟩
    set x' := (quatUnitsEquiv (a : F) (b : F)).symm ((quatUnitsEquiv (a : F) (b : F) x).1, u)
    have hx'f : (quatUnitsEquiv (a : F) (b : F) x').2 = u := by simp [x']
    have hx'i : (quatUnitsEquiv (a : F) (b : F) x').1 = (quatUnitsEquiv (a : F) (b : F) x).1 := by simp [x']
    refine ⟨x', (show (quatUnitsEquiv (a : F) (b : F) x').2 ∈ quatCongS a b S m hm1 by rw [hx'f]; exact hu), ?_⟩
    apply (pdAdeleEquiv a b ha hb).injective
    change pdAdeleEquiv a b ha hb (QuotientGroup.mk x' : PDAdele a b) =
      pdAdeleEquiv a b ha hb (QuotientGroup.mk x : PDAdele a b)
    rw [pdAdeleEquiv_mk, pdAdeleEquiv_mk, conjAdele_apply, conjAdele_apply, hx'f, hx'i, hux]
  · rintro ⟨x', hx', hxx⟩
    have he := congrArg (pdAdeleEquiv a b ha hb) hxx
    change pdAdeleEquiv a b ha hb (QuotientGroup.mk x' : PDAdele a b) =
      pdAdeleEquiv a b ha hb (QuotientGroup.mk x : PDAdele a b) at he
    rw [pdAdeleEquiv_mk, pdAdeleEquiv_mk, conjAdele_apply, conjAdele_apply] at he
    exact ⟨_, hx', (congrArg Prod.snd he)⟩

variable [IsTotallyReal F]

include hb in
/-- **$\mu_{PD}(\operatorname{pd}(H_S)) = \mu^{SO(D^0)}_{\mathrm{Tam}}(G_\infty\times\mathrm{box})$** (totally definite $D$). -/
@[kb "weil1982" "Thm 3.2.1, p. 43; §3.7(a), p. 63 [unverified page]"]
theorem muPD_pdMk_HS (hQ : (Q₃).Nondegenerate) (hpd : IsTotallyPosDef (QuadFormsKB.HilbertModular.formF Q₃))
    (hdiv : ∀ ξ : ℍ[F,(a : F),(b : F)], ξ ≠ 0 → IsUnit ξ)
    (hS : ∀ v ∉ S, Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1)
    (hmS : ∀ v ∈ S, 2 * sExp v < m v ∧ sExp v + eExp a ha v ≤ m v) :
    muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha) (by simpa using hb)
        (pdMk (a : F) (b : F) '' (HS a b S m hm1 : Set (QuatAdele (a : F) (b : F))ˣ)) =
      muArchTamSO Q₃ hQ univ *
        QuadFormsKB.Tamagawa.Measure.muFin Q₃ (fun _ => 1)
          (QuadFormsKB.Tamagawa.Measure.boxSO Q₃ S (congSO3S m hm1)) := by
  have hbox_m : MeasurableSet (QuadFormsKB.Tamagawa.Measure.boxSO Q₃ S (congSO3S m hm1)) := by
    rw [← coe_map_quatCongS ha hb S m hm1 hS hmS]
    exact (isOpen_map_conjFin ha hb (isOpen_quatCongS S m hm1)).measurableSet
  rw [← pdAdeleEquiv_preimage_box ha hb S m hm1 hS hmS, ← Measure.map_apply
    (map_continuous (pdAdeleEquiv a b ha hb)).measurable (MeasurableSet.univ.prod hbox_m),
    map_muPD_pdAdeleEquiv ha hb hQ hpd hdiv, muTam, Measure.prod_prod]

end Box

end QuadFormsKB.Tamagawa.Measure.Weil
