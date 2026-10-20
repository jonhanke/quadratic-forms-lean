/-
# $\Phi(\pi(S_0)) = G_\infty\times\prod_{v\in S}K_{m_v}\times\prod_{v\notin S}SO(L_v)$

**Layer:** a number field $F$, $a, b\in\mathcal O_F\setminus0$, the square model and its isomorphism
$\Phi$ = `sqPEquiv : P ≃ₜ* SO(⟨1,-a,-b,ab⟩)(𝔸)`. Data: a finite set $S$ of finite places containing every $v$ with
$|2abv|\ne1$, and levels $m_v$ ($v\in S$) with $2s_v < m_v$, $s_v + e_a(v)\le m_v$.

* `quatCongS` $\le\hat\Lambda^\times$: $u_v\in\Lambda_v^\times$ ($v\notin S$), $u_v\in\Lambda^{(m_v)}_v$ (`lamCong`, $v\in S$);
  `econgS`: $u_v\in\Lambda_v^\times$ ($v\notin S$), $u_v\in1+\pi^{m_v}\Lambda_v$ ($v\in S$);
  `HS`, `ES` $\le(D\otimes\mathbb A)^\times$: the finite part in `quatCongS`, `econgS` (no archimedean condition).
* `HS` normalizes `ES` (`HS_normalizes_ES`), both are open.
* **`sqPEquiv_preimage_box`**: $\Phi^{-1}(G_\infty\times\mathrm{box}) = \pi(S_0(H_S, E_S))$, `box` = `boxSO (qSq a b) S K_m`.

*Proof.* $\supseteq$: the local images (`sqSOK_mem_congSub`, `sqSOK_mem_stdStab`). $\subseteq$: rescale the local
components of a lift by scalars (`exists_smul_of_sqSOK_mem_congSub`, `exists_smul_mem_lamLocUnits_sq`); all rescaled
components are integral units, so they assemble (`mkAdeleUnit`), and the scalars do not change $\Phi$.

Source: Weil 1982, §3.7, p. 65 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqCongLocal
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqFibration
import QuadFormsKB.Tamagawa.Measure.Weil.PDFinRatio

open Matrix NumberField NumberField.InfinitePlace IsDedekindDomain WithZero MeasureTheory Set Filter Function
open scoped ENNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices LerayPadic QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Siegel
  QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}

/-! ### Local normalization -/

theorem oneAddCong_normal (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) {h e : (QuatV (a : F) (b : F) v)ˣ}
    (hh : h ∈ lamLocUnits (a : F) (b : F) v) (he : e ∈ oneAddCong v a b m) :
    h * e * h⁻¹ ∈ oneAddCong v a b m := by
  refine ⟨lamLocUnits_mul_mem (fun w => valued_algebraMap_le_one a w) (fun w => valued_algebraMap_le_one b w)
    (lamLocUnits_mul_mem (fun w => valued_algebraMap_le_one a w) (fun w => valued_algebraMap_le_one b w) hh he.1)
      ⟨hh.2, by rw [inv_inv]; exact hh.1⟩, ?_⟩
  have h1 := qSmall_one_of_lamLocUnits hh
  rw [show ((h * e * h⁻¹ : (QuatV (a : F) (b : F) v)ˣ) : QuatV (a : F) (b : F) v) - 1 =
    (h : QuatV (a : F) (b : F) v) * ((e : QuatV (a : F) (b : F) v) - 1) *
      ((h⁻¹ : (QuatV (a : F) (b : F) v)ˣ) : QuatV (a : F) (b : F) v) by
      rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.mul_inv]]
  exact QSmall.mul_right (valuedA v a) (valuedB v b)
    (QSmall.mul_left (valuedA v a) (valuedB v b) h1.1 he.2) h1.2

theorem scal_comm {K : Type*} [Field K] {A B : K} (r : Kˣ) (x : (ℍ[K,A,B])ˣ) :
    Units.map (algebraMap K ℍ[K,A,B]).toMonoidHom r * x = x * Units.map (algebraMap K ℍ[K,A,B]).toMonoidHom r :=
  Units.ext (Algebra.commutes (r : K) (x : ℍ[K,A,B]))

theorem scal_mul_inv_scal {K : Type*} [Field K] {A B : K} (r : Kˣ) (x y : (ℍ[K,A,B])ˣ) :
    (Units.map (algebraMap K ℍ[K,A,B]).toMonoidHom r * x) *
      (Units.map (algebraMap K ℍ[K,A,B]).toMonoidHom r * y)⁻¹ = x * y⁻¹ := by
  have h1 := scal_comm r x
  have h2 := scal_comm r y⁻¹
  generalize Units.map (algebraMap K ℍ[K,A,B]).toMonoidHom r = s at h1 h2 ⊢
  calc (s * x) * (s * y)⁻¹ = x * (s * y⁻¹) * s⁻¹ := by rw [h1]; group
    _ = x * (y⁻¹ * s) * s⁻¹ := by rw [h2]
    _ = x * y⁻¹ := by group

theorem scal_eq_mul {K : Type*} [Field K] {A B : K} (r : Kˣ) (x y : (ℍ[K,A,B])ˣ) :
    Units.map (algebraMap K ℍ[K,A,B]).toMonoidHom r * x =
      (x * y⁻¹) * (Units.map (algebraMap K ℍ[K,A,B]).toMonoidHom r * y) := by
  have h1 := scal_comm r x
  have h2 := scal_comm r y
  generalize Units.map (algebraMap K ℍ[K,A,B]).toMonoidHom r = s at h1 h2 ⊢
  rw [h2, h1]; group

/-! ### The subgroups -/

section Groups

variable (a b) (S : Finset (HeightOneSpectrum (𝓞 F))) (m : HeightOneSpectrum (𝓞 F) → ℕ) (hm1 : ∀ v, 1 ≤ m v)

/-- $u_v\in\Lambda^\times_v$ off $S$, $u_v\in\Lambda^{(m_v)}_v$ on $S$. -/
def quatCongS : Subgroup (QuatFin (a : F) (b : F))ˣ :=
  lamHatSub a b ⊓ ⨅ v ∈ S, (lamCong v a b (m v) (hm1 v)).comap (unitAtQ _ _ v)

/-- $u_v\in\Lambda^\times_v$ off $S$, $u_v\in1+\pi^{m_v}\Lambda_v$ on $S$. -/
def econgS : Subgroup (QuatFin (a : F) (b : F))ˣ :=
  lamHatSub a b ⊓ ⨅ v ∈ S, (oneAddCong v a b (m v)).comap (unitAtQ _ _ v)

theorem mem_quatCongS {u : (QuatFin (a : F) (b : F))ˣ} :
    u ∈ quatCongS a b S m hm1 ↔ (∀ v, unitAtQ _ _ v u ∈ lamLocUnits (a : F) (b : F) v) ∧
      ∀ v ∈ S, unitAtQ _ _ v u ∈ lamCong v a b (m v) (hm1 v) := by
  simp only [quatCongS, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap]
  exact and_congr_left' (mem_lamHatUnits_iff _ _ u)

theorem mem_econgS {u : (QuatFin (a : F) (b : F))ˣ} :
    u ∈ econgS a b S m ↔ (∀ v, unitAtQ _ _ v u ∈ lamLocUnits (a : F) (b : F) v) ∧
      ∀ v ∈ S, unitAtQ _ _ v u ∈ oneAddCong v a b (m v) := by
  simp only [econgS, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap]
  exact and_congr_left' (mem_lamHatUnits_iff _ _ u)

/-- The finite part $(D\otimes\mathbb A)^\times\to(D\otimes\mathbb A_f)^\times$. -/
abbrev quatFinPart : (QuatAdele (a : F) (b : F))ˣ →* (QuatFin (a : F) (b : F))ˣ :=
  (MonoidHom.snd _ _).comp (quatUnitsEquiv (a : F) (b : F)).toMulEquiv.toMonoidHom

theorem continuous_quatFinPart : Continuous (quatFinPart a b) :=
  continuous_snd.comp (quatUnitsEquiv (a : F) (b : F)).continuous

/-- $H_S = \{x : x_f\in$ `quatCongS`$\}$. -/
def HS : Subgroup (QuatAdele (a : F) (b : F))ˣ := (quatCongS a b S m hm1).comap (quatFinPart a b)

/-- $E_S = \{x : x_f\in$ `econgS`$\}$. -/
def ES : Subgroup (QuatAdele (a : F) (b : F))ˣ := (econgS a b S m).comap (quatFinPart a b)

theorem mem_HS {x : (QuatAdele (a : F) (b : F))ˣ} :
    x ∈ HS a b S m hm1 ↔ (∀ v, unitAtA _ _ v x ∈ lamLocUnits (a : F) (b : F) v) ∧
      ∀ v ∈ S, unitAtA _ _ v x ∈ lamCong v a b (m v) (hm1 v) :=
  mem_quatCongS a b S m hm1

theorem mem_ES {x : (QuatAdele (a : F) (b : F))ˣ} :
    x ∈ ES a b S m ↔ (∀ v, unitAtA _ _ v x ∈ lamLocUnits (a : F) (b : F) v) ∧
      ∀ v ∈ S, unitAtA _ _ v x ∈ oneAddCong v a b (m v) :=
  mem_econgS a b S m

theorem HS_normalizes_ES : ∀ h ∈ HS a b S m hm1, ∀ e ∈ ES a b S m, h * e * h⁻¹ ∈ ES a b S m := by
  intro h hh e he
  rw [mem_HS] at hh
  rw [mem_ES] at he ⊢
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · rw [map_mul, map_mul, map_inv]
    exact lamLocUnits_mul_mem (fun w => valued_algebraMap_le_one a w) (fun w => valued_algebraMap_le_one b w)
      (lamLocUnits_mul_mem (fun w => valued_algebraMap_le_one a w) (fun w => valued_algebraMap_le_one b w)
        (hh.1 v) (he.1 v)) ⟨(hh.1 v).2, by rw [inv_inv]; exact (hh.1 v).1⟩
  · rw [map_mul, map_mul, map_inv]
    exact oneAddCong_normal v (m v) (hh.1 v) (he.2 v hv)

end Groups

/-! ### The image of $\pi(S_0)$ under $\Phi$ -/

section Image

variable (ha0 : a ≠ 0) (hb0 : b ≠ 0) (S : Finset (HeightOneSpectrum (𝓞 F)))
  (m : HeightOneSpectrum (𝓞 F) → ℕ) (hm1 : ∀ v, 1 ≤ m v)

local notation "Q₀" => qSq a b
local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (qSq a b)

/-- The local sets of the box: $K_{m_v}\subseteq SO(V)(F_v)$. -/
def congSOS (v : HeightOneSpectrum (𝓞 F)) : Set (Measure.SOv v Q₀) :=
  Subtype.val ⁻¹' (congSub v Q₀ (m v) (hm1 v) : Set (orthGroup QF (v.adicCompletion F)))

/-- The compact open subgroup $K' = G_\infty\times\prod_{v\in S}K_{m_v}\times\prod_{v\notin S}SO(L_v)$. -/
def boxK : Set (SOAdele Q₀) := univ ×ˢ QuadFormsKB.Tamagawa.Measure.boxSO Q₀ S (congSOS m hm1)

/-- The pair at `v` after rescaling by a scalar. -/
theorem pairV_scalar_eq (g : (gnatSqO ha0 hb0).G) (v : HeightOneSpectrum (𝓞 F)) (r : (v.adicCompletion F)ˣ)
    (g' : (gnatSqO ha0 hb0).G)
    (h1 : unitAtA (a : F) (b : F) v (gFst ha0 hb0 g') =
      Units.map (algebraMap _ (QuatV (a : F) (b : F) v)).toMonoidHom r * unitAtA (a : F) (b : F) v (gFst ha0 hb0 g))
    (h2 : unitAtA (a : F) (b : F) v (gSnd ha0 hb0 g') =
      Units.map (algebraMap _ (QuatV (a : F) (b : F) v)).toMonoidHom r * unitAtA (a : F) (b : F) v (gSnd ha0 hb0 g)) :
    pairV ha0 hb0 v g' = scalarPair r * pairV ha0 hb0 v g :=
  Subtype.ext (Prod.ext h1 h2)

theorem sqAdele_mem_boxK (g : (gnatSqO ha0 hb0).G)
    (hg : g ∈ sqS0 ha0 hb0 (HS a b S m hm1) (ES a b S m) (HS_normalizes_ES a b S m hm1)) :
    sqAdele ha0 hb0 g ∈ boxK S m hm1 := by
  have ha' : (a : F) ≠ 0 := coe_ne_zero' ha0
  have hgβ := (mem_HS a b S m hm1).1 hg.1
  have hgγ := (mem_ES a b S m).1 hg.2
  rw [boxK, mem_prod]
  refine ⟨mem_univ _, ?_⟩
  change sqFin ha0 hb0 g ∈ QuadFormsKB.Tamagawa.Measure.boxSO Q₀ S (congSOS m hm1)
  have e : ∀ v, ((QuadFormsKB.Tamagawa.Measure.evalSO Q₀ v (sqFin ha0 hb0 g) : Measure.SOv v Q₀) :
      orthGroup QF (v.adicCompletion F)) = (sqSOK _ ha' (pairV ha0 hb0 v g) : orthGroup QF _) :=
    fun v => sqFin_apply ha0 hb0 g v
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · show ((QuadFormsKB.Tamagawa.Measure.evalSO Q₀ v (sqFin ha0 hb0 g) : Measure.SOv v Q₀) :
      orthGroup QF (v.adicCompletion F)) ∈ (congSub v Q₀ (m v) (hm1 v) : Set _)
    rw [e]
    refine sqSOK_mem_congSub ha' (m v) (hm1 v) _ (hgβ.2 v hv) ?_
    have := hgγ.2 v hv
    rwa [map_mul, map_inv] at this
  · show ((QuadFormsKB.Tamagawa.Measure.evalSO Q₀ v (sqFin ha0 hb0 g) : Measure.SOv v Q₀) :
      orthGroup QF (v.adicCompletion F)) ∈ stdStab QF v
    rw [e]
    refine sqSOK_mem_stdStab v (fun w => valued_algebraMap_int_le_one w a)
      (fun w => valued_algebraMap_int_le_one w b) ha' _ ?_ (hgβ.1 v)
    have h1 := hgγ.1 v
    rw [map_mul, map_inv] at h1
    have := lamLocUnits_mul_mem (fun w => valued_algebraMap_le_one a w) (fun w => valued_algebraMap_le_one b w)
      h1 (hgβ.1 v)
    rwa [inv_mul_cancel_right] at this


set_option maxHeartbeats 800000 in
/-- Local rescalings of a lift of an element of $K'$. -/
theorem exists_local_rescale
    (hS : ∀ v ∉ S, Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1)
    (hmS : ∀ v ∈ S, 2 * sExp v < m v ∧ sExp v + eExp a ha0 v ≤ m v) (g : (gnatSqO ha0 hb0).G)
    (hbox : sqFin ha0 hb0 g ∈ QuadFormsKB.Tamagawa.Measure.boxSO Q₀ S (congSOS m hm1)) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ r : (v.adicCompletion F)ˣ,
        Units.map (algebraMap _ (QuatV (a : F) (b : F) v)).toMonoidHom r * unitAtA (a : F) (b : F) v (gFst ha0 hb0 g) ∈
          lamLocUnits (a : F) (b : F) v ∧
        Units.map (algebraMap _ (QuatV (a : F) (b : F) v)).toMonoidHom r * unitAtA (a : F) (b : F) v (gSnd ha0 hb0 g) ∈
          lamLocUnits (a : F) (b : F) v ∧
        (v ∈ S → Units.map (algebraMap _ (QuatV (a : F) (b : F) v)).toMonoidHom r *
            unitAtA (a : F) (b : F) v (gSnd ha0 hb0 g) ∈ lamCong v a b (m v) (hm1 v) ∧
          unitAtA (a : F) (b : F) v (gFst ha0 hb0 g) * (unitAtA (a : F) (b : F) v (gSnd ha0 hb0 g))⁻¹ ∈
            oneAddCong v a b (m v)) := by
  have ha' : (a : F) ≠ 0 := coe_ne_zero' ha0
  obtain ⟨hbox1, hbox2⟩ := hbox
  have e : ((QuadFormsKB.Tamagawa.Measure.evalSO Q₀ v (sqFin ha0 hb0 g) : Measure.SOv v Q₀) :
      orthGroup QF (v.adicCompletion F)) = (sqSOK _ ha' (pairV ha0 hb0 v g) : orthGroup QF _) :=
    sqFin_apply ha0 hb0 g v
  by_cases hv : v ∈ S
  · have hp : (sqSOK _ ha' (pairV ha0 hb0 v g) : orthGroup QF _) ∈ congSub v Q₀ (m v) (hm1 v) := by
      have := hbox1 v hv
      change ((QuadFormsKB.Tamagawa.Measure.evalSO Q₀ v (sqFin ha0 hb0 g) : Measure.SOv v Q₀) :
        orthGroup QF (v.adicCompletion F)) ∈ (congSub v Q₀ (m v) (hm1 v) : Set _) at this
      rwa [e] at this
    obtain ⟨hγ, r, hr⟩ := exists_smul_of_sqSOK_mem_congSub ha' (valued_two_eq v) (valued_eExp a ha0 v)
      (hmS v hv).1 (hmS v hv).2 (hm1 v) _ hp
    refine ⟨r, ?_, hr.2, fun _ => ⟨hr, hγ⟩⟩
    have e2 := scal_eq_mul r (unitAtA (a : F) (b : F) v (gFst ha0 hb0 g)) (unitAtA (a : F) (b : F) v (gSnd ha0 hb0 g))
    rw [e2]
    exact lamLocUnits_mul_mem (fun w => valued_algebraMap_le_one a w) (fun w => valued_algebraMap_le_one b w)
      hγ.1 hr.2
  · have hp : (sqSOK _ ha' (pairV ha0 hb0 v g) : orthGroup QF _) ∈ stdStab QF v := by
      have := hbox2 v hv
      change ((QuadFormsKB.Tamagawa.Measure.evalSO Q₀ v (sqFin ha0 hb0 g) : Measure.SOv v Q₀) :
        orthGroup QF (v.adicCompletion F)) ∈ stdStab QF v at this
      rwa [e] at this
    obtain ⟨r, hr1, hr2⟩ := exists_smul_mem_lamLocUnits_sq v (fun w => valued_algebraMap_int_le_one w a)
      (fun w => valued_algebraMap_int_le_one w b) ha' (hS v hv).1 (hS v hv).2.1 (hS v hv).2.2 _ hp
    exact ⟨r, hr1, hr2, fun h => absurd h hv⟩

set_option maxHeartbeats 1600000 in
/-- A rescaled lift in $S_0$. -/
theorem exists_mem_sqS0_of_box
    (hS : ∀ v ∉ S, Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1)
    (hmS : ∀ v ∈ S, 2 * sExp v < m v ∧ sExp v + eExp a ha0 v ≤ m v) (g : (gnatSqO ha0 hb0).G)
    (hbox : sqFin ha0 hb0 g ∈ QuadFormsKB.Tamagawa.Measure.boxSO Q₀ S (congSOS m hm1)) :
    (gnatSqO ha0 hb0).π g ∈
      (gnatSqO ha0 hb0).π '' (sqS0 ha0 hb0 (HS a b S m hm1) (ES a b S m) (HS_normalizes_ES a b S m hm1)) := by
  have ha' : (a : F) ≠ 0 := coe_ne_zero' ha0
  have hloc := exists_local_rescale ha0 hb0 S m hm1 hS hmS g hbox
  choose r hr using hloc
  obtain ⟨α', hα'⟩ : ∃ α' : (QuatAdele (a : F) (b : F))ˣ, α' = mkAdeleUnit (a : F) (b : F)
      (fun w => unitAtR (a : F) (b : F) w (gFst ha0 hb0 g)) (fun w => unitAtC (a : F) (b : F) w (gFst ha0 hb0 g))
      (fun v => Units.map (algebraMap _ (QuatV (a : F) (b : F) v)).toMonoidHom (r v) *
        unitAtA (a : F) (b : F) v (gFst ha0 hb0 g)) (Eventually.of_forall fun v => (hr v).1) := ⟨_, rfl⟩
  obtain ⟨β', hβ'⟩ : ∃ β' : (QuatAdele (a : F) (b : F))ˣ, β' = mkAdeleUnit (a : F) (b : F)
      (fun w => unitAtR (a : F) (b : F) w (gSnd ha0 hb0 g)) (fun w => unitAtC (a : F) (b : F) w (gSnd ha0 hb0 g))
      (fun v => Units.map (algebraMap _ (QuatV (a : F) (b : F) v)).toMonoidHom (r v) *
        unitAtA (a : F) (b : F) v (gSnd ha0 hb0 g)) (Eventually.of_forall fun v => (hr v).2.1) := ⟨_, rfl⟩
  have hαA : ∀ v, unitAtA (a : F) (b : F) v α' = Units.map (algebraMap _ (QuatV (a : F) (b : F) v)).toMonoidHom (r v) *
      unitAtA (a : F) (b : F) v (gFst ha0 hb0 g) := fun v => by rw [hα', unitAtA_mkAdeleUnit]
  have hβA : ∀ v, unitAtA (a : F) (b : F) v β' = Units.map (algebraMap _ (QuatV (a : F) (b : F) v)).toMonoidHom (r v) *
      unitAtA (a : F) (b : F) v (gSnd ha0 hb0 g) := fun v => by rw [hβ', unitAtA_mkAdeleUnit]
  have hαR : ∀ w, unitAtR (a : F) (b : F) w α' = unitAtR (a : F) (b : F) w (gFst ha0 hb0 g) :=
    fun w => by rw [hα', unitAtR_mkAdeleUnit]
  have hβR : ∀ w, unitAtR (a : F) (b : F) w β' = unitAtR (a : F) (b : F) w (gSnd ha0 hb0 g) :=
    fun w => by rw [hβ', unitAtR_mkAdeleUnit]
  have hαC : ∀ w, unitAtC (a : F) (b : F) w α' = unitAtC (a : F) (b : F) w (gFst ha0 hb0 g) :=
    fun w => by rw [hα', unitAtC_mkAdeleUnit]
  have hβC : ∀ w, unitAtC (a : F) (b : F) w β' = unitAtC (a : F) (b : F) w (gSnd ha0 hb0 g) :=
    fun w => by rw [hβ', unitAtC_mkAdeleUnit]
  clear hα' hβ'
  have hnrd : nrdUnit β' = nrdUnit α' := by
    refine nrdUnit_eq_of_local (fun v => ?_) (fun w => ?_) (fun w => ?_)
    · rw [hαA, hβA, Units.val_mul, Units.val_mul]
      simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
      rw [← Algebra.smul_def, ← Algebra.smul_def, nrd_smul, nrd_smul]
      exact congrArg _ (pairV ha0 hb0 v g).2.symm
    · rw [hαR, hβR]; exact (pairR ha0 hb0 w g).2.symm
    · rw [hαC, hβC]; exact (pairC ha0 hb0 w g).2.symm
  let g' : (gnatSqO ha0 hb0).G := ⟨((α', β'), nrdUnit α'), Prod.ext rfl hnrd⟩
  have hgF : gFst ha0 hb0 g' = α' := rfl
  have hgS : gSnd ha0 hb0 g' = β' := rfl
  refine ⟨g', ⟨?_, ?_⟩, ?_⟩
  · rw [mem_HS]
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · change unitAtA _ _ v β' ∈ _
      rw [hβA]; exact (hr v).2.1
    · change unitAtA _ _ v β' ∈ _
      rw [hβA]; exact ((hr v).2.2 hv).1
  · rw [mem_ES]
    have hcancel : ∀ v, unitAtA (a : F) (b : F) v (α' * β'⁻¹) =
        unitAtA (a : F) (b : F) v (gFst ha0 hb0 g) * (unitAtA (a : F) (b : F) v (gSnd ha0 hb0 g))⁻¹ := by
      intro v
      rw [map_mul, map_inv, hαA, hβA, scal_mul_inv_scal]
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · change unitAtA _ _ v (α' * β'⁻¹) ∈ _
      rw [map_mul, map_inv, hαA, hβA]
      exact (lamLocUnitsSub v a b).mul_mem (hr v).1 ((lamLocUnitsSub v a b).inv_mem (hr v).2.1)
    · change unitAtA _ _ v (α' * β'⁻¹) ∈ _
      rw [hcancel]; exact ((hr v).2.2 hv).2
  · apply (sqPEquiv ha0 hb0).injective
    rw [sqPEquiv_mk, sqPEquiv_mk]
    refine Prod.ext (Prod.ext (funext fun w => archSO_ext ?_) (funext fun w => archSOC_ext' ?_)) ?_
    · have hp : pairR ha0 hb0 w g' = pairR ha0 hb0 w g := by
        apply Subtype.ext
        refine Prod.ext ?_ ?_
        · rw [pairR_fst, pairR_fst, hgF, hαR]
        · rw [pairR_snd, pairR_snd, hgS, hβR]
      change ArchSO.incl _ (sqR ha0 hb0 w g') = ArchSO.incl _ (sqR ha0 hb0 w g)
      rw [sqR_incl, sqR_incl, sqGLR_apply, sqGLR_apply, hp]
    · have hp : pairC ha0 hb0 w g' = pairC ha0 hb0 w g := by
        apply Subtype.ext
        refine Prod.ext ?_ ?_
        · rw [pairC_fst, pairC_fst, hgF, hαC]
        · rw [pairC_snd, pairC_snd, hgS, hβC]
      change ArchSOC.incl _ (sqC ha0 hb0 w g') = ArchSOC.incl _ (sqC ha0 hb0 w g)
      rw [sqC_incl, sqC_incl, sqGLC_apply, sqGLC_apply, hp]
    · ext v : 2
      change ((sqFin ha0 hb0 g' : SOAf Q₀) : OAf QF) v = ((sqFin ha0 hb0 g : SOAf Q₀) : OAf QF) v
      rw [sqFin_apply, sqFin_apply, pairV_scalar_eq ha0 hb0 g v (r v) g' (by rw [hgF, hαA]) (by rw [hgS, hβA]),
        sqSOK_scalarPair_mul]

set_option maxHeartbeats 1600000 in
/-- **$\Phi^{-1}(K') = \pi(S_0(H_S,E_S))$.** -/
@[kb "weil1982" "§3.7, p. 65 [unverified page]"]
theorem sqPEquiv_preimage_boxK
    (hS : ∀ v ∉ S, Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1)
    (hmS : ∀ v ∈ S, 2 * sExp v < m v ∧ sExp v + eExp a ha0 v ≤ m v) :
    sqPEquiv ha0 hb0 ⁻¹' boxK S m hm1 =
      (gnatSqO ha0 hb0).π '' (sqS0 ha0 hb0 (HS a b S m hm1) (ES a b S m) (HS_normalizes_ES a b S m hm1)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, rfl⟩ := (gnatSqO ha0 hb0).π_surjective x
    rw [mem_preimage, sqPEquiv_mk, boxK, mem_prod] at hx
    exact exists_mem_sqS0_of_box ha0 hb0 S m hm1 hS hmS g hx.2
  · rintro ⟨g, hg, rfl⟩
    rw [mem_preimage, sqPEquiv_mk]
    exact sqAdele_mem_boxK ha0 hb0 S m hm1 g hg

end Image

end QuadFormsKB.Tamagawa.Measure.Weil
