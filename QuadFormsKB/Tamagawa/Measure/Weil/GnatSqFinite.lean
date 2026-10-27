/-
# The finite-place identity for the square model over every number field

**Layer:** a number field $F$ (no signature condition: complex places allowed), $a, b\in\mathcal O_F\setminus0$ with
$D = (a,b)_F$ arbitrary, $Q_0 = \langle1,-a,-b,ab\rangle$ (`qSq a b`) nondegenerate.

Everything about the finite places in the proof of `map_muP_sqPEquiv_eq_muTam` (totally real, totally definite) is valid
for every number field; only the archimedean identity and the product formula used total reality. This file extracts it.
With $S$ the places where $|2ab|_v\ne1$ and levels $m_v$ (`sqBad`, `sqLev`), write
$M_3 = \mu_f^{(3)}(\mathrm{box}_3)$, $M_4 = \mu_f^{(4)}(\mathrm{box}_4)$, $q_H = \mu_{D^\times}(H_S)$, $q_E = \mu_{D^\times}(E_S)$,
$N = \mu_{G_m}(N_{E})$, $U = \mu_{G_m}(\hat{\mathcal O}^\times)$.

* **`fin_identity_sq`**: $M_4\,N\,q_H\prod_{v\in S}q_v^{3(e_a(v)+e_b(v))} = M_3^2\,q_E\,U$ (real numbers, local ratios
  `local_ratio_sq` and the Euler product `siegelDensity_qSq_good`).
* **`rF_eq_div_quatCongS`**: $r_f = q_H/(U\,M_3)$ (the analogue of `rF_eq_div` for $H_S$).
* **`fin_identity_sq_E`**: $q_E\,M_3 = c_F(3)\,8^{-r_1}\,64^{-r_2}\,N\,M_4$, using $r_f = K_\infty$
  (`rF_toReal_eq_kInf`) and the product formula over every number field (`finprod_norm_eq_inv_real_complex`).
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqMeasure
import QuadFormsKB.Tamagawa.Measure.Weil.PDArchRatio

open MeasureTheory Set Filter NumberField NumberField.InfinitePlace IsDedekindDomain WithZero
open scoped ENNReal Classical

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices LerayPadic LocalDensity QuadFormsKB.Tamagawa.Measure

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}

/-! ### The product formula over every number field -/

/-- **The product formula for $ab$ over every number field**:
$\prod_{v\in S}q_v^{-(e_a(v)+e_b(v))} = \big(\prod_{w\ \mathrm{real}}|\sigma_w(ab)|\prod_{w\ \mathrm{complex}}\|\sigma_w(ab)\|^2\big)^{-1}$. -/
theorem prod_sqBad_q_pow_gen (ha : a ≠ 0) (hb : b ≠ 0) :
    ∏ v ∈ sqBad ha hb, ((LocalDensity.DVR.q (v.adicCompletionIntegers F) : ℝ) ^ (eExp a ha v + eExp b hb v))⁻¹ =
      ((∏ w : {w : InfinitePlace F // w.IsReal}, |sR w ((a : F) * (b : F))|) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, ‖sC w ((a : F) * (b : F))‖ ^ 2)⁻¹ := by
  set S := sqBad ha hb
  set N : HeightOneSpectrum (𝓞 F) → ℝ := fun v => ‖algebraMap F (v.adicCompletion F) ((a : F) * (b : F))‖
  have hN : ∀ v, N v = ((LocalDensity.DVR.q (v.adicCompletionIntegers F) : ℝ) ^ (eExp a ha v + eExp b hb v))⁻¹ := by
    intro v
    obtain ⟨h1, h2⟩ := pow_dvd_of_valued (valued_ab ha hb v)
    have := QuadFormsKB.Tamagawa.norm_coe_of_pow_dvd v h1 h2
    rw [coe_ι, show ((a * b : 𝓞 F) : F) = (a : F) * (b : F) by push_cast; ring] at this
    exact this
  have hoff : ∀ v ∉ S, eExp a ha v + eExp b hb v = 0 := by
    intro v hv
    obtain ⟨-, hav, hbv⟩ := good_of_not_mem_sqBad ha hb hv
    have hea : eExp a ha v = 0 := by
      have := (valued_eExp a ha v).symm.trans hav
      rw [← WithZero.exp_zero, WithZero.exp_inj] at this; omega
    have heb : eExp b hb v = 0 := by
      have := (valued_eExp b hb v).symm.trans hbv
      rw [← WithZero.exp_zero, WithZero.exp_inj] at this; omega
    rw [hea, heb]
  have hab : (a : F) * (b : F) ≠ 0 := mul_ne_zero (by exact_mod_cast ha) (by exact_mod_cast hb)
  have h := finprod_norm_eq_inv_real_complex _ hab
  rw [← h, finprod_eq_prod_of_mulSupport_subset _ (s := S) (fun v hv => by
    by_contra hS
    apply Function.mem_mulSupport.mp hv
    show N v = 1
    rw [hN, hoff v hS, pow_zero, inv_one])]
  exact Finset.prod_congr rfl fun v _ => (hN v).symm

/-! ### The final bookkeeping, abstractly (finite places only) -/

/-- The finite-place bookkeeping of `real_assembly`, without the archimedean factors. -/
theorem real_assembly_fin {ι : Type*} (S : Finset ι) (f3 Qv oh : ℝ)
    (L3 L4 α3 α4 wl wL wo wn wu qq : ι → ℝ) (e : ι → ℕ)
    (hα3 : ∀ v, α3 v ≠ 0) (hα4 : ∀ v, α4 v ≠ 0) (hwu : ∀ v, wu v ≠ 0) (hwL : ∀ v, wL v ≠ 0) (hqq : ∀ v, qq v ≠ 0)
    (hloc : ∀ v ∈ S, L4 v * wn v * wl v * qq v ^ (3 * e v) = L3 v ^ 2 * wo v * wu v) :
    ((f3 ^ 2 * ∏ v ∈ S, α4 v / α3 v ^ 2) * ∏ v ∈ S, L4 v / α4 v) *
        ((oh * ∏ v ∈ S, wn v / wu v) * (Qv * ∏ v ∈ S, wl v / wL v)) * ∏ v ∈ S, qq v ^ (3 * e v) =
      (f3 * ∏ v ∈ S, L3 v / α3 v) ^ 2 * (Qv * ∏ v ∈ S, wo v / wL v) * oh := by
  have key : ∀ v ∈ S, α4 v / α3 v ^ 2 * (L4 v / α4 v) * (wn v / wu v) * (wl v / wL v) * qq v ^ (3 * e v) =
      (L3 v / α3 v) ^ 2 * (wo v / wL v) := by
    intro v hv
    have h := hloc v hv
    have hq3 : qq v ^ (3 * e v) ≠ 0 := pow_ne_zero _ (hqq v)
    have hα3' := hα3 v; have hα4' := hα4 v; have hwu' := hwu v; have hwL' := hwL v
    calc α4 v / α3 v ^ 2 * (L4 v / α4 v) * (wn v / wu v) * (wl v / wL v) * qq v ^ (3 * e v)
        = (L4 v * wn v * wl v * qq v ^ (3 * e v)) / (α3 v ^ 2 * wu v * wL v) := by
          field_simp
      _ = (L3 v ^ 2 * wo v * wu v) / (α3 v ^ 2 * wu v * wL v) := by rw [h]
      _ = (L3 v / α3 v) ^ 2 * (wo v / wL v) := by
          field_simp
  have hP : (∏ v ∈ S, α4 v / α3 v ^ 2) * (∏ v ∈ S, L4 v / α4 v) * (∏ v ∈ S, wn v / wu v) *
      (∏ v ∈ S, wl v / wL v) * (∏ v ∈ S, qq v ^ (3 * e v)) =
      (∏ v ∈ S, L3 v / α3 v) ^ 2 * (∏ v ∈ S, wo v / wL v) := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl key
  calc ((f3 ^ 2 * ∏ v ∈ S, α4 v / α3 v ^ 2) * ∏ v ∈ S, L4 v / α4 v) *
        ((oh * ∏ v ∈ S, wn v / wu v) * (Qv * ∏ v ∈ S, wl v / wL v)) * ∏ v ∈ S, qq v ^ (3 * e v)
      = f3 ^ 2 * oh * Qv * ((∏ v ∈ S, α4 v / α3 v ^ 2) * (∏ v ∈ S, L4 v / α4 v) *
          (∏ v ∈ S, wn v / wu v) * (∏ v ∈ S, wl v / wL v) * (∏ v ∈ S, qq v ^ (3 * e v))) := by ring
    _ = f3 ^ 2 * oh * Qv * ((∏ v ∈ S, L3 v / α3 v) ^ 2 * (∏ v ∈ S, wo v / wL v)) := by rw [hP]
    _ = _ := by ring

/-! ### Finiteness and positivity -/

section Basic

variable (S : Finset (HeightOneSpectrum (𝓞 F))) (m : HeightOneSpectrum (𝓞 F) → ℕ) (hm1 : ∀ v, 1 ≤ m v)

theorem muFinQuat_quatCongS_ne_top : muFinQuat (a : F) (b : F) (quatCongS a b S m hm1) ≠ ⊤ := by
  refine ne_of_lt (lt_of_le_of_lt (measure_mono (fun u hu => ?_)) (by
    rw [muFinQuat_lamHatUnits]; exact ENNReal.ofReal_lt_top))
  exact ((mem_quatCongS a b S m hm1).1 hu).1 |> (mem_lamHatUnits_iff _ _ u).2

theorem muFinQuat_econgS_ne_top : muFinQuat (a : F) (b : F) (econgS a b S m) ≠ ⊤ := by
  refine ne_of_lt (lt_of_le_of_lt (measure_mono (fun u hu => ?_)) (by
    rw [muFinQuat_lamHatUnits]; exact ENNReal.ofReal_lt_top))
  exact ((mem_econgS a b S m).1 hu).1 |> (mem_lamHatUnits_iff _ _ u).2

theorem muFinQuat_quatCongS_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) :
    muFinQuat (a : F) (b : F) (quatCongS a b S m hm1) ≠ 0 := by
  have := isHaarMeasure_muFinQuat' ha hb
  exact ((isOpen_quatCongS S m hm1).measure_pos (muFinQuat (a : F) (b : F))
    ⟨1, (quatCongS a b S m hm1).one_mem⟩).ne'

include hm1 in
theorem muFinQuat_econgS_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) :
    muFinQuat (a : F) (b : F) (econgS a b S m) ≠ 0 := by
  have := isHaarMeasure_muFinQuat' ha hb
  exact ((isOpen_econgS S m hm1).measure_pos (muFinQuat (a : F) (b : F))
    ⟨1, (econgS a b S m).one_mem⟩).ne'

theorem muFinUnits_OHatUnits_ne_top : muFinUnits F (OHatUnits F) ≠ ⊤ := by
  rw [muFinUnits_OHatUnits]; exact ENNReal.ofReal_ne_top

theorem muFinUnits_OHatUnits_ne_zero : muFinUnits F (OHatUnits F) ≠ 0 := by
  rw [muFinUnits_OHatUnits]; exact (ENNReal.ofReal_pos.mpr ohatVol_pos).ne'

/-- The finite measures of the boxes $\prod_{v\in S}K_{m_v}\times\prod_{v\notin S}SO(L_v)$ are finite. -/
theorem muFin_box_ne_top {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) :
    QuadFormsKB.Tamagawa.Measure.muFin Q₀ (fun _ => 1)
      (QuadFormsKB.Tamagawa.Measure.boxSO Q₀ S (congSOgen Q₀ m hm1)) ≠ ⊤ := by
  refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) (by
    rw [QuadFormsKB.Tamagawa.Measure.muFin_KSO]; exact ENNReal.ofReal_lt_top))
  rw [← coe_boxSub]
  exact inf_le_left

include hm1 in
theorem omegaV_nU_toReal_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < (omegaV v (nU m v)).toReal := by
  have h := omegaV_oneAdd v (k := m v + sExp v) (Nat.le_add_right_of_le (hm1 v))
  change (omegaV v {r : (v.adicCompletion F)ˣ | Valued.v ((r : v.adicCompletion F) - 1) ≤
    exp (-((m v + sExp v : ℕ) : ℤ))}).toReal > 0
  rw [h, selfDualV_latticeV_nat, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  exact div_pos (selfDualV_real_pos v) (pow_pos (by exact_mod_cast DVR.q_pos (R := v.adicCompletionIntegers F)) _)

include hm1 in
theorem muFinUnits_NE_toReal_pos :
    0 < (muFinUnits F (NE S m)).toReal := by
  have hwu : ∀ v : HeightOneSpectrum (𝓞 F), 0 < (omegaV v (unitsVSub v)).toReal := fun v =>
    ENNReal.toReal_pos (omegaV_unitsVSub_ne_zero v) (omegaV_unitsVSub_ne_top v)
  have hnn : (muFinUnits F (NE S m)).toReal =
      ohatVol F * ∏ v ∈ S, (omegaV v (nU m v)).toReal / (omegaV v (unitsVSub v)).toReal :=
    muFinUnits_ideleBox_toReal S (nU m) (fun v _ => measurableSet_nU m v)
  rw [hnn]
  exact mul_pos ohatVol_pos (Finset.prod_pos fun v _ => div_pos (omegaV_nU_toReal_pos m hm1 v) (hwu v))

include hm1 in
theorem muFinUnits_NE_ne_zero : muFinUnits F (NE S m) ≠ 0 := fun h => by
  have := muFinUnits_NE_toReal_pos (F := F) S m hm1
  rw [h, ENNReal.toReal_zero] at this; exact lt_irrefl _ this

include hm1 in
theorem muFinUnits_NE_ne_top : muFinUnits F (NE S m) ≠ ⊤ := fun h => by
  have := muFinUnits_NE_toReal_pos (F := F) S m hm1
  rw [h, ENNReal.toReal_top] at this; exact lt_irrefl _ this

end Basic

/-! ### The finite-place identity -/

set_option maxHeartbeats 4000000 in
/-- **The finite-place identity for the square model** (every number field, every $a, b\ne0$ with $Q_0$ nondegenerate):
$$M_4\cdot N\cdot q_H\cdot\prod_{v\in S}q_v^{3(e_a(v)+e_b(v))} = M_3^2\cdot q_E\cdot U$$
in real numbers, where $S$ = `sqBad`, $m$ = `sqLev`, $M_3, M_4$ are the finite Tamagawa volumes of the boxes
$\prod_{v\in S}K_{m_v}\times\prod_{v\notin S}SO(L_v)$ in $SO(D^0)(\mathbb A_f)$ and $SO(Q_0)(\mathbb A_f)$,
$q_H = \mu_{D^\times}(H_S)$, $q_E = \mu_{D^\times}(E_S)$, $N = \mu_{G_m}(N_E)$, $U = \mu_{G_m}(\hat{\mathcal O}^\times)$.
Unconditional: it uses only the local ratios `local_ratio_sq` and the Euler products at the good places. -/
theorem fin_identity_sq (ha : a ≠ 0) (hb : b ≠ 0) (hQ : (qSq a b).Nondegenerate) :
    (QuadFormsKB.Tamagawa.Measure.muFin (qSq a b) (fun _ => 1)
        (QuadFormsKB.Tamagawa.Measure.boxSO (qSq a b) (sqBad ha hb)
          (congSOS (a := a) (b := b) (sqLev ha hb) (one_le_sqLev ha hb))) *
      (muFinUnits F (NE (sqBad ha hb) (sqLev ha hb)) *
        muFinQuat (a : F) (b : F) (quatCongS a b (sqBad ha hb) (sqLev ha hb) (one_le_sqLev ha hb)))).toReal *
      ∏ v ∈ sqBad ha hb, (LocalDensity.DVR.q (v.adicCompletionIntegers F) : ℝ) ^ (3 * (eExp a ha v + eExp b hb v)) =
    ((QuadFormsKB.Tamagawa.Measure.muFin (QuatZeta.pureFormO a b) (fun _ => 1)
        (QuadFormsKB.Tamagawa.Measure.boxSO (QuatZeta.pureFormO a b) (sqBad ha hb)
          (congSO3S (a := a) (b := b) (sqLev ha hb) (one_le_sqLev ha hb)))) ^ 2 *
      muFinQuat (a : F) (b : F) (econgS a b (sqBad ha hb) (sqLev ha hb)) *
      muFinUnits F (OHatUnits F)).toReal := by
  set S := sqBad ha hb
  set m := sqLev ha hb
  have hm1 := one_le_sqLev ha hb
  have hS : ∀ v ∉ S, Valued.v (2 : v.adicCompletion F) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
        Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1 := fun v hv => good_of_not_mem_sqBad ha hb hv
  have hmS : ∀ v ∈ S, 2 * sExp v < m v ∧ sExp v + eExp a ha v ≤ m v := fun v _ => sqLev_cond ha hb v
  have hQ3 := nondegenerate_pureFormO a b ha hb
  set M3 := QuadFormsKB.Tamagawa.Measure.muFin (QuatZeta.pureFormO a b) (fun _ => 1)
    (QuadFormsKB.Tamagawa.Measure.boxSO (QuatZeta.pureFormO a b) S (congSO3S m hm1))
  set M4 := QuadFormsKB.Tamagawa.Measure.muFin (qSq a b) (fun _ => 1)
    (QuadFormsKB.Tamagawa.Measure.boxSO (qSq a b) S (congSOS m hm1))
  set qH := muFinQuat (a : F) (b : F) (quatCongS a b S m hm1)
  set qE := muFinQuat (a : F) (b : F) (econgS a b S m)
  set N := muFinUnits F (NE S m)
  set U := muFinUnits F (OHatUnits F)
  -- real values of the box measures
  have hU3m : ∀ v ∈ S, MeasurableSet (congSO3S (a := a) (b := b) m hm1 v) := fun v _ =>
    ((isOpen_congSub v _ (m v) (hm1 v)).preimage continuous_subtype_val).measurableSet
  have hU4m : ∀ v ∈ S, MeasurableSet (congSOS (a := a) (b := b) m hm1 v) := fun v _ =>
    ((isOpen_congSub v _ (m v) (hm1 v)).preimage continuous_subtype_val).measurableSet
  have hsm : ∀ v ∈ S, sExp v < m v := fun v hv => by have := (hmS v hv).1; have := hm1 v; omega
  have hm3 := muFin_boxSO_toReal (QuatZeta.pureFormO a b) hQ3 S (congSO3S m hm1) hU3m
  have hm4 := muFin_boxSO_toReal (qSq a b) hQ S (congSOS m hm1) hU4m
  have hqh := muFinQuat_quatBox_toReal ha hb S
    (fun v => (lamCong v a b (m v) (hm1 v) : Set (QuatV (a : F) (b : F) v)ˣ))
    (fun v _ => (isOpen_lamCong v (m v) (hm1 v)).measurableSet)
  rw [← quatCongS_eq_quatBox] at hqh
  have hqe := muFinQuat_quatBox_toReal ha hb S
    (fun v => (oneAddCong v a b (m v) : Set (QuatV (a : F) (b : F) v)ˣ))
    (fun v _ => (isOpen_oneAddCong v a b (hm1 v)).measurableSet)
  rw [← econgS_eq_quatBox] at hqe
  have hnn := muFinUnits_ideleBox_toReal S (nU m) (fun v _ => measurableSet_nU m v)
  have huu : U.toReal = ohatVol F := by
    rw [show U = ENNReal.ofReal (ohatVol F) from muFinUnits_OHatUnits, ENNReal.toReal_ofReal ohatVol_pos.le]
  -- the SO-side local volumes are the `muLoc` volumes of `K_m`
  have hL3 : ∀ v ∈ S, (QuadFormsKB.Tamagawa.Measure.muLocSO v (QuatZeta.pureFormO a b) 1
      (congSO3S (a := a) (b := b) m hm1 v)).toReal =
      (Measure.muLoc v (QuatZeta.pureFormO a b) 1 (congSub v (QuatZeta.pureFormO a b) (m v) (hm1 v) : Set _)).toReal :=
    fun v hv => by
    rw [congSO3S, muLocSO_congSub v (by norm_num) _ hQ3 (valued_two_eq v) (hsm v hv) (hm1 v)]
  have hL4 : ∀ v ∈ S, (QuadFormsKB.Tamagawa.Measure.muLocSO v (qSq a b) 1
      (congSOS (a := a) (b := b) m hm1 v)).toReal =
      (Measure.muLoc v (qSq a b) 1 (congSub v (qSq a b) (m v) (hm1 v) : Set _)).toReal := fun v hv => by
    rw [congSOS, muLocSO_congSub v (by norm_num) _ hQ (valued_two_eq v) (hsm v hv) (hm1 v)]
  rw [Finset.prod_congr rfl fun v hv => by rw [hL3 v hv]] at hm3
  rw [Finset.prod_congr rfl fun v hv => by rw [hL4 v hv]] at hm4
  -- the finite factors
  have hf4 : QuadFormsKB.Tamagawa.Measure.finFactor (qSq a b) (fun _ => 1) =
      QuadFormsKB.Tamagawa.Measure.finFactor (QuatZeta.pureFormO a b) (fun _ => 1) ^ 2 *
        ∏ v ∈ S, NF.siegelDensity v (qSq a b) (qSq a b) /
          NF.siegelDensity v (QuatZeta.pureFormO a b) (QuatZeta.pureFormO a b) ^ 2 := by
    rw [QuadFormsKB.Tamagawa.Measure.finFactor_one _ hQ, QuadFormsKB.Tamagawa.Measure.finFactor_one _ hQ3]
    refine tprod_sq_split _ _ S (multipliable_siegelDensity (by norm_num) (by norm_num) _ hQ3)
      (multipliable_siegelDensity (by norm_num) (by norm_num) _ hQ) (fun v hv => ?_)
      (fun v => (siegelDensity_self_pos' _ hQ3 v).ne')
    obtain ⟨h2, hav, hbv⟩ := hS v hv
    rw [siegelDensity_qSq_good v h2 hav hbv, siegelDensity_pureFormO_good v h2 hav hbv]
  -- the local ratios
  have hloc : ∀ v ∈ S, (Measure.muLoc v (qSq a b) 1 (congSub v (qSq a b) (m v) (hm1 v) : Set _)).toReal *
      (omegaV v (nU m v)).toReal * (omegaQuatV v (a : F) (b : F) (lamCong v a b (m v) (hm1 v))).toReal *
        (LocalDensity.DVR.q (v.adicCompletionIntegers F) : ℝ) ^ (3 * (eExp a ha v + eExp b hb v)) =
      (Measure.muLoc v (QuatZeta.pureFormO a b) 1 (congSub v (QuatZeta.pureFormO a b) (m v) (hm1 v) : Set _)).toReal ^ 2 *
        (omegaQuatV v (a : F) (b : F) (oneAddCong v a b (m v))).toReal * (omegaV v (unitsVSub v)).toReal :=
    fun v _ => local_ratio_sq ha hb hQ (valued_two_eq v) (valued_eExp a ha v) (valued_eExp b hb v) le_rfl
  have hwu : ∀ v : HeightOneSpectrum (𝓞 F), 0 < (omegaV v (unitsVSub v)).toReal := fun v =>
    ENNReal.toReal_pos (omegaV_unitsVSub_ne_zero v) (omegaV_unitsVSub_ne_top v)
  have hnn' : N.toReal = ohatVol F * ∏ v ∈ S, (omegaV v (nU m v)).toReal / (omegaV v (unitsVSub v)).toReal := hnn
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow]
  rw [hm4, hnn', hqh, hm3, hqe, huu, hf4]
  exact real_assembly_fin S _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun v => (siegelDensity_self_pos' _ hQ3 v).ne') (fun v => (siegelDensity_self_pos' _ hQ v).ne')
    (fun v => (hwu v).ne')
    (fun v => (ENNReal.toReal_pos (omegaQuatV_lamLocUnits_ne_zero _ _ v)
      (omegaQuatV_lamLocUnits_ne_top _ _ v)).ne')
    (fun v => (Nat.cast_pos.2 (DVR.q_pos (R := v.adicCompletionIntegers F))).ne')
    hloc

/-! ### The finite ratio via $H_S$ -/

section Ratio

variable (S : Finset (HeightOneSpectrum (𝓞 F))) (m : HeightOneSpectrum (𝓞 F) → ℕ) (hm1 : ∀ v, 1 ≤ m v)

/-- The central units of $\hat\Lambda^\times$ lie in $H_S$ (`quatCongS`), for any levels. -/
theorem lamHat_inf_ker_le_quatCongS (ha : a ≠ 0) :
    lamHatSub a b ⊓ (conjFin a b).ker ≤ quatCongS a b S m hm1 := by
  rintro u ⟨hu, hk⟩
  refine ⟨hu, Subgroup.mem_iInf.mpr fun v => Subgroup.mem_iInf.mpr fun hv => ?_⟩
  rw [Subgroup.mem_comap]
  obtain ⟨c, rfl⟩ := (conjFin_eq_one_iff a b ha u).mp hk
  have huv : unitAtQ _ _ v (finScalar (a : F) (b : F) c) ∈ lamLocUnits (a : F) (b : F) v :=
    (mem_lamHatUnits_iff _ _ _).mp hu v
  refine ⟨?_, huv⟩
  have h1 : conjOrth (QuadForm.map (algebraMap (𝓞 F) F) (QuatZeta.pureFormO a b)) (hQF a b)
      (unitAtQ _ _ v (finScalar (a : F) (b : F) c)) = 1 :=
    (conjOrth_eq_one_iff _ (hQF a b) (by exact_mod_cast ha) _).2 (unitAtQ_finScalar _ _ c v)
  show unitAtQ _ _ v (finScalar (a : F) (b : F) c) ∈ (LerayPadic.congSub v (QuatZeta.pureFormO a b) (m v)
    (hm1 v)).comap (conjOrth (QuadForm.map (algebraMap (𝓞 F) F) (QuatZeta.pureFormO a b)) (hQF a b))
  rw [Subgroup.mem_comap, h1]
  exact Subgroup.one_mem _

theorem relIndex_quatCongS_ne_zero :
    (quatCongS a b S m hm1).relIndex (lamHatSub a b) ≠ 0 :=
  Measure.relIndex_ne_zero_of_isOpen (isCompact_lamHatUnits (a : F) (b : F)) (isOpen_quatCongS S m hm1)

/-- **$r_f = \mu_{D^\times}(H_S)/(\mu_{G_m}(\hat{\mathcal O}^\times)\,\mu_f(c(H_S)))$** for any finite set $S$ of finite
places off which $|2ab|_v = 1$ and any admissible levels (the index $[\hat\Lambda^\times : H_S]$ cancels). Here
$\mu_f(c(H_S))$ is the finite Tamagawa volume of the box $\prod_{v\in S}K_{m_v}\times\prod_{v\notin S}SO(L^0_v)$ in
$SO(D^0)(\mathbb A_f)$. Analogue of `rF_eq_div` for `quatCongS`. -/
theorem rF_eq_div_quatCongS (ha : a ≠ 0) (hb : b ≠ 0)
    (hS : ∀ v ∉ S, Valued.v (2 : v.adicCompletion F) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
        Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1)
    (hmS : ∀ v ∈ S, 2 * sExp v < m v ∧ sExp v + eExp a ha v ≤ m v) :
    rF a b = muFinQuat (a : F) (b : F) (quatCongS a b S m hm1) /
      (muFinUnits F (OHatUnits F) * QuadFormsKB.Tamagawa.Measure.muFin (QuatZeta.pureFormO a b) (fun _ => 1)
        (QuadFormsKB.Tamagawa.Measure.boxSO (QuatZeta.pureFormO a b) S (congSO3S (a := a) (b := b) m hm1))) := by
  have hker := lamHat_inf_ker_le_quatCongS (b := b) S m hm1 ha
  have hle : quatCongS a b S m hm1 ≤ lamHatSub a b := inf_le_left
  have hidx := relIndex_quatCongS_ne_zero (a := a) (b := b) S m hm1
  have hH := isHaarMeasure_muFinQuat' ha hb
  have h1 : muFinQuat (a : F) (b : F) (lamHatUnits (a : F) (b : F)) =
      ((quatCongS a b S m hm1).relIndex (lamHatSub a b) : ℝ≥0∞) * muFinQuat (a : F) (b : F) (quatCongS a b S m hm1) :=
    Measure.measure_subgroup_eq_relIndex_mul (muFinQuat (a : F) (b : F)) (A := lamHatSub a b)
      (B := quatCongS a b S m hm1) (isOpen_quatCongS S m hm1) hle hidx
  have h2 : QuadFormsKB.Tamagawa.Measure.muFin (QuatZeta.pureFormO a b) (fun _ => 1) (lamHatSO a b : Set _) =
      ((quatCongS a b S m hm1).relIndex (lamHatSub a b) : ℝ≥0∞) *
        QuadFormsKB.Tamagawa.Measure.muFin (QuatZeta.pureFormO a b) (fun _ => 1)
          ((quatCongS a b S m hm1).map (conjFin a b) : Set _) := by
    unfold lamHatSO
    rw [← relIndex_map_eq_of_ker_le (conjFin a b) hle hker]
    refine Measure.measure_subgroup_eq_relIndex_mul _ (isOpen_map_conjFin ha hb (isOpen_quatCongS S m hm1))
      (Subgroup.map_mono hle) ?_
    rw [relIndex_map_eq_of_ker_le (conjFin a b) hle hker]
    exact hidx
  rw [coe_map_quatCongS ha hb S m hm1 hS hmS] at h2
  unfold rF cPD
  rw [h1, h2]
  set N := ((quatCongS a b S m hm1).relIndex (lamHatSub a b) : ℝ≥0∞)
  have hN0 : N ≠ 0 := Nat.cast_ne_zero.mpr hidx
  have hNt : N ≠ ⊤ := ENNReal.natCast_ne_top _
  have hU0 := muFinUnits_OHatUnits_ne_zero (F := F)
  have hUt := muFinUnits_OHatUnits_ne_top (F := F)
  set X := muFinQuat (a : F) (b : F) (quatCongS a b S m hm1)
  set U := muFinUnits F (OHatUnits F)
  set Y := QuadFormsKB.Tamagawa.Measure.muFin (QuatZeta.pureFormO a b) (fun _ => 1)
    (QuadFormsKB.Tamagawa.Measure.boxSO (QuatZeta.pureFormO a b) S (congSO3S (a := a) (b := b) m hm1))
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (Or.inl hN0) (Or.inl hNt)]
  calc (N⁻¹ * Y⁻¹) * (U⁻¹ * (N * X)) = (N * N⁻¹) * ((U * Y)⁻¹ * X) := by
        rw [ENNReal.mul_inv (Or.inl hU0) (Or.inl hUt)]
        ring
    _ = _ := by rw [ENNReal.mul_inv_cancel hN0 hNt, one_mul]

end Ratio

/-! ### The target identity for $q_E\,M_3$ -/

/-- The archimedean constants: $K_\infty\cdot(\prod_w|\sigma_w(ab)|\cdots)^3 = c_F(3)\,8^{-r_1}\,64^{-r_2}$. -/
theorem kInf_mul_cube (ha : a ≠ 0) (hb : b ≠ 0) :
    kInf F a b * (((∏ w : {w : InfinitePlace F // w.IsReal}, |sR w ((a : F) * (b : F))|) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, ‖sC w ((a : F) * (b : F))‖ ^ 2)) ^ 3 =
      cF F 3 * (∏ w : {w : InfinitePlace F // w.IsReal}, (1 / 8 : ℝ)) *
        (∏ w : {w : InfinitePlace F // w.IsComplex}, (1 / 64 : ℝ)) := by
  have ha' : (a : F) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : F) ≠ 0 := by exact_mod_cast hb
  have hR : (∏ w : {w : InfinitePlace F // w.IsReal}, 1 / (8 * |sR w (a : F)| ^ 3 * |sR w (b : F)| ^ 3)) *
      (∏ w : {w : InfinitePlace F // w.IsReal}, |sR w ((a : F) * (b : F))|) ^ 3 =
      ∏ w : {w : InfinitePlace F // w.IsReal}, (1 / 8 : ℝ) := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    have h1 : |sR w (a : F)| ≠ 0 := abs_ne_zero.mpr ((map_ne_zero _).mpr ha')
    have h2 : |sR w (b : F)| ≠ 0 := abs_ne_zero.mpr ((map_ne_zero _).mpr hb')
    rw [map_mul, abs_mul]
    field_simp
  have hC : (∏ w : {w : InfinitePlace F // w.IsComplex}, 1 / (8 * ‖sC w (a : F)‖ ^ 3 * ‖sC w (b : F)‖ ^ 3) ^ 2) *
      (∏ w : {w : InfinitePlace F // w.IsComplex}, ‖sC w ((a : F) * (b : F))‖ ^ 2) ^ 3 =
      ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 / 64 : ℝ) := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    have h1 : ‖sC w (a : F)‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero _).mpr ha')
    have h2 : ‖sC w (b : F)‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero _).mpr hb')
    rw [map_mul, norm_mul]
    field_simp
    ring
  rw [mul_pow, kInf]
  calc cF F 3 * (∏ w : {w : InfinitePlace F // w.IsReal}, 1 / (8 * |sR w (a : F)| ^ 3 * |sR w (b : F)| ^ 3)) *
        (∏ w : {w : InfinitePlace F // w.IsComplex}, 1 / (8 * ‖sC w (a : F)‖ ^ 3 * ‖sC w (b : F)‖ ^ 3) ^ 2) *
        ((∏ w : {w : InfinitePlace F // w.IsReal}, |sR w ((a : F) * (b : F))|) ^ 3 *
          (∏ w : {w : InfinitePlace F // w.IsComplex}, ‖sC w ((a : F) * (b : F))‖ ^ 2) ^ 3)
      = cF F 3 * ((∏ w : {w : InfinitePlace F // w.IsReal}, 1 / (8 * |sR w (a : F)| ^ 3 * |sR w (b : F)| ^ 3)) *
          (∏ w : {w : InfinitePlace F // w.IsReal}, |sR w ((a : F) * (b : F))|) ^ 3) *
        ((∏ w : {w : InfinitePlace F // w.IsComplex}, 1 / (8 * ‖sC w (a : F)‖ ^ 3 * ‖sC w (b : F)‖ ^ 3) ^ 2) *
          (∏ w : {w : InfinitePlace F // w.IsComplex}, ‖sC w ((a : F) * (b : F))‖ ^ 2) ^ 3) := by ring
    _ = _ := by rw [hR, hC]

set_option maxHeartbeats 4000000 in
/-- **The finite-place identity $q_E\,M_3 = c_F(3)\,8^{-r_1}\,64^{-r_2}\,N\,M_4$** for every number field $F$ (complex
places allowed) and every $a, b\ne0$ with $Q_0 = \langle1,-a,-b,ab\rangle$ nondegenerate.

Derivation: `fin_identity_sq` gives $M_4 N q_H P = M_3^2 q_E U$ with $P = \prod_{v\in S}q_v^{3(e_a+e_b)}$;
`rF_eq_div_quatCongS` gives $q_H = r_f U M_3$; `rF_toReal_eq_kInf` gives $r_f = K_\infty$; and the product formula
`prod_sqBad_q_pow_gen` gives $P = (\prod_{w\ \mathrm{real}}|\sigma_w(ab)|\prod_{w\ \mathrm{complex}}\|\sigma_w(ab)\|^2)^3$.
Unconditional. -/
theorem fin_identity_sq_E (ha : a ≠ 0) (hb : b ≠ 0) (hQ : (qSq a b).Nondegenerate) :
    ((muFinQuat (a : F) (b : F) (econgS a b (sqBad ha hb) (sqLev ha hb))) *
      QuadFormsKB.Tamagawa.Measure.muFin (QuatZeta.pureFormO a b) (fun _ => 1)
        (QuadFormsKB.Tamagawa.Measure.boxSO (QuatZeta.pureFormO a b) (sqBad ha hb)
          (congSO3S (a := a) (b := b) (sqLev ha hb) (one_le_sqLev ha hb)))).toReal =
      cF F 3 * (∏ w : {w : InfinitePlace F // w.IsReal}, (1 / 8 : ℝ)) *
        (∏ w : {w : InfinitePlace F // w.IsComplex}, (1 / 64 : ℝ)) *
        ((muFinUnits F (NE (sqBad ha hb) (sqLev ha hb))) *
          QuadFormsKB.Tamagawa.Measure.muFin (qSq a b) (fun _ => 1)
            (QuadFormsKB.Tamagawa.Measure.boxSO (qSq a b) (sqBad ha hb)
              (congSOS (a := a) (b := b) (sqLev ha hb) (one_le_sqLev ha hb)))).toReal := by
  have T1 := fin_identity_sq ha hb hQ
  set S := sqBad ha hb
  set m := sqLev ha hb
  have hm1 := one_le_sqLev ha hb
  have hS : ∀ v ∉ S, Valued.v (2 : v.adicCompletion F) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
        Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1 := fun v hv => good_of_not_mem_sqBad ha hb hv
  have hmS : ∀ v ∈ S, 2 * sExp v < m v ∧ sExp v + eExp a ha v ≤ m v := fun v _ => sqLev_cond ha hb v
  have T2 := rF_eq_div_quatCongS S m hm1 ha hb hS hmS
  set M3 := QuadFormsKB.Tamagawa.Measure.muFin (QuatZeta.pureFormO a b) (fun _ => 1)
    (QuadFormsKB.Tamagawa.Measure.boxSO (QuatZeta.pureFormO a b) S (congSO3S m hm1))
  set M4 := QuadFormsKB.Tamagawa.Measure.muFin (qSq a b) (fun _ => 1)
    (QuadFormsKB.Tamagawa.Measure.boxSO (qSq a b) S (congSOS m hm1))
  set qH := muFinQuat (a : F) (b : F) (quatCongS a b S m hm1)
  set qE := muFinQuat (a : F) (b : F) (econgS a b S m)
  set N := muFinUnits F (NE S m)
  set U := muFinUnits F (OHatUnits F)
  have hM3t : M3 ≠ ⊤ := muFin_box_ne_top S m hm1 (QuatZeta.pureFormO a b)
  have hqH0 : qH ≠ 0 := muFinQuat_quatCongS_ne_zero S m hm1 ha hb
  have hU0 : U ≠ 0 := muFinUnits_OHatUnits_ne_zero
  have hUt : U ≠ ⊤ := muFinUnits_OHatUnits_ne_top
  -- `r_f = K_∞ > 0`
  have hrF := rF_toReal_eq_kInf a b ha hb
  have hk := kInf_pos a b ha hb
  have hrFt : rF a b ≠ ⊤ := fun h => by rw [h, ENNReal.toReal_top] at hrF; linarith
  -- `M₃ ≠ 0`
  have hM30 : M3 ≠ 0 := by
    intro h0
    rw [h0, mul_zero, ENNReal.div_zero hqH0] at T2
    exact hrFt T2
  have hUM0 : U * M3 ≠ 0 := mul_ne_zero hU0 hM30
  have hUMt : U * M3 ≠ ⊤ := ENNReal.mul_ne_top hUt hM3t
  have T3 : qH = rF a b * (U * M3) := by
    rw [T2, ENNReal.div_mul_cancel hUM0 hUMt]
  have hqHr : qH.toReal = kInf F a b * (U.toReal * M3.toReal) := by
    rw [T3, ENNReal.toReal_mul, ENNReal.toReal_mul, hrF]
  have hUr : 0 < U.toReal := ENNReal.toReal_pos hU0 hUt
  have hM3r : 0 < M3.toReal := ENNReal.toReal_pos hM30 hM3t
  -- the product formula
  have hq : ∀ v : HeightOneSpectrum (𝓞 F), 0 < ((LocalDensity.DVR.q (v.adicCompletionIntegers F) : ℕ) : ℝ) ^
      (eExp a ha v + eExp b hb v) := fun v =>
    pow_pos (Nat.cast_pos.2 (DVR.q_pos (R := v.adicCompletionIntegers F))) _
  set X : ℝ := ∏ v ∈ S, ((LocalDensity.DVR.q (v.adicCompletionIntegers F) : ℕ) : ℝ) ^ (eExp a ha v + eExp b hb v)
  have hXe : X = (∏ w : {w : InfinitePlace F // w.IsReal}, |sR w ((a : F) * (b : F))|) *
      ∏ w : {w : InfinitePlace F // w.IsComplex}, ‖sC w ((a : F) * (b : F))‖ ^ 2 := by
    have h := prod_sqBad_q_pow_gen ha hb
    rw [Finset.prod_inv_distrib, inv_inj] at h
    exact h
  have hP : ∏ v ∈ S, ((LocalDensity.DVR.q (v.adicCompletionIntegers F) : ℕ) : ℝ) ^
      (3 * (eExp a ha v + eExp b hb v)) = X ^ 3 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun v _ => by rw [← pow_mul, mul_comm]
  have hXk : kInf F a b * X ^ 3 = cF F 3 * (∏ w : {w : InfinitePlace F // w.IsReal}, (1 / 8 : ℝ)) *
      (∏ w : {w : InfinitePlace F // w.IsComplex}, (1 / 64 : ℝ)) := by
    rw [hXe]; exact kInf_mul_cube ha hb
  -- assemble
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow] at T1 ⊢
  rw [hP, hqHr] at T1
  have key : M4.toReal * N.toReal * kInf F a b * X ^ 3 = M3.toReal * qE.toReal := by
    refine mul_left_cancel₀ (mul_pos hUr hM3r).ne' ?_
    linear_combination T1
  linear_combination (-1 : ℝ) * key + (M4.toReal * N.toReal) * hXk

end QuadFormsKB.Tamagawa.Measure.Weil
