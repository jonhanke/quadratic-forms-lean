/-
# The bad-place ratio of the non-square model — `NSBadDeepRatio F`

**Layer:** a number field $F$ (any; totally real only for the consumers), the non-square model $(a, b, d)$, $K = F(\delta)$
with basis $(1,\delta)$, $\alpha = a$, $\beta = b$ in $\mathcal O_K$, and a finite place $v$ of $F$ (any: split, inert,
ramified, dyadic).

**`nsBadDeepRatio`**: `NSBadDeepRatio F` holds. For $M_w = $ `nsLevK w` $+ e_wn$ ($n$ large) and $N = n + C$:

* $\mu^{SO}_v(U^{(M)}_v) = [U^{(M)}_v : K_N]\,\mu_v(K_N)$ (`congSub_le_nsUSub`), $[U^{(M)}_v : K_N] = [Y^{(M)} : Z_N]
  = [\mathfrak L:\mathfrak L_N]\,[T : T\cap Z_N]$ (`index_ZN`), $[T : T\cap Z_N]\cdot2 = [N_v:\mathcal O_v^{\times2}]\cdot2^g$
  (`relIndex_ZN_TY`), $[\mathfrak L:\mathfrak L_N] = \mathrm{vol}(\mathfrak L)/\mathrm{vol}(\mathfrak L_N)$ (`relIndex_L_mul_vol`);
* $\omega_w(\mathcal O_w^\times)/\omega_w(\mathcal O_w^{\times2}) = 2q_w^{s_w}$, $\omega_v(N_v)/\omega_v(\mathcal O_v^\times) =
  [N_v:\mathcal O_v^{\times2}]/2q^s$ (`omegaV_unitsVSub_eq_sq`), $\prod_wq_w^{e_w} = q^2$ (`prod_q_pow_ramE`),
  $c_v^2|4d|_v = 1$ (`localConst_sq_mul_norm`), and the congruence volumes `muLoc_congSub_pureFormO_mul`,
  `muLoc_congSub_qNS_mul`;
* both sides of the bad-place identity equal $q^{13s+6e_a+6e_b+2\mu}\,2^g\,[N_v:\mathcal O_v^{\times2}]/(2\prod_wq_w^{3M_w})$
  (`final_arith`).

Source: Weil 1982, §2.2-2.3, Thm 2.3.1; §3.7, pp. 64-65 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSWinVol

open MeasureTheory Set Function Topology NumberField IsDedekindDomain WithZero
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Quat QuadFormsKB.Quat.Gnat LerayPadic LocalDensity

/-- **The final arithmetic** of the bad-place identity (pure algebra over $\mathbb R$). -/
theorem final_arith (q c V P2 X Pmu Prho volLc volLwc μKN I J Nidx relDisc abn dn t G : ℝ)
    (s ea eb ed μ N : ℕ)
    (hq : 0 < q) (hc : 0 < c) (hV : 0 < V) (hP2 : 0 < P2) (hX : 0 < X) (hLwcp : 0 < volLwc)
    (hrelp : 0 < relDisc) (habp : 0 < abn) (hdnp : 0 < dn) (htp : 0 < t)
    (hμ : Pmu * X = q ^ (2 * (6 * s + 3 * ea + 3 * eb + μ)))
    (hρ : Prho = G * q ^ (2 * s))
    (hLc : volLc * X = c ^ 3 * P2 ^ 3 * q ^ (6 * s + 2 * μ))
    (hLwc : volLwc * q ^ (6 * N) = V ^ 6 * q ^ (6 * s + μ))
    (hK : μKN * q ^ (6 * N) = q ^ (10 * s + 3 * ea + 3 * eb + 6 * ed + μ))
    (hI : I * volLwc = volLc) (hJ : J * 2 = Nidx * G)
    (hrel : relDisc * V ^ 2 = P2) (hct : c * t = q ^ s) (hdn : dn * q ^ ed = 1)
    (hab : abn * q ^ (ea + eb) = 1) (hc2 : c ^ 2 = q ^ (2 * s + ed)) :
    (Pmu * Prho) * (Nidx / (2 * q ^ s)) = (relDisc⁻¹ ^ 3 * abn⁻¹ ^ 3 * (dn ^ 7 * t)) * (I * J * μKN) := by
  have hq0 : q ≠ 0 := hq.ne'
  have eμ : Pmu = q ^ (2 * (6 * s + 3 * ea + 3 * eb + μ)) / X := by field_simp; linarith
  have eLc : volLc = c ^ 3 * P2 ^ 3 * q ^ (6 * s + 2 * μ) / X := by field_simp; linarith
  have eLwc : volLwc = V ^ 6 * q ^ (6 * s + μ) / q ^ (6 * N) := by field_simp; linarith
  have eK : μKN = q ^ (10 * s + 3 * ea + 3 * eb + 6 * ed + μ) / q ^ (6 * N) := by field_simp; linarith
  have eI : I = volLc / volLwc := by field_simp; linarith
  have eJ : J = Nidx * G / 2 := by field_simp; linarith
  have erel : relDisc = P2 / V ^ 2 := by field_simp; linarith
  have edn : dn = 1 / q ^ ed := by field_simp; linarith
  have eab : abn = 1 / q ^ (ea + eb) := by field_simp; linarith
  have et : t = q ^ s / c := by field_simp; linarith
  rw [hρ, eμ, eI, eJ, eK, erel, eab, edn, et, eLc, eLwc]
  field_simp
  rw [hc2]
  ring

theorem nondegenerate_qNS {F : Type} [Field F] [NumberField F] {a b d : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) : (qNS a b d).Nondegenerate := by
  show (qNS a b d).hessian.det ≠ 0
  rw [hessian_qNS, Matrix.det_diagonal, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons]
  have h2 : (2 : 𝓞 F) ≠ 0 := two_ne_zero
  have := mul_ne_zero ha hd
  have := mul_ne_zero hb hd
  have := mul_ne_zero (mul_ne_zero ha hb) hd
  simp_all

section Local

variable {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] [Algebra F K]

theorem min_mul_left' (e x y : ℕ) : min (e * x) (e * y) = e * min x y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (Nat.mul_le_mul_left e h)]
  · rw [min_eq_right h, min_eq_right (Nat.mul_le_mul_left e h)]

theorem omegaV_sqUnits_ne_zero (u : HeightOneSpectrum (𝓞 F)) : omegaV u (sqUnits F u) ≠ 0 :=
  (isOpen_sqSub u).measure_ne_zero _ ⟨1, (sqSub F u).one_mem⟩

theorem omegaV_sqUnits_ne_top (u : HeightOneSpectrum (𝓞 F)) : omegaV u (sqUnits F u) ≠ ⊤ :=
  ne_top_of_le_ne_top ((isCompact_unitsVSub u).measure_lt_top.ne) (measure_mono (sqSub_le_unitsSub u))

/-- **$\omega_v(\mathcal O_v^\times)/\omega_v(\mathcal O_v^{\times2}) = 2q^s$.** -/
theorem omegaV_ratio_sq (u : HeightOneSpectrum (𝓞 F)) :
    (omegaV u (unitsVSub u) / omegaV u (sqUnits F u)).toReal =
      2 * (DVR.q (u.adicCompletionIntegers F) : ℝ) ^ sExp u := by
  rw [omegaV_unitsVSub_eq_sq, ENNReal.mul_div_cancel_right (omegaV_sqUnits_ne_zero u) (omegaV_sqUnits_ne_top u)]
  simp [ENNReal.toReal_mul, ENNReal.toReal_pow]

variable {α β : 𝓞 K} (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (M : HeightOneSpectrum (𝓞 K) → ℕ) (hM1 : ∀ w, 1 ≤ M w)

/-- **The $SO_3$ congruence volume at $w$** in real numbers. -/
theorem muK3_real (hMd : ∀ w, nsLevK hα0 hβ0 w ≤ M w) (w : HeightOneSpectrum (𝓞 K)) :
    (Measure.muLocSO w (QuatZeta.pureFormO α β) 1 (congSO3S (a := α) (b := β) M hM1 w)).toReal *
        (DVR.q (w.adicCompletionIntegers K) : ℝ) ^ (3 * M w) =
      (DVR.q (w.adicCompletionIntegers K) : ℝ) ^ (6 * sExp w + 3 * eExp α hα0 w + 3 * eExp β hβ0 w +
        min (eExp α hα0 w) (eExp β hβ0 w)) := by
  have hm := hMd w
  unfold nsLevK at hm
  have h1 := muLocSO_congSub w (n := 3) (by norm_num) (QuatZeta.pureFormO α β)
    (nondegenerate_pureFormO α β hα0 hβ0) (valued_two_eq w) (m := M w) (by omega) (hM1 w)
  have h2 := muLoc_congSub_pureFormO_mul (v := w) hα0 hβ0 (valued_two_eq w) (valued_eExp α hα0 w)
    (valued_eExp β hβ0 w) hm
  rw [show congSO3S (a := α) (b := β) M hM1 w = Subtype.val ⁻¹' (congSub w (QuatZeta.pureFormO α β) (M w)
    (hM1 w) : Set _) from rfl, h1]
  have := congrArg ENNReal.toReal h2
  simpa [ENNReal.toReal_mul, ENNReal.toReal_pow] using this

/-- **$\omega_w(\mathcal O_w^\times)/\omega_w(\operatorname{nrd}\Lambda^{(M_w)}_w) = 2q_w^{s_w}$** at deep levels. -/
theorem omega_ratio_w (hMd : ∀ w, nsLevK hα0 hβ0 w ≤ M w) (w : HeightOneSpectrum (𝓞 K)) :
    (omegaV w (unitsVSub w) / omegaV w (nL α β M hM1 w)).toReal =
      2 * (DVR.q (w.adicCompletionIntegers K) : ℝ) ^ sExp w := by
  have hm := hMd w
  unfold nsLevK at hm
  rw [nL_eq_sqUnits M hM1 hα0 w (by omega) (by omega), omegaV_ratio_sq]

end Local

section NvSec

variable {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] [Algebra F K] {d : 𝓞 F}
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (M : HeightOneSpectrum (𝓞 K) → ℕ) (hM1 : ∀ w, 1 ≤ M w)
  (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

theorem sqSub_le_NvSub : sqSub F v ≤ NvSub K v := by
  rintro _ ⟨r, hr, rfl⟩ w
  refine ⟨localRingHom v w.1 w.2 r, (valued_localRingHom_eq_one_iff w.1 w.2 _).2 hr, ?_⟩
  rw [Units.val_pow_eq_pow_val, map_pow]

include hb₀ hb₁ in
theorem NvSub_le_unitsSub : NvSub K v ≤ unitsSub v := by
  intro c hc
  obtain ⟨w, hw⟩ := exists_place_over hb₀ hb₁ v (K := K)
  obtain ⟨u, hu, hcu⟩ := hc ⟨w, hw⟩
  have h1 : Valued.v (localRingHom v w hw (c : Fv)) = 1 := by
    change Valued.v (localRingHom v (⟨w, hw⟩ : PlaceSet (K := K) v).1 _ (c : Fv)) = 1
    rw [hcu, map_pow, hu, one_pow]
  exact (valued_localRingHom_eq_one_iff w hw _).1 h1

theorem isOpen_NvSub : IsOpen (NvSub K v : Set Fvˣ) :=
  Subgroup.isOpen_mono (sqSub_le_NvSub v) (isOpen_sqSub v)

include hb₀ hb₁ in
theorem relIndex_sqSub_NvSub_ne_zero : (sqSub F v).relIndex (NvSub K v) ≠ 0 :=
  relIndex_ne_zero_of_isOpen ((isCompact_unitsVSub v).of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ (isOpen_NvSub v)) (NvSub_le_unitsSub hb₀ hb₁ v)) (isOpen_sqSub v)

theorem nsN_eq_NvSub (hMd : ∀ w, nsLevK hα0 hβ0 w ≤ M w) :
    nsN α β M hM1 v = (NvSub K v : Set Fvˣ) := by
  ext r
  simp only [nsN, Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · intro h w
    have hm := hMd w.1
    unfold nsLevK at hm
    have := h w.1 w.2
    rw [nL_eq_sqUnits M hM1 hα0 w.1 (by omega) (by omega)] at this
    obtain ⟨u, hu, hcu⟩ := this
    exact ⟨u, hu, by rw [← Units.val_pow_eq_pow_val, ← hcu]; rfl⟩
  · intro h w hw
    have hm := hMd w
    unfold nsLevK at hm
    rw [nL_eq_sqUnits M hM1 hα0 w (by omega) (by omega)]
    obtain ⟨u, hu, hcu⟩ := h ⟨w, hw⟩
    have hu0 : u ≠ 0 := by intro h0; rw [h0, map_zero] at hu; exact zero_ne_one hu
    exact ⟨Units.mk0 u hu0, hu, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← hcu]; rfl)⟩

include hb₀ hb₁ in
/-- **$\omega_v(N_v)/\omega_v(\mathcal O_v^\times) = [N_v:\mathcal O_v^{\times2}]/2q^s$** at deep levels. -/
theorem omega_ratio_v (hMd : ∀ w, nsLevK hα0 hβ0 w ≤ M w) :
    (omegaV v (nsN α β M hM1 v) / omegaV v (unitsVSub v)).toReal =
      ((sqSub F v).relIndex (NvSub K v) : ℝ) / (2 * (DVR.q (v.adicCompletionIntegers F) : ℝ) ^ sExp v) := by
  rw [nsN_eq_NvSub hα0 hβ0 M hM1 v hMd, measure_subgroup_eq_relIndex_mul (omegaV v) (isOpen_sqSub v)
    (sqSub_le_NvSub v) (relIndex_sqSub_NvSub_ne_zero hb₀ hb₁ v), omegaV_unitsVSub_eq_sq,
    ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_mul]
  have h1 := ENNReal.toReal_pos (omegaV_sqUnits_ne_zero v) (omegaV_sqUnits_ne_top v)
  simp only [ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  change _ * (omegaV v (sqUnits F v)).toReal / (_ * (omegaV v (sqUnits F v)).toReal) = _
  field_simp
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  simp only [ENNReal.toReal_ofNat]
  have hq : (0 : ℝ) < (DVR.q (v.adicCompletionIntegers F) : ℝ) := by
    exact_mod_cast DVR.q_pos (R := v.adicCompletionIntegers F)
  field_simp

end NvSec

section USec

variable {F : Type} [Field F] [NumberField F] {a b d : 𝓞 F} {K : Type} [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
  (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (ha0 : (a : F) ≠ 0) (hd0 : (d : F) ≠ 0) {v : HeightOneSpectrum (𝓞 F)}
  {M : HeightOneSpectrum (𝓞 K) → ℕ} {hM1 : ∀ w, 1 ≤ M w}

local notation "Fv" => v.adicCompletion F
local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (qNS a b d)

include hb₀ in
/-- **$\mu^{SO}_v(U^{(M)}_v) = [Y^{(M)} : Z_N]\,\mu_v(K_N)$.** -/
theorem muLocSO_nsU_eq (hb0 : (b : F) ≠ 0) {c₀ n N : ℕ} (hW : WinHyp hb₁ hα0 hβ0 ha0 v M c₀ n N)
    (hΓ : ∀ w : PlaceSet (K := K) v, (M w.1 : ℤ) ≤
      ramE v w.1 * ((N : ℤ) - cGam a b d v ha0 hb0 hd0 - 2 * sExp v - c₀))
    (hN : (cGam a b d v ha0 hb0 hd0 : ℤ) + 2 * sExp v < N)
    (hfin : (ZN hb₁ hα hβ ha0 hd0 v M hM1 (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW)).index ≠ 0) :
    Measure.muLocSO v (qNS a b d) 1 (nsU hb₁ hα hβ ha0 hd0 M hM1 v) =
      ((ZN hb₁ hα hβ ha0 hd0 v M hM1 (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW)).index : ℝ≥0∞) *
        Measure.muLoc v (qNS a b d) 1 (congSub v (qNS a b d) N (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW) : Set _) := by
  set KN := (congSub v (qNS a b d) N (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW)).comap (soSub QF Fv).subtype
  set U := nsUSub hb₁ hα hβ ha0 hd0 v M hM1
  have hle : KN ≤ U := congSub_le_nsUSub hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 hb0 hW hΓ hN
  have hidx : KN.relIndex U = (ZN hb₁ hα hβ ha0 hd0 v M hM1 (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW)).index := by
    rw [Subgroup.relIndex, ← Subgroup.index_comap_of_surjective (H := KN.subgroupOf U)
      ((nsSOK Fv a b d ha0 hd0).subgroupMap_surjective (nsLocSub hb₁ hα hβ v M hM1))]
    congr 1
  have hKo : IsOpen (KN : Set (Measure.SOv v (qNS a b d))) :=
    (isOpen_congSub v _ _ (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW)).preimage continuous_subtype_val
  have : (Measure.muLocSO v (qNS a b d) 1).IsMulLeftInvariant := by unfold Measure.muLocSO; infer_instance
  have e := measure_subgroup_eq_relIndex_mul (Measure.muLocSO v (qNS a b d) 1) hKo hle (by rw [hidx]; exact hfin)
  rw [← coe_nsUSub, e, hidx]
  congr 1
  have hQ := nondegenerate_qNS (aO_ne_zero ha0) (aO_ne_zero hb0) (aO_ne_zero hd0)
  exact muLocSO_congSub v (n := 4) (by norm_num) (qNS a b d) hQ (valued_two_eq v) (by have := hW.Ns; omega)
    (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW)

end USec

section VolReal

variable {F : Type} [Field F] [NumberField F] {a b d : 𝓞 F} {K : Type} [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (v : HeightOneSpectrum (𝓞 F)) (M : HeightOneSpectrum (𝓞 K) → ℕ)

local notation "Fv" => v.adicCompletion F

/-- $\mathrm{vol}(\mathcal O_u)$ for the self-dual measure (as a real number). -/
abbrev voR {L : Type} [Field L] [NumberField L] (u : HeightOneSpectrum (𝓞 L)) : ℝ :=
  (Analysis.selfDualV u (Analysis.latticeV u 0)).toReal

theorem voR_pos {L : Type} [Field L] [NumberField L] (u : HeightOneSpectrum (𝓞 L)) : 0 < voR u :=
  ENNReal.toReal_pos (selfDualV_latticeV_ne_zero u 0) (selfDualV_latticeV_ne_top u 0)

theorem selfDualV_latticeV_real {L : Type} [Field L] [NumberField L] (u : HeightOneSpectrum (𝓞 L)) (k : ℕ) :
    (Analysis.selfDualV u (Analysis.latticeV u (k : ℤ))).toReal * (DVR.q (u.adicCompletionIntegers L) : ℝ) ^ k =
      voR u := by
  rw [selfDualV_latticeV_nat, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  have : (0 : ℝ) < (DVR.q (u.adicCompletionIntegers L) : ℝ) := by
    exact_mod_cast DVR.q_pos (R := u.adicCompletionIntegers L)
  field_simp

include hb₀ in
/-- **$\mathrm{vol}(\mathfrak L)\prod_wq_w^{3M_w} = c_v^3\prod_w\mathrm{vol}(\mathcal O_w)^3q_w^{3s_w+\mu_w}$.** -/
theorem volLc_real (hMd : ∀ w, nsLevK hα0 hβ0 w ≤ M w) :
    (volC v (((LSub hb₁ α β v M).comap (toE d v) : AddSubgroup (Fin 3 → Fin 2 → Fv)) : Set _)).toReal *
        ∏ w : PlaceSet (K := K) v, (DVR.q (w.1.adicCompletionIntegers K) : ℝ) ^ (3 * M w.1) =
      (localConst bK v : ℝ) ^ 3 * (∏ w : PlaceSet (K := K) v, voR w.1) ^ 3 *
        ∏ w : PlaceSet (K := K) v, (DVR.q (w.1.adicCompletionIntegers K) : ℝ) ^
          (3 * sExp w.1 + min (eExp α hα0 w.1) (eExp β hβ0 w.1)) := by
  rw [vol_Lc hb₀ hb₁ v M, ENNReal.toReal_prod, Fin.prod_univ_three]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.coe_toReal]
  simp only [boxL_eq hα0 hβ0 v M hMd]
  simp only [show ((0 : Fin 3) = 2) = False by decide, show ((1 : Fin 3) = 2) = False by decide, if_true, if_false,
    Nat.sub_zero]
  rw [show (localConst bK v : ℝ) ^ 3 * (∏ w : PlaceSet (K := K) v, voR w.1) ^ 3 *
      ∏ w : PlaceSet (K := K) v, (DVR.q (w.1.adicCompletionIntegers K) : ℝ) ^
        (3 * sExp w.1 + min (eExp α hα0 w.1) (eExp β hβ0 w.1)) =
      (localConst bK v : ℝ) * (localConst bK v : ℝ) * (localConst bK v : ℝ) *
        ∏ w : PlaceSet (K := K) v, (voR w.1 ^ 3 * (DVR.q (w.1.adicCompletionIntegers K) : ℝ) ^
          (3 * sExp w.1 + min (eExp α hα0 w.1) (eExp β hβ0 w.1))) by
    rw [Finset.prod_mul_distrib, Finset.prod_pow]; ring]
  rw [show ∀ (x y z : ℝ) (A B C D : ℝ), x * A * (y * B) * (z * C) * D = x * y * z * (A * B * C * D) by
    intros; ring, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  have hm := hMd w.1
  unfold nsLevK at hm
  set qw := (DVR.q (w.1.adicCompletionIntegers K) : ℝ)
  set μw := min (eExp α hα0 w.1) (eExp β hβ0 w.1)
  have hμ : μw ≤ eExp α hα0 w.1 := min_le_left _ _
  have h1 := selfDualV_latticeV_real w.1 (M w.1 - sExp w.1)
  have h2 := selfDualV_latticeV_real w.1 (M w.1 - sExp w.1 - μw)
  set A := (Analysis.selfDualV w.1 (Analysis.latticeV w.1 ((M w.1 - sExp w.1 : ℕ) : ℤ))).toReal
  set B := (Analysis.selfDualV w.1 (Analysis.latticeV w.1 ((M w.1 - sExp w.1 - μw : ℕ) : ℤ))).toReal
  have e1 : qw ^ (3 * M w.1) = (qw ^ (M w.1 - sExp w.1)) ^ 2 * qw ^ (M w.1 - sExp w.1 - μw) *
      qw ^ (3 * sExp w.1 + μw) := by
    rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; omega
  have h3 : voR w.1 ^ 3 = (A * qw ^ (M w.1 - sExp w.1)) * (A * qw ^ (M w.1 - sExp w.1)) *
      (B * qw ^ (M w.1 - sExp w.1 - μw)) := by rw [h1, h2]; ring
  rw [e1, h3]; ring

/-- **$\mathrm{vol}(\mathfrak L_N)\,q^{6N} = \mathrm{vol}(\mathcal O_v)^6q^{6s+\mu}$.** -/
theorem volLwc_real (ha0 : a ≠ 0) (hb0 : b ≠ 0) {N : ℕ} (hN : sExp v + min (eExp a ha0 v) (eExp b hb0 v) ≤ N) :
    (volC v (((LwinSub a b d v N).comap (toE d v) : AddSubgroup (Fin 3 → Fin 2 → Fv)) : Set _)).toReal *
        (DVR.q (v.adicCompletionIntegers F) : ℝ) ^ (6 * N) =
      voR v ^ 6 * (DVR.q (v.adicCompletionIntegers F) : ℝ) ^ (6 * sExp v + min (eExp a ha0 v) (eExp b hb0 v)) := by
  rw [vol_Lwc, ENNReal.toReal_prod, Fin.prod_univ_three]
  simp only [ENNReal.toReal_mul, boxW, show ((0 : Fin 3) = 2) = False by decide,
    show ((1 : Fin 3) = 2) = False by decide, if_true, if_false]
  rw [latTwo_eq' v (by omega), latTwoAB_eq' v ha0 hb0 hN]
  set μ := min (eExp a ha0 v) (eExp b hb0 v)
  set q := (DVR.q (v.adicCompletionIntegers F) : ℝ)
  have h1 := selfDualV_latticeV_real v (N - sExp v)
  have h2 := selfDualV_latticeV_real v (N - sExp v - μ)
  set A := (Analysis.selfDualV v (Analysis.latticeV v ((N - sExp v : ℕ) : ℤ))).toReal
  set B := (Analysis.selfDualV v (Analysis.latticeV v ((N - sExp v - μ : ℕ) : ℤ))).toReal
  have e1 : q ^ (6 * N) = (q ^ (N - sExp v)) ^ 5 * q ^ (N - sExp v - μ) * q ^ (6 * sExp v + μ) := by
    rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; omega
  have h3 : voR v ^ 6 = (A * q ^ (N - sExp v)) ^ 5 * (B * q ^ (N - sExp v - μ)) := by rw [h1, h2]; ring
  rw [e1, h3]; ring

end VolReal

section Main

variable (F : Type) [Field F] [NumberField F]

set_option maxHeartbeats 8000000 in
/-- **`NSBadDeepRatio F` holds for every number field $F$**: the bad-place identity of the non-square model at the
deep levels $M_w = $ `nsLevK w` $+ e_wn$, $n$ large (Weil 1982, Thm 2.3.1 for $m = 4$, non-square discriminant). -/
@[kb "weil1982" "Thm 2.3.1 (local ratios); §3.7, pp. 64-65 [unverified page]"]
theorem nsBadDeepRatio : NSBadDeepRatio F := by
  refine ⟨fun a b d K _ _ _ bK hb₀ hb₁ α β hα hβ hα0 hβ0 _ _ _ v _ => ?_⟩
  have ha0 := ne_zero_of_algebraMap_eq hα hα0
  have hb0 := ne_zero_of_algebraMap_eq hβ hβ0
  have hd0 := d_ne_zero_of_basis hb₁
  have haO := aO_ne_zero ha0
  have hbO := aO_ne_zero hb0
  have hdO := aO_ne_zero hd0
  obtain ⟨c₀, hc₀⟩ := exists_pl_cl hb₀ hb₁ (v := v) (K := K)
  set s := sExp v
  set ea := eExp a haO v
  set eb := eExp b hbO v
  set ed := eExp d hdO v
  set μ := min ea eb
  set C := 9 * s + 6 * ea + 6 * eb + 6 * ed + c₀ + 1
  set n := C + s + 4 * c₀ + 1
  set N := n + C
  set M : HeightOneSpectrum (𝓞 K) → ℕ := fun w => nsLevK hα0 hβ0 w + ramE v w * n
  have hM : ∀ w, nsLevK hα0 hβ0 w ≤ M w := fun w => Nat.le_add_right _ _
  refine ⟨M, hM, ?_⟩
  set hM1 := one_le_of_deep hα0 hβ0 hM
  -- the exponents at `w ∣ v`
  have hexp : ∀ w : PlaceSet (K := K) v, sExp w.1 = ramE v w.1 * s ∧ eExp α hα0 w.1 = ramE v w.1 * ea ∧
      eExp β hβ0 w.1 = ramE v w.1 * eb ∧ 1 ≤ ramE v w.1 :=
    fun w => ⟨sExp_over v w.1 w.2, eExp_over v hα haO hα0 w.1 w.2, eExp_over v hβ hbO hβ0 w.1 w.2,
      one_le_ramE v w.1 w.2⟩
  have hMw : ∀ w : PlaceSet (K := K) v, M w.1 = ramE v w.1 * (6 * s + 4 * ea + 4 * eb) + 1 + ramE v w.1 * n := by
    intro w
    obtain ⟨h1, h2, h3, -⟩ := hexp w
    simp only [M, nsLevK, h1, h2, h3]; ring
  -- the window hypotheses
  have hW : WinHyp hb₁ hα0 hβ0 ha0 v M c₀ n N := by
    refine ⟨hM, hc₀, fun w => ?_, fun w => ?_, ?_, ?_, ?_⟩
    · obtain ⟨h1, h2, -, he⟩ := hexp w
      rw [hMw w, h1, h2]; nlinarith
    · obtain ⟨-, -, -, he⟩ := hexp w
      rw [hMw w]
      have he' : (1 : ℤ) ≤ ramE v w.1 := by exact_mod_cast he
      push_cast
      simp only [N, C]; push_cast; nlinarith
    · simp only [N, n, C]; push_cast; omega
    · simp only [n, C]; omega
    · simp only [N, n, C]; omega
  have hcGam : cGam a b d v ha0 hb0 hd0 = ea + eb + ed := rfl
  have hΓ : ∀ w : PlaceSet (K := K) v, (M w.1 : ℤ) ≤
      ramE v w.1 * ((N : ℤ) - cGam a b d v ha0 hb0 hd0 - 2 * sExp v - c₀) := by
    intro w
    obtain ⟨-, -, -, he⟩ := hexp w
    rw [hMw w, hcGam]
    have he' : (1 : ℤ) ≤ ramE v w.1 := by exact_mod_cast he
    push_cast
    simp only [N, n, C]; push_cast; nlinarith
  have hNcov : (cGam a b d v ha0 hb0 hd0 : ℤ) + 2 * sExp v < N := by
    rw [hcGam]; simp only [N, n, C]; push_cast; omega
  have hNμ : sExp v + min (eExp a haO v) (eExp b hbO v) ≤ N := by
    have : min ea eb ≤ ea := min_le_left _ _
    simp only [N, n, C]; omega
  have hNK : 2 * (4 * s + 2 * ea + 2 * eb + 3 * ed) + 1 ≤ N := by simp only [N, n, C]; omega
  -- the indices
  set I := (LwinSub a b d v N).relIndex (LSub hb₁ α β v M)
  set Z := ZN hb₁ hα hβ ha0 hd0 v M hM1 (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW)
  set J := Z.relIndex (TY hb₁ hα hβ v M hM1)
  set Nidx := (sqSub F v).relIndex (NvSub K v)
  have hZ : Z.index = I * J := index_ZN hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 hW
  have hJ : J * 2 = Nidx * 2 ^ Fintype.card (PlaceSet (K := K) v) :=
    relIndex_ZN_TY hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 hW
  have hNidx0 : Nidx ≠ 0 := relIndex_sqSub_NvSub_ne_zero hb₀ hb₁ v
  have hvolI := relIndex_L_mul_vol hb₀ hb₁ hα0 hβ0 v M haO hbO hM hNμ hW.MN
  -- real-number facts
  set q := (DVR.q (v.adicCompletionIntegers F) : ℝ)
  have hq : 0 < q := Nat.cast_pos.2 (DVR.q_pos (R := v.adicCompletionIntegers F))
  have hQ := prod_q_pow_ramE hb₀ hb₁ v
  have hprodpow : ∀ k : ℕ, ∏ w : PlaceSet (K := K) v,
      ((DVR.q (w.1.adicCompletionIntegers K) : ℝ) ^ ramE v w.1) ^ k = q ^ (2 * k) := by
    intro k; rw [Finset.prod_pow, hQ, ← pow_mul]
  set g := Fintype.card (PlaceSet (K := K) v)
  set Pmu := ∏ w : PlaceSet (K := K) v,
    (Measure.muLocSO w.1 (QuatZeta.pureFormO α β) 1 (congSO3S (a := α) (b := β) M hM1 w.1)).toReal
  set X := ∏ w : PlaceSet (K := K) v, (DVR.q (w.1.adicCompletionIntegers K) : ℝ) ^ (3 * M w.1)
  have hX : 0 < X := Finset.prod_pos fun w _ =>
    pow_pos (by exact_mod_cast DVR.q_pos (R := w.1.adicCompletionIntegers K)) _
  have hμ : Pmu * X = q ^ (2 * (6 * s + 3 * ea + 3 * eb + μ)) := by
    simp only [Pmu, X]
    rw [← hprodpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [muK3_real hα0 hβ0 M hM1 hM w.1, ← pow_mul]
    obtain ⟨h1, h2, h3, -⟩ := hexp w
    rw [h1, h2, h3, min_mul_left']; congr 1; ring
  set Prho := ∏ w : PlaceSet (K := K) v, (2 * (DVR.q (w.1.adicCompletionIntegers K) : ℝ) ^ sExp w.1)
  have hρ : Prho = 2 ^ g * q ^ (2 * s) := by
    simp only [Prho]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← hprodpow]
    congr 1
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← pow_mul, (hexp w).1]
  -- the lattice volumes
  set volLc := (volC v (((LSub hb₁ α β v M).comap (toE d v) : AddSubgroup (Fin 3 → Fin 2 → _)) : Set _)).toReal
  set volLwc := (volC v (((LwinSub a b d v N).comap (toE d v) : AddSubgroup (Fin 3 → Fin 2 → _)) : Set _)).toReal
  set P2 := ∏ w : PlaceSet (K := K) v, voR w.1
  set c := (localConst bK v : ℝ)
  have hLc : volLc * X = c ^ 3 * P2 ^ 3 * q ^ (6 * s + 2 * μ) := by
    have h := volLc_real hb₀ hb₁ hα0 hβ0 v M hM
    rw [show ∏ w : PlaceSet (K := K) v, (DVR.q (w.1.adicCompletionIntegers K) : ℝ) ^
        (3 * sExp w.1 + min (eExp α hα0 w.1) (eExp β hβ0 w.1)) = q ^ (6 * s + 2 * μ) by
      rw [show 6 * s + 2 * μ = 2 * (3 * s + μ) by ring, ← hprodpow]
      refine Finset.prod_congr rfl fun w _ => ?_
      obtain ⟨h1, h2, h3, -⟩ := hexp w
      rw [h1, h2, h3, min_mul_left', ← pow_mul]; congr 1; ring] at h
    exact h
  have hLwc : volLwc * q ^ (6 * N) = voR v ^ 6 * q ^ (6 * s + μ) := volLwc_real v haO hbO hNμ
  have hLwcp : 0 < volLwc := by
    have h1 : 0 < voR v ^ 6 * q ^ (6 * s + μ) := mul_pos (pow_pos (voR_pos v) _) (pow_pos hq _)
    rw [← hLwc] at h1
    exact pos_of_mul_pos_left h1 (pow_pos hq _).le
  have hI : (I : ℝ) * volLwc = volLc := by
    have := congrArg ENNReal.toReal hvolI
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at this
  have hJr : (J : ℝ) * 2 = (Nidx : ℝ) * 2 ^ g := by exact_mod_cast hJ
  -- the volume of `K_N`
  have hQns := nondegenerate_qNS haO hbO hdO
  set μKN := (Measure.muLoc v (qNS a b d) 1 (congSub v (qNS a b d) N
    (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW) : Set _)).toReal
  have hK : μKN * q ^ (6 * N) = q ^ (10 * s + 3 * ea + 3 * eb + 6 * ed + μ) := by
    have h := muLoc_congSub_qNS_mul hQns (valued_two_eq v) (valued_eExp a haO v) (valued_eExp b hbO v)
      (valued_eExp d hdO v) hNK
    have := congrArg ENNReal.toReal h
    simpa [ENNReal.toReal_mul, ENNReal.toReal_pow] using this
  -- the norms and the local constant
  set dn := ‖algebraMap F (v.adicCompletion F) (d : F)‖
  set abn := ‖algebraMap F (v.adicCompletion F) ((a : F) * (b : F))‖
  have hdn : dn * q ^ ed = 1 := by
    simp only [dn]
    rw [norm_of_valued_exp v (k := (ed : ℤ)) (valued_eExp d hdO v), zpow_neg, zpow_natCast,
      inv_mul_cancel₀ (pow_ne_zero _ hq.ne')]
  have hab : abn * q ^ (ea + eb) = 1 := by
    have hv : Valued.v (algebraMap F (v.adicCompletion F) ((a : F) * (b : F))) = exp (-((ea + eb : ℕ) : ℤ)) := by
      rw [map_mul, map_mul, valued_eExp a haO v, valued_eExp b hbO v, ← exp_add]; congr 1; push_cast; ring
    simp only [abn]
    rw [norm_of_valued_exp v hv, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hq.ne')]
  have hdnp : 0 < dn := by
    have h := hdn; by_contra h0; push Not at h0
    have : dn = 0 := le_antisymm h0 (norm_nonneg _)
    rw [this, zero_mul] at h; exact zero_ne_one h
  have h4 : ‖algebraMap F (v.adicCompletion F) (4 * (d : F))‖ = dn / q ^ (2 * s) := by
    have hv4 : Valued.v (algebraMap F (v.adicCompletion F) 4) = exp (-((2 * s : ℕ) : ℤ)) := by
      rw [map_ofNat, show (4 : v.adicCompletion F) = 2 * 2 by norm_num, map_mul, valued_two_eq v, ← exp_add]
      congr 1; push_cast; ring
    rw [map_mul, norm_mul, norm_of_valued_exp v hv4, zpow_neg, zpow_natCast]
    simp only [q, dn]; ring
  have hc0 := localConst_sq_mul_norm hb₀ hb₁ v
  rw [h4] at hc0
  have hcpos : 0 < c := localConst_pos bK v
  have hc2d : c ^ 2 * dn = q ^ (2 * s) := by
    field_simp at hc0; linarith
  set t := Real.sqrt dn
  have ht : t ^ 2 = dn := Real.sq_sqrt hdnp.le
  have htp : 0 < t := Real.sqrt_pos.2 hdnp
  have hct : c * t = q ^ s := by
    have h1 : (c * t) ^ 2 = (q ^ s) ^ 2 := by rw [mul_pow, ht, hc2d, ← pow_mul, mul_comm]
    exact (pow_left_inj₀ (mul_pos hcpos htp).le (pow_pos hq _).le two_ne_zero).1 h1
  have hc2 : c ^ 2 = q ^ (2 * s + ed) := by
    have : c ^ 2 = c ^ 2 * dn * q ^ ed := by rw [mul_assoc, hdn, mul_one]
    rw [this, hc2d, pow_add]
  -- the relative discriminant
  have hrel : relDisc K v * voR v ^ 2 = P2 := by
    unfold relDisc
    rw [← prod_placeSet_eq v (fun w => vo w)]
    have hvo : ∀ {L : Type} [Field L] [NumberField L] (u : HeightOneSpectrum (𝓞 L)), vo u = voR u := fun _ => rfl
    simp only [hvo, P2]
    rw [div_mul_cancel₀ _ (pow_pos (voR_pos v) 2).ne']
  -- the `SO` side
  have hI0 : I ≠ 0 := by
    intro h0
    have h1 : volLc = 0 := by rw [← hI, h0, Nat.cast_zero, zero_mul]
    have h2 : 0 < c ^ 3 * P2 ^ 3 * q ^ (6 * s + 2 * μ) :=
      mul_pos (mul_pos (pow_pos hcpos _) (pow_pos (Finset.prod_pos fun w _ => voR_pos w.1) _)) (pow_pos hq _)
    rw [← hLc, h1, zero_mul] at h2; exact lt_irrefl _ h2
  have hJ0 : J ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hJ
    exact mul_ne_zero hNidx0 (pow_ne_zero _ two_ne_zero) hJ.symm
  have hU := muLocSO_nsU_eq hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 (hM1 := hM1) hb0 hW hΓ hNcov
    (by rw [hZ]; exact mul_ne_zero hI0 hJ0)
  rw [hU, hZ]
  -- both sides in real numbers
  have hPmu : 0 < Pmu := pos_of_mul_pos_left (by rw [hμ]; exact pow_pos hq _) hX.le
  have hPrho : 0 < Prho := by rw [hρ]; exact mul_pos (pow_pos two_pos _) (pow_pos hq _)
  have hNidxp : (0 : ℝ) < Nidx := Nat.cast_pos.2 (Nat.pos_of_ne_zero hNidx0)
  have hLreal : ((∏ w ∈ placesOver (K := K) v, Measure.muLocSO w (QuatZeta.pureFormO α β) 1
      (congSO3S (a := α) (b := β) M hM1 w) * omegaV w (unitsVSub w) / omegaV w (nL α β M hM1 w)) *
      (omegaV v (nsN α β M hM1 v) / omegaV v (unitsVSub v))).toReal =
      (Pmu * Prho) * ((Nidx : ℝ) / (2 * q ^ s)) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_prod, omega_ratio_v hb₀ hb₁ hα0 hβ0 M hM1 v hM]
    congr 1
    rw [← prod_placeSet_eq v (fun w => (Measure.muLocSO w (QuatZeta.pureFormO α β) 1
      (congSO3S (a := α) (b := β) M hM1 w) * omegaV w (unitsVSub w) / omegaV w (nL α β M hM1 w)).toReal)]
    rw [show Pmu * Prho = ∏ w : PlaceSet (K := K) v,
      ((Measure.muLocSO w.1 (QuatZeta.pureFormO α β) 1 (congSO3S (a := α) (b := β) M hM1 w.1)).toReal *
        (2 * (DVR.q (w.1.adicCompletionIntegers K) : ℝ) ^ sExp w.1)) from (Finset.prod_mul_distrib).symm]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [mul_div_assoc, ENNReal.toReal_mul, omega_ratio_w hα0 hβ0 M hM1 hM w.1]
  have habp : 0 < abn := by
    have h := hab; by_contra h0; push Not at h0
    have : abn = 0 := le_antisymm h0 (norm_nonneg _)
    rw [this, zero_mul] at h; exact zero_ne_one h
  have hrv : 0 < nsRatio K a b d v := by
    unfold nsRatio
    have := relDisc_pos (K := K) v
    exact mul_pos (mul_pos (pow_pos (inv_pos.2 this) _) (pow_pos (inv_pos.2 habp) _))
      (Real.rpow_pos_of_pos hdnp _)
  have hRreal : (ENNReal.ofReal (nsRatio K a b d v) * (((I * J : ℕ) : ℝ≥0∞) *
      Measure.muLoc v (qNS a b d) 1 (congSub v (qNS a b d) N (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW) : Set _))).toReal =
      ((relDisc K v)⁻¹ ^ 3 * abn⁻¹ ^ 3 * (dn ^ 7 * t)) * ((I : ℝ) * J * μKN) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hrv.le, ENNReal.toReal_mul, ENNReal.toReal_natCast]
    unfold nsRatio
    rw [← pow_mul_sqrt_eq_rpow hdnp, Nat.cast_mul]
  have hfin := final_arith q c (voR v) P2 X Pmu Prho volLc volLwc μKN I J Nidx (relDisc K v) abn dn t (2 ^ g)
    s ea eb ed μ N hq hcpos (voR_pos v) (Finset.prod_pos fun w _ => voR_pos w.1) hX hLwcp (relDisc_pos v)
    (by have := hab; by_contra h0; push Not at h0
        have : abn = 0 := le_antisymm h0 (norm_nonneg _)
        rw [this, zero_mul] at hab; exact zero_ne_one hab)
    hdnp htp hμ hρ hLc hLwc hK hI hJr hrel hct hdn hab hc2
  have hLpos : 0 < (Pmu * Prho) * ((Nidx : ℝ) / (2 * q ^ s)) :=
    mul_pos (mul_pos hPmu hPrho) (div_pos hNidxp (mul_pos two_pos (pow_pos hq _)))
  have hRpos : 0 < ((relDisc K v)⁻¹ ^ 3 * abn⁻¹ ^ 3 * (dn ^ 7 * t)) * ((I : ℝ) * J * μKN) := hfin ▸ hLpos
  rw [← hLreal, ← hRreal] at hfin
  refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).1 hfin
  · intro h; rw [h, ENNReal.toReal_top] at hLreal; rw [← hLreal] at hLpos; exact lt_irrefl _ hLpos
  · intro h; rw [h, ENNReal.toReal_top] at hRreal; rw [← hRreal] at hRpos; exact lt_irrefl _ hRpos

end Main

end QuadFormsKB.Tamagawa.Measure.Weil
