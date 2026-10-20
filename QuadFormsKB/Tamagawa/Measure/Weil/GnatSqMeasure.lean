/-
# Weil's local-ratio identity $\Phi_*\mu_P = \mu_{\mathrm{Tam}}$ for the square model

**Layer:** a totally real number field $F$ (any class number), $a, b\in\mathcal O_F\setminus0$ with $-a, -b\gg0$
($D = (a,b)_F$ totally definite), $Q_0 = \langle1,-a,-b,ab\rangle$ (`qSq a b`).

**`gnatMeasureComparisonDef_sq`**: `((gnatSqO ha hb).muP (muSq ha hb)).map (sqPEquiv ha hb) = muTam (qSq a b) hQ 1`
— the square half of the input `GnatMeasureComparisonDef F`, now a theorem.

*Proof* (Weil 1982, Thm 2.3.1, $\prod_v r_v = 1$). By Haar uniqueness (`map_muP_sq_eq_of_compact_open`) it
suffices to compare both measures on $K' = G_\infty\times\prod_{v\in S}K_{m_v}\times\prod_{v\notin S}SO(L_v)$
($S$ = the places with $|2ab|_v\ne1$, $m_v = 2(4s_v+2e_a+2e_b)+1$). `muP_boxK_mul` expresses $\mu_P(\Phi^{-1}K')$ through
$\mu_{PD}(\operatorname{pd}H_S) = \mu^{SO(D^0)}_{\mathrm{Tam}}(K'_3)$ (`muPD_pdMk_HS`) and local volumes; the SO side is
$c_F(4)\prod_w\mathrm{vol}(SO_4(\mathbb R))\cdot\prod'_v\alpha_v\cdot\prod_{v\in S}\mu_v(K_{m_v})/\alpha_v$. At $v\notin S$:
$\alpha^{(4)}_v = (\alpha^{(3)}_v)^2$ (`siegelDensity_qSq_good`); at $v\in S$: $r_v = |ab|_v^{-3}$ (`local_ratio_sq`); at $\infty$:
$\mu^{(3)}_\infty(G^{(3)}_\infty)^2 = \mu^{(4)}_\infty(G_\infty)\prod_w|\sigma_w(ab)|^{-3}$; and $\prod_v|ab|_v^3\prod_w|\sigma_w(ab)|^{-3}\cdot
\ldots = 1$ is the product formula (`finprod_norm_eq`).
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqLocalRatio

open MeasureTheory Set Filter NumberField NumberField.InfinitePlace IsDedekindDomain WithZero
open scoped ENNReal Classical

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices LerayPadic LocalDensity QuadFormsKB.Tamagawa.Measure

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}

/-! ### The bad set and the levels -/

section Bad

variable (ha : a ≠ 0) (hb : b ≠ 0)

include ha hb in
theorem eventually_good_sq : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
    Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1 := by
  filter_upwards [eventually_good_place (a := (a : F)) (b := (b : F)) (by exact_mod_cast ha) (by exact_mod_cast hb)]
    with v hv
  exact ⟨hv.1, hv.2.1, hv.2.2.1⟩

/-- The bad places: $|2ab|_v\ne1$. -/
def sqBad : Finset (HeightOneSpectrum (𝓞 F)) :=
  (Filter.eventually_cofinite.mp (eventually_good_sq ha hb)).toFinset

theorem good_of_not_mem_sqBad {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ sqBad ha hb) :
    Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1 := by
  by_contra h
  exact hv ((Set.Finite.mem_toFinset _).mpr h)

/-- The levels $m_v = 2(4s_v+2e_a(v)+2e_b(v))+1$. -/
def sqLev (v : HeightOneSpectrum (𝓞 F)) : ℕ := 2 * (4 * sExp v + 2 * eExp a ha v + 2 * eExp b hb v) + 1

theorem one_le_sqLev (v : HeightOneSpectrum (𝓞 F)) : 1 ≤ sqLev ha hb v := by unfold sqLev; omega

theorem sqLev_cond (v : HeightOneSpectrum (𝓞 F)) :
    2 * sExp v < sqLev ha hb v ∧ sExp v + eExp a ha v ≤ sqLev ha hb v := by unfold sqLev; omega

end Bad

/-! ### Products over the places -/

/-- **$\prod'_v\alpha^{(4)}_v = (\prod'_v\alpha^{(3)}_v)^2\prod_{v\in S}\alpha^{(4)}_v/(\alpha^{(3)}_v)^2$** when the two agree off $S$. -/
theorem tprod_sq_split {ι : Type*} (f g : ι → ℝ) (S : Finset ι) (hf : Multipliable f)
    (hg : Multipliable g) (hfg : ∀ i ∉ S, g i = f i ^ 2) (hf0 : ∀ i, f i ≠ 0) :
    ∏' i, g i = (∏' i, f i) ^ 2 * ∏ i ∈ S, g i / f i ^ 2 := by
  classical
  have hr : ∀ i ∉ S, g i / (f i * f i) = 1 := fun i hi => by
    rw [hfg i hi, sq, div_self (mul_ne_zero (hf0 i) (hf0 i))]
  have hmr : Multipliable fun i => g i / (f i * f i) := multipliable_of_ne_finset_one hr
  calc ∏' i, g i = ∏' i, ((f i * f i) * (g i / (f i * f i))) :=
        tprod_congr fun i => (mul_div_cancel₀ _ (mul_ne_zero (hf0 i) (hf0 i))).symm
    _ = (∏' i, (f i * f i)) * ∏' i, (g i / (f i * f i)) := (hf.mul hf).tprod_mul hmr
    _ = (∏' i, f i) ^ 2 * ∏ i ∈ S, g i / f i ^ 2 := by
        rw [hf.tprod_mul hf, tprod_eq_prod hr, sq]
        simp only [sq]

/-! ### The product formula and the archimedean identity -/

theorem valued_ab (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((NF.ι v (a * b) : v.adicCompletionIntegers F) : v.adicCompletion F) =
      exp (-((eExp a ha v + eExp b hb v : ℕ) : ℤ)) := by
  rw [coe_ι, show ((a * b : 𝓞 F) : F) = (a : F) * (b : F) by push_cast; ring, map_mul, map_mul,
    valued_eExp a ha v, valued_eExp b hb v, ← WithZero.exp_add]
  congr 1; push_cast; ring

/-- **The product formula for $ab$**: $\prod_{v\in S}q_v^{-(e_a(v)+e_b(v))} = \prod_w|\sigma_w(ab)|^{-1}$. -/
theorem prod_sqBad_q_pow [IsTotallyReal F] (ha : a ≠ 0) (hb : b ≠ 0) :
    ∏ v ∈ sqBad ha hb, ((LocalDensity.DVR.q (v.adicCompletionIntegers F) : ℝ) ^ (eExp a ha v + eExp b hb v))⁻¹ =
      (∏ w : {w : InfinitePlace F // w.IsReal}, |sigW w ((a : F) * (b : F))|)⁻¹ := by
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
  have h := QuadFormsKB.Tamagawa.finprod_norm_eq _ hab
  rw [prod_norm_embeddings_eq_prod_sigW] at h
  rw [← h, finprod_eq_prod_of_mulSupport_subset _ (s := S) (fun v hv => by
    by_contra hS
    apply Function.mem_mulSupport.mp hv
    show N v = 1
    rw [hN, hoff v hS, pow_zero, inv_one])]
  exact Finset.prod_congr rfl fun v _ => (hN v).symm

theorem cF_three_sq : cF F 3 ^ 2 = cF F 4 := by
  have hd : 0 ≤ |(discr F : ℝ)| := abs_nonneg _
  rw [cF, cF, ← Real.rpow_natCast, ← Real.rpow_mul hd]
  norm_num

/-- **The archimedean identity** $\mu^{(3)}_\infty(G^{(3)}_\infty)^2 = \mu^{(4)}_\infty(G_\infty)\cdot\prod_w|\sigma_w(ab)|^{-3}$. -/
theorem arch_identity [IsTotallyReal F] (ha : a ≠ 0) (hb : b ≠ 0) (hna : IsTotallyPos (-(a : F)))
    (hnb : IsTotallyPos (-(b : F))) (hQ : (qSq a b).Nondegenerate) :
    (muArchTamSO (QuatZeta.pureFormO a b) (nondegenerate_pureFormO a b ha hb) Set.univ).toReal ^ 2 =
      (muArchTamSO (qSq a b) hQ Set.univ).toReal *
        ((∏ w : {w : InfinitePlace F // w.IsReal}, |sigW w ((a : F) * (b : F))|)⁻¹) ^ 3 := by
  have hpd3 := hpd_pureFormO hna hnb
  have hpd4 := hpd_qSq hna hnb
  have hneg := fun w : {w : InfinitePlace F // w.IsReal} =>
    (⟨emb_neg_of_isTotallyPos_neg hna w.1 w.2, emb_neg_of_isTotallyPos_neg hnb w.1 w.2⟩ :
      sigW w (a : F) < 0 ∧ sigW w (b : F) < 0)
  rw [muArchTamSO_univ_toReal ha hb hpd3, muArchTamSO_qSq_univ hQ hpd4, ENNReal.toReal_mul, ENNReal.toReal_ofReal cF_nonneg,
    ENNReal.toReal_prod, ← cF_three_sq, mul_pow, ← Finset.prod_pow, ← Finset.prod_inv_distrib, ← Finset.prod_pow,
    mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  have hx : 0 < sigW w (a : F) * sigW w (b : F) := mul_pos_of_neg_of_neg (hneg w).1 (hneg w).2
  have hd : 0 < (sigW w (a : F)) ^ 2 * (sigW w (b : F)) ^ 2 := by
    rw [show (sigW w (a : F)) ^ 2 * (sigW w (b : F)) ^ 2 = (sigW w (a : F) * sigW w (b : F)) ^ 2 by ring]
    positivity
  rw [gramDetR_QRe_qSq, ENNReal.toReal_ofReal (by rw [archVolSO_four hd]; positivity), archVolSO_four hd,
    map_mul, abs_of_pos hx,
    show (sigW w (a : F)) ^ 2 * (sigW w (b : F)) ^ 2 = (sigW w (a : F) * sigW w (b : F)) ^ 2 by ring,
    Real.sqrt_sq hx.le]
  field_simp
  ring

/-! ### Box measures in real numbers -/

theorem muFin_boxSO_toReal {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v, Set (QuadFormsKB.Tamagawa.Measure.SOv v Q₀))
    (hU : ∀ v ∈ S, MeasurableSet (U v)) :
    (QuadFormsKB.Tamagawa.Measure.muFin Q₀ (fun _ => 1) (QuadFormsKB.Tamagawa.Measure.boxSO Q₀ S U)).toReal =
      QuadFormsKB.Tamagawa.Measure.finFactor Q₀ (fun _ => 1) *
        ∏ v ∈ S, (QuadFormsKB.Tamagawa.Measure.muLocSO v Q₀ 1 (U v)).toReal / NF.siegelDensity v Q₀ Q₀ := by
  rw [QuadFormsKB.Tamagawa.Measure.muFin_boxSO Q₀ hQ (fun _ => one_pos) S U hU, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (QuadFormsKB.Tamagawa.Measure.finFactor_nonneg Q₀ _), ENNReal.toReal_prod]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [ENNReal.toReal_div, QuadFormsKB.Tamagawa.Measure.muLocSO_soStabSO, div_one,
    ENNReal.toReal_ofReal (siegelDensity_self_pos' Q₀ hQ v).le]

theorem muFinQuat_quatBox_toReal (ha : a ≠ 0) (hb : b ≠ 0) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (QuatV (a : F) (b : F) v)ˣ) (hU : ∀ v ∈ S, MeasurableSet (U v)) :
    (muFinQuat (a : F) (b : F) (quatBox (a : F) (b : F) S U)).toReal =
      quatHatVol (a : F) (b : F) * ∏ v ∈ S, (omegaQuatV v (a : F) (b : F) (U v)).toReal /
        (omegaQuatV v (a : F) (b : F) (lamLocUnits (a : F) (b : F) v)).toReal := by
  rw [muFinQuat_quatBox_of_measurable (intA a) (intA b) (by exact_mod_cast ha) (by exact_mod_cast hb) S U hU,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (quatHatVol_pos (intA a) (intA b) (by exact_mod_cast ha) (by exact_mod_cast hb)).le,
    ENNReal.toReal_prod]
  congr 1
  exact Finset.prod_congr rfl fun v _ => ENNReal.toReal_div _ _

theorem muFinUnits_ideleBox_toReal (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)ˣ) (hU : ∀ v ∈ S, MeasurableSet (U v)) :
    (muFinUnits F (ideleBox S U)).toReal =
      ohatVol F * ∏ v ∈ S, (omegaV v (U v)).toReal / (omegaV v (unitsVSub v)).toReal := by
  rw [muFinUnits_ideleBox_of_measurable S U hU, ENNReal.toReal_mul, muFinUnits_OHatUnits,
    ENNReal.toReal_ofReal ohatVol_pos.le, ENNReal.toReal_prod]
  congr 1
  exact Finset.prod_congr rfl fun v _ => ENNReal.toReal_div _ _

/-! ### The final bookkeeping, abstractly -/

theorem real_assembly {ι : Type*} (S : Finset ι) (a3 a4 f3 Qv oh σ : ℝ)
    (L3 L4 α3 α4 wl wL wo wn wu qq : ι → ℝ) (e : ι → ℕ)
    (hα3 : ∀ v, α3 v ≠ 0) (hα4 : ∀ v, α4 v ≠ 0) (hwu : ∀ v, wu v ≠ 0) (hwL : ∀ v, wL v ≠ 0) (hqq : ∀ v, qq v ≠ 0)
    (hloc : ∀ v ∈ S, L4 v * wn v * wl v * qq v ^ (3 * e v) = L3 v ^ 2 * wo v * wu v)
    (harch : a3 ^ 2 = a4 * σ ^ 3) (hprod : ∏ v ∈ S, (qq v ^ e v)⁻¹ = σ) :
    a4 * ((f3 ^ 2 * ∏ v ∈ S, α4 v / α3 v ^ 2) * ∏ v ∈ S, L4 v / α4 v) *
        ((oh * ∏ v ∈ S, wn v / wu v) * (Qv * ∏ v ∈ S, wl v / wL v)) =
      (a3 * (f3 * ∏ v ∈ S, L3 v / α3 v)) ^ 2 * (Qv * ∏ v ∈ S, wo v / wL v) * oh := by
  have key : ∀ v ∈ S, α4 v / α3 v ^ 2 * (L4 v / α4 v) * (wn v / wu v) * (wl v / wL v) =
      (L3 v / α3 v) ^ 2 * (wo v / wL v) * ((qq v ^ e v)⁻¹) ^ 3 := by
    intro v hv
    have h := hloc v hv
    have hq3 : qq v ^ (3 * e v) ≠ 0 := pow_ne_zero _ (hqq v)
    rw [show (qq v ^ e v)⁻¹ ^ 3 = (qq v ^ (3 * e v))⁻¹ by rw [inv_pow, ← pow_mul, mul_comm (e v) 3]]
    have hα3' := hα3 v; have hα4' := hα4 v; have hwu' := hwu v; have hwL' := hwL v
    calc α4 v / α3 v ^ 2 * (L4 v / α4 v) * (wn v / wu v) * (wl v / wL v)
        = (L4 v * wn v * wl v * qq v ^ (3 * e v)) / (α3 v ^ 2 * wu v * wL v * qq v ^ (3 * e v)) := by
          field_simp
      _ = (L3 v ^ 2 * wo v * wu v) / (α3 v ^ 2 * wu v * wL v * qq v ^ (3 * e v)) := by rw [h]
      _ = (L3 v / α3 v) ^ 2 * (wo v / wL v) * (qq v ^ (3 * e v))⁻¹ := by
          field_simp
  have hP : (∏ v ∈ S, α4 v / α3 v ^ 2) * (∏ v ∈ S, L4 v / α4 v) * (∏ v ∈ S, wn v / wu v) *
      (∏ v ∈ S, wl v / wL v) = (∏ v ∈ S, L3 v / α3 v) ^ 2 * (∏ v ∈ S, wo v / wL v) * σ ^ 3 := by
    rw [← hprod, ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl key
  calc a4 * ((f3 ^ 2 * ∏ v ∈ S, α4 v / α3 v ^ 2) * ∏ v ∈ S, L4 v / α4 v) *
        ((oh * ∏ v ∈ S, wn v / wu v) * (Qv * ∏ v ∈ S, wl v / wL v))
      = a4 * f3 ^ 2 * oh * Qv * ((∏ v ∈ S, α4 v / α3 v ^ 2) * (∏ v ∈ S, L4 v / α4 v) *
          (∏ v ∈ S, wn v / wu v) * (∏ v ∈ S, wl v / wL v)) := by ring
    _ = (a4 * σ ^ 3) * f3 ^ 2 * oh * Qv * ((∏ v ∈ S, L3 v / α3 v) ^ 2 * (∏ v ∈ S, wo v / wL v)) := by
        rw [hP]; ring
    _ = _ := by rw [← harch]; ring

/-! ### The theorem -/

set_option maxHeartbeats 4000000 in
/-- **Weil's local-ratio identity for the square model** ($m = 4$, $D = (a,b)_F$ totally definite over a totally real $F$,
any class number): $\Phi_*\mu_P = \mu_{\mathrm{Tam}}$ for the $\Phi$ = `sqPEquiv`. -/
@[kb "weil1982" "Thm 2.3.1 (local ratios, ∏_v r_v = 1); §3.7, p. 65 [unverified page]"]
theorem map_muP_sqPEquiv_eq_muTam [IsTotallyReal F] (ha : a ≠ 0) (hb : b ≠ 0) (hna : IsTotallyPos (-(a : F)))
    (hnb : IsTotallyPos (-(b : F))) (hQ : (qSq a b).Nondegenerate) :
    ((gnatSqO ha hb).muP (muSq ha hb)).map (sqPEquiv ha hb) = muTam (qSq a b) hQ (fun _ => 1) := by
  set S := sqBad ha hb
  set m := sqLev ha hb
  have hm1 := one_le_sqLev ha hb
  have hS : ∀ v ∉ S, Valued.v (2 : v.adicCompletion F) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
        Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1 := fun v hv => good_of_not_mem_sqBad ha hb hv
  have hmS : ∀ v ∈ S, 2 * sExp v < m v ∧ sExp v + eExp a ha v ≤ m v := fun v _ => sqLev_cond ha hb v
  have hpd4 := hpd_qSq hna hnb
  have hpd3 := hpd_pureFormO hna hnb
  have hQ3 := nondegenerate_pureFormO a b ha hb
  have hdiv := hdiv_of_totallyNeg (F := F) (a := (a : F)) (b := (b : F))
    (fun w hw => emb_neg_of_isTotallyPos_neg hna w hw) (fun w hw => emb_neg_of_isTotallyPos_neg hnb w hw)
  refine map_muP_sq_eq_of_compact_open ha hb hQ (isCompact_boxK S m hm1 hQ hpd4) (isOpen_boxK S m hm1)
    (nonempty_boxK S m hm1) ?_
  have hA := muP_boxK_mul S m hm1 ha hb hna hnb hS hmS
  have hD := muPD_pdMk_HS ha hb S m hm1 hQ3 hpd3 hdiv hS hmS
  -- names
  set P := (gnatSqO ha hb).muP (muSq ha hb) (sqPEquiv ha hb ⁻¹' boxK S m hm1) with hP
  set A3 := muArchTamSO (QuatZeta.pureFormO a b) hQ3 Set.univ
  set A4 := muArchTamSO (qSq a b) hQ Set.univ
  set M3 := QuadFormsKB.Tamagawa.Measure.muFin (QuatZeta.pureFormO a b) (fun _ => 1)
    (QuadFormsKB.Tamagawa.Measure.boxSO (QuatZeta.pureFormO a b) S (congSO3S m hm1))
  set M4 := QuadFormsKB.Tamagawa.Measure.muFin (qSq a b) (fun _ => 1)
    (QuadFormsKB.Tamagawa.Measure.boxSO (qSq a b) S (congSOS m hm1))
  set qH := muFinQuat (a : F) (b : F) (quatCongS a b S m hm1)
  set qE := muFinQuat (a : F) (b : F) (econgS a b S m)
  set N := muFinUnits F (NE S m)
  set U := muFinUnits F (OHatUnits F)
  have hT : muTam (qSq a b) hQ (fun _ => 1) (boxK S m hm1) = A4 * M4 := by
    rw [boxK, muTam, Measure.prod_prod]
  rw [hT]
  classical
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
      (Measure.muLoc v (QuatZeta.pureFormO a b) 1 (congSub v (QuatZeta.pureFormO a b) (m v) (hm1 v) : Set _)).toReal := fun v hv => by
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
  have harch := arch_identity ha hb hna hnb hQ
  have hprod := prod_sqBad_q_pow ha hb
  -- finiteness and positivity
  have hH := isHaarMeasure_muFinQuat' ha hb
  have hqH0 : qH ≠ 0 :=
    ((isOpen_quatCongS S m hm1).measure_pos (muFinQuat (a : F) (b : F)) ⟨1, (quatCongS a b S m hm1).one_mem⟩).ne'
  have hqHt : qH ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (fun u hu => ?_)) (by
      rw [muFinQuat_lamHatUnits]; exact ENNReal.ofReal_lt_top))
    exact ((mem_quatCongS a b S m hm1).1 hu).1 |> (mem_lamHatUnits_iff _ _ u).2
  have hqEt : qE ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (fun u hu => ?_)) (by
      rw [muFinQuat_lamHatUnits]; exact ENNReal.ofReal_lt_top))
    exact ((mem_econgS a b S m).1 hu).1 |> (mem_lamHatUnits_iff _ _ u).2
  have hUt : U ≠ ⊤ := by rw [show U = ENNReal.ofReal (ohatVol F) from muFinUnits_OHatUnits]; exact ENNReal.ofReal_ne_top
  have hwu : ∀ v : HeightOneSpectrum (𝓞 F), 0 < (omegaV v (unitsVSub v)).toReal := fun v =>
    ENNReal.toReal_pos (omegaV_unitsVSub_ne_zero v) (omegaV_unitsVSub_ne_top v)
  have hwn : ∀ v : HeightOneSpectrum (𝓞 F), 0 < (omegaV v (nU m v)).toReal := by
    intro v
    have h := omegaV_oneAdd v (k := m v + sExp v) (Nat.le_add_right_of_le (hm1 v))
    change (omegaV v {r : (v.adicCompletion F)ˣ | Valued.v ((r : v.adicCompletion F) - 1) ≤
      exp (-((m v + sExp v : ℕ) : ℤ))}).toReal > 0
    rw [h, selfDualV_latticeV_nat, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast]
    exact div_pos (selfDualV_real_pos v) (pow_pos (by exact_mod_cast DVR.q_pos (R := v.adicCompletionIntegers F)) _)
  have hNpos : 0 < N.toReal := by
    have hnn' : N.toReal = ohatVol F * ∏ v ∈ S, (omegaV v (nU m v)).toReal / (omegaV v (unitsVSub v)).toReal := hnn
    rw [hnn']
    exact mul_pos ohatVol_pos (Finset.prod_pos fun v _ => div_pos (hwn v) (hwu v))
  have hN0 : N ≠ 0 := fun h => by rw [h, ENNReal.toReal_zero] at hNpos; exact lt_irrefl _ hNpos
  have hNt : N ≠ ⊤ := fun h => by rw [h, ENNReal.toReal_top] at hNpos; exact lt_irrefl _ hNpos
  have hA3t : A3 ≠ ⊤ := by
    rw [show A3 = _ from muArchTamSO_univ ha hb hpd3]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top)
  have hA4t : A4 ≠ ⊤ := by
    rw [show A4 = _ from muArchTamSO_qSq_univ hQ hpd4]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top)
  have hM3t : M3 ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) (by
      rw [QuadFormsKB.Tamagawa.Measure.muFin_KSO]; exact ENNReal.ofReal_lt_top))
    rw [show congSO3S (a := a) (b := b) m hm1 = congSOgen (QuatZeta.pureFormO a b) m hm1 from rfl, ← coe_boxSub]
    exact inf_le_left
  have hM4t : M4 ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) (by
      rw [QuadFormsKB.Tamagawa.Measure.muFin_KSO]; exact ENNReal.ofReal_lt_top))
    rw [show congSOS (a := a) (b := b) m hm1 = congSOgen (qSq a b) m hm1 from rfl, ← coe_boxSub]
    exact inf_le_left
  -- the identity in real numbers
  have hreal : (A4 * M4 * (N * qH)).toReal = ((A3 * M3) ^ 2 * qE * U).toReal := by
    have hnn' : N.toReal = ohatVol F * ∏ v ∈ S, (omegaV v (nU m v)).toReal / (omegaV v (unitsVSub v)).toReal := hnn
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow]
    rw [hm4, hnn', hqh, hm3, hqe, huu, hf4]
    exact real_assembly S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (fun v => (siegelDensity_self_pos' _ hQ3 v).ne') (fun v => (siegelDensity_self_pos' _ hQ v).ne')
      (fun v => (hwu v).ne')
      (fun v => (ENNReal.toReal_pos (omegaQuatV_lamLocUnits_ne_zero _ _ v)
        (omegaQuatV_lamLocUnits_ne_top _ _ v)).ne')
      (fun v => (Nat.cast_pos.2 (DVR.q_pos (R := v.adicCompletionIntegers F))).ne')
      hloc harch hprod
  have hX : A4 * M4 * (N * qH) = (A3 * M3) ^ 2 * qE * U :=
    (ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top (ENNReal.mul_ne_top hA4t hM4t) (ENNReal.mul_ne_top hNt hqHt))
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.mul_ne_top hA3t hM3t)) hqEt) hUt)).1 hreal
  rw [hD] at hA
  have hPT : P * (N * qH) = A4 * M4 * (N * qH) := by rw [← mul_assoc, hA, hX]
  exact (ENNReal.mul_left_inj (mul_ne_zero hN0 hqH0) (ENNReal.mul_ne_top hNt hqHt)).1 hPT

end QuadFormsKB.Tamagawa.Measure.Weil
