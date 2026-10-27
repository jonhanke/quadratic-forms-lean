import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereConst

/-!
# The box formula $\sigma_{\mathbb A} = \bigotimes_v\sigma_v$

Totally real $F$, $N = k + 1\ge4$. For measurable $A_w\subseteq T(\rho)_w$ (real places),
(**`sphereMeasure_boxA`**)
$$\sigma_{\mathbb A}\Big(\prod_wA_w\times\prod_v(T_v\cap L_v)\Big) =
  \frac{c_F(N)}{c_F(N-1)}\prod_v\sigma_v(T_v\cap L_v)\cdot\prod_w\sigma_w(A_w),$$
$\sigma_v$, $\sigma_w$ the Leray measures of $Q_0$ on the local spheres (the finite-place and archimedean `sig`), $c_F(n) = |d_F|^{-n(n-1)/4}$.
The local constants $c_v = |\det G/d|_v^N|2\rho|_v^{-k}$ cancel by the product formula
(`prod_cReal_mul_tprod_cFin`).
-/

open MeasureTheory Set Matrix
open scoped ENNReal RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

/-- **A quotient of convergent products, modified at finitely many places.** -/
theorem hasProd_of_ratio {ι : Type*} [DecidableEq ι] {α β a : ι → ℝ} {A B : ℝ} (S : Finset ι)
    (hα : HasProd α A) (hβ : HasProd β B) (hB : B ≠ 0) (hβpos : ∀ v, 0 < β v) (hαpos : ∀ v, 0 < α v)
    (hoff : ∀ v ∉ S, α v = a v * β v) :
    HasProd a (A / B * ∏ v ∈ S, (a v * β v / α v)) := by
  have hg : HasProd (fun v => α v / β v) (A / B) := by
    have h1 : Filter.Tendsto (fun s : Finset ι => ∏ i ∈ s, α i) Filter.atTop (nhds A) := hα
    have h2 : Filter.Tendsto (fun s : Finset ι => ∏ i ∈ s, β i) Filter.atTop (nhds B) := hβ
    have h3 := Filter.Tendsto.div h1 h2 hB
    show Filter.Tendsto (fun s : Finset ι => ∏ i ∈ s, α i / β i) Filter.atTop (nhds (A / B))
    simp only [Finset.prod_div_distrib]
    exact h3
  have hh : HasProd (fun v => if v ∈ S then a v * β v / α v else 1) (∏ v ∈ S, (a v * β v / α v)) := by
    have h1 : HasProd (fun v => if v ∈ S then a v * β v / α v else 1)
        (∏ v ∈ S, (if v ∈ S then a v * β v / α v else 1)) :=
      hasProd_prod_of_ne_finset_one fun v hv => by simp [hv]
    rwa [Finset.prod_congr rfl fun v hv => (show (if v ∈ S then a v * β v / α v else 1) = a v * β v / α v by
      simp [hv])] at h1
  convert hg.mul hh using 1
  funext v
  by_cases hv : v ∈ S
  · simp only [hv, if_true]
    field_simp [(hβpos v).ne', (hαpos v).ne']
  · simp only [hv, if_false, mul_one]
    rw [hoff v hv]; field_simp [(hβpos v).ne']

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.Measure.SphereLeray

variable {F : Type} [Field F] [NumberField F] {k : ℕ} {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F}

theorem measurableSet_intVec (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} :
    MeasurableSet {x : Fin n → v.adicCompletion F | IntVec v x} := by
  have h1 : MeasurableSet {a : v.adicCompletion F | Valued.v a ≤ 1} := by
    have := (measurable_id.prodMk (measurable_const (a := (1 : v.adicCompletion F)))) (measurableSet_valued_le v)
    simpa using this
  have : {x : Fin n → v.adicCompletion F | IntVec v x} = ⋂ i, (fun x => x i) ⁻¹' {a | Valued.v a ≤ 1} := by
    ext x; simp [IntVec]
  rw [this]
  exact MeasurableSet.iInter fun i => (measurable_pi_apply i) h1

theorem measurableSet_intSph (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (AdelicSphereSetup.intSph Q₀ ρ v) :=
  measurable_subtype_coe (measurableSet_intVec v)

open scoped Pointwise in
/-- A symmetric neighbourhood of $1$ of positive finite Haar measure. -/
theorem exists_symm_nbhd {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G] (μ : Measure G) [μ.IsHaarMeasure] :
    ∃ U : Set G, MeasurableSet U ∧ (∀ g, g⁻¹ ∈ U ↔ g ∈ U) ∧ μ U ≠ 0 ∧ μ U ≠ ∞ := by
  obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : G)
  refine ⟨K ∩ K⁻¹, hKc.isClosed.measurableSet.inter hKc.inv.isClosed.measurableSet, fun g => ?_,
    (μ.measure_pos_of_mem_nhds (Filter.inter_mem hK1 (inv_mem_nhds_one G hK1))).ne',
    ne_top_of_le_ne_top hKc.measure_lt_top.ne (measure_mono inter_subset_left)⟩
  simp only [mem_inter_iff, Set.mem_inv, inv_inv]
  exact and_comm

namespace AdelicSphereSetup

variable (S : AdelicSphereSetup Q₀ ρ) (hρ : ρ ≠ 0) (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

theorem measurableSet_boxA (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (Sph (QRe Q₀ w) (σR w ρ)))
    (hAR : ∀ w, MeasurableSet (AR w)) : MeasurableSet (boxA Q₀ ρ AR) := by
  simp only [boxA, Set.ofPred_and, Set.ofPred_forall]
  refine (MeasurableSet.iInter fun w : {w : InfinitePlace F // w.IsReal} => ?_).inter
    (MeasurableSet.iInter fun v : HeightOneSpectrum (𝓞 F) => ?_)
  · exact (Measurable.subtype_mk (measurable_adR Q₀ ρ w)) (hAR w)
  · exact (measurable_adV Q₀ ρ v) (measurableSet_intVec v)

theorem measurableSet_boxB (BR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ArchSO (QRe S.C.Q' w)))
    (hBR : ∀ w, MeasurableSet (BR w)) : MeasurableSet (S.boxB BR) := by
  simp only [boxB, Set.ofPred_and, Set.ofPred_forall]
  refine (MeasurableSet.iInter fun w : {w : InfinitePlace F // w.IsReal} => ?_).inter ?_
  · exact (measurable_pi_apply w).comp (measurable_fst.comp measurable_fst) (hBR w)
  · exact measurable_snd (isOpen_KSO S.C.Q').measurableSet

/-- The bad places, as a finite set. -/
def badFin (hρ : ρ ≠ 0) : Finset (HeightOneSpectrum (𝓞 F)) :=
  (Filter.eventually_cofinite.mp (S.eventually_goodFin hρ)).toFinset

theorem goodFin_of_not_mem {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S.badFin hρ) : S.GoodFin v := by
  by_contra h
  exact hv ((Set.Finite.mem_toFinset _).mpr h)

theorem finBox_eq :
    {g : SOAf Q₀ | ∀ v, evalSO Q₀ v g ∈ S.EV hρ v} = boxSO Q₀ (S.badFin hρ) (S.EV hρ) := by
  ext g
  simp only [mem_setOf_eq, boxSO]
  constructor
  · intro h
    refine ⟨fun v _ => h v, fun v hv => ?_⟩
    have := h v
    rwa [EV, S.secMulImage_good hρ v (S.goodFin_of_not_mem hρ hv)] at this
  · rintro ⟨h1, h2⟩ v
    by_cases hv : v ∈ S.badFin hρ
    · exact h1 v hv
    · rw [EV, S.secMulImage_good hρ v (S.goodFin_of_not_mem hρ hv)]; exact h2 v hv

open Classical in
/-- **The box formula** (totally real $F$, $N = k+1\ge4$):
$\sigma_{\mathbb A}\big(\prod_wA_w\times\prod_v(T_v\cap L_v)\big) = \frac{c_F(N)}{c_F(N-1)}\prod_v\sigma_v(T_v\cap L_v)
\prod_w\sigma_w(A_w)$. -/
theorem sphereMeasure_boxA [IsEmpty {w : InfinitePlace F // w.IsComplex}] (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (Sph (QRe Q₀ w) (σR w ρ)))
    (hAR : ∀ w, MeasurableSet (AR w)) (hfin : ∀ v, sigV Q₀ ρ hQ v (intSph Q₀ ρ v) ≠ ⊤) :
    S.sphereMeasure hρ hQ hk (boxA Q₀ ρ AR) =
      ENNReal.ofReal (cF F (k + 1) / cF F k * ∏' v, (sigV Q₀ ρ hQ v (intSph Q₀ ρ v)).toReal) *
        ∏ w, sig (QRe Q₀ w) (σR w ρ) (AR w) := by
  have hk1 : 1 ≤ k := by omega
  -- the auxiliary symmetric sets at the real places
  have hBex : ∀ w : {w : InfinitePlace F // w.IsReal}, ∃ U : Set (ArchSO (QRe S.C.Q' w)), MeasurableSet U ∧
      (∀ g, g⁻¹ ∈ U ↔ g ∈ U) ∧ lerayMeasure (QRe S.C.Q' w) (gramDetR_QRe_ne_zero S.C.Q' S.C.hQ' w) U ≠ 0 ∧
      lerayMeasure (QRe S.C.Q' w) (gramDetR_QRe_ne_zero S.C.Q' S.C.hQ' w) U ≠ ∞ := fun w => by
    have := isHaarMeasure_lerayMeasure (gramDetR_QRe_ne_zero S.C.Q' S.C.hQ' w)
    exact exists_symm_nbhd _
  choose BR hBRm hBRs hBR0 hBRt using hBex
  have hB := S.measurableSet_boxB BR hBRm
  have hBsym : ∀ h, h⁻¹ ∈ S.boxB BR ↔ h ∈ S.boxB BR := fun h => by
    simp only [boxB, mem_setOf_eq, Prod.fst_inv, Pi.inv_apply, Prod.snd_inv, inv_mem_iff, hBRs]
  have hA := measurableSet_boxA AR hAR
  have key := S.sphereMeasure_mul_secMulImage hρ hQ hk hA hB hBsym
  rw [S.secMulImage_box hρ AR BR] at key
  rw [show {g : SOAdele Q₀ | (∀ w, g.1.1 w ∈ S.ER hρ AR BR w) ∧ ∀ v, evalSO Q₀ v g.2 ∈ S.EV hρ v} =
      {g | (∀ w, g.1.1 w ∈ S.ER hρ AR BR w) ∧ g.2 ∈ {gf : SOAf Q₀ | ∀ v, evalSO Q₀ v gf ∈ S.EV hρ v}} from rfl,
    muTam_prodSet, S.finBox_eq hρ] at key
  rw [show S.boxB BR = {h : SOAdele S.C.Q' | (∀ w, h.1.1 w ∈ BR w) ∧ h.2 ∈ (KSO S.C.Q' : Set (SOAf S.C.Q'))}
      from rfl, muTam_prodSet, muFin_KSO] at key
  -- the finite box
  have hEV : ∀ v ∈ S.badFin hρ, MeasurableSet (S.EV hρ v) := fun v _ =>
    (S.measurableSet_secMulImage hρ hQ v (measurableSet_intSph v) (isOpen_soStabSO v S.C.Q').measurableSet).1
  have hmult := multipliable_muLocSO_one Q₀ hQ (by omega : k + 1 ≠ 0) (by omega : k + 1 ≠ 2)
  rw [muFin_boxSO_split Q₀ hQ (fun _ => one_pos) hmult _ _ hEV] at key
  -- real numbers
  set a : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (sigV Q₀ ρ hQ v (intSph Q₀ ρ v)).toReal with ha
  set β : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    (muLocSO v S.C.Q' 1 (soStabSO v S.C.Q' : Set (SOv v S.C.Q'))).toReal with hβ
  set α : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    (muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀))).toReal with hα
  set c : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (S.cFin v).toReal with hc
  set r : {w : InfinitePlace F // w.IsReal} → ℝ := fun w => (S.cReal w).toReal with hr
  have hβK : ∀ v, muLocSO v S.C.Q' 1 (soStabSO v S.C.Q' : Set (SOv v S.C.Q')) = ENNReal.ofReal (β v) := fun v => by
    rw [hβ, ENNReal.ofReal_toReal]; rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top
  have hαK : ∀ v, muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀)) = ENNReal.ofReal (α v) := fun v => by
    rw [hα, ENNReal.ofReal_toReal]; rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top
  have haK : ∀ v, sigV Q₀ ρ hQ v (intSph Q₀ ρ v) = ENNReal.ofReal (a v) := fun v => by
    rw [ha, ENNReal.ofReal_toReal (hfin v)]
  have hcK : ∀ v, S.cFin v = ENNReal.ofReal (c v) := fun v => by
    rw [hc, ENNReal.ofReal_toReal]; rw [S.cFin_eq hρ v]; exact ENNReal.ofReal_ne_top
  have hrK : ∀ w, S.cReal w = ENNReal.ofReal (r w) := fun w => by
    rw [hr, ENNReal.ofReal_toReal (S.cReal_ne_top hρ w)]
  have hβpos : ∀ v, 0 < β v := fun v => ENNReal.toReal_pos (muLocSO_soStabSO_pos S.C.Q' S.C.hQ' v one_pos)
    (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)
  have hαpos : ∀ v, 0 < α v := fun v => ENNReal.toReal_pos (muLocSO_soStabSO_pos Q₀ hQ v one_pos)
    (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)
  have ha0 : ∀ v, 0 ≤ a v := fun v => ENNReal.toReal_nonneg
  have hc0 : ∀ v, 0 ≤ c v := fun v => ENNReal.toReal_nonneg
  have hr0 : ∀ w, 0 ≤ r w := fun w => ENNReal.toReal_nonneg
  -- the local identities
  have hERw : ∀ w, lerayMeasure (QRe Q₀ w) (gramDetR_QRe_ne_zero Q₀ hQ w) (S.ER hρ AR BR w) =
      ENNReal.ofReal (r w) * sig (QRe Q₀ w) (σR w ρ) (AR w) *
        lerayMeasure (QRe S.C.Q' w) (gramDetR_QRe_ne_zero S.C.Q' S.C.hQ' w) (BR w) := fun w => by
    rw [ER, S.localFib_real' hρ hQ w (hAR w) (hBRm w), hrK]
  have hEVv : ∀ v, muLocSO v Q₀ 1 (S.EV hρ v) = ENNReal.ofReal (c v * a v * β v) := fun v => by
    rw [EV, S.localFib_fin' hρ hQ v hk1 (measurableSet_intSph v) (isOpen_soStabSO v S.C.Q').measurableSet,
      hcK, haK, hβK, ← ENNReal.ofReal_mul (hc0 v), ← ENNReal.ofReal_mul (mul_nonneg (hc0 v) (ha0 v))]
  have hgood : ∀ v ∉ S.badFin hρ, α v = a v * β v := fun v hv => by
    have := S.muLocSO_soStab_good hρ hQ v hk1 (S.goodFin_of_not_mem hρ hv)
    rw [hαK, haK, hβK, ← ENNReal.ofReal_mul (ha0 v)] at this
    exact (ENNReal.ofReal_eq_ofReal_iff (hαpos v).le (mul_nonneg (ha0 v) (hβpos v).le)).mp this
  have hcgood : ∀ v ∉ S.badFin hρ, c v = 1 := fun v hv => by
    show (S.cFin v).toReal = 1
    rw [S.cFin_good v (S.goodFin_of_not_mem hρ hv), ENNReal.toReal_one]
  simp only [hERw, hEVv] at key
  -- the real identity
  set Sb := S.badFin hρ
  have hmultβ := multipliable_muLocSO_one S.C.Q' S.C.hQ' (by omega : k ≠ 0) (by omega : k ≠ 2)
  have hBpos : 0 < ∏' v, β v := by
    have := tprod_siegelDensity_pos (by omega : 3 ≤ k) S.C.Q' S.C.hQ'
    rw [← finFactor_one S.C.Q' S.C.hQ'] at this
    exact this
  have hsplitα : ∏' v, α v = (∏ v ∈ Sb, α v) * ∏' v, (if v ∈ Sb then 1 else α v) :=
    tprod_eq_prod_mul_tprod_ite α hmult Sb fun v _ => (hαpos v).ne'
  have hratio := (hasProd_of_ratio Sb hmult.hasProd hmultβ.hasProd hBpos.ne' hβpos hαpos hgood).tprod_eq
  have hcS : ∏' v, c v = ∏ v ∈ Sb, c v := tprod_eq_prod fun v hv => hcgood v hv
  have hprod := S.prod_cReal_mul_tprod_cFin hρ
  rw [show (fun v => (S.cFin v).toReal) = c from rfl, hcS] at hprod
  have hαS : 0 < ∏ v ∈ Sb, α v := Finset.prod_pos fun v _ => hαpos v
  have hcF : 0 < cF F k := cF_pos'
  have hreal : cF F (k + 1) * (∏ w, r w) * (∏ v ∈ Sb, (c v * a v * β v)) *
      (∏' v, if v ∈ Sb then 1 else α v) =
      cF F (k + 1) / cF F k * (∏' v, a v) * cF F k * ∏' v, β v := by
    have e1 : ∏' v, (if v ∈ Sb then 1 else α v) = (∏' v, α v) / ∏ v ∈ Sb, α v := by
      rw [hsplitα]; field_simp
    rw [e1, hratio, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_div_distrib,
      Finset.prod_mul_distrib]
    have e2 : (∏ w, r w) * ∏ v ∈ Sb, c v = 1 := hprod
    have hc0' : ∏ v ∈ Sb, c v ≠ 0 := by intro h; rw [h, mul_zero] at e2; exact zero_ne_one e2
    have e2' : ∏ w, r w = (∏ v ∈ Sb, c v)⁻¹ := eq_inv_of_mul_eq_one_left e2
    rw [e2']
    have hB0 : ∏' v, β v ≠ 0 := hBpos.ne'
    simp only [← hβ]
    field_simp
  -- back to `ℝ≥0∞`
  set P := ∏ w, sig (QRe Q₀ w) (σR w ρ) (AR w)
  set M := ∏ w, lerayMeasure (QRe S.C.Q' w) (gramDetR_QRe_ne_zero S.C.Q' S.C.hQ' w) (BR w)
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => hBR0 w
  have hMt : M ≠ ⊤ := ENNReal.prod_ne_top fun w _ => hBRt w
  have hr' : ∏ w, (ENNReal.ofReal (r w) * sig (QRe Q₀ w) (σR w ρ) (AR w) *
      lerayMeasure (QRe S.C.Q' w) (gramDetR_QRe_ne_zero S.C.Q' S.C.hQ' w) (BR w)) =
      ENNReal.ofReal (∏ w, r w) * P * M := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ENNReal.ofReal_prod_of_nonneg fun w _ => hr0 w]
  have hS' : ∏ v ∈ Sb, ENNReal.ofReal (c v * a v * β v) = ENNReal.ofReal (∏ v ∈ Sb, (c v * a v * β v)) :=
    (ENNReal.ofReal_prod_of_nonneg fun v _ => mul_nonneg (mul_nonneg (hc0 v) (ha0 v)) (hβpos v).le).symm
  rw [hr', hS', show finFactor S.C.Q' (fun _ => 1) = ∏' v, β v from rfl] at key
  have hite0 : 0 ≤ ∏' v, (if v ∈ Sb then 1 else α v) :=
    tprod_nonneg fun v => by split_ifs; exacts [zero_le_one, (hαpos v).le]
  have hD0 : ENNReal.ofReal (cF F k) * M * ENNReal.ofReal (∏' v, β v) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ENNReal.ofReal_pos.mpr hcF).ne' hM0) (ENNReal.ofReal_pos.mpr hBpos).ne'
  have hDt : ENNReal.ofReal (cF F k) * M * ENNReal.ofReal (∏' v, β v) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hMt) ENNReal.ofReal_ne_top
  apply (ENNReal.mul_left_inj hD0 hDt).mp
  rw [key]
  have hY0 : 0 ≤ cF F (k + 1) / cF F k * ∏' v, a v :=
    mul_nonneg (div_nonneg cF_pos'.le hcF.le) (tprod_nonneg ha0)
  calc ENNReal.ofReal (cF F (k + 1)) * (ENNReal.ofReal (∏ w, r w) * P * M) *
        (ENNReal.ofReal (∏ v ∈ Sb, (c v * a v * β v)) * ENNReal.ofReal (∏' v, if v ∈ Sb then 1 else α v))
      = ENNReal.ofReal (cF F (k + 1) * (∏ w, r w) * (∏ v ∈ Sb, (c v * a v * β v)) *
          (∏' v, if v ∈ Sb then 1 else α v)) * P * M := by
        rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg cF_pos'.le (Finset.prod_nonneg fun w _ => hr0 w))
            (Finset.prod_nonneg fun v _ => mul_nonneg (mul_nonneg (hc0 v) (ha0 v)) (hβpos v).le)),
          ENNReal.ofReal_mul (mul_nonneg cF_pos'.le (Finset.prod_nonneg fun w _ => hr0 w)),
          ENNReal.ofReal_mul cF_pos'.le]
        ring
    _ = ENNReal.ofReal (cF F (k + 1) / cF F k * (∏' v, a v) * cF F k * ∏' v, β v) * P * M := by rw [hreal]
    _ = ENNReal.ofReal (cF F (k + 1) / cF F k * ∏' v, a v) * P *
          (ENNReal.ofReal (cF F k) * M * ENNReal.ofReal (∏' v, β v)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hY0 hcF.le), ENNReal.ofReal_mul hY0]
        ring


end AdelicSphereSetup

end QuadFormsKB.Tamagawa.Measure.Weil

end
