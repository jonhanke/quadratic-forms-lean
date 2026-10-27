import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereDensitiesProof
import QuadFormsKB.Tamagawa.Measure.Weil.LintegralPiProd

/-!
# The box formula with finitely many free finite places

Totally real $F$, $N = k+1\ge4$. The box formula `sphereMeasure_boxA` fixes $A_v = T_v\cap L_v$ at every finite
place. Here $A_v$ is any measurable subset of $T_v$ of finite Leray measure, equal to $T_v\cap L_v$ outside a finite set
(**`sphereMeasure_boxG`**):
$$\sigma_{\mathbb A}\Big(\prod_wA_w\times\prod_vA_v\Big) = \frac{c_F(N)}{c_F(N-1)}\prod_v\sigma_v(A_v)\cdot\prod_w\sigma_w(A_w).$$
Same proof (the local identity `localFib_fin'` holds for every measurable $A_v$; the bad set of `muFin_boxSO_split` is
enlarged by the free places). Consequences: the image of $\sigma_{\mathbb A}$ restricted to such a box at the real places
(**`map_projR_restrict_boxG`**) and the integral of a product function over the box (**`lintegral_boxG_prod`**).
-/

open MeasureTheory Set Matrix
open scoped ENNReal RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.Measure.SphereLeray

variable {F : Type} [Field F] [NumberField F] {k : ℕ} {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F}

namespace AdelicSphereSetup

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

variable (Q₀ ρ) in
/-- **The product set** $\prod_wA_w\times\prod_vA_v$ in $T(\rho)_{\mathbb A}$. -/
def boxG (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (Sph (QRe Q₀ w) (σR w ρ)))
    (AV : ∀ v : HeightOneSpectrum (𝓞 F), Set (sphV Q₀ ρ v)) : Set (adelicSphere Q₀ ρ) :=
  {y | (∀ w, (⟨adR y.1 w, (mem_sphR_iff Q₀ ρ w _).mpr (y.2.1 w)⟩ : Sph (QRe Q₀ w) (σR w ρ)) ∈ AR w) ∧
    ∀ v, (⟨adV y.1 v, (mem_sphV_iff Q₀ ρ v _).mpr (y.2.2.2 v)⟩ : sphV Q₀ ρ v) ∈ AV v}

theorem measurableSet_boxG (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (Sph (QRe Q₀ w) (σR w ρ)))
    (hAR : ∀ w, MeasurableSet (AR w)) (AV : ∀ v : HeightOneSpectrum (𝓞 F), Set (sphV Q₀ ρ v))
    (hAV : ∀ v, MeasurableSet (AV v)) : MeasurableSet (boxG Q₀ ρ AR AV) := by
  simp only [boxG, Set.ofPred_and, Set.ofPred_forall]
  refine (MeasurableSet.iInter fun w : {w : InfinitePlace F // w.IsReal} => ?_).inter
    (MeasurableSet.iInter fun v : HeightOneSpectrum (𝓞 F) => ?_)
  · exact (Measurable.subtype_mk (measurable_adR Q₀ ρ w)) (hAR w)
  · exact (Measurable.subtype_mk (measurable_adV Q₀ ρ v)) (hAV v)

variable (S : AdelicSphereSetup Q₀ ρ) (hρ : ρ ≠ 0) (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k)

/-- The local images at the finite places for general $A_v$: $s_v(A_v)\,\iota_v(SO(L'_v))$. -/
def EVG (AV : ∀ v : HeightOneSpectrum (𝓞 F), Set (sphV Q₀ ρ v)) (v : HeightOneSpectrum (𝓞 F)) : Set (SOv v Q₀) :=
  secMulImage (S.secSO hρ v) (S.iotaSO v) (AV v) (soStabSO v S.C.Q' : Set (SOv v S.C.Q'))

set_option maxHeartbeats 1000000 in
/-- **$s(A)\,\iota(B)$ for the generalized product sets is a product set.** -/
theorem secMulImage_boxG [IsEmpty {w : InfinitePlace F // w.IsComplex}] (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (Sph (QRe Q₀ w) (σR w ρ)))
    (BR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ArchSO (QRe S.C.Q' w)))
    (T : Finset (HeightOneSpectrum (𝓞 F))) (AV : ∀ v : HeightOneSpectrum (𝓞 F), Set (sphV Q₀ ρ v))
    (hAVT : ∀ v ∉ T, AV v = intSph Q₀ ρ v) :
    secMulImage (S.sphereSection hρ) S.iota (boxG Q₀ ρ AR AV) (S.boxB BR) =
      {g | (∀ w, g.1.1 w ∈ S.ER hρ AR BR w) ∧ ∀ v, evalSO Q₀ v g.2 ∈ S.EVG hρ AV v} := by
  ext g
  constructor
  · rintro ⟨y, hy, h, hh, rfl⟩
    refine ⟨fun w => ⟨⟨adR y.1 w, (mem_sphR_iff Q₀ ρ w _).mpr (y.2.1 w)⟩, hy.1 w, h.1.1 w, hh.1 w, ?_⟩,
      fun v => ⟨⟨adV y.1 v, (mem_sphV_iff Q₀ ρ v _).mpr (y.2.2.2 v)⟩, hy.2 v, evalSO S.C.Q' v h.2,
      (mem_KSO_iff S.C.Q' h.2).mp hh.2 v, ?_⟩⟩
    · rw [← S.secInf_fst, ← S.iota_fst]; rfl
    · rw [← S.evalSO_sphereSection, ← S.evalSO_iota, Prod.snd_mul, map_mul]
  · rintro ⟨hgR, hgV⟩
    choose yw hyw hw hhw ew using hgR
    choose yv hyv hv hhv ev using hgV
    have hev : ∀ᶠ v in Filter.cofinite, v ∉ T :=
      Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun v hv => not_not.mp hv)
    -- the adelic point
    let y : AdeleSpace F (Fin (k + 1)) := fun j =>
      (((fun w => (yw w).1 j), (fun w => isEmptyElim w)),
        ⟨fun v => (yv v).1 j, hev.mono fun v hv =>
          (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (by
            have h : yv v ∈ intSph Q₀ ρ v := by rw [← hAVT v hv]; exact hyv v
            exact h j)⟩)
    have hyR : ∀ w, adR y w = (yw w).1 := fun w => rfl
    have hyV : ∀ v, adV y v = (yv v).1 := fun v => rfl
    have hyT : y ∈ adelicSphere Q₀ ρ := ⟨fun w => by rw [hyR]; exact (mem_sphR_iff Q₀ ρ w _).mp (yw w).2,
      fun w => isEmptyElim w, fun v => by rw [hyV]; exact (mem_sphV_iff Q₀ ρ v _).mp (yv v).2⟩
    let y' : adelicSphere Q₀ ρ := ⟨y, hyT⟩
    have hyA : y' ∈ boxG Q₀ ρ AR AV := ⟨fun w => by
      have : (⟨adR y'.1 w, (mem_sphR_iff Q₀ ρ w _).mpr (y'.2.1 w)⟩ : Sph (QRe Q₀ w) (σR w ρ)) = yw w :=
        Subtype.ext rfl
      rw [this]; exact hyw w, fun v => by
      have : (⟨adV y'.1 v, (mem_sphV_iff Q₀ ρ v _).mpr (y'.2.2.2 v)⟩ : sphV Q₀ ρ v) = yv v := Subtype.ext rfl
      rw [this]; exact hyv v⟩
    -- the adelic stabilizer element
    let hf : OAf (S.C.Q'.map (algebraMap (𝓞 F) F)) :=
      ⟨fun v => ((hv v : SOv v S.C.Q') : orthGroup (S.C.Q'.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)),
        Filter.Eventually.of_forall fun v => Subgroup.mem_subgroupOf.mp (hhv v)⟩
    have hfso : hf ∈ soAf (S.C.Q'.map (algebraMap (𝓞 F) F)) := fun v => (hv v).2
    let h : SOAdele S.C.Q' := ((hw, fun w => isEmptyElim w), ⟨hf, hfso⟩)
    have hB : h ∈ S.boxB BR := ⟨hhw, (mem_KSO_iff S.C.Q' _).mpr fun v => hhv v⟩
    refine ⟨y', hyA, h, hB, ?_⟩
    refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => isEmptyElim w)) ?_
    · rw [ew w]
      show _ = (S.secInf hρ y').1 w * S.iotaR w (hw w)
      rw [S.secInf_fst]
      congr 2
    · apply Subtype.ext; apply RestrictedProduct.ext; intro v
      have e := congrArg (fun x : SOv v Q₀ => (x : orthGroup QF (v.adicCompletion F))) (ev v)
      simp only [coe_evalSO] at e
      rw [e]
      show _ = (((S.sphereSection hρ y').2 : OAf QF) v) * ((S.iota h).2 : OAf QF) v
      have e1 : ((S.sphereSection hρ y').2 : OAf QF) v =
          ((S.secSO hρ v ⟨adV y'.1 v, (mem_sphV_iff Q₀ ρ v _).mpr (y'.2.2.2 v)⟩ : SOv v Q₀) :
            orthGroup QF (v.adicCompletion F)) := rfl
      have e2 : ((S.iota h).2 : OAf QF) v = ((S.iotaSO v (hv v) : SOv v Q₀) : orthGroup QF (v.adicCompletion F)) :=
        rfl
      rw [e1, e2]
      have : (⟨adV y'.1 v, (mem_sphV_iff Q₀ ρ v _).mpr (y'.2.2.2 v)⟩ : sphV Q₀ ρ v) = yv v := Subtype.ext rfl
      rw [this]; rfl

open Classical in
/-- **The finite box for the generalized product sets**: away from $S_b\supseteq$ bad places $\cup\,T$ the image is
$SO(L_v)$. -/
theorem finBoxG_eq (T : Finset (HeightOneSpectrum (𝓞 F))) (AV : ∀ v : HeightOneSpectrum (𝓞 F), Set (sphV Q₀ ρ v))
    (hAVT : ∀ v ∉ T, AV v = intSph Q₀ ρ v) :
    {g : SOAf Q₀ | ∀ v, evalSO Q₀ v g ∈ S.EVG hρ AV v} = boxSO Q₀ (S.badFin hρ ∪ T) (S.EVG hρ AV) := by
  have hoff : ∀ v ∉ S.badFin hρ ∪ T, S.EVG hρ AV v = (soStabSO v Q₀ : Set (SOv v Q₀)) := fun v hv => by
    rw [Finset.mem_union, not_or] at hv
    rw [EVG, hAVT v hv.2, S.secMulImage_good hρ v (S.goodFin_of_not_mem hρ hv.1)]
  ext g
  simp only [mem_setOf_eq, boxSO]
  constructor
  · intro h
    refine ⟨fun v _ => h v, fun v hv => ?_⟩
    have := h v
    rwa [hoff v hv] at this
  · rintro ⟨h1, h2⟩ v
    by_cases hv : v ∈ S.badFin hρ ∪ T
    · exact h1 v hv
    · rw [hoff v hv]; exact h2 v hv

include S hρ hk in
open Classical in
/-- **The local volumes $\sigma_v(T_v\cap L_v)$ form a convergent product with nonzero value** off a finite set $S_0$
(the bad places): there $\sigma_v(T_v\cap L_v)\ne0$, and $\prod'_{v\notin S_0}\sigma_v(T_v\cap L_v)\ne0$ (from
$\mu_v(SO(L_v)) = \sigma_v(T_v\cap L_v)\,\mu_v(SO(L'_v))$ at good places, `hasProd_of_ratio`). -/
theorem exists_hasProd_sigV_intSph (hfin : ∀ v, sigV Q₀ ρ hQ v (intSph Q₀ ρ v) ≠ ⊤) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∉ S₀, (sigV Q₀ ρ hQ v (intSph Q₀ ρ v)).toReal ≠ 0) ∧
      Multipliable (fun v => if v ∈ S₀ then 1 else (sigV Q₀ ρ hQ v (intSph Q₀ ρ v)).toReal) ∧
      (∏' v, if v ∈ S₀ then 1 else (sigV Q₀ ρ hQ v (intSph Q₀ ρ v)).toReal) ≠ 0 := by
  have hk1 : 1 ≤ k := by omega
  refine ⟨S.badFin hρ, ?_⟩
  set Sb := S.badFin hρ
  set a : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (sigV Q₀ ρ hQ v (intSph Q₀ ρ v)).toReal with ha
  set β : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    (muLocSO v S.C.Q' 1 (soStabSO v S.C.Q' : Set (SOv v S.C.Q'))).toReal with hβ
  set α : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    (muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀))).toReal with hα
  have hβK : ∀ v, muLocSO v S.C.Q' 1 (soStabSO v S.C.Q' : Set (SOv v S.C.Q')) = ENNReal.ofReal (β v) := fun v => by
    rw [hβ, ENNReal.ofReal_toReal]; rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top
  have hαK : ∀ v, muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀)) = ENNReal.ofReal (α v) := fun v => by
    rw [hα, ENNReal.ofReal_toReal]; rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top
  have haK : ∀ v, sigV Q₀ ρ hQ v (intSph Q₀ ρ v) = ENNReal.ofReal (a v) := fun v => by
    rw [ha, ENNReal.ofReal_toReal (hfin v)]
  have hβpos : ∀ v, 0 < β v := fun v => ENNReal.toReal_pos (muLocSO_soStabSO_pos S.C.Q' S.C.hQ' v one_pos)
    (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)
  have hαpos : ∀ v, 0 < α v := fun v => ENNReal.toReal_pos (muLocSO_soStabSO_pos Q₀ hQ v one_pos)
    (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)
  have ha0 : ∀ v, 0 ≤ a v := fun v => ENNReal.toReal_nonneg
  have hgood : ∀ v ∉ Sb, α v = a v * β v := fun v hv => by
    have := S.muLocSO_soStab_good hρ hQ v hk1 (S.goodFin_of_not_mem hρ hv)
    rw [hαK, haK, hβK, ← ENNReal.ofReal_mul (ha0 v)] at this
    exact (ENNReal.ofReal_eq_ofReal_iff (hαpos v).le (mul_nonneg (ha0 v) (hβpos v).le)).mp this
  have hmult := multipliable_muLocSO_one Q₀ hQ (by omega : k + 1 ≠ 0) (by omega : k + 1 ≠ 2)
  have hmultβ := multipliable_muLocSO_one S.C.Q' S.C.hQ' (by omega : k ≠ 0) (by omega : k ≠ 2)
  have hBpos : 0 < ∏' v, β v := by
    have := tprod_siegelDensity_pos (by omega : 3 ≤ k) S.C.Q' S.C.hQ'
    rw [← finFactor_one S.C.Q' S.C.hQ'] at this
    exact this
  have hApos : 0 < ∏' v, α v := by
    have := tprod_siegelDensity_pos (by omega : 3 ≤ k + 1) Q₀ hQ
    rw [← finFactor_one Q₀ hQ] at this
    exact this
  have hr := hasProd_of_ratio (a := fun v => if v ∈ Sb then 1 else a v) Sb hmult.hasProd hmultβ.hasProd
    hBpos.ne' hβpos hαpos (fun v hv => by simp only [hv, if_false]; exact hgood v hv)
  refine ⟨fun v hv h0 => ?_, hr.multipliable, ?_⟩
  · have := hgood v hv
    have h0' : a v = 0 := h0
    rw [h0', zero_mul] at this
    exact (hαpos v).ne' this
  · rw [hr.tprod_eq]
    refine mul_ne_zero (div_pos hApos hBpos).ne' (Finset.prod_ne_zero_iff.mpr fun v hv => ?_)
    simp only [hv, if_true, one_mul]
    exact (div_pos (hβpos v) (hαpos v)).ne'

set_option maxHeartbeats 1000000 in
open Classical in
/-- **The box formula with finitely many free finite places** (totally real $F$, $N = k+1\ge4$). -/
theorem sphereMeasure_boxG [IsEmpty {w : InfinitePlace F // w.IsComplex}] (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (Sph (QRe Q₀ w) (σR w ρ)))
    (hAR : ∀ w, MeasurableSet (AR w)) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (AV : ∀ v : HeightOneSpectrum (𝓞 F), Set (sphV Q₀ ρ v)) (hAV : ∀ v, MeasurableSet (AV v))
    (hAVT : ∀ v ∉ T, AV v = intSph Q₀ ρ v) (hfinV : ∀ v, sigV Q₀ ρ hQ v (AV v) ≠ ⊤)
    (hfin : ∀ v, sigV Q₀ ρ hQ v (intSph Q₀ ρ v) ≠ ⊤) :
    S.sphereMeasure hρ hQ hk (boxG Q₀ ρ AR AV) =
      ENNReal.ofReal (cF F (k + 1) / cF F k * ∏' v, (sigV Q₀ ρ hQ v (AV v)).toReal) *
        ∏ w, sig (QRe Q₀ w) (σR w ρ) (AR w) := by
  have hk1 : 1 ≤ k := by omega
  have hBex : ∀ w : {w : InfinitePlace F // w.IsReal}, ∃ U : Set (ArchSO (QRe S.C.Q' w)), MeasurableSet U ∧
      (∀ g, g⁻¹ ∈ U ↔ g ∈ U) ∧ lerayMeasure (QRe S.C.Q' w) (gramDetR_QRe_ne_zero S.C.Q' S.C.hQ' w) U ≠ 0 ∧
      lerayMeasure (QRe S.C.Q' w) (gramDetR_QRe_ne_zero S.C.Q' S.C.hQ' w) U ≠ ∞ := fun w => by
    have := isHaarMeasure_lerayMeasure (gramDetR_QRe_ne_zero S.C.Q' S.C.hQ' w)
    exact exists_symm_nbhd _
  choose BR hBRm hBRs hBR0 hBRt using hBex
  have hB := S.measurableSet_boxB BR hBRm
  have hBsym : ∀ h, h⁻¹ ∈ S.boxB BR ↔ h ∈ S.boxB BR := fun h => by
    simp only [boxB, mem_setOf_eq, Prod.fst_inv, Pi.inv_apply, Prod.snd_inv, inv_mem_iff, hBRs]
  have hA := measurableSet_boxG AR hAR AV hAV
  have key := S.sphereMeasure_mul_secMulImage hρ hQ hk hA hB hBsym
  rw [S.secMulImage_boxG hρ AR BR T AV hAVT] at key
  rw [show {g : SOAdele Q₀ | (∀ w, g.1.1 w ∈ S.ER hρ AR BR w) ∧ ∀ v, evalSO Q₀ v g.2 ∈ S.EVG hρ AV v} =
      {g | (∀ w, g.1.1 w ∈ S.ER hρ AR BR w) ∧ g.2 ∈ {gf : SOAf Q₀ | ∀ v, evalSO Q₀ v gf ∈ S.EVG hρ AV v}} from rfl,
    muTam_prodSet, S.finBoxG_eq hρ T AV hAVT] at key
  rw [show S.boxB BR = {h : SOAdele S.C.Q' | (∀ w, h.1.1 w ∈ BR w) ∧ h.2 ∈ (KSO S.C.Q' : Set (SOAf S.C.Q'))}
      from rfl, muTam_prodSet, muFin_KSO] at key
  -- the finite box
  have hEV : ∀ v ∈ S.badFin hρ ∪ T, MeasurableSet (S.EVG hρ AV v) := fun v _ =>
    (S.measurableSet_secMulImage hρ hQ v (hAV v) (isOpen_soStabSO v S.C.Q').measurableSet).1
  have hmult := multipliable_muLocSO_one Q₀ hQ (by omega : k + 1 ≠ 0) (by omega : k + 1 ≠ 2)
  rw [muFin_boxSO_split Q₀ hQ (fun _ => one_pos) hmult _ _ hEV] at key
  -- real numbers
  set a : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (sigV Q₀ ρ hQ v (AV v)).toReal with ha
  set ai : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (sigV Q₀ ρ hQ v (intSph Q₀ ρ v)).toReal with hai
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
  have haK : ∀ v, sigV Q₀ ρ hQ v (AV v) = ENNReal.ofReal (a v) := fun v => by
    rw [ha, ENNReal.ofReal_toReal (hfinV v)]
  have haiK : ∀ v, sigV Q₀ ρ hQ v (intSph Q₀ ρ v) = ENNReal.ofReal (ai v) := fun v => by
    rw [hai, ENNReal.ofReal_toReal (hfin v)]
  have hcK : ∀ v, S.cFin v = ENNReal.ofReal (c v) := fun v => by
    rw [hc, ENNReal.ofReal_toReal]; rw [S.cFin_eq hρ v]; exact ENNReal.ofReal_ne_top
  have hrK : ∀ w, S.cReal w = ENNReal.ofReal (r w) := fun w => by
    rw [hr, ENNReal.ofReal_toReal (S.cReal_ne_top hρ w)]
  have hβpos : ∀ v, 0 < β v := fun v => ENNReal.toReal_pos (muLocSO_soStabSO_pos S.C.Q' S.C.hQ' v one_pos)
    (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)
  have hαpos : ∀ v, 0 < α v := fun v => ENNReal.toReal_pos (muLocSO_soStabSO_pos Q₀ hQ v one_pos)
    (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)
  have ha0 : ∀ v, 0 ≤ a v := fun v => ENNReal.toReal_nonneg
  have hai0 : ∀ v, 0 ≤ ai v := fun v => ENNReal.toReal_nonneg
  have hc0 : ∀ v, 0 ≤ c v := fun v => ENNReal.toReal_nonneg
  have hr0 : ∀ w, 0 ≤ r w := fun w => ENNReal.toReal_nonneg
  -- the local identities
  have hERw : ∀ w, lerayMeasure (QRe Q₀ w) (gramDetR_QRe_ne_zero Q₀ hQ w) (S.ER hρ AR BR w) =
      ENNReal.ofReal (r w) * sig (QRe Q₀ w) (σR w ρ) (AR w) *
        lerayMeasure (QRe S.C.Q' w) (gramDetR_QRe_ne_zero S.C.Q' S.C.hQ' w) (BR w) := fun w => by
    rw [ER, S.localFib_real' hρ hQ w (hAR w) (hBRm w), hrK]
  have hEVv : ∀ v, muLocSO v Q₀ 1 (S.EVG hρ AV v) = ENNReal.ofReal (c v * a v * β v) := fun v => by
    rw [EVG, S.localFib_fin' hρ hQ v hk1 (hAV v) (isOpen_soStabSO v S.C.Q').measurableSet,
      hcK, haK, hβK, ← ENNReal.ofReal_mul (hc0 v), ← ENNReal.ofReal_mul (mul_nonneg (hc0 v) (ha0 v))]
  have hgood : ∀ v ∉ S.badFin hρ, α v = ai v * β v := fun v hv => by
    have := S.muLocSO_soStab_good hρ hQ v hk1 (S.goodFin_of_not_mem hρ hv)
    rw [hαK, haiK, hβK, ← ENNReal.ofReal_mul (hai0 v)] at this
    exact (ENNReal.ofReal_eq_ofReal_iff (hαpos v).le (mul_nonneg (hai0 v) (hβpos v).le)).mp this
  set Sb := S.badFin hρ ∪ T with hSb
  have hgoodb : ∀ v ∉ Sb, α v = a v * β v := fun v hv => by
    rw [hSb, Finset.mem_union, not_or] at hv
    have h1 := hgood v hv.1
    have h2 : a v = ai v := by simp only [ha, hai, hAVT v hv.2]
    rw [h2]; exact h1
  have hcgood : ∀ v ∉ Sb, c v = 1 := fun v hv => by
    rw [hSb, Finset.mem_union, not_or] at hv
    show (S.cFin v).toReal = 1
    rw [S.cFin_good v (S.goodFin_of_not_mem hρ hv.1), ENNReal.toReal_one]
  simp only [hERw, hEVv] at key
  -- the real identity
  have hmultβ := multipliable_muLocSO_one S.C.Q' S.C.hQ' (by omega : k ≠ 0) (by omega : k ≠ 2)
  have hBpos : 0 < ∏' v, β v := by
    have := tprod_siegelDensity_pos (by omega : 3 ≤ k) S.C.Q' S.C.hQ'
    rw [← finFactor_one S.C.Q' S.C.hQ'] at this
    exact this
  have hsplitα : ∏' v, α v = (∏ v ∈ Sb, α v) * ∏' v, (if v ∈ Sb then 1 else α v) :=
    tprod_eq_prod_mul_tprod_ite α hmult Sb fun v _ => (hαpos v).ne'
  have hratio := (hasProd_of_ratio Sb hmult.hasProd hmultβ.hasProd hBpos.ne' hβpos hαpos hgoodb).tprod_eq
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

open Classical in
/-- **The image of $\sigma_{\mathbb A}$ on a box at the real places.** -/
theorem map_projR_restrict_boxG [IsEmpty {w : InfinitePlace F // w.IsComplex}] (T : Finset (HeightOneSpectrum (𝓞 F)))
    (AV : ∀ v : HeightOneSpectrum (𝓞 F), Set (sphV Q₀ ρ v)) (hAV : ∀ v, MeasurableSet (AV v))
    (hAVT : ∀ v ∉ T, AV v = intSph Q₀ ρ v) (hfinV : ∀ v, sigV Q₀ ρ hQ v (AV v) ≠ ⊤)
    (hfin : ∀ v, sigV Q₀ ρ hQ v (intSph Q₀ ρ v) ≠ ⊤) :
    ((S.sphereMeasure hρ hQ hk).restrict (boxG Q₀ ρ (fun _ => univ) AV)).map (projR Q₀ ρ) =
      ENNReal.ofReal (cF F (k + 1) / cF F k * ∏' v, (sigV Q₀ ρ hQ v (AV v)).toReal) •
        Measure.pi fun w => sig (QRe Q₀ w) (σR w ρ) := by
  set D := cF F (k + 1) / cF F k * ∏' v, (sigV Q₀ ρ hQ v (AV v)).toReal
  have hσ : ∀ w, SigmaFinite (sig (QRe Q₀ w) (σR w ρ)) := fun w => sigmaFinite_sig ((map_ne_zero _).mpr hρ)
  obtain ⟨w₀⟩ : Nonempty {w : InfinitePlace F // w.IsReal} := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact ⟨⟨w, not_isComplex_iff_isReal.mp fun h => isEmptyElim (⟨w, h⟩ : {w : InfinitePlace F // w.IsComplex})⟩⟩
  classical
  set c : {w : InfinitePlace F // w.IsReal} → NNReal := fun w => if w = w₀ then D.toNNReal else 1
  have key : ∀ μ' : Measure (∀ w : {w : InfinitePlace F // w.IsReal}, Sph (QRe Q₀ w) (σR w ρ)),
      (∀ s : ∀ w, Set (Sph (QRe Q₀ w) (σR w ρ)), (∀ w, MeasurableSet (s w)) →
        μ' (univ.pi s) = ENNReal.ofReal D * ∏ w, sig (QRe Q₀ w) (σR w ρ) (s w)) →
      Measure.pi (fun w => c w • sig (QRe Q₀ w) (σR w ρ)) = μ' := fun μ' h => by
    refine Measure.pi_eq fun s hs => ?_
    rw [h s hs]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib]
    congr 1
    rw [← ENNReal.ofNNReal_finsetProd]
    simp only [c, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    rfl
  refine (key _ fun s hs => ?_).symm.trans (key _ fun s hs => ?_)
  · rw [Measure.map_apply measurable_projR (MeasurableSet.univ_pi hs),
      Measure.restrict_apply (measurable_projR (MeasurableSet.univ_pi hs))]
    have : projR Q₀ ρ ⁻¹' univ.pi s ∩ boxG Q₀ ρ (fun _ => univ) AV = boxG Q₀ ρ s AV := by
      ext y
      simp only [mem_inter_iff, mem_preimage, mem_univ_pi, boxG, mem_setOf_eq, mem_univ, implies_true,
        true_and, projR]
    rw [this, S.sphereMeasure_boxG hρ hQ hk s hs T AV hAV hAVT hfinV hfin]
  · rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi]

open Classical in
/-- **The integral of a product function over a box**:
$\int_{\prod_vA_v}\prod_wf_w(y_w)\,d\sigma_{\mathbb A} = \frac{c_F(N)}{c_F(N-1)}\prod_v\sigma_v(A_v)\prod_w\int f_w\,d\sigma_w$. -/
theorem lintegral_boxG_prod [IsEmpty {w : InfinitePlace F // w.IsComplex}] (T : Finset (HeightOneSpectrum (𝓞 F)))
    (AV : ∀ v : HeightOneSpectrum (𝓞 F), Set (sphV Q₀ ρ v)) (hAV : ∀ v, MeasurableSet (AV v))
    (hAVT : ∀ v ∉ T, AV v = intSph Q₀ ρ v) (hfinV : ∀ v, sigV Q₀ ρ hQ v (AV v) ≠ ⊤)
    (hfin : ∀ v, sigV Q₀ ρ hQ v (intSph Q₀ ρ v) ≠ ⊤)
    (f : ∀ w : {w : InfinitePlace F // w.IsReal}, Sph (QRe Q₀ w) (σR w ρ) → ℝ≥0∞) (hf : ∀ w, Measurable (f w)) :
    ∫⁻ y, (boxG Q₀ ρ (fun _ => univ) AV).indicator (fun y => ∏ w, f w (projR Q₀ ρ y w)) y
        ∂S.sphereMeasure hρ hQ hk =
      ENNReal.ofReal (cF F (k + 1) / cF F k * ∏' v, (sigV Q₀ ρ hQ v (AV v)).toReal) *
        ∏ w, ∫⁻ x, f w x ∂sig (QRe Q₀ w) (σR w ρ) := by
  have hσ : ∀ w, SigmaFinite (sig (QRe Q₀ w) (σR w ρ)) := fun w => sigmaFinite_sig ((map_ne_zero _).mpr hρ)
  have hW := measurableSet_boxG (Q₀ := Q₀) (ρ := ρ) (fun _ => univ) (fun _ => MeasurableSet.univ) AV hAV
  have hf' : Measurable fun x : (∀ w : {w : InfinitePlace F // w.IsReal}, Sph (QRe Q₀ w) (σR w ρ)) =>
      ∏ w, f w (x w) := Finset.measurable_prod _ fun w _ => (hf w).comp (measurable_pi_apply w)
  rw [lintegral_indicator hW, ← lintegral_map hf' measurable_projR,
    S.map_projR_restrict_boxG hρ hQ hk T AV hAV hAVT hfinV hfin, lintegral_smul_measure,
    lintegral_pi_prod _ f hf, smul_eq_mul]

end AdelicSphereSetup

end QuadFormsKB.Tamagawa.Measure.Weil

end
