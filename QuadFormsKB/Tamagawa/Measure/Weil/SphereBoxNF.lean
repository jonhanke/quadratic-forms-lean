import QuadFormsKB.Tamagawa.Measure.Weil.SphereEulerBox
import QuadFormsKB.Tamagawa.Measure.Weil.MuTamProdSetNF

/-!
# The sphere box formula over every number field

$F$ any number field, $N = k+1\ge4$. The box formula `sphereMeasure_boxG` is stated for totally real $F$.
With the complex places (**`sphereMeasure_boxGNF`**): for measurable $A_w\subseteq T(\rho)_w$ at the real and the complex
places and measurable $A_v\subseteq T_v$ of finite Leray measure, equal to $T_v\cap L_v$ outside a finite set,
$$\sigma_{\mathbb A}\Big(\prod_wA_w\times\prod_vA_v\Big) = \frac{c_F(N)\,2^{N(N-1)r_2/2}}{c_F(N-1)\,2^{(N-1)(N-2)r_2/2}}
  \prod_v\sigma_v(A_v)\cdot\prod_{w\ \mathrm{real}}\sigma_w(A_w)\prod_{w\ \mathrm{complex}}\sigma_w(A_w),$$
$\sigma_w$ = `sig` (real) and `sigC` (complex, built from Lebesgue measure $dx\,dy$), the factor $2^{(N-1)r_2}$ coming from
Weil's normalization of `muTam` at the complex places (`cxWeil`). Same proof as `sphereMeasure_boxG`, with the
complex local identity `localFib_complex`, the product set formula `muTam_prodSetNF` and the product formula at all
places `prod_cReal_cCx_mul_tprod_cFin`. Consequences: the image of $\sigma_{\mathbb A}$ restricted to a box at the
archimedean places (**`map_projRC_restrict_boxGNF`**) and the integral of a product function over a box
(**`lintegral_boxGNF_prod`**).
-/

open MeasureTheory Set Matrix
open scoped ENNReal RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.Measure.SphereLeray QuadFormsKB.Tamagawa.Measure.LerayComplex
  QuadFormsKB.Tamagawa.Measure.SphereLerayC

variable {F : Type} [Field F] [NumberField F] {k : ℕ} {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F}

namespace AdelicSphereSetup

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

variable (Q₀ ρ) in
/-- **The projection of the adelic sphere to the complex places**, $y\mapsto(y_w)_w$. -/
def projC (y : adelicSphere Q₀ ρ) : ∀ w : {w : InfinitePlace F // w.IsComplex}, SphC (QCx Q₀ w) (σC w ρ) :=
  fun w => ⟨adC y.1 w, eval_of_qH w (y.2.2.1 w)⟩

theorem measurable_projC : Measurable (projC Q₀ ρ) :=
  measurable_pi_iff.mpr fun w => (measurable_adC Q₀ ρ w).subtype_mk

variable (Q₀ ρ) in
/-- **The product set** $\prod_{w\ \mathrm{real}}A_w\times\prod_{w\ \mathrm{complex}}A_w\times\prod_vA_v$ in
$T(\rho)_{\mathbb A}$. -/
def boxGNF (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (Sph (QRe Q₀ w) (σR w ρ)))
    (AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (SphC (QCx Q₀ w) (σC w ρ)))
    (AV : ∀ v : HeightOneSpectrum (𝓞 F), Set (sphV Q₀ ρ v)) : Set (adelicSphere Q₀ ρ) :=
  {y | (∀ w, projR Q₀ ρ y w ∈ AR w) ∧ (∀ w, projC Q₀ ρ y w ∈ AC w) ∧
    ∀ v, (⟨adV y.1 v, (mem_sphV_iff Q₀ ρ v _).mpr (y.2.2.2 v)⟩ : sphV Q₀ ρ v) ∈ AV v}

theorem measurableSet_boxGNF (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (Sph (QRe Q₀ w) (σR w ρ)))
    (hAR : ∀ w, MeasurableSet (AR w))
    (AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (SphC (QCx Q₀ w) (σC w ρ)))
    (hAC : ∀ w, MeasurableSet (AC w)) (AV : ∀ v : HeightOneSpectrum (𝓞 F), Set (sphV Q₀ ρ v))
    (hAV : ∀ v, MeasurableSet (AV v)) : MeasurableSet (boxGNF Q₀ ρ AR AC AV) := by
  simp only [boxGNF, Set.ofPred_and, Set.ofPred_forall]
  refine (MeasurableSet.iInter fun w : {w : InfinitePlace F // w.IsReal} => ?_).inter
    ((MeasurableSet.iInter fun w : {w : InfinitePlace F // w.IsComplex} => ?_).inter
      (MeasurableSet.iInter fun v : HeightOneSpectrum (𝓞 F) => ?_))
  · exact ((measurable_pi_apply w).comp measurable_projR) (hAR w)
  · exact ((measurable_pi_apply w).comp measurable_projC) (hAC w)
  · exact (Measurable.subtype_mk (measurable_adV Q₀ ρ v)) (hAV v)

variable (S : AdelicSphereSetup Q₀ ρ) (hρ : ρ ≠ 0) (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k)

/-- **The product set** $\prod_wB_w\times SO(\hat L')$ in $SO(Q')(\mathbb A)$, real and complex places. -/
def boxBNF (BR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ArchSO (QRe S.C.Q' w)))
    (BC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ArchSOC (QCx S.C.Q' w))) : Set (SOAdele S.C.Q') :=
  {h | (∀ w, h.1.1 w ∈ BR w) ∧ (∀ w, h.1.2 w ∈ BC w) ∧ h.2 ∈ KSO S.C.Q'}

theorem measurableSet_boxBNF (BR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ArchSO (QRe S.C.Q' w)))
    (hBR : ∀ w, MeasurableSet (BR w)) (BC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ArchSOC (QCx S.C.Q' w)))
    (hBC : ∀ w, MeasurableSet (BC w)) : MeasurableSet (S.boxBNF BR BC) := by
  simp only [boxBNF, Set.ofPred_and, Set.ofPred_forall]
  refine (MeasurableSet.iInter fun w : {w : InfinitePlace F // w.IsReal} => ?_).inter
    ((MeasurableSet.iInter fun w : {w : InfinitePlace F // w.IsComplex} => ?_).inter ?_)
  · exact (measurable_pi_apply w).comp (measurable_fst.comp measurable_fst) (hBR w)
  · exact (measurable_pi_apply w).comp (measurable_snd.comp measurable_fst) (hBC w)
  · exact measurable_snd (isOpen_KSO S.C.Q').measurableSet

/-- The local images at the complex places. -/
def ERC (AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (SphC (QCx Q₀ w) (σC w ρ)))
    (BC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ArchSOC (QCx S.C.Q' w)))
    (w : {w : InfinitePlace F // w.IsComplex}) : Set (ArchSOC (QCx Q₀ w)) :=
  secMulImage (S.secSOC hρ w) (S.iotaC w) (AC w) (BC w)

set_option maxHeartbeats 1000000 in
/-- **$s(A)\,\iota(B)$ for the product sets is a product set** (every number field). -/
theorem secMulImage_boxGNF (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (Sph (QRe Q₀ w) (σR w ρ)))
    (AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (SphC (QCx Q₀ w) (σC w ρ)))
    (BR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ArchSO (QRe S.C.Q' w)))
    (BC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ArchSOC (QCx S.C.Q' w)))
    (T : Finset (HeightOneSpectrum (𝓞 F))) (AV : ∀ v : HeightOneSpectrum (𝓞 F), Set (sphV Q₀ ρ v))
    (hAVT : ∀ v ∉ T, AV v = intSph Q₀ ρ v) :
    secMulImage (S.sphereSection hρ) S.iota (boxGNF Q₀ ρ AR AC AV) (S.boxBNF BR BC) =
      {g | (∀ w, g.1.1 w ∈ S.ER hρ AR BR w) ∧ (∀ w, g.1.2 w ∈ S.ERC hρ AC BC w) ∧
        ∀ v, evalSO Q₀ v g.2 ∈ S.EVG hρ AV v} := by
  ext g
  constructor
  · rintro ⟨y, hy, h, hh, rfl⟩
    refine ⟨fun w => ⟨projR Q₀ ρ y w, hy.1 w, h.1.1 w, hh.1 w, ?_⟩,
      fun w => ⟨projC Q₀ ρ y w, hy.2.1 w, h.1.2 w, hh.2.1 w, ?_⟩,
      fun v => ⟨⟨adV y.1 v, (mem_sphV_iff Q₀ ρ v _).mpr (y.2.2.2 v)⟩, hy.2.2 v, evalSO S.C.Q' v h.2,
      (mem_KSO_iff S.C.Q' h.2).mp hh.2.2 v, ?_⟩⟩
    · rfl
    · rfl
    · rw [← S.evalSO_sphereSection, ← S.evalSO_iota, Prod.snd_mul, map_mul]
  · rintro ⟨hgR, hgC, hgV⟩
    choose yw hyw hw hhw ew using hgR
    choose yc hyc hc hhc ec using hgC
    choose yv hyv hv hhv ev using hgV
    have hev : ∀ᶠ v in Filter.cofinite, v ∉ T :=
      Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun v hv => not_not.mp hv)
    -- the adelic point
    let y : AdeleSpace F (Fin (k + 1)) := fun j =>
      (((fun w => (yw w).1 j), (fun w => (yc w).1 j)),
        ⟨fun v => (yv v).1 j, hev.mono fun v hv =>
          (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (by
            have h : yv v ∈ intSph Q₀ ρ v := by rw [← hAVT v hv]; exact hyv v
            exact h j)⟩)
    have hyR : ∀ w, adR y w = (yw w).1 := fun w => rfl
    have hyC : ∀ w, adC y w = (yc w).1 := fun w => rfl
    have hyV : ∀ v, adV y v = (yv v).1 := fun v => rfl
    have hyT : y ∈ adelicSphere Q₀ ρ := ⟨fun w => by rw [hyR]; exact (mem_sphR_iff Q₀ ρ w _).mp (yw w).2,
      fun w => by rw [hyC]; exact qH_of_mem_sphC w (yc w),
      fun v => by rw [hyV]; exact (mem_sphV_iff Q₀ ρ v _).mp (yv v).2⟩
    let y' : adelicSphere Q₀ ρ := ⟨y, hyT⟩
    have hpR : ∀ w, projR Q₀ ρ y' w = yw w := fun w => Subtype.ext rfl
    have hpC : ∀ w, projC Q₀ ρ y' w = yc w := fun w => Subtype.ext rfl
    have hyA : y' ∈ boxGNF Q₀ ρ AR AC AV := ⟨fun w => by rw [hpR]; exact hyw w,
      fun w => by rw [hpC]; exact hyc w, fun v => by
      have : (⟨adV y'.1 v, (mem_sphV_iff Q₀ ρ v _).mpr (y'.2.2.2 v)⟩ : sphV Q₀ ρ v) = yv v := Subtype.ext rfl
      rw [this]; exact hyv v⟩
    -- the adelic stabilizer element
    let hf : OAf (S.C.Q'.map (algebraMap (𝓞 F) F)) :=
      ⟨fun v => ((hv v : SOv v S.C.Q') : orthGroup (S.C.Q'.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)),
        Filter.Eventually.of_forall fun v => Subgroup.mem_subgroupOf.mp (hhv v)⟩
    have hfso : hf ∈ soAf (S.C.Q'.map (algebraMap (𝓞 F) F)) := fun v => (hv v).2
    let h : SOAdele S.C.Q' := ((hw, hc), ⟨hf, hfso⟩)
    have hB : h ∈ S.boxBNF BR BC := ⟨hhw, hhc, (mem_KSO_iff S.C.Q' _).mpr fun v => hhv v⟩
    refine ⟨y', hyA, h, hB, ?_⟩
    refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) ?_
    · rw [ew w]
      show _ = (S.secInf hρ y').1 w * S.iotaR w (hw w)
      rw [S.secInf_fst]
      congr 2
    · rw [ec w]
      show _ = (S.secInf hρ y').2 w * S.iotaC w (hc w)
      rw [S.secInf_snd_eq]
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

variable (F k) in
/-- **The constant of the sphere box formula**
$\frac{c_F(N)\,2^{N(N-1)r_2/2}}{c_F(N-1)\,2^{(N-1)(N-2)r_2/2}}$, $N = k+1$ (`cF`, `cxWeil`). -/
def boxConstNF : ℝ := cF F (k + 1) * cxWeil F (k + 1) / (cF F k * cxWeil F k)

theorem boxConstNF_pos : 0 < boxConstNF F k :=
  div_pos (mul_pos cF_pos' cxWeil_pos) (mul_pos cF_pos' cxWeil_pos)

set_option maxHeartbeats 2000000 in
open Classical in
/-- **The box formula over every number field** ($N = k+1\ge4$):
$\sigma_{\mathbb A}\big(\prod_wA_w\times\prod_vA_v\big) = $ `boxConstNF` $\cdot\prod_v\sigma_v(A_v)\cdot
\prod_{w\ \mathrm{real}}\sigma_w(A_w)\prod_{w\ \mathrm{complex}}\sigma_w(A_w)$. -/
theorem sphereMeasure_boxGNF (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (Sph (QRe Q₀ w) (σR w ρ)))
    (hAR : ∀ w, MeasurableSet (AR w))
    (AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (SphC (QCx Q₀ w) (σC w ρ)))
    (hAC : ∀ w, MeasurableSet (AC w)) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (AV : ∀ v : HeightOneSpectrum (𝓞 F), Set (sphV Q₀ ρ v)) (hAV : ∀ v, MeasurableSet (AV v))
    (hAVT : ∀ v ∉ T, AV v = intSph Q₀ ρ v) (hfinV : ∀ v, sigV Q₀ ρ hQ v (AV v) ≠ ⊤)
    (hfin : ∀ v, sigV Q₀ ρ hQ v (intSph Q₀ ρ v) ≠ ⊤) :
    S.sphereMeasure hρ hQ hk (boxGNF Q₀ ρ AR AC AV) =
      ENNReal.ofReal (boxConstNF F k * ∏' v, (sigV Q₀ ρ hQ v (AV v)).toReal) *
        ((∏ w, sig (QRe Q₀ w) (σR w ρ) (AR w)) * ∏ w, sigC (QCx Q₀ w) (σC w ρ) (AC w)) := by
  have hk1 : 1 ≤ k := by omega
  have hBex : ∀ w : {w : InfinitePlace F // w.IsReal}, ∃ U : Set (ArchSO (QRe S.C.Q' w)), MeasurableSet U ∧
      (∀ g, g⁻¹ ∈ U ↔ g ∈ U) ∧ lerayMeasure (QRe S.C.Q' w) (gramDetR_QRe_ne_zero S.C.Q' S.C.hQ' w) U ≠ 0 ∧
      lerayMeasure (QRe S.C.Q' w) (gramDetR_QRe_ne_zero S.C.Q' S.C.hQ' w) U ≠ ∞ := fun w => by
    have := isHaarMeasure_lerayMeasure (gramDetR_QRe_ne_zero S.C.Q' S.C.hQ' w)
    exact exists_symm_nbhd _
  choose BR hBRm hBRs hBR0 hBRt using hBex
  have hBexC : ∀ w : {w : InfinitePlace F // w.IsComplex}, ∃ U : Set (ArchSOC (QCx S.C.Q' w)), MeasurableSet U ∧
      (∀ g, g⁻¹ ∈ U ↔ g ∈ U) ∧ lerayMeasureC (QCx S.C.Q' w) (gramDetC_QCx_ne_zero S.C.Q' S.C.hQ' w) U ≠ 0 ∧
      lerayMeasureC (QCx S.C.Q' w) (gramDetC_QCx_ne_zero S.C.Q' S.C.hQ' w) U ≠ ∞ := fun w => by
    have := isHaarMeasure_lerayMeasureC (gramDetC_QCx_ne_zero S.C.Q' S.C.hQ' w)
    exact exists_symm_nbhd _
  choose BC hBCm hBCs hBC0 hBCt using hBexC
  have hB := S.measurableSet_boxBNF BR hBRm BC hBCm
  have hBsym : ∀ h, h⁻¹ ∈ S.boxBNF BR BC ↔ h ∈ S.boxBNF BR BC := fun h => by
    simp only [boxBNF, mem_ofPred_eq, Prod.fst_inv, Pi.inv_apply, Prod.snd_inv, inv_mem_iff, hBRs, hBCs]
  have hA := measurableSet_boxGNF AR hAR AC hAC AV hAV
  have key := S.sphereMeasure_mul_secMulImage hρ hQ hk hA hB hBsym
  rw [S.secMulImage_boxGNF hρ AR AC BR BC T AV hAVT] at key
  rw [show {g : SOAdele Q₀ | (∀ w, g.1.1 w ∈ S.ER hρ AR BR w) ∧ (∀ w, g.1.2 w ∈ S.ERC hρ AC BC w) ∧
        ∀ v, evalSO Q₀ v g.2 ∈ S.EVG hρ AV v} =
      {g | (∀ w, g.1.1 w ∈ S.ER hρ AR BR w) ∧ (∀ w, g.1.2 w ∈ S.ERC hρ AC BC w) ∧
        g.2 ∈ {gf : SOAf Q₀ | ∀ v, evalSO Q₀ v gf ∈ S.EVG hρ AV v}} from rfl,
    muTam_prodSetNF, S.finBoxG_eq hρ T AV hAVT] at key
  rw [show S.boxBNF BR BC = {h : SOAdele S.C.Q' | (∀ w, h.1.1 w ∈ BR w) ∧ (∀ w, h.1.2 w ∈ BC w) ∧
      h.2 ∈ (KSO S.C.Q' : Set (SOAf S.C.Q'))} from rfl, muTam_prodSetNF, muFin_KSO] at key
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
  set cc : {w : InfinitePlace F // w.IsComplex} → ℝ := fun w => (S.cCx w).toReal with hcc
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
  have hccK : ∀ w, S.cCx w = ENNReal.ofReal (cc w) := fun w => by
    rw [hcc, ENNReal.ofReal_toReal (S.cCx_ne_top w)]
  have hβpos : ∀ v, 0 < β v := fun v => ENNReal.toReal_pos (muLocSO_soStabSO_pos S.C.Q' S.C.hQ' v one_pos)
    (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)
  have hαpos : ∀ v, 0 < α v := fun v => ENNReal.toReal_pos (muLocSO_soStabSO_pos Q₀ hQ v one_pos)
    (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)
  have ha0 : ∀ v, 0 ≤ a v := fun v => ENNReal.toReal_nonneg
  have hai0 : ∀ v, 0 ≤ ai v := fun v => ENNReal.toReal_nonneg
  have hc0 : ∀ v, 0 ≤ c v := fun v => ENNReal.toReal_nonneg
  have hr0 : ∀ w, 0 ≤ r w := fun w => ENNReal.toReal_nonneg
  have hcc0 : ∀ w, 0 ≤ cc w := fun w => ENNReal.toReal_nonneg
  -- the local identities
  have hERw : ∀ w, lerayMeasure (QRe Q₀ w) (gramDetR_QRe_ne_zero Q₀ hQ w) (S.ER hρ AR BR w) =
      ENNReal.ofReal (r w) * sig (QRe Q₀ w) (σR w ρ) (AR w) *
        lerayMeasure (QRe S.C.Q' w) (gramDetR_QRe_ne_zero S.C.Q' S.C.hQ' w) (BR w) := fun w => by
    rw [ER, S.localFib_real' hρ hQ w (hAR w) (hBRm w), hrK]
  have hERc : ∀ w, lerayMeasureC (QCx Q₀ w) (gramDetC_QCx_ne_zero Q₀ hQ w) (S.ERC hρ AC BC w) =
      ENNReal.ofReal (cc w) * sigC (QCx Q₀ w) (σC w ρ) (AC w) *
        lerayMeasureC (QCx S.C.Q' w) (gramDetC_QCx_ne_zero S.C.Q' S.C.hQ' w) (BC w) := fun w => by
    rw [ERC, S.localFib_complex hρ hQ hk1 w (hAC w) (hBCm w), hccK]
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
  simp only [hERw, hERc, hEVv] at key
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
  have hprod := S.prod_cReal_cCx_mul_tprod_cFin hρ
  rw [show (fun v => (S.cFin v).toReal) = c from rfl, hcS] at hprod
  have hαS : 0 < ∏ v ∈ Sb, α v := Finset.prod_pos fun v _ => hαpos v
  have hcF : 0 < cF F k * cxWeil F k := mul_pos cF_pos' cxWeil_pos
  have hcF1 : 0 < cF F (k + 1) * cxWeil F (k + 1) := mul_pos cF_pos' cxWeil_pos
  have hreal : cF F (k + 1) * cxWeil F (k + 1) * ((∏ w, r w) * ∏ w, cc w) * (∏ v ∈ Sb, (c v * a v * β v)) *
      (∏' v, if v ∈ Sb then 1 else α v) =
      boxConstNF F k * (∏' v, a v) * (cF F k * cxWeil F k) * ∏' v, β v := by
    have e1 : ∏' v, (if v ∈ Sb then 1 else α v) = (∏' v, α v) / ∏ v ∈ Sb, α v := by
      rw [hsplitα]; field_simp
    rw [e1, hratio, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_div_distrib,
      Finset.prod_mul_distrib]
    have e2 : (∏ w, r w) * (∏ w, cc w) * ∏ v ∈ Sb, c v = 1 := hprod
    have hc0' : ∏ v ∈ Sb, c v ≠ 0 := by intro h; rw [h, mul_zero] at e2; exact zero_ne_one e2
    have e2' : (∏ w, r w) * ∏ w, cc w = (∏ v ∈ Sb, c v)⁻¹ := eq_inv_of_mul_eq_one_left e2
    rw [e2', boxConstNF]
    have hB0 : ∏' v, β v ≠ 0 := hBpos.ne'
    have hk0 : cF F k ≠ 0 := cF_pos'.ne'
    have hw0 : cxWeil F k ≠ 0 := cxWeil_pos.ne'
    simp only [← hβ]
    field_simp
  -- back to `ℝ≥0∞`
  set PR := ∏ w, sig (QRe Q₀ w) (σR w ρ) (AR w)
  set PC := ∏ w, sigC (QCx Q₀ w) (σC w ρ) (AC w)
  set MR := ∏ w, lerayMeasure (QRe S.C.Q' w) (gramDetR_QRe_ne_zero S.C.Q' S.C.hQ' w) (BR w)
  set MC := ∏ w, lerayMeasureC (QCx S.C.Q' w) (gramDetC_QCx_ne_zero S.C.Q' S.C.hQ' w) (BC w)
  have hM0 : MR * MC ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun w _ => hBR0 w)
    (Finset.prod_ne_zero_iff.mpr fun w _ => hBC0 w)
  have hMt : MR * MC ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.prod_ne_top fun w _ => hBRt w)
    (ENNReal.prod_ne_top fun w _ => hBCt w)
  have hr' : (∏ w, (ENNReal.ofReal (r w) * sig (QRe Q₀ w) (σR w ρ) (AR w) *
      lerayMeasure (QRe S.C.Q' w) (gramDetR_QRe_ne_zero S.C.Q' S.C.hQ' w) (BR w))) *
      ∏ w, (ENNReal.ofReal (cc w) * sigC (QCx Q₀ w) (σC w ρ) (AC w) *
        lerayMeasureC (QCx S.C.Q' w) (gramDetC_QCx_ne_zero S.C.Q' S.C.hQ' w) (BC w)) =
      ENNReal.ofReal ((∏ w, r w) * ∏ w, cc w) * (PR * PC) * (MR * MC) := by
    simp only [Finset.prod_mul_distrib]
    rw [← ENNReal.ofReal_prod_of_nonneg fun w _ => hr0 w, ← ENNReal.ofReal_prod_of_nonneg fun w _ => hcc0 w,
      ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => hr0 w)]
    ring
  have hS' : ∏ v ∈ Sb, ENNReal.ofReal (c v * a v * β v) = ENNReal.ofReal (∏ v ∈ Sb, (c v * a v * β v)) :=
    (ENNReal.ofReal_prod_of_nonneg fun v _ => mul_nonneg (mul_nonneg (hc0 v) (ha0 v)) (hβpos v).le).symm
  rw [hr', hS', show finFactor S.C.Q' (fun _ => 1) = ∏' v, β v from rfl] at key
  have hD0 : ENNReal.ofReal (cF F k * cxWeil F k) * (MR * MC) * ENNReal.ofReal (∏' v, β v) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ENNReal.ofReal_pos.mpr hcF).ne' hM0) (ENNReal.ofReal_pos.mpr hBpos).ne'
  have hDt : ENNReal.ofReal (cF F k * cxWeil F k) * (MR * MC) * ENNReal.ofReal (∏' v, β v) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hMt) ENNReal.ofReal_ne_top
  apply (ENNReal.mul_left_inj hD0 hDt).mp
  rw [key]
  have hY0 : 0 ≤ boxConstNF F k * ∏' v, a v := mul_nonneg boxConstNF_pos.le (tprod_nonneg ha0)
  have hRC0 : 0 ≤ (∏ w, r w) * ∏ w, cc w :=
    mul_nonneg (Finset.prod_nonneg fun w _ => hr0 w) (Finset.prod_nonneg fun w _ => hcc0 w)
  have hSb0 : 0 ≤ ∏ v ∈ Sb, (c v * a v * β v) :=
    Finset.prod_nonneg fun v _ => mul_nonneg (mul_nonneg (hc0 v) (ha0 v)) (hβpos v).le
  calc ENNReal.ofReal (cF F (k + 1) * cxWeil F (k + 1)) *
        (ENNReal.ofReal ((∏ w, r w) * ∏ w, cc w) * (PR * PC) * (MR * MC)) *
        (ENNReal.ofReal (∏ v ∈ Sb, (c v * a v * β v)) * ENNReal.ofReal (∏' v, if v ∈ Sb then 1 else α v))
      = ENNReal.ofReal (cF F (k + 1) * cxWeil F (k + 1) * ((∏ w, r w) * ∏ w, cc w) *
          (∏ v ∈ Sb, (c v * a v * β v)) * (∏' v, if v ∈ Sb then 1 else α v)) * (PR * PC) * (MR * MC) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hcF1.le hRC0) hSb0),
          ENNReal.ofReal_mul (mul_nonneg hcF1.le hRC0), ENNReal.ofReal_mul hcF1.le]
        ring
    _ = ENNReal.ofReal (boxConstNF F k * (∏' v, a v) * (cF F k * cxWeil F k) * ∏' v, β v) * (PR * PC) *
          (MR * MC) := by rw [hreal]
    _ = ENNReal.ofReal (boxConstNF F k * ∏' v, a v) * (PR * PC) *
          (ENNReal.ofReal (cF F k * cxWeil F k) * (MR * MC) * ENNReal.ofReal (∏' v, β v)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hY0 hcF.le), ENNReal.ofReal_mul hY0]
        ring

/-! ### The image on the archimedean places and integrals of product functions -/

variable (Q₀ ρ) in
/-- **The projection to all archimedean places**, $y\mapsto((y_w)_{w\ \mathrm{real}}, (y_w)_{w\ \mathrm{complex}})$. -/
def projRC (y : adelicSphere Q₀ ρ) :
    (∀ w : {w : InfinitePlace F // w.IsReal}, Sph (QRe Q₀ w) (σR w ρ)) ×
      (∀ w : {w : InfinitePlace F // w.IsComplex}, SphC (QCx Q₀ w) (σC w ρ)) :=
  (projR Q₀ ρ y, projC Q₀ ρ y)

theorem measurable_projRC : Measurable (projRC Q₀ ρ) := measurable_projR.prodMk measurable_projC

/-- A finite multiple of a measure with finite spanning sets in `C` has finite spanning sets in `C`. -/
def finiteSpanningSetsIn_smul {α : Type*} [MeasurableSpace α] {μ : Measure α} {C : Set (Set α)}
    (h : μ.FiniteSpanningSetsIn C) {c : ℝ≥0∞} (hc : c ≠ ⊤) : (c • μ).FiniteSpanningSetsIn C where
  set := h.set
  set_mem := h.set_mem
  finite i := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (h.finite i)
  spanning := h.spanning

open Classical in
/-- **The image of $\sigma_{\mathbb A}$ on a box at the archimedean places** (every number field). -/
theorem map_projRC_restrict_boxGNF (T : Finset (HeightOneSpectrum (𝓞 F)))
    (AV : ∀ v : HeightOneSpectrum (𝓞 F), Set (sphV Q₀ ρ v)) (hAV : ∀ v, MeasurableSet (AV v))
    (hAVT : ∀ v ∉ T, AV v = intSph Q₀ ρ v) (hfinV : ∀ v, sigV Q₀ ρ hQ v (AV v) ≠ ⊤)
    (hfin : ∀ v, sigV Q₀ ρ hQ v (intSph Q₀ ρ v) ≠ ⊤) :
    ((S.sphereMeasure hρ hQ hk).restrict (boxGNF Q₀ ρ (fun _ => univ) (fun _ => univ) AV)).map (projRC Q₀ ρ) =
      (ENNReal.ofReal (boxConstNF F k * ∏' v, (sigV Q₀ ρ hQ v (AV v)).toReal) •
        Measure.pi fun w => sig (QRe Q₀ w) (σR w ρ)).prod (Measure.pi fun w => sigC (QCx Q₀ w) (σC w ρ)) := by
  set D := boxConstNF F k * ∏' v, (sigV Q₀ ρ hQ v (AV v)).toReal
  have hσ : ∀ w, SigmaFinite (sig (QRe Q₀ w) (σR w ρ)) := fun w => sigmaFinite_sig ((map_ne_zero _).mpr hρ)
  have hσC : ∀ w, SigmaFinite (sigC (QCx Q₀ w) (σC w ρ)) := fun w =>
    sigmaFinite_sigC ((map_ne_zero _).mpr hρ) (Nat.succ_pos k)
  have h3C := finiteSpanningSetsIn_smul
    (Measure.FiniteSpanningSetsIn.pi fun w => (sig (QRe Q₀ w) (σR w ρ)).toFiniteSpanningSetsIn)
    (ENNReal.ofReal_ne_top (r := D))
  have h3D := Measure.FiniteSpanningSetsIn.pi fun w => (sigC (QCx Q₀ w) (σC w ρ)).toFiniteSpanningSetsIn
  refine (Measure.prod_eq_generateFrom generateFrom_pi generateFrom_pi isPiSystem_pi isPiSystem_pi h3C h3D ?_).symm
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  have hs' : ∀ w, MeasurableSet (s w) := fun w => hs w (mem_univ w)
  have ht' : ∀ w, MeasurableSet (t w) := fun w => ht w (mem_univ w)
  have hst : MeasurableSet (univ.pi s ×ˢ univ.pi t) := (MeasurableSet.univ_pi hs').prod (MeasurableSet.univ_pi ht')
  rw [Measure.map_apply measurable_projRC hst, Measure.restrict_apply (measurable_projRC hst)]
  have : projRC Q₀ ρ ⁻¹' (univ.pi s ×ˢ univ.pi t) ∩ boxGNF Q₀ ρ (fun _ => univ) (fun _ => univ) AV =
      boxGNF Q₀ ρ s t AV := by
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ_pi, boxGNF, mem_ofPred_eq, mem_univ, implies_true,
      true_and, projRC, and_assoc]
  rw [this, S.sphereMeasure_boxGNF hρ hQ hk s hs' t ht' T AV hAV hAVT hfinV hfin, Measure.smul_apply, smul_eq_mul,
    Measure.pi_pi, Measure.pi_pi, mul_assoc]

open Classical in
/-- **The integral of a product function over a box** (every number field):
$\int_{\prod_vA_v}\prod_wf_w(y_w)\,d\sigma_{\mathbb A} = $ `boxConstNF` $\cdot\prod_v\sigma_v(A_v)
\prod_{w\ \mathrm{real}}\int f_w\,d\sigma_w\prod_{w\ \mathrm{complex}}\int f_w\,d\sigma_w$. -/
theorem lintegral_boxGNF_prod (T : Finset (HeightOneSpectrum (𝓞 F)))
    (AV : ∀ v : HeightOneSpectrum (𝓞 F), Set (sphV Q₀ ρ v)) (hAV : ∀ v, MeasurableSet (AV v))
    (hAVT : ∀ v ∉ T, AV v = intSph Q₀ ρ v) (hfinV : ∀ v, sigV Q₀ ρ hQ v (AV v) ≠ ⊤)
    (hfin : ∀ v, sigV Q₀ ρ hQ v (intSph Q₀ ρ v) ≠ ⊤)
    (f : ∀ w : {w : InfinitePlace F // w.IsReal}, Sph (QRe Q₀ w) (σR w ρ) → ℝ≥0∞) (hf : ∀ w, Measurable (f w))
    (g : ∀ w : {w : InfinitePlace F // w.IsComplex}, SphC (QCx Q₀ w) (σC w ρ) → ℝ≥0∞) (hg : ∀ w, Measurable (g w)) :
    ∫⁻ y, (boxGNF Q₀ ρ (fun _ => univ) (fun _ => univ) AV).indicator
        (fun y => (∏ w, f w (projR Q₀ ρ y w)) * ∏ w, g w (projC Q₀ ρ y w)) y ∂S.sphereMeasure hρ hQ hk =
      ENNReal.ofReal (boxConstNF F k * ∏' v, (sigV Q₀ ρ hQ v (AV v)).toReal) *
        ((∏ w, ∫⁻ x, f w x ∂sig (QRe Q₀ w) (σR w ρ)) * ∏ w, ∫⁻ x, g w x ∂sigC (QCx Q₀ w) (σC w ρ)) := by
  have hσ : ∀ w, SigmaFinite (sig (QRe Q₀ w) (σR w ρ)) := fun w => sigmaFinite_sig ((map_ne_zero _).mpr hρ)
  have hσC : ∀ w, SigmaFinite (sigC (QCx Q₀ w) (σC w ρ)) := fun w =>
    sigmaFinite_sigC ((map_ne_zero _).mpr hρ) (Nat.succ_pos k)
  have hW := measurableSet_boxGNF (Q₀ := Q₀) (ρ := ρ) (fun _ => univ) (fun _ => MeasurableSet.univ)
    (fun _ => univ) (fun _ => MeasurableSet.univ) AV hAV
  have hf' : Measurable fun x : (∀ w : {w : InfinitePlace F // w.IsReal}, Sph (QRe Q₀ w) (σR w ρ)) =>
      ∏ w, f w (x w) := Finset.measurable_prod _ fun w _ => (hf w).comp (measurable_pi_apply w)
  have hg' : Measurable fun x : (∀ w : {w : InfinitePlace F // w.IsComplex}, SphC (QCx Q₀ w) (σC w ρ)) =>
      ∏ w, g w (x w) := Finset.measurable_prod _ fun w _ => (hg w).comp (measurable_pi_apply w)
  have hfg : Measurable fun p : (∀ w : {w : InfinitePlace F // w.IsReal}, Sph (QRe Q₀ w) (σR w ρ)) ×
      (∀ w : {w : InfinitePlace F // w.IsComplex}, SphC (QCx Q₀ w) (σC w ρ)) =>
      (∏ w, f w (p.1 w)) * ∏ w, g w (p.2 w) := (hf'.comp measurable_fst).mul (hg'.comp measurable_snd)
  rw [lintegral_indicator hW]
  refine (lintegral_map hfg measurable_projRC).symm.trans ?_
  rw [S.map_projRC_restrict_boxGNF hρ hQ hk T AV hAV hAVT hfinV hfin, ofReal_smul_eq,
    lintegral_prod_mul hf'.aemeasurable hg'.aemeasurable, lintegral_smul_measure,
    lintegral_pi_prod _ f hf, lintegral_pi_prod _ g hg, ENNReal.smul_def, smul_eq_mul, ENNReal.ofReal]
  ring

end AdelicSphereSetup

end QuadFormsKB.Tamagawa.Measure.Weil

end
