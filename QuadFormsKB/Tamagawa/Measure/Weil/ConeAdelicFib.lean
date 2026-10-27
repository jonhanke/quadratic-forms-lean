import QuadFormsKB.Tamagawa.Measure.Weil.ConeAdelicStab
import QuadFormsKB.Tamagawa.Measure.Weil.QuotientSigma
import QuadFormsKB.Tamagawa.Measure.Weil.ConeUnfoldAdelic
import QuadFormsKB.Tamagawa.Measure.Weil.ThetaPoissonSO
import QuadFormsKB.Tamagawa.Measure.Weil.MuTamUnimodular
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereCont

/-!
# Weil's adelic fibration over the cone, proved

**Discharges the input `AdelicConeFibration`** for constructed data, for the cone form
$Q_0 = \langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'$ with $Q_0'$ nondegenerate in $k\ge3$ variables (every number field,
every signature):

* **`coneMuP`** $\mu_P = \mathrm{decomp}_*(dw^{\mathrm{Tam}}\otimes\mu_{SO(Q_0')})$ on $P = \operatorname{Stab}(e)$; it is left and right
  invariant (`coneMuP_mul_left`, `coneMuP_mul_right`: $P$ is unimodular), $\sigma$-finite and nonzero.
* **`coneMeasure`** $\sigma_C$: the quotient measure of $\mu_{\mathrm{Tam}}$ by $\mu_P$ on the adelic cone (`quotMeasureσ`), so
  $\mu_{\mathrm{Tam}} = \mathrm{coord}_*(\sigma_C\otimes\mu_P)$ with constant $1$ (`coneFib`).
* **`coneMeasure_homog`**: homogeneity of degree $n-2$: $\int f(zx)\,d\sigma_C = \|z\|^{2-n}\int f\,d\sigma_C$; the torus element
  $d(z)$ normalizes $P$ and scales $dw^{\mathrm{Tam}}$ by $\|z\|^{k}$.
* **`coneData`**, **`coneFibration`**: `AdelicConeFibration hQ hQ' (coneData …)`.
-/

open MeasureTheory Set Matrix
open scoped ENNReal RestrictedProduct Pointwise

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayComplex
  QuadFormsKB.Tamagawa.Measure.ConeAlgebra

variable {F : Type} [Field F] [NumberField F]

section MuP

variable {c₀ : 𝓞 F} {k : ℕ} {Q₀' : QuadForm (𝓞 F) k} (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate)

local notation "QC" => ConeFinite.Qcone c₀ Q₀'

/-- **The measure $\mu_P$** $= \mathrm{decomp}_*(dw^{\mathrm{Tam}}\otimes\mu_{SO(Q_0')})$ on the stabilizer $P$ of $e$. -/
@[kb "weil1982" "§4.5, p. 108 (the measure on P' = SO(V') ⋉ V') [unverified page]"]
def coneMuP : Measure (Pc c₀ Q₀') := ((ConeAdelic.dwTam F k).prod (muTam Q₀' hQ' 1)).map (decompEquiv hc hQ')

instance sigmaFinite_coneMuP : SigmaFinite (coneMuP hc hQ') := by
  have : SigmaFinite (muAddVec F (Fin k)) := by unfold muAddVec; infer_instance
  unfold coneMuP
  rw [dwTam_eq_muAddVec]
  exact MeasurableEquiv.sigmaFinite_map (decompEquiv hc hQ')

theorem decompFun_mul (ν w : AdeleSpace F (Fin k)) (η h : SOAdele Q₀') :
    decompFun hc hQ' (ν, η) * decompFun hc hQ' (w, h) = decompFun hc hQ' (ν + η • w, η * h) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, decompFun_val]
  rw [coneN_add, map_mul, show coneN hc hQ' ν * hA η * (coneN hc hQ' w * hA h) = coneN hc hQ' ν * (hA η * coneN hc hQ' w) * hA h by
    group, hA_mul_coneN]
  group

include hQ' in
/-- $w\mapsto h\cdot w$ preserves $dw^{\mathrm{Tam}}$ for $h\in SO(Q_0')(\mathbb A)$. -/
theorem measurePreserving_smul_muAddVec (η : SOAdele Q₀') :
    MeasurePreserving (fun w : AdeleSpace F (Fin k) => η • w) (muAddVec F (Fin k)) (muAddVec F (Fin k)) := by
  have he : (fun w : AdeleSpace F (Fin k) => η • w) = (soGL Q₀' η : Matrix (Fin k) (Fin k) (Adeles F)).mulVec := by
    funext w; rw [coe_soGL, soMat_mulVec]
  have hm : Measurable fun w : AdeleSpace F (Fin k) => η • w := by
    rw [he]
    exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  refine ⟨hm, ?_⟩
  rw [he, map_mulVec_muAddVec, ideleNorm_det_soGL hQ' η, inv_one, ENNReal.ofReal_one, one_smul]

theorem measurePreserving_decomp_left (ν : AdeleSpace F (Fin k)) (η : SOAdele Q₀') :
    MeasurePreserving (fun p : AdeleSpace F (Fin k) × SOAdele Q₀' => (ν + η • p.1, η * p.2))
      ((muAddVec F (Fin k)).prod (muTam Q₀' hQ' 1)) ((muAddVec F (Fin k)).prod (muTam Q₀' hQ' 1)) := by
  have : SigmaFinite (muAddVec F (Fin k)) := by unfold muAddVec; infer_instance
  have h1 : MeasurePreserving (fun w : AdeleSpace F (Fin k) => ν + η • w) (muAddVec F (Fin k)) (muAddVec F (Fin k)) :=
    (measurePreserving_add_left (muAddVec F (Fin k)) ν).comp (measurePreserving_smul_muAddVec hQ' η)
  exact h1.prod (measurePreserving_mul_left (muTam Q₀' hQ' 1) η)

/-- **$\mu_P$ is left invariant.** -/
theorem coneMuP_mul_left (p : Pc c₀ Q₀') {E : Set (Pc c₀ Q₀')} (hE : MeasurableSet E) :
    coneMuP hc hQ' ((fun q => p * q) ⁻¹' E) = coneMuP hc hQ' E := by
  obtain ⟨⟨ν, η⟩, rfl⟩ := (decompEquiv hc hQ').surjective p
  have hE' := (measurable_const_mul (decompEquiv hc hQ' (ν, η))) hE
  rw [coneMuP, dwTam_eq_muAddVec, Measure.map_apply (decompEquiv hc hQ').measurable hE',
    Measure.map_apply (decompEquiv hc hQ').measurable hE]
  have hset : (decompEquiv hc hQ') ⁻¹' ((fun q => decompEquiv hc hQ' (ν, η) * q) ⁻¹' E) =
      (fun p : AdeleSpace F (Fin k) × SOAdele Q₀' => (ν + η • p.1, η * p.2)) ⁻¹' ((decompEquiv hc hQ') ⁻¹' E) := by
    ext ⟨w, h⟩
    simp only [mem_preimage, decompEquiv_apply, decompFun_mul]
  rw [hset]
  exact (measurePreserving_decomp_left hQ' ν η).measure_preimage
    ((decompEquiv hc hQ').measurable hE).nullMeasurableSet

instance isMulLeftInvariant_coneMuP : (coneMuP hc hQ').IsMulLeftInvariant :=
  ⟨fun p => by
    ext E hE
    rw [Measure.map_apply (measurable_const_mul p) hE]
    exact coneMuP_mul_left hc hQ' p hE⟩

theorem measurePreserving_decomp_right (hk : 0 < k) (ν : AdeleSpace F (Fin k)) (η : SOAdele Q₀') :
    MeasurePreserving (fun p : AdeleSpace F (Fin k) × SOAdele Q₀' => (p.1 + p.2 • ν, p.2 * η))
      ((muAddVec F (Fin k)).prod (muTam Q₀' hQ' 1)) ((muAddVec F (Fin k)).prod (muTam Q₀' hQ' 1)) := by
  have : SigmaFinite (muAddVec F (Fin k)) := by unfold muAddVec; infer_instance
  have := isMulRightInvariant_muTam Q₀' hQ' hk
  have h1 : MeasurePreserving (fun h : SOAdele Q₀' => h * η) (muTam Q₀' hQ' 1) (muTam Q₀' hQ' 1) :=
    measurePreserving_mul_right (muTam Q₀' hQ' 1) η
  have hgm : Measurable (Function.uncurry fun (h : SOAdele Q₀') (w : AdeleSpace F (Fin k)) => w + h • ν) :=
    measurable_snd.add ((measurable_smul_const Q₀' ν).comp measurable_fst)
  have hsk := h1.skew_product (μc := muAddVec F (Fin k)) (μd := muAddVec F (Fin k)) hgm
    (Filter.Eventually.of_forall fun h => by
      have := (measurePreserving_add_right (muAddVec F (Fin k)) (h • ν)).map_eq
      exact this)
  have hs1 := Measure.measurePreserving_swap (μ := muAddVec F (Fin k)) (ν := muTam Q₀' hQ' 1)
  have hs2 := Measure.measurePreserving_swap (μ := muTam Q₀' hQ' 1) (ν := muAddVec F (Fin k))
  exact (hs2.comp hsk).comp hs1

/-- **$\mu_P$ is right invariant** ($P$ is unimodular). -/
theorem coneMuP_mul_right (hk : 0 < k) (p : Pc c₀ Q₀') {E : Set (Pc c₀ Q₀')} (hE : MeasurableSet E) :
    coneMuP hc hQ' ((fun q => q * p) ⁻¹' E) = coneMuP hc hQ' E := by
  obtain ⟨⟨ν, η⟩, rfl⟩ := (decompEquiv hc hQ').surjective p
  have hE' := (measurable_mul_const (decompEquiv hc hQ' (ν, η))) hE
  rw [coneMuP, dwTam_eq_muAddVec, Measure.map_apply (decompEquiv hc hQ').measurable hE',
    Measure.map_apply (decompEquiv hc hQ').measurable hE]
  have hset : (decompEquiv hc hQ') ⁻¹' ((fun q => q * decompEquiv hc hQ' (ν, η)) ⁻¹' E) =
      (fun p : AdeleSpace F (Fin k) × SOAdele Q₀' => (p.1 + p.2 • ν, p.2 * η)) ⁻¹' ((decompEquiv hc hQ') ⁻¹' E) := by
    ext ⟨w, h⟩
    simp only [mem_preimage, decompEquiv_apply, decompFun_mul]
  rw [hset]
  exact (measurePreserving_decomp_right hQ' hk ν η).measure_preimage
    ((decompEquiv hc hQ').measurable hE).nullMeasurableSet

theorem coneMuP_ne_zero (hk : 3 ≤ k) : coneMuP hc hQ' ≠ 0 := by
  intro h
  have h1 : coneMuP hc hQ' univ = 0 := by rw [h]; rfl
  rw [coneMuP, Measure.map_apply (decompEquiv hc hQ').measurable MeasurableSet.univ, preimage_univ,
    ← univ_prod_univ, Measure.prod_prod, dwTam_eq_muAddVec] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact (Measure.measure_univ_ne_zero.mpr (NeZero.ne (muAddVec F (Fin k)))) h2
  · exact (muTam_ne_zero Q₀' hQ' hk) (Measure.measure_univ_eq_zero.mp h2)

end MuP


/-! ### The cone measure $\sigma_C$ and the fibration identity -/

section ConeMeasure

variable {c₀ : 𝓞 F} {k : ℕ} {Q₀' : QuadForm (𝓞 F) k} (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) (hk : 3 ≤ k)

local notation "QC" => ConeFinite.Qcone c₀ Q₀'

include hc hQ' in
theorem nondeg_QC : (ConeFinite.Qcone c₀ Q₀').Nondegenerate := ConeFinite.nondeg_cone c₀ Q₀' hc hQ'

include hc hQ' hk in
/-- The section data of the cone form ($k\ge3$). -/
abbrev Dc : ConeSecData (ConeFinite.Qcone c₀ Q₀') := coneSecData hc hQ' (by omega : 1 ≤ k)

/-- **The orbit coordinates** $C(\mathbb A)\times P\simeq SO(V)(\mathbb A)$, $(x, p)\mapsto p\,s(x)^{-1}$. -/
def coneCoord : adelicCone QC × Pc c₀ Q₀' ≃ᵐ SOAdele QC := (Dc hc hQ' hk).coordEquiv

theorem coneCoord_apply (p : adelicCone QC × Pc c₀ Q₀') :
    coneCoord hc hQ' hk p = (p.2 : SOAdele QC) * ((Dc hc hQ' hk).secA p.1)⁻¹ := rfl

/-- An auxiliary set $U\subseteq P$ with $0 < \mu_P(U) < \infty$. -/
def refSetP : Set (Pc c₀ Q₀') :=
  (OrbitSection.exists_pos_lt_top (coneMuP hc hQ') (coneMuP_ne_zero hc hQ' hk)).choose

theorem refSetP_spec : MeasurableSet (refSetP hc hQ' hk) ∧ coneMuP hc hQ' (refSetP hc hQ' hk) ≠ 0 ∧
    coneMuP hc hQ' (refSetP hc hQ' hk) ≠ ∞ :=
  (OrbitSection.exists_pos_lt_top (coneMuP hc hQ') (coneMuP_ne_zero hc hQ' hk)).choose_spec

/-- Covering sets of the cone: $A_i = \{x : s(x)^{-1}\in C_i\}$. -/
def coverA (i : ℕ) : Set (adelicCone QC) :=
  (fun x => ((Dc hc hQ' hk).secA x)⁻¹) ⁻¹' compactCovering (SOAdele QC) i

/-- Covering sets of $P$: $K_j = P\cap C_j$. -/
def coverK (j : ℕ) : Set (Pc c₀ Q₀') := (Subtype.val) ⁻¹' compactCovering (SOAdele QC) j

theorem measurableSet_coverA (i : ℕ) : MeasurableSet (coverA hc hQ' hk i) :=
  (Dc hc hQ' hk).measurable_secA.inv (isCompact_compactCovering (SOAdele QC) i).isClosed.measurableSet

theorem measurableSet_coverK (j : ℕ) : MeasurableSet (coverK (c₀ := c₀) (Q₀' := Q₀') j) :=
  measurable_subtype_coe (isCompact_compactCovering (SOAdele QC) j).isClosed.measurableSet

theorem iUnion_coverA : ⋃ i, coverA hc hQ' hk i = univ := by
  simp only [coverA, ← preimage_iUnion, iUnion_compactCovering, preimage_univ]

theorem iUnion_coverK : ⋃ j, coverK (c₀ := c₀) (Q₀' := Q₀') j = univ := by
  simp only [coverK, ← preimage_iUnion, iUnion_compactCovering, preimage_univ]

theorem cover_fin (i j : ℕ) :
    muTam QC (nondeg_QC hc hQ') 1 ((coneCoord hc hQ' hk).symm ⁻¹' (coverA hc hQ' hk i ×ˢ coverK j)) ≠ ∞ := by
  have := isFiniteMeasureOnCompacts_muTam' QC (nondeg_QC hc hQ') (fun _ => 1)
  have hcpt : IsCompact (compactCovering (SOAdele QC) j * compactCovering (SOAdele QC) i) :=
    (isCompact_compactCovering _ j).mul (isCompact_compactCovering _ i)
  refine ne_top_of_le_ne_top hcpt.measure_lt_top.ne (measure_mono ?_)
  intro g hg
  simp only [mem_preimage, mem_prod] at hg
  have e : g = coneCoord hc hQ' hk ((coneCoord hc hQ' hk).symm g) :=
    ((coneCoord hc hQ' hk).apply_symm_apply g).symm
  rw [e, coneCoord_apply]
  exact Set.mul_mem_mul hg.2 hg.1

theorem coneCoord_mul (x : adelicCone QC) (p p' : Pc c₀ Q₀') :
    coneCoord hc hQ' hk (x, p' * p) = (p' : SOAdele QC) * coneCoord hc hQ' hk (x, p) :=
  (Dc hc hQ' hk).coordFun_mul x p p'

theorem muTam_preimage_mul (h' : Pc c₀ Q₀') (E : Set (SOAdele QC)) (_hE : MeasurableSet E) :
    muTam QC (nondeg_QC hc hQ') 1 ((fun g => (Pc c₀ Q₀').subtype h' * g) ⁻¹' E) =
      muTam QC (nondeg_QC hc hQ') 1 E :=
  measure_preimage_mul _ _ _

/-- **The cone measure** $\sigma_C$ on the adelic punctured cone: the quotient of Weil's Tamagawa measure of
$SO(V)(\mathbb A)$ by $\mu_P$ (Weil's $dx/dQ$ on $C^\circ(\mathbb A)$, Tamagawa-normalized). -/
@[kb "weil1982" "Lemma 2.4.1, Thm 2.4.3 [unverified page]; §4.5, p. 108 (the measure on C°_A)"]
def coneMeasure : Measure (adelicCone QC) :=
  quotMeasureσ (coneCoord hc hQ' hk) (muTam QC (nondeg_QC hc hQ') 1) (refSetP hc hQ' hk) (coneMuP hc hQ')

theorem coneMeasure_mul {E : Set (adelicCone QC)} (hE : MeasurableSet E) {B : Set (Pc c₀ Q₀')}
    (hB : MeasurableSet B) :
    muTam QC (nondeg_QC hc hQ') 1 ((coneCoord hc hQ' hk).symm ⁻¹' (E ×ˢ B)) =
      coneMeasure hc hQ' hk E * coneMuP hc hQ' B :=
  quotMeasureσ_mul (coneCoord hc hQ' hk) (Pc c₀ Q₀').subtype (coneCoord_mul hc hQ' hk) _
    (muTam_preimage_mul hc hQ') (coneMuP hc hQ') (refSetP_spec hc hQ' hk).1 (refSetP_spec hc hQ' hk).2.1
    (refSetP_spec hc hQ' hk).2.2 _ (measurableSet_coverA hc hQ' hk) (iUnion_coverA hc hQ' hk) _
    measurableSet_coverK iUnion_coverK (cover_fin hc hQ' hk) hB hE

instance sigmaFinite_coneMeasure : SigmaFinite (coneMeasure hc hQ' hk) :=
  sigmaFinite_quotMeasureσ (coneCoord hc hQ' hk) (Pc c₀ Q₀').subtype (coneCoord_mul hc hQ' hk) _
    (muTam_preimage_mul hc hQ') (coneMuP hc hQ') (coneMuP_ne_zero hc hQ' hk) (refSetP_spec hc hQ' hk).1
    (refSetP_spec hc hQ' hk).2.1 (refSetP_spec hc hQ' hk).2.2 _ (measurableSet_coverA hc hQ' hk)
    (iUnion_coverA hc hQ' hk) _ measurableSet_coverK iUnion_coverK (cover_fin hc hQ' hk)

/-- **Weil's fibration over the cone, constant $1$**: $\mu_{\mathrm{Tam}} = \mathrm{coord}_*(\sigma_C\otimes\mu_P)$. -/
@[kb "weil1982" "Lemma 2.4.1, Thm 2.4.3 [unverified page]; §4.5, p. 108 (fibration over the cone)"]
theorem coneFib : muTam QC (nondeg_QC hc hQ') 1 =
    ((coneMeasure hc hQ' hk).prod (coneMuP hc hQ')).map (coneCoord hc hQ' hk) :=
  map_prod_quotMeasureσ (coneCoord hc hQ' hk) (Pc c₀ Q₀').subtype (coneCoord_mul hc hQ' hk) _
    (muTam_preimage_mul hc hQ') (coneMuP hc hQ') (coneMuP_ne_zero hc hQ' hk) (refSetP_spec hc hQ' hk).1
    (refSetP_spec hc hQ' hk).2.1 (refSetP_spec hc hQ' hk).2.2 _ (measurableSet_coverA hc hQ' hk)
    (iUnion_coverA hc hQ' hk) _ measurableSet_coverK iUnion_coverK (cover_fin hc hQ' hk)

end ConeMeasure


/-! ### Homogeneity of degree $n - 2$ -/

section Homog

variable {c₀ : 𝓞 F} {k : ℕ} {Q₀' : QuadForm (𝓞 F) k} (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) (hk : 3 ≤ k)
  (z : (Adeles F)ˣ)

local notation "QC" => ConeFinite.Qcone c₀ Q₀'

theorem cone_units_smul_eq (x : adelicCone QC) :
    z • x.1 = ((Dc hc hQ' hk).secA x * dA (c₀ := c₀) (Q₀' := Q₀') z) • eA F k := by
  conv_lhs => rw [← (Dc hc hQ' hk).secA_smul x]
  rw [mul_smul, dA_smul_eA, smul_units_comm]
  rfl

include hc hQ' hk in
theorem cone_units_smul_mem (x : adelicCone QC) : z • x.1 ∈ adelicCone QC := by
  rw [cone_units_smul_eq hc hQ' hk]
  exact smul_mem_adelicCone QC _ (Dc hc hQ' hk).eAd_mem

include hc hQ' hk in
/-- Scaling by an idele on the adelic cone. -/
def smulC (x : adelicCone QC) : adelicCone QC := ⟨z • x.1, cone_units_smul_mem hc hQ' hk z x⟩

theorem measurable_smulC : Measurable (smulC hc hQ' hk z) :=
  Measurable.subtype_mk ((measurable_units_smul.comp (measurable_const.prodMk measurable_id)).comp
    measurable_subtype_coe)

/-- Conjugation of $P$ by $d(z)$: $p\mapsto d(z)^{-1}p\,d(z)$. -/
def alphaP (p : Pc c₀ Q₀') : Pc c₀ Q₀' :=
  ⟨(dA z)⁻¹ * (p : SOAdele QC) * dA z, by
    show ((dA z)⁻¹ * (p : SOAdele QC) * dA z) • eA F k = eA F k
    have hp : (p : SOAdele QC) • eA F k = eA F k := p.2
    rw [mul_smul, mul_smul, dA_smul_eA, smul_units_comm, hp, ← dA_smul_eA (c₀ := c₀) (Q₀' := Q₀'),
      inv_smul_smul]⟩

/-- The correction $q(x) = d(z)^{-1}s(x)^{-1}s(zx)\in P$. -/
def qP (x : adelicCone QC) : Pc c₀ Q₀' :=
  ⟨(dA z)⁻¹ * ((Dc hc hQ' hk).secA x)⁻¹ * (Dc hc hQ' hk).secA (smulC hc hQ' hk z x), by
    show ((dA z)⁻¹ * ((Dc hc hQ' hk).secA x)⁻¹ * (Dc hc hQ' hk).secA (smulC hc hQ' hk z x)) • eA F k = eA F k
    rw [mul_smul, mul_smul, show (Dc hc hQ' hk).secA (smulC hc hQ' hk z x) • eA F k = z • x.1 from
      (Dc hc hQ' hk).secA_smul _, smul_units_comm, ← (Dc hc hQ' hk).secA_smul x, inv_smul_smul]
    show (dA (c₀ := c₀) (Q₀' := Q₀') z)⁻¹ • z • eA F k = eA F k
    rw [← dA_smul_eA (c₀ := c₀) (Q₀' := Q₀'), inv_smul_smul]⟩

theorem coneCoord_L (x : adelicCone QC) (p : Pc c₀ Q₀') :
    (dA z)⁻¹ * coneCoord hc hQ' hk (x, p) =
      coneCoord hc hQ' hk (smulC hc hQ' hk z x, alphaP z p * qP hc hQ' hk z x) := by
  rw [coneCoord_apply, coneCoord_apply]
  simp only [alphaP, qP, Subgroup.coe_mul]
  group

theorem measurable_alphaP : Measurable (alphaP (c₀ := c₀) (Q₀' := Q₀') z) :=
  Measurable.subtype_mk ((measurable_const.mul measurable_subtype_coe).mul measurable_const)

/-- $d(z)^{-1}n(w)\mathrm{diag}(1,1,h)\,d(z) = n(z^{-1}w)\,\mathrm{diag}(1,1,h)$. -/
theorem alphaP_decomp (w : AdeleSpace F (Fin k)) (h : SOAdele Q₀') :
    alphaP z (decompFun hc hQ' (w, h)) = decompFun hc hQ' (z⁻¹ • w, h) := by
  apply Subtype.ext
  simp only [alphaP, decompFun_val]
  have h1 : coneN hc hQ' w * dA z = dA z * coneN hc hQ' (z⁻¹ • w) := by
    rw [dA_mul_coneN, smul_inv_smul]
  have h2 : hA h * dA z = dA z * hA (c₀ := c₀) h := hA_mul_dA h z
  rw [mul_assoc, mul_assoc, h2, ← mul_assoc (coneN hc hQ' w), h1]
  group

/-- **$\mu_P(d S d^{-1}) = \|z\|^k\mu_P(S)$**: conjugation by $d(z)$ scales $dw^{\mathrm{Tam}}$ by $\|z\|^k$. -/
theorem coneMuP_alphaP {S : Set (Pc c₀ Q₀')} (hS : MeasurableSet S) :
    coneMuP hc hQ' (alphaP z ⁻¹' S) = ENNReal.ofReal (ideleNorm F z ^ k) * coneMuP hc hQ' S := by
  have : SigmaFinite (muAddVec F (Fin k)) := by unfold muAddVec; infer_instance
  set M : GL (Fin k) (Adeles F) := Matrix.GeneralLinearGroup.scalar (Fin k) z⁻¹
  have hM : (M : Matrix (Fin k) (Fin k) (Adeles F)).mulVec = fun w => z⁻¹ • w := by
    funext w
    simp [M, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.smul_mulVec, Units.smul_def]
  have hdet : ideleNorm F (GeneralLinearGroup.det M) = (ideleNorm F z ^ k)⁻¹ := by
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
    rw [show ideleNorm F (z⁻¹ ^ k) = ideleNorm F z⁻¹ ^ k by
      rw [← coe_ideleNormHom, map_pow, NNReal.coe_pow, coe_ideleNormHom]]
    rw [ideleNorm_inv, inv_pow]
  have hmap : (muAddVec F (Fin k)).map (fun w => z⁻¹ • w) = ENNReal.ofReal (ideleNorm F z ^ k) • muAddVec F (Fin k) := by
    rw [← hM, map_mulVec_muAddVec, hdet, inv_inv]
  have hmw : Measurable fun w : AdeleSpace F (Fin k) => z⁻¹ • w := by
    rw [← hM]; exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hS' : MeasurableSet (alphaP z ⁻¹' S) := measurable_alphaP z hS
  rw [coneMuP, dwTam_eq_muAddVec, Measure.map_apply (decompEquiv hc hQ').measurable hS',
    Measure.map_apply (decompEquiv hc hQ').measurable hS]
  have hset : (decompEquiv hc hQ') ⁻¹' (alphaP z ⁻¹' S) =
      Prod.map (fun w : AdeleSpace F (Fin k) => z⁻¹ • w) id ⁻¹' ((decompEquiv hc hQ') ⁻¹' S) := by
    ext ⟨w, h⟩
    simp only [mem_preimage, decompEquiv_apply, Prod.map, id, alphaP_decomp]
  rw [hset, ← Measure.map_apply (hmw.prodMap measurable_id) ((decompEquiv hc hQ').measurable hS),
    ← Measure.map_prod_map _ _ hmw measurable_id, hmap, Measure.map_id, Measure.prod_smul_left,
    Measure.smul_apply, smul_eq_mul]

/-- **Scaling the cone**: $\sigma_C(z^{-1}E) = \|z\|^{-k}\sigma_C(E)$. -/
theorem coneMeasure_smulC_preimage {E : Set (adelicCone QC)} (hE : MeasurableSet E) :
    coneMeasure hc hQ' hk (smulC hc hQ' hk z ⁻¹' E) =
      (ENNReal.ofReal (ideleNorm F z ^ k))⁻¹ * coneMeasure hc hQ' hk E := by
  have hk0 : 0 < k := by omega
  obtain ⟨hUm, hU0, hUt⟩ := refSetP_spec hc hQ' hk
  set U := refSetP hc hQ' hk
  set c := ENNReal.ofReal (ideleNorm F z ^ k) with hc_def
  have hcpos : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (pow_pos (ideleNorm_pos z) k)
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hEU : MeasurableSet ((coneCoord hc hQ' hk).symm ⁻¹' (E ×ˢ U)) := (coneCoord hc hQ' hk).symm.measurable (hE.prod hUm)
  -- the set S in coordinates
  set S : Set (adelicCone QC × Pc c₀ Q₀') := (coneCoord hc hQ' hk) ⁻¹' ((fun g => (dA z)⁻¹ * g) ⁻¹' ((coneCoord hc hQ' hk).symm ⁻¹' (E ×ˢ U)))
  have hSm : MeasurableSet S := (coneCoord hc hQ' hk).measurable ((measurable_const_mul _) hEU)
  have hSmem : ∀ x p, (x, p) ∈ S ↔ smulC hc hQ' hk z x ∈ E ∧ alphaP z p * qP hc hQ' hk z x ∈ U := by
    intro x p
    show (coneCoord hc hQ' hk).symm ((dA z)⁻¹ * coneCoord hc hQ' hk (x, p)) ∈ E ×ˢ U ↔ _
    rw [coneCoord_L hc hQ' hk z x p, MeasurableEquiv.symm_apply_apply, mem_prod]
  -- (1) the left side
  have h1 : muTam QC (nondeg_QC hc hQ') 1 ((coneCoord hc hQ' hk).symm ⁻¹' (E ×ˢ U)) = coneMeasure hc hQ' hk E * coneMuP hc hQ' U :=
    coneMeasure_mul hc hQ' hk hE hUm
  -- (2) left invariance and the fibration
  have h2 : muTam QC (nondeg_QC hc hQ') 1 ((coneCoord hc hQ' hk).symm ⁻¹' (E ×ˢ U)) = ((coneMeasure hc hQ' hk).prod (coneMuP hc hQ')) S := by
    rw [← measure_preimage_mul (muTam QC (nondeg_QC hc hQ') 1) (dA (c₀ := c₀) (Q₀' := Q₀') z)⁻¹ ((coneCoord hc hQ' hk).symm ⁻¹' (E ×ˢ U))]
    conv_lhs => rw [coneFib hc hQ' hk]
    rw [Measure.map_apply (coneCoord hc hQ' hk).measurable ((measurable_const_mul _) hEU)]
  -- (3) the slices
  have h3 : ((coneMeasure hc hQ' hk).prod (coneMuP hc hQ')) S =
      c * coneMuP hc hQ' U * coneMeasure hc hQ' hk (smulC hc hQ' hk z ⁻¹' E) := by
    rw [Measure.prod_apply hSm]
    have hslice : ∀ x, coneMuP hc hQ' (Prod.mk x ⁻¹' S) =
        (smulC hc hQ' hk z ⁻¹' E).indicator (fun _ => c * coneMuP hc hQ' U) x := by
      intro x
      by_cases hx : smulC hc hQ' hk z x ∈ E
      · rw [indicator_of_mem (show x ∈ smulC hc hQ' hk z ⁻¹' E from hx)]
        have hs : Prod.mk x ⁻¹' S = alphaP z ⁻¹' ((fun q => q * qP hc hQ' hk z x) ⁻¹' U) := by
          ext p; simp only [mem_preimage, hSmem, hx, true_and]
        rw [hs, coneMuP_alphaP hc hQ' z ((measurable_mul_const _) hUm), coneMuP_mul_right hc hQ' hk0 _ hUm]
      · rw [indicator_of_notMem (show x ∉ smulC hc hQ' hk z ⁻¹' E from hx)]
        have hs : Prod.mk x ⁻¹' S = ∅ := by
          ext p; simp only [mem_preimage, hSmem, hx, false_and, mem_empty_iff_false]
        rw [hs, measure_empty]
    simp_rw [hslice]
    rw [lintegral_indicator_const ((measurable_smulC hc hQ' hk z) hE), mul_comm]
  -- combine
  have key : coneMeasure hc hQ' hk E * coneMuP hc hQ' U =
      c * coneMeasure hc hQ' hk (smulC hc hQ' hk z ⁻¹' E) * coneMuP hc hQ' U := by
    rw [← h1, h2, h3]; ring
  have key' := (ENNReal.mul_left_inj hU0 hUt).mp key
  rw [key', ← mul_assoc, ENNReal.inv_mul_cancel hcpos hctop, one_mul]

/-- **Homogeneity of degree $n - 2$ under the ideles**: $\int f(zx)\,d\sigma_C(x) = \|z\|^{2-n}\int f\,d\sigma_C$,
$n = k + 2$. -/
@[kb "weil1982" "§4.5, p. 108 (homogeneity of the cone measure, degree m − 2) [unverified page]"]
theorem coneMeasure_homog (f : AdeleSpace F (Fin (k + 1 + 1)) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f (z • x.1) ∂coneMeasure hc hQ' hk =
      ENNReal.ofReal (ideleNorm F z ^ ((2 : ℝ) - ((k + 1 + 1 : ℕ) : ℝ))) * ∫⁻ x, f x.1 ∂coneMeasure hc hQ' hk := by
  have hmap : (coneMeasure hc hQ' hk).map (smulC hc hQ' hk z) =
      (ENNReal.ofReal (ideleNorm F z ^ k))⁻¹ • coneMeasure hc hQ' hk := by
    ext E hE
    rw [Measure.map_apply (measurable_smulC hc hQ' hk z) hE, coneMeasure_smulC_preimage hc hQ' hk z hE,
      Measure.smul_apply, smul_eq_mul]
  have hexp : ideleNorm F z ^ ((2 : ℝ) - ((k + 1 + 1 : ℕ) : ℝ)) = (ideleNorm F z ^ k)⁻¹ := by
    rw [show (2 : ℝ) - ((k + 1 + 1 : ℕ) : ℝ) = -(k : ℝ) by push_cast; ring,
      Real.rpow_neg (ideleNorm_pos z).le, Real.rpow_natCast]
  have hfv : Measurable fun x : adelicCone QC => f x.1 := hf.comp measurable_subtype_coe
  calc ∫⁻ x, f (z • x.1) ∂coneMeasure hc hQ' hk = ∫⁻ x, f (smulC hc hQ' hk z x).1 ∂coneMeasure hc hQ' hk := rfl
    _ = ∫⁻ y, f y.1 ∂(coneMeasure hc hQ' hk).map (smulC hc hQ' hk z) :=
        (lintegral_map hfv (measurable_smulC hc hQ' hk z)).symm
    _ = _ := by
        rw [hmap, lintegral_smul_measure, smul_eq_mul, hexp, ENNReal.ofReal_inv_of_pos (pow_pos (ideleNorm_pos z) k)]

end Homog


/-! ### The input `AdelicConeFibration`, proved -/

section Assemble

variable {c₀ : 𝓞 F} {k : ℕ} {Q₀' : QuadForm (𝓞 F) k} (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) (hk : 3 ≤ k)

local notation "QC" => ConeFinite.Qcone c₀ Q₀'

theorem qF_eV_cone : qF (ConeFinite.Qcone c₀ Q₀') eV = 0 := by
  have h := qH_hessian (ConeFinite.Qcone c₀ Q₀') eV
  rw [qH_eV_cone] at h
  exact (mul_eq_zero.mp h.symm).resolve_left two_ne_zero

theorem eV_ne_zero' : (eV : Fin (k + 1 + 1) → F) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [eV, v3] at this

/-- The base point $e = e_0 + e_1\in C(F)\setminus0$. -/
def coneRat : RatCone (ConeFinite.Qcone c₀ Q₀') := ⟨eV, qF_eV_cone, eV_ne_zero'⟩

/-- **The adelic cone data of the cone form**: base point $e$, the adelic cone $C(\mathbb A)$ with $\sigma_C$, the orbit
coordinates, $\mu_P$, and $P = N\rtimes SO(Q_0')(\mathbb A)$. -/
@[kb "weil1982" "§4.5, p. 108 (the adelic cone and its measure) [unverified page]"]
def coneData : AdelicConeData (ConeFinite.Qcone c₀ Q₀') Q₀' where
  ξ := coneRat
  C := adelicCone QC
  σ := coneMeasure hc hQ' hk
  μP := coneMuP hc hQ'
  coord := coneCoord hc hQ' hk
  nA w := ⟨coneN hc hQ' w, coneN_smul_eA hc hQ' w⟩
  hA := (hA (c₀ := c₀) (Q₀' := Q₀')).codRestrict (Pc c₀ Q₀') fun h => hA_smul_eA h
  act h w := h • w
  decomp := decompEquiv hc hQ'

/-- **`AdelicConeFibration`, proved** for the constructed data (the cone form $\langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'$,
$Q_0'$ nondegenerate in $k\ge3$ variables, every number field, every signature): the orbit coordinates, the fibration
$\mu_{\mathrm{Tam}} = \mathrm{coord}_*(\sigma_C\otimes\mu_P)$ with constant $1$, homogeneity of degree $n-2$, the semidirect
product structure $P = N\rtimes SO(Q_0')(\mathbb A)$ with its rational points, and $\mu_P = dw^{\mathrm{Tam}}\otimes\mu_{SO(Q_0')}$. -/
@[kb "weil1982" "Lemma 2.4.1, Thm 2.4.3 [unverified page]; §4.5, p. 108 (fibration over the cone)"]
theorem coneFibration : AdelicConeFibration (nondeg_QC hc hQ') hQ' (coneData hc hQ' hk) where
  mul x p p' := coneCoord_mul hc hQ' hk x p p'
  orbit x p := (Dc hc hQ' hk).coordFun_inv_smul (x, p)
  sFinite := by show SFinite (coneMeasure hc hQ' hk); infer_instance
  fib := coneFib hc hQ' hk
  homog z f hf := coneMeasure_homog hc hQ' hk z f hf
  decomp_apply w h := rfl
  nA_add w w' := Subtype.ext (coneN_add hc hQ' w w')
  conj h w := by
    apply Subtype.ext
    show hA h * coneN hc hQ' w * (hA h)⁻¹ = coneN hc hQ' (h • w)
    rw [hA_mul_coneN, mul_inv_cancel_right]
  nA_rat ν hν := coneN_mem_gamma hc hQ' hν
  hA_rat η hη := hA_mem_gamma hη
  rat_decomp p hp := decomp_symm_rat hc hQ' p hp
  leftInv := isMulLeftInvariant_coneMuP hc hQ'
  μP_eq := rfl

end Assemble

end QuadFormsKB.Tamagawa.Measure.Weil

end
