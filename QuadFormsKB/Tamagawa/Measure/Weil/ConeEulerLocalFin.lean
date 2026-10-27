import QuadFormsKB.Tamagawa.Measure.Weil.ConeEulerBase

/-!
# The cone at a finite place with the adelic section

$v$ a finite place, $Q_0 = \langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'$ ($k\ge3$), our coordinates $(z, p)\mapsto s(z)p$ with $s$ the
$v$-component of the adelic section (`ofCoordV`). With $P_v = \operatorname{Stab}(e) = N\rtimes SO(Q_0')(F_v)$ and
$\mu_{P,v}$ = `muPV`:

* **`isMulLeftInvariant_muPV`**: $\mu_{P,v}$ is left invariant;
* **`muLocSO_ofCoordV_image`**: $\mu_v(s(A)\,B) = |2c_0|_v^{-2(k+1)}\,\sigma_{C,v}(A)\,\mu_{P,v}(B)$ for our section $s$ (the identity
  with the section changed, `OrbitSection.fibMeasure_eq_of_sec`);
* **`BfinV`** $= P(\mathfrak o_v) = n(\mathfrak o_v^k)\,\mathrm{diag}(1,1,SO(L'_v))$: inversion-stable (`inv_preimage_BfinV`), of measure
  $\mu'_v(SO(L'_v))$ (`muPV_BfinV`), membership in matrix terms (`mem_BfinV_iff`);
* **`ofCoordV_image_good`**: at a good place $s(C^\circ_v\cap L_v^{\mathrm{prim}})\,P(\mathfrak o_v) = SO(L_v)$.
-/

open MeasureTheory Set Matrix
open scoped ENNReal RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayComplex
  QuadFormsKB.Tamagawa.Measure.ConeAlgebra QuadFormsKB.Tamagawa.Measure.LerayReal

variable {F : Type} [Field F] [NumberField F] {c₀ : 𝓞 F} {k : ℕ} {Q₀' : QuadForm (𝓞 F) k}
  (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) (hk : 3 ≤ k) (v : HeightOneSpectrum (𝓞 F))

local notation "QC" => ConeFinite.Qcone c₀ Q₀'
local notation "Fv" => v.adicCompletion F

theorem oneLe {k : ℕ} (hk : 3 ≤ k) : 1 ≤ k := by omega

/-! ### The parametrization of the stabilizer -/

theorem coe_pElemV (p : (Fin k → Fv) × SOv v Q₀') :
    ((ConeFinite.pElemV v c₀ Q₀' hc hQ' (oneLe hk) p : _) : SOv v QC) =
      ConeFinite.nG v c₀ Q₀' hc hQ' p.1 * ConeFinite.mG v c₀ Q₀' p.2 := rfl

theorem mat_pElemV (p : (Fin k → Fv) × SOv v Q₀') :
    ConeFinite.mat v QC (ConeFinite.pElemV v c₀ Q₀' hc hQ' (oneLe hk) p : SOv v QC) =
      nM (cAt c₀ (σV v)) (QAt Q₀' (σV v)) p.1 * mM (ConeFinite.mat v Q₀' p.2) := rfl

theorem pElemV_mul (ν w : Fin k → Fv) (η h : SOv v Q₀') :
    ConeFinite.pElemV v c₀ Q₀' hc hQ' (oneLe hk) (ν, η) * ConeFinite.pElemV v c₀ Q₀' hc hQ' (oneLe hk) (w, h) =
      ConeFinite.pElemV v c₀ Q₀' hc hQ' (oneLe hk) (ν + ConeFinite.mat v Q₀' η *ᵥ w, η * h) := by
  apply Subtype.ext
  show ConeFinite.nG v c₀ Q₀' hc hQ' ν * ConeFinite.mG v c₀ Q₀' η *
      (ConeFinite.nG v c₀ Q₀' hc hQ' w * ConeFinite.mG v c₀ Q₀' h) =
    ConeFinite.nG v c₀ Q₀' hc hQ' (ν + ConeFinite.mat v Q₀' η *ᵥ w) * ConeFinite.mG v c₀ Q₀' (η * h)
  rw [show ConeFinite.nG v c₀ Q₀' hc hQ' ν * ConeFinite.mG v c₀ Q₀' η *
      (ConeFinite.nG v c₀ Q₀' hc hQ' w * ConeFinite.mG v c₀ Q₀' h) =
      ConeFinite.nG v c₀ Q₀' hc hQ' ν * (ConeFinite.mG v c₀ Q₀' η * ConeFinite.nG v c₀ Q₀' hc hQ' w) *
        ConeFinite.mG v c₀ Q₀' h by group,
    ConeFinite.mG_mul_nG v c₀ Q₀' hc hQ', map_mul, ← ConeFinite.nG_add v c₀ Q₀' hc hQ']
  group

theorem pElemV_injective : Function.Injective (ConeFinite.pElemV v c₀ Q₀' hc hQ' (oneLe hk)) := by
  intro p q h
  apply ConeFinite.pElem_injective v c₀ Q₀' hc hQ'
  apply Subtype.ext
  have h' := congrArg (fun x : (ConeFinite.coneOrbitSectionV v c₀ Q₀' hc hQ' (oneLe hk)).stab => (x : SOv v QC)) h
  exact h'

theorem exists_pElemV (g : (ConeFinite.coneOrbitSectionV v c₀ Q₀' hc hQ' (oneLe hk)).stab) :
    ∃ p, ConeFinite.pElemV v c₀ Q₀' hc hQ' (oneLe hk) p = g := by
  have hg : (g : SOv v QC) ∈ ConeFinite.stabE v c₀ Q₀' := by
    rw [ConeFinite.mem_stabE_iff]
    have := g.2
    rw [MulAction.mem_stabilizer_iff] at this
    exact congrArg Subtype.val this
  obtain ⟨p, hp⟩ := ConeFinite.exists_pElem v c₀ Q₀' hc hQ' ⟨g, hg⟩
  exact ⟨p, Subtype.ext (show (ConeFinite.pElem v c₀ Q₀' hc hQ' p : SOv v QC) = g from congrArg Subtype.val hp)⟩

theorem measurable_pElemV : Measurable (ConeFinite.pElemV v c₀ Q₀' hc hQ' (oneLe hk)) :=
  (ConeFinite.continuous_pElemV v c₀ Q₀' hc hQ' (oneLe hk)).measurable

/-- The inclusion of `stabE` into the orbit stabilizer (the same subgroup). -/
def stabEtoStab (g : ConeFinite.stabE v c₀ Q₀') : (ConeFinite.coneOrbitSectionV v c₀ Q₀' hc hQ' (oneLe hk)).stab :=
  ⟨g, by
    rw [MulAction.mem_stabilizer_iff]
    exact Subtype.ext ((ConeFinite.mem_stabE_iff v c₀ Q₀' _).mp g.2)⟩

theorem measurableEmbedding_pElemV :
    MeasurableEmbedding (ConeFinite.pElemV v c₀ Q₀' hc hQ' (oneLe hk)) := by
  refine ⟨pElemV_injective hc hQ' hk v, measurable_pElemV hc hQ' hk v, fun S hS => ?_⟩
  have hemb := ConeFinite.measurableEmbedding_pElem v c₀ Q₀' hc hQ'
  have hmeas : Measurable fun g : (ConeFinite.coneOrbitSectionV v c₀ Q₀' hc hQ' (oneLe hk)).stab =>
      (⟨(g : SOv v QC), (ConeFinite.mem_stabE_iff v c₀ Q₀' _).mpr (by
        have := g.2; rw [MulAction.mem_stabilizer_iff] at this; exact congrArg Subtype.val this)⟩ :
        ConeFinite.stabE v c₀ Q₀') := measurable_subtype_coe.subtype_mk
  have : ConeFinite.pElemV v c₀ Q₀' hc hQ' (oneLe hk) '' S =
      (fun g : (ConeFinite.coneOrbitSectionV v c₀ Q₀' hc hQ' (oneLe hk)).stab => (⟨(g : SOv v QC), (ConeFinite.mem_stabE_iff v c₀ Q₀' _).mpr (by
        have := g.2; rw [MulAction.mem_stabilizer_iff] at this; exact congrArg Subtype.val this)⟩ :
        ConeFinite.stabE v c₀ Q₀')) ⁻¹' (ConeFinite.pElem v c₀ Q₀' hc hQ' '' S) := by
    ext g
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, e⟩
      exact ⟨p, hp, Subtype.ext (show (ConeFinite.pElem v c₀ Q₀' hc hQ' p : SOv v QC) = g from
        congrArg Subtype.val e)⟩
  rw [this]
  exact hmeas (hemb.measurableSet_image.mpr hS)

/-! ### Left invariance of $\mu_{P,v}$ -/

theorem measurePreserving_mulVec_so (η : SOv v Q₀') :
    MeasurePreserving (fun w : Fin k → Fv => ConeFinite.mat v Q₀' η *ᵥ w) (LerayThick.volV (Analysis.haarV v) k) (LerayThick.volV (Analysis.haarV v) k) := by
  have hm : Measurable fun w : Fin k → Fv => ConeFinite.mat v Q₀' η *ᵥ w :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  refine ⟨hm, ?_⟩
  ext S hS
  rw [Measure.map_apply hm hS, ← lintegral_indicator_one (hm hS), ← lintegral_indicator_one hS]
  exact ConeFinite.lintegral_mulVec_so v Q₀' η (measurable_one.indicator hS)

include hQ' in
theorem muPV_map_mul_left (p : (ConeFinite.coneOrbitSectionV v c₀ Q₀' hc hQ' (oneLe hk)).stab) :
    (ConeFinite.muPV v c₀ Q₀' hc hQ' (oneLe hk)).map (p * ·) =
      ConeFinite.muPV v c₀ Q₀' hc hQ' (oneLe hk) := by
  have := ConeFinite.isHaarMeasure_muLocSO v Q₀' hQ'
  obtain ⟨⟨ν, η⟩, rfl⟩ := exists_pElemV hc hQ' hk v p
  have hΦ : MeasurePreserving (fun q : (Fin k → Fv) × SOv v Q₀' => (ν + ConeFinite.mat v Q₀' η *ᵥ q.1, η * q.2))
      ((LerayThick.volV (Analysis.haarV v) k).prod (muLocSO v Q₀' 1)) ((LerayThick.volV (Analysis.haarV v) k).prod (muLocSO v Q₀' 1)) :=
    ((measurePreserving_add_left (LerayThick.volV (Analysis.haarV v) k) ν).comp (measurePreserving_mulVec_so v η)).prod
      (measurePreserving_mul_left (muLocSO v Q₀' 1) η)
  unfold ConeFinite.muPV
  rw [Measure.map_map (measurable_const_mul _) (measurable_pElemV hc hQ' hk v)]
  have e : (fun q => ConeFinite.pElemV v c₀ Q₀' hc hQ' (oneLe hk) (ν, η) * q) ∘
      ConeFinite.pElemV v c₀ Q₀' hc hQ' (oneLe hk) =
      ConeFinite.pElemV v c₀ Q₀' hc hQ' (oneLe hk) ∘
        (fun q : (Fin k → Fv) × SOv v Q₀' => (ν + ConeFinite.mat v Q₀' η *ᵥ q.1, η * q.2)) := by
    funext q; exact pElemV_mul hc hQ' hk v ν q.1 η q.2
  rw [e, ← Measure.map_map (measurable_pElemV hc hQ' hk v) hΦ.measurable, hΦ.map_eq]

include hQ' in
theorem isMulLeftInvariant_muPV :
    (ConeFinite.muPV v c₀ Q₀' hc hQ' (oneLe hk)).IsMulLeftInvariant :=
  ⟨fun p => muPV_map_mul_left hc hQ' hk v p⟩

/-! ### The local identity with our section -/

/-- **Our coordinates** $(z, p)\mapsto s(z)\,p$ on $C^\circ_v\times P_v$. -/
def ofCoordV (q : ConeFinite.ConeTV v QC × (ConeFinite.coneOrbitSectionV v c₀ Q₀' hc hQ' (oneLe hk)).stab) :
    SOv v QC :=
  secV hc hQ' hk v q.1 * (q.2 : SOv v QC)

/-- The fibre coordinate $g\mapsto s(ge)^{-1}g\in P_v$. -/
def fibV (g : SOv v QC) : (ConeFinite.coneOrbitSectionV v c₀ Q₀' hc hQ' (oneLe hk)).stab :=
  ⟨(secV hc hQ' hk v (g • ConeFinite.eConeV v c₀ Q₀'))⁻¹ * g, by
    rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
    exact (secV_smul hc hQ' hk v _).symm⟩

theorem ofCoordV_smul (q : ConeFinite.ConeTV v QC × (ConeFinite.coneOrbitSectionV v c₀ Q₀' hc hQ' (oneLe hk)).stab) :
    ofCoordV hc hQ' hk v q • ConeFinite.eConeV v c₀ Q₀' = q.1 := by
  have hp : (q.2 : SOv v QC) • ConeFinite.eConeV v c₀ Q₀' = ConeFinite.eConeV v c₀ Q₀' := q.2.2
  rw [ofCoordV, mul_smul, hp, secV_smul]

theorem ofCoordV_fibV (g : SOv v QC) :
    ofCoordV hc hQ' hk v (g • ConeFinite.eConeV v c₀ Q₀', fibV hc hQ' hk v g) = g := by
  simp [ofCoordV, fibV]

theorem fibV_ofCoordV (q : ConeFinite.ConeTV v QC × (ConeFinite.coneOrbitSectionV v c₀ Q₀' hc hQ' (oneLe hk)).stab) :
    fibV hc hQ' hk v (ofCoordV hc hQ' hk v q) = q.2 := by
  apply Subtype.ext
  simp only [fibV, ofCoordV_smul]
  simp [ofCoordV]

theorem ofCoordV_injective : Function.Injective (ofCoordV hc hQ' hk v) := by
  intro p q h
  have h1 : p.1 = q.1 := by rw [← ofCoordV_smul hc hQ' hk v p, ← ofCoordV_smul hc hQ' hk v q, h]
  have h2 : p.2 = q.2 := by rw [← fibV_ofCoordV hc hQ' hk v p, ← fibV_ofCoordV hc hQ' hk v q, h]
  exact Prod.ext h1 h2

/-- **The image of a product set**: $g\in s(A)B\iff ge\in A$ and $s(ge)^{-1}g\in B$. -/
theorem mem_ofCoordV_image {A : Set (ConeFinite.ConeTV v QC)}
    {B : Set (ConeFinite.coneOrbitSectionV v c₀ Q₀' hc hQ' (oneLe hk)).stab} (g : SOv v QC) :
    g ∈ ofCoordV hc hQ' hk v '' (A ×ˢ B) ↔ g • ConeFinite.eConeV v c₀ Q₀' ∈ A ∧ fibV hc hQ' hk v g ∈ B := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [ofCoordV_smul, fibV_ofCoordV]; exact hq
  · rintro ⟨h1, h2⟩
    exact ⟨_, ⟨h1, h2⟩, ofCoordV_fibV hc hQ' hk v g⟩

theorem measurable_smul_eConeV : Measurable fun g : SOv v QC => g • ConeFinite.eConeV v c₀ Q₀' :=
  ((ConeFinite.continuous_smul_coneV v QC).comp (continuous_id.prodMk continuous_const)).measurable

theorem measurable_fibV : Measurable (fibV hc hQ' hk v) :=
  Measurable.subtype_mk (((measurable_secV hc hQ' hk v).comp (measurable_smul_eConeV v)).inv.mul measurable_id)

theorem measurableSet_ofCoordV_image {A : Set (ConeFinite.ConeTV v QC)} (hA : MeasurableSet A)
    {B : Set (ConeFinite.coneOrbitSectionV v c₀ Q₀' hc hQ' (oneLe hk)).stab} (hB : MeasurableSet B) :
    MeasurableSet (ofCoordV hc hQ' hk v '' (A ×ˢ B)) := by
  have : ofCoordV hc hQ' hk v '' (A ×ˢ B) = (fun g => g • ConeFinite.eConeV v c₀ Q₀') ⁻¹' A ∩
      fibV hc hQ' hk v ⁻¹' B := by
    ext g; rw [mem_ofCoordV_image]; rfl
  rw [this]
  exact (measurable_smul_eConeV v hA).inter (measurable_fibV hc hQ' hk v hB)

include hQ' in
/-- **The local fibration identity with our section**: $\mu_v(s(A)B) = |2c_0|_v^{-2(k+1)}\sigma_{C,v}(A)\,\mu_{P,v}(B)$. -/
theorem muLocSO_ofCoordV_image {A : Set (ConeFinite.ConeTV v QC)} (hA : MeasurableSet A)
    {B : Set (ConeFinite.coneOrbitSectionV v c₀ Q₀' hc hQ' (oneLe hk)).stab} (hB : MeasurableSet B) :
    muLocSO v QC 1 (ofCoordV hc hQ' hk v '' (A ×ˢ B)) =
      ENNReal.ofReal ((absTwoM v c₀ ^ (2 * k + 2))⁻¹) *
        ConeFinite.sigConeV v QC (ConeFinite.nondeg_cone c₀ Q₀' hc hQ') A *
        ConeFinite.muPV v c₀ Q₀' hc hQ' (oneLe hk) B := by
  have := ConeFinite.sFinite_muPV v c₀ Q₀' hc hQ' (oneLe hk)
  have := isMulLeftInvariant_muPV hc hQ' hk v
  have hsec := (ConeFinite.coneOrbitSectionV v c₀ Q₀' hc hQ' (oneLe hk)).fibMeasure_eq_of_sec
    (secV hc hQ' hk v) (secV_smul hc hQ' hk v) (measurable_secV hc hQ' hk v)
    (ConeFinite.sigConeV v QC (ConeFinite.nondeg_cone c₀ Q₀' hc hQ'))
    (ConeFinite.muPV v c₀ Q₀' hc hQ' (oneLe hk))
  have hT := measurableSet_ofCoordV_image hc hQ' hk v hA hB
  have hmeas : Measurable (ofCoordV hc hQ' hk v) :=
    ((measurable_secV hc hQ' hk v).comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  have hfib : (ConeFinite.coneOrbitSectionV v c₀ Q₀' hc hQ' (oneLe hk)).fibMeasure
      (ConeFinite.sigConeV v QC (ConeFinite.nondeg_cone c₀ Q₀' hc hQ'))
      (ConeFinite.muPV v c₀ Q₀' hc hQ' (oneLe hk)) =
      ((ConeFinite.sigConeV v QC (ConeFinite.nondeg_cone c₀ Q₀' hc hQ')).prod
        (ConeFinite.muPV v c₀ Q₀' hc hQ' (oneLe hk))).map (ofCoordV hc hQ' hk v) := hsec.symm
  rw [ConeFinite.lerayMeasure_cone_orbital_finitePlace v c₀ Q₀' hc hQ' (oneLe hk), Measure.smul_apply,
    smul_eq_mul, hfib, Measure.map_apply hmeas hT, (ofCoordV_injective hc hQ' hk v).preimage_image,
    Measure.prod_prod, mul_assoc]

/-! ### The integral points $P(\mathfrak o_v)$ -/

/-- **$P(\mathfrak o_v) = n(\mathfrak o_v^k)\,\mathrm{diag}(1,1,SO(L'_v))$.** -/
def BfinV : Set (ConeFinite.coneOrbitSectionV v c₀ Q₀' hc hQ' (oneLe hk)).stab :=
  ConeFinite.pElemV v c₀ Q₀' hc hQ' (oneLe hk) '' ({w : Fin k → Fv | IntVec v w} ×ˢ
    (soStabSO v Q₀' : Set (SOv v Q₀')))

theorem measurableSet_BfinV : MeasurableSet (BfinV hc hQ' hk v) :=
  (measurableEmbedding_pElemV hc hQ' hk v).measurableSet_image.mpr
    ((measurableSet_intVec v).prod (isOpen_soStabSO v Q₀').measurableSet)

theorem mat_mem_intMat_of_soStab {h : SOv v Q₀'} (hh : h ∈ soStabSO v Q₀') :
    ConeFinite.mat v Q₀' h ∈ intMat v ∧ ConeFinite.mat v Q₀' h⁻¹ ∈ intMat v := by
  have h1 : ((h : orthGroup (Q₀'.map (algebraMap (𝓞 F) F)) Fv) : GL (Fin k) Fv) ∈ glInt v :=
    Subgroup.mem_subgroupOf.mp hh
  exact (mem_glInt_iff v).mp h1

theorem mem_soStab_of_mat {g : SOv v QC} (h1 : ConeFinite.mat v QC g ∈ intMat v)
    (h2 : ConeFinite.mat v QC g⁻¹ ∈ intMat v) : g ∈ soStabSO v QC := by
  show ((g : orthGroup ((ConeFinite.Qcone c₀ Q₀').map (algebraMap (𝓞 F) F)) Fv) : GL (Fin (k + 1 + 1)) Fv) ∈ glInt v
  rw [mem_glInt_iff v]
  exact ⟨h1, h2⟩

theorem pElemV_zero_one : ConeFinite.pElemV v c₀ Q₀' hc hQ' (oneLe hk) (0, 1) = 1 := by
  apply Subtype.ext
  show ConeFinite.nG v c₀ Q₀' hc hQ' 0 * ConeFinite.mG v c₀ Q₀' 1 = 1
  rw [ConeFinite.nG_zero v c₀ Q₀' hc hQ', map_one, mul_one]

theorem pElemV_inv (w : Fin k → Fv) (h : SOv v Q₀') :
    (ConeFinite.pElemV v c₀ Q₀' hc hQ' (oneLe hk) (w, h))⁻¹ =
      ConeFinite.pElemV v c₀ Q₀' hc hQ' (oneLe hk) (-(ConeFinite.mat v Q₀' h⁻¹ *ᵥ w), h⁻¹) := by
  rw [inv_eq_iff_mul_eq_one, pElemV_mul hc hQ' hk v, mulVec_neg, mulVec_mulVec, ← ConeFinite.mat_mul, mul_inv_cancel,
    ConeFinite.mat_one, one_mulVec, add_neg_cancel]
  exact pElemV_zero_one hc hQ' hk v

theorem inv_mem_BfinV {p : (ConeFinite.coneOrbitSectionV v c₀ Q₀' hc hQ' (oneLe hk)).stab}
    (hp : p ∈ BfinV hc hQ' hk v) : p⁻¹ ∈ BfinV hc hQ' hk v := by
  unfold BfinV at hp ⊢
  rcases hp with ⟨q, hq, e⟩
  have hinv : p⁻¹ = ConeFinite.pElemV v c₀ Q₀' hc hQ' (oneLe hk) (-(ConeFinite.mat v Q₀' q.2⁻¹ *ᵥ q.1), q.2⁻¹) := by
    rw [← e]; exact pElemV_inv hc hQ' hk v q.1 q.2
  rw [hinv]
  refine Set.mem_image_of_mem _ (show _ ∈ {w : Fin k → Fv | IntVec v w} ×ˢ (soStabSO v Q₀' : Set (SOv v Q₀')) from
    ⟨?_, (soStabSO v Q₀').inv_mem hq.2⟩)
  exact IntVec.neg v (IntVec.mulVec v (mat_mem_intMat_of_soStab v hq.2).2 hq.1)

theorem inv_preimage_BfinV : (fun p => p⁻¹) ⁻¹' (BfinV hc hQ' hk v) = BfinV hc hQ' hk v := by
  ext p
  simp only [mem_preimage]
  exact ⟨fun hp => by simpa using inv_mem_BfinV hc hQ' hk v hp, inv_mem_BfinV hc hQ' hk v⟩

theorem volV_intVec : LerayThick.volV (Analysis.haarV v) k {w : Fin k → Fv | IntVec v w} = 1 := by
  have : {w : Fin k → Fv | IntVec v w} = Set.pi univ fun _ => (Analysis.latticeV v 0 : Set Fv) := by
    ext w; simp [IntVec, Set.mem_pi, coe_latticeV_zero]
  rw [this, LerayThick.volV, Measure.pi_pi]
  simp [Analysis.haarV_latticeV_zero]

include hQ' in
theorem muPV_BfinV : ConeFinite.muPV v c₀ Q₀' hc hQ' (oneLe hk) (BfinV hc hQ' hk v) =
    muLocSO v Q₀' 1 (soStabSO v Q₀' : Set (SOv v Q₀')) := by
  rw [ConeFinite.muPV, (measurableEmbedding_pElemV hc hQ' hk v).map_apply, BfinV,
    (pElemV_injective hc hQ' hk v).preimage_image, Measure.prod_prod, volV_intVec, one_mul]

theorem mem_BfinV_iff (p : (ConeFinite.coneOrbitSectionV v c₀ Q₀' hc hQ' (oneLe hk)).stab) :
    p ∈ BfinV hc hQ' hk v ↔ IntVec v (tl (ConeFinite.mat v QC p *ᵥ e₀)) ∧
      ∃ h ∈ (soStabSO v Q₀' : Set (SOv v Q₀')), mM (ConeFinite.mat v Q₀' h) =
        nM (cAt c₀ (σV v)) (QAt Q₀' (σV v)) (-tl (ConeFinite.mat v QC p *ᵥ e₀)) * ConeFinite.mat v QC p := by
  constructor
  · rintro ⟨⟨w, h⟩, ⟨hw, hh⟩, rfl⟩
    have htl : tl (ConeFinite.mat v QC (ConeFinite.pElemV v c₀ Q₀' hc hQ' (oneLe hk) (w, h) : SOv v QC) *ᵥ
        e₀) = w := by
      rw [mat_pElemV hc hQ' hk v, ← mulVec_mulVec, mM_mulVec_e₀, tl_nM_mulVec_e₀ _ _ (cAt_ne_zero hc _)]
    rw [htl]
    refine ⟨hw, h, hh, ?_⟩
    rw [mat_pElemV hc hQ' hk v, ← Matrix.mul_assoc, nM_neg_mul _ _ (cAt_ne_zero hc _), Matrix.one_mul]
  · rintro ⟨hw, h, hh, e⟩
    refine ⟨(tl (ConeFinite.mat v QC p *ᵥ e₀), h), ⟨hw, hh⟩, ?_⟩
    apply Subtype.ext
    apply ConeFinite.mat_injective v QC
    rw [mat_pElemV hc hQ' hk v, e, ← Matrix.mul_assoc, nM_mul _ _ (cAt_ne_zero hc _), add_neg_cancel, nM_zero, Matrix.one_mul]

/-! ### Good places -/

theorem primV_eV : PrimV v (eV : Fin (k + 1 + 1) → Fv) := by
  refine ⟨fun i => ?_, 0, by simp [eV, v3]⟩
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;> simp [eV, v3]

theorem matInv_secV (z : ConeFinite.ConeTV v QC) :
    ConeFinite.mat v QC (secV hc hQ' hk v z)⁻¹ = (Dc hc hQ' hk).secMInv (σV v) z.1 := rfl

/-- **Good places**: $s(C^\circ_v\cap L_v^{\mathrm{prim}})\,P(\mathfrak o_v) = SO(L_v)$. -/
theorem ofCoordV_image_good (hv : (Dc hc hQ' hk).GoodV v) (h2c : Valued.v (cAt c₀ (σV v) * 2) = 1) :
    ofCoordV hc hQ' hk v '' ({z | PrimV v z.1} ×ˢ BfinV hc hQ' hk v) =
      (soStabSO v QC : Set (SOv v QC)) := by
  ext g
  constructor
  · rintro ⟨⟨z, p⟩, ⟨hz, hp⟩, rfl⟩
    obtain ⟨⟨w, h⟩, ⟨hw, hh⟩, rfl⟩ := hp
    have hs := ConeSecData.secM_mem_intMat hv hz (qH_of_mem_coneSetV v z.2)
    have hn1 := nM_mem_intMat v c₀ Q₀' h2c hw
    have hn2 := nM_mem_intMat v c₀ Q₀' h2c (hw.mulVec v (mat_mem_intMat_of_soStab v hh).2).neg
    have hm := mat_mem_intMat_of_soStab v hh
    refine mem_soStab_of_mat v ?_ ?_
    · show ConeFinite.mat v QC (secV hc hQ' hk v z * _) ∈ intMat v
      rw [ConeFinite.mat_mul, mat_secV, coe_pElemV hc hQ' hk v, ConeFinite.mat_mul, ConeFinite.mat_nG, ConeFinite.mat_mG]
      exact mul_mem_intMat v hs.1 (mul_mem_intMat v hn1 (mM_mem_intMat v hm.1))
    · show ConeFinite.mat v QC (secV hc hQ' hk v z * _)⁻¹ ∈ intMat v
      rw [_root_.mul_inv_rev, ConeFinite.mat_mul, matInv_secV, ← Subgroup.coe_inv, pElemV_inv hc hQ' hk v,
        coe_pElemV hc hQ' hk v,
        ConeFinite.mat_mul, ConeFinite.mat_nG, ConeFinite.mat_mG]
      exact mul_mem_intMat v (mul_mem_intMat v hn2 (mM_mem_intMat v hm.2)) hs.2
  · intro hg
    have hgi := (mem_glInt_iff v).mp (Subgroup.mem_subgroupOf.mp hg)
    set z : ConeFinite.ConeTV v QC := g • ConeFinite.eConeV v c₀ Q₀'
    have hz : PrimV v z.1 := by
      show PrimV v (ConeFinite.mat v QC g *ᵥ eV)
      exact (primV_eV v).mulVec v hgi.1 hgi.2
    set p := fibV hc hQ' hk v g
    have hgp : ofCoordV hc hQ' hk v (z, p) = g := ofCoordV_fibV hc hQ' hk v g
    refine ⟨(z, p), ⟨hz, ?_⟩, hgp⟩
    have hs := ConeSecData.secM_mem_intMat hv hz (qH_of_mem_coneSetV v z.2)
    have hp1 : ConeFinite.mat v QC (p : SOv v QC) ∈ intMat v := by
      show ConeFinite.mat v QC ((secV hc hQ' hk v z)⁻¹ * g) ∈ intMat v
      rw [ConeFinite.mat_mul, matInv_secV]
      exact mul_mem_intMat v hs.2 hgi.1
    have hp2 : ConeFinite.mat v QC (p : SOv v QC)⁻¹ ∈ intMat v := by
      show ConeFinite.mat v QC ((secV hc hQ' hk v z)⁻¹ * g)⁻¹ ∈ intMat v
      rw [_root_.mul_inv_rev, inv_inv, ConeFinite.mat_mul, mat_secV]
      exact mul_mem_intMat v hgi.2 hs.1
    obtain ⟨⟨w, h⟩, hpw⟩ := exists_pElemV hc hQ' hk v p
    have hw : IntVec v w := by
      have : tl (ConeFinite.mat v QC (p : SOv v QC) *ᵥ e₀) = w := by
        rw [← hpw, mat_pElemV hc hQ' hk v, ← mulVec_mulVec, mM_mulVec_e₀, tl_nM_mulVec_e₀ _ _ (cAt_ne_zero hc _)]
      rw [← this]
      exact (IntVec.mulVec v hp1 (by
        intro i; refine Fin.cases ?_ (fun i => ?_) i <;> simp [e₀])).tl v
    have hpm : ConeFinite.mat v QC (p : SOv v QC) = nM (cAt c₀ (σV v)) (QAt Q₀' (σV v)) w *
        mM (ConeFinite.mat v Q₀' h) := by rw [← hpw, mat_pElemV hc hQ' hk v]
    have hpm' : ConeFinite.mat v QC (p : SOv v QC)⁻¹ = mM (ConeFinite.mat v Q₀' h⁻¹) *
        nM (cAt c₀ (σV v)) (QAt Q₀' (σV v)) (-w) := by
      rw [← hpw, ← Subgroup.coe_inv, pElemV_inv hc hQ' hk v w h, mat_pElemV hc hQ' hk v,
        mM_mul_nM _ _ (ConeFinite.isometry_base v Q₀' h⁻¹), mulVec_neg]
    have hh : h ∈ soStabSO v Q₀' := by
      show ((h : orthGroup (Q₀'.map (algebraMap (𝓞 F) F)) Fv) : GL (Fin k) Fv) ∈ glInt v
      rw [mem_glInt_iff v]
      have e1 : mM (ConeFinite.mat v Q₀' h) = nM (cAt c₀ (σV v)) (QAt Q₀' (σV v)) (-w) *
          ConeFinite.mat v QC (p : SOv v QC) := by
        rw [hpm, ← Matrix.mul_assoc, nM_neg_mul _ _ (cAt_ne_zero hc _), Matrix.one_mul]
      have e2 : mM (ConeFinite.mat v Q₀' h⁻¹) = ConeFinite.mat v QC (p : SOv v QC)⁻¹ *
          nM (cAt c₀ (σV v)) (QAt Q₀' (σV v)) w := by
        rw [hpm', Matrix.mul_assoc, nM_neg_mul _ _ (cAt_ne_zero hc _), Matrix.mul_one]
      refine ⟨?_, ?_⟩
      · have := blk_mem_intMat v (mul_mem_intMat v (nM_mem_intMat v c₀ Q₀' h2c hw.neg) hp1)
        rw [← e1, blk_mM] at this
        exact this
      · have := blk_mem_intMat v (mul_mem_intMat v hp2 (nM_mem_intMat v c₀ Q₀' h2c hw))
        rw [← e2, blk_mM] at this
        exact this
    exact ⟨(w, h), ⟨hw, hh⟩, hpw⟩

end QuadFormsKB.Tamagawa.Measure.Weil

end
