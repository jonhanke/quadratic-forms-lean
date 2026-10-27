import QuadFormsKB.Tamagawa.Measure.Weil.ConeEulerLocalComplex
import QuadFormsKB.Tamagawa.Measure.Weil.MuTamProdSetNF

/-!
# The box formula for the adelic cone measure over every number field
$F$ any number field, $Q_0 = \langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'$ ($k\ge3$), $\sigma_C$ = `coneMeasure`.
The box formula `coneMeasure_coneBox` is stated for totally real $F$. With the complex places, for the
product set (`coneBoxNF`)
$$A = \{x\in C(\mathbb A) : x_w\in A_w\ (w\mid\infty),\ x_v\in A_v\ (v\in S),\ x_v\ \text{primitive}\ (v\notin S)\}$$
($S\supseteq$ `badCone`), **`coneMeasure_coneBoxNF`**:
$$\sigma_C(A) = M(S)\prod_{w\ \mathrm{real}}\sigma_{C,w}(A_w)\prod_{w\ \mathrm{complex}}\sigma_{C,w}(A_w)
  \prod_{v\in S}\sigma_{C,v}(A_v),$$
$M(S)$ = `boxConstNF'` (independent of the sets $A$). Same proof as `coneMeasure_coneBox`: the auxiliary box $B\subseteq P$
gets complex components (`W₀C`, `V₀C`), the product set formula is `muTam_prodSetNF`, and the complex local identity is
`lerayMeasureC_ofCoordCx_image` (`ConeEulerLocalComplex.lean`).
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
  (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) (hk : 3 ≤ k)

local notation "QC" => ConeFinite.Qcone c₀ Q₀'

/-! ### Cone points at the complex places -/

section Points

theorem eval_QwC_of_qH (w : {w : InfinitePlace F // w.IsComplex}) {z : Fin (k + 1 + 1) → ℂ}
    (h : qH (hesAt QC (σC w)) z = 0) : (QwC c₀ Q₀' w).eval z = 0 := by
  rw [qH_hesAt_C, show QCx QC w = QwC c₀ Q₀' w from ConeAdelic.QCx_cone w] at h
  exact (mul_eq_zero.mp h).resolve_left two_ne_zero

/-- The complex component of a point of the adelic cone, as a point of $C^\circ_w$. -/
def coneCpt (x : adelicCone QC) (w : {w : InfinitePlace F // w.IsComplex}) : ConeComplex.ConeT (QwC c₀ Q₀' w) :=
  ⟨adC x.1 w, eval_QwC_of_qH w (x.2.2.1 w).1, (x.2.2.1 w).2⟩

theorem measurable_coneCpt (w : {w : InfinitePlace F // w.IsComplex}) :
    Measurable fun x : adelicCone QC => coneCpt x w :=
  Measurable.subtype_mk ((continuous_adC w).measurable.comp measurable_subtype_coe)

end Points

/-! ### The product sets -/

section Box

/-- **The product set** $\{x : x_w\in A_w\ (w\mid\infty),\ x_v\in A_v\ (v\in S),\ x_v\ \text{primitive}\ (v\notin S)\}$
of the adelic cone, real and complex places. -/
def coneBoxNF (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w)))
    (AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ConeComplex.ConeT (QwC c₀ Q₀' w)))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (AV : ∀ v, Set (ConeFinite.ConeTV v QC)) : Set (adelicCone QC) :=
  {x | (∀ w, coneRpt x w ∈ AR w) ∧ (∀ w, coneCpt x w ∈ AC w) ∧ (∀ v ∈ S, coneVpt x v ∈ AV v) ∧
    ∀ v ∉ S, PrimV v (adV x.1 v)}

theorem measurableSet_coneBoxNF
    {AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w))} (hAR : ∀ w, MeasurableSet (AR w))
    {AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ConeComplex.ConeT (QwC c₀ Q₀' w))}
    (hAC : ∀ w, MeasurableSet (AC w)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    {AV : ∀ v, Set (ConeFinite.ConeTV v QC)} (hAV : ∀ v, MeasurableSet (AV v)) :
    MeasurableSet (coneBoxNF AR AC S AV) := by
  have : coneBoxNF AR AC S AV = (⋂ w, (fun x => coneRpt x w) ⁻¹' AR w) ∩ ((⋂ w, (fun x => coneCpt x w) ⁻¹' AC w) ∩
      ((⋂ v ∈ S, (fun x => coneVpt x v) ⁻¹' AV v) ∩
        ⋂ v ∉ S, (fun x : adelicCone QC => adV x.1 v) ⁻¹' {z | PrimV v z})) := by
    ext x; simp [coneBoxNF]
  rw [this]
  refine (MeasurableSet.iInter fun w => measurable_coneRpt w (hAR w)).inter
    ((MeasurableSet.iInter fun w => measurable_coneCpt w (hAC w)).inter
    ((MeasurableSet.biInter S.countable_toSet fun v _ => measurable_coneVpt v (hAV v)).inter
      (MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ =>
        ((continuous_adV v).measurable.comp measurable_subtype_coe) (measurableSet_primVec v))))

/-- The unit polydisc in $\mathbb C^k$. -/
def W₀C (k : ℕ) : Set (Fin k → ℂ) := Set.pi univ fun _ => Metric.closedBall (0 : ℂ) 1

theorem measurableSet_W₀C : MeasurableSet (W₀C k) :=
  MeasurableSet.univ_pi fun _ => Metric.isClosed_closedBall.measurableSet

theorem volume_W₀C_ne_zero : volume (W₀C k) ≠ 0 := by
  rw [W₀C, volume_pi_pi]
  exact Finset.prod_ne_zero_iff.mpr fun _ _ => (Metric.measure_closedBall_pos volume _ one_pos).ne'

theorem volume_W₀C_ne_top : volume (W₀C k) ≠ ⊤ := by
  rw [W₀C, volume_pi_pi]
  exact ENNReal.prod_ne_top fun _ _ => measure_closedBall_lt_top.ne

include hQ' in
theorem exists_V₀C (w : {w : InfinitePlace F // w.IsComplex}) :
    ∃ V : Set (ArchSOC (QCx Q₀' w)), MeasurableSet V ∧
      lerayMeasureC (QCx Q₀' w) (gramDetC_QCx_ne_zero Q₀' hQ' w) V ≠ 0 ∧
      lerayMeasureC (QCx Q₀' w) (gramDetC_QCx_ne_zero Q₀' hQ' w) V ≠ ⊤ := by
  have := isHaarMeasure_lerayMeasureC (gramDetC_QCx_ne_zero Q₀' hQ' w)
  exact OrbitSection.exists_pos_lt_top _ (NeZero.ne _)

/-- An auxiliary set $V_w\subseteq SO(Q'_w)(\mathbb C)$ of positive finite measure. -/
def V₀C (w : {w : InfinitePlace F // w.IsComplex}) : Set (ArchSOC (QCx Q₀' w)) := (exists_V₀C hQ' w).choose

theorem V₀C_spec (w : {w : InfinitePlace F // w.IsComplex}) :
    MeasurableSet (V₀C hQ' w) ∧ lerayMeasureC (QCx Q₀' w) (gramDetC_QCx_ne_zero Q₀' hQ' w) (V₀C hQ' w) ≠ 0 ∧
      lerayMeasureC (QCx Q₀' w) (gramDetC_QCx_ne_zero Q₀' hQ' w) (V₀C hQ' w) ≠ ⊤ :=
  (exists_V₀C hQ' w).choose_spec

/-- The local auxiliary box $B_w = n(W_0)\,\mathrm{diag}(1,1,V_w)\subseteq P_w$ at a complex place. -/
def BCx (w : {w : InfinitePlace F // w.IsComplex}) : Set (PCx Q₀' hc w) :=
  ConeComplex.pElem (cCx_ne hc w) (gramDetC_QCx' hQ' w) '' (W₀C k ×ˢ V₀C hQ' w)

/-- The adelic auxiliary box (every number field): $W$ = unit cubes at the real places, unit polydiscs at the complex
places, $\hat{\mathcal O}^k$ at the finite places; $V = \prod_wV_w\times SO(\hat L')$. -/
def WboxNF (k : ℕ) : Set (AdeleSpace F (Fin k)) :=
  {y | (∀ w, adR y w ∈ W₀ k) ∧ (∀ w, adC y w ∈ W₀C k) ∧ ∀ v, IntVec v (adV y v)}

def VboxNF : Set (SOAdele Q₀') := {h | (∀ w, h.1.1 w ∈ V₀ hQ' w) ∧ (∀ w, h.1.2 w ∈ V₀C hQ' w) ∧ h.2 ∈ KSO Q₀'}

def BboxNF : Set (Pc c₀ Q₀') := decompEquiv hc hQ' '' (WboxNF k ×ˢ VboxNF hQ')

end Box

/-! ### Membership, place by place -/

section Members

/-- The matrix $M_w$ of the fibre element at a complex place. -/
abbrev fibMatC (g : SOAdele QC) (w : {w : InfinitePlace F // w.IsComplex}) :
    Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) ℂ :=
  matC QC (fibOf hc hQ' hk g : SOAdele QC) w

/-- The local box condition at a complex place. -/
def condC (g : SOAdele QC) (w : {w : InfinitePlace F // w.IsComplex}) : Prop :=
  tl (fibMatC hc hQ' hk g w *ᵥ e₀) ∈ W₀C k ∧ ∃ h ∈ V₀C hQ' w, mM (ArchSOC.mat _ h) =
    nM (ConeAdelic.cCx c₀ w) (QCx Q₀' w) (-tl (fibMatC hc hQ' hk g w *ᵥ e₀)) * fibMatC hc hQ' hk g w

theorem matC_fibOf (g : SOAdele QC) (w : {w : InfinitePlace F // w.IsComplex}) :
    matC QC (fibOf hc hQ' hk g : SOAdele QC) w =
      matC QC g⁻¹ w * (Dc hc hQ' hk).secM (σC w) (matC QC g w *ᵥ eV) := by
  show matC QC (g⁻¹ * (Dc hc hQ' hk).secA (ptOf hc hQ' hk g)) w = _
  rw [matC_mul, ConeSecData.matC_secA]
  congr 2
  show adC (g • eA F k) w = _
  rw [smul_apply_fst_snd, adC_eA]

theorem castCx_smul_eCone (g : SOAdele QC) (w : {w : InfinitePlace F // w.IsComplex}) :
    castCx w (g.1.2 w) • ConeComplex.eCone (cCx_ne hc w) = coneCpt (ptOf hc hQ' hk g) w := by
  apply Subtype.ext
  rw [ConeComplex.coe_smul_cone, mat_castCx]
  show matC QC g w *ᵥ eV = adC (g • eA F k) w
  rw [smul_apply_fst_snd, adC_eA]

theorem coe_fibCx_inv (w : {w : InfinitePlace F // w.IsComplex}) (x : ArchSOC (QwC c₀ Q₀' w)) :
    (((fibCx hc hQ' hk w x)⁻¹ : PCx Q₀' hc w) : ArchSOC (QwC c₀ Q₀' w)) =
      x⁻¹ * secCx hc hQ' hk w (x • ConeComplex.eCone (cCx_ne hc w)) := by
  rw [Subgroup.coe_inv]
  show ((secCx hc hQ' hk w (x • ConeComplex.eCone (cCx_ne hc w)))⁻¹ * x)⁻¹ = _
  group

theorem mat_fibCx_inv (g : SOAdele QC) (w : {w : InfinitePlace F // w.IsComplex}) :
    ArchSOC.mat _ (((fibCx hc hQ' hk w (castCx w (g.1.2 w)))⁻¹ : PCx Q₀' hc w) : ArchSOC (QwC c₀ Q₀' w)) =
      fibMatC hc hQ' hk g w := by
  rw [coe_fibCx_inv hc hQ' hk w, ArchSOC.mat_mul, mat_secCx, castCx_smul_eCone hc hQ' hk g w, fibMatC,
    matC_fibOf]
  refine congrArg₂ (· * ·) rfl ?_
  show (Dc hc hQ' hk).secM (σC w) (adC (g • eA F k) w) = _
  rw [smul_apply_fst_snd, adC_eA]

theorem mem_ERC_iff (AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ConeComplex.ConeT (QwC c₀ Q₀' w)))
    (g : SOAdele QC) (w : {w : InfinitePlace F // w.IsComplex}) :
    castCx w (g.1.2 w) ∈ ofCoordCx hc hQ' hk w '' (AC w ×ˢ ((fun p => p⁻¹) ⁻¹' BCx hc hQ' w)) ↔
      coneCpt (ptOf hc hQ' hk g) w ∈ AC w ∧ condC hc hQ' hk g w := by
  rw [mem_ofCoordCx_image hc hQ' hk w, castCx_smul_eCone hc hQ' hk g w]
  refine and_congr Iff.rfl ?_
  show (fibCx hc hQ' hk w (castCx w (g.1.2 w)))⁻¹ ∈ BCx hc hQ' w ↔ _
  have key := mem_pElemC_image_iff hc hQ' hk w (W := W₀C k) (V := V₀C hQ' w)
    ((fibCx hc hQ' hk w (castCx w (g.1.2 w)))⁻¹)
  have hm := mat_fibCx_inv hc hQ' hk g w
  exact key.trans (by rw [show ArchSOC.mat _ ((((fibCx hc hQ' hk w (castCx w (g.1.2 w)))⁻¹ :
      (orbCx hc hQ' hk w).stab)) : ArchSOC (QwC c₀ Q₀' w)) = fibMatC hc hQ' hk g w from hm]; rfl)

/-- The Levi component at a complex place lies in $V_w$ iff the local box condition holds. -/
theorem leviC_mem_iff (p : Pc c₀ Q₀') (w : {w : InfinitePlace F // w.IsComplex}) :
    (leviOf hc hQ' p).1.2 w ∈ V₀C hQ' w ↔ ∃ h ∈ V₀C hQ' w, mM (ArchSOC.mat _ h) =
      nM (ConeAdelic.cCx c₀ w) (QCx Q₀' w) (-tl (matC QC (p : SOAdele QC) w *ᵥ e₀)) *
        matC QC (p : SOAdele QC) w := by
  have he : mM (ArchSOC.mat _ ((leviOf hc hQ' p).1.2 w)) =
      nM (ConeAdelic.cCx c₀ w) (QCx Q₀' w) (-tl (matC QC (p : SOAdele QC) w *ᵥ e₀)) * matC QC (p : SOAdele QC) w :=
    mM_leviAt hc hQ' (σC w) _ (isSOAt_C (p : SOAdele QC) w) (heC p w)
  constructor
  · intro h; exact ⟨_, h, he⟩
  · rintro ⟨h, hh, e⟩
    have : h = (leviOf hc hQ' p).1.2 w := by
      apply Subtype.ext; apply Units.ext
      exact mM_injective (e.trans he.symm)
    rw [← this]; exact hh

/-- **The fibre element lies in the auxiliary box** iff all the local box conditions hold (every number field). -/
theorem fibOf_mem_BboxNF_iff (g : SOAdele QC) :
    fibOf hc hQ' hk g ∈ BboxNF hc hQ' ↔
      (∀ w, condR hc hQ' hk g w) ∧ (∀ w, condC hc hQ' hk g w) ∧ ∀ v, condV hc hQ' hk g v := by
  rw [BboxNF, MeasurableEquiv.image_eq_preimage_symm, mem_preimage, decompEquiv_symm, mem_prod]
  simp only [WboxNF, VboxNF, mem_setOf_eq, mem_KSO_iff, adR_wOf, adC_wOf, adV_wOf, leviR_mem_iff, leviC_mem_iff,
    leviV_mem_iff]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩
    exact ⟨fun w => ⟨h1 w, h4 w⟩, fun w => ⟨h2 w, h5 w⟩, fun v => ⟨h3 v, h6 v⟩⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨fun w => (h1 w).1, fun w => (h2 w).1, fun v => (h3 v).1⟩, fun w => (h1 w).2, fun w => (h2 w).2,
      fun v => (h3 v).2⟩

end Members

/-! ### The set identity and the measure of a product set -/

section Measure

/-- The local sets at the complex places. -/
def ERsetC (AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ConeComplex.ConeT (QwC c₀ Q₀' w)))
    (w : {w : InfinitePlace F // w.IsComplex}) : Set (ArchSOC (QCx QC w)) :=
  castCx w ⁻¹' (ofCoordCx hc hQ' hk w '' (AC w ×ˢ ((fun p => p⁻¹) ⁻¹' BCx hc hQ' w)))

/-- **The inverse of the coordinate image of a product set is a box of $SO(V)(\mathbb A)$** (every number field). -/
theorem inv_coord_boxNF_eq (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w)))
    (AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ConeComplex.ConeT (QwC c₀ Q₀' w)))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S) (AV : ∀ v, Set (ConeFinite.ConeTV v QC)) :
    (fun g => g⁻¹) ⁻¹' ((coneCoord hc hQ' hk).symm ⁻¹' (coneBoxNF AR AC S AV ×ˢ BboxNF hc hQ')) =
      {g : SOAdele QC | (∀ w, g.1.1 w ∈ ERset hc hQ' hk AR w) ∧ (∀ w, g.1.2 w ∈ ERsetC hc hQ' hk AC w) ∧
        g.2 ∈ {gf : SOAf QC | ∀ v, evalSO QC v gf ∈ EVset hc hQ' hk S AV v}} := by
  ext g
  simp only [mem_preimage, coneCoord_symm_inv, mem_prod, mem_setOf_eq, fibOf_mem_BboxNF_iff, ERset, ERsetC, EVset]
  simp only [mem_EV_iff hc hQ' hk S hS AV g]
  simp only [mem_preimage, mem_ER_iff hc hQ' hk AR g, mem_ERC_iff hc hQ' hk AC g]
  simp only [coneBoxNF, mem_setOf_eq]
  constructor
  · rintro ⟨⟨h1, h1c, h2, h3⟩, h4, h4c, h5⟩
    exact ⟨fun w => ⟨h1 w, h4 w⟩, fun w => ⟨h1c w, h4c w⟩, fun v => ⟨⟨h2 v, h3 v⟩, h5 v⟩⟩
  · rintro ⟨h1, h1c, h2⟩
    exact ⟨⟨fun w => (h1 w).1, fun w => (h1c w).1, fun v => (h2 v).1.1, fun v => (h2 v).1.2⟩, fun w => (h1 w).2,
      fun w => (h1c w).2, fun v => (h2 v).2⟩

theorem measurableSet_BCx (w : {w : InfinitePlace F // w.IsComplex}) : MeasurableSet (BCx hc hQ' w) :=
  (ConeComplex.measurableEmbedding_pElem (cCx_ne hc w) (gramDetC_QCx' hQ' w)).measurableSet_image.mpr
    (measurableSet_W₀C.prod (V₀C_spec hQ' w).1)

theorem measurableSet_WboxNF : MeasurableSet (WboxNF (F := F) k) := by
  have : WboxNF (F := F) k = (⋂ w, (fun y : AdeleSpace F (Fin k) => adR y w) ⁻¹' W₀ k) ∩
      ((⋂ w, (fun y : AdeleSpace F (Fin k) => adC y w) ⁻¹' W₀C k) ∩
        ⋂ v, (fun y : AdeleSpace F (Fin k) => adV y v) ⁻¹' {z | IntVec v z}) := by
    ext y; simp [WboxNF]
  rw [this]
  exact (MeasurableSet.iInter fun w => (continuous_adR w).measurable measurableSet_W₀).inter
    ((MeasurableSet.iInter fun w => (continuous_adC w).measurable measurableSet_W₀C).inter
      (MeasurableSet.iInter fun v => (continuous_adV v).measurable (measurableSet_intVec v)))

theorem measurableSet_VboxNF : MeasurableSet (VboxNF hQ') := by
  have : VboxNF hQ' = (⋂ w, (fun h : SOAdele Q₀' => h.1.1 w) ⁻¹' V₀ hQ' w) ∩
      ((⋂ w, (fun h : SOAdele Q₀' => h.1.2 w) ⁻¹' V₀C hQ' w) ∩
        (fun h : SOAdele Q₀' => h.2) ⁻¹' (KSO Q₀' : Set (SOAf Q₀'))) := by
    ext h; simp [VboxNF]
  rw [this]
  exact (MeasurableSet.iInter fun w => ((measurable_pi_apply w).comp (measurable_fst.comp measurable_fst))
    (V₀_spec hQ' w).1).inter ((MeasurableSet.iInter fun w => ((measurable_pi_apply w).comp
      (measurable_snd.comp measurable_fst)) (V₀C_spec hQ' w).1).inter
      (measurable_snd (isOpen_KSO Q₀').measurableSet))

theorem measurableSet_BboxNF : MeasurableSet (BboxNF hc hQ') :=
  (decompEquiv hc hQ').measurableEmbedding.measurableSet_image.mpr
    ((measurableSet_WboxNF (F := F)).prod (measurableSet_VboxNF hQ'))

theorem finBoxSetNF_eq (S : Finset (HeightOneSpectrum (𝓞 F))) (AV : ∀ v, Set (ConeFinite.ConeTV v QC)) :
    {gf : SOAf QC | ∀ v, evalSO QC v gf ∈ EVset hc hQ' hk S AV v} = boxSO QC S (EVset hc hQ' hk S AV) := by
  ext gf
  simp only [mem_setOf_eq, boxSO]
  constructor
  · intro h
    refine ⟨fun v _ => h v, fun v hv => ?_⟩
    have := h v
    rwa [EVset, if_neg hv] at this
  · rintro ⟨h1, h2⟩ v
    by_cases hv : v ∈ S
    · exact h1 v hv
    · rw [EVset, if_neg hv]; exact h2 v hv

set_option maxHeartbeats 1000000 in
open Classical in
/-- **The measure of a product set, first form** (every number field). -/
theorem coneMeasure_coneBoxNF_mul_aux
    {AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w))} (hAR : ∀ w, MeasurableSet (AR w))
    {AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ConeComplex.ConeT (QwC c₀ Q₀' w))}
    (hAC : ∀ w, MeasurableSet (AC w))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S) {AV : ∀ v, Set (ConeFinite.ConeTV v QC)}
    (hAV : ∀ v, MeasurableSet (AV v)) :
    coneMeasure hc hQ' hk (coneBoxNF AR AC S AV) * coneMuP hc hQ' (BboxNF hc hQ') =
      ENNReal.ofReal (cF F (k + 1 + 1) * cxWeil F (k + 1 + 1)) *
        ((∏ w, lerayMeasure (Qw c₀ Q₀' w) (ConeReal.gramDetR_cone (cRe_ne hc w) (gramDetR_QRe' hQ' w))
          (ofCoordR hc hQ' hk w '' (AR w ×ˢ ((fun p => p⁻¹) ⁻¹' BR hc hQ' w)))) *
        ∏ w, lerayMeasureC (QwC c₀ Q₀' w) (ConeComplex.gramDetC_cone (cCx_ne hc w) (gramDetC_QCx' hQ' w))
          (ofCoordCx hc hQ' hk w '' (AC w ×ˢ ((fun p => p⁻¹) ⁻¹' BCx hc hQ' w)))) *
        Measure.muFin QC (fun _ => 1) (boxSO QC S (EVset hc hQ' hk S AV)) := by
  have hA := measurableSet_coneBoxNF hAR hAC S hAV
  have hB := measurableSet_BboxNF hc hQ'
  have hpre : MeasurableSet ((coneCoord hc hQ' hk).symm ⁻¹' (coneBoxNF AR AC S AV ×ˢ BboxNF hc hQ')) :=
    (coneCoord hc hQ' hk).symm.measurable (hA.prod hB)
  rw [← coneMeasure_mul hc hQ' hk hA hB]
  change muTam QC (nondeg_QC hc hQ') (fun _ => 1) _ = _
  rw [← muTam_inv_preimage QC (nondeg_QC hc hQ') (by omega) _ hpre, inv_coord_boxNF_eq hc hQ' hk AR AC S hS AV,
    muTam_prodSetNF, finBoxSetNF_eq]
  congr 3
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [ERset, ← Measure.map_apply (measurable_castR w)
      (measurableSet_ofCoordR_image hc hQ' hk w (hAR w) (measurable_inv (measurableSet_BR hc hQ' w))),
      map_castR hc hQ' w]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [ERsetC, ← Measure.map_apply (measurable_castCx w)
      (measurableSet_ofCoordCx_image hc hQ' hk w (hAC w) (measurable_inv (measurableSet_BCx hc hQ' w))),
      map_castCx hc hQ' w]

end Measure

/-! ### The local evaluations and the normalized box formula -/

section Formula

theorem lerayMeasureC_ERsetC (w : {w : InfinitePlace F // w.IsComplex})
    {A : Set (ConeComplex.ConeT (QwC c₀ Q₀' w))} (hA : MeasurableSet A) :
    lerayMeasureC (QwC c₀ Q₀' w) (ConeComplex.gramDetC_cone (cCx_ne hc w) (gramDetC_QCx' hQ' w))
        (ofCoordCx hc hQ' hk w '' (A ×ˢ ((fun p => p⁻¹) ⁻¹' BCx hc hQ' w))) =
      cCw c₀ k w * ConeComplex.sigCone (cCx_ne hc w) A *
        (volume (W₀C k) * lerayMeasureC (QCx Q₀' w) (gramDetC_QCx_ne_zero Q₀' hQ' w) (V₀C hQ' w)) := by
  rw [lerayMeasureC_ofCoordCx_image hc hQ' hk w hA (measurable_inv (measurableSet_BCx hc hQ' w))]
  congr 1
  have h1 := muPC_inv_preimage hc hQ' hk w (B := BCx hc hQ' w) (measurableSet_BCx hc hQ' w)
  have h2 := muPC_pElem_image hc hQ' w (W := W₀C k) measurableSet_W₀C (V₀C_spec hQ' w).1
  exact h1.trans h2

/-- The mixed-space unit box $\{m : m_w\in[0,1]\ (w\ \mathrm{real}),\ |m_w|\le1\ (w\ \mathrm{complex})\}$. -/
def mBoxNF (F : Type) [Field F] [NumberField F] : Set (NumberField.mixedEmbedding.mixedSpace F) :=
  {m | (∀ w, m.1 w ∈ Icc 0 1) ∧ ∀ w, m.2 w ∈ Metric.closedBall (0 : ℂ) 1}

theorem mBoxNF_eq : mBoxNF F = (Set.pi univ fun _ => Icc (0 : ℝ) 1) ×ˢ
    (Set.pi univ fun _ => Metric.closedBall (0 : ℂ) 1) := by
  ext m; simp only [mBoxNF, mem_prod, Set.mem_pi, mem_univ, true_implies, mem_ofPred_eq]

theorem selfDualInf_mBoxNF_ne_top : Analysis.selfDualInf (F := F) (mBoxNF F) ≠ ⊤ := by
  have hcpt : IsCompact (mBoxNF F) := by
    rw [mBoxNF_eq]
    exact (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_closedBall _ _)
  exact hcpt.measure_lt_top.ne

theorem selfDualInf_mBoxNF_ne_zero : Analysis.selfDualInf (F := F) (mBoxNF F) ≠ 0 := by
  set Uo : Set (NumberField.mixedEmbedding.mixedSpace F) :=
    (Set.pi (univ : Set {w : InfinitePlace F // w.IsReal}) fun _ => Ioo (0 : ℝ) 1) ×ˢ
      (Set.pi (univ : Set {w : InfinitePlace F // w.IsComplex}) fun _ => Metric.ball (0 : ℂ) 1) with hUo
  have hopen : IsOpen Uo :=
    (isOpen_set_pi (i := (univ : Set {w : InfinitePlace F // w.IsReal})) (s := fun _ => Ioo (0 : ℝ) 1)
      finite_univ fun _ _ => isOpen_Ioo).prod
    (isOpen_set_pi (i := (univ : Set {w : InfinitePlace F // w.IsComplex})) (s := fun _ => Metric.ball (0 : ℂ) 1)
      finite_univ fun _ _ => Metric.isOpen_ball)
  have hne : Uo.Nonempty :=
    ⟨((fun _ => (1 / 2 : ℝ)), (0 : {w : InfinitePlace F // w.IsComplex} → ℂ)),
      fun w _ => ⟨by norm_num, by norm_num⟩, fun w _ => Metric.mem_ball_self one_pos⟩
  refine (measure_pos_of_superset ?_ (hopen.measure_ne_zero _ hne)).ne'
  intro m hm
  exact ⟨fun w => Ioo_subset_Icc_self (hm.1 w (mem_univ w)),
    fun w => Metric.ball_subset_closedBall (hm.2 w (mem_univ w))⟩

theorem WboxNF_eq : WboxNF (F := F) k = boxSet (Set.pi univ fun _ => mBoxNF F) OHatVec := by
  ext y
  simp only [WboxNF, mem_setOf_eq, mem_boxSet, Set.mem_pi, mem_univ, true_implies, mBoxNF, W₀, W₀C, OHatVec,
    OHat, IntVec]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => ⟨fun w => h1 w i, fun w => h2 w i⟩, fun i v => ?_⟩
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (h3 v i)
  · rintro ⟨h1, h2⟩
    exact ⟨fun w i => (h1 i).1 w, fun w i => (h1 i).2 w,
      fun v i => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h2 i v)⟩

theorem muAddVec_WboxNF_ne_zero : muAddVec F (Fin k) (WboxNF (F := F) k) ≠ 0 := by
  rw [WboxNF_eq, muAddVec_boxSet, Measure.pi_pi]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun _ _ => selfDualInf_mBoxNF_ne_zero) muFinVec_OHatVec_ne_zero

theorem muAddVec_WboxNF_ne_top : muAddVec F (Fin k) (WboxNF (F := F) k) ≠ ⊤ := by
  rw [WboxNF_eq, muAddVec_boxSet, Measure.pi_pi]
  exact ENNReal.mul_ne_top (ENNReal.prod_ne_top fun _ _ => selfDualInf_mBoxNF_ne_top) muFinVec_OHatVec_ne_top

end Formula

/-! ### The normalized box formula -/

section Normalized

open Classical in
theorem coneMuP_BboxNF : coneMuP hc hQ' (BboxNF hc hQ') = muAddVec F (Fin k) (WboxNF (F := F) k) *
    (ENNReal.ofReal (cF F k * cxWeil F k) * ((∏ w, lerayMeasure (QRe Q₀' w) (gramDetR_QRe' hQ' w) (V₀ hQ' w)) *
      ∏ w, lerayMeasureC (QCx Q₀' w) (gramDetC_QCx_ne_zero Q₀' hQ' w) (V₀C hQ' w)) *
      ENNReal.ofReal (finFactor Q₀' (fun _ => 1))) := by
  rw [coneMuP, BboxNF, MeasurableEquiv.map_apply, MeasurableEquiv.preimage_image, Measure.prod_prod,
    dwTam_eq_muAddVec]
  congr 1
  have : VboxNF hQ' = {h : SOAdele Q₀' | (∀ w, h.1.1 w ∈ V₀ hQ' w) ∧ (∀ w, h.1.2 w ∈ V₀C hQ' w) ∧
      h.2 ∈ (KSO Q₀' : Set (SOAf Q₀'))} := rfl
  rw [this]
  change muTam Q₀' hQ' (fun _ => 1) _ = _
  rw [muTam_prodSetNF, muFin_KSO]

theorem coneMuP_BboxNF_ne_zero (hk : 3 ≤ k) : coneMuP hc hQ' (BboxNF hc hQ') ≠ 0 := by
  classical
  rw [coneMuP_BboxNF]
  refine mul_ne_zero muAddVec_WboxNF_ne_zero (mul_ne_zero (mul_ne_zero ?_ (mul_ne_zero ?_ ?_)) ?_)
  · exact (ENNReal.ofReal_pos.mpr (mul_pos cF_pos' cxWeil_pos)).ne'
  · exact Finset.prod_ne_zero_iff.mpr fun w _ => (V₀_spec hQ' w).2.1
  · exact Finset.prod_ne_zero_iff.mpr fun w _ => (V₀C_spec hQ' w).2.1
  · rw [ne_eq, ENNReal.ofReal_eq_zero, not_le, finFactor_one Q₀' hQ']
    exact tprod_siegelDensity_pos hk Q₀' hQ'

theorem coneMuP_BboxNF_ne_top : coneMuP hc hQ' (BboxNF hc hQ') ≠ ⊤ := by
  classical
  rw [coneMuP_BboxNF]
  exact ENNReal.mul_ne_top muAddVec_WboxNF_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (ENNReal.prod_ne_top fun w _ => (V₀_spec hQ' w).2.2)
      (ENNReal.prod_ne_top fun w _ => (V₀C_spec hQ' w).2.2))) ENNReal.ofReal_ne_top)

open Classical in
/-- **The constant of the box formula** over every number field, for a finite set $S\supseteq$ `badCone`. -/
def boxConstNF' (S : Finset (HeightOneSpectrum (𝓞 F))) : ℝ≥0∞ :=
  ENNReal.ofReal (cF F (k + 1 + 1) * cxWeil F (k + 1 + 1)) *
      ((∏ w, ENNReal.ofReal (cRw c₀ k w) *
          (volume (W₀ k) * lerayMeasure (QRe Q₀' w) (gramDetR_QRe' hQ' w) (V₀ hQ' w))) *
        ∏ w, cCw c₀ k w *
          (volume (W₀C k) * lerayMeasureC (QCx Q₀' w) (gramDetC_QCx_ne_zero Q₀' hQ' w) (V₀C hQ' w))) *
      ((∏ v ∈ S, ENNReal.ofReal (cVv c₀ k v) * muLocSO v Q₀' 1 (soStabSO v Q₀' : Set (SOv v Q₀'))) *
        ENNReal.ofReal (∏' v, if v ∈ S then 1 else (muLocSO v QC 1 (soStabSO v QC : Set (SOv v QC))).toReal)) /
    coneMuP hc hQ' (BboxNF hc hQ')

open Classical in
/-- **The box formula over every number field** ($k\ge3$, $S\supseteq$ `badCone`):
$$\sigma_C\Big(\{x : x_w\in A_w,\ x_v\in A_v\ (v\in S),\ x_v\ \text{primitive}\ (v\notin S)\}\Big) =
  M(S)\prod_{w\ \mathrm{real}}\sigma_{C,w}(A_w)\prod_{w\ \mathrm{complex}}\sigma_{C,w}(A_w)\prod_{v\in S}\sigma_{C,v}(A_v),$$
$M(S)$ = `boxConstNF' S`. -/
@[kb "weil1982" "§2.3, p. 21; §4.5, p. 108 (the cone measure on product sets) [unverified page]"]
theorem coneMeasure_coneBoxNF
    {AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w))} (hAR : ∀ w, MeasurableSet (AR w))
    {AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ConeComplex.ConeT (QwC c₀ Q₀' w))}
    (hAC : ∀ w, MeasurableSet (AC w))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S) {AV : ∀ v, Set (ConeFinite.ConeTV v QC)}
    (hAV : ∀ v, MeasurableSet (AV v)) :
    coneMeasure hc hQ' hk (coneBoxNF AR AC S AV) =
      boxConstNF' hc hQ' S * ((∏ w, ConeReal.sigCone (cRe_ne hc w) (AR w)) *
        ∏ w, ConeComplex.sigCone (cCx_ne hc w) (AC w)) *
        ∏ v ∈ S, ConeFinite.sigConeV v QC (ConeFinite.nondeg_cone c₀ Q₀' hc hQ') (AV v) := by
  have h := coneMeasure_coneBoxNF_mul_aux hc hQ' hk hAR hAC S hS hAV
  have hEV : ∀ v ∈ S, MeasurableSet (EVset hc hQ' hk S AV v) := fun v _ => measurableSet_EVset hc hQ' hk S hAV v
  have hmult := multipliable_muLocSO_one QC (nondeg_QC hc hQ') (by omega : k + 1 + 1 ≠ 0) (by omega : k + 1 + 1 ≠ 2)
  rw [muFin_boxSO_split QC (nondeg_QC hc hQ') (fun _ => one_pos) hmult S _ hEV] at h
  simp only [lerayMeasure_ERset hc hQ' hk _ (hAR _), lerayMeasureC_ERsetC hc hQ' hk _ (hAC _)] at h
  rw [Finset.prod_congr rfl fun v hv => muLocSO_EVset hc hQ' hk S hAV hv] at h
  have h0 := coneMuP_BboxNF_ne_zero hc hQ' hk
  have ht := coneMuP_BboxNF_ne_top hc hQ'
  have hσ := (ENNReal.eq_div_iff h0 ht).mpr (show coneMuP hc hQ' (BboxNF hc hQ') *
      coneMeasure hc hQ' hk (coneBoxNF AR AC S AV) = _ from (mul_comm _ _).trans h)
  rw [hσ, boxConstNF', ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  simp only [Finset.prod_mul_distrib]
  ring

end Normalized

end QuadFormsKB.Tamagawa.Measure.Weil

end
