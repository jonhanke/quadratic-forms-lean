import QuadFormsKB.Tamagawa.Measure.Weil.ConeEulerLocalFin
import QuadFormsKB.Tamagawa.Measure.Weil.ConeEulerLocalReal
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereBoxFormula

/-!
# The box formula for the adelic cone measure

$F$ totally real, $Q_0 = \langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'$ ($k\ge3$), $\sigma_C$ = `coneMeasure`. For a product set
$$A = \{x\in C(\mathbb A) : x_w\in A_w\ (w\mid\infty),\ x_v\in A_v\ (v\in S),\ x_v\ \text{primitive}\ (v\notin S)\}$$
(`coneBox`, $S$ a finite set of places containing the bad places `badCone`), **`coneMeasure_coneBox_mul`**:
$$\sigma_C(A)\,\mu_P(B) = c_F(n)\prod_w c_w\,\sigma_{C,w}(A_w)\,\mu_{P,w}(B_w)\cdot\prod_{v\in S}c_v\,\sigma_{C,v}(A_v)\,\mu'_v(SO(L'_v))
  \cdot\prod'_{v\notin S}\mu_v(SO(L_v))$$
for a fixed auxiliary box $B\subseteq P$: the quotient identity $\sigma_C(A)\mu_P(B) = \mu(\mathrm{coord}(A\times B))$, the inversion
invariance of $\mu$, and the fact that $\mathrm{coord}(A\times B)^{-1}$ is a box of $SO(V)(\mathbb A)$ whose local factors are
the sets of the local identities (`ConeEulerLocalFin.lean`, `ConeEulerLocalReal.lean`).
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

/-! ### Real-place coordinates without the orbit-section wrapper -/

section RealCoord

variable (w : {w : InfinitePlace F // w.IsReal})

/-- The stabilizer $P_w$ of $e$ in $SO(Q_w)(\mathbb R)$. -/
abbrev PR (Q₀' : QuadForm (𝓞 F) k) (hc : c₀ ≠ 0) (w : {w : InfinitePlace F // w.IsReal}) :
    Subgroup (ArchSO (Qw c₀ Q₀' w)) := ConeReal.stabP (Q' := QRe Q₀' w) (cRe_ne hc w)

/-- Our coordinates $(z, p)\mapsto s(z)\,p$ at $w$. -/
def ofCoordR (q : ConeReal.ConeT (Qw c₀ Q₀' w) × PR Q₀' hc w) : ArchSO (Qw c₀ Q₀' w) :=
  secR hc hQ' hk w q.1 * (q.2 : ArchSO (Qw c₀ Q₀' w))

/-- The fibre coordinate $g\mapsto s(ge)^{-1}g$ at $w$. -/
def fibR (g : ArchSO (Qw c₀ Q₀' w)) : PR Q₀' hc w :=
  ⟨(secR hc hQ' hk w (g • ConeReal.eCone (cRe_ne hc w)))⁻¹ * g, by
    rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
    exact (secR_smul hc hQ' hk w _).symm⟩

theorem ofCoordR_smul (q : ConeReal.ConeT (Qw c₀ Q₀' w) × PR Q₀' hc w) :
    ofCoordR hc hQ' hk w q • ConeReal.eCone (cRe_ne hc w) = q.1 := by
  have hp : (q.2 : ArchSO (Qw c₀ Q₀' w)) • ConeReal.eCone (cRe_ne hc w) = ConeReal.eCone (cRe_ne hc w) := q.2.2
  rw [ofCoordR, mul_smul, hp, secR_smul]

theorem ofCoordR_fibR (g : ArchSO (Qw c₀ Q₀' w)) :
    ofCoordR hc hQ' hk w (g • ConeReal.eCone (cRe_ne hc w), fibR hc hQ' hk w g) = g := by
  simp [ofCoordR, fibR]

theorem fibR_ofCoordR (q : ConeReal.ConeT (Qw c₀ Q₀' w) × PR Q₀' hc w) :
    fibR hc hQ' hk w (ofCoordR hc hQ' hk w q) = q.2 := by
  apply Subtype.ext
  simp only [fibR, ofCoordR_smul]
  simp [ofCoordR]

theorem mem_ofCoordR_image {A : Set (ConeReal.ConeT (Qw c₀ Q₀' w))} {B : Set (PR Q₀' hc w)}
    (g : ArchSO (Qw c₀ Q₀' w)) :
    g ∈ ofCoordR hc hQ' hk w '' (A ×ˢ B) ↔ g • ConeReal.eCone (cRe_ne hc w) ∈ A ∧ fibR hc hQ' hk w g ∈ B := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [ofCoordR_smul, fibR_ofCoordR]; exact hq
  · rintro ⟨h1, h2⟩
    exact ⟨_, ⟨h1, h2⟩, ofCoordR_fibR hc hQ' hk w g⟩

theorem lerayMeasure_ofCoordR_image {A : Set (ConeReal.ConeT (Qw c₀ Q₀' w))} (hA : MeasurableSet A)
    {B : Set (PR Q₀' hc w)} (hB : MeasurableSet B) :
    lerayMeasure (Qw c₀ Q₀' w) (ConeReal.gramDetR_cone (cRe_ne hc w) (gramDetR_QRe' hQ' w))
        (ofCoordR hc hQ' hk w '' (A ×ˢ B)) =
      ENNReal.ofReal ((|2 * ConeAdelic.cRe c₀ w| ^ (2 * k + 2))⁻¹) * ConeReal.sigCone (cRe_ne hc w) A *
        ConeReal.muP (cRe_ne hc w) (gramDetR_QRe' hQ' w) B :=
  lerayMeasure_orbR_image hc hQ' hk w hA hB

end RealCoord


/-! ### Cone points at the places -/

section Points

theorem eval_Qw_of_qH (w : {w : InfinitePlace F // w.IsReal}) {z : Fin (k + 1 + 1) → ℝ}
    (h : qH (hesAt QC (σR w)) z = 0) : (Qw c₀ Q₀' w).eval z = 0 := by
  have h2 := QuadFormsKB.Siegel.Kneser.two_mul_evalIn (K := ℝ) (Qw c₀ Q₀' w) z
  rw [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id, ← hesAt_eq_Qw] at h2
  have h3 : 2 * QuadForm.evalIn ℝ (Qw c₀ Q₀' w) z = 0 := by rw [h2]; exact h
  exact (mul_eq_zero.mp h3).resolve_left two_ne_zero

theorem evalIn_Qp_of_qH (v : HeightOneSpectrum (𝓞 F)) {z : Fin (k + 1 + 1) → v.adicCompletion F}
    (h : qH (hesAt QC (σV v)) z = 0) : (LocalDensity.NF.Qp v QC).evalIn (v.adicCompletion F) z = 0 := by
  rw [qH_hesAt_eq_two_mul] at h
  rw [LocalDensity.NF.evalIn_Qp]
  exact (mul_eq_zero.mp h).resolve_left two_ne_zero

/-- The real component of a point of the adelic cone, as a point of $C^\circ_w$. -/
def coneRpt (x : adelicCone QC) (w : {w : InfinitePlace F // w.IsReal}) : ConeReal.ConeT (Qw c₀ Q₀' w) :=
  ⟨adR x.1 w, eval_Qw_of_qH w (x.2.1 w).1, (x.2.1 w).2⟩

/-- The $v$-component of a point of the adelic cone, as a point of $C^\circ_v$. -/
def coneVpt (x : adelicCone QC) (v : HeightOneSpectrum (𝓞 F)) : ConeFinite.ConeTV v QC :=
  ⟨adV x.1 v, evalIn_Qp_of_qH v (x.2.2.2.1 v).1, (x.2.2.2.1 v).2⟩

theorem measurable_coneRpt (w : {w : InfinitePlace F // w.IsReal}) :
    Measurable fun x : adelicCone QC => coneRpt x w :=
  Measurable.subtype_mk ((continuous_adR w).measurable.comp measurable_subtype_coe)

theorem measurable_coneVpt (v : HeightOneSpectrum (𝓞 F)) : Measurable fun x : adelicCone QC => coneVpt x v :=
  Measurable.subtype_mk ((continuous_adV v).measurable.comp measurable_subtype_coe)

end Points

/-! ### The product sets -/

section Box

/-- **The product set** $\{x : x_w\in A_w,\ x_v\in A_v\ (v\in S),\ x_v\ \text{primitive}\ (v\notin S)\}$ of the adelic cone. -/
def coneBox (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w)))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (AV : ∀ v, Set (ConeFinite.ConeTV v QC)) : Set (adelicCone QC) :=
  {x | (∀ w, coneRpt x w ∈ AR w) ∧ (∀ v ∈ S, coneVpt x v ∈ AV v) ∧ ∀ v ∉ S, PrimV v (adV x.1 v)}

theorem measurableSet_coneBox {AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w))}
    (hAR : ∀ w, MeasurableSet (AR w)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    {AV : ∀ v, Set (ConeFinite.ConeTV v QC)} (hAV : ∀ v, MeasurableSet (AV v)) :
    MeasurableSet (coneBox AR S AV) := by
  have : coneBox AR S AV = (⋂ w, (fun x => coneRpt x w) ⁻¹' AR w) ∩
      ((⋂ v ∈ S, (fun x => coneVpt x v) ⁻¹' AV v) ∩ ⋂ v ∉ S, (fun x : adelicCone QC => adV x.1 v) ⁻¹' {z | PrimV v z}) := by
    ext x; simp [coneBox]
  rw [this]
  refine (MeasurableSet.iInter fun w => measurable_coneRpt w (hAR w)).inter
    ((MeasurableSet.biInter S.countable_toSet fun v _ => measurable_coneVpt v (hAV v)).inter
      (MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ =>
        ((continuous_adV v).measurable.comp measurable_subtype_coe) (measurableSet_primVec v)))

/-- The unit cube in $\mathbb R^k$. -/
def W₀ (k : ℕ) : Set (Fin k → ℝ) := Set.pi univ fun _ => Icc 0 1

theorem measurableSet_W₀ : MeasurableSet (W₀ k) := MeasurableSet.univ_pi fun _ => measurableSet_Icc

theorem volume_W₀ : volume (W₀ k) = 1 := by
  rw [W₀, volume_pi_pi]; simp

include hQ' in
theorem exists_V₀ (w : {w : InfinitePlace F // w.IsReal}) :
    ∃ V : Set (ArchSO (QRe Q₀' w)), MeasurableSet V ∧ lerayMeasure (QRe Q₀' w) (gramDetR_QRe' hQ' w) V ≠ 0 ∧
      lerayMeasure (QRe Q₀' w) (gramDetR_QRe' hQ' w) V ≠ ⊤ := by
  have := isHaarMeasure_lerayMeasure (gramDetR_QRe' hQ' w)
  exact OrbitSection.exists_pos_lt_top _ (NeZero.ne _)

/-- An auxiliary set $V_w\subseteq SO(Q'_w)(\mathbb R)$ of positive finite measure. -/
def V₀ (w : {w : InfinitePlace F // w.IsReal}) : Set (ArchSO (QRe Q₀' w)) := (exists_V₀ hQ' w).choose

theorem V₀_spec (w : {w : InfinitePlace F // w.IsReal}) :
    MeasurableSet (V₀ hQ' w) ∧ lerayMeasure (QRe Q₀' w) (gramDetR_QRe' hQ' w) (V₀ hQ' w) ≠ 0 ∧
      lerayMeasure (QRe Q₀' w) (gramDetR_QRe' hQ' w) (V₀ hQ' w) ≠ ⊤ :=
  (exists_V₀ hQ' w).choose_spec

/-- The local auxiliary box $B_w = n(W_0)\,\mathrm{diag}(1,1,V_w)\subseteq P_w$. -/
def BR (w : {w : InfinitePlace F // w.IsReal}) : Set (PR Q₀' hc w) :=
  ConeReal.pElem (cRe_ne hc w) (gramDetR_QRe' hQ' w) '' (W₀ k ×ˢ V₀ hQ' w)

/-- The adelic auxiliary box $B = n(W)\,\mathrm{diag}(1,1,V)\subseteq P$, $W = W_0^{\mathrm{real}}\times\hat{\mathcal O}^k$,
$V = \prod_wV_w\times SO(\hat L')$. -/
def Wbox (k : ℕ) : Set (AdeleSpace F (Fin k)) := {y | (∀ w, adR y w ∈ W₀ k) ∧ ∀ v, IntVec v (adV y v)}

def Vbox : Set (SOAdele Q₀') := {h | (∀ w, h.1.1 w ∈ V₀ hQ' w) ∧ h.2 ∈ KSO Q₀'}

def Bbox : Set (Pc c₀ Q₀') := decompEquiv hc hQ' '' (Wbox k ×ˢ Vbox hQ')

include hc in
theorem eventually_good_cone :
    ∀ᶠ v in Filter.cofinite, (Dc hc hQ' hk).GoodV v ∧ Valued.v (cAt c₀ (σV v) * 2) = 1 :=
  ((Dc hc hQ' hk).eventually_goodV).and (eventually_two_c hc)

/-- **The bad places**: those where the section or $n(\cdot)$ fails to be integral. -/
def badCone : Finset (HeightOneSpectrum (𝓞 F)) :=
  (Filter.eventually_cofinite.mp (eventually_good_cone hc hQ' hk)).toFinset

theorem good_of_not_mem_badCone {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ badCone hc hQ' hk) :
    (Dc hc hQ' hk).GoodV v ∧ Valued.v (cAt c₀ (σV v) * 2) = 1 := by
  by_contra h
  exact hv ((Set.Finite.mem_toFinset _).mpr h)

end Box

/-! ### The inverse of the coordinate image of a product set -/

section Coord

theorem eAd_eq : (Dc hc hQ' hk).eAd = eA F k := rfl

/-- The point $x = ge$ of the adelic cone. -/
def ptOf (g : SOAdele QC) : adelicCone QC := ⟨g • eA F k, smul_mem_adelicCone QC g (Dc hc hQ' hk).eAd_mem⟩

/-- The fibre element $p = g^{-1}s(ge)\in P$. -/
def fibOf (g : SOAdele QC) : Pc c₀ Q₀' :=
  ⟨g⁻¹ * (Dc hc hQ' hk).secA (ptOf hc hQ' hk g), by
    show (g⁻¹ * (Dc hc hQ' hk).secA (ptOf hc hQ' hk g)) • eA F k = eA F k
    rw [mul_smul, show (Dc hc hQ' hk).secA (ptOf hc hQ' hk g) • eA F k = g • eA F k from
      (Dc hc hQ' hk).secA_smul _, inv_smul_smul]⟩

theorem coneCoord_symm_inv (g : SOAdele QC) :
    (coneCoord hc hQ' hk).symm g⁻¹ = (ptOf hc hQ' hk g, fibOf hc hQ' hk g) := by
  apply (coneCoord hc hQ' hk).injective
  rw [MeasurableEquiv.apply_symm_apply, coneCoord_apply]
  simp [fibOf]

theorem matR_fibOf (g : SOAdele QC) (w : {w : InfinitePlace F // w.IsReal}) :
    matR QC (fibOf hc hQ' hk g : SOAdele QC) w =
      matR QC g⁻¹ w * (Dc hc hQ' hk).secM (σR w) (matR QC g w *ᵥ eV) := by
  show matR QC (g⁻¹ * (Dc hc hQ' hk).secA (ptOf hc hQ' hk g)) w = _
  rw [matR_mul, ConeSecData.matR_secA]
  congr 2
  show adR (g • eA F k) w = _
  rw [smul_apply_fst_fst, adR_eA]

theorem matV_fibOf (g : SOAdele QC) (v : HeightOneSpectrum (𝓞 F)) :
    matV QC (fibOf hc hQ' hk g : SOAdele QC) v =
      matV QC g⁻¹ v * (Dc hc hQ' hk).secM (σV v) (matV QC g v *ᵥ eV) := by
  show matV QC (g⁻¹ * (Dc hc hQ' hk).secA (ptOf hc hQ' hk g)) v = _
  rw [matV_mul, ConeSecData.matV_secA]
  congr 2
  show adV (g • eA F k) v = _
  rw [smul_apply_snd, adV_eA]

end Coord


/-! ### Membership, place by place -/

section Members

/-- The matrix $M_w$ of the fibre element at a real place. -/
abbrev fibMatR (g : SOAdele QC) (w : {w : InfinitePlace F // w.IsReal}) : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) ℝ :=
  matR QC (fibOf hc hQ' hk g : SOAdele QC) w

/-- The matrix $M_v$ of the fibre element at a finite place. -/
abbrev fibMatV (g : SOAdele QC) (v : HeightOneSpectrum (𝓞 F)) :
    Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) (v.adicCompletion F) :=
  matV QC (fibOf hc hQ' hk g : SOAdele QC) v

/-- The local box condition at a real place. -/
def condR (g : SOAdele QC) (w : {w : InfinitePlace F // w.IsReal}) : Prop :=
  tl (fibMatR hc hQ' hk g w *ᵥ e₀) ∈ W₀ k ∧ ∃ h ∈ V₀ hQ' w, mM (ArchSOInst.mat _ h) =
    nM (ConeAdelic.cRe c₀ w) (QRe Q₀' w) (-tl (fibMatR hc hQ' hk g w *ᵥ e₀)) * fibMatR hc hQ' hk g w

/-- The local box condition at a finite place. -/
def condV (g : SOAdele QC) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  IntVec v (tl (fibMatV hc hQ' hk g v *ᵥ e₀)) ∧ ∃ h ∈ (soStabSO v Q₀' : Set (SOv v Q₀')),
    mM (ConeFinite.mat v Q₀' h) = nM (cAt c₀ (σV v)) (QAt Q₀' (σV v)) (-tl (fibMatV hc hQ' hk g v *ᵥ e₀)) *
      fibMatV hc hQ' hk g v

theorem castR_smul_eCone (g : SOAdele QC) (w : {w : InfinitePlace F // w.IsReal}) :
    castR w (g.1.1 w) • ConeReal.eCone (cRe_ne hc w) = coneRpt (ptOf hc hQ' hk g) w := by
  apply Subtype.ext
  rw [ConeReal.coe_smul_cone, mat_castR]
  show matR QC g w *ᵥ eV = adR (g • eA F k) w
  rw [smul_apply_fst_fst, adR_eA]

theorem coe_fibR_inv (w : {w : InfinitePlace F // w.IsReal}) (x : ArchSO (Qw c₀ Q₀' w)) :
    (((fibR hc hQ' hk w x)⁻¹ : PR Q₀' hc w) : ArchSO (Qw c₀ Q₀' w)) =
      x⁻¹ * secR hc hQ' hk w (x • ConeReal.eCone (cRe_ne hc w)) := by
  rw [Subgroup.coe_inv]
  show ((secR hc hQ' hk w (x • ConeReal.eCone (cRe_ne hc w)))⁻¹ * x)⁻¹ = _
  group

theorem mat_fibR_inv (g : SOAdele QC) (w : {w : InfinitePlace F // w.IsReal}) :
    ArchSOInst.mat _ (((fibR hc hQ' hk w (castR w (g.1.1 w)))⁻¹ : PR Q₀' hc w) : ArchSO (Qw c₀ Q₀' w)) =
      fibMatR hc hQ' hk g w := by
  rw [coe_fibR_inv hc hQ' hk w, ArchSOInst.mat_mul, mat_secR, castR_smul_eCone hc hQ' hk g w, fibMatR,
    matR_fibOf]
  refine congrArg₂ (· * ·) rfl ?_
  show (Dc hc hQ' hk).secM (σR w) (adR (g • eA F k) w) = _
  rw [smul_apply_fst_fst, adR_eA]

theorem mem_ER_iff (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w)))
    (g : SOAdele QC) (w : {w : InfinitePlace F // w.IsReal}) :
    castR w (g.1.1 w) ∈ ofCoordR hc hQ' hk w '' (AR w ×ˢ ((fun p => p⁻¹) ⁻¹' BR hc hQ' w)) ↔
      coneRpt (ptOf hc hQ' hk g) w ∈ AR w ∧ condR hc hQ' hk g w := by
  rw [mem_ofCoordR_image hc hQ' hk w, castR_smul_eCone hc hQ' hk g w]
  refine and_congr Iff.rfl ?_
  show (fibR hc hQ' hk w (castR w (g.1.1 w)))⁻¹ ∈ BR hc hQ' w ↔ _
  have key := mem_pElem_image_iff hc hQ' hk w (W := W₀ k) (V := V₀ hQ' w)
    ((fibR hc hQ' hk w (castR w (g.1.1 w)))⁻¹)
  have hm := mat_fibR_inv hc hQ' hk g w
  exact key.trans (by rw [show ArchSOInst.mat _ ((((fibR hc hQ' hk w (castR w (g.1.1 w)))⁻¹ :
      (orbR hc hQ' hk w).stab)) : ArchSO (Qw c₀ Q₀' w)) = fibMatR hc hQ' hk g w from hm]; rfl)

theorem mat_fibV_inv (g : SOAdele QC) (v : HeightOneSpectrum (𝓞 F)) :
    ConeFinite.mat v QC (((fibV hc hQ' hk v (evalSO QC v g.2))⁻¹ :
      (ConeFinite.coneOrbitSectionV v c₀ Q₀' hc hQ' (oneLe hk)).stab) : SOv v QC) = fibMatV hc hQ' hk g v := by
  rw [fibMatV, matV_fibOf]
  show ConeFinite.mat v QC ((secV hc hQ' hk v (evalSO QC v g.2 • ConeFinite.eConeV v c₀ Q₀'))⁻¹ * evalSO QC v g.2)⁻¹ = _
  rw [_root_.mul_inv_rev, inv_inv, ConeFinite.mat_mul, mat_secV]
  rfl

theorem evalSO_smul_eConeV (g : SOAdele QC) (v : HeightOneSpectrum (𝓞 F)) :
    evalSO QC v g.2 • ConeFinite.eConeV v c₀ Q₀' = coneVpt (ptOf hc hQ' hk g) v := by
  apply Subtype.ext
  rw [ConeFinite.coe_smul_coneV]
  show matV QC g v *ᵥ eV = adV (g • eA F k) v
  rw [smul_apply_snd, adV_eA]

theorem mem_ofCoordV_iff (v : HeightOneSpectrum (𝓞 F)) {A : Set (ConeFinite.ConeTV v QC)} (g : SOAdele QC) :
    evalSO QC v g.2 ∈ ofCoordV hc hQ' hk v '' (A ×ˢ BfinV hc hQ' hk v) ↔
      coneVpt (ptOf hc hQ' hk g) v ∈ A ∧ condV hc hQ' hk g v := by
  rw [mem_ofCoordV_image hc hQ' hk v, evalSO_smul_eConeV hc hQ' hk g v]
  refine and_congr Iff.rfl ?_
  rw [← inv_preimage_BfinV hc hQ' hk v, mem_preimage, mem_BfinV_iff hc hQ' hk v, mat_fibV_inv hc hQ' hk g v]
  rfl

open Classical in
theorem mem_EV_iff (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S)
    (AV : ∀ v, Set (ConeFinite.ConeTV v QC)) (g : SOAdele QC) (v : HeightOneSpectrum (𝓞 F)) :
    evalSO QC v g.2 ∈ (if v ∈ S then ofCoordV hc hQ' hk v '' (AV v ×ˢ BfinV hc hQ' hk v)
        else (soStabSO v QC : Set (SOv v QC))) ↔
      ((v ∈ S → coneVpt (ptOf hc hQ' hk g) v ∈ AV v) ∧ (v ∉ S → PrimV v (adV (ptOf hc hQ' hk g).1 v))) ∧
        condV hc hQ' hk g v := by
  by_cases hv : v ∈ S
  · rw [if_pos hv, mem_ofCoordV_iff hc hQ' hk v]
    simp [hv]
  · rw [if_neg hv]
    have hg := good_of_not_mem_badCone hc hQ' hk (fun h => hv (hS h))
    rw [← ofCoordV_image_good hc hQ' hk v hg.1 hg.2, mem_ofCoordV_iff hc hQ' hk v]
    simp only [hv, false_imp_iff, true_and, not_false_eq_true, true_implies]
    rfl

/-- The Levi component at a real place lies in $V_w$ iff the local box condition holds. -/
theorem leviR_mem_iff (p : Pc c₀ Q₀') (w : {w : InfinitePlace F // w.IsReal}) :
    (leviOf hc hQ' p).1.1 w ∈ V₀ hQ' w ↔ ∃ h ∈ V₀ hQ' w, mM (ArchSOInst.mat _ h) =
      nM (ConeAdelic.cRe c₀ w) (QRe Q₀' w) (-tl (matR QC (p : SOAdele QC) w *ᵥ e₀)) * matR QC (p : SOAdele QC) w := by
  have he : mM (ArchSOInst.mat _ ((leviOf hc hQ' p).1.1 w)) =
      nM (ConeAdelic.cRe c₀ w) (QRe Q₀' w) (-tl (matR QC (p : SOAdele QC) w *ᵥ e₀)) * matR QC (p : SOAdele QC) w :=
    mM_leviAt hc hQ' (σR w) _ (isSOAt_R (p : SOAdele QC) w) (heR p w)
  constructor
  · intro h; exact ⟨_, h, he⟩
  · rintro ⟨h, hh, e⟩
    have : h = (leviOf hc hQ' p).1.1 w := by
      apply Subtype.ext; apply Units.ext
      exact mM_injective (e.trans he.symm)
    rw [← this]; exact hh

/-- The Levi component at a finite place lies in $SO(L'_v)$ iff the local box condition holds. -/
theorem leviV_mem_iff (p : Pc c₀ Q₀') (v : HeightOneSpectrum (𝓞 F)) :
    evalSO Q₀' v (leviOf hc hQ' p).2 ∈ (soStabSO v Q₀' : Set (SOv v Q₀')) ↔
      ∃ h ∈ (soStabSO v Q₀' : Set (SOv v Q₀')), mM (ConeFinite.mat v Q₀' h) =
        nM (cAt c₀ (σV v)) (QAt Q₀' (σV v)) (-tl (matV QC (p : SOAdele QC) v *ᵥ e₀)) * matV QC (p : SOAdele QC) v := by
  have he : mM (ConeFinite.mat v Q₀' (evalSO Q₀' v (leviOf hc hQ' p).2)) =
      nM (cAt c₀ (σV v)) (QAt Q₀' (σV v)) (-tl (matV QC (p : SOAdele QC) v *ᵥ e₀)) * matV QC (p : SOAdele QC) v :=
    mM_leviAt hc hQ' (σV v) _ (isSOAt_V (p : SOAdele QC) v) (heV p v)
  constructor
  · intro h; exact ⟨_, h, he⟩
  · rintro ⟨h, hh, e⟩
    have : h = evalSO Q₀' v (leviOf hc hQ' p).2 :=
      ConeFinite.mat_injective v Q₀' (mM_injective (e.trans he.symm))
    rw [← this]; exact hh

/-- **The fibre element lies in the auxiliary box** iff all the local box conditions hold. -/
theorem fibOf_mem_Bbox_iff (g : SOAdele QC) :
    fibOf hc hQ' hk g ∈ Bbox hc hQ' ↔ (∀ w, condR hc hQ' hk g w) ∧ ∀ v, condV hc hQ' hk g v := by
  rw [Bbox, MeasurableEquiv.image_eq_preimage_symm, mem_preimage, decompEquiv_symm, mem_prod]
  simp only [Wbox, Vbox, mem_setOf_eq, mem_KSO_iff, adR_wOf, adV_wOf, leviR_mem_iff, leviV_mem_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨fun w => ⟨h1 w, h3 w⟩, fun v => ⟨h2 v, h4 v⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun w => (h1 w).1, fun v => (h2 v).1⟩, fun w => (h1 w).2, fun v => (h2 v).2⟩

end Members


/-! ### The set identity and the measure of a product set -/

section Measure

open Classical in
/-- The local sets at the finite places. -/
def EVset (S : Finset (HeightOneSpectrum (𝓞 F))) (AV : ∀ v, Set (ConeFinite.ConeTV v QC))
    (v : HeightOneSpectrum (𝓞 F)) : Set (SOv v QC) :=
  if v ∈ S then ofCoordV hc hQ' hk v '' (AV v ×ˢ BfinV hc hQ' hk v) else (soStabSO v QC : Set (SOv v QC))

/-- The local sets at the real places. -/
def ERset (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w)))
    (w : {w : InfinitePlace F // w.IsReal}) : Set (ArchSO (QRe QC w)) :=
  castR w ⁻¹' (ofCoordR hc hQ' hk w '' (AR w ×ˢ ((fun p => p⁻¹) ⁻¹' BR hc hQ' w)))

/-- **The inverse of the coordinate image of a product set is a box of $SO(V)(\mathbb A)$.** -/
theorem inv_coord_box_eq (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w)))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S) (AV : ∀ v, Set (ConeFinite.ConeTV v QC)) :
    (fun g => g⁻¹) ⁻¹' ((coneCoord hc hQ' hk).symm ⁻¹' (coneBox AR S AV ×ˢ Bbox hc hQ')) =
      {g : SOAdele QC | (∀ w, g.1.1 w ∈ ERset hc hQ' hk AR w) ∧
        g.2 ∈ {gf : SOAf QC | ∀ v, evalSO QC v gf ∈ EVset hc hQ' hk S AV v}} := by
  ext g
  simp only [mem_preimage, coneCoord_symm_inv, mem_prod, mem_setOf_eq, fibOf_mem_Bbox_iff, ERset, EVset]
  simp only [mem_EV_iff hc hQ' hk S hS AV g]
  simp only [mem_preimage, mem_ER_iff hc hQ' hk AR g]
  simp only [coneBox, mem_setOf_eq]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
    exact ⟨fun w => ⟨h1 w, h4 w⟩, fun v => ⟨⟨h2 v, h3 v⟩, h5 v⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun w => (h1 w).1, fun v => (h2 v).1.1, fun v => (h2 v).1.2⟩, fun w => (h1 w).2, fun v => (h2 v).2⟩

theorem measurable_fibR (w : {w : InfinitePlace F // w.IsReal}) : Measurable (fibR hc hQ' hk w) := by
  have hsm : Measurable fun g : ArchSO (Qw c₀ Q₀' w) => g • ConeReal.eCone (cRe_ne hc w) :=
    ((ConeReal.continuous_smul_cone _).comp (continuous_id.prodMk continuous_const)).measurable
  exact Measurable.subtype_mk (((measurable_secR hc hQ' hk w).comp hsm).inv.mul measurable_id)

theorem measurableSet_ofCoordR_image (w : {w : InfinitePlace F // w.IsReal})
    {A : Set (ConeReal.ConeT (Qw c₀ Q₀' w))} (hA : MeasurableSet A) {B : Set (PR Q₀' hc w)} (hB : MeasurableSet B) :
    MeasurableSet (ofCoordR hc hQ' hk w '' (A ×ˢ B)) := by
  have hsm : Measurable fun g : ArchSO (Qw c₀ Q₀' w) => g • ConeReal.eCone (cRe_ne hc w) :=
    ((ConeReal.continuous_smul_cone _).comp (continuous_id.prodMk continuous_const)).measurable
  have : ofCoordR hc hQ' hk w '' (A ×ˢ B) = (fun g => g • ConeReal.eCone (cRe_ne hc w)) ⁻¹' A ∩
      fibR hc hQ' hk w ⁻¹' B := by
    ext g; rw [mem_ofCoordR_image]; rfl
  rw [this]
  exact (hsm hA).inter (measurable_fibR hc hQ' hk w hB)

theorem measurableSet_BR (w : {w : InfinitePlace F // w.IsReal}) : MeasurableSet (BR hc hQ' w) :=
  (ConeReal.measurableEmbedding_pElem (cRe_ne hc w) (gramDetR_QRe' hQ' w)).measurableSet_image.mpr
    (measurableSet_W₀.prod (V₀_spec hQ' w).1)

theorem measurableSet_EVset (S : Finset (HeightOneSpectrum (𝓞 F))) {AV : ∀ v, Set (ConeFinite.ConeTV v QC)}
    (hAV : ∀ v, MeasurableSet (AV v)) (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (EVset hc hQ' hk S AV v) := by
  unfold EVset
  split_ifs
  · exact measurableSet_ofCoordV_image hc hQ' hk v (hAV v) (measurableSet_BfinV hc hQ' hk v)
  · exact (isOpen_soStabSO v QC).measurableSet

theorem finBoxSet_eq (S : Finset (HeightOneSpectrum (𝓞 F))) (AV : ∀ v, Set (ConeFinite.ConeTV v QC)) :
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

open Classical in
/-- **The measure of a product set, first form**: $\sigma_C(A)\,\mu_P(B) = c_F(n)\prod_w\mu_w(E_w)\cdot\mu_f(\prod_vE_v)$. -/
theorem coneMeasure_coneBox_mul_aux [IsEmpty {w : InfinitePlace F // w.IsComplex}]
    {AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w))} (hAR : ∀ w, MeasurableSet (AR w))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S) {AV : ∀ v, Set (ConeFinite.ConeTV v QC)}
    (hAV : ∀ v, MeasurableSet (AV v)) :
    coneMeasure hc hQ' hk (coneBox AR S AV) * coneMuP hc hQ' (Bbox hc hQ') =
      ENNReal.ofReal (cF F (k + 1 + 1)) *
        (∏ w, lerayMeasure (Qw c₀ Q₀' w) (ConeReal.gramDetR_cone (cRe_ne hc w) (gramDetR_QRe' hQ' w))
          (ofCoordR hc hQ' hk w '' (AR w ×ˢ ((fun p => p⁻¹) ⁻¹' BR hc hQ' w)))) *
        Measure.muFin QC (fun _ => 1) (boxSO QC S (EVset hc hQ' hk S AV)) := by
  have hA := measurableSet_coneBox hAR S hAV
  have hB : MeasurableSet (Bbox hc hQ') :=
    (decompEquiv hc hQ').measurableEmbedding.measurableSet_image.mpr
      ((show MeasurableSet (Wbox (F := F) k) from by
        have : Wbox (F := F) k = (⋂ w, (fun y : AdeleSpace F (Fin k) => adR y w) ⁻¹' W₀ k) ∩
            ⋂ v, (fun y : AdeleSpace F (Fin k) => adV y v) ⁻¹' {z | IntVec v z} := by
          ext y; simp [Wbox]
        rw [this]
        exact (MeasurableSet.iInter fun w => (continuous_adR w).measurable measurableSet_W₀).inter
          (MeasurableSet.iInter fun v => (continuous_adV v).measurable (measurableSet_intVec v))).prod
       (show MeasurableSet (Vbox hQ') from by
        have : Vbox hQ' = (⋂ w, (fun h : SOAdele Q₀' => h.1.1 w) ⁻¹' V₀ hQ' w) ∩
            (fun h : SOAdele Q₀' => h.2) ⁻¹' (KSO Q₀' : Set (SOAf Q₀')) := by
          ext h; simp [Vbox]
        rw [this]
        exact (MeasurableSet.iInter fun w => ((measurable_pi_apply w).comp (measurable_fst.comp measurable_fst))
          (V₀_spec hQ' w).1).inter (measurable_snd (isOpen_KSO Q₀').measurableSet)))
  have hpre : MeasurableSet ((coneCoord hc hQ' hk).symm ⁻¹' (coneBox AR S AV ×ˢ Bbox hc hQ')) :=
    (coneCoord hc hQ' hk).symm.measurable (hA.prod hB)
  rw [← coneMeasure_mul hc hQ' hk hA hB]
  change muTam QC (nondeg_QC hc hQ') (fun _ => 1) _ = _
  rw [← muTam_inv_preimage QC (nondeg_QC hc hQ') (by omega) _ hpre, inv_coord_box_eq hc hQ' hk AR S hS AV,
    AdelicSphereSetup.muTam_prodSet, finBoxSet_eq]
  congr 2
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [ERset, ← Measure.map_apply (measurable_castR w)
    (measurableSet_ofCoordR_image hc hQ' hk w (hAR w) (measurable_inv (measurableSet_BR hc hQ' w))),
    map_castR hc hQ' w]

end Measure


/-! ### The local evaluations and the normalized box formula -/

section Formula

/-- The real constant $|2c_w|^{-(2k+2)}$. -/
abbrev cRw (c₀ : 𝓞 F) (k : ℕ) (w : {w : InfinitePlace F // w.IsReal}) : ℝ :=
  (|2 * ConeAdelic.cRe c₀ w| ^ (2 * k + 2))⁻¹

/-- The finite constant $|2c_0|_v^{-(2k+2)}$. -/
abbrev cVv (c₀ : 𝓞 F) (k : ℕ) (v : HeightOneSpectrum (𝓞 F)) : ℝ := (absTwoM v c₀ ^ (2 * k + 2))⁻¹

theorem lerayMeasure_ERset (w : {w : InfinitePlace F // w.IsReal})
    {A : Set (ConeReal.ConeT (Qw c₀ Q₀' w))} (hA : MeasurableSet A) :
    lerayMeasure (Qw c₀ Q₀' w) (ConeReal.gramDetR_cone (cRe_ne hc w) (gramDetR_QRe' hQ' w))
        (ofCoordR hc hQ' hk w '' (A ×ˢ ((fun p => p⁻¹) ⁻¹' BR hc hQ' w))) =
      ENNReal.ofReal (cRw c₀ k w) * ConeReal.sigCone (cRe_ne hc w) A *
        (volume (W₀ k) * lerayMeasure (QRe Q₀' w) (gramDetR_QRe' hQ' w) (V₀ hQ' w)) := by
  rw [lerayMeasure_ofCoordR_image hc hQ' hk w hA (measurable_inv (measurableSet_BR hc hQ' w))]
  congr 1
  have h1 := muP_inv_preimage hc hQ' hk w (B := BR hc hQ' w) (measurableSet_BR hc hQ' w)
  have h2 := muP_pElem_image hc hQ' w (W := W₀ k) measurableSet_W₀ (V₀_spec hQ' w).1
  exact h1.trans h2

theorem muLocSO_EVset (S : Finset (HeightOneSpectrum (𝓞 F))) {AV : ∀ v, Set (ConeFinite.ConeTV v QC)}
    (hAV : ∀ v, MeasurableSet (AV v)) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    muLocSO v QC 1 (EVset hc hQ' hk S AV v) =
      ENNReal.ofReal (cVv c₀ k v) * ConeFinite.sigConeV v QC (ConeFinite.nondeg_cone c₀ Q₀' hc hQ') (AV v) *
        muLocSO v Q₀' 1 (soStabSO v Q₀' : Set (SOv v Q₀')) := by
  rw [EVset, if_pos hv, muLocSO_ofCoordV_image hc hQ' hk v (hAV v) (measurableSet_BfinV hc hQ' hk v),
    muPV_BfinV hc hQ' hk v]

/-- The mixed-space unit box $\{m : m_w\in[0,1]\}$. -/
def mBox (F : Type) [Field F] [NumberField F] : Set (NumberField.mixedEmbedding.mixedSpace F) :=
  {m | ∀ w, m.1 w ∈ Icc 0 1}

theorem selfDualInf_mBox_ne_top [IsEmpty {w : InfinitePlace F // w.IsComplex}] : Analysis.selfDualInf (F := F) (mBox F) ≠ ⊤ := by
  have hcpt : IsCompact (mBox F) := by
    have : mBox F = (Set.pi univ fun _ => Icc (0 : ℝ) 1) ×ˢ (univ : Set ({w : InfinitePlace F // w.IsComplex} → ℂ)) := by
      ext m
      constructor
      · intro h; exact ⟨fun w _ => h w, mem_univ _⟩
      · rintro ⟨h, -⟩ w; exact h w (mem_univ w)
    rw [this]
    have hu : (univ : Set ({w : InfinitePlace F // w.IsComplex} → ℂ)) = {0} := by
      ext x; simp only [mem_univ, mem_singleton_iff, true_iff]; exact Subsingleton.elim _ _
    rw [hu]
    exact (isCompact_univ_pi fun _ => isCompact_Icc).prod isCompact_singleton
  exact hcpt.measure_lt_top.ne

theorem selfDualInf_mBox_ne_zero : Analysis.selfDualInf (F := F) (mBox F) ≠ 0 := by
  set Uo : Set (NumberField.mixedEmbedding.mixedSpace F) :=
    (Set.pi (univ : Set {w : InfinitePlace F // w.IsReal}) fun _ => Ioo (0 : ℝ) 1) ×ˢ
      (univ : Set ({w : InfinitePlace F // w.IsComplex} → ℂ)) with hUo
  have hopen : IsOpen Uo :=
    (isOpen_set_pi (i := (univ : Set {w : InfinitePlace F // w.IsReal})) (s := fun _ => Ioo (0 : ℝ) 1)
      finite_univ fun _ _ => isOpen_Ioo).prod isOpen_univ
  have hne : Uo.Nonempty :=
    ⟨((fun _ => (1 / 2 : ℝ)), (0 : {w : InfinitePlace F // w.IsComplex} → ℂ)),
      fun w _ => ⟨by norm_num, by norm_num⟩, mem_univ _⟩
  refine (measure_pos_of_superset ?_ (hopen.measure_ne_zero _ hne)).ne'
  intro m hm
  exact fun w => Ioo_subset_Icc_self (hm.1 w (mem_univ w))

theorem Wbox_eq : Wbox (F := F) k = boxSet (Set.pi univ fun _ => mBox F) OHatVec := by
  ext y
  simp only [Wbox, mem_setOf_eq, mem_boxSet, Set.mem_pi, mem_univ, true_implies, mBox, W₀, OHatVec,
    OHat, IntVec]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i w => h1 w i, fun i v => ?_⟩
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (h2 v i)
  · rintro ⟨h1, h2⟩
    exact ⟨fun w i => h1 i w, fun v i => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h2 i v)⟩

theorem muAddVec_Wbox_ne_zero : muAddVec F (Fin k) (Wbox (F := F) k) ≠ 0 := by
  rw [Wbox_eq, muAddVec_boxSet, Measure.pi_pi]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun _ _ => selfDualInf_mBox_ne_zero) muFinVec_OHatVec_ne_zero

theorem muAddVec_Wbox_ne_top [IsEmpty {w : InfinitePlace F // w.IsComplex}] : muAddVec F (Fin k) (Wbox (F := F) k) ≠ ⊤ := by
  rw [Wbox_eq, muAddVec_boxSet, Measure.pi_pi]
  exact ENNReal.mul_ne_top (ENNReal.prod_ne_top fun _ _ => selfDualInf_mBox_ne_top) muFinVec_OHatVec_ne_top

end Formula


/-! ### The normalized box formula -/

section Normalized

variable [IsEmpty {w : InfinitePlace F // w.IsComplex}]

open Classical in
theorem coneMuP_Bbox : coneMuP hc hQ' (Bbox hc hQ') = muAddVec F (Fin k) (Wbox (F := F) k) *
    (ENNReal.ofReal (cF F k) * (∏ w, lerayMeasure (QRe Q₀' w) (gramDetR_QRe' hQ' w) (V₀ hQ' w)) *
      ENNReal.ofReal (finFactor Q₀' (fun _ => 1))) := by
  rw [coneMuP, Bbox, MeasurableEquiv.map_apply, MeasurableEquiv.preimage_image, Measure.prod_prod,
    dwTam_eq_muAddVec]
  congr 1
  have : Vbox hQ' = {h : SOAdele Q₀' | (∀ w, h.1.1 w ∈ V₀ hQ' w) ∧ h.2 ∈ (KSO Q₀' : Set (SOAf Q₀'))} := rfl
  rw [this]
  change muTam Q₀' hQ' (fun _ => 1) _ = _
  rw [AdelicSphereSetup.muTam_prodSet, muFin_KSO]

theorem coneMuP_Bbox_ne_zero (hk : 3 ≤ k) : coneMuP hc hQ' (Bbox hc hQ') ≠ 0 := by
  classical
  rw [coneMuP_Bbox]
  refine mul_ne_zero muAddVec_Wbox_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_)
  · exact (ENNReal.ofReal_pos.mpr cF_pos').ne'
  · exact Finset.prod_ne_zero_iff.mpr fun w _ => (V₀_spec hQ' w).2.1
  · rw [ne_eq, ENNReal.ofReal_eq_zero, not_le, finFactor_one Q₀' hQ']
    exact tprod_siegelDensity_pos hk Q₀' hQ'

theorem coneMuP_Bbox_ne_top : coneMuP hc hQ' (Bbox hc hQ') ≠ ⊤ := by
  classical
  rw [coneMuP_Bbox]
  exact ENNReal.mul_ne_top muAddVec_Wbox_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.prod_ne_top fun w _ => (V₀_spec hQ' w).2.2)) ENNReal.ofReal_ne_top)

open Classical in
/-- **The constant of the box formula** for a finite set $S\supseteq$ `badCone` of finite places. -/
def boxConst (S : Finset (HeightOneSpectrum (𝓞 F))) : ℝ≥0∞ :=
  ENNReal.ofReal (cF F (k + 1 + 1)) *
      (∏ w, ENNReal.ofReal (cRw c₀ k w) * (volume (W₀ k) * lerayMeasure (QRe Q₀' w) (gramDetR_QRe' hQ' w) (V₀ hQ' w))) *
      ((∏ v ∈ S, ENNReal.ofReal (cVv c₀ k v) * muLocSO v Q₀' 1 (soStabSO v Q₀' : Set (SOv v Q₀'))) *
        ENNReal.ofReal (∏' v, if v ∈ S then 1 else (muLocSO v QC 1 (soStabSO v QC : Set (SOv v QC))).toReal)) /
    coneMuP hc hQ' (Bbox hc hQ')

open Classical in
/-- **The box formula** ($F$ totally real, $k\ge3$, $S\supseteq$ `badCone`):
$$\sigma_C\Big(\{x : x_w\in A_w,\ x_v\in A_v\ (v\in S),\ x_v\ \text{primitive}\ (v\notin S)\}\Big) =
  M(S)\prod_w\sigma_{C,w}(A_w)\prod_{v\in S}\sigma_{C,v}(A_v),$$
$M(S)$ = `boxConst S` (independent of the sets $A$). -/
@[kb "weil1982" "§2.3, p. 21; §4.5, p. 108 (the cone measure on product sets) [unverified page]"]
theorem coneMeasure_coneBox
    {AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w))} (hAR : ∀ w, MeasurableSet (AR w))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S) {AV : ∀ v, Set (ConeFinite.ConeTV v QC)}
    (hAV : ∀ v, MeasurableSet (AV v)) :
    coneMeasure hc hQ' hk (coneBox AR S AV) =
      boxConst hc hQ' S * (∏ w, ConeReal.sigCone (cRe_ne hc w) (AR w)) *
        ∏ v ∈ S, ConeFinite.sigConeV v QC (ConeFinite.nondeg_cone c₀ Q₀' hc hQ') (AV v) := by
  have h := coneMeasure_coneBox_mul_aux hc hQ' hk hAR S hS hAV
  have hEV : ∀ v ∈ S, MeasurableSet (EVset hc hQ' hk S AV v) := fun v _ => measurableSet_EVset hc hQ' hk S hAV v
  have hmult := multipliable_muLocSO_one QC (nondeg_QC hc hQ') (by omega : k + 1 + 1 ≠ 0) (by omega : k + 1 + 1 ≠ 2)
  rw [muFin_boxSO_split QC (nondeg_QC hc hQ') (fun _ => one_pos) hmult S _ hEV] at h
  simp only [lerayMeasure_ERset hc hQ' hk _ (hAR _)] at h
  rw [Finset.prod_congr rfl fun v hv => muLocSO_EVset hc hQ' hk S hAV hv] at h
  have h0 := coneMuP_Bbox_ne_zero hc hQ' hk
  have ht := coneMuP_Bbox_ne_top hc hQ'
  have hσ := (ENNReal.eq_div_iff h0 ht).mpr (show coneMuP hc hQ' (Bbox hc hQ') *
      coneMeasure hc hQ' hk (coneBox AR S AV) = _ from (mul_comm _ _).trans h)
  rw [hσ, boxConst, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  simp only [Finset.prod_mul_distrib]
  ring

end Normalized

end QuadFormsKB.Tamagawa.Measure.Weil

end
