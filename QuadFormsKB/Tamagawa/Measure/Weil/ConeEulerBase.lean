import QuadFormsKB.Tamagawa.Measure.Weil.ConeAdelicFib
import QuadFormsKB.Tamagawa.Measure.ConeFiniteOrbit
import QuadFormsKB.Tamagawa.Measure.ConeRealOrbit
import QuadFormsKB.Tamagawa.Measure.ConeAdelic
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereLocalFin

/-!
# The adelic section at one place

For the cone form $Q_0 = \langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'$ ($k\ge3$) and the section data `Dc`:

* at a finite place $v$: **`secV`**, the $v$-component of the adelic section as a map $C^\circ_v\to SO(V)(F_v)$ on the
  punctured cone `ConeFinite.ConeTV`, and **`orbV`**, the orbit section `coneOrbitSectionV` with its section
  replaced by `secV` (same base point $e$, same stabilizer);
* at a real place $w$: **`secR`**, **`orbR`**, the same for the real `ConeReal.coneOrbitSection` of
  $Q_w = \langle c_w\rangle\perp\langle -c_w\rangle\perp Q'_w$, and the identification
  **`castR`** : $SO(Q_0^{\sigma_w})(\mathbb R)\simeq SO(Q_w)(\mathbb R)$ (the two forms are equal, `ConeAdelic.QRe_cone`).
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

variable {F : Type} [Field F] [NumberField F]

/-! ### Finite places -/

section Fin

variable {c₀ : 𝓞 F} {k : ℕ} {Q₀' : QuadForm (𝓞 F) k} (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) (hk : 3 ≤ k)
  (v : HeightOneSpectrum (𝓞 F))

local notation "QC" => ConeFinite.Qcone c₀ Q₀'

theorem qH_of_mem_coneSetV {z : Fin (k + 1 + 1) → v.adicCompletion F} (hz : z ∈ ConeFinite.coneSetV v QC) :
    qH (hesAt QC (σV v)) z = 0 := by
  rw [qH_hesAt_eq_two_mul]
  have h : (LocalDensity.NF.Qp v QC).evalIn (v.adicCompletion F) z = 0 := hz.1
  rw [LocalDensity.NF.evalIn_Qp] at h
  rw [h, mul_zero]

theorem eAt_coneSecData {K : Type*} [Field K] (σ : F →+* K) :
    (Dc hc hQ' hk).eAt σ = (eV : Fin (k + 1 + 1) → K) :=
  map_eV σ

/-- **The section at a finite place** $v$: the $v$-component of the adelic section, $C^\circ_v\to SO(V)(F_v)$. -/
def secV (z : ConeFinite.ConeTV v QC) : SOv v QC :=
  ⟨⟨(Dc hc hQ' hk).secGL z.1 (qH_of_mem_coneSetV v z.2) z.2.2,
    mem_orthGroup_of QC v ((Dc hc hQ' hk).isSOAt_secGL (qH_of_mem_coneSetV v z.2) z.2.2).1⟩,
    ((Dc hc hQ' hk).isSOAt_secGL (qH_of_mem_coneSetV v z.2) z.2.2).2⟩

theorem mat_secV (z : ConeFinite.ConeTV v QC) :
    ConeFinite.mat v QC (secV hc hQ' hk v z) = (Dc hc hQ' hk).secM (σV v) z.1 := rfl

theorem secV_smul (z : ConeFinite.ConeTV v QC) : secV hc hQ' hk v z • ConeFinite.eConeV v c₀ Q₀' = z := by
  apply Subtype.ext
  rw [ConeFinite.coe_smul_coneV, mat_secV]
  have h := (Dc hc hQ' hk).secGL_mulVec (σ := σV v) (qH_of_mem_coneSetV v z.2) z.2.2
  rw [eAt_coneSecData] at h
  exact h

theorem measurable_secV : Measurable (secV hc hQ' hk v) := by
  refine Measurable.subtype_mk ?_
  refine measurable_orthGroup_of v (f := fun z => ((secV hc hQ' hk v z : SOv v QC) :
    orthGroup ((ConeFinite.Qcone c₀ Q₀').map (algebraMap (𝓞 F) F)) (v.adicCompletion F))) ?_ ?_
  · exact ((Dc hc hQ' hk).measurable_secM (σV v)).comp measurable_subtype_coe
  · exact ((Dc hc hQ' hk).measurable_secMInv (σV v)).comp measurable_subtype_coe

/-- **The finite-place orbit section with our section** (same base point and stabilizer). -/
def orbV : OrbitSection (SOv v QC) (ConeFinite.ConeTV v QC) :=
  { ConeFinite.coneOrbitSectionV v c₀ Q₀' hc hQ' (by omega : 1 ≤ k) with
    sec := secV hc hQ' hk v
    sec_smul := secV_smul hc hQ' hk v
    measurable_sec := measurable_secV hc hQ' hk v }

theorem orbV_stab : (orbV hc hQ' hk v).stab = (ConeFinite.coneOrbitSectionV v c₀ Q₀' hc hQ' (by omega)).stab := rfl

end Fin

/-! ### Real places -/

section Real

variable {c₀ : 𝓞 F} {k : ℕ} {Q₀' : QuadForm (𝓞 F) k} (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) (hk : 3 ≤ k)
  (w : {w : InfinitePlace F // w.IsReal})

local notation "QC" => ConeFinite.Qcone c₀ Q₀'

/-- The cone form at the real place $w$: $\langle c_w\rangle\perp\langle -c_w\rangle\perp Q'_w$. -/
abbrev Qw (c₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) k) (w : {w : InfinitePlace F // w.IsReal}) : QuadForm ℝ (k + 1 + 1) :=
  coneForm (ConeAdelic.cRe c₀ w) (QRe Q₀' w)

theorem QRe_eq_Qw : QRe QC w = Qw c₀ Q₀' w := ConeAdelic.QRe_cone w

theorem hesAt_eq_Qw : hesAt QC (σR w) = (Qw c₀ Q₀' w).hessian := hesAt_cone c₀ Q₀' (σR w)

include hc in
theorem cRe_ne : ConeAdelic.cRe c₀ w ≠ 0 := ConeAdelic.cRe_ne_zero hc w

include hQ' in
theorem gramDetR_QRe' : Siegel.gramDetR (QRe Q₀' w) ≠ 0 := gramDetR_QRe_ne_zero Q₀' hQ' w

theorem qH_of_mem_coneSet {z : Fin (k + 1 + 1) → ℝ} (hz : z ∈ ConeReal.coneSet (Qw c₀ Q₀' w)) :
    qH (hesAt QC (σR w)) z = 0 := by
  rw [hesAt_eq_Qw]
  have h := QuadFormsKB.Siegel.Kneser.two_mul_evalIn (K := ℝ) (Qw c₀ Q₀' w) z
  rw [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at h
  rw [qH, ← h, show QuadForm.evalIn ℝ (Qw c₀ Q₀' w) z = 0 from hz.1, mul_zero]

theorem mem_soReal_Qw {g : GL (Fin (k + 1 + 1)) ℝ} (hg : IsSOAt QC (σR w) g) : g ∈ soReal (Qw c₀ Q₀' w) := by
  rw [mem_soReal_iff]
  unfold IsSOAt at hg
  rw [hesAt_eq_Qw] at hg
  exact hg

/-- **The section at a real place** $w$, $C^\circ_w\to SO(Q_w)(\mathbb R)$. -/
def secR (z : ConeReal.ConeT (Qw c₀ Q₀' w)) : ArchSO (Qw c₀ Q₀' w) :=
  ArchSOInst.mk _ ((Dc hc hQ' hk).secGL z.1 (qH_of_mem_coneSet w z.2) z.2.2)
    (mem_soReal_Qw w ((Dc hc hQ' hk).isSOAt_secGL (qH_of_mem_coneSet w z.2) z.2.2))

theorem mat_secR (z : ConeReal.ConeT (Qw c₀ Q₀' w)) :
    ArchSOInst.mat _ (secR hc hQ' hk w z) = (Dc hc hQ' hk).secM (σR w) z.1 := rfl

theorem secR_smul (z : ConeReal.ConeT (Qw c₀ Q₀' w)) :
    secR hc hQ' hk w z • ConeReal.eCone (cRe_ne hc w) = z := by
  apply Subtype.ext
  rw [ConeReal.coe_smul_cone, mat_secR]
  have h := (Dc hc hQ' hk).secGL_mulVec (σ := σR w) (qH_of_mem_coneSet w z.2) z.2.2
  rw [eAt_coneSecData] at h
  exact h

theorem measurable_secR : Measurable (secR hc hQ' hk w) := by
  refine measurable_archSO_of (f := secR hc hQ' hk w) ?_ ?_
  · exact ((Dc hc hQ' hk).measurable_secM (σR w)).comp measurable_subtype_coe
  · exact ((Dc hc hQ' hk).measurable_secMInv (σR w)).comp measurable_subtype_coe

/-- **The real orbit section at $w$ with our section** (same base point and stabilizer). -/
def orbR : OrbitSection (ArchSO (Qw c₀ Q₀' w)) (ConeReal.ConeT (Qw c₀ Q₀' w)) :=
  { ConeReal.coneOrbitSection (cRe_ne hc w) (gramDetR_QRe' hQ' w)
      (OrbitalReal.sphSection (neg_ne_zero.mpr (cRe_ne hc w)) (by omega : 1 ≤ k) (gramDetR_QRe' hQ' w)) with
    sec := secR hc hQ' hk w
    sec_smul := secR_smul hc hQ' hk w
    measurable_sec := measurable_secR hc hQ' hk w }

/-- **The identification** $SO(Q_0^{\sigma_w})(\mathbb R)\to SO(Q_w)(\mathbb R)$ (the same matrices). -/
def castR : ArchSO (QRe QC w) →* ArchSO (Qw c₀ Q₀' w) where
  toFun g := ArchSOInst.mk _ (ArchSO.incl _ g) (by
    have := AdelicSphereSetup.hes_of_mem_soReal QC (σR w) g.2
    exact mem_soReal_Qw w this)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem mat_castR (g : ArchSO (QRe QC w)) : ArchSOInst.mat _ (castR w g) = ArchSOInst.mat _ g := rfl

theorem castR_injective : Function.Injective (castR (c₀ := c₀) (Q₀' := Q₀') w) := fun g h e =>
  Subtype.ext (congrArg (fun x : ArchSO (Qw c₀ Q₀' w) => (ArchSO.incl _ x : GL (Fin (k + 1 + 1)) ℝ)) e)

theorem castR_surjective : Function.Surjective (castR (c₀ := c₀) (Q₀' := Q₀') w) := fun g =>
  ⟨ArchSOInst.mk _ (ArchSO.incl _ g) (by
    rw [mem_soReal_iff, (QRe_eq_Qw w : QRe QC w = _)]
    exact (mem_soReal_iff _ _).mp g.2), rfl⟩

end Real

end QuadFormsKB.Tamagawa.Measure.Weil

end
