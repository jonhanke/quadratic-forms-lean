import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereCoord
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereCont
import QuadFormsKB.Tamagawa.Measure.Weil.SphereLocalTransport
import QuadFormsKB.Tamagawa.Measure.LerayTransport
import QuadFormsKB.Tamagawa.Measure.FibreSO
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarLocal

/-!
# The local orbital identity at a finite place, for an arbitrary base point

For the setup of `AdelicSphere.lean` and a finite place $v$, with our local section $s_v$ (`secSO`), our embedding
$\iota_v$ (`iotaSO`) and the Leray measure $\sigma_v$ of $Q_0$ on the sphere $\{Q_0 = \rho\}$ (`sphMeasV`, `sig`):
$$\mu_v\big(s_v(A)\,\iota_v(B)\big) = c_v\,\sigma_v(A)\,\mu'_v(B)\qquad(\texttt{localFib\_fin}),$$
$c_v = |\det G|_v^{N+1}\cdot\frac{|d^{-2}|_v}{|\det(d^{-1}G)|_v}\cdot|2m_0|_v^{-k}$ (`cFin`), for measurable $A$, $B$.
*Proof.* The finite-place orbital identity for $\langle m_0\rangle\perp Q'$ at $e_0$
(`lerayMeasure_orbital_finitePlace`), moved to $Q_0$ by conjugation with $G$ (`map_muLocSO_simConjSOV`) and
$x\mapsto d^{-1}Gx$ (`sig_map_transport`), with the change of
section absorbed by left invariance (`measure_mul_image_eq`).
-/

open MeasureTheory Set Matrix
open scoped ENNReal RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.FibreDecomp QuadFormsKB.Tamagawa.Measure.FibreConst

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

/-! ### Generic helpers -/

/-- The measures `muLocSO` of equal forms correspond under the identity on matrices. -/
theorem muLocSO_congr (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} {Q Q' : QuadForm (𝓞 F) n} (h : Q = Q')
    (f : SOv v Q → SOv v Q')
    (hf : ∀ g, ((f g : orthGroup (Q'.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) : GL (Fin n) (v.adicCompletion F)) =
      ((g : orthGroup (Q.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) : GL (Fin n) (v.adicCompletion F))) :
    (muLocSO v Q 1).map f = muLocSO v Q' 1 := by
  subst h
  have : f = id := funext fun g => Subtype.ext (Subtype.ext (hf g))
  rw [this, Measure.map_id]

/-- Restricting a measure concentrated on `s` to the subtype commutes with a measurable equivalence carrying `s`
onto `t`. -/
theorem map_comap_subtype {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (ν : Measure α)
    {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : MeasurableSet t) (hν : ν sᶜ = 0) (e : α ≃ᵐ β)
    (hst : ∀ x, x ∈ s ↔ e x ∈ t) (e' : s ≃ᵐ t) (he' : ∀ x, (e' x : β) = e x) :
    (ν.comap Subtype.val).map e' = (ν.map e).comap Subtype.val := by
  ext C hC
  rw [Measure.map_apply e'.measurable hC, (MeasurableEmbedding.subtype_coe hs).comap_apply,
    (MeasurableEmbedding.subtype_coe ht).comap_apply, Measure.map_apply e.measurable
      ((MeasurableEmbedding.subtype_coe ht).measurableSet_image.mpr hC)]
  congr 1
  ext x
  simp only [mem_image, mem_preimage, Subtype.exists, exists_and_right, exists_eq_right]
  constructor
  · rintro ⟨hx, hC'⟩
    refine ⟨(hst x).mp hx, ?_⟩
    have : e' ⟨x, hx⟩ = ⟨e x, (hst x).mp hx⟩ := Subtype.ext (he' _)
    rw [← this]; exact hC'
  · rintro ⟨hx, hC'⟩
    have hx' : x ∈ s := (hst x).mpr hx
    refine ⟨hx', ?_⟩
    have : e' ⟨x, hx'⟩ = ⟨e x, hx⟩ := Subtype.ext (he' _)
    rw [this]; exact hC'

/-! ### The data at a finite place -/

variable {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F}

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

theorem evalIn_map_eq {n : ℕ} (Q : QuadForm (𝓞 F) n) {K : Type*} [Field K] [Algebra F K] [Algebra (𝓞 F) K]
    [IsScalarTower (𝓞 F) F K] (x : Fin n → K) :
    (Q.map (algebraMap (𝓞 F) F)).evalIn K x = Q.evalIn K x := by
  simp only [QuadForm.evalIn, QuadForm.map, Matrix.map_apply, ← IsScalarTower.algebraMap_apply]

theorem qH_hesAt_eq_two_mul {n : ℕ} (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F))
    (x : Fin n → v.adicCompletion F) :
    qH (hesAt Q (σV v)) x = 2 * Q.evalIn (v.adicCompletion F) x := by
  rw [← evalIn_map_eq Q x, Lattices.two_mul_evalIn]
  rfl

namespace AdelicSphereSetup

variable (S : AdelicSphereSetup Q₀ ρ) (hρ : ρ ≠ 0) (hQ : Q₀.Nondegenerate) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

variable (Q₀ ρ) in
/-- The local sphere $\{Q_0 = \rho\}$ at $v$. -/
abbrev sphV : Set (Fin (k + 1) → Fv) := FibreLeray.sphereV v Q₀ (σV v ρ)

variable (Q₀ ρ) in
theorem mem_sphV_iff (x : Fin (k + 1) → Fv) : x ∈ sphV Q₀ ρ v ↔ qH (hesAt Q₀ (σV v)) x = σV v (2 * ρ) := by
  rw [qH_hesAt_eq_two_mul, map_mul, map_ofNat]
  show Q₀.evalIn Fv x = σV v ρ ↔ _
  exact ⟨fun h => by rw [h], fun h => mul_left_cancel₀ two_ne_zero h⟩

/-- **Our section at $v$** on the local sphere. -/
def secSO (x : sphV Q₀ ρ v) : SOv v Q₀ :=
  ⟨⟨S.secFinGL hρ v x.1 ((mem_sphV_iff Q₀ ρ v x.1).mp x.2),
    mem_orthGroup_of Q₀ v (S.secFinGL_mem hρ v x.1 ((mem_sphV_iff Q₀ ρ v x.1).mp x.2)).1⟩,
    (S.secFinGL_mem hρ v x.1 ((mem_sphV_iff Q₀ ρ v x.1).mp x.2)).2⟩

/-- **Our embedding at $v$** on $SO$. -/
def iotaSO : SOv v S.C.Q' →* SOv v Q₀ :=
  ((S.iotaV v).comp (soSub (S.C.Q'.map (algebraMap (𝓞 F) F)) Fv).subtype).codRestrict
    (soSub QF Fv) fun h => by
      show ((S.iotaV v h.1 : orthGroup QF Fv) : GL (Fin (k + 1)) Fv).val.det = 1
      rw [det_iotaV]; exact h.2

theorem secSO_val (x : sphV Q₀ ρ v) :
    (((S.secSO hρ v x : SOv v Q₀) : orthGroup QF Fv) : GL (Fin (k + 1)) Fv).val =
      secP (hesAt Q₀ (σV v)) (S.sphereDataAt hρ (σV v)) (S.bFin hρ v) x.1 := rfl

theorem iotaSO_val (h : SOv v S.C.Q') :
    (((S.iotaSO v h : SOv v Q₀) : orthGroup QF Fv) : GL (Fin (k + 1)) Fv).val =
      conjBlock (S.PAt (σV v)).val ((h : orthGroup (S.C.Q'.map (algebraMap (𝓞 F) F)) Fv) : GL (Fin k) Fv).val :=
  S.iotaV_val v h.1

/-! ### The split side -/

/-- The cast between the groups of equal forms. -/
def castSO {n : ℕ} {Q Q' : QuadForm (𝓞 F) n} (h : Q = Q') : SOv v Q →* SOv v Q' := by
  subst h; exact MonoidHom.id _

theorem castSO_val {n : ℕ} {Q Q' : QuadForm (𝓞 F) n} (h : Q = Q') (g : SOv v Q) :
    ((castSO v h g : orthGroup (Q'.map (algebraMap (𝓞 F) F)) Fv) : GL (Fin n) Fv) =
      ((g : orthGroup (Q.map (algebraMap (𝓞 F) F)) Fv) : GL (Fin n) Fv) := by
  subst h; rfl

theorem continuous_castSO {n : ℕ} {Q Q' : QuadForm (𝓞 F) n} (h : Q = Q') : Continuous (castSO v h) := by
  subst h; exact continuous_id

theorem simForm_one_eq : simForm Q₀ 1 S.C.G = splitForm S.C.m₀ S.C.Q' := by
  rw [← S.C.split]
  ext i j
  simp

/-- The conjugation $g\mapsto G^{-1}gG$, $SO(Q_0)(F_v)\to SO(\langle m_0\rangle\perp Q')(F_v)$. -/
def phiV : SOv v Q₀ →* SOv v (splitForm S.C.m₀ S.C.Q') :=
  (castSO v S.simForm_one_eq).comp (simConjSOV (Q₀ := Q₀) v (one_ne_zero : (1 : 𝓞 F) ≠ 0) S.C.hG).toMonoidHom

theorem phiV_val (g : SOv v Q₀) :
    ((S.phiV v g : orthGroup ((splitForm S.C.m₀ S.C.Q').map (algebraMap (𝓞 F) F)) Fv) : GL (Fin (k + 1)) Fv) =
      (S.PAt (σV v))⁻¹ * ((g : orthGroup QF Fv) : GL (Fin (k + 1)) Fv) * S.PAt (σV v) := by
  rw [phiV, MonoidHom.comp_apply, castSO_val]
  rfl

theorem phiV_injective : Function.Injective (S.phiV v) := by
  intro g g' e
  have := congrArg (fun x : SOv v (splitForm S.C.m₀ S.C.Q') =>
    ((x : orthGroup ((splitForm S.C.m₀ S.C.Q').map (algebraMap (𝓞 F) F)) Fv) : GL (Fin (k + 1)) Fv)) e
  simp only [phiV_val, mul_left_inj, mul_right_inj] at this
  exact Subtype.ext (Subtype.ext this)

theorem continuous_phiV : Continuous (S.phiV v) :=
  (continuous_castSO v _).comp (simConjSOV (Q₀ := Q₀) v (one_ne_zero : (1 : 𝓞 F) ≠ 0) S.C.hG).continuous

include hQ in
/-- The measure ratio of the conjugation. -/
theorem map_phiV : (muLocSO v Q₀ 1).map (S.phiV v) =
    ENNReal.ofReal ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F (simJac 1 S.C.G))‖ •
      muLocSO v (splitForm S.C.m₀ S.C.Q') 1 := by
  have hc : Measurable (simConjSOV (Q₀ := Q₀) v (one_ne_zero : (1 : 𝓞 F) ≠ 0) S.C.hG) :=
    (simConjSOV (Q₀ := Q₀) v (one_ne_zero : (1 : 𝓞 F) ≠ 0) S.C.hG).continuous.measurable
  have e : ⇑(S.phiV v) = ⇑(castSO v S.simForm_one_eq) ∘
      ⇑(simConjSOV (Q₀ := Q₀) v (one_ne_zero : (1 : 𝓞 F) ≠ 0) S.C.hG) := rfl
  rw [e, ← Measure.map_map (continuous_castSO v _).measurable hc,
    map_muLocSO_simConjSOV v (by omega) hQ one_ne_zero S.C.hG, Measure.map_smul,
    muLocSO_congr v S.simForm_one_eq _ (castSO_val v S.simForm_one_eq)]
  exact (continuous_castSO v _).measurable.aemeasurable

theorem qH_mulVec_eq {K : Type*} [Field K] {n : ℕ} (H P : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    qH H (P *ᵥ x) = qH (Pᵀ * H * P) x := by
  unfold qH
  rw [dotProduct_comm (P *ᵥ x), ← dotProduct_transpose_mulVec, mulVec_mulVec, mulVec_mulVec]

theorem qH_smul {K : Type*} [Field K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (c : K) (x : Fin n → K) :
    qH H (c • x) = c ^ 2 * qH H x := by
  unfold qH
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring

theorem hesAt_splitForm {K : Type*} [Field K] (σ : F →+* K) :
    hesAt (splitForm S.C.m₀ S.C.Q') σ = cornerMat (σ (algebraMap (𝓞 F) F (2 * S.C.m₀))) (hesAt S.C.Q' σ) := by
  rw [hesAt, map_splitForm, hessian_splitForm, cornerMat_map, hesAt]
  simp only [map_mul, map_ofNat]

/-- **The change of variables $x\mapsto d^{-1}Gx$ scales the forms**: $Q_0(d^{-1}Gx) = d^{-2}\,Q_1(x)$. -/
theorem evalIn_psi (x : Fin (k + 1) → Fv) :
    Q₀.evalIn Fv (((σV v (algebraMap (𝓞 F) F S.C.d))⁻¹ • (S.PAt (σV v)).val) *ᵥ x) =
      (σV v (algebraMap (𝓞 F) F S.C.d))⁻¹ ^ 2 * (splitForm S.C.m₀ S.C.Q').evalIn Fv x := by
  have h2 : (2 : Fv) ≠ 0 := two_ne_zero
  apply mul_left_cancel₀ h2
  rw [← qH_hesAt_eq_two_mul, smul_mulVec, qH_smul, qH_mulVec_eq, S.PAt_hes, ← S.hesAt_splitForm,
    qH_hesAt_eq_two_mul]
  ring

/-- $d$ at $v$. -/
abbrev dV : Fv := σV v (algebraMap (𝓞 F) F S.C.d)

theorem dV_ne_zero : S.dV v ≠ 0 := S.d_ne_zero (σV v)

/-- The linear map $x\mapsto d^{-1}Gx$ at $v$. -/
def psiGL : GL (Fin (k + 1)) Fv :=
  ⟨(S.dV v)⁻¹ • (S.PAt (σV v)).val, S.dV v • ((S.PAt (σV v))⁻¹ : GL (Fin (k + 1)) Fv).val, by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ (S.dV_ne_zero v), ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_smul], by
    rw [smul_mul_smul_comm, mul_inv_cancel₀ (S.dV_ne_zero v), ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_smul]⟩

theorem psiGL_val : (S.psiGL v).val = (S.dV v)⁻¹ • (S.PAt (σV v)).val := rfl

/-- The scalar $d^{-2}$ as a unit. -/
def cPsi : Fvˣ := Units.mk0 ((S.dV v)⁻¹ ^ 2) (pow_ne_zero _ (inv_ne_zero (S.dV_ne_zero v)))

theorem cPsi_mul : (S.cPsi v : Fv) * algebraMap F Fv (mm S.C.m₀) = σV v ρ := by
  have hq : qF Q₀ S.ξ.1 = ρ := S.ξ.2
  have hd := S.dV_ne_zero v
  rw [cPsi, Units.val_mk0, mm, S.C.m₀_eq, hq, map_mul, map_pow]
  field_simp

theorem evalIn_psiGL (x : Fin (k + 1) → Fv) :
    Q₀.evalIn Fv ((S.psiGL v).val *ᵥ x) = (S.cPsi v : Fv) * (splitForm S.C.m₀ S.C.Q').evalIn Fv x :=
  S.evalIn_psi v x

/-- The split sphere $\{Q_1 = m_0\}$ at $v$ (`sphereSet`). -/
abbrev X1 : Set (Fin (k + 1) → Fv) := FibreO.sphereSet v (QQ S.C.m₀ S.C.Q') (mm S.C.m₀)

theorem mem_X1_iff_psi (x : Fin (k + 1) → Fv) :
    x ∈ S.X1 v ↔ (S.psiGL v).val *ᵥ x ∈ sphV Q₀ ρ v := by
  show (QQ S.C.m₀ S.C.Q').evalIn Fv x = algebraMap F Fv (mm S.C.m₀) ↔ Q₀.evalIn Fv _ = σV v ρ
  rw [evalIn_map_eq, S.evalIn_psiGL, ← S.cPsi_mul v]
  exact ⟨fun h => by rw [h], fun h => mul_left_cancel₀ (S.cPsi v).ne_zero h⟩

/-- **The sphere map** $\psi : \{Q_1 = m_0\}\to\{Q_0 = \rho\}$, $x\mapsto d^{-1}Gx$. -/
def psi : S.X1 v ≃ᵐ sphV Q₀ ρ v where
  toFun x := ⟨(S.psiGL v).val *ᵥ x.1, (S.mem_X1_iff_psi v x.1).mp x.2⟩
  invFun y := ⟨((S.psiGL v)⁻¹ : GL (Fin (k + 1)) Fv).val *ᵥ y.1, (S.mem_X1_iff_psi v _).mpr (by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]; exact y.2)⟩
  left_inv x := Subtype.ext (by
    simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec])
  right_inv y := Subtype.ext (by
    simp only [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec])
  measurable_toFun := ((continuous_const.matrix_mulVec continuous_subtype_val).subtype_mk _).measurable
  measurable_invFun := ((continuous_const.matrix_mulVec continuous_subtype_val).subtype_mk _).measurable

theorem psi_val (x : S.X1 v) : ((S.psi v x : sphV Q₀ ρ v) : Fin (k + 1) → Fv) = (S.psiGL v).val *ᵥ x.1 := rfl

variable (Q₀ ρ) in
/-- The Leray measure of $Q_0$ on the local sphere. -/
def sigV : Measure (sphV Q₀ ρ v) := (FibreLeray.sig v Q₀ hQ (σV v ρ)).comap Subtype.val

/-- The constant of $\psi$: $\Delta(d^{-2})/\Delta(\det(d^{-1}G))$. -/
def bPsi : ℝ≥0∞ := (distribHaarChar Fv (S.cPsi v) : ℝ≥0∞) /
  (distribHaarChar Fv (Matrix.GeneralLinearGroup.det (S.psiGL v)) : ℝ≥0∞)

theorem comap_smul_measure {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : MeasurableEmbedding f) (c : ℝ≥0∞) (ν : Measure β) : (c • ν).comap f = c • ν.comap f := by
  ext A hA
  rw [hf.comap_apply, Measure.smul_apply, Measure.smul_apply, hf.comap_apply]

include hQ in
/-- **$\psi_*\sigma_1 = b\,\sigma_0$** (`sig_map_transport`). -/
theorem map_psi_nuS (hm : S.C.m₀ ≠ 0) :
    (nuS v S.C.m₀ hm S.C.Q' S.C.hQ').map (S.psi v) = S.bPsi v • sigV Q₀ ρ hQ v := by
  have hQ1 : (splitForm S.C.m₀ S.C.Q').Nondegenerate := hQ0 S.C.m₀ S.C.Q' hm S.C.hQ'
  have hs : MeasurableSet (S.X1 v) := FibreLeray.measurableSet_sphereSet v _ _
  have ht' : MeasurableSet (sphV Q₀ ρ v) := (FibreLeray.isClosed_sphereV v Q₀ _).measurableSet
  have htr := LerayTransport.sig_map_transport v Q₀ (splitForm S.C.m₀ S.C.Q') hQ hQ1 (S.psiGL v) (S.cPsi v)
    (S.evalIn_psiGL v) (algebraMap F Fv (mm S.C.m₀))
  rw [S.cPsi_mul v] at htr
  have key := map_comap_subtype (FibreLeray.sig v (splitForm S.C.m₀ S.C.Q') hQ1 (algebraMap F Fv (mm S.C.m₀)))
    hs ht' (by
      have := FibreLeray.sig_sph_compl v (splitForm S.C.m₀ S.C.Q') hQ1 (algebraMap F Fv (mm S.C.m₀))
      rwa [← FibreLeray.sphereSet_eq] at this) (LerayThick.glEquiv (S.psiGL v)) (S.mem_X1_iff_psi v)
    (S.psi v) (fun x => rfl)
  rw [nuS, FibreLeray.sphereMeasure, key, LerayThick.coe_glEquiv, htr, comap_smul_measure
    (MeasurableEmbedding.subtype_coe ht'), sigV, bPsi]

/-! ### The split section and embedding -/

variable (hk : 1 ≤ k)

/-- The embedding $h\mapsto\mathrm{diag}(1, h)$ on $SO$. -/
def iota1 : SOv v S.C.Q' →* SOv v (splitForm S.C.m₀ S.C.Q') :=
  ((FibreO.iota v (QQ S.C.m₀ S.C.Q') (mm S.C.m₀) (QQ' S.C.Q') (hEE S.C.m₀ S.C.Q')).comp
    (soSub (S.C.Q'.map (algebraMap (𝓞 F) F)) Fv).subtype).codRestrict
    (soSub ((splitForm S.C.m₀ S.C.Q').map (algebraMap (𝓞 F) F)) Fv) fun h => by
      show (cornerMat 1 ((h.1 : GL (Fin k) Fv).val)).det = 1
      rw [det_cornerMat, one_mul]; exact h.2

theorem iota1_val (h : SOv v S.C.Q') :
    (((S.iota1 v h : SOv v (splitForm S.C.m₀ S.C.Q')) : orthGroup (QQ S.C.m₀ S.C.Q') Fv) : GL (Fin (k + 1)) Fv).val =
      cornerMat 1 (((h : orthGroup (QQ' S.C.Q') Fv) : GL (Fin k) Fv).val) := rfl

/-- The section, as $x\mapsto\mathrm{orb}(x, 1)$. -/
def sec1 (x : S.X1 v) : SOv v (splitForm S.C.m₀ S.C.Q') :=
  FibreSO.orbSO v S.C.m₀ S.C.hm S.C.Q' S.C.hQ' hk (x, 1)

theorem orbSO_eq_mul :
    FibreSO.orbSO v S.C.m₀ S.C.hm S.C.Q' S.C.hQ' hk = fun p => S.sec1 v hk p.1 * S.iota1 v p.2 := by
  funext p
  apply Subtype.ext
  show FibreO.orb v (QQ S.C.m₀ S.C.Q') (mm S.C.m₀) (QQ' S.C.Q') (hEE S.C.m₀ S.C.Q') (mm_ne S.C.m₀ S.C.hm)
      (QQ'_nondeg S.C.Q' S.C.hQ') hk (p.1, p.2.1) =
    FibreO.orb v (QQ S.C.m₀ S.C.Q') (mm S.C.m₀) (QQ' S.C.Q') (hEE S.C.m₀ S.C.Q') (mm_ne S.C.m₀ S.C.hm)
      (QQ'_nondeg S.C.Q' S.C.hQ') hk (p.1, 1) * FibreO.iota v (QQ S.C.m₀ S.C.Q') (mm S.C.m₀) (QQ' S.C.Q')
        (hEE S.C.m₀ S.C.Q') p.2.1
  simp only [FibreO.orb, map_one, mul_one]

theorem sec1_mulVec (x : S.X1 v) :
    (((S.sec1 v hk x : SOv v (splitForm S.C.m₀ S.C.Q')) : orthGroup (QQ S.C.m₀ S.C.Q') Fv) :
      GL (Fin (k + 1)) Fv).val *ᵥ (e₀ : Fin (k + 1) → Fv) = x.1 := by
  have h := (FibreO.orbitSection v (QQ S.C.m₀ S.C.Q') (mm S.C.m₀) (QQ' S.C.Q') (hEE S.C.m₀ S.C.Q')
    (mm_ne S.C.m₀ S.C.hm) (QQ'_nondeg S.C.Q' S.C.hQ') hk).sec_smul x
  have h' := congrArg Subtype.val h
  rw [← h']
  show _ = (FibreO.secOrth v (QQ S.C.m₀ S.C.Q') (mm S.C.m₀) (QQ' S.C.Q') (hEE S.C.m₀ S.C.Q')
    (mm_ne S.C.m₀ S.C.hm) (QQ'_nondeg S.C.Q' S.C.hQ') hk x : GL (Fin (k + 1)) Fv).val *ᵥ e₀
  simp only [sec1, FibreSO.orbSO, FibreO.orb, OneMemClass.coe_one, map_one, mul_one]

theorem iota1_mulVec (h : SOv v S.C.Q') :
    (((S.iota1 v h : SOv v (splitForm S.C.m₀ S.C.Q')) : orthGroup (QQ S.C.m₀ S.C.Q') Fv) :
      GL (Fin (k + 1)) Fv).val *ᵥ (e₀ : Fin (k + 1) → Fv) = e₀ :=
  FibreO.iota_mulVec_e₀ v (QQ S.C.m₀ S.C.Q') (mm S.C.m₀) (QQ' S.C.Q') (hEE S.C.m₀ S.C.Q') h.1

theorem orb1_injective :
    Function.Injective fun p : S.X1 v × SOv v S.C.Q' => S.sec1 v hk p.1 * S.iota1 v p.2 := by
  rintro ⟨x, h⟩ ⟨x', h'⟩ e
  simp only at e
  have hx : x = x' := Subtype.ext (by
    have := congrArg (fun g : SOv v (splitForm S.C.m₀ S.C.Q') =>
      ((g : orthGroup (QQ S.C.m₀ S.C.Q') Fv) : GL (Fin (k + 1)) Fv).val *ᵥ (e₀ : Fin (k + 1) → Fv)) e
    simp only [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, S.iota1_mulVec] at this
    rwa [S.sec1_mulVec v hk, S.sec1_mulVec v hk] at this)
  subst hx
  have e2 := mul_left_cancel e
  have e3 := congrArg (fun g : SOv v (splitForm S.C.m₀ S.C.Q') =>
    ((g : orthGroup (QQ S.C.m₀ S.C.Q') Fv) : GL (Fin (k + 1)) Fv).val) e2
  simp only [iota1_val] at e3
  exact Prod.ext rfl (Subtype.ext (Subtype.ext (Units.ext (cornerMat_injective_right e3))))

/-! ### The stabilizer correction $\kappa$ -/

theorem cornerMat_sub_of_fix {K : Type*} [Field K] {C : Matrix (Fin (k + 1)) (Fin (k + 1)) K}
    {H' : Matrix (Fin k) (Fin k) K} {a : K} (ha : a ≠ 0) (hC : C = cornerMat a H')
    {M : Matrix (Fin (k + 1)) (Fin (k + 1)) K} (h1 : Mᵀ * C * M = C) (h2 : M *ᵥ (e₀ : Fin (k + 1) → K) = e₀) :
    M = cornerMat 1 (M.submatrix Fin.succ Fin.succ) ∧
      (M.submatrix Fin.succ Fin.succ)ᵀ * H' * M.submatrix Fin.succ Fin.succ = H' ∧
      (M.submatrix Fin.succ Fin.succ).det = M.det := by
  have hP : IsUnit (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) K).det := by simp
  have hPH : (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) K)ᵀ * C * 1 = cornerMat a H' := by simp [hC]
  have h2' : M *ᵥ ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) K) *ᵥ e0) =
      (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) K) *ᵥ e0 := by
    rw [one_mulVec]; show M *ᵥ Pi.single 0 1 = Pi.single 0 1; rw [← e₀_eq_single]; exact h2
  obtain ⟨e1, e2, e3⟩ := exists_conjBlock_eq hP ha hPH h1 h2'
  have hb : blockOf 1 M = M.submatrix Fin.succ Fin.succ := by simp [blockOf]
  rw [hb] at e1 e2 e3
  refine ⟨?_, e2, e3⟩
  rw [conjBlock] at e1
  simpa using e1.symm

/-- The block of an isometry of $\mathrm{diag}(a, H')$ fixing $e_0$, as an element of $GL_k$. -/
def subGL {K : Type*} [Field K] {C : Matrix (Fin (k + 1)) (Fin (k + 1)) K}
    {H' : Matrix (Fin k) (Fin k) K} {a : K} (ha : a ≠ 0) (hC : C = cornerMat a H') (M : GL (Fin (k + 1)) K)
    (h1 : M.valᵀ * C * M.val = C) (h2 : M.val *ᵥ (e₀ : Fin (k + 1) → K) = e₀) : GL (Fin k) K := by
  have h1' : (M⁻¹ : GL (Fin (k + 1)) K).valᵀ * C * (M⁻¹ : GL (Fin (k + 1)) K).val = C := by
    calc (M⁻¹ : GL (Fin (k + 1)) K).valᵀ * C * (M⁻¹ : GL (Fin (k + 1)) K).val
        = (M⁻¹ : GL (Fin (k + 1)) K).valᵀ * (M.valᵀ * C * M.val) * (M⁻¹ : GL (Fin (k + 1)) K).val := by rw [h1]
      _ = (M.val * (M⁻¹ : GL (Fin (k + 1)) K).val)ᵀ * C * (M.val * (M⁻¹ : GL (Fin (k + 1)) K).val) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = C := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]; simp
  have h2' : (M⁻¹ : GL (Fin (k + 1)) K).val *ᵥ (e₀ : Fin (k + 1) → K) = e₀ := by
    conv_lhs => rw [← h2]
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have A := cornerMat_sub_of_fix ha hC h1 h2
  have B := cornerMat_sub_of_fix ha hC h1' h2'
  exact ⟨M.val.submatrix Fin.succ Fin.succ, (M⁻¹ : GL (Fin (k + 1)) K).val.submatrix Fin.succ Fin.succ,
    cornerMat_injective_right (c := 1) (d := 1) (by
      rw [show ∀ X Y : Matrix (Fin k) (Fin k) K, cornerMat (1 : K) (X * Y) = cornerMat 1 X * cornerMat 1 Y from
        fun X Y => by rw [cornerMat_mul, one_mul], ← A.1, ← B.1, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        cornerMat_one]),
    cornerMat_injective_right (c := 1) (d := 1) (by
      rw [show ∀ X Y : Matrix (Fin k) (Fin k) K, cornerMat (1 : K) (X * Y) = cornerMat 1 X * cornerMat 1 Y from
        fun X Y => by rw [cornerMat_mul, one_mul], ← B.1, ← A.1, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        cornerMat_one])⟩

theorem subGL_val {K : Type*} [Field K] {C : Matrix (Fin (k + 1)) (Fin (k + 1)) K}
    {H' : Matrix (Fin k) (Fin k) K} {a : K} (ha : a ≠ 0) (hC : C = cornerMat a H') (M : GL (Fin (k + 1)) K)
    (h1 : M.valᵀ * C * M.val = C) (h2 : M.val *ᵥ (e₀ : Fin (k + 1) → K) = e₀) :
    (subGL ha hC M h1 h2).val = M.val.submatrix Fin.succ Fin.succ := rfl

theorem subGL_inv_val {K : Type*} [Field K] {C : Matrix (Fin (k + 1)) (Fin (k + 1)) K}
    {H' : Matrix (Fin k) (Fin k) K} {a : K} (ha : a ≠ 0) (hC : C = cornerMat a H') (M : GL (Fin (k + 1)) K)
    (h1 : M.valᵀ * C * M.val = C) (h2 : M.val *ᵥ (e₀ : Fin (k + 1) → K) = e₀) :
    ((subGL ha hC M h1 h2)⁻¹ : GL (Fin k) K).val = (M⁻¹ : GL (Fin (k + 1)) K).val.submatrix Fin.succ Fin.succ := rfl

/-- The correction $M(x) = s_1(x)^{-1}\varphi(s_0(\psi x))$, an element of the stabilizer of $e_0$. -/
def corrM (x : S.X1 v) : SOv v (splitForm S.C.m₀ S.C.Q') :=
  (S.sec1 v hk x)⁻¹ * S.phiV v (S.secSO hρ v (S.psi v x))

theorem corrM_iso (x : S.X1 v) :
    (((S.corrM hρ v hk x : SOv v _) : orthGroup (QQ S.C.m₀ S.C.Q') Fv) : GL (Fin (k + 1)) Fv).valᵀ *
      hesAt (splitForm S.C.m₀ S.C.Q') (σV v) *
      (((S.corrM hρ v hk x : SOv v _) : orthGroup (QQ S.C.m₀ S.C.Q') Fv) : GL (Fin (k + 1)) Fv).val =
      hesAt (splitForm S.C.m₀ S.C.Q') (σV v) :=
  (mem_orthGroup _).mp ((S.corrM hρ v hk x : SOv v _) : orthGroup (QQ S.C.m₀ S.C.Q') Fv).2

theorem phiV_secSO_mulVec (x : S.X1 v) :
    (((S.phiV v (S.secSO hρ v (S.psi v x)) : SOv v _) : orthGroup (QQ S.C.m₀ S.C.Q') Fv) :
      GL (Fin (k + 1)) Fv).val *ᵥ (e₀ : Fin (k + 1) → Fv) = x.1 := by
  rw [phiV_val, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, e₀_eq_single]
  have hP := S.PAt_mulVec_e0 (σV v)
  have hs := S.secFinGL_mulVec hρ v (S.psi v x).1 ((mem_sphV_iff Q₀ ρ v _).mp (S.psi v x).2)
  rw [show (Pi.single 0 1 : Fin (k + 1) → Fv) = e0 from rfl, hP, mulVec_smul]
  rw [show (((S.secSO hρ v (S.psi v x) : SOv v Q₀) : orthGroup QF Fv) : GL (Fin (k + 1)) Fv).val =
      (S.secFinGL hρ v (S.psi v x).1 ((mem_sphV_iff Q₀ ρ v _).mp (S.psi v x).2)).val from rfl]
  rw [show (fun i => σV v (S.ξ.1 i)) = (S.sphereDataAt hρ (σV v)).x₀ from rfl, hs, psi_val, psiGL_val,
    smul_mulVec, smul_smul, mul_inv_cancel₀ (S.dV_ne_zero v), one_smul, mulVec_mulVec, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, one_mulVec]

theorem corrM_fix (x : S.X1 v) :
    (((S.corrM hρ v hk x : SOv v _) : orthGroup (QQ S.C.m₀ S.C.Q') Fv) : GL (Fin (k + 1)) Fv).val *ᵥ
      (e₀ : Fin (k + 1) → Fv) = e₀ := by
  rw [corrM, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, S.phiV_secSO_mulVec]
  conv_lhs => rw [← S.sec1_mulVec v hk x]
  rw [mulVec_mulVec, ← Units.val_mul]
  simp

/-- **The correction $\kappa(x)\in SO(Q')(F_v)$** with $\varphi(s_0(\psi x)) = s_1(x)\,\mathrm{diag}(1,\kappa(x))$. -/
def kappa (x : S.X1 v) : SOv v S.C.Q' :=
  ⟨⟨subGL (S.two_m₀_ne_zero (σV v)) (S.hesAt_splitForm (σV v))
      (((S.corrM hρ v hk x : SOv v _) : orthGroup (QQ S.C.m₀ S.C.Q') Fv) : GL (Fin (k + 1)) Fv)
      (S.corrM_iso hρ v hk x) (S.corrM_fix hρ v hk x),
    (mem_orthGroup _).mpr (cornerMat_sub_of_fix (S.two_m₀_ne_zero (σV v)) (S.hesAt_splitForm (σV v))
      (S.corrM_iso hρ v hk x) (S.corrM_fix hρ v hk x)).2.1⟩, by
    show (subGL (S.two_m₀_ne_zero (σV v)) (S.hesAt_splitForm (σV v)) _ (S.corrM_iso hρ v hk x)
      (S.corrM_fix hρ v hk x)).val.det = 1
    rw [subGL_val, (cornerMat_sub_of_fix (S.two_m₀_ne_zero (σV v)) (S.hesAt_splitForm (σV v))
      (S.corrM_iso hρ v hk x) (S.corrM_fix hρ v hk x)).2.2]
    exact ((S.corrM hρ v hk x : SOv v _)).2⟩

theorem phiV_secSO_eq (x : S.X1 v) :
    S.phiV v (S.secSO hρ v (S.psi v x)) = S.sec1 v hk x * S.iota1 v (S.kappa hρ v hk x) := by
  have hM := (cornerMat_sub_of_fix (S.two_m₀_ne_zero (σV v)) (S.hesAt_splitForm (σV v))
      (S.corrM_iso hρ v hk x) (S.corrM_fix hρ v hk x)).1
  have : S.iota1 v (S.kappa hρ v hk x) = S.corrM hρ v hk x :=
    Subtype.ext (Subtype.ext (Units.ext (by rw [iota1_val]; exact hM.symm)))
  rw [this, corrM, mul_inv_cancel_left]

/-! ### Measurability -/

include hQ in
theorem measurable_secSO : Measurable (S.secSO hρ v) := by
  refine Measurable.subtype_mk (FibreO.measurable_of_val v QF (nondegenerate_QF Q₀ hQ) ?_)
  exact (measurable_secP _ _ (S.measurableSet_bFin hρ v)).comp measurable_subtype_coe

theorem measurable_sec1 : Measurable (S.sec1 v hk) :=
  (FibreSO.measurable_orbSO v S.C.m₀ S.C.hm S.C.Q' S.C.hQ' hk).comp (measurable_id.prodMk measurable_const)

include hQ in
theorem measurable_corrM : Measurable (S.corrM hρ v hk) :=
  (S.measurable_sec1 v hk).inv.mul
    ((S.continuous_phiV v).measurable.comp ((S.measurable_secSO hρ hQ v).comp (S.psi v).measurable))

include hQ in
theorem measurable_kappa : Measurable (S.kappa hρ v hk) := by
  refine Measurable.subtype_mk (FibreO.measurable_of_val v (QQ' S.C.Q') (QQ'_nondeg S.C.Q' S.C.hQ') ?_)
  have hc : Continuous fun g : SOv v (splitForm S.C.m₀ S.C.Q') =>
      ((((g : orthGroup (QQ S.C.m₀ S.C.Q') Fv) : GL (Fin (k + 1)) Fv)).val).submatrix Fin.succ Fin.succ :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_submatrix _ _
  exact hc.measurable.comp (S.measurable_corrM hρ hQ v hk)

/-! ### The local identity -/

/-- **The local constant at $v$**: $|\det G|_v^{N+1}\cdot\frac{\Delta(d^{-2})}{\Delta(\det(d^{-1}G))}\cdot|2m_0|_v^{-k}$. -/
def cFin : ℝ≥0∞ :=
  ENNReal.ofReal ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F (simJac 1 S.C.G))‖ * S.bPsi v *
    ENNReal.ofReal ((absTwoM v S.C.m₀ ^ k)⁻¹)

include hQ hk in
/-- **The local orbital identity at a finite place, for our section and embedding** (set form):
$\mu_v(s_v(A)\,\iota_v(B)) = c_v\,\sigma_v(A)\,\mu'_v(B)$. -/
theorem localFib_fin {A : Set (sphV Q₀ ρ v)} (hA : MeasurableSet A) {B : Set (SOv v S.C.Q')} (hB : MeasurableSet B)
    (hE : MeasurableSet (secMulImage (S.secSO hρ v) (S.iotaSO v) A B))
    (hφE : MeasurableSet (S.phiV v '' secMulImage (S.secSO hρ v) (S.iotaSO v) A B)) :
    muLocSO v Q₀ 1 (secMulImage (S.secSO hρ v) (S.iotaSO v) A B) =
      S.cFin v * sigV Q₀ ρ hQ v A * muLocSO v S.C.Q' 1 B := by
  have hQ' := S.C.hQ'
  have : SFinite (nuS v S.C.m₀ S.C.hm S.C.Q' S.C.hQ') := inferInstance
  have : (muLocSO v S.C.Q' 1).IsMulLeftInvariant := by unfold muLocSO; infer_instance
  have : SFinite (muLocSO v S.C.Q' 1) := by unfold muLocSO; infer_instance
  have hfib := FibreSO.lerayMeasure_orbital_finitePlace v S.C.m₀ S.C.hm S.C.Q' S.C.hQ' hk
  rw [S.orbSO_eq_mul v hk] at hfib
  have horbm : Measurable fun p : S.X1 v × SOv v S.C.Q' => S.sec1 v hk p.1 * S.iota1 v p.2 := by
    rw [← S.orbSO_eq_mul v hk]; exact FibreSO.measurable_orbSO v S.C.m₀ S.C.hm S.C.Q' S.C.hQ' hk
  have hι : ∀ h, S.phiV v (S.iotaSO v h) = S.iota1 v h := by
    intro h
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    rw [phiV_val, Units.val_mul, Units.val_mul, iotaSO_val, iota1_val, conjBlock, ← Matrix.coe_units_inv]
    simp only [← Matrix.mul_assoc]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.mul_one]
  have hι₁ : Function.Injective (S.iota1 v) := fun h h' e => by
    have := congrArg (fun g : SOv v (splitForm S.C.m₀ S.C.Q') =>
      ((g : orthGroup (QQ S.C.m₀ S.C.Q') Fv) : GL (Fin (k + 1)) Fv).val) e
    simp only [iota1_val] at this
    exact Subtype.ext (Subtype.ext (Units.ext (cornerMat_injective_right this)))
  rw [measure_mul_image_eq (S.phiV v) (S.phiV_injective v) (S.continuous_phiV v).measurable (muLocSO v Q₀ 1)
    (muLocSO v (splitForm S.C.m₀ S.C.Q') 1) _ (S.map_phiV hQ v) (S.psi v) (sigV Q₀ ρ hQ v)
    (nuS v S.C.m₀ S.C.hm S.C.Q' S.C.hQ') (S.bPsi v) (S.map_psi_nuS hQ v S.C.hm) (muLocSO v S.C.Q' 1)
    (S.sec1 v hk) (S.iota1 v) hι₁ (S.orb1_injective v hk) horbm _ hfib (S.secSO hρ v) (S.iotaSO v) hι
    (S.kappa hρ v hk) (S.measurable_kappa hρ hQ v hk) (S.phiV_secSO_eq hρ v hk) hA hB hE hφE, cFin]

/-! ### Measurability of the images (Lusin–Souslin) -/

theorem secMulImage_eq_image {X G : Type*} [Mul G] (s : X → G) (ι : SOv v S.C.Q' → G) (A : Set X)
    (B : Set (SOv v S.C.Q')) : secMulImage s ι A B = (fun p : X × SOv v S.C.Q' => s p.1 * ι p.2) '' (A ×ˢ B) := by
  ext g
  simp only [secMulImage, mem_setOf_eq, mem_image, mem_prod, Prod.exists]
  constructor
  · rintro ⟨y, hy, h, hh, rfl⟩; exact ⟨y, h, ⟨hy, hh⟩, rfl⟩
  · rintro ⟨y, h, ⟨hy, hh⟩, rfl⟩; exact ⟨y, hy, h, hh, rfl⟩

theorem continuous_iotaSO : Continuous (S.iotaSO v) :=
  Continuous.subtype_mk ((S.continuous_iotaV v).comp continuous_subtype_val) _

theorem iotaSO_GL (h : SOv v S.C.Q') :
    (((S.iotaSO v h : SOv v Q₀) : orthGroup QF Fv) : GL (Fin (k + 1)) Fv) =
      conjBlockGL (S.PAt (σV v)) ((h : orthGroup (S.C.Q'.map (algebraMap (𝓞 F) F)) Fv) : GL (Fin k) Fv) := rfl

theorem secSO_iotaSO_mulVec (y : sphV Q₀ ρ v) (h : SOv v S.C.Q') :
    ((((S.secSO hρ v y * S.iotaSO v h : SOv v Q₀) : orthGroup QF Fv) : GL (Fin (k + 1)) Fv).val *ᵥ
      (S.sphereDataAt hρ (σV v)).x₀) = y.1 := by
  have e : (((S.secSO hρ v y * S.iotaSO v h : SOv v Q₀) : orthGroup QF Fv) : GL (Fin (k + 1)) Fv).val =
      (((S.secSO hρ v y : SOv v Q₀) : orthGroup QF Fv) : GL (Fin (k + 1)) Fv).val *
        (((S.iotaSO v h : SOv v Q₀) : orthGroup QF Fv) : GL (Fin (k + 1)) Fv).val := rfl
  rw [e, ← mulVec_mulVec, S.iotaSO_GL v h, S.conjBlockGL_fix hρ]
  exact S.secFinGL_mulVec hρ v y.1 ((mem_sphV_iff Q₀ ρ v y.1).mp y.2)

theorem secSO_iotaSO_injective :
    Function.Injective fun p : sphV Q₀ ρ v × SOv v S.C.Q' => S.secSO hρ v p.1 * S.iotaSO v p.2 := by
  rintro ⟨y, h⟩ ⟨y', h'⟩ e
  simp only at e
  have hy : y = y' := Subtype.ext (by
    rw [← S.secSO_iotaSO_mulVec hρ v y h, ← S.secSO_iotaSO_mulVec hρ v y' h', e])
  subst hy
  have e2 := mul_left_cancel e
  have e3 := congrArg (fun g : SOv v Q₀ => ((g : orthGroup QF Fv) : GL (Fin (k + 1)) Fv)) e2
  simp only [S.iotaSO_GL v] at e3
  exact Prod.ext rfl (Subtype.ext (Subtype.ext (conjBlockGL_injective _ e3)))

include hQ in
/-- **The sets $s_v(A)\iota_v(B)$ and $\varphi(s_v(A)\iota_v(B))$ are measurable** (Lusin–Souslin). -/
theorem measurableSet_secMulImage {A : Set (sphV Q₀ ρ v)} (hA : MeasurableSet A) {B : Set (SOv v S.C.Q')}
    (hB : MeasurableSet B) :
    MeasurableSet (secMulImage (S.secSO hρ v) (S.iotaSO v) A B) ∧
      MeasurableSet (S.phiV v '' secMulImage (S.secSO hρ v) (S.iotaSO v) A B) := by
  have : PolishSpace (sphV Q₀ ρ v) := (FibreLeray.isClosed_sphereV v Q₀ _).polishSpace
  have : PolishSpace (SOv v S.C.Q') := polishSpace_of_isTopologicalGroup _
  have : PolishSpace (SOv v Q₀) := polishSpace_of_isTopologicalGroup _
  have : PolishSpace (SOv v (splitForm S.C.m₀ S.C.Q')) := polishSpace_of_isTopologicalGroup _
  have hm : Measurable fun p : sphV Q₀ ρ v × SOv v S.C.Q' => S.secSO hρ v p.1 * S.iotaSO v p.2 :=
    ((S.measurable_secSO hρ hQ v).comp measurable_fst).mul ((S.continuous_iotaSO v).measurable.comp measurable_snd)
  have hE : MeasurableSet (secMulImage (S.secSO hρ v) (S.iotaSO v) A B) := by
    rw [S.secMulImage_eq_image v]
    exact (hm.measurableEmbedding (S.secSO_iotaSO_injective hρ v)).measurableSet_image.mpr (hA.prod hB)
  exact ⟨hE, ((S.continuous_phiV v).measurable.measurableEmbedding (S.phiV_injective v)).measurableSet_image.mpr hE⟩

include hQ hk in
/-- **The local orbital identity at a finite place** (set form, no side conditions). -/
theorem localFib_fin' {A : Set (sphV Q₀ ρ v)} (hA : MeasurableSet A) {B : Set (SOv v S.C.Q')}
    (hB : MeasurableSet B) :
    muLocSO v Q₀ 1 (secMulImage (S.secSO hρ v) (S.iotaSO v) A B) =
      S.cFin v * sigV Q₀ ρ hQ v A * muLocSO v S.C.Q' 1 B :=
  S.localFib_fin hρ hQ v hk hA hB (S.measurableSet_secMulImage hρ hQ v hA hB).1
    (S.measurableSet_secMulImage hρ hQ v hA hB).2

end AdelicSphereSetup

end QuadFormsKB.Tamagawa.Measure.Weil

end
