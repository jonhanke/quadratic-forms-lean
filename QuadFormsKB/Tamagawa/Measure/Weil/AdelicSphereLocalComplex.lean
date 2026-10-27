import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereLocalFin
import QuadFormsKB.Tamagawa.Measure.OrbitalComplexStab
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarArchComplex
import QuadFormsKB.Tamagawa.Measure.Weil.SphereLocalTransport

/-!
# The local orbital identity at a complex place, for an arbitrary base point

For the setup of `AdelicSphere.lean` and a complex place $w$ with embedding $\tau = \sigma_w : F\to\mathbb C$, write
$Q_0^\tau$ (`QCx Q₀ w`), $Q'^\tau$ (`QCx S.C.Q' w`), $c = \tau(m_0)$ (`ccC`), $d = \tau(d)$ (`dC`), $G = \tau(G)$ (`PAt`).
Our section $s_w$ (`secSOC`, the component of `secInf`: its matrix is `secArchGL`), our embedding $\iota_w$ (`iotaC`) and the
Leray measure $\sigma_w$ of $Q_0^\tau$ on the sphere $\{Q_0^\tau = \tau(\rho)\}$ (`sigC`) satisfy
$$\mu_w\big(s_w(A)\,\iota_w(B)\big) = c_w\,\sigma_w(A)\,\mu'_w(B)\qquad(\texttt{localFib\_complex}),$$
with the explicit constant (`cCx`, `cCx_closed`)
$$c_w = \frac{|\det G|^{2(N)}\,|d|^{2k}}{|d|^{2}\,|2c|^{2k}},\qquad N = k+1,$$
(all absolute values the usual complex ones; $|\cdot|_w = |\cdot|^2$), for measurable $A$, $B$ (no side conditions).

*Proof.* The complex orbital identity for $\langle c\rangle\perp Q'^\tau$ at $e_0$ (`lerayMeasureC_orbital`,
valid for any section), moved to $Q_0^\tau$ by conjugation with $G$ (`map_lerayMeasureC_conjSOC'`) and the sphere
map $x\mapsto d^{-1}Gx$ (a new generic transport lemma `map_sphEquivC_sigC` for $\sigma_c$ under an invertible
linear map scaling the forms), with the change of section absorbed by left invariance (`measure_mul_image_eq`).
-/

open MeasureTheory Set Matrix
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.Measure.SphereLerayC

/-! ### A generic transport lemma for the complex sphere measure -/

section SphTransport

variable {n : ℕ}

/-- **Volume under a linear map of $\mathbb C^n$**: $\mathrm{vol}(g E) = |\det g|^2\,\mathrm{vol}(E)$. -/
theorem volume_image_toLin'_nnnorm (g : Matrix (Fin n) (Fin n) ℂ) (E : Set (Fin n → ℂ)) :
    volume (Matrix.toLin' g '' E) = ((‖g.det‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) * volume E := by
  rw [show ⇑(Matrix.toLin' g) = ⇑((Matrix.toLin' g).restrictScalars ℝ) from rfl, Measure.addHaar_image_linearMap,
    LerayComplex.det_restrictScalars_complex, LinearMap.det_toLin', Complex.normSq_eq_norm_sq,
    abs_of_nonneg (by positivity), ← ENNReal.ofReal_coe_nnreal]
  congr 2

variable {Q₁ Q₀ : QuadForm ℂ n} (P : GL (Fin n) ℂ) {a c₁ c₀ : ℂ} (ha : a ≠ 0)
  (hQ : ∀ x, Q₀.eval (P.val *ᵥ x) = a * Q₁.eval x) (hc : a * c₁ = c₀)

include hQ hc in
theorem sphEquivC_mem (x : SphC Q₁ c₁) : Q₀.eval (P.val *ᵥ x.1) = c₀ := by
  have hx : Q₁.eval x.1 = c₁ := x.2
  rw [hQ, hx, hc]

include ha hQ hc in
theorem sphEquivC_mem_symm (y : SphC Q₀ c₀) : Q₁.eval (((P⁻¹ : GL (Fin n) ℂ)).val *ᵥ y.1) = c₁ := by
  have hy : Q₀.eval y.1 = c₀ := y.2
  have h := hQ (((P⁻¹ : GL (Fin n) ℂ)).val *ᵥ y.1)
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, hy] at h
  exact mul_left_cancel₀ ha (h.symm.trans hc.symm)

/-- **The sphere map** $S_{c_1}(Q_1)\to S_{c_0}(Q_0)$, $x\mapsto Px$, for $P\in GL_n(\mathbb C)$ with
$Q_0(Px) = a\,Q_1(x)$ and $a c_1 = c_0$. -/
def sphEquivC : SphC Q₁ c₁ ≃ᵐ SphC Q₀ c₀ where
  toFun x := ⟨P.val *ᵥ x.1, sphEquivC_mem P hQ hc x⟩
  invFun y := ⟨((P⁻¹ : GL (Fin n) ℂ)).val *ᵥ y.1, sphEquivC_mem_symm P ha hQ hc y⟩
  left_inv x := Subtype.ext (by
    simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec])
  right_inv y := Subtype.ext (by
    simp only [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec])
  measurable_toFun := ((continuous_const.matrix_mulVec continuous_subtype_val).subtype_mk _).measurable
  measurable_invFun := ((continuous_const.matrix_mulVec continuous_subtype_val).subtype_mk _).measurable

theorem sphEquivC_val (x : SphC Q₁ c₁) :
    ((sphEquivC P ha hQ hc x : SphC Q₀ c₀) : Fin n → ℂ) = P.val *ᵥ x.1 := rfl

/-- **The cone measure under the sphere map**: $(\nu_{c_1})$ pushed forward is $|\det P|^{-2}\nu_{c_0}$. -/
theorem map_sphEquivC_nuC (hc₁ : c₁ ≠ 0) (hc₀ : c₀ ≠ 0) :
    (nuC Q₁ c₁).map (sphEquivC P ha hQ hc) = (((‖P.val.det‖₊ ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞) • nuC Q₀ c₀ := by
  have hdet : P.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp P.isUnit).ne_zero
  have hd2 : (‖P.val.det‖₊ ^ 2 : ℝ≥0) ≠ 0 := pow_ne_zero _ (nnnorm_ne_zero_iff.mpr hdet)
  have hr0 : ((‖P.val.det‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hd2
  ext A hA
  have himg : Matrix.toLin' P.val '' (polC Q₁ c₁ '' (R0 ×ˢ (sphEquivC P ha hQ hc ⁻¹' A))) =
      polC Q₀ c₀ '' (R0 ×ˢ A) := by
    ext y
    constructor
    · rintro ⟨_, ⟨⟨β, x⟩, ⟨hβ, hx⟩, rfl⟩, rfl⟩
      refine ⟨(β, sphEquivC P ha hQ hc x), ⟨hβ, hx⟩, ?_⟩
      show (β : ℂ) • (P.val *ᵥ x.1) = Matrix.toLin' P.val ((β : ℂ) • x.1)
      rw [Matrix.toLin'_apply, mulVec_smul]
    · rintro ⟨⟨β, x⟩, ⟨hβ, hx⟩, rfl⟩
      refine ⟨polC Q₁ c₁ (β, (sphEquivC P ha hQ hc).symm x), ⟨(β, (sphEquivC P ha hQ hc).symm x), ⟨hβ, ?_⟩, rfl⟩, ?_⟩
      · show sphEquivC P ha hQ hc ((sphEquivC P ha hQ hc).symm x) ∈ A
        rw [MeasurableEquiv.apply_symm_apply]; exact hx
      · have h : P.val *ᵥ ((sphEquivC P ha hQ hc).symm x).1 = x.1 :=
          congrArg Subtype.val ((sphEquivC P ha hQ hc).apply_symm_apply x)
        show Matrix.toLin' P.val ((β : ℂ) • ((sphEquivC P ha hQ hc).symm x).1) = (β : ℂ) • x.1
        rw [Matrix.toLin'_apply, mulVec_smul, h]
  rw [Measure.map_apply (sphEquivC P ha hQ hc).measurable hA,
    nuC_apply_volume hc₁ ((sphEquivC P ha hQ hc).measurable hA), Measure.smul_apply, nuC_apply_volume hc₀ hA,
    smul_eq_mul, ← himg, volume_image_toLin'_nnnorm, ENNReal.coe_inv hd2]
  set V := volume (polC Q₁ c₁ '' (R0 ×ˢ (sphEquivC P ha hQ hc ⁻¹' A)))
  set L := (lamU n R0)⁻¹
  set r : ℝ≥0∞ := ((‖P.val.det‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)
  have : r⁻¹ * (L * (r * V)) = (r⁻¹ * r) * (L * V) := by ring
  rw [this, ENNReal.inv_mul_cancel hr0 ENNReal.coe_ne_top, one_mul]

/-- **The Leray measure $\sigma_c$ under the sphere map**: $(\sigma_{c_1})$ pushed forward by $x\mapsto Px$ is
$|2c_1|^{-2}|\det P|^{-2}|2c_0|^{2}\,\sigma_{c_0}$. -/
theorem map_sphEquivC_sigC (hc₁ : c₁ ≠ 0) (hc₀ : c₀ ≠ 0) :
    (sigC Q₁ c₁).map (sphEquivC P ha hQ hc) =
      (((‖2 * c₁‖₊ ^ 2)⁻¹ * (‖P.val.det‖₊ ^ 2)⁻¹ * ‖2 * c₀‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) • sigC Q₀ c₀ := by
  have e1 : sigC Q₁ c₁ = (((‖2 * c₁‖₊ ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞) • nuC Q₁ c₁ := rfl
  rw [e1, Measure.map_smul, map_sphEquivC_nuC P ha hQ hc hc₁ hc₀, nuC_eq_smul_sigC hc₀, smul_smul, smul_smul,
    ← ENNReal.coe_mul, ← ENNReal.coe_mul, mul_assoc]
  exact (sphEquivC P ha hQ hc).measurable.aemeasurable

end SphTransport

/-! ### The complex data -/

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

theorem hesAt_QCx {n : ℕ} (Q : QuadForm (𝓞 F) n) (w : {w : InfinitePlace F // w.IsComplex}) :
    hesAt Q (σC w) = (QCx Q w).hessian :=
  (Siegel.hessian_map_NF _ _).symm

/-- $q(x) = x^{\mathsf T}Hx = 2\,Q^\tau(x)$ at a complex place. -/
theorem qH_hesAt_C {n : ℕ} (Q : QuadForm (𝓞 F) n) (w : {w : InfinitePlace F // w.IsComplex}) (x : Fin n → ℂ) :
    qH (hesAt Q (σC w)) x = 2 * (QCx Q w).eval x := by
  have h2 : (QCx Q w).hessian = (2 : ℂ) • gramC (QCx Q w) := by
    rw [gramC, smul_smul]; norm_num
  rw [hesAt_QCx, h2, SphereLerayC.eval_eq_gramC]
  unfold qH
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul]

variable {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F}

namespace AdelicSphereSetup

variable (S : AdelicSphereSetup Q₀ ρ) (hρ : ρ ≠ 0) (hQ : Q₀.Nondegenerate) (hk : 1 ≤ k)
  (w : {w : InfinitePlace F // w.IsComplex})

/-- $\tau(m_0)$, where $\tau = \sigma_w$ is the embedding at the complex place $w$. -/
abbrev ccC : ℂ := σC w (algebraMap (𝓞 F) F S.C.m₀)

/-- $\tau(d)$ at the complex place $w$. -/
abbrev dC : ℂ := σC w (algebraMap (𝓞 F) F S.C.d)

/-- **The split complex form** $\langle\tau(m_0)\rangle\perp Q'^\tau$. -/
abbrev QsC : QuadForm ℂ (k + 1) := splitForm (S.ccC w) (QCx S.C.Q' w)

theorem ccC_ne_zero : S.ccC w ≠ 0 := by
  rw [map_ne_zero, map_ne_zero_iff _ RingOfIntegers.coe_injective]; exact S.C.hm

theorem dC_ne_zero : S.dC w ≠ 0 := S.d_ne_zero (σC w)

theorem gdQ' : gramDetC (QCx S.C.Q' w) ≠ 0 := gramDetC_QCx_ne_zero S.C.Q' S.C.hQ' w

theorem gdQs : gramDetC (S.QsC w) ≠ 0 := OrbitalComplex.gramDetC_splitForm_ne_zero (S.ccC_ne_zero w) (S.gdQ' w)

/-- **$G^{\mathsf T}H_{Q_0}G = H_{\langle c\rangle\perp Q'}$** over $\mathbb C$. -/
theorem hessian_QsC :
    (S.QsC w).hessian = ((S.PAt (σC w) : GL (Fin (k + 1)) ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)ᵀ *
      (QCx Q₀ w).hessian * ((S.PAt (σC w) : GL (Fin (k + 1)) ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) := by
  have h := S.PAt_hes (σC w)
  rw [hesAt_QCx Q₀ w, hesAt_QCx S.C.Q' w] at h
  rw [hessian_splitForm]
  show _ = (S.PAt (σC w)).valᵀ * _ * (S.PAt (σC w)).val
  rw [h]
  simp only [map_mul, map_ofNat]

theorem hH_C : (S.QsC w).hessian = (1 : ℂ) • (((S.PAt (σC w) : GL (Fin (k + 1)) ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)ᵀ *
      (QCx Q₀ w).hessian * ((S.PAt (σC w) : GL (Fin (k + 1)) ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) := by
  rw [one_smul]; exact S.hessian_QsC w

/-! #### The sphere $\{Q_0^\tau = \tau(\rho)\}$ -/

theorem qH_of_mem_sphC (x : SphC (QCx Q₀ w) (σC w ρ)) : qH (hesAt Q₀ (σC w)) x.1 = σC w (2 * ρ) := by
  rw [qH_hesAt_C, map_mul, map_ofNat]
  have hx : (QCx Q₀ w).eval x.1 = σC w ρ := x.2
  rw [hx]

theorem eval_of_qH {x : Fin (k + 1) → ℂ} (hx : qH (hesAt Q₀ (σC w)) x = σC w (2 * ρ)) :
    (QCx Q₀ w).eval x = σC w ρ := by
  rw [qH_hesAt_C, map_mul, map_ofNat] at hx
  exact mul_left_cancel₀ two_ne_zero hx

/-- **Our section at the complex place $w$** on the sphere (the component of `secInf`). -/
def secSOC (x : SphC (QCx Q₀ w) (σC w ρ)) : ArchSOC (QCx Q₀ w) :=
  ArchSOC.mk _ (S.secArchGL hρ two_ne_zero (σC w) x.1 (qH_of_mem_sphC w x))
    (mem_soC_of Q₀ (σC w) (S.secArchGL_mem hρ two_ne_zero _ _ _).1 (S.secArchGL_mem hρ two_ne_zero _ _ _).2)

/-- **The matrix of our section** is `secArchGL` (so `secSOC` agrees with `secInf`). -/
theorem secSOC_mat (x : SphC (QCx Q₀ w) (σC w ρ)) :
    ArchSOC.mat _ (S.secSOC hρ w x) = (S.secArchGL hρ two_ne_zero (σC w) x.1 (qH_of_mem_sphC w x)).val := rfl

/-- **`secSOC` is the complex component of `secInf`.** -/
theorem secInf_snd_eq (y : adelicSphere Q₀ ρ) :
    (S.secInf hρ y).2 w =
      S.secSOC hρ w ⟨adC y.1 w, eval_of_qH w (y.2.2.1 w)⟩ := rfl

/-- **Our embedding at $w$** has matrix $G\,\mathrm{diag}(1, h)\,G^{-1}$. -/
theorem iotaC_mat (h : ArchSOC (QCx S.C.Q' w)) :
    ArchSOC.mat _ (S.iotaC w h) = conjBlock (S.PAt (σC w)).val (ArchSOC.mat _ h) :=
  conjBlockGL_val _ _

theorem iotaC_GL (h : ArchSOC (QCx S.C.Q' w)) :
    ((S.iotaC w h : ArchSOC (QCx Q₀ w)).1 : GL (Fin (k + 1)) ℂ) =
      conjBlockGL (S.PAt (σC w)) (h.1 : GL (Fin k) ℂ) := rfl

include hQ in
theorem measurable_secSOC : Measurable (S.secSOC hρ w) := by
  refine measurable_archSOC_of (f := S.secSOC hρ w) ?_ ?_
  · exact (measurable_secP _ _ (S.measurableSet_bArch hρ (σC w))).comp measurable_subtype_coe
  · exact (measurable_secPInv _ _ (S.measurableSet_bArch hρ (σC w))).comp measurable_subtype_coe

/-! #### The change of variables $x\mapsto d^{-1}Gx$ -/

/-- The linear map $x\mapsto d^{-1}Gx$ at $w$. -/
def psiC : GL (Fin (k + 1)) ℂ :=
  ⟨(S.dC w)⁻¹ • (S.PAt (σC w)).val, S.dC w • ((S.PAt (σC w))⁻¹ : GL (Fin (k + 1)) ℂ).val, by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ (S.dC_ne_zero w), ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_smul], by
    rw [smul_mul_smul_comm, mul_inv_cancel₀ (S.dC_ne_zero w), ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_smul]⟩

theorem psiC_val : (S.psiC w).val = (S.dC w)⁻¹ • (S.PAt (σC w)).val := rfl

theorem cPsiC_mul : ((S.dC w)⁻¹) ^ 2 * S.ccC w = σC w ρ := by
  have hq : qF Q₀ S.ξ.1 = ρ := S.ξ.2
  have hd := S.dC_ne_zero w
  rw [ccC, S.C.m₀_eq, hq, map_mul, map_pow]
  field_simp

/-- **$Q_0^\tau(d^{-1}Gx) = d^{-2}\,(\langle c\rangle\perp Q'^\tau)(x)$.** -/
theorem eval_psiC (x : Fin (k + 1) → ℂ) :
    (QCx Q₀ w).eval ((S.psiC w).val *ᵥ x) = ((S.dC w)⁻¹) ^ 2 * (S.QsC w).eval x := by
  have hs := gramC_similar (G := S.PAt (σC w)) (c := (1 : ℂ)) (Q := QCx Q₀ w) (Q' := S.QsC w) (S.hH_C w)
  rw [SphereLerayC.eval_eq_gramC (QCx Q₀ w), SphereLerayC.eval_eq_gramC (S.QsC w)]
  show qH (gramC (QCx Q₀ w)) _ = _ * qH (gramC (S.QsC w)) x
  rw [psiC_val, smul_mulVec, qH_smul, qH_mulVec_eq, hs, one_smul]

/-- **The sphere map** $\psi : \{\langle c\rangle\perp Q'^\tau = c\}\to\{Q_0^\tau = \tau(\rho)\}$, $x\mapsto d^{-1}Gx$. -/
def psiE : SphC (S.QsC w) (S.ccC w) ≃ᵐ SphC (QCx Q₀ w) (σC w ρ) :=
  sphEquivC (S.psiC w) (a := ((S.dC w)⁻¹) ^ 2) (pow_ne_zero 2 (inv_ne_zero (S.dC_ne_zero w)))
    (fun x => S.eval_psiC w x) (S.cPsiC_mul w)

theorem psiE_val (x : SphC (S.QsC w) (S.ccC w)) :
    ((S.psiE w x : SphC (QCx Q₀ w) (σC w ρ)) : Fin (k + 1) → ℂ) = (S.psiC w).val *ᵥ x.1 := rfl

/-- The constant of $\psi$ on the Leray measures. -/
def bPsiC : ℝ≥0∞ :=
  (((‖2 * S.ccC w‖₊ ^ 2)⁻¹ * (‖(S.psiC w).val.det‖₊ ^ 2)⁻¹ * ‖2 * σC w ρ‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)

/-- **$\psi_*\sigma_1 = b\,\sigma_0$.** -/
theorem map_psiE_sigC (hρ : ρ ≠ 0) :
    (sigC (S.QsC w) (S.ccC w)).map (S.psiE w) = S.bPsiC w • sigC (QCx Q₀ w) (σC w ρ) :=
  map_sphEquivC_sigC (S.psiC w) _ _ (S.cPsiC_mul w) (S.ccC_ne_zero w) ((map_ne_zero _).mpr hρ)

/-! #### The conjugation $g\mapsto G^{-1}gG$ -/

/-- The conjugation $SO(Q_0^\tau)(\mathbb C)\to SO(\langle c\rangle\perp Q'^\tau)(\mathbb C)$, $g\mapsto G^{-1}gG$. -/
def phiC : ArchSOC (QCx Q₀ w) →* ArchSOC (S.QsC w) :=
  (conjSOC (S.PAt (σC w)) (1 : ℂ) (S.hH_C w) one_ne_zero).toMulEquiv.toMonoidHom

theorem phiC_mat (g : ArchSOC (QCx Q₀ w)) :
    ArchSOC.mat _ (S.phiC w g) =
      (((S.PAt (σC w))⁻¹ : GL (Fin (k + 1)) ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) * ArchSOC.mat _ g *
        ((S.PAt (σC w) : GL (Fin (k + 1)) ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) := rfl

theorem continuous_phiC : Continuous (S.phiC w) :=
  (conjSOC (S.PAt (σC w)) (1 : ℂ) (S.hH_C w) one_ne_zero).continuous

theorem phiC_injective : Function.Injective (S.phiC w) :=
  (conjSOC (S.PAt (σC w)) (1 : ℂ) (S.hH_C w) one_ne_zero).injective

include hQ in
/-- The measure ratio of the conjugation. -/
theorem map_phiC :
    (lerayMeasureC (QCx Q₀ w) (gramDetC_QCx_ne_zero Q₀ hQ w)).map (S.phiC w) =
      ENNReal.ofReal (‖(S.PAt (σC w)).val.det‖ ^ (2 * (k + 1 + 1))) •
        lerayMeasureC (S.QsC w) (S.gdQs w) := by
  have h := map_lerayMeasureC_conjSOC' (S.PAt (σC w)) (1 : ℂ) (S.hH_C w) one_ne_zero
    (gramDetC_QCx_ne_zero Q₀ hQ w) (S.gdQs w)
  rw [norm_one, one_pow, one_mul] at h
  exact h

theorem phiC_iotaC (h : ArchSOC (QCx S.C.Q' w)) :
    S.phiC w (S.iotaC w h) = OrbitalComplex.iotaC (S.ccC w) (QCx S.C.Q' w) h := by
  apply Subtype.ext; apply Units.ext
  show ArchSOC.mat _ (S.phiC w (S.iotaC w h)) = ArchSOC.mat _ (OrbitalComplex.iotaC (S.ccC w) (QCx S.C.Q' w) h)
  rw [S.phiC_mat, S.iotaC_mat, OrbitalComplex.mat_iotaC, conjBlock, ← Matrix.coe_units_inv]
  simp only [← Matrix.mul_assoc]
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.mul_one]

/-! #### The split section and the stabilizer correction $\kappa$ -/

/-- The section for $\langle c\rangle\perp Q'^\tau$ (two reflections). -/
def sec1C : SphC (S.QsC w) (S.ccC w) → ArchSOC (S.QsC w) :=
  (OrbitalComplex.sphSectionC (S.ccC_ne_zero w) hk (S.gdQ' w)).toFun

theorem sec1C_spec (x : SphC (S.QsC w) (S.ccC w)) :
    ArchSOC.mat _ (S.sec1C hk w x) *ᵥ (e₀ : Fin (k + 1) → ℂ) = x.1 :=
  (OrbitalComplex.sphSectionC (S.ccC_ne_zero w) hk (S.gdQ' w)).spec x

/-- The correction $M(x) = s_1(x)^{-1}\varphi(s_w(\psi x))$, an element of the stabilizer of $e_0$. -/
def corrC (x : SphC (S.QsC w) (S.ccC w)) : ArchSOC (S.QsC w) :=
  (S.sec1C hk w x)⁻¹ * S.phiC w (S.secSOC hρ w (S.psiE w x))

theorem phiC_secSOC_mulVec (x : SphC (S.QsC w) (S.ccC w)) :
    ArchSOC.mat _ (S.phiC w (S.secSOC hρ w (S.psiE w x))) *ᵥ (e₀ : Fin (k + 1) → ℂ) = x.1 := by
  have hP := S.PAt_mulVec_e0 (σC w)
  have hs := S.secArchGL_mulVec hρ two_ne_zero (σC w) (S.psiE w x).1 (qH_of_mem_sphC w (S.psiE w x))
  rw [S.phiC_mat, ← mulVec_mulVec, ← mulVec_mulVec, e₀_eq_single,
    show (Pi.single 0 1 : Fin (k + 1) → ℂ) = e0 from rfl, hP]
  simp only [mulVec_smul]
  rw [S.secSOC_mat hρ w (S.psiE w x)]
  rw [show (fun i => σC w (S.ξ.1 i)) = (S.sphereDataAt hρ (σC w)).x₀ from rfl, hs, psiE_val, psiC_val,
    smul_mulVec, mulVec_smul, smul_smul, mul_inv_cancel₀ (S.dC_ne_zero w), one_smul, mulVec_mulVec,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem corrC_fix (x : SphC (S.QsC w) (S.ccC w)) :
    ArchSOC.mat _ (S.corrC hρ hk w x) *ᵥ (e₀ : Fin (k + 1) → ℂ) = e₀ := by
  rw [corrC, ArchSOC.mat_mul, ← mulVec_mulVec, S.phiC_secSOC_mulVec hρ w x]
  have h1 := S.sec1C_spec hk w x
  conv_lhs => rw [← h1]
  rw [mulVec_mulVec, ArchSOC.mat_inv_mul, one_mulVec]

/-- **The correction $\kappa(x)\in SO(Q'^\tau)(\mathbb C)$** with $\varphi(s_w(\psi x)) = s_1(x)\,\mathrm{diag}(1,\kappa(x))$. -/
def kappaC (x : SphC (S.QsC w) (S.ccC w)) : ArchSOC (QCx S.C.Q' w) :=
  Classical.choose (OrbitalComplex.exists_iotaC_eq_of_mulVec_e₀ (S.ccC_ne_zero w) (S.corrC hρ hk w x)
    (S.corrC_fix hρ hk w x))

theorem iotaC_kappaC (x : SphC (S.QsC w) (S.ccC w)) :
    OrbitalComplex.iotaC (S.ccC w) (QCx S.C.Q' w) (S.kappaC hρ hk w x) = S.corrC hρ hk w x :=
  Classical.choose_spec (OrbitalComplex.exists_iotaC_eq_of_mulVec_e₀ (S.ccC_ne_zero w) (S.corrC hρ hk w x)
    (S.corrC_fix hρ hk w x))

theorem phiC_secSOC_eq (x : SphC (S.QsC w) (S.ccC w)) :
    S.phiC w (S.secSOC hρ w (S.psiE w x)) =
      S.sec1C hk w x * OrbitalComplex.iotaC (S.ccC w) (QCx S.C.Q' w) (S.kappaC hρ hk w x) := by
  rw [S.iotaC_kappaC hρ hk w x, corrC, mul_inv_cancel_left]

/-! #### Measurability -/

theorem measurable_sec1C : Measurable (S.sec1C hk w) :=
  (OrbitalComplex.sphSectionC (S.ccC_ne_zero w) hk (S.gdQ' w)).measurable

include hQ in
theorem measurable_corrC : Measurable (S.corrC hρ hk w) :=
  (S.measurable_sec1C hk w).inv.mul
    ((S.continuous_phiC w).measurable.comp ((S.measurable_secSOC hρ hQ w).comp (S.psiE w).measurable))

include hQ in
theorem measurable_kappaC : Measurable (S.kappaC hρ hk w) := by
  have : PolishSpace (ArchSOC (QCx S.C.Q' w)) := inferInstance
  have hemb := (OrbitalComplex.continuous_iotaC (S.ccC w) (QCx S.C.Q' w)).measurableEmbedding
    OrbitalComplex.iotaC_injective
  rw [← hemb.measurable_comp_iff]
  have : (OrbitalComplex.iotaC (S.ccC w) (QCx S.C.Q' w)) ∘ (S.kappaC hρ hk w) = S.corrC hρ hk w :=
    funext fun x => S.iotaC_kappaC hρ hk w x
  rw [this]
  exact S.measurable_corrC hρ hQ hk w

/-! ### The constant -/

/-- **The local constant at the complex place $w$**:
$$c_w = \frac{|\det G|^{2(k+1)}\,|d|^{2k}}{|d|^{2}\,|2c|^{2k}},\qquad G = \tau(G),\ d = \tau(d),\ c = \tau(m_0).$$ -/
def cCx : ℝ≥0∞ :=
  ENNReal.ofReal (‖(S.PAt (σC w)).val.det‖ ^ (2 * (k + 1)) * ‖S.dC w‖ ^ (2 * k) /
    (‖S.dC w‖ ^ 2 * ‖2 * S.ccC w‖ ^ (2 * k)))

theorem det_PAt_ne_zero : (S.PAt (σC w)).val.det ≠ 0 :=
  (S.isUnit_det_PAt (σC w)).ne_zero

theorem cCx_ne_zero : S.cCx w ≠ 0 := by
  have h1 := norm_pos_iff.mpr (S.det_PAt_ne_zero w)
  have h2 := norm_pos_iff.mpr (S.dC_ne_zero w)
  have h3 := norm_pos_iff.mpr (mul_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0) (S.ccC_ne_zero w))
  exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'

theorem cCx_ne_top : S.cCx w ≠ ⊤ := ENNReal.ofReal_ne_top

theorem norm_det_psiC :
    ‖(S.psiC w).val.det‖ = ‖S.dC w‖⁻¹ ^ (k + 1) * ‖(S.PAt (σC w)).val.det‖ := by
  rw [psiC_val, Matrix.det_smul, norm_mul, norm_pow, norm_inv, Fintype.card_fin]

theorem norm_two_mul_rho : ‖2 * σC w ρ‖ = ‖S.dC w‖⁻¹ ^ 2 * ‖2 * S.ccC w‖ := by
  rw [← S.cPsiC_mul w, show 2 * (((S.dC w)⁻¹) ^ 2 * S.ccC w) = ((S.dC w)⁻¹) ^ 2 * (2 * S.ccC w) by ring,
    norm_mul, norm_pow, norm_inv]

theorem bPsiC_eq : S.bPsiC w = ENNReal.ofReal ((‖2 * S.ccC w‖ ^ 2)⁻¹ * (‖(S.psiC w).val.det‖ ^ 2)⁻¹ *
    ‖2 * σC w ρ‖ ^ 2) := by
  rw [bPsiC, ← ENNReal.ofReal_coe_nnreal]
  congr 1

theorem c1C_eq : (((‖2 * S.ccC w‖₊ ^ (2 * k))⁻¹ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ((‖2 * S.ccC w‖ ^ (2 * k))⁻¹) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1

theorem real_ident (g d c : ℝ) (hg : g ≠ 0) (hd : d ≠ 0) (hc : c ≠ 0) (k : ℕ) :
    g ^ (2 * (k + 1 + 1)) * ((c ^ 2)⁻¹ * (((d⁻¹) ^ (k + 1) * g) ^ 2)⁻¹ * ((d⁻¹) ^ 2 * c) ^ 2) * (c ^ (2 * k))⁻¹ =
      g ^ (2 * (k + 1)) * d ^ (2 * k) / (d ^ 2 * c ^ (2 * k)) := by
  simp only [inv_pow]
  field_simp
  ring

/-- **The constant is the product of the three factors** (conjugation, sphere map, orbital constant). -/
theorem cCx_eq_factors :
    ENNReal.ofReal (‖(S.PAt (σC w)).val.det‖ ^ (2 * (k + 1 + 1))) * S.bPsiC w *
      (((‖2 * S.ccC w‖₊ ^ (2 * k))⁻¹ : ℝ≥0) : ℝ≥0∞) = S.cCx w := by
  have hg := norm_pos_iff.mpr (S.det_PAt_ne_zero w)
  have hd := norm_pos_iff.mpr (S.dC_ne_zero w)
  have hc := norm_pos_iff.mpr (mul_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0) (S.ccC_ne_zero w))
  rw [S.bPsiC_eq w, S.c1C_eq w, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), cCx,
    S.norm_det_psiC w, S.norm_two_mul_rho w]
  congr 1
  exact real_ident _ _ _ hg.ne' hd.ne' hc.ne' k

/-- **Closed form of the constant.** -/
theorem cCx_closed :
    S.cCx w = ENNReal.ofReal (‖(S.PAt (σC w)).val.det‖ ^ (2 * (k + 1)) * ‖S.dC w‖ ^ (2 * k) /
      (‖S.dC w‖ ^ 2 * ‖2 * S.ccC w‖ ^ (2 * k))) := rfl

/-! ### The local identity -/

include hQ hk in
/-- **The local orbital identity at a complex place, for our section and embedding** (set form, with the
measurability side conditions as hypotheses). -/
theorem localFib_complex_aux {A : Set (SphC (QCx Q₀ w) (σC w ρ))} (hA : MeasurableSet A)
    {B : Set (ArchSOC (QCx S.C.Q' w))} (hB : MeasurableSet B)
    (hE : MeasurableSet (secMulImage (S.secSOC hρ w) (S.iotaC w) A B))
    (hφE : MeasurableSet (S.phiC w '' secMulImage (S.secSOC hρ w) (S.iotaC w) A B)) :
    lerayMeasureC (QCx Q₀ w) (gramDetC_QCx_ne_zero Q₀ hQ w) (secMulImage (S.secSOC hρ w) (S.iotaC w) A B) =
      S.cCx w * sigC (QCx Q₀ w) (σC w ρ) A * lerayMeasureC (QCx S.C.Q' w) (S.gdQ' w) B := by
  have hcc := S.ccC_ne_zero w
  have hQ' := S.gdQ' w
  have : SigmaFinite (sigC (S.QsC w) (S.ccC w)) := sigmaFinite_sigC hcc (by omega)
  have := isHaarMeasure_lerayMeasureC hQ'
  have hfib := OrbitalComplex.lerayMeasureC_orbital hcc hQ' (OrbitalComplex.sphSectionC hcc hk hQ')
  have horbm : Measurable fun p : SphC (S.QsC w) (S.ccC w) × ArchSOC (QCx S.C.Q' w) =>
      S.sec1C hk w p.1 * OrbitalComplex.iotaC (S.ccC w) (QCx S.C.Q' w) p.2 :=
    OrbitalComplex.measurable_orbC (OrbitalComplex.sphSectionC hcc hk hQ')
  have horb : Function.Injective fun p : SphC (S.QsC w) (S.ccC w) × ArchSOC (QCx S.C.Q' w) =>
      S.sec1C hk w p.1 * OrbitalComplex.iotaC (S.ccC w) (QCx S.C.Q' w) p.2 :=
    (OrbitalComplex.orbC_bijective hcc (OrbitalComplex.sphSectionC hcc hk hQ')).1
  rw [measure_mul_image_eq (S.phiC w) (S.phiC_injective w) (S.continuous_phiC w).measurable
    (lerayMeasureC (QCx Q₀ w) (gramDetC_QCx_ne_zero Q₀ hQ w)) (lerayMeasureC (S.QsC w) (S.gdQs w)) _
    (S.map_phiC hQ w) (S.psiE w) (sigC (QCx Q₀ w) (σC w ρ)) (sigC (S.QsC w) (S.ccC w)) (S.bPsiC w)
    (S.map_psiE_sigC w hρ) (lerayMeasureC (QCx S.C.Q' w) hQ')
    (S.sec1C hk w) (OrbitalComplex.iotaC (S.ccC w) (QCx S.C.Q' w)) OrbitalComplex.iotaC_injective horb horbm _
    hfib (S.secSOC hρ w) (S.iotaC w) (S.phiC_iotaC w) (S.kappaC hρ hk w) (S.measurable_kappaC hρ hQ hk w)
    (S.phiC_secSOC_eq hρ hk w) hA hB hE hφE, cCx_eq_factors]

/-! ### Measurability of the images (Lusin–Souslin) -/

theorem secMulImage_eq_imageC {X G : Type*} [Mul G] (s : X → G) (ι : ArchSOC (QCx S.C.Q' w) → G) (A : Set X)
    (B : Set (ArchSOC (QCx S.C.Q' w))) :
    secMulImage s ι A B = (fun p : X × ArchSOC (QCx S.C.Q' w) => s p.1 * ι p.2) '' (A ×ˢ B) := by
  ext g
  simp only [secMulImage, mem_ofPred_eq, mem_image, mem_prod, Prod.exists]
  constructor
  · rintro ⟨y, hy, h, hh, rfl⟩; exact ⟨y, h, ⟨hy, hh⟩, rfl⟩
  · rintro ⟨y, h, ⟨hy, hh⟩, rfl⟩; exact ⟨y, hy, h, hh, rfl⟩

theorem secSOC_iotaC_mulVec (y : SphC (QCx Q₀ w) (σC w ρ)) (h : ArchSOC (QCx S.C.Q' w)) :
    (ArchSOC.mat _ (S.secSOC hρ w y * S.iotaC w h)) *ᵥ (S.sphereDataAt hρ (σC w)).x₀ = y.1 := by
  have e : ArchSOC.mat _ (S.secSOC hρ w y * S.iotaC w h) =
      ArchSOC.mat _ (S.secSOC hρ w y) * ArchSOC.mat _ (S.iotaC w h) := ArchSOC.mat_mul _ _ _
  have hfix : conjBlock (S.PAt (σC w)).val (ArchSOC.mat _ h) *ᵥ (S.sphereDataAt hρ (σC w)).x₀ =
      (S.sphereDataAt hρ (σC w)).x₀ := by
    have := S.conjBlockGL_fix hρ (σC w) (ArchSOC.incl _ h)
    rw [conjBlockGL_val] at this
    exact this
  rw [e, ← mulVec_mulVec, S.iotaC_mat w h, hfix]
  exact S.secArchGL_mulVec hρ two_ne_zero (σC w) y.1 (qH_of_mem_sphC w y)

theorem secSOC_iotaC_injective :
    Function.Injective fun p : SphC (QCx Q₀ w) (σC w ρ) × ArchSOC (QCx S.C.Q' w) =>
      S.secSOC hρ w p.1 * S.iotaC w p.2 := by
  rintro ⟨y, h⟩ ⟨y', h'⟩ e
  simp only at e
  have hy : y = y' := Subtype.ext (by
    rw [← S.secSOC_iotaC_mulVec hρ w y h, ← S.secSOC_iotaC_mulVec hρ w y' h', e])
  subst hy
  have e2 := mul_left_cancel e
  have e3 := congrArg (fun g : ArchSOC (QCx Q₀ w) => (g.1 : GL (Fin (k + 1)) ℂ)) e2
  simp only [S.iotaC_GL w] at e3
  exact Prod.ext rfl (Subtype.ext (conjBlockGL_injective _ e3))

include hQ in
/-- **The sets $s_w(A)\iota_w(B)$ and $\varphi(s_w(A)\iota_w(B))$ are measurable** (Lusin–Souslin). -/
theorem measurableSet_secMulImageC {A : Set (SphC (QCx Q₀ w) (σC w ρ))} (hA : MeasurableSet A)
    {B : Set (ArchSOC (QCx S.C.Q' w))} (hB : MeasurableSet B) :
    MeasurableSet (secMulImage (S.secSOC hρ w) (S.iotaC w) A B) ∧
      MeasurableSet (S.phiC w '' secMulImage (S.secSOC hρ w) (S.iotaC w) A B) := by
  have hm : Measurable fun p : SphC (QCx Q₀ w) (σC w ρ) × ArchSOC (QCx S.C.Q' w) =>
      S.secSOC hρ w p.1 * S.iotaC w p.2 :=
    ((S.measurable_secSOC hρ hQ w).comp measurable_fst).mul
      ((S.continuous_iotaC w).measurable.comp measurable_snd)
  have hE : MeasurableSet (secMulImage (S.secSOC hρ w) (S.iotaC w) A B) := by
    rw [S.secMulImage_eq_imageC w]
    exact (hm.measurableEmbedding (S.secSOC_iotaC_injective hρ w)).measurableSet_image.mpr (hA.prod hB)
  exact ⟨hE, ((S.continuous_phiC w).measurable.measurableEmbedding (S.phiC_injective w)).measurableSet_image.mpr hE⟩

include hQ hk in
/-- **The local orbital identity at a complex place** (set form, no side conditions):
$$\mu_w\big(s_w(A)\,\iota_w(B)\big) = c_w\,\sigma_w(A)\,\mu'_w(B)\qquad(A\subseteq\{Q_0^\tau = \tau(\rho)\},\ B\subseteq SO(Q'^\tau)(\mathbb C)\text{ measurable}),$$
with $\mu_w,\mu'_w$ the complex Leray measures of $Q_0^\tau$, $Q'^\tau$ and $\sigma_w$ = `sigC`. The constant `cCx` is nonzero
and finite (`cCx_ne_zero`, `cCx_ne_top`), with closed form `cCx_closed`. -/
theorem localFib_complex {A : Set (SphC (QCx Q₀ w) (σC w ρ))} (hA : MeasurableSet A)
    {B : Set (ArchSOC (QCx S.C.Q' w))} (hB : MeasurableSet B) :
    lerayMeasureC (QCx Q₀ w) (gramDetC_QCx_ne_zero Q₀ hQ w) (secMulImage (S.secSOC hρ w) (S.iotaC w) A B) =
      S.cCx w * sigC (QCx Q₀ w) (σC w ρ) A * lerayMeasureC (QCx S.C.Q' w) (S.gdQ' w) B :=
  S.localFib_complex_aux hρ hQ hk w hA hB (S.measurableSet_secMulImageC hρ hQ w hA hB).1
    (S.measurableSet_secMulImageC hρ hQ w hA hB).2

end AdelicSphereSetup

end QuadFormsKB.Tamagawa.Measure.Weil

end
