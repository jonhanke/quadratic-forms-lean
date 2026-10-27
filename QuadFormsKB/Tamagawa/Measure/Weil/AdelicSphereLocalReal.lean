import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereLocalFin
import QuadFormsKB.Tamagawa.Measure.OrbitalReal
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarArchReal
import QuadFormsKB.Tamagawa.Measure.Weil.MuTamSO

/-!
# The local orbital identity at a real place, for an arbitrary base point

The real-place analogue of `AdelicSphereLocalFin.lean`. For the setup of `AdelicSphere.lean` and a real place $w$
(embedding $\sigma = \sigma_w : F\to\mathbb R$), write $Q_0^w$ (`QRe Q₀ w`) for the real form, $s_w$ (`secSOR`) for
our section on the sphere $\{Q_0^w = \sigma(\rho)\}$ (the $w$-component of the adelic section `secInf`, see
`secInf_fst`), $\iota_w$ (`iotaR`) for our embedding $SO(Q'^w)(\mathbb R)\to SO(Q_0^w)(\mathbb R)$ and $\sigma_w$-Leray
measures $\mu_w$ (`LerayReal.lerayMeasure`) on the groups and $\operatorname{sig}$ (`SphereLeray.sig`) on the sphere. Then
$$\mu_w\big(s_w(A)\,\iota_w(B)\big) = c_w\,\operatorname{sig}(A)\,\mu'_w(B)\qquad(\texttt{localFib\_real}),$$
for measurable $A$, $B$, with the explicit constant
$$c_w = |\det G|_w^{N+1}\cdot\frac{|d|_w^{k+1}}{|d|_w^{2}\,|\det G|_w}\cdot|2m_0|_w^{-k}
 = \Big|\frac{\det G}{d}\Big|_w^{k+1}\,|2\sigma(\rho)|^{-k}\qquad(\texttt{cReal},\ \texttt{cReal\_eq}),$$
where $N = k+1$, $G$ is the integral complement ($Q_0\circ G = \langle m_0\rangle\perp Q'$, $Ge_0 = d\xi$) and
$\sigma(m_0) = \sigma(d)^2\sigma(\rho)$. The constant is nonzero and finite (`cReal_ne_zero`, `cReal_ne_top`).

*Proof.* The real orbital identity (`OrbitalReal.lerayMeasure_orbital`, valid for **any** measurable section) for the
split form $\langle\sigma(m_0)\rangle\perp Q'^w$, with the section $\varphi\circ s_w\circ\psi$ (the transported section, so
that the stabilizer correction is trivial), moved to $Q_0^w$ by the conjugation $g\mapsto G^{-1}gG$
(`map_lerayMeasure_conjSO'`, with $c = 1$) and the sphere map $\psi : x\mapsto d^{-1}Gx$, whose effect on the Leray
measure of the sphere is `sig_transport` (a direct version of `sig_eq_smul_map_sphGL` combined with the homogeneity
`sig_scale`), through the generic `measure_mul_image_eq`.

*Note.* No hypothesis $1\le k$ is needed here (the finite place has one for `FibreSO`).
-/

open MeasureTheory Set Matrix
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.Measure.SphereLeray

/-! ### The Leray measure of a level set under a linear change of variables -/

section SphTransport

variable {n : ℕ} {Q Q₁ : QuadForm ℝ n} {c c₁ a : ℝ}

theorem eval_mulVec_mem (P : GL (Fin n) ℝ) (hc : c = a * c₁)
    (hP : ∀ x, Q.eval ((P : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) = a * Q₁.eval x) (x : Sph Q₁ c₁) :
    Q.eval ((P : Matrix (Fin n) (Fin n) ℝ) *ᵥ x.1) = c := by
  have h : Q₁.eval x.1 = c₁ := x.2
  rw [hP, hc, h]

theorem eval_mulVec_inv_mem (P : GL (Fin n) ℝ) (ha : a ≠ 0) (hc : c = a * c₁)
    (hP : ∀ x, Q.eval ((P : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) = a * Q₁.eval x) (y : Sph Q c) :
    Q₁.eval (((P⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) *ᵥ y.1) = c₁ := by
  apply mul_left_cancel₀ ha
  have h : Q.eval y.1 = c := y.2
  rw [← hP, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, h, hc]

/-- **The level-set map** $S_{c_1}(Q_1)\to S_c(Q)$, $x\mapsto Px$, when $Q(Px) = a\,Q_1(x)$ and $c = a\,c_1$
($a\ne0$), as a measurable equivalence. -/
def sphTEquiv (P : GL (Fin n) ℝ) (ha : a ≠ 0) (hc : c = a * c₁)
    (hP : ∀ x, Q.eval ((P : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) = a * Q₁.eval x) : Sph Q₁ c₁ ≃ᵐ Sph Q c where
  toFun x := ⟨(P : Matrix (Fin n) (Fin n) ℝ) *ᵥ x.1, eval_mulVec_mem P hc hP x⟩
  invFun y := ⟨((P⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) *ᵥ y.1, eval_mulVec_inv_mem P ha hc hP y⟩
  left_inv x := Subtype.ext (by
    simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec])
  right_inv y := Subtype.ext (by
    simp only [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec])
  measurable_toFun := ((continuous_const.matrix_mulVec continuous_subtype_val).subtype_mk _).measurable
  measurable_invFun := ((continuous_const.matrix_mulVec continuous_subtype_val).subtype_mk _).measurable

theorem sphTEquiv_apply (P : GL (Fin n) ℝ) (ha : a ≠ 0) (hc : c = a * c₁)
    (hP : ∀ x, Q.eval ((P : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) = a * Q₁.eval x) (x : Sph Q₁ c₁) :
    ((sphTEquiv P ha hc hP x : Sph Q c) : Fin n → ℝ) = (P : Matrix (Fin n) (Fin n) ℝ) *ᵥ x.1 := rfl

theorem det_GL_ne_zero' (P : GL (Fin n) ℝ) : (P : Matrix (Fin n) (Fin n) ℝ).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit P)).ne_zero

/-- **The cone measure under $x\mapsto Px$**: $\nu_c(Q) = |\det P|\cdot(x\mapsto Px)_*\nu_{c_1}(Q_1)$ when
$Q(Px) = a\,Q_1(x)$ and $c = a\,c_1$. -/
theorem nu_transport (hc : c ≠ 0) (hc₁ : c₁ ≠ 0) (ha : a ≠ 0) (hca : c = a * c₁) (P : GL (Fin n) ℝ)
    (hP : ∀ x, Q.eval ((P : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) = a * Q₁.eval x) :
    nu Q c = ENNReal.ofReal |(P : Matrix (Fin n) (Fin n) ℝ).det| •
      (nu Q₁ c₁).map (sphTEquiv P ha hca hP) := by
  ext A hA
  set e := sphTEquiv P ha hca hP with he
  have hm : Measurable e := e.measurable
  rw [Measure.smul_apply, Measure.map_apply hm hA, nu_apply hc hA, nu_apply hc₁ (hm hA), smul_eq_mul]
  have himg : Matrix.toLin' (P : Matrix (Fin n) (Fin n) ℝ) '' (pol Q₁ c₁ '' (Iic 0 ×ˢ (e ⁻¹' A))) =
      pol Q c '' (Iic 0 ×ˢ A) := by
    ext v
    constructor
    · rintro ⟨_, ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩, rfl⟩
      refine ⟨(t, e x), ⟨ht, hx⟩, ?_⟩
      simp [pol, sphTEquiv_apply, he]
    · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
      refine ⟨pol Q₁ c₁ (t, e.symm x), ⟨(t, e.symm x), ⟨ht, ?_⟩, rfl⟩, ?_⟩
      · show e (e.symm x) ∈ A
        rw [e.apply_symm_apply]; exact hx
      · have h1 : (P : Matrix (Fin n) (Fin n) ℝ) *ᵥ ((e.symm x : Sph Q₁ c₁) : Fin n → ℝ) = x.1 :=
          congrArg Subtype.val (e.apply_symm_apply x)
        simp only [pol, Matrix.toLin'_apply, mulVec_smul, h1]
  rw [← himg, MeasureTheory.Measure.addHaar_image_linearMap, LinearMap.det_toLin']
  ring

/-- **The Leray measure of the level set under $x\mapsto Px$**:
$\operatorname{sig}_c(Q) = \frac{|\det P|}{|a|}\,(x\mapsto Px)_*\operatorname{sig}_{c_1}(Q_1)$ when $Q(Px) = a\,Q_1(x)$,
$c = a\,c_1$. -/
theorem sig_transport (hc : c ≠ 0) (hc₁ : c₁ ≠ 0) (ha : a ≠ 0) (hca : c = a * c₁) (P : GL (Fin n) ℝ)
    (hP : ∀ x, Q.eval ((P : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) = a * Q₁.eval x) :
    sig Q c = ENNReal.ofReal (|(P : Matrix (Fin n) (Fin n) ℝ).det| / |a|) •
      (sig Q₁ c₁).map (sphTEquiv P ha hca hP) := by
  have hm := (sphTEquiv P ha hca hP).measurable
  have h1 : 0 < |a| := abs_pos.mpr ha
  have h2 : 0 < |c₁| := abs_pos.mpr hc₁
  rw [sig, sig, Measure.map_smul, nu_transport hc hc₁ ha hca P hP, smul_smul, smul_smul,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  · congr 2
    rw [hca, abs_mul]
    field_simp
  · exact hm.aemeasurable

/-- **The same, read backwards**: $(x\mapsto Px)_*\operatorname{sig}_{c_1}(Q_1) = \frac{|a|}{|\det P|}\operatorname{sig}_c(Q)$. -/
theorem map_sig_transport (hc : c ≠ 0) (hc₁ : c₁ ≠ 0) (ha : a ≠ 0) (hca : c = a * c₁) (P : GL (Fin n) ℝ)
    (hP : ∀ x, Q.eval ((P : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) = a * Q₁.eval x) :
    (sig Q₁ c₁).map (sphTEquiv P ha hca hP) =
      ENNReal.ofReal (|a| / |(P : Matrix (Fin n) (Fin n) ℝ).det|) • sig Q c := by
  have h1 : 0 < |a| := abs_pos.mpr ha
  have h2 : 0 < |(P : Matrix (Fin n) (Fin n) ℝ).det| := abs_pos.mpr (det_GL_ne_zero' P)
  rw [sig_transport hc hc₁ ha hca P hP, smul_smul, ← ENNReal.ofReal_mul (by positivity),
    show |a| / |(P : Matrix (Fin n) (Fin n) ℝ).det| * (|(P : Matrix (Fin n) (Fin n) ℝ).det| / |a|) = 1 by
      field_simp, ENNReal.ofReal_one, one_smul]

end SphTransport

/-! ### Real forms: Hessians and the level sets -/

section RealForms

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

theorem hessian_QRe' {n : ℕ} (Q : QuadForm (𝓞 F) n) (w : {w : InfinitePlace F // w.IsReal}) :
    (QRe Q w).hessian = hesAt Q (σR w) := Siegel.hessian_map_NF _ _

/-- $q_H(x) = 2Q(x)$ for a real quadratic form, $H$ its Hessian. -/
theorem two_mul_eval_real {n : ℕ} (Q : QuadForm ℝ n) (x : Fin n → ℝ) : qH Q.hessian x = 2 * Q.eval x := by
  have h := QuadFormsKB.Siegel.Kneser.two_mul_evalIn (K := ℝ) Q x
  rw [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at h
  exact h.symm

variable {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F}

variable (Q₀ ρ) in
/-- $x$ lies on the real sphere $\{Q_0^w = \sigma_w(\rho)\}$ iff $q(x) = \sigma_w(2\rho)$. -/
theorem mem_sphR_iff (w : {w : InfinitePlace F // w.IsReal}) (x : Fin (k + 1) → ℝ) :
    x ∈ sph (QRe Q₀ w) (σR w ρ) ↔ qH (hesAt Q₀ (σR w)) x = σR w (2 * ρ) := by
  rw [← hessian_QRe' Q₀ w, two_mul_eval_real, map_mul, map_ofNat]
  show (QRe Q₀ w).eval x = σR w ρ ↔ _
  exact ⟨fun h => by rw [h], fun h => mul_left_cancel₀ two_ne_zero h⟩

end RealForms

namespace AdelicSphereSetup

variable {F : Type} [Field F] [NumberField F] {k : ℕ} {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F}
  (S : AdelicSphereSetup Q₀ ρ) (hρ : ρ ≠ 0) (hQ : Q₀.Nondegenerate) (w : {w : InfinitePlace F // w.IsReal})

/-! ### The data at a real place -/

/-- $d$ at the real place $w$. -/
abbrev dR : ℝ := σR w (algebraMap (𝓞 F) F S.C.d)

/-- $m_0$ at the real place $w$. -/
abbrev mR : ℝ := σR w (algebraMap (𝓞 F) F S.C.m₀)

theorem dR_ne_zero : S.dR w ≠ 0 := S.d_ne_zero (σR w)

theorem mR_ne_zero : S.mR w ≠ 0 := by
  rw [mR, map_ne_zero, map_ne_zero_iff _ RingOfIntegers.coe_injective]; exact S.C.hm

/-- $\sigma(m_0) = \sigma(d)^2\sigma(\rho)$. -/
theorem mR_eq : S.mR w = S.dR w ^ 2 * σR w ρ := by
  have hq : qF Q₀ S.ξ.1 = ρ := S.ξ.2
  rw [mR, dR, S.C.m₀_eq, hq, map_mul, map_pow]

/-- **The split real form** $\langle\sigma_w(m_0)\rangle\perp Q'^w$. -/
abbrev Q1R : QuadForm ℝ (k + 1) := splitForm (S.mR w) (QRe S.C.Q' w)

/-- $H_{Q_1} = G^{\mathsf T}H_{Q_0}G$ at the real place. -/
theorem hess1 : (S.Q1R w).hessian =
    (1 : ℝ) • (((S.PAt (σR w)).val)ᵀ * (QRe Q₀ w).hessian * (S.PAt (σR w)).val) := by
  rw [one_smul, hessian_QRe', S.PAt_hes, Q1R, hessian_splitForm, hessian_QRe']
  simp only [mR, map_mul, map_ofNat]

/-- **The conjugation $g\mapsto G^{-1}gG$**, $SO(Q_0^w)(\mathbb R)\cong SO(Q_1^w)(\mathbb R)$ (the case $c=1$). -/
abbrev phiRE : ArchSO (QRe Q₀ w) ≃ₜ* ArchSO (S.Q1R w) :=
  conjSO (S.PAt (σR w)) 1 (S.hess1 w) one_ne_zero

/-- The conjugation as a homomorphism. -/
def phiR : ArchSO (QRe Q₀ w) →* ArchSO (S.Q1R w) := (S.phiRE w).toMulEquiv.toMonoidHom

theorem phiR_apply (g : ArchSO (QRe Q₀ w)) : S.phiR w g = S.phiRE w g := rfl

theorem mat_phiR (g : ArchSO (QRe Q₀ w)) :
    ArchSOInst.mat _ (S.phiR w g) =
      ((S.PAt (σR w))⁻¹ : GL (Fin (k + 1)) ℝ).val * ArchSOInst.mat _ g * (S.PAt (σR w)).val := rfl

theorem phiR_injective : Function.Injective (S.phiR w) := (S.phiRE w).injective

theorem continuous_phiR : Continuous (S.phiR w) := (S.phiRE w).continuous

include hQ in
/-- **The measure ratio of the conjugation**: $(\varphi)_*\mu_{Q_0^w} = |\det G|_w^{N+1}\mu_{Q_1^w}$,
$N = k+1$. -/
theorem map_phiR :
    (LerayReal.lerayMeasure (QRe Q₀ w) (gramDetR_QRe_ne_zero Q₀ hQ w)).map (S.phiR w) =
      ENNReal.ofReal (|(S.PAt (σR w)).val.det| ^ (k + 1 + 1)) •
        LerayReal.lerayMeasure (S.Q1R w)
          (OrbitalReal.gramDetR_splitForm_ne_zero (S.mR_ne_zero w) (gramDetR_QRe_ne_zero S.C.Q' S.C.hQ' w)) := by
  have h := map_lerayMeasure_conjSO' (S.PAt (σR w)) 1 (S.hess1 w) one_ne_zero (gramDetR_QRe_ne_zero Q₀ hQ w)
    (OrbitalReal.gramDetR_splitForm_ne_zero (S.mR_ne_zero w) (gramDetR_QRe_ne_zero S.C.Q' S.C.hQ' w))
  simp only [abs_one, one_pow, one_mul] at h
  exact h

/-! ### The sphere map $\psi : x\mapsto d^{-1}Gx$ -/

/-- The linear map $x\mapsto d^{-1}Gx$ at $w$. -/
def psiGLR : GL (Fin (k + 1)) ℝ :=
  ⟨(S.dR w)⁻¹ • (S.PAt (σR w)).val, S.dR w • ((S.PAt (σR w))⁻¹ : GL (Fin (k + 1)) ℝ).val, by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ (S.dR_ne_zero w), ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_smul], by
    rw [smul_mul_smul_comm, mul_inv_cancel₀ (S.dR_ne_zero w), ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_smul]⟩

theorem psiGLR_val : (S.psiGLR w).val = (S.dR w)⁻¹ • (S.PAt (σR w)).val := rfl

/-- **$Q_0^w(d^{-1}Gx) = d^{-2}Q_1^w(x)$.** -/
theorem eval_psiGLR (x : Fin (k + 1) → ℝ) :
    (QRe Q₀ w).eval ((S.psiGLR w).val *ᵥ x) = ((S.dR w)⁻¹) ^ 2 * (S.Q1R w).eval x := by
  have h1 := S.hess1 w
  rw [hessian_QRe', one_smul] at h1
  apply mul_left_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0)
  calc 2 * (QRe Q₀ w).eval ((S.psiGLR w).val *ᵥ x)
      = qH (hesAt Q₀ (σR w)) ((S.dR w)⁻¹ • ((S.PAt (σR w)).val *ᵥ x)) := by
        rw [← hessian_QRe' Q₀ w, ← two_mul_eval_real, psiGLR_val, smul_mulVec]
    _ = ((S.dR w)⁻¹) ^ 2 * qH (((S.PAt (σR w)).val)ᵀ * hesAt Q₀ (σR w) * (S.PAt (σR w)).val) x := by
        rw [qH_smul, qH_mulVec_eq]
    _ = ((S.dR w)⁻¹) ^ 2 * qH (S.Q1R w).hessian x := by rw [h1]
    _ = 2 * (((S.dR w)⁻¹) ^ 2 * (S.Q1R w).eval x) := by rw [two_mul_eval_real]; ring

theorem hca_R : σR w ρ = ((S.dR w)⁻¹) ^ 2 * S.mR w := by
  have hd := S.dR_ne_zero w
  rw [S.mR_eq w]
  field_simp

theorem sq_inv_ne_zero : ((S.dR w)⁻¹) ^ 2 ≠ 0 := pow_ne_zero _ (inv_ne_zero (S.dR_ne_zero w))

/-- **The sphere map** $\psi : \{Q_1^w = \sigma(m_0)\}\to\{Q_0^w = \sigma(\rho)\}$, $x\mapsto d^{-1}Gx$. -/
def psiR : Sph (S.Q1R w) (S.mR w) ≃ᵐ Sph (QRe Q₀ w) (σR w ρ) :=
  sphTEquiv (S.psiGLR w) (S.sq_inv_ne_zero w) (S.hca_R w) (S.eval_psiGLR w)

theorem psiR_val (x : Sph (S.Q1R w) (S.mR w)) :
    ((S.psiR w x : Sph (QRe Q₀ w) (σR w ρ)) : Fin (k + 1) → ℝ) = (S.psiGLR w).val *ᵥ x.1 := rfl

/-- $\det(d^{-1}G)$ in terms of $\det G$. -/
theorem abs_ratio :
    |((S.dR w)⁻¹) ^ 2| / |((S.psiGLR w : GL (Fin (k + 1)) ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ).det| =
      |S.dR w| ^ (k + 1) / (|S.dR w| ^ 2 * |(S.PAt (σR w)).val.det|) := by
  have hd : 0 < |S.dR w| := abs_pos.mpr (S.dR_ne_zero w)
  have hg : 0 < |(S.PAt (σR w)).val.det| := abs_pos.mpr (det_GL_ne_zero' _)
  rw [show ((S.psiGLR w : GL (Fin (k + 1)) ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) =
      (S.dR w)⁻¹ • (S.PAt (σR w)).val from rfl, Matrix.det_smul, Fintype.card_fin, abs_mul, abs_pow, abs_pow,
    abs_inv]
  have hp : |S.dR w| ^ (k + 1) ≠ 0 := (pow_pos hd _).ne'
  field_simp
  rw [one_div, inv_pow, inv_mul_cancel₀ hp]

include hρ in
/-- **$\psi_*\operatorname{sig}_1 = b\operatorname{sig}_0$** at $w$, $b = |d|^{k+1}/(|d|^2|\det G|)$. -/
theorem map_psiR :
    (SphereLeray.sig (S.Q1R w) (S.mR w)).map (S.psiR w) =
      ENNReal.ofReal (|S.dR w| ^ (k + 1) / (|S.dR w| ^ 2 * |(S.PAt (σR w)).val.det|)) •
        SphereLeray.sig (QRe Q₀ w) (σR w ρ) := by
  have h := map_sig_transport (Q := QRe Q₀ w) (Q₁ := S.Q1R w) ((map_ne_zero _).mpr hρ) (S.mR_ne_zero w)
    (S.sq_inv_ne_zero w) (S.hca_R w) (S.psiGLR w) (S.eval_psiGLR w)
  rw [abs_ratio] at h
  exact h

/-! ### Our section and embedding at $w$ -/

/-- **Our section at $w$** on the real sphere (the two-reflection section). -/
def secSOR (x : Sph (QRe Q₀ w) (σR w ρ)) : ArchSO (QRe Q₀ w) :=
  ArchSOInst.mk _ (S.secArchGL hρ two_ne_zero (σR w) x.1 ((mem_sphR_iff Q₀ ρ w x.1).mp x.2))
    (mem_soReal_of Q₀ (σR w) (S.secArchGL_mem hρ two_ne_zero _ _ _).1
      (S.secArchGL_mem hρ two_ne_zero _ _ _).2)

theorem secSOR_mat (x : Sph (QRe Q₀ w) (σR w ρ)) :
    ArchSOInst.mat _ (S.secSOR hρ w x) =
      (S.secArchGL hρ two_ne_zero (σR w) x.1 ((mem_sphR_iff Q₀ ρ w x.1).mp x.2)).val := rfl

/-- **Agreement with the adelic section**: the $w$-component of `secInf` is `secSOR` (on the nose). -/
theorem secInf_fst (y : adelicSphere Q₀ ρ) :
    (S.secInf hρ y).1 w = S.secSOR hρ w ⟨adR y.1 w, (mem_sphR_iff Q₀ ρ w _).mpr (y.2.1 w)⟩ := rfl

/-- **Agreement on matrices** between the adelic section at $w$ and `secSOR`. -/
theorem secInf_fst_mat (y : adelicSphere Q₀ ρ) :
    ArchSOInst.mat _ ((S.secInf hρ y).1 w) =
      (S.secArchGL hρ two_ne_zero (σR w) (adR y.1 w) (y.2.1 w)).val := rfl

/-- **Our embedding at $w$** is the $w$-component of the adelic `iota` (on the nose). -/
theorem iota_fst (g : SOAdele S.C.Q') : (S.iota g).1.1 w = S.iotaR w (g.1.1 w) := rfl

theorem iotaR_mat (h : ArchSO (QRe S.C.Q' w)) :
    ArchSOInst.mat _ (S.iotaR w h) = conjBlock (S.PAt (σR w)).val (ArchSOInst.mat _ h) :=
  conjBlockGL_val _ _

include hρ in
theorem measurable_secSOR : Measurable (S.secSOR hρ w) := by
  refine measurable_archSO_of ?_ ?_
  · exact (measurable_secP _ _ (S.measurableSet_bArch hρ (σR w))).comp measurable_subtype_coe
  · exact (measurable_secPInv _ _ (S.measurableSet_bArch hρ (σR w))).comp measurable_subtype_coe

/-! ### The split side: the transported section -/

/-- **The transported section** $s_1(x) = \varphi(s_w(\psi x))$ on the split sphere. -/
def sec1R (x : Sph (S.Q1R w) (S.mR w)) : ArchSO (S.Q1R w) := S.phiR w (S.secSOR hρ w (S.psiR w x))

theorem sec1R_mulVec (x : Sph (S.Q1R w) (S.mR w)) :
    ArchSOInst.mat _ (S.sec1R hρ w x) *ᵥ (e₀ : Fin (k + 1) → ℝ) = x.1 := by
  have hs := S.secArchGL_mulVec hρ two_ne_zero (σR w) (S.psiR w x).1
    ((mem_sphR_iff Q₀ ρ w _).mp (S.psiR w x).2)
  have hmat : ArchSOInst.mat _ (S.secSOR hρ w (S.psiR w x)) =
      (S.secArchGL hρ two_ne_zero (σR w) (S.psiR w x).1
        ((mem_sphR_iff Q₀ ρ w _).mp (S.psiR w x).2)).val := rfl
  rw [sec1R, mat_phiR, ← mulVec_mulVec, ← mulVec_mulVec, e₀_eq_single,
    show (Pi.single 0 1 : Fin (k + 1) → ℝ) = e0 from rfl, S.PAt_mulVec_e0 (σR w), mulVec_smul, hmat,
    show (fun i => σR w (S.ξ.1 i)) = (S.sphereDataAt hρ (σR w)).x₀ from rfl, hs, psiR_val, psiGLR_val,
    smul_mulVec, smul_smul, mul_inv_cancel₀ (S.dR_ne_zero w), one_smul, mulVec_mulVec, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, one_mulVec]

include hρ in
theorem measurable_sec1R : Measurable (S.sec1R hρ w) :=
  (S.continuous_phiR w).measurable.comp ((S.measurable_secSOR hρ w).comp (S.psiR w).measurable)

/-- **The transported section as an `OrbitalReal.SphSection`** for $\langle\sigma(m_0)\rangle\perp Q'^w$. -/
def sphSecR : OrbitalReal.SphSection (S.mR w) (QRe S.C.Q' w) where
  toFun := S.sec1R hρ w
  measurable := S.measurable_sec1R hρ w
  spec := S.sec1R_mulVec hρ w

theorem iota_injective' (c : ℝ) {m : ℕ} (Q' : QuadForm ℝ m) : Function.Injective (OrbitalReal.iota c Q') := by
  intro h h' e
  have := congrArg (fun g : ArchSO (splitForm c Q') => ArchSOInst.mat _ g) e
  simp only [OrbitalReal.mat_iota] at this
  exact Subtype.ext (Units.ext (cornerMat_injective_right this))

theorem orbR_injective :
    Function.Injective fun p : Sph (S.Q1R w) (S.mR w) × ArchSO (QRe S.C.Q' w) =>
      S.sec1R hρ w p.1 * OrbitalReal.iota (S.mR w) (QRe S.C.Q' w) p.2 := by
  rintro ⟨x, h⟩ ⟨x', h'⟩ e
  simp only at e
  have hx : x = x' := Subtype.ext (by
    have := congrArg (fun g : ArchSO (S.Q1R w) => ArchSOInst.mat _ g *ᵥ (e₀ : Fin (k + 1) → ℝ)) e
    simp only [ArchSOInst.mat_mul, ← mulVec_mulVec, OrbitalReal.iota_mulVec_e₀] at this
    rwa [S.sec1R_mulVec hρ w, S.sec1R_mulVec hρ w] at this)
  subst hx
  exact Prod.ext rfl (iota_injective' _ _ (mul_left_cancel e))

theorem phiR_iotaR (h : ArchSO (QRe S.C.Q' w)) :
    S.phiR w (S.iotaR w h) = OrbitalReal.iota (S.mR w) (QRe S.C.Q' w) h := by
  apply Subtype.ext; apply Units.ext
  show ArchSOInst.mat _ (S.phiR w (S.iotaR w h)) = ArchSOInst.mat _ (OrbitalReal.iota (S.mR w) (QRe S.C.Q' w) h)
  rw [mat_phiR, iotaR_mat, OrbitalReal.mat_iota (S.mR w) (QRe S.C.Q' w) h, conjBlock, ← Matrix.coe_units_inv]
  simp only [← Matrix.mul_assoc]
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.mul_one]

/-! ### The local identity -/

/-- **The local constant at the real place $w$**:
$|\det G|_w^{N+1}\cdot\frac{|d|_w^{k+1}}{|d|_w^{2}|\det G|_w}\cdot|2m_0|_w^{-k}$ ($N = k+1$), the product of the
conjugation ratio, the sphere-transport constant of $x\mapsto d^{-1}Gx$ and the orbital $|2m_0|^{-k}$. -/
def cReal : ℝ≥0∞ :=
  ENNReal.ofReal (|(S.PAt (σR w)).val.det| ^ (k + 1 + 1)) *
    ENNReal.ofReal (|S.dR w| ^ (k + 1) / (|S.dR w| ^ 2 * |(S.PAt (σR w)).val.det|)) *
    ENNReal.ofReal ((|2 * S.mR w| ^ k)⁻¹)

include hρ in
/-- **Closed form**: $c_w = \big|\det G/d\big|_w^{k+1}\,|2\sigma_w(\rho)|^{-k}$. -/
theorem cReal_eq : S.cReal w =
    ENNReal.ofReal (|(S.PAt (σR w)).val.det / S.dR w| ^ (k + 1) * (|2 * σR w ρ| ^ k)⁻¹) := by
  have hd : 0 < |S.dR w| := abs_pos.mpr (S.dR_ne_zero w)
  have hg : 0 < |(S.PAt (σR w)).val.det| := abs_pos.mpr (det_GL_ne_zero' _)
  have hr : 0 < |σR w ρ| := abs_pos.mpr ((map_ne_zero _).mpr hρ)
  rw [cReal, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [S.mR_eq w, abs_div, abs_mul, abs_mul, abs_pow, abs_two, abs_mul]
  generalize |(S.PAt (σR w)).val.det| = g at *
  generalize |S.dR w| = d at *
  generalize |σR w ρ| = r at *
  have e1 : (2 * (d ^ 2 * r)) ^ k = 2 ^ k * d ^ (2 * k) * r ^ k := by
    rw [mul_pow, mul_pow, ← pow_mul]; ring
  rw [e1, div_pow, pow_succ, pow_succ, mul_pow]
  field_simp
  ring

include hρ in
theorem cReal_ne_top : S.cReal w ≠ ⊤ := by
  rw [S.cReal_eq hρ w]; exact ENNReal.ofReal_ne_top

include hρ in
theorem cReal_ne_zero : S.cReal w ≠ 0 := by
  have hd : 0 < |S.dR w| := abs_pos.mpr (S.dR_ne_zero w)
  have hg : 0 < |(S.PAt (σR w)).val.det| := abs_pos.mpr (det_GL_ne_zero' _)
  have hr : 0 < |σR w ρ| := abs_pos.mpr ((map_ne_zero _).mpr hρ)
  rw [S.cReal_eq hρ w]
  refine (ENNReal.ofReal_pos.mpr ?_).ne'
  rw [abs_div]
  have : 0 < |2 * σR w ρ| := abs_pos.mpr (mul_ne_zero two_ne_zero ((map_ne_zero _).mpr hρ))
  positivity

include hQ hρ in
/-- **The local orbital identity at a real place, for our section and embedding** (set form):
$\mu_w(s_w(A)\,\iota_w(B)) = c_w\,\operatorname{sig}(A)\,\mu'_w(B)$. -/
theorem localFib_real {A : Set (Sph (QRe Q₀ w) (σR w ρ))} (hA : MeasurableSet A)
    {B : Set (ArchSO (QRe S.C.Q' w))} (hB : MeasurableSet B)
    (hE : MeasurableSet (secMulImage (S.secSOR hρ w) (S.iotaR w) A B))
    (hφE : MeasurableSet (S.phiR w '' secMulImage (S.secSOR hρ w) (S.iotaR w) A B)) :
    LerayReal.lerayMeasure (QRe Q₀ w) (gramDetR_QRe_ne_zero Q₀ hQ w)
        (secMulImage (S.secSOR hρ w) (S.iotaR w) A B) =
      S.cReal w * SphereLeray.sig (QRe Q₀ w) (σR w ρ) A *
        LerayReal.lerayMeasure (QRe S.C.Q' w) (gramDetR_QRe_ne_zero S.C.Q' S.C.hQ' w) B := by
  have hm0 := S.mR_ne_zero w
  have hQ' := gramDetR_QRe_ne_zero S.C.Q' S.C.hQ' w
  have hfib := OrbitalReal.lerayMeasure_orbital hm0 hQ' (S.sphSecR hρ w)
  have := LerayReal.isHaarMeasure_lerayMeasure hQ'
  have := sigmaFinite_sig (Q := S.Q1R w) hm0
  exact measure_mul_image_eq (S.phiR w) (S.phiR_injective w) (S.continuous_phiR w).measurable _ _ _
    (S.map_phiR hQ w) (S.psiR w) (SphereLeray.sig (QRe Q₀ w) (σR w ρ)) (SphereLeray.sig (S.Q1R w) (S.mR w)) _
    (S.map_psiR hρ w) (LerayReal.lerayMeasure (QRe S.C.Q' w) hQ') (S.sec1R hρ w)
    (OrbitalReal.iota (S.mR w) (QRe S.C.Q' w)) (iota_injective' _ _) (S.orbR_injective hρ w)
    (OrbitalReal.measurable_orb (S.sphSecR hρ w)) _ hfib (S.secSOR hρ w) (S.iotaR w) (S.phiR_iotaR w)
    (fun _ => 1) measurable_const (fun x => by rw [map_one, mul_one]; rfl) hA hB hE hφE

/-! ### Measurability of the images (Lusin–Souslin) -/

theorem secMulImage_eq_imageR {X G : Type*} [Mul G] (s : X → G) (ι : ArchSO (QRe S.C.Q' w) → G) (A : Set X)
    (B : Set (ArchSO (QRe S.C.Q' w))) :
    secMulImage s ι A B = (fun p : X × ArchSO (QRe S.C.Q' w) => s p.1 * ι p.2) '' (A ×ˢ B) := by
  ext g
  simp only [secMulImage, Set.mem_ofPred_eq, mem_image, mem_prod, Prod.exists]
  constructor
  · rintro ⟨y, hy, h, hh, rfl⟩; exact ⟨y, h, ⟨hy, hh⟩, rfl⟩
  · rintro ⟨y, h, ⟨hy, hh⟩, rfl⟩; exact ⟨y, hy, h, hh, rfl⟩

theorem secSOR_iotaR_mulVec (y : Sph (QRe Q₀ w) (σR w ρ)) (h : ArchSO (QRe S.C.Q' w)) :
    ArchSOInst.mat _ (S.secSOR hρ w y * S.iotaR w h) *ᵥ (S.sphereDataAt hρ (σR w)).x₀ = y.1 := by
  rw [ArchSOInst.mat_mul, ← mulVec_mulVec,
    show ArchSOInst.mat _ (S.iotaR w h) = (conjBlockGL (S.PAt (σR w)) (ArchSO.incl _ h)).val from rfl,
    S.conjBlockGL_fix hρ (σR w)]
  exact S.secArchGL_mulVec hρ two_ne_zero (σR w) y.1 ((mem_sphR_iff Q₀ ρ w y.1).mp y.2)

theorem secSOR_iotaR_injective :
    Function.Injective fun p : Sph (QRe Q₀ w) (σR w ρ) × ArchSO (QRe S.C.Q' w) =>
      S.secSOR hρ w p.1 * S.iotaR w p.2 := by
  rintro ⟨y, h⟩ ⟨y', h'⟩ e
  simp only at e
  have hy : y = y' := Subtype.ext (by
    rw [← S.secSOR_iotaR_mulVec hρ w y h, ← S.secSOR_iotaR_mulVec hρ w y' h', e])
  subst hy
  have e2 := mul_left_cancel e
  have e3 := congrArg (fun g : ArchSO (QRe Q₀ w) => ArchSOInst.mat _ g) e2
  have e4 : conjBlockGL (S.PAt (σR w)) (ArchSO.incl _ h) = conjBlockGL (S.PAt (σR w)) (ArchSO.incl _ h') :=
    Units.ext e3
  exact Prod.ext rfl (Subtype.ext (conjBlockGL_injective _ e4))

include hQ hρ in
/-- **The sets $s_w(A)\iota_w(B)$ and $\varphi(s_w(A)\iota_w(B))$ are measurable** (Lusin–Souslin). -/
theorem measurableSet_secMulImageR {A : Set (Sph (QRe Q₀ w) (σR w ρ))} (hA : MeasurableSet A)
    {B : Set (ArchSO (QRe S.C.Q' w))} (hB : MeasurableSet B) :
    MeasurableSet (secMulImage (S.secSOR hρ w) (S.iotaR w) A B) ∧
      MeasurableSet (S.phiR w '' secMulImage (S.secSOR hρ w) (S.iotaR w) A B) := by
  have : PolishSpace (Sph (QRe Q₀ w) (σR w ρ)) := (isClosed_sph _ _).polishSpace
  have hm : Measurable fun p : Sph (QRe Q₀ w) (σR w ρ) × ArchSO (QRe S.C.Q' w) =>
      S.secSOR hρ w p.1 * S.iotaR w p.2 :=
    ((S.measurable_secSOR hρ w).comp measurable_fst).mul ((S.continuous_iotaR w).measurable.comp measurable_snd)
  have hE : MeasurableSet (secMulImage (S.secSOR hρ w) (S.iotaR w) A B) := by
    rw [S.secMulImage_eq_imageR w]
    exact (hm.measurableEmbedding (S.secSOR_iotaR_injective hρ w)).measurableSet_image.mpr (hA.prod hB)
  exact ⟨hE, ((S.continuous_phiR w).measurable.measurableEmbedding (S.phiR_injective w)).measurableSet_image.mpr hE⟩

include hQ hρ in
/-- **The local orbital identity at a real place** (set form, no side conditions). -/
theorem localFib_real' {A : Set (Sph (QRe Q₀ w) (σR w ρ))} (hA : MeasurableSet A)
    {B : Set (ArchSO (QRe S.C.Q' w))} (hB : MeasurableSet B) :
    LerayReal.lerayMeasure (QRe Q₀ w) (gramDetR_QRe_ne_zero Q₀ hQ w)
        (secMulImage (S.secSOR hρ w) (S.iotaR w) A B) =
      S.cReal w * SphereLeray.sig (QRe Q₀ w) (σR w ρ) A *
        LerayReal.lerayMeasure (QRe S.C.Q' w) (gramDetR_QRe_ne_zero S.C.Q' S.C.hQ' w) B :=
  S.localFib_real hρ hQ w hA hB (S.measurableSet_secMulImageR hρ hQ w hA hB).1
    (S.measurableSet_secMulImageR hρ hQ w hA hB).2

end AdelicSphereSetup

end QuadFormsKB.Tamagawa.Measure.Weil

end
