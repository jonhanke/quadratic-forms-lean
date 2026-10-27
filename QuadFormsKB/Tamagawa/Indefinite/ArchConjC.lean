/-
# The complex-place fibration at an arbitrary vector (Siegel's formula for indefinite forms)

**Layer:** complex analysis on $SO(Q)(\mathbb C)$ (the Leray measures, the orbital identity).
This is the complex-place analogue of `ArchConj.lean` (real places).

Let $Q$ be a nondegenerate complex quadratic form in $n = m+1\ge2$ variables, $c\ne0$, and
$S_c = \{Q = c\}$ (`SphereLerayC.SphC`) with its complex Leray measure $\sigma_c = dx/dQ$ (`SphereLerayC.sigC`).
The group $G = SO(Q)(\mathbb C)$ acts on $\mathbb C^n$ by $g\cdot v = gv$ (`archSOCAction`). `OrbitalComplex.lean`
proved the orbital identity only for the split form $\langle c\rangle\perp Q'$ at the base
point $e_0$. Here it is moved to **every** point $y\in S_c$ by a change of basis $P$ with $Pe_0 = y$ and
$Q\circ P = \langle c\rangle\perp Q'_y$ (`OrthFq.exists_split`, `eq_splitForm_of`).

**Proves** (all unconditional, standard axioms only)
* `exists_splitFrameC`: split frames exist at every $y$ with $Q(y) = c\ne0$;
* `SplitFrameC.lerayMeasureC_eq_map_coord` (**the complex-place fibration at $y$**): for $m\ge1$,
  $$\mu_Q = |2c|_{\mathbb C}^{-m}\cdot\mathrm{coord}_*(\sigma_c\otimes\mu_{H_y}),\qquad
  \mathrm{coord}(x, h) = hS(x)^{-1},\quad |z|_{\mathbb C} = |z|^2,$$
  where $\mu_{H_y}$ (`stabMeasure`) is the Haar measure on $H_y = \operatorname{Stab}_G(y)\cong SO(Q'_y)(\mathbb C)$
  determined by this identity (an explicit positive multiple of the image of the Leray measure of $Q'_y$; the
  change of variables $x\mapsto Px$ on spheres has Jacobian $\|\det P\|^2$, `map_sphEquivC_sigC`);
* `complexArchFibration` (**packaging**): these data form an `ArchFibration` over $S_c$ with the single constant
  $|2c|_{\mathbb C}^{-m}$, the input of the classical theta unfolding (`ThetaUnfold.lean`);
* `SplitFrameC.isMulRightInvariant_stabMeasure`, `isMulRightInvariant_complexStabMeasure`: the stabilizer measures
  are right invariant ($H_y\cong SO(Q')(\mathbb C)$ is unimodular).

**Outside results used:** Mathlib's `isMulLeftInvariant_eq_smul` (uniqueness of Haar measure); the library's
`lerayMeasureC_orbital`, `sphSectionC`, `exists_iotaC_eq_of_mulVec_e₀`,`conjSOC` (similarity conjugation),
`sphEquivC`, `map_sphEquivC_sigC`, `exists_split` (`OrthFq.lean`), `eq_splitForm_of`, `isMulRightInvariant_lerayMeasureC`.
-/
import QuadFormsKB.Tamagawa.Indefinite.ArchConj
import QuadFormsKB.Tamagawa.Indefinite.ArchUnique
import QuadFormsKB.Tamagawa.Indefinite.ClassicalSetup
import QuadFormsKB.Tamagawa.Indefinite.ThetaUnfold
import QuadFormsKB.Tamagawa.Measure.OrbitalComplexStab
import QuadFormsKB.Tamagawa.Measure.LerayUnimodularC
import QuadFormsKB.Tamagawa.Measure.ConeReal
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarArchComplex
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereLocalComplex
import QuadFormsKB.Tamagawa.OrthFq
import QuadFormsKB.Tamagawa.AlphaLawMoves

open MeasureTheory Measure Matrix MulAction Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa
open QuadFormsKB.Tamagawa.Measure.Weil
open QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.Measure.SphereLerayC
open QuadFormsKB.Tamagawa.Measure.OrbitalComplex

/-! ### Split frames at a vector (complex place) -/

section Frame

variable {m : ℕ}

local notation "𝕄" => Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ

/-- **A split frame at `y`** for the complex form `Q` in $m+1$ variables and the value `c`: a change of basis
$P\in GL_{m+1}(\mathbb C)$ (`P`) with $Pe_0 = y$ (`base`) and $Q\circ P = \langle c\rangle\perp Q'$ (`hess`, stated on
Hessians: $H_{\langle c\rangle\perp Q'} = P^{\mathsf T}H_QP$), where $Q'$ (`Q'`) is the form of $y^\perp$ in the basis
given by the last $m$ columns of $P$. Data with its defining properties. Fields: `P`, `Q'`, `hess`, `base`. -/
structure SplitFrameC (Q : QuadForm ℂ (m + 1)) (c : ℂ) (y : Fin (m + 1) → ℂ) where
  /-- The change of basis. -/
  P : GL (Fin (m + 1)) ℂ
  /-- The form on the orthogonal complement of `y`. -/
  Q' : QuadForm ℂ m
  /-- $Q\circ P = \langle c\rangle\perp Q'$. -/
  hess : (splitForm c Q').hessian = (P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)ᵀ * Q.hessian * P
  /-- $Pe_0 = y$. -/
  base : (P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) *ᵥ e₀ = y

theorem e₀_eq_singleC : (e₀ : Fin (m + 1) → ℂ) = Pi.single 0 1 := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp [Fin.succ_ne_zero]

/-- **Split frames exist** at every vector `y` with $Q(y) = c\ne0$ (orthogonal splitting, `OrthFq.exists_split`). -/
theorem exists_splitFrameC (Q : QuadForm ℂ (m + 1)) {c : ℂ} (hc : c ≠ 0) {y : Fin (m + 1) → ℂ}
    (hy : Q.eval y = c) : Nonempty (SplitFrameC Q c y) := by
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
    by_contra h
    push Not at h
    have hy0 : y = (0 : ℂ) • y := by rw [zero_smul]; exact funext h
    apply hc
    rw [← hy, hy0, eval_smulC]
    ring
  obtain ⟨g, hg0, hsplit⟩ := QuadForm.exists_split Q y
    (by rw [hy]; exact (mul_ne_zero two_ne_zero hc).isUnit) i hi.isUnit
  have hcol0 : (fun l => g.val l 0) = y := by rw [← hg0, mulVec_single_one]; rfl
  have h00 : (Q.compMat g.val).coeff 0 0 = c := by
    rw [QuadForm.compMat_coeff]
    simp [hcol0, hy]
  have hQ := eq_splitForm_of (Q.compMat g.val) hsplit
  rw [h00] at hQ
  refine ⟨⟨g, tailForm (Q.compMat g.val), ?_, ?_⟩⟩
  · rw [← hQ, QuadForm.hessian_compMat]
  · rw [e₀_eq_singleC]; exact hg0

theorem det_GL_ne_zeroC (P : GL (Fin (m + 1)) ℂ) : (P : 𝕄).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit P)).ne_zero

theorem norm_det_GL_pos (P : GL (Fin (m + 1)) ℂ) : (‖(P : 𝕄).det‖₊ ^ 2 : ℝ≥0) ≠ 0 :=
  pow_ne_zero _ (nnnorm_ne_zero_iff.mpr (det_GL_ne_zeroC P))

namespace SplitFrameC

variable {Q : QuadForm ℂ (m + 1)} {c : ℂ} {y : Fin (m + 1) → ℂ} (F : SplitFrameC Q c y)

theorem P_mul_P_inv : (F.P : 𝕄) * ((F.P⁻¹ : GL (Fin (m + 1)) ℂ) : 𝕄) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem P_inv_mul_P : ((F.P⁻¹ : GL (Fin (m + 1)) ℂ) : 𝕄) * (F.P : 𝕄) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem P_inv_base : ((F.P⁻¹ : GL (Fin (m + 1)) ℂ) : 𝕄) *ᵥ y = e₀ := by
  have h : ((F.P⁻¹ : GL (Fin (m + 1)) ℂ) : 𝕄) *ᵥ ((F.P : 𝕄) *ᵥ e₀) = e₀ := by
    rw [mulVec_mulVec, F.P_inv_mul_P, one_mulVec]
  rwa [F.base] at h

theorem gramC_split : gramC (splitForm c F.Q') = (F.P : 𝕄)ᵀ * gramC Q * (F.P : 𝕄) := by
  have := gramC_similar (G := F.P) (c := (1 : ℂ)) (Q := Q) (Q' := splitForm c F.Q')
    (by rw [one_smul]; exact F.hess)
  rwa [one_smul] at this

/-- $Q_1(x) = Q(Px)$ for the split form $Q_1 = \langle c\rangle\perp Q'$. -/
theorem eval_split (x : Fin (m + 1) → ℂ) :
    (splitForm c F.Q').eval x = Q.eval ((F.P : 𝕄) *ᵥ x) := by
  rw [eval_eq_gramC, eval_eq_gramC]
  show qH _ x = qH _ ((F.P : 𝕄) *ᵥ x)
  rw [AdelicSphereSetup.qH_mulVec_eq, F.gramC_split]

include F in
theorem eval_y : Q.eval y = c := by
  have h := F.eval_split e₀
  have h0 : (splitForm c F.Q').eval (e₀ : Fin (m + 1) → ℂ) = c := evalIn_splitForm_e₀ ℂ c F.Q'
  rw [h0, F.base] at h
  exact h.symm

theorem gramDetC_Q' (hQ : gramDetC Q ≠ 0) : gramDetC F.Q' ≠ 0 := by
  have h : gramDetC (splitForm c F.Q') = (F.P : 𝕄).det ^ 2 * gramDetC Q := by
    rw [gramDetC, gramDetC, F.gramC_split, det_mul, det_mul, det_transpose]; ring
  rw [gramDetC_splitForm] at h
  intro h0
  rw [h0, mul_zero] at h
  exact mul_ne_zero (pow_ne_zero 2 (det_GL_ne_zeroC F.P)) hQ h.symm

theorem hessC : (splitForm c F.Q').hessian = (1 : ℂ) • ((F.P : 𝕄)ᵀ * Q.hessian * (F.P : 𝕄)) := by
  rw [one_smul]; exact F.hess

/-- Conjugation by $P$: $SO(\langle c\rangle\perp Q')(\mathbb C)\cong SO(Q)(\mathbb C)$, $g\mapsto PgP^{-1}$
(the inverse of `conjSOC` with $c = 1$). -/
def conj (_hc : c ≠ 0) : ArchSOC (splitForm c F.Q') ≃ₜ* ArchSOC Q :=
  (conjSOC F.P (1 : ℂ) F.hessC one_ne_zero).symm

theorem mat_conj (hc : c ≠ 0) (g : ArchSOC (splitForm c F.Q')) :
    ArchSOC.mat Q (F.conj hc g) = (F.P : 𝕄) * ArchSOC.mat _ g * ((F.P⁻¹ : GL (Fin (m + 1)) ℂ) : 𝕄) := by
  show (((F.P * ArchSOC.incl _ g * F.P⁻¹ : GL (Fin (m + 1)) ℂ)) : 𝕄) = _
  rw [Units.val_mul, Units.val_mul]
  rfl

theorem continuous_conj (hc : c ≠ 0) : Continuous (F.conj hc) := (F.conj hc).continuous_toFun

theorem continuous_conj_symm (hc : c ≠ 0) : Continuous (F.conj hc).symm := (F.conj hc).continuous_invFun

/-- The sphere map $x\mapsto Px$, $S_c(Q_1)\to S_c(Q)$. -/
def fwd : SphC (splitForm c F.Q') c ≃ᵐ SphC Q c :=
  sphEquivC F.P (a := (1 : ℂ)) one_ne_zero (fun x => by rw [one_mul]; exact (F.eval_split x).symm)
    (one_mul c)

/-- The sphere map $x\mapsto P^{-1}x$, $S_c(Q)\to S_c(Q_1)$. -/
def bwd : SphC Q c → SphC (splitForm c F.Q') c := F.fwd.symm

theorem bwd_val (x : SphC Q c) :
    ((F.bwd x : SphC (splitForm c F.Q') c) : Fin (m + 1) → ℂ) = ((F.P⁻¹ : GL (Fin (m + 1)) ℂ) : 𝕄) *ᵥ x.1 := rfl

theorem bwd_fwd (x : SphC (splitForm c F.Q') c) : F.bwd (F.fwd x) = x := F.fwd.symm_apply_apply x

theorem measurable_bwd : Measurable F.bwd := F.fwd.symm.measurable

variable (hc : c ≠ 0) (hm : 1 ≤ m) (hQ : gramDetC Q ≠ 0)

/-- The explicit section for the split form. -/
def sphSec : SphSectionC c F.Q' := sphSectionC hc hm (F.gramDetC_Q' hQ)

/-- **The section at `y`**: $S(x) = P\,s(P^{-1}x)\,P^{-1}$, so that $S(x)\,y = x$. -/
def sec (x : SphC Q c) : ArchSOC Q := F.conj hc ((F.sphSec hc hm hQ).toFun (F.bwd x))

theorem sec_smul (x : SphC Q c) : F.sec hc hm hQ x • y = (x : Fin (m + 1) → ℂ) := by
  rw [sec, archSOC_smul_def, mat_conj, ← mulVec_mulVec, ← mulVec_mulVec, F.P_inv_base,
    (F.sphSec hc hm hQ).spec]
  show (F.P : 𝕄) *ᵥ (((F.P⁻¹ : GL (Fin (m + 1)) ℂ) : 𝕄) *ᵥ (x : Fin (m + 1) → ℂ)) = x
  rw [mulVec_mulVec, F.P_mul_P_inv, one_mulVec]

theorem measurable_sec : Measurable (F.sec hc hm hQ) :=
  (F.continuous_conj hc).measurable.comp ((F.sphSec hc hm hQ).measurable.comp F.measurable_bwd)

theorem sec_fwd (x : SphC (splitForm c F.Q') c) :
    F.sec hc hm hQ (F.fwd x) = F.conj hc ((F.sphSec hc hm hQ).toFun x) := by
  rw [sec, bwd_fwd]

theorem eval_archSOC_smul (g : ArchSOC Q) (v : Fin (m + 1) → ℂ) : Q.eval (g • v) = Q.eval v :=
  eval_mulVec_of_isometryC (ArchSOC.isometry Q g) v

include F in
/-- The orbit point $g^{-1}y\in S_c$. -/
def proj (g : ArchSOC Q) : SphC Q c := ⟨g⁻¹ • y, by show Q.eval _ = c; rw [eval_archSOC_smul, F.eval_y]⟩

include F in
theorem measurable_proj : Measurable F.proj :=
  ((continuous_archSOC_smul Q).comp (continuous_inv.prodMk continuous_const)).measurable.subtype_mk

/-- **The orbit coordinates at `y`**: $(x, h)\mapsto hS(x)^{-1}$, $S_c\times H_y\cong SO(Q)(\mathbb C)$. -/
def coord : OrbitCoord (stabilizer (ArchSOC Q) y).subtype (Subtype.val : SphC Q c → Fin (m + 1) → ℂ) y :=
  orbitCoordOfSection Subtype.val Subtype.val_injective y (F.sec hc hm hQ) (F.measurable_sec hc hm hQ)
    (F.sec_smul hc hm hQ) F.proj F.measurable_proj fun _ => rfl

theorem conj_iota_mem (h : ArchSOC F.Q') :
    F.conj hc (iotaC c F.Q' h) ∈ stabilizer (ArchSOC Q) y := by
  rw [mem_stabilizer_iff, archSOC_smul_def, mat_conj, ← mulVec_mulVec, ← mulVec_mulVec, F.P_inv_base,
    iotaC_mulVec_e₀, F.base]

/-- **The stabilizer of `y`** is $P\,\iota(SO(Q'))\,P^{-1}$: the homomorphism $SO(Q')(\mathbb C)\to H_y$. -/
def stabHom : ArchSOC F.Q' →* stabilizer (ArchSOC Q) y :=
  ((F.conj hc).toMulEquiv.toMonoidHom.comp (iotaC c F.Q')).codRestrict _ (F.conj_iota_mem hc)

theorem coe_stabHom (h : ArchSOC F.Q') : (F.stabHom hc h : ArchSOC Q) = F.conj hc (iotaC c F.Q' h) := rfl

theorem measurable_stabHom : Measurable (F.stabHom hc) :=
  ((F.continuous_conj hc).comp (continuous_iotaC c F.Q')).measurable.subtype_mk

theorem continuous_stabHom : Continuous (F.stabHom hc) :=
  ((F.continuous_conj hc).comp (continuous_iotaC c F.Q')).subtype_mk _

theorem stabHom_surjective : Function.Surjective (F.stabHom hc) := by
  rintro ⟨g, hg⟩
  have hfix : ArchSOC.mat _ ((F.conj hc).symm g) *ᵥ (e₀ : Fin (m + 1) → ℂ) = e₀ := by
    have h1 : ArchSOC.mat Q (F.conj hc ((F.conj hc).symm g)) *ᵥ y = y := by
      rw [ContinuousMulEquiv.apply_symm_apply]; exact mem_stabilizer_iff.mp hg
    rw [mat_conj] at h1
    have hM : ArchSOC.mat _ ((F.conj hc).symm g) * ((F.P⁻¹ : GL (Fin (m + 1)) ℂ) : 𝕄) =
        ((F.P⁻¹ : GL (Fin (m + 1)) ℂ) : 𝕄) * ((F.P : 𝕄) * ArchSOC.mat _ ((F.conj hc).symm g) *
          ((F.P⁻¹ : GL (Fin (m + 1)) ℂ) : 𝕄)) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, F.P_inv_mul_P, Matrix.one_mul]
    rw [← F.P_inv_base, mulVec_mulVec, hM, ← mulVec_mulVec, h1]
  obtain ⟨h, hh⟩ := exists_iotaC_eq_of_mulVec_e₀ hc ((F.conj hc).symm g) hfix
  refine ⟨h, Subtype.ext ?_⟩
  rw [coe_stabHom, hh, ContinuousMulEquiv.apply_symm_apply]

theorem stabHom_injective : Function.Injective (F.stabHom hc) := by
  intro a b h
  have h1 : F.conj hc (iotaC c F.Q' a) = F.conj hc (iotaC c F.Q' b) := by
    rw [← coe_stabHom, ← coe_stabHom, h]
  exact iotaC_injective ((F.conj hc).injective h1)

theorem isHaarMeasure_map_conj :
    ((lerayMeasureC (splitForm c F.Q') (gramDetC_splitForm_ne_zero hc (F.gramDetC_Q' hQ))).map
      (F.conj hc)).IsHaarMeasure := by
  haveI := isHaarMeasure_lerayMeasureC (gramDetC_splitForm_ne_zero hc (F.gramDetC_Q' hQ))
  exact MulEquiv.isHaarMeasure_map _ (F.conj hc).toMulEquiv (F.continuous_conj hc) (F.continuous_conj_symm hc)

/-- **The Haar constant of the conjugation** $\kappa_P$: $(g\mapsto PgP^{-1})_*\mu_{Q_1} = \kappa_P\,\mu_Q$
(`map_conj_lerayMeasureC`; uniqueness of Haar measure). -/
def haarConst : ℝ≥0 := by
  haveI := isHaarMeasure_lerayMeasureC hQ
  haveI := F.isHaarMeasure_map_conj hc hQ
  exact haarScalarFactor ((lerayMeasureC (splitForm c F.Q')
    (gramDetC_splitForm_ne_zero hc (F.gramDetC_Q' hQ))).map (F.conj hc)) (lerayMeasureC Q hQ)

theorem map_conj_lerayMeasureC :
    (lerayMeasureC (splitForm c F.Q') (gramDetC_splitForm_ne_zero hc (F.gramDetC_Q' hQ))).map (F.conj hc) =
      F.haarConst hc hQ • lerayMeasureC Q hQ := by
  haveI := F.isHaarMeasure_map_conj hc hQ
  haveI := isHaarMeasure_lerayMeasureC hQ
  exact isMulLeftInvariant_eq_smul _ _

theorem haarConst_pos : 0 < F.haarConst hc hQ := by
  haveI := F.isHaarMeasure_map_conj hc hQ
  haveI := isHaarMeasure_lerayMeasureC hQ
  exact haarScalarFactor_pos_of_isHaarMeasure _ _

/-- The Jacobian $\|\det P\|^2$ of $x\mapsto Px$ on the complex spheres, as an extended nonnegative real. -/
def jac : ℝ≥0∞ := ((‖(F.P : 𝕄).det‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)

theorem jac_ne_zero : F.jac ≠ 0 := by
  have := norm_det_GL_pos F.P
  unfold jac
  exact_mod_cast this

theorem jac_ne_top : F.jac ≠ ⊤ := ENNReal.coe_ne_top

/-- **The measure on the stabilizer $H_y$**: $\mu_{H_y} = (\kappa_P\,\|\det P\|^2)^{-1}\cdot
(h\mapsto P\iota(h)P^{-1})_*\mu_{Q'}$, the Haar measure for which $\mu_Q = |2c|_{\mathbb C}^{-m}\,
\sigma_c\otimes\mu_{H_y}$ (`lerayMeasureC_eq_map_coord`). -/
def stabMeasure : Measure (stabilizer (ArchSOC Q) y) :=
  ((((F.haarConst hc hQ : ℝ≥0) : ℝ≥0∞))⁻¹ * F.jac⁻¹) •
    (lerayMeasureC F.Q' (F.gramDetC_Q' hQ)).map (F.stabHom hc)

theorem coord_apply (x : SphC Q c) (h : stabilizer (ArchSOC Q) y) :
    (F.coord hc hm hQ).coord (x, h) = (h : ArchSOC Q) * (F.sec hc hm hQ x)⁻¹ := rfl

theorem sigC_eq_smul_map_fwd (hc : c ≠ 0) :
    sigC Q c = F.jac • (sigC (splitForm c F.Q') c).map F.fwd := by
  have h := map_sphEquivC_sigC F.P (a := (1 : ℂ)) one_ne_zero
    (fun x => by rw [one_mul]; exact (F.eval_split x).symm) (one_mul c) hc hc
  have hx : ((‖2 * c‖₊ ^ 2 : ℝ≥0)) ≠ 0 :=
    pow_ne_zero _ (nnnorm_ne_zero_iff.mpr (mul_ne_zero two_ne_zero hc))
  have hb : (((‖2 * c‖₊ ^ 2)⁻¹ * (‖(F.P : 𝕄).det‖₊ ^ 2)⁻¹ * ‖2 * c‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) = F.jac⁻¹ := by
    have : ((‖2 * c‖₊ ^ 2)⁻¹ * (‖(F.P : 𝕄).det‖₊ ^ 2)⁻¹ * ‖2 * c‖₊ ^ 2 : ℝ≥0) =
        (‖(F.P : 𝕄).det‖₊ ^ 2)⁻¹ := by
      rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hx, one_mul]
    rw [this, jac, ENNReal.coe_inv (norm_det_GL_pos F.P)]
  have h' : (sigC (splitForm c F.Q') c).map F.fwd = F.jac⁻¹ • sigC Q c := by
    rw [← hb]; exact h
  rw [h', smul_smul, ENNReal.mul_inv_cancel F.jac_ne_zero F.jac_ne_top, one_smul]

/-- **The complex-place fibration at `y`** (Weil 1982, Lemma 2.4.1 / Thm 2.4.3 at an arbitrary point of the
quadric): for every split frame at `y` (so $Q(y) = c$) and $m\ge1$,
$$\mu_Q = |2c|_{\mathbb C}^{-m}\cdot\mathrm{coord}_*(\sigma_c\otimes\mu_{H_y}),\qquad
\mathrm{coord}(x, h) = hS(x)^{-1}.$$ -/
theorem lerayMeasureC_eq_map_coord :
    lerayMeasureC Q hQ = (((‖2 * c‖₊ ^ (2 * m))⁻¹ : ℝ≥0) : ℝ≥0∞) •
      ((sigC Q c).prod (F.stabMeasure hc hQ)).map (F.coord hc hm hQ).coord := by
  have hQ' := F.gramDetC_Q' hQ
  have hQ1 := gramDetC_splitForm_ne_zero hc hQ'
  have hn1 : 1 ≤ m + 1 := by omega
  set k : ℝ≥0∞ := (((‖2 * c‖₊ ^ (2 * m))⁻¹ : ℝ≥0) : ℝ≥0∞) with hk
  set d := F.jac with hd
  set κ : ℝ≥0∞ := (F.haarConst hc hQ : ℝ≥0∞) with hκ
  set μ' := lerayMeasureC F.Q' hQ'
  set σ₁ := sigC (splitForm c F.Q') c
  set μ₁ := lerayMeasureC (splitForm c F.Q') hQ1
  set s := F.sphSec hc hm hQ
  haveI := sigmaFinite_sigC (Q := splitForm c F.Q') hc hn1
  haveI := sigmaFinite_sigC (Q := Q) hc hn1
  haveI := isHaarMeasure_lerayMeasureC hQ'
  haveI := isHaarMeasure_lerayMeasureC hQ1
  haveI := isHaarMeasure_lerayMeasureC hQ
  haveI := isMulRightInvariant_lerayMeasureC hQ'
  haveI := isMulRightInvariant_lerayMeasureC hQ1
  have hd0 : d ≠ 0 := F.jac_ne_zero
  have hκ0 : κ ≠ 0 := ENNReal.coe_ne_zero.mpr (F.haarConst_pos hc hQ).ne'
  -- the two images: σ_Q and μ_{H_y}
  have hprod : (sigC Q c).prod (F.stabMeasure hc hQ) =
      (d * (κ⁻¹ * d⁻¹)) • (σ₁.prod μ').map (Prod.map F.fwd (F.stabHom hc)) := by
    have hσ : sigC Q c = d • σ₁.map F.fwd := F.sigC_eq_smul_map_fwd hc
    rw [hσ, stabMeasure, Measure.prod_smul_left,
      Measure.prod_smul_right, smul_smul,
      map_prod_map _ _ F.fwd.measurable (F.measurable_stabHom hc)]
  -- the composite map
  have hcomp : (F.coord hc hm hQ).coord ∘ Prod.map F.fwd (F.stabHom hc) =
      F.conj hc ∘ (fun g => g⁻¹) ∘ orbC s ∘ Prod.map id (fun h => h⁻¹) := by
    funext p
    obtain ⟨x, h⟩ := p
    simp only [Function.comp_apply, Prod.map_apply, id]
    rw [coord_apply, coe_stabHom, sec_fwd, orbC, _root_.mul_inv_rev, map_inv, inv_inv, map_mul, map_inv]
  have hA : (σ₁.prod μ').map (Prod.map id fun h => h⁻¹) = σ₁.prod μ' := by
    rw [← map_prod_map _ _ measurable_id measurable_inv, Measure.map_id]
    congr 1
    exact QuadFormsKB.Tamagawa.Measure.ConeReal.inv_eq_self_of_unimodular μ'
  have hinv₁ : μ₁.map (fun g => g⁻¹) = μ₁ := QuadFormsKB.Tamagawa.Measure.ConeReal.inv_eq_self_of_unimodular μ₁
  have horb : μ₁ = k • (σ₁.prod μ').map (orbC s) := lerayMeasureC_orbital hc hQ' s
  have hmc := (F.coord hc hm hQ).coord.measurable
  have hmP : Measurable (Prod.map F.fwd (F.stabHom hc)) := F.fwd.measurable.prodMap (F.measurable_stabHom hc)
  have hmorb := measurable_orbC s
  have hmconj := (F.continuous_conj hc).measurable
  have hmP' : Measurable (Prod.map (id : SphC (splitForm c F.Q') c → _) fun h : ArchSOC F.Q' => h⁻¹) :=
    measurable_id.prodMap measurable_inv
  symm
  calc k • ((sigC Q c).prod (F.stabMeasure hc hQ)).map (F.coord hc hm hQ).coord
      = (k * (d * (κ⁻¹ * d⁻¹))) • (σ₁.prod μ').map
          ((F.coord hc hm hQ).coord ∘ Prod.map F.fwd (F.stabHom hc)) := by
        rw [hprod, Measure.map_smul _ hmc.aemeasurable, Measure.map_map hmc hmP, smul_smul]
    _ = (k * (d * (κ⁻¹ * d⁻¹))) • (((((σ₁.prod μ').map (Prod.map id fun h => h⁻¹)).map (orbC s)).map
          (fun g => g⁻¹)).map (F.conj hc)) := by
        rw [hcomp, Measure.map_map hmorb hmP', Measure.map_map measurable_inv (hmorb.comp hmP'),
          Measure.map_map hmconj (measurable_inv.comp (hmorb.comp hmP'))]
    _ = (d * (κ⁻¹ * d⁻¹)) • (((k • (σ₁.prod μ').map (orbC s)).map (fun g => g⁻¹)).map (F.conj hc)) := by
        rw [hA, Measure.map_smul _ measurable_inv.aemeasurable, Measure.map_smul _ hmconj.aemeasurable, smul_smul,
          mul_comm k]
    _ = (d * (κ⁻¹ * d⁻¹)) • (κ • lerayMeasureC Q hQ) := by
        rw [← horb, hinv₁, map_conj_lerayMeasureC]
        rfl
    _ = lerayMeasureC Q hQ := by
        have h1 : d * (κ⁻¹ * d⁻¹) * κ = 1 := by
          calc d * (κ⁻¹ * d⁻¹) * κ = (d * d⁻¹) * (κ⁻¹ * κ) := by ring
            _ = 1 := by
              rw [ENNReal.mul_inv_cancel hd0 F.jac_ne_top, ENNReal.inv_mul_cancel hκ0 ENNReal.coe_ne_top,
                one_mul]
        rw [smul_smul, h1, one_smul]

/-- $\mu_{H_y}$ is σ-finite: it is finite on the images of a compact exhaustion of $SO(Q')(\mathbb C)$. -/
theorem sigmaFinite_stabMeasure : SigmaFinite (F.stabMeasure hc hQ) := by
  haveI := isHaarMeasure_lerayMeasureC (F.gramDetC_Q' hQ)
  set K := compactCovering (ArchSOC F.Q')
  have hK : ∀ k, IsCompact (K k) := isCompact_compactCovering _
  have hS : ∀ k, MeasurableSet (F.stabHom hc '' K k) := fun k =>
    ((hK k).image (F.continuous_stabHom hc)).isClosed.measurableSet
  have hd0 : F.jac ≠ 0 := F.jac_ne_zero
  have hκ0 : ((F.haarConst hc hQ : ℝ≥0) : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (F.haarConst_pos hc hQ).ne'
  have hfin : ∀ k, F.stabMeasure hc hQ (F.stabHom hc '' K k) < ⊤ := by
    intro k
    rw [stabMeasure, Measure.smul_apply, Measure.map_apply (F.measurable_stabHom hc) (hS k),
      (F.stabHom_injective hc).preimage_image, smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hκ0))
      (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hd0))) (hK k).measure_lt_top
  have hspan : ⋃ k, F.stabHom hc '' K k = Set.univ := by
    rw [← Set.image_iUnion, iUnion_compactCovering, Set.image_univ, (F.stabHom_surjective hc).range_eq]
  exact ⟨⟨⟨fun k => F.stabHom hc '' K k, fun _ => trivial, hfin, hspan⟩⟩⟩

theorem isMulLeftInvariant_stabMeasure : (F.stabMeasure hc hQ).IsMulLeftInvariant := by
  haveI := isHaarMeasure_lerayMeasureC (F.gramDetC_Q' hQ)
  haveI := measurableMul_subgroup (stabilizer (ArchSOC Q) y)
  haveI := isMulLeftInvariant_map (μ := lerayMeasureC F.Q' (F.gramDetC_Q' hQ)) (F.stabHom hc).toMulHom
    (F.measurable_stabHom hc) (F.stabHom_surjective hc)
  unfold stabMeasure
  infer_instance

theorem isMulRightInvariant_stabMeasure : (F.stabMeasure hc hQ).IsMulRightInvariant := by
  haveI := isMulRightInvariant_lerayMeasureC (F.gramDetC_Q' hQ)
  haveI := measurableMul_subgroup (stabilizer (ArchSOC Q) y)
  haveI := isMulRightInvariant_map_of_surjective (lerayMeasureC F.Q' (F.gramDetC_Q' hQ)) (F.stabHom hc)
    (F.measurable_stabHom hc) (F.stabHom_surjective hc)
  unfold stabMeasure
  infer_instance

end SplitFrameC

/-! ### Packaging: the archimedean fibration at a complex place -/

variable (Q : QuadForm ℂ (m + 1)) (hQ : gramDetC Q ≠ 0) {c : ℂ} (hc : c ≠ 0) (hm : 1 ≤ m)

/-- A chosen split frame at each point of the quadric $S_c$. -/
def frameAtC {y : Fin (m + 1) → ℂ} (hy : y ∈ sphC Q c) : SplitFrameC Q c y :=
  (exists_splitFrameC Q hc hy).some

/-- **The measure $\mu_{H_y}$ on the stabilizer of `y`** (for $y\notin S_c$ it is $0$; it is never used there). -/
def complexStabMeasure (y : Fin (m + 1) → ℂ) : Measure (stabilizer (ArchSOC Q) y) :=
  haveI := Classical.propDecidable (y ∈ sphC Q c)
  if hy : y ∈ sphC Q c then (frameAtC Q hc hy).stabMeasure hc hQ else 0

/-- **The archimedean fibration at a complex place** (Weil 1982, Lemma 2.4.1 / Thm 2.4.3): for a
nondegenerate complex form $Q$ in $m+1\ge2$ variables and $c\ne0$, the orbit maps $g\mapsto g^{-1}y$ ($y\in S_c$) of
$SO(Q)(\mathbb C)$ are fibred with
$$\mu_Q = |2c|_{\mathbb C}^{-m}\cdot\mathrm{coord}_*(\sigma_c\otimes\mu_{H_y}),\qquad |z|_{\mathbb C} = |z|^2,$$
for every $y\in S_c$, one constant for all $y$. Built from `SplitFrameC.lerayMeasureC_eq_map_coord` at a chosen
split frame. -/
@[kb "weil1982" "§2.4 Lemma 2.4.1, Theorem 2.4.3, p. 25 (matching measures on G, H, G/H; complex place) [unverified page]"]
def complexArchFibration :
    ArchFibration (lerayMeasureC Q hQ) (sphC Q c) (sigC Q c) Subtype.val
      (((‖2 * c‖₊ ^ (2 * m))⁻¹ : ℝ≥0) : ℝ≥0∞) where
  μH := complexStabMeasure Q hQ hc
  coord y hy := (frameAtC Q hc hy).coord hc hm hQ
  sigmaFinite y := by
    unfold complexStabMeasure
    split_ifs with hy
    · exact (frameAtC Q hc hy).sigmaFinite_stabMeasure hc hQ
    · infer_instance
  leftInv y := by
    unfold complexStabMeasure
    split_ifs with hy
    · exact (frameAtC Q hc hy).isMulLeftInvariant_stabMeasure hc hQ
    · exact ⟨fun g => by simp⟩
  fib y hy := by
    rw [complexStabMeasure, dite_eq_left_of_eq_true (eq_true hy)]
    exact (frameAtC Q hc hy).lerayMeasureC_eq_map_coord hc hm hQ

include hm in
/-- **The complex-place stabilizer measures are right invariant** ($H_y\cong SO(Q'_y)(\mathbb C)$ is unimodular). -/
theorem isMulRightInvariant_complexStabMeasure (y : Fin (m + 1) → ℂ) :
    (complexStabMeasure Q hQ hc y).IsMulRightInvariant := by
  unfold complexStabMeasure
  split_ifs with hy
  · exact (frameAtC Q hc hy).isMulRightInvariant_stabMeasure hc hQ
  · exact ⟨fun g => by simp⟩

end Frame

end QuadFormsKB.Tamagawa.Indefinite
