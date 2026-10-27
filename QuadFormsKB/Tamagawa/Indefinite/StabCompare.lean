/-
# The stabilizer measures over all infinite places, from frame data

**Layer:** number fields, archimedean places. $F$ a number field, $Q_0$ a nondegenerate form over $\mathcal O_F$ in
$N = k + 1$ variables (any signature), $m\in F$, $m\ne0$, $\xi\in F^N$.

the archimedean fibration `archFibrationNF` of the numbers headline over the quadric $\{Q = m\}\subseteq V_\infty$
gives every point $y$ a measure
$\mu_{H_y}$ on its stabilizer $H_y\subseteq G_\infty = SO(V)(F_\infty)$, defined place by place from chosen split frames.
The frame fibrations of the forms headlines define the stabilizer measure at $a\,\Xi_\infty$ instead from the
frame data $g = [\Xi\mid C]$, as $\lambda\cdot(h\mapsto a\,\iota_\infty(h)\,a^{-1})_*\mu^{\mathrm{Tam}}_{Q''}$. This file shows
that, for a $1$-frame $\Xi = \xi$, the two agree.

**Defines**
* **`SplitDataInf Q₀ m ξ`**: frame data at infinity for $\xi$: a nondegenerate form $Q''$ over $\mathcal O_F$ in $k$
  variables (`Q''`, `hQ''`), $g\in GL_N(F)$ with $g e_0 = \xi$ (`base`) and $Q_0\circ g = \langle m\rangle\perp Q''$ (`hess`, on
  Hessians), and a homomorphism $\iota : G_\infty(Q'')\to G_\infty(Q_0)$ (`ι`, `measurable_ι`) with
  $\iota(h)_w = g\,\mathrm{diag}(1, h_w)\,g^{-1}$ at every real (`matR_ι`) and complex (`matC_ι`) place $w$ (matrices of
  $g$ embedded by $\sigma_w$);
* `ξInf`: the point $(\sigma_w(\xi))_w\in V_\infty$; `SplitDataInf.conjHom a` $: h\mapsto a\,\iota(h)\,a^{-1}$, into the
  stabilizer of $a\,\xi_\infty$; `SplitDataInf.lam` $=\lambda = \prod_{w\ \mathrm{real}}|\sigma_w\det g|^{N}\cdot
  \prod_{w\ \mathrm{complex}}\|\sigma_w\det g\|^{2N}/c_F(k)$.

**Proves** (unconditional)
* `SplitDataInf.frameR`, `SplitDataInf.frameC`: $P_w = a_wg_w$ is a split frame at $(a\xi_\infty)_w$, and
  `SplitDataInf.conjHom_eq`: $h\mapsto a\,\iota(h)\,a^{-1}$ is, place by place, the stabilizer embedding of $P_w$.
  The comparison of the measures is `archFibrationNF_μH_eq` (StabCompareNF.lean).
-/
import QuadFormsKB.Tamagawa.Indefinite.StabLocal
import QuadFormsKB.Tamagawa.Indefinite.SiegelComplex

open MeasureTheory Measure Matrix MulAction Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace QuadFormsKB.Siegel QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.ArchSOMeasure
open QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

/-- **Frame data at infinity** for $\xi\in F^{k+1}$ (so $Q_0(\xi) = m$): a complement form $Q''$, a change of basis $g$ with
$ge_0 = \xi$ and $Q_0\circ g = \langle m\rangle\perp Q''$, and $\iota : G_\infty(Q'')\to G_\infty(Q_0)$ acting as
$g\,\mathrm{diag}(1,\cdot)\,g^{-1}$ at every infinite place. Data with its defining properties. Fields: `Q''`, `hQ''`, `g`,
`hess`, `base`, `ι`, `measurable_ι`, `matR_ι`, `matC_ι`. -/
structure SplitDataInf (Q₀ : QuadForm (𝓞 F) (k + 1)) (m : F) (ξ : Fin (k + 1) → F) where
  /-- The complement form, in $k$ variables. -/
  Q'' : QuadForm (𝓞 F) k
  /-- It is nondegenerate. -/
  hQ'' : Q''.Nondegenerate
  /-- The change of basis $g = [\xi\mid C]$. -/
  g : GL (Fin (k + 1)) F
  /-- $Q_0\circ g = \langle m\rangle\perp Q''$ (on Hessians). -/
  hess : (splitForm m (Q''.map (algebraMap (𝓞 F) F))).hessian =
    (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian * g
  /-- $ge_0 = \xi$. -/
  base : (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ Pi.single 0 1 = ξ
  /-- The embedding $\iota : G_\infty(Q'')\to G_\infty(Q_0)$. -/
  ι : GInfSO Q'' →* GInfSO Q₀
  /-- $\iota$ is measurable. -/
  measurable_ι : Measurable ι
  /-- $\iota(h)_w = g\,\mathrm{diag}(1, h_w)\,g^{-1}$ at the real places. -/
  matR_ι : ∀ (h : GInfSO Q'') (w : {w : InfinitePlace F // w.IsReal}),
    ((ArchSO.incl _ ((ι h).1 w) : GL (Fin (k + 1)) ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) =
      (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F).map (σR w) *
        cornerMat 1 ((ArchSO.incl _ (h.1 w) : GL (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ) *
          ((g⁻¹ : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F).map (σR w)
  /-- $\iota(h)_w = g\,\mathrm{diag}(1, h_w)\,g^{-1}$ at the complex places. -/
  matC_ι : ∀ (h : GInfSO Q'') (w : {w : InfinitePlace F // w.IsComplex}),
    ((ArchSOC.incl _ ((ι h).2 w) : GL (Fin (k + 1)) ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) =
      (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F).map (σC w) *
        cornerMat 1 ((ArchSOC.incl _ (h.2 w) : GL (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ) *
          ((g⁻¹ : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F).map (σC w)

/-- The point $\xi_\infty = (\sigma_w(\xi))_w\in V_\infty$. -/
def ξInf (ξ : Fin (k + 1) → F) : VInf F (k + 1) := (fun w j => σR w (ξ j), fun w j => σC w (ξ j))

namespace SplitDataInf

variable {Q₀ : QuadForm (𝓞 F) (k + 1)} {m : F} {ξ : Fin (k + 1) → F} (D : SplitDataInf Q₀ m ξ)

theorem cornerMat_e₀' {K : Type} [Field K] (B : Matrix (Fin k) (Fin k) K) :
    cornerMat 1 B *ᵥ (e₀ : Fin (k + 1) → K) = e₀ := by
  rw [cornerMat_mulVec, one_mul, mulVec_zero]

theorem single_eq_e₀ {K : Type} [Field K] : (Pi.single 0 1 : Fin (k + 1) → K) = e₀ := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp [Fin.succ_ne_zero]

theorem sigma_base {K : Type} [Field K] (f : F →+* K) :
    (fun j => f (ξ j)) = (D.g : Matrix (Fin (k + 1)) (Fin (k + 1)) F).map f *ᵥ (e₀ : Fin (k + 1) → K) := by
  have h := congrArg (fun v : Fin (k + 1) → F => fun j => f (v j)) D.base
  rw [← h, ← single_eq_e₀]
  ext j
  have := RingHom.map_mulVec f (D.g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (Pi.single 0 1) j
  have e : (f ∘ (Pi.single 0 1 : Fin (k + 1) → F)) = (Pi.single 0 1 : Fin (k + 1) → K) := by
    ext i
    by_cases hi : i = 0 <;> simp [hi]
  rw [this, e]

theorem map_inv_mul' {K : Type} [Field K] (f : F →+* K) :
    ((D.g⁻¹ : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F).map f *
      (D.g : Matrix (Fin (k + 1)) (Fin (k + 1)) F).map f = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one f (map_zero f) (map_one f)]

/-- $\iota(h)$ fixes $\xi_\infty$. -/
theorem ι_smul_ξInf (h : GInfSO D.Q'') : D.ι h • ξInf ξ = ξInf ξ := by
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · show (ArchSO.incl _ ((D.ι h).1 w) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) *ᵥ (fun j => σR w (ξ j)) =
      fun j => σR w (ξ j)
    rw [D.matR_ι, D.sigma_base (σR w), mulVec_mulVec, Matrix.mul_assoc (_ * _) _ _,
      D.map_inv_mul', Matrix.mul_one, ← mulVec_mulVec, cornerMat_e₀']
  · show (ArchSOC.incl _ ((D.ι h).2 w) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) *ᵥ (fun j => σC w (ξ j)) =
      fun j => σC w (ξ j)
    rw [D.matC_ι, D.sigma_base (σC w), mulVec_mulVec, Matrix.mul_assoc (_ * _) _ _,
      D.map_inv_mul', Matrix.mul_one, ← mulVec_mulVec, cornerMat_e₀']

/-- **The conjugated embedding** $h\mapsto a\,\iota(h)\,a^{-1}$, $G_\infty(Q'')\to H_{a\xi_\infty}$. -/
def conjHom (a : GInfSO Q₀) : GInfSO D.Q'' →* stabilizer (GInfSO Q₀) (a • ξInf ξ) where
  toFun h := ⟨a * D.ι h * a⁻¹, by
    show (a * D.ι h * a⁻¹) • a • ξInf ξ = a • ξInf ξ
    rw [mul_smul, mul_smul, inv_smul_smul, D.ι_smul_ξInf]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' h h' := Subtype.ext (by simp [mul_assoc])

theorem measurable_conjHom (a : GInfSO Q₀) : Measurable (D.conjHom a) :=
  (((measurable_const_mul a).comp D.measurable_ι).mul_const _).subtype_mk

/-- `conjHom a` into the stabilizer of a point $y$ given with $a\,\xi_\infty = y$. -/
def conjHomAt (a : GInfSO Q₀) {y : VInf F (k + 1)} (hy : a • ξInf ξ = y) :
    GInfSO D.Q'' →* stabilizer (GInfSO Q₀) y := by
  subst hy; exact D.conjHom a

theorem conjHomAt_apply (a : GInfSO Q₀) {y : VInf F (k + 1)} (hy : a • ξInf ξ = y) (h : GInfSO D.Q'') :
    ((D.conjHomAt a hy h : stabilizer (GInfSO Q₀) y) : GInfSO Q₀) = a * D.ι h * a⁻¹ := by
  subst hy; rfl

theorem measurable_conjHomAt (a : GInfSO Q₀) {y : VInf F (k + 1)} (hy : a • ξInf ξ = y) :
    Measurable (D.conjHomAt a hy) := by
  subst hy; exact D.measurable_conjHom a

open Classical in
/-- **The scale** $\lambda = \prod_{w\ \mathrm{real}}|\sigma_w\det g|^{k+1}\prod_{w\ \mathrm{complex}}\|\sigma_w\det g\|^{2(k+1)}/c_F(k)$. -/
def lam : ℝ≥0∞ :=
  ENNReal.ofReal ((∏ w : {w : InfinitePlace F // w.IsReal},
      |σR w (D.g : Matrix (Fin (k + 1)) (Fin (k + 1)) F).det| ^ (k + 1)) *
    (∏ w : {w : InfinitePlace F // w.IsComplex},
      ‖σC w (D.g : Matrix (Fin (k + 1)) (Fin (k + 1)) F).det‖ ^ (2 * (k + 1))) / cF F k)

/-! ### The split frames $P_w = a_w g_w$ -/

/-- The matrix of $g$ at a real place. -/
abbrev gR (w : {w : InfinitePlace F // w.IsReal}) : GL (Fin (k + 1)) ℝ :=
  Matrix.GeneralLinearGroup.map (σR w) D.g

/-- The matrix of $g$ at a complex place. -/
abbrev gC (w : {w : InfinitePlace F // w.IsComplex}) : GL (Fin (k + 1)) ℂ :=
  Matrix.GeneralLinearGroup.map (σC w) D.g

theorem hessR (a : GInfSO Q₀) (w : {w : InfinitePlace F // w.IsReal}) :
    (splitForm (mR m w) (QRe D.Q'' w)).hessian =
      ((ArchSO.incl _ (a.1 w) * D.gR w : GL (Fin (k + 1)) ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)ᵀ *
        (QRe Q₀ w).hessian * (ArchSO.incl _ (a.1 w) * D.gR w : GL (Fin (k + 1)) ℝ) := by
  have h1 := congrArg (fun M : Matrix (Fin (k + 1)) (Fin (k + 1)) F => M.map (σR w)) D.hess
  rw [← hessian_map', map_splitForm] at h1
  refine h1.trans ?_
  have hA :=((mem_soReal_iff _ _).mp (ArchSOInst.incl_mem (QRe Q₀ w) (a.1 w))).1
  have hH : (QRe Q₀ w).hessian = (Q₀.map (algebraMap (𝓞 F) F)).hessian.map (σR w) := hessian_map' _ _
  rw [hH] at hA ⊢
  rw [Units.val_mul, Matrix.transpose_mul]
  simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.mul_assoc]
  have hA' : ∀ X, (ArchSO.incl _ (a.1 w) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)ᵀ *
      ((Q₀.map (algebraMap (𝓞 F) F)).hessian.map (σR w) *
        ((ArchSO.incl _ (a.1 w) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) * X)) =
      (Q₀.map (algebraMap (𝓞 F) F)).hessian.map (σR w) * X := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA]
  rw [show ((D.gR w : GL (Fin (k + 1)) ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) =
    (D.g : Matrix (Fin (k + 1)) (Fin (k + 1)) F).map (σR w) from rfl, hA']

theorem baseR (a : GInfSO Q₀) (w : {w : InfinitePlace F // w.IsReal}) :
    ((ArchSO.incl _ (a.1 w) * D.gR w : GL (Fin (k + 1)) ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) *ᵥ e₀ =
      (a • ξInf ξ).1 w := by
  show _ = (ArchSO.incl _ (a.1 w) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) *ᵥ (fun j => σR w (ξ j))
  rw [D.sigma_base (σR w), Units.val_mul, ← mulVec_mulVec]
  rfl

/-- **The split frame at a real place**: $P_w = a_wg_w$ at $(a\xi_\infty)_w$, complement form $Q''^{\sigma_w}$. -/
def frameR (a : GInfSO Q₀) (w : {w : InfinitePlace F // w.IsReal}) :
    SplitFrame (QRe Q₀ w) (mR m w) ((a • ξInf ξ).1 w) where
  P := ArchSO.incl _ (a.1 w) * D.gR w
  Q' := QRe D.Q'' w
  hess := D.hessR a w
  base := D.baseR a w

theorem hessC (a : GInfSO Q₀) (w : {w : InfinitePlace F // w.IsComplex}) :
    (splitForm (mC m w) (QCx D.Q'' w)).hessian =
      ((ArchSOC.incl _ (a.2 w) * D.gC w : GL (Fin (k + 1)) ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)ᵀ *
        (QCx Q₀ w).hessian * (ArchSOC.incl _ (a.2 w) * D.gC w : GL (Fin (k + 1)) ℂ) := by
  have h1 := congrArg (fun M : Matrix (Fin (k + 1)) (Fin (k + 1)) F => M.map (σC w)) D.hess
  rw [← hessian_map', map_splitForm] at h1
  refine h1.trans ?_
  have hA0:= ArchSOC.isometry (QCx Q₀ w) (a.2 w)
  simp only [gramC, Matrix.mul_smul, Matrix.smul_mul] at hA0
  have hA : (ArchSOC.incl _ (a.2 w) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)ᵀ * (QCx Q₀ w).hessian *
      (ArchSOC.incl _ (a.2 w) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) = (QCx Q₀ w).hessian :=
    smul_right_injective _ (by norm_num : (1 / 2 : ℂ) ≠ 0) hA0
  have hH : (QCx Q₀ w).hessian = (Q₀.map (algebraMap (𝓞 F) F)).hessian.map (σC w) := hessian_map' _ _
  rw [hH] at hA ⊢
  rw [Units.val_mul, Matrix.transpose_mul]
  simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.mul_assoc]
  have hA' : ∀ X, (ArchSOC.incl _ (a.2 w) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)ᵀ *
      ((Q₀.map (algebraMap (𝓞 F) F)).hessian.map (σC w) *
        ((ArchSOC.incl _ (a.2 w) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) * X)) =
      (Q₀.map (algebraMap (𝓞 F) F)).hessian.map (σC w) * X := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA]
  rw [show ((D.gC w : GL (Fin (k + 1)) ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) =
    (D.g : Matrix (Fin (k + 1)) (Fin (k + 1)) F).map (σC w) from rfl, hA']

theorem baseC (a : GInfSO Q₀) (w : {w : InfinitePlace F // w.IsComplex}) :
    ((ArchSOC.incl _ (a.2 w) * D.gC w : GL (Fin (k + 1)) ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) *ᵥ e₀ =
      (a • ξInf ξ).2 w := by
  show _ = (ArchSOC.incl _ (a.2 w) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) *ᵥ (fun j => σC w (ξ j))
  rw [D.sigma_base (σC w), Units.val_mul, ← mulVec_mulVec]
  rfl

/-- **The split frame at a complex place**: $P_w = a_wg_w$ at $(a\xi_\infty)_w$. -/
def frameC (a : GInfSO Q₀) (w : {w : InfinitePlace F // w.IsComplex}) :
    SplitFrameC (QCx Q₀ w) (mC m w) ((a • ξInf ξ).2 w) where
  P := ArchSOC.incl _ (a.2 w) * D.gC w
  Q' := QCx D.Q'' w
  hess := D.hessC a w
  base := D.baseC a w

/-- **`conjHom` place by place**: its component at a real place $w$ is the stabilizer embedding of the split frame
$P_w$, at a complex place likewise. -/
theorem conjHom_eq (hm : m ≠ 0) (a : GInfSO Q₀) (h : GInfSO D.Q'') :
    D.conjHom a h = (stabProdME (a • ξInf ξ)).symm
      ((stabPiME (a • ξInf ξ).1).symm (fun w => (D.frameR a w).stabHom (h.1 w)),
        (stabPiME (a • ξInf ξ).2).symm (fun w => (D.frameC a w).stabHom (mC_ne_zero hm w) (h.2 w))) := by
  refine Subtype.ext (Prod.ext (funext fun w => ?_) (funext fun w => ?_))
  · refine Subtype.ext (Units.ext ?_)
    show (ArchSO.incl _ (a.1 w) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) *
        (ArchSO.incl _ ((D.ι h).1 w) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) *
        (ArchSO.incl _ (a.1 w)⁻¹ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) =
      ArchSOInst.mat _ ((D.frameR a w).conj (QuadFormsKB.Tamagawa.Measure.OrbitalReal.iota _ _ (h.1 w)))
    rw [SplitFrame.mat_conj, D.matR_ι]
    change _ = ((ArchSO.incl _ (a.1 w) * D.gR w : GL (Fin (k + 1)) ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) *
      cornerMat 1 ((ArchSO.incl _ (h.1 w) : GL (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ) *
      (((ArchSO.incl _ (a.1 w) * D.gR w)⁻¹ : GL (Fin (k + 1)) ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul]
    simp only [Matrix.mul_assoc]
    rfl
  · refine Subtype.ext (Units.ext ?_)
    show (ArchSOC.incl _ (a.2 w) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) *
        (ArchSOC.incl _ ((D.ι h).2 w) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) *
        (ArchSOC.incl _ (a.2 w)⁻¹ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) =
      ArchSOC.mat _ ((D.frameC a w).conj (mC_ne_zero hm w)
        (QuadFormsKB.Tamagawa.Measure.OrbitalComplex.iotaC _ _ (h.2 w)))
    rw [SplitFrameC.mat_conj, D.matC_ι]
    change _ = ((ArchSOC.incl _ (a.2 w) * D.gC w : GL (Fin (k + 1)) ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) *
      cornerMat 1 ((ArchSOC.incl _ (h.2 w) : GL (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ) *
      (((ArchSOC.incl _ (a.2 w) * D.gC w)⁻¹ : GL (Fin (k + 1)) ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul]
    simp only [Matrix.mul_assoc]
    rfl

end SplitDataInf

end QuadFormsKB.Tamagawa.Indefinite
