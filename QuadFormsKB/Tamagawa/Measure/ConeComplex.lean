import QuadFormsKB.Tamagawa.Measure.OrbitalComplexStab
import QuadFormsKB.Tamagawa.Measure.ConeRealOrbit

/-!
# The archimedean cone at a complex place: parabolic slice and sphere chart

The complex analogue of `ConeReal.lean`, for $Q = \langle c\rangle\perp\langle -c\rangle\perp Q'$ over $\mathbb C$
(`ConeAlgebra.coneForm c Q'`, $c \ne 0$, $Q'$ nondegenerate in $k$ variables), with $|z|_{\mathbb C} = |z|^2$ and the
complex Leray measures of `LerayComplex.lean` and `SphereLerayC.lean`:

1. (`lintegral_sigC_graph`) **the hyperbolic-split chart of the complex sphere** $S_c$:
   $\sigma_c = d^2q\,d^2x'/|2cq|_{\mathbb C}$ on $\{q \ne 0\}$ in the graph coordinates $(q, x')$, and $\{q = 0\}$ is
   null. Proof: the complex polar coordinates on the half plane (`lintegral_polC_half`) against a direct computation of
   $dx$ in the coordinates $(u, q, x')$, $u = Q/c$, and the substitution $u = \beta^2$ on $\{\operatorname{Re}\beta>0\}$.
2. the parabolic section $s(x) = d((x_0 - x_1)^{-1})\,n(x')$ of $SO(Q)(\mathbb C) \to S_c$;
3. (`lintegral_lerayMeasureC_cone_param`) the parametric cone identity, from the sphere identities and the
   unimodularity of $SO(Q)(\mathbb C)$ (`isMulRightInvariant_lerayMeasureC`).
-/

open MeasureTheory Measure Matrix Set Filter Topology
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.ConeComplex

open QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.ArchVol
open QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.Measure.SphereLerayC
open QuadFormsKB.Tamagawa.Measure.OrbitalComplex QuadFormsKB.Tamagawa.Measure.ConeAlgebra

variable {k : ℕ}

/-! ### Group elements of the parabolic in $SO(Q)(\mathbb C)$ -/

theorem gramC_eq {n : ℕ} (Q : QuadForm ℂ n) : gramC Q = (1 / 2 : ℂ) • Q.hessian := rfl

theorem hessian_det_ne_zeroC {n : ℕ} {Q : QuadForm ℂ n} (hQ : gramDetC Q ≠ 0) : Q.hessian.det ≠ 0 := by
  intro h; apply hQ; rw [gramDetC, gramC_eq, det_smul, h, mul_zero]

theorem isometry_hessian_of_gramC {n : ℕ} {Q : QuadForm ℂ n} {M : Matrix (Fin n) (Fin n) ℂ}
    (h : Mᵀ * gramC Q * M = gramC Q) : Mᵀ * Q.hessian * M = Q.hessian := by
  rw [gramC_eq, Matrix.mul_smul, Matrix.smul_mul] at h
  have := congrArg (fun A => (2 : ℂ) • A) h
  simpa [smul_smul] using this

theorem isometry_gramC_of_hessian {n : ℕ} {Q : QuadForm ℂ n} {M : Matrix (Fin n) (Fin n) ℂ}
    (h : Mᵀ * Q.hessian * M = Q.hessian) : Mᵀ * gramC Q * M = gramC Q := by
  rw [gramC_eq, Matrix.mul_smul, Matrix.smul_mul, h]

/-- A matrix-valued map is continuous if all its actions on vectors are. -/
theorem continuous_of_mulVecC {n : ℕ} {X : Type*} [TopologicalSpace X] {M : X → Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ v, Continuous fun t => M t *ᵥ v) : Continuous M := by
  refine continuous_matrix fun i j => ?_
  have := (continuous_apply i).comp (h (Pi.single j 1))
  convert this using 1
  funext t
  simp [mulVec, dotProduct, Pi.single_apply]

theorem continuous_v3C {X : Type*} [TopologicalSpace X] {a b : X → ℂ} {y : X → Fin k → ℂ} (ha : Continuous a)
    (hb : Continuous b) (hy : Continuous y) : Continuous fun t => v3 (a t) (b t) (y t) :=
  ha.finCons (hb.finCons hy)

theorem continuous_tlC : Continuous (tl : (Fin (k + 1 + 1) → ℂ) → Fin k → ℂ) :=
  continuous_pi fun i => continuous_apply _

variable {c : ℂ} {Q' : QuadForm ℂ k}

/-- The middle form $Q_m = \langle -c\rangle \perp Q'$ over $\mathbb C$. -/
abbrev QmC (c : ℂ) (Q' : QuadForm ℂ k) : QuadForm ℂ (k + 1) := splitForm (-c) Q'

theorem gramDetC_Qm (hc : c ≠ 0) (hQ' : gramDetC Q' ≠ 0) : gramDetC (QmC c Q') ≠ 0 :=
  gramDetC_splitForm_ne_zero (neg_ne_zero.mpr hc) hQ'

theorem gramDetC_cone (hc : c ≠ 0) (hQ' : gramDetC Q' ≠ 0) : gramDetC (coneForm c Q') ≠ 0 :=
  gramDetC_splitForm_ne_zero hc (gramDetC_Qm hc hQ')

theorem hessian_cone_detC (hc : c ≠ 0) (hQ' : gramDetC Q' ≠ 0) : (coneForm c Q').hessian.det ≠ 0 :=
  hessian_det_ne_zeroC (gramDetC_cone hc hQ')

theorem sq_or_neg_sqC (a : ℂ) : ∃ b, b ^ 2 = a ∨ b ^ 2 = -a :=
  ⟨a ^ (2⁻¹ : ℂ), Or.inl (by exact_mod_cast Complex.cpow_nat_inv_pow a (n := 2) two_ne_zero)⟩

/-- $d(a)$ in $\mathrm{GL}_{k+2}(\mathbb C)$. -/
def dGLC {a : ℂ} (ha : a ≠ 0) : GL (Fin (k + 1 + 1)) ℂ := ⟨dM a, dM a⁻¹, dM_mul_inv ha, dM_inv_mul ha⟩

theorem dGLC_mem (hc : c ≠ 0) (hQ' : gramDetC Q' ≠ 0) {a : ℂ} (ha : a ≠ 0) :
    dGLC (k := k) ha ∈ soC (coneForm c Q') := by
  rw [mem_soC_iff]
  exact ⟨isometry_gramC_of_hessian (isometry_dM c Q' ha),
    det_dM c Q' (hessian_cone_detC hc hQ') ha (sq_or_neg_sqC a)⟩

/-- **The torus element** $d(a) \in SO(Q)(\mathbb C)$. -/
def dG (hc : c ≠ 0) (hQ' : gramDetC Q' ≠ 0) {a : ℂ} (ha : a ≠ 0) : ArchSOC (coneForm c Q') :=
  ArchSOC.mk _ (dGLC ha) (dGLC_mem hc hQ' ha)

theorem mat_dG (hc : c ≠ 0) (hQ' : gramDetC Q' ≠ 0) {a : ℂ} (ha : a ≠ 0) :
    ArchSOC.mat _ (dG hc hQ' ha) = dM a := rfl

/-- $n(w)$ in $\mathrm{GL}_{k+2}(\mathbb C)$. -/
def nGLC (hc : c ≠ 0) (w : Fin k → ℂ) : GL (Fin (k + 1 + 1)) ℂ :=
  ⟨nM c Q' w, nM c Q' (-w), nM_mul_neg c Q' hc w, nM_neg_mul c Q' hc w⟩

theorem nGLC_mem (hc : c ≠ 0) (hQ' : gramDetC Q' ≠ 0) (w : Fin k → ℂ) :
    nGLC hc (Q' := Q') w ∈ soC (coneForm c Q') := by
  rw [mem_soC_iff]
  exact ⟨isometry_gramC_of_hessian (isometry_nM c Q' hc w), det_nM c Q' hc (hessian_cone_detC hc hQ') w⟩

/-- **The Eichler transformation** $n(w) \in SO(Q)(\mathbb C)$. -/
def nG (hc : c ≠ 0) (hQ' : gramDetC Q' ≠ 0) (w : Fin k → ℂ) : ArchSOC (coneForm c Q') :=
  ArchSOC.mk _ (nGLC hc w) (nGLC_mem hc hQ' w)

variable (hc : c ≠ 0) (hQ' : gramDetC Q' ≠ 0)
include hc hQ'

theorem mat_nG (w : Fin k → ℂ) : ArchSOC.mat _ (nG hc hQ' w) = nM c Q' w := rfl

omit hc hQ' in
/-- **The Levi factor** $SO(Q')(\mathbb C) \to SO(Q)(\mathbb C)$, $h \mapsto \mathrm{diag}(1, 1, h)$. -/
def mG (c : ℂ) (Q' : QuadForm ℂ k) : ArchSOC Q' →* ArchSOC (coneForm c Q') :=
  (iotaC c (QmC c Q')).comp (iotaC (-c) Q')

omit hc hQ' in
theorem mat_mG (h : ArchSOC Q') : ArchSOC.mat _ (mG c Q' h) = mM (ArchSOC.mat _ h) := rfl

omit hc hQ' in
theorem continuous_mG : Continuous (mG c Q') := (continuous_iotaC _ _).comp (continuous_iotaC _ _)

omit hc hQ' in
theorem mat_ext' {g h : ArchSOC (coneForm c Q')} (e : ArchSOC.mat _ g = ArchSOC.mat _ h) : g = h := by
  apply Subtype.ext; apply Units.ext; exact e

theorem nG_add (w w' : Fin k → ℂ) : nG hc hQ' w * nG hc hQ' w' = nG hc hQ' (w + w') :=
  mat_ext' (by rw [ArchSOC.mat_mul, mat_nG, mat_nG, mat_nG, nM_mul c Q' hc])

theorem nG_zero : nG hc hQ' (0 : Fin k → ℂ) = 1 :=
  mat_ext' (by rw [mat_nG, nM_zero, ArchSOC.mat_one])

theorem nG_neg (w : Fin k → ℂ) : (nG hc hQ' w)⁻¹ = nG hc hQ' (-w) := by
  rw [inv_eq_iff_mul_eq_one, nG_add, add_neg_cancel, nG_zero]

theorem dG_mul {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    dG hc hQ' ha * dG hc hQ' hb = dG hc hQ' (mul_ne_zero ha hb) :=
  mat_ext' (by rw [ArchSOC.mat_mul, mat_dG, mat_dG, mat_dG, dM_mul _ _ ha hb])

theorem dG_inv {a : ℂ} (ha : a ≠ 0) : (dG hc hQ' ha)⁻¹ = dG hc hQ' (inv_ne_zero ha) := by
  rw [inv_eq_iff_mul_eq_one, dG_mul]
  exact mat_ext' (by rw [mat_dG, mul_inv_cancel₀ ha, dM_one, ArchSOC.mat_one])

theorem dG_mul_nG {a : ℂ} (ha : a ≠ 0) (w : Fin k → ℂ) :
    dG hc hQ' ha * nG hc hQ' w = nG hc hQ' (a • w) * dG hc hQ' ha :=
  mat_ext' (by rw [ArchSOC.mat_mul, ArchSOC.mat_mul, mat_dG, mat_nG, mat_nG, dM_mul_nM c Q' hc ha])

theorem mG_mul_dG (h : ArchSOC Q') {a : ℂ} (ha : a ≠ 0) :
    mG c Q' h * dG hc hQ' ha = dG hc hQ' ha * mG c Q' h :=
  mat_ext' (by rw [ArchSOC.mat_mul, ArchSOC.mat_mul, mat_dG, mat_mG, mM_mul_dM])

omit hc hQ' in
theorem isometry_hessianC (h : ArchSOC Q') :
    (ArchSOC.mat _ h)ᵀ * Q'.hessian * ArchSOC.mat _ h = Q'.hessian :=
  isometry_hessian_of_gramC (ArchSOC.isometry _ h)

theorem mG_mul_nG (h : ArchSOC Q') (w : Fin k → ℂ) :
    mG c Q' h * nG hc hQ' w = nG hc hQ' (ArchSOC.mat _ h *ᵥ w) * mG c Q' h :=
  mat_ext' (by rw [ArchSOC.mat_mul, ArchSOC.mat_mul, mat_nG, mat_nG, mat_mG,
    mM_mul_nM c Q' (isometry_hessianC h)])

theorem continuous_nG : Continuous (nG hc hQ' : (Fin k → ℂ) → ArchSOC (coneForm c Q')) := by
  have hv : ∀ v : Fin (k + 1 + 1) → ℂ, Continuous fun w : Fin k → ℂ => nM c Q' w *ᵥ v := by
    intro v
    have : (fun w : Fin k → ℂ => nM c Q' w *ᵥ v) = fun w => nM c Q' w *ᵥ v3 (v 0) (v 1) (tl v) := by
      rw [v3_eta]
    rw [this]
    simp only [nM_mulVec_v3]
    have hq : Continuous fun w : Fin k → ℂ => Q'.eval w := continuous_evalC Q'
    have hd : Continuous fun w : Fin k → ℂ => (Q'.hessian *ᵥ w) ⬝ᵥ tl v :=
      (continuous_const.matrix_mulVec continuous_id).dotProduct continuous_const
    refine continuous_v3C ?_ ?_ ?_
    · exact continuous_const.sub ((hd.add (continuous_const.mul hq)).div_const _)
    · exact continuous_const.sub ((hd.add (continuous_const.mul hq)).div_const _)
    · exact continuous_const.add (continuous_const_smul _)
  have h1 : Continuous fun w : Fin k → ℂ => nM c Q' w := continuous_of_mulVecC hv
  have h2 : Continuous fun w : Fin k → ℂ => nM c Q' (-w) := h1.comp continuous_neg
  exact Continuous.subtype_mk (Units.continuous_iff.mpr ⟨h1, h2⟩) _

theorem continuous_dG' : Continuous fun a : {a : ℂ // a ≠ 0} => dG hc hQ' a.2 := by
  have hinv : Continuous fun a : {a : ℂ // a ≠ 0} => (a : ℂ)⁻¹ := continuous_subtype_val.inv₀ fun a => a.2
  have hv : ∀ (f : {a : ℂ // a ≠ 0} → ℂ), Continuous f → Continuous (fun a => (f a)⁻¹) →
      Continuous fun a : {a : ℂ // a ≠ 0} => dM (k := k) (f a) := by
    intro f hf hf'
    refine continuous_of_mulVecC fun v => ?_
    have : (fun a : {a : ℂ // a ≠ 0} => dM (k := k) (f a) *ᵥ v) =
        fun a => dM (k := k) (f a) *ᵥ v3 (v 0) (v 1) (tl v) := by rw [v3_eta]
    rw [this]
    simp only [dM_mulVec_v3]
    refine continuous_v3C ?_ ?_ continuous_const
    · exact (continuous_const.add (((hf.sub continuous_const).div_const _).mul continuous_const)).add
        (((hf'.sub continuous_const).div_const _).mul continuous_const)
    · exact (continuous_const.add (((hf.sub continuous_const).div_const _).mul continuous_const)).sub
        (((hf'.sub continuous_const).div_const _).mul continuous_const)
  have h1 := hv (fun a => (a : ℂ)) continuous_subtype_val hinv
  have h2 := hv (fun a => (a : ℂ)⁻¹) hinv (by simpa using continuous_subtype_val)
  exact Continuous.subtype_mk (Units.continuous_iff.mpr ⟨h1, h2⟩) _


/-! ### Lebesgue measure in the coordinates $(x_0, x_1, x')$ over $\mathbb C$ -/

omit hc hQ' in
theorem measurable_v3C' : Measurable fun p : ℂ × ℂ × (Fin k → ℂ) => v3 p.1 p.2.1 p.2.2 :=
  (continuous_v3C continuous_fst (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd)).measurable

omit hc hQ' in
theorem Measurable.v3C {X : Type*} [MeasurableSpace X] {a b : X → ℂ} {y : X → Fin k → ℂ} (ha : Measurable a)
    (hb : Measurable b) (hy : Measurable y) : Measurable fun t => ConeAlgebra.v3 (a t) (b t) (y t) :=
  measurable_v3C'.comp (ha.prodMk (hb.prodMk hy))

omit hc hQ' in
theorem lintegral_cons_splitC {N : ℕ} {G : (Fin (N + 1) → ℂ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G x = ∫⁻ a, ∫⁻ y : Fin N → ℂ, G (Fin.cons a y) := by
  let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℂ) 0
  have hE : MeasurePreserving E volume volume := volume_preserving_piFinSuccAbove _ 0
  rw [← hE.symm.lintegral_comp_emb E.symm.measurableEmbedding, Measure.volume_eq_prod,
    lintegral_prod (f := fun z => G (E.symm z)) (hG.comp E.symm.measurable).aemeasurable]
  refine lintegral_congr fun a => lintegral_congr fun y => ?_
  congr 1
  simp [E, MeasurableEquiv.piFinSuccAbove]
  rfl

omit hc hQ' in
theorem lintegral_v3_splitC {G : (Fin (k + 1 + 1) → ℂ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G x = ∫⁻ a, ∫⁻ b, ∫⁻ y, G (v3 a b y) := by
  rw [lintegral_cons_splitC hG]
  refine lintegral_congr fun a => ?_
  exact lintegral_cons_splitC (G := fun y => G (Fin.cons a y))
    (hG.comp (continuous_const.finCons continuous_id).measurable)

omit hc hQ' in
/-- **Complex affine change of variables**: $\int\Psi(\alpha b + \beta)\,d^2b = |\alpha|^{-2}\int\Psi$. -/
theorem lintegral_comp_affineC {Ψ : ℂ → ℝ≥0∞} (hΨ : Measurable Ψ) {α : ℂ} (hα : α ≠ 0) (β : ℂ) :
    ∫⁻ b, Ψ (α * b + β) = (((‖α‖₊ ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞) * ∫⁻ u, Ψ u := by
  have h := SphereLerayC.map_mul_volume (Units.mk0 α hα)
  rw [show (∫⁻ b, Ψ (α * b + β)) = ∫⁻ u, Ψ (u + β) ∂(volume.map ((Units.mk0 α hα : ℂ) * ·)) from
      (lintegral_map (hΨ.comp (measurable_add_const β)) (measurable_const_mul _)).symm,
    h, lintegral_smul_measure, lintegral_add_right_eq_self (fun u => Ψ u) β, smul_eq_mul, SphereLerayC.wt,
    Units.val_mk0]
  congr 2

/-! ### The hyperbolic-split chart of the complex sphere -/

omit hc hQ' in
def graphBC (c : ℂ) (Q' : QuadForm ℂ k) (q : ℂ) (y : Fin k → ℂ) : ℂ := (1 - q ^ 2 - Q'.eval y / c) / (2 * q)

omit hc hQ' in
/-- **The graph point** of $S_c$ over $(q, y)$: $x = (b + q, b, y)$. -/
@[irreducible] def graphVC (c : ℂ) (Q' : QuadForm ℂ k) (q : ℂ) (y : Fin k → ℂ) : Fin (k + 1 + 1) → ℂ :=
  v3 (graphBC c Q' q y + q) (graphBC c Q' q y) y

omit hQ' in
theorem eval_graphVC {q : ℂ} (hq : q ≠ 0) (y : Fin k → ℂ) : (coneForm c Q').eval (graphVC c Q' q y) = c := by
  rw [graphVC, eval_coneForm_v3, graphBC]
  field_simp
  ring

omit hc hQ' in
theorem measurable_graphVC : Measurable fun p : ℂ × (Fin k → ℂ) => graphVC c Q' p.1 p.2 := by
  have hb : Measurable fun p : ℂ × (Fin k → ℂ) => graphBC c Q' p.1 p.2 := by
    unfold graphBC
    exact ((measurable_const.sub (measurable_fst.pow_const 2)).sub
      (((continuous_evalC Q').measurable.comp measurable_snd).div_const c)).div
      (measurable_const.mul measurable_fst)
  unfold graphVC
  exact Measurable.v3C (hb.add measurable_fst) hb measurable_snd

omit hc hQ' in
/-- The radial test function $\varphi = 1_D$, $D = \{\operatorname{Re}u > 0,\ |u| < 1\}$. -/
def phiC : ℂ → ℝ≥0∞ := {u : ℂ | 0 < u.re ∧ ‖u‖ < 1}.indicator 1

omit hc hQ' in
theorem measurableSet_DC : MeasurableSet {u : ℂ | 0 < u.re ∧ ‖u‖ < 1} :=
  (measurableSet_lt measurable_const Complex.continuous_re.measurable).inter
    (measurableSet_lt continuous_norm.measurable measurable_const)

omit hc hQ' in
theorem measurable_phiC : Measurable phiC := measurable_one.indicator measurableSet_DC

omit hc hQ' in
theorem phiC_eq_zero {u : ℂ} (hu : ¬ 0 < u.re) : phiC u = 0 :=
  indicator_of_notMem (fun h => hu h.1) _

omit hc hQ' in
/-- The principal square root $u^{1/2}$. -/
def sqrtC (u : ℂ) : ℂ := u ^ (2⁻¹ : ℂ)

omit hc hQ' in
theorem sqrtC_sq (u : ℂ) : sqrtC u ^ 2 = u := by simp [sqrtC]

omit hc hQ' in
theorem sqrtC_ne_zero {u : ℂ} (hu : u ≠ 0) : sqrtC u ≠ 0 := by
  intro h; apply hu; rw [← sqrtC_sq u, h]; ring

omit hc hQ' in
theorem measurable_sqrtC : Measurable sqrtC := measurable_id.pow_const _

omit hc hQ' in
/-- The test function $f(x) = \varphi(Q(x)/c)\,F\big(x/(Q(x)/c)^{1/2}\big)$. -/
@[irreducible] def testFC (c : ℂ) (Q' : QuadForm ℂ k) (F : (Fin (k + 1 + 1) → ℂ) → ℝ≥0∞)
    (x : Fin (k + 1 + 1) → ℂ) : ℝ≥0∞ :=
  phiC ((coneForm c Q').eval x / c) * F ((sqrtC ((coneForm c Q').eval x / c))⁻¹ • x)

omit hc hQ' in
theorem measurable_testFC {F : (Fin (k + 1 + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F) : Measurable (testFC c Q' F) := by
  have hu : Measurable fun x : Fin (k + 1 + 1) → ℂ => (coneForm c Q').eval x / c :=
    (continuous_evalC _).measurable.div_const c
  unfold testFC
  exact (measurable_phiC.comp hu).mul (hF.comp ((measurable_sqrtC.comp hu).inv.smul measurable_id))

omit hQ' in
theorem testFC_v3_eq {F : (Fin (k + 1 + 1) → ℂ) → ℝ≥0∞} {q : ℂ} (hq : q ≠ 0) (b : ℂ) (y : Fin k → ℂ) :
    testFC c Q' F (v3 (q + b) b y) =
      phiC (2 * q * b + (q ^ 2 + Q'.eval y / c)) *
        F (graphVC c Q' (q / sqrtC (2 * q * b + (q ^ 2 + Q'.eval y / c)))
          ((sqrtC (2 * q * b + (q ^ 2 + Q'.eval y / c)))⁻¹ • y)) := by
  set u := 2 * q * b + (q ^ 2 + Q'.eval y / c) with hu_def
  have hu : (coneForm c Q').eval (v3 (q + b) b y) / c = u := by
    rw [eval_coneForm_v3, hu_def]; field_simp; ring
  rw [testFC, hu]
  by_cases h0 : 0 < u.re
  · have hu0 : u ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl _ h0
    congr 2
    set s := sqrtC u
    have hs : s ≠ 0 := sqrtC_ne_zero hu0
    have hs2 : s ^ 2 = u := sqrtC_sq u
    rw [v3_smul, graphVC]
    have hQc : Q'.eval y / c = s ^ 2 - 2 * q * b - q ^ 2 := by rw [hs2, hu_def]; ring
    have hB : graphBC c Q' (q / s) (s⁻¹ • y) = s⁻¹ * b := by
      rw [graphBC, eval_smulC, show s⁻¹ ^ 2 * Q'.eval y / c = s⁻¹ ^ 2 * (Q'.eval y / c) by ring, hQc]
      field_simp
      ring
    refine v3_congr ?_ hB.symm rfl
    rw [hB]; field_simp; ring
  · rw [phiC_eq_zero h0, zero_mul, zero_mul]


omit hc hQ' in
/-- The density $|q|_{\mathbb C}^{-1}$-type weight $|\alpha q|^{-2}$. -/
@[irreducible] def dens2 (α q : ℂ) : ℝ≥0∞ := (((‖α * q‖₊ ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞)

omit hc hQ' in
theorem measurable_dens2 (α : ℂ) : Measurable (dens2 α) := by
  unfold dens2
  exact ((((continuous_const.mul continuous_id).nnnorm.pow 2).measurable).inv).coe_nnreal_ennreal

omit hc hQ' in
theorem measurable_T3C {F : (Fin (k + 1 + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F) :
    Measurable fun p : (ℂ × ℂ) × (Fin k → ℂ) => testFC c Q' F (v3 p.1.1 p.1.2 p.2) :=
  (measurable_testFC hF).comp (Measurable.v3C (measurable_fst.comp measurable_fst)
    (measurable_snd.comp measurable_fst) measurable_snd)

omit hQ' in
theorem lintegral_testFC_reorder {F : (Fin (k + 1 + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, testFC c Q' F x = ∫⁻ q, ∫⁻ y, ∫⁻ b, testFC c Q' F (v3 (q + b) b y) := by
  have h3 := measurable_T3C (c := c) (Q' := Q') hF
  rw [lintegral_v3_splitC (measurable_testFC hF)]
  have hA : AEMeasurable (Function.uncurry fun a b : ℂ => ∫⁻ y, testFC c Q' F (v3 a b y)) (volume.prod volume) :=
    h3.lintegral_prod_right'.aemeasurable
  rw [lintegral_lintegral_swap hA]
  have e1 : ∀ b : ℂ, ∫⁻ a, ∫⁻ y, testFC c Q' F (v3 a b y) = ∫⁻ q, ∫⁻ y, testFC c Q' F (v3 (q + b) b y) :=
    fun b => (lintegral_add_right_eq_self (fun a => ∫⁻ y, testFC c Q' F (v3 a b y)) b).symm
  rw [lintegral_congr e1]
  have h3' : Measurable fun p : (ℂ × ℂ) × (Fin k → ℂ) => testFC c Q' F (v3 (p.1.2 + p.1.1) p.1.1 p.2) :=
    (measurable_testFC hF).comp (Measurable.v3C ((measurable_snd.comp measurable_fst).add
      (measurable_fst.comp measurable_fst)) (measurable_fst.comp measurable_fst) measurable_snd)
  have hA' : AEMeasurable (Function.uncurry fun b q : ℂ => ∫⁻ y, testFC c Q' F (v3 (q + b) b y))
      (volume.prod volume) := h3'.lintegral_prod_right'.aemeasurable
  rw [lintegral_lintegral_swap hA']
  refine lintegral_congr fun q => ?_
  have h2 : Measurable fun p : ℂ × (Fin k → ℂ) => testFC c Q' F (v3 (q + p.1) p.1 p.2) :=
    (measurable_testFC hF).comp (Measurable.v3C (measurable_const.add measurable_fst) measurable_fst measurable_snd)
  exact lintegral_lintegral_swap h2.aemeasurable

omit hc hQ' in
theorem measurable_WC {F : (Fin (k + 1 + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F) :
    Measurable fun p : ℂ × (Fin k → ℂ) × ℂ =>
      F (graphVC c Q' (p.1 / sqrtC p.2.2) ((sqrtC p.2.2)⁻¹ • p.2.1)) := by
  have hs : Measurable fun p : ℂ × (Fin k → ℂ) × ℂ => sqrtC p.2.2 :=
    measurable_sqrtC.comp (measurable_snd.comp measurable_snd)
  have hg : Measurable fun p : ℂ × (Fin k → ℂ) × ℂ =>
      ((p.1 / sqrtC p.2.2, (sqrtC p.2.2)⁻¹ • p.2.1) : ℂ × (Fin k → ℂ)) :=
    (measurable_fst.div hs).prodMk (hs.inv.smul (measurable_fst.comp measurable_snd))
  have := hF.comp ((measurable_graphVC (c := c) (Q' := Q')).comp hg)
  exact this

omit hQ' in
theorem lintegral_testFC_u {F : (Fin (k + 1 + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, testFC c Q' F x = ∫⁻ u, phiC u * ∫⁻ q, ∫⁻ y, dens2 2 q *
      F (graphVC c Q' (q / sqrtC u) ((sqrtC u)⁻¹ • y)) := by
  have hW := measurable_WC (c := c) (Q' := Q') hF
  rw [lintegral_testFC_reorder hc hF]
  have hae : ∀ᵐ q : ℂ, q ≠ 0 := by
    rw [ae_iff]; simp only [ne_eq, not_not, ofPred_eq_eq_singleton, measure_singleton]
  have hB : ∀ᵐ q : ℂ, (∫⁻ y, ∫⁻ b, testFC c Q' F (v3 (q + b) b y)) =
      ∫⁻ y, ∫⁻ u, dens2 2 q * (phiC u * F (graphVC c Q' (q / sqrtC u) ((sqrtC u)⁻¹ • y))) := by
    filter_upwards [hae] with q hq
    refine lintegral_congr fun y => ?_
    simp_rw [testFC_v3_eq hc hq]
    have hΨ : Measurable fun u : ℂ => phiC u * F (graphVC c Q' (q / sqrtC u) ((sqrtC u)⁻¹ • y)) :=
      measurable_phiC.mul (hW.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
    rw [lintegral_comp_affineC (Ψ := fun u => phiC u * F (graphVC c Q' (q / sqrtC u) ((sqrtC u)⁻¹ • y)))
      hΨ (mul_ne_zero two_ne_zero hq), lintegral_const_mul _ hΨ, dens2]
  rw [lintegral_congr_ae hB]
  have hm3 : Measurable fun p : ℂ × (Fin k → ℂ) × ℂ =>
      dens2 2 p.1 * (phiC p.2.2 * F (graphVC c Q' (p.1 / sqrtC p.2.2) ((sqrtC p.2.2)⁻¹ • p.2.1))) :=
    ((measurable_dens2 2).comp measurable_fst).mul
      ((measurable_phiC.comp (measurable_snd.comp measurable_snd)).mul hW)
  have e2 : ∀ q : ℂ, (∫⁻ y, ∫⁻ u, dens2 2 q *
      (phiC u * F (graphVC c Q' (q / sqrtC u) ((sqrtC u)⁻¹ • y))))
      = ∫⁻ u, ∫⁻ y, dens2 2 q * (phiC u * F (graphVC c Q' (q / sqrtC u) ((sqrtC u)⁻¹ • y))) := by
    intro q
    have := hm3.comp ((measurable_const (a := q)).prodMk measurable_id)
    simp only [Function.comp_def] at this
    exact lintegral_lintegral_swap this.aemeasurable
  simp_rw [e2]
  have hm3' : Measurable fun p : ℂ × ℂ => ∫⁻ y, dens2 2 p.1 *
      (phiC p.2 * F (graphVC c Q' (p.1 / sqrtC p.2) ((sqrtC p.2)⁻¹ • y))) := by
    have : Measurable fun p : (ℂ × ℂ) × (Fin k → ℂ) => dens2 2 p.1.1 *
        (phiC p.1.2 * F (graphVC c Q' (p.1.1 / sqrtC p.1.2) ((sqrtC p.1.2)⁻¹ • p.2))) :=
      by have := hm3.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.prodMk
            (measurable_snd.comp measurable_fst)))
         simp only [Function.comp_def] at this
         exact this
    exact this.lintegral_prod_right'
  rw [lintegral_lintegral_swap hm3'.aemeasurable]
  refine lintegral_congr fun u => ?_
  rw [← lintegral_const_mul' _ _ (by unfold phiC; by_cases h : u ∈ {u : ℂ | 0 < u.re ∧ ‖u‖ < 1} <;> simp [h])]
  refine lintegral_congr fun q => ?_
  rw [← lintegral_const_mul' _ _ (by unfold phiC; by_cases h : u ∈ {u : ℂ | 0 < u.re ∧ ‖u‖ < 1} <;> simp [h])]
  refine lintegral_congr fun y => ?_
  ring


omit hc hQ' in
theorem dens2_mul (α s q : ℂ) (hs : s ≠ 0) :
    dens2 α (s * q) = (((‖s‖₊ ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞) * dens2 α q := by
  unfold dens2
  rw [← ENNReal.coe_mul, ← mul_inv, ← mul_pow, ← nnnorm_mul]
  congr 3
  ring

omit hc hQ' in
theorem nnnorm_sqrtC_sq (u : ℂ) : ‖sqrtC u‖₊ ^ 2 = ‖u‖₊ := by
  rw [← nnnorm_pow, sqrtC_sq]

omit hc hQ' in
/-- Step E: the substitution $q = s\tilde q$, $y = s\tilde y$ ($s = u^{1/2}$) gives the factor $|u|^k$. -/
theorem lintegral_graph_scaleC {F : (Fin (k + 1 + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F) {u : ℂ} (hu : u ≠ 0) :
    ∫⁻ q, ∫⁻ y, dens2 2 q * F (graphVC c Q' (q / sqrtC u) ((sqrtC u)⁻¹ • y)) =
      ((‖u‖₊ ^ k : ℝ≥0) : ℝ≥0∞) * ∫⁻ q, ∫⁻ y, dens2 2 q * F (graphVC c Q' q y) := by
  set s := sqrtC u with hs_def
  have hs : s ≠ 0 := sqrtC_ne_zero hu
  have hGm : Measurable fun p : ℂ × (Fin k → ℂ) => F (graphVC c Q' p.1 p.2) :=
    hF.comp (measurable_graphVC (c := c) (Q' := Q'))
  set K : ℂ → ℝ≥0∞ := fun q => ∫⁻ y, F (graphVC c Q' q y) with hK
  have hKm : Measurable K := hGm.lintegral_prod_right'
  have h1 : ∀ q : ℂ, ∫⁻ y, dens2 2 q * F (graphVC c Q' (q / s) (s⁻¹ • y)) =
      dens2 2 q * (((‖s‖₊ ^ (2 * k)) : ℝ≥0) : ℝ≥0∞) * K (q / s) := by
    intro q
    rw [lintegral_const_mul' _ _ (by unfold dens2; exact ENNReal.coe_ne_top), mul_assoc]
    congr 1
    have := lintegral_smul_vecC (K := fun y => F (graphVC c Q' (q / s) y))
      (hGm.comp (measurable_const.prodMk measurable_id)) (inv_ne_zero hs)
    beta_reduce at this
    rw [hK]
    beta_reduce
    rw [this, ← mul_assoc, ← ENNReal.coe_mul, nnnorm_inv, inv_pow,
      mul_inv_cancel₀ (pow_ne_zero _ (nnnorm_ne_zero_iff.mpr hs)), ENNReal.coe_one, one_mul]
  simp_rw [h1]
  have hΨ : Measurable fun q : ℂ => dens2 2 q * (((‖s‖₊ ^ (2 * k)) : ℝ≥0) : ℝ≥0∞) * K (q / s) :=
    ((measurable_dens2 2).mul measurable_const).mul (hKm.comp (measurable_id.div_const s))
  have h2 := lintegral_comp_affineC hΨ hs 0
  simp only [add_zero] at h2
  have h3 : ∫⁻ q, dens2 2 q * (((‖s‖₊ ^ (2 * k)) : ℝ≥0) : ℝ≥0∞) * K (q / s) =
      ((‖s‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) * ∫⁻ q, dens2 2 (s * q) * (((‖s‖₊ ^ (2 * k)) : ℝ≥0) : ℝ≥0∞) * K (s * q / s) := by
    rw [h2, ← mul_assoc, ← ENNReal.coe_mul, mul_inv_cancel₀ (pow_ne_zero _ (nnnorm_ne_zero_iff.mpr hs)),
      ENNReal.coe_one, one_mul]
  rw [h3]
  have h4 : ∀ q : ℂ, dens2 2 (s * q) * (((‖s‖₊ ^ (2 * k)) : ℝ≥0) : ℝ≥0∞) * K (s * q / s) =
      (((‖s‖₊ ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞) * (((‖s‖₊ ^ (2 * k)) : ℝ≥0) : ℝ≥0∞) * (dens2 2 q * K q) := by
    intro q
    rw [mul_div_cancel_left₀ _ hs, dens2_mul 2 s q hs]
    ring
  simp_rw [h4]
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top), ← mul_assoc,
    ← mul_assoc, ← ENNReal.coe_mul, mul_inv_cancel₀ (pow_ne_zero _ (nnnorm_ne_zero_iff.mpr hs)), ENNReal.coe_one,
    one_mul, pow_mul, nnnorm_sqrtC_sq]
  congr 1
  refine lintegral_congr fun q => ?_
  rw [hK, lintegral_const_mul' _ _ (by unfold dens2; exact ENNReal.coe_ne_top)]

/-- The radial integral $I = \int_D |u|^k\,d^2u$ (only $0 < I < \infty$ is used). -/
def radIC (k : ℕ) : ℝ≥0∞ := ∫⁻ u, phiC u * ((‖u‖₊ ^ k : ℝ≥0) : ℝ≥0∞)

omit hc hQ' in
theorem measurable_radIC_integrand : Measurable fun u : ℂ => phiC u * ((‖u‖₊ ^ k : ℝ≥0) : ℝ≥0∞) :=
  measurable_phiC.mul ((continuous_nnnorm.pow k).measurable.coe_nnreal_ennreal)

omit hc hQ' in
theorem radIC_ne_top : radIC k ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ u, phiC u) ?_ (lintegral_mono fun u => ?_)
  · rw [phiC, lintegral_indicator measurableSet_DC]
    simp only [Pi.one_apply, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul]
    refine ne_top_of_le_ne_top (b := volume (Metric.ball (0 : ℂ) 1)) measure_ball_lt_top.ne
      (measure_mono fun u hu => by simpa using hu.2)
  · by_cases hu : u ∈ {u : ℂ | 0 < u.re ∧ ‖u‖ < 1}
    · rw [phiC, indicator_of_mem hu, Pi.one_apply, one_mul]
      have : ‖u‖₊ ^ k ≤ 1 := pow_le_one₀ bot_le (by
        have := hu.2; exact_mod_cast this.le)
      exact ENNReal.coe_le_one_iff.mpr this
    · rw [phiC, indicator_of_notMem hu, zero_mul]

omit hc hQ' in
theorem radIC_ne_zero : radIC k ≠ 0 := by
  intro h
  rw [radIC, lintegral_eq_zero_iff measurable_radIC_integrand] at h
  have hsub : {u : ℂ | 0 < u.re ∧ ‖u‖ < 1} ⊆ {u | phiC u * ((‖u‖₊ ^ k : ℝ≥0) : ℝ≥0∞) ≠ 0} := by
    intro u hu
    have hu0 : u ≠ 0 := fun h => by subst h; simp at hu
    simp only [mem_ofPred_eq, phiC, indicator_of_mem hu, Pi.one_apply, one_mul, ne_eq, ENNReal.coe_eq_zero,
      pow_eq_zero_iff', nnnorm_eq_zero, hu0, false_and, not_false_eq_true]
  have h0 : volume {u : ℂ | phiC u * ((‖u‖₊ ^ k : ℝ≥0) : ℝ≥0∞) ≠ 0} = 0 := by
    rw [Filter.EventuallyEq, ae_iff] at h
    simpa using h
  have hpos : 0 < volume {u : ℂ | 0 < u.re ∧ ‖u‖ < 1} := by
    refine IsOpen.measure_pos _ ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)) ⟨1 / 2, by norm_num, by norm_num⟩
  exact hpos.ne' (measure_mono_null hsub h0)

omit hQ' in
/-- **The coordinate side** (complex): $\int f\,dx = I\cdot\int\int |2q|^{-2}F(\mathrm{graph}(q, y))$. -/
theorem lintegral_testFC_coords {F : (Fin (k + 1 + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, testFC c Q' F x = radIC k * ∫⁻ q, ∫⁻ y, dens2 2 q * F (graphVC c Q' q y) := by
  rw [lintegral_testFC_u hc hF, radIC, ← lintegral_mul_const _ measurable_radIC_integrand]
  refine lintegral_congr fun u => ?_
  by_cases hu : 0 < u.re
  · have hu0 : u ≠ 0 := fun h => by rw [h, Complex.zero_re] at hu; exact lt_irrefl _ hu
    rw [lintegral_graph_scaleC hF hu0, mul_assoc]
  · rw [phiC_eq_zero hu, zero_mul, zero_mul, zero_mul]


omit hc hQ' in
theorem re_sqrtC_pos {u : ℂ} (hu : 0 < u.re) : 0 < (sqrtC u).re := by
  rw [sqrtC, Complex.cpow_inv_two_re]
  apply Real.sqrt_pos.mpr
  have := norm_nonneg u
  linarith

omit hQ' in
/-- **The polar side** (complex): by the polar coordinates on the half plane,
$\int f\,dx = \int_{\operatorname{Re}\beta>0}\varphi(\beta^2)\,d\lambda(\beta)\cdot\int_{S_c}F\,d\nu_c$. -/
theorem lintegral_testFC_polar {F : (Fin (k + 1 + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, testFC c Q' F x =
      (∫⁻ β in halfU, phiC ((β : ℂ) ^ 2) ∂lamU (k + 1 + 1)) * ∫⁻ x, F x ∂nuC (coneForm c Q') c := by
  have hn : 1 ≤ k + 1 + 1 := by omega
  have hS : MeasurableSet (polC (coneForm c Q') c '' (halfU ×ˢ univ)) :=
    (isOpen_halfU.measurableSet.prod MeasurableSet.univ).image_of_continuousOn_injOn
      (continuous_polC _ _).continuousOn (injOn_polC_halfU hc)
  have hvan : ∫⁻ x, testFC c Q' F x = ∫⁻ x in polC (coneForm c Q') c '' (halfU ×ˢ univ), testFC c Q' F x := by
    rw [← lintegral_indicator hS]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ polC (coneForm c Q') c '' (halfU ×ˢ univ)
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy, testFC]
      by_cases hu : 0 < ((coneForm c Q').eval y / c).re
      · exfalso; apply hy
        set u := (coneForm c Q').eval y / c
        have hu0 : u ≠ 0 := fun h => by rw [h, Complex.zero_re] at hu; exact lt_irrefl _ hu
        set β := sqrtC u
        have hβ0 : β ≠ 0 := sqrtC_ne_zero hu0
        have hβ2 : β ^ 2 = u := sqrtC_sq u
        have hmem : β⁻¹ • y ∈ sphC (coneForm c Q') c := by
          show (coneForm c Q').eval (β⁻¹ • y) = c
          rw [eval_smulC, inv_pow, hβ2]
          have : (coneForm c Q').eval y = c * u := by simp only [u]; field_simp
          rw [this]; field_simp
        refine ⟨(Units.mk0 β hβ0, ⟨β⁻¹ • y, hmem⟩), ⟨?_, mem_univ _⟩, ?_⟩
        · show 0 < (β : ℂ).re
          exact re_sqrtC_pos hu
        · show (β : ℂ) • (β⁻¹ • y) = y
          rw [smul_smul, mul_inv_cancel₀ hβ0, one_smul]
      · rw [phiC_eq_zero hu, zero_mul]
  rw [hvan, lintegral_polC_half hc hn (measurable_testFC hF)]
  have hpt : ∀ β ∈ halfU, ∫⁻ x, testFC c Q' F ((β : ℂ) • (x : Fin (k + 1 + 1) → ℂ)) ∂nuC (coneForm c Q') c =
      phiC ((β : ℂ) ^ 2) * ∫⁻ x, F x ∂nuC (coneForm c Q') c := by
    intro β hβ
    have hβre : 0 < (β : ℂ).re := hβ
    have hpt' : ∀ x : SphC (coneForm c Q') c,
        testFC c Q' F ((β : ℂ) • (x : Fin (k + 1 + 1) → ℂ)) = phiC ((β : ℂ) ^ 2) * F x := by
      intro x
      have hx : (coneForm c Q').eval (x : Fin (k + 1 + 1) → ℂ) = c := x.2
      have h1 : (coneForm c Q').eval ((β : ℂ) • (x : Fin (k + 1 + 1) → ℂ)) / c = (β : ℂ) ^ 2 := by
        rw [eval_smulC, hx, mul_div_assoc, div_self hc, mul_one]
      rw [testFC, h1, sqrtC, Complex.sq_cpow_two_inv hβre, smul_smul, inv_mul_cancel₀ β.ne_zero, one_smul]
    simp_rw [hpt']
    rw [lintegral_const_mul' _ _ (by unfold phiC; by_cases h : ((β : ℂ) ^ 2) ∈ {u : ℂ | 0 < u.re ∧ ‖u‖ < 1} <;>
      simp [h])]
  rw [setLIntegral_congr_fun isOpen_halfU.measurableSet hpt]
  have hm : Measurable fun β : ℂˣ => phiC ((β : ℂ) ^ 2) :=
    measurable_phiC.comp ((Units.continuous_val.pow 2).measurable)
  exact lintegral_mul_const _ hm


omit hc hQ' in
/-- $\int_{\operatorname{Re}\beta>0}G\,d\lambda_{k+2} = \int_{\operatorname{Re}z>0}|z|^{2k+2}G(z)\,d^2z$. -/
theorem setLIntegral_halfU_lamU {G : ℂ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ β in halfU, G β ∂lamU (k + 1 + 1) = ∫⁻ z in halfC, ((‖z‖₊ ^ (2 * k + 2) : ℝ≥0) : ℝ≥0∞) * G z := by
  set g : ℂ → ℝ≥0∞ := halfC.indicator fun z => ((‖z‖₊ ^ (2 * k + 2) : ℝ≥0) : ℝ≥0∞) * G z with hg
  have hw : ∀ β : ℂˣ, SphereLerayC.wt (2 * ((k + 1 + 1 : ℕ) : ℤ) - 2) β = ((‖(β : ℂ)‖₊ ^ (2 * k + 2) : ℝ≥0) : ℝ≥0∞) := by
    intro β
    rw [SphereLerayC.wt, show (2 * ((k + 1 + 1 : ℕ) : ℤ) - 2) = ((2 * k + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  rw [lamU, setLIntegral_withDensity_eq_setLIntegral_mul _ (SphereLerayC.measurable_wt _)
    (g := fun β : ℂˣ => G β) (hG.comp Units.continuous_val.measurable) isOpen_halfU.measurableSet, ← lintegral_indicator isOpen_halfU.measurableSet]
  have e : ∀ β : ℂˣ, halfU.indicator ((SphereLerayC.wt (2 * ((k + 1 + 1 : ℕ) : ℤ) - 2)) * fun β : ℂˣ => G β) β =
      g (β : ℂ) := by
    intro β
    by_cases hβ : β ∈ halfU
    · rw [indicator_of_mem hβ, hg, indicator_of_mem (show (β : ℂ) ∈ halfC from hβ), Pi.mul_apply, hw]
    · rw [indicator_of_notMem hβ, hg, indicator_of_notMem (show (β : ℂ) ∉ halfC from hβ)]
  simp_rw [e]
  show ∫⁻ β : ℂˣ, g (β : ℂ) ∂(Measure.comap Units.val volume) = _
  rw [← measurableEmbedding_val.lintegral_map, measurableEmbedding_val.map_comap, hg,
    lintegral_indicator measurableSet_halfC, Measure.restrict_restrict measurableSet_halfC]
  congr 2
  refine inter_eq_left.mpr fun z hz => ⟨Units.mk0 z (ne_zero_of_mem_halfC hz), rfl⟩

omit hc hQ' in
/-- **The substitution $u = \beta^2$**: $I = \int_D|u|^k\,d^2u = 4\int_{\operatorname{Re}\beta>0}\varphi(\beta^2)\,d\lambda(\beta)$. -/
theorem radIC_eq : radIC k = 4 * ∫⁻ β in halfU, phiC ((β : ℂ) ^ 2) ∂lamU (k + 1 + 1) := by
  rw [setLIntegral_halfU_lamU (G := fun z : ℂ => phiC (z ^ 2)) (measurable_phiC.comp (measurable_id.pow_const 2))]
  set f : ℂ → ℂ := fun z => z ^ 2
  have hinj : InjOn f halfC := fun β hβ β' hβ' h =>
    eq_of_sq_eq_half (c := 1) one_ne_zero hβ hβ' (by simpa [f] using h)
  have hsupp : ∀ u : ℂ, u ∉ f '' halfC → phiC u * ((‖u‖₊ ^ k : ℝ≥0) : ℝ≥0∞) = 0 := by
    intro u hu
    by_cases h0 : 0 < u.re
    · exfalso; exact hu ⟨sqrtC u, re_sqrtC_pos h0, sqrtC_sq u⟩
    · rw [phiC_eq_zero h0, zero_mul]
  have hmS : MeasurableSet (f '' halfC) :=
    measurableSet_halfC.image_of_continuousOn_injOn (by fun_prop) hinj
  have hstep : radIC k = ∫⁻ u in f '' halfC, phiC u * ((‖u‖₊ ^ k : ℝ≥0) : ℝ≥0∞) := by
    rw [radIC, ← lintegral_indicator hmS]
    refine lintegral_congr fun u => ?_
    by_cases hu : u ∈ f '' halfC
    · rw [indicator_of_mem hu]
    · rw [indicator_of_notMem hu, hsupp u hu]
  rw [hstep, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_halfC
    (f' := fun β => (ContinuousLinearMap.toSpanSingleton ℂ (2 * β)).restrictScalars ℝ)
    (fun β _ => by
      have h : HasDerivAt f (2 * β) β := by
        have := hasDerivAt_pow 2 β
        convert this using 1; simp
      exact (h.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hinj]
  rw [← lintegral_const_mul' _ _ (by norm_num)]
  refine setLIntegral_congr_fun measurableSet_halfC fun z hz => ?_
  rw [det_toSpanSingleton, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
  simp only [f]
  rw [mul_comm (phiC (z ^ 2)), ← mul_assoc, ← mul_assoc]
  congr 1
  have e1 : ∀ m : ℕ, ((‖z‖₊ ^ m : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (‖z‖ ^ m) := fun m => by
    rw [← ENNReal.ofReal_coe_nnreal]; push_cast; rfl
  rw [nnnorm_pow, ← pow_mul, e1, e1, show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  rw [norm_mul, Complex.norm_two]
  ring


omit hQ' in
/-- **The hyperbolic-split chart of the complex sphere** ($c \ne 0$): in the graph coordinates
$(q, y) \mapsto x = (b + q, b, y)$ of $S_c$,
$$\int_{S_c}F\,d\sigma_c = \int_{\mathbb C}\int_{\mathbb C^k}\frac{F(\mathrm{graph}(q, y))}{|2cq|^2}\,d^2y\,d^2q,$$
i.e. $\sigma_c = d^2q\,d^2x'/|2cq|_{\mathbb C}$ (= $dx/dQ$ with $|\cdot|_{\mathbb C}$), and $\{x_0 = x_1\}$ is null. -/
@[kb "weil1982" "§2.2 (the Leray form dx/dQ in a chart, complex place) [unverified]"]
theorem lintegral_sigC_graph {F : (Fin (k + 1 + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂sigC (coneForm c Q') c = ∫⁻ q, ∫⁻ y, dens2 (2 * c) q * F (graphVC c Q' q y) := by
  set Iβ := ∫⁻ β in halfU, phiC ((β : ℂ) ^ 2) ∂lamU (k + 1 + 1)
  have h1 := lintegral_testFC_polar hc hF (Q' := Q')
  rw [lintegral_testFC_coords hc hF, radIC_eq] at h1
  have hI0 : Iβ ≠ 0 := by
    intro h; apply radIC_ne_zero (k := k); rw [radIC_eq]; simp [Iβ, h]
  have hIt : Iβ ≠ ⊤ := by
    intro h; apply radIC_ne_top (k := k); rw [radIC_eq]; simp [Iβ, h]
  have h2 : ∫⁻ x, F x ∂nuC (coneForm c Q') c = 4 * ∫⁻ q, ∫⁻ y, dens2 2 q * F (graphVC c Q' q y) := by
    rw [mul_assoc, mul_comm (4 : ℝ≥0∞), mul_assoc] at h1
    rw [((ENNReal.mul_right_inj hI0 hIt).mp h1).symm, mul_comm]
  have hc0 : (‖2 * c‖₊ : ℝ≥0) ≠ 0 := nnnorm_ne_zero_iff.mpr (mul_ne_zero two_ne_zero hc)
  rw [sigC, lintegral_smul_measure, h2, smul_eq_mul, ← mul_assoc, ← lintegral_const_mul' _ _ (by
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (by norm_num))]
  refine lintegral_congr fun q => ?_
  rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.coe_ne_top (by norm_num))]
  refine lintegral_congr fun y => ?_
  rw [← mul_assoc]
  congr 1
  unfold dens2
  by_cases hq : q = 0
  · simp [hq]
  · have h4 : (4 : ℝ≥0∞) = ((4 : ℝ≥0) : ℝ≥0∞) := by norm_num
    rw [h4, ← ENNReal.coe_mul, ← ENNReal.coe_mul]
    congr 1
    have h2' : ‖(2 : ℂ)‖₊ = 2 := by
      rw [← NNReal.coe_inj]; simp
    simp only [nnnorm_mul, h2']
    have hq0 : ‖q‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr hq
    have hcn : ‖c‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr hc
    field_simp
    ring


/-! ### A section of $SO(Q)(\mathbb C) \to S_c$ through the parabolic -/

omit hQ' in
theorem dM_nM_e₀C {q : ℂ} (hq : q ≠ 0) (y : Fin k → ℂ) :
    dM q⁻¹ *ᵥ (nM c Q' y *ᵥ (e₀ : Fin (k + 1 + 1) → ℂ)) = graphVC c Q' q y := by
  rw [nM_mulVec_e₀ c Q' hc, dM_mulVec_v3, graphVC, graphBC, inv_inv]
  refine v3_congr ?_ ?_ rfl <;> field_simp <;> ring

omit hQ' in
theorem graphVC_of_mem {x : Fin (k + 1 + 1) → ℂ} (hx : (coneForm c Q').eval x = c) (hq : x 0 - x 1 ≠ 0) :
    graphVC c Q' (x 0 - x 1) (tl x) = x := by
  conv_rhs => rw [← v3_eta x]
  rw [eval_coneForm] at hx
  have hb : graphBC c Q' (x 0 - x 1) (tl x) = x 1 := by
    rw [graphBC, div_eq_iff (mul_ne_zero two_ne_zero hq)]
    have : Q'.eval (tl x) / c = 1 - (x 0 ^ 2 - x 1 ^ 2) := by
      rw [div_eq_iff hc]; linear_combination hx
    rw [this]; ring
  rw [graphVC, hb]
  refine v3_congr (by ring) rfl rfl

/-- **The parabolic section** of $SO(Q)(\mathbb C) \to S_c$: $s(x) = d((x_0 - x_1)^{-1})\,n(x')$ on $\{x_0 \ne x_1\}$,
The reflection section on the null set $\{x_0 = x_1\}$. -/
def secCC (x : SphC (coneForm c Q') c) : ArchSOC (coneForm c Q') :=
  if h : (x : Fin (k + 1 + 1) → ℂ) 0 - (x : Fin (k + 1 + 1) → ℂ) 1 ≠ 0 then
    dG hc hQ' (inv_ne_zero h) * nG hc hQ' (tl (x : Fin (k + 1 + 1) → ℂ))
  else (sphSectionC hc (by omega : 1 ≤ k + 1) (gramDetC_Qm hc hQ')).toFun x

theorem secCC_spec (x : SphC (coneForm c Q') c) :
    ArchSOC.mat _ (secCC hc hQ' x) *ᵥ (e₀ : Fin (k + 1 + 1) → ℂ) = (x : Fin (k + 1 + 1) → ℂ) := by
  unfold secCC
  by_cases h : (x : Fin (k + 1 + 1) → ℂ) 0 - (x : Fin (k + 1 + 1) → ℂ) 1 ≠ 0
  · rw [dif_pos h, ArchSOC.mat_mul, mat_dG, mat_nG, ← mulVec_mulVec, dM_nM_e₀C hc (q := _) h,
      graphVC_of_mem hc x.2 h]
  · rw [dif_neg h]
    exact (sphSectionC hc (by omega : 1 ≤ k + 1) (gramDetC_Qm hc hQ')).spec x

theorem measurable_secCC : Measurable (secCC hc hQ') := by
  have hU : MeasurableSet {x : SphC (coneForm c Q') c | (x : Fin (k + 1 + 1) → ℂ) 0 - (x : Fin (k + 1 + 1) → ℂ) 1 ≠ 0} :=
    (isOpen_ne_fun ((continuous_apply 0).comp continuous_subtype_val |>.sub
      ((continuous_apply 1).comp continuous_subtype_val)) continuous_const).measurableSet
  set U : Set (SphC (coneForm c Q') c) := {x | (x : Fin (k + 1 + 1) → ℂ) 0 - (x : Fin (k + 1 + 1) → ℂ) 1 ≠ 0}
  refine measurable_of_restrict_of_restrict_compl hU ?_ ?_
  swap
  · have e : Uᶜ.domRestrict (secCC hc hQ') = fun y : ↥Uᶜ =>
        (sphSectionC hc (by omega : 1 ≤ k + 1) (gramDetC_Qm hc hQ')).toFun y.1 := by
      funext y; show secCC hc hQ' y.1 = _; unfold secCC
      rw [dif_neg (show ¬ (((y : SphC (coneForm c Q') c) : Fin (k + 1 + 1) → ℂ) 0 -
        ((y : SphC (coneForm c Q') c) : Fin (k + 1 + 1) → ℂ) 1 ≠ 0) from y.2)]
    rw [e]
    exact (sphSectionC hc (by omega : 1 ≤ k + 1) (gramDetC_Qm hc hQ')).measurable.comp measurable_subtype_coe
  have e : U.domRestrict (secCC hc hQ') = fun y : ↥U =>
      dG hc hQ' (inv_ne_zero y.2) * nG hc hQ' (tl ((y : SphC (coneForm c Q') c) : Fin (k + 1 + 1) → ℂ)) := by
    funext y; show secCC hc hQ' y.1 = _; unfold secCC
    rw [dif_pos (show ((y : SphC (coneForm c Q') c) : Fin (k + 1 + 1) → ℂ) 0 -
        ((y : SphC (coneForm c Q') c) : Fin (k + 1 + 1) → ℂ) 1 ≠ 0 from y.2)]
  rw [e]
  have hq : Continuous fun x : ↥U =>
      (((x : SphC (coneForm c Q') c) : Fin (k + 1 + 1) → ℂ) 0 - ((x : SphC (coneForm c Q') c) : Fin (k + 1 + 1) → ℂ) 1) :=
    ((continuous_apply 0).comp (continuous_subtype_val.comp continuous_subtype_val)).sub
      ((continuous_apply 1).comp (continuous_subtype_val.comp continuous_subtype_val))
  have hqi : Continuous fun x : ↥U =>
      (⟨(((x : SphC (coneForm c Q') c) : Fin (k + 1 + 1) → ℂ) 0 -
        ((x : SphC (coneForm c Q') c) : Fin (k + 1 + 1) → ℂ) 1)⁻¹, inv_ne_zero x.2⟩ : {a : ℂ // a ≠ 0}) :=
    (hq.inv₀ fun x => x.2).subtype_mk _
  have hc1 : Continuous fun y : ↥U => dG hc hQ' (inv_ne_zero y.2) := by
    have := (continuous_dG' hc hQ').comp hqi
    simp only [Function.comp_def] at this
    exact this
  have hc2 : Continuous fun y : ↥U => nG hc hQ' (tl ((y : SphC (coneForm c Q') c) : Fin (k + 1 + 1) → ℂ)) :=
    (continuous_nG hc hQ').comp (continuous_tlC.comp (continuous_subtype_val.comp continuous_subtype_val))
  exact (hc1.mul hc2).measurable

/-- **The parabolic sphere section** as `SphSectionC`. -/
def coneSphSectionC : SphSectionC c (QmC c Q') := ⟨secCC hc hQ', measurable_secCC hc hQ', secCC_spec hc hQ'⟩

/-! ### Unimodularity and the parametric cone identity -/

omit hc hQ' in
theorem lintegral_inv_lerayMeasureC {n : ℕ} {Q : QuadForm ℂ n} (hQ : gramDetC Q ≠ 0) {f : ArchSOC Q → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ g, f g⁻¹ ∂lerayMeasureC Q hQ = ∫⁻ g, f g ∂lerayMeasureC Q hQ := by
  have := isHaarMeasure_lerayMeasureC hQ
  have := isMulRightInvariant_lerayMeasureC hQ
  have h := ConeReal.inv_eq_self_of_unimodular (lerayMeasureC Q hQ)
  rw [← lintegral_map hf measurable_inv, ← Measure.inv_def, h]

/-- $d(q)$ for $q \ne 0$ (and $1$ at $q = 0$). -/
def dGt (q : ℂ) : ArchSOC (coneForm c Q') := if h : q = 0 then 1 else dG hc hQ' h

theorem dGt_of_ne {q : ℂ} (h : q ≠ 0) : dGt hc hQ' q = dG hc hQ' h := dif_neg h

theorem measurable_dGt : Measurable (dGt hc hQ') := by
  refine measurable_of_continuousOn_compl_singleton 0 ?_
  rw [continuousOn_iff_continuous_domRestrict]
  have e : ({0}ᶜ : Set ℂ).domRestrict (dGt hc hQ') = fun a : ({0}ᶜ : Set ℂ) => dG hc hQ' a.2 := by
    funext a; exact dGt_of_ne hc hQ' a.2
  rw [e]
  exact (continuous_dG' hc hQ').comp (continuous_subtype_val.subtype_mk fun a => a.2)

theorem graphVC_mem {q : ℂ} (hq : q ≠ 0) (y : Fin k → ℂ) : graphVC c Q' q y ∈ sphC (coneForm c Q') c :=
  eval_graphVC hc hq y

omit hc hQ' in
theorem graphVC_sub {q : ℂ} (y : Fin k → ℂ) : graphVC c Q' q y 0 - graphVC c Q' q y 1 = q := by
  rw [graphVC]; simp

omit hc hQ' in
theorem tl_graphVC {q : ℂ} (y : Fin k → ℂ) : tl (graphVC c Q' q y) = y := by rw [graphVC, tl_v3]

theorem secCC_graph {q : ℂ} (hq : q ≠ 0) (y : Fin k → ℂ) :
    secCC hc hQ' ⟨graphVC c Q' q y, graphVC_mem hc hQ' hq y⟩ = dG hc hQ' (inv_ne_zero hq) * nG hc hQ' y := by
  unfold secCC
  have h : graphVC c Q' q y 0 - graphVC c Q' q y 1 ≠ 0 := by rw [graphVC_sub]; exact hq
  rw [dif_pos h]
  congr 1
  · exact mat_ext' (by rw [mat_dG, mat_dG, graphVC_sub])
  · rw [tl_graphVC]

theorem inv_dG_nG {q : ℂ} (hq : q ≠ 0) (y : Fin k → ℂ) :
    (dG hc hQ' (inv_ne_zero hq) * nG hc hQ' y)⁻¹ = dG hc hQ' hq * nG hc hQ' (-(q⁻¹ • y)) := by
  rw [_root_.mul_inv_rev, nG_neg, dG_inv, dG_mul_nG hc hQ' hq, smul_neg, smul_smul, mul_inv_cancel₀ hq, one_smul]
  congr 1
  exact mat_ext' (by rw [mat_dG, mat_dG, inv_inv])

omit hQ' in
theorem lintegral_sigC_graph' {G : SphC (coneForm c Q') c → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G x ∂sigC (coneForm c Q') c = ∫⁻ q, ∫⁻ y, dens2 (2 * c) q *
      Function.extend Subtype.val G 0 (graphVC c Q' q y) := by
  have he := MeasurableEmbedding.subtype_coe (isClosed_sphC (coneForm c Q') c).measurableSet
  have hm : Measurable (Function.extend Subtype.val G 0) := he.measurable_extend hG measurable_const
  rw [← lintegral_sigC_graph hc hm]
  refine lintegral_congr fun x => ?_
  exact (Subtype.val_injective.extend_apply G 0 x).symm

theorem mG_mul_dGt (h : ArchSOC Q') (q : ℂ) : mG c Q' h * dGt hc hQ' q = dGt hc hQ' q * mG c Q' h := by
  by_cases hq : q = 0
  · simp [dGt, hq]
  · rw [dGt_of_ne hc hQ' hq, mG_mul_dG]

/-- Step 1 (complex): sphere identity on $S_c$, inversion, sphere chart. -/
theorem lintegral_coneC_P1 {f : ArchSOC (coneForm c Q') → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ g, f g ∂lerayMeasureC (coneForm c Q') (gramDetC_cone hc hQ') =
      (((‖2 * c‖₊ ^ (2 * (k + 1)))⁻¹ : ℝ≥0) : ℝ≥0∞) * ∫⁻ q, ∫⁻ y, dens2 (2 * c) q *
        ∫⁻ h, f (iotaC c (QmC c Q') h * dGt hc hQ' q * nG hc hQ' (-(q⁻¹ • y))) ∂lerayMeasureC (QmC c Q')
          (gramDetC_Qm hc hQ') := by
  have := isHaarMeasure_lerayMeasureC (gramDetC_Qm hc hQ')
  rw [← lintegral_inv_lerayMeasureC _ hf]
  rw [lintegral_lerayMeasureC_orbital hc (gramDetC_Qm hc hQ') (coneSphSectionC hc hQ') (f := fun g => f g⁻¹)
    (hf.comp measurable_inv)]
  congr 1
  set G : SphC (coneForm c Q') c → ℝ≥0∞ := fun x => ∫⁻ h, f (iotaC c (QmC c Q') h * (secCC hc hQ' x)⁻¹)
    ∂lerayMeasureC (QmC c Q') (gramDetC_Qm hc hQ') with hG
  have hGm : Measurable G := by
    have : Measurable fun p : SphC (coneForm c Q') c × ArchSOC (QmC c Q') =>
        f (iotaC c (QmC c Q') p.2 * (secCC hc hQ' p.1)⁻¹) :=
      hf.comp (((continuous_iotaC _ _).measurable.comp measurable_snd).mul
        ((measurable_secCC hc hQ').comp measurable_fst).inv)
    exact this.lintegral_prod_right'
  have step3 : ∀ x : SphC (coneForm c Q') c, (∫⁻ h, f ((coneSphSectionC hc hQ').toFun x * iotaC c (QmC c Q') h)⁻¹
      ∂lerayMeasureC (QmC c Q') (gramDetC_Qm hc hQ')) = G x := by
    intro x
    have hF : Measurable fun h : ArchSOC (QmC c Q') => f (iotaC c (QmC c Q') h * (secCC hc hQ' x)⁻¹) :=
      hf.comp (((continuous_iotaC _ _).measurable).mul_const _)
    show _ = ∫⁻ h, f (iotaC c (QmC c Q') h * (secCC hc hQ' x)⁻¹) ∂lerayMeasureC (QmC c Q') (gramDetC_Qm hc hQ')
    rw [← lintegral_inv_lerayMeasureC _ hF]
    refine lintegral_congr fun h => ?_
    rw [map_inv, ← _root_.mul_inv_rev]
    rfl
  rw [lintegral_congr step3, lintegral_sigC_graph' hc hGm]
  refine lintegral_congr fun q => lintegral_congr fun y => ?_
  by_cases hq : q = 0
  · simp [hq, dens2]
  · congr 1
    have e := Subtype.val_injective.extend_apply G 0
      (⟨graphVC c Q' q y, graphVC_mem hc hQ' hq y⟩ : SphC (coneForm c Q') c)
    rw [show graphVC c Q' q y = ((⟨graphVC c Q' q y, graphVC_mem hc hQ' hq y⟩ : SphC (coneForm c Q') c) :
      Fin (k + 1 + 1) → ℂ) from rfl, e, hG]
    simp only
    rw [secCC_graph hc hQ' hq, inv_dG_nG hc hQ' hq, dGt_of_ne hc hQ' hq]
    simp only [mul_assoc]

/-- Step 2 (complex): sphere identity for $SO(\langle -c\rangle \perp Q')$ on $S'_{-c}$. -/
theorem lintegral_coneC_P2 (s' : SphSectionC (-c) Q') {f : ArchSOC (coneForm c Q') → ℝ≥0∞} (hf : Measurable f)
    (q : ℂ) (w₀ : Fin k → ℂ) :
    ∫⁻ h, f (iotaC c (QmC c Q') h * dGt hc hQ' q * nG hc hQ' w₀) ∂lerayMeasureC (QmC c Q') (gramDetC_Qm hc hQ') =
      (((‖2 * c‖₊ ^ (2 * k))⁻¹ : ℝ≥0) : ℝ≥0∞) * ∫⁻ y, ∫⁻ h, f (iotaC c (QmC c Q') (s'.toFun y) * dGt hc hQ' q *
        nG hc hQ' (ArchSOC.mat _ h *ᵥ w₀) * mG c Q' h) ∂lerayMeasureC Q' hQ' ∂sigC (QmC c Q') (-c) := by
  have hF : Measurable fun h : ArchSOC (QmC c Q') => f (iotaC c (QmC c Q') h * dGt hc hQ' q * nG hc hQ' w₀) :=
    hf.comp (((continuous_iotaC _ _).measurable.mul_const _).mul_const _)
  rw [lintegral_lerayMeasureC_orbital (neg_ne_zero.mpr hc) hQ' s' hF]
  have habs : ‖2 * -c‖₊ = ‖2 * c‖₊ := by rw [mul_neg, nnnorm_neg]
  rw [habs]
  congr 1
  refine lintegral_congr fun y => lintegral_congr fun h => ?_
  congr 1
  rw [map_mul]
  change iotaC c (QmC c Q') (s'.toFun y) * mG c Q' h * dGt hc hQ' q * nG hc hQ' w₀ = _
  rw [mul_assoc (iotaC c (QmC c Q') (s'.toFun y)), mG_mul_dGt, ← mul_assoc, mul_assoc _ (mG c Q' h),
    mG_mul_nG, ← mul_assoc]

omit hc hQ' in
theorem lintegral_smul_vecC' {Ψ : (Fin k → ℂ) → ℝ≥0∞} (hΨ : Measurable Ψ) {a : ℂ} (ha : a ≠ 0) :
    ∫⁻ z, Ψ (a • z) = ((‖a⁻¹‖₊ ^ (2 * k) : ℝ≥0) : ℝ≥0∞) * ∫⁻ w, Ψ w := by
  have := lintegral_smul_vecC (K := fun z => Ψ (a • z)) (hΨ.comp (measurable_const_smul a)) (inv_ne_zero ha)
  rw [this]
  congr 1
  refine lintegral_congr fun w => ?_
  rw [smul_smul, mul_inv_cancel₀ ha, one_smul]

/-- Step 3 (complex): the substitution $w = h(-q^{-1}y)$ on $\mathbb C^k$, Jacobian $|q|^{-2k}$. -/
theorem lintegral_coneC_P3 {q : ℂ} (hq : q ≠ 0)
    {Φ : SphC (QmC c Q') (-c) × ArchSOC Q' × (Fin k → ℂ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ y, ∫⁻ x, ∫⁻ h, Φ (x, h, ArchSOC.mat _ h *ᵥ (-(q⁻¹ • y))) ∂lerayMeasureC Q' hQ' ∂sigC (QmC c Q') (-c) =
      ((‖q‖₊ ^ (2 * k) : ℝ≥0) : ℝ≥0∞) * ∫⁻ x, ∫⁻ h, ∫⁻ w, Φ (x, h, w) ∂volume ∂lerayMeasureC Q' hQ'
        ∂sigC (QmC c Q') (-c) := by
  have := isHaarMeasure_lerayMeasureC hQ'
  have := sigmaFinite_sigC (Q := QmC c Q') (neg_ne_zero.mpr hc) (by omega)
  have hM : Continuous fun h : ArchSOC Q' => ArchSOC.mat _ h := ArchSOC.continuous_mat Q'
  have hm3 : Measurable fun p : ((Fin k → ℂ) × SphC (QmC c Q') (-c)) × ArchSOC Q' =>
      Φ (p.1.2, p.2, ArchSOC.mat _ p.2 *ᵥ (-(q⁻¹ • p.1.1))) := by
    refine hΦ.comp ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.prodMk ?_))
    exact ((hM.comp continuous_snd).matrix_mulVec
      ((continuous_const_smul _).comp (continuous_fst.comp continuous_fst)).neg).measurable
  rw [lintegral_lintegral_swap hm3.lintegral_prod_right'.aemeasurable]
  rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_congr fun x => ?_
  have hm2 : Measurable fun p : (Fin k → ℂ) × ArchSOC Q' => Φ (x, p.2, ArchSOC.mat _ p.2 *ᵥ (-(q⁻¹ • p.1))) :=
    hm3.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  rw [lintegral_lintegral_swap hm2.aemeasurable, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_congr fun h => ?_
  have e : ∀ y : Fin k → ℂ, ArchSOC.mat _ h *ᵥ (-(q⁻¹ • y)) = (-q⁻¹) • (ArchSOC.mat _ h *ᵥ y) := by
    intro y; rw [mulVec_neg, mulVec_smul, neg_smul]
  simp_rw [e]
  have hΨ : Measurable fun z : Fin k → ℂ => Φ (x, h, (-q⁻¹) • z) :=
    hΦ.comp (measurable_const.prodMk (measurable_const.prodMk (measurable_const_smul _)))
  have hdet : ‖(ArchSOC.mat _ h).det‖ = 1 := by rw [ArchSOC.det_mat, norm_one]
  rw [(measurePreserving_mulVecC _ hdet).lintegral_comp hΨ,
    lintegral_smul_vecC' (Ψ := fun w => Φ (x, h, w)) (hΦ.comp (measurable_const.prodMk
      (measurable_const.prodMk measurable_id))) (neg_ne_zero.mpr (inv_ne_zero hq)), inv_neg, inv_inv, nnnorm_neg]

/-- **The parametric cone identity** at a complex place:
$$\int f\,d\mu_Q = |2c|_{\mathbb C}^{-(k+1)}|2c|_{\mathbb C}^{-k}\int_{\mathbb C}\frac{|q|^{2k}}{|2cq|^2}
\int_{S'_{-c}}\int_{SO(Q')}\int_{\mathbb C^k}f\big(\iota(s'(y))\,d(q)\,n(w)\,\mathrm{diag}(1,1,h)\big)\,d^2w\,
d\mu_{Q'}(h)\,d\sigma'_{-c}(y)\,d^2q.$$ -/
@[kb "weil1982" "§2.4 (Lemma 2.4.1 / Theorem 2.4.3 for the cone orbit, complex place) [unverified]"]
theorem lintegral_lerayMeasureC_cone_param (s' : SphSectionC (-c) Q') {f : ArchSOC (coneForm c Q') → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ g, f g ∂lerayMeasureC (coneForm c Q') (gramDetC_cone hc hQ') =
      (((‖2 * c‖₊ ^ (2 * (k + 1)))⁻¹ : ℝ≥0) : ℝ≥0∞) * (((‖2 * c‖₊ ^ (2 * k))⁻¹ : ℝ≥0) : ℝ≥0∞) *
        ∫⁻ q, dens2 (2 * c) q * ((‖q‖₊ ^ (2 * k) : ℝ≥0) : ℝ≥0∞) *
          ∫⁻ y, ∫⁻ h, ∫⁻ w, f (iotaC c (QmC c Q') (s'.toFun y) * dGt hc hQ' q * nG hc hQ' w * mG c Q' h)
            ∂volume ∂lerayMeasureC Q' hQ' ∂sigC (QmC c Q') (-c) := by
  rw [lintegral_coneC_P1 hc hQ' hf, mul_assoc]
  congr 1
  have hΦ : ∀ q : ℂ, Measurable fun p : SphC (QmC c Q') (-c) × ArchSOC Q' × (Fin k → ℂ) =>
      f (iotaC c (QmC c Q') (s'.toFun p.1) * dGt hc hQ' q * nG hc hQ' p.2.2 * mG c Q' p.2.1) := by
    intro q
    exact hf.comp (((((continuous_iotaC _ _).measurable.comp (s'.measurable.comp measurable_fst)).mul_const _).mul
      ((continuous_nG hc hQ').measurable.comp (measurable_snd.comp measurable_snd))).mul
      (continuous_mG.measurable.comp (measurable_fst.comp measurable_snd)))
  have hae : ∀ᵐ q : ℂ, q ≠ 0 := by
    rw [ae_iff]; simp only [ne_eq, not_not, ofPred_eq_eq_singleton, measure_singleton]
  rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with q hq
  have e1 : ∀ y : Fin k → ℂ, dens2 (2 * c) q * ∫⁻ h, f (iotaC c (QmC c Q') h * dGt hc hQ' q *
      nG hc hQ' (-(q⁻¹ • y))) ∂lerayMeasureC (QmC c Q') (gramDetC_Qm hc hQ') =
      dens2 (2 * c) q * ((((‖2 * c‖₊ ^ (2 * k))⁻¹ : ℝ≥0) : ℝ≥0∞) *
        ∫⁻ x, ∫⁻ h, f (iotaC c (QmC c Q') (s'.toFun x) * dGt hc hQ' q *
          nG hc hQ' (ArchSOC.mat _ h *ᵥ (-(q⁻¹ • y))) * mG c Q' h) ∂lerayMeasureC Q' hQ' ∂sigC (QmC c Q') (-c)) := by
    intro y; rw [lintegral_coneC_P2 hc hQ' s' hf]
  simp_rw [e1]
  rw [lintegral_const_mul' _ _ (by unfold dens2; exact ENNReal.coe_ne_top),
    lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_coneC_P3 hc hQ' hq (hΦ q)]
  ring

end QuadFormsKB.Tamagawa.Measure.ConeComplex
