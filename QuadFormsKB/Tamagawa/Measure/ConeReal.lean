import QuadFormsKB.Tamagawa.Measure.OrbitalReal
import QuadFormsKB.Tamagawa.Measure.ConeAlgebra
import QuadFormsKB.Tamagawa.Measure.Weil.OrbitFibration

/-!
# The archimedean cone at a real place

Let $Q = \langle c\rangle \perp \langle -c\rangle \perp Q'$ (`ConeAlgebra.coneForm c Q'`) be a nondegenerate real form in
$n = k + 1 + 1$ variables, any signature, $c \ne 0$; every isotropic real form has this shape ($V = H \perp V'$, $H$ a
hyperbolic plane). In the **hyperbolic split** coordinates $p = x_0 + x_1$, $q = x_0 - x_1$ we have
$Q = c\,pq + Q'(x')$, and $e = e_0 + e_1$ is isotropic.

This file proves the cone orbital identity at the real places. The route: **an explicit parabolic slice obtained from the
two sphere identities of `SphereLeray.lean`** (no new Leray analysis on $M_n(\mathbb R)$, no limit $c \to 0$):

1. (`lintegral_sig_graph`) **the hyperbolic-split chart of the sphere** $S_c$: in the graph coordinates
   $(q, x') \mapsto (p, q, x')$, $p = (c - Q'(x'))/(cq)$, the Leray measure is $\sigma_c = dq\,dx'/(2|c||q|)$ on
   $\{q \ne 0\}$ and $\{q = 0\}$ is $\sigma_c$-null. Proof: the Leray fibration (`lintegral_posSet_fibration`) against a
   direct computation of $dx$ in the coordinates $(u, q, x')$, $u = Q/c$ (affine in $p$ for fixed $q \ne 0$).
2. The graph point is $d(q^{-1})\,n(x')\,e_0$ (torus and Eichler transformation of the parabolic $P_e$), so
   $g = d(q^{-1})n(x')$ is a **section of $SO(Q) \to S_c$ on $\{q \ne 0\}$** (`coneSphSection`).
3. The sphere identity for $S_c$ with this section, then inversion ($SO(Q)$ is unimodular), then the sphere identity
   for $SO(\langle -c\rangle \perp Q')$ on $S'_{-c}$, then the commutation rules of the parabolic, give
   (`lintegral_lerayMeasure_cone_param`)
   $$\int f\,d\mu_Q = |2c|^{-(2k+2)}\int_{\mathbb R}|q|^{k-1}\int_{S'_{-c}}\int_{SO(Q')}\int_{\mathbb R^k}
     f\big(\iota(s'(y))\,d(q)\,n(w)\,\mathrm{diag}(1,1,h)\big)\,dw\,d\mu_{Q'}(h)\,d\sigma'_{-c}(y)\,dq.$$
-/

open MeasureTheory Measure Matrix Set Filter Topology
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.ConeReal

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.ArchVol QuadFormsKB.Tamagawa.ArchSOMeasure
open QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.SphereLeray
open QuadFormsKB.Tamagawa.Measure.OrbitalReal QuadFormsKB.Tamagawa.Measure.ConeAlgebra

variable {k : ℕ}

/-! ### Group elements of the parabolic in $SO(Q)(\mathbb R)$ -/

theorem hessian_det_ne_zero {n : ℕ} {Q : QuadForm ℝ n} (hQ : gramDetR Q ≠ 0) : Q.hessian.det ≠ 0 := by
  intro h; apply hQ; rw [gramDetR, h, zero_div]

/-- A matrix-valued map is continuous if all its actions on vectors are. -/
theorem continuous_of_mulVec {n : ℕ} {X : Type*} [TopologicalSpace X] {M : X → Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ v, Continuous fun t => M t *ᵥ v) : Continuous M := by
  refine continuous_matrix fun i j => ?_
  have := (continuous_apply i).comp (h (Pi.single j 1))
  convert this using 1
  funext t
  simp [mulVec, dotProduct, Pi.single_apply]

theorem continuous_v3 {X : Type*} [TopologicalSpace X] {a b : X → ℝ} {y : X → Fin k → ℝ} (ha : Continuous a)
    (hb : Continuous b) (hy : Continuous y) : Continuous fun t => v3 (a t) (b t) (y t) :=
  ha.finCons (hb.finCons hy)

theorem continuous_tl : Continuous (tl : (Fin (k + 1 + 1) → ℝ) → Fin k → ℝ) :=
  continuous_pi fun i => continuous_apply _

variable {c : ℝ} {Q' : QuadForm ℝ k}

/-- The middle form $Q_m = \langle -c\rangle \perp Q'$; the cone form is $\langle c\rangle \perp Q_m$. -/
abbrev Qm (c : ℝ) (Q' : QuadForm ℝ k) : QuadForm ℝ (k + 1) := splitForm (-c) Q'

theorem coneForm_eq (c : ℝ) (Q' : QuadForm ℝ k) : coneForm c Q' = splitForm c (Qm c Q') := rfl

theorem gramDetR_Qm (hc : c ≠ 0) (hQ' : gramDetR Q' ≠ 0) : gramDetR (Qm c Q') ≠ 0 := gramDetR_splitForm_ne_zero (neg_ne_zero.mpr hc) hQ'

theorem gramDetR_cone (hc : c ≠ 0) (hQ' : gramDetR Q' ≠ 0) : gramDetR (coneForm c Q') ≠ 0 := gramDetR_splitForm_ne_zero hc (gramDetR_Qm hc hQ')

theorem hessian_cone_det (hc : c ≠ 0) (hQ' : gramDetR Q' ≠ 0) : (coneForm c Q').hessian.det ≠ 0 := hessian_det_ne_zero (gramDetR_cone hc hQ')

theorem sq_or_neg_sq (a : ℝ) : ∃ b, b ^ 2 = a ∨ b ^ 2 = -a := by
  rcases le_total 0 a with h | h
  · exact ⟨Real.sqrt a, Or.inl (Real.sq_sqrt h)⟩
  · exact ⟨Real.sqrt (-a), Or.inr (Real.sq_sqrt (by linarith))⟩

/-- $d(a)$ as an element of $\mathrm{GL}_{k+2}(\mathbb R)$. -/
def dGL {a : ℝ} (ha : a ≠ 0) : GL (Fin (k + 1 + 1)) ℝ := ⟨dM a, dM a⁻¹, dM_mul_inv ha, dM_inv_mul ha⟩

theorem dGL_mem (hc : c ≠ 0) (hQ' : gramDetR Q' ≠ 0) {a : ℝ} (ha : a ≠ 0) : dGL (k := k) ha ∈ soReal (coneForm c Q') := by
  rw [mem_soReal_iff]
  exact ⟨isometry_dM c Q' ha, det_dM c Q' (hessian_cone_det hc hQ') ha (sq_or_neg_sq a)⟩

/-- **The torus element** $d(a) \in SO(Q)(\mathbb R)$ ($p \mapsto ap$, $q \mapsto a^{-1}q$; $d(a)e = ae$). -/
def dG (hc : c ≠ 0) (hQ' : gramDetR Q' ≠ 0) {a : ℝ} (ha : a ≠ 0) : ArchSO (coneForm c Q') := ArchSOInst.mk _ (dGL ha) (dGL_mem hc hQ' ha)

theorem mat_dG (hc : c ≠ 0) (hQ' : gramDetR Q' ≠ 0) {a : ℝ} (ha : a ≠ 0) : ArchSOInst.mat _ (dG hc hQ' ha) = dM a := rfl

/-- $n(w)$ as an element of $\mathrm{GL}_{k+2}(\mathbb R)$. -/
def nGL (hc : c ≠ 0) (w : Fin k → ℝ) : GL (Fin (k + 1 + 1)) ℝ := ⟨nM c Q' w, nM c Q' (-w), nM_mul_neg c Q' hc w, nM_neg_mul c Q' hc w⟩

theorem nGL_mem (hc : c ≠ 0) (hQ' : gramDetR Q' ≠ 0) (w : Fin k → ℝ) : nGL hc (Q' := Q') w ∈ soReal (coneForm c Q') := by
  rw [mem_soReal_iff]
  exact ⟨isometry_nM c Q' hc w, det_nM c Q' hc (hessian_cone_det hc hQ') w⟩

/-- **The Eichler transformation** $n(w) \in SO(Q)(\mathbb R)$ (unipotent radical of the stabilizer of $e$). -/
def nG (hc : c ≠ 0) (hQ' : gramDetR Q' ≠ 0) (w : Fin k → ℝ) : ArchSO (coneForm c Q') := ArchSOInst.mk _ (nGL hc w) (nGL_mem hc hQ' w)

variable (hc : c ≠ 0) (hQ' : gramDetR Q' ≠ 0)
include hc hQ'

theorem mat_nG (w : Fin k → ℝ) : ArchSOInst.mat _ (nG hc hQ' w) = nM c Q' w := rfl

omit hc hQ' in
/-- **The Levi factor** $SO(Q') \to SO(Q)$, $h \mapsto \mathrm{diag}(1, 1, h)$. -/
def mG (c : ℝ) (Q' : QuadForm ℝ k) : ArchSO Q' →* ArchSO (coneForm c Q') := (iota c (Qm c Q')).comp (iota (-c) Q')

omit hc hQ' in
theorem mat_mG (h : ArchSO Q') : ArchSOInst.mat _ (mG c Q' h) = mM (ArchSOInst.mat _ h) := rfl

omit hc hQ' in
theorem continuous_mG : Continuous (mG c Q') := (continuous_iota _ _).comp (continuous_iota _ _)

omit hc hQ' in
theorem mat_ext' {g h : ArchSO (coneForm c Q')} (e : ArchSOInst.mat _ g = ArchSOInst.mat _ h) : g = h := by
  apply Subtype.ext; apply Units.ext; exact e

theorem nG_add (w w' : Fin k → ℝ) : nG hc hQ' w * nG hc hQ' w' = nG hc hQ' (w + w') :=
  mat_ext' (by rw [ArchSOInst.mat_mul, mat_nG, mat_nG, mat_nG, nM_mul c Q' hc])

theorem nG_zero : nG hc hQ' (0 : Fin k → ℝ) = 1 :=
  mat_ext' (by rw [mat_nG, nM_zero, ArchSOInst.mat_one])

theorem nG_neg (w : Fin k → ℝ) : (nG hc hQ' w)⁻¹ = nG hc hQ' (-w) := by
  rw [inv_eq_iff_mul_eq_one, nG_add, add_neg_cancel, nG_zero]

theorem dG_mul {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    dG hc hQ' ha * dG hc hQ' hb = dG hc hQ' (mul_ne_zero ha hb) :=
  mat_ext' (by rw [ArchSOInst.mat_mul, mat_dG, mat_dG, mat_dG, dM_mul _ _ ha hb])

theorem dG_inv {a : ℝ} (ha : a ≠ 0) : (dG hc hQ' ha)⁻¹ = dG hc hQ' (inv_ne_zero ha) := by
  rw [inv_eq_iff_mul_eq_one, dG_mul]
  exact mat_ext' (by rw [mat_dG, mul_inv_cancel₀ ha, dM_one, ArchSOInst.mat_one])

theorem dG_mul_nG {a : ℝ} (ha : a ≠ 0) (w : Fin k → ℝ) :
    dG hc hQ' ha * nG hc hQ' w = nG hc hQ' (a • w) * dG hc hQ' ha :=
  mat_ext' (by rw [ArchSOInst.mat_mul, ArchSOInst.mat_mul, mat_dG, mat_nG, mat_nG, dM_mul_nM c Q' hc ha])

theorem mG_mul_dG (h : ArchSO Q') {a : ℝ} (ha : a ≠ 0) :
    mG c Q' h * dG hc hQ' ha = dG hc hQ' ha * mG c Q' h :=
  mat_ext' (by rw [ArchSOInst.mat_mul, ArchSOInst.mat_mul, mat_dG, mat_mG, mM_mul_dM])

omit hc hQ' in
theorem isometry_hessian (h : ArchSO Q') :
    (ArchSOInst.mat _ h)ᵀ * Q'.hessian * ArchSOInst.mat _ h = Q'.hessian :=
  ((mem_soReal_iff Q' _).mp (ArchSOInst.incl_mem Q' h)).1

theorem mG_mul_nG (h : ArchSO Q') (w : Fin k → ℝ) :
    mG c Q' h * nG hc hQ' w = nG hc hQ' (ArchSOInst.mat _ h *ᵥ w) * mG c Q' h :=
  mat_ext' (by rw [ArchSOInst.mat_mul, ArchSOInst.mat_mul, mat_nG, mat_nG, mat_mG,
    mM_mul_nM c Q' (isometry_hessian h)])

theorem continuous_nG : Continuous (nG hc hQ' : (Fin k → ℝ) → ArchSO (coneForm c Q')) := by
  have hv : ∀ v : Fin (k + 1 + 1) → ℝ, Continuous fun w : Fin k → ℝ => nM c Q' w *ᵥ v := by
    intro v
    have : (fun w : Fin k → ℝ => nM c Q' w *ᵥ v) = fun w => nM c Q' w *ᵥ v3 (v 0) (v 1) (tl v) := by
      rw [v3_eta]
    rw [this]
    simp only [nM_mulVec_v3]
    have hq : Continuous fun w : Fin k → ℝ => Q'.eval w := continuous_eval_real Q'
    have hd : Continuous fun w : Fin k → ℝ => (Q'.hessian *ᵥ w) ⬝ᵥ tl v :=
      (continuous_const.matrix_mulVec continuous_id).dotProduct continuous_const
    refine continuous_v3 ?_ ?_ ?_
    · exact continuous_const.sub ((hd.add (continuous_const.mul hq)).div_const _)
    · exact continuous_const.sub ((hd.add (continuous_const.mul hq)).div_const _)
    · exact continuous_const.add (continuous_const_smul _)
  have h1 : Continuous fun w : Fin k → ℝ => nM c Q' w := continuous_of_mulVec hv
  have h2 : Continuous fun w : Fin k → ℝ => nM c Q' (-w) := h1.comp continuous_neg
  exact Continuous.subtype_mk (Units.continuous_iff.mpr ⟨h1, h2⟩) _


/-! ### Lebesgue measure in the coordinates $(x_0, x_1, x')$ -/

omit hc hQ' in
theorem measurable_v3' : Measurable fun p : ℝ × ℝ × (Fin k → ℝ) => v3 p.1 p.2.1 p.2.2 :=
  (continuous_v3 continuous_fst (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd)).measurable

omit hc hQ' in
theorem Measurable.v3 {X : Type*} [MeasurableSpace X] {a b : X → ℝ} {y : X → Fin k → ℝ} (ha : Measurable a)
    (hb : Measurable b) (hy : Measurable y) : Measurable fun t => ConeAlgebra.v3 (a t) (b t) (y t) :=
  measurable_v3'.comp (ha.prodMk (hb.prodMk hy))

omit hc hQ' in
theorem lintegral_cons_split {N : ℕ} {G : (Fin (N + 1) → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G x = ∫⁻ a, ∫⁻ y : Fin N → ℝ, G (Fin.cons a y) := by
  let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) 0
  have hE : MeasurePreserving E volume volume := volume_preserving_piFinSuccAbove _ 0
  rw [← hE.symm.lintegral_comp_emb E.symm.measurableEmbedding, Measure.volume_eq_prod,
    lintegral_prod (f := fun z => G (E.symm z)) (hG.comp E.symm.measurable).aemeasurable]
  refine lintegral_congr fun a => lintegral_congr fun y => ?_
  congr 1
  simp [E, MeasurableEquiv.piFinSuccAbove]
  rfl

omit hc hQ' in
/-- $dx = dx_0\,dx_1\,dx'$ in the coordinates $x = (x_0, x_1, x')$. -/
theorem lintegral_v3_split {G : (Fin (k + 1 + 1) → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G x = ∫⁻ a, ∫⁻ b, ∫⁻ y, G (v3 a b y) := by
  rw [lintegral_cons_split hG]
  refine lintegral_congr fun a => ?_
  exact lintegral_cons_split (G := fun y => G (Fin.cons a y))
    (hG.comp (continuous_const.finCons continuous_id).measurable)

omit hc hQ' in
/-- **Affine change of variables on the line**: $\int\Psi(\alpha b + \beta)\,db = |\alpha|^{-1}\int\Psi$. -/
theorem lintegral_comp_affine {Ψ : ℝ → ℝ≥0∞} (hΨ : Measurable Ψ) {α : ℝ} (hα : α ≠ 0) (β : ℝ) :
    ∫⁻ b, Ψ (α * b + β) = ENNReal.ofReal (|α|⁻¹) * ∫⁻ u, Ψ u := by
  rw [show (∫⁻ b, Ψ (α * b + β)) = ∫⁻ u, Ψ (u + β) ∂(volume.map (α * ·)) from
      (lintegral_map (hΨ.comp (measurable_add_const β)) (measurable_const_mul α)).symm,
    Real.map_volume_mul_left hα, lintegral_smul_measure, lintegral_add_right_eq_self (fun u => Ψ u) β, abs_inv,
    smul_eq_mul]

/-! ### The hyperbolic-split chart of the sphere $S_c$ -/

omit hc hQ' in
/-- $x_1$ of the graph point: $b = (1 - q^2 - Q'(y)/c)/(2q)$. -/
def graphB (c : ℝ) (Q' : QuadForm ℝ k) (q : ℝ) (y : Fin k → ℝ) : ℝ := (1 - q ^ 2 - Q'.eval y / c) / (2 * q)

omit hc hQ' in
/-- **The graph point** of $S_c$ over $(q, y)$: $x = (b + q, b, y)$, i.e. $x_0 - x_1 = q$, $x' = y$, and
$p = x_0 + x_1 = (c - Q'(y))/(cq)$. -/
@[irreducible] def graphV (c : ℝ) (Q' : QuadForm ℝ k) (q : ℝ) (y : Fin k → ℝ) : Fin (k + 1 + 1) → ℝ :=
  v3 (graphB c Q' q y + q) (graphB c Q' q y) y

omit hQ' in
theorem eval_graphV {q : ℝ} (hq : q ≠ 0) (y : Fin k → ℝ) : (coneForm c Q').eval (graphV c Q' q y) = c := by
  rw [graphV, eval_coneForm_v3, graphB]
  field_simp
  ring

omit hc hQ' in
theorem measurable_graphV : Measurable fun p : ℝ × (Fin k → ℝ) => graphV c Q' p.1 p.2 := by
  have hb : Measurable fun p : ℝ × (Fin k → ℝ) => graphB c Q' p.1 p.2 := by
    unfold graphB
    exact ((measurable_const.sub (measurable_fst.pow_const 2)).sub
      (((continuous_eval_real Q').measurable.comp measurable_snd).div_const c)).div
      (measurable_const.mul measurable_fst)
  unfold graphV
  exact Measurable.v3 (hb.add measurable_fst) hb measurable_snd


omit hc hQ' in
/-- The radial test function $\varphi = 1_{(0, 1]}$. -/
def phiR : ℝ → ℝ≥0∞ := (Ioc (0 : ℝ) 1).indicator 1

omit hc hQ' in
theorem measurable_phiR : Measurable phiR := measurable_one.indicator measurableSet_Ioc

omit hc hQ' in
theorem phiR_of_nonpos {u : ℝ} (hu : u ≤ 0) : phiR u = 0 :=
  indicator_of_notMem (fun h => by have := h.1; linarith) _

omit hc hQ' in
/-- The test function $f(x) = \varphi(Q(x)/c)\,F\big(x/\sqrt{Q(x)/c}\big)$ (radial part times angular part). -/
@[irreducible] def testF (c : ℝ) (Q' : QuadForm ℝ k) (F : (Fin (k + 1 + 1) → ℝ) → ℝ≥0∞) (x : Fin (k + 1 + 1) → ℝ) : ℝ≥0∞ :=
  phiR ((coneForm c Q').eval x / c) * F ((Real.sqrt ((coneForm c Q').eval x / c))⁻¹ • x)

omit hc hQ' in
theorem measurable_testF {F : (Fin (k + 1 + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) : Measurable (testF c Q' F) := by
  have hu : Measurable fun x : Fin (k + 1 + 1) → ℝ => (coneForm c Q').eval x / c :=
    (continuous_eval_real _).measurable.div_const c
  unfold testF
  exact (measurable_phiR.comp hu).mul (hF.comp ((Real.continuous_sqrt.measurable.comp hu).inv.smul measurable_id))

omit hQ' in
/-- **The fibration side**: by the Leray fibration,
$\int f\,dx = |c|\int_0^\infty u^{k/2}\varphi(u)\,du\cdot\int_{S_c}F\,d\sigma_c$. -/
theorem lintegral_testF_fibration {F : (Fin (k + 1 + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, testF c Q' F x =
      ENNReal.ofReal |c| * (∫⁻ u, phiR u * ENNReal.ofReal (u ^ ((k : ℝ) / 2))) *
        ∫⁻ x, F x ∂sig (coneForm c Q') c := by
  have hn : 1 ≤ k + 1 + 1 := by omega
  have hvan : ∫⁻ x, testF c Q' F x = ∫⁻ x in posSet (coneForm c Q') c, testF c Q' F x := by
    rw [← lintegral_indicator (isOpen_posSet _ _).measurableSet]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ posSet (coneForm c Q') c
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, testF, phiR_of_nonpos, zero_mul]
      have : ¬ 0 < c * (coneForm c Q').eval x := hx
      rw [div_nonpos_iff]
      rcases lt_or_gt_of_ne hc with h | h
      · left; constructor <;> nlinarith
      · right; constructor <;> nlinarith
  rw [hvan, lintegral_posSet_fibration hc hn (measurable_testF hF)]
  have hpt : ∀ u ∈ Ioi (0 : ℝ), ENNReal.ofReal (|c| * u ^ (((k + 1 + 1 : ℕ) : ℝ) / 2 - 1)) *
      ∫⁻ x, testF c Q' F (Real.sqrt u • (x : Fin (k + 1 + 1) → ℝ)) ∂sig (coneForm c Q') c =
      ENNReal.ofReal |c| * (phiR u * ENNReal.ofReal (u ^ ((k : ℝ) / 2))) * ∫⁻ x, F x ∂sig (coneForm c Q') c := by
    intro u hu
    have hu0 : 0 < u := hu
    have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
    have hpt' : ∀ x : Sph (coneForm c Q') c, testF c Q' F (Real.sqrt u • (x : Fin (k + 1 + 1) → ℝ)) = phiR u * F x := by
      intro x
      have hx : (coneForm c Q').eval (x : Fin (k + 1 + 1) → ℝ) = c := x.2
      have h1 : (coneForm c Q').eval (Real.sqrt u • (x : Fin (k + 1 + 1) → ℝ)) / c = u := by
        rw [eval_smul_real, hx, Real.sq_sqrt hu0.le, mul_div_assoc, div_self hc, mul_one]
      rw [testF, h1, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
    simp_rw [hpt']
    rw [show (∫⁻ x : Sph (coneForm c Q') c, phiR u * F x ∂sig (coneForm c Q') c) =
        phiR u * ∫⁻ x : Sph (coneForm c Q') c, F x ∂sig (coneForm c Q') c from
      lintegral_const_mul _ (hF.comp measurable_subtype_coe)]
    have he : ((k + 1 + 1 : ℕ) : ℝ) / 2 - 1 = (k : ℝ) / 2 := by push_cast; ring
    rw [he, ENNReal.ofReal_mul (abs_nonneg c)]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_mul_const _ ?_, lintegral_const_mul _ ?_]
  · congr 2
    rw [← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun u => ?_
    by_cases hu : u ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hu]
    · rw [indicator_of_notMem hu, phiR_of_nonpos (not_lt.mp hu), zero_mul]
  · exact measurable_phiR.mul (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))
  · exact measurable_const.mul (measurable_phiR.mul (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)))


omit hQ' in
/-- The pointwise substitution behind the coordinate computation: for $q \ne 0$, with $u = 2qb + q^2 + Q'(y)/c$,
$f(q + b, b, y) = \varphi(u)\,F\big(\mathrm{graph}(q/\sqrt u, y/\sqrt u)\big)$. -/
theorem testF_v3_eq {F : (Fin (k + 1 + 1) → ℝ) → ℝ≥0∞} {q : ℝ} (hq : q ≠ 0) (b : ℝ) (y : Fin k → ℝ) :
    testF c Q' F (v3 (q + b) b y) =
      phiR (2 * q * b + (q ^ 2 + Q'.eval y / c)) *
        F (graphV c Q' (q / Real.sqrt (2 * q * b + (q ^ 2 + Q'.eval y / c)))
          ((Real.sqrt (2 * q * b + (q ^ 2 + Q'.eval y / c)))⁻¹ • y)) := by
  set u := 2 * q * b + (q ^ 2 + Q'.eval y / c) with hu_def
  have hu : (coneForm c Q').eval (v3 (q + b) b y) / c = u := by
    rw [eval_coneForm_v3, hu_def]; field_simp; ring
  rw [testF, hu]
  rcases le_or_gt u 0 with h0 | h0
  · rw [phiR_of_nonpos h0, zero_mul, zero_mul]
  · congr 2
    set s := Real.sqrt u
    have hs : 0 < s := Real.sqrt_pos.mpr h0
    have hs2 : s ^ 2 = u := Real.sq_sqrt h0.le
    rw [v3_smul, graphV]
    have hQc : Q'.eval y / c = s ^ 2 - 2 * q * b - q ^ 2 := by rw [hs2, hu_def]; ring
    have hB : graphB c Q' (q / s) (s⁻¹ • y) = s⁻¹ * b := by
      rw [graphB, eval_smul_real, show s⁻¹ ^ 2 * Q'.eval y / c = s⁻¹ ^ 2 * (Q'.eval y / c) by ring, hQc]
      field_simp
      ring
    refine v3_congr ?_ hB.symm rfl
    rw [hB]; field_simp; ring

omit hc hQ' in
theorem measurable_T3 {F : (Fin (k + 1 + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    Measurable fun p : (ℝ × ℝ) × (Fin k → ℝ) => testF c Q' F (v3 p.1.1 p.1.2 p.2) :=
  (measurable_testF hF).comp (Measurable.v3 (measurable_fst.comp measurable_fst)
    (measurable_snd.comp measurable_fst) measurable_snd)

omit hQ' in
/-- Step A: $\int f\,dx = \int_q\int_y\int_b f(q + b, b, y)$. -/
theorem lintegral_testF_reorder {F : (Fin (k + 1 + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, testF c Q' F x = ∫⁻ q, ∫⁻ y, ∫⁻ b, testF c Q' F (v3 (q + b) b y) := by
  have h3 := measurable_T3 (c := c) (Q' := Q') hF
  rw [lintegral_v3_split (measurable_testF hF)]
  have hA : AEMeasurable (Function.uncurry fun a b : ℝ => ∫⁻ y, testF c Q' F (v3 a b y)) (volume.prod volume) :=
    h3.lintegral_prod_right'.aemeasurable
  rw [lintegral_lintegral_swap hA]
  have e1 : ∀ b : ℝ, ∫⁻ a, ∫⁻ y, testF c Q' F (v3 a b y) = ∫⁻ q, ∫⁻ y, testF c Q' F (v3 (q + b) b y) :=
    fun b => (lintegral_add_right_eq_self (fun a => ∫⁻ y, testF c Q' F (v3 a b y)) b).symm
  rw [lintegral_congr e1]
  have h3' : Measurable fun p : (ℝ × ℝ) × (Fin k → ℝ) => testF c Q' F (v3 (p.1.2 + p.1.1) p.1.1 p.2) :=
    (measurable_testF hF).comp (Measurable.v3 ((measurable_snd.comp measurable_fst).add
      (measurable_fst.comp measurable_fst)) (measurable_fst.comp measurable_fst) measurable_snd)
  have hA' : AEMeasurable (Function.uncurry fun b q : ℝ => ∫⁻ y, testF c Q' F (v3 (q + b) b y))
      (volume.prod volume) := h3'.lintegral_prod_right'.aemeasurable
  rw [lintegral_lintegral_swap hA']
  refine lintegral_congr fun q => ?_
  have h2 : Measurable fun p : ℝ × (Fin k → ℝ) => testF c Q' F (v3 (q + p.1) p.1 p.2) :=
    (measurable_testF hF).comp (Measurable.v3 (measurable_const.add measurable_fst) measurable_fst measurable_snd)
  exact lintegral_lintegral_swap h2.aemeasurable

omit hc hQ' in
theorem measurable_W {F : (Fin (k + 1 + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    Measurable fun p : ℝ × (Fin k → ℝ) × ℝ =>
      F (graphV c Q' (p.1 / Real.sqrt p.2.2) ((Real.sqrt p.2.2)⁻¹ • p.2.1)) := by
  have hs : Measurable fun p : ℝ × (Fin k → ℝ) × ℝ => Real.sqrt p.2.2 :=
    Real.continuous_sqrt.measurable.comp (measurable_snd.comp measurable_snd)
  have hg : Measurable fun p : ℝ × (Fin k → ℝ) × ℝ =>
      ((p.1 / Real.sqrt p.2.2, (Real.sqrt p.2.2)⁻¹ • p.2.1) : ℝ × (Fin k → ℝ)) :=
    (measurable_fst.div hs).prodMk (hs.inv.smul (measurable_fst.comp measurable_snd))
  have := hF.comp ((measurable_graphV (c := c) (Q' := Q')).comp hg)
  exact this

omit hQ' in
/-- Steps B–D: for every $u$, after the affine substitution in $b$ the integral is
$\int_u\varphi(u)\int_q\int_y |2q|^{-1}F(\mathrm{graph}(q/\sqrt u, y/\sqrt u))$. -/
theorem lintegral_testF_u {F : (Fin (k + 1 + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, testF c Q' F x = ∫⁻ u, phiR u * ∫⁻ q, ∫⁻ y, ENNReal.ofReal (|2 * q|⁻¹) *
      F (graphV c Q' (q / Real.sqrt u) ((Real.sqrt u)⁻¹ • y)) := by
  have hW := measurable_W (c := c) (Q' := Q') hF
  rw [lintegral_testF_reorder hc hF]
  have hae : ∀ᵐ q : ℝ, q ≠ 0 := by
    rw [ae_iff]; simp only [ne_eq, not_not, ofPred_eq_eq_singleton, measure_singleton]
  have hB : ∀ᵐ q : ℝ, (∫⁻ y, ∫⁻ b, testF c Q' F (v3 (q + b) b y)) =
      ∫⁻ y, ∫⁻ u, ENNReal.ofReal (|2 * q|⁻¹) *
        (phiR u * F (graphV c Q' (q / Real.sqrt u) ((Real.sqrt u)⁻¹ • y))) := by
    filter_upwards [hae] with q hq
    refine lintegral_congr fun y => ?_
    simp_rw [testF_v3_eq hc hq]
    have hΨ : Measurable fun u : ℝ => phiR u * F (graphV c Q' (q / Real.sqrt u) ((Real.sqrt u)⁻¹ • y)) :=
      measurable_phiR.mul (hW.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
    rw [lintegral_comp_affine (Ψ := fun u => phiR u * F (graphV c Q' (q / Real.sqrt u) ((Real.sqrt u)⁻¹ • y)))
      hΨ (mul_ne_zero two_ne_zero hq), lintegral_const_mul _ hΨ]
  rw [lintegral_congr_ae hB]
  have hm3 : Measurable fun p : ℝ × (Fin k → ℝ) × ℝ =>
      ENNReal.ofReal (|2 * p.1|⁻¹) * (phiR p.2.2 * F (graphV c Q' (p.1 / Real.sqrt p.2.2)
        ((Real.sqrt p.2.2)⁻¹ • p.2.1))) :=
    (ENNReal.measurable_ofReal.comp ((measurable_const.mul measurable_fst).abs.inv)).mul
      ((measurable_phiR.comp (measurable_snd.comp measurable_snd)).mul hW)
  have e2 : ∀ q : ℝ, (∫⁻ y, ∫⁻ u, ENNReal.ofReal (|2 * q|⁻¹) *
      (phiR u * F (graphV c Q' (q / Real.sqrt u) ((Real.sqrt u)⁻¹ • y))))
      = ∫⁻ u, ∫⁻ y, ENNReal.ofReal (|2 * q|⁻¹) *
      (phiR u * F (graphV c Q' (q / Real.sqrt u) ((Real.sqrt u)⁻¹ • y))) := by
    intro q
    exact lintegral_lintegral_swap ((hm3.comp (measurable_const.prodMk measurable_id)).aemeasurable)
  simp_rw [e2]
  have hm3' : Measurable fun p : ℝ × ℝ => ∫⁻ y, ENNReal.ofReal (|2 * p.1|⁻¹) *
      (phiR p.2 * F (graphV c Q' (p.1 / Real.sqrt p.2) ((Real.sqrt p.2)⁻¹ • y))) := by
    have : Measurable fun p : (ℝ × ℝ) × (Fin k → ℝ) => ENNReal.ofReal (|2 * p.1.1|⁻¹) *
        (phiR p.1.2 * F (graphV c Q' (p.1.1 / Real.sqrt p.1.2) ((Real.sqrt p.1.2)⁻¹ • p.2))) :=
      hm3.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.prodMk
        (measurable_snd.comp measurable_fst)))
    exact this.lintegral_prod_right'
  rw [lintegral_lintegral_swap hm3'.aemeasurable]
  refine lintegral_congr fun u => ?_
  rw [← lintegral_const_mul _ ?_]
  · refine lintegral_congr fun q => ?_
    rw [← lintegral_const_mul _ ?_]
    · refine lintegral_congr fun y => ?_
      ring
    · exact measurable_const.mul (hW.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
  · have : Measurable fun p : ℝ × (Fin k → ℝ) => ENNReal.ofReal (|2 * p.1|⁻¹) *
        F (graphV c Q' (p.1 / Real.sqrt u) ((Real.sqrt u)⁻¹ • p.2)) :=
      (ENNReal.measurable_ofReal.comp ((measurable_const.mul measurable_fst).abs.inv)).mul
        (hW.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const)))
    exact this.lintegral_prod_right'



omit hc hQ' in
theorem sqrt_pow_eq_rpow {u : ℝ} (hu : 0 ≤ u) : Real.sqrt u ^ k = u ^ ((k : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hu]; ring_nf

omit hc hQ' in
/-- Step E: scaling $q = \sqrt u\,\tilde q$, $y = \sqrt u\,\tilde y$ gives the factor $u^{k/2}$. -/
theorem lintegral_graph_scale {F : (Fin (k + 1 + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) {u : ℝ} (hu : 0 < u) :
    ∫⁻ q, ∫⁻ y, ENNReal.ofReal (|2 * q|⁻¹) * F (graphV c Q' (q / Real.sqrt u) ((Real.sqrt u)⁻¹ • y)) =
      ENNReal.ofReal (u ^ ((k : ℝ) / 2)) * ∫⁻ q, ∫⁻ y, ENNReal.ofReal (|2 * q|⁻¹) * F (graphV c Q' q y) := by
  set s := Real.sqrt u with hs_def
  have hs : 0 < s := Real.sqrt_pos.mpr hu
  have hGm : Measurable fun p : ℝ × (Fin k → ℝ) => F (graphV c Q' p.1 p.2) :=
    hF.comp (measurable_graphV (c := c) (Q' := Q'))
  set K : ℝ → ℝ≥0∞ := fun q => ∫⁻ y, F (graphV c Q' q y) with hK
  have hKm : Measurable K := hGm.lintegral_prod_right'
  have h1 : ∀ q : ℝ, ∫⁻ y, ENNReal.ofReal (|2 * q|⁻¹) * F (graphV c Q' (q / s) (s⁻¹ • y)) =
      ENNReal.ofReal (|2 * q|⁻¹) * ENNReal.ofReal (s ^ k) * K (q / s) := by
    intro q
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_assoc]
    congr 1
    have := lintegral_comp_smul_pi (G := fun y => F (graphV c Q' (q / s) y)) (inv_pos.mpr hs)
      (hGm.comp (measurable_const.prodMk measurable_id))
    beta_reduce at this
    rw [this, inv_pow, inv_inv]
  simp_rw [h1]
  have hΨ : Measurable fun q : ℝ => ENNReal.ofReal (|2 * q|⁻¹) * ENNReal.ofReal (s ^ k) * K (q / s) :=
    ((ENNReal.measurable_ofReal.comp ((measurable_const.mul measurable_id).abs.inv)).mul measurable_const).mul
      (hKm.comp (measurable_id.div_const s))
  have h2 := lintegral_comp_affine hΨ hs.ne' 0
  simp only [add_zero] at h2
  have h3 : ∫⁻ q, ENNReal.ofReal (|2 * q|⁻¹) * ENNReal.ofReal (s ^ k) * K (q / s) =
      ENNReal.ofReal s * ∫⁻ q, ENNReal.ofReal (|2 * (s * q)|⁻¹) * ENNReal.ofReal (s ^ k) * K (s * q / s) := by
    rw [h2, ← mul_assoc, ← ENNReal.ofReal_mul hs.le, abs_of_pos hs, mul_inv_cancel₀ hs.ne', ENNReal.ofReal_one,
      one_mul]
  rw [h3]
  have h4 : ∀ q : ℝ, ENNReal.ofReal (|2 * (s * q)|⁻¹) * ENNReal.ofReal (s ^ k) * K (s * q / s) =
      ENNReal.ofReal (s⁻¹) * ENNReal.ofReal (s ^ k) * (ENNReal.ofReal (|2 * q|⁻¹) * K q) := by
    intro q
    rw [mul_div_cancel_left₀ _ hs.ne', show 2 * (s * q) = s * (2 * q) by ring, abs_mul, abs_of_pos hs,
      mul_inv, ENNReal.ofReal_mul (inv_nonneg.mpr hs.le)]
    ring
  simp_rw [h4]
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
    ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hs.le, mul_inv_cancel₀ hs.ne', ENNReal.ofReal_one,
    one_mul, hs_def, sqrt_pow_eq_rpow hu.le]
  congr 1
  refine lintegral_congr fun q => ?_
  rw [hK, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The radial integral $I = \int_0^1 u^{k/2}\,du$ (only $0 < I < \infty$ is used). -/
def radI (k : ℕ) : ℝ≥0∞ := ∫⁻ u, phiR u * ENNReal.ofReal (u ^ ((k : ℝ) / 2))

omit hc hQ' in
theorem measurable_radI_integrand : Measurable fun u : ℝ => phiR u * ENNReal.ofReal (u ^ ((k : ℝ) / 2)) :=
  measurable_phiR.mul (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))

omit hc hQ' in
theorem radI_ne_top : radI k ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ u, phiR u) ?_ (lintegral_mono fun u => ?_)
  · rw [phiR, lintegral_indicator measurableSet_Ioc]
    simp
  · by_cases hu : u ∈ Ioc (0 : ℝ) 1
    · rw [phiR, indicator_of_mem hu, Pi.one_apply, one_mul]
      exact ENNReal.ofReal_le_one.mpr (Real.rpow_le_one hu.1.le hu.2 (by positivity))
    · rw [phiR, indicator_of_notMem hu, zero_mul]

omit hc hQ' in
theorem radI_ne_zero : radI k ≠ 0 := by
  intro h
  rw [radI, lintegral_eq_zero_iff measurable_radI_integrand] at h
  have hsub : Ioc (0 : ℝ) 1 ⊆ {u | phiR u * ENNReal.ofReal (u ^ ((k : ℝ) / 2)) ≠ 0} := by
    intro u hu
    simp only [mem_ofPred_eq, phiR, indicator_of_mem hu, Pi.one_apply, one_mul, ne_eq, ENNReal.ofReal_eq_zero,
      not_le]
    exact Real.rpow_pos_of_pos hu.1 _
  have h0 : volume {u : ℝ | phiR u * ENNReal.ofReal (u ^ ((k : ℝ) / 2)) ≠ 0} = 0 := by
    rw [Filter.EventuallyEq, ae_iff] at h
    simpa using h
  have := measure_mono_null hsub h0
  simp at this

omit hQ' in
/-- **The coordinate side**: $\int f\,dx = I\cdot\int_q\int_y |2q|^{-1}F(\mathrm{graph}(q, y))$. -/
theorem lintegral_testF_coords {F : (Fin (k + 1 + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, testF c Q' F x = radI k * ∫⁻ q, ∫⁻ y, ENNReal.ofReal (|2 * q|⁻¹) * F (graphV c Q' q y) := by
  rw [lintegral_testF_u hc hF, radI, ← lintegral_mul_const _ measurable_radI_integrand]
  refine lintegral_congr fun u => ?_
  rcases le_or_gt u 0 with hu | hu
  · rw [phiR_of_nonpos hu, zero_mul, zero_mul, zero_mul]
  · rw [lintegral_graph_scale hF hu, mul_assoc]

omit hQ' in
/-- **The hyperbolic-split chart of the sphere** (any signature, $c \ne 0$): in the graph coordinates
$(q, y) \mapsto x = (b + q, b, y)$ of $S_c$ ($q = x_0 - x_1$, $y = x'$), the Leray measure is
$$\int_{S_c}F\,d\sigma_c = \int_{\mathbb R}\int_{\mathbb R^k}\frac{F(\mathrm{graph}(q, y))}{2|c|\,|q|}\,dy\,dq,$$
i.e. $\sigma_c = dq\,dx'/(2|c||q|) = dx/dQ$ (as $dx_0\,dx_1 = \tfrac12 dp\,dq$ and $\partial Q/\partial p = cq$), and
$\{x_0 = x_1\}$ is $\sigma_c$-null. -/
@[kb "weil1982" "§2.2 (the Leray form dx/dQ in a chart) [unverified]"]
theorem lintegral_sig_graph {F : (Fin (k + 1 + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂sig (coneForm c Q') c =
      ∫⁻ q, ∫⁻ y, ENNReal.ofReal (1 / (2 * |c| * |q|)) * F (graphV c Q' q y) := by
  have h1 := lintegral_testF_fibration hc hF (Q' := Q')
  rw [lintegral_testF_coords hc hF, mul_comm (ENNReal.ofReal |c|), mul_assoc] at h1
  have h2 := (ENNReal.mul_right_inj radI_ne_zero radI_ne_top).mp h1
  have hc0 : 0 < |c| := abs_pos.mpr hc
  have e : ∫⁻ x, F x ∂sig (coneForm c Q') c = ENNReal.ofReal (|c|⁻¹) * (ENNReal.ofReal |c| *
      ∫⁻ x, F x ∂sig (coneForm c Q') c) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hc0.le), inv_mul_cancel₀ hc0.ne', ENNReal.ofReal_one,
      one_mul]
  rw [e, ← h2, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun q => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun y => ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hc0.le)]
  congr 2
  rw [abs_mul, abs_two]; field_simp


/-! ### A section of $SO(Q) \to S_c$ through the parabolic -/

omit hQ' in
/-- **The graph point is $d(q^{-1})\,n(y)\,e_0$.** -/
theorem dM_nM_e₀ {q : ℝ} (hq : q ≠ 0) (y : Fin k → ℝ) :
    dM q⁻¹ *ᵥ (nM c Q' y *ᵥ (e₀ : Fin (k + 1 + 1) → ℝ)) = graphV c Q' q y := by
  rw [nM_mulVec_e₀ c Q' hc, dM_mulVec_v3, graphV, graphB, inv_inv]
  refine v3_congr ?_ ?_ rfl <;> field_simp <;> ring

omit hQ' in
/-- On $S_c \cap \{x_0 \ne x_1\}$ the graph map recovers $x$. -/
theorem graphV_of_mem {x : Fin (k + 1 + 1) → ℝ} (hx : (coneForm c Q').eval x = c) (hq : x 0 - x 1 ≠ 0) :
    graphV c Q' (x 0 - x 1) (tl x) = x := by
  conv_rhs => rw [← v3_eta x]
  rw [eval_coneForm] at hx
  have hb : graphB c Q' (x 0 - x 1) (tl x) = x 1 := by
    rw [graphB, div_eq_iff (mul_ne_zero two_ne_zero hq)]
    have : Q'.eval (tl x) / c = 1 - (x 0 ^ 2 - x 1 ^ 2) := by
      rw [div_eq_iff hc]; linear_combination hx
    rw [this]; ring
  rw [graphV, hb]
  refine v3_congr (by ring) rfl rfl

theorem continuous_dG' : Continuous fun a : {a : ℝ // a ≠ 0} => dG hc hQ' a.2 := by
  have hinv : Continuous fun a : {a : ℝ // a ≠ 0} => (a : ℝ)⁻¹ := continuous_subtype_val.inv₀ fun a => a.2
  have hv : ∀ (f : {a : ℝ // a ≠ 0} → ℝ), Continuous f → Continuous (fun a => (f a)⁻¹) →
      Continuous fun a : {a : ℝ // a ≠ 0} => dM (k := k) (f a) := by
    intro f hf hf'
    refine continuous_of_mulVec fun v => ?_
    have : (fun a : {a : ℝ // a ≠ 0} => dM (k := k) (f a) *ᵥ v) =
        fun a => dM (k := k) (f a) *ᵥ v3 (v 0) (v 1) (tl v) := by rw [v3_eta]
    rw [this]
    simp only [dM_mulVec_v3]
    refine continuous_v3 ?_ ?_ continuous_const
    · exact (continuous_const.add (((hf.sub continuous_const).div_const _).mul continuous_const)).add
        (((hf'.sub continuous_const).div_const _).mul continuous_const)
    · exact (continuous_const.add (((hf.sub continuous_const).div_const _).mul continuous_const)).sub
        (((hf'.sub continuous_const).div_const _).mul continuous_const)
  have h1 := hv (fun a => (a : ℝ)) continuous_subtype_val hinv
  have h2 := hv (fun a => (a : ℝ)⁻¹) hinv (by simpa using continuous_subtype_val)
  exact Continuous.subtype_mk (Units.continuous_iff.mpr ⟨h1, h2⟩) _

/-- **The parabolic section** of $SO(Q)(\mathbb R) \to S_c$: $s(x) = d((x_0 - x_1)^{-1})\,n(x')$ on $\{x_0 \ne x_1\}$
(the graph chart), and the reflection section `secFun` on the $\sigma_c$-null set $\{x_0 = x_1\}$. -/
def secC (x : Sph (coneForm c Q') c) : ArchSO (coneForm c Q') :=
  if h : (x : Fin (k + 1 + 1) → ℝ) 0 - (x : Fin (k + 1 + 1) → ℝ) 1 ≠ 0 then
    dG hc hQ' (inv_ne_zero h) * nG hc hQ' (tl (x : Fin (k + 1 + 1) → ℝ))
  else secFun hc (by omega : 1 ≤ k + 1) (gramDetR_Qm hc hQ') ⟨(x : Fin (k + 1 + 1) → ℝ), x.2⟩

theorem secC_spec (x : Sph (coneForm c Q') c) :
    ArchSOInst.mat _ (secC hc hQ' x) *ᵥ (e₀ : Fin (k + 1 + 1) → ℝ) = (x : Fin (k + 1 + 1) → ℝ) := by
  unfold secC
  by_cases h : (x : Fin (k + 1 + 1) → ℝ) 0 - (x : Fin (k + 1 + 1) → ℝ) 1 ≠ 0
  · rw [dif_pos h, ArchSOInst.mat_mul, mat_dG, mat_nG, ← mulVec_mulVec, dM_nM_e₀ hc (q := _) h,
      graphV_of_mem hc x.2 h]
  · rw [dif_neg h]
    exact secFun_spec hc _ _ ⟨(x : Fin (k + 1 + 1) → ℝ), x.2⟩

theorem measurable_secC : Measurable (secC hc hQ') := by
  have hU : MeasurableSet {x : Sph (coneForm c Q') c | (x : Fin (k + 1 + 1) → ℝ) 0 - (x : Fin (k + 1 + 1) → ℝ) 1 ≠ 0} :=
    (isOpen_ne_fun ((continuous_apply 0).comp continuous_subtype_val |>.sub
      ((continuous_apply 1).comp continuous_subtype_val)) continuous_const).measurableSet
  set U : Set (Sph (coneForm c Q') c) := {x | (x : Fin (k + 1 + 1) → ℝ) 0 - (x : Fin (k + 1 + 1) → ℝ) 1 ≠ 0}
  refine measurable_of_restrict_of_restrict_compl hU ?_ ?_
  swap
  · have e : Uᶜ.domRestrict (secC hc hQ') = fun y : ↥Uᶜ => secFun hc (by omega : 1 ≤ k + 1) (gramDetR_Qm hc hQ')
        ⟨((y : Sph (coneForm c Q') c) : Fin (k + 1 + 1) → ℝ), (y : Sph (coneForm c Q') c).2⟩ := by
      funext y; show secC hc hQ' y.1 = _; unfold secC
      rw [dif_neg (show ¬ (((y : Sph (coneForm c Q') c) : Fin (k + 1 + 1) → ℝ) 0 -
        ((y : Sph (coneForm c Q') c) : Fin (k + 1 + 1) → ℝ) 1 ≠ 0) from y.2)]
    rw [e]
    have hm : Measurable fun y : ↥Uᶜ => (⟨((y : Sph (coneForm c Q') c) : Fin (k + 1 + 1) → ℝ),
        (y : Sph (coneForm c Q') c).2⟩ : Sph (splitForm c (Qm c Q')) c) :=
      (continuous_subtype_val.comp continuous_subtype_val).measurable.subtype_mk
    exact (measurable_secFun hc _ _).comp hm
  have e : U.domRestrict (secC hc hQ') = fun y : ↥U =>
      dG hc hQ' (inv_ne_zero y.2) * nG hc hQ' (tl ((y : Sph (coneForm c Q') c) : Fin (k + 1 + 1) → ℝ)) := by
    funext y; show secC hc hQ' y.1 = _; unfold secC
    rw [dif_pos (show ((y : Sph (coneForm c Q') c) : Fin (k + 1 + 1) → ℝ) 0 -
        ((y : Sph (coneForm c Q') c) : Fin (k + 1 + 1) → ℝ) 1 ≠ 0 from y.2)]
  rw [e]
  have hq : Continuous fun x : {x : Sph (coneForm c Q') c //
      (x : Fin (k + 1 + 1) → ℝ) 0 - (x : Fin (k + 1 + 1) → ℝ) 1 ≠ 0} =>
      ((x : Fin (k + 1 + 1) → ℝ) 0 - (x : Fin (k + 1 + 1) → ℝ) 1) :=
    ((continuous_apply 0).comp (continuous_subtype_val.comp continuous_subtype_val)).sub
      ((continuous_apply 1).comp (continuous_subtype_val.comp continuous_subtype_val))
  have hqi : Continuous fun x : {x : Sph (coneForm c Q') c //
      (x : Fin (k + 1 + 1) → ℝ) 0 - (x : Fin (k + 1 + 1) → ℝ) 1 ≠ 0} =>
      (⟨((x : Fin (k + 1 + 1) → ℝ) 0 - (x : Fin (k + 1 + 1) → ℝ) 1)⁻¹, inv_ne_zero x.2⟩ : {a : ℝ // a ≠ 0}) :=
    (hq.inv₀ fun x => x.2).subtype_mk _
  have hc1 := (continuous_dG' hc hQ').comp hqi
  have hc2 : Continuous fun y : ↥U => nG hc hQ' (tl ((y : Sph (coneForm c Q') c) : Fin (k + 1 + 1) → ℝ)) :=
    (continuous_nG hc hQ').comp (continuous_tl.comp (continuous_subtype_val.comp continuous_subtype_val))
  exact (hc1.mul hc2).measurable

/-- **The parabolic sphere section** as `SphSection`. -/
def coneSphSection : SphSection c (Qm c Q') := ⟨secC hc hQ', measurable_secC hc hQ', secC_spec hc hQ'⟩


/-! ### Unimodularity: inversion invariance -/

omit hc hQ' in
/-- **A right-invariant Haar measure is inversion invariant** (unimodular LCSC groups). -/
theorem inv_eq_self_of_unimodular {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsHaarMeasure μ] [IsMulRightInvariant μ] : μ.inv = μ := by
  set c := haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := isMulLeftInvariant_eq_smul μ.inv μ
  have h2 : μ = (c * c) • μ := by
    conv_lhs => rw [← Measure.inv_inv μ, hc]
    rw [Measure.inv_def, Measure.map_smul _ measurable_inv.aemeasurable, ← Measure.inv_def, hc, smul_smul]
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h0 : μ K ≠ 0 := (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have ht : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have h3 : ((c * c : ℝ≥0) : ℝ≥0∞) * μ K = 1 * μ K := by
    conv_rhs => rw [one_mul, h2]
    rfl
  have h4 : ((c * c : ℝ≥0) : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj h0 ht).1 h3
  have h5 : c = 1 := by
    have h6 : (c : ℝ) * c = 1 := by exact_mod_cast h4
    have h7 : ((c : ℝ) - 1) * ((c : ℝ) + 1) = 0 := by linear_combination h6
    have h8 : (c : ℝ) + 1 ≠ 0 := by positivity
    have h9 : (c : ℝ) = 1 := by linarith [(mul_eq_zero.mp h7).resolve_right h8]
    exact_mod_cast h9
  rw [hc, h5, one_smul]

omit hc hQ' in
/-- $\int f(g^{-1})\,d\mu_Q = \int f\,d\mu_Q$ for the Leray measure (unimodularity). -/
theorem lintegral_inv_lerayMeasure {n : ℕ} {Q : QuadForm ℝ n} (hQ : gramDetR Q ≠ 0) {f : ArchSO Q → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ g, f g⁻¹ ∂lerayMeasure Q hQ = ∫⁻ g, f g ∂lerayMeasure Q hQ := by
  have := isHaarMeasure_lerayMeasure hQ
  have := LerayReal.isMulRightInvariant_lerayMeasure hQ
  have h := inv_eq_self_of_unimodular (lerayMeasure Q hQ)
  rw [← lintegral_map hf measurable_inv, ← Measure.inv_def, h]

/-! ### The parametric cone identity -/

/-- $d(q)$ for $q \ne 0$ (and $1$ at $q = 0$, a null point). -/
def dGt (q : ℝ) : ArchSO (coneForm c Q') := if h : q = 0 then 1 else dG hc hQ' h

theorem dGt_of_ne {q : ℝ} (h : q ≠ 0) : dGt hc hQ' q = dG hc hQ' h := dif_neg h

theorem measurable_dGt : Measurable (dGt hc hQ') := by
  refine measurable_of_continuousOn_compl_singleton 0 ?_
  rw [continuousOn_iff_continuous_domRestrict]
  have e : ({0}ᶜ : Set ℝ).domRestrict (dGt hc hQ') = fun a : ({0}ᶜ : Set ℝ) => dG hc hQ' a.2 := by
    funext a; exact dGt_of_ne hc hQ' a.2
  rw [e]
  exact (continuous_dG' hc hQ').comp (continuous_subtype_val.subtype_mk fun a => a.2)

theorem graphV_mem {q : ℝ} (hq : q ≠ 0) (y : Fin k → ℝ) : graphV c Q' q y ∈ sph (coneForm c Q') c :=
  eval_graphV hc hq y

theorem graphV_sub {q : ℝ} (y : Fin k → ℝ) : graphV c Q' q y 0 - graphV c Q' q y 1 = q := by
  rw [graphV]; simp

theorem tl_graphV {q : ℝ} (y : Fin k → ℝ) : tl (graphV c Q' q y) = y := by rw [graphV, tl_v3]

theorem secC_graph {q : ℝ} (hq : q ≠ 0) (y : Fin k → ℝ) :
    secC hc hQ' ⟨graphV c Q' q y, graphV_mem hc hQ' hq y⟩ = dG hc hQ' (inv_ne_zero hq) * nG hc hQ' y := by
  unfold secC
  have h : graphV c Q' q y 0 - graphV c Q' q y 1 ≠ 0 := by rw [graphV_sub hc hQ']; exact hq
  rw [dif_pos h]
  congr 1
  · exact mat_ext' (by rw [mat_dG, mat_dG, graphV_sub hc hQ'])
  · rw [tl_graphV hc hQ']

theorem inv_dG_nG {q : ℝ} (hq : q ≠ 0) (y : Fin k → ℝ) :
    (dG hc hQ' (inv_ne_zero hq) * nG hc hQ' y)⁻¹ = dG hc hQ' hq * nG hc hQ' (-(q⁻¹ • y)) := by
  rw [_root_.mul_inv_rev, nG_neg, dG_inv, dG_mul_nG hc hQ' hq, smul_neg, smul_smul, mul_inv_cancel₀ hq, one_smul]
  congr 1
  exact mat_ext' (by rw [mat_dG, mat_dG, inv_inv])

omit hQ' in
/-- The sphere chart for functions on the sphere (extension by $0$ off $S_c$). -/
theorem lintegral_sig_graph' {G : Sph (coneForm c Q') c → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G x ∂sig (coneForm c Q') c = ∫⁻ q, ∫⁻ y, ENNReal.ofReal (1 / (2 * |c| * |q|)) *
      Function.extend Subtype.val G 0 (graphV c Q' q y) := by
  have he := MeasurableEmbedding.subtype_coe (measurableSet_sph (coneForm c Q') c)
  have hm : Measurable (Function.extend Subtype.val G 0) := he.measurable_extend hG measurable_const
  rw [← lintegral_sig_graph hc hm]
  refine lintegral_congr fun x => ?_
  exact (Subtype.val_injective.extend_apply G 0 x).symm


theorem mG_mul_dGt (h : ArchSO Q') (q : ℝ) : mG c Q' h * dGt hc hQ' q = dGt hc hQ' q * mG c Q' h := by
  by_cases hq : q = 0
  · simp [dGt, hq]
  · rw [dGt_of_ne hc hQ' hq, mG_mul_dG]

/-- Step 1 (sphere identity on $S_c$, inversion, sphere chart). -/
theorem lintegral_cone_P1 {f : ArchSO (coneForm c Q') → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ g, f g ∂lerayMeasure (coneForm c Q') (gramDetR_cone hc hQ') =
      ENNReal.ofReal ((|2 * c| ^ (k + 1))⁻¹) * ∫⁻ q, ∫⁻ y, ENNReal.ofReal (1 / (2 * |c| * |q|)) *
        ∫⁻ h, f (iota c (Qm c Q') h * dGt hc hQ' q * nG hc hQ' (-(q⁻¹ • y))) ∂lerayMeasure (Qm c Q')
          (gramDetR_Qm hc hQ') := by
  have := isHaarMeasure_lerayMeasure (gramDetR_Qm hc hQ')
  rw [← lintegral_inv_lerayMeasure _ hf]
  rw [lintegral_lerayMeasure_orbital hc (gramDetR_Qm hc hQ') (coneSphSection hc hQ') (f := fun g => f g⁻¹)
    (hf.comp measurable_inv)]
  congr 1
  set G : Sph (coneForm c Q') c → ℝ≥0∞ := fun x => ∫⁻ h, f (iota c (Qm c Q') h * (secC hc hQ' x)⁻¹)
    ∂lerayMeasure (Qm c Q') (gramDetR_Qm hc hQ') with hG
  have hGm : Measurable G := by
    have : Measurable fun p : Sph (coneForm c Q') c × ArchSO (Qm c Q') =>
        f (iota c (Qm c Q') p.2 * (secC hc hQ' p.1)⁻¹) :=
      hf.comp (((continuous_iota _ _).measurable.comp measurable_snd).mul
        ((measurable_secC hc hQ').comp measurable_fst).inv)
    exact this.lintegral_prod_right'
  have step3 : ∀ x : Sph (coneForm c Q') c, (∫⁻ h, f ((coneSphSection hc hQ').toFun x * iota c (Qm c Q') h)⁻¹
      ∂lerayMeasure (Qm c Q') (gramDetR_Qm hc hQ')) = G x := by
    intro x
    have hF : Measurable fun h : ArchSO (Qm c Q') => f (iota c (Qm c Q') h * (secC hc hQ' x)⁻¹) :=
      hf.comp (((continuous_iota _ _).measurable).mul_const _)
    show _ = ∫⁻ h, f (iota c (Qm c Q') h * (secC hc hQ' x)⁻¹) ∂lerayMeasure (Qm c Q') (gramDetR_Qm hc hQ')
    rw [← lintegral_inv_lerayMeasure _ hF]
    refine lintegral_congr fun h => ?_
    rw [map_inv, ← _root_.mul_inv_rev]
    rfl
  rw [lintegral_congr step3, lintegral_sig_graph' hc hGm]
  refine lintegral_congr fun q => lintegral_congr fun y => ?_
  by_cases hq : q = 0
  · simp [hq]
  · congr 1
    have e := Subtype.val_injective.extend_apply G 0
      (⟨graphV c Q' q y, graphV_mem hc hQ' hq y⟩ : Sph (coneForm c Q') c)
    rw [show graphV c Q' q y = ((⟨graphV c Q' q y, graphV_mem hc hQ' hq y⟩ : Sph (coneForm c Q') c) :
      Fin (k + 1 + 1) → ℝ) from rfl, e, hG]
    simp only
    rw [secC_graph hc hQ' hq, inv_dG_nG hc hQ' hq, dGt_of_ne hc hQ' hq]
    simp only [mul_assoc]


/-- Step 2 (sphere identity for $SO(\langle -c\rangle \perp Q')$ on $S'_{-c}$, commutation in the parabolic). -/
theorem lintegral_cone_P2 (s' : SphSection (-c) Q') {f : ArchSO (coneForm c Q') → ℝ≥0∞} (hf : Measurable f)
    (q : ℝ) (w₀ : Fin k → ℝ) :
    ∫⁻ h, f (iota c (Qm c Q') h * dGt hc hQ' q * nG hc hQ' w₀) ∂lerayMeasure (Qm c Q') (gramDetR_Qm hc hQ') =
      ENNReal.ofReal ((|2 * c| ^ k)⁻¹) * ∫⁻ y, ∫⁻ h, f (iota c (Qm c Q') (s'.toFun y) * dGt hc hQ' q *
        nG hc hQ' (ArchSOInst.mat _ h *ᵥ w₀) * mG c Q' h) ∂lerayMeasure Q' hQ' ∂sig (Qm c Q') (-c) := by
  have hF : Measurable fun h : ArchSO (Qm c Q') => f (iota c (Qm c Q') h * dGt hc hQ' q * nG hc hQ' w₀) :=
    hf.comp (((continuous_iota _ _).measurable.mul_const _).mul_const _)
  rw [lintegral_lerayMeasure_orbital (neg_ne_zero.mpr hc) hQ' s' hF]
  have habs : |2 * -c| = |2 * c| := by rw [mul_neg, abs_neg]
  rw [habs]
  congr 1
  refine lintegral_congr fun y => lintegral_congr fun h => ?_
  congr 1
  rw [map_mul]
  change iota c (Qm c Q') (s'.toFun y) * mG c Q' h * dGt hc hQ' q * nG hc hQ' w₀ = _
  rw [mul_assoc (iota c (Qm c Q') (s'.toFun y)), mG_mul_dGt, ← mul_assoc, mul_assoc _ (mG c Q' h),
    mG_mul_nG, ← mul_assoc]

omit hc hQ' in
/-- $\int_{\mathbb R^k}\Psi(a\,z)\,dz = |a|^{-k}\int\Psi$, in the form $|a^{-1}|^k$. -/
theorem lintegral_smul_vec' {Ψ : (Fin k → ℝ) → ℝ≥0∞} (hΨ : Measurable Ψ) {a : ℝ} (ha : a ≠ 0) :
    ∫⁻ z, Ψ (a • z) = ENNReal.ofReal (|a⁻¹| ^ k) * ∫⁻ w, Ψ w := by
  have := lintegral_smul_vec (K := fun z => Ψ (a • z)) (hΨ.comp (measurable_const_smul a)) (inv_ne_zero ha)
  rw [this]
  congr 1
  refine lintegral_congr fun w => ?_
  rw [smul_smul, mul_inv_cancel₀ ha, one_smul]

/-- Step 3 (the substitution $w = h\,(-q^{-1}y)$ on $V' = \mathbb R^k$, Jacobian $|q|^{-k}$). -/
theorem lintegral_cone_P3 {q : ℝ} (hq : q ≠ 0)
    {Φ : Sph (Qm c Q') (-c) × ArchSO Q' × (Fin k → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ y, ∫⁻ x, ∫⁻ h, Φ (x, h, ArchSOInst.mat _ h *ᵥ (-(q⁻¹ • y))) ∂lerayMeasure Q' hQ' ∂sig (Qm c Q') (-c) =
      ENNReal.ofReal (|q| ^ k) * ∫⁻ x, ∫⁻ h, ∫⁻ w, Φ (x, h, w) ∂volume ∂lerayMeasure Q' hQ'
        ∂sig (Qm c Q') (-c) := by
  have := isHaarMeasure_lerayMeasure hQ'
  have := sigmaFinite_sig (Q := Qm c Q') (neg_ne_zero.mpr hc)
  have hM : Continuous fun h : ArchSO Q' => ArchSOInst.mat _ h := ArchSOInst.continuous_mat Q'
  have hm3 : Measurable fun p : ((Fin k → ℝ) × Sph (Qm c Q') (-c)) × ArchSO Q' =>
      Φ (p.1.2, p.2, ArchSOInst.mat _ p.2 *ᵥ (-(q⁻¹ • p.1.1))) := by
    refine hΦ.comp ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.prodMk ?_))
    exact ((hM.comp continuous_snd).matrix_mulVec
      ((continuous_const_smul _).comp (continuous_fst.comp continuous_fst)).neg).measurable
  rw [lintegral_lintegral_swap hm3.lintegral_prod_right'.aemeasurable]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun x => ?_
  have hm2 : Measurable fun p : (Fin k → ℝ) × ArchSO Q' => Φ (x, p.2, ArchSOInst.mat _ p.2 *ᵥ (-(q⁻¹ • p.1))) :=
    hm3.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  rw [lintegral_lintegral_swap hm2.aemeasurable, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun h => ?_
  have e : ∀ y : Fin k → ℝ, ArchSOInst.mat _ h *ᵥ (-(q⁻¹ • y)) = (-q⁻¹) • (ArchSOInst.mat _ h *ᵥ y) := by
    intro y; rw [mulVec_neg, mulVec_smul, neg_smul]
  simp_rw [e]
  have hΨ : Measurable fun z : Fin k → ℝ => Φ (x, h, (-q⁻¹) • z) :=
    hΦ.comp (measurable_const.prodMk (measurable_const.prodMk (measurable_const_smul _)))
  have hdet : |(ArchSOInst.mat _ h).det| = 1 := by rw [ArchSOInst.det_mat, abs_one]
  rw [(ArchVol.measurePreserving_mulVec _ hdet).lintegral_comp hΨ,
    lintegral_smul_vec' (Ψ := fun w => Φ (x, h, w)) (hΦ.comp (measurable_const.prodMk
      (measurable_const.prodMk measurable_id))) (neg_ne_zero.mpr (inv_ne_zero hq)), inv_neg, inv_inv, abs_neg]


/-- **The parametric cone identity** (real places, any signature; $Q = \langle c\rangle\perp\langle -c\rangle\perp Q'$,
$Q'$ nondegenerate in $k$ variables, $s'$ any measurable section of $SO(\langle -c\rangle \perp Q') \to S'_{-c}$):
$$\int f\,d\mu_Q = |2c|^{-(k+1)}|2c|^{-k}\int_{\mathbb R}\frac{|q|^k}{2|c||q|}\int_{S'_{-c}}\int_{SO(Q')}
  \int_{\mathbb R^k}f\big(\iota(s'(y))\,d(q)\,n(w)\,\mathrm{diag}(1,1,h)\big)\,dw\,d\mu_{Q'}(h)\,d\sigma'_{-c}(y)\,dq.$$
So $SO(Q)$ is, up to a null set, $\iota(SO(\langle -c\rangle\perp Q'))\cdot A\cdot N\cdot SO(Q')$ with Haar measure
$|2c|^{-(2k+2)}\,\sigma'_{-c}\otimes|q|^{k-1}dq\otimes dw\otimes\mu_{Q'}$. -/
@[kb "weil1982" "§2.4 (Lemma 2.4.1 / Theorem 2.4.3 for the cone orbit; stabilizer P = SO(V')⋉V') [unverified]"]
theorem lintegral_lerayMeasure_cone_param (s' : SphSection (-c) Q') {f : ArchSO (coneForm c Q') → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ g, f g ∂lerayMeasure (coneForm c Q') (gramDetR_cone hc hQ') =
      ENNReal.ofReal ((|2 * c| ^ (k + 1))⁻¹) * ENNReal.ofReal ((|2 * c| ^ k)⁻¹) *
        ∫⁻ q, ENNReal.ofReal (|q| ^ k / (2 * |c| * |q|)) *
          ∫⁻ y, ∫⁻ h, ∫⁻ w, f (iota c (Qm c Q') (s'.toFun y) * dGt hc hQ' q * nG hc hQ' w * mG c Q' h)
            ∂volume ∂lerayMeasure Q' hQ' ∂sig (Qm c Q') (-c) := by
  rw [lintegral_cone_P1 hc hQ' hf, mul_assoc]
  congr 1
  have hΦ : ∀ q : ℝ, Measurable fun p : Sph (Qm c Q') (-c) × ArchSO Q' × (Fin k → ℝ) =>
      f (iota c (Qm c Q') (s'.toFun p.1) * dGt hc hQ' q * nG hc hQ' p.2.2 * mG c Q' p.2.1) := by
    intro q
    exact hf.comp (((((continuous_iota _ _).measurable.comp (s'.measurable.comp measurable_fst)).mul_const _).mul
      ((continuous_nG hc hQ').measurable.comp (measurable_snd.comp measurable_snd))).mul
      (continuous_mG.measurable.comp (measurable_fst.comp measurable_snd)))
  have hae : ∀ᵐ q : ℝ, q ≠ 0 := by
    rw [ae_iff]; simp only [ne_eq, not_not, ofPred_eq_eq_singleton, measure_singleton]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with q hq
  have e1 : ∀ y : Fin k → ℝ, ENNReal.ofReal (1 / (2 * |c| * |q|)) * ∫⁻ h, f (iota c (Qm c Q') h * dGt hc hQ' q *
      nG hc hQ' (-(q⁻¹ • y))) ∂lerayMeasure (Qm c Q') (gramDetR_Qm hc hQ') =
      ENNReal.ofReal (1 / (2 * |c| * |q|)) * (ENNReal.ofReal ((|2 * c| ^ k)⁻¹) *
        ∫⁻ x, ∫⁻ h, f (iota c (Qm c Q') (s'.toFun x) * dGt hc hQ' q *
          nG hc hQ' (ArchSOInst.mat _ h *ᵥ (-(q⁻¹ • y))) * mG c Q' h) ∂lerayMeasure Q' hQ' ∂sig (Qm c Q') (-c)) := by
    intro y; rw [lintegral_cone_P2 hc hQ' s' hf]
  simp_rw [e1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_cone_P3 hc hQ' hq (hΦ q)]
  have hq0 : 0 < |q| := abs_pos.mpr hq
  have hc0 : 0 < |c| := abs_pos.mpr hc
  rw [show |q| ^ k / (2 * |c| * |q|) = 1 / (2 * |c| * |q|) * |q| ^ k by ring,
    ENNReal.ofReal_mul (by positivity)]
  ring

end QuadFormsKB.Tamagawa.Measure.ConeReal
