/-
# The theta kernel

**Layer:** global, over a number field $F$ (the bridge: totally real $F$).

**The kernel.** An adelic point $h$ of the orthogonal group acts on data by $\Phi \mapsto \Phi\circ h^{-1}$ at every
place; we record the maps $\sigma_u = h_u^{-1}$ (`AdelicMap`, `GDatum.comp`). For $\gamma \in \mathrm{SL}_2(F)$,
$$\theta(\gamma, h;\Phi) = \sum_{\xi\in V(F)}(\omega(\gamma)\Phi)(h^{-1}\xi)\qquad(\texttt{thetaKernel}).$$

* `thetaDist_comp_ratMul`, `thetaKernel_left_rat`: **left invariance under $O(V)(F)$** (indeed under all of
  $\mathrm{GL}_n(F)$): $\theta(\gamma, \delta h) = \theta(\gamma, h)$, since $\xi \mapsto \delta^{-1}\xi$ is a bijection of $V(F)$.
* `thetaKernel_one_left_SL2`: **left invariance under $\mathrm{SL}_2(F)$** at $h = 1$:
  $\theta(\gamma\gamma', 1;\Phi) = \theta(\gamma', 1;\Phi) = \Theta(\Phi)$ for fully factorizable $\Phi$ (`thetaDist_omegaG`).
* `thetaDist_omegaG_borelInf`: with an archimedean Borel element $g_\infty = n(x)m(t)$ ($x \in F_\infty$,
  $t \in F_\infty^\times$) acting first: $\Theta(\omega(\gamma)\omega_\infty(g_\infty)\Phi) = \Theta(\omega_\infty(g_\infty)\Phi)$, i.e.
  $g_\infty \mapsto \theta(g_\infty, 1;\Phi)$ is left $\mathrm{SL}_2(F)$-invariant, with $\omega(\gamma g_\infty) := \omega(\gamma)\omega(g_\infty)$.

**The bridge to the classical theta series** (`thetaKernel_gz_eq_thetaQ`). Let $F$ be totally real, $a_i \in \mathcal O_F$
nonzero, $Q = \langle a_0, \dots, a_{2m-1}\rangle$ (`QuadForm.diag`), $\varphi_\infty(x) = e^{-2\pi\sum_wQ_w(x_w)}$ the
standard Gaussian (`gaussQ`), $\varphi_v = \mathbf 1_{\mathcal O_v^{2m}}$, and for $z \in \mathbb H^d$ let
$g_z = n(x)m(y^{1/2})$ at the infinite places ($x_w = \operatorname{Re}z_w$, $y_w = \operatorname{Im}z_w$). Then
$$\theta(g_z, 1;\varphi) = \prod_{w}y_w^{n/4}\cdot\theta_Q(z),\qquad n = 2m,$$
with $\theta_Q(z) = \sum_{x\in\mathcal O_F^n}e(\operatorname{Tr}(Q(x)z))$ the theta series of `HilbertModular/Theta.lean`.

**Not done here** (see `docs/weil-representation.md`): $\mathrm{SL}_2(F)$-invariance of $\theta(\cdot, h)$ for $h_\infty \ne 1$
needs Poisson summation for non-factorizable archimedean components, and for $h_f \ne 1$ the linear extension of
`thetaDist_omegaG` to sums of factorizable data; the multiplicativity $\omega_\infty(gg') = \omega_\infty(g)\omega_\infty(g')$
needs the Weil identity for all Schwartz functions at the archimedean places.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Global
import QuadFormsKB.HilbertModular.Theta

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Metric MeasureTheory
open QuadFormsKB.Analysis Matrix
open scoped MatrixGroups Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep

open LocalData

variable {F : Type} [Field F] [NumberField F]

/-! ### Translates by the orthogonal group -/

variable (F) in
/-- **The inverse $h^{-1}$ of an adelic point $h$**, as maps $\sigma_\infty$ on $F_\infty^n$ and $\sigma_v$ on $F_v^n$ (for
$h \in O(V)(\mathbb A)$: $\sigma_u = h_u^{-1}$, $\sigma_v$ preserving $\mathcal O_v^n$ for almost all $v$). -/
structure AdelicMap (n : ℕ) where
  inf : (Fin n → mixedSpace F) → (Fin n → mixedSpace F)
  fin : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → v.adicCompletion F) → (Fin n → v.adicCompletion F)

/-- The identity. -/
def AdelicMap.id (n : ℕ) : AdelicMap F n := ⟨fun x => x, fun _ x => x⟩

/-- **The translate $\Phi\circ h^{-1}$** of a datum. -/
def GDatum.comp {n : ℕ} (Φ : GDatum F n) (σ : AdelicMap F n) : GDatum F n :=
  ⟨Φ.inf ∘ σ.inf, fun v => Φ.fin v ∘ σ.fin v⟩

@[simp] lemma GDatum.comp_id {n : ℕ} (Φ : GDatum F n) : Φ.comp (AdelicMap.id n) = Φ := rfl

/-- $\sigma\circ M$ for a rational matrix $M \in \mathrm{GL}_n(F)$ acting at every place (for $h \mapsto \delta h$:
$(\delta h)^{-1} = h^{-1}\delta^{-1}$, $M = \delta^{-1}$). -/
def AdelicMap.ratMul {n : ℕ} (σ : AdelicMap F n) (M : GL (Fin n) F) : AdelicMap F n :=
  ⟨fun x => σ.inf ((M : Matrix (Fin n) (Fin n) F).map (mixedEmbedding F) *ᵥ x),
    fun v x => σ.fin v ((M : Matrix (Fin n) (Fin n) F).map (algebraMap F (v.adicCompletion F)) *ᵥ x)⟩

/-- $\xi \mapsto M\xi$ on $F^n$. -/
def mulVecEquiv {n : ℕ} (M : GL (Fin n) F) : (Fin n → F) ≃ (Fin n → F) where
  toFun ξ := (M : Matrix (Fin n) (Fin n) F) *ᵥ ξ
  invFun ξ := ((M⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ ξ
  left_inv ξ := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  right_inv ξ := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]

/-- **$\Theta$ is invariant under rational translations** $h \mapsto \delta h$, $\delta \in \mathrm{GL}_n(F)$ (in particular
$\delta \in O(V)(F)$), for every datum. -/
@[kb "weil1964" "§29 (invariance of $\\sum_\\xi$ under the rational points) [unverified]"]
theorem thetaDist_comp_ratMul {n : ℕ} (Ψ : GDatum F n) (σ : AdelicMap F n) (M : GL (Fin n) F) :
    thetaDist (Ψ.comp (σ.ratMul M)) = thetaDist (Ψ.comp σ) := by
  have h : ∀ ξ, (Ψ.comp (σ.ratMul M)).eval ξ = (Ψ.comp σ).eval (mulVecEquiv M ξ) := by
    intro ξ
    simp only [GDatum.eval, GDatum.comp, AdelicMap.ratMul, Function.comp, mulVecEquiv, Equiv.coe_fn_mk]
    congr 2
    · congr 1; funext i
      exact (RingHom.map_mulVec (mixedEmbedding F) _ ξ i).symm
    · funext v; congr 2; funext i
      exact (RingHom.map_mulVec (algebraMap F (v.adicCompletion F)) _ ξ i).symm
  rw [thetaDist, tsum_congr h]
  exact (mulVecEquiv M).tsum_eq fun ξ => (Ψ.comp σ).eval ξ

/-! ### The theta kernel -/

variable {m : ℕ} (a : Fin (2 * m) → Fˣ)

/-- **The theta kernel** $\theta(\gamma, h;\Phi) = \sum_{\xi\in V(F)}(\omega(\gamma)\Phi)(h^{-1}\xi)$ for
$\gamma \in \mathrm{SL}_2(F)$ and $h^{-1} = \sigma$. -/
@[kb "weil1964" "§29; Kudla, Notes §I.4 (the theta kernel $\\theta(g, h;\\varphi)$) [unverified]"]
def thetaKernel (γ : SL(2, F)) (σ : AdelicMap F (2 * m)) (Φ : GDatum F (2 * m)) : ℂ :=
  thetaDist ((omegaG a γ Φ).comp σ)

/-- **Left $O(V)(F)$-invariance** of the theta kernel (indeed $\mathrm{GL}_n(F)$-invariance). -/
@[kb "kudla1996" "§I.4 (left invariance of the theta kernel) [unverified]"]
theorem thetaKernel_left_rat (γ : SL(2, F)) (σ : AdelicMap F (2 * m)) (M : GL (Fin (2 * m)) F)
    (Φ : GDatum F (2 * m)) : thetaKernel a γ (σ.ratMul M) Φ = thetaKernel a γ σ Φ :=
  thetaDist_comp_ratMul _ σ M

/-- **Left $\mathrm{SL}_2(F)$-invariance** of the theta kernel at $h = 1$, for fully factorizable $\Phi$:
$\theta(\gamma\gamma', 1;\Phi) = \theta(\gamma', 1;\Phi)$ $(= \Theta(\Phi))$. -/
@[kb "kudla1996" "§I.4 (left invariance of the theta kernel) [unverified]"]
theorem thetaKernel_one_left_SL2 {Φ : GDatum F (2 * m)} (hΦ : Φ.IsPure) (γ γ' : SL(2, F)) :
    thetaKernel a (γ * γ') (AdelicMap.id _) Φ = thetaKernel a γ' (AdelicMap.id _) Φ := by
  simp only [thetaKernel, GDatum.comp_id, thetaDist_omegaG a hΦ]

/-! ### An archimedean Borel element -/

/-- **$\omega_\infty(n(x)m(t))$**, $x, t \in F_\infty$, acting on the archimedean component only. -/
def borelInf (x t : mixedSpace F) : Function.End (GDatum F (2 * m)) := fun Φ =>
  ⟨(localDataInf (F := F)).opNf (aInf a) x ((localDataInf (F := F)).opMf (aInf a) t Φ.inf), Φ.fin⟩

/-- Multiplication by a unit of $F_\infty$, as a continuous linear equivalence. -/
def mulCLE (t : (mixedSpace F)ˣ) : mixedSpace F ≃L[ℝ] mixedSpace F :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => (t : mixedSpace F) * x
      invFun := fun x => ((t⁻¹ : (mixedSpace F)ˣ) : mixedSpace F) * x
      map_add' := fun x y => mul_add _ x y
      map_smul' := fun c x => by simp [Algebra.mul_smul_comm]
      left_inv := fun x => by simp [← mul_assoc]
      right_inv := fun x => by simp [← mul_assoc] }

lemma dil_mem_schwartzInf (t : (mixedSpace F)ˣ) {g : mixedSpace F → ℂ} (hg : g ∈ schwartzInf) :
    dil (t : mixedSpace F) g ∈ schwartzInf := by
  obtain ⟨G, rfl⟩ := hg
  exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mulCLE t) G, rfl⟩

lemma GDatum.IsPure.borelInf {Φ : GDatum F (2 * m)} (hΦ : Φ.IsPure) (x : mixedSpace F)
    (t : (mixedSpace F)ˣ) : (borelInf a x t Φ).IsPure := by
  obtain ⟨c₀, f₀, c, f, T, hf₀, hf, hT, rfl⟩ := hΦ
  refine ⟨(localDataInf (F := F)).chiV (aInf a) t * ((localDataInf (F := F)).md t : ℂ) ^ m * c₀,
    fun i => (localDataInf (F := F)).chirp (x * (aInf a i : mixedSpace F)) (dil (t : mixedSpace F) (f₀ i)),
    c, f, T, fun i => chirp_mem_schwartzInf _ (dil_mem_schwartzInf t (hf₀ i)), hf, hT, ?_⟩
  show GDatum.mk _ _ = GDatum.mk _ _
  congr 1
  dsimp only [pureD]
  rw [opMf_smul, opMf_ptensor, smul_smul, opNf_smul, opNf_ptensor]
  rw [mul_comm c₀]

/-- **Left $\mathrm{SL}_2(F)$-invariance after an archimedean Borel element:** for fully factorizable $\Phi$,
$\gamma \in \mathrm{SL}_2(F)$, $x \in F_\infty$, $t \in F_\infty^\times$,
$\Theta\big(\omega(\gamma)\,\omega_\infty(n(x)m(t))\Phi\big) = \Theta\big(\omega_\infty(n(x)m(t))\Phi\big)$. -/
@[kb "kudla1996" "§I.4 (automorphy of $\\theta(g, h;\\varphi)$ in $g$) [unverified]"]
theorem thetaDist_omegaG_borelInf {Φ : GDatum F (2 * m)} (hΦ : Φ.IsPure) (γ : SL(2, F)) (x : mixedSpace F)
    (t : (mixedSpace F)ˣ) : thetaDist (omegaG a γ (borelInf a x t Φ)) = thetaDist (borelInf a x t Φ) :=
  thetaDist_omegaG a (hΦ.borelInf a x t) γ

/-! ### The bridge to the classical theta series (totally real $F$) -/

section Bridge

variable [IsTotallyReal F] (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)

lemma eval_diag (x : Fin (2 * m) → 𝓞 F) : (QuadForm.diag b).eval x = ∑ i, b i * x i ^ 2 := by
  simp only [QuadForm.eval, QuadForm.evalIn, QuadForm.diag, Algebra.algebraMap_self, RingHom.id_apply,
    Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp [sq, mul_assoc]
  · intro j _ hj; simp [Ne.symm hj]
  · simp

/-- The coefficients $a_i = b_i \in F^\times$. -/
def bF : Fin (2 * m) → Fˣ := fun i => Units.mk0 (b i : F) (by exact_mod_cast hb i)

/-- **The standard Gaussian of $Q$ at the infinite places:** $\varphi_\infty(x) = \exp\big(-2\pi\sum_w\sum_ib_i^{(w)}x_{i,w}^2\big)$,
$w$ running over the real places. -/
def gaussQ (x : Fin (2 * m) → mixedSpace F) : ℂ :=
  Complex.exp (-(2 * Real.pi) * ((∑ w : {w : InfinitePlace F // IsReal w}, ∑ i,
    (mixedEmbedding F (b i : F)).1 w * ((x i).1 w) ^ 2 : ℝ) : ℂ))

/-- The standard datum $\varphi = \varphi_\infty\otimes\bigotimes_v\mathbf 1_{\mathcal O_v^n}$. -/
def phiStd : GDatum F (2 * m) := ⟨gaussQ b, fun v => oneV v (2 * m)⟩

/-- $x = (\operatorname{Re}z_w)_w \in F_\infty$. -/
def zRe (z : InfinitePlace F → UpperHalfPlane) : mixedSpace F := (fun w => (z w.1).re, fun w => isEmptyElim w)

/-- $y^{1/2} = (\operatorname{Im}(z_w)^{1/2})_w \in F_\infty^\times$. -/
def zSqrtIm (z : InfinitePlace F → UpperHalfPlane) : (mixedSpace F)ˣ where
  val := (fun w => Real.sqrt (z w.1).im, fun w => isEmptyElim w)
  inv := (fun w => (Real.sqrt (z w.1).im)⁻¹, fun w => isEmptyElim w)
  val_inv := by
    ext w
    · exact mul_inv_cancel₀ (Real.sqrt_pos.mpr (z w.1).im_pos).ne'
    · exact isEmptyElim w
  inv_val := by
    ext w
    · exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (z w.1).im_pos).ne'
    · exact isEmptyElim w

lemma real_coord_Qform (ξ : Fin (2 * m) → F) (w : {w : InfinitePlace F // IsReal w}) :
    (mixedEmbedding F (Qform (bF b hb) ξ)).1 w =
      ∑ i, (mixedEmbedding F (b i : F)).1 w * ((mixedEmbedding F (ξ i)).1 w) ^ 2 := by
  unfold Qform
  rw [map_sum, Prod.fst_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [bF, Units.val_mk0, map_mul, map_pow, Prod.fst_mul, Pi.mul_apply, sq]

lemma finprod_oneV_eq (ξ : Fin (2 * m) → F) :
    ∏ᶠ v, oneV v (2 * m) (ιV v ξ) = if ∀ i, ξ i ∈ (algebraMap (𝓞 F) F).range then 1 else 0 := by
  split_ifs with h
  · refine finprod_eq_one_of_forall_eq_one fun v => ?_
    unfold oneV ptensor
    refine Finset.prod_eq_one fun i _ => ?_
    obtain ⟨x, hx⟩ := h i
    show ballIndV v 0 0 (algebraMap F _ (ξ i)) = 1
    rw [ballIndV, Set.indicator_of_mem]
    simp only [sub_zero, neg_zero, WithZero.exp_zero, Set.mem_setOf_eq, ← hx, HN.valued_algebraMap]
    exact v.valuation_le_one x
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    have : ¬ ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (ξ i) ≤ 1 :=
      fun h' => hi (HeightOneSpectrum.mem_integers_of_valuation_le_one F (ξ i) h')
    push_neg at this
    obtain ⟨v, hv⟩ := this
    refine finprod_eq_zero _ v ?_ ?_
    · unfold oneV ptensor
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      show ballIndV v 0 0 (algebraMap F _ (ξ i)) = 0
      rw [ballIndV, Set.indicator_of_notMem]
      simp only [sub_zero, neg_zero, WithZero.exp_zero, Set.mem_setOf_eq, HN.valued_algebraMap, not_le]
      exact hv
    · refine (badSet_finite ξ).subset fun w hw => ?_
      by_contra h'
      exact hw (oneV_eval_eq_one h')

lemma hilbInf_zSqrtIm (z : InfinitePlace F → UpperHalfPlane) {d : mixedSpace F} (hd : ∀ w, d.1 w ≠ 0) :
    hilbInf ((zSqrtIm z : (mixedSpace F)ˣ) : mixedSpace F) d = 1 := by
  refine Finset.prod_eq_one fun w _ => ?_
  have hpos : 0 < Real.sqrt (z w.1).im := Real.sqrt_pos.mpr (z w.1).im_pos
  rcases HN.hilbertSymbol_eq_one_or ℝ (Real.sqrt (z w.1).im) (d.1 w) with h | h
  · exact h
  · exact absurd ((hilbertSymbol_real _ _ hpos.ne' (hd w)).mp h).1 (not_lt.mpr hpos.le)

lemma norm_zSqrtIm (z : InfinitePlace F → UpperHalfPlane) :
    mixedEmbedding.norm ((zSqrtIm z : (mixedSpace F)ˣ) : mixedSpace F) = ∏ v, Real.sqrt (z v).im := by
  rw [mixedEmbedding.norm_apply]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hm : v.mult = 1 := by simp [mult, IsTotallyReal.isReal v]
  rw [hm, pow_one, normAtPlace_apply_of_isReal (IsTotallyReal.isReal v)]
  exact abs_of_nonneg (Real.sqrt_nonneg _)

/-- The sum over the real places as a sum over all infinite places ($F$ totally real). -/
lemma sum_real_eq {G : InfinitePlace F → ℝ} :
    ∑ w : {w : InfinitePlace F // IsReal w}, G w.1 = ∑ v, G v :=
  Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun v => IsTotallyReal.isReal v) _ _ fun _ => rfl

/-- **The bridge:** for totally real $F$, $Q = \langle b_0, \dots, b_{2m-1}\rangle$ over $\mathcal O_F$, the standard datum
$\varphi = \varphi_\infty\otimes\bigotimes_v\mathbf 1_{\mathcal O_v^n}$ and $g_z = n(x)m(y^{1/2})$ at the infinite places,
$$\theta(g_z, 1;\varphi) = \sum_{\xi\in F^n}\big(\omega(g_z)\varphi\big)(\xi) = \prod_vy_v^{n/4}\cdot\theta_Q(z),\qquad n = 2m,$$
$\theta_Q$ = `HilbertModular.thetaQ`. Here $\omega_\infty(m(y^{1/2}))$ contributes $\chi_V(y^{1/2})|y^{1/2}|^{n/2} = \prod_vy_v^{n/4}$
($\chi_V = 1$ on totally positive elements), and $\omega_\infty(n(x))$ the phase $e(\operatorname{Tr}(xQ(\xi)))$. -/
@[kb "kudla1996" "§I.4; Hanke, AWS notes (4.24)–(4.30) (the classical theta function from the kernel) [unverified]"]
theorem thetaKernel_gz_eq_thetaQ (z : InfinitePlace F → UpperHalfPlane) :
    thetaDist (borelInf (bF b hb) (zRe z) (zSqrtIm z) (phiStd b)) =
      ((∏ v : InfinitePlace F, (z v).im ^ ((2 * m : ℝ) / 4) : ℝ) : ℂ) * HilbertModular.thetaQ (QuadForm.diag b) z := by
  set C : ℂ := ((∏ v : InfinitePlace F, (z v).im ^ ((2 * m : ℝ) / 4) : ℝ) : ℂ)
  -- the term at `ξ ∈ F^n`
  set term : (Fin (2 * m) → F) → ℂ := fun ξ =>
    Complex.exp (2 * Real.pi * Complex.I *
      ∑ v, (HilbertModular.realEmb F v (Qform (bF b hb) ξ) : ℂ) * (z v : ℂ))
  have hD : ∀ w, (mixedEmbedding F ((discV (bF b hb) : Fˣ) : F)).1 w ≠ 0 := fun w => by
    rw [mixedEmbedding_apply_isReal]; exact (map_ne_zero _).mpr (discV (bF b hb)).ne_zero
  have hinf : ∀ ξ : Fin (2 * m) → F, (borelInf (bF b hb) (zRe z) (zSqrtIm z) (phiStd b)).inf (ιInf ξ) =
      C * term ξ := by
    intro ξ
    simp only [borelInf, phiStd, LocalData.opNf, LocalData.opMf, Qform_ιInf, ψInf_eq]
    -- the character `χ_V(y^{1/2}) = 1`
    have hχ : (localDataInf (F := F)).chiV (aInf (bF b hb)) ((zSqrtIm z : (mixedSpace F)ˣ) : mixedSpace F) = 1 := by
      simp only [LocalData.chiV, LocalData.hC, discV_aInf]
      rw [show (localDataInf (F := F)).hilb = hilbInf from rfl, hilbInf_zSqrtIm z hD]; simp
    rw [hχ, one_mul]
    -- the modulus
    have hmd : ((localDataInf (F := F)).md ((zSqrtIm z : (mixedSpace F)ˣ) : mixedSpace F) : ℂ) ^ m = C := by
      show ((mixedEmbedding.norm ((zSqrtIm z : (mixedSpace F)ˣ) : mixedSpace F) : ℝ) : ℂ) ^ m = C
      rw [norm_zSqrtIm, ← Complex.ofReal_pow, ← Finset.prod_pow]
      congr 1
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (z v).im_pos.le]
      congr 1; ring
    rw [hmd]
    -- the Gaussian and the phase
    have hq : ∀ w : {w : InfinitePlace F // IsReal w},
        (mixedEmbedding F (Qform (bF b hb) ξ)).1 w = HilbertModular.realEmb F w.1 (Qform (bF b hb) ξ) := by
      intro w; rw [mixedEmbedding_apply_isReal]; rfl
    have hgauss : gaussQ b (fun i => ((zSqrtIm z : (mixedSpace F)ˣ) : mixedSpace F) * ιInf ξ i) =
        Complex.exp (-(2 * Real.pi) * ((∑ v, (z v).im * HilbertModular.realEmb F v (Qform (bF b hb) ξ) : ℝ) : ℂ)) := by
      unfold gaussQ
      congr 3
      rw [← sum_real_eq (G := fun v => (z v).im * HilbertModular.realEmb F v (Qform (bF b hb) ξ))]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [← hq, real_coord_Qform, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [zSqrtIm, ιInf, Prod.fst_mul, Pi.mul_apply, Units.val_mk]
      rw [mul_pow, Real.sq_sqrt (z w.1).im_pos.le]
      ring
    have hphase : (psiInf (zRe z * mixedEmbedding F (Qform (bF b hb) ξ)) : ℂ) =
        Complex.exp (2 * Real.pi * Complex.I *
          ((∑ v, (z v).re * HilbertModular.realEmb F v (Qform (bF b hb) ξ) : ℝ) : ℂ)) := by
      rw [psiInf, fourierChar_coe_eq_exp]
      congr 2
      rw [traceInf]
      have h0 : ∑ w : {w : InfinitePlace F // IsComplex w},
          2 * ((zRe z * mixedEmbedding F (Qform (bF b hb) ξ)).2 w).re = 0 :=
        Finset.sum_eq_zero fun w _ => isEmptyElim w
      rw [h0, add_zero, ← sum_real_eq (G := fun v => (z v).re * HilbertModular.realEmb F v (Qform (bF b hb) ξ))]
      push_cast
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [← hq]
      simp [zRe, Prod.fst_mul]
    rw [hgauss, hphase]
    simp only [term]
    rw [show ∀ x y : ℂ, x * (C * y) = C * (x * y) by intros; ring, ← Complex.exp_add]
    congr 2
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hz : (z v : ℂ) = ((z v).re : ℂ) + ((z v).im : ℂ) * Complex.I := (Complex.re_add_im _).symm
    rw [hz]
    ring_nf
    rw [Complex.I_sq]
    ring
  have heval : ∀ ξ, (borelInf (bF b hb) (zRe z) (zSqrtIm z) (phiStd b)).eval ξ =
      (Set.range fun x : Fin (2 * m) → 𝓞 F => fun i => (x i : F)).indicator (fun ξ => C * term ξ) ξ := by
    intro ξ
    rw [GDatum.eval, hinf]
    show C * term ξ * ∏ᶠ v, oneV v (2 * m) (ιV v ξ) = _
    rw [finprod_oneV_eq]
    by_cases h : ∀ i, ξ i ∈ (algebraMap (𝓞 F) F).range
    · rw [if_pos h, mul_one, Set.indicator_of_mem]
      exact ⟨fun i => (h i).choose, funext fun i => (h i).choose_spec⟩
    · rw [if_neg h, mul_zero, Set.indicator_of_notMem]
      rintro ⟨x, rfl⟩
      exact h fun i => ⟨x i, rfl⟩
  have hinj : Function.Injective fun x : Fin (2 * m) → 𝓞 F => fun i => (x i : F) := by
    intro x y hxy
    funext i
    exact RingOfIntegers.coe_injective (congrFun hxy i)
  rw [thetaDist, tsum_congr heval, ← hinj.tsum_eq (Set.support_indicator_subset), HilbertModular.thetaQ,
    ← tsum_mul_left]
  refine tsum_congr fun x => ?_
  rw [Set.indicator_of_mem (Set.mem_range_self x)]
  congr 1
  simp only [term]
  congr 4
  funext v
  congr 3
  rw [eval_diag, Qform]
  simp [bF, map_sum, map_mul, map_pow]

end Bridge

end QuadFormsKB.WeilRep
