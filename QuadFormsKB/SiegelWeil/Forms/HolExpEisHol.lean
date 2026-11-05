/-
# Continuity and separate holomorphy of $\mathcal E^{(r)}$ in complex coordinates
**Layer:** archimedean, over a totally real number field $F$ of degree $d$.

**Setting.** $J$ = `JR F r`, $Z(t)$ = `zC t`, $K$ = `coneK F r` and $f = $ `fC b hb hbpos` $= \mathcal E^{(r)}\circ Z$ on the tube $\{x + iy : y \in K\}$
(`HolExpEisCoord`), with $m > 4r^2$ and $r \ge 1$. The Fourier-coefficient arguments of `HolExpTorus` need, for each $y \in K$, that
$x \mapsto f(x + iy)$ is continuous, and that $f$ is holomorphic in each single complex coordinate $t_i$ at every point of the tube.

**Results.**
* `isOpen_coneK`, `convex_coneK`, `smul_mem_coneK`: $K$ is an open convex cone (positive definiteness is an open condition on symmetric matrices,
  by compactness of the unit sphere);
* **`continuous_fC_slice`**: $x \mapsto f(x + iy)$ is continuous for $y \in K$;
* **`differentiableAt_fC_update`**: $s \mapsto f(t[i \mapsto s])$ is complex differentiable at $s = x_i + iy_i$ whenever $y \in K$.

*Proof.* Both are Weierstrass tests (`continuousOn_tsum`, `differentiableOn_tsum_of_summable_norm`) with the majorant `exists_holQ_majorant`,
uniform on the compact set of points $Z(\cdot)$ obtained from a closed ball of parameters. Every term is $j(\gamma, Z)^{-m}$ times a constant; $j$ is a
polynomial in the entries of $Z$ and does not vanish on $\mathbb H_r^d$.

Sources: Freitag, *Siegelsche Modulfunktionen* (1983), Ch. I [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.HolExpEisCoord
import QuadFormsKB.SiegelWeil.Forms.HolExpBound
import QuadFormsKB.SiegelWeil.Forms.EisensteinLowerCell

open Matrix NumberField Filter Topology
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep.Genus QuadFormsKB.SiegelWeil.Forms.HolExp

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {m r : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

/-! ### The cone $K$ is open, convex and stable under positive scaling -/

lemma xCoord_smul (c : ℝ) (t : JR F r → ℝ) (p : SymIdx r) : xCoord (c • t) p = c • xCoord t p := by
  unfold xCoord
  rw [← map_smul]
  rfl

lemma symOf_smul (c : ℝ) (u : SymIdx r → ℝ) : symOf (c • u) = c • symOf u := by
  ext i j; simp only [symOf, Matrix.smul_apply, of_apply, Pi.smul_apply]; split_ifs <;> rfl

lemma xMat_symm (t : JR F r → ℝ) (w : InfinitePlace F) : (xMat t w)ᵀ = xMat t w := symOf_transpose _

/-- For the symmetric matrices $X_w(y)$, positive definiteness is positivity of the quadratic form off $0$. -/
lemma posDef_xMat_iff (y : JR F r → ℝ) (w : InfinitePlace F) :
    (xMat y w).PosDef ↔ ∀ v : Fin r → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (xMat y w) *ᵥ v := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  have hH : (xMat y w).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact xMat_symm y w
  simp only [hH, true_and, star_trivial]

lemma isOpen_coneK : IsOpen (coneK F r) := by
  rw [isOpen_iff_mem_nhds]
  intro y₀ hy₀
  have key : ∀ w, ∀ᶠ y in 𝓝 y₀, (xMat y w).PosDef := by
    intro w
    have hc : Continuous fun p : (JR F r → ℝ) × (Fin r → ℝ) => p.2 ⬝ᵥ (xMat p.1 w) *ᵥ p.2 := by
      simp only [dotProduct, mulVec]
      refine continuous_finsetSum _ fun i _ => Continuous.mul (by fun_prop) ?_
      exact continuous_finsetSum _ fun j _ =>
        Continuous.mul ((continuous_xMat_apply w i j).comp continuous_fst) (by fun_prop)
    have hsph : IsCompact (Metric.sphere (0 : Fin r → ℝ) 1) := isCompact_sphere _ _
    have hev := hsph.eventually_forall_of_forall_eventually (x₀ := y₀)
      (P := fun y v => 0 < v ⬝ᵥ (xMat y w) *ᵥ v) fun v hv => by
        have hv0 : v ≠ 0 := by
          rintro rfl; simp at hv
        have h0 := (posDef_xMat_iff y₀ w).1 (hy₀ w) v hv0
        exact (hc.isOpen_preimage _ isOpen_Ioi).mem_nhds (show (y₀, v) ∈ _ from h0)
    refine hev.mono fun y hy => (posDef_xMat_iff y w).2 fun v hv => ?_
    have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
    have hu : ‖(‖v‖⁻¹) • v‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have h1 := hy _ (mem_sphere_zero_iff_norm.2 hu)
    rw [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at h1
    have hn2 : 0 < ‖v‖⁻¹ * ‖v‖⁻¹ := by positivity
    by_contra hneg
    push Not at hneg
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hn2.le hneg]
  exact (Filter.eventually_all.2 key).mono fun y hy => hy

lemma smul_mem_coneK {y : JR F r → ℝ} (hy : y ∈ coneK F r) {c : ℝ} (hc : 0 < c) : c • y ∈ coneK F r := by
  intro w
  have hy' := (posDef_xMat_iff y w).1 (hy w)
  refine (posDef_xMat_iff _ w).2 fun v hv => ?_
  have := hy' v hv
  rw [xMat_smul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  exact mul_pos hc this

lemma convex_coneK : Convex ℝ (coneK F r) := by
  rw [convex_iff_forall_pos]
  intro y hy z hz a b ha hb _ w
  have hy' := (posDef_xMat_iff y w).1 (hy w)
  have hz' := (posDef_xMat_iff z w).1 (hz w)
  refine (posDef_xMat_iff _ w).2 fun v hv => ?_
  rw [xMat_add, xMat_smul, xMat_smul, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.smul_mulVec,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  exact add_pos (mul_pos ha (hy' v hv)) (mul_pos hb (hz' v hv))

/-! ### Continuity on horizontal slices -/

lemma continuous_holTermR_zPt (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    {Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ} (hY : ∀ w, (Y w).PosDef) (γ : Sp r F) :
    Continuous fun t : JR F r → ℝ => holTermR b hb (zPt Y t) γ := by
  unfold holTermR
  refine Continuous.mul (Continuous.zpow₀ ?_ _ fun t => Or.inl ?_) continuous_const
  · unfold denR
    refine continuous_finsetProd _ fun w _ => ?_
    unfold denW
    exact ((continuous_const.matrix_mul (continuous_zPt_apply Y w)).add continuous_const).matrix_det
  · unfold denR
    exact Finset.prod_ne_zero_iff.mpr fun w _ => det_denW_ne_zero _ (zPt_mem_siegelHF Y hY t) w

/-- **Continuity on slices**: $x \mapsto f(x + iy)$ is continuous for $y \in K$. -/
theorem continuous_fC_slice (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) (hr : 1 ≤ r) (hm : 4 * (r : ℝ) ^ 2 < m)
    {y : JR F r → ℝ} (hy : y ∈ coneK F r) :
    Continuous fun x : JR F r → ℝ => fC b hb hbpos (HolExp.cplx x y) := by
  set Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ := fun w => xMat y w with hYdef
  have hY : ∀ w, (Y w).PosDef := hy
  have e : (fun x : JR F r → ℝ => fC b hb hbpos (HolExp.cplx x y)) =
      fun x => ∑' q, holQ b hb hbpos (zPt Y x) q := by
    funext x; rw [fC_cplx b hb hbpos x hy]; rfl
  rw [e, continuous_iff_continuousAt]
  intro x₀
  have hS : ∀ w, IsCompact ((fun t => zPt Y t w) '' Metric.closedBall x₀ 1) := fun w =>
    (isCompact_closedBall _ _).image (continuous_zPt_apply Y w)
  have hSH : ∀ w, (fun t => zPt Y t w) '' Metric.closedBall x₀ 1 ⊆ siegelH r := by
    rintro w _ ⟨t, -, rfl⟩; exact zPt_mem_siegelHF Y hY t w
  obtain ⟨M, G, hG, -, hmaj⟩ := exists_holQ_majorant b hb hbpos hr hm hS hSH
  have hcon : ContinuousOn (fun x => ∑' q, holQ b hb hbpos (zPt Y x) q) (Metric.closedBall x₀ 1) := by
    refine continuousOn_tsum (u := fun q => M * G q) (fun q => ?_) (hG.mul_left M)
      (fun q x hx => hmaj _ (fun w => ⟨x, hx, rfl⟩) q)
    have : (fun x => holQ b hb hbpos (zPt Y x) q) = fun x => holTermR b hb (zPt Y x) q.out :=
      funext fun x => holQ_eq_out b hb hbpos (zPt_mem_siegelHF Y hY x) q
    rw [this]
    exact (continuous_holTermR_zPt b hb hY _).continuousOn
  exact hcon.continuousAt (Metric.closedBall_mem_nhds x₀ one_pos)

/-! ### Holomorphy in one complex coordinate -/

lemma update_cplx (x y : JR F r → ℝ) (i : JR F r) (s : ℂ) :
    Function.update (HolExp.cplx x y) i s = HolExp.cplx (Function.update x i s.re) (Function.update y i s.im) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [HolExp.cplx]
  · simp [HolExp.cplx, hj]

lemma differentiable_det_denW (γ : Sp r F) (t : JR F r → ℂ) (i : JR F r) (v : InfinitePlace F) :
    Differentiable ℂ fun s : ℂ => (denW γ (zC (Function.update t i s)) v).det := by
  have hent : ∀ j k, Differentiable ℂ fun s : ℂ => denW γ (zC (Function.update t i s)) v j k := by
    intro j k
    simp only [denW, Matrix.add_apply, Matrix.mul_apply, zC_update, Matrix.map_apply, Matrix.smul_apply]
    fun_prop
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine Differentiable.fun_sum fun σ _ => ?_
  exact (differentiable_const _).mul (fun s => DifferentiableAt.fun_finsetProd fun l _ => hent _ _ s)

lemma continuous_zC_update (t : JR F r → ℂ) (i : JR F r) (w : InfinitePlace F) :
    Continuous fun s : ℂ => zC (Function.update t i s) w := by
  refine continuous_pi fun j => continuous_pi fun k => ?_
  simp only [zC_update, Matrix.add_apply, Matrix.smul_apply]
  fun_prop

/-- **Separate holomorphy**: for $y \in K$, $s \mapsto f(t[i \mapsto s])$, $t = x + iy$, is complex differentiable at $s = x_i + iy_i$. -/
theorem differentiableAt_fC_update (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) (hr : 1 ≤ r) (hm : 4 * (r : ℝ) ^ 2 < m)
    (x y : JR F r → ℝ) (hy : y ∈ coneK F r) (i : JR F r) :
    DifferentiableAt ℂ (fun s : ℂ => fC b hb hbpos (Function.update (HolExp.cplx x y) i s))
      ((x i : ℂ) + (y i : ℂ) * Complex.I) := by
  set t : JR F r → ℂ := HolExp.cplx x y with ht
  set s₀ : ℂ := (x i : ℂ) + (y i : ℂ) * Complex.I with hs₀
  have hU : IsOpen {s : ℂ | Function.update y i s.im ∈ coneK F r} :=
    isOpen_coneK.preimage (continuous_const.update i Complex.continuous_im)
  have hs₀U : s₀ ∈ {s : ℂ | Function.update y i s.im ∈ coneK F r} := by
    show Function.update y i s₀.im ∈ coneK F r
    have : s₀.im = y i := by simp [hs₀]
    rw [this, Function.update_eq_self]; exact hy
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU s₀ hs₀U
  have hmem : ∀ s ∈ Metric.ball s₀ ε, zC (Function.update t i s) ∈ siegelHF F r := by
    intro s hs
    rw [ht, update_cplx]
    exact zC_mem _ (hball hs)
  have hS : ∀ w, IsCompact ((fun s => zC (Function.update t i s) w) '' Metric.closedBall s₀ (ε / 2)) :=
    fun w => (isCompact_closedBall _ _).image (continuous_zC_update t i w)
  have hSH : ∀ w, (fun s => zC (Function.update t i s) w) '' Metric.closedBall s₀ (ε / 2) ⊆ siegelH r := by
    rintro w _ ⟨s, hs, rfl⟩
    exact hmem s (Metric.closedBall_subset_ball (by linarith) hs) w
  obtain ⟨M, G, hG, -, hmaj⟩ := exists_holQ_majorant b hb hbpos hr hm hS hSH
  have hF : DifferentiableOn ℂ (fun s => ∑' q, holQ b hb hbpos (zC (Function.update t i s)) q)
      (Metric.ball s₀ (ε / 2)) := by
    refine Complex.differentiableOn_tsum_of_summable_norm (u := fun q => M * G q) (hG.mul_left M) (fun q => ?_)
      Metric.isOpen_ball (fun q s hs => hmaj _ (fun w => ⟨s, Metric.ball_subset_closedBall hs, rfl⟩) q)
    have hball' : ∀ s ∈ Metric.ball s₀ (ε / 2), s ∈ Metric.ball s₀ ε := fun s hs =>
      Metric.ball_subset_ball (by linarith) hs
    have hden : DifferentiableOn ℂ (fun s => denR q.out (zC (Function.update t i s))) (Metric.ball s₀ (ε / 2)) := by
      unfold denR
      exact (show Differentiable ℂ fun s => ∏ v, (denW q.out (zC (Function.update t i s)) v).det from
        fun s => DifferentiableAt.fun_finsetProd fun v _ => differentiable_det_denW q.out t i v s).differentiableOn
    have hterm : DifferentiableOn ℂ (fun s => holTermR b hb (zC (Function.update t i s)) q.out)
        (Metric.ball s₀ (ε / 2)) := by
      unfold holTermR
      refine DifferentiableOn.mul (DifferentiableOn.zpow hden (Or.inl fun s hs => ?_)) (differentiableOn_const _)
      unfold denR
      exact Finset.prod_ne_zero_iff.mpr fun w _ => det_denW_ne_zero _ (hmem s (hball' s hs)) w
    refine hterm.congr fun s hs => ?_
    exact holQ_eq_out b hb hbpos (hmem s (hball' s hs)) q
  have hat : DifferentiableAt ℂ (fun s => ∑' q, holQ b hb hbpos (zC (Function.update t i s)) q) s₀ :=
    hF.differentiableAt (Metric.ball_mem_nhds _ (by linarith))
  refine hat.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds s₀ hε] with s hs
  unfold fC
  rw [if_pos (hmem s hs)]
  rfl

end QuadFormsKB.SiegelWeil.Forms
