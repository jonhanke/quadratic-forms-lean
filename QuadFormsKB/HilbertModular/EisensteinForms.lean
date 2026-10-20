/-
# Hilbert Eisenstein series III: holomorphy and constant terms at every cusp, $k \ge 3$

For an admissible weight $W$ (`EisWeight`) and $k \ge 3$:

* **holomorphy** (`isHolomorphic_eisSeries`): $E_{W,k}$ is continuous on $\mathbb{H}^d$ and holomorphic in each variable
  (Weierstrass M-test with the majorant of `exists_summable_bound`);
* **the constant term at $\infty$** (`tendsto_eisSeries_of_periodic`): if $E_{W,k}$ is periodic under translation by a
  fractional ideal $J$, then
  $$E_{W,k}(z) \longrightarrow \mathrm{c}_\infty(W) = \sum_{x \in U\backslash F^2,\ c = 0}W(0, d)\,N(d)^{-k}
    \qquad (\min_v\operatorname{Im}z_v \to \infty)$$
  (`eisConst`; the sum of the terms with $c = 0$). *Proof:* periodicity moves $\operatorname{Re}z$ into a fixed box
  (`tendsto_of_periodic`, using a fundamental domain of $J$); on the box the majorant is uniform, so dominated convergence
  applies termwise: terms with $c \ne 0$ tend to $0$ since $|\sigma_v(c)z_v + \sigma_v(d)| \ge |\sigma_v c|\operatorname{Im}z_v$
  (`tendsto_eisSeries_box`).
* **the constant term at every cusp** (`tendsto_eisSeries_slash`): if moreover $W$ has a level $\mathfrak M \ne 0$
  ($W(y\gamma^{-1}) = W(y)$ for $\gamma \in \Gamma(\mathfrak M)$, `HasLevel`), then for every $A \in \mathrm{SL}_2(F)$, i.e. at the cusp
  $A\infty = A_{00}/A_{10}$,
  $$(E_{W,k}\,|_k\,A)(z) \longrightarrow \mathrm{c}_\infty(W_A) = \sum_{y \in U\backslash F^2,\ y_0 = 0}W(yA^{-1})\,N(y_1)^{-k},$$
  because $E_{W,k}|A = E_{W_A,k}$ (`eisSeries_slash`) and $E_{W_A,k}$ is periodic ($A\,T(\beta)A^{-1} \in \Gamma(\mathfrak M)$ for
  $\beta$ in a fractional ideal, `koecher_cusp_hyp_of_GammaFull_le`). In particular $E_{W,k}|A$ is bounded at $\infty$ for every
  $A$, for **every** degree $d \ge 1$ (no Koecher principle needed), and $E_{W,k} \in M_k(\Gamma(\mathfrak M))$
  (`eisSeries_mem_modularFormSpace`).

Sources: Freitag (1990), Ch. I §5 [unverified]; Garrett (1990), Ch. 3 [unverified]; Shimura (Duke 1978), §3 [unverified].
-/
import QuadFormsKB.HilbertModular.EisensteinConv

open Complex Matrix NumberField UpperHalfPlane Filter Topology
open scoped MatrixGroups ModularForm nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-! ### Continuity and holomorphy -/

lemma eisDen_ne_zero {x : F × F} (hx : x ≠ 0) {Z : InfinitePlace F → ℂ} (hZ : ∀ v, 0 < (Z v).im) :
    eisDen x Z ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun v _ => ?_
  by_cases hc : realEmb F v x.1 = 0
  · have hc' : x.1 = 0 := (map_eq_zero_iff _ (realEmb_injective F v)).mp hc
    have hd : x.2 ≠ 0 := fun hd => hx (Prod.ext hc' hd)
    rw [hc, ofReal_zero, zero_mul, zero_add, ofReal_ne_zero]
    exact (map_ne_zero_iff _ (realEmb_injective F v)).mpr hd
  · intro h
    have := congrArg Complex.im h
    simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, zero_im] at this
    exact (mul_ne_zero hc (hZ v).ne') this

lemma continuous_eisDen (x : F × F) :
    Continuous fun z : InfinitePlace F → ℍ => eisDen x fun v => (z v : ℂ) := by
  unfold eisDen
  have : ∀ v : InfinitePlace F, Continuous fun z : InfinitePlace F → ℍ => ((z v : ℍ) : ℂ) :=
    fun v => UpperHalfPlane.continuous_coe.comp (continuous_apply v)
  fun_prop

lemma continuous_eisTerm (W : F × F → ℂ) (k : ℤ) (x : F × F) :
    Continuous fun z : InfinitePlace F → ℍ => eisTerm W k x fun v => (z v : ℂ) := by
  by_cases hx : x = 0
  · subst hx; simp only [eisTerm, eisDen_zero]; exact continuous_const
  · refine continuous_const.mul ((continuous_eisDen x).zpow₀ _ fun z => Or.inl ?_)
    exact eisDen_ne_zero hx fun v => (z v).im_pos

lemma exists_strip_nhds (z0 : InfinitePlace F → ℍ) : ∃ A B : ℝ, 0 < B ∧
    {z : InfinitePlace F → ℍ | ∀ v, |(z v).re| < A ∧ B < (z v).im} ∈ 𝓝 z0 := by
  obtain ⟨B, hB, hBz⟩ := exists_pos_lt_min (y := imVec z0) (imVec_pos z0)
  refine ⟨∑ v, |(z0 v).re| + 1, B, hB, IsOpen.mem_nhds ?_ fun v => ⟨?_, hBz v⟩⟩
  · rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun v => (isOpen_lt (continuous_abs.comp
      (UpperHalfPlane.continuous_re.comp (continuous_apply v))) continuous_const).inter
        (isOpen_lt continuous_const (UpperHalfPlane.continuous_im.comp (continuous_apply v)))
  · have := Finset.single_le_sum (f := fun v => |(z0 v).re|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ v)
    linarith

lemma mem_verticalStrip_of {z : ℍ} {A B : ℝ} (h : |z.re| < A ∧ B < z.im) : z ∈ verticalStrip A B :=
  ⟨h.1.le, h.2.le⟩

/-- **$E_{W,k}$ is continuous** ($k \ge 3$). -/
theorem continuous_eisSeries {W : F × F → ℂ} {k : ℤ} (hW : EisWeight W k) (hk : 3 ≤ k) :
    Continuous (eisSeries W k) := by
  rw [continuous_iff_continuousAt]
  intro z0
  obtain ⟨A, B, hB, hU⟩ := exists_strip_nhds z0
  obtain ⟨h, hs, hb⟩ := exists_summable_bound hW hk A hB
  have hc : ContinuousOn (eisSeries W k)
      {z : InfinitePlace F → ℍ | ∀ v, |(z v).re| < A ∧ B < (z v).im} :=
    continuousOn_tsum (fun o => (continuous_eisTerm W k _).continuousOn) hs
      fun o z hz => hb z (fun v => mem_verticalStrip_of (hz v)) o
  exact hc.continuousAt hU

lemma differentiable_eisDen_update [DecidableEq (InfinitePlace F)] (x : F × F)
    (Z : InfinitePlace F → ℂ) (v : InfinitePlace F) :
    Differentiable ℂ fun w : ℂ => eisDen x (Function.update Z v w) := by
  unfold eisDen
  have := differentiable_update_apply' Z v
  fun_prop
where
  differentiable_update_apply' (Z : InfinitePlace F → ℂ) (v : InfinitePlace F) :
      ∀ u, Differentiable ℂ fun w : ℂ => Function.update Z v w u := by
    intro u
    by_cases h : u = v
    · subst h; simp
    · simp [Function.update_of_ne h]

lemma update_coe_eq [DecidableEq (InfinitePlace F)] (z : InfinitePlace F → ℍ) (v : InfinitePlace F)
    {w : ℂ} (hw : 0 < w.im) :
    Function.update (fun u => (z u : ℂ)) v w =
      fun u => ((Function.update z v (UpperHalfPlane.ofComplex w) u : ℍ) : ℂ) := by
  funext u
  by_cases h : u = v
  · subst h; simp [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  · simp [Function.update_of_ne h]

/-- **$E_{W,k}$ is holomorphic on $\mathbb{H}^d$** ($k \ge 3$): continuous, and holomorphic in each variable. -/
@[kb "freitag1990" "Ch. I §5, Eisenstein series are holomorphic [unverified]"]
theorem isHolomorphic_eisSeries {W : F × F → ℂ} {k : ℤ} (hW : EisWeight W k) (hk : 3 ≤ k) :
    IsHolomorphic (eisSeries W k) := by
  classical
  refine ⟨continuous_eisSeries hW hk, fun z v => ?_⟩
  rw [UpperHalfPlane.mdifferentiable_iff]
  set Z : InfinitePlace F → ℂ := fun u => (z u : ℂ)
  set g : ℂ → ℂ := fun w => eisSeriesC W k (Function.update Z v w)
  have hg : DifferentiableOn ℂ g {w | 0 < w.im} := by
    intro w0 hw0
    have hw0' : 0 < w0.im := hw0
    obtain ⟨δ, hδ, hδz⟩ := exists_pos_lt_min (y := imVec z) (imVec_pos z)
    set B := min δ (w0.im / 2)
    have hB : 0 < B := lt_min hδ (by linarith)
    set A := |w0.re| + ∑ u, |(z u).re| + 1
    set U : Set ℂ := {w | |w.re| < A ∧ B < w.im}
    have hUo : IsOpen U := (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im)
    have hA0 : 0 ≤ ∑ u, |(z u).re| := Finset.sum_nonneg fun u _ => abs_nonneg _
    have hw0U : w0 ∈ U := by
      refine ⟨?_, ?_⟩
      · show |w0.re| < A; simp only [A]; linarith
      · show B < w0.im; exact (min_le_right _ _).trans_lt (by linarith)
    obtain ⟨h, hs, hb⟩ := exists_summable_bound hW hk A hB
    have hD : DifferentiableOn ℂ g U := by
      refine differentiableOn_tsum_of_summable_norm hs (fun o => ?_) hUo fun o w hw => ?_
      · by_cases hx : o.out = 0
        · simp only [eisTerm, hx, eisDen_zero]; exact differentiableOn_const _
        · refine DifferentiableOn.mul (differentiableOn_const _) ?_
          refine ((differentiable_eisDen_update _ Z v).differentiableOn).zpow (Or.inl fun w hw => ?_)
          refine eisDen_ne_zero hx fun u => ?_
          by_cases h : u = v
          · subst h; simp only [Function.update_self]; exact hB.trans hw.2
          · simp [Function.update_of_ne h, Z, (z u).im_pos]
      · have hwpos : 0 < w.im := hB.trans hw.2
        rw [update_coe_eq z v hwpos]
        refine hb _ (fun u => ?_) o
        by_cases h : u = v
        · subst h
          simp only [Function.update_self]
          refine ⟨?_, ?_⟩
          · rw [UpperHalfPlane.ofComplex_apply_of_im_pos hwpos]; exact hw.1.le
          · rw [UpperHalfPlane.ofComplex_apply_of_im_pos hwpos]; exact hw.2.le
        · simp only [Function.update_of_ne h]
          refine ⟨?_, (min_le_left _ _).trans (hδz u).le⟩
          have := Finset.single_le_sum (f := fun u => |(z u).re|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ u)
          simp only [A]; linarith [abs_nonneg w0.re]
    exact (hD.differentiableAt (hUo.mem_nhds hw0U)).differentiableWithinAt
  refine hg.congr fun w hw => ?_
  simp only [Function.comp_apply, eisSeries, g]
  rw [update_coe_eq z v hw]

/-! ### Periodicity and the constant term at $\infty$ -/

open Classical in
/-- **The constant term of $E_{W,k}$ at $\infty$**:
$\mathrm{c}_\infty(W) = \sum_{o \in U\backslash F^2}[c_o = 0]\,W(x_o)\,N(d_o)^{-k}$, $x_o = (c_o, d_o)$ the representative of $o$
(the terms of $E_{W,k}$ with $c = 0$, which do not depend on $z$). -/
@[kb "freitag1990" "Ch. I §5, constant term of the Eisenstein series [unverified]"]
noncomputable def eisConst (W : F × F → ℂ) (k : ℤ) : ℂ :=
  ∑' o : UOrbit F, if o.out.1 = 0 then W o.out * (∏ v, (realEmb F v o.out.2 : ℂ)) ^ (-k) else 0

/-- Translation of $z \in \mathbb{H}^\iota$ by $\sigma(\beta)$, $\beta \in F$. -/
noncomputable def translH (β : F) (z : InfinitePlace F → ℍ) : InfinitePlace F → ℍ :=
  fun v => (realEmb F v β) +ᵥ z v

/-- $f\,|_k\,T(\beta)$ is $z \mapsto f(z + \beta)$. -/
lemma slash_transl_apply (k : ℤ) (f : (InfinitePlace F → ℍ) → ℂ) (β : F) (z : InfinitePlace F → ℍ) :
    (f ∣[k] slHom (realEmb F) (transl β)) z = f (translH β z) := by
  rw [slash_apply]
  have hprod : ∏ v, (((((slHom (realEmb F) (transl β) v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ).det.val ^
      (k - 1) : ℝ)) : ℂ) * denom ((slHom (realEmb F) (transl β) v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ)
        (z v) ^ (-k) = 1 := by
    refine Finset.prod_eq_one fun v _ => ?_
    rw [slHom_det, _root_.one_zpow, ofReal_one, one_mul]
    simp [denom]
  rw [hprod, mul_one]
  congr 1
  funext v
  apply UpperHalfPlane.ext
  rw [Pi.smul_apply', glPos_smul_eq, coe_smul_of_det_pos (det_glPos_pos _)]
  simp [num, denom, translH, add_comm]

/-- An element of the $\mathbb{Z}$-span of the lattice basis of $J$ is $\sigma(\beta)$ for some $\beta \in J$. -/
lemma exists_realVec_eq_floor (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (x : InfinitePlace F → ℝ) :
    ∃ β ∈ (J : FractionalIdeal (𝓞 F)⁰ F), (ZSpan.floor (koecherBasis J) x : InfinitePlace F → ℝ) =
      realVec β := by
  refine ⟨QuadFormsKB.Analysis.latElt J fun j => ⌊(koecherBasis J).repr x j⌋, latElt_mem J _, ?_⟩
  rw [← koecherBasis_symm]
  apply (koecherBasis J).equivFun.injective
  funext j
  rw [LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply, ZSpan.repr_floor_apply]

/-- **Periodicity reduces the limit at $\infty$ to a box**: if $g(z + \beta) = g(z)$ for $\beta \in J$ and, for every $R$,
$g \to a$ along $\{\operatorname{Im}z_v \to \infty\} \cap \{|\operatorname{Re}z_v| \le R\}$, then $g \to a$ at $\infty$. -/
theorem tendsto_of_periodic (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) {g : (InfinitePlace F → ℍ) → ℂ} {a : ℂ}
    (hper : ∀ β ∈ (J : FractionalIdeal (𝓞 F)⁰ F), ∀ z, g (translH β z) = g z)
    (h : ∀ R : ℝ, Tendsto g (atImInftyPi ⊓ 𝓟 {z | ∀ v, |(z v).re| ≤ R}) (𝓝 a)) :
    Tendsto g atImInftyPi (𝓝 a) := by
  set b := koecherBasis J
  set R := ∑ j, ‖b j‖
  choose β hβJ hβ using fun z : InfinitePlace F → ℍ => exists_realVec_eq_floor J (reVec z)
  set s : (InfinitePlace F → ℍ) → (InfinitePlace F → ℍ) := fun z => translH (-β z) z
  have hgs : g ∘ s = g := by
    funext z
    have hneg : -β z ∈ (J : FractionalIdeal (𝓞 F)⁰ F) := by
      have := hβJ z
      rw [← FractionalIdeal.mem_coe] at this ⊢
      exact Submodule.neg_mem _ this
    exact hper _ hneg z
  have hs : Tendsto s atImInftyPi (atImInftyPi ⊓ 𝓟 {z | ∀ v, |(z v).re| ≤ R}) := by
    refine tendsto_inf.mpr ⟨?_, tendsto_principal.mpr (Eventually.of_forall fun z v => ?_)⟩
    · refine tendsto_iInf.mpr fun v => tendsto_comap_iff.mpr ?_
      have : (fun z => (s z v).im) = fun z => (z v).im := by
        funext z; simp [s, translH]
      rw [Function.comp_def, this]
      exact tendsto_comap.mono_left (iInf_le _ v)
    · have hf := ZSpan.norm_fract_le b (reVec z)
      rw [ZSpan.fract_apply, hβ z] at hf
      have hv := (norm_le_pi_norm (reVec z - realVec (β z)) v).trans hf
      simpa [s, translH, reVec, realVec, Real.norm_eq_abs, sub_eq_add_neg, add_comm] using hv
  rw [← hgs]
  exact (h R).comp hs

/-- The terms with $c \ne 0$ tend to $0$ at $\infty$. -/
lemma tendsto_eisTerm_of_fst_ne_zero {W : F × F → ℂ} {n : ℕ} (hn : n ≠ 0) {x : F × F} (hx : x.1 ≠ 0) :
    Tendsto (fun z : InfinitePlace F → ℍ => eisTerm W (n : ℤ) x fun v => (z v : ℂ)) atImInftyPi
      (𝓝 0) := by
  classical
  set c := ∏ v, |realEmb F v x.1|
  have hc : 0 < c := Finset.prod_pos fun v _ =>
    abs_pos.mpr ((map_ne_zero_iff _ (realEmb_injective F v)).mpr hx)
  -- `∏ Im z_v → ∞`
  have hP : Tendsto (fun z : InfinitePlace F → ℍ => ∏ v, (z v).im) atImInftyPi atTop := by
    refine tendsto_atTop.mpr fun T => ?_
    filter_upwards [eventually_im_ge (ι := InfinitePlace F) (max T 1)] with z hz
    obtain ⟨v₀⟩ : Nonempty (InfinitePlace F) := inferInstance
    have h1 : ∀ v, 1 ≤ (z v).im := fun v => (le_max_right _ _).trans (hz v)
    calc T ≤ (z v₀).im := (le_max_left _ _).trans (hz v₀)
      _ ≤ ∏ v, (z v).im := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v₀)]
        refine le_mul_of_one_le_right (zero_le_one.trans (h1 v₀)) ?_
        calc (1 : ℝ) = ∏ _v ∈ Finset.univ.erase v₀, (1 : ℝ) := by simp
          _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun v _ => h1 v
  have hlow : ∀ z : InfinitePlace F → ℍ, c * ∏ v, (z v).im ≤ ‖eisDen x fun v => (z v : ℂ)‖ := by
    intro z
    rw [eisDen, norm_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun v _ => mul_nonneg (abs_nonneg _) (z v).im_pos.le) fun v _ => ?_
    refine le_trans (le_of_eq ?_) (Complex.abs_im_le_norm _)
    simp [abs_mul, abs_of_pos (z v).im_pos]
  have hT : Tendsto (fun z : InfinitePlace F → ℍ => ((c * ∏ v, (z v).im) ^ n)⁻¹) atImInftyPi (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop hn).comp (hP.const_mul_atTop hc))
  refine squeeze_zero_norm' ?_ (hT.const_mul ‖W x‖ |>.congr' (Eventually.of_forall fun _ => rfl)
    |> fun h => by simpa using h)
  filter_upwards [eventually_im_ge (ι := InfinitePlace F) 1] with z hz
  have hpos : 0 < c * ∏ v, (z v).im := mul_pos hc (Finset.prod_pos fun v _ => (z v).im_pos)
  rw [eisTerm, norm_mul, _root_.zpow_neg, zpow_natCast, norm_inv, norm_pow]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos hpos n) (pow_le_pow_left₀ hpos.le (hlow z) n))
    (norm_nonneg _)

/-- **Dominated convergence on a box**: along $\{\operatorname{Im}z_v \to \infty\} \cap \{|\operatorname{Re}z_v| \le R\}$,
$E_{W,k} \to \mathrm{c}_\infty(W)$ ($k \ge 3$). -/
theorem tendsto_eisSeries_box {W : F × F → ℂ} {k : ℤ} (hW : EisWeight W k) (hk : 3 ≤ k) (R : ℝ) :
    Tendsto (eisSeries W k) (atImInftyPi ⊓ 𝓟 {z | ∀ v, |(z v).re| ≤ R}) (𝓝 (eisConst W k)) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n := ⟨k.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hn : n ≠ 0 := by omega
  obtain ⟨h, hs, hb⟩ := exists_summable_bound hW hk R one_pos
  refine tendsto_tsum_of_dominated_convergence hs (fun o => ?_) ?_
  · by_cases h1 : o.out.1 = 0
    · simp only [h1, ↓reduceIte]
      have : (fun z : InfinitePlace F → ℍ => eisTerm W (n : ℤ) o.out fun v => (z v : ℂ)) =
          fun _ => W o.out * (∏ v, (realEmb F v o.out.2 : ℂ)) ^ (-(n : ℤ)) := by
        funext z; simp [eisTerm, eisDen, h1]
      rw [this]; exact tendsto_const_nhds
    · simp only [h1, ↓reduceIte]
      exact (tendsto_eisTerm_of_fst_ne_zero hn h1).mono_left inf_le_left
  · have h1 : ∀ᶠ z in atImInftyPi ⊓ 𝓟 {z : InfinitePlace F → ℍ | ∀ v, |(z v).re| ≤ R},
        ∀ v, 1 ≤ (z v).im := mem_inf_of_left (eventually_im_ge 1)
    have h2 : ∀ᶠ z in atImInftyPi ⊓ 𝓟 {z : InfinitePlace F → ℍ | ∀ v, |(z v).re| ≤ R},
        ∀ v, |(z v).re| ≤ R := mem_inf_of_right (mem_principal_self _)
    filter_upwards [h1, h2] with z hz1 hz2 o
    exact hb z (fun v => ⟨hz2 v, hz1 v⟩) o

/-- **The constant term at $\infty$ of a periodic Eisenstein series** ($k \ge 3$): if $E_{W,k}(z + \beta) = E_{W,k}(z)$ for
$\beta \in J$, then $E_{W,k} \to \mathrm{c}_\infty(W)$ as $\min_v\operatorname{Im}z_v \to \infty$. -/
theorem tendsto_eisSeries_of_periodic {W : F × F → ℂ} {k : ℤ} (hW : EisWeight W k) (hk : 3 ≤ k)
    (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (hper : ∀ β ∈ (J : FractionalIdeal (𝓞 F)⁰ F), ∀ z, eisSeries W k (translH β z) = eisSeries W k z) :
    Tendsto (eisSeries W k) atImInftyPi (𝓝 (eisConst W k)) :=
  tendsto_of_periodic J hper (tendsto_eisSeries_box hW hk)

/-! ### Transformed weights and levels -/

/-- **$W_A$ is admissible** for every $A \in \mathrm{SL}_2(F)$: if $W$ is supported on $I^2$, then $W_A$ is supported on
$(D^{-1}I)^2$ for a common denominator $D$ of the entries of $A$. -/
theorem EisWeight.slash {W : F × F → ℂ} {k : ℤ} (hW : EisWeight W k) (A : SL(2, F)) :
    EisWeight (slashWeight W A) k := by
  refine ⟨hW.unit.slashWeight A, ?_, ?_⟩
  · obtain ⟨I, hI⟩ := hW.supp
    obtain ⟨D, hD, he⟩ := exists_denom A
    choose e he using he
    have hDF : algebraMap (𝓞 F) F D ≠ 0 := by
      rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
    have hS : FractionalIdeal.spanSingleton (𝓞 F)⁰ (algebraMap (𝓞 F) F D)⁻¹ ≠ 0 := by
      rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact inv_ne_zero hDF
    refine ⟨Units.mk0 _ hS * I, fun y hy => ?_⟩
    have hx := hI _ hy
    set x := rowMul y A⁻¹
    have hyx : y = rowMul x A := (rowMul_inv_rowMul y A).symm
    have key : ∀ (p q : F), p ∈ (I : FractionalIdeal (𝓞 F)⁰ F) → q ∈ (I : FractionalIdeal (𝓞 F)⁰ F) →
        ∀ i j : Fin 2, p * A 0 j + q * A 1 j ∈
          ((Units.mk0 _ hS * I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) := by
      intro p q hp hq _ j
      have hmem : algebraMap (𝓞 F) F D * (p * A 0 j + q * A 1 j) ∈ (I : FractionalIdeal (𝓞 F)⁰ F) := by
        have : algebraMap (𝓞 F) F D * (p * A 0 j + q * A 1 j) =
            e 0 j • p + e 1 j • q := by
          rw [Algebra.smul_def, Algebra.smul_def, he, he]; ring
        rw [this]
        rw [← FractionalIdeal.mem_coe] at hp hq ⊢
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ hp) (Submodule.smul_mem _ _ hq)
      have : p * A 0 j + q * A 1 j =
          (algebraMap (𝓞 F) F D)⁻¹ * (algebraMap (𝓞 F) F D * (p * A 0 j + q * A 1 j)) := by
        field_simp
      rw [this, Units.val_mul, Units.val_mk0]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hmem
    rw [hyx]
    exact ⟨key _ _ hx.1 hx.2 0 0, key _ _ hx.1 hx.2 0 1⟩
  · obtain ⟨B, hB⟩ := hW.bdd
    exact ⟨B, fun y => hB _⟩

/-- **A level for a weight**: $W(y\gamma^{-1}) = W(y)$ for all $\gamma$ in the principal congruence subgroup $\Gamma(\mathfrak M)$. -/
def HasLevel (W : F × F → ℂ) (𝔐 : Ideal (𝓞 F)) : Prop :=
  ∀ γ ∈ GammaFull 𝔐, slashWeight W γ = W

/-- With a level, $E_{W,k}$ is $\Gamma(\mathfrak M)$-invariant. -/
lemma eisSeries_slash_of_hasLevel {W : F × F → ℂ} {k : ℤ} (hW : IsUnitEquivariant W k)
    {𝔐 : Ideal (𝓞 F)} (hlev : HasLevel W 𝔐) {γ : SL(2, F)} (hγ : γ ∈ GammaFull 𝔐) :
    eisSeries W k ∣[k] slHom (realEmb F) γ = eisSeries W k := by
  rw [eisSeries_slash hW, hlev γ hγ]

/-- **$E_{W,k}|A$ is periodic** under translations by a fractional ideal (depending on $A$), for a weight with a level. -/
lemma exists_periodic_slash {W : F × F → ℂ} {k : ℤ} (hW : IsUnitEquivariant W k) {𝔐 : Ideal (𝓞 F)}
    (h𝔐 : 𝔐 ≠ ⊥) (hlev : HasLevel W 𝔐) (A : SL(2, F)) :
    ∃ J : (FractionalIdeal (𝓞 F)⁰ F)ˣ, ∀ β ∈ (J : FractionalIdeal (𝓞 F)⁰ F), ∀ z,
      (eisSeries W k ∣[k] slHom (realEmb F) A) (translH β z) =
        (eisSeries W k ∣[k] slHom (realEmb F) A) z := by
  obtain ⟨J, -, -, hJ, -⟩ := koecher_cusp_hyp_of_GammaFull_le 𝔐 h𝔐 le_rfl A
  refine ⟨J, fun β hβ z => ?_⟩
  rw [← slash_transl_apply k (eisSeries W k ∣[k] slHom (realEmb F) A) β z, ← SlashAction.slash_mul,
    ← map_mul]
  have : A * transl β = (A * transl β * A⁻¹) * A := by group
  rw [this, map_mul, SlashAction.slash_mul, eisSeries_slash_of_hasLevel hW hlev (hJ β hβ)]

/-- **The constant term of $E_{W,k}$ at every cusp** ($k \ge 3$): for $A \in \mathrm{SL}_2(F)$ (the cusp $A\infty$),
$$\lim_{\min_v\operatorname{Im}z_v\to\infty}(E_{W,k}\,|_k\,A)(z) = \mathrm{c}_\infty(W_A)
  = \sum_{o \in U\backslash F^2}[y_{o,0} = 0]\,W(y_oA^{-1})\,N(y_{o,1})^{-k},$$
for an admissible weight $W$ with a level $\mathfrak M \ne 0$. -/
@[kb "freitag1990" "Ch. I §5, constant terms of Eisenstein series at the cusps [unverified]"]
theorem tendsto_eisSeries_slash {W : F × F → ℂ} {k : ℤ} (hW : EisWeight W k) (hk : 3 ≤ k)
    {𝔐 : Ideal (𝓞 F)} (h𝔐 : 𝔐 ≠ ⊥) (hlev : HasLevel W 𝔐) (A : SL(2, F)) :
    Tendsto (eisSeries W k ∣[k] slHom (realEmb F) A) atImInftyPi
      (𝓝 (eisConst (slashWeight W A) k)) := by
  obtain ⟨J, hJ⟩ := exists_periodic_slash hW.unit h𝔐 hlev A
  rw [eisSeries_slash hW.unit A] at hJ ⊢
  exact tendsto_eisSeries_of_periodic (hW.slash A) hk J hJ

/-- **$E_{W,k}$ is a Hilbert modular form for $\Gamma(\mathfrak M)$** ($k \ge 3$, any degree $d \ge 1$): holomorphic,
$\Gamma(\mathfrak M)$-invariant, and bounded at every cusp (it has a limit there, `tendsto_eisSeries_slash`). -/
@[kb "freitag1990" "Ch. I §5, Eisenstein series are modular forms [unverified]"]
theorem eisSeries_mem_modularFormSpace {W : F × F → ℂ} {k : ℤ} (hW : EisWeight W k) (hk : 3 ≤ k)
    {𝔐 : Ideal (𝓞 F)} (h𝔐 : 𝔐 ≠ ⊥) (hlev : HasLevel W 𝔐) :
    eisSeries W k ∈ HMF F (GammaFull 𝔐) k := by
  refine ⟨fun γ hγ => eisSeries_slash_of_hasLevel hW.unit hlev hγ, isHolomorphic_eisSeries hW hk,
    fun A => ?_⟩
  exact (tendsto_eisSeries_slash hW hk h𝔐 hlev A).isBigO_one ℝ

end QuadFormsKB.HilbertModular
