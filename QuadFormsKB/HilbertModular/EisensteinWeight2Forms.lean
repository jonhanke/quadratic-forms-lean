/-
# Hilbert Eisenstein series IX: parallel weight 2 as Hilbert modular forms, $d \ge 2$

For an integral weight $W$ of weight $2$ and $d \ge 2$ (`eis2`, the Hecke limit `tendsto_heckeSeries_two`):

* `eis2_slash_of_weight`: if $W(yA^{-1}) = \lambda W(y)$ for $A \in \mathrm{SL}_2(F)$, then $E_{W,2}\,|_2\,A = \lambda E_{W,2}$ (take $s \to 0$ in the
  exact transformation law `heckeSeries_smul` of $H_{W,2}(\cdot, s)$; the factor $|N(j(A, z))|^{2s} \to 1$);
* `eis2_eq_osc`, `isHolomorphic_eis2`: $E_{W,2} = \mathrm{c}_\infty(W) + \sum_{t,\ \nu\ne0}(\dots)e(\operatorname{Tr}\tilde t\nu z)$ is holomorphic
  (locally uniform convergence, `heckeMaj`);
* `tendsto_eis2_atImInfty`: $E_{W,2} \to \mathrm{c}_\infty(W)$ at $\infty$;
* `eis2Char_mem_modularFormChar`: for $W = W_\chi$, $E_{2,\chi} \in M_2(\Gamma_0(\mathfrak N), \chi)$ (cusp conditions by Koecher's principle).
-/
import QuadFormsKB.HilbertModular.EisensteinWeight2

open Complex Matrix NumberField UpperHalfPlane Filter Topology MeasureTheory Set
open scoped MatrixGroups ModularForm nonZeroDivisors Real

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

lemma heckeSeries_smul_weight (W : F × F → ℂ) (k : ℕ) (s : ℝ) (c : ℂ) (z : InfinitePlace F → ℍ) :
    heckeSeries (c • W) k s z = c * heckeSeries W k s z := by
  rw [heckeSeries, heckeSeries, ← tsum_mul_left]
  refine tsum_congr fun o => ?_
  simp only [heckeTerm, Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- **The transformation law in weight 2**: if $W_A = \lambda W$ then $E_{W,2}\,|_2\,A = \lambda E_{W,2}$ ($d \ge 2$). -/
@[kb "shimura1978" "§3, transformation law of the weight-2 Eisenstein series [unverified]"]
theorem eis2_slash_of_weight (hd : 2 ≤ Fintype.card (InfinitePlace F)) {W : F × F → ℂ}
    {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W 2 𝔐) (A : SL(2, F)) {c : ℂ}
    (hA : slashWeight W A = c • W) :
    eis2 W 𝔐 hW.ne ∣[(2 : ℤ)] slHom (realEmb F) A = c • eis2 W 𝔐 hW.ne := by
  funext z
  rw [slash_apply, Pi.smul_apply, smul_eq_mul]
  set j : InfinitePlace F → ℂ := fun v => denom ((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v)
  have hj : ∀ v, j v ≠ 0 := fun v => denom_ne_zero _ _
  have hfac : ∏ v, ((((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ).det.val ^ ((2 : ℤ) - 1) : ℝ) : ℂ) *
      denom ((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v) ^ (-(2 : ℤ)) =
      ∏ v, (j v ^ 2)⁻¹ := by
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [slHom_det, _root_.one_zpow, ofReal_one, one_mul, _root_.zpow_neg, zpow_ofNat]
  rw [hfac]
  -- both sides are limits of the same Hecke series
  have h1 := (tendsto_heckeSeries_two hd hW (slHom (realEmb F) A • z)).mul_const (∏ v, (j v ^ 2)⁻¹)
  have h2 : Tendsto (fun s : ℝ => (∏ v, (((‖j v‖ ^ (2 * s) : ℝ)) : ℂ)) * (c * heckeSeries W 2 s z))
      (𝓝[>] 0) (𝓝 ((∏ v, (((‖j v‖ ^ (2 * (0 : ℝ)) : ℝ)) : ℂ)) * (c * eis2 W 𝔐 hW.ne z))) := by
    refine Tendsto.mul ?_ ((tendsto_heckeSeries_two hd hW z).const_mul c)
    refine tendsto_finset_prod _ fun v _ => ?_
    have : Continuous fun s : ℝ => ((‖j v‖ ^ (2 * s) : ℝ) : ℂ) :=
      continuous_ofReal.comp (continuous_const.rpow (by fun_prop) fun _ =>
        Or.inl (norm_ne_zero_iff.mpr (hj v)))
    exact (this.tendsto 0).mono_left nhdsWithin_le_nhds
  simp only [mul_zero, Real.rpow_zero, ofReal_one, Finset.prod_const_one, one_mul] at h2
  have heq : ∀ s : ℝ, heckeSeries W 2 s (slHom (realEmb F) A • z) * ∏ v, (j v ^ 2)⁻¹ =
      (∏ v, (((‖j v‖ ^ (2 * s) : ℝ)) : ℂ)) * (c * heckeSeries W 2 s z) := by
    intro s
    have := heckeSeries_smul hW.unit s A z
    rw [hA, heckeSeries_smul_weight] at this
    exact this
  simp_rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

/-! ### Series of exponentials $e(\langle\mu, z\rangle)$ -/

section QSeries

variable {ι : Type*} [Fintype ι] {α : Type*}

/-- $Z \mapsto e(\sum_v\mu_vZ_v)$ on $\mathbb{C}^\iota$. -/
noncomputable def qTermC (μ : ι → ℝ) (Z : ι → ℂ) : ℂ := cexp (2 * π * Complex.I * ∑ v, (μ v : ℂ) * Z v)

lemma qTerm_eq_qTermC (μ : ι → ℝ) (z : ι → ℍ) : qTerm μ z = qTermC μ fun v => (z v : ℂ) := rfl

/-- **A locally uniformly dominated series of exponentials is holomorphic.** -/
theorem isHolomorphic_tsum_qTerm (a : α → ℂ) (μ : α → ι → ℝ)
    (hdom : ∀ y₀ : ℝ, 0 < y₀ → ∃ g : α → ℝ, Summable g ∧ ∀ z : ι → ℍ, (∀ v, y₀ ≤ (z v).im) →
      ∀ p, ‖a p * qTerm (μ p) z‖ ≤ g p) :
    IsHolomorphic (fun z => ∑' p, a p * qTerm (μ p) z) := by
  classical
  have hcont_term : ∀ p, Continuous fun z : ι → ℍ => a p * qTerm (μ p) z := by
    intro p
    unfold qTerm
    have : ∀ v : ι, Continuous fun z : ι → ℍ => ((z v : ℍ) : ℂ) :=
      fun v => UpperHalfPlane.continuous_coe.comp (continuous_apply v)
    fun_prop
  refine ⟨?_, fun z v => ?_⟩
  · rw [continuous_iff_continuousAt]
    intro z0
    obtain ⟨y₀, hy₀, hy₀v⟩ := exists_pos_lt_min (y := imVec z0) (imVec_pos z0)
    obtain ⟨g, hg, hgb⟩ := hdom y₀ hy₀
    set U : Set (ι → ℍ) := {z | ∀ v, y₀ < (z v).im}
    have hUo : IsOpen U := by
      simp only [U, Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun v =>
        isOpen_lt continuous_const (UpperHalfPlane.continuous_im.comp (continuous_apply v))
    have hc : ContinuousOn (fun z => ∑' p, a p * qTerm (μ p) z) U :=
      continuousOn_tsum (fun p => (hcont_term p).continuousOn) hg fun p z hz => hgb z (fun v => (hz v).le) p
    exact hc.continuousAt (hUo.mem_nhds hy₀v)
  · rw [UpperHalfPlane.mdifferentiable_iff]
    set Z : ι → ℂ := fun u => (z u : ℂ)
    set G : ℂ → ℂ := fun w => ∑' p, a p * qTermC (μ p) (Function.update Z v w)
    have hG : DifferentiableOn ℂ G {w | 0 < w.im} := by
      intro w0 hw0
      have hw0' : 0 < w0.im := hw0
      obtain ⟨δ, hδ, hδz⟩ := exists_pos_lt_min (y := imVec z) (imVec_pos z)
      set y₀ := min δ (w0.im / 2)
      have hy₀ : 0 < y₀ := lt_min hδ (by linarith)
      obtain ⟨g, hg, hgb⟩ := hdom y₀ hy₀
      set U : Set ℂ := {w | y₀ < w.im}
      have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
      have hw0U : w0 ∈ U := by
        show y₀ < w0.im
        exact (min_le_right _ _).trans_lt (by linarith)
      have hD : DifferentiableOn ℂ G U := by
        refine differentiableOn_tsum_of_summable_norm hg (fun p => ?_) hUo fun p w hw => ?_
        · refine (DifferentiableOn.const_mul ?_ (a p))
          unfold qTermC
          have : ∀ u, Differentiable ℂ fun w : ℂ => Function.update Z v w u := by
            intro u; by_cases h : u = v
            · subst h; simp
            · simp [Function.update_of_ne h]
          exact (by fun_prop : Differentiable ℂ fun w : ℂ =>
            cexp (2 * π * Complex.I * ∑ u, (μ p u : ℂ) * Function.update Z v w u)).differentiableOn
        · have hwpos : 0 < w.im := hy₀.trans hw
          have heq : Function.update Z v w = fun u => ((Function.update z v (UpperHalfPlane.ofComplex w) u : ℍ) : ℂ) := by
            funext u
            by_cases h : u = v
            · subst h; simp [UpperHalfPlane.ofComplex_apply_of_im_pos hwpos]
            · simp [Function.update_of_ne h, Z]
          rw [heq, ← qTerm_eq_qTermC]
          refine hgb _ (fun u => ?_) p
          by_cases h : u = v
          · subst h; simp only [Function.update_self]
            rw [UpperHalfPlane.ofComplex_apply_of_im_pos hwpos]; exact hw.le
          · simp only [Function.update_of_ne h]; exact (min_le_left _ _).trans (hδz u).le
      exact (hD.differentiableAt (hUo.mem_nhds hw0U)).differentiableWithinAt
    refine hG.congr fun w hw => ?_
    simp only [Function.comp_apply, G]
    refine tsum_congr fun p => ?_
    rw [qTerm_eq_qTermC]
    congr 2
    funext u
    by_cases h : u = v
    · subst h; simp [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    · simp [Function.update_of_ne h, Z]

/-- **Limit at $\infty$** of a dominated series of exponentials whose nonzero terms have totally positive exponents. -/
theorem tendsto_tsum_qTerm_atImInfty [Nonempty ι] (a : α → ℂ) (μ : α → ι → ℝ)
    (hpos : ∀ p, a p ≠ 0 → ∀ v, 0 < μ p v) {g : α → ℝ} (hg : Summable g)
    (hgb : ∀ z : ι → ℍ, (∀ v, 1 ≤ (z v).im) → ∀ p, ‖a p * qTerm (μ p) z‖ ≤ g p) :
    Tendsto (fun z => ∑' p, a p * qTerm (μ p) z) atImInftyPi (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := (atImInftyPi : Filter (ι → ℍ))) hg
    (f := fun z p => a p * qTerm (μ p) z) (g := fun _ => 0) (fun p => ?_) ?_
  · simpa using h
  · by_cases hp : a p = 0
    · simp only [hp, zero_mul]; exact tendsto_const_nhds
    · rw [show (0 : ℂ) = a p * 0 by ring]
      refine Tendsto.const_mul _ ?_
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp_rw [norm_qTerm]
      obtain ⟨v₀⟩ : Nonempty ι := inferInstance
      have hv : ∀ v, 0 < μ p v := hpos p hp
      have him : Tendsto (fun z : ι → ℍ => (z v₀).im) atImInftyPi atTop :=
        tendsto_comap.mono_left (iInf_le _ v₀)
      have hpair : Tendsto (fun z : ι → ℍ => pair (μ p) (imVec z)) atImInftyPi atTop := by
        refine tendsto_atTop_mono (fun z => ?_) (him.const_mul_atTop (hv v₀))
        simp only [pair, imVec]
        exact Finset.single_le_sum (f := fun v => μ p v * (z v).im)
          (fun v _ => mul_nonneg (hv v).le (z v).im_pos.le) (Finset.mem_univ v₀)
      have := Real.tendsto_exp_atBot.comp (hpair.const_mul_atTop_of_neg (by nlinarith [Real.pi_pos] :
        (-2 * π : ℝ) < 0))
      simpa [Function.comp_def] using this
  · exact (eventually_im_ge 1).mono fun z hz p => hgb z hz p

end QSeries

/-! ### The $q$-expansion of $E_{W,2}$ -/

open Classical in
/-- The coefficient of the exponential $e(\operatorname{Tr}\tilde t\nu z)$ in $E_{W,2}$ (index $p = (t, n)$, $\nu = \nu_n$; $0$ for
$t = 0$ or $n = 0$). -/
noncomputable def oscA (W : F × F → ℂ) (𝔐 : Ideal (𝓞 F)) (h𝔐 : 𝔐 ≠ ⊥)
    (p : UOrbitF F × (Fin (Module.finrank ℚ F) → ℤ)) : ℂ :=
  if p.1.out = 0 ∨ p.2 = 0 then 0 else
    (latConst (levelBasis 𝔐 h𝔐) : ℂ) * rowR W 𝔐 (crep p.1) (dualVec (levelBasis 𝔐 h𝔐) p.2) *
      (if ∀ v, 0 < dualVec (levelBasis 𝔐 h𝔐) p.2 v * realEmb F v (crep p.1) then
        normSign (crep p.1) * ((-2 * π * Complex.I) ^ 2 / (2 - 1).factorial) ^
          Fintype.card (InfinitePlace F) * ∏ v, ((dualVec (levelBasis 𝔐 h𝔐) p.2 v : ℂ) ^ (2 - 1)) else 0)

/-- The exponent $\mu = \tilde t\nu_n$ (componentwise $\mu_v = \nu_{n,v}\sigma_v(\tilde t)$). -/
noncomputable def oscMu (𝔐 : Ideal (𝓞 F)) (h𝔐 : 𝔐 ≠ ⊥) (p : UOrbitF F × (Fin (Module.finrank ℚ F) → ℤ)) :
    InfinitePlace F → ℝ :=
  fun v => dualVec (levelBasis 𝔐 h𝔐) p.2 v * realEmb F v (crep p.1)

lemma heckeOsc_zero_eq {W : F × F → ℂ} {𝔐 : Ideal (𝓞 F)} (h𝔐 : 𝔐 ≠ ⊥) (z : InfinitePlace F → ℍ) (p) :
    heckeOsc W 𝔐 h𝔐 0 z p = oscA W 𝔐 h𝔐 p * qTerm (oscMu 𝔐 h𝔐 p) z := by
  classical
  unfold heckeOsc oscA
  by_cases h0 : p.1.out = 0 ∨ p.2 = 0
  · rw [if_pos h0, if_pos h0, zero_mul]
  · rw [if_neg h0, if_neg h0]
    push Not at h0
    rw [rowCoeff_zero_eq h𝔐 le_rfl ((crep_eq_zero_iff _).not.mpr h0.1) z p.2]
    unfold oscMu
    ring

lemma oscMu_pos {W : F × F → ℂ} {𝔐 : Ideal (𝓞 F)} (h𝔐 : 𝔐 ≠ ⊥) {p} (hp : oscA W 𝔐 h𝔐 p ≠ 0) :
    ∀ v, 0 < oscMu 𝔐 h𝔐 p v := by
  classical
  unfold oscA at hp
  split_ifs at hp with h0 h1
  · exact absurd rfl hp
  · exact h1
  · simp at hp

/-- **The $q$-expansion of $E_{W,2}$**: $E_{W,2}(z) = \mathrm{c}_\infty(W) + \sum_{(t, n)}a_{t,n}\,e(\langle\mu_{t,n}, z\rangle)$ with
$\mu_{t,n} = \tilde t\nu_n \gg 0$ whenever $a_{t,n} \ne 0$ (`oscA`, `oscMu`, `oscMu_pos`). -/
@[kb "shimura1978" "(3.11)-type expansion of E₂ (Ramanujan-sum form) [unverified]"]
theorem eis2_eq_qSeries {W : F × F → ℂ} {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W 2 𝔐) (z : InfinitePlace F → ℍ) :
    eis2 W 𝔐 hW.ne z = eisConst W 2 + ∑' p, oscA W 𝔐 hW.ne p * qTerm (oscMu 𝔐 hW.ne p) z := by
  classical
  obtain ⟨y₀, hy₀, hy₀v⟩ := exists_pos_lt_min (y := imVec z) (imVec_pos z)
  have hz : ∀ v, y₀ ≤ (z v).im := fun v => (hy₀v v).le
  obtain ⟨K₀, a₁, a₂, hK₀, ha₁, ha₂, hM1⟩ := norm_rowCoeff_two_le hW hy₀
  have hZ0f : (fun t : UOrbitF F => if t.out = 0 then (0 : ℂ) else rowCoeff W 𝔐 hW.ne 2 0 (crep t) z 0) = 0 := by
    funext t
    simp only [Pi.zero_apply]
    split_ifs with ht
    · rfl
    · exact rowCoeff_two_zero_zero hW.ne ((crep_eq_zero_iff _).not.mpr ht) z
  have hZ0s : Summable fun t : UOrbitF F => if t.out = 0 then (0 : ℂ) else rowCoeff W 𝔐 hW.ne 2 0 (crep t) z 0 := by
    rw [hZ0f]; exact summable_zero
  rw [eis2, rows_split hW hK₀ ha₁ ha₂ hM1 le_rfl zero_le_one hz hZ0s, hZ0f,
    show (0 : UOrbitF F → ℂ) = fun _ => 0 from rfl, tsum_zero, zero_add]
  congr 1
  exact tsum_congr fun p => heckeOsc_zero_eq hW.ne z p

lemma dom_oscA {W : F × F → ℂ} {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W 2 𝔐) {y₀ : ℝ} (hy₀ : 0 < y₀) :
    ∃ g : UOrbitF F × (Fin (Module.finrank ℚ F) → ℤ) → ℝ, Summable g ∧ ∀ z : InfinitePlace F → ℍ,
      (∀ v, y₀ ≤ (z v).im) → ∀ p, ‖oscA W 𝔐 hW.ne p * qTerm (oscMu 𝔐 hW.ne p) z‖ ≤ g p := by
  obtain ⟨K₀, a₁, a₂, hK₀, ha₁, ha₂, hM1⟩ := norm_rowCoeff_two_le hW hy₀
  refine ⟨_, summable_heckeMaj 𝔐 hW.ne hK₀ ha₁ ha₂, fun z hz p => ?_⟩
  rw [← heckeOsc_zero_eq]
  exact norm_heckeOsc_le hW hK₀ hM1 le_rfl zero_le_one hz p

/-- **$E_{W,2}$ is holomorphic** on $\mathbb{H}^d$. -/
@[kb "shimura1978" "Prop. 3.4, holomorphy of E₂ for d ≥ 2 [unverified]"]
theorem isHolomorphic_eis2 {W : F × F → ℂ} {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W 2 𝔐) :
    IsHolomorphic (eis2 W 𝔐 hW.ne) := by
  have h : eis2 W 𝔐 hW.ne = (fun _ => eisConst W 2) +
      fun z => ∑' p, oscA W 𝔐 hW.ne p * qTerm (oscMu 𝔐 hW.ne p) z := by
    funext z; exact eis2_eq_qSeries hW z
  rw [h]
  refine IsHolomorphic.add ⟨continuous_const, fun _ _ => mdifferentiable_const⟩ ?_
  exact isHolomorphic_tsum_qTerm _ _ fun y₀ hy₀ => dom_oscA hW hy₀

/-- **The constant term of $E_{W,2}$ at $\infty$**: $E_{W,2}(z) \to \mathrm{c}_\infty(W)$. -/
theorem tendsto_eis2_atImInfty {W : F × F → ℂ} {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W 2 𝔐) :
    Tendsto (eis2 W 𝔐 hW.ne) atImInftyPi (𝓝 (eisConst W 2)) := by
  obtain ⟨g, hg, hgb⟩ := dom_oscA hW one_pos
  have h := tendsto_tsum_qTerm_atImInfty (oscA W 𝔐 hW.ne) (oscMu 𝔐 hW.ne)
    (fun p hp => oscMu_pos hW.ne hp) hg hgb
  have := (tendsto_const_nhds (x := eisConst W 2)).add h
  rw [add_zero] at this
  exact this.congr fun z => (eis2_eq_qSeries hW z).symm

/-! ### Level $\mathfrak N$ with character -/

/-- **The parallel weight 2 Eisenstein series of level $\mathfrak N$ and character $\chi$** ($d \ge 2$):
$E_{2,\chi} = \lim_{s\to0^+}\sum_{(c,d)\in U\backslash(\mathfrak N\times\mathcal{O}_F)}\chi(d)^{-1}N(cz+d)^{-2}|N(cz+d)|^{-2s}$. -/
noncomputable def eis2Char (𝔑 : Ideal (𝓞 F)) (h𝔑 : 𝔑 ≠ ⊥) (χ : MulChar (𝓞 F ⧸ 𝔑) ℂ) :
    (InfinitePlace F → ℍ) → ℂ :=
  eis2 (chiWeight 𝔑 χ) 𝔑 h𝔑

/-- **$E_{2,\chi} \in M_2(\Gamma_0(\mathfrak N), \chi)$** for $d \ge 2$, $\mathfrak N \ne 0$ and $\chi(\varepsilon) = N(\varepsilon)^2 = 1$ on units
(i.e. $\chi$ trivial on the image of $\mathcal{O}_F^\times$). The cusp conditions hold by Koecher's principle. -/
@[kb "shimura1978" "§3, E₂(z; χ) ∈ M₂(Γ₀(𝔑), χ) for [F:ℚ] ≥ 2 [unverified]"]
theorem eis2Char_mem_modularFormChar (hd : 2 ≤ Fintype.card (InfinitePlace F)) {𝔑 : Ideal (𝓞 F)}
    (h𝔑 : 𝔑 ≠ ⊥) {χ : MulChar (𝓞 F ⧸ 𝔑) ℂ}
    (hχ : ∀ ε : (𝓞 F)ˣ, χ (Ideal.Quotient.mk 𝔑 (ε : 𝓞 F)) = ((unitNorm ε : ℝ) : ℂ) ^ (2 : ℤ)) :
    eis2Char 𝔑 h𝔑 χ ∈ modularFormChar 𝔑 χ 2 := by
  have hW := intWeight_chiWeight h𝔑 hχ
  have hlaw : ∀ γ ∈ Gamma0R 𝔑, eis2Char 𝔑 h𝔑 χ ∣[(2 : ℤ)] slHom (realEmb F) (toF F γ) =
      χ (Ideal.Quotient.mk 𝔑 (γ 1 1)) • eis2Char 𝔑 h𝔑 χ :=
    fun γ hγ => eis2_slash_of_weight hd hW (toF F γ) (slashWeight_chiWeight hγ)
  refine ⟨?_, hlaw⟩
  refine mem_modularFormSpace_of_GammaFull_le hd 𝔑 h𝔑 (GammaFull_le_Gamma1 𝔑) ?_ (isHolomorphic_eis2 hW)
  rintro _ ⟨γ, hγ, rfl⟩
  have h1 := (mem_Gamma1R 𝔑).mp hγ
  rw [hlaw γ h1.1, h1.2, map_one, one_smul]

/-- **The constant term of $E_{2,\chi}$ at $\infty$**: $\mathrm{c}_\infty(W_\chi) = \sum_{t\in U\backslash(\mathcal{O}_F\setminus0)}\chi(t)^{-1}N(t)^{-2}$. -/
theorem tendsto_eis2Char_atImInfty {𝔑 : Ideal (𝓞 F)} (h𝔑 : 𝔑 ≠ ⊥) {χ : MulChar (𝓞 F ⧸ 𝔑) ℂ}
    (hχ : ∀ ε : (𝓞 F)ˣ, χ (Ideal.Quotient.mk 𝔑 (ε : 𝓞 F)) = ((unitNorm ε : ℝ) : ℂ) ^ (2 : ℤ)) :
    Tendsto (eis2Char 𝔑 h𝔑 χ) atImInftyPi (𝓝 (eisConst (chiWeight 𝔑 χ) 2)) :=
  tendsto_eis2_atImInfty (intWeight_chiWeight h𝔑 hχ)

end QuadFormsKB.HilbertModular
