import QuadFormsKB.Tamagawa.Measure.Weil.AdditiveScaling

/-!
# Poisson summation on $\mathbb A_F$ twisted by an idele

For a factorizable Schwartz–Bruhat function $\Phi = f_\infty\otimes\bigotimes_v f_v$ on $\mathbb A_F$ ($f_\infty$ Schwartz on
$F_\infty$, $f_v$ finite combinations of coset indicators, $f_v = \mathbf 1_{\mathcal O_v}$ for $v\notin S$) and
$g\in\mathbb A_F^\times$,
$$\sum_{\xi\in F}\Phi(g\xi) = \|g\|_{\mathbb A}^{-1}\sum_{\xi\in F}\hat\Phi(g^{-1}\xi)$$
(`adelicPoisson_smul`). For $A = F$ the trace pairing is $\psi(xy)$, so the inverse adjoint $g^*$ is
$g^{-1}$. Proof: $x\mapsto\Phi(gx)$ is again factorizable Schwartz–Bruhat (`isSchwartzBruhatV_comp_mul`,
`ballIndV_comp_mul`); its local transforms are $\Delta_w(g_w)^{-1}\hat f_w(g_w^{-1}\,\cdot)$ (`integral_comp_mul_left`, from
the scaling of Haar measure); then the library's `adelicPoisson_factorizable`.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology NumberField.mixedEmbedding WithZero
open scoped Classical ENNReal NNReal Pointwise

namespace MeasureTheory

/-- Change of variables $y\mapsto ty$ for a regular Haar measure on a locally compact ring:
$\int h(ty)\,d\mu(y) = \Delta(t)^{-1}\int h\,d\mu$. -/
theorem integral_comp_mul_left {A : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
    [LocallyCompactSpace A] [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure]
    [μ.Regular] (t : Aˣ) (h : A → ℂ) :
    ∫ y, h ((t : A) * y) ∂μ = ((distribHaarChar A t : ℝ))⁻¹ • ∫ u, h u ∂μ := by
  have := integral_map_equiv (μ := μ) (MeasurableEquiv.smul t) h
  rw [show (⇑(MeasurableEquiv.smul t) : A → A) = (t • ·) from rfl, map_smul_eq_distribHaarChar_inv] at this
  simp only [Units.smul_def, smul_eq_mul] at this
  rw [← this, integral_smul_nnreal_measure, NNReal.smul_def, NNReal.coe_inv]

end MeasureTheory

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F
local notation "V" => mixedSpace F

/-! ### Local transforms of $x\mapsto f(tx)$ -/

theorem fourierInf_comp_mul (t : Vˣ) (f : V → ℂ) (z : V) :
    Analysis.fourierInf (fun y => f ((t : V) * y)) z =
      ((distribHaarChar V t : ℝ))⁻¹ • Analysis.fourierInf f (((t⁻¹ : Vˣ) : V) * z) := by
  unfold Analysis.fourierInf
  rw [← integral_comp_mul_left Analysis.selfDualInf t]
  congr 1
  ext y
  congr 3
  rw [mul_assoc, mul_left_comm (y : V), ← mul_assoc, Units.mul_inv, one_mul]

theorem fourierV_comp_mul (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ)
    (f : v.adicCompletion F → ℂ) (z : v.adicCompletion F) :
    Analysis.fourierV v (fun y => f ((t : v.adicCompletion F) * y)) z =
      ((distribHaarChar (v.adicCompletion F) t : ℝ))⁻¹ •
        Analysis.fourierV v f (((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * z) := by
  unfold Analysis.fourierV
  rw [← integral_comp_mul_left (Analysis.selfDualV v) t]
  congr 1
  ext y
  congr 3
  rw [mul_assoc, mul_left_comm (y : v.adicCompletion F), ← mul_assoc, Units.mul_inv, one_mul]

/-! ### Schwartz–Bruhat functions are stable under $x\mapsto ux$ -/

section Local

variable (v : HeightOneSpectrum (𝓞 F))

theorem valued_mul_le_exp_iff (u : (v.adicCompletion F)ˣ) (w : ℤᵐ⁰) (k : ℤ) :
    Valued.v (u : v.adicCompletion F) * w ≤ exp (-k) ↔
      w ≤ exp (-(k + log (Valued.v (u : v.adicCompletion F)))) := by
  have hu : Valued.v (u : v.adicCompletion F) ≠ 0 := by simp
  conv_lhs => rw [← exp_log hu]
  rw [mul_comm, ← le_div_iff₀ (zero_lt_iff.mpr exp_ne_zero), ← exp_sub]
  congr! 2
  ring

/-- $\mathbf 1_{c+\mathfrak p_v^k}(ux) = \mathbf 1_{u^{-1}c+\mathfrak p_v^{k+\operatorname{ord}(u)}}(x)$, with
$v(u) = \exp(\log v(u))$ (so $\log v(u) = -\operatorname{ord}_v u$). -/
theorem ballIndV_comp_mul (u : (v.adicCompletion F)ˣ) (c : v.adicCompletion F) (k : ℤ) :
    (fun x => Analysis.ballIndV v c k ((u : v.adicCompletion F) * x)) =
      Analysis.ballIndV v (((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * c)
        (k + log (Valued.v (u : v.adicCompletion F))) := by
  funext x
  have hx : (u : v.adicCompletion F) * x - c =
      (u : v.adicCompletion F) * (x - ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * c) := by
    rw [mul_sub, ← mul_assoc, Units.mul_inv, one_mul]
  simp only [Analysis.ballIndV, Set.indicator, Set.mem_ofPred_eq, hx, map_mul, valued_mul_le_exp_iff]

theorem isSchwartzBruhatV_comp_mul {f : v.adicCompletion F → ℂ} (hf : Analysis.IsSchwartzBruhatV v f)
    (u : (v.adicCompletion F)ˣ) :
    Analysis.IsSchwartzBruhatV v (fun x => f ((u : v.adicCompletion F) * x)) := by
  obtain ⟨n, a, c, k, rfl⟩ := hf
  refine ⟨n, a, fun i => ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * c i,
    fun i => k i + log (Valued.v (u : v.adicCompletion F)), ?_⟩
  funext x
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← ballIndV_comp_mul]

theorem isSchwartzBruhatV_ballIndV (c : v.adicCompletion F) (k : ℤ) :
    Analysis.IsSchwartzBruhatV v (Analysis.ballIndV v c k) :=
  ⟨1, fun _ => 1, fun _ => c, fun _ => k, by funext x; simp⟩

theorem ballIndV_zero_comp_mul (u : (v.adicCompletion F)ˣ) (hu : Valued.v (u : v.adicCompletion F) = 1) :
    (fun x => Analysis.ballIndV v 0 0 ((u : v.adicCompletion F) * x)) = Analysis.ballIndV v 0 0 := by
  rw [ballIndV_comp_mul, hu, mul_zero]
  simp

end Local

theorem valued_unitAt_eq_one {g : AFˣ} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ (finite_bad g).toFinset) :
    Valued.v ((unitAt g v : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_or, not_not] at hv
  have h1 := hv.1
  have h2 := hv.2
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 h2
  have hmul : Valued.v ((g : AF) v) * Valued.v (((g⁻¹ : AFˣ) : AF) v) = 1 := by
    rw [← map_mul]
    have : (g : AF) v * ((g⁻¹ : AFˣ) : AF) v = 1 := congrArg (fun x : AF => x v) g.mul_inv
    rw [this, map_one]
  refine le_antisymm h1 ?_
  by_contra hlt
  push Not at hlt
  have : Valued.v ((g : AF) v) * Valued.v (((g⁻¹ : AFˣ) : AF) v) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  exact this.ne hmul

/-! ### The twisted Poisson formula -/

/-- Multiplication by a unit of $F_\infty$ as a continuous linear equivalence. -/
def mulCLE (t : Vˣ) : V ≃L[ℝ] V :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => (t : V) * x
      invFun := fun x => ((t⁻¹ : Vˣ) : V) * x
      map_add' := mul_add _
      map_smul' := fun c x => mul_smul_comm c _ _
      left_inv := fun x => by simp [← mul_assoc]
      right_inv := fun x => by simp [← mul_assoc] }

@[simp] theorem mulCLE_apply (t : Vˣ) (x : V) : mulCLE t x = (t : V) * x := rfl

section Twisted

variable (fv : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ) (S : Finset (HeightOneSpectrum (𝓞 F)))
  (hS : ∀ v ∈ S, Analysis.IsSchwartzBruhatV v (fv v)) (hout : ∀ v ∉ S, fv v = Analysis.ballIndV v 0 0)

include hout in
theorem finite_mulSupport_fourierV (g : AFˣ) (γ : F) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      Analysis.fourierV v (fv v) (((unitAt g v)⁻¹ : (v.adicCompletion F)ˣ) * algebraMap F _ γ)).Finite := by
  refine ((S.finite_toSet.union (finite_bad g)).union (Analysis.finite_support_diffExp.union
    (HeightOneSpectrum.Support.finite (𝓞 F) γ))).subset fun v hv => ?_
  rw [Function.mem_mulSupport] at hv
  by_contra h
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_ofPred_eq, Function.mem_support, not_or, not_not,
    HeightOneSpectrum.Support, not_lt] at h
  obtain ⟨⟨hvS, hb1, hb2⟩, hd, hγ⟩ := h
  apply hv
  rw [hout v hvS]
  refine Analysis.fourierV_ballIndV_zero_eq_one v (by exact_mod_cast hd) ?_
  have hnb : v ∉ (finite_bad g).toFinset := by simp [hb1, hb2]
  have h1 : Valued.v (((unitAt g v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, valued_unitAt_eq_one hnb, inv_one]
  rw [map_mul, h1, one_mul, HN.valued_algebraMap]
  exact hγ

/-- The twist $y\mapsto f(ty)$ of a Schwartz function on $F_\infty$ by $t\in F_\infty^\times$. -/
def twistInf (t : Vˣ) (f : SchwartzMap V ℂ) : SchwartzMap V ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mulCLE t) f

@[simp] theorem twistInf_apply (t : Vˣ) (f : SchwartzMap V ℂ) (y : V) :
    twistInf t f y = f ((t : V) * y) := rfl

omit [NumberField F] in
/-- The twist $x\mapsto f_v(g_vx)$ of the local components by a finite idele $g_f$. -/
def twistFin (gf : AFˣ) : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ :=
  fun v x => fv v ((unitAt gf v : v.adicCompletion F) * x)

include hS hout in
theorem isSchwartzBruhatV_twistFin (gf : AFˣ) :
    ∀ v ∈ S ∪ (finite_bad gf).toFinset, Analysis.IsSchwartzBruhatV v (twistFin fv gf v) := by
  intro v _
  by_cases hv : v ∈ S
  · exact isSchwartzBruhatV_comp_mul v (hS v hv) _
  · have := isSchwartzBruhatV_comp_mul v (isSchwartzBruhatV_ballIndV v 0 0) (unitAt gf v)
    show Analysis.IsSchwartzBruhatV v (fun x => fv v ((unitAt gf v : v.adicCompletion F) * x))
    rw [hout v hv]; exact this

include hout in
theorem twistFin_eq_of_notMem (gf : AFˣ) :
    ∀ v ∉ S ∪ (finite_bad gf).toFinset, twistFin fv gf v = Analysis.ballIndV v 0 0 := by
  intro v hv
  simp only [Finset.mem_union, not_or] at hv
  show (fun x => fv v ((unitAt gf v : v.adicCompletion F) * x)) = _
  rw [hout v hv.1]
  exact ballIndV_zero_comp_mul v _ (valued_unitAt_eq_one hv.2)

include hout in
/-- Pointwise identity behind the twisted Poisson formula: the transform of the twisted function at $\gamma$ is
$\|g\|^{-1}$ times the transform of the original one at $g^{-1}\gamma$. -/
theorem fourier_twist_eq (f : SchwartzMap V ℂ) (g : (Adeles F)ˣ) (γ : F) :
    Analysis.fourierInf (twistInf (infPart g) f) (mixedEmbedding F γ) *
        ∏ᶠ v, Analysis.fourierV v (twistFin fv (finPart g) v) (algebraMap F _ γ) =
      (((ideleNorm F g)⁻¹ : ℝ) : ℂ) * (Analysis.fourierInf f
          (((infPart g)⁻¹ : Vˣ) * mixedEmbedding F γ) *
        ∏ᶠ v, Analysis.fourierV v (fv v)
          (((unitAt (finPart g) v)⁻¹ : (v.adicCompletion F)ˣ) * algebraMap F _ γ)) := by
  set t := infPart g
  set gf := finPart g
  have hInf : ∀ z, Analysis.fourierInf (⇑(twistInf t f)) z =
      (((distribHaarChar V t : ℝ))⁻¹ : ℂ) * Analysis.fourierInf f (((t⁻¹ : Vˣ) : V) * z) := by
    intro z
    have : (⇑(twistInf t f)) = fun y => f ((t : V) * y) := funext fun y => rfl
    rw [this, fourierInf_comp_mul, Complex.real_smul]
    push_cast; rfl
  have hV : ∀ (v : HeightOneSpectrum (𝓞 F)) z,
      Analysis.fourierV v (twistFin fv gf v) z =
      (((modAt gf v : ℝ))⁻¹ : ℂ) *
        Analysis.fourierV v (fv v) (((unitAt gf v)⁻¹ : (v.adicCompletion F)ˣ) * z) := by
    intro v z
    show Analysis.fourierV v (fun x => fv v ((unitAt gf v : v.adicCompletion F) * x)) z = _
    rw [fourierV_comp_mul, Complex.real_smul, modAt, Complex.ofReal_inv]
  have hfinΔ : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (((modAt gf v : ℝ))⁻¹ : ℂ)).Finite :=
    (mulSupport_modAt_finite gf).subset fun v hv => by
      rw [Function.mem_mulSupport] at hv ⊢
      intro h; apply hv; rw [h]; simp
  have hprodΔ : ∏ᶠ v, (((modAt gf v : ℝ))⁻¹ : ℂ) = (((∏ᶠ v, (modAt gf v : ℝ)))⁻¹ : ℂ) := by
    rw [← finprod_inv_distrib]
  have hsplit : ∏ᶠ v, (((modAt gf v : ℝ))⁻¹ : ℂ) *
      Analysis.fourierV v (fv v) (((unitAt gf v)⁻¹ : (v.adicCompletion F)ˣ) * algebraMap F _ γ) =
      (((∏ᶠ v, (modAt gf v : ℝ)))⁻¹ : ℂ) * ∏ᶠ v, Analysis.fourierV v (fv v)
        (((unitAt gf v)⁻¹ : (v.adicCompletion F)ˣ) * algebraMap F _ γ) := by
    rw [finprod_mul_distrib hfinΔ (finite_mulSupport_fourierV fv S hout gf γ), hprodΔ]
  have hnorm : (((ideleNorm F g)⁻¹ : ℝ) : ℂ) =
      (((distribHaarChar V t : ℝ))⁻¹ : ℂ) * (((∏ᶠ v, (modAt gf v : ℝ)))⁻¹ : ℂ) := by
    have hc : (((∏ᶠ v, (modAt gf v : ℝ) : ℝ)) : ℂ) = ∏ᶠ v, (((modAt gf v : ℝ)) : ℂ) :=
      MonoidHom.map_finprod Complex.ofRealHom.toMonoidHom (f := fun v => (modAt gf v : ℝ))
        ((mulSupport_modAt_finite gf).subset fun v hv => by
          rw [Function.mem_mulSupport] at hv ⊢; intro h; apply hv; exact_mod_cast h)
    rw [ideleNorm, ← distribHaarChar_mixedSpace]
    push_cast
    rw [mul_inv, hc]
  rw [hInf, finprod_congr fun v => hV v _, hsplit, hnorm]
  ring

include hS hout in
/-- **Poisson summation on $\mathbb A_F$, twisted by an idele ($A = F$).** For $f_\infty$ Schwartz on $F_\infty$,
Schwartz–Bruhat $f_v$ with $f_v = \mathbf 1_{\mathcal O_v}$ off a finite set $S$, and $g = (g_\infty, g_f)\in\mathbb A_F^\times$:
$$\sum_{\gamma\in F}f_\infty(g_\infty\gamma)\prod_v f_v(g_v\gamma) =
\|g\|_{\mathbb A}^{-1}\sum_{\gamma\in F}\hat f_\infty(g_\infty^{-1}\gamma)\prod_v\hat f_v(g_v^{-1}\gamma).$$ -/
@[kb "weil1982" "§2.1 [unverified page]; Poisson as in casselsfrohlich1967 Ch. XV (Tate), Thm. 4.2.1 [unverified]"]
theorem adelicPoisson_smul (f : SchwartzMap V ℂ) (g : (Adeles F)ˣ) :
    ∑' γ : F, f ((infPart g : V) * mixedEmbedding F γ) *
        ∏ᶠ v, fv v ((unitAt (finPart g) v : v.adicCompletion F) * algebraMap F _ γ) =
      ((ideleNorm F g)⁻¹ : ℝ) • ∑' γ : F, Analysis.fourierInf f
          (((infPart g)⁻¹ : Vˣ) * mixedEmbedding F γ) *
        ∏ᶠ v, Analysis.fourierV v (fv v)
          (((unitAt (finPart g) v)⁻¹ : (v.adicCompletion F)ˣ) * algebraMap F _ γ) := by
  have key := Analysis.adelicPoisson_factorizable (twistFin fv (finPart g)) _
    (isSchwartzBruhatV_twistFin fv S hS hout _) (twistFin_eq_of_notMem fv S hout _)
    (twistInf (infPart g) f)
  calc _ = ∑' γ : F, twistInf (infPart g) f (mixedEmbedding F γ) *
        ∏ᶠ v, twistFin fv (finPart g) v (algebraMap F _ γ) := rfl
    _ = _ := key
    _ = _ := by
      rw [Complex.real_smul, ← tsum_mul_left]
      exact tsum_congr fun γ => fourier_twist_eq fv S hout f g γ

include hS hout in
/-- The left side of `adelicPoisson_smul` converges absolutely. -/
theorem summable_adelicPoisson_smul_lhs (f : SchwartzMap V ℂ) (g : (Adeles F)ˣ) :
    Summable fun γ : F => f ((infPart g : V) * mixedEmbedding F γ) *
      ∏ᶠ v, fv v ((unitAt (finPart g) v : v.adicCompletion F) * algebraMap F _ γ) :=
  Analysis.summable_adelicPoisson_factorizable_lhs (twistFin fv (finPart g)) _
    (isSchwartzBruhatV_twistFin fv S hS hout _) (twistFin_eq_of_notMem fv S hout _) (twistInf (infPart g) f)

include hS hout in
/-- The right side of `adelicPoisson_smul` converges absolutely. -/
theorem summable_adelicPoisson_smul_rhs (f : SchwartzMap V ℂ) (g : (Adeles F)ˣ) :
    Summable fun γ : F => Analysis.fourierInf f (((infPart g)⁻¹ : Vˣ) * mixedEmbedding F γ) *
      ∏ᶠ v, Analysis.fourierV v (fv v)
        (((unitAt (finPart g) v)⁻¹ : (v.adicCompletion F)ˣ) * algebraMap F _ γ) := by
  have h := Analysis.summable_adelicPoisson_factorizable_rhs (twistFin fv (finPart g)) _
    (isSchwartzBruhatV_twistFin fv S hS hout _) (twistFin_eq_of_notMem fv S hout _) (twistInf (infPart g) f)
  have hc : (((ideleNorm F g)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (inv_pos.mpr (ideleNorm_pos g)).ne'
  simp_rw [fourier_twist_eq fv S hout f g] at h
  exact (summable_mul_left_iff hc).mp h

end Twisted

end

end QuadFormsKB.Tamagawa.Measure.Weil
