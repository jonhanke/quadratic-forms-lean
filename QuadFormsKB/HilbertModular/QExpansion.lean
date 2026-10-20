/-
# Hilbert modular forms IV: Fourier coefficients and the Koecher principle, analytic core

Setting: $\iota$ finite (the real places), $b = (b_j)_{j\in J}$ an $\mathbb{R}$-basis of $\mathbb{R}^\iota$ spanning a lattice
$\Lambda = \bigoplus_j\mathbb{Z}b_j$ (for $F$: the image of a fractional ideal, e.g. $(\mathfrak a\mathfrak d)^{-1}$), and
$f : \mathbb{H}^\iota \to \mathbb{C}$ holomorphic (`IsHolomorphic`) and $\Lambda$-periodic: $f(z + \lambda) = f(z)$ for $\lambda \in \Lambda$.
Write $\langle \nu, x\rangle = \sum_v \nu_vx_v$ (for $F$: $\operatorname{Tr}(\nu x)$), $e(w) = e^{2\pi i w}$, and $x(t) = \sum_j t_jb_j$.

* `coeff f b ν y` $= c_\nu(y) = \displaystyle\int_{t\in(0,1]^J} f\big(x(t) + iy\big)\,e\big(-\langle\nu, x(t)\rangle\big)\,dt$, the $\nu$-th Fourier coefficient
  of $x \mapsto f(x+iy)$ on $\mathbb{R}^\iota/\Lambda$ (up to the covolume of $\Lambda$), for $\nu$ in the dual lattice
  ($\langle\nu, b_j\rangle \in \mathbb{Z}$).
* `coeff_add_single`, `coeff_eq_exp_mul`: **holomorphy fixes the $y$-dependence**,
  $c_\nu(y') = e^{-2\pi\langle\nu, y'-y\rangle}c_\nu(y)$ for all $y, y' \in \mathbb{R}_{>0}^\iota$; so
  $c_\nu(y) = a_\nu e^{-2\pi\langle\nu,y\rangle}$ with $a_\nu$ = `qCoeff f b ν` independent of $y$.
  *Proof:* for one variable $v$, $\Phi(w) = \int f(x(t) + iy + we_v)\,e(-\langle\nu, x(t) + we_v\rangle)\,dt$ is holomorphic on
  $\operatorname{Im} w > -y_v$ (`differentiableOn_setIntegral_of_compact`: Cauchy estimates + differentiation under the
  integral), constant on $\mathbb{R}$ by periodicity (`integral_unitCube_add`: integrals of $\mathbb{Z}^J$-periodic functions over
  translated unit cubes agree), hence constant (identity theorem); $\Phi(is) = e^{2\pi\nu_vs}c_\nu(y + se_v)$.
* `norm_coeff_le`: $|c_\nu(y)| \le \sup_x |f(x+iy)|$; `exists_bound_slice`: this supremum is finite.
* `coeff_eq_zero_of_isBounded`: if $f$ is bounded on $\{\operatorname{Im} z_v \ge A\ \forall v\}$, then $a_\nu = 0$ unless $\nu_v \ge 0$ for all $v$.
* **Koecher principle, analytic core** (`koecher_coeff_eq_zero`): suppose $\varepsilon \in \mathbb{R}_{>0}^\iota$ satisfies
  $|f(\varepsilon z)| = |f(z)|$ (componentwise scaling), $\varepsilon_w > 1$ and $\varepsilon_v < 1$ for $v \ne w$. If $\nu_w < 0$ then
  $c_\nu \equiv 0$. *No boundedness at the cusp is assumed.* For a Hilbert modular form, $\varepsilon = (u_v^2)$ for a unit $u$
  with $|u_v| < 1$ for $v \ne w$ (Dirichlet); such units exist exactly when $d \ge 2$ (`Koecher.lean`).

Sources: Koecher (1954) [unverified]; Freitag, *Hilbert Modular Forms*, Ch. I, §4 (Koecher's principle) [unverified];
Garrett 1990, Ch. 1 [unverified]. The proof here is the standard one (unit scaling of the Fourier coefficients) on the
level of coefficients; Fourier inversion (the expansion converging to $f$) is not needed for it.
-/
import QuadFormsKB.HilbertModular.Basic

open MeasureTheory Set Metric Filter Topology Complex UpperHalfPlane
open scoped Real Manifold

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

/-! ### Integrals of periodic functions over unit cubes -/

/-- The unit cube $(0,1]^J$. -/

def unitCube (J : Type*) : Set (J → ℝ) := {t | ∀ j, t j ∈ Ioc (0:ℝ) 1}

lemma rep_sub_int (x : ℝ) : ∃ n : ℤ, ((AddCircle.equivIoc 1 0 (x : UnitAddCircle) : ℝ)) = x + n := by
  have h : (((AddCircle.equivIoc 1 0 (x : UnitAddCircle) : ℝ) - x : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, AddCircle.coe_equivIoc, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp h
  exact ⟨n, by simp at hn; linarith⟩

lemma integral_unitCube_add {J : Type*} [Fintype J] (G : (J → ℝ) → ℂ)
    (hG : ∀ (m : J → ℤ) t, G (t + fun j => (m j : ℝ)) = G t) (a : J → ℝ) :
    ∫ t in unitCube J, G (t + a) = ∫ t in unitCube J, G t := by
  set Gt : UnitAddTorus J → ℂ := fun θ => G (fun j => ((AddCircle.equivIoc 1 0 (θ j)) : ℝ))
  have key : ∀ x : J → ℝ, Gt (fun i => (x i : UnitAddCircle)) = G x := by
    intro x
    choose n hn using fun i => rep_sub_int (x i)
    simp only [Gt]
    rw [show (fun j => ((AddCircle.equivIoc 1 0 ((x j : UnitAddCircle))) : ℝ)) = x + fun j => (n j : ℝ) from
      funext fun j => hn j]
    exact hG n x
  have hA : ∀ b : J → ℝ, ∫ x in {x : J → ℝ | ∀ i, x i ∈ Ioc (b i) (b i + 1)}, G x =
      ∫ x in unitCube J, G x := by
    intro b
    have e1 := UnitAddTorus.integral_preimage Gt b
    have e0 := UnitAddTorus.integral_preimage Gt 0
    simp_rw [key] at e1 e0
    rw [← e1, e0]
    simp [unitCube]
  have ha := hA a
  have hpre : (fun t => t + a) ⁻¹' {x : J → ℝ | ∀ i, x i ∈ Ioc (a i) (a i + 1)} = unitCube J := by
    ext t; simp only [mem_preimage, mem_setOf_eq, unitCube, Pi.add_apply, mem_Ioc]
    constructor <;> intro h i <;> have := h i <;> constructor <;> linarith [this.1, this.2]
  have hT := (measurePreserving_add_right (volume : Measure (J → ℝ)) a).setIntegral_preimage_emb
    (measurableEmbedding_addRight a) G {x : J → ℝ | ∀ i, x i ∈ Ioc (a i) (a i + 1)}
  rw [hpre] at hT
  rw [hT, ha]

/-! ### Holomorphy of parametric integrals -/

/-- **Holomorphy of parametric integrals**: if $h(t, w)$ is continuous on $K \times U$ ($K$ compact, $U \subseteq \mathbb{C}$ open) and
holomorphic in $w \in U$ for each $t \in K$, then $w \mapsto \int_S h(t, w)\,dt$ is holomorphic on $U$ for measurable $S \subseteq K$. -/

lemma differentiableOn_setIntegral_of_compact {J : Type*} [Fintype J]
    {S K : Set (J → ℝ)} (hSK : S ⊆ K) (hK : IsCompact K) (hS : MeasurableSet S)
    {U : Set ℂ} (hU : IsOpen U) (h : (J → ℝ) → ℂ → ℂ)
    (hc : ContinuousOn (Function.uncurry h) (K ×ˢ U))
    (hd : ∀ t ∈ K, DifferentiableOn ℂ (h t) U) :
    DifferentiableOn ℂ (fun w => ∫ t in S, h t w) U := by
  intro w₀ hw₀
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU w₀ hw₀
  set r := R / 3 with hr
  have hr0 : 0 < r := by positivity
  have hball : closedBall w₀ (2 * r) ⊆ U := fun z hz =>
    hRU (lt_of_le_of_lt (mem_closedBall.mp hz) (by rw [hr]; linarith))
  have hKc : IsCompact (K ×ˢ closedBall w₀ (2 * r)) := hK.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn
    (hc.mono (prod_mono le_rfl hball))
  have hfin : volume S < ⊤ := lt_of_le_of_lt (measure_mono hSK) hK.measure_lt_top
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hfin.ne
  have hcont : ∀ w ∈ U, ContinuousOn (fun t => h t w) K := fun w hw =>
    (hc.comp (continuousOn_id.prodMk continuousOn_const) fun t ht => ⟨ht, hw⟩ :)
  have hder : ∀ t ∈ K, ∀ w ∈ ball w₀ r, ‖deriv (h t) w‖ ≤ C / r := by
    intro t ht w hw
    have hw' := mem_ball.mp hw
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0 ?_ fun z hz => ?_
    · refine (hd t ht).diffContOnCl_ball ?_
      intro z hz
      apply hball
      rw [mem_closedBall]
      have := mem_closedBall.mp hz
      calc dist z w₀ ≤ dist z w + dist w w₀ := dist_triangle _ _ _
        _ ≤ 2 * r := by linarith
    · have : (t, z) ∈ K ×ˢ closedBall w₀ (2 * r) := by
        refine ⟨ht, ?_⟩
        rw [mem_closedBall]
        have h1 := mem_sphere.mp hz
        calc dist z w₀ ≤ dist z w + dist w w₀ := dist_triangle _ _ _
          _ ≤ 2 * r := by linarith
      exact hC _ this
  have hmeas : ∀ w ∈ U, AEStronglyMeasurable (fun t => h t w) (volume.restrict S) := fun w hw =>
    ((hcont w hw).mono hSK).aestronglyMeasurable hS
  have hint : Integrable (fun t => h t w₀) (volume.restrict S) :=
    ((hcont w₀ hw₀).integrableOn_compact hK).mono_set hSK
  -- the sequence `c n = r / (n + 1) → 0`
  set c : ℕ → ℂ := fun n => (r : ℂ) / ((n : ℂ) + 1) with hcdef
  have hcU : ∀ n, w₀ + c n ∈ U := by
    intro n
    apply hball
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, hcdef]
    simp only [norm_div]
    have h1 : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
      rw [show ((n : ℂ) + 1) = ((n + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    rw [h1, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hF'meas : AEStronglyMeasurable (fun t => deriv (h t) w₀) (volume.restrict S) := by
    have hseq : Tendsto c atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)).const_mul (r : ℂ)
        simpa [hcdef, div_eq_mul_inv] using this
      · simp only [hcdef, mem_compl_iff, mem_singleton_iff, div_eq_zero_iff, Complex.ofReal_eq_zero,
          hr0.ne', false_or]
        exact_mod_cast Nat.succ_ne_zero n
    have hlim : ∀ t ∈ K, Tendsto (fun n : ℕ => (c n)⁻¹ * (h t (w₀ + c n) - h t w₀))
        atTop (𝓝 (deriv (h t) w₀)) := by
      intro t ht
      have hdA : HasDerivAt (h t) (deriv (h t) w₀) w₀ :=
        ((hd t ht).differentiableAt (hU.mem_nhds hw₀)).hasDerivAt
      have := hdA.tendsto_slope_zero.comp hseq
      refine this.congr fun n => ?_
      simp only [Function.comp_apply, smul_eq_mul]
    refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter ℕ)
      (f := fun (n : ℕ) (t : J → ℝ) => (c n)⁻¹ * (h t (w₀ + c n) - h t w₀)) (fun n => ?_) ?_
    · exact ((hmeas _ (hcU n)).sub (hmeas _ hw₀)).const_mul _
    · exact (ae_restrict_iff' hS).mpr (Eventually.of_forall fun t ht => hlim t (hSK ht))
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict S)
    (F := fun w t => h t w) (F' := fun w t => deriv (h t) w) (x₀ := w₀) (bound := fun _ => C / r)
    (ball_mem_nhds w₀ hr0)
    (Eventually.mono (ball_mem_nhds w₀ (show 0 < R by linarith)) fun w hw => hmeas w (hRU hw))
    hint hF'meas
    ((ae_restrict_iff' hS).mpr (Eventually.of_forall fun t ht w hw => hder t (hSK ht) w hw))
    (integrable_const _)
    ((ae_restrict_iff' hS).mpr (Eventually.of_forall fun t ht w hw =>
      ((hd t (hSK ht)).differentiableAt (hU.mem_nhds (hball (ball_subset_closedBall
        (ball_subset_ball (by linarith) hw))))).hasDerivAt))
  exact hmain.2.differentiableAt.differentiableWithinAt

/-! ### Fourier coefficients -/

variable {ι : Type*} [Fintype ι] {J : Type*} [Fintype J]



/-- $Z \mapsto (Z_v)_v \in \mathbb{H}^\iota$ for $Z \in \mathbb{C}^\iota$ (Mathlib's `ofComplex` in each coordinate; junk where
$\operatorname{Im} Z_v \le 0$). -/
noncomputable def toHPi (Z : ι → ℂ) : ι → ℍ := fun v => ofComplex (Z v)

/-- **The point $x + iy \in \mathbb{H}^\iota$** for $x, y \in \mathbb{R}^\iota$, $y > 0$ (junk otherwise). -/
noncomputable def ptXY (x y : ι → ℝ) : ι → ℍ := toHPi (fun v => (x v : ℂ) + (y v : ℂ) * Complex.I)

/-- **The pairing** $\langle\nu, x\rangle = \sum_v\nu_vx_v$ on $\mathbb{R}^\iota$ (for $F$: $\operatorname{Tr}(\nu x)$). -/
def pair (ν x : ι → ℝ) : ℝ := ∑ v, ν v * x v

/-- **The $\nu$-th Fourier coefficient at height $y$**:
$c_\nu(y) = \int_{t\in(0,1]^J} f\big(x(t) + iy\big)\,e\big(-\langle\nu, x(t)\rangle\big)\,dt$, $x(t) = \sum_jt_jb_j$ (`b.equivFun.symm t`).

Parameters: `f`, `b` (a basis of $\mathbb{R}^\iota$; its $\mathbb{Z}$-span is the period lattice), `ν` (the frequency), `y` (the
height, $y > 0$). -/
@[kb "garrett1990" "Ch. 1, Fourier expansions of Hilbert modular forms [unverified]"]
noncomputable def coeff (f : (ι → ℍ) → ℂ) (b : Module.Basis J ℝ (ι → ℝ)) (ν y : ι → ℝ) : ℂ :=
  ∫ t in unitCube J, f (ptXY (b.equivFun.symm t) y) *
    cexp (-(2 * π * Complex.I) * (pair ν (b.equivFun.symm t) : ℂ))

/-- $\{Z \in \mathbb{C}^\iota : \operatorname{Im}Z_v > 0\ \forall v\}$. -/
def posSet (ι : Type*) : Set (ι → ℂ) := {Z | ∀ v, 0 < (Z v).im}

lemma continuousOn_comp_toHPi {f : (ι → ℍ) → ℂ} (hf : Continuous f) :
    ContinuousOn (fun Z => f (toHPi Z)) (posSet ι) := by
  refine hf.comp_continuousOn (continuousOn_pi.mpr fun v Z hZ => ?_)
  exact ContinuousAt.continuousWithinAt (ContinuousAt.comp (f := fun Z : ι → ℂ => Z v)
    (mdifferentiableAt_ofComplex (hZ v)).continuousAt (continuous_apply v).continuousAt)

lemma IsHolomorphic.mdiff_update [DecidableEq ι] {f : (ι → ℍ) → ℂ} (hf : IsHolomorphic f)
    (z : ι → ℍ) (v : ι) : MDiff (fun w : ℍ => f (Function.update z v w)) := by
  convert hf.2 z v

lemma toHPi_update [DecidableEq ι] (Z : ι → ℂ) (v : ι) (w : ℂ) :
    toHPi (Function.update Z v w) = Function.update (toHPi Z) v (ofComplex w) := by
  funext u
  by_cases h : u = v
  · subst h; simp [toHPi]
  · simp [toHPi, Function.update_of_ne h]

lemma differentiableOn_update [DecidableEq ι] {f : (ι → ℍ) → ℂ} (hf : IsHolomorphic f)
    (Z : ι → ℂ) (v : ι) :
    DifferentiableOn ℂ (fun w => f (toHPi (Function.update Z v (Z v + w))))
      {w | -(Z v).im < w.im} := by
  have hg := UpperHalfPlane.mdifferentiable_iff.mp (hf.mdiff_update (toHPi Z) v)
  have : (fun w => f (toHPi (Function.update Z v (Z v + w)))) =
      ((fun ζ : ℍ => f (Function.update (toHPi Z) v ζ)) ∘ ofComplex) ∘ (fun w => Z v + w) := by
    funext w; simp [toHPi_update]
  rw [this]
  refine hg.comp ((differentiable_const _).add differentiable_id).differentiableOn ?_
  intro w hw
  simp only [mem_setOf_eq, add_im] at hw ⊢
  linarith


lemma add_single_eq_update [DecidableEq ι] (Z : ι → ℂ) (v : ι) (w : ℂ) :
    Z + Pi.single v w = Function.update Z v (Z v + w) := by
  funext u
  by_cases h : u = v
  · subst h; simp
  · simp [Function.update_of_ne h, Pi.single_apply, h]

lemma pair_add (ν x x' : ι → ℝ) : pair ν (x + x') = pair ν x + pair ν x' := by
  simp [pair, mul_add, Finset.sum_add_distrib]

lemma pair_smul (ν x : ι → ℝ) (c : ℝ) : pair ν (c • x) = c * pair ν x := by
  simp only [pair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma pair_sub (ν x x' : ι → ℝ) : pair ν (x - x') = pair ν x - pair ν x' := by
  simp [pair, mul_sub, Finset.sum_sub_distrib]

lemma pair_single [DecidableEq ι] (ν : ι → ℝ) (v : ι) (c : ℝ) : pair ν (Pi.single v c) = ν v * c := by
  simp [pair, Pi.single_apply]

/-- **Lattice periodicity** of $f$: $f(z + \lambda) = f(z)$ for $\lambda \in \Lambda = \bigoplus_j\mathbb{Z}b_j$, in coordinates
$z = x + iy$. -/
def IsLatticePeriodic (f : (ι → ℍ) → ℂ) (b : Module.Basis J ℝ (ι → ℝ)) : Prop :=
  ∀ (m : J → ℤ) (x y : ι → ℝ), (∀ v, 0 < y v) →
    f (ptXY (x + b.equivFun.symm (fun j => (m j : ℝ))) y) = f (ptXY x y)

/-- **$\nu$ is in the dual lattice**: $\langle\nu, b_j\rangle \in \mathbb{Z}$ for all $j$. -/
def IsDual (b : Module.Basis J ℝ (ι → ℝ)) (ν : ι → ℝ) : Prop := ∀ j, ∃ n : ℤ, pair ν (b j) = n

lemma IsDual.pair_int {b : Module.Basis J ℝ (ι → ℝ)} {ν : ι → ℝ} (hν : IsDual b ν) (m : J → ℤ) :
    ∃ n : ℤ, pair ν (b.equivFun.symm (fun j => (m j : ℝ))) = n := by
  choose n hn using hν
  refine ⟨∑ j, m j * n j, ?_⟩
  rw [Module.Basis.equivFun_symm_apply]
  calc pair ν (∑ j, (m j : ℝ) • b j) = ∑ j, (m j : ℝ) * pair ν (b j) := by
        simp only [pair, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun u _ => by ring
    _ = _ := by simp [hn]

lemma measurableSet_unitCube : MeasurableSet (unitCube J) := by
  have : unitCube J = Set.pi univ (fun _ => Ioc (0:ℝ) 1) := by ext t; simp [unitCube]
  rw [this]; exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc

lemma unitCube_subset : unitCube J ⊆ Set.pi univ (fun _ => Icc (0:ℝ) 1) :=
  fun t ht j _ => Ioc_subset_Icc_self (ht j)

lemma ptXY_im {x y : ι → ℝ} (hy : ∀ v, 0 < y v) (v : ι) :
    ((ptXY x y v : ℍ) : ℂ) = (x v : ℂ) + (y v : ℂ) * Complex.I := by
  simp only [ptXY, toHPi]
  rw [ofComplex_apply_of_im_pos (by simpa using hy v)]

/-- **Holomorphy fixes the $y$-dependence, one variable at a time**:
$c_\nu(y + se_v) = e^{-2\pi\nu_vs}\,c_\nu(y)$ whenever $y > 0$ and $y_v + s > 0$. -/
lemma coeff_update [DecidableEq ι] {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)} {ν : ι → ℝ}
    (hf : IsHolomorphic f) (hper : IsLatticePeriodic f b) (hν : IsDual b ν)
    {y : ι → ℝ} (hy : ∀ v, 0 < y v) (v : ι) {s : ℝ} (hs : 0 < y v + s) :
    coeff f b ν (Function.update y v (y v + s)) =
      (Real.exp (-2 * π * ν v * s) : ℂ) * coeff f b ν y := by
  set x : (J → ℝ) → (ι → ℝ) := fun t => b.equivFun.symm t with hx
  set Z : (J → ℝ) → (ι → ℂ) := fun t u => (x t u : ℂ) + (y u : ℂ) * Complex.I with hZ
  set E : (J → ℝ) → ℂ → ℂ := fun t w =>
    cexp (-(2 * π * Complex.I) * ((pair ν (x t) : ℂ) + ν v * w)) with hE
  set h : (J → ℝ) → ℂ → ℂ := fun t w => f (toHPi (Z t + Pi.single v w)) * E t w with hh
  set U : Set ℂ := {w | -y v < w.im} with hUdef
  set K : Set (J → ℝ) := Set.pi univ (fun _ => Icc (0:ℝ) 1) with hKdef
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hxc : Continuous x := (b.equivFun.symm : (J → ℝ) →ₗ[ℝ] (ι → ℝ)).continuous_of_finiteDimensional
  have hZc : Continuous Z := continuous_pi fun u =>
    (Complex.continuous_ofReal.comp ((continuous_apply u).comp hxc)).add continuous_const
  have hEc : Continuous (Function.uncurry E) := by
    refine Complex.continuous_exp.comp (continuous_const.mul ?_)
    refine (Complex.continuous_ofReal.comp ?_).add (continuous_const.mul continuous_snd)
    exact (continuous_finsetSum _ fun u _ => continuous_const.mul
      ((continuous_apply u).comp hxc)).comp continuous_fst
  have hpos : ∀ t, ∀ w ∈ U, Z t + Pi.single v w ∈ posSet ι := by
    intro t w hw u
    by_cases huv : u = v
    · subst huv; simp only [Pi.add_apply, Pi.single_eq_same, add_im, hZ, ofReal_im, mul_im,
        ofReal_re, Complex.I_im, Complex.I_re, mul_zero, zero_add, mul_one]
      have := hw; simp only [hUdef, mem_setOf_eq] at this; linarith
    · simp [hZ, Pi.single_apply, huv, hy u]
  have hcont : ContinuousOn (Function.uncurry h) (K ×ˢ U) := by
    refine ContinuousOn.mul ?_ hEc.continuousOn
    refine (continuousOn_comp_toHPi hf.1).comp (Continuous.continuousOn ?_) ?_
    · exact (hZc.comp continuous_fst).add ((continuous_single v).comp continuous_snd)
    · rintro ⟨t, w⟩ ⟨-, hw⟩; exact hpos t w hw
  have hdiff : ∀ t ∈ K, DifferentiableOn ℂ (h t) U := by
    intro t _
    refine DifferentiableOn.mul ?_ ?_
    · have := differentiableOn_update hf (Z t) v
      have hZv : (Z t v).im = y v := by simp [hZ]
      rw [hZv] at this
      simp only [add_single_eq_update]
      exact this
    · exact (Complex.differentiable_exp.comp ((differentiable_const _).mul
        ((differentiable_const _).add ((differentiable_const _).mul differentiable_id)))).differentiableOn
  have hΦ := differentiableOn_setIntegral_of_compact unitCube_subset hK measurableSet_unitCube hU h
    hcont hdiff
  set Φ : ℂ → ℂ := fun w => ∫ t in unitCube J, h t w with hΦdef
  -- periodic integrand
  set G : (J → ℝ) → ℂ := fun t => f (ptXY (x t) y) *
    cexp (-(2 * π * Complex.I) * (pair ν (x t) : ℂ)) with hG
  have hGper : ∀ (m : J → ℤ) t, G (t + fun j => (m j : ℝ)) = G t := by
    intro m t
    simp only [hG, hx, map_add]
    rw [hper m _ y hy]
    obtain ⟨n, hn⟩ := hν.pair_int m
    rw [pair_add, hn]
    congr 1
    rw [show -(2 * π * Complex.I) * (((pair ν (b.equivFun.symm t) + n : ℝ)) : ℂ) =
      -(2 * π * Complex.I) * (pair ν (b.equivFun.symm t) : ℂ) + (-n : ℤ) * (2 * π * Complex.I) by
        push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  set a : J → ℝ := b.equivFun (Pi.single v 1) with ha
  have hxa : ∀ t (r : ℝ), x (t + r • a) = x t + Pi.single v r := by
    intro t r
    simp only [hx, ha, map_add, map_smul, LinearEquiv.symm_apply_apply]
    congr 1
    funext u; simp [Pi.single_apply]
  have hreal : ∀ r : ℝ, Φ r = coeff f b ν y := by
    intro r
    have : ∀ t, h t r = G (t + r • a) := by
      intro t
      simp only [hh, hG, hE, hxa]
      congr 1
      · congr 1
        funext u
        simp only [ptXY, toHPi, hZ, Pi.add_apply]
        congr 1
        by_cases huv : u = v
        · subst huv; simp; ring
        · simp [Pi.single_apply, huv]
      · rw [pair_add, pair_single]; push_cast; ring_nf
    simp only [hΦdef, this]
    rw [integral_unitCube_add G hGper]
    rfl
  -- identity theorem
  have hconst : EqOn Φ (fun _ => coeff f b ν y) U := by
    have hpc : IsPreconnected U := by
      have : Convex ℝ U := (convex_Ioi (-y v)).linear_preimage Complex.imLm
      exact this.isPreconnected
    have h0 : (0 : ℂ) ∈ U := by simp [hUdef, hy v]
    refine (hΦ.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const hpc h0 ?_
    have hseq : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have := (Complex.continuous_ofReal.tendsto 0).comp
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        exact this
      · simp only [mem_compl_iff, mem_singleton_iff, ofReal_eq_zero, one_div, inv_eq_zero]
        positivity
    exact hseq.frequently (Frequently.of_forall fun n => hreal _)
  -- evaluate at `s * I`
  have hsI : (s : ℂ) * Complex.I ∈ U := by
    simp only [hUdef, mem_setOf_eq, mul_im, ofReal_re, Complex.I_im, ofReal_im, Complex.I_re, mul_zero,
      add_zero, mul_one]
    linarith
  have hI : Φ ((s : ℂ) * Complex.I) =
      (Real.exp (2 * π * ν v * s) : ℂ) * coeff f b ν (Function.update y v (y v + s)) := by
    have : ∀ t, h t ((s : ℂ) * Complex.I) = (Real.exp (2 * π * ν v * s) : ℂ) *
        (f (ptXY (x t) (Function.update y v (y v + s))) *
          cexp (-(2 * π * Complex.I) * (pair ν (x t) : ℂ))) := by
      intro t
      simp only [hh, hE]
      have hpt : toHPi (Z t + Pi.single v ((s : ℂ) * Complex.I)) =
          ptXY (x t) (Function.update y v (y v + s)) := by
        funext u
        simp only [ptXY, toHPi, hZ, Pi.add_apply]
        congr 1
        by_cases huv : u = v
        · subst huv; simp; ring
        · simp [Pi.single_apply, huv, Function.update_of_ne huv]
      rw [hpt, Complex.ofReal_exp]
      rw [show -(2 * π * Complex.I) * ((pair ν (x t) : ℂ) + ν v * ((s : ℂ) * Complex.I)) =
        -(2 * π * Complex.I) * (pair ν (x t) : ℂ) + ((2 * π * ν v * s : ℝ) : ℂ) by
          push_cast; ring_nf; rw [Complex.I_sq]; ring, Complex.exp_add]
      ring
    simp only [hΦdef, this]
    rw [integral_const_mul]
    rfl
  have := hconst hsI
  rw [hI] at this
  simp only at this
  rw [← this, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  ring_nf
  simp


lemma add_single_eq_update_real [DecidableEq ι] (y : ι → ℝ) (v : ι) (r : ℝ) :
    Function.update y v (y v + r) = y + Pi.single v r := by
  funext u
  by_cases h : u = v
  · subst h; simp
  · simp [Function.update_of_ne h, Pi.single_apply, h]

/-- **The $y$-dependence of the Fourier coefficients**: $c_\nu(y') = e^{-2\pi\langle\nu, y' - y\rangle}\,c_\nu(y)$ for all
$y, y' \in \mathbb{R}_{>0}^\iota$ ($f$ holomorphic and $\Lambda$-periodic, $\nu$ in the dual lattice). -/
theorem coeff_eq_exp_mul [DecidableEq ι] {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)}
    {ν : ι → ℝ} (hf : IsHolomorphic f) (hper : IsLatticePeriodic f b) (hν : IsDual b ν)
    {y y' : ι → ℝ} (hy : ∀ v, 0 < y v) (hy' : ∀ v, 0 < y' v) :
    coeff f b ν y' = (Real.exp (-2 * π * pair ν (y' - y)) : ℂ) * coeff f b ν y := by
  have key : ∀ s : Finset ι, coeff f b ν (fun u => if u ∈ s then y' u else y u) =
      (Real.exp (-2 * π * pair ν ((fun u => if u ∈ s then y' u else y u) - y)) : ℂ) *
        coeff f b ν y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [pair]
    | insert v s hv ih =>
      set ys : ι → ℝ := fun u => if u ∈ s then y' u else y u with hysdef
      have hys : ∀ u, 0 < ys u := fun u => by
        simp only [hysdef]; split_ifs; exacts [hy' u, hy u]
      have hyv : ys v = y v := by simp [hysdef, hv]
      have heq : (fun u => if u ∈ insert v s then y' u else y u) =
          Function.update ys v (ys v + (y' v - y v)) := by
        funext u
        by_cases huv : u = v
        · subst huv; simp [hyv]
        · simp [Function.update_of_ne huv, Finset.mem_insert, huv, hysdef]
      rw [heq, coeff_update hf hper hν hys v (by rw [hyv]; linarith [hy' v]), ih,
        ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, add_single_eq_update_real,
        show ys + Pi.single v (y' v - y v) - y = (ys - y) + Pi.single v (y' v - y v) by abel,
        pair_add, pair_single]
      congr 3
      ring
  have h := key Finset.univ
  simp only [Finset.mem_univ, if_true] at h
  exact h

/-- **The $q$-coefficient** $a_\nu = c_\nu(\mathbf 1)\,e^{2\pi\langle\nu, \mathbf 1\rangle}$ ($\mathbf 1 = (1, \dots, 1)$), so that
$c_\nu(y) = a_\nu e^{-2\pi\langle\nu, y\rangle}$ (`coeff_eq_qCoeff`). -/
noncomputable def qCoeff (f : (ι → ℍ) → ℂ) (b : Module.Basis J ℝ (ι → ℝ)) (ν : ι → ℝ) : ℂ :=
  coeff f b ν 1 * (Real.exp (2 * π * pair ν 1) : ℂ)

theorem coeff_eq_qCoeff [DecidableEq ι] {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)}
    {ν : ι → ℝ} (hf : IsHolomorphic f) (hper : IsLatticePeriodic f b) (hν : IsDual b ν)
    {y : ι → ℝ} (hy : ∀ v, 0 < y v) :
    coeff f b ν y = qCoeff f b ν * (Real.exp (-2 * π * pair ν y) : ℂ) := by
  have h := coeff_eq_exp_mul hf hper hν (y := 1) (fun _ => one_pos) hy
  rw [h, qCoeff, pair_sub, show -2 * π * (pair ν y - pair ν 1) =
    2 * π * pair ν 1 + -2 * π * pair ν y by ring, Real.exp_add, Complex.ofReal_mul]
  ring

lemma continuous_ptXY {y : ι → ℝ} (hy : ∀ v, 0 < y v) {f : (ι → ℍ) → ℂ} (hf : Continuous f) :
    Continuous fun x : ι → ℝ => f (ptXY x y) := by
  refine (continuousOn_comp_toHPi hf).comp_continuous ?_ fun x v => by simpa using hy v
  exact continuous_pi fun u => (Complex.continuous_ofReal.comp (continuous_apply u)).add
    continuous_const

/-- **Horizontal slices are bounded**: a continuous $\Lambda$-periodic $f$ is bounded on $\{x + iy : x \in \mathbb{R}^\iota\}$. -/
lemma exists_bound_slice {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)} (hf : Continuous f)
    (hper : IsLatticePeriodic f b) {y : ι → ℝ} (hy : ∀ v, 0 < y v) :
    ∃ B, ∀ x, ‖f (ptXY x y)‖ ≤ B := by
  have hK : IsCompact (Set.pi univ (fun _ : J => Icc (0:ℝ) 1)) := isCompact_univ_pi fun _ => isCompact_Icc
  have hg : Continuous fun t : J → ℝ => f (ptXY (b.equivFun.symm t) y) :=
    (continuous_ptXY hy hf).comp
      (b.equivFun.symm : (J → ℝ) →ₗ[ℝ] (ι → ℝ)).continuous_of_finiteDimensional
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨B, fun x => ?_⟩
  set t := b.equivFun x
  set m : J → ℤ := fun j => ⌊t j⌋
  have hx : x = b.equivFun.symm (t - fun j => (m j : ℝ)) + b.equivFun.symm (fun j => (m j : ℝ)) := by
    rw [← map_add, sub_add_cancel]; simp [t]
  rw [hx, hper m _ y hy]
  refine hB _ fun j _ => ?_
  simp only [Pi.sub_apply, m]
  exact ⟨by linarith [Int.floor_le (t j)], by linarith [Int.lt_floor_add_one (t j)]⟩

lemma volume_unitCube : volume (unitCube J) = 1 := by
  have : unitCube J = Set.pi univ (fun _ => Ioc (0:ℝ) 1) := by ext t; simp [unitCube]
  rw [this, Real.volume_pi_Ioc]
  simp

/-- $|c_\nu(y)| \le \sup_x|f(x + iy)|$. -/
lemma norm_coeff_le {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)} {ν y : ι → ℝ} {B : ℝ}
    (hB : ∀ x, ‖f (ptXY x y)‖ ≤ B) : ‖coeff f b ν y‖ ≤ B := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := unitCube J)
    (f := fun t => f (ptXY (b.equivFun.symm t) y) *
      cexp (-(2 * π * Complex.I) * (pair ν (b.equivFun.symm t) : ℂ))) (C := B)
    (by rw [volume_unitCube]; exact ENNReal.one_lt_top) (fun t _ => ?_)
  · rw [measureReal_def, volume_unitCube, ENNReal.toReal_one, mul_one] at h
    exact h
  · rw [norm_mul, show -(2 * π * Complex.I) * (pair ν (b.equivFun.symm t) : ℂ) =
      ((-(2 * π * pair ν (b.equivFun.symm t)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hB _


/-- If $\|c(y_n)\| \le B$ along a sequence with $\langle\nu, y_n - y\rangle \to -\infty$, then $c_\nu(y) = 0$. -/
lemma coeff_eq_zero_of_tendsto [DecidableEq ι] {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)}
    {ν : ι → ℝ} (hf : IsHolomorphic f) (hper : IsLatticePeriodic f b) (hν : IsDual b ν)
    {y : ι → ℝ} (hy : ∀ v, 0 < y v) (yn : ℕ → ι → ℝ) (hyn : ∀ n v, 0 < yn n v) {B : ℝ}
    (hB : ∀ n, ‖coeff f b ν (yn n)‖ ≤ B)
    (hlim : Tendsto (fun n => pair ν (yn n - y)) atTop atBot) : coeff f b ν y = 0 := by
  have hle : ∀ n, ‖coeff f b ν y‖ ≤ B * Real.exp (2 * π * pair ν (yn n - y)) := by
    intro n
    have h := coeff_eq_exp_mul hf hper hν hy (hyn n)
    have hpos : 0 < Real.exp (-2 * π * pair ν (yn n - y)) := Real.exp_pos _
    have : ‖coeff f b ν (yn n)‖ = Real.exp (-2 * π * pair ν (yn n - y)) * ‖coeff f b ν y‖ := by
      rw [h, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    have h2 : Real.exp (-2 * π * pair ν (yn n - y)) * ‖coeff f b ν y‖ ≤ B := this ▸ hB n
    have h3 : Real.exp (2 * π * pair ν (yn n - y)) * Real.exp (-2 * π * pair ν (yn n - y)) = 1 := by
      rw [← Real.exp_add]; simp
    calc ‖coeff f b ν y‖ = Real.exp (2 * π * pair ν (yn n - y)) *
          (Real.exp (-2 * π * pair ν (yn n - y)) * ‖coeff f b ν y‖) := by
            rw [← mul_assoc, h3, one_mul]
      _ ≤ Real.exp (2 * π * pair ν (yn n - y)) * B :=
            mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = B * Real.exp (2 * π * pair ν (yn n - y)) := mul_comm _ _
  have ht : Tendsto (fun n => B * Real.exp (2 * π * pair ν (yn n - y))) atTop (𝓝 0) := by
    have : Tendsto (fun n => Real.exp (2 * π * pair ν (yn n - y))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (hlim.const_mul_atBot (by positivity))
    simpa using this.const_mul B
  have h0 : ‖coeff f b ν y‖ ≤ 0 := ge_of_tendsto' ht hle
  exact norm_le_zero_iff.mp h0

/-- **Coefficients of forms bounded at $i\infty$ live on $\nu \ge 0$.** If $|f(z)| \le B$ whenever $\operatorname{Im} z_v \ge A$ for all
$v$, and $\nu_w < 0$ for some $w$, then $c_\nu \equiv 0$. -/
theorem coeff_eq_zero_of_isBounded [DecidableEq ι] {f : (ι → ℍ) → ℂ}
    {b : Module.Basis J ℝ (ι → ℝ)} {ν : ι → ℝ} (hf : IsHolomorphic f)
    (hper : IsLatticePeriodic f b) (hν : IsDual b ν) {A B : ℝ}
    (hbd : ∀ x y, (∀ v, A ≤ y v) → (∀ v, 0 < y v) → ‖f (ptXY x y)‖ ≤ B)
    {w : ι} (hνw : ν w < 0) {y : ι → ℝ} (hy : ∀ v, 0 < y v) : coeff f b ν y = 0 := by
  set yn : ℕ → ι → ℝ := fun n => y + (fun _ => |A|) + Pi.single w (n : ℝ) with hyn
  have hge : ∀ n v, |A| + y v ≤ yn n v := by
    intro n v
    simp only [hyn, Pi.add_apply, Pi.single_apply]
    split_ifs <;> linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hpos : ∀ n v, 0 < yn n v := fun n v =>
    lt_of_lt_of_le (by linarith [abs_nonneg A, hy v]) (hge n v)
  refine coeff_eq_zero_of_tendsto hf hper hν hy yn hpos (B := B) (fun n => norm_coeff_le
    fun x => hbd x _ (fun v => le_trans (le_abs_self A) (by linarith [hge n v, hy v])) (hpos n)) ?_
  have : (fun n : ℕ => pair ν (yn n - y)) = fun n : ℕ => pair ν (fun _ => |A|) + ν w * (n : ℝ) := by
    funext n
    simp only [hyn]
    rw [show (y + fun _ => |A|) + Pi.single w (n : ℝ) - y = (fun _ => |A|) + Pi.single w (n : ℝ) by
      abel, pair_add, pair_single]
  rw [this]
  exact tendsto_atBot_add_const_left _ _
    ((tendsto_natCast_atTop_atTop).const_mul_atTop_of_neg hνw)

/-- Iterated scaling: $|f(\varepsilon^nx + i\varepsilon^ny)| = |f(x + iy)|$. -/
lemma norm_scale_pow {f : (ι → ℍ) → ℂ} {ε : ι → ℝ}
    (hfε : ∀ x y, (∀ v, 0 < y v) → ‖f (ptXY (ε * x) (ε * y))‖ = ‖f (ptXY x y)‖)
    (hε : ∀ v, 0 < ε v) (n : ℕ) (x y : ι → ℝ) (hy : ∀ v, 0 < y v) :
    ‖f (ptXY (ε ^ n * x) (ε ^ n * y))‖ = ‖f (ptXY x y)‖ := by
  induction n generalizing x y with
  | zero => simp
  | succ n ih =>
    have hy' : ∀ v, 0 < (ε ^ n * y) v := fun v => by
      simp only [Pi.mul_apply, Pi.pow_apply]; exact mul_pos (pow_pos (hε v) n) (hy v)
    rw [← ih x y hy, ← hfε _ _ hy', pow_succ', mul_assoc, mul_assoc]

/-- **The Koecher principle, analytic core.** Let $f$ be holomorphic on $\mathbb{H}^\iota$ and $\Lambda$-periodic, $\nu$ in the
dual lattice, and $\varepsilon \in \mathbb{R}^\iota_{>0}$ with $|f(\varepsilon z)| = |f(z)|$ (componentwise scaling
$\varepsilon z = (\varepsilon_vz_v)_v$), $\varepsilon_w > 1$ and $\varepsilon_v < 1$ for $v \ne w$. If $\nu_w < 0$, then
$c_\nu(y) = 0$ for all $y > 0$. No growth condition at the cusp is assumed. -/
@[kb "freitag1990" "Ch. I, §4, Koecher principle [unverified]"]
theorem koecher_coeff_eq_zero [DecidableEq ι] {f : (ι → ℍ) → ℂ}
    {b : Module.Basis J ℝ (ι → ℝ)} {ν : ι → ℝ} (hf : IsHolomorphic f)
    (hper : IsLatticePeriodic f b) (hν : IsDual b ν) {ε : ι → ℝ} (hε : ∀ v, 0 < ε v)
    (hfε : ∀ x y, (∀ v, 0 < y v) → ‖f (ptXY (ε * x) (ε * y))‖ = ‖f (ptXY x y)‖)
    {w : ι} (hνw : ν w < 0) (hεw : 1 < ε w) (hεv : ∀ v ≠ w, ε v < 1)
    {y : ι → ℝ} (hy : ∀ v, 0 < y v) : coeff f b ν y = 0 := by
  obtain ⟨B, hB⟩ := exists_bound_slice hf.1 hper hy
  set yn : ℕ → ι → ℝ := fun n => ε ^ n * y with hyn
  have hpos : ∀ n v, 0 < yn n v := fun n v => by
    simp only [hyn, Pi.mul_apply, Pi.pow_apply]; exact mul_pos (pow_pos (hε v) n) (hy v)
  have hbd : ∀ n x, ‖f (ptXY x (yn n))‖ ≤ B := by
    intro n x
    have hx : x = ε ^ n * ((ε ^ n)⁻¹ * x) := by
      funext v
      simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply]
      rw [← mul_assoc, mul_inv_cancel₀ (pow_pos (hε v) n).ne', one_mul]
    rw [hx, norm_scale_pow hfε hε n _ y hy]
    exact hB _
  refine coeff_eq_zero_of_tendsto hf hper hν hy yn hpos (fun n => norm_coeff_le (hbd n)) ?_
  have hsplit : ∀ n, pair ν (yn n - y) = ν w * (ε w ^ n * y w - y w) +
      ∑ v ∈ Finset.univ.erase w, ν v * (ε v ^ n * y v - y v) := by
    intro n
    rw [pair, ← Finset.add_sum_erase _ _ (Finset.mem_univ w)]
    simp [hyn]
  simp only [hsplit]
  refine Tendsto.atBot_add (C := ∑ v ∈ Finset.univ.erase w, ν v * (0 * y v - y v)) ?_
    (tendsto_finsetSum _ fun v hv => ?_)
  · have h1 : Tendsto (fun n : ℕ => ε w ^ n * y w - y w) atTop atTop :=
      tendsto_atTop_add_const_right _ _
        ((tendsto_pow_atTop_atTop_of_one_lt hεw).atTop_mul_const (hy w))
    exact h1.const_mul_atTop_of_neg hνw
  · have h1 : Tendsto (fun n : ℕ => ε v ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (hε v).le (hεv v (Finset.ne_of_mem_erase hv))
    exact ((h1.mul_const (y v)).sub_const (y v)).const_mul (ν v)

end QuadFormsKB.HilbertModular
