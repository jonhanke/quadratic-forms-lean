/-
# Fourier expansion of a periodic holomorphic function on a tube domain

**Layer:** complex analysis (no arithmetic input).

**Setting.** Let $\iota$ be a finite index type and $K \subseteq \mathbb R^\iota$ an open convex set (the allowed imaginary parts).
Let $f : \mathbb C^\iota \to \mathbb C$ be periodic, $f(t + m) = f(t)$ for $m \in \mathbb Z^\iota$, continuous in the real parts
$x$ on every slice $t = x + iy$ with $y \in K$, and holomorphic in each complex variable separately on the tube
$\{x + iy : y \in K\}$. Write $\operatorname{cplx}(x, y) = x + iy$, $\mathrm{dotZ}(n, t) = \sum_i n_it_i$ and
$\mathrm{charZ}(n, t) = e^{2\pi i\,\mathrm{dotZ}(n,t)}$. The coefficient of $f$ at $y$ is
$$c_n(y) = \int_{(0,1]^\iota} f(x + iy)\,e^{-2\pi i\,n\cdot(x + iy)}\,dx$$
(`coeffY`; the integral is over the half-open unit box `unitBox`, the form in which Mathlib's `UnitAddTorus` integrals are stated).

**Results.**
* **`coeffY_const`**: $c_n(y)$ does not depend on $y \in K$. (Cauchy's theorem on a rectangle in one variable at a time,
  the vertical sides cancelling by periodicity; the integral over the other coordinates is handled by translation
  invariance on the torus `UnitAddTorus ι` and Fubini, `integral_unitBox_eq_slice`.)
* **`hasSum_expansion`**: if $y = \operatorname{Im}t \in K$ and $\sum_n|c_n(y)e^{2\pi i\,n\cdot t}| < \infty$, then
  $f(t) = \sum_{n\in\mathbb Z^\iota}c_n(y)\,e^{2\pi i\,n\cdot t}$ (Mathlib's pointwise Fourier inversion on the torus,
  `UnitAddTorus.hasSum_mFourier_series_apply_of_summable`). By `coeffY_const` the coefficients $a_n = c_n(y)$ are independent of $y$.
  (Convention check: $e^{-2\pi i\,n\cdot(x+iy)} = e^{-2\pi i\,n\cdot x}e^{2\pi\,n\cdot y}$, so $c_n(y)$ is already the
  $y$-independent coefficient; no extra factor $e^{\pm2\pi\,n\cdot y}$ appears.)
* **`coeffY_eq_zero_of_bounded`** (Koecher's principle): if $K$ is moreover a cone and $f$ is bounded on
  $\{t : \operatorname{Im}t - y_0 \in K\}$, then $a_n = 0$ unless $n\cdot y \ge 0$ for all $y \in K$.

Source: Freitag, *Siegelsche Modulfunktionen* (1983), Ch. I (Fourier expansion and Koecher's principle) [unverified].
-/
import Mathlib

open MeasureTheory Complex Set
open scoped Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms.HolExp

/-- The measure on the circle $\mathbb R/\mathbb Z$ used by Mathlib's `UnitAddTorus` Fourier analysis
(normalized Haar measure), reinstated locally as in `Mathlib/Analysis/Fourier/AddCircleMulti.lean`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The measure on the torus $(\mathbb R/\mathbb Z)^\iota$ is invariant under translation. -/
instance torus_isAddRightInvariant : (volume : Measure (UnitAddTorus ι)).IsAddRightInvariant := by
  show (Measure.pi fun _ : ι => (AddCircle.haarAddCircle : Measure UnitAddCircle)).IsAddRightInvariant
  infer_instance

/-- The half-open unit box $(0, 1]^\iota \subseteq \mathbb R^\iota$. -/
def unitBox (ι : Type*) : Set (ι → ℝ) := {x | ∀ i, x i ∈ Ioc (0:ℝ) 1}

/-- The unit box is measurable. -/
lemma measurableSet_unitBox : MeasurableSet (unitBox ι) := by
  have := MeasurableSet.univ_pi (fun _ : ι => (measurableSet_Ioc : MeasurableSet (Ioc (0:ℝ) 1)))
  simpa [unitBox, Set.pi] using this

/-- The half-open unit box lies in the closed unit box. -/
lemma unitBox_subset_Icc : unitBox ι ⊆ Icc 0 1 :=
  fun _ hx => ⟨fun i => (hx i).1.le, fun i => (hx i).2⟩

/-- The unit box in the form used by Mathlib's `UnitAddTorus.integral_preimage` (base point $a = 0$). -/
lemma unitBox_eq :
    unitBox ι = {x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} := by
  simp [unitBox]

/-- The quotient map $\mathbb R^\iota \to (\mathbb R/\mathbb Z)^\iota$. -/
def toTorus (x : ι → ℝ) : UnitAddTorus ι := fun i => (x i : UnitAddCircle)

/-- `toTorus` is an open quotient map. -/
lemma toTorus_isOpenQuotientMap : IsOpenQuotientMap (toTorus (ι := ι)) := by
  have : ∀ _ : ι, IsOpenQuotientMap ((↑) : ℝ → UnitAddCircle) :=
    fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  exact IsOpenQuotientMap.piMap this

/-- Two points with the same image in the torus differ by an integer vector. -/
lemma toTorus_eq_iff {x x' : ι → ℝ} (h : toTorus x' = toTorus x) :
    ∃ m : ι → ℤ, x' = x + fun i => (m i : ℝ) := by
  have : ∀ i, ∃ k : ℤ, x' i = x i + k := by
    intro i
    have := congrFun h i
    simp only [toTorus] at this
    rw [QuotientAddGroup.eq] at this
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp this
    exact ⟨-k, by push_cast; simp at hk; linarith⟩
  choose m hm using this
  exact ⟨m, funext fun i => hm i⟩

/-- `toTorus` is additive. -/
lemma toTorus_add (x c : ι → ℝ) : toTorus (x + c) = toTorus x + toTorus c := by
  funext i
  simp [toTorus]

/-- A function on $\mathbb R^\iota$ is periodic if it is invariant under translation by integer vectors. -/
def IsIntPeriodic (H : (ι → ℝ) → ℂ) : Prop :=
  ∀ (x : ι → ℝ) (m : ι → ℤ), H (x + fun i => (m i : ℝ)) = H x

/-- An integer-periodic function descends to the torus. -/
lemma exists_lift {H : (ι → ℝ) → ℂ} (hH : IsIntPeriodic H) :
    ∃ g : UnitAddTorus ι → ℂ, ∀ x, g (toTorus x) = H x := by
  obtain ⟨s, hs⟩ := (toTorus_isOpenQuotientMap (ι := ι)).surjective.hasRightInverse
  refine ⟨fun z => H (s z), fun x => ?_⟩
  obtain ⟨m, hm⟩ := toTorus_eq_iff (hs (toTorus x))
  simp only [hm]
  exact hH x m

/-- The descent of a continuous periodic function is continuous. -/
lemma continuous_of_lift {H : (ι → ℝ) → ℂ} {g : UnitAddTorus ι → ℂ}
    (hg : ∀ x, g (toTorus x) = H x) (hc : Continuous H) : Continuous g := by
  rw [toTorus_isOpenQuotientMap.isQuotientMap.continuous_iff]
  have : g ∘ toTorus = H := funext hg
  rw [this]; exact hc

/-- The integral of a periodic function over the unit box is invariant under translation. -/
lemma setIntegral_unitBox_shift {H : (ι → ℝ) → ℂ} (hH : IsIntPeriodic H) (c : ι → ℝ) :
    ∫ x in unitBox ι, H (x + c) = ∫ x in unitBox ι, H x := by
  obtain ⟨g, hg⟩ := exists_lift hH
  have h1 := integral_add_right_eq_self (μ := (volume : Measure (UnitAddTorus ι))) g (toTorus c)
  have h2 := UnitAddTorus.integral_preimage (fun z => g (z + toTorus c)) (0 : ι → ℝ)
  have h3 := UnitAddTorus.integral_preimage g (0 : ι → ℝ)
  rw [← unitBox_eq] at h2 h3
  calc ∫ x in unitBox ι, H (x + c) = ∫ x in unitBox ι, g (toTorus x + toTorus c) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show H (x + c) = g (toTorus x + toTorus c)
        rw [← toTorus_add, hg]
    _ = ∫ z : UnitAddTorus ι, g (z + toTorus c) := h2.symm
    _ = ∫ z : UnitAddTorus ι, g z := h1
    _ = ∫ x in unitBox ι, g (toTorus x) := h3
    _ = ∫ x in unitBox ι, H x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        exact hg x

/-- For continuous periodic $H$, the integral over the unit box equals the integral over the box of the
average of $H$ along a unit segment in direction $i$ (Fubini plus translation invariance). -/
lemma integral_unitBox_eq_slice {H : (ι → ℝ) → ℂ} (hH : IsIntPeriodic H) (hc : Continuous H)
    (i : ι) :
    ∫ x in unitBox ι, H x = ∫ x in unitBox ι, ∫ a in (0 : ℝ)..1, H (x + Pi.single i a) := by
  have hint : Integrable (Function.uncurry fun (x : ι → ℝ) (a : ℝ) => H (x + Pi.single i a))
      ((volume.restrict (unitBox ι)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    have hcont : Continuous
        (Function.uncurry fun (x : ι → ℝ) (a : ℝ) => H (x + Pi.single i a)) := by
      refine hc.comp ?_
      exact continuous_fst.add ((continuous_single i).comp continuous_snd)
    have hK : IsCompact ((Icc (0 : ι → ℝ) 1) ×ˢ (Icc (0 : ℝ) 1)) :=
      isCompact_Icc.prod isCompact_Icc
    have := hcont.continuousOn.integrableOn_compact (μ := (volume : Measure ((ι → ℝ) × ℝ))) hK
    exact this.mono_set (prod_mono unitBox_subset_Icc Ioc_subset_Icc_self)
  have e1 : ∀ x : ι → ℝ, ∫ a in (0 : ℝ)..1, H (x + Pi.single i a)
      = ∫ a in Ioc (0 : ℝ) 1, H (x + Pi.single i a) :=
    fun x => intervalIntegral.integral_of_le zero_le_one
  simp_rw [e1]
  rw [integral_integral_swap hint]
  have e2 : ∀ a : ℝ, ∫ x in unitBox ι, H (x + Pi.single i a) = ∫ x in unitBox ι, H x :=
    fun a => setIntegral_unitBox_shift hH _
  simp_rw [e2]
  simp

/-- Cauchy's theorem on a rectangle: for $\varphi : \mathbb C \to \mathbb C$ with $\varphi(u + 1) = \varphi(u)$,
holomorphic on the strip $\operatorname{Im} w \in [b, b']$, the integral over one period of
$\varphi(\cdot + ib)$ equals that of $\varphi(\cdot + ib')$. -/
lemma integral_period_eq {φ : ℂ → ℂ} (hper : ∀ u, φ (u + 1) = φ u) (r b b' : ℝ)
    (hd : ∀ w : ℂ, w.im ∈ uIcc b b' → DifferentiableAt ℂ φ w) :
    ∫ a in (0 : ℝ)..1, φ (((r + a : ℝ) : ℂ) + (b : ℂ) * Complex.I)
      = ∫ a in (0 : ℝ)..1, φ (((r + a : ℝ) : ℂ) + (b' : ℂ) * Complex.I) := by
  set z : ℂ := (r : ℂ) + (b : ℂ) * Complex.I with hz
  set w : ℂ := ((r + 1 : ℝ) : ℂ) + (b' : ℂ) * Complex.I with hw
  have hzre : z.re = r := by simp [hz]
  have hzim : z.im = b := by simp [hz]
  have hwre : w.re = r + 1 := by simp [hw]
  have hwim : w.im = b' := by simp [hw]
  have hrect : DifferentiableOn ℂ φ (uIcc z.re w.re ×ℂ uIcc z.im w.im) := by
    intro p hp
    refine (hd p ?_).differentiableWithinAt
    have := hp.2
    rwa [hzim, hwim] at this
  have hC := Complex.integral_boundary_rect_eq_zero_of_differentiableOn φ z w hrect
  have hvert : (∫ y : ℝ in z.im..w.im, φ (w.re + y * Complex.I))
      = ∫ y : ℝ in z.im..w.im, φ (z.re + y * Complex.I) := by
    refine intervalIntegral.integral_congr fun y _ => ?_
    have : (w.re : ℂ) + y * Complex.I = ((z.re : ℂ) + y * Complex.I) + 1 := by
      rw [hwre, hzre]; push_cast; ring
    rw [this, hper]
  rw [hvert, add_sub_cancel_right] at hC
  rw [hzre, hwre, hzim, hwim] at hC
  have h1 := intervalIntegral.integral_comp_add_left
    (fun s : ℝ => φ ((s : ℂ) + (b : ℂ) * Complex.I)) (a := 0) (b := 1) r
  have h2 := intervalIntegral.integral_comp_add_left
    (fun s : ℝ => φ ((s : ℂ) + (b' : ℂ) * Complex.I)) (a := 0) (b := 1) r
  simp only [add_zero] at h1 h2
  rw [h1, h2]
  exact sub_eq_zero.mp hC

/-- The complex point $x + iy$ with real part $x$ and imaginary part $y$. -/
def cplx (x y : ι → ℝ) : ι → ℂ := fun i => (x i : ℂ) + (y i : ℂ) * Complex.I

/-- The pairing $\sum_i n_it_i$ of an integer vector with a complex vector. -/
def dotZ (n : ι → ℤ) (t : ι → ℂ) : ℂ := ∑ i, (n i : ℂ) * t i

/-- The character $t \mapsto e^{2\pi i\,n\cdot t}$. -/
def charZ (n : ι → ℤ) (t : ι → ℂ) : ℂ := Complex.exp (2 * π * Complex.I * dotZ n t)

/-- **The Fourier coefficient at height $y$:**
$c_n(y) = \int_{(0,1]^\iota}f(x + iy)\,e^{-2\pi i\,n\cdot(x+iy)}\,dx$. -/
def coeffY (f : (ι → ℂ) → ℂ) (n : ι → ℤ) (y : ι → ℝ) : ℂ :=
  ∫ x in unitBox ι, f (cplx x y) * charZ (-n) (cplx x y)

/-- Shifting the real part along coordinate $i$ and replacing the imaginary part of coordinate $i$
amounts to replacing the $i$-th complex coordinate. -/
lemma cplx_shift (x y : ι → ℝ) (i : ι) (a s : ℝ) :
    cplx (x + Pi.single i a) (Function.update y i s)
      = Function.update (cplx x y) i (((x i + a : ℝ) : ℂ) + (s : ℂ) * Complex.I) := by
  funext j
  by_cases h : j = i
  · subst h; simp [cplx]
  · simp [cplx, h]

/-- The case $s = y_i$ of `cplx_shift`. -/
lemma cplx_shift_self (x y : ι → ℝ) (i : ι) (a : ℝ) :
    cplx (x + Pi.single i a) y
      = Function.update (cplx x y) i (((x i + a : ℝ) : ℂ) + (y i : ℂ) * Complex.I) := by
  rw [← cplx_shift, Function.update_eq_self]

/-- Replacing coordinate $i$ of a complex point does not depend on the old $i$-th coordinate. -/
lemma update_cplx_update (x y : ι → ℝ) (i : ι) (a b : ℝ) (v : ℂ) :
    Function.update (cplx (Function.update x i a) (Function.update y i b)) i v
      = Function.update (cplx x y) i v := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [cplx, h]

/-- Translating the real part by an integer vector translates `cplx` by the same vector. -/
lemma cplx_add_int (x y : ι → ℝ) (m : ι → ℤ) :
    cplx (x + fun i => (m i : ℝ)) y = cplx x y + fun i => (m i : ℂ) := by
  funext i
  simp [cplx]
  ring

/-- The character is periodic under translation by integer vectors. -/
lemma charZ_add_int (n m : ι → ℤ) (t : ι → ℂ) :
    charZ n (t + fun i => (m i : ℂ)) = charZ n t := by
  have h : dotZ n (t + fun i => (m i : ℂ)) = dotZ n t + ((∑ i, n i * m i : ℤ) : ℂ) := by
    simp only [dotZ, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    push_cast
    rfl
  unfold charZ
  rw [h, mul_add, Complex.exp_add]
  have : 2 * (π : ℂ) * Complex.I * ((∑ i, n i * m i : ℤ) : ℂ)
      = ((∑ i, n i * m i : ℤ) : ℂ) * (2 * π * Complex.I) := by ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The character is continuous in the real part. -/
lemma continuous_charZ_cplx (n : ι → ℤ) (y : ι → ℝ) :
    Continuous fun x : ι → ℝ => charZ n (cplx x y) := by
  unfold charZ dotZ cplx
  fun_prop

/-- The character is holomorphic in each complex variable separately. -/
lemma differentiableAt_charZ_update (n : ι → ℤ) (t : ι → ℂ) (i : ι) (s₀ : ℂ) :
    DifferentiableAt ℂ (fun s => charZ n (Function.update t i s)) s₀ := by
  unfold charZ dotZ
  refine DifferentiableAt.cexp ?_
  refine (differentiableAt_const _).mul ?_
  refine DifferentiableAt.fun_sum fun j _ => ?_
  by_cases h : j = i
  · subst h; simp; fun_prop
  · simp [Function.update_of_ne h]

section Main

variable {K : Set (ι → ℝ)} {f : (ι → ℂ) → ℂ}

/-- The integrand of `coeffY` is periodic in the real part. -/
lemma isIntPeriodic_integrand
    (hper : ∀ (t : ι → ℂ) (n : ι → ℤ), f (t + fun i => (n i : ℂ)) = f t)
    (n : ι → ℤ) (y : ι → ℝ) :
    IsIntPeriodic fun x : ι → ℝ => f (cplx x y) * charZ (-n) (cplx x y) := by
  intro x m
  simp only
  rw [cplx_add_int, hper, charZ_add_int]

/-- **Moving one coordinate of the height:** if the segment from $y$ to $y$ with $y_i$ replaced by $s$
lies in $K$, then $c_n$ takes the same value at both ends. -/
lemma coeffY_update_eq
    (hper : ∀ (t : ι → ℂ) (n : ι → ℤ), f (t + fun i => (n i : ℂ)) = f t)
    (hcont : ∀ y ∈ K, Continuous fun x : ι → ℝ => f (cplx x y))
    (hhol : ∀ (x y : ι → ℝ), y ∈ K → ∀ i, DifferentiableAt ℂ
      (fun s : ℂ => f (Function.update (cplx x y) i s)) ((x i : ℂ) + (y i : ℂ) * Complex.I))
    (n : ι → ℤ) {y : ι → ℝ} (hy : y ∈ K) (i : ι) (s : ℝ)
    (hseg : ∀ u ∈ uIcc (y i) s, Function.update y i u ∈ K) :
    coeffY f n (Function.update y i s) = coeffY f n y := by
  have hy' : Function.update y i s ∈ K := hseg s right_mem_uIcc
  unfold coeffY
  rw [integral_unitBox_eq_slice (isIntPeriodic_integrand hper n _)
      ((hcont _ hy').mul (continuous_charZ_cplx _ _)) i,
    integral_unitBox_eq_slice (isIntPeriodic_integrand hper n _)
      ((hcont _ hy).mul (continuous_charZ_cplx _ _)) i]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show _ = _
  set φ : ℂ → ℂ := fun w => f (Function.update (cplx x y) i w)
    * charZ (-n) (Function.update (cplx x y) i w) with hφ
  have hperφ : ∀ u, φ (u + 1) = φ u := by
    intro u
    have : Function.update (cplx x y) i (u + 1)
        = Function.update (cplx x y) i u + fun j => (((Pi.single i 1 : ι → ℤ) j : ℤ) : ℂ) := by
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
    simp only [hφ]
    rw [this, hper, charZ_add_int]
  have hd : ∀ w : ℂ, w.im ∈ uIcc (y i) s → DifferentiableAt ℂ φ w := by
    intro w hw
    have h1 := hhol (Function.update x i w.re) (Function.update y i w.im)
      (hseg _ hw) i
    simp only [update_cplx_update, Function.update_self, Complex.re_add_im] at h1
    exact h1.mul (differentiableAt_charZ_update (-n) _ i _)
  have key := integral_period_eq hperφ (x i) (y i) s hd
  have e1 : ∀ a : ℝ, f (cplx (x + Pi.single i a) y) * charZ (-n) (cplx (x + Pi.single i a) y)
      = φ (((x i + a : ℝ) : ℂ) + (y i : ℂ) * Complex.I) := by
    intro a; rw [cplx_shift_self]
  have e2 : ∀ a : ℝ, f (cplx (x + Pi.single i a) (Function.update y i s))
      * charZ (-n) (cplx (x + Pi.single i a) (Function.update y i s))
      = φ (((x i + a : ℝ) : ℂ) + (s : ℂ) * Complex.I) := by
    intro a; rw [cplx_shift]
  simp_rw [e1, e2]
  exact key.symm

/-- **Local constancy:** $c_n$ is constant on every sup-norm ball contained in $K$
(move one coordinate at a time to the centre). -/
lemma coeffY_eq_of_mem_ball
    (hper : ∀ (t : ι → ℂ) (n : ι → ℤ), f (t + fun i => (n i : ℂ)) = f t)
    (hcont : ∀ y ∈ K, Continuous fun x : ι → ℝ => f (cplx x y))
    (hhol : ∀ (x y : ι → ℝ), y ∈ K → ∀ i, DifferentiableAt ℂ
      (fun s : ℂ => f (Function.update (cplx x y) i s)) ((x i : ℂ) + (y i : ℂ) * Complex.I))
    (n : ι → ℤ) {y₀ : ι → ℝ} {ε : ℝ} (hball : Metric.ball y₀ ε ⊆ K)
    {y : ι → ℝ} (hy : y ∈ Metric.ball y₀ ε) :
    coeffY f n y = coeffY f n y₀ := by
  have hε : 0 < ε := Metric.pos_of_mem_ball hy
  have hmem : ∀ z : ι → ℝ, z ∈ Metric.ball y₀ ε ↔ ∀ j, |z j - y₀ j| < ε := by
    intro z
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    simp [Real.dist_eq]
  let ys : Finset ι → ι → ℝ := fun S j => if j ∈ S then y₀ j else y j
  have hclose : ∀ (z : ι → ℝ), z ∈ Metric.ball y₀ ε → ∀ i, ∀ u ∈ uIcc (z i) (y₀ i),
      Function.update z i u ∈ Metric.ball y₀ ε := by
    intro z hz i u hu
    rw [hmem] at hz ⊢
    intro j
    by_cases h : j = i
    · subst h
      have h1 := hz j
      rw [abs_lt] at h1 ⊢
      rw [Set.mem_uIcc] at hu
      simp only [Function.update_self]
      rcases hu with hu | hu <;> constructor <;> linarith [hu.1, hu.2]
    · rw [Function.update_of_ne h]; exact hz j
  have hys : ∀ S : Finset ι, ys S ∈ Metric.ball y₀ ε ∧ coeffY f n (ys S) = coeffY f n y := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have : ys ∅ = y := by funext j; simp [ys]
      rw [this]; exact ⟨hy, rfl⟩
    | insert i S hi ih =>
      have hup : ys (insert i S) = Function.update (ys S) i (y₀ i) := by
        funext j
        by_cases h : j = i
        · subst h; simp [ys]
        · simp [ys, h]
      have hseg : ∀ u ∈ uIcc (ys S i) (y₀ i), Function.update (ys S) i u ∈ K :=
        fun u hu => hball (hclose _ ih.1 i u hu)
      rw [hup]
      refine ⟨hclose _ ih.1 i _ right_mem_uIcc, ?_⟩
      rw [coeffY_update_eq hper hcont hhol n (hball ih.1) i _ hseg]
      exact ih.2
  have hfin : ys Finset.univ = y₀ := by funext j; simp [ys]
  have := (hys Finset.univ).2
  rw [hfin] at this
  exact this.symm

/-- **The Fourier coefficients do not depend on the height:** for $K$ open and convex, $c_n(y) = c_n(y')$
for all $y, y' \in K$ (a locally constant function on the preconnected set $K$ is constant). -/
lemma coeffY_const (hK : IsOpen K) (hKc : Convex ℝ K)
    (hper : ∀ (t : ι → ℂ) (n : ι → ℤ), f (t + fun i => (n i : ℂ)) = f t)
    (hcont : ∀ y ∈ K, Continuous fun x : ι → ℝ => f (cplx x y))
    (hhol : ∀ (x y : ι → ℝ), y ∈ K → ∀ i, DifferentiableAt ℂ
      (fun s : ℂ => f (Function.update (cplx x y) i s)) ((x i : ℂ) + (y i : ℂ) * Complex.I))
    (n : ι → ℤ) {y y' : ι → ℝ} (hy : y ∈ K) (hy' : y' ∈ K) :
    coeffY f n y = coeffY f n y' := by
  have : PreconnectedSpace K := Subtype.preconnectedSpace hKc.isPreconnected
  let g : K → ℂ := fun z => coeffY f n z
  have hg : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro z
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hK z z.2
    have hnhds : ∀ᶠ w : K in nhds z, (w : ι → ℝ) ∈ Metric.ball (z : ι → ℝ) ε :=
      continuous_subtype_val.continuousAt.eventually_mem (Metric.ball_mem_nhds _ hε)
    filter_upwards [hnhds] with w hw
    exact coeffY_eq_of_mem_ball hper hcont hhol n hball hw
  exact hg.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ ⟨y, hy⟩)
    (Set.mem_univ ⟨y', hy'⟩)

end Main

/-- The Mathlib monomial $e^{2\pi i\,n\cdot x}$ on the torus, evaluated at a lift. -/
lemma mFourier_toTorus (n : ι → ℤ) (x : ι → ℝ) :
    UnitAddTorus.mFourier n (toTorus x)
      = Complex.exp (2 * π * Complex.I * ((∑ i, (n i : ℝ) * x i : ℝ) : ℂ)) := by
  simp only [UnitAddTorus.mFourier, toTorus, ContinuousMap.coe_mk, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- $e^{2\pi i\,n\cdot(x+iy)} = e^{2\pi i\,n\cdot x}\,e^{-2\pi\,n\cdot y}$. -/
lemma charZ_cplx (n : ι → ℤ) (x y : ι → ℝ) :
    charZ n (cplx x y) = Complex.exp (2 * π * Complex.I * ((∑ i, (n i : ℝ) * x i : ℝ) : ℂ))
      * Complex.exp (-(2 * π * (∑ i, (n i : ℝ) * y i : ℝ) : ℝ)) := by
  unfold charZ
  rw [← Complex.exp_add]
  congr 1
  simp only [dotZ, cplx]
  push_cast
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  linear_combination (2 * (π : ℂ) * (n i : ℂ) * (y i : ℂ)) * Complex.I_mul_I

/-- $e^{-2\pi i\,n\cdot(x+iy)} = e^{-2\pi i\,n\cdot x}\,e^{2\pi\,n\cdot y}$, with the first factor
the Mathlib monomial of $-n$. -/
lemma charZ_neg_cplx (n : ι → ℤ) (x y : ι → ℝ) :
    charZ (-n) (cplx x y) = UnitAddTorus.mFourier (-n) (toTorus x)
      * ((Real.exp (2 * π * ∑ i, (n i : ℝ) * y i) : ℝ) : ℂ) := by
  rw [charZ_cplx, mFourier_toTorus, Complex.ofReal_exp]
  congr 2
  simp [Finset.sum_neg_distrib]

/-- $|e^{2\pi i\,n\cdot(x+iy)}| = e^{-2\pi\,n\cdot y}$. -/
lemma norm_charZ_cplx (n : ι → ℤ) (x y : ι → ℝ) :
    ‖charZ n (cplx x y)‖ = Real.exp (-(2 * π * ∑ i, (n i : ℝ) * y i)) := by
  rw [charZ_cplx, norm_mul]
  have h1 : 2 * (π : ℂ) * Complex.I * ((∑ i, (n i : ℝ) * x i : ℝ) : ℂ)
      = ((2 * π * ∑ i, (n i : ℝ) * x i : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h1, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_exp]
  simp

/-- The torus Fourier coefficient of a lift of $x \mapsto f(x + iy)$, times $e^{2\pi\,n\cdot y}$,
is `coeffY`. -/
lemma mFourierCoeff_mul_exp {y : ι → ℝ} {g : UnitAddTorus ι → ℂ} (f : (ι → ℂ) → ℂ)
    (hg : ∀ x, g (toTorus x) = f (cplx x y)) (n : ι → ℤ) :
    UnitAddTorus.mFourierCoeff g n * ((Real.exp (2 * π * ∑ i, (n i : ℝ) * y i) : ℝ) : ℂ)
      = coeffY f n y := by
  have h := UnitAddTorus.mFourierCoeff_eq_integral g n (0 : ι → ℝ)
  rw [← unitBox_eq] at h
  rw [h, ← integral_mul_const]
  unfold coeffY
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show UnitAddTorus.mFourier (-n) (toTorus x) • g (toTorus x) * _ = _
  rw [hg, smul_eq_mul]
  show _ = f (cplx x y) * charZ (-n) (cplx x y)
  rw [charZ_neg_cplx]
  ring

/-- The torus Fourier coefficient is `coeffY` times $e^{-2\pi\,n\cdot y}$. -/
lemma mFourierCoeff_eq {y : ι → ℝ} {g : UnitAddTorus ι → ℂ} (f : (ι → ℂ) → ℂ)
    (hg : ∀ x, g (toTorus x) = f (cplx x y)) (n : ι → ℤ) :
    UnitAddTorus.mFourierCoeff g n
      = coeffY f n y * ((Real.exp (-(2 * π * ∑ i, (n i : ℝ) * y i)) : ℝ) : ℂ) := by
  have h := mFourierCoeff_mul_exp f hg n
  have hr : ((Real.exp (2 * π * ∑ i, (n i : ℝ) * y i) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  rw [← h, Real.exp_neg]
  push_cast
  field_simp

/-- The expansion at $t = x_0 + iy$, stated in terms of real and imaginary parts. -/
lemma hasSum_expansion_cplx (f : (ι → ℂ) → ℂ)
    (hper : ∀ (t : ι → ℂ) (n : ι → ℤ), f (t + fun i => (n i : ℂ)) = f t)
    (x₀ y : ι → ℝ) (hcy : Continuous fun x : ι → ℝ => f (cplx x y))
    (hsum : Summable fun n : ι → ℤ => ‖coeffY f n y * charZ n (cplx x₀ y)‖) :
    HasSum (fun n : ι → ℤ => coeffY f n y * charZ n (cplx x₀ y)) (f (cplx x₀ y)) := by
  have hpH : IsIntPeriodic fun x : ι → ℝ => f (cplx x y) := by
    intro x m
    simp only
    rw [cplx_add_int, hper]
  obtain ⟨g, hg'⟩ := exists_lift hpH
  let ĝ : C(UnitAddTorus ι, ℂ) := ⟨g, continuous_of_lift hg' hcy⟩
  have hg : ∀ x, (ĝ : UnitAddTorus ι → ℂ) (toTorus x) = f (cplx x y) := hg'
  have hcoef := mFourierCoeff_eq f hg
  have hterm : ∀ n : ι → ℤ, UnitAddTorus.mFourierCoeff (ĝ : UnitAddTorus ι → ℂ) n
      • UnitAddTorus.mFourier n (toTorus x₀) = coeffY f n y * charZ n (cplx x₀ y) := by
    intro n
    rw [hcoef, smul_eq_mul, mFourier_toTorus, charZ_cplx, Complex.ofReal_exp]
    push_cast
    ring
  have hnorm : ∀ n : ι → ℤ, ‖UnitAddTorus.mFourierCoeff (ĝ : UnitAddTorus ι → ℂ) n‖
      = ‖coeffY f n y * charZ n (cplx x₀ y)‖ := by
    intro n
    rw [hcoef, norm_mul, norm_mul, norm_charZ_cplx, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hsumC : Summable (UnitAddTorus.mFourierCoeff (ĝ : UnitAddTorus ι → ℂ)) :=
    Summable.of_norm (by simpa only [hnorm] using hsum)
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsumC (toTorus x₀)
  have h2 : (fun n : ι → ℤ => coeffY f n y * charZ n (cplx x₀ y))
      = fun n => UnitAddTorus.mFourierCoeff (ĝ : UnitAddTorus ι → ℂ) n
        • UnitAddTorus.mFourier n (toTorus x₀) := funext fun n => (hterm n).symm
  rw [h2, ← hg x₀]
  exact h

/-- **Fourier expansion of a periodic function.** If $y = \operatorname{Im}t \in K$ and the series
$\sum_n c_n(y)\,e^{2\pi i\,n\cdot t}$ converges absolutely, then it sums to $f(t)$. (Only periodicity and
continuity in the real part at the height $y$ are used; with `coeffY_const` the coefficients are
independent of $y$.) -/
theorem hasSum_expansion {K : Set (ι → ℝ)} {f : (ι → ℂ) → ℂ}
    (hper : ∀ (t : ι → ℂ) (n : ι → ℤ), f (t + fun i => (n i : ℂ)) = f t)
    (hcont : ∀ y ∈ K, Continuous fun x : ι → ℝ => f (cplx x y))
    (t : ι → ℂ) (ht : (fun i => (t i).im) ∈ K)
    (hsum : Summable fun n : ι → ℤ => ‖coeffY f n (fun i => (t i).im) * charZ n t‖) :
    HasSum (fun n : ι → ℤ => coeffY f n (fun i => (t i).im) * charZ n t) (f t) := by
  have htc : cplx (fun i => (t i).re) (fun i => (t i).im) = t := by
    funext i; simp [cplx]
  have := hasSum_expansion_cplx f hper (fun i => (t i).re) (fun i => (t i).im) (hcont _ ht)
    (by rwa [htc])
  rwa [htc] at this

/-- The half-open unit box has volume at most one. -/
lemma volume_real_unitBox_le : volume.real (unitBox ι) ≤ 1 := by
  have h1 : volume.real (unitBox ι) ≤ volume.real (Icc (0 : ι → ℝ) 1) :=
    measureReal_mono unitBox_subset_Icc isCompact_Icc.measure_lt_top.ne
  have h2 : volume.real (Icc (0 : ι → ℝ) 1) = 1 := by
    simp [Measure.real, Real.volume_Icc_pi]
  linarith

/-- If $|f| \le M$ on the height $y$ then $|c_n(y)| \le Me^{2\pi\,n\cdot y}$. -/
lemma norm_coeffY_le {f : (ι → ℂ) → ℂ} {y : ι → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x : ι → ℝ, ‖f (cplx x y)‖ ≤ M) (n : ι → ℤ) :
    ‖coeffY f n y‖ ≤ M * Real.exp (2 * π * ∑ i, (n i : ℝ) * y i) := by
  have hb : ∀ x ∈ unitBox ι, ‖f (cplx x y) * charZ (-n) (cplx x y)‖
      ≤ M * Real.exp (2 * π * ∑ i, (n i : ℝ) * y i) := by
    intro x _
    rw [norm_mul, norm_charZ_cplx]
    have : -(2 * π * ∑ i, (((-n) i : ℤ) : ℝ) * y i) = 2 * π * ∑ i, (n i : ℝ) * y i := by
      simp [Finset.sum_neg_distrib]
    rw [this]
    exact mul_le_mul_of_nonneg_right (hM x) (Real.exp_pos _).le
  have hfin : volume (unitBox ι) < ⊤ :=
    (measure_mono unitBox_subset_Icc).trans_lt isCompact_Icc.measure_lt_top
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) hfin hb
  unfold coeffY
  refine h.trans ?_
  exact mul_le_of_le_one_right (mul_nonneg hM0 (Real.exp_pos _).le) volume_real_unitBox_le

/-- **Koecher's principle.** Let $K$ be an open convex cone and $f$ as above, bounded by $M$ on
$\{t : \operatorname{Im}t - y_0 \in K\}$ for some $y_0 \in K$. If $n\cdot y < 0$ for some $y \in K$
then the coefficient $c_n(y_0)$ (hence every $c_n(y)$, $y \in K$) vanishes. -/
theorem coeffY_eq_zero_of_bounded {K : Set (ι → ℝ)} {f : (ι → ℂ) → ℂ}
    (hK : IsOpen K) (hKc : Convex ℝ K) (hcone : ∀ y ∈ K, ∀ c : ℝ, 0 < c → c • y ∈ K)
    (hper : ∀ (t : ι → ℂ) (n : ι → ℤ), f (t + fun i => (n i : ℂ)) = f t)
    (hcont : ∀ y ∈ K, Continuous fun x : ι → ℝ => f (cplx x y))
    (hhol : ∀ (x y : ι → ℝ), y ∈ K → ∀ i, DifferentiableAt ℂ
      (fun s : ℂ => f (Function.update (cplx x y) i s)) ((x i : ℂ) + (y i : ℂ) * Complex.I))
    {y₀ : ι → ℝ} (hy₀ : y₀ ∈ K) {M : ℝ}
    (hM : ∀ t : ι → ℂ, ((fun i => (t i).im) - y₀) ∈ K → ‖f t‖ ≤ M)
    (n : ι → ℤ) (hn : ¬ ∀ y ∈ K, 0 ≤ ∑ i, (n i : ℝ) * y i) :
    coeffY f n y₀ = 0 := by
  push Not at hn
  obtain ⟨y₁, hy₁, hS₁⟩ := hn
  set S₀ : ℝ := ∑ i, (n i : ℝ) * y₀ i with hS₀
  set S₁ : ℝ := ∑ i, (n i : ℝ) * y₁ i with hS₁def
  have hyc : ∀ c : ℝ, 0 < c → y₀ + c • y₁ ∈ K := by
    intro c hc
    have h1 := hKc (hcone y₀ hy₀ 2 two_pos) (hcone y₁ hy₁ (2 * c) (by positivity))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have : (1 / 2 : ℝ) • ((2 : ℝ) • y₀) + (1 / 2 : ℝ) • ((2 * c) • y₁) = y₀ + c • y₁ := by
      module
    rwa [this] at h1
  have hbound : ∀ c : ℝ, 0 < c →
      ‖coeffY f n y₀‖ ≤ M * Real.exp (2 * π * (S₀ + c * S₁)) := by
    intro c hc
    have hmem := hyc c hc
    have hMc : ∀ x : ι → ℝ, ‖f (cplx x (y₀ + c • y₁))‖ ≤ M := by
      intro x
      apply hM
      have : ((fun i => (cplx x (y₀ + c • y₁) i).im) - y₀) = c • y₁ := by
        funext i; simp [cplx]
      rw [this]; exact hcone y₁ hy₁ c hc
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hMc 0)
    have h := norm_coeffY_le hM0 hMc n
    rw [← coeffY_const hK hKc hper hcont hhol n hy₀ hmem] at h
    have hsum : ∑ i, (n i : ℝ) * (y₀ + c • y₁) i = S₀ + c * S₁ := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
        hS₀, hS₁def, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rwa [hsum] at h
  have hlim : Filter.Tendsto (fun c : ℝ => M * Real.exp (2 * π * (S₀ + c * S₁)))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun c : ℝ => c * S₁) Filter.atTop Filter.atBot :=
      Filter.tendsto_id.atTop_mul_const_of_neg hS₁
    have h2 : Filter.Tendsto (fun c : ℝ => S₀ + c * S₁) Filter.atTop Filter.atBot :=
      Filter.tendsto_atBot_add_const_left _ _ h1
    have h3 : Filter.Tendsto (fun c : ℝ => 2 * π * (S₀ + c * S₁)) Filter.atTop Filter.atBot :=
      h2.const_mul_atBot (by positivity)
    have h4 := Real.tendsto_exp_atBot.comp h3
    simpa using h4.const_mul M
  have hle : ‖coeffY f n y₀‖ ≤ 0 :=
    ge_of_tendsto hlim ((Filter.eventually_gt_atTop 0).mono fun c hc => hbound c hc)
  exact norm_le_zero_iff.mp hle

end QuadFormsKB.SiegelWeil.Forms.HolExp
