import Mathlib

/-!
# The local fibration $\mathrm{GL}_2\to\mathbb G_m$, $X\mapsto\det X$, in the gauge chart

**Generic (Mathlib only).** $R$ a commutative ring with a measure $\mu$ (in the applications: a local field $F_v$ with its
self-dual measure, or $F_\infty = F\otimes\mathbb R$ with $\prod_w$ of the self-dual measures), invariant under
translations and scaled by units: $(u\cdot)_*\mu = |u|^{-1}\mu$ for a multiplicative "module" $|\cdot|$.

For $\mathrm{SL}_2$ Weil's gauge form is $\omega = da\wedge db\wedge dc/a$ in the chart
$(a, b, c)\mapsto\begin{pmatrix} a & b\\ c & (1 + bc)/a\end{pmatrix}$; for $\mathrm{GL}_2$ it is
$|\det X|^{-2}dX$. With the section $\sigma(t) = \operatorname{diag}(1, t)$ of $\det$,
$$\sigma(t)\begin{pmatrix} a & b\\ c & (1 + bc)/a\end{pmatrix} = \begin{pmatrix} a & b\\ tc & t(1 + bc)/a\end{pmatrix},$$
and **`lintegral_gl2_fibration`** says
$$\int |a|^{-1}|t|^{-1} f\Big(a, b, tc, \frac{t(1+bc)}{a}\Big)\,da\,db\,dc\,dt =
  \int f(a, b, z, s)\,|as - bz|^{-2}\,da\,db\,dz\,ds$$
(over $a$, $t$ units resp. $a$, $as - bz$ units), i.e. $|\det X|^{-2}dX = \omega_{\mathrm{SL}_2}\otimes d^\times t$ under
$(h, t)\mapsto\sigma(t)h$: Weil 1982, §2.4, Thm 2.4.4 for $1\to\mathrm{SL}_2\to\mathrm{GL}_2\to\mathbb G_m\to 1$.
*Proof.* Two substitutions, Fubini in between: $z = tc$ for fixed $t$ (factor $|t|^{-1}$), then
$s = (t + bz)/a$ for fixed $z$ (factor $|a|$).
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

namespace GL2Fib

set_option linter.unusedSectionVars false

variable {R : Type} [CommRing R] [Inv R] [MeasurableSpace R] [MeasurableAdd₂ R] [MeasurableMul₂ R]
  [MeasurableNeg R] (μ : Measure R) [SFinite μ] [μ.IsAddLeftInvariant]
  (md : R → ℝ≥0∞)

/-- The hypotheses on the ring $R$, its measure and its module. -/
structure Hyp : Prop where
  /-- Inversion is measurable. -/
  measurable_inv : Measurable (Inv.inv : R → R)
  /-- $a a^{-1} = 1$ for units. -/
  mul_inv_cancel : ∀ a : R, IsUnit a → a * a⁻¹ = 1
  /-- The units form a measurable set. -/
  measurableSet_units : MeasurableSet {x : R | IsUnit x}
  /-- The module is measurable. -/
  measurable_md : Measurable md
  /-- The module is multiplicative on units. -/
  md_mul : ∀ u v : R, IsUnit u → IsUnit v → md (u * v) = md u * md v
  /-- $|1| = 1$. -/
  md_one : md 1 = 1
  /-- The module of a unit is neither $0$ nor $\infty$. -/
  md_ne_zero : ∀ u : R, IsUnit u → md u ≠ 0
  /-- The module of a unit is finite. -/
  md_ne_top : ∀ u : R, IsUnit u → md u ≠ ∞
  /-- $(u\cdot)_*\mu = |u|^{-1}\mu$ for units $u$. -/
  map_mul : ∀ u : R, IsUnit u → μ.map (fun x => u * x) = (md u)⁻¹ • μ

variable {μ md}

/-- The set of units. -/
abbrev U : Set R := {x : R | IsUnit x}

theorem lintegral_mul_left (h : Hyp μ md) {u : R} (hu : IsUnit u) {g : R → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g (u * x) ∂μ = (md u)⁻¹ * ∫⁻ x, g x ∂μ := by
  rw [← lintegral_map hg (measurable_const_mul u), h.map_mul u hu, lintegral_smul_measure, smul_eq_mul]

theorem isUnit_inv (h : Hyp μ md) {a : R} (ha : IsUnit a) : IsUnit a⁻¹ :=
  ⟨⟨a⁻¹, a, by rw [mul_comm]; exact h.mul_inv_cancel a ha, h.mul_inv_cancel a ha⟩, rfl⟩

theorem md_inv (h : Hyp μ md) {a : R} (ha : IsUnit a) : (md a⁻¹)⁻¹ = md a := by
  have h1 : md a * md a⁻¹ = 1 := by
    rw [← h.md_mul a a⁻¹ ha (isUnit_inv h ha), h.mul_inv_cancel a ha, h.md_one]
  exact (ENNReal.eq_inv_of_mul_eq_one_left h1).symm

/-- **The second substitution** $s = (t + w)/a$: $\int g((t + w)a^{-1})\,dt = |a|\int g(s)\,ds$. -/
theorem lintegral_affine (h : Hyp μ md) {a : R} (ha : IsUnit a) (w : R) {g : R → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ t, g ((t + w) * a⁻¹) ∂μ = md a * ∫⁻ s, g s ∂μ := by
  have e : (fun t => g ((t + w) * a⁻¹)) = fun t => (fun x => g (a⁻¹ * x)) (w + t) := by
    funext t; rw [mul_comm, add_comm]
  rw [e, lintegral_add_left_eq_self (fun x => g (a⁻¹ * x)), lintegral_mul_left h (isUnit_inv h ha) hg,
    md_inv h ha]

variable (F : R → R → R → R → ℝ≥0∞)

/-- **The local fibration $\mathrm{GL}_2\to\mathbb G_m$ in the gauge chart.** -/
theorem lintegral_gl2_fibration (h : Hyp μ md)
    (hF : Measurable fun p : R × R × R × R => F p.1 p.2.1 p.2.2.1 p.2.2.2) :
    ∫⁻ a, U.indicator (fun a => (md a)⁻¹ * ∫⁻ b, ∫⁻ c, ∫⁻ t,
      U.indicator (fun t => (md t)⁻¹ * F a b (t * c) (t * (1 + c * b) * a⁻¹)) t ∂μ ∂μ ∂μ) a ∂μ =
    ∫⁻ a, U.indicator (fun a => ∫⁻ b, ∫⁻ z, ∫⁻ s,
      U.indicator (fun d => (md d)⁻¹ ^ 2) (a * s - b * z) * F a b z s ∂μ ∂μ ∂μ) a ∂μ := by
  have hU : MeasurableSet (U : Set R) := h.measurableSet_units
  have hmd := h.measurable_md
  refine lintegral_congr fun a => ?_
  by_cases ha : IsUnit a
  swap
  · simp [Set.indicator_of_notMem (show a ∉ (U : Set R) from ha)]
  rw [Set.indicator_of_mem (show a ∈ (U : Set R) from ha), Set.indicator_of_mem (show a ∈ (U : Set R) from ha)]
  have hma0 := h.md_ne_zero a ha
  have hmat := h.md_ne_top a ha
  rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hma0)]
  refine lintegral_congr fun b => ?_
  -- measurability of the integrands
  have hFm : ∀ {X : Type} [MeasurableSpace X] {f₁ f₂ f₃ f₄ : X → R}, Measurable f₁ → Measurable f₂ →
      Measurable f₃ → Measurable f₄ → Measurable fun x => F (f₁ x) (f₂ x) (f₃ x) (f₄ x) :=
    fun h1 h2 h3 h4 => hF.comp (h1.prodMk (h2.prodMk (h3.prodMk h4)))
  set ι : R → ℝ≥0∞ := U.indicator fun t => (md t)⁻¹ with hι_def
  set κ : R → ℝ≥0∞ := U.indicator fun d => (md d)⁻¹ ^ 2 with hκ_def
  have hι : Measurable ι := hmd.inv.indicator hU
  have hκ : Measurable κ := (hmd.inv.pow_const 2).indicator hU
  have hιt : ∀ t, ι t ≠ ∞ := fun t => by
    by_cases ht : IsUnit t
    · rw [hι_def, Set.indicator_of_mem (show t ∈ (U : Set R) from ht)]
      exact ENNReal.inv_ne_top.2 (h.md_ne_zero t ht)
    · rw [hι_def, Set.indicator_of_notMem (show t ∉ (U : Set R) from ht)]; exact ENNReal.zero_ne_top
  have hind : ∀ c t, U.indicator (fun t => (md t)⁻¹ * F a b (t * c) (t * (1 + c * b) * a⁻¹)) t =
      ι t * F a b (t * c) (t * (1 + c * b) * a⁻¹) := fun c t =>
    Set.indicator_mul_left _ _ _
  simp_rw [hind]
  -- swap `c` and `t`
  rw [lintegral_lintegral_swap (by
    refine (Measurable.mul (hι.comp measurable_snd) (hFm measurable_const measurable_const
      (measurable_snd.mul measurable_fst) ?_)).aemeasurable
    exact (measurable_snd.mul (measurable_const.add (measurable_fst.mul measurable_const))).mul measurable_const)]
  -- the substitution `z = t c`
  have hS2 : ∀ t, ∫⁻ c, ι t * F a b (t * c) (t * (1 + c * b) * a⁻¹) ∂μ =
      κ t * ∫⁻ z, F a b z ((t + z * b) * a⁻¹) ∂μ := by
    intro t
    by_cases ht : IsUnit t
    · set G : R → ℝ≥0∞ := fun z => F a b z ((t + z * b) * a⁻¹) with hG
      have e : (fun c => ι t * F a b (t * c) (t * (1 + c * b) * a⁻¹)) = fun c => ι t * G (t * c) := by
        funext c; simp only [hG]; congr 2; ring
      rw [e, lintegral_const_mul' _ _ (hιt t), lintegral_mul_left h ht (g := G) (hFm measurable_const measurable_const
        measurable_id ((measurable_const.add (measurable_id.mul measurable_const)).mul measurable_const)),
        ← mul_assoc, hι_def, hκ_def, Set.indicator_of_mem (show t ∈ (U : Set R) from ht),
        Set.indicator_of_mem (show t ∈ (U : Set R) from ht), sq]
    · simp [hι_def, hκ_def, Set.indicator_of_notMem (show t ∉ (U : Set R) from ht)]
  simp_rw [hS2]
  have hS3 : ∀ t, κ t * ∫⁻ z, F a b z ((t + z * b) * a⁻¹) ∂μ =
      ∫⁻ z, κ t * F a b z ((t + z * b) * a⁻¹) ∂μ := fun t =>
    (lintegral_const_mul _ (hFm measurable_const measurable_const measurable_id
      ((measurable_const.add (measurable_id.mul measurable_const)).mul measurable_const))).symm
  simp_rw [hS3]
  rw [lintegral_lintegral_swap (by
    refine (Measurable.mul (hκ.comp measurable_fst) (hFm measurable_const measurable_const measurable_snd
      ?_)).aemeasurable
    exact (measurable_fst.add (measurable_snd.mul measurable_const)).mul measurable_const)]
  -- the substitution `s = (t + z b)/a`
  have hS4 : ∀ z, ∫⁻ t, κ t * F a b z ((t + z * b) * a⁻¹) ∂μ =
      md a * ∫⁻ s, κ (a * s - b * z) * F a b z s ∂μ := by
    intro z
    set G : R → ℝ≥0∞ := fun s => κ (a * s - b * z) * F a b z s with hG
    have e : (fun t => κ t * F a b z ((t + z * b) * a⁻¹)) = fun t => G ((t + z * b) * a⁻¹) := by
      funext t
      have : a * ((t + z * b) * a⁻¹) - b * z = t := by
        calc a * ((t + z * b) * a⁻¹) - b * z = (t + z * b) * (a * a⁻¹) - b * z := by ring
          _ = t := by rw [h.mul_inv_cancel a ha]; ring
      simp only [hG, this]
    rw [e]
    exact lintegral_affine h ha (g := G) _ ((hκ.comp ((measurable_const.mul measurable_id).sub measurable_const)).mul
      (hFm measurable_const measurable_const measurable_const measurable_id))
  simp_rw [hS4]
  rw [lintegral_const_mul' _ _ hmat, ← mul_assoc, ENNReal.inv_mul_cancel hma0 hmat, one_mul]

/-! ### Four coordinates as a product measure -/

section Pi4

variable {S : Type} [MeasurableSpace S] (ν : Measure S) [SigmaFinite ν]

/-- $(a, b, z, s)\mapsto(a, b, z, s)$ as a vector. -/
def v4 (p : S × S × S × S) : Fin 4 → S := ![p.1, p.2.1, p.2.2.1, p.2.2.2]

theorem measurable_v4 : Measurable (v4 (S := S)) := by
  refine measurable_pi_iff.2 fun i => ?_
  fin_cases i
  · exact measurable_fst
  · exact measurable_fst.comp measurable_snd
  · exact measurable_fst.comp (measurable_snd.comp measurable_snd)
  · exact measurable_snd.comp (measurable_snd.comp measurable_snd)

theorem pi_four_eq : Measure.pi (fun _ : Fin 4 => ν) = (ν.prod (ν.prod (ν.prod ν))).map v4 := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply measurable_v4 (MeasurableSet.univ_pi hs)]
  have : v4 ⁻¹' Set.univ.pi s = s 0 ×ˢ (s 1 ×ˢ (s 2 ×ˢ s 3)) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod, Fin.forall_fin_succ, v4]
    simp [IsEmpty.forall_iff]
  rw [this, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, Fin.prod_univ_four]
  ring

/-- $\int f\,d\nu^{\otimes4} = \int\!\!\int\!\!\int\!\!\int f(a, b, z, s)\,da\,db\,dz\,ds$. -/
theorem lintegral_pi_four {f : (Fin 4 → S) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ v, f v ∂Measure.pi (fun _ : Fin 4 => ν) = ∫⁻ a, ∫⁻ b, ∫⁻ z, ∫⁻ s, f ![a, b, z, s] ∂ν ∂ν ∂ν ∂ν := by
  rw [pi_four_eq, lintegral_map hf measurable_v4]
  rw [lintegral_prod (fun p => f (v4 p)) (hf.comp measurable_v4).aemeasurable]
  refine lintegral_congr fun a => ?_
  rw [lintegral_prod (fun p => f (v4 (a, p))) ((hf.comp measurable_v4).comp measurable_prodMk_left).aemeasurable]
  refine lintegral_congr fun b => ?_
  rw [lintegral_prod (fun p => f (v4 (a, b, p))) (((hf.comp measurable_v4).comp measurable_prodMk_left).comp
    measurable_prodMk_left).aemeasurable]
  rfl

/-- Permuting the coordinates preserves $\nu^{\otimes4}$. -/
theorem lintegral_pi_four_perm (σ : Equiv.Perm (Fin 4)) {f : (Fin 4 → S) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ v, f (v ∘ σ) ∂Measure.pi (fun _ : Fin 4 => ν) = ∫⁻ v, f v ∂Measure.pi (fun _ : Fin 4 => ν) := by
  have hm : Measurable fun v : Fin 4 → S => v ∘ σ := measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hmap : (Measure.pi fun _ : Fin 4 => ν).map (fun v => v ∘ σ) = Measure.pi fun _ : Fin 4 => ν := by
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
    have : (fun v : Fin 4 → S => v ∘ σ) ⁻¹' Set.univ.pi s = Set.univ.pi fun i => s (σ.symm i) := by
      ext v
      simp only [Set.mem_preimage, Set.mem_univ_pi, Function.comp_apply]
      exact ⟨fun h i => by simpa using h (σ.symm i), fun h i => by simpa using h (σ i)⟩
    rw [this, Measure.pi_pi]
    exact Equiv.prod_comp σ.symm fun i => ν (s i)
  rw [← lintegral_map hf hm, hmap]

end Pi4

/-- **The local fibration, in the order $(t, a, c, b)$ and with the right side over $\nu^{\otimes4}$.** -/
theorem lintegral_gl2_fibration' [SigmaFinite μ] (h : Hyp μ md) {F : (Fin 4 → R) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ t, U.indicator (fun t => (md t)⁻¹ * ∫⁻ a, U.indicator (fun a => (md a)⁻¹ * ∫⁻ c, ∫⁻ b,
      F ![a, b, t * c, t * (1 + c * b) * a⁻¹] ∂μ ∂μ) a ∂μ) t ∂μ =
    ∫⁻ v, U.indicator (fun _ => 1) (v 0) * U.indicator (fun d => (md d)⁻¹ ^ 2) (v 0 * v 3 - v 1 * v 2) * F v
      ∂Measure.pi (fun _ : Fin 4 => μ) := by
  have hU : MeasurableSet (U : Set R) := h.measurableSet_units
  have hmd := h.measurable_md
  have hinv := h.measurable_inv
  set ι : R → ℝ≥0∞ := U.indicator fun t => (md t)⁻¹ with hι_def
  have hι : Measurable ι := hmd.inv.indicator hU
  have hιt : ∀ t, ι t ≠ ∞ := fun t => by
    by_cases ht : IsUnit t
    · rw [hι_def, Set.indicator_of_mem (show t ∈ (U : Set R) from ht)]
      exact ENNReal.inv_ne_top.2 (h.md_ne_zero t ht)
    · rw [hι_def, Set.indicator_of_notMem (show t ∉ (U : Set R) from ht)]; exact ENNReal.zero_ne_top
  have hind : ∀ (g : R → ℝ≥0∞) x, U.indicator (fun t => (md t)⁻¹ * g t) x = ι x * g x := fun g x =>
    Set.indicator_mul_left _ _ _
  -- the common integrand, in the variables `(a, b, c, t)`
  set Ψ : (Fin 4 → R) → ℝ≥0∞ := fun v => ι (v 0) * ι (v 3) * F ![v 0, v 1, v 3 * v 2, v 3 * (1 + v 2 * v 1) * (v 0)⁻¹]
    with hΨ
  have hm4 : ∀ {f₀ f₁ f₂ f₃ : (Fin 4 → R) → R}, Measurable f₀ → Measurable f₁ → Measurable f₂ → Measurable f₃ →
      Measurable fun v => F ![f₀ v, f₁ v, f₂ v, f₃ v] := by
    intro f₀ f₁ f₂ f₃ h0 h1 h2 h3
    refine hF.comp (measurable_pi_iff.2 fun i => ?_)
    fin_cases i
    exacts [h0, h1, h2, h3]
  have hp : ∀ i : Fin 4, Measurable fun v : Fin 4 → R => v i := fun i => measurable_pi_apply i
  have hΨm : Measurable Ψ :=
    ((hι.comp (hp 0)).mul (hι.comp (hp 3))).mul (hm4 (hp 0) (hp 1) ((hp 3).mul (hp 2))
      (((hp 3).mul (measurable_const.add ((hp 2).mul (hp 1)))).mul (hinv.comp (hp 0))))
  -- the permutation `(t, a, c, b) ↦ (a, b, c, t)`
  let σ : Equiv.Perm (Fin 4) := ⟨![1, 3, 2, 0], ![3, 0, 2, 1], by decide, by decide⟩
  have hL : ∫⁻ t, U.indicator (fun t => (md t)⁻¹ * ∫⁻ a, U.indicator (fun a => (md a)⁻¹ * ∫⁻ c, ∫⁻ b,
      F ![a, b, t * c, t * (1 + c * b) * a⁻¹] ∂μ ∂μ) a ∂μ) t ∂μ = ∫⁻ v, Ψ v ∂Measure.pi (fun _ : Fin 4 => μ) := by
    rw [← lintegral_pi_four_perm μ σ hΨm, lintegral_pi_four μ (f := fun v => Ψ (v ∘ σ)) (hΨm.comp
      (measurable_pi_iff.2 fun i => measurable_pi_apply _))]
    refine lintegral_congr fun t => ?_
    rw [hind, ← lintegral_const_mul' _ _ (hιt t)]
    refine lintegral_congr fun a => ?_
    rw [hind, ← mul_assoc, ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top (hιt t) (hιt a))]
    refine lintegral_congr fun c => ?_
    rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top (hιt t) (hιt a))]
    refine lintegral_congr fun b => ?_
    simp only [hΨ, Function.comp_apply, σ, Equiv.coe_fn_mk, Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Fin.isValue]
    ring_nf
  have hR := lintegral_gl2_fibration (fun a b z s => F ![a, b, z, s]) h (hF.comp measurable_v4)
  rw [hL]
  -- the left side of `hR` is `∫ Ψ`
  have hL' : ∫⁻ a, U.indicator (fun a => (md a)⁻¹ * ∫⁻ b, ∫⁻ c, ∫⁻ t,
      U.indicator (fun t => (md t)⁻¹ * F ![a, b, t * c, t * (1 + c * b) * a⁻¹]) t ∂μ ∂μ ∂μ) a ∂μ =
      ∫⁻ v, Ψ v ∂Measure.pi (fun _ : Fin 4 => μ) := by
    rw [lintegral_pi_four μ hΨm]
    refine lintegral_congr fun a => ?_
    rw [hind, ← lintegral_const_mul' _ _ (hιt a)]
    refine lintegral_congr fun b => ?_
    rw [← lintegral_const_mul' _ _ (hιt a)]
    refine lintegral_congr fun c => ?_
    rw [← lintegral_const_mul' _ _ (hιt a)]
    refine lintegral_congr fun t => ?_
    rw [hind]
    simp only [hΨ, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue]
    ring
  rw [← hL', hR, lintegral_pi_four μ ?_]
  · refine lintegral_congr fun a => ?_
    by_cases ha : IsUnit a
    · rw [Set.indicator_of_mem (show a ∈ (U : Set R) from ha)]
      refine lintegral_congr fun b => lintegral_congr fun z => lintegral_congr fun s => ?_
      simp only [Set.indicator_of_mem (show a ∈ (U : Set R) from ha), one_mul, Matrix.cons_val,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue]
    · rw [Set.indicator_of_notMem (show a ∉ (U : Set R) from ha)]
      simp [Set.indicator_of_notMem (show a ∉ (U : Set R) from ha)]
  · exact ((measurable_const.indicator hU).comp (hp 0)).mul (((hmd.inv.pow_const 2).indicator hU).comp
      (((hp 0).mul (hp 3)).sub ((hp 1).mul (hp 2))))|>.mul hF

end GL2Fib

end QuadFormsKB.Tamagawa.Measure.Weil
