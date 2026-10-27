import QuadFormsKB.Tamagawa.Measure.Weil.SphereEulerLocalReal
import QuadFormsKB.Tamagawa.Measure.SphereLerayC
import QuadFormsKB.Tamagawa.SphericalResidueNF

/-!
# The local spherical identity at a complex place

$Q$ a complex quadratic form in $N\ge1$ variables, $c\in\mathbb C^\times$, $\sigma_c$ = the Leray measure on the
sphere $S_c = \{Q = c\}$ (`SphereLerayC.sigC`, built from Lebesgue measure $dx\,dy$), $G_{\mathbb C}(x) =
e^{-2\pi\sum_i|x_i|^2}$ (`gaussFnC`, the self-dual Gaussian of $\mathbb C^N$ for the trace pairing), $a = N + 2s$,
$|z|_{\mathbb C} = |z|^2$. The archimedean factor of the adelic spherical integral at a complex place is
$$\int_{S_c}\int_{\mathbb C}|t|_{\mathbb C}^{a-1}G_{\mathbb C}(ty)\,dt\,d\sigma_c(y) =
  \frac{2}{|2c|_{\mathbb C}\,|c|_{\mathbb C}^{s}}\int_{\mathbb C^N}|Q(x)|_{\mathbb C}^sG_{\mathbb C}(x)\,dx$$
(**`lintegral_archMellinC_sigC`**; polar coordinates `fibreCount_polC`, the polar map being two-to-one onto
$\{Q\ne0\}$, $\sigma_c = \nu_c/|2c|_{\mathbb C}$), hence (**`lintegral_archMellinC_sigCx`**) it equals
$2Z_w(s)/(2^N|2\rho|_w|\rho|_w^s)$ with $Z_w$ = `cplxZetaAt` for $\Psi_w = G_{\mathbb C}$; here $2Z_w(s)$ is the complex
factor of `sphericalZetaAtNF` and $2^N$ is absorbed by Weil's normalization (`cxWeil`) in the box formula.
Also: $G_{\mathbb C}$ is an admissible test function (**`isArchTestFnC_gaussFnC`**) with $2^N\int G_{\mathbb C} = 1$
(**`integral_gaussFnC`**).
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace QuadFormsKB.Tamagawa.Measure.SphereLerayC

/-- **The complex Gaussian** $G_{\mathbb C}(x) = e^{-2\pi\sum_i|x_i|^2}$ on $\mathbb C^n$ (the self-dual Gaussian of
$\mathbb C^n$ for $(z, z')\mapsto 2\operatorname{Re}(zz')$, the complex component of `gV`). -/
def gaussFnC {n : ℕ} (x : Fin n → ℂ) : ℝ := Real.exp (-(2 * Real.pi) * ∑ i, ‖x i‖ ^ 2)

/-- **The complex Mellin transform of the Gaussian**
$M^{\mathbb C}_a(y) = \int_{\mathbb C}|t|_{\mathbb C}^{a}|t|_{\mathbb C}^{-1}G_{\mathbb C}(ty)\,dt$ ($dt$ Lebesgue measure on
$\mathbb C$, $|t|_{\mathbb C} = |t|^2$). -/
def archMellinC {n : ℕ} (a : ℝ) (y : Fin n → ℂ) : ℝ≥0∞ :=
  ∫⁻ t : ℂ, ENNReal.ofReal ((‖t‖ ^ 2) ^ a * (‖t‖ ^ 2)⁻¹) * ENNReal.ofReal (gaussFnC (t • y))

theorem measurable_gaussFnC {n : ℕ} : Measurable (gaussFnC (n := n)) := by
  unfold gaussFnC
  fun_prop

theorem measurable_archMellinC {n : ℕ} (a : ℝ) : Measurable (archMellinC (n := n) a) := by
  unfold archMellinC
  refine Measurable.lintegral_prod_left' (μ := (volume : Measure ℂ)) (f := fun p : ℂ × (Fin n → ℂ) =>
    ENNReal.ofReal ((‖p.1‖ ^ 2) ^ a * (‖p.1‖ ^ 2)⁻¹) * ENNReal.ofReal (gaussFnC (p.1 • p.2))) ?_
  refine Measurable.mul ?_ (ENNReal.measurable_ofReal.comp
    (measurable_gaussFnC.comp (measurable_fst.smul measurable_snd)))
  exact ENNReal.measurable_ofReal.comp ((((measurable_fst.norm).pow_const 2).pow_const a).mul
    ((measurable_fst.norm).pow_const 2).inv)

/-- $G_{\mathbb C}$ is a product of one-dimensional Gaussians. -/
theorem gaussFnC_eq_prod {n : ℕ} (x : Fin n → ℂ) : gaussFnC x = ∏ i, Real.exp (-(2 * Real.pi) * ‖x i‖ ^ 2) := by
  rw [gaussFnC, ← Real.exp_sum, Finset.mul_sum]

/-- $z \mapsto e^{-b|z|^2}$ is integrable on $\mathbb C$ for $b > 0$. -/
theorem integrable_exp_neg_mul_sq_norm_complex {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : ℂ => Real.exp (-b * ‖z‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (b : ℂ)) (by simpa using hb) 0 0
  refine h.norm.congr (Eventually.of_forall fun z => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re]
  rw [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- $\int_{\mathbb C}e^{-b|z|^2} = \pi/b$. -/
theorem integral_exp_neg_mul_sq_norm_complex {b : ℝ} (hb : 0 < b) :
    ∫ z : ℂ, Real.exp (-b * ‖z‖ ^ 2) = Real.pi / b := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb, Complex.finrank_real_complex]
  norm_num

/-- Products of the one-dimensional Gaussians on $\mathbb C^n$ are integrable. -/
theorem integrable_prod_exp_complex {n : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Fin n → ℂ => ∏ i, Real.exp (-b * ‖x i‖ ^ 2)) := by
  have hg : Integrable (fun x : Fin n → ℂ => ∏ i, Real.exp (-b * ‖x i‖ ^ 2))
      (Measure.pi fun _ : Fin n => (volume : Measure ℂ)) :=
    Integrable.fintype_prod fun _ => integrable_exp_neg_mul_sq_norm_complex hb
  rwa [← volume_pi] at hg

/-- $G_{\mathbb C}$ is Lebesgue integrable on $\mathbb C^n$. -/
theorem integrable_gaussFnC {n : ℕ} : Integrable (gaussFnC : (Fin n → ℂ) → ℝ) := by
  refine (integrable_prod_exp_complex (n := n) (by positivity : 0 < 2 * Real.pi)).congr
    (Eventually.of_forall fun x => (gaussFnC_eq_prod x).symm)

/-- $\|x\|^2 \le \sum_i |x_i|^2$ for $x \in \mathbb C^n$ (sup norm). -/
theorem sq_norm_le_sum_sq_complex {n : ℕ} (z : Fin n → ℂ) : ‖z‖ ^ 2 ≤ ∑ i, ‖z i‖ ^ 2 := by
  have hs : 0 ≤ ∑ i, ‖z i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h : ‖z‖ ≤ Real.sqrt (∑ i, ‖z i‖ ^ 2) :=
    (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i =>
      Real.le_sqrt_of_sq_le (Finset.single_le_sum (f := fun j => ‖z j‖ ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i))
  calc ‖z‖ ^ 2 ≤ Real.sqrt (∑ i, ‖z i‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ i, ‖z i‖ ^ 2 := Real.sq_sqrt hs

/-- A complex quadratic form is bounded by a multiple of $\sum_i|x_i|^2$. -/
theorem norm_eval_le_sum_sq {N : ℕ} (Q : QuadForm ℂ N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Fin N → ℂ, ‖Q.eval x‖ ≤ B * ∑ i, ‖x i‖ ^ 2 := by
  refine ⟨∑ i, ∑ j, ‖Q.coeff i j‖,
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _, fun x => ?_⟩
  have h := QuadFormsKB.ArchTest.norm_evalIn_le Q x
  refine h.trans (mul_le_mul_of_nonneg_left (sq_norm_le_sum_sq_complex x)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _))

/-- **Polynomial decay**: $(|Q(x)|^2)^s\,G_{\mathbb C}(x) \le K\prod_ie^{-\pi|x_i|^2}$ for $s \ge 0$. -/
theorem rpow_mul_gaussFnC_le {N : ℕ} (Q : QuadForm ℂ N) {s : ℝ} (hs : 0 ≤ s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Fin N → ℂ,
      (‖Q.eval x‖ ^ 2) ^ s * gaussFnC x ≤ K * ∏ i, Real.exp (-Real.pi * ‖x i‖ ^ 2) := by
  obtain ⟨B, hB0, hB⟩ := norm_eval_le_sum_sq Q
  obtain ⟨C, hC⟩ := exists_bound_rpow_mul_exp (s := 2 * s) (by positivity) Real.pi_pos
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 1 zero_le_one)
  refine ⟨(B ^ 2) ^ s * C, by positivity, fun x => ?_⟩
  set u := ∑ i, ‖x i‖ ^ 2 with hu
  have hu0 : 0 ≤ u := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hprod : ∏ i, Real.exp (-Real.pi * ‖x i‖ ^ 2) = Real.exp (-Real.pi * u) := by
    rw [← Real.exp_sum, hu, Finset.mul_sum]
  have hG : gaussFnC x = Real.exp (-Real.pi * u) * Real.exp (-Real.pi * u) := by
    rw [gaussFnC, ← Real.exp_add, hu]; congr 1; ring
  rw [hprod, hG]
  have h1 : ‖Q.eval x‖ ^ 2 ≤ (B * u) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hB x) 2
  have h2 : (‖Q.eval x‖ ^ 2) ^ s ≤ ((B * u) ^ 2) ^ s :=
    Real.rpow_le_rpow (by positivity) h1 hs
  have h3 : ((B * u) ^ 2) ^ s = (B ^ 2) ^ s * u ^ (2 * s) := by
    rw [mul_pow, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast u 2, ← Real.rpow_mul hu0]
    norm_num
  have h4 := hC u hu0
  have he := (Real.exp_pos (-Real.pi * u)).le
  calc (‖Q.eval x‖ ^ 2) ^ s * (Real.exp (-Real.pi * u) * Real.exp (-Real.pi * u))
      ≤ ((B ^ 2) ^ s * u ^ (2 * s)) * (Real.exp (-Real.pi * u) * Real.exp (-Real.pi * u)) := by
        rw [← h3]; exact mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = (B ^ 2) ^ s * (u ^ (2 * s) * Real.exp (-Real.pi * u)) * Real.exp (-Real.pi * u) := by ring
    _ ≤ (B ^ 2) ^ s * C * Real.exp (-Real.pi * u) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (by positivity)) he

/-- **Finiteness**: $\int_{\mathbb C^N}(|Q|^2)^sG_{\mathbb C}\,dx < \infty$ for $s \ge 0$. -/
theorem lintegral_gaussFnC_lt_top {N : ℕ} (Q : QuadForm ℂ N) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ x, ENNReal.ofReal ((‖Q.eval x‖ ^ 2) ^ s) * ENNReal.ofReal (gaussFnC x) < ⊤ := by
  obtain ⟨K, hK0, hK⟩ := rpow_mul_gaussFnC_le Q hs
  have hi : Integrable (fun x : Fin N → ℂ => K * ∏ i, Real.exp (-Real.pi * ‖x i‖ ^ 2)) :=
    (integrable_prod_exp_complex Real.pi_pos).const_mul _
  refine lt_of_le_of_lt ?_ hi.lintegral_lt_top
  refine lintegral_mono fun x => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (hK x)

/-- **Integrating along a fibre-counting measure**: $\int g(m(y))\,d(m^\#\nu) = \int g(z)\,\#m^{-1}(z)\,d\nu(z)$. -/
theorem lintegral_fibreCount_comp {Y Z : Type*} [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [TopologicalSpace Z] [T2Space Z] [MeasurableSpace Z] [BorelSpace Z] {m : Y → Z}
    (hm : Continuous m) (hloc : Leray.IsLocInj m) (ν : Measure Z) {g : Z → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, g (m y) ∂Leray.fibreCount m ν = ∫⁻ z, g z * Measure.count (m ⁻¹' {z}) ∂ν := by
  unfold Leray.fibreCount
  rw [Measure.lintegral_bind (f := fun y => g (m y)) (Leray.measurable_fibreKernel hm hloc).aemeasurable
    (hg.comp hm.measurable).aemeasurable]
  refine lintegral_congr fun z => ?_
  have hs : MeasurableSet (m ⁻¹' {z}) := hm.measurable (measurableSet_singleton z)
  rw [setLIntegral_congr_fun hs (g := fun _ => g z) (fun y hy => by
    have : m y = z := hy
    simp [this]), setLIntegral_const]

/-- **The polar map is two-to-one onto $\{Q \ne 0\}$**: the fibre over $z$ has exactly two points. -/
theorem count_polC_fibre {N : ℕ} (Q : QuadForm ℂ N) {c : ℂ} (hc : c ≠ 0) {z : Fin N → ℂ}
    (hz : Q.eval z ≠ 0) : Measure.count (polC Q c ⁻¹' {z}) = 2 := by
  obtain ⟨β0, hβ0⟩ := IsAlgClosed.exists_pow_nat_eq (Q.eval z / c) (two_pos : 0 < 2)
  have hβne : β0 ≠ 0 := by
    rintro rfl
    have : Q.eval z / c = 0 := by rw [← hβ0]; norm_num
    exact hz ((div_eq_zero_iff.mp this).resolve_right hc)
  have hx0 : Q.eval (β0⁻¹ • z) = c := by
    rw [eval_smulC, inv_pow, hβ0]
    field_simp
  let x0 : SphC Q c := ⟨β0⁻¹ • z, hx0⟩
  let p : ℂˣ × SphC Q c := (Units.mk0 β0 hβne, x0)
  let q : ℂˣ × SphC Q c := (-p.1, ⟨-(x0 : Fin N → ℂ), by
    show Q.eval _ = c
    rw [← neg_one_smul ℂ, eval_smulC, show Q.eval (x0 : Fin N → ℂ) = c from hx0]
    norm_num⟩)
  have hp : polC Q c p = z := by
    simp only [polC, p, x0, Units.val_mk0, smul_smul, mul_inv_cancel₀ hβne, one_smul]
  have hq : polC Q c q = z := by
    show (-β0) • (-(β0⁻¹ • z)) = z
    rw [smul_neg, neg_smul, neg_neg, smul_smul, mul_inv_cancel₀ hβne, one_smul]
  have hfib : polC Q c ⁻¹' {z} = {p, q} := by
    ext r
    simp only [mem_preimage, mem_singleton_iff, mem_insert_iff]
    constructor
    · intro h
      rcases polC_eq_imp hc (h.trans hp.symm) with h1 | h1
      · exact Or.inl (polC_eq_of_fst_eq (h.trans hp.symm) h1)
      · refine Or.inr (polC_eq_of_fst_eq (h.trans hq.symm) ?_)
        simp only [q, Units.val_neg]
        linear_combination -h1
    · rintro (rfl | rfl)
      · exact hp
      · exact hq
  have hne : p ≠ q := by
    intro h
    have h1 : (p.1 : ℂ) = (q.1 : ℂ) := congrArg (fun r => (r.1 : ℂ)) h
    simp only [q, Units.val_neg] at h1
    have : (p.1 : ℂ) = 0 := by linear_combination (1 / 2 : ℂ) * h1
    exact p.1.ne_zero this
  have hms : MeasurableSet (polC Q c ⁻¹' {z}) := (continuous_polC Q c).measurable (measurableSet_singleton z)
  rw [Measure.count_apply hms, hfib, Set.encard_pair hne]
  rfl

/-- **Two-to-one polar integration**: for $f$ vanishing on $\{Q = 0\}$,
$\int f(\beta x)\,d(\lambda\otimes\nu_c) = 2\int f$. -/
theorem lintegral_polC_comp {N : ℕ} (Q : QuadForm ℂ N) {c : ℂ} (hc : c ≠ 0) (hN : 1 ≤ N)
    {f : (Fin N → ℂ) → ℝ≥0∞} (hf : Measurable f) (hf0 : ∀ x, Q.eval x = 0 → f x = 0) :
    ∫⁻ p, f (polC Q c p) ∂(lamU N).prod (nuC Q c) = 2 * ∫⁻ x, f x := by
  rw [← fibreCount_polC (Q := Q) hc hN,
    lintegral_fibreCount_comp (continuous_polC Q c) (isLocInj_polC hc) volume hf,
    ← lintegral_const_mul 2 hf]
  refine lintegral_congr fun z => ?_
  by_cases hz : Q.eval z = 0
  · simp [hf0 z hz]
  · rw [count_polC_fibre Q hc hz, mul_comm]

/-- **The radial identity**: for $r > 0$, $r^{2N-2}\,(r^4C)^s = C^s\,(r^2)^{N+2s}(r^2)^{-1}$. -/
theorem radial_identity {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (N : ℕ) (s : ℝ) :
    r ^ (2 * (N : ℤ) - 2) * (r ^ 4 * C) ^ s = C ^ s * ((r ^ 2) ^ ((N : ℝ) + 2 * s) * (r ^ 2)⁻¹) := by
  have h1 : r ^ (2 * (N : ℤ) - 2) = r ^ ((2 * (N : ℝ) - 2)) := by
    rw [← Real.rpow_intCast]; push_cast; rfl
  have h2 : (r ^ 4 * C) ^ s = r ^ (4 * s) * C ^ s := by
    rw [Real.mul_rpow (by positivity) hC, ← Real.rpow_natCast r 4, ← Real.rpow_mul hr.le]
    norm_num
  have h3 : (r ^ 2) ^ ((N : ℝ) + 2 * s) = r ^ (2 * ((N : ℝ) + 2 * s)) := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]; norm_num
  have h4 : (r ^ 2)⁻¹ = r ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hr.le]; norm_num
  rw [h1, h2, h3, h4]
  have : 2 * (N : ℝ) - 2 + 4 * s = 2 * ((N : ℝ) + 2 * s) + -2 := by ring
  calc r ^ (2 * (N : ℝ) - 2) * (r ^ (4 * s) * C ^ s)
      = (r ^ (2 * (N : ℝ) - 2) * r ^ (4 * s)) * C ^ s := by ring
    _ = r ^ (2 * (N : ℝ) - 2 + 4 * s) * C ^ s := by rw [Real.rpow_add hr]
    _ = _ := by rw [this, Real.rpow_add hr]; ring

/-- **The radial integral on a fibre**: for $x \in S_c$,
$\int f(\beta x)\,d\lambda_N(\beta) = (|c|^2)^s\,M^{\mathbb C}_{N+2s}(x)$. -/
theorem lintegral_lamU_polC {N : ℕ} (Q : QuadForm ℂ N) (c : ℂ) (s : ℝ) (x : SphC Q c) :
    ∫⁻ β, ENNReal.ofReal ((‖Q.eval ((β : ℂ) • (x : Fin N → ℂ))‖ ^ 2) ^ s) *
        ENNReal.ofReal (gaussFnC ((β : ℂ) • (x : Fin N → ℂ))) ∂lamU N =
      ENNReal.ofReal ((‖c‖ ^ 2) ^ s) * archMellinC ((N : ℝ) + 2 * s) (x : Fin N → ℂ) := by
  set k : ℤ := 2 * (N : ℤ) - 2 with hk
  have hm : Measurable fun β : ℂˣ => ENNReal.ofReal ((‖Q.eval ((β : ℂ) • (x : Fin N → ℂ))‖ ^ 2) ^ s) *
      ENNReal.ofReal (gaussFnC ((β : ℂ) • (x : Fin N → ℂ))) := by
    have hc : Continuous fun β : ℂˣ => (β : ℂ) • (x : Fin N → ℂ) :=
      Units.continuous_val.smul continuous_const
    exact Measurable.mul (ENNReal.measurable_ofReal.comp
      ((((continuous_evalC Q).comp hc).measurable.norm.pow_const 2).pow_const s))
      (ENNReal.measurable_ofReal.comp (measurable_gaussFnC.comp hc.measurable))
  rw [lamU, lintegral_withDensity_eq_lintegral_mul volU (measurable_wt _) hm]
  set G : ℂ → ℝ≥0∞ := fun z => ((‖z‖₊ ^ k : ℝ≥0) : ℝ≥0∞) *
    (ENNReal.ofReal ((‖Q.eval (z • (x : Fin N → ℂ))‖ ^ 2) ^ s) *
      ENNReal.ofReal (gaussFnC (z • (x : Fin N → ℂ)))) with hG
  have e1 : ∫⁻ β : ℂˣ, G (β : ℂ) ∂volU = ∫⁻ z, G z ∂(volume.restrict {z : ℂ | z ≠ 0}) := by
    have hr := MeasurableEmbedding.map_comap SphereLerayC.measurableEmbedding_val (volume : Measure ℂ)
    rw [range_val] at hr
    rw [← hr, SphereLerayC.measurableEmbedding_val.lintegral_map]
    rfl
  have e2 : ∫⁻ β : ℂˣ, (wt k * fun β : ℂˣ => ENNReal.ofReal ((‖Q.eval ((β : ℂ) • (x : Fin N → ℂ))‖ ^ 2) ^ s) *
      ENNReal.ofReal (gaussFnC ((β : ℂ) • (x : Fin N → ℂ)))) β ∂volU = ∫⁻ β : ℂˣ, G (β : ℂ) ∂volU := rfl
  rw [e2, e1]
  have hpt : ∀ z ∈ {z : ℂ | z ≠ 0}, G z = ENNReal.ofReal ((‖c‖ ^ 2) ^ s) *
      (ENNReal.ofReal ((‖z‖ ^ 2) ^ ((N : ℝ) + 2 * s) * (‖z‖ ^ 2)⁻¹) * ENNReal.ofReal (gaussFnC (z • (x : Fin N → ℂ)))) := by
    intro z hz
    have hz' : z ≠ 0 := hz
    have hw : ((‖z‖₊ ^ k : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (‖z‖ ^ k) := by
      rw [← ENNReal.ofReal_coe_nnreal]; congr 1
    have hev : Q.eval (z • (x : Fin N → ℂ)) = z ^ 2 * c := by
      rw [eval_smulC, show Q.eval (x : Fin N → ℂ) = c from x.2]
    have hnorm : (‖z ^ 2 * c‖ ^ 2) ^ s = (‖z‖ ^ 4 * ‖c‖ ^ 2) ^ s := by
      congr 1; rw [norm_mul, norm_pow]; ring
    have rad := radial_identity (norm_pos_iff.mpr hz') (by positivity : 0 ≤ ‖c‖ ^ 2) N s
    simp only [hG]
    rw [hw, hev, hnorm, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity)]
    rw [hk, rad, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  rw [setLIntegral_congr_fun (by exact (measurableSet_singleton (0 : ℂ)).compl) hpt,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  have hs0 : {z : ℂ | z ≠ 0} = ({0} : Set ℂ)ᶜ := by ext z; simp
  rw [hs0, restrict_compl_singleton]
  rfl

/-- **Polar coordinates for the complex Mellin transform**:
$\int_{S_c}M^{\mathbb C}_{N+2s}\,d\sigma_c = 2\,|c|_{\mathbb C}^{-s}|2c|_{\mathbb C}^{-1}\int_{\mathbb C^N}|Q|_{\mathbb C}^sG_{\mathbb C}\,dx$. -/
theorem lintegral_archMellinC_sigC {N : ℕ} (Q : QuadForm ℂ N) {c : ℂ} (hc : c ≠ 0) (hN : 1 ≤ N) {s : ℝ}
    (hs : 0 < s) :
    ∫⁻ y, archMellinC ((N : ℝ) + 2 * s) (y : Fin N → ℂ) ∂sigC Q c =
      ENNReal.ofReal (2 * (‖c‖ ^ 2) ^ (-s) * (‖2 * c‖ ^ 2)⁻¹) *
        ∫⁻ x, ENNReal.ofReal ((‖Q.eval x‖ ^ 2) ^ s) * ENNReal.ofReal (gaussFnC x) := by
  have hsf := sigmaFinite_nuC (Q := Q) hc hN
  set f : (Fin N → ℂ) → ℝ≥0∞ := fun x => ENNReal.ofReal ((‖Q.eval x‖ ^ 2) ^ s) *
    ENNReal.ofReal (gaussFnC x) with hf
  have hfm : Measurable f :=
    Measurable.mul (ENNReal.measurable_ofReal.comp
      (((continuous_evalC Q).measurable.norm.pow_const 2).pow_const s))
      (ENNReal.measurable_ofReal.comp measurable_gaussFnC)
  have hf0 : ∀ x, Q.eval x = 0 → f x = 0 := by
    intro x hx
    simp [hf, hx, Real.zero_rpow hs.ne']
  have h1 := lintegral_polC_comp Q hc hN hfm hf0
  have hMm : Measurable fun x : SphC Q c => archMellinC ((N : ℝ) + 2 * s) (x : Fin N → ℂ) :=
    (measurable_archMellinC _).comp measurable_subtype_coe
  have h2 : ∫⁻ p, f (polC Q c p) ∂(lamU N).prod (nuC Q c) =
      ENNReal.ofReal ((‖c‖ ^ 2) ^ s) * ∫⁻ x, archMellinC ((N : ℝ) + 2 * s) (x : Fin N → ℂ) ∂nuC Q c := by
    rw [lintegral_prod_symm (fun p : ℂˣ × SphC Q c => f (polC Q c p)) (hfm.comp (continuous_polC Q c).measurable).aemeasurable,
      ← lintegral_const_mul _ hMm]
    exact lintegral_congr fun x => lintegral_lamU_polC Q c s x
  rw [h1, nuC_eq_smul_sigC hc, lintegral_smul_measure] at h2
  set I := ∫⁻ x, f x
  set J := ∫⁻ y, archMellinC ((N : ℝ) + 2 * s) (y : Fin N → ℂ) ∂sigC Q c
  have hP : 0 < (‖c‖ ^ 2) ^ s := Real.rpow_pos_of_pos (by have := norm_pos_iff.mpr hc; positivity) s
  have hD : 0 < ‖2 * c‖ ^ 2 := by
    have := norm_pos_iff.mpr (mul_ne_zero two_ne_zero hc); positivity
  have hK : (((‖2 * c‖₊ ^ 2 : ℝ≥0)) : ℝ≥0∞) = ENNReal.ofReal (‖2 * c‖ ^ 2) := by
    rw [← ENNReal.ofReal_coe_nnreal]; congr 1
  rw [hK, smul_eq_mul] at h2
  have e : ENNReal.ofReal (2 * (‖c‖ ^ 2) ^ (-s) * (‖2 * c‖ ^ 2)⁻¹) * I =
      ENNReal.ofReal (((‖c‖ ^ 2) ^ s)⁻¹ * (‖2 * c‖ ^ 2)⁻¹) * (2 * I) := by
    rw [← mul_assoc]; congr 1
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.rpow_neg (by positivity)]; ring
  rw [e, h2, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  have : ((‖c‖ ^ 2) ^ s)⁻¹ * (‖2 * c‖ ^ 2)⁻¹ * (‖c‖ ^ 2) ^ s * ‖2 * c‖ ^ 2 = 1 := by
    field_simp
  rw [this]; simp

/-- **$G_{\mathbb C}$ is an admissible test function at the complex places.** -/
theorem isArchTestFnC_gaussFnC {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) :
    SphericalNF.IsArchTestFnC Q₀ (fun _ => gaussFnC) := by
  refine ⟨fun _ => integrable_gaussFnC, fun w => ?_⟩
  obtain ⟨K, hK0, hK⟩ := rpow_mul_gaussFnC_le (SphericalNF.cplxForm Q₀ w) (s := 1) zero_le_one
  have hi : Integrable (fun x : Fin n → ℂ => K * ∏ i, Real.exp (-Real.pi * ‖x i‖ ^ 2)) :=
    (integrable_prod_exp_complex Real.pi_pos).const_mul _
  refine hi.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (((continuous_norm.comp (SphericalNF.continuous_cplxVal Q₀ w)).pow 2).mul
      (by unfold gaussFnC; fun_prop)).aestronglyMeasurable
  · have h := hK x
    rw [Real.rpow_one] at h
    have hnn : 0 ≤ ‖SphericalNF.cplxVal Q₀ w x‖ ^ 2 * gaussFnC x := by unfold gaussFnC; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact h

/-- **$2^n\int_{\mathbb C^n}G_{\mathbb C} = 1$.** -/
theorem integral_gaussFnC {n : ℕ} : (2 : ℝ) ^ n * ∫ x : Fin n → ℂ, gaussFnC x = 1 := by
  have h := integral_fintype_prod_volume_eq_prod (ι := Fin n) (𝕜 := ℝ) (E := fun _ => ℂ)
    (fun (_ : Fin n) (z : ℂ) => Real.exp (-(2 * Real.pi) * ‖z‖ ^ 2))
  simp_rw [gaussFnC_eq_prod]
  rw [h]
  simp_rw [integral_exp_neg_mul_sq_norm_complex (by positivity : 0 < 2 * Real.pi)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_pow]
  have : (2 : ℝ) * (Real.pi / (2 * Real.pi)) = 1 := by field_simp
  rw [this, one_pow]

/-- **The local identity at a complex place**: $\int_{T(\rho)_w}M^{\mathbb C}_{N+2s}\,d\sigma_w =
2Z_w(s)/(2^N|2\rho|_w|\rho|_w^s)$ with $Z_w$ = `cplxZetaAt` for $\Psi_w = G_{\mathbb C}$, $|z|_w = |z|^2$. -/
theorem lintegral_archMellinC_sigCx {F : Type} [Field F] [NumberField F] {k : ℕ} (Q₀ : QuadForm (𝓞 F) (k + 1))
    (w : {w : InfinitePlace F // w.IsComplex}) {ρ : F} (hρ : ρ ≠ 0) {s : ℝ} (hs : 0 < s) :
    ∫⁻ y, archMellinC (((k + 1 : ℕ) : ℝ) + 2 * s) (y : Fin (k + 1) → ℂ) ∂sigC (QCx Q₀ w) (σC w ρ) =
      ENNReal.ofReal (2 * SphericalNF.cplxZetaAt Q₀ w gaussFnC s /
        (2 ^ (k + 1) * (‖σC w (2 * ρ)‖ ^ 2 * (‖σC w ρ‖ ^ 2) ^ s))) := by
  have hc : σC w ρ ≠ 0 := (map_ne_zero _).mpr hρ
  have hcn : 0 < ‖σC w ρ‖ := norm_pos_iff.mpr hc
  rw [lintegral_archMellinC_sigC (QCx Q₀ w) hc (Nat.succ_pos k) hs]
  have hval : ∀ x : Fin (k + 1) → ℂ, SphericalNF.cplxVal Q₀ w x = (QCx Q₀ w).eval x := by
    intro x
    simp [SphericalNF.cplxVal, SphericalNF.cplxForm, QuadForm.eval, QuadForm.evalIn, QuadForm.map, QCx]
  have hdef : SphericalNF.cplxZetaAt Q₀ w gaussFnC s =
      2 ^ (k + 1) * ∫ x, (‖(QCx Q₀ w).eval x‖ ^ 2) ^ s * gaussFnC x := by
    simp only [SphericalNF.cplxZetaAt, hval]
  have hlt := lintegral_gaussFnC_lt_top (QCx Q₀ w) hs.le
  have hint : ∫ x, (‖(QCx Q₀ w).eval x‖ ^ 2) ^ s * gaussFnC x =
      (∫⁻ x, ENNReal.ofReal ((‖(QCx Q₀ w).eval x‖ ^ 2) ^ s) * ENNReal.ofReal (gaussFnC x)).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae]
    · congr 2
      funext x
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
    · exact Filter.Eventually.of_forall fun x => mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (by unfold gaussFnC; positivity)
    · exact (((((continuous_evalC (QCx Q₀ w)).measurable.norm.pow_const 2).pow_const s).mul
        measurable_gaussFnC)).aestronglyMeasurable
  rw [hdef, hint]
  conv_lhs => rw [← ENNReal.ofReal_toReal hlt.ne]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  set J := (∫⁻ x, ENNReal.ofReal ((‖(QCx Q₀ w).eval x‖ ^ 2) ^ s) * ENNReal.ofReal (gaussFnC x)).toReal
  have h2 : ‖σC w (2 * ρ)‖ = ‖2 * σC w ρ‖ := by rw [map_mul, map_ofNat]
  have hpow : 0 < (‖σC w ρ‖ ^ 2) ^ s := Real.rpow_pos_of_pos (by positivity) s
  rw [h2, Real.rpow_neg (by positivity), norm_mul, Complex.norm_ofNat]
  field_simp

end QuadFormsKB.Tamagawa.Measure.Weil

end
