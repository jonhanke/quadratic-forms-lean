/-
# The Weil representation at a finite place

**Layer:** local, non-archimedean. Every finite place $v$ of a number field $F$, dyadic places included.

**Test functions** (`SBK K`, for any non-archimedean local field $K$ with a standard character $\psi$ and a Haar
measure $\mu$): $f : K \to \mathbb C$ with bounded support and invariant under a small ball,
$$\exists R,\ \varepsilon > 0:\quad f(x) \ne 0 \Rightarrow \|x\| \le R,\qquad f(x + h) = f(x)\ \ (\|h\| \le \varepsilon),$$
i.e. the locally constant compactly supported functions. At $K = F_v$ they are exactly the repo's Schwartz–Bruhat
functions (`isSchwartzBruhatV_of_mem_SBK`: every such $f$ is a finite combination of coset indicators).

**General $K$** (proved here, for every non-archimedean $K$ with $2 \ne 0$):
* closure under $e_s$, $D_t$ and $\mathcal F$ (`chirp_mem_SBK`, `dil_mem_SBK`, `four_mem_SBK`);
* **the Weil identity for every test function** (`weil_identity_SBK`):
  $$\mathcal F\big(e_b\,\mathcal Ff\big)(y) = \gamma(b)\,\psi(cy^2)\,\mathcal F(e_cf)(2cy),\qquad c = -(4b)^{-1},$$
  with $\gamma(b)$ the Gauss integral `Weil.gaussInt` (generalizing `Weil.weil_identity_ball`, same proof).

**At a finite place** (`localDataV v`, `isModel_V`): $\psi_v$ (`psiV`), the self-dual measure (`selfDualV`), the
Haar modulus (`Weil.modK`), the Weil constant $\gamma_v$ (`weilV`), the Hilbert symbol over $F_v$; all axioms of
`LocalData.IsModel` hold, with Fourier inversion from `fourierInvV_fourierV_of_isSchwartzBruhat` and the
Weil–Hilbert identity $\gamma_v(ab)\gamma_v(1) = (a,b)_v\gamma_v(a)\gamma_v(b)$ from `HN.weilV_mul_identity`.

**Headline** (`weilRepV`): for $a_0, \dots, a_{2m-1} \in F_v^\times$, the Weil representation
$$\omega_v : \mathrm{SL}_2(F_v) \to \operatorname{End}_{\mathbb C}S(V_v),\qquad V_v = \langle a_0, \dots, a_{2m-1}\rangle,$$
a monoid homomorphism with the Schrödinger-model formulas on $n(b)$, $m(t)$, $w$.

Sources: Weil, Acta Math. 111 (1964), §14 [unverified]; Kudla, *Notes on the local theta correspondence*, §I.1
[unverified]; Rao (1993), §3 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Model
import QuadFormsKB.Analysis.WeilIndexNF
import QuadFormsKB.Literature.HasseNorm.Reciprocity

open MeasureTheory Metric
open scoped NNReal MatrixGroups

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep

/-! ### Test functions on a non-archimedean local field -/

section General

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [BorelSpace K]

/-- **Test functions on a non-archimedean local field $K$:** the locally constant compactly supported
$f : K \to \mathbb C$, i.e. there are $R$ and $\varepsilon > 0$ with $f(x) \ne 0 \Rightarrow \|x\| \le R$ and
$f(x+h) = f(x)$ for $\|h\| \le \varepsilon$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §1.3, pp. 307–308 (Tate's class 𝔅₁: f continuous and integrable with f̂ integrable)"]
def SBK : Submodule ℂ (K → ℂ) where
  carrier := {f | ∃ R ε : ℝ, 0 < ε ∧ (∀ x, f x ≠ 0 → ‖x‖ ≤ R) ∧ ∀ x h, ‖h‖ ≤ ε → f (x + h) = f x}
  zero_mem' := ⟨0, 1, one_pos, fun x h => absurd rfl h, fun _ _ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨R, ε, hε, hR, hinv⟩ ⟨R', ε', hε', hR', hinv'⟩
    refine ⟨max R R', min ε ε', lt_min hε hε', fun x hx => ?_, fun x h hh => ?_⟩
    · by_cases hf : f x = 0
      · have : g x ≠ 0 := by intro hg; apply hx; simp [hf, hg]
        exact (hR' x this).trans (le_max_right _ _)
      · exact (hR x hf).trans (le_max_left _ _)
    · simp only [Pi.add_apply]
      rw [hinv x h (hh.trans (min_le_left _ _)), hinv' x h (hh.trans (min_le_right _ _))]
  smul_mem' := by
    rintro c f ⟨R, ε, hε, hR, hinv⟩
    refine ⟨R, ε, hε, fun x hx => hR x fun h => hx (by simp [h]), fun x h hh => ?_⟩
    simp only [Pi.smul_apply, hinv x h hh]

variable {K}

lemma mem_SBK {f : K → ℂ} :
    f ∈ SBK K ↔ ∃ R ε : ℝ, 0 < ε ∧ (∀ x, f x ≠ 0 → ‖x‖ ≤ R) ∧ ∀ x h, ‖h‖ ≤ ε → f (x + h) = f x := Iff.rfl

lemma continuous_of_mem_SBK {f : K → ℂ} (hf : f ∈ SBK K) : Continuous f := by
  obtain ⟨R, ε, hε, -, hinv⟩ := hf
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have : f =ᶠ[nhds x] fun _ => f x := by
    filter_upwards [closedBall_mem_nhds x hε] with y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    have := hinv x (y - x) hy
    rwa [add_sub_cancel] at this
  exact continuousAt_const.congr this.symm

lemma hasCompactSupport_of_mem_SBK {f : K → ℂ} (hf : f ∈ SBK K) : HasCompactSupport f := by
  obtain ⟨R, ε, -, hR, -⟩ := hf
  refine HasCompactSupport.intro (isCompact_closedBall (0 : K) R) fun x hx => ?_
  by_contra h
  exact hx (by rw [mem_closedBall, dist_zero_right]; exact hR x h)

lemma norm_two_le_one' : ‖(2 : K)‖ ≤ 1 := by
  rw [show (2 : K) = ((2 : ℕ) : K) by norm_num]; exact IsUltrametricDist.norm_natCast_le_one _ _

/-- Indicators of closed balls are test functions. -/
lemma indicator_closedBall_mem_SBK (c : K) {ρ : ℝ} (hρ : 0 < ρ) :
    (closedBall c ρ).indicator (fun _ => (1 : ℂ)) ∈ SBK K := by
  refine ⟨max ‖c‖ ρ, ρ, hρ, fun x hx => ?_, fun x h hh => ?_⟩
  · have hx' : x ∈ closedBall c ρ := by by_contra h; exact hx (Set.indicator_of_notMem h _)
    rw [mem_closedBall, dist_eq_norm] at hx'
    calc ‖x‖ = ‖(x - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ max ‖x - c‖ ‖c‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ max ‖c‖ ρ := by rw [max_comm]; exact max_le_max le_rfl hx'
  · have : x + h ∈ closedBall c ρ ↔ x ∈ closedBall c ρ := by
      simp only [mem_closedBall, dist_eq_norm]
      constructor
      · intro h1
        calc ‖x - c‖ = ‖(x + h - c) + -h‖ := by congr 1; ring
          _ ≤ max ‖x + h - c‖ ‖-h‖ := IsUltrametricDist.norm_add_le_max _ _
          _ ≤ ρ := max_le h1 (by rwa [norm_neg])
      · intro h1
        calc ‖x + h - c‖ = ‖(x - c) + h‖ := by congr 1; ring
          _ ≤ max ‖x - c‖ ‖h‖ := IsUltrametricDist.norm_add_le_max _ _
          _ ≤ ρ := max_le h1 hh
    by_cases hx : x ∈ closedBall c ρ
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (this.mpr hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (this.mp h'))]

variable {ψ : AddChar K Circle}

lemma continuous_psi_mul (hψ : Analysis.Weil.IsStdChar ψ) (y : K) : Continuous fun x : K => (ψ (x * y) : ℂ) :=
  continuous_subtype_val.comp (hψ.cont.comp (continuous_id.mul continuous_const))

lemma integrable_mul_psi_SBK (μ : Measure K) [IsFiniteMeasureOnCompacts μ] (hψ : Analysis.Weil.IsStdChar ψ)
    {f : K → ℂ} (hf : f ∈ SBK K) (y : K) : Integrable (fun x => f x * (ψ (x * y) : ℂ)) μ :=
  ((continuous_of_mem_SBK hf).mul (continuous_psi_mul hψ y)).integrable_of_hasCompactSupport
    ((hasCompactSupport_of_mem_SBK hf).mul_right)

/-- Test functions are stable under chirps $e_sf(x) = \psi(sx^2)f(x)$. -/
lemma chirp_mem_SBK (hψ : Analysis.Weil.IsStdChar ψ) {f : K → ℂ} (hf : f ∈ SBK K) (s : K) :
    (fun x => (ψ (s * x ^ 2) : ℂ) * f x) ∈ SBK K := by
  obtain ⟨R, ε, hε, hR, hinv⟩ := hf
  obtain ⟨r, hr, hr1⟩ := hψ.triv
  set ε' : ℝ := min ε (min 1 (r / ((‖s‖ + 1) * (|R| + 1)))) with hε'
  have hpos : 0 < (‖s‖ + 1) * (|R| + 1) := by positivity
  have hε'pos : 0 < ε' := lt_min hε (lt_min one_pos (div_pos hr hpos))
  refine ⟨R, ε', hε'pos, fun x hx => hR x fun h => hx (by simp [h]), fun x h hh => ?_⟩
  have hhε : ‖h‖ ≤ ε := hh.trans (min_le_left _ _)
  show (ψ (s * (x + h) ^ 2) : ℂ) * f (x + h) = (ψ (s * x ^ 2) : ℂ) * f x
  rw [hinv x h hhε]
  by_cases hfx : f x = 0
  · simp [hfx]
  have hx := hR x hfx
  have h1 : ‖h‖ ≤ 1 := hh.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h2 : ‖h‖ ≤ r / ((‖s‖ + 1) * (|R| + 1)) := hh.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsmall : ‖2 * s * x * h + s * h ^ 2‖ ≤ r := by
    have hb : (‖s‖ + 1) * (|R| + 1) * ‖h‖ ≤ r := by
      rw [le_div_iff₀ hpos] at h2; linarith
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_mul, norm_mul]
      calc ‖(2 : K)‖ * ‖s‖ * ‖x‖ * ‖h‖ ≤ 1 * (‖s‖ + 1) * (|R| + 1) * ‖h‖ := by
            gcongr
            · exact norm_two_le_one'
            · linarith
            · exact hx.trans ((le_abs_self R).trans (by linarith))
        _ ≤ r := by linarith
    · rw [norm_mul, norm_pow]
      calc ‖s‖ * ‖h‖ ^ 2 ≤ (‖s‖ + 1) * (|R| + 1) * ‖h‖ := by
            have : ‖h‖ ^ 2 ≤ ‖h‖ := by nlinarith [norm_nonneg h]
            have h3 : ‖s‖ ≤ (‖s‖ + 1) * (|R| + 1) := by nlinarith [abs_nonneg R, norm_nonneg s]
            calc ‖s‖ * ‖h‖ ^ 2 ≤ ‖s‖ * ‖h‖ := by gcongr
              _ ≤ (‖s‖ + 1) * (|R| + 1) * ‖h‖ := by gcongr
        _ ≤ r := hb
  rw [show s * (x + h) ^ 2 = s * x ^ 2 + (2 * s * x * h + s * h ^ 2) by ring, AddChar.map_add_eq_mul,
    hr1 _ hsmall, mul_one]

/-- Test functions are stable under dilations $D_tf(x) = f(tx)$, $t \ne 0$. -/
lemma dil_mem_SBK {f : K → ℂ} (hf : f ∈ SBK K) {t : K} (ht : t ≠ 0) : dil t f ∈ SBK K := by
  obtain ⟨R, ε, hε, hR, hinv⟩ := hf
  have htn : 0 < ‖t‖ := norm_pos_iff.mpr ht
  refine ⟨R / ‖t‖, ε / ‖t‖, div_pos hε htn, fun x hx => ?_, fun x h hh => ?_⟩
  · have := hR _ hx
    rw [norm_mul] at this
    rw [le_div_iff₀ htn]; linarith
  · show f (t * (x + h)) = f (t * x)
    rw [mul_add]
    refine hinv _ _ ?_
    rw [norm_mul]
    rw [le_div_iff₀ htn] at hh; linarith

variable (μ : Measure K) [μ.IsAddHaarMeasure]

/-- The Fourier transform $\mathcal Ff(y) = \int_K f(x)\psi(xy)\,d\mu(x)$. -/
def fourK (f : K → ℂ) (y : K) : ℂ := ∫ x, f x * (ψ (x * y) : ℂ) ∂μ

variable {μ}

/-- The transform of a test function vanishes outside a ball. -/
lemma fourK_eq_zero_of_large (hψ : Analysis.Weil.IsStdChar ψ) {f : K → ℂ} (hf : f ∈ SBK K) :
    ∃ R₁ : ℝ, ∀ y, R₁ < ‖y‖ → fourK (ψ := ψ) μ f y = 0 := by
  obtain ⟨R, ε, hε, -, hinv⟩ := hf
  obtain ⟨A, hA, hA1⟩ := hψ.exists_large
  refine ⟨A / ε, fun y hy => ?_⟩
  obtain ⟨h, hh, hψh⟩ := hA1 y ε (by rw [div_lt_iff₀ hε] at hy; linarith)
  have key : fourK (ψ := ψ) μ f y = (ψ (y * h) : ℂ) * fourK (ψ := ψ) μ f y := by
    unfold fourK
    conv_lhs => rw [← integral_add_right_eq_self _ h]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [hinv x h hh, add_mul, AddChar.map_add_eq_mul, Circle.coe_mul, mul_comm h y]
    ring
  have hne : (ψ (y * h) : ℂ) ≠ 1 := fun h1 => hψh (Subtype.ext h1)
  have : (1 - (ψ (y * h) : ℂ)) * fourK (ψ := ψ) μ f y = 0 := by linear_combination key
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (by linear_combination -h0) hne
  · exact h0

/-- Test functions are stable under the Fourier transform. -/
lemma four_mem_SBK (hψ : Analysis.Weil.IsStdChar ψ) {f : K → ℂ} (hf : f ∈ SBK K) : fourK (ψ := ψ) μ f ∈ SBK K := by
  obtain ⟨R₁, hR₁⟩ := fourK_eq_zero_of_large (μ := μ) hψ hf
  obtain ⟨R, ε, hε, hR, hinv⟩ := hf
  obtain ⟨r, hr, hr1⟩ := hψ.triv
  refine ⟨R₁, r / (|R| + 1), div_pos hr (by positivity), fun y hy => ?_, fun y h hh => ?_⟩
  · by_contra h; exact hy (hR₁ y (lt_of_not_ge h))
  · unfold fourK
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    by_cases hfx : f x = 0
    · simp [hfx]
    have hx := hR x hfx
    have hxh : ‖x * h‖ ≤ r := by
      rw [norm_mul]
      have h1 : ‖x‖ ≤ |R| + 1 := hx.trans ((le_abs_self R).trans (by linarith))
      rw [le_div_iff₀ (by positivity)] at hh
      nlinarith [norm_nonneg x, norm_nonneg h]
    rw [mul_add, AddChar.map_add_eq_mul, hr1 _ hxh, mul_one]

/-- **The Weil identity for every test function** (generalizing `Weil.weil_identity_ball`): for $b \ne 0$,
$c = -(4b)^{-1}$ and $f$ locally constant with compact support,
$$\mathcal F\big(\psi(bx^2)\,\mathcal Ff\big)(y) = \gamma(b)\,\psi(cy^2)\,\mathcal F\big(\psi(cx^2)f\big)(2cy),$$
$\gamma(b)$ = `Weil.gaussInt μ ψ b`. *Proof:* as for a ball: both sides are $\iint f(z)\psi(bx^2 + xz + xy)$ over
$B_R \times B_r$ (complete the square in $x$, shift by $w = (z+y)/2b$, $\|w\| \le R$), and Fubini. -/
theorem weil_identity_SBK (hψ : Analysis.Weil.IsStdChar ψ) (h2 : (2 : K) ≠ 0) {b : K} (hb : b ≠ 0)
    {f : K → ℂ} (hf : f ∈ SBK K) (y : K) :
    fourK (ψ := ψ) μ (fun x => (ψ (b * x ^ 2) : ℂ) * fourK (ψ := ψ) μ f x) y =
      Analysis.Weil.gaussInt μ ψ b * (ψ (-(4 * b)⁻¹ * y ^ 2) : ℂ) *
        fourK (ψ := ψ) μ (fun x => (ψ (-(4 * b)⁻¹ * x ^ 2) : ℂ) * f x) (2 * (-(4 * b)⁻¹) * y) := by
  set c : K := -(4 * b)⁻¹ with hc
  obtain ⟨R₁, hR₁⟩ := fourK_eq_zero_of_large (μ := μ) hψ hf
  obtain ⟨C, hC⟩ := (continuous_of_mem_SBK hf).bounded_above_of_compact_support
    (hasCompactSupport_of_mem_SBK hf)
  have hfc := continuous_of_mem_SBK hf
  obtain ⟨Rf, -, -, hRf, -⟩ := hf
  obtain ⟨R₀, hR₀⟩ := Analysis.Weil.gaussInt_spec (μ := μ) hψ h2 hb
  have h2b : 0 < ‖2 * b‖ := norm_pos_iff.mpr (mul_ne_zero h2 hb)
  set R : ℝ≥0 := max R₀ (max ⟨|R₁|, abs_nonneg _⟩ ⟨max |Rf| ‖y‖ / ‖2 * b‖, by positivity⟩) with hRdef
  have hR1 : |R₁| ≤ R := by
    have : (⟨|R₁|, abs_nonneg _⟩ : ℝ≥0) ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
    exact_mod_cast this
  have hRw : max |Rf| ‖y‖ / ‖2 * b‖ ≤ R := by
    have : (⟨max |Rf| ‖y‖ / ‖2 * b‖, by positivity⟩ : ℝ≥0) ≤ R :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    exact_mod_cast this
  set BR : Set K := (Analysis.Weil.bsub K R : Set K) with hBR
  set H : Set K := closedBall (0 : K) |Rf| with hH
  have hBRm : MeasurableSet BR := Analysis.Weil.measurableSet_bsub R
  have hHm : MeasurableSet H := measurableSet_closedBall
  have hfH : ∀ z, z ∉ H → f z = 0 := by
    intro z hz; by_contra h
    exact hz (by rw [mem_closedBall, dist_zero_right]; exact (hRf z h).trans (le_abs_self _))
  have hF0 : ∀ x, x ∉ BR → fourK (ψ := ψ) μ f x = 0 := by
    intro x hx
    refine hR₁ x ?_
    have : (R : ℝ) < ‖x‖ := lt_of_not_ge hx
    exact lt_of_le_of_lt ((le_abs_self R₁).trans hR1) this
  have hfun : ∀ x z : K, (ψ (b * x ^ 2) : ℂ) * (f z * (ψ (z * x) : ℂ)) * (ψ (x * y) : ℂ) =
      f z * (ψ (b * x ^ 2 + x * z + x * y) : ℂ) := by
    intro x z
    rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, Circle.coe_mul, Circle.coe_mul, mul_comm z x]
    ring
  -- the left side as an iterated integral over `B_R × H`
  have hL : fourK (ψ := ψ) μ (fun x => (ψ (b * x ^ 2) : ℂ) * fourK (ψ := ψ) μ f x) y =
      ∫ x in BR, ∫ z in H, f z * (ψ (b * x ^ 2 + x * z + x * y) : ℂ) ∂μ ∂μ := by
    show ∫ x, (ψ (b * x ^ 2) : ℂ) * fourK (ψ := ψ) μ f x * (ψ (x * y) : ℂ) ∂μ = _
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := BR) (fun x hx => by rw [hF0 x hx]; simp)]
    refine setIntegral_congr_fun hBRm fun x _ => ?_
    simp only [fourK]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := H) (fun z hz => by rw [hfH z hz]; simp),
      ← integral_const_mul, ← integral_mul_const]
    refine setIntegral_congr_fun hHm fun z _ => ?_
    exact hfun x z
  -- the right side as an iterated integral over `H × B_R`
  have hR : Analysis.Weil.gaussInt μ ψ b * (ψ (c * y ^ 2) : ℂ) *
      fourK (ψ := ψ) μ (fun x => (ψ (c * x ^ 2) : ℂ) * f x) (2 * c * y) =
      ∫ z in H, ∫ x in BR, f z * (ψ (b * x ^ 2 + x * z + x * y) : ℂ) ∂μ ∂μ := by
    simp only [fourK]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := H) (fun z hz => by rw [hfH z hz]; simp),
      ← integral_const_mul]
    refine setIntegral_congr_fun hHm fun z hz => ?_
    have hw : ‖(z + y) / (2 * b)‖ ≤ R := by
      rw [norm_div]
      refine le_trans ?_ hRw
      gcongr
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ le_rfl)
      rw [mem_closedBall, dist_zero_right] at hz; exact hz
    rw [integral_const_mul, ← hR₀ R (le_max_left _ _), Analysis.Weil.gaussI,
      ← Analysis.Weil.setIntegral_bsub_add μ (fun x => (ψ (b * x ^ 2) : ℂ)) hw, ← integral_mul_const,
      ← integral_mul_const, ← integral_const_mul]
    refine setIntegral_congr_fun hBRm fun x _ => ?_
    simp only [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    have h4 : (4 : K) ≠ 0 := by
      rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
    have e : b * (x + (z + y) / (2 * b)) ^ 2 + (c * y ^ 2 + (c * z ^ 2 + z * (2 * c * y))) =
        b * x ^ 2 + x * z + x * y := by
      rw [hc]; field_simp; ring
    have hψ3 : (ψ (b * (x + (z + y) / (2 * b)) ^ 2 + c * y ^ 2) : ℂ) * (ψ (c * z ^ 2) : ℂ) *
        (ψ (z * (2 * c * y)) : ℂ) = (ψ (b * x ^ 2 + x * z + x * y) : ℂ) := by
      rw [← Circle.coe_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 2
      linear_combination e
    linear_combination (f z) * hψ3
  rw [hL, hR]
  have : IsFiniteMeasure (μ.restrict BR) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (Analysis.Weil.measure_bsub_ne_top μ R).lt_top⟩
  have : IsFiniteMeasure (μ.restrict H) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall _ _).measure_lt_top⟩
  refine integral_integral_swap (Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun p => ?_))
  · exact ((hfc.comp continuous_snd).mul (continuous_subtype_val.comp (hψ.cont.comp
      ((continuous_const.mul (continuous_fst.pow 2)).add (continuous_fst.mul continuous_snd) |>.add
        (continuous_fst.mul continuous_const))))).aestronglyMeasurable
  · simp only [Function.uncurry, norm_mul, Circle.norm_coe, mul_one]
    exact hC p.2

end General

/-! ### The instance at a finite place of a number field -/

section Place

open IsDedekindDomain NumberField Analysis

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- **Test functions at $F_v$ are Schwartz–Bruhat functions** in the repo's sense (finite combinations of coset
indicators $\mathbf 1_{c + \mathfrak p_v^k}$). -/
theorem isSchwartzBruhatV_of_mem_SBK {f : Fv → ℂ} (hf : f ∈ SBK Fv) : IsSchwartzBruhatV v f := by
  obtain ⟨R, ε, hε, hR, hinv⟩ := hf
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (norm_ϖ_lt_one v)
  set k : ℤ := (n : ℤ)
  have hk : ‖HN.ϖ v ^ k‖ ≤ ε := by
    rw [show k = (n : ℤ) from rfl, zpow_natCast, norm_pow]; exact hn.le
  set P : AddSubgroup Fv := latticeV v k
  have hPo : IsOpen (P : Set Fv) := by
    rw [coe_latticeV]
    exact IsUltrametricDist.isOpen_closedBall _ (norm_ne_zero_iff.mpr (zpow_ne_zero _ (HN.ϖ_ne_zero v)))
  set ρ : ℝ≥0 := ⟨max |R| ‖HN.ϖ v ^ k‖, le_max_of_le_right (norm_nonneg _)⟩
  set L : AddSubgroup Fv := Analysis.Weil.bsub Fv ρ
  have hLc : IsCompact (L : Set Fv) := Analysis.Weil.isCompact_bsub ρ
  have hPL : P ≤ L := fun x hx => by
    have : x ∈ (P : Set Fv) := hx
    rw [coe_latticeV, mem_closedBall, dist_zero_right] at this
    exact Analysis.Weil.mem_bsub.mpr (this.trans (le_max_right _ _))
  obtain ⟨N, c, -, hsum⟩ := Analysis.Weil.exists_coset_sum L P hLc hPo hPL f fun x _ h hh => by
    have : h ∈ (P : Set Fv) := hh
    rw [coe_latticeV, mem_closedBall, dist_zero_right] at this
    exact hinv x h (this.trans hk)
  refine ⟨N, fun i => f (c i), c, fun _ => k, funext fun x => ?_⟩
  have hfx : f x = (L : Set Fv).indicator f x := by
    by_cases hx : f x = 0
    · rw [hx]; by_cases hxL : x ∈ (L : Set Fv)
      · rw [Set.indicator_of_mem hxL, hx]
      · rw [Set.indicator_of_notMem hxL]
    · have hxL : x ∈ (L : Set Fv) :=
        Analysis.Weil.mem_bsub.mpr ((hR x hx).trans ((le_abs_self R).trans (le_max_left _ _)))
      rw [Set.indicator_of_mem hxL]
  rw [hfx, hsum x]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1

/-- **The local data at a finite place $v$:** $\psi_v$, the self-dual measure, the Haar modulus, the Weil constant
$\gamma_v$ (`weilV`), the Hilbert symbol of $F_v$, and the test functions `SBK`. -/
@[kb "weil1964" "§14 (local data at a $\\mathfrak p$-adic place) [unverified]"]
def localDataV : LocalData Fv where
  ψ := psiV v
  μ := selfDualV v
  md := Analysis.Weil.modK Fv
  γ := weilV v
  hilb := hilbertSymbol Fv
  S := SBK Fv
  two := Units.mk0 2 two_ne_zero
  two_eq := rfl

lemma localDataV_four (f : Fv → ℂ) : (localDataV v).four f = fourierV v f := rfl

lemma isOps_V : (localDataV v).IsOps where
  sigmaFinite := by show SigmaFinite (selfDualV v); infer_instance
  md_pos t := Analysis.Weil.modK_pos t.ne_zero
  md_mul s t := Analysis.Weil.modK_mul s.ne_zero t.ne_zero
  integrable_char f hf y := integrable_mul_psi_SBK (selfDualV v) (isStdChar_psiV v) hf y
  chirp_mem f hf s := chirp_mem_SBK (isStdChar_psiV v) hf s
  dil_mem f hf t := dil_mem_SBK hf t.ne_zero
  four_mem f hf := four_mem_SBK (μ := selfDualV v) (isStdChar_psiV v) hf
  hilb_pm s t := HN.hilbertSymbol_eq_one_or _ _ _
  hilb_comm s t := hilbertSymbol_comm _ _ _
  hilb_mul_left s s' t := HN.hilbertSymbol_mul_left_finite_nf v _ _ _ s.ne_zero s'.ne_zero t.ne_zero
  hilb_neg s := by
    show hilbertSymbol Fv s (-(s : Fv)) = 1
    unfold hilbertSymbol; exact if_pos ⟨1, 1, 0, by simp, by ring⟩

/-- **All axioms of the local model hold at every finite place** (dyadic places included). -/
@[kb "weil1964" "§14, §26–28 [unverified]"]
theorem isModel_V : (localDataV v).IsModel where
  toIsOps := isOps_V v
  inversion f hf x := by
    have := congrFun (fourierInvV_fourierV_of_isSchwartzBruhat v (isSchwartzBruhatV_of_mem_SBK v hf)) (-x)
    rw [← this, localDataV_four, localDataV_four]
    unfold fourierInvV
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [neg_mul, neg_neg, mul_comm y x]
  four_dil f hf t y := by
    have := Analysis.Weil.integral_comp_mul_left (μ := selfDualV v)
      (fun x => f x * (psiV v (x * (↑t⁻¹ * y)) : ℂ)) t.ne_zero
    show ∫ x, f (t * x) * (psiV v (x * y) : ℂ) ∂selfDualV v = _
    have e : ∀ x : Fv, (t : Fv) * x * (↑t⁻¹ * y) = x * y := fun x => by
      rw [show (t : Fv) * x * (↑t⁻¹ * y) = x * y * ((t : Fv) * ↑t⁻¹) by ring, Units.mul_inv, mul_one]
    simp only [e] at this
    rw [this, Complex.real_smul, Complex.ofReal_inv]
    rfl
  weil f hf b y := by
    have hc : (((localDataV v).cW b : (Fv)ˣ) : Fv) = -(4 * (b : Fv))⁻¹ := by
      simp only [LocalData.cW, Units.val_neg, Units.val_inv_eq_inv_val, Units.val_mul]
      simp [localDataV]; norm_num
    rw [hc]
    exact weil_identity_SBK (μ := selfDualV v) (isStdChar_psiV v) two_ne_zero b.ne_zero hf y
  γ_sq t s := by
    show weilV v ((t : Fv) * (s : Fv) ^ 2) = _
    rw [weilV, Analysis.Weil.gaussInt_mul_sq (isStdChar_psiV v) two_ne_zero t.ne_zero s.ne_zero,
      Complex.real_smul, Complex.ofReal_inv]
    rfl
  weil_hilb s t := HN.weilV_mul_identity v s.ne_zero t.ne_zero
  nontrivial := ⟨(closedBall (0 : Fv) 1).indicator fun _ => (1 : ℂ),
    indicator_closedBall_mem_SBK 0 one_pos, fun h => by
      have := congrFun h 0
      simp at this⟩

/-- **The local Weil representation at a finite place** $v$ of a number field $F$ (dyadic places included), for the
quadratic space $V_v = \langle a_0, \dots, a_{2m-1}\rangle$ over $F_v$ of even dimension $n = 2m$:
$$\omega_v : \mathrm{SL}_2(F_v) \to \operatorname{End}_{\mathbb C}S(V_v),$$
a monoid homomorphism (no metaplectic cover, $n$ even) with
$\omega_v(n(b))\Phi(x) = \psi_v(bQ(x))\Phi(x)$, $\omega_v(m(t))\Phi(x) = \chi_V(t)|t|_v^{m}\Phi(tx)$,
$\omega_v(w)\Phi = \gamma_V\hat\Phi$ (`LocalData.weilRep_nMat`, `_mMat`, `_wMat`). Here $\psi_v = \psi_p\circ\operatorname{Tr}$,
$|t|_v$ is the Haar modulus, $\chi_V(t) = (t, (-1)^m\det V)_v$, $\hat\Phi(y) = \int\Phi(x)\psi_v(B(x,y))\,d\mu_B$ with the
self-dual measure, and $\gamma_V = \chi_V(-1)\prod_ig_v(a_i)^{-1}$, $g_v(t) = \gamma_v(t)|2t|_v^{1/2}$. -/
@[kb "weil1964" "§14, Thm. 2 (even $n$: a true representation) [unverified]"]
def weilRepV {m : ℕ} (a : Fin (2 * m) → (Fv)ˣ) : SL(2, Fv) →* Module.End ℂ ((localDataV v).Sn (2 * m)) :=
  (localDataV v).weilRep (isModel_V v) (a := a) (RingHom.id _)

end Place

end QuadFormsKB.WeilRep
