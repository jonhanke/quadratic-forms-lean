/-
# The global zeta integral of a quadratic form and its residue at $s = 0$

**Layer:** global assembly of local factors: the finite places are the local zeta functions (`LocalZeta.lean`), the
Euler product is `GlobalZeta.lean`, and the only global analytic input is the residue of $\zeta_F$ at $1$
(Mathlib's class number formula `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`).

**Setting.** $F$ a number field, $Q$ = `QuadForm (𝓞 F) n` nondegenerate, $n \ge 4$. The archimedean places are the real
places $w$ of $F$ (`Siegel.RealPlace F`), with $Q_w = \sigma_w(Q)$ (`Siegel.realForm`) on $F_w^n = \mathbb R^n$ and
Lebesgue measure $dx_w$ (`volume` on `Fin n → ℝ`), which is the self-dual measure for $x \mapsto e^{2\pi i xy}$. **For
$F$ totally real** these are all the infinite places and $V_\infty = \prod_w\mathbb R^n = V \otimes_{\mathbb Q}\mathbb R$; for a
general $F$ the complex places are simply absent from `archZeta` (not treated).

**The test function** is $\Phi = \Phi_\infty\otimes\bigotimes_v\mathbf 1_{L_v}$, $L_v = \mathcal O_v^n$, with
$\Phi_\infty = \bigotimes_w\Phi_w$, $\Phi_w : \mathbb R^n \to \mathbb R$ arbitrary subject to `IsArchTestFn`: $\Phi_w$ and
$|Q_w|\Phi_w$ are Lebesgue integrable (true for every Schwartz function, in particular the Gaussian
$e^{-\pi\,\mathrm{tr}\,Q}$ that the theta-function argument will use). For the residue, the null cone $\{Q_w = 0\}$ must be
Lebesgue-null at each $w$ (`IsTotallyPosDef` implies it for $n \ge 1$: then $\{Q_w = 0\} = \{0\}$).

**Measures (Weil's normalizations).** On $V(\mathbb A) = \mathbb A_F^n$ the **Tamagawa measure** $dx$ is the self-dual
measure, $\prod_w dx_w \times \prod_v dx_v^{\mathrm{sd}}$ (`selfDualV`, $\operatorname{vol}(\mathcal O_v) = N(\mathfrak d_v)^{-1/2}$); since
$\prod_v N(\mathfrak d_v) = |d_F|$, it equals $|d_F|^{-n/2}\prod_w dx_w\prod_v dx_v^{\mathrm{std}}$ (`prod_selfDual_vol`). The measure in
the zeta integral is Weil's $d'x = |d_F|^{-n/2}\prod_w dx_w\prod_v(1-q_v^{-1})^{-1}dx_v^{\mathrm{std}}$ (§4.4, (1), p. 92: the Tamagawa
measure on $V = \{Q \ne 0\}$ from the gauge form $dx_0\cdots dx_{n-1}$ and the convergence factors $1-q_v^{-1}$).

**Definitions.**
* `archZeta Q Φ s` $= Z_\infty(s) = \prod_w\int_{\mathbb R^n}|Q_w(x)|^s\Phi_w(x)\,dx$.
* `globalZeta Q Φ s` $= Z(s) = |d_F|^{-n/2}\,Z_\infty(s)\prod_v Z_\mathfrak p(s)$, the zeta integral
  $\int_{V(\mathbb A)}|Q(x)|^s\Phi(x)\,d'x$ (Weil §4.5, p. 106, the integral with $\lambda = 1$; §4.4, (1), p. 92) computed
  **multiplicatively**: it is *defined* here as the product of the local integrals. The **additive** side works
  with an adelic integral (an unfolding over $V(F)$) and must identify it with this product (Fubini over the restricted
  product of the $V(F_v)$). This is the chosen split. *Note:* Weil's own $Z(s)$ in §4.5, (2), p. 102 is the sum
  $\sum_\rho Z(s,\rho)$ of spherical zeta functions (no factor $\frac12$); it has the same residue (Weil's (8), p. 108), by the
  comparison (Lemmas 4.5.2–4.5.3) formalized in `SphericalResidue.lean` (`tendsto_mul_sphericalZeta_zero`).
* `phiIntegral Φ` $= \int_{V(\mathbb A)}\Phi\,dx = \prod_w\int\Phi_w\,dx_w\cdot\prod_v\operatorname{vol}_{\mathrm{sd}}(L_v)$ (Tamagawa measure).

**Results.**
* `globalZeta_eq` (**the Euler product**): for $s > 0$,
  $Z(s) = |d_F|^{-n/2}\,Z_\infty(s)\,\zeta_F(1+s)\prod_v Z_v(s)/\lambda_v(s)$.
* `tendsto_mul_dedekindZetaR_one_add`: $s\,\zeta_F(1+s) \to \rho_F$ as $s \to 0^+$, $\rho_F$ = `dedekindZeta_residue F`
  $= 2^{r_1}(2\pi)^{r_2}h_FR_F/(w_F\sqrt{|d_F|})$.
* `continuousWithinAt_archZeta`: $Z_\infty(s) \to Z_\infty(0) = \prod_w\int\Phi_w$ as $s \to 0^+$ (dominated convergence).
* **`tendsto_mul_globalZeta_zero`** (Weil §4.5, p. 106, the residue $\rho_k\int\Phi\,dx$; the value of (8), p. 108): for $n \ge 4$,
  $$\lim_{s\to0^+}s\,Z(s) = \rho_F\cdot|d_F|^{-n/2}\prod_w\int_{\mathbb R^n}\Phi_w\,dx_w = \rho_F\int_{V(\mathbb A)}\Phi\,dx,$$
  the local factors at $s = 0$ being $Z_v(0)/\lambda_v(0) = \operatorname{vol}(L_v)/1 = 1$ (`zetaStd_zero`, `lambdaV_zero`).
* `isArchTestFn_gaussian`, **`tendsto_mul_globalZeta_zero_gaussian`**: for $Q$ totally positive definite and the Gaussian
  $\Phi_w = e^{-aQ_w}$ ($a > 0$; `gaussian`), the condition `IsArchTestFn` is proved (via $Q_w(x) \ge c\sum_ix_i^2$,
  `exists_lower_bound`), so the residue formula holds with no hypothesis beyond nondegeneracy, total positivity, $n \ge 4$.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.GlobalZeta

open IsDedekindDomain NumberField MeasureTheory WithZero Filter Topology
open QuadFormsKB.Analysis

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.GlobalZeta

open Classical

open QuadFormsKB.LocalDensity QuadFormsKB.LocalZeta QuadFormsKB.NFEuler QuadFormsKB.Siegel

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### The residue of $\zeta_F$ -/

/-- **The residue of $\zeta_F$ at $1$, in the variable $s$ of the zeta integral:** $s\,\zeta_F(1+s) \to \rho_F$ as $s \to 0^+$
($s$ real), $\rho_F$ = `dedekindZeta_residue F`. From Mathlib's class number formula
`tendsto_sub_one_mul_dedekindZeta_nhdsGT` ($\zeta_F$ real on $(1,\infty)$: `dedekindZetaR` is its real part). -/
@[kb "weil1982" "§3.1, Theorem 3.1.1 (i), p. 40–41 (ρ_k = [(s-1)ζ_k(s)]_{s=1})"]
theorem tendsto_mul_dedekindZetaR_one_add :
    Tendsto (fun s : ℝ => s * dedekindZetaR F (1 + s)) (𝓝[>] 0) (𝓝 (dedekindZeta_residue F)) := by
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_sub_one_mul_dedekindZeta_nhdsGT F)
  rw [Complex.ofReal_re] at h
  have hshift : Tendsto (fun s : ℝ => 1 + s) (𝓝[>] 0) (𝓝[>] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun s hs => ?_⟩
    · have : Tendsto (fun s : ℝ => 1 + s) (𝓝 0) (𝓝 (1 + 0)) := tendsto_const_nhds.add tendsto_id
      rw [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · simp only [Set.mem_Ioi] at hs ⊢; linarith
  refine (h.comp hshift).congr fun s => ?_
  simp only [Function.comp_apply, dedekindZetaR]
  rw [show ((1 + s : ℝ) : ℂ) - 1 = (s : ℂ) by push_cast; ring, Complex.re_ofReal_mul]

/-! ### The archimedean factor -/

/-- **The value of $Q$ at a real place:** $Q_w(x) = \sigma_w(Q)(x)$ for $x \in \mathbb R^n$. -/
def realVal (Q : QuadForm (𝓞 F) n) (w : RealPlace F) (x : Fin n → ℝ) : ℝ := (realForm Q w).evalIn ℝ x

lemma continuous_realVal (Q : QuadForm (𝓞 F) n) (w : RealPlace F) : Continuous (realVal Q w) := by
  unfold realVal QuadForm.evalIn
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by split_ifs <;> fun_prop

/-- **The local archimedean zeta integral** at a real place $w$:
$Z_w(s) = \int_{\mathbb R^n}|Q_w(x)|^s\,\varphi(x)\,dx$ (Lebesgue measure, `volume`). -/
@[kb "weil1982" "§4.4, p. 93 (the finite part, an integral over ∏_{v∈S} V_{k_v})"]
def archZetaAt (Q : QuadForm (𝓞 F) n) (w : RealPlace F) (φ : (Fin n → ℝ) → ℝ) (s : ℝ) : ℝ :=
  ∫ x, |realVal Q w x| ^ s * φ x

/-- **The archimedean zeta integral** $Z_\infty(s) = \prod_w\int_{\mathbb R^n}|Q_w(x)|^s\,\Phi_w(x)\,dx$, the product over the
real places $w$ of $F$ (all infinite places when $F$ is totally real), for $\Phi_\infty = \bigotimes_w\Phi_w$. -/
def archZeta (Q : QuadForm (𝓞 F) n) (Φ : RealPlace F → (Fin n → ℝ) → ℝ) (s : ℝ) : ℝ :=
  ∏ w, archZetaAt Q w (Φ w) s

/-- **Admissible archimedean test functions** (a condition on the chosen data, not a cited input): at every real place
$w$, $\Phi_w$ and $|Q_w|\,\Phi_w$ are Lebesgue integrable on $\mathbb R^n$. Every Schwartz function satisfies it. -/
structure IsArchTestFn (Q : QuadForm (𝓞 F) n) (Φ : RealPlace F → (Fin n → ℝ) → ℝ) : Prop where
  /-- $\Phi_w \in L^1(\mathbb R^n)$. -/
  integrable : ∀ w, Integrable (Φ w)
  /-- $|Q_w|\,\Phi_w \in L^1(\mathbb R^n)$. -/
  integrable_mul : ∀ w, Integrable fun x => |realVal Q w x| * Φ w x

/-- **$Q$ is totally positive definite:** $Q_w(x) > 0$ for every real place $w$ and every $x \ne 0$ in $\mathbb R^n$. -/
def IsTotallyPosDef (Q : QuadForm (𝓞 F) n) : Prop := ∀ (w : RealPlace F) (x : Fin n → ℝ), x ≠ 0 → 0 < realVal Q w x

/-- For a totally positive definite $Q$ in $n \ge 1$ variables, the null cone $\{Q_w = 0\} = \{0\}$ is Lebesgue-null. -/
theorem ae_realVal_ne_zero {Q : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef Q) (hn : 1 ≤ n) (w : RealPlace F) :
    ∀ᵐ x : Fin n → ℝ, realVal Q w x ≠ 0 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h0 : ∀ᵐ x : Fin n → ℝ, x ≠ 0 := by
    rw [ae_iff]; simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton, measure_singleton]
  filter_upwards [h0] with x hx using (hQ w x hx).ne'

lemma rpow_le_one_add {t s : ℝ} (ht : 0 ≤ t) (hs : s ∈ Set.Icc (0 : ℝ) 1) : t ^ s ≤ 1 + t := by
  rcases le_total t 1 with h | h
  · linarith [Real.rpow_le_one ht h hs.1]
  · have := Real.rpow_le_rpow_of_exponent_le h hs.2
    rw [Real.rpow_one] at this; linarith

/-- **Continuity of the archimedean local zeta integral at $s = 0^+$** (dominated convergence, majorant
$(1 + |Q_w|)|\varphi|$ on $s \in [0,1]$): $Z_w(s) \to Z_w(0) = \int\varphi$. -/
theorem continuousWithinAt_archZetaAt (Q : QuadForm (𝓞 F) n) (w : RealPlace F) {φ : (Fin n → ℝ) → ℝ}
    (hφ : Integrable φ) (hφQ : Integrable fun x => |realVal Q w x| * φ x)
    (hnull : ∀ᵐ x : Fin n → ℝ, realVal Q w x ≠ 0) :
    ContinuousWithinAt (archZetaAt Q w φ) (Set.Icc 0 1) 0 := by
  have hc := continuous_realVal Q w
  refine continuousWithinAt_of_dominated (bound := fun x => |φ x| + |realVal Q w x| * |φ x|) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun s =>
      ((continuous_abs.comp hc).measurable.pow_const s).aestronglyMeasurable.mul hφ.aestronglyMeasurable
  · refine eventually_nhdsWithin_of_forall fun s hs => Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    have := rpow_le_one_add (abs_nonneg (realVal Q w x)) hs
    nlinarith [abs_nonneg (φ x)]
  · exact hφ.abs.add (by simpa [abs_mul] using hφQ.abs)
  · filter_upwards [hnull] with x hx
    exact ((Real.continuousAt_const_rpow (abs_ne_zero.mpr hx)).mul continuousAt_const).continuousWithinAt

theorem archZetaAt_zero (Q : QuadForm (𝓞 F) n) (w : RealPlace F) (φ : (Fin n → ℝ) → ℝ) :
    archZetaAt Q w φ 0 = ∫ x, φ x := by
  simp [archZetaAt]

/-- **$Z_\infty(s) \to \prod_w\int_{\mathbb R^n}\Phi_w$ as $s \to 0^+$.** -/
theorem tendsto_archZeta_zero (Q : QuadForm (𝓞 F) n) {Φ : RealPlace F → (Fin n → ℝ) → ℝ}
    (hΦ : IsArchTestFn Q Φ) (hnull : ∀ w, ∀ᵐ x : Fin n → ℝ, realVal Q w x ≠ 0) :
    Tendsto (archZeta Q Φ) (𝓝[>] 0) (𝓝 (∏ w, ∫ x, Φ w x)) := by
  unfold archZeta
  refine tendsto_finsetProd _ fun w _ => ?_
  have h : Tendsto (archZetaAt Q w (Φ w)) (𝓝[Set.Icc 0 1] 0) (𝓝 (archZetaAt Q w (Φ w) 0)) :=
    continuousWithinAt_archZetaAt Q w (hΦ.integrable w) (hΦ.integrable_mul w) (hnull w)
  rw [archZetaAt_zero] at h
  exact h.mono_left (nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem ⟨le_rfl, zero_lt_one⟩))

/-! ### The self-dual normalization: $\prod_v\operatorname{vol}_{\mathrm{sd}}(L_v) = |d_F|^{-n/2}$ -/

/-- **$\prod_v N(\mathfrak d_v) = |d_F|$ over $\mathbb R$**, as a finite product over the places with $d_v \ne 0$. -/
lemma prod_absNorm_pow_diffExp :
    ∏ v ∈ (finite_support_diffExp (F := F)).toFinset, ((Ideal.absNorm v.asIdeal : ℝ) ^ diffExp v) =
      |(NumberField.discr F : ℝ)| := by
  have h := finprod_absNorm_pow_diffExp (F := F)
  rw [finprod_eq_prod_of_mulSupport_subset (s := (finite_support_diffExp (F := F)).toFinset)] at h
  · have h' := congrArg (fun x : ℚ => (x : ℝ)) h
    simp only [Rat.cast_prod, Rat.cast_abs, Rat.cast_intCast, zpow_natCast, Rat.cast_pow,
      Rat.cast_natCast] at h'
    exact h'
  · intro v hv
    simp only [Set.Finite.coe_toFinset, Function.mem_support, ne_eq, Nat.cast_eq_zero]
    intro h0
    apply hv
    simp [h0]

/-- **The self-dual volume of $L_v$**: $\operatorname{vol}_{\mathrm{sd}}(\mathcal O_v^n) = N(\mathfrak d_v)^{-n/2}$. -/
lemma selfDual_vol_latL (v : HeightOneSpectrum (𝓞 F)) :
    (Measure.pi fun _ : Fin n => selfDualV v).real (latL v n) =
      ((Ideal.absNorm v.asIdeal : ℝ) ^ diffExp v) ^ (-(n : ℝ) / 2) := by
  have hN : (0 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ diffExp v := by positivity
  rw [Measure.real, measure_latL, ENNReal.toReal_pow, ← Measure.real, selfDualV_real_Ov,
    ← Real.rpow_natCast, ← Real.rpow_mul hN]
  congr 1; ring

/-- **$\prod_v\operatorname{vol}_{\mathrm{sd}}(L_v) = |d_F|^{-n/2}$** (Tate's thesis normalization; the self-dual measure on $\mathbb A_F$
gives $\mathbb A_F/F$ volume $1$): the factors are $1$ outside the primes dividing the different, and
$\prod_v N(\mathfrak d_v) = |d_F|$ (`finprod_absNorm_pow_diffExp`). -/
@[kb "weil1982" "§2.1.3, pp. 12–13 (μ_k = |Δ_k|^{1/2}) and §2.3, p. 21 (Tamagawa measure μ_k^{-dim V}∏ω_v)"]
theorem prod_selfDual_vol :
    ∏' v : HeightOneSpectrum (𝓞 F), (Measure.pi fun _ : Fin n => selfDualV v).real (latL v n) =
      |(NumberField.discr F : ℝ)| ^ (-(n : ℝ) / 2) := by
  set S := (finite_support_diffExp (F := F)).toFinset
  rw [tprod_eq_prod (s := S)]
  · rw [Finset.prod_congr rfl fun v _ => selfDual_vol_latL (n := n) v,
      Real.finsetProd_rpow _ _ (fun _ _ => by positivity), prod_absNorm_pow_diffExp]
  · intro v hv
    have h0 : diffExp v = 0 := by
      by_contra h; apply hv; simp [S, h]
    rw [selfDual_vol_latL, h0, pow_zero, Real.one_rpow]

/-! ### The global zeta integral and its residue -/

/-- **The global zeta integral of $Q$, computed multiplicatively** (Weil 1982, §4.5, p. 106; §4.4, (1),
p. 92): for $\Phi = \Phi_\infty\otimes\bigotimes_v\mathbf 1_{L_v}$ and real $s > 0$,
$$Z(s) = \int_{V(\mathbb A)}|Q(x)|^s\,\Phi(x)\,d'x = |d_F|^{-n/2}\,Z_\infty(s)\prod_v Z_\mathfrak p(s),$$
$d'x$ Weil's Tamagawa measure on $\{Q \ne 0\}$ with the convergence factors $1 - q_v^{-1}$ (`zetaWeil`), $|Q(x)|$ the idelic
absolute value $\prod_w|Q_w(x_w)|\prod_v|Q(x_v)|_v$. Defined here as the product of the local integrals (`tprod`; it
converges for $n \ge 4$, `hasProd_zetaWeil`). -/
@[kb "weil1982" "§4.5, p. 106 (∫_{V_A}|F(x)|^sλ(F(x))Φ(x)d'x with λ = 1); §4.4, (1), p. 92"]
def globalZeta (Q : QuadForm (𝓞 F) n) (Φ : RealPlace F → (Fin n → ℝ) → ℝ) (s : ℝ) : ℝ :=
  |(NumberField.discr F : ℝ)| ^ (-(n : ℝ) / 2) * archZeta Q Φ s * ∏' v, zetaWeil Q v s

/-- **$\int_{V(\mathbb A)}\Phi\,dx$** for $\Phi = \bigotimes_w\Phi_w\otimes\bigotimes_v\mathbf 1_{L_v}$, $dx$ the Tamagawa (self-dual)
measure on $V(\mathbb A) = \mathbb A_F^n$: $\prod_w\int_{\mathbb R^n}\Phi_w\,dx_w\cdot\prod_v\operatorname{vol}_{\mathrm{sd}}(L_v)$. -/
def phiIntegral (Φ : RealPlace F → (Fin n → ℝ) → ℝ) : ℝ :=
  (∏ w, ∫ x, Φ w x) * ∏' v : HeightOneSpectrum (𝓞 F), (Measure.pi fun _ : Fin n => selfDualV v).real (latL v n)

theorem phiIntegral_eq (Φ : RealPlace F → (Fin n → ℝ) → ℝ) :
    phiIntegral Φ = |(NumberField.discr F : ℝ)| ^ (-(n : ℝ) / 2) * ∏ w, ∫ x, Φ w x := by
  rw [phiIntegral, prod_selfDual_vol, mul_comm]

/-- **The Euler-product form of $Z(s)$** (Weil 1982, §4.5, p. 108): for real $s > 0$ and $n \ge 4$,
$$Z(s) = |d_F|^{-n/2}\cdot Z_\infty(s)\cdot\zeta_F(1+s)\cdot\prod_v\frac{Z_v(s)}{\lambda_v(s)},$$
with $\prod_v Z_v/\lambda_v$ absolutely convergent for $s \ge 0$ and continuous on $[0,1]$ (`continuousOn_zetaRatioProd`). -/
@[kb "weil1982" "§4.5, pp. 107–108 (the multiplicative calculation)"]
theorem globalZeta_eq (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 4 ≤ n)
    (Φ : RealPlace F → (Fin n → ℝ) → ℝ) {s : ℝ} (hs : 0 < s) :
    globalZeta Q Φ s = |(NumberField.discr F : ℝ)| ^ (-(n : ℝ) / 2) * archZeta Q Φ s *
      dedekindZetaR F (1 + s) * zetaRatioProd Q s := by
  rw [globalZeta, (hasProd_zetaWeil Q hQ hn hs).tprod_eq, zetaRatioProd]; ring

/-- **The self-dual form of $Z(s)$:** $Z(s) = Z_\infty(s)\prod_v\int_{L_v}|Q|_v^s\,(1-q_v^{-1})^{-1}dx_v^{\mathrm{sd}}$, the product of the
local integrals for the self-dual measures (`selfDualV`) with Weil's convergence factors; the factor $|d_F|^{-n/2}$ is
absorbed by $\prod_v N(\mathfrak d_v)^{-n/2} = |d_F|^{-n/2}$. -/
theorem globalZeta_eq_selfDual (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 4 ≤ n)
    (Φ : RealPlace F → (Fin n → ℝ) → ℝ) {s : ℝ} (hs : 0 < s) :
    globalZeta Q Φ s = archZeta Q Φ s *
      ∏' v, zetaInt v (selfDualV v) (NF.Qp v Q) s / (1 - ((DVR.q (v.adicCompletionIntegers F) : ℕ) : ℝ)⁻¹) := by
  set S := (finite_support_diffExp (F := F)).toFinset
  have hfin : ∀ v ∉ S, (Measure.pi fun _ : Fin n => selfDualV v).real (latL v n) = 1 := fun v hv => by
    have h0 : diffExp v = 0 := by by_contra h; apply hv; simp [S, h]
    rw [selfDual_vol_latL, h0, pow_zero, Real.one_rpow]
  have hc : HasProd (fun v : HeightOneSpectrum (𝓞 F) =>
      (Measure.pi fun _ : Fin n => selfDualV v).real (latL v n)) (|(NumberField.discr F : ℝ)| ^ (-(n : ℝ) / 2)) := by
    have h1 : HasProd (fun v : HeightOneSpectrum (𝓞 F) =>
        (Measure.pi fun _ : Fin n => selfDualV v).real (latL v n))
        (∏ v ∈ S, (Measure.pi fun _ : Fin n => selfDualV v).real (latL v n)) :=
      hasProd_prod_of_ne_finset_one hfin
    have h2 : ∏' v : HeightOneSpectrum (𝓞 F), (Measure.pi fun _ : Fin n => selfDualV v).real (latL v n) =
        ∏ v ∈ S, (Measure.pi fun _ : Fin n => selfDualV v).real (latL v n) := tprod_eq_prod hfin
    rwa [← h2, prod_selfDual_vol] at h1
  have h := (hc.mul (hasProd_zetaWeil Q hQ hn hs).multipliable.hasProd).tprod_eq
  rw [globalZeta, mul_comm _ (archZeta Q Φ s), mul_assoc, ← h]
  congr 1
  refine tprod_congr fun v => ?_
  rw [zetaWeil, zetaStd, zetaInt_selfDual v _ (NF.nondegenerate_Qp v hQ) (by omega) hs.le, Measure.real,
    measure_latL, ENNReal.toReal_pow, ← Measure.real, selfDualV_real_Ov, mul_div_assoc]

/-- **The residue of the zeta integral at $s = 0$** (Weil 1982, §4.5, p. 106: "only the one corresponding to $\lambda = 1$
gives a residue for $s = 0$, this residue being $\rho_k\int\Phi(x)dx$"; the same value as Weil's (8), p. 108). For $Q$
nondegenerate in $n \ge 4$ variables and $\Phi_\infty$ admissible (`IsArchTestFn`) with Lebesgue-null null cones,
$$\lim_{s\to0^+}s\,Z(s) = \rho_F\cdot|d_F|^{-n/2}\prod_w\int_{\mathbb R^n}\Phi_w(x)\,dx = \rho_F\int_{V(\mathbb A)}\Phi(x)\,dx,$$
$\rho_F$ = `dedekindZeta_residue F` the residue of $\zeta_F$ at $1$ and $dx$ the Tamagawa (self-dual) measure
(`phiIntegral`). The finite places contribute $\prod_v Z_v(0)/\lambda_v(0) = \prod_v\operatorname{vol}_{\mathrm{std}}(L_v) = 1$.

*Which zeta function.* $Z(s)$ here is $\int_{V(\mathbb A)}|Q(x)|^s\Phi(x)\,d'x$ (Weil's integral on p. 106 with $\lambda = 1$, the
analogue of $I_0$ in §4.4, p. 94). Weil's $Z(s)$ of §4.5, (2), p. 102, is instead $\sum_\rho Z(s,\rho)$ over the spherical
zeta functions of the varieties $Q(x) = \rho y^2$; (8) states $\lim s\,Z(s) = \rho_k\int\Phi\,dx$ for that function, which Weil
deduces from the present limit with Lemmas 4.5.2–4.5.3 (bounds $\mu(S) < 2^{-|S|}Z(s)Z_S(s)^{-1} < \mu'(S)$). That
comparison is formalized in `SphericalResidue.lean` (`tendsto_mul_sphericalZeta_zero`).

*Proof.* $s\,Z(s) = |d_F|^{-n/2}\,Z_\infty(s)\,(s\,\zeta_F(1+s))\,R(s)$ for $s > 0$ (`globalZeta_eq`), with
$Z_\infty(s) \to \prod_w\int\Phi_w$ (`tendsto_archZeta_zero`), $s\,\zeta_F(1+s) \to \rho_F$ (`tendsto_mul_dedekindZetaR_one_add`) and
$R(s) \to 1$ (`tendsto_zetaRatioProd_zero`, the M-test); $n \ge 4$ suffices for the Euler product. -/
@[kb "weil1982" "§4.5, p. 106 (residue ρ_k∫Φ(x)dx at s = 0 for λ = 1); cf. (8), p. 108"]
theorem tendsto_mul_globalZeta_zero (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 4 ≤ n)
    {Φ : RealPlace F → (Fin n → ℝ) → ℝ} (hΦ : IsArchTestFn Q Φ)
    (hnull : ∀ w, ∀ᵐ x : Fin n → ℝ, realVal Q w x ≠ 0) :
    Tendsto (fun s => s * globalZeta Q Φ s) (𝓝[>] 0) (𝓝 (dedekindZeta_residue F * phiIntegral Φ)) := by
  have h := ((tendsto_const_nhds (x := |(NumberField.discr F : ℝ)| ^ (-(n : ℝ) / 2)).mul
    (tendsto_archZeta_zero Q hΦ hnull)).mul (tendsto_mul_dedekindZetaR_one_add (F := F))).mul
    (tendsto_zetaRatioProd_zero Q hQ hn)
  rw [phiIntegral_eq, show ∀ a b c : ℝ, a * (b * c) = b * c * a * 1 by intros; ring]
  refine h.congr' (eventually_nhdsWithin_of_forall fun s hs => ?_)
  show _ = s * globalZeta Q Φ s
  rw [globalZeta_eq Q hQ hn Φ hs]; ring

/-- **The residue at $s = 0$ for a totally positive definite form** ($n \ge 4$): the null cones are $\{0\}$. -/
@[kb "weil1982" "§4.5, p. 106 (residue at s = 0, totally definite case); cf. (8), p. 108"]
theorem tendsto_mul_globalZeta_zero_of_posDef (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate)
    (hpos : IsTotallyPosDef Q) (hn : 4 ≤ n) {Φ : RealPlace F → (Fin n → ℝ) → ℝ} (hΦ : IsArchTestFn Q Φ) :
    Tendsto (fun s => s * globalZeta Q Φ s) (𝓝[>] 0) (𝓝 (dedekindZeta_residue F * phiIntegral Φ)) :=
  tendsto_mul_globalZeta_zero Q hQ hn hΦ fun w => ae_realVal_ne_zero hpos (by omega) w

/-! ### The Gaussian test function -/

/-- $Q_w(tx) = t^2Q_w(x)$. -/
lemma realVal_smul (Q : QuadForm (𝓞 F) n) (w : RealPlace F) (t : ℝ) (x : Fin n → ℝ) :
    realVal Q w (t • x) = t ^ 2 * realVal Q w x := by
  unfold realVal QuadForm.evalIn
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp only [Pi.smul_apply, smul_eq_mul, mul_zero]; ring

/-- **Positive definiteness is uniform:** for $Q$ totally positive definite there is $c > 0$ with
$Q_w(x) \ge c\sum_i x_i^2$ on $\mathbb R^n$ (minimum of $Q_w$ on the compact unit sphere). -/
theorem exists_lower_bound {Q : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef Q) (w : RealPlace F) :
    ∃ c > 0, ∀ x : Fin n → ℝ, c * ∑ i, x i ^ 2 ≤ realVal Q w x := by
  set S : Set (Fin n → ℝ) := {x | ∑ i, x i ^ 2 = 1}
  have hScpt : IsCompact S := by
    refine (isCompact_closedBall (0 : Fin n → ℝ) 1).of_isClosed_subset
      (isClosed_eq (continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2) continuous_const) ?_
    intro x hx
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have hi : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
      Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [show ∑ j, x j ^ 2 = 1 from hx] at hi
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (x i), sq_abs (x i)]
  rcases S.eq_empty_or_nonempty with hS | hS
  · -- $n = 0$: every $x$ has $\sum x_i^2 = 0$
    refine ⟨1, one_pos, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp [realVal, QuadForm.evalIn]
    · have hsum : 0 < ∑ i, x i ^ 2 := by
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
        exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi))) (Finset.single_le_sum (f := fun j => x j ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ i))
      exfalso
      have : (Real.sqrt (∑ i, x i ^ 2))⁻¹ • x ∈ S := by
        simp only [S, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, inv_pow,
          Real.sq_sqrt hsum.le]
        exact inv_mul_cancel₀ hsum.ne'
      rw [hS] at this; exact this
  obtain ⟨x₀, hx₀, hmin⟩ := hScpt.exists_isMinOn hS (continuous_realVal Q w).continuousOn
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl; simp [S] at hx₀
  refine ⟨realVal Q w x₀, hQ w x₀ hx₀0, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx; simp [realVal, QuadForm.evalIn]
  have hsum : 0 < ∑ i, x i ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi))) (Finset.single_le_sum (f := fun j => x j ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  set r := Real.sqrt (∑ i, x i ^ 2)
  have hr : 0 < r := Real.sqrt_pos.mpr hsum
  have hy : r⁻¹ • x ∈ S := by
    simp only [S, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, inv_pow, r,
      Real.sq_sqrt hsum.le]
    exact inv_mul_cancel₀ hsum.ne'
  have h1 := hmin hy
  simp only [Set.mem_ofPred_eq] at h1
  have hxe : x = r • (r⁻¹ • x) := by rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hsr : ∑ i, x i ^ 2 = r ^ 2 := (Real.sq_sqrt hsum.le).symm
  rw [hsr]
  conv_rhs => rw [hxe, realVal_smul]
  nlinarith [sq_nonneg r]

/-- **The Gaussian** $\Phi_w(x) = e^{-a\,Q_w(x)}$ ($a > 0$) at every real place. -/
def gaussian (Q : QuadForm (𝓞 F) n) (a : ℝ) : RealPlace F → (Fin n → ℝ) → ℝ :=
  fun w x => Real.exp (-a * realVal Q w x)

lemma integrable_exp_neg_mul_realVal {Q : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef Q) (w : RealPlace F)
    {b : ℝ} (hb : 0 < b) : Integrable fun x : Fin n → ℝ => Real.exp (-b * realVal Q w x) := by
  obtain ⟨c, hc, hle⟩ := exists_lower_bound hQ w
  have hg : Integrable (fun x : Fin n → ℝ => ∏ i, Real.exp (-(b * c) * x i ^ 2))
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) :=
    Integrable.fintype_prod fun _ => integrable_exp_neg_mul_sq (mul_pos hb hc)
  rw [← volume_pi] at hg
  refine hg.mono' ((Real.continuous_exp.comp (continuous_const.mul
    (continuous_realVal Q w))).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_sum, Real.exp_le_exp]
  have := hle x
  have hs : ∑ i, -(b * c) * x i ^ 2 = -b * (c * ∑ i, x i ^ 2) := by rw [Finset.mul_sum, Finset.mul_sum]; ring_nf
  rw [hs]; nlinarith

/-- **The Gaussian is an admissible archimedean test function** for a totally positive definite $Q$:
$e^{-aQ_w}$ and $|Q_w|e^{-aQ_w} \le \frac2a e^{-aQ_w/2}$ are integrable (`exists_lower_bound`: $Q_w \ge c|x|^2$). -/
theorem isArchTestFn_gaussian {Q : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef Q) {a : ℝ} (ha : 0 < a) :
    IsArchTestFn Q (gaussian Q a) where
  integrable w := integrable_exp_neg_mul_realVal hQ w ha
  integrable_mul w := by
    have hi := (integrable_exp_neg_mul_realVal hQ w (half_pos ha)).const_mul (2 / a)
    refine hi.mono' ((continuous_abs.comp (continuous_realVal Q w)).mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_realVal Q w)))).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    have hq : 0 ≤ realVal Q w x := by
      by_cases hx : x = 0
      · subst hx; simp [realVal, QuadForm.evalIn]
      · exact (hQ w x hx).le
    simp only [gaussian]
    rw [Real.norm_eq_abs, abs_of_nonneg hq, abs_of_nonneg (mul_nonneg hq (Real.exp_pos _).le)]
    -- $t \le \frac2a e^{at/2}$
    have h1 : realVal Q w x ≤ 2 / a * Real.exp (a / 2 * realVal Q w x) := by
      have := Real.add_one_le_exp (a / 2 * realVal Q w x)
      rw [div_mul_eq_mul_div, le_div_iff₀ ha]; nlinarith [Real.exp_pos (a / 2 * realVal Q w x)]
    calc realVal Q w x * Real.exp (-a * realVal Q w x)
        ≤ 2 / a * Real.exp (a / 2 * realVal Q w x) * Real.exp (-a * realVal Q w x) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = 2 / a * Real.exp (-(a / 2) * realVal Q w x) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- **The residue at $s = 0$ for the Gaussian** (unconditional for totally positive definite $Q$, $n \ge 4$, $a > 0$):
$\lim_{s\to0^+}s\,Z(s) = \rho_F\,|d_F|^{-n/2}\prod_w\int_{\mathbb R^n}e^{-aQ_w(x)}dx$. -/
@[kb "weil1982" "§4.5, p. 106 (residue at s = 0, Gaussian Φ_∞); cf. (8), p. 108"]
theorem tendsto_mul_globalZeta_zero_gaussian (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate)
    (hpos : IsTotallyPosDef Q) (hn : 4 ≤ n) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun s => s * globalZeta Q (gaussian Q a) s) (𝓝[>] 0)
      (𝓝 (dedekindZeta_residue F * phiIntegral (gaussian Q a))) :=
  tendsto_mul_globalZeta_zero_of_posDef Q hQ hpos hn (isArchTestFn_gaussian hpos ha)

end QuadFormsKB.GlobalZeta
