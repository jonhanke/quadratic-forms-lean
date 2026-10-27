import QuadFormsKB.Tamagawa.Measure.Weil.ConeUnfoldAdelic
import QuadFormsKB.Tamagawa.Measure.ConeAdelic
import QuadFormsKB.Tamagawa.Measure.ConeReduction
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarTernary
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSiegelTotallyReal

/-!
# $\tau(SO(V)) = 2$ for isotropic $V$, and for every $V$ of dimension $\ge5$

$F$ a number field. This file finishes Weil's induction (Weil 1982, §4.5, pp. 108–109, the cone case)
on top of the sphere unfolding and the anisotropic case, the cone development (local and adelic cone measures,
the reduction of an isotropic form to the cone form) and `ConeUnfoldAdelic.lean` (the cone unfolding).

* **The comparison with bounded cone terms** (`tamagawaNumberTwoAdelic_of_coneBound`): for a nondegenerate $Q_0$ in
  $m = k+1\ge5$ variables, any signature, with the data `AdelicWeilCore` (sphere fibration, twisted Poisson formula,
  Euler-product identifications), the induction hypothesis in dimension $m-1$ and the bound $C_1(s), C_2(s)\le K<\infty$
  for $0 < s\le1$: $\tau(SO(V)) = 2$. Step 4 (finiteness of the volume by positivity, now with $C_1$), the residue of
  $Z^+$ (with $sC_1(s), sC_2(s)\to0$), Step 1 and the multiplicative residue.
* **The cone form** $Q_0 = \langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'$ (`coneFormO`; $\dim V = k+2$):
  `tamagawaNumberTwoAdelic_cone`: given `AdelicConeInputs` (the adelic cone fibration with $V' = Q_0'$, and the
  identification of $I_C(\Phi), I_C(\hat\Phi)$ with `coneIntegral`, `AdelicConeEuler`), the induction hypothesis
  in dimension $k+1$ and $\operatorname{covol}(SO(Q_0')) < \infty$ (dimension $k$), $\tau(SO(V)) = 2$; the cone bound is
  `coneC1_le`/`coneC2_le` with `coneIntegral_lt_top` ($k\ge3$).
* **Every isotropic $V$** (`tamagawaNumberTwoAdelic_of_isotropic`, $\dim V\ge5$): `covolume_muTam_eq_cone` moves
  $\tau$ to a cone form.
* **The combined induction** (`tauTwoAll_of_inputs`): from $\tau = 2$ in dimension $3$ (proved: `covolume_muTam_ternary`,
  the ternary case), the base case for all quaternary forms (`QuaternaryTauTwoBase`, input) and the per-dimension inputs
  (`AdelicStepInputs` for anisotropic forms, `AdelicConeStepInputs` for cone forms), $\tau(SO(V)) = 2$ for **every**
  nondegenerate $V$ of dimension $\ge3$ over $F$. Over a totally real field the base case is only needed for
  quaternary forms that are not totally positive definite (`quaternaryTauTwoBase_of_notPosDef`, from
  `quaternaryTamagawaTwo_nf'`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure QuadFormsKB.SphericalZeta
  QuadFormsKB.SphericalNF QuadFormsKB.GlobalZeta QuadFormsKB.Siegel QuadFormsKB.Tamagawa.Measure.ConeAdelic
  QuadFormsKB.Tamagawa.Measure.ConeAlgebra QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure.ConeReduction

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

/-! ### The comparison with bounded cone terms -/

/-- **$\tau(SO(V)) = 2$ from dimension $m-1$, given bounded cone terms** (Weil 1982, §4.5, pp. 108–109,
Steps 1, 2, 4): for a nondegenerate $Q_0$ in $m = k+1\ge5$ variables over a number field $F$ (any signature, isotropic
or not), with the data `W : AdelicWeilCore Q₀ hQ`, the induction hypothesis `AdelicComplementTauTwo W.S` and a constant
$K < \infty$ with $C_1(s)\le K$ and $C_2(s)\le K$ for $0 < s\le 1$ (for every pair of fundamental domains),
$\tau(SO(V)) = 2$. For anisotropic $Q$ the cone terms vanish ($K = 0$). -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(G) = 2 by comparing the residues, cone terms included)"]
theorem tamagawaNumberTwoAdelic_of_coneBound (hk : 4 ≤ k) {Q₀ : QuadForm (𝓞 F) (k + 1)} {hQ : Q₀.Nondegenerate}
    (W : AdelicWeilCore Q₀ hQ) (hτ : AdelicComplementTauTwo W.S) {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hC1 : ∀ (D : Set (SOAdele Q₀)) (DM : Set (Adeles F)ˣ), IsFundamentalDomain (GammaSOAdele Q₀) D (muTam Q₀ hQ 1) →
      IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F) → ∀ s, 0 < s → s ≤ 1 → coneC1 Q₀ hQ W.Φ D DM s ≤ K)
    (hC2 : ∀ (D : Set (SOAdele Q₀)) (DM : Set (Adeles F)ˣ), IsFundamentalDomain (GammaSOAdele Q₀) D (muTam Q₀ hQ 1) →
      IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F) → ∀ s, 0 < s → s ≤ 1 → coneC2 Q₀ hQ W.Φh D DM s ≤ K) :
    TamagawaNumberTwoAdelic Q₀ hQ := by
  have hρ := dedekindZeta_residue_pos F
  obtain ⟨D, hD⟩ := (hasFundamentalDomain_GammaSOAdele Q₀ (muTam Q₀ hQ 1)).ExistsIsFundamentalDomain
  obtain ⟨DM, hDM⟩ := exists_isFundamentalDomain_ideles (tamIdeles F)
  have hk1 : 1 ≤ k := by omega
  have hmeas : ∀ s, Measurable (adelicInner Q₀ W.Φ DM s) := fun s =>
    W.fib.measurable_adelicInner hk1 W.measurable_Φ hDM s
  -- the multiplicative side
  have hZ : ∀ s, 0 < s → adelicZetaPlus Q₀ hQ W.Φ D DM s = ENNReal.ofReal (W.κ * sphericalZetaNF Q₀ W.Φr W.Ψ s) :=
    fun s hs => by
      rw [adelicZetaPlus_eq_tsum_of_complementTauTwo hk1 W.S W.fib hτ W.measurable_Φ hD hDM s]
      exact tsum_adelicSphZeta_eq hk W.euler W.κ_nonneg hQ W.Φr_nonneg W.Ψ_nonneg W.vanish hs
  have hZh : adelicZetaPlus Q₀ hQ W.Φh D DM 1 ≠ ⊤ :=
    (adelicZetaPlus_lt_top hk W.S W.fib hτ W.measurable_Φh W.eulerHat W.κh_nonneg W.Φhr_nonneg W.Ψh_nonneg hD hDM
      one_pos).ne
  -- Step 4: finite volume
  set t : ℝ := (k + 1) * W.b / (4 * (W.a + 1)) with ht
  set s₀ : ℝ := min 1 t with hs₀
  have ha1 : 0 < W.a + 1 := by linarith [W.a_nonneg]
  have htpos : 0 < t := by have := W.b_pos; positivity
  have hs₀pos : 0 < s₀ := lt_min one_pos htpos
  have hs₀1 : s₀ ≤ 1 := min_le_left _ _
  have hsb : 2 * s₀ * W.a < ((k + 1 : ℕ) : ℝ) * W.b := by
    have hb := W.b_pos
    have h1 : 2 * t * W.a < ((k + 1 : ℕ) : ℝ) * W.b := by
      rw [ht]; push_cast
      have hkb : 0 < ((k : ℝ) + 1) * W.b := by positivity
      rw [show 2 * ((↑k + 1) * W.b / (4 * (W.a + 1))) * W.a = ((↑k + 1) * W.b) * (W.a / (2 * (W.a + 1))) by
        field_simp; ring]
      have : W.a / (2 * (W.a + 1)) < 1 := by
        rw [div_lt_one (by positivity)]; linarith [W.a_nonneg]
      nlinarith
    have h2 : 2 * s₀ * W.a ≤ 2 * t * W.a :=
      mul_le_mul_of_nonneg_right (by linarith [min_le_right 1 t]) W.a_nonneg
    linarith
  have hDfin : muTam Q₀ hQ 1 D < ⊤ :=
    measure_fundamentalDomain_lt_top_cone W.measurable_Φ W.measurable_Φh W.poisson hDM W.a_nonneg W.b_pos
      W.Φ_zero W.Φh_zero hs₀pos hsb (hmeas s₀) (by rw [hZ s₀ hs₀pos]; exact ENNReal.ofReal_ne_top)
      (ne_top_of_le_ne_top hK (hC1 D DM hD hDM s₀ hs₀pos hs₀1))
  -- the additive residue
  have hC : adelicZetaPlus Q₀ hQ W.Φh D DM 1 + adelicZetaPlus Q₀ hQ W.Φ D DM 1 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hZh, by rw [hZ 1 one_pos]; exact ENNReal.ofReal_ne_top⟩
  have hadd := tendsto_mul_adelicZetaPlus_cone (by omega) W.measurable_Φ W.measurable_Φh W.poisson hDM
    W.a_nonneg W.b_pos W.Φ_zero W.Φh_zero hDfin.ne hC
    (W.fib.measurable_adelicInner hk1 W.measurable_Φh hDM 1) hmeas hK (hC1 D DM hD hDM) (hC2 D DM hD hDM)
  -- the multiplicative residue
  have hmul : Tendsto (fun s => s * (adelicZetaPlus Q₀ hQ W.Φ D DM s).toReal) (𝓝[>] 0)
      (𝓝 (dedekindZeta_residue F * W.b)) := by
    have h := (tendsto_mul_sphericalZetaNF_zero_of_nonneg Q₀ hQ (by omega) W.archTest W.Φr_nonneg
      W.archTestC).const_mul W.κ
    rw [W.b_eq]
    refine (h.congr' ?_).trans (by rw [show W.κ * (dedekindZeta_residue F * phiIntegralNF W.Φr W.Ψ) =
      dedekindZeta_residue F * (W.κ * phiIntegralNF W.Φr W.Ψ) by ring])
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hnn : 0 ≤ W.κ * sphericalZetaNF Q₀ W.Φr W.Ψ s := mul_nonneg W.κ_nonneg (by
      unfold sphericalZetaNF; exact tsum_nonneg fun c => sphericalZetaAtNF_nonneg' Q₀ W.Φr_nonneg W.Ψ_nonneg _ s)
    rw [hZ s hs, ENNReal.toReal_ofReal hnn]
    ring
  have heq := tendsto_nhds_unique hadd hmul
  have hV : (muTam Q₀ hQ 1 D).toReal = 2 := by
    have hbpos := W.b_pos
    have : (muTam Q₀ hQ 1 D).toReal * (dedekindZeta_residue F * W.b) = 2 * (dedekindZeta_residue F * W.b) := by
      linarith
    exact mul_right_cancel₀ (by positivity) this
  show covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ 1) = 2
  rw [covolume_muTam_eq Q₀ hQ _ hD]
  show muTam Q₀ hQ 1 D = 2
  rw [← ENNReal.ofReal_toReal hDfin.ne, hV]
  simp

/-! ### The cone form -/

/-- **The cone form** $\langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'$ over $\mathcal O_F$ in $k+2$ variables
($x_0, x_1$ the hyperbolic plane, $x_2, \dots, x_{k+1}$ the variables of $Q_0'$), the target of the reduction
`covolume_muTam_eq_cone`. -/
abbrev coneFormO (c₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) k) : QuadForm (𝓞 F) (k + 1 + 1) :=
  splitForm c₀ (splitForm (-c₀) Q₀')

/-- **The cone integral is the product of local cone integrals** (**input**; Weil 1982, §4.5, p. 108
[unverified page]): for the cone form `coneFormO c₀ Q₀'`, the measure
$\sigma$ on the adelic punctured cone and the test function $\Phi$, there are archimedean factors $\Phi_w$ bounded by
Gaussians $C_we^{-a_w\|z\|^2}$ and a bounded family of compact sets $K_v$ ($v\in S$, $K_v = L_v$ otherwise) with
$$\int_C\Phi\,d\sigma = I_C = \prod_{w\mid\infty}\int\Phi_w\,d\sigma_{C,w}\cdot\sigma_{C,f}\Big(\prod_v K_v\Big)
  \quad(\texttt{coneIntegral}).$$
This is the product decomposition of the adelic cone measure into the local cone measures, applied to
$\Phi = \Phi_\infty\otimes\mathbf 1_{\hat L}$ (or $\hat\Phi$). It says nothing about any covolume. Field: `eq`. -/
@[kb "weil1982" "§4.5, p. 108 (the cone integral as a product of local factors) [unverified page]"]
structure AdelicConeEuler {c₀ : 𝓞 F} (hc₀ : c₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) k)
    (hQ : (coneFormO c₀ Q₀').Nondegenerate) {C : Set (AdeleSpace F (Fin (k + 1 + 1)))} (σ : Measure C)
    (Φ : AdeleSpace F (Fin (k + 1 + 1)) → ℝ≥0∞) : Prop where
  /-- The identification with `coneIntegral` for Gaussian-bounded archimedean factors and a bounded box. -/
  eq : ∃ (Φr : ∀ w : {w : InfinitePlace F // w.IsReal}, ConeReal.ConeT (coneForm (cRe c₀ w) (QRe Q₀' w)) → ℝ≥0∞)
    (Φc : ∀ w : {w : InfinitePlace F // w.IsComplex}, ConeComplex.ConeT (coneForm (cCx c₀ w) (QCx Q₀' w)) → ℝ≥0∞)
    (ar Cr : {w : InfinitePlace F // w.IsReal} → ℝ) (ac Cc : {w : InfinitePlace F // w.IsComplex} → ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)),
    (∀ w, 0 < ar w) ∧ (∀ w, 0 ≤ Cr w) ∧
    (∀ w z, Φr w z ≤ ENNReal.ofReal (Cr w * Real.exp (-(ar w * ‖(z : Fin (k + 1 + 1) → ℝ)‖ ^ 2)))) ∧
    (∀ w, 0 < ac w) ∧ (∀ w, 0 ≤ Cc w) ∧
    (∀ w z, Φc w z ≤ ENNReal.ofReal (Cc w * Real.exp (-(ac w * ‖(z : Fin (k + 1 + 1) → ℂ)‖ ^ 2)))) ∧
    (∀ v ∈ S, Bornology.IsBounded (K v)) ∧
    ∫⁻ x, Φ x.1 ∂σ = coneIntegral hc₀ Q₀' hQ Φr Φc S K

/-- **$I_C(\Phi) < \infty$** for $\dim V = k+2\ge5$, from the identification and `coneIntegral_lt_top`. -/
theorem AdelicConeEuler.lt_top (hk : 3 ≤ k) {c₀ : 𝓞 F} {hc₀ : c₀ ≠ 0} {Q₀' : QuadForm (𝓞 F) k}
    (hQ' : Q₀'.Nondegenerate) {hQ : (coneFormO c₀ Q₀').Nondegenerate} {C : Set (AdeleSpace F (Fin (k + 1 + 1)))}
    {σ : Measure C} {Φ : AdeleSpace F (Fin (k + 1 + 1)) → ℝ≥0∞} (h : AdelicConeEuler hc₀ Q₀' hQ σ Φ) :
    ∫⁻ x, Φ x.1 ∂σ < ⊤ := by
  obtain ⟨Φr, Φc, ar, Cr, ac, Cc, S, K, har, hCr, hΦr, hac, hCc, hΦc, hK, heq⟩ := h.eq
  rw [heq]
  exact coneIntegral_lt_top hc₀ hk hQ' hQ Φr Φc ar Cr har hCr hΦr ac Cc hac hCc hΦc S K hK

/-- **The cone inputs for one cone form** with test functions $\Phi$, $\hat\Phi$: the adelic cone data with
$V' = Q_0'$, Weil's adelic fibration over the cone (`AdelicConeFibration`, input), and the identification of
$I_C(\Phi)$ and $I_C(\hat\Phi)$ with `coneIntegral` (`AdelicConeEuler`, input). Fields: `A`, `fib`, `euler`,
`eulerHat`. -/
structure AdelicConeInputs {c₀ : 𝓞 F} (hc₀ : c₀ ≠ 0) {Q₀' : QuadForm (𝓞 F) k} (hQ' : Q₀'.Nondegenerate)
    (hQ : (coneFormO c₀ Q₀').Nondegenerate) (Φ Φh : AdeleSpace F (Fin (k + 1 + 1)) → ℝ≥0∞) where
  /-- The adelic cone data. -/
  A : AdelicConeData (coneFormO c₀ Q₀') Q₀'
  /-- Weil's fibration over the cone (input). -/
  fib : AdelicConeFibration hQ hQ' A
  /-- The cone integral of $\Phi$ as a product of local factors (input). -/
  euler : AdelicConeEuler hc₀ Q₀' hQ A.σ Φ
  /-- The cone integral of $\hat\Phi$ as a product of local factors (input). -/
  eulerHat : AdelicConeEuler hc₀ Q₀' hQ A.σ Φh

/-- **$\tau(SO(V)) = 2$ for the cone form** $\langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'$, $\dim V = k+2\ge5$
(Weil 1982, §4.5, pp. 108–109, Steps 1–4): given the sphere data `W` (the inputs), the cone
inputs `I`, the induction hypothesis in dimension $k+1$ (`AdelicComplementTauTwo W.S`) and
$\operatorname{covol}(SO(Q_0')(F)\backslash SO(Q_0')(\mathbb A)) < \infty$ (dimension $k$). -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(G) = 2 for isotropic V, the cone terms C₁, C₂)"]
theorem tamagawaNumberTwoAdelic_cone (hk : 3 ≤ k) {c₀ : 𝓞 F} (hc₀ : c₀ ≠ 0) {Q₀' : QuadForm (𝓞 F) k}
    (hQ' : Q₀'.Nondegenerate) {hQ : (coneFormO c₀ Q₀').Nondegenerate} (W : AdelicWeilCore (coneFormO c₀ Q₀') hQ)
    (I : AdelicConeInputs hc₀ hQ' hQ W.Φ W.Φh) (hτ : AdelicComplementTauTwo W.S) (hcov : covolSO Q₀' hQ' ≠ ⊤) :
    TamagawaNumberTwoAdelic (coneFormO c₀ Q₀') hQ := by
  have hn : 3 ≤ k + 1 + 1 := by omega
  set c1 := covolSO Q₀' hQ' * (I.A.coneInt W.Φ * ENNReal.ofReal (dedekindZeta_residue F / 2)) with hc1
  set c2 := covolSO Q₀' hQ' * (I.A.coneInt W.Φh *
    ENNReal.ofReal (dedekindZeta_residue F / (((k + 1 + 1 : ℕ) : ℝ) - 2))) with hc2
  have hI1 : I.A.coneInt W.Φ ≠ ⊤ := (I.euler.lt_top hk hQ').ne
  have hI2 : I.A.coneInt W.Φh ≠ ⊤ := (I.eulerHat.lt_top hk hQ').ne
  have hK : c1 + c2 ≠ ⊤ := ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top hcov (ENNReal.mul_ne_top hI1 ENNReal.ofReal_ne_top),
      ENNReal.mul_ne_top hcov (ENNReal.mul_ne_top hI2 ENNReal.ofReal_ne_top)⟩
  refine tamagawaNumberTwoAdelic_of_coneBound (k := k + 1) (by omega) W hτ hK ?_ ?_
  · intro D DM hD hDM s hs _
    exact (I.fib.coneC1_le hn hD hDM W.measurable_Φ hs).trans le_self_add
  · intro D DM hD hDM s hs _
    exact (I.fib.coneC2_le hn hD hDM W.measurable_Φh hs).trans le_add_self

/-! ### Every isotropic $V$ -/

/-- **The per-dimension cone inputs** (**input**): every cone form $\langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'$
with $Q_0'$ nondegenerate in $k$ variables carries the sphere data `AdelicWeilCore` and the cone inputs
`AdelicConeInputs` for the same test functions. It contains no covolume or Tamagawa number of the form itself. Field:
`data`. -/
@[kb "weil1982" "§4.5, pp. 108–109 (inputs of the induction step, isotropic case) [unverified page]"]
structure AdelicConeStepInputs (F : Type) [Field F] [NumberField F] (k : ℕ) : Prop where
  /-- The data for each cone form. -/
  data : ∀ (c₀ : 𝓞 F) (hc₀ : c₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) k) (hQ' : Q₀'.Nondegenerate)
    (hQ : (coneFormO c₀ Q₀').Nondegenerate),
    Nonempty (Σ W : AdelicWeilCore (coneFormO c₀ Q₀') hQ, AdelicConeInputs hc₀ hQ' hQ W.Φ W.Φh)

/-- **$\tau(SO(V)) = 2$ for every isotropic $V$ of dimension $k+2\ge5$** over a number field $F$ (Weil 1982, §4.5;
cone case): given the per-dimension cone inputs, $\tau = 2$ for every nondegenerate form in $k+1$ variables (the
complements) and $\operatorname{covol} < \infty$ for every nondegenerate form in $k$ variables ($V' = \xi_0^\perp/\xi_0$).
The reduction to the cone form is `covolume_muTam_eq_cone`. -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(SO(V)) = 2, V isotropic, dim ≥ 5)"]
theorem tamagawaNumberTwoAdelic_of_isotropic (hk : 3 ≤ k) (Q₀ : QuadForm (𝓞 F) (k + 1 + 1)) (hQ : Q₀.Nondegenerate)
    (hiso : (Q₀.map (algebraMap (𝓞 F) F)).IsotropicIn F) (step : AdelicConeStepInputs F k)
    (hτ : ∀ (Q : QuadForm (𝓞 F) (k + 1)) (hQ : Q.Nondegenerate), TamagawaNumberTwoAdelic Q hQ)
    (hcov : ∀ (Q : QuadForm (𝓞 F) k) (hQ : Q.Nondegenerate), covolSO Q hQ ≠ ⊤) :
    TamagawaNumberTwoAdelic Q₀ hQ := by
  obtain ⟨c₀, hc₀, Q₀', hQ', heq⟩ := covolume_muTam_eq_cone (by omega) Q₀ hQ hiso
  show covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) = 2
  rw [heq]
  have hQc : (coneFormO c₀ Q₀').Nondegenerate :=
    nondegenerate_splitForm hc₀ (nondegenerate_splitForm (neg_ne_zero.mpr hc₀) hQ')
  obtain ⟨⟨W, I⟩⟩ := step.data c₀ hc₀ Q₀' hQ' hQc
  exact tamagawaNumberTwoAdelic_cone hk hc₀ hQ' W I ⟨fun c => hτ _ _⟩ (hcov _ _)

/-! ### The combined induction -/

/-- **$\tau = 2$ for all nondegenerate forms of dimension $m$ over $F$** (target statement). -/
def TauTwoAll (F : Type) [Field F] [NumberField F] (m : ℕ) : Prop :=
  ∀ (Q₀ : QuadForm (𝓞 F) m) (hQ : Q₀.Nondegenerate), TamagawaNumberTwoAdelic Q₀ hQ

/-- **The base case: every quaternary form** (**input**; generalizes `AnisotropicTauTwoBase F 4` to all
quaternary forms, isotropic or not). Over a totally real field, the totally positive definite case
is proved (`quaternaryTauTwoBase_of_notPosDef`). Field: `tau_two`. -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4), p. 65; §4.5 (induction base) [unverified page]"]
structure QuaternaryTauTwoBase (F : Type) [Field F] [NumberField F] : Prop where
  /-- $\tau = 2$ in dimension $4$. -/
  tau_two : TauTwoAll F 4

/-- The anisotropic base case is a special case. -/
theorem QuaternaryTauTwoBase.anisotropic (h : QuaternaryTauTwoBase F) : AnisotropicTauTwoBase F 4 :=
  ⟨fun Q₀ hQ _ => h.tau_two Q₀ hQ⟩

/-- **$\tau = 2$ in dimension $3$** over every number field, unconditionally (`covolume_muTam_ternary`). -/
@[kb "weil1982" "§3.7(a), pp. 62–63; Thm 3.7.1 (m = 3), p. 65"]
theorem tauTwoAll_three : TauTwoAll F 3 := fun Q₀ hQ => covolume_muTam_ternary Q₀ hQ

/-- **The base case over a totally real field**: only the quaternary forms that are not totally positive
definite are needed (`quaternaryTamagawaTwo_nf'` gives the totally positive definite ones, unconditionally). -/
theorem quaternaryTauTwoBase_of_notPosDef [IsTotallyReal F]
    (h : ∀ (Q₀ : QuadForm (𝓞 F) 4) (hQ : Q₀.Nondegenerate), ¬ Lattices.IsTotallyPosDef (HilbertModular.formF Q₀) →
      TamagawaNumberTwoAdelic Q₀ hQ) : QuaternaryTauTwoBase F := by
  refine ⟨fun Q₀ hQ => ?_⟩
  by_cases hpd : Lattices.IsTotallyPosDef (HilbertModular.formF Q₀)
  · exact (tamagawaNumberTwoAdelic_iff Q₀ hQ (by norm_num) hpd (LatChange.isIntegral_std Q₀)).2
      ((quaternaryTamagawaTwo_nf' F).tau_eq_two Q₀ hpd)
  · exact h Q₀ hQ hpd

/-- A form that is not anisotropic over $F$ is isotropic over $F$. -/
theorem isotropicIn_of_not_anisotropicF {n : ℕ} {Q₀ : QuadForm (𝓞 F) n} (h : ¬ AnisotropicF Q₀) :
    (Q₀.map (algebraMap (𝓞 F) F)).IsotropicIn F := by
  unfold AnisotropicF at h
  push_neg at h
  obtain ⟨ξ, hξ, hξ0⟩ := h
  refine ⟨ξ, hξ0, ?_⟩
  simpa [qF, QuadForm.evalIn, QuadForm.eval] using hξ

/-- **Weil's induction for every nondegenerate form**: from $\tau = 2$ in dimension $3$
(proved), the quaternary base case (`QuaternaryTauTwoBase`, input) and the per-dimension inputs (`AdelicStepInputs`
for anisotropic forms of dimension $\ge5$, `AdelicConeStepInputs` for cone forms of dimension $\ge5$),
$\tau(SO(V)) = 2$ for every nondegenerate $V$ of dimension $m\ge3$ over the number field $F$, anisotropic or isotropic,
every signature. -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(SO(V)) = 2 for all V, dim ≥ 3, by induction on dim)"]
theorem tauTwoAll_of_inputs (base : QuaternaryTauTwoBase F) (stepA : ∀ k, 4 ≤ k → AdelicStepInputs F k)
    (stepC : ∀ k, 3 ≤ k → AdelicConeStepInputs F k) : ∀ m, 3 ≤ m → TauTwoAll F m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases (show m = 3 ∨ m = 4 ∨ 5 ≤ m by omega) with rfl | rfl | h5
    · exact tauTwoAll_three
    · exact base.tau_two
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 + 1 := ⟨m - 2, by omega⟩
      intro Q₀ hQ
      have hτ : TauTwoAll F (k + 1) := ih (k + 1) (by omega) (by omega)
      by_cases haniso : AnisotropicF Q₀
      · obtain ⟨W⟩ := (stepA (k + 1) (by omega)).data Q₀ hQ haniso
        exact tamagawaNumberTwoAdelic_of_anisotropic (k := k + 1) (by omega) haniso W.toAdelicWeilCore
          ⟨fun c => hτ _ _⟩
      · refine tamagawaNumberTwoAdelic_of_isotropic (by omega) Q₀ hQ (isotropicIn_of_not_anisotropicF haniso)
          (stepC k (by omega)) hτ fun Q hQ' => ?_
        exact (ih k (by omega) (by omega) Q hQ').finite.ne

end QuadFormsKB.Tamagawa.Measure.Weil
