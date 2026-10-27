import QuadFormsKB.Tamagawa.Measure.Weil.TauTwoFinal
import QuadFormsKB.Tamagawa.Measure.Weil.TauTwoIsotropicGauss
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereDensitiesProof
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqTauTwo
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSIndefFinal

/-!
# Weil's induction step with a bound for $\hat\Phi$ in place of its Euler identity

`AdelicWeilCore` asks for the Euler-product identification of the adelic spherical integrals of $\hat\Phi$ with the
**standard** local factors of $Q_0$ (`eulerHat`). For $\hat\Phi$ = `gaussTestHat Q₀` this is false in general (its local
lattice is $H^{-1}\mathfrak d^{-1}\mathcal O_v^n$, not $\mathcal O_v^n$). The induction
step only uses `eulerHat` to get $Z^+_{\hat\Phi}(1) < \infty$. Here:

* **`AdelicWeilCoreB`**: the data of `AdelicWeilCore` with `eulerHat` (and its archimedean data) replaced by the pointwise
  bound `hatBound`: $M_1\hat\Phi\le C\,M_1\Phi$ for the multiplicative transforms (`mellinPhi`), $C<\infty$;
* **`adelicZetaPlus_ne_top_of_hatBound`**: then $Z^+_{\hat\Phi}(1)\le C\,Z^+_\Phi(1) < \infty$;
* the induction step with it: **`tamagawaNumberTwoAdelic_of_coneBound_B`**, **`tamagawaNumberTwoAdelic_of_anisotropic_B`**,
  **`tamagawaNumberTwoAdelic_cone_B`** (same proofs as `tamagawaNumberTwoAdelic_of_coneBound`,
  `tamagawaNumberTwoAdelic_of_anisotropic`, `tamagawaNumberTwoAdelic_cone`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.SphericalZeta QuadFormsKB.SphericalNF QuadFormsKB.GlobalZeta QuadFormsKB.Siegel
  QuadFormsKB.Tamagawa.Measure.ConeAdelic QuadFormsKB.Tamagawa.Measure.ConeAlgebra
  QuadFormsKB.Tamagawa.Measure.ConeReduction

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

/-- **The data of Weil's induction step with a bound for $\hat\Phi$** ($Q_0$ in $m = k+1$ variables): the fields of
`AdelicWeilCore` except the Euler identification for $\hat\Phi$ and its archimedean data, together with `hatBound`:
$M_1\hat\Phi(y)\le C\,M_1\Phi(y)$ for all $y$, some $C<\infty$ (`mellinPhi`, $s = 1$). The named inputs among the
fields are `fib`, `poisson`, `euler`, `vanish`; the rest are data and elementary conditions. Fields: `S`, `fib`, `Φ`,
`Φh`, `measurable_Φ`, `measurable_Φh`, `poisson`, `a`, `b`, `a_nonneg`, `b_pos`, `Φ_zero`, `Φh_zero`, `Φr`, `Ψ`, `κ`,
`euler`, `κ_nonneg`, `b_eq`, `archTest`, `Φr_nonneg`, `archTestC`, `Ψ_nonneg`, `vanish`, `hatBound`. -/
structure AdelicWeilCoreB (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate) where
  /-- The sphere family. -/
  S : AdelicSphereFamily Q₀
  /-- Weil's fibration over each sphere. -/
  fib : S.Fibration hQ
  /-- The test function $\Phi$. -/
  Φ : AdeleSpace F (Fin (k + 1)) → ℝ≥0∞
  /-- Its Fourier transform $\hat\Phi$. -/
  Φh : AdeleSpace F (Fin (k + 1)) → ℝ≥0∞
  measurable_Φ : Measurable Φ
  measurable_Φh : Measurable Φh
  /-- The twisted Poisson formula. -/
  poisson : AdelicThetaPoisson Q₀ Φ Φh
  /-- $\Phi(0)$. -/
  a : ℝ
  /-- $\hat\Phi(0)$. -/
  b : ℝ
  a_nonneg : 0 ≤ a
  b_pos : 0 < b
  Φ_zero : Φ 0 = ENNReal.ofReal a
  Φh_zero : Φh 0 = ENNReal.ofReal b
  /-- Real-place data of $\Phi$. -/
  Φr : RealPlace F → (Fin (k + 1) → ℝ) → ℝ
  /-- Complex-place data of $\Phi$. -/
  Ψ : ComplexPlace F → (Fin (k + 1) → ℂ) → ℝ
  /-- The measure constant for $\Phi$. -/
  κ : ℝ
  /-- The Euler-product identification for $\Phi$. -/
  euler : AdelicSphericalEuler S Φ Φr Ψ κ
  κ_nonneg : 0 ≤ κ
  /-- $\hat\Phi(0) = \int_{V_{\mathbb A}}\Phi = \kappa\cdot$ `phiIntegralNF`. -/
  b_eq : b = κ * phiIntegralNF Φr Ψ
  archTest : IsArchTestFn Q₀ Φr
  Φr_nonneg : ∀ w x, 0 ≤ Φr w x
  archTestC : IsArchTestFnC Q₀ Ψ
  Ψ_nonneg : ∀ w x, 0 ≤ Ψ w x
  /-- Vanishing at non-represented classes. -/
  vanish : NonrepresentedVanish Q₀ Φr Ψ
  /-- The multiplicative transform of $\hat\Phi$ is bounded by that of $\Phi$. -/
  hatBound : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ y, mellinPhi Φh 1 y ≤ C * mellinPhi Φ 1 y

variable {Q₀ : QuadForm (𝓞 F) (k + 1)} {hQ : Q₀.Nondegenerate}

/-- **$Z^+_{\hat\Phi}(1) < \infty$ from the bound**: $Z^+_{\hat\Phi}(1) = \sum_cZ_{\hat\Phi}(1,c)\le C\sum_cZ_\Phi(1,c) =
C\,Z^+_\Phi(1)$. -/
theorem adelicZetaPlus_ne_top_of_hatBound (hk : 1 ≤ k) (S : AdelicSphereFamily Q₀) (hS : S.Fibration hQ)
    (hτ : AdelicComplementTauTwo S) {Φ Φh : AdeleSpace F (Fin (k + 1)) → ℝ≥0∞} (hΦ : Measurable Φ)
    (hΦh : Measurable Φh) {C : ℝ≥0∞} (hC : C ≠ ⊤) (hb : ∀ y, mellinPhi Φh 1 y ≤ C * mellinPhi Φ 1 y)
    {D : Set (SOAdele Q₀)} (hD : IsFundamentalDomain (GammaSOAdele Q₀) D (muTam Q₀ hQ 1))
    {DM : Set (Adeles F)ˣ} (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F))
    (hZ : adelicZetaPlus Q₀ hQ Φ D DM 1 ≠ ⊤) : adelicZetaPlus Q₀ hQ Φh D DM 1 ≠ ⊤ := by
  rw [adelicZetaPlus_eq_tsum_of_complementTauTwo hk S hS hτ hΦh hD hDM 1]
  rw [adelicZetaPlus_eq_tsum_of_complementTauTwo hk S hS hτ hΦ hD hDM 1] at hZ
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hC hZ) ?_
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun c => ?_
  unfold adelicSphZeta
  rw [← lintegral_const_mul' _ _ hC]
  exact lintegral_mono fun x => hb x.1

/-- **$\tau(SO(V)) = 2$ from dimension $m-1$, given bounded cone terms, with the bound for $\hat\Phi$** (as
`tamagawaNumberTwoAdelic_of_coneBound`, with `W : AdelicWeilCoreB`). -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(G) = 2 by comparing the residues, cone terms included)"]
theorem tamagawaNumberTwoAdelic_of_coneBound_B (hk : 4 ≤ k) (W : AdelicWeilCoreB Q₀ hQ)
    (hτ : AdelicComplementTauTwo W.S) {K : ℝ≥0∞} (hK : K ≠ ⊤)
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
  have hZh : adelicZetaPlus Q₀ hQ W.Φh D DM 1 ≠ ⊤ := by
    obtain ⟨C, hC, hb⟩ := W.hatBound
    exact adelicZetaPlus_ne_top_of_hatBound hk1 W.S W.fib hτ W.measurable_Φ W.measurable_Φh hC hb hD hDM
      (by rw [hZ 1 one_pos]; exact ENNReal.ofReal_ne_top)
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

/-- **$\tau(SO(V)) = 2$ for anisotropic $V$ of dimension $m = k+1\ge5$, with the bound for $\hat\Phi$** (as
`tamagawaNumberTwoAdelic_of_anisotropic`; the cone terms vanish). -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(G) = 2 by comparing the residues of Z(s) at s = 0)"]
theorem tamagawaNumberTwoAdelic_of_anisotropic_B (hk : 4 ≤ k) (haniso : AnisotropicF Q₀) (W : AdelicWeilCoreB Q₀ hQ)
    (hτ : AdelicComplementTauTwo W.S) : TamagawaNumberTwoAdelic Q₀ hQ := by
  have hρ := dedekindZeta_residue_pos F
  obtain ⟨D, hD⟩ := (hasFundamentalDomain_GammaSOAdele Q₀ (muTam Q₀ hQ 1)).ExistsIsFundamentalDomain
  obtain ⟨DM, hDM⟩ := exists_isFundamentalDomain_ideles (tamIdeles F)
  have hk1 : 1 ≤ k := by omega
  -- the multiplicative side
  have hZ : ∀ s, 0 < s → adelicZetaPlus Q₀ hQ W.Φ D DM s = ENNReal.ofReal (W.κ * sphericalZetaNF Q₀ W.Φr W.Ψ s) :=
    fun s hs => by
      rw [adelicZetaPlus_eq_tsum_of_complementTauTwo hk1 W.S W.fib hτ W.measurable_Φ hD hDM s]
      exact tsum_adelicSphZeta_eq hk W.euler W.κ_nonneg hQ W.Φr_nonneg W.Ψ_nonneg W.vanish hs
  have hZh : adelicZetaPlus Q₀ hQ W.Φh D DM 1 ≠ ⊤ := by
    obtain ⟨C, hC, hb⟩ := W.hatBound
    exact adelicZetaPlus_ne_top_of_hatBound hk1 W.S W.fib hτ W.measurable_Φ W.measurable_Φh hC hb hD hDM
      (by rw [hZ 1 one_pos]; exact ENNReal.ofReal_ne_top)
  -- Step 4: finite volume
  set s₀ : ℝ := (k + 1) * W.b / (4 * (W.a + 1)) with hs₀
  have ha1 : 0 < W.a + 1 := by linarith [W.a_nonneg]
  have hs₀pos : 0 < s₀ := by have := W.b_pos; positivity
  have hsb : 2 * s₀ * W.a < ((k + 1 : ℕ) : ℝ) * W.b := by
    rw [hs₀]; push_cast
    have hb := W.b_pos
    have hkb : 0 < ((k : ℝ) + 1) * W.b := by positivity
    rw [show 2 * ((↑k + 1) * W.b / (4 * (W.a + 1))) * W.a = ((↑k + 1) * W.b) * (W.a / (2 * (W.a + 1))) by
      field_simp; ring]
    have : W.a / (2 * (W.a + 1)) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [W.a_nonneg]
    nlinarith
  have hDfin : muTam Q₀ hQ 1 D < ⊤ := measure_fundamentalDomain_lt_top haniso W.measurable_Φ W.measurable_Φh
    W.poisson hDM W.a_nonneg W.b_pos W.Φ_zero W.Φh_zero hs₀pos hsb
    (by rw [hZ s₀ hs₀pos]; exact ENNReal.ofReal_ne_top)
  -- the additive residue
  have hC : adelicZetaPlus Q₀ hQ W.Φh D DM 1 + adelicZetaPlus Q₀ hQ W.Φ D DM 1 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hZh, by rw [hZ 1 one_pos]; exact ENNReal.ofReal_ne_top⟩
  have hadd := tendsto_mul_adelicZetaPlus (by omega) haniso W.measurable_Φ W.measurable_Φh W.poisson hDM
    W.a_nonneg W.b_pos W.Φ_zero W.Φh_zero hDfin.ne hC
    (W.fib.measurable_adelicInner hk1 W.measurable_Φh hDM 1)
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

/-- **$\tau(SO(V)) = 2$ for the cone form, with the bound for $\hat\Phi$** (as `tamagawaNumberTwoAdelic_cone`). -/
@[kb "weil1982" "§4.5, pp. 108–109 (τ(G) = 2 for isotropic V, the cone terms C₁, C₂)"]
theorem tamagawaNumberTwoAdelic_cone_B (hk : 3 ≤ k) {c₀ : 𝓞 F} (hc₀ : c₀ ≠ 0) {Q₀' : QuadForm (𝓞 F) k}
    (hQ' : Q₀'.Nondegenerate) {hQ : (coneFormO c₀ Q₀').Nondegenerate} (W : AdelicWeilCoreB (coneFormO c₀ Q₀') hQ)
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
  refine tamagawaNumberTwoAdelic_of_coneBound_B (k := k + 1) (by omega) W hτ hK ?_ ?_
  · intro D DM hD hDM s hs _
    exact (I.fib.coneC1_le hn hD hDM W.measurable_Φ hs).trans le_self_add
  · intro D DM hD hDM s hs _
    exact (I.fib.coneC2_le hn hD hDM W.measurable_Φh hs).trans le_add_self

end QuadFormsKB.Tamagawa.Measure.Weil

end
