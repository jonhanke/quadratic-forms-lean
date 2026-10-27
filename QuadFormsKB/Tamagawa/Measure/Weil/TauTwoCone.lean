import QuadFormsKB.Tamagawa.Measure.Weil.TauTwoAnisotropic

/-!
# Steps 2 and 4 of Weil's induction with the cone terms

$F$ a number field, $Q_0$ a nondegenerate form over $\mathcal O_F$ in $n$ variables, **any** $Q = Q_0\otimes F$ (isotropic
or not), $G = SO(V)$ with Weil's measure $\mu$ = `muTam Q₀ hQ 1`, $D$ a fundamental domain of $SO(V)(F)$, $D_M$ one of
$F^\times$ in $\mathbb A^\times$. This file generalizes the Steps 2 and 4 (`TauTwoAnisotropic.lean`) by
keeping the cone $C(F)\setminus0 = \{\xi\ne0 : Q(\xi) = 0\}$ in the theta sum:
$$V(F) = \{0\}\sqcup\{Q\ne0\}\sqcup(C(F)\setminus0)\qquad(\texttt{tsum\_theta\_cone\_eq}).$$

* **The cone terms.** `coneTheta` $\kappa_\Phi(g,z) = \sum_{\xi\in C(F)\setminus0}\Phi(z\,g^{-1}\xi)$, its parts on
  $\|z\|\le1$: `coneLo` $= \int_{D_M,\|z\|\le1}\|z\|^{n+2s}\kappa_\Phi(g,z)$ and `coneRem`
  $= \int_{D_M,\|z\|\le1}\|z\|^{2s}\kappa_{\hat\Phi}(g,z^{-1})$, and their integrals over $D$: `coneC1` $= C_1(s)$,
  `coneC2` $= C_2(s)$ (Weil 1982, §4.5, p. 108, Step 2).
* **Step 2** (`lo_add_cone_eq`): with the twisted Poisson formula (`AdelicThetaPoisson`), for $s > 0$,
  $$\Phi(0)\frac{\rho_F}{n+2s} + \mathrm{lo}(g,s) + \mathrm{coneLo}(g,s) = \hat\Phi(0)\frac{\rho_F}{2s} + J(g,s) +
    \mathrm{coneRem}(g,s).$$
* **Step 4** (`measure_fundamentalDomain_lt_top_cone`): if $Z^+(s_0) < \infty$ and $C_1(s_0) < \infty$ for one $s_0 > 0$
  with $2s_0\Phi(0) < n\hat\Phi(0)$, then $\operatorname{vol}(SO(V)(F)\backslash SO(V)(\mathbb A)) < \infty$ (exhaustion, as
  in the anisotropic case; no decay estimate).
* **The residue** (`tendsto_mul_adelicZetaPlus_cone`): if moreover $C_1(s), C_2(s)\le K < \infty$ for $0 < s\le1$, then
  $sZ^+(s)\to\operatorname{vol}\cdot\rho_F\hat\Phi(0)/2$ as $s\to0^+$.

The closed forms $C_1(s) = \operatorname{covol}(SO(V'))\,I_C(\Phi)\,\rho_F/(2+2s)$ and
$C_2(s) = \operatorname{covol}(SO(V'))\,I_C(\hat\Phi)\,\rho_F/(n-2+2s)$ (Step 3) are in `ConeUnfoldAdelic.lean`; for
anisotropic $Q$ the cone terms vanish and these statements reduce to the anisotropic ones.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure QuadFormsKB.SphericalZeta

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### The cone part of the theta sum -/

open Classical in
/-- **The cone theta sum** $\kappa_\Phi(g, z) = \sum_{\xi\in C(F)\setminus0}\Phi(z\,g^{-1}\xi)$, $C(F)\setminus0 =
\{\xi\in F^n : Q(\xi) = 0,\ \xi\ne0\}$ (Weil 1982, §4.5, p. 108). Parameters: `Q₀`, `Φ`, `g`, `z`. -/
def coneTheta (Q₀ : QuadForm (𝓞 F) n) (Φ : AdeleSpace F (Fin n) → ℝ≥0∞) (g : SOAdele Q₀) (z : (Adeles F)ˣ) :
    ℝ≥0∞ :=
  ∑' ξ : Fin n → F, (if qF Q₀ ξ = 0 ∧ ξ ≠ 0 then Φ (z • g⁻¹ • diagVec F (Fin n) ξ) else 0)

theorem measurable_coneTheta (Q₀ : QuadForm (𝓞 F) n) {Φ : AdeleSpace F (Fin n) → ℝ≥0∞} (hΦ : Measurable Φ)
    (g : SOAdele Q₀) : Measurable (coneTheta Q₀ Φ g) := by
  refine Measurable.ennreal_tsum fun ξ => ?_
  split_ifs
  · exact hΦ.comp (measurable_units_smul.comp (measurable_id.prodMk measurable_const))
  · exact measurable_const

/-- **The three-way split of the theta sum** (any $Q$): $\sum_{\xi\in V(F)}\Phi(z\,g^{-1}\xi) = \Phi(0) +
\theta_\Phi(g,z) + \kappa_\Phi(g,z)$ ($\xi = 0$, $Q(\xi)\ne0$, and the punctured cone). -/
theorem tsum_theta_cone_eq (Q₀ : QuadForm (𝓞 F) n) (Φ : AdeleSpace F (Fin n) → ℝ≥0∞) (g : SOAdele Q₀)
    (z : (Adeles F)ˣ) :
    ∑' ξ : Fin n → F, Φ (z • g⁻¹ • diagVec F (Fin n) ξ) = Φ 0 + thetaNZ Q₀ Φ g z + coneTheta Q₀ Φ g z := by
  classical
  rw [ENNReal.tsum_eq_add_tsum_ite (0 : Fin n → F), map_zero, soAdele_smul_zero, smul_zero, add_assoc, thetaNZ,
    coneTheta, ← ENNReal.tsum_add]
  congr 1
  refine tsum_congr fun ξ => ?_
  by_cases h : ξ = 0
  · subst h
    have h0 : qF Q₀ 0 = 0 := by simpa using qF_smul Q₀ 0 0
    simp [h0]
  · by_cases hq : qF Q₀ ξ = 0
    · simp [h, hq]
    · simp [h, hq]

/-- **Pointwise Tate split with the cone** (any $Q$, given the twisted Poisson formula):
$\|z\|^{n+2s}(\Phi(0) + \theta_\Phi(g,z) + \kappa_\Phi(g,z)) =
\|z\|^{2s}(\hat\Phi(0) + \theta_{\hat\Phi}(g,z^{-1}) + \kappa_{\hat\Phi}(g,z^{-1}))$. -/
theorem zetaWeight_mul_theta_cone {Q₀ : QuadForm (𝓞 F) n} {Φ Φh : AdeleSpace F (Fin n) → ℝ≥0∞}
    (hP : AdelicThetaPoisson Q₀ Φ Φh) (s : ℝ) (g : SOAdele Q₀) (z : (Adeles F)ˣ) :
    zetaWeight s n z * (Φ 0 + thetaNZ Q₀ Φ g z + coneTheta Q₀ Φ g z) =
      ENNReal.ofReal (ideleNorm F z ^ (2 * s)) * (Φh 0 + thetaNZ Q₀ Φh g z⁻¹ + coneTheta Q₀ Φh g z⁻¹) := by
  rw [← tsum_theta_cone_eq, ← tsum_theta_cone_eq, ← hP.poisson g z, zetaWeight,
    show (n : ℝ) + 2 * s = 2 * s + n by ring, Real.rpow_add (ideleNorm_pos z),
    ENNReal.ofReal_mul (Real.rpow_nonneg (ideleNorm_pos z).le _), mul_assoc]

variable {Q₀ : QuadForm (𝓞 F) n} {DM : Set (Adeles F)ˣ}

/-- The cone part of the inner integral on $\|z\|\le1$:
$\mathrm{coneLo}(g,s) = \int_{D_M,\ \|z\|\le1}\|z\|^{n+2s}\kappa_\Phi(g,z)\,d\nu(z)$. -/
def coneLo (Q₀ : QuadForm (𝓞 F) n) (Φ : AdeleSpace F (Fin n) → ℝ≥0∞) (DM : Set (Adeles F)ˣ) (s : ℝ)
    (g : SOAdele Q₀) : ℝ≥0∞ :=
  ∫⁻ z in DM, (normLeOne F).indicator (fun z => zetaWeight s n z * coneTheta Q₀ Φ g z) z ∂tamIdeles F

/-- The dual cone remainder $\mathrm{coneRem}(g,s) = \int_{D_M,\ \|z\|\le1}\|z\|^{2s}\kappa_{\hat\Phi}(g,z^{-1})\,d\nu(z)$. -/
def coneRem (Q₀ : QuadForm (𝓞 F) n) (Φh : AdeleSpace F (Fin n) → ℝ≥0∞) (DM : Set (Adeles F)ˣ) (s : ℝ)
    (g : SOAdele Q₀) : ℝ≥0∞ :=
  ∫⁻ z in DM, (normLeOne F).indicator
    (fun z => ENNReal.ofReal (ideleNorm F z ^ (2 * s)) * coneTheta Q₀ Φh g z⁻¹) z ∂tamIdeles F

/-- **The Tate split of the part $\|z\|\le1$ with the cone terms** (Weil 1982, §4.5, pp. 108–109, Step 2;
any $Q$): for $s > 0$,
$$\Phi(0)\frac{\rho_F}{n+2s} + \mathrm{lo}(g,s) + \mathrm{coneLo}(g,s) = \hat\Phi(0)\frac{\rho_F}{2s} + J(g,s) +
  \mathrm{coneRem}(g,s).$$
For anisotropic $Q$ both cone terms vanish and this is `lo_add_eq`. -/
@[kb "weil1982" "§4.5, pp. 108–109 (split of ∫_{|z|≤1} by Poisson, with the cone terms) [unverified page]"]
theorem lo_add_cone_eq {Φ Φh : AdeleSpace F (Fin n) → ℝ≥0∞} (hΦ : Measurable Φ) (hΦh : Measurable Φh)
    (hP : AdelicThetaPoisson Q₀ Φ Φh) (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F)) {s : ℝ}
    (hs : 0 < s) (g : SOAdele Q₀) :
    Φ 0 * ENNReal.ofReal (dedekindZeta_residue F / (n + 2 * s)) + loInner Q₀ Φ DM s g + coneLo Q₀ Φ DM s g =
      Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s)) + dualRem Q₀ Φh DM s g +
        coneRem Q₀ Φh DM s g := by
  have hw := lintegral_ideleFD_le_one_rpow hDM (a := n + 2 * s) (by positivity)
  have hw2 := lintegral_ideleFD_le_one_rpow hDM (a := 2 * s) (by positivity)
  simp_rw [← indicator_rpow_eq] at hw hw2
  have hmw : ∀ a : ℝ, Measurable fun z : (Adeles F)ˣ => ENNReal.ofReal (ideleNorm F z ^ a) := fun a =>
    ENNReal.measurable_ofReal.comp (continuous_ideleNorm.measurable.pow_const a)
  have hmi : Measurable fun z : (Adeles F)ˣ => z⁻¹ := measurable_inv
  rw [← hw, ← hw2, ← lintegral_const_mul _ ((hmw _).indicator measurableSet_normLeOne),
    ← lintegral_const_mul _ ((hmw _).indicator measurableSet_normLeOne), loInner, dualRem, coneLo, coneRem]
  have hm1 : Measurable fun z => Φ 0 * (normLeOne F).indicator
      (fun z => ENNReal.ofReal (ideleNorm F z ^ ((n : ℝ) + 2 * s))) z :=
    measurable_const.mul ((hmw _).indicator measurableSet_normLeOne)
  have hm1' : Measurable fun z => (normLeOne F).indicator
      (fun z => zetaWeight s n z * thetaNZ Q₀ Φ g z) z :=
    ((measurable_zetaWeight s n).mul (measurable_thetaNZ Q₀ hΦ g)).indicator measurableSet_normLeOne
  have hm2 : Measurable fun z => Φh 0 * (normLeOne F).indicator
      (fun z => ENNReal.ofReal (ideleNorm F z ^ (2 * s))) z :=
    measurable_const.mul ((hmw _).indicator measurableSet_normLeOne)
  have hm2' : Measurable fun z => (normLeOne F).indicator
      (fun z => ENNReal.ofReal (ideleNorm F z ^ (2 * s)) * thetaNZ Q₀ Φh g z⁻¹) z :=
    ((hmw _).mul ((measurable_thetaNZ Q₀ hΦh g).comp hmi)).indicator measurableSet_normLeOne
  have hm12 : Measurable fun z => Φ 0 * (normLeOne F).indicator
      (fun z => ENNReal.ofReal (ideleNorm F z ^ ((n : ℝ) + 2 * s))) z +
        (normLeOne F).indicator (fun z => zetaWeight s n z * thetaNZ Q₀ Φ g z) z := hm1.add hm1'
  have hm22 : Measurable fun z => Φh 0 * (normLeOne F).indicator
      (fun z => ENNReal.ofReal (ideleNorm F z ^ (2 * s))) z +
        (normLeOne F).indicator
          (fun z => ENNReal.ofReal (ideleNorm F z ^ (2 * s)) * thetaNZ Q₀ Φh g z⁻¹) z := hm2.add hm2'
  rw [← lintegral_add_left hm1, ← lintegral_add_left hm12, ← lintegral_add_left hm2,
    ← lintegral_add_left hm22]
  refine lintegral_congr fun z => ?_
  by_cases h : z ∈ normLeOne F
  · simp only [indicator_of_mem h]
    have := zetaWeight_mul_theta_cone hP s g z
    rw [mul_add, mul_add, mul_add, mul_add] at this
    rw [zetaWeight] at this ⊢
    rw [mul_comm (Φ 0), mul_comm (Φh 0)]
    exact this
  · simp [indicator_of_notMem h]

/-! ### Step 4 with the cone terms -/

section Global

variable {hQ : Q₀.Nondegenerate} {D : Set (SOAdele Q₀)}

/-- **The cone term** $C_1(s) = \int_D\mathrm{coneLo}(g,s)\,d\mu(g) = \int_{[G]}\int_{\|z\|\le1}\|z\|^{n+2s}
\sum_{\xi\in C(F)\setminus0}\Phi(z\,g^{-1}\xi)$ (Step 2). -/
def coneC1 (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (Φ : AdeleSpace F (Fin n) → ℝ≥0∞) (D : Set (SOAdele Q₀))
    (DM : Set (Adeles F)ˣ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ g in D, coneLo Q₀ Φ DM s g ∂muTam Q₀ hQ 1

/-- **The dual cone term** $C_2(s) = \int_D\mathrm{coneRem}(g,s)\,d\mu(g) = \int_{[G]}\int_{\|w\|\ge1}\|w\|^{-2s}
\sum_{\xi\in C(F)\setminus0}\hat\Phi(w\,g^{-1}\xi)$ (written with $w = z^{-1}$; Step 2). -/
def coneC2 (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (Φh : AdeleSpace F (Fin n) → ℝ≥0∞)
    (D : Set (SOAdele Q₀)) (DM : Set (Adeles F)ˣ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ g in D, coneRem Q₀ Φh DM s g ∂muTam Q₀ hQ 1

/-- The $E$-form of the Step 4 inequality with the cone term (any $Q$): for $E\subseteq D$ and $s > 0$,
$\mu(E)\,\hat\Phi(0)\frac{\rho_F}{2s}\le\mu(E)\,\Phi(0)\frac{\rho_F}{n+2s} + Z^+(s) + C_1(s)$. -/
theorem measure_mul_le_of_subset_cone {Φ Φh : AdeleSpace F (Fin n) → ℝ≥0∞}
    (hΦ : Measurable Φ) (hΦh : Measurable Φh) (hP : AdelicThetaPoisson Q₀ Φ Φh)
    (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F)) {s : ℝ} (hs : 0 < s)
    (hmeas : Measurable (adelicInner Q₀ Φ DM s)) {E : Set (SOAdele Q₀)} (hE : E ⊆ D) :
    muTam Q₀ hQ 1 E * (Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s))) ≤
      muTam Q₀ hQ 1 E * (Φ 0 * ENNReal.ofReal (dedekindZeta_residue F / (n + 2 * s))) +
        adelicZetaPlus Q₀ hQ Φ D DM s + coneC1 Q₀ hQ Φ D DM s := by
  set μ := muTam Q₀ hQ 1
  set A := Φ 0 * ENNReal.ofReal (dedekindZeta_residue F / (n + 2 * s))
  set B := Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s))
  calc μ E * B = ∫⁻ _ in E, B ∂μ := by rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ g in E, (B + dualRem Q₀ Φh DM s g + coneRem Q₀ Φh DM s g) ∂μ :=
        lintegral_mono fun g => by rw [add_assoc]; exact le_self_add
    _ = ∫⁻ g in E, (A + loInner Q₀ Φ DM s g + coneLo Q₀ Φ DM s g) ∂μ :=
        lintegral_congr fun g => (lo_add_cone_eq hΦ hΦh hP hDM hs g).symm
    _ ≤ ∫⁻ g in E, (A + (adelicInner Q₀ Φ DM s g + coneLo Q₀ Φ DM s g)) ∂μ :=
        lintegral_mono fun g => by rw [add_assoc]; gcongr; exact loInner_le_adelicInner hΦ s g
    _ = μ E * A + (∫⁻ g in E, adelicInner Q₀ Φ DM s g ∂μ + ∫⁻ g in E, coneLo Q₀ Φ DM s g ∂μ) := by
        rw [lintegral_add_left measurable_const, setLIntegral_const, mul_comm, lintegral_add_left hmeas]
    _ ≤ μ E * A + adelicZetaPlus Q₀ hQ Φ D DM s + coneC1 Q₀ hQ Φ D DM s := by
        rw [add_assoc]
        gcongr
        · exact lintegral_mono_set hE
        · exact lintegral_mono_set hE

/-- **Step 4 with the cone: $\operatorname{vol}(SO(V)(F)\backslash SO(V)(\mathbb A)) < \infty$ by positivity**
(Step 4; any $Q$): if $\Phi(0) = a\ge0$, $\hat\Phi(0) = b > 0$, and $Z^+(s_0) < \infty$, $C_1(s_0) < \infty$ for one
$s_0 > 0$ with $2s_0a < nb$, then $\mu(D) < \infty$. No decay estimate and no reduction theory. -/
@[kb "weil1982" "§4.5, pp. 108–109 (finiteness of τ(G))"]
theorem measure_fundamentalDomain_lt_top_cone {Φ Φh : AdeleSpace F (Fin n) → ℝ≥0∞}
    (hΦ : Measurable Φ) (hΦh : Measurable Φh) (hP : AdelicThetaPoisson Q₀ Φ Φh)
    (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hΦ0 : Φ 0 = ENNReal.ofReal a) (hΦh0 : Φh 0 = ENNReal.ofReal b) {s₀ : ℝ} (hs₀ : 0 < s₀)
    (hsb : 2 * s₀ * a < n * b) (hmeas : Measurable (adelicInner Q₀ Φ DM s₀))
    (hfin : adelicZetaPlus Q₀ hQ Φ D DM s₀ ≠ ⊤) (hC1 : coneC1 Q₀ hQ Φ D DM s₀ ≠ ⊤) :
    muTam Q₀ hQ 1 D < ⊤ := by
  have hρ := dedekindZeta_residue_pos F
  have key := fun (E : Set (SOAdele Q₀)) (hE : E ⊆ D) =>
    measure_mul_le_of_subset_cone (hQ := hQ) hΦ hΦh hP hDM hs₀ hmeas hE
  have hn0 : (0 : ℝ) < n + 2 * s₀ := by positivity
  have hAeq : Φ 0 * ENNReal.ofReal (dedekindZeta_residue F / (n + 2 * s₀)) =
      ENNReal.ofReal (a * (dedekindZeta_residue F / (n + 2 * s₀))) := by
    rw [hΦ0, ← ENNReal.ofReal_mul ha]
  have hBeq : Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s₀)) =
      ENNReal.ofReal (b * (dedekindZeta_residue F / (2 * s₀))) := by
    rw [hΦh0, ← ENNReal.ofReal_mul hb.le]
  generalize hA : Φ 0 * ENNReal.ofReal (dedekindZeta_residue F / (n + 2 * s₀)) = A at key hAeq
  generalize hB : Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s₀)) = B at key hBeq
  have hZC : adelicZetaPlus Q₀ hQ Φ D DM s₀ + coneC1 Q₀ hQ Φ D DM s₀ ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hfin, hC1⟩
  generalize hZ : adelicZetaPlus Q₀ hQ Φ D DM s₀ + coneC1 Q₀ hQ Φ D DM s₀ = Z at hZC
  have key' : ∀ E ⊆ D, muTam Q₀ hQ 1 E * B ≤ muTam Q₀ hQ 1 E * A + Z := fun E hE => by
    rw [← hZ, ← add_assoc]; exact key E hE
  have hAB : A < B := by
    rw [hAeq, hBeq, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    rw [mul_div_assoc', mul_div_assoc', div_lt_div_iff₀ hn0 (by positivity)]
    have h1 : a * (2 * s₀) < b * (n + 2 * s₀) := by nlinarith [mul_pos hb hs₀]
    nlinarith [mul_lt_mul_of_pos_left h1 hρ]
  have hAt : A ≠ ⊤ := by rw [hAeq]; exact ENNReal.ofReal_ne_top
  have hBA : B - A ≠ 0 := (tsub_pos_of_lt hAB).ne'
  have hbound : ∀ E ⊆ D, muTam Q₀ hQ 1 E < ⊤ → muTam Q₀ hQ 1 E ≤ Z / (B - A) := by
    intro E hE hEt
    have k1 := key' E hE
    have hsplit : muTam Q₀ hQ 1 E * B = muTam Q₀ hQ 1 E * A + muTam Q₀ hQ 1 E * (B - A) := by
      rw [← mul_add, add_tsub_cancel_of_le hAB.le]
    rw [hsplit] at k1
    have k2 : muTam Q₀ hQ 1 E * (B - A) ≤ Z :=
      (ENNReal.add_le_add_iff_left (ENNReal.mul_ne_top hEt.ne hAt)).mp k1
    exact (ENNReal.le_div_iff_mul_le (Or.inl hBA) (Or.inr hZC)).mpr k2
  have hU : D = ⋃ i, D ∩ spanningSets (muTam Q₀ hQ 1) i := by
    rw [← inter_iUnion, iUnion_spanningSets, inter_univ]
  have hmono : Monotone fun i => D ∩ spanningSets (muTam Q₀ hQ 1) i := fun i j hij =>
    inter_subset_inter_right _ (monotone_spanningSets _ hij)
  have hle : muTam Q₀ hQ 1 D ≤ Z / (B - A) := by
    rw [hU, hmono.measure_iUnion]
    exact iSup_le fun i => hbound _ inter_subset_left
      ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top _ i))
  exact hle.trans_lt (ENNReal.div_lt_top hZC hBA)

/-- **$\lim_{s\to0^+}sZ^+(s) = \operatorname{vol}\cdot\rho_F\hat\Phi(0)/2$ with the cone terms** (Step 4; Weil
1982, §4.5, p. 109; any $Q$): once the volume is finite and the cone terms are bounded,
$C_1(s), C_2(s)\le K < \infty$ for $0 < s\le1$. The outer terms are bounded by $Z^+_\Phi(1) + Z^+_{\hat\Phi}(1)$
(monotonicity only), and $sC_1(s), sC_2(s)\to0$. -/
@[kb "weil1982" "§4.5, p. 109 (residue of Z⁺ at s = 0 is ρ_kτ(G)Φ̂(0)/2, cone terms included)"]
theorem tendsto_mul_adelicZetaPlus_cone (hn : 1 ≤ n) {Φ Φh : AdeleSpace F (Fin n) → ℝ≥0∞}
    (hΦ : Measurable Φ) (hΦh : Measurable Φh) (hP : AdelicThetaPoisson Q₀ Φ Φh)
    (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hΦ0 : Φ 0 = ENNReal.ofReal a) (hΦh0 : Φh 0 = ENNReal.ofReal b) (hDfin : muTam Q₀ hQ 1 D ≠ ⊤)
    (hC : adelicZetaPlus Q₀ hQ Φh D DM 1 + adelicZetaPlus Q₀ hQ Φ D DM 1 ≠ ⊤)
    (hmeasH : Measurable (adelicInner Q₀ Φh DM 1)) (hmeas : ∀ s, Measurable (adelicInner Q₀ Φ DM s))
    {K : ℝ≥0∞} (hK : K ≠ ⊤) (hC1 : ∀ s, 0 < s → s ≤ 1 → coneC1 Q₀ hQ Φ D DM s ≤ K)
    (hC2 : ∀ s, 0 < s → s ≤ 1 → coneC2 Q₀ hQ Φh D DM s ≤ K) :
    Tendsto (fun s => s * (adelicZetaPlus Q₀ hQ Φ D DM s).toReal) (𝓝[>] 0)
      (𝓝 ((muTam Q₀ hQ 1 D).toReal * (dedekindZeta_residue F * b) / 2)) := by
  have hρ := dedekindZeta_residue_pos F
  set V := muTam Q₀ hQ 1 D with hV
  set Zh := adelicZetaPlus Q₀ hQ Φh D DM 1 + adelicZetaPlus Q₀ hQ Φ D DM 1 with hZh
  have hlow : ∀ s, 0 < s → s ≤ 1 → V * (Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s))) ≤
      adelicZetaPlus Q₀ hQ Φ D DM s + K +
        V * (Φ 0 * ENNReal.ofReal (dedekindZeta_residue F / (n + 2 * s))) := fun s hs hs1 => by
    have h := measure_mul_le_of_subset_cone (hQ := hQ) hΦ hΦh hP hDM hs (hmeas s) (subset_refl D)
    calc _ ≤ _ := h
      _ = adelicZetaPlus Q₀ hQ Φ D DM s + coneC1 Q₀ hQ Φ D DM s +
          V * (Φ 0 * ENNReal.ofReal (dedekindZeta_residue F / (n + 2 * s))) := by ring
      _ ≤ _ := by gcongr; exact hC1 s hs hs1
  have hup : ∀ s, 0 < s → s ≤ 1 → adelicZetaPlus Q₀ hQ Φ D DM s ≤
      V * (Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s))) + (Zh + K) := fun s hs hs1 => by
    rw [adelicZetaPlus_eq_lintegral_inner]
    calc ∫⁻ g in D, adelicInner Q₀ Φ DM s g ∂muTam Q₀ hQ 1
        = ∫⁻ g in D, (loInner Q₀ Φ DM s g + hiInner Q₀ Φ DM s g) ∂muTam Q₀ hQ 1 :=
          lintegral_congr fun g => adelicInner_eq_lo_add_hi hΦ s g
      _ ≤ ∫⁻ g in D, (Φ 0 * ENNReal.ofReal (dedekindZeta_residue F / (n + 2 * s)) + loInner Q₀ Φ DM s g +
          coneLo Q₀ Φ DM s g + hiInner Q₀ Φ DM s g) ∂muTam Q₀ hQ 1 := lintegral_mono fun g => by
            gcongr; exact le_add_self.trans le_self_add
      _ = ∫⁻ g in D, (Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s)) + dualRem Q₀ Φh DM s g +
          coneRem Q₀ Φh DM s g + hiInner Q₀ Φ DM s g) ∂muTam Q₀ hQ 1 :=
          lintegral_congr fun g => by rw [lo_add_cone_eq hΦ hΦh hP hDM hs g]
      _ ≤ ∫⁻ g in D, (Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s)) +
          (adelicInner Q₀ Φh DM 1 g + (adelicInner Q₀ Φ DM 1 g + coneRem Q₀ Φh DM s g))) ∂muTam Q₀ hQ 1 :=
          lintegral_mono fun g => by
            have h1 := dualRem_le_adelicInner (Q₀ := Q₀) hΦh hDM hs.le g
            have h2 := hiInner_le (Q₀ := Q₀) (Φ := Φ) (DM := DM) hs1 g
            calc _ = Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s)) +
                  (dualRem Q₀ Φh DM s g + (hiInner Q₀ Φ DM s g + coneRem Q₀ Φh DM s g)) := by ring
              _ ≤ _ := by gcongr
      _ = V * (Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s))) +
          (adelicZetaPlus Q₀ hQ Φh D DM 1 + (adelicZetaPlus Q₀ hQ Φ D DM 1 + coneC2 Q₀ hQ Φh D DM s)) := by
          rw [lintegral_add_left measurable_const, setLIntegral_const, lintegral_add_left hmeasH,
            lintegral_add_left (hmeas 1), mul_comm]
          rfl
      _ ≤ _ := by
          rw [hZh, ← add_assoc (adelicZetaPlus Q₀ hQ Φh D DM 1)]
          gcongr
          exact hC2 s hs hs1
  have hBr : ∀ s, 0 < s → (V * (Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s)))).toReal =
      V.toReal * (b * (dedekindZeta_residue F / (2 * s))) := fun s hs => by
    rw [hΦh0, ← ENNReal.ofReal_mul hb.le, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hAr : ∀ s, 0 < s →
      (V * (Φ 0 * ENNReal.ofReal (dedekindZeta_residue F / (n + 2 * s)))).toReal =
      V.toReal * (a * (dedekindZeta_residue F / (n + 2 * s))) := fun s hs => by
    rw [hΦ0, ← ENNReal.ofReal_mul ha, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hBt : ∀ s, V * (Φh 0 * ENNReal.ofReal (dedekindZeta_residue F / (2 * s))) ≠ ⊤ := fun s => by
    rw [hΦh0]; exact ENNReal.mul_ne_top hDfin (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have hAt : ∀ s, V * (Φ 0 * ENNReal.ofReal (dedekindZeta_residue F / (n + 2 * s))) ≠ ⊤ := fun s => by
    rw [hΦ0]; exact ENNReal.mul_ne_top hDfin (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have hZKt : Zh + K ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hC, hK⟩
  have hZt : ∀ s, 0 < s → s ≤ 1 → adelicZetaPlus Q₀ hQ Φ D DM s ≠ ⊤ := fun s hs hs1 =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hBt s, hZKt⟩) (hup s hs hs1)
  have hupR : ∀ s, 0 < s → s ≤ 1 → s * (adelicZetaPlus Q₀ hQ Φ D DM s).toReal ≤
      V.toReal * (dedekindZeta_residue F * b) / 2 + s * (Zh + K).toReal := fun s hs hs1 => by
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hBt s, hZKt⟩) (hup s hs hs1)
    rw [ENNReal.toReal_add (hBt s) hZKt, hBr s hs] at h
    calc s * (adelicZetaPlus Q₀ hQ Φ D DM s).toReal ≤ s * (V.toReal *
          (b * (dedekindZeta_residue F / (2 * s))) + (Zh + K).toReal) := by gcongr
      _ = _ := by field_simp
  have hlowR : ∀ s, 0 < s → s ≤ 1 → V.toReal * (dedekindZeta_residue F * b) / 2 -
      s * (V.toReal * (a * (dedekindZeta_residue F / (n + 2 * s)))) - s * K.toReal ≤
        s * (adelicZetaPlus Q₀ hQ Φ D DM s).toReal := fun s hs hs1 => by
    have hZK : adelicZetaPlus Q₀ hQ Φ D DM s + K ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hZt s hs hs1, hK⟩
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hZK, hAt s⟩) (hlow s hs hs1)
    rw [ENNReal.toReal_add hZK (hAt s), ENNReal.toReal_add (hZt s hs hs1) hK, hBr s hs, hAr s hs] at h
    have e : V.toReal * (dedekindZeta_residue F * b) / 2 =
        s * (V.toReal * (b * (dedekindZeta_residue F / (2 * s)))) := by field_simp
    rw [e, sub_sub, ← mul_add, ← mul_sub]
    gcongr
    linarith
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s ≤ 1 :=
    Filter.eventually_of_mem (Ioc_mem_nhdsGT zero_lt_one) fun s hs => ⟨hs.1, hs.2⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlowT : Tendsto (fun s : ℝ => V.toReal * (dedekindZeta_residue F * b) / 2 -
      s * (V.toReal * (a * (dedekindZeta_residue F / (n + 2 * s)))) - s * K.toReal) (𝓝[>] 0)
      (𝓝 (V.toReal * (dedekindZeta_residue F * b) / 2)) := by
    have hc : ContinuousAt (fun s : ℝ => V.toReal * (dedekindZeta_residue F * b) / 2 -
        s * (V.toReal * (a * (dedekindZeta_residue F / (n + 2 * s)))) - s * K.toReal) 0 := by
      refine (continuousAt_const.sub (continuousAt_id.mul (continuousAt_const.mul (continuousAt_const.mul
        (continuousAt_const.div (continuousAt_const.add (continuousAt_const.mul continuousAt_id)) ?_))))).sub
        (continuousAt_id.mul continuousAt_const)
      show (n : ℝ) + 2 * 0 ≠ 0
      rw [mul_zero, add_zero]; exact hnpos.ne'
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have hupT : Tendsto (fun s : ℝ => V.toReal * (dedekindZeta_residue F * b) / 2 + s * (Zh + K).toReal)
      (𝓝[>] 0) (𝓝 (V.toReal * (dedekindZeta_residue F * b) / 2)) := by
    have hc : ContinuousAt (fun s : ℝ => V.toReal * (dedekindZeta_residue F * b) / 2 +
        s * (Zh + K).toReal) 0 := by fun_prop
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowT hupT
    (hev.mono fun s hs => hlowR s hs.1 hs.2) (hev.mono fun s hs => hupR s hs.1 hs.2)

end Global

end QuadFormsKB.Tamagawa.Measure.Weil
