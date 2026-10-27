import QuadFormsKB.Tamagawa.SphericalUnfold
import QuadFormsKB.Tamagawa.TauTwo
import QuadFormsKB.HilbertModular.SteinitzGenus

/-!
# Weil's fibration over the spheres, reduced to the orbital Euler product

**Setting** (the scope). $F$ totally real, $Q_0$ nondegenerate over $\mathcal O_F$ in $n \ge 1$ variables, $Q_0\otimes F$ totally
positive definite, $L = \mathcal O_F^n$, the genus of $L$ free (`GenusFree`; automatic for $\mathcal O_F$ a PID), $M_c$ the classes of the
genus with Gram forms $A_c$ (`classForm`), $\mu = \mu_{\mathrm{Tam}}(K_{SO})$ (`tamagawaK`), $\Phi_w = e^{-\pi Q_w}$.

**The target.** the input `SphericalFibration Q₀ (sphFamily Q₀) τ'`: $Z^+(s) = \sum_\rho\frac{\tau'_\rho}2Z(s,\rho)$ for $s > 0$
(Weil 1982, §4.5, p. 109).

**What is proved here.** Combining the $\rho$-wise unfolding of $Z^+$ (`SphericalUnfold.additiveZeta_eq_tsum_sqClasses`), the
archimedean Mellin integral (`archMellin_eq`) and the archimedean spherical factor (`sphArchAt_gaussian`):
`SphericalFibration` **follows from the orbital Euler product** (`sphericalFibration_of_orbitalEulerProduct`), the identity, for
every totally positive representative $\rho$ of a square class and $s > 0$,
$$2\mu\sum_{\mathfrak b}N\mathfrak b^{-n-2s}\sum_{\mathrm{cls}M}\frac{\#\{\eta\in\mathfrak b^{-1}M : Q(\eta) = \rho\}}{|O(M)|}
  = \tau'_\rho\,|d_F|^{-\frac{n-1}2}\prod_w\frac{2\pi^{n/2}\sigma_w(\rho)^{\frac n2+s}}{\Gamma(\frac n2)\sqrt{\det A_w}}\prod_vZ_\mathfrak p(s,\rho)
  \qquad(\texttt{OrbitalEulerProduct}),$$
$Z_\mathfrak p(s,\rho)$ = `sphLocal`. Consequently $\tau(SO(V)) = 2$ given `OrbitalEulerProduct` and `ComplementTauTwo`
(`tamagawaNumberTwo_of_orbitalEulerProduct`).

**Status of `OrbitalEulerProduct`.** It is Siegel's theorem for the numbers $\rho b^2$, with the constant $\tau'_\rho$ in place of
$\tau(G)$, summed against $N\mathfrak b^{-n-2s}$: the combinatorial heart of Weil's p. 109. It is recorded as an `interface` (the target of
the remaining work), **not** as an acceptable input: it is not formally equivalent to
$\tau(SO(V)) = 2$, but it carries the content of the induction step. Its proof reduces (docs) to `repMass_eq_mass_mul` for the
lattice $\mathfrak b^{-1}L$ in coordinates adapted to $\langle\rho\rangle\perp\xi_\rho^\perp$, the stabilizer's $\tau'_\rho = \tau(SO(\xi_\rho^\perp))$, the
factorization of the type sum over the primes, local orbital identities, the local spherical factor
$Z_\mathfrak p(s,\rho) = |2|_v\sum_j|\rho\pi^{2j}|_v^{1+s}\beta_v(\rho\pi^{2j})$, and the Euler product over the ideals $\mathfrak b$.
-/

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Set Filter Topology
open scoped Real ENNReal nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SphericalFibration

open QuadFormsKB.Lattices QuadFormsKB.HilbertModular QuadFormsKB.IdeleClass QuadFormsKB.AdditiveZeta
open QuadFormsKB.SphericalZeta QuadFormsKB.SphericalUnfold QuadFormsKB.GlobalZeta QuadFormsKB.TauTwo

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-- **The orbital Dirichlet series of the genus** at the square class $k$ ($\rho = \rho_k$ = `rep k`), in $[0,\infty]$:
$$D_k(s) = \sum_{\mathfrak b}N\mathfrak b^{-n-2s}\sum_{\mathrm{cls}M\subseteq\mathrm{gen}L}\frac{\#\{\eta\in\mathfrak b^{-1}M : Q(\eta) = \rho\}}{|O(M)|},$$
$\mathfrak b$ over all fractional ideals, $M$ over the classes of the genus of $\mathcal O_F^n$ with their Gram forms (`classForm`),
$|O(M)|$ = `LatClass.autCard`. -/
def orbitalSeries (Q₀ : QuadForm (𝓞 F) n) (s : ℝ) (k : SqClasses F) : ℝ≥0∞ :=
  ∑' 𝔟 : FracIdeal F, ENNReal.ofReal (idealNorm F 𝔟 ^ (-((n : ℝ) + 2 * s))) *
    ∑ᶠ c ∈ genusClasses (formF Q₀) stdLat,
      sphereCount (gramF (classForm Q₀ c)) (fun _ => 1) (rep k) 𝔟 *
        ENNReal.ofReal ((LatClass.autCard (formF Q₀) c : ℝ))⁻¹

/-- **The archimedean constant of the orbital Euler product** at a real place $w$:
$2\pi^{n/2}\sigma_w(\rho)^{\frac n2+s}/(\Gamma(\frac n2)\sqrt{\det A_w})$, $A_w = \varphi_w(H/2)$. -/
def orbitalArch (Q₀ : QuadForm (𝓞 F) n) (s : ℝ) (ρ : F) (w : Siegel.RealPlace F) : ℝ :=
  2 * π ^ ((n : ℝ) / 2) * (realEmb F w.1 ρ) ^ ((n : ℝ) / 2 + s) / Real.Gamma ((n : ℝ) / 2) *
    (Real.sqrt ((gramF Q₀).map (realEmb F w.1)).det)⁻¹

open Classical in
/-- **Interface: the orbital Euler product** (Weil 1982, §4.5, p. 109, in combinatorial form; Siegel's theorem for the numbers
$\rho b^2$ with the constant $\tau'_\rho$, summed over $\mathfrak b$). For every square class $k$ whose representative $\rho = \rho_k$ is totally
positive and every $s > 0$:
$$2\mu\,D_k(s) = \tau'_k\,|d_F|^{-\frac{n-1}2}\prod_w\frac{2\pi^{n/2}\sigma_w(\rho)^{\frac n2+s}}{\Gamma(\frac n2)\sqrt{\det A_w}}\prod_vZ_\mathfrak p(s,\rho),$$
$\mu$ = `tamagawaK Q₀`, $D_k$ = `orbitalSeries`, $Z_\mathfrak p$ = `sphLocal` (`tprod` over the finite places), Field: `euler`. *Classification:* `interface` — the remaining combinatorial-local core of the
induction step; it does not mention $\tau(SO(V))$, but it is not regarded as an acceptable input (see the module docstring). -/
@[kb "weil1982" "§4.5, p. 109 (unfolding over T(ρ) via Lemma 2.4.2); Siegel's theorem for the numbers ρb² [interface]"]
structure OrbitalEulerProduct (Q₀ : QuadForm (𝓞 F) n) (τ' : SqClasses F → ℝ) : Prop where
  /-- The Euler product identity. -/
  euler : ∀ k s, 0 < s → (∀ v : InfinitePlace F, 0 < realEmb F v (rep k)) →
    2 * Tamagawa.tamagawaK Q₀ * (orbitalSeries Q₀ s k).toReal =
      τ' k * |(NumberField.discr F : ℝ)| ^ (-((n : ℝ) - 1) / 2) * (∏ w, orbitalArch Q₀ s (rep k) w) *
        ∏' v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
          sphLocal Q₀ v (algebraMap F (v.adicCompletion F) (rep k)) s

/-! ### The genus sum of the unfolded zeta functions -/

/-- The term of the square class $k$: $T_k(s) = \frac12|d_F|^{-1/2}I_{\rho_k}(s)D_k(s)$. -/
def sphTerm (Q₀ : QuadForm (𝓞 F) n) (s : ℝ) (k : SqClasses F) : ℝ≥0∞ :=
  2⁻¹ * ENNReal.ofReal (ideleConst F) * archMellin n s (rep k) * orbitalSeries Q₀ s k

/-- **The genus sum, unfolded** (in $[0,\infty]$): $\sum_{\mathrm{cls}M}Z^+_M(s)/|O(M)| = \sum_kT_k(s)$. -/
theorem sum_additiveZeta_eq_tsum_sphTerm (Q₀ : QuadForm (𝓞 F) n) (hpd : IsTotallyPosDef (formF Q₀))
    (hfree : GenusFree (formF Q₀) stdLat) (s : ℝ) :
    ∑ c ∈ (genusClasses_finite hpd stdLat (isIntegral_stdLat Q₀)).toFinset,
      additiveZeta (gramF (classForm Q₀ c)) (fun _ => 1) s *
        ENNReal.ofReal ((LatClass.autCard (formF Q₀) c : ℝ))⁻¹ = ∑' k, sphTerm Q₀ s k := by
  set C := (genusClasses_finite hpd stdLat (isIntegral_stdLat Q₀)).toFinset
  have h1 : ∀ c ∈ C, additiveZeta (gramF (classForm Q₀ c)) (fun _ => 1) s *
      ENNReal.ofReal ((LatClass.autCard (formF Q₀) c : ℝ))⁻¹ =
      ∑' k : SqClasses F, 2⁻¹ * ENNReal.ofReal (ideleConst F) * archMellin n s (rep k) *
        ∑' 𝔟 : FracIdeal F, ENNReal.ofReal (idealNorm F 𝔟 ^ (-((n : ℝ) + 2 * s))) *
          (sphereCount (gramF (classForm Q₀ c)) (fun _ => 1) (rep k) 𝔟 *
            ENNReal.ofReal ((LatClass.autCard (formF Q₀) c : ℝ))⁻¹) := by
    intro c hc
    have hcg : c ∈ genusClasses (formF Q₀) stdLat := (genusClasses_finite hpd stdLat (isIntegral_stdLat Q₀)).mem_toFinset.1 hc
    rw [additiveZeta_eq_tsum_sqClasses (classForm_props Q₀ hpd hfree hcg).2, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun k => ?_
    rw [mul_assoc, ← ENNReal.tsum_mul_right]
    congr 1
    refine tsum_congr fun 𝔟 => ?_
    ring
  rw [Finset.sum_congr rfl h1, ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine tsum_congr fun k => ?_
  rw [← Finset.mul_sum, sphTerm, orbitalSeries]
  congr 1
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine tsum_congr fun 𝔟 => ?_
  rw [← Finset.mul_sum, finsum_mem_eq_finite_toFinset_sum _
    (genusClasses_finite hpd stdLat (isIntegral_stdLat Q₀))]

/-! ### Square classes that are not totally positive contribute nothing -/

lemma realEmb_siegel (w : Siegel.RealPlace F) (x : F) : Siegel.realEmb w x = realEmb F w.1 x := rfl

/-- No vector of a totally positive form has a value that is not totally positive: $\#\{Q(\eta) = \rho\} = 0$. -/
lemma sphereCount_eq_zero {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A) (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    {ρ : F} (hρ0 : ρ ≠ 0) {v : InfinitePlace F} (hv : realEmb F v ρ ≤ 0) (𝔟 : FracIdeal F) :
    sphereCount A J ρ 𝔟 = 0 := by
  classical
  unfold sphereCount
  refine ENNReal.tsum_eq_zero.mpr fun η => ?_
  rw [if_neg]
  rintro ⟨hη, -⟩
  by_cases h0 : η = 0
  · subst h0
    simp [qv] at hη
    exact hρ0 hη.symm
  · have := realEmb_qv_pos hA v h0
    rw [hη] at this
    linarith

lemma orbitalSeries_eq_zero (Q₀ : QuadForm (𝓞 F) n) (hpd : IsTotallyPosDef (formF Q₀))
    (hfree : GenusFree (formF Q₀) stdLat) (s : ℝ) {k : SqClasses F} {v : InfinitePlace F}
    (hv : realEmb F v (rep k) ≤ 0) : orbitalSeries Q₀ s k = 0 := by
  unfold orbitalSeries
  refine ENNReal.tsum_eq_zero.mpr fun 𝔟 => ?_
  rw [finsum_mem_eq_finite_toFinset_sum _ (genusClasses_finite hpd stdLat (isIntegral_stdLat Q₀))]
  rw [Finset.sum_eq_zero fun c hc => ?_, mul_zero]
  have hcg : c ∈ genusClasses (formF Q₀) stdLat :=
    (genusClasses_finite hpd stdLat (isIntegral_stdLat Q₀)).mem_toFinset.1 hc
  rw [sphereCount_eq_zero (classForm_props Q₀ hpd hfree hcg).2 _ (rep_ne_zero k) hv, zero_mul]

/-- $Z_w(s,r) = 0$ for $r < 0$: a positive definite $Q_w$ takes no value in $r\mathbb R^{\times2}$. -/
lemma sphArchAt_eq_zero_of_neg (Q₀ : QuadForm (𝓞 F) n) (hpd : IsTotallyPosDef (formF Q₀))
    (w : Siegel.RealPlace F) (φ : (Fin n → ℝ) → ℝ) {r : ℝ} (hr : r < 0) (s : ℝ) :
    sphArchAt Q₀ w φ r s = 0 := by
  have hempty : realVal Q₀ w ⁻¹' sqClass r = ∅ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    rintro ⟨y, hy, hxy⟩
    have h1 : 0 ≤ realVal Q₀ w x := by
      by_cases hx : x = 0
      · subst hx; simp [realVal_eq_dotProduct]
      · exact (globalZeta_isTotallyPosDef Q₀ hpd w x hx).le
    have h2 : r * y ^ 2 < 0 := mul_neg_of_neg_of_pos hr (by positivity)
    linarith
  unfold sphArchAt
  rw [hempty, Measure.restrict_empty, integral_zero_measure, mul_zero]

lemma sphFamily_eq_zero (Q₀ : QuadForm (𝓞 F) n) (hpd : IsTotallyPosDef (formF Q₀)) {k : SqClasses F}
    {v : InfinitePlace F} (hv : realEmb F v (rep k) ≤ 0) (s : ℝ) : sphFamily Q₀ k s = 0 := by
  classical
  have hlt : realEmb F v (rep k) < 0 :=
    lt_of_le_of_ne hv fun h => rep_ne_zero k ((realEmb F v).injective (h.trans (map_zero _).symm))
  unfold sphFamily sphericalZetaAt
  rw [Finset.prod_eq_zero (Finset.mem_univ (⟨v, IsTotallyReal.isReal v⟩ : Siegel.RealPlace F))
    (sphArchAt_eq_zero_of_neg Q₀ hpd _ _ (by rw [realEmb_siegel]; exact hlt) s)]
  simp

/-! ### The term of a totally positive square class -/

lemma ideleConst_eq : ideleConst F = |(NumberField.discr F : ℝ)| ^ (-(1 / 2 : ℝ)) := by
  rw [ideleConst, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, mul_one]

/-- The archimedean bookkeeping at one real place: $(\pi\sigma)^{-\frac n2-s}\Gamma(\frac n2+s)\cdot\frac{2\pi^{n/2}\sigma^{\frac n2+s}}{\Gamma(\frac n2)\sqrt{\det}}
= \frac{2\pi^{-s}\Gamma(\frac n2+s)}{\Gamma(\frac n2)\sqrt{\det}}$. -/
lemma arch_place_identity {σ s : ℝ} (hσ : 0 < σ) (G D : ℝ) :
    (π * σ) ^ (-((n : ℝ) + 2 * s) / 2) * Real.Gamma (((n : ℝ) + 2 * s) / 2) *
      (2 * π ^ ((n : ℝ) / 2) * σ ^ ((n : ℝ) / 2 + s) / G * D) =
    2 * (π ^ (-s) * Real.Gamma ((n : ℝ) / 2 + s) / G) * D := by
  have he : -((n : ℝ) + 2 * s) / 2 = -((n : ℝ) / 2 + s) := by ring
  have he2 : ((n : ℝ) + 2 * s) / 2 = (n : ℝ) / 2 + s := by ring
  rw [he, he2, Real.mul_rpow Real.pi_pos.le hσ.le]
  have h1 : σ ^ (-((n : ℝ) / 2 + s)) * σ ^ ((n : ℝ) / 2 + s) = 1 := by
    rw [← Real.rpow_add hσ, neg_add_cancel, Real.rpow_zero]
  have h2 : π ^ (-((n : ℝ) / 2 + s)) * π ^ ((n : ℝ) / 2) = π ^ (-s) := by
    rw [← Real.rpow_add Real.pi_pos]; ring_nf
  calc π ^ (-((n : ℝ) / 2 + s)) * σ ^ (-((n : ℝ) / 2 + s)) * Real.Gamma ((n : ℝ) / 2 + s) *
        (2 * π ^ ((n : ℝ) / 2) * σ ^ ((n : ℝ) / 2 + s) / G * D)
      = 2 * ((π ^ (-((n : ℝ) / 2 + s)) * π ^ ((n : ℝ) / 2)) *
          (σ ^ (-((n : ℝ) / 2 + s)) * σ ^ ((n : ℝ) / 2 + s)) * Real.Gamma ((n : ℝ) / 2 + s) / G) * D := by ring
    _ = _ := by rw [h1, h2, mul_one]

open Classical in
/-- **One square class**: if $\rho_k$ is totally positive and $T_k(s) < \infty$, the orbital Euler product gives
$2\mu\,T_k(s) = \frac{\tau'_k}2Z(s,\rho_k)$ (with the normalizations of $Z(s,\rho)$). -/
theorem two_mul_sphTerm_eq (Q₀ : QuadForm (𝓞 F) n) (hpd : IsTotallyPosDef (formF Q₀)) (hn : 1 ≤ n)
    {τ' : SqClasses F → ℝ} (h : OrbitalEulerProduct Q₀ τ') {s : ℝ} (hs : 0 < s) (k : SqClasses F)
    (hpos : ∀ v : InfinitePlace F, 0 < realEmb F v (rep k)) (hfin : sphTerm Q₀ s k ≠ ⊤) :
    2 * Tamagawa.tamagawaK Q₀ * (sphTerm Q₀ s k).toReal = τ' k / 2 * sphFamily Q₀ k s := by
  have ha : 1 < (n : ℝ) + 2 * s := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set ρ := rep k
  set D := |(NumberField.discr F : ℝ)|
  have hD : 0 < D := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F)
  set X : InfinitePlace F → ℝ := fun v =>
    (π * realEmb F v ρ) ^ (-((n : ℝ) + 2 * s) / 2) * Real.Gamma (((n : ℝ) + 2 * s) / 2)
  have hX : ∀ v, 0 ≤ X v := fun v => mul_nonneg (Real.rpow_nonneg (mul_pos Real.pi_pos (hpos v)).le _)
    (Real.Gamma_nonneg_of_nonneg (by positivity))
  have hM : (archMellin n s ρ).toReal = ∏ v, X v := by
    rw [archMellin_eq hpos ha, ENNReal.toReal_prod]
    exact Finset.prod_congr rfl fun v _ => ENNReal.toReal_ofReal (hX v)
  have hterm : (sphTerm Q₀ s k).toReal = 2⁻¹ * ideleConst F * (∏ v, X v) * (orbitalSeries Q₀ s k).toReal := by
    unfold sphTerm
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (by rw [ideleConst_eq]; positivity), hM]
  have heul := h.euler k s hs hpos
  set P := ∏' v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
    sphLocal Q₀ v (algebraMap F (v.adicCompletion F) ρ) s
  have eR : ∏ v : InfinitePlace F, X v = ∏ w : Siegel.RealPlace F, X w.1 :=
    (Fintype.prod_equiv (Equiv.subtypeUnivEquiv fun w => IsTotallyReal.isReal w).symm _ _ fun v => rfl)
  have hsph : sphFamily Q₀ k s = D ^ (-(n : ℝ) / 2) *
      (∏ w : Siegel.RealPlace F, 2 * (π ^ (-s) * Real.Gamma ((n : ℝ) / 2 + s) / Real.Gamma ((n : ℝ) / 2)) *
        (Real.sqrt ((gramF Q₀).map (realEmb F w.1)).det)⁻¹) * P := by
    unfold sphFamily sphericalZetaAt
    congr 2
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [realEmb_siegel]
    exact sphArchAt_gaussian Q₀ hpd hn w (hpos w.1) hs
  rw [hterm, hsph]
  have hprod : (∏ w : Siegel.RealPlace F, X w.1) * ∏ w, orbitalArch Q₀ s ρ w =
      ∏ w : Siegel.RealPlace F, 2 * (π ^ (-s) * Real.Gamma ((n : ℝ) / 2 + s) / Real.Gamma ((n : ℝ) / 2)) *
        (Real.sqrt ((gramF Q₀).map (realEmb F w.1)).det)⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    exact arch_place_identity (hpos w.1) _ _
  have hDD : D ^ (-(1 / 2 : ℝ)) * D ^ (-((n : ℝ) - 1) / 2) = D ^ (-(n : ℝ) / 2) := by
    rw [← Real.rpow_add hD]; ring_nf
  rw [← hprod, ← hDD, eR, ideleConst_eq]
  calc 2 * Tamagawa.tamagawaK Q₀ * (2⁻¹ * D ^ (-(1 / 2 : ℝ)) * (∏ w : Siegel.RealPlace F, X w.1) *
        (orbitalSeries Q₀ s k).toReal)
      = 2⁻¹ * D ^ (-(1 / 2 : ℝ)) * (∏ w : Siegel.RealPlace F, X w.1) *
          (2 * Tamagawa.tamagawaK Q₀ * (orbitalSeries Q₀ s k).toReal) := by ring
    _ = _ := by rw [heul]; ring

/-! ### Assembly: `SphericalFibration` from the orbital Euler product -/

lemma sphTerm_eq_zero (Q₀ : QuadForm (𝓞 F) n) (hpd : IsTotallyPosDef (formF Q₀))
    (hfree : GenusFree (formF Q₀) stdLat) (s : ℝ) {k : SqClasses F} {v : InfinitePlace F}
    (hv : realEmb F v (rep k) ≤ 0) : sphTerm Q₀ s k = 0 := by
  rw [sphTerm, orbitalSeries_eq_zero Q₀ hpd hfree s hv, mul_zero]

/-- **The genus additive zeta function as the sum of the class terms** ($s > 0$): $Z^+(s) = \sum_k2\mu\,T_k(s)$, the series of
nonnegative finite terms converging (`summable`), with $\sum_kT_k(s) < \infty$. -/
theorem genusAdditiveZeta_eq_tsum (Q₀ : QuadForm (𝓞 F) n) (hpd : IsTotallyPosDef (formF Q₀))
    (hfree : GenusFree (formF Q₀) stdLat) {s : ℝ} (hs : 0 < s) :
    (∑' k, sphTerm Q₀ s k) ≠ ⊤ ∧
      genusAdditiveZeta Q₀ s = 2 * Tamagawa.tamagawaK Q₀ * ∑' k, (sphTerm Q₀ s k).toReal := by
  have hfin := genusClasses_finite hpd stdLat (isIntegral_stdLat Q₀)
  set C := hfin.toFinset
  have hsum := sum_additiveZeta_eq_tsum_sphTerm Q₀ hpd hfree s
  have hne : ∀ c ∈ C, additiveZeta (gramF (classForm Q₀ c)) (fun _ => 1) s *
      ENNReal.ofReal ((LatClass.autCard (formF Q₀) c : ℝ))⁻¹ ≠ ⊤ := fun c hc =>
    ENNReal.mul_ne_top (additiveZeta_lt_top (classForm_props Q₀ hpd hfree (hfin.mem_toFinset.1 hc)).2 _ hs).ne
      ENNReal.ofReal_ne_top
  have htop : (∑' k, sphTerm Q₀ s k) ≠ ⊤ := by
    rw [← hsum]; exact (ENNReal.sum_ne_top).2 hne
  refine ⟨htop, ?_⟩
  rw [genusAdditiveZeta, finsum_mem_eq_finite_toFinset_sum _ hfin,
    ← ENNReal.tsum_toReal_eq (fun k => ENNReal.ne_top_of_tsum_ne_top htop k), ← hsum,
    ENNReal.toReal_sum hne]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 (Nat.cast_nonneg _)), div_eq_mul_inv]

/-- **Weil's fibration over the spheres from the orbital Euler product** (Weil 1982, §4.5, p. 109). For $Q_0$ nondegenerate
over $\mathcal O_F$, $n \ge 1$, $Q_0\otimes F$ totally positive definite, the genus of $\mathcal O_F^n$ free, and any $\tau'$:
`OrbitalEulerProduct Q₀ τ'` implies `SphericalFibration Q₀ (sphFamily Q₀) τ'`, i.e. for $s > 0$
$$Z^+(s) = \sum_{\rho\in F^\times/F^{\times2}}\frac{\tau'_\rho}2Z(s,\rho)$$
(summable), with exactly the $Z(s,\rho)$ for the Gaussian $\Phi_w = e^{-\pi Q_w}$ and the $Z^+$. Proved: the unfolding over the
spheres and $F^\times$ (`additiveZeta_eq_tsum_sqClasses`), the archimedean integrals (`archMellin_eq`, `sphArchAt_gaussian`), the
vanishing at the square classes that are not totally positive, and the constants ($|d_F|^{-1/2}|d_F|^{-(n-1)/2} = |d_F|^{-n/2}$). -/
@[kb "weil1982" "§4.5, p. 109 (Z(s) = Σ_ρ Z(s,ρ) via Lemma 2.4.2 on T(ρ)); (1)–(2), p. 102"]
theorem sphericalFibration_of_orbitalEulerProduct (Q₀ : QuadForm (𝓞 F) n) (hn : 1 ≤ n)
    (hpd : IsTotallyPosDef (formF Q₀)) (hfree : GenusFree (formF Q₀) stdLat) {τ' : SqClasses F → ℝ}
    (h : OrbitalEulerProduct Q₀ τ') : SphericalFibration Q₀ (sphFamily Q₀) τ' := by
  have hterm : ∀ s, 0 < s → ∀ k, 2 * Tamagawa.tamagawaK Q₀ * (sphTerm Q₀ s k).toReal =
      τ' k / 2 * sphFamily Q₀ k s := by
    intro s hs k
    obtain ⟨htop, -⟩ := genusAdditiveZeta_eq_tsum Q₀ hpd hfree hs
    by_cases hpos : ∀ v : InfinitePlace F, 0 < realEmb F v (rep k)
    · exact two_mul_sphTerm_eq Q₀ hpd hn h hs k hpos (ENNReal.ne_top_of_tsum_ne_top htop k)
    · push_neg at hpos
      obtain ⟨v, hv⟩ := hpos
      rw [sphTerm_eq_zero Q₀ hpd hfree s hv, sphFamily_eq_zero Q₀ hpd hv]
      simp
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · obtain ⟨htop, -⟩ := genusAdditiveZeta_eq_tsum Q₀ hpd hfree hs
    exact ((ENNReal.summable_toReal htop).mul_left (2 * Tamagawa.tamagawaK Q₀)).congr (hterm s hs)
  · obtain ⟨-, heq⟩ := genusAdditiveZeta_eq_tsum Q₀ hpd hfree hs
    rw [heq, ← tsum_mul_left]
    exact tsum_congr (hterm s hs)

/-- **Weil's Theorem 4.5.1 from the orbital Euler product**: for $n \ge 5$, `OrbitalEulerProduct Q₀ τ'` and `ComplementTauTwo τ'`
give $\tau(SO(V)) = 2$ (the comparison of residues, `tamagawaNumberTwo_of_sphericalFibration`). -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109"]
theorem tamagawaNumberTwo_of_orbitalEulerProduct (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hn : 5 ≤ n)
    (hpd : IsTotallyPosDef (formF Q₀)) (hfree : GenusFree (formF Q₀) stdLat) {τ' : SqClasses F → ℝ}
    (h : OrbitalEulerProduct Q₀ τ') (htwo : ComplementTauTwo τ') : Tamagawa.TamagawaNumberTwo Q₀ :=
  tamagawaNumberTwo_of_sphericalFibration Q₀ hQ hn hpd hfree
    (sphericalFibration_of_orbitalEulerProduct Q₀ (by omega) hpd hfree h) htwo

/-! ### Without the scope hypothesis (Steinitz: the genus of $\mathcal O_F^n$ is free for every $F$) -/

/-- **For every totally real $F$**: `tamagawaNumberTwo_of_sphericalFibration` with `GenusFree` discharged by Steinitz
(`genusFree_formF`, any class number). For $n \ge 5$: `SphericalFibration` and `ComplementTauTwo` give $\tau(SO(V)) = 2$. -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109"]
theorem tamagawaNumberTwo_of_sphericalFibration' (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hn : 5 ≤ n)
    (hpd : IsTotallyPosDef (formF Q₀)) {τ' : SqClasses F → ℝ}
    (hfib : SphericalFibration Q₀ (sphFamily Q₀) τ') (htwo : ComplementTauTwo τ') :
    Tamagawa.TamagawaNumberTwo Q₀ :=
  tamagawaNumberTwo_of_sphericalFibration Q₀ hQ hn hpd (genusFree_formF hpd) hfib htwo

/-- **Weil's Theorem 4.5.1 from the orbital Euler product, every totally real $F$** ($n \ge 5$): `OrbitalEulerProduct Q₀ τ'` and
`ComplementTauTwo τ'` give $\tau(SO(V)) = 2$; hence the mass formula $\mathrm{Mass}(\mathcal O_F^n) = \mu_{\mathrm{Tam}}(K_{SO})^{-1}$
(`massFormula_of_orbitalEulerProduct`). -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109"]
theorem tamagawaNumberTwo_of_orbitalEulerProduct' (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hn : 5 ≤ n)
    (hpd : IsTotallyPosDef (formF Q₀)) {τ' : SqClasses F → ℝ}
    (h : OrbitalEulerProduct Q₀ τ') (htwo : ComplementTauTwo τ') : Tamagawa.TamagawaNumberTwo Q₀ :=
  tamagawaNumberTwo_of_orbitalEulerProduct Q₀ hQ hn hpd (genusFree_formF hpd) h htwo

/-- **The mass formula in rank $n \ge 5$ from the orbital Euler product** (`massFormula`). -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109; cf. Kitaoka 1993, Thm 6.8.1 [unverified]"]
theorem massFormula_of_orbitalEulerProduct (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hn : 5 ≤ n)
    (hpd : IsTotallyPosDef (formF Q₀)) {τ' : SqClasses F → ℝ}
    (h : OrbitalEulerProduct Q₀ τ') (htwo : ComplementTauTwo τ') :
    mass (formF Q₀) (Tamagawa.stdLat F n) = (Tamagawa.tamagawaK Q₀)⁻¹ :=
  Tamagawa.massFormula Q₀ hQ (by omega) hpd (isIntegral_stdLat Q₀)
    (tamagawaNumberTwo_of_orbitalEulerProduct' Q₀ hQ hn hpd h htwo)

end QuadFormsKB.SphericalFibration
