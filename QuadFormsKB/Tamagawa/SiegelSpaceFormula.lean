/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.SiegelSpace

/-!
# Siegel's formula for a quadratic space over a totally real field, without $\mathcal O_F$-coordinates

**Layer:** $F$ a totally real number field (any class number); $V = F^N$ with an **arbitrary** totally positive definite quadratic
form $Q$ over $F$ (`QuadForm F N`, coefficients in $F$); $L$ any $\mathcal O_F$-lattice on $V$ (any Steinitz class) with $Q$ integral
on $L$; $m \in \mathcal O_F$ totally positive.

**Proves** (unconditional; every term attached to $(Q, L)$ — `mass`, `repMass`, and SiegelSpace's `spaceBeta`, `detGramF`,
`sqChar`-characters, $|d_F|$ — none to a choice of coordinates over $\mathcal O_F$):
* **`siegelFormula_space_totallyReal`** ($N \ge 4$): $\mathrm{repMass}(Q, L, m) = \mathrm{Mass}(Q, L)\cdot S(Q, L, m)$.
* **`siegelFormula3_space_totallyReal`** ($N = 3$, regularized with $\chi_m$ of $F(\sqrt{-2m\det H_Q})/F$).
* **`siegelFormula2_space_totallyReal`** ($N = 2$, $\varepsilon = \tfrac12$, regularized with $\chi_Q$ of $F(\sqrt{-\det H_Q})/F$).
* **`siegelFormula1_space_totallyReal`** ($N = 1$): $\mathrm{repMass} = \mathrm{Mass}\cdot 2\,\mathcal S_1$.
* Natural order (given `NaturalOrderEulerOne` of the character): `siegelFormula3_space_natural`, `siegelFormula2_space_natural`.
* **Basis independence** (`siegelProductSpace_compMat`, `siegelProduct3Space_compMat`, `siegelProduct2RegSpace_compMat`,
  `siegelProductOneSpace_compMat`; with `repMass_compMat`, `mass_similar`): every term is unchanged under
  $(Q, L) \mapsto (Q\circ g, g^{-1}L)$, $g \in \mathrm{GL}_N(F)$. So each statement is a statement about the quadratic space
  $(V, Q)$ and the lattice $L$, for any choice of $F$-basis of $V$.

**Route.** `exists_coords_of_isIntegral` gives $\gamma \in \mathrm{GL}_N(F)$ and $Q_0$ over $\mathcal O_F$ with $Q\circ\gamma = Q_0$; G's
headlines for $(Q_0, \gamma^{-1}L)$, `repMass_compMat`, `mass_similar`, and SiegelSpace's comparison
$S(Q, L) = S(Q_0, \gamma^{-1}L)$ (product formula for $\det\gamma$; the characters agree off finitely many primes, which the regularized
product does not see, `regProd_congr_finite`).

**Scope.** The ambient space is $F^N$ with an arbitrary form over $F$: abstract $(V, q)$ (Mathlib's `QuadraticForm F V`) would need
genus, class and mass objects for lattices in $V$, which the repository defines on $F^N$ only; the basis-independence theorems
are what makes the transfer along any $V \cong F^N$ automatic.

Source: Siegel 1935, Hauptsatz; Siegel 1937 (over number fields); Weil 1982, §4.5 [unverified locators].
-/

open NumberField IsDedekindDomain Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.SiegelSpace

open Matrix
open QuadFormsKB.Lattices QuadFormsKB.LocalDensity QuadFormsKB.QuadForm QuadFormsKB.HilbertModular QuadFormsKB.NFEuler
open QuadFormsKB.RegProd QuadFormsKB.Tamagawa.SiegelLat LatChange

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem lat_image_mul {N : ℕ} (a b : GL (Fin N) F) (L : Lat F N) :
    Lat.image (a * b) L = Lat.image a (Lat.image b L) :=
  Subtype.ext (glImage_mul a b L.1)

theorem lat_image_image_inv {N : ℕ} (γ : GL (Fin N) F) (L : Lat F N) : Lat.image γ (Lat.image γ⁻¹ L) = L := by
  rw [← lat_image_mul, mul_inv_cancel]
  exact Subtype.ext (glImage_one L.1)

/-- **The genus side in coordinates:** $\mathrm{repMass}$ and $\mathrm{Mass}$ of $(Q, L)$ are those of $(Q_0, \gamma^{-1}L)$. -/
theorem repMass_mass_coords {N : ℕ} (Q : QuadForm F N) (hpd : IsTotallyPosDef Q) (L : Lat F N)
    (hLi : Lattices.IsIntegral Q L.1) (γ : GL (Fin N) F) (Q₀ : QuadForm (𝓞 F) N) (hγ : formF Q₀ = Q.compMat γ.val)
    (t : F) :
    repMass Q L t = repMass (formF Q₀) (Lat.image γ⁻¹ L) t ∧ mass Q L = mass (formF Q₀) (Lat.image γ⁻¹ L) := by
  refine ⟨by rw [hγ, repMass_compMat Q γ hpd hLi], ?_⟩
  have h1 : (1 : F) • Q.compMat γ.val = Q.compMat γ.val := by ext i j; simp
  rw [hγ, ← h1, mass_similar Q one_ne_zero γ, lat_image_image_inv]

/-- Coordinates for $(Q, L)$, with $Q_0$ totally positive definite and integral on $\gamma^{-1}L$. -/
theorem exists_coords {n : ℕ} (Q : QuadForm F (n + 1)) (hpd : IsTotallyPosDef Q) (L : Lat F (n + 1))
    (hLi : Lattices.IsIntegral Q L.1) :
    ∃ (γ : GL (Fin (n + 1)) F) (Q₀ : QuadForm (𝓞 F) (n + 1)), formF Q₀ = Q.compMat γ.val ∧
      IsTotallyPosDef (formF Q₀) ∧ Lattices.IsIntegral (formF Q₀) (Lat.image γ⁻¹ L).1 := by
  obtain ⟨γ, Q₀, hγ, -, -, hLi'⟩ := exists_coords_of_isIntegral Q L hLi
  exact ⟨γ, Q₀, hγ, by rw [hγ]; exact isTotallyPosDef_compMat Q γ hpd, hLi'⟩

/-! ### The headlines -/

/-- **Siegel's formula for a quadratic space over a totally real field, $N \ge 4$** (unconditional; Siegel 1935, Hauptsatz; over
$F$: Siegel 1937 [unverified]): for every totally positive definite quadratic form $Q$ over $F$ in $N \ge 4$ variables, every
$\mathcal O_F$-lattice $L$ on $(F^N, Q)$ with $Q$ integral on $L$ and every totally positive $m \in \mathcal O_F$,
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(m)}{|O(M)|} = \mathrm{Mass}(L)\cdot|d_F|^{-\frac{N-1}2}\prod_\sigma\beta_\sigma(Q;m)
\prod_\mathfrak p\beta_\mathfrak p(L, m).$$ -/
@[kb "siegel1935" "Hauptsatz, quadratic space over a totally real field, every genus [unverified for F]"]
theorem siegelFormula_space_totallyReal {N : ℕ} (hN : 4 ≤ N) (Q : QuadForm F N) (hpd : IsTotallyPosDef Q) (L : Lat F N)
    (hLi : Lattices.IsIntegral Q L.1) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMass Q L (algebraMap (𝓞 F) F m) = mass Q L * siegelProductSpace Q L m := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  obtain ⟨γ, Q₀, hγ, hpd₀, hLi'⟩ := exists_coords Q hpd L hLi
  obtain ⟨h1, h2⟩ := repMass_mass_coords Q hpd L hLi γ Q₀ hγ (algebraMap (𝓞 F) F m)
  rw [h1, h2, siegelProductSpace_eq Q L hLi γ Q₀ hγ (by omega) hpd₀ hm]
  exact (siegelFormulaAtLat_totallyReal hN Q₀ hpd₀ _ hLi' hm).repMass_eq

/-- **Siegel's formula for a ternary quadratic space over a totally real field** (unconditional; regularized product with
$\chi_m$): $\mathrm{repMass}(Q, L, m) = \mathrm{Mass}(Q, L)\cdot S_3(Q, L, m)$. -/
@[kb "siegel1935" "Hauptsatz, n = 3, quadratic space over a totally real field, every genus [unverified for F]"]
theorem siegelFormula3_space_totallyReal (Q : QuadForm F 3) (hpd : IsTotallyPosDef Q) (L : Lat F 3)
    (hLi : Lattices.IsIntegral Q L.1) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMass Q L (algebraMap (𝓞 F) F m) = mass Q L * siegelProduct3Space Q L m := by
  obtain ⟨γ, Q₀, hγ, hpd₀, hLi'⟩ := exists_coords (n := 2) Q hpd L hLi
  obtain ⟨h1, h2⟩ := repMass_mass_coords Q hpd L hLi γ Q₀ hγ (algebraMap (𝓞 F) F m)
  rw [h1, h2, siegelProduct3Space_eq Q L hLi γ Q₀ hγ hpd₀ hm]
  exact (siegelFormulaAt3Lat_totallyReal Q₀ hpd₀ _ hLi' hm).repMass_eq

/-- **Siegel's formula for a binary quadratic space over a totally real field** (unconditional; $\varepsilon = \tfrac12$,
regularized product with $\chi_Q$): $\mathrm{repMass}(Q, L, m) = \tfrac12\,\mathrm{Mass}(Q, L)\cdot S^{\mathrm{reg}}_2(Q, L, m)$. -/
@[kb "siegel1935" "Hauptsatz, n = 2 (ε = 1/2), quadratic space over a totally real field, every genus [unverified for F]"]
theorem siegelFormula2_space_totallyReal (Q : QuadForm F 2) (hpd : IsTotallyPosDef Q) (L : Lat F 2)
    (hLi : Lattices.IsIntegral Q L.1) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMass Q L (algebraMap (𝓞 F) F m) = (1 / 2 : ℝ) * mass Q L * siegelProduct2RegSpace Q L m := by
  obtain ⟨γ, Q₀, hγ, hpd₀, hLi'⟩ := exists_coords (n := 1) Q hpd L hLi
  obtain ⟨h1, h2⟩ := repMass_mass_coords Q hpd L hLi γ Q₀ hγ (algebraMap (𝓞 F) F m)
  rw [h1, h2, siegelProduct2RegSpace_eq Q L hLi γ Q₀ hγ hpd₀ hm]
  exact (siegelFormulaAt2Lat_totallyReal Q₀ hpd₀ _ hLi' hm).repMass_eq

/-- **Siegel's formula for a unary quadratic space over a totally real field** (unconditional; $\varepsilon = \tfrac12$):
$\mathrm{repMass}(Q, L, m) = \mathrm{Mass}(Q, L)\cdot 2\,\mathcal S_1(Q, L, m)$. -/
@[kb "siegel1935" "Hauptsatz, n = 1 (ε = 1/2), quadratic space over a totally real field, every genus [unverified for F]"]
theorem siegelFormula1_space_totallyReal (Q : QuadForm F 1) (hpd : IsTotallyPosDef Q) (L : Lat F 1)
    (hLi : Lattices.IsIntegral Q L.1) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMass Q L (algebraMap (𝓞 F) F m) = mass Q L * (2 * siegelProductOneSpace Q L m) := by
  obtain ⟨γ, Q₀, hγ, hpd₀, hLi'⟩ := exists_coords (n := 0) Q hpd L hLi
  obtain ⟨h1, h2⟩ := repMass_mass_coords Q hpd L hLi γ Q₀ hγ (algebraMap (𝓞 F) F m)
  rw [h1, h2, siegelProductOneSpace_eq Q L hLi γ Q₀ hγ hpd₀ hm]
  exact siegelFormulaOneLat_totallyReal Q₀ hpd₀ _ hLi' hm

/-! ### Basis independence -/

section Basis

/-- New coordinates for $(Q\circ g, g^{-1}L)$ from coordinates for $(Q, L)$: $\gamma' = g^{-1}\gamma$, the same $Q_0$. -/
theorem coords_compMat {N : ℕ} (Q : QuadForm F N) (L : Lat F N) (g γ : GL (Fin N) F) (Q₀ : QuadForm (𝓞 F) N)
    (hγ : formF Q₀ = Q.compMat γ.val) :
    formF Q₀ = (Q.compMat g.val).compMat (g⁻¹ * γ).val ∧
      Lat.image (g⁻¹ * γ)⁻¹ (Lat.image g⁻¹ L) = Lat.image γ⁻¹ L := by
  refine ⟨by rw [compMat_mul, ← Units.val_mul, mul_inv_cancel_left, hγ], ?_⟩
  rw [← lat_image_mul, _root_.mul_inv_rev, inv_inv, mul_inv_cancel_right]

/-- **$S(Q, L)$ does not depend on the basis** ($N \ge 4$): $S(Q\circ g, g^{-1}L, m) = S(Q, L, m)$ for $g \in \mathrm{GL}_N(F)$. -/
theorem siegelProductSpace_compMat {n : ℕ} (hn : 3 ≤ n) (Q : QuadForm F (n + 1)) (hpd : IsTotallyPosDef Q)
    (L : Lat F (n + 1)) (hLi : Lattices.IsIntegral Q L.1) (g : GL (Fin (n + 1)) F) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProductSpace (Q.compMat g.val) (Lat.image g⁻¹ L) m = siegelProductSpace Q L m := by
  obtain ⟨γ, Q₀, hγ, hpd₀, -⟩ := exists_coords Q hpd L hLi
  obtain ⟨hγ', himg⟩ := coords_compMat Q L g γ Q₀ hγ
  rw [siegelProductSpace_eq Q L hLi γ Q₀ hγ hn hpd₀ hm,
    siegelProductSpace_eq _ _ (isIntegral_compMat Q g hLi) _ Q₀ hγ' hn hpd₀ hm, himg]

/-- **$S_3(Q, L)$ does not depend on the basis.** -/
theorem siegelProduct3Space_compMat (Q : QuadForm F 3) (hpd : IsTotallyPosDef Q) (L : Lat F 3)
    (hLi : Lattices.IsIntegral Q L.1) (g : GL (Fin 3) F) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProduct3Space (Q.compMat g.val) (Lat.image g⁻¹ L) m = siegelProduct3Space Q L m := by
  obtain ⟨γ, Q₀, hγ, hpd₀, -⟩ := exists_coords (n := 2) Q hpd L hLi
  obtain ⟨hγ', himg⟩ := coords_compMat Q L g γ Q₀ hγ
  rw [siegelProduct3Space_eq Q L hLi γ Q₀ hγ hpd₀ hm,
    siegelProduct3Space_eq _ _ (isIntegral_compMat Q g hLi) _ Q₀ hγ' hpd₀ hm, himg]

/-- **$S^{\mathrm{reg}}_2(Q, L)$ does not depend on the basis.** -/
theorem siegelProduct2RegSpace_compMat (Q : QuadForm F 2) (hpd : IsTotallyPosDef Q) (L : Lat F 2)
    (hLi : Lattices.IsIntegral Q L.1) (g : GL (Fin 2) F) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProduct2RegSpace (Q.compMat g.val) (Lat.image g⁻¹ L) m = siegelProduct2RegSpace Q L m := by
  obtain ⟨γ, Q₀, hγ, hpd₀, -⟩ := exists_coords (n := 1) Q hpd L hLi
  obtain ⟨hγ', himg⟩ := coords_compMat Q L g γ Q₀ hγ
  rw [siegelProduct2RegSpace_eq Q L hLi γ Q₀ hγ hpd₀ hm,
    siegelProduct2RegSpace_eq _ _ (isIntegral_compMat Q g hLi) _ Q₀ hγ' hpd₀ hm, himg]

/-- **$\mathcal S_1(Q, L)$ does not depend on the basis.** -/
theorem siegelProductOneSpace_compMat (Q : QuadForm F 1) (hpd : IsTotallyPosDef Q) (L : Lat F 1)
    (hLi : Lattices.IsIntegral Q L.1) (g : GL (Fin 1) F) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProductOneSpace (Q.compMat g.val) (Lat.image g⁻¹ L) m = siegelProductOneSpace Q L m := by
  obtain ⟨γ, Q₀, hγ, hpd₀, -⟩ := exists_coords (n := 0) Q hpd L hLi
  obtain ⟨hγ', himg⟩ := coords_compMat Q L g γ Q₀ hγ
  rw [siegelProductOneSpace_eq Q L hLi γ Q₀ hγ hpd₀ hm,
    siegelProductOneSpace_eq _ _ (isIntegral_compMat Q g hLi) _ Q₀ hγ' hpd₀ hm, himg]

/-- **The local densities move with the basis:** $\beta_\mathfrak p(Q\circ g; g^{-1}L, m) = \|\det g\|_\mathfrak p^{-1}\beta_\mathfrak p(Q; L, m)$ (the
Haar measure of $F_\mathfrak p^N$ is that of the coordinates; the product formula cancels the factors against `detGramF`). -/
theorem spaceBeta_compMat {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Q : QuadForm F (n + 1)) (hpd : IsTotallyPosDef Q)
    (L : Lat F (n + 1)) (hLi : Lattices.IsIntegral Q L.1) (g : GL (Fin (n + 1)) F) (m : 𝓞 F) :
    spaceBeta v (Q.compMat g.val) (Lat.image g⁻¹ L) m =
      ‖algebraMap F (v.adicCompletion F) g.val.det‖⁻¹ * spaceBeta v Q L m := by
  obtain ⟨γ, Q₀, hγ, -, -⟩ := exists_coords Q hpd L hLi
  obtain ⟨hγ', himg⟩ := coords_compMat Q L g γ Q₀ hγ
  have hinv : ‖algebraMap F (v.adicCompletion F) (g⁻¹ : GL (Fin (n + 1)) F).val.det‖ =
      ‖algebraMap F (v.adicCompletion F) g.val.det‖⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← norm_mul, ← map_mul, ← det_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, det_one, map_one, norm_one]
  rw [spaceBeta_eq v Q L hLi γ Q₀ hγ, spaceBeta_eq v _ _ (isIntegral_compMat Q g hLi) _ Q₀ hγ', himg,
    Units.val_mul, det_mul, map_mul, norm_mul, hinv]
  ring

/-- **`detGramF` moves with the basis:** $\det_\sigma(Q\circ g) = |\sigma\det g|^2\det_\sigma(Q)$. -/
theorem detGramF_compMat {N : ℕ} (Q : QuadForm F N) (g : GL (Fin N) F) (σ : F →ₐ[ℚ] ℂ) :
    detGramF (Q.compMat g.val) σ = ‖σ g.val.det‖ ^ 2 * detGramF Q σ := by
  unfold detGramF
  rw [hessian_det_compMat', mul_div_assoc, map_mul, norm_mul, map_pow, norm_pow]

end Basis

/-! ### Natural order -/

section Natural

/-- **The corrected product survives a finite change of the character and a finitely supported factor.** -/
theorem multipliable_corr_transfer {χ χ₀ f g : HeightOneSpectrum (𝓞 F) → ℝ}
    (hχ₀ : ∀ v, |χ₀ v| ≤ 1) (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, χ v = χ₀ v) (e : ℤ)
    (hf : Multipliable fun v => f v * (1 - χ₀ v / (normP v : ℝ)) ^ e) (hg : Multipliable g) :
    Multipliable fun v => (f v * g v) * (1 - χ v / (normP v : ℝ)) ^ e := by
  have hr : Multipliable fun v => ((1 - χ v / (normP v : ℝ)) / (1 - χ₀ v / (normP v : ℝ))) ^ e :=
    multipliable_of_ne_finset_one (s := S) fun v hv => by
      rw [hS v hv, div_self (one_sub_div_pos (hχ₀ v) v).ne', _root_.one_zpow]
  refine ((hf.mul hg).mul hr).congr fun v => ?_
  have h0 := (one_sub_div_pos (hχ₀ v) v).ne'
  simp only [div_zpow]
  field_simp [zpow_ne_zero e h0]

/-- $L_F(1,\chi) > 0$ survives a finite change of the character. -/
theorem lOne_pos_of_congr {χ χ₀ : HeightOneSpectrum (𝓞 F) → ℝ} (hχ : ∀ v, |χ v| ≤ 1) (hχ₀ : ∀ v, |χ₀ v| ≤ 1)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, χ v = χ₀ v) (hpos : 0 < LOne χ₀)
    (hL : HasLOne χ₀ (LOne χ₀)) : 0 < LOne χ := by
  rw [(hL.congr_finite hχ hχ₀ S hS).lOne_eq]
  have hf : ∀ (c : HeightOneSpectrum (𝓞 F) → ℝ), (∀ v, |c v| ≤ 1) → ∀ v, 0 < lFactor c 1 v := fun c hc v => by
    have : lFactor c 1 v = (1 - c v / (normP v : ℝ))⁻¹ := by
      simp only [lFactor, Real.rpow_neg_one, div_eq_mul_inv]
    rw [this]; exact inv_pos.mpr (one_sub_div_pos (hc v) v)
  exact mul_pos hpos (Finset.prod_pos fun v _ => div_pos (hf χ hχ v) (hf χ₀ hχ₀ v))

/-- **Siegel's formula for a ternary quadratic space over $F$, natural order** (Hanke 2004, (5.3), p. 368, over $F$): given
`NaturalOrderEulerOne (spaceChar3 Q m)` (prime ideal theorem for $\chi_m$; convention input),
$\lim_X\prod_{N\mathfrak p\le X}\beta_\mathfrak p(L, m)$ is the regularized value in `siegelProduct3Space`, and Siegel's formula holds. -/
@[kb "hanke2004" "(5.3), p. 368 (n = 3, natural order), quadratic space over a totally real field"]
theorem siegelFormula3_space_natural (Q : QuadForm F 3) (hpd : IsTotallyPosDef Q) (L : Lat F 3)
    (hLi : Lattices.IsIntegral Q L.1) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (hN : NaturalOrderEulerOne (spaceChar3 Q m)) :
    HasProd (fun v => spaceBeta v Q L m) (regProd (spaceChar3 Q m) 1 fun v => spaceBeta v Q L m) (normOrder F) ∧
      repMass Q L (algebraMap (𝓞 F) F m) = mass Q L * siegelProduct3Space Q L m := by
  refine ⟨?_, siegelFormula3_space_totallyReal Q hpd L hLi hm⟩
  obtain ⟨γ, Q₀, hγ, hpd₀, hLi'⟩ := exists_coords (n := 2) Q hpd L hLi
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_of_isTotallyPosDef hpd₀
  have hm0 : m ≠ 0 := ne_zero_of_totallyPos hm
  have hβ := multipliable_latBeta_mul_chiTern hQ₀ _ hLi' hm0
  have hχ := Filter.eventually_cofinite.mp (eventually_chiTern_eq Q γ Q₀ hγ hQ₀ hm0)
  have hmul := multipliable_corr_transfer (χ := spaceChar3 Q m)
    (fun v => abs_chiTern_le v Q₀ m) hχ.toFinset
    (fun v hv => by by_contra hc; exact hv (hχ.mem_toFinset.mpr (fun h => hc h.symm))) 1 hβ
    (hasProd_norm_det γ).multipliable
  replace hmul : Multipliable fun v => spaceBeta v Q L m * (1 - spaceChar3 Q m v / (normP v : ℝ)) :=
    hmul.congr fun v => by rw [spaceBeta_eq v Q L hLi γ Q₀ hγ, zpow_one]; ring
  exact hasProd_normOrder_regProd hN (fun v => abs_sqChar_le v _) hmul.hasProd

/-- **Siegel's formula for a binary quadratic space over $F$, natural order**: given `NaturalOrderEulerOne (spaceChar2 Q)`,
$\lim_X\prod_{N\mathfrak p\le X}\beta_\mathfrak p(L, m)$ is the regularized value in `siegelProduct2RegSpace`, and Siegel's formula holds. -/
@[kb "siegel1935" "Hauptsatz, n = 2 (natural order), quadratic space over a totally real field [unverified]"]
theorem siegelFormula2_space_natural (Q : QuadForm F 2) (hpd : IsTotallyPosDef Q) (L : Lat F 2)
    (hLi : Lattices.IsIntegral Q L.1) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (hN : NaturalOrderEulerOne (spaceChar2 Q)) :
    HasProd (fun v => spaceBeta v Q L m) (regProd (spaceChar2 Q) (-1) fun v => spaceBeta v Q L m) (normOrder F) ∧
      repMass Q L (algebraMap (𝓞 F) F m) = (1 / 2 : ℝ) * mass Q L * siegelProduct2RegSpace Q L m := by
  refine ⟨?_, siegelFormula2_space_totallyReal Q hpd L hLi hm⟩
  obtain ⟨γ, Q₀, hγ, hpd₀, hLi'⟩ := exists_coords (n := 1) Q hpd L hLi
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_of_isTotallyPosDef hpd₀
  obtain ⟨P₀, hP₀⟩ := exists_hasProd_latBeta_mul_chiP Q₀ hpd₀ _ hLi' hm
  have hχ := Filter.eventually_cofinite.mp (eventually_chiP_eq Q γ Q₀ hγ hQ₀)
  have hS : ∀ v ∉ hχ.toFinset, spaceChar2 Q v = chiP v Q₀ :=
    fun v hv => by by_contra hc; exact hv (hχ.mem_toFinset.mpr (fun h => hc h.symm))
  have hmul := multipliable_corr_transfer (χ := spaceChar2 Q)
    (fun v => abs_chiP_le Q₀ v) hχ.toFinset hS (-1) hP₀.multipliable (hasProd_norm_det γ).multipliable
  replace hmul : Multipliable fun v => spaceBeta v Q L m * (1 - spaceChar2 Q v / (normP v : ℝ)) ^ (-1 : ℤ) :=
    hmul.congr fun v => by rw [spaceBeta_eq v Q L hLi γ Q₀ hγ]; ring
  set χ := spaceChar2 Q
  set β : HeightOneSpectrum (𝓞 F) → ℝ := fun v => spaceBeta v Q L m
  obtain ⟨hL0, hL⟩ := lOne_chiP_binary hpd₀
  have hpos : 0 < LOne χ := lOne_pos_of_congr (fun v => abs_sqChar_le v _) (fun v => abs_chiP_le Q₀ v)
    hχ.toFinset hS hL0 hL
  have hinv := hasProd_zpow hN.hasProd hpos.ne' (-1)
  have h := hmul.hasProd.normOrder.mul hinv
  have e : regProd χ (-1) β = (∏' v, β v * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ)) * LOne χ ^ (-1 : ℤ) := by
    simp only [regProd]; ring
  rw [e]
  refine h.congr_fun fun v => ?_
  have hl : 1 - χ v / (normP v : ℝ) ≠ 0 := (one_sub_div_pos (abs_sqChar_le v _) v).ne'
  simp only [_root_.zpow_neg_one, inv_inv]
  rw [mul_assoc, inv_mul_cancel₀ hl, mul_one]

end Natural

/-! ### Consistency with G's statements -/

section Consistency

theorem coords_one {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (L : Lat F N) :
    formF Q₀ = (formF Q₀).compMat (1 : GL (Fin N) F).val ∧ Lat.image (1 : GL (Fin N) F)⁻¹ L = L := by
  refine ⟨by rw [Units.val_one, compMat_one], ?_⟩
  rw [inv_one]; exact Subtype.ext (glImage_one L.1)

/-- For a form over $\mathcal O_F$, the coordinate-free product is G's (`siegelProductLat`), $N \ge 4$. -/
theorem siegelProductSpace_formF {n : ℕ} (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀))
    (L : Lat F (n + 1)) (hLi : Lattices.IsIntegral (formF Q₀) L.1) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProductSpace (formF Q₀) L m = siegelProductLat Q₀ L m := by
  obtain ⟨h1, h2⟩ := coords_one Q₀ L
  rw [siegelProductSpace_eq _ L hLi 1 Q₀ h1 hn hpd hm, h2]

/-- For a form over $\mathcal O_F$, the coordinate-free rank-3 product (character `spaceChar3`) is G's (character `chiTern`). -/
theorem siegelProduct3Space_formF (Q₀ : QuadForm (𝓞 F) 3) (hpd : IsTotallyPosDef (formF Q₀)) (L : Lat F 3)
    (hLi : Lattices.IsIntegral (formF Q₀) L.1) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProduct3Space (formF Q₀) L m = siegelProduct3Lat Q₀ L m := by
  obtain ⟨h1, h2⟩ := coords_one Q₀ L
  rw [siegelProduct3Space_eq _ L hLi 1 Q₀ h1 hpd hm, h2]

/-- For a form over $\mathcal O_F$, the coordinate-free rank-2 product (character `spaceChar2`) is G's (character `chiP`). -/
theorem siegelProduct2RegSpace_formF (Q₀ : QuadForm (𝓞 F) 2) (hpd : IsTotallyPosDef (formF Q₀)) (L : Lat F 2)
    (hLi : Lattices.IsIntegral (formF Q₀) L.1) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProduct2RegSpace (formF Q₀) L m = siegelProduct2RegLat Q₀ L m := by
  obtain ⟨h1, h2⟩ := coords_one Q₀ L
  rw [siegelProduct2RegSpace_eq _ L hLi 1 Q₀ h1 hpd hm, h2]

/-- For a form over $\mathcal O_F$, the coordinate-free rank-1 product is G's. -/
theorem siegelProductOneSpace_formF (Q₀ : QuadForm (𝓞 F) 1) (hpd : IsTotallyPosDef (formF Q₀)) (L : Lat F 1)
    (hLi : Lattices.IsIntegral (formF Q₀) L.1) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProductOneSpace (formF Q₀) L m = siegelProductOneLat Q₀ L m := by
  obtain ⟨h1, h2⟩ := coords_one Q₀ L
  rw [siegelProductOneSpace_eq _ L hLi 1 Q₀ h1 hpd hm, h2]

end Consistency

end QuadFormsKB.Tamagawa.SiegelSpace
