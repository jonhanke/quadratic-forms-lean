import QuadFormsKB.Tamagawa.LocalOrbitalGlobal

/-!
# The orbit identity: Siegel's theorem for a number with the stabilizer's Tamagawa number

**The combinatorial core of Weil's p. 109.** For a totally definite genus and a number $t$, Weil's unfolding over the sphere
$\{Q = t\}$ (Lemma 2.4.2 with $\Gamma = G\times\mathbb G_m$ and stabilizer $G' = SO(\xi^\perp)$, Witt's theorem) says, in combinatorial form,
$$2\mu_{\mathrm{Tam}}(K_{SO})\sum_{\mathrm{cls}(M)}\frac{r_M(t)}{|O(M)|} = \tau(G')\cdot S(L, t),\qquad
  S(L,t) = |d_F|^{-\frac{N-1}2}\prod_\sigma\beta_\sigma(t)\prod_\mathfrak p\beta_\mathfrak p(L, t)$$
(`siegelProduct`): the left side is the Tamagawa volume of the orbit of pairs, the right side its fibration over the sphere
with fibre $G'$. With Siegel's theorem $\sum r_M(t)/|O(M)| = \mathrm{Mass}(L)\,S(L,t)$ and $2\mu\,\mathrm{Mass} = \tau(G)$ this is
$\tau(G) = \tau(G')$; Weil's proof runs the other way: the orbit identity (from $\tau(G') = 2$ and local identities) feeds the
additive calculation, whose comparison with the multiplicative one gives $\tau(G) = 2$.

**Proved here: the split case** (`two_mul_tamagawaK_mul_repMass_split`). For $Q_0 = \langle m\rangle\perp Q_0'$ and $t = m$ the identity
follows from the global reduction (`repMass_eq_mass_mul`: $\sum_Mr_M(m)/|O(M)| = \mathrm{Mass}(L')\cdot W$), the
definition of the stabilizer's Tamagawa number
($\tau(SO(Q_0')) = \mu(K'_{SO})\cdot2\,\mathrm{Mass}(L')$) and the local orbital identity
($W\mu(K_{SO}) = S(L,m)\,\mu(K'_{SO})$), with the local identity at $\mathfrak p \mid 2m$ as the named input
`LocalOrbitalIdentityAt` and the mass formula in rank $n$ (the induction hypothesis) for the convergence of $\prod\alpha_\mathfrak p(L')$.
The general case (any lattice $\mathfrak b^{-1}L$ and any $t = \rho b^2$) needs the same three steps for non-split lattices.
-/

open NumberField IsDedekindDomain Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open Lattices LocalDensity

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **The orbit identity in the split case** (Weil 1982, §4.5, p. 109, combinatorial form). For $Q_0 = \langle m\rangle\perp Q_0'$
over $\mathcal O_F$ ($m \ne 0$, $n \ge 3$), totally positive definite with $\mathcal O_F^{n+1}$ integral, given the local orbital identity
at the primes $\mathfrak p \mid 2m$ (`LocalOrbitalIdentityAt`, input) and the mass formula for $Q_0'$ (rank $n$; the induction
hypothesis, `MassFormulaHolds Q₀'`, equivalently $\tau(SO(Q_0')) = 2$):
$$2\,\mu_{\mathrm{Tam}}(K_{SO})\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(m)}{|O(M)|} = \tau(SO(Q_0'))\cdot S(L, m),$$
$\mu_{\mathrm{Tam}}(K_{SO})$ = `tamagawaK (splitForm m Q₀')`, $\tau(SO(Q_0'))$ = `tauSO Q₀'` (the stabilizer of $e_0$), $S$ = `siegelProduct`.
The value $\tau(SO(\langle m\rangle\perp Q_0'))$ does not occur. -/
@[kb "weil1982" "§4.5, p. 109 (fibration over T(ρ), stabilizer G'); §3.4-3.5 [unverified locator]"]
theorem two_mul_tamagawaK_mul_repMass_split (m : 𝓞 F) (hm : m ≠ 0) (Q₀' : QuadForm (𝓞 F) n) (hn : 3 ≤ n)
    (hpd : IsTotallyPosDef ((splitForm m Q₀').map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral ((splitForm m Q₀').map (algebraMap (𝓞 F) F)) (stdLat F (n + 1)).1)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), 2 * m ∈ v.asIdeal → LocalOrbitalIdentityAt v Q₀' m)
    (hIH : MassFormulaHolds Q₀') :
    2 * tamagawaK (splitForm m Q₀') *
        repMass ((splitForm m Q₀').map (algebraMap (𝓞 F) F)) (stdLat F (n + 1)) (algebraMap (𝓞 F) F m) =
      tauSO Q₀' * siegelProduct (splitForm m Q₀') m := by
  have hloc := localOrbitalIdentity_of_massFormula m hm Q₀' hn hpd hLi hbad hIH
  set QF' := Q₀'.map (algebraMap (𝓞 F) F)
  set mF := algebraMap (𝓞 F) F m
  have hsplit := map_splitForm_alg m Q₀'
  have hpd₀ := hpd
  have hLi₀ := hLi
  rw [hsplit] at hpd₀ hLi₀
  have hmF : mF ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hm
  have hpd' := isTotallyPosDef_of_splitForm hpd₀
  have hLi' := isIntegral_of_splitForm hLi₀
  have hQ' : Q₀'.Nondegenerate := nondegenerate_of_map hpd'.nondegenerate
  have hR := repMass_eq_mass_mul mF QF' (stdLat F (n + 1)) hpd₀ hLi₀ hmF hpd' hLi'
  have hloc' := hloc.typeSum_eq
  set W := ∑ᶠ t : orbitRel.Quotient (OAf QF') (CompSet mF QF' (stdLat F (n + 1))),
    typeWeight mF QF' (stdLat F (n + 1)) t
  set A := ∏' v : HeightOneSpectrum (𝓞 F), NF.siegelDensity v (splitForm m Q₀') (splitForm m Q₀')
  set A' := ∏' v : HeightOneSpectrum (𝓞 F), NF.siegelDensity v Q₀' Q₀'
  set B := ∏' v : HeightOneSpectrum (𝓞 F), NF.localDensity v (splitForm m Q₀') m
  set Pr := ∏ σ : F →ₐ[ℚ] ℂ, archVolSO (n + 1) (detGram (splitForm m Q₀') σ)
  set Pr' := ∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram Q₀' σ)
  set ρ := ∏ σ : F →ₐ[ℚ] ℂ, archRepDensity (n + 1) ‖σ mF‖ (detGram (splitForm m Q₀') σ)
  set δ := |(NumberField.discr F : ℝ)|
  have hδ : 0 < δ := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F)
  have harch : Pr * normTwoM m ^ n = Pr' * ρ := archProd_splitForm m hm Q₀' hQ'
  have hT : tamagawaK (splitForm m Q₀') = δ ^ (-(((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) - 1) / 4)) * Pr * A := rfl
  have hT' : tamagawaK Q₀' = δ ^ (-((n : ℝ) * (n - 1) / 4)) * Pr' * A' := rfl
  have hSP : siegelProduct (splitForm m Q₀') m = δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2) * ρ * B := rfl
  have hδe : δ ^ (-(((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) - 1) / 4)) =
      δ ^ (-((n : ℝ) * (n - 1) / 4)) * δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2) := by
    rw [← Real.rpow_add hδ]; push_cast; ring_nf
  have key : W * tamagawaK (splitForm m Q₀') = siegelProduct (splitForm m Q₀') m * tamagawaK Q₀' := by
    rw [hT, hT', hSP, hδe]
    linear_combination (δ ^ (-((n : ℝ) * (n - 1) / 4)) * δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2) * Pr) * hloc' +
      (δ ^ (-((n : ℝ) * (n - 1) / 4)) * δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2) * A' * B) * harch
  have htau : tauSO Q₀' = tamagawaK Q₀' * (2 * mass QF' (stdLat F n)) := by
    rw [tauSO, mass_SO_eq_two_mul_mass Q₀' hQ' (by omega) hpd' hLi']
  rw [hsplit, hR, htau]
  linear_combination (2 * mass QF' (stdLat F n)) * key

end QuadFormsKB.Tamagawa
