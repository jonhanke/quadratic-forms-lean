/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.SiegelLat
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSiegelTotallyReal
import QuadFormsKB.Tamagawa.TernaryTamagawaNF

/-!
# Siegel's formula for every genus in rank $N \ge 4$, every totally real field

**Layer:** $F$ totally real (any class number); $Q_0$ totally positive definite over $\mathcal O_F$ in $N = n + 1 \ge 4$ variables; $L$ an
**arbitrary** $\mathcal O_F$-lattice on $V = (F^N, Q_0)$ with $Q_0$ integral on $L$ (any Steinitz class); $m \in \mathcal O_F$ totally positive.

**Proves**
* **`two_mul_tamagawaKLat_mul_repMass_frame`**: $2\,\mu_{\mathrm{Tam}}(K_{SO}(L))\,\mathrm{repMass}(L, m) = \tau(SO(Q_0'))\cdot S(L, m)$ for an
  adapted frame $Q_0\circ g = \langle m\rangle\perp Q_0'$ (`two_mul_tamagawaK_mul_repMass_frame` for an arbitrary lattice; the local
  input is the unconditional `latOrbitalIdentity`);
* `siegelProductLat_eq_zero_of_not_rep`: both sides vanish when $Q_0$ does not represent $m$ over $F$;
* `siegelFormulaAtLat_of_tau`: Siegel's formula for the genus of $L$ from $\tau(SO) = 2$ in ranks $N$ and $N - 1$;
* **`siegelFormulaAtLat_totallyReal`** (headline, unconditional): for every $N \ge 4$, every totally real $F$, every integral lattice $L$
  on $(F^N, Q_0)$ and every totally positive $m$,
  $$\sum_{\mathrm{cls}M\subseteq\mathrm{gen}L}\frac{r_M(m)}{|O(M)|} = \mathrm{Mass}(L)\cdot|d_F|^{-\frac{N-1}2}\prod_\sigma\beta_\sigma(m)\prod_\mathfrak p\beta_\mathfrak p(L, m);$$
  for $L = \mathcal O_F^N$ it is `siegelFormulaAt_totallyReal` (`siegelFormulaAtLat_totallyReal_std`);
* `exists_coords_of_isIntegral`: every integral lattice on every totally positive definite space $(F^N, Q)$ is, in suitable
  coordinates, a lattice $L \supseteq \mathcal O_F^N$ on $(F^N, Q_0)$ with $Q_0$ over $\mathcal O_F$ (so the headline covers every genus).

Sources: Weil 1982, §4.5, p. 100 and p. 109 [unverified]; Siegel 1935, Hauptsatz (over $F$ [unverified]).
-/

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.SiegelLat

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.LocalDensity QuadFormsKB.QuadForm
open QuadFormsKB.HilbertModular LatChange

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-! ### Siegel's theorem for one number and one lattice, with the stabilizer's $\tau$ -/

/-- **The frame identity for the genus of an arbitrary lattice** (Weil 1982, §4.5, p. 109 [unverified]): for $Q_0$ totally positive
definite in $N = n + 1 \ge 4$ variables, $L$ integral, $m = \rho$ totally positive and an adapted frame $Q_0\circ g = \langle\rho\rangle\perp Q_0'$,
$$2\,\mu_{\mathrm{Tam}}(K_{SO}(L))\cdot\mathrm{repMass}(L, \rho) = \tau(SO(Q_0'))\cdot S(L, m).$$
*Proof:* `repMass_eq_mass_mul_finprod_lat` gives $\mathrm{repMass}(L, \rho) = \mathrm{Mass}(Q_0')\prod_\mathfrak pW_\mathfrak p(g^{-1}L_\mathfrak p, 1)$; `latOrbitalIdentity` gives $W_\mathfrak p\,r_\mathfrak p(L) = \alpha_\mathfrak p(Q_0')\,|\det g|^{n+1}|2\rho|^{-n}\beta_\mathfrak p(L, m)/\alpha_\mathfrak p(Q_0)$;
$\mu(K_{SO}(L)) = \mu(K_{SO}(\mathcal O_F^N))\prod_\mathfrak pr_\mathfrak p(L)$ (`tamagawaKLat_eq_finprod`); the archimedean step is that of `SiegelAllRanks`. -/
@[kb "weil1982" "§4.5, p. 100 and p. 109 (Siegel's theorem from the fibration over T(ρ), arbitrary lattice) [unverified]"]
theorem two_mul_tamagawaKLat_mul_repMass_frame (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀))
    (hn : 3 ≤ n) (L : Lat F (n + 1)) (hLi : Lattices.IsIntegral (formF Q₀) L.1) {m : 𝓞 F} {ρ : F}
    (hmρ : algebraMap (𝓞 F) F m = ρ) (hm : ∀ v : InfinitePlace F, 0 < realEmb F v ρ)
    (fr : AdaptedFrame (formF Q₀) ρ) :
    2 * tamagawaKLat Q₀ L * repMass (formF Q₀) L ρ = tauSO fr.Q' * siegelProductLat Q₀ L m := by
  classical
  have hρ : ρ ≠ 0 := by
    intro h; obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have := hm w; rw [h, map_zero] at this; exact lt_irrefl 0 this
  have hQF : (formF Q₀).Nondegenerate := hpd.nondegenerate
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_of_map hQF
  have hQ'nd : fr.Q'.Nondegenerate := fr.nondegenerate hQF hρ
  set QF' := fr.Q'.map (algebraMap (𝓞 F) F)
  have hpd' : IsTotallyPosDef QF' := by
    have h1 := isTotallyPosDef_compMat (formF Q₀) fr.g hpd
    rw [fr.compMat_eq] at h1
    exact isTotallyPosDef_of_splitForm h1
  -- the local factors
  set W0 : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    locTypeSumG v ρ QF' (loc v (glImage fr.g⁻¹ L.1)) (algebraMap F (v.adicCompletion F) 1)
  set r : HeightOneSpectrum (𝓞 F) → ℝ := fun v => locRatio v Q₀ L
  set α : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v Q₀ Q₀
  set α' : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v fr.Q' fr.Q'
  set E : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (n + 1) / ‖algebraMap F (v.adicCompletion F) (2 * ρ)‖ ^ n
  set β : HeightOneSpectrum (𝓞 F) → ℝ := fun v => latBeta v Q₀ L m
  have hEpos : ∀ v, 0 < E v := fun v => by
    have h1 : algebraMap F (v.adicCompletion F) fr.g.val.det ≠ 0 :=
      (map_ne_zero _).mpr (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero
    have h2 : algebraMap F (v.adicCompletion F) (2 * ρ) ≠ 0 := (map_ne_zero _).mpr (mul_ne_zero two_ne_zero hρ)
    exact div_pos (pow_pos (norm_pos_iff.mpr h1) _) (pow_pos (norm_pos_iff.mpr h2) _)
  have hαpos : ∀ v, 0 < α v := fun v => siegelDensity_pos v Q₀ hQ₀
  have hα'pos : ∀ v, 0 < α' v := fun v => siegelDensity_pos v fr.Q' hQ'nd
  have hrpos : ∀ v, 0 < r v := fun v => locRatio_pos v hQ₀ L hLi
  -- the local identity
  have hW : ∀ v, W0 v = α' v * E v * β v / (α v * r v) := by
    intro v
    have hj := latOrbitalIdentity v Q₀ hQ₀ (by omega) L hLi hmρ hρ fr
    rw [show (2 : v.adicCompletion F) * algebraMap F (v.adicCompletion F) ρ =
      algebraMap F (v.adicCompletion F) (2 * ρ) by rw [map_mul, map_ofNat]] at hj
    have hdet : 0 < ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (n + 1) :=
      pow_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero)) _
    have h2ρ : 0 < ‖algebraMap F (v.adicCompletion F) (2 * ρ)‖ ^ n :=
      pow_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr (mul_ne_zero two_ne_zero hρ))) _
    have hα := hαpos v
    have hr := hrpos v
    simp only [W0, E, α, α', β, r] at hj ⊢
    generalize ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (n + 1) = D at hj hdet ⊢
    generalize ‖algebraMap F (v.adicCompletion F) (2 * ρ)‖ ^ n = B2 at hj h2ρ ⊢
    rw [eq_div_iff (mul_pos hα hr).ne']
    field_simp at hj ⊢
    linear_combination hj
  -- finite supports
  have hglat : (glImage fr.g⁻¹ L.1).IsLattice F := glImage_isLattice fr.g⁻¹ L.2
  have hfin₀ : {v : HeightOneSpectrum (𝓞 F) | loc v (glImage fr.g⁻¹ L.1) ≠ std v ∨ v.valuation F ρ ≠ 1 ∨
      v.valuation F 2 ≠ 1}.Finite :=
    ((Filter.eventually_cofinite.mp (loc_eventually_std hglat)).union
      ((finite_valuation_ne_one hρ).union (finite_valuation_ne_one (two_ne_zero (α := F))))).subset fun v hv => by
        simpa [or_assoc] using hv
  have hW0fin : Function.HasFiniteMulSupport W0 := by
    refine hfin₀.subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_setOf_eq, not_or, not_not] at h
    apply hv
    show locTypeSumG v ρ QF' (loc v (glImage fr.g⁻¹ L.1)) (algebraMap F (v.adicCompletion F) 1) = 1
    rw [h.1, map_one]
    exact locTypeSumG_std_one_of_units v fr.Q' hQ'nd h.2.1 h.2.2
  have hrfin : Function.HasFiniteMulSupport r := by
    refine (Filter.eventually_cofinite.mp (loc_eventually_std L.2)).subset fun v hv => ?_
    by_contra h
    exact hv (locRatio_eq_one v Q₀ L (by simpa using h))
  have hEfin : Function.HasFiniteMulSupport E := by
    have hdet : fr.g.val.det ≠ 0 := (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero
    refine ((finite_valuation_ne_one hdet).union (finite_valuation_ne_one (mul_ne_zero two_ne_zero hρ))).subset
      fun v hv => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    apply hv
    show E v = 1
    simp only [E, norm_algebraMap_eq_one h.1, norm_algebraMap_eq_one h.2, one_pow, div_one]
  -- the products
  have hαm : Multipliable α := multipliable_siegelDensity (N := n + 1) (by omega) (by omega) Q₀ hQ₀
  have hα'm : Multipliable α' := multipliable_siegelDensity (N := n) (by omega) (by omega) fr.Q' hQ'nd
  have hA' : 0 < ∏' v, α' v := tprod_siegelDensity_pos (N := n) (by omega) fr.Q' hQ'nd
  have hfp : ∀ {f : HeightOneSpectrum (𝓞 F) → ℝ}, Function.HasFiniteMulSupport f → HasProd f (∏ᶠ v, f v) :=
    fun {f} hf => by
      have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hf).hasProd
      rwa [tprod_eq_finprod hf] at this
  have hEprod : 0 < ∏ᶠ v, E v := by
    rw [finprod_eq_prod_of_mulSupport_subset E (s := hEfin.toFinset) fun v hv => (Set.Finite.mem_toFinset _).mpr hv]
    exact Finset.prod_pos fun v _ => hEpos v
  have hβeq : β = fun v => W0 v * α v * r v / (α' v * E v) := by
    funext v
    rw [hW v]
    have := hα'pos v; have := hEpos v; have := hαpos v; have := hrpos v
    field_simp
  have hβp : HasProd β ((∏ᶠ v, W0 v) * (∏' v, α v) * (∏ᶠ v, r v) / ((∏' v, α' v) * ∏ᶠ v, E v)) := by
    rw [hβeq]
    exact (((hfp hW0fin).mul hαm.hasProd).mul (hfp hrfin)).div₀ (hα'm.hasProd.mul (hfp hEfin))
      (mul_pos hA' hEprod).ne'
  -- `repMass` through the frame
  have hrep : repMass (formF Q₀) L ρ = mass QF' (stdLat F n) * ∏ᶠ v, W0 v := by
    have h1 := repMass_eq_mass_mul_finprod_lat Q₀ hpd hρ fr (β := 1) one_ne_zero L hLi
    rw [one_pow, one_mul] at h1
    exact h1
  have htau : tauSO fr.Q' = tamagawaK fr.Q' * (2 * mass QF' (stdLat F n)) := by
    rw [tauSO, mass_SO_eq_two_mul_mass fr.Q' hQ'nd (by omega) hpd' (HilbertModular.isIntegral_stdLat fr.Q')]
  -- the archimedean products
  have key : (∏ σ : F →ₐ[ℚ] ℂ, archVolSO (n + 1) (detGram Q₀ σ)) * ∏ᶠ v, E v =
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram fr.Q' σ)) *
        ∏ σ : F →ₐ[ℚ] ℂ, archRepDensity (n + 1) ‖σ ρ‖ (detGram Q₀ σ) := by
    rw [finprod_frameJac fr hρ, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun σ _ => arch_place_siegel Q₀ hpd fr hρ σ
  set δ := |(NumberField.discr F : ℝ)|
  have hδ : 0 < δ := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F)
  have hδe : δ ^ (-((((n + 1 : ℕ) : ℝ)) * (((n + 1 : ℕ) : ℝ) - 1) / 4)) =
      δ ^ (-((n : ℝ) * ((n : ℝ) - 1) / 4)) * δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2) := by
    rw [← Real.rpow_add hδ]; push_cast; ring_nf
  rw [tamagawaKLat_eq_finprod, hrep, htau, siegelProductLat, hmρ, hβp.tprod_eq]
  unfold tamagawaK
  rw [hδe]
  set M := mass QF' (stdLat F n)
  set P := ∏ᶠ v, W0 v
  set R := ∏ᶠ v, r v
  set A := ∏' v, α v
  set A' := ∏' v, α' v
  set Ep := ∏ᶠ v, E v
  set V₀ := ∏ σ : F →ₐ[ℚ] ℂ, archVolSO (n + 1) (detGram Q₀ σ)
  set V' := ∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram fr.Q' σ)
  set Rσ := ∏ σ : F →ₐ[ℚ] ℂ, archRepDensity (n + 1) ‖σ ρ‖ (detGram Q₀ σ)
  have hdiv : P * A * R / (A' * Ep) * (A' * Ep) = P * A * R := div_mul_cancel₀ _ (mul_pos hA' hEprod).ne'
  calc 2 * (δ ^ (-((n : ℝ) * ((n : ℝ) - 1) / 4)) * δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2) * V₀ * A * R) * (M * P)
      = 2 * δ ^ (-((n : ℝ) * ((n : ℝ) - 1) / 4)) * δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2) * M *
          (P * A * R / (A' * Ep) * (A' * Ep)) * V₀ := by rw [hdiv]; ring
    _ = 2 * δ ^ (-((n : ℝ) * ((n : ℝ) - 1) / 4)) * δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2) * M *
          (P * A * R / (A' * Ep)) * A' * (V₀ * Ep) := by ring
    _ = _ := by rw [key]; ring

/-! ### Numbers not represented over $F$ -/

/-- If $Q_0$ does not represent the totally positive $m$ over $F$, then $S(L, m) = 0$ for every integral lattice $L$: by Hasse–Minkowski
some prime $\mathfrak p$ has $m$ not represented over $F_\mathfrak p$, and then $\beta_\mathfrak p(Q_A, m) = 0$ for the model form $Q_A \cong Q_0$. -/
theorem siegelProductLat_eq_zero_of_not_rep (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀))
    (L : Lat F (n + 1)) (hLi : Lattices.IsIntegral (formF Q₀) L.1) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (h : ¬ ∃ ξ, (formF Q₀).eval ξ = algebraMap (𝓞 F) F m) : siegelProductLat Q₀ L m = 0 := by
  have hρ : algebraMap (𝓞 F) F m ≠ 0 := by
    intro h0; obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have := hm w; rw [h0, map_zero] at this; exact lt_irrefl 0 this
  have hQF := hpd.nondegenerate
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_of_map hQF
  have hnot : ¬ (formF Q₀).RepresentsIn F (algebraMap (𝓞 F) F m) := by
    rintro ⟨x, hx⟩; exact h ⟨x, hx⟩
  rw [represents_iff_everywhere_nf (formF Q₀) hQF _ hρ] at hnot
  simp only [NFPlace.Everywhere, not_forall] at hnot
  obtain ⟨p, hp⟩ := hnot
  cases p with
  | infinite w => exact absurd (representsIn_real Q₀ hpd hm w) hp
  | finite v =>
    obtain ⟨A, hA⟩ := exists_isLocModel v L
    have hint := hA.isIntegral v hLi
    have hQ₁ := nondegenerate_gramZ hQ₀ A hint
    have hp₁ : ¬ (formF (gramZ (formF Q₀) A hint)).RepresentsIn (v.adicCompletion F) (algebraMap (𝓞 F) F m) := by
      rintro ⟨x, hx⟩
      apply hp
      refine ⟨(A.val.map (algebraMap F (v.adicCompletion F))) *ᵥ x, ?_⟩
      rw [← evalIn_compMat_gl, ← formF_gramZ Q₀ A hint]
      exact hx
    have h0 : latBeta v Q₀ L m = 0 := by
      rw [latBeta_eq v Q₀ L hA hint, ← betaZ_algebraMap,
        betaZ_eq_zero_of_not_rep _ hQ₁ (by omega) v hρ hp₁, mul_zero]
    unfold siegelProductLat
    rw [tprod_of_exists_eq_zero ⟨v, h0⟩, mul_zero]

/-! ### Siegel's formula for every genus -/

/-- **Siegel's formula for the genus of an arbitrary lattice, from $\tau = 2$** (Weil 1982, §4.5, p. 100 [unverified]): for $Q_0$ totally
positive definite in $N = n + 1 \ge 4$ variables with $\tau(SO(Q_0)) = 2$ and $\tau(SO(Q')) = 2$ for every totally positive definite $Q'$ in $n$
variables, every integral lattice $L$ on $(F^N, Q_0)$ and every totally positive $m$: `SiegelFormulaAtLat Q₀ L m`. -/
@[kb "weil1982" "§4.5, p. 100 (Siegel's theorem from τ = 2), arbitrary lattice [unverified]"]
theorem siegelFormulaAtLat_of_tau (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀)) (hn : 3 ≤ n)
    (hτ : TamagawaNumberTwo Q₀) (hτ' : ∀ Q' : QuadForm (𝓞 F) n, IsTotallyPosDef (formF Q') → TamagawaNumberTwo Q')
    (L : Lat F (n + 1)) (hLi : Lattices.IsIntegral (formF Q₀) L.1) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAtLat Q₀ L m := by
  refine ⟨?_⟩
  have hρ : algebraMap (𝓞 F) F m ≠ 0 := by
    intro h0; obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have := hm w; rw [h0, map_zero] at this; exact lt_irrefl 0 this
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  by_cases h : ∃ ξ, (formF Q₀).eval ξ = algebraMap (𝓞 F) F m
  · obtain ⟨ξ, hξ⟩ := h
    obtain ⟨fr⟩ := exists_adaptedFrame (formF Q₀) hξ hρ
    have hpd' : IsTotallyPosDef (formF fr.Q') := by
      have h1 := isTotallyPosDef_compMat (formF Q₀) fr.g hpd
      rw [fr.compMat_eq] at h1
      exact isTotallyPosDef_of_splitForm h1
    have key := two_mul_tamagawaKLat_mul_repMass_frame Q₀ hpd hn L hLi rfl hm fr
    rw [show tauSO fr.Q' = 2 from hτ' fr.Q' hpd'] at key
    have hmass := massFormula_lat_nf Q₀ hQ₀ (by omega) hpd hτ L hLi
    have hpos := mass_pos hpd L hLi
    have hμ : tamagawaKLat Q₀ L ≠ 0 := by
      intro h0; rw [hmass, h0, _root_.inv_zero] at hpos; exact lt_irrefl 0 hpos
    rw [hmass]
    field_simp
    linarith
  · rw [repMass_eq_zero_of_not_rep _ _ h, siegelProductLat_eq_zero_of_not_rep Q₀ hpd L hLi hm h, mul_zero]

/-- **Siegel's formula for every genus of totally positive definite lattices in rank $N \ge 4$, over every totally real field**
(unconditional; Siegel 1935, Hauptsatz, over $F$ [unverified]; Weil 1982, §4.5, p. 100 [unverified]). For $F$ totally real (any class
number), $Q_0$ totally positive definite over $\mathcal O_F$ in $N \ge 4$ variables, **every** $\mathcal O_F$-lattice $L$ on $(F^N, Q_0)$ on which
$Q_0$ is integral (any Steinitz class, free or not) and every totally positive $m \in \mathcal O_F$:
$$\sum_{\mathrm{cls}M\subseteq\mathrm{gen}L}\frac{r_M(m)}{|O(M)|} = \mathrm{Mass}(L)\cdot|d_F|^{-\frac{N-1}2}\prod_\sigma\beta_\sigma(m)\prod_\mathfrak p\beta_\mathfrak p(L, m).$$
*Proof:* `siegelFormulaAtLat_of_tau` with $\tau = 2$ in ranks $N$ (`tamagawaNumberTwo_all_ranks_totallyReal`) and $N - 1$ (the same, or
`tamagawaNumberTwo_ternary_nf` for $N - 1 = 3$). -/
@[kb "siegel1935" "Hauptsatz, every genus, over totally real F, rank ≥ 4 [unverified for F]"]
theorem siegelFormulaAtLat_totallyReal {N : ℕ} (hN : 4 ≤ N) (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀))
    (L : Lat F N) (hLi : Lattices.IsIntegral (formF Q₀) L.1) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAtLat Q₀ L m := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  refine siegelFormulaAtLat_of_tau Q₀ hpd (by omega)
    (Measure.Weil.tamagawaNumberTwo_all_ranks_totallyReal hN Q₀ hpd) (fun Q' hQ' => ?_) L hLi hm
  rcases Nat.lt_or_ge n 4 with h3 | h4
  · obtain rfl : n = 3 := by omega
    exact tamagawaNumberTwo_ternary_nf Q' hQ'
  · exact Measure.Weil.tamagawaNumberTwo_all_ranks_totallyReal h4 Q' hQ'

/-- The headline for $L = \mathcal O_F^N$ is the existing `siegelFormulaAt_totallyReal`. -/
theorem siegelFormulaAtLat_totallyReal_std {N : ℕ} (hN : 4 ≤ N) (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt Q₀ m :=
  (siegelFormulaAtLat_std_iff Q₀ m).mp
    (siegelFormulaAtLat_totallyReal hN Q₀ hpd (stdLat F N) (HilbertModular.isIntegral_stdLat Q₀) hm)

/-! ### Every genus is covered -/

/-- **Normal coordinates for an integral lattice**: for every form $Q$ over $F$ and every lattice $L$ with $Q$ integral on $L$, there are
$\gamma \in \mathrm{GL}_N(F)$ with columns in $L$ and a form $Q_0$ over $\mathcal O_F$ with $Q\circ\gamma = Q_0$ over $F$; then $\gamma^{-1}L \supseteq \mathcal O_F^N$ is a
lattice on $(F^N, Q_0)$ on which $Q_0$ is integral, and $\mathrm{repMass}$, $\mathrm{Mass}$ of $(Q, L)$ are those of $(Q_0, \gamma^{-1}L)$
(`repMass_compMat`, `mass_similar`). So `siegelFormulaAtLat_totallyReal` covers every genus of integral lattices on every totally
positive definite quadratic space over $F$. -/
theorem exists_coords_of_isIntegral {N : ℕ} (Q : QuadForm F (N + 1)) (L : Lat F (N + 1))
    (hLi : Lattices.IsIntegral Q L.1) :
    ∃ (γ : GL (Fin (N + 1)) F) (Q₀ : QuadForm (𝓞 F) (N + 1)), formF Q₀ = Q.compMat γ.val ∧
      Lattices.latOf γ ≤ L.1 ∧ (intVec : Submodule (𝓞 F) (Fin (N + 1) → F)) ≤ (Lat.image γ⁻¹ L).1 ∧
      Lattices.IsIntegral (formF Q₀) (Lat.image γ⁻¹ L).1 := by
  obtain ⟨v⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := inferInstance
  obtain ⟨A, hA⟩ := exists_isLocModel v L
  have hint : Lattices.IsIntegral Q (Lattices.latOf A) := hA.isIntegral v hLi
  set Q₀ := gramZ Q A hint
  have hQ₀ : formF Q₀ = Q.compMat A.val :=
    QuadForm.ext_eval fun y => by
      show ((gramZ Q A hint).map (algebraMap (𝓞 F) F)).eval y = _
      rw [gramZ_map, eval_gramFormF_col, eval_compMat]
  refine ⟨A, Q₀, hQ₀, hA.1, fun x hx => ?_, ?_⟩
  · refine ⟨A.val *ᵥ x, hA.1 (mulVec_mem_glImage hx), ?_⟩
    show A⁻¹.val *ᵥ (A.val *ᵥ x) = x
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  · rw [hQ₀]; exact isIntegral_compMat Q A hLi

end QuadFormsKB.Tamagawa.SiegelLat
