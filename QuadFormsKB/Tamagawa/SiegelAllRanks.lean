/-
# $\tau(SO) = 2$ in every rank $N \ge 3$ and Siegel's formula in every rank $N \ge 4$, odd ranks included

Weil 1982, §4.5, Thm. 4.5.1, p. 109 ($\tau = 2$ by induction on the dimension, bases §3.7, Thm. 3.7.1, p. 65), and §4.5, p. 100
(Siegel's theorem as a formal consequence of $\tau = 2$). $F$ is totally real; $\mathcal O_F$ is a PID wherever the induction is used.

**Per number** (no class-number hypothesis). For $Q_0$ totally positive definite over $\mathcal O_F$ in $N = n + 1 \ge 4$ variables, $m \in \mathcal O_F$
totally positive and an adapted frame $Q_0\circ g = \langle m\rangle\perp Q_0'$ with the local orbital identity of the frame at every prime,
$$2\,\mu_{\mathrm{Tam}}(K_{SO}(Q_0))\sum_{\mathrm{cls}M\subseteq\mathrm{gen}\,\mathcal O_F^N}\frac{r_M(m)}{|O(M)|} = \tau(SO(Q_0'))\cdot S(L, m),\qquad
S(L, m) = |d_F|^{-\frac{N-1}2}\prod_\sigma\beta_\sigma(m)\prod_\mathfrak p\beta_\mathfrak p(L, m)$$
(`two_mul_tamagawaK_mul_repMass_frame`): Siegel's theorem with the stabilizer's Tamagawa number, for **every** lattice $\mathcal O_F^N$ (not
only split ones). This is the $\mathfrak b = 1$ term of the orbital Euler product; unlike the full series it needs no absolute
convergence over the ideals, so it holds from $N = 4$ on. With $\tau(SO(Q_0)) = \tau(SO(Q_0')) = 2$ it is `SiegelFormulaAt Q₀ m`
(`siegelFormulaAt_of_local`); when $Q_0$ does not represent $m$ over $F$ both sides vanish (Hasse–Minkowski gives a prime with
$\beta_\mathfrak p(L, m) = 0$).

**The induction** ($\mathcal O_F$ a PID, $[F:\mathbb Q] \ge 2$), on two named inputs:
* `TernaryTamagawaTwo F` (rank 3; reduced from rank 4 in `TauFour`, `TernaryReduction`);
* `OddRankOrbitalLocalIdentities F`: `OrbitalLocalIdentities Q₀` for the totally positive definite $Q_0$ of **odd** rank $\ge 5$ (the subject of `OrbitalNonStd`).
Even ranks $2k \ge 4$ need no local input: Siegel's formula for numbers is a theorem there (Hilbert modular forms of
integral weight $k$) and the step `tamagawaNumberTwo_succ'` gives $\tau_{2k} = 2$ from $\tau_{2k-1} = 2$ for split lattices; the change of lattice (`LatChange.tauSO_smul_compMat`) extends it to every genus. Odd ranks $2k+1 \ge 5$ use the step
`tamagawaNumberTwo_of_complement`. Headlines: `tamagawaNumberTwo_all_ranks`, `massFormula_all_ranks`, `siegelFormulaAt_all_ranks`,
`siegelFormula_genusAvg_all_ranks`; for odd rank, `siegelFormulaAt_odd` and `siegelFormula_odd_aENF` (the formula, no
half-integral weight).
-/
import QuadFormsKB.Tamagawa.OrbitalEuler
import QuadFormsKB.Tamagawa.TernaryReduction

open NumberField Matrix Filter Topology
open scoped Real

noncomputable section

namespace QuadFormsKB.Tamagawa

open Lattices LocalDensity QuadForm IsDedekindDomain QuadFormsKB.HilbertModular

/-! ### Local densities at integral elements -/

section Beta

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/-- `betaZ` at an element of $\mathcal O_F$ is the local density $\beta_\mathfrak p(L, m)$ of `siegelProduct`. -/
theorem betaZ_algebraMap {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (m : 𝓞 F) :
    betaZ v Q₀ (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F m)) = NF.localDensity v Q₀ m := by
  have e : algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F m) =
      ((NF.ι v m : v.adicCompletionIntegers F) : v.adicCompletion F) := rfl
  have h : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F m)) ≤ 1 := by
    rw [e]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (NF.ι v m).2
  unfold betaZ
  rw [dif_pos h, NF.localDensity_eq_completion]
  rfl

/-- $\beta_\mathfrak p(L, t) \ge 0$ (an eventual normalized count). -/
theorem betaZ_nonneg {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate) {t : v.adicCompletion F}
    (ht : t ≠ 0) : 0 ≤ betaZ v Q₀ t := by
  unfold betaZ
  split_ifs with h
  · obtain ⟨k, hk⟩ := (DVR.localDensity_eventually_eq (NF.Qp v Q₀) (NF.nondegenerate_Qp v hQ) (NF.π v)
      (NF.irreducible_π v) ⟨t, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr h⟩
      (fun h0 => ht (congrArg Subtype.val h0)) (NF.two_ne_zero' v)).exists
    rw [← hk]
    positivity
  · exact le_rfl

end Beta

/-! ### Siegel's theorem for one number, with the stabilizer's $\tau$ -/

section PerNumber

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-- **The product formula for the frame Jacobians**: $\prod_\mathfrak p|\det g|_\mathfrak p^{n+1}|2\rho|_\mathfrak p^{-n} = \prod_\sigma|\sigma\det g|^{-(n+1)}|\sigma(2\rho)|^n$. -/
theorem finprod_frameJac {Q : QuadForm F (n + 1)} {ρ : F} (fr : AdaptedFrame Q ρ) (hρ : ρ ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (n + 1) /
        ‖algebraMap F (v.adicCompletion F) (2 * ρ)‖ ^ n =
      ∏ σ : F →ₐ[ℚ] ℂ, (‖σ fr.g.val.det‖ ^ (n + 1))⁻¹ * ‖σ (2 * ρ)‖ ^ n := by
  classical
  have hdet : fr.g.val.det ≠ 0 := (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero
  have h2ρ : (2 * ρ : F) ≠ 0 := mul_ne_zero two_ne_zero hρ
  have hfin := (finite_valuation_ne_one hdet).union (finite_valuation_ne_one h2ρ)
  set T := hfin.toFinset
  have hT : ∀ v ∉ T, v.valuation F fr.g.val.det = 1 ∧ v.valuation F (2 * ρ) = 1 := by
    intro v hv
    simp only [T, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hv
    exact hv
  set A : HeightOneSpectrum (𝓞 F) → ℝ := fun v => ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖
  set B : HeightOneSpectrum (𝓞 F) → ℝ := fun v => ‖algebraMap F (v.adicCompletion F) (2 * ρ)‖
  have hA : ∏ᶠ v, A v = ∏ v ∈ T, A v := finprod_eq_prod_of_one T fun v hv => norm_algebraMap_eq_one (hT v hv).1
  have hB : ∏ᶠ v, B v = ∏ v ∈ T, B v := finprod_eq_prod_of_one T fun v hv => norm_algebraMap_eq_one (hT v hv).2
  have hET : ∏ᶠ v, A v ^ (n + 1) / B v ^ n = ∏ v ∈ T, A v ^ (n + 1) / B v ^ n :=
    finprod_eq_prod_of_one T fun v hv => by
      simp only [A, B, norm_algebraMap_eq_one (hT v hv).1, norm_algebraMap_eq_one (hT v hv).2, one_pow, div_one]
  show ∏ᶠ v, A v ^ (n + 1) / B v ^ n = _
  rw [hET, Finset.prod_div_distrib, Finset.prod_pow, Finset.prod_pow, ← hA, ← hB]
  simp only [A, B]
  rw [finprod_norm_eq _ hdet, finprod_norm_eq _ h2ρ, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    Finset.prod_pow, Finset.prod_pow, inv_pow, inv_pow, div_inv_eq_mul]

/-- **The archimedean fibration at one embedding** for a frame ($a = \sigma\rho$, $c = |\sigma\det g|$, $D' = \det A'_\sigma$, $D_0 = aD'/c^2$):
$\mathrm{vol}(SO_{n+1}, D_0)\,c^{-(n+1)}(2a)^n = \mathrm{vol}(SO_n, D')\,\beta_\infty(a)$ (`archVolSO_succ` in the frame's coordinates). -/
theorem arch_place_siegel (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀)) {ρ : F}
    (fr : AdaptedFrame (formF Q₀) ρ) (hρ : ρ ≠ 0) (σ : F →ₐ[ℚ] ℂ) :
    archVolSO (n + 1) (detGram Q₀ σ) * ((‖σ fr.g.val.det‖ ^ (n + 1))⁻¹ * ‖σ (2 * ρ)‖ ^ n) =
      archVolSO n (detGram fr.Q' σ) * archRepDensity (n + 1) ‖σ ρ‖ (detGram Q₀ σ) := by
  have hQF := hpd.nondegenerate
  have hQ'nd := fr.nondegenerate hQF hρ
  set a := ‖σ ρ‖
  set c := ‖σ fr.g.val.det‖
  set D' := detGram fr.Q' σ
  have ha : 0 < a := norm_pos_iff.mpr ((map_ne_zero σ).mpr hρ)
  have hc : 0 < c := norm_pos_iff.mpr ((map_ne_zero σ).mpr (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero)
  have hD' : 0 < D' := by
    refine norm_pos_iff.mpr ((map_ne_zero σ).mpr (div_ne_zero ?_ (pow_ne_zero _ two_ne_zero)))
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ'nd
  have hD₀ : detGram Q₀ σ = a * (D' / c ^ 2) := by
    rw [← mul_div_assoc, eq_div_iff (by positivity)]; exact detGram_frame Q₀ fr σ
  have h2ρ : ‖σ (2 * ρ)‖ = 2 * a := by rw [map_mul, norm_mul, map_ofNat, Complex.norm_ofNat]
  have h1 := archVolSO_succ n ha (show 0 < D' / c ^ 2 by positivity)
  rw [archVolSO_div_sq n hD' hc] at h1
  rw [hD₀, h2ρ]
  have hc' : c ^ (n + 1) ≠ 0 := by positivity
  calc archVolSO (n + 1) (a * (D' / c ^ 2)) * ((c ^ (n + 1))⁻¹ * (2 * a) ^ n)
      = archVolSO (n + 1) (a * (D' / c ^ 2)) * (2 * a) ^ n * (c ^ (n + 1))⁻¹ := by ring
    _ = _ := by rw [h1]; field_simp

/-- `two_mul_tamagawaK_mul_repMass_frame` with the number written as $\rho \in F$, $\rho = m$. -/
theorem two_mul_tamagawaK_mul_repMass_frame_aux (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀))
    (hn : 3 ≤ n) {m : 𝓞 F} {ρ : F} (hmρ : algebraMap (𝓞 F) F m = ρ) (hm : ∀ v : InfinitePlace F, 0 < realEmb F v ρ)
    (fr : AdaptedFrame (formF Q₀) ρ) (hgli : ∀ v, OrbitalLocalIdentityAt v Q₀ fr) :
    2 * tamagawaK Q₀ * repMass (formF Q₀) (stdLat F (n + 1)) ρ = tauSO fr.Q' * siegelProduct Q₀ m := by
  classical
  have hρ : ρ ≠ 0 := by
    intro h; obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have := hm w; rw [h, map_zero] at this; exact lt_irrefl 0 this
  have hQF : (formF Q₀).Nondegenerate := hpd.nondegenerate
  have hQ₀ : Q₀.Nondegenerate := by
    have := hQF
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    exact fun h => this (by rw [h, map_zero])
  have hQ'nd : fr.Q'.Nondegenerate := fr.nondegenerate hQF hρ
  set QF' := fr.Q'.map (algebraMap (𝓞 F) F)
  have hpd' : IsTotallyPosDef QF' := by
    have h1 := isTotallyPosDef_compMat (formF Q₀) fr.g hpd
    rw [fr.compMat_eq] at h1
    exact isTotallyPosDef_of_splitForm h1
  -- the local factors
  set W0 : HeightOneSpectrum (𝓞 F) → ℝ := fun v => locW v fr 0
  set α : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v Q₀ Q₀
  set α' : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v fr.Q' fr.Q'
  set E : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (n + 1) / ‖algebraMap F (v.adicCompletion F) (2 * ρ)‖ ^ n
  set β : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.localDensity v Q₀ m
  have hEpos : ∀ v, 0 < E v := fun v => by
    have h1 : algebraMap F (v.adicCompletion F) fr.g.val.det ≠ 0 :=
      (map_ne_zero _).mpr (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero
    have h2 : algebraMap F (v.adicCompletion F) (2 * ρ) ≠ 0 := (map_ne_zero _).mpr (mul_ne_zero two_ne_zero hρ)
    exact div_pos (pow_pos (norm_pos_iff.mpr h1) _) (pow_pos (norm_pos_iff.mpr h2) _)
  have hαpos : ∀ v, 0 < α v := fun v => siegelDensity_pos v Q₀ hQ₀
  have hα'pos : ∀ v, 0 < α' v := fun v => siegelDensity_pos v fr.Q' hQ'nd
  -- the local identity at `j = 0`
  have hW : ∀ v, W0 v = α' v * E v * β v / α v := by
    intro v
    have hj := (hgli v).eq 0
    simp only [zero_mul, zpow_zero, mul_zero, mul_one] at hj
    rw [show (2 : v.adicCompletion F) * algebraMap F (v.adicCompletion F) ρ =
      algebraMap F (v.adicCompletion F) (2 * ρ) by rw [map_mul, map_ofNat]] at hj
    have hb : betaZ v Q₀ (algebraMap F (v.adicCompletion F) ρ) = β v := by
      rw [← hmρ]; exact betaZ_algebraMap v Q₀ m
    rw [hb] at hj
    have hdet : 0 < ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (n + 1) :=
      pow_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero)) _
    have h2ρ : 0 < ‖algebraMap F (v.adicCompletion F) (2 * ρ)‖ ^ n :=
      pow_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr (mul_ne_zero two_ne_zero hρ))) _
    have hα : 0 < NF.siegelDensity v Q₀ Q₀ := siegelDensity_pos v Q₀ hQ₀
    simp only [W0, E, α, α']
    generalize ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (n + 1) = D at hj hdet ⊢
    generalize ‖algebraMap F (v.adicCompletion F) (2 * ρ)‖ ^ n = B2 at hj h2ρ ⊢
    rw [eq_div_iff hα.ne']
    calc locW v fr 0 * NF.siegelDensity v Q₀ Q₀
        = locW v fr 0 * NF.siegelDensity v Q₀ Q₀ * B2 * D⁻¹ * D / B2 := by field_simp
      _ = _ := by rw [hj]; ring
  -- `W0` has finite support (one local type of weight 1 at the standard primes)
  have hfin₀ : {v : HeightOneSpectrum (𝓞 F) | frameLat v fr.g ≠ std v ∨ v.valuation F ρ ≠ 1 ∨
      v.valuation F 2 ≠ 1}.Finite := by
    refine ((Filter.eventually_cofinite.mp (loc_eventually_std (glImage_isLattice fr.g⁻¹ intVec_isLattice))).union
      ((finite_valuation_ne_one hρ).union (finite_valuation_ne_one (two_ne_zero (α := F))))).subset fun v hv => ?_
    simpa [frameLat, or_assoc] using hv
  have hW0fin : Function.HasFiniteMulSupport W0 := by
    refine hfin₀.subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_setOf_eq, not_or, not_not] at h
    apply hv
    show locW v fr 0 = 1
    unfold locW
    rw [zpow_zero, h.1]
    exact locTypeSumG_std_one_of_units v fr.Q' hQ'nd h.2.1 h.2.2
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
  have hA : 0 < ∏' v, α v := tprod_siegelDensity_pos (N := n + 1) (by omega) Q₀ hQ₀
  have hW0p : HasProd W0 (∏ᶠ v, W0 v) := by
    have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hW0fin).hasProd
    rwa [tprod_eq_finprod hW0fin] at this
  have hEp : HasProd E (∏ᶠ v, E v) := by
    have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hEfin).hasProd
    rwa [tprod_eq_finprod hEfin] at this
  have hEprod : 0 < ∏ᶠ v, E v := by
    rw [finprod_eq_prod_of_mulSupport_subset E (s := hEfin.toFinset) fun v hv => (Set.Finite.mem_toFinset _).mpr hv]
    exact Finset.prod_pos fun v _ => hEpos v
  have hβeq : β = fun v => W0 v * α v / (α' v * E v) := by
    funext v
    rw [hW v]
    have := hα'pos v; have := hEpos v; have := hαpos v
    field_simp
  have hβp : HasProd β ((∏ᶠ v, W0 v) * (∏' v, α v) / ((∏' v, α' v) * ∏ᶠ v, E v)) := by
    rw [hβeq]
    exact (hW0p.mul hαm.hasProd).div₀ (hα'm.hasProd.mul hEp) (mul_pos hA' hEprod).ne'
  -- `repMass` through the frame
  have hrep : repMass (formF Q₀) (stdLat F (n + 1)) ρ = mass QF' (stdLat F n) * ∏ᶠ v, W0 v := by
    have h1 := repMass_eq_mass_mul_finprod Q₀ hpd hρ fr (β := 1) one_ne_zero
    rw [one_pow, one_mul] at h1
    rw [h1]
    congr 1
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
  rw [hrep, htau, siegelProduct, hmρ, hβp.tprod_eq]
  unfold tamagawaK
  rw [hδe]
  set M := mass QF' (stdLat F n)
  set P := ∏ᶠ v, W0 v
  set A := ∏' v, α v
  set A' := ∏' v, α' v
  set Ep := ∏ᶠ v, E v
  set V₀ := ∏ σ : F →ₐ[ℚ] ℂ, archVolSO (n + 1) (detGram Q₀ σ)
  set V' := ∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram fr.Q' σ)
  set R := ∏ σ : F →ₐ[ℚ] ℂ, archRepDensity (n + 1) ‖σ ρ‖ (detGram Q₀ σ)
  have hdiv : P * A / (A' * Ep) * (A' * Ep) = P * A := div_mul_cancel₀ _ (mul_pos hA' hEprod).ne'
  calc 2 * (δ ^ (-((n : ℝ) * ((n : ℝ) - 1) / 4)) * δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2) * V₀ * A) * (M * P)
      = 2 * δ ^ (-((n : ℝ) * ((n : ℝ) - 1) / 4)) * δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2) * M *
          (P * A / (A' * Ep) * (A' * Ep)) * V₀ := by rw [hdiv]; ring
    _ = 2 * δ ^ (-((n : ℝ) * ((n : ℝ) - 1) / 4)) * δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2) * M *
          (P * A / (A' * Ep)) * A' * (V₀ * Ep) := by ring
    _ = _ := by rw [key]; ring

/-- **Siegel's theorem for one number, with the stabilizer's Tamagawa number** (Weil 1982, §4.5, p. 109; §3.4–3.5 [unverified locator]; the
$\mathfrak b = 1$ term of the orbital Euler product). For $Q_0$ totally positive definite over $\mathcal O_F$ in $N = n + 1 \ge 4$
variables ($F$ totally real, any class number), $m \in \mathcal O_F$ totally positive, an adapted frame $Q_0\circ g = \langle m\rangle\perp Q_0'$ and
the local orbital identity of the frame at every prime (`OrbitalLocalIdentityAt`),
$$2\,\mu_{\mathrm{Tam}}(K_{SO}(Q_0))\cdot\mathrm{repMass}(\mathcal O_F^N, m) = \tau(SO(Q_0'))\cdot S(L, m),$$
$S$ = `siegelProduct` $= |d_F|^{-(N-1)/2}\prod_\sigma\beta_\sigma(m)\prod_\mathfrak p\beta_\mathfrak p(L, m)$ (the $|d_F|$ power is the proved erratum).
*Proof.* `repMass_eq_mass_mul_finprod` ($\beta = 1$): $\mathrm{repMass} = \mathrm{Mass}(Q_0')\prod_\mathfrak pW_\mathfrak p(0)$; the local identity at $j = 0$ gives
$W_\mathfrak p(0) = \alpha_\mathfrak p(Q_0')\,|\det g|_\mathfrak p^{n+1}|2m|_\mathfrak p^{-n}\,\beta_\mathfrak p(L, m)/\alpha_\mathfrak p(Q_0)$; the product formula and
`archVolSO_succ` at each real place turn the Jacobians into the archimedean densities. -/
@[kb "weil1982" "§4.5, p. 100 and p. 109 (Siegel's theorem from the fibration over T(ρ), one number) [unverified]"]
theorem two_mul_tamagawaK_mul_repMass_frame (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀))
    (hn : 3 ≤ n) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (fr : AdaptedFrame (formF Q₀) (algebraMap (𝓞 F) F m)) (hgli : ∀ v, OrbitalLocalIdentityAt v Q₀ fr) :
    2 * tamagawaK Q₀ * repMass (formF Q₀) (stdLat F (n + 1)) (algebraMap (𝓞 F) F m) =
      tauSO fr.Q' * siegelProduct Q₀ m :=
  two_mul_tamagawaK_mul_repMass_frame_aux Q₀ hpd hn rfl hm fr hgli

end PerNumber

/-! ### Numbers not represented over $F$: both sides vanish -/

section NotRep

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

open QuadFormsKB.SphericalFibration QuadFormsKB.SphericalZeta in
/-- If $Q$ does not represent $\rho$ over $F_\mathfrak p$, then $\beta_\mathfrak p(L, \rho) = 0$ (the spherical factor $Z_\mathfrak p(0, \rho)$ is the integral over an
empty set, and it is a series of the nonnegative numbers $|\varpi^{2j}|\beta_\mathfrak p(\rho\varpi^{2j})$, `hasSum_betaZ_series`). -/
theorem betaZ_eq_zero_of_not_rep {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate) (hN : 1 ≤ N)
    (v : HeightOneSpectrum (𝓞 F)) {ρ : F} (hρ : ρ ≠ 0) (hp : ¬ (formF Q₀).RepresentsIn (v.adicCompletion F) ρ) :
    betaZ v Q₀ (algebraMap F (v.adicCompletion F) ρ) = 0 := by
  have hρv : algebraMap F (v.adicCompletion F) ρ ≠ 0 := (map_ne_zero _).mpr hρ
  have hempty : LocalZeta.latL v N ∩ (NF.Qp v Q₀).evalIn (v.adicCompletion F) ⁻¹'
      sqClass (algebraMap F (v.adicCompletion F) ρ) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_empty_iff_false, iff_false, not_and]
    rintro - ⟨y, hy, hxy⟩
    apply hp
    refine ⟨y⁻¹ • x, ?_⟩
    rw [evalIn_smul', evalIn_formF, ← NF.evalIn_Qp v, hxy]
    field_simp
  have hZ : sphLocal Q₀ v (algebraMap F (v.adicCompletion F) ρ) 0 = 0 := by
    unfold sphLocal sphInt
    rw [hempty, MeasureTheory.Measure.restrict_empty, MeasureTheory.integral_zero_measure, mul_zero, zero_div]
  have hS := hasSum_betaZ_series v Q₀ hQ hN hρv (s := 0) le_rfl
  rw [hZ, mul_zero, mul_zero] at hS
  have hϖ0 : unifV v ≠ 0 := by
    have hvϖ : Valued.v (unifV v) = WithZero.exp (-1 : ℤ) := NF.valued_π v
    intro h; rw [h, map_zero] at hvϖ; exact WithZero.zero_ne_coe hvϖ
  have hnn : ∀ j : ℤ, 0 ≤ ‖unifV v ^ (2 * j)‖ ^ (1 + (0 : ℝ)) *
      betaZ v Q₀ (algebraMap F (v.adicCompletion F) ρ * unifV v ^ (2 * j)) := fun j =>
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (betaZ_nonneg v Q₀ hQ (mul_ne_zero hρv (zpow_ne_zero _ hϖ0)))
  have h0 := congrFun ((hasSum_zero_iff_of_nonneg hnn).mp hS) 0
  simpa using h0

/-- If $Q$ does not represent $m$ over $F$, no lattice in $(F^N, Q)$ does: $\mathrm{repMass}(L, m) = 0$. -/
theorem repMass_eq_zero_of_not_rep {N : ℕ} (Q : QuadForm F N) (L : Lat F N) {t : F}
    (h : ¬ ∃ ξ : Fin N → F, Q.eval ξ = t) : repMass Q L t = 0 := by
  unfold repMass
  have hz : ∀ c ∈ genusClasses Q L, (LatClass.repCount Q c t : ℝ) / LatClass.autCard Q c = 0 := by
    intro c _
    rw [latClass_repCount_eq]
    have : repCount Q c.out t = 0 := by
      unfold repCount
      rw [Nat.card_eq_zero]
      left
      exact ⟨fun x => h ⟨x.1, x.2.2⟩⟩
    rw [this, Nat.cast_zero, zero_div]
  exact (finsum_mem_congr rfl hz).trans (finsum_mem_zero _)

/-- If $Q$ does not represent the totally positive $m$ over $F$, then $S(L, m) = 0$: by Hasse–Minkowski
(`represents_iff_everywhere_nf`) some completion does not represent $m$; it is not a real one ($Q$ is totally positive definite), so it is
a prime with $\beta_\mathfrak p(L, m) = 0$. -/
theorem siegelProduct_eq_zero_of_not_rep (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (h : ¬ ∃ ξ, (formF Q₀).eval ξ = algebraMap (𝓞 F) F m) : siegelProduct Q₀ m = 0 := by
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
    have h0 : NF.localDensity v Q₀ m = 0 := by
      rw [← betaZ_algebraMap]; exact betaZ_eq_zero_of_not_rep Q₀ hQ₀ (by omega) v hρ hp
    unfold siegelProduct
    rw [tprod_of_exists_eq_zero ⟨v, h0⟩, mul_zero]

end NotRep

/-! ### Siegel's formula for every form, from $\tau = 2$ in ranks $N$ and $N - 1$ -/

section SiegelLocal

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-- **Siegel's formula for numbers, for every totally positive definite form, from $\tau = 2$** (Weil 1982, §4.5, p. 100 [unverified]): for
$Q_0$ totally positive definite over $\mathcal O_F$ in $N = n + 1 \ge 4$ variables ($F$ totally real, any class number), if $\tau(SO(Q_0)) = 2$,
$\tau(SO(Q')) = 2$ for every totally positive definite $Q'$ in $n$ variables over $\mathcal O_F$, and the local orbital identities of $Q_0$ hold
at the non-standard primes of its frames (`OrbitalLocalIdentities`), then for every totally positive $m \in \mathcal O_F$
$$\sum_{\mathrm{cls}M\subseteq\mathrm{gen}\,\mathcal O_F^N}\frac{r_M(m)}{|O(M)|} = \mathrm{Mass}(\mathcal O_F^N)\cdot|d_F|^{-\frac{N-1}2}\prod_\sigma\beta_\sigma(m)\prod_\mathfrak p\beta_\mathfrak p(L, m)$$
(`SiegelFormulaAt Q₀ m`). No split shape and no condition on the lattice: the frame $Q_0\circ g = \langle m\rangle\perp Q'$ is over $F$. -/
@[kb "weil1982" "§4.5, p. 100 (Siegel's theorem from τ = 2), for every form [unverified]"]
theorem siegelFormulaAt_of_local (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀)) (hn : 3 ≤ n)
    (hloc : OrbitalLocalIdentities Q₀) (hτ : TamagawaNumberTwo Q₀)
    (hτ' : ∀ Q' : QuadForm (𝓞 F) n, IsTotallyPosDef (formF Q') → TamagawaNumberTwo Q')
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt Q₀ m := by
  refine ⟨?_⟩
  have hρ : algebraMap (𝓞 F) F m ≠ 0 := by
    intro h0; obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have := hm w; rw [h0, map_zero] at this; exact lt_irrefl 0 this
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  show repMass (formF Q₀) (stdLat F (n + 1)) (algebraMap (𝓞 F) F m) =
    mass (formF Q₀) (stdLat F (n + 1)) * siegelProduct Q₀ m
  by_cases h : ∃ ξ, (formF Q₀).eval ξ = algebraMap (𝓞 F) F m
  · obtain ⟨ξ, hξ⟩ := h
    obtain ⟨fr⟩ := exists_adaptedFrame (formF Q₀) hξ hρ
    have hpd' : IsTotallyPosDef (formF fr.Q') := by
      have h1 := isTotallyPosDef_compMat (formF Q₀) fr.g hpd
      rw [fr.compMat_eq] at h1
      exact isTotallyPosDef_of_splitForm h1
    have key := two_mul_tamagawaK_mul_repMass_frame Q₀ hpd hn hm fr
      (fun v => orbitalLocalIdentityAt_all hloc hQ₀ (by omega) hρ fr v)
    rw [show tauSO fr.Q' = 2 from hτ' fr.Q' hpd'] at key
    have hmass := massFormula Q₀ hQ₀ (by omega) hpd (HilbertModular.isIntegral_stdLat Q₀) hτ
    have hpos := mass_pos hpd (stdLat F (n + 1)) (HilbertModular.isIntegral_stdLat Q₀)
    have hμ : tamagawaK Q₀ ≠ 0 := by
      intro h0; rw [hmass, h0, _root_.inv_zero] at hpos; exact lt_irrefl 0 hpos
    rw [hmass]
    field_simp
    linarith
  · rw [repMass_eq_zero_of_not_rep _ _ h, siegelProduct_eq_zero_of_not_rep Q₀ hpd hm h, mul_zero]

end SiegelLocal

/-! ### Weil's induction: $\tau(SO) = 2$ in every rank $N \ge 3$ -/

section Induction

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-- **Input: the local orbital identities in odd rank $\ge 5$** (Weil 1982, §3.4 and §4.5, p. 109 [unverified]; Kitaoka 1993, §5.6
[unverified]): `OrbitalLocalIdentities Q₀` for every totally positive definite $Q_0$ over $\mathcal O_F$ in $n + 1$ variables,
$n \ge 4$ even (so $N = n + 1 = 5, 7, 9, \dots$).

Field:
- `odd`: the statement above.

*Why only odd rank.* In even rank $2k \ge 4$ Siegel's formula for numbers is a theorem (Hilbert modular forms of integral
weight $k$), and the step then gives $\tau_{2k} = 2$ from $\tau_{2k-1} = 2$ with no local input; the local identities are needed only
for the step into odd rank, and for Siegel's formula in odd rank. *Hygiene.* A family of purely local statements (one prime at a time,
local densities and index ratios of compact open subgroups); it mentions no class, mass or $\tau$, and it is not equivalent to any
conclusion it is used for. When `OrbitalLocalIdentities` is proved for all forms, `OddRankOrbitalLocalIdentities.of_all` discharges it. -/
@[kb "weil1982" "§3.4 and §4.5, p. 109 (local fibration at the non-standard primes), odd rank ≥ 5 [unverified]"]
structure OddRankOrbitalLocalIdentities (F : Type) [Field F] [NumberField F] [IsTotallyReal F] : Prop where
  odd : ∀ n : ℕ, 4 ≤ n → Even n → ∀ Q₀ : QuadForm (𝓞 F) (n + 1), IsTotallyPosDef (formF Q₀) →
    OrbitalLocalIdentities Q₀

/-- The odd-rank input from the local identities for all forms (the one-line discharge once they are proved). -/
theorem OddRankOrbitalLocalIdentities.of_all
    (h : ∀ (n : ℕ) (Q₀ : QuadForm (𝓞 F) (n + 1)), IsTotallyPosDef (formF Q₀) → OrbitalLocalIdentities Q₀) :
    OddRankOrbitalLocalIdentities F :=
  ⟨fun n _ _ Q₀ hpd => h n Q₀ hpd⟩

/-- **Input (rank 4): $\tau(SO_4) = 2$ for every totally positive definite quaternary form over $\mathcal O_F$** (Weil 1982, §3.7,
Thm. 3.7.1 ($m = 4$), p. 65).

Field:
- `tau_eq_two`: the statement above.

*Status.* For $[F:\mathbb Q] \ge 2$ and $\mathcal O_F$ a PID it is equivalent to `TernaryTamagawaTwo F` (`LatChange.ternaryTamagawaTwo_iff_four_all`) and follows from it (`quaternaryTamagawaTwo_of_ternary`). It is a separate name only so that the
induction can be stated over $\mathbb Q$; there it is equivalent to `TernaryTamagawaTwo ℚ` too (`RatBridge.ternaryTamagawaTwo_iff_quaternary_rat`, rank-4
Siegel through the bridge). Not equivalent to
any conclusion it is used for (ranks $\ge 5$). -/
@[kb "weil1982" "§3.7, Thm. 3.7.1 (m = 4), p. 65"]
structure QuaternaryTamagawaTwo (F : Type) [Field F] [NumberField F] : Prop where
  tau_eq_two : ∀ Q₀ : QuadForm (𝓞 F) 4, IsTotallyPosDef (formF Q₀) → TamagawaNumberTwo Q₀

variable [IsPrincipalIdealRing (𝓞 F)]

/-- The rank-4 input from the rank-3 one ($[F:\mathbb Q] \ge 2$, $\mathcal O_F$ a PID; `tamagawaNumberTwo_four_all`). -/
theorem quaternaryTamagawaTwo_of_ternary (hd : 2 ≤ Fintype.card (InfinitePlace F)) (hT : TernaryTamagawaTwo F) :
    QuaternaryTamagawaTwo F :=
  ⟨fun Q₀ hpd => LatChange.tamagawaNumberTwo_four_all hT hd Q₀ (nondegenerate_of_map hpd.nondegenerate) hpd⟩

/-- **Reduction to split lattices** (the change of lattice): if $\tau = 2$ for every totally positive definite $\langle m_0\rangle\perp Q_0'$
over $\mathcal O_F$ in $n + 1$ variables, then for every totally positive definite form in $n + 1$ variables ($n \ge 2$, $\mathcal O_F$ a PID).
*Proof:* $Q_0\circ G = \langle e_0, \dots, e_n\rangle = \langle e_0\rangle\perp\langle e_1,\dots,e_n\rangle$ (`exists_compMat_eq_diag`) and
$\tau(Q_0\circ G) = \tau(Q_0)$ (`tauSO_smul_compMat`). -/
theorem tamagawaNumberTwo_of_split {n : ℕ} (hn : 2 ≤ n)
    (h : ∀ (m₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n), (∀ v, 0 < realEmb F v (algebraMap (𝓞 F) F m₀)) →
      IsTotallyPosDef (formF (splitForm m₀ Q₀')) → TamagawaNumberTwo (splitForm m₀ Q₀'))
    (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ := by
  have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  obtain ⟨G, hG, e, he, hGe⟩ := LatChange.exists_compMat_eq_diag Q₀ hQ
  have hGF : (G.map (algebraMap (𝓞 F) F)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hG
  have hpdD : IsTotallyPosDef ((QuadForm.diag e).map (algebraMap (𝓞 F) F)) := by
    rw [← hGe, ← map_compMat]
    exact LatChange.isTotallyPosDef_compMat_of_det hpd hGF
  have h1 := LatChange.tauSO_smul_compMat (by omega) (by omega) Q₀ hQ hpd one_ne_zero G hG (by
    rw [show (1 : 𝓞 F) • Q₀.compMat G = Q₀.compMat G by ext a b; simp [smul_coeff], hGe]; exact hpdD)
  rw [show (1 : 𝓞 F) • Q₀.compMat G = Q₀.compMat G by ext a b; simp [smul_coeff], hGe] at h1
  unfold TamagawaNumberTwo
  rw [← h1, LatChange.diag_eq_splitForm]
  rw [LatChange.diag_eq_splitForm] at hpdD
  have he0 : IsTotallyPos (((e 0 : 𝓞 F)) : F) := by
    have := hpdD (Pi.single 0 1) (by simp)
    rw [eval_single] at this
    simpa [QuadForm.map, splitForm_coeff] using this
  exact h _ _ (fun v => LatChange.realEmb_pos_of_isTotallyPos he0 v) hpdD

/-- **The even step** $\tau_{2k-1} = 2 \Rightarrow \tau_{2k} = 2$ ($2k \ge 4$; for $2k = 4$ also $[F:\mathbb Q] \ge 2$), with **no local input**: Siegel's
formula for numbers in rank $2k$ is a theorem (Hilbert modular forms: `siegelFormulaAt_of_pid`, `siegelFormulaAt_of_pid_four`), and the step
`tamagawaNumberTwo_succ'` (the local orbital identity proved at every prime) gives $\tau = 2$ for split lattices; then
`tamagawaNumberTwo_of_split`. -/
@[kb "weil1982" "Thm. 4.5.1, p. 109 (even rank, via Siegel's theorem as in §4.5, p. 100)"]
theorem tamagawaNumberTwo_even_step {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    (hd : n = 3 → 2 ≤ Fintype.card (InfinitePlace F))
    (hIH : ∀ Q' : QuadForm (𝓞 F) n, IsTotallyPosDef (formF Q') → TamagawaNumberTwo Q')
    (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ := by
  refine tamagawaNumberTwo_of_split (by omega) (fun m₀ Q₀' hm hpds => ?_) Q₀ hpd
  have hm0 : m₀ ≠ 0 := by
    rintro rfl
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    simpa using hm v
  have hpd' : IsTotallyPosDef (formF Q₀') := by
    have := isTotallyPosDef_of_splitForm (m := algebraMap (𝓞 F) F m₀) (Q' := Q₀'.map (algebraMap (𝓞 F) F))
      (by rw [← map_splitForm]; exact hpds)
    exact this
  have hQ' : Q₀'.Nondegenerate := nondegenerate_of_map hpd'.nondegenerate
  have hS : SiegelFormulaAt (splitForm m₀ Q₀') m₀ := by
    obtain ⟨k, hk⟩ := hodd
    by_cases h3 : n = 3
    · exact HilbertModular.siegelFormulaAt_of_pid_four hpds (by omega) (hd h3) hm
    · exact HilbertModular.siegelFormulaAt_of_pid hpds (k := k + 1) (by omega) (by omega) hm
  exact tamagawaNumberTwo_succ' m₀ hm0 Q₀' hn hpds (HilbertModular.isIntegral_stdLat _) hS
    (massFormula Q₀' hQ' (by omega) hpd' (HilbertModular.isIntegral_stdLat _) (hIH Q₀' hpd'))

/-- **Weil's induction from rank 4** ($\mathcal O_F$ a PID, any totally real $F$, $\mathbb Q$ included): given $\tau(SO_4) = 2$
(`QuaternaryTamagawaTwo F`) and the local orbital identities in odd rank (`OddRankOrbitalLocalIdentities F`), $\tau(SO(Q_0)) = 2$ for every
totally positive definite $Q_0$ over $\mathcal O_F$ in $N \ge 4$ variables. Odd $N$: `tamagawaNumberTwo_of_complement`; even $N \ge 6$:
`tamagawaNumberTwo_even_step` (no local input). -/
@[kb "weil1982" "Thm. 4.5.1, p. 109 (induction on the dimension from m = 4)"]
theorem tamagawaNumberTwo_of_four (h4 : QuaternaryTamagawaTwo F) (hloc : OddRankOrbitalLocalIdentities F) {N : ℕ}
    (hN : 4 ≤ N) (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ := by
  revert Q₀
  induction N, hN using Nat.le_induction with
  | base => exact h4.tau_eq_two
  | succ n hn ih =>
    intro Q₀ hpd
    rcases Nat.even_or_odd n with he | ho
    · exact tamagawaNumberTwo_of_complement Q₀ hpd hn (hloc.odd n hn he Q₀ hpd) ih
    · exact tamagawaNumberTwo_even_step (by omega) ho (fun h => absurd h (by omega)) ih Q₀ hpd

/-- **$\tau(SO) = 2$ in every rank $N \ge 3$** (Weil 1982, Thm. 4.5.1, p. 109, with the bases of Thm. 3.7.1, p. 65): for $F$ totally real
of degree $\ge 2$ with $\mathcal O_F$ a PID and every totally positive definite $Q_0$ over $\mathcal O_F$ in $N \ge 3$ variables,
$\tau(SO(Q_0)) = 2$ (`tauSO`), conditional on exactly two named inputs: `TernaryTamagawaTwo F` (rank 3) and
`OddRankOrbitalLocalIdentities F` (the local orbital identities in odd rank $\ge 5$). Rank 4: `TernaryReduction`; even rank $\ge 6$: the Siegel formula and the step; odd rank $\ge 5$: the step. -/
@[kb "weil1982" "Thm. 4.5.1, p. 109 and Thm. 3.7.1, p. 65 (τ(SO) = 2, m ≥ 3)"]
theorem tamagawaNumberTwo_all_ranks (hd : 2 ≤ Fintype.card (InfinitePlace F)) (hT : TernaryTamagawaTwo F)
    (hloc : OddRankOrbitalLocalIdentities F) {N : ℕ} (hN : 3 ≤ N) (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ := by
  rcases Nat.lt_or_ge N 4 with h | h
  · obtain rfl : N = 3 := by omega
    exact hT.tau_eq_two Q₀ (nondegenerate_of_map hpd.nondegenerate) hpd (HilbertModular.isIntegral_stdLat Q₀)
  · exact tamagawaNumberTwo_of_four (quaternaryTamagawaTwo_of_ternary hd hT) hloc h Q₀ hpd

/-- **The Smith–Minkowski–Siegel mass formula in every rank $N \ge 3$** (same hypotheses):
$\mathrm{Mass}(\mathcal O_F^N) = \mu_{\mathrm{Tam}}(K_{SO})^{-1} = |d_F|^{N(N-1)/4}\big(\prod_\sigma\mathrm{vol}(SO(V_\sigma))\big)^{-1}\big(\prod_\mathfrak p\alpha_\mathfrak p(L,L)\big)^{-1}$
(`massFormula`; the explicit Euler products are `massFormula_odd`/`massFormula_even`). -/
@[kb "kitaoka1993" "Thm 6.8.1 (mass formula), every rank ≥ 3, over totally real F [unverified]"]
theorem massFormula_all_ranks (hd : 2 ≤ Fintype.card (InfinitePlace F)) (hT : TernaryTamagawaTwo F)
    (hloc : OddRankOrbitalLocalIdentities F) {N : ℕ} (hN : 3 ≤ N) (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (formF Q₀)) : MassFormulaHolds Q₀ :=
  massFormula Q₀ (nondegenerate_of_map hpd.nondegenerate) (by omega) hpd (HilbertModular.isIntegral_stdLat Q₀)
    (tamagawaNumberTwo_all_ranks hd hT hloc hN Q₀ hpd)

/-! ### Siegel's formula in every rank $N \ge 4$ -/

/-- **Siegel's formula for numbers in odd rank** $N = n + 1 \ge 5$, for every totally positive definite form over $\mathcal O_F$ and every
totally positive $m$ (conditional on the two named inputs): `SiegelFormulaAt Q₀ m`. Odd rank needs no modular forms of half-integral
weight: it comes from $\tau = 2$ in ranks $N$ and $N - 1$ (`siegelFormulaAt_of_local`). -/
@[kb "siegel1935" "Hauptsatz (numbers), odd rank ≥ 5, over totally real F, via Weil 1982 §4.5 [unverified]"]
theorem siegelFormulaAt_odd (hd : 2 ≤ Fintype.card (InfinitePlace F)) (hT : TernaryTamagawaTwo F)
    (hloc : OddRankOrbitalLocalIdentities F) {n : ℕ} (hn : 4 ≤ n) (he : Even n) (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F} (hm : ∀ v, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_of_local Q₀ hpd (by omega) (hloc.odd n hn he Q₀ hpd)
    (tamagawaNumberTwo_all_ranks hd hT hloc (by omega) Q₀ hpd)
    (fun Q' hQ' => tamagawaNumberTwo_all_ranks hd hT hloc (by omega) Q' hQ') hm

/-- **Siegel's formula for numbers in every rank $N \ge 4$** ($F$ totally real of degree $\ge 2$, $\mathcal O_F$ a PID, $Q_0$ totally positive
definite over $\mathcal O_F$, $m \in \mathcal O_F$ totally positive):
$$\sum_{\mathrm{cls}M\subseteq\mathrm{gen}\,\mathcal O_F^N}\frac{r_M(m)}{|O(M)|} = \mathrm{Mass}(\mathcal O_F^N)\cdot|d_F|^{-\frac{N-1}2}\prod_\sigma\beta_\sigma(m)\prod_\mathfrak p\beta_\mathfrak p(L, m)$$
(`SiegelFormulaAt`). Even $N$: unconditional; odd $N$: conditional on `TernaryTamagawaTwo F` and
`OddRankOrbitalLocalIdentities F` (`siegelFormulaAt_odd`). -/
@[kb "siegel1935" "Hauptsatz (numbers), every rank ≥ 4, over totally real F [unverified]"]
theorem siegelFormulaAt_all_ranks (hd : 2 ≤ Fintype.card (InfinitePlace F)) (hT : TernaryTamagawaTwo F)
    (hloc : OddRankOrbitalLocalIdentities F) {N : ℕ} (hN : 4 ≤ N) (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F} (hm : ∀ v, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    SiegelFormulaAt Q₀ m := by
  rcases Nat.even_or_odd N with ⟨k, hk⟩ | ⟨k, hk⟩
  · by_cases h4 : N = 4
    · exact HilbertModular.siegelFormulaAt_of_pid_four hpd h4 hd hm
    · exact HilbertModular.siegelFormulaAt_of_pid hpd (k := k) (by omega) (by omega) hm
  · subst hk
    exact siegelFormulaAt_odd hd hT hloc (n := 2 * k) (by omega) (even_two_mul k) Q₀ hpd hm

/-- **The genus average in every rank $N \ge 4$** (Siegel's formula as $r_{\mathrm{gen}}(L, m) = S(L, m)$):
$\mathrm{Mass}(\mathcal O_F^N)^{-1}\,\mathrm{repMass}(\mathcal O_F^N, m) = |d_F|^{-(N-1)/2}\prod_\sigma\beta_\sigma(m)\prod_\mathfrak p\beta_\mathfrak p(L, m)$. -/
@[kb "siegel1935" "Hauptsatz: genus average = product of local densities, every rank ≥ 4 [unverified]"]
theorem siegelFormula_genusAvg_all_ranks (hd : 2 ≤ Fintype.card (InfinitePlace F)) (hT : TernaryTamagawaTwo F)
    (hloc : OddRankOrbitalLocalIdentities F) {N : ℕ} (hN : 4 ≤ N) (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F} (hm : ∀ v, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    (mass (formF Q₀) (stdLat F N))⁻¹ * repMass (formF Q₀) (stdLat F N) (algebraMap (𝓞 F) F m) =
      siegelProduct Q₀ m := by
  have hS := (siegelFormulaAt_all_ranks hd hT hloc hN Q₀ hpd hm).repMass_eq
  have hpos := mass_pos hpd (stdLat F N) (HilbertModular.isIntegral_stdLat Q₀)
  rw [show repMass (formF Q₀) (stdLat F N) (algebraMap (𝓞 F) F m) = _ from hS, ← mul_assoc,
    inv_mul_cancel₀ hpos.ne', one_mul]

/-- **Consistency with the Hilbert modular form argument: odd rank in the form** (`HilbertModular.siegelFormula_nf_repMass` is the even-rank statement): for odd
$N = n + 1 \ge 5$, under the two named inputs,
$\mathrm{repMass}(\mathcal O_F^N, m) = \mathrm{Mass}(\mathcal O_F^N)\cdot|d_F|^{-(N-1)/2}\,\mathtt{aENF}(Q_0, m)$, with the same Eisenstein-type local
product `Siegel.aENF` (Hanke's (5.3) over $F$) and the same discriminant factor (the erratum) as there — so in every rank $N \ge 4$
the genus average is $|d_F|^{-(N-1)/2}\,\mathtt{aENF}$, by Hilbert modular forms of weight $N/2$ for even $N$ and by $\tau = 2$ for odd $N$. -/
@[kb "siegel1935" "Hauptsatz over F in the aENF form, odd rank ≥ 5 [unverified]"]
theorem siegelFormula_odd_aENF (hd : 2 ≤ Fintype.card (InfinitePlace F)) (hT : TernaryTamagawaTwo F)
    (hloc : OddRankOrbitalLocalIdentities F) {n : ℕ} (hn : 4 ≤ n) (he : Even n) (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F} (hm : ∀ v, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMass (formF Q₀) (stdLat F (n + 1)) (algebraMap (𝓞 F) F m) =
      mass (formF Q₀) (stdLat F (n + 1)) * ((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (n + 1 - 1) * Siegel.aENF Q₀ m) := by
  rw [← HilbertModular.siegelProduct_eq_discr_mul_aENF (HilbertModular.isTotPosGram_Q₀ hpd) (by omega) hm]
  exact (siegelFormulaAt_odd hd hT hloc hn he Q₀ hpd hm).repMass_eq

end Induction

/-! ### Consistency with the even-rank statement, and $F = \mathbb Q$ -/

section Consistency

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [IsPrincipalIdealRing (𝓞 F)]

/-- **Siegel's formula in every rank $N \ge 5$ without $[F:\mathbb Q] \ge 2$** (so for $F = \mathbb Q$ too, see `siegelFormulaAt_rat`), given
$\tau(SO_4) = 2$ (`QuaternaryTamagawaTwo F`) and the odd-rank local identities. Even $N \ge 6$: Hilbert modular forms (unconditional); odd $N$:
`siegelFormulaAt_of_local` with `tamagawaNumberTwo_of_four`. -/
@[kb "siegel1935" "Hauptsatz (numbers), every rank ≥ 5, any totally real F with h_F = 1 [unverified]"]
theorem siegelFormulaAt_of_four (h4 : QuaternaryTamagawaTwo F) (hloc : OddRankOrbitalLocalIdentities F) {N : ℕ}
    (hN : 5 ≤ N) (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v, 0 < realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt Q₀ m := by
  rcases Nat.even_or_odd N with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact HilbertModular.siegelFormulaAt_of_pid hpd (k := k) (by omega) (by omega) hm
  · subst hk
    exact siegelFormulaAt_of_local Q₀ hpd (by omega) (hloc.odd (2 * k) (by omega) (even_two_mul k) Q₀ hpd)
      (tamagawaNumberTwo_of_four h4 hloc (by omega) Q₀ hpd)
      (fun Q' hQ' => tamagawaNumberTwo_of_four h4 hloc (by omega) Q' hQ') hm

/-- **Consistency of the two routes in even rank** (the Siegel formula vs Weil's local identities): for $Q_0$ totally positive definite in
even rank $N = n + 1 \ge 6$ (or $N = 4$ with $[F:\mathbb Q] \ge 2$), a totally positive $m$ with $S(L, m) \ne 0$ and an adapted frame
$Q_0\circ g = \langle m\rangle\perp Q_0'$ with the local orbital identity at every prime, Hilbert modular forms (`siegelFormulaAt_of_pid`) and
the per-number identity of Weil's route (`two_mul_tamagawaK_mul_repMass_frame`) together give $\tau(SO(Q_0)) = \tau(SO(Q_0'))$ — with **no**
$\tau = 2$ input. So where both apply they agree: the genus average forces exactly the equality of Tamagawa numbers that Weil's
induction step propagates. -/
@[kb "weil1982" "§4.5, p. 100 (τ(G) = τ(G') ⟺ Siegel's theorem), even rank"]
theorem tauSO_eq_tauSO_frame_of_even {n : ℕ} (hn : 3 ≤ n) (heven : Even (n + 1))
    (hd : n + 1 = 4 → 2 ≤ Fintype.card (InfinitePlace F)) (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F} (hm : ∀ v, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (hS : siegelProduct Q₀ m ≠ 0) (fr : AdaptedFrame (formF Q₀) (algebraMap (𝓞 F) F m))
    (hgli : ∀ v, OrbitalLocalIdentityAt v Q₀ fr) : tauSO Q₀ = tauSO fr.Q' := by
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  have hC : SiegelFormulaAt Q₀ m := by
    obtain ⟨k, hk⟩ := heven
    by_cases h4 : n + 1 = 4
    · exact HilbertModular.siegelFormulaAt_of_pid_four hpd h4 (hd h4) hm
    · exact HilbertModular.siegelFormulaAt_of_pid hpd (k := k) (by omega) (by omega) hm
  have key := two_mul_tamagawaK_mul_repMass_frame Q₀ hpd hn hm fr hgli
  have hrep := hC.repMass_eq
  have htau : tauSO Q₀ = tamagawaK Q₀ * (2 * mass (formF Q₀) (stdLat F (n + 1))) := by
    rw [tauSO, mass_SO_eq_two_mul_mass Q₀ hQ₀ (by omega) hpd (HilbertModular.isIntegral_stdLat Q₀)]
  have h2 : tauSO Q₀ * siegelProduct Q₀ m = tauSO fr.Q' * siegelProduct Q₀ m := by
    rw [← key, htau]
    rw [show repMass (formF Q₀) (stdLat F (n + 1)) (algebraMap (𝓞 F) F m) = _ from hrep]
    ring
  exact mul_right_cancel₀ hS h2

end Consistency

/-- $\mathcal O_{\mathbb Q}$ is a PID ($\mathcal O_{\mathbb Q} \cong \mathbb Z$, Mathlib's `Rat.ringOfIntegersEquiv`). -/
instance isPrincipalIdealRing_ringOfIntegers_rat : IsPrincipalIdealRing (𝓞 ℚ) :=
  IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom Rat.ringOfIntegersEquiv.symm.surjective

/-- **Over $\mathbb Q$** ($F = \mathbb Q$ is not covered by `siegelFormulaAt_all_ranks`, whose rank-4 base needs $[F:\mathbb Q] \ge 2$): Siegel's
formula for numbers in every rank $N \ge 5$ for totally positive definite forms over $\mathcal O_{\mathbb Q}$, given $\tau(SO_4) = 2$ over $\mathbb Q$
(`QuaternaryTamagawaTwo ℚ`, which follows from `TernaryTamagawaTwo ℚ` by `RatBridge.quaternaryTamagawaTwo_rat`; all ranks $N \ge 4$ over $\mathbb Q$:
`RatBridge.siegelFormulaAt_rat_all_ranks`) and the odd-rank
local identities. Even $N \ge 6$ is unconditional (Hilbert modular forms over $\mathbb Q$). -/
@[kb "siegel1935" "Hauptsatz (numbers) over ℚ, every rank ≥ 5 [unverified]"]
theorem siegelFormulaAt_rat (h4 : QuaternaryTamagawaTwo ℚ) (hloc : OddRankOrbitalLocalIdentities ℚ) {N : ℕ}
    (hN : 5 ≤ N) (Q₀ : QuadForm (𝓞 ℚ) N) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 ℚ}
    (hm : ∀ v, 0 < realEmb ℚ v (algebraMap (𝓞 ℚ) ℚ m)) : SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_of_four h4 hloc hN Q₀ hpd hm

end QuadFormsKB.Tamagawa
