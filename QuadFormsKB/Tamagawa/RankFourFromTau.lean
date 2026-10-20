import QuadFormsKB.Tamagawa.TauFour
import QuadFormsKB.Tamagawa.TernaryTamagawaNF

/-!
# Rank-4 Siegel for the number $m_0$ from $\tau(SO_3) = \tau(SO_4) = 2$

**Layer:** a totally real number field $F$, **any class number**; `tauSO`, `SiegelFormulaAt`.

The step (`tamagawaNumberTwo_four_of_three_of_siegel`, `tamagawaNumberTwo_three_of_four_of_siegel`) uses three facts
about the split lattice $L = \mathcal O_Fe_0\perp L'$, $Q(e_0) = m_0$:
$\mathrm{repMass}(L, m_0) = \mathrm{Mass}(L')\,W$ (the reduction), $W\mu(K_{SO}(L)) = \mu(K_{SO}(L'))\,S(L, m_0)$ (the local orbital
identity, proved at every prime, and the archimedean identity) and Siegel's formula $\mathrm{repMass}(L, m_0) = \mathrm{Mass}(L)S(L, m_0)$.
Any two of "Siegel", "$\tau(L') = 2$", "$\tau(L) = 2$" give the third. This file adds the third direction:

* **`siegelFormulaAt_of_three_of_four`**: $\tau(SO(Q_0')) = 2$ and $\tau(SO(\langle m_0\rangle\perp Q_0')) = 2$ imply Siegel's formula for
  the number $m_0$ and the lattice $\mathcal O_F\perp\mathcal O_F^3$ (no PID, no degree hypothesis);
* **`rankFourUnitSiegel_of_quaternary`**: `QuaternaryTamagawaTwo F → RankFourUnitSiegel F` for every totally real $F$ (the ternary input
  is a theorem, `ternaryTamagawaTwo_nf`), and **`rankFourUnitSiegel_iff_quaternary`**: the two named inputs are **equivalent**;
* consumers: `tamagawaNumberTwo_all_ranks_of_quaternary_nf`, `massFormula_all_ranks_of_quaternary_nf`,
  `siegelFormulaAt_all_ranks_of_quaternary_nf`, `siegelFormulaAt_four_of_quaternary_nf` (rank-4 Siegel for every $m_0\gg0$).

This is the route to `RankFourUnitSiegel F` via $m = 4$ and $\tau(SO_4) = 2$: the remaining content is
$\tau(SO_4) = 2$ for definite quaternary forms, i.e. Weil's adelic theorem for $m = 4$ (`Measure/Weil/GnatTamagawa*.lean`).

Sources: Weil 1982, §3.7, Thm 3.7.1, p. 65 ($m = 3, 4$) and §4.5, p. 100 (Siegel's theorem as a consequence of $\tau = 2$);
Siegel 1935, Hauptsatz [unverified page].
-/

open NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open Lattices QuadForm HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-- **Siegel's formula for the number $m_0$ in rank $4$ from $\tau(SO_3) = 2$ and $\tau(SO_4) = 2$** (the third direction of the step; no PID, no degree hypothesis): for $m_0\gg0$ and $Q_0'$ ternary with $\langle m_0\rangle\perp Q_0'$ totally positive definite and
$\mathcal O_F^4$ integral,
$\tau(SO(Q_0')) = 2\ \wedge\ \tau(SO(\langle m_0\rangle\perp Q_0')) = 2\ \Longrightarrow\ \mathrm{repMass}(L, m_0) = \mathrm{Mass}(L)\,S(L, m_0)$.

*Proof.* $\mathrm{repMass}(L, m_0) = \mathrm{Mass}(L')W$ (`repMass_eq_mass_mul`), $W\mu(L) = \mu(L')S$ (local orbital identity at every
prime, `localOrbitalIdentityAt_local`, and `archProd_splitForm`), $\mathrm{Mass}(L) = \mu(L)^{-1}$ and $\mathrm{Mass}(L') = \mu(L')^{-1}$
(`massFormula` from the two $\tau$'s). -/
@[kb "weil1982" "§4.5, p. 100 (Siegel from τ = 2), rank 4; Thm 3.7.1, p. 65; any class number"]
theorem siegelFormulaAt_of_three_of_four {m₀ : 𝓞 F}
    (hm : ∀ v, 0 < HilbertModular.realEmb F v (algebraMap (𝓞 F) F m₀)) (Q₀' : QuadForm (𝓞 F) 3)
    (hpd : IsTotallyPosDef ((splitForm m₀ Q₀').map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral ((splitForm m₀ Q₀').map (algebraMap (𝓞 F) F)) (stdLat F 4).1)
    (hτ3 : TamagawaNumberTwo Q₀') (hτ4 : TamagawaNumberTwo (splitForm m₀ Q₀')) :
    SiegelFormulaAt (splitForm m₀ Q₀') m₀ := by
  have hm0 : m₀ ≠ 0 := by
    rintro rfl
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    simpa using hm v
  have hQ4 : (splitForm m₀ Q₀').Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  have hQ' : Q₀'.Nondegenerate := nondegenerate_of_posDef_split m₀ Q₀' hpd
  have hloc : LocalOrbitalIdentity Q₀' m₀ :=
    localOrbitalIdentity_of_local' m₀ hm0 Q₀' hpd hLi
      (fun v _ => localOrbitalIdentityAt_local v m₀ hm0 Q₀' hQ')
      (multipliable_siegelDensity (by norm_num) (by norm_num) _ hQ4)
      (multipliable_siegelDensity (by norm_num) (by norm_num) _ hQ')
      (tprod_siegelDensity_three_ne_zero Q₀' hQ')
  have hMF : MassFormulaHolds (splitForm m₀ Q₀') := massFormula _ hQ4 (by norm_num) hpd hLi hτ4
  unfold MassFormulaHolds at hMF
  set QF' := Q₀'.map (algebraMap (𝓞 F) F)
  set mF := algebraMap (𝓞 F) F m₀
  have hsplit := map_splitForm_alg m₀ Q₀'
  have hpd₀ := hpd
  have hLi₀ := hLi
  rw [hsplit] at hpd₀ hLi₀ hMF
  have hmF : mF ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hm0
  have hpd' := isTotallyPosDef_of_splitForm hpd₀
  have hLi' := isIntegral_of_splitForm hLi₀
  have hMF3 : MassFormulaHolds Q₀' := massFormula Q₀' hQ' (by norm_num) hpd' hLi' hτ3
  unfold MassFormulaHolds at hMF3
  have hR := repMass_eq_mass_mul mF QF' (stdLat F (3 + 1)) hpd₀ hLi₀ hmF hpd' hLi'
  have hloc' := hloc.typeSum_eq
  set W := ∑ᶠ t : MulAction.orbitRel.Quotient (OAf QF') (CompSet mF QF' (stdLat F (3 + 1))),
    typeWeight mF QF' (stdLat F (3 + 1)) t
  set A := ∏' v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
    LocalDensity.NF.siegelDensity v (splitForm m₀ Q₀') (splitForm m₀ Q₀')
  set A' := ∏' v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), LocalDensity.NF.siegelDensity v Q₀' Q₀'
  set B := ∏' v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), LocalDensity.NF.localDensity v (splitForm m₀ Q₀') m₀
  set Pr := ∏ σ : F →ₐ[ℚ] ℂ, archVolSO (3 + 1) (detGram (splitForm m₀ Q₀') σ)
  set Pr' := ∏ σ : F →ₐ[ℚ] ℂ, archVolSO 3 (detGram Q₀' σ)
  set ρ := ∏ σ : F →ₐ[ℚ] ℂ, archRepDensity (3 + 1) ‖σ mF‖ (detGram (splitForm m₀ Q₀') σ)
  set Nm := normTwoM m₀
  set δ := |(discr F : ℝ)|
  have hδ : 0 < δ := abs_pos.mpr (by exact_mod_cast discr_ne_zero F)
  have harch : Pr * Nm ^ 3 = Pr' * ρ := archProd_splitForm m₀ hm0 Q₀' hQ'
  have hT : tamagawaK (splitForm m₀ Q₀') = δ ^ (-(((3 + 1 : ℕ) : ℝ) * ((3 + 1 : ℕ) - 1) / 4)) * Pr * A := rfl
  have hT' : tamagawaK Q₀' = δ ^ (-((3 : ℝ) * (3 - 1) / 4)) * Pr' * A' := rfl
  have hSP : siegelProduct (splitForm m₀ Q₀') m₀ = δ ^ (-(((3 + 1 : ℕ) : ℝ) - 1) / 2) * ρ * B := rfl
  have hδe : δ ^ (-(((3 + 1 : ℕ) : ℝ) * ((3 + 1 : ℕ) - 1) / 4)) =
      δ ^ (-((3 : ℝ) * (3 - 1) / 4)) * δ ^ (-(((3 + 1 : ℕ) : ℝ) - 1) / 2) := by
    rw [← Real.rpow_add hδ]; push_cast; ring_nf
  have hmassL := mass_pos hpd₀ (stdLat F (3 + 1)) hLi₀
  have hmassL' := mass_pos hpd' (stdLat F 3) hLi'
  have hTpos : 0 < tamagawaK (splitForm m₀ Q₀') := by rw [hMF] at hmassL; exact inv_pos.mp hmassL
  have hT'pos : 0 < tamagawaK Q₀' := by rw [hMF3] at hmassL'; exact inv_pos.mp hmassL'
  set D' := δ ^ (-((3 : ℝ) * (3 - 1) / 4))
  set Ds := δ ^ (-(((3 + 1 : ℕ) : ℝ) - 1) / 2)
  have key : W * tamagawaK (splitForm m₀ Q₀') = tamagawaK Q₀' * siegelProduct (splitForm m₀ Q₀') m₀ := by
    rw [hT, hδe, hT', hSP]
    linear_combination (D' * Ds * Pr) * hloc' + (D' * Ds * A' * B) * harch
  refine ⟨?_⟩
  rw [hsplit, hR, hMF, hMF3]
  have hT0 := hTpos.ne'
  have hT'0 := hT'pos.ne'
  field_simp
  linear_combination key

/-- **`RankFourUnitSiegel F` from `QuaternaryTamagawaTwo F`** (every totally real field, any class number): the ternary input is a
theorem (`ternaryTamagawaTwo_nf`), so $\tau(SO_4) = 2$ alone gives rank-4 Siegel for the number $1$. -/
@[kb "weil1982" "§4.5, p. 100 (Siegel from τ = 2), rank 4, m = 1; any class number"]
theorem rankFourUnitSiegel_of_quaternary (h4 : QuaternaryTamagawaTwo F) : RankFourUnitSiegel F :=
  ⟨fun Q₃ hpd => by
    have hpd₀ := hpd
    rw [formF, map_splitForm_alg] at hpd₀
    have hpd' := isTotallyPosDef_of_splitForm hpd₀
    exact siegelFormulaAt_of_three_of_four realEmb_one_pos Q₃ hpd (LatChange.isIntegral_std _)
      (tamagawaNumberTwo_ternary_nf Q₃ hpd') (h4.tau_eq_two _ hpd)⟩

/-- **The two rank-4 inputs are equivalent over every totally real field** (any class number):
`RankFourUnitSiegel F ↔ QuaternaryTamagawaTwo F` (both directions use the proved ternary case `ternaryTamagawaTwo_nf`). -/
@[kb "weil1982" "Thm 3.7.1 (m = 4), p. 65 ⟺ rank-4 Siegel for m = 1; any class number"]
theorem rankFourUnitSiegel_iff_quaternary : RankFourUnitSiegel F ↔ QuaternaryTamagawaTwo F :=
  ⟨quaternaryTamagawaTwo_nf, rankFourUnitSiegel_of_quaternary⟩

/-- **Rank-4 Siegel for every totally positive number $m_0$** and every split lattice $\mathcal O_F\perp\mathcal O_F^3$, given
`QuaternaryTamagawaTwo F` (any class number). -/
@[kb "weil1982" "§4.5, p. 100 (Siegel from τ = 2), rank 4; any class number, given τ(SO_4) = 2"]
theorem siegelFormulaAt_four_of_quaternary_nf (h4 : QuaternaryTamagawaTwo F) {m₀ : 𝓞 F}
    (hm : ∀ v, 0 < HilbertModular.realEmb F v (algebraMap (𝓞 F) F m₀)) (Q₀' : QuadForm (𝓞 F) 3)
    (hpd : IsTotallyPosDef ((splitForm m₀ Q₀').map (algebraMap (𝓞 F) F))) :
    SiegelFormulaAt (splitForm m₀ Q₀') m₀ := by
  have hpd₀ := hpd
  rw [map_splitForm_alg] at hpd₀
  have hpd' := isTotallyPosDef_of_splitForm hpd₀
  exact siegelFormulaAt_of_three_of_four hm Q₀' hpd (LatChange.isIntegral_std _)
    (tamagawaNumberTwo_ternary_nf Q₀' hpd') (h4.tau_eq_two _ hpd)

/-- **$\tau = 2$ in every rank $N\ge4$ over every totally real field**, given `QuaternaryTamagawaTwo F`. -/
@[kb "weil1982" "Thm 3.7.1, Thm 4.5.1, p. 109; any class number, given τ(SO_4) = 2"]
theorem tamagawaNumberTwo_all_ranks_of_quaternary_nf (h4 : QuaternaryTamagawaTwo F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ :=
  tamagawaNumberTwo_all_ranks_nf (rankFourUnitSiegel_of_quaternary h4) hN Q₀ hpd

/-- **The mass formula in every rank $N\ge4$ over every totally real field**, given `QuaternaryTamagawaTwo F`. -/
@[kb "weil1982" "Thm 4.5.1, p. 109; mass formula; any class number, given τ(SO_4) = 2"]
theorem massFormula_all_ranks_of_quaternary_nf (h4 : QuaternaryTamagawaTwo F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) : MassFormulaHolds Q₀ :=
  massFormula_all_ranks_nf (rankFourUnitSiegel_of_quaternary h4) hN Q₀ hpd

/-- **Siegel's formula for numbers in every rank $N\ge5$ over every totally real field**, given `QuaternaryTamagawaTwo F`. -/
@[kb "weil1982" "§4.5, p. 100; Thm 4.5.1, p. 109; any class number, given τ(SO_4) = 2"]
theorem siegelFormulaAt_all_ranks_of_quaternary_nf (h4 : QuaternaryTamagawaTwo F) {n : ℕ} (hn : 4 ≤ n)
    (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v, 0 < realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_all_ranks_nf (rankFourUnitSiegel_of_quaternary h4) hn Q₀ hpd hm

end QuadFormsKB.Tamagawa
