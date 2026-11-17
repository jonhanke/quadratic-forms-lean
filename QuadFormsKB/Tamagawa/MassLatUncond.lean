import QuadFormsKB.Tamagawa.InputsFollowup

/-!
# The mass formula for every lattice over every totally real field, unconditional

**Setting.** $F$ a totally real number field of **any class number**, $Q_0$ a totally positive definite quadratic form over
$\mathcal O_F$ in $n \ge 3$ variables, $V = (F^n, Q_0)$, $L$ any lattice on $V$ integral for $Q_0$ (**any Steinitz class**: $L$ need not
be free, e.g. $L = \mathfrak a e_0 \oplus \mathcal O_F e_1 \oplus \dots$ with $\mathfrak a$ non-principal).

**Main results.**
* `massFormula_lat_totallyReal`: $\mathrm{Mass}(L) = \sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}|O(M)|^{-1} = \mu_{\mathrm{Tam}}(K_{SO}(L))^{-1}$
  (`LatChange.tamagawaKLat`).
* `massFormula_lat_local_totallyReal`: the same with $\mu_{\mathrm{Tam}}(K_{SO}(L))$ written as the product of local factors
  of $L$ ($|d_F|^{-n(n-1)/4}\prod_\sigma\mathrm{vol}(SO(V_\sigma))\prod_\mathfrak p\tfrac12\beta_\mathfrak p(Q_0\circ P_\mathfrak p)\|\det P_\mathfrak p\|^{n+1}$).

Both are `LatChange.massFormula_lat_nf` / `massFormula_lat_local_nf` with their hypothesis $\tau(SO(Q_0)) = 2$ discharged by
`tamagawaNumberTwo_totallyReal` (every rank $n \ge 3$, every totally real field). The other wrappers of this kind (`massFormula_all_ranks_nf`,
`siegelFormulaAt_all_ranks_nf`, `massFormula_lat_all_ranks_nf` without `RankFourUnitSiegel`) are already
`Measure.Weil.massFormula_all_ranks_totallyReal`, `Measure.Weil.siegelFormulaAt_totallyReal` and the first theorem below.

Sources: Kitaoka, *Arithmetic of quadratic forms* (1993), Thm 6.8.1 [unverified]; Weil, *Adeles and algebraic groups* (1982),
Thm 4.5.1 [unverified page].
-/

open Matrix

noncomputable section

namespace QuadFormsKB.Tamagawa.LatChange

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.LocalDensity QuadFormsKB.QuadForm
open QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-- **The mass formula for the genus of every lattice, every totally real field, unconditional**: for $Q_0$ totally positive
definite over $\mathcal O_F$ in $n \ge 3$ variables and every lattice $L$ on $(F^n, Q_0)$ integral for $Q_0$ (any Steinitz class),
$$\mathrm{Mass}(L) = \sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac1{|O(M)|} = \mu_{\mathrm{Tam}}(K_{SO}(L))^{-1}.$$ -/
@[kb "kitaoka1993" "Thm 6.8.1 (mass formula), arbitrary lattice, every totally real F, n ≥ 3, unconditional [unverified]"]
theorem massFormula_lat_totallyReal (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hpd : IsTotallyPosDef (formF Q₀))
    (L : Lat F n) (hLi : IsIntegral (formF Q₀) L.1) :
    mass (formF Q₀) L = (tamagawaKLat Q₀ L)⁻¹ :=
  massFormula_lat_nf Q₀ (nondegenerate_of_map hpd.nondegenerate) (by omega) hpd
    (tamagawaNumberTwo_totallyReal hn Q₀ hpd) L hLi

/-- **Local form: the mass of every lattice from its local data**, every totally real field, $n \ge 3$, unconditional: for
$L \subseteq F^n$ integral with local bases $L_\mathfrak p = P_\mathfrak p\,\mathfrak o_\mathfrak p^n$,
$$\mathrm{Mass}(L) = |d_F|^{n(n-1)/4}\Big(\prod_\sigma\mathrm{vol}(SO(V_\sigma))\Big)^{-1}\Big(\prod_\mathfrak p\tfrac12\beta_\mathfrak p(Q_0\circ P_\mathfrak p)
  \|\det P_\mathfrak p\|^{n+1}\Big)^{-1}.$$ -/
@[kb "kitaoka1993" "Thm 6.8.1 (mass formula), arbitrary lattice, local factors, every totally real F, n ≥ 3, unconditional [unverified]"]
theorem massFormula_lat_local_totallyReal (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hpd : IsTotallyPosDef (formF Q₀))
    (L : Lat F n) (hLi : IsIntegral (formF Q₀) L.1)
    (P : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F))
    (hP : ∀ v, (P v).det ≠ 0) (hL : ∀ v, loc v L.1 = locAct v (glOf v (P v) (hP v)) (std v)) :
    mass (formF Q₀) L = ((|(discr F : ℝ)|) ^ (-((n : ℝ) * (n - 1) / 4)) *
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram Q₀ σ)) * ∏' v, latLocalFactor v Q₀ (P v))⁻¹ :=
  massFormula_lat_local_nf (by omega) (by omega) Q₀ (nondegenerate_of_map hpd.nondegenerate) hpd
    (tamagawaNumberTwo_totallyReal hn Q₀ hpd) L hLi P hP hL

end QuadFormsKB.Tamagawa.LatChange

end
