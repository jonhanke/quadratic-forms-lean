/-
# Siegel's formula over every totally real field in the language of forms

**Layer:** $F$ a totally real number field, **any class number**; $Q$ a totally positive definite form over $\mathcal O_F$; $m \in \mathcal O_F$
totally positive. The KB's Siegel formulas over $F$ are stated for the lattice classes in the genus of $\mathcal O_F^N$ in $(F^N, Q)$.
By `FormClassNF.bijOn_formClass` (every lattice in that genus is free, `genusFree_formF`; Hasse–Minkowski over $F$ for the converse)
these are the classical sums over $\mathrm{GL}_N(\mathcal O_F)$-classes $[Q']$ of totally positive definite forms over $\mathcal O_F$ in the
genus of $Q$ (`formGenusClasses`), with weights $1/|\mathrm{Aut}_{\mathrm{GL}_N(\mathcal O_F)}(Q')|$ (improper automorphisms included) and
$r_{Q'}(m) = \#\{x \in \mathcal O_F^N : Q'(x) = m\}$:

* `siegelFormula_binary_totallyReal_forms` ($N = 2$, unconditional, every term unfolded as in `siegelFormula_binary_totallyReal`):
  $$\sum_{[Q']}\frac{r_{Q'}(m)}{|\mathrm{Aut}(Q')|} = \frac12\Bigl(\sum_{[Q']}\frac1{|\mathrm{Aut}(Q')|}\Bigr)|d_F|^{-1/2}\prod_\sigma\beta_\sigma(m)\cdot
    L_F(1,\chi_Q)^{-1}\prod_\mathfrak p\frac{\beta_\mathfrak p(Q,m)}{1-\chi_Q(\mathfrak p)N\mathfrak p^{-1}};$$
* `siegelFormulaAt3_totallyReal_forms` ($N = 3$, unconditional; regularized product `siegelProduct3`);
* `siegelFormulaAt_totallyReal_forms` ($N \ge 4$, unconditional; `siegelProduct`).

Sources: Siegel, Ann. Math. 36 (1935), 38 (1937) [unverified locators]; Steinitz 1911; O'Meara 1963, 81:5, p. 212, §82, pp. 220–238.
-/
import QuadFormsKB.Tamagawa.FormClassNF
import QuadFormsKB.Tamagawa.SiegelBinaryTotallyReal
import QuadFormsKB.Tamagawa.BinaryTauNF
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSiegelTotallyReal

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.FormClassNF

open QuadFormsKB.Lattices QuadFormsKB.HilbertModular NFEuler RegProd LocalDensity

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-- **Siegel's theorem for binary forms over a totally real number field, forms language** (unconditional). For $F$ totally real (any
class number), $Q$ a totally positive definite binary form over $\mathcal O_F$ (any discriminant, primitive or not) and $m \gg 0$:
$$\sum_{[Q']}\frac{r_{Q'}(m)}{|\mathrm{Aut}(Q')|}
 = \frac12\Bigl(\sum_{[Q']}\frac1{|\mathrm{Aut}(Q')|}\Bigr)\,|d_F|^{-1/2}
 \prod_{\sigma}\beta_\sigma(m)\cdot L_F(1,\chi_Q)^{-1}\prod_{\mathfrak p}\frac{\beta_\mathfrak p(Q,m)}{1-\chi_Q(\mathfrak p)N\mathfrak p^{-1}},$$
$[Q']$ over the $\mathrm{GL}_2(\mathcal O_F)$-classes of totally positive definite binary forms over $\mathcal O_F$ in the genus of $Q$
(`formGenusClasses`), $\mathrm{Aut}(Q') \subseteq \mathrm{GL}_2(\mathcal O_F)$ (`FormClass.autCard`), $r_{Q'}(m)$ = `FormClass.repNum`; the right
side as in `siegelFormula_binary_totallyReal`. From that theorem by `formMass_eq`, `formRepMass_eq` (every lattice in the genus of
$\mathcal O_F^2$ is free, `genusFree_formF`). -/
@[kb "siegel1935" "Hauptsatz, n = 2 (ε = 1/2), over a totally real field, classes of forms [unverified]"]
theorem siegelFormula_binary_totallyReal_forms (Q : QuadForm (𝓞 F) 2) (hpd : IsTotallyPosDef (formF Q)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    ∑ᶠ c ∈ formGenusClasses Q, (FormClass.repNum c m : ℝ) / FormClass.autCard c =
      (1 / 2 : ℝ) * (∑ᶠ c ∈ formGenusClasses Q, ((FormClass.autCard c : ℝ))⁻¹) *
        (|(discr F : ℝ)| ^ (-(1 / 2 : ℝ)) *
          (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 2 ‖σ (algebraMap (𝓞 F) F m)‖ (detGram Q σ)) *
          ((LOne fun v => chiP v Q)⁻¹ *
            ∏' v, NF.localDensity v Q m / (1 - chiP v Q / (normP v : ℝ)))) := by
  have h := siegelFormula_binary_totallyReal Q hpd hm
  change formRepMass Q m = (1 / 2 : ℝ) * formMass Q * _
  rw [formRepMass_eq hpd, formMass_eq hpd]
  exact h

/-- **Rank-3 Siegel over every totally real field, forms language** (unconditional): for $Q_0$ totally positive definite ternary over
$\mathcal O_F$ and $m \gg 0$, $\sum_{[Q']}r_{Q'}(m)/|\mathrm{Aut}(Q')| = \bigl(\sum_{[Q']}1/|\mathrm{Aut}(Q')|\bigr)\cdot S_3(Q_0, m)$ over the
$\mathrm{GL}_3(\mathcal O_F)$-classes in the genus of $Q_0$ (`siegelFormulaAt3_nf_uncond` with `formMass_eq`, `formRepMass_eq`). -/
@[kb "siegel1935" "Hauptsatz, n = 3, over a totally real field, classes of forms [unverified]"]
theorem siegelFormulaAt3_totallyReal_forms (Q₀ : QuadForm (𝓞 F) 3) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    ∑ᶠ c ∈ formGenusClasses Q₀, (FormClass.repNum c m : ℝ) / FormClass.autCard c =
      (∑ᶠ c ∈ formGenusClasses Q₀, ((FormClass.autCard c : ℝ))⁻¹) * siegelProduct3 Q₀ m := by
  have h := (siegelFormulaAt3_nf_uncond Q₀ hpd hm).repMass_eq
  change formRepMass Q₀ m = formMass Q₀ * _
  rw [formRepMass_eq hpd, formMass_eq hpd]
  exact h

/-- **Siegel's formula in every rank $N \ge 4$ over every totally real field, forms language** (unconditional): for $Q_0$ totally positive
definite over $\mathcal O_F$ in $N \ge 4$ variables and $m \gg 0$,
$\sum_{[Q']}r_{Q'}(m)/|\mathrm{Aut}(Q')| = \bigl(\sum_{[Q']}1/|\mathrm{Aut}(Q')|\bigr)\cdot S(Q_0, m)$ over the $\mathrm{GL}_N(\mathcal O_F)$-classes in
the genus of $Q_0$, $S$ = `siegelProduct` (`Measure.Weil.siegelFormulaAt_totallyReal` with `formMass_eq`, `formRepMass_eq`). -/
@[kb "siegel1935" "Hauptsatz, over a totally real field, classes of forms [unverified]"]
theorem siegelFormulaAt_totallyReal_forms {N : ℕ} (hN : 4 ≤ N) (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    ∑ᶠ c ∈ formGenusClasses Q₀, (FormClass.repNum c m : ℝ) / FormClass.autCard c =
      (∑ᶠ c ∈ formGenusClasses Q₀, ((FormClass.autCard c : ℝ))⁻¹) * siegelProduct Q₀ m := by
  have h := (Measure.Weil.siegelFormulaAt_totallyReal hN Q₀ hpd hm).repMass_eq
  change formRepMass Q₀ m = formMass Q₀ * _
  rw [formRepMass_eq hpd, formMass_eq hpd]
  exact h

end QuadFormsKB.Tamagawa.FormClassNF
