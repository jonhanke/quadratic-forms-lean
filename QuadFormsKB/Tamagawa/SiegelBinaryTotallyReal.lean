import QuadFormsKB.Tamagawa.SiegelBinaryNF

/-!
# Siegel's theorem for binary forms over a totally real number field, fully unfolded

**Layer:** $F$ a totally real number field (any degree, any class number $h_F$); $Q$ a totally positive definite **binary**
quadratic form over $\mathcal O_F$ (any discriminant, primitive or not); $L = \mathcal O_F^2$; $m \in \mathcal O_F$ totally positive.

This file is packaging of `siegelFormulaAt2_nf`: the same theorem with every term written out with its
named definition, so that the statement can be read without unfolding `SiegelFormulaAt2`, `repMass`, `mass`,
`siegelProduct2Reg`, `siegelProductWith` or `regProd`.

**Statement** (`siegelFormula_binary_totallyReal`):
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(\mathcal O_F^2)}\frac{r_M(m)}{|O(M)|}
 = \frac12\Bigl(\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(\mathcal O_F^2)}\frac1{|O(M)|}\Bigr)\,|d_F|^{-1/2}
 \prod_{\sigma:F\to\mathbb C}\beta_\sigma(m)\cdot L_F(1,\chi_Q)^{-1}\prod_{\mathfrak p}\frac{\beta_\mathfrak p(Q,m)}{1-\chi_Q(\mathfrak p)N\mathfrak p^{-1}}.$$

**Conventions (read before using the statement).**
* *The genus.* `genusClasses (formF Q) (stdLat F 2)` is the set of $O(V)(F)$-isometry classes of **all** $\mathcal O_F$-lattices
  $M \subseteq F^2$ in the genus of $L = \mathcal O_F^2$ for the quadratic space $(F^2, Q)$: lattices locally isometric to $L$ at
  every finite prime. **Every lattice in this genus is free**, $M = \gamma\mathcal O_F^2$, for every class number
  (`HilbertModular.genusFree_formF`: the Steinitz class is a genus invariant, since $M_\mathfrak p = \sigma_\mathfrak pL_\mathfrak p$ with
  $\det\sigma_\mathfrak p = \pm1$), so the sum is the classical sum over $\mathrm{GL}_2(\mathcal O_F)$-classes of binary forms over
  $\mathcal O_F$ in the genus of $Q$: `FormClassNF.siegelFormula_binary_totallyReal_forms` (over $F = \mathbb Q$ also
  `RatBridge.mass_rat`, `RatBridge.repMass_rat`). Lattices of nontrivial Steinitz class ($\cong \mathcal O_F \oplus \mathfrak a$,
  $[\mathfrak a] \ne 1$) form *other* genera, not covered here. (An earlier version of this docstring said
  the genus contains non-free lattices when $h_F > 1$; that was wrong.)
* *Classes and weights.* Classes are isometry classes (the analogue of $\mathrm{GL}_2$-equivalence, not $\mathrm{SL}_2$);
  $O(M)$ (`LatClass.autCard`) is the full isometry group of $M$, improper automorphisms included; $r_M(m)$
  (`LatClass.repCount`) $= \#\{v \in M : Q(v) = m\}$.
* *Local factors.* $\beta_\mathfrak p(Q,m)$ = `NF.localDensity v Q m`, the library's local density of $Q\otimes\mathcal O_\mathfrak p$ at $m$
  (counting measure normalization $\lim_k N\mathfrak p^{-k}\#\{x \bmod \mathfrak p^k : Q(x) \equiv m\}$), at **every** prime,
  dyadic and ramified included, not evaluated in closed form. $\beta_\sigma(m)$ = `archRepDensity 2 |σ m| (detGram Q σ)`
  $= \pi\,\det(\sigma(H_Q)/2)^{-1/2}$ (`archRepDensity_two`), $\sigma$ ranging over the $[F:\mathbb Q]$ (real) embeddings.
  $\chi_Q$ = `chiP · Q`, the quadratic character of $F(\sqrt{-\det(H_Q/2)})/F$ at the primes $\mathfrak p \nmid 2\det H_Q$ ($0$ at the
  others; changing it at finitely many primes does not change the value, `RegProd.regProd_congr_finite`).
  $L_F(1,\chi_Q)$ = `RegProd.LOne`, the limit $s \to 1^+$ of $\prod_\mathfrak p(1-\chi_Q(\mathfrak p)N\mathfrak p^{-s})^{-1}$; it exists
  and is positive (`lOne_chiP_binary`).
* *The product.* $\prod_\mathfrak p$ is Mathlib's unconditional `tprod`; the corrected factors
  $\beta_\mathfrak p(1-\chi_Q(\mathfrak p)/N\mathfrak p)^{-1}$ are $1$ outside a finite set when $m$ is represented by $Q$ over $F$,
  and some factor is $0$ otherwise (`multipliable_corrected_nf`), so the product is a genuine finite product (the regularized product,
  "$L^{-1}\times$ finite product").
* *No hypothesis* on the discriminant of $Q$, on primitivity, on the class number, or on the primes dividing $m$ or $2\det H_Q$.

**Proves (unconditional; packaging of `siegelFormulaAt2_nf`).**
* **`siegelFormula_binary_totallyReal`** — the statement above.
* **`genusAverage_binary_totallyReal`** — the genus average form:
  $\bigl(\sum r_M(m)/|O(M)|\bigr)/\bigl(\sum 1/|O(M)|\bigr) = \tfrac12\,|d_F|^{-1/2}\prod_\sigma\beta_\sigma(m)\,L_F(1,\chi_Q)^{-1}\prod_\mathfrak p\cdots$.
* **`siegelFormula_binary_totallyReal_natural`** — the natural-order Euler-product form, given only the convention input
  `NaturalOrderEulerOne (chiP · Q)` (a prime ideal theorem for $\chi_Q$): $\prod_{N\mathfrak p \le X}\beta_\mathfrak p(Q,m)$ converges
  (in the order of the norm) to the value $L_F(1,\chi_Q)^{-1}\prod_\mathfrak p\beta_\mathfrak p(1-\chi_Q(\mathfrak p)/N\mathfrak p)^{-1}$
  that appears in the formula.
* `multipliable_corrected_nf`, `archRepDensity_two`.

Source: Siegel 1935, Hauptsatz ($n = 2$, $\varepsilon = \tfrac12$); Siegel 1937 (over number fields) [unverified locators].
-/

open NumberField IsDedekindDomain Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open Lattices NFEuler RegProd LocalDensity QuadForm QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F]

/-- **$\beta_\sigma$ in rank 2:** `archRepDensity 2 a d` $= \pi\,d^{-1/2}$, independent of $a$ (the exponent $(N-2)/2$ vanishes). -/
theorem archRepDensity_two (a d : ℝ) : archRepDensity 2 a d = Real.pi * d ^ (-(1 / 2 : ℝ)) := by
  rw [archRepDensity]
  norm_num [Real.Gamma_one]

variable [IsTotallyReal F]

/-- **The corrected local factors have a genuine product** (unconditional): for $Q$ totally positive definite binary and
$m \gg 0$, the factors $\beta_\mathfrak p(Q,m)\,(1-\chi_Q(\mathfrak p)/N\mathfrak p)^{-1}$ are unconditionally multipliable: they are
$1$ outside a finite set when $m$ is represented over $F$ (`two_mul_tamagawaKReg_mul_repMass_frame2`), and one of
them is $0$ otherwise (`exists_localDensity_eq_zero_of_not_rep`). -/
theorem multipliable_corrected_nf (Q : QuadForm (𝓞 F) 2) (hpd : IsTotallyPosDef (formF Q)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    Multipliable fun v => NF.localDensity v Q m * (1 - chiP v Q / (normP v : ℝ)) ^ (-1 : ℤ) := by
  by_cases h : ∃ ξ, (formF Q).eval ξ = algebraMap (𝓞 F) F m
  · obtain ⟨ξ, hξ⟩ := h
    have hρ : algebraMap (𝓞 F) F m ≠ 0 :=
      (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (ne_zero_of_totallyPos hm)
    obtain ⟨fr⟩ := exists_adaptedFrame (n := 1) (formF Q) hξ hρ
    exact multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _)
      (two_mul_tamagawaKReg_mul_repMass_frame2 Q hpd hm fr).2
  · obtain ⟨v, h0⟩ := exists_localDensity_eq_zero_of_not_rep Q hpd hm h
    exact (hasProd_zero_of_exists_eq_zero ⟨v, by simp only [h0, zero_mul]⟩).multipliable

/-- The unfolded right-hand side equals `(1/2) * mass * siegelProduct2Reg Q m`. -/
theorem siegelProduct2Reg_unfold (Q : QuadForm (𝓞 F) 2) (m : 𝓞 F) :
    siegelProduct2Reg Q m =
      |(discr F : ℝ)| ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 2 ‖σ (algebraMap (𝓞 F) F m)‖ (detGram Q σ)) *
        ((LOne fun v => chiP v Q)⁻¹ *
          ∏' v, NF.localDensity v Q m / (1 - chiP v Q / (normP v : ℝ))) := by
  rw [siegelProduct2Reg, siegelProductWith, regProd]
  simp only [_root_.zpow_neg_one, div_eq_mul_inv]
  norm_num

/-- **Siegel's theorem for binary forms over a totally real number field** (unconditional; every term unfolded). Let $F$ be a
totally real number field (any class number), $Q$ a totally positive definite binary quadratic form over $\mathcal O_F$
(**any** discriminant, primitive or not), and $m \in \mathcal O_F$ totally positive. Then
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(\mathcal O_F^2)}\frac{r_M(m)}{|O(M)|}
 = \frac12\Bigl(\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(\mathcal O_F^2)}\frac1{|O(M)|}\Bigr)\,|d_F|^{-1/2}
 \prod_{\sigma}\beta_\sigma(m)\cdot L_F(1,\chi_Q)^{-1}\prod_{\mathfrak p}\frac{\beta_\mathfrak p(Q,m)}{1-\chi_Q(\mathfrak p)N\mathfrak p^{-1}}.$$
* the sums run over the isometry classes of **all** lattices in the genus of $\mathcal O_F^2$ in $(F^2, Q)$ — all of them free
  for every $h_F$ (`genusFree_formF`), so these are the $\mathrm{GL}_2(\mathcal O_F)$-classes of forms in the genus of $Q$
  (`siegelFormula_binary_totallyReal_forms`); $|O(M)|$ counts proper and improper isometries (`LatClass.autCard`); $r_M(m)$ = `LatClass.repCount`;
* $\sigma$ runs over the $[F:\mathbb Q]$ real embeddings, $\beta_\sigma(m)$ = `archRepDensity 2 |σ m| (detGram Q σ)`
  $= \pi\det(\sigma H_Q/2)^{-1/2}$;
* $\chi_Q$ = `chiP · Q` (the character of $F(\sqrt{-\det(H_Q/2)})/F$, $0$ at $\mathfrak p \mid 2\det H_Q$), $L_F(1,\chi_Q)$ = `LOne`,
  $\beta_\mathfrak p$ = `NF.localDensity` at every prime (dyadic and ramified included), $\prod_\mathfrak p$ the unconditional `tprod`
  of a family with finite support or a zero factor (`multipliable_corrected_nf`);
* no hypothesis on the discriminant, primitivity, the class number, or the primes dividing $m$.
Packaging of `siegelFormulaAt2_nf` ($\tau^{\mathrm{reg}}(SO_2) = 2$, `binaryTamagawaTwoReg_nf`). -/
@[kb "siegel1935" "Hauptsatz, n = 2 (ε = 1/2, regularized), over a totally real field, unfolded [unverified]"]
theorem siegelFormula_binary_totallyReal (Q : QuadForm (𝓞 F) 2) (hpd : IsTotallyPosDef (formF Q)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    ∑ᶠ c ∈ genusClasses (formF Q) (stdLat F 2),
        (LatClass.repCount (formF Q) c (algebraMap (𝓞 F) F m) : ℝ) / LatClass.autCard (formF Q) c =
      (1 / 2 : ℝ) * (∑ᶠ c ∈ genusClasses (formF Q) (stdLat F 2), ((LatClass.autCard (formF Q) c : ℝ))⁻¹) *
        (|(discr F : ℝ)| ^ (-(1 / 2 : ℝ)) *
          (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 2 ‖σ (algebraMap (𝓞 F) F m)‖ (detGram Q σ)) *
          ((LOne fun v => chiP v Q)⁻¹ *
            ∏' v, NF.localDensity v Q m / (1 - chiP v Q / (normP v : ℝ)))) := by
  have h := (siegelFormulaAt2_nf Q hpd hm).repMass_eq
  rw [siegelProduct2Reg_unfold] at h
  exact h

/-- **The genus-average form** (unconditional): the $1/|O(M)|$-weighted average of $r_M(m)$ over the classes in the genus
of $\mathcal O_F^2$ (all lattice classes; every one is free, `genusFree_formF`) is
$$\frac{\sum r_M(m)/|O(M)|}{\sum 1/|O(M)|} = \tfrac12\,|d_F|^{-1/2}\prod_\sigma\beta_\sigma(m)\cdot L_F(1,\chi_Q)^{-1}
\prod_\mathfrak p\frac{\beta_\mathfrak p(Q,m)}{1-\chi_Q(\mathfrak p)N\mathfrak p^{-1}},$$
for every totally positive definite binary $Q$ over $\mathcal O_F$ (any discriminant, primitive or not) and every $m \gg 0$. -/
@[kb "siegel1935" "Hauptsatz, n = 2 (genus average), over a totally real field, unfolded [unverified]"]
theorem genusAverage_binary_totallyReal (Q : QuadForm (𝓞 F) 2) (hpd : IsTotallyPosDef (formF Q)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    (∑ᶠ c ∈ genusClasses (formF Q) (stdLat F 2),
        (LatClass.repCount (formF Q) c (algebraMap (𝓞 F) F m) : ℝ) / LatClass.autCard (formF Q) c) /
      (∑ᶠ c ∈ genusClasses (formF Q) (stdLat F 2), ((LatClass.autCard (formF Q) c : ℝ))⁻¹) =
      (1 / 2 : ℝ) *
        (|(discr F : ℝ)| ^ (-(1 / 2 : ℝ)) *
          (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 2 ‖σ (algebraMap (𝓞 F) F m)‖ (detGram Q σ)) *
          ((LOne fun v => chiP v Q)⁻¹ *
            ∏' v, NF.localDensity v Q m / (1 - chiP v Q / (normP v : ℝ)))) := by
  have h := genusAverage_eq_nf Q hpd hm
  rw [siegelProduct2Reg_unfold] at h
  exact h

/-- **The natural-order Euler-product form** (convention input only): given `NaturalOrderEulerOne (chiP · Q)`
($\prod_{N\mathfrak p\le X}(1-\chi_Q(\mathfrak p)/N\mathfrak p)^{-1} \to L_F(1,\chi_Q)$, a prime ideal theorem for $\chi_Q$; a theorem
over $\mathbb Q$), the partial products $\prod_{N\mathfrak p\le X}\beta_\mathfrak p(Q, m)$ (in the order of the norm, `normOrder F`)
converge to $P = L_F(1,\chi_Q)^{-1}\prod_\mathfrak p\beta_\mathfrak p(Q,m)(1-\chi_Q(\mathfrak p)/N\mathfrak p)^{-1}$, and
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(\mathcal O_F^2)}\frac{r_M(m)}{|O(M)|}
 = \frac12\Bigl(\sum\frac1{|O(M)|}\Bigr)\,|d_F|^{-1/2}\prod_\sigma\beta_\sigma(m)\cdot P.$$ -/
@[kb "siegel1935" "Hauptsatz, n = 2 (natural order), over a totally real field, unfolded [unverified]"]
theorem siegelFormula_binary_totallyReal_natural (Q : QuadForm (𝓞 F) 2) (hpd : IsTotallyPosDef (formF Q)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (hN : NaturalOrderEulerOne fun v => chiP v Q) :
    HasProd (fun v => NF.localDensity v Q m)
        ((LOne fun v => chiP v Q)⁻¹ * ∏' v, NF.localDensity v Q m / (1 - chiP v Q / (normP v : ℝ)))
        (normOrder F) ∧
      ∑ᶠ c ∈ genusClasses (formF Q) (stdLat F 2),
          (LatClass.repCount (formF Q) c (algebraMap (𝓞 F) F m) : ℝ) / LatClass.autCard (formF Q) c =
        (1 / 2 : ℝ) * (∑ᶠ c ∈ genusClasses (formF Q) (stdLat F 2), ((LatClass.autCard (formF Q) c : ℝ))⁻¹) *
          (|(discr F : ℝ)| ^ (-(1 / 2 : ℝ)) *
            (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 2 ‖σ (algebraMap (𝓞 F) F m)‖ (detGram Q σ)) *
            ((LOne fun v => chiP v Q)⁻¹ *
              ∏' v, NF.localDensity v Q m / (1 - chiP v Q / (normP v : ℝ)))) := by
  refine ⟨?_, siegelFormula_binary_totallyReal Q hpd hm⟩
  have h := (siegelFormulaAt2_natural_nf Q hpd hm hN).1
  have e : regProd (fun v => chiP v Q) (-1) (fun v => NF.localDensity v Q m) =
      (LOne fun v => chiP v Q)⁻¹ * ∏' v, NF.localDensity v Q m / (1 - chiP v Q / (normP v : ℝ)) := by
    rw [regProd]; simp only [_root_.zpow_neg_one, div_eq_mul_inv]
  rwa [e] at h

end QuadFormsKB.Tamagawa
