import QuadFormsKB.Tamagawa.BinaryTauNF

/-!
# Siegel's formula for binary forms over every totally real field

**Layer:** $F$ a totally real number field (any class number); $Q$ a totally positive definite **binary** form over $\mathcal O_F$,
$L = \mathcal O_F^2$, $m \in \mathcal O_F$ totally positive.

**Statement** (`SiegelFormulaAt2`, the rank-2 twin of the `SiegelFormulaAt3`, Siegel's constant $\varepsilon = \tfrac12$):
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(m)}{|O(M)|} = \tfrac12\,\mathrm{Mass}(L)\cdot S^{\mathrm{reg}}_2(Q,m),\qquad
S^{\mathrm{reg}}_2(Q,m) = |d_F|^{-1/2}\prod_\sigma\beta_\sigma(m)\cdot L_F(1,\chi_Q)^{-1}\prod_\mathfrak p\frac{\beta_\mathfrak p(Q,m)}{1-\chi_Q(\mathfrak p)N\mathfrak p^{-1}}$$
(the `siegelProduct2Reg`; $\chi_Q$ = the `chiP · Q`, the quadratic character of $F(\sqrt{-\det H_Q})/F$; regularized
product `regProd`).

**Proves (unconditional)**
* **`siegelFormulaAt2_nf`**: `SiegelFormulaAt2 Q m` for every totally positive definite binary $Q$ over $\mathcal O_F$ and every totally
  positive $m$ — every prime included (dyadic and ramified), every discriminant (the local factors are the library's
  `NF.localDensity` of $Q$ itself, not evaluated in closed form), every class number. For $m$ represented over $F$ it is the
  step $1\to2$ (`two_mul_tamagawaKReg_mul_repMass`) with the $\tau^{\mathrm{reg}}(SO_2) = 2$ (`binaryTamagawaTwoReg_nf`);
  otherwise both sides vanish (`siegelProduct2Reg_eq_zero_of_not_rep`, Hasse–Minkowski over $F$).
* `genusAverage_eq_nf`: the same as an average, $\mathrm{repMass}/\mathrm{Mass} = \tfrac12 S^{\mathrm{reg}}_2$.
* **`siegelFormulaAt2_natural_nf`**: given only `NaturalOrderEulerOne (chiP · Q)` (a prime ideal theorem for $\chi_Q$; convention-level
  input, a theorem over $\mathbb Q$), the regularized value is the natural-order limit of $\prod_{N\mathfrak p\le X}\beta_\mathfrak p(Q,m)$.

**Route**: the τ route, not the genus-by-genus formula `siegel_binaryF_genus'` (already unconditional:
`posClassNumberRelation`), which is stated over $K^+$ for a free $\mathcal O_K$ with $\nu$ prime to $2\Delta$ only.

Source: Siegel 1935, Hauptsatz ($n = 2$, $\varepsilon = \tfrac12$); Siegel 1937 (over number fields); Weil 1982, §4.5 and Thm. 3.7.1
[unverified locators].
-/

open NumberField IsDedekindDomain Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open Lattices NFEuler RegProd LocalDensity QuadForm QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F]

local notation "QFof" Q₀ => QuadForm.map (algebraMap (𝓞 F) F) Q₀

/-- **Siegel's formula for the number $m$ in rank $2$** (Siegel 1935, Hauptsatz with $\varepsilon = \tfrac12$ [unverified]; over a
number field: Siegel 1937 [unverified]), with the regularized product (`siegelProduct2Reg`):
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(m)}{|O(M)|} = \tfrac12\,\mathrm{Mass}(L)\cdot S^{\mathrm{reg}}_2(Q,m),\qquad L = \mathcal O_F^2.$$

Field:
- `repMass_eq`: `repMass QF L m = (1/2) * mass QF L * siegelProduct2Reg Q m`.

*Independence (hypothesis hygiene):* like `SiegelFormulaAt3`, a statement about the genus average $\mathrm{repMass}/\mathrm{Mass}$ of
the representation numbers of one number $m$; homogeneous in the weights $1/|O(M)|$, so it says nothing about $\mathrm{Mass}(L)$
itself. Over $\mathbb Q$, for $Q$ of fundamental discriminant $D < 0$, it is `Binary.siegelFormula_binary`
(regularized product = `binaryEulerValue`, `BinaryTauRat.regProd_up_eq_binaryEulerValue`). Proved for every totally real $F$:
`siegelFormulaAt2_nf`. -/
@[kb "siegel1935" "Hauptsatz, n = 2 (ε = 1/2, regularized) [unverified]"]
structure SiegelFormulaAt2 (Q : QuadForm (𝓞 F) 2) (m : 𝓞 F) : Prop where
  repMass_eq : repMass (QFof Q) (stdLat F 2) (algebraMap (𝓞 F) F m) =
    (1 / 2 : ℝ) * mass (QFof Q) (stdLat F 2) * siegelProduct2Reg Q m

variable [IsTotallyReal F]

/-- **Numbers not represented over $F$ have a vanishing local density:** Hasse–Minkowski over $F$ (`represents_iff_everywhere_nf`)
gives a place where $m$ is not represented; it is finite ($Q$ totally positive definite, $m \gg 0$), and there
$\beta_\mathfrak p(Q, m) = 0$. -/
theorem exists_localDensity_eq_zero_of_not_rep (Q : QuadForm (𝓞 F) 2) (hpd : IsTotallyPosDef (formF Q)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (h : ¬ ∃ ξ, (formF Q).eval ξ = algebraMap (𝓞 F) F m) :
    ∃ v, NF.localDensity v Q m = 0 := by
  have hρ : algebraMap (𝓞 F) F m ≠ 0 :=
    (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (ne_zero_of_totallyPos hm)
  have hQF := hpd.nondegenerate
  have hQ : Q.Nondegenerate := nondegenerate_of_map hQF
  have hnot : ¬ (formF Q).RepresentsIn F (algebraMap (𝓞 F) F m) := by
    rintro ⟨x, hx⟩; exact h ⟨x, hx⟩
  rw [represents_iff_everywhere_nf (formF Q) hQF _ hρ] at hnot
  simp only [NFPlace.Everywhere, not_forall] at hnot
  obtain ⟨p, hp⟩ := hnot
  cases p with
  | infinite w => exact absurd (representsIn_real (n := 1) Q hpd hm w) hp
  | finite v =>
    exact ⟨v, by rw [← betaZ_algebraMap]; exact betaZ_eq_zero_of_not_rep Q hQ (by omega) v hρ hp⟩

/-- **Numbers not represented over $F$:** $S^{\mathrm{reg}}_2(Q, m) = 0$ (the corrected product has the zero factor of
`exists_localDensity_eq_zero_of_not_rep`). -/
theorem siegelProduct2Reg_eq_zero_of_not_rep (Q : QuadForm (𝓞 F) 2) (hpd : IsTotallyPosDef (formF Q)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (h : ¬ ∃ ξ, (formF Q).eval ξ = algebraMap (𝓞 F) F m) : siegelProduct2Reg Q m = 0 := by
  obtain ⟨v, h0⟩ := exists_localDensity_eq_zero_of_not_rep Q hpd hm h
  unfold siegelProduct2Reg siegelProductWith regProd
  rw [tprod_of_exists_eq_zero ⟨v, by simp only [h0, zero_mul]⟩, mul_zero, mul_zero]

/-- **Siegel's formula in rank 2 from $\tau^{\mathrm{reg}}(SO(Q)) = 2$** (any totally real $F$): the step $1\to2$
(`two_mul_tamagawaKReg_mul_repMass`: $2\mu^{\mathrm{reg}}\,\mathrm{repMass} = S^{\mathrm{reg}}_2$) and $\tau^{\mathrm{reg}} =
\mu^{\mathrm{reg}}\cdot2\,\mathrm{Mass}$ (`tauSOReg_eq`). The converse direction is `tauSOReg_eq_two_of_siegel`. -/
theorem siegelFormulaAt2_of_tau (Q : QuadForm (𝓞 F) 2) (hpd : IsTotallyPosDef (formF Q)) (hτ : tauSOReg Q = 2)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt2 Q m := by
  refine ⟨?_⟩
  show repMass (formF Q) (stdLat F 2) (algebraMap (𝓞 F) F m) =
    (1 / 2 : ℝ) * mass (formF Q) (stdLat F 2) * siegelProduct2Reg Q m
  by_cases h : ∃ ξ, (formF Q).eval ξ = algebraMap (𝓞 F) F m
  · have key := two_mul_tamagawaKReg_mul_repMass Q hpd hm h
    have hQ : Q.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
    rw [tauSOReg_eq Q hQ hpd] at hτ
    rw [← key]
    linear_combination (-(repMass (formF Q) (stdLat F 2) (algebraMap (𝓞 F) F m)) / 2) * hτ
  · rw [repMass_eq_zero_of_not_rep _ _ h, siegelProduct2Reg_eq_zero_of_not_rep Q hpd hm h, mul_zero]

/-- **Siegel's formula for binary forms over every totally real field** (unconditional): for every totally positive definite
binary $Q$ over $\mathcal O_F$ and every totally positive $m \in \mathcal O_F$,
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(\mathcal O_F^2)}\frac{r_M(m)}{|O(M)|} = \tfrac12\,\mathrm{Mass}(\mathcal O_F^2)\cdot
|d_F|^{-1/2}\prod_\sigma\beta_\sigma(m)\cdot L_F(1,\chi_Q)^{-1}\prod_\mathfrak p\frac{\beta_\mathfrak p(Q,m)}{1-\chi_Q(\mathfrak p)N\mathfrak p^{-1}}.$$
Any class number, every prime (dyadic and ramified included), every discriminant of $Q$. From the
`binaryTamagawaTwoReg_nf` ($\tau^{\mathrm{reg}}(SO_2) = 2$) and `siegelFormulaAt2_of_tau`. -/
@[kb "siegel1935" "Hauptsatz, n = 2 (ε = 1/2, regularized), over a totally real field [unverified]"]
theorem siegelFormulaAt2_nf (Q : QuadForm (𝓞 F) 2) (hpd : IsTotallyPosDef (formF Q)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt2 Q m :=
  siegelFormulaAt2_of_tau Q hpd (binaryTamagawaTwoReg_nf.tau_eq_two Q hpd) hm

/-- **The genus average form** (unconditional): $\mathrm{repMass}(\mathcal O_F^2, m)/\mathrm{Mass}(\mathcal O_F^2) =
\tfrac12\,S^{\mathrm{reg}}_2(Q, m)$, i.e. the $1/|O(M)|$-weighted average of $r_M(m)$ over the classes in the genus. -/
@[kb "siegel1935" "Hauptsatz, n = 2 (genus average), over a totally real field [unverified]"]
theorem genusAverage_eq_nf (Q : QuadForm (𝓞 F) 2) (hpd : IsTotallyPosDef (formF Q)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMass (formF Q) (stdLat F 2) (algebraMap (𝓞 F) F m) / mass (formF Q) (stdLat F 2) =
      (1 / 2 : ℝ) * siegelProduct2Reg Q m := by
  have hpos := mass_pos hpd (stdLat F 2) (HilbertModular.isIntegral_stdLat Q)
  rw [(siegelFormulaAt2_nf Q hpd hm).repMass_eq, div_eq_iff hpos.ne']
  ring

/-- **The natural-order reading over $F$** (convention input only): given `NaturalOrderEulerOne (chiP · Q)`
($\prod_{N\mathfrak p\le X}(1-\chi_Q(\mathfrak p)/N\mathfrak p)^{-1} \to L_F(1,\chi_Q)$), the partial products
$\prod_{N\mathfrak p\le X}\beta_\mathfrak p(Q, m)$ converge to the regularized value
$L_F(1,\chi_Q)^{-1}\prod_\mathfrak p\beta_\mathfrak p(Q,m)(1-\chi_Q(\mathfrak p)/N\mathfrak p)^{-1}$, and Siegel's formula holds. -/
@[kb "siegel1935" "Hauptsatz, n = 2 (natural order), over a totally real field [unverified]"]
theorem siegelFormulaAt2_natural_nf (Q : QuadForm (𝓞 F) 2) (hpd : IsTotallyPosDef (formF Q)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (hN : NaturalOrderEulerOne fun v => chiP v Q) :
    HasProd (fun v => NF.localDensity v Q m) (regProd (fun v => chiP v Q) (-1) fun v => NF.localDensity v Q m)
        (normOrder F) ∧
      SiegelFormulaAt2 Q m := by
  refine ⟨?_, siegelFormulaAt2_nf Q hpd hm⟩
  set χ : HeightOneSpectrum (𝓞 F) → ℝ := fun v => chiP v Q
  set β : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.localDensity v Q m
  -- the corrected product converges unconditionally (finite support, or a zero factor)
  obtain ⟨P, hP⟩ : ∃ P, HasProd (fun v => β v * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ)) P := by
    by_cases h : ∃ ξ, (formF Q).eval ξ = algebraMap (𝓞 F) F m
    · obtain ⟨ξ, hξ⟩ := h
      have hρ : algebraMap (𝓞 F) F m ≠ 0 :=
        (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (ne_zero_of_totallyPos hm)
      obtain ⟨fr⟩ := exists_adaptedFrame (n := 1) (formF Q) hξ hρ
      exact ⟨_, (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _)
        (two_mul_tamagawaKReg_mul_repMass_frame2 Q hpd hm fr).2).hasProd⟩
    · obtain ⟨v, h0⟩ := exists_localDensity_eq_zero_of_not_rep Q hpd hm h
      exact ⟨0, hasProd_zero_of_exists_eq_zero ⟨v, by simp only [β, h0, zero_mul]⟩⟩
  obtain ⟨hL0, -⟩ := lOne_chiP_binary hpd
  have hinv := hasProd_zpow hN.hasProd hL0.ne' (-1)
  have h := hP.normOrder.mul hinv
  have e : regProd χ (-1) β = P * LOne χ ^ (-1 : ℤ) := by
    simp only [regProd, hP.tprod_eq]; ring
  rw [e]
  refine h.congr_fun fun v => ?_
  have hl : 1 - χ v / (normP v : ℝ) ≠ 0 := (one_sub_div_pos (abs_chiP_le Q v) v).ne'
  simp only [_root_.zpow_neg_one, inv_inv]
  rw [mul_assoc, inv_mul_cancel₀ hl, mul_one]

end QuadFormsKB.Tamagawa
