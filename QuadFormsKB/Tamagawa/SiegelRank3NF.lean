import QuadFormsKB.Tamagawa.BinaryNormOne
import QuadFormsKB.Tamagawa.TernaryTamagawaNF
import QuadFormsKB.Tamagawa.BinaryTauRat

/-!
# Siegel's formula in rank 3 over every totally real field

**Layer:** $F$ totally real (any class number), $Q_0$ a totally positive definite ternary form over $\mathcal O_F$
($L = \mathcal O_F^3$), $m \in \mathcal O_F$ totally positive.

Assembles the frame identity (`siegelFormulaAt3_of_diag`) with the theorem $\tau(SO_3) = 2$ for every totally real $F$
(`tamagawaNumberTwo_ternary_nf`, from `QuatOrder.ternaryTamagawaTwo_nf`):

* **`siegelFormulaAt3_nf`**: `BinaryTamagawaTwoRegDiag F` $\Rightarrow$ `SiegelFormulaAt3 Q₀ m` for every $Q_0$ and every totally
  positive $m$ — the input $\tau^{\mathrm{reg}}(SO_2) = 2$ is proved (`binaryTamagawaTwoRegDiag_nf`,
  `binaryTamagawaTwoReg_nf`; see `siegelFormulaAt3_nf_uncond`), and by
  `binaryTamagawaTwoRegDiag_iff_massFormula` is the mass formula $\mathrm{Mass}(\mathcal O_F^2,\langle1,D\rangle)\cdot
  S^{\mathrm{reg}}_2(\langle1,D\rangle,1) = 1$ of the orders $\mathcal O_F[\sqrt{-D}]$.
* **`siegelFormulaAt3_natural_nf`**: with the named input `NaturalOrderEulerOne (chiTern Q₀ m)` (a prime ideal theorem for
  $\chi_m$ over $F$, not in Mathlib or the repository) the local product is also the natural-order limit
  $\lim_X\prod_{N\mathfrak p\le X}\beta_\mathfrak p(L, m)$ (`hasProd_normOrder_regProd`).

Over $\mathbb Q$ both inputs are theorems (`binaryTamagawaTwoReg_rat`, `isEulerProductValue_eulerProductReg3`).

Source: Siegel 1935, Hauptsatz; Weil 1982, §4.5 [unverified locators]; Hanke 2004, (5.3), p. 368 (natural order).
-/

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open Lattices NFEuler RegProd LocalDensity QuadForm QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-- **Rank-3 Siegel over every totally real field, given $\tau^{\mathrm{reg}}(SO_2) = 2$:** for every totally positive definite
ternary $Q_0$ over $\mathcal O_F$ and every totally positive $m$,
$$\sum_{\mathrm{cls}M\subseteq\mathrm{gen}(\mathcal O_F^3)}\frac{r_M(m)}{|O(M)|} = \mathrm{Mass}(\mathcal O_F^3)\cdot|d_F|^{-1}\prod_\sigma\beta_\sigma(m)
\cdot L_F(1,\chi_m)\prod_\mathfrak p\beta_\mathfrak p(m)\bigl(1-\chi_m(\mathfrak p)N\mathfrak p^{-1}\bigr).$$
$\tau(SO_3) = 2$ holds for any class number (`tamagawaNumberTwo_ternary_nf`); the frame identity is the one above. -/
@[kb "siegel1935" "Hauptsatz, n = 3, over a totally real field (regularized product) [unverified]"]
theorem siegelFormulaAt3_nf (hB : BinaryTamagawaTwoRegDiag F) (Q₀ : QuadForm (𝓞 F) 3)
    (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt3 Q₀ m :=
  siegelFormulaAt3_of_diag Q₀ hpd (tamagawaNumberTwo_ternary_nf Q₀ hpd) hB hm

/-- **The natural-order reading over $F$:** given in addition `NaturalOrderEulerOne (chiTern Q₀ m)`, the partial products
$\prod_{N\mathfrak p\le X}\beta_\mathfrak p(\mathcal O_F^3, m)$ converge to the regularized value
$L_F(1,\chi_m)\prod_\mathfrak p\beta_\mathfrak p(1-\chi_m(\mathfrak p)/N\mathfrak p)$ used in `siegelProduct3`, so Siegel's formula holds with
the local product read in Siegel's natural order. -/
@[kb "hanke2004" "(5.3), p. 368 (n = 3, natural order), over a totally real field"]
theorem siegelFormulaAt3_natural_nf (hB : BinaryTamagawaTwoRegDiag F) (Q₀ : QuadForm (𝓞 F) 3)
    (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (hN : NaturalOrderEulerOne (chiTern Q₀ m)) :
    HasProd (fun v => NF.localDensity v Q₀ m) (regProd (chiTern Q₀ m) 1 fun v => NF.localDensity v Q₀ m)
        (normOrder F) ∧
      SiegelFormulaAt3 Q₀ m := by
  refine ⟨?_, siegelFormulaAt3_nf hB Q₀ hpd hm⟩
  have hQ : Q₀.Nondegenerate := nondegenerate_of_isTotallyPosDef hpd
  have hm0 : m ≠ 0 := by
    rintro rfl
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
    simpa using hm v
  have hmul := multipliable_localDensity_mul_chiTern hQ hm0
  simp only [zpow_one] at hmul
  exact hasProd_normOrder_regProd hN (fun v => abs_chiTern_le v Q₀ m) hmul.hasProd

/-- **Cross-check over $\mathbb Q$: the mass formula of $\mathbb Z[\sqrt{-D}]$ with Siegel's factors at $1$** (unconditional): for
$\langle1,D\rangle$ positive definite, $\mathrm{Mass}(\mathbb Z^2,\langle1,D\rangle)\cdot S^{\mathrm{reg}}_2(\langle1,D\rangle,1) = 1$ — i.e.
$\tau^{\mathrm{reg}}(SO_2) = 2$ over $\mathbb Q$ through `binaryTamagawaTwoRegDiag_iff_massFormula`. This is the statement the plan
proves over every totally real $F$. -/
theorem massFormula_diagForm1_rat (D : 𝓞 ℚ) (hpd : IsTotallyPosDef (formF (diagForm1 D))) :
    mass (formF (diagForm1 D)) (stdLat ℚ 2) * siegelProduct2Reg (diagForm1 D) 1 = 1 :=
  BinaryNormOne.binaryTamagawaTwoRegDiag_iff_massFormula.mp BinaryTauRat.binaryTamagawaTwoRegDiag_rat D hpd

end QuadFormsKB.Tamagawa
