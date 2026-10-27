import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.RelativeCNF
import QuadFormsKB.Binary.SiegelBinary
import QuadFormsKB.Siegel.NFMainTerm

/-!
# Siegel's constant for binary forms over a totally real field: The $|d_F|^{-1/2}$ check (partial)

Siegel's formula for $n = 2$ over a totally real $F$ of degree $d$ predicts, for a genus $\mathcal G$ of totally positive binary
$\mathcal O_F$-lattices of "discriminant $E$" ($E/F$ CM) and $\nu \gg 0$,
$$r_\mathcal G(\nu) = \varepsilon\cdot|d_F|^{-(n-1)/2}\cdot\beta_\infty(\nu)\cdot L(1,\chi_{E/F})^{-1}\cdot C_\mathcal G(\nu),\qquad \varepsilon = \tfrac12,$$
in the repository's normalizations (Lebesgue $\beta_w$, $\mathrm{vol}(\mathcal O_\mathfrak p) = 1$, `eisQ_coeff_eq_discr_mul_aENF` for the factor
$|d_F|^{-(n-1)/2}$, the regularized product convention: $C_\mathcal G(\nu)$ is the finite product of
$\beta_\mathfrak p(\nu)/(1 - \chi(\mathfrak p)N\mathfrak p^{-1})$ over $\mathfrak p \mid \nu\,\mathfrak d_{E/F}$).
This file proves the **archimedean and $L$-value part** of that constant:

* **`betaInfNF_binary`:** for every binary form $Q$ over $\mathcal O_F$, $\beta_\infty(\nu) = \pi^{r_1}\prod_w D_w^{-1/2}$, independent of $\nu$
  ($n = 2$: the exponent $(n-2)/2$ vanishes); $D_w = \det(H_w/2)$ (`Siegel.gramDetNF`).
* **`siegelConstant_binaryF`:** let $K$ be a CM field, $F = K^+$, $d = [K^+ : \mathbb Q]$, and $Q$ a totally positive binary form over
  $\mathcal O_{K^+}$ with $\prod_w D_w = |d_K|/(4^d|d_{K^+}|^2)$ (`HasNormLatticeDet`: the norm form $N_{K/K^+}$ in an $\mathcal O_{K^+}$-basis of $\mathcal O_K$
  has this determinant, see below). With $L(1,\chi) = \lim_{s\to1^+}L(s,\chi_{K/K^+})$ (`relativeClassNumberFormula_hasse`),
  $$\tfrac12\,|d_{K^+}|^{-1/2}\,\beta_\infty(\nu)\,L(1,\chi)^{-1} = \frac{Q_K\,w_K\,h_{K^+}}{2\,h_K}.$$
  **This is the check of the factor $|d_F|^{-(n-1)/2} = |d_F|^{-1/2}$ for $n = 2$:** $\beta_\infty \propto |d_F|$ and $L(1,\chi)^{-1} \propto |d_F|^{-1/2}$,
  so exactly the factor $|d_F|^{-1/2}$ makes the constant a rational number built from class numbers and units, as the genus
  average (a ratio of integers) requires; with the factor omitted the constant would be $\sqrt{|d_F|}\,Q_Kw_Kh_{K^+}/(2h_K)$.
* **`siegelConstant_rat`** (cross-check at $F = \mathbb Q$): for $D < 0$ fundamental and $f$ of discriminant $D$,
  $\tfrac12\,\beta_\infty\,L(1,\chi_D)^{-1} = \frac{w}{2h}$, the constant of `siegelSide_explicit`; this is the formula above with
  $|d_\mathbb Q| = 1$, $Q = 1$, $h_\mathbb Q = 1$.

**Why `HasNormLatticeDet` holds for the norm form** (classical; *not formalized*, so it is a hypothesis, classified as a
*condition* on $Q$): if $\mathcal O_K = \mathcal O_{K^+}b_0 \oplus \mathcal O_{K^+}b_1$, the Gram matrix of $N$ is $(\mathrm{Tr}(b_i\bar b_j))/2$-type with
$\det(H/2) = -\mathrm{disc}_{K/K^+}(b)/4$, and $|d_K| = |d_{K^+}|^2\,|N_{K^+/\mathbb Q}(\mathrm{disc}_{K/K^+}(b))|$ (tower formula; Mathlib has its
ideal form `natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`, not the basis form). For a non-free $\mathcal O_K$ the
lattice is not given by a form in two variables, and the repository's $\beta_\infty$ (`Siegel.betaInfNF`) is not defined.

*Update:* `HasNormLatticeDet` is proved for the norm form $Q_b$ of every $\mathcal O_{K^+}$-basis $b$ of $\mathcal O_K$
(`RelNormDisc.hasNormLatticeDet`, from the discriminant tower `discr_tower`), and `siegelConstant_binaryF_basis` is the unconditional
form; the good-prime densities are in `RelDensities.lean`.

**Not done:** the local densities $\beta_\mathfrak p(\nu)$ of the norm lattices over $F$ (in particular at dyadic and
ramified $\mathfrak p$), the genus average over $F$ and hence Siegel's formula itself over $F$; these need genus theory over $F$
(`RelGenus.lean` has only its first step). The class-sum identity `sum_repNumLat_eq` (all classes and unit twists together) is
proved in `RelRepCount.lean`.

Sources: Siegel, *Ann. Math.* 36 (1935) [unverified locator]; Hanke 2004, (5.3)–(5.5); Washington, Thm. 4.17
[unverified locator]; Shimura, *Arithmetic of Quadratic Forms* (2010) [unverified locator].
-/

open NumberField Module Filter Topology Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Binary.Rel

/-! ### $\beta_\infty$ for binary forms over $F$ -/

section BetaInf

variable {F : Type} [Field F] [NumberField F]

/-- **$\beta_w$ of a binary form:** $\beta_w(\nu) = \pi\,D_w^{-1/2}$ (Hanke (5.5) with $n = 2$, $\omega_2 = \pi$; independent of $\nu$). -/
@[kb "hanke2004" "(5.5), p. 369 (n = 2, at a real place)"]
theorem betaInfAt_binary (Q : QuadForm (𝓞 F) 2) (w : Siegel.RealPlace F) (ν : F) :
    Siegel.betaInfAt Q w ν = Real.pi * Siegel.gramDetNF Q w ^ (-(1 / 2 : ℝ)) := by
  rw [Siegel.betaInfAt, unitBallVol_two, show (((2 : ℕ) : ℝ) - 2) / 2 = 0 by norm_num, Real.rpow_zero,
    mul_one]
  push_cast
  ring

/-- **$\beta_\infty$ of a binary form over $F$:** $\beta_\infty(\nu) = \pi^{r_1}\big(\prod_w D_w\big)^{-1/2}$ for a totally positive
definite $Q$ ($r_1$ = number of real places), independent of $\nu$. -/
@[kb "hanke2004" "(5.3), (5.5), pp. 368–369 (n = 2)"]
theorem betaInfNF_binary {Q : QuadForm (𝓞 F) 2} (hQ : Siegel.IsTotallyPosDef Q) (ν : F) :
    Siegel.betaInfNF Q ν =
      Real.pi ^ Fintype.card (Siegel.RealPlace F) *
        (∏ w : Siegel.RealPlace F, Siegel.gramDetNF Q w) ^ (-(1 / 2 : ℝ)) := by
  rw [Siegel.betaInfNF]
  simp_rw [betaInfAt_binary]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Real.finsetProd_rpow _ _ (fun w _ => (Siegel.gramDetNF_pos hQ w).le)]

end BetaInf

/-! ### The constant over a CM field -/

section CM

variable (K : Type) [Field K] [NumberField K] [IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- **The discriminant condition of the norm lattice** (a *condition* on a binary form $Q$ over $\mathcal O_{K^+}$):
$\prod_w D_w(Q) = |d_K|/(4^d\,|d_{K^+}|^2)$, $d = [K^+ : \mathbb Q]$, $D_w = \det(H_w/2)$. The relative norm form $N_{K/K^+}$ in an
$\mathcal O_{K^+}$-basis of $\mathcal O_K$ (when $\mathcal O_K$ is free over $\mathcal O_{K^+}$) satisfies it; see the module docstring. -/
@[kb "hanke2004" "(5.5) (D at the real places); Neukirch Ch. III §2 (discriminant tower) [unverified]"]
structure HasNormLatticeDet (Q : QuadForm (𝓞 K⁺) 2) : Prop where
  /-- $\prod_w D_w = |d_K|/(4^d|d_{K^+}|^2)$. -/
  prod_gramDet : ∏ w : Siegel.RealPlace K⁺, Siegel.gramDetNF Q w =
    |(discr K : ℝ)| / (4 ^ finrank ℚ K⁺ * |(discr K⁺ : ℝ)| ^ 2)

theorem card_realPlace : Fintype.card (Siegel.RealPlace K⁺) = finrank ℚ K⁺ := by
  rw [IsTotallyReal.finrank (K := K⁺), InfinitePlace.nrRealPlaces]

/-- **Siegel's constant for $n = 2$ over $F = K^+$: the $|d_F|^{-1/2}$ check.** For $Q$ totally positive with the determinant of
the norm lattice (`HasNormLatticeDet`), every $\nu$, and $\lambda = L(1,\chi_{K/K^+}) = \lim_{s\to1^+}L(s,\chi_{K/K^+})$:
$$\tfrac12\,|d_{K^+}|^{-1/2}\,\beta_\infty(\nu)\,\lambda^{-1} = \frac{Q_K\,w_K\,h_{K^+}}{2\,h_K}.$$ -/
@[kb "hanke2004" "(5.3)–(5.5); Washington Thm. 4.17 [unverified]; eisQ_coeff_eq_discr_mul_aENF"]
theorem siegelConstant_binaryF {Q : QuadForm (𝓞 K⁺) 2} (hQ : Siegel.IsTotallyPosDef Q)
    (hdet : HasNormLatticeDet K Q) (ν : K⁺) {lam : ℝ} (hlam : Tendsto (relLR K⁺ K) (𝓝[>] 1) (𝓝 lam)) :
    (1 / 2 : ℝ) * |(discr K⁺ : ℝ)| ^ (-(1 / 2 : ℝ)) * Siegel.betaInfNF Q ν / lam =
      IsCMField.indexRealUnits K * Units.torsionOrder K * classNumber K⁺ / (2 * classNumber K) := by
  have hL := tendsto_nhds_unique hlam (relativeClassNumberFormula_hasse K)
  rw [hL, betaInfNF_binary hQ, hdet.prod_gramDet, card_realPlace]
  set d := finrank ℚ K⁺
  have hQK : (0 : ℝ) < IsCMField.indexRealUnits K := by
    rcases hasseUnitIndex_eq_one_or_two K with h | h <;> rw [h] <;> norm_num
  have hw : (0 : ℝ) < Units.torsionOrder K := Nat.cast_pos.mpr (Units.torsionOrder_pos K)
  have hhF : (0 : ℝ) < classNumber K⁺ := Nat.cast_pos.mpr (classNumber_pos _)
  have hhK : (0 : ℝ) < classNumber K := Nat.cast_pos.mpr (classNumber_pos _)
  have hdF : (0 : ℝ) < |(discr K⁺ : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero _))
  have hdK : (0 : ℝ) < |(discr K : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  have h4 : (0 : ℝ) < 4 ^ d := by positivity
  -- convert the rpow's to square roots
  rw [Real.rpow_neg hdF.le, ← Real.sqrt_eq_rpow,
    Real.rpow_neg (div_pos hdK (mul_pos h4 (pow_pos hdF 2))).le, ← Real.sqrt_eq_rpow,
    Real.sqrt_div' _ (mul_pos h4 (pow_pos hdF 2)).le, Real.sqrt_mul h4.le, Real.sqrt_sq hdF.le,
    show (4 : ℝ) ^ d = (2 ^ d) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
    Real.sqrt_sq (by positivity)]
  have hsF : 0 < Real.sqrt |(discr K⁺ : ℝ)| := Real.sqrt_pos.mpr hdF
  have hsK : 0 < Real.sqrt |(discr K : ℝ)| := Real.sqrt_pos.mpr hdK
  have hsF2 : Real.sqrt |(discr K⁺ : ℝ)| ^ 2 = |(discr K⁺ : ℝ)| := Real.sq_sqrt hdF.le
  rw [mul_pow]
  field_simp
  exact hsF2.symm

end CM

/-! ### Cross-check at $F = \mathbb Q$ -/

/-- **Cross-check at $F = \mathbb Q$:** for fundamental $D < 0$ and $f$ of discriminant $D$,
$\tfrac12\,\beta_\infty\,L(1,\chi_D)^{-1} = \frac{w}{2h}$ — the constant of `siegelSide_explicit`, and the formula of
`siegelConstant_binaryF` with $|d_\mathbb Q| = 1$, $Q = 1$, $h_\mathbb Q = 1$. -/
@[kb "hanke2004" "(5.3)–(5.5); cf. siegelSide_explicit"]
theorem siegelConstant_rat {D : ℤ} [IsQuadDisc D] (hD : D < 0) (f : BinQF) (hfD : f.disc = D) (m : ℝ) :
    (1 / 2 : ℝ) * Siegel.betaInf f m / ((kroneckerChar D).LFunction 1).re =
      Units.torsionOrder (QField D) / (2 * classNumber (QField D)) := by
  rw [betaInf_binary f (by rw [hfD]; exact hD), classNumberFormula_neg hD, Complex.ofReal_re, hfD,
    abs_of_neg (by exact_mod_cast hD : (D : ℝ) < 0)]
  have hs : 0 < Real.sqrt (-(D : ℝ)) := Real.sqrt_pos.mpr (by
    have : (D : ℝ) < 0 := by exact_mod_cast hD
    linarith)
  have hw : (0 : ℝ) < Units.torsionOrder (QField D) := Nat.cast_pos.mpr (Units.torsionOrder_pos _)
  have hh : (0 : ℝ) < classNumber (QField D) := Nat.cast_pos.mpr (classNumber_pos _)
  field_simp

end QuadFormsKB.Binary.Rel
