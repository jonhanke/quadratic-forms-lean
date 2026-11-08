/-
# Hanke 2011 (enumerating maximal definite forms): the tables of §4 against Gan–Hanke–Yu, and the mass formula (2)

J. Hanke, arXiv:1110.1876v1 (`hanke2011enumerating`), §4, pp. 6–7, formula (2).

* The mass-type of a local space is read off Gan–Hanke–Yu's local data as used in `Hanke2005.lambdaGHYOdd` /
  `Hanke2005.lambdaGHYEven` (`oddTypeOf`, `evenTypeOf`), and the paper's $\lambda_{\mathrm{odd},p}$, $\lambda_{\mathrm{even},p}$
  (`lambdaOdd`, `lambdaEven`) agree with them (`lambdaGHYOdd_eq`, `lambdaGHYEven_eq`): no second meaning is introduced.
* **(2)** over $\mathbb Q$ (`mass_formula_odd`, `mass_formula_even`): for a maximal positive definite $\mathbb Z$-valued
  form in $n\ge3$ variables,
  $$\mathrm{Mass}^+(L) = 2^{\frac{3-n}2}\prod_{k=1}^{\frac{n-1}2}|\zeta(1-2k)|\prod_p\lambda_{\mathrm{odd},p}\ (n\text{ odd}),\qquad
  \mathrm{Mass}^+(L) = 2^{\frac{2-n}2}\,|L(1-\tfrac n2,\chi)|\prod_{k=1}^{\frac{n-2}2}|\zeta(1-2k)|\prod_p\lambda_{\mathrm{even},p}\ (n\text{ even}),$$
  the specialization to $F = \mathbb Q$ of Gan–Hanke–Yu's Props. 7.4 and 7.5 (`Hanke2005.ghy_prop74`, `Hanke2005.ghy_prop75_proved`).
  Here $|\zeta(1-2k)|$ is `Hanke2005.absZetaNeg ℚ k` and $|L(1-\frac n2,\chi)|$ is `Hanke2005.absLNeg Q₀ (n/2)` (both written
  through the functional equations, since Mathlib's Dirichlet series have no values at negative integers in that form),
  the product over $p$ is over the maximal ideals $v$ of $\mathcal O_{\mathbb Q} = \mathbb Z$ with $q_v = N v = p$.
-/
import QuadFormsKB.Literature.Hanke2005.GHYConductorDyadic
import QuadFormsKB.Literature.Hanke2011Enumerating.LocalFactors

open NumberField IsDedekindDomain
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2011Enumerating

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Hanke2005

/-! ### Mass-types from Gan–Hanke–Yu's local data -/

open Classical in
/-- **The odd mass-type of Gan–Hanke–Yu's local data** ($n$ odd): $t$ = the anisotropic dimension ($1$ or $3$; $w = 1$ iff $t = 1$) and
`unitDisc` = "$\delta\in A_v^\times$", i.e. $\mathrm{ord}_v\delta$ even (`Hanke2005.DetUnitSqAt`): `gen` ($\delta$ unit, $t = 1$),
`I` ($\delta$ unit, $t\ne1$), `IIplus` ($\delta$ not a unit, $t = 1$), `IIminus` ($\delta$ not a unit, $t\ne1$). -/
def oddTypeOf (t : ℕ) (unitDisc : Prop) : OddType :=
  if unitDisc then (if t = 1 then .gen else .I) else (if t = 1 then .IIplus else .IIminus)

open Classical in
/-- **The even mass-type of Gan–Hanke–Yu's local data** ($n$ even): $t$ = the anisotropic dimension, `sq` = "$\delta$ is a square",
`ram` = "$E_\delta$ ramified", `sd` = "the maximal lattice is self-dual" (for $E_\delta$ unramified, $w = 1$ iff self-dual):
`gen` ($\delta$ square, $t = 0$; or unramified non-square, self-dual), `I` ($\delta$ square, $t\ne0$), `III` (ramified), `II`
(unramified non-square, not self-dual). -/
def evenTypeOf (t : ℕ) (sq ram sd : Prop) : EvenType :=
  if sq then (if t = 0 then .gen else .I) else if ram then .III else if sd then .gen else .II

/-- **The paper's $\lambda_{\mathrm{odd},p}$ is Gan–Hanke–Yu's $\lambda_v$** (Prop. 7.4) for $n = 2k+1$: for every $q$, $k$, $t$ and
`unitDisc`, `lambdaGHYOdd q k t unitDisc = lambdaOdd q (2k+1) (oddTypeOf t unitDisc)`. -/
@[kb "hanke2011enumerating" "§4, Table of λ_odd,p, p. 6 (= Gan–Hanke–Yu 2001, Prop. 7.4)"]
theorem lambdaGHYOdd_eq (q : ℝ) (k t : ℕ) (unitDisc : Prop) :
    lambdaGHYOdd q k t unitDisc = lambdaOdd q (2 * k + 1) (oddTypeOf t unitDisc) := by
  classical
  have e1 : 2 * k + 1 - 1 = 2 * k := by omega
  unfold lambdaGHYOdd oddTypeOf
  by_cases hu : unitDisc <;> by_cases ht : t = 1 <;> simp [hu, ht, lambdaOdd, e1]

/-- **The paper's $\lambda_{\mathrm{even},p}$ is Gan–Hanke–Yu's $\lambda_v$** (Prop. 7.5) for $n = 2k$. -/
@[kb "hanke2011enumerating" "§4, Table of λ_even,p, p. 6 (= Gan–Hanke–Yu 2001, Prop. 7.5)"]
theorem lambdaGHYEven_eq (q : ℝ) (k t : ℕ) (sq ram sd : Prop) :
    lambdaGHYEven q k t sq ram sd = lambdaEven q (2 * k) (evenTypeOf t sq ram sd) := by
  classical
  have e1 : (2 * k - 2) / 2 = k - 1 := by omega
  have e2 : 2 * k / 2 = k := by omega
  unfold lambdaGHYEven evenTypeOf
  by_cases hs : sq <;> by_cases ht : t = 0 <;> by_cases hr : ram <;> by_cases hd : sd <;>
    simp [hs, ht, hr, hd, lambdaEven, e1, e2]

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- The odd mass-type of $(V_v, Q_v)$ for $Q_0$ over $\mathcal O_F$. -/
def oddTypeAt (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n) : OddType :=
  oddTypeOf (anisoDim v Q₀) (DetUnitSqAt v Q₀)

/-- The even mass-type of $(V_v, Q_v)$ for $Q_0$ over $\mathcal O_F$. -/
def evenTypeAt (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n) : EvenType :=
  evenTypeOf (anisoDim v Q₀) (IsSquare (algebraMap F (v.adicCompletion F) (discK Q₀))) (IsRamifiedAt v Q₀)
    (dualIndexAt v Q₀ = 1)

theorem lambdaGHYAt_eq_lambdaOdd (hodd : Odd n) (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n) :
    lambdaGHYAt v Q₀ = lambdaOdd (normQ v) n (oddTypeAt v Q₀) := by
  unfold lambdaGHYAt oddTypeAt
  rw [lambdaGHYOdd_eq]
  congr 1
  obtain ⟨k, rfl⟩ := hodd
  omega

theorem lambdaGHYEvenAt_eq_lambdaEven (heven : Even n) (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n) :
    lambdaGHYEvenAt v Q₀ = lambdaEven (normQ v) n (evenTypeAt v Q₀) := by
  unfold lambdaGHYEvenAt evenTypeAt
  rw [lambdaGHYEven_eq]
  congr 1
  obtain ⟨k, rfl⟩ := heven
  omega

/-! ### The mass formula (2) over $\mathbb Q$ -/

/-- **(2), $n$ odd** (Hanke 2011, p. 6, from Gan–Hanke–Yu 2001 Prop. 7.4 with $F = \mathbb Q$): for $Q_0$ a $\mathbb Z$-valued
(i.e. $\mathcal O_{\mathbb Q}$-valued) form in $n\ge3$ variables, $n$ odd, nondegenerate, positive definite, with $\mathbb Z^n$
maximal,
$$\mathrm{Mass}^+(L) = \sum_{\mathrm{Cls}^+}\frac1{|SO(M)|} = 2^{\frac{3-n}2}\prod_{k=1}^{\frac{n-1}2}|\zeta(1-2k)|
\prod_p\lambda_{\mathrm{odd},p},$$
with $\lambda_{\mathrm{odd},p}$ = `lambdaOdd p n (oddTypeAt v Q₀)`, $p = q_v$. **Unconditional.** -/
@[kb "hanke2011enumerating" "(2), p. 6 (n odd)"]
theorem mass_formula_odd (hn : 3 ≤ n) (hodd : Odd n) (Q₀ : QuadForm (𝓞 ℚ) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 ℚ) ℚ))) (hmax : StdIsMaximal Q₀) :
    ∑' i : DC Q₀, ((Nat.card (unitGroup Q₀ i) : ℝ≥0∞))⁻¹ =
      ENNReal.ofReal ((2 : ℝ) ^ ((3 - (n : ℝ)) / 2) * (∏ k ∈ Finset.range ((n - 1) / 2), absZetaNeg ℚ (k + 1)) *
        ∏' v : HeightOneSpectrum (𝓞 ℚ), lambdaOdd (normQ v) n (oddTypeAt v Q₀)) := by
  rw [ghy_prop74 hn hodd Q₀ hQ hpd hmax]
  congr 1
  rw [tprod_congr fun v => lambdaGHYAt_eq_lambdaOdd hodd v Q₀]
  obtain ⟨k, rfl⟩ := hodd
  have e1 : (2 * k + 1) / 2 = k := by omega
  have e2 : (2 * k + 1 - 1) / 2 = k := by omega
  have e3 : (3 - ((2 * k + 1 : ℕ) : ℝ)) / 2 = 1 - (k : ℝ) := by push_cast; ring
  rw [e1, e2, e3, Module.finrank_self, mul_one, lMotiveOdd]
  rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_natCast]
  ring

/-- **(2), $n$ even** (Hanke 2011, p. 6, from Gan–Hanke–Yu 2001 Prop. 7.5 with $F = \mathbb Q$): for $n\ge4$ even,
$$\mathrm{Mass}^+(L) = 2^{\frac{2-n}2}\,|L(1-\tfrac n2,\chi)|\prod_{k=1}^{\frac{n-2}2}|\zeta(1-2k)|\prod_p\lambda_{\mathrm{even},p},$$
$\chi$ the quadratic character of $\mathbb Q(\sqrt\delta)$, $\delta = (-1)^{n/2}\det(H)/2^n$, and $|L(1-\frac n2,\chi)|$ =
`absLNeg Q₀ (n/2)`. **Unconditional.** -/
@[kb "hanke2011enumerating" "(2), p. 6 (n even)"]
theorem mass_formula_even (hn : 4 ≤ n) (heven : Even n) (Q₀ : QuadForm (𝓞 ℚ) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 ℚ) ℚ))) (hmax : StdIsMaximal Q₀) :
    ∑' i : DC Q₀, ((Nat.card (unitGroup Q₀ i) : ℝ≥0∞))⁻¹ =
      ENNReal.ofReal ((2 : ℝ) ^ ((2 - (n : ℝ)) / 2) * absLNeg Q₀ (n / 2) *
        (∏ k ∈ Finset.range ((n - 2) / 2), absZetaNeg ℚ (k + 1)) *
        ∏' v : HeightOneSpectrum (𝓞 ℚ), lambdaEven (normQ v) n (evenTypeAt v Q₀)) := by
  rw [ghy_prop75_proved hn heven Q₀ hQ hpd hmax]
  congr 1
  rw [tprod_congr fun v => lambdaGHYEvenAt_eq_lambdaEven heven v Q₀]
  obtain ⟨k, rfl⟩ := heven
  have e1 : (k + k) / 2 = k := by omega
  have e2 : (k + k - 2) / 2 = k - 1 := by omega
  have e3 : (2 - ((k + k : ℕ) : ℝ)) / 2 = 1 - (k : ℝ) := by push_cast; ring
  rw [e1, e2, e3, Module.finrank_self, mul_one, lMotiveEven, lMotiveOdd]
  rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_natCast]
  ring

end QuadFormsKB.Hanke2011Enumerating
