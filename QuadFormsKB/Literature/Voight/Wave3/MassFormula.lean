/-
# The Eichler mass formula for maximal orders, unconditionally (Voight, Theorems 15.5.5, 25.1.1, 26.1.12)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Theorem 15.5.5 (p. 249),
Theorem 25.1.1 (p. 415), Main Theorem 26.1.5 (p. 432), Theorem 26.1.12 (p. 433).

The library first proved the mass formula for maximal orders conditional on the named input
`MassWave2.MaximalOrderDiscriminant F` (Theorem 15.5.5, "only if"). That input is proved for every number
field (`Disc.maximalOrderDiscriminant`, file `LocalDiscriminant.lean`), so the following are **unconditional**:
* `classMass_eq_maximal`: for $F$ totally real with $\mathbb Z_F$ a principal ideal domain, $B = (a,b)_F$ totally
  definite and a maximal order $\mathcal O \supseteq \mathbb Z_F\langle i,j\rangle$,
  $$\operatorname{mass}(\operatorname{Cls}\mathcal O) = \frac{2\,\zeta_F(2)}{(2\pi)^{2n}}\,|d_F|^{3/2}\,h_F
  \prod_{\mathfrak p \mid \mathfrak D}(N\mathfrak p - 1), \qquad n = [F:\mathbb Q];$$
* `classMass_eq_rat_maximal`: over $\mathbb Q$, $\operatorname{mass}(\operatorname{Cls}\mathcal O) = \varphi(D)/12$.

**Restrictions** (inherited from the repository's analytic proof `QuatOrder.eichler_mass_formula'`):
$\mathbb Z_F$ a principal ideal domain and $\mathcal O \supseteq \mathbb Z_F\langle i,j\rangle$ (`stdOrder F a b ≤ O`);
Voight's theorem holds for every maximal order and every class number.
-/
import QuadFormsKB.Literature.Voight.Wave3.LocalDiscriminant

set_option linter.unusedSectionVars false

open NumberField Quaternion
open scoped Real

noncomputable section

namespace QuadFormsKB.Voight.Wave3

open QuadFormsKB.Quat QuadFormsKB.QuatOrder QuadFormsKB.NFEuler QuadFormsKB.Voight.MassWave2

/-- **The Eichler mass formula for maximal orders** (Voight 2021, Theorem 26.1.12 with level $\mathfrak M = R$;
Main Theorem 26.1.5), unconditional: for a totally real number field $F$ with $\mathbb Z_F$ a principal ideal domain,
$B = (a,b)_F$ totally definite ($a, b \in \mathbb Z_F$ nonzero) and a maximal order
$\mathcal O \supseteq \mathbb Z_F\langle i,j\rangle$,
$$\operatorname{mass}(\operatorname{Cls}\mathcal O) = \frac{2\,\zeta_F(2)}{(2\pi)^{2n}}\,|d_F|^{3/2}\,h_F
\prod_{\mathfrak p \mid \mathfrak D}(N\mathfrak p - 1),$$
$\mathfrak D = \prod_{\mathfrak p \in \operatorname{Ram}_f B}\mathfrak p$ (`ramFin`), $n = [F : \mathbb Q]$. -/
@[kb "voight2021" "Main Theorem 26.1.5, p. 432; Theorem 26.1.12, p. 433"]
theorem classMass_eq_maximal {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [IsPrincipalIdealRing (𝓞 F)]
    {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b)
    {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsMaximalOrder (𝓞 F) F O) (hstd : stdOrder F a b ≤ O) :
    classMass O = 2 * dedekindZetaR F 2 / (2 * Real.pi) ^ (2 * Module.finrank ℚ F) *
        |(NumberField.discr F : ℝ)| ^ (3 / 2 : ℝ) * (NumberField.classNumber F : ℝ) *
        ∏ v ∈ ramFin ha hb, ((Ideal.absNorm v.asIdeal : ℝ) - 1) :=
  classMass_eq_of_maximalOrderDiscriminant (Disc.maximalOrderDiscriminant F) ha hb hdef hO hstd

/-- **The Eichler mass formula over $\mathbb Q$** (Voight 2021, Theorem 25.1.1 = Theorem 25.3.15), unconditional: for a
definite quaternion algebra $B = (a,b)_{\mathbb Q}$ of discriminant $D$ and a maximal order
$\mathcal O \supseteq \mathbb Z\langle i,j\rangle$,
$$\sum_{[J] \in \operatorname{Cls}\mathcal O}\frac1{w_J} = \frac{\varphi(D)}{12} = \frac1{12}\prod_{p \mid D}(p - 1).$$ -/
@[kb "voight2021" "Theorem 25.1.1, p. 415; Theorem 25.3.15, p. 422"]
theorem classMass_eq_rat_maximal {a b : 𝓞 ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b)
    {O : Subalgebra (𝓞 ℚ) (QuatF ℚ a b)} (hO : IsMaximalOrder (𝓞 ℚ) ℚ O) (hstd : stdOrder ℚ a b ≤ O) :
    classMass O = (∏ v ∈ ramFin ha hb, ((Ideal.absNorm v.asIdeal : ℝ) - 1)) / 12 :=
  classMass_eq_rat_of_maximalOrderDiscriminant (Disc.maximalOrderDiscriminant ℚ) ha hb hdef hO hstd

end QuadFormsKB.Voight.Wave3
