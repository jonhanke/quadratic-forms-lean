/-
# The Eichler mass formula: statements (Voight, Ch. 25–26)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021, Theorem 25.1.1, Theorem 25.3.15,
Main Theorem 26.1.5 and Theorem 26.1.12 (key `voight2021`).

**Setting** (Voight 26.1.1). $F$ is a totally real number field of degree $n = [F:\mathbb Q]$,
absolute discriminant $d_F$, ring of integers $R = \mathbb Z_F$, class number $h_F$ and Dedekind zeta
function $\zeta_F$; $B$ is a totally definite quaternion algebra over $F$ with discriminant
$\mathfrak D$ (the product of the finite ramified primes) and $\mathcal O \subset B$ is an order.
The **mass** of the class set is
$$\operatorname{mass}(\operatorname{Cls}\mathcal O) = \sum_{[J] \in \operatorname{Cls}\mathcal O}
[\mathcal O_L(J)^\times : R^\times]^{-1}$$
(Definition 26.1.4), and for a maximal order (Theorem 26.1.12 with level $\mathfrak M = R$)
$$\operatorname{mass}(\operatorname{Cls}\mathcal O) = \frac{2\,\zeta_F(2)}{(2\pi)^{2n}}\, d_F^{3/2}\, h_F
\prod_{\mathfrak p \mid \mathfrak D} (N\mathfrak p - 1).$$
Over $\mathbb Q$ this is $\sum_{[J]} 1/w_J = \varphi(D)/12$ (Theorem 25.1.1 = Theorem 25.3.15).

**Model in this repository.** $B = (a, b)_F$ = `QuatF F a b` with $a, b \in \mathbb Z_F$ nonzero and
`IsTotDefinite a b`; orders are `Subalgebra (𝓞 F) (QuatF F a b)`, maximal ones `IsMaximalOrder`.
The repository sums over classes of nonzero **left** ideals $J$ with the unit group $\Gamma_J$ of the
**right** order (`QuatOrder.rStab`) and the subgroup $R^\times$ (`QuatOrder.centralUnitsIn`); Voight
uses right ideals and left orders. The two conventions give the same mass (the standard involution
exchanges them); for a maximal order every nonzero integral one-sided ideal is invertible and every
class contains an integral ideal, so this is $\operatorname{Cls}\mathcal O$.

**Status.**
* `EichlerMassFormulaMaximal F` (Theorem 26.1.12 for maximal orders, i.e. Main Theorem 26.1.5
  with $\operatorname{discrd}\mathcal O = \mathfrak D$) and `EichlerMassFormulaRat`
  (Theorem 25.1.1) are statements (named propositions), not proved here.
* What the repository proves (`QuatOrder.eichler_mass_formula_nf`, Theorem 26.5.4) is the same
  identity with the left side multiplied by an explicit lattice constant
  $\Lambda_{\mathcal O}$ (`QuatOrder.massConstNF`); the missing input is the value of
  $\Lambda_{\mathcal O}$, i.e. the covolume of a maximal order ($\operatorname{disc}\mathcal O = \mathfrak D^2$).
-/
import QuadFormsKB.Tamagawa.EichlerMassNF
import QuadFormsKB.Siegel.ThetaCharacter

open NumberField Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Voight

open QuadFormsKB.Quat QuadFormsKB.QuatOrder QuadFormsKB.NFEuler

variable {F : Type} [Field F] [NumberField F]

/-- **The mass of the class set** (Voight 2021, Definition 26.1.4):
$$\operatorname{mass}(\operatorname{Cls}\mathcal O) = \sum_{[J]} [\Gamma_J : R^\times]^{-1},$$
the sum over the classes $[J]$ of nonzero left ideals of $\mathcal O$ (classes under
$J \sim J\beta$, $\beta \in B^\times$: `QuatOrder.idealSetoid`), $\Gamma_J$ the unit group of the right
order of $J$ (`QuatOrder.rStab`) and $R^\times = \mathbb Z_F^\times$ (`QuatOrder.centralUnitsIn`).
For a totally definite algebra the indices are finite and there are finitely many classes; the sum is
a `tsum` (it is $0$ by convention if not summable). -/
@[kb "voight2021" "Definition 26.1.4, p. 432"]
def classMass {a b : 𝓞 F} (O : Subalgebra (𝓞 F) (QuatF F a b)) : ℝ :=
  ∑' c : {c : Quotient (idealSetoid O) // c.out ≠ ⊥},
    (((centralUnitsIn (R := 𝓞 F) c.1.out).index : ℕ) : ℝ)⁻¹

/-- **The Eichler mass formula for maximal orders** (Voight 2021, Theorem 26.1.12 with level
$\mathfrak M = R$; Main Theorem 26.1.5 for $\operatorname{discrd}\mathcal O = \mathfrak D$), as a named
proposition about the totally real number field $F$: for all nonzero $a, b \in \mathbb Z_F$ with
$B = (a,b)_F$ totally definite and every maximal order $\mathcal O \subset B$,
$$\operatorname{mass}(\operatorname{Cls}\mathcal O) = \frac{2\,\zeta_F(2)}{(2\pi)^{2n}}\,|d_F|^{3/2}\,h_F
\prod_{\mathfrak p \in \operatorname{Ram}_f(B)} (N\mathfrak p - 1),$$
$n = [F : \mathbb Q]$, $d_F$ the discriminant, $h_F$ the class number. ($\zeta_F(2)$ is real:
`NFEuler.dedekindZetaR`.) Stated, not proved here; see the module docstring for what is proved. -/
@[kb "voight2021" "Main Theorem 26.1.5, p. 432; Theorem 26.1.12, p. 433"]
def EichlerMassFormulaMaximal (F : Type) [Field F] [NumberField F] : Prop :=
  ∀ (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0), IsTotDefinite a b →
    ∀ O : Subalgebra (𝓞 F) (QuatF F a b), IsMaximalOrder (𝓞 F) F O →
      classMass O = 2 * dedekindZetaR F 2 / (2 * Real.pi) ^ (2 * Module.finrank ℚ F) *
        |(NumberField.discr F : ℝ)| ^ (3 / 2 : ℝ) * (NumberField.classNumber F : ℝ) *
        ∏ v ∈ ramFin ha hb, ((Ideal.absNorm v.asIdeal : ℝ) - 1)

/-- **The Eichler mass formula over $\mathbb Q$, maximal orders** (Voight 2021, Theorem 25.1.1 =
Theorem 25.3.15), as a named proposition: for a definite quaternion algebra $B = (a,b)_{\mathbb Q}$
of discriminant $D$ and a maximal order $\mathcal O \subset B$,
$$\sum_{[J] \in \operatorname{Cls}\mathcal O} \frac{1}{w_J} = \frac{\varphi(D)}{12}, \qquad
w_J = \#\mathcal O_L(J)^\times/\{\pm 1\},\quad \varphi(D) = \prod_{p \mid D}(p - 1).$$
Stated, not proved here. It is the case $F = \mathbb Q$ of `EichlerMassFormulaMaximal`
($\zeta(2) = \pi^2/6$, $d_{\mathbb Q} = h_{\mathbb Q} = n = 1$). -/
@[kb "voight2021" "Theorem 25.1.1, p. 415; Theorem 25.3.15, p. 422"]
def EichlerMassFormulaRat : Prop :=
  ∀ (a b : 𝓞 ℚ) (ha : a ≠ 0) (hb : b ≠ 0), IsTotDefinite a b →
    ∀ O : Subalgebra (𝓞 ℚ) (QuatF ℚ a b), IsMaximalOrder (𝓞 ℚ) ℚ O →
      classMass O = (∏ v ∈ ramFin ha hb, ((Ideal.absNorm v.asIdeal : ℝ) - 1)) / 12

/-- **The Eichler class number formula over $\mathbb Q$, maximal orders** (Voight 2021,
Theorem 30.1.5 with level $M = 1$), as a named proposition: for a definite quaternion algebra
$B = (a,b)_{\mathbb Q}$ of discriminant $D$ and a maximal order $\mathcal O \subset B$,
$$\#\operatorname{Cls}\mathcal O = \frac{\varphi(D)}{12} + \frac14 \prod_{p \mid D}\Bigl(1 - \Bigl(\frac{-4}{p}\Bigr)\Bigr)
+ \frac13 \prod_{p \mid D}\Bigl(1 - \Bigl(\frac{-3}{p}\Bigr)\Bigr)$$
with the Kronecker symbols $\left(\frac{-4}{p}\right)$, $\left(\frac{-3}{p}\right)$ (`Siegel.kroneckerSym`)
(the conditions $4 \nmid N$, $9 \nmid N$ of the theorem hold since $N = D$ is squarefree). The class
number counts the classes of nonzero left ideals (`QuatOrder.idealSetoid`). Stated, not proved here:
it needs the optimal embedding numbers of Chapter 30. -/
@[kb "voight2021" "Theorem 30.1.5, p. 543"]
def EichlerClassNumberFormulaRat : Prop :=
  ∀ (a b : 𝓞 ℚ) (ha : a ≠ 0) (hb : b ≠ 0), IsTotDefinite a b →
    ∀ O : Subalgebra (𝓞 ℚ) (QuatF ℚ a b), IsMaximalOrder (𝓞 ℚ) ℚ O →
      (Nat.card {c : Quotient (idealSetoid O) // c.out ≠ ⊥} : ℝ) =
        (∏ v ∈ ramFin ha hb, ((Ideal.absNorm v.asIdeal : ℝ) - 1)) / 12 +
        (∏ v ∈ ramFin ha hb, (1 - (Siegel.kroneckerSym (-4) (Ideal.absNorm v.asIdeal) : ℝ))) / 4 +
        (∏ v ∈ ramFin ha hb, (1 - (Siegel.kroneckerSym (-3) (Ideal.absNorm v.asIdeal) : ℝ))) / 3

/-! ### The class set of a general order (locally principal ideals) -/

/-- **Locally principal left ideal** (Voight 2021, Definition 16.2.4; Main Theorem 16.6.1 and 16.7.7: for lattices in a
quaternion algebra over a Dedekind domain, locally principal is equivalent to invertible): a left ideal $J$ of $\mathcal O$ is
locally principal if for every finite place $v$ its completion is principal,
$J_v = \mathcal O_v\alpha_v$ with $\alpha_v \in B_v^\times$ (`QuatOrder.localIdeal`, `QuatOrder.localOrder`; completions in
place of the book's localizations $J_{(\mathfrak p)}$). Then $\mathcal O_L(J) = \mathcal O$ and $J$ is invertible, so the classes
of nonzero locally principal left ideals form $\operatorname{Cls}\mathcal O$ (section 17.1, with left and right exchanged, as in
`classMass`). For a maximal order every nonzero left ideal is locally principal (`clsMass_eq_classMass`); for a
non-maximal order this is a genuine condition: for an Eichler order $\mathcal O$ of level $\mathfrak p$ and a maximal order
$\mathcal O' \supsetneq \mathcal O$, the left ideal $J = \mathfrak p\mathcal O' \subseteq \mathcal O$ has left order $\mathcal O'$ and is excluded. -/
@[kb "voight2021" "Definition 16.2.4, p. 259; Main Theorem 16.6.1, p. 267"]
def IsLocPrincipal {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)} (J : Ideal O) : Prop :=
  ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ α : (QuatV v a b)ˣ,
    idealSet (localIdeal (v := v) J) = rTrans (localOrder (v := v) a b O : Set (QuatV v a b)) α

/-- **The class set** $\operatorname{Cls}\mathcal O$ (Voight 2021, 17.1 and Definition 26.1.4) of an order: the classes
$[J]$ (under $J \sim J\beta$, `QuatOrder.idealSetoid`) of nonzero locally principal left ideals of $\mathcal O$. -/
@[kb "voight2021" "17.1, p. 278"]
abbrev ClsO {a b : 𝓞 F} (O : Subalgebra (𝓞 F) (QuatF F a b)) : Type :=
  {c : Quotient (idealSetoid O) // c.out ≠ ⊥ ∧ IsLocPrincipal c.out}

/-- **The mass of the class set of an order** (Voight 2021, Definition 26.1.4):
$\operatorname{mass}(\operatorname{Cls}\mathcal O) = \sum_{[J] \in \operatorname{Cls}\mathcal O}[\Gamma_J : R^\times]^{-1}$, the sum over the
classes of nonzero **locally principal** left ideals (`ClsO`), with $\Gamma_J$ and $R^\times$ as in `classMass`. Equal to
`classMass O` for maximal orders (`clsMass_eq_classMass`). -/
@[kb "voight2021" "Definition 26.1.4, p. 432"]
def clsMass {a b : 𝓞 F} (O : Subalgebra (𝓞 F) (QuatF F a b)) : ℝ :=
  ∑' c : ClsO O, (((centralUnitsIn (R := 𝓞 F) c.1.out).index : ℕ) : ℝ)⁻¹

/-- **The class number** $\#\operatorname{Cls}\mathcal O$ of an order (`Nat.card`; finite: Theorem 17.1.1 over $\mathbb Q$, Main Theorem 17.7.1 in general). -/
@[kb "voight2021" "17.1, p. 278"]
def clsNum {a b : 𝓞 F} (O : Subalgebra (𝓞 F) (QuatF F a b)) : ℕ := Nat.card (ClsO O)

end QuadFormsKB.Voight
