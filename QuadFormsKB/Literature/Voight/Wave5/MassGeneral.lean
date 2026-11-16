/-
# The Eichler mass formula for an arbitrary order: statements (Voight, 24.3.13, 25.3.19, 26.1.5, 26.6.4)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Definition 24.3.13 (p. 403),
Main Theorem 25.3.19 (p. 423), (26.1.2) and Main Theorem 26.1.5 (pp. 431–432), Proposition 26.6.4 (p. 445).

**Setting.** $F$ a totally real number field with ring of integers $R = \mathbb Z_F$, $B = (a, b)_F$ = `QuatF F a b`
totally definite, $\mathcal O \subseteq B$ an order with reduced discriminant $\mathfrak N = \operatorname{discrd}\mathcal O$
(`Voight.HasDiscrd`), $\operatorname{mass}(\operatorname{Cls}\mathcal O)$ = `clsMass O`. For a prime $\mathfrak p$ (a
`HeightOneSpectrum`), $\mathcal O_{\mathfrak p}$ = `localOrder` is the completion and $q = N\mathfrak p$.

**Contents.**
* `HasEichlerSymbolAt v O s` (**Definition 24.3.13**): $(\mathcal O \mid \mathfrak p) = (\mathcal O_{\mathfrak p} \mid \mathfrak p)$, the
  Eichler symbol (`Wave6.HasEichlerSymbol`, Definition 24.3.2) of the completion. Definition.
* `eichlerLambda s q` (**(25.3.20), (26.1.2)**): $\lambda(\mathcal O, \mathfrak p) = 1 + 1/q, 1 - 1/q, 1 - 1/q^2$ for
  $(\mathcal O \mid \mathfrak p) = 1, -1, 0$; `eichlerLambda_eq` checks the book's closed form
  $\lambda = (1 - q^{-2})/(1 - (\mathcal O \mid \mathfrak p)q^{-1})$. Definition, proved identity.
* `EichlerMassFormulaGeneralRat` (**Main Theorem 25.3.19**) and `EichlerMassFormulaGeneral F` (**Main Theorem 26.1.5**):
  $\operatorname{mass}(\operatorname{Cls}\mathcal O) = \frac{2\zeta_F(2)}{(2\pi)^{2n}}d_F^{3/2}h_F N(\mathfrak N)\prod_{\mathfrak p \mid \mathfrak N}\lambda(\mathcal O, \mathfrak p)$,
  over $\mathbb Q$: $\frac{N}{12}\prod_{p \mid N}\lambda(\mathcal O, p)$. Named propositions, not proved.
* `MassSuperorder F` (**Proposition 26.6.4**): if $\mathcal O \subseteq \mathcal O'$ agree away from $\mathfrak p$, then
  $\operatorname{mass}(\operatorname{Cls}\mathcal O) = [\mathcal O'^\times_{\mathfrak p} : \mathcal O^\times_{\mathfrak p}]\operatorname{mass}(\operatorname{Cls}\mathcal O')$.
  Named proposition, not proved.

The maximal-order and Eichler-order cases are `Voight.EichlerMassFormulaMaximal`, `Voight.EichlerMassFormulaEichlerOrders`
(Theorem 26.1.12) and `Voight.EichlerMassFormulaEichlerOrdersRat` (Theorem 25.3.18).

*Restricted hypothesis.* Over a general $F$ the reduced discriminant is read through an $R$-basis (`HasDiscrd`), so
`EichlerMassFormulaGeneral` assumes $\mathcal O$ free over $R$ (the general case, with pseudo-bases, is open).
-/
import QuadFormsKB.Literature.Voight.Wave5.EichlerSymbol
import QuadFormsKB.Literature.Voight.Wave2.Statements

open NumberField IsDedekindDomain Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Voight.Wave6

open QuadFormsKB.Quat QuadFormsKB.QuatOrder QuadFormsKB.Voight QuadFormsKB.NFEuler

variable {F : Type} [Field F] [NumberField F]

/-- **The Eichler symbol at a prime** (Voight 2021, Definition 24.3.13): $(\mathcal O \mid \mathfrak p) := (\mathcal O_{\mathfrak p} \mid \mathfrak p)$,
the Eichler symbol of the completion $\mathcal O_{\mathfrak p}$ (`localOrder`) over the valuation ring
$R_{\mathfrak p}$ (`adicCompletionIntegers`). -/
@[kb "voight2021" "Definition 24.3.13, p. 403"]
def HasEichlerSymbolAt (v : HeightOneSpectrum (𝓞 F)) {a b : 𝓞 F} (O : Subalgebra (𝓞 F) (QuatF F a b))
    (s : EichlerSym) : Prop :=
  HasEichlerSymbol (v.adicCompletionIntegers F) (localOrder (v := v) a b O) s

/-- **The local mass factor** $\lambda(\mathcal O, \mathfrak p)$ (Voight 2021, (25.3.20) and (26.1.2)) in terms of the Eichler
symbol $s = (\mathcal O \mid \mathfrak p)$ and $q = N\mathfrak p$: $1 + 1/q$ if $s = 1$, $1 - 1/q$ if $s = -1$, $1 - 1/q^2$ if
$s = 0$. (For $\mathfrak p \mid \operatorname{discrd}\mathcal O$ the symbol is never $*$, since $(\mathcal O \mid \mathfrak p) = *$ forces
$\mathcal O_{\mathfrak p} \cong \mathrm M_2(R_{\mathfrak p})$, 24.3.5; the value $1$ for $*$ is a placeholder that never enters.) -/
@[kb "voight2021" "(25.3.20), p. 423; (26.1.2), p. 431"]
def eichlerLambda (s : EichlerSym) (q : ℝ) : ℝ :=
  match s with
  | .one => 1 + 1 / q
  | .negOne => 1 - 1 / q
  | .zero => 1 - 1 / q ^ 2
  | .star => 1

/-- The integer value $1, 0, -1$ of the symbols $1, 0, -1$ (and $0$ for $*$, unused). -/
def EichlerSym.toInt : EichlerSym → ℤ
  | .one => 1
  | .zero => 0
  | .negOne => -1
  | .star => 0

/-- **The book's closed form of $\lambda$** ((25.3.20), (26.1.2)): for $s \in \{1, 0, -1\}$ and $q > 1$,
$\lambda(\mathcal O, \mathfrak p) = \dfrac{1 - q^{-2}}{1 - s\,q^{-1}}$. -/
@[kb "voight2021" "(25.3.20), p. 423; (26.1.2), p. 431"]
theorem eichlerLambda_eq (s : EichlerSym) (hs : s ≠ .star) {q : ℝ} (hq : 1 < q) :
    eichlerLambda s q = (1 - q⁻¹ ^ 2) / (1 - (s.toInt : ℝ) * q⁻¹) := by
  have hq0 : q ≠ 0 := by positivity
  have hq1 : q - 1 ≠ 0 := by linarith
  have hq2 : q + 1 ≠ 0 := by linarith
  cases s with
  | star => exact absurd rfl hs
  | one =>
    simp only [eichlerLambda, EichlerSym.toInt, Int.cast_one, one_mul]
    field_simp
    ring
  | zero =>
    simp only [eichlerLambda, EichlerSym.toInt, Int.cast_zero, zero_mul, sub_zero, div_one]
    field_simp
  | negOne =>
    simp only [eichlerLambda, EichlerSym.toInt, Int.cast_neg, Int.cast_one, neg_one_mul, sub_neg_eq_add]
    field_simp
    ring

/-- **The Eichler mass formula for an arbitrary order over $\mathbb Q$** (Voight 2021, Main Theorem 25.3.19), as a named
proposition: let $B = (a, b)_{\mathbb Q}$ be definite and $\mathcal O \subset B$ an order with $\operatorname{discrd}\mathcal O = N\mathbb Z$.
Then
$$\sum_{[J] \in \operatorname{Cls}\mathcal O}\frac1{w_J} = \frac N{12}\prod_{p \mid N}\lambda(\mathcal O, p),$$
$w_J = [\mathcal O_L(J)^\times : \mathbb Z^\times]$ (`clsMass`), with $\lambda$ from the Eichler symbols $(\mathcal O \mid p)$
(`HasEichlerSymbolAt`; quantified over every assignment $s$ of symbols, which is unique by 24.3.1). -/
@[kb "voight2021" "Main Theorem 25.3.19, p. 423"]
def EichlerMassFormulaGeneralRat : Prop :=
  ∀ (a b : 𝓞 ℚ), a ≠ 0 → b ≠ 0 → IsTotDefinite a b →
  ∀ O : Subalgebra (𝓞 ℚ) (QuatF ℚ a b), IsOrder (𝓞 ℚ) ℚ O →
  ∀ N : ℕ, HasDiscrd O (Ideal.span {(N : 𝓞 ℚ)}) →
  ∀ s : HeightOneSpectrum (𝓞 ℚ) → EichlerSym, (∀ v, HasEichlerSymbolAt v O (s v)) →
    clsMass O = (N : ℝ) / 12 *
      ∏ᶠ (v : HeightOneSpectrum (𝓞 ℚ)) (_ : v.asIdeal ∣ Ideal.span {(N : 𝓞 ℚ)}),
        eichlerLambda (s v) (Ideal.absNorm v.asIdeal)

/-- **The Eichler mass formula for an arbitrary order** (Voight 2021, Main Theorem 26.1.5), as a named proposition about the
totally real number field $F$ of degree $n$: for $B = (a,b)_F$ totally definite and an order $\mathcal O \subset B$, free
over $R$, with reduced discriminant $\mathfrak N$,
$$\operatorname{mass}(\operatorname{Cls}\mathcal O) = \frac{2\,\zeta_F(2)}{(2\pi)^{2n}}\,|d_F|^{3/2}\,h_F\,N(\mathfrak N)
\prod_{\mathfrak p \mid \mathfrak N}\lambda(\mathcal O, \mathfrak p),$$
$\lambda$ from the Eichler symbols as in `EichlerMassFormulaGeneralRat`. -/
@[kb "voight2021" "Main Theorem 26.1.5, p. 432"]
def EichlerMassFormulaGeneral (F : Type) [Field F] [NumberField F] : Prop :=
  IsTotallyReal F → ∀ (a b : 𝓞 F), a ≠ 0 → b ≠ 0 → IsTotDefinite a b →
  ∀ O : Subalgebra (𝓞 F) (QuatF F a b), IsOrder (𝓞 F) F O →
  Nonempty (Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) →
  ∀ 𝔑 : Ideal (𝓞 F), HasDiscrd O 𝔑 →
  ∀ s : HeightOneSpectrum (𝓞 F) → EichlerSym, (∀ v, HasEichlerSymbolAt v O (s v)) →
    clsMass O = 2 * dedekindZetaR F 2 / (2 * Real.pi) ^ (2 * Module.finrank ℚ F) *
      |(NumberField.discr F : ℝ)| ^ (3 / 2 : ℝ) * (NumberField.classNumber F : ℝ) * (Ideal.absNorm 𝔑 : ℝ) *
      ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : v.asIdeal ∣ 𝔑), eichlerLambda (s v) (Ideal.absNorm v.asIdeal)

/-! ### Proposition 26.6.4 -/

/-- Completion is monotone: $\mathcal O \subseteq \mathcal O'$ gives $\mathcal O_{\mathfrak p} \subseteq \mathcal O'_{\mathfrak p}$. -/
theorem localOrder_mono (v : HeightOneSpectrum (𝓞 F)) {a b : 𝓞 F} {O O' : Subalgebra (𝓞 F) (QuatF F a b)}
    (h : O ≤ O') : localOrder (v := v) a b O ≤ localOrder (v := v) a b O' := by
  intro x hx
  exact Submodule.span_mono (Set.image_mono h) hx

/-- **The local unit index** $[\mathcal O'^\times_{\mathfrak p} : \mathcal O^\times_{\mathfrak p}]$ for orders $\mathcal O \subseteq \mathcal O'$
(`Subgroup.index` of the image of $\mathcal O_{\mathfrak p}^\times$ in $\mathcal O'^\times_{\mathfrak p}$; $0$ if infinite). -/
@[kb "voight2021" "Proposition 26.6.4, p. 445"]
def localUnitIndex (v : HeightOneSpectrum (𝓞 F)) {a b : 𝓞 F} {O O' : Subalgebra (𝓞 F) (QuatF F a b)}
    (h : O ≤ O') : ℕ :=
  (Units.map (Subalgebra.inclusion (localOrder_mono v h)).toMonoidHom).range.index

/-- **Mass of a suborder** (Voight 2021, Proposition 26.6.4), as a named proposition about a totally real number field
$F$: for orders $\mathcal O \subseteq \mathcal O'$ of a totally definite $B = (a,b)_F$ and a prime $\mathfrak p$ with
$\mathcal O_{\mathfrak q} = \mathcal O'_{\mathfrak q}$ for all primes $\mathfrak q \ne \mathfrak p$,
$\operatorname{mass}(\operatorname{Cls}\mathcal O) = [\mathcal O'^\times_{\mathfrak p} : \mathcal O^\times_{\mathfrak p}]\operatorname{mass}(\operatorname{Cls}\mathcal O')$. -/
@[kb "voight2021" "Proposition 26.6.4, p. 445"]
def MassSuperorder (F : Type) [Field F] [NumberField F] : Prop :=
  IsTotallyReal F → ∀ (a b : 𝓞 F), a ≠ 0 → b ≠ 0 → IsTotDefinite a b →
  ∀ O O' : Subalgebra (𝓞 F) (QuatF F a b), IsOrder (𝓞 F) F O → IsOrder (𝓞 F) F O' → ∀ h : O ≤ O',
  ∀ 𝔭 : HeightOneSpectrum (𝓞 F), (∀ v, v ≠ 𝔭 → localOrder (v := v) a b O = localOrder (v := v) a b O') →
    clsMass O = (localUnitIndex 𝔭 h : ℝ) * clsMass O'

end QuadFormsKB.Voight.Wave6
