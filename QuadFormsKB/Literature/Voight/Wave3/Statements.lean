/-
# Mass of a suborder and class number one: statements (Voight, Proposition 26.6.4, Theorem 25.4.1)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Theorem 25.4.1 (p. 431),
Proposition 26.6.4 (p. 451).

**Model** (as in `Voight/MassFormula.lean`): $F$ a number field, $B = (a,b)_F$ = `QuatF F a b`, orders are
`Subalgebra (𝓞 F) (QuatF F a b)`, `classMass O` $= \sum_{[J]}1/[\mathcal O_L(J)^\times : \mathbb Z_F^\times]$, completions
$\mathcal O_v$ = `localOrder`, $\mathfrak D = \prod_{\mathfrak p \in \operatorname{Ram}_f B}\mathfrak p$ (`ramFin`).

Both results are **stated, not proved** (named propositions):
* `MassSuborderOnePlace F` (Proposition 26.6.4): if $\mathcal O \subseteq \mathcal O'$ are orders of a totally definite $B$
  whose completions agree away from one finite place $v$, then
  $\operatorname{mass}(\operatorname{Cls}\mathcal O) = [\mathcal O_v'^\times : \mathcal O_v^\times]\operatorname{mass}(\operatorname{Cls}\mathcal O')$.
  It needs the comparison of the class sets of $\mathcal O$ and $\mathcal O'$ (Lemma 26.6.2), not formalized.
* `ClassNumberOneMaximalRat` (Theorem 25.4.1): a maximal order of a definite quaternion algebra over $\mathbb Q$ of
  discriminant $D$ has class number one iff $D \in \{2, 3, 5, 7, 13\}$. It needs the unit groups $w_J$ beyond the mass
  formula `Wave3.classMass_eq_rat_maximal` (proved).
-/
import QuadFormsKB.Literature.Voight.Wave3.MassFormula

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain Quaternion

noncomputable section

namespace QuadFormsKB.Voight.Wave3

open QuadFormsKB.Quat QuadFormsKB.QuatOrder

/-- Completion is monotone: $\mathcal O \subseteq \mathcal O'$ gives $\mathcal O_v \subseteq \mathcal O'_v$. -/
theorem localOrder_mono {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} {O O' : Subalgebra (𝓞 F) (QuatF F a b)}
    (hle : O ≤ O') (v : HeightOneSpectrum (𝓞 F)) : localOrder (v := v) a b O ≤ localOrder (v := v) a b O' :=
  Submodule.span_mono (Set.image_mono hle)

/-- **The mass of a suborder differing at one place** (Voight 2021, Proposition 26.6.4), as a named proposition about
the number field $F$: let $B = (a,b)_F$ be totally definite, $\mathcal O \subseteq \mathcal O'$ orders and $v$ a finite place
with $\mathcal O_w = \mathcal O'_w$ for every finite place $w \ne v$. Then
$$\operatorname{mass}(\operatorname{Cls}\mathcal O) = [\mathcal O_v'^\times : \mathcal O_v^\times]\,
\operatorname{mass}(\operatorname{Cls}\mathcal O'),$$
the index of the unit group of $\mathcal O_v$ (embedded by inclusion) in that of $\mathcal O'_v$. The masses are `clsMass`
(classes of locally principal left ideals, the book's $\operatorname{Cls}$); *correction:* `classMass` before,
which counts non-invertible ideals of the suborder too. Stated, not proved. -/
@[kb "voight2021" "Proposition 26.6.4, p. 451"]
def MassSuborderOnePlace (F : Type) [Field F] [NumberField F] : Prop :=
  ∀ (a b : 𝓞 F), a ≠ 0 → b ≠ 0 → IsTotDefinite a b →
    ∀ (O O' : Subalgebra (𝓞 F) (QuatF F a b)), IsOrder (𝓞 F) F O → IsOrder (𝓞 F) F O' →
      ∀ (hle : O ≤ O') (v : HeightOneSpectrum (𝓞 F)),
        (∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → localOrder (v := w) a b O = localOrder (v := w) a b O') →
          clsMass O = ((Units.map (Subalgebra.inclusion (localOrder_mono hle v)).toMonoidHom).range.index : ℝ) *
            clsMass O'

/-- **Class number one for maximal orders over $\mathbb Q$** (Voight 2021, Theorem 25.4.1), as a named proposition: for a
definite quaternion algebra $B = (a,b)_{\mathbb Q}$ ($a, b < 0$) of discriminant $D = \prod_{p \in \operatorname{Ram}_f B}p$ and a
maximal order $\mathcal O \subset B$, the number of classes of nonzero (invertible) left ideals of $\mathcal O$ is $1$ iff
$D \in \{2, 3, 5, 7, 13\}$. Stated, not proved. -/
@[kb "voight2021" "Theorem 25.4.1, p. 431"]
def ClassNumberOneMaximalRat : Prop :=
  ∀ (a b : 𝓞 ℚ) (ha : a ≠ 0) (hb : b ≠ 0), IsTotDefinite a b →
    ∀ O : Subalgebra (𝓞 ℚ) (QuatF ℚ a b), IsMaximalOrder (𝓞 ℚ) ℚ O →
      (Nat.card {c : Quotient (idealSetoid O) // c.out ≠ ⊥} = 1 ↔
        ∏ v ∈ ramFin ha hb, Ideal.absNorm v.asIdeal ∈ ({2, 3, 5, 7, 13} : Finset ℕ))

end QuadFormsKB.Voight.Wave3
