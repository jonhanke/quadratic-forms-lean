/-
# O'Meara §93D: Examples 93:18 and 93:20 over completions of number fields

The abstract statements of Examples 93:18 (iii)–(vi) and 93:20 (`Sec93D18Q.lean`, `Sec93D18T.lean`,
`Sec93D18Five.lean`, `Sec93D18Six.lean`, `Sec93D20.lean`) are made over an abstract Henselian discrete valuation ring
$R$ with finite residue field and fraction field $F$ satisfying the Hilbert-symbol axioms `LocalHilbertField`. Here
they are specialized to $R = \mathcal O_{\mathfrak p}$ and $F = F_\mathfrak p$, the completion of a number field at a
finite place $\mathfrak p$ (as in the last section of `Sec91Local.lean`); the `LocalHilbertField` hypothesis is
discharged by `HasseIsoNF.localHilbertField_adicCompletion`. The dyadic hypothesis
$2 \notin \mathcal O_{\mathfrak p}^\times$ is kept.

**Proves**
* `omeara93_18_iii_nf` (**93:18 (iii)**), `omeara93_18_iv_nf` (**93:18 (iv)**), `omeara93_18_v_nf` and
  `omeara93_18_v_normGroup_nf` (**93:18 (v)**), `omeara93_18_vi_nf` (**93:18 (vi)**) for dyadic completions of
  number fields;
* `omeara93_20_nf` (**93:20**) for dyadic completions of number fields.
-/
import QuadFormsKB.Literature.OMeara.Sec93D20
import QuadFormsKB.Literature.OMeara.Sec93D18Six
import QuadFormsKB.Literature.OMeara.Sec91Local

open QuadraticMap Submodule Module IsLocalRing QuadFormsKB.PadicClass
open NumberField IsDedekindDomain
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.D18

section NumberFieldCompletion

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {V : Type*} [AddCommGroup V] [Module (v.adicCompletion F) V]
  [FiniteDimensional (v.adicCompletion F) V]
  [Module (v.adicCompletionIntegers F) V] [IsScalarTower (v.adicCompletionIntegers F) (v.adicCompletion F) V]
variable (Q : QuadraticForm (v.adicCompletion F) V)

/-- **93:18 (iii) for $F_\mathfrak p$** (O'Meara 1963, pp. 260–261): `omeara93_18_iii` at a dyadic finite place
$\mathfrak p$ of a number field $F$, with $R = \mathcal O_\mathfrak p$ and the field $F_\mathfrak p$. For a unimodular
lattice $L$ of rank $4$ on a $4$-dimensional space over $F_\mathfrak p$ with norm generator $a$ and weight generator $b$
such that $\operatorname{ord} a + \operatorname{ord} b$ is odd, the conclusions about $\alpha \in \mathfrak a b$ and the
exclusive alternative of the two block decompositions hold exactly as in the abstract statement. The hypothesis
`h2p` ($2$ is not a unit of $\mathcal O_\mathfrak p$, i.e. $\mathfrak p \mid 2$) is kept. -/
@[kb "omeara1963" "§93D, 93:18 (iii), pp. 260–261 (completion of a number field)"]
theorem omeara93_18_iii_nf (h2p : ¬ IsUnit (2 : v.adicCompletionIntegers F))
    {π : v.adicCompletionIntegers F} (hπ : Irreducible π)
    (hV : finrank (v.adicCompletion F) V = 4) {L : Submodule (v.adicCompletionIntegers F) V} (hfg : L.FG)
    (hU : IsUnimodular Q L) (hrk : finrank (v.adicCompletionIntegers F) L = 4)
    {a b : v.adicCompletion F} (ha : IsNormGenerator Q L a) (hb : IsWeightGenerator Q L b)
    (hodd : Odd (dord hπ a + dord hπ b)) {α : v.adicCompletionIntegers F}
    (hd : ∃ e : Basis (Fin 4) (v.adicCompletionIntegers F) L, (gram Q fun i => (e i : V)).det =
      1 + algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) α)
    (hdef : quadDefect (v.adicCompletionIntegers F)
      (1 + algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) α) =
      span (v.adicCompletionIntegers F) {algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) α})
    {ρ : v.adicCompletionIntegers F}
    (hρ : quadDefect (v.adicCompletionIntegers F)
      (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (1 + 4 * ρ)) =
      span (v.adicCompletionIntegers F) {(4 : v.adicCompletion F)}) :
    algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) α ∈
        (v.adicCompletionIntegers F) ∙ (a * b) ∧
      Xor' (HasBlk Q L a (-(algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) α) / a) b 0)
        (HasBlk Q L a (-(algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) α -
            4 * algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ρ) / a) b
          (4 * algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ρ / b)) :=
  omeara93_18_iii (R := v.adicCompletionIntegers F) Q (HasseIsoNF.localHilbertField_adicCompletion v) h2p hπ hV
    hfg hU hrk ha hb hodd hd hdef hρ

/-- **93:18 (iv) for $F_\mathfrak p$** (O'Meara 1963, p. 261): `omeara93_18_iv` at a dyadic finite place
$\mathfrak p$ of a number field $F$, with $R = \mathcal O_\mathfrak p$ and the field $F_\mathfrak p$. A unimodular
ternary lattice $L$ over $\mathcal O_\mathfrak p$ with odd $\operatorname{ord} a + \operatorname{ord} b$ and
determinant $d$ is of exactly one of the two block forms: either $L$ has a block with $b$ and $-d$, or one with $b$,
$4\rho/b$ and $-d(1-4\rho)$, where $\rho$ is as in the hypothesis `hρ`. The hypothesis `h2p` ($\mathfrak p \mid 2$)
is kept. -/
@[kb "omeara1963" "§93D, 93:18 (iv), p. 261 (completion of a number field)"]
theorem omeara93_18_iv_nf (h2p : ¬ IsUnit (2 : v.adicCompletionIntegers F))
    {π : v.adicCompletionIntegers F} (hπ : Irreducible π)
    (hV : finrank (v.adicCompletion F) V = 3) {L : Submodule (v.adicCompletionIntegers F) V} (hfg : L.FG)
    (hU : IsUnimodular Q L) (hrk : finrank (v.adicCompletionIntegers F) L = 3)
    {a b : v.adicCompletion F} (ha : IsNormGenerator Q L a) (hb : IsWeightGenerator Q L b)
    (hodd : Odd (dord hπ a + dord hπ b)) {d : v.adicCompletionIntegers F}
    (hd : ∃ e : Basis (Fin 3) (v.adicCompletionIntegers F) L, (gram Q fun i => (e i : V)).det =
      algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) d)
    {ρ : v.adicCompletionIntegers F}
    (hρ : quadDefect (v.adicCompletionIntegers F)
      (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (1 + 4 * ρ)) =
      span (v.adicCompletionIntegers F) {(4 : v.adicCompletion F)}) :
    Xor' (HasBlk1 Q L b 0 (-algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) d))
      (HasBlk1 Q L b (4 * algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ρ / b)
        (-(algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) d *
          (1 - 4 * algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ρ)))) :=
  omeara93_18_iv (R := v.adicCompletionIntegers F) Q (HasseIsoNF.localHilbertField_adicCompletion v) h2p hπ hV
    hfg hU hrk ha hb hodd hd hρ

/-- **93:18 (v) for $F_\mathfrak p$** (O'Meara 1963, p. 261): `omeara93_18_v` at a dyadic finite place
$\mathfrak p$ of a number field $F$, with $R = \mathcal O_\mathfrak p$ and the field $F_\mathfrak p$. A unimodular
lattice $L$ of rank $\ge 5$ contains vectors $x, y$ with $Q(x) = Q(y) = 0$ and $B(x, y) = 1$, so $L$ splits off a
hyperbolic plane $A(0,0)$. The hypothesis `h2p` ($\mathfrak p \mid 2$) is kept. -/
@[kb "omeara1963" "§93D, 93:18 (v), p. 261 (completion of a number field)"]
theorem omeara93_18_v_nf (h2p : ¬ IsUnit (2 : v.adicCompletionIntegers F))
    {L : Submodule (v.adicCompletionIntegers F) V} (hfg : L.FG) (hU : IsUnimodular Q L)
    (hrk : 5 ≤ finrank (v.adicCompletionIntegers F) L) :
    ∃ x ∈ L, ∃ y ∈ L, Q x = 0 ∧ Q y = 0 ∧ bil Q x y = 1 :=
  omeara93_18_v (R := v.adicCompletionIntegers F) Q (HasseIsoNF.localHilbertField_adicCompletion v) h2p hfg hU
    hrk

/-- **93:18 (v), "and so $\mathfrak g L = Q(L)$", for $F_\mathfrak p$** (O'Meara 1963, p. 261):
`omeara93_18_v_normGroup` at a dyadic finite place $\mathfrak p$ of a number field $F$, with
$R = \mathcal O_\mathfrak p$. A unimodular lattice $L$ of rank $\ge 5$ has norm group $\mathfrak g L$ equal to the set
of values $Q(L)$. The hypothesis `h2p` ($\mathfrak p \mid 2$) is kept. -/
@[kb "omeara1963" "§93D, 93:18 (v), p. 261 (gL = Q(L)) (completion of a number field)"]
theorem omeara93_18_v_normGroup_nf (h2p : ¬ IsUnit (2 : v.adicCompletionIntegers F))
    {L : Submodule (v.adicCompletionIntegers F) V} (hfg : L.FG) (hU : IsUnimodular Q L)
    (hrk : 5 ≤ finrank (v.adicCompletionIntegers F) L) :
    (normGroup Q L : Set (v.adicCompletion F)) = Q '' (L : Set V) :=
  omeara93_18_v_normGroup (R := v.adicCompletionIntegers F) Q
    (HasseIsoNF.localHilbertField_adicCompletion v) h2p hfg hU hrk

/-- **93:18 (vi) for $F_\mathfrak p$** (O'Meara 1963, pp. 261–262): `omeara93_18_vi` at a dyadic finite place
$\mathfrak p$ of a number field $F$, with $R = \mathcal O_\mathfrak p$ and the field $F_\mathfrak p$. For a unimodular
lattice $L$ of rank $4$ on a $4$-dimensional space with determinant $1$ (up to the stated basis), norm generator $a$
and weight generator $b$: if $V$ is isotropic then $L$ has the block form $A(a, 0) \perp A(b, 0)$ (`HasBlk Q L a 0 b 0`),
and if $V$ is anisotropic then $L$ has the block form with parameters $4\rho/a$ and $4\rho/b$. The hypothesis `h2p`
($\mathfrak p \mid 2$) is kept. -/
@[kb "omeara1963" "§93D, 93:18 (vi), pp. 261–262 (completion of a number field)"]
theorem omeara93_18_vi_nf (h2p : ¬ IsUnit (2 : v.adicCompletionIntegers F))
    {π : v.adicCompletionIntegers F} (hπ : Irreducible π)
    (hV : finrank (v.adicCompletion F) V = 4) {L : Submodule (v.adicCompletionIntegers F) V} (hfg : L.FG)
    (hU : IsUnimodular Q L) (hrk : finrank (v.adicCompletionIntegers F) L = 4)
    {a b : v.adicCompletion F} (ha : IsNormGenerator Q L a) (hb : IsWeightGenerator Q L b)
    (hd : ∃ e : Basis (Fin 4) (v.adicCompletionIntegers F) L, (gram Q fun i => (e i : V)).det = 1)
    {ρ : v.adicCompletionIntegers F}
    (hρ : quadDefect (v.adicCompletionIntegers F)
      (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (1 + 4 * ρ)) =
      span (v.adicCompletionIntegers F) {(4 : v.adicCompletion F)}) :
    ((∃ v : V, v ≠ 0 ∧ Q v = 0) → HasBlk Q L a 0 b 0) ∧
      ((¬ ∃ v : V, v ≠ 0 ∧ Q v = 0) →
        HasBlk Q L a (4 * algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ρ / a) b
          (4 * algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ρ / b)) :=
  omeara93_18_vi (R := v.adicCompletionIntegers F) Q (HasseIsoNF.localHilbertField_adicCompletion v) h2p hπ hV
    hfg hU hrk ha hb hd hρ

/-- **93:20 for $F_\mathfrak p$** (O'Meara 1963, p. 262): `omeara93_20` at a dyadic finite place $\mathfrak p$ of a
number field $F$, with $R = \mathcal O_\mathfrak p$ and the field $F_\mathfrak p$. If $L$ is a modular lattice of rank
$\ge 3$ then $\theta(O^+(L)) \supseteq \mathfrak u$: every unit $\varepsilon$ of $\mathcal O_\mathfrak p$ is the spinor
norm of some $\sigma \in O^+(L)$. The hypothesis `h2p` ($\mathfrak p \mid 2$) is kept. -/
@[kb "omeara1963" "§93D, 93:20, p. 262 (completion of a number field)"]
theorem omeara93_20_nf (h2p : ¬ IsUnit (2 : v.adicCompletionIntegers F))
    {a : Submodule (v.adicCompletionIntegers F) (v.adicCompletion F)}
    {L : Submodule (v.adicCompletionIntegers F) V}
    (hfg : L.FG) (hL : IsModular Q a L) (hrk : 3 ≤ finrank (v.adicCompletionIntegers F) L)
    {ε : v.adicCompletionIntegers F} (hε : IsUnit ε) :
    ∃ σ ∈ orthLatPlus Q L, HasSpinorNorm Q σ
      (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ε) :=
  omeara93_20 (R := v.adicCompletionIntegers F) Q (HasseIsoNF.localHilbertField_adicCompletion v) h2p hfg hL hrk
    hε

end NumberFieldCompletion

end QuadFormsKB.OMeara.D18
