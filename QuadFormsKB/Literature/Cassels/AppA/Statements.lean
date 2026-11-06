/-
# Cassels, Appendix A: the cited results stated as named statements

Cassels, *Rational Quadratic Forms* (1978), Appendix A (*Definite forms*), pp. 362–367. Results that Cassels quotes
without proof, or proves only by a sketch whose steps are not in the library, are stated here as named `Prop`
structures. None of them is assumed by a theorem of the library except where said; each docstring says what a proof
needs.

**Layer.** As in `AppA/Sec2.lean` and `AppA/Watson.lean`: forms `Q : QuadForm ℚ n` on $V = \mathbb Q^n$, lattices are
$\mathcal O_{\mathbb Q}$-submodules of $\mathbb Q^n$ (Cassels' sublattices, `Lattices.addSubgroupOrderIso`); integer-valued
forms `Q : QuadForm ℤ n` with genus `Siegel.SameGenus` and classes `Siegel.genusClasses`; $\Gamma_8$ is `Siegel.e8`,
$\Gamma_{16}$ is `Lattices.gamma16`, $r\Gamma_8$ is `DefiniteForms.repE8 r`.

| Cassels | Lean |
|---|---|
| p. 363: for indefinite $\phi$ the decomposition of a decomposable lattice is never unique, except possibly $n = 2$, $\phi$ isotropic | `IndefiniteSplittingNotUnique` (named) |
| p. 364: Watson: every genus of definite forms in $n > 11$ variables has at least two classes | `WatsonTwoClasses` (named), `WatsonTwoClasses.two_le_encard` (proved from it) |
| p. 365, footnote †: Niemeier: the genus of $3\Gamma_8$ contains $22$ indecomposable classes besides $3\Gamma_8$, $\Gamma_8 + \Gamma_{16}$ | `NiemeierThreeE8` (named) |
| p. 366: Theorem 3.1 for spinor genera | `minSpinorGenusClasses`, `WatsonSpinor` (named) |
| p. 366: the two points of the spinor-genus version | `WatsonSpinorConstruction`, `WatsonSpinorTypeLattice` (named) |
-/
import QuadFormsKB.Literature.Cassels.AppA.Watson
import QuadFormsKB.Lattices.SpinorGenus

open NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.DefiniteForms

open Siegel Lattices

/-! ### §2: indefinite lattices -/

/-- **Cassels, App. A, §2, p. 363** (named statement): *the orthogonal decomposition of a decomposable lattice $\Lambda$
can never be unique when $\phi$ is indefinite, except, possibly, in the very special case $n = 2$ and $\phi$ isotropic.*
For every nondegenerate indefinite form $Q$ on $\mathbb Q^n$ (it takes a positive and a negative value) and every
lattice `L` of full rank $n$ (finitely generated, spanning $\mathbb Q^n$) that is decomposable (`IsDecomposable`), unless
$n = 2$ and $Q$ is isotropic, there are two different orthogonal splittings `S ≠ S'` of `L` into indecomposable
sublattices.

Cassels says "a similar argument shows" this, after the example $x_1^2 - 2x_2^2$ (`Lattices.indefinite_not_unique`):
apply an automorph $T$ of $\Lambda$ that does not permute the summands. A proof needs, for a decomposable indefinite
lattice, an integral automorph moving some indecomposable summand off the set of summands (for instance from the
infinitude of the automorph group of an indefinite summand of rank $\ge 2$, or of a sum of two definite summands of
opposite signs, against the finiteness of the permutations of the summands). Not proved here. -/
@[kb "cassels1978" "App. A, §2, p. 363 (indefinite φ: the decomposition is never unique, except possibly n = 2, φ isotropic)"]
structure IndefiniteSplittingNotUnique : Prop where
  /-- For all `n`, `Q`, `L` as in the statement there are splittings `S ≠ S'` into indecomposable sublattices. -/
  not_unique : ∀ (n : ℕ) (Q : QuadForm ℚ n) (L : Submodule (𝓞 ℚ) (Fin n → ℚ)),
    Q.Nondegenerate → (∃ x, 0 < Q.eval x) → (∃ y, Q.eval y < 0) →
    L.FG → Submodule.span ℚ (L : Set (Fin n → ℚ)) = ⊤ → IsDecomposable Q L →
    ¬ (n = 2 ∧ ∃ x : Fin n → ℚ, x ≠ 0 ∧ Q.eval x = 0) →
    ∃ S S' : Finset (Submodule (𝓞 ℚ) (Fin n → ℚ)),
      IsOrthSplitting Q L S ∧ (∀ K ∈ S, IsIndecomposable Q K) ∧
      IsOrthSplitting Q L S' ∧ (∀ K ∈ S', IsIndecomposable Q K) ∧ S ≠ S'

/-! ### §3: class numbers -/

/-- **Watson's theorem as quoted by Cassels** (App. A, §3, p. 364; named statement): *every genus of positive definite
forms in $n > 11$ variables contains at least $2$ classes* [Watson (1975)]. Stated with $c(n)$ = `minGenusClasses n`,
the minimum number of classes in a genus of positive definite integer-valued forms in $n$ variables (the same notion
as Theorem 3.1, `WatsonStatement`). Cassels gives no proof; a proof needs Watson's analysis of the Watson operation at
every prime (the local study of `WatsonLocalStudy`, made effective), or a mass-formula estimate. -/
@[kb "cassels1978" "App. A, §3, p. 364 (Watson: every genus in n > 11 variables has at least 2 classes)"]
structure WatsonTwoClasses : Prop where
  /-- For $n > 11$: $c(n) \ge 2$. -/
  two_le : ∀ n : ℕ, 11 < n → (2 : ℕ∞) ≤ minGenusClasses n

/-- **From `WatsonTwoClasses`:** the genus of every positive definite integer-valued form `Q` in $n > 11$ variables has at
least two classes. Arguments: `h` the named statement, `hn : 11 < n`, `hQ` positive definiteness. -/
@[kb "cassels1978" "App. A, §3, p. 364 (Watson: every genus in n > 11 variables has at least 2 classes)"]
theorem WatsonTwoClasses.two_le_encard (h : WatsonTwoClasses) {n : ℕ} (hn : 11 < n) {Q : QuadForm ℤ n}
    (hQ : IntQF.PosDef Q) : (2 : ℕ∞) ≤ (genusClasses Q).encard :=
  (h.two_le n hn).trans (iInf_le (fun Q : {Q : QuadForm ℤ n // IntQF.PosDef Q} => (genusClasses Q.1).encard) ⟨Q, hQ⟩)

/-- $\Gamma_8 + \Gamma_{16}$ as a form in $24 = 8 \cdot 3$ variables. -/
def e8Gamma16 : QuadForm ℤ (8 * 3) := (by norm_num : 8 + 16 = 8 * 3) ▸ QuadForm.orthSum e8 gamma16

/-- **Niemeier's count as quoted by Cassels** (App. A, §3, footnote † on p. 365; named statement): *the genus of
$3\Gamma_8$ contains $22$ indecomposable isomorphism classes in addition to the decomposable $3\Gamma_8$ and
$\Gamma_8 + \Gamma_{16}$* [Niemeier (1973)]. Formally: the classes of the genus of $3\Gamma_8$ (`repE8 3`) that contain a
decomposable form (`¬ SplitCount Q 1`, i.e. $\mathbb Z^{24}$ is not indecomposable for $Q$) are exactly the classes of
$3\Gamma_8$ and $\Gamma_8 + \Gamma_{16}$, and $22$ classes contain an indecomposable form (being indecomposable is a class
invariant: `splitCount_of_isometricGL`). Cassels gives no proof; it is the classification of the even unimodular
lattices of rank $24$ (the $24$ Niemeier lattices; the Leech lattice is one of the $22$). -/
@[kb "cassels1978" "App. A, §3, footnote † on p. 365 (Niemeier: 22 indecomposable classes in the genus of 3Γ₈)"]
structure NiemeierThreeE8 : Prop where
  /-- The decomposable classes of the genus are those of $3\Gamma_8$ and $\Gamma_8 + \Gamma_{16}$. -/
  decomposable : {c ∈ genusClasses (repE8 3) | ∃ Q, classOf Q = c ∧ ¬ SplitCount Q 1} =
    {classOf (repE8 3), classOf e8Gamma16}
  /-- There are $22$ indecomposable classes in the genus. -/
  indecomposable : {c ∈ genusClasses (repE8 3) | ∃ Q, classOf Q = c ∧ SplitCount Q 1}.ncard = 22

/-! ### §3: the spinor-genus version of Theorem 3.1 -/

/-- $\mathbb Z^n$ as a lattice (`Lat ℚ n`) of $\mathbb Q^n$. -/
def intLat (n : ℕ) : Lat ℚ n := ⟨intVec, intVec_isLattice⟩

/-- **The number of classes in the spinor genus** of an integer-valued form $Q$ (Cassels, App. A, §3, p. 366): the
classes (`LatClass`, lattices up to isometry of $(\mathbb Q^n, Q)$) of the lattices in the spinor genus
`latSpinorGenus` of $\mathbb Z^n$ in $(\mathbb Q^n, Q)$, counted in $\mathbb N \cup \{\infty\}$. -/
def spinorGenusClassCount {n : ℕ} (Q : QuadForm ℤ n) : ℕ∞ :=
  (Quotient.mk (latSetoid (QQ Q)) '' latSpinorGenus (QQ Q) (intLat n)).encard

/-- **$c_{\mathrm{spn}}(n)$:** the minimum number of classes in a spinor genus of positive definite integer-valued forms
in $n$ variables (Cassels, App. A, §3, p. 366: Theorem 3.1 "with genus replaced by spinor genus"). -/
def minSpinorGenusClasses (n : ℕ) : ℕ∞ :=
  ⨅ Q : {Q : QuadForm ℤ n // IntQF.PosDef Q}, spinorGenusClassCount Q.1

/-- **Cassels, App. A, Theorem 3.1 for spinor genera** (p. 364 and p. 366; named statement): $c_{\mathrm{spn}}(n) \to \infty$
as $n \to \infty$. Cassels proves it by the argument for genera (`watson_of_inputs`) together with the two points
`WatsonSpinorConstruction` and `WatsonSpinorTypeLattice` of p. 366; the assembly also needs that the lattices (3.2) of a
genus containing $r\Gamma_8 + \Delta$ lie in one spinor genus. Not proved here. -/
@[kb "cassels1978" "App. A, §3, Thm. 3.1, p. 364, and p. 366 (the spinor-genus version)"]
structure WatsonSpinor : Prop where
  /-- $c_{\mathrm{spn}}(n) \to \infty$. -/
  tendsto : Filter.Tendsto minSpinorGenusClasses Filter.atTop (nhds ⊤)

/-- **Cassels, App. A, §3, p. 366, first point** (named statement): *if $(\Lambda_1, \phi_1)$ and $(\Lambda_1', \phi_1')$
are in the same spinor genus then $\Lambda'$ with $\Lambda' \supset \Lambda_1'$ can be chosen in the spinor genus of
$(\Lambda, \phi)$*: so the spinor genus of a Watson-derived form has at most as many classes as the spinor genus of the
form. Stated in the form used: for `Q` positive definite and `Q'` derived from `Q` at `p` (`IsWatsonDerived`),
`spinorGenusClassCount Q' ≤ spinorGenusClassCount Q`. Cassels' construction: $(\Lambda')_q = \alpha_q\Lambda_q$ for local
$\alpha_q \in \Theta(V_q)$ with $\alpha_q(\Lambda_1)_q = (\Lambda_1')_q$. -/
@[kb "cassels1978" "App. A, §3, p. 366 (spinor genera: first point)"]
structure WatsonSpinorConstruction : Prop where
  /-- Watson operations do not increase the number of classes in the spinor genus. -/
  monotone : ∀ (n : ℕ) (Q Q' : QuadForm ℤ n) (p : ℕ), IntQF.PosDef Q → IsWatsonDerived Q p Q' →
    spinorGenusClassCount Q' ≤ spinorGenusClassCount Q

/-- **Cassels, App. A, §3, p. 366, second point** (named statement): *a spinor genus contains a lattice of the type
(3.1) if the genus containing it does, at least when $\Delta$ has dimension $\ge 3$* (footnote: if $\dim\Delta \le 2$,
replace $r$ by $r - 1$); "this follows as in the proof of Theorem 7.1 of Chapter 11". Formally: if `Q` (positive
definite, $n$ variables) is in the genus of $r\Gamma_8 \perp \Delta$ ($\Delta$ positive definite in $m$ variables), then
the spinor genus of $\mathbb Z^n$ in $(\mathbb Q^n, Q)$ contains a lattice isometric to $r'\Gamma_8 \perp \Delta'$ for some
positive definite $\Delta'$, with $r' = r$ if $m \ge 3$ and $r' = r - 1$ if $m \le 2$ (the isometry of a lattice $M$ of
$(\mathbb Q^n, Q)$ with a form $Q''$ on $\mathbb Z^n$: some $g$ with $M = g\mathbb Z^n$ and $Q(gx) = Q''(x)$). -/
@[kb "cassels1978" "App. A, §3, p. 366 and footnote (spinor genera: second point)"]
structure WatsonSpinorTypeLattice : Prop where
  /-- The spinor genus of $\mathbb Z^n$ contains a lattice of type (3.1). -/
  exists_type : ∀ (n r m : ℕ) (Q : QuadForm ℤ n) (Δ : QuadForm ℤ m) (h : 8 * r + m = n), IntQF.PosDef Q →
    IntQF.PosDef Δ → SameGenus Q (h ▸ QuadForm.orthSum (repE8 r) Δ) →
    ∃ (r' m' : ℕ) (Δ' : QuadForm ℤ m') (h' : 8 * r' + m' = n), (r' = if 3 ≤ m then r else r - 1) ∧
      IntQF.PosDef Δ' ∧ ∃ M ∈ latSpinorGenus (QQ Q) (intLat n), ∃ g : Matrix (Fin n) (Fin n) ℚ,
        (M.1 : Set (Fin n → ℚ)) = g.mulVec '' (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ∧
        ∀ x : Fin n → ℤ, Q.evalIn ℚ (g.mulVec fun i => (x i : ℚ)) =
          ((h' ▸ QuadForm.orthSum (repE8 r') Δ' : QuadForm ℤ n).eval x : ℚ)

end QuadFormsKB.DefiniteForms
