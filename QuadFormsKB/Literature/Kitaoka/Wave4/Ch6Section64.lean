/-
# Kitaoka 1993, Section 6.4: representation of codimension 1

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (Cambridge Tracts in Mathematics 106, 1993), §6.4,
pp. 151–156 (printed pages): the invariant $t_p(L)$ (p. 152), Lemma 6.4.1 (p. 152), Theorem 6.4.1 (p. 153),
Proposition 6.4.1 (p. 155), Corollary 6.4.1 (p. 156).

**Setting.** Local statements are over $\mathbb Z_p \subset \mathbb Q_p$ (or, in the global statements, over the
completions $\mathfrak o_v \subset \mathbb Q_v$, `loc v`), phrased with the repository's O'Meara layer
(`OMeara.IsJordanSplitting`, `OMeara.scale`, `OMeara.IsModular`, `OMeara.SameDisc`, ...), generic over a discrete
valuation ring $R$ with fraction field $F$; a lattice is a finitely generated $R$-submodule spanning the space
(`Submodule.IsLattice`). Global statements are over $\mathbb Q$ as in `Ch6Representation.lean`: quadratic spaces
$(\mathbb Q^n, Q)$ with `Q : QuadForm ℚ n`, lattices `Lat ℚ n`, primes as `HeightOneSpectrum (𝓞 ℚ)`, localization
`loc v`, representation `LatRep`, `LocLatRep`. Kitaoka's bilinear form is $B(x, y) = \tfrac12(Q(x+y)-Q(x)-Q(y))$.

**Reading of the OCR.** In the machine-read text the relation "$\ge$" is printed as ">" (the underline is lost):
Kitaoka's ordering on the sequences $t_p$ is "$a \le b$ iff $a_i = b_i$ for $i < k$ and $a_k < b_k$, or $a = b$", and the
"$t_p(L') > t_p(L)$" of Lemma 6.4.1 and Theorem 6.4.1 is read as $t_p(L') \ge t_p(L)$ (the proof of Lemma 6.4.1 uses
"$t_p(L') \ge t_p(L) = (0, \dots, 0)$ implies every coordinate of $t_p(L')$ is non-negative").

**Defines**
* `IsTypeSequence Q L e`: $e = t_p(L)$, the sequence of exponents of the scales of the Jordan components of $L$, each
  repeated rank-many times (6.4.d1, p. 152);
* `TypeSeqLE Q L Q' L'`: $t_p(L) \le t_p(L')$ in the lexicographic order (p. 152);
* `IsCharacteristicSubmodule Q L M`: $M$ is a characteristic submodule of $L$ (conditions (i), (ii) of Lemma 6.4.1);
* `AdmissibleSet Q L S`, `GlobalCharacteristicConditions Q L S M`: the standing hypotheses on $S$ and the three
  conditions (i)–(iii) on $M$ of Theorem 6.4.1;
* `Lemma641`, `Theorem641`, `Proposition641`, `Corollary641`: the statements of Lemma 6.4.1, Theorem 6.4.1,
  Proposition 6.4.1, Corollary 6.4.1 (all *stated*, not proved).

**Proves** nothing: every result of this section is stated only.
-/
import QuadFormsKB.Literature.Kitaoka.Ch6Representation
import QuadFormsKB.Literature.OMeara.Sec91Jordan
import QuadFormsKB.Literature.OMeara.Sec82Isom
import Mathlib.Order.PiLex
import Mathlib.NumberTheory.Padics.PadicIntegers

open NumberField IsDedekindDomain QuadFormsKB.Lattices Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka

section Generic

variable {R : Type*} [CommRing R] [IsDomain R] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']

/-- **The invariant $t_p(L)$** (Kitaoka 1993, §6.4, definition 6.4.d1, p. 152). Let $R$ be the valuation ring of a
local field $F$ (for $F = \mathbb Q_p$: $R = \mathbb Z_p$) and $L$ a regular lattice in the quadratic space $(V, Q)$.
For a Jordan splitting $L = L_0 \perp \cdots \perp L_{t-1}$ (`OMeara.IsJordanSplitting`: every $L_i$ modular, the scales
strictly decreasing) let $a_i \in \mathbb Z$ be defined by $\mathfrak s(L_i) = \varpi^{a_i} R$, where $\varpi$ is a
uniformizer of $R$ (for $\mathbb Z_p$: $\varpi = p$), so that $a_0 < \cdots < a_{t-1}$. Then
$$t_p(L) = (\underbrace{a_0, \dots, a_0}_{\operatorname{rank} L_0}, \dots,
  \underbrace{a_{t-1}, \dots, a_{t-1}}_{\operatorname{rank} L_{t-1}}).$$
Kitaoka notes that it is independent of the Jordan splitting (O'Meara 91:9); for a unimodular $L$ it is
$(0, \dots, 0)$.

*Encoding.* `IsTypeSequence Q L e` says $e = t_p(L)$ as a sequence `e : Fin n → ℤ` (indices $0, \dots, n-1$, with
$n$ = `finrank R L`): there are a uniformizer `ϖ`, a Jordan splitting `Ls : Fin t → Submodule R V` of `L`
(components $L_0, \dots, L_{t-1}$) and exponents `a i` with `OMeara.scale Q (Ls i) = ϖ ^ (a i) • R`, such that `e` is
non-decreasing and, for each integer $k$, the number of indices $j$ with $e_j = k$ equals the total rank of the
components with $a_i = k$. Since the $a_i$ are strictly increasing this determines `e` uniquely, and it is the sequence
above. -/
@[kb "kitaoka1993" "§6.4, 6.4.d1 (the invariant t_p(L)), p. 152"]
def IsTypeSequence (Q : QuadraticForm F V) (L : Submodule R V) {n : ℕ} (e : Fin n → ℤ) : Prop :=
  finrank R L = n ∧ Monotone e ∧
    ∃ (t : ℕ) (Ls : Fin t → Submodule R V) (a : Fin t → ℤ) (ϖ : R), Irreducible ϖ ∧
      OMeara.IsJordanSplitting Q L Ls ∧
      (∀ i, OMeara.scale Q (Ls i) = Submodule.span R {algebraMap R F ϖ ^ a i}) ∧
      ∀ k : ℤ, (Finset.univ.filter fun j => e j = k).card =
        ∑ i ∈ Finset.univ.filter (fun i => a i = k), finrank R (Ls i)

/-- **The order $t_p(L) \le t_p(L')$** (Kitaoka 1993, §6.4, p. 152). For two ordered sets
$a = (a_0, \dots, a_{n-1})$, $b = (b_0, \dots, b_{n-1})$ Kitaoka defines $a \le b$ iff either $a_i = b_i$ for $i < k$
and $a_k < b_k$ for some $k < n$, or $a_i = b_i$ for all $i$: the lexicographic order (`toLex e ≤ toLex e'`).
`TypeSeqLE Q L Q' L'` says that $t_p(L) \le t_p(L')$, where $L$ lies in $(V, Q)$ and $L'$ in $(V', Q')$: there are
sequences $e = t_p(L)$ and $e' = t_p(L')$ (`IsTypeSequence`, of the same length $n$) with $e \le e'$ lexicographically.
(Existence of the sequences is O'Meara 91:1 for regular lattices; uniqueness is O'Meara 91:9, so "there are $e$, $e'$"
is the same as "for the $e$, $e'$".) -/
@[kb "kitaoka1993" "§6.4, ordering of the invariants t_p, p. 152"]
def TypeSeqLE (Q : QuadraticForm F V) (L : Submodule R V) (Q' : QuadraticForm F V') (L' : Submodule R V') :
    Prop :=
  ∃ (n : ℕ) (e e' : Fin n → ℤ), IsTypeSequence Q L e ∧ IsTypeSequence Q' L' e' ∧ toLex e ≤ toLex e'

/-- **Characteristic submodule** (Kitaoka 1993, §6.4, Lemma 6.4.1, p. 152, and the sentence "We call a submodule $M$ in
the lemma a characteristic submodule of $L$", p. 153). A submodule $M$ of a lattice $L$ on a regular quadratic space
$(V, Q)$ over a local field is *characteristic* if
1. (i) $\operatorname{rank} M = \operatorname{rank} L - 1$ (written $\operatorname{rank} M + 1 = \operatorname{rank} L$),
   $dM \ne 0$ (some, equivalently every, basis of $M$ has Gram determinant $\beta \ne 0$) and $M$ is a direct summand of
   $L$ as a module (there is a submodule $N \subseteq L$ with $M \cap N = 0$ and $M + N = L$), and
2. (ii) every lattice $L'$ on $V$ with $M \subseteq L'$, $dL' = dL$ (`OMeara.SameDisc`, equality of discriminants up to
   squares of units) and $t_p(L') \ge t_p(L)$ (`TypeSeqLE Q L Q L'`) equals $L$. -/
@[kb "kitaoka1993" "§6.4, characteristic submodule (Lemma 6.4.1), pp. 152–153"]
def IsCharacteristicSubmodule (Q : QuadraticForm F V) (L M : Submodule R V) : Prop :=
  M ≤ L ∧ finrank R M + 1 = finrank R L ∧ (∃ β : F, β ≠ 0 ∧ OMeara.HasDisc Q M β) ∧
    (∃ N : Submodule R V, N ≤ L ∧ Disjoint M N ∧ M ⊔ N = L) ∧
    ∀ L' : Submodule R V, L'.IsLattice F → M ≤ L' → OMeara.SameDisc Q Q L' L → TypeSeqLE Q L Q L' → L' = L

end Generic

/-- **Kitaoka 1993, Lemma 6.4.1** (p. 152), *stated*. Let $U = (\mathbb Q_p^n, Q)$ be a regular quadratic space over
$\mathbb Q_p$ ($Q$ with non-degenerate bilinear form `associated Q`) and $L$ a lattice on it (a finitely generated
$\mathbb Z_p$-submodule spanning $U$). Then $L$ contains a submodule $M$ such that (i) $\operatorname{rank} M =
\operatorname{rank} L - 1$, $dM \ne 0$ and $M$ is a direct summand of $L$ as a module, and (ii) every lattice $L'$ on
$U$ containing $M$ with $dL' = dL$ and $t_p(L') \ge t_p(L)$ equals $L$. That is, $L$ has a characteristic submodule
(`IsCharacteristicSubmodule`; $t_p$ is `IsTypeSequence`, the order is `TypeSeqLE`).

*Encoding.* $n \ge 1$ is assumed (for $n = 0$ the rank $-1$ of $M$ is meaningless; Kitaoka's $\dim U \ge 1$ is
implicit). The prime is `p` with `Fact p.Prime`. $dL' = dL$ is equality up to squares of units of $\mathbb Z_p$, the
meaning of the discriminant of a $\mathbb Z_p$-lattice. Kitaoka's proof is by induction on $\dim U$, treating
unimodular lattices with and without an orthogonal basis (the latter for $p = 2$) and reducing the general case to
the modular components. -/
@[kb "kitaoka1993" "§6.4, Lemma 6.4.1, p. 152"]
def Lemma641 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n : ℕ}, 0 < n →
    letI := invertibleTwo ℚ_[p]
    ∀ Q : QuadraticForm ℚ_[p] (Fin n → ℚ_[p]), (QuadraticMap.associated Q).Nondegenerate →
      ∀ L : Submodule ℤ_[p] (Fin n → ℚ_[p]), L.IsLattice ℚ_[p] →
        ∃ M : Submodule ℤ_[p] (Fin n → ℚ_[p]), IsCharacteristicSubmodule Q L M

section Global

variable {n : ℕ}

/-- **The standing hypotheses on $S$ in Theorem 6.4.1** (Kitaoka 1993, §6.4, p. 153): $S$ is a finite set of primes
(here: of places `v : HeightOneSpectrum (𝓞 ℚ)`, the primes $p$ with prime ideal $p\mathbb Z$) with $2 \in S$ (the
place with prime ideal $2\mathbb Z$), and $L_p$ is unimodular (`OMeara.IsUnimodular`) for every prime $p \notin S$. -/
@[kb "kitaoka1993" "§6.4, Thm. 6.4.1 (hypotheses on S), p. 153"]
def AdmissibleSet (Q : QuadForm ℚ n) (L : Lat ℚ n) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Prop :=
  (∃ v ∈ S, v.asIdeal = Ideal.span {((2 : ℕ) : 𝓞 ℚ)}) ∧
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      letI := invertibleTwo (v.adicCompletion ℚ)
      OMeara.IsUnimodular (Q.toQuadraticFormIn (v.adicCompletion ℚ)) (loc v L.1)

/-- **The three conditions on $M$ in Theorem 6.4.1** (Kitaoka 1993, §6.4, p. 153; also the conclusion of Proposition
6.4.1, p. 155). For a lattice $L$ on $(\mathbb Q^n, Q)$ and a finite set $S$ of places, a $\mathbb Z$-submodule
$M \subseteq L$ satisfies
1. (i) $\operatorname{rank} M = n - 1$ (written $\operatorname{rank} M + 1 = n$);
2. (ii) $M_p$ is a characteristic submodule of $L_p$ (`IsCharacteristicSubmodule`, localizations `loc v`) for every
   $p \in S$;
3. (iii) $M_p$ is unimodular for every prime $p \notin S$, with precisely one exception $p = q$, where
   $\mathfrak s(M_q) \subseteq \mathbb Z_q$ and $dM_q \in q\mathbb Z_q$. Here $q \notin S$ is a prime (a place `q`),
   $q\mathbb Z_q$ is the maximal ideal of $\mathfrak o_q$, and "$dM_q \in q\mathbb Z_q$" means that $M_q$ has a basis
   with Gram determinant $\beta$ in that ideal.

The exception is "precisely one" automatically: a lattice of positive rank with $dM_q \in q\mathbb Z_q$ is not
unimodular. -/
@[kb "kitaoka1993" "§6.4, Thm. 6.4.1 (conditions (i)-(iii) on M), p. 153"]
def GlobalCharacteristicConditions (Q : QuadForm ℚ n) (L : Lat ℚ n) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (M : Submodule (𝓞 ℚ) (Fin n → ℚ)) : Prop :=
  M ≤ L.1 ∧ finrank (𝓞 ℚ) M + 1 = n ∧
    (∀ v ∈ S,
      letI := invertibleTwo (v.adicCompletion ℚ)
      IsCharacteristicSubmodule (Q.toQuadraticFormIn (v.adicCompletion ℚ)) (loc v L.1) (loc v M)) ∧
    ∃ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → v ≠ q →
        letI := invertibleTwo (v.adicCompletion ℚ)
        OMeara.IsUnimodular (Q.toQuadraticFormIn (v.adicCompletion ℚ)) (loc v M)) ∧
      letI := invertibleTwo (q.adicCompletion ℚ)
      OMeara.scale (Q.toQuadraticFormIn (q.adicCompletion ℚ)) (loc q M) ≤ 1 ∧
        ∃ β : q.adicCompletionIntegers ℚ, β ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers ℚ) ∧
          OMeara.HasDisc (Q.toQuadraticFormIn (q.adicCompletion ℚ)) (loc q M)
            (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ) β)

/-- **Kitaoka 1993, Theorem 6.4.1** (p. 153), *stated*. Let $U = (\mathbb Q^n, Q)$ be a regular quadratic space over
$\mathbb Q$, $L$ a lattice on it, $S$ a finite set of primes with $2 \in S$ and $L_p$ unimodular for $p \notin S$
(`AdmissibleSet`), and $M \subseteq L$ a submodule satisfying (i)–(iii) (`GlobalCharacteristicConditions`: rank $n - 1$;
$M_p$ characteristic in $L_p$ for $p \in S$; $M_p$ unimodular for $p \notin S$ except one prime $q$ with
$\mathfrak s(M_q) \subseteq \mathbb Z_q$, $dM_q \in q\mathbb Z_q$). Let $L'$ be a lattice on a quadratic space
$U' = (\mathbb Q^n, Q')$ of dimension $n$ with $dL' = dL$ and $t_p(L'_p) \ge t_p(L_p)$ for every prime $p$
(`TypeSeqLE`), and suppose $u : M \to L'$ is an isometry (an injective $\mathbb Z$-linear map with $Q'(ux) = Q(x)$).
Then $U' \cong U$ and, extending $u$ to an isometry $\hat u : U \to U'$, one has $L' = \hat u(L)$ or
$L' = \hat u(\tau_x L)$ where $x$ is an element with $U = \mathbb QM \perp \mathbb Qx$ and $\tau_x$ is the symmetry
(reflexion) in $x$; moreover $\hat u(L) \ne \hat u(\tau_x L)$.

*Encoding.* $n \ge 1$ is assumed. "$U' = U$" is the existence of a $\mathbb Q$-linear bijection
$\hat u : \mathbb Q^n \to \mathbb Q^n$ with $Q'(\hat u y) = Q(y)$ extending $u$ (`û x = u x` for $x \in M$). The element
$x$ is any vector with $Q(x) \ne 0$ and $B(x, M) = 0$ (then $\mathbb Qx$ is a regular line orthogonal to the regular
$(n-1)$-dimensional space $\mathbb QM$, so $U = \mathbb QM \perp \mathbb Qx$; $M$ is regular since $M_2$ is
characteristic, hence $dM_2 \ne 0$); the conclusion is asserted for every such $x$ (all such $x$ lie on one line, so
$\tau_x$ does not depend on the choice). $\tau_x$ is `OMeara.symmetry`. $dL' = dL$ is `OMeara.SameDisc` over
$\mathcal O_{\mathbb Q} = \mathbb Z$ (equality, since $\mathbb Z^\times = \{\pm1\}$ has trivial squares). -/
@[kb "kitaoka1993" "§6.4, Thm. 6.4.1, p. 153"]
def Theorem641 : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ (Q : QuadForm ℚ n), Q.Nondegenerate →
  ∀ (L : Lat ℚ n) (S : Finset (HeightOneSpectrum (𝓞 ℚ))), AdmissibleSet Q L S →
  ∀ M : Submodule (𝓞 ℚ) (Fin n → ℚ), GlobalCharacteristicConditions Q L S M →
  ∀ (Q' : QuadForm ℚ n) (L' : Lat ℚ n),
    letI := invertibleTwo ℚ
    OMeara.SameDisc (Q'.toQuadraticFormIn ℚ) (Q.toQuadraticFormIn ℚ) L'.1 L.1 →
    (∀ v : HeightOneSpectrum (𝓞 ℚ),
      letI := invertibleTwo (v.adicCompletion ℚ)
      TypeSeqLE (Q.toQuadraticFormIn (v.adicCompletion ℚ)) (loc v L.1)
        (Q'.toQuadraticFormIn (v.adicCompletion ℚ)) (loc v L'.1)) →
    ∀ u : M →ₗ[𝓞 ℚ] L'.1, Function.Injective u → (∀ x : M, Q'.evalIn ℚ (u x : Fin n → ℚ) = Q.evalIn ℚ (x : Fin n → ℚ)) →
      ∃ û : (Fin n → ℚ) ≃ₗ[ℚ] (Fin n → ℚ),
        (∀ y, Q'.evalIn ℚ (û y) = Q.evalIn ℚ y) ∧ (∀ x : M, û (x : Fin n → ℚ) = (u x : Fin n → ℚ)) ∧
        ∀ (x : Fin n → ℚ) (hx : Q.toQuadraticFormIn ℚ x ≠ 0),
          (∀ m ∈ M, OMeara.bil (Q.toQuadraticFormIn ℚ) m x = 0) →
          (L'.1 = L.1.map ((û : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ)).restrictScalars (𝓞 ℚ)) ∨
            L'.1 = (L.1.map (((OMeara.symmetry (Q.toQuadraticFormIn ℚ) x hx :
                (Fin n → ℚ) ≃ₗ[ℚ] (Fin n → ℚ)) : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ)).restrictScalars (𝓞 ℚ))).map
              ((û : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ)).restrictScalars (𝓞 ℚ))) ∧
          L.1.map ((û : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ)).restrictScalars (𝓞 ℚ)) ≠
            (L.1.map (((OMeara.symmetry (Q.toQuadraticFormIn ℚ) x hx :
                (Fin n → ℚ) ≃ₗ[ℚ] (Fin n → ℚ)) : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ)).restrictScalars (𝓞 ℚ))).map
              ((û : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ)).restrictScalars (𝓞 ℚ))

/-- **Kitaoka 1993, Proposition 6.4.1** (p. 155), *stated*. Let $U = (\mathbb Q^n, Q)$ be a regular quadratic space
over $\mathbb Q$, $L$ a lattice on it and $S$ a finite set of primes with $2 \in S$ and $L_p$ unimodular for
$p \notin S$ (`AdmissibleSet`; the data of Theorem 6.4.1). Then there is a submodule $M \subseteq L$ satisfying the
three conditions (i)–(iii) of Theorem 6.4.1 (`GlobalCharacteristicConditions`). Here $n \ge 1$ is assumed (as in
`Theorem641`). Kitaoka's proof treats the hyperbolic plane by hand and otherwise combines Lemma 6.4.1 at the primes
of $S$ with the approximation Theorem 6.2.1. -/
@[kb "kitaoka1993" "§6.4, Prop. 6.4.1, p. 155"]
def Proposition641 : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ (Q : QuadForm ℚ n), Q.Nondegenerate →
  ∀ (L : Lat ℚ n) (S : Finset (HeightOneSpectrum (𝓞 ℚ))), AdmissibleSet Q L S →
    ∃ M : Submodule (𝓞 ℚ) (Fin n → ℚ), GlobalCharacteristicConditions Q L S M

/-- **Kitaoka 1993, Corollary 6.4.1** (p. 156), *stated*. Let $L_1, \dots, L_m$ be lattices of rank $n$ on quadratic
spaces $V_i$ with $dL_i = d$ for all $i$, pairwise not isometric. Then there is a submodule $M$ of some $L_j$ with
$\operatorname{rank} M = n - 1$ such that $M$ is not represented by $L_i$ for every $i \ne j$.

*Encoding and deviations.* The lattices are `Ls i : Lat ℚ n` on the coordinate spaces $V_i = (\mathbb Q^n, Q_i)$,
`Qs i : QuadForm ℚ n` (indices $0, \dots, m-1$); "rank $L_i = n$" is that $L_i$ is a full lattice on an
$n$-dimensional space. $dL_i = d$ is `OMeara.HasDisc` with a common value $d \in \mathbb Q$ (an integer for integral
lattices; discriminants over $\mathbb Z$ are exact since $\mathbb Z^\times = \{\pm 1\}$). "Isometric" is
`IsometricLattices`; "$M$ is represented by $L_i$" is `LatRep (Qs j) (Qs i) M (Ls i)` ($M$ on the space $V_j$).
*Hypothesis made explicit:* the spaces $V_i$ are assumed regular (non-degenerate; the proofs of Theorem 6.4.1 and
Proposition 6.4.1 that the argument relies on are for regular $U$), and $m \ge 1$, $n \ge 1$ are assumed (otherwise
no $j$ resp. no submodule of rank $n - 1$ exists). -/
@[kb "kitaoka1993" "§6.4, Cor. 6.4.1, p. 156"]
def Corollary641 : Prop :=
  ∀ {m n : ℕ}, 0 < m → 0 < n → ∀ (Qs : Fin m → QuadForm ℚ n) (Ls : Fin m → Lat ℚ n),
    (∀ i, (Qs i).Nondegenerate) →
    letI := invertibleTwo ℚ
    (∃ d : ℚ, ∀ i, OMeara.HasDisc ((Qs i).toQuadraticFormIn ℚ) (Ls i).1 d) →
    (∀ i j, i ≠ j → ¬ IsometricLattices ((Qs i).toQuadraticFormIn ℚ) ((Qs j).toQuadraticFormIn ℚ) (Ls i).1 (Ls j).1) →
    ∃ (j : Fin m) (M : Submodule (𝓞 ℚ) (Fin n → ℚ)), M ≤ (Ls j).1 ∧ finrank (𝓞 ℚ) M + 1 = n ∧
      ∀ i, i ≠ j → ¬ LatRep (Qs j) (Qs i) M (Ls i).1

end Global

end QuadFormsKB.Kitaoka
