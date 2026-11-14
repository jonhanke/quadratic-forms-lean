/-
# Kitaoka 1993, Section 6.6: representation of codimension at least 3 (Lemmas 6.6.2–6.6.4 and the exercise)

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (Cambridge Tracts in Mathematics 106, 1993), §6.6:
Lemma 6.6.2 (p. 165), Lemmas 6.6.3 and 6.6.4 (p. 166), and the exercise after the proof of Theorem 6.6.2 (p. 169).
Printed page numbers.

**Setting.** As in `Literature/Kitaoka/Ch6Representation.lean`: quadratic spaces $(\mathbb Q^n, Q)$ with
`Q : QuadForm ℚ n`, lattices `Lat ℚ n`, places `HeightOneSpectrum (𝓞 ℚ)`, localization `loc v`, representations
`LatRep` / `LocLatRep`. Local statements (Lemma 6.6.2) are over $\mathbb Z_p \subset \mathbb Q_p$ with the O'Meara layer
(`OMeara.IsRegular`, `OMeara.LatticeIsometryInto`). Kitaoka's bilinear form is $B(x, y) = \tfrac12(Q(x+y)-Q(x)-Q(y))$
(`kbil`).

**Reading of the OCR.** The machine-read text prints "$\ge$" as ">" (underline lost). The hypotheses "rank $L > m + 3$"
(Lemma 6.6.4) and "rank $L >$ rank $K + 3$" (exercise) are read as "$\ge$", i.e. $m + 3 \le \operatorname{rank} L$, in
accordance with the proof of Lemma 6.6.4 ("$\operatorname{rank} L - m \ge 3$", needed for Theorem 5.2.3) and with
Theorem 6.6.1 as formalized in `Ch6Representation.lean`. Likewise "$(B(v_i, v_j)) > c\,1_m$" is read as: the matrix
$(B(v_i, v_j)) - c\,1_m$ is positive definite. "Maximal lattice" is read as maximal for its own norm: $L_p$ is
maximal if it is $(\mathfrak n L_p)$-maximal (Kitaoka §5.2, p. 72), i.e. no lattice properly containing $L_p$ has norm
contained in $\mathfrak nL_p$.

**Defines**
* `scaledLat c L`: the lattice $cL = \{cx \mid x \in L\}$ (so $q^sL$ in Lemmas 6.6.3, 6.6.4);
* `orthSumLat K N`: the orthogonal sum $K \perp N$ of lattices, inside $\mathbb Q^{k + n}$ with the form `QuadForm.orthSum`;
* `IsMaximalLattice Q L`: $L$ is maximal for its own norm;
* `ScaleRepresents QU L q s`: the conclusion of Lemma 6.6.3 for the number $s$;
* `Lemma662`, `Lemma663`, `Lemma664`, `Exercise66`: the statements (all *stated*, not proved).

**Proves** nothing: every result of this file is stated only.
-/
import QuadFormsKB.Literature.Kitaoka.Ch6Representation
import QuadFormsKB.Literature.OMeara.Sec82Isom
import QuadFormsKB.Witt.Bridge
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.LinearAlgebra.Matrix.PosDef

open NumberField IsDedekindDomain QuadFormsKB.Lattices Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka

/-- **The lattice $q^sL$ in Lemmas 6.6.3 and 6.6.4** (Kitaoka 1993, §6.6, pp. 166–167): the submodule
$\{c x \mid x \in L\}$ of the same space, for a scalar $c \in \mathcal O_{\mathbb Q} = \mathbb Z$ (here $c = q^s$ for a
prime $q$ and a natural number $s$). It carries the restriction of the form of the space (so $Q(cx) = c^2 Q(x)$). -/
def scaledLat {n : ℕ} (c : 𝓞 ℚ) (L : Submodule (𝓞 ℚ) (Fin n → ℚ)) : Submodule (𝓞 ℚ) (Fin n → ℚ) :=
  L.map (c • LinearMap.id)

/-- **The orthogonal sum $K \perp N$ of lattices** (Kitaoka 1993, §6.6, Lemma 6.6.4, p. 166) in the space
$\mathbb Q^{k+n}$ with the form `QuadForm.orthSum QK QN`: the vectors $x$ whose first $k$ coordinates
$(x_0, \dots, x_{k-1})$ lie in $K$ and whose last $n$ coordinates $(x_k, \dots, x_{k+n-1})$ lie in $N$. -/
def orthSumLat {k n : ℕ} (K : Submodule (𝓞 ℚ) (Fin k → ℚ)) (N : Submodule (𝓞 ℚ) (Fin n → ℚ)) :
    Submodule (𝓞 ℚ) (Fin (k + n) → ℚ) :=
  K.comap (LinearMap.funLeft (𝓞 ℚ) ℚ (Fin.castAdd n)) ⊓ N.comap (LinearMap.funLeft (𝓞 ℚ) ℚ (Fin.natAdd k))

/-- **Maximal lattice** (Kitaoka 1993, §5.2, p. 72; used in §6.6, Lemma 6.6.3): over a local field with valuation ring
$R$, a lattice $L$ in $(V, Q)$ is maximal if it is $(\mathfrak nL)$-maximal (`OMeara.IsMaximal`): $\mathfrak nL \subseteq
\mathfrak nL$ and every lattice $K \supseteq L$ with $\mathfrak nK \subseteq \mathfrak nL$ equals $L$. -/
def IsMaximalLattice {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
    (Q : QuadraticForm F V) (L : Submodule R V) : Prop :=
  OMeara.IsMaximal Q (OMeara.normIdeal Q L) L

/-- **Kitaoka 1993, Lemma 6.6.2** (p. 165), *stated*. Let $N_p$ be a regular quadratic lattice over $\mathbb Z_p$ of rank
$n > m$. Then there are only finitely many regular submodules $M_p(j)$ of rank $m$ of $N_p$ such that every regular
submodule $M_p$ of rank $m$ of $N_p$ is represented by some $M_p(j)$.

*Encoding.* The lattice lives in $(\mathbb Q_p^k, Q)$ with a quadratic form `Q` (not assumed non-degenerate; $N_p$ need
not span the space). $N_p$ is a finitely generated $\mathbb Z_p$-submodule `N` that is regular (`OMeara.IsRegular`,
trivial radical) of rank $n$ = `finrank ℤ_[p] N` $> m$. The family is a finite set `T` of regular submodules of `N` of
rank $m$; "$M_p$ is represented by $M_p(j)$" is `OMeara.LatticeIsometryInto Q Q M M'` (an injective $\mathbb Z_p$-linear
map $M \to M'$ preserving $Q$). Kitaoka's proof reduces, via Jordan splittings, to finitely many invariants and uses
Dickson's lemma (his Lemma 6.6.1, `lemma661`). -/
@[kb "kitaoka1993" "§6.6, Lemma 6.6.2, p. 165"]
def Lemma662 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {k : ℕ},
    letI := invertibleTwo ℚ_[p]
    ∀ (Q : QuadraticForm ℚ_[p] (Fin k → ℚ_[p])) (N : Submodule ℤ_[p] (Fin k → ℚ_[p])), N.FG →
      OMeara.IsRegular Q N → ∀ m : ℕ, m < finrank ℤ_[p] N →
        ∃ T : Set (Submodule ℤ_[p] (Fin k → ℚ_[p])), T.Finite ∧
          (∀ M' ∈ T, M' ≤ N ∧ OMeara.IsRegular Q M' ∧ finrank ℤ_[p] M' = m) ∧
          ∀ M : Submodule ℤ_[p] (Fin k → ℚ_[p]), M ≤ N → OMeara.IsRegular Q M → finrank ℤ_[p] M = m →
            ∃ M' ∈ T, OMeara.LatticeIsometryInto Q Q M M'

/-- **The conclusion of Lemma 6.6.3 for a number $s$** (Kitaoka 1993, §6.6, p. 166): the lattice $L$ on $(\mathbb Q^n,
Q_U)$ represents every positive definite quadratic lattice $H$ (a lattice on a positive definite space
$(\mathbb Q^m, Q_H)$, any $m$) for which $H_p$ is represented by $(q^sL)_p$ for every prime $p$:
`LocLatRep v QH QU H (q^s L)` (which localizes at `v` itself) at every place `v`, giving `LatRep QH QU H L`. -/
def ScaleRepresents {n : ℕ} (QU : QuadForm ℚ n) (L : Lat ℚ n) (q s : ℕ) : Prop :=
  ∀ {m : ℕ} (QH : QuadForm ℚ m) (H : Lat ℚ m), IsTotallyPosDef QH →
    (∀ v : HeightOneSpectrum (𝓞 ℚ), LocLatRep v QH QU H.1 (scaledLat ((q : 𝓞 ℚ) ^ s) L.1)) →
    LatRep QH QU H.1 L.1

/-- **Kitaoka 1993, Lemma 6.6.3** (p. 166), *stated*. Let $U = (\mathbb Q^n, Q_U)$ be a positive definite quadratic space
over $\mathbb Q$ with $\dim U \ge 3$ such that $U_q$ is isotropic for a prime $q$, and let $L$ be a lattice on $U$ with
$L_p$ maximal for every prime $p$. Then there is a natural number $s$ such that $L$ represents every positive definite
quadratic lattice $H$ for which $H_p$ is represented by $q^sL_p$ for every prime $p$ (`ScaleRepresents QU L q s`).

*Encoding.* The prime is `q : ℕ` with `q.Prime`; $U_q$ is isotropic is `QuadForm.IsotropicIn` over the completion at the
place `v` with prime ideal $q\mathbb Z$. Maximality of $L_p$ is `IsMaximalLattice` over $\mathfrak o_p$ (see the module
docstring), $q^sL$ is `scaledLat`. Kitaoka's proof uses Theorems 6.3.2, 6.1.3 and Corollary 6.3.2 (strong approximation
for the spinor kernel). -/
@[kb "kitaoka1993" "§6.6, Lemma 6.6.3, p. 166"]
def Lemma663 : Prop :=
  ∀ {n : ℕ} (QU : QuadForm ℚ n), IsTotallyPosDef QU → 3 ≤ n →
    ∀ q : ℕ, q.Prime →
      (∃ v : HeightOneSpectrum (𝓞 ℚ), v.asIdeal = Ideal.span {((q : ℕ) : 𝓞 ℚ)} ∧
        QU.IsotropicIn (v.adicCompletion ℚ)) →
      ∀ L : Lat ℚ n,
        (∀ v : HeightOneSpectrum (𝓞 ℚ),
          letI := invertibleTwo (v.adicCompletion ℚ)
          IsMaximalLattice (QU.toQuadraticFormIn (v.adicCompletion ℚ)) (loc v L.1)) →
        ∃ s : ℕ, ScaleRepresents QU L q s

/-- **Kitaoka 1993, Lemma 6.6.4** (p. 166), *stated*. Let $L$, $q$, $s$ be as in Lemma 6.6.3 (a positive definite space
$U = (\mathbb Q^n, Q_U)$, $\dim U \ge 3$, $U_q$ isotropic, $L_p$ maximal for all $p$, and $s$ such that $L$ represents
every positive definite $H$ with $H_p$ represented by $(q^sL)_p$ for all $p$: `ScaleRepresents QU L q s`), $m$ an integer
with $\operatorname{rank} L \ge m + 3$ and $K$ a lattice on a positive definite quadratic space over $\mathbb Q$. Then
there is a positive constant $c$ such that $K \perp q^sL$ represents a lattice $M = \mathbb Z[v_0, \dots, v_{m-1}]$
provided that $M_p$ is represented by $(K \perp q^sL)_p$ for every prime $p$ and the Gram matrix
$(B(v_i, v_j))_{i,j}$ satisfies $(B(v_i, v_j)) > c\,1_m$ (read: $(B(v_i, v_j)) - c\,1_m$ is positive definite).

*Encoding.* $K$ is a lattice `K : Lat ℚ k` on $(\mathbb Q^k, Q_K)$ positive definite; $K \perp q^sL$ is `orthSumLat K
(scaledLat q^s L)` on $(\mathbb Q^{k+n}, $ `QuadForm.orthSum QK QU`$)$. The lattice $M$ lies on a positive definite space
$(\mathbb Q^m, Q_M)$ and is given by vectors `v : Fin m → (Fin m → ℚ)` (indices $0, \dots, m-1$) as
$M = \mathbb Z[v_0, \dots, v_{m-1}]$; $c$ is a rational number $> 0$ (it depends on $K$, $L$, $q$, $s$, $m$ only, as the
order of quantifiers shows), and the Gram matrix is `Matrix.of fun i j => kbil QM ℚ (v i) (v j)`. Positive definiteness
of the Gram matrix minus $c\,1_m$ forces the $v_i$ to be independent, so $M$ is a lattice of rank $m$. -/
@[kb "kitaoka1993" "§6.6, Lemma 6.6.4, p. 166"]
def Lemma664 : Prop :=
  ∀ {n : ℕ} (QU : QuadForm ℚ n), IsTotallyPosDef QU → 3 ≤ n →
    ∀ q : ℕ, q.Prime →
      (∃ v : HeightOneSpectrum (𝓞 ℚ), v.asIdeal = Ideal.span {((q : ℕ) : 𝓞 ℚ)} ∧
        QU.IsotropicIn (v.adicCompletion ℚ)) →
      ∀ L : Lat ℚ n,
        (∀ v : HeightOneSpectrum (𝓞 ℚ),
          letI := invertibleTwo (v.adicCompletion ℚ)
          IsMaximalLattice (QU.toQuadraticFormIn (v.adicCompletion ℚ)) (loc v L.1)) →
        ∀ s : ℕ, ScaleRepresents QU L q s →
        ∀ {m : ℕ}, m + 3 ≤ n →
        ∀ {k : ℕ} (QK : QuadForm ℚ k) (K : Lat ℚ k), IsTotallyPosDef QK →
          ∃ c : ℚ, 0 < c ∧
            ∀ (QM : QuadForm ℚ m), IsTotallyPosDef QM → ∀ v : Fin m → (Fin m → ℚ),
              (∀ w : HeightOneSpectrum (𝓞 ℚ),
                LocLatRep w QM (QuadForm.orthSum QK QU) (Submodule.span (𝓞 ℚ) (Set.range v))
                  (orthSumLat K.1 (scaledLat ((q : 𝓞 ℚ) ^ s) L.1))) →
              ((Matrix.of fun i j => kbil QM ℚ (v i) (v j)) - c • (1 : Matrix (Fin m) (Fin m) ℚ)).PosDef →
              LatRep QM (QuadForm.orthSum QK QU) (Submodule.span (𝓞 ℚ) (Set.range v))
                (orthSumLat K.1 (scaledLat ((q : 𝓞 ℚ) ^ s) L.1))

/-- **Kitaoka 1993, exercise after Theorem 6.6.2** (p. 169), *stated*. Let $K$, $L$ be regular quadratic lattices over
$\mathbb Z$ with $\operatorname{rank} L \ge \operatorname{rank} K + 3$. If $K$ is represented by $\mathrm{gen}(L)$, then
$K$ is represented by $\mathrm{spn}^+(L)$.

*Encoding.* $K$ is a lattice on the regular space $(\mathbb Q^m, Q_K)$ and $L$ a lattice on the regular space
$(\mathbb Q^n, Q_L)$ (a regular quadratic lattice is a lattice on a regular space; the ranks are $m$ and $n$), with
$m + 3 \le n$ (the OCR's "$>$" read as "$\ge$", see the module docstring). "Represented by $\mathrm{gen}(L)$" is
`RepByGenus` and "represented by $\mathrm{spn}^+(L)$" is `RepByProperSpinorGenus` (both from `Ch6Representation.lean`).
No definiteness is assumed. -/
@[kb "kitaoka1993" "§6.6, Exercise after Thm. 6.6.2, p. 169"]
def Exercise66 : Prop :=
  ∀ {m n : ℕ} (QK : QuadForm ℚ m) (QL : QuadForm ℚ n), QK.Nondegenerate → QL.Nondegenerate → m + 3 ≤ n →
    ∀ (K : Lat ℚ m) (L : Lat ℚ n),
      RepByGenus QK QL K.1 L → RepByProperSpinorGenus QK QL K.1 L

end QuadFormsKB.Kitaoka
