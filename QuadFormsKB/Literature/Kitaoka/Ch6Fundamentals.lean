/-
# Kitaoka 1993, Section 6.1: representations of lattices, proper classes, Theorems 6.1.2 and 6.1.3

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms*, Cambridge Tracts in Mathematics 106 (1993), §1.2, p. 5
(isometries into, representations), §6.1, pp. 129–134. Page numbers are the printed pages of the book.

**Setting.** As everywhere in the lattice layer (`Lattices/Genus.lean`), a quadratic space of dimension $n$ over a
number field $F$ is $(F^n, Q)$ with `Q : QuadForm F n`, and a lattice is an $\mathcal O_F$-submodule
`L : Submodule (𝓞 F) (Fin n → F)` (a full lattice when it is a `Lat F n`). Kitaoka works over $F = \mathbb Q$; the
definitions below are made over every number field and specialize to his at $F = \mathbb Q$, where
$\mathcal O_{\mathbb Q} = \mathbb Z$ and the finite places are the primes $p$.

**Defines** (Kitaoka's notation $\sigma : M \rightarrowtail N$, "an isometry from $M$ to $N$", §1.2, p. 5: an injective
linear map with $Q(\sigma x) = Q(x)$; then $M$ *is represented by* $N$):
* `LatRep QU QV L M`: the lattice $L$ on $(F^m, Q_U)$ is represented by the lattice $M$ on $(F^n, Q_V)$, $L \rightarrowtail M$;
* `LocLatRep v QU QV L M`: $L_\mathfrak p \rightarrowtail M_\mathfrak p$ over the completion $F_\mathfrak p$ at the
  finite place $\mathfrak p$ = `v`;
* `SpaceRepAt w QU QV`: $U_w \rightarrowtail V_w$ over the completion $F_w$ at the infinite place `w` (for
  $F = \mathbb Q$ this is Kitaoka's $U_\infty \rightarrowtail V_\infty$ over $\mathbb R$);
* `Theorem613`: the statement of Theorem 6.1.3 (stated, over $\mathbb Q$, as in the book; proved for regular spaces in
  `Ch6Theorem613.lean`).

**Proves**
* `properGenusClasses_finite` (Theorem 6.1.2): the genus of a lattice on a regular space contains only finitely many
  proper classes, over every number field. *Proof:* the genus has finitely many classes
  (`Lattices.ClassFin.genusClasses_finite_nf`, O'Meara 103:4) and each class contains at most two proper classes
  (`Lattices.properGenusClasses_subset`, O'Meara 102:2).

**Existing objects used for Kitaoka's notions** (no redefinition):
* the proper class $\mathrm{cls}^+(L)$ (6.1.d6, p. 131) is `Lattices.IsProperIsometric`, the class $\mathrm{cls}(L)$ is
  `Lattices.IsIsometric`, the genus $\mathrm{gen}(L)$ is `Lattices.SameGenus`, the spinor genus $\mathrm{spn}(L)$ is
  `Lattices.SameSpinorGenus` and the proper spinor genus $\mathrm{spn}^+(L)$ is `Lattices.SameProperSpinorGenus`;
* Kitaoka's genus uses the adelic group $O_{\mathbb A}(V)$ including the real place; the repository's `SameGenus` asks
  for local isometries at the finite places only, which is the same condition since both lattices lie on the same
  space $V$ (so they agree at the infinite places).
-/
import QuadFormsKB.Literature.OMeara.Sec102
import QuadFormsKB.Literature.OMeara.Sec82Classes
import QuadFormsKB.Literature.OMeara.Sec6Defs
import QuadFormsKB.Lattices.ClassFinite

open NumberField IsDedekindDomain QuadFormsKB.Lattices

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka

/-- $2$ is invertible in a field of characteristic zero. O'Meara's lattice predicates (`OMeara.LatticeIsometryInto`)
carry an `[Invertible (2 : F)]` argument; this supplies it for number fields and their completions. -/
abbrev invertibleTwo (K : Type*) [Field K] [CharZero K] : Invertible (2 : K) := invertibleOfNonzero two_ne_zero

section Rep

variable {F : Type} [Field F] [NumberField F] {m n : ℕ}

/-- **Representation of lattices** $L \rightarrowtail M$ (Kitaoka 1993, §1.2, p. 5: "an isometry from $L$ to $M$"):
the lattice $L$ on the quadratic space $(F^m, Q_U)$ is represented by the lattice $M$ on $(F^n, Q_V)$, i.e. there is
an injective $\mathcal O_F$-linear map $\sigma : L \to M$ with $Q_V(\sigma x) = Q_U(x)$ for all $x \in L$. This is
O'Meara's isometry into (`OMeara.LatticeIsometryInto`, O'Meara 1963, §82A, p. 220) for the forms $Q_U$ on $F^m$ and
$Q_V$ on $F^n$. Neither $L$ nor $M$ is required to be a full lattice. -/
@[kb "kitaoka1993" "§1.2, p. 5 (isometry σ : M ↪ N, M is represented by N)"]
def LatRep (QU : QuadForm F m) (QV : QuadForm F n) (L : Submodule (𝓞 F) (Fin m → F))
    (M : Submodule (𝓞 F) (Fin n → F)) : Prop :=
  letI := invertibleTwo F
  OMeara.LatticeIsometryInto (QU.toQuadraticFormIn F) (QV.toQuadraticFormIn F) L M

/-- **Local representation of lattices** $L_\mathfrak p \rightarrowtail M_\mathfrak p$ (Kitaoka 1993, §1.2, p. 5, over
$R = \mathfrak o_\mathfrak p$; used in Theorem 6.1.3, p. 134): at the finite place $\mathfrak p$ = `v` of $F$, there is
an injective $\mathfrak o_\mathfrak p$-linear map $\sigma_\mathfrak p : L_\mathfrak p \to M_\mathfrak p$ with
$Q_V(\sigma_\mathfrak p x) = Q_U(x)$, where $L_\mathfrak p$ = `loc v L` $\subseteq F_\mathfrak p^m$ and
$M_\mathfrak p$ = `loc v M` $\subseteq F_\mathfrak p^n$ are the localizations (closures) and the forms are extended to
$F_\mathfrak p$. For $F = \mathbb Q$ and $\mathfrak p = (p)$ this is $L_p \rightarrowtail M_p$ over $\mathbb Z_p$. -/
@[kb "kitaoka1993" "§1.2, p. 5 (isometry into); §6.1, Thm. 6.1.3, p. 134 (L_p ↪ M_p)"]
def LocLatRep (v : HeightOneSpectrum (𝓞 F)) (QU : QuadForm F m) (QV : QuadForm F n)
    (L : Submodule (𝓞 F) (Fin m → F)) (M : Submodule (𝓞 F) (Fin n → F)) : Prop :=
  letI := invertibleTwo (v.adicCompletion F)
  OMeara.LatticeIsometryInto (R := v.adicCompletionIntegers F) (QU.toQuadraticFormIn (v.adicCompletion F))
    (QV.toQuadraticFormIn (v.adicCompletion F)) (loc v L) (loc v M)

/-- **Representation of spaces at an infinite place** $U_w \rightarrowtail V_w$ (Kitaoka 1993, §1.2, p. 5; for
$F = \mathbb Q$ and the real place this is $U_\infty \rightarrowtail V_\infty$, Theorem 6.1.3, p. 134): over the
completion $F_w$ ($\cong \mathbb R$ or $\mathbb C$) there is an injective linear map $\sigma : F_w^m \to F_w^n$ with
$Q_V(\sigma x) = Q_U(x)$ (`OMeara.IsRepresentedBy`). -/
@[kb "kitaoka1993" "§1.2, p. 5 (isometry into); §6.1, Thm. 6.1.3, p. 134 (U_∞ ↪ V_∞)"]
def SpaceRepAt (w : InfinitePlace F) (QU : QuadForm F m) (QV : QuadForm F n) : Prop :=
  OMeara.IsRepresentedBy (QU.toQuadraticFormIn w.Completion) (QV.toQuadraticFormIn w.Completion)

end Rep

/-! ### Theorem 6.1.2: finitely many proper classes in a genus -/

section Finite

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- **Kitaoka 1993, Theorem 6.1.2** (p. 133): for a lattice $L$ on a regular quadratic space $V = (F^n, Q)$, the
number of different proper classes $\mathrm{cls}^+(M)$ ($M$ up to isometries of determinant $1$,
`Lattices.IsProperIsometric`) in the genus $\mathrm{gen}(L)$ is finite. Kitaoka states it for $F = \mathbb Q$; this is
the statement over every number field $F$.

*Proof.* The genus contains finitely many classes (`Lattices.ClassFin.genusClasses_finite_nf`, O'Meara 103:4, proved in
the repository by reduction theory), and each class contains at most two proper classes, those of $M$ and of
$\tau M$ for a fixed improper isometry $\tau$ (`Lattices.properGenusClasses_subset`, O'Meara 102:2). Kitaoka's own
proof is the same: finiteness of $\mathrm{GL}_n(\mathbb Z)$-classes (his Corollary 2.1.1) and
$[\mathrm{GL}_n(\mathbb Z) : \mathrm{SL}_n(\mathbb Z)] = 2$. -/
@[kb "kitaoka1993" "§6.1, Thm. 6.1.2, p. 133"]
theorem properGenusClasses_finite (hQ : Q.Nondegenerate) (L : Lat F n) :
    (properGenusClasses Q L).Finite := by
  have hG := ClassFin.genusClasses_finite_nf Q hQ L
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact (hG.image _).subset (properGenusClasses_subset_zero Q hn L)
  · obtain ⟨τ, hτ⟩ := Tamagawa.exists_orthGroup_det_neg_one Q hQ hn
    exact ((hG.image _).union (hG.image _)).subset (properGenusClasses_subset Q hQ L τ hτ)

end Finite

/-! ### Theorem 6.1.3: local representations give a representation by a lattice of the genus -/

/-- **Kitaoka 1993, Theorem 6.1.3** (p. 134), *stated*: let $U = (\mathbb Q^m, Q_U)$ and $V = (\mathbb Q^n, Q_V)$ be
quadratic spaces over $\mathbb Q$ and $L$, $M$ lattices on $U$, $V$. If there is an isometry
$\sigma_v : L_v \rightarrowtail M_v$ for every place $v$ (at $v = \infty$, $L_\infty$ and $M_\infty$ mean
$U_\infty$ and $V_\infty$), then $L \rightarrowtail N$ for some lattice $N$ in the genus of $M$.

The hypotheses: `LocLatRep v QU QV L M` at every prime `v`, `SpaceRepAt w QU QV` at the infinite place `w` (there is
one for $\mathbb Q$). The conclusion: a full lattice `N` on $V$ with `SameGenus QV M N` and `LatRep QU QV L N`.
As in the book, the spaces are not assumed regular. Kitaoka's proof uses the Hasse principle for representations of
spaces (his Corollary 4.1.2) and the gluing of local lattices (Theorem 6.1.1).

*Update (hypothesis):* Corollary 4.1.2 and Witt's theorem, both used in the proof, need $U$ and $V$ regular; the theorem
is proved for regular $U$, $V$ over every number field as `theorem613_of_nondegenerate` (`Ch6Theorem613.lean`). -/
@[kb "kitaoka1993" "§6.1, Thm. 6.1.3, p. 134"]
def Theorem613 : Prop :=
  ∀ {m n : ℕ} (QU : QuadForm ℚ m) (QV : QuadForm ℚ n) (L : Lat ℚ m) (M : Lat ℚ n),
    (∀ v : HeightOneSpectrum (𝓞 ℚ), LocLatRep v QU QV L.1 M.1) →
    (∀ w : InfinitePlace ℚ, SpaceRepAt w QU QV) →
    ∃ N : Lat ℚ n, SameGenus QV M.1 N.1 ∧ LatRep QU QV L.1 N.1

end QuadFormsKB.Kitaoka
