/-
# Chenevier–Lannes, §1.1 and §2.3: the classification of even unimodular lattices of dimension 8, 16 and 24

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §1.1 (pp. 1–2), §2.3 (pp. 34–44). Printed page numbers.

**Layer.** `EvenUnimodular.lean` (the class sets $X_n$ = `classSet n`, roots, Coxeter numbers $h = |R|/n$).

**States** (named propositions; the book's proofs use Venkov's theory of theta series with harmonic coefficients and a
case-by-case study of root systems, not formalized here):
- `MordellRankEight` (Corollary 2.3.5, p. 36): $X_8 = \{E_8\}$;
- `WittRankSixteen` (Corollary 2.3.6, p. 36): $X_{16} = \{E_8 \oplus E_8, E_{16}\}$;
- `ConwayLeechUnique` (Theorem 2.3.16, p. 43) and `LeechExists`: there is exactly one Niemeier lattice without roots;
- `NiemeierCoxeterNumbers` (Theorem 2.3.17, p. 43, with Table 1.1, p. 2): the Coxeter numbers of the $24$ elements of
  $X_{24}$, with multiplicity; in particular `niemeierCount_of_coxeterNumbers`: $|X_{24}| = 24$.

**Proves** (unconditional unless said):
- `wittRankSixteen_iff`: `WittRankSixteen` is equivalent to Cassels' named statement `Cassels.WittTwoClassesSixteen`
  (the same classification, quoted from Witt by Cassels), so the two inputs coincide;
- `classSet_sixteen_ncard` (conditional on `WittRankSixteen`): $|X_{16}| = 2$ (the two classes are distinct,
  `Lattices.gamma16_not_isometric`, proved);
- `isEvenUnimodular_e8`, `isEvenUnimodular_twoE8`, `isEvenUnimodular_gamma16`: the lattices $E_8$, $E_8 \oplus E_8$,
  $E_{16}$ are even unimodular.
-/
import QuadFormsKB.Literature.ChenevierLannes.EvenUnimodular
import QuadFormsKB.Literature.Cassels.AppBSec5
import QuadFormsKB.Literature.Cassels.AppB.Statements

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Lattices

variable {n : ℕ}

/-! ### The lattices $E_8$, $E_8 \oplus E_8$, $E_{16}$ -/

/-- $E_8$ (`Siegel.e8`, the form with Hessian the Cartan matrix of $E_8$) is even unimodular. -/
theorem isEvenUnimodular_e8 : IsEvenUnimodular e8 := ⟨e8_posDef, e8_det⟩

/-- $E_8 \oplus E_8$ (`Lattices.twoE8`) is even unimodular. -/
theorem isEvenUnimodular_twoE8 : IsEvenUnimodular twoE8 := ⟨twoE8_posDef, twoE8_det⟩

/-- $E_{16} = D_{16}^+$ (Cassels' $\Gamma_{16}$, `Lattices.gamma16`) is even unimodular. -/
theorem isEvenUnimodular_gamma16 : IsEvenUnimodular gamma16 := ⟨gamma16_posDef, gamma16_det⟩

/-! ### Dimension 8 and 16 -/

/-- **Corollary 2.3.5 (Mordell)** (Chenevier–Lannes, p. 36; named statement): every even unimodular lattice of
dimension $8$ is isomorphic to $E_8$, i.e. $X_8 = \{E_8\}$. The book's proof: the theta series is $E_4$, so
$|R(L)| = 240$, $h(L) = 30$, and $R(L)$ is of type $E_8$, which already has covolume $1$. -/
@[kb "chenevierlannes2019" "Cor. 2.3.5, p. 36"]
def MordellRankEight : Prop := classSet 8 = {classOf e8}

/-- **Corollary 2.3.6 (Witt)** (Chenevier–Lannes, p. 36; named statement): every even unimodular lattice of dimension
$16$ is isomorphic to $E_{16} = D_{16}^+$ or to $E_8 \oplus E_8$, i.e. $X_{16} = \{E_8 \oplus E_8, E_{16}\}$. (That the
two are not isomorphic is proved: `Lattices.gamma16_not_isometric`.) -/
@[kb "chenevierlannes2019" "Cor. 2.3.6, p. 36; §1.1, p. 2"]
def WittRankSixteen : Prop := classSet 16 = {classOf twoE8, classOf gamma16}

/-- **`WittRankSixteen` is Cassels' `WittTwoClassesSixteen`**: $X_{16}$ is the genus of $E_8 \oplus E_8$
(`classSet_eq_genusClasses`), so the two named statements say the same thing. Unconditional. -/
theorem wittRankSixteen_iff : WittRankSixteen ↔ Cassels.WittTwoClassesSixteen := by
  unfold WittRankSixteen
  rw [classSet_eq_genusClasses isEvenUnimodular_twoE8]
  exact ⟨fun h => ⟨h⟩, fun h => h.classes⟩

/-- **$|X_{16}| = 2$** (Chenevier–Lannes, §1.1, p. 2): **conditional** on `WittRankSixteen`; the two classes are
distinct by `Lattices.gamma16_not_isometric`. -/
@[kb "chenevierlannes2019" "§1.1, p. 2; Cor. 2.3.6, p. 36"]
theorem classSet_sixteen_ncard (h : WittRankSixteen) : (classSet 16).ncard = 2 := by
  rw [h, Set.ncard_pair]
  intro he
  exact gamma16_not_isometric (IsometricGL.symm (classOf_eq_classOf_iff.mp he))

/-! ### Dimension 24 -/

/-- **Theorem 2.3.16 (Conway)** (Chenevier–Lannes, p. 43; named statement): any two Niemeier lattices without roots are
isomorphic (each is isomorphic to the Leech lattice). -/
@[kb "chenevierlannes2019" "Thm. 2.3.16, p. 43"]
def ConwayLeechUnique : Prop :=
  ∀ M M' : QuadForm ℤ 24, IsLeechType M → IsLeechType M' → IntEquiv M M'

/-- **The Leech lattice exists** (Chenevier–Lannes, §1.1, p. 2, and §2.3; named statement): there is a Niemeier lattice
without roots. (The book constructs it, e.g. as $\mathrm{vois}_{47}(E_{24}; \rho)$, §1.2, p. 3, or from the Golay code.) -/
@[kb "chenevierlannes2019" "§1.1, p. 2 (the Leech lattice)"]
def LeechExists : Prop := ∃ M : QuadForm ℤ 24, IsLeechType M

/-- **The Coxeter number of a class** $h(x) = |R(x)|/n$ (well defined: `QClass.repNum`). -/
noncomputable def classCoxeterNumber (x : QClass n) : ℚ := (x.repNum 1 : ℚ) / n

/-- **The Coxeter numbers of the 24 Niemeier lattices** (Table 1.1, p. 2): $0$ (the Leech lattice) and the numbers $h(R)$
of the $23$ equi-Coxeter ADE root systems of rank $24$, with multiplicity. -/
def niemeierCoxeterTable : Multiset ℚ :=
  {0, 46, 30, 30, 25, 22, 18, 18, 16, 14, 13, 12, 12, 10, 10, 9, 8, 7, 6, 6, 5, 4, 3, 2}

/-- **Theorem 2.3.17 (Niemeier), numerical form** (Chenevier–Lannes, p. 43, with Table 1.1, p. 2; named statement): the
multiset of Coxeter numbers $h(x) = |R(x)|/24$ of the elements $x$ of $X_{24}$ is `niemeierCoxeterTable`.
*Weaker than the book:* the book's theorem is that $L \mapsto R(L)$ is a bijection from $X_{24}$ onto the set made of the
empty root system and the $23$ equi-Coxeter ADE root systems of rank $24$ (Table 1.1); root systems are not formalized
here, so only the number of elements of $X_{24}$ and the Coxeter numbers (equivalently the root counts $24h$) are
recorded. -/
@[kb "chenevierlannes2019" "Thm. 2.3.17, p. 43; Table 1.1, p. 2"]
def NiemeierCoxeterNumbers : Prop :=
  Multiset.map classCoxeterNumber (classSet_finite 24).toFinset.val = niemeierCoxeterTable

/-- **$|X_{24}| = 24$** (Chenevier–Lannes, §1.1, p. 2): **conditional** on `NiemeierCoxeterNumbers`. -/
@[kb "chenevierlannes2019" "§1.1, p. 2 (X_24 has 24 elements)"]
theorem niemeierCount_of_coxeterNumbers (h : NiemeierCoxeterNumbers) : (classSet 24).ncard = 24 := by
  have := congrArg Multiset.card h
  rw [Multiset.card_map] at this
  rw [Set.ncard_eq_toFinset_card _ (classSet_finite 24)]
  exact this

end QuadFormsKB.ChenevierLannes
