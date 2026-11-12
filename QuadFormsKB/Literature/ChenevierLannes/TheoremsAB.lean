/-
# Chenevier–Lannes, Theorems A and B: Kneser neighbours in dimensions 16 and 24

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §1.2 (pp. 3–5), §3.3 (pp. 57–59), §3.4.1 (p. 62). Printed page
numbers.

**Layer.** Even unimodular lattices as integral forms (`EvenUnimodular.lean`), the neighbour numbers $N_p(x, y)$
(`Neighbors.lean`; `Siegel.Kneser.nbCount Q p y` is $N_p([Q], y)$). The book's $E_8 \oplus E_8$ is
`Lattices.twoE8` ($= E_8 \perp E_8$), its $E_{16} = D_{16}^+$ is Cassels' $\Gamma_{16}$, `Lattices.gamma16`; Ramanujan's
$\tau$ is `Lattices.ramanujanTau` (the $q$-expansion coefficients of $\Delta$, complex-valued).

**States** (named propositions; the book proves them with the theory of Chapters 5–10, not formalized here):
- `TheoremA` (p. 3): the matrix of $T_p$ on $\mathbb{Z}[X_{16}]$;
- `HeckeTwoSixteen`, `HeckeThreeSixteen` (§3.3.1–3.3.2, pp. 57–59): the explicit matrices of $T_2$ and $T_3$;
- `TheoremB_i`, `TheoremB_ii` (p. 4): Niemeier lattices as $p$-neighbours of the Leech lattice; completeness of
  $K_{24}(p)$ for $p \ge 47$;
- `NeighborWithoutRoots` (Proposition 3.4.1.1, p. 62): a $p$-neighbour without roots forces $p \ge h(L)$.

**Proves** (unconditional unless said):
- `repNum_leechType_prime` (§1.2, p. 4): for a Niemeier lattice $M$ without roots and $p$ prime,
  $r_M(p) = \tfrac{65520}{691}\,(1 + p^{11} - \tau(p))$;
- `theoremA_iff_offDiag` (odd $p$; conditional on Witt's `Cassels.WittTwoClassesSixteen`): the diagonal entries in
  Theorem A follow from the off-diagonal ones (Proposition 3.2.2);
- `nbCount_twoE8_gamma16_eq_leech` (footnote 2, p. 4; conditional on `TheoremA`): the "purely quadratic" relation
  $N_p(E_8 \oplus E_8, E_{16}) = \tfrac{9}{1456}\, r_{\mathrm{Leech}}(p)\,\tfrac{p^4 - 1}{p - 1}$.
-/
import QuadFormsKB.Literature.ChenevierLannes.Neighbors
import QuadFormsKB.Literature.ChenevierLannes.Classification
import QuadFormsKB.Literature.Cassels.AppBSec5
import QuadFormsKB.Literature.Cassels.AppB.Statements

open Matrix ModularForm EisensteinSeries
open scoped ArithmeticFunction.sigma

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser QuadFormsKB.Lattices

/-! ### Theorem A: the operator $T_p$ on $\mathbb{Z}[X_{16}]$ -/

/-- The scalar $\tfrac{1}{691}(1 + p + p^2 + p^3)(1 + p^{11} - \tau(p))$ of Theorem A. -/
noncomputable def thmAScalar (p : ℕ) : ℂ :=
  (1 + p + p ^ 2 + p ^ 3) * (1 + (p : ℂ) ^ 11 - ramanujanTau p) / 691

/-- **Theorem A** (Chenevier–Lannes, §1.2, p. 3; named statement, proved in the book in §5.4 and §9.4.1): for every
prime $p$, in the basis $(E_8 \oplus E_8, E_{16})$ of $\mathbb{Z}[X_{16}]$ the matrix of $T_p$ is
$$c_{16}(p)\begin{pmatrix}1&0\\0&1\end{pmatrix} + \frac{(1 + p + p^2 + p^3)(1 + p^{11} - \tau(p))}{691}
\begin{pmatrix}-405&286\\405&-286\end{pmatrix}.$$
Written with the entries $N_p(x, y)$ (the $(y, x)$ entry of the matrix): with $c$ = `thmAScalar p`,
$N_p(E_8^2, E_8^2) = c_{16}(p) - 405c$, $N_p(E_8^2, E_{16}) = 405c$, $N_p(E_{16}, E_8^2) = 286c$,
$N_p(E_{16}, E_{16}) = c_{16}(p) - 286c$. -/
@[kb "chenevierlannes2019" "Thm. A, p. 3"]
def TheoremA : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    (nbCount twoE8 p (classOf twoE8) : ℂ) = cn 16 p - 405 * thmAScalar p ∧
    (nbCount twoE8 p (classOf gamma16) : ℂ) = 405 * thmAScalar p ∧
    (nbCount gamma16 p (classOf twoE8) : ℂ) = 286 * thmAScalar p ∧
    (nbCount gamma16 p (classOf gamma16) : ℂ) = cn 16 p - 286 * thmAScalar p

/-- **The operator $T_2$ on $\mathbb{Z}[X_{16}]$** (Chenevier–Lannes, §3.3.1, p. 57; named statement): in the basis
$(E_{16}, E_8 \oplus E_8)$, $T_2 = \begin{pmatrix}20025&18225\\12870&14670\end{pmatrix}$, i.e.
$N_2(E_8^2, E_{16}) = 18225$, $N_2(E_8^2, E_8^2) = 14670$, $N_2(E_{16}, E_8^2) = 12870$, $N_2(E_{16}, E_{16}) = 20025$.
The book computes it from the orbits of $O(E_8 \oplus E_8)$ on the quadric and Kneser's theorem. (The case $p = 2$ of
`TheoremA`: there $c = 45$.) -/
@[kb "chenevierlannes2019" "§3.3.1, p. 57 (T_2 for n = 16)"]
def HeckeTwoSixteen : Prop :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  nbCount twoE8 2 (classOf gamma16) = 18225 ∧ nbCount twoE8 2 (classOf twoE8) = 14670 ∧
    nbCount gamma16 2 (classOf twoE8) = 12870 ∧ nbCount gamma16 2 (classOf gamma16) = 20025

/-- **The operator $T_3$ on $\mathbb{Z}[X_{16}]$** (Chenevier–Lannes, §3.3.2, pp. 58–59; named statement): in the basis
$(E_{16}, E_8 \oplus E_8)$, $T_3 = \begin{pmatrix}4248000&4147200\\2928640&3029440\end{pmatrix}$. (The case $p = 3$ of
`TheoremA`: there $c = 10240$.) -/
@[kb "chenevierlannes2019" "§3.3.2, pp. 58–59 (T_3 for n = 16)"]
def HeckeThreeSixteen : Prop :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  nbCount twoE8 3 (classOf gamma16) = 4147200 ∧ nbCount twoE8 3 (classOf twoE8) = 3029440 ∧
    nbCount gamma16 3 (classOf twoE8) = 2928640 ∧ nbCount gamma16 3 (classOf gamma16) = 4248000

/-- **The rows of $T_p$ on $X_{16}$ sum to $c_{16}(p)$** (Proposition 3.2.2 for $n = 16$, odd $p$): conditional on Witt's
classification `Cassels.WittTwoClassesSixteen` ($X_{16} = \{E_8 \oplus E_8, E_{16}\}$),
$N_p(E_8^2, E_8^2) + N_p(E_8^2, E_{16}) = c_{16}(p)$ and $N_p(E_{16}, E_8^2) + N_p(E_{16}, E_{16}) = c_{16}(p)$. -/
@[kb "chenevierlannes2019" "Prop. 3.2.2, p. 56 (n = 16, odd p)"]
theorem nbCount_sixteen_add (hW : Cassels.WittTwoClassesSixteen) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    nbCount twoE8 p (classOf twoE8) + nbCount twoE8 p (classOf gamma16) = cn 16 p ∧
      nbCount gamma16 p (classOf twoE8) + nbCount gamma16 p (classOf gamma16) = cn 16 p := by
  classical
  have hne : classOf twoE8 ≠ classOf gamma16 := fun he =>
    gamma16_not_isometric (IsometricGL.symm (classOf_eq_classOf_iff.mp he))
  have hT : ∀ {R : QuadForm ℤ 16}, IsEvenUnimodular R → ∀ c,
      c ∈ ({classOf twoE8, classOf gamma16} : Finset (QClass 16)) ↔ c ∈ genusClasses R := by
    intro R hR c
    rw [← classSet_eq_genusClasses hR, (wittRankSixteen_iff.mpr hW : WittRankSixteen)]
    simp
  have key : ∀ {R : QuadForm ℤ 16}, IsEvenUnimodular R →
      nbCount R p (classOf twoE8) + nbCount R p (classOf gamma16) = cn 16 p := by
    intro R hR
    have := sum_nbCount hp2 (not_dvd_det hR p) _ (hT hR)
    rwa [Finset.sum_pair hne, card_neighbors_eq_cn hR (by norm_num) hp2] at this
  exact ⟨key isEvenUnimodular_twoE8, key isEvenUnimodular_gamma16⟩

/-- **Theorem A reduces to its off-diagonal entries** (odd $p$; conditional on `Cassels.WittTwoClassesSixteen`): the
diagonal entries of the matrix in Theorem A are forced by Proposition 3.2.2 (`nbCount_sixteen_add`). -/
theorem theoremA_iff_offDiag (hW : Cassels.WittTwoClassesSixteen) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ((nbCount twoE8 p (classOf twoE8) : ℂ) = cn 16 p - 405 * thmAScalar p ∧
      (nbCount twoE8 p (classOf gamma16) : ℂ) = 405 * thmAScalar p ∧
      (nbCount gamma16 p (classOf twoE8) : ℂ) = 286 * thmAScalar p ∧
      (nbCount gamma16 p (classOf gamma16) : ℂ) = cn 16 p - 286 * thmAScalar p) ↔
    ((nbCount twoE8 p (classOf gamma16) : ℂ) = 405 * thmAScalar p ∧
      (nbCount gamma16 p (classOf twoE8) : ℂ) = 286 * thmAScalar p) := by
  obtain ⟨h1, h2⟩ := nbCount_sixteen_add hW hp2
  have e1 : (nbCount twoE8 p (classOf twoE8) : ℂ) + nbCount twoE8 p (classOf gamma16) = cn 16 p := by
    exact_mod_cast h1
  have e2 : (nbCount gamma16 p (classOf twoE8) : ℂ) + nbCount gamma16 p (classOf gamma16) = cn 16 p := by
    exact_mod_cast h2
  constructor
  · rintro ⟨-, a, b, -⟩; exact ⟨a, b⟩
  · rintro ⟨a, b⟩
    refine ⟨?_, a, b, ?_⟩
    · rw [← a]; linear_combination e1
    · rw [← b]; linear_combination e2

/-! ### The Leech lattice: $r_{\mathrm{Leech}}(p)$ -/

private theorem bernoulli'_six_aux : bernoulli' 6 = 1 / 42 := by
  have h3 : bernoulli' 3 = 0 := bernoulli'_eq_zero_of_odd ⟨1, rfl⟩ (by norm_num)
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd ⟨2, rfl⟩ (by norm_num)
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, h3, h5, bernoulli'_two, bernoulli'_four]
  norm_num

private theorem bernoulli'_eight_aux : bernoulli' 8 = -1 / 30 := by
  have h3 : bernoulli' 3 = 0 := bernoulli'_eq_zero_of_odd ⟨1, rfl⟩ (by norm_num)
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd ⟨2, rfl⟩ (by norm_num)
  have h7 : bernoulli' 7 = 0 := bernoulli'_eq_zero_of_odd ⟨3, rfl⟩ (by norm_num)
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, h3, h5, h7, bernoulli'_two, bernoulli'_four, bernoulli'_six_aux]
  norm_num

private theorem bernoulli'_ten_aux : bernoulli' 10 = 5 / 66 := by
  have h3 : bernoulli' 3 = 0 := bernoulli'_eq_zero_of_odd ⟨1, rfl⟩ (by norm_num)
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd ⟨2, rfl⟩ (by norm_num)
  have h7 : bernoulli' 7 = 0 := bernoulli'_eq_zero_of_odd ⟨3, rfl⟩ (by norm_num)
  have h9 : bernoulli' 9 = 0 := bernoulli'_eq_zero_of_odd ⟨4, rfl⟩ (by norm_num)
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, h3, h5, h7, h9, bernoulli'_two, bernoulli'_four, bernoulli'_six_aux,
    bernoulli'_eight_aux]
  norm_num

private theorem bernoulli_twelve_aux : bernoulli 12 = -691 / 2730 := by
  have h3 : bernoulli' 3 = 0 := bernoulli'_eq_zero_of_odd ⟨1, rfl⟩ (by norm_num)
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd ⟨2, rfl⟩ (by norm_num)
  have h7 : bernoulli' 7 = 0 := bernoulli'_eq_zero_of_odd ⟨3, rfl⟩ (by norm_num)
  have h9 : bernoulli' 9 = 0 := bernoulli'_eq_zero_of_odd ⟨4, rfl⟩ (by norm_num)
  have h11 : bernoulli' 11 = 0 := bernoulli'_eq_zero_of_odd ⟨5, rfl⟩ (by norm_num)
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, h3, h5, h7, h9, h11, bernoulli'_two, bernoulli'_four,
    bernoulli'_six_aux, bernoulli'_eight_aux, bernoulli'_ten_aux]
  norm_num

/-- **The representation numbers of the Leech lattice at primes** (Chenevier–Lannes, §1.2, p. 4): for a Niemeier lattice
$M$ without roots (the Leech lattice, `IsLeechType`) and $p$ prime,
$$r_M(p) = |\{x \in M : x \cdot x = 2p\}| = \frac{65520}{691}\bigl(1 + p^{11} - \tau(p)\bigr).$$
Unconditional: $\theta_M = E_{12} - \tfrac{65520}{691}\Delta$ (`Lattices.repNum_rank24` with $r_M(1) = 0$) and the
$q$-expansion of $E_{12}$ (`EisensteinSeries.E_qExpansion_coeff`, $-24/B_{12} = 65520/691$). -/
@[kb "chenevierlannes2019" "§1.2, p. 4 (r_Leech(p))"]
theorem repNum_leechType_prime {M : QuadForm ℤ 24} (hM : IsLeechType M) {p : ℕ} (hp : p.Prime) :
    (repNum M p : ℂ) = 65520 / 691 * (1 + (p : ℂ) ^ 11 - ramanujanTau p) := by
  obtain ⟨⟨hpos, hdet⟩, hroot⟩ := hM
  have h1 : repNum M 1 = 0 := by
    have : repSet M 1 = ∅ := hroot
    simp [repNum, this]
  have hr := repNum_rank24 hpos hdet (m := p) hp.one_lt.le
  rw [h1] at hr
  have hsig : ((σ 11 p : ℕ) : ℂ) = 1 + (p : ℂ) ^ 11 := by
    have := ArithmeticFunction.sigma_apply_prime_pow (k := 11) (i := 1) hp
    rw [pow_one] at this
    rw [this]
    simp [Finset.sum_range_succ]
  have hp0 : p ≠ 0 := hp.ne_zero
  have e1 : (UpperHalfPlane.qExpansion 1 (E (k := 12) (by norm_num))).coeff 1 = 65520 / 691 := by
    rw [E_qExpansion_coeff (k := 12) (by norm_num) ⟨6, rfl⟩ 1]
    simp [bernoulli_twelve_aux]
    norm_num
  have ep : (UpperHalfPlane.qExpansion 1 (E (k := 12) (by norm_num))).coeff p = 65520 / 691 * (1 + (p : ℂ) ^ 11) := by
    rw [E_qExpansion_coeff (k := 12) (by norm_num) ⟨6, rfl⟩ p]
    simp only [hp0, ↓reduceIte]
    have := hsig
    norm_num at this ⊢
    rw [this, bernoulli_twelve_aux]
    push_cast
    ring
  rw [hr, ep, e1]
  push_cast
  ring

/-- **The "purely quadratic" relation of footnote 2** (Chenevier–Lannes, §1.2, p. 4): **conditional** on `TheoremA`, for
every prime $p$ and every Niemeier lattice $M$ without roots,
$$N_p(E_8 \oplus E_8, E_{16}) = \frac{9}{1456}\, r_M(p)\, \frac{p^4 - 1}{p - 1}.$$
(The book: "which we do not know how to prove directly".) From `TheoremA` and `repNum_leechType_prime`. -/
@[kb "chenevierlannes2019" "§1.2, footnote 2, p. 4"]
theorem nbCount_twoE8_gamma16_eq_leech (hA : TheoremA) {M : QuadForm ℤ 24} (hM : IsLeechType M) {p : ℕ}
    [hp : Fact p.Prime] :
    (nbCount twoE8 p (classOf gamma16) : ℂ) = 9 / 1456 * repNum M p * (1 + p + p ^ 2 + p ^ 3) := by
  rw [(hA p).2.1, repNum_leechType_prime hM hp.out, thmAScalar]
  ring

/-! ### Theorem B and Proposition 3.4.1.1 -/

/-- **Theorem B (i)** (Chenevier–Lannes, §1.2, p. 4; named statement, proved in the book in §3.4 and §10.2–10.3): a
Niemeier lattice $L$ with roots is a $p$-neighbour of the Leech lattice iff $p \ge h(R(L))$. Here the Leech lattice is
any Niemeier lattice $M$ without roots (`IsLeechType`; unique by Conway's theorem), "$L$ is a $p$-neighbour of $M$" is
`NbrStep p L M` (some $p$-neighbour of $L$ in $\mathbb{Q} \otimes L$ is isomorphic to $M$), and $h(R(L))$ is
`coxeterNumber L` $= |R(L)|/24$. -/
@[kb "chenevierlannes2019" "Thm. B (i), p. 4"]
def TheoremB_i : Prop :=
  ∀ (L M : QuadForm ℤ 24), IsNiemeier L → (rootSet L).Nonempty → IsLeechType M →
    ∀ p : ℕ, p.Prime → (NbrStep p L M ↔ coxeterNumber L ≤ p)

/-- **Theorem B (ii)** (Chenevier–Lannes, §1.2, p. 4; named statement): the neighbour graph $K_{24}(p)$ is complete iff
$p \ge 47$: any two non-isomorphic Niemeier lattices are $p$-neighbours iff $p \ge 47$. -/
@[kb "chenevierlannes2019" "Thm. B (ii), p. 4"]
def TheoremB_ii : Prop :=
  ∀ p : ℕ, p.Prime →
    ((∀ L M : QuadForm ℤ 24, IsNiemeier L → IsNiemeier M → ¬ IntEquiv L M → NbrStep p L M) ↔ 47 ≤ p)

/-- **Proposition 3.4.1.1** (Chenevier–Lannes, p. 62; named statement, for prime $d = p$): if a Niemeier lattice $L$ with
roots has a $p$-neighbour without roots, then $p \ge h(L)$. (The "elementary part" of Theorem B, the analogue of Kostant's
theorem on regular elements; the book proves it for every integer $d \ge 2$ via the affine Weyl group, not formalized
here. Only prime $d$ is stated, since the library's neighbours are $p$-neighbours for a prime $p$.) -/
@[kb "chenevierlannes2019" "Prop. 3.4.1.1, p. 62 (prime d)"]
def NeighborWithoutRoots : Prop :=
  ∀ (L M : QuadForm ℤ 24), IsNiemeier L → (rootSet L).Nonempty → IsNiemeier M → rootSet M = ∅ →
    ∀ p : ℕ, p.Prime → NbrStep p L M → coxeterNumber L ≤ p

/-- **Proposition 3.4.1.1 is the "only if" half of Theorem B (i).** -/
theorem neighborWithoutRoots_of_theoremB_i (h : TheoremB_i) : NeighborWithoutRoots :=
  fun L M hL hR hM hM0 p hp hs => (h L M hL hR ⟨hM, hM0⟩ p hp).mp hs

end QuadFormsKB.ChenevierLannes
