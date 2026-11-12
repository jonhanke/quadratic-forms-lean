/-
# Chenevier–Lannes, Chapter 3: Kneser neighbours and the Hecke operators $T_p$ on $\mathbb{Z}[X_n]$

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §1.2 (pp. 3–5), §3.1 (pp. 45–54), §3.2 (pp. 55–57). Printed page numbers.

**Layer.** Even unimodular lattices as integral forms (`EvenUnimodular.lean`). The book's $p$-neighbours of $L$ in
$\mathbb{Q} \otimes L$ (§1.2, p. 3; Scholium-Definition 3.1.2, p. 46) are `Siegel.Kneser.neighbors Q p`, the lattices
$L' \subset \mathbb{Q}^n$ with $[L : L \cap L'] = [L' : L \cap L'] = p$ on which $Q$ is integral (`IsNeighbor`); for an
even unimodular $L$ these are exactly the self-dual integral lattices with $L/(L \cap L') \cong \mathbb{Z}/p$ (the
book's definition), because an integral lattice of the same covolume as $L$ is unimodular. Two forms are
**$p$-neighbours as classes** (the book's abstract $p$-neighbours, §3.1, p. 48) when `NbrStep p Q Q'`.
The book's integers $N_p(x, y)$ (§3.1, p. 49) are `nbNum p x y`.

**Proves**, for an odd prime $p$ (unconditional):
- `card_neighbors_eq_cn` (§1.2, p. 3; Prop.-Def. 3.2.1, pp. 55–56): an even unimodular $L$ of dimension $n > 0$ has exactly
  $c_n(p) = \sum_{m=0}^{n-2} p^m + p^{n/2-1}$ $p$-neighbours;
- `sum_nbNum` (Prop. 3.2.2, p. 56): $\sum_{y \in X_n} N_p(x, y) = c_n(p)$;
- `nbNum_mul_autCard` (Scholium 3.1.7, p. 49, and Prop. 3.2.3, p. 56): $N_p(x, y)\,|O(y)| = N_p(y, x)\,|O(x)|$;
- `sum_nbNum_div_autCard` (Prop. 3.2.4, p. 56): $\sum_{x} N_p(x, y)/|O(x)| = c_n(p)/|O(y)|$, i.e. $\sum_x x/|O(x)|$ is an
  eigenvector of $T_p$ with eigenvalue $c_n(p)$;
- `kneser_connected_of_input` (Theorem 3.1.12, p. 52, for odd $p$ and $n \ge 3$): conditional on the named input
  `EvenUnimodularOneSpinorGenus`.

**States** (named propositions, not proved): `NeighborCountTwo` (the case $p = 2$ of Prop.-Def. 3.2.1),
`KneserConnectivity` (Theorem 3.1.12 for every prime).
-/
import QuadFormsKB.Literature.ChenevierLannes.EvenUnimodular
import QuadFormsKB.Siegel.KneserConnectedProof

open Matrix

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser

variable {n : ℕ}

/-! ### The number of $p$-neighbours -/

/-- For $8 \mid n$ and $\det H = 1$ the discriminant sign $\left(\frac{(-1)^{n/2}\det H}{p}\right)$ is $1$
(the quadric $C_L$ is hyperbolic, Scholium 2.2.5 (a), p. 31). -/
theorem discSign_eq_one {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) (p : ℕ) [Fact p.Prime] :
    discSign Q p = 1 := by
  unfold discSign
  obtain ⟨k, hk⟩ := eight_dvd_of_isEvenUnimodular hQ
  rw [hQ.det_one, hk, show 8 * k / 2 = 2 * (2 * k) by omega, pow_mul]
  simp [legendreSym.at_one]

/-- $p \nmid \det H = 1$. -/
theorem not_dvd_det {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) (p : ℕ) [Fact p.Prime] :
    ¬ (p : ℤ) ∣ Q.hessian.det := by
  rw [hQ.det_one]
  exact fun h => (Fact.out : p.Prime).one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by omega) h)

/-- **The number of $p$-neighbours of an even unimodular lattice** (Chenevier–Lannes, §1.2, p. 3, and
Proposition-Definition 3.2.1, pp. 55–56): for $L$ even unimodular of dimension $n > 0$ and $p$ an odd prime, $L$ has exactly
$$c_n(p) = 1 + p + \cdots + p^{n-2} + p^{n/2-1}$$
$p$-neighbours. *Proof:* the $p$-neighbours correspond to the isotropic lines of $L/pL$ (Arizona Winter School Thm. 1.10.4,
`Siegel.Kneser.card_neighbors`), and there are $p^{n-1} + (p-1)p^{n/2-1}$ isotropic vectors (`card_qv_zero`, with
discriminant sign $1$). Unconditional. The case $p = 2$ is `NeighborCountTwo` (stated). -/
@[kb "chenevierlannes2019" "§1.2, p. 3; Prop.-Def. 3.2.1, pp. 55–56 (odd p)"]
theorem card_neighbors_eq_cn {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) (hn : 0 < n) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) : (neighbors Q p).card = cn n p := by
  have hp := (Fact.out : p.Prime)
  have hdet := not_dvd_det hQ p
  have heven : Even n := by
    obtain ⟨k, hk⟩ := eight_dvd_of_isEvenUnimodular hQ
    exact ⟨4 * k, by omega⟩
  have h1 := card_neighbors (Q := Q) (p := p) hdet
  have h2 := card_isoSet (Q := Q) (p := p)
  have h3 := card_qv_zero (Q := Q) (p := p) hp2 hdet heven (by omega)
  rw [discSign_eq_one hQ] at h3
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hgeom : (∑ m ∈ Finset.range (n - 1), (p : ℤ) ^ m) * ((p : ℤ) - 1) = (p : ℤ) ^ (n - 1) - 1 :=
    geom_sum_mul _ _
  have e1 : (((p - 1) * (neighbors Q p).card : ℕ) : ℤ) = ((isoSet Q p).card : ℤ) := by rw [h1]
  push_cast [Nat.cast_sub hp1] at e1
  have e2 : (((isoSet Q p).card + 1 : ℕ) : ℤ) = _ := congrArg (fun k : ℕ => (k : ℤ)) h2
  push_cast at e2
  have hp0 : ((p : ℤ) - 1) ≠ 0 := by have := hp.one_lt; omega
  have key : ((p : ℤ) - 1) * (neighbors Q p).card = ((p : ℤ) - 1) * (cn n p : ℤ) := by
    simp only [cn]
    push_cast
    linear_combination e1 + e2 + h3 - hgeom
  exact_mod_cast mul_left_cancel₀ hp0 key

/-- **Proposition-Definition 3.2.1 at $p = 2$** (Chenevier–Lannes, p. 56; named statement, not proved here): an even
unimodular lattice of dimension $n > 0$ has exactly $c_n(2) = 2^{n-1} - 1 + 2^{n/2-1}$ $2$-neighbours. The book's
proof: $\mathbb{F}_2 \otimes L$ is a hyperbolic quadratic space (Scholium 2.2.5 (a)), whose isotropic lines are counted
by the standard formula. Not proved here because the count of isotropic vectors of a quadratic form over
$\mathbb{F}_2$ (Arf invariant $0$) is not yet in the library. -/
@[kb "chenevierlannes2019" "Prop.-Def. 3.2.1, pp. 55–56 (p = 2)"]
def NeighborCountTwo : Prop :=
  ∀ (n : ℕ) (Q : QuadForm ℤ n), IsEvenUnimodular Q → 0 < n →
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩; (neighbors Q 2).card = cn n 2

/-! ### The integers $N_p(x, y)$ and the Hecke operator $T_p$ -/

/-- **The integers $N_p(x, y)$** (Chenevier–Lannes, §3.1, p. 49; §3.2, p. 55): for classes $x, y$, the
number of $p$-neighbours of a lattice $L$ of class $x$ (in $\mathbb{Q} \otimes L$) that are isomorphic to $y$. The
representative $L$ is the chosen one, `Quotient.out x`; `nbCount` (`Siegel/EichlerGenus.lean`) counts the neighbours of
$\mathbb{Z}^n$ with the form of that representative, by class. The Hecke operator of §3.2 is
$$T_p\,x = \sum_{y \in X_n} N_p(x, y)\,y$$
on $\mathbb{Z}[X_n]$, i.e. the $X_n \times X_n$ matrix with $(y, x)$ entry $N_p(x, y)$; `nbNum` is that matrix. -/
@[kb "chenevierlannes2019" "§3.1, p. 49; §3.2, p. 55 (N_p(x, y), matrix of T_p)"]
noncomputable def nbNum (p : ℕ) [Fact p.Prime] (x y : QClass n) : ℕ :=
  nbCount (Quotient.out (s := intSetoid n) x) p y

/-- **The Hecke operator $T_p$ on functions** (Chenevier–Lannes, §1.3, p. 7, and §3.2, p. 55): for $f : X_n \to R$,
$(T_pf)(x) = \sum_y N_p(x, y)\,f(y)$, the sum of $f$ over the $p$-neighbours of a lattice of class $x$. -/
@[kb "chenevierlannes2019" "§1.3, p. 7; §3.2, p. 55 (T_p)"]
noncomputable def heckeT {R : Type*} [AddCommMonoid R] (p : ℕ) [Fact p.Prime] (f : QClass n → R) (x : QClass n) : R :=
  ∑ y ∈ (classSet_finite n).toFinset, nbNum p x y • f y

theorem out_isEvenUnimodular {x : QClass n} (hx : x ∈ classSet n) :
    IsEvenUnimodular (Quotient.out (s := intSetoid n) x) := by
  rw [← mem_classSet_classOf]
  have : classOf (Quotient.out (s := intSetoid n) x) = x := Quotient.out_eq _
  rwa [this]

/-- **Proposition 3.2.2** (Chenevier–Lannes, p. 56; odd $p$): for every $x \in X_n$ ($n > 0$),
$\sum_{y \in X_n} N_p(x, y) = c_n(p)$. Unconditional (every $p$-neighbour lies in $X_n$, `sum_nbCount`, and
`card_neighbors_eq_cn`). -/
@[kb "chenevierlannes2019" "Prop. 3.2.2, p. 56 (odd p)"]
theorem sum_nbNum {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 0 < n) {x : QClass n} (hx : x ∈ classSet n) :
    ∑ y ∈ (classSet_finite n).toFinset, nbNum p x y = cn n p := by
  have hQ := out_isEvenUnimodular hx
  unfold nbNum
  rw [sum_nbCount hp2 (not_dvd_det hQ p) _
      (fun c => by rw [Set.Finite.mem_toFinset, classSet_eq_genusClasses hQ]),
    card_neighbors_eq_cn hQ hn hp2]

/-- $|O(x)|$ is the order of the automorphism group of the chosen representative. -/
theorem autCard_eq_out (x : QClass n) : x.autCard = Nat.card (Aut (Quotient.out (s := intSetoid n) x)) := by
  conv_lhs => rw [← (Quotient.out_eq x : classOf (Quotient.out (s := intSetoid n) x) = x)]
  rfl

/-- **Scholium 3.1.7 and Proposition 3.2.3** (Chenevier–Lannes, pp. 49 and 56; odd $p$): for $x, y \in X_n$,
$$N_p(x, y)\,|O(y)| = N_p(y, x)\,|O(x)|,$$
i.e. $T_p$ is self-adjoint for the inner product $(x \mid y) = |O(x)|\,\delta_{x,y}$ on $\mathbb{Z}[X_n]$. Unconditional
(`Siegel.Kneser.nbCount_mul_autCard`, the double count of neighbour matrices). -/
@[kb "chenevierlannes2019" "Scholium 3.1.7, p. 49; Prop. 3.2.3, p. 56 (odd p)"]
theorem nbNum_mul_autCard {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {x y : QClass n} (hx : x ∈ classSet n)
    (hy : y ∈ classSet n) : nbNum p x y * y.autCard = nbNum p y x * x.autCard := by
  have hQ := out_isEvenUnimodular hx
  have hQ' := out_isEvenUnimodular hy
  have h := nbCount_mul_autCard hp2 hQ.posDef hQ'.posDef (not_dvd_det hQ p) (not_dvd_det hQ' p)
  have ex : classOf (Quotient.out (s := intSetoid n) x) = x := Quotient.out_eq _
  have ey : classOf (Quotient.out (s := intSetoid n) y) = y := Quotient.out_eq _
  rw [ex, ey] at h
  unfold nbNum
  rw [autCard_eq_out x, autCard_eq_out y]
  exact h

/-- **Proposition 3.2.4** (Chenevier–Lannes, p. 56; odd $p$): $\sum_{x \in X_n} x/|O(x)|$ is an eigenvector of $T_p$ with
eigenvalue $c_n(p)$. In coordinates: for every $y \in X_n$ ($n > 0$),
$$\sum_{x \in X_n} \frac{N_p(x, y)}{|O(x)|} = \frac{c_n(p)}{|O(y)|}.$$
Unconditional (from `nbNum_mul_autCard` and `sum_nbNum`). -/
@[kb "chenevierlannes2019" "Prop. 3.2.4, p. 56 (odd p)"]
theorem sum_nbNum_div_autCard {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 0 < n) {y : QClass n}
    (hy : y ∈ classSet n) :
    ∑ x ∈ (classSet_finite n).toFinset, (nbNum p x y : ℚ) / x.autCard = cn n p / y.autCard := by
  have hpos : ∀ x ∈ classSet n, (x.autCard : ℚ) ≠ 0 := fun x hx => by
    have h := (out_isEvenUnimodular hx).posDef.card_aut_pos
    rw [autCard_eq_out x]
    exact_mod_cast h.ne'
  calc ∑ x ∈ (classSet_finite n).toFinset, (nbNum p x y : ℚ) / x.autCard
      = ∑ x ∈ (classSet_finite n).toFinset, (nbNum p y x : ℚ) / y.autCard :=
        Finset.sum_congr rfl fun x hx => by
          have hx' := (Set.Finite.mem_toFinset _).mp hx
          rw [div_eq_div_iff (hpos x hx') (hpos y hy)]
          exact_mod_cast nbNum_mul_autCard hp2 hx' hy
    _ = (∑ x ∈ (classSet_finite n).toFinset, (nbNum p y x : ℚ)) / y.autCard := by rw [Finset.sum_div]
    _ = cn n p / y.autCard := by rw [← sum_nbNum hp2 hn hy]; push_cast; rfl

/-! ### Kneser's connectivity theorem -/

/-- **The neighbour graph $K_n(p)$ is connected** (the conclusion of Chenevier–Lannes, Theorem 3.1.12, p. 52, for one
$n$ and $p$): any two even unimodular lattices of dimension $n$ are joined by a chain of $p$-neighbour steps
(`Siegel.Kneser.NbrReach`, steps between classes). -/
@[kb "chenevierlannes2019" "§3.1, p. 52 (K_n(p) and Thm. 3.1.12)"]
def NeighborGraphConnected (n p : ℕ) : Prop :=
  ∀ Q Q' : QuadForm ℤ n, IsEvenUnimodular Q → IsEvenUnimodular Q' → NbrReach p Q Q'

/-- **Theorem 3.1.12 (M. Kneser)** (Chenevier–Lannes, p. 52; named statement): for every $n$ and every prime $p$, the
graph $K_n(p)$ of $p$-neighbours on $X_n$ is connected. Proved below for odd $p$ and $n \ge 3$ conditional on
`EvenUnimodularOneSpinorGenus`; the case $p = 2$ is not proved here. -/
@[kb "chenevierlannes2019" "Thm. 3.1.12, p. 52"]
def KneserConnectivity : Prop := ∀ n p : ℕ, p.Prime → NeighborGraphConnected n p

/-- **Input: the genus of an even unimodular lattice is one spinor genus** (Eichler, Kneser; used by Chenevier–Lannes in
the proof of Theorem 3.1.12, p. 52, through strong approximation for the spin group). For every even unimodular $Q$ of
dimension $n$, every lattice of $(\mathbb{Q}^n, Q)$ in the genus of $\mathbb{Z}^n$ lies in its spinor genus. This is the
hypothesis `hgs` of `Siegel.Kneser.kneserConnected_of_spinorGenus`, assumed rather than proved: it follows from the local
spinor norms $\theta(O^+(L_p)) \supseteq \mathbb{Z}_p^\times$ of unimodular $\mathbb{Z}_p$-lattices (including $p = 2$ for
even ones) and $h^+(\mathbb{Q}) = 1$, which are not formalized for definite forms here. -/
@[kb "chenevierlannes2019" "proof of Thm. 3.1.12, p. 52 (genus = spinor genus)"]
structure EvenUnimodularOneSpinorGenus (n : ℕ) : Prop where
  /-- Every lattice in the genus of $\mathbb{Z}^n$ for an even unimodular $Q$ is in its spinor genus. -/
  spinor : ∀ Q : QuadForm ℤ n, IsEvenUnimodular Q →
    ∀ M : Lattices.Lat ℚ n, Lattices.SameGenus (HilbertModular.formF (Tamagawa.RatBridge.up Q)) Lattices.intVec M.1 →
      Lattices.SameSpinorGenus (HilbertModular.formF (Tamagawa.RatBridge.up Q)) (HilbertModular.stdLat (F := ℚ)) M

/-- **Kneser's theorem for odd $p$** (Chenevier–Lannes, Theorem 3.1.12, p. 52, for $p$ odd and $n \ge 3$):
**conditional** on the named input `EvenUnimodularOneSpinorGenus n`, the neighbour graph $K_n(p)$ is connected. From
`Siegel.Kneser.kneserConnected_of_spinorGenus` and `sameGenus_of_isEvenUnimodular`. -/
@[kb "chenevierlannes2019" "Thm. 3.1.12, p. 52 (odd p, conditional)"]
theorem kneser_connected_of_input (hsp : EvenUnimodularOneSpinorGenus n) (hn : 3 ≤ n) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) : NeighborGraphConnected n p := by
  intro Q Q' hQ hQ'
  refine kneserConnected_of_spinorGenus Q hQ.posDef hn p hp2 ?_ (hsp.spinor Q hQ) Q'
    (sameGenus_of_isEvenUnimodular hQ hQ')
  rw [hQ.det_one]
  exact fun h => (Fact.out : p.Prime).one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by omega) h)

end QuadFormsKB.ChenevierLannes
