/-
# Cassels, Chapter 12: remarks on Lemma 1.2, Example 1 (ii)–(iii), and the binary action formula

Cassels, *Rational Quadratic Forms* (1978), Ch. 12: Lemma 1.2 and Note 2 (p. 257), the binary case (p. 275), and
Example 1 (ii), (iii) (p. 282). Conventions: indices are 0-based (`Fin n`; Cassels' $x_1, \dots, x_n$ are
$x_0, \dots, x_{n-1}$ here); a form $f(\vec{x}) = \vec{x}^{\mathsf T} F \vec{x}$ is given by its real symmetric matrix $F$, as
in the rest of the Chapter 12 files (`Reduction.val`, `Reduction.act`, `Reduction.IsMinkowskiReduced`).

## What is formalized

* **Note 2 to Lemma 1.2** (`note_two`): for $n \le 4$, every test vector $\vec{s}$ of Lemma 1.2 (ii)
  (`minkowskiTestVectors`) other than the trivial one $\vec{s} = e_j$ is needed: there is a real symmetric $F$ that
  satisfies (i) and (ii) for every test vector except $\vec{s}$, but violates (ii) for $\vec{s}$, hence is not
  Minkowski-reduced. The witnesses are explicit integral matrices (tables `witList2`, `witList3`, `witList4`, found by
  computer search and checked by `decide`); they are *not* the forms in the neighbourhoods of Cassels' examples
  $f_n = \sum_i x_i^2 + (\sum_i x_i)^2$ ($2 \le n \le 4$) and $g_4 = 2\sum_i x_i^2 + 2x_3(x_0 + x_1 + x_2)$ (0-based; the
  book's $g_4$ has $2x_4(x_1 + x_2 + x_3)$), which the book only describes in words. *Update:* the book's claim that the
  set of $\vec{s}$ in (ii) "cannot be replaced by a smaller set" is literally false for $\vec{s} = e_j$ (the
  inequality $f_{jj} \le f(e_j)$ is an equality, so these vectors can be dropped); it holds exactly for the
  nontrivial vectors. (The tests with $\vec{s} = e_j$ are formally part of `minkowskiTestVectors`, but they are
  vacuous.) The book's wording about "forms in the neighbourhood" is replaced by the equivalent, precise statement
  that the other conditions do not imply the condition for $\vec{s}$.
* **Example 1 (ii), (iii)** (`example_1_ii`, `example_1_iii`): positive definiteness and an explicit unimodular
  reduction, in the same style as `Reduction.example_1_i`.
* **Binary action formula** (`act_binary_entries`, `act_binary_point`): the coefficients of $T f$ for
  $T = \begin{pmatrix} a & b \\ c & d \end{pmatrix}$ acting on $[f_{00}, f_{01}, f_{11}]$, and the induced map on the
  disc coordinates $(\xi, \eta)$ of `binXi`, `binEta`. The statements match the printed formulas (p. 275, read from the page image)
  and are proved by direct computation of $T^{\mathsf T} F T$.

Helpers (`IntCond`, `qf`, `decodeVec`, ...) reduce statements about the finitely many test vectors with entries in
$\{0, \pm 1\}$ to decidable statements about integer matrices.
-/
import QuadFormsKB.Literature.Cassels.Ch12.LemmaOneTwo
import QuadFormsKB.Literature.Cassels.Ch12.Sec6

open Matrix

namespace QuadFormsKB.Reduction
namespace Ch12Remarks

variable {n : ℕ}

/-- Helper: decoding of the digits $0, 1, 2$ of `Fin 3` as the integers $0, 1, -1$. -/
def dig (t : Fin 3) : ℤ := ![0, 1, -1] t

/-- Helper: the integer vector with coordinates `dig (t i)`, i.e. with all entries in $\{0, 1, -1\}$. -/
def decodeVec (t : Fin n → Fin 3) : Fin n → ℤ := fun i => dig (t i)

/-- Helper: the integral value $\sum_{i,k} s_i G_{ik} s_k$ of the quadratic form of an integer matrix $G$ at an
integer vector $s$. -/
def qf (G : Matrix (Fin n) (Fin n) ℤ) (s : Fin n → ℤ) : ℤ := ∑ i, ∑ k, s i * G i k * s k

/-- Helper: the finite-check form of the hypotheses of Lemma 1.2 for an integer matrix $G$: symmetry, (i), and (ii) for
every test vector (with entries in $\{0, \pm 1\}$, given as a digit vector `t`) for which `skip j s` is `false`. -/
def IntCond (G : Matrix (Fin n) (Fin n) ℤ) (skip : Fin n → (Fin n → ℤ) → Bool) : Prop :=
  Gᵀ = G ∧ (∀ i : Fin n, i.val = 0 → 0 < G i i) ∧ (∀ i k : Fin n, i ≤ k → G i i ≤ G k k) ∧
    ∀ (j : Fin n) (t : Fin n → Fin 3), t j = 1 → (∀ i, j < i → t i = 0) →
      skip j (decodeVec t) = false → G j j ≤ qf G (decodeVec t)

instance (G : Matrix (Fin n) (Fin n) ℤ) (skip : Fin n → (Fin n → ℤ) → Bool) : Decidable (IntCond G skip) := by
  unfold IntCond
  infer_instance

/-- Helper: the skip function that omits exactly the test $(j_0, \vec{s}_0)$. -/
def skipOne (j₀ : Fin n) (s₀ : Fin n → ℤ) : Fin n → (Fin n → ℤ) → Bool :=
  fun j s => decide (j = j₀ ∧ s = s₀)

/-- Helper: every test vector of Lemma 1.2 (ii) is `decodeVec t` for a digit vector `t` with $t_j = 1$ and $t_i = 0$ for
$i > j$. -/
theorem exists_code {j : Fin n} {s : Fin n → ℤ} (hs : s ∈ minkowskiTestVectors j) :
    ∃ t : Fin n → Fin 3, decodeVec t = s ∧ t j = 1 ∧ ∀ i, j < i → t i = 0 := by
  have hall : ∀ i, s i = 0 ∨ s i = 1 ∨ s i = -1 := by
    intro i
    rcases lt_trichotomy i j with h | h | h
    · exact hs.1 i h
    · subst h; exact Or.inr (Or.inl hs.2.1)
    · exact Or.inl (hs.2.2 i h)
  refine ⟨fun i => if s i = 0 then 0 else if s i = 1 then 1 else 2, ?_, ?_, ?_⟩
  · funext i
    rcases hall i with h | h | h <;> simp [decodeVec, dig, h]
  · simp [hs.2.1]
  · intro i hi
    simp [hs.2.2 i hi]

/-- Helper: $f(\vec{s}) = \sum_{i,k} s_i F_{ik} s_k$ for the cast of an integer matrix and integer vector. -/
theorem val_castM_cast (G : Matrix (Fin n) (Fin n) ℤ) (s : Fin n → ℤ) :
    val (castM G) (cast s) = (qf G s : ℝ) := by
  simp only [val, dotProduct, Matrix.mulVec, qf, castM, Matrix.map_apply, cast]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Helper: an integer matrix satisfying `IntCond G skip` gives a real form with symmetry, (i), and (ii) for all test
vectors not skipped. -/
theorem IntCond.real {G : Matrix (Fin n) (Fin n) ℤ} {skip : Fin n → (Fin n → ℤ) → Bool} (h : IntCond G skip) :
    (castM G).IsSymm ∧ (∀ i : Fin n, i.val = 0 → 0 < castM G i i) ∧ (∀ i k : Fin n, i ≤ k → castM G i i ≤ castM G k k) ∧
      ∀ j : Fin n, ∀ s ∈ minkowskiTestVectors j, skip j s = false → castM G j j ≤ val (castM G) (cast s) := by
  obtain ⟨hsym, h0, hmono, htest⟩ := h
  refine ⟨?_, fun i hi => ?_, fun i k hik => ?_, fun j s hs hsk => ?_⟩
  · show (G.map (Int.cast : ℤ → ℝ))ᵀ = G.map (Int.cast : ℤ → ℝ)
    rw [← Matrix.transpose_map, hsym]
  · simpa [castM] using h0 i hi
  · simpa [castM] using hmono i k hik
  · obtain ⟨t, rfl, hj, hz⟩ := exists_code hs
    rw [val_castM_cast]
    have := htest j t hj hz hsk
    simpa [castM] using this

/-- Helper: for $n \le 4$, an integer matrix satisfying `IntCond` with nothing skipped is Minkowski-reduced (Lemma 1.2). -/
theorem IntCond.isMinkowskiReduced (hn : n ≤ 4) {G : Matrix (Fin n) (Fin n) ℤ}
    (h : IntCond G (fun _ _ => false)) : IsMinkowskiReduced (castM G) := by
  obtain ⟨hs, h0, hm, ht⟩ := h.real
  exact (lemma_1_2 hn hs).2 ⟨h0, hm, fun j s hs' => ht j s hs' rfl⟩

/-- Helper: a table of candidate witnesses for Note 2: entries (row index $j$, test vector, integer matrix). -/
abbrev WitList (n : ℕ) := List (Fin n × (Fin n → ℤ) × Matrix (Fin n) (Fin n) ℤ)

/-- Helper: the statement that a table covers every nontrivial test vector: for each $j$ and each digit vector with
$t_j = 1$, $t_i = 0$ ($i > j$) other than $e_j$, some table entry is an integer matrix satisfying (i), symmetry and
(ii) except at $(j, \vec{s})$, and violating (ii) at $(j, \vec{s})$. -/
def WitOK (L : WitList n) : Prop :=
  ∀ (j : Fin n) (t : Fin n → Fin 3), t j = 1 → (∀ i, j < i → t i = 0) → decodeVec t ≠ Pi.single j 1 →
    ∃ p ∈ L, p.1 = j ∧ p.2.1 = decodeVec t ∧ IntCond p.2.2 (skipOne j (decodeVec t)) ∧
      qf p.2.2 (decodeVec t) < p.2.2 j j

instance (L : WitList n) : Decidable (WitOK L) := by
  unfold WitOK
  infer_instance

set_option maxHeartbeats 4000000 in
/-- Helper: explicit witnesses for Note 2 ($n = 2$): for each nontrivial test vector, an integer symmetric matrix
satisfying (i) and (ii) except for that vector, for which (ii) fails. Found by computer search. -/
def witList2 : WitList 2 := [
  ((1 : Fin 2), ![1, 1], !![7, -4; -4, 7]),
  ((1 : Fin 2), ![-1, 1], !![5, 4; 4, 7])]

/-- Helper: the table `witList2` covers every nontrivial test vector ($n = 2$), by exhaustive evaluation. -/
theorem witOK2 : WitOK witList2 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- Helper: explicit witnesses for Note 2 ($n = 3$): for each nontrivial test vector, an integer symmetric matrix
satisfying (i) and (ii) except for that vector, for which (ii) fails. Found by computer search. -/
def witList3 : WitList 3 := [
  ((2 : Fin 3), ![0, -1, 1], !![6, -3, -3; -3, 6, 4; -3, 4, 6]),
  ((2 : Fin 3), ![-1, 0, 1], !![6, -2, 4; -2, 6, -2; 4, -2, 6]),
  ((1 : Fin 3), ![-1, 1, 0], !![8, 5, 3; 5, 8, 4; 3, 4, 8]),
  ((2 : Fin 3), ![1, 0, 1], !![6, -3, -4; -3, 6, 3; -4, 3, 7]),
  ((2 : Fin 3), ![0, 1, 1], !![5, -2, 2; -2, 5, -3; 2, -3, 6]),
  ((1 : Fin 3), ![1, 1, 0], !![7, -4, -3; -4, 8, 4; -3, 4, 9]),
  ((2 : Fin 3), ![1, 1, 1], !![3, -1, -1; -1, 4, -2; -1, -2, 4]),
  ((2 : Fin 3), ![-1, -1, 1], !![3, -1, 1; -1, 4, 2; 1, 2, 4]),
  ((2 : Fin 3), ![1, -1, 1], !![3, 1, -1; 1, 4, 2; -1, 2, 4]),
  ((2 : Fin 3), ![-1, 1, 1], !![3, 1, 1; 1, 4, -2; 1, -2, 4])]

/-- Helper: the table `witList3` covers every nontrivial test vector ($n = 3$), by exhaustive evaluation. -/
theorem witOK3 : WitOK witList3 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- Helper: explicit witnesses for Note 2 ($n = 4$): for each nontrivial test vector, an integer symmetric matrix
satisfying (i) and (ii) except for that vector, for which (ii) fails. Found by computer search. -/
def witList4 : WitList 4 := [
  ((2 : Fin 4), ![0, 1, 1, 0], !![8, 4, -4, 3; 4, 8, -5, 3; -4, -5, 8, -4; 3, 3, -4, 8]),
  ((3 : Fin 4), ![0, 1, -1, 1], !![8, 0, -3, 0; 0, 8, 4, -1; -3, 4, 8, 4; 0, -1, 4, 8]),
  ((3 : Fin 4), ![0, -1, 0, 1], !![3, 1, 1, 1; 1, 5, 2, 3; 1, 2, 5, 2; 1, 3, 2, 5]),
  ((3 : Fin 4), ![0, 1, 0, 1], !![4, 2, 2, -2; 2, 4, 2, -3; 2, 2, 4, -1; -2, -3, -1, 4]),
  ((3 : Fin 4), ![1, 0, 0, 1], !![6, -3, 2, -4; -3, 6, -2, 3; 2, -2, 6, -3; -4, 3, -3, 7]),
  ((3 : Fin 4), ![0, -1, -1, 1], !![4, 1, 1, 2; 1, 4, -1, 2; 1, -1, 4, 2; 2, 2, 2, 4]),
  ((2 : Fin 4), ![1, 1, 1, 0], !![4, -2, -2, 2; -2, 4, -1, -1; -2, -1, 4, 0; 2, -1, 0, 4]),
  ((1 : Fin 4), ![-1, 1, 0, 0], !![8, 5, 3, 4; 5, 8, 3, 3; 3, 3, 9, 4; 4, 3, 4, 9]),
  ((1 : Fin 4), ![1, 1, 0, 0], !![6, -4, 2, 3; -4, 6, 0, -1; 2, 0, 7, 0; 3, -1, 0, 7]),
  ((3 : Fin 4), ![0, 0, 1, 1], !![8, -4, 4, -3; -4, 8, -4, 4; 4, -4, 8, -5; -3, 4, -5, 8]),
  ((3 : Fin 4), ![-1, 0, 0, 1], !![3, 1, -1, 2; 1, 4, -2, 2; -1, -2, 5, -1; 2, 2, -1, 5]),
  ((2 : Fin 4), ![1, 0, 1, 0], !![8, 3, -5, 3; 3, 8, -4, 3; -5, -4, 8, -3; 3, 3, -3, 8]),
  ((3 : Fin 4), ![1, 1, 0, 1], !![4, -1, 1, -2; -1, 4, 1, -2; 1, 1, 4, -1; -2, -2, -1, 4]),
  ((2 : Fin 4), ![-1, -1, 1, 0], !![6, -1, 3, 0; -1, 6, 3, 0; 3, 3, 6, -2; 0, 0, -2, 7]),
  ((3 : Fin 4), ![0, 0, -1, 1], !![8, 0, 0, 3; 0, 8, 0, 3; 0, 0, 9, 5; 3, 3, 5, 9]),
  ((2 : Fin 4), ![0, -1, 1, 0], !![6, -3, -3, 3; -3, 6, 4, -3; -3, 4, 6, -3; 3, -3, -3, 6]),
  ((2 : Fin 4), ![1, -1, 1, 0], !![6, 3, -3, 3; 3, 6, 1, 1; -3, 1, 6, -1; 3, 1, -1, 6]),
  ((2 : Fin 4), ![-1, 0, 1, 0], !![6, -2, 4, -2; -2, 6, -3, 2; 4, -3, 6, -3; -2, 2, -3, 6]),
  ((3 : Fin 4), ![1, 0, 1, 1], !![6, 0, -3, -1; 0, 6, 2, 0; -3, 2, 6, -3; -1, 0, -3, 6]),
  ((3 : Fin 4), ![0, 1, 1, 1], !![5, 0, 0, 2; 0, 5, -1, -2; 0, -1, 6, -3; 2, -2, -3, 6]),
  ((3 : Fin 4), ![-1, 0, -1, 1], !![5, 0, -2, 1; 0, 6, -2, -1; -2, -2, 6, 3; 1, -1, 3, 6]),
  ((3 : Fin 4), ![-1, 1, 1, 1], !![3, 1, 1, 0; 1, 4, -1, -1; 1, -1, 4, -2; 0, -1, -2, 4]),
  ((3 : Fin 4), ![-1, 1, -1, 1], !![8, 4, 0, 1; 4, 8, 4, -3; 0, 4, 8, 1; 1, -3, 1, 8]),
  ((3 : Fin 4), ![1, 0, -1, 1], !![4, 1, 2, -1; 1, 4, 2, 1; 2, 2, 4, 2; -1, 1, 2, 4]),
  ((3 : Fin 4), ![-1, 1, 0, 1], !![4, 2, 2, 2; 2, 4, 1, -1; 2, 1, 4, 1; 2, -1, 1, 5]),
  ((3 : Fin 4), ![1, -1, 1, 1], !![8, 1, -3, -1; 1, 8, 4, 0; -3, 4, 8, -4; -1, 0, -4, 8]),
  ((2 : Fin 4), ![-1, 1, 1, 0], !![8, 1, 4, 1; 1, 8, -4, -1; 4, -4, 8, 4; 1, -1, 4, 8]),
  ((3 : Fin 4), ![-1, -1, 0, 1], !![6, -3, 0, 1; -3, 7, 3, 3; 0, 3, 7, 0; 1, 3, 0, 7]),
  ((3 : Fin 4), ![1, 1, 1, 1], !![4, -2, 0, -1; -2, 4, -2, -1; 0, -2, 4, -1; -1, -1, -1, 4]),
  ((3 : Fin 4), ![0, -1, 1, 1], !![4, 1, 0, 1; 1, 4, 1, 2; 0, 1, 4, -2; 1, 2, -2, 5]),
  ((3 : Fin 4), ![-1, 0, 1, 1], !![6, 0, 3, 1; 0, 6, 3, -1; 3, 3, 7, -3; 1, -1, -3, 7]),
  ((3 : Fin 4), ![1, -1, -1, 1], !![8, 1, 3, -1; 1, 8, -4, 0; 3, -4, 8, 4; -1, 0, 4, 8]),
  ((3 : Fin 4), ![1, -1, 0, 1], !![6, 1, -1, -3; 1, 6, 1, 3; -1, 1, 7, 2; -3, 3, 2, 7]),
  ((3 : Fin 4), ![-1, -1, 1, 1], !![6, -2, 1, 1; -2, 6, 3, 3; 1, 3, 6, 0; 1, 3, 0, 7]),
  ((3 : Fin 4), ![-1, -1, -1, 1], !![3, -1, -1, 1; -1, 3, -1, 1; -1, -1, 3, 0; 1, 1, 0, 5]),
  ((3 : Fin 4), ![1, 1, -1, 1], !![6, -3, 1, 0; -3, 6, 2, -3; 1, 2, 7, 1; 0, -3, 1, 7])]

/-- Helper: the table `witList4` covers every nontrivial test vector ($n = 4$), by exhaustive evaluation. -/
theorem witOK4 : WitOK witList4 := by decide +kernel


/-- **Note 2 to Lemma 1.2** (Cassels, Ch. 12, §1, p. 257): for $n \le 4$, no nontrivial test vector of Lemma 1.2 (ii) can
be dropped. For every $j$ and every $\vec{s}$ in `minkowskiTestVectors j` other than the trivial vector $e_j$ (for which
(ii) reads $f_{jj} \le f_{jj}$), there is a real symmetric matrix $F$ ($n \times n$) satisfying (i) and (ii) for all test
vectors $(j', \vec{s}')$ other than $(j, \vec{s})$, with $f(\vec{s}) < f_{jj}$; so $F$ is not Minkowski-reduced.
*Update:* the printed claim ("the set of $\vec{s}$ cannot be replaced by a smaller set") holds only for the
nontrivial $\vec{s}$; the vectors $\vec{s} = e_j$ are redundant. Arguments: `hn` is $n \le 4$, `j` the index, `s` the
test vector (`hs`: it lies in `minkowskiTestVectors j`; `hne`: it is not $e_j$). -/
@[kb "cassels1978" "Ch. 12, §1, Lemma 1.2, Note 2, p. 257"]
theorem note_two (hn : n ≤ 4) (j : Fin n) (s : Fin n → ℤ) (hs : s ∈ minkowskiTestVectors j)
    (hne : s ≠ Pi.single j 1) :
    ∃ F : Matrix (Fin n) (Fin n) ℝ, F.IsSymm ∧ (∀ i : Fin n, i.val = 0 → 0 < F i i) ∧
      (∀ i k : Fin n, i ≤ k → F i i ≤ F k k) ∧
      (∀ j' : Fin n, ∀ s' ∈ minkowskiTestVectors j', (j', s') ≠ (j, s) → F j' j' ≤ val F (cast s')) ∧
      val F (cast s) < F j j ∧ ¬ IsMinkowskiReduced F := by
  have key : ∃ G : Matrix (Fin n) (Fin n) ℤ, IntCond G (skipOne j s) ∧ qf G s < G j j := by
    interval_cases n
    · exact j.elim0
    · exfalso
      apply hne
      funext i
      have : i = j := Subsingleton.elim _ _
      subst this
      simp [hs.2.1]
    · obtain ⟨t, rfl, hj, hz⟩ := exists_code hs
      obtain ⟨p, -, -, -, hI, hlt⟩ := witOK2 j t hj hz hne
      exact ⟨p.2.2, hI, hlt⟩
    · obtain ⟨t, rfl, hj, hz⟩ := exists_code hs
      obtain ⟨p, -, -, -, hI, hlt⟩ := witOK3 j t hj hz hne
      exact ⟨p.2.2, hI, hlt⟩
    · obtain ⟨t, rfl, hj, hz⟩ := exists_code hs
      obtain ⟨p, -, -, -, hI, hlt⟩ := witOK4 j t hj hz hne
      exact ⟨p.2.2, hI, hlt⟩
  obtain ⟨G, hI, hlt⟩ := key
  obtain ⟨hsym, h0, hm, ht⟩ := hI.real
  have hsk : ∀ j' s', (j', s') ≠ (j, s) → skipOne j s j' s' = false := by
    intro j' s' h
    simp only [skipOne, decide_eq_false_iff_not]
    rintro ⟨h1, h2⟩
    exact h (by rw [h1, h2])
  have hlt' : val (castM G) (cast s) < castM G j j := by
    rw [val_castM_cast]
    simpa [castM] using (show ((qf G s : ℤ) : ℝ) < ((G j j : ℤ) : ℝ) by exact_mod_cast hlt)
  refine ⟨castM G, hsym, h0, hm, fun j' s' hs' hne' => ht j' s' hs' (hsk j' s' hne'), hlt', ?_⟩
  intro hR
  have h3 := ((lemma_1_2 hn hsym).1 hR).2.2 j s hs
  linarith

/-- **Example 1 (ii)** (Cassels, Ch. 12, p. 282): $f = 25x^2 + 22xy + 5y^2$ (matrix
$\begin{pmatrix}25 & 11\\ 11 & 5\end{pmatrix}$, determinant $4$) is positive definite, and the unimodular substitution
$T = \begin{pmatrix}1 & -1\\ -2 & 3\end{pmatrix}$, $(x, y) = (X - Y, -2X + 3Y)$, takes it to the reduced form
$X^2 + 4Y^2$. (The new basis vectors are $(1, -2)$, with $f = 1$, and $(-1, 3)$, with $f = 4$.) -/
@[kb "cassels1978" "Ch. 12, Examples, Ex. 1 (ii), p. 282"]
theorem example_1_ii :
    (!![25, 11; 11, 5] : Matrix (Fin 2) (Fin 2) ℝ).PosDef ∧
      ∃ T : GL (Fin 2) ℤ, T.val = !![1, -1; -2, 3] ∧ act T.val !![25, 11; 11, 5] = !![1, 0; 0, 4] ∧
        IsMinkowskiReduced (!![1, 0; 0, 4] : Matrix (Fin 2) (Fin 2) ℝ) := by
  refine ⟨?_, ⟨!![1, -1; -2, 3], !![3, 1; 2, 1], ?_, ?_⟩, rfl, ?_, ?_⟩
  · rw [posDef_iff]
    refine ⟨by ext i j; fin_cases i <;> fin_cases j <;> simp, fun x hx => ?_⟩
    have : val (!![25, 11; 11, 5] : Matrix (Fin 2) (Fin 2) ℝ) x =
        25 * (x 0 + 11 / 25 * x 1) ^ 2 + 4 / 25 * x 1 ^ 2 := by
      simp [val, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      ring
    rw [this]
    by_cases h1 : x 1 = 0
    · have h0 : x 0 ≠ 0 := fun h0 => hx (by ext i; fin_cases i <;> simp [h0, h1])
      rw [h1]; have := sq_pos_of_ne_zero h0; nlinarith
    · have := sq_pos_of_ne_zero h1
      nlinarith [sq_nonneg (x 0 + 11 / 25 * x 1)]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [act, castM, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  · have h : (!![1, 0; 0, 4] : Matrix (Fin 2) (Fin 2) ℝ) = castM (!![1, 0; 0, 4] : Matrix (Fin 2) (Fin 2) ℤ) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [castM]
    rw [h]
    exact IntCond.isMinkowskiReduced (by norm_num) (by decide +kernel)

/-- **Example 1 (iii)** (Cassels, Ch. 12, p. 282): $f = x^2 + y^2 + z^2 + 10(x + y + z)^2$ (matrix with diagonal
entries $11$ and off-diagonal entries $10$) is positive definite, and the unimodular substitution
$T = \begin{pmatrix}1 & 0 & 0\\ -1 & 1 & 0\\ 0 & -1 & 1\end{pmatrix}$, $(x, y, z) = (X, -X + Y, -Y + Z)$, takes it to the
reduced form with matrix $\begin{pmatrix}2 & -1 & 0\\ -1 & 2 & -1\\ 0 & -1 & 11\end{pmatrix}$, i.e.
$2X^2 + 2Y^2 + 11Z^2 - 2XY - 2YZ$. (Reducedness is checked with Lemma 1.2, `lemma_1_2`, as $n = 3 \le 4$.) -/
@[kb "cassels1978" "Ch. 12, Examples, Ex. 1 (iii), p. 282"]
theorem example_1_iii :
    (!![11, 10, 10; 10, 11, 10; 10, 10, 11] : Matrix (Fin 3) (Fin 3) ℝ).PosDef ∧
      ∃ T : GL (Fin 3) ℤ, T.val = !![1, 0, 0; -1, 1, 0; 0, -1, 1] ∧
        act T.val !![11, 10, 10; 10, 11, 10; 10, 10, 11] = !![2, -1, 0; -1, 2, -1; 0, -1, 11] ∧
        IsMinkowskiReduced (!![2, -1, 0; -1, 2, -1; 0, -1, 11] : Matrix (Fin 3) (Fin 3) ℝ) := by
  refine ⟨?_, ⟨!![1, 0, 0; -1, 1, 0; 0, -1, 1], !![1, 0, 0; 1, 1, 0; 1, 1, 1], ?_, ?_⟩, rfl, ?_, ?_⟩
  · rw [posDef_iff]
    refine ⟨by ext i j; fin_cases i <;> fin_cases j <;> simp, fun x hx => ?_⟩
    have hv : val (!![11, 10, 10; 10, 11, 10; 10, 10, 11] : Matrix (Fin 3) (Fin 3) ℝ) x =
        x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + 10 * (x 0 + x 1 + x 2) ^ 2 := by
      simp [val, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    have hpos : 0 < x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
      by_contra hc
      push Not at hc
      have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
      have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
      have h2 : x 2 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
      exact hx (by ext i; fin_cases i <;> simp [h0, h1, h2])
    rw [hv]
    nlinarith [sq_nonneg (x 0 + x 1 + x 2)]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [act, castM, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num
  · have h : (!![2, -1, 0; -1, 2, -1; 0, -1, 11] : Matrix (Fin 3) (Fin 3) ℝ) =
        castM (!![2, -1, 0; -1, 2, -1; 0, -1, 11] : Matrix (Fin 3) (Fin 3) ℤ) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [castM]
    rw [h]
    exact IntCond.isMinkowskiReduced (by norm_num) (by decide +kernel)

/-- **The action of $T = \begin{pmatrix}a & b\\ c & d\end{pmatrix}$ on a binary form** (Cassels, Ch. 12, §6, p. 275,
as printed): for a symmetric $2 \times 2$ real matrix $F = (f_{ij})$ (the form $f_{00}x_0^2 + 2f_{01}x_0x_1 +
f_{11}x_1^2$, written $[f_{00}, f_{01}, f_{11}]$) and integers `a`, `b`, `c`, `d`, the form $Tf(\vec{x}) = f(T\vec{x})$
(`act`, matrix $T^{\mathsf T}FT$) has the entries
$$(Tf)_{00} = a^2f_{00} + 2ac\,f_{01} + c^2f_{11},\quad (Tf)_{01} = (Tf)_{10} = ab\,f_{00} + (ad + bc)f_{01} +
cd\,f_{11},\quad (Tf)_{11} = b^2f_{00} + 2bd\,f_{01} + d^2f_{11}.$$
This is the book's displayed formula (read from the page image). -/
@[kb "cassels1978" "Ch. 12, §6, p. 275 (action of T on a binary form)"]
theorem act_binary_entries (a b c d : ℤ) {F : Matrix (Fin 2) (Fin 2) ℝ} (hF : F.IsSymm) :
    act !![a, b; c, d] F 0 0 = (a : ℝ) ^ 2 * F 0 0 + 2 * a * c * F 0 1 + (c : ℝ) ^ 2 * F 1 1 ∧
    act !![a, b; c, d] F 0 1 = (a : ℝ) * b * F 0 0 + (a * d + b * c) * F 0 1 + (c : ℝ) * d * F 1 1 ∧
    act !![a, b; c, d] F 1 0 = (a : ℝ) * b * F 0 0 + (a * d + b * c) * F 0 1 + (c : ℝ) * d * F 1 1 ∧
    act !![a, b; c, d] F 1 1 = (b : ℝ) ^ 2 * F 0 0 + 2 * b * d * F 0 1 + (d : ℝ) ^ 2 * F 1 1 := by
  have h10 : F 1 0 = F 0 1 := by
    have := congrFun (congrFun hF 0) 1
    simpa using this
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [act, castM, Matrix.mul_apply, Fin.sum_univ_two, h10] <;> ring

/-- **The action of $T = \begin{pmatrix}a & b\\ c & d\end{pmatrix}$ on the point $(\xi, \eta)$ of a binary form**
(Cassels, Ch. 12, §6, p. 275, as printed): with $(\xi, \eta)$ = (`binXi F`, `binEta F`) the disc coordinates (6.4) of a
symmetric $F$ with $f_{00} + f_{11} \ne 0$, the coordinates of $Tf$ are $T(\xi, \eta) = (2p/t,\ q/t)$ where
$$p = (ab + cd) + (ad + bc)\xi + (cd - ab)\eta,\qquad
t = (a^2 + b^2 + c^2 + d^2) + 2(ac + bd)\xi + (c^2 + d^2 - a^2 - b^2)\eta,$$
$$q = (b^2 + d^2 - a^2 - c^2) + 2(bd - ac)\xi + (a^2 + d^2 - b^2 - c^2)\eta.$$
(In Lean division by $0$ is $0$, which is consistent on both sides when $t = 0$; for positive definite $F$ one has
$t > 0$.) The integers `a`, `b`, `c`, `d` are the entries of $T$; `hF` says $F$ is symmetric; `hs` is
$f_{00} + f_{11} \ne 0$. -/
@[kb "cassels1978" "Ch. 12, §6, p. 275 (action of T on the disc)"]
theorem act_binary_point (a b c d : ℤ) {F : Matrix (Fin 2) (Fin 2) ℝ} (hF : F.IsSymm) (hs : F 0 0 + F 1 1 ≠ 0) :
    binXi (act !![a, b; c, d] F) =
        2 * (((a : ℝ) * b + c * d) + (a * d + b * c) * binXi F + (c * d - a * b) * binEta F) /
          ((a : ℝ) ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + 2 * (a * c + b * d) * binXi F +
            (c ^ 2 + d ^ 2 - a ^ 2 - b ^ 2) * binEta F) ∧
    binEta (act !![a, b; c, d] F) =
        (((b : ℝ) ^ 2 + d ^ 2 - a ^ 2 - c ^ 2) + 2 * (b * d - a * c) * binXi F +
            (a ^ 2 + d ^ 2 - b ^ 2 - c ^ 2) * binEta F) /
          ((a : ℝ) ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + 2 * (a * c + b * d) * binXi F +
            (c ^ 2 + d ^ 2 - a ^ 2 - b ^ 2) * binEta F) := by
  obtain ⟨h00, h01, -, h11⟩ := act_binary_entries a b c d hF
  have hD : (a : ℝ) ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + 2 * (a * c + b * d) * binXi F +
      (c ^ 2 + d ^ 2 - a ^ 2 - b ^ 2) * binEta F =
      2 * (act !![a, b; c, d] F 0 0 + act !![a, b; c, d] F 1 1) / (F 0 0 + F 1 1) := by
    rw [h00, h11, binXi, binEta]
    field_simp
    ring
  by_cases hsum : act !![a, b; c, d] F 0 0 + act !![a, b; c, d] F 1 1 = 0
  · rw [hD, hsum]
    simp [binXi, binEta, hsum]
  · rw [hD]
    unfold binXi binEta
    rw [h00, h01, h11]
    rw [h00, h11] at hsum
    field_simp
    constructor <;> ring

end Ch12Remarks
end QuadFormsKB.Reduction
