import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2023ThreeTerm.Basic
import QuadFormsKB.Literature.Hanke2023ThreeTerm.Order
import QuadFormsKB.Literature.Hanke2023ThreeTerm.KeyLemma
import QuadFormsKB.Siegel.Inputs

/-!
# Saha–Hanke, three-term theta relations: successive minima, K-sets, normalized relations

Source: R. Saha and J. Hanke, *On three-term linear relations for theta series of positive-definite
binary quadratic forms*, arXiv:2307.00747v1 (bib key `hanke2023threeterm`), §3.3 (Definitions
3.13, 3.16, Example 3.14, Lemma 3.15, Remarks 3.17, 3.18, Corollary 3.19), §4 (Definition 4.1,
Lemmas 4.2, 4.3, Remark 4.4), §5.1 (Definitions 5.3, 5.5, Remark 5.4) and §5.2 (Remark 5.8).

Conventions used throughout this file.

* $\widetilde{\mathbb{Z}^2_*}$ is the set of strongly primitive vectors (`spSet`).
* Sequences are indexed from $0$ (`ℕ`, or `Fin k`), not from $1$ as in the paper; "the paper's
  $X_i$, $i \ge 1$" is `X i` with `i ≥ 1`, and `X 0` is an extra (possibly empty) member.
  Vectors $\vec x_1, \vec x_2, \dots$ of the paper are `x 0, x 1, …`.
* A set of vectors `S` is removed from a set `X` by the set difference `X \ S`.

Not formalized: Remark 3.18 (a description of an algorithm, not a mathematical statement) and
the existence of the normalization in Definition 5.3 (only the notion is recorded).
-/

namespace QuadFormsKB.Hanke2023ThreeTerm

open QuadFormsKB QuadFormsKB.Siegel

/-- The set $\widetilde{\mathbb{Z}^2_*}$ of strongly primitive vectors (Definition 3.1), as a
set of `ℤ × ℤ`. -/
def spSet : Set (ℤ × ℤ) := {v | StronglyPrimitive v}

lemma mem_spSet {v : ℤ × ℤ} : v ∈ spSet ↔ StronglyPrimitive v := Iff.rfl

lemma spSet_infinite : spSet.Infinite := by
  have hi : Function.Injective (fun a : ℤ => ((a, 1) : ℤ × ℤ)) := fun a b h => by simpa using h
  exact Set.infinite_of_injective_forall_mem hi (fun a => stronglyPrimitive_a_one a)

lemma sp_sumSq_pos {v : ℤ × ℤ} (hv : StronglyPrimitive v) :
    (0 : ℝ) < (v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2 := by
  by_contra h
  have h1 : (v.1 : ℝ) = 0 := by nlinarith [sq_nonneg (v.1 : ℝ), sq_nonneg (v.2 : ℝ)]
  have h2 : (v.2 : ℝ) = 0 := by nlinarith [sq_nonneg (v.1 : ℝ), sq_nonneg (v.2 : ℝ)]
  have h1' : v.1 = 0 := by exact_mod_cast h1
  have h2' : v.2 = 0 := by exact_mod_cast h2
  have := hv.1
  rw [h1', h2'] at this
  simp at this

/-- **Positive definiteness of a real binary form** $Q = (q_{11}, q_{22}, q_{12})$: the standard
criterion $q_{11} > 0$ and $4 q_{11} q_{22} - q_{12}^2 > 0$ (i.e. $q_{11} > 0$ and negative
discriminant). -/
def RForm.PosDef (Q : RForm) : Prop := 0 < Q.1 ∧ 0 < 4 * Q.1 * Q.2.1 - Q.2.2 ^ 2

lemma domainV_posDef {Q : RForm} (hQ : Q ∈ domainV) : Q.PosDef := by
  obtain ⟨h1, h2, h3, h4⟩ := hQ
  refine ⟨h4, ?_⟩
  nlinarith [mul_nonneg h2 h3, mul_pos h4 h4, mul_nonneg h4.le h1]

lemma finite_eval_le {Q : RForm} (hQ : Q ∈ domainV) (t : ℝ) :
    {w : ℤ × ℤ | Q.eval w ≤ t}.Finite := by
  have hq : 0 < Q.1 := hQ.2.2.2
  refine (finite_sumSq_le ⌈2 * t / Q.1⌉).subset ?_
  intro v hv
  have h := eval_ge hQ v
  have hv' : Q.eval v ≤ t := hv
  have h' : (v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2 ≤ 2 * t / Q.1 := by
    rw [le_div_iff₀ hq]; nlinarith
  have h'' : ((v.1 ^ 2 + v.2 ^ 2 : ℤ) : ℝ) ≤ 2 * t / Q.1 := by push_cast; exact h'
  exact Int.cast_le.mp (h''.trans (Int.le_ceil _))

lemma eval_pos_of_sp {Q : RForm} (hQ : Q ∈ domainV) {v : ℤ × ℤ} (hv : StronglyPrimitive v) :
    0 < Q.eval v := by
  have h := eval_ge hQ v
  have := sp_sumSq_pos hv
  have hq : 0 < Q.1 := hQ.2.2.2
  have : 0 < Q.1 / 2 * ((v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2) := by positivity
  linarith

/-! ### Definition 3.13, Example 3.14 -/

/-- **Definition 3.13 (successive minima sequence).** Let $Q$ be a positive definite real binary
form (field `posDef`) and $(X_i)_{i \ge 0}$ a sequence of sets of vectors. It is a *successive
minima sequence of $Q$* if the following hold (indices start at $0$, not $1$):
* `finite`: each $X_i$ is finite, and `subset`: each $X_i \subseteq \widetilde{\mathbb{Z}^2_*}$;
* `exists_unique` (condition 1): every strongly primitive vector lies in exactly one $X_i$;
* `const` (condition 2): for every $i$ there is $m \in \mathbb{R}_{>0}$ with
  $Q(X_i) \in \{\emptyset, \{m\}\}$ (`Q.eval '' X i`);
* `mono` (condition 3): for $i < j$ with $Q(X_i) = \{a\}$ and $Q(X_j) = \{b\}$ (i.e. both sets
  non-empty, the paper's "$Q(X_i) \le Q(X_j)$" for singletons) we have $a \le b$. -/
@[kb "hanke2023threeterm" "§3.3, Definition 3.13, p. 7"]
structure IsSuccMinSeq (Q : RForm) (X : ℕ → Set (ℤ × ℤ)) : Prop where
  posDef : Q.PosDef
  finite : ∀ i, (X i).Finite
  subset : ∀ i, X i ⊆ spSet
  exists_unique : ∀ v, StronglyPrimitive v → ∃! i, v ∈ X i
  const : ∀ i, ∃ m : ℝ, 0 < m ∧ (Q.eval '' X i = ∅ ∨ Q.eval '' X i = {m})
  mono : ∀ i j, i < j → ∀ a b : ℝ, Q.eval '' X i = {a} → Q.eval '' X j = {b} → a ≤ b

/-- **Example 3.14 (sums of two squares).** For $Q(x, y) = x^2 + y^2$ (`E2`) the sequence
$X_i = \{\vec v \text{ strongly primitive} : Q(\vec v) = i\}$ is a successive minima sequence.
(Paper: $i \ge 1$; here $X_0 = \emptyset$ is the extra term at index $0$, since no strongly
primitive vector has norm $0$.) -/
@[kb "hanke2023threeterm" "§3.3, Example 3.14, p. 7"]
theorem example_3_14 :
    IsSuccMinSeq E2 (fun i : ℕ => {v : ℤ × ℤ | StronglyPrimitive v ∧ E2.eval v = (i : ℝ)}) := by
  have key : ∀ (i : ℕ) (v : ℤ × ℤ), (E2.eval v = (i : ℝ)) ↔ v.1 ^ 2 + v.2 ^ 2 = (i : ℤ) := by
    intro i v
    rw [E2_eval]; exact_mod_cast Iff.rfl
  refine ⟨⟨by simp [E2], by simp [E2]⟩, ?_, fun i v hv => hv.1, ?_, ?_, ?_⟩
  · intro i
    refine (finite_sumSq_le (i : ℤ)).subset ?_
    intro v hv
    exact ((key i v).mp hv.2).le
  · intro v hv
    have hpos := sp_sumSq_pos hv
    have e : ((v.1 ^ 2 + v.2 ^ 2 : ℤ) : ℝ) = (((v.1 ^ 2 + v.2 ^ 2).toNat : ℕ) : ℝ) := by
      have h0 : 0 ≤ v.1 ^ 2 + v.2 ^ 2 := by positivity
      exact_mod_cast (Int.toNat_of_nonneg h0).symm
    refine ⟨(v.1 ^ 2 + v.2 ^ 2).toNat, ⟨hv, ?_⟩, ?_⟩
    · rw [E2_eval]; push_cast at e; linarith
    · rintro j ⟨-, hj⟩
      rw [E2_eval] at hj
      have : ((j : ℤ) : ℝ) = ((v.1 ^ 2 + v.2 ^ 2 : ℤ) : ℝ) := by push_cast; linarith
      have h2 : (j : ℤ) = v.1 ^ 2 + v.2 ^ 2 := by exact_mod_cast this
      omega
  · intro i
    by_cases hne : ({v : ℤ × ℤ | StronglyPrimitive v ∧ E2.eval v = (i : ℝ)}).Nonempty
    · obtain ⟨v, hv, hvi⟩ := hne
      refine ⟨i, ?_, Or.inr ?_⟩
      · rw [← hvi]; exact sp_sumSq_pos hv |>.trans_eq (E2_eval v).symm
      · ext r
        constructor
        · rintro ⟨w, hw, rfl⟩; exact hw.2
        · rintro rfl; exact ⟨v, ⟨hv, hvi⟩, hvi⟩
    · refine ⟨1, one_pos, Or.inl ?_⟩
      rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp
  · intro i j hij a b ha hb
    have ha' : a ∈ E2.eval '' {v : ℤ × ℤ | StronglyPrimitive v ∧ E2.eval v = (i : ℝ)} := by
      rw [ha]; rfl
    have hb' : b ∈ E2.eval '' {v : ℤ × ℤ | StronglyPrimitive v ∧ E2.eval v = (j : ℝ)} := by
      rw [hb]; rfl
    obtain ⟨v, hv, rfl⟩ := ha'
    obtain ⟨w, hw, rfl⟩ := hb'
    rw [hv.2, hw.2]; exact_mod_cast hij.le

/-! ### Lemma 3.15 -/

lemma exists_step {Q : RForm} (hQ : Q ∈ domainV) (S : Set (ℤ × ℤ)) (hS : S.Finite) :
    ∃ x, x ∈ MIN (spSet \ S) ∧ ∀ w ∈ spSet \ S, Q.eval x ≤ Q.eval w := by
  have hne : (spSet \ S).Nonempty := (spSet_infinite.sdiff hS).nonempty
  obtain ⟨m, hm1, hm2⟩ := MIN_attains_min (X := spSet \ S) (fun v hv => hv.1) hne hQ
  obtain ⟨x, hx, hxm⟩ := hm2.1
  refine ⟨x, hx, fun w hw => ?_⟩
  rw [hxm]; exact hm1.2 ⟨w, hw, rfl⟩

open scoped Classical in
/-- The vector chosen at one step of the construction of Lemma 3.15: a vector of
$\mathrm{MIN}(\widetilde{\mathbb{Z}^2_*} \setminus S)$ at which $Q$ is minimal on
$\widetilde{\mathbb{Z}^2_*} \setminus S$ (junk value $0$ if there is none). -/
noncomputable def minSeqStep (Q : RForm) (S : Finset (ℤ × ℤ)) : ℤ × ℤ :=
  if h : ∃ x, x ∈ MIN (spSet \ (S : Set (ℤ × ℤ))) ∧
      ∀ w ∈ spSet \ (S : Set (ℤ × ℤ)), Q.eval x ≤ Q.eval w then h.choose else 0

open scoped Classical in
/-- The finite set $\{\vec x_0, \dots, \vec x_{n-1}\}$ of vectors chosen so far. -/
noncomputable def minSeqState (Q : RForm) : ℕ → Finset (ℤ × ℤ)
  | 0 => ∅
  | n + 1 => insert (minSeqStep Q (minSeqState Q n)) (minSeqState Q n)

/-- The sequence $\vec x_n$ of Lemma 3.15. -/
noncomputable def minSeq (Q : RForm) (n : ℕ) : ℤ × ℤ := minSeqStep Q (minSeqState Q n)

lemma minSeqState_coe (Q : RForm) (n : ℕ) :
    ((minSeqState Q n : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = minSeq Q '' Set.Iio n := by
  induction n with
  | zero => simp [minSeqState]
  | succ n ih =>
    rw [minSeqState, Finset.coe_insert, ih]
    ext y
    simp only [Set.mem_insert_iff, Set.mem_image, Set.mem_Iio]
    constructor
    · rintro (rfl | ⟨k, hk, rfl⟩)
      · exact ⟨n, by omega, rfl⟩
      · exact ⟨k, by omega, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | rfl
      · exact Or.inr ⟨k, h, rfl⟩
      · exact Or.inl rfl

lemma minSeqStep_spec {Q : RForm} (hQ : Q ∈ domainV) (S : Finset (ℤ × ℤ)) :
    minSeqStep Q S ∈ MIN (spSet \ (S : Set (ℤ × ℤ))) ∧
      ∀ w ∈ spSet \ (S : Set (ℤ × ℤ)), Q.eval (minSeqStep Q S) ≤ Q.eval w := by
  have h : ∃ x, x ∈ MIN (spSet \ (S : Set (ℤ × ℤ))) ∧
      ∀ w ∈ spSet \ (S : Set (ℤ × ℤ)), Q.eval x ≤ Q.eval w :=
    exists_step hQ _ (Finset.finite_toSet _)
  unfold minSeqStep
  rw [dite_cond_eq_true (eq_true h)]
  exact h.choose_spec

lemma minSeq_spec {Q : RForm} (hQ : Q ∈ domainV) (n : ℕ) :
    minSeq Q n ∈ MIN (spSet \ (minSeq Q '' Set.Iio n)) ∧
      ∀ w ∈ spSet \ (minSeq Q '' Set.Iio n), Q.eval (minSeq Q n) ≤ Q.eval w := by
  have := minSeqStep_spec hQ (minSeqState Q n)
  rw [minSeqState_coe] at this
  exact this

lemma minSeq_injective {Q : RForm} (hQ : Q ∈ domainV) : Function.Injective (minSeq Q) := by
  have key : ∀ i j, i < j → minSeq Q i ≠ minSeq Q j := by
    intro i j hij h
    have := (minSeq_spec hQ j).1.1.2
    exact this ⟨i, hij, h⟩
  intro i j h
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact absurd h (key i j hij)
  · rfl
  · exact absurd h.symm (key j i hij)

lemma minSeq_mem_sp {Q : RForm} (hQ : Q ∈ domainV) (n : ℕ) : StronglyPrimitive (minSeq Q n) :=
  (minSeq_spec hQ n).1.1.1

/-- **Lemma 3.15 (MIN successive minima sequences).** Let $Q \in V$ (`domainV`). Then there is a
sequence $(\vec x_i)_{i \ge 0}$ of vectors such that $(\{\vec x_i\})_{i \ge 0}$ is a successive
minima sequence of $Q$ (`IsSuccMinSeq`) and, for every $i \ge 0$,
$\vec x_i \in \mathrm{MIN}\big(\widetilde{\mathbb{Z}^2_*} \setminus \{\vec x_0, \dots, \vec x_{i-1}\}\big)$
(for $i = 0$ the removed set is empty). Indices start at $0$; the paper's $\vec x_{i+1}$ is
`x i`. -/
@[kb "hanke2023threeterm" "§3.3, Lemma 3.15, p. 7"]
theorem exists_minSeq {Q : RForm} (hQ : Q ∈ domainV) :
    ∃ x : ℕ → ℤ × ℤ, IsSuccMinSeq Q (fun i => {x i}) ∧
      ∀ i, x i ∈ MIN (spSet \ (x '' Set.Iio i)) := by
  refine ⟨minSeq Q, ⟨domainV_posDef hQ, fun i => Set.finite_singleton _, ?_, ?_, ?_, ?_⟩,
    fun i => (minSeq_spec hQ i).1⟩
  · intro i v hv
    rw [Set.mem_singleton_iff.mp hv]; exact minSeq_mem_sp hQ i
  · intro v hv
    have hex : ∃ i, minSeq Q i = v := by
      by_contra hno
      push Not at hno
      have hinf : {w : ℤ × ℤ | Q.eval w ≤ Q.eval v}.Infinite := by
        refine Set.infinite_of_injective_forall_mem (minSeq_injective hQ) (fun n => ?_)
        refine (minSeq_spec hQ n).2 v ⟨hv, ?_⟩
        rintro ⟨k, -, hk⟩
        exact hno k hk
      exact hinf (finite_eval_le hQ _)
    obtain ⟨i, rfl⟩ := hex
    exact ⟨i, rfl, fun j hj => (minSeq_injective hQ (Set.mem_singleton_iff.mp hj)).symm⟩
  · intro i
    exact ⟨Q.eval (minSeq Q i), eval_pos_of_sp hQ (minSeq_mem_sp hQ i), Or.inr (by simp)⟩
  · intro i j hij a b ha hb
    simp only [Set.image_singleton, Set.singleton_eq_singleton_iff] at ha hb
    subst ha hb
    refine (minSeq_spec hQ i).2 _ ⟨minSeq_mem_sp hQ j, ?_⟩
    rintro ⟨k, hk, hkj⟩
    have := minSeq_injective hQ hkj
    simp only [Set.mem_Iio] at hk
    omega

/-! ### Definition 3.16, Remark 3.17, Corollary 3.19 -/

/-- **Definition 3.16 ($n$-th order minimal subset $\mathrm{MIN}_n(X)$).** For $X \subseteq
\mathbb{Z}^2$ and $n \in \mathbb{N}$, $\mathrm{MIN}_n(X)$ is the set of finite sets
$S \subseteq \widetilde{\mathbb{Z}^2_*}$ (`StronglyPrimitive` members) with $\#S = n$ for which
some ordering $S = \{\vec x_0, \dots, \vec x_{n-1}\}$ (`x : Fin n → ℤ × ℤ`, 0-based) satisfies
$\vec x_i \in \mathrm{MIN}(X \setminus \{\vec x_0, \dots, \vec x_{i-1}\})$ for each $0 \le i < n$.

*Deviation:* the source's set-builder reuses the letter $X$ for the members of
$\mathrm{MIN}_n(X)$; we rename the bound variable to $S$ (the removed sets
$X \setminus \{\dots\}$ use the outer $X$). The source takes $n \ge 1$; here $n = 0$ is allowed and
gives $\{\emptyset\}$ (needed for Corollary 3.19 with $n = 0$). -/
@[kb "hanke2023threeterm" "§3.3, Definition 3.16, p. 8"]
def MINn (n : ℕ) (X : Set (ℤ × ℤ)) : Set (Finset (ℤ × ℤ)) :=
  {S | (∀ v ∈ S, StronglyPrimitive v) ∧ S.card = n ∧
    ∃ x : Fin n → ℤ × ℤ, (∀ v, v ∈ S ↔ ∃ i, x i = v) ∧
      ∀ i : Fin n, x i ∈ MIN (X \ {y | ∃ j : Fin n, j < i ∧ x j = y})}

/-- **Remark 3.17 ($\mathrm{MIN}_1$ as $\mathrm{MIN}$).** For $X \subseteq
\widetilde{\mathbb{Z}^2_*}$ (strongly primitive vectors; needed because
$\mathrm{MIN}_n$ only contains sets of strongly primitive vectors),
$\mathrm{MIN}_1(X) = \{\{\vec x\} : \vec x \in \mathrm{MIN}(X)\}$. -/
@[kb "hanke2023threeterm" "§3.3, Remark 3.17, p. 8"]
theorem MINn_one {X : Set (ℤ × ℤ)} (hX : ∀ v ∈ X, StronglyPrimitive v) :
    MINn 1 X = {S | ∃ x ∈ MIN X, S = {x}} := by
  ext S
  constructor
  · rintro ⟨-, -, x, hS, hx⟩
    refine ⟨x 0, ?_, ?_⟩
    · have h0 := hx 0
      have : {y | ∃ j : Fin 1, j < 0 ∧ x j = y} = ∅ := by
        ext y; simp
      rw [this, Set.diff_empty] at h0
      exact h0
    · ext v
      rw [hS v, Finset.mem_singleton]
      constructor
      · rintro ⟨i, rfl⟩; rw [Subsingleton.elim i 0]
      · rintro rfl; exact ⟨0, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, by simp, fun _ => x, ?_, ?_⟩
    · intro v hv
      rw [Finset.mem_singleton.mp hv]; exact hX x hx.1
    · intro v; simp [eq_comm]
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simpa using hx

/-- **Corollary 3.19 ($\mathrm{MIN}_n$ and successive minima sequences).** Let
$(\vec x_i)_{i \ge 0}$ satisfy $\vec x_i \in \mathrm{MIN}(\widetilde{\mathbb{Z}^2_*} \setminus
\{\vec x_0, \dots, \vec x_{i-1}\})$ for all $i$ (the last property of Lemma 3.15; the successive
minima property is not used). Then for all $m, n \in \mathbb{N}$,
$\{\vec x_m, \dots, \vec x_{m+n-1}\} \in \mathrm{MIN}_n\big(\widetilde{\mathbb{Z}^2_*} \setminus
\{\vec x_0, \dots, \vec x_{m-1}\}\big)$.
(0-based version of the paper's $\{\vec x_{m+1}, \dots, \vec x_{m+n}\}$.) -/
@[kb "hanke2023threeterm" "§3.3, Corollary 3.19, p. 8"]
theorem minSeq_window_mem_MINn {x : ℕ → ℤ × ℤ}
    (hx : ∀ i, x i ∈ MIN (spSet \ (x '' Set.Iio i))) (m n : ℕ) :
    (by classical exact (Finset.range n).image (fun k => x (m + k)) : Finset (ℤ × ℤ)) ∈
      MINn n (spSet \ (x '' Set.Iio m)) := by
  classical
  have hinj : Function.Injective x := by
    have key : ∀ i j, i < j → x i ≠ x j := by
      intro i j hij h
      exact (hx j).1.2 ⟨i, hij, h⟩
    intro i j h
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact absurd h (key i j hij)
    · rfl
    · exact absurd h.symm (key j i hij)
  refine ⟨?_, ?_, fun k => x (m + k), ?_, ?_⟩
  · intro v hv
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hv
    exact (hx (m + k)).1.1
  · rw [Finset.card_image_of_injective _ (fun i j h => by simpa using hinj h)]
    simp
  · intro v
    simp only [Finset.mem_image, Finset.mem_range, Fin.exists_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
  · intro i
    have heq : (spSet \ (x '' Set.Iio m)) \ {y | ∃ j : Fin n, j < i ∧ x (m + j) = y} =
        spSet \ (x '' Set.Iio (m + i)) := by
      ext y
      simp only [Set.mem_diff, Set.mem_image, Set.mem_Iio, Set.mem_setOf_eq, not_exists, not_and]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1, fun k hk hky => ?_⟩
        by_cases hkm : k < m
        · exact h2 k hkm hky
        · have hi := i.2
          refine h3 ⟨k - m, by omega⟩ (Fin.mk_lt_of_lt_val (by show k - m < i.val; omega)) ?_
          show x (m + (k - m)) = y
          rw [Nat.add_sub_cancel' (not_lt.mp hkm)]; exact hky
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, fun k hk hky => h2 k (by omega) hky⟩, fun j hj hjy => ?_⟩
        have hj' : j.val < i.val := Fin.lt_def.mp hj
        exact h2 (m + j) (by omega) hjy
    rw [heq]
    exact hx (m + i)

/-! ### Definition 4.1, Lemmas 4.2 and 4.3 -/

/-- **Definition 4.1 (the K-set $K(X; X_1, \dots, X_k)$).** For $X \subseteq \mathbb{Z}^2$ and sets
$X_0, \dots, X_{k-1}$ (`Xs : Fin k → Set (ℤ × ℤ)`; 0-based; the paper requires them to be finite,
pairwise disjoint subsets of $X \subseteq \widetilde{\mathbb{Z}^2_*}$, which we state as hypotheses
of the theorems rather than in the definition): the set of $Q \in V$ such that for each $i$,
$Q(X_i) \in \{\emptyset, \{m_i\}\}$ where
$m_i = \min Q\big(X \setminus (X_0 \cup \dots \cup X_{i-1})\big)$ (`IsLeast`; when
$X_i = \emptyset$ the condition holds whether or not that minimum exists). -/
@[kb "hanke2023threeterm" "§4, Definition 4.1, p. 8"]
def Kset (X : Set (ℤ × ℤ)) {k : ℕ} (Xs : Fin k → Set (ℤ × ℤ)) : Set RForm :=
  {Q | Q ∈ domainV ∧ ∀ i : Fin k, Q.eval '' Xs i = ∅ ∨
    ∃ m : ℝ, IsLeast (Q.eval '' (X \ ⋃ j : Fin k, ⋃ (_ : j < i), Xs j)) m ∧
      Q.eval '' Xs i = {m}}

/-- **Lemma 4.2 (singleton K-set).** Let $\vec x_0, \dots, \vec x_{k-1}$ be pairwise distinct
(`hinj`, implicit in Definition 4.1's disjointness) vectors of $X \subseteq
\widetilde{\mathbb{Z}^2_*}$ (`hX`, `hxX`). Then
$$K(X; \{\vec x_0\}, \dots, \{\vec x_{k-1}\}) = \{Q \in V : Q(\vec x_0) \le \dots \le Q(\vec x_{k-1})
\le Q(\vec y) \ \forall \vec y \in \mathrm{MIN}(X \setminus \{\vec x_0, \dots, \vec x_{k-1}\})\}.$$
The chain is written `∀ i ≤ j, Q (x i) ≤ Q (x j)` and the last inequality is required for the
last index `i` (with `i + 1 = k`; vacuous for `k = 0`). That the right side is a polyhedral cone
is `kset_singleton_polyhedral`. -/
@[kb "hanke2023threeterm" "§4, Lemma 4.2, p. 8"]
theorem kset_singleton_eq {X : Set (ℤ × ℤ)} (hX : X ⊆ spSet) {k : ℕ} (x : Fin k → ℤ × ℤ)
    (hxX : ∀ i, x i ∈ X) (hinj : Function.Injective x) :
    Kset X (fun i => {x i}) =
      {Q | Q ∈ domainV ∧ (∀ i j : Fin k, i ≤ j → Q.eval (x i) ≤ Q.eval (x j)) ∧
        ∀ i : Fin k, i.val + 1 = k → ∀ y ∈ MIN (X \ Set.range x), Q.eval (x i) ≤ Q.eval y} := by
  ext Q
  constructor
  · rintro ⟨hV, hK⟩
    have hmin : ∀ i : Fin k, ∀ w ∈ X, (∀ j : Fin k, j < i → w ≠ x j) → Q.eval (x i) ≤ Q.eval w := by
      intro i w hw hne
      rcases hK i with h | ⟨m, hm, hm2⟩
      · simp at h
      · have : Q.eval (x i) = m := by
          have : Q.eval (x i) ∈ ({m} : Set ℝ) := by rw [← hm2]; exact ⟨x i, rfl, rfl⟩
          exact this
        rw [this]
        refine hm.2 ⟨w, ⟨hw, ?_⟩, rfl⟩
        simp only [Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, not_exists, not_and]
        exact fun j hj hwj => hne j hj hwj
    refine ⟨hV, fun i j hij => hmin i (x j) (hxX j) (fun l hl h => ?_), ?_⟩
    · have := hinj h
      subst this
      exact absurd hl (not_lt.mpr hij)
    · intro i hi y hy
      refine hmin i y hy.1.1 (fun l _ h => hy.1.2 ⟨l, h.symm⟩)
  · rintro ⟨hV, hchain, hlast⟩
    refine ⟨hV, fun i => Or.inr ⟨Q.eval (x i), ⟨⟨x i, ⟨hxX i, ?_⟩, rfl⟩, ?_⟩, by simp⟩⟩
    · simp only [Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, not_exists, not_and]
      intro j hj h
      exact absurd (hinj h) (ne_of_lt hj).symm
    · rintro _ ⟨w, ⟨hwX, hw⟩, rfl⟩
      simp only [Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, not_exists, not_and] at hw
      by_cases hwr : w ∈ Set.range x
      · obtain ⟨j, rfl⟩ := hwr
        refine hchain i j ?_
        by_contra hlt
        exact hw j (not_le.mp hlt) rfl
      · have hne : (X \ Set.range x).Nonempty := ⟨w, hwX, hwr⟩
        obtain ⟨m', hm1, hm2⟩ :=
          MIN_attains_min (X := X \ Set.range x) (fun v hv => hX hv.1) hne hV
        obtain ⟨y, hy, hym⟩ := hm2.1
        have hk : 0 < k := Nat.pos_of_ne_zero (by have := i.2; omega)
        have hl := hlast ⟨k - 1, by omega⟩ (by simp; omega) y hy
        have h1 : Q.eval (x i) ≤ Q.eval (x ⟨k - 1, by omega⟩) :=
          hchain i _ (by rw [Fin.le_def]; have := i.2; simp; omega)
        have h2 : m' ≤ Q.eval w := hm1.2 ⟨w, ⟨hwX, hwr⟩, rfl⟩
        linarith

/-- **Lemma 4.3 (general K-set).** Let $X_0, \dots, X_{k-1} \subseteq X$ be given by an enumeration
`z : Fin N → ℤ × ℤ` (injective, with values in $X$) cut into consecutive blocks by a weakly
increasing block map `b : Fin N → Fin k`: $X_i = \{z_t : b(t) = i\}$ (so each $X_i$ is finite and the
$X_i$ are pairwise disjoint). Then
$$K(X; X_0, \dots, X_{k-1}) = K'_{X; X_\bullet} \cap L_{X; X_\bullet},$$
where $K' = K(X; \{z_0\}, \dots, \{z_{N-1}\})$ is the singleton K-set of the enumeration and
$L = \{Q \in V : Q(z_s) = Q(z_t) \text{ whenever } b(s) = b(t)\}$.
This is Lemma 4.3 together with Remark 4.4: the enumeration need only list the blocks in
increasing order of $i$, with ties inside a block broken arbitrarily (the lexicographic order of the
statement is one such choice). Each of $K'$ (Lemma 4.2, `kset_singleton_eq`) and $L$ is a
polyhedral cone. -/
@[kb "hanke2023threeterm" "§4, Lemma 4.3, Remark 4.4, p. 9"]
theorem kset_general_eq {X : Set (ℤ × ℤ)} {k N : ℕ} (z : Fin N → ℤ × ℤ)
    (hz : Function.Injective z) (hzX : ∀ t, z t ∈ X) (b : Fin N → Fin k) (hb : Monotone b)
    (Xs : Fin k → Set (ℤ × ℤ)) (hXs : ∀ i, Xs i = z '' {t | b t = i}) :
    Kset X Xs = Kset X (fun t : Fin N => {z t}) ∩
      {Q | Q ∈ domainV ∧ ∀ s t, b s = b t → Q.eval (z s) = Q.eval (z t)} := by
  have memB : ∀ i w, w ∈ X \ (⋃ j : Fin k, ⋃ (_ : j < i), Xs j) ↔
      w ∈ X ∧ ∀ s, b s < i → w ≠ z s := by
    intro i w
    simp only [Set.mem_diff, Set.mem_iUnion, exists_prop, not_exists, not_and, hXs,
      Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun s hs hws => h2 (b s) hs s rfl hws.symm⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun j hj s hsj hsw => ?_⟩
      exact h2 s (hsj ▸ hj) hsw.symm
  have memT : ∀ t w, w ∈ X \ (⋃ s : Fin N, ⋃ (_ : s < t), ({z s} : Set (ℤ × ℤ))) ↔
      w ∈ X ∧ ∀ s, s < t → w ≠ z s := by
    intro t w
    simp only [Set.mem_diff, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, not_exists,
      not_and]
  ext Q
  constructor
  · rintro ⟨hV, hK⟩
    have hblock : ∀ t, ∃ m : ℝ, IsLeast (Q.eval '' (X \ ⋃ j : Fin k, ⋃ (_ : j < b t), Xs j)) m ∧
        ∀ s, b s = b t → Q.eval (z s) = m := by
      intro t
      rcases hK (b t) with h | ⟨m, hm, hm2⟩
      · exfalso
        have : Q.eval (z t) ∈ Q.eval '' Xs (b t) := ⟨z t, by rw [hXs]; exact ⟨t, rfl, rfl⟩, rfl⟩
        rw [h] at this; exact this
      · refine ⟨m, hm, fun s hs => ?_⟩
        have : Q.eval (z s) ∈ Q.eval '' Xs (b t) :=
          ⟨z s, by rw [hXs]; exact ⟨s, hs, rfl⟩, rfl⟩
        rw [hm2] at this; exact this
    refine ⟨⟨hV, fun t => Or.inr ?_⟩, hV, ?_⟩
    · obtain ⟨m, hm, hall⟩ := hblock t
      have hmt : Q.eval (z t) = m := hall t rfl
      refine ⟨m, ⟨⟨z t, ?_, hmt⟩, ?_⟩, by simp [hmt]⟩
      · rw [memT]
        exact ⟨hzX t, fun s hs h => absurd (hz h) (ne_of_lt hs).symm⟩
      · rintro _ ⟨w, hw, rfl⟩
        rw [memT] at hw
        refine hm.2 ⟨w, ?_, rfl⟩
        rw [memB]
        refine ⟨hw.1, fun s hs => hw.2 s ?_⟩
        by_contra hst
        exact absurd (hb (not_lt.mp hst)) (not_le.mpr hs)
    · intro s t hst
      obtain ⟨m, -, hall⟩ := hblock t
      rw [hall s hst, hall t rfl]
  · rintro ⟨⟨-, hK⟩, hV, hL⟩
    refine ⟨hV, fun i => ?_⟩
    by_cases hne : ∃ t, b t = i
    swap
    · left
      push Not at hne
      ext r
      simp only [Set.mem_image, hXs, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_exists, not_and]
      rintro w ⟨t, ht, rfl⟩
      exact absurd ht (hne t)
    · right
      obtain ⟨t, ht⟩ := hne
      obtain ⟨t0, ht0, hmin⟩ := wellFounded_lt.has_min {t | b t = i} ⟨t, ht⟩
      have ht0' : b t0 = i := ht0
      have hset : (X \ ⋃ j : Fin k, ⋃ (_ : j < i), Xs j) =
          X \ ⋃ s : Fin N, ⋃ (_ : s < t0), ({z s} : Set (ℤ × ℤ)) := by
        ext w
        rw [memB, memT]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun s hs => h2 s ?_⟩
          have h3 : b s ≤ b t0 := hb hs.le
          have h4 : b s ≠ i := fun h => hmin s h hs
          rw [ht0'] at h3
          exact lt_of_le_of_ne h3 h4
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun s hs => h2 s ?_⟩
          by_contra hst
          have := hb (not_lt.mp hst)
          rw [ht0'] at this
          exact absurd hs (not_lt.mpr this)
      rcases hK t0 with h | ⟨m, hm, hm2⟩
      · simp at h
      · have hmt : Q.eval (z t0) = m := by
          have : Q.eval (z t0) ∈ ({m} : Set ℝ) := by rw [← hm2]; exact ⟨z t0, rfl, rfl⟩
          exact this
        refine ⟨m, ?_, ?_⟩
        · rw [hset]; exact hm
        · ext r
          constructor
          · rintro ⟨w, hw, rfl⟩
            rw [hXs] at hw
            obtain ⟨s, hs, rfl⟩ := hw
            have : Q.eval (z s) = Q.eval (z t0) := hL s t0 (by rw [ht0']; exact hs)
            rw [this, hmt]; rfl
          · intro hr
            rw [Set.mem_singleton_iff] at hr
            exact ⟨z t0, by rw [hXs]; exact ⟨t0, ht0, rfl⟩, by rw [hmt, hr]⟩

/-- The coefficient vector $(v_0^2, v_1^2, v_0 v_1) \in \mathbb{R}^3$ of the evaluation
$Q \mapsto Q(\vec v) = q_{11} v_0^2 + q_{22} v_1^2 + q_{12} v_0 v_1$ at $\vec v = (v_0, v_1)$,
in the coordinates $(q_{11}, q_{22}, q_{12})$ of `RForm.toVec`. -/
def evalCoef (v : ℤ × ℤ) : Fin 3 → ℝ := ![(v.1 : ℝ) ^ 2, (v.2 : ℝ) ^ 2, (v.1 : ℝ) * v.2]

lemma evalCoef_dot (v : ℤ × ℤ) (Q : RForm) : evalCoef v ⬝ᵥ Q.toVec = Q.eval v := by
  simp [dotProduct, Fin.sum_univ_three, evalCoef, RForm.toVec, RForm.eval]
  ring

/-- **Lemma 4.2, polyhedral form.** In the situation of `kset_singleton_eq`, the singleton K-set
is a polyhedral cone (Definition 2.4) in the coordinates $(q_{11}, q_{22}, q_{12})$: there is a
finite set $A$ of vectors in $\mathbb{R}^3$ (the three inequalities defining $V$, the differences
`evalCoef (x j) - evalCoef (x i)` for $i \le j$, and `evalCoef y - evalCoef (x i)` for the last
index `i` and $\vec y \in \mathrm{MIN}(X \setminus \{\vec x_0, \dots\})$, finite by `MIN_finite`)
with $K = \{Q : (q_{11}, q_{22}, q_{12}) \in P(A, \{(1,0,0)\})\}$. -/
@[kb "hanke2023threeterm" "§4, Lemma 4.2, p. 8"]
theorem kset_singleton_polyhedral {X : Set (ℤ × ℤ)} (hX : X ⊆ spSet) {k : ℕ}
    (x : Fin k → ℤ × ℤ) (hxX : ∀ i, x i ∈ X) (hinj : Function.Injective x) :
    ∃ A : Finset (Fin 3 → ℝ),
      Kset X (fun i => {x i}) =
        RForm.toVec ⁻¹' polyhedralCone A ({![1, 0, 0]} : Finset (Fin 3 → ℝ)) := by
  classical
  have hfin := MIN_finite (X \ Set.range x)
  refine ⟨({![-1, 1, 0], ![1, 0, -1], ![0, 0, 1]} : Finset (Fin 3 → ℝ)) ∪
    ((Finset.univ.filter (fun p : Fin k × Fin k => p.1 ≤ p.2)).image
      (fun p => evalCoef (x p.2) - evalCoef (x p.1))) ∪
    (((Finset.univ.filter (fun i : Fin k => i.val + 1 = k)) ×ˢ hfin.toFinset).image
      (fun p => evalCoef p.2 - evalCoef (x p.1))), ?_⟩
  rw [kset_singleton_eq hX x hxX hinj]
  have hV := domainV_eq_polyhedralCone
  ext Q
  have hVQ : Q ∈ domainV ↔ (∀ a ∈ ({![-1, 1, 0], ![1, 0, -1], ![0, 0, 1]} : Finset (Fin 3 → ℝ)),
      0 ≤ a ⬝ᵥ Q.toVec) ∧ ∀ b ∈ ({![1, 0, 0]} : Finset (Fin 3 → ℝ)), 0 < b ⬝ᵥ Q.toVec := by
    rw [hV]; rfl
  simp only [Set.mem_preimage, polyhedralCone, Set.mem_setOf_eq, Finset.mem_union,
    Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
    Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨hQ, hchain, hlast⟩
    obtain ⟨hA, hB⟩ := hVQ.mp hQ
    refine ⟨?_, hB⟩
    rintro a ((ha | ⟨⟨i, j⟩, hij, rfl⟩) | ⟨⟨i, y⟩, ⟨hi, hy⟩, rfl⟩)
    · exact hA a ha
    · simp only [sub_dotProduct, evalCoef_dot]
      exact sub_nonneg.mpr (hchain i j hij)
    · simp only [sub_dotProduct, evalCoef_dot]
      exact sub_nonneg.mpr (hlast i hi y hy)
  · rintro ⟨hA, hB⟩
    refine ⟨hVQ.mpr ⟨fun a ha => hA a (Or.inl (Or.inl ha)), hB⟩, ?_, ?_⟩
    · intro i j hij
      have := hA _ (Or.inl (Or.inr ⟨(i, j), hij, rfl⟩))
      simp only [sub_dotProduct, evalCoef_dot] at this
      linarith
    · intro i hi y hy
      have := hA _ (Or.inr ⟨(i, y), ⟨hi, hy⟩, rfl⟩)
      simp only [sub_dotProduct, evalCoef_dot] at this
      linarith

/-! ### Definition 5.3, Remark 5.4, Definition 5.5 -/

/-- **Definition 5.3 (normalized rational 3-term linear relation).** Positive definite integral
binary forms $Q_1, Q_2, Q_3$ and rational $\beta_1, \beta_2 \ge 0$ satisfy the normalized relation
$\beta_1 \theta_{Q_1} + \beta_2 \theta_{Q_2} = \theta_{Q_3}$, as an identity of all
$q$-expansion coefficients: $\beta_1 r_{Q_1}(m) + \beta_2 r_{Q_2}(m) = r_{Q_3}(m)$ for all
$m \ge 0$. (The permutation $\sigma$ of the source only renames which of the three forms plays which
role, so it is built into the choice of $Q_1, Q_2, Q_3$. That every rational three-term relation
can be so normalized is not formalized here.) -/
@[kb "hanke2023threeterm" "§5.1, Definition 5.3, p. 9"]
def NormalizedRelation (Q₁ Q₂ Q₃ : BinQF) (β₁ β₂ : ℚ) : Prop :=
  IntQF.PosDef Q₁ ∧ IntQF.PosDef Q₂ ∧ IntQF.PosDef Q₃ ∧ 0 ≤ β₁ ∧ 0 ≤ β₂ ∧
    ∀ m : ℕ, (β₁ : ℝ) * repNum Q₁ m + (β₂ : ℝ) * repNum Q₂ m = repNum Q₃ m

/-- **Remark 5.4, constant term.** In a normalized relation $\beta_1 \theta_{Q_1} + \beta_2
\theta_{Q_2} = \theta_{Q_3}$ one has $\beta_1 + \beta_2 = 1$ (compare the constant terms
$r_{Q_i}(0) = 1$, `repNum_zero`). -/
@[kb "hanke2023threeterm" "§5.1, Remark 5.4, p. 9"]
theorem NormalizedRelation.sum_eq_one {Q₁ Q₂ Q₃ : BinQF} {β₁ β₂ : ℚ}
    (h : NormalizedRelation Q₁ Q₂ Q₃ β₁ β₂) : β₁ + β₂ = 1 := by
  obtain ⟨hp₁, hp₂, hp₃, -, -, hrel⟩ := h
  have := hrel 0
  simp only [Nat.cast_zero, Int.cast_zero, repNum_zero hp₁, repNum_zero hp₂,
    repNum_zero hp₃] at this
  have h' : ((β₁ + β₂ : ℚ) : ℝ) = 1 := by push_cast; simpa using this
  exact_mod_cast h'

/-- **Remark 5.4 (integral form of a normalized relation).** In a normalized relation
$\beta_1 \theta_{Q_1} + \beta_2 \theta_{Q_2} = \theta_{Q_3}$ there are $a, b, c \in \mathbb{Z}_{\ge 0}$
with $c > 0$, $\gcd(a, c) = \gcd(b, c) = 1$, $\beta_1 = a/c$, $\beta_2 = b/c$ and $c = a + b$. -/
@[kb "hanke2023threeterm" "§5.1, Remark 5.4, p. 9"]
theorem NormalizedRelation.integral_form {Q₁ Q₂ Q₃ : BinQF} {β₁ β₂ : ℚ}
    (h : NormalizedRelation Q₁ Q₂ Q₃ β₁ β₂) :
    ∃ a b c : ℕ, 0 < c ∧ Nat.gcd a c = 1 ∧ Nat.gcd b c = 1 ∧
      β₁ = (a : ℚ) / c ∧ β₂ = (b : ℚ) / c ∧ c = a + b := by
  have hs := h.sum_eq_one
  obtain ⟨-, -, -, h1, h2, -⟩ := h
  have hle : β₁ ≤ 1 := by linarith
  have hnum : 0 ≤ β₁.num := Rat.num_nonneg.mpr h1
  set c := β₁.den with hc
  set a := β₁.num.toNat with ha
  have hac : (a : ℤ) = β₁.num := Int.toNat_of_nonneg hnum
  have hcpos : 0 < c := β₁.den_pos
  have hβ : β₁ = (a : ℚ) / c := by
    have := Rat.num_div_den β₁
    rw [← this]
    simp only [← hc]
    congr 1
    exact_mod_cast hac.symm
  have hale : a ≤ c := by
    have : (a : ℚ) ≤ c := by
      rw [hβ, div_le_one (by exact_mod_cast hcpos)] at hle
      exact hle
    exact_mod_cast this
  have hcop : Nat.Coprime a c := by
    have h0 := β₁.reduced
    have e : β₁.num.natAbs = a := by rw [ha]; omega
    rwa [e] at h0
  refine ⟨a, c - a, c, hcpos, hcop, ?_, hβ, ?_, by omega⟩
  · have h3 : Nat.Coprime a (c - a) := (Nat.coprime_sub_self_right hale).mpr hcop
    have h4 : Nat.Coprime (c - a) (a + (c - a)) := Nat.coprime_add_self_right.mpr h3.symm
    rwa [Nat.add_sub_cancel' hale] at h4
  · have : β₂ = 1 - β₁ := by linarith
    rw [this, hβ]
    have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hcpos.ne'
    rw [Nat.cast_sub hale]
    field_simp

/-- **Definition 5.5 (solution set $D_{a,b}$).** For $a, b \in \mathbb{Z}_{\ge 0}$ with
$a + b > 0$: the set of triples $(Q_1, Q_2, Q_3) \in V \times V \times V$ for which equation (6),
$\frac{a}{a+b}\theta_{Q_1} + \frac{b}{a+b}\theta_{Q_2} = \theta_{Q_3}$, holds. Since theta series
are only defined here for integral forms, a triple of real forms belongs to $D_{a,b}$ when each
$Q_i$ is the triple `toRForm f_i` of an integral binary form $f_i$ and the coefficientwise identity
$\frac{a}{a+b} r_{f_1}(m) + \frac{b}{a+b} r_{f_2}(m) = r_{f_3}(m)$ holds for all $m \ge 0$. -/
@[kb "hanke2023threeterm" "§5.1, Definition 5.5, p. 10"]
def Dab (a b : ℕ) : Set (RForm × RForm × RForm) :=
  {T | T.1 ∈ domainV ∧ T.2.1 ∈ domainV ∧ T.2.2 ∈ domainV ∧
    ∃ f₁ f₂ f₃ : BinQF, toRForm f₁ = T.1 ∧ toRForm f₂ = T.2.1 ∧ toRForm f₃ = T.2.2 ∧
      ∀ m : ℕ, (a : ℝ) / (a + b) * repNum f₁ m + (b : ℝ) / (a + b) * repNum f₂ m = repNum f₃ m}

/-- **Definition 5.5 (diagonal $\Delta$).** $\Delta = \{(Q_1, Q_2, Q_3) \in V \times V \times V :
Q_1 = Q_2 = Q_3\}$.

*Deviation:* the source asserts $\Delta \subseteq D_{a,b}$, which only makes sense for integral
forms (theta series of non-integral real forms are not defined here); see
`diagonal_integral_subset_Dab` for the precise statement. -/
@[kb "hanke2023threeterm" "§5.1, Definition 5.5, p. 10"]
def diagonalΔ : Set (RForm × RForm × RForm) :=
  {T | T.1 ∈ domainV ∧ T.2.1 ∈ domainV ∧ T.2.2 ∈ domainV ∧ T.1 = T.2.1 ∧ T.2.1 = T.2.2}

/-- **Definition 5.5, $\Delta \subseteq D_{a,b}$ for integral forms.** If $a + b > 0$, every
diagonal triple $(Q, Q, Q)$ with $Q \in V$ the triple of an integral binary form lies in
$D_{a,b}$. -/
@[kb "hanke2023threeterm" "§5.1, Definition 5.5, p. 10"]
theorem diagonal_integral_subset_Dab {a b : ℕ} (hab : a + b ≠ 0) {T : RForm × RForm × RForm}
    (hT : T ∈ diagonalΔ) (hint : ∃ f : BinQF, toRForm f = T.1) : T ∈ Dab a b := by
  obtain ⟨h1, h2, h3, e1, e2⟩ := hT
  obtain ⟨f, hf⟩ := hint
  refine ⟨h1, h2, h3, f, f, f, hf, e1 ▸ hf, (e1.trans e2) ▸ hf, fun m => ?_⟩
  have h : ((a : ℝ) + b) ≠ 0 := by exact_mod_cast hab
  field_simp

/-! ### Remark 5.8 -/

/-- **Remark 5.8, case $a = 0$ or $b = 0$.** If $(a, b) \ne (0, 0)$ and $a = 0$ or $b = 0$, then
$L_{a,b} = [L_1, L_2, L_3]$ with $L_1 = L_2 + L_3$, so $\{L_1, L_2, L_3\}$ is not a minimal set of
generators of $\mathbb{Z}_{\ge 0}[L_{a,b}]$ ($L_1$ is redundant; $\{L_2, L_3\}$ generates). -/
@[kb "hanke2023threeterm" "§5.2, Remark 5.8, p. 11"]
theorem linset_dependent {a b : ℕ} (hab : a + b ≠ 0) (h : a = 0 ∨ b = 0) :
    ∃ L₁ L₂ L₃ : ℕ × ℕ × ℕ, linset a b = [L₁, L₂, L₃] ∧ L₁ = L₂ + L₃ := by
  refine ⟨(1, 1, 1), _, _, rfl, ?_⟩
  rcases h with rfl | rfl
  · have hb : b ≠ 0 := by omega
    simp [linset, Nat.div_self (Nat.pos_of_ne_zero hb)]
  · have ha : a ≠ 0 := by omega
    simp [linset, Nat.div_self (Nat.pos_of_ne_zero ha)]

/-- **Remark 5.8, case $a \ne 0$, $b \ne 0$.** Then $L_{a,b} = [L_1, L_2, L_3]$ and none of the
three vectors is a $\mathbb{Z}_{\ge 0}$-combination of the other two. Hence dropping any one of them
strictly shrinks $\mathbb{Z}_{\ge 0}[L_{a,b}]$, i.e. $\{L_1, L_2, L_3\}$ is a minimal set of
generators. -/
@[kb "hanke2023threeterm" "§5.2, Remark 5.8, p. 11"]
theorem linset_irredundant {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ L₁ L₂ L₃ : ℕ × ℕ × ℕ, linset a b = [L₁, L₂, L₃] ∧
      (∀ c d : ℕ, L₁ ≠ c • L₂ + d • L₃) ∧ (∀ c d : ℕ, L₂ ≠ c • L₁ + d • L₃) ∧
      (∀ c d : ℕ, L₃ ≠ c • L₁ + d • L₂) := by
  obtain ⟨p, hp⟩ := Nat.gcd_dvd_left a b
  obtain ⟨q, hq⟩ := Nat.gcd_dvd_right a b
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero ha)
  have hp0 : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h] at hp; omega
    · exact h
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h] at hq; omega
    · exact h
  have e1 : a / Nat.gcd a b = p := Nat.div_eq_of_eq_mul_right hg hp
  have e2 : b / Nat.gcd a b = q := Nat.div_eq_of_eq_mul_right hg hq
  have e3 : (a + b) / Nat.gcd a b = p + q := by
    have : a + b = Nat.gcd a b * (p + q) := by rw [mul_add, ← hp, ← hq]
    exact Nat.div_eq_of_eq_mul_right hg this
  refine ⟨(1, 1, 1), (p + q, 0, p), (0, p + q, q), by simp [linset, e1, e2, e3], ?_, ?_, ?_⟩
  · intro c d h
    have h1 := congrArg Prod.fst h
    simp at h1
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp at h1
    · nlinarith
  · intro c d h
    have h1 := congrArg (fun v => v.2.1) h
    have h2 := congrArg Prod.fst h
    simp at h1 h2
    nlinarith
  · intro c d h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg (fun v => v.2.1) h
    simp at h1 h2
    nlinarith

end QuadFormsKB.Hanke2023ThreeTerm
