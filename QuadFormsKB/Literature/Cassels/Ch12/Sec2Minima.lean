/-
# Cassels, Chapter 12, §2: successive minima, Lemma 2.1 and Theorem 2.2

Cassels, *Rational Quadratic Forms* (1978), Ch. 12, §2, pp. 262–263.

* The successive minima $M_0 \le \dots \le M_{n-1}$ (`succMin`, Definition p. 262), (2.3)–(2.4), Lemma 2.1.
* Theorem 2.2 (`prod_succMin_le`): $M_0M_1\cdots M_{n-1} \le \gamma_n^n D$ (Minkowski).

Indices are 0-based: Cassels' $M_1, \dots, M_n$ and $m_1, \dots, m_n$ are $M_0, \dots, M_{n-1}$ and
$\vec{m}_0, \dots, \vec{m}_{n-1}$ here, so "$M_j$ is the least $M$ for which $\{f(\vec{m}) \le M\}$ spans a space of
dimension $\ge j$" reads "$M_j$ is the least $M$ for which it spans a space of dimension $\ge j+1$".
-/
import QuadFormsKB.Literature.Cassels.Ch12.Sec2

open Matrix

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-- **The real span of the integral vectors in $\{f \le M\}$**: the subspace of $\mathbb{R}^n$ spanned by the
$\vec{m} \in \mathbb{Z}^n$ with $f(\vec{m}) \le M$. -/
def spanLE (F : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ (cast '' {m | val F (cast m) ≤ M})

/-- **The real span of the integral vectors in $\{f < M\}$.** -/
def spanLT (F : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ (cast '' {m | val F (cast m) < M})

/-- **The $j$-th successive minimum** $M_j$ of a strictly positive definite real form (Cassels, Ch. 12, §2, Definition,
p. 262; his $M_{j+1}$, 0-based here): the least real $M$ such that the integral vectors $\vec{m}$ with
$f(\vec{m}) \le M$ span a subspace of $\mathbb{R}^n$ of dimension $\ge j + 1$:
$$M_j = \inf\{M \in \mathbb{R} : \dim \mathrm{span}_{\mathbb{R}}\{\vec{m} \in \mathbb{Z}^n : f(\vec{m}) \le M\} \ge j+1\}.$$
Cassels defines $M_j$ by the two conditions (i) $\{f(\vec{m}) \le M_j\}$ spans dimension $\ge j+1$ and (ii)
$\{f(\vec{m}) < M_j\}$ spans dimension $< j + 1$; this infimum satisfies both (`succMin_spec`) and is the only number
that does (`succMin_unique`). For a form that is not strictly positive definite the value is meaningless (the set may
be empty or unbounded below; Mathlib's `sInf` then returns $0$ or a junk value). -/
@[kb "cassels1978" "Ch. 12, §2, Definition (successive minima), p. 262"]
noncomputable def succMin (F : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : ℝ :=
  sInf {M : ℝ | j.val + 1 ≤ Module.finrank ℝ (spanLE F M)}

/-- Helper: the real span of the first `k` vectors `cast (g i)`, `i < k`. -/
private abbrev headSpan (g : Fin n → Fin n → ℤ) (k : ℕ) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ ((fun i => cast (g i)) '' {i : Fin n | i.val < k})

/-- Helper: vectors not in the span of their predecessors are linearly independent. -/
private theorem linearIndependent_of_notMem_head {v : Fin n → Fin n → ℝ}
    (h : ∀ j : Fin n, v j ∉ Submodule.span ℝ (v '' {i : Fin n | i < j})) : LinearIndependent ℝ v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  obtain ⟨i0, hi0⟩ := hne
  set S : Finset (Fin n) := Finset.univ.filter fun i => c i ≠ 0 with hS
  have hSne : S.Nonempty := ⟨i0, by simp [hS, hi0]⟩
  set J := S.max' hSne with hJ
  have hJS : c J ≠ 0 := by
    have := S.max'_mem hSne
    simpa [hS] using this
  have hgt : ∀ i, J < i → c i = 0 := by
    intro i hi
    by_contra hci
    have : i ∈ S := by simp [hS, hci]
    exact absurd (S.le_max' i this) (not_le.2 hi)
  have hsplit : ∑ i, c i • v i = c J • v J + ∑ i ∈ Finset.univ.filter (· < J), c i • v i := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ J)]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase J) (· < J)]
    have h1 : ∑ i ∈ (Finset.univ.erase J).filter (¬ · < J), c i • v i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_erase] at hi
      have : J < i := lt_of_le_of_ne (not_lt.1 hi.2) (Ne.symm hi.1.1)
      simp [hgt i this]
    rw [h1, add_zero]
    apply Finset.sum_congr
    · ext i
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      exact ⟨fun h => h.2, fun h => ⟨ne_of_lt h, h⟩⟩
    · intros; rfl
  apply h J
  have hvJ : v J = -(c J)⁻¹ • ∑ i ∈ Finset.univ.filter (· < J), c i • v i := by
    rw [hsplit] at hc
    have : c J • v J = -∑ i ∈ Finset.univ.filter (· < J), c i • v i := eq_neg_of_add_eq_zero_left hc
    calc v J = (c J)⁻¹ • (c J • v J) := by rw [smul_smul, inv_mul_cancel₀ hJS, one_smul]
      _ = _ := by rw [this, smul_neg, neg_smul]
  rw [hvJ]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_)
  exact Submodule.subset_span ⟨i, (Finset.mem_filter.1 hi).2, rfl⟩

/-- Helper: the span of the first `k` vectors has dimension at most `k`. -/
private theorem finrank_headSpan_le (g : Fin n → Fin n → ℤ) (k : ℕ) :
    Module.finrank ℝ (headSpan g k) ≤ k := by
  classical
  have h1 : (fun i => cast (g i)) '' {i : Fin n | i.val < k} =
      Set.range (fun i : {i : Fin n // i.val < k} => (cast (g i.1) : Fin n → ℝ)) := by
    ext x; simp
  unfold headSpan
  rw [h1]
  refine (finrank_range_le_card _).trans ?_
  rw [Fintype.card_subtype]
  calc (Finset.univ.filter fun i : Fin n => i.val < k).card
      ≤ (Finset.range k).card := by
        apply Finset.card_le_card_of_injOn (fun i => i.val)
        · intro i hi
          simpa using (Finset.mem_filter.1 hi).2
        · intro a _ b _ h; exact Fin.ext h
    _ = k := Finset.card_range k

/-- Helper: when `k < n` some integral vector lies outside the span of the first `k` vectors. -/
private theorem exists_notMem_headSpan (g : Fin n → Fin n → ℤ) {k : ℕ} (hk : k < n) :
    ∃ c : Fin n → ℤ, cast c ∉ headSpan g k := by
  by_contra hcon
  push Not at hcon
  have hle : (⊤ : Submodule ℝ (Fin n → ℝ)) ≤ headSpan g k := by
    rw [← (Pi.basisFun ℝ (Fin n)).span_eq]
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : Pi.basisFun ℝ (Fin n) i = cast (Pi.single i (1 : ℤ) : Fin n → ℤ) := by
      ext j; by_cases h : j = i <;> simp [h, cast]
    rw [this]
    exact hcon _
  have h1 : Module.finrank ℝ (⊤ : Submodule ℝ (Fin n → ℝ)) ≤ Module.finrank ℝ (headSpan g k) :=
    Submodule.finrank_mono hle
  rw [finrank_top] at h1
  have := finrank_headSpan_le g k
  simp at h1
  omega

/-- Helper: the greedy property of a sequence of integral vectors: `g j` has minimal value among the integral
vectors outside the span of `g 0, …, g (j-1)` (and is itself outside it). -/
private def IsGreedy (F : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → Fin n → ℤ) : Prop :=
  ∀ j : Fin n, cast (g j) ∉ headSpan g j.val ∧
    ∀ c : Fin n → ℤ, cast c ∉ headSpan g j.val → val F (cast (g j)) ≤ val F (cast c)

/-- Helper: a minimizer of `val F` over the integral vectors outside a given subspace. -/
private theorem exists_min_notMem {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef)
    (W : Submodule ℝ (Fin n → ℝ)) (hW : ∃ c : Fin n → ℤ, cast c ∉ W) :
    ∃ a : Fin n → ℤ, cast a ∉ W ∧ ∀ c : Fin n → ℤ, cast c ∉ W → val F (cast a) ≤ val F (cast c) := by
  obtain ⟨c0, hc0⟩ := hW
  obtain ⟨a, ha, hmin⟩ := Set.exists_min_image
    ({c : Fin n → ℤ | cast c ∉ W} ∩ {c | val F (cast c) ≤ val F (cast c0)}) (fun c => val F (cast c))
    ((finite_val_le hF _).subset Set.inter_subset_right) ⟨c0, ⟨hc0, (le_refl (val F (cast c0)) : _)⟩⟩
  refine ⟨a, ha.1, fun c hc => ?_⟩
  by_cases h : val F (cast c) ≤ val F (cast c0)
  · exact hmin c ⟨hc, h⟩
  · exact (ha.2.trans (not_le.1 h).le)

/-- Helper: the headSpan of `Function.update g j0 a` agrees with that of `g` up to index `j0`. -/
private theorem headSpan_update (g : Fin n → Fin n → ℤ) (j0 : Fin n) (a : Fin n → ℤ) {k : ℕ}
    (hk : k ≤ j0.val) : headSpan (Function.update g j0 a) k = headSpan g k := by
  unfold headSpan
  congr 1
  apply Set.image_congr
  intro i hi
  have : i ≠ j0 := fun h => by
    have : i.val < k := hi
    rw [h] at this; omega
  simp [Function.update_of_ne this]

/-- Helper: existence of a greedy sequence. -/
private theorem exists_greedy {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) : ∃ g, IsGreedy F g := by
  have key : ∀ k, k ≤ n → ∃ g : Fin n → Fin n → ℤ, ∀ j : Fin n, j.val < k →
      cast (g j) ∉ headSpan g j.val ∧
        ∀ c : Fin n → ℤ, cast c ∉ headSpan g j.val → val F (cast (g j)) ≤ val F (cast c) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨fun _ => 0, fun j hj => absurd hj (by omega)⟩
    | succ k ih =>
      intro hk
      obtain ⟨g, hg⟩ := ih (by omega)
      set j0 : Fin n := ⟨k, by omega⟩ with hj0
      obtain ⟨a, ha, hmin⟩ := exists_min_notMem hF (headSpan g k)
        (exists_notMem_headSpan g (by omega))
      refine ⟨Function.update g j0 a, fun j hj => ?_⟩
      by_cases hjk : j = j0
      · rw [hjk]
        have e : headSpan (Function.update g j0 a) j0.val = headSpan g k :=
          headSpan_update g j0 a (by simp [hj0])
        rw [e, Function.update_self]
        refine ⟨ha, fun c hc => ?_⟩
        exact hmin c hc
      · have hjk' : j.val < k := by
          have : j.val ≠ k := fun h => hjk (Fin.ext h)
          omega
        have e : headSpan (Function.update g j0 a) j.val = headSpan g j.val :=
          headSpan_update g j0 a (by simp [hj0]; omega)
        rw [e, Function.update_of_ne hjk]
        exact hg j hjk'
  obtain ⟨g, hg⟩ := key n le_rfl
  exact ⟨g, fun j => hg j j.2⟩

/-- Helper: a greedy sequence is linearly independent. -/
private theorem IsGreedy.linearIndependent {F : Matrix (Fin n) (Fin n) ℝ} {g : Fin n → Fin n → ℤ}
    (hg : IsGreedy F g) : LinearIndependent ℝ (fun j => cast (g j)) :=
  linearIndependent_of_notMem_head fun j => (hg j).1

/-- Helper: `headSpan` is monotone in the number of vectors. -/
private theorem headSpan_mono (g : Fin n → Fin n → ℤ) {k l : ℕ} (h : k ≤ l) :
    headSpan g k ≤ headSpan g l :=
  Submodule.span_mono (Set.image_mono fun i (hi : i.val < k) => (show i.val < l by omega))

/-- Helper: the values along a greedy sequence are monotone. -/
private theorem IsGreedy.mono {F : Matrix (Fin n) (Fin n) ℝ} {g : Fin n → Fin n → ℤ}
    (hg : IsGreedy F g) {i j : Fin n} (hij : i ≤ j) : val F (cast (g i)) ≤ val F (cast (g j)) := by
  rcases hij.eq_or_lt with rfl | h
  · exact le_rfl
  · refine (hg i).2 _ fun hmem => (hg j).1 ?_
    exact headSpan_mono g (show i.val ≤ j.val from h.le) hmem

/-- Helper (key fact (K)): an integral vector of smaller value than `g j` lies in the span of the earlier ones. -/
private theorem IsGreedy.mem_headSpan {F : Matrix (Fin n) (Fin n) ℝ} {g : Fin n → Fin n → ℤ}
    (hg : IsGreedy F g) {j : Fin n} {c : Fin n → ℤ} (hc : val F (cast c) < val F (cast (g j))) :
    cast c ∈ headSpan g j.val := by
  by_contra h
  exact absurd ((hg j).2 c h) (not_le.2 hc)

/-- Helper: the values along a greedy sequence are positive. -/
private theorem IsGreedy.pos {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) {g : Fin n → Fin n → ℤ}
    (hg : IsGreedy F g) (j : Fin n) : 0 < val F (cast (g j)) := by
  refine ((posDef_iff F).1 hF).2 _ fun h0 => (hg j).1 ?_
  rw [h0]; exact Submodule.zero_mem _

/-- Helper: the span of `g 0, …, g j` has dimension at least `j + 1`; it lies in `spanLE F M` (resp. `spanLT F M`)
once `val g_j ≤ M` (resp. `<`). -/
private theorem IsGreedy.finrank_le_span {F : Matrix (Fin n) (Fin n) ℝ} {g : Fin n → Fin n → ℤ}
    (hg : IsGreedy F g) (j : Fin n) {S : Submodule ℝ (Fin n → ℝ)}
    (hS : ∀ i : Fin n, i ≤ j → cast (g i) ∈ S) : j.val + 1 ≤ Module.finrank ℝ S := by
  classical
  have hli : LinearIndependent ℝ (fun i : {i : Fin n // i ≤ j} => (cast (g i.1) : Fin n → ℝ)) :=
    hg.linearIndependent.comp _ Subtype.val_injective
  have h1 := finrank_span_eq_card hli
  have h2 : Submodule.span ℝ (Set.range (fun i : {i : Fin n // i ≤ j} => (cast (g i.1) : Fin n → ℝ))) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hS i.1 i.2
  have h3 := Submodule.finrank_mono h2
  rw [h1] at h3
  refine le_trans ?_ h3
  have : Fintype.card (Fin (j.val + 1)) ≤ Fintype.card {i : Fin n // i ≤ j} :=
    Fintype.card_le_of_injective (fun t => ⟨⟨t.val, by omega⟩, Fin.mk_le_of_le_val (by omega)⟩)
      (fun a b h => by simpa [Fin.ext_iff] using h)
  simpa using this

/-- Helper: for a greedy sequence, `M_j = f(g_j)`. -/
private theorem IsGreedy.succMin_eq {F : Matrix (Fin n) (Fin n) ℝ} {g : Fin n → Fin n → ℤ}
    (hg : IsGreedy F g) (j : Fin n) : succMin F j = val F (cast (g j)) := by
  apply IsLeast.csInf_eq
  constructor
  · show j.val + 1 ≤ Module.finrank ℝ (spanLE F (val F (cast (g j))))
    refine hg.finrank_le_span j fun i hi => Submodule.subset_span ⟨g i, ?_, rfl⟩
    exact hg.mono hi
  · intro M hM
    by_contra hlt
    push Not at hlt
    have hle : spanLE F M ≤ headSpan g j.val := by
      unfold spanLE
      rw [Submodule.span_le]
      rintro _ ⟨c, hc, rfl⟩
      exact hg.mem_headSpan (lt_of_le_of_lt hc hlt)
    have := (Submodule.finrank_mono hle).trans (finrank_headSpan_le g j.val)
    have hM' : j.val + 1 ≤ Module.finrank ℝ (spanLE F M) := hM
    omega

/-- Helper: `M_j` is a lower bound for the `M` with `spanLE F M` of dimension `≥ j+1`. -/
private theorem IsGreedy.le_of_finrank {F : Matrix (Fin n) (Fin n) ℝ} {g : Fin n → Fin n → ℤ}
    (hg : IsGreedy F g) {j : Fin n} {M : ℝ} (hM : j.val + 1 ≤ Module.finrank ℝ (spanLE F M)) :
    val F (cast (g j)) ≤ M := by
  by_contra hlt
  push Not at hlt
  have hle : spanLE F M ≤ headSpan g j.val := by
    unfold spanLE
    rw [Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    exact hg.mem_headSpan (lt_of_le_of_lt hc hlt)
  have := (Submodule.finrank_mono hle).trans (finrank_headSpan_le g j.val)
  omega

/-- Helper: any independent family of `k ≤ n` vectors `cast (m i)` lying in `S` forces `k ≤ dim S`. -/
private theorem finrank_ge_of_head {m : Fin n → Fin n → ℤ} (hm : LinearIndependent ℝ (fun j => cast (m j)))
    {k : ℕ} (hk : k ≤ n) {S : Submodule ℝ (Fin n → ℝ)} (hS : ∀ i : Fin n, i.val < k → cast (m i) ∈ S) :
    k ≤ Module.finrank ℝ S := by
  classical
  have hli : LinearIndependent ℝ (fun i : {i : Fin n // i.val < k} => (cast (m i.1) : Fin n → ℝ)) :=
    hm.comp _ Subtype.val_injective
  have h1 := finrank_span_eq_card hli
  have h2 : Submodule.span ℝ (Set.range (fun i : {i : Fin n // i.val < k} => (cast (m i.1) : Fin n → ℝ))) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hS i.1 i.2
  have h3 := Submodule.finrank_mono h2
  rw [h1] at h3
  refine le_trans ?_ h3
  have : Fintype.card (Fin k) ≤ Fintype.card {i : Fin n // i.val < k} :=
    Fintype.card_le_of_injective (fun t => ⟨⟨t.val, by omega⟩, t.2⟩)
      (fun a b h => by simpa [Fin.ext_iff] using h)
  simpa using this

/-- **The defining properties** (Cassels, Ch. 12, Definition, p. 262): for strictly positive definite $F$,
(i) the integral $\vec{m}$ with $f(\vec{m}) \le M_j$ span a subspace of dimension $\ge j + 1$, and (ii) those with
$f(\vec{m}) < M_j$ span a subspace of dimension $\le j$. -/
@[kb "cassels1978" "Ch. 12, §2, Definition (successive minima), p. 262"]
theorem succMin_spec {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) (j : Fin n) :
    j.val + 1 ≤ Module.finrank ℝ (spanLE F (succMin F j)) ∧
      Module.finrank ℝ (spanLT F (succMin F j)) ≤ j.val := by
  obtain ⟨g, hg⟩ := exists_greedy hF
  rw [hg.succMin_eq j]
  refine ⟨hg.finrank_le_span j fun i hi => Submodule.subset_span ⟨g i, hg.mono hi, rfl⟩, ?_⟩
  have hle : spanLT F (val F (cast (g j))) ≤ headSpan g j.val := by
    unfold spanLT
    rw [Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    exact hg.mem_headSpan hc
  exact (Submodule.finrank_mono hle).trans (finrank_headSpan_le g j.val)

/-- **$M_j$ is well defined** (Cassels, Ch. 12, p. 262, "it is clear that $M_1, \dots, M_n$ are well defined"): a real
$M$ satisfying (i) and (ii) of the definition equals $M_j$. -/
@[kb "cassels1978" "Ch. 12, §2, p. 262 (the M_j are well defined)"]
theorem succMin_unique {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) (j : Fin n) {M : ℝ}
    (h1 : j.val + 1 ≤ Module.finrank ℝ (spanLE F M)) (h2 : Module.finrank ℝ (spanLT F M) ≤ j.val) :
    M = succMin F j := by
  obtain ⟨g, hg⟩ := exists_greedy hF
  rw [hg.succMin_eq j]
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    have := hg.finrank_le_span j (S := spanLT F M) fun i hi =>
      Submodule.subset_span ⟨g i, lt_of_le_of_lt (hg.mono hi) hlt, rfl⟩
    omega
  · exact hg.le_of_finrank h1

/-- **(2.3)** (Cassels, Ch. 12, p. 262): $0 < M_0 \le M_1 \le \dots \le M_{n-1}$. -/
@[kb "cassels1978" "Ch. 12, §2, (2.3), p. 262"]
theorem succMin_pos {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) (j : Fin n) : 0 < succMin F j := by
  obtain ⟨g, hg⟩ := exists_greedy hF
  rw [hg.succMin_eq j]
  exact hg.pos hF j

@[kb "cassels1978" "Ch. 12, §2, (2.3), p. 262"]
theorem succMin_mono {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) {i j : Fin n} (hij : i ≤ j) :
    succMin F i ≤ succMin F j := by
  obtain ⟨g, hg⟩ := exists_greedy hF
  rw [hg.succMin_eq i, hg.succMin_eq j]
  exact hg.mono hij

/-- **$M_0$ is the minimum** $\min_{\vec{m} \in \mathbb{Z}^n \setminus 0} f(\vec{m})$ (Cassels, Ch. 12, Thm. 2.1, p. 260,
where $M_1$ is defined this way, and p. 262): it is a value of $f$ at a nonzero integral vector and
$f(\vec{m}) \ge M_0$ for all nonzero integral $\vec{m}$. -/
@[kb "cassels1978" "Ch. 12, §2, Thm. 2.1 (M_1 = inf f(m)), p. 260; Definition, p. 262"]
theorem succMin_zero_spec {F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hF : F.PosDef) :
    (∃ m : Fin (n + 1) → ℤ, m ≠ 0 ∧ val F (cast m) = succMin F 0) ∧
      ∀ m : Fin (n + 1) → ℤ, m ≠ 0 → succMin F 0 ≤ val F (cast m) := by
  obtain ⟨g, hg⟩ := exists_greedy hF
  have h0 : headSpan g (0 : Fin (n + 1)).val = ⊥ := by simp [headSpan]
  rw [hg.succMin_eq 0]
  refine ⟨⟨g 0, fun h => (hg 0).1 ?_, rfl⟩, fun m hm => (hg 0).2 m ?_⟩
  · rw [h0, Submodule.mem_bot]; funext i; simp [h, cast]
  · rw [h0, Submodule.mem_bot]
    intro h
    apply hm
    funext i
    simpa [cast] using congrFun h i

/-- **(2.4)** (Cassels, Ch. 12, p. 262): there are integral vectors $\vec{m}_0, \dots, \vec{m}_{n-1}$, linearly independent
over $\mathbb{R}$, with $f(\vec{m}_j) = M_j$. -/
@[kb "cassels1978" "Ch. 12, §2, (2.4), p. 262"]
theorem exists_succMin_vectors {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) :
    ∃ m : Fin n → Fin n → ℤ, LinearIndependent ℝ (fun j => cast (m j)) ∧
      ∀ j, val F (cast (m j)) = succMin F j := by
  obtain ⟨g, hg⟩ := exists_greedy hF
  exact ⟨g, hg.linearIndependent, fun j => (hg.succMin_eq j).symm⟩

/-- **Lemma 2.1** (Cassels, Ch. 12, p. 262): let $\vec{m}_0, \dots, \vec{m}_{n-1}$ be any linearly independent integral
vectors with $f(\vec{m}_j) = M_j$. If $\vec{c}$ is integral and $f(\vec{c}) < M_j$, then $\vec{c}$ is a linear combination
of $\vec{m}_0, \dots, \vec{m}_{j-1}$ (over $\mathbb{R}$). -/
@[kb "cassels1978" "Ch. 12, §2, Lemma 2.1, p. 262"]
theorem mem_span_of_val_lt_succMin {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) {m : Fin n → Fin n → ℤ}
    (hm : LinearIndependent ℝ (fun j => cast (m j))) (hmM : ∀ j, val F (cast (m j)) = succMin F j)
    {j : Fin n} {c : Fin n → ℤ} (hc : val F (cast c) < succMin F j) :
    cast c ∈ Submodule.span ℝ (Set.image (fun i => cast (m i)) {i | i < j}) := by
  classical
  have hex : ∃ k, ∃ h : k < n, succMin F ⟨k, h⟩ = succMin F j := ⟨j.val, j.2, rfl⟩
  obtain ⟨hkn, hkM⟩ := Nat.find_spec hex
  set k := Nat.find hex with hk
  have hkj : k ≤ j.val := Nat.find_min' hex ⟨j.2, rfl⟩
  have hlt : ∀ i : Fin n, i.val < k → succMin F i < succMin F j := by
    intro i hi
    have hne : succMin F i ≠ succMin F j := fun h => Nat.find_min hex hi ⟨i.2, h⟩
    exact lt_of_le_of_ne (succMin_mono hF (show i ≤ j from by
      show i.val ≤ j.val; omega)) hne
  have hspec := (succMin_spec hF ⟨k, hkn⟩).2
  rw [hkM] at hspec
  have hWle : headSpan m k ≤ spanLT F (succMin F j) := by
    unfold headSpan
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact Submodule.subset_span ⟨m i, by simpa [hmM i] using hlt i hi, rfl⟩
  have hge : k ≤ Module.finrank ℝ (headSpan m k) :=
    finrank_ge_of_head hm hkn.le fun i hi => Submodule.subset_span ⟨i, hi, rfl⟩
  have hs' : Module.finrank ℝ (spanLT F (succMin F j)) ≤ k := hspec
  have hfin : Module.finrank ℝ (spanLT F (succMin F j)) ≤ Module.finrank ℝ (headSpan m k) := by omega
  have heq : headSpan m k = spanLT F (succMin F j) :=
    Submodule.eq_of_le_of_finrank_le hWle hfin
  have hc' : cast c ∈ spanLT F (succMin F j) := Submodule.subset_span ⟨c, hc, rfl⟩
  rw [← heq] at hc'
  exact headSpan_mono m hkj hc'

/-- The value of a diagonal form: $f(\vec{x}) = \sum_i d_i x_i^2$. -/
theorem val_diagonal (d x : Fin n → ℝ) : val (diagonal d) x = ∑ i, d i * x i ^ 2 := by
  simp only [val, dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Helper: the key inequality in the proof of Theorem 2.2. -/
private theorem key_ineq {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) {m : Fin n → Fin n → ℤ}
    (hm : LinearIndependent ℝ (fun j => cast (m j))) (hmM : ∀ j, val F (cast (m j)) = succMin F j)
    (P : Matrix (Fin n) (Fin n) ℝ) (hPm : ∀ j, P *ᵥ Pi.single j 1 = cast (m j))
    (hPinv : P⁻¹ * P = 1) (hPinv' : P * P⁻¹ = 1)
    {h : Fin n → ℝ} {C : Matrix (Fin n) (Fin n) ℝ} (hdec : IsSqDecomp (Pᵀ * F * P) h C)
    (hpos : ∀ i, 0 < h i) (b : Fin n → ℤ) (hb : b ≠ 0) :
    1 ≤ val ((C * P⁻¹)ᵀ * diagonal (fun j => h j / succMin F j) * (C * P⁻¹)) (cast b) := by
  classical
  have hMpos : ∀ j, 0 < succMin F j := succMin_pos hF
  set y : Fin n → ℝ := P⁻¹ *ᵥ cast b with hy
  have hPy : P *ᵥ y = cast b := by
    rw [hy, Matrix.mulVec_mulVec, hPinv', Matrix.one_mulVec]
  have hy0 : y ≠ 0 := by
    intro h0
    apply hb
    rw [h0, Matrix.mulVec_zero] at hPy
    funext i
    have := congrFun hPy i
    simpa [cast] using this.symm
  set S : Finset (Fin n) := Finset.univ.filter fun i => y i ≠ 0 with hS
  have hSne : S.Nonempty := by
    by_contra hne
    apply hy0
    funext i
    by_contra hi
    exact hne ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  set J := S.max' hSne with hJ
  have hJS : y J ≠ 0 := by
    have := S.max'_mem hSne
    simpa [hS] using this
  have hgt : ∀ i, J < i → y i = 0 := by
    intro i hi
    by_contra hci
    have : i ∈ S := by simp [hS, hci]
    exact absurd (S.le_max' i this) (not_le.2 hi)
  -- Claim 1: f(b) >= M_J
  have hclaim1 : succMin F J ≤ val F (cast b) := by
    by_contra hlt
    push Not at hlt
    have hmem := mem_span_of_val_lt_succMin hF hm hmM hlt
    have hker : Submodule.span ℝ ((fun i => (cast (m i) : Fin n → ℝ)) '' {i : Fin n | i < J}) ≤
        LinearMap.ker ((LinearMap.proj J : (Fin n → ℝ) →ₗ[ℝ] ℝ) ∘ₗ (P⁻¹).mulVecLin) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      have hiJ : i ≠ J := ne_of_lt hi
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        Matrix.mulVecLin_apply, LinearMap.coe_proj, Function.eval]
      rw [← hPm i, Matrix.mulVec_mulVec, hPinv, Matrix.one_mulVec]
      simp [hiJ.symm]
    have := hker hmem
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply,
      LinearMap.coe_proj, Function.eval] at this
    exact hJS this
  -- Claim 2: (C y)_i = 0 for i > J
  have hclaim2 : ∀ i, J < i → (C *ᵥ y) i = 0 := by
    intro i hi
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k < i
    · rw [hdec.1 i k hk, zero_mul]
    · rw [hgt k (lt_of_lt_of_le hi (not_lt.1 hk)), mul_zero]
  have hQb : (C * P⁻¹) *ᵥ cast b = C *ᵥ y := by
    rw [← Matrix.mulVec_mulVec]
  rw [val_conj, val_diagonal, hQb]
  have hG : val (Pᵀ * F * P) y = ∑ i, h i * (C *ᵥ y) i ^ 2 := val_eq_of_isSqDecomp hdec y
  rw [val_conj, hPy] at hG
  have hle : ∑ i, h i * (C *ᵥ y) i ^ 2 / succMin F J ≤
      ∑ i, h i / succMin F i * (C *ᵥ y) i ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i ≤ J
    · have h1 : h i / succMin F J ≤ h i / succMin F i :=
        div_le_div_of_nonneg_left (hpos i).le (hMpos i) (succMin_mono hF hi)
      calc h i * (C *ᵥ y) i ^ 2 / succMin F J = h i / succMin F J * (C *ᵥ y) i ^ 2 := by ring
        _ ≤ _ := by gcongr
    · rw [hclaim2 i (not_le.1 hi)]; simp
  have heq : ∑ i, h i * (C *ᵥ y) i ^ 2 / succMin F J = val F (cast b) / succMin F J := by
    rw [hG, ← Finset.sum_div]
  refine le_trans ?_ hle
  rw [heq, le_div_iff₀ (hMpos J)]
  linarith

/-- **Theorem 2.2** (Minkowski; Cassels, Ch. 12, §2, (2.5), p. 262): for every strictly positive definite real form
and every $\gamma$ satisfying Theorem 2.1 in dimension $n$,
$$M_0M_1\cdots M_{n-1} \le \gamma^n D, \qquad D = d(f) = \det F.$$
Formula (2.5) is lost in the machine-read text; it is reconstructed from the proof ((2.11) and (2.16), p. 263):
$1 \le \gamma\,d(h)^{1/n}$ with $d(h) = D/(M_0\cdots M_{n-1})$. *Proof* (Cassels'): in the coordinates
$\vec{x} = \sum_j y_j\vec{m}_j$ complete the squares, $f = \sum_j L_j^2$, and apply Theorem 2.1 to
$h = \sum_j L_j^2/M_j$, which is $\ge 1$ at nonzero integral points by Lemma 2.1. -/
@[kb "cassels1978" "Ch. 12, §2, Thm. 2.2, (2.5), pp. 262–263"]
theorem prod_succMin_le {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) {γ : ℝ} (hγ : HermiteConstantBound n γ) :
    ∏ j, succMin F j ≤ γ ^ n * F.det := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨m, hm, hmM⟩ := exists_succMin_vectors hF
  have hMpos : ∀ j, 0 < succMin F j := succMin_pos hF
  set P : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (m j i : ℝ) with hP
  have hPm : ∀ j, P *ᵥ Pi.single j 1 = cast (m j) := by
    intro j
    rw [Matrix.mulVec_single_one]
    ext i
    simp [hP, cast]
  have hPu : IsUnit P := Matrix.linearIndependent_col_iff_isUnit.1 hm
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have hPinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPdet
  have hPinv' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPdet
  have hGpos : (Pᵀ * F * P).PosDef := by
    have := hF.conjTranspose_mul_mul_same (B := P) (Matrix.mulVec_injective_of_isUnit hPu)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  obtain ⟨h, C, hdec, hpos⟩ := exists_isSqDecomp hGpos
  have hCdet : C.det = 1 := by
    rw [det_of_isUpperTriangular (fun i j hij => hdec.1 i j hij)]
    simp [hdec.2.1]
  have hPinvdet : (P⁻¹).det = (P.det)⁻¹ := by
    have := congrArg Matrix.det hPinv'
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact eq_inv_of_mul_eq_one_right this
  have hP0 : P.det ≠ 0 := hPdet.ne_zero
  have hQdet : (C * P⁻¹).det = (P.det)⁻¹ := by
    rw [Matrix.det_mul, hCdet, one_mul, hPinvdet]
  have hQu : IsUnit (C * P⁻¹) := by
    rw [Matrix.isUnit_iff_isUnit_det, hQdet]
    exact (isUnit_iff_ne_zero.2 (inv_ne_zero hP0))
  have hDpos : (diagonal fun j => h j / succMin F j).PosDef :=
    Matrix.posDef_diagonal_iff.2 fun j => div_pos (hpos j) (hMpos j)
  have hHpos : ((C * P⁻¹)ᵀ * diagonal (fun j => h j / succMin F j) * (C * P⁻¹)).PosDef := by
    have := hDpos.conjTranspose_mul_mul_same (B := C * P⁻¹) (Matrix.mulVec_injective_of_isUnit hQu)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hdetG : (Pᵀ * F * P).det = P.det ^ 2 * F.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]; ring
  have hprodh : ∏ i, h i = P.det ^ 2 * F.det := by
    rw [← hdetG]; exact (hdec.det_eq).symm
  have hdetH : ((C * P⁻¹)ᵀ * diagonal (fun j => h j / succMin F j) * (C * P⁻¹)).det =
      F.det / ∏ j, succMin F j := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hQdet, Matrix.det_diagonal,
      Finset.prod_div_distrib, hprodh]
    field_simp
  obtain ⟨b, hb0, hb⟩ := hγ _ hHpos
  have h1 := key_ineq hF hm hmM P hPm hPinv hPinv' hdec hpos b hb0
  rw [hdetH] at hb
  have hFd : 0 < F.det := hF.det_pos
  have hprodpos : 0 < ∏ j, succMin F j := Finset.prod_pos fun j _ => hMpos j
  have hdpos : 0 < F.det / ∏ j, succMin F j := div_pos hFd hprodpos
  have hrpos : 0 < (F.det / ∏ j, succMin F j) ^ ((1 : ℝ) / n) := Real.rpow_pos_of_pos hdpos _
  have hγpos : 0 < γ := by
    by_contra hneg
    push Not at hneg
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hneg hrpos.le]
  have hone : 1 ≤ γ * (F.det / ∏ j, succMin F j) ^ ((1 : ℝ) / n) := h1.trans hb
  have hpow := pow_le_pow_left₀ zero_le_one hone n
  rw [one_pow, mul_pow] at hpow
  have : ((F.det / ∏ j, succMin F j) ^ ((1 : ℝ) / n)) ^ n = F.det / ∏ j, succMin F j := by
    rw [one_div]
    exact Real.rpow_inv_natCast_pow hdpos.le hn.ne'
  rw [this, mul_div_assoc', le_div_iff₀ hprodpos] at hpow
  linarith

end QuadFormsKB.Reduction
