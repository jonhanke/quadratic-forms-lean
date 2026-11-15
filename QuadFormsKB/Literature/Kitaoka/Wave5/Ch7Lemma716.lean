/-
# Kitaoka 1993, Lemma 7.1.6: the lattice with Gram matrix $p I - J$ is of E-type

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §7.1, Lemma 7.1.6, p. 196 (printed page).

**Statement.** Let $p$ be a prime and $L = \mathbb Z u_1 + \dots + \mathbb Z u_{p-1}$ the quadratic lattice with
$B(u_i, u_j) = -1$ for $i \ne j$ and $B(u_i, u_i) = p - 1$. Then $L$ is a positive lattice of E-type.

**Encoding.** The Gram-matrix model of `Ch7EType.lean`: $L = (\mathbb Z^{n}, A_n)$ with $n = p - 1$ and
$(A_n)_{ij} = n$ for $i = j$, $-1$ for $i \ne j$ (`gram716 n`; 0-based, Kitaoka's $u_1, \dots, u_{p-1}$ are the basis
vectors $e_0, \dots, e_{n-1}$). Kitaoka's proof never uses that $p$ is prime, so the result is proved for every $n$
(`isPosGram_gram716`, `isEType_gram716`) and specialised to $n = p - 1$ in `lemma716`.

**Proof** (Kitaoka's, reorganised). For $X = \sum_i u_i \otimes w_i \in L \otimes M$ (rows $w_i \in M$),
$Q(X) = (n+1)\sum_i Q(w_i) - Q(\sum_i w_i)$ (`tensorQ_gram716`). If $T = \{i \mid w_i \ne 0\}$ has $k$ elements, then
$$Q(X) = (n + 1 - k)\sum_{i \in T} Q(w_i) + \tfrac12 \sum_{i, j \in T} Q(w_i - w_j)
  \ \ge\ (n + 1 - k)\,k \min M \ \ge\ n \min M,$$
since $(n+1-k)k - n = (k-1)(n-k) \ge 0$; and $Q(u_1 \otimes y) = n \min M$ for a minimal $y$. So a minimal $X$ has all
$w_i$ ($i \in T$) equal and $k = 1$ or $k = n$, i.e. $X = u_i \otimes w$ or $X = (\sum_i u_i) \otimes w$.

**Proves** `gram716`, `isPosGram_gram716`, `tensorQ_gram716`, `isEType_gram716`, `lemma716` (unconditional).
*Update* (generalization): the primality of $p$ is not used; $p I - J$ of rank $p - 1$ is of E-type for every integer
$p \ge 1$.
-/
import Mathlib.Algebra.Order.Chebyshev
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch7Lemma711

open Matrix

noncomputable section

namespace QuadFormsKB.Kitaoka.EType

open scoped BigOperators

/-- **The Gram matrix of Kitaoka's Lemma 7.1.6** (p. 196), of size $n = p - 1$: $n$ on the diagonal and $-1$ off it,
i.e. $(n + 1) I - J$. -/
def gram716 (n : ℕ) : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => if i = j then (n : ℚ) else -1

@[simp] theorem gram716_apply (n : ℕ) (i j : Fin n) : gram716 n i j = if i = j then (n : ℚ) else -1 := rfl

section Bil

variable {κ : Type*} [Fintype κ]

/-- The bilinear form $B(u, v) = \sum_{j, l} u_j v_l B_{jl}$ of the lattice $(\mathbb Z^\kappa, B)$. -/
def bq (B : Matrix κ κ ℚ) (u v : κ → ℤ) : ℚ := ∑ j, ∑ l, (u j : ℚ) * v l * B j l

theorem gramQ_eq_bq (B : Matrix κ κ ℚ) (u : κ → ℤ) : gramQ B u = bq B u u := by
  rw [gramQ_eq_sum]; rfl

theorem bq_add_left (B : Matrix κ κ ℚ) (u u' v : κ → ℤ) : bq B (u + u') v = bq B u v + bq B u' v := by
  simp only [bq, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]

theorem bq_add_right (B : Matrix κ κ ℚ) (u v v' : κ → ℤ) : bq B u (v + v') = bq B u v + bq B u v' := by
  simp only [bq, Pi.add_apply, Int.cast_add, mul_add, add_mul, Finset.sum_add_distrib]

/-- $u \mapsto B(u, v)$ as an additive map. -/
def bqL (B : Matrix κ κ ℚ) (v : κ → ℤ) : (κ → ℤ) →+ ℚ :=
  AddMonoidHom.mk' (fun u => bq B u v) fun u u' => bq_add_left B u u' v

/-- $v \mapsto B(u, v)$ as an additive map. -/
def bqR (B : Matrix κ κ ℚ) (u : κ → ℤ) : (κ → ℤ) →+ ℚ :=
  AddMonoidHom.mk' (fun v => bq B u v) fun v v' => bq_add_right B u v v'

theorem bq_sum_left {α : Type*} (B : Matrix κ κ ℚ) (s : Finset α) (u : α → κ → ℤ) (v : κ → ℤ) :
    bq B (∑ a ∈ s, u a) v = ∑ a ∈ s, bq B (u a) v :=
  map_sum (bqL B v) u s

theorem bq_sum_right {α : Type*} (B : Matrix κ κ ℚ) (s : Finset α) (u : κ → ℤ) (v : α → κ → ℤ) :
    bq B u (∑ a ∈ s, v a) = ∑ a ∈ s, bq B u (v a) :=
  map_sum (bqR B u) v s

theorem bq_comm {B : Matrix κ κ ℚ} (hB : B.IsSymm) (u v : κ → ℤ) : bq B u v = bq B v u := by
  simp only [bq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  have : B l j = B j l := by
    have := congrFun (congrFun hB j) l
    simpa [Matrix.transpose_apply] using this
  rw [this]; ring

theorem bq_sub_sub {B : Matrix κ κ ℚ} (hB : B.IsSymm) (u v : κ → ℤ) :
    bq B (u - v) (u - v) = bq B u u + bq B v v - 2 * bq B u v := by
  have h := bq_comm hB v u
  simp only [bq, Pi.sub_apply, Int.cast_sub] at h ⊢
  have e : ∀ j l, ((u j : ℚ) - v j) * ((u l : ℚ) - v l) * B j l =
      (u j : ℚ) * u l * B j l + (v j : ℚ) * v l * B j l - (u j : ℚ) * v l * B j l
        - (v j : ℚ) * u l * B j l := fun j l => by ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [h]; ring

/-- The $i$-th row $w_i = X_{i, \cdot}$ of an integer matrix, as a vector. -/
def rowV {ι : Type*} (X : Matrix ι κ ℤ) (i : ι) : κ → ℤ := fun j => X i j

end Bil

/-- The form of $L \otimes M$ for Lemma 7.1.6: with rows $w_i = X_{i,\cdot}$,
$Q(X) = (n+1)\sum_i Q(w_i) - Q(\sum_i w_i)$. -/
theorem tensorQ_gram716 {κ : Type*} [Fintype κ] (n : ℕ) (B : Matrix κ κ ℚ) (X : Matrix (Fin n) κ ℤ) :
    tensorQ (gram716 n) B X = (n + 1) * ∑ i, bq B (rowV X i) (rowV X i) - bq B (∑ i, rowV X i) (∑ i, rowV X i) := by
  have h1 : tensorQ (gram716 n) B X = ∑ i, ∑ k, gram716 n i k * bq B (rowV X i) (rowV X k) := by
    simp only [tensorQ, bq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [rowV]; ring
  rw [h1, bq_sum_left]
  simp only [bq_sum_right, gram716_apply, ite_mul, neg_one_mul, Finset.mul_sum]
  have : ∀ i : Fin n, ∑ k, (if i = k then (n : ℚ) * bq B (rowV X i) (rowV X k) else -bq B (rowV X i) (rowV X k)) =
      (n + 1) * bq B (rowV X i) (rowV X i) - ∑ k, bq B (rowV X i) (rowV X k) := by
    intro i
    have e : ∀ k, (if i = k then (n : ℚ) * bq B (rowV X i) (rowV X k) else -bq B (rowV X i) (rowV X k)) =
        (if i = k then ((n : ℚ) + 1) * bq B (rowV X i) (rowV X k) else 0) - bq B (rowV X i) (rowV X k) := by
      intro k; split_ifs <;> ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [this, Finset.sum_sub_distrib]

/-- $Q(e_i) = A_{ii}$. -/
theorem gramQ_single {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℚ) (i : ι) :
    gramQ A (Pi.single i 1) = A i i := by
  rw [gramQ_eq_sum]
  simp only [Pi.single_apply]
  simp [Finset.sum_ite_eq', ite_mul, mul_ite]

/-- The Gram matrix of Lemma 7.1.6 is symmetric. -/
theorem gram716_isSymm (n : ℕ) : (gram716 n).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, gram716_apply]
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- **Kitaoka 1993, Lemma 7.1.6** (p. 196), first assertion, for every $n$: the lattice with Gram matrix
$(n + 1)I - J$ is positive, since $x^{\mathsf T}A_n x = (n+1)\sum_i x_i^2 - (\sum_i x_i)^2 \ge \sum_i x_i^2$
(Cauchy–Schwarz). -/
theorem isPosGram_gram716 (n : ℕ) : IsPosGram (gram716 n) := by
  refine ⟨gram716_isSymm n, fun x hx => ?_⟩
  have hform : x ⬝ᵥ (gram716 n *ᵥ x) = (n + 1) * ∑ i, x i ^ 2 - (∑ i, x i) ^ 2 := by
    simp only [dotProduct, mulVec, gram716_apply]
    have : ∀ i : Fin n, x i * ∑ k, (if i = k then (n : ℚ) else -1) * x k =
        (n + 1) * x i ^ 2 - x i * ∑ k, x k := by
      intro i
      have e : ∀ k, (if i = k then (n : ℚ) else -1) * x k = (if i = k then ((n : ℚ) + 1) * x k else 0) - x k := by
        intro k; split_ifs <;> ring
      simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      ring
    simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [hform]
  have hcs : (∑ i, x i) ^ 2 ≤ (Finset.univ.card : ℚ) * ∑ i, x i ^ 2 := sq_sum_le_card_mul_sum_sq
  simp only [Finset.card_univ, Fintype.card_fin] at hcs
  have hpos : 0 < ∑ i, x i ^ 2 := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h; push_neg at h; exact hx (funext h)
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => x i ^ 2)
      (fun i _ => sq_nonneg (x i)) (Finset.mem_univ i))
  nlinarith

/-- The minimum of $L \otimes M$ for Lemma 7.1.6: if $y$ is a minimal vector of $M$ and $X$ is a nonzero vector of
$L \otimes M$, then $Q(X) \ge n\,Q(y)$, and equality forces $X$ to be split. -/
theorem tensorQ_gram716_ge {m : ℕ} (n : ℕ) {B : Matrix (Fin m) (Fin m) ℚ} (hB : IsPosGram B)
    {y : Fin m → ℤ} (hy : IsMinimalVector B y) {X : Matrix (Fin n) (Fin m) ℤ} (hX : X ≠ 0) :
    (n : ℚ) * gramQ B y ≤ tensorQ (gram716 n) B X ∧
      (tensorQ (gram716 n) B X ≤ n * gramQ B y → ∃ x : Fin n → ℤ, ∃ w : Fin m → ℤ, X = vecMulVec x w) := by
  classical
  set m0 := gramQ B y with hm0
  have hm0pos : 0 < m0 := gramQ_pos hB hy.1
  set T : Finset (Fin n) := Finset.univ.filter (fun i => rowV X i ≠ 0) with hT
  set k := T.card with hk
  have hoff : ∀ i, i ∉ T → rowV X i = 0 := by
    intro i hi; by_contra h; exact hi (by simp [hT, h])
  have hTne : T.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hX; ext i j
    exact congrFun (hoff i (by simp [h])) j
  have hk1 : 1 ≤ k := Finset.card_pos.2 hTne
  have hkn : k ≤ n := by
    have := Finset.card_le_univ T; simpa using this
  -- the sums restricted to `T`
  have hS1 : ∑ i, bq B (rowV X i) (rowV X i) = ∑ i ∈ T, bq B (rowV X i) (rowV X i) :=
    (Finset.sum_subset (Finset.subset_univ T) fun i _ hi => by rw [hoff i hi]; simp [bq]).symm
  have hs : ∑ i, rowV X i = ∑ i ∈ T, rowV X i :=
    (Finset.sum_subset (Finset.subset_univ T) fun i _ hi => hoff i hi).symm
  set S1 := ∑ i ∈ T, bq B (rowV X i) (rowV X i) with hS1def
  set P := ∑ a ∈ T, ∑ b ∈ T, bq B (rowV X a - rowV X b) (rowV X a - rowV X b) with hP
  -- `P = 2 k S1 - 2 Q(s)`
  have hPeq : P = 2 * k * S1 - 2 * bq B (∑ i ∈ T, rowV X i) (∑ i ∈ T, rowV X i) := by
    simp only [hP, bq_sub_sub hB.1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, bq_sum_left, bq_sum_right]
    rw [Finset.sum_comm (s := T) (t := T) (f := fun x a => bq B (rowV X a) (rowV X x))]
    simp only [hS1def, hk]
    ring
  have hQ : tensorQ (gram716 n) B X = (n + 1 - k) * S1 + P / 2 := by
    rw [tensorQ_gram716, hS1, hs, hPeq]; ring
  have hP0 : 0 ≤ P := by
    refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
    rw [← gramQ_eq_bq]; exact gramQ_nonneg hB _
  have hS1ge : (k : ℚ) * m0 ≤ S1 := by
    have : ∑ i ∈ T, m0 ≤ S1 := Finset.sum_le_sum fun i hi => by
      rw [← gramQ_eq_bq]
      exact hy.2 _ (by simpa [hT] using hi)
    simpa [hk] using this
  have hkq1 : (1 : ℚ) ≤ k := by exact_mod_cast hk1
  have hkqn : (k : ℚ) ≤ n := by exact_mod_cast hkn
  have hlow : (n + 1 - k) * (k * m0) ≤ tensorQ (gram716 n) B X := by
    rw [hQ]
    have : (n + 1 - k) * (k * m0) ≤ (n + 1 - k) * S1 :=
      mul_le_mul_of_nonneg_left hS1ge (by linarith)
    linarith
  have hkey : (n : ℚ) * m0 + (k - 1) * (n - k) * m0 ≤ tensorQ (gram716 n) B X := by
    have : (n + 1 - k) * (k * m0) = (n : ℚ) * m0 + (k - 1) * (n - k) * m0 := by ring
    linarith
  have hnn : 0 ≤ ((k : ℚ) - 1) * (n - k) * m0 :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) hm0pos.le
  refine ⟨by linarith, fun hle => ?_⟩
  -- equality case
  have hP0' : P = 0 := by
    have h1 : (n + 1 - k) * S1 + P / 2 ≤ n * m0 := by rw [← hQ]; exact hle
    have : (n + 1 - k) * (k * m0) ≤ (n + 1 - k) * S1 := mul_le_mul_of_nonneg_left hS1ge (by linarith)
    have : (n + 1 - k) * (k * m0) = (n : ℚ) * m0 + (k - 1) * (n - k) * m0 := by ring
    linarith
  have hprod : ((k : ℚ) - 1) * (n - k) = 0 := by
    have h1 : (n + 1 - k) * S1 + P / 2 ≤ n * m0 := by rw [← hQ]; exact hle
    have : (n + 1 - k) * (k * m0) ≤ (n + 1 - k) * S1 := mul_le_mul_of_nonneg_left hS1ge (by linarith)
    have : (n + 1 - k) * (k * m0) = (n : ℚ) * m0 + (k - 1) * (n - k) * m0 := by ring
    have h3 : ((k : ℚ) - 1) * (n - k) * m0 ≤ 0 := by linarith
    have h4 : ((k : ℚ) - 1) * (n - k) ≤ 0 := by
      by_contra h; push_neg at h; nlinarith
    exact le_antisymm h4 (mul_nonneg (by linarith) (by linarith))
  -- all rows in `T` are equal
  have heq : ∀ a ∈ T, ∀ b ∈ T, rowV X a = rowV X b := by
    intro a ha b hb
    have hterm : bq B (rowV X a - rowV X b) (rowV X a - rowV X b) = 0 := by
      have hnn' : ∀ a ∈ T, ∀ b ∈ T, 0 ≤ bq B (rowV X a - rowV X b) (rowV X a - rowV X b) := fun a _ b _ => by
        rw [← gramQ_eq_bq]; exact gramQ_nonneg hB _
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun a ha =>
        Finset.sum_nonneg fun b hb => hnn' a ha b hb).1 hP0' a ha
      exact (Finset.sum_eq_zero_iff_of_nonneg fun b hb => hnn' a ha b hb).1 h1 b hb
    by_contra hne
    have := gramQ_pos hB (sub_ne_zero.2 hne)
    rw [gramQ_eq_bq, hterm] at this
    exact lt_irrefl _ this
  obtain ⟨a, ha⟩ := hTne
  rcases mul_eq_zero.1 hprod with h | h
  · -- `k = 1`: `X = e_a ⊗ X a`
    have hk1' : k = 1 := by
      have : (k : ℚ) = 1 := by linarith
      exact_mod_cast this
    refine ⟨Pi.single a 1, rowV X a, ?_⟩
    ext i j
    simp only [vecMulVec_apply]
    by_cases hi : i = a
    · subst hi; simp [rowV]
    · rw [Pi.single_eq_of_ne hi, zero_mul]
      have : i ∉ T := by
        intro hiT
        have h2 : ({a, i} : Finset (Fin n)) ⊆ T := by
          intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
        have := Finset.card_le_card h2
        rw [Finset.card_pair (Ne.symm hi)] at this
        omega
      exact congrFun (hoff i this) j
  · -- `k = n`: all rows equal, `X = (1, …, 1) ⊗ X a`
    have hkn' : k = n := by
      have : (k : ℚ) = n := by linarith
      exact_mod_cast this
    have hTuniv : T = Finset.univ := Finset.eq_univ_of_card T (by simp [← hk, hkn'])
    refine ⟨fun _ => 1, rowV X a, ?_⟩
    ext i j
    simp only [vecMulVec_apply, one_mul]
    exact congrFun (heq i (by simp [hTuniv]) a ha) j

/-- **Kitaoka 1993, Lemma 7.1.6** (p. 196), for every $n$: the lattice $(\mathbb Z^n, (n+1)I - J)$ is of E-type. -/
theorem isEType_gram716 (n : ℕ) : IsEType (gram716 n) := by
  intro m B hB X hX
  obtain ⟨y, hy⟩ : ∃ y, IsMinimalVector B y := by
    -- `M` has a nonzero vector, read off from a nonzero entry of `X`
    obtain ⟨i, j, hij⟩ : ∃ i j, X i j ≠ 0 := by
      by_contra h; push_neg at h; exact hX.1 (by ext i j; exact h i j)
    exact exists_isMinimalVector hB (z0 := Pi.single j 1) (by
      intro h0; have := congrFun h0 j; simp at this)
  obtain ⟨i0, j0, hij⟩ : ∃ i j, X i j ≠ 0 := by
    by_contra h; push_neg at h; exact hX.1 (by ext i j; exact h i j)
  -- the competitor `e_{i0} ⊗ y` has `Q = n Q(y)`
  have hcomp : tensorQ (gram716 n) B (vecMulVec (Pi.single i0 1) y) = n * gramQ B y := by
    rw [tensorQ_vecMulVec]
    rw [gramQ_single, gram716_apply, if_pos rfl]
  have hle := hX.2 _ (vecMulVec_ne_zero (x := Pi.single i0 1) (by
    intro h0; have := congrFun h0 i0; simp at this) hy.1)
  rw [hcomp] at hle
  exact (tensorQ_gram716_ge n hB hy hX.1).2 hle

/-- **Kitaoka 1993, Lemma 7.1.6** (p. 196): for a prime $p$, the lattice $L = \mathbb Z u_1 + \dots +
\mathbb Z u_{p-1}$ with $B(u_i, u_j) = -1$ ($i \ne j$) and $B(u_i, u_i) = p - 1$ is a positive lattice of E-type.
(The proof does not use that $p$ is prime; see `isEType_gram716`.) -/
@[kb "kitaoka1993" "§7.1, Lemma 7.1.6, p. 196"]
theorem lemma716 (p : ℕ) (_hp : p.Prime) :
    IsPosGram (gram716 (p - 1)) ∧ IsEType (gram716 (p - 1)) :=
  ⟨isPosGram_gram716 _, isEType_gram716 _⟩

/-- The minimum in Lemma 7.1.6 (p. 196): $\min(L \otimes M) = (p - 1)\min M$, i.e. $Q(X) \ge n\,Q(y)$ for every
nonzero $X \in L \otimes M$ and minimal $y \in M$, with equality for $X = u_1 \otimes y$. -/
theorem lemma716_min {m : ℕ} (n : ℕ) (hn : 0 < n) {B : Matrix (Fin m) (Fin m) ℚ} (hB : IsPosGram B)
    {y : Fin m → ℤ} (hy : IsMinimalVector B y) :
    (∀ X : Matrix (Fin n) (Fin m) ℤ, X ≠ 0 → (n : ℚ) * gramQ B y ≤ tensorQ (gram716 n) B X) ∧
      tensorQ (gram716 n) B (vecMulVec (Pi.single ⟨0, hn⟩ 1) y) = n * gramQ B y := by
  refine ⟨fun X hX => (tensorQ_gram716_ge n hB hy hX).1, ?_⟩
  rw [tensorQ_vecMulVec]
  rw [gramQ_single, gram716_apply, if_pos rfl]

end QuadFormsKB.Kitaoka.EType
