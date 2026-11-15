/-
# Kitaoka 1993, §§7.2–7.3: divisibility, Minkowski's congruence lemma, weighted graphs

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §7.2 (definition of divisibility, p. 199;
Lemma 7.2.2, p. 203) and §7.3 (weighted graphs, p. 217; Theorem 7.3.1, p. 222).

**Contents**
* `IsDivisibleBy` (7.2.d1): $M$ is divisible by $L$ if $M \cong L \otimes K$ for a positive lattice $K$.
* `Lemma722` (Lemma 7.2.2, *stated*): a matrix $A \in M_n(\mathbb Z)$ with $A \equiv 1_n \bmod p$ and $A^k = 1_n$ is
  $1_n$, or ($p = 2$ only) conjugate in $\mathrm{GL}_n(\mathbb Z)$ to a diagonal matrix of signs.
* `WeightedGraph`, `WeightedGraph.IsConnected`, `WeightedGraph.prod`, `WeightedGraph.pi`, `WeightedGraph.Isometry`,
  `WeightedGraph.IsIndecomposable` (7.3.d1, 7.3.d2): Kitaoka's weighted graphs, products and isometries;
  `WeightedGraph.pi_eq_one_iff` checks that the product is again a weighted graph.
* `Theorem731` (Theorem 7.3.1, *stated*): unique factorization of finite weighted graphs into connected
  indecomposable factors with more than one element.

The proofs of Lemma 7.2.2 and Theorem 7.3.1 are not formalized here (out of reach this wave).
-/
import QuadFormsKB.Literature.Kitaoka.Ch7EType

open Matrix

noncomputable section

namespace QuadFormsKB.Kitaoka.EType

/-- **Divisibility of positive lattices** (Kitaoka 1993, §7.2, p. 199): the positive lattice $M = (\mathbb Z^\kappa, B)$
is *divisible by* $L = (\mathbb Z^\iota, A)$ if $M \cong L \otimes K$ for some positive lattice $K = (\mathbb Z^c, C)$
(Gram matrix of $L \otimes K$: the Kronecker product $A \otimes C$). -/
@[kb "kitaoka1993" "§7.2, p. 199 (M divisible by L)"]
def IsDivisibleBy {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (B : Matrix κ κ ℚ) (A : Matrix ι ι ℚ) : Prop :=
  ∃ (c : ℕ) (C : Matrix (Fin c) (Fin c) ℚ), IsPosGram C ∧ GramIsometric (Matrix.kroneckerMap (· * ·) A C) B

/-- **Kitaoka 1993, Lemma 7.2.2** (p. 203; Minkowski), *stated*: let $p$ be a prime and $A \in M_n(\mathbb Z)$ with
$A \equiv 1_n \bmod p$. If $A^k = 1_n$ for some $k \ge 1$, then $A = 1_n$ or $A = W\operatorname{diag}(\pm1, \dots,
\pm1)W^{-1}$ for some $W \in \mathrm{GL}_n(\mathbb Z)$; the latter occurs only when $p = 2$. -/
@[kb "kitaoka1993" "§7.2, Lemma 7.2.2, p. 203"]
def Lemma722 : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), (∀ i j, (p : ℤ) ∣ (A - 1) i j) →
    ∀ k : ℕ, 1 ≤ k → A ^ k = 1 →
      A = 1 ∨ (p = 2 ∧ ∃ (W : GL (Fin n) ℤ) (s : Fin n → ℤ), (∀ i, s i = 1 ∨ s i = -1) ∧
        A = (W : Matrix (Fin n) (Fin n) ℤ) * diagonal s * ((W⁻¹ : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ))

/-- **A weighted graph** (Kitaoka 1993, §7.3, p. 217): a finite set $V$ with a map $[\,,\,] : V \times V \to [0, 1]$
such that $[a, a'] = 1$ if and only if $a = a'$, and $[a, a'] = [a', a]$. Fields: `w` the weight, `nonneg`,
`le_one` (values in $[0,1]$), `eq_one_iff`, `symm`. -/
@[kb "kitaoka1993" "§7.3, p. 217 (weighted graph)"]
structure WeightedGraph (V : Type*) [Fintype V] where
  /-- The weight $[a, a']$. -/
  w : V → V → ℝ
  nonneg : ∀ a b, 0 ≤ w a b
  le_one : ∀ a b, w a b ≤ 1
  eq_one_iff : ∀ a b, w a b = 1 ↔ a = b
  symm : ∀ a b, w a b = w b a

namespace WeightedGraph

variable {V W : Type*} [Fintype V] [Fintype W]

/-- **Connected weighted graph** (Kitaoka 1993, §7.3, p. 217): $A$ is connected unless $A = A_1 \sqcup A_2$ with
$A_1, A_2$ nonempty and $[a_1, a_2] = 0$ for all $a_1 \in A_1$, $a_2 \in A_2$. -/
@[kb "kitaoka1993" "§7.3, p. 217 (connected weighted graph)"]
def IsConnected (G : WeightedGraph V) : Prop :=
  ∀ S : Set V, S.Nonempty → Sᶜ.Nonempty → ∃ a ∈ S, ∃ b ∉ S, G.w a b ≠ 0

/-- A product of numbers in $[0, 1]$ over a finite set is $1$ iff every factor is $1$. -/
theorem prod_eq_one_iff_of_le_one {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h0 : ∀ i, 0 ≤ f i) (h1 : ∀ i, f i ≤ 1) :
    ∏ i ∈ s, f i = 1 ↔ ∀ i ∈ s, f i = 1 := by
  classical
  constructor
  · intro h i hi
    refine le_antisymm (h1 i) ?_
    have hrest : ∏ j ∈ s.erase i, f j ≤ 1 := Finset.prod_le_one₀ (fun j _ => h0 j) (fun j _ => h1 j)
    rw [← Finset.mul_prod_erase s f hi] at h
    nlinarith [h0 i, Finset.prod_nonneg fun j (_ : j ∈ s.erase i) => h0 j]
  · intro h
    exact Finset.prod_eq_one h

/-- **The product of weighted graphs** $A_0 \times \dots \times A_{k-1}$ (Kitaoka 1993, §7.3, p. 217), with weight
$[(a_i), (a'_i)] = \prod_i [a_i, a'_i]$. -/
@[kb "kitaoka1993" "§7.3, p. 217 (product of weighted graphs)"]
def pi {k : ℕ} {V : Fin k → Type*} [∀ i, Fintype (V i)] (G : ∀ i, WeightedGraph (V i)) :
    WeightedGraph (∀ i, V i) where
  w a b := ∏ i, (G i).w (a i) (b i)
  nonneg a b := Finset.prod_nonneg fun i _ => (G i).nonneg _ _
  le_one a b := Finset.prod_le_one₀ (fun i _ => (G i).nonneg _ _) fun i _ => (G i).le_one _ _
  eq_one_iff a b := by
    rw [prod_eq_one_iff_of_le_one _ _ (fun i => (G i).nonneg _ _) (fun i => (G i).le_one _ _)]
    simp only [Finset.mem_univ, true_implies, (G _).eq_one_iff]
    exact ⟨funext, fun h i => congrFun h i⟩
  symm a b := Finset.prod_congr rfl fun i _ => (G i).symm _ _

/-- `pi` is a weighted graph: its weight is $1$ exactly on the diagonal (restating the field for reference). -/
theorem pi_eq_one_iff {k : ℕ} {V : Fin k → Type*} [∀ i, Fintype (V i)] (G : ∀ i, WeightedGraph (V i))
    (a b : ∀ i, V i) : (pi G).w a b = 1 ↔ a = b :=
  (pi G).eq_one_iff a b

/-- **The product of two weighted graphs** $A \times B$ (Kitaoka 1993, §7.3, p. 217):
$[(a_1, b_1), (a_2, b_2)] = [a_1, a_2]\,[b_1, b_2]$. -/
@[kb "kitaoka1993" "§7.3, p. 217 (A × B)"]
def prod (G : WeightedGraph V) (H : WeightedGraph W) : WeightedGraph (V × W) where
  w a b := G.w a.1 b.1 * H.w a.2 b.2
  nonneg a b := mul_nonneg (G.nonneg _ _) (H.nonneg _ _)
  le_one a b := (mul_le_mul (G.le_one _ _) (H.le_one _ _) (H.nonneg _ _) zero_le_one).trans_eq (one_mul 1)
  eq_one_iff a b := by
    constructor
    · intro h
      have h1 := G.le_one a.1 b.1
      have h2 := H.le_one a.2 b.2
      have h3 := G.nonneg a.1 b.1
      have h4 := H.nonneg a.2 b.2
      have e1 : G.w a.1 b.1 = 1 := by nlinarith
      have e2 : H.w a.2 b.2 = 1 := by nlinarith
      exact Prod.ext ((G.eq_one_iff _ _).1 e1) ((H.eq_one_iff _ _).1 e2)
    · rintro rfl
      rw [(G.eq_one_iff _ _).2 rfl, (H.eq_one_iff _ _).2 rfl, one_mul]
  symm a b := by rw [G.symm, H.symm]

/-- **An isometry of weighted graphs** $\sigma : A \cong B$ (Kitaoka 1993, §7.3, p. 217): a bijection with
$[\sigma x, \sigma y] = [x, y]$. -/
@[kb "kitaoka1993" "§7.3, p. 217 (isometry of weighted graphs)"]
def Isometry (G : WeightedGraph V) (H : WeightedGraph W) (σ : V ≃ W) : Prop :=
  ∀ x y, H.w (σ x) (σ y) = G.w x y

/-- **Indecomposable weighted graph** (Kitaoka 1993, §7.3, p. 222): $A$ is not isometric to $B \times C$ for weighted
graphs $B$, $C$ with $\#B > 1$, $\#C > 1$. -/
@[kb "kitaoka1993" "§7.3, p. 222 (indecomposable weighted graph)"]
def IsIndecomposable (G : WeightedGraph V) : Prop :=
  ∀ (B C : Type) [Fintype B] [Fintype C] (GB : WeightedGraph B) (GC : WeightedGraph C) (σ : V ≃ B × C),
    1 < Fintype.card B → 1 < Fintype.card C → ¬ Isometry G (GB.prod GC) σ

end WeightedGraph

open WeightedGraph in
/-- **Kitaoka 1993, Theorem 7.3.1** (p. 222), *stated*: let $A_i$ ($0 \le i < m$) and $B_j$ ($0 \le j < n$) be
connected, indecomposable weighted graphs with $\#A_i > 1$, $\#B_j > 1$, and let
$\sigma : \prod_i A_i \cong \prod_j B_j$ be an isometry. Then $m = n$ and $\sigma$ is a product of isometries
$\sigma_i : A_i \cong B_{s(i)}$ for a permutation $s$: $\sigma(a)_{s(i)} = \sigma_i(a_i)$. -/
@[kb "kitaoka1993" "§7.3, Thm. 7.3.1, p. 222"]
def Theorem731 : Prop :=
  ∀ (m n : ℕ) (A : Fin m → Type) (B : Fin n → Type) [∀ i, Fintype (A i)] [∀ j, Fintype (B j)]
    (GA : ∀ i, WeightedGraph (A i)) (GB : ∀ j, WeightedGraph (B j)),
    (∀ i, (GA i).IsConnected ∧ (GA i).IsIndecomposable ∧ 1 < Fintype.card (A i)) →
    (∀ j, (GB j).IsConnected ∧ (GB j).IsIndecomposable ∧ 1 < Fintype.card (B j)) →
    ∀ σ : (∀ i, A i) ≃ (∀ j, B j), Isometry (pi GA) (pi GB) σ →
      ∃ h : m = n, ∃ s : Equiv.Perm (Fin m), ∃ τ : ∀ i, A i ≃ B (Fin.cast h (s i)),
        (∀ i, Isometry (GA i) (GB (Fin.cast h (s i))) (τ i)) ∧
        ∀ a i, σ a (Fin.cast h (s i)) = τ i (a i)

end QuadFormsKB.Kitaoka.EType
