/-
# Kitaoka 1993, §5.6: the second reduction formula (Lemmas 5.6.6, 5.6.7, 5.6.8, Theorem 5.6.2, Corollary 5.6.1)

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.6, pp. 104–108 (printed pages): the set
$C_{p^r}(M, N; K)$ (pp. 104–105), Lemma 5.6.6 (p. 105), Lemma 5.6.7 (pp. 105–106), Lemma 5.6.8 (p. 106),
Theorem 5.6.2 (p. 107), Corollary 5.6.1 (p. 108).

**Setting** (as in `Ch5Densities.lean`). $p$ is a prime and $R = \mathbb Z_p$. $N$ is a regular lattice of rank $n$ with
integral Gram matrix $S$ (an $n \times n$ matrix), $M = M_1 \perp M_2$ with $M_i$ of rank $m_i$ and integral Gram
matrices $T_1$, $T_2$; the Gram matrix of $M$ is the block diagonal matrix `blockGram T₁ T₂` (basis of $M_1$ first).
A submodule $K$ of $N$ isometric to $M_1$ is given by a matrix $Y \in M_{n,m_1}(R)$ with $Y^{\mathsf T} S Y = T_1$
(the columns of $Y$ are the images of the basis of $M_1$, they span $K$). The orthogonal group is
$O(N) = \{A \in \mathrm{GL}_n(R) \mid A^{\mathsf T} S A = S\}$. Two such matrices $Y, Y'$ give submodules transformed
into each other by $O(N)$ exactly when $AY = Y'G$ for some $A \in O(N)$ and $G \in \mathrm{GL}_{m_1}(R)$
(`SameOrbit`). Kitaoka writes $K^{\#}$ for the dual lattice of $K$ in $FK$ and $K^{\perp} = N \cap FK^{\perp}$; here
$[K^{\#} : K] = |\det T_1|_p^{-1}$ (the discriminant index of $M_1$, $= [M_1^{\#} : M_1]$, as Kitaoka notes in the proof
of Theorem 5.6.2), and $K^{\perp}$ is described by a basis matrix $Z \in M_{n,k}(R)$ (`IsPerpBasis`).

**Defines**
* `blockGram T₁ T₂`: the Gram matrix of $M_1 \perp M_2$;
* `IsClassSystem S T₁ Y`: a complete system $\{K_i\}$ of submodules of $N$ isometric to $M_1$, pairwise not
  transformed into each other by $O(N)$ (`SameOrbit`);
* `IsPerpBasis S Y Z`: the columns of $Z$ are a basis of $K^{\perp} = \{x \in N \mid B(K, x) = 0\}$;
* `perpIndex Y Z` $= [N : K \perp K^{\perp}]$;
* `countC p r S T Y` $= \#C_{p^r}(M_1, N; K)$ and `betaPK p S T Y` $= \beta_p(M_1, N; K)$;
* `countOrth p r S T₂ Y` $= \#\{\sigma_2 \in A_{p^r}(M_2, N) \mid B(K, \sigma_2(M_2)) \equiv 0 \bmod p^r\}$;
* statements `Lemma566`, `Lemma567`, `Lemma568`, `Theorem562`, `Corollary561` (all *stated*, none proved here).

**Not in the statements.** That the number of orbits of such submodules is finite is implicit in Kitaoka's "complete
set" and sums; the statements quantify over finite complete systems (index type with `Fintype`). Kitaoka's "for $r$
sufficiently large" is `∃ r₀, ∀ r ≥ r₀` (with $r_0$ depending on $M$, $N$ and the system).
-/
import QuadFormsKB.Literature.Kitaoka.Ch5Densities

open Matrix Filter

noncomputable section

namespace QuadFormsKB.Kitaoka.Density

/-- **The Gram matrix of $M_1 \perp M_2$**: the block diagonal matrix with blocks $T_1$ ($m_1 \times m_1$) and $T_2$
($m_2 \times m_2$), indexed by `Fin (m₁ + m₂)` (basis of $M_1$ first, then that of $M_2$). -/
def blockGram {p : ℕ} [Fact p.Prime] {m₁ m₂ : ℕ} (T₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[p])
    (T₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[p]) : Matrix (Fin (m₁ + m₂)) (Fin (m₁ + m₂)) ℤ_[p] :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks T₁ 0 0 T₂)

/-- **Same orbit under $O(N)$** (Kitaoka 1993, §5.6, p. 105): the submodules $K = YR^{m_1}$ and $K' = Y'R^{m_1}$ of
$N$ (Gram matrix $S$) are transformed into each other by an isometry of $N$, i.e. there are $A \in \mathrm{GL}_n(R)$
with $A^{\mathsf T} S A = S$ and $G \in \mathrm{GL}_{m_1}(R)$ with $AY = Y'G$. -/
def SameOrbit {p : ℕ} [Fact p.Prime] {n m₁ : ℕ} (S : Matrix (Fin n) (Fin n) ℤ_[p])
    (Y Y' : Matrix (Fin n) (Fin m₁) ℤ_[p]) : Prop :=
  ∃ (A : Matrix (Fin n) (Fin n) ℤ_[p]) (G : Matrix (Fin m₁) (Fin m₁) ℤ_[p]),
    IsUnit A ∧ Aᵀ * S * A = S ∧ IsUnit G ∧ A * Y = Y' * G

/-- **A complete system of submodules isometric to $M_1$ modulo $O(N)$** (Kitaoka 1993, Theorem 5.6.2, p. 107): the
matrices $Y_i$ ($i$ in a finite index type) satisfy $Y_i^{\mathsf T} S Y_i = T_1$ (the columns span a submodule $K_i$ of
$N$ isometric to $M_1$), no two different $i$ are in the same orbit under $O(N)$, and every matrix $Y'$ with
$Y'^{\mathsf T} S Y' = T_1$ is in the orbit of some $Y_i$. -/
def IsClassSystem {p : ℕ} [Fact p.Prime] {n m₁ : ℕ} {ι : Type} (S : Matrix (Fin n) (Fin n) ℤ_[p])
    (T₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[p]) (Y : ι → Matrix (Fin n) (Fin m₁) ℤ_[p]) : Prop :=
  (∀ i, (Y i)ᵀ * S * Y i = T₁) ∧ (∀ i j, SameOrbit S (Y i) (Y j) → i = j) ∧
    ∀ Y' : Matrix (Fin n) (Fin m₁) ℤ_[p], Y'ᵀ * S * Y' = T₁ → ∃ i, SameOrbit S (Y i) Y'

/-- **A basis matrix of $K^{\perp}$** (Kitaoka 1993, proof of Lemma 5.6.8, p. 106): $K = YR^{m_1} \subseteq N = R^n$
with Gram matrix $S$; the columns of $Z \in M_{n,k}(R)$ are linearly independent and span
$K^{\perp} = N \cap FK^{\perp} = \{x \in R^n \mid Y^{\mathsf T} S x = 0\}$ (the Gram matrix of $K^{\perp}$ is then
$Z^{\mathsf T} S Z$, of size $k \times k$). -/
def IsPerpBasis {p : ℕ} [Fact p.Prime] {n m₁ k : ℕ} (S : Matrix (Fin n) (Fin n) ℤ_[p])
    (Y : Matrix (Fin n) (Fin m₁) ℤ_[p]) (Z : Matrix (Fin n) (Fin k) ℤ_[p]) : Prop :=
  Function.Injective Z.mulVecLin ∧ colSpan Z = LinearMap.ker (Yᵀ * S).mulVecLin

/-- **The index $[N : K \perp K^{\perp}]$** (Kitaoka 1993, Lemma 5.6.8, p. 106) for $K = YR^{m_1}$ and
$K^{\perp} = ZR^k$: the index in $N = R^n$ of the submodule spanned by the columns of $Y$ and $Z$ (Lean's `index`,
which is $0$ if it were infinite; it is finite when $Y$ and $Z$ together have rank $n$). -/
def perpIndex {p : ℕ} [Fact p.Prime] {n m₁ k : ℕ} (Y : Matrix (Fin n) (Fin m₁) ℤ_[p])
    (Z : Matrix (Fin n) (Fin k) ℤ_[p]) : ℕ :=
  (colSpan Y ⊔ colSpan Z).toAddSubgroup.index

/-- **$\#C_{p^r}(M_1, N; K)$** (Kitaoka 1993, §5.6, p. 105, matrix form): the number of
$X \in M_{n,m_1}(R/p^rR)$ with $S[X] \equiv T \bmod p^rE_{m_1}$ (diagonal entries modulo $2p^r$, the others modulo
$p^r$; see `countA`) such that there are $A \in \mathrm{GL}_n(R)$ with $S[A] = S$ and $G \in \mathrm{GL}_{m_1}(R)$ with
$AY = XG$, where $K = YR^{m_1}$, $Y^{\mathsf T} S Y = T$ and $X$ is represented by $0, \dots, p^r - 1$. (The set is
the set of $\sigma : M_1 \to N/p^rN$ with $Q(\sigma(x)) \equiv Q(x) \bmod 2p^r$ for which a lift $\sigma'$ has
$\eta(K) = R[\sigma'(m_0), \dots]$ for some $\eta \in O(N)$; Kitaoka notes it is independent of the lifts for large
$r$.) -/
@[kb "kitaoka1993" "§5.6, p. 105 (C_{p^r}(M, N; K))"]
def countC (p : ℕ) [Fact p.Prime] {n m₁ : ℕ} (r : ℕ) (S : Matrix (Fin n) (Fin n) ℤ_[p])
    (T : Matrix (Fin m₁) (Fin m₁) ℤ_[p]) (Y : Matrix (Fin n) (Fin m₁) ℤ_[p]) : ℕ :=
  Nat.card {X : Matrix (Fin n) (Fin m₁) (Fin (p ^ r)) //
    (∀ i j, ((p : ℤ_[p]) ^ r * if i = j then 2 else 1) ∣ ((liftRes p r X)ᵀ * S * liftRes p r X - T) i j) ∧
    ∃ (A : Matrix (Fin n) (Fin n) ℤ_[p]) (G : Matrix (Fin m₁) (Fin m₁) ℤ_[p]),
      IsUnit A ∧ Aᵀ * S * A = S ∧ IsUnit G ∧ A * Y = liftRes p r X * G}

/-- **The density $\beta_p(M_1, N; K)$** (Kitaoka 1993, Lemma 5.6.6, p. 105): for $K = YR^{m_1}$,
$\lim_{r\to\infty}(p^r)^{m_1(m_1+1)/2 - m_1 n}\#C_{p^r}(M_1, N; K)$ (Lean's `limUnder`; Lemma 5.6.6 says the sequence
is eventually constant). -/
@[kb "kitaoka1993" "§5.6, Lemma 5.6.6, p. 105 (β_p(M, N; K))"]
def betaPK (p : ℕ) [Fact p.Prime] {n m₁ : ℕ} (S : Matrix (Fin n) (Fin n) ℤ_[p])
    (T : Matrix (Fin m₁) (Fin m₁) ℤ_[p]) (Y : Matrix (Fin n) (Fin m₁) ℤ_[p]) : ℝ :=
  limUnder atTop fun r : ℕ =>
    ((p : ℝ) ^ r) ^ (((m₁ * (m₁ + 1) / 2 : ℕ) : ℤ) - (m₁ : ℤ) * n) * (countC p r S T Y : ℝ)

/-- **$\#\{\sigma_2 \in A_{p^r}(M_2, N) \mid B(K, \sigma_2(M_2)) \equiv 0 \bmod p^r\}$** (Kitaoka 1993, Lemma 5.6.7,
p. 105): the number of $X \in M_{n,m_2}(R/p^rR)$ with $S[X] \equiv T_2 \bmod p^rE_{m_2}$ and
$Y^{\mathsf T} S X \equiv 0 \bmod p^r$ (every entry), where $K = YR^{m_1}$; $X$ is represented by
$0, \dots, p^r - 1$. For $m_2 = 0$ the count is $1$. -/
@[kb "kitaoka1993" "§5.6, Lemma 5.6.7, p. 105 (orthogonality count)"]
def countOrth (p : ℕ) [Fact p.Prime] {n m₁ m₂ : ℕ} (r : ℕ) (S : Matrix (Fin n) (Fin n) ℤ_[p])
    (T₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[p]) (Y : Matrix (Fin n) (Fin m₁) ℤ_[p]) : ℕ :=
  Nat.card {X : Matrix (Fin n) (Fin m₂) (Fin (p ^ r)) //
    (∀ i j, ((p : ℤ_[p]) ^ r * if i = j then 2 else 1) ∣ ((liftRes p r X)ᵀ * S * liftRes p r X - T₂) i j) ∧
    ∀ i j, (p : ℤ_[p]) ^ r ∣ (Yᵀ * S * liftRes p r X) i j}

/-- **Kitaoka 1993, Lemma 5.6.6** (p. 105), *stated*: let $N$, $M_1$ be regular lattices over $\mathbb Z_p$ with
integral Gram matrices $S$ ($n \times n$) and $T$ ($m_1 \times m_1$), and $K = YR^{m_1}$ a submodule of $N$ isometric
to $M_1$ ($Y^{\mathsf T} S Y = T$). Then
$\beta_p(M_1, N; K) = (p^r)^{m_1(m_1+1)/2 - m_1 n}\#C_{p^r}(M_1, N; K)$ is independent of $r$ for $r$ sufficiently
large: there is $r_0$ with the expression equal for $r$ and $r + 1$ whenever $r \ge r_0$. -/
@[kb "kitaoka1993" "§5.6, Lemma 5.6.6, p. 105"]
def Lemma566 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n m₁ : ℕ) (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T : Matrix (Fin m₁) (Fin m₁) ℤ_[p])
    (Y : Matrix (Fin n) (Fin m₁) ℤ_[p]),
    IsRegGram S → IsRegGram T → Yᵀ * S * Y = T →
    ∃ r₀ : ℕ, ∀ r ≥ r₀,
      ((p : ℝ) ^ r) ^ (((m₁ * (m₁ + 1) / 2 : ℕ) : ℤ) - (m₁ : ℤ) * n) * (countC p r S T Y : ℝ) =
      ((p : ℝ) ^ (r + 1)) ^ (((m₁ * (m₁ + 1) / 2 : ℕ) : ℤ) - (m₁ : ℤ) * n) * (countC p (r + 1) S T Y : ℝ)

/-- **Kitaoka 1993, Lemma 5.6.7** (pp. 105–106), *stated*: let $M = M_1 \perp M_2$ with $m_1 = \operatorname{rank} M_1
> 0$, $N$ regular with integral Gram matrices $S$, $T_1$, $T_2$, and let $(K_i)_{i \in \iota}$ (matrices $Y_i$,
`IsClassSystem`) be a complete set of submodules of $N$ isometric to $M_1$ not transformed into each other by
$O(N)$. Then for $r$ sufficiently large
$$\#A_{p^r}(M, N) = \sum_i \#C_{p^r}(M_1, N; K_i)\cdot
\#\{\sigma_2 \in A_{p^r}(M_2, N) \mid B(K_i, \sigma_2(M_2)) \equiv 0 \bmod p^r\},$$
with the second factor equal to $1$ when $M_2 = 0$. -/
@[kb "kitaoka1993" "§5.6, Lemma 5.6.7, pp. 105-106"]
def Lemma567 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n m₁ m₂ : ℕ) (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[p])
    (T₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[p]) (ι : Type) [Fintype ι] (Y : ι → Matrix (Fin n) (Fin m₁) ℤ_[p]),
    0 < m₁ → IsRegGram S → IsRegGram T₁ → IsRegGram T₂ → IsClassSystem S T₁ Y →
    ∃ r₀ : ℕ, ∀ r ≥ r₀,
      countA p r S (blockGram T₁ T₂) = ∑ i, countC p r S T₁ (Y i) * countOrth p r S T₂ (Y i)

/-- **Kitaoka 1993, Lemma 5.6.8** (p. 106), *stated*: let $N$ be regular with integral Gram matrix $S$, $K = YR^{m_1}
\subseteq N$ isometric to $M_1$ ($Y^{\mathsf T} S Y = T_1$, $m_1 > 0$), $K^{\perp} = ZR^k$ (`IsPerpBasis`) and $M_2$
with integral Gram matrix $T_2$. For $r$ sufficiently large
$$\#\{\sigma_2 \in A_{p^r}(M_2, N) \mid B(K, \sigma_2(M_2)) \equiv 0 \bmod p^r\} =
\Bigl(\frac{[K^{\#} : K]}{[N : K \perp K^{\perp}]}\Bigr)^{m_2}\#A_{p^r}(M_2, K^{\perp}),$$
where $[K^{\#} : K] = |\det T_1|_p^{-1}$ and $A_{p^r}(M_2, K^{\perp})$ is counted with the Gram matrix
$Z^{\mathsf T} S Z$ of $K^{\perp}$. (The statement is read with $K^{\#}$ the dual lattice of $K$ in $FK$, as the proof
on pp. 106–107 shows; the OCR of the printed statement is damaged.) -/
@[kb "kitaoka1993" "§5.6, Lemma 5.6.8, p. 106"]
def Lemma568 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n m₁ m₂ k : ℕ) (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[p])
    (T₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[p]) (Y : Matrix (Fin n) (Fin m₁) ℤ_[p]) (Z : Matrix (Fin n) (Fin k) ℤ_[p]),
    0 < m₁ → IsRegGram S → IsRegGram T₁ → IsRegGram T₂ → Yᵀ * S * Y = T₁ → IsPerpBasis S Y Z →
    ∃ r₀ : ℕ, ∀ r ≥ r₀,
      (countOrth p r S T₂ Y : ℝ) =
        (‖T₁.det‖⁻¹ / (perpIndex Y Z : ℝ)) ^ m₂ * (countA p r (Zᵀ * S * Z) T₂ : ℝ)

/-- **Kitaoka 1993, Theorem 5.6.2** (second reduction; p. 107), *stated*: let $M = M_1 \perp M_2$ and $N$ be regular
quadratic lattices over $\mathbb Z_p$ with $m_i = \operatorname{rank} M_i > 0$ and integral scales (Gram matrices $S$,
$T_1$, $T_2$ integral), and let $(K_i)_{i\in\iota}$ (`IsClassSystem`, matrices $Y_i$) be a complete set of submodules of
$N$ isometric to $M_1$ not transformed into each other by $O(N)$; $K_i^{\perp} = Z_iR^k$ (`IsPerpBasis`). Then
$$\beta_p(M, N) = \sum_i \Bigl(\frac{[M_1^{\#} : M_1]}{[N : K_i \perp K_i^{\perp}]}\Bigr)^{m_2}
\beta_p(M_1, N; K_i)\,\beta_p(M_2, K_i^{\perp}),$$
with $[M_1^{\#} : M_1] = |\det T_1|_p^{-1}$ and $\beta_p(M_2, K_i^{\perp})$ computed with the Gram matrix
$Z_i^{\mathsf T} S Z_i$. *Deviation:* the book requires $m_2 > 0$ for the theorem and adds the convention
$\beta_p(M_2, K_i^{\perp}) = 1$ if $m_2 = 0$; here $m_2 \ge 0$ is allowed, and for $m_2 = 0$ that value holds by the
definition `betaP` (count $1$, exponent $0$). -/
@[kb "kitaoka1993" "§5.6, Theorem 5.6.2, p. 107"]
def Theorem562 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n m₁ m₂ k : ℕ) (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[p])
    (T₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[p]) (ι : Type) [Fintype ι] (Y : ι → Matrix (Fin n) (Fin m₁) ℤ_[p])
    (Z : ι → Matrix (Fin n) (Fin k) ℤ_[p]),
    0 < m₁ → IsRegGram S → IsRegGram T₁ → IsRegGram T₂ → IsClassSystem S T₁ Y → (∀ i, IsPerpBasis S (Y i) (Z i)) →
    betaP p S (blockGram T₁ T₂) =
      ∑ i, (‖T₁.det‖⁻¹ / (perpIndex (Y i) (Z i) : ℝ)) ^ m₂ * betaPK p S T₁ (Y i) *
        betaP p ((Z i)ᵀ * S * Z i) T₂

/-- **Kitaoka 1993, Corollary 5.6.1** (p. 108), *stated*: in the situation of Theorem 5.6.2, assume that all
submodules of $N$ isometric to $M_1$ are transformed into each other by $O(N)$ (any two matrices $Y, Y'$ with
$Y^{\mathsf T} S Y = Y'^{\mathsf T} S Y' = T_1$ satisfy `SameOrbit`). Then, for a submodule $K = YR^{m_1}$ of $N$
isometric to $M_1$ and $K^{\perp} = ZR^k$,
$$\beta_p(M, N) = \Bigl(\frac{[M_1^{\#} : M_1]}{[N : K \perp K^{\perp}]}\Bigr)^{m_2}
\beta_p(M_1, N)\,\beta_p(M_2, K^{\perp}),$$
with $[M_1^{\#} : M_1] = |\det T_1|_p^{-1}$. (Here $m_2 \ge 0$ is allowed, as in `Theorem562`.) -/
@[kb "kitaoka1993" "§5.6, Cor. 5.6.1, p. 108"]
def Corollary561 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n m₁ m₂ k : ℕ) (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[p])
    (T₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[p]) (Y : Matrix (Fin n) (Fin m₁) ℤ_[p]) (Z : Matrix (Fin n) (Fin k) ℤ_[p]),
    0 < m₁ → IsRegGram S → IsRegGram T₁ → IsRegGram T₂ → Yᵀ * S * Y = T₁ → IsPerpBasis S Y Z →
    (∀ Y' Y'' : Matrix (Fin n) (Fin m₁) ℤ_[p], Y'ᵀ * S * Y' = T₁ → Y''ᵀ * S * Y'' = T₁ → SameOrbit S Y' Y'') →
    betaP p S (blockGram T₁ T₂) =
      (‖T₁.det‖⁻¹ / (perpIndex Y Z : ℝ)) ^ m₂ * betaP p S T₁ * betaP p (Zᵀ * S * Z) T₂

end QuadFormsKB.Kitaoka.Density
