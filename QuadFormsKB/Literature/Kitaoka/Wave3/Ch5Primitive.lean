/-
# Kitaoka 1993, §5.6: the primitive local density $d_p(M, N)$ and Siegel's reduction formula (Theorem 5.6.1)

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.6, definition of the primitive local density,
p. 100, and Theorem 5.6.1, pp. 101–103 (printed pages).

**Setting** (as in `Ch5Densities.lean`). $p$ is a prime, $R = \mathbb Z_p$, $S$ an integral symmetric $n \times n$
matrix (the Gram matrix of $N$), $T$ an integral symmetric $m \times m$ matrix (the Gram matrix of $M$). A matrix
$X \in M_{n,m}(R)$ is *primitive* when the map $M/pM \to N/pN$ it induces is injective, i.e. $X \bmod p$ has rank
$m$ over $\mathbb F_p$ (Kitaoka, p. 2: $X$ extends to an element of $\mathrm{GL}_n(R)$; for $R = \mathbb Z_p$ these
agree). Kitaoka shows (p. 100, last display) that for integral $S$, $T$
$$d_p(M, N) = \lim_{r\to\infty}(p^r)^{m(m+1)/2 - mn}\#\{X \in A_{p^r}(T, S) \mid X \text{ primitive}\}.$$

**Defines**
* `IsPrimMat X`: $X \bmod p$ has rank $m$ (Mathlib `Matrix.rank` over `ZMod p` of `X.map PadicInt.toZMod`);
* `countPrim p r S T` $= \#\{X \in A_{p^r}(T, S) \mid X \text{ primitive}\}$;
* `primDensity p S T` $= d_p(M, N)$ (Lean's `limUnder`; a junk value if the limit does not exist);
* `IsOverlatticeData T K T'`: $K \in M_m(R)$ with $\det K \ne 0$ and $T'$ integral symmetric with
  $K^{\mathsf T}T'K = T$; this is the overlattice $M' \supseteq M$ with basis $(m_0, \dots, m_{m-1})K^{-1}$, Gram
  matrix $T' = T[K^{-1}]$ and index $[M' : M] = |\det K|_p^{-1}$;
* `Theorem561` (**Siegel's reduction formula**, stated).

*Overlattices with non-integral Gram matrix.* Kitaoka sums over all lattices $M'$ with $FM \supseteq M' \supseteq M$.
When $S$ is integral, a lattice $M'$ whose Gram matrix $T[K^{-1}]$ is not integral is not represented by $N$, so
$d_p(M', N) = 0$ (Kitaoka, p. 103: "If $d_p(M', N) \ne 0$, then there is an isometry $\sigma : M' \to N$. Hence
$dM' \subseteq (\mathfrak s(N))^m$ …"). The statement below therefore sums over the overlattices with integral Gram
matrix only, which is where `primDensity` is defined; Kitaoka's proof in matrix form (p. 103) has the same range,
"$K$ ranges over regular matrices in $\mathrm{GL}_m(R)\backslash M_m(R)$ such that $T[K^{-1}]$ is integral".
-/
import QuadFormsKB.Literature.Kitaoka.Ch5Densities
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.NumberTheory.Padics.RingHoms

open Matrix Filter

noncomputable section

namespace QuadFormsKB.Kitaoka.Density

variable {m n : ℕ}

/-- **A primitive matrix** $X \in M_{n,m}(\mathbb Z_p)$ (Kitaoka 1993, p. 2 and §5.6, p. 100): $X \bmod p$ has rank
$m$, i.e. $X$ induces an injective map $M/pM \to N/pN$. -/
@[kb "kitaoka1993" "§5.6, p. 100 (primitive X)"]
def IsPrimMat (p : ℕ) [Fact p.Prime] (X : Matrix (Fin n) (Fin m) ℤ_[p]) : Prop :=
  (X.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)).rank = m

/-- **$\#\{X \in A_{p^r}(T, S) \mid X \text{ primitive}\}$** (Kitaoka 1993, §5.6, p. 100). -/
@[kb "kitaoka1993" "§5.6, p. 100 (primitive count)"]
def countPrim (p : ℕ) [Fact p.Prime] (r : ℕ) (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T : Matrix (Fin m) (Fin m) ℤ_[p]) :
    ℕ :=
  Nat.card {X : Matrix (Fin n) (Fin m) (Fin (p ^ r)) //
    (∀ i j, ((p : ℤ_[p]) ^ r * if i = j then 2 else 1) ∣ ((liftRes p r X)ᵀ * S * liftRes p r X - T) i j) ∧
      IsPrimMat p (liftRes p r X)}

/-- **The primitive local density** $d_p(M, N)$ (Kitaoka 1993, §5.6, p. 100) of the lattice $M$ with integral Gram
matrix $T$ in the lattice $N$ with integral Gram matrix $S$:
$\lim_{r\to\infty}(p^r)^{m(m+1)/2 - mn}\#\{X \in A_{p^r}(T, S) \mid X \text{ primitive}\}$ (Lean's `limUnder`). -/
@[kb "kitaoka1993" "§5.6, p. 100 (primitive local density d_p(M, N))"]
def primDensity (p : ℕ) [Fact p.Prime] (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T : Matrix (Fin m) (Fin m) ℤ_[p]) : ℝ :=
  limUnder atTop fun r : ℕ =>
    ((p : ℝ) ^ r) ^ (((m * (m + 1) / 2 : ℕ) : ℤ) - (m : ℤ) * n) * (countPrim p r S T : ℝ)

/-- **An overlattice of $M$ with integral Gram matrix** (Kitaoka 1993, proof of Theorem 5.6.1, p. 103): $K$ is a
regular integral $m \times m$ matrix and $T'$ an integral symmetric matrix with $K^{\mathsf T}T'K = T$. It describes
the lattice $M' = (m_0, \dots, m_{m-1})K^{-1}R^m \supseteq M$ on $FM$, with Gram matrix $T' = T[K^{-1}]$ and
$[M' : M] = |\det K|_p^{-1}$. -/
def IsOverlatticeData {p : ℕ} [Fact p.Prime] (T K T' : Matrix (Fin m) (Fin m) ℤ_[p]) : Prop :=
  K.det ≠ 0 ∧ T'ᵀ = T' ∧ Kᵀ * T' * K = T

/-- Two overlattice data give the same lattice $M'$ exactly when $K_2 = UK_1$ for some $U \in \mathrm{GL}_m(R)$
($K$ is determined by $M'$ up to the left action of $\mathrm{GL}_m(R)$). -/
def SameOverlattice {p : ℕ} [Fact p.Prime] (K₁ K₂ : Matrix (Fin m) (Fin m) ℤ_[p]) : Prop :=
  ∃ U : Matrix (Fin m) (Fin m) ℤ_[p], IsUnit U ∧ K₂ = U * K₁

/-- **Kitaoka 1993, Theorem 5.6.1** (Siegel; p. 101), *stated*: for regular quadratic lattices $M$, $N$ over
$\mathbb Z_p$ with $m = \operatorname{rank} M \le n = \operatorname{rank} N$,
$$\beta_p(M, N) = \sum_{FM \supseteq M' \supseteq M} [M' : M]^{m+1-n}\, d_p(M', N),$$
and the summation on $M'$ is finite.

*Encoding.* Gram matrices $T$ (of $M$) and $S$ (of $N$) are integral (Kitaoka: "we may suppose that $S$ and $T$ are
integral by scaling"). The lattices $M'$ with integral Gram matrix are described by `IsOverlatticeData T K T'` up to
`SameOverlattice` (see the module docstring for why the others contribute $0$). The statement has two parts:
(finiteness) there is a finite complete system of such data, pairwise distinct lattices; (formula) for *every* finite
complete system $(K_i, T'_i)_{i \in \iota}$ of pairwise distinct lattices,
$\beta_p(M, N) = \sum_i |\det K_i|_p^{-(m+1-n)}\, d_p(M'_i, N)$, where $d_p(M'_i, N)$ = `primDensity p S (T' i)`. -/
@[kb "kitaoka1993" "§5.6, Thm. 5.6.1, p. 101"]
def Theorem561 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (m n : ℕ) (T : Matrix (Fin m) (Fin m) ℤ_[p]) (S : Matrix (Fin n) (Fin n) ℤ_[p]),
    m ≤ n → IsRegGram T → IsRegGram S →
    (∃ (ι : Type) (_ : Fintype ι) (K T' : ι → Matrix (Fin m) (Fin m) ℤ_[p]),
      (∀ i, IsOverlatticeData T (K i) (T' i)) ∧ (∀ i j, SameOverlattice (K i) (K j) → i = j) ∧
      ∀ K₀ T₀ : Matrix (Fin m) (Fin m) ℤ_[p], IsOverlatticeData T K₀ T₀ → ∃ i, SameOverlattice (K i) K₀) ∧
    ∀ (ι : Type) [Fintype ι] (K T' : ι → Matrix (Fin m) (Fin m) ℤ_[p]),
      (∀ i, IsOverlatticeData T (K i) (T' i)) → (∀ i j, SameOverlattice (K i) (K j) → i = j) →
      (∀ K₀ T₀ : Matrix (Fin m) (Fin m) ℤ_[p], IsOverlatticeData T K₀ T₀ → ∃ i, SameOverlattice (K i) K₀) →
      betaP p S T = ∑ i, ‖(K i).det‖⁻¹ ^ ((m : ℤ) + 1 - n) * primDensity p S (T' i)

end QuadFormsKB.Kitaoka.Density
