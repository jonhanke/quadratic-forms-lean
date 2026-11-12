/-
# Kitaoka 1993, Theorems 7.1.3, 7.5.1, 7.5.2: rings of integers as lattices, scalar extension of positive lattices

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §7.1, Theorem 7.1.3, p. 195; §7.5, Theorems 7.5.1 and
7.5.2, pp. 242–243 (printed pages).

**Setting.** Positive lattices are Gram matrices as in `Ch7EType.lean`: $L = (\mathbb Z^n, A)$ with $A$ symmetric,
rational and positive definite (`EType.IsPosGram`). For a number field $K$ with ring of integers $R_K$ the scalar
extension $R_K L = R_K \otimes L$ carries the $K$-bilinear extension of $B$ (Kitaoka, §7.5), with Gram matrix $A$ in
the same basis, now over $R_K$. An isometry $\sigma : R_K L \cong R_K M$ is then a matrix $P \in \mathrm{GL}_n(R_K)$
($\det P$ a unit of $R_K$) with $P^{\mathsf T} B P = A$ over $K$, and $\sigma(L) = M$ means $P \in \mathrm{GL}_n(\mathbb Z)$.

For a totally real $K$, $(R_K, B_K)$ with $B_K(x, y) = \operatorname{tr}_{K/\mathbb Q}(xy)$ (Lemma 7.5.5, p. 241) is a
positive lattice; its Gram matrix in the integral basis $(b_i)$ (`NumberField.integralBasis`) is
$(\operatorname{tr}_{K/\mathbb Q}(b_i b_j))$ (`traceGram`).

**Defines** `traceGram K`, `IsScalarExtensionIsometry K A B P`; statements `Theorem713`, `Theorem751`, `Theorem752`
(stated).
-/
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.Trace.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.FieldTheory.Galois.Basic
import QuadFormsKB.Literature.Kitaoka.Ch7EType

open Matrix NumberField

noncomputable section

namespace QuadFormsKB.Kitaoka.EType

/-- **The Gram matrix of $(R_K, B_K)$**, $B_K(x, y) = \operatorname{tr}_{K/\mathbb Q}(xy)$ (Kitaoka 1993, Lemma 7.5.5,
p. 241), in the integral basis $(b_i)$ of $K$: $(\operatorname{tr}_{K/\mathbb Q}(b_i b_j))_{i,j}$. It is positive
definite when $K$ is totally real. -/
@[kb "kitaoka1993" "§7.5, p. 241 ((R_K, B_K), B_K(x, y) = tr(xy))"]
def traceGram (K : Type) [Field K] [NumberField K] :
    Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ℚ :=
  Matrix.of fun i j => Algebra.trace ℚ K (integralBasis K i * integralBasis K j)

/-- **An isometry $\sigma : R_K L \cong R_K M$** (Kitaoka 1993, §7.5, p. 242) for $L = (\mathbb Z^n, A)$,
$M = (\mathbb Z^n, B)$: a matrix $P$ over $R_K$ with $\det P \in R_K^\times$ and $P^{\mathsf T} B P = A$ over $K$. -/
def IsScalarExtensionIsometry (K : Type) [Field K] [NumberField K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ)
    (P : Matrix (Fin n) (Fin n) (𝓞 K)) : Prop :=
  IsUnit P.det ∧
    (P.map (algebraMap (𝓞 K) K))ᵀ * B.map (algebraMap ℚ K) * P.map (algebraMap (𝓞 K) K) = A.map (algebraMap ℚ K)

/-- **Kitaoka 1993, Theorem 7.1.3** (p. 195), *stated*: let $F$ be a finite abelian extension of $\mathbb Q$ and $R_F$
its ring of integers, with $B_F(x, y) = \operatorname{tr}_{F/\mathbb Q}(x\bar y)$ ($\bar y$ the complex conjugate).
Then $(R_F, B_F)$ is a positive lattice of E-type. Since $F$ is abelian, complex conjugation is an automorphism of $F$
and $\operatorname{tr}_{F/\mathbb Q}(x \bar y) = \sum_\tau \tau(x)\overline{\tau(y)}$, the sum over the embeddings
$\tau : F \to \mathbb C$; the statement says that the Gram matrix of $B_F$ in the integral basis $(b_i)$, computed by
this sum, is rational, positive definite and of E-type. -/
@[kb "kitaoka1993" "§7.1, Thm. 7.1.3, p. 195"]
def Theorem713 : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsGalois ℚ F], (∀ σ τ : F ≃ₐ[ℚ] F, σ * τ = τ * σ) →
    ∃ A : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) ℚ,
      (∀ i j, (A i j : ℂ) = ∑ τ : F →+* ℂ, τ (integralBasis F i) * starRingEnd ℂ (τ (integralBasis F j))) ∧
      IsPosGram A ∧ IsEType A

/-- **Kitaoka 1993, Theorem 7.5.1** (p. 242), *stated*: let $K/\mathbb Q$ be totally real. For positive lattices $L$,
$M$ (Gram matrices $A$, $B$), every isometry $\sigma : R_K L \cong R_K M$ satisfies $\sigma(L) = M$, provided
$\operatorname{rank} L = \operatorname{rank} M < 43$ or $(R_K, B_K)$ is of E-type. Both lattices are taken of the same
rank $n$ (an isometry forces it). -/
@[kb "kitaoka1993" "§7.5, Thm. 7.5.1, p. 242"]
def Theorem751 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], IsTotallyReal K →
    ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℚ), IsPosGram A → IsPosGram B → (n < 43 ∨ IsEType (traceGram K)) →
      ∀ P : Matrix (Fin n) (Fin n) (𝓞 K), IsScalarExtensionIsometry K A B P →
        ∃ P₀ : Matrix (Fin n) (Fin n) ℤ, P = P₀.map (Int.cast : ℤ → 𝓞 K)

/-- **Kitaoka 1993, Theorem 7.5.2** (p. 243), *stated*: let $K/\mathbb Q$ be a totally real nilpotent Galois extension
(the Galois group is nilpotent). Then for positive lattices $L$, $M$, every isometry $\sigma : R_K L \cong R_K M$
satisfies $\sigma(L) = M$. -/
@[kb "kitaoka1993" "§7.5, Thm. 7.5.2, p. 243"]
def Theorem752 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K], IsTotallyReal K → Group.IsNilpotent (K ≃ₐ[ℚ] K) →
    ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℚ), IsPosGram A → IsPosGram B →
      ∀ P : Matrix (Fin n) (Fin n) (𝓞 K), IsScalarExtensionIsometry K A B P →
        ∃ P₀ : Matrix (Fin n) (Fin n) ℤ, P = P₀.map (Int.cast : ℤ → 𝓞 K)

end QuadFormsKB.Kitaoka.EType
