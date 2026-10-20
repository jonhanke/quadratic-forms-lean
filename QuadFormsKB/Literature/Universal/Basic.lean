/-
# Positive definite forms, representation, universality

Shared vocabulary for the universality results (15-Theorem, 290-Theorem), for **integral**
forms $Q$ (`IntQF n`, integer coefficients). Representation is by **integer** vectors
$\vec{x} \in \mathbb{Z}^n$.
-/
import QuadFormsKB.Defs.Integral

namespace QuadFormsKB

variable {n : ℕ}

/-- **Positive definite:** $Q(\vec{x}) > 0$ for every nonzero integer vector
$\vec{x} \in \mathbb{Z}^n$. (Equivalently over $\mathbb{R}$, by homogeneity and density; not
proved here. For $n = 0$ it holds vacuously.) -/
def IntQF.PosDef (Q : IntQF n) : Prop := ∀ x, x ≠ 0 → 0 < Q.eval x

/-- **$Q$ represents $m \in \mathbb{Z}$:** $Q(\vec{x}) = m$ for some **integer** vector
$\vec{x} \in \mathbb{Z}^n$. Every form represents $0$. -/
def IntQF.Represents (Q : IntQF n) (m : ℤ) : Prop := ∃ x, Q.eval x = m

/-- **Universal:** $Q$ represents every positive integer $m \ge 1$ (by integer vectors). -/
@[kb "conway1997" "Afterthoughts"]
def IntQF.Universal (Q : IntQF n) : Prop := ∀ m : ℤ, 0 < m → Q.Represents m

end QuadFormsKB
