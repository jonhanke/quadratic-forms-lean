import QuadFormsKB.Literature.Cassels.Ch9Sec2
import QuadFormsKB.Literature.Cassels.Ch9Sec6

/-!
# Cassels, Chapter 13, §12: Problem 1 reduces to Problem 2

Cassels, *Rational Quadratic Forms* (1978), Ch. 13, §12, pp. 324–325, poses two decision problems for integral
forms $f$: **Problem 1**, does $f$ represent a given integer $b \ne 0$; **Problem 2**, are two integral forms
integrally equivalent (and if so, give an equivalence $T$). The book remarks that Problem 1 reduces to Problem 2
(Ch. 9, §6): $f$ represents $b$ primitively precisely when $f$ is integrally equivalent to a form $g$ with
$g(\vec e_0) = b$, since a primitive vector is the first column of a unimodular matrix (Ch. 9, §2). The
computability of the problems is not formalized; this file states the reduction.

Indices are 0-based: the book's first basis vector $\vec e_1$ is `Pi.single ⟨0, hn⟩ 1` here.
-/

open Matrix

namespace QuadFormsKB.Siegel

variable {n : ℕ}

/-- **Problem 1 reduces to Problem 2** (Cassels, Ch. 13, §12, pp. 324–325; Ch. 9, §6): for $n \ge 1$, an integral
form $f$ in $n$ variables primitively represents $b$ (some $\vec c \in \mathbb Z^n$ with
$\gcd(c_0, \dots, c_{n-1}) = 1$ and $f(\vec c) = b$) if and only if there is $T \in \mathrm{GL}_n(\mathbb Z)$ such
that the equivalent form $g(\vec x) = f(T\vec x)$ has $g(\vec e_0) = b$. -/
@[kb "cassels1978" "Ch. 13, §12, pp. 324–325 (Problem 1 reduces to Problem 2)"]
theorem primRepSet_nonempty_iff_exists_GL (hn : 0 < n) (f : QuadForm ℤ n) (b : ℤ) :
    (primRepSet f b).Nonempty ↔
      ∃ T : GL (Fin n) ℤ, f.eval (T.val *ᵥ Pi.single ⟨0, hn⟩ 1) = b := by
  constructor
  · rintro ⟨c, hc, hfc⟩
    obtain ⟨T, hT⟩ := (exists_basis_first_iff_gcd hn c).2 hc
    exact ⟨T, hT ▸ hfc⟩
  · rintro ⟨T, hT⟩
    exact ⟨_, (exists_basis_first_iff_gcd hn _).1 ⟨T, rfl⟩, hT⟩

end QuadFormsKB.Siegel
