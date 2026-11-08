/-
# O'Meara §103A: the counting number of a scalar

**Layer:** $F$ a number field, $\mathfrak o = \mathcal O_F$ (O'Meara's $S$ = all finite spots); fractional ideals
`FractionalIdeal (𝓞 F)⁰ F` with Mathlib's absolute norm `FractionalIdeal.absNorm` (values in $\mathbb Q$).

**Proves**
* `omeara103_r1` (§103A, p. 305): the counting number $N\alpha = N(\alpha\mathfrak o)$ is multiplicative,
  $N(\alpha\beta) = N\alpha\,N\beta$, and equals $\lvert N_{F/\mathbb Q}(\alpha)\rvert$. (O'Meara's formula
  $N\alpha = \prod_{\mathfrak p \in S}\lvert\alpha\rvert_\mathfrak p^{-1}$ is not stated separately.)
-/
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.NumberTheory.NumberField.Basic
import QuadFormsKB.Citation

open NumberField
open scoped nonZeroDivisors

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F]

/-- **The counting number of a scalar** (O'Meara 1973, §103A, p. 305): $N\alpha = N(\alpha\mathfrak o)$ (the absolute
norm of the principal fractional ideal $\alpha\mathfrak o$) satisfies $N(\alpha\beta) = N\alpha\,N\beta$, and
$N\alpha = \lvert N_{F/\mathbb Q}(\alpha)\rvert$. -/
@[kb "omeara1963" "§103A, p. 305 (the counting number Nα = N(α𝔬); N(αβ) = Nα Nβ)"]
theorem omeara103_r1 (α β : F) :
    FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 F)⁰ (α * β)) =
        FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 F)⁰ α) *
          FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 F)⁰ β) ∧
      FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 F)⁰ α) = |Algebra.norm ℚ α| := by
  refine ⟨?_, FractionalIdeal.absNorm_span_singleton (𝓞 F) α⟩
  simp only [map_mul]

end QuadFormsKB.Lattices
