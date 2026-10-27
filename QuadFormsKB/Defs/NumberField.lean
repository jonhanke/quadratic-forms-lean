/-
# Places of a number field and local conditions (groundwork for #5)

For a number field $F$, the **places** of $F$ are its infinite places $w$ (archimedean
absolute values; Mathlib's `NumberField.InfinitePlace F`, completion $F_w \cong \mathbb{R}$ or
$\mathbb{C}$) and its finite places, the nonzero primes $\mathfrak{p}$ of $\mathcal{O}_F$
(Mathlib's `IsDedekindDomain.HeightOneSpectrum (𝓞 F)`, completion $F_{\mathfrak{p}}$ =
`adicCompletion F 𝔭`).

A quadratic form over $F$ is just `QuadForm F n` (`Defs/QuadForm.lean`); it is evaluated over
each completion $F_v$ by `evalIn`, since $F_v$ is an $F$-algebra. The Hilbert symbol is the
general `hilbertSymbol` over the field $F_v$.

This is the number-field version of `RatPlace` (`Defs/Rational.lean`). For $F = \mathbb{Q}$
the two agree (`Equiv/NumberFieldRat.lean`), so the $\mathbb{Q}$ results are the $F = \mathbb{Q}$
case of the statements here rather than a parallel copy.
-/
import Mathlib
import QuadFormsKB.Defs.QuadForm
import QuadFormsKB.Defs.Hilbert

open NumberField IsDedekindDomain

namespace QuadFormsKB

/-- **The places of a number field $F$:** an infinite place $w$ (an archimedean absolute
value; real or complex) or a finite place, i.e. a nonzero prime $\mathfrak{p}$ of the ring of
integers $\mathcal{O}_F$. -/
inductive NFPlace (F : Type) [Field F] [NumberField F]
  | infinite (w : InfinitePlace F)
  | finite (v : HeightOneSpectrum (𝓞 F))

namespace NFPlace

variable {F : Type} [Field F] [NumberField F]

/-- **A property at the place $v$ of $F$:** `atPlace P v` means $P$ holds over the completion
$F_v$, which is $F_w$ (`w.Completion`, isomorphic to $\mathbb{R}$ or $\mathbb{C}$) for an
infinite place and $F_{\mathfrak{p}}$ (`adicCompletion F 𝔭`) for a finite place. $P$ is a
predicate on fields $K$ with an $F$-algebra structure. -/
def atPlace (P : (K : Type) → [Field K] → [Algebra F K] → Prop) : NFPlace F → Prop
  | infinite w => P w.Completion
  | finite v => P (v.adicCompletion F)

/-- **A property everywhere locally:** $P$ holds over **every** completion $F_v$ of $F$, at all
infinite places and at all finite places. -/
def Everywhere (P : (K : Type) → [Field K] → [Algebra F K] → Prop) : Prop :=
  ∀ v : NFPlace F, atPlace P v

/-- **The local Hilbert symbol $(a,b)_v$** of $a, b \in F$ at the place $v$: the Hilbert symbol
over the completion $F_v$, with $a, b$ viewed in $F_v$. Solutions are sought **in $F_v$**, not
in $F$. -/
@[kb "omeara1963" "§63B, p. 164 (Hilbert symbol)"]
noncomputable def hilbert : NFPlace F → F → F → ℤ
  | infinite w, a, b => hilbertSymbol w.Completion (algebraMap F _ a) (algebraMap F _ b)
  | finite v, a, b => hilbertSymbol (v.adicCompletion F) (algebraMap F _ a) (algebraMap F _ b)

end NFPlace

end QuadFormsKB
