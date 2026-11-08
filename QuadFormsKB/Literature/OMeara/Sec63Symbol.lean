/-
# O'Meara §63B: $(\alpha, 1 - \alpha) = 1$

**Layer:** any field $K$; the Hilbert symbol `hilbertSymbol K a b` ($= 1$ iff $z^2 = ax^2 + by^2$ has a non-zero
solution in $K$; O'Meara's $(\alpha, \beta)_\mathfrak p$ over a local field, §63B).

**Proves**
* `hilbertSymbol_one_sub` (§63B, p. 166, the formula $(\alpha, 1 - \alpha) = 1$ of 57:10 for the symbol): the
  remaining formula of row 63.r18; $(1, \alpha) = (\alpha, -\alpha) = 1$, symmetry and invariance under squares are
  `hilbertSymbol_comm`, `hilbertSymbol_self_neg` and the `PadicClass` lemmas.
-/
import QuadFormsKB.Defs.Hilbert
import QuadFormsKB.Citation

namespace QuadFormsKB

/-- **$(\alpha, 1 - \alpha) = 1$** (O'Meara 1973, §63B, p. 166, from 57:10; Serre, Ch. III, §1.1, Prop. 2 (iii) in
the form $(a, 1 - a) = 1$) over any field $K$: $z^2 = \alpha x^2 + (1 - \alpha)y^2$ has the solution
$x = y = z = 1$. -/
@[kb "omeara1963" "§63B, p. 166 ((α, 1 − α) = 1)"]
theorem hilbertSymbol_one_sub (K : Type*) [Field K] (a : K) : hilbertSymbol K a (1 - a) = 1 := by
  unfold hilbertSymbol
  split_ifs with h
  · rfl
  · exact absurd ⟨1, 1, 1, by simp, by ring⟩ h

end QuadFormsKB
