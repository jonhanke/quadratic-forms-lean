/-
# Classical special cases over $\mathbb Q$: the forms and discriminants

**Layer:** $\mathbb Q$. Shared definitions for the classical specializations of the indefinite Siegel headlines.

**Defines**
* `qInd` $= x_0^2 + x_1^2 - x_2^2$ (indefinite ternary, $\det H = -8$);
* `sumTwoSqZ` $= x_0^2 + x_1^2$ (positive definite binary, discriminant $-4$) and `pell2Z` $= x_0^2 - 2x_1^2$ (indefinite
  binary, discriminant $8$), over $\mathbb Z$;
* `gaussDisc m`, the discriminant of $\mathbb Q(\sqrt{-m})$, and `realDisc m`, the discriminant of $\mathbb Q(\sqrt m)$,
  for squarefree $m$.
-/
import QuadFormsKB.Tamagawa.Indefinite.SiegelCorankOne
import QuadFormsKB.Tamagawa.Indefinite.SiegelTernary
import QuadFormsKB.Tamagawa.Indefinite.SiegelTernaryIso
import QuadFormsKB.Tamagawa.RatHeadline3Uncond

namespace QuadFormsKB.Tamagawa.Classical

/-- **$x_0^2 + x_1^2 - x_2^2$** over $\mathbb Z$ (Hessian $\mathrm{diag}(2, 2, -2)$, $\det H = -8$). -/
def qInd : QuadForm ℤ 3 := QuadForm.diag ![1, 1, -1]

/-- **$x_0^2 + x_1^2$** over $\mathbb Z$ (discriminant $-4$). -/
def sumTwoSqZ : QuadForm ℤ 2 := QuadForm.diag ![1, 1]

/-- **$x_0^2 - 2x_1^2$** over $\mathbb Z$ (discriminant $8$). -/
def pell2Z : QuadForm ℤ 2 := QuadForm.diag ![1, -2]

/-- **The discriminant of $\mathbb Q(\sqrt{-m})$** for squarefree $m \ge 1$: $-m$ if $m \equiv 3 \pmod 4$, else $-4m$.
Parameter: `m`. -/
def gaussDisc (m : ℤ) : ℤ := if m % 4 = 3 then -m else -4 * m

/-- **The discriminant of $\mathbb Q(\sqrt m)$** for squarefree $m \ne 1$ (of either sign): $m$ if $m \equiv 1 \pmod 4$,
else $4m$. Parameter: `m`. -/
def realDisc (m : ℤ) : ℤ := if m % 4 = 1 then m else 4 * m

end QuadFormsKB.Tamagawa.Classical
