/-
# Cassels, Chapter 6, §2: the Weak Hasse Principle from the Strong one

Cassels' §2 (pp. 77–78, item 6.p1) deduces Theorem 1.2 (Weak Hasse Principle) from Theorem 1.1 (Strong Hasse
Principle): by induction on $n$, $f$ and $g$ represent a common $e \ne 0$ over $\mathbb Q$ (Ch. 2, Lemma 2.3, applied to
$f(\vec x) - g(\vec y)$, which is isotropic over every $\mathbb Q_p$ and hence over $\mathbb Q$),
$f \cong \langle e\rangle \perp f_1$, $g \cong \langle e\rangle \perp g_1$, and Witt's cancellation gives
$f_1 \cong g_1$ over every $\mathbb Q_p$.

The library's `isometric_of_everywhere` (`Literature/LocalGlobal/HasseMinkowski.lean`, the "⇐" half of
`isometric_iff_everywhere`) is this argument: the common value is a diagonal coefficient $b$ of $g$, represented by $f$
over $\mathbb Q$ by `represents_iff_everywhere` (the Strong Hasse Principle for $f \perp \langle -b\rangle$, i.e.
Corollary 2 to Theorem 1.1), then `QuadForm.exists_isometric_diag_cons`, Witt cancellation at each place
(`QuadForm.isometricIn_of_diag_cons`) and induction. It is cited here; the file where it lives is unchanged.
-/
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski

namespace QuadFormsKB

attribute [kb "cassels1978" "Ch. 6, §2, pp. 77–78 (proof of Thm. 1.2 from Thm. 1.1: a common value, Witt cancellation, induction)"]
  isometric_of_everywhere

end QuadFormsKB
