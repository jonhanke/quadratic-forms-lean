/-
# Conway–Sloane, Ch. 15, §2.1: the two notions of integrality

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §2.1, p. 355
(`conwaysloane1999`): "if $f$ is integral in either sense then $2f$ is integral in the other, and $f \sim g$ if and only
if $2f \sim 2g$". In the library, "integral as a quadratic form" is `IntQF` (integer coefficients) and "integral as a
bilinear form" is `IsClassicallyIntegral`.

**Proves** `two_smul_isClassicallyIntegral` (in the library, tagged here),
`intEquiv_two_smul_iff` ($f \sim g \iff 2f \sim 2g$ over $\mathbb Z$).
-/
import QuadFormsKB.Equiv.Integral
import QuadFormsKB.Siegel.NeighborGenus

namespace QuadFormsKB.ConwaySloane

open Siegel

attribute [kb "conwaysloane1999" "Ch. 15, §2.1, p. 355 (2f is classically integral)"] two_smul_isClassicallyIntegral

/-- **$f \sim g \iff 2f \sim 2g$** (Conway–Sloane, §2.1, p. 355), for integral equivalence of integer forms. -/
@[kb "conwaysloane1999" "Ch. 15, §2.1, p. 355"]
theorem intEquiv_two_smul_iff {n : ℕ} (f g : QuadForm ℤ n) : IntEquiv ((2 : ℤ) • f) ((2 : ℤ) • g) ↔ IntEquiv f g := by
  constructor
  · rintro ⟨T, hT⟩
    refine ⟨T, fun x => ?_⟩
    have := hT x
    rw [Kneser.eval_smul_form, Kneser.eval_smul_form] at this
    exact mul_left_cancel₀ two_ne_zero this
  · rintro ⟨T, hT⟩
    exact ⟨T, fun x => by rw [Kneser.eval_smul_form, Kneser.eval_smul_form, hT x]⟩

end QuadFormsKB.ConwaySloane
