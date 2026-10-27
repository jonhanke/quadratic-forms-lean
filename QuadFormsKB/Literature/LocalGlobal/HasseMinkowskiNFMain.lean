/-
# Hasse–Minkowski over a number field: the main theorem

Assembles `hasseMinkowski_nf` from Lam's route (`hasseMinkowski_nf_of_lamInputs`, proved) and the two
inputs: squares local–global (proved, `SqLG.isSquare_iff_everywhere`) and the Hasse norm theorem
for quadratic extensions (our own proof, `HasseNorm.hilbert_eq_one_of_everywhere`; the
Yamaguchi-derived version, is archived in `archive/yamaguchi/` and no longer built). So
`hasseMinkowski_nf`, and the whole build, depends only on Mathlib and this repository.
-/
import QuadFormsKB.Literature.LocalGlobal.SquaresLocalGlobal
import QuadFormsKB.Literature.HasseNorm.Main

open NumberField

namespace QuadFormsKB

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **Lam's inputs hold:** squares local–global is our `SqLG.isSquare_iff_everywhere`; the
Hasse norm theorem is our `HasseNorm.hilbert_eq_one_of_everywhere` (Chevalley's algebraic second
inequality for $n = 2$). Both proved; no `sorry`, no imported class field theory. -/
@[kb "lam2005" "Ch. VI §3 [unverified]"]
theorem lamInputs : NFInputs.LamInputs :=
  ⟨fun _ _ _ a => SqLG.isSquare_iff_everywhere a,
    fun _ _ _ a b ha hb h => HasseNorm.hilbert_eq_one_of_everywhere a b ha hb h⟩

/-- **Hasse–Minkowski over a number field $F$:** a nondegenerate quadratic form over $F$ is
isotropic over $F$ iff it is isotropic over every completion $F_v$. This is
`hasseMinkowski_nf_of_lamInputs` applied to `lamInputs` (Lam's route): **fully proved**. It uses our
squares local–global theorem and our Hasse norm theorem for quadratic extensions; it no
longer depends on N. Yamaguchi's formalization. -/
@[kb "omeara1963" "§66:1 [unverified]"]
theorem hasseMinkowski_nf (Q : QuadForm F n) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn F ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.IsotropicIn K :=
  hasseMinkowski_nf_of_lamInputs lamInputs Q hQ

end QuadFormsKB
