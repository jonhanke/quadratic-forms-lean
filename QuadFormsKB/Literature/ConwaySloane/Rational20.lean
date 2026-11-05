/-
# Conway–Sloane, Ch. 15, §6.3: the equivalence (20)

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §6.3, (20), p. 377
(`conwaysloane1999`).

In the proof of Theorem 7, for an odd prime $p$ let $u = r + 1$ be the least positive non-residue mod $p$ (so $r$ is a
residue). The chain (20) replaces two $p$-terms $p, p$ by $p, pr$ (replacement lemma, Theorem 8, `replacement_lemma`),
then by $pu, pur$, then by $pu, pu$ (Theorem 8 again). The middle step is an equivalence over $\mathbb Q$, proved here
for all rationals: $\mathrm{diag}\{p, pr\}$ represents $p + pr = pu$, and $\mathrm{diag}\{p, pr\} \sim
\mathrm{diag}\{pu, pur\}$ via the basis $(1, 1)$, $(r, -1)$.
-/
import QuadFormsKB.Literature.ConwaySloane.Rational

namespace QuadFormsKB.ConwaySloane.Rational

open QuadForm

/-- **(20), the middle step** (Conway–Sloane, §6.3, p. 377): $\mathrm{diag}\{p, pr\} \sim \mathrm{diag}\{pu, pur\}$ over
$\mathbb Q$ when $u = r + 1 \ne 0$. -/
@[kb "conwaysloane1999" "Ch. 15, §6.3, (20), p. 377"]
theorem diag_p_pr_equiv (p r : ℚ) (hu : r + 1 ≠ 0) :
    (diag ![p, p * r]).IsometricIn ℚ (diag ![p * (r + 1), p * (r + 1) * r]) := by
  refine isometricIn_diag_two_mk _ _ _ _ 1 r 1 (-1) ?_ fun x0 x1 => ?_
  · intro h; apply hu; linarith
  · ring

/-- **(20), the represented number** (p. 377): $\mathrm{diag}\{p, pr\}$ represents $pu$, $u = r + 1$. -/
@[kb "conwaysloane1999" "Ch. 15, §6.3, (20), p. 377"]
theorem diag_p_pr_represents (p r : ℚ) : p * 1 ^ 2 + p * r * 1 ^ 2 = p * (r + 1) := by ring

end QuadFormsKB.ConwaySloane.Rational
