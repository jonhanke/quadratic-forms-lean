import QuadFormsKB.Historical.Gauss.TransformationsFinite
import Mathlib.NumberTheory.Pell

/-!
# Infinitely many transformations when the determinant is positive and nonsquare (Art. 214)

(Gauss, *Disq. Arith.* Art. 214, closing remark).

`TransformationsFinite.lean` proves that the set of proper transformations of Gauss's form $(a, b, c)$ into a form
$F$ is finite when the determinant $D = b^2 - ac$ is negative or a nonzero square, and exhibits infinitely many
for $D = 0$ and $D = 2$. This file proves Gauss's remaining assertion: **if $D > 0$ is not a square and one proper
transformation of $(a, b, c)$ into $F$ exists, then there are infinitely many.**

* `gauss_properTransformations_infinite_of_gaussDet_pos_nonsq`: the theorem (proved, unconditional).

Proof: a nontrivial solution $(t, u)$ of $t^2 - D u^2 = 1$ exists (Mathlib `Pell.Solution₁`), and its powers give
infinitely many solutions $(t_n, u_n)$ with $t_n$ strictly increasing. Each yields the proper automorph
$(t - bu,\ -cu,\ au,\ t + bu)$ of $(a, b, c)$ (Art. 162, here `private` lemmas `gaussAutomorph_*`); composing
with the given transformation $T$ (first the automorph, then $T$, via `subst_subst`) gives proper transformations
of $(a, b, c)$ into $F$, pairwise distinct because $T$ has determinant $1$ and so can be cancelled.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary

/-- The automorph $(t - bu, -cu, au, t + bu)$ of $(a, b, c)$ attached to a solution of $t^2 - Du^2 = 1$ has
determinant $1$. -/
private theorem gaussAutomorph_det (a b c t u : ℤ) (hu : t ^ 2 - (b ^ 2 - a * c) * u ^ 2 = 1) :
    (t - b * u) * (t + b * u) - (-c * u) * (a * u) = 1 := by
  linear_combination hu

/-- The automorph carries $(a, b, c)$ into itself. -/
private theorem gaussAutomorph_subst (a b c t u : ℤ) (hu : t ^ 2 - (b ^ 2 - a * c) * u ^ 2 = 1) :
    subst (t - b * u) (-c * u) (a * u) (t + b * u) (gaussForm a b c) = gaussForm a b c := by
  apply ext_eval; intro x y
  simp only [eval_subst, eval_gaussForm]
  linear_combination (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) * hu

/-- Distinct values of $t$ give distinct composites with a fixed substitution of determinant $1$. -/
private theorem gaussAutomorph_comp_inj {α β γ δ : ℤ} (hdet : α * δ - β * γ = 1)
    {p q r s p' q' r' s' : ℤ}
    (h1 : p * α + q * γ = p' * α + q' * γ) (h2 : p * β + q * δ = p' * β + q' * δ)
    (h3 : r * α + s * γ = r' * α + s' * γ) (h4 : r * β + s * δ = r' * β + s' * δ) :
    p = p' ∧ s = s' := by
  constructor
  · linear_combination δ * h1 - γ * h2 - (p - p') * hdet
  · linear_combination (-β) * h3 + α * h4 - (s - s') * hdet

/-- **Infinitely many proper transformations when $D > 0$ is not a square** (Gauss, *Disq. Arith.* Art. 214,
closing remark): if the determinant $D = b^2 - ac$ of Gauss's form
$(a, b, c)$ is positive and not a perfect square, and some proper transformation of $(a, b, c)$ into the form $F$
exists, then there are infinitely many proper transformations of $(a, b, c)$ into $F$.

Together with `gauss_properTransformations_finite_of_gaussDet_neg` and `gauss_properTransformations_finite_of_gaussDet_sq`
this completes Gauss's dichotomy for $D \ne 0$ (for $D = 0$ both behaviours occur,
`properTransformations_infinite_gaussDet_zero`). Proved from Mathlib's Pell equation theory
(`Pell.Solution₁`): the automorphs $(t - bu, -cu, au, t + bu)$ ($t^2 - Du^2 = 1$) composed with a given
transformation. No difference from the source (Gauss refers to Arts. 202-205 and 162 for the solutions and the
automorphs; the hypothesis "one transformation exists" is his). -/
@[kb "gauss1801" "Art. 214, closing remark"]
theorem gauss_properTransformations_infinite_of_gaussDet_pos_nonsq (a b c : ℤ) (F : BinQF)
    (hD : 0 < gaussDet a b c) (hns : ¬ IsSquare (gaussDet a b c))
    (hne : (properTransformationsInto (gaussForm a b c) F).Nonempty) :
    (properTransformationsInto (gaussForm a b c) F).Infinite := by
  obtain ⟨⟨α, β, γ, δ⟩, hdet, hT⟩ := hne
  have hdet' : α * δ - β * γ = 1 := hdet
  have hT' : subst α β γ δ (gaussForm a b c) = F := hT
  obtain ⟨s, hsx, hsy⟩ := Pell.Solution₁.exists_pos_of_not_isSquare hD hns
  have hpos : ∀ n : ℕ, 0 < (s ^ n).x ∧ 0 ≤ (s ^ n).y := by
    intro n
    refine ⟨Pell.Solution₁.x_pow_pos (by omega) n, ?_⟩
    cases n with
    | zero => simp
    | succ n => exact (Pell.Solution₁.y_pow_succ_pos (by omega) hsy n).le
  have hmono : StrictMono (fun n : ℕ => (s ^ n).x) := by
    apply strictMono_nat_of_lt_succ
    intro n
    obtain ⟨h1, h2⟩ := hpos n
    show (s ^ n).x < (s ^ (n + 1)).x
    rw [pow_succ, Pell.Solution₁.x_mul]
    have : 0 ≤ gaussDet a b c * ((s ^ n).y * s.y) := by positivity
    nlinarith
  let A : ℕ → ℤ × ℤ × ℤ × ℤ := fun n =>
    let t := (s ^ n).x
    let u := (s ^ n).y
    (t - b * u, -c * u, a * u, t + b * u)
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ =>
      (((A n).1 * α + (A n).2.1 * γ, (A n).1 * β + (A n).2.1 * δ,
        (A n).2.2.1 * α + (A n).2.2.2 * γ, (A n).2.2.1 * β + (A n).2.2.2 * δ) : ℤ × ℤ × ℤ × ℤ))
    ?_ ?_
  · intro m n h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    obtain ⟨e1, e2⟩ := gaussAutomorph_comp_inj hdet' h1 h2 h3 h4
    apply hmono.injective
    show (s ^ m).x = (s ^ n).x
    simp only [A] at e1 e2
    linarith
  · intro n
    have hu : (s ^ n).x ^ 2 - (b ^ 2 - a * c) * (s ^ n).y ^ 2 = 1 := (s ^ n).prop
    have hA := gaussAutomorph_det a b c _ _ hu
    have e := gaussAutomorph_subst a b c _ _ hu
    refine ⟨?_, ?_⟩
    · show _ * _ - _ * _ = 1
      simp only [A]
      linear_combination (α * δ - β * γ) * hA + hdet'
    · show subst _ _ _ _ (gaussForm a b c) = F
      rw [← hT']
      exact (subst_subst _ _ _ _ α β γ δ (gaussForm a b c)).symm.trans (congrArg (subst α β γ δ) e)

end QuadFormsKB.Historical.Gauss