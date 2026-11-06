/-
# Cassels, Chapter 14, §3: $p$-adic binary forms are improperly equivalent to themselves

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §3, p. 339: "every $p$-adic binary form is improperly
$\mathbb Z_p$-equivalent to itself (Chapter 8, Lemma 3.2, Corollary)". Consequently proper and improper
$\mathbb Z_p$-equivalence give the same classes, which is why `LocalClasses` (Cassels' $\mathcal G_p$) may be defined
with $\mathrm{GL}_2(\mathbb Z_p)$-equivalence (`isometricGL_iff_proper`). The proof is the reflection in a vector of
minimal order (`QuadForm.exists_refl_data_dvr`, O'Meara 91:4), valid at $p = 2$ as well.
-/
import QuadFormsKB.Literature.Cassels.Ch14.LocalClasses
import QuadFormsKB.Tamagawa.Reflection

namespace QuadFormsKB.Composition

open QuadForm Siegel Matrix

/-- **Cassels, Ch. 14, §3** (p. 339): *every nondegenerate $p$-adic binary form $g$ is improperly
$\mathbb Z_p$-equivalent to itself*: there is $T \in \mathrm{GL}_2(\mathbb Z_p)$ with $\det T = -1$ and
$g(T\vec x) = g(\vec x)$. -/
@[kb "cassels1978" "Ch. 14, §3, p. 339 (every p-adic binary form is improperly equivalent to itself)"]
theorem exists_improper_aut_Zp {p : ℕ} [Fact p.Prime] (g : QuadForm ℤ_[p] 2) (hg : g.Nondegenerate) :
    ∃ T : GL (Fin 2) ℤ_[p], T.val.det = -1 ∧ ∀ x, g.eval (T.val *ᵥ x) = g.eval x := by
  obtain ⟨x, w, hx, hw⟩ := QuadForm.exists_refl_data_dvr g hg (by norm_num)
  have hdet := QuadForm.det_reflMat g hw hx
  exact ⟨Matrix.nonsingInvUnit (QuadForm.reflMat x w) (by rw [hdet]; exact isUnit_one.neg), hdet,
    fun y => QuadForm.eval_reflMat g hw y⟩

/-- **Proper and improper $\mathbb Z_p$-classes coincide** (Cassels, Ch. 14, §3, p. 339): two nondegenerate binary
forms over $\mathbb Z_p$ of the same discriminant (as for two elements of $\mathcal G_p$) that are
$\mathrm{GL}_2(\mathbb Z_p)$-equivalent are already equivalent by a matrix of determinant $1$. (Without the equal
discriminants an equivalence may have any unit determinant $u$, and then $u^2 \ne 1$ is possible.) -/
@[kb "cassels1978" "Ch. 14, §3, p. 339 (proper and improper ℤ_p-equivalence of binary forms agree)"]
theorem isometricGL_iff_proper {p : ℕ} [Fact p.Prime] (f g : QuadForm ℤ_[p] 2) (hf : f.Nondegenerate)
    (hfg : f.hessian.det = g.hessian.det) :
    IsometricGL f g ↔ ∃ T : GL (Fin 2) ℤ_[p], T.val.det = 1 ∧ ∀ x, f.eval (T.val *ᵥ x) = g.eval x := by
  constructor
  · rintro ⟨T, hT⟩
    have hg : f.compMat T.val = g := QuadForm.eq_of_eval_eq (fun x => by rw [QuadForm.eval_compMat]; exact hT x)
    have hh : g.hessian.det = T.val.det ^ 2 * f.hessian.det := by
      rw [← hg, QuadForm.hessian_compMat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]; ring
    have hsq : (T.val.det - 1) * (T.val.det + 1) * f.hessian.det = 0 := by
      rw [← hfg] at hh; linear_combination -hh
    have hf' : f.hessian.det ≠ 0 := hf
    have h1 : (T.val.det - 1) * (T.val.det + 1) = 0 := by
      rcases mul_eq_zero.mp hsq with h | h
      · exact h
      · exact absurd h hf'
    rcases mul_eq_zero.mp h1 with h | h
    · exact ⟨T, by linear_combination h, hT⟩
    · obtain ⟨R, hR, hRf⟩ := exists_improper_aut_Zp f hf
      refine ⟨R * T, ?_, fun x => ?_⟩
      · rw [Units.val_mul, Matrix.det_mul, hR]; linear_combination (-1 : ℤ_[p]) * h
      · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hRf]; exact hT x
  · rintro ⟨T, -, hT⟩
    exact ⟨T, hT⟩

end QuadFormsKB.Composition
