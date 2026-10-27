/-
# Non-vacuity of the rank-2 headlines

**Layer:** number fields. Over **every** number field $F$ the hypotheses of `siegelIndefinite_ternary_uncond` (hence of
`siegelIndefiniteForms_rank2_uncond` with $r = 1$) are satisfiable: for an anisotropic binary $W$ over $\mathcal O_F$
(`exists_anisotropicF_binary`), the ternary form $Q_0 = \langle1\rangle\perp W$ (`blockForm`) is nondegenerate, represents
$m = 1$ over $F$ (at $e_0$), and $-2m\det H_{Q_0} = -4\det H_W$ is not a square in $F$ ($W$ anisotropic,
`anisotropicF_iff_not_isSquare`).
-/
import QuadFormsKB.Tamagawa.Indefinite.SiegelTernary

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField IsDedekindDomain QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Frames LocalDensity

/-- **The hypotheses of the ternary headline are satisfiable over every number field**: there is a nondegenerate
ternary $Q_0$ over $\mathcal O_F$ representing $m = 1$ over $F$ with $-2m\det H_{Q_0}$ not a square in $F$. -/
theorem exists_ternary_rank2_instance (F : Type) [Field F] [NumberField F] :
    ∃ Q₀ : QuadForm (𝓞 F) (1 + 2), Q₀.Nondegenerate ∧
      ¬ IsSquare (-(2 * ((1 : 𝓞 F) : F) * algebraMap (𝓞 F) F Q₀.hessian.det)) ∧
      Nonempty (RatSphere Q₀ ((1 : 𝓞 F) : F)) := by
  obtain ⟨W, hW⟩ := exists_anisotropicF_binary F
  have hdet : (blockForm (DVR.unary (1 : 𝓞 F)) W).hessian.det = 2 * W.hessian.det := by
    rw [det_hessian_blockForm]
    congr 1
    rw [Matrix.det_unique]
    simp [DVR.unary, QuadForm.hessian, QuadForm.diag]
    norm_num
  refine ⟨blockForm (DVR.unary (1 : 𝓞 F)) W, ?_, ?_, ?_⟩
  · unfold QuadForm.Nondegenerate
    rw [hdet]
    exact mul_ne_zero two_ne_zero (nondegenerate_of_anisotropicF hW)
  · rw [hdet]
    have h := (anisotropicF_iff_not_isSquare W).mp hW
    rintro ⟨s, hs⟩
    apply h
    refine ⟨s / 2, ?_⟩
    simp only [map_neg, map_mul, map_ofNat, map_one] at hs ⊢
    field_simp
    linear_combination hs
  · refine ⟨⟨Pi.single 0 1, ?_⟩⟩
    show qF _ _ = _
    simp only [qF, QuadForm.eval, map_blockForm, evalIn_blockForm]
    have h2 : ∀ j : Fin 2, (Pi.single (0 : Fin (1 + 2)) (1 : F) : Fin (1 + 2) → F) (Fin.natAdd 1 j) = 0 := by
      intro j
      rw [Pi.single_apply, ite_eq_right_iff]
      intro h
      have := congrArg Fin.val h
      simp at this
    simp [QuadForm.evalIn, QuadForm.map, h2, DVR.unary, QuadForm.diag, Pi.single_apply]

end QuadFormsKB.Tamagawa.Indefinite
