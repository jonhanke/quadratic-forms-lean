/-
# O'Meara §101B: spinor norms of rotations over a global function field (101:8a)

**Setting.** $k$ a finite field, $F$ a finite extension of $k(t)$ (a *global function field*,
`FunctionField k F`), $\operatorname{char} F \ne 2$ (`Invertible (2 : F)`), and $(V, Q)$ a regular
quadratic space over $F$ with $\dim V \ge 3$.

**Proves** `omeara101_8a` (O'Meara 1973, §101B, 101:8a, p. 292): the spinor norm of the rotation group is
everything, $\theta(O^+(V)) = F^\times$, i.e. `(spinorNormHom Q hQ).range = ⊤`.

**Deviation from O'Meara's proof.** O'Meara combines local surjectivity of the spinor norm at every spot
with the Hasse principle. Here the global function field is $C_2$-like: by
`exists_isotropic_of_functionField` (Chevalley–Warning / Tsen–Lang, `FunctionField/GlobalTsen.lean`) every
quadratic form in $\ge 5$ variables over $F$ has a nontrivial zero. For $\alpha \in F^\times$ the form
$Q(x) - \alpha Q(y)$ on $V \times V$ has $2\dim V \ge 6$ variables, so $Q(x) = \alpha Q(y)$ for some
$(x, y) \ne 0$. If $V$ is isotropic, `spinorNormHom_surjective_of_isotropic` (55:6a) already gives the
claim. Otherwise $Q(y) \ne 0 \ne Q(x)$ and $\tau_x \tau_y \in O^+(V)$ has spinor norm
$Q(x) Q(y) = \alpha Q(y)^2 \equiv \alpha$. No local theory and no Hasse principle is used.

Indices are 0-based.
-/
import Mathlib
import QuadFormsKB.FunctionField.GlobalTsen
import QuadFormsKB.Literature.OMeara.Sec55

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

/-- **101:8a** (O'Meara 1973, §101B, p. 292). Over a global function field $F$ (a finite extension of
$k(t)$, $k$ finite, $\operatorname{char} F \ne 2$), for a regular quadratic space $V$ of dimension
$n \ge 3$ the spinor norm of the rotation group is all of $F^\times / F^{\times 2}$:
$\theta(O^+(V)) = F^\times$. Fields of the statement: `k` the finite constant field, `F` the function
field, `V` the $F$-space, `Q` its quadratic form, `hQ` regularity, `hn` $\dim_F V \ge 3$.
The proof uses Chevalley–Warning (the $C_2$ property of $F$) instead of local surjectivity and the Hasse
principle; see the module docstring. -/
@[kb "omeara1963" "§101B, 101:8a, p. 292"]
theorem omeara101_8a {k : Type} [Field k] [Fintype k] {F : Type} [Field F] [Algebra (RatFunc k) F]
    [FunctionField k F] [Invertible (2 : F)]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V)
    (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : 3 ≤ Module.finrank F V) :
    (spinorNormHom Q hQ).range = ⊤ := by
  by_cases hiso : ∃ x : V, x ≠ 0 ∧ Q x = 0
  · exact MonoidHom.range_eq_top.mpr (spinorNormHom_surjective_of_isotropic Q hQ hiso)
  · rw [MonoidHom.range_eq_top]
    intro c
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective (s := (powMonoidHom 2 : Fˣ →* Fˣ).range) c
    set α : F := (u : F) with hα
    have hα0 : α ≠ 0 := u.ne_zero
    have h5 : 5 ≤ Module.finrank F (V × V) := by
      rw [Module.finrank_prod]; omega
    obtain ⟨⟨x, y⟩, hxy0, hxy⟩ :=
      QuadFormsKB.RatFuncPlace.exists_isotropic_of_functionField (k := k) (F := F)
        (QuadraticMap.prod Q ((-α) • Q)) h5
    have hxy' : Q x + (-α) * Q y = 0 := by simpa using hxy
    have hy : Q y ≠ 0 := by
      intro hy0
      have hx0 : Q x = 0 := by rw [hy0] at hxy'; simpa using hxy'
      have hy' : y = 0 := by
        by_contra h; exact hiso ⟨y, h, hy0⟩
      have hx' : x = 0 := by
        by_contra h; exact hiso ⟨x, h, hx0⟩
      exact hxy0 (by simp [hx', hy'])
    have hQx : Q x = α * Q y := by linear_combination hxy'
    have hx : Q x ≠ 0 := by rw [hQx]; exact mul_ne_zero hα0 hy
    have hmem : symmetry Q x hx * symmetry Q y hy ∈ orthPlus Q := by
      refine ⟨mul_mem (symmetry_mem_orth Q hx) (symmetry_mem_orth Q hy), ?_⟩
      show LinearEquiv.det (symmetry Q x hx * symmetry Q y hy) = 1
      rw [map_mul, det_symmetry, det_symmetry]; norm_num
    have hsp : HasSpinorNorm Q (symmetry Q x hx * symmetry Q y hy) α :=
      HasSpinorNorm.of_eq_mul_sq Q
        (HasSpinorNorm.mul Q (hasSpinorNorm_symmetry Q hx) (hasSpinorNorm_symmetry Q hy))
        (inv_ne_zero hy) (by rw [hQx]; field_simp)
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [spinorNormHom_apply Q hQ hsp, Sp55.sqClassOf_of_ne_zero' hα0]
    have e : Units.mk0 α hα0 = u := Units.ext rfl
    rw [e]
    rfl

end QuadFormsKB.OMeara
