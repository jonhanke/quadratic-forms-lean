/-
# Kitaoka 1993, §1.5: Proposition 1.5.4 on quaternion algebras (parts)

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §1.5, pp. 25–27 (printed pages).

**Proves** (for $C = (\alpha, \beta)$, $\alpha, \beta \in F^\times$, `ℍ[F,α,β]` $= ℍ[F,\alpha,0,\beta]$):
* `quatNorm_apply`: $N(x) = a_0^2 - \alpha a_1^2 - \beta a_2^2 + \alpha\beta a_3^2$ in terms of the structure fields;
* `quatNorm_eq_mul_star`: $N(x) = \operatorname{re}(x\bar x)$; `quatNorm_mul`: $N(xy) = N(x)N(y)$;
* `proposition154_ii`: conjugation is an isometry of $(C, N)$ and has determinant $-1 \ne 1$ (char $\ne 2$);
* `proposition154_iii`: the symmetry formula $\tau_u(x) = -uxu^{-1}$ for pure $u$, $x$;
* `proposition154_i_norm`: the norm-preservation half of the "$\Leftarrow$" direction of (i).

**Not proved here.** `Proposition154` as a whole (the "$\Rightarrow$" direction of (i), and $\det f = 1$ in the
"$\Leftarrow$" direction), and `Proposition152`.

*Proof sketches.* The norm is computed in coordinates. Conjugation is $\operatorname{diag}(1,-1,-1,-1)$ in the
coordinates $(a_0,\dots,a_3)$ (via `LinearMap.det_conj` and `LinearMap.det_toLin'`), so $\det = -1$. The symmetry formula
is a polynomial identity in the coordinates after clearing the denominator $N(u) \ne 0$. For (i), $N(axb) = N(a)N(x)N(b)
= N(ab)N(x) = N(x)$ by multiplicativity and commutativity of $F$.
-/
import QuadFormsKB.Literature.Kitaoka.Ch1Spaces

open QuadraticMap Quaternion

noncomputable section

namespace QuadFormsKB.Kitaoka

section Quaternion

variable {F : Type} [Field F]

/-- The conjugation `quatConj` is the quaternion star $x \mapsto \bar x$. -/
theorem quatConj_apply (α β : F) (x : ℍ[F,α,β]) : quatConj α β x = star x := rfl

/-- The norm form in coordinates: $N(x) = a_0^2 - \alpha a_1^2 - \beta a_2^2 + \alpha\beta a_3^2$. -/
theorem quatNorm_apply (α β : F) (x : ℍ[F,α,β]) :
    quatNorm α β x = x.re ^ 2 - α * x.imI ^ 2 - β * x.imJ ^ 2 + α * β * x.imK ^ 2 := by
  have h0 : (QuaternionAlgebra.linearEquivTuple (R := F) α 0 β x) 0 = x.re := rfl
  have h1 : (QuaternionAlgebra.linearEquivTuple (R := F) α 0 β x) 1 = x.imI := rfl
  have h2 : (QuaternionAlgebra.linearEquivTuple (R := F) α 0 β x) 2 = x.imJ := rfl
  have h3 : (QuaternionAlgebra.linearEquivTuple (R := F) α 0 β x) 3 = x.imK := rfl
  simp [quatNorm, QuadraticMap.comp_apply, weightedSumSquares_apply, Fin.sum_univ_four]
  ring

/-- $N(x) = \operatorname{re}(x \bar x)$. -/
theorem quatNorm_eq_mul_star (α β : F) (x : ℍ[F,α,β]) :
    quatNorm α β x = (x * star x).re := by
  rw [quatNorm_apply]
  simp
  ring

/-- The norm is multiplicative: $N(xy) = N(x)N(y)$. -/
theorem quatNorm_mul (α β : F) (x y : ℍ[F,α,β]) :
    quatNorm α β (x * y) = quatNorm α β x * quatNorm α β y := by
  simp only [quatNorm_apply]
  simp
  ring

/-- Conjugation preserves the norm. -/
theorem quatNorm_conj (α β : F) (x : ℍ[F,α,β]) :
    quatNorm α β (quatConj α β x) = quatNorm α β x := by
  simp only [quatConj_apply, quatNorm_apply]
  simp

/-- The determinant of conjugation is $-1$: it is $\operatorname{diag}(1,-1,-1,-1)$ in the coordinates
$(a_0, a_1, a_2, a_3)$. -/
theorem quatConj_det (α β : F) : LinearMap.det (quatConj α β) = -1 := by
  classical
  set e := QuaternionAlgebra.linearEquivTuple (R := F) α 0 β with he
  have key : (e : ℍ[F,α,β] →ₗ[F] (Fin 4 → F)) ∘ₗ quatConj α β ∘ₗ (e.symm : (Fin 4 → F) →ₗ[F] ℍ[F,α,β])
      = Matrix.toLin' (Matrix.diagonal ![1, -1, -1, -1]) := by
    apply LinearMap.ext
    intro v
    funext i
    have hv : e.symm v = ⟨v 0, v 1, v 2, v 3⟩ := rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, quatConj_apply, hv,
      Matrix.toLin'_apply, Matrix.mulVec_diagonal]
    fin_cases i <;> simp [he, QuaternionAlgebra.linearEquivTuple, QuaternionAlgebra.addEquivTuple] <;> rfl
  rw [← LinearMap.det_conj (quatConj α β) e, key, LinearMap.det_toLin', Matrix.det_diagonal]
  simp [Fin.prod_univ_four]

/-- **Kitaoka 1993, Proposition 1.5.4 (ii)** (p. 27), *proved*: $x \mapsto \bar x$ is an isometry of $(C, N)$ whose
determinant ($-1$) is not $1$, when $\operatorname{char} F \ne 2$. -/
@[kb "kitaoka1993" "§1.5, Prop. 1.5.4 (ii), p. 27"]
theorem proposition154_ii (h2 : (2 : F) ≠ 0) (α β : F) :
    (∀ x, quatNorm α β (quatConj α β x) = quatNorm α β x) ∧ LinearMap.det (quatConj α β) ≠ 1 := by
  refine ⟨quatNorm_conj α β, ?_⟩
  rw [quatConj_det]
  intro h
  apply h2
  linear_combination -h

/-- **Kitaoka 1993, Proposition 1.5.4 (iii)** (p. 27), *proved*: for pure $u, x$ with $N(u) \ne 0$ the symmetry
$x - \frac{T(x\bar u)}{N(u)}u$ equals $-u x u^{-1}$ with $u^{-1} = N(u)^{-1}\bar u$. No hypothesis on
$\alpha, \beta$ or the characteristic is needed. -/
@[kb "kitaoka1993" "§1.5, Prop. 1.5.4 (iii), p. 27"]
theorem proposition154_iii (α β : F) (u x : ℍ[F,α,β]) (hu : u.re = 0) (hx : x.re = 0)
    (hN : quatNorm α β u ≠ 0) :
    x - ((x * star u + star (x * star u)).re / quatNorm α β u) • u =
      -(u * x * ((quatNorm α β u)⁻¹ • star u)) := by
  have hNe : quatNorm α β u = -(α * u.imI ^ 2) - β * u.imJ ^ 2 + α * β * u.imK ^ 2 := by
    rw [quatNorm_apply, hu]; ring
  generalize quatNorm α β u = N at *
  ext <;> simp [hu, hx]
  all_goals first | (right; subst hNe; ring1) | (field_simp; subst hNe; ring)

/-- **Kitaoka 1993, Proposition 1.5.4 (i), norm half of "$\Leftarrow$"** (p. 27), *proved*: if $f(x) = axb$ with
$N(ab) = 1$ then $f$ preserves $N$. (The determinant-$1$ half is not proved here.) -/
@[kb "kitaoka1993" "§1.5, Prop. 1.5.4 (i), p. 27"]
theorem proposition154_i_norm (α β : F) (a b : ℍ[F,α,β]) (hab : quatNorm α β (a * b) = 1)
    (x : ℍ[F,α,β]) : quatNorm α β (a * x * b) = quatNorm α β x := by
  rw [quatNorm_mul, quatNorm_mul]
  rw [quatNorm_mul] at hab
  linear_combination quatNorm α β x * hab

end Quaternion

end QuadFormsKB.Kitaoka
