/-
# Estes–Pall, the local step: the spinor norm at a prime dividing $w$ is a unit class

Helper for the Estes–Pall theorem (Conway–Sloane, Ch. 15, §3.5, p. 366; `Section3EstesPallIf.lean`).

**Setting.** $F_v$ is the completion of $\mathbb Q$ at a prime $v = p$; $Q$ is a nondegenerate binary form over
$\mathbb Q$ and $P \in M_2(F_v)$ a matrix with
$$Q(Pz) = f'(z) = a z_0^2 + B z_0z_1 + C w^4 z_1^2 \qquad (z \in F_v^2),$$
where $a, B, C, w \in F_v$, $a$, $B$, $2$ and $D = B^2 - 4aCw^4$ are units, $|C|_v \le 1$ and $|w|_v < 1$ ($p$ divides $w$
but not $2aD$). The lattice $M_v = P\gamma\,\mathfrak o_v^2$, $\gamma = \operatorname{diag}(w^2, w^{-2})$, has Gram form
$g'(t) = aw^4t_0^2 + Bt_0t_1 + Ct_1^2$.

**Statement** (`isUnitSqClass_spinorNorm_local`). Every rotation $\sigma \in O^+(V_v)$ with $\sigma x \in M_v$ for
$x = Pe_0$ has a unit spinor norm class: $\theta(\sigma) \in \mathfrak o_v^\times F_v^{\times 2}$.

**Proof.** Write $\sigma x = P\gamma t$ with $t \in \mathfrak o_v^2$. Since $g'(t) = Q(\sigma x) = Q(x) = a$,
$a(1 - w^4t_0^2) = t_1(Bt_0 + Ct_1)$, so $t_1$ is a unit. With $y = P(-B, 2a)$ (orthogonal to $x$, $Q(y) = -aD$),
$$Q(\sigma x - x) = f'(w^2t_0 - 1, w^{-2}t_1) = w^{-2}E, \qquad E = 2aw^2(1 - w^2t_0) - Bt_1,$$
and $E$ is a unit. By `binary_spinorNorm_eq`, $\theta(\sigma) = Q(\sigma x - x)Q(y) = (w^{-1})^2\cdot(-aDE)$, a unit
times a square. The evenness of the exponent of $w$ (here $w^{\pm 2}$, coming from a **fourth** power in the class
group) is exactly what makes the valuation of $\theta(\sigma)$ even.
-/
import QuadFormsKB.Literature.ConwaySloane.Section3BinarySpinorNorm
import QuadFormsKB.Lattices.SpinorLocal

open NumberField Matrix IsDedekindDomain

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

namespace QuadFormsKB.ConwaySloane.EstesPall

open QuadFormsKB.Lattices

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "Fv" => v.adicCompletion ℚ

/-- The binary form $f'(z) = az_0^2 + Bz_0z_1 + Cw^4z_1^2$. -/
def fq (a B C w : Fv) (z : Fin 2 → Fv) : Fv := a * z 0 ^ 2 + B * z 0 * z 1 + C * w ^ 4 * z 1 ^ 2

/-- **The local step of Estes–Pall** (see the module docstring): at a prime dividing $w$ but not $2aD$, every rotation
carrying $x = Pe_0$ into $P\gamma\,\mathfrak o_v^2$ ($\gamma = \operatorname{diag}(w^2, w^{-2})$) has a unit spinor
norm class. -/
@[kb "conwaysloane1999" "Ch. 15, §3.5, p. 366 (Estes–Pall: the local spinor norm at p | w)"]
theorem isUnitSqClass_spinorNorm_local (Q : QuadForm ℚ 2) (hQ : Q.Nondegenerate) (P : Matrix (Fin 2) (Fin 2) Fv)
    {a B C w : Fv} (hP : ∀ z, Q.evalIn Fv (P *ᵥ z) = fq v a B C w z)
    (ha : Valued.v a = 1) (hB : Valued.v B = 1) (h2 : Valued.v (2 : Fv) = 1)
    (hD : Valued.v (B ^ 2 - 4 * a * C * w ^ 4) = 1) (hC : Valued.v C ≤ 1) (hw : Valued.v w < 1) (hw0 : w ≠ 0)
    (σ : orthGroup Q Fv) (hσ : (σ : GL (Fin 2) Fv).val.det = 1) {t : Fin 2 → Fv}
    (ht : ∀ i, Valued.v (t i) ≤ 1)
    (hσx : (σ : GL (Fin 2) Fv).val *ᵥ (P *ᵥ ![1, 0]) = P *ᵥ ![w ^ 2 * t 0, (w ^ 2)⁻¹ * t 1]) :
    IsUnitSqClass v (spinorNorm Q Fv σ) := by
  set S := (σ : GL (Fin 2) Fv).val with hS
  set D := B ^ 2 - 4 * a * C * w ^ 4 with hDdef
  have hσo : (σ : GL (Fin 2) Fv) ∈ orthGroup Q Fv := σ.2
  have ha0 : a ≠ 0 := by intro h; rw [h, map_zero] at ha; exact zero_ne_one ha
  have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw0
  have hD0 : D ≠ 0 := by intro h; rw [h, map_zero] at hD; exact zero_ne_one hD
  set x : Fin 2 → Fv := P *ᵥ ![1, 0] with hx
  set y : Fin 2 → Fv := P *ᵥ ![-B, 2 * a] with hy
  have hQx : Q.evalIn Fv x = a := by rw [hx, hP]; simp [fq]
  have hQy : Q.evalIn Fv y = -a * D := by rw [hy, hP]; simp [fq, hDdef]; ring
  have hxy : x ⬝ᵥ (Q.hessian.map (algebraMap ℚ Fv) *ᵥ y) = 0 := by
    rw [← QuadForm.polar_eq_hessian, hx, hy, ← mulVec_add, hP, hP, hP]
    simp [fq]; ring
  -- `t₁` is a unit
  have hQσx : Q.evalIn Fv (S *ᵥ x) = a := by rw [evalIn_mulVec_of_mem Q hσo x, hQx]
  have hfq : fq v a B C w ![w ^ 2 * t 0, (w ^ 2)⁻¹ * t 1] = a * w ^ 4 * t 0 ^ 2 + B * t 0 * t 1 + C * t 1 ^ 2 := by
    simp only [fq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp
  have hg : a * w ^ 4 * t 0 ^ 2 + B * t 0 * t 1 + C * t 1 ^ 2 = a := by
    have := hQσx
    rw [hx, hσx, hP, hfq] at this
    exact this
  have ht1 : Valued.v (t 1) = 1 := by
    refine le_antisymm (ht 1) (not_lt.mp fun hlt => ?_)
    have e : a * (1 - w ^ 4 * t 0 ^ 2) = t 1 * (B * t 0 + C * t 1) := by linear_combination -hg
    have h1 : Valued.v (w ^ 4 * t 0 ^ 2) < 1 := by
      rw [map_mul, map_pow, map_pow]
      exact mul_lt_one_of_lt_of_le (pow_lt_one' hw (by norm_num)) (pow_le_one' (ht 0) 2)
    have hl : Valued.v (a * (1 - w ^ 4 * t 0 ^ 2)) = 1 := by
      rw [map_mul, ha, one_mul, Valuation.map_sub_eq_of_lt_left _ (by rw [map_one]; exact h1), map_one]
    have hr : Valued.v (t 1 * (B * t 0 + C * t 1)) < 1 := by
      rw [map_mul]
      have hle : Valued.v (B * t 0 + C * t 1) ≤ 1 := by
        refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
        · rw [map_mul, hB, one_mul]; exact ht 0
        · rw [map_mul]; exact mul_le_one' hC (ht 1)
      exact mul_lt_one_of_lt_of_le hlt hle
    rw [e] at hl
    exact absurd hl (ne_of_lt hr)
  -- `Q(σx - x) = w⁻² E`
  set E := 2 * a * w ^ 2 * (1 - w ^ 2 * t 0) - B * t 1 with hE
  have hQu : Q.evalIn Fv (S *ᵥ x - x) = (w ^ 2)⁻¹ * E := by
    have : S *ᵥ x - x = P *ᵥ ![w ^ 2 * t 0 - 1, (w ^ 2)⁻¹ * t 1] := by
      rw [hσx, hx, ← mulVec_sub]
      congr 1
      ext i; fin_cases i <;> simp
    rw [this, hP]
    simp only [fq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hE]
    have hk : w ^ 2 * (w ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hw2
    linear_combination hg + (B * t 0 * t 1 + C * t 1 ^ 2 * (w ^ 2 * (w ^ 2)⁻¹ + 1) - 2 * a +
      2 * a * w ^ 2 * t 0) * hk
  have hEv : Valued.v E = 1 := by
    have h1 : Valued.v (2 * a * w ^ 2 * (1 - w ^ 2 * t 0)) < 1 := by
      rw [map_mul, map_mul, map_mul, h2, ha, one_mul, one_mul, map_pow]
      have hle : Valued.v (1 - w ^ 2 * t 0) ≤ 1 := by
        refine (Valuation.map_sub _ _ _).trans (max_le (by rw [map_one]) ?_)
        rw [map_mul, map_pow]
        exact mul_le_one' (pow_le_one' hw.le 2) (ht 0)
      exact mul_lt_one_of_lt_of_le (pow_lt_one' hw (by norm_num)) hle
    have h2' : Valued.v (B * t 1) = 1 := by rw [map_mul, hB, ht1, one_mul]
    rw [hE, Valuation.map_sub_eq_of_lt_right _ (by rw [h2']; exact h1), h2']
  have hE0 : E ≠ 0 := by intro h; rw [h, map_zero] at hEv; exact zero_ne_one hEv
  have hu : Q.evalIn Fv (S *ᵥ x - x) ≠ 0 := by rw [hQu]; exact mul_ne_zero (inv_ne_zero hw2) hE0
  have hθ := binary_spinorNorm_eq Q Fv hQ σ hσ (x := x) (y := y) (by rw [hQx]; exact ha0)
    (by rw [hQy]; exact mul_ne_zero (neg_ne_zero.mpr ha0) hD0) hxy hu
  refine ⟨-a * D * E, ?_, ?_⟩
  · rw [map_mul, map_mul, Valuation.map_neg, ha, hD, hEv]; simp
  · rw [hθ, hQu, hQy]
    have e : (w ^ 2)⁻¹ * E * (-a * D) = (w⁻¹) ^ 2 * (-a * D * E) := by
      rw [inv_pow]; ring
    have hu0 : (w⁻¹) ^ 2 ≠ 0 := pow_ne_zero 2 (inv_ne_zero hw0)
    have hd0 : -a * D * E ≠ 0 := mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr ha0) hD0) hE0
    rw [e, sqClassOf_mul hu0 hd0, (sqClassOf_eq_one_iff hu0).mpr ⟨w⁻¹, sq _⟩, one_mul]

end QuadFormsKB.ConwaySloane.EstesPall
