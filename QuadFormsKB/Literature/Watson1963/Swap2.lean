/-
# Watson (1963): changing the type of an even unimodular part over $\mathbb Z_2$

Over $\mathbb Z_2$ there are two even unimodular forms of each rank $2k \ge 2$: $H^k$ and $H^{k-1} \perp A$
(`even_unimodular_classification`). If an even unimodular sublattice $V$ of rank $2k$ of a form $G$ is orthogonal to
a vector $x_0$ with odd value $w = G(x_0)$, then $G$ represents **both** types of rank $2k$
(`rep2_unimodular_of_odd_vec`): in the last binary block ($H$ with basis $p, q$, resp. $A$) the vectors $p + x_0$ and
$p + q$ (resp. $p + x_0$ and $q$) span a binary of the other type (Gram determinant $4w - 1$, resp. $4(1+w) - 1$).
This is the dyadic phenomenon that a unimodular component next to an odd $2$-modular one does not have a fixed type
(Watson 1963, §3, the case $r_2$ odd).
-/
import QuadFormsKB.Literature.Watson1963.PsiFacts

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms QuadFormsKB.Hanke2011Structure

variable {N : ℕ}

/-- Helper: an orthogonal sum of $H^j$ (represented by $M_1$) and a binary spanned by two vectors $x, y$ orthogonal
to the columns of $M_1$. -/
theorem rep2_hypSum_bq {j : ℕ} (G : QuadForm ℤ_[2] N) (M₁ : Matrix (Fin N) (Fin (2 * j)) ℤ_[2])
    (h₁ : ∀ y, G.eval (M₁ *ᵥ y) = (hypSum j : QuadForm ℤ_[2] (2 * j)).eval y) (x y : Fin N → ℤ_[2])
    {α β γ : ℤ_[2]} (hx : G.eval x = α) (hy : G.eval y = γ) (hxy : x ⬝ᵥ (G.hessian *ᵥ y) = β)
    (hox : ∀ z, (M₁ *ᵥ z) ⬝ᵥ (G.hessian *ᵥ x) = 0) (hoy : ∀ z, (M₁ *ᵥ z) ⬝ᵥ (G.hessian *ᵥ y) = 0) :
    Rep2 G (QuadForm.orthSum (hypSum j) (Composition.bq α β γ)) := by
  let M₂ : Matrix (Fin N) (Fin 2) ℤ_[2] := Matrix.of fun r c => (![x, y] c) r
  have hM₂ : ∀ z, M₂ *ᵥ z = z 0 • x + z 1 • y := fun z => by
    ext r; simp [M₂, mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  refine rep2_orthSum M₁ M₂ h₁ (fun z => ?_) (fun z w => ?_)
  · have hz : z = ![z 0, z 1] := by ext i; fin_cases i <;> rfl
    rw [hM₂, hz, Composition.bq_eval]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    have hp := QuadForm.eval_polar G (z 0 • x) (z 1 • y)
    rw [eval_smul_sq, eval_smul_sq, mulVec_smul, dotProduct_smul, smul_dotProduct, hxy, hx, hy] at hp
    simp only [smul_eq_mul] at hp
    linear_combination hp
  · rw [hM₂, mulVec_add, mulVec_smul, mulVec_smul, dotProduct_add, dotProduct_smul, dotProduct_smul, hox, hoy]
    simp

/-- Helper: the Hessian determinant of $H^j \perp (\alpha x^2 + \beta xy + \gamma y^2)$. -/
theorem hessian_det_hypSum_bq (j : ℕ) (α β γ : ℤ_[2]) :
    (QuadForm.orthSum (hypSum j) (Composition.bq α β γ)).hessian.det = (-1) ^ j * (4 * α * γ - β ^ 2) := by
  rw [hessian_orthSum_det, hypSum_hessian_det]
  have := Composition.neg_det_bq α β γ
  linear_combination (-(-1 : ℤ_[2]) ^ j) * this

/-- Helper: the column-selection matrix $\vec y \mapsto (\vec y, 0)$. -/
def selFirst (a b : ℕ) : Matrix (Fin (a + b)) (Fin a) ℤ_[2] :=
  Matrix.of fun i c => if i = Fin.castAdd b c then 1 else 0

theorem selFirst_mulVec (a b : ℕ) (y : Fin a → ℤ_[2]) : selFirst a b *ᵥ y = Fin.append y 0 := by
  ext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [selFirst, mulVec, dotProduct, Fin.castAdd_inj]
  · have hne : ∀ z : Fin a, Fin.natAdd a i ≠ Fin.castAdd b z := fun z h => by
      have := congrArg Fin.val h; simp at this; omega
    simp [selFirst, mulVec, dotProduct, hne]

/-- **Both types of even unimodular forms of rank $2(j+1)$ are represented** by $G$ when $G$ has an even unimodular
sublattice of that rank (columns of $H$) orthogonal to a vector $x_0$ with odd value (see the module docstring).
Arguments: `H`, `hH` (unit Gram determinant), `x₀`, `hx₀` ($G(x_0)$ odd), `horth`, and the target `Y` with `hY`. -/
theorem rep2_unimodular_of_odd_vec {j : ℕ} (G : QuadForm ℤ_[2] N) (H : Matrix (Fin N) (Fin (2 * (j + 1))) ℤ_[2])
    (hH : IsUnit (Hᵀ * G.hessian * H).det) (x₀ : Fin N → ℤ_[2]) (hx₀ : ¬ (2 : ℤ_[2]) ∣ G.eval x₀)
    (horth : ∀ y, (H *ᵥ y) ⬝ᵥ (G.hessian *ᵥ x₀) = 0) (Y : QuadForm ℤ_[2] (2 * (j + 1)))
    (hY : IsUnit Y.hessian.det) : Rep2 G Y := by
  set V := G.compMat H
  have hV : IsUnit V.hessian.det := by rw [QuadForm.hessian_compMat]; exact hH
  have hw := isUnit_of_toZMod_ne_zero (toZMod_ne_zero_of_not_dvd hx₀)
  obtain ⟨t, ht⟩ := Composition.two_dvd_sub_one_of_isUnit hw
  have hY' := even_unimodular_classification Y hY
  -- general step: a model `W` of `V`, block vectors, and the new binary
  have step : ∀ (B : QuadForm ℤ_[2] 2), IsometricGL V (QuadForm.orthSum (hypSum j) B) →
      ∀ (p q : Fin 2 → ℤ_[2]) {α β γ : ℤ_[2]}, B.eval p + G.eval x₀ = α → B.eval q = γ →
        p ⬝ᵥ (B.hessian *ᵥ q) = β →
      Rep2 G (QuadForm.orthSum (hypSum j) (Composition.bq α β γ)) := by
    intro B ⟨T, hT⟩ p q α β γ hα hγ hβ
    set M₀ := H * T.val
    have hM₀ : ∀ z, G.eval (M₀ *ᵥ z) = (QuadForm.orthSum (hypSum j) B).eval z := fun z => by
      rw [← mulVec_mulVec, ← QuadForm.eval_compMat, ← hT]
    have hM₀x : ∀ z, (M₀ *ᵥ z) ⬝ᵥ (G.hessian *ᵥ x₀) = 0 := fun z => by rw [← mulVec_mulVec]; exact horth _
    set P := M₀ *ᵥ Fin.append (0 : Fin (2 * j) → ℤ_[2]) p
    set Qv := M₀ *ᵥ Fin.append (0 : Fin (2 * j) → ℤ_[2]) q
    have hdotM : ∀ z z', (M₀ *ᵥ z) ⬝ᵥ (G.hessian *ᵥ (M₀ *ᵥ z')) =
        z ⬝ᵥ ((QuadForm.orthSum (hypSum j) B).hessian *ᵥ z') := dot_of_rep hM₀
    have hblk : ∀ (s : Fin (2 * j) → ℤ_[2]) (r : Fin 2 → ℤ_[2]),
        Fin.append s 0 ⬝ᵥ ((QuadForm.orthSum (hypSum j) B).hessian *ᵥ Fin.append 0 r) = 0 := by
      intro s r
      apply dot_eq_zero_of_eval_add
      rw [append_add_append, add_zero, zero_add, eval_orthSum_append, eval_orthSum_append, eval_orthSum_append,
        eval_zero_vec, eval_zero_vec]; ring
    have hblk2 : ∀ (r r' : Fin 2 → ℤ_[2]),
        Fin.append (0 : Fin (2 * j) → ℤ_[2]) r ⬝ᵥ ((QuadForm.orthSum (hypSum j) B).hessian *ᵥ Fin.append 0 r') =
          r ⬝ᵥ (B.hessian *ᵥ r') := by
      intro r r'
      rw [← QuadForm.eval_polar, ← QuadForm.eval_polar, append_add_append, add_zero, eval_orthSum_append,
        eval_orthSum_append, eval_orthSum_append, eval_zero_vec]; ring
    refine rep2_hypSum_bq G (M₀ * selFirst (2 * j) 2) (fun y => ?_) (P + x₀) Qv ?_ ?_ ?_ (fun z => ?_) (fun z => ?_)
    · rw [← mulVec_mulVec, hM₀, selFirst_mulVec, eval_orthSum_append, eval_zero_vec, add_zero]
    · have hp := QuadForm.eval_polar G P x₀
      rw [hM₀x] at hp
      have hP : G.eval P = B.eval p := by
        simp only [P]; rw [hM₀, eval_orthSum_append, eval_zero_vec, zero_add]
      rw [← hα]
      linear_combination hp + hP
    · rw [hM₀, eval_orthSum_append, eval_zero_vec, zero_add, hγ]
    · rw [add_dotProduct, hdotM, hblk2, hβ, dot_symm G x₀ Qv, hM₀x, add_zero]
    · rw [← mulVec_mulVec, selFirst_mulVec, mulVec_add, dotProduct_add, hdotM, hblk, hM₀x, add_zero]
    · rw [← mulVec_mulVec, selFirst_mulVec, hdotM, hblk]
  have hrep : ∀ W : QuadForm ℤ_[2] (2 * (j + 1)), Rep2 G W → IsometricGL W Y → Rep2 G Y :=
    fun W hW hWY => hW.trans (Rep2.of_isometricGL hWY)
  have hVrep : IsometricGL V Y → Rep2 G Y := fun h => hrep V (Rep2.compMat G H) h
  have h8 : (8 : ℤ_[2]) ∣ 4 * (1 + G.eval x₀) := ⟨1 + t, by linear_combination 4 * ht⟩
  have hsign : ∀ d : ℤ_[2], (-1 : ℤ_[2]) ^ (j + 1) * ((-1) ^ j * d) = -d := fun d => by
    have := neg_one_pow_mul_self (k := j)
    rw [pow_succ]; linear_combination (-d) * this
  have hdetU : ∀ a : ℤ_[2], IsUnit ((-1 : ℤ_[2]) ^ j * (2 * a - 1)) := fun a =>
    isUnit_neg_one_pow.mul (isUnit_of_toZMod_ne_zero (by
      rw [map_sub, map_mul, map_ofNat, show (2 : ZMod 2) = 0 by decide, zero_mul, map_one]; decide))
  rcases even_unimodular_classification V hV with ⟨-, hVh⟩ | ⟨-, -, hVa⟩
  · rcases hY' with ⟨-, hYh⟩ | ⟨-, -, hYa⟩
    · exact hVrep (hVh.trans hYh.symm)
    · -- V of type H^{j+1}: the binary spanned by p + x₀ and p + q is of type A
      have hR := step hypPlane hVh ![1, 0] ![1, 1] (α := G.eval x₀) (β := 1) (γ := 1)
        (by rw [hypPlane_eval]; ring) (by rw [hypPlane_eval]; ring)
        (by
          rw [← QuadForm.eval_polar]
          rw [Matrix.cons_add_cons, Matrix.cons_add_cons, Matrix.empty_add_empty,
            hypPlane_eval, hypPlane_eval, hypPlane_eval]; ring)
      have hd : (QuadForm.orthSum (hypSum j) (Composition.bq (G.eval x₀) 1 1)).hessian.det =
          (-1) ^ j * (2 * (2 * G.eval x₀) - 1) := by rw [hessian_det_hypSum_bq]; ring
      refine hrep _ hR (((isometricGL_hypA_iff _ (by rw [hd]; exact hdetU _)).2 ?_).trans hYa.symm)
      rw [hd, hsign]
      intro hsq
      have hX : IsUnit (-(2 * (2 * G.eval x₀) - 1)) := by
        have := hdetU (2 * G.eval x₀); exact (IsUnit.mul_iff.1 this).2.neg
      have h4 : (4 : ℤ_[2]) ∣ -(2 * (2 * G.eval x₀) - 1) - 1 := ⟨-G.eval x₀, by ring⟩
      obtain ⟨c, hc⟩ := (isSquare_iff_dvd_eight hX h4).1 hsq
      apply hx₀
      refine ⟨-c, ?_⟩
      have h40 : (4 : ℤ_[2]) ≠ 0 := by norm_num
      have : (4 : ℤ_[2]) * (G.eval x₀ + 2 * c) = 0 := by linear_combination -hc
      have := (mul_eq_zero.1 this).resolve_left h40
      linear_combination this
  · rcases hY' with ⟨-, hYh⟩ | ⟨-, -, hYa⟩
    · -- V of type H^j ⊥ A: the binary spanned by p + x₀ and q is of type H
      have hR := step quadA hVa ![1, 0] ![0, 1] (α := 1 + G.eval x₀) (β := 1) (γ := 1)
        (by unfold quadA; rw [Composition.bq_eval]; ring) (by unfold quadA; rw [Composition.bq_eval]; ring)
        (by
          rw [← QuadForm.eval_polar]
          rw [Matrix.cons_add_cons, Matrix.cons_add_cons, Matrix.empty_add_empty]
          unfold quadA; rw [Composition.bq_eval, Composition.bq_eval, Composition.bq_eval]; ring)
      have hd : (QuadForm.orthSum (hypSum j) (Composition.bq (1 + G.eval x₀) 1 1)).hessian.det =
          (-1) ^ j * (2 * (2 * (1 + G.eval x₀)) - 1) := by rw [hessian_det_hypSum_bq]; ring
      refine hrep _ hR (((isometricGL_hyp_iff _ (by rw [hd]; exact hdetU _)).2 ?_).trans hYh.symm)
      rw [hd, hsign]
      have hX : IsUnit (-(2 * (2 * (1 + G.eval x₀)) - 1)) := by
        have := hdetU (2 * (1 + G.eval x₀)); exact (IsUnit.mul_iff.1 this).2.neg
      have h4 : (4 : ℤ_[2]) ∣ -(2 * (2 * (1 + G.eval x₀)) - 1) - 1 := ⟨-(1 + G.eval x₀), by ring⟩
      refine (isSquare_iff_dvd_eight hX h4).2 ?_
      obtain ⟨c, hc⟩ := h8
      exact ⟨-c, by linear_combination -hc⟩
    · exact hVrep (hVa.trans hYa.symm)

end QuadFormsKB.Watson1963
