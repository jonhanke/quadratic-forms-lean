/-
# Watson (1963), Lemma 2 at $p = 2$: the local representations of the probes

Watson, *The class-number of a positive quadratic form*, Proc. London Math. Soc. (3) 13 (1963), §4, Lemma 2,
(4.12)–(4.16), pp. 555–556, at $p = 2$, for the perfect forms of §8. **This proves the named input
`WatsonLocalProbesTwo`** (`watsonLocalProbesTwo_holds`).

Let $f$ be Watson-minimal positive definite in $n \ge 12$ variables, $F$ its base change to $\mathbb Z_2$, and
$F = U \perp \psi$ the shape of `exists_decomp_two` ($U$ even unimodular of rank $2k$, $\psi$ with even Hessian,
$2k \le r_2(f) \le 2k + 1$); $\psi$ is square-free (`sqFreePsi_of_decomp`). Each probe $\varphi$ in $v$ variables
with $r_2(f) \ge v + 1$ is, over $\mathbb Z_2$, $Y \perp S$ with $Y$ even unimodular (`ProbeDecomp.lean`), and:
* $A_5 = A_4 \perp \langle 15\rangle$, $E_7 = A_6 \perp \langle 7\rangle$: $U \supseteq Y \perp U'$, and $U'$
  (even unimodular of rank $\ge 2$) represents the unit;
* $D_5 = A_4 \perp \langle 10\rangle$, $D_9 = A_8 \perp \langle 18\rangle$: the value $2u$ comes from $U'$ (rank
  $\ge 4$), or from $U'$ plus an odd value of $\psi$, or from $\psi$ itself when all its values are even ((ψ1));
* $D_6 = A_4 \perp \langle a, c\rangle$ with $a \equiv 3$ or $7 \pmod 8$: from $U'$ (rank $\ge 4$), or from a value
  $\equiv 3 \pmod 4$ of $\psi$ ((ψ2)) and $U'$;
* $A_6$, $E_8$ (unimodular): from $U$, or, when $2k = v$, from $U$ and an odd value of $\psi$ (`Swap2.lean`).
-/
import QuadFormsKB.Literature.Watson1963.Probes2Aux
import QuadFormsKB.Literature.Watson1963.Reduced

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms QuadFormsKB.Hanke2011Structure

variable {N : ℕ}

/-! ### Helpers -/

theorem not_two_dvd_of_odd {c : ℤ} (hc : Odd c) : ¬ (2 : ℤ) ∣ c := fun h =>
  (Int.not_even_iff_odd.mpr hc) (even_iff_two_dvd.mpr h)

theorem isUnit_of_odd {c : ℤ} (hc : Odd c) : IsUnit ((c : ℤ) : ℤ_[2]) := isUnit_intCast_two (not_two_dvd_of_odd hc)

theorem isUnit_map_det {v : ℕ} (Y : QuadForm ℤ v) (h : ¬ (2 : ℤ) ∣ Y.hessian.det) :
    IsUnit (Y.map (Int.castRingHom ℤ_[2])).hessian.det := by
  rw [QuadForm.hessian_map]
  have : (Y.hessian.map (Int.castRingHom ℤ_[2])).det = ((Y.hessian.det : ℤ) : ℤ_[2]) :=
    (RingHom.map_det (Int.castRingHom ℤ_[2]) Y.hessian).symm
  rw [this]
  exact isUnit_intCast_two h

theorem not_two_dvd_phiA_det (k : ℕ) (hk : Even k) : ¬ (2 : ℤ) ∣ (phiA k).hessian.det := by
  rw [phiA_hessian_det]
  obtain ⟨r, rfl⟩ := hk
  omega

/-- Helper: a single column. -/
theorem col_mulVec (x : Fin N → ℤ_[2]) (z : Fin 1 → ℤ_[2]) :
    (Matrix.of fun r (_ : Fin 1) => x r) *ᵥ z = z 0 • x := by
  ext r; simp [mulVec, dotProduct, mul_comm]

/-- **$A \perp \langle c\rangle$ from a representation of $A$ and an orthogonal vector of value $c$.** -/
theorem rep2_orthSum_diag_one {a : ℕ} {G : QuadForm ℤ_[2] N} {A : QuadForm ℤ_[2] a}
    (M₁ : Matrix (Fin N) (Fin a) ℤ_[2]) (h₁ : ∀ y, G.eval (M₁ *ᵥ y) = A.eval y) (x : Fin N → ℤ_[2]) {c : ℤ_[2]}
    (hx : G.eval x = c) (horth : ∀ y, (M₁ *ᵥ y) ⬝ᵥ (G.hessian *ᵥ x) = 0) :
    Rep2 G (QuadForm.orthSum A (QuadForm.diag ![c])) := by
  refine rep2_orthSum M₁ (Matrix.of fun r _ => x r) h₁ (fun z => ?_) (fun y z => ?_)
  · rw [col_mulVec, eval_smul_sq, hx, eval_diag']; simp [mul_comm]
  · rw [col_mulVec, mulVec_smul, dotProduct_smul, horth]; simp

/-- **$A \perp \langle a, c\rangle$ from a representation of $A$ and two orthogonal vectors.** -/
theorem rep2_orthSum_diag_two {k : ℕ} {G : QuadForm ℤ_[2] N} {A : QuadForm ℤ_[2] k}
    (M₁ : Matrix (Fin N) (Fin k) ℤ_[2]) (h₁ : ∀ y, G.eval (M₁ *ᵥ y) = A.eval y) (x y : Fin N → ℤ_[2])
    {a c : ℤ_[2]} (hx : G.eval x = a) (hy : G.eval y = c) (hxy : x ⬝ᵥ (G.hessian *ᵥ y) = 0)
    (hox : ∀ z, (M₁ *ᵥ z) ⬝ᵥ (G.hessian *ᵥ x) = 0) (hoy : ∀ z, (M₁ *ᵥ z) ⬝ᵥ (G.hessian *ᵥ y) = 0) :
    Rep2 G (QuadForm.orthSum A (QuadForm.diag ![a, c])) := by
  let M₂ : Matrix (Fin N) (Fin 2) ℤ_[2] := Matrix.of fun r i => (![x, y] i) r
  have hM₂ : ∀ z, M₂ *ᵥ z = z 0 • x + z 1 • y := fun z => by
    ext r; simp [M₂, mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  refine rep2_orthSum M₁ M₂ h₁ (fun z => ?_) (fun w z => ?_)
  · rw [hM₂, eval_diag', Fin.sum_univ_two]
    have hp := QuadForm.eval_polar G (z 0 • x) (z 1 • y)
    rw [eval_smul_sq, eval_smul_sq, mulVec_smul, dotProduct_smul, smul_dotProduct, hxy, hx, hy] at hp
    simp only [smul_eq_mul, mul_zero] at hp
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    linear_combination hp
  · rw [hM₂, mulVec_add, mulVec_smul, mulVec_smul, dotProduct_add, dotProduct_smul, dotProduct_smul, hox, hoy]
    simp

/-- **From an odd-index decomposition of a probe to its local representation.** -/
theorem repOver_of_decomp {n v : ℕ} {f : QuadForm ℤ n} {φ X : QuadForm ℤ v} (T : Matrix (Fin v) (Fin v) ℤ)
    (hT : Odd T.det) (h : φ.compMat T = X) (hX : Rep2 (f.map (Int.castRingHom ℤ_[2])) (X.map (Int.castRingHom ℤ_[2]))) :
    RepOver ℤ_[2] f φ :=
  repOver_of_rep2 (hX.trans (rep2_of_compMat_odd T hT h))

/-- Helper: from $A^{\mathbb Z_2} \perp S^{\mathbb Z_2}$ to $(A \perp S)^{\mathbb Z_2}$. -/
theorem rep2_map_orthSum {a b : ℕ} {G : QuadForm ℤ_[2] N} {A : QuadForm ℤ a} {B : QuadForm ℤ b}
    (h : Rep2 G (QuadForm.orthSum (A.map (Int.castRingHom ℤ_[2])) (B.map (Int.castRingHom ℤ_[2])))) :
    Rep2 G ((QuadForm.orthSum A B).map (Int.castRingHom ℤ_[2])) :=
  h.congr fun y => (eval_map_orthSum A B y).symm

/-- Helper: a unit times the square of a unit, when congruent modulo $8$. -/
theorem exists_sq_mul_eq {t a : ℤ_[2]} (ht : IsUnit t) (ha : IsUnit a) (h8 : (8 : ℤ_[2]) ∣ t - a) :
    ∃ s, s ^ 2 * t = a := by
  obtain ⟨tu, rfl⟩ := ht
  set r := a * (↑tu⁻¹ : ℤ_[2])
  have hr : IsUnit r := ha.mul (Units.isUnit _)
  have hr1 : r - 1 = (a - tu) * ↑tu⁻¹ := by
    simp only [r, sub_mul, Units.mul_inv]
  have h8' : (8 : ℤ_[2]) ∣ r - 1 := by
    rw [hr1]; exact Dvd.dvd.mul_right (by rw [← neg_sub]; exact (dvd_neg).2 h8) _
  have h4 : (4 : ℤ_[2]) ∣ r - 1 := dvd_trans ⟨2, by norm_num⟩ h8'
  obtain ⟨s, hs⟩ := (isSquare_iff_dvd_eight hr h4).2 h8'
  refine ⟨s, ?_⟩
  rw [sq, ← hs]
  simp only [r, mul_assoc, Units.inv_mul, mul_one]

theorem intCast_dvd_eight_of_emod {a : ℤ} {b : ℤ} (h : a % 8 = b) : (8 : ℤ_[2]) ∣ (a : ℤ_[2]) - b := by
  have : 8 * (a / 8) + a % 8 = a := by omega
  refine ⟨((a / 8 : ℤ) : ℤ_[2]), ?_⟩
  have e : (a : ℤ_[2]) = ((a % 8 : ℤ) : ℤ_[2]) + 8 * ((a / 8 : ℤ) : ℤ_[2]) := by
    conv_lhs => rw [← this]
    push_cast; ring
  rw [e, h]; ring

end QuadFormsKB.Watson1963
