/-
# The self-density of the hyperbolic plane
**Layer:** DVR, every residue characteristic (dyadic included: $H$ is even unimodular).

**Proves** `localDensityForm_hyperbolic`: for the hyperbolic plane $H(x_0, x_1) = x_0 x_1$,
$$\beta_\pi(H, H) = \frac{|O(\bar H)|}{q} = \frac{2(q - 1)}{q} = 2(1 - q^{-1}),$$
the case $n = 2m$, $m = 1$, $\chi = +1$ of the closed form $2(1 - \chi q^{-m})\prod_{i=1}^{m-1}(1 - q^{-2i})$ for
unimodular forms [unverified] (Siegel's $\alpha_\pi(H, H) = 1 - q^{-1}$). Over a field $K$, the isometries of $H$ are
$\mathrm{diag}(u, u^{-1})$ and the antidiagonal $\begin{pmatrix} 0 & u^{-1} \\ u & 0 \end{pmatrix}$, $u \in K^\times$
(`card_orth_hyperbolic_field`), so $|O(\bar H)| = 2(q-1)$.
**Depends on** `FormDensitySelf.lean`.
-/
import QuadFormsKB.LocalDensity.FormDensitySelf

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm Matrix

set_option linter.unusedSectionVars false
set_option linter.deprecated false

/-- **The hyperbolic plane** $H(x_0, x_1) = x_0 x_1$ (coefficients $c_{01} = 1$, $c_{00} = c_{11} = 0$). -/
@[kb "omeara1963" "§42, p. 94 (hyperbolic plane, row 42.d3; scaled by 1/2)"]
def hyperbolic (A : Type*) [CommRing A] : QuadForm A 2 := QuadForm.ofUpper ![![0, 1], ![0, 0]]

section Field

variable {K : Type*} [Field K]

theorem hyperbolic_map {A : Type*} [CommRing A] (f : A →+* K) : (hyperbolic A).map f = hyperbolic K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hyperbolic, QuadForm.map, QuadForm.ofUpper]

/-- The isometry condition $H \circ X = H$ in coordinates. -/
theorem compMat_hyperbolic_iff (X : Matrix (Fin 2) (Fin 2) K) :
    (hyperbolic K).compMat X = hyperbolic K ↔
      X 0 0 * X 1 0 = 0 ∧ X 0 1 * X 1 1 = 0 ∧ X 0 0 * X 1 1 + X 1 0 * X 0 1 = 1 := by
  have e00 : ((hyperbolic K).compMat X).coeff 0 0 = X 0 0 * X 1 0 := by
    simp [compMat_coeff, hyperbolic, QuadForm.eval, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_two]
  have e11 : ((hyperbolic K).compMat X).coeff 1 1 = X 0 1 * X 1 1 := by
    simp [compMat_coeff, hyperbolic, QuadForm.eval, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_two]
  have e01 : ((hyperbolic K).compMat X).coeff 0 1 = X 0 0 * X 1 1 + X 1 0 * X 0 1 := by
    simp [compMat_coeff, hyperbolic, QuadForm.hessian, QuadForm.ofUpper, dotProduct, mulVec,
      Fin.sum_univ_two]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · rw [← e00, h]; simp [hyperbolic, QuadForm.ofUpper]
    · rw [← e11, h]; simp [hyperbolic, QuadForm.ofUpper]
    · rw [← e01, h]; simp [hyperbolic, QuadForm.ofUpper]
  · rintro ⟨h0, h1, h2⟩
    apply ext_upper
    intro i j hij
    fin_cases i <;> fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue] at *; rw [e00, h0]; simp [hyperbolic, QuadForm.ofUpper]
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at *; rw [e01, h2]
      simp [hyperbolic, QuadForm.ofUpper]
    · exact absurd hij (by decide)
    · simp only [Fin.mk_one, Fin.isValue] at *; rw [e11, h1]; simp [hyperbolic, QuadForm.ofUpper]

/-- **$|O(H)| = 2(|K| - 1)$ over a finite field $K$:** the isometries are $\mathrm{diag}(u, u^{-1})$ and
$\begin{pmatrix} 0 & u^{-1} \\ u & 0\end{pmatrix}$. -/
theorem card_orth_hyperbolic_field [Fintype K] :
    Nat.card {X : Matrix (Fin 2) (Fin 2) K // (hyperbolic K).compMat X = hyperbolic K} =
      2 * (Fintype.card K - 1) := by
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight compMat_hyperbolic_iff)]
  set S := fun X : Matrix (Fin 2) (Fin 2) K =>
    X 0 0 * X 1 0 = 0 ∧ X 0 1 * X 1 1 = 0 ∧ X 0 0 * X 1 1 + X 1 0 * X 0 1 = 1
  have hsplit := natCard_split S (fun X => S X ∧ X 0 0 ≠ 0) (fun X => S X ∧ ¬ X 0 0 ≠ 0) (fun X => X 0 0 ≠ 0)
    (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  -- diagonal isometries
  have e0 : {X // S X ∧ X 0 0 ≠ 0} ≃ Kˣ :=
    { toFun := fun X => Units.mk0 (X.1 0 0) X.2.2
      invFun := fun u => ⟨!![(u : K), 0; 0, (u⁻¹ : Kˣ)], by
        refine ⟨⟨by simp, by simp, by simp⟩, by simp⟩⟩
      left_inv := fun ⟨X, ⟨h0, h1, h2⟩, h3⟩ => by
        have h10 : X 1 0 = 0 := (mul_eq_zero.mp h0).resolve_left h3
        rw [h10, zero_mul, add_zero] at h2
        have h11 : X 1 1 = (X 0 0)⁻¹ := eq_inv_of_mul_eq_one_right h2
        have h01 : X 0 1 = 0 := (mul_eq_zero.mp h1).resolve_right (by rw [h11]; exact inv_ne_zero h3)
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h10, h11, h01]
      right_inv := fun u => by ext; simp }
  -- antidiagonal isometries
  have e1 : {X // S X ∧ ¬ X 0 0 ≠ 0} ≃ Kˣ :=
    { toFun := fun X => Units.mk0 (X.1 1 0) (by
        intro h
        have h2 := X.2.1.2.2
        rw [not_not.mp X.2.2, h] at h2
        simp at h2)
      invFun := fun u => ⟨!![0, (u⁻¹ : Kˣ); (u : K), 0], by
        refine ⟨⟨by simp, by simp, by simp⟩, by simp⟩⟩
      left_inv := fun ⟨X, ⟨h0, h1, h2⟩, h3⟩ => by
        have h00 : X 0 0 = 0 := not_not.mp h3
        rw [h00, zero_mul, zero_add] at h2
        have h10 : X 1 0 ≠ 0 := left_ne_zero_of_mul_eq_one h2
        have h01 : X 0 1 = (X 1 0)⁻¹ := eq_inv_of_mul_eq_one_right h2
        have h11 : X 1 1 = 0 := (mul_eq_zero.mp h1).resolve_left (by rw [h01]; exact inv_ne_zero h10)
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h00, h11, h01]
      right_inv := fun u => by ext; simp }
  rw [hsplit, Nat.card_congr e0, Nat.card_congr e1, Nat.card_eq_fintype_card, Fintype.card_units]
  ring

end Field

/-- **The self-density of the hyperbolic plane** at every prime: $\beta_\pi(H, H) = 2(q - 1)/q = 2(1 - q^{-1})$
(Siegel's $\alpha_\pi(H, H) = 1 - q^{-1}$) [closed form: unverified against the literature; proved here]. -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem localDensityForm_hyperbolic {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Finite (IsLocalRing.ResidueField R)] (π : R) (hπ : Irreducible π) :
    localDensityForm (hyperbolic R) (hyperbolic R) π = 2 * ((q R : ℝ) - 1) / q R := by
  classical
  have hdet : IsUnit (hyperbolic R).hessian.det := by
    have : (hyperbolic R).hessian.det = -1 := by
      simp [hyperbolic, QuadForm.hessian, QuadForm.ofUpper, Matrix.det_fin_two]
    rw [this]; exact isUnit_one.neg
  rw [localDensityForm_eq_of_isUnit _ _ π hπ hdet le_rfl]
  have hmax : (Ideal.span {π ^ 1}).IsMaximal := by
    rw [pow_one, ← hπ.maximalIdeal_eq]; exact IsLocalRing.maximalIdeal.isMaximal R
  let _ : Field (R ⧸ Ideal.span {π ^ 1}) := Ideal.Quotient.field _
  have := finite_quot_pow π hπ 1
  let _ : Fintype (R ⧸ Ideal.span {π ^ 1}) := Fintype.ofFinite _
  have hcount : repCountForm (hyperbolic R) (hyperbolic R) π 1 = 2 * (q R - 1) := by
    unfold repCountForm
    rw [hyperbolic_map, card_orth_hyperbolic_field, ← Nat.card_eq_fintype_card, card_quot_pow π hπ, pow_one]
  have hq1 : 1 ≤ q R := q_pos
  rw [hcount]
  norm_num
  rw [Nat.cast_sub hq1]
  push_cast
  ring

end QuadFormsKB.LocalDensity.DVR
