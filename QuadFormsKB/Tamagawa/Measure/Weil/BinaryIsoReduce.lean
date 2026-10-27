import QuadFormsKB.Tamagawa.Measure.Weil.BinaryIsoFacts

/-!
# Isotropic binary forms are similar to a multiple of the hyperbolic plane
**Layer:** a number field $F$; $Q_0$ a nondegenerate binary form over $\mathcal O_F$ with an isotropic vector
$e\in F^2$ ($e\ne0$, $Q_0(e)=0$).

**Proves**
* `iso_eval_fin_two`, `iso_hessian_det_fin_two`: the evaluation $Q(x) = ax_0^2+\beta x_0x_1+\gamma x_1^2$ and the
  determinant $\det H_Q = 4a\gamma-\beta^2$ of a binary form (0-based indices);
* `iso_compMat_hyp`: if $Q$ has $a = Q.\mathrm{coeff}\,0\,0 = 0$ and $\beta = Q.\mathrm{coeff}\,0\,1$, $\gamma = Q.\mathrm{coeff}\,1\,1$,
  then $Q\circ\begin{pmatrix}\beta&-\gamma\\0&\beta\end{pmatrix} = \beta^3\,x_0x_1$;
* **`exists_hyp_similarity`**: there are $d\in F^\times$, $G\in M_2(\mathcal O_F)$ with $\det G\ne0$, $b\in\mathcal O_F\setminus0$,
  $\kappa\in F^\times$ such that $Q_0\circ G = b\cdot(x_0x_1)$ (`simForm`) and $G^{-1}(d\,e) = \kappa\,(1,0)$, i.e. $Q_0$ is
  similar to a multiple of the hyperbolic plane, carrying the isotropic line $Fe$ to the line $F(1,0)$.

*Proof.* Clear denominators so that $d\,e = (p,q)\in\mathcal O_F^2$; complete $(p,q)$ to a matrix $G_1$ with
$\det G_1\ne0$ and first column $(p,q)$; then $Q_0\circ G_1 = \beta x_0x_1+\gamma x_1^2$ with $\beta\ne0$ by
nondegeneracy, and $\begin{pmatrix}\beta&-\gamma\\0&\beta\end{pmatrix}$ finishes. Indices are 0-based.
-/

open Matrix

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.LocalDensity QuadFormsKB.QuadForm
  QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure

/-! ### Coefficient computations for binary forms -/

/-- **A binary form in coordinates**: $Q(x) = Q_{00}x_0^2 + Q_{01}x_0x_1 + Q_{11}x_1^2$. -/
theorem iso_eval_fin_two {R : Type*} [CommRing R] (Q : QuadForm R 2) (x : Fin 2 → R) :
    Q.eval x = Q.coeff 0 0 * x 0 ^ 2 + Q.coeff 0 1 * x 0 * x 1 + Q.coeff 1 1 * x 1 ^ 2 := by
  have h10 : Q.coeff 1 0 = 0 := Q.upper (show (0 : Fin 2) < 1 by decide)
  simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_two, h10]
  ring

/-- **The determinant of the Hessian of a binary form**: $\det H_Q = 4Q_{00}Q_{11} - Q_{01}^2$. -/
theorem iso_hessian_det_fin_two {R : Type*} [CommRing R] (Q : QuadForm R 2) :
    Q.hessian.det = 4 * Q.coeff 0 0 * Q.coeff 1 1 - Q.coeff 0 1 ^ 2 := by
  have h10 : Q.coeff 1 0 = 0 := Q.upper (show (0 : Fin 2) < 1 by decide)
  simp [QuadForm.hessian, Matrix.det_fin_two, h10]
  ring

/-- The coefficients of $\mathrm{hyp}_F = x_0x_1$. -/
theorem iso_hypForm_coeff (F : Type) [Field F] [NumberField F] :
    (hypForm F).coeff 0 0 = 0 ∧ (hypForm F).coeff 0 1 = 1 ∧ (hypForm F).coeff 1 1 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [hypForm, QuadFormsKB.LocalDensity.DVR.hyperbolic, QuadForm.ofUpper]

/-- **Triangular normalization**: if $Q_{00} = 0$ then $Q\circ\begin{pmatrix}\beta&-\gamma\\0&\beta\end{pmatrix} =
\beta^3\,x_0x_1$, where $\beta = Q_{01}$, $\gamma = Q_{11}$. -/
theorem iso_compMat_hyp (F : Type) [Field F] [NumberField F] (Q : QuadForm (𝓞 F) 2) (h00 : Q.coeff 0 0 = 0) :
    Q.compMat !![Q.coeff 0 1, -Q.coeff 1 1; 0, Q.coeff 0 1] = (Q.coeff 0 1 ^ 3) • hypForm F := by
  obtain ⟨k0, k1, k2⟩ := iso_hypForm_coeff F
  have h10 : Q.coeff 1 0 = 0 := Q.upper (show (0 : Fin 2) < 1 by decide)
  apply QuadForm.ext_upper
  intro i j hij
  rw [QuadForm.compMat_coeff, if_pos hij, QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j
  · simp [iso_eval_fin_two Q, h00, k0]
  · have : (0 : Fin 2) ≠ 1 := by decide
    simp [QuadForm.hessian, h00, h10, k1, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mulVec]
    ring
  · exact absurd hij (by decide)
  · simp [iso_eval_fin_two Q, h00, k2]
    ring

/-- A nonzero vector over a domain is the first column of a matrix with nonzero determinant. -/
theorem iso_exists_col {R : Type*} [CommRing R] [IsDomain R] {v : Fin 2 → R} (hv : v ≠ 0) :
    ∃ G : Matrix (Fin 2) (Fin 2) R, G.det ≠ 0 ∧ G 0 0 = v 0 ∧ G 1 0 = v 1 := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨!![v 0, 1; v 1, 0], ?_, by simp, by simp⟩
    simp [Matrix.det_fin_two_of, h1]
  · refine ⟨!![v 0, 0; v 1, 1], ?_, by simp, by simp⟩
    simp [Matrix.det_fin_two_of, h0]

/-! ### The similarity -/

/-- **Every nondegenerate binary form with an isotropic vector is similar to a multiple of the hyperbolic plane,
compatibly with the isotropic line**: there are $d\in F^\times$, $G\in M_2(\mathcal O_F)$ with $\det G\ne0$,
$b\in\mathcal O_F\setminus0$ and $\kappa\in F^\times$ with $Q_0\circ G = b\cdot x_0x_1$ and $G^{-1}(d\,e) = \kappa\,(1,0)$. -/
theorem exists_hyp_similarity {F : Type} [Field F] [NumberField F] {Q₀ : QuadForm (𝓞 F) 2}
    (hQ : Q₀.Nondegenerate) {e : Fin 2 → F} (he : IsIsoVec Q₀ e) :
    ∃ (d : F) (_ : d ≠ 0) (G : Matrix (Fin 2) (Fin 2) (𝓞 F)) (hG : G.det ≠ 0) (b : 𝓞 F) (_ : b ≠ 0)
      (κ : F) (_ : κ ≠ 0),
      simForm Q₀ 1 G = simForm (hypForm F) b 1 ∧
      (((LatChange.glF G hG)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ (d • e) = κ • hypE F := by
  classical
  -- clear denominators
  obtain ⟨m, hm⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 F)) e
  set d : F := algebraMap (𝓞 F) F (m : 𝓞 F) with hd
  have hm0 : (m : 𝓞 F) ≠ 0 := nonZeroDivisors.coe_ne_zero m
  have hd0 : d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hm0
  have hv : ∀ i, ∃ x : 𝓞 F, algebraMap (𝓞 F) F x = d * e i := fun i => by
    obtain ⟨x, hx⟩ := hm i
    exact ⟨x, by rw [hx, Algebra.smul_def]⟩
  choose v hv using hv
  have hvde : (fun i => algebraMap (𝓞 F) F (v i)) = d • e := funext fun i => by simp [hv]
  have hv0 : v ≠ 0 := by
    intro h0
    apply he.1
    have : d • e = 0 := by rw [← hvde, h0]; funext i; simp
    exact (smul_eq_zero.mp this).resolve_left hd0
  have hiso : Q₀.eval v = 0 := by
    apply IsFractionRing.injective (𝓞 F) F
    have hq : qF Q₀ (d • e) = 0 := by rw [qF_smul, he.2, mul_zero]
    rw [← hvde] at hq
    have h1 := iso_eval_fin_two (Q₀.map (algebraMap (𝓞 F) F)) (fun i => algebraMap (𝓞 F) F (v i))
    have h2 := iso_eval_fin_two Q₀ v
    rw [map_zero, h2]
    simp only [map_add, map_mul, map_pow]
    have h3 : qF Q₀ (fun i => algebraMap (𝓞 F) F (v i)) = _ := h1
    rw [h3] at hq
    simpa [QuadForm.map] using hq
  -- first column
  obtain ⟨G₁, hG₁, h10, h11⟩ := iso_exists_col hv0
  set Q₁ := Q₀.compMat G₁ with hQ₁
  have hcol : (fun l => G₁ l 0) = v := funext fun l => by fin_cases l <;> simp [h10, h11]
  have h00 : Q₁.coeff 0 0 = 0 := by
    rw [hQ₁, QuadForm.compMat_coeff, if_pos le_rfl, if_pos rfl, hcol, hiso]
  have hQ₁nd : Q₁.hessian.det ≠ 0 := by
    rw [hQ₁, QuadForm.hessian_compMat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hG₁ hQ) hG₁
  have hβ : Q₁.coeff 0 1 ≠ 0 := by
    intro h
    apply hQ₁nd
    rw [iso_hessian_det_fin_two, h00, h]; ring
  set β := Q₁.coeff 0 1 with hβdef
  set γ := Q₁.coeff 1 1 with hγdef
  set G₂ : Matrix (Fin 2) (Fin 2) (𝓞 F) := !![β, -γ; 0, β] with hG₂
  have hG₂det : G₂.det = β ^ 2 := by simp [hG₂, Matrix.det_fin_two_of]; ring
  have hGdet : (G₁ * G₂).det ≠ 0 := by
    rw [Matrix.det_mul, hG₂det]; exact mul_ne_zero hG₁ (pow_ne_zero _ hβ)
  have hβF : algebraMap (𝓞 F) F β ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hβ
  refine ⟨d, hd0, G₁ * G₂, hGdet, β ^ 3, pow_ne_zero _ hβ, (algebraMap (𝓞 F) F β)⁻¹, inv_ne_zero hβF, ?_, ?_⟩
  · have h1 : ∀ S : QuadForm (𝓞 F) 2, simForm S 1 1 = S := fun S => by
      show (1 : 𝓞 F) • S.compMat 1 = S
      rw [QuadForm.compMat_one]; ext a b; simp [QuadForm.smul_coeff]
    have h2 : ∀ (S : QuadForm (𝓞 F) 2) (G : Matrix (Fin 2) (Fin 2) (𝓞 F)), simForm S 1 G = S.compMat G := fun S G => by
      show (1 : 𝓞 F) • S.compMat G = S.compMat G
      ext a b; simp [QuadForm.smul_coeff]
    have h3 : simForm (hypForm F) (β ^ 3) 1 = (β ^ 3) • hypForm F := by
      show (β ^ 3) • (hypForm F).compMat 1 = _
      rw [QuadForm.compMat_one]
    rw [h2, h3, ← QuadForm.compMat_mul, ← hQ₁]
    exact iso_compMat_hyp F Q₁ h00
  · set P := LatChange.glF (G₁ * G₂) hGdet with hP
    have hPv : (P : Matrix (Fin 2) (Fin 2) F) *ᵥ ((algebraMap (𝓞 F) F β)⁻¹ • hypE F) = d • e := by
      rw [← hvde]
      funext i
      have hcoe : (P : Matrix (Fin 2) (Fin 2) F) = (G₁ * G₂).map (algebraMap (𝓞 F) F) := LatChange.glF_val _ _
      rw [hcoe]
      fin_cases i
      · simp [hG₂, hypE, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply, h10, h11]
        field_simp
      · simp [hG₂, hypE, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply, h10, h11]
        field_simp
    rw [← hPv, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

end QuadFormsKB.Tamagawa.Measure.Weil
