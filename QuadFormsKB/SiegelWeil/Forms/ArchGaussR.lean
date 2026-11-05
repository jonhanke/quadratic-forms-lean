/-
# The Gaussian integral of degree $r$ on $\mathbb R^{N\times r}$ (Siegel–Weil for forms by forms)

**Layer:** local, one real place; classical analysis on $\mathbb R^{N\times r}$ (no global input).

**Setting.** $Z \in \mathbb H_r$ (`WeilRep.Genus.siegelH r`: $Z^{\mathsf T} = Z$, $\operatorname{Im}Z$ positive definite), $r \ge 0$;
$Q = \sum_{i<N}s_ix_i^2$ a positive definite diagonal form on $\mathbb R^N$, $s_i > 0$, with Gram matrix $S = \operatorname{diag}(s)$
(0-based indices). Points of $\mathbb R^{N\times r}$ are $X = (X_0, \dots, X_{r-1})$, $X_a \in \mathbb R^N$ the columns, and
$Q[X] = X^{\mathsf T}SX$, $(X^{\mathsf T}SX)_{ab} = \sum_is_iX_{a,i}X_{b,i}$.

**Definitions.**
* `qZ Z x` $= x^{\mathsf T}Zx = \sum_{a,b}x_aZ_{ab}x_b$ for $x \in \mathbb R^r$;
* `gaussOne Z` $= g(Z) = \int_{\mathbb R^r}e^{2\pi i\,x^{\mathsf T}Zx}\,dx$;
* `gaussR s Z` $= G_S(Z) = \int_{\mathbb R^{N\times r}}e^{2\pi i\operatorname{tr}(X^{\mathsf T}SX\,Z)}\,dX$, the degree-$r$ analogue of `gaussQ`.

**Results.**
* `exists_decomp_siegelH`: $Z = R^{\mathsf T}(D + iI)R$ with $R$ real invertible and $D$ real diagonal (simultaneous diagonalization of
  $\operatorname{Re}Z$ and $\operatorname{Im}Z$);
* `gaussOne_sq`: $g(Z)^2 = \det(-2iZ)^{-1}$;
* `gaussOne_smul`: $g(tZ) = t^{-r/2}g(Z)$ for $t > 0$;
* **`gaussR_eq`**: for $N = 2k$,
  $$G_S(Z) = \det(2S)^{-r/2}\,\det(-iZ)^{-k} = \Big(\prod_{i<N}2s_i\Big)^{-r/2}\det(Z/i)^{-N/2},$$
  with no branch ambiguity since $N$ is even. For $r = 1$ it is `gaussQ_eq` (with $\tau = Z$).

Sources: Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. of Math. 36 (1935), §§ on the archimedean factor
[unverified]; Siegel, *Einführung in die Theorie der Modulfunktionen n-ten Grades*, Math. Ann. 116 (1939), §6 (the integral
$\int e^{\pi i\operatorname{tr}(X^{\mathsf T}SXZ)}dX$) [unverified]; Kudla, *Some extensions of the Siegel–Weil formula* (2008), §1 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Genus.SiegelSpace
import QuadFormsKB.Tamagawa.Measure.PiProdLintegral

open MeasureTheory Matrix Complex
open scoped Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms.ArchR

open WeilRep.Genus

/-! ### Orthogonal diagonalization and the decomposition of a point of $\mathbb H_r$ -/

/-- **Orthogonal diagonalization** of a real symmetric matrix: $A = U\operatorname{diag}(\lambda)U^{\mathsf T}$ with $U^{\mathsf T}U = UU^{\mathsf T} = 1$,
$\lambda$ the eigenvalues. -/
lemma exists_orth_diag {r : ℕ} {A : Matrix (Fin r) (Fin r) ℝ} (hA : A.IsHermitian) :
    ∃ U : Matrix (Fin r) (Fin r) ℝ, Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧ A = U * diagonal hA.eigenvalues * Uᵀ := by
  set U : Matrix (Fin r) (Fin r) ℝ := (hA.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ)
  have hstar : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hUU : Uᵀ * U = 1 := by
    rw [← hstar]; exact Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hUU' : U * Uᵀ = 1 := by
    rw [← hstar]; exact Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hdiag : Uᵀ * A * U = diagonal hA.eigenvalues := by
    have := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    rw [← hstar]
    convert this using 2
    funext i; simp
  refine ⟨U, hUU, hUU', ?_⟩
  rw [← hdiag]
  simp only [← Matrix.mul_assoc, hUU', Matrix.one_mul]
  rw [Matrix.mul_assoc, hUU', Matrix.mul_one]

lemma cR_mul {r : ℕ} (A B : Matrix (Fin r) (Fin r) ℝ) : cR (A * B) = cR A * cR B :=
  Matrix.map_mul (f := Complex.ofRealHom)

/-- **Simultaneous diagonalization** of $\operatorname{Re}Z$ and $\operatorname{Im}Z$ for $Z \in \mathbb H_r$:
$Z = R^{\mathsf T}(\operatorname{diag}(d) + iI)R$ with $R$ real, $\det R \ne 0$, $d \in \mathbb R^r$. -/
theorem exists_decomp_siegelH {r : ℕ} {Z : Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelH r) :
    ∃ (R : Matrix (Fin r) (Fin r) ℝ) (d : Fin r → ℝ), R.det ≠ 0 ∧
      Z = cR Rᵀ * diagonal (fun j => (d j : ℂ) + I) * cR R := by
  obtain ⟨hsym, hY⟩ := hZ
  set Y := Z.map Complex.im with hYdef
  set X0 := Z.map Complex.re with hX0def
  have hX0 : X0ᵀ = X0 := by rw [hX0def, ← transpose_map, hsym]
  obtain ⟨U, hUU, hUU', hYeq⟩ := exists_orth_diag hY.isHermitian
  set lam := hY.isHermitian.eigenvalues
  have hlpos : ∀ i, 0 < lam i := hY.eigenvalues_pos
  set P : Matrix (Fin r) (Fin r) ℝ := diagonal (fun i => Real.sqrt (lam i)) * Uᵀ
  set Pi' : Matrix (Fin r) (Fin r) ℝ := U * diagonal (fun i => (Real.sqrt (lam i))⁻¹)
  have hsq : ∀ i, Real.sqrt (lam i) ≠ 0 := fun i => (Real.sqrt_pos.2 (hlpos i)).ne'
  have hd1 : diagonal (fun i => (Real.sqrt (lam i))⁻¹) * diagonal (fun i => Real.sqrt (lam i)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact inv_mul_cancel₀ (hsq i)
  have hd2 : diagonal (fun i => Real.sqrt (lam i)) * diagonal (fun i => (Real.sqrt (lam i))⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hsq i)
  have hPiP : Pi' * P = 1 := by
    simp only [Pi', P, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (diagonal _) (diagonal _), hd1, Matrix.one_mul, hUU']
  have hPPi : P * Pi' = 1 := by
    simp only [Pi', P, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᵀ U, hUU, Matrix.one_mul, hd2]
  have hYP : Y = Pᵀ * P := by
    rw [hYeq]
    simp only [P, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
    congr 1
    rw [← Matrix.mul_assoc, diagonal_mul_diagonal]
    congr 2
    funext i
    rw [Real.mul_self_sqrt (hlpos i).le]
  set C := Pi'ᵀ * X0 * Pi'
  have hC : C.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    simp only [C, transpose_mul, transpose_transpose, hX0, Matrix.mul_assoc]
  obtain ⟨V, hVV, hVV', hCeq⟩ := exists_orth_diag hC
  set d := hC.eigenvalues
  set R := Vᵀ * P
  have hRR : Rᵀ * R = Y := by
    simp only [R, transpose_mul, transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V Vᵀ, hVV', Matrix.one_mul, hYP]
  have hRdR : Rᵀ * diagonal d * R = X0 := by
    simp only [R, transpose_mul, transpose_transpose, Matrix.mul_assoc]
    rw [show V * (diagonal d * (Vᵀ * P)) = C * P by rw [hCeq]; simp only [Matrix.mul_assoc]]
    simp only [C, Matrix.mul_assoc]
    rw [hPiP, Matrix.mul_one, ← Matrix.mul_assoc, ← transpose_mul, hPiP, transpose_one, Matrix.one_mul]
  refine ⟨R, d, ?_, ?_⟩
  · intro h0
    have := congrArg Matrix.det hRR
    rw [det_mul, det_transpose, h0, zero_mul] at this
    exact hY.det_pos.ne' this.symm
  · have hdiag : diagonal (fun j => (d j : ℂ) + I) = cR (diagonal d) + I • 1 := by
      ext i j
      by_cases h : i = j
      · subst h; simp
      · simp [h]
    rw [hdiag, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      ← cR_mul, ← cR_mul, ← cR_mul, hRdR, hRR]
    ext i j
    apply Complex.ext <;> simp [X0, Y]

/-! ### The Gaussian integral on $\mathbb R^r$ -/

/-- **The quadratic form** $x^{\mathsf T}Zx = \sum_{a,b}x_aZ_{ab}x_b$ of a complex $r\times r$ matrix $Z$ at a real vector $x \in \mathbb R^r$. -/
def qZ {r : ℕ} (Z : Matrix (Fin r) (Fin r) ℂ) (x : Fin r → ℝ) : ℂ :=
  (fun a => (x a : ℂ)) ⬝ᵥ (Z *ᵥ fun a => (x a : ℂ))

/-- **The Gaussian integral on $\mathbb R^r$** $g(Z) = \int_{\mathbb R^r}e^{2\pi i\,x^{\mathsf T}Zx}\,dx$ (Lebesgue measure). -/
def gaussOne {r : ℕ} (Z : Matrix (Fin r) (Fin r) ℂ) : ℂ :=
  ∫ x : Fin r → ℝ, cexp (2 * π * I * qZ Z x)

lemma qZ_smul {r : ℕ} (t : ℂ) (Z : Matrix (Fin r) (Fin r) ℂ) (x : Fin r → ℝ) : qZ (t • Z) x = t * qZ Z x := by
  simp [qZ, smul_mulVec, dotProduct_smul]

lemma qZ_smul_vec {r : ℕ} (c : ℝ) (Z : Matrix (Fin r) (Fin r) ℂ) (x : Fin r → ℝ) :
    qZ Z (c • x) = (c : ℂ) ^ 2 * qZ Z x := by
  have : (fun a => (((c • x) a : ℝ) : ℂ)) = (c : ℂ) • fun a => (x a : ℂ) := by
    funext a; simp
  rw [qZ, qZ, this, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring

lemma qZ_decomp {r : ℕ} (R : Matrix (Fin r) (Fin r) ℝ) (δ : Fin r → ℂ) (x : Fin r → ℝ) :
    qZ (cR Rᵀ * diagonal δ * cR R) x = ∑ j, δ j * (((R *ᵥ x) j : ℝ) : ℂ) ^ 2 := by
  have hx : cR R *ᵥ (fun a => (x a : ℂ)) = fun j => (((R *ᵥ x) j : ℝ) : ℂ) := by
    funext j; simp [mulVec, dotProduct]
  have hT : cR Rᵀ = (cR R)ᵀ := by ext; simp
  rw [qZ, ← mulVec_mulVec, ← mulVec_mulVec, hT, dotProduct_mulVec, vecMul_transpose, hx]
  simp only [mulVec_diagonal, dotProduct]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- **The Gaussian integral in diagonal form:** for $R$ real invertible and $d \in \mathbb R^r$,
$g\big(R^{\mathsf T}(\operatorname{diag}(d) + iI)R\big) = |\det R|^{-1}\prod_j\big(\pi/b_j\big)^{1/2}$, $b_j = 2\pi(1 - id_j)$. -/
lemma gaussOne_decomp {r : ℕ} {R : Matrix (Fin r) (Fin r) ℝ} (hR : R.det ≠ 0) (d : Fin r → ℝ) :
    gaussOne (cR Rᵀ * diagonal (fun j => (d j : ℂ) + I) * cR R) =
      ((|R.det⁻¹| : ℝ) : ℂ) * ∏ j, ((π : ℂ) / (2 * π * (1 - I * d j))) ^ (1 / 2 : ℂ) := by
  set b : Fin r → ℂ := fun j => 2 * π * (1 - I * d j) with hbdef
  have hb : ∀ j, 0 < (b j).re := by
    intro j; simp [b, Complex.mul_re]; positivity
  set f : (Fin r → ℝ) → ℂ := fun y => ∏ j, cexp (-b j * (y j : ℂ) ^ 2)
  have hint : ∀ x, cexp (2 * π * I * qZ (cR Rᵀ * diagonal (fun j => (d j : ℂ) + I) * cR R) x) =
      f (Matrix.toLin' R x) := by
    intro x
    rw [qZ_decomp, Finset.mul_sum, Complex.exp_sum, Matrix.toLin'_apply]
    refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    simp only [b]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi hR
  have hm : Measurable (Matrix.toLin' R) := (Matrix.toLin' R).continuous_of_finiteDimensional.measurable
  have hfc : Continuous f := by simp only [f]; fun_prop
  unfold gaussOne
  simp_rw [hint]
  rw [← integral_map hm.aemeasurable hfc.aestronglyMeasurable, hmap, integral_smul_measure, volume_pi,
    integral_fintype_prod_eq_prod (f := fun j (t : ℝ) => cexp (-b j * (t : ℂ) ^ 2))]
  simp only [integral_gaussian_complex (hb _), b]
  rw [ENNReal.toReal_ofReal (abs_nonneg _), Complex.real_smul]

lemma sq_cpow_half (x : ℂ) : (x ^ (1 / 2 : ℂ)) ^ 2 = x := by
  rw [one_div]; exact cpow_ofNat_inv_pow x 2

/-- **The square of the Gaussian integral:** $g(Z)^2 = \det(-2iZ)^{-1}$ for $Z \in \mathbb H_r$. -/
theorem gaussOne_sq {r : ℕ} {Z : Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelH r) :
    gaussOne Z ^ 2 = (det ((-2 * I) • Z))⁻¹ := by
  obtain ⟨R, d, hR, rfl⟩ := exists_decomp_siegelH hZ
  rw [gaussOne_decomp hR, mul_pow, ← Finset.prod_pow]
  simp only [sq_cpow_half]
  rw [det_smul, det_mul, det_mul, det_diagonal, Fintype.card_fin]
  have hdR : (cR R).det = (R.det : ℂ) := by
    rw [show cR R = R.map Complex.ofRealHom from rfl, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
  have hdRT : (cR Rᵀ).det = (R.det : ℂ) := by
    rw [show cR Rᵀ = Rᵀ.map Complex.ofRealHom from rfl, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_transpose]
    rfl
  rw [hdR, hdRT, ← Fin.prod_const r (-2 * I)]
  have hR' : (R.det : ℂ) ≠ 0 := by exact_mod_cast hR
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hne : ∀ j, (1 - I * d j) ≠ 0 := by
    intro j h; have := congrArg Complex.re h; simp at this
  have hP : ∏ j, (π : ℂ) / (2 * π * (1 - I * d j)) = (∏ j, (-2 * I) * ((d j : ℂ) + I))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    have h1 : (-2 * I) * ((d j : ℂ) + I) = 2 * (1 - I * d j) := by ring_nf; rw [Complex.I_sq]; ring
    rw [h1]
    field_simp [hne j]
  have hA : ((|R.det⁻¹| : ℝ) : ℂ) ^ 2 = ((R.det : ℂ) * R.det)⁻¹ := by
    rw [← Complex.ofReal_pow, sq_abs, ← Complex.ofReal_mul, ← Complex.ofReal_inv]; congr 1; ring
  rw [hP, hA, ← mul_inv, Finset.prod_mul_distrib]
  congr 1
  ring

/-- **Scaling:** $g(tZ) = t^{-r/2}g(Z)$ for $t > 0$ (substitute $x \mapsto \sqrt t\,x$). -/
theorem gaussOne_smul {r : ℕ} {t : ℝ} (ht : 0 < t) (Z : Matrix (Fin r) (Fin r) ℂ) :
    gaussOne ((t : ℂ) • Z) = (((Real.sqrt t ^ r)⁻¹ : ℝ) : ℂ) * gaussOne Z := by
  have h : ∀ x, cexp (2 * π * I * qZ ((t : ℂ) • Z) x) = cexp (2 * π * I * qZ Z (Real.sqrt t • x)) := by
    intro x
    rw [qZ_smul, qZ_smul_vec, ← Complex.ofReal_pow, Real.sq_sqrt ht.le]
  unfold gaussOne
  simp_rw [h]
  rw [Measure.integral_comp_smul volume (fun x => cexp (2 * π * I * qZ Z x)) (Real.sqrt t), Module.finrank_fin_fun,
    abs_of_pos (by positivity), Complex.real_smul]

/-- **The Gaussian integral of degree $r$** (`gaussR s Z`):
$$G_S(Z) = \int_{\mathbb R^{N\times r}}\exp\big(2\pi i\operatorname{tr}(X^{\mathsf T}SX\,Z)\big)\,dX
  = \int\exp\Big(2\pi i\sum_{a,b<r}\Big(\sum_{i<N}s_iX_{a,i}X_{b,i}\Big)Z_{ba}\Big)\,dX,$$
$S = \operatorname{diag}(s)$, $X = (X_0, \dots, X_{r-1})$ the columns ($X_a \in \mathbb R^N$, Lebesgue measure on $(\mathbb R^N)^r$). For $r = 1$ this is
`gaussQ`. Parameters: `s` (the diagonal of the Gram matrix of $Q = \sum_is_ix_i^2$), `Z` (an $r\times r$ complex matrix). -/
@[kb "siegel1939" "§6 (the Gaussian integral over rectangular matrices) [unverified]"]
def gaussR {N r : ℕ} (s : Fin N → ℝ) (Z : Matrix (Fin r) (Fin r) ℂ) : ℂ :=
  ∫ X : Fin r → Fin N → ℝ, cexp (2 * π * I * ∑ a, ∑ b, ((∑ i, s i * X a i * X b i : ℝ) : ℂ) * Z b a)

/-- The swap $(\mathbb R^N)^r \cong (\mathbb R^r)^N$ of the two indices of a matrix, as a measurable equivalence. -/
def swapEquiv (N r : ℕ) : (Fin r → Fin N → ℝ) ≃ᵐ (Fin N → Fin r → ℝ) where
  toEquiv := Equiv.piComm _
  measurable_toFun := measurable_pi_iff.2 fun k => measurable_pi_iff.2 fun i =>
    (measurable_pi_apply k).comp (measurable_pi_apply i)
  measurable_invFun := measurable_pi_iff.2 fun k => measurable_pi_iff.2 fun i =>
    (measurable_pi_apply k).comp (measurable_pi_apply i)

/-- The integrand of $G_S$ as a product over the rows: $e^{2\pi i\operatorname{tr}(X^{\mathsf T}SXZ)} = \prod_{i<N}e^{2\pi i\,s_i\,x^{(i)\mathsf T}Zx^{(i)}}$,
$x^{(i)} = (X_{a,i})_a$. -/
lemma gaussR_integrand_eq {N r : ℕ} (s : Fin N → ℝ) (Z : Matrix (Fin r) (Fin r) ℂ) (X : Fin r → Fin N → ℝ) :
    cexp (2 * π * I * ∑ a, ∑ b, ((∑ i, s i * X a i * X b i : ℝ) : ℂ) * Z b a) =
      ∏ i, cexp (2 * π * I * qZ ((s i : ℂ) • Z) (swapEquiv N r X i)) := by
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.mul_sum]
  congr 1
  simp only [qZ, dotProduct, mulVec, swapEquiv, MeasurableEquiv.coe_mk, Equiv.piComm_apply,
    Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Function.swap, Matrix.smul_apply, smul_eq_mul]
  ring

/-- **Row factorization:** $G_S(Z) = \prod_{i<N}g(s_iZ)$ (the rows $x^{(i)} = (X_{a,i})_a \in \mathbb R^r$ are independent variables). -/
theorem gaussR_eq_prod {N r : ℕ} (s : Fin N → ℝ) (Z : Matrix (Fin r) (Fin r) ℂ) :
    gaussR s Z = ∏ i, gaussOne ((s i : ℂ) • Z) := by
  have hexp := gaussR_integrand_eq s Z
  have hmp : MeasurePreserving (swapEquiv N r) volume volume :=
    QuadFormsKB.Tamagawa.Measure.measurePreserving_piComm (ι := Fin r) (κ := Fin N) (volume : Measure ℝ)
  unfold gaussR
  simp_rw [hexp]
  rw [hmp.integral_comp (swapEquiv N r).measurableEmbedding
    (fun W : Fin N → Fin r → ℝ => ∏ i, cexp (2 * π * I * qZ ((s i : ℂ) • Z) (W i)))]
  rw [volume_pi, integral_fintype_prod_eq_prod (f := fun i (x : Fin r → ℝ) => cexp (2 * π * I * qZ ((s i : ℂ) • Z) x))]
  rfl

/-- **The Gaussian integral of degree $r$** (Siegel): for $N = 2k$, $s_i > 0$ and $Z \in \mathbb H_r$,
$$G_S(Z) = \Big(\prod_{i<N}s_i^{-r/2}\Big)\det(-2iZ)^{-k} = \det(2S)^{-r/2}\det(-iZ)^{-N/2}.$$
No branch of the square root is involved, $N$ being even. -/
@[kb "siegel1939" "§6 (the Gaussian integral over rectangular matrices) [unverified]"]
theorem gaussR_eq {k r : ℕ} (s : Fin (2 * k) → ℝ) (hs : ∀ i, 0 < s i) {Z : Matrix (Fin r) (Fin r) ℂ}
    (hZ : Z ∈ siegelH r) :
    gaussR s Z = ((∏ i, (Real.sqrt (s i) ^ r)⁻¹ : ℝ) : ℂ) * (det ((-2 * I) • Z))⁻¹ ^ k := by
  rw [gaussR_eq_prod]
  simp only [gaussOne_smul (hs _)]
  rw [Finset.prod_mul_distrib, Fin.prod_const, pow_mul, gaussOne_sq hZ, Complex.ofReal_prod]

/-! ### Integrability -/

/-- $tZ \in \mathbb H_r$ for $Z \in \mathbb H_r$ and $t > 0$. -/
lemma smul_mem_siegelH {r : ℕ} {t : ℝ} (ht : 0 < t) {Z : Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelH r) :
    (t : ℂ) • Z ∈ siegelH r := by
  refine ⟨by rw [transpose_smul, hZ.1], ?_⟩
  have : ((t : ℂ) • Z).map Complex.im = t • Z.map Complex.im := by
    ext i j; simp
  rw [this]
  exact hZ.2.smul ht

/-- **The Gaussian is integrable:** $x \mapsto e^{2\pi i\,x^{\mathsf T}Zx}$ is integrable on $\mathbb R^r$ for $Z \in \mathbb H_r$. -/
theorem integrable_gaussOne {r : ℕ} {Z : Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelH r) :
    Integrable fun x : Fin r → ℝ => cexp (2 * π * I * qZ Z x) := by
  obtain ⟨R, d, hR, rfl⟩ := exists_decomp_siegelH hZ
  set b : Fin r → ℂ := fun j => 2 * π * (1 - I * d j)
  have hb : ∀ j, 0 < (b j).re := by
    intro j; simp [b, Complex.mul_re]; positivity
  set f : (Fin r → ℝ) → ℂ := fun y => ∏ j, cexp (-b j * (y j : ℂ) ^ 2)
  have hint : (fun x => cexp (2 * π * I * qZ (cR Rᵀ * diagonal (fun j => (d j : ℂ) + I) * cR R) x)) =
      f ∘ Matrix.toLin' R := by
    funext x
    rw [Function.comp_apply, qZ_decomp, Finset.mul_sum, Complex.exp_sum, Matrix.toLin'_apply]
    refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    simp only [b]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hf : Integrable f := by
    have := Integrable.fintype_prod (f := fun j (t : ℝ) => cexp (-b j * (t : ℂ) ^ 2))
      (μ := fun _ => volume) (fun j => integrable_cexp_neg_mul_sq (hb j))
    simpa [f, volume_pi] using this
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi hR
  have hm : Measurable (Matrix.toLin' R) := (Matrix.toLin' R).continuous_of_finiteDimensional.measurable
  have hfc : Continuous f := by simp only [f]; fun_prop
  rw [hint, ← integrable_map_measure hfc.aestronglyMeasurable hm.aemeasurable, hmap]
  exact hf.smul_measure ENNReal.ofReal_ne_top

/-- **The integrand of $G_S$ is integrable** on $\mathbb R^{N\times r}$ for $s_i > 0$ and $Z \in \mathbb H_r$. -/
theorem integrable_gaussR {N r : ℕ} {s : Fin N → ℝ} (hs : ∀ i, 0 < s i) {Z : Matrix (Fin r) (Fin r) ℂ}
    (hZ : Z ∈ siegelH r) :
    Integrable fun X : Fin r → Fin N → ℝ => cexp (2 * π * I * ∑ a, ∑ b, ((∑ i, s i * X a i * X b i : ℝ) : ℂ) * Z b a) := by
  simp_rw [gaussR_integrand_eq s Z]
  have hmp : MeasurePreserving (swapEquiv N r) volume volume :=
    QuadFormsKB.Tamagawa.Measure.measurePreserving_piComm (ι := Fin r) (κ := Fin N) (volume : Measure ℝ)
  have h := Integrable.fintype_prod (f := fun i (x : Fin r → ℝ) => cexp (2 * π * I * qZ ((s i : ℂ) • Z) x))
    (μ := fun _ => volume) (fun i => integrable_gaussOne (smul_mem_siegelH (hs i) hZ))
  rw [← volume_pi] at h
  exact (hmp.integrable_comp_emb (swapEquiv N r).measurableEmbedding).mpr h

end QuadFormsKB.SiegelWeil.Forms.ArchR
