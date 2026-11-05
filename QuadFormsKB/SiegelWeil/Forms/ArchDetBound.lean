/-
# A lower bound for $|\det(Z + X)|$ and the integrability of $|\det(Z + X)|^{-k}$ over symmetric $X$
**Layer:** local, one real place; linear algebra and analysis on the space of real symmetric $r \times r$ matrices
(no global input).

**Setting.** $Z \in \mathbb H_r$ (`WeilRep.Genus.siegelH r`: $Z^{\mathsf T} = Z$, $\operatorname{Im}Z$ positive definite),
$\mathrm{UIdx}\ r = \{(i,j) : i \le j\}$ the index set of the upper triangle (0-based), and
`symU b` the real symmetric matrix with upper coordinates $b \in \mathbb R^{\mathrm{UIdx}\,r}$. The space
$\mathbb R^{\mathrm{UIdx}\,r}$ has dimension $r(r+1)/2$ and Lebesgue measure.

**Results.**
* `norm_det_sq_ge`: for a real symmetric $C$, $|\det(C + iI)|^2 \ge 1 + \sum_{i,j}C_{ij}^2$
  (since $|\det(C + iI)|^2 = \prod_j(1 + \mu_j^2)$ for the eigenvalues $\mu_j$ of $C$);
* **`exists_lower_bound_det`**: for a real positive definite $Y$ there is $c > 0$ with
  $$c\,(1 + \|b\|) \le |\det(\mathrm{symU}(b) + iY)| \quad \text{for all } b \in \mathbb R^{\mathrm{UIdx}\,r},$$
  where $\|b\|$ is the supremum norm (write $Y = P^{\mathsf T}P$, so $\mathrm{symU}(b) + iY = P^{\mathsf T}(C + iI)P$ with
  $C = P^{-\mathsf T}\,\mathrm{symU}(b)\,P^{-1}$, which is an injective linear function of $b$);
* `continuous_det_add_symU`: $b \mapsto \det(Z + \mathrm{symU}(b))$ is continuous;
* **`integrable_inv_norm_det_pow`**: for $k > r(r+1)/2$ and $Z \in \mathbb H_r$, the function
  $b \mapsto |\det(Z + \mathrm{symU}(b))|^{-k}$ is Lebesgue integrable on $\mathbb R^{\mathrm{UIdx}\,r}$.

Sources: Siegel, *Symplectic geometry*, Amer. J. Math. 65 (1943), §§ on the Siegel half space [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.SiegelWeil.Forms.ArchGaussR
import QuadFormsKB.Tamagawa.ArchVolume
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarDet

open MeasureTheory Matrix Complex
open scoped Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms.ArchR

open WeilRep.Genus QuadFormsKB.Tamagawa.ArchVol

/-! ### The symmetric matrix with given upper coordinates -/

/-- `symU` is additive in the upper coordinates. -/
lemma symU_add {r : ℕ} (a b : UIdx r → ℝ) : symU (a + b) = symU a + symU b := by
  ext i j; simp only [symU, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]; split_ifs <;> rfl

/-- `symU` commutes with real scalar multiplication. -/
lemma symU_smul {r : ℕ} (c : ℝ) (a : UIdx r → ℝ) : symU (c • a) = c • symU a := by
  ext i j; simp only [symU, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply]; split_ifs <;> rfl

/-- The upper entry $(i,j)$, $i \le j$, of `symU a` is the coordinate $a_{(i,j)}$. -/
lemma symU_apply_upper {r : ℕ} (a : UIdx r → ℝ) (p : UIdx r) : symU a p.1.1 p.1.2 = a p := by
  simp [symU, p.2]

/-- Every real symmetric matrix is `symU` of its upper coordinates. -/
lemma symU_upper {r : ℕ} {A : Matrix (Fin r) (Fin r) ℝ} (hA : Aᵀ = A) :
    symU (fun p : UIdx r => A p.1.1 p.1.2) = A := by
  ext i j
  simp only [symU, Matrix.of_apply]
  split_ifs with h
  · rfl
  · have := congrFun (congrFun hA i) j
    simpa using this

/-- `symU a` is symmetric. -/
lemma symU_transpose {r : ℕ} (a : UIdx r → ℝ) : (symU a)ᵀ = symU a := by
  ext i j
  simp only [symU, Matrix.transpose_apply, Matrix.of_apply]
  by_cases h : i ≤ j
  · by_cases h' : j ≤ i
    · have : i = j := le_antisymm h h'
      subst this; rfl
    · simp [h, h']
  · have h' : j ≤ i := le_of_not_ge h
    simp [h, h']

/-- Each entry of `symU a` is a continuous function of `a`. -/
lemma continuous_symU_apply {r : ℕ} (i j : Fin r) : Continuous fun a : UIdx r → ℝ => symU a i j := by
  simp only [symU, Matrix.of_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_apply _

/-! ### The determinant of $C + iI$ -/

/-- For nonnegative reals, $1 + \sum a_j \le \prod(1 + a_j)$. -/
lemma one_add_sum_le_prod {r : ℕ} (a : Fin r → ℝ) (ha : ∀ j, 0 ≤ a j) :
    1 + ∑ j, a j ≤ ∏ j, (1 + a j) := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
    have h1 := ih (fun j => a j.succ) (fun j => ha _)
    have h0 := ha 0
    have hs : 0 ≤ ∑ j : Fin n, a j.succ := Finset.sum_nonneg fun j _ => ha _
    nlinarith

/-- A real symmetric matrix $C$ has $\sum_{i,j}C_{ij}^2 = \sum_j\mu_j^2$ for its eigenvalues, and
$|\det(C + iI)|^2 = \prod_j(1 + \mu_j^2)$; hence $|\det(C + iI)|^2 \ge 1 + \sum_{i,j}C_{ij}^2$. -/
lemma norm_det_sq_ge {r : ℕ} {C : Matrix (Fin r) (Fin r) ℝ} (hC : Cᵀ = C) :
    1 + ∑ i, ∑ j, C i j ^ 2 ≤ ‖(cR C + I • (1 : Matrix (Fin r) (Fin r) ℂ)).det‖ ^ 2 := by
  have hH : C.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hC
  obtain ⟨U, hUU, hUU', hCeq⟩ := exists_orth_diag hH
  set μ := hH.eigenvalues
  have hdiag : cR C + I • (1 : Matrix (Fin r) (Fin r) ℂ) =
      cR U * diagonal (fun j => (μ j : ℂ) + I) * cR Uᵀ := by
    have h1 : diagonal (fun j => (μ j : ℂ) + I) = cR (diagonal μ) + I • 1 := by
      ext i j
      by_cases h : i = j
      · subst h; simp [Matrix.one_apply]
      · simp [h]
    have h2 : cR U * cR Uᵀ = 1 := by rw [← cR_mul, hUU']; ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [h1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, h2,
      ← cR_mul, ← cR_mul, ← hCeq]
  have h3 : cR Uᵀ * cR U = 1 := by rw [← cR_mul, hUU]; ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hdet : (cR C + I • (1 : Matrix (Fin r) (Fin r) ℂ)).det = ∏ j, ((μ j : ℂ) + I) := by
    rw [hdiag, Matrix.mul_assoc, Matrix.det_mul_comm, Matrix.mul_assoc, h3, Matrix.mul_one, det_diagonal]
  have hnorm : ‖(cR C + I • (1 : Matrix (Fin r) (Fin r) ℂ)).det‖ ^ 2 = ∏ j, (1 + μ j ^ 2) := by
    rw [hdet, ← Complex.normSq_eq_norm_sq, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [Complex.normSq_apply]; ring
  have htr : ∑ i, ∑ j, C i j ^ 2 = ∑ j, μ j ^ 2 := by
    have h4 : (C * C).trace = ∑ j, μ j ^ 2 := by
      have : C * C = U * (diagonal μ * diagonal μ) * Uᵀ := by
        conv_lhs => rw [hCeq]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Uᵀ U, hUU, Matrix.one_mul]
      rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul, diagonal_mul_diagonal]
      simp [Matrix.trace, sq]
    rw [← h4]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : C j i = C i j := by simpa using congrFun (congrFun hC i) j
    rw [this]; ring
  rw [hnorm, htr]
  exact one_add_sum_le_prod (fun j => μ j ^ 2) (fun j => sq_nonneg _)

/-! ### The lower bound -/

/-- The determinant of a complex image of a real matrix is the image of its determinant. -/
lemma det_cR {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) : (cR A).det = (A.det : ℂ) := by
  rw [show cR A = A.map Complex.ofRealHom from rfl, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl

/-- **The key lower bound.** For a real positive definite $Y$ there is $c > 0$ with
$c\,(1 + \|b\|) \le |\det(\mathrm{symU}(b) + iY)|$ for every $b \in \mathbb R^{\mathrm{UIdx}\,r}$
($\|b\|$ the supremum norm). -/
theorem exists_lower_bound_det {r : ℕ} {Y : Matrix (Fin r) (Fin r) ℝ} (hY : Y.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ b : UIdx r → ℝ,
      c * (1 + ‖b‖) ≤ ‖(cR (symU b) + I • cR Y).det‖ := by
  obtain ⟨P, hYP, hP⟩ := exists_eq_transpose_mul hY
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  set Q : Matrix (Fin r) (Fin r) ℝ := P⁻¹ with hQ
  have hQP : Q * P = 1 := Matrix.nonsing_inv_mul _ hu
  have hQP' : Pᵀ * Qᵀ = 1 := by rw [← transpose_mul, hQP, transpose_one]
  have hSG : ∀ S : Matrix (Fin r) (Fin r) ℝ, S = Pᵀ * (Qᵀ * S * Q) * P := by
    intro S
    calc S = (Pᵀ * Qᵀ) * S * (Q * P) := by rw [hQP', hQP, Matrix.one_mul, Matrix.mul_one]
      _ = Pᵀ * (Qᵀ * S * Q) * P := by simp only [Matrix.mul_assoc]
  -- the linear map b ↦ Qᵀ (symU b) Q
  let L : (UIdx r → ℝ) →ₗ[ℝ] (Fin r → Fin r → ℝ) :=
    { toFun := fun b => fun i j => (Qᵀ * symU b * Q) i j
      map_add' := fun a b => by
        ext i j; simp [symU_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c a => by
        ext i j; simp [symU_smul] }
  have hLb : ∀ b i j, L b i j = (Qᵀ * symU b * Q) i j := fun _ _ _ => rfl
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro b hb
    have h0 : Qᵀ * symU b * Q = 0 := by
      ext i j; have := congrFun (congrFun hb i) j; simpa [hLb] using this
    have hS := hSG (symU b)
    rw [h0, Matrix.mul_zero, Matrix.zero_mul] at hS
    funext p
    have := congrFun (congrFun hS p.1.1) p.1.2
    rw [symU_apply_upper] at this
    simpa using this
  obtain ⟨K, hK0, hK⟩ := L.exists_antilipschitzWith hker
  set K' : ℝ := max (K : ℝ) 1 with hK'
  have hK'1 : 1 ≤ K' := le_max_right _ _
  have hK'0 : 0 < K' := by linarith
  have hbL : ∀ b : UIdx r → ℝ, ‖b‖ ≤ K' * ‖L b‖ := by
    intro b
    have := hK.le_mul_dist b 0
    simp only [dist_zero_right, map_zero] at this
    calc ‖b‖ ≤ K * ‖L b‖ := by simpa using this
      _ ≤ K' * ‖L b‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hLs : ∀ b : UIdx r → ℝ, ‖L b‖ ^ 2 ≤ ∑ i, ∑ j, (Qᵀ * symU b * Q) i j ^ 2 := by
    intro b
    set s := ∑ i, ∑ j, (Qᵀ * symU b * Q) i j ^ 2 with hs
    have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have : ‖L b‖ ≤ Real.sqrt s := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
      rw [Real.norm_eq_abs, hLb]
      apply Real.abs_le_sqrt
      calc (Qᵀ * symU b * Q) i j ^ 2 ≤ ∑ j', (Qᵀ * symU b * Q) i j' ^ 2 :=
            Finset.single_le_sum (f := fun j' => (Qᵀ * symU b * Q) i j' ^ 2)
              (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
        _ ≤ s := Finset.single_le_sum (f := fun i' => ∑ j', (Qᵀ * symU b * Q) i' j' ^ 2)
              (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    calc ‖L b‖ ^ 2 ≤ Real.sqrt s ^ 2 := by gcongr
      _ = s := Real.sq_sqrt hs0
  set d : ℝ := |P.det| ^ 2 with hd
  have hd0 : 0 < d := by have := abs_pos.2 hP; positivity
  refine ⟨d / (2 * K'), by positivity, fun b => ?_⟩
  set C : Matrix (Fin r) (Fin r) ℝ := Qᵀ * symU b * Q with hCdef
  have hCt : Cᵀ = C := by
    simp only [hCdef, transpose_mul, transpose_transpose, symU_transpose, Matrix.mul_assoc]
  have hS : symU b = Pᵀ * C * P := by
    exact hSG _
  have hfac : cR (symU b) + I • cR Y = cR Pᵀ * (cR C + I • 1) * cR P := by
    rw [hYP, hS]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, cR_mul]
  have hdet : ‖(cR (symU b) + I • cR Y).det‖ = d * ‖(cR C + I • (1 : Matrix (Fin r) (Fin r) ℂ)).det‖ := by
    rw [hfac, det_mul, det_mul, det_cR, det_cR, det_transpose, norm_mul, norm_mul, hd]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    ring
  rw [hdet]
  have hN := norm_det_sq_ge hCt
  set N := ‖(cR C + I • (1 : Matrix (Fin r) (Fin r) ℂ)).det‖ with hNdef
  have hN0 : 0 ≤ N := norm_nonneg _
  set u := ‖b‖ with hu'
  have hu0 : 0 ≤ u := norm_nonneg _
  have hus : u ^ 2 ≤ K' ^ 2 * (N ^ 2 - 1) := by
    have h1 : u ≤ K' * ‖L b‖ := hbL b
    have h2 : u ^ 2 ≤ (K' * ‖L b‖) ^ 2 := by gcongr
    have h3 : ‖L b‖ ^ 2 ≤ N ^ 2 - 1 := by linarith [hLs b]
    calc u ^ 2 ≤ (K' * ‖L b‖) ^ 2 := h2
      _ = K' ^ 2 * ‖L b‖ ^ 2 := by ring
      _ ≤ K' ^ 2 * (N ^ 2 - 1) := by gcongr
  have ht : (1 + u) / (2 * K') ≤ N := by
    have hsq : ((1 + u) / (2 * K')) ^ 2 ≤ N ^ 2 := by
      rw [div_pow, div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg (1 - u), sq_nonneg K', mul_nonneg (sq_nonneg K') (sq_nonneg (1 - u)),
        sq_nonneg (K' - 1), mul_nonneg hK'0.le hu0]
    exact (sq_le_sq₀ (by positivity) hN0).1 hsq
  calc d / (2 * K') * (1 + u) = d * ((1 + u) / (2 * K')) := by ring
    _ ≤ d * N := by gcongr

/-! ### Continuity and integrability -/

/-- The determinant $b \mapsto \det(Z + \mathrm{symU}(b))$ is continuous in the upper coordinates $b$. -/
lemma continuous_det_add_symU {r : ℕ} (Z : Matrix (Fin r) (Fin r) ℂ) :
    Continuous fun b : UIdx r → ℝ => (Z + cR (symU b)).det := by
  refine Continuous.matrix_det ?_
  refine continuous_matrix fun i j => ?_
  simp only [Matrix.add_apply, Matrix.map_apply]
  exact continuous_const.add (Complex.continuous_ofReal.comp (continuous_symU_apply i j))

/-- The function $b \mapsto \|\det(Z + \mathrm{symU}(b))\|^{-1}$ raised to the power $k$ is measurable. -/
lemma measurable_inv_norm_det_pow {r : ℕ} (k : ℕ) (Z : Matrix (Fin r) (Fin r) ℂ) :
    Measurable fun b : UIdx r → ℝ => ‖(Z + cR (symU b)).det‖⁻¹ ^ k :=
  ((continuous_det_add_symU Z).norm.measurable.inv).pow_const k

/-- **Integrability of $|\det(Z + X)|^{-k}$ over real symmetric $X$.** For $Z \in \mathbb H_r$ and
$k > r(r+1)/2$ (the dimension of the space of symmetric matrices), the function
$b \mapsto \|\det(Z + \mathrm{symU}(b))\|^{-k}$ is Lebesgue integrable on $\mathbb R^{\mathrm{UIdx}\,r}$.
It is bounded by $A^k(1 + \|b - b_0\|)^{-k}$ (`exists_lower_bound_det`, with $b_0$ the upper coordinates of
$\operatorname{Re}Z$), which is integrable by Mathlib's `integrable_one_add_norm`. -/
@[kb "siegel1943" "the integral of |det(Y + iX)|^{-k} over symmetric X [unverified]"]
theorem integrable_inv_norm_det_pow {r k : ℕ} (hk : r * (r + 1) / 2 < k) {Z : Matrix (Fin r) (Fin r) ℂ}
    (hZ : Z ∈ WeilRep.Genus.siegelH r) :
    MeasureTheory.Integrable (fun b : UIdx r → ℝ => ‖(Z + cR (symU b)).det‖⁻¹ ^ k) := by
  obtain ⟨hsym, hY⟩ := hZ
  set Y := Z.map Complex.im with hYdef
  set X0 := Z.map Complex.re with hX0def
  have hX0 : X0ᵀ = X0 := by rw [hX0def, ← transpose_map, hsym]
  set x0 : UIdx r → ℝ := fun p => X0 p.1.1 p.1.2 with hx0
  have hZeq : Z = cR (symU x0) + I • cR Y := by
    rw [hx0, symU_upper hX0]
    ext i j
    apply Complex.ext <;> simp [X0, Y]
  obtain ⟨c, hc, hbound⟩ := exists_lower_bound_det hY
  have hpt : ∀ b : UIdx r → ℝ, c * (1 + ‖b + x0‖) ≤ ‖(Z + cR (symU b)).det‖ := by
    intro b
    have : Z + cR (symU b) = cR (symU (b + x0)) + I • cR Y := by
      rw [hZeq, symU_add]
      ext i j
      simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply]
      push_cast; ring
    rw [this]; exact hbound _
  have hdim : (Module.finrank ℝ (UIdx r → ℝ) : ℝ) < (k : ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card, QuadFormsKB.Tamagawa.Measure.Weil.card_UIdx]
    exact_mod_cast hk
  have hint : Integrable (fun b : UIdx r → ℝ => (1 + ‖b + x0‖) ^ (-(k : ℝ))) := by
    have := integrable_one_add_norm (μ := (volume : Measure (UIdx r → ℝ))) hdim
    exact this.comp_add_right x0
  refine Integrable.mono' (hint.const_mul ((c⁻¹) ^ k)) (measurable_inv_norm_det_pow k Z).aestronglyMeasurable
    (Filter.Eventually.of_forall fun b => ?_)
  have hpos : 0 < c * (1 + ‖b + x0‖) := by positivity
  have h1 : ‖(Z + cR (symU b)).det‖⁻¹ ≤ (c * (1 + ‖b + x0‖))⁻¹ := inv_anti₀ hpos (hpt b)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖(Z + cR (symU b)).det‖⁻¹ ^ k ≤ ((c * (1 + ‖b + x0‖))⁻¹) ^ k := by gcongr
    _ = c⁻¹ ^ k * (1 + ‖b + x0‖) ^ (-(k : ℝ)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast, mul_inv, mul_pow, inv_pow, inv_pow]

end QuadFormsKB.SiegelWeil.Forms.ArchR
