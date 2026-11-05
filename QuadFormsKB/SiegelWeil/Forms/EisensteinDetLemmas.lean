/-
# Two lemmas on the Eisenstein denominator $\det(CZ+D)$
**Layer:** real and complex linear algebra (no arithmetic input).

**Setting.** A real *symmetric coprime pair* $(C, D)$ of size $r$: $C D^{\mathsf T} = D C^{\mathsf T}$ (and, for the
monotonicity statement, no nonzero real $u$ with $uC = 0 = uD$).  $Z$ lies in the Siegel upper half space
$\mathbb H_r$ (symmetric with positive definite imaginary part), and $M = CZ + D$ is the complex matrix whose
determinant is the denominator of the Siegel Eisenstein series.

**Results.**
* `det_add_vecMulVec`: the matrix determinant lemma $\det(M + a b^{\mathsf T}) = \det M\,(1 + b^{\mathsf T}M^{-1}a)$;
* **`det_add_sym_ker`** (translation invariance): if $\det M \ne 0$ and $Cu = 0$, then for every real $v$
  $\det\bigl(C(Z + uv^{\mathsf T} + vu^{\mathsf T}) + D\bigr) = \det(CZ + D)$ (because $M^{-1}C$ is symmetric);
* `mem_siegelH_add_rankOne`: $Z + (t i)\, vv^{\mathsf T} \in \mathbb H_r$ for real $t \ge 0$
  (`mem_siegelH_add_rankOne_complex`: for complex $s$ with $\operatorname{Re}s \ge 0$);
* **`monotoneOn_norm_det_rankOne`**: $t \mapsto \lVert\det(C(Z + t i\, vv^{\mathsf T}) + D)\rVert$ is monotone on
  $[0, \infty)$ (the determinant is affine in $t$ and its root has real part $\le 0$ by `PhiArch.det_ne_zero`).

Source: Klingen, *Introductory lectures on Siegel modular forms* (1990), §5 [unverified];
Freitag, *Siegelsche Modulfunktionen* (1983), Ch. I [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.PhiArch

open Matrix Complex
open QuadFormsKB.WeilRep.Genus

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

/-- Matrix determinant lemma for a rank-one update (invertible case):
$\det(M + a b^{\mathsf T}) = \det M\,(1 + b^{\mathsf T}M^{-1}a)$. -/
theorem det_add_vecMulVec {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (hM : M.det ≠ 0)
    (a b : Fin r → ℂ) :
    (M + Matrix.vecMulVec a b).det = M.det * (1 + b ⬝ᵥ (M⁻¹ *ᵥ a)) := by
  have hU : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  rw [Matrix.vecMulVec_eq Unit, Matrix.det_add_mul _ _ hU]
  congr 1
  rw [Matrix.det_unique]
  simp [Matrix.mul_apply, dotProduct, Matrix.mulVec]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- $M^{-1}C$ is symmetric when $CM^{\mathsf T} = MC^{\mathsf T}$ and $M$ is invertible. -/
private lemma inv_mul_symm {r : ℕ} (M C : Matrix (Fin r) (Fin r) ℂ) (hM : M.det ≠ 0)
    (h : C * Mᵀ = M * Cᵀ) : (M⁻¹ * C)ᵀ = M⁻¹ * C := by
  have hU : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have hMt : IsUnit Mᵀ.det := by rwa [Matrix.det_transpose]
  have h1 : M⁻¹ * C * Mᵀ = Cᵀ := by
    rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]
  have h2 : M⁻¹ * C = Cᵀ * (Mᵀ)⁻¹ := by
    rw [← h1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hMt, Matrix.mul_one]
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, h2]

/-- The symmetry $C M^{\mathsf T} = M C^{\mathsf T}$ for $M = CZ + D$, $Z$ symmetric. -/
private lemma sym_M {r : ℕ} (C D : Matrix (Fin r) (Fin r) ℝ) (hCD : C * Dᵀ = D * Cᵀ)
    {Z : Matrix (Fin r) (Fin r) ℂ} (hZs : Zᵀ = Z) :
    C.map (↑) * (C.map (↑) * Z + D.map (↑) : Matrix (Fin r) (Fin r) ℂ)ᵀ =
      (C.map (↑) * Z + D.map (↑) : Matrix (Fin r) (Fin r) ℂ) * (C.map (↑))ᵀ := by
  have hD : (C.map (↑) : Matrix (Fin r) (Fin r) ℂ) * (D.map (↑))ᵀ
      = (D.map (↑)) * (C.map (↑))ᵀ := by
    have h := congrArg (RingHom.mapMatrix Complex.ofRealHom) hCD
    simp [RingHom.mapMatrix_apply, Matrix.transpose_map] at h
    exact h
  rw [Matrix.transpose_add, Matrix.transpose_mul, hZs, Matrix.mul_add, Matrix.add_mul, hD,
    Matrix.mul_assoc]

/-- **Translation invariance** of $\det(CZ+D)$ along $uv^{\mathsf T} + vu^{\mathsf T}$ with $Cu = 0$. -/
theorem det_add_sym_ker {r : ℕ} (C D : Matrix (Fin r) (Fin r) ℝ) (hCD : C * Dᵀ = D * Cᵀ)
    {Z : Matrix (Fin r) (Fin r) ℂ} (hZs : Zᵀ = Z)
    (hdet : (C.map (↑) * Z + D.map (↑) : Matrix (Fin r) (Fin r) ℂ).det ≠ 0)
    (u v : Fin r → ℝ) (hu : C *ᵥ u = 0) :
    (C.map (↑) * (Z + (Matrix.vecMulVec u v + Matrix.vecMulVec v u).map (↑)) + D.map (↑) :
        Matrix (Fin r) (Fin r) ℂ).det =
      (C.map (↑) * Z + D.map (↑) : Matrix (Fin r) (Fin r) ℂ).det := by
  set M : Matrix (Fin r) (Fin r) ℂ := C.map (↑) * Z + D.map (↑) with hMdef
  set C' : Matrix (Fin r) (Fin r) ℂ := C.map (↑) with hC'
  set u' : Fin r → ℂ := fun i => (u i : ℂ) with hu'
  set v' : Fin r → ℂ := fun i => (v i : ℂ) with hv'
  have hCu : C' *ᵥ u' = 0 := by
    funext i
    have := congrFun hu i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this ⊢
    simp only [hC', hu', Matrix.map_apply]
    exact_mod_cast this
  have hcast : ((Matrix.vecMulVec u v + Matrix.vecMulVec v u).map (↑) :
      Matrix (Fin r) (Fin r) ℂ) = Matrix.vecMulVec u' v' + Matrix.vecMulVec v' u' := by
    ext i j; simp [Matrix.vecMulVec_apply, hu', hv']
  have hsym : C' * Mᵀ = M * C'ᵀ := sym_M C D hCD hZs
  have hN := inv_mul_symm M C' hdet hsym
  have key : C' * (Z + (Matrix.vecMulVec u' v' + Matrix.vecMulVec v' u')) + D.map (↑) =
      M + Matrix.vecMulVec (C' *ᵥ v') u' := by
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, hCu, hMdef,
      Matrix.vecMulVec_eq_zero.mpr (Or.inl rfl)]
    abel
  rw [hcast, key, det_add_vecMulVec M hdet]
  have h0 : u' ⬝ᵥ (M⁻¹ *ᵥ (C' *ᵥ v')) = 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    have : u' ᵥ* (M⁻¹ * C') = 0 := by
      calc u' ᵥ* (M⁻¹ * C') = u' ᵥ* ((M⁻¹ * C')ᵀ)ᵀ := by rw [Matrix.transpose_transpose]
        _ = (M⁻¹ * C')ᵀ *ᵥ u' := (Matrix.mulVec_transpose _ _).symm
        _ = 0 := by rw [hN, ← Matrix.mulVec_mulVec, hCu, Matrix.mulVec_zero]
    rw [this]; simp
  rw [h0]; simp

/-- $Z + (s i)\,vv^{\mathsf T} \in \mathbb H_r$ for $Z \in \mathbb H_r$ and $\operatorname{Re}s \ge 0$. -/
theorem mem_siegelH_add_rankOne_complex {r : ℕ} {Z : Matrix (Fin r) (Fin r) ℂ}
    (hZ : Z ∈ siegelH r) (v : Fin r → ℝ) {s : ℂ} (hs : 0 ≤ s.re) :
    Z + (s * Complex.I) • (Matrix.vecMulVec v v).map (↑) ∈ siegelH r := by
  refine ⟨?_, ?_⟩
  · ext i j
    have h := congrFun₂ hZ.1 i j
    simp only [Matrix.transpose_apply] at h
    simp [Matrix.vecMulVec_apply, h, mul_comm]
  · have himg : ((Z + (s * Complex.I) • (Matrix.vecMulVec v v).map (↑) :
        Matrix (Fin r) (Fin r) ℂ)).map Complex.im
        = Z.map Complex.im + s.re • Matrix.vecMulVec v v := by
      ext i j
      simp [Matrix.vecMulVec_apply]
    rw [himg]
    refine hZ.2.add_posSemidef (Matrix.PosSemidef.smul ?_ hs)
    simpa using Matrix.posSemidef_vecMulVec_self_star v

/-- $Z + (t i)\,vv^{\mathsf T} \in \mathbb H_r$ for $Z \in \mathbb H_r$ and real $t \ge 0$. -/
theorem mem_siegelH_add_rankOne {r : ℕ} {Z : Matrix (Fin r) (Fin r) ℂ}
    (hZ : Z ∈ siegelH r) (v : Fin r → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Z + ((t : ℂ) * Complex.I) • (Matrix.vecMulVec v v).map (↑) ∈ siegelH r :=
  mem_siegelH_add_rankOne_complex hZ v (by simpa using ht)

/-- **Monotonicity** of $t \mapsto \lVert\det(C(Z + t i\,vv^{\mathsf T}) + D)\rVert$ on $[0,\infty)$. -/
theorem monotoneOn_norm_det_rankOne {r : ℕ} {C D : Matrix (Fin r) (Fin r) ℝ}
    (hsym : C * Dᵀ = D * Cᵀ)
    (hrank : ∀ u : Fin r → ℝ, u ᵥ* C = 0 → u ᵥ* D = 0 → u = 0)
    {Z : Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ QuadFormsKB.WeilRep.Genus.siegelH r) (v : Fin r → ℝ) :
    MonotoneOn (fun t : ℝ => ‖(C.map (↑) * (Z + ((t : ℂ) * Complex.I) • (Matrix.vecMulVec v v).map (↑)) + D.map (↑) :
        Matrix (Fin r) (Fin r) ℂ).det‖) (Set.Ici 0) := by
  set M : Matrix (Fin r) (Fin r) ℂ := C.map (↑) * Z + D.map (↑) with hMdef
  have hM : M.det ≠ 0 := PhiArch.det_ne_zero hsym hrank hZ
  set C' : Matrix (Fin r) (Fin r) ℂ := C.map (↑) with hC'
  set v' : Fin r → ℂ := fun i => (v i : ℂ) with hv'
  have hvv : ((Matrix.vecMulVec v v).map (↑) : Matrix (Fin r) (Fin r) ℂ) = Matrix.vecMulVec v' v' := by
    ext i j; simp [Matrix.vecMulVec_apply, hv']
  set β : ℂ := M.det with hβ
  set α : ℂ := M.det * (Complex.I * (v' ⬝ᵥ (M⁻¹ *ᵥ (C' *ᵥ v')))) with hα
  have hform : ∀ s : ℂ, (C' * (Z + (s * Complex.I) • (Matrix.vecMulVec v v).map (↑)) + D.map (↑) :
      Matrix (Fin r) (Fin r) ℂ).det = β + s * α := by
    intro s
    have : C' * (Z + (s * Complex.I) • (Matrix.vecMulVec v v).map (↑)) + D.map (↑) =
        M + Matrix.vecMulVec ((s * Complex.I) • (C' *ᵥ v')) v' := by
      rw [hvv, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_vecMulVec, ← Matrix.smul_vecMulVec,
        hMdef]
      abel
    rw [this, det_add_vecMulVec M hM, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
    simp only [hα, hβ]; ring
  have hne : ∀ s : ℂ, 0 ≤ s.re → β + s * α ≠ 0 := by
    intro s hs
    rw [← hform s]
    exact PhiArch.det_ne_zero hsym hrank (mem_siegelH_add_rankOne_complex hZ v hs)
  intro t₁ ht₁ t₂ _ hle
  have ht1 : (0 : ℝ) ≤ t₁ := ht₁
  beta_reduce
  rw [hform, hform]
  by_cases hα0 : α = 0
  · simp [hα0]
  · set s' : ℂ := -β / α with hs'
    have hre : s'.re ≤ 0 := by
      by_contra hpos
      push Not at hpos
      apply hne s' hpos.le
      have : β + s' * α = 0 := by simp only [hs']; field_simp; ring
      exact this
    have hnorm : ∀ t : ℝ, ‖β + (t : ℂ) * α‖ = ‖α‖ * ‖(t : ℂ) - s'‖ := by
      intro t
      rw [← norm_mul]
      congr 1
      simp only [hs']; field_simp; ring
    rw [hnorm, hnorm]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im]
    nlinarith

end QuadFormsKB.SiegelWeil.Forms
