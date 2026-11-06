/-
# Hua's integral: $|\det(Z + X)|^{-\sigma}$ is integrable over real symmetric $X$ for $\sigma > r$
**Layer:** local, one real place; analysis on the space $\mathrm{Sym}_r(\mathbb R)$ of real symmetric $r \times r$ matrices
(no global input).

**Setting.** $\mathrm{UIdx}\ r = \{(i,j) : i \le j\}$ (0-based) and `symU b` the real symmetric matrix with upper
coordinates $b \in \mathbb R^{\mathrm{UIdx}\,r}$ (Lebesgue measure on $\mathbb R^{\mathrm{UIdx}\,r}$). For real $\sigma$,
$$\mathrm{hua}_r(\sigma) = \int_{\mathbb R^{\mathrm{UIdx}\,r}}|\det(\mathrm{symU}(b) + iI)|^{-\sigma}\,db \in [0, \infty].$$

**Results.**
* `det_hH_asm` (Schur complement in the first row): for $B = \begin{pmatrix}a & u^{\mathsf T}\\ u & B'\end{pmatrix}$,
  $\det(B + iI) = \det(B' + iI)\,(a + i - u^{\mathsf T}(B' + iI)^{-1}u)$;
* `exists_im_quad`: there is a real $A$ with $|\det A| = |\det(B' + iI)|$ and
  $\operatorname{Im}\big((Aw)^{\mathsf T}(B' + iI)^{-1}(Aw)\big) = -w^{\mathsf T}w$ (from $B' = U\operatorname{diag}(\mu)U^{\mathsf T}$,
  $A = U\operatorname{diag}(\sqrt{1 + \mu_j^2})$);
* **`hua_succ`** (Hua's recursion): $\mathrm{hua}_{r+1}(\sigma) = c_1(\sigma)\,c_2(r, \sigma)\,\mathrm{hua}_r(\sigma - 1)$, with
  $c_1(\sigma) = \int_{\mathbb R}(1 + t^2)^{-\sigma/2}dt$ and $c_2(r, \sigma) = \int_{\mathbb R^r}(1 + w^{\mathsf T}w)^{1-\sigma}dw$
  (integrate $a$, then $u$);
* **`hua_lt_top`**: $\mathrm{hua}_r(\sigma) < \infty$ for $\sigma > r$ (Hua's integral; this range is sharp);
* **`integrable_inv_norm_det_rpow`**: for $Z \in \mathbb H_r$ and real $\sigma > r$, $b \mapsto |\det(Z + \mathrm{symU}(b))|^{-\sigma}$
  is integrable (Siegel's range, sharpening `integrable_inv_norm_det_pow`, which needs $\sigma > r(r+1)/2$);
  `integrable_inv_norm_det_pow_sharp` is the integer-exponent form.

Sources: Hua, *Harmonic analysis of functions of several complex variables in the classical domains*, AMS (1963),
§2.1 [unverified]; Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. of Math. 36 (1935) (the range
$N > 2r$ of the archimedean factor) [unverified]. The proof by the Schur complement in the first row is the standard
inductive one (the same reduction as Siegel's computation of the Gaussian of degree $r$).
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.SiegelWeil.Forms.ArchHuaAlg
import QuadFormsKB.SiegelWeil.Forms.ArchHuaInt

open MeasureTheory Matrix Complex
open scoped Real ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms.ArchR

open WeilRep.Genus QuadFormsKB.Tamagawa.ArchVol

/-! ### Hua's recursion -/

/-- **Hua's integral** $\mathrm{hua}_r(\sigma) = \int|\det(\mathrm{symU}(b) + iI)|^{-\sigma}db$. -/
def hua (r : ℕ) (σ : ℝ) : ℝ≥0∞ := ∫⁻ b : UIdx r → ℝ, ENNReal.ofReal (‖(hH b).det‖ ^ (-σ))

lemma measurable_huaF {r : ℕ} (σ : ℝ) :
    Measurable fun b : UIdx r → ℝ => ENNReal.ofReal (‖(hH b).det‖ ^ (-σ)) := by
  refine ENNReal.measurable_ofReal.comp ?_
  exact (continuous_det_hH.norm.rpow_const fun b => Or.inl (by
    have := one_le_norm_det_hH b; linarith)).measurable

/-- The inner integral over the first row: for fixed $B'$,
$\int_{\mathbb R^r}\int_{\mathbb R}|\det(B + iI)|^{-\sigma}\,da\,du = c_1(\sigma)c_2(r,\sigma)|\det(B' + iI)|^{1-\sigma}$. -/
theorem lintegral_row {r : ℕ} {σ : ℝ} (v : UIdx r → ℝ) :
    ∫⁻ u : Fin r → ℝ, ∫⁻ a : ℝ, ENNReal.ofReal (‖(hH (asm a u v)).det‖ ^ (-σ)) =
      hc1 σ * hc2 r σ * ENNReal.ofReal (‖(hH v).det‖ ^ (-(σ - 1))) := by
  set D := ‖(hH v).det‖ with hD
  have hD1 : 1 ≤ D := one_le_norm_det_hH v
  have hD0 : 0 < D := by linarith
  set X : (Fin r → ℝ) → ℂ := fun u => cV u ⬝ᵥ ((hH v)⁻¹ *ᵥ cV u) with hX
  obtain ⟨A, hAdet, hA⟩ := exists_im_quad v
  have hA0 : A.det ≠ 0 := by
    intro h; rw [h, abs_zero] at hAdet; linarith
  have hXcont : Continuous X := by
    simp only [hX, dotProduct, mulVec]
    fun_prop
  -- every `u` is `A w`, so the imaginary part of `X u` is `≤ 0`
  have him : ∀ u, (X u).im ≤ 0 := by
    intro u
    have hu : A *ᵥ (A⁻¹ *ᵥ u) = u := by
      rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA0), one_mulVec]
    have := hA (A⁻¹ *ᵥ u)
    rw [hu] at this
    simp only [hX, this, neg_nonpos]
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  set y : (Fin r → ℝ) → ℝ := fun u => 1 - (X u).im with hy
  have hy1 : ∀ u, 1 ≤ y u := fun u => by simp only [hy]; linarith [him u]
  -- the determinant through the Schur complement
  have hpt : ∀ u a, ‖(hH (asm a u v)).det‖ ^ (-σ) =
      D ^ (-σ) * ‖((a - (X u).re : ℝ) : ℂ) + I * (y u : ℝ)‖ ^ (-σ) := by
    intro u a
    rw [det_hH_asm, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    congr 2
    change ‖(a : ℂ) + I - X u‖ = _
    congr 1
    apply Complex.ext <;> simp [hy]
  have hinner : ∀ u, ∫⁻ a : ℝ, ENNReal.ofReal (‖(hH (asm a u v)).det‖ ^ (-σ)) =
      ENNReal.ofReal (D ^ (-σ)) * (ENNReal.ofReal (y u ^ (1 - σ)) * hc1 σ) := by
    intro u
    simp_rw [hpt u, ENNReal.ofReal_mul (Real.rpow_nonneg hD0.le _)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_norm_add_I_rpow (by linarith [hy1 u])]
  simp_rw [hinner]
  have hmeas : Measurable fun u => ENNReal.ofReal (y u ^ (1 - σ)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact ((continuous_const.sub (Complex.continuous_im.comp hXcont)).measurable).pow_const _
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_mul_const _ hmeas,
    lintegral_eq_det_mul_comp hA0 hmeas]
  have hyA : ∀ w, y (A *ᵥ w) = 1 + w ⬝ᵥ w := fun w => by
    simp only [hy]; rw [show X (A *ᵥ w) = cV (A *ᵥ w) ⬝ᵥ ((hH v)⁻¹ *ᵥ cV (A *ᵥ w)) from rfl, hA w]; ring
  simp_rw [hyA]
  rw [← hc2, hAdet]
  have : ENNReal.ofReal (D ^ (-(σ - 1))) = ENNReal.ofReal (D ^ (-σ)) * ENNReal.ofReal D := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hD0.le _)]
    congr 1
    rw [show -(σ - 1) = -σ + 1 by ring, Real.rpow_add hD0, Real.rpow_one]
  rw [this]
  ring

/-- **Hua's recursion:** $\mathrm{hua}_{r+1}(\sigma) = c_1(\sigma)c_2(r,\sigma)\,\mathrm{hua}_r(\sigma - 1)$. -/
theorem hua_succ (r : ℕ) (σ : ℝ) : hua (r + 1) σ = hc1 σ * hc2 r σ * hua r (σ - 1) := by
  have hFm : Measurable fun b : UIdx (r + 1) → ℝ => ENNReal.ofReal (‖(hH b).det‖ ^ (-σ)) := measurable_huaF σ
  have hG : Measurable fun x : ℝ × (Fin r → ℝ) × (UIdx r → ℝ) =>
      ENNReal.ofReal (‖(hH (asm x.1 x.2.1 x.2.2)).det‖ ^ (-σ)) :=
    hFm.comp measurable_asm
  have hA : ∀ a : ℝ, ∫⁻ u : Fin r → ℝ, ∫⁻ v : UIdx r → ℝ, ENNReal.ofReal (‖(hH (asm a u v)).det‖ ^ (-σ)) =
      ∫⁻ v : UIdx r → ℝ, ∫⁻ u : Fin r → ℝ, ENNReal.ofReal (‖(hH (asm a u v)).det‖ ^ (-σ)) := by
    intro a
    exact lintegral_lintegral_swap
      (hG.comp (f := fun x : (Fin r → ℝ) × (UIdx r → ℝ) => (a, x.1, x.2)) (by fun_prop)).aemeasurable
  have hH2 : Measurable fun x : (ℝ × (UIdx r → ℝ)) × (Fin r → ℝ) =>
      ENNReal.ofReal (‖(hH (asm x.1.1 x.2 x.1.2)).det‖ ^ (-σ)) :=
    hG.comp (f := fun x : (ℝ × (UIdx r → ℝ)) × (Fin r → ℝ) => (x.1.1, x.2, x.1.2)) (by fun_prop)
  have hB : (∫⁻ a : ℝ, ∫⁻ v : UIdx r → ℝ, ∫⁻ u : Fin r → ℝ, ENNReal.ofReal (‖(hH (asm a u v)).det‖ ^ (-σ))) =
      ∫⁻ v : UIdx r → ℝ, ∫⁻ a : ℝ, ∫⁻ u : Fin r → ℝ, ENNReal.ofReal (‖(hH (asm a u v)).det‖ ^ (-σ)) :=
    lintegral_lintegral_swap
      (f := fun a v => ∫⁻ u : Fin r → ℝ, ENNReal.ofReal (‖(hH (asm a u v)).det‖ ^ (-σ)))
      (by exact (hH2.lintegral_prod_right').aemeasurable)
  have hC : ∀ v : UIdx r → ℝ, ∫⁻ a : ℝ, ∫⁻ u : Fin r → ℝ, ENNReal.ofReal (‖(hH (asm a u v)).det‖ ^ (-σ)) =
      ∫⁻ u : Fin r → ℝ, ∫⁻ a : ℝ, ENNReal.ofReal (‖(hH (asm a u v)).det‖ ^ (-σ)) := by
    intro v
    exact lintegral_lintegral_swap
      (hG.comp (f := fun x : ℝ × (Fin r → ℝ) => (x.1, x.2, v)) (by fun_prop)).aemeasurable
  unfold hua
  rw [lintegral_split hFm, lintegral_congr fun a => hA a]
  rw [show (∫⁻ a : ℝ, ∫⁻ v : UIdx r → ℝ, ∫⁻ u : Fin r → ℝ, ENNReal.ofReal (‖(hH (asm a u v)).det‖ ^ (-σ))) =
      ∫⁻ v : UIdx r → ℝ, ∫⁻ a : ℝ, ∫⁻ u : Fin r → ℝ, ENNReal.ofReal (‖(hH (asm a u v)).det‖ ^ (-σ)) from hB]
  rw [lintegral_congr fun v => hC v, lintegral_congr fun v => lintegral_row v]
  exact lintegral_const_mul _ (measurable_huaF (σ - 1))

/-- **Hua's integral is finite for $\sigma > r$.** -/
@[kb "hua1963" "Hua's integral over real symmetric matrices [unverified]"]
theorem hua_lt_top : ∀ (r : ℕ) {σ : ℝ}, (r : ℝ) < σ → hua r σ < ∞
  | 0, σ, _ => by
    have h1 : ∀ b : UIdx 0 → ℝ, ENNReal.ofReal (‖(hH b).det‖ ^ (-σ)) = 1 := fun b => by
      simp [Matrix.det_isEmpty]
    simp only [hua, h1, lintegral_one]
    rw [volume_pi, Measure.pi_of_empty]; simp
  | r + 1, σ, hσ => by
    push_cast at hσ
    rw [hua_succ]
    have h1 : hc1 σ < ∞ := hc1_lt_top (by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)])
    have h2 : hc2 r σ < ∞ := hc2_lt_top (by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)])
    have h3 : hua r (σ - 1) < ∞ := hua_lt_top r (by linarith)
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top h1 h2) h3

/-! ### General $Z \in \mathbb H_r$ -/

/-- **Integrability of $|\det(Z + X)|^{-\sigma}$ over real symmetric $X$ in Siegel's range $\sigma > r$.** -/
@[kb "hua1963" "the integral of |det(Z + X)|^{-σ} over symmetric X, σ > r [unverified]"]
theorem integrable_inv_norm_det_rpow {r : ℕ} {σ : ℝ} (hσ : (r : ℝ) < σ) {Z : Matrix (Fin r) (Fin r) ℂ}
    (hZ : Z ∈ siegelH r) :
    Integrable (fun b : UIdx r → ℝ => ‖(Z + cR (symU b)).det‖ ^ (-σ)) := by
  obtain ⟨R, d, hR, hZR⟩ := exists_decomp_siegelH hZ
  have hu : IsUnit R.det := isUnit_iff_ne_zero.mpr hR
  set Q : Matrix (Fin r) (Fin r) ℝ := R⁻¹ with hQ
  have hQR : Q * R = 1 := Matrix.nonsing_inv_mul _ hu
  have hRQ' : Rᵀ * Qᵀ = 1 := by rw [← transpose_mul, hQR, transpose_one]
  have hSG : ∀ S : Matrix (Fin r) (Fin r) ℝ, S = Rᵀ * (Qᵀ * S * Q) * R := by
    intro S
    calc S = (Rᵀ * Qᵀ) * S * (Q * R) := by rw [hRQ', hQR, Matrix.one_mul, Matrix.mul_one]
      _ = Rᵀ * (Qᵀ * S * Q) * R := by simp only [Matrix.mul_assoc]
  -- the linear map `b ↦ Qᵀ (symU b) Q` in upper coordinates
  let L : (UIdx r → ℝ) →ₗ[ℝ] (UIdx r → ℝ) :=
    { toFun := fun b p => (Qᵀ * symU b * Q) p.1.1 p.1.2
      map_add' := fun a b => by
        ext p; simp [symU_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c a => by
        ext p; simp [symU_smul] }
  have hsymL : ∀ b, symU (L b) = Qᵀ * symU b * Q := by
    intro b
    exact symU_upper (A := Qᵀ * symU b * Q)
      (by simp only [transpose_mul, transpose_transpose, symU_transpose, Matrix.mul_assoc])
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro b hb
    have h0 : Qᵀ * symU b * Q = 0 := by rw [← hsymL, hb]; ext i j; simp [symU]
    have hS := hSG (symU b)
    rw [h0, Matrix.mul_zero, Matrix.zero_mul] at hS
    funext p
    have := congrFun (congrFun hS p.1.1) p.1.2
    rw [symU_apply_upper] at this
    simpa using this
  have hdetL : LinearMap.det L ≠ 0 :=
    ((LinearMap.isUnit_iff_isUnit_det L).mp ((LinearMap.isUnit_iff_ker_eq_bot L).mpr hker)).ne_zero
  -- the constant part `diag d` in upper coordinates
  set c0 : UIdx r → ℝ := fun p => (diagonal d) p.1.1 p.1.2 with hc0
  have hsym0 : symU c0 = diagonal d := symU_upper (by simp)
  -- the factorization of the determinant
  have hfac : ∀ b, ‖(Z + cR (symU b)).det‖ ^ (-σ) =
      (|R.det| ^ 2) ^ (-σ) * ‖(hH (L b + c0)).det‖ ^ (-σ) := by
    intro b
    have hmat : Z + cR (symU b) = cR Rᵀ * hH (L b + c0) * cR R := by
      rw [hZR, hH, symU_add, hsymL, hsym0]
      conv_lhs => rw [hSG (symU b)]
      simp only [cR_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      have hdiag : diagonal (fun j => (d j : ℂ) + I) = cR (diagonal d) + I • (1 : Matrix (Fin r) (Fin r) ℂ) := by
        ext i j; by_cases h : i = j
        · subst h; simp
        · simp [h]
      rw [hdiag]
      have hadd : cR (Qᵀ * symU b * Q + diagonal d) = cR Qᵀ * cR (symU b) * cR Q + cR (diagonal d) := by
        rw [← cR_mul, ← cR_mul]; ext i j; simp only [Matrix.map_apply, Matrix.add_apply, Complex.ofReal_add]
      rw [hadd]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      abel
    rw [hmat, det_mul, det_mul, det_cR, det_cR, det_transpose, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, ← Real.mul_rpow (by positivity) (norm_nonneg _)]
    congr 1; ring
  -- integrability of the normalized function
  have hf : Integrable fun c : UIdx r → ℝ => ‖(hH c).det‖ ^ (-σ) := by
    refine ⟨(continuous_det_hH.norm.rpow_const fun b => Or.inl (by
      have := one_le_norm_det_hH b; linarith)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun c => Real.rpow_nonneg (norm_nonneg _) _)]
    exact hua_lt_top r hσ
  have hf0 : Integrable fun c : UIdx r → ℝ => ‖(hH (c + c0)).det‖ ^ (-σ) := hf.comp_add_right c0
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (UIdx r → ℝ))) hdetL
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  have hf1 : Integrable (fun c : UIdx r → ℝ => ‖(hH (c + c0)).det‖ ^ (-σ)) (Measure.map L volume) := by
    rw [hmap]; exact hf0.smul_measure ENNReal.ofReal_ne_top
  have hf2 := (integrable_map_measure hf1.aestronglyMeasurable hLm.aemeasurable).mp hf1
  refine (hf2.const_mul ((|R.det| ^ 2) ^ (-σ))).congr (Filter.Eventually.of_forall fun b => ?_)
  simp only [Function.comp_apply]
  rw [hfac]

/-- Integer-exponent form: $b \mapsto |\det(Z + \mathrm{symU}(b))|^{-k}$ is integrable for $k > r$. -/
theorem integrable_inv_norm_det_pow_sharp {r k : ℕ} (hk : r < k) {Z : Matrix (Fin r) (Fin r) ℂ}
    (hZ : Z ∈ siegelH r) :
    Integrable (fun b : UIdx r → ℝ => ‖(Z + cR (symU b)).det‖⁻¹ ^ k) := by
  refine (integrable_inv_norm_det_rpow (σ := k) (by exact_mod_cast hk) hZ).congr
    (Filter.Eventually.of_forall fun b => ?_)
  simp only
  rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, inv_pow]

end QuadFormsKB.SiegelWeil.Forms.ArchR
