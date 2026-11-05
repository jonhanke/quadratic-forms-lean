/-
# A uniform lower bound for $|\det(CZ+D)|$ on compact subsets of the Siegel upper half space

**Layer:** real and complex linear algebra, compactness.

**Statement** (`exists_norm_det_CZD_ge_unif`).  Let $K\subseteq\mathbb H_r$ (`WeilRep.Genus.siegelH r`) be compact.  There is
$c>0$ such that for every $Z\in K$, every real $r\times 2r$ matrix $E=(C\ D)$ with $CD^{\mathsf T}=DC^{\mathsf T}$ such that some
$r$ columns of $E$ (selected by $h$) form the identity matrix, and every entry $E_{ix}$,
$$c\cdot\max(1,|E_{ix}|)\ \le\ |\det(CZ+D)|.$$
This is `exists_norm_det_CZD_ge` with the constant uniform in $Z\in K$.

**Proof sketch.**
1. `norm_det_CZD_ge_of`: the proof of `exists_norm_det_CZD_ge`, with the constant made explicit: if $\alpha,\beta,\delta>0$,
   $K_x\ge0$ satisfy $\alpha|u|^2\le u^{\mathsf T}Y^{-1}u$, $\beta|u|^2\le u^{\mathsf T}Yu$, $\delta\le\det Y$,
   $\sum X_{ij}^2\le K_x$ (where $Z=X+iY$), then $c=\sqrt{\delta\mu^r}$ works with $\mu=\min(\alpha/2,\beta/(1+2K_x))$.
2. `exists_coercive_unif`: on a compact set, a continuous family of positive definite matrices is uniformly coercive (minimum of a
   continuous positive function on $K\times\{u\cdot u=1\}$, then scaling).  Applied to $Z\mapsto\operatorname{Im}Z$ and
   $Z\mapsto(\operatorname{Im}Z)^{-1}$ (continuous on invertible matrices); $\det\operatorname{Im}Z$ has a positive minimum and
   $\sum(\operatorname{Re}Z)_{ij}^2$ a maximum on $K$.

Sources: standard (cf. Siegel, *Symplectic geometry*, Amer. J. Math. 65 (1943); Freitag, *Siegelsche Modulfunktionen* (1983),
Ch. I) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.EisensteinArchBound

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

/-- Variant of `exists_quad_coercive` with the coercivity constants of $Y$, $Y_i$ and the bound on $\sum X_{ij}^2$ given. -/
lemma quad_coercive_of {r : ℕ} (X : Matrix (Fin r) (Fin r) ℝ) {Y Yi : Matrix (Fin r) (Fin r) ℝ}
    {α β Kx : ℝ} (hα : 0 < α) (hβ : 0 < β) (hKx : 0 ≤ Kx)
    (hαY : ∀ u, α * (u ⬝ᵥ u) ≤ u ⬝ᵥ Yi *ᵥ u) (hβY : ∀ u, β * (u ⬝ᵥ u) ≤ u ⬝ᵥ Y *ᵥ u)
    (hK : ∑ i, ∑ j, X i j ^ 2 ≤ Kx) :
    ∀ u v : Fin r → ℝ,
      min (α / 2) (β / (1 + 2 * Kx)) * (u ⬝ᵥ u + v ⬝ᵥ v) ≤
        (X *ᵥ u + v) ⬝ᵥ Yi *ᵥ (X *ᵥ u + v) + u ⬝ᵥ Y *ᵥ u := by
  intro u v
  set K : ℝ := ∑ i, ∑ j, X i j ^ 2 with hKdef
  have hμpos : 0 < min (α / 2) (β / (1 + 2 * Kx)) := lt_min (by positivity) (by positivity)
  set μ := min (α / 2) (β / (1 + 2 * Kx)) with hμ
  have hμ0 : 0 ≤ μ := hμpos.le
  have hμ1 : 2 * μ ≤ α := by
    have := min_le_left (α / 2) (β / (1 + 2 * Kx)); linarith
  have hμ2 : μ * (1 + 2 * Kx) ≤ β := by
    have := min_le_right (α / 2) (β / (1 + 2 * Kx))
    rwa [le_div_iff₀ (by positivity)] at this
  have hXu : (X *ᵥ u) ⬝ᵥ (X *ᵥ u) ≤ Kx * (u ⬝ᵥ u) := by
    have hi : ∀ i, (X *ᵥ u) i * (X *ᵥ u) i ≤ (∑ j, X i j ^ 2) * (u ⬝ᵥ u) := by
      intro i
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => X i j) u
      simpa [sq, mulVec, dotProduct] using this
    have u0 : 0 ≤ u ⬝ᵥ u := dotProduct_self_star_nonneg _
    calc (X *ᵥ u) ⬝ᵥ (X *ᵥ u) = ∑ i, (X *ᵥ u) i * (X *ᵥ u) i := rfl
      _ ≤ ∑ i, (∑ j, X i j ^ 2) * (u ⬝ᵥ u) := Finset.sum_le_sum fun i _ => hi i
      _ = K * (u ⬝ᵥ u) := by rw [hKdef, Finset.sum_mul]
      _ ≤ Kx * (u ⬝ᵥ u) := mul_le_mul_of_nonneg_right hK u0
  have hvv : v ⬝ᵥ v ≤ 2 * ((X *ᵥ u + v) ⬝ᵥ (X *ᵥ u + v)) + 2 * ((X *ᵥ u) ⬝ᵥ (X *ᵥ u)) := by
    simp only [dotProduct, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    nlinarith [sq_nonneg (2 * (X *ᵥ u) i + v i)]
  have h1 := hαY (X *ᵥ u + v)
  have h2 := hβY u
  have a0 : 0 ≤ (X *ᵥ u + v) ⬝ᵥ (X *ᵥ u + v) := dotProduct_self_star_nonneg _
  have u0 : 0 ≤ u ⬝ᵥ u := dotProduct_self_star_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hμ1 a0, mul_le_mul_of_nonneg_right hμ2 u0,
    mul_le_mul_of_nonneg_left hvv hμ0, mul_le_mul_of_nonneg_left hXu hμ0]

/-- **Parametrized lower bound for $|\det(CZ+D)|$**: the constant of `exists_norm_det_CZD_ge`, made explicit in terms of
coercivity constants of $\operatorname{Im}Z$ and $(\operatorname{Im}Z)^{-1}$, a lower bound for $\det\operatorname{Im}Z$ and an
upper bound for $\sum(\operatorname{Re}Z)_{ij}^2$. -/
theorem norm_det_CZD_ge_of {r : ℕ} {Z : Matrix (Fin r) (Fin r) ℂ}
    (hZ : Z ∈ WeilRep.Genus.siegelH r) {α β δ Kx : ℝ} (hα : 0 < α) (hβ : 0 < β) (hδ : 0 < δ)
    (hKx : 0 ≤ Kx)
    (hαY : ∀ u : Fin r → ℝ, α * (u ⬝ᵥ u) ≤ u ⬝ᵥ (Z.map Complex.im)⁻¹ *ᵥ u)
    (hβY : ∀ u : Fin r → ℝ, β * (u ⬝ᵥ u) ≤ u ⬝ᵥ (Z.map Complex.im) *ᵥ u)
    (hδY : δ ≤ (Z.map Complex.im).det)
    (hK : ∑ i, ∑ j, ((Z i j).re) ^ 2 ≤ Kx) :
    ∀ (C D : Matrix (Fin r) (Fin r) ℝ), C * Dᵀ = D * Cᵀ →
      ∀ h : Fin r → Fin r ⊕ Fin r, (Matrix.fromCols C D).submatrix id h = 1 →
        ∀ (i : Fin r) (x : Fin r ⊕ Fin r),
          √(δ * (min (α / 2) (β / (1 + 2 * Kx))) ^ r) * max 1 |Matrix.fromCols C D i x| ≤
            ‖(C.map (↑) * Z + D.map (↑) : Matrix (Fin r) (Fin r) ℂ).det‖ := by
  obtain ⟨hZs, hY⟩ := hZ
  set X : Matrix (Fin r) (Fin r) ℝ := Z.map Complex.re with hXdef
  set Y : Matrix (Fin r) (Fin r) ℝ := Z.map Complex.im with hYdef
  have hXs : Xᵀ = X := by rw [hXdef, ← Matrix.transpose_map, hZs]
  have hYs : Yᵀ = Y := by rw [hYdef, ← Matrix.transpose_map, hZs]
  have hZeq : Z = X.map (↑) + Complex.I • Y.map (↑) := by
    ext i j
    simp only [hXdef, hYdef, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    rw [mul_comm Complex.I]; exact (Complex.re_add_im _).symm
  have hdetY : 0 < Y.det := hY.det_pos
  have hYu : IsUnit Y.det := isUnit_iff_ne_zero.2 hdetY.ne'
  have hYYi : Y * Y⁻¹ = 1 := Matrix.mul_nonsing_inv Y hYu
  have hYiY : Y⁻¹ * Y = 1 := Matrix.nonsing_inv_mul Y hYu
  have hμ0 : 0 < min (α / 2) (β / (1 + 2 * Kx)) := lt_min (by positivity) (by positivity)
  have hμ := quad_coercive_of X hα hβ hKx hαY hβY hK
  set μ := min (α / 2) (β / (1 + 2 * Kx)) with hμdef
  have hdd : Y.det * Y⁻¹.det = 1 := by rw [← det_mul, hYYi, det_one]
  intro C D hCD h hh i x
  set E : Matrix (Fin r) (Fin r ⊕ Fin r) ℝ := fromCols C D with hEdef
  set H : Matrix (Fin r) (Fin r) ℝ := (C * X + D) * Y⁻¹ * (C * X + D)ᵀ + C * Y * Cᵀ with hHdef
  have hQ : ∀ w, μ * ((Eᵀ *ᵥ w) ⬝ᵥ (Eᵀ *ᵥ w)) ≤ w ⬝ᵥ H *ᵥ w :=
    quad_form_bound (Y := Y) (Yi := Y⁻¹) C D hXs hμ
  have hHs : Hᵀ = H := by
    have hYis : (Y⁻¹)ᵀ = Y⁻¹ := by rw [transpose_nonsing_inv, hYs]
    rw [hHdef, transpose_add, transpose_mul, transpose_mul, transpose_mul, transpose_transpose,
      hYis, transpose_mul, transpose_transpose, hYs]
    simp only [mul_assoc]
  have hBs : (H - μ • (1 : Matrix (Fin r) (Fin r) ℝ))ᵀ = H - μ • 1 := by
    rw [transpose_sub, transpose_smul, transpose_one, hHs]
  have hB : (H - μ • (1 : Matrix (Fin r) (Fin r) ℝ)).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg (by rw [isHermitian_iff_isSymm]; exact hBs)
      fun w => ?_
    have h1 := hQ w
    have h2 := frame_dot_le hh w
    have h3 := mul_le_mul_of_nonneg_left h2 hμ0.le
    simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
      smul_eq_mul]
    linarith
  have hdiag : ∀ k, μ * ∑ y, E k y ^ 2 ≤ H k k := by
    intro k
    have h1 := hQ (Pi.single k 1)
    have e3 : (Pi.single k (1 : ℝ)) ⬝ᵥ H *ᵥ Pi.single k 1 = H k k := by
      simp [mulVec_single]
    have e4 : (Eᵀ *ᵥ Pi.single k (1 : ℝ)) ⬝ᵥ (Eᵀ *ᵥ Pi.single k (1 : ℝ)) = ∑ y, E k y ^ 2 := by
      simp [mulVec_single, dotProduct, sq]
    rw [e3, e4] at h1
    exact h1
  have htrH : μ * ∑ y, ∑ k, E k y ^ 2 ≤ H.trace := by
    calc μ * ∑ y, ∑ k, E k y ^ 2 = ∑ k, μ * ∑ y, E k y ^ 2 := by
          rw [Finset.sum_comm, Finset.mul_sum]
      _ ≤ ∑ k, H k k := Finset.sum_le_sum fun k _ => hdiag k
      _ = H.trace := by simp [trace]
  have hS := frame_sum_ge hh i x
  have htrB : μ * (E i x ^ 2 - 1) ≤ (H - μ • (1 : Matrix (Fin r) (Fin r) ℝ)).trace := by
    rw [trace_sub, trace_smul, trace_one]
    simp only [Fintype.card_fin, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hS hμ0.le]
  have hdetH := det_ge_of_sub_psd hμ0 hB (E i x ^ 2) htrB
  have hkey := key_identity (Y := Y) (Yi := Y⁻¹) C D hXs hYs hYYi hYiY hCD hZeq
  have hdc : ∀ M : Matrix (Fin r) (Fin r) ℝ, (M.map (↑) : Matrix (Fin r) (Fin r) ℂ).det =
      ((M.det : ℝ) : ℂ) := fun M => (RingHom.map_det Complex.ofRealHom M).symm
  set W : Matrix (Fin r) (Fin r) ℂ := C.map (↑) * Z + D.map (↑) with hWdef
  have hdet := congrArg Matrix.det hkey
  rw [det_mul, det_mul, det_conjTranspose, hdc, hdc] at hdet
  have hnorm : Y⁻¹.det * ‖W.det‖ ^ 2 = H.det := by
    have hmc : W.det * star W.det = ((‖W.det‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have h1 : (((Y⁻¹.det * ‖W.det‖ ^ 2 : ℝ)) : ℂ) = ((H.det : ℝ) : ℂ) := by
      calc (((Y⁻¹.det * ‖W.det‖ ^ 2 : ℝ)) : ℂ) = (Y⁻¹.det : ℂ) * (W.det * star W.det) := by
            rw [hmc]; push_cast; ring
        _ = W.det * (Y⁻¹.det : ℂ) * star W.det := by ring
        _ = _ := hdet
    exact_mod_cast h1
  have hn2 : ‖W.det‖ ^ 2 = Y.det * H.det := by
    calc ‖W.det‖ ^ 2 = (Y.det * Y⁻¹.det) * ‖W.det‖ ^ 2 := by rw [hdd, one_mul]
      _ = Y.det * (Y⁻¹.det * ‖W.det‖ ^ 2) := by ring
      _ = _ := by rw [hnorm]
  have hm2 : (max 1 |E i x|) ^ 2 ≤ max 1 (E i x ^ 2) := by
    rcases le_total 1 |E i x| with h1 | h1
    · rw [max_eq_right h1, sq_abs]; exact le_max_right _ _
    · rw [max_eq_left h1]; simp
  have hc2 : (√(δ * μ ^ r)) ^ 2 = δ * μ ^ r :=
    Real.sq_sqrt (mul_pos hδ (pow_pos hμ0 r)).le
  have hsq : (√(δ * μ ^ r) * max 1 |E i x|) ^ 2 ≤ ‖W.det‖ ^ 2 := by
    rw [mul_pow, hc2, hn2]
    have h1 : μ ^ r * (max 1 |E i x|) ^ 2 ≤ H.det :=
      le_trans (mul_le_mul_of_nonneg_left hm2 (pow_nonneg hμ0.le r)) hdetH
    have h2 := mul_le_mul_of_nonneg_left h1 hdetY.le
    have h3 : 0 ≤ μ ^ r * (max 1 |E i x|) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hδY h3]
  have hcm : 0 ≤ √(δ * μ ^ r) * max 1 |E i x| :=
    mul_nonneg (Real.sqrt_nonneg _) (le_trans zero_le_one (le_max_left _ _))
  exact (pow_le_pow_iff_left₀ hcm (norm_nonneg _) (by norm_num)).1 hsq

/-- Uniform coercivity: a continuous-on-$K$ family of positive definite matrices over a compact $K$ is uniformly coercive. -/
lemma exists_coercive_unif {r : ℕ} {M : Type*} [TopologicalSpace M] {K : Set M} (hK : IsCompact K)
    (F : M → Matrix (Fin r) (Fin r) ℝ) (hF : ContinuousOn F K) (hpos : ∀ Z ∈ K, (F Z).PosDef) :
    ∃ α : ℝ, 0 < α ∧ ∀ Z ∈ K, ∀ u : Fin r → ℝ, α * (u ⬝ᵥ u) ≤ u ⬝ᵥ F Z *ᵥ u := by
  set S : Set (Fin r → ℝ) := {u | u ⬝ᵥ u = 1} with hSdef
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact isClosed_eq (by unfold dotProduct; fun_prop) continuous_const
    · refine (Metric.isBounded_closedBall (x := (0 : Fin r → ℝ)) (r := 1)).subset fun u hu => ?_
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have h1 : u i * u i ≤ u ⬝ᵥ u := by
        unfold dotProduct
        exact Finset.single_le_sum (f := fun j => u j * u j) (fun j _ => mul_self_nonneg _)
          (Finset.mem_univ i)
      rw [Real.norm_eq_abs]
      have : u ⬝ᵥ u = 1 := hu
      nlinarith [abs_mul_abs_self (u i), abs_nonneg (u i)]
  have hKS : IsCompact (K ×ˢ S) := hK.prod hSc
  have hFe : ∀ i j, ContinuousOn (fun p : M × (Fin r → ℝ) => F p.1 i j) (K ×ˢ S) := fun i j =>
    ((continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn
      (hF.comp continuousOn_fst (fun p hp => hp.1))))
  have hg : ContinuousOn (fun p : M × (Fin r → ℝ) => p.2 ⬝ᵥ F p.1 *ᵥ p.2) (K ×ˢ S) := by
    unfold dotProduct mulVec dotProduct
    refine continuousOn_finsetSum _ fun i _ => ?_
    refine ContinuousOn.mul ((continuous_apply i).comp_continuousOn continuousOn_snd) ?_
    refine continuousOn_finsetSum _ fun j _ => ?_
    exact (hFe i j).mul ((continuous_apply j).comp_continuousOn continuousOn_snd)
  obtain ⟨α, hα, hαmin⟩ := hKS.exists_forall_le' hg (a := 0) (fun p hp => by
    have := (hpos p.1 hp.1).dotProduct_mulVec_pos (x := p.2) (by
      intro h0
      have := hp.2
      simp only [hSdef, Set.mem_ofPred_eq] at this
      rw [h0] at this; simp at this)
    simpa using this)
  refine ⟨α, hα, fun Z hZ u => ?_⟩
  by_cases hu : u ⬝ᵥ u = 0
  · have : u = 0 := dotProduct_self_eq_zero.1 hu
    subst this; simp
  · have hpos' : 0 < u ⬝ᵥ u := lt_of_le_of_ne (dotProduct_self_star_nonneg u) (Ne.symm hu)
    set s := √(u ⬝ᵥ u) with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 hpos'
    have hss : s * s = u ⬝ᵥ u := Real.mul_self_sqrt hpos'.le
    have hw : (s⁻¹ • u) ⬝ᵥ (s⁻¹ • u) = 1 := by
      rw [smul_dotProduct, dotProduct_smul]
      simp only [smul_eq_mul]
      rw [← hss]; field_simp
    have h1 := hαmin (Z, s⁻¹ • u) ⟨hZ, hw⟩
    simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1
    have h2 : s⁻¹ * (s⁻¹ * (u ⬝ᵥ F Z *ᵥ u)) = (u ⬝ᵥ F Z *ᵥ u) / (u ⬝ᵥ u) := by
      rw [← hss]; field_simp
    rw [h2, le_div_iff₀ hpos'] at h1
    linarith

/-- $Z\mapsto(\operatorname{Im}Z)^{-1}$ is continuous on $\mathbb H_r$. -/
lemma continuousOn_inv_im (r : ℕ) :
    ContinuousOn (fun Z : Matrix (Fin r) (Fin r) ℂ => (Z.map Complex.im)⁻¹)
      (WeilRep.Genus.siegelH r) := by
  intro Z hZ
  have hcont : Continuous (fun Z : Matrix (Fin r) (Fin r) ℂ => Z.map Complex.im) :=
    continuous_pi fun i => continuous_pi fun j =>
      Complex.continuous_im.comp ((continuous_apply j).comp (continuous_apply i))
  have hdet : (Z.map Complex.im).det ≠ 0 := hZ.2.det_pos.ne'
  have hinv : ContinuousAt (Inv.inv : Matrix (Fin r) (Fin r) ℝ → _) (Z.map Complex.im) := by
    refine continuousAt_matrix_inv _ ?_
    have : (Ring.inverse : ℝ → ℝ) = Inv.inv := Ring.inverse_eq_inv'
    rw [this]
    exact continuousAt_inv₀ hdet
  exact (ContinuousAt.comp (g := (Inv.inv : Matrix (Fin r) (Fin r) ℝ → _)) (f := fun Z : Matrix (Fin r) (Fin r) ℂ => Z.map Complex.im) hinv hcont.continuousAt).continuousWithinAt

/-- **Uniform lower bound for $|\det(CZ+D)|$ on a compact subset of the Siegel upper half space.**  As
`exists_norm_det_CZD_ge`, but the constant $c$ works for all $Z\in K$. -/
theorem exists_norm_det_CZD_ge_unif {r : ℕ} {K : Set (Matrix (Fin r) (Fin r) ℂ)} (hK : IsCompact K)
    (hKH : K ⊆ WeilRep.Genus.siegelH r) :
    ∃ c : ℝ, 0 < c ∧ ∀ Z ∈ K, ∀ (C D : Matrix (Fin r) (Fin r) ℝ), C * Dᵀ = D * Cᵀ →
      ∀ h : Fin r → Fin r ⊕ Fin r, (Matrix.fromCols C D).submatrix id h = 1 →
        ∀ (i : Fin r) (x : Fin r ⊕ Fin r),
          c * max 1 |Matrix.fromCols C D i x| ≤
            ‖(C.map (↑) * Z + D.map (↑) : Matrix (Fin r) (Fin r) ℂ).det‖ := by
  have him : Continuous (fun Z : Matrix (Fin r) (Fin r) ℂ => Z.map Complex.im) :=
    continuous_pi fun i => continuous_pi fun j =>
      Complex.continuous_im.comp ((continuous_apply j).comp (continuous_apply i))
  have hKc : ∀ Z ∈ K, Z ∈ WeilRep.Genus.siegelH r := hKH
  obtain ⟨α, hα, hαK⟩ := exists_coercive_unif hK _
    ((continuousOn_inv_im r).mono hKH) (fun Z hZ => (hKc Z hZ).2.inv)
  obtain ⟨β, hβ, hβK⟩ := exists_coercive_unif hK _ him.continuousOn (fun Z hZ => (hKc Z hZ).2)
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_forall_le' (f := fun Z : Matrix (Fin r) (Fin r) ℂ =>
      (Z.map Complex.im).det) (a := 0)
    (him.matrix_det.continuousOn) (fun Z hZ => (hKc Z hZ).2.det_pos)
  have hre : Continuous (fun Z : Matrix (Fin r) (Fin r) ℂ => ∑ i, ∑ j, ((Z i j).re) ^ 2) := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (Complex.continuous_re.comp ((continuous_apply j).comp (continuous_apply i))).pow 2
  obtain ⟨M, hM⟩ := hK.bddAbove_image hre.continuousOn
  set Kx := max M 0 with hKxdef
  have hKx : 0 ≤ Kx := le_max_right _ _
  have hμ : 0 < min (α / 2) (β / (1 + 2 * Kx)) := lt_min (by positivity) (by positivity)
  refine ⟨√(δ * (min (α / 2) (β / (1 + 2 * Kx))) ^ r), Real.sqrt_pos.2 (by positivity), ?_⟩
  intro Z hZ
  exact norm_det_CZD_ge_of (hKc Z hZ) hα hβ hδ hKx (hαK Z hZ) (hβK Z hZ) (hδK Z hZ)
    ((hM ⟨Z, hZ, rfl⟩).trans (le_max_left _ _))

end QuadFormsKB.SiegelWeil.Forms
