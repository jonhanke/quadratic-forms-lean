/-
# Siegel's formula: $\beta_\infty(m)$ as a limit of volumes

**Proves** that the archimedean density `betaInf` (Hanke 2004, (5.5), p. 369) is Siegel's (5.1) at $v = \infty$:
$\mathrm{Vol}\{Q \le t\} = \omega_n D^{-1/2} t^{n/2}$ (`volume_setOf_evalIn_le`) and
$\mathrm{Vol}\{m < Q \le m+\varepsilon\}/\varepsilon \to \beta_\infty(m)$ (`tendsto_volume_shell_div`), for positive definite
integral $Q$. This pins down the normalization $D = \det(H/2) = \det H/2^n$ (`gramDet`).
-/
import QuadFormsKB.Siegel.LocalProduct

open Matrix MeasureTheory Filter Topology

namespace QuadFormsKB.Siegel

variable {n : ℕ}

/-- **Square-root factorization of a positive definite real symmetric matrix** (spectral theorem): if
$A = A^{\mathsf T}$ and $\vec{x}^{\mathsf T}A\vec{x} > 0$ for $\vec{x} \ne 0$, there is $S$ with
$\vec{x}^{\mathsf T}A\vec{x} = \sum_i (S\vec{x})_i^2$, $\det A > 0$ and $|\det S| = \sqrt{\det A}$
($S = \mathrm{diag}(\sqrt{\lambda_i})\,U^{\mathsf T}$ for Mathlib's eigen-decomposition $A = U\,\mathrm{diag}(\lambda)\,U^{\mathsf T}$). -/
theorem exists_sqrt_factor (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)) :
    ∃ S : Matrix (Fin n) (Fin n) ℝ, (∀ x, x ⬝ᵥ (A *ᵥ x) = ∑ i, (S *ᵥ x) i ^ 2) ∧
      0 < A.det ∧ |S.det| = Real.sqrt A.det := by
  set U : Matrix (Fin n) (Fin n) ℝ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  set lam := hA.eigenvalues
  have hstar : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hUU : Uᵀ * U = 1 := by
    rw [← hstar]; exact Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hUU' : U * Uᵀ = 1 := by
    rw [← hstar]; exact Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hdiag : Uᵀ * A * U = diagonal lam := by
    have := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    rw [← hstar]
    convert this using 2
    funext i; simp [lam]
  have hAeq : A = U * diagonal lam * Uᵀ := by
    rw [← hdiag]
    simp only [← Matrix.mul_assoc, hUU', Matrix.one_mul]
    rw [Matrix.mul_assoc, hUU', Matrix.mul_one]
  have hlpos : ∀ i, 0 < lam i := by
    intro i
    have hne : U *ᵥ Pi.single i 1 ≠ 0 := by
      intro h0
      have := congrArg (fun v => Uᵀ *ᵥ v) h0
      simp only [mulVec_mulVec, hUU, one_mulVec, mulVec_zero] at this
      have := congrFun this i
      simp at this
    have h1 := hpos _ hne
    have h2 : (U *ᵥ Pi.single i 1) ⬝ᵥ (A *ᵥ (U *ᵥ Pi.single i 1)) = lam i := by
      rw [dotProduct_conj, hdiag]
      simp
    linarith
  set S : Matrix (Fin n) (Fin n) ℝ := diagonal (fun i => Real.sqrt (lam i)) * Uᵀ
  have hSS : Sᵀ * S = A := by
    rw [hAeq]
    simp only [S, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
    congr 1
    rw [← Matrix.mul_assoc, diagonal_mul_diagonal]
    congr 2
    funext i
    rw [Real.mul_self_sqrt (hlpos i).le]
  have hdetA : A.det = ∏ i, lam i := by
    have h := congrArg Matrix.det hAeq
    rw [det_mul, det_mul, det_diagonal, det_transpose] at h
    have hU2 : U.det * U.det = 1 := by
      have := congrArg Matrix.det hUU
      rwa [det_mul, det_transpose, det_one] at this
    rw [h]
    linear_combination (∏ i, lam i) * hU2
  refine ⟨S, fun x => ?_, ?_, ?_⟩
  · have : ∑ i, (S *ᵥ x) i ^ 2 = (S *ᵥ x) ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ (S *ᵥ x)) := by
      simp [dotProduct, sq]
    rw [this, dotProduct_conj, Matrix.mul_one, hSS]
  · rw [hdetA]; exact Finset.prod_pos fun i _ => hlpos i
  · have hU2 : U.det * U.det = 1 := by
      have := congrArg Matrix.det hUU
      rwa [det_mul, det_transpose, det_one] at this
    have hUabs : |U.det| = 1 := by
      have h0 : |U.det| * |U.det| = 1 := by rw [← abs_mul, hU2, abs_one]
      nlinarith [abs_nonneg U.det]
    have hP : 0 ≤ ∏ i, Real.sqrt (lam i) := Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _
    rw [show S.det = (∏ i, Real.sqrt (lam i)) * U.det by simp [S, det_mul, det_diagonal],
      abs_mul, hUabs, mul_one, abs_of_nonneg hP, hdetA]
    rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (Finset.prod_nonneg fun i _ => (hlpos i).le) hP,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => (Real.mul_self_sqrt (hlpos i).le).symm


/-- **The real Gram matrix** $A = H/2$ of an integral form: $Q(\vec{x}) = \vec{x}^{\mathsf T} A \vec{x}$ on $\mathbb{R}^n$
(`evalIn_real_eq_gram`); Hanke's symmetric $(c_{ij})$ in (2.1). -/
noncomputable def gramMatrix (Q : QuadForm ℤ n) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • Q.hessian.map (algebraMap ℤ ℝ)

/-- $Q(\vec{x}) = \vec{x}^{\mathsf T}(H/2)\vec{x}$ for $\vec{x} \in \mathbb{R}^n$. -/
theorem evalIn_real_eq_gram (Q : QuadForm ℤ n) (x : Fin n → ℝ) :
    Q.evalIn ℝ x = x ⬝ᵥ (gramMatrix Q *ᵥ x) := by
  have h := QuadForm.polar_eq_hessian ℝ Q x x
  rw [← two_smul ℝ x, LocalDensity.evalIn_smul] at h
  rw [gramMatrix, smul_mulVec, dotProduct_smul, smul_eq_mul, ← h]
  ring

/-- The Gram matrix is symmetric. -/
theorem gramMatrix_isHermitian (Q : QuadForm ℤ n) : (gramMatrix Q).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, gramMatrix,
    transpose_smul, ← Matrix.transpose_map, (LocalDensity.hessian_isSymm Q).eq]

/-- `gramDet Q` $= \det(H/2)$, Hanke's $D$. -/
theorem gramDet_eq_det (Q : QuadForm ℤ n) : gramDet Q = (gramMatrix Q).det := by
  have h := RingHom.map_det (algebraMap ℤ ℝ) Q.hessian
  rw [RingHom.mapMatrix_apply] at h
  rw [gramDet, gramMatrix, det_smul, ← h, Fintype.card_fin]
  simp [div_eq_inv_mul]

/-- $2\,\Gamma(3/2) = \sqrt{\pi}$. -/
theorem two_mul_Gamma_three_halves : 2 * Real.Gamma (1 / 2 + 1) = Real.sqrt Real.pi := by
  rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  ring

/-- **Volume of the solid ellipsoid:** for positive definite $Q$, $n \ge 1$ and $t \ge 0$,
$$\mathrm{Vol}\{\vec{x} \in \mathbb{R}^n : Q(\vec{x}) \le t\} = \omega_n\, D^{-1/2}\, t^{n/2}$$
(Lebesgue measure on $\mathbb{R}^n$; $\omega_n$ = `unitBallVol n`, $D$ = `gramDet Q`). *Proof:* $Q(\vec{x}) = \|S\vec{x}\|^2$
(`exists_sqrt_factor`), change of variables (`addHaar_preimage_linearMap`) and Mathlib's volume of the
Euclidean ball (`volume_sum_rpow_le`). -/
theorem volume_setOf_evalIn_le {Q : IntQF n} (hQ : Q.PosDef) (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    volume {x : Fin n → ℝ | Q.evalIn ℝ x ≤ t} =
      ENNReal.ofReal (unitBallVol n * gramDet Q ^ (-(1 / 2 : ℝ)) * t ^ ((n : ℝ) / 2)) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨S, hS, hdetpos, hdetS⟩ := exists_sqrt_factor (gramMatrix Q) (gramMatrix_isHermitian Q)
    (fun x hx => by rw [← evalIn_real_eq_gram]; exact hQ.evalIn_real_pos x hx)
  have hS0 : S.det ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hdetS
    exact (Real.sqrt_pos.mpr hdetpos).ne' hdetS.symm
  set s : Set (Fin n → ℝ) := {y | (∑ i, |y i| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ Real.sqrt t}
  have hset : {x : Fin n → ℝ | Q.evalIn ℝ x ≤ t} = (Matrix.toLin' S) ⁻¹' s := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Matrix.toLin'_apply, s]
    rw [evalIn_real_eq_gram, hS]
    have e : (∑ i, |(S *ᵥ x) i| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = Real.sqrt (∑ i, (S *ᵥ x) i ^ 2) := by
      rw [Real.sqrt_eq_rpow]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.rpow_two, sq_abs]
    rw [e, Real.sqrt_le_sqrt_iff ht]
  rw [hset, MeasureTheory.Measure.addHaar_preimage_linearMap _ (by rwa [LinearMap.det_toLin']),
    LinearMap.det_toLin', MeasureTheory.volume_sum_rpow_le (Fin n) (by norm_num : (1 : ℝ) ≤ 2),
    Fintype.card_fin, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hG : 2 * Real.Gamma (2⁻¹ + 1) = Real.sqrt Real.pi := by
    rw [← one_div]; exact two_mul_Gamma_three_halves
  have hD : 0 ≤ gramDet Q := by rw [gramDet_eq_det]; exact hdetpos.le
  have ht' : Real.sqrt t ^ n = t ^ ((n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht]
    ring_nf
  have hD' : gramDet Q ^ (-(2⁻¹ : ℝ)) = (Real.sqrt (gramDet Q))⁻¹ := by
    rw [Real.rpow_neg hD, Real.sqrt_eq_rpow, one_div]
  rw [abs_inv, hdetS, ← gramDet_eq_det, unitBallVol_eq hn, one_div, hG, hD', ht']
  ring


/-- **$\beta_\infty(m)$ is Siegel's archimedean density (5.1)** (Hanke 2004, (5.5), p. 369; Siegel, Hilfssatz 26):
for positive definite $Q$, $n \ge 1$ and $m > 0$,
$$\lim_{\varepsilon \to 0^+} \frac{\mathrm{Vol}\{\vec{x} \in \mathbb{R}^n : m < Q(\vec{x}) \le m + \varepsilon\}}{\varepsilon}
= \frac{n\,\omega_n D^{-1/2}}{2} m^{(n-2)/2} = \beta_\infty(m),$$
i.e. (5.1) with $U = (m, m+\varepsilon]$ (Lebesgue measure on $\mathbb{R}^n$ and $\mathbb{R}$). This confirms the
normalization $D = \det(H/2)$ of `gramDet`. (General neighbourhoods $U \to \{m\}$ follow from the same
differentiability; not stated.) -/
@[kb "hanke2004" "(5.1), (5.5), pp. 368–369"]
theorem tendsto_volume_shell_div {Q : IntQF n} (hQ : Q.PosDef) (hn : 1 ≤ n) {m : ℝ} (hm : 0 < m) :
    Tendsto (fun ε => (volume {x : Fin n → ℝ | Q.evalIn ℝ x ∈ Set.Ioc m (m + ε)}).toReal / ε)
      (𝓝[>] 0) (𝓝 (betaInf Q m)) := by
  set K := unitBallVol n * gramDet Q ^ (-(1 / 2 : ℝ))
  have hK : 0 ≤ K := by
    have : 0 ≤ unitBallVol n := ENNReal.toReal_nonneg
    have : 0 ≤ gramDet Q ^ (-(1 / 2 : ℝ)) := by
      rw [gramDet_eq_det]
      exact Real.rpow_nonneg (le_of_lt (by
        obtain ⟨S, -, h, -⟩ := exists_sqrt_factor (gramMatrix Q) (gramMatrix_isHermitian Q)
          (fun x hx => by rw [← evalIn_real_eq_gram]; exact hQ.evalIn_real_pos x hx)
        exact h)) _
    positivity
  set f : ℝ → ℝ := fun t => K * t ^ ((n : ℝ) / 2)
  have hf : HasDerivAt f (K * ((n : ℝ) / 2 * m ^ ((n : ℝ) / 2 - 1))) m :=
    (Real.hasDerivAt_rpow_const (Or.inl hm.ne')).const_mul K
  have heq : betaInf Q m = K * ((n : ℝ) / 2 * m ^ ((n : ℝ) / 2 - 1)) := by
    rw [betaInf, show ((n : ℝ) / 2 - 1) = ((n : ℝ) - 2) / 2 by ring]
    ring
  rw [heq]
  refine hf.tendsto_slope_zero_right.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : 0 < ε := hε
  have hsub : {x : Fin n → ℝ | Q.evalIn ℝ x ≤ m} ⊆ {x | Q.evalIn ℝ x ≤ m + ε} :=
    fun x (hx : Q.evalIn ℝ x ≤ m) => show Q.evalIn ℝ x ≤ m + ε by linarith
  have hdiff : {x : Fin n → ℝ | Q.evalIn ℝ x ∈ Set.Ioc m (m + ε)} =
      {x | Q.evalIn ℝ x ≤ m + ε} \ {x | Q.evalIn ℝ x ≤ m} := by
    ext x; simp [Set.mem_Ioc, and_comm]
  have hmeas : MeasurableSet {x : Fin n → ℝ | Q.evalIn ℝ x ≤ m} :=
    (isClosed_le (continuous_evalIn_real Q) continuous_const).measurableSet
  have hmono : m ^ ((n : ℝ) / 2) ≤ (m + ε) ^ ((n : ℝ) / 2) :=
    Real.rpow_le_rpow hm.le (by linarith) (by positivity)
  rw [hdiff, measure_sdiff hsub hmeas.nullMeasurableSet (by
      rw [volume_setOf_evalIn_le hQ hn hm.le]; exact ENNReal.ofReal_ne_top),
    volume_setOf_evalIn_le hQ hn (by linarith), volume_setOf_evalIn_le hQ hn hm.le,
    ← ENNReal.ofReal_sub _ (by positivity), ENNReal.toReal_ofReal (by nlinarith)]
  simp only [f, smul_eq_mul]
  field_simp
  ring

end QuadFormsKB.Siegel
