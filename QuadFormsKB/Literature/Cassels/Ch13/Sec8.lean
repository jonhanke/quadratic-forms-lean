/-
# Cassels, Chapter 13, §8 (and §6, Theorem 6.1): the fundamental domain of an anisotropic ternary form

Formalization of Cassels, *Rational Quadratic Forms* (1978), Ch. 13, §6, Theorem 6.1 and Corollary (pp. 304–305), and
§8, *Proof of Theorem 6.1*, pp. 313–316: for an integral indefinite ternary form $f$ the group $O^+(f)$ of proper
integral automorphs acts on the non-Euclidean plane $\mathcal D$ (§7) with finite stabilizers of compact sets
(Lemma 8.1); for anisotropic $f$ the orbit of the origin is $d_1$-dense (Lemmas 8.2, 8.3), the Dirichlet domain is a
polygon (Lemma 8.4 and Corollary). Theorems 6.1 (a convex polygon as fundamental domain) and 8.1 (generators) are in
`Sec8Fund.lean`.

**Setting** (Cassels, §6, (6.1)–(6.11), pp. 303–304). $f$ is an integral ternary form (`IntQF 3`) with real matrix
$F$, and $L$ is an invertible real matrix with $F = L^{\mathsf T}\operatorname{diag}(1, 1, -1)L$, i.e.
$f = X_0^2 + X_1^2 - X_2^2$ with the real linear forms $X_j = (L\vec{x})_j$ (6.3). (Cassels first replaces $f$ by $-f$
if need be.) A real automorph $T$ acts on $\mathcal D$ by $T(\vec{\xi}) = \pi(LTL^{-1}(\xi_0, \xi_1, 1))$ (6.9) (`actD`).
-/
import QuadFormsKB.Literature.Cassels.Ch13.Sec7
import QuadFormsKB.Literature.Cassels.Ch13.Sec2
import QuadFormsKB.Literature.Cassels.Ch13.Sec8Lorentz
import QuadFormsKB.Literature.Cassels.Ch13.Sec8Polytope

open Matrix

namespace QuadFormsKB.Reduction

open S8

/-- **The action (6.9) of a real automorph on the plane**: $T(\vec{\xi}) = \pi(LTL^{-1}(\xi_0, \xi_1, 1))$, for the
coordinates $X = L\vec{x}$ of (6.3)–(6.7). -/
@[kb "cassels1978" "Ch. 13, §6, (6.9)–(6.11), p. 304 (the action of O⁺(f) on 𝒟)"]
noncomputable def actD (L : Matrix (Fin 3) (Fin 3) ℝ) (T : Matrix (Fin 3) (Fin 3) ℝ) (ξ : Fin 2 → ℝ) : Fin 2 → ℝ :=
  flt (L * T * L⁻¹) ξ

/-- Helper: $\cosh d(0, P(0)) = |P_{22}|$ for a Lorentz matrix $P$. -/
theorem coshDist_zero_flt_zero {P : Matrix (Fin 3) (Fin 3) ℝ} (hP : IsLor P) :
    coshDist 0 (flt P 0) = |P 2 2| := by
  have hu := hP.entry_eq 2 2
  simp [lorentz] at hu
  have e : ∀ i, (P *ᵥ liftPt 0) i = P i 2 := fun i => by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, liftPt]
  have h22 : P 2 2 ≠ 0 := by
    intro h
    rw [h] at hu
    nlinarith [sq_nonneg (P 0 2), sq_nonneg (P 1 2)]
  rw [coshDist_zero_left, flt_apply_zero, flt_apply_one, e, e, e]
  have : 1 - (P 0 2 / P 2 2) ^ 2 - (P 1 2 / P 2 2) ^ 2 = (P 2 2 ^ 2)⁻¹ := by
    field_simp
    linarith
  rw [this, Real.sqrt_inv, Real.sqrt_sq_eq_abs]
  simp

/-- Helper: the Lorentz matrix $P = LTL^{-1}$ of an integral automorph. -/
theorem isLor_conj_aut {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) {T : GL (Fin 3) ℤ} (hT : T ∈ Siegel.Aut Q) :
    IsLor (L * castM T.val * L⁻¹) :=
  isLor_conj hL hF ((mem_aut_iff_act Q T).1 hT)

/-- Helper: conjugation is multiplicative. -/
theorem conj_mul_eq {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det) (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    L * (A * B) * L⁻¹ = (L * A * L⁻¹) * (L * B * L⁻¹) := by
  have h : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul _ hL
  calc L * (A * B) * L⁻¹ = L * A * (L⁻¹ * L) * B * L⁻¹ := by rw [h]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = (L * A * L⁻¹) * (L * B * L⁻¹) := by simp only [Matrix.mul_assoc]

/-- **The integral automorphs act on $\mathcal D$** (Cassels, Ch. 13, (6.10), p. 304): for $T \in O(f)$,
$\vec{\xi} \mapsto T(\vec{\xi})$ maps $\mathcal D$ into itself, and $(TT')(\vec{\xi}) = T(T'(\vec{\xi}))$. -/
@[kb "cassels1978" "Ch. 13, §6, (6.10), p. 304"]
theorem actD_mapsTo {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) {T T' : GL (Fin 3) ℤ} (hT : T ∈ Siegel.Aut Q) (hT' : T' ∈ Siegel.Aut Q)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ disc) :
    actD L (castM T.val) ξ ∈ disc ∧
      actD L (castM (T * T').val) ξ = actD L (castM T.val) (actD L (castM T'.val) ξ) := by
  have hP := isLor_conj_aut hL hF hT
  have hP' := isLor_conj_aut hL hF hT'
  refine ⟨hP.flt_mem_disc hξ, ?_⟩
  unfold actD
  rw [Units.val_mul, castM_mul, conj_mul_eq hL]
  exact hP'.flt_mul hξ

/-- Helper (the content of Lemma 8.1): integral automorphs moving $\vec\eta$ into a disc of radius $r$, $0\le r<1$,
have entries bounded by a constant depending only on $L$, $\vec\eta$, $r$. -/
theorem entry_bound_of_ball {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) {η : Fin 2 → ℝ} (hη : η ∈ disc) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    ∃ K : ℝ, ∀ T ∈ Siegel.Aut Q, (actD L (castM T.val) η) 0 ^ 2 + (actD L (castM T.val) η) 1 ^ 2 ≤ r ^ 2 →
      ∀ i j, |(T.val i j : ℝ)| ≤ K := by
  have hη' : η 0 ^ 2 + η 1 ^ 2 < 1 := hη
  have hκ : 0 < 1 - η 0 ^ 2 - η 1 ^ 2 := by linarith
  obtain ⟨B, hB, hBe⟩ := exists_lorBoost hη
  obtain ⟨mB, hmB0, hmB⟩ := exists_entry_bound (lorInv B)
  obtain ⟨mL, hmL0, hmL⟩ := exists_entry_bound L
  obtain ⟨mLi, hmLi0, hmLi⟩ := exists_entry_bound L⁻¹
  have hr1 : 0 < 1 - r ^ 2 := by nlinarith
  set κ := 1 - η 0 ^ 2 - η 1 ^ 2 with hκdef
  set U := √(κ / (1 - r ^ 2)) with hU
  have hU0 : 0 ≤ U := Real.sqrt_nonneg _
  have hU2 : U ^ 2 = κ / (1 - r ^ 2) := Real.sq_sqrt (by positivity)
  have hsk : 0 < √κ := Real.sqrt_pos.2 hκ
  set C := (√κ)⁻¹ * U with hC
  refine ⟨3 * (3 * mLi * (3 * C * mB)) * mL, fun T hT hball i j => ?_⟩
  have hP := isLor_conj_aut hL hF hT
  set P := L * castM T.val * L⁻¹ with hPdef
  set u := P *ᵥ liftPt η with hu
  have hu2 := hP.last_ne hη
  have hcone := hP.bil_mulVec (liftPt η) (liftPt η)
  rw [bil_liftPt] at hcone
  unfold bil at hcone
  have hz0 : (actD L (castM T.val) η) 0 = u 0 / u 2 := flt_apply_zero P η
  have hz1 : (actD L (castM T.val) η) 1 = u 1 / u 2 := flt_apply_one P η
  rw [hz0, hz1, div_pow, div_pow, ← add_div, div_le_iff₀ (by positivity)] at hball
  have hu2sq : u 2 ^ 2 ≤ U ^ 2 := by
    rw [hU2, le_div_iff₀ hr1]
    nlinarith
  have hule : ∀ k, |u k| ≤ U := by
    intro k
    apply abs_le_of_sq_le_sq _ hU0
    fin_cases k
    · show u 0 ^ 2 ≤ U ^ 2
      nlinarith [sq_nonneg (u 1), sq_nonneg (u 2)]
    · show u 1 ^ 2 ≤ U ^ 2
      nlinarith [sq_nonneg (u 0), sq_nonneg (u 2)]
    · exact hu2sq
  have hW := hP.mul hB
  have hWe : (P * B) *ᵥ liftPt 0 = (√κ)⁻¹ • u := by
    rw [← mulVec_mulVec, hBe, mulVec_smul]
  have hWc : ∀ k, |(P * B) k 2| ≤ C := by
    intro k
    have h1 : ((P * B) *ᵥ liftPt 0) k = (P * B) k 2 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, liftPt]
    rw [← h1, hWe, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.2 hsk)]
    exact mul_le_mul_of_nonneg_left (hule k) (inv_pos.2 hsk).le
  have hWb := hW.entry_le hWc
  have hPe : P = (P * B) * lorInv B := by rw [Matrix.mul_assoc, hB.mul_lorInv, Matrix.mul_one]
  have hPb : ∀ i j, |P i j| ≤ 3 * C * mB := fun i j => by
    rw [hPe]; exact entry_mul_le hWb hmB i j
  have hTe : castM T.val = L⁻¹ * P * L := by
    rw [hPdef]
    have h : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul _ hL
    calc castM T.val = (L⁻¹ * L) * castM T.val * (L⁻¹ * L) := by rw [h]; simp
      _ = L⁻¹ * (L * castM T.val * L⁻¹) * L := by simp only [Matrix.mul_assoc]
  have h1 : ∀ i j, |(L⁻¹ * P) i j| ≤ 3 * mLi * (3 * C * mB) := fun i j => entry_mul_le hmLi hPb i j
  have h2 := entry_mul_le h1 hmL i j
  have h3 : castM T.val i j = (T.val i j : ℝ) := rfl
  rw [← h3, hTe]
  exact h2

/-- Helper: Lemma 8.1 for $0 \le r < 1$. -/
theorem finite_actD_mem_ball' {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) {η : Fin 2 → ℝ} (hη : η ∈ disc) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    {T : GL (Fin 3) ℤ | T ∈ Siegel.AutPlus Q ∧
      (actD L (castM T.val) η) 0 ^ 2 + (actD L (castM T.val) η) 1 ^ 2 ≤ r ^ 2}.Finite := by
  obtain ⟨K, hK⟩ := entry_bound_of_ball hL hF hη hr0 hr
  exact (finite_gl_bounded K).subset fun T ⟨hT, hb⟩ => hK T (Siegel.mem_autPlus_iff.1 hT).1 hb

theorem zero_mem_disc : (0 : Fin 2 → ℝ) ∈ disc := by simp [disc]

/-- Helper: only finitely many $T \in O^+(f)$ have $d(0, T(0)) \le R$. -/
theorem finite_dist_le {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) (R : ℝ) :
    {T : GL (Fin 3) ℤ | T ∈ Siegel.AutPlus Q ∧ hypDist 0 (actD L (castM T.val) 0) ≤ R}.Finite := by
  obtain ⟨r, hr0, hr1, hr⟩ := exists_ball_of_hypDist_le R
  refine (finite_actD_mem_ball' hL hF zero_mem_disc hr0 hr1).subset fun T ⟨hT, hd⟩ => ⟨hT, ?_⟩
  exact hr _ (actD_mapsTo hL hF (Siegel.mem_autPlus_iff.1 hT).1 (Siegel.mem_autPlus_iff.1 hT).1
    zero_mem_disc).1 hd

/-- **Lemma 8.1** (Cassels, Ch. 13, §8, p. 313): let $f$ be integral and indefinite. For $\vec{\eta} \in \mathcal D$ and
$0 \le r < 1$ there are only finitely many $T \in O^+(f)$ with $T(\vec{\eta})$ in the disc $\xi_0^2 + \xi_1^2 \le r^2$
(Cassels: $< r^2$). $f$ need not be anisotropic. The radius $r \ge 0$ is implicit in Cassels and is a hypothesis
here (for $r \le -1$ the disc $\xi_0^2 + \xi_1^2 \le r^2$ would contain all of $\mathcal D$). -/
@[kb "cassels1978" "Ch. 13, §8, Lemma 8.1, p. 313"]
theorem finite_actD_mem_ball {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) {η : Fin 2 → ℝ} (hη : η ∈ disc) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    {T : GL (Fin 3) ℤ | T ∈ Siegel.AutPlus Q ∧
      (actD L (castM T.val) η) 0 ^ 2 + (actD L (castM T.val) η) 1 ^ 2 ≤ r ^ 2}.Finite :=
  finite_actD_mem_ball' hL hF hη hr0 hr

/-- **Lemma 8.3** (Cassels, Ch. 13, §8, p. 314): for $k > 0$ there is $d_2$, depending only on $k$ and $f$ (here: on $k$
and $L$), such that $d(0, U(0)) \le d_2$ for every real automorph $U$ of $f$ whose elements are at most $k$ in absolute
value. -/
@[kb "cassels1978" "Ch. 13, §8, Lemma 8.3, pp. 314–315"]
theorem exists_hypDist_le_of_bounded {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) (k : ℝ) : ∃ d₂ : ℝ, ∀ U : Matrix (Fin 3) (Fin 3) ℝ,
      Uᵀ * realMat Q * U = realMat Q → (∀ i j, |U i j| ≤ k) → hypDist 0 (actD L U 0) ≤ d₂ := by
  obtain ⟨mL, hmL0, hmL⟩ := exists_entry_bound L
  obtain ⟨mLi, hmLi0, hmLi⟩ := exists_entry_bound L⁻¹
  refine ⟨Real.arcosh (max (3 * (3 * mL * k) * mLi) 1), fun U hU hk => ?_⟩
  have hP : IsLor (L * U * L⁻¹) := isLor_conj hL hF hU
  have hPb : |(L * U * L⁻¹) 2 2| ≤ 3 * (3 * mL * k) * mLi := entry_mul_le (entry_mul_le hmL hk) hmLi 2 2
  have hpos : 0 < |(L * U * L⁻¹) 2 2| := by
    have r22 := hP.entry_eq 2 2
    simp [lorentz] at r22
    apply abs_pos.2
    intro h
    rw [h] at r22
    nlinarith [sq_nonneg ((L * U * L⁻¹) 0 2), sq_nonneg ((L * U * L⁻¹) 1 2)]
  unfold hypDist actD
  rw [coshDist_zero_flt_zero hP]
  exact (Real.arcosh_le_arcosh hpos (by positivity)).2 (hPb.trans (le_max_left _ _))

/-- Helper: the real matrix of a form with $F = L^{\mathsf T} f_0 L$, $L$ invertible, is nondegenerate. -/
theorem nondegenerate_of_hF {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) : Q.Nondegenerate := by
  intro h
  have h0 : (realMat Q).det = 0 := by
    have h1 : (Q.hessian.map (algebraMap ℤ ℝ)).det = algebraMap ℤ ℝ Q.hessian.det := by
      have := (algebraMap ℤ ℝ).map_det Q.hessian
      simpa [RingHom.mapMatrix_apply] using this.symm
    show ((1 / 2 : ℝ) • Q.hessian.map (algebraMap ℤ ℝ)).det = 0
    rw [Matrix.det_smul, h1, h]
    simp
  rw [hF, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h0
  have hl : lorentz.det = -1 := by simp [lorentz, Matrix.det_diagonal, Fin.prod_univ_three]
  rw [hl] at h0
  have : L.det * L.det = 0 := by linarith
  exact hL.ne_zero (mul_self_eq_zero.1 this)

theorem flt_neg (P : Matrix (Fin 3) (Fin 3) ℝ) (ξ : Fin 2 → ℝ) : flt (-P) ξ = flt P ξ := by
  unfold flt
  rw [Matrix.neg_mulVec, ← neg_one_smul ℝ (P *ᵥ liftPt ξ)]
  exact projPt_smul' (by norm_num) _

/-- Helper: every integral automorph agrees on $\mathcal D$ with one of determinant $1$ (namely $\pm$ itself). -/
theorem exists_autPlus_actD_eq {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} {W : GL (Fin 3) ℤ}
    (hW : W ∈ Siegel.Aut Q) :
    ∃ T ∈ Siegel.AutPlus Q, ∀ ξ, actD L (castM T.val) ξ = actD L (castM W.val) ξ := by
  have hdet : IsUnit W.val.det := (Matrix.isUnit_iff_isUnit_det _).1 W.isUnit
  rcases Int.isUnit_iff.1 hdet with h | h
  · exact ⟨W, Siegel.mem_autPlus_iff.2 ⟨hW, h⟩, fun _ => rfl⟩
  · have hc : castM (-W).val = -castM W.val := by
      ext i j; simp [castM]
    refine ⟨-W, Siegel.mem_autPlus_iff.2 ⟨?_, ?_⟩, fun ξ => ?_⟩
    · rw [mem_aut_iff_act] at hW ⊢
      unfold act at hW ⊢
      rw [hc]
      simpa [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg] using hW
    · simp [Matrix.det_neg, h]
    · unfold actD
      rw [hc, Matrix.mul_neg, Matrix.neg_mul, flt_neg]

/-- **Lemma 8.2** (Cassels, Ch. 13, §8, p. 314): let $f$ be anisotropic. There is $d_1$, depending only on $f$, such
that every $\vec{\xi} \in \mathcal D$ has $d(\vec{\xi}, T(0)) \le d_1$ for some $T \in O^+(f)$ (8.1). (From Theorem 2.2
and Lemma 8.3.) -/
@[kb "cassels1978" "Ch. 13, §8, Lemma 8.2, (8.1), p. 314"]
theorem exists_hypDist_orbit_le {Q : IntQF 3} (hQ : ¬ Q.IsotropicIn ℚ) {L : Matrix (Fin 3) (Fin 3) ℝ}
    (hL : IsUnit L.det) (hF : realMat Q = Lᵀ * lorentz * L) :
    ∃ d₁ : ℝ, ∀ ξ ∈ disc, ∃ T ∈ Siegel.AutPlus Q, hypDist ξ (actD L (castM T.val) 0) ≤ d₁ := by
  obtain ⟨k, hk⟩ := exists_aut_mul_bounded Q (nondegenerate_of_hF hL hF) hQ
  obtain ⟨d₂, hd₂⟩ := exists_hypDist_le_of_bounded hL hF k
  refine ⟨d₂, fun ξ hξ => ?_⟩
  obtain ⟨B, hB, hBe⟩ := exists_lorBoost hξ
  have hB0 := flt_zero_boost hξ hBe
  have hBi := hB.isLor_lorInv
  have hS : (L⁻¹ * B * L)ᵀ * realMat Q * (L⁻¹ * B * L) = realMat Q := automorph_of_lor hL hF hB
  have hSi : (L⁻¹ * lorInv B * L)ᵀ * realMat Q * (L⁻¹ * lorInv B * L) = realMat Q :=
    automorph_of_lor hL hF hBi
  have hSinv : (L⁻¹ * B * L)⁻¹ = L⁻¹ * lorInv B * L := by
    apply Matrix.inv_eq_right_inv
    calc L⁻¹ * B * L * (L⁻¹ * lorInv B * L) = L⁻¹ * B * (L * L⁻¹) * lorInv B * L := by
          simp only [Matrix.mul_assoc]
      _ = L⁻¹ * (B * lorInv B) * L := by
          rw [Matrix.mul_nonsing_inv _ hL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hB.mul_lorInv, Matrix.mul_one, Matrix.nonsing_inv_mul _ hL]
  obtain ⟨T, hT, W, hW, hTW⟩ := hk (L⁻¹ * B * L) hS
  rw [hSinv] at hTW
  have hWa : (castM W.val)ᵀ * realMat Q * castM W.val = realMat Q := (mem_aut_iff_act Q W).1 hW
  have hU : (L⁻¹ * lorInv B * L * castM W.val)ᵀ * realMat Q * (L⁻¹ * lorInv B * L * castM W.val) =
      realMat Q := by
    calc (L⁻¹ * lorInv B * L * castM W.val)ᵀ * realMat Q * (L⁻¹ * lorInv B * L * castM W.val)
        = (castM W.val)ᵀ * ((L⁻¹ * lorInv B * L)ᵀ * realMat Q * (L⁻¹ * lorInv B * L)) * castM W.val := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = realMat Q := by rw [hSi, hWa]
  have hd := hd₂ _ hU (fun i j => (hTW i j).2)
  obtain ⟨T', hT', hT'e⟩ := exists_autPlus_actD_eq (L := L) hW
  refine ⟨T', hT', ?_⟩
  have hPW := isLor_conj_aut hL hF hW
  have hζ : actD L (castM W.val) 0 ∈ disc := hPW.flt_mem_disc zero_mem_disc
  have hconj : L * (L⁻¹ * lorInv B * L) * L⁻¹ = lorInv B := by
    calc L * (L⁻¹ * lorInv B * L) * L⁻¹ = (L * L⁻¹) * lorInv B * (L * L⁻¹) := by simp only [Matrix.mul_assoc]
      _ = lorInv B := by rw [Matrix.mul_nonsing_inv _ hL]; simp
  have hact : actD L (L⁻¹ * lorInv B * L * castM W.val) 0 = flt (lorInv B) (actD L (castM W.val) 0) := by
    unfold actD
    rw [conj_mul_eq hL, hconj]
    exact flt_mul_of (hPW.last_ne zero_mem_disc)
  rw [hact] at hd
  rw [hT'e 0]
  have := hBi.hypDist_flt hξ hζ
  rw [← hB0, hB.flt_lorInv zero_mem_disc] at this
  rw [← hB0]
  rw [← this]
  exact hd

/-! ### The action of $O^+(f)$ and the metric -/

theorem actD_one {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det) (ξ : Fin 2 → ℝ) :
    actD L (castM (1 : GL (Fin 3) ℤ).val) ξ = ξ := by
  unfold actD
  rw [Units.val_one, castM_one, Matrix.mul_one, Matrix.mul_nonsing_inv _ hL, flt_one]

theorem aut_of_autPlus {Q : IntQF 3} {T : GL (Fin 3) ℤ} (hT : T ∈ Siegel.AutPlus Q) : T ∈ Siegel.Aut Q :=
  (Siegel.mem_autPlus_iff.1 hT).1

theorem actD_mem_disc {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) {T : GL (Fin 3) ℤ} (hT : T ∈ Siegel.AutPlus Q) {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ disc) : actD L (castM T.val) ξ ∈ disc :=
  (actD_mapsTo hL hF (aut_of_autPlus hT) (aut_of_autPlus hT) hξ).1

theorem actD_mul {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) {T T' : GL (Fin 3) ℤ} (hT : T ∈ Siegel.AutPlus Q)
    (hT' : T' ∈ Siegel.AutPlus Q) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ disc) :
    actD L (castM (T * T').val) ξ = actD L (castM T.val) (actD L (castM T'.val) ξ) :=
  (actD_mapsTo hL hF (aut_of_autPlus hT) (aut_of_autPlus hT') hξ).2

theorem actD_inv_actD {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) {T : GL (Fin 3) ℤ} (hT : T ∈ Siegel.AutPlus Q) {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ disc) : actD L (castM (T⁻¹).val) (actD L (castM T.val) ξ) = ξ := by
  rw [← actD_mul hL hF (inv_mem hT) hT hξ, inv_mul_cancel, actD_one hL]

theorem actD_actD_inv {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) {T : GL (Fin 3) ℤ} (hT : T ∈ Siegel.AutPlus Q) {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ disc) : actD L (castM T.val) (actD L (castM (T⁻¹).val) ξ) = ξ := by
  rw [← actD_mul hL hF hT (inv_mem hT) hξ, mul_inv_cancel, actD_one hL]

theorem hypDist_actD {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) {T : GL (Fin 3) ℤ} (hT : T ∈ Siegel.AutPlus Q) {ξ η : Fin 2 → ℝ}
    (hξ : ξ ∈ disc) (hη : η ∈ disc) :
    hypDist (actD L (castM T.val) ξ) (actD L (castM T.val) η) = hypDist ξ η :=
  (isLor_conj_aut hL hF (aut_of_autPlus hT)).hypDist_flt hξ hη

theorem hd_nonneg {ξ η : Fin 2 → ℝ} (hξ : ξ ∈ disc) (hη : η ∈ disc) : 0 ≤ hypDist ξ η :=
  (hypDist_metric.1 ξ hξ η hη).1

theorem hd_comm {ξ η : Fin 2 → ℝ} (hξ : ξ ∈ disc) (hη : η ∈ disc) : hypDist ξ η = hypDist η ξ :=
  (hypDist_metric.1 ξ hξ η hη).2.2

theorem hd_eq_zero {ξ η : Fin 2 → ℝ} (hξ : ξ ∈ disc) (hη : η ∈ disc) : hypDist ξ η = 0 ↔ ξ = η :=
  (hypDist_metric.1 ξ hξ η hη).2.1

theorem hd_triangle {ξ η ζ : Fin 2 → ℝ} (hξ : ξ ∈ disc) (hη : η ∈ disc) (hζ : ζ ∈ disc) :
    hypDist ξ ζ ≤ hypDist ξ η + hypDist η ζ :=
  hypDist_metric.2.1 ξ hξ η hη ζ hζ

theorem convex_disc : Convex ℝ disc := by
  intro x hx y hy a b ha hb hab
  have hx' : x 0 ^ 2 + x 1 ^ 2 < 1 := hx
  have hy' : y 0 ^ 2 + y 1 ^ 2 < 1 := hy
  show (a • x + b • y) 0 ^ 2 + (a • x + b • y) 1 ^ 2 < 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [mul_nonneg ha hb, sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1),
    mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x 0 - y 0)), mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x 1 - y 1)),
    mul_nonneg ha (sub_nonneg.2 (le_of_lt hx')), mul_nonneg hb (sub_nonneg.2 (le_of_lt hy'))]

/-- Helper: the nearest orbit point of $0$ to $\vec\xi$ exists. -/
theorem exists_nearest_orbit {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ disc) :
    ∃ T₀ ∈ Siegel.AutPlus Q, ∀ T ∈ Siegel.AutPlus Q,
      hypDist ξ (actD L (castM T₀.val) 0) ≤ hypDist ξ (actD L (castM T.val) 0) := by
  set ρ := hypDist ξ 0 with hρ
  have hfin := finite_dist_le hL hF (2 * ρ)
  have h1 : (1 : GL (Fin 3) ℤ) ∈ {T : GL (Fin 3) ℤ | T ∈ Siegel.AutPlus Q ∧
      hypDist 0 (actD L (castM T.val) 0) ≤ 2 * ρ} := by
    refine ⟨one_mem _, ?_⟩
    rw [actD_one hL, (hd_eq_zero zero_mem_disc zero_mem_disc).2 rfl]
    have := hd_nonneg hξ zero_mem_disc
    linarith
  obtain ⟨T₀, ⟨hT₀, hT₀d⟩, hmin⟩ := Set.exists_min_image _
    (fun T => hypDist ξ (actD L (castM T.val) 0)) hfin ⟨1, h1⟩
  refine ⟨T₀, hT₀, fun T hT => ?_⟩
  by_cases hTd : hypDist 0 (actD L (castM T.val) 0) ≤ 2 * ρ
  · exact hmin T ⟨hT, hTd⟩
  · push Not at hTd
    have hm1 := hmin 1 h1
    rw [actD_one hL] at hm1
    have htri := hd_triangle zero_mem_disc hξ (actD_mem_disc hL hF hT zero_mem_disc)
    rw [hd_comm zero_mem_disc hξ] at htri
    linarith

/-- Helper: the bisector of $0$ and $T(0)$. -/
theorem exists_halfplane {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) {T : GL (Fin 3) ℤ} (hT : T ∈ Siegel.AutPlus Q)
    (hne : actD L (castM T.val) 0 ≠ 0) :
    ∃ (a : Fin 2 → ℝ) (c : ℝ), a ≠ 0 ∧
      (∀ ζ ∈ disc, hypDist ζ 0 = hypDist ζ (actD L (castM T.val) 0) ↔ a ⬝ᵥ ζ = c) ∧
      (∀ ζ ∈ disc, hypDist ζ 0 ≤ hypDist ζ (actD L (castM T.val) 0) ↔ a ⬝ᵥ ζ ≤ c) :=
  exists_bisector zero_mem_disc (actD_mem_disc hL hF hT zero_mem_disc) hne.symm

/-- **The Dirichlet domain $\mathcal D_0$ with respect to $0$** (Cassels, Ch. 13, §8, (8.2)–(8.4), p. 315): the points
$\vec{\xi} \in \mathcal D$ with $d(\vec{\xi}, 0) \le d(\vec{\xi}, T(0))$ for all $T \in O^+(f)$. (Cassels writes it
$\mathscr D$; renamed here to avoid a clash with the disc.) -/
@[kb "cassels1978" "Ch. 13, §8, (8.2)–(8.4), p. 315 (the Dirichlet domain)"]
def dirichletDomain (Q : IntQF 3) (L : Matrix (Fin 3) (Fin 3) ℝ) : Set (Fin 2 → ℝ) :=
  {ξ | ξ ∈ disc ∧ ∀ T ∈ Siegel.AutPlus Q, hypDist ξ 0 ≤ hypDist ξ (actD L (castM T.val) 0)}

/-- Helper: a closed half-plane is convex. -/
theorem convex_halfspace (a : Fin 2 → ℝ) (c : ℝ) : Convex ℝ {x : Fin 2 → ℝ | a ⬝ᵥ x ≤ c} := by
  intro x hx y hy p q hp hq hpq
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have h := add_le_add (mul_le_mul_of_nonneg_left hx hp) (mul_le_mul_of_nonneg_left hy hq)
  have h2 : p * c + q * c = c := by rw [← add_mul, hpq, one_mul]
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
  linarith

/-- Helper: the half-planes (8.4) of all $T \in O^+(f)$ at once (for $T(0) = 0$ the inequality is trivial). -/
theorem exists_halfplane_all {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) :
    ∃ (a : GL (Fin 3) ℤ → Fin 2 → ℝ) (c : GL (Fin 3) ℤ → ℝ), ∀ T ∈ Siegel.AutPlus Q,
      (actD L (castM T.val) 0 ≠ 0 → a T ≠ 0) ∧
      ∀ ζ ∈ disc, (hypDist ζ 0 ≤ hypDist ζ (actD L (castM T.val) 0) ↔ a T ⬝ᵥ ζ ≤ c T) := by
  classical
  have key : ∀ T : GL (Fin 3) ℤ, ∃ (a : Fin 2 → ℝ) (c : ℝ), T ∈ Siegel.AutPlus Q →
      ((actD L (castM T.val) 0 ≠ 0 → a ≠ 0) ∧
      ∀ ζ ∈ disc, (hypDist ζ 0 ≤ hypDist ζ (actD L (castM T.val) 0) ↔ a ⬝ᵥ ζ ≤ c)) := by
    intro T
    by_cases hT : T ∈ Siegel.AutPlus Q
    · by_cases hne : actD L (castM T.val) 0 ≠ 0
      · obtain ⟨a, c, ha, -, hle⟩ := exists_halfplane hL hF hT hne
        exact ⟨a, c, fun _ => ⟨fun _ => ha, hle⟩⟩
      · push Not at hne
        refine ⟨0, 0, fun _ => ⟨fun h => absurd hne h, fun ζ hζ => ?_⟩⟩
        rw [hne]; simp
    · exact ⟨0, 0, fun h => absurd h hT⟩
  choose a c h using key
  exact ⟨a, c, h⟩

/-- Helper: the constant of a bisector half-plane is non-negative (the origin satisfies the inequality). -/
theorem halfplane_const_nonneg {a : Fin 2 → ℝ} {c : ℝ} {η : Fin 2 → ℝ} (hη : η ∈ disc)
    (h : ∀ ζ ∈ disc, (hypDist ζ 0 ≤ hypDist ζ η ↔ a ⬝ᵥ ζ ≤ c)) : 0 ≤ c := by
  have := (h 0 zero_mem_disc).1 (by
    rw [(hd_eq_zero zero_mem_disc zero_mem_disc).2 rfl]; exact hd_nonneg zero_mem_disc hη)
  simpa using this

/-- Helper: points of the Dirichlet domain are within $d_1$ of the origin. -/
theorem dirichlet_dist_le {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} {d₁ : ℝ}
    (hd₁ : ∀ ξ ∈ disc, ∃ T ∈ Siegel.AutPlus Q, hypDist ξ (actD L (castM T.val) 0) ≤ d₁)
    {ζ : Fin 2 → ℝ} (hζ : ζ ∈ dirichletDomain Q L) : hypDist 0 ζ ≤ d₁ := by
  obtain ⟨T, hT, hle⟩ := hd₁ ζ hζ.1
  have := hζ.2 T hT
  rw [hd_comm zero_mem_disc hζ.1]; linarith

/-- **(8.2)–(8.4)** (Cassels, Ch. 13, §8, p. 315), for integral indefinite $f$: the infimum
$\inf_{T} d(\vec{\xi}, T(0))$ is attained; $\mathcal D = \bigcup_T T(\mathcal D_0)$ (8.3); and $\mathcal D_0$ is convex and
relatively closed in $\mathcal D$. -/
@[kb "cassels1978" "Ch. 13, §8, (8.2)–(8.4), p. 315"]
theorem dirichletDomain_spec {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) :
    (∀ ξ ∈ disc, ∃ T₀ ∈ Siegel.AutPlus Q, ∀ T ∈ Siegel.AutPlus Q,
      hypDist ξ (actD L (castM T₀.val) 0) ≤ hypDist ξ (actD L (castM T.val) 0)) ∧
    disc = ⋃ T ∈ Siegel.AutPlus Q, actD L (castM T.val) '' dirichletDomain Q L ∧
    Convex ℝ (dirichletDomain Q L) ∧ ∃ C : Set (Fin 2 → ℝ), IsClosed C ∧ dirichletDomain Q L = C ∩ disc := by
  obtain ⟨a, c, h⟩ := exists_halfplane_all hL hF
  have hD : dirichletDomain Q L = (⋂ T ∈ Siegel.AutPlus Q, {ζ | a T ⬝ᵥ ζ ≤ c T}) ∩ disc := by
    ext ξ
    simp only [dirichletDomain, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hξ, hT⟩
      exact ⟨fun T hT' => ((h T hT').2 ξ hξ).1 (hT T hT'), hξ⟩
    · rintro ⟨hT, hξ⟩
      exact ⟨hξ, fun T hT' => ((h T hT').2 ξ hξ).2 (hT T hT')⟩
  refine ⟨fun ξ hξ => exists_nearest_orbit hL hF hξ, ?_, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro ξ hξ
      obtain ⟨T₀, hT₀, hmin⟩ := exists_nearest_orbit hL hF hξ
      have hζdisc : actD L (castM (T₀⁻¹).val) ξ ∈ disc := actD_mem_disc hL hF (inv_mem hT₀) hξ
      simp only [Set.mem_iUnion]
      refine ⟨T₀, hT₀, actD L (castM (T₀⁻¹).val) ξ, ⟨hζdisc, fun T hT => ?_⟩,
        actD_actD_inv hL hF hT₀ hξ⟩
      have e1 : hypDist (actD L (castM (T₀⁻¹).val) ξ) 0 = hypDist ξ (actD L (castM T₀.val) 0) := by
        rw [← hypDist_actD hL hF hT₀ hζdisc zero_mem_disc, actD_actD_inv hL hF hT₀ hξ]
      have e2 : hypDist (actD L (castM (T₀⁻¹).val) ξ) (actD L (castM T.val) 0) =
          hypDist ξ (actD L (castM (T₀ * T).val) 0) := by
        rw [← hypDist_actD hL hF hT₀ hζdisc (actD_mem_disc hL hF hT zero_mem_disc),
          actD_actD_inv hL hF hT₀ hξ, actD_mul hL hF hT₀ hT zero_mem_disc]
      rw [e1, e2]
      exact hmin _ (mul_mem hT₀ hT)
    · intro ξ hξ
      simp only [Set.mem_iUnion] at hξ
      obtain ⟨T, hT, x, hx, rfl⟩ := hξ
      exact actD_mem_disc hL hF hT hx.1
  · rw [hD]
    exact (convex_iInter fun T => convex_iInter fun _ => convex_halfspace _ _).inter convex_disc
  · refine ⟨⋂ T ∈ Siegel.AutPlus Q, {ζ | a T ⬝ᵥ ζ ≤ c T}, isClosed_biInter fun T _ => ?_, hD⟩
    refine isClosed_le ?_ continuous_const
    show Continuous fun ζ : Fin 2 → ℝ => ∑ i, a T i * ζ i
    fun_prop

/-- **Lemma 8.4** (Cassels, Ch. 13, §8, p. 315): let $f$ be anisotropic and let $d_1$ be as in Lemma 8.2. Then
$\mathcal D_0$ is defined by the inequalities (8.4) taken over the $T$ with $d(0, T(0)) \le 2d_1$ (8.5). -/
@[kb "cassels1978" "Ch. 13, §8, Lemma 8.4, (8.5)–(8.9), p. 315"]
theorem dirichletDomain_eq_finite {Q : IntQF 3} (hQ : ¬ Q.IsotropicIn ℚ) {L : Matrix (Fin 3) (Fin 3) ℝ}
    (hL : IsUnit L.det) (hF : realMat Q = Lᵀ * lorentz * L) {d₁ : ℝ}
    (hd₁ : ∀ ξ ∈ disc, ∃ T ∈ Siegel.AutPlus Q, hypDist ξ (actD L (castM T.val) 0) ≤ d₁) :
    dirichletDomain Q L = {ξ | ξ ∈ disc ∧ ∀ T ∈ Siegel.AutPlus Q, hypDist 0 (actD L (castM T.val) 0) ≤ 2 * d₁ →
      hypDist ξ 0 ≤ hypDist ξ (actD L (castM T.val) 0)} := by
  apply Set.Subset.antisymm
  · intro ξ hξ
    exact ⟨hξ.1, fun T hT _ => hξ.2 T hT⟩
  intro ξ hξ
  obtain ⟨a, c, h⟩ := exists_halfplane_all hL hF
  have hd0 : 0 ≤ d₁ := by
    obtain ⟨T, hT, hle⟩ := hd₁ 0 zero_mem_disc
    exact (hd_nonneg zero_mem_disc (actD_mem_disc hL hF hT zero_mem_disc)).trans hle
  obtain ⟨δ, hδ0, hδ1, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ T ∈ Siegel.AutPlus Q,
      2 * d₁ < hypDist 0 (actD L (castM T.val) 0) →
        2 * d₁ + 2 * δ ≤ hypDist 0 (actD L (castM T.val) 0) := by
    have hfin := finite_dist_le hL hF (2 * d₁ + 2)
    have hS'fin : {T : GL (Fin 3) ℤ | T ∈ Siegel.AutPlus Q ∧
        hypDist 0 (actD L (castM T.val) 0) ≤ 2 * d₁ + 2 ∧
        2 * d₁ < hypDist 0 (actD L (castM T.val) 0)}.Finite :=
      hfin.subset fun T ⟨h1, h2, _⟩ => ⟨h1, h2⟩
    by_cases hne : {T : GL (Fin 3) ℤ | T ∈ Siegel.AutPlus Q ∧
        hypDist 0 (actD L (castM T.val) 0) ≤ 2 * d₁ + 2 ∧
        2 * d₁ < hypDist 0 (actD L (castM T.val) 0)}.Nonempty
    · obtain ⟨Tm, ⟨hTm, hTm1, hTm2⟩, hmin⟩ := Set.exists_min_image _
        (fun T : GL (Fin 3) ℤ => hypDist 0 (actD L (castM T.val) 0)) hS'fin hne
      refine ⟨min 1 ((hypDist 0 (actD L (castM Tm.val) 0) - 2 * d₁) / 2),
        lt_min one_pos (by linarith), min_le_left _ _, fun T hT hlt => ?_⟩
      have hm := min_le_right 1 ((hypDist 0 (actD L (castM Tm.val) 0) - 2 * d₁) / 2)
      have hm1 := min_le_left 1 ((hypDist 0 (actD L (castM Tm.val) 0) - 2 * d₁) / 2)
      by_cases hle : hypDist 0 (actD L (castM T.val) 0) ≤ 2 * d₁ + 2
      · have h1 : hypDist 0 (actD L (castM Tm.val) 0) ≤ hypDist 0 (actD L (castM T.val) 0) :=
          hmin T ⟨hT, hle, hlt⟩
        linarith
      · push Not at hle
        linarith
    · refine ⟨1, one_pos, le_rfl, fun T hT hlt => ?_⟩
      by_contra hcon
      push Not at hcon
      exact hne ⟨T, hT, by linarith, hlt⟩
  have hA : ∀ ζ ∈ disc, (∀ T ∈ Siegel.AutPlus Q, hypDist 0 (actD L (castM T.val) 0) ≤ 2 * d₁ →
      hypDist ζ 0 ≤ hypDist ζ (actD L (castM T.val) 0)) → hypDist 0 ζ ≤ d₁ + δ →
      ζ ∈ dirichletDomain Q L := by
    intro ζ hζ hR hz
    refine ⟨hζ, fun T hT => ?_⟩
    by_cases hle : hypDist 0 (actD L (castM T.val) 0) ≤ 2 * d₁
    · exact hR T hT hle
    · push Not at hle
      have h2 := hδ T hT hle
      have htri := hd_triangle zero_mem_disc hζ (actD_mem_disc hL hF hT zero_mem_disc)
      rw [hd_comm hζ zero_mem_disc]
      linarith
  have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (t • ξ) ∈ disc ∧ ∀ T ∈ Siegel.AutPlus Q,
      hypDist 0 (actD L (castM T.val) 0) ≤ 2 * d₁ →
      hypDist (t • ξ) 0 ≤ hypDist (t • ξ) (actD L (castM T.val) 0) := by
    intro t ht0 ht1
    have hdisc : t • ξ ∈ disc := by
      have := convex_disc zero_mem_disc hξ.1 (a := 1 - t) (b := t) (by linarith) ht0 (by ring)
      simpa using this
    refine ⟨hdisc, fun T hT hle => ?_⟩
    rw [(h T hT).2 _ hdisc]
    have h1 := ((h T hT).2 ξ hξ.1).1 (hξ.2 T hT hle)
    have hc := halfplane_const_nonneg (actD_mem_disc hL hF hT zero_mem_disc) (h T hT).2
    rw [dotProduct_smul, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1 ht0, mul_le_mul_of_nonneg_right ht1 hc]
  have hgform : ∀ t : ℝ, hypDist 0 (t • ξ) =
      Real.arcosh (1 / √(1 - (t * ξ 0) ^ 2 - (t * ξ 1) ^ 2)) := by
    intro t
    simp [hypDist, coshDist_zero_left]
  have hcont : ContinuousOn (fun t : ℝ => hypDist 0 (t • ξ)) (Set.Icc 0 1) := by
    simp only [hgform]
    refine Real.continuousOn_arcosh.comp (f := fun t : ℝ => 1 / √(1 - (t * ξ 0) ^ 2 - (t * ξ 1) ^ 2)) ?_ ?_
    · refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
      intro t ht
      have := disc_u_pos (hseg t ht.1 ht.2).1
      simp only [Pi.smul_apply, smul_eq_mul] at this
      exact (Real.sqrt_pos.2 this).ne'
    · intro t ht
      have := one_le_coshDist_zero (hseg t ht.1 ht.2).1
      rw [coshDist_zero_left] at this
      simp only [Pi.smul_apply, smul_eq_mul] at this
      exact Set.mem_Ici.2 this
  by_cases hg1 : hypDist 0 ξ ≤ d₁ + δ
  · exact hA ξ hξ.1 hξ.2 hg1
  · push Not at hg1
    have hg0 : hypDist 0 ((0 : ℝ) • ξ) = 0 := by
      rw [zero_smul]; exact (hd_eq_zero zero_mem_disc zero_mem_disc).2 rfl
    have hmem : d₁ + δ ∈ Set.Icc (hypDist 0 ((0 : ℝ) • ξ)) (hypDist 0 ((1 : ℝ) • ξ)) := by
      rw [hg0, one_smul]; exact ⟨by linarith, hg1.le⟩
    obtain ⟨t, ht, hte⟩ := intermediate_value_Icc zero_le_one hcont hmem
    obtain ⟨hd, hR⟩ := hseg t ht.1 ht.2
    have hte' : hypDist 0 (t • ξ) = d₁ + δ := hte
    have hD := hA _ hd hR hte'.le
    have := dirichlet_dist_le hd₁ hD
    linarith

/-- **Lemma 8.4, Corollary** (Cassels, Ch. 13, §8, p. 315): for anisotropic $f$, $\mathcal D_0$ is a closed polygon
whose vertices all lie in $\mathcal D$: the convex hull of finitely many points of $\mathcal D$. -/
@[kb "cassels1978" "Ch. 13, §8, Lemma 8.4, Cor., pp. 315–316"]
theorem dirichletDomain_eq_convexHull {Q : IntQF 3} (hQ : ¬ Q.IsotropicIn ℚ) {L : Matrix (Fin 3) (Fin 3) ℝ}
    (hL : IsUnit L.det) (hF : realMat Q = Lᵀ * lorentz * L) :
    ∃ V : Finset (Fin 2 → ℝ), (∀ v ∈ V, v ∈ disc) ∧ dirichletDomain Q L = convexHull ℝ (V : Set (Fin 2 → ℝ)) := by
  classical
  obtain ⟨d₁, hd₁⟩ := exists_hypDist_orbit_le hQ hL hF
  have hDe := dirichletDomain_eq_finite hQ hL hF hd₁
  obtain ⟨a, c, h⟩ := exists_halfplane_all hL hF
  have hfin : {T : GL (Fin 3) ℤ | T ∈ Siegel.AutPlus Q ∧ hypDist 0 (actD L (castM T.val) 0) ≤ 2 * d₁ ∧
      actD L (castM T.val) 0 ≠ 0}.Finite :=
    (finite_dist_le hL hF (2 * d₁)).subset fun T ⟨h1, h2, _⟩ => ⟨h1, h2⟩
  set s := hfin.toFinset with hs
  set H : Set (Fin 2 → ℝ) := {x | ∀ i ∈ s, a i ⬝ᵥ x ≤ c i} with hH
  have hDH : dirichletDomain Q L = H ∩ disc := by
    rw [hDe]
    ext ξ
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨hξ, hT⟩
      refine ⟨fun i hi => ?_, hξ⟩
      have hi' := hfin.mem_toFinset.1 hi
      exact ((h i hi'.1).2 ξ hξ).1 (hT i hi'.1 hi'.2.1)
    · rintro ⟨hH', hξ⟩
      refine ⟨hξ, fun T hT hle => ?_⟩
      by_cases hz : actD L (castM T.val) 0 = 0
      · rw [hz]
      · exact ((h T hT).2 ξ hξ).2 (hH' T (hfin.mem_toFinset.2 ⟨hT, hle, hz⟩))
  have hHc : ∀ i ∈ s, 0 ≤ c i := fun i hi =>
    halfplane_const_nonneg (actD_mem_disc hL hF (hfin.mem_toFinset.1 hi).1 zero_mem_disc)
      (h i (hfin.mem_toFinset.1 hi).1).2
  have hH0 : (0 : Fin 2 → ℝ) ∈ H := fun i hi => by simpa using hHc i hi
  have hHconv : Convex ℝ H := by
    have : H = ⋂ i ∈ s, {x | a i ⬝ᵥ x ≤ c i} := by ext; simp [hH]
    rw [this]
    exact convex_iInter fun i => convex_iInter fun _ => convex_halfspace _ _
  obtain ⟨r, hr0, hr1, hr⟩ := exists_ball_of_hypDist_le d₁
  have hDball : ∀ x ∈ dirichletDomain Q L, x 0 ^ 2 + x 1 ^ 2 ≤ r ^ 2 := fun x hx =>
    hr x hx.1 (dirichlet_dist_le hd₁ hx)
  have hHball : ∀ x ∈ H, x 0 ^ 2 + x 1 ^ 2 ≤ r ^ 2 := by
    intro x hx
    by_contra hcon
    push Not at hcon
    obtain ⟨N, hN⟩ : ∃ N, N = x 0 ^ 2 + x 1 ^ 2 := ⟨_, rfl⟩
    rw [← hN] at hcon
    by_cases hN1 : N < 1
    · have : x ∈ dirichletDomain Q L := by
        rw [hDH]; exact ⟨hx, by show x 0 ^ 2 + x 1 ^ 2 < 1; linarith⟩
      have := hDball x this
      linarith
    · push Not at hN1
      obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (r + 1) / 2 := ⟨_, rfl⟩
      have hm0 : r < m := by rw [hm]; linarith
      have hm1 : m < 1 := by rw [hm]; linarith
      have hsN : 1 ≤ √N := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hN1
      have hsp : 0 < √N := by linarith
      obtain ⟨t, ht⟩ : ∃ t : ℝ, t = m / √N := ⟨_, rfl⟩
      have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg (by linarith) hsp.le
      have ht1 : t ≤ 1 := by rw [ht, div_le_one hsp]; linarith
      have hy : t • x ∈ H := by
        have := hHconv hH0 hx (a := 1 - t) (b := t) (by linarith) ht0 (by ring)
        simpa using this
      have hyN : (t • x) 0 ^ 2 + (t • x) 1 ^ 2 = m ^ 2 := by
        simp only [Pi.smul_apply, smul_eq_mul]
        have : (t * x 0) ^ 2 + (t * x 1) ^ 2 = t ^ 2 * N := by rw [hN]; ring
        rw [this, ht, div_pow, Real.sq_sqrt (by linarith)]
        field_simp
      have hyd : t • x ∈ dirichletDomain Q L := by
        rw [hDH]
        exact ⟨hy, by show (t • x) 0 ^ 2 + (t • x) 1 ^ 2 < 1; rw [hyN]; nlinarith⟩
      have := hDball _ hyd
      rw [hyN] at this
      nlinarith
  have hbd : ∀ x ∈ H, ‖x‖ ≤ 1 := by
    intro x hx
    have hb := hHball x hx
    rw [pi_norm_le_iff_of_nonneg zero_le_one, Fin.forall_fin_two]
    constructor <;> rw [Real.norm_eq_abs, ← sq_le_one_iff_abs_le_one] <;>
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  obtain ⟨V, hV⟩ := exists_finset_convexHull_of_halfplanes s a c
    (fun i hi => (h i (hfin.mem_toFinset.1 hi).1).1 (hfin.mem_toFinset.1 hi).2.2) 1 hbd
  have hV' : H = convexHull ℝ (V : Set (Fin 2 → ℝ)) := hV
  have hHdisc : ∀ x ∈ H, x ∈ disc := fun x hx =>
    show x 0 ^ 2 + x 1 ^ 2 < 1 from lt_of_le_of_lt (hHball x hx) (by nlinarith)
  refine ⟨V, fun v hv => hHdisc v ?_, ?_⟩
  · rw [hV']; exact subset_convexHull ℝ _ hv
  · rw [hDH, ← hV']
    exact Set.inter_eq_left.2 fun x hx => hHdisc x hx

/-- **Theorem 6.1, Corollary** (Cassels, Ch. 13, §6, (6.12)–(6.13), p. 305): the polygon $\mathcal P$ lies in a disc
$\xi_0^2 + \xi_1^2 \le r^2$ with $r < 1$ (any convex polygon with vertices in $\mathcal D$ does; Cassels notes that this
is false for every isotropic form, whose fundamental polygons have vertices on the boundary). (The displays (6.12),
(6.13) are lost in the machine-read text.) -/
@[kb "cassels1978" "Ch. 13, §6, Thm. 6.1, Cor., (6.12)–(6.13), p. 305"]
theorem convexHull_subset_ball {V : Finset (Fin 2 → ℝ)} (hV : ∀ v ∈ V, v ∈ disc) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ ξ ∈ convexHull ℝ (V : Set (Fin 2 → ℝ)), ξ 0 ^ 2 + ξ 1 ^ 2 ≤ r ^ 2 := by
  classical
  by_cases hne : V.Nonempty
  · obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image V (fun ξ : Fin 2 → ℝ => ξ 0 ^ 2 + ξ 1 ^ 2) hne
    have hvd : v 0 ^ 2 + v 1 ^ 2 < 1 := hV v hv
    have hnn : 0 ≤ v 0 ^ 2 + v 1 ^ 2 := by positivity
    refine ⟨√(v 0 ^ 2 + v 1 ^ 2), Real.sqrt_nonneg _, ?_, fun ξ hξ => ?_⟩
    · rw [Real.sqrt_lt' one_pos, one_pow]; exact hvd
    · rw [Real.sq_sqrt hnn]
      have hconv : Convex ℝ {ξ : Fin 2 → ℝ | ξ 0 ^ 2 + ξ 1 ^ 2 ≤ v 0 ^ 2 + v 1 ^ 2} := by
        intro x hx y hy p q hp hq hpq
        simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
        have hq' : q = 1 - p := by linarith
        subst hq'
        nlinarith [mul_nonneg hp hq, mul_nonneg (mul_nonneg hp hq) (sq_nonneg (x 0 - y 0)),
          mul_nonneg (mul_nonneg hp hq) (sq_nonneg (x 1 - y 1)),
          mul_le_mul_of_nonneg_left hx hp, mul_le_mul_of_nonneg_left hy hq]
      exact convexHull_min (fun w hw => hmax w hw) hconv hξ
  · refine ⟨0, le_rfl, one_pos, fun ξ hξ => ?_⟩
    rw [Finset.not_nonempty_iff_eq_empty.1 hne] at hξ
    simp at hξ

end QuadFormsKB.Reduction
