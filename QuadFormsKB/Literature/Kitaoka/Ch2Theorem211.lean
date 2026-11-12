/-
# Kitaoka 1993, Section 2.1: Theorem 2.1.1 from Lemma 2.1.3

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §2.1, Theorem 2.1.1, p. 36.

**Proves**
* `theorem211` (Theorem 2.1.1, **proved**): `theorem211_of_lemma213` applied to `lemma213` (`Ch2Lemma213.lean`);
  and `hermiteConst_le`: Hermite's constant satisfies $\mu_m \le (4/3)^{(m-1)/2}$ for $m \ge 2$.
* `theorem211_of_lemma213`: `Lemma213` implies `Theorem211`.
  (i) Write $p = {}^t g\,g$ with $g \in \mathrm{GL}_m(\mathbb R)$ (spectral theorem,
  `exists_GL_eq_transpose_mul_self`). Lemma 2.1.3 gives $\gamma_0$ with $g\gamma_0 = k a n$,
  $a = \mathrm{diag}(\alpha) \in A_{2/\sqrt3}$, $n \in N_{1/2}$, so
  ${}^t\gamma_0\,p\,\gamma_0 = {}^t n\,\mathrm{diag}(\alpha_i^2)\,n \in S_{4/3,1/2}$ (as
  $\alpha_i^2/\alpha_{i+1}^2 \le 4/3$), and $\gamma = \gamma_0^{-1}$.
  (ii) For $p = {}^t\gamma\,({}^t n\,a\,n)\,\gamma$ with $a = \mathrm{diag}(\alpha) \in A_{4/3}$, put
  $x = \gamma^{-1} e_0 \in \mathbb Z^m$; then $p[x] = \alpha_0$, so $\min p \le \alpha_0$. Also
  $\det p = \prod_i \alpha_i \ge \alpha_0^m (3/4)^{m(m-1)/2}$ because $\alpha_{i+1} \ge \tfrac34 \alpha_i$,
  whence $\alpha_0 \le (4/3)^{(m-1)/2} (\det p)^{1/m}$.
-/
import QuadFormsKB.Literature.Kitaoka.Ch2ReductionProofs
import QuadFormsKB.Literature.Kitaoka.Ch2Lemma213
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Matrix

noncomputable section

namespace QuadFormsKB.Kitaoka.Reduction

/-- A positive definite real matrix is ${}^t g\,g$ for some $g \in \mathrm{GL}_m(\mathbb R)$ (spectral theorem). -/
theorem exists_GL_eq_transpose_mul_self {m : ℕ} (p : Matrix (Fin m) (Fin m) ℝ) (hp : p.PosDef) :
    ∃ g : GL (Fin m) ℝ, p = (g : Matrix (Fin m) (Fin m) ℝ)ᵀ * (g : Matrix (Fin m) (Fin m) ℝ) := by
  classical
  set U : Matrix (Fin m) (Fin m) ℝ := (hp.1.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) with hUdef
  set lam := hp.1.eigenvalues with hlamdef
  have hlam : ∀ i, 0 < lam i := hp.eigenvalues_pos
  have hpeq : p = U * diagonal lam * star U := by
    conv_lhs => rw [hp.1.spectral_theorem]
    simp [hUdef, hlamdef]
  set C : Matrix (Fin m) (Fin m) ℝ := diagonal (fun i => Real.sqrt (lam i)) * star U with hCdef
  have hstarU : (star U)ᴴ = U := by simp [Matrix.star_eq_conjTranspose]
  have hCA : Cᴴ * C = p := by
    rw [hpeq, hCdef, conjTranspose_mul, hstarU, diagonal_conjTranspose]
    have hd : star (fun i => Real.sqrt (lam i)) = fun i => Real.sqrt (lam i) := by
      ext i; simp
    rw [hd]
    have hsq : diagonal (fun i => Real.sqrt (lam i)) * diagonal (fun i => Real.sqrt (lam i)) = diagonal lam := by
      rw [diagonal_mul_diagonal]
      congr 1; ext i
      exact Real.mul_self_sqrt (hlam i).le
    calc U * diagonal (fun i => Real.sqrt (lam i)) * (diagonal (fun i => Real.sqrt (lam i)) * star U)
        = U * (diagonal (fun i => Real.sqrt (lam i)) * diagonal (fun i => Real.sqrt (lam i))) * star U := by
          simp only [Matrix.mul_assoc]
      _ = U * diagonal lam * star U := by rw [hsq]
  have hCdet : C.det ≠ 0 := by
    intro h0
    have h1 : p.det = 0 := by rw [← hCA, det_mul, h0, mul_zero]
    exact (hp.det_pos).ne' h1
  refine ⟨Matrix.nonsingInvUnit C (Ne.isUnit hCdet), ?_⟩
  rw [← hCA, Matrix.conjTranspose_eq_transpose_of_trivial]
  rfl

/-- Quadratic form transformation rule: $v \cdot ({}^t B\,M\,B) v = (Bv) \cdot M (Bv)$. -/
theorem dot_conj_mulVec {m : ℕ} (B M : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → ℝ) :
    v ⬝ᵥ ((Bᵀ * M * B) *ᵥ v) = (B *ᵥ v) ⬝ᵥ (M *ᵥ (B *ᵥ v)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- Part (i) of Theorem 2.1.1 from Lemma 2.1.3. -/
theorem theorem211_partOne_of_lemma213 (h : Lemma213) {m : ℕ} (hm : 2 ≤ m) (p : Matrix (Fin m) (Fin m) ℝ)
    (hp : p.PosDef) :
    ∃ γ : GL (Fin m) ℤ, ∃ s ∈ siegelDomain m (4 / 3) (1 / 2), p = (intCast γ)ᵀ * s * intCast γ := by
  obtain ⟨g, hg⟩ := exists_GL_eq_transpose_mul_self p hp
  obtain ⟨γ₀, -, k, hk, a, ha, n, hn, hkan⟩ := h m hm g
  obtain ⟨α, hα, hαr, rfl⟩ := ha
  have hk' : kᵀ * k = 1 := by
    have := (Matrix.mem_orthogonalGroup_iff' (Fin m) ℝ).mp hk
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  set s : Matrix (Fin m) (Fin m) ℝ := nᵀ * diagonal (fun i => α i * α i) * n with hs
  have hGs : (intCast γ₀)ᵀ * p * (intCast γ₀) = s := by
    have e1 : (intCast γ₀)ᵀ * p * (intCast γ₀) =
        ((g : Matrix (Fin m) (Fin m) ℝ) * (intCast γ₀))ᵀ * ((g : Matrix (Fin m) (Fin m) ℝ) * (intCast γ₀)) := by
      rw [hg]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e1, hkan, hs]
    simp only [Matrix.transpose_mul, Matrix.diagonal_transpose]
    have : nᵀ * (diagonal α * (kᵀ * k) * diagonal α) * n = nᵀ * diagonal (fun i => α i * α i) * n := by
      rw [hk', Matrix.mul_one, diagonal_mul_diagonal]
    rw [← this]
    simp only [Matrix.mul_assoc]
  refine ⟨γ₀⁻¹, s, ⟨diagonal (fun i => α i * α i),
    ⟨fun i => α i * α i, fun i => mul_pos (hα i) (hα i), ?_, rfl⟩, n, hn, rfl⟩, ?_⟩
  · intro i j hij
    have h1 := hαr i j hij
    have hpos := hα j
    have hpi := hα i
    have : α i * α i / (α j * α j) = (α i / α j) ^ 2 := by field_simp
    rw [this]
    have h0 : 0 ≤ α i / α j := (div_pos hpi hpos).le
    have h2 : (2 / Real.sqrt 3) ^ 2 = 4 / 3 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
    calc (α i / α j) ^ 2 ≤ (2 / Real.sqrt 3) ^ 2 := by gcongr
      _ = 4 / 3 := h2
  · have hinv : intCast (γ₀⁻¹) * (intCast γ₀) = 1 := by
      have : ((γ₀⁻¹ : GL (Fin m) ℤ) : Matrix (Fin m) (Fin m) ℤ) * (γ₀ : Matrix (Fin m) (Fin m) ℤ) = 1 :=
        Units.inv_mul γ₀
      have h2 := congrArg (fun M : Matrix (Fin m) (Fin m) ℤ => M.map (Int.cast : ℤ → ℝ)) this
      simpa only [intCast, map_cast_mul', map_cast_one'] using h2
    have hinv' : (intCast γ₀) * intCast (γ₀⁻¹) = 1 := by
      have : (γ₀ : Matrix (Fin m) (Fin m) ℤ) * ((γ₀⁻¹ : GL (Fin m) ℤ) : Matrix (Fin m) (Fin m) ℤ) = 1 :=
        Units.mul_inv γ₀
      have h2 := congrArg (fun M : Matrix (Fin m) (Fin m) ℤ => M.map (Int.cast : ℤ → ℝ)) this
      simpa only [intCast, map_cast_mul', map_cast_one'] using h2
    rw [← hGs]
    calc p = ((intCast γ₀) * intCast (γ₀⁻¹))ᵀ * p * ((intCast γ₀) * intCast (γ₀⁻¹)) := by rw [hinv']; simp
      _ = _ := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]

/-- Part (ii) of Theorem 2.1.1, once $p = {}^t\gamma\,({}^t n\,a\,n)\,\gamma$. -/
theorem theorem211_partTwo_aux {m : ℕ} (hm : 2 ≤ m) (p : Matrix (Fin m) (Fin m) ℝ) (hp : p.PosDef)
    (γ : GL (Fin m) ℤ) (α : Fin m → ℝ) (hα : ∀ i, 0 < α i)
    (hαr : ∀ i j : Fin m, j.val = i.val + 1 → α i / α j ≤ 4 / 3)
    (n : Matrix (Fin m) (Fin m) ℝ) (hn : n ∈ unitri m)
    (hpeq : p = (intCast γ)ᵀ * (nᵀ * diagonal α * n) * intCast γ) :
    latMin p ≤ (4 / 3 : ℝ) ^ (((m : ℝ) - 1) / 2) * p.det ^ ((1 : ℝ) / m) := by
  have hmpos : 0 < m := by omega
  let i0 : Fin m := ⟨0, hmpos⟩
  have hΓX : intCast γ * intCast (γ⁻¹) = 1 := by
    have : (γ : Matrix (Fin m) (Fin m) ℤ) * ((γ⁻¹ : GL (Fin m) ℤ) : Matrix (Fin m) (Fin m) ℤ) = 1 :=
      Units.mul_inv γ
    have h2 := congrArg (fun M : Matrix (Fin m) (Fin m) ℤ => M.map (Int.cast : ℤ → ℝ)) this
    simpa only [intCast, map_cast_mul', map_cast_one'] using h2
  set Γ := intCast γ with hΓ
  set X := intCast (γ⁻¹) with hX
  let xz : Fin m → ℤ := fun i => ((γ⁻¹ : GL (Fin m) ℤ) : Matrix (Fin m) (Fin m) ℤ) i i0
  have hxz : xz ≠ 0 := by
    intro h0
    have hinv : ((γ⁻¹ : GL (Fin m) ℤ) : Matrix (Fin m) (Fin m) ℤ) *ᵥ (Pi.single i0 1) = 0 := by
      ext i; simpa [Matrix.mulVec_single_one, xz] using congrFun h0 i
    have h3 : (Pi.single i0 (1 : ℤ) : Fin m → ℤ) = 0 := by
      have := congrArg (fun v => ((γ : Matrix (Fin m) (Fin m) ℤ)) *ᵥ v) hinv
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
      have h4 : (γ : Matrix (Fin m) (Fin m) ℤ) * ((γ⁻¹ : GL (Fin m) ℤ) : Matrix (Fin m) (Fin m) ℤ) = 1 :=
        Units.mul_inv γ
      rwa [h4, Matrix.one_mulVec] at this
    have := congrFun h3 i0
    simp at this
  set xr : Fin m → ℝ := fun i => (xz i : ℝ) with hxr
  have hxrX : xr = X *ᵥ Pi.single i0 1 := by
    ext i; simp [xr, xz, hX, intCast]
  have hΓx : Γ *ᵥ xr = Pi.single i0 1 := by
    rw [hxrX, Matrix.mulVec_mulVec, hΓX, Matrix.one_mulVec]
  -- n e = e
  have hne : n *ᵥ (Pi.single i0 1 : Fin m → ℝ) = Pi.single i0 1 := by
    ext i
    rw [Matrix.mulVec_single_one]
    simp only [Matrix.col_apply]
    by_cases hi : i = i0
    · subst hi; exact hn.2 _ |>.trans (by simp)
    · have : n i i0 = 0 := by
        apply hn.1
        rcases lt_or_gt_of_ne hi with h | h
        · exact absurd h (by simp [i0, Fin.lt_def])
        · exact h
      simp [this, hi]
  have hval : xr ⬝ᵥ (p *ᵥ xr) = α i0 := by
    rw [hpeq, dot_conj_mulVec, hΓx, dot_conj_mulVec, hne]
    simp
  -- latMin p ≤ α i0
  have hle : latMin p ≤ α i0 := by
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro r ⟨x, hx, rfl⟩
      have hx' : (fun i => (x i : ℝ)) ≠ 0 := by
        intro h0; apply hx; ext i; simpa using congrFun h0 i
      exact (hp.dotProduct_mulVec_pos hx').le
    · exact ⟨xz, hxz, hval.symm⟩
  -- determinant
  have hdetn : n.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hn.1]; simp [hn.2]
  have hdetΓ : Γ.det = ((γ : Matrix (Fin m) (Fin m) ℤ).det : ℝ) := by
    simpa [Γ, intCast] using ((Int.castRingHom ℝ).map_det (γ : Matrix (Fin m) (Fin m) ℤ)).symm
  have hdetsq : Γ.det * Γ.det = 1 := by
    have hu : IsUnit (γ : Matrix (Fin m) (Fin m) ℤ).det := (Matrix.isUnit_iff_isUnit_det _).mp γ.isUnit
    rw [hdetΓ]
    rcases Int.isUnit_iff.mp hu with h1 | h1 <;> rw [h1] <;> norm_num
  have hdet : p.det = ∏ i, α i := by
    rw [hpeq, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      Matrix.det_transpose, hdetn, Matrix.det_diagonal]
    calc Γ.det * ((1 * ∏ i, α i) * 1) * Γ.det = (Γ.det * Γ.det) * ∏ i, α i := by ring
      _ = _ := by rw [hdetsq, one_mul]
  -- α i ≥ α i0 (3/4)^i
  have hchain : ∀ i : ℕ, ∀ hi : i < m, α i0 * (3 / 4 : ℝ) ^ i ≤ α ⟨i, hi⟩ := by
    intro i
    induction i with
    | zero => intro hi; simp [i0]
    | succ k ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := hαr ⟨k, by omega⟩ ⟨k + 1, hi⟩ rfl
      have hp2 := hα ⟨k + 1, hi⟩
      rw [div_le_iff₀ hp2] at h2
      calc α i0 * (3 / 4 : ℝ) ^ (k + 1) = (α i0 * (3 / 4) ^ k) * (3 / 4) := by ring
        _ ≤ α ⟨k, by omega⟩ * (3 / 4) := by gcongr
        _ ≤ α ⟨k + 1, hi⟩ := by linarith
  have hprod : ∏ i : Fin m, (α i0 * (3 / 4 : ℝ) ^ i.val) ≤ ∏ i, α i :=
    Finset.prod_le_prod₀ (fun i _ => by have := hα i0; positivity) (fun i _ => hchain i.val i.isLt)
  set S : ℕ := ∑ i : Fin m, i.val with hS
  have hS2 : (S : ℝ) * 2 = (m : ℝ) * ((m : ℝ) - 1) := by
    have h := Finset.sum_range_id_mul_two m
    have h' : S = ∑ i ∈ Finset.range m, i := Fin.sum_univ_eq_sum_range (fun i => i) m
    rw [h']
    have hc : ((∑ i ∈ Finset.range m, i) * 2 : ℕ) = m * (m - 1) := h
    have hm1 : 1 ≤ m := hmpos
    have := congrArg (fun k : ℕ => (k : ℝ)) hc
    simp only [Nat.cast_mul, Nat.cast_sub hm1, Nat.cast_one] at this
    exact this
  have hprod2 : ∏ i : Fin m, (α i0 * (3 / 4 : ℝ) ^ i.val) = α i0 ^ m * (3 / 4 : ℝ) ^ S := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum]
    simp [hS]
  have hdpos : 0 < p.det := hp.det_pos
  have hα0 := hα i0
  have hmain : α i0 ^ m ≤ (4 / 3 : ℝ) ^ S * p.det := by
    have h1 : α i0 ^ m * (3 / 4 : ℝ) ^ S ≤ p.det := by rw [← hprod2, hdet]; exact hprod
    have h2 : (3 / 4 : ℝ) ^ S * (4 / 3) ^ S = 1 := by rw [← mul_pow]; norm_num
    calc α i0 ^ m = α i0 ^ m * (3 / 4 : ℝ) ^ S * (4 / 3) ^ S := by
          rw [mul_assoc, h2, mul_one]
      _ ≤ p.det * (4 / 3) ^ S := by gcongr
      _ = _ := by ring
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hroot : α i0 ≤ (4 / 3 : ℝ) ^ (((m : ℝ) - 1) / 2) * p.det ^ ((1 : ℝ) / m) := by
    have h1 := Real.rpow_le_rpow (by positivity) hmain (by positivity : (0 : ℝ) ≤ 1 / m)
    rw [Real.mul_rpow (by positivity) hdpos.le] at h1
    have e1 : (α i0 ^ m) ^ ((1 : ℝ) / m) = α i0 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hα0.le]
      rw [mul_one_div_cancel hmR.ne', Real.rpow_one]
    have e2 : ((4 / 3 : ℝ) ^ S) ^ ((1 : ℝ) / m) = (4 / 3 : ℝ) ^ (((m : ℝ) - 1) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      field_simp
      linarith
    rw [e1, e2] at h1
    exact h1
  exact hle.trans hroot

/-- **Kitaoka 1993, Theorem 2.1.1** (p. 36) from Lemma 2.1.3: for $m \ge 2$ every positive definite $p$ is
${}^t\gamma\,s\,\gamma$ with $s \in S_{4/3,1/2}$ and $\gamma \in \mathrm{GL}_m(\mathbb Z)$, and
$\min p \le (4/3)^{(m-1)/2} (\det p)^{1/m}$, i.e. $\mu_m \le (4/3)^{(m-1)/2}$. -/
theorem theorem211_of_lemma213 (h : Lemma213) : Theorem211 := by
  intro m hm
  refine ⟨fun p hp => theorem211_partOne_of_lemma213 h hm p hp, fun p hp => ?_⟩
  obtain ⟨γ, s, ⟨a, ⟨α, hα, hαr, rfl⟩, n, hn, rfl⟩, hpeq⟩ := theorem211_partOne_of_lemma213 h hm p hp
  exact theorem211_partTwo_aux hm p hp γ α hα hαr n hn.1 hpeq

/-- **Kitaoka 1993, Theorem 2.1.1** (p. 36), *proved*: for $m \ge 2$, $P = \bigcup_{\gamma \in \Gamma}
S_{4/3,1/2}[\gamma]$, and $\min p \le (4/3)^{(m-1)/2} (\det p)^{1/m}$ for every positive definite $p$. Proof:
`theorem211_of_lemma213` with Lemma 2.1.3 (`lemma213`). -/
@[kb "kitaoka1993" "§2.1, Thm. 2.1.1, p. 36"]
theorem theorem211 : Theorem211 := theorem211_of_lemma213 lemma213

/-- **Hermite's constant** (Kitaoka 1993, Theorem 2.1.1, p. 36), *proved*: $\mu_m \le (4/3)^{(m-1)/2}$ for
$m \ge 2$, where $\mu_m$ = `hermiteConst m` $= \sup_{p \in P} \min p / (\det p)^{1/m}$. -/
@[kb "kitaoka1993" "§2.1, Thm. 2.1.1, p. 36 (μ_m ≤ (4/3)^{(m-1)/2})"]
theorem hermiteConst_le {m : ℕ} (hm : 2 ≤ m) :
    hermiteConst m ≤ (4 / 3 : ℝ) ^ (((m : ℝ) - 1) / 2) := by
  refine csSup_le ⟨_, 1, Matrix.PosDef.one, rfl⟩ ?_
  rintro r ⟨p, hp, rfl⟩
  have hdet : 0 < p.det ^ ((1 : ℝ) / m) := Real.rpow_pos_of_pos hp.det_pos _
  rw [div_le_iff₀ hdet]
  exact (theorem211 m hm).2 p hp

end QuadFormsKB.Kitaoka.Reduction
