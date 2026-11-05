/-
# Hanke 2005, §4.2: the stabilizer $C_{\mathbb R}$ of the base point

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Proves** (all unconditional; $\alpha\in O(\varphi_v)$, $u$ = the last $r$ columns of $\alpha$,
$u = \begin{bmatrix}c\\f\\w\end{bmatrix}$)
* `FR_eq_pR_iff` ((4.2.6)): $F_{\mathbb R}(\alpha) = p_{\mathbb R}$ iff $c = 0$ and $f = 0$;
* `stab_blockDiag` ((4.2.7)): if $F_{\mathbb R}(\alpha) = p_{\mathbb R}$ then $\alpha$ is block diagonal for the
  splitting $n = q + r$: the top-right $q\times r$ block and the bottom-left $r\times q$ block vanish.
-/
import QuadFormsKB.Literature.Hanke2005.ArchSymmetricReal
import QuadFormsKB.Citation

open Matrix

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchReal

variable {r t : ℕ}

/-- For $\alpha\in O(\varphi_v)$ the last $r$ columns $u$ satisfy ${}^tu\varphi_vu = -1$. -/
theorem lastCols_gram {α : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ} (hα : αᵀ * phiR r t * α = phiR r t) :
    (lastCols α)ᵀ * phiR r t * lastCols α = -1 := by
  have h : (lastCols α)ᵀ * phiR r t * lastCols α =
      (αᵀ * phiR r t * α).submatrix (Fin.natAdd (r + t)) (Fin.natAdd (r + t)) := by
    ext i j; simp [lastCols, Matrix.mul_apply]
  rw [h, hα]
  ext i j
  simp [phiR, diagonal_apply, signVec, one_apply, Fin.natAdd_inj]
  split_ifs <;> simp

theorem lastCols_neg_posDef {α : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ}
    (hα : αᵀ * phiR r t * α = phiR r t) :
    (-((lastCols α)ᵀ * phiR r t * lastCols α)).PosDef := by
  rw [lastCols_gram hα, neg_neg]; exact PosDef.one

/-- **(4.2.6)** $F_{\mathbb R}(\alpha) = p_{\mathbb R}$ iff $c = 0$ and $f = 0$, for $\alpha\in O(\varphi_v)$ and
$\begin{bmatrix}c\\f\\w\end{bmatrix}$ the last $r$ columns of $\alpha$ (Hanke thesis, (4.2.6), p. 11). -/
@[kb "hanke2005crelle" "(4.2.6), p. 11 (C_R)"]
theorem FR_eq_pR_iff {α : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ} (hα : αᵀ * phiR r t * α = phiR r t) :
    FR α = pR r t ↔ cBlk (lastCols α) = 0 ∧ fBlk (lastCols α) = 0 := by
  have hU : IsUnit (wBlk (lastCols α) + cBlk (lastCols α)).det :=
    isUnit_iff_ne_zero.mpr (det_wc_ne_zero (lastCols_neg_posDef hα))
  rw [FR]
  generalize lastCols α = u at hU ⊢
  have hpR : pR r t = zMk 1 0 := by
    rw [← zMk_xBlk_yBlk (pR r t), xBlk_pR, yBlk_pR]
  constructor
  · intro h
    have hx := congrArg xBlk h
    have hy := congrArg yBlk h
    rw [zOf, xBlk_zMk, xBlk_pR] at hx
    rw [zOf, yBlk_zMk, yBlk_pR] at hy
    have hx' : wBlk u - cBlk u = wBlk u + cBlk u := by
      have := congrArg (fun A => A * (wBlk u + cBlk u)) hx
      simpa [Matrix.mul_assoc, nonsing_inv_mul _ hU] using this
    have hy' : fBlk u = 0 := by
      have := congrArg (fun A => A * (wBlk u + cBlk u)) hy
      simp only [Matrix.smul_mul, Matrix.mul_assoc, nonsing_inv_mul _ hU, Matrix.mul_one,
        Matrix.zero_mul] at this
      rcases smul_eq_zero.mp this with h0 | h0
      · exact absurd h0 (by positivity)
      · exact h0
    refine ⟨?_, hy'⟩
    have h2 : (2 : ℝ) • cBlk u = 0 := by
      have : wBlk u + cBlk u - (wBlk u - cBlk u) = 0 := by rw [hx']; abel
      rw [two_smul]; rw [← this]; abel
    rcases smul_eq_zero.mp h2 with h0 | h0
    · norm_num at h0
    · exact h0
  · rintro ⟨hc, hf⟩
    rw [zOf, hc, hf, hpR]
    rw [hc, add_zero] at hU
    simp only [add_zero, sub_zero, Matrix.zero_mul, smul_zero]
    rw [mul_nonsing_inv _ hU]

/-- ${}^tww = 1$ once $c = 0$, $f = 0$. -/
theorem wBlk_gram {α : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ} (hα : αᵀ * phiR r t * α = phiR r t)
    (hc : cBlk (lastCols α) = 0) (hf : fBlk (lastCols α) = 0) :
    (wBlk (lastCols α))ᵀ * wBlk (lastCols α) = 1 := by
  have h := lastCols_gram hα
  rw [transpose_mul_phiR_mul, hc, hf] at h
  simp only [Matrix.transpose_zero, Matrix.zero_mul, zero_add, zero_sub] at h
  exact neg_injective (by simpa using h)

/-- **(4.2.7)** If $F_{\mathbb R}(\alpha) = p_{\mathbb R}$ then $\alpha\in O(\varphi_v)$ is block diagonal:
$\alpha_{a,\,q+c} = 0$ and $\alpha_{q+c,\,a} = 0$ for $a < q = r+t$, $c < r$ (Hanke thesis, (4.2.7), p. 12). -/
@[kb "hanke2005crelle" "(4.2.7), p. 12 (C_R is block diagonal)"]
theorem stab_blockDiag {α : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ} (hα : αᵀ * phiR r t * α = phiR r t)
    (h : FR α = pR r t) (a : Fin (r + t)) (c : Fin r) :
    α (Fin.castAdd r a) (Fin.natAdd (r + t) c) = 0 ∧ α (Fin.natAdd (r + t) c) (Fin.castAdd r a) = 0 := by
  obtain ⟨hc, hf⟩ := (FR_eq_pR_iff hα).mp h
  have top : ∀ (a : Fin (r + t)) (d : Fin r), α (Fin.castAdd r a) (Fin.natAdd (r + t) d) = 0 := by
    intro a d
    refine Fin.addCases (fun i => ?_) (fun k => ?_) a
    · have := congrFun (congrFun hc i) d
      simpa [cBlk, lastCols] using this
    · have := congrFun (congrFun hf k) d
      simpa [fBlk, lastCols] using this
  refine ⟨top a c, ?_⟩
  have hw := wBlk_gram hα hc hf
  have hw' : wBlk (lastCols α) * (wBlk (lastCols α))ᵀ = 1 := mul_eq_one_comm.mp hw
  set v : Fin r → ℝ := fun k => α (Fin.natAdd (r + t) k) (Fin.castAdd r a) with hv
  have hmul : (wBlk (lastCols α))ᵀ *ᵥ v = 0 := by
    funext d
    have e := congrFun (congrFun hα (Fin.castAdd r a)) (Fin.natAdd (r + t) d)
    have e2 : (αᵀ * phiR r t * α) (Fin.castAdd r a) (Fin.natAdd (r + t) d) =
        ∑ k, α k (Fin.castAdd r a) * signVec r t k * α k (Fin.natAdd (r + t) d) := by
      rw [Matrix.mul_assoc, Matrix.mul_apply]
      simp only [transpose_apply, phiR, diagonal_mul]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [e2, Fin.sum_univ_add] at e
    have e3 : phiR r t (Fin.castAdd r a) (Fin.natAdd (r + t) d) = 0 := by
      rw [phiR, diagonal_apply_ne]
      intro hh
      have := congrArg Fin.val hh
      simp at this
      omega
    rw [e3] at e
    simp only [top, mul_zero, Finset.sum_const_zero, zero_add, signVec, Fin.addCases_right] at e
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, transpose_apply, wBlk, lastCols,
      submatrix_apply, Matrix.of_apply, id]
    simp only [mul_neg_one, neg_mul, Finset.sum_neg_distrib, neg_eq_zero] at e
    simp [hv]
    exact (Finset.sum_congr rfl fun x _ => by ring).trans e
  have : v = 0 := by
    have := congrArg (fun x => (wBlk (lastCols α)) *ᵥ x) hmul
    simpa [Matrix.mulVec_mulVec, hw'] using this
  exact congrFun this c

end QuadFormsKB.Hanke2005.ArchReal
