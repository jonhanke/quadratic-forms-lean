/-
# Hanke 2005, §4.2: the symmetric space $Z_{\mathbb R}$ of $SO(q, r)$ and the map $F_{\mathbb R}$

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Setting** (§4.2, p. 11). At a real place where $\varphi_v$ is indefinite, $\varphi_v = \mathrm{diag}[1_q, -1_r]$ with
$q\ge r\ge1$ (2.9); write $q = r + t$ and $n = q + r = r + t + r$. Vectors of $\mathbb R^n$ are split in blocks of sizes
$r, t, r$, as in (4.2.4). Here everything is indexed by `Fin (r + t + r)` (the first $q = r + t$ coordinates positive,
the last $r$ negative); indices are 0-based.

**Defines**
* `xBlk`, `yBlk`: for $z\in\mathbb R^{q\times r}$ (`Fin (r + t) → Fin r → ℝ`, $z_{ij}$ = row $i$, column $j$), the
  blocks $z = \begin{bmatrix}x\\y\end{bmatrix}$, $x\in\mathbb R^{r\times r}$, $y\in\mathbb R^{t\times r}$;
* `xiR z` $= \tfrac12({}^tx + x - {}^tyy)$ and `deltaR z` $=\delta(z) = \det\tfrac12({}^tx + x - {}^tyy)$ ((4.2.8), p. 12);
* `ZR r t` $= Z_{\mathbb R} = \{z : {}^tx + x > {}^tyy\}$ (positive definite), p. 11;
* `cBlk`, `fBlk`, `wBlk`: for an $n\times r$ matrix $u$ (the last $r$ columns of $\alpha$ in (4.2.4)), its blocks
  $u = \begin{bmatrix}c\\f\\w\end{bmatrix}$ of sizes $r, t, r$;
* `zOf u` $= \begin{bmatrix}(w-c)(w+c)^{-1}\\\sqrt2\,f(w+c)^{-1}\end{bmatrix}$, the right side of (4.2.5);
* `FR α` $= F_{\mathbb R}(\alpha) = \alpha p_{\mathbb R}$ by (4.2.5) (`lastCols α` = the last $r$ columns of $\alpha$);
* `pR` $= p_{\mathbb R} = \begin{bmatrix}1_r\\0\end{bmatrix}$ (p. 11);
* `frameOf z m` $= P(z)\,m$, $P(z) = \begin{bmatrix}(1-x)/2\\y/\sqrt2\\(1+x)/2\end{bmatrix}$: the inverse of `zOf` on
  frames with $w + c = m$ (not in the paper; used to compute the volumes of §4.2).

**Proves** (all unconditional)
* `transpose_frameOf_mul`: ${}^t(P(z)m)\,\varphi_v\,(P(z)m) = -{}^tm\,\xi(z)\,m$;
* `zOf_frameOf`, `frameOf_zOf`: $z\leftrightarrow u$ are inverse ($m$ invertible, resp. $w + c$ invertible);
* `det_wc_ne_zero`: if ${}^tu\varphi_vu$ is negative definite then $w + c$ is invertible;
* `xiR_zOf`: then $\xi(\mathrm{zOf}\,u) = -{}^tM\,({}^tu\varphi_vu)\,M$, $M = (w+c)^{-1}$, so `zOf_mem_ZR`: $\mathrm{zOf}\,u\in Z_{\mathbb R}$;
* (in `ArchActionReal.lean`: `FR_mem_ZR'`, (4.2.5) lands in $Z_{\mathbb R}$): $F_{\mathbb R}(\alpha)\in Z_{\mathbb R}$ for every $\alpha$ with
  ${}^t\alpha\varphi_v\alpha = \varphi_v$;
* `zOf_mul_right`: $\mathrm{zOf}(ub) = \mathrm{zOf}(u)$ for $b\in GL_r(\mathbb R)$;
* (in `ArchStabilizerReal.lean`: `FR_eq_pR_iff`, (4.2.6)) for $\alpha\in O(\varphi_v)$, $F_{\mathbb R}(\alpha) = p_{\mathbb R}$ iff $c = 0$ and $f = 0$;
* `deltaR_pR`: $\delta(p_{\mathbb R}) = 1$;
* `actR` (the action (4.2.1)–(4.2.2), $\alpha z = \mathrm{zOf}(\alpha P(z))$) and `FR_mul`:
  $F_{\mathbb R}(\alpha\beta) = \alpha F_{\mathbb R}(\beta)$ for $\beta\in O(\varphi_v)$.
-/
import Mathlib
import QuadFormsKB.Citation

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchReal

variable {r t : ℕ}

/-! ### The space $Z_{\mathbb R}$ -/

/-- The block $x\in\mathbb R^{r\times r}$ of $z = \begin{bmatrix}x\\y\end{bmatrix}\in\mathbb R^{q\times r}$ (Hanke thesis, §4.2,
p. 11): the first $r$ rows. -/
def xBlk (z : Fin (r + t) → Fin r → ℝ) : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun i j => z (Fin.castAdd t i) j

/-- The block $y\in\mathbb R^{t\times r}$ of $z$: the last $t$ rows. -/
def yBlk (z : Fin (r + t) → Fin r → ℝ) : Matrix (Fin t) (Fin r) ℝ := Matrix.of fun k j => z (Fin.natAdd r k) j

/-- $\xi(z) = \tfrac12({}^tx + x - {}^tyy)$, the matrix whose determinant is $\delta(z)$ (Hanke thesis, (4.2.8), p. 12). -/
def xiR (z : Fin (r + t) → Fin r → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  (1 / 2 : ℝ) • ((xBlk z)ᵀ + xBlk z - (yBlk z)ᵀ * yBlk z)

/-- $\delta(z) = \det\big(\tfrac12({}^tx + x - {}^tyy)\big)$ (Hanke thesis, (4.2.8), p. 12). -/
@[kb "hanke2005crelle" "(4.2.8), p. 12 (δ(z))"]
def deltaR (z : Fin (r + t) → Fin r → ℝ) : ℝ := (xiR z).det

/-- **The symmetric space** $Z_{\mathbb R} = \Big\{\begin{bmatrix}x\\y\end{bmatrix}\in\mathbb R^q_r \;\Big|\; x\in\mathbb R^r_r,\
y\in\mathbb R^t_r,\ {}^tx + x > {}^tyy\Big\}$ of $SO(q, r)$, $q = r + t$ (Hanke thesis, §4.2, p. 11; Shimura 1999, §6):
$>$ means that ${}^tx + x - {}^tyy$ is positive definite. -/
@[kb "hanke2005crelle" "§4.2, p. 11 (Z_R)"]
def ZR (r t : ℕ) : Set (Fin (r + t) → Fin r → ℝ) := {z | (xiR z).PosDef}

theorem xiR_transpose (z : Fin (r + t) → Fin r → ℝ) : (xiR z)ᵀ = xiR z := by
  simp only [xiR, transpose_smul, transpose_sub, transpose_add, transpose_transpose, transpose_mul]
  congr 1; abel

/-- **The base point** $p_{\mathbb R} = \begin{bmatrix}1_r\\0^t_r\end{bmatrix}$ (Hanke thesis, p. 11). -/
@[kb "hanke2005crelle" "§4.2, p. 11 (p_R)"]
def pR (r t : ℕ) : Fin (r + t) → Fin r → ℝ :=
  fun i => Fin.addCases (motive := fun _ => Fin r → ℝ) (fun a => (1 : Matrix (Fin r) (Fin r) ℝ) a)
    (fun _ => 0) i

theorem xBlk_pR : xBlk (pR r t) = 1 := by
  ext i j; simp [xBlk, pR]

theorem yBlk_pR : yBlk (pR r t) = 0 := by
  ext i j; simp [yBlk, pR]

theorem xiR_pR : xiR (pR r t) = 1 := by
  rw [xiR, xBlk_pR, yBlk_pR]
  ext i j; by_cases h : i = j
  · subst h; simp [one_apply]; norm_num
  · simp [h, one_apply]

/-- $\delta(p_{\mathbb R}) = 1$ (Hanke thesis, p. 12). -/
@[kb "hanke2005crelle" "§4.2, p. 12 (δ(p_R) = 1)"]
theorem deltaR_pR : deltaR (pR r t) = 1 := by rw [deltaR, xiR_pR, det_one]

theorem pR_mem_ZR : pR r t ∈ ZR r t := by
  show (xiR (pR r t)).PosDef
  rw [xiR_pR]; exact PosDef.one

/-! ### Frames and the map $F_{\mathbb R}$ -/

/-- The signs of $\varphi_v = \mathrm{diag}[1_q, -1_r]$, $q = r + t$. -/
def signVec (r t : ℕ) : Fin (r + t + r) → ℝ :=
  fun i => Fin.addCases (motive := fun _ => ℝ) (fun _ => 1) (fun _ => -1) i

/-- The Gram matrix $\varphi_v = \mathrm{diag}[1_q, -1_r]$ (Hanke thesis, (2.9), p. 6). -/
def phiR (r t : ℕ) : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ := diagonal (signVec r t)

/-- The block $c$ (first $r$ rows) of an $n\times r$ matrix $u = \begin{bmatrix}c\\f\\w\end{bmatrix}$ (Hanke thesis, (4.2.4)). -/
def cBlk (u : Matrix (Fin (r + t + r)) (Fin r) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun i j => u (Fin.castAdd r (Fin.castAdd t i)) j

/-- The block $f$ (middle $t$ rows) of $u$. -/
def fBlk (u : Matrix (Fin (r + t + r)) (Fin r) ℝ) : Matrix (Fin t) (Fin r) ℝ :=
  Matrix.of fun k j => u (Fin.castAdd r (Fin.natAdd r k)) j

/-- The block $w$ (last $r$ rows) of $u$. -/
def wBlk (u : Matrix (Fin (r + t + r)) (Fin r) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun i j => u (Fin.natAdd (r + t) i) j

/-- Assemble a $q\times r$ matrix from its blocks $x$ ($r\times r$) and $y$ ($t\times r$). -/
def zMk (x : Matrix (Fin r) (Fin r) ℝ) (y : Matrix (Fin t) (Fin r) ℝ) : Fin (r + t) → Fin r → ℝ :=
  fun i => Fin.addCases (motive := fun _ => Fin r → ℝ) (fun a => x a) (fun b => y b) i

@[simp] theorem xBlk_zMk (x : Matrix (Fin r) (Fin r) ℝ) (y : Matrix (Fin t) (Fin r) ℝ) : xBlk (zMk x y) = x := by
  ext i j; simp [xBlk, zMk]

@[simp] theorem yBlk_zMk (x : Matrix (Fin r) (Fin r) ℝ) (y : Matrix (Fin t) (Fin r) ℝ) : yBlk (zMk x y) = y := by
  ext i j; simp [yBlk, zMk]

theorem zMk_xBlk_yBlk (z : Fin (r + t) → Fin r → ℝ) : zMk (xBlk z) (yBlk z) = z := by
  funext i j
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp [zMk, xBlk, yBlk]

/-- **The map (4.2.5)** on frames: $u = \begin{bmatrix}c\\f\\w\end{bmatrix}\mapsto
\begin{bmatrix}(w-c)(w+c)^{-1}\\\sqrt2\,f(w+c)^{-1}\end{bmatrix}$ (Hanke thesis, (4.2.5), p. 11). -/
@[kb "hanke2005crelle" "(4.2.5), p. 11"]
def zOf (u : Matrix (Fin (r + t + r)) (Fin r) ℝ) : Fin (r + t) → Fin r → ℝ :=
  zMk ((wBlk u - cBlk u) * (wBlk u + cBlk u)⁻¹) (Real.sqrt 2 • fBlk u * (wBlk u + cBlk u)⁻¹)

/-- The last $r$ columns of an $n\times n$ matrix. -/
def lastCols (α : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ) : Matrix (Fin (r + t + r)) (Fin r) ℝ :=
  α.submatrix id (Fin.natAdd (r + t))

/-- **The map** $F_{\mathbb R} : G_{\mathbb R}\to Z_{\mathbb R}$, $\alpha\mapsto\alpha p_{\mathbb R}$, in the explicit form (4.2.5)
(Hanke thesis, (4.2.3), (4.2.5), p. 11): it depends only on the last $r$ columns of $\alpha$. -/
@[kb "hanke2005crelle" "(4.2.3), (4.2.5), p. 11 (F_R)"]
def FR (α : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ) : Fin (r + t) → Fin r → ℝ := zOf (lastCols α)

/-- $P(z)\,m$ with $P(z) = \begin{bmatrix}(1-x)/2\\y/\sqrt2\\(1+x)/2\end{bmatrix}$: the frame with `zOf` $= z$ and $w + c = m$. -/
def frameOf (z : Fin (r + t) → Fin r → ℝ) (m : Matrix (Fin r) (Fin r) ℝ) : Matrix (Fin (r + t + r)) (Fin r) ℝ :=
  Matrix.of fun i j => Fin.addCases (motive := fun _ => ℝ)
    (fun a => Fin.addCases (motive := fun _ => ℝ) (fun a₁ => ((1 / 2 : ℝ) • ((1 - xBlk z) * m)) a₁ j)
      (fun b => ((Real.sqrt 2)⁻¹ • (yBlk z * m)) b j) a)
    (fun c => ((1 / 2 : ℝ) • ((1 + xBlk z) * m)) c j) i

@[simp] theorem cBlk_frameOf (z : Fin (r + t) → Fin r → ℝ) (m : Matrix (Fin r) (Fin r) ℝ) :
    cBlk (frameOf z m) = (1 / 2 : ℝ) • ((1 - xBlk z) * m) := by
  ext i j; simp [cBlk, frameOf]

@[simp] theorem fBlk_frameOf (z : Fin (r + t) → Fin r → ℝ) (m : Matrix (Fin r) (Fin r) ℝ) :
    fBlk (frameOf z m) = (Real.sqrt 2)⁻¹ • (yBlk z * m) := by
  ext i j; simp [fBlk, frameOf]

@[simp] theorem wBlk_frameOf (z : Fin (r + t) → Fin r → ℝ) (m : Matrix (Fin r) (Fin r) ℝ) :
    wBlk (frameOf z m) = (1 / 2 : ℝ) • ((1 + xBlk z) * m) := by
  ext i j; simp [wBlk, frameOf]

theorem wBlk_add_cBlk_frameOf (z : Fin (r + t) → Fin r → ℝ) (m : Matrix (Fin r) (Fin r) ℝ) :
    wBlk (frameOf z m) + cBlk (frameOf z m) = m := by
  rw [wBlk_frameOf, cBlk_frameOf, ← smul_add, ← add_mul]
  rw [show (1 + xBlk z + (1 - xBlk z)) = (2 : ℝ) • (1 : Matrix (Fin r) (Fin r) ℝ) by
    rw [two_smul]; abel]
  rw [smul_mul_assoc, Matrix.one_mul, smul_smul]; norm_num

theorem wBlk_sub_cBlk_frameOf (z : Fin (r + t) → Fin r → ℝ) (m : Matrix (Fin r) (Fin r) ℝ) :
    wBlk (frameOf z m) - cBlk (frameOf z m) = xBlk z * m := by
  rw [wBlk_frameOf, cBlk_frameOf, ← smul_sub, ← sub_mul]
  rw [show (1 + xBlk z - (1 - xBlk z)) = (2 : ℝ) • xBlk z by rw [two_smul]; abel]
  rw [smul_mul_assoc, smul_smul]; norm_num

/-- `zOf` inverts `frameOf` for invertible $m$. -/
theorem zOf_frameOf (z : Fin (r + t) → Fin r → ℝ) {m : Matrix (Fin r) (Fin r) ℝ} (hm : IsUnit m.det) :
    zOf (frameOf z m) = z := by
  rw [zOf, wBlk_add_cBlk_frameOf, wBlk_sub_cBlk_frameOf, fBlk_frameOf, Matrix.mul_assoc,
    mul_nonsing_inv _ hm, Matrix.mul_one, smul_smul, mul_inv_cancel₀ (by positivity), one_smul,
    Matrix.mul_assoc, mul_nonsing_inv _ hm, Matrix.mul_one, zMk_xBlk_yBlk]

/-- `frameOf` inverts `zOf` on frames with $w + c$ invertible. -/
theorem frameOf_zOf {u : Matrix (Fin (r + t + r)) (Fin r) ℝ} (hu : IsUnit (wBlk u + cBlk u).det) :
    frameOf (zOf u) (wBlk u + cBlk u) = u := by
  set m := wBlk u + cBlk u
  have hx : xBlk (zOf u) * m = wBlk u - cBlk u := by
    rw [zOf, xBlk_zMk, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
  have hy : yBlk (zOf u) * m = Real.sqrt 2 • fBlk u := by
    rw [zOf, yBlk_zMk, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
  ext i j
  refine Fin.addCases (fun a => ?_) (fun c => ?_) i
  · refine Fin.addCases (fun a₁ => ?_) (fun b => ?_) a
    · have : ((1 / 2 : ℝ) • ((1 - xBlk (zOf u)) * m)) a₁ j = cBlk u a₁ j := by
        rw [sub_mul, Matrix.one_mul, hx]
        simp only [m, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]; ring
      simpa [frameOf, cBlk] using this
    · have : ((Real.sqrt 2)⁻¹ • (yBlk (zOf u) * m)) b j = fBlk u b j := by
        rw [hy, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
      simpa [frameOf, fBlk] using this
  · have : ((1 / 2 : ℝ) • ((1 + xBlk (zOf u)) * m)) c j = wBlk u c j := by
      rw [add_mul, Matrix.one_mul, hx]
      simp only [m, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]; ring
    simpa [frameOf, wBlk] using this

/-! ### The Gram matrix of a frame -/

/-- ${}^tu\,\varphi_v\,u = {}^tcc + {}^tff - {}^tww$. -/
theorem transpose_mul_phiR_mul (u : Matrix (Fin (r + t + r)) (Fin r) ℝ) :
    uᵀ * phiR r t * u = (cBlk u)ᵀ * cBlk u + (fBlk u)ᵀ * fBlk u - (wBlk u)ᵀ * wBlk u := by
  ext i j
  rw [phiR, Matrix.mul_apply]
  simp only [mul_diagonal, transpose_apply]
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp [signVec, cBlk, fBlk, wBlk, Matrix.mul_apply]
  ring

/-- **The Gram matrix of $P(z)m$:** ${}^t(P(z)m)\,\varphi_v\,(P(z)m) = -{}^tm\,\xi(z)\,m$. -/
theorem transpose_frameOf_mul (z : Fin (r + t) → Fin r → ℝ) (m : Matrix (Fin r) (Fin r) ℝ) :
    (frameOf z m)ᵀ * phiR r t * frameOf z m = -(mᵀ * xiR z * m) := by
  rw [transpose_mul_phiR_mul, cBlk_frameOf, fBlk_frameOf, wBlk_frameOf]
  simp only [transpose_smul, transpose_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, xiR]
  have h2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num
  rw [h2]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one,
    transpose_sub, transpose_add, transpose_one, Matrix.mul_assoc]
  module

/-- If ${}^tu\varphi_vu$ is negative definite then $w + c$ is invertible. -/
theorem det_wc_ne_zero {u : Matrix (Fin (r + t + r)) (Fin r) ℝ} (hu : (-(uᵀ * phiR r t * u)).PosDef) :
    (wBlk u + cBlk u).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hpos := hu.dotProduct_mulVec_pos hv
  rw [transpose_mul_phiR_mul] at hpos
  have hw : wBlk u *ᵥ v = -(cBlk u *ᵥ v) := by
    rw [Matrix.add_mulVec] at hv0; exact eq_neg_of_add_eq_zero_left hv0
  have key : ∀ {k : ℕ} (A : Matrix (Fin k) (Fin r) ℝ), v ⬝ᵥ ((Aᵀ * A) *ᵥ v) = (A *ᵥ v) ⬝ᵥ (A *ᵥ v) := by
    intro k A; rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [star_trivial, Matrix.neg_mulVec, dotProduct_neg, Matrix.sub_mulVec, Matrix.add_mulVec,
    dotProduct_sub, dotProduct_add, key, hw, neg_dotProduct, dotProduct_neg, neg_neg] at hpos
  have : 0 ≤ (fBlk u *ᵥ v) ⬝ᵥ (fBlk u *ᵥ v) := by
    simpa using dotProduct_star_self_nonneg (fBlk u *ᵥ v)
  linarith

/-- $\xi(\mathrm{zOf}\,u) = -{}^tM\,({}^tu\varphi_vu)\,M$ with $M = (w + c)^{-1}$, for $w + c$ invertible. -/
theorem xiR_zOf {u : Matrix (Fin (r + t + r)) (Fin r) ℝ} (hu : IsUnit (wBlk u + cBlk u).det) :
    xiR (zOf u) = -((wBlk u + cBlk u)⁻¹ᵀ * (uᵀ * phiR r t * u) * (wBlk u + cBlk u)⁻¹) := by
  have h := transpose_frameOf_mul (zOf u) (wBlk u + cBlk u)
  rw [frameOf_zOf hu] at h
  rw [h, Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← transpose_mul, mul_nonsing_inv _ hu, transpose_one, Matrix.one_mul, Matrix.mul_assoc,
    mul_nonsing_inv _ hu, Matrix.mul_one]

/-- **(4.2.5) lands in $Z_{\mathbb R}$**: if ${}^tu\varphi_vu$ is negative definite then $\mathrm{zOf}\,u\in Z_{\mathbb R}$. -/
theorem zOf_mem_ZR {u : Matrix (Fin (r + t + r)) (Fin r) ℝ} (hu : (-(uᵀ * phiR r t * u)).PosDef) :
    zOf u ∈ ZR r t := by
  have hdet := det_wc_ne_zero hu
  have hU : IsUnit (wBlk u + cBlk u).det := isUnit_iff_ne_zero.mpr hdet
  show (xiR (zOf u)).PosDef
  set M := (wBlk u + cBlk u)⁻¹
  have hM : IsUnit M := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_nonsing_inv_det _ hU)
  have hinj : Function.Injective M.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hM
  have := hu.conjTranspose_mul_mul_same hinj
  rw [conjTranspose_eq_transpose_of_trivial, Matrix.mul_neg, Matrix.neg_mul] at this
  rw [xiR_zOf hU]; exact this

/-! ### The action of $G_{\mathbb R}$ on $Z_{\mathbb R}$ -/

theorem frameOf_eq_mul (z : Fin (r + t) → Fin r → ℝ) (m : Matrix (Fin r) (Fin r) ℝ) :
    frameOf z m = frameOf z 1 * m := by
  ext i j
  refine Fin.addCases (fun a => ?_) (fun c => ?_) i
  · refine Fin.addCases (fun a₁ => ?_) (fun b => ?_) a
    · simp [frameOf, Matrix.mul_apply, Matrix.smul_apply, Finset.mul_sum, mul_assoc]
    · simp [frameOf, Matrix.mul_apply, Matrix.smul_apply, Finset.mul_sum, mul_assoc]
  · simp [frameOf, Matrix.mul_apply, Matrix.smul_apply, Finset.mul_sum, mul_assoc]

theorem cBlk_mul (u : Matrix (Fin (r + t + r)) (Fin r) ℝ) (b : Matrix (Fin r) (Fin r) ℝ) :
    cBlk (u * b) = cBlk u * b := by ext i j; simp [cBlk, Matrix.mul_apply]

theorem fBlk_mul (u : Matrix (Fin (r + t + r)) (Fin r) ℝ) (b : Matrix (Fin r) (Fin r) ℝ) :
    fBlk (u * b) = fBlk u * b := by ext i j; simp [fBlk, Matrix.mul_apply]

theorem wBlk_mul (u : Matrix (Fin (r + t + r)) (Fin r) ℝ) (b : Matrix (Fin r) (Fin r) ℝ) :
    wBlk (u * b) = wBlk u * b := by ext i j; simp [wBlk, Matrix.mul_apply]

/-- **`zOf` is invariant under $u\mapsto ub$**, $b\in GL_r(\mathbb R)$. -/
theorem zOf_mul_right (u : Matrix (Fin (r + t + r)) (Fin r) ℝ) {b : Matrix (Fin r) (Fin r) ℝ} (hb : IsUnit b.det) :
    zOf (u * b) = zOf u := by
  rw [zOf, zOf, cBlk_mul, fBlk_mul, wBlk_mul, ← sub_mul, ← add_mul, Matrix.mul_inv_rev, ← Matrix.mul_assoc,
    Matrix.mul_assoc (wBlk u - cBlk u), mul_nonsing_inv _ hb, Matrix.mul_one, ← Matrix.mul_assoc,
    Matrix.smul_mul, Matrix.mul_assoc (fBlk u), mul_nonsing_inv _ hb, Matrix.mul_one, Matrix.smul_mul]

/-- **The action of $G_{\mathbb R}$ on $Z_{\mathbb R}$** (Hanke thesis, (4.2.1)–(4.2.2), p. 11; Shimura 1999, §6):
$\alpha z = \mathrm{zOf}(\alpha P(z))$, $P(z)$ = `frameOf z 1`; by `zOf_mul_right` any frame with `zOf` $= z$ may be
used, so this is the action induced by left multiplication on the frames of (4.2.1). -/
@[kb "hanke2005crelle" "(4.2.1)–(4.2.2), p. 11 (the G_R-action on Z_R)"]
def actR (α : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ) (z : Fin (r + t) → Fin r → ℝ) :
    Fin (r + t) → Fin r → ℝ :=
  zOf (α * frameOf z 1)

/-- **(4.2.2)–(4.2.3): $F_{\mathbb R}$ is equivariant**, $F_{\mathbb R}(\alpha\beta) = \alpha F_{\mathbb R}(\beta)$ for every
$\beta\in O(\varphi_v)$ and every matrix $\alpha$. -/
@[kb "hanke2005crelle" "(4.2.2)–(4.2.3), p. 11"]
theorem FR_mul (α : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ) {β : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ}
    (hβ : βᵀ * phiR r t * β = phiR r t) : FR (α * β) = actR α (FR β) := by
  have hneg : (-((lastCols β)ᵀ * phiR r t * lastCols β)).PosDef := by
    have : (lastCols β)ᵀ * phiR r t * lastCols β = -1 := by
      have h : (lastCols β)ᵀ * phiR r t * lastCols β =
          (βᵀ * phiR r t * β).submatrix (Fin.natAdd (r + t)) (Fin.natAdd (r + t)) := by
        ext i j; simp [lastCols, Matrix.mul_apply]
      rw [h, hβ]
      ext i j
      simp [phiR, diagonal_apply, signVec, one_apply, Fin.natAdd_inj]
      split_ifs <;> simp
    rw [this, neg_neg]; exact PosDef.one
  have hU : IsUnit (wBlk (lastCols β) + cBlk (lastCols β)).det := isUnit_iff_ne_zero.mpr (det_wc_ne_zero hneg)
  rw [FR, FR, actR, show lastCols (α * β) = α * lastCols β from by ext i j; simp [lastCols, Matrix.mul_apply]]
  conv_lhs => rw [← frameOf_zOf hU, frameOf_eq_mul, ← Matrix.mul_assoc, zOf_mul_right _ hU]

end QuadFormsKB.Hanke2005.ArchReal
