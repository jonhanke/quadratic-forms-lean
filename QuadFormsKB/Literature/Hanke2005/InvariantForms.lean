/-
# Hanke 2005, the invariant form $\gamma_n$ on $\mathrm{SO}_n$ (4.1) and Calculation 4.1, pointwise

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

Mathlib has no invariant differential forms on Lie groups, so the forms of (4.1) are formalized **pointwise as
linear algebra**: a form on $G = \mathrm{SO}_n(K)$ is a family of alternating maps on the tangent spaces
$T_gG = g\cdot\mathrm{Skew}_n$. Here the alternating maps are defined on all of $M_n(K)$, indexed by the pairs
$(i,k)$ with $i>k$ (`LowIdx n`); the thesis's $x_{ik}$, $1\le i,k\le n$, are `x i k` with `i k : Fin n` (0-based).

**Defines** `gammaForm g` ($\gamma_g(X_1,\dots,X_m) = \det[(g^{-1}X_b)_{i_ak_a}]_{a,b}$) and `deltaForm`
($\bigwedge_{i>k}dx_{ik}$).

**Proves** (4.1) left invariance `gammaForm_left_invariant`, non-degeneracy `gammaForm_skewUnit`,
Calculation 4.1 (second equality) `gammaForm_eq_inv_prod_deltaForm`, and (first equality, at the identity) the
numerical identity `omegaTilde_one` ($\tilde\omega_G = \pm2^{-n}\gamma_1$), via the Gram determinant
`det_combMatSq` ($\pm2^{n(n-1)/2}$) and `omegaTdF_eq` ($\omega_T(dF_1P) = 2^{n(n+1)/2}$).

**Remarks.** (i) No sign $\pm$ is needed in the second equality for $\mathrm{SO}_n$: it holds with sign $+$, using
$\det x = 1$ (Lemma A4 contributes $\det(x)^{n-1}$). (ii) The first equality is only established at $x=1$, as the
characterization of $\tilde\omega_G$ by (2.5)–(2.7) there; the statement is about any scalar `c` satisfying the
defining relation $\omega_X(S,P) = c\,\omega_T(dF_1P)$. (iii) Characteristic $0$ is used (skew-symmetric matrices
have zero diagonal; division by $2$).
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2005.Jacobians

open Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace QuadFormsKB.Hanke2005

variable {K : Type*} [Field K] {n : ℕ}

/-- The coordinates $(X_{ik})_{i>k}$ of a matrix, as a linear map. -/
def lowCoord : Matrix (Fin n) (Fin n) K →ₗ[K] (LowIdx n → K) where
  toFun X p := X p.1.1 p.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- $X\mapsto ((gX)_{ik})_{i>k}$: the coordinates $i>k$ of $gX$. -/
def leftLowCoord (g : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K →ₗ[K] (LowIdx n → K) :=
  lowCoord ∘ₗ LinearMap.mulLeft K g

theorem leftLowCoord_apply (g X : Matrix (Fin n) (Fin n) K) (p : LowIdx n) :
    leftLowCoord g X p = (g * X) p.1.1 p.1.2 := rfl

/-- **The form $\delta = \bigwedge_{i>k}dx_{ik}$**, pointwise:
$\delta(X_1,\dots,X_m) = \det[(X_b)_{i_ak_a}]_{a,b}$. -/
def deltaForm : (Matrix (Fin n) (Fin n) K) [⋀^LowIdx n]→ₗ[K] K :=
  (Matrix.detRowAlternating : (LowIdx n → K) [⋀^LowIdx n]→ₗ[K] K).compLinearMap lowCoord

/-- **The form $\gamma_g$** of (4.1) at the point $g$ (thesis, p. 9): $\gamma_g = \bigwedge_{i>k}(g^{-1}dg)_{ik}$, i.e.
$\gamma_g(X_1,\dots,X_m) = \det[(g^{-1}X_b)_{i_ak_a}]_{a,b}$ where $(i_a,k_a)$ runs over the pairs $i>k$. -/
def gammaForm (g : Matrix (Fin n) (Fin n) K) : (Matrix (Fin n) (Fin n) K) [⋀^LowIdx n]→ₗ[K] K :=
  (Matrix.detRowAlternating : (LowIdx n → K) [⋀^LowIdx n]→ₗ[K] K).compLinearMap (leftLowCoord g⁻¹)

theorem gammaForm_apply (g : Matrix (Fin n) (Fin n) K) (X : LowIdx n → Matrix (Fin n) (Fin n) K) :
    gammaForm g X = (Matrix.of fun b a : LowIdx n => (g⁻¹ * X b) a.1.1 a.1.2).det := rfl

theorem deltaForm_apply (X : LowIdx n → Matrix (Fin n) (Fin n) K) :
    deltaForm X = (Matrix.of fun b a : LowIdx n => X b a.1.1 a.1.2).det := rfl

/-- **(4.1), left invariance**: $L_h^*\gamma_{hg} = \gamma_g$, i.e. $\gamma_{hg}(hX_1,\dots,hX_m) =
\gamma_g(X_1,\dots,X_m)$ for invertible $h$ (the differential of left translation is $X\mapsto hX$). -/
@[kb "hanke2005crelle" "(4.1), p. 9"]
theorem gammaForm_left_invariant (h g : Matrix (Fin n) (Fin n) K) (hh : IsUnit h.det)
    (X : LowIdx n → Matrix (Fin n) (Fin n) K) :
    gammaForm (h * g) (fun b => h * X b) = gammaForm g X := by
  rw [gammaForm_apply, gammaForm_apply]
  congr 2
  ext b a
  simp only [Matrix.mul_inv_rev]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc h⁻¹, Matrix.nonsing_inv_mul _ hh, Matrix.one_mul]

/-- The tangent vector $E_{ik}-E_{ki}$ ($i>k$) of $\mathrm{Skew}_n$ at the identity. -/
def skewUnit (p : LowIdx n) : Matrix (Fin n) (Fin n) K :=
  Matrix.single p.1.1 p.1.2 1 - Matrix.single p.1.2 p.1.1 1

/-- **(4.1), volume form**: for invertible $g$, $\gamma_g$ takes the value $1$ on the basis
$g(E_{ik}-E_{ki})_{i>k}$ of the tangent space $g\cdot\mathrm{Skew}_n$, so it is nonzero there. -/
@[kb "hanke2005crelle" "(4.1), p. 9"]
theorem gammaForm_skewUnit (g : Matrix (Fin n) (Fin n) K) (hg : IsUnit g.det) :
    gammaForm g (fun p => g * skewUnit p) = 1 := by
  rw [gammaForm_apply]
  have : (Matrix.of fun b a : LowIdx n =>
      (g⁻¹ * (g * (skewUnit b : Matrix (Fin n) (Fin n) K))) a.1.1 a.1.2) = 1 := by
    ext b a
    simp only [Matrix.of_apply]
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hg, Matrix.one_mul]
    obtain ⟨⟨i, k⟩, hik⟩ := b
    obtain ⟨⟨i', k'⟩, hik'⟩ := a
    simp only at hik hik'
    simp only [skewUnit, Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply,
      Subtype.mk.injEq, Prod.mk.injEq]
    by_cases h1 : i = i' ∧ k = k'
    · obtain ⟨rfl, rfl⟩ := h1
      simp [hik.ne']
    · have h2 : ¬ (k = i' ∧ i = k') := by
        rintro ⟨rfl, rfl⟩; exact absurd hik (not_lt.mpr hik'.le)
      simp only [h1, h2, ite_false, sub_zero]
  rw [this, Matrix.det_one]

/-- Applying a linear map to the rows of a square matrix multiplies the determinant by the determinant of the
map. -/
theorem det_rows_map {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → K) →ₗ[K] (ι → K))
    (w : ι → ι → K) :
    (Matrix.of fun b => f (w b)).det = LinearMap.det f * (Matrix.of w).det := by
  have hf : ∀ v, f v = (LinearMap.toMatrix' f) *ᵥ v := by
    intro v
    conv_lhs => rw [← Matrix.toLin'_toMatrix' f]
    rfl
  have : (Matrix.of fun b => f (w b)) = Matrix.of w * (LinearMap.toMatrix' f)ᵀ := by
    ext b a
    simp only [Matrix.of_apply, hf, Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec,
      dotProduct]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  rw [this, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix', mul_comm]

/-- On a skew-symmetric matrix, the coordinates $i>k$ determine the matrix (characteristic $\ne 2$). -/
theorem skewOf_skewCoord [CharZero K] (S : skewMat K n) :
    skewOf (skewCoord S) = (S : Matrix (Fin n) (Fin n) K) := by
  have hs : ∀ i j, (S : Matrix (Fin n) (Fin n) K) j i = -(S : Matrix (Fin n) (Fin n) K) i j :=
    fun i j => congrFun (congrFun S.2 i) j
  ext i k
  unfold skewOf
  split_ifs with h h'
  · rfl
  · exact (hs k i).symm
  · have : i = k := le_antisymm (not_lt.mp h) (not_lt.mp h')
    subst this
    have := hs i i
    exact (self_eq_neg.mp this).symm

/-- **Calculation 4.1, second equality, pointwise** (multiplicative form). For $x\in\mathrm{SO}_n(K)$
(${}^tx\,x = 1$, $\det x = 1$) and tangent vectors $X_b = x S_b$ with $S_b$ skew-symmetric,
$$\delta_x(X_1,\dots,X_m) = \prod_{l=1}^{n-1}\det{}_l(x)\cdot\gamma_x(X_1,\dots,X_m).$$
Proof: $X_b = (xS_bx^t)\,x$, with $xS_bx^t$ skew; Lemma A5 gives the factor $\prod_{l=1}^{n-1}\det_l(x)$ for right
multiplication by $x$, and Lemma A4 gives $\det(x^t)^{n-1} = 1$ for the conjugation $S\mapsto xSx^t$.
Here the product runs over `l.castSucc`, $l = 0,\dots,n-1$ (with $\det_0 = 1$). -/
theorem deltaForm_eq_prod_mul_gammaForm [CharZero K] (x : Matrix (Fin n) (Fin n) K)
    (hx : xᵀ * x = 1) (hdet : x.det = 1) (X : LowIdx n → Matrix (Fin n) (Fin n) K)
    (hX : ∀ b, ∃ S ∈ skewMat K n, X b = x * S) :
    deltaForm X = (∏ l : Fin n, detLead x l.castSucc) * gammaForm x X := by
  classical
  have hx' : x * xᵀ = 1 := mul_eq_one_comm.mp hx
  have hinv : x⁻¹ = xᵀ := Matrix.inv_eq_right_inv hx'
  choose S hS hXS using hX
  let Sb : LowIdx n → skewMat K n := fun b => ⟨S b, hS b⟩
  let e : skewMat K n ≃ₗ[K] (LowIdx n → K) := LinearEquiv.ofBijective skewCoord skewCoord_bijective
  let F : (LowIdx n → K) →ₗ[K] (LowIdx n → K) :=
    (e : skewMat K n →ₗ[K] (LowIdx n → K)) ∘ₗ congrSkew xᵀ ∘ₗ (e.symm : (LowIdx n → K) →ₗ[K] skewMat K n)
  have hFdet : LinearMap.det F = 1 := by
    rw [← det_eq_of_intertwine (congrSkew xᵀ) e F (by intro v; simp [F]), det_congrSkew,
      Matrix.det_transpose, hdet, one_pow]
  let w : LowIdx n → LowIdx n → K := fun b => skewCoord (Sb b)
  have hg : gammaForm x X = (Matrix.of w).det := by
    rw [gammaForm_apply]
    congr 1
    ext b a
    simp only [Matrix.of_apply, hinv, hXS b, ← Matrix.mul_assoc, hx, Matrix.one_mul]
    rfl
  have hd : ∀ b, (fun p : LowIdx n => X b p.1.1 p.1.2) = skewMulRight x (F (w b)) := by
    intro b
    have hF : F (w b) = skewCoord (congrSkew xᵀ (Sb b)) := by
      simp only [F, w, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [show skewCoord (Sb b) = e (Sb b) from rfl, LinearEquiv.symm_apply_apply]
      rfl
    funext p
    show X b p.1.1 p.1.2 = (skewOf (F (w b)) * x) p.1.1 p.1.2
    rw [hF, skewOf_skewCoord]
    show X b p.1.1 p.1.2 = (xᵀᵀ * (S b) * xᵀ * x) p.1.1 p.1.2
    rw [hXS b, Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.mul_assoc, hx, Matrix.mul_one]
  rw [deltaForm_apply, hg]
  have : (Matrix.of fun b a : LowIdx n => X b a.1.1 a.1.2) =
      Matrix.of fun b => (skewMulRight x ∘ₗ F) (w b) := by
    ext b a
    exact congrFun (hd b) a
  rw [this, det_rows_map, LinearMap.det_comp, hFdet, det_skewMulRight, mul_one]

/-- **Calculation 4.1, second equality, pointwise.** For $x\in\mathrm{SO}_n(K)$ with all $\det_l(x)\ne0$ and
tangent vectors $X_b\in x\cdot\mathrm{Skew}_n$,
$$\gamma_x(X_1,\dots,X_m) = \Big(\prod_{l=1}^{n}\det{}_l(x)\Big)^{-1}\delta_x(X_1,\dots,X_m),$$
with sign $+$ (no $\pm$ is needed; the product runs over `l : Fin (n + 1)`, i.e. $l=0,\dots,n$, with $\det_0 = 1$ and
$\det_n(x) = \det x = 1$). -/
@[kb "hanke2005crelle" "Calculation 4.1, pp. 9–10"]
theorem gammaForm_eq_inv_prod_deltaForm [CharZero K] (x : Matrix (Fin n) (Fin n) K)
    (hx : xᵀ * x = 1) (hdet : x.det = 1) (hl : ∀ l : Fin (n + 1), detLead x l ≠ 0)
    (X : LowIdx n → Matrix (Fin n) (Fin n) K) (hX : ∀ b, ∃ S ∈ skewMat K n, X b = x * S) :
    gammaForm x X = (∏ l : Fin (n + 1), detLead x l)⁻¹ * deltaForm X := by
  have hlast : detLead x (Fin.last n) = 1 := by
    rw [← hdet]
    unfold detLead
    congr 1
  have hprod : ∏ l : Fin (n + 1), detLead x l = ∏ l : Fin n, detLead x l.castSucc := by
    rw [Fin.prod_univ_castSucc, hlast, mul_one]
  have hne : (∏ l : Fin n, detLead x l.castSucc) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun l _ => hl _
  rw [hprod, deltaForm_eq_prod_mul_gammaForm x hx hdet X hX, ← mul_assoc, inv_mul_cancel₀ hne,
    one_mul]

/-! ### Calculation 4.1, first equality, at the identity -/

/-- The index set of the combined basis $\{S_p\}_{p\in\mathrm{LowIdx}}\cup\{P_q\}_{q\in\mathrm{UpIdx}}$. -/
abbrev CombIdx (n : ℕ) := LowIdx n ⊕ UpIdx n

/-- The symmetric basis $P_{(i,i)} = E_{ii}$, $P_{(i,j)} = E_{ij}+E_{ji}$ ($i<j$). -/
def symUnit (q : UpIdx n) : Matrix (Fin n) (Fin n) K :=
  if q.1.1 = q.1.2 then Matrix.single q.1.1 q.1.1 1
  else Matrix.single q.1.1 q.1.2 1 + Matrix.single q.1.2 q.1.1 1

/-- The combined basis of $M_n(K)$: skew elements $S_{(i,k)}$ and symmetric elements $P_{(i,j)}$. -/
def combBasis : CombIdx n → Matrix (Fin n) (Fin n) K
  | Sum.inl p => skewUnit p
  | Sum.inr q => symUnit q

/-- The coordinate matrix of the combined basis in the coordinates $x_{ij}$: column $c$ is `combBasis c`. -/
def combMat : Matrix (Fin n × Fin n) (CombIdx n) K := fun rs c => combBasis c rs.1 rs.2

/-- The diagonal of the Gram matrix of the combined basis. -/
def gramDiag : CombIdx n → K
  | Sum.inl _ => 2
  | Sum.inr q => if q.1.1 = q.1.2 then 1 else 2

theorem sum_single_mul (a b c d : Fin n) :
    ∑ rs : Fin n × Fin n, (Matrix.single a b (1 : K)) rs.1 rs.2 * (Matrix.single c d (1 : K)) rs.1 rs.2
      = if a = c ∧ b = d then 1 else 0 := by
  classical
  simp [Matrix.single_apply, Fintype.sum_prod_type, ite_and]

theorem combMat_gram [CharZero K] (c c' : CombIdx n) :
    ∑ rs : Fin n × Fin n, combMat rs c * combMat (K := K) rs c' = if c = c' then gramDiag c else 0 := by
  classical
  rcases c with ⟨⟨i, k⟩, hik⟩ | ⟨⟨a, b⟩, hab⟩ <;> rcases c' with ⟨⟨i', k'⟩, hik'⟩ | ⟨⟨a', b'⟩, hab'⟩
  · simp only at hik hik'
    simp only [combMat, combBasis, skewUnit, gramDiag, Matrix.sub_apply,
      sub_mul, mul_sub, Finset.sum_sub_distrib, sum_single_mul, Sum.inl.injEq, Subtype.mk.injEq,
      Prod.mk.injEq]
    split_ifs <;> grind
  · simp only at hik hab'
    by_cases hd : a' = b'
    · simp only [combMat, combBasis, skewUnit, symUnit, hd, ite_true, gramDiag, Matrix.sub_apply,
        sub_mul, mul_sub, Finset.sum_sub_distrib, sum_single_mul, reduceCtorEq, ite_false]
      split_ifs <;> grind
    · simp only [combMat, combBasis, skewUnit, symUnit, hd, ite_false, gramDiag, Matrix.sub_apply,
        Matrix.add_apply, sub_mul, mul_sub, add_mul, mul_add, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, sum_single_mul, reduceCtorEq]
      split_ifs <;> grind
  · simp only at hik' hab
    by_cases hd : a = b
    · simp only [combMat, combBasis, skewUnit, symUnit, hd, ite_true, gramDiag, Matrix.sub_apply,
        sub_mul, mul_sub, Finset.sum_sub_distrib, sum_single_mul, reduceCtorEq, ite_false]
      split_ifs <;> grind
    · simp only [combMat, combBasis, skewUnit, symUnit, hd, ite_false, gramDiag, Matrix.sub_apply,
        Matrix.add_apply, sub_mul, mul_sub, add_mul, mul_add, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, sum_single_mul, reduceCtorEq]
      split_ifs <;> grind
  · simp only at hab hab'
    by_cases hd : a = b <;> by_cases hd' : a' = b'
    all_goals
      simp only [combMat, combBasis, symUnit, hd, hd', ite_true, ite_false, gramDiag, Matrix.add_apply,
        add_mul, mul_add, Finset.sum_add_distrib, sum_single_mul, Sum.inr.injEq, Subtype.mk.injEq,
        Prod.mk.injEq]
      try (split_ifs <;> grind)

/-- The coordinate change $(\mathrm{Fin}\,n)^2\simeq\mathrm{LowIdx}\sqcup\mathrm{UpIdx}$: $(r,s)\mapsto$ the
lower index $(r,s)$ if $s<r$, else the upper index $(r,s)$. -/
def idxEquiv : Fin n × Fin n ≃ CombIdx n :=
  (Equiv.sumCompl (fun r : Fin n × Fin n => r.2 < r.1)).symm.trans
    (Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivRight fun _ => not_lt))

/-- $\mathrm{UpIdx}\simeq\mathrm{LowIdx}\sqcup\mathrm{Fin}\,n$: the strictly upper pairs $(a,b)$, $a<b$, correspond to
the lower pairs $(b,a)$, and the diagonal pairs to $\mathrm{Fin}\,n$. -/
def upEquiv : UpIdx n ≃ LowIdx n ⊕ Fin n where
  toFun q := if h : q.1.1 = q.1.2 then Sum.inr q.1.1 else Sum.inl ⟨(q.1.2, q.1.1), lt_of_le_of_ne q.2 h⟩
  invFun
    | Sum.inl p => ⟨(p.1.2, p.1.1), p.2.le⟩
    | Sum.inr i => ⟨(i, i), le_rfl⟩
  left_inv := by
    rintro ⟨⟨a, b⟩, hab⟩
    by_cases h : a = b
    · subst h; simp
    · simp [h]
  right_inv := by
    rintro (⟨⟨i, k⟩, h⟩ | i)
    · have : ¬ k = i := h.ne
      simp [this]
    · simp

theorem card_up_add_low : Fintype.card (UpIdx n) = Fintype.card (LowIdx n) + n := by
  rw [Fintype.card_congr (upEquiv (n := n)), Fintype.card_sum, Fintype.card_fin]

theorem card_low_add_up : Fintype.card (LowIdx n) + Fintype.card (UpIdx n) = n * n := by
  rw [← Fintype.card_sum, ← Fintype.card_congr (idxEquiv (n := n)), Fintype.card_prod,
    Fintype.card_fin]

theorem prod_gramDiag : ∏ c : CombIdx n, (gramDiag c : K) = 2 ^ (2 * Fintype.card (LowIdx n)) := by
  classical
  rw [Fintype.prod_sum_type, ← Equiv.prod_comp (upEquiv (n := n)).symm, Fintype.prod_sum_type]
  have h : ∀ p : LowIdx n, (gramDiag (Sum.inr ((upEquiv (n := n)).symm (Sum.inl p))) : K) = 2 := by
    intro p
    simp [gramDiag, upEquiv, p.2.ne]
  simp only [h]
  simp [gramDiag, upEquiv, two_mul, pow_add]

theorem card_low : Fintype.card (LowIdx n) = n * (n - 1) / 2 := by
  have h1 := card_low_add_up (n := n)
  have h2 := card_up_add_low (n := n)
  have h3 : n * (n - 1) = n * n - n := Nat.mul_sub_one n n
  generalize n * n = N at *
  omega

/-- The matrix of the combined basis in the coordinates $x_{ij}$, with rows and columns both indexed by
`CombIdx n` through a bijection `e` of the coordinate pairs with `CombIdx n` (a different `e` only changes the
sign of the determinant). -/
def combMatSq (e : Fin n × Fin n ≃ CombIdx n) : Matrix (CombIdx n) (CombIdx n) K :=
  Matrix.reindex e (Equiv.refl _) combMat

theorem combMatSq_gram [CharZero K] (e : Fin n × Fin n ≃ CombIdx n) :
    (combMatSq e : Matrix (CombIdx n) (CombIdx n) K)ᵀ * combMatSq e = Matrix.diagonal gramDiag := by
  classical
  ext c c'
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  simp only [Matrix.transpose_apply, combMatSq, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.refl_symm, Equiv.coe_refl, id]
  rw [Equiv.sum_comp e.symm (fun r => combMat r c * combMat r c')]
  exact combMat_gram c c'

/-- The square of the determinant of the combined basis is $2^{n(n-1)}$ (Gram determinant: the basis is
orthogonal for the trace form with squared lengths $2$ ($S_{ik}$, $P_{ij}$, $i<j$) and $1$ ($P_{ii}$)). -/
theorem det_combMatSq_sq [CharZero K] (e : Fin n × Fin n ≃ CombIdx n) :
    (combMatSq e : Matrix (CombIdx n) (CombIdx n) K).det ^ 2 = 2 ^ (2 * Fintype.card (LowIdx n)) := by
  rw [sq]
  nth_rewrite 1 [← Matrix.det_transpose]
  rw [← Matrix.det_mul, combMatSq_gram, Matrix.det_diagonal, prod_gramDiag]

/-- The determinant of the combined basis $\{S_{(i,k)}\}_{i>k}\cup\{P_{(i,j)}\}_{i\le j}$ in the coordinates $x_{ij}$
is $\pm2^{n(n-1)/2}$. -/
theorem det_combMatSq [CharZero K] (e : Fin n × Fin n ≃ CombIdx n) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧
      (combMatSq e : Matrix (CombIdx n) (CombIdx n) K).det = ε * 2 ^ (n * (n - 1) / 2) := by
  have h := det_combMatSq_sq (K := K) e
  rw [pow_mul', card_low, ] at h
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp h) with h | h
  · exact ⟨1, Or.inl rfl, by rw [h, one_mul]⟩
  · exact ⟨-1, Or.inr rfl, by rw [h]; ring⟩

/-- The differential at the identity of $F(x) = {}^tx\,x$: $dF_1(Y) = Y + {}^tY$. -/
def dFOne (Y : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K := Y + Yᵀ

/-- $\omega_T(dF_1P_1,\dots,dF_1P_r)$ for the symmetric basis $P$: the determinant of the coordinates
$(t_{ij})_{i\le j}$ of $dF_1(P_q)$. -/
def omegaTdF (K : Type*) [Field K] (n : ℕ) : K :=
  (Matrix.of fun q' q : UpIdx n => dFOne (symUnit q' : Matrix (Fin n) (Fin n) K) q.1.1 q.1.2).det

theorem omegaTdF_eq [CharZero K] : omegaTdF K n = 2 ^ (Fintype.card (LowIdx n) + n) := by
  classical
  have : (Matrix.of fun q' q : UpIdx n => dFOne (symUnit q' : Matrix (Fin n) (Fin n) K) q.1.1 q.1.2) =
      Matrix.diagonal fun _ => 2 := by
    ext ⟨⟨a, b⟩, hab⟩ ⟨⟨i, j⟩, hij⟩
    simp only at hab hij
    simp only [Matrix.of_apply, dFOne, Matrix.add_apply, Matrix.transpose_apply, symUnit,
      Matrix.diagonal_apply, Subtype.mk.injEq, Prod.mk.injEq]
    split_ifs <;> simp_all [Matrix.single_apply] <;> grind
  rw [omegaTdF, this, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, card_up_add_low]

/-- **Calculation 4.1, first equality, at the identity.** At $x = 1$ the form $\tilde\omega_G$ is characterized by
$\omega_X(S_1,\dots,S_m,P_1,\dots,P_r) = \tilde\omega_G(S_1,\dots,S_m)\cdot\omega_T(dF_1P_1,\dots,dF_1P_r)$, where
$\omega_X$ of the combined basis is the determinant of `combMatSq e` (up to the sign fixed by `e`) and
$\omega_T(dF_1P) = $ `omegaTdF K n` $= 2^{n(n+1)/2}$. Hence the value $c = \tilde\omega_G(S)$ satisfies
$c = \pm2^{-n}\gamma_1(S)$, with $\gamma_1(S)=1$ (`gammaForm_skewUnit`). -/
@[kb "hanke2005crelle" "Calculation 4.1, pp. 9–10"]
theorem omegaTilde_one [CharZero K] (e : Fin n × Fin n ≃ CombIdx n) (c : K)
    (hc : (combMatSq e : Matrix (CombIdx n) (CombIdx n) K).det = c * omegaTdF K n) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧
      c = ε * ((2 : K) ^ n)⁻¹ * gammaForm (1 : Matrix (Fin n) (Fin n) K) (fun p => skewUnit p) := by
  obtain ⟨ε, hε, hdet⟩ := det_combMatSq (K := K) e
  have hg : gammaForm (1 : Matrix (Fin n) (Fin n) K) (fun p => skewUnit p) = 1 := by
    simpa using gammaForm_skewUnit (1 : Matrix (Fin n) (Fin n) K) (by simp)
  refine ⟨ε, hε, ?_⟩
  rw [hg, mul_one]
  rw [omegaTdF_eq, card_low, hdet, pow_add] at hc
  have hn : (2 : K) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  field_simp
  have h3 : (2 : K) ^ (n * (n - 1) / 2) ≠ 0 := pow_ne_zero _ two_ne_zero
  apply mul_left_cancel₀ h3
  linear_combination hc.symm

end QuadFormsKB.Hanke2005
