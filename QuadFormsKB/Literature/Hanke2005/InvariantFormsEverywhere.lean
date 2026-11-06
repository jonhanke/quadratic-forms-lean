/-
# Hanke 2005, Calculation 4.1 (first equality) at every point of $\mathrm{SO}_n$

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

Setting ($\psi = 1_n$): $X = M_n(K)$, $T$ = symmetric matrices, $F(x) = {}^tx\,x$, $G = \mathrm{SO}_n = F^{-1}(1)\cap
\{\det = 1\}$, $\omega_X = \bigwedge_{i,j}dx_{ij}$, $\omega_T = \bigwedge_{i\le j}dt_{ij}$, and $\tilde\omega_G$ is
defined by (2.5)--(2.7) through $\omega_X = F^*(\omega_T)\wedge\tilde\omega_G$ along the fibre. Pointwise at
$x\in G$: for a basis $S_1,\dots,S_m$ of $T_xG = x\cdot\mathrm{Skew}_n$ and complementary vectors $P_1,\dots,P_r$,
$$\omega_X(S_1,\dots,S_m,P_1,\dots,P_r) = \tilde\omega_G(x)(S_1,\dots,S_m)\cdot\omega_T(dF_xP_1,\dots,dF_xP_r),
\qquad dF_x(P) = {}^tP\,x + {}^tx\,P.$$
Calculation 4.1 says $\tilde\omega_G = \pm2^{-n}\gamma_n$ with $\gamma_n = \bigwedge_{i>k}(x^{-1}dx)_{ik}$ left invariant.
`InvariantForms.lean` proves this at $x = 1$ (`omegaTilde_one`).

**Defines** `combMatOf`/`omegaX` ($\omega_X$ of a tuple of matrices), `dFAt`, `omegaTdFAt` ($\omega_T(dF_x P)$ for
$P_q = x\,\mathrm{sym}_q$), `omegaTildeScalar` ($c = \det/\omega_T(dF)$), `omegaTildeForm` ($\tilde\omega_G(x)$ as an
alternating map on $M_n$).

**Proves**
* `omegaX_leftMul`: $\omega_X(xV_1,\dots) = \det(x)^n\,\omega_X(V_1,\dots)$;
* `omegaTdFAt_eq`: $\omega_T(dF_x(xP_q)) = \omega_T(dF_1P_q)$ for ${}^tx\,x = 1$;
* `omegaTilde_at_iff`: the defining relation at $x$ (transported bases) holds for a scalar $c$ iff the relation at $1$
  holds for the same $c$ (same sign);
* `omegaTilde_at`: **first equality at every $x\in\mathrm{SO}_n$**: $c = \pm2^{-n}\gamma_x(xS_\bullet)$ and
  $\gamma_x(xS_\bullet)=1$;
* `omegaTildeForm_unique`: any alternating $\omega$ satisfying the relation on the basis $x\cdot\mathrm{skew}_\bullet$
  equals $\pm2^{-n}\gamma_x$ on all tuples of tangent vectors at $x$;
* `omegaTildeForm_relation`: conversely $\tilde\omega_G(x)$ satisfies the defining relation for *all* tangent tuples;
* `omegaTildeForm_left_invariant`, `omegaTilde_family_left_invariant`: left invariance
  $\tilde\omega_G(hx)(hS) = \tilde\omega_G(x)(S)$.

**Remarks.** (i) This is the pointwise statement: Mathlib has no differential forms on manifolds, so assembling the
forms $\tilde\omega_G(x)$, $x\in G$, into a smooth section of $\Lambda^m T^*G$ is not covered. (ii) The sign $\pm$ is
that of $\det$ of the combined basis for the chosen ordering `e` of coordinates, the same at every $x$.
(iii) Characteristic $0$ is used (division by $2$, skew matrices have zero diagonal). (iv) The remark after (2.8)
(change of basis $\psi\mapsto{}^tA\psi A$) is not treated here.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2005.InvariantForms

open Matrix Kronecker

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace QuadFormsKB.Hanke2005

variable {K : Type*} [Field K] {n : ℕ}

/-- The coordinate matrix (rows $(r,s)$, columns $c$) of a tuple $V = (V_c)_{c}$ of matrices:
the entry is $(V_c)_{rs}$. -/
def combMatOf (V : CombIdx n → Matrix (Fin n) (Fin n) K) : Matrix (Fin n × Fin n) (CombIdx n) K :=
  fun rs c => V c rs.1 rs.2

/-- $\omega_X(V)$ for a tuple $V$ indexed by `CombIdx n`: the determinant of the coordinates, the rows ordered
through the bijection `e`. -/
def omegaX (e : Fin n × Fin n ≃ CombIdx n) (V : CombIdx n → Matrix (Fin n) (Fin n) K) : K :=
  (Matrix.reindex e (Equiv.refl _) (combMatOf V)).det

theorem omegaX_combBasis (e : Fin n × Fin n ≃ CombIdx n) :
    omegaX e (combBasis : CombIdx n → Matrix (Fin n) (Fin n) K) =
      (combMatSq e : Matrix _ _ K).det := rfl

/-- **Left multiplication by $x$ scales $\omega_X$ by $\det(x)^n$** (the linear map $Y\mapsto xY$ on $M_n$ has
determinant $\det(x)^n$). -/
theorem omegaX_leftMul (e : Fin n × Fin n ≃ CombIdx n) (x : Matrix (Fin n) (Fin n) K)
    (V : CombIdx n → Matrix (Fin n) (Fin n) K) :
    omegaX e (fun c => x * V c) = x.det ^ n * omegaX e V := by
  classical
  have h : combMatOf (fun c => x * V c) =
      (x ⊗ₖ (1 : Matrix (Fin n) (Fin n) K)) * combMatOf V := by
    ext ⟨r, s⟩ c
    simp [combMatOf, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply,
      Matrix.kroneckerMap_apply]
  unfold omegaX
  rw [h, Matrix.reindex_apply, Matrix.reindex_apply]
  have h2 : ((x ⊗ₖ (1 : Matrix (Fin n) (Fin n) K)) * combMatOf V).submatrix e.symm
        (Equiv.refl _).symm
      = (x ⊗ₖ (1 : Matrix (Fin n) (Fin n) K)).submatrix e.symm e.symm *
        (combMatOf V).submatrix e.symm (Equiv.refl _).symm := by
    rw [Matrix.submatrix_mul_equiv]
  rw [h2, Matrix.det_mul, Matrix.det_submatrix_equiv_self, Matrix.det_kronecker]
  simp

/-- $dF_x(P) = {}^tP\,x + {}^tx\,P$, the differential of $F(x) = {}^tx\,x$ at $x$. -/
def dFAt (x P : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K := Pᵀ * x + xᵀ * P

/-- $\omega_T(dF_xP_1,\dots,dF_xP_r)$ for $P_q = x\cdot\mathrm{sym}_q$: the determinant of the coordinates
$(t_{ij})_{i\le j}$ of $dF_x(P_q)$. -/
def omegaTdFAt (x : Matrix (Fin n) (Fin n) K) : K :=
  (Matrix.of fun q' q : UpIdx n =>
    dFAt x (x * symUnit q' : Matrix (Fin n) (Fin n) K) q.1.1 q.1.2).det

/-- For ${}^tx\,x = 1$: $dF_x(xY) = Y + {}^tY = dF_1(Y)$. -/
theorem dFAt_mul (x Y : Matrix (Fin n) (Fin n) K) (hx : xᵀ * x = 1) :
    dFAt x (x * Y) = dFOne Y := by
  unfold dFAt dFOne
  rw [Matrix.transpose_mul, Matrix.mul_assoc, hx, Matrix.mul_one, ← Matrix.mul_assoc, hx,
    Matrix.one_mul, add_comm]

theorem omegaTdFAt_eq (x : Matrix (Fin n) (Fin n) K) (hx : xᵀ * x = 1) :
    omegaTdFAt x = omegaTdF K n := by
  unfold omegaTdFAt omegaTdF
  simp only [dFAt_mul x _ hx]

/-- The defining relation of $\tilde\omega_G(x)$ for the transported bases, and at $1$, involve the same scalar:
for $x\in\mathrm{SO}_n(K)$ (${}^tx\,x = 1$, $\det x = 1$),
$\omega_X(xS_\bullet,xP_\bullet) = c\,\omega_T(dF_x(xP_\bullet))$ iff $\omega_X(S_\bullet,P_\bullet) =
c\,\omega_T(dF_1P_\bullet)$ (the latter is the relation of `omegaTilde_one`). -/
@[kb "hanke2005crelle" "Calculation 4.1, pp. 9–10 (first equality, every point)"]
theorem omegaTilde_at_iff (e : Fin n × Fin n ≃ CombIdx n) (x : Matrix (Fin n) (Fin n) K)
    (hx : xᵀ * x = 1) (hdet : x.det = 1) (c : K) :
    omegaX e (fun b => x * combBasis b) = c * omegaTdFAt x ↔
      (combMatSq e : Matrix (CombIdx n) (CombIdx n) K).det = c * omegaTdF K n := by
  rw [omegaX_leftMul, hdet, one_pow, one_mul, omegaTdFAt_eq x hx]
  rfl

/-- **Calculation 4.1, first equality, at every $x\in\mathrm{SO}_n(K)$.** Let ${}^tx\,x = 1$, $\det x = 1$. If a
scalar $c = \tilde\omega_G(x)(xS_\bullet)$ satisfies the defining relation
$\omega_X(xS_\bullet,xP_\bullet) = c\,\omega_T(dF_x(xP_\bullet))$ for the transported skew basis
$S_{(i,k)} = E_{ik}-E_{ki}$ and symmetric complement $P_q$, then $c = \varepsilon\,2^{-n}\gamma_x(xS_\bullet)$ with
$\varepsilon=\pm1$, and $\gamma_x(xS_\bullet) = 1$. The sign $\varepsilon$ depends only on `e`, not on $x$. -/
@[kb "hanke2005crelle" "Calculation 4.1, pp. 9–10 (first equality, every point)"]
theorem omegaTilde_at [CharZero K] (e : Fin n × Fin n ≃ CombIdx n) (x : Matrix (Fin n) (Fin n) K)
    (hx : xᵀ * x = 1) (hdet : x.det = 1) (c : K)
    (hc : omegaX e (fun b => x * combBasis b) = c * omegaTdFAt x) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧
      c = ε * ((2 : K) ^ n)⁻¹ * gammaForm x (fun p => x * skewUnit p) := by
  have h1 := (omegaTilde_at_iff e x hx hdet c).mp hc
  obtain ⟨ε, hε, hcε⟩ := omegaTilde_one e c h1
  have hg1 : gammaForm (1 : Matrix (Fin n) (Fin n) K) (fun p => skewUnit p) = 1 := by
    simpa using gammaForm_skewUnit (1 : Matrix (Fin n) (Fin n) K) (by simp)
  refine ⟨ε, hε, ?_⟩
  rw [gammaForm_skewUnit x (by simp [hdet]), mul_one]
  rw [hg1, mul_one] at hcε
  exact hcε

/-- The scalar $c = \det(\text{combined basis})/\omega_T(dF_1P_\bullet)$ of the defining relation (at $1$, hence at
every $x\in\mathrm{SO}_n$ by `omegaTilde_at_iff`). -/
def omegaTildeScalar (e : Fin n × Fin n ≃ CombIdx n) : K :=
  (combMatSq e : Matrix (CombIdx n) (CombIdx n) K).det / omegaTdF K n

/-- **The form $\tilde\omega_G(x)$**, as an alternating map on $M_n(K)$ (meaningful on the tangent space
$x\cdot\mathrm{Skew}_n$): $\tilde\omega_G(x) = c\,\gamma_x$ with $c$ = `omegaTildeScalar e` $=\pm2^{-n}$. -/
def omegaTildeForm (e : Fin n × Fin n ≃ CombIdx n) (x : Matrix (Fin n) (Fin n) K) :
    (Matrix (Fin n) (Fin n) K) [⋀^LowIdx n]→ₗ[K] K :=
  (omegaTildeScalar e : K) • gammaForm x

theorem omegaTdF_ne_zero [CharZero K] : omegaTdF K n ≠ 0 := by
  rw [omegaTdF_eq]; exact pow_ne_zero _ two_ne_zero

/-- `omegaTildeScalar e` is $\pm2^{-n}$. -/
@[kb "hanke2005crelle" "Calculation 4.1, pp. 9–10 (first equality, every point)"]
theorem omegaTildeScalar_eq [CharZero K] (e : Fin n × Fin n ≃ CombIdx n) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ (omegaTildeScalar e : K) = ε * ((2 : K) ^ n)⁻¹ := by
  obtain ⟨ε, hε, h⟩ := omegaTilde_one (K := K) e (omegaTildeScalar e)
    (by unfold omegaTildeScalar; rw [div_mul_cancel₀ _ omegaTdF_ne_zero])
  have hg1 : gammaForm (1 : Matrix (Fin n) (Fin n) K) (fun p => skewUnit p) = 1 := by
    simpa using gammaForm_skewUnit (1 : Matrix (Fin n) (Fin n) K) (by simp)
  rw [hg1, mul_one] at h
  exact ⟨ε, hε, h⟩

/-- Two alternating maps on $M$ (indexed by `ι`) that agree on a family $B$ agree on every tuple lying in the span
coordinatewise: $S_b = \sum_a C_{ba}B_a$. -/
theorem alternating_eq_of_span {M : Type*} [AddCommGroup M] [Module K M] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (ω ω' : M [⋀^ι]→ₗ[K] K) (B : ι → M) (hB : ω B = ω' B) (S : ι → M)
    (C : ι → ι → K) (hS : ∀ b, S b = ∑ a, C b a • B a) : ω S = ω' S := by
  let φ : (ι → K) →ₗ[K] M := Fintype.linearCombination K B
  have hφ : ∀ b, φ (C b) = S b := fun b => by
    simp [φ, Fintype.linearCombination_apply, hS b]
  have hφe : (fun a => φ (Pi.single a (1 : K))) = B := by
    funext a; simp [φ, Fintype.linearCombination_apply_single]
  have h1 := (ω.compLinearMap φ).eq_smul_basis_det (Pi.basisFun K ι)
  have h2 := (ω'.compLinearMap φ).eq_smul_basis_det (Pi.basisFun K ι)
  have h3 : ω.compLinearMap φ (Pi.basisFun K ι) = ω'.compLinearMap φ (Pi.basisFun K ι) := by
    simpa [AlternatingMap.compLinearMap_apply, hφe] using hB
  have e1 : ω S = ω.compLinearMap φ C := by
    simp [AlternatingMap.compLinearMap_apply, hφ]
  have e2 : ω' S = ω'.compLinearMap φ C := by
    simp [AlternatingMap.compLinearMap_apply, hφ]
  rw [e1, e2, h1, h2, h3]

/-- $\mathrm{skewOf}(y) = \sum_{i>k}y_{ik}(E_{ik}-E_{ki})$. -/
theorem skewOf_eq_sum (y : LowIdx n → K) :
    skewOf y = ∑ a : LowIdx n, y a • (skewUnit a : Matrix (Fin n) (Fin n) K) := by
  classical
  ext i k
  simp only [Matrix.sum_apply, Matrix.smul_apply, skewUnit, Matrix.sub_apply, Matrix.single_apply,
    smul_eq_mul]
  unfold skewOf
  split_ifs with h h'
  · rw [Finset.sum_eq_single ⟨(i, k), h⟩]
    · simp [h.ne']
    · rintro ⟨⟨a, b⟩, hab⟩ _ hne
      have h1 : ¬ (a = i ∧ b = k) := fun hh => hne (by obtain ⟨rfl, rfl⟩ := hh; rfl)
      have h2 : ¬ (b = i ∧ a = k) := by
        rintro ⟨rfl, rfl⟩; exact absurd hab (not_lt.mpr h.le)
      dsimp only
      simp only [h1, h2, ite_false, sub_self, mul_zero]
    · simp
  · rw [Finset.sum_eq_single ⟨(k, i), h'⟩]
    · simp [h'.ne]
    · rintro ⟨⟨a, b⟩, hab⟩ _ hne
      have h1 : ¬ (b = i ∧ a = k) := fun hh => hne (by obtain ⟨rfl, rfl⟩ := hh; rfl)
      have h2 : ¬ (a = i ∧ b = k) := by
        rintro ⟨rfl, rfl⟩; exact absurd hab (not_lt.mpr h'.le)
      dsimp only
      simp only [h1, h2, ite_false, sub_self, mul_zero]
    · simp
  · have : i = k := le_antisymm (not_lt.mp h) (not_lt.mp h')
    subst this
    refine (Finset.sum_eq_zero fun a _ => ?_).symm
    obtain ⟨⟨a, b⟩, hab⟩ := a
    simp only at hab
    have h1 : ¬ (a = i ∧ b = i) := by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ hab
    have h1' : ¬ (b = i ∧ a = i) := fun hh => h1 ⟨hh.2, hh.1⟩
    simp only [Subtype.mk.injEq, Prod.mk.injEq, h1, h1', ite_false, sub_self, mul_zero]

/-- A tangent vector $xA$ ($A$ skew-symmetric) is the combination of the basis $x\cdot\mathrm{skew}_a$ with
coefficients $A_{ik}$, $i>k$. -/
theorem tangent_eq_sum [CharZero K] (x : Matrix (Fin n) (Fin n) K) (A : Matrix (Fin n) (Fin n) K)
    (hA : A ∈ skewMat K n) :
    x * A = ∑ a : LowIdx n, A a.1.1 a.1.2 • (x * skewUnit a) := by
  have h := skewOf_eq_sum (K := K) (n := n) (fun a => A a.1.1 a.1.2)
  have h0 : skewOf (fun a : LowIdx n => A a.1.1 a.1.2) = A :=
    skewOf_skewCoord ⟨A, hA⟩
  rw [h0] at h
  conv_lhs => rw [h]
  rw [Matrix.mul_sum]
  simp [Matrix.mul_smul]

/-- **Uniqueness of $\tilde\omega_G(x)$; Calculation 4.1 (first equality) as an equality of forms.**
Let $x\in\mathrm{SO}_n(K)$ and let $\omega$ be an alternating map on $M_n(K)$ (indexed by `LowIdx n`) satisfying the
defining relation on the basis $xS_\bullet$ of the tangent space,
$\omega_X(xS_\bullet,xP_\bullet) = \omega(xS_\bullet)\cdot\omega_T(dF_x(xP_\bullet))$. Then for **all** tuples of
tangent vectors $X_b\in x\cdot\mathrm{Skew}_n$,
$\omega(X_1,\dots,X_m) = \tilde\omega_G(x)(X_1,\dots,X_m) = \varepsilon\,2^{-n}\gamma_x(X_1,\dots,X_m)$,
$\varepsilon=\pm1$. -/
@[kb "hanke2005crelle" "Calculation 4.1, pp. 9–10 (first equality, every point)"]
theorem omegaTildeForm_unique [CharZero K] (e : Fin n × Fin n ≃ CombIdx n)
    (x : Matrix (Fin n) (Fin n) K) (hx : xᵀ * x = 1) (hdet : x.det = 1)
    (ω : (Matrix (Fin n) (Fin n) K) [⋀^LowIdx n]→ₗ[K] K)
    (hω : omegaX e (fun b => x * combBasis b) = ω (fun p => x * skewUnit p) * omegaTdFAt x)
    (X : LowIdx n → Matrix (Fin n) (Fin n) K) (hX : ∀ b, ∃ S ∈ skewMat K n, X b = x * S) :
    ω X = omegaTildeForm e x X ∧
      ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ω X = ε * ((2 : K) ^ n)⁻¹ * gammaForm x X := by
  classical
  have hxu : IsUnit x.det := by simp [hdet]
  have hc : ω (fun p => x * skewUnit p) = omegaTildeScalar e := by
    have h1 := (omegaTilde_at_iff e x hx hdet (ω (fun p => x * skewUnit p))).mp hω
    unfold omegaTildeScalar
    rw [h1, mul_div_assoc, div_self omegaTdF_ne_zero, mul_one]
  have key : ω X = omegaTildeForm e x X := by
    choose A hA hXA using hX
    refine alternating_eq_of_span ω (omegaTildeForm e x) (fun p => x * skewUnit p) ?_ X
      (fun b a => A b a.1.1 a.1.2) (fun b => by rw [hXA b]; exact tangent_eq_sum x _ (hA b))
    simp only [omegaTildeForm, _root_.smul_apply, gammaForm_skewUnit x hxu, smul_eq_mul,
      mul_one]
    exact hc
  refine ⟨key, ?_⟩
  obtain ⟨ε, hε, hs⟩ := omegaTildeScalar_eq (K := K) e
  refine ⟨ε, hε, ?_⟩
  rw [key]
  simp [omegaTildeForm, hs]

/-- **The defining relation holds for $\tilde\omega_G(x)$ on all tangent tuples.** For $x\in\mathrm{SO}_n(K)$ and
$S_b = xA_b$ with $A_b$ skew-symmetric,
$\omega_X(S_\bullet,xP_\bullet) = \tilde\omega_G(x)(S_\bullet)\cdot\omega_T(dF_x(xP_\bullet))$,
where the tuple $(S_\bullet,xP_\bullet)$ is indexed by `CombIdx n` through `Sum.elim`. -/
@[kb "hanke2005crelle" "Calculation 4.1, pp. 9–10 (first equality, every point)"]
theorem omegaTildeForm_relation [CharZero K] (e : Fin n × Fin n ≃ CombIdx n)
    (x : Matrix (Fin n) (Fin n) K) (hx : xᵀ * x = 1) (hdet : x.det = 1)
    (S : LowIdx n → Matrix (Fin n) (Fin n) K) (hS : ∀ b, ∃ A ∈ skewMat K n, S b = x * A) :
    omegaX e (Sum.elim S (fun q => x * symUnit q)) = omegaTildeForm e x S * omegaTdFAt x := by
  classical
  have hxu : IsUnit x.det := by simp [hdet]
  choose A hA hSA using hS
  set C : LowIdx n → LowIdx n → K := fun b a => A b a.1.1 a.1.2 with hC
  let D : Matrix (CombIdx n) (CombIdx n) K := Matrix.fromBlocks (Matrix.of C) 0 0 1
  have hV : ∀ c, (Sum.elim S (fun q => x * symUnit q) : CombIdx n → Matrix (Fin n) (Fin n) K) c =
      ∑ c', D c c' • (fun c'' => x * combBasis c'' : CombIdx n → Matrix (Fin n) (Fin n) K) c' := by
    rintro (b | q)
    · rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, D, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.of_apply, zero_smul, Finset.sum_const_zero, add_zero, combBasis]
      rw [hSA b, tangent_eq_sum x _ (hA b)]
      simp [hC]
    · rw [Fintype.sum_sum_type]
      simp [D, combBasis, Matrix.one_apply, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  have hmat : combMatOf (Sum.elim S (fun q => x * symUnit q)) =
      combMatOf (fun c'' => x * combBasis c'') * Dᵀ := by
    ext rs c
    simp only [combMatOf, hV c, Matrix.mul_apply, Matrix.transpose_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hD : D.det = (Matrix.of C).det := by
    simp [D, Matrix.det_fromBlocks_zero₁₂]
  have h2 : omegaX e (Sum.elim S (fun q => x * symUnit q)) =
      (Matrix.of C).det * omegaX e (fun b => x * combBasis b) := by
    unfold omegaX
    have hre : Matrix.reindex e (Equiv.refl _) (combMatOf (Sum.elim S (fun q => x * symUnit q))) =
        Matrix.reindex e (Equiv.refl _) (combMatOf (fun c'' => x * combBasis c'')) * Dᵀ := by
      rw [hmat]
      ext r c
      simp [Matrix.mul_apply]
    rw [hre, Matrix.det_mul, Matrix.det_transpose, hD, mul_comm]
  have hg : gammaForm x S = (Matrix.of C).det := by
    rw [gammaForm_apply]
    congr 1
    ext b a
    simp only [Matrix.of_apply, hSA b, hC]
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hxu, Matrix.one_mul]
  have hx1 : omegaX e (fun b => x * combBasis b) = omegaTildeScalar e * omegaTdFAt x :=
    (omegaTilde_at_iff e x hx hdet _).mpr
      (by unfold omegaTildeScalar; rw [div_mul_cancel₀ _ omegaTdF_ne_zero])
  rw [h2, hx1]
  simp only [omegaTildeForm, _root_.smul_apply, hg, smul_eq_mul]
  ring

/-- **Left invariance of $\tilde\omega_G$.** For invertible $h$ (in particular $h\in\mathrm{SO}_n(K)$):
$\tilde\omega_G(hx)(hX_1,\dots,hX_m) = \tilde\omega_G(x)(X_1,\dots,X_m)$. -/
@[kb "hanke2005crelle" "Calculation 4.1, pp. 9–10 (first equality, every point)"]
theorem omegaTildeForm_left_invariant (e : Fin n × Fin n ≃ CombIdx n) (h x : Matrix (Fin n) (Fin n) K)
    (hh : IsUnit h.det) (X : LowIdx n → Matrix (Fin n) (Fin n) K) :
    omegaTildeForm e (h * x) (fun b => h * X b) = omegaTildeForm e x X := by
  simp [omegaTildeForm, gammaForm_left_invariant h x hh X]

/-- **Left invariance of any family satisfying the defining relation.** Let $(\omega_x)_{x}$ be alternating maps on
$M_n(K)$ such that each $\omega_x$ ($x\in\mathrm{SO}_n(K)$) satisfies the defining relation on the basis
$xS_\bullet$. Then for $h,x\in\mathrm{SO}_n(K)$ and tangent vectors $X_b\in x\cdot\mathrm{Skew}_n$,
$\omega_{hx}(hX_1,\dots,hX_m) = \omega_x(X_1,\dots,X_m)$. -/
@[kb "hanke2005crelle" "Calculation 4.1, pp. 9–10 (first equality, every point)"]
theorem omegaTilde_family_left_invariant [CharZero K] (e : Fin n × Fin n ≃ CombIdx n)
    (ω : Matrix (Fin n) (Fin n) K → (Matrix (Fin n) (Fin n) K) [⋀^LowIdx n]→ₗ[K] K)
    (hω : ∀ x : Matrix (Fin n) (Fin n) K, xᵀ * x = 1 → x.det = 1 →
      omegaX e (fun b => x * combBasis b) = ω x (fun p => x * skewUnit p) * omegaTdFAt x)
    (h x : Matrix (Fin n) (Fin n) K) (hh : hᵀ * h = 1) (hhd : h.det = 1)
    (hx : xᵀ * x = 1) (hxd : x.det = 1)
    (X : LowIdx n → Matrix (Fin n) (Fin n) K) (hX : ∀ b, ∃ S ∈ skewMat K n, X b = x * S) :
    ω (h * x) (fun b => h * X b) = ω x X := by
  have hhx : (h * x)ᵀ * (h * x) = 1 := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc hᵀ h x, hh, Matrix.one_mul, hx]
  have hhxd : (h * x).det = 1 := by rw [Matrix.det_mul, hhd, hxd, one_mul]
  have hhu : IsUnit h.det := by simp [hhd]
  have h1 := (omegaTildeForm_unique e (h * x) hhx hhxd (ω (h * x)) (hω _ hhx hhxd)
    (fun b => h * X b) (fun b => by
      obtain ⟨S, hS, hXS⟩ := hX b
      exact ⟨S, hS, by rw [hXS, Matrix.mul_assoc]⟩)).1
  have h2 := (omegaTildeForm_unique e x hx hxd (ω x) (hω _ hx hxd) X hX).1
  rw [h1, h2, omegaTildeForm_left_invariant e h x hhu X]

end QuadFormsKB.Hanke2005
