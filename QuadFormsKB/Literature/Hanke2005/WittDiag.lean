/-
# Hanke 2005: Witt decompositions with a diagonal anisotropic part (any field of characteristic ≠ 2)

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

Generic tools for the local types of §3 (the normal form (2.9), p. 6): over a field $K$ with $2\ne0$, a nondegenerate
form $Q$ in $n$ variables with Witt index $w$ is isometric to $\mathbb H^w\perp\langle a_0,\dots,a_{t-1}\rangle$ with the
diagonal part anisotropic, $t = n - 2w$, and $\det H_Q = c^2(-1)^w2^t\prod a_i$ (`exists_witt_diag`). Consequences:
the Witt index is an invariant of equivalence (`wittIndex_eq_of_equivalent`) and adds over hyperbolic summands
(`wittIndex_hyperbolic_prod`); for even $n$ the discriminant $\delta = (-1)^{n/2}\det H_Q$ is a square when $t = 0$ and a
non-square when $t = 2$, and (given that quaternary forms of non-square determinant are isotropic, true over every
local field) a square when $t = 4$ (`even_disc_of_anisoDim`).
-/
import QuadFormsKB.Witt.Bridge

open Module QuadraticMap QuadraticForm

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

section Generic

variable {K : Type*} [Field K] {n : ℕ}

/-- **The Witt index is an invariant of equivalence.** -/
theorem wittIndex_eq_of_equivalent {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {Q₁ : QuadraticForm K V} {Q₂ : QuadraticForm K W}
    (h : Q₁.Equivalent Q₂) (hQ : Q₁.radical = ⊥) : wittIndex Q₁ = wittIndex Q₂ := by
  have hQ₂ : Q₂.radical = ⊥ := Witt.radical_eq_bot_of_isometryEquiv h.some.symm hQ
  obtain ⟨U, _, _, _, Qa, ha, h'⟩ := wittIndex_spec Q₂ hQ₂
  exact (eq_wittIndex Q₁ hQ ha (h.trans h')).symm

/-- $\mathbb H^k\perp\mathbb H^w\cong\mathbb H^{k+w}$. -/
theorem hyperbolicSpace_prod_equiv (k w : ℕ) :
    ((hyperbolicSpace K k).prod (hyperbolicSpace K w)).Equivalent (hyperbolicSpace K (k + w)) := by
  induction k with
  | zero => rw [Nat.zero_add]; exact ⟨Witt.hyperbolicSpaceZeroProd _⟩
  | succ k ih =>
    have e : ((hyperbolicSpace K (k + 1)).prod (hyperbolicSpace K w)).IsometryEquiv
        (hyperbolicSpace K (k + w + 1)) :=
      ((Witt.hyperbolicSpaceSucc k).symm.prod (QuadraticMap.IsometryEquiv.refl _)).trans
        ((Witt.prodAssoc _ _ _).trans (((QuadraticMap.IsometryEquiv.refl _).prod ih.some).trans
          (Witt.hyperbolicSpaceSucc (k + w))))
    rw [show k + 1 + w = k + w + 1 by omega]
    exact ⟨e⟩

/-- **Hyperbolic summands add to the Witt index:** $w(\mathbb H^k\perp Q) = k + w(Q)$. -/
theorem wittIndex_hyperbolic_prod {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (k : ℕ)
    (Q : QuadraticForm K V) (hQ : Q.radical = ⊥) :
    wittIndex ((hyperbolicSpace K k).prod Q) = k + wittIndex Q := by
  obtain ⟨U, _, _, _, Qa, ha, ⟨e⟩⟩ := wittIndex_spec Q hQ
  have e2 : ((hyperbolicSpace K k).prod Q).IsometryEquiv
      ((hyperbolicSpace K (k + wittIndex Q)).prod Qa) :=
    ((QuadraticMap.IsometryEquiv.refl _).prod e).trans ((Witt.prodAssoc _ _ _).symm.trans
      ((hyperbolicSpace_prod_equiv k _).some.prod (QuadraticMap.IsometryEquiv.refl _)))
  have hrad := radical_prod_eq_bot (nondegenerate_hyperbolicSpace K k) hQ
  exact (eq_wittIndex _ hrad ha ⟨e2⟩).symm

/-- The Gram determinant of the polar form of `S` is `c ^ 2 * d` (`c ≠ 0`) in every basis. -/
def SqDet {V : Type*} [AddCommGroup V] [Module K V] (S : QuadraticForm K V) (d : K) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V),
    ∃ c : K, c ≠ 0 ∧ (LinearMap.BilinForm.toMatrix b (polarBilin S)).det = c ^ 2 * d

theorem sqDet_of_basis {V : Type*} [AddCommGroup V] [Module K V] {S : QuadraticForm K V} {d : K}
    {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀] (b₀ : Module.Basis ι₀ K V) (c₀ : K) (hc₀ : c₀ ≠ 0)
    (h₀ : (LinearMap.BilinForm.toMatrix b₀ (polarBilin S)).det = c₀ ^ 2 * d) : SqDet S d := by
  intro ι _ _ b
  let e : ι ≃ ι₀ := b.indexEquiv b₀
  let b₁ : Module.Basis ι K V := b₀.reindex e.symm
  have hG : LinearMap.BilinForm.toMatrix b₁ (polarBilin S) =
      (LinearMap.BilinForm.toMatrix b₀ (polarBilin S)).submatrix e e := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply, b₁]
  have hP := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix b₁ b (polarBilin S)
  have hu : IsUnit (b₁.toMatrix b).det := by
    have := b₁.isUnit_det b
    rwa [Module.Basis.det_apply] at this
  refine ⟨(b₁.toMatrix b).det * c₀, mul_ne_zero hu.ne_zero hc₀, ?_⟩
  rw [← hP, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hG,
    Matrix.det_submatrix_equiv_self, h₀]
  ring

theorem SqDet.of_isometryEquiv {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂]
    [Module K V₂] {S₁ : QuadraticForm K V₁} {S₂ : QuadraticForm K V₂} (e : S₁.IsometryEquiv S₂)
    {d : K} (h : SqDet S₂ d) : SqDet S₁ d := by
  intro ι _ _ b
  obtain ⟨c, hc, hd⟩ := h ι (b.map e.toLinearEquiv)
  refine ⟨c, hc, ?_⟩
  convert hd using 2
  ext i j
  simp only [LinearMap.BilinForm.toMatrix_apply, Module.Basis.map_apply, polarBilin_apply_apply]
  have h3 : ∀ x y : V₁, polar S₂ (e x) (e y) = polar S₁ x y := fun x y => by
    have hm : ∀ z, S₂ (e z) = S₁ z := fun z => e.map_app z
    show S₂ (e x + e y) - S₂ (e x) - S₂ (e y) = S₁ (x + y) - S₁ x - S₁ y
    rw [← map_add e x y, hm, hm, hm]
  exact (h3 _ _).symm

/-- **Decomposition of a Gram determinant over an orthogonal sum.** -/
theorem SqDet.prod {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂]
    [Module K V₂] [FiniteDimensional K V₁] [FiniteDimensional K V₂] {S₁ : QuadraticForm K V₁}
    {S₂ : QuadraticForm K V₂} {d₁ d₂ : K} (h₁ : SqDet S₁ d₁) (h₂ : SqDet S₂ d₂) :
    SqDet (S₁.prod S₂) (d₁ * d₂) := by
  obtain ⟨c₁, hc₁, hd₁⟩ := h₁ _ (Module.finBasis K V₁)
  obtain ⟨c₂, hc₂, hd₂⟩ := h₂ _ (Module.finBasis K V₂)
  refine sqDet_of_basis ((Module.finBasis K V₁).prod (Module.finBasis K V₂)) (c₁ * c₂)
    (mul_ne_zero hc₁ hc₂) ?_
  have : LinearMap.BilinForm.toMatrix ((Module.finBasis K V₁).prod (Module.finBasis K V₂))
      (polarBilin (S₁.prod S₂)) = Matrix.fromBlocks
        (LinearMap.BilinForm.toMatrix (Module.finBasis K V₁) (polarBilin S₁)) 0 0
        (LinearMap.BilinForm.toMatrix (Module.finBasis K V₂) (polarBilin S₂)) := by
    ext (i | i) (j | j) <;>
    simp [LinearMap.BilinForm.toMatrix_apply, polar]
  rw [this, Matrix.det_fromBlocks_zero₂₁, hd₁, hd₂]
  ring

/-- **Decomposition of a Gram determinant over an orthogonal sum.** -/
theorem sqDet_hyperbolicPlane : SqDet (hyperbolicPlane K) (-1) := by
  refine sqDet_of_basis (Module.Basis.finTwoProd K) 1 one_ne_zero ?_
  rw [Matrix.det_fin_two]
  simp [LinearMap.BilinForm.toMatrix_apply, polar_hyperbolicPlane]

theorem sqDet_hyperbolicSpace (m : ℕ) : SqDet (hyperbolicSpace K m) ((-1) ^ m) := by
  induction m with
  | zero =>
    refine sqDet_of_basis (ι₀ := Fin 0) (Module.Basis.empty _) 1 one_ne_zero ?_
    simp
  | succ m ih =>
    have := (sqDet_hyperbolicPlane (K := K)).prod ih
    rw [show ((-1 : K) ^ (m + 1)) = -1 * (-1) ^ m by ring]
    exact SqDet.of_isometryEquiv (Witt.hyperbolicSpaceSucc m).symm this

theorem sqDet_weightedSumSquares {t : ℕ} (a : Fin t → K) :
    SqDet (weightedSumSquares K a) (2 ^ t * ∏ i, a i) := by
  refine sqDet_of_basis (Pi.basisFun K (Fin t)) 1 one_ne_zero ?_
  have : LinearMap.BilinForm.toMatrix (Pi.basisFun K (Fin t)) (polarBilin (weightedSumSquares K a)) =
      Matrix.diagonal (fun i => 2 * a i) := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply, polar, weightedSumSquares_apply, Matrix.diagonal_apply]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    calc _ = ∑ x, 2 * a x * ((Pi.single i (1 : K) : Fin t → K) x * (Pi.single j (1 : K) : Fin t → K) x) :=
          Finset.sum_congr rfl fun x _ => by ring
      _ = _ := by
        by_cases hij : i = j
        · subst hij; simp [Pi.single_apply]
        · simp only [hij, ite_false]
          refine Finset.sum_eq_zero fun x _ => ?_
          by_cases hx : x = i
          · subst hx; simp [Ne.symm hij]
          · simp [Pi.single_apply, hx]
  rw [this, Matrix.det_diagonal, Finset.prod_mul_distrib]
  simp

theorem exists_witt_diag_aux (h2 : (2 : K) ≠ 0) (Q : QuadForm K n) (hQ : Q.Nondegenerate) :
    2 * wittIndex Q.toQuadraticForm ≤ n ∧
    ∃ a : Fin (n - 2 * wittIndex Q.toQuadraticForm) → K,
      (∀ x : Fin (n - 2 * wittIndex Q.toQuadraticForm) → K, ∑ i, a i * x i ^ 2 = 0 → x = 0) ∧
      (∃ c : K, c ≠ 0 ∧ Q.hessian.det =
        c ^ 2 * (-1) ^ wittIndex Q.toQuadraticForm * 2 ^ (n - 2 * wittIndex Q.toQuadraticForm) * ∏ i, a i) ∧
      Q.toQuadraticForm.Equivalent
        ((hyperbolicSpace K (wittIndex Q.toQuadraticForm)).prod (weightedSumSquares K a)) := by
  have hnd : (polarBilin Q.toQuadraticForm).Nondegenerate := by
    have h := QuadForm.nondegenerate_polarBilin_toQuadraticFormIn (K := K) (Q := Q) hQ
    have e : Q.toQuadraticFormIn K = Q.toQuadraticForm := by
      unfold QuadForm.toQuadraticFormIn
      congr 1
    rw [e] at h; exact h
  have hrad := radical_eq_bot_of_nondegenerate _ hnd
  obtain ⟨U, _, _, _, Qa, ha, ⟨e⟩⟩ := wittIndex_spec _ hrad
  have hdim' := e.toLinearEquiv.finrank_eq
  simp [Module.finrank_prod, Module.finrank_pi_fintype] at hdim'
  have hdim : finrank K U = n - 2 * wittIndex Q.toQuadraticForm := by omega
  have hle : 2 * wittIndex Q.toQuadraticForm ≤ n := by omega
  have key : ∀ t, finrank K U = t → ∃ a : Fin t → K, Qa.Equivalent (weightedSumSquares K a) := by
    intro t ht
    subst ht
    have : Invertible (2 : K) := invertibleOfNonzero h2
    exact equivalent_weightedSumSquares Qa
  obtain ⟨a, ha'⟩ := key _ hdim
  have hE : Q.toQuadraticForm.Equivalent
      ((hyperbolicSpace K (wittIndex Q.toQuadraticForm)).prod (weightedSumSquares K a)) :=
    ⟨e.trans ((QuadraticMap.IsometryEquiv.refl _).prod ha'.some)⟩
  have hanis : (weightedSumSquares K a).Anisotropic :=
    Witt.anisotropic_of_isometryEquiv ha'.some.symm ha
  refine ⟨hle, a, ?_, ?_, hE⟩
  · intro x hx
    apply hanis x
    rw [weightedSumSquares_apply]
    simpa [smul_eq_mul, _root_.sq] using hx
  · have hS := (sqDet_hyperbolicSpace (K := K) (wittIndex Q.toQuadraticForm)).prod
      (sqDet_weightedSumSquares a)
    have hS' := SqDet.of_isometryEquiv hE.some hS
    obtain ⟨c, hc, hd⟩ := hS' (Fin n) (Pi.basisFun K (Fin n))
    refine ⟨c, hc, ?_⟩
    have hG : LinearMap.BilinForm.toMatrix (Pi.basisFun K (Fin n)) (polarBilin Q.toQuadraticForm) =
        Q.hessian := by
      ext i j
      have h : Q.eval (Pi.single i 1 + Pi.single j 1) - Q.eval (Pi.single i 1) - Q.eval (Pi.single j 1) =
          dotProduct (Pi.single i 1 : Fin n → K) ((Q.hessian.map (algebraMap K K)).mulVec (Pi.single j 1 : Fin n → K)) :=
        QuadForm.polar_eq_hessian K Q (Pi.single i 1) (Pi.single j 1)
      simp only [LinearMap.BilinForm.toMatrix_apply, polarBilin_apply_apply, polar,
        QuadForm.toQuadraticForm_apply, Pi.basisFun_apply]
      rw [h]
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hG] at hd
    rw [hd]
    ring

/-- **Witt decomposition with a diagonal anisotropic part, and its determinant** (the normal form (2.9) of Hanke's
thesis, p. 6, over any field with $2\ne0$): for $Q$ nondegenerate with Witt index $w$ and $t = n - 2w$, there are
$a_0,\dots,a_{t-1}$ with $\langle a_0,\dots,a_{t-1}\rangle$ anisotropic, $Q\cong\mathbb H^w\perp\langle a\rangle$ and
$\det H_Q = c^2(-1)^w2^t\prod_ia_i$ for some $c\ne0$. -/
theorem exists_witt_diag (h2 : (2 : K) ≠ 0) (Q : QuadForm K n) (hQ : Q.Nondegenerate) :
    ∃ a : Fin (n - 2 * wittIndex Q.toQuadraticForm) → K,
      (∀ x : Fin (n - 2 * wittIndex Q.toQuadraticForm) → K, ∑ i, a i * x i ^ 2 = 0 → x = 0) ∧
      (∃ c : K, c ≠ 0 ∧ Q.hessian.det =
        c ^ 2 * (-1) ^ wittIndex Q.toQuadraticForm * 2 ^ (n - 2 * wittIndex Q.toQuadraticForm) * ∏ i, a i) ∧
      Q.toQuadraticForm.Equivalent
        ((hyperbolicSpace K (wittIndex Q.toQuadraticForm)).prod (weightedSumSquares K a)) := by
  exact (exists_witt_diag_aux h2 Q hQ).2

/-- **Discriminant and the dimension $t$ of the anisotropic kernel, $n$ even** (Hanke thesis, §3, p. 8 and the remark
after Theorem 6.3, p. 21): with $\delta = (-1)^{n/2}\det H_Q$, $t = 0$ gives $\delta$ a square, $t = 2$ gives $\delta$ a
non-square, and $t = 4$ gives $\delta$ a square provided every diagonal quaternary form of non-square determinant is
isotropic (`hquat`; true over every completion of a number field, `LocalRankFive.isotropic_four_of_not_isSquare`). -/
theorem even_disc_of_anisoDim (h2 : (2 : K) ≠ 0) (Q : QuadForm K n) (hQ : Q.Nondegenerate) (hn : Even n) :
    (n - 2 * wittIndex Q.toQuadraticForm = 0 → IsSquare ((-1) ^ (n / 2) * Q.hessian.det)) ∧
    (n - 2 * wittIndex Q.toQuadraticForm = 2 → ¬ IsSquare ((-1) ^ (n / 2) * Q.hessian.det)) ∧
    ((∀ b : Fin 4 → K, (∀ i, b i ≠ 0) → ¬ IsSquare (b 0 * b 1 * b 2 * b 3) →
        ∃ x : Fin 4 → K, x ≠ 0 ∧ ∑ i, b i * x i ^ 2 = 0) →
      n - 2 * wittIndex Q.toQuadraticForm = 4 → IsSquare ((-1) ^ (n / 2) * Q.hessian.det)) := by
  obtain ⟨hle, a, hanis, ⟨c, hc, hdet⟩, -⟩ := exists_witt_diag_aux h2 Q hQ
  obtain ⟨r, hr⟩ := hn
  generalize wittIndex Q.toQuadraticForm = w at *
  generalize ht : n - 2 * w = t at *
  have hane : ∀ i, a i ≠ 0 := by
    intro i hi
    have h := hanis (Pi.single i 1) (by simp [Pi.single_apply, hi])
    have := congrFun h i
    simp at this
  have hdelta : (-1) ^ (n / 2) * Q.hessian.det = (-1) ^ (t / 2) * (c ^ 2 * 2 ^ t * ∏ i, a i) := by
    have hn2 : n / 2 = w + t / 2 := by omega
    have hsq : (-1 : K) ^ w * (-1) ^ w = 1 := by rw [← mul_pow]; simp
    rw [hdet, hn2, pow_add]
    linear_combination ((-1 : K) ^ (t / 2) * c ^ 2 * 2 ^ t * ∏ i, a i) * hsq
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    subst h0
    exact ⟨c, by rw [hdelta]; simp [pow_two]⟩
  · intro h0 hsqr
    subst h0
    obtain ⟨s, hs⟩ := hsqr
    have h2c : 2 * c ≠ 0 := mul_ne_zero h2 hc
    have hs' : s * s = -((2 * c) ^ 2 * (a 0 * a 1)) := by
      rw [← hs, hdelta, Fin.prod_univ_two, show 2 / 2 = 1 from rfl]; ring
    have hrr : (s / (2 * c)) * (s / (2 * c)) = -(a 0 * a 1) := by
      field_simp
      linear_combination hs'
    have hz := hanis ![s / (2 * c), a 0] (by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination (a 0) * hrr)
    have := congrFun hz 1
    exact hane 0 (by simpa using this)
  · intro hquat h0
    subst h0
    by_cases hsqr : IsSquare (∏ i, a i)
    · obtain ⟨u, hu⟩ := hsqr
      exact ⟨4 * c * u, by rw [hdelta, hu]; norm_num; ring⟩
    · exfalso
      obtain ⟨x, hx0, hx⟩ := hquat a hane (by simpa [Fin.prod_univ_four] using hsqr)
      exact hx0 (hanis x hx)

end Generic

end QuadFormsKB.Hanke2005
