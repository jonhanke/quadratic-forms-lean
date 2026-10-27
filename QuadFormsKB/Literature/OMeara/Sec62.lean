/-
# O'Meara §62: quadratic spaces over finite fields

**Setting.** $F$ is a finite field of $q$ elements whose characteristic is not $2$ (`ringChar F ≠ 2`; O'Meara's
standing assumption of Part Three), and $(V, Q)$, $(U, Q_U)$ are finite-dimensional quadratic spaces over $F$ (Mathlib
`QuadraticForm F V`); *regular* means `Q.radical = ⊥`.

**Discriminant.** O'Meara's discriminant $dV \in \dot F/\dot F^{2}$ is the class of $d(x_1, \dots, x_n) =
\det(B(x_i, x_j))$ for any base $x_1, \dots, x_n$ of $V$ (§41B, p. 87), where $B$ is his bilinear form with
$B(x, x) = Q(x)$ (`OMeara.bil`, `OMeara.gram`, `Sec82.lean`). Statements below take bases explicitly and write
"$dU = dV$" as $d(\text{base of } U) = t^{2}\, d(\text{base of } V)$ for some $t \ne 0$.

**Proves** (§62, pp. 157–158)
* `isSquare_or_isSquare_mul` (p. 157): every nonzero element is a square or a square times a fixed non-square;
* Proposition 62:1 (p. 157): a regular space of dimension $n \ge 2$ is universal (`isUniversal_of_two_le`);
* Corollary 62:1a (p. 157): $V \cong \langle 1\rangle \perp \cdots \perp \langle 1\rangle \perp \langle dV\rangle$
  (`equivalent_one_disc`), and there are exactly two regular spaces of each dimension $n \ge 1$
  (`equivalent_one_or_nonsquare`, `not_equivalent_one_nonsquare`);
* Corollary 62:1b (p. 158): $V$ is isotropic if $n \ge 3$ (`not_anisotropic_of_three_le`);
* Theorem 62:2 (p. 158): $U \cong V$ if and only if $\dim U = \dim V$ and $dU = dV$ (`equivalent_iff_finrank_disc`);
* Remark 62:3 (p. 158): $\langle\alpha\rangle \perp \langle\beta\rangle$ represents $1$ (`exists_sq_add_sq_eq_one`),
  so every quaternion algebra is $\left(\frac{1,-1}{F}\right)$ (`quat_finite_equiv`).
-/
import QuadFormsKB.Literature.OMeara.Sec61B
import QuadFormsKB.Literature.OMeara.Sec82

open QuadraticMap QuadraticForm Module
open scoped Quaternion Polynomial Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {F : Type*} [Field F] [Fintype F]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {U : Type*} [AddCommGroup U] [Module F U] [FiniteDimensional F U]

/-! ### Auxiliary lemmas (no `@[kb]`) -/

section Aux

theorem nonsq_mul_nonsq {a b : F} (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) : IsSquare (a * b) := by
  classical
  have ha0 : a ≠ 0 := fun h => ha (h ▸ ⟨0, by simp⟩)
  have hb0 : b ≠ 0 := fun h => hb (h ▸ ⟨0, by simp⟩)
  rw [← quadraticChar_one_iff_isSquare (mul_ne_zero ha0 hb0), map_mul,
    quadraticChar_neg_one_iff_not_isSquare.mpr ha, quadraticChar_neg_one_iff_not_isSquare.mpr hb]
  norm_num

theorem exists_eq_mul_sq_of_nonsq {a ε : F} (ha : ¬ IsSquare a) (hε : ¬ IsSquare ε) :
    ∃ t : F, t ≠ 0 ∧ a = ε * t ^ 2 := by
  have hε0 : ε ≠ 0 := fun h => hε (h ▸ ⟨0, by simp⟩)
  have ha0 : a ≠ 0 := fun h => ha (h ▸ ⟨0, by simp⟩)
  obtain ⟨s, hs⟩ := nonsq_mul_nonsq ha hε
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
    rcases hs with h | h <;> contradiction
  refine ⟨s / ε, div_ne_zero hs0 hε0, ?_⟩
  field_simp
  linear_combination hs

theorem exists_sq_add_sq_eq_one' (hF : ringChar F ≠ 2) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ x y : F, a * x ^ 2 + b * y ^ 2 = 1 := by
  have h := FiniteField.exists_root_sum_quadratic (f := Polynomial.C a * Polynomial.X ^ 2)
    (g := Polynomial.C b * Polynomial.X ^ 2 - Polynomial.C 1) (by
      rw [Polynomial.degree_C_mul_X_pow 2 ha]; rfl) (by
      rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;>
      rw [Polynomial.degree_C_mul_X_pow 2 hb] <;> simp)
    (FiniteField.odd_card_of_char_ne_two hF)
  obtain ⟨x, y, h⟩ := h
  refine ⟨x, y, ?_⟩
  simp at h
  linear_combination h

section Gram
variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {U : Type*} [AddCommGroup U] [Module K U]

/-- Two bases of the same space with the same index type: the Gram determinants differ by a nonzero square. -/
theorem gram_basis_change (Q : QuadraticForm K V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b c : Basis ι K V) : ∃ t : K, t ≠ 0 ∧ (gram Q c).det = t ^ 2 * (gram Q b).det := by
  let T : Matrix ι ι K := Matrix.of fun j i => b.repr (c j) i
  have hc : (fun j => c j) = fun j => ∑ i, T j i • b i := by
    funext j
    exact (b.sum_repr (c j)).symm
  have hg : gram Q (fun j => c j) = T * gram Q b * Tᵀ := by
    rw [hc, gram_comb (R := K)]
    simp
  have hT : T.det ≠ 0 := by
    have := (b.isUnit_det c).ne_zero
    rw [Basis.det_apply] at this
    have hTT : b.toMatrix c = Tᵀ := by ext i j; simp [T, Basis.toMatrix_apply]
    rwa [hTT, Matrix.det_transpose] at this
  refine ⟨T.det, hT, ?_⟩
  have : gram Q c = gram Q (fun j => c j) := rfl
  rw [this, hg, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- Two bases of the same space: the Gram determinants differ by a nonzero square. -/
theorem gram_basis_change' (Q : QuadraticForm K V) {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (c : Basis κ K V) :
    ∃ t : K, t ≠ 0 ∧ (gram Q b).det = t ^ 2 * (gram Q c).det := by
  have hcard : Fintype.card κ = Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis b, ← Module.finrank_eq_card_basis c]
  let σ : κ ≃ ι := Fintype.equivOfCardEq hcard
  obtain ⟨t, ht, h⟩ := gram_basis_change Q (c.reindex σ) b
  have : gram Q (c.reindex σ) = (gram Q c).submatrix σ.symm σ.symm := by
    ext i j; simp [gram]
  rw [this, Matrix.det_submatrix_equiv_self] at h
  exact ⟨t, ht, h⟩

theorem gram_isometryEquiv {Q : QuadraticForm K V} {Q' : QuadraticForm K U} (e : Q.IsometryEquiv Q')
    {ι : Type*} (x : ι → V) : gram Q' (fun i => e (x i)) = gram Q x := by
  ext i j
  simp only [gram, Matrix.of_apply, bil, QuadraticMap.associated_apply]
  rw [← map_add, e.map_app, e.map_app, e.map_app]

theorem bil_wss {n : ℕ} (w : Fin n → K) (x y : Fin n → K) :
    bil (weightedSumSquares K w) x y = ∑ k, w k * (x k * y k) := by
  simp only [bil, QuadraticMap.associated_apply, weightedSumSquares_apply, smul_eq_mul]
  have : ∑ k, w k * ((x + y) k * (x + y) k) - ∑ k, w k * (x k * x k) - ∑ k, w k * (y k * y k)
      = ∑ k, 2 * (w k * (x k * y k)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.add_apply]; ring
  rw [this, ← Finset.mul_sum]
  simp [Algebra.smul_def, ← mul_assoc]

theorem gram_wss {n : ℕ} (w : Fin n → K) :
    gram (weightedSumSquares K w) (Pi.basisFun K (Fin n)) = Matrix.diagonal w := by
  ext i j
  simp only [gram, Matrix.of_apply, bil_wss, Pi.basisFun_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp [Pi.single_apply]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = i
    · subst hk; simp [Pi.single_apply, Ne.symm h]
    · simp [Pi.single_apply, hk]

theorem gram_det_of_equiv {Q : QuadraticForm K V} {n : ℕ} {w : Fin n → K}
    (h : Q.Equivalent (weightedSumSquares K w)) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) : ∃ t : K, t ≠ 0 ∧ (gram Q b).det = t ^ 2 * ∏ i, w i := by
  obtain ⟨e⟩ := h
  let b' : Basis (Fin n) K V := (Pi.basisFun K (Fin n)).map e.symm.toLinearEquiv
  have hb' : gram Q b' = Matrix.diagonal w := by
    rw [← gram_wss]
    exact gram_isometryEquiv e.symm (Pi.basisFun K (Fin n))
  obtain ⟨t, ht, h⟩ := gram_basis_change' Q b b'
  exact ⟨t, ht, by rw [h, hb', Matrix.det_diagonal]⟩

theorem exists_diag (Q : QuadraticForm K V) (hQ : Q.radical = ⊥) {n : ℕ}
    (hn : finrank K V = n) :
    ∃ w : Fin n → Kˣ, Q.Equivalent (weightedSumSquares K fun i => (w i : K)) := by
  subst hn
  have hsep : (QuadraticMap.associated (R := K) Q).SeparatingLeft := by
    rw [LinearMap.separatingLeft_iff_ker_eq_bot, ← QuadraticMap.radical_eq_ker_associated]
    exact hQ
  obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hsep
  refine ⟨w, ⟨?_⟩⟩
  exact e.trans (weightedSumSquaresCongr (by ext; simp))

end Gram

section Split
variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- The orthogonal complement `v^⊥` of a vector `v` (kernel of `B(v, ·)`). -/
abbrev Wperp (Q : QuadraticForm K V) (v : V) : Submodule K V :=
  LinearMap.ker ((QuadraticMap.associated (R := K) Q) v)

theorem mem_Wperp (Q : QuadraticForm K V) (v y : V) : y ∈ Wperp Q v ↔ bil Q v y = 0 := Iff.rfl

/-- `K × K^k ≃ K^(k+1)` by `Fin.cons`. -/
def consEquiv (K : Type*) [Field K] (k : ℕ) : (K × (Fin k → K)) ≃ₗ[K] (Fin (k + 1) → K) where
  toFun p := Fin.cons p.1 p.2
  invFun f := (f 0, Fin.tail f)
  map_add' p q := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c p := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  left_inv p := by simp
  right_inv f := by simp

theorem wperp_aux (Q : QuadraticForm K V) {v : V} (ha : Q v ≠ 0) (x : V) :
    x - (((Q v)⁻¹ * bil Q v x) • v) ∈ Wperp Q v := by
  rw [mem_Wperp, bil_sub_right, bil_smul_right, bil_self]
  field_simp
  ring

/-- `V ≃ K × v^⊥` when `Q v ≠ 0`. -/
def splitEquiv (Q : QuadraticForm K V) {v : V} (ha : Q v ≠ 0) : V ≃ₗ[K] (K × Wperp Q v) where
  toFun x := ((Q v)⁻¹ * bil Q v x, ⟨x - (((Q v)⁻¹ * bil Q v x) • v), wperp_aux Q ha x⟩)
  invFun p := p.1 • v + (p.2 : V)
  map_add' x y := by
    refine Prod.ext (by simp [bil_add_right, mul_add]) (Subtype.ext ?_)
    simp [bil_add_right, mul_add, add_smul]
    abel
  map_smul' c x := by
    refine Prod.ext (by simp [bil_smul_right]; ring) (Subtype.ext ?_)
    simp [bil_smul_right, smul_sub, smul_smul, mul_assoc, mul_left_comm]
  left_inv x := by simp
  right_inv p := by
    obtain ⟨c, y, hy⟩ := p
    have hy' : bil Q v y = 0 := hy
    have h1 : bil Q v (c • v + y) = c * Q v := by
      rw [bil_add_right, bil_smul_right, bil_self, hy', add_zero]
    have h2 : (Q v)⁻¹ * bil Q v (c • v + y) = c := by
      rw [h1]; field_simp
    refine Prod.ext (by simpa using h2) (Subtype.ext ?_)
    simp only
    rw [h2]; abel

theorem equivalent_cons (Q : QuadraticForm K V) {v : V} (ha : Q v ≠ 0) {k : ℕ} {w : Fin k → K}
    (h : (Q.comp (Wperp Q v).subtype).Equivalent (weightedSumSquares K w)) :
    Q.Equivalent (weightedSumSquares K (Fin.cons (Q v) w : Fin (k + 1) → K)) := by
  obtain ⟨e⟩ := h
  refine ⟨{ (splitEquiv Q ha).trans ((LinearEquiv.prodCongr (LinearEquiv.refl K K)
    e.toLinearEquiv).trans (consEquiv K k)) with map_app' := fun x => ?_ }⟩
  set c : K := (Q v)⁻¹ * bil Q v x with hc
  have hy : bil Q v (x - c • v) = 0 := wperp_aux Q ha x
  have hQy := e.map_app ⟨x - c • v, wperp_aux Q ha x⟩
  have hx : Q x = c ^ 2 * Q v + Q (x - c • v) := by
    have : x = c • v + (x - c • v) := by abel
    conv_lhs => rw [this]
    rw [Q_add, bil_smul_left, hy, Q_smul]; ring
  have hQy' : Q (x - c • v) = (weightedSumSquares K w) (e ⟨x - c • v, wperp_aux Q ha x⟩) := by
    rw [hQy]; rfl
  rw [hx, hQy']
  simp [weightedSumSquares_apply, Fin.sum_univ_succ, consEquiv, splitEquiv, ← hc]
  rw [hQy', weightedSumSquares_apply]
  simp only [smul_eq_mul]
  ring

theorem radical_comp_wperp (Q : QuadraticForm K V) {v : V} (ha : Q v ≠ 0) (hQ : Q.radical = ⊥) :
    (Q.comp (Wperp Q v).subtype).radical = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [QuadraticMap.radical_eq_ker_associated, LinearMap.mem_ker] at hy
  have hyv : bil Q v y = 0 := y.2
  have hy0 : (y : V) ∈ Q.radical := by
    rw [QuadraticMap.radical_eq_ker_associated, LinearMap.mem_ker]
    refine LinearMap.ext fun x => ?_
    have hz : ∀ z : Wperp Q v, bil Q y z = 0 := fun z => by
      have := LinearMap.congr_fun hy z
      simpa [QuadraticMap.associated_apply] using this
    have hx : x = ((Q v)⁻¹ * bil Q v x) • v + (x - (((Q v)⁻¹ * bil Q v x) • v)) := by abel
    have h1 : bil Q (y : V) x = 0 := by
      rw [hx, bil_add_right, bil_smul_right, bil_comm Q (y : V) v, hyv,
        hz ⟨_, wperp_aux Q ha x⟩]
      simp
    simpa using h1
  rw [hQ] at hy0
  exact (Submodule.mem_bot K).mpr (Subtype.ext ((Submodule.mem_bot K).mp hy0))

theorem finrank_wperp (Q : QuadraticForm K V) [FiniteDimensional K V] {v : V} (ha : Q v ≠ 0) :
    finrank K V = finrank K (Wperp Q v) + 1 := by
  rw [(splitEquiv Q ha).finrank_eq, Module.finrank_prod, finrank_self]; ring

end Split

section FinField
variable {F : Type*} [Field F] [Fintype F]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem wss_supp {n : ℕ} (w x : Fin n → F) (S : Finset (Fin n)) (hS : ∀ k ∉ S, x k = 0) :
    weightedSumSquares F w x = ∑ k ∈ S, w k * (x k * x k) := by
  rw [weightedSumSquares_apply]
  simp only [smul_eq_mul]
  exact (Finset.sum_subset (Finset.subset_univ S) fun k _ hk => by simp [hS k hk]).symm

theorem wss_represents_two {n : ℕ} (hF : ringChar F ≠ 2) {w : Fin n → F} (hn : 2 ≤ n)
    (hw : ∀ i, w i ≠ 0) (c : F) : ∃ x, weightedSumSquares F w x = c := by
  by_cases hc : c = 0
  · exact ⟨0, by simp [hc]⟩
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  obtain ⟨s, t, h⟩ := exists_sq_add_sq_eq_one' hF (a := w i0 / c) (b := w i1 / c)
    (div_ne_zero (hw _) hc) (div_ne_zero (hw _) hc)
  refine ⟨Pi.single i0 s + Pi.single i1 t, ?_⟩
  rw [wss_supp w _ {i0, i1} (by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    simp [Pi.single_apply, hk.1, hk.2])]
  rw [Finset.sum_pair hne]
  simp [Pi.single_apply, hne, hne.symm]
  field_simp at h
  linear_combination h

theorem isUniversal_of_two_le' (hF : ringChar F ≠ 2) (Q : QuadraticForm F V) (hQ : Q.radical = ⊥)
    (hn : 2 ≤ finrank F V) : ∀ a : F, ∃ x : V, Q x = a := by
  haveI : Invertible (2 : F) := invertibleOfNonzero (Ring.two_ne_zero hF)
  obtain ⟨w, ⟨e⟩⟩ := exists_diag Q hQ (rfl : finrank F V = finrank F V)
  intro a
  obtain ⟨x, hx⟩ := wss_represents_two hF hn (fun i => (w i).ne_zero) a
  exact ⟨e.symm x, by rw [e.symm.map_app, hx]⟩

theorem not_anisotropic_of_three_le' (hF : ringChar F ≠ 2) (Q : QuadraticForm F V)
    (hn : 3 ≤ finrank F V) : ¬ Q.Anisotropic := by
  haveI : Invertible (2 : F) := invertibleOfNonzero (Ring.two_ne_zero hF)
  obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares
  rw [QuadraticMap.not_anisotropic_iff_exists]
  by_cases h : ∃ i, w i = 0
  · obtain ⟨i, hi⟩ := h
    refine ⟨e.symm (Pi.single i 1), ?_, ?_⟩
    · intro h0
      have := e.symm.toLinearEquiv.map_eq_zero_iff.mp h0
      have := congr_fun this i
      simp at this
    · rw [e.symm.map_app, wss_supp w _ {i} (by
        intro k hk
        simp only [Finset.mem_singleton] at hk
        simp [Pi.single_apply, hk])]
      simp [hi]
  · push_neg at h
    let i0 : Fin (finrank F V) := ⟨0, by omega⟩
    let i1 : Fin (finrank F V) := ⟨1, by omega⟩
    let i2 : Fin (finrank F V) := ⟨2, by omega⟩
    have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
    have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
    obtain ⟨s, t, hst⟩ := exists_sq_add_sq_eq_one' hF (a := -w i0 / w i2) (b := -w i1 / w i2)
      (div_ne_zero (neg_ne_zero.mpr (h _)) (h _)) (div_ne_zero (neg_ne_zero.mpr (h _)) (h _))
    refine ⟨e.symm (Pi.single i0 s + Pi.single i1 t + Pi.single i2 1), ?_, ?_⟩
    · intro h0
      have := e.symm.toLinearEquiv.map_eq_zero_iff.mp h0
      have := congr_fun this i2
      simp [Pi.single_apply, h02.symm, h12.symm] at this
    · rw [e.symm.map_app, wss_supp w _ {i0, i1, i2} (by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
        simp [Pi.single_apply, hk.1, hk.2.1, hk.2.2])]
      rw [Finset.sum_insert (by simp [h01, h02]), Finset.sum_pair h12]
      simp [Pi.single_apply, h01, h01.symm, h02, h02.symm, h12, h12.symm]
      have h2 := h i2
      field_simp at hst
      linear_combination (-1 : F) * hst

theorem prod_snoc_one (m : ℕ) (δ : F) :
    ∏ i, (Fin.snoc (fun _ : Fin m => (1 : F)) δ : Fin (m + 1) → F) i = δ := by
  rw [Fin.prod_univ_castSucc]; simp

theorem snoc_equiv (m : ℕ) {δ δ' t : F} (ht : t ≠ 0) (h : δ = δ' * t ^ 2) :
    (weightedSumSquares F (Fin.snoc (fun _ : Fin m => (1 : F)) δ : Fin (m + 1) → F)).Equivalent
    (weightedSumSquares F (Fin.snoc (fun _ : Fin m => (1 : F)) δ' : Fin (m + 1) → F)) := by
  refine ⟨isometryEquivWeightedSumSquaresWeightedSumSquares
    (Fin.snoc (fun _ : Fin m => (1 : Fˣ)) (Units.mk0 t ht) : Fin (m + 1) → Fˣ) ?_⟩
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [h]
  · simp

universe u in
/-- Every regular space of dimension `m + 1` is `⟨1, …, 1, δ⟩` for some `δ ≠ 0`. -/
theorem exists_one_snoc (hF : ringChar F ≠ 2) : ∀ (m : ℕ) {W : Type u} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (Q : QuadraticForm F W), Q.radical = ⊥ → finrank F W = m + 1 →
    ∃ δ : F, δ ≠ 0 ∧
      Q.Equivalent (weightedSumSquares F (Fin.snoc (fun _ : Fin m => (1 : F)) δ : Fin (m + 1) → F)) := by
  haveI : Invertible (2 : F) := invertibleOfNonzero (Ring.two_ne_zero hF)
  intro m
  induction m with
  | zero =>
    intro W _ _ _ Q hQ hn
    obtain ⟨w, ⟨e⟩⟩ := exists_diag Q hQ hn
    refine ⟨w 0, (w 0).ne_zero, ?_⟩
    have : (Fin.snoc (fun _ : Fin 0 => (1 : F)) (w 0 : F) : Fin (0 + 1) → F) = fun i => (w i : F) := by
      funext i
      fin_cases i
      simp [Fin.snoc]
    rw [this]
    exact ⟨e⟩
  | succ m ih =>
    intro W _ _ _ Q hQ hn
    obtain ⟨v, hv⟩ := isUniversal_of_two_le' hF Q hQ (by omega) 1
    have ha : Q v ≠ 0 := by rw [hv]; exact one_ne_zero
    have hfin := finrank_wperp Q ha
    obtain ⟨δ, hδ, hE⟩ := ih (Q.comp (Wperp Q v).subtype) (radical_comp_wperp Q ha hQ) (by omega)
    refine ⟨δ, hδ, ?_⟩
    have := equivalent_cons Q ha hE
    rw [hv] at this
    have hfun : (Fin.cons (1 : F) (Fin.snoc (fun _ : Fin m => (1 : F)) δ : Fin (m + 1) → F) :
        Fin (m + 1 + 1) → F) = Fin.snoc (fun _ : Fin (m + 1) => (1 : F)) δ := by
      rw [Fin.cons_snoc_eq_snoc_cons]
      congr 1
      funext j
      refine Fin.cases rfl (fun _ => rfl) j
    rw [hfun] at this
    exact this

end FinField

end Aux

/-- **Every nonzero element of $F$ is a square or a square times a fixed non-square** (O'Meara 1963, §62, p. 157):
the squaring map on $\dot F$ has kernel $\{\pm 1\}$, so $(\dot F : \dot F^{2}) = 2$. Here: there is a non-square
$\epsilon$ such that every $a \ne 0$ is a square or $\epsilon$ times a square. -/
@[kb "omeara1963" "§62, p. 157 (every element is a square or a square times a fixed non-square)"]
theorem isSquare_or_isSquare_mul (hF : ringChar F ≠ 2) :
    ∃ ε : F, ¬ IsSquare ε ∧ ∀ a : F, a ≠ 0 → IsSquare a ∨ ∃ t : F, a = ε * t ^ 2 := by
  obtain ⟨ε, hε⟩ := FiniteField.exists_nonsquare hF
  refine ⟨ε, hε, fun a _ => ?_⟩
  by_cases ha : IsSquare a
  · exact Or.inl ha
  · obtain ⟨t, -, ht⟩ := exists_eq_mul_sq_of_nonsq ha hε
    exact Or.inr ⟨t, ht⟩

/-- **Proposition 62:1** (O'Meara 1963, p. 157): a regular quadratic space of dimension $n \ge 2$ over a finite field
is universal. -/
@[kb "omeara1963" "§62, 62:1, p. 157 (a regular space with n ≥ 2 is universal)"]
theorem isUniversal_of_two_le (hF : ringChar F ≠ 2) (Q : QuadraticForm F V) (hQ : Q.radical = ⊥)
    (hn : 2 ≤ finrank F V) : IsUniversal Q :=
  isUniversal_of_two_le' hF Q hQ hn

/-- **Corollary 62:1a** (O'Meara 1963, p. 157): a regular space $V$ of dimension $m + 1$ over a finite field has a
splitting $V \cong \langle 1\rangle \perp \cdots \perp \langle 1\rangle \perp \langle dV\rangle$; here $dV$ is the
discriminant $\det(B(b_i, b_j))$ of any base $b$ of $V$. -/
@[kb "omeara1963" "§62, 62:1a, p. 157 (V ≅ ⟨1⟩ ⊥ ⋯ ⊥ ⟨1⟩ ⊥ ⟨dV⟩)"]
theorem equivalent_one_disc [Invertible (2 : F)] (hF : ringChar F ≠ 2) (Q : QuadraticForm F V)
    (hQ : Q.radical = ⊥) {m : ℕ} (b : Basis (Fin (m + 1)) F V) :
    Q.Equivalent (weightedSumSquares F (Fin.snoc (fun _ : Fin m => (1 : F)) (gram Q b).det)) := by
  have hn : finrank F V = m + 1 := by simp [Module.finrank_eq_card_basis b]
  obtain ⟨δ, hδ, hE⟩ := exists_one_snoc hF m Q hQ hn
  obtain ⟨t, ht, h⟩ := gram_det_of_equiv hE b
  rw [prod_snoc_one] at h
  refine hE.trans (snoc_equiv m (t := t⁻¹) (inv_ne_zero ht) ?_)
  rw [h]
  field_simp

/-- **There are at most two regular spaces of each dimension** (O'Meara 1963, 62:1a, p. 157, "essentially two regular
quadratic spaces of given dimension"): for a non-square $\epsilon$, every regular space of dimension $m + 1$ is
isometric to $\langle 1, \dots, 1, 1\rangle$ or to $\langle 1, \dots, 1, \epsilon\rangle$. -/
@[kb "omeara1963" "§62, 62:1a, p. 157 (two regular spaces of each dimension)"]
theorem equivalent_one_or_nonsquare (hF : ringChar F ≠ 2) (Q : QuadraticForm F V) (hQ : Q.radical = ⊥)
    {m : ℕ} (hn : finrank F V = m + 1) {ε : F} (hε : ¬ IsSquare ε) :
    Q.Equivalent (weightedSumSquares F (Fin.snoc (fun _ : Fin m => (1 : F)) 1)) ∨
      Q.Equivalent (weightedSumSquares F (Fin.snoc (fun _ : Fin m => (1 : F)) ε)) := by
  obtain ⟨δ, hδ, hE⟩ := exists_one_snoc hF m Q hQ hn
  by_cases hs : IsSquare δ
  · obtain ⟨s, hs⟩ := hs
    have hs0 : s ≠ 0 := by rintro rfl; simp at hs; exact hδ hs
    exact Or.inl (hE.trans (snoc_equiv m hs0 (by rw [hs]; ring)))
  · obtain ⟨t, ht, hδt⟩ := exists_eq_mul_sq_of_nonsq hs hε
    exact Or.inr (hE.trans (snoc_equiv m ht hδt))

/-- **The two spaces are distinct** (O'Meara 1963, 62:1a, p. 157): for a non-square $\epsilon$,
$\langle 1, \dots, 1, 1\rangle \not\cong \langle 1, \dots, 1, \epsilon\rangle$ (their discriminants differ). -/
@[kb "omeara1963" "§62, 62:1a, p. 157 (the two spaces of each dimension are distinct)"]
theorem not_equivalent_one_nonsquare (hF : ringChar F ≠ 2) (m : ℕ) {ε : F} (hε : ¬ IsSquare ε) :
    ¬ (weightedSumSquares F (Fin.snoc (fun _ : Fin m => (1 : F)) 1)).Equivalent
      (weightedSumSquares F (Fin.snoc (fun _ : Fin m => (1 : F)) ε)) := by
  intro h
  haveI : Invertible (2 : F) := invertibleOfNonzero (Ring.two_ne_zero hF)
  obtain ⟨t, ht, h⟩ := gram_det_of_equiv h.symm (Pi.basisFun F (Fin (m + 1)))
  rw [gram_wss, Matrix.det_diagonal, prod_snoc_one, prod_snoc_one] at h
  exact hε ⟨t, by linear_combination h⟩

/-- **Corollary 62:1b** (O'Meara 1963, p. 158): a quadratic space of dimension $n \ge 3$ over a finite field is
isotropic. O'Meara states it for regular spaces (it is the case $d = 2$ of the Chevalley–Warning theorem, his footnote);
it holds for all spaces. -/
@[kb "omeara1963" "§62, 62:1b, p. 158 (V is isotropic if n ≥ 3)"]
theorem not_anisotropic_of_three_le (hF : ringChar F ≠ 2) (Q : QuadraticForm F V) (hn : 3 ≤ finrank F V) :
    ¬ Q.Anisotropic :=
  not_anisotropic_of_three_le' hF Q hn

/-- **Theorem 62:2** (O'Meara 1963, p. 158): regular quadratic spaces $U$, $V$ over a finite field are isometric if and
only if $\dim U = \dim V$ and $dU = dV$, i.e. the discriminants of bases $b$ of $U$ and $c$ of $V$ differ by a nonzero
square. -/
@[kb "omeara1963" "§62, 62:2, p. 158 (U ≅ V iff dim U = dim V and dU = dV)"]
theorem equivalent_iff_finrank_disc [Invertible (2 : F)] (hF : ringChar F ≠ 2) (QU : QuadraticForm F U)
    (Q : QuadraticForm F V) (hU : QU.radical = ⊥) (hV : Q.radical = ⊥) {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (b : Basis ι F U) (c : Basis κ F V) :
    QU.Equivalent Q ↔ finrank F U = finrank F V ∧ ∃ t : F, t ≠ 0 ∧ (gram QU b).det = t ^ 2 * (gram Q c).det := by
  constructor
  · rintro ⟨e⟩
    refine ⟨e.toLinearEquiv.finrank_eq, ?_⟩
    let b' : Basis ι F V := b.map e.toLinearEquiv
    have hb' : gram Q b' = gram QU b := gram_isometryEquiv e b
    obtain ⟨t, ht, h⟩ := gram_basis_change' Q b' c
    exact ⟨t, ht, by rw [← hb', h]⟩
  · rintro ⟨hfin, t, ht, hdet⟩
    cases hn : finrank F V with
    | zero =>
      obtain ⟨wU, ⟨eU⟩⟩ := exists_diag QU hU (hfin.trans hn)
      obtain ⟨wV, ⟨eV⟩⟩ := exists_diag Q hV hn
      have : (fun i => (wU i : F)) = fun i => (wV i : F) := funext fun i => i.elim0
      rw [this] at eU
      exact ⟨eU.trans eV.symm⟩
    | succ m =>
      obtain ⟨δU, hδU, hEU⟩ := exists_one_snoc hF m QU hU (hfin.trans hn)
      obtain ⟨δV, hδV, hEV⟩ := exists_one_snoc hF m Q hV hn
      obtain ⟨tU, htU, hU'⟩ := gram_det_of_equiv hEU b
      obtain ⟨tV, htV, hV'⟩ := gram_det_of_equiv hEV c
      rw [prod_snoc_one] at hU' hV'
      have key : tU ^ 2 * δU = t ^ 2 * (tV ^ 2 * δV) := by rw [← hU', hdet, hV']
      have h2 : δU = δV * (t * tV / tU) ^ 2 := by
        field_simp
        linear_combination key
      exact hEU.trans ((snoc_equiv m (div_ne_zero (mul_ne_zero ht htV) htU) h2).trans hEV.symm)

/-- **Remark 62:3, first part** (O'Meara 1963, p. 158): $\langle\alpha\rangle \perp \langle\beta\rangle$ represents $1$
whenever $\alpha, \beta \in \dot F$: $\alpha x^2 + \beta y^2 = 1$ for some $x, y \in F$. -/
@[kb "omeara1963" "§62, 62:3, p. 158 (⟨α⟩ ⊥ ⟨β⟩ represents 1)"]
theorem exists_sq_add_sq_eq_one (hF : ringChar F ≠ 2) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ x y : F, a * x ^ 2 + b * y ^ 2 = 1 :=
  exists_sq_add_sq_eq_one' hF ha hb

/-- **Remark 62:3** (O'Meara 1963, p. 158): there is one quaternion algebra over a finite field: for
$\alpha, \beta \in \dot F$, $\left(\frac{\alpha,\beta}{F}\right) \cong \left(\frac{1,-1}{F}\right)$. -/
@[kb "omeara1963" "§62, 62:3, p. 158 (every quaternion algebra over a finite field is (1,−1))"]
theorem quat_finite_equiv (hF : ringChar F ≠ 2) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    Nonempty (ℍ[F,a,b] ≃ₐ[F] ℍ[F,1,-1]) := by
  have hb' : b⁻¹ ≠ 0 := inv_ne_zero hb
  obtain ⟨x, y, h⟩ := exists_sq_add_sq_eq_one' hF hb' (b := -a * b⁻¹)
    (mul_ne_zero (neg_ne_zero.mpr ha) hb')
  refine ⟨quatEquivOneNegOne (Ring.two_ne_zero hF) ha hb (x := x) (y := y) ?_⟩
  field_simp at h
  linear_combination h

end QuadFormsKB.OMeara
