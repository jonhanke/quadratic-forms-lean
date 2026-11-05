/-
# O'Meara §93D: matrix and Hilbert-symbol tools for Example 93:18

**Setting**: $K$ a field with $2 \in K^\times$ and a quadratic space $(V, Q)$ over $K$; for the Hilbert symbols, $K$ of
characteristic $0$ satisfying `PadicClass.LocalHilbertField`.

**Proves**
* `blk2` ($A(a, \beta) \perp A(b, \gamma)$), `det_blk2`, `map_blk2`;
* `Rep` (the space has a base with a given matrix), `rep_congr_iff`, `rep_diag_iff`, `rep_diag_iff_S` (63:20 in matrix
  form: two diagonal forms of the same dimension are isometric iff they have the same discriminant and Hasse symbol);
* `rep_blk2_iff`: $A(a,\beta) \perp A(b, \gamma)$ is congruent to the diagonal matrix `dw2`;
* `hasseS_four_diff`, `hdd_of`: the Hasse-symbol computation of 93:18 (iii);
* `hilbert_delta_parity`: $(x, \Delta) = (-1)^{\operatorname{ord} x}$ for the unit $\Delta$ of quadratic defect
  $4\mathfrak o$ (63:11a).
-/
import QuadFormsKB.Literature.OMeara.Sec93Adj
import QuadFormsKB.Literature.OMeara.Sec91Local
import QuadFormsKB.Literature.OMeara.Sec63C

open QuadraticMap Submodule Module IsLocalRing
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.D18

/-- The block matrix $A(a,\beta) \perp A(b,\gamma)$. -/
def blk2 {S : Type*} [Semiring S] (a β b γ : S) : Matrix (Fin 4) (Fin 4) S :=
  Matrix.of ![![a, 1, 0, 0], ![1, β, 0, 0], ![0, 0, b, 1], ![0, 0, 1, γ]]

/-- Determinant of `blk2`. -/
theorem det_blk2 {S : Type*} [CommRing S] (a β b γ : S) :
    (blk2 a β b γ).det = (a * β - 1) * (b * γ - 1) := by
  simp [blk2, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- `blk2` commutes with ring homomorphisms. -/
theorem map_blk2 {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T) (a β b γ : S) :
    (blk2 a β b γ).map f = blk2 (f a) (f β) (f b) (f γ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [blk2]

section Rep

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

/-- The space $(V, Q)$ has a base with Gram matrix `M`. -/
def Rep {n : ℕ} (M : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ e : Basis (Fin n) K V, gram Q (fun i => e i) = M

theorem gram_comb {ι : Type*} [Fintype ι] (P : Matrix ι ι K) (e : ι → V) :
    gram Q (fun i => ∑ j, P i j • e j) = P * gram Q e * Pᵀ := by
  ext i k
  show bil Q (∑ j, P i j • e j) (∑ l, P k l • e l) = _
  rw [Matrix.mul_apply, bil_sum_left]
  simp_rw [bil_smul_left, bil_sum_right, bil_smul_right, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [gram, Matrix.of_apply]
  ring

theorem gram_change {ι : Type*} [Fintype ι] [DecidableEq ι] (e e' : Basis ι K V) :
    ∃ P : Matrix ι ι K, IsUnit P.det ∧ gram Q (fun i => e' i) = P * gram Q (fun i => e i) * Pᵀ := by
  refine ⟨Matrix.of fun i j => e.repr (e' i) j, ?_, ?_⟩
  · have : (Matrix.of fun i j => e.repr (e' i) j) = (e.toMatrix e')ᵀ := by
      ext i j; simp [Basis.toMatrix_apply]
    rw [this, Matrix.det_transpose, ← Basis.det_apply]
    exact Basis.isUnit_det e e'
  · have h : ∀ i, e' i = ∑ j, (Matrix.of fun i j => e.repr (e' i) j) i j • e j := fun i => by
      simpa using (e.sum_repr (e' i)).symm
    rw [← gram_comb]
    congr 1
    funext i
    exact h i

theorem rep_congr {n : ℕ} {M : Matrix (Fin n) (Fin n) K} (h : Rep Q M) {P : Matrix (Fin n) (Fin n) K}
    (hP : IsUnit P.det) : Rep Q (P * M * Pᵀ) := by
  obtain ⟨e, he⟩ := h
  have hPT : IsUnit (Pᵀ).det := by rwa [Matrix.det_transpose]
  refine ⟨e.map (Matrix.toLinearEquiv e Pᵀ hPT), ?_⟩
  rw [← he, ← gram_comb]
  congr 1
  funext i
  simp [Matrix.toLinearEquiv_apply, Matrix.toLin_self]

end Rep

section Pol

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

theorem dot_diag (w : Fin n → K) (x : Fin n → K) :
    x ⬝ᵥ (Matrix.diagonal w) *ᵥ x = ∑ i, w i * x i ^ 2 := by
  simp only [dotProduct, Matrix.mulVec_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem dot_congr (D P : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    x ⬝ᵥ (Pᵀ * D * P) *ᵥ x = (P *ᵥ x) ⬝ᵥ D *ᵥ (P *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- Polarization for symmetric matrices. -/
theorem mat_ext_of_quad (A B : Matrix (Fin n) (Fin n) K) (hA : Aᵀ = A) (hB : Bᵀ = B)
    (h : ∀ x, x ⬝ᵥ A *ᵥ x = x ⬝ᵥ B *ᵥ x) : A = B := by
  have key : ∀ (C : Matrix (Fin n) (Fin n) K), Cᵀ = C → (∀ x, x ⬝ᵥ C *ᵥ x = 0) → C = 0 := by
    intro C hC h0
    ext i j
    have e : ∀ i j, (Pi.single i (1 : K)) ⬝ᵥ C *ᵥ (Pi.single j 1) = C i j := by
      intro i j
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have h1 := h0 (Pi.single i 1 + Pi.single j 1)
    have h2 := h0 (Pi.single i 1)
    have h3 := h0 (Pi.single j 1)
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, e, e, e, e] at h1
    rw [e] at h2 h3
    have hji : C j i = C i j := by
      have := congrFun (congrFun hC j) i
      simpa using this.symm
    have : (2 : K) * C i j = 0 := by linear_combination h1 - h2 - h3 - hji
    simpa [Matrix.zero_apply] using (mul_eq_zero.mp this).resolve_left two_ne_zero
  have := key (A - B) (by rw [Matrix.transpose_sub, hA, hB]) (fun x => by
    rw [Matrix.sub_mulVec, dotProduct_sub, h x, sub_self])
  exact sub_eq_zero.mp this

theorem isometricIn_iff_congr (w w' : Fin n → K) :
    (QuadFormsKB.QuadForm.diag w).IsometricIn K (QuadFormsKB.QuadForm.diag w') ↔
      ∃ P : Matrix (Fin n) (Fin n) K, IsUnit P.det ∧
        Matrix.diagonal w' = P * Matrix.diagonal w * Pᵀ := by
  have ev : ∀ (v : Fin n → K) (x : Fin n → K),
      (QuadFormsKB.QuadForm.diag v).evalIn K x = x ⬝ᵥ (Matrix.diagonal v) *ᵥ x := fun v x => by
    rw [QuadFormsKB.PadicClass.evalIn_diag_self, dot_diag]
  constructor
  · rintro ⟨P0, hP0, hx⟩
    refine ⟨P0ᵀ, by rwa [Matrix.det_transpose], ?_⟩
    rw [Matrix.transpose_transpose]
    refine mat_ext_of_quad _ _ (Matrix.diagonal_transpose _) ?_ fun x => ?_
    · simp [Matrix.transpose_mul, mul_assoc]
    · rw [← ev, ← hx, ev, dot_congr]
  · rintro ⟨P, hP, hD⟩
    refine ⟨Pᵀ, by rwa [Matrix.det_transpose], fun x => ?_⟩
    rw [ev, ev, ← dot_congr, Matrix.transpose_transpose, hD]

end Pol

section Class

open QuadFormsKB.PadicClass

variable {K : Type*} [Field K] [CharZero K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

/-- **63:20, in the form used here.** If $V$ has an orthogonal base with weights `w`, then it has one with weights `w'`
exactly when the discriminants agree modulo squares and the Hasse invariants agree. -/
theorem rep_diag_iff (hK : LocalHilbertField K) {n : ℕ} {w w' : Fin n → K} (hw : ∀ i, w i ≠ 0)
    (hw' : ∀ i, w' i ≠ 0) (h : Rep Q (Matrix.diagonal w)) :
    Rep Q (Matrix.diagonal w') ↔
      (∃ t : K, t ≠ 0 ∧ ∏ i, w' i = t ^ 2 * ∏ i, w i) ∧ hasseVec w = hasseVec w' := by
  rw [← isometric_iff_invariants hK hw hw', isometricIn_iff_congr]
  constructor
  · rintro ⟨e', he'⟩
    obtain ⟨e, he⟩ := h
    obtain ⟨P, hP, hPe⟩ := gram_change Q e e'
    exact ⟨P, hP, by rw [← he', hPe, he]⟩
  · rintro ⟨P, hP, hD⟩
    rw [hD]
    exact rep_congr Q h hP

/-- The same with O'Meara's Hasse symbol `hasseS` (§63B). -/
theorem rep_diag_iff_S (hK : LocalHilbertField K) {n : ℕ} {w w' : Fin n → K} (hw : ∀ i, w i ≠ 0)
    (hw' : ∀ i, w' i ≠ 0) (h : Rep Q (Matrix.diagonal w)) :
    Rep Q (Matrix.diagonal w') ↔
      (∃ t : K, t ≠ 0 ∧ ∏ i, w' i = t ^ 2 * ∏ i, w i) ∧ hasseS K w = hasseS K w' := by
  rw [rep_diag_iff Q hK hw hw' h]
  refine and_congr_right fun ⟨t, ht, hd⟩ => ?_
  rw [hasseS_eq_vec_mul hK w hw, hasseS_eq_vec_mul hK w' hw', hd, hs_sq_right _ _ _ ht]
  have hne : hilbertSymbol K (-1) (∏ i, w i) ≠ 0 := by
    rcases hs_pm (-1 : K) (∏ i, w i) with h1 | h1 <;> rw [h1] <;> norm_num
  exact ⟨fun h1 => by rw [h1], fun h1 => mul_right_cancel₀ hne h1⟩

end Class

section Exist

variable {K : Type*} [Field K] [CharZero K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

theorem Q_sum_gram {ι : Type*} [Fintype ι] (v : ι → V) (x : ι → K) :
    Q (∑ i, x i • v i) = x ⬝ᵥ gram Q v *ᵥ x := by
  rw [← bil_self, bil_sum_left]
  simp_rw [bil_smul_left, bil_sum_right, bil_smul_right]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [gram, Matrix.of_apply]
  ring

theorem rep_diag_exists [FiniteDimensional K V] (hV : LinearMap.SeparatingLeft (associated Q)) :
    ∃ w : Fin (finrank K V) → K, (∀ i, w i ≠ 0) ∧ Rep Q (Matrix.diagonal w) := by
  obtain ⟨w, ⟨e⟩⟩ := QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' Q hV
  have hQ : ∀ z : Fin (finrank K V) → K, Q (e.symm z) = ∑ i, (w i : K) * z i ^ 2 := by
    intro z
    have h1 := e.map_app (e.symm z)
    have h2 : e (e.symm z) = z := by simp
    rw [h2] at h1
    rw [← h1, QuadraticMap.weightedSumSquares_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Units.smul_def, _root_.sq]
  refine ⟨fun i => (w i : K), fun i => (w i).ne_zero, ?_⟩
  let g : Basis (Fin (finrank K V)) K V := (Pi.basisFun K (Fin (finrank K V))).map e.symm.toLinearEquiv
  refine ⟨g, ?_⟩
  have hg : ∀ x : Fin (finrank K V) → K, ∑ i, x i • g i = e.symm x := by
    intro x
    have h := (Pi.basisFun K (Fin (finrank K V))).sum_repr x
    simp only [Pi.basisFun_repr] at h
    calc ∑ i, x i • g i = e.symm.toLinearEquiv (∑ i, x i • (Pi.basisFun K (Fin (finrank K V))) i) := by
          simp [g, map_sum]
      _ = e.symm x := by rw [h]; rfl
  refine mat_ext_of_quad _ _ ?_ (Matrix.diagonal_transpose _) fun x => ?_
  · ext i j
    exact bil_comm Q (g j) (g i)
  · rw [← Q_sum_gram, hg, hQ, dot_diag]

end Exist

section Blocks

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

theorem rep_congr_iff {n : ℕ} {M : Matrix (Fin n) (Fin n) K} {P : Matrix (Fin n) (Fin n) K}
    (hP : IsUnit P.det) : Rep Q (P * M * Pᵀ) ↔ Rep Q M := by
  refine ⟨fun h => ?_, fun h => rep_congr Q h hP⟩
  have := rep_congr Q h (Matrix.isUnit_nonsing_inv_det P hP)
  have e : P⁻¹ * (P * M * Pᵀ) * (P⁻¹)ᵀ = M := by
    simp only [← Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hP, Matrix.one_mul, Matrix.mul_assoc M, ← Matrix.transpose_mul,
      Matrix.nonsing_inv_mul _ hP, Matrix.transpose_one, Matrix.mul_one]
  rwa [e] at this

/-- Weights of the orthogonal splitting of $A(a,\beta) \perp A(b,\gamma)$ over a field. -/
def dw2 (a β b γ : K) : Fin 4 → K := ![a, a * (a * β - 1), b, b * (b * γ - 1)]

/-- The change of basis from `blk2` to a diagonal matrix. -/
def pblk2 (a b : K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of ![![1, 0, 0, 0], ![-1, a, 0, 0], ![0, 0, 1, 0], ![0, 0, -1, b]]

theorem pblk2_det (a b : K) : (pblk2 a b).det = a * b := by
  simp [pblk2, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem pblk2_mul (a β b γ : K) :
    pblk2 a b * blk2 a β b γ * (pblk2 a b)ᵀ = Matrix.diagonal (dw2 a β b γ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pblk2, blk2, dw2, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply] <;> ring

theorem rep_blk2_iff {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (β γ : K) :
    Rep Q (blk2 a β b γ) ↔ Rep Q (Matrix.diagonal (dw2 a β b γ)) := by
  rw [← pblk2_mul, rep_congr_iff Q]
  rw [pblk2_det]
  exact (mul_ne_zero ha hb).isUnit

end Blocks

section Hilb

open QuadFormsKB.PadicClass

variable {K : Type*} [Field K] [CharZero K]

theorem hasseVec_four (w : Fin 4 → K) :
    hasseVec w = hilbertSymbol K (w 0) (w 1) * hilbertSymbol K (w 0) (w 2) * hilbertSymbol K (w 0) (w 3) *
      (hilbertSymbol K (w 1) (w 2) * hilbertSymbol K (w 1) (w 3)) * hilbertSymbol K (w 2) (w 3) := by
  simp only [hasseVec, Fin.prod_univ_four]
  simp

theorem hasseS_four_diff (hK : LocalHilbertField K) {a b d d' e : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hd : d ≠ 0) (hd' : d' ≠ 0) (he : e ≠ 0)
    (hdd : ∀ x : K, x ≠ 0 → hilbertSymbol K x d' = hilbertSymbol K x d * hilbertSymbol K x e)
    (hdd2 : ∃ t : K, t ≠ 0 ∧ d' * e = t ^ 2 * d) :
    hasseS K ![a, -(a * d), b, -b] * hasseS K ![a, -(a * d'), b, -(b * e)] =
      hilbertSymbol K (-(a * b * d)) e := by
  obtain ⟨t, ht, hte⟩ := hdd2
  have hw1 : ∀ i, (![a, -(a * d), b, -b] : Fin 4 → K) i ≠ 0 := by
    intro i; fin_cases i <;> simp [*]
  have hw2 : ∀ i, (![a, -(a * d'), b, -(b * e)] : Fin 4 → K) i ≠ 0 := by
    intro i; fin_cases i <;> simp [*]
  rw [hasseS_eq_vec_mul hK _ hw1, hasseS_eq_vec_mul hK _ hw2, hasseVec_four, hasseVec_four]
  have p1 : ∏ i, (![a, -(a * d), b, -b] : Fin 4 → K) i = (a * b) ^ 2 * d := by
    simp [Fin.prod_univ_four]; ring
  have p2 : ∏ i, (![a, -(a * d'), b, -(b * e)] : Fin 4 → K) i = (a * b) ^ 2 * (d' * e) := by
    simp [Fin.prod_univ_four]; ring
  rw [p1, p2, hte, hs_sq_right _ _ _ (mul_ne_zero ha hb), show (a * b) ^ 2 * (t ^ 2 * d) = (a * b * t) ^ 2 * d by ring,
    hs_sq_right _ _ _ (mul_ne_zero (mul_ne_zero ha hb) ht)]
  have L1 : ∀ x y z : K, x ≠ 0 → y ≠ 0 → z ≠ 0 →
      hilbertSymbol K (x * y) z = hilbertSymbol K x z * hilbertSymbol K y z := fun x y z hx hy hz =>
    hK.mul_left x y z hx hy hz
  have R1 : ∀ x y z : K, x ≠ 0 → y ≠ 0 → z ≠ 0 →
      hilbertSymbol K x (y * z) = hilbertSymbol K x y * hilbertSymbol K x z := fun x y z hx hy hz =>
    hK.mul_right hx hy hz
  have S1 : ∀ x : K, x ≠ 0 → hilbertSymbol K x x = hilbertSymbol K x (-1) := fun x hx => hK.self hx
  have e1 : -(a * d) = (-1) * (a * d) := by ring
  have e2 : -b = (-1) * b := by ring
  have e3 : -(a * d') = (-1) * (a * d') := by ring
  have e4 : -(b * e) = (-1) * (b * e) := by ring
  have e5 : -(a * b * d) = (-1) * (a * b * d) := by ring
  have hdd' : ∀ x : K, x ≠ 0 → hilbertSymbol K d' x = hilbertSymbol K d x * hilbertSymbol K e x := by
    intro x hx
    rw [hilbertSymbol_comm K d' x, hdd x hx, hilbertSymbol_comm K x d, hilbertSymbol_comm K x e]
  simp (disch := simp [ha, hb, hd, hd', he]) only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, e1, e2, e3, e4, e5,
    L1, R1, S1, hdd, hdd']
  simp only [hilbertSymbol_comm K]
  have sq : ∀ x y : K, hilbertSymbol K x y ^ 2 = 1 := fun x y => by
    rcases hs_pm x y with h | h <;> simp [h]
  have s1 := sq a (-1)
  have s2 := sq b (-1)
  have s3 := sq d (-1)
  have s4 := sq e (-1)
  have s5 := sq (-1) (-1)
  have s6 := sq a b
  have s7 := sq a d
  have s8 := sq a e
  have s9 := sq b d
  have s10 := sq b e
  have s11 := sq d e
  grind

theorem hdd_of (hK : LocalHilbertField K) {d d' e t : K} (hd : d ≠ 0) (hd' : d' ≠ 0) (he : e ≠ 0)
    (hte : d' * e = t ^ 2 * d) (ht : t ≠ 0) :
    ∀ x : K, x ≠ 0 → hilbertSymbol K x d' = hilbertSymbol K x d * hilbertSymbol K x e := by
  intro x hx
  have h1 := hK.mul_right hx hd' he
  rw [hte, hs_sq_right _ _ _ ht] at h1
  rw [h1]
  rcases hs_pm x d' with h | h <;> rcases hs_pm x e with h' | h' <;> rw [h, h'] <;> norm_num

end Hilb

section DeltaSym

open QuadFormsKB.PadicClass

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {K : Type*} [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]

/-- **$(x, \Delta) = (-1)^{\operatorname{ord} x}$** for the unit $\Delta$ of quadratic defect $4\mathfrak o$
(O'Meara 63:11a, p. 165, extended multiplicatively). -/
theorem hilbert_delta_parity (hK : LocalHilbertField K) (h2 : (2 : R) ≠ 0) {Δ : R} (hΔ : IsUnit Δ)
    (hΔd : quadDefect R (algebraMap R K Δ) = span R {(4 : K)}) {π : R} (hπ : Irreducible π) {x : K}
    (hx : x ≠ 0) :
    hilbertSymbol K x (algebraMap R K Δ) = if Even (dord hπ x) then 1 else -1 := by
  obtain ⟨u, hu, hxu⟩ := dord_spec hπ hx
  have hne := alg_pi_ne_zero (R := R) (F := K) hπ
  have hu0 := alg_ne_zero_of_unit (F := K) hu
  have hΔ0 := alg_ne_zero_of_unit (F := K) hΔ
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' (dord hπ x)
  · have hx2 : x = (algebraMap R K π ^ m) ^ 2 * algebraMap R K u := by
      rw [hxu, hm, two_mul, zpow_add₀ hne]; ring
    have hEven : Even (dord hπ x) := ⟨m, by omega⟩
    rw [if_pos hEven, hx2, hs_sq_left _ _ _ (zpow_ne_zero _ hne)]
    exact hilbertSymbol_unit_delta h2 hΔ hΔd hu
  · have hx2 : x = (algebraMap R K π ^ m) ^ 2 * (algebraMap R K π * algebraMap R K u) := by
      rw [hxu, hm, zpow_add₀ hne, two_mul, zpow_add₀ hne]; simp; ring
    have hOdd : ¬ Even (dord hπ x) := by
      rw [Int.not_even_iff_odd]; exact ⟨m, hm⟩
    rw [if_neg hOdd, hx2, hs_sq_left _ _ _ (zpow_ne_zero _ hne), hK.mul_left _ _ _ hne hu0 hΔ0,
      hilbertSymbol_prime_delta h2 hΔ hΔd hπ, hilbertSymbol_unit_delta h2 hΔ hΔd hu]
    norm_num

end DeltaSym

end QuadFormsKB.OMeara.D18
