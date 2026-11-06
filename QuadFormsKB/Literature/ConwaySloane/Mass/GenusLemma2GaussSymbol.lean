/-
# Conway–Sloane, LDL IV, §11, Lemma 2 at $p = 2$: symbol bookkeeping for the Gauss sum argument

For block decompositions `D`, `D'` (2-adic Jordan decompositions in Cassels' normalization) with 2-adic symbols
$\sigma$ = `blockSymbol D`, $\tau$ = `blockSymbol D'`:
* `dim_eq_of_sum_min`: equal torsion counts $\sum_x \min(k, e_x)$ (all $k$) and equal rank give equal dimensions
  $n_{2^k}$ of all Jordan constituents;
* `isTypeI_zero_iff`: the constituent of scale $1$ is odd iff the integral Gram matrix is odd (`EvenGram`);
* `qv_bmat_half`: $2^m y^{\mathsf T}Fy \in 2\mathbb Z_2$ unless $m = 0$ and the scale-1 constituent is odd;
* `sum_blockPhase`, `prefix_eq_of_phase`: the phase of the Gauss sum at $2^m$ determines Theorem 10 (ii) at a type II
  scale $2^m$, given the $\mathbb Q_2$-class (equal total oddity and total sign).

Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemma2GaussBmat
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemma2Odd

set_option linter.unusedSectionVars false

open Matrix QuadFormsKB QuadFormsKB.Cassels Finset QuadFormsKB.ConwaySloane.TwoAdic

namespace QuadFormsKB.ConwaySloane.Mass.Gauss2

/-! ### Even quadratic values -/

/-- A symmetric integral matrix with even diagonal has even quadratic values on $\mathbb Z_2^n$. -/
theorem qv_half_of_diag {n : ℕ} (F : Matrix (Fin n) (Fin n) ℚ_[2]) (hs : Fᵀ = F) (hint : IsIntM F)
    (hd : ∀ i, ‖F i i / 2‖ ≤ 1) (z : Fin n → ℚ_[2]) (hz : IsIntV z) : ‖qv F z / 2‖ ≤ 1 := by
  set a : Fin n → Fin n → ℚ_[2] := fun i j => z i * F i j * z j with ha
  have hsym : ∀ i j, a i j = a j i := fun i j => by
    have : F j i = F i j := by rw [← transpose_apply F i j, hs]
    simp only [ha, this]; ring
  have hq : qv F z = ∑ i, ∑ j, a i j := by
    simp only [qv, dotProduct, mulVec, ha, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hsplit : ∀ i, ∑ j, a i j = a i i + ∑ j ∈ univ.filter (· < i), a i j + ∑ j ∈ univ.filter (i < ·), a i j := by
    intro i
    rw [← Finset.sum_filter_add_sum_filter_not univ (· < i), ← Finset.sum_filter_add_sum_filter_not
      (univ.filter fun j => ¬ j < i) (i < ·)]
    have h1 : ((univ.filter fun j => ¬ j < i).filter fun j => ¬ i < j) = {i} := by
      ext j; simp only [mem_filter, mem_univ, true_and, mem_singleton]; omega
    have h2 : ((univ.filter fun j => ¬ j < i).filter fun j => i < j) = univ.filter (i < ·) := by
      ext j; simp only [mem_filter, mem_univ, true_and]; omega
    rw [h1, h2, sum_singleton]; ring
  have hcomm : ∑ i, ∑ j ∈ univ.filter (i < ·), a i j = ∑ i, ∑ j ∈ univ.filter (· < i), a i j := by
    rw [Finset.sum_comm' (t' := univ) (s' := fun j => univ.filter (· < j))]
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsym _ _
    · intro i j; simp
  have htot : qv F z = ∑ i, a i i + 2 * ∑ i, ∑ j ∈ univ.filter (· < i), a i j := by
    rw [hq, Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, Finset.sum_add_distrib, hcomm]
    ring
  rw [htot, add_div, Finset.sum_div, mul_div_cancel_left₀ _ (two_ne_zero)]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · refine norm_sum_le_one _ _ fun i _ => ?_
    rw [show a i i / 2 = z i * (F i i / 2) * z i by simp only [ha]; ring]
    exact norm_mul_le_one' (norm_mul_le_one' (hz i) (hd i)) (hz i)
  · refine norm_sum_le_one _ _ fun i _ => norm_sum_le_one _ _ fun j _ => ?_
    exact norm_mul_le_one' (norm_mul_le_one' (hz i) (hint i j)) (hz j)

theorem half_sq (k : ℕ) (u : ℤ) (y : Fin 1 → ℚ_[2]) (hy : IsIntV y) :
    ‖qv (!![(2 : ℚ_[2]) ^ ((k : ℤ) + 1) * u] : Matrix (Fin 1) (Fin 1) ℚ_[2]) y / 2‖ ≤ 1 := by
  have : qv (!![(2 : ℚ_[2]) ^ ((k : ℤ) + 1) * u] : Matrix (Fin 1) (Fin 1) ℚ_[2]) y / 2 =
      (2 : ℚ_[2]) ^ k * (u : ℚ_[2]) * (y 0 * y 0) := by
    simp only [qv, dotProduct, mulVec, Fin.sum_univ_one, of_apply, cons_val', cons_val_fin_one, empty_val']
    rw [zpow_add₀ two_ne_zero, zpow_natCast, zpow_one]; field_simp
  rw [this]
  exact norm_mul_le_one' (norm_mul_le_one' (norm_two_pow_le k) (Padic.norm_int_le_one u))
    (norm_mul_le_one' (hy 0) (hy 0))

theorem half_hyp (e : ℤ) (he : 0 ≤ e) (y : Fin 2 → ℚ_[2]) (hy : IsIntV y) :
    ‖qv ((2 : ℚ_[2]) ^ e • !![(0 : ℚ_[2]), 1; 1, 0]) y / 2‖ ≤ 1 := by
  have : qv ((2 : ℚ_[2]) ^ e • !![(0 : ℚ_[2]), 1; 1, 0]) y / 2 = (2 : ℚ_[2]) ^ e.toNat * (y 0 * y 1) := by
    simp only [qv, dotProduct, mulVec, Fin.sum_univ_two, Matrix.smul_apply, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one, smul_eq_mul]
    rw [zpow_eq_pow_toNat he]; ring
  rw [this]
  exact norm_mul_le_one' (norm_two_pow_le _) (norm_mul_le_one' (hy 0) (hy 1))

theorem half_ell (e : ℤ) (he : 0 ≤ e) (y : Fin 2 → ℚ_[2]) (hy : IsIntV y) :
    ‖qv ((2 : ℚ_[2]) ^ e • !![(2 : ℚ_[2]), 1; 1, 2]) y / 2‖ ≤ 1 := by
  have : qv ((2 : ℚ_[2]) ^ e • !![(2 : ℚ_[2]), 1; 1, 2]) y / 2 =
      (2 : ℚ_[2]) ^ e.toNat * (y 0 * y 0 + y 0 * y 1 + y 1 * y 1) := by
    simp only [qv, dotProduct, mulVec, Fin.sum_univ_two, Matrix.smul_apply, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one, smul_eq_mul]
    rw [zpow_eq_pow_toNat he]; ring
  rw [this]
  refine norm_mul_le_one' (norm_two_pow_le _) ?_
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (norm_mul_le_one' (hy 0) (hy 0)) (norm_mul_le_one' (hy 0) (hy 1)))) (norm_mul_le_one' (hy 1) (hy 1)))

/-- The quadratic form of a block, halved, is integral unless the block is $u x^2$ with exponent $0$. -/
theorem qv_mat_half (b : DyBlock) (he : 0 ≤ blockExp b) (hb : ¬ (IsSqBlock b ∧ bex b = 0))
    (y : Fin b.dim → ℚ_[2]) (hy : IsIntV y) : ‖qv b.mat y / 2‖ ≤ 1 := by
  cases b with
  | sq e u =>
    have he1 : 1 ≤ e := by
      simp only [IsSqBlock, true_and, bex, blockExp] at hb; omega
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, e = (k : ℤ) + 1 := ⟨(e - 1).toNat, by omega⟩
    exact half_sq k u y hy
  | hyp e => exact half_hyp e he y hy
  | ell e => exact half_ell e he y hy

theorem qv_mat_int' (b : DyBlock) (he : 0 ≤ blockExp b) (y : Fin b.dim → ℚ_[2]) (hy : IsIntV y) :
    ‖qv b.mat y‖ ≤ 1 := qv_mat_int b he y hy

/-- **Evenness of the scaled form**: $2^m y^{\mathsf T}Fy \in 2\mathbb Z_2$ for $y \in \mathbb Z_2^\iota$, if $m \ge 1$ or no
block $u x^2$ has exponent $0$. -/
theorem qv_bmat_half (D : List DyBlock) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) (m : ℕ)
    (hm : 1 ≤ m ∨ ∀ j, ¬ (IsSqBlock (D.get j) ∧ bexp D j = 0)) (y : BIdx D → ℚ_[2]) (hy : IsIntV y) :
    ‖(2 : ℚ_[2]) ^ m * qv (bmat D) y / 2‖ ≤ 1 := by
  rw [bmat, qv_blockDiagonal', Finset.mul_sum, Finset.sum_div]
  refine norm_sum_le_one _ _ fun j _ => ?_
  have he := hD0 _ (List.get_mem D j)
  have hyj : IsIntV fun s => y ⟨j, s⟩ := fun s => hy _
  rcases hm with hm | hm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [show (2 : ℚ_[2]) ^ (1 + k) * qv (D.get j).mat (fun s => y ⟨j, s⟩) / 2 =
      (2 : ℚ_[2]) ^ k * qv (D.get j).mat (fun s => y ⟨j, s⟩) by rw [pow_add]; field_simp]
    exact norm_mul_le_one' (norm_two_pow_le k) (qv_mat_int _ he _ hyj)
  · rw [mul_div_assoc]
    exact norm_mul_le_one' (norm_two_pow_le m) (qv_mat_half _ he (hm j) _ hyj)

/-! ### The type of the scale-1 constituent -/

theorem isIntM_bmat (D : List DyBlock) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) : IsIntM (bmat D) := by
  intro x y
  rw [bmat, blockDiagonal'_apply]
  split_ifs with h
  · obtain ⟨j, s⟩ := x
    obtain ⟨j', t⟩ := y
    simp only at h
    subst h
    simp only [cast_eq]
    rw [mat_eq_smul _ (hD0 _ (List.get_mem _ _)), Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
    exact norm_mul_le_one' (norm_two_pow_le _) ((bU (D.get j)) s t).2
  · simp

/-- Diagonal entries of the block matrix are even unless they come from a block $u x^2$ of exponent $0$. -/
theorem bmat_diag_half (D : List DyBlock) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b)
    (h0 : ∀ j, ¬ (IsSqBlock (D.get j) ∧ bexp D j = 0)) (x : BIdx D) : ‖bmat D x x / 2‖ ≤ 1 := by
  have := qv_bmat_half D hD0 0 (Or.inr h0) (Pi.single x 1) (fun i => by
    by_cases h : i = x
    · subst h; simp
    · simp [h])
  simpa [qv] using this

theorem castMat_eq (D : List DyBlock) {n : ℕ} (h : dyDim D = n) :
    castMat D h = (bmat D).submatrix (bE D h) (bE D h) := by ext i j; rw [castMat_apply]; rfl

/-- **The scale-1 constituent is odd iff the integral form is odd.** -/
theorem isTypeI_zero_iff {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (hsA : Aᵀ = A) {D : List DyBlock}
    (hD : ∀ b ∈ D, b.Valid) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) (h : dyDim D = n)
    (hAD : ZpEquiv (A.map (Int.castRingHom ℚ_[2])) (castMat D h)) :
    IsTypeI (blockSymbol D) 0 ↔ ¬ EvenGram A := by
  obtain ⟨T, hT⟩ := hAD
  set S := T.val.map PadicInt.Coe.ringHom with hS
  set Si := (T⁻¹).val.map PadicInt.Coe.ringHom with hSi
  have one_map : (1 : Matrix (Fin n) (Fin n) ℤ_[2]).map PadicInt.Coe.ringHom = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have h1 : S * Si = 1 := by
    rw [hS, hSi, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_map]
  have hSint : IsIntM S := fun i j => by rw [hS, Matrix.map_apply]; exact (T.val i j).2
  have hSiint : IsIntM Si := fun i j => by rw [hSi, Matrix.map_apply]; exact ((T⁻¹).val i j).2
  set FA := A.map (Int.castRingHom ℚ_[2]) with hFA
  have hFAs : FAᵀ = FA := by rw [hFA, ← Matrix.transpose_map, hsA]
  have hFAint : IsIntM FA := fun i j => by rw [hFA, Matrix.map_apply]; exact Padic.norm_int_le_one _
  have hCs : (castMat D h)ᵀ = castMat D h := castMat_transpose D h
  have hCint : IsIntM (castMat D h) := fun i j => by rw [castMat_apply]; exact isIntM_bmat D hD0 _ _
  -- FA = Siᵀ C Si
  have hFAC : FA = Siᵀ * castMat D h * Si := by
    rw [← hT]
    simp only [Matrix.mul_assoc]
    rw [h1, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.transpose_mul, h1, Matrix.transpose_one, Matrix.one_mul]
  have hqs : ∀ (F : Matrix (Fin n) (Fin n) ℚ_[2]) (i : Fin n), qv F (Pi.single i 1) = F i i := fun F i => by
    simp [qv]
  have hconj : ∀ (M N : Matrix (Fin n) (Fin n) ℚ_[2]) (v : Fin n → ℚ_[2]), qv (Mᵀ * N * M) v = qv N (M *ᵥ v) :=
    fun M N v => (Lemma2Odd.conj_dot M N v).symm
  have hsingle : ∀ i : Fin n, IsIntV (Pi.single i (1 : ℚ_[2])) := fun i r => by
    by_cases hr : r = i
    · subst hr; simp
    · simp [hr]
  rw [isTypeI_blockSymbol D hD0]
  constructor
  · rintro ⟨j, hj0, hsq⟩ hEven
    have hdim : 0 < (D.get j).dim := by
      cases hb : D.get j <;> simp_all [IsSqBlock, DyBlock.dim]
    set s0 : Fin (D.get j).dim := ⟨0, hdim⟩
    set i := (bE D h).symm ⟨j, s0⟩
    have hFAhalf : ∀ z, IsIntV z → ‖qv FA z / 2‖ ≤ 1 := qv_half_of_diag FA hFAs hFAint (fun i => by
      rw [hFA, Matrix.map_apply]
      obtain ⟨c, hc⟩ := (hEven i).two_dvd
      rw [hc, eq_intCast, Int.cast_mul, Int.cast_ofNat, mul_div_cancel_left₀ _ two_ne_zero]
      exact Padic.norm_int_le_one c)
    have hCi : castMat D h i i = qv FA (S *ᵥ Pi.single i 1) := by
      rw [← hconj, hT, hqs]
    have hval : castMat D h i i = (D.get j).mat s0 s0 := by
      rw [castMat_apply]
      simp only [i, Equiv.apply_symm_apply, bmat]
      exact blockDiagonal'_apply_eq _ _ _ _
    obtain ⟨u, hu, hmu⟩ := TwoAdic.mat_sq_unit (D.get j) (hD _ (List.get_mem _ _)) (hD0 _ (List.get_mem _ _)) hsq s0
    have hj0' : (blockExp (D.get j)).toNat = 0 := hj0
    rw [hj0', pow_zero, one_mul] at hmu
    have h2 := hFAhalf _ (hSint.mulVec (hsingle i))
    rw [← hCi, hval, hmu] at h2
    have hun : ‖(u : ℚ_[2])‖ = 1 := PadicInt.isUnit_iff.1 hu
    rw [norm_div, hun, show ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ by simpa using Padic.norm_p (p := 2)] at h2
    norm_num at h2
  · intro hE
    by_contra hno
    apply hE
    have h0 : ∀ j, ¬ (IsSqBlock (D.get j) ∧ bexp D j = 0) := fun j ⟨hsq, hj⟩ => hno ⟨j, hj, hsq⟩
    have hChalf : ∀ z, IsIntV z → ‖qv (castMat D h) z / 2‖ ≤ 1 :=
      qv_half_of_diag _ hCs hCint (fun i => by rw [castMat_apply]; exact bmat_diag_half D hD0 h0 _)
    intro i
    have h2 := hChalf _ (hSiint.mulVec (hsingle i))
    rw [← hconj, ← hFAC, hqs, hFA, Matrix.map_apply, eq_intCast] at h2
    have h3 : ‖((A i i : ℤ) : ℚ_[2])‖ ≤ (2 : ℝ) ^ (-(1 : ℕ) : ℤ) := by
      rw [norm_div, show ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ by simpa using Padic.norm_p (p := 2)] at h2
      have : ‖((A i i : ℤ) : ℚ_[2])‖ ≤ (2 : ℝ)⁻¹ := by
        have := mul_le_mul_of_nonneg_right h2 (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
        rwa [div_mul_cancel₀ _ (by norm_num), one_mul] at this
      simpa using this
    have := (Padic.norm_int_le_pow_iff_dvd (p := 2) _ 1).1 h3
    exact even_iff_two_dvd.2 (by simpa using this)

/-! ### Dimensions from torsion counts -/

theorem card_BIdx (D : List DyBlock) : Fintype.card (BIdx D) = dyDim D := by
  rw [← Fintype.card_fin (dyDim D)]; exact (Fintype.card_congr (bEquiv D)).symm

section Counting

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

theorem sum_min_succ (e : ι → ℕ) (k : ℕ) :
    ∑ i, min (k + 1) (e i) = ∑ i, min k (e i) + (univ.filter fun i => k < e i).card := by
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> omega

theorem card_gt_eq {e : ι → ℕ} {e' : ι' → ℕ} (hmin : ∀ k, ∑ i, min k (e i) = ∑ i, min k (e' i)) (k : ℕ) :
    (univ.filter fun i => k < e i).card = (univ.filter fun i => k < e' i).card := by
  have h := hmin (k + 1)
  rw [sum_min_succ, sum_min_succ, hmin k] at h
  omega

theorem card_gt_split (e : ι → ℕ) (k : ℕ) :
    (univ.filter fun i => k < e i).card =
      (univ.filter fun i => e i = k + 1).card + (univ.filter fun i => k + 1 < e i).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> omega

theorem card_zero_split (e : ι → ℕ) :
    Fintype.card ι = (univ.filter fun i => e i = 0).card + (univ.filter fun i => 0 < e i).card := by
  rw [← Finset.card_univ, Finset.card_filter, Finset.card_filter, Finset.card_eq_sum_ones,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> omega

theorem card_level_eq {e : ι → ℕ} {e' : ι' → ℕ} (hcard : Fintype.card ι = Fintype.card ι')
    (hmin : ∀ k, ∑ i, min k (e i) = ∑ i, min k (e' i)) (k : ℕ) :
    (univ.filter fun i => e i = k).card = (univ.filter fun i => e' i = k).card := by
  cases k with
  | zero =>
    have h1 := card_zero_split e
    have h2 := card_zero_split e'
    have h3 := card_gt_eq hmin 0
    omega
  | succ k =>
    have h1 := card_gt_split e k
    have h2 := card_gt_split e' k
    have h3 := card_gt_eq hmin k
    have h4 := card_gt_eq hmin (k + 1)
    omega

end Counting

theorem dim_eq_card (D : List DyBlock) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) (k : ℕ) :
    (blockSymbol D k).dim = (univ.filter fun x : BIdx D => bx D x = k).card := by
  rw [dim_blockSymbol D hD0]
  have : (univ.filter fun x : BIdx D => bx D x = k) =
      (univ.filter fun j => bexp D j = k).sigma fun _ => univ := by
    ext ⟨j, s⟩; rw [Finset.mem_filter, Finset.mem_sigma, Finset.mem_filter]; simp [bx]
  rw [this, Finset.card_sigma]
  simp

/-- **Equal dimensions of all Jordan constituents** from equal torsion counts and equal rank. -/
theorem dim_eq_of_sum_min {D D' : List DyBlock} (hD0 : ∀ b ∈ D, 0 ≤ blockExp b)
    (hD'0 : ∀ b ∈ D', 0 ≤ blockExp b) (hn : dyDim D = dyDim D')
    (hmin : ∀ k, ∑ x, min k (bx D x) = ∑ x, min k (bx D' x)) (k : ℕ) :
    (blockSymbol D' k).dim = (blockSymbol D k).dim := by
  rw [dim_eq_card D hD0, dim_eq_card D' hD'0]
  exact (card_level_eq (by rw [card_BIdx, card_BIdx, hn]) hmin k).symm

/-! ### The phase and Theorem 10 (ii) -/

theorem four_signInd_prodList (B : List DyBlock) :
    4 * signInd (Sign.prodList (B.map blockSign)) = (B.map fun b => 4 * signInd (blockSign b)).sum := by
  induction B with
  | nil => simp [Sign.prodList, signInd]
  | cons b B ih =>
    simp only [List.map_cons, Sign.prodList, List.sum_cons]
    have := four_mul_signInd_mul 1 (blockSign b) (Sign.prodList (B.map blockSign))
    simp only [mul_one] at this
    rw [this, ih]

theorem four_signInd_blockSymbol (D : List DyBlock) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) (k : ℕ) :
    4 * signInd (blockSymbol D k).sign =
      ∑ j ∈ univ.filter (fun j => bexp D j = k), 4 * signInd (blockSign (D.get j)) := by
  rw [show (∑ j ∈ univ.filter (fun j => bexp D j = k), 4 * signInd (blockSign (D.get j))) =
      ((D.filter fun b => decide ((blockExp b).toNat = k)).map fun b => 4 * signInd (blockSign b)).sum from
    sum_fiber D (fun b => (blockExp b).toNat = k) (fun b => 4 * signInd (blockSign b)), ← filter_exp_eq D hD0,
    blockSymbol_sign, four_signInd_prodList]

theorem four_minusBelow (D : List DyBlock) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) : ∀ m : ℕ,
    4 * (minusBelow (blockSymbol D) m : ZMod 8) =
      ∑ j ∈ univ.filter (fun j => bexp D j < m), 4 * signInd (blockSign (D.get j))
  | 0 => by simp [minusBelow]
  | m + 1 => by
    have hsucc : 4 * (minusBelow (blockSymbol D) (m + 1) : ZMod 8) =
        4 * (minusBelow (blockSymbol D) m : ZMod 8) + 4 * signInd (blockSymbol D m).sign := by
      simp only [minusBelow, signInd]; push_cast; split_ifs <;> ring
    rw [hsucc, four_minusBelow D hD0 m, four_signInd_blockSymbol D hD0, ← Finset.sum_union]
    · congr 1; ext j; simp only [mem_union, mem_filter, mem_univ, true_and]; omega
    · exact Finset.disjoint_filter.2 fun j _ h1 h2 => by omega

theorem sum_blockPhase (D : List DyBlock) (hD : ∀ b ∈ D, b.Valid) (m : ℕ) :
    ∑ j, blockPhase (D.get j) m = ∑ j ∈ univ.filter (fun j => m < bexp D j),
      (bOdd (D.get j) - (m : ZMod 8) * (4 * signInd (blockSign (D.get j)))) := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [blockPhase, bex, bexp]
  split_ifs with h
  · rw [bOdd_eq _ (hD _ (List.get_mem _ _)), Nat.cast_sub h.le]; ring
  · exact (if_neg h).trans (if_neg h).symm

theorem sum_split (D : List DyBlock) {N : ℕ} (hN : ∀ j, bexp D j < N) (m : ℕ) (f : Fin D.length → ZMod 8) :
    ∑ j ∈ univ.filter (fun j => bexp D j < N), f j =
      ∑ j ∈ univ.filter (fun j => bexp D j < m + 1), f j + ∑ j ∈ univ.filter (fun j => m < bexp D j), f j := by
  rw [Finset.filter_true_of_mem fun j _ => hN j, ← Finset.sum_filter_add_sum_filter_not univ
    (fun j => bexp D j < m + 1)]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j; simp only [mem_filter, mem_univ, true_and]; omega

theorem phase_key (D : List DyBlock) (hD : ∀ b ∈ D, b.Valid) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) {N : ℕ}
    (hN : ∀ j, bexp D j < N) (m : ℕ) (hII : ¬ IsTypeI (blockSymbol D) m) :
    oddPre (blockSymbol D) N = oddPre (blockSymbol D) m + 4 * (m : ZMod 8) * signInd (blockSymbol D m).sign +
        (∑ j, blockPhase (D.get j) m +
          (m : ZMod 8) * ∑ j ∈ univ.filter (fun j => m < bexp D j), 4 * signInd (blockSign (D.get j))) ∧
      4 * (minusBelow (blockSymbol D) N : ZMod 8) = 4 * (minusBelow (blockSymbol D) m : ZMod 8) +
        4 * signInd (blockSymbol D m).sign +
          ∑ j ∈ univ.filter (fun j => m < bexp D j), 4 * signInd (blockSign (D.get j)) := by
  have hodd0 : (blockSymbol D m).oddity = 0 :=
    (blockSymbol_exists D hD m).2.2.2.2 (type_eq_II_of_not hII)
  constructor
  · rw [oddPre_blockSymbol D hD hD0, sum_split D hN m, ← oddPre_blockSymbol D hD hD0, oddPre, oddW, hodd0,
      sum_blockPhase D hD, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  · rw [four_minusBelow D hD0, sum_split D hN m, ← four_minusBelow D hD0, minusBelow]
    push_cast
    rw [mul_add]
    congr 1

theorem two_mul_sum_four (D : List DyBlock) (m : ℕ) :
    2 * ∑ j ∈ univ.filter (fun j => m < bexp D j), 4 * signInd (blockSign (D.get j)) = 0 := by
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h8 : (8 : ZMod 8) = 0 := by decide
  linear_combination signInd (blockSign (D.get j)) * h8

/-- **Theorem 10 (ii) at a type II scale from the Gauss phase.** For block decompositions with the same total oddity
and $4 \cdot$(number of sign differences) $= 0$ (the same $\mathbb Q_2$-class), equal phases of the Gauss sums at
$2^m$ give Theorem 10 (ii) at $2^m$, in the prefix form of `theorem10Cond_iff_prefix`. -/
theorem prefix_eq_of_phase {D D' : List DyBlock} (hD : ∀ b ∈ D, b.Valid) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b)
    (hD' : ∀ b ∈ D', b.Valid) (hD'0 : ∀ b ∈ D', 0 ≤ blockExp b) {N : ℕ} (hN : ∀ j, bexp D j < N)
    (hN' : ∀ j, bexp D' j < N) (m : ℕ) (hII : ¬ IsTypeI (blockSymbol D) m)
    (hII' : ¬ IsTypeI (blockSymbol D') m)
    (hO : oddPre (blockSymbol D) N = oddPre (blockSymbol D') N)
    (hS : 4 * signCnt (blockSymbol D) (blockSymbol D') N = 0)
    (hP : ∑ j, blockPhase (D.get j) m = ∑ j, blockPhase (D'.get j) m) :
    oddDiff (blockSymbol D) (blockSymbol D') m +
      4 * (m : ZMod 8) * signCnt (blockSymbol D) (blockSymbol D') m = 0 := by
  obtain ⟨o1, s1⟩ := phase_key D hD hD0 hN m hII
  obtain ⟨o2, s2⟩ := phase_key D' hD' hD'0 hN' m hII'
  have t1 := two_mul_sum_four D m
  have t2 := two_mul_sum_four D' m
  have h8 : (8 : ZMod 8) = 0 := by decide
  unfold oddDiff signCnt at *
  linear_combination -o1 + o2 + hO - hP - (m : ZMod 8) * s1 - (m : ZMod 8) * s2 + (m : ZMod 8) * hS -
    (m : ZMod 8) * t1 - (m : ZMod 8) * signInd (blockSymbol D m).sign * h8

end QuadFormsKB.ConwaySloane.Mass.Gauss2
