/-
# Cassels, Chapter 8, §4: forms over $\mathbb Z_2$

**Setting** (as in `Ch8/Bases.lean`, $p = 2$): a form $f(\vec x) = \vec x^{t}F\vec x$ with $F \in M_n(\mathbb Q_2)$
symmetric; $\mathbb Z_2$-equivalence `ZpEquiv`; classical integrality and (im)proper primitivity as in
`Ch8/Primitive.lean`. The orthogonal sum $f \perp g$ of forms in distinct variables (Cassels writes $f + g$) has the
block diagonal matrix `orthSumMat F G` (variables of $f$ first). In Cassels' building blocks
$2xy$ has matrix $H = \begin{pmatrix} 0 & 1 \\ 1 & 0\end{pmatrix}$ and $2x^{2} + 2xy + 2y^{2}$ has matrix
$A = \begin{pmatrix} 2 & 1 \\ 1 & 2\end{pmatrix}$ (classical matrices: $f_{12} = f_{21}$ is half the coefficient of
$xy$).

**Proves**
* `exists_dyadic_decomp` (**Lemma 4.1**, pp. 117–119): every regular form over $\mathbb Q_2$ is $\mathbb Z_2$-equivalent to
  an orthogonal sum of forms $2^{e}ux^{2}$ ($u \in \{1, 3, 5, 7\}$), $2^{e}\cdot 2xy$ and
  $2^{e}(2x^{2} + 2xy + 2y^{2})$ ($e \in \mathbb Z$);
* `equiv_4_7`, `equiv_4_8`, `equiv_4_9`: Cassels' equivalences (4.7)–(4.9) (p. 118). They were first reconstructed
  (the machine-read text lost the formulas) and then checked against the page image (2026-10-30): (4.8) and (4.9) are
  as printed; `equiv_4_7` is an equivalent variant of the printed (4.7) $ux_1^{2} + 2x_2x_3 \sim ux_1^{2} + x_2^{2} -
  x_3^{2}$, which is `equiv_4_7_printed` in `Ch8/DyadicEquivs.lean`, together with (4.4)–(4.6);
* `zpEquiv_of_improperlyPrimitive` (**Corollary to Lemma 4.1**, p. 119): improperly primitive integral forms with the
  same unit determinant are $\mathbb Z_2$-equivalent.
-/
import QuadFormsKB.Literature.Cassels.Ch8.Canonical
import QuadFormsKB.Literature.Cassels.Ch8.Primitive
import QuadFormsKB.Literature.Cassels.Ch8.Congruent

namespace QuadFormsKB.Cassels

open Matrix

variable {n : ℕ}

/-- The matrix of the orthogonal sum $f \perp g$ of forms in distinct variables (Cassels' $f + g$, Ch. 2, §5): the
block diagonal matrix $\begin{pmatrix} F & 0 \\ 0 & G \end{pmatrix}$, the variables of $f$ first (the matrix counterpart
of `QuadForm.orthSum`). -/
def orthSumMat {K : Type*} [Zero K] {a b : ℕ} (F : Matrix (Fin a) (Fin a) K) (G : Matrix (Fin b) (Fin b) K) :
    Matrix (Fin (a + b)) (Fin (a + b)) K :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks F 0 0 G)

/-- Cassels' building blocks (4.1)–(4.3) for $p = 2$: `sq e u` is $2^{e}ux^{2}$ (with $u \in \{1, 3, 5, 7\}$, see
`DyBlock.Valid`), `hyp e` is $2^{e}\cdot 2xy$ and `ell e` is $2^{e}(2x^{2} + 2xy + 2y^{2})$, $e \in \mathbb Z$. -/
@[kb "cassels1978" "Ch. 8, Lemma 4.1, (4.1)–(4.3), p. 117 (the building blocks)"]
inductive DyBlock
  | sq (e : ℤ) (u : ℤ)
  | hyp (e : ℤ)
  | ell (e : ℤ)

/-- The admissible units in (4.1): $u \in \{1, 3, 5, 7\}$. -/
def DyBlock.Valid : DyBlock → Prop
  | .sq _ u => u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7
  | _ => True

/-- The number of variables of a block. -/
def DyBlock.dim : DyBlock → ℕ
  | .sq .. => 1
  | _ => 2

/-- The (classical) matrix of a block. -/
noncomputable def DyBlock.mat : (b : DyBlock) → Matrix (Fin b.dim) (Fin b.dim) ℚ_[2]
  | .sq e u => !![(2 : ℚ_[2]) ^ e * u]
  | .hyp e => (2 : ℚ_[2]) ^ e • !![0, 1; 1, 0]
  | .ell e => (2 : ℚ_[2]) ^ e • !![2, 1; 1, 2]

/-- The number of variables of an orthogonal sum of blocks. -/
def dyDim : List DyBlock → ℕ
  | [] => 0
  | b :: D => b.dim + dyDim D

/-- The matrix of the orthogonal sum of the blocks of `D`, in this order. -/
noncomputable def dyMat : (D : List DyBlock) → Matrix (Fin (dyDim D)) (Fin (dyDim D)) ℚ_[2]
  | [] => 0
  | b :: D => orthSumMat b.mat (dyMat D)

/-! ### Helpers: congruence modulo 8 -/

theorem dyadic_val_unit {c : ℤ_[2]} (hc : IsUnit c) : c.valuation = 0 := by
  have h1 := PadicInt.isUnit_iff.1 hc
  have h0 : c ≠ 0 := hc.ne_zero
  rw [PadicInt.norm_eq_zpow_neg_valuation h0] at h1
  have : ((2:ℝ)) ^ (-(c.valuation : ℤ)) = 2 ^ (0:ℤ) := by simpa using h1
  have := zpow_right_injective₀ (by norm_num : (0:ℝ) < 2) (by norm_num) this
  omega

/-- Congruence mod 8 gives `ZpEquiv` for unit determinant (Lemma 5.1). -/
theorem dyadic_zpEquiv_of_mod8 {n : ℕ} (F G : Matrix (Fin n) (Fin n) ℤ_[2]) (hF : Fᵀ = F) (hG : Gᵀ = G)
    (hdet : IsUnit F.det) (hd : ∀ i j, (2 : ℤ_[2]) ^ 3 ∣ F i j - G i j) :
    ZpEquiv (F.map PadicInt.Coe.ringHom) (G.map PadicInt.Coe.ringHom) := by
  have h4 : ((4 : ℤ_[2]) * F.det).valuation < 3 := by
    have : (4 : ℤ_[2]) = (2 : ℤ_[2]) ^ 2 := by norm_num
    rw [this]
    have h := PadicInt.valuation_p_pow_mul (p := 2) 2 F.det hdet.ne_zero
    simp only [Nat.cast_ofNat] at h
    rw [h, dyadic_val_unit hdet]; norm_num
  obtain ⟨T, -, hT⟩ := exists_equiv_of_dvd_pow F G hF hG hdet.ne_zero 3 h4 (by simpa using hd)
  refine ⟨T, ?_⟩
  rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hT]

theorem dyadic_isUnit_int_cast_of_odd {k : ℤ} (hk : Odd k) : IsUnit ((k : ℤ) : ℤ_[2]) := by
  rw [PadicInt.isUnit_iff]
  have h1 : ¬ ‖((k : ℤ) : ℤ_[2])‖ < 1 := by
    rw [PadicInt.norm_int_lt_one_iff_dvd]
    intro h; have : (2 : ℤ) ∣ k := by simpa using h
    exact (Int.not_even_iff_odd.2 hk) (even_iff_two_dvd.2 this)
  exact le_antisymm (PadicInt.norm_le_one _) (not_lt.1 h1)

theorem dyadic_unit_det_map {n : ℕ} (T : Matrix (Fin n) (Fin n) ℤ) (hT : Odd T.det) :
    IsUnit (T.map (Int.castRingHom ℤ_[2])).det := by
  have := RingHom.map_det (Int.castRingHom ℤ_[2]) T
  show IsUnit (RingHom.mapMatrix (Int.castRingHom ℤ_[2]) T).det
  rw [← this]; exact dyadic_isUnit_int_cast_of_odd hT

/-- Equivalence of integer matrices from a congruence mod 8 after an odd-determinant substitution. -/
theorem dyadic_zpEquiv_of_int {n : ℕ} (P Q T0 : Matrix (Fin n) (Fin n) ℤ) (hP : Pᵀ = P) (hQ : Qᵀ = Q)
    (hdP : Odd P.det) (hT : Odd T0.det) (h : ∀ i j, (8 : ℤ) ∣ (T0ᵀ * P * T0) i j - Q i j) :
    ZpEquiv (P.map (Int.cast : ℤ → ℚ_[2])) (Q.map (Int.cast : ℤ → ℚ_[2])) := by
  set ι := Int.castRingHom ℤ_[2]
  have hmap : ∀ M : Matrix (Fin n) (Fin n) ℤ,
      M.map (Int.cast : ℤ → ℚ_[2]) = (M.map ι).map PadicInt.Coe.ringHom := by
    intro M; ext i j; simp [ι]
  rw [hmap, hmap]
  have hTu : IsUnit (T0.map ι) := (Matrix.isUnit_iff_isUnit_det _).2 (dyadic_unit_det_map T0 hT)
  have e1 : ZpEquiv ((P.map ι).map PadicInt.Coe.ringHom) (((T0ᵀ * P * T0).map ι).map PadicInt.Coe.ringHom) := by
    refine ⟨hTu.unit, ?_⟩
    simp only [IsUnit.unit_spec, Matrix.map_mul, Matrix.transpose_map]
  have hsym : (T0ᵀ * P * T0)ᵀ = T0ᵀ * P * T0 := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hP, Matrix.mul_assoc]
  have hdet : Odd (T0ᵀ * P * T0).det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]; exact (hT.mul hdP).mul hT
  have e2 := dyadic_zpEquiv_of_mod8 ((T0ᵀ * P * T0).map ι) (Q.map ι) (by rw [← Matrix.transpose_map, hsym])
    (by rw [← Matrix.transpose_map, hQ]) (dyadic_unit_det_map _ hdet) (fun i j => by
      obtain ⟨c, hc⟩ := h i j
      refine ⟨c, ?_⟩
      have := congrArg (Int.cast : ℤ → ℤ_[2]) hc
      rw [show (2 : ℤ_[2]) ^ 3 = 8 by norm_num]; simpa [ι] using this)
  exact e1.trans e2

/-- A unit of `ℤ₂` is congruent mod 8 to one of `1, 3, 5, 7`. -/
theorem dyadic_exists_mod8 {w : ℤ_[2]} (hw : IsUnit w) :
    ∃ u₀ : ℤ, (u₀ = 1 ∨ u₀ = 3 ∨ u₀ = 5 ∨ u₀ = 7) ∧ (2 : ℤ_[2]) ^ 3 ∣ w - u₀ := by
  have hspec := PadicInt.appr_spec 3 w
  rw [Ideal.mem_span_singleton] at hspec
  have hlt := PadicInt.appr_lt w 3
  have hodd : ¬ 2 ∣ PadicInt.appr w 3 := by
    intro h2
    have h2' : (2 : ℤ_[2]) ∣ ((PadicInt.appr w 3 : ℕ) : ℤ_[2]) := by
      obtain ⟨c, hc⟩ := h2; exact ⟨c, by rw [hc]; push_cast; ring⟩
    have h8 : (2 : ℤ_[2]) ∣ w - PadicInt.appr w 3 := by
      refine (dvd_pow_self (2 : ℤ_[2]) (by norm_num : 3 ≠ 0)).trans ?_
      simpa using hspec
    have : (2 : ℤ_[2]) ∣ w := by
      have := dvd_add h8 h2'
      simpa using this
    have h1 := (PadicInt.norm_lt_one_iff_dvd (p := 2) w).2 (by simpa using this)
    rw [PadicInt.isUnit_iff.1 hw] at h1
    exact lt_irrefl _ h1
  refine ⟨(PadicInt.appr w 3 : ℕ), ?_, by simpa using hspec⟩
  have : PadicInt.appr w 3 < 8 := by simpa using hlt
  omega

private theorem ZpEquiv.smul' {F G : Matrix (Fin n) (Fin n) ℚ_[2]} (c : ℚ_[2]) (h : ZpEquiv F G) :
    ZpEquiv (c • F) (c • G) := by
  obtain ⟨T, rfl⟩ := h
  exact ⟨T, by rw [Matrix.mul_smul, Matrix.smul_mul]⟩

/-- Lift a unit of `ℚ₂` to `ℤ₂` together with its residue mod 8. -/
theorem dyadic_exists_lift {u : ℚ_[2]} (hu : ‖u‖ = 1) :
    ∃ (w : ℤ_[2]) (u₀ : ℤ), (w : ℚ_[2]) = u ∧ IsUnit w ∧ (u₀ = 1 ∨ u₀ = 3 ∨ u₀ = 5 ∨ u₀ = 7) ∧
      (2 : ℤ_[2]) ^ 3 ∣ w - u₀ := by
  have hw : IsUnit (⟨u, hu.le⟩ : ℤ_[2]) := PadicInt.isUnit_iff.2 (by exact hu)
  obtain ⟨u₀, h1, h2⟩ := dyadic_exists_mod8 hw
  exact ⟨⟨u, hu.le⟩, u₀, rfl, hw, h1, h2⟩

theorem dyadic_isUnit_three : IsUnit (3 : ℤ_[2]) := by
  simpa using dyadic_isUnit_int_cast_of_odd (k := 3) (by decide)

private theorem ex48_int (u₀ : ℤ) (h : u₀ = 1 ∨ u₀ = 3 ∨ u₀ = 5 ∨ u₀ = 7) :
    ZpEquiv !![(u₀ : ℚ_[2]), 0, 0; 0, 2, 1; 0, 1, 2] !![3 * (u₀ : ℚ_[2]), 0, 0; 0, -u₀, 0; 0, 0, -u₀] := by
  have key : ∀ T0 : Matrix (Fin 3) (Fin 3) ℤ, Odd T0.det →
      (∀ i j, (8 : ℤ) ∣ (T0ᵀ * !![u₀, 0, 0; 0, 2, 1; 0, 1, 2] * T0) i j - (!![3 * u₀, 0, 0; 0, -u₀, 0; 0, 0, -u₀]) i j) →
      Odd u₀ →
      ZpEquiv !![(u₀ : ℚ_[2]), 0, 0; 0, 2, 1; 0, 1, 2] !![3 * (u₀ : ℚ_[2]), 0, 0; 0, -u₀, 0; 0, 0, -u₀] := by
    intro T0 hT hd hu
    have := dyadic_zpEquiv_of_int (!![u₀, 0, 0; 0, 2, 1; 0, 1, 2] : Matrix (Fin 3) (Fin 3) ℤ)
      !![3 * u₀, 0, 0; 0, -u₀, 0; 0, 0, -u₀] T0
      (by ext i j; fin_cases i <;> fin_cases j <;> rfl) (by ext i j; fin_cases i <;> fin_cases j <;> rfl)
      (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; exact hu.mul (by decide)) hT hd
    convert this using 1 <;> (ext i j; fin_cases i <;> fin_cases j <;> simp)
  rcases h with rfl | rfl | rfl | rfl
  · exact key !![-3,-3,-3; -3,-3,2; -1,-2,-1] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) (by decide)
  · exact key !![-3,-3,-3; -3,-1,0; -3,4,3] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) (by decide)
  · exact key !![-3,-3,-3; -3,-3,2; -1,2,3] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) (by decide)
  · exact key !![-3,-3,-3; -3,-1,0; -3,0,-1] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) (by decide)

private theorem coe_ofNat' (n : ℕ) [n.AtLeastTwo] :
    (((OfNat.ofNat n : ℤ_[2])) : ℚ_[2]) = OfNat.ofNat n := by
  exact_mod_cast PadicInt.coe_natCast (p := 2) n

private theorem ex47_int (u₀ : ℤ) (h : u₀ = 1 ∨ u₀ = 3 ∨ u₀ = 5 ∨ u₀ = 7) :
    ZpEquiv !![(u₀ : ℚ_[2]), 0, 0; 0, 0, 1; 0, 1, 0] !![(u₀ : ℚ_[2]), 0, 0; 0, u₀, 0; 0, 0, -u₀] := by
  have key : ∀ T0 : Matrix (Fin 3) (Fin 3) ℤ, Odd T0.det →
      (∀ i j, (8 : ℤ) ∣ (T0ᵀ * !![u₀, 0, 0; 0, 0, 1; 0, 1, 0] * T0) i j - (!![u₀, 0, 0; 0, u₀, 0; 0, 0, -u₀]) i j) →
      Odd u₀ →
      ZpEquiv !![(u₀ : ℚ_[2]), 0, 0; 0, 0, 1; 0, 1, 0] !![(u₀ : ℚ_[2]), 0, 0; 0, u₀, 0; 0, 0, -u₀] := by
    intro T0 hT hd hu
    have := dyadic_zpEquiv_of_int (!![u₀, 0, 0; 0, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℤ)
      !![u₀, 0, 0; 0, u₀, 0; 0, 0, -u₀] T0
      (by ext i j; fin_cases i <;> fin_cases j <;> rfl) (by ext i j; fin_cases i <;> fin_cases j <;> rfl)
      (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; exact hu) hT hd
    convert this using 1 <;> (ext i j; fin_cases i <;> fin_cases j <;> simp)
  rcases h with rfl | rfl | rfl | rfl
  · exact key !![-3,-3,-3; -3,0,-3; 0,3,3] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) (by decide)
  · exact key !![-3,-3,-3; -3,0,-3; 0,1,1] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) (by decide)
  · exact key !![-3,-3,-3; -3,0,-3; 0,-1,-1] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) (by decide)
  · exact key !![-3,-3,-3; -3,0,-3; 0,-3,-3] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) (by decide)

private theorem ex48_gen {u : ℚ_[2]} (hu : ‖u‖ = 1) :
    ZpEquiv !![u, 0, 0; 0, 2, 1; 0, 1, 2] !![3 * u, 0, 0; 0, -u, 0; 0, 0, -u] := by
  obtain ⟨w, u₀, rfl, hw, h0, hd⟩ := dyadic_exists_lift hu
  have h3 := dyadic_isUnit_three
  have hd1 : (2 : ℤ_[2]) ^ 3 ∣ 3 * w - 3 * (u₀ : ℤ_[2]) := by rw [← mul_sub]; exact hd.mul_left 3
  have hd2 : (2 : ℤ_[2]) ^ 3 ∣ -w + (u₀ : ℤ_[2]) := by
    rw [show -w + (u₀ : ℤ_[2]) = -(w - u₀) by ring]; exact (dvd_neg).2 hd
  have e1 := dyadic_zpEquiv_of_mod8 (!![w, 0, 0; 0, 2, 1; 0, 1, 2]) (!![(u₀ : ℤ_[2]), 0, 0; 0, 2, 1; 0, 1, 2])
    (by ext i j; fin_cases i <;> fin_cases j <;> rfl) (by ext i j; fin_cases i <;> fin_cases j <;> rfl)
    (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; exact ⟨hw, by norm_num; exact h3⟩)
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [hd])
  have e2 := dyadic_zpEquiv_of_mod8 (!![3 * w, 0, 0; 0, -w, 0; 0, 0, -w]) (!![3 * (u₀ : ℤ_[2]), 0, 0; 0, -u₀, 0; 0, 0, -u₀])
    (by ext i j; fin_cases i <;> fin_cases j <;> rfl) (by ext i j; fin_cases i <;> fin_cases j <;> rfl)
    (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; exact ⟨h3, hw⟩)
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [hd1, hd2])
  have e3 := ex48_int u₀ h0
  have e1' : ZpEquiv !![(w : ℚ_[2]), 0, 0; 0, 2, 1; 0, 1, 2] !![(u₀ : ℚ_[2]), 0, 0; 0, 2, 1; 0, 1, 2] := by
    convert e1 using 1 <;> (ext i j; fin_cases i <;> fin_cases j <;> simp <;> first | rfl | exact Or.inl rfl)
  have e2' : ZpEquiv !![3 * (w : ℚ_[2]), 0, 0; 0, -w, 0; 0, 0, -w] !![3 * (u₀ : ℚ_[2]), 0, 0; 0, -u₀, 0; 0, 0, -u₀] := by
    convert e2 using 1 <;> (ext i j; fin_cases i <;> fin_cases j <;> simp <;> first | rfl | exact Or.inl rfl)
  exact e1'.trans (e3.trans e2'.symm)

private theorem ex47_gen {u : ℚ_[2]} (hu : ‖u‖ = 1) :
    ZpEquiv !![u, 0, 0; 0, 0, 1; 0, 1, 0] !![u, 0, 0; 0, u, 0; 0, 0, -u] := by
  obtain ⟨w, u₀, rfl, hw, h0, hd⟩ := dyadic_exists_lift hu
  have hd2 : (2 : ℤ_[2]) ^ 3 ∣ -w + (u₀ : ℤ_[2]) := by
    rw [show -w + (u₀ : ℤ_[2]) = -(w - u₀) by ring]; exact (dvd_neg).2 hd
  have e1 := dyadic_zpEquiv_of_mod8 (!![w, 0, 0; 0, 0, 1; 0, 1, 0]) (!![(u₀ : ℤ_[2]), 0, 0; 0, 0, 1; 0, 1, 0])
    (by ext i j; fin_cases i <;> fin_cases j <;> rfl) (by ext i j; fin_cases i <;> fin_cases j <;> rfl)
    (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; exact hw)
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [hd])
  have e2 := dyadic_zpEquiv_of_mod8 (!![w, 0, 0; 0, w, 0; 0, 0, -w]) (!![(u₀ : ℤ_[2]), 0, 0; 0, u₀, 0; 0, 0, -u₀])
    (by ext i j; fin_cases i <;> fin_cases j <;> rfl) (by ext i j; fin_cases i <;> fin_cases j <;> rfl)
    (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; exact hw)
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [hd, hd2])
  have e3 := ex47_int u₀ h0
  have e1' : ZpEquiv !![(w : ℚ_[2]), 0, 0; 0, 0, 1; 0, 1, 0] !![(u₀ : ℚ_[2]), 0, 0; 0, 0, 1; 0, 1, 0] := by
    convert e1 using 1 <;> (ext i j; fin_cases i <;> fin_cases j <;> simp <;> first | rfl | exact Or.inl rfl)
  have e2' : ZpEquiv !![(w : ℚ_[2]), 0, 0; 0, w, 0; 0, 0, -w] !![(u₀ : ℚ_[2]), 0, 0; 0, u₀, 0; 0, 0, -u₀] := by
    convert e2 using 1 <;> (ext i j; fin_cases i <;> fin_cases j <;> simp <;> first | rfl | exact Or.inl rfl)
  exact e1'.trans (e3.trans e2'.symm)

private theorem ex49_aux :
    ZpEquiv (p := 2) !![2, 1, 0, 0; 1, 2, 0, 0; 0, 0, 2, 1; 0, 0, 1, 2]
      !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] := by
  have := dyadic_zpEquiv_of_int (!![2, 1, 0, 0; 1, 2, 0, 0; 0, 0, 2, 1; 0, 0, 1, 2] : Matrix (Fin 4) (Fin 4) ℤ)
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
    !![-3,-3,-3,-2; -3,-3,-2,3; -3,-1,4,4; -1,4,-3,-1]
    (by ext i j; fin_cases i <;> fin_cases j <;> rfl) (by ext i j; fin_cases i <;> fin_cases j <;> rfl)
    (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
    (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] )
  convert this using 1 <;> (ext i j; fin_cases i <;> fin_cases j <;> simp)



/-! ### Helpers: equivalences and block sums -/

/-- The permutation matrix of `σ` as an element of `GL`. -/
noncomputable def dyadicPermGL (σ : Equiv.Perm (Fin n)) : GL (Fin n) ℤ_[2] :=
  ⟨(1 : Matrix (Fin n) (Fin n) ℤ_[2]).submatrix id σ, (1 : Matrix (Fin n) (Fin n) ℤ_[2]).submatrix σ id,
    by rw [← Matrix.submatrix_mul _ _ _ _ _ σ.bijective, Matrix.mul_one]; simp,
    by rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_one]; simp⟩

theorem dyadic_zpEquiv_perm (G : Matrix (Fin n) (Fin n) ℚ_[2]) (σ : Equiv.Perm (Fin n)) :
    ZpEquiv G (G.submatrix σ σ) := by
  refine ⟨dyadicPermGL σ, ?_⟩
  have h : (dyadicPermGL σ).val.map PadicInt.Coe.ringHom = (1 : Matrix (Fin n) (Fin n) ℚ_[2]).submatrix id σ := by
    ext i j; simp [dyadicPermGL, Matrix.one_apply]
  rw [h, Matrix.transpose_submatrix, Matrix.transpose_one]
  calc _ = (1 : Matrix (Fin n) (Fin n) ℚ_[2]).submatrix σ id * G.submatrix id id *
      (1 : Matrix (Fin n) (Fin n) ℚ_[2]).submatrix id σ := rfl
    _ = G.submatrix σ σ := by
      rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.one_mul,
        ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_one]

/-- Block diagonal elements of `GL`. -/
noncomputable def dyadicBlockGL {a b : ℕ} (T : GL (Fin a) ℤ_[2]) (S : GL (Fin b) ℤ_[2]) :
    GL (Fin (a + b)) ℤ_[2] :=
  ⟨(Matrix.fromBlocks T.val 0 0 S.val).submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
   (Matrix.fromBlocks (T⁻¹).val 0 0 (S⁻¹).val).submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
    by rw [← Matrix.submatrix_mul _ _ _ _ _ finSumFinEquiv.symm.bijective, Matrix.fromBlocks_multiply]; simp,
    by rw [← Matrix.submatrix_mul _ _ _ _ _ finSumFinEquiv.symm.bijective, Matrix.fromBlocks_multiply]; simp⟩

theorem dyadic_orthSumMat_eq {K : Type*} [Zero K] {a b : ℕ} (F : Matrix (Fin a) (Fin a) K)
    (G : Matrix (Fin b) (Fin b) K) :
    orthSumMat F G = (Matrix.fromBlocks F 0 0 G).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  simp [orthSumMat, Matrix.reindex_apply]

theorem dyadic_zpEquiv_orthSum {a b : ℕ} {B B' : Matrix (Fin a) (Fin a) ℚ_[2]}
    {E E' : Matrix (Fin b) (Fin b) ℚ_[2]} (h1 : ZpEquiv B B') (h2 : ZpEquiv E E') :
    ZpEquiv (orthSumMat B E) (orthSumMat B' E') := by
  obtain ⟨T, rfl⟩ := h1
  obtain ⟨S, rfl⟩ := h2
  refine ⟨dyadicBlockGL T S, ?_⟩
  have h : (dyadicBlockGL T S).val.map PadicInt.Coe.ringHom = (Matrix.fromBlocks (T.val.map PadicInt.Coe.ringHom) 0 0
      (S.val.map PadicInt.Coe.ringHom)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    show ((Matrix.fromBlocks T.val 0 0 S.val).submatrix finSumFinEquiv.symm finSumFinEquiv.symm).map _ = _
    rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]
    rw [Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
  rw [h, dyadic_orthSumMat_eq, dyadic_orthSumMat_eq, Matrix.transpose_submatrix,
    ← Matrix.submatrix_mul _ _ _ _ _ finSumFinEquiv.symm.bijective,
    ← Matrix.submatrix_mul _ _ _ _ _ finSumFinEquiv.symm.bijective, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp


/-- The unipotent element `[[1, -Λ], [0, 1]]` of `GL`. -/
noncomputable def dyadicUnipGL {a b : ℕ} (Λ : Matrix (Fin a) (Fin b) ℤ_[2]) : GL (Fin (a + b)) ℤ_[2] :=
  ⟨(Matrix.fromBlocks 1 (-Λ) 0 1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
   (Matrix.fromBlocks 1 Λ 0 1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
    by rw [← Matrix.submatrix_mul _ _ _ _ _ finSumFinEquiv.symm.bijective, Matrix.fromBlocks_multiply]; simp,
    by rw [← Matrix.submatrix_mul _ _ _ _ _ finSumFinEquiv.symm.bijective, Matrix.fromBlocks_multiply]; simp⟩

theorem dyadic_zpEquiv_split {a b : ℕ} (F : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[2]) (hF : Fᵀ = F)
    (Λ : Matrix (Fin a) (Fin b) ℤ_[2])
    (hC : F.submatrix (Fin.castAdd b) (Fin.natAdd a) =
      F.submatrix (Fin.castAdd b) (Fin.castAdd b) * Λ.map PadicInt.Coe.ringHom) :
    ZpEquiv F (orthSumMat (F.submatrix (Fin.castAdd b) (Fin.castAdd b))
      (F.submatrix (Fin.natAdd a) (Fin.natAdd a) - (Λ.map PadicInt.Coe.ringHom)ᵀ *
        F.submatrix (Fin.castAdd b) (Fin.castAdd b) * Λ.map PadicInt.Coe.ringHom)) := by
  set B := F.submatrix (Fin.castAdd b) (Fin.castAdd b) with hB
  set C := F.submatrix (Fin.castAdd b) (Fin.natAdd a) with hCdef
  set E := F.submatrix (Fin.natAdd a) (Fin.natAdd a) with hE
  set L := Λ.map PadicInt.Coe.ringHom with hL
  have hBt : Bᵀ = B := by
    ext i j; simp [hB, Matrix.transpose_apply]; exact congrFun (congrFun hF _) _
  have hFe : F = (Matrix.fromBlocks B C Cᵀ E).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [hB, hCdef, hE, Matrix.transpose_apply, Matrix.fromBlocks]
    exact congrFun (congrFun hF _) _
  refine ⟨dyadicUnipGL Λ, ?_⟩
  have h : (dyadicUnipGL Λ).val.map PadicInt.Coe.ringHom =
      (Matrix.fromBlocks 1 (-L) 0 1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    show ((Matrix.fromBlocks 1 (-Λ) 0 1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm).map _ = _
    have hneg : (-Λ).map PadicInt.Coe.ringHom = -L := by ext i j; simp [hL]
    rw [← Matrix.submatrix_map, Matrix.fromBlocks_map, hneg]
    simp [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _)]
  have hCt : Cᵀ = Lᵀ * B := by
    rw [hC, Matrix.transpose_mul, hBt]
  conv_lhs => rw [h, hFe]
  rw [dyadic_orthSumMat_eq, Matrix.transpose_submatrix,
    ← Matrix.submatrix_mul _ _ _ _ _ finSumFinEquiv.symm.bijective,
    ← Matrix.submatrix_mul _ _ _ _ _ finSumFinEquiv.symm.bijective, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 1
  simp [hC, hBt, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
  abel


/-- Congruence of an integral binary form modulo 8. -/
private theorem bin_gen (x z q11 q12 q22 p q r s : ℤ) (hdet : Odd (x * z - 1)) (hT : Odd (p * s - q * r))
    (h11 : (8 : ℤ) ∣ x * p ^ 2 + 2 * p * r + z * r ^ 2 - q11)
    (h12 : (8 : ℤ) ∣ x * p * q + p * s + q * r + z * r * s - q12)
    (h22 : (8 : ℤ) ∣ x * q ^ 2 + 2 * q * s + z * s ^ 2 - q22) :
    ZpEquiv !![(x : ℚ_[2]), 1; 1, (z : ℚ_[2])] !![(q11 : ℚ_[2]), q12; q12, q22] := by
  have := dyadic_zpEquiv_of_int (!![x, 1; 1, z] : Matrix (Fin 2) (Fin 2) ℤ) !![q11, q12; q12, q22] !![p, q; r, s]
    (by ext i j; fin_cases i <;> fin_cases j <;> rfl) (by ext i j; fin_cases i <;> fin_cases j <;> rfl)
    (by simpa [Matrix.det_fin_two] using hdet) (by simpa [Matrix.det_fin_two] using hT)
    (by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | (convert h11 using 2 <;> ring1) | (convert h12 using 2 <;> ring1) | (convert h22 using 2 <;> ring1))
  convert this using 1 <;> (ext i j; fin_cases i <;> fin_cases j <;> simp)

private theorem bin_H (x z p q r s : ℤ) (hdet : Odd (x * z - 1)) (hT : Odd (p * s - q * r))
    (h11 : (8 : ℤ) ∣ x * p ^ 2 + 2 * p * r + z * r ^ 2 - 0)
    (h12 : (8 : ℤ) ∣ x * p * q + p * s + q * r + z * r * s - 1)
    (h22 : (8 : ℤ) ∣ x * q ^ 2 + 2 * q * s + z * s ^ 2 - 0) :
    ZpEquiv !![(x : ℚ_[2]), 1; 1, (z : ℚ_[2])] !![0, 1; 1, 0] := by
  simpa using bin_gen x z 0 1 0 p q r s hdet hT h11 h12 h22

private theorem bin_A (x z p q r s : ℤ) (hdet : Odd (x * z - 1)) (hT : Odd (p * s - q * r))
    (h11 : (8 : ℤ) ∣ x * p ^ 2 + 2 * p * r + z * r ^ 2 - 2)
    (h12 : (8 : ℤ) ∣ x * p * q + p * s + q * r + z * r * s - 1)
    (h22 : (8 : ℤ) ∣ x * q ^ 2 + 2 * q * s + z * s ^ 2 - 2) :
    ZpEquiv !![(x : ℚ_[2]), 1; 1, (z : ℚ_[2])] !![2, 1; 1, 2] := by
  simpa using bin_gen x z 2 1 2 p q r s hdet hT h11 h12 h22

private theorem bin_core (x z : ℤ) (hx : x = 0 ∨ x = 2 ∨ x = 4 ∨ x = 6) (hz : z = 0 ∨ z = 2 ∨ z = 4 ∨ z = 6) :
    ZpEquiv !![(x : ℚ_[2]), 1; 1, (z : ℚ_[2])] !![0, 1; 1, 0] ∨
      ZpEquiv !![(x : ℚ_[2]), 1; 1, (z : ℚ_[2])] !![2, 1; 1, 2] := by
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl
  · exact Or.inl (bin_H _ _ (-3) (0) (0) (-3) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact Or.inl (bin_H _ _ (-3) (-1) (-1) (0) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact Or.inl (bin_H _ _ (-3) (-2) (0) (-3) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact Or.inl (bin_H _ _ (-3) (-3) (-3) (0) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact Or.inl (bin_H _ _ (-3) (0) (-1) (-3) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact Or.inr (bin_A _ _ (-3) (-3) (-1) (4) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact Or.inl (bin_H _ _ (-3) (-2) (-3) (-1) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact Or.inr (bin_A _ _ (-3) (-2) (-3) (-3) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact Or.inl (bin_H _ _ (-3) (0) (-2) (-3) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact Or.inl (bin_H _ _ (-3) (-1) (-3) (-2) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact Or.inl (bin_H _ _ (-3) (-2) (-2) (1) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact Or.inl (bin_H _ _ (-3) (-3) (-2) (-1) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact Or.inl (bin_H _ _ (-3) (0) (-3) (-3) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact Or.inr (bin_A _ _ (-3) (-3) (-3) (-2) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact Or.inl (bin_H _ _ (-3) (-2) (-1) (3) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact Or.inr (bin_A _ _ (-3) (-2) (-2) (1) (by decide) (by decide) (by decide) (by decide) (by decide))


theorem dyadic_not_isUnit_of_two_dvd {x : ℤ_[2]} (h : (2 : ℤ_[2]) ∣ x) : ¬ IsUnit x := by
  intro hu
  have h1 := (PadicInt.norm_lt_one_iff_dvd (p := 2) x).2 (by simpa using h)
  rw [PadicInt.isUnit_iff.1 hu] at h1
  exact lt_irrefl _ h1

theorem dyadic_isUnit_mul_sub_one {x z : ℤ_[2]} (hx : (2 : ℤ_[2]) ∣ x) : IsUnit (x * z - 1) := by
  have h : x * z ∈ nonunits ℤ_[2] := fun hu => dyadic_not_isUnit_of_two_dvd hx (isUnit_of_mul_isUnit_left hu)
  have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ h
  have h2 : x * z - 1 = -(1 - x * z) := by ring
  rw [h2]; exact this.neg

theorem dyadic_exists_mod8_even {x : ℤ_[2]} (hx : (2 : ℤ_[2]) ∣ x) :
    ∃ x₀ : ℤ, (x₀ = 0 ∨ x₀ = 2 ∨ x₀ = 4 ∨ x₀ = 6) ∧ (2 : ℤ_[2]) ^ 3 ∣ x - x₀ := by
  have hspec := PadicInt.appr_spec 3 x
  rw [Ideal.mem_span_singleton] at hspec
  have hlt := PadicInt.appr_lt x 3
  have h8 : (2 : ℤ_[2]) ∣ x - PadicInt.appr x 3 := by
    refine (dvd_pow_self (2 : ℤ_[2]) (by norm_num : 3 ≠ 0)).trans ?_
    simpa using hspec
  have h2' : (2 : ℤ_[2]) ∣ ((PadicInt.appr x 3 : ℕ) : ℤ_[2]) := by
    have := dvd_sub hx h8
    simpa using this
  have h4 : 2 ∣ PadicInt.appr x 3 := by
    have := (PadicInt.norm_lt_one_iff_dvd (p := 2) ((PadicInt.appr x 3 : ℕ) : ℤ_[2])).2 (by simpa using h2')
    simpa using this
  refine ⟨(PadicInt.appr x 3 : ℕ), ?_, by simpa using hspec⟩
  have : PadicInt.appr x 3 < 8 := by simpa using hlt
  omega


/-- The diagonal element `diag(1, v)` of `GL₂(ℤ₂)`. -/
noncomputable def dyadicDiagGL (v : ℤ_[2]ˣ) : GL (Fin 2) ℤ_[2] :=
  ⟨!![1, 0; 0, (v : ℤ_[2])], !![1, 0; 0, ((v⁻¹ : ℤ_[2]ˣ) : ℤ_[2])],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

/-- An even-diagonal binary form with unit off-diagonal entry is equivalent to `H` or to `A`. -/
theorem dyadic_bin_unit {x z β : ℤ_[2]} (hx : (2 : ℤ_[2]) ∣ x) (hz : (2 : ℤ_[2]) ∣ z) (hβ : IsUnit β) :
    ZpEquiv !![(x : ℚ_[2]), β; β, z] !![0, 1; 1, 0] ∨ ZpEquiv !![(x : ℚ_[2]), β; β, z] !![2, 1; 1, 2] := by
  set u := hβ.unit with hu
  have hβu : (u : ℤ_[2]) = β := rfl
  set z' : ℤ_[2] := z * ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) ^ 2 with hz'
  have hz'2 : (2 : ℤ_[2]) ∣ z' := hz.mul_right _
  have e0 : ZpEquiv !![(x : ℚ_[2]), β; β, z] !![(x : ℚ_[2]), 1; 1, (z' : ℚ_[2])] := by
    refine ⟨dyadicDiagGL u⁻¹, ?_⟩
    have hb : (β : ℚ_[2]) * (((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) : ℚ_[2]) = 1 := by
      rw [← PadicInt.coe_mul, ← hβu, ← Units.val_mul, mul_inv_cancel]; simp
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dyadicDiagGL, Matrix.mul_apply, Fin.sum_univ_two, hz', PadicInt.coe_mul] <;> try ring1
    all_goals first | exact hb | (rw [mul_comm]; exact hb)
  obtain ⟨x₀, hx₀, hdx⟩ := dyadic_exists_mod8_even hx
  obtain ⟨z₀, hz₀, hdz⟩ := dyadic_exists_mod8_even hz'2
  have e1 := dyadic_zpEquiv_of_mod8 (!![x, 1; 1, z']) (!![(x₀ : ℤ_[2]), 1; 1, (z₀ : ℤ_[2])])
    (by ext i j; fin_cases i <;> fin_cases j <;> rfl) (by ext i j; fin_cases i <;> fin_cases j <;> rfl)
    (by rw [Matrix.det_fin_two_of]; simpa using dyadic_isUnit_mul_sub_one (z := z') hx)
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [hdx, hdz])
  have e1' : ZpEquiv !![(x : ℚ_[2]), 1; 1, (z' : ℚ_[2])] !![(x₀ : ℚ_[2]), 1; 1, (z₀ : ℚ_[2])] := by
    convert e1 using 1 <;> (ext i j; fin_cases i <;> fin_cases j <;> simp)
  rcases bin_core x₀ z₀ hx₀ hz₀ with h | h
  · exact Or.inl (e0.trans (e1'.trans h))
  · exact Or.inr (e0.trans (e1'.trans h))


private theorem norm_two_zpow (e : ℤ) : ‖(2 : ℚ_[2]) ^ e‖ = (2 : ℝ) ^ (-e) := by
  rw [norm_zpow]
  have h : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by simpa using (Padic.norm_p (p := 2))
  rw [h, _root_.inv_zpow']

/-- A nonzero `b` is `2^e` times a unit. -/
private theorem exists_unit_scale {b : ℚ_[2]} (hb : b ≠ 0) :
    ∃ e : ℤ, (2 : ℚ_[2]) ^ e ≠ 0 ∧ ‖(2 : ℚ_[2]) ^ e‖ = ‖b‖ := by
  refine ⟨b.valuation, zpow_ne_zero _ (by norm_num), ?_⟩
  rw [norm_two_zpow, Padic.norm_eq_zpow_neg_valuation hb]
  simp

private theorem block1 {b : ℚ_[2]} (hb : b ≠ 0) :
    ∃ e u : ℤ, (u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) ∧ ZpEquiv !![b] (DyBlock.sq e u).mat := by
  obtain ⟨e, hs0, hs⟩ := exists_unit_scale hb
  set s : ℚ_[2] := (2 : ℚ_[2]) ^ e with hsdef
  have hu : ‖b / s‖ = 1 := by
    rw [norm_div, hs, div_self (norm_ne_zero_iff.2 hb)]
  obtain ⟨w, u₀, hw, hwu, h0, hd⟩ := dyadic_exists_lift hu
  have e1 := dyadic_zpEquiv_of_mod8 (!![w]) (!![(u₀ : ℤ_[2])])
    (by ext i j; fin_cases i; fin_cases j; rfl) (by ext i j; fin_cases i; fin_cases j; rfl)
    (by simpa using hwu) (by intro i j; fin_cases i; fin_cases j; simpa using hd)
  have e1' : ZpEquiv !![b / s] !![(u₀ : ℚ_[2])] := by
    rw [← hw]
    convert e1 using 1 <;> (ext i j; fin_cases i; fin_cases j; simp)
  refine ⟨e, u₀, h0, ?_⟩
  have := e1'.smul' s
  have h1 : s • !![b / s] = !![b] := by
    ext i j; fin_cases i; fin_cases j; simp [mul_div_cancel₀ _ hs0]
  have h2 : s • !![(u₀ : ℚ_[2])] = (DyBlock.sq e u₀).mat := by
    ext i j; fin_cases i; fin_cases j; simp [DyBlock.mat, hsdef]
  rw [h1, h2] at this
  exact this

private theorem block2 {a β c : ℚ_[2]} (hβ : β ≠ 0) (ha : ‖a‖ < ‖β‖) (hc : ‖c‖ < ‖β‖) :
    ∃ e : ℤ, ZpEquiv !![a, β; β, c] (DyBlock.hyp e).mat ∨ ZpEquiv !![a, β; β, c] (DyBlock.ell e).mat := by
  obtain ⟨e, hs0, hs⟩ := exists_unit_scale hβ
  set s : ℚ_[2] := (2 : ℚ_[2]) ^ e with hsdef
  have hspos : 0 < ‖s‖ := norm_pos_iff.2 hs0
  have hn : ∀ y : ℚ_[2], ‖y‖ < ‖β‖ → ‖y / s‖ < 1 := fun y hy => by
    rw [norm_div, div_lt_one hspos, hs]; exact hy
  have hβ1 : ‖β / s‖ = 1 := by rw [norm_div, hs, div_self (norm_ne_zero_iff.2 hβ)]
  let A : ℤ_[2] := ⟨a / s, (hn a ha).le⟩
  let C : ℤ_[2] := ⟨c / s, (hn c hc).le⟩
  let Bt : ℤ_[2] := ⟨β / s, hβ1.le⟩
  have hA : (2 : ℤ_[2]) ∣ A := by
    have := (PadicInt.norm_lt_one_iff_dvd (p := 2) A).1 (hn a ha); simpa using this
  have hC : (2 : ℤ_[2]) ∣ C := by
    have := (PadicInt.norm_lt_one_iff_dvd (p := 2) C).1 (hn c hc); simpa using this
  have hB : IsUnit Bt := PadicInt.isUnit_iff.2 hβ1
  refine ⟨e, ?_⟩
  have key := dyadic_bin_unit hA hC hB
  have eq : (2 : ℚ_[2]) ^ e • !![(A : ℚ_[2]), Bt; Bt, C] = !![a, β; β, c] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [A, C, Bt, hsdef.symm, mul_div_cancel₀ _ hs0]
  rcases key with h | h
  · left
    have := h.smul' ((2 : ℚ_[2]) ^ e)
    rw [eq] at this; exact this
  · right
    have := h.smul' ((2 : ℚ_[2]) ^ e)
    rw [eq] at this; exact this


private theorem single_lambda {m : ℕ} (B : Matrix (Fin 1) (Fin 1) ℚ_[2]) (C : Matrix (Fin 1) (Fin m) ℚ_[2])
    (hB : B 0 0 ≠ 0) (hC : ∀ k, ‖C 0 k‖ ≤ ‖B 0 0‖) :
    ∃ Λ : Matrix (Fin 1) (Fin m) ℤ_[2], C = B * Λ.map PadicInt.Coe.ringHom := by
  have hb : ∀ k, ‖C 0 k / B 0 0‖ ≤ 1 := fun k => by
    rw [norm_div]; exact (div_le_one (norm_pos_iff.2 hB)).2 (hC k)
  refine ⟨Matrix.of fun _ k => ⟨C 0 k / B 0 0, hb k⟩, ?_⟩
  ext r k
  fin_cases r
  rw [Matrix.mul_apply, Fin.sum_univ_one]
  show C 0 k = B 0 0 * (C 0 k / B 0 0)
  field_simp

private theorem pair_lambda {m : ℕ} (B : Matrix (Fin 2) (Fin 2) ℚ_[2]) (C : Matrix (Fin 2) (Fin m) ℚ_[2])
    (hBt : Bᵀ = B) (hβ : B 0 1 ≠ 0) (ha : ‖B 0 0‖ < ‖B 0 1‖) (hc : ‖B 1 1‖ < ‖B 0 1‖)
    (hC : ∀ i k, ‖C i k‖ ≤ ‖B 0 1‖) :
    ∃ Λ : Matrix (Fin 2) (Fin m) ℤ_[2], C = B * Λ.map PadicInt.Coe.ringHom := by
  have h10 : B 1 0 = B 0 1 := by simpa using congrFun (congrFun hBt 0) 1
  have hβpos : 0 < ‖B 0 1‖ := norm_pos_iff.2 hβ
  have hD : ‖B.det‖ = ‖B 0 1‖ * ‖B 0 1‖ := by
    have hlt : ‖B 0 0 * B 1 1‖ < ‖B 0 1 * B 0 1‖ := by
      rw [norm_mul, norm_mul]
      exact mul_lt_mul'' ha hc (norm_nonneg _) (norm_nonneg _)
    rw [Matrix.det_fin_two, h10, sub_eq_add_neg,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; exact hlt.ne), norm_neg,
      max_eq_right hlt.le, norm_mul]
  have hD0 : B.det ≠ 0 := fun h => by rw [h, norm_zero] at hD; nlinarith
  have hadj : ∀ r s, ‖(Matrix.adjugate B) r s‖ ≤ ‖B 0 1‖ := by
    intro r s
    rw [Matrix.adjugate_fin_two]
    fin_cases r <;> fin_cases s <;> simp [h10] <;> first | exact hc.le | exact ha.le | exact le_rfl
  set Lam : Matrix (Fin 2) (Fin m) ℚ_[2] := B.det⁻¹ • (Matrix.adjugate B * C) with hLam
  have hbd : ∀ r k, ‖Lam r k‖ ≤ 1 := by
    intro r k
    simp only [hLam, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two, norm_mul, norm_inv]
    rw [hD]
    have h1 : ‖(Matrix.adjugate B) r 0 * C 0 k + (Matrix.adjugate B) r 1 * C 1 k‖ ≤ ‖B 0 1‖ * ‖B 0 1‖ := by
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]; exact mul_le_mul (hadj _ _) (hC _ _) (norm_nonneg _) hβpos.le
      · rw [norm_mul]; exact mul_le_mul (hadj _ _) (hC _ _) (norm_nonneg _) hβpos.le
    calc (‖B 0 1‖ * ‖B 0 1‖)⁻¹ * ‖(Matrix.adjugate B) r 0 * C 0 k + (Matrix.adjugate B) r 1 * C 1 k‖
        ≤ (‖B 0 1‖ * ‖B 0 1‖)⁻¹ * (‖B 0 1‖ * ‖B 0 1‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := inv_mul_cancel₀ (by positivity)
  refine ⟨Matrix.of fun r k => ⟨Lam r k, hbd r k⟩, ?_⟩
  show C = B * Lam
  rw [hLam, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul,
    smul_smul, inv_mul_cancel₀ hD0, one_smul]


theorem dyadic_det_orthSumMat {a b : ℕ} (B : Matrix (Fin a) (Fin a) ℚ_[2]) (E : Matrix (Fin b) (Fin b) ℚ_[2]) :
    (orthSumMat B E).det = B.det * E.det := by
  rw [dyadic_orthSumMat_eq, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

/-- Equivalent forms have determinants differing by the square of a unit. -/
theorem dyadic_zpEquiv_det_rel {F G : Matrix (Fin n) (Fin n) ℚ_[2]} (h : ZpEquiv F G) :
    ∃ s : ℚ_[2], ‖s‖ = 1 ∧ G.det = s ^ 2 * F.det := by
  obtain ⟨T, rfl⟩ := h
  have hu : IsUnit T.val.det := (Matrix.isUnit_iff_isUnit_det _).1 T.isUnit
  have hmap : (T.val.map PadicInt.Coe.ringHom).det = ((T.val.det : ℤ_[2]) : ℚ_[2]) :=
    (RingHom.map_det PadicInt.Coe.ringHom T.val).symm
  refine ⟨((T.val.det : ℤ_[2]) : ℚ_[2]), ?_, ?_⟩
  · have := PadicInt.isUnit_iff.1 hu
    rwa [PadicInt.norm_def] at this
  · rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hmap]; ring

theorem dyadic_zpEquiv_det_ne {F G : Matrix (Fin n) (Fin n) ℚ_[2]} (h : ZpEquiv F G) (hF : F.det ≠ 0) :
    G.det ≠ 0 := by
  obtain ⟨s, hs, hG⟩ := dyadic_zpEquiv_det_rel h
  have : s ≠ 0 := fun h0 => by rw [h0, norm_zero] at hs; exact zero_ne_one hs
  rw [hG]; exact mul_ne_zero (pow_ne_zero _ this) hF

private theorem split_symm {a b : ℕ} {B : Matrix (Fin a) (Fin a) ℚ_[2]} {E : Matrix (Fin b) (Fin b) ℚ_[2]}
    {L : Matrix (Fin a) (Fin b) ℚ_[2]} (hB : Bᵀ = B) (hE : Eᵀ = E) : (E - Lᵀ * B * L)ᵀ = E - Lᵀ * B * L := by
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hB, hE,
    Matrix.mul_assoc]

private theorem assemble {m : ℕ} (b : DyBlock) (hv : b.Valid) (F : Matrix (Fin (b.dim + m)) (Fin (b.dim + m)) ℚ_[2])
    (E' : Matrix (Fin m) (Fin m) ℚ_[2]) (hFE : ZpEquiv F (orthSumMat b.mat E'))
    (IH : ∃ D : List DyBlock, (∀ x ∈ D, x.Valid) ∧ ∃ h : dyDim D = m,
      ZpEquiv E' ((dyMat D).submatrix (Fin.cast h.symm) (Fin.cast h.symm))) :
    ∃ D : List DyBlock, (∀ x ∈ D, x.Valid) ∧ ∃ h : dyDim D = b.dim + m,
      ZpEquiv F ((dyMat D).submatrix (Fin.cast h.symm) (Fin.cast h.symm)) := by
  obtain ⟨D', hv', h', hE⟩ := IH
  subst h'
  refine ⟨b :: D', ?_, rfl, ?_⟩
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hv
    · exact hv' x hx
  · exact hFE.trans (dyadic_zpEquiv_orthSum (ZpEquiv.refl _) hE)


private theorem step1core {m : ℕ} (F : Matrix (Fin (1 + m)) (Fin (1 + m)) ℚ_[2]) (hF : Fᵀ = F)
    (hb : F (Fin.castAdd m 0) (Fin.castAdd m 0) ≠ 0)
    (hC : ∀ k, ‖F (Fin.castAdd m 0) (Fin.natAdd 1 k)‖ ≤ ‖F (Fin.castAdd m 0) (Fin.castAdd m 0)‖) :
    ∃ Λ : Matrix (Fin 1) (Fin m) ℤ_[2],
      ZpEquiv F (orthSumMat (F.submatrix (Fin.castAdd m) (Fin.castAdd m))
        (F.submatrix (Fin.natAdd 1) (Fin.natAdd 1) - (Λ.map PadicInt.Coe.ringHom)ᵀ *
          F.submatrix (Fin.castAdd m) (Fin.castAdd m) * Λ.map PadicInt.Coe.ringHom)) := by
  obtain ⟨Λ, hΛ⟩ := single_lambda (F.submatrix (Fin.castAdd m) (Fin.castAdd m))
    (F.submatrix (Fin.castAdd m) (Fin.natAdd 1)) (by simpa using hb) (fun k => by simpa using hC k)
  exact ⟨Λ, dyadic_zpEquiv_split F hF Λ hΛ⟩

private theorem step2core {m : ℕ} (F : Matrix (Fin (2 + m)) (Fin (2 + m)) ℚ_[2]) (hF : Fᵀ = F)
    (hβ : F (Fin.castAdd m 0) (Fin.castAdd m 1) ≠ 0)
    (ha : ‖F (Fin.castAdd m 0) (Fin.castAdd m 0)‖ < ‖F (Fin.castAdd m 0) (Fin.castAdd m 1)‖)
    (hc : ‖F (Fin.castAdd m 1) (Fin.castAdd m 1)‖ < ‖F (Fin.castAdd m 0) (Fin.castAdd m 1)‖)
    (hC : ∀ (i : Fin 2) (k : Fin m), ‖F (Fin.castAdd m i) (Fin.natAdd 2 k)‖ ≤
      ‖F (Fin.castAdd m 0) (Fin.castAdd m 1)‖) :
    ∃ Λ : Matrix (Fin 2) (Fin m) ℤ_[2],
      ZpEquiv F (orthSumMat (F.submatrix (Fin.castAdd m) (Fin.castAdd m))
        (F.submatrix (Fin.natAdd 2) (Fin.natAdd 2) - (Λ.map PadicInt.Coe.ringHom)ᵀ *
          F.submatrix (Fin.castAdd m) (Fin.castAdd m) * Λ.map PadicInt.Coe.ringHom)) := by
  have hBt : (F.submatrix (Fin.castAdd m) (Fin.castAdd m))ᵀ = F.submatrix (Fin.castAdd m) (Fin.castAdd m) := by
    rw [Matrix.transpose_submatrix, hF]
  obtain ⟨Λ, hΛ⟩ := pair_lambda (F.submatrix (Fin.castAdd m) (Fin.castAdd m))
    (F.submatrix (Fin.castAdd m) (Fin.natAdd 2)) hBt (by simpa using hβ) (by simpa using ha)
    (by simpa using hc) (fun i k => by simpa using hC i k)
  exact ⟨Λ, dyadic_zpEquiv_split F hF Λ hΛ⟩

theorem dyadic_front1 {m : ℕ} (a : Fin (1 + m)) :
    ∃ σ : Equiv.Perm (Fin (1 + m)), σ (Fin.castAdd m 0) = a :=
  ⟨Equiv.swap (Fin.castAdd m 0) a, Equiv.swap_apply_left _ _⟩

theorem dyadic_front2 {m : ℕ} {i j : Fin (2 + m)} (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin (2 + m)), σ (Fin.castAdd m 0) = i ∧ σ (Fin.castAdd m 1) = j := by
  have h01 : (Fin.castAdd m (0 : Fin 2)) ≠ Fin.castAdd m 1 := by
    intro h; have := congrArg Fin.val h; simp at this
  set τ1 := Equiv.swap (Fin.castAdd m (0 : Fin 2)) i with hτ1
  set j' := τ1 j with hj'
  set τ2 := Equiv.swap (Fin.castAdd m (1 : Fin 2)) j' with hτ2
  have hj'0 : Fin.castAdd m (0 : Fin 2) ≠ j' := by
    intro h
    apply hij
    have h1 : τ1 (Fin.castAdd m 0) = i := Equiv.swap_apply_left _ _
    have h2 : τ1 j' = j := Equiv.swap_apply_self _ _ _
    calc i = τ1 (Fin.castAdd m 0) := h1.symm
      _ = τ1 j' := by rw [h]
      _ = j := h2
  refine ⟨τ1 * τ2, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, hτ2, Equiv.swap_apply_of_ne_of_ne h01 hj'0, hτ1, Equiv.swap_apply_left]
  · rw [Equiv.Perm.mul_apply, hτ2, Equiv.swap_apply_left, hj', hτ1, Equiv.swap_apply_self]


private theorem dyadic_aux : ∀ (n : ℕ) (F : Matrix (Fin n) (Fin n) ℚ_[2]), Fᵀ = F → F.det ≠ 0 →
    ∃ D : List DyBlock, (∀ b ∈ D, b.Valid) ∧ ∃ h : dyDim D = n,
      ZpEquiv F ((dyMat D).submatrix (Fin.cast h.symm) (Fin.cast h.symm)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F hF hdet
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨[], by simp, rfl, ?_⟩
    convert ZpEquiv.refl F using 1
    exact Subsingleton.elim _ _
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨⟨i, j⟩, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun p : Fin n × Fin n => ‖F p.1 p.2‖)
    Finset.univ_nonempty
  have hle : ∀ a b, ‖F a b‖ ≤ ‖F i j‖ := fun a b => hmax (a, b) (Finset.mem_univ _)
  have hM : 0 < ‖F i j‖ := by
    rcases (norm_nonneg (F i j)).lt_or_eq with h | h
    · exact h
    · exfalso; apply hdet
      have : F = 0 := by
        ext a b
        have := hle a b
        rw [← h] at this
        exact norm_le_zero_iff.1 this
      rw [this]; exact Matrix.det_zero
  by_cases hd : ∃ a, ‖F a a‖ = ‖F i j‖
  · obtain ⟨a, ha⟩ := hd
    obtain ⟨m, rfl⟩ : ∃ m, n = 1 + m := ⟨n - 1, by omega⟩
    obtain ⟨σ, hσ⟩ := dyadic_front1 a
    have hF' : (F.submatrix σ σ)ᵀ = F.submatrix σ σ := by rw [Matrix.transpose_submatrix, hF]
    have hEq : ZpEquiv F (F.submatrix σ σ) := dyadic_zpEquiv_perm F σ
    have hdet' : (F.submatrix σ σ).det ≠ 0 := dyadic_zpEquiv_det_ne hEq hdet
    have hb : (F.submatrix σ σ) (Fin.castAdd m 0) (Fin.castAdd m 0) ≠ 0 := by
      simp only [Matrix.submatrix_apply, hσ]
      intro h0; rw [h0, norm_zero] at ha; linarith
    obtain ⟨Λ, hΛ⟩ := step1core (F.submatrix σ σ) hF' hb (fun k => by
      simp only [Matrix.submatrix_apply, hσ]; rw [ha]; exact hle _ _)
    have hBeq : (F.submatrix σ σ).submatrix (Fin.castAdd m) (Fin.castAdd m) =
        !![(F.submatrix σ σ) (Fin.castAdd m 0) (Fin.castAdd m 0)] := by
      ext r s; fin_cases r; fin_cases s; rfl
    obtain ⟨e, u, hu, hBl⟩ := block1 hb
    have hBt : ((F.submatrix σ σ).submatrix (Fin.castAdd m) (Fin.castAdd m))ᵀ =
        (F.submatrix σ σ).submatrix (Fin.castAdd m) (Fin.castAdd m) := by
      rw [Matrix.transpose_submatrix, hF']
    have hEt : ((F.submatrix σ σ).submatrix (Fin.natAdd 1) (Fin.natAdd 1))ᵀ =
        (F.submatrix σ σ).submatrix (Fin.natAdd 1) (Fin.natAdd 1) := by
      rw [Matrix.transpose_submatrix, hF']
    have hsym := split_symm (L := Λ.map PadicInt.Coe.ringHom) hBt hEt
    have hdetE := dyadic_zpEquiv_det_ne hΛ hdet'
    rw [dyadic_det_orthSumMat] at hdetE
    have IH := ih m (by omega) _ hsym (mul_ne_zero_iff.1 hdetE).2
    refine assemble (.sq e u) hu F _ ?_ IH
    refine hEq.trans (hΛ.trans (dyadic_zpEquiv_orthSum ?_ (ZpEquiv.refl _)))
    rw [hBeq]; exact hBl
  · push Not at hd
    have hij : i ≠ j := fun h => by subst h; exact hd i rfl
    have h2n : 2 ≤ n := by
      by_contra hlt
      push Not at hlt
      apply hij
      have := i.isLt; have := j.isLt
      exact Fin.ext (by omega)
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by omega⟩
    obtain ⟨σ, h0, h1⟩ := dyadic_front2 hij
    have hF' : (F.submatrix σ σ)ᵀ = F.submatrix σ σ := by rw [Matrix.transpose_submatrix, hF]
    have hEq : ZpEquiv F (F.submatrix σ σ) := dyadic_zpEquiv_perm F σ
    have hdet' : (F.submatrix σ σ).det ≠ 0 := dyadic_zpEquiv_det_ne hEq hdet
    have hβ : (F.submatrix σ σ) (Fin.castAdd m 0) (Fin.castAdd m 1) ≠ 0 := by
      simp only [Matrix.submatrix_apply, h0, h1]
      exact norm_pos_iff.1 hM
    have ha : ‖(F.submatrix σ σ) (Fin.castAdd m 0) (Fin.castAdd m 0)‖ <
        ‖(F.submatrix σ σ) (Fin.castAdd m 0) (Fin.castAdd m 1)‖ := by
      simp only [Matrix.submatrix_apply, h0, h1]
      exact lt_of_le_of_ne (hle _ _) (hd i)
    have hc : ‖(F.submatrix σ σ) (Fin.castAdd m 1) (Fin.castAdd m 1)‖ <
        ‖(F.submatrix σ σ) (Fin.castAdd m 0) (Fin.castAdd m 1)‖ := by
      simp only [Matrix.submatrix_apply, h0, h1]
      exact lt_of_le_of_ne (hle _ _) (hd j)
    obtain ⟨Λ, hΛ⟩ := step2core (F.submatrix σ σ) hF' hβ ha hc (fun i' k => by
      simp only [Matrix.submatrix_apply, h0, h1]; exact hle _ _)
    have hBt : ((F.submatrix σ σ).submatrix (Fin.castAdd m) (Fin.castAdd m))ᵀ =
        (F.submatrix σ σ).submatrix (Fin.castAdd m) (Fin.castAdd m) := by
      rw [Matrix.transpose_submatrix, hF']
    have hBeq : (F.submatrix σ σ).submatrix (Fin.castAdd m) (Fin.castAdd m) =
        !![(F.submatrix σ σ) (Fin.castAdd m 0) (Fin.castAdd m 0), (F.submatrix σ σ) (Fin.castAdd m 0) (Fin.castAdd m 1);
          (F.submatrix σ σ) (Fin.castAdd m 0) (Fin.castAdd m 1), (F.submatrix σ σ) (Fin.castAdd m 1) (Fin.castAdd m 1)] := by
      have h10 : (F.submatrix σ σ) (Fin.castAdd m 1) (Fin.castAdd m 0) =
          (F.submatrix σ σ) (Fin.castAdd m 0) (Fin.castAdd m 1) := by
        have := congrFun (congrFun hF' (Fin.castAdd m 0)) (Fin.castAdd m 1)
        simpa using this
      ext r s; fin_cases r <;> fin_cases s <;> first | rfl | exact h10
    have hEt : ((F.submatrix σ σ).submatrix (Fin.natAdd 2) (Fin.natAdd 2))ᵀ =
        (F.submatrix σ σ).submatrix (Fin.natAdd 2) (Fin.natAdd 2) := by
      rw [Matrix.transpose_submatrix, hF']
    have hsym := split_symm (L := Λ.map PadicInt.Coe.ringHom) hBt hEt
    have hdetE := dyadic_zpEquiv_det_ne hΛ hdet'
    rw [dyadic_det_orthSumMat] at hdetE
    have IH := ih m (by omega) _ hsym (mul_ne_zero_iff.1 hdetE).2
    obtain ⟨e, hBl⟩ := block2 hβ ha hc
    rcases hBl with hBl | hBl
    · refine assemble (.hyp e) trivial F _ ?_ IH
      refine hEq.trans (hΛ.trans (dyadic_zpEquiv_orthSum ?_ (ZpEquiv.refl _)))
      rw [hBeq]; exact hBl
    · refine assemble (.ell e) trivial F _ ?_ IH
      refine hEq.trans (hΛ.trans (dyadic_zpEquiv_orthSum ?_ (ZpEquiv.refl _)))
      rw [hBeq]; exact hBl


/-! ### Helpers for the Corollary -/

/-- An *even unimodular* integral symmetric matrix over `ℚ₂`: integral entries, diagonal in `2ℤ₂`, unit
determinant. -/
def dyadicEU (F : Matrix (Fin n) (Fin n) ℚ_[2]) : Prop :=
  Fᵀ = F ∧ (∀ i j, ‖F i j‖ ≤ 1) ∧ (∀ i, ‖F i i‖ < 1) ∧ ‖F.det‖ = 1

theorem dyadic_lift_mat {F : Matrix (Fin n) (Fin n) ℚ_[2]} (h : ∀ i j, ‖F i j‖ ≤ 1) :
    ∃ Fz : Matrix (Fin n) (Fin n) ℤ_[2], Fz.map PadicInt.Coe.ringHom = F :=
  ⟨Matrix.of fun i j => ⟨F i j, h i j⟩, rfl⟩

theorem dyadic_det_map_coe (Fz : Matrix (Fin n) (Fin n) ℤ_[2]) :
    (Fz.map PadicInt.Coe.ringHom).det = ((Fz.det : ℤ_[2]) : ℚ_[2]) :=
  (RingHom.map_det PadicInt.Coe.ringHom Fz).symm

theorem dyadic_norm_det_le_one {F : Matrix (Fin n) (Fin n) ℚ_[2]} (h : ∀ i j, ‖F i j‖ ≤ 1) :
    ‖F.det‖ ≤ 1 := by
  obtain ⟨Fz, rfl⟩ := dyadic_lift_mat h
  rw [dyadic_det_map_coe]; exact PadicInt.norm_le_one _

theorem dyadic_two_dvd_det (hn : 0 < n) (Fz : Matrix (Fin n) (Fin n) ℤ_[2]) (h : ∀ i j, (2 : ℤ_[2]) ∣ Fz i j) :
    (2 : ℤ_[2]) ∣ Fz.det := by
  rw [Matrix.det_apply']
  refine Finset.dvd_sum fun σ _ => ?_
  exact Dvd.dvd.mul_left ((h _ _).trans (Finset.dvd_prod_of_mem (fun i => Fz (σ i) i) (Finset.mem_univ ⟨0, hn⟩))) _

theorem dyadic_two_dvd_of_norm_lt {x : ℤ_[2]} (h : ‖(x : ℚ_[2])‖ < 1) : (2 : ℤ_[2]) ∣ x := by
  have := (PadicInt.norm_lt_one_iff_dvd (p := 2) x).1 (by simpa using h)
  simpa using this

theorem dyadic_exists_unit_entry (hn : 0 < n) {F : Matrix (Fin n) (Fin n) ℚ_[2]} (hint : ∀ i j, ‖F i j‖ ≤ 1)
    (hdet : ‖F.det‖ = 1) : ∃ i j, ‖F i j‖ = 1 := by
  by_contra hno
  push Not at hno
  obtain ⟨Fz, rfl⟩ := dyadic_lift_mat hint
  have h2 : ∀ i j, (2 : ℤ_[2]) ∣ Fz i j := fun i j =>
    dyadic_two_dvd_of_norm_lt (lt_of_le_of_ne (hint i j) (hno i j))
  have h3 := dyadic_two_dvd_det hn Fz h2
  rw [dyadic_det_map_coe] at hdet
  have hu : IsUnit Fz.det := PadicInt.isUnit_iff.2 (by simpa using hdet)
  exact dyadic_not_isUnit_of_two_dvd h3 hu


theorem dyadic_norm_det_zpEquiv {F G : Matrix (Fin n) (Fin n) ℚ_[2]} (h : ZpEquiv F G) : ‖G.det‖ = ‖F.det‖ := by
  obtain ⟨s, hs, hG⟩ := dyadic_zpEquiv_det_rel h
  rw [hG, norm_mul, norm_pow, hs]; simp

theorem dyadic_block2_unit {a β c : ℚ_[2]} (ha : ‖a‖ < 1) (hc : ‖c‖ < 1) (hβ : ‖β‖ = 1) :
    ZpEquiv !![a, β; β, c] !![0, 1; 1, 0] ∨ ZpEquiv !![a, β; β, c] !![2, 1; 1, 2] := by
  obtain ⟨A, rfl⟩ : ∃ A : ℤ_[2], (A : ℚ_[2]) = a := ⟨⟨a, ha.le⟩, rfl⟩
  obtain ⟨C, rfl⟩ : ∃ C : ℤ_[2], (C : ℚ_[2]) = c := ⟨⟨c, hc.le⟩, rfl⟩
  obtain ⟨Bt, rfl⟩ : ∃ Bt : ℤ_[2], (Bt : ℚ_[2]) = β := ⟨⟨β, hβ.le⟩, rfl⟩
  exact dyadic_bin_unit (dyadic_two_dvd_of_norm_lt ha) (dyadic_two_dvd_of_norm_lt hc) (PadicInt.isUnit_iff.2 (by simpa using hβ))

theorem dyadic_EU_perm {F : Matrix (Fin n) (Fin n) ℚ_[2]} (hF : dyadicEU F) (σ : Equiv.Perm (Fin n)) :
    dyadicEU (F.submatrix σ σ) := by
  obtain ⟨hs, hi, hd, hdet⟩ := hF
  refine ⟨by rw [Matrix.transpose_submatrix, hs], fun i j => hi _ _, fun i => hd _, ?_⟩
  rw [dyadic_norm_det_zpEquiv (dyadic_zpEquiv_perm F σ), hdet]

/-- Complement of a split-off binary block in an even unimodular matrix is again even unimodular. -/
theorem dyadic_EU_comp {m : ℕ} (B : Matrix (Fin 2) (Fin 2) ℚ_[2]) (E : Matrix (Fin m) (Fin m) ℚ_[2])
    (Λ : Matrix (Fin 2) (Fin m) ℤ_[2]) (hB : Bᵀ = B) (hE : Eᵀ = E) (hBi : ∀ i j, ‖B i j‖ ≤ 1)
    (hEi : ∀ i j, ‖E i j‖ ≤ 1) (hBd : ∀ i, ‖B i i‖ < 1) (hEd : ∀ i, ‖E i i‖ < 1)
    (hdet : ‖(orthSumMat B (E - (Λ.map PadicInt.Coe.ringHom)ᵀ * B * Λ.map PadicInt.Coe.ringHom)).det‖ = 1) :
    dyadicEU (E - (Λ.map PadicInt.Coe.ringHom)ᵀ * B * Λ.map PadicInt.Coe.ringHom) := by
  obtain ⟨Ez, hEz⟩ := dyadic_lift_mat hEi
  obtain ⟨Bz, hBz⟩ := dyadic_lift_mat hBi
  have hE'eq : E - (Λ.map PadicInt.Coe.ringHom)ᵀ * B * Λ.map PadicInt.Coe.ringHom =
      (Ez - Λᵀ * Bz * Λ).map PadicInt.Coe.ringHom := by
    rw [← hEz, ← hBz]
    show _ = (RingHom.mapMatrix PadicInt.Coe.ringHom) (Ez - Λᵀ * Bz * Λ)
    rw [map_sub]
    simp only [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map]
  have hsymz : ∀ r s, Bz r s = Bz s r := fun r s => by
    have := congrFun (congrFun hB r) s
    rw [← hBz] at this
    exact (PadicInt.ext (by simpa using this)).symm
  refine ⟨split_symm hB hE, ?_, ?_, ?_⟩
  · intro r s; rw [hE'eq]; exact PadicInt.norm_le_one _
  · intro k
    rw [hE'eq]
    have hE2 : (2 : ℤ_[2]) ∣ Ez k k := dyadic_two_dvd_of_norm_lt (by rw [← hEz] at hEd; simpa using hEd k)
    have hB0 : (2 : ℤ_[2]) ∣ Bz 0 0 := dyadic_two_dvd_of_norm_lt (by rw [← hBz] at hBd; simpa using hBd 0)
    have hB1 : (2 : ℤ_[2]) ∣ Bz 1 1 := dyadic_two_dvd_of_norm_lt (by rw [← hBz] at hBd; simpa using hBd 1)
    obtain ⟨a', ha'⟩ := hB0
    obtain ⟨c', hc'⟩ := hB1
    have : (2 : ℤ_[2]) ∣ (Ez - Λᵀ * Bz * Λ) k k := by
      simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
      rw [hsymz 1 0]
      refine dvd_sub hE2 ⟨Λ 0 k * Λ 0 k * a' + Λ 0 k * Bz 0 1 * Λ 1 k + Λ 1 k * Λ 1 k * c', ?_⟩
      rw [ha', hc']; ring
    show ‖(((Ez - Λᵀ * Bz * Λ) k k : ℤ_[2]) : ℚ_[2])‖ < 1
    rw [← PadicInt.norm_def]
    exact (PadicInt.norm_lt_one_iff_dvd (p := 2) _).2 (by simpa using this)
  · have h1 := hdet
    rw [dyadic_det_orthSumMat, norm_mul] at h1
    have h2 := dyadic_norm_det_le_one hBi
    have h3 := dyadic_norm_det_le_one (F := E - (Λ.map PadicInt.Coe.ringHom)ᵀ * B * Λ.map PadicInt.Coe.ringHom)
      (fun r s => by rw [hE'eq]; exact PadicInt.norm_le_one _)
    have := norm_nonneg (E - (Λ.map PadicInt.Coe.ringHom)ᵀ * B * Λ.map PadicInt.Coe.ringHom).det
    have := norm_nonneg B.det
    nlinarith


theorem dyadic_EU_split_front {m : ℕ} {F : Matrix (Fin (2 + m)) (Fin (2 + m)) ℚ_[2]} (hF : dyadicEU F)
    (h : ‖F (Fin.castAdd m 0) (Fin.castAdd m 1)‖ = 1) :
    ∃ (X : Matrix (Fin 2) (Fin 2) ℚ_[2]) (E' : Matrix (Fin m) (Fin m) ℚ_[2]),
      (X = !![0, 1; 1, 0] ∨ X = !![2, 1; 1, 2]) ∧ dyadicEU E' ∧ ZpEquiv F (orthSumMat X E') := by
  obtain ⟨hsym, hint, hdiag, hdet⟩ := hF
  have hβ : F (Fin.castAdd m 0) (Fin.castAdd m 1) ≠ 0 := fun h0 => by
    rw [h0, norm_zero] at h; exact zero_ne_one h
  have ha : ‖F (Fin.castAdd m 0) (Fin.castAdd m 0)‖ < ‖F (Fin.castAdd m 0) (Fin.castAdd m 1)‖ := by
    rw [h]; exact hdiag _
  have hc : ‖F (Fin.castAdd m 1) (Fin.castAdd m 1)‖ < ‖F (Fin.castAdd m 0) (Fin.castAdd m 1)‖ := by
    rw [h]; exact hdiag _
  obtain ⟨Λ, hΛ⟩ := step2core F hsym hβ ha hc (fun i' k => by rw [h]; exact hint _ _)
  have hBt : (F.submatrix (Fin.castAdd m) (Fin.castAdd m))ᵀ = F.submatrix (Fin.castAdd m) (Fin.castAdd m) := by
    rw [Matrix.transpose_submatrix, hsym]
  have hEt : (F.submatrix (Fin.natAdd 2) (Fin.natAdd 2))ᵀ = F.submatrix (Fin.natAdd 2) (Fin.natAdd 2) := by
    rw [Matrix.transpose_submatrix, hsym]
  have h10 : F (Fin.castAdd m 1) (Fin.castAdd m 0) = F (Fin.castAdd m 0) (Fin.castAdd m 1) := by
    have := congrFun (congrFun hsym (Fin.castAdd m 0)) (Fin.castAdd m 1)
    simpa using this
  have hBeq : F.submatrix (Fin.castAdd m) (Fin.castAdd m) =
      !![F (Fin.castAdd m 0) (Fin.castAdd m 0), F (Fin.castAdd m 0) (Fin.castAdd m 1);
        F (Fin.castAdd m 0) (Fin.castAdd m 1), F (Fin.castAdd m 1) (Fin.castAdd m 1)] := by
    ext r s; fin_cases r <;> fin_cases s <;> first | rfl | exact h10
  have hU : ‖(orthSumMat (F.submatrix (Fin.castAdd m) (Fin.castAdd m))
      (F.submatrix (Fin.natAdd 2) (Fin.natAdd 2) - (Λ.map PadicInt.Coe.ringHom)ᵀ *
        F.submatrix (Fin.castAdd m) (Fin.castAdd m) * Λ.map PadicInt.Coe.ringHom)).det‖ = 1 := by
    rw [dyadic_norm_det_zpEquiv hΛ, hdet]
  have hEU := dyadic_EU_comp (F.submatrix (Fin.castAdd m) (Fin.castAdd m)) (F.submatrix (Fin.natAdd 2) (Fin.natAdd 2)) Λ
    hBt hEt (fun r s => hint _ _) (fun r s => hint _ _) (fun r => hdiag _) (fun r => hdiag _) hU
  have hBX : ZpEquiv (F.submatrix (Fin.castAdd m) (Fin.castAdd m)) !![0, 1; 1, 0] ∨
      ZpEquiv (F.submatrix (Fin.castAdd m) (Fin.castAdd m)) !![2, 1; 1, 2] := by
    rw [hBeq]; exact dyadic_block2_unit (hdiag _) (hdiag _) h
  rcases hBX with h' | h'
  · exact ⟨_, _, Or.inl rfl, hEU, hΛ.trans (dyadic_zpEquiv_orthSum h' (ZpEquiv.refl _))⟩
  · exact ⟨_, _, Or.inr rfl, hEU, hΛ.trans (dyadic_zpEquiv_orthSum h' (ZpEquiv.refl _))⟩

theorem dyadic_EU_split {m : ℕ} {F : Matrix (Fin (2 + m)) (Fin (2 + m)) ℚ_[2]} (hF : dyadicEU F) :
    ∃ (X : Matrix (Fin 2) (Fin 2) ℚ_[2]) (E' : Matrix (Fin m) (Fin m) ℚ_[2]),
      (X = !![0, 1; 1, 0] ∨ X = !![2, 1; 1, 2]) ∧ dyadicEU E' ∧ ZpEquiv F (orthSumMat X E') := by
  obtain ⟨hsym, hint, hdiag, hdet⟩ := hF
  obtain ⟨i, j, hij⟩ := dyadic_exists_unit_entry (by omega) hint hdet
  have hne : i ≠ j := fun h => by subst h; have := hdiag i; linarith
  obtain ⟨σ, h0, h1⟩ := dyadic_front2 hne
  obtain ⟨X, E', hX, hE', hz⟩ := dyadic_EU_split_front (dyadic_EU_perm ⟨hsym, hint, hdiag, hdet⟩ σ)
    (by simp only [Matrix.submatrix_apply, h0, h1]; exact hij)
  exact ⟨X, E', hX, hE', (dyadic_zpEquiv_perm F σ).trans hz⟩


theorem dyadic_orthSumMat_cc {a b : ℕ} (F : Matrix (Fin a) (Fin a) ℚ_[2]) (G : Matrix (Fin b) (Fin b) ℚ_[2])
    (i j : Fin a) : orthSumMat F G (Fin.castAdd b i) (Fin.castAdd b j) = F i j := by
  simp [dyadic_orthSumMat_eq]

theorem dyadic_orthSumMat_cn {a b : ℕ} (F : Matrix (Fin a) (Fin a) ℚ_[2]) (G : Matrix (Fin b) (Fin b) ℚ_[2])
    (i : Fin a) (j : Fin b) : orthSumMat F G (Fin.castAdd b i) (Fin.natAdd a j) = 0 := by
  simp [dyadic_orthSumMat_eq]

theorem dyadic_orthSumMat_nc {a b : ℕ} (F : Matrix (Fin a) (Fin a) ℚ_[2]) (G : Matrix (Fin b) (Fin b) ℚ_[2])
    (i : Fin b) (j : Fin a) : orthSumMat F G (Fin.natAdd a i) (Fin.castAdd b j) = 0 := by
  simp [dyadic_orthSumMat_eq]

theorem dyadic_orthSumMat_nn {a b : ℕ} (F : Matrix (Fin a) (Fin a) ℚ_[2]) (G : Matrix (Fin b) (Fin b) ℚ_[2])
    (i j : Fin b) : orthSumMat F G (Fin.natAdd a i) (Fin.natAdd a j) = G i j := by
  simp [dyadic_orthSumMat_eq]

theorem dyadic_orthSumMat_assoc {a b c : ℕ} (P : Matrix (Fin a) (Fin a) ℚ_[2]) (Q : Matrix (Fin b) (Fin b) ℚ_[2])
    (R : Matrix (Fin c) (Fin c) ℚ_[2]) (h : a + (b + c) = a + b + c) :
    orthSumMat P (orthSumMat Q R) =
      (orthSumMat (orthSumMat P Q) R).submatrix (Fin.cast h) (Fin.cast h) := by
  have c1 : ∀ i : Fin a, Fin.cast h (Fin.castAdd (b + c) i) = Fin.castAdd c (Fin.castAdd b i) :=
    fun i => Fin.ext (by simp)
  have c2 : ∀ i : Fin b, Fin.cast h (Fin.natAdd a (Fin.castAdd c i)) = Fin.castAdd c (Fin.natAdd a i) :=
    fun i => Fin.ext (by simp)
  have c3 : ∀ i : Fin c, Fin.cast h (Fin.natAdd a (Fin.natAdd b i)) = Fin.natAdd (a + b) i :=
    fun i => Fin.ext (by simp; omega)
  ext i j
  induction i using Fin.addCases with
  | left i1 =>
    induction j using Fin.addCases with
    | left j1 => simp [c1, dyadic_orthSumMat_cc]
    | right j2 =>
      induction j2 using Fin.addCases with
      | left j21 => simp [c1, c2, dyadic_orthSumMat_cc, dyadic_orthSumMat_cn]
      | right j22 => simp [c1, c3, dyadic_orthSumMat_cn]
  | right i2 =>
    induction i2 using Fin.addCases with
    | left i21 =>
      induction j using Fin.addCases with
      | left j1 => simp [c1, c2, dyadic_orthSumMat_cc, dyadic_orthSumMat_nc]
      | right j2 =>
        induction j2 using Fin.addCases with
        | left j21 => simp [c2, dyadic_orthSumMat_cc, dyadic_orthSumMat_nn, dyadic_orthSumMat_cn]
        | right j22 => simp [c2, c3, dyadic_orthSumMat_cn, dyadic_orthSumMat_nc, dyadic_orthSumMat_nn]
    | right i22 =>
      induction j using Fin.addCases with
      | left j1 => simp [c1, c3, dyadic_orthSumMat_nc]
      | right j2 =>
        induction j2 using Fin.addCases with
        | left j21 => simp [c2, c3, dyadic_orthSumMat_nc, dyadic_orthSumMat_nn, dyadic_orthSumMat_cc]
        | right j22 => simp [c3, dyadic_orthSumMat_nn]

theorem dyadic_zpEquiv_cast {n n' : ℕ} {F G : Matrix (Fin n) (Fin n) ℚ_[2]} (h : n' = n) (hFG : ZpEquiv F G) :
    ZpEquiv (F.submatrix (Fin.cast h) (Fin.cast h)) (G.submatrix (Fin.cast h) (Fin.cast h)) := by
  subst h; exact hFG

theorem dyadic_assoc_equiv {m : ℕ} {P Q P' Q' : Matrix (Fin 2) (Fin 2) ℚ_[2]} (R : Matrix (Fin m) (Fin m) ℚ_[2])
    (h : ZpEquiv (orthSumMat P Q) (orthSumMat P' Q')) :
    ZpEquiv (orthSumMat P (orthSumMat Q R)) (orthSumMat P' (orthSumMat Q' R)) := by
  have hh : 2 + (2 + m) = 2 + 2 + m := by omega
  rw [dyadic_orthSumMat_assoc P Q R hh, dyadic_orthSumMat_assoc P' Q' R hh]
  exact dyadic_zpEquiv_cast hh (dyadic_zpEquiv_orthSum h (ZpEquiv.refl R))

theorem dyadic_orthSumMat_flip {a : ℕ} (P Q : Matrix (Fin a) (Fin a) ℚ_[2]) :
    (orthSumMat P Q).submatrix (finAddFlip : Fin (a + a) ≃ Fin (a + a)) (finAddFlip : Fin (a + a) ≃ Fin (a + a)) =
      orthSumMat Q P := by
  ext i j
  induction i using Fin.addCases with
  | left i1 =>
    induction j using Fin.addCases with
    | left j1 =>
      simp only [Matrix.submatrix_apply, finAddFlip_apply_castAdd, dyadic_orthSumMat_cc, dyadic_orthSumMat_nn]
    | right j2 =>
      simp only [Matrix.submatrix_apply, finAddFlip_apply_castAdd, finAddFlip_apply_natAdd, dyadic_orthSumMat_cn,
        dyadic_orthSumMat_nc]
  | right i2 =>
    induction j using Fin.addCases with
    | left j1 =>
      simp only [Matrix.submatrix_apply, finAddFlip_apply_castAdd, finAddFlip_apply_natAdd, dyadic_orthSumMat_cn,
        dyadic_orthSumMat_nc]
    | right j2 =>
      simp only [Matrix.submatrix_apply, finAddFlip_apply_natAdd, dyadic_orthSumMat_cc, dyadic_orthSumMat_nn]

theorem dyadic_zpEquiv_flip {a : ℕ} (P Q : Matrix (Fin a) (Fin a) ℚ_[2]) :
    ZpEquiv (orthSumMat P Q) (orthSumMat Q P) := by
  have := dyadic_zpEquiv_perm (orthSumMat P Q) (finAddFlip : Fin (a + a) ≃ Fin (a + a))
  rwa [dyadic_orthSumMat_flip] at this


theorem dyadic_norm_two_q : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by simpa using (Padic.norm_p (p := 2))

theorem dyadic_EU_H : dyadicEU (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2]) := by
  refine ⟨by ext i j; fin_cases i <;> fin_cases j <;> rfl, ?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp
  · intro i; fin_cases i <;> simp
  · simp [Matrix.det_fin_two_of]

theorem dyadic_EU_A : dyadicEU (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ_[2]) := by
  have h3 : ‖(3 : ℚ_[2])‖ = 1 := by
    have := PadicInt.isUnit_iff.1 dyadic_isUnit_three
    rw [PadicInt.norm_def] at this
    exact this
  have h2 := dyadic_norm_two_q
  refine ⟨by ext i j; fin_cases i <;> fin_cases j <;> rfl, ?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp [h2] <;> norm_num
  · intro i; fin_cases i <;> simp [h2] <;> norm_num
  · rw [Matrix.det_fin_two_of]; norm_num; exact h3

theorem dyadic_EU_orthSum {a b : ℕ} {X : Matrix (Fin a) (Fin a) ℚ_[2]} {E : Matrix (Fin b) (Fin b) ℚ_[2]}
    (hX : dyadicEU X) (hE : dyadicEU E) : dyadicEU (orthSumMat X E) := by
  obtain ⟨hXs, hXi, hXd, hXdet⟩ := hX
  obtain ⟨hEs, hEi, hEd, hEdet⟩ := hE
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [dyadic_orthSumMat_eq, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]
    simp [hXs, hEs]
  · intro i j
    rw [dyadic_orthSumMat_eq, Matrix.submatrix_apply]
    rcases finSumFinEquiv.symm i with x | x <;> rcases finSumFinEquiv.symm j with y | y <;>
      simp [hXi, hEi]
  · intro i
    rw [dyadic_orthSumMat_eq, Matrix.submatrix_apply]
    rcases finSumFinEquiv.symm i with x | x <;> simp [hXd, hEd]
  · rw [dyadic_det_orthSumMat, norm_mul, hXdet, hEdet]; norm_num

/-- `-3` is not the square of a `2`-adic unit. -/
theorem dyadic_neg_three_not_sq {s : ℚ_[2]} (hs : ‖s‖ = 1) : s ^ 2 ≠ -3 := by
  obtain ⟨w, u₀, rfl, hw, h0, hd⟩ := dyadic_exists_lift hs
  intro h
  have h' : w ^ 2 = -3 := by
    have : ((w ^ 2 : ℤ_[2]) : ℚ_[2]) = ((-3 : ℤ_[2]) : ℚ_[2]) := by
      rw [PadicInt.coe_neg, PadicInt.coe_pow]; exact h
    exact PadicInt.ext this
  obtain ⟨t, ht⟩ := hd
  have hu : (u₀ : ℤ_[2]) ^ 2 = 1 + 8 * (((u₀ ^ 2 - 1) / 8 : ℤ) : ℤ_[2]) := by
    rcases h0 with rfl | rfl | rfl | rfl <;> norm_num
  have hw8 : w = u₀ + 8 * t := by
    have : w = u₀ + (2 : ℤ_[2]) ^ 3 * t := by rw [← ht]; ring
    rw [this]; norm_num
  have hsq : w ^ 2 = 1 + 8 * (((u₀ ^ 2 - 1) / 8 : ℤ) + 2 * u₀ * t + 8 * t ^ 2 : ℤ_[2]) := by
    rw [hw8, add_sq]; rw [hu]; ring
  rw [h'] at hsq
  have h4 : (4 : ℤ_[2]) * (1 + 2 * (((u₀ ^ 2 - 1) / 8 : ℤ) + 2 * u₀ * t + 8 * t ^ 2 : ℤ_[2])) = 0 := by
    linear_combination (-1 : ℤ_[2]) * hsq
  have h1 : (1 : ℤ_[2]) + 2 * (((u₀ ^ 2 - 1) / 8 : ℤ) + 2 * u₀ * t + 8 * t ^ 2 : ℤ_[2]) = 0 := by
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have h2 : (2 : ℤ_[2]) ∣ 1 :=
    ⟨-(((u₀ ^ 2 - 1) / 8 : ℤ) + 2 * u₀ * t + 8 * t ^ 2 : ℤ_[2]), by linear_combination h1⟩
  exact dyadic_not_isUnit_of_two_dvd h2 isUnit_one


/-- **Cassels, Ch. 8, Lemma 4.1** ($p = 2$): *every regular quadratic form taking values in $\mathbb Q_2$ is
$\mathbb Z_2$-equivalent to a sum of forms of the following types in distinct variables: $2^{e}x^{2}$,
$2^{e}3x^{2}$, $2^{e}5x^{2}$, $2^{e}7x^{2}$ (4.1), $2^{e}\cdot 2xy$ (4.2), $2^{e}(2x^{2} + 2xy + 2y^{2})$ (4.3)
($e \in \mathbb Z$).* The list (4.1)–(4.3) is partly lost in the scan and is reconstructed from the proof
("$u$ is of one of the shapes $v^{2}, 3v^{2}, 5v^{2}, 7v^{2}$"; case (ii) ends with $2y_1y_2$ or
$2y_1^{2} + 2y_1y_2 + 2y_2^{2}$). Formally: $F$ is $\mathbb Z_2$-equivalent to `dyMat D` for a list `D` of valid blocks
with $n$ variables in all. -/
@[kb "cassels1978" "Ch. 8, Lemma 4.1, pp. 117–119"]
theorem exists_dyadic_decomp (F : Matrix (Fin n) (Fin n) ℚ_[2]) (hF : Fᵀ = F) (hdet : F.det ≠ 0) :
    ∃ D : List DyBlock, (∀ b ∈ D, b.Valid) ∧ ∃ h : dyDim D = n,
      ZpEquiv F ((dyMat D).submatrix (Fin.cast h.symm) (Fin.cast h.symm)) :=
  dyadic_aux n F hF hdet

/-- **Cassels, Ch. 8, (4.7)**, variant (p. 118): *$ux_1^{2} + 2x_2x_3 \sim u(x_1^{2} + x_2^{2} - x_3^{2})$* for a
$2$-adic unit $u$ ($\sim$ is $\mathbb Z_2$-equivalence). The printed (4.7) has $ux_1^{2} + x_2^{2} - x_3^{2}$ on the right
(`equiv_4_7_printed`); the two right-hand sides are equivalent (`zpEquiv_unit_hyp`). This is why Witt's lemma fails over $\mathbb Z_2$ without the
hypotheses of Lemma 4.2: $2x_2x_3 \not\sim x_2^{2} - x_3^{2}$. -/
@[kb "cassels1978" "Ch. 8, §4, (4.7), p. 118 (variant: u(x₁² + x₂² − x₃²) on the right)"]
theorem equiv_4_7 {u : ℚ_[2]} (hu : ‖u‖ = 1) :
    ZpEquiv !![u, 0, 0; 0, 0, 1; 0, 1, 0] !![u, 0, 0; 0, u, 0; 0, 0, -u] := ex47_gen hu

/-- **Cassels, Ch. 8, (4.8)** (p. 118, checked against the page image): *$ux_1^{2} + (2x_2^{2} + 2x_2x_3 + 2x_3^{2}) \sim
u(3x_1^{2} - x_2^{2} - x_3^{2})$* for a $2$-adic unit $u$. -/
@[kb "cassels1978" "Ch. 8, §4, (4.8), p. 118"]
theorem equiv_4_8 {u : ℚ_[2]} (hu : ‖u‖ = 1) :
    ZpEquiv !![u, 0, 0; 0, 2, 1; 0, 1, 2] !![3 * u, 0, 0; 0, -u, 0; 0, 0, -u] := ex48_gen hu

/-- **Cassels, Ch. 8, (4.9)** (p. 118, checked against the page image): *$(2x_1^{2} + 2x_1x_2 + 2x_2^{2}) + (2x_3^{2} + 2x_3x_4 +
2x_4^{2}) \sim 2x_1x_2 + 2x_3x_4$.* -/
@[kb "cassels1978" "Ch. 8, §4, (4.9), p. 118"]
theorem equiv_4_9 :
    ZpEquiv (p := 2) !![2, 1, 0, 0; 1, 2, 0, 0; 0, 0, 2, 1; 0, 0, 1, 2]
      !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] := ex49_aux


/-! ### The Corollary: induction -/

/-- `G`'s determinant is a unit square times that of `F`. -/
def dyadicRel (F G : Matrix (Fin n) (Fin n) ℚ_[2]) : Prop := ∃ s : ℚ_[2], ‖s‖ = 1 ∧ G.det = s ^ 2 * F.det

theorem dyadicRel.symm' {F G : Matrix (Fin n) (Fin n) ℚ_[2]} (h : dyadicRel F G) : dyadicRel G F := by
  obtain ⟨s, hs, hG⟩ := h
  have hs0 : s ≠ 0 := fun h0 => by rw [h0, norm_zero] at hs; exact zero_ne_one hs
  refine ⟨s⁻¹, by rw [norm_inv, hs]; simp, ?_⟩
  rw [hG, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hs0]; simp

theorem dyadicRel.trans' {F G H : Matrix (Fin n) (Fin n) ℚ_[2]} (h1 : dyadicRel F G) (h2 : dyadicRel G H) : dyadicRel F H := by
  obtain ⟨s, hs, hG⟩ := h1
  obtain ⟨t, ht, hH⟩ := h2
  refine ⟨t * s, by rw [norm_mul, hs, ht]; simp, ?_⟩
  rw [hH, hG]; ring

theorem dyadicRel.of_zp {F G : Matrix (Fin n) (Fin n) ℚ_[2]} (h : ZpEquiv F G) : dyadicRel F G := dyadic_zpEquiv_det_rel h

theorem dyadicRel.cong {F G F1 G1 : Matrix (Fin n) (Fin n) ℚ_[2]} (hF : ZpEquiv F F1) (hG : ZpEquiv G G1)
    (h : dyadicRel F G) : dyadicRel F1 G1 :=
  (dyadicRel.of_zp hF).symm'.trans' (h.trans' (dyadicRel.of_zp hG))

theorem dyadicRel.cancel {a b : ℕ} {X : Matrix (Fin a) (Fin a) ℚ_[2]} {E E' : Matrix (Fin b) (Fin b) ℚ_[2]}
    (hX : X.det ≠ 0) (h : dyadicRel (orthSumMat X E) (orthSumMat X E')) : dyadicRel E E' := by
  obtain ⟨s, hs, hG⟩ := h
  refine ⟨s, hs, ?_⟩
  rw [dyadic_det_orthSumMat, dyadic_det_orthSumMat] at hG
  apply mul_left_cancel₀ hX
  rw [hG]; ring

theorem dyadic_EU_fin_one {F : Matrix (Fin 1) (Fin 1) ℚ_[2]} (h : dyadicEU F) : False := by
  obtain ⟨-, -, hd, hdet⟩ := h
  rw [Matrix.det_unique] at hdet
  have := hd default
  rw [Fin.default_eq_zero] at hdet this
  linarith

private theorem finish_step {m : ℕ} {X : Matrix (Fin 2) (Fin 2) ℚ_[2]} (hX : X.det ≠ 0)
    (IH : ∀ F G : Matrix (Fin m) (Fin m) ℚ_[2], dyadicEU F → dyadicEU G → dyadicRel F G → ZpEquiv F G)
    {F G : Matrix (Fin (2 + m)) (Fin (2 + m)) ℚ_[2]} {EF EG : Matrix (Fin m) (Fin m) ℚ_[2]}
    (hEF : dyadicEU EF) (hEG : dyadicEU EG) (hF : ZpEquiv F (orthSumMat X EF)) (hG : ZpEquiv G (orthSumMat X EG))
    (hrel : dyadicRel F G) : ZpEquiv F G := by
  have h1 : dyadicRel (orthSumMat X EF) (orthSumMat X EG) := dyadicRel.cong hF hG hrel
  have h2 : ZpEquiv EF EG := IH EF EG hEF hEG (dyadicRel.cancel hX h1)
  exact hF.trans ((dyadic_zpEquiv_orthSum (ZpEquiv.refl X) h2).trans hG.symm)

private theorem hh_eq : orthSumMat (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2]) !![0, 1; 1, 0] =
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

private theorem aa_eq : orthSumMat (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ_[2]) !![2, 1; 1, 2] =
    !![2, 1, 0, 0; 1, 2, 0, 0; 0, 0, 2, 1; 0, 0, 1, 2] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

private theorem convert_H {m' : ℕ} {F : Matrix (Fin (2 + (2 + m'))) (Fin (2 + (2 + m'))) ℚ_[2]}
    {EF : Matrix (Fin (2 + m')) (Fin (2 + m')) ℚ_[2]} (hEF : dyadicEU EF)
    (h : ZpEquiv F (orthSumMat !![0, 1; 1, 0] EF)) :
    ∃ W : Matrix (Fin (2 + m')) (Fin (2 + m')) ℚ_[2], dyadicEU W ∧ ZpEquiv F (orthSumMat !![2, 1; 1, 2] W) := by
  obtain ⟨X', E', hX', hE', hE⟩ := dyadic_EU_split hEF
  have h1 : ZpEquiv F (orthSumMat !![0, 1; 1, 0] (orthSumMat X' E')) :=
    h.trans (dyadic_zpEquiv_orthSum (ZpEquiv.refl _) hE)
  rcases hX' with rfl | rfl
  · have e : ZpEquiv (orthSumMat (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2]) !![0, 1; 1, 0])
        (orthSumMat (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ_[2]) !![2, 1; 1, 2]) := by
      rw [hh_eq, aa_eq]; exact equiv_4_9.symm
    exact ⟨orthSumMat !![2, 1; 1, 2] E', dyadic_EU_orthSum dyadic_EU_A hE', h1.trans (dyadic_assoc_equiv E' e)⟩
  · have e := dyadic_zpEquiv_flip (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2]) !![2, 1; 1, 2]
    exact ⟨orthSumMat !![0, 1; 1, 0] E', dyadic_EU_orthSum dyadic_EU_H hE', h1.trans (dyadic_assoc_equiv E' e)⟩

private theorem contra_HA {F G : Matrix (Fin (2 + 0)) (Fin (2 + 0)) ℚ_[2]} {EF EG : Matrix (Fin 0) (Fin 0) ℚ_[2]}
    (hF : ZpEquiv F (orthSumMat !![0, 1; 1, 0] EF)) (hG : ZpEquiv G (orthSumMat !![2, 1; 1, 2] EG))
    (hrel : dyadicRel F G) : False := by
  obtain ⟨s, hs, h⟩ := dyadicRel.cong hF hG hrel
  rw [dyadic_det_orthSumMat, dyadic_det_orthSumMat] at h
  simp [Matrix.det_fin_two_of] at h
  apply dyadic_neg_three_not_sq hs
  linear_combination h

theorem dyadic_EU_equiv : ∀ (n : ℕ) (F G : Matrix (Fin n) (Fin n) ℚ_[2]), dyadicEU F → dyadicEU G → dyadicRel F G →
    ZpEquiv F G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F G hF hG hrel
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · convert ZpEquiv.refl F using 1; exact Subsingleton.elim _ _
    · exact (dyadic_EU_fin_one hF).elim
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by omega⟩
  have IH := ih m (by omega)
  obtain ⟨X, EF, hX, hEF, hFX⟩ := dyadic_EU_split hF
  obtain ⟨Y, EG, hY, hEG, hGY⟩ := dyadic_EU_split hG
  have hdH : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2]).det ≠ 0 := by simp [Matrix.det_fin_two_of]
  have hdA : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ_[2]).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]; norm_num
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
  · exact finish_step hdH IH hEF hEG hFX hGY hrel
  · -- F ~ H ⊕ EF, G ~ A ⊕ EG
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · exact (contra_HA hFX hGY hrel).elim
      · exact (dyadic_EU_fin_one hEF).elim
    · obtain ⟨m', rfl⟩ : ∃ m', m = 2 + m' := ⟨m - 2, by omega⟩
      obtain ⟨W, hW, hFW⟩ := convert_H hEF hFX
      exact finish_step hdA IH hW hEG hFW hGY hrel
  · rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · exact (contra_HA hGY hFX hrel.symm').elim
      · exact (dyadic_EU_fin_one hEG).elim
    · obtain ⟨m', rfl⟩ : ∃ m', m = 2 + m' := ⟨m - 2, by omega⟩
      obtain ⟨W, hW, hGW⟩ := convert_H hEG hGY
      exact finish_step hdA IH hEF hW hFX hGW hrel
  · exact finish_step hdA IH hEF hEG hFX hGY hrel


/-- **Cassels, Ch. 8, Corollary to Lemma 4.1** ($p = 2$): *let $f, g$ be two improperly primitive integral forms and
suppose that $d(f) = d(g)$ is a unit. Then $f, g$ are $\mathbb Z_2$-equivalent.* Here $d(f) = \det F$. -/
@[kb "cassels1978" "Ch. 8, Cor. to Lemma 4.1, p. 119"]
theorem zpEquiv_of_improperlyPrimitive {F G : Matrix (Fin n) (Fin n) ℚ_[2]} (hF : Fᵀ = F) (hG : Gᵀ = G)
    (hFi : IsImproperlyPrimitive F) (hGi : IsImproperlyPrimitive G) (hd : F.det = G.det) (hu : ‖F.det‖ = 1) :
    ZpEquiv F G := by
  have hint : ∀ {M : Matrix (Fin n) (Fin n) ℚ_[2]}, IsImproperlyPrimitive M →
      (∀ i j, ‖M i j‖ ≤ 1) ∧ ∀ i, ‖M i i‖ < 1 := fun h =>
    ⟨h.1.1, fun i => lt_of_le_of_ne (h.1.1 i i) (fun hi => h.2 ⟨h.1, i, hi⟩)⟩
  have hEF : dyadicEU F := ⟨hF, (hint hFi).1, (hint hFi).2, hu⟩
  have hEG : dyadicEU G := ⟨hG, (hint hGi).1, (hint hGi).2, by rw [← hd]; exact hu⟩
  exact dyadic_EU_equiv n F G hEF hEG ⟨1, by simp, by simp [hd]⟩

end QuadFormsKB.Cassels
