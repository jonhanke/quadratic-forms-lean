/-
# Cassels, Chapter 9: Examples 2 and 9

**Layer:** binary forms `BinQF = QuadForm ℤ 2` (`BinQF.mk a b c` is $ax^2 + bxy + cy^2$) with the library's binary genus
theory (`Binary.sameGenus_iff_genusVec_eq`, fundamental discriminants); classically integral forms, with Cassels' entries
$g_{ij} = H_{ij}/2$ ($H$ the Hessian) and $d(f) = \det H/2^n$; proper equivalence `ProperIntEquiv` (`Ch9Sec1.lean`).

**Proves**
* Example 2 (first two parts): $x^2 + xy + 6y^2$, $2x^2 + xy + 3y^2$, $2x^2 - xy + 3y^2$ (discriminant $-23$) are in one
  genus (`ex2_sameGenus`) and no two of them are properly equivalent (`ex2_not_properIntEquiv`). The third part (every
  positive definite form of that determinant is properly equivalent to one of them) is not formalized.
* Example 9 (`ex9`): an isotropic classically integral form in $n \ge 2$ variables is properly equivalent to a form $g$
  with $g_{11} = 0$ and $g_{1j} = 0$ for $j \ge 3$; then $g_{12}^2 \mid d(f)$ (0-based: entries $(0, 0)$, $(0, j)$ for
  $j \ge 2$, and $(0, 1)$).
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec1
import QuadFormsKB.Literature.Cassels.Ch9Sec2
import QuadFormsKB.Binary.GenusCount

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

/-! ### Example 2 -/

/-- $x^2 + xy + 6y^2$. -/
def ex2f1 : BinQF := BinQF.mk 1 1 6
/-- $2x^2 + xy + 3y^2$. -/
def ex2f2 : BinQF := BinQF.mk 2 1 3
/-- $2x^2 - xy + 3y^2$. -/
def ex2f3 : BinQF := BinQF.mk 2 (-1) 3

/-- $-23$ is a fundamental discriminant, not $1$. -/
instance isQuadDisc_neg_twentythree : Binary.IsQuadDisc (-23) where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    left
    refine ⟨by norm_num, ?_⟩
    exact Int.squarefree_natAbs.mp (by norm_num; exact Nat.prime_iff.mp (by norm_num : Nat.Prime 23) |>.squarefree)
  ne_one := by norm_num

/-- The genus vector of a primitive positive definite form of discriminant $-23$ is trivial. -/
theorem genusVec_neg23 {f : BinQF} (hf : Binary.Primitive f) (hD : f.disc = -23) (hpos : f.PosDef') :
    Binary.genusVec (-23) f = 1 := by
  have hprod := Binary.prod_genusVec hf hD hpos
  have h23 : ∀ p : (-23 : ℤ).natAbs.primeFactors, (p : ℕ) = 23 := by
    rintro ⟨q, hq⟩
    have hp : (-23 : ℤ).natAbs.primeFactors = {23} := by
      have : (-23 : ℤ).natAbs = 23 := by norm_num
      rw [this]; exact Nat.Prime.primeFactors (by norm_num)
    rw [hp] at hq
    simpa using hq
  funext p
  rw [Finset.prod_eq_single p (fun q _ hq => absurd (Subtype.ext ((h23 q).trans (h23 p).symm)) hq)
    (by simp)] at hprod
  exact hprod

/-- **Cassels, Ch. 9, Example 2** (p. 162), first part: *the integer-valued forms $x^2 + xy + 6y^2$,
$2x^2 + xy + 3y^2$, $2x^2 - xy + 3y^2$ are in the same genus.* -/
@[kb "cassels1978" "Ch. 9, Ex. 2, p. 162 (the three forms are in one genus)"]
theorem ex2_sameGenus : SameGenus ex2f1 ex2f2 ∧ SameGenus ex2f1 ex2f3 := by
  have h1 : Binary.Primitive ex2f1 := by simp [Binary.Primitive, ex2f1]
  have h2 : Binary.Primitive ex2f2 := by simp [Binary.Primitive, ex2f2]
  have h3 : Binary.Primitive ex2f3 := by simp [Binary.Primitive, ex2f3]
  have d1 : ex2f1.disc = -23 := by simp [BinQF.disc, ex2f1]
  have d2 : ex2f2.disc = -23 := by simp [BinQF.disc, ex2f2]
  have d3 : ex2f3.disc = -23 := by simp [BinQF.disc, ex2f3]
  have p1 : ex2f1.PosDef' := ⟨by simp [ex2f1], by rw [d1]; norm_num⟩
  have p2 : ex2f2.PosDef' := ⟨by simp [ex2f2], by rw [d2]; norm_num⟩
  have p3 : ex2f3.PosDef' := ⟨by simp [ex2f3], by rw [d3]; norm_num⟩
  exact ⟨(Binary.sameGenus_iff_genusVec_eq h1 h2 d1 d2 p1 p2).mpr
      ((genusVec_neg23 h1 d1 p1).trans (genusVec_neg23 h2 d2 p2).symm),
    (Binary.sameGenus_iff_genusVec_eq h1 h3 d1 d3 p1 p3).mpr
      ((genusVec_neg23 h1 d1 p1).trans (genusVec_neg23 h3 d3 p3).symm)⟩

/-- A binary form evaluated at an arbitrary vector, in coordinates. -/
theorem binEval (f : BinQF) (v : Fin 2 → ℤ) :
    QuadForm.eval f v = f.a * v 0 ^ 2 + f.b * v 0 * v 1 + f.c * v 1 ^ 2 := by
  have h := BinQF.eval_eq f (v 0) (v 1)
  unfold BinQF.eval at h
  rwa [show ![v 0, v 1] = v by ext i; fin_cases i <;> rfl] at h

/-- A proper equivalence of binary forms in coordinates. -/
theorem proper_binary {f g : BinQF} (h : ProperIntEquiv f g) :
    ∃ p q r s : ℤ, p * s - q * r = 1 ∧ ∀ x y : ℤ,
      f.a * (p * x + q * y) ^ 2 + f.b * (p * x + q * y) * (r * x + s * y) + f.c * (r * x + s * y) ^ 2
        = g.a * x ^ 2 + g.b * x * y + g.c * y ^ 2 := by
  obtain ⟨T, hT, h⟩ := h
  refine ⟨T.val 0 0, T.val 0 1, T.val 1 0, T.val 1 1, by rw [Matrix.det_fin_two] at hT; linarith, fun x y => ?_⟩
  have := h ![x, y]
  rw [binEval, binEval] at this
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this

/-- $x^2 + xy + 6y^2$ never takes the value $2$. -/
theorem ex2f1_ne_two (a b : ℤ) : 1 * a ^ 2 + 1 * a * b + 6 * b ^ 2 ≠ 2 := by
  intro h
  have hb : b = 0 := by nlinarith [sq_nonneg (2 * a + b), sq_nonneg b]
  subst hb
  have : a ^ 2 = 2 := by linarith
  have h1 : a ≤ 1 := by nlinarith
  have h2 : -1 ≤ a := by nlinarith
  interval_cases a <;> omega

/-- **Cassels, Ch. 9, Example 2** (p. 162), second part: *no two of them are properly integrally equivalent.* -/
@[kb "cassels1978" "Ch. 9, Ex. 2, p. 162 (no two are properly equivalent)"]
theorem ex2_not_properIntEquiv :
    ¬ ProperIntEquiv ex2f1 ex2f2 ∧ ¬ ProperIntEquiv ex2f1 ex2f3 ∧ ¬ ProperIntEquiv ex2f2 ex2f3 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    obtain ⟨p, q, r, s, -, hh⟩ := proper_binary h
    have := hh 1 0
    simp [ex2f1, ex2f2] at this
    exact ex2f1_ne_two p r (by linarith)
  · intro h
    obtain ⟨p, q, r, s, -, hh⟩ := proper_binary h
    have := hh 1 0
    simp [ex2f1, ex2f3] at this
    exact ex2f1_ne_two p r (by linarith)
  · intro h
    obtain ⟨p, q, r, s, hdet, hh⟩ := proper_binary h
    have e0 := hh 1 0
    have e1 := hh 0 1
    have e2 := hh 1 1
    simp [ex2f2, ex2f3] at e0 e1 e2
    have hr : r = 0 := by nlinarith [sq_nonneg (4 * p + r), sq_nonneg r]
    subst hr
    have hp : p * p = 1 := by nlinarith
    have hs : s = p := by
      rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hp with ⟨h1, -⟩ | ⟨h1, -⟩ <;> subst h1 <;> linarith
    subst hs
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hp with ⟨h1, -⟩ | ⟨h1, -⟩ <;> subst h1 <;> (have : 4 * q + 2 = 0 ∨ 4 * q - 2 = 0 := by first | (left; nlinarith) | (right; nlinarith)) <;> omega

/-! ### Example 9 -/

/-- The matrix $R = r \otimes e_{i_0}$, i.e. $R_{ab} = r_a \delta_{b, i_0}$. -/
def unipR {n : ℕ} (i0 : Fin n) (r : Fin n → ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun a b => r a * (if b = i0 then 1 else 0)

/-- $(R M)_{ak} = r_a M_{i_0 k}$. -/
theorem unipR_mul_apply {n : ℕ} (i0 : Fin n) (r : Fin n → ℤ) (M : Matrix (Fin n) (Fin n) ℤ) (a k : Fin n) :
    (unipR i0 r * M) a k = r a * M i0 k := by
  simp [unipR, Matrix.mul_apply]

/-- $R \vec x = x_{i_0} r$. -/
theorem unipR_mulVec {n : ℕ} (i0 : Fin n) (r : Fin n → ℤ) (x : Fin n → ℤ) (a : Fin n) :
    (unipR i0 r *ᵥ x) a = r a * x i0 := by
  simp [unipR, Matrix.mulVec, dotProduct]

/-- $R^2 = 0$ when $r_{i_0} = 0$. -/
theorem unipR_mul_self {n : ℕ} (i0 : Fin n) (r : Fin n → ℤ) (hr : r i0 = 0) :
    unipR i0 r * unipR i0 r = 0 := by
  ext a b
  rw [unipR_mul_apply]
  simp [unipR, hr]

/-- The unipotent matrix $1 - r \otimes e_{i_0}$ ($r_{i_0} = 0$) as an element of $\mathrm{GL}_n(\mathbb Z)$. -/
def unipCol {n : ℕ} (i0 : Fin n) (r : Fin n → ℤ) (hr : r i0 = 0) : GL (Fin n) ℤ where
  val := 1 - unipR i0 r
  inv := 1 + unipR i0 r
  val_inv := by
    have h : (1 - unipR i0 r) * (1 + unipR i0 r) = 1 - unipR i0 r * unipR i0 r := by noncomm_ring
    rw [h, unipR_mul_self i0 r hr, sub_zero]
  inv_val := by
    have h : (1 + unipR i0 r) * (1 - unipR i0 r) = 1 - unipR i0 r * unipR i0 r := by noncomm_ring
    rw [h, unipR_mul_self i0 r hr, sub_zero]

/-- The transpose of an element of $\mathrm{GL}_n(\mathbb Z)$. -/
def glTranspose {n : ℕ} (U : GL (Fin n) ℤ) : GL (Fin n) ℤ where
  val := U.valᵀ
  inv := (U⁻¹).valᵀ
  val_inv := by rw [← Matrix.transpose_mul]; simp
  inv_val := by rw [← Matrix.transpose_mul]; simp

/-- A vector $w$ with $w_0 = 0$ can be written $w = c \cdot (\text{row } 1 \text{ of } Q)$ for some $Q \in \mathrm{GL}_n(\mathbb Z)$
fixing $e_0$. -/
theorem exists_fixing_row {n : ℕ} (hn : 2 ≤ n) (w : Fin n → ℤ) (hw : w ⟨0, by omega⟩ = 0) :
    ∃ (Q : GL (Fin n) ℤ) (c : ℤ), Q.val *ᵥ Pi.single ⟨0, by omega⟩ 1 = Pi.single ⟨0, by omega⟩ 1 ∧
      ∀ k, w k = c * Q.val ⟨1, hn⟩ k := by
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, hn⟩ with hi1
  have h01 : i0 < i1 := by simp [Fin.lt_def, hi0, hi1]
  obtain ⟨w', hw', hg⟩ := Finset.extract_gcd w (Finset.univ_nonempty_iff.mpr ⟨i0⟩)
  set c := Finset.univ.gcd w with hc
  by_cases hc0 : c = 0
  · refine ⟨1, c, by rw [Units.val_one, Matrix.one_mulVec], fun k => ?_⟩
    rw [hw' k (Finset.mem_univ k), hc0]; simp
  have hw'0 : w' i0 = 0 := by
    have := hw' i0 (Finset.mem_univ _)
    rw [hw] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hc0
  have htail : Reduction.tailGcd i1 w' = 1 := by
    have hdvd : Reduction.tailGcd i1 w' ∣ Finset.univ.gcd w' := by
      apply Finset.dvd_gcd
      intro k _
      by_cases hk : i1 ≤ k
      · exact Finset.gcd_dvd (by simp [hk])
      · have : k = i0 := by
          rw [not_le, Fin.lt_def] at hk
          ext; simp [hi0, hi1] at hk ⊢; omega
        subst this; rw [hw'0]; exact dvd_zero _
    rw [hg] at hdvd
    have hnn : 0 ≤ Reduction.tailGcd i1 w' := Int.nonneg_of_normalize_eq_self Finset.normalize_gcd
    exact Int.eq_one_of_dvd_one hnn hdvd
  obtain ⟨U, hU1, hU2⟩ := (Reduction.extendsBasis_iff_gcd i1 w').mpr htail
  have hU0 : ∀ k, U.val k i0 = (Pi.single i0 1 : Fin n → ℤ) k := hU1 i0 h01
  set r : Fin n → ℤ := fun k => if k = i0 then 0 else U.val i0 k with hr
  have hr0 : r i0 = 0 := by simp [hr]
  have hne : i1 ≠ i0 := ne_of_gt h01
  have hr1 : r i1 = 0 := by simp [hr, hne, hU2, hw'0]
  refine ⟨unipCol i0 r hr0 * glTranspose U, c, ?_, fun k => ?_⟩
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    have h1 : (glTranspose U).val *ᵥ Pi.single i0 1 = fun k => U.val i0 k := by
      rw [glTranspose, Matrix.mulVec_single_one]; rfl
    rw [h1]
    ext k
    simp only [unipCol, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, unipR_mulVec]
    have h2 : U.val i0 i0 = 1 := by rw [hU0]; simp
    rw [h2]
    by_cases hk : k = i0
    · subst hk; simp [hr0, h2]
    · have := hU0 k
      simp [hk, hr]
  · rw [hw' k (Finset.mem_univ k)]
    congr 1
    rw [Units.val_mul]
    have h3 : (unipCol i0 r hr0).val = 1 - unipR i0 r := rfl
    rw [h3, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, unipR_mul_apply, hr1, zero_mul, sub_zero]
    simp [glTranspose, hU2]


/-- A matrix whose first column is $(b, 0, \dots, 0)^{\mathsf T}$ has determinant $b \cdot$ (the minor). -/
theorem det_firstCol_single (m : ℕ) (B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (h : ∀ i : Fin m, B i.succ 0 = 0) :
    ∃ k : ℤ, B.det = B 0 0 * k := by
  refine ⟨(B.submatrix Fin.succ Fin.succ).det, ?_⟩
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h]

/-- If the first row of a symmetric $A$ is $(0, c, 0, \dots, 0)$ then $c^2 \mid \det A$. -/
theorem sq_dvd_det_of_firstRow (m : ℕ) (A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℤ) (hA : A.IsSymm)
    (h0 : ∀ j, j ≠ 1 → A 0 j = 0) : A 0 1 ^ 2 ∣ A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hz : ∀ j : Fin m, A 0 j.succ.succ = 0 := fun j => h0 _ (by simp [Fin.ext_iff])
  have h00 : A 0 0 = 0 := h0 0 (by simp)
  obtain ⟨k, hk⟩ := det_firstCol_single m (A.submatrix Fin.succ (Fin.succAbove (Fin.succ 0))) (fun i => by
    have : A i.succ.succ 0 = A 0 i.succ.succ := by
      have := congrFun (congrFun hA 0) i.succ.succ
      simpa [Matrix.transpose_apply] using this
    simp [this, hz])
  have hc : A 1 0 = A 0 1 := by
    have := congrFun (congrFun hA 0) 1
    simpa [Matrix.transpose_apply] using this
  have hk' : (A.submatrix Fin.succ (Fin.succAbove 1)).det = A 1 0 * k := by simpa using hk
  refine ⟨-k, ?_⟩
  simp [hz, h00]
  rw [hk', hc]
  ring


/-- $M_{ij} = e_i^{\mathsf T} M e_j$. -/
theorem entry_eq_dot {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    M i j = Pi.single i 1 ⬝ᵥ (M *ᵥ Pi.single j 1) := by
  simp

/-- **Core of Example 9:** for a symmetric $G$ and a nonzero isotropic $v$ ($v^{\mathsf T}Gv = 0$) there is
$T \in \mathrm{SL}_n(\mathbb Z)$ with $(T^{\mathsf T}GT)_{0j} = 0$ for all $j \ne 1$. -/
theorem exists_isotropic_basis {n : ℕ} (hn : 2 ≤ n) (G : Matrix (Fin n) (Fin n) ℤ) (hG : G.IsSymm)
    (v : Fin n → ℤ) (hv : v ≠ 0) (hGv : v ⬝ᵥ (G *ᵥ v) = 0) :
    ∃ T : GL (Fin n) ℤ, T.val.det = 1 ∧
      ∀ j : Fin n, (j : ℕ) ≠ 1 → (T.valᵀ * G * T.val) ⟨0, by omega⟩ j = 0 := by
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, hn⟩ with hi1
  obtain ⟨v', hv', hg⟩ := Finset.extract_gcd v (Finset.univ_nonempty_iff.mpr ⟨i0⟩)
  set d := Finset.univ.gcd v with hd
  have hd0 : d ≠ 0 := by
    intro h0
    apply hv
    funext k
    rw [hv' k (Finset.mem_univ k), h0]; simp
  have hvv : v = d • v' := funext fun k => by rw [hv' k (Finset.mem_univ k)]; rfl
  have hiso : v' ⬝ᵥ (G *ᵥ v') = 0 := by
    rw [hvv, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_smul] at hGv
    simp only [smul_eq_mul] at hGv
    exact (mul_eq_zero.mp hGv).resolve_left (mul_ne_zero hd0 hd0)
  obtain ⟨T1, hT1⟩ := (exists_basis_first_iff_gcd (by omega : 0 < n) v').mpr hg
  set u := G *ᵥ v' with hu
  set w := T1.valᵀ *ᵥ u with hw
  have hw0 : w i0 = 0 := by
    have : w i0 = v' ⬝ᵥ u := by
      rw [← hT1, Matrix.mulVec_single_one]
      simp [hw, Matrix.mulVec, dotProduct, mul_comm, Matrix.col]
      rfl
    rw [this, hu]; exact hiso
  obtain ⟨Q, c, hQ0, hQc⟩ := exists_fixing_row hn w hw0
  have hQi0 : Q⁻¹.val *ᵥ Pi.single i0 1 = Pi.single i0 1 := by
    conv_lhs => rw [← hQ0]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hrow : ∀ j : Fin n, (j : ℕ) ≠ 1 → ((T1 * Q⁻¹).valᵀ * G * (T1 * Q⁻¹).val) i0 j = 0 := by
    intro j hj
    have hji : i1 ≠ j := fun h => hj (by rw [← h])
    rw [Units.val_mul]
    set T : Matrix (Fin n) (Fin n) ℤ := T1.val * Q⁻¹.val with hT
    have hTe0 : T *ᵥ Pi.single i0 1 = v' := by
      rw [hT, ← Matrix.mulVec_mulVec, hQi0]; exact hT1
    have h1 : (Tᵀ * G * T) i0 j = Pi.single i0 1 ⬝ᵥ (Tᵀ *ᵥ (G *ᵥ (T *ᵥ Pi.single j 1))) := by
      rw [entry_eq_dot (Tᵀ * G * T) i0 j, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hvG : v' ᵥ* G = u := by
      conv_lhs => rw [← hG.eq]
      exact Matrix.vecMul_transpose G v'
    have h2 : Pi.single i0 1 ⬝ᵥ (Tᵀ *ᵥ (G *ᵥ (T *ᵥ Pi.single j 1))) = u ⬝ᵥ (T *ᵥ Pi.single j 1) := by
      rw [Matrix.dotProduct_mulVec (Pi.single i0 1) Tᵀ, Matrix.vecMul_transpose, hTe0,
        Matrix.dotProduct_mulVec v' G, hvG]
    have hu1 : u ᵥ* T1.val = w := by
      rw [hw, ← Matrix.vecMul_transpose, Matrix.transpose_transpose]
    have h3 : u ⬝ᵥ (T *ᵥ Pi.single j 1) = w ⬝ᵥ (Q⁻¹.val *ᵥ Pi.single j 1) := by
      rw [hT, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u T1.val, hu1]
    have h4 : w ⬝ᵥ (Q⁻¹.val *ᵥ Pi.single j 1) = c * (Q.val * Q⁻¹.val) i1 j := by
      simp only [dotProduct, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.mulVec_single_one]
      show w k * Q⁻¹.val k j = c * (Q.val i1 k * Q⁻¹.val k j)
      rw [hQc k]; ring
    rw [h1, h2, h3, h4, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_ne hji, mul_zero]
  rcases det_GL_int_eq (T1 * Q⁻¹) with hd | hd
  · exact ⟨T1 * Q⁻¹, hd, hrow⟩
  · have hnpos : 0 < n := by omega
    refine ⟨T1 * Q⁻¹ * reflFirst hnpos, ?_, fun j hj => ?_⟩
    · rw [Units.val_mul, Matrix.det_mul, hd, det_reflFirst]; norm_num
    · set R := (reflFirst hnpos).val with hR
      have hRd : ∃ d : Fin n → ℤ, R = Matrix.diagonal d := ⟨_, rfl⟩
      obtain ⟨dd, hdd⟩ := hRd
      have hRt : Rᵀ = R := by rw [hdd, Matrix.diagonal_transpose]
      rw [Units.val_mul, Matrix.transpose_mul, hRt, ← hR]
      have e : R * (T1 * Q⁻¹).valᵀ * G * ((T1 * Q⁻¹).val * R)
          = R * ((T1 * Q⁻¹).valᵀ * G * (T1 * Q⁻¹).val) * R := by
        simp only [Matrix.mul_assoc]
      rw [e, hdd, Matrix.mul_diagonal, Matrix.diagonal_mul, hrow j hj]
      simp


/-- A form given by a symmetric Gram matrix $A$ has Hessian $A + A^{\mathsf T}$. -/
theorem hessian_of_gram {n : ℕ} (g : QuadForm ℤ n) (A : Matrix (Fin n) (Fin n) ℤ)
    (h : ∀ x, g.eval x = x ⬝ᵥ (A *ᵥ x)) : g.hessian = A + Aᵀ := by
  have := (eval_mulVec_eq_iff_hessian g (LocalDensity.ofMatrixZ A) 1).mp (fun x => by
    rw [Matrix.one_mulVec, LocalDensity.eval_ofMatrixZ, h])
  simpa [LocalDensity.hessian_ofMatrixZ] using this

/-- **Cassels, Ch. 9, Example 9** (p. 163): *let $f(\mathbf x)$ be an isotropic classically integral form in $n$
variables. Show that $f$ is properly integrally equivalent to a form $g(\mathbf x) = \sum g_{ij}x_ix_j$ with
$g_{1j} = 0$ ($j \ne 2$). Deduce that $g_{12}^2 \mid d(f)$.* Here $n \ge 2$, isotropic means $f(\mathbf x) = 0$ for some
$\mathbf x \in \mathbb Z^n$, $\mathbf x \ne 0$, and indices are 0-based ($g_{1j} = H_{0j}/2$ for the Hessian $H$ of $g$,
$d(f) = \det H_f/2^n$). -/
@[kb "cassels1978" "Ch. 9, Ex. 9, p. 163"]
theorem ex9 {n : ℕ} (hn : 2 ≤ n) {f : QuadForm ℤ n} (hf : IsClassicallyIntegral f)
    (hiso : ∃ x : Fin n → ℤ, x ≠ 0 ∧ f.eval x = 0) :
    ∃ g : QuadForm ℤ n, ProperIntEquiv f g ∧ IsClassicallyIntegral g ∧
      (∀ j : Fin n, (j : ℕ) ≠ 1 → g.hessian ⟨0, by omega⟩ j = 0) ∧
      (g.hessian ⟨0, by omega⟩ ⟨1, hn⟩ / 2) ^ 2 ∣ f.hessian.det / 2 ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨G, hGs, hGe⟩ := hf
  obtain ⟨v, hv, hf0⟩ := hiso
  have hGv : v ⬝ᵥ (G *ᵥ v) = 0 := by rw [← hf0, hGe]; rfl
  obtain ⟨T, hdet, hrow⟩ := exists_isotropic_basis hn G hGs v hv hGv
  obtain ⟨g, hg⟩ := exists_eval_mulVec_form f T.val
  have hAs : (T.valᵀ * G * T.val).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hGs.eq, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hgA : ∀ x, g.eval x = x ⬝ᵥ ((T.valᵀ * G * T.val) *ᵥ x) := by
    intro x
    rw [← hg, hGe, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x,
      Matrix.vecMul_transpose]
    rfl
  have hgH := hessian_of_gram g _ hgA
  have hfH := hessian_of_gram f G hGe
  rw [hAs.eq] at hgH
  rw [hGs.eq] at hfH
  have h0 : ∀ j : Fin (m + 2), j ≠ 1 → (T.valᵀ * G * T.val) 0 j = 0 := fun j hj =>
    hrow j (fun h => hj (Fin.ext (by simpa using h)))
  refine ⟨g, ⟨T, hdet, hg⟩, ⟨_, hAs, hgA⟩, fun j hj => ?_, ?_⟩
  · rw [hgH, Matrix.add_apply]
    have := h0 j (fun h => hj (by rw [h]; rfl))
    rw [show (⟨0, by omega⟩ : Fin (m + 2)) = 0 from rfl, this]
    simp
  · have e1 : g.hessian ⟨0, by omega⟩ ⟨1, hn⟩ / 2 = (T.valᵀ * G * T.val) 0 1 := by
      rw [hgH, Matrix.add_apply]
      rw [show (⟨0, by omega⟩ : Fin (m + 2)) = 0 from rfl, show (⟨1, hn⟩ : Fin (m + 2)) = 1 from rfl]
      omega
    have e2 : f.hessian.det / 2 ^ (m + 2) = G.det := by
      rw [hfH, show G + G = (2 : ℤ) • G by rw [two_smul], Matrix.det_smul, Fintype.card_fin]
      exact Int.mul_ediv_cancel_left _ (by positivity)
    have e3 : (T.valᵀ * G * T.val).det = G.det := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdet]; ring
    rw [e1, e2, ← e3]
    exact sq_dvd_det_of_firstRow m _ hAs h0


end QuadFormsKB.Siegel
