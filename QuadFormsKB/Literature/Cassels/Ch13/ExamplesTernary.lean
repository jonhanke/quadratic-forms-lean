/-
# Cassels, Chapter 13, Example 8: helpers

Helper lemmas for `example_8` (`Ch13/Examples.lean`): stabilizers of an integral vector in the automorph group of a
classically integral ternary form that is real-equivalent to $X^2 + Y^2 - Z^2$.
-/
import QuadFormsKB.Literature.Cassels.Ch13.Sec8
import QuadFormsKB.Literature.Cassels.Ch13.Sec3

open Matrix

namespace QuadFormsKB.Reduction

/-- Helper: the real matrix of `ofGram A` is `A` (for symmetric `A`). -/
theorem realMat_ofGram_eq {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) (hA : A.IsSymm) :
    realMat (Siegel.ofGram A) = A.map (Int.cast : ℤ → ℝ) := by
  ext i j
  have h := congrFun (congrFun hA.eq i) j
  simp only [Matrix.transpose_apply] at h
  simp [realMat, Siegel.hessian_ofGram, Matrix.add_apply, ← h]
  ring

/-- Helper: automorphs of `ofGram A` are the integral `T` with `TᵀAT = A`. -/
theorem mem_aut_ofGram {k : ℕ} {A : Matrix (Fin k) (Fin k) ℤ} (hA : A.IsSymm) (T : GL (Fin k) ℤ) :
    T ∈ Siegel.Aut (Siegel.ofGram A) ↔ T.valᵀ * A * T.val = A := by
  rw [show T ∈ Siegel.Aut (Siegel.ofGram A) ↔ T.valᵀ * (Siegel.ofGram A).hessian * T.val = (Siegel.ofGram A).hessian from
    Siegel.eval_mulVec_eq_iff_hessian _ _ T.val, Siegel.hessian_ofGram, hA.eq]
  have e : T.valᵀ * (A + A) * T.val = T.valᵀ * A * T.val + T.valᵀ * A * T.val := by
    simp only [Matrix.mul_add, Matrix.add_mul]
  rw [e]
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.add_apply] at this
    omega
  · intro h; rw [h]

/-- Helper: the stabilizer is finite when `f(b) < 0` (Example 8 (i)). -/
theorem ex8_finite {A : Matrix (Fin 3) (Fin 3) ℤ} (hA : A.IsSymm) {L : Matrix (Fin 3) (Fin 3) ℝ}
    (hL : IsUnit L.det) (hF : A.map (Int.cast : ℤ → ℝ) = Lᵀ * lorentz * L) (b : Fin 3 → ℤ)
    (hb : b ⬝ᵥ (A *ᵥ b) < 0) :
    {T | T ∈ Siegel.Aut (Siegel.ofGram A) ∧ T.val *ᵥ b = b}.Finite := by
  set Q := Siegel.ofGram A with hQdef
  have hQ : realMat Q = Lᵀ * lorentz * L := (realMat_ofGram_eq A hA).trans hF
  set Y : Fin 3 → ℝ := L *ᵥ cast b with hYdef
  have hY : Y 0 ^ 2 + Y 1 ^ 2 < Y 2 ^ 2 := by
    have h1 : cast b ⬝ᵥ ((A.map (Int.cast : ℤ → ℝ)) *ᵥ cast b) = ((b ⬝ᵥ (A *ᵥ b) : ℤ) : ℝ) := by
      simp [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
    have h2 : cast b ⬝ᵥ ((A.map (Int.cast : ℤ → ℝ)) *ᵥ cast b) = Y ⬝ᵥ (lorentz *ᵥ Y) := by
      rw [hF, hYdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_transpose]
    have h3 : Y ⬝ᵥ (lorentz *ᵥ Y) = Y 0 ^ 2 + Y 1 ^ 2 - Y 2 ^ 2 := by
      rw [lorentz_mulVec]; simp [dotProduct, Fin.sum_univ_three]; ring
    have h4 : ((b ⬝ᵥ (A *ᵥ b) : ℤ) : ℝ) < 0 := by exact_mod_cast hb
    linarith
  obtain ⟨hY2, hη⟩ := projPt_mem_disc hY
  set η := projPt Y with hη_def
  set r : ℝ := Real.sqrt (η 0 ^ 2 + η 1 ^ 2) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : r < 1 := by
    rw [hr, Real.sqrt_lt' one_pos]; simpa [disc] using hη
  have hr2 : r ^ 2 = η 0 ^ 2 + η 1 ^ 2 := Real.sq_sqrt (by positivity)
  have hS := finite_actD_mem_ball hL hQ hη hr0 hr1
  -- fixed points
  have hfix : ∀ T : GL (Fin 3) ℤ, T.val *ᵥ b = b → actD L (castM T.val) η = η := by
    intro T hT
    unfold actD flt
    have hLL : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul _ hL
    have hP : (L * castM T.val * L⁻¹) *ᵥ Y = Y := by
      rw [hYdef, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hLL, Matrix.mul_one,
        ← Matrix.mulVec_mulVec, castM_mulVec_cast, hT]
    rw [hη_def, mulVec_liftPt_projPt _ hY2, hP, projPt_smul (inv_ne_zero hY2)]
  -- negation
  have hneg : ∀ W : GL (Fin 3) ℤ, W ∈ Siegel.Aut Q → W.val.det = -1 →
      -W ∈ Siegel.AutPlus Q ∧ ∀ ξ, actD L (castM (-W).val) ξ = actD L (castM W.val) ξ := by
    intro W hW h
    have hc : castM (-W).val = -castM W.val := by
      ext i j; simp [castM]
    refine ⟨Siegel.mem_autPlus_iff.2 ⟨?_, ?_⟩, fun ξ => ?_⟩
    · rw [mem_aut_iff_act] at hW ⊢
      unfold act at hW ⊢
      rw [hc]
      simpa [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg] using hW
    · simp [Matrix.det_neg, h]
    · unfold actD
      rw [hc, Matrix.mul_neg, Matrix.neg_mul, flt_neg]
  refine (hS.union (hS.image Neg.neg)).subset ?_
  rintro T ⟨hT, hTb⟩
  have hfx := hfix T hTb
  have hdet : IsUnit T.val.det := (Matrix.isUnit_iff_isUnit_det _).1 T.isUnit
  rcases Int.isUnit_iff.1 hdet with h | h
  · left
    refine ⟨Siegel.mem_autPlus_iff.2 ⟨hT, h⟩, ?_⟩
    rw [hfx, hr2]
  · right
    obtain ⟨h1, h2⟩ := hneg T hT h
    refine ⟨-T, ⟨h1, ?_⟩, neg_neg T⟩
    rw [h2, hfx, hr2]

/-- Helper: integer vectors orthogonal to `w` completing `b` (with `b ⬝ w ≠ 0`) to a basis (up to finite index). -/
theorem ex8_perp (w b : Fin 3 → ℤ) (hm : b ⬝ᵥ w ≠ 0) :
    ∃ u v : Fin 3 → ℤ, u ⬝ᵥ w = 0 ∧ v ⬝ᵥ w = 0 ∧
      (!![b 0, u 0, v 0; b 1, u 1, v 1; b 2, u 2, v 2] : Matrix (Fin 3) (Fin 3) ℤ).det ≠ 0 := by
  have hw : w 0 ≠ 0 ∨ w 1 ≠ 0 ∨ w 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hm
    simp [dotProduct, Fin.sum_univ_three, h.1, h.2.1, h.2.2]
  rcases hw with h | h | h
  · refine ⟨![w 1, -w 0, 0], ![w 2, 0, -w 0], ?_, ?_, ?_⟩
    · simp [dotProduct, Fin.sum_univ_three]; ring
    · simp [dotProduct, Fin.sum_univ_three]; ring
    · have : (!![b 0, w 1, w 2; b 1, -w 0, 0; b 2, 0, -w 0] : Matrix (Fin 3) (Fin 3) ℤ).det
          = w 0 * (b ⬝ᵥ w) := by
        simp [Matrix.det_fin_three, dotProduct, Fin.sum_univ_three]; ring
      simpa using (show (!![b 0, w 1, w 2; b 1, -w 0, 0; b 2, 0, -w 0] : Matrix (Fin 3) (Fin 3) ℤ).det ≠ 0 from
        this ▸ mul_ne_zero h hm)
  · refine ⟨![-w 1, w 0, 0], ![0, w 2, -w 1], ?_, ?_, ?_⟩
    · simp [dotProduct, Fin.sum_univ_three]; ring
    · simp [dotProduct, Fin.sum_univ_three]; ring
    · have : (!![b 0, -w 1, 0; b 1, w 0, w 2; b 2, 0, -w 1] : Matrix (Fin 3) (Fin 3) ℤ).det
          = -(w 1 * (b ⬝ᵥ w)) := by
        simp [Matrix.det_fin_three, dotProduct, Fin.sum_univ_three]; ring
      simpa using (show (!![b 0, -w 1, 0; b 1, w 0, w 2; b 2, 0, -w 1] : Matrix (Fin 3) (Fin 3) ℤ).det ≠ 0 from
        this ▸ neg_ne_zero.2 (mul_ne_zero h hm))
  · refine ⟨![w 2, 0, -w 0], ![0, w 2, -w 1], ?_, ?_, ?_⟩
    · simp [dotProduct, Fin.sum_univ_three]; ring
    · simp [dotProduct, Fin.sum_univ_three]; ring
    · have : (!![b 0, w 2, 0; b 1, 0, w 2; b 2, -w 0, -w 1] : Matrix (Fin 3) (Fin 3) ℤ).det
          = w 2 * (b ⬝ᵥ w) := by
        simp [Matrix.det_fin_three, dotProduct, Fin.sum_univ_three]; ring
      simpa using (show (!![b 0, w 2, 0; b 1, 0, w 2; b 2, -w 0, -w 1] : Matrix (Fin 3) (Fin 3) ℤ).det ≠ 0 from
        this ▸ mul_ne_zero h hm)

/-- Helper: a nonzero binary form `(a, b, c)` with `a c - b² < 0` is `g` times a primitive one. -/
theorem ex8_primitive {a b c : ℤ} (h : a * c - b ^ 2 < 0) :
    ∃ g a' b' c' : ℤ, 0 < g ∧ a = g * a' ∧ b = g * b' ∧ c = g * c' ∧ Int.gcd a' (Int.gcd b' c') = 1 := by
  set n := Int.gcd a (Int.gcd b c) with hn
  have hn0 : n ≠ 0 := by
    intro h0
    have h1 : a = 0 := Int.gcd_eq_zero_iff.1 h0 |>.1
    have h2 : ((Int.gcd b c : ℕ) : ℤ) = 0 := Int.gcd_eq_zero_iff.1 h0 |>.2
    have h3 : b = 0 := Int.gcd_eq_zero_iff.1 (by exact_mod_cast h2) |>.1
    subst h1 h3
    simp at h
  have hda : (n : ℤ) ∣ a := Int.gcd_dvd_left _ _
  have hdbc : (n : ℤ) ∣ ((Int.gcd b c : ℕ) : ℤ) := Int.gcd_dvd_right _ _
  have hdb : (n : ℤ) ∣ b := hdbc.trans (Int.gcd_dvd_left _ _)
  have hdc : (n : ℤ) ∣ c := hdbc.trans (Int.gcd_dvd_right _ _)
  obtain ⟨a', ha⟩ := hda
  obtain ⟨b', hb⟩ := hdb
  obtain ⟨c', hc⟩ := hdc
  refine ⟨n, a', b', c', by positivity, ha, hb, hc, ?_⟩
  have key : Int.gcd ((n : ℤ) * a') (Int.gcd ((n : ℤ) * b') ((n : ℤ) * c')) = n := by
    rw [← ha, ← hb, ← hc]
  rw [Int.gcd_mul_left (n : ℤ) b' c', Int.natAbs_natCast] at key
  push_cast at key
  rw [Int.gcd_mul_left, Int.natAbs_natCast] at key
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn0) (key.trans (mul_one n).symm)

/-- Helper: some positive power of `T₀ ∈ GL₂(ℤ)` and all its multiples are `≡ 1 (mod D)` entrywise. -/
theorem ex8_cong (T₀ : GL (Fin 2) ℤ) (D : ℤ) (hD : D ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ ∀ (j : ℕ) (i i' : Fin 2), D ∣ (T₀ ^ (k * j)).val i i' - (1 : Matrix (Fin 2) (Fin 2) ℤ) i i' := by
  haveI : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.2 hD⟩
  let φ : Matrix (Fin 2) (Fin 2) ℤ →+* Matrix (Fin 2) (Fin 2) (ZMod D.natAbs) :=
    (Int.castRingHom (ZMod D.natAbs)).mapMatrix
  let t : (Matrix (Fin 2) (Fin 2) (ZMod D.natAbs))ˣ := Units.map φ.toMonoidHom T₀
  have hfin : IsOfFinOrder t := isOfFinOrder_of_finite t
  refine ⟨orderOf t, hfin.orderOf_pos, fun j i i' => ?_⟩
  have h1 : t ^ (orderOf t * j) = 1 := by rw [pow_mul, pow_orderOf_eq_one, one_pow]
  have h2 : φ ((T₀ ^ (orderOf t * j)).val) = 1 := by
    have := congrArg Units.val h1
    simpa [t, Units.val_pow_eq_pow_val] using this
  have h3 := congrFun (congrFun h2 i) i'
  have h3' : (((T₀ ^ (orderOf t * j)).val i i' : ℤ) : ZMod D.natAbs) =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod D.natAbs)) i i' := h3
  have h4 : (((T₀ ^ (orderOf t * j)).val i i' - (1 : Matrix (Fin 2) (Fin 2) ℤ) i i' : ℤ) : ZMod D.natAbs) = 0 := by
    rw [Int.cast_sub, h3']
    by_cases hi : i = i' <;> simp [Matrix.one_apply, hi]
  have h5 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h4
  exact Int.natAbs_dvd.1 (by exact_mod_cast h5)

/-- Helper: the block embedding `N ↦ diag(1, N)`. -/
def blk1 (N : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0; 0, N 0 0, N 0 1; 0, N 1 0, N 1 1]

/-- Helper: the block embedding `X ↦ diag(0, X)`. -/
def blk0 (N : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 0; 0, N 0 0, N 0 1; 0, N 1 0, N 1 1]

theorem blk1_eq {N X : Matrix (Fin 2) (Fin 2) ℤ} {D : ℤ} (h : N = 1 + D • X) :
    blk1 N = 1 + D • blk0 X := by
  subst h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk1, blk0, Matrix.one_apply, Matrix.smul_apply, -zsmul_eq_mul]

theorem det_blk1 (N : Matrix (Fin 2) (Fin 2) ℤ) : (blk1 N).det = N.det := by
  simp [blk1, Matrix.det_fin_three, Matrix.det_fin_two]

/-- Helper: `diag(1, N)` preserves `diag(m, g G)` when `N` preserves `G`. -/
theorem blk1_preserves (m g a b c : ℤ) (N : Matrix (Fin 2) (Fin 2) ℤ)
    (hN : Nᵀ * !![a, b; b, c] * N = !![a, b; b, c]) :
    (blk1 N)ᵀ * !![m, 0, 0; 0, g * a, g * b; 0, g * b, g * c] * blk1 N =
      !![m, 0, 0; 0, g * a, g * b; 0, g * b, g * c] := by
  have e00 := congrFun (congrFun hN 0) 0
  have e01 := congrFun (congrFun hN 0) 1
  have e10 := congrFun (congrFun hN 1) 0
  have e11 := congrFun (congrFun hN 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk1, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;>
    first | linear_combination g * e00 | linear_combination g * e01 | linear_combination g * e10 |
      linear_combination g * e11

/-- Helper: automorphs of `cform a b c` are the integral `T` with `TᵀGT = G`. -/
theorem mem_aut_cform (a b c : ℤ) (T : GL (Fin 2) ℤ) :
    T ∈ Siegel.Aut (cform a b c) ↔ T.valᵀ * !![a, b; b, c] * T.val = !![a, b; b, c] := by
  have hh : (cform a b c).hessian = !![a, b; b, c] + !![a, b; b, c] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [QuadForm.hessian, cform, BinQF.mk, QuadForm.ofUpper] <;> ring
  rw [show T ∈ Siegel.Aut (cform a b c) ↔ T.valᵀ * (cform a b c).hessian * T.val = (cform a b c).hessian from
    Siegel.eval_mulVec_eq_iff_hessian _ _ T.val, hh]
  have e : T.valᵀ * (!![a, b; b, c] + !![a, b; b, c]) * T.val
      = T.valᵀ * !![a, b; b, c] * T.val + T.valᵀ * !![a, b; b, c] * T.val := by
    simp only [Matrix.mul_add, Matrix.add_mul]
  rw [e]
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.add_apply] at this
    omega
  · intro h; rw [h]

/-- Helper: conjugating `diag(1, T₀^{kj})` by `C` gives infinitely many integral automorphs fixing `C e₀`. -/
theorem ex8_construct {A : Matrix (Fin 3) (Fin 3) ℤ} (hA : A.IsSymm) (C : Matrix (Fin 3) (Fin 3) ℤ)
    (hD : C.det ≠ 0) (m g a b c : ℤ)
    (hP : Cᵀ * A * C = !![m, 0, 0; 0, g * a, g * b; 0, g * b, g * c])
    {T₀ : GL (Fin 2) ℤ} (hT₀ : T₀ ∈ Siegel.AutPlus (cform a b c)) (hord : orderOf T₀ = 0) :
    {T : GL (Fin 3) ℤ | T ∈ Siegel.Aut (Siegel.ofGram A) ∧
      T.val *ᵥ (fun i => C i 0) = fun i => C i 0}.Infinite := by
  obtain ⟨k, hk, hcong⟩ := ex8_cong T₀ C.det hD
  have hS : ∀ j : ℕ, T₀ ^ (k * j) ∈ Siegel.AutPlus (cform a b c) := fun j => pow_mem hT₀ _
  have hNaut : ∀ j : ℕ, ((T₀ ^ (k * j)).val)ᵀ * !![a, b; b, c] * (T₀ ^ (k * j)).val = !![a, b; b, c] := fun j =>
    (mem_aut_cform a b c _).1 (Siegel.mem_autPlus_iff.1 (hS j)).1
  have hNdet : ∀ j : ℕ, (T₀ ^ (k * j)).val.det = 1 := fun j => (Siegel.mem_autPlus_iff.1 (hS j)).2
  have hX : ∀ j : ℕ, ∃ X : Matrix (Fin 2) (Fin 2) ℤ, (T₀ ^ (k * j)).val = 1 + C.det • X := by
    intro j
    refine ⟨Matrix.of fun i i' => ((T₀ ^ (k * j)).val i i' - (1 : Matrix (Fin 2) (Fin 2) ℤ) i i') / C.det, ?_⟩
    ext i i'
    obtain ⟨q, hq⟩ := hcong j i i'
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, hq]
    rw [Int.mul_ediv_cancel_left _ hD]
    linarith
  choose X hXeq using hX
  set T : ℕ → Matrix (Fin 3) (Fin 3) ℤ := fun j => 1 + C * blk0 (X j) * C.adjugate with hT
  have hTC : ∀ j, T j * C = C * blk1 (T₀ ^ (k * j)).val := by
    intro j
    rw [blk1_eq (hXeq j), hT]
    simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, Matrix.adjugate_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  have hDD : ∀ M : Matrix (Fin 3) (Fin 3) ℤ, (C.adjugate)ᵀ * (Cᵀ * M * C) * C.adjugate = (C.det * C.det) • M := by
    intro M
    calc _ = (C * C.adjugate)ᵀ * M * (C * C.adjugate) := by
          simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by
          rw [Matrix.mul_adjugate]
          simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.mul_smul,
            Matrix.one_mul, Matrix.mul_one, smul_smul]
  have hdet : ∀ j, (T j).det = 1 := by
    intro j
    have h := congrArg Matrix.det (hTC j)
    rw [Matrix.det_mul, Matrix.det_mul, det_blk1, hNdet, mul_one] at h
    exact mul_right_cancel₀ hD (by rw [h, one_mul])
  have hTAT : ∀ j, (T j)ᵀ * A * T j = A := by
    intro j
    have h1 : Cᵀ * ((T j)ᵀ * A * T j) * C = Cᵀ * A * C := by
      calc Cᵀ * ((T j)ᵀ * A * T j) * C = (T j * C)ᵀ * A * (T j * C) := by
            simp [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = (C * blk1 (T₀ ^ (k * j)).val)ᵀ * A * (C * blk1 (T₀ ^ (k * j)).val) := by rw [hTC]
        _ = (blk1 (T₀ ^ (k * j)).val)ᵀ * (Cᵀ * A * C) * blk1 (T₀ ^ (k * j)).val := by
            simp [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = Cᵀ * A * C := by rw [hP]; exact blk1_preserves m g a b c _ (hNaut j)
    have h2 := congrArg (fun M => (C.adjugate)ᵀ * M * C.adjugate) h1
    simp only [hDD] at h2
    ext i i'
    have h3 := congrFun (congrFun h2 i) i'
    simp only [Matrix.smul_apply, smul_eq_mul] at h3
    exact mul_left_cancel₀ (mul_ne_zero hD hD) h3
  have hmem : ∀ j, IsUnit (T j).det := fun j => by rw [hdet j]; exact isUnit_one
  let Tg : ℕ → GL (Fin 3) ℤ := fun j => Matrix.nonsingInvUnit (T j) (hmem j)
  have hTg : ∀ j, (Tg j).val = T j := fun j => rfl
  have hb : (fun i => C i 0) = C *ᵥ ![1, 0, 0] := by
    ext i; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hinj : Function.Injective Tg := by
    intro j j' h
    have h1 : T j = T j' := by rw [← hTg, ← hTg, h]
    have h2 : C * blk1 (T₀ ^ (k * j)).val = C * blk1 (T₀ ^ (k * j')).val := by
      rw [← hTC, ← hTC, h1]
    have h3 : C.det • blk1 (T₀ ^ (k * j)).val = C.det • blk1 (T₀ ^ (k * j')).val := by
      have := congrArg (fun M => C.adjugate * M) h2
      simpa [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul] using this
    have h4 : blk1 (T₀ ^ (k * j)).val = blk1 (T₀ ^ (k * j')).val := by
      ext i i'
      have := congrFun (congrFun h3 i) i'
      simp only [Matrix.smul_apply, smul_eq_mul] at this
      exact mul_left_cancel₀ hD this
    have e00 := congrFun (congrFun h4 1) 1
    have e01 := congrFun (congrFun h4 1) 2
    have e10 := congrFun (congrFun h4 2) 1
    have e11 := congrFun (congrFun h4 2) 2
    simp [blk1] at e00 e01 e10 e11
    have h5 : T₀ ^ (k * j) = T₀ ^ (k * j') := by
      ext i i'
      fin_cases i <;> fin_cases i' <;> simpa
    have hinjpow : Function.Injective (fun n : ℕ => T₀ ^ n) :=
      injective_pow_iff_not_isOfFinOrder.2 (orderOf_eq_zero_iff.1 hord)
    have := hinjpow h5
    exact Nat.eq_of_mul_eq_mul_left hk this
  refine Set.infinite_of_injective_forall_mem hinj fun j => ⟨?_, ?_⟩
  · rw [mem_aut_ofGram hA, hTg]; exact hTAT j
  · rw [hTg, hb, Matrix.mulVec_mulVec, hTC, ← Matrix.mulVec_mulVec]
    congr 1
    ext i; fin_cases i <;> simp [blk1, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- Helper: symmetry of the bilinear pairing. -/
theorem dot_mulVec_symm {R : Type*} [CommRing R] {n : ℕ} {A : Matrix (Fin n) (Fin n) R} (hA : A.IsSymm)
    (x y : Fin n → R) : x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA.eq, dotProduct_comm]

/-- Helper: values of `ofGram A` over `ℚ`. -/
theorem ex8_evalIn {A : Matrix (Fin 3) (Fin 3) ℤ} (hA : A.IsSymm) (y : Fin 3 → ℚ) :
    (Siegel.ofGram A).evalIn ℚ y = y ⬝ᵥ (A.map (Int.cast : ℤ → ℚ) *ᵥ y) := by
  have h : ∀ i j, A i j = A j i := fun i j => by simpa using (congrFun (congrFun hA.eq j) i)
  have h01 := h 0 1
  have h02 := h 0 2
  have h12 := h 1 2
  simp [QuadForm.evalIn, Siegel.ofGram, QuadForm.ofUpper, Fin.sum_univ_three, dotProduct, Matrix.mulVec]
  rw [← h01, ← h02, ← h12]
  ring

/-- Helper: casting a dot product. -/
theorem ex8_cast_dot (A : Matrix (Fin 3) (Fin 3) ℤ) (u v : Fin 3 → ℤ) :
    ((u ⬝ᵥ (A *ᵥ v) : ℤ) : ℚ) =
      (fun i => (u i : ℚ)) ⬝ᵥ ((A.map (Int.cast : ℤ → ℚ)) *ᵥ (fun i => (v i : ℚ))) := by
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]

/-- Helper: the stabilizer is infinite when `f` is anisotropic and `f(b) > 0` (Example 8 (ii)). -/
theorem ex8_infinite {A : Matrix (Fin 3) (Fin 3) ℤ} (hA : A.IsSymm) {L : Matrix (Fin 3) (Fin 3) ℝ}
    (hL : IsUnit L.det) (hF : A.map (Int.cast : ℤ → ℝ) = Lᵀ * lorentz * L) (b : Fin 3 → ℤ)
    (haniso : ¬ (Siegel.ofGram A).IsotropicIn ℚ) (hb : 0 < b ⬝ᵥ (A *ᵥ b)) :
    {T | T ∈ Siegel.Aut (Siegel.ofGram A) ∧ T.val *ᵥ b = b}.Infinite := by
  set m := b ⬝ᵥ (A *ᵥ b) with hm
  obtain ⟨u, v, hu, hv, hdet⟩ := ex8_perp (A *ᵥ b) b (by rw [← hm]; exact hb.ne')
  set C : Matrix (Fin 3) (Fin 3) ℤ := !![b 0, u 0, v 0; b 1, u 1, v 1; b 2, u 2, v 2] with hC
  have hcol : (fun i => C i 0) = b := by ext i; fin_cases i <;> rfl
  set a0 := u ⬝ᵥ (A *ᵥ u) with ha0
  set β0 := u ⬝ᵥ (A *ᵥ v) with hβ0
  set c0 := v ⬝ᵥ (A *ᵥ v) with hc0
  have hu' : b ⬝ᵥ (A *ᵥ u) = 0 := by rw [dot_mulVec_symm hA]; exact hu
  have hv' : b ⬝ᵥ (A *ᵥ v) = 0 := by rw [dot_mulVec_symm hA]; exact hv
  have hPentry : ∀ i j, (Cᵀ * A * C) i j = ![b, u, v] i ⬝ᵥ (A *ᵥ ![b, u, v] j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hC, Matrix.mul_apply, dotProduct, Matrix.mulVec, Fin.sum_univ_three] <;> ring
  have hP : Cᵀ * A * C = !![m, 0, 0; 0, a0, β0; 0, β0, c0] := by
    ext i j
    rw [hPentry]
    fin_cases i <;> fin_cases j <;> simp [hm, ha0, hβ0, hc0]
    all_goals first | assumption | (rw [dot_mulVec_symm hA]; assumption) | exact dot_mulVec_symm hA _ _
  -- the determinant of A is negative
  have hdetA : A.det < 0 := by
    have hmap : (A.map (Int.cast : ℤ → ℝ)).det = ((A.det : ℤ) : ℝ) := by
      have := RingHom.map_det (Int.castRingHom ℝ) A
      simpa [RingHom.mapMatrix_apply] using this.symm
    have h1 : ((A.det : ℤ) : ℝ) = -(L.det * L.det) := by
      have := congrArg Matrix.det hF
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
        show lorentz.det = -1 by simp [lorentz, Matrix.det_diagonal, Fin.prod_univ_three], hmap] at this
      rw [this]; ring
    have h2 : 0 < L.det * L.det := mul_self_pos.2 hL.ne_zero
    have : ((A.det : ℤ) : ℝ) < 0 := by rw [h1]; linarith
    exact_mod_cast this
  have hind0 : a0 * c0 - β0 ^ 2 < 0 := by
    have h1 := congrArg Matrix.det hP
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
    have hdP : (!![m, 0, 0; 0, a0, β0; 0, β0, c0] : Matrix (Fin 3) (Fin 3) ℤ).det = m * (a0 * c0 - β0 ^ 2) := by
      simp [Matrix.det_fin_three]; ring
    rw [hdP] at h1
    have h2 : 0 < C.det * C.det := mul_self_pos.2 hdet
    have h3 : m * (a0 * c0 - β0 ^ 2) < 0 := by
      rw [← h1]; nlinarith [mul_neg_of_pos_of_neg h2 hdetA]
    by_contra hcon
    push Not at hcon
    nlinarith [mul_nonneg hb.le hcon]
  obtain ⟨g, a', b', c', hg, ha, hb', hc, hprim⟩ := ex8_primitive hind0
  have hind' : a' * c' - b' ^ 2 < 0 := by
    by_contra hcon
    push Not at hcon
    have : a0 * c0 - β0 ^ 2 = g * g * (a' * c' - b' ^ 2) := by rw [ha, hb', hc]; ring
    nlinarith [mul_nonneg (mul_self_nonneg g) hcon]
  have haniso' : ¬ (cform a' b' c').IsotropicIn ℚ := by
    rintro ⟨x, hx0, hx⟩
    rw [evalIn_cform] at hx
    set y : Fin 3 → ℚ := fun i => x 0 * u i + x 1 * v i with hy
    have hCq : (C.map (Int.cast : ℤ → ℚ)) *ᵥ ![0, x 0, x 1] = y := by
      ext i; fin_cases i <;> simp [hC, hy, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0] at hCq
      have hdq : (C.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
        have := RingHom.map_det (Int.castRingHom ℚ) C
        rw [show C.map (Int.cast : ℤ → ℚ) = (Int.castRingHom ℚ).mapMatrix C from rfl, ← this]
        simpa using hdet
      have := Matrix.eq_zero_of_mulVec_eq_zero hdq hCq
      apply hx0
      ext i; fin_cases i
      · simpa using congrFun this 1
      · simpa using congrFun this 2
    apply haniso
    refine ⟨y, hy0, ?_⟩
    rw [ex8_evalIn hA]
    have hAq : (A.map (Int.cast : ℤ → ℚ)).IsSymm := hA.map _
    have e1 := ex8_cast_dot A u u
    have e2 := ex8_cast_dot A u v
    have e3 := ex8_cast_dot A v v
    have e4 := dot_mulVec_symm hAq (fun i => (u i : ℚ)) (fun i => (v i : ℚ))
    have hyv : y = x 0 • (fun i => (u i : ℚ)) + x 1 • (fun i => (v i : ℚ)) := by
      ext i; simp [hy]
    rw [hyv]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    rw [← e4]
    have hq : (a0 : ℚ) * x 0 ^ 2 + 2 * β0 * x 0 * x 1 + c0 * x 1 ^ 2 = 0 := by
      rw [ha, hb', hc]; push_cast
      linear_combination (g : ℚ) * hx
    rw [← e1, ← e2, ← e3]
    linear_combination hq
  obtain ⟨T₀, hT₀, hord, -⟩ := autPlus_cform_cyclic hprim hind' haniso'
  have hP' : Cᵀ * A * C = !![m, 0, 0; 0, g * a', g * b'; 0, g * b', g * c'] := by
    rw [hP, ← ha, ← hb', ← hc]
  have := ex8_construct hA C hdet m g a' b' c' hP' hT₀ hord
  rwa [hcol] at this

/-- **Example 8 (i)–(ii)**, assembled (see `example_8`). -/
theorem ex8_main {A : Matrix (Fin 3) (Fin 3) ℤ} (hA : A.IsSymm) {L : Matrix (Fin 3) (Fin 3) ℝ}
    (hL : IsUnit L.det) (hF : A.map (Int.cast : ℤ → ℝ) = Lᵀ * lorentz * L) (b : Fin 3 → ℤ) :
    (b ⬝ᵥ (A *ᵥ b) < 0 → {T | T ∈ Siegel.Aut (Siegel.ofGram A) ∧ T.val *ᵥ b = b}.Finite) ∧
    (¬ (Siegel.ofGram A).IsotropicIn ℚ → 0 < b ⬝ᵥ (A *ᵥ b) →
      {T | T ∈ Siegel.Aut (Siegel.ofGram A) ∧ T.val *ᵥ b = b}.Infinite) :=
  ⟨ex8_finite hA hL hF b, fun h1 h2 => ex8_infinite hA hL hF b h1 h2⟩

end QuadFormsKB.Reduction
