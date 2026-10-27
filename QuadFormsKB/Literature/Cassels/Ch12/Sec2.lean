/-
# Cassels, Chapter 12, §2: Theorem 2.1 (Hermite's constant)

Cassels, *Rational Quadratic Forms* (1978), Ch. 12, §2, pp. 260–261.

* Theorem 2.1 (`exists_val_le_det_rpow`): $\min_{\vec{m} \ne 0} f(\vec{m}) \le \gamma_n D^{1/n}$ with $\gamma_n = n$,
  from Minkowski's convex body theorem (Mathlib's
  `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure`) applied to a box adapted to the
  completed squares (`IsSqDecomp`), not to the ellipsoid of Cassels' proof (ii); and the best value $2/\sqrt3$ for
  $n = 2$ (`binary_min_le`, `binary_min_eq`).
* `HermiteConstantBound n γ`: "$\gamma$ satisfies Theorem 2.1 in dimension $n$", the hypothesis of Theorem 2.2.

The successive minima, Lemma 2.1 and Theorem 2.2 are in `Sec2Minima.lean`.
-/
import QuadFormsKB.Literature.Cassels.Ch12.Sec1

open Matrix

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-- **Minkowski's convex body theorem for $\mathbb{Z}^n$** (Cassels, Ch. 5, Thm. 2.4 note, p. 71, used in Ch. 12, proof
(ii) of Thm. 2.1, p. 261): a compact convex subset of $\mathbb{R}^n$, symmetric about $0$, of volume $\ge 2^n$ contains a
nonzero integral point. (A specialization of Mathlib's
`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure` to the lattice $\mathbb{Z}^n$.) -/
theorem exists_int_mem_of_volume_ge {s : Set (Fin n → ℝ)} (hn : 0 < n) (hsymm : ∀ x ∈ s, -x ∈ s)
    (hconv : Convex ℝ s) (hcpt : IsCompact s) (hvol : (2 : ENNReal) ^ n ≤ MeasureTheory.volume s) :
    ∃ m : Fin n → ℤ, m ≠ 0 ∧ cast m ∈ s := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : Nontrivial (Fin n → ℝ) := inferInstance
  have : Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))))
  have fund := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin n)) (MeasureTheory.volume)
  have hvolF : MeasureTheory.volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin n))) = 1 := by
    rw [ZSpan.volume_fundamentalDomain]
    have : Matrix.of (⇑(Pi.basisFun ℝ (Fin n))) = 1 := by
      ext i j
      simp [Pi.single_apply, Matrix.one_apply, eq_comm]
    rw [this]
    simp
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    fund hsymm hconv hcpt (by simpa [hvolF] using hvol)
  have hint : ∀ i, ∃ z : ℤ, (z : ℝ) = (x : Fin n → ℝ) i := fun i => by
    have := ((Pi.basisFun ℝ (Fin n)).mem_span_iff_repr_mem ℤ (x : Fin n → ℝ)).mp x.2 i
    obtain ⟨z, hz⟩ := this
    exact ⟨z, by simpa using hz⟩
  choose m hm using hint
  refine ⟨m, ?_, ?_⟩
  · intro h0
    apply hx0
    apply Subtype.ext
    funext i
    rw [← hm i, h0]
    simp
  · have : cast m = (x : Fin n → ℝ) := funext fun i => hm i
    rw [this]; exact hxs

/-- **Theorem 2.1** (Cassels, Ch. 12, §2, p. 260): there is a constant $\gamma_n$ (here $\gamma_n = n$) such that every
strictly positive definite real form in $n \ge 1$ variables, of determinant $D = d(f) = \det F$, takes a value
$$f(\vec{m}) \le \gamma_n D^{1/n}$$
at some nonzero integral $\vec{m}$; that is, $M_0 \le \gamma_n D^{1/n}$. *Proof:* write $f = \sum_j h_j L_j(\vec{x})^2$
(`IsSqDecomp`); the box $\{|L_j(\vec{x})| \le (D^{1/n}/h_j)^{1/2}\}$ is convex, symmetric, of volume $2^n$
(the $L_j$ have determinant $1$ and $\prod h_j = D$), so it contains a nonzero integral $\vec{m}$ (Minkowski), and
$f(\vec{m}) \le \sum_j h_j\cdot D^{1/n}/h_j = nD^{1/n}$. Cassels' proof (ii) uses the ellipsoid $f \le M$ and gets
$\gamma_n = 4K_n^{-2/n}$; his proof (i) (Hermite) gets $(4/3)^{(n-1)/2}$; the statement only asserts that some
$\gamma_n$ exists. -/
@[kb "cassels1978" "Ch. 12, §2, Thm. 2.1, p. 260, proof (ii), p. 261 (with a box, γ_n = n)"]
theorem exists_val_le_det_rpow {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) (hn : 0 < n) :
    ∃ m : Fin n → ℤ, m ≠ 0 ∧ val F (cast m) ≤ n * F.det ^ ((1 : ℝ) / n) := by
  obtain ⟨h, C, hd, hpos⟩ := exists_isSqDecomp hF
  have hdetC : C.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun i j hij => hd.1 i j hij)]
    simp [hd.2.1]
  have hD : F.det = ∏ i, h i := hd.det_eq
  have hDpos : 0 < F.det := by rw [hD]; exact Finset.prod_pos fun i _ => hpos i
  set a : ℝ := F.det ^ ((1 : ℝ) / n) with ha
  have hapos : 0 < a := Real.rpow_pos_of_pos hDpos _
  have han : a ^ n = F.det := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hDpos.le]
    have : (1 : ℝ) / n * n = 1 := by
      have : (n : ℝ) ≠ 0 := by positivity
      field_simp
    rw [this, Real.rpow_one]
  set r : Fin n → ℝ := fun i => Real.sqrt (a / h i) with hr
  have hrpos : ∀ i, 0 < r i := fun i => Real.sqrt_pos.2 (div_pos hapos (hpos i))
  have hr2 : ∀ i, r i ^ 2 = a / h i := fun i => Real.sq_sqrt (div_pos hapos (hpos i)).le
  have hprod : ∏ i, r i = 1 := by
    have h1 : (∏ i, r i) ^ 2 = 1 := by
      rw [← Finset.prod_pow]
      simp_rw [hr2]
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, han, hD,
        div_self (by rw [← hD]; exact hDpos.ne')]
    have h0 : 0 < ∏ i, r i := Finset.prod_pos fun i _ => hrpos i
    nlinarith
  set box : Set (Fin n → ℝ) := Set.Icc (fun i => -r i) r with hbox
  set f : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Matrix.toLin' C⁻¹ with hf
  set S : Set (Fin n → ℝ) := f '' box with hS
  have hCinv : ∀ y, C *ᵥ (C⁻¹ *ᵥ y) = y := by
    intro y
    have hU : IsUnit C.det := by rw [hdetC]; exact isUnit_one
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]
  have hvol : MeasureTheory.volume S = 2 ^ n := by
    rw [hS, MeasureTheory.Measure.addHaar_image_linearMap, hbox, Real.volume_Icc_pi]
    have hdf : LinearMap.det f = 1 := by
      rw [hf, LinearMap.det_toLin', Matrix.det_nonsing_inv, hdetC]; simp
    rw [hdf]
    simp only [abs_one, ENNReal.ofReal_one, one_mul]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by linarith [hrpos i])]
    have : ∏ i, (r i - -r i) = 2 ^ n := by
      have : ∀ i, r i - -r i = 2 * r i := fun i => by ring
      simp_rw [this]
      rw [Finset.prod_mul_distrib, hprod]; simp
    rw [this]
    rw [ENNReal.ofReal_pow (by norm_num)]
    simp
  have hn' : 0 < n := hn
  obtain ⟨m, hm0, hmS⟩ := exists_int_mem_of_volume_ge (s := S) hn'
    (by
      rintro x ⟨y, hy, rfl⟩
      refine ⟨-y, ⟨?_, ?_⟩, by rw [map_neg]⟩ <;> intro i <;> simp <;>
        linarith [(hy.1 i), (hy.2 i), show (-y) i = - y i from rfl])
    ((convex_Icc _ _).linear_image f)
    (isCompact_Icc.image (LinearMap.continuous_of_finiteDimensional f))
    hvol.ge
  refine ⟨m, hm0, ?_⟩
  obtain ⟨y, hy, hyx⟩ := hmS
  have hCm : C *ᵥ cast m = y := by
    rw [← hyx, hf, Matrix.toLin'_apply, hCinv]
  rw [val_eq_of_isSqDecomp hd, hCm]
  calc ∑ i, h i * y i ^ 2 ≤ ∑ _i : Fin n, a := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 : y i ^ 2 ≤ r i ^ 2 := by
          apply sq_le_sq'
          · linarith [hy.1 i]
          · exact hy.2 i
        calc h i * y i ^ 2 ≤ h i * r i ^ 2 := by gcongr; exact (hpos i).le
          _ = a := by rw [hr2]; field_simp [(hpos i).ne']
    _ = n * a := by simp

/-- **The property "$\gamma$ satisfies Theorem 2.1 in dimension $n$"**: every strictly positive definite real form $f$ in
$n$ variables takes a value $f(\vec{m}) \le \gamma\,(\det F)^{1/n}$ at a nonzero integral $\vec{m}$. Cassels,
Ch. 12, Thm. 2.1, p. 260 ("there is a constant $\gamma_n$"); Thm. 2.2 holds for every such $\gamma$. By
Theorem 2.1, $\gamma = n$ qualifies for $n \ge 1$ (`hermiteConstantBound_n`). -/
@[kb "cassels1978" "Ch. 12, §2, Thm. 2.1, p. 260 (a constant γ_n)"]
def HermiteConstantBound (n : ℕ) (γ : ℝ) : Prop :=
  ∀ F : Matrix (Fin n) (Fin n) ℝ, F.PosDef → ∃ m : Fin n → ℤ, m ≠ 0 ∧ val F (cast m) ≤ γ * F.det ^ ((1 : ℝ) / n)

theorem hermiteConstantBound_n (hn : 0 < n) : HermiteConstantBound n n :=
  fun _ hF => exists_val_le_det_rpow hF hn

/-- **The best value of $\gamma_2$, the inequality** (Cassels, Ch. 12, §2, p. 261): a strictly positive definite binary
form has $M_0 \le (2/\sqrt3)\,D^{1/2}$. *Proof:* for a reduced form $f_{00} \le f_{11}$ and $|2f_{01}| \le f_{00}$
(Lemma 1.1), so $D = f_{00}f_{11} - f_{01}^2 \ge \tfrac34 f_{00}^2$. -/
@[kb "cassels1978" "Ch. 12, §2, p. 261 (best value 2/√3 of γ_2)"]
theorem binary_min_le {F : Matrix (Fin 2) (Fin 2) ℝ} (hF : F.PosDef) :
    ∃ m : Fin 2 → ℤ, m ≠ 0 ∧ val F (cast m) ≤ 2 / Real.sqrt 3 * F.det ^ ((1 : ℝ) / 2) := by
  obtain ⟨T, hT⟩ := exists_isMinkowskiReduced hF
  have hG := QuadFormsKB.Reduction.PosDef.act hF T
  set G := act T.val F with hGdef
  have hdetG : G.det = F.det := det_act T F
  have hGs : G.IsSymm := ((posDef_iff G).1 hG).1
  have hG10 : G 1 0 = G 0 1 := by
    have := congrFun (congrFun hGs 0) 1
    simpa [Matrix.transpose_apply] using this
  have hpos : 0 < G 0 0 := by
    have := ((posDef_iff G).1 hG).2 (Pi.single 0 1) (by
      intro h; have := congrFun h 0; simp at this)
    rwa [val_single] at this
  have h1 : G 0 0 ≤ G 1 1 := hT.diag_mono (by decide : (0 : Fin 2) ≤ 1)
  have h2 : |2 * G 0 1| ≤ G 0 0 := hT.abs_two_mul_le (by decide : (0 : Fin 2) < 1)
  have h3 : (2 * G 0 1) ^ 2 ≤ G 0 0 ^ 2 := by
    have := sq_le_sq' (abs_le.1 h2).1 (abs_le.1 h2).2
    exact this
  have hD : G.det = G 0 0 * G 1 1 - G 0 1 ^ 2 := by
    rw [Matrix.det_fin_two, hG10]; ring
  have hD2 : 3 / 4 * G 0 0 ^ 2 ≤ F.det := by
    rw [← hdetG, hD]; nlinarith
  refine ⟨T.val *ᵥ Pi.single 0 1, ?_, ?_⟩
  · intro h
    have h' := congrArg (fun v => (T⁻¹).val *ᵥ v) h
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at h'
    have := congrFun h' 0
    simp at this
  · have hc : cast ((T.val *ᵥ Pi.single 0 1 : Fin 2 → ℤ)) = castM T.val *ᵥ Pi.single 0 1 := by
      rw [← castM_mulVec_cast]
      congr 1
      funext i
      fin_cases i <;> simp
    rw [hc, ← val_act, val_single]
    have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hs0 : 0 < Real.sqrt 3 := by positivity
    have hle : Real.sqrt 3 / 2 * G 0 0 ≤ Real.sqrt F.det := by
      apply Real.le_sqrt_of_sq_le
      nlinarith
    rw [← Real.sqrt_eq_rpow]
    calc G 0 0 = 2 / Real.sqrt 3 * (Real.sqrt 3 / 2 * G 0 0) := by field_simp
      _ ≤ _ := by gcongr

/-- **The best value of $\gamma_2$, equality** (Cassels, Ch. 12, §2, p. 261): for $x_0^2 + x_0x_1 + x_1^2$ (matrix
$\begin{pmatrix}1 & 1/2\\ 1/2 & 1\end{pmatrix}$, $D = 3/4$) every nonzero integral value is
$\ge 1 = (2/\sqrt3)\,D^{1/2}$, so $2/\sqrt3$ cannot be lowered. -/
@[kb "cassels1978" "Ch. 12, §2, p. 261 (equality for x² + xy + y²)"]
theorem binary_min_eq :
    let F : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1 / 2; 1 / 2, 1]
    F.PosDef ∧ 2 / Real.sqrt 3 * F.det ^ ((1 : ℝ) / 2) = 1 ∧
      ∀ m : Fin 2 → ℤ, m ≠ 0 → 1 ≤ val F (cast m) := by
  intro F
  have hval : ∀ x : Fin 2 → ℝ, val F x = x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2 := by
    intro x
    simp [F, val, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    ring
  have hdet : F.det = 3 / 4 := by
    simp [F, Matrix.det_fin_two]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [posDef_iff]
    refine ⟨?_, fun x hx => ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [F]
    · rw [hval]
      by_cases h1 : x 1 = 0
      · have h0 : x 0 ≠ 0 := by
          intro h0; apply hx; ext i; fin_cases i <;> simp [h0, h1]
        rw [h1]; have := sq_pos_of_ne_zero h0; nlinarith
      · nlinarith [sq_nonneg (2 * x 0 + x 1), sq_pos_of_ne_zero h1]
  · rw [hdet, ← Real.sqrt_eq_rpow]
    have h3 : Real.sqrt (3 / 4) = Real.sqrt 3 / 2 := by
      rw [show (3 / 4 : ℝ) = 3 / 2 ^ 2 by norm_num, Real.sqrt_div (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [h3]
    have : Real.sqrt 3 ≠ 0 := by positivity
    field_simp
  · intro m hm
    have hint : (1 : ℤ) ≤ m 0 ^ 2 + m 0 * m 1 + m 1 ^ 2 := by
      by_cases h1 : m 1 = 0
      · have h0 : m 0 ≠ 0 := by
          intro h0; apply hm; ext i; fin_cases i <;> simp [h0, h1]
        rw [h1]; nlinarith [sq_pos_of_ne_zero h0]
      · nlinarith [sq_nonneg (2 * m 0 + m 1), sq_pos_of_ne_zero h1]
    rw [hval]
    exact_mod_cast hint

end QuadFormsKB.Reduction
