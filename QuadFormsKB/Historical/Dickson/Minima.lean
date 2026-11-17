/-
# Minima of positive definite forms: Hermite, Gauss–Seeber, Korkine–Zolotarev; unimodular forms of rank at most $7$

**Library** `QuadFormsKB.Historical.Dickson` (historical library, not imported by `QuadFormsKB`).  Targets
:

* (Dickson, *History* III (1923)), Hermite's inequality: a
  positive definite real form $f$ in $n + 1$ variables of determinant $D$ takes a value
  $f(x) \le (4/3)^{n/2} D^{1/(n+1)}$ at some nonzero integral $x$ (`hermite_inequality`, **wrapper** of
  `QuadFormsKB.Reduction.hermiteConstantBound_hermite`).
* (Dickson, *Studies* (1930), ch. XI), Seeber's inequality
  (first proved by Gauss): every positive ternary form of determinant $d$ is equivalent to one with $a \le b \le c$ and
  $abc \le 2d$ (`seeber_inequality`, from Cassels' Example 3 of Ch. 12, `QuadFormsKB.Reduction.example_3`, applied to a
  Minkowski-reduced form).
* (*Studies*): the minimum $m$ of a positive ternary form of
  determinant $d$ satisfies $m^3 \le 2d$, i.e. $m \le \sqrt[3]{2d}$ (`ternary_min_cube_le`), with equality for
  $x^2 + y^2 + z^2 + xy + xz + yz$ (`fccGram`, determinant $1/2$, minimum $1$: `fccGram_det`, `fccGram_min`).
* (*Studies*) and (*History* III,
  ), Korkine–Zolotarev (1872): the minimum $m$ of a positive quaternary form of
  determinant $d$ satisfies $m^4 \le 4d$, with equality for
  $x_0^2 + x_1^2 + x_2^2 + x_3^2 + x_0x_1 + x_0x_2 + x_0x_3$ (`d4Gram`, determinant $1/4$, minimum $1$). The bound is
  **stated** (`KorkineZolotarevQuaternary`, a named proposition, not assumed anywhere); the equality case is proved
  (`d4Gram_det`, `d4Gram_min`).
* (*History* III): for $n \le 7$ every positive definite
  classically integral $n$-ary form of determinant $1$ is equivalent to the sum of $n$ squares
  (`unimodular_le_seven`, **wrapper** of
  `QuadFormsKB.Lattices.Cassels.Ch11Unimodular.unimodular_posDef_equiv_one_le_seven`).

**Conventions.** A real form is given by its symmetric Gram matrix $F$, $f(x) = x^{\mathsf T}Fx$ (`Reduction.val`), and
its determinant is $\det F$ (Dickson's determinant of $ax^2 + by^2 + cz^2 + 2ryz + 2sxz + 2txy$). Equivalence is
$F \mapsto T^{\mathsf T}FT$ with $T \in \mathrm{GL}_n(\mathbb Z)$ (`Reduction.act`).
-/
import QuadFormsKB.Literature.Cassels.Ch12.Hermite
import QuadFormsKB.Literature.Cassels.Ch12.Examples
import QuadFormsKB.Literature.Cassels.Ch11Sec8Unimodular

namespace QuadFormsKB.Historical.Dickson

open Matrix QuadFormsKB.Reduction

/-! ### Hermite's inequality -/

private theorem pow_pos_of_ne_zero {x : ℝ} (hx : x ≠ 0) : 0 < x ^ 2 := by positivity

private theorem sum_sq_pos {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) : 0 < ∑ i, x i ^ 2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  exact lt_of_lt_of_le (pow_pos_of_ne_zero hi) (Finset.single_le_sum (f := fun j => x j ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i))

private theorem GL_mulVec_ne {n : ℕ} (T : GL (Fin n) ℤ) (v : Fin n → ℤ) (hv : v ≠ 0) :
    T.val *ᵥ v ≠ 0 := by
  intro h
  apply hv
  have := congrArg (fun w => ((T⁻¹ : GL (Fin n) ℤ).val) *ᵥ w) h
  simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this



/-- (Dickson, *History* III), **Hermite's
inequality**: for every positive definite real symmetric $(n+1) \times (n+1)$ matrix $F$ (the form
$f(x) = x^{\mathsf T}Fx$, determinant $D = \det F$) there is a nonzero $x \in \mathbb Z^{n+1}$ with
$f(x) \le (4/3)^{n/2} D^{1/(n+1)}$. **Wrapper** of `QuadFormsKB.Reduction.hermiteConstantBound_hermite`. -/
@[kb "dickson1923" "[unverified locator]"]
theorem hermite_inequality (n : ℕ) (F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hF : F.PosDef) :
    ∃ x : Fin (n + 1) → ℤ, x ≠ 0 ∧
      val F (cast x) ≤ (4 / 3 : ℝ) ^ ((n : ℝ) / 2) * F.det ^ ((1 : ℝ) / (n + 1 : ℕ)) := by
  have h := hermiteConstantBound_hermite (Nat.succ_pos n) F hF
  obtain ⟨m, hm, hle⟩ := h
  refine ⟨m, hm, ?_⟩
  have e : (((n + 1 : ℕ) : ℝ) - 1) = n := by push_cast; ring
  rw [e] at hle
  exact hle

/-! ### Ternary forms: Gauss–Seeber -/

/-- (Dickson, *Studies* (1930)), **Seeber's
inequality** (Gauss, 1831): every positive definite real ternary form $F$ of determinant $d = \det F$ is equivalent,
by some $T \in \mathrm{GL}_3(\mathbb Z)$, to a form $G = T^{\mathsf T}FT$ whose diagonal coefficients $a = G_{00}$,
$b = G_{11}$, $c = G_{22}$ satisfy $a \le b \le c$ and $abc \le 2d$. -/
@[kb "dickson1930" "[unverified locator]"]
theorem seeber_inequality (F : Matrix (Fin 3) (Fin 3) ℝ) (hF : F.PosDef) :
    ∃ T : GL (Fin 3) ℤ, (act T.val F) 0 0 ≤ (act T.val F) 1 1 ∧ (act T.val F) 1 1 ≤ (act T.val F) 2 2 ∧
      (act T.val F) 0 0 * (act T.val F) 1 1 * (act T.val F) 2 2 ≤ 2 * F.det := by
  obtain ⟨T, hT⟩ := exists_isMinkowskiReduced hF
  have h := example_3 hT
  rw [det_act] at h
  exact ⟨T, hT.diag_mono (by decide), hT.diag_mono (by decide), h⟩

/-- (Dickson, *Studies* (1930)), first part (Gauss):
a positive definite real ternary form $F$ of determinant $d$ takes a value $m = f(x)$ with $m^3 \le 2d$ at some
nonzero integral $x$, i.e. its minimum is at most $\sqrt[3]{2d}$ (Hermite's constant $\gamma_3^3 = 2$). -/
@[kb "dickson1930" "[unverified locator]"]
theorem ternary_min_cube_le (F : Matrix (Fin 3) (Fin 3) ℝ) (hF : F.PosDef) :
    ∃ x : Fin 3 → ℤ, x ≠ 0 ∧ val F (cast x) ^ 3 ≤ 2 * F.det := by
  obtain ⟨T, hT⟩ := exists_isMinkowskiReduced hF
  have h := example_3 hT
  rw [det_act] at h
  have h01 : (act T.val F) 0 0 ≤ (act T.val F) 1 1 := hT.diag_mono (by decide)
  have h12 : (act T.val F) 1 1 ≤ (act T.val F) 2 2 := hT.diag_mono (by decide)
  have hne : T.val *ᵥ (Pi.single 0 1 : Fin 3 → ℤ) ≠ 0 :=
    GL_mulVec_ne T _ (by intro h0; have := congrFun h0 0; simp at this)
  refine ⟨_, hne, ?_⟩
  have hd := act_diag T.val F 0
  rw [← hd]
  have hpos : 0 < (act T.val F) 0 0 := hT.1.diag_pos
  have h3 : (act T.val F) 0 0 ^ 3 ≤ (act T.val F) 0 0 * (act T.val F) 1 1 * (act T.val F) 2 2 := by
    have a : (act T.val F) 0 0 ≤ (act T.val F) 2 2 := h01.trans h12
    calc _ = (act T.val F) 0 0 * (act T.val F) 0 0 * (act T.val F) 0 0 := by ring
      _ ≤ _ := by
        gcongr
        all_goals nlinarith
  linarith

/-- The Gram matrix of $x_0^2 + x_1^2 + x_2^2 + x_0x_1 + x_0x_2 + x_1x_2$ (the face-centred cubic form): diagonal $1$,
off-diagonal $1/2$. -/
noncomputable def fccGram : Matrix (Fin 3) (Fin 3) ℝ := !![1, 1/2, 1/2; 1/2, 1, 1/2; 1/2, 1/2, 1]

/-- equality case: the form $x_0^2 + x_1^2 + x_2^2 + x_0x_1 + x_0x_2 + x_1x_2$ has
determinant $1/2$ (so $2d = 1$). -/
@[kb "dickson1930" "[unverified locator]"]
theorem fccGram_det : fccGram.det = 1 / 2 := by
  simp [fccGram, Matrix.det_fin_three]
  norm_num

/-- equality case: $x_0^2 + x_1^2 + x_2^2 + x_0x_1 + x_0x_2 + x_1x_2$ is positive
definite with minimum $1$ over nonzero integral vectors (attained at $e_0$), so $m^3 = 1 = 2d$. -/
@[kb "dickson1930" "[unverified locator]"]
theorem fccGram_min : fccGram.PosDef ∧ val fccGram (cast (Pi.single 0 1)) = 1 ∧
    ∀ x : Fin 3 → ℤ, x ≠ 0 → 1 ≤ val fccGram (cast x) := by
  have hq : ∀ x : Fin 3 → ℝ, val fccGram x = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 0 * x 1 + x 0 * x 2 + x 1 * x 2 := by
    intro x
    simp [val, fccGram, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [posDef_iff]
    refine ⟨?_, fun x hx => ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [fccGram]
    · have := sum_sq_pos x hx
      rw [hq]
      simp only [Fin.sum_univ_three] at this
      nlinarith [sq_nonneg (x 0 + x 1 + x 2)]
  · rw [cast_single, val_single]; simp [fccGram]
  · intro x hx
    have hx' : cast x ≠ 0 := by
      intro h; apply hx; funext i; have := congrFun h i; simpa using this
    have := sum_sq_pos (cast x) hx'
    rw [hq]
    simp only [Fin.sum_univ_three] at this
    have h1 : (0:ℤ) < x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 0 * x 1 + x 0 * x 2 + x 1 * x 2 := by
      have : (0:ℝ) < ((x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 : ℤ) : ℝ) := by push_cast; simpa using this
      have h2 : (0:ℤ) < x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by exact_mod_cast this
      nlinarith [sq_nonneg (x 0 + x 1 + x 2)]
    have : (1:ℤ) ≤ x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 0 * x 1 + x 0 * x 2 + x 1 * x 2 := h1
    exact_mod_cast this

/-! ### Quaternary forms: Korkine–Zolotarev -/

/-- (Dickson, *Studies* (1930)) and
(*History* III), **Korkine–Zolotarev's bound** (1872): every
positive definite real quaternary form $F$ of determinant $d$ takes a value $m = f(x)$ with $m^4 \le 4d$ at some
nonzero integral $x$ (Hermite's constant $\gamma_4 = \sqrt 2$). **Stated**, not proved (a named proposition, not used
as a hypothesis anywhere); see the loose end for the missing step. -/
@[kb "dickson1930" "[unverified locator]"]
def KorkineZolotarevQuaternary : Prop :=
  ∀ F : Matrix (Fin 4) (Fin 4) ℝ, F.PosDef → ∃ x : Fin 4 → ℤ, x ≠ 0 ∧ val F (cast x) ^ 4 ≤ 4 * F.det

/-- The Gram matrix of $x_0^2 + x_1^2 + x_2^2 + x_3^2 + x_0x_1 + x_0x_2 + x_0x_3$ (the $D_4$ form): diagonal $1$,
entries $(0, j)$ and $(j, 0)$ equal to $1/2$ for $j = 1, 2, 3$, the other entries $0$. -/
noncomputable def d4Gram : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 1/2, 1/2, 1/2; 1/2, 1, 0, 0; 1/2, 0, 1, 0; 1/2, 0, 0, 1]

/-- equality case: the $D_4$ form has determinant $1/4$ (so $4d = 1$). -/
@[kb "dickson1930" "[unverified locator]"]
theorem d4Gram_det : d4Gram.det = 1 / 4 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, d4Gram, Fin.succAbove]
  norm_num

/-- equality case: the $D_4$ form is positive definite with minimum $1$ over nonzero
integral vectors (attained at $e_0$), so $m^4 = 1 = 4d$ and the bound of `KorkineZolotarevQuaternary` is sharp. -/
@[kb "dickson1930" "[unverified locator]"]
theorem d4Gram_min : d4Gram.PosDef ∧ val d4Gram (cast (Pi.single 0 1)) = 1 ∧
    ∀ x : Fin 4 → ℤ, x ≠ 0 → 1 ≤ val d4Gram (cast x) := by
  have hq : ∀ x : Fin 4 → ℝ, val d4Gram x = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 +
      x 0 * (x 1 + x 2 + x 3) := by
    intro x
    simp [val, d4Gram, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    ring
  have key : ∀ x : Fin 4 → ℝ, (1/20) * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) ≤
      x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 0 * (x 1 + x 2 + x 3) := by
    intro x
    nlinarith [sq_nonneg (9/10 * x 0 + 5/9 * (x 1 + x 2 + x 3)), sq_nonneg (x 1 - x 2),
      sq_nonneg (x 1 - x 3), sq_nonneg (x 2 - x 3)]
  refine ⟨?_, ?_, ?_⟩
  · rw [posDef_iff]
    refine ⟨?_, fun x hx => ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [d4Gram]
    · have := sum_sq_pos x hx
      rw [hq]
      simp only [Fin.sum_univ_four] at this
      linarith [key x]
  · rw [cast_single, val_single]; simp [d4Gram]
  · intro x hx
    have hx' : cast x ≠ 0 := by
      intro h; apply hx; funext i; have := congrFun h i; simpa using this
    have := sum_sq_pos (cast x) hx'
    rw [hq]
    simp only [Fin.sum_univ_four] at this
    have k := key (cast x)
    have h1 : (0:ℤ) < x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 0 * (x 1 + x 2 + x 3) := by
      have h3 : (0:ℝ) < ((x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 0 * (x 1 + x 2 + x 3) : ℤ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast h3
    have : (1:ℤ) ≤ x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 0 * (x 1 + x 2 + x 3) := h1
    exact_mod_cast this

/-! ### Unimodular forms of rank at most 7 -/

/-- (Dickson, *History* III): for $n \le 7$ every
positive definite classically integral form in $n$ variables (integral symmetric Gram matrix $A$) of determinant $1$
is equivalent to the sum of $n$ squares: $g^{\mathsf T}Ag = I$ for some $g \in \mathrm{GL}_n(\mathbb Z)$. **Wrapper** of
`QuadFormsKB.Lattices.Cassels.Ch11Unimodular.unimodular_posDef_equiv_one_le_seven`. -/
@[kb "dickson1923" "[unverified locator]"]
theorem unimodular_le_seven {n : ℕ} (hn : n ≤ 7) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : Siegel.Hermite.IsPosDefInt A) (hd : A.det = 1) :
    ∃ g : GL (Fin n) ℤ, g.valᵀ * A * g.val = 1 :=
  QuadFormsKB.Lattices.Cassels.Ch11Unimodular.unimodular_posDef_equiv_one_le_seven hn A hA hd

end QuadFormsKB.Historical.Dickson
