/-
# Cassels, Chapter 13, §4: construction of automorphs

Formalization of Cassels, *Rational Quadratic Forms* (1978), Ch. 13, §4, *Construction of automorphs*, pp. 298–300:
integral symmetries (p. 298), automorphs fixing a vector $\vec{e}$ with $f(\vec{e}) \ne 0$ (Theorem 4.1) and with
$f(\vec{e}) = 0$ (Theorem 4.2), and the commensurability of the integral automorph groups of rationally equivalent
forms (Lemma 4.1).

**Conventions.** In Theorems 4.1 and 4.2 the form is classically integral, $f(\vec{x}) = \vec{x}^{\mathsf T}A\vec{x}$ with
$A$ a symmetric integer matrix (Cassels' $(f_{ij})$), i.e. the library form `Siegel.ofGram A`; its group of
integral automorphs $O(f)$ is `Siegel.Aut (Siegel.ofGram A)`. Indices are 0-based: Cassels' $\vec{e}_1$ and
$f_{11}, f_{12}$ are $\vec{e}_0$ and `A 0 0`, `A 0 1` here; his variables $x_2, \dots, x_n$ of the form $g$ are
$x_1, \dots, x_n$ of a form in $n + 1$ variables, re-indexed $0, \dots, n - 1$ (`Fin.succ`).
-/
import QuadFormsKB.Literature.Cassels.Ch13.Basic
import QuadFormsKB.Literature.Cassels.Ch9Sec6Weight
import QuadFormsKB.Lattices.CartanDieudonne

open Matrix

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-! ### Helper lemmas -/

/-- Membership in `Aut (ofGram A)` in matrix form: $T^{\mathsf T}AT = A$. -/
theorem mem_aut_ofGram_iff {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) (T : GL (Fin n) ℤ) :
    T ∈ Siegel.Aut (Siegel.ofGram A) ↔ T.valᵀ * A * T.val = A := by
  have h := Siegel.eval_mulVec_eq_iff_hessian (Siegel.ofGram A) (Siegel.ofGram A) T.val
  rw [Siegel.hessian_ofGram, hA.eq] at h
  show (∀ x, _) ↔ _
  rw [h]
  constructor
  · intro h
    ext i j
    have := congr_fun (congr_fun h i) j
    simp only [Matrix.add_apply, Matrix.mul_add, Matrix.add_mul] at this
    linarith
  · intro h
    rw [Matrix.mul_add, Matrix.add_mul, h]

/-- A subgroup containing all elements of `G` congruent to `1` modulo a nonzero `m` has finite index in `G`. -/
theorem finiteIndex_subgroupOf_of_cong (G H : Subgroup (GL (Fin n) ℤ)) {m : ℕ} (hm : m ≠ 0)
    (h : ∀ S ∈ G, (∀ i j, (m : ℤ) ∣ (S.val - 1) i j) → S ∈ H) : (H.subgroupOf G).FiniteIndex := by
  haveI : NeZero m := ⟨hm⟩
  let φ : GL (Fin n) ℤ →* GL (Fin n) (ZMod m) := Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod m))
  haveI : (MonoidHom.ker φ).FiniteIndex := Subgroup.finiteIndex_ker φ
  haveI : ((MonoidHom.ker φ).subgroupOf G).FiniteIndex := inferInstance
  refine @Subgroup.finiteIndex_of_le _ _ _ _ ‹_› ?_
  intro S hS
  show (S : GL (Fin n) ℤ) ∈ H
  refine h S S.2 fun i j => ?_
  have h1 : φ S = 1 := hS
  have h2 := congrArg (fun g : GL (Fin n) (ZMod m) => (g.val : Matrix (Fin n) (Fin n) (ZMod m)) i j) h1
  simp only [φ, Matrix.GeneralLinearGroup.map_apply] at h2
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  by_cases hij : i = j <;> simp_all [Matrix.one_apply]

/-- Column $0$ of a matrix is $\vec e_0$ iff the matrix fixes $\vec e_0$. -/
theorem mulVec_single_zero_iff {m : ℕ} (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) :
    M *ᵥ Pi.single 0 1 = Pi.single 0 1 ↔ M 0 0 = 1 ∧ ∀ i : Fin m, M i.succ 0 = 0 := by
  constructor
  · intro h
    have h' : ∀ i, M i 0 = (Pi.single 0 1 : Fin (m + 1) → ℤ) i := fun i => by
      have := congr_fun h i
      simpa [mulVec, dotProduct, Pi.single_apply] using this
    exact ⟨by simpa using h' 0, fun i => by simpa [Fin.succ_ne_zero] using h' i.succ⟩
  · rintro ⟨h0, h1⟩
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [mulVec, dotProduct, Pi.single_apply] using h0
    · simpa [mulVec, dotProduct, Pi.single_apply, Fin.succ_ne_zero] using h1 i

/-- Determinant of a matrix with first column $\vec e_0$-like (zero below the corner). -/
theorem det_eq_of_col_zero {m : ℕ} (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (h : ∀ i : Fin m, M i.succ 0 = 0) :
    M.det = M 0 0 * (M.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h, Fin.succAbove_zero]

/-- The lower-right block of a product, when the left factor has first column zero below the corner. -/
theorem submatrix_succ_mul {m : ℕ} (M N : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (h : ∀ i : Fin m, M i.succ 0 = 0) :
    (M * N).submatrix Fin.succ Fin.succ = M.submatrix Fin.succ Fin.succ * N.submatrix Fin.succ Fin.succ := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_succ, h]

/-- Invariance of the pairing under an automorph. -/
theorem dot_aut {A T : Matrix (Fin n) (Fin n) ℤ} (hT : Tᵀ * A * T = A) (u v : Fin n → ℤ) :
    (T *ᵥ u) ⬝ᵥ (A *ᵥ (T *ᵥ v)) = u ⬝ᵥ (A *ᵥ v) := by
  conv_rhs => rw [← hT]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec u Tᵀ, vecMul_transpose]


/-- Square-one criterion for a reflection matrix. -/
theorem reflMat_mul_self {x w : Fin n → ℤ} (hw : w ⬝ᵥ x = 2) :
    QuadForm.reflMat x w * QuadForm.reflMat x w = 1 := by
  refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
  simp only [Matrix.toLin'_apply, ← mulVec_mulVec, QuadForm.reflMat_mulVec, one_mulVec]
  rw [dotProduct_sub, dotProduct_smul, hw, smul_eq_mul, sub_sub, ← add_smul]
  ring_nf

/-! ### Integral symmetries (p. 298) -/

-- 13.r4: the rational automorphs are generated by symmetries (Cartan–Dieudonné), recalled from Ch. 2, §4
attribute [kb "cassels1978" "Ch. 13, §4, (4.1), p. 298 (rational automorphs generated by the symmetries τ_a)"]
  Lattices.exists_symmProd_eq

/-- **Integral symmetries** (Cassels, Ch. 13, §4, (4.1), p. 298): the rational automorphs of $f$ are generated by the
symmetries
$$\tau_{\vec{a}}: \vec{x} \mapsto \vec{x} - \frac{2B(\vec{a}, \vec{x})}{f(\vec{a})}\vec{a} \qquad (f(\vec{a}) \ne 0)$$
(Cartan–Dieudonné, `Lattices.exists_symmProd_eq`); the symmetry $\tau_{\vec{a}}$ is integral if $f$ is classically
integral, $\vec{a}$ is integral and $f(\vec{a}) = \pm 1$ or $\pm 2$. Here: for a symmetric integer matrix $A$ and
$\vec{a} \in \mathbb{Z}^n$ with $\vec{a}^{\mathsf T}A\vec{a} \in \{\pm1, \pm2\}$, the rational symmetry
`Lattices.symm` of $f$ in $\vec{a}$ is (the image of) an integral automorph of $f$. -/
@[kb "cassels1978" "Ch. 13, §4, (4.1), p. 298 (τ_a is integral when f(a) = ±1, ±2)"]
theorem exists_aut_eq_symm {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) {a : Fin n → ℤ}
    (ha : a ⬝ᵥ (A *ᵥ a) = 1 ∨ a ⬝ᵥ (A *ᵥ a) = -1 ∨ a ⬝ᵥ (A *ᵥ a) = 2 ∨ a ⬝ᵥ (A *ᵥ a) = -2) :
    ∃ T ∈ Siegel.Aut (Siegel.ofGram A),
      T.val.map (Int.cast : ℤ → ℚ) =
        ((Lattices.symm ((Siegel.ofGram A).map (Int.castRingHom ℚ)) ℚ (fun i => (a i : ℚ)) :
          GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) := by
  obtain ⟨d, hd⟩ : ∃ d : ℤ, d * (a ⬝ᵥ (A *ᵥ a)) = 2 := by
    rcases ha with h | h | h | h
    · exact ⟨2, by rw [h]; norm_num⟩
    · exact ⟨-2, by rw [h]; norm_num⟩
    · exact ⟨1, by rw [h]; norm_num⟩
    · exact ⟨-1, by rw [h]; norm_num⟩
  set c := a ⬝ᵥ (A *ᵥ a) with hc
  set w : Fin n → ℤ := d • (A *ᵥ a) with hw
  have hw2 : w ⬝ᵥ a = 2 := by
    rw [hw, smul_dotProduct, dotProduct_comm, smul_eq_mul, hd]
  have hev : (Siegel.ofGram A).eval a = c := Siegel.eval_ofGram hA a
  have hH : (Siegel.ofGram A).hessian *ᵥ a = (Siegel.ofGram A).eval a • w := by
    rw [Siegel.hessian_ofGram, hA.eq, hev, hw, smul_smul, mul_comm, hd, add_mulVec, two_smul]
  have hsq := reflMat_mul_self hw2
  refine ⟨⟨QuadForm.reflMat a w, QuadForm.reflMat a w, hsq, hsq⟩, ?_, ?_⟩
  · intro x
    exact QuadForm.eval_reflMat _ hH x
  · have hev' : (((Siegel.ofGram A).map (Int.castRingHom ℚ)).evalIn ℚ (fun i => (a i : ℚ))) = (c : ℚ) := by
      have h2 := QuadForm.dotProduct_hessian_self ((Siegel.ofGram A).map (Int.castRingHom ℚ))
        (fun i => (a i : ℚ))
      rw [QuadForm.hessian_map, Siegel.hessian_ofGram, hA.eq] at h2
      have h3 : (fun i => (a i : ℚ)) ⬝ᵥ ((A + A).map (Int.castRingHom ℚ) *ᵥ (fun i => (a i : ℚ))) =
          ((a ⬝ᵥ ((A + A) *ᵥ a) : ℤ) : ℚ) := by
        simp [dotProduct, mulVec, Matrix.map_apply]
      rw [h3, add_mulVec, dotProduct_add, ← hc] at h2
      have h4 : ((c + c : ℤ) : ℚ) = 2 * ((Siegel.ofGram A).map (Int.castRingHom ℚ)).eval (fun i => (a i : ℚ)) := h2
      push_cast at h4
      show ((Siegel.ofGram A).map (Int.castRingHom ℚ)).eval _ = _
      linarith
    have hx : ((Siegel.ofGram A).map (Int.castRingHom ℚ)).evalIn ℚ (fun i => (a i : ℚ)) ≠ 0 := by
      rw [hev']; rcases ha with h | h | h | h <;> rw [h] <;> norm_num
    rw [Lattices.symm_val _ _ hx]
    have hcq : (c : ℚ) ≠ 0 := by rw [← hev']; exact hx
    have hdq : (d : ℚ) * c = 2 := by exact_mod_cast hd
    have hsv : Lattices.symmVec ((Siegel.ofGram A).map (Int.castRingHom ℚ)) ℚ (fun i => (a i : ℚ)) =
        fun i => (w i : ℚ) := by
      ext i
      rw [Lattices.symmVec, hev']
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [QuadForm.hessian_map, Siegel.hessian_ofGram, hA.eq]
      simp only [hw, Pi.smul_apply, smul_eq_mul, Int.cast_mul]
      have h5 : (((A + A).map (Int.castRingHom ℚ)).map (algebraMap ℚ ℚ) *ᵥ fun i => (a i : ℚ)) i =
          2 * ((A *ᵥ a) i : ℤ) := by
        simp [mulVec, dotProduct, Matrix.map_apply, add_mul, Finset.sum_add_distrib]
        ring
      rw [h5]
      field_simp
      linear_combination (-(((A *ᵥ a) i : ℤ) : ℚ)) * hdq
    rw [hsv]
    ext i j
    by_cases h : i = j <;> simp [QuadForm.reflMat, vecMulVec_apply, h]


/-! ### Automorphs fixing a vector $\vec{e}$ with $f(\vec{e}) \ne 0$: Theorem 4.1 (p. 299) -/

/-- **Completing the square** (Cassels, Ch. 13, §4, (4.4), p. 299): the matrix of the integral form $g$ in the
variables $x_1, \dots, x_n$ with $f_{00}f(\vec{x}) = (f_{00}x_0 + f_{01}x_1 + \cdots + f_{0n}x_n)^2 + g(x_1, \dots, x_n)$:
$g_{ij} = f_{00}f_{ij} - f_{0i}f_{0j}$ ($1 \le i, j \le n$, re-indexed from $0$).

Equivalent to `Cassels.Ch13.complForm` (the values of the same form $g$), which carries the tag of the definition. -/
def complSq (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => A 0 0 * A i.succ j.succ - A 0 i.succ * A 0 j.succ

/-- **(4.4)** (Cassels, Ch. 13, §4, p. 299): $f_{00}f(\vec{x}) = (\sum_j f_{0j}x_j)^2 + g(x_1, \dots, x_n)$. -/
@[kb "cassels1978" "Ch. 13, §4, (4.4), p. 299"]
theorem complSq_spec {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ} (hA : A.IsSymm) (x : Fin (n + 1) → ℤ) :
    A 0 0 * (x ⬝ᵥ (A *ᵥ x)) = (∑ j, A 0 j * x j) ^ 2 + Fin.tail x ⬝ᵥ (complSq A *ᵥ Fin.tail x) := by
  have hs : ∀ i : Fin n, A i.succ 0 = A 0 i.succ := fun i => by
    have := congr_fun (congr_fun hA 0) i.succ
    simpa using this
  set y : Fin n → ℤ := Fin.tail x with hy
  have hx : ∀ i : Fin n, x i.succ = y i := fun i => rfl
  simp only [dotProduct, mulVec, Fin.sum_univ_succ, complSq, Matrix.of_apply, hs, hx, ← hy]
  simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib, add_mul, sq, Finset.sum_mul,
    Finset.mul_sum, mul_add]
  have d1 : ∑ x : Fin n, ∑ i : Fin n, y x * ((A 0 0 * A x.succ i.succ - A 0 x.succ * A 0 i.succ) * y i) =
      ∑ x : Fin n, ∑ i : Fin n, A 0 0 * (y x * (A x.succ i.succ * y i)) -
        ∑ x : Fin n, ∑ i : Fin n, A 0 i.succ * y i * (A 0 x.succ * y x) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have c1 : ∑ i : Fin n, A 0 0 * (y i * (A 0 i.succ * x 0)) = ∑ i : Fin n, A 0 i.succ * y i * (A 0 0 * x 0) :=
    Finset.sum_congr rfl fun _ _ => by ring
  have c2 : ∑ i : Fin n, A 0 0 * (x 0 * (A 0 i.succ * y i)) = ∑ i : Fin n, A 0 0 * x 0 * (A 0 i.succ * y i) :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [d1]
  linarith

/-- The form $g$ of (4.4) has symmetric matrix. -/
theorem complSq_isSymm {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ} (hA : A.IsSymm) : (complSq A).IsSymm := by
  ext i j
  have := congr_fun (congr_fun hA i.succ) j.succ
  have h2 := congr_fun (congr_fun hA 0) 0
  simp only [complSq, Matrix.transpose_apply, Matrix.of_apply]
  rw [show A j.succ i.succ = A i.succ j.succ from by simpa using this]
  ring

/-- (4.4) in terms of `mulVec`. -/
theorem spec_vec {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ} (hA : A.IsSymm) (x : Fin (n + 1) → ℤ) :
    A 0 0 * (x ⬝ᵥ (A *ᵥ x)) = ((A *ᵥ x) 0) ^ 2 + Fin.tail x ⬝ᵥ (complSq A *ᵥ Fin.tail x) := by
  rw [complSq_spec hA x]
  rfl

/-- The restriction of an automorph fixing $\vec e_0$ is an automorph of $g$ (as a matrix identity). -/
theorem sub_eval {A T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ} (hA : A.IsSymm) (h00 : A 0 0 ≠ 0)
    (hT : Tᵀ * A * T = A) (hT0 : T *ᵥ Pi.single 0 1 = Pi.single 0 1) (y : Fin n → ℤ) :
    (Siegel.ofGram (complSq A)).eval (T.submatrix Fin.succ Fin.succ *ᵥ y) =
      (Siegel.ofGram (complSq A)).eval y := by
  obtain ⟨h0, h1⟩ := (mulVec_single_zero_iff T).1 hT0
  set x : Fin (n + 1) → ℤ := Fin.cons 0 y with hxdef
  have htail : Fin.tail (T *ᵥ x) = T.submatrix Fin.succ Fin.succ *ᵥ y := by
    ext i
    simp [Fin.tail, mulVec, dotProduct, Fin.sum_univ_succ, h1, x]
  have hxt : Fin.tail x = y := Fin.tail_cons _ _
  have hc : (A *ᵥ (T *ᵥ x)) 0 = (A *ᵥ x) 0 := by
    have := dot_aut hT (Pi.single 0 1) x
    rw [hT0] at this
    simpa [dotProduct, Pi.single_apply] using this
  have hf : (T *ᵥ x) ⬝ᵥ (A *ᵥ (T *ᵥ x)) = x ⬝ᵥ (A *ᵥ x) := dot_aut hT x x
  have s1 := spec_vec hA (T *ᵥ x)
  have s2 := spec_vec hA x
  rw [hc, hf, htail] at s1
  rw [hxt] at s2
  rw [Siegel.eval_ofGram (complSq_isSymm hA), Siegel.eval_ofGram (complSq_isSymm hA)]
  linarith

/-- Lifting (4.5): an automorph $S$ of $g$ with $S \equiv I \pmod{f_{00}}$ extends to an automorph of $f$ fixing
$\vec e_0$. -/
theorem lift_exists {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ} (hA : A.IsSymm) (h00 : A 0 0 ≠ 0)
    (S : Matrix (Fin n) (Fin n) ℤ)
    (hS : ∀ y, (S *ᵥ y) ⬝ᵥ (complSq A *ᵥ (S *ᵥ y)) = y ⬝ᵥ (complSq A *ᵥ y))
    (hdiv : ∀ i j, A 0 0 ∣ (S - 1) i j) :
    ∃ T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ,
      (∀ x, (T *ᵥ x) ⬝ᵥ (A *ᵥ (T *ᵥ x)) = x ⬝ᵥ (A *ᵥ x)) ∧ T *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧
      T.submatrix Fin.succ Fin.succ = S ∧ T.det = S.det := by
  set a : Fin n → ℤ := fun i : Fin n => A 0 i.succ with ha
  have ht : ∀ j, ∃ tj : ℤ, A 0 0 * tj = a j - ∑ i, S i j * a i := by
    intro j
    have h1 : A 0 0 ∣ ∑ i, (S - 1) i j * a i :=
      Finset.dvd_sum fun i _ => Dvd.dvd.mul_right (hdiv i j) _
    have h2 : ∑ i, (S - 1) i j * a i = ∑ i, S i j * a i - a j := by
      simp [Matrix.sub_apply, Matrix.one_apply, sub_mul, Finset.sum_sub_distrib]
    rw [h2] at h1
    obtain ⟨q, hq⟩ := h1
    exact ⟨-q, by linarith⟩
  choose t ht using ht
  let T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
    Matrix.of fun i j => Fin.cases (Fin.cases 1 (fun j' => t j') j) (fun i' : Fin n => Fin.cases 0 (fun j' : Fin n => S i' j') j) i
  have T00 : T 0 0 = 1 := rfl
  have T0s : ∀ j : Fin n, T 0 j.succ = t j := fun j => rfl
  have Ts0 : ∀ i : Fin n, T i.succ 0 = 0 := fun i => rfl
  have Tss : ∀ i j : Fin n, T i.succ j.succ = S i j := fun i j => rfl
  have hsub : T.submatrix Fin.succ Fin.succ = S := by ext i j; exact Tss i j
  have hT0 : T *ᵥ Pi.single 0 1 = Pi.single 0 1 := (mulVec_single_zero_iff T).2 ⟨T00, Ts0⟩
  have hdet : T.det = S.det := by rw [det_eq_of_col_zero T Ts0, T00, hsub, one_mul]
  refine ⟨T, fun x => ?_, hT0, hsub, hdet⟩
  set y := Fin.tail x with hy
  have htail : Fin.tail (T *ᵥ x) = S *ᵥ y := by
    ext i
    simp [Fin.tail, mulVec, dotProduct, Fin.sum_univ_succ, Ts0, Tss, y]
  have h0 : (T *ᵥ x) 0 = x 0 + ∑ j, t j * y j := by
    simp [mulVec, dotProduct, Fin.sum_univ_succ, T00, T0s, y, Fin.tail]
  have hc : (A *ᵥ (T *ᵥ x)) 0 = (A *ᵥ x) 0 := by
    have e1 : (A *ᵥ (T *ᵥ x)) 0 = A 0 0 * (T *ᵥ x) 0 + ∑ i, a i * (Fin.tail (T *ᵥ x)) i := by
      simp [mulVec, dotProduct, Fin.sum_univ_succ, Fin.tail, ha]
    have e2 : (A *ᵥ x) 0 = A 0 0 * x 0 + ∑ i, a i * y i := by
      simp [mulVec, dotProduct, Fin.sum_univ_succ, Fin.tail, ha, y]
    rw [e1, e2, h0, htail]
    have e3 : ∑ i, a i * (S *ᵥ y) i = ∑ j, (∑ i, S i j * a i) * y j := by
      simp only [mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have e4 : A 0 0 * ∑ j, t j * y j = ∑ j, (a j - ∑ i, S i j * a i) * y j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [← ht j]; ring
    have e5 : ∑ j, (a j - ∑ i, S i j * a i) * y j = ∑ j, a j * y j - ∑ j, (∑ i, S i j * a i) * y j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    linarith
  have s1 := spec_vec hA (T *ᵥ x)
  have s2 := spec_vec hA x
  rw [hc, htail] at s1
  rw [← hy] at s2
  rw [hS y] at s1
  exact mul_left_cancel₀ h00 (by linarith)

/-- **Theorem 4.1** (Cassels, Ch. 13, §4, p. 299): let $f$ be classically integral with $f_{00} = f(\vec{e}_0) \ne 0$ and
let $g$ be the form of (4.4). Every $T \in O(f)$ with $T\vec{e}_0 = \vec{e}_0$ (4.3) has the shape (4.5)
$$y_0 = x_0 + t_1x_1 + \cdots + t_nx_n, \qquad y_j = \textstyle\sum_{k \ge 1} s_{jk}x_k \ (j \ge 1),$$
and induces an automorph $S = (s_{jk}) \in O(g)$. The set of such $S$ is a subgroup of finite index of $O(g)$, which
includes all the $S \equiv I \pmod{f_{00}}$. (Statements (i)–(iii) below.)

Kept beside `Cassels.Ch13.thm_4_1` and `Cassels.Ch13.thm_4_1_ext` (integral matrices, no hypothesis
$f_{00} \ne 0$ in the first). -/
@[kb "cassels1978" "Ch. 13, §4, Thm. 4.1, (4.3)–(4.5), p. 299"]
theorem aut_fix_restrict {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ} (hA : A.IsSymm) (h00 : A 0 0 ≠ 0) :
    (∀ T ∈ Siegel.Aut (Siegel.ofGram A), T.val *ᵥ Pi.single 0 1 = Pi.single 0 1 →
      ∃ S ∈ Siegel.Aut (Siegel.ofGram (complSq A)), S.val = T.val.submatrix Fin.succ Fin.succ) ∧
    (∀ S ∈ Siegel.Aut (Siegel.ofGram (complSq A)), (∀ i j, A 0 0 ∣ (S.val - 1) i j) →
      ∃ T ∈ Siegel.Aut (Siegel.ofGram A), T.val *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧
        T.val.submatrix Fin.succ Fin.succ = S.val) ∧
    ∃ H : Subgroup (GL (Fin n) ℤ), H ≤ Siegel.Aut (Siegel.ofGram (complSq A)) ∧
      (H.subgroupOf (Siegel.Aut (Siegel.ofGram (complSq A)))).FiniteIndex ∧
      ∀ S : GL (Fin n) ℤ, S ∈ H ↔ ∃ T ∈ Siegel.Aut (Siegel.ofGram A),
        T.val *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧ T.val.submatrix Fin.succ Fin.succ = S.val := by
  have part1 : ∀ T ∈ Siegel.Aut (Siegel.ofGram A), T.val *ᵥ Pi.single 0 1 = Pi.single 0 1 →
      ∃ S ∈ Siegel.Aut (Siegel.ofGram (complSq A)), S.val = T.val.submatrix Fin.succ Fin.succ := by
    intro T hT hT0
    have hTm := (mem_aut_ofGram_iff hA T).1 hT
    obtain ⟨h0, h1⟩ := (mulVec_single_zero_iff T.val).1 hT0
    have hdet : (T.val.submatrix Fin.succ Fin.succ).det = T.val.det := by
      rw [det_eq_of_col_zero T.val h1, h0, one_mul]
    have hu : IsUnit (T.val.submatrix Fin.succ Fin.succ).det := by
      rw [hdet]; exact Matrix.isUnits_det_units T
    refine ⟨Matrix.nonsingInvUnit _ hu, ?_, rfl⟩
    intro y
    exact sub_eval hA h00 hTm hT0 y
  have part2 : ∀ S ∈ Siegel.Aut (Siegel.ofGram (complSq A)), (∀ i j, A 0 0 ∣ (S.val - 1) i j) →
      ∃ T ∈ Siegel.Aut (Siegel.ofGram A), T.val *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧
        T.val.submatrix Fin.succ Fin.succ = S.val := by
    intro S hS hdiv
    have hS' : ∀ y, (S.val *ᵥ y) ⬝ᵥ (complSq A *ᵥ (S.val *ᵥ y)) = y ⬝ᵥ (complSq A *ᵥ y) := by
      intro y
      have := hS y
      rwa [Siegel.eval_ofGram (complSq_isSymm hA), Siegel.eval_ofGram (complSq_isSymm hA)] at this
    obtain ⟨T, hf, hT0, hsub, hdet⟩ := lift_exists hA h00 S.val hS' hdiv
    have hu : IsUnit T.det := by rw [hdet]; exact Matrix.isUnits_det_units S
    refine ⟨Matrix.nonsingInvUnit T hu, ?_, hT0, hsub⟩
    intro x
    show (Siegel.ofGram A).eval (T *ᵥ x) = (Siegel.ofGram A).eval x
    rw [Siegel.eval_ofGram hA, Siegel.eval_ofGram hA]
    exact hf x
  refine ⟨part1, part2, ?_⟩
  let H : Subgroup (GL (Fin n) ℤ) :=
    { carrier := {S | ∃ T ∈ Siegel.Aut (Siegel.ofGram A), T.val *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧
        T.val.submatrix Fin.succ Fin.succ = S.val}
      one_mem' := ⟨1, one_mem _, by rw [Units.val_one, one_mulVec], by
        simp only [Units.val_one]
        exact Matrix.submatrix_one _ (Fin.succ_injective _)⟩
      mul_mem' := by
        rintro S1 S2 ⟨T1, hT1, h1, e1⟩ ⟨T2, hT2, h2, e2⟩
        refine ⟨T1 * T2, mul_mem hT1 hT2, ?_, ?_⟩
        · rw [Units.val_mul, ← mulVec_mulVec, h2, h1]
        · rw [Units.val_mul, Units.val_mul, submatrix_succ_mul _ _ ((mulVec_single_zero_iff T1.val).1 h1).2, e1, e2]
      inv_mem' := by
        rintro S ⟨T, hT, h1, e1⟩
        refine ⟨T⁻¹, inv_mem hT, ?_, ?_⟩
        · calc (T⁻¹).val *ᵥ Pi.single 0 1 = (T⁻¹).val *ᵥ (T.val *ᵥ Pi.single 0 1) := by rw [h1]
            _ = Pi.single 0 1 := by rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
        · have hm := submatrix_succ_mul T.val (T⁻¹).val ((mulVec_single_zero_iff T.val).1 h1).2
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one,
            Matrix.submatrix_one _ (Fin.succ_injective _), e1] at hm
          calc (T⁻¹).val.submatrix Fin.succ Fin.succ
              = (S⁻¹).val * (S.val * (T⁻¹).val.submatrix Fin.succ Fin.succ) := by
                rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
            _ = (S⁻¹).val := by rw [← hm, Matrix.mul_one] }
  refine ⟨H, ?_, ?_, fun S => Iff.rfl⟩
  · rintro S ⟨T, hT, h1, e1⟩
    obtain ⟨S', hS', e2⟩ := part1 T hT h1
    have : S' = S := Units.ext (by rw [e2, e1])
    rwa [← this]
  · refine finiteIndex_subgroupOf_of_cong _ _ (m := (A 0 0).natAbs) (Int.natAbs_ne_zero.2 h00) ?_
    intro S hS hdiv
    exact part2 S hS (fun i j => Int.natAbs_dvd.1 (hdiv i j))

/-! ### Automorphs fixing an isotropic vector: Theorem 4.2 (p. 300) -/

/-- Polarization identity for a symmetric matrix. -/
theorem form_add {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) (u v : Fin n → ℤ) :
    (u + v) ⬝ᵥ (A *ᵥ (u + v)) = u ⬝ᵥ (A *ᵥ u) + 2 * (u ⬝ᵥ (A *ᵥ v)) + v ⬝ᵥ (A *ᵥ v) := by
  have h : v ⬝ᵥ (A *ᵥ u) = u ⬝ᵥ (A *ᵥ v) := by
    rw [dotProduct_mulVec, dotProduct_comm, ← hA.eq, vecMul_transpose, hA.eq]
  simp only [mulVec_add, dotProduct_add, add_dotProduct, h]
  ring

/-- $(Su)^{\mathsf T}H(Sv) = u^{\mathsf T}(S^{\mathsf T}HS)v$. -/
theorem dot_conj2 {K : Type*} [CommRing K] (S H : Matrix (Fin n) (Fin n) K) (u v : Fin n → K) :
    (S *ᵥ u) ⬝ᵥ (H *ᵥ (S *ᵥ v)) = u ⬝ᵥ ((Sᵀ * H * S) *ᵥ v) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec u Sᵀ, vecMul_transpose]

/-- A matrix is determined by its bilinear form. -/
theorem matrix_ext_dot {K : Type*} [CommRing K] (M N : Matrix (Fin n) (Fin n) K)
    (h : ∀ x y, x ⬝ᵥ (M *ᵥ y) = x ⬝ᵥ (N *ᵥ y)) : M = N := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa [dotProduct, mulVec, Pi.single_apply] using this

/-- Hessians of rationally related forms: $H_g = S^{\mathsf T}H_fS$. -/
theorem hessian_rel {f g : IntQF n} {S : Matrix (Fin n) (Fin n) ℚ}
    (hg : ∀ x : Fin n → ℚ, g.evalIn ℚ x = f.evalIn ℚ (S *ᵥ x)) :
    g.hessian.map (Int.castRingHom ℚ) = Sᵀ * f.hessian.map (Int.castRingHom ℚ) * S := by
  apply matrix_ext_dot
  intro x y
  have h1 := QuadForm.polar_eq_hessian ℚ g x y
  have h2 := QuadForm.polar_eq_hessian ℚ f (S *ᵥ x) (S *ᵥ y)
  simp only [algebraMap_int_eq] at h1 h2
  rw [← h1, ← dot_conj2, ← h2, hg, hg, hg, mulVec_add]

/-- Membership in `Aut Q` in terms of the Hessian. -/
theorem mem_aut_iff_hessian (Q : IntQF n) (T : GL (Fin n) ℤ) :
    T ∈ Siegel.Aut Q ↔ T.valᵀ * Q.hessian * T.val = Q.hessian :=
  Siegel.eval_mulVec_eq_iff_hessian Q Q T.val

/-- An integral matrix that is a rational conjugate of a unimodular one is unimodular. -/
theorem exists_gl_of_cast {R W : Matrix (Fin n) (Fin n) ℚ} (T : GL (Fin n) ℤ) (M : Matrix (Fin n) (Fin n) ℤ)
    (hRW : R.det * W.det = 1) (h : M.map (Int.castRingHom ℚ) = R * T.val.map (Int.castRingHom ℚ) * W) :
    ∃ U : GL (Fin n) ℤ, U.val = M := by
  have h1 : (M.det : ℚ) = (T.val.det : ℚ) := by
    have e1 : (M.det : ℚ) = (M.map (Int.castRingHom ℚ)).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
    have e2 : (T.val.det : ℚ) = (T.val.map (Int.castRingHom ℚ)).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
    rw [e1, e2, h, det_mul, det_mul]
    linear_combination (T.val.map (Int.castRingHom ℚ)).det * hRW
  have h2 : M.det = T.val.det := by exact_mod_cast h1
  exact ⟨Matrix.nonsingInvUnit M (by rw [h2]; exact Matrix.isUnits_det_units T), rfl⟩

/-- Clearing denominators of a rational matrix. -/
theorem exists_clear_denoms (M : Matrix (Fin n) (Fin n) ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ P : Matrix (Fin n) (Fin n) ℤ, P.map (Int.castRingHom ℚ) = (N : ℚ) • M := by
  refine ⟨∏ i, ∏ j, (M i j).den, Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => (M i j).den_pos, ?_⟩
  have hd : ∀ i j, ∃ z : ℤ, (z : ℚ) = ((∏ i, ∏ j, (M i j).den : ℕ) : ℚ) * M i j := by
    intro i j
    obtain ⟨c, hc⟩ : (M i j).den ∣ ∏ i, ∏ j, (M i j).den :=
      dvd_trans (Finset.dvd_prod_of_mem (fun j => (M i j).den) (Finset.mem_univ j))
        (Finset.dvd_prod_of_mem (fun i => ∏ j, (M i j).den) (Finset.mem_univ i))
    refine ⟨(M i j).num * c, ?_⟩
    rw [hc]
    push_cast
    have := Rat.mul_den_eq_num (M i j)
    linear_combination (-(c : ℚ)) * this
  choose z hz using hd
  exact ⟨Matrix.of z, by ext i j; simp [hz]⟩

/-- Divisibility of all entries by `m` gives a quotient matrix. -/
theorem exists_smul_of_dvd {m : ℤ} (M : Matrix (Fin n) (Fin n) ℤ) (h : ∀ i j, m ∣ M i j) :
    ∃ X : Matrix (Fin n) (Fin n) ℤ, M = m • X := by
  choose X hX using h
  exact ⟨Matrix.of X, by ext i j; simp [hX]⟩

/-- The conjugation relation $S^{-1}TS = U$ between integral matrices. -/
def ConjRel (S : Matrix (Fin n) (Fin n) ℚ) (T U : GL (Fin n) ℤ) : Prop :=
  S⁻¹ * T.val.map (Int.castRingHom ℚ) * S = U.val.map (Int.castRingHom ℚ)

theorem ConjRel.one (S : Matrix (Fin n) (Fin n) ℚ) (hS : IsUnit S.det) : ConjRel S 1 1 := by
  simp [ConjRel, Matrix.nonsing_inv_mul _ hS]

theorem ConjRel.mul {S : Matrix (Fin n) (Fin n) ℚ} (hS : IsUnit S.det) {T1 T2 U1 U2 : GL (Fin n) ℤ}
    (h1 : ConjRel S T1 U1) (h2 : ConjRel S T2 U2) : ConjRel S (T1 * T2) (U1 * U2) := by
  unfold ConjRel at *
  rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, ← h1, ← h2]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc S S⁻¹, Matrix.mul_nonsing_inv _ hS, Matrix.one_mul]

theorem ConjRel.inv {S : Matrix (Fin n) (Fin n) ℚ} (hS : IsUnit S.det) {T U : GL (Fin n) ℤ}
    (h : ConjRel S T U) : ConjRel S T⁻¹ U⁻¹ := by
  unfold ConjRel at *
  have hTT : (T⁻¹).val.map (Int.castRingHom ℚ) * T.val.map (Int.castRingHom ℚ) = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel]; simp
  have hUU : U.val.map (Int.castRingHom ℚ) * (U⁻¹).val.map (Int.castRingHom ℚ) = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel]; simp
  calc S⁻¹ * (T⁻¹).val.map (Int.castRingHom ℚ) * S
      = (S⁻¹ * (T⁻¹).val.map (Int.castRingHom ℚ) * S) * (U.val.map (Int.castRingHom ℚ) *
          (U⁻¹).val.map (Int.castRingHom ℚ)) := by rw [hUU, Matrix.mul_one]
    _ = (S⁻¹ * (T⁻¹).val.map (Int.castRingHom ℚ) * S * (S⁻¹ * T.val.map (Int.castRingHom ℚ) * S)) *
          (U⁻¹).val.map (Int.castRingHom ℚ) := by rw [h, Matrix.mul_assoc _ (U.val.map _)]
    _ = (U⁻¹).val.map (Int.castRingHom ℚ) := by
      have : S⁻¹ * (T⁻¹).val.map (Int.castRingHom ℚ) * S * (S⁻¹ * T.val.map (Int.castRingHom ℚ) * S) = 1 := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc S S⁻¹, Matrix.mul_nonsing_inv _ hS, Matrix.one_mul, ← Matrix.mul_assoc _ (T.val.map _),
          hTT, Matrix.one_mul, Matrix.nonsing_inv_mul _ hS]
      rw [this, Matrix.one_mul]

/-- Conjugating an automorph: $S U = T S$, $T^{\mathsf T}H T = H$ gives $U^{\mathsf T}(S^{\mathsf T}HS)U = S^{\mathsf T}HS$. -/
theorem conj_inv1 {K : Type*} [CommRing K] (S Hf Tq Uq : Matrix (Fin n) (Fin n) K) (hSU : S * Uq = Tq * S)
    (hT : Tqᵀ * Hf * Tq = Hf) : Uqᵀ * (Sᵀ * Hf * S) * Uq = Sᵀ * Hf * S := by
  calc Uqᵀ * (Sᵀ * Hf * S) * Uq = (S * Uq)ᵀ * Hf * (S * Uq) := by
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (Tq * S)ᵀ * Hf * (Tq * S) := by rw [hSU]
    _ = Sᵀ * (Tqᵀ * Hf * Tq) * S := by simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Sᵀ * Hf * S := by rw [hT]

theorem conj_inv2 {K : Type*} [CommRing K] (S S' Hf Tq Uq : Matrix (Fin n) (Fin n) K) (h1 : S * S' = 1)
    (hSU : S * Uq = Tq * S) (hU : Uqᵀ * (Sᵀ * Hf * S) * Uq = Sᵀ * Hf * S) : Tqᵀ * Hf * Tq = Hf := by
  calc Tqᵀ * Hf * Tq = (Tq * S * S')ᵀ * Hf * (Tq * S * S') := by rw [Matrix.mul_assoc Tq S S', h1, Matrix.mul_one]
    _ = S'ᵀ * ((Tq * S)ᵀ * Hf * (Tq * S)) * S' := by simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = S'ᵀ * ((S * Uq)ᵀ * Hf * (S * Uq)) * S' := by rw [hSU]
    _ = S'ᵀ * (Uqᵀ * (Sᵀ * Hf * S) * Uq) * S' := by simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = S'ᵀ * (Sᵀ * Hf * S) * S' := by rw [hU]
    _ = (S * S')ᵀ * Hf * (S * S') := by simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Hf := by rw [h1]; simp

theorem ConjRel.comm {S : Matrix (Fin n) (Fin n) ℚ} (hS : IsUnit S.det) {T U : GL (Fin n) ℤ}
    (h : ConjRel S T U) :
    S * U.val.map (Int.castRingHom ℚ) = T.val.map (Int.castRingHom ℚ) * S := by
  unfold ConjRel at h
  rw [← h]
  calc S * (S⁻¹ * T.val.map (Int.castRingHom ℚ) * S) = (S * S⁻¹) * T.val.map (Int.castRingHom ℚ) * S := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hS, Matrix.one_mul]

theorem cast_conj (T H : Matrix (Fin n) (Fin n) ℤ) :
    (Tᵀ * H * T).map (Int.castRingHom ℚ) =
      (T.map (Int.castRingHom ℚ))ᵀ * H.map (Int.castRingHom ℚ) * T.map (Int.castRingHom ℚ) := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

theorem conjrel_mem_aut {f g : IntQF n} {S : Matrix (Fin n) (Fin n) ℚ} (hS : IsUnit S.det)
    (hg : ∀ x : Fin n → ℚ, g.evalIn ℚ x = f.evalIn ℚ (S *ᵥ x)) {T U : GL (Fin n) ℤ}
    (hT : T ∈ Siegel.Aut f) (h : ConjRel S T U) : U ∈ Siegel.Aut g := by
  rw [mem_aut_iff_hessian] at hT ⊢
  apply Matrix.map_injective (f := Int.castRingHom ℚ) (RingHom.injective_int _)
  have hT' := congrArg (Matrix.map · (Int.castRingHom ℚ)) hT
  simp only [cast_conj] at hT' ⊢
  have := conj_inv1 S _ _ _ (h.comm hS) hT'
  rw [← hessian_rel hg] at this
  exact this

theorem conjrel_mem_aut' {f g : IntQF n} {S : Matrix (Fin n) (Fin n) ℚ} (hS : IsUnit S.det)
    (hg : ∀ x : Fin n → ℚ, g.evalIn ℚ x = f.evalIn ℚ (S *ᵥ x)) {T U : GL (Fin n) ℤ}
    (hU : U ∈ Siegel.Aut g) (h : ConjRel S T U) : T ∈ Siegel.Aut f := by
  rw [mem_aut_iff_hessian] at hU ⊢
  apply Matrix.map_injective (f := Int.castRingHom ℚ) (RingHom.injective_int _)
  have hU' := congrArg (Matrix.map · (Int.castRingHom ℚ)) hU
  simp only [cast_conj] at hU' ⊢
  rw [hessian_rel hg] at hU'
  exact conj_inv2 S S⁻¹ _ _ _ (Matrix.mul_nonsing_inv _ hS) (h.comm hS) hU'

/-- A common denominator `N` for `S` and `S⁻¹`, with the integral matrices `P = N S`, `Q = N S⁻¹`. -/
theorem exists_modulus (S : Matrix (Fin n) (Fin n) ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ P Q : Matrix (Fin n) (Fin n) ℤ,
      P.map (Int.castRingHom ℚ) = (N : ℚ) • S ∧ Q.map (Int.castRingHom ℚ) = (N : ℚ) • S⁻¹ := by
  obtain ⟨N1, h1, P1, hP1⟩ := exists_clear_denoms S
  obtain ⟨N2, h2, P2, hP2⟩ := exists_clear_denoms S⁻¹
  refine ⟨N1 * N2, Nat.mul_pos h1 h2, (N2 : ℤ) • P1, (N1 : ℤ) • P2, ?_, ?_⟩
  · ext i j
    have := congr_fun (congr_fun hP1 i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, eq_intCast, Int.cast_mul,
      Int.cast_natCast, Nat.cast_mul] at this ⊢
    rw [this]; ring
  · ext i j
    have := congr_fun (congr_fun hP2 i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, eq_intCast, Int.cast_mul,
      Int.cast_natCast, Nat.cast_mul] at this ⊢
    rw [this]; ring

/-- **The unipotent matrix (4.7)**: $x_0 \mapsto x_0 + l_1x_1 + \cdots + l_{m+1}x_{m+1}$, $x_1 \mapsto x_1$,
$x_j \mapsto x_j + k_jx_1$ ($j \ge 2$), for $\vec{l}, \vec{k} \in \mathbb{Z}^{m+2}$ (the entries $l_0$, $k_0$, $k_1$ are
not used). -/
def unipMat {m : ℕ} (l k : Fin (m + 2) → ℤ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℤ :=
  Matrix.of fun i j =>
    (if i = j then 1 else 0) + (if i = 0 ∧ j ≠ 0 then l j else 0) + (if 2 ≤ i.val ∧ j = 1 then k i else 0)

/-- **Theorem 4.2** (Cassels, Ch. 13, §4, p. 300): let
$$f(\vec{x}) = 2f_{01}x_0x_1 + g(x_1, \dots, x_{m+1}) \tag{4.6}$$
be classically integral (matrix $A$ with $A_{00} = 0$ and $A_{0j} = 0$ for $j \ge 2$), and let $k_2, \dots, k_{m+1}$ be
integers with $k_j \equiv 0 \pmod{2f_{01}}$. Then there are integers $l_1, \dots, l_{m+1}$ such that the transformation
(4.7) $x_0 \mapsto x_0 + l_1x_1 + \cdots + l_{m+1}x_{m+1}$, $x_1 \mapsto x_1$, $x_j \mapsto x_j + k_jx_1$ ($j \ge 2$) is an
automorph of $f$. (Cassels' variables $x_1, \dots, x_n$ are $x_0, \dots, x_{m+1}$ here; the displays (4.6), (4.7) and
the congruence are garbled in the machine-read text and were reconstructed: with $k_j = 2f_{01}m_j$ one can take
$l_j = -2\sum_i g_{ji}m_i$ for $j \ge 2$ and $l_1 = -2\sum_i g_{1i}m_i - 2f_{01}g(\vec{m})$.) -/
@[kb "cassels1978" "Ch. 13, §4, Thm. 4.2, (4.6)–(4.7), p. 300"]
theorem exists_unipotent_aut {m : ℕ} {A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℤ} (hA : A.IsSymm)
    (h00 : A 0 0 = 0) (h0j : ∀ j : Fin (m + 2), 2 ≤ j.val → A 0 j = 0) (k : Fin (m + 2) → ℤ)
    (hk : ∀ j : Fin (m + 2), 2 ≤ j.val → 2 * A 0 1 ∣ k j) :
    ∃ l : Fin (m + 2) → ℤ, ∀ x, (Siegel.ofGram A).eval (unipMat l k *ᵥ x) = (Siegel.ofGram A).eval x := by
  set α := A 0 1 with hα
  have hsym : ∀ i j, A i j = A j i := fun i j => by
    have := congr_fun (congr_fun hA i) j
    simpa using this.symm
  have hcol : ∀ i : Fin (m + 2), i ≠ 1 → A i 0 = 0 := by
    intro i hi
    rw [hsym]
    by_cases hi0 : i = 0
    · rw [hi0]; exact h00
    · exact h0j i (by
        have h1 : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
        have h2 : i.val ≠ 1 := fun h => hi (Fin.ext h)
        omega)
  let mm : Fin (m + 2) → ℤ := fun i => if 2 ≤ i.val then k i / (2 * α) else 0
  have hmm0 : mm 0 = 0 := by simp [mm]
  have hmm1 : mm 1 = 0 := by simp [mm]
  have hkm : ∀ i : Fin (m + 2), 2 ≤ i.val → k i = 2 * α * mm i := by
    intro i hi
    simp only [mm, hi, if_true]
    exact (Int.mul_ediv_cancel' (hk i hi)).symm
  let F : ℤ := mm ⬝ᵥ (A *ᵥ mm)
  let l : Fin (m + 2) → ℤ := fun j => -2 * (∑ i, mm i * A i j) - (if j = 1 then 2 * α * F else 0)
  refine ⟨l, fun x => ?_⟩
  rw [Siegel.eval_ofGram hA, Siegel.eval_ofGram hA]
  set s : ℤ := ∑ j, (if j = 0 then 0 else l j * x j) with hs
  have hU : unipMat l k *ᵥ x = x + s • Pi.single 0 1 + (2 * α * x 1) • mm := by
    ext i
    simp only [mulVec, dotProduct, unipMat, Matrix.of_apply, add_mul, Finset.sum_add_distrib, ite_mul, one_mul,
      zero_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    by_cases hi0 : i = 0
    · subst hi0
      have : (∑ x_1, if (0 : Fin (m + 2)) = 0 ∧ x_1 ≠ 0 then l x_1 * x x_1 else 0) = s := by
        rw [hs]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : j = 0 <;> simp [hj]
      rw [this, hmm0]
      simp
    · have h1 : (∑ x_1, if i = 0 ∧ x_1 ≠ 0 then l x_1 * x x_1 else 0) = 0 := by simp [hi0]
      rw [h1]
      by_cases h2 : 2 ≤ i.val
      · have h3 : (∑ x_1, if 2 ≤ i.val ∧ x_1 = 1 then k i * x x_1 else 0) = k i * x 1 := by
          simp [h2]
        rw [h3, hkm i h2]
        simp [hi0]
        ring
      · have h3 : (∑ x_1, if 2 ≤ i.val ∧ x_1 = 1 then k i * x x_1 else 0) = 0 := by simp [h2]
        have h4 : mm i = 0 := by simp [mm, h2]
        rw [h3, h4]
        simp [hi0]
  set P : ℤ := x ⬝ᵥ (A *ᵥ mm) with hP
  set e0 : Fin (m + 2) → ℤ := Pi.single 0 1 with he0
  have hf0 : e0 ⬝ᵥ (A *ᵥ e0) = 0 := by
    simp [he0, dotProduct_single, mulVec_single_one, h00]
  have hAm0 : (A *ᵥ mm) 0 = 0 := by
    simp only [mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj0 : j = 0
    · rw [hj0, hmm0, mul_zero]
    by_cases hj1 : j = 1
    · rw [hj1, hmm1, mul_zero]
    rw [h0j j (by
      have h1 : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
      have h2 : j.val ≠ 1 := fun h => hj1 (Fin.ext h)
      omega), zero_mul]
  have hb : e0 ⬝ᵥ (A *ᵥ mm) = 0 := by
    simp [he0, single_dotProduct, hAm0]
  have hc : x ⬝ᵥ (A *ᵥ e0) = α * x 1 := by
    simp only [he0, mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [Finset.sum_eq_single (1 : Fin (m + 2))]
    · rw [hsym 1 0]; ring
    · intro i _ hi; rw [hcol i hi]; ring
    · simp
  have hl0 : l 0 = 0 := by
    have : ∑ i, mm i * A i 0 = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : i = 1
      · rw [hi, hmm1, zero_mul]
      · rw [hcol i hi, mul_zero]
    simp [l, this]
  have hsP : s = -2 * P - 2 * α * F * x 1 := by
    have e1 : ∑ j, l j * x j = s + l 0 * x 0 := by
      have : ∀ j, l j * x j = (if j = 0 then 0 else l j * x j) + (if j = 0 then l 0 * x 0 else 0) := by
        intro j
        by_cases hj : j = 0
        · subst hj; simp
        · simp [hj]
      rw [hs, Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib]
      simp
    have e2 : ∑ j, l j * x j = -2 * ∑ j, (∑ i, mm i * A i j) * x j - 2 * α * F * x 1 := by
      have hj : ∀ j, l j * x j = -2 * ((∑ i, mm i * A i j) * x j) - (if j = 1 then 2 * α * F * x 1 else 0) := by
        intro j
        by_cases hj : j = 1
        · subst hj; simp only [l, if_true]; ring
        · simp only [l, hj, if_false]; ring
      rw [Finset.sum_congr rfl (fun j _ => hj j), Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp
    have e3 : ∑ j, (∑ i, mm i * A i j) * x j = P := by
      simp only [hP, mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [hsym i j]; ring
    rw [hl0, zero_mul, add_zero] at e1
    rw [← e1, e2, e3]
  rw [hU, add_assoc, form_add hA x (s • e0 + (2 * α * x 1) • mm),
    form_add hA (s • e0) ((2 * α * x 1) • mm)]
  simp only [mulVec_smul, mulVec_add, dotProduct_smul, smul_dotProduct, dotProduct_add, smul_eq_mul]
  linear_combination (s ^ 2) * hf0 + (2 * s * (2 * α * x 1)) * hb + (2 * s) * hc + (2 * α * x 1) * hsP

/-! ### Rationally equivalent forms: Lemma 4.1 (p. 300) -/

/-- **Lemma 4.1** (Cassels, Ch. 13, §4, p. 300): let $f$ and $g(\vec{x}) = f(S\vec{x})$ be integral forms, $S$ a
non-singular rational matrix. If $T \in O(f)$ and $U = S^{-1}TS$ is integral then $U \in O(g)$. The set of such $T$
is a subgroup of finite index in $O(f)$, and the set of such $U$ is a subgroup of finite index in $O(g)$. Stated for
integer-valued $f$, $g$ (Cassels' "quadratic forms" here are integral, as $O(f)$ is the group of integral
automorphs).

Superseded by `Cassels.Ch13.lemma_4_1`, the same statement for every rational matrix $F$. -/
theorem aut_commensurable {f g : IntQF n} {S : Matrix (Fin n) (Fin n) ℚ} (hS : IsUnit S.det)
    (hg : ∀ x : Fin n → ℚ, g.evalIn ℚ x = f.evalIn ℚ (S *ᵥ x)) :
    (∀ T ∈ Siegel.Aut f, ∀ U : GL (Fin n) ℤ,
      S⁻¹ * T.val.map (Int.cast : ℤ → ℚ) * S = U.val.map (Int.cast : ℤ → ℚ) → U ∈ Siegel.Aut g) ∧
    (∃ H : Subgroup (GL (Fin n) ℤ), H ≤ Siegel.Aut f ∧ (H.subgroupOf (Siegel.Aut f)).FiniteIndex ∧
      ∀ T : GL (Fin n) ℤ, T ∈ H ↔ T ∈ Siegel.Aut f ∧
        ∃ U : GL (Fin n) ℤ, S⁻¹ * T.val.map (Int.cast : ℤ → ℚ) * S = U.val.map (Int.cast : ℤ → ℚ)) ∧
    (∃ H' : Subgroup (GL (Fin n) ℤ), H' ≤ Siegel.Aut g ∧ (H'.subgroupOf (Siegel.Aut g)).FiniteIndex ∧
      ∀ U : GL (Fin n) ℤ, U ∈ H' ↔ ∃ T ∈ Siegel.Aut f,
        S⁻¹ * T.val.map (Int.cast : ℤ → ℚ) * S = U.val.map (Int.cast : ℤ → ℚ)) := by
  have hSS : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv _ hS
  have hSS' : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul _ hS
  have hdet1 : S⁻¹.det * S.det = 1 := by rw [← det_mul, hSS', det_one]
  have hdet2 : S.det * S⁻¹.det = 1 := by rw [← det_mul, hSS, det_one]
  obtain ⟨N, hN, P, Q, hP, hQ⟩ := exists_modulus S
  have hNN : (N * N : ℕ) ≠ 0 := Nat.mul_ne_zero hN.ne' hN.ne'
  refine ⟨fun T hT U h => conjrel_mem_aut hS hg hT h, ?_, ?_⟩
  · let H : Subgroup (GL (Fin n) ℤ) :=
      { carrier := {T | T ∈ Siegel.Aut f ∧ ∃ U, ConjRel S T U}
        one_mem' := ⟨one_mem _, 1, ConjRel.one S hS⟩
        mul_mem' := by
          rintro T1 T2 ⟨h1, U1, e1⟩ ⟨h2, U2, e2⟩
          exact ⟨mul_mem h1 h2, U1 * U2, ConjRel.mul hS e1 e2⟩
        inv_mem' := by
          rintro T ⟨h1, U, e1⟩
          exact ⟨inv_mem h1, U⁻¹, ConjRel.inv hS e1⟩ }
    refine ⟨H, fun T hT => hT.1, ?_, fun T => Iff.rfl⟩
    refine finiteIndex_subgroupOf_of_cong _ _ (m := N * N) hNN ?_
    intro T hT hdiv
    refine ⟨hT, ?_⟩
    obtain ⟨X, hX⟩ := exists_smul_of_dvd _ hdiv
    have hX' : T.val = 1 + ((N * N : ℕ) : ℤ) • X := by rw [← hX]; abel
    have hmap : T.val.map (Int.castRingHom ℚ) = 1 + ((N : ℚ) * N) • X.map (Int.castRingHom ℚ) := by
      rw [hX']
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
      by_cases hij : i = j <;> simp [hij]
    have heq : (1 + Q * X * P).map (Int.castRingHom ℚ) = S⁻¹ * T.val.map (Int.castRingHom ℚ) * S := by
      rw [hmap, Matrix.map_add _ (fun a b => map_add (Int.castRingHom ℚ) a b), Matrix.map_mul, Matrix.map_mul, hP, hQ,
        Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hSS', mul_smul_comm, smul_mul_assoc,
        Matrix.map_one _ (map_zero _) (map_one _)]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    obtain ⟨U, hU⟩ := exists_gl_of_cast (R := S⁻¹) (W := S) T (1 + Q * X * P) hdet1 heq
    exact ⟨U, by unfold ConjRel; rw [hU, heq]⟩
  · let H' : Subgroup (GL (Fin n) ℤ) :=
      { carrier := {U | ∃ T ∈ Siegel.Aut f, ConjRel S T U}
        one_mem' := ⟨1, one_mem _, ConjRel.one S hS⟩
        mul_mem' := by
          rintro U1 U2 ⟨T1, h1, e1⟩ ⟨T2, h2, e2⟩
          exact ⟨T1 * T2, mul_mem h1 h2, ConjRel.mul hS e1 e2⟩
        inv_mem' := by
          rintro U ⟨T, h1, e1⟩
          exact ⟨T⁻¹, inv_mem h1, ConjRel.inv hS e1⟩ }
    refine ⟨H', ?_, ?_, fun U => Iff.rfl⟩
    · rintro U ⟨T, hT, e⟩
      exact conjrel_mem_aut hS hg hT e
    · refine finiteIndex_subgroupOf_of_cong _ _ (m := N * N) hNN ?_
      intro U hU hdiv
      obtain ⟨Y, hY⟩ := exists_smul_of_dvd _ hdiv
      have hY' : U.val = 1 + ((N * N : ℕ) : ℤ) • Y := by rw [← hY]; abel
      have hmap : U.val.map (Int.castRingHom ℚ) = 1 + ((N : ℚ) * N) • Y.map (Int.castRingHom ℚ) := by
        rw [hY']
        ext i j
        simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
        by_cases hij : i = j <;> simp [hij]
      have heq : (1 + P * Y * Q).map (Int.castRingHom ℚ) = S * U.val.map (Int.castRingHom ℚ) * S⁻¹ := by
        rw [hmap, Matrix.map_add _ (fun a b => map_add (Int.castRingHom ℚ) a b), Matrix.map_mul, Matrix.map_mul, hP,
          hQ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hSS, mul_smul_comm, smul_mul_assoc,
          Matrix.map_one _ (map_zero _) (map_one _)]
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      obtain ⟨T, hT⟩ := exists_gl_of_cast (R := S) (W := S⁻¹) U (1 + P * Y * Q) hdet2 heq
      have hrel : ConjRel S T U := by
        unfold ConjRel
        rw [hT, heq]
        calc S⁻¹ * (S * U.val.map (Int.castRingHom ℚ) * S⁻¹) * S
            = (S⁻¹ * S) * U.val.map (Int.castRingHom ℚ) * (S⁻¹ * S) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hSS', Matrix.one_mul, Matrix.mul_one]
      exact ⟨T, conjrel_mem_aut' hS hg hU hrel, hrel⟩

end QuadFormsKB.Reduction
