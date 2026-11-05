/-
# Cassels, Chapter 12: remarks on semi-definite forms, level sets, the cone of definite forms, and neighbours

Cassels, *Rational Quadratic Forms* (1978), Ch. 12, pp. 260, 271 and 279. Four remarks of the running text, each
formalized here as a statement about the library's real forms (a form is its symmetric matrix $F$, with value
`val F x` $= \vec{x}^{\mathsf T}F\vec{x}$; `Basic.lean`).

* **p. 260 (§1).** A positive definite form $f$ in the wide sense (`Matrix.PosSemidef`) is equivalent over $\mathbb{R}$ to
  a sum of $m \le n$ squares of coordinates; $m = n$ iff $f$ is strictly definite (`Matrix.PosDef`), and a semi-definite
  form which is not strictly definite is singular, and conversely (`posSemidef_equiv_sum_squares`,
  `posDef_iff_card_eq_of_sq_decomp`, `posSemidef_not_posDef_iff_det_eq_zero`). *Reconstruction:* the "sum of squares
  $y_0^2 + \dots + y_{m-1}^2$" is stated as a sum of squares of the coordinates $y_i$, $i \in s$, of $\vec{y} = P\vec{x}$
  over a set $s$ of $m$ coordinates, $P$ an invertible real matrix; a permutation of the coordinates turns $s$ into
  $\{0, \dots, m-1\}$, so this is the same statement. Proved from Mathlib's spectral theorem.
* **p. 260 (§1).** The set $\{\vec{x} : f(\vec{x}) \le M\}$ is symmetric and convex, and bounded iff $f$ is strictly
  definite (`val_sublevel_symm`, `convex_val_sublevel`, `isBounded_val_sublevel_iff`).
* **p. 271 (§5, Note).** $d(f) > 0$ on $\mathcal P^\circ$ and $d(f) = 0$ on $\mathcal P \setminus \mathcal P^\circ$; hence
  $\mathcal P^\circ$ is a connected component of the complement of the hypersurface $d(f) = 0$ in the space of symmetric
  matrices (`posDef_det_pos`, `det_eq_zero_of_posSemidef_not_posDef`, `posDef_closed_in_nonsingular`,
  `posDef_eq_connectedComponentIn`). Fully proved, including the identification with a connected component.
* **p. 279 (§7).** $\mathcal R$, the sets $T\mathcal R$ and their intersections are convex (`convex_isMinkowskiReduced`,
  `convex_img`, `convex_img_inter`); the notion of *neighbours* (`AreNeighbours`: the intersection has codimension $1$ in
  the $N = n(n+1)/2$-dimensional space of forms, i.e. its affine span has dimension $N - 1$) and the set $\Sigma'$
  (`sigmaPrime`). The remark that $T_1\mathcal R, T_2\mathcal R$ are neighbours exactly when
  $T_1 = ST_2$ with $\mathcal R, S\mathcal R$ neighbours is `areNeighbours_mul_iff`
  (order of composition as in `Sec7.lean`: $T(Sf) = (ST)f$).

**Conventions.** Indices are 0-based; the dimension is $n$; $\mathcal P^\circ$ is `{F | F.PosDef}`, $\mathcal P$ is
`{F | F.PosSemidef}`; $d(f) = \det F$.
-/
import QuadFormsKB.Literature.Cassels.Ch12.Sec7

open Matrix

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-! ### Semi-definite forms as sums of squares (p. 260) -/

/-- Helper: spectral decomposition of a positive semi-definite real matrix as $F = P^{\mathsf T}DP$ with $P$ invertible
and $D$ the diagonal $0/1$ matrix of a set $s$ of coordinates ($F$ positive semi-definite; $P$ real $n \times n$). -/
theorem exists_conj_diag_indicator {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosSemidef) :
    ∃ (P : Matrix (Fin n) (Fin n) ℝ) (s : Finset (Fin n)), IsUnit P.det ∧
      F = Pᵀ * diagonal (fun i => if i ∈ s then (1 : ℝ) else 0) * P := by
  classical
  have hH : F.IsHermitian := hF.1
  set U : Matrix (Fin n) (Fin n) ℝ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU
  have hUU : Uᵀ * U = 1 := by
    have := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    simpa [hU, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hspec := hH.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] at hspec
  set lam : Fin n → ℝ := hH.eigenvalues with hlam
  have hnn : ∀ i, 0 ≤ lam i := fun i => hF.eigenvalues_nonneg i
  have hspec' : F = U * diagonal lam * Uᵀ := by
    rw [hspec]
    simp [hU, hlam]
  let c : Fin n → ℝ := fun i => if lam i = 0 then 1 else Real.sqrt (lam i)
  have hc : ∀ i, c i ≠ 0 := by
    intro i
    by_cases h : lam i = 0
    · simp [c, h]
    · simp only [c, h, ite_false]
      exact (Real.sqrt_pos.2 (lt_of_le_of_ne (hnn i) (Ne.symm h))).ne'
  refine ⟨diagonal c * Uᵀ, Finset.univ.filter fun i => lam i ≠ 0, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_diagonal]
    have : (Uᵀ).det * U.det = 1 := by rw [← Matrix.det_mul, hUU, Matrix.det_one]
    refine IsUnit.mul ?_ (IsUnit.of_mul_eq_one _ this)
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hc i).isUnit
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose]
    have hd : diagonal c * diagonal (fun i => if i ∈ Finset.univ.filter (fun i => lam i ≠ 0) then (1 : ℝ) else 0)
        * diagonal c = diagonal lam := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      by_cases h : lam i = 0
      · simp [c, h]
      · have := Real.sq_sqrt (hnn i)
        simp [c, h]
        nlinarith
    calc F = U * diagonal lam * Uᵀ := hspec'
      _ = _ := by rw [← hd]; simp only [Matrix.mul_assoc]

/-- Helper: the value of $P^{\mathsf T}DP$ for the diagonal $0/1$ matrix $D$ of a coordinate set $s$ is the sum of the
squares of the coordinates $(P\vec{x})_i$, $i \in s$. -/
theorem val_conj_indicator (P : Matrix (Fin n) (Fin n) ℝ) (s : Finset (Fin n)) (x : Fin n → ℝ) :
    val (Pᵀ * diagonal (fun i => if i ∈ s then (1 : ℝ) else 0) * P) x = ∑ i ∈ s, (P *ᵥ x) i ^ 2 := by
  rw [val_conj]
  simp only [val, dotProduct, mulVec_diagonal]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ s)]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have h2 : ∑ i ∈ Finset.univ.filter (fun i => i ∉ s), (P *ᵥ x) i * ((if i ∈ s then (1 : ℝ) else 0) * (P *ᵥ x) i)
      = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [(Finset.mem_filter.1 hi).2]
  rw [h2, add_zero]
  exact Finset.sum_congr rfl fun i hi => by simp [hi, sq]

/-- **A decomposition into squares decides strict definiteness** (Cassels, Ch. 12, §1, p. 260: "if $m = n$ then $f$ is
strictly definite but if $m < n$ then $f$ is only semi-definite"). Let $F$ be a positive semi-definite real symmetric
matrix, $P$ an invertible real $n \times n$ matrix and $s$ a set of coordinates with
$f(\vec{x}) = \sum_{i \in s}(P\vec{x})_i^2$ for all real $\vec{x}$. Then $F$ is strictly positive definite iff $s$ has
$n$ elements, i.e. iff $s$ is all of $\{0, \dots, n-1\}$. -/
@[kb "cassels1978" "Ch. 12, §1, p. 260 (m = n iff f strictly definite)"]
theorem posDef_iff_card_eq_of_sq_decomp {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosSemidef)
    {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsUnit P.det) {s : Finset (Fin n)}
    (h : ∀ x, val F x = ∑ i ∈ s, (P *ᵥ x) i ^ 2) : F.PosDef ↔ s.card = n := by
  classical
  have hcard : s.card = n ↔ s = Finset.univ := by
    have := Finset.card_eq_iff_eq_univ s
    rwa [Fintype.card_fin] at this
  rw [hcard]
  constructor
  · intro hd
    by_contra hne
    have : ∃ i, i ∉ s := by
      by_contra hall
      push Not at hall
      exact hne (Finset.eq_univ_of_forall hall)
    obtain ⟨i, hi⟩ := this
    set x : Fin n → ℝ := P⁻¹ *ᵥ Pi.single i 1 with hx
    have hPx : P *ᵥ x = Pi.single i 1 := by
      rw [hx, mulVec_mulVec, mul_nonsing_inv _ hP, one_mulVec]
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, mulVec_zero] at hPx
      have := congrFun hPx i
      simp at this
    have hpos := ((posDef_iff F).1 hd).2 x hx0
    rw [h x, hPx] at hpos
    have : ∑ j ∈ s, ((Pi.single i 1 : Fin n → ℝ) j) ^ 2 = 0 :=
      Finset.sum_eq_zero fun j hj => by
        have : j ≠ i := fun e => hi (e ▸ hj)
        simp [this]
    linarith
  · intro hs
    subst hs
    refine (posDef_iff F).2 ⟨((posSemidef_iff F).1 hF).1, fun x hx => ?_⟩
    rw [h x]
    have hPx : P *ᵥ x ≠ 0 := by
      intro h0
      apply hx
      calc x = (P⁻¹ * P) *ᵥ x := by rw [nonsing_inv_mul _ hP, one_mulVec]
        _ = 0 := by rw [← mulVec_mulVec, h0, mulVec_zero]
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hPx
    exact Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨j, Finset.mem_univ j, by
      simp only [Pi.zero_apply] at hj
      positivity⟩

/-- **A semi-definite form which is not strictly definite is singular, and conversely** (Cassels, Ch. 12, §1, p. 260:
"a positive definite $f$ is semi-definite if and only if it is singular"). For a positive semi-definite real symmetric
matrix $F$: $F$ is not strictly positive definite iff $\det F = 0$. -/
@[kb "cassels1978" "Ch. 12, §1, p. 260 (semi-definite iff singular)"]
theorem posSemidef_not_posDef_iff_det_eq_zero {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosSemidef) :
    ¬ F.PosDef ↔ F.det = 0 := by
  rw [hF.posDef_iff_det_ne_zero, not_not]

/-- **A positive (semi-)definite form is a sum of $m \le n$ squares over $\mathbb{R}$** (Cassels, Ch. 12, §1, p. 260).
For a positive semi-definite real symmetric matrix $F$ ($n \times n$) there are $m \le n$, an invertible real matrix $P$
(the real substitution $\vec{y} = P\vec{x}$) and a set $s$ of $m$ coordinates such that
$$f(\vec{x}) = \sum_{i \in s} (P\vec{x})_i^2 \quad (\vec{x} \in \mathbb{R}^n);$$
moreover $m = n$ iff $F$ is strictly positive definite, and $m < n$ iff $\det F = 0$ iff $F$ is semi-definite and not
strictly definite. (After permuting the coordinates, $s = \{0, \dots, m-1\}$ and the right-hand side is
$y_0^2 + \dots + y_{m-1}^2$.) Proof from Mathlib's spectral theorem (`Matrix.IsHermitian.spectral_theorem`). -/
@[kb "cassels1978" "Ch. 12, §1, p. 260 (definite form equivalent over ℝ to a sum of m ≤ n squares)"]
theorem posSemidef_equiv_sum_squares {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosSemidef) :
    ∃ (m : ℕ) (P : Matrix (Fin n) (Fin n) ℝ) (s : Finset (Fin n)), s.card = m ∧ m ≤ n ∧ IsUnit P.det ∧
      (∀ x, val F x = ∑ i ∈ s, (P *ᵥ x) i ^ 2) ∧ (m = n ↔ F.PosDef) ∧ (m < n ↔ F.det = 0) := by
  obtain ⟨P, s, hP, hFP⟩ := exists_conj_diag_indicator hF
  have hv : ∀ x, val F x = ∑ i ∈ s, (P *ᵥ x) i ^ 2 := fun x => by
    rw [hFP]; exact val_conj_indicator P s x
  have hle : s.card ≤ n := by simpa using Finset.card_le_univ s
  have hiff := posDef_iff_card_eq_of_sq_decomp hF hP hv
  refine ⟨s.card, P, s, rfl, hle, hP, hv, hiff.symm, ?_⟩
  rw [← posSemidef_not_posDef_iff_det_eq_zero hF]
  constructor
  · intro h hpd
    exact h.ne (hiff.1 hpd)
  · intro h
    exact lt_of_le_of_ne hle (fun e => h (hiff.2 e))

/-! ### Level sets of a positive semi-definite form (p. 260) -/

/-- **The set $f(\vec{x}) \le M$ is symmetric** (Cassels, Ch. 12, §1, p. 260): $f(-\vec{x}) = f(\vec{x})$, so $\vec{x}$ is in
the set iff $-\vec{x}$ is. Holds for every real form (matrix $F$) and every real $M$. -/
@[kb "cassels1978" "Ch. 12, §1, p. 260 (the set f(x) ≤ M is symmetric)"]
theorem val_sublevel_symm (F : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) :
    ∀ x : Fin n → ℝ, x ∈ {x | val F x ≤ M} ↔ -x ∈ {x | val F x ≤ M} := by
  intro x
  have : val F (-x) = val F x := by
    have := val_smul F (-1) x
    simpa using this
  simp only [Set.mem_ofPred_eq, this]

/-- **The set $f(\vec{x}) \le M$ is convex** (Cassels, Ch. 12, §1, p. 260), for a positive semi-definite form $f$ with
matrix $F$ and every real $M$ (it is empty for $M < 0$). Proved from the triangle inequality for $\sqrt f$
(`sqrt_val_add_le`). -/
@[kb "cassels1978" "Ch. 12, §1, p. 260 (the set f(x) ≤ M is convex)"]
theorem convex_val_sublevel {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosSemidef) (M : ℝ) :
    Convex ℝ {x : Fin n → ℝ | val F x ≤ M} := by
  intro x hx y hy a b ha hb hab
  have hnn := ((posSemidef_iff F).1 hF).2
  have hxM : val F x ≤ M := hx
  have hyM : val F y ≤ M := hy
  have hM : 0 ≤ M := (hnn x).trans hxM
  show val F (a • x + b • y) ≤ M
  have h1 := sqrt_val_add_le hF (a • x) (b • y)
  rw [sqrt_val_smul, sqrt_val_smul, abs_of_nonneg ha, abs_of_nonneg hb] at h1
  have hsx : Real.sqrt (val F x) ≤ Real.sqrt M := Real.sqrt_le_sqrt hxM
  have hsy : Real.sqrt (val F y) ≤ Real.sqrt M := Real.sqrt_le_sqrt hyM
  have h2 : Real.sqrt (val F (a • x + b • y)) ≤ Real.sqrt M := by
    calc _ ≤ a * Real.sqrt (val F x) + b * Real.sqrt (val F y) := h1
      _ ≤ a * Real.sqrt M + b * Real.sqrt M := by gcongr
      _ = Real.sqrt M := by rw [← add_mul, hab, one_mul]
  exact (Real.sqrt_le_sqrt_iff hM).1 h2

/-- **The set $f(\vec{x}) \le M$ is bounded iff $f$ is strictly definite** (Cassels, Ch. 12, §1, p. 260), for a positive
semi-definite form $f$ with matrix $F$ and a real $M \ge 0$: the set $\{\vec{x} \in \mathbb{R}^n : f(\vec{x}) \le M\}$
is bounded iff $F$ is strictly positive definite.
*Update:* the printed "for any $M$" needs $M \ge 0$ for the direction "bounded implies strictly definite": for $M < 0$ the
set is empty, hence bounded, whatever $f$ is. (Confirmed by the proof: the singular form $f = 0$ has empty level set for
$M = -1$.) -/
@[kb "cassels1978" "Ch. 12, §1, p. 260 (bounded iff f strictly definite)"]
theorem isBounded_val_sublevel_iff {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosSemidef) {M : ℝ} (hM : 0 ≤ M) :
    Bornology.IsBounded {x : Fin n → ℝ | val F x ≤ M} ↔ F.PosDef := by
  have hnn := ((posSemidef_iff F).1 hF).2
  constructor
  · intro hb
    by_contra hnpd
    have hsing : ∃ x : Fin n → ℝ, x ≠ 0 ∧ val F x = 0 := by
      by_contra hno
      push Not at hno
      exact hnpd ((posDef_iff F).2 ⟨((posSemidef_iff F).1 hF).1, fun x hx =>
        lt_of_le_of_ne (hnn x) (Ne.symm (hno x hx))⟩)
    obtain ⟨x0, hx0, hv0⟩ := hsing
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Fin n → ℝ)).1 hb
    have hn0 : 0 < ‖x0‖ := norm_pos_iff.2 hx0
    set t : ℝ := (|R| + 1) / ‖x0‖ with ht
    have hmem : t • x0 ∈ {x : Fin n → ℝ | val F x ≤ M} := by
      show val F (t • x0) ≤ M
      rw [val_smul, hv0]; simpa using hM
    have := hR hmem
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, ht, abs_of_pos (by positivity),
      div_mul_cancel₀ _ hn0.ne'] at this
    linarith [le_abs_self R]
  · intro hpd
    obtain ⟨K, hK, hKx⟩ := exists_val_ge hpd
    rw [Metric.isBounded_iff_subset_closedBall (0 : Fin n → ℝ)]
    refine ⟨Real.sqrt (M / K), fun x hx => ?_⟩
    have hxM : val F x ≤ M := hx
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    have h1 : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
      Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : x i ^ 2 ≤ M / K := by
      rw [le_div_iff₀ hK]; nlinarith [hKx x]
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt h2

/-! ### The cone of strictly definite forms (p. 271) -/

/-- **$d(f) > 0$ on $\mathcal P^\circ$** (Cassels, Ch. 12, §5, Note, p. 271): a strictly positive definite real symmetric
matrix has positive determinant. -/
@[kb "cassels1978" "Ch. 12, §5, Note, p. 271 (d(f) > 0 on 𝒫°)"]
theorem posDef_det_pos {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) : 0 < F.det :=
  hF.det_pos

/-- **$d(f) = 0$ on $\mathcal P \setminus \mathcal P^\circ$** (Cassels, Ch. 12, §5, Note, p. 271): a positive semi-definite
real symmetric matrix which is not strictly positive definite has determinant $0$. -/
@[kb "cassels1978" "Ch. 12, §5, Note, p. 271 (d(f) = 0 on 𝒫 − 𝒫°)"]
theorem det_eq_zero_of_posSemidef_not_posDef {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosSemidef) (hF' : ¬ F.PosDef) :
    F.det = 0 :=
  (posSemidef_not_posDef_iff_det_eq_zero hF).1 hF'

/-- **$\mathcal P^\circ$ is relatively closed in the nonsingular symmetric matrices** (Cassels, Ch. 12, §5, Note, p. 271):
there is a closed set $C \subseteq M_n(\mathbb{R})$ (the positive semi-definite matrices) with
$\mathcal P^\circ = C \cap \{F \text{ symmetric} : \det F \ne 0\}$. Together with `thm_5_1_open` ($\mathcal P^\circ$ is open
in the symmetric matrices) it says that $\mathcal P^\circ$ is open and closed in $\{d \ne 0\}$. -/
@[kb "cassels1978" "Ch. 12, §5, Note, p. 271 (𝒫° open and closed in {d ≠ 0})"]
theorem posDef_closed_in_nonsingular :
    ∃ C : Set (Matrix (Fin n) (Fin n) ℝ), IsClosed C ∧
      {F : Matrix (Fin n) (Fin n) ℝ | F.PosDef} = C ∩ {F | F.IsSymm ∧ F.det ≠ 0} := by
  refine ⟨{F | F.PosSemidef}, ?_, ?_⟩
  · have : {F : Matrix (Fin n) (Fin n) ℝ | F.PosSemidef} =
        {F | F.IsSymm} ∩ ⋂ x : Fin n → ℝ, {F | 0 ≤ val F x} := by
      ext F; simp [posSemidef_iff]
    rw [this]
    exact isClosed_isSymm.inter (isClosed_iInter fun x =>
      isClosed_le continuous_const (continuous_val_left x))
  · ext F
    constructor
    · intro hF
      exact ⟨hF.posSemidef, ((posSemidef_iff F).1 hF.posSemidef).1, (posDef_det_pos hF).ne'⟩
    · rintro ⟨hC, -, hd⟩
      exact (hC.posDef_iff_det_ne_zero).2 hd

/-- Helper: a nonsingular symmetric matrix which is not strictly positive definite takes a negative value. -/
theorem exists_val_neg_of_nonsingular {G : Matrix (Fin n) (Fin n) ℝ} (hs : G.IsSymm) (hd : G.det ≠ 0)
    (hG : ¬ G.PosDef) : ∃ x, val G x < 0 := by
  by_contra hno
  push Not at hno
  exact hG ((((posSemidef_iff G).2 ⟨hs, hno⟩).posDef_iff_det_ne_zero).2 hd)

/-- **$\mathcal P^\circ$ is a connected component of the complement of the hypersurface $d(f) = 0$** (Cassels, Ch. 12,
§5, Note, p. 271): in the space of symmetric matrices, the complement of the hypersurface is
$X = \{F \text{ symmetric} : \det F \ne 0\}$, and for every strictly positive definite $F_0$ the connected component of
$F_0$ in $X$ (Mathlib's `connectedComponentIn`) is exactly $\mathcal P^\circ$. Proof: $\mathcal P^\circ$ is convex
(`thm_5_1_convex`), hence connected, so it lies in the component; conversely the component is preconnected and is
covered by the two open sets $\{F : \exists \vec{x},\ f(\vec{x}) < 0\}$ and the open set $U$ of `thm_5_1_open`
(with $\mathcal P^\circ = U \cap \{\text{symmetric}\}$), which do not meet on symmetric matrices. -/
@[kb "cassels1978" "Ch. 12, §5, Note, p. 271 (𝒫° is one of the components of the complement of d(f) = 0)"]
theorem posDef_eq_connectedComponentIn {F₀ : Matrix (Fin n) (Fin n) ℝ} (h₀ : F₀.PosDef) :
    connectedComponentIn {F : Matrix (Fin n) (Fin n) ℝ | F.IsSymm ∧ F.det ≠ 0} F₀ = {F | F.PosDef} := by
  set X : Set (Matrix (Fin n) (Fin n) ℝ) := {F | F.IsSymm ∧ F.det ≠ 0} with hX
  have hsub : {F : Matrix (Fin n) (Fin n) ℝ | F.PosDef} ⊆ X := fun F hF =>
    ⟨((posSemidef_iff F).1 hF.posSemidef).1, (posDef_det_pos hF).ne'⟩
  apply Set.Subset.antisymm
  · obtain ⟨U, hUo, hU⟩ := thm_5_1_open (n := n)
    set V : Set (Matrix (Fin n) (Fin n) ℝ) := {F | ∃ x, val F x < 0} with hV
    have hVo : IsOpen V := by
      have : V = ⋃ x, {F : Matrix (Fin n) (Fin n) ℝ | val F x < 0} := by
        ext F; simp [hV]
      rw [this]
      exact isOpen_iUnion fun x => isOpen_lt (continuous_val_left x) continuous_const
    set s := connectedComponentIn X F₀ with hsdef
    have hs : IsPreconnected s := isPreconnected_connectedComponentIn
    have hsX : s ⊆ X := connectedComponentIn_subset _ _
    have hF₀s : F₀ ∈ s := mem_connectedComponentIn (hsub h₀)
    have hF₀U : F₀ ∈ U := by
      have : F₀ ∈ U ∩ {F | F.IsSymm} := by rw [← hU]; exact h₀
      exact this.1
    intro G hG
    by_contra hGn
    have hGV : G ∈ V := by
      obtain ⟨hGs, hGd⟩ := hsX hG
      exact exists_val_neg_of_nonsingular hGs hGd hGn
    have hcover : s ⊆ U ∪ V := by
      intro F hF
      by_cases hFp : F.PosDef
      · left
        have : F ∈ U ∩ {F | F.IsSymm} := by rw [← hU]; exact hFp
        exact this.1
      · right
        obtain ⟨hFs, hFd⟩ := hsX hF
        exact exists_val_neg_of_nonsingular hFs hFd hFp
    obtain ⟨F, hFs, hFU, x, hx⟩ := hs U V hUo hVo hcover ⟨F₀, hF₀s, hF₀U⟩ ⟨G, hG, hGV⟩
    have hFp : F.PosDef := by
      have : F ∈ U ∩ {F | F.IsSymm} := ⟨hFU, (hsX hFs).1⟩
      rw [← hU] at this
      exact this
    by_cases hx0 : x = 0
    · subst hx0; simp [val] at hx
    · exact absurd (((posDef_iff F).1 hFp).2 x hx0) (not_lt.2 hx.le)
  · exact thm_5_1_convex.isPreconnected.subset_connectedComponentIn h₀ hsub

/-! ### Convexity of the reduced domain and its images; neighbours (p. 279) -/

/-- **The set $\mathcal R$ of reduced forms is convex** (Cassels, Ch. 12, §7, p. 279, "the $T\mathcal R$ are convex" for
$T = 1$): the Minkowski-reduced matrices (`IsMinkowskiReduced`: strictly positive definite, and $f(\vec{e}^{\,*}) \ge f_{jj}$
for every $j$ and every integral $\vec{e}^{\,*}$ extending $e_0, \dots, e_{j-1}$ to a basis) form a convex set, since
the defining inequalities are linear in $F$ and $\mathcal P^\circ$ is convex (`thm_5_1_convex`). -/
@[kb "cassels1978" "Ch. 12, §7, p. 279 (𝓡 is convex)"]
theorem convex_isMinkowskiReduced :
    Convex ℝ {G : Matrix (Fin n) (Fin n) ℝ | IsMinkowskiReduced G} := by
  intro F hF G hG a b ha hb hab
  refine ⟨thm_5_1_convex hF.1 hG.1 ha hb hab, fun j e he => ?_⟩
  have h1 := hF.2 j e he
  have h2 := hG.2 j e he
  have hv : val (a • F + b • G) (cast e) = a * val F (cast e) + b * val G (cast e) := val_add_mat F G a b _
  rw [hv]
  have hd : (a • F + b • G) j j = a * F j j + b * G j j := by simp
  rw [hd]
  nlinarith

/-- Helper: `img T` is the image of the set of reduced forms under the linear map `actL7 T`. -/
theorem img_eq_actL7_image (T : GL (Fin n) ℤ) :
    img T = (actL7 T.val) '' {G | IsMinkowskiReduced G} := rfl

/-- **The sets $T\mathcal R$ are convex** (Cassels, Ch. 12, §7, p. 279): $T\mathcal R = \{T^{\mathsf T}GT : G \in \mathcal R\}$
(`img T`) is convex for every $T \in \mathrm{GL}_n(\mathbb{Z})$, being the image of the convex set $\mathcal R$ under the
linear map $F \mapsto T^{\mathsf T}FT$. -/
@[kb "cassels1978" "Ch. 12, §7, p. 279 (the sets T𝓡 are convex)"]
theorem convex_img (T : GL (Fin n) ℤ) : Convex ℝ (img T) := by
  rw [img_eq_actL7_image]
  exact convex_isMinkowskiReduced.linear_image _

/-- **The intersection $T_1\mathcal R \cap T_2\mathcal R$ is convex** (Cassels, Ch. 12, §7, p. 279). -/
@[kb "cassels1978" "Ch. 12, §7, p. 279 (T₁𝓡 ∩ T₂𝓡 is convex)"]
theorem convex_img_inter (T₁ T₂ : GL (Fin n) ℤ) : Convex ℝ (img T₁ ∩ img T₂) :=
  (convex_img T₁).inter (convex_img T₂)

/-- **Neighbours** (Cassels, Ch. 12, §7, p. 279): $T_1\mathcal R$ and $T_2\mathcal R$ (`img T₁`, `img T₂`) are
*neighbours* if their intersection has codimension $1$ in the space of forms. The space of forms (symmetric matrices) has
dimension $N = n(n+1)/2$; the intersection, a convex set, has codimension $1$ iff it is nonempty and its affine span
(inside $M_n(\mathbb{R})$, contained in the symmetric matrices) has dimension $N - 1$, i.e. the direction of the affine
span has real dimension $N - 1$ (stated as `dimension + 1 = N`, which avoids truncated subtraction). -/
@[kb "cassels1978" "Ch. 12, §7, p. 279 (neighbours: T₁𝓡 ∩ T₂𝓡 has codimension 1)"]
def AreNeighbours (T₁ T₂ : GL (Fin n) ℤ) : Prop :=
  (img T₁ ∩ img T₂).Nonempty ∧
    Module.finrank ℝ (affineSpan ℝ (img T₁ ∩ img T₂)).direction + 1 = n * (n + 1) / 2

/-- **The set $\Sigma'$** (Cassels, Ch. 12, §7, p. 279): the integral unimodular $S$ such that $\mathcal R$ and
$S\mathcal R$ are neighbours (`AreNeighbours 1 S`, as $1\cdot\mathcal R = \mathcal R$). -/
@[kb "cassels1978" "Ch. 12, §7, p. 279 (the set Σ′ of S with 𝓡 and S𝓡 neighbours)"]
def sigmaPrime (n : ℕ) : Set (GL (Fin n) ℤ) := {S | AreNeighbours (1 : GL (Fin n) ℤ) S}

/-- $\Sigma' \subseteq \Sigma$: if $\mathcal R$ and $S\mathcal R$ are neighbours they meet. -/
theorem sigmaPrime_subset_sigma (n : ℕ) : sigmaPrime n ⊆ sigma n := by
  rintro S ⟨⟨G, hG1, hG2⟩, -⟩
  refine ⟨G, ?_, hG2⟩
  obtain ⟨H, hH, rfl⟩ := hG1
  rw [Units.val_one, act_one]; exact hH

/-- Helper: `img (S * T)` is the image of `img S` under the substitution `T`. -/
theorem img_mul (S T : GL (Fin n) ℤ) : img (S * T) = actL7 T.val '' img S := by
  ext F
  constructor
  · rintro ⟨G, hG, rfl⟩
    exact ⟨act S.val G, ⟨G, hG, rfl⟩, by rw [Units.val_mul, act_mul]; rfl⟩
  · rintro ⟨_, ⟨G, hG, rfl⟩, rfl⟩
    exact ⟨G, hG, by rw [Units.val_mul, act_mul]; rfl⟩

/-- Helper: the substitution by an invertible integral matrix is a linear equivalence of the space of matrices. -/
noncomputable def actEquiv (T : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  LinearEquiv.ofLinearMap (actL7 T.val) (actL7 T⁻¹.val)
    (LinearMap.ext fun F => act_act_inv7 T F) (LinearMap.ext fun F => act_inv_act7 T F)

/-- **Neighbours are transported by substitutions** (Cassels, Ch. 12, §7, p. 279: "$T_1\mathcal R$, $T_2\mathcal R$ are
neighbours precisely when $T_1 = ST_2$ for some $S$ such that $\mathcal R$ and $S\mathcal R$ are neighbours", in the order of
composition of `Sec7.lean`, where $T(Sf) = (ST)f$): `img (S * T)` and `img T` are neighbours iff `img S` and `img 1`
are (the intersection is the image of $S\mathcal R \cap \mathcal R$ under the substitution $T$, a linear equivalence
preserving the dimension of affine spans); this says $S \in \Sigma'$ up to the order of the two sets. -/
@[kb "cassels1978" "Ch. 12, §7, p. 279 (T₁𝓡, T₂𝓡 neighbours iff T₁ = T₂S with S ∈ Σ′)"]
theorem areNeighbours_mul_iff (S T : GL (Fin n) ℤ) :
    AreNeighbours (S * T) T ↔ AreNeighbours S 1 := by
  have e1 : img T = actEquiv T '' img 1 := by
    have := img_mul 1 T
    rw [one_mul] at this
    rw [this]; rfl
  have e2 : img (S * T) = actEquiv T '' img S := by
    rw [img_mul]; rfl
  have h1 : img (S * T) ∩ img T = actEquiv T '' (img S ∩ img 1) := by
    rw [e2, e1, Set.image_inter (actEquiv T).injective]
  have hdim : ∀ A : Set (Matrix (Fin n) (Fin n) ℝ),
      Module.finrank ℝ (affineSpan ℝ (actEquiv T '' A)).direction =
        Module.finrank ℝ (affineSpan ℝ A).direction := by
    intro A
    have : (actEquiv T '' A) = (actEquiv T).toLinearMap.toAffineMap '' A := rfl
    rw [this, ← AffineSubspace.map_span, AffineSubspace.map_direction]
    exact LinearEquiv.finrank_map_eq (actEquiv T) _
  unfold AreNeighbours
  rw [h1, hdim, Set.image_nonempty]

end QuadFormsKB.Reduction
