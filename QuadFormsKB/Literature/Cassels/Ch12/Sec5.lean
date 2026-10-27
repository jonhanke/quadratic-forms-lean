/-
# Cassels, Chapter 12, §5: the geometry of definite and reduced forms

Cassels, *Rational Quadratic Forms* (1978), Ch. 12, §5, pp. 269–273, and Theorem 1.3 (p. 256).

A real form $f = \sum f_{ij}x_ix_j$ is the point $(f_{ij})_{i \le j}$ of $\mathbb{R}^{n(n+1)/2}$ (p. 269). Here the forms are
the symmetric matrices $F$; "open in $\mathbb{R}^{n(n+1)/2}$" is "open relative to the symmetric matrices"
(`IsOpenInSym`), and Cassels' linear inequalities in the $f_{ij}$ are inequalities between values $f(\vec{v})$ at
integral vectors, which are linear in $F$.

* Lemmas 5.1, 5.2 (`abs_val_le`; Lemma 5.2 is `exists_val_ge` in `Basic.lean`), Theorem 5.1 (`thm_5_1_convex`,
  `thm_5_1_open`, `thm_5_1_closure`).
* Strictly reduced forms (`IsStrictlyReduced`, p. 271) and the condition (5.4) (`isStrictlyReduced_iff`).
* Lemma 5.3 (`lemma_5_3_convex`, `lemma_5_3_open`, `lemma_5_3_closure`).
* The finite sets $W_j$ (`W`, p. 272), Theorem 5.2 (`thm_5_2`), its Corollary (`thm_5_2_cor`), Lemma 5.4
  (`lemma_5_4`), and Theorem 1.3 (`thm_1_3`).

Indices are 0-based (Cassels' $W_1, \dots, W_n$ are `W 0`, …, `W (n-1)`; his $f(e_1) > 0$ is $f_{00} > 0$).
-/
import QuadFormsKB.Literature.Cassels.Ch12.Sec4

open Matrix

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-- **Open relative to the symmetric matrices** (Cassels' "open subset of $\mathbb{R}^{n(n+1)/2}$", p. 270): a set $S$ of
symmetric real $n \times n$ matrices is the intersection of an open subset of $M_n(\mathbb{R})$ with the symmetric
matrices. (The symmetric matrices are a linear subspace isomorphic to $\mathbb{R}^{n(n+1)/2}$ by
$F \mapsto (f_{ij})_{i \le j}$.) -/
def IsOpenInSym (S : Set (Matrix (Fin n) (Fin n) ℝ)) : Prop :=
  ∃ U : Set (Matrix (Fin n) (Fin n) ℝ), IsOpen U ∧ S = U ∩ {F | F.IsSymm}

/-- **The norm $|f|$ of a form** (Cassels, Ch. 12, §5, p. 270): $|f|^2 = \sum_{i \le j} f_{ij}^2$, the euclidean length of
the point $(f_{ij})_{i \le j}$. -/
@[kb "cassels1978" "Ch. 12, §5, p. 270 (the euclidean length |f|)"]
noncomputable def formNorm (F : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, if i ≤ j then F i j ^ 2 else 0)

/-- Helper: $f$ is linear in the matrix $F$. -/
theorem val_add_mat (F G : Matrix (Fin n) (Fin n) ℝ) (a b : ℝ) (x : Fin n → ℝ) :
    val (a • F + b • G) x = a * val F x + b * val G x := by
  simp [val, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul]

/-- Helper: the form of the identity matrix is $\sum x_i^2$. -/
theorem val_one5 (x : Fin n → ℝ) : val (1 : Matrix (Fin n) (Fin n) ℝ) x = ∑ i, x i ^ 2 := by
  simp [val, dotProduct, sq]

/-- Helper: $(F, \vec{x}) \mapsto f(\vec{x})$ is continuous. -/
theorem continuous_val_pair :
    Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) => val p.1 p.2) := by
  unfold val Matrix.mulVec dotProduct
  fun_prop

/-- Helper: $F \mapsto f(\vec{x})$ is continuous. -/
theorem continuous_val_left (x : Fin n → ℝ) :
    Continuous (fun F : Matrix (Fin n) (Fin n) ℝ => val F x) :=
  (continuous_val_pair (n := n)).comp (Continuous.prodMk continuous_id (continuous_const (y := x)))

/-- Helper: the symmetric matrices form a closed set. -/
theorem isClosed_isSymm : IsClosed {F : Matrix (Fin n) (Fin n) ℝ | F.IsSymm} := by
  have : {F : Matrix (Fin n) (Fin n) ℝ | F.IsSymm} = {F | Fᵀ = F} := rfl
  rw [this]
  exact isClosed_eq (continuous_id.matrix_transpose) continuous_id

/-- **Lemma 5.1** (Cassels, Ch. 12, §5, p. 270): $|f(\vec{x})| \le 2|f|\,|\vec{x}|^2$ for every real symmetric $F$ and real
$\vec{x}$, where $|\vec{x}|^2 = \sum_i x_i^2$. -/
@[kb "cassels1978" "Ch. 12, §5, Lemma 5.1, p. 270"]
theorem abs_val_le {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsSymm) (x : Fin n → ℝ) :
    |val F x| ≤ 2 * formNorm F * ∑ i, x i ^ 2 := by
  set N : ℝ := ∑ i, ∑ j, if i ≤ j then F i j ^ 2 else 0 with hN
  have hN0 : 0 ≤ N :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  have hsymm : ∀ i j, F j i = F i j := fun i j => by
    have : Fᵀ = F := hF
    simpa using congrFun (congrFun this i) j
  have hS : ∑ i, ∑ j, F i j ^ 2 ≤ 2 * N := by
    have h1 : ∑ i, ∑ j, F i j ^ 2 = N + ∑ i, ∑ j, (if i ≤ j then 0 else F i j ^ 2) := by
      rw [hN, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    have h2 : ∑ i, ∑ j, (if i ≤ j then 0 else F i j ^ 2) ≤ N := by
      rw [Finset.sum_comm, hN]
      refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
      by_cases h : b ≤ a
      · rw [if_pos h]; split_ifs <;> positivity
      · have h' : a ≤ b := (not_le.1 h).le
        rw [if_neg h, if_pos h', hsymm]
    linarith
  have hCS : (val F x) ^ 2 ≤ (∑ i, ∑ j, F i j ^ 2) * (∑ i, x i ^ 2) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
      (fun p => F p.1 p.2) (fun p => x p.1 * x p.2)
    have e1 : val F x = ∑ p : Fin n × Fin n, F p.1 p.2 * (x p.1 * x p.2) := by
      rw [Fintype.sum_prod_type]
      simp only [val, dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have e2 : ∑ p : Fin n × Fin n, F p.1 p.2 ^ 2 = ∑ i, ∑ j, F i j ^ 2 := Fintype.sum_prod_type _
    have e3 : ∑ p : Fin n × Fin n, (x p.1 * x p.2) ^ 2 = (∑ i, x i ^ 2) ^ 2 := by
      rw [Fintype.sum_prod_type, sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e1]; rw [e2, e3] at h; exact h
  have hx0 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsq : (formNorm F) ^ 2 = N := Real.sq_sqrt hN0
  have hfn : 0 ≤ formNorm F := Real.sqrt_nonneg _
  apply abs_le_of_sq_le_sq _ (by positivity)
  calc (val F x) ^ 2 ≤ (∑ i, ∑ j, F i j ^ 2) * (∑ i, x i ^ 2) ^ 2 := hCS
    _ ≤ (2 * N) * (∑ i, x i ^ 2) ^ 2 := by gcongr
    _ ≤ (2 * formNorm F * ∑ i, x i ^ 2) ^ 2 := by
      rw [mul_pow, mul_pow, hsq]; nlinarith [sq_nonneg (∑ i, x i ^ 2)]

/-- Helper: the euclidean unit sphere $\{\vec{x} : \sum x_i^2 = 1\}$. -/
def unitSphere5 : Set (Fin n → ℝ) := {x | ∑ i, x i ^ 2 = 1}

/-- Helper: the unit sphere is compact. -/
theorem isCompact_unitSphere5 : IsCompact (unitSphere5 (n := n)) := by
  have hSc : IsClosed (unitSphere5 (n := n)) :=
    isClosed_eq (by fun_prop) continuous_const
  have hSb : Bornology.IsBounded (unitSphere5 (n := n)) := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun x hx => ?_⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : x i ^ 2 ≤ 1 := by
      have : x i ^ 2 ≤ ∑ i, x i ^ 2 :=
        Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
      have hx' : ∑ i, x i ^ 2 = 1 := hx
      linarith
    rw [Real.norm_eq_abs]
    exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith)
  exact Metric.isCompact_of_isClosed_isBounded hSc hSb

/-- Helper: a nonzero real vector has positive squared length. -/
theorem sum_sq_pos5 {x : Fin n → ℝ} (hx : x ≠ 0) : 0 < ∑ i, x i ^ 2 := by
  by_contra h
  apply hx
  have h0 : ∑ i, x i ^ 2 = 0 :=
    le_antisymm (not_lt.1 h) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  ext i
  simpa using (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))).1 h0 i (Finset.mem_univ i)

/-- Helper: points of the unit sphere are nonzero. -/
theorem ne_zero_of_mem_unitSphere5 {x : Fin n → ℝ} (hx : x ∈ unitSphere5) : x ≠ 0 := by
  rintro rfl
  have : ∑ i : Fin n, (0 : Fin n → ℝ) i ^ 2 = 1 := hx
  simp at this

/-- Helper: positivity on the unit sphere gives positivity at every nonzero vector. -/
theorem pos_of_sphere5 {F : Matrix (Fin n) (Fin n) ℝ} (h : ∀ x ∈ unitSphere5 (n := n), 0 < val F x)
    {x : Fin n → ℝ} (hx : x ≠ 0) : 0 < val F x := by
  have hpos := sum_sq_pos5 hx
  set r := Real.sqrt (∑ i, x i ^ 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hpos
  have hr2 : r ^ 2 = ∑ i, x i ^ 2 := Real.sq_sqrt hpos.le
  have hy : r⁻¹ • x ∈ unitSphere5 := by
    show ∑ i, (r⁻¹ • x) i ^ 2 = 1
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
    rw [← hr2]
    field_simp
  have h1 := h _ hy
  rw [val_smul] at h1
  have : val F x = r ^ 2 * ((r⁻¹) ^ 2 * val F x) := by field_simp
  rw [this]
  exact mul_pos (by positivity) h1

/-- Helper: $F + tI$ is strictly positive definite for semi-definite $F$ and $t > 0$. -/
theorem posDef_add_smul_one {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosSemidef) {t : ℝ} (ht : 0 < t) :
    (F + t • 1).PosDef := by
  obtain ⟨hs, hp⟩ := (posSemidef_iff F).1 hF
  rw [posDef_iff]
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 : Fᵀ = F := hs
    show (F + t • 1)ᵀ = F + t • 1
    rw [transpose_add, transpose_smul, transpose_one, h1]
  · have : F + t • (1 : Matrix (Fin n) (Fin n) ℝ) = (1 : ℝ) • F + t • 1 := by simp
    rw [this, val_add_mat, val_one5]
    have := sum_sq_pos5 hx
    nlinarith [hp x]

/-- **Theorem 5.1 (i), convexity** (Cassels, Ch. 12, p. 270): the set $\mathcal P^\circ$ of strictly positive definite
forms is convex. -/
@[kb "cassels1978" "Ch. 12, §5, Thm. 5.1 (i), p. 270"]
theorem thm_5_1_convex : Convex ℝ {F : Matrix (Fin n) (Fin n) ℝ | F.PosDef} := by
  intro F hF G hG a b ha hb hab
  obtain ⟨hFs, hFp⟩ := (posDef_iff F).1 hF
  obtain ⟨hGs, hGp⟩ := (posDef_iff G).1 hG
  rw [Set.mem_setOf_eq, posDef_iff]
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 : Fᵀ = F := hFs
    have h2 : Gᵀ = G := hGs
    show (a • F + b • G)ᵀ = a • F + b • G
    rw [transpose_add, transpose_smul, transpose_smul, h1, h2]
  · rw [val_add_mat]
    have h1 := hFp x hx
    have h2 := hGp x hx
    rcases ha.eq_or_lt with h0 | h0
    · have : b = 1 := by linarith
      subst this
      rw [← h0]
      linarith
    · nlinarith [mul_pos h0 h1, mul_nonneg hb h2.le]

/-- **Theorem 5.1 (i), openness** (Cassels, Ch. 12, pp. 270–271): $\mathcal P^\circ$ is open in the space of forms. -/
@[kb "cassels1978" "Ch. 12, §5, Thm. 5.1 (i), pp. 270–271"]
theorem thm_5_1_open : IsOpenInSym {F : Matrix (Fin n) (Fin n) ℝ | F.PosDef} := by
  have hU : IsOpen {F : Matrix (Fin n) (Fin n) ℝ | ∀ x ∈ unitSphere5 (n := n), 0 < val F x} := by
    rw [isOpen_iff_mem_nhds]
    intro F₀ hF₀
    have := (isCompact_unitSphere5 (n := n)).eventually_forall_of_forall_eventually (x₀ := F₀)
      (P := fun F x => 0 < val F x) (fun y hy =>
        continuous_val_pair.continuousAt.eventually (lt_mem_nhds (hF₀ y hy)))
    exact this
  refine ⟨_, hU, ?_⟩
  ext F
  constructor
  · intro hF
    obtain ⟨hs, hp⟩ := (posDef_iff F).1 hF
    exact ⟨fun x hx => hp x (ne_zero_of_mem_unitSphere5 hx), hs⟩
  · rintro ⟨hU', hs⟩
    exact (posDef_iff F).2 ⟨hs, fun x hx => pos_of_sphere5 hU' hx⟩

/-- **Theorem 5.1 (ii)** (Cassels, Ch. 12, p. 271): the closure of $\mathcal P^\circ$ is the set $\mathcal P$ of positive
definite or semi-definite forms. (Closure in $M_n(\mathbb{R})$; the symmetric matrices form a closed subspace, so this
is also the closure in $\mathbb{R}^{n(n+1)/2}$.) -/
@[kb "cassels1978" "Ch. 12, §5, Thm. 5.1 (ii), p. 271"]
theorem thm_5_1_closure :
    closure {F : Matrix (Fin n) (Fin n) ℝ | F.PosDef} = {F | F.PosSemidef} := by
  have hclosed : IsClosed {F : Matrix (Fin n) (Fin n) ℝ | F.PosSemidef} := by
    have : {F : Matrix (Fin n) (Fin n) ℝ | F.PosSemidef} =
        {F | F.IsSymm} ∩ ⋂ x : Fin n → ℝ, {F | 0 ≤ val F x} := by
      ext F; simp [posSemidef_iff]
    rw [this]
    exact isClosed_isSymm.inter (isClosed_iInter fun x =>
      isClosed_le continuous_const (continuous_val_left x))
  apply Set.Subset.antisymm
  · exact closure_minimal (fun F hF => hF.posSemidef) hclosed
  · intro F hF
    refine mem_closure_of_tendsto (b := nhdsWithin (0 : ℝ) (Set.Ioi 0)) (f := fun t : ℝ => F + t • 1) ?_ ?_
    · exact ((continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 F
        (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact posDef_add_smul_one hF ht

/-- **Diagonal unimodular matrices**: $T = \mathrm{diag}(\pm1, \dots, \pm1)$, the substitutions
$x_i \mapsto \pm x_i$. -/
def IsSignDiagonal (T : GL (Fin n) ℤ) : Prop :=
  ∃ d : Fin n → ℤ, (∀ i, d i = 1 ∨ d i = -1) ∧ T.val = diagonal d

/-- **Strictly reduced form** (Cassels, Ch. 12, §5, Definition, p. 271): $f$ is Minkowski-reduced and the only
$T \in \mathrm{GL}_n(\mathbb{Z})$ for which $f(T\vec{x})$ is also reduced are the diagonal matrices with entries $\pm1$.
Equivalent to (5.4) (`isStrictlyReduced_iff`). -/
@[kb "cassels1978" "Ch. 12, §5, Definition (strictly reduced), p. 271"]
def IsStrictlyReduced (F : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsMinkowskiReduced F ∧ ∀ T : GL (Fin n) ℤ, IsMinkowskiReduced (act T.val F) → IsSignDiagonal T

/-- Helper: casting a negated integral vector. -/
theorem cast_neg5 (e : Fin n → ℤ) : cast (-e) = (-1 : ℝ) • cast e := by
  funext k
  simp [cast]

/-- Helper: $f(-\vec{x}) = f(\vec{x})$ for an integral vector. -/
theorem val_cast_neg5 (F : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℤ) :
    val F (cast (-e)) = val F (cast e) := by
  rw [cast_neg5, val_smul]; simp

/-- Helper: the element $\mathrm{diag}(d_0, \dots, d_{n-1})$ of $\mathrm{GL}_n(\mathbb{Z})$ for signs $d_i = \pm 1$. -/
def signGL (d : Fin n → ℤ) (hd : ∀ i, d i = 1 ∨ d i = -1) : GL (Fin n) ℤ :=
  ⟨diagonal d, diagonal d, by
    rw [diagonal_mul_diagonal]
    convert (diagonal_one : (diagonal (fun _ : Fin n => (1 : ℤ))) = 1)
    rename_i i; rcases hd i with h | h <;> simp [h], by
    rw [diagonal_mul_diagonal]
    convert (diagonal_one : (diagonal (fun _ : Fin n => (1 : ℤ))) = 1)
    rename_i i; rcases hd i with h | h <;> simp [h]⟩

/-- Helper: a unimodular matrix whose columns $i < j$ are $\pm e_i$ has column $j$ extending $e_0, \dots, e_{j-1}$
(multiply by the sign matrix to turn $\pm e_i$ into $e_i$). -/
theorem extendsBasis_col (U : GL (Fin n) ℤ) (j : Fin n) (d : Fin n → ℤ) (hd : ∀ i, d i = 1 ∨ d i = -1)
    (hU : ∀ i < j, ∀ k, U.val k i = d i * (Pi.single i 1 : Fin n → ℤ) k) :
    ExtendsBasis j (fun k => U.val k j) := by
  have hd' : ∀ i, (if i < j then d i else 1) = 1 ∨ (if i < j then d i else 1) = -1 := by
    intro i; split_ifs
    · exact hd i
    · exact Or.inl rfl
  refine ⟨U * signGL _ hd', fun i hi k => ?_, fun k => ?_⟩
  · simp only [Units.val_mul, signGL, Matrix.mul_diagonal, if_pos hi, hU i hi k]
    rcases hd i with h | h <;> simp [h]
  · simp [Units.val_mul, signGL, Matrix.mul_diagonal]

/-- Helper: the inverse of such a matrix has the same columns $i < j$. -/
theorem inv_col (U : GL (Fin n) ℤ) (j : Fin n) (d : Fin n → ℤ) (hd : ∀ i, d i = 1 ∨ d i = -1)
    (hU : ∀ i < j, ∀ k, U.val k i = d i * (Pi.single i 1 : Fin n → ℤ) k) :
    ∀ i < j, ∀ k, U⁻¹.val k i = d i * (Pi.single i 1 : Fin n → ℤ) k := by
  intro i hi k
  have h1 := congrFun (congrFun (Units.inv_mul U) k) i
  simp only [Matrix.mul_apply, hU i hi] at h1
  have h2 : U⁻¹.val k i * d i = (1 : Matrix (Fin n) (Fin n) ℤ) k i := by
    rw [← h1]
    simp [Pi.single_apply]
  have hdd : d i * d i = 1 := by rcases hd i with h | h <;> simp [h]
  calc U⁻¹.val k i = U⁻¹.val k i * (d i * d i) := by rw [hdd, mul_one]
    _ = (U⁻¹.val k i * d i) * d i := by ring
    _ = (1 : Matrix (Fin n) (Fin n) ℤ) k i * d i := by rw [h2]
    _ = d i * (Pi.single i 1 : Fin n → ℤ) k := by
      by_cases hk : k = i <;> simp [Matrix.one_apply, Pi.single_apply, hk, mul_comm]

/-- Helper: if $F$ is reduced and $\vec{e}^{\,*}$ extends $e_0, \dots, e_{j-1}$ with $f(\vec{e}^{\,*}) \le f_{jj}$, there is
$T \in \mathrm{GL}_n(\mathbb{Z})$ with columns $e_0, \dots, e_{j-1}, \vec{e}^{\,*}$ (in positions $0, \dots, j$) such that
$f(T\vec{x})$ is again reduced. -/
theorem exists_reduced_col {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsMinkowskiReduced F) {j : Fin n}
    {e : Fin n → ℤ} (he : ExtendsBasis j e) (hle : val F (cast e) ≤ F j j) :
    ∃ T : GL (Fin n) ℤ, (∀ i < j, ∀ k, T.val k i = (Pi.single i 1 : Fin n → ℤ) k) ∧ (∀ k, T.val k j = e k) ∧
      IsMinkowskiReduced (act T.val F) := by
  obtain ⟨U, hU1, hU2⟩ := he
  have hGp : (act U.val F).PosDef := PosDef.act hF.1 U
  have hcolj : U.val *ᵥ Pi.single j 1 = e := by
    funext a
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, hU2 a]
  have h0 : ∀ i : Fin n, i.val < j.val + 1 → ∀ e', ExtendsBasis i e' →
      act U.val F i i ≤ val (act U.val F) (cast e') := by
    intro i hi e' he'
    rw [act_diag, val_act, castM_mulVec_cast]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hij | hij
    · have hcol : U.val *ᵥ Pi.single i 1 = Pi.single i 1 :=
        mulVec_single_of_col _ i (hU1 i (Fin.lt_def.2 hij))
      rw [hcol, cast_single, val_single]
      exact hF.2 i _ (he'.mulVec U (fun i' hi' => hU1 i' (hi'.trans (Fin.lt_def.2 hij))))
    · have : i = j := Fin.ext hij
      subst this
      rw [hcolj]
      exact hle.trans (hF.2 i _ (he'.mulVec U hU1))
  obtain ⟨V, hV1, hV2⟩ := exists_reduced_from hGp (j.val + 1) h0 n (by have := j.2; omega)
  refine ⟨U * V, fun i hi k => ?_, fun k => ?_, ?_⟩
  · have hi' : i.val < j.val + 1 := by have := Fin.lt_def.1 hi; omega
    rw [Units.val_mul, Matrix.mul_apply]
    simp only [hV1 i hi']
    simp [Pi.single_apply, hU1 i hi k]
  · have hj' : j.val < j.val + 1 := Nat.lt_succ_self _
    rw [Units.val_mul, Matrix.mul_apply]
    simp only [hV1 j hj']
    simp [Pi.single_apply, hU2 k]
  · rw [Units.val_mul, act_mul]
    exact ⟨PosDef.act hGp V, fun j' e' he' => hV2 j' j'.2 e' he'⟩

/-- **Strict reduction by (5.4)** (Cassels, Ch. 12, p. 271, "in other words"): $f$ is strictly reduced iff it is
strictly positive definite and $f(\vec{e}^{\,*}) > f(e_j)$ whenever $\vec{e}^{\,*}$ extends $e_0, \dots, e_{j-1}$ to a basis
and $\vec{e}^{\,*} \ne \pm e_j$. -/
@[kb "cassels1978" "Ch. 12, §5, Definition and (5.4), p. 271"]
theorem isStrictlyReduced_iff (F : Matrix (Fin n) (Fin n) ℝ) :
    IsStrictlyReduced F ↔ F.PosDef ∧ ∀ j : Fin n, ∀ e : Fin n → ℤ, ExtendsBasis j e →
      e ≠ Pi.single j 1 → e ≠ -Pi.single j 1 → F j j < val F (cast e) := by
  constructor
  · rintro ⟨hR, hS⟩
    refine ⟨hR.1, fun j e he hne1 hne2 => ?_⟩
    rcases (hR.2 j e he).lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨T, hT1, hT2, hTR⟩ := exists_reduced_col hR he h.symm.le
      obtain ⟨d, hd, hTd⟩ := hS T hTR
      have hcol : ∀ k, e k = if k = j then d j else 0 := by
        intro k
        rw [← hT2 k, hTd]
        by_cases hk : k = j
        · subst hk; simp
        · simp [diagonal_apply, hk]
      rcases hd j with h1 | h1
      · apply hne1; funext k; rw [hcol k]; by_cases hk : k = j <;> simp [hk, h1, Pi.single_apply]
      · apply hne2; funext k; rw [hcol k]; by_cases hk : k = j <;> simp [hk, h1, Pi.single_apply]
  · rintro ⟨hP, h54⟩
    have hR : IsMinkowskiReduced F := ⟨hP, fun j e he => by
      by_cases h1 : e = Pi.single j 1
      · subst h1; rw [cast_single, val_single]
      by_cases h2 : e = -Pi.single j 1
      · subst h2; rw [val_cast_neg5, cast_single, val_single]
      · exact (h54 j e he h1 h2).le⟩
    refine ⟨hR, fun T hT => ?_⟩
    have key : ∀ m : ℕ, m ≤ n → ∃ d : Fin n → ℤ, (∀ i, d i = 1 ∨ d i = -1) ∧
        ∀ i : Fin n, i.val < m → ∀ k, T.val k i = d i * (Pi.single i 1 : Fin n → ℤ) k := by
      intro m
      induction m with
      | zero => intro _; exact ⟨fun _ => 1, fun _ => Or.inl rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
      | succ m ih =>
        intro hm
        obtain ⟨d, hd, hT'⟩ := ih (by omega)
        set j : Fin n := ⟨m, by omega⟩ with hj
        have hcolT : ∀ i < j, ∀ k, T.val k i = d i * (Pi.single i 1 : Fin n → ℤ) k :=
          fun i hi => hT' i (Fin.lt_def.1 hi)
        have e1 := extendsBasis_col T j d hd hcolT
        have e2 := extendsBasis_col T⁻¹ j d hd (inv_col T j d hd hcolT)
        have h1 := hR.2 j _ e1
        have h2 := hT.2 j _ e2
        rw [act_diag, val_act, castM_mulVec_cast] at h2
        have ht : T.val *ᵥ Pi.single j 1 = fun k => T.val k j := by
          funext k; exact mulVec_single_apply _ _ _
        have ht' : T.val *ᵥ (fun k => T⁻¹.val k j) = Pi.single j 1 := by
          have : (fun k => T⁻¹.val k j) = T⁻¹.val *ᵥ Pi.single j 1 := by
            funext k; exact (mulVec_single_apply _ _ _).symm
          rw [this, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
        rw [ht, ht', cast_single, val_single] at h2
        have hEq : val F (cast fun k => T.val k j) = F j j := le_antisymm h2 h1
        obtain ⟨s, hs, hcol⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
            ∀ k, T.val k j = s * (Pi.single j 1 : Fin n → ℤ) k := by
          by_cases hp : (fun k => T.val k j) = Pi.single j 1
          · exact ⟨1, Or.inl rfl, fun k => by simpa using congrFun hp k⟩
          by_cases hq : (fun k => T.val k j) = -Pi.single j 1
          · exact ⟨-1, Or.inr rfl, fun k => by simpa using congrFun hq k⟩
          exact absurd hEq (h54 j _ e1 hp hq).ne'
        refine ⟨Function.update d j s, ?_, ?_⟩
        · intro i
          by_cases hij : i = j
          · subst hij; simpa using hs
          · rw [Function.update_of_ne hij]; exact hd i
        · intro i hi k
          by_cases hij : i = j
          · subst hij; simpa using hcol k
          · have : i.val < m := by
              have : i.val ≠ m := fun h => hij (Fin.ext h)
              omega
            rw [Function.update_of_ne hij]; exact hT' i this k
    obtain ⟨d, hd, hT'⟩ := key n le_rfl
    refine ⟨d, hd, ?_⟩
    ext a b
    rw [hT' b b.2 a]
    by_cases hab : a = b
    · subst hab; simp
    · simp [diagonal_apply, Pi.single_apply, hab, Ne.symm hab]

/-- There are strictly reduced forms, e.g. $\sum_i (1 + \tfrac{i}{n+1})x_i^2$ (used in Lemma 5.3, Theorem 5.2 and Theorems 7.2, 7.7). *Proof:* an $\vec{e}^{\,*} \ne \pm e_j$ extending
$e_0, \dots, e_{j-1}$ either has two nonzero coordinates, so $f(\vec{e}^{\,*}) \ge 2 > f_{jj}$, or is $\pm e_k$ with $k > j$. -/
theorem exists_isStrictlyReduced (n : ℕ) : ∃ F : Matrix (Fin n) (Fin n) ℝ, IsStrictlyReduced F := by
  set lam : Fin n → ℝ := fun i => 1 + (i.val : ℝ) / (n + 1) with hlam
  have hlam1 : ∀ i, 1 ≤ lam i := fun i => by
    simp only [hlam]; have : (0 : ℝ) ≤ (i.val : ℝ) / (n + 1) := by positivity
    linarith
  have hlam2 : ∀ i, lam i < 2 := fun i => by
    simp only [hlam]
    have : (i.val : ℝ) / (n + 1) < 1 := by
      rw [div_lt_one (by positivity)]
      have : (i.val : ℝ) < n := by exact_mod_cast i.2
      linarith
    linarith
  have hlamlt : ∀ i k, i < k → lam i < lam k := fun i k hik => by
    simp only [hlam]
    have : (i.val : ℝ) < k.val := by exact_mod_cast hik
    have := div_lt_div_of_pos_right this (show (0 : ℝ) < n + 1 by positivity)
    linarith
  have hval : ∀ x : Fin n → ℝ, val (diagonal lam) x = ∑ i, lam i * x i ^ 2 := by
    intro x
    simp [val, dotProduct, Matrix.mulVec, diagonal_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine ⟨diagonal lam, (isStrictlyReduced_iff _).2 ⟨?_, ?_⟩⟩
  · rw [posDef_iff]
    refine ⟨by simp [Matrix.IsSymm], fun x hx => ?_⟩
    rw [hval]
    have := sum_sq_pos5 hx
    calc 0 < ∑ i, x i ^ 2 := this
      _ ≤ ∑ i, lam i * x i ^ 2 := Finset.sum_le_sum fun i _ => by
          nlinarith [hlam1 i, sq_nonneg (x i)]
  · intro j e he hne1 hne2
    have hg : (Finset.univ.filter fun k : Fin n => j ≤ k).gcd e = 1 := (extendsBasis_iff_gcd j e).1 he
    have hdj : (diagonal lam) j j = lam j := by simp
    rw [hdj, hval]
    have hsq : ∀ a, e a ≠ 0 → (1 : ℝ) ≤ (e a : ℝ) ^ 2 := by
      intro a ha
      have : (1 : ℤ) ≤ e a ^ 2 := by
        have := Int.one_le_abs ha
        nlinarith [sq_abs (e a)]
      exact_mod_cast this
    by_cases h2 : ∃ a b, a ≠ b ∧ e a ≠ 0 ∧ e b ≠ 0
    · obtain ⟨a, b, hab, ha, hb⟩ := h2
      have hsub : ∑ i ∈ ({a, b} : Finset (Fin n)), lam i * (e i : ℝ) ^ 2 ≤ ∑ i, lam i * (e i : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => by
          have := hlam1 i; positivity)
      rw [Finset.sum_pair hab] at hsub
      have h1 := hsq a ha
      have h2 := hsq b hb
      have := hlam1 a
      have := hlam1 b
      have := hlam2 j
      calc lam j < 2 := hlam2 j
        _ ≤ _ := by simp only [cast]; nlinarith
    · push_neg at h2
      have hex : ∃ l, j ≤ l ∧ e l ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        have : (Finset.univ.filter fun k : Fin n => j ≤ k).gcd e = 0 :=
          Finset.gcd_eq_zero_iff.2 (fun k hk => hcon k (Finset.mem_filter.1 hk).2)
        rw [hg] at this
        exact one_ne_zero this
      obtain ⟨l, hl, hel⟩ := hex
      have hzero : ∀ t, t ≠ l → e t = 0 := by
        intro t htl
        by_contra hne
        exact hel (h2 t l htl hne)
      have hunit : e l = 1 ∨ e l = -1 := by
        have hd : e l ∣ (Finset.univ.filter fun k : Fin n => j ≤ k).gcd e := by
          apply Finset.dvd_gcd
          intro t _
          by_cases htl : t = l
          · rw [htl]
          · rw [hzero t htl]; exact dvd_zero _
        rw [hg] at hd
        exact Int.isUnit_iff.1 (isUnit_of_dvd_one hd)
      have hlj : j < l := by
        rcases hl.lt_or_eq with h | h
        · exact h
        · exfalso
          subst h
          rcases hunit with h | h
          · apply hne1; funext k; by_cases hk : k = j
            · rw [hk]; simp [h]
            · simp [hzero k hk, Pi.single_apply, hk]
          · apply hne2; funext k; by_cases hk : k = j
            · rw [hk]; simp [h]
            · simp [hzero k hk, Pi.single_apply, hk]
      have hsum : ∑ i, lam i * (e i : ℝ) ^ 2 = lam l * (e l : ℝ) ^ 2 := by
        rw [Finset.sum_eq_single l]
        · intro t _ htl; simp [hzero t htl]
        · intro h; exact absurd (Finset.mem_univ l) h
      rw [hsum]
      have : (e l : ℝ) ^ 2 = 1 := by rcases hunit with h | h <;> simp [h]
      rw [this, mul_one]
      exact hlamlt j l hlj

/-- **Lemma 5.3 (i), convexity** (Cassels, Ch. 12, p. 271): the set $\mathcal R^\circ$ of strictly reduced forms is
convex. -/
@[kb "cassels1978" "Ch. 12, §5, Lemma 5.3 (i), p. 271"]
theorem lemma_5_3_convex : Convex ℝ {F : Matrix (Fin n) (Fin n) ℝ | IsStrictlyReduced F} := by
  intro F hF G hG a b ha hb hab
  rw [Set.mem_setOf_eq, isStrictlyReduced_iff] at hF hG ⊢
  refine ⟨thm_5_1_convex hF.1 hG.1 ha hb hab, fun j e he h1 h2 => ?_⟩
  have e1 := hF.2 j e he h1 h2
  have e2 := hG.2 j e he h1 h2
  have hj : (a • F + b • G) j j = a * F j j + b * G j j := by simp
  rw [hj, val_add_mat]
  rcases ha.eq_or_lt with h0 | h0
  · have : b = 1 := by linarith
    subst this
    rw [← h0]
    linarith
  · nlinarith [mul_pos h0 (sub_pos.2 e1), mul_nonneg hb (sub_pos.2 e2).le]

/-- Helper: the $\ell^1$ norm of the entries of a matrix. -/
def N1 (G : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, |G i j|

/-- Helper: $|g(\vec{x})| \le \|G\|_1 |\vec{x}|^2$ (a cruder version of Lemma 5.1, valid for every matrix). -/
theorem abs_val_le_N1 (G : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    |val G x| ≤ N1 G * ∑ i, x i ^ 2 := by
  set S : ℝ := ∑ i, x i ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hxx : ∀ i j, |x i * x j| ≤ S := by
    intro i j
    apply abs_le_of_sq_le_sq _ hS0
    have hi : x i ^ 2 ≤ S :=
      Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
    have hj : x j ^ 2 ≤ S :=
      Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    calc (x i * x j) ^ 2 = x i ^ 2 * x j ^ 2 := by ring
      _ ≤ S * S := mul_le_mul hi hj (sq_nonneg _) hS0
      _ = S ^ 2 := by ring
  have e1 : val G x = ∑ i, ∑ j, x i * (G i j * x j) := by
    simp only [val, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [e1]
  calc |∑ i, ∑ j, x i * (G i j * x j)|
      ≤ ∑ i, |∑ j, x i * (G i j * x j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |x i * (G i j * x j)| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |G i j| * S := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
        have : |x i * (G i j * x j)| = |G i j| * |x i * x j| := by
          rw [← abs_mul]; congr 1; ring
        rw [this]
        exact mul_le_mul_of_nonneg_left (hxx i j) (abs_nonneg _)
    _ = N1 G * S := by simp [N1, Finset.sum_mul]

/-- Helper: $(f - g)(\vec{x}) = f(\vec{x}) - g(\vec{x})$. -/
theorem val_sub (F G : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : val (F - G) x = val F x - val G x := by
  simp [val, Matrix.sub_mulVec, dotProduct_sub]

/-- Helper: a set of symmetric matrices that is locally the trace of open sets is open relative to the symmetric
matrices. -/
theorem isOpenInSym_of_local {S : Set (Matrix (Fin n) (Fin n) ℝ)} (hsub : ∀ F ∈ S, F.IsSymm)
    (h : ∀ F ∈ S, ∃ V : Set (Matrix (Fin n) (Fin n) ℝ), IsOpen V ∧ F ∈ V ∧ ∀ G ∈ V, G.IsSymm → G ∈ S) :
    IsOpenInSym S := by
  choose! V hVo hFV hVS using h
  refine ⟨⋃ F ∈ S, V F, isOpen_biUnion fun F hF => hVo F hF, ?_⟩
  ext G
  constructor
  · intro hG
    exact ⟨Set.mem_biUnion hG (hFV G hG), hsub G hG⟩
  · rintro ⟨hU, hs⟩
    obtain ⟨F, hF, hGV⟩ := Set.mem_iUnion₂.1 hU
    exact hVS F hF G hGV hs

/-- **Lemma 5.3 (i), openness** (Cassels, Ch. 12, p. 271). -/
@[kb "cassels1978" "Ch. 12, §5, Lemma 5.3 (i), p. 271"]
theorem lemma_5_3_open : IsOpenInSym {F : Matrix (Fin n) (Fin n) ℝ | IsStrictlyReduced F} := by
  apply isOpenInSym_of_local
  · intro F hF
    exact ((posDef_iff F).1 ((isStrictlyReduced_iff F).1 hF).1).1
  · intro F₀ hF₀
    obtain ⟨hP, h54⟩ := (isStrictlyReduced_iff F₀).1 hF₀
    obtain ⟨K, hK, hKx⟩ := exists_val_ge hP
    set B : ℝ := ∑ j, |F₀ j j| with hB
    set X : ℝ := 2 * (B + 1) / K with hX
    have hone : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef :=
      (posDef_iff _).2 ⟨by simp [Matrix.IsSymm], fun x hx => by rw [val_one5]; exact sum_sq_pos5 hx⟩
    set Q : Set (Fin n × (Fin n → ℤ)) := {p | val 1 (cast p.2) ≤ X ∧ ExtendsBasis p.1 p.2 ∧
      p.2 ≠ Pi.single p.1 1 ∧ p.2 ≠ -Pi.single p.1 1} with hQ
    have hQfin : Q.Finite := by
      refine (Set.finite_univ.prod (finite_val_le hone X)).subset ?_
      rintro ⟨j, e⟩ ⟨h1, _⟩
      exact ⟨Set.mem_univ _, h1⟩
    refine ⟨{F | N1 (F - F₀) < min (K / 2) 1} ∩ ⋂ p ∈ Q, {F | F p.1 p.1 < val F (cast p.2)}, ?_, ?_, ?_⟩
    · refine (isOpen_lt ?_ continuous_const).inter (hQfin.isOpen_biInter fun p _ => isOpen_lt ?_ ?_)
      · unfold N1; fun_prop
      · fun_prop
      · exact continuous_val_left _
    · refine ⟨by simp [N1, hK], ?_⟩
      simp only [Set.mem_iInter]
      intro p hp
      exact h54 p.1 p.2 hp.2.1 hp.2.2.1 hp.2.2.2
    · rintro F ⟨hF1, hF2⟩ hFs
      have hN : N1 (F - F₀) < min (K / 2) 1 := hF1
      have hN1 : N1 (F - F₀) < K / 2 := lt_of_lt_of_le hN (min_le_left _ _)
      have hN2 : N1 (F - F₀) < 1 := lt_of_lt_of_le hN (min_le_right _ _)
      have hbound : ∀ x, K / 2 * ∑ i, x i ^ 2 ≤ val F x := by
        intro x
        have h1 := abs_val_le_N1 (F - F₀) x
        have h2 := hKx x
        have hS : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
        rw [val_sub] at h1
        have h3 := (abs_le.1 h1).1
        nlinarith [mul_le_mul_of_nonneg_right hN1.le hS]
      have hdiag : ∀ j, F j j ≤ B + 1 := by
        intro j
        have h1 := abs_val_le_N1 (F - F₀) (Pi.single j 1)
        rw [val_sub, val_single, val_single] at h1
        have hsum : ∑ i, (Pi.single j (1 : ℝ) : Fin n → ℝ) i ^ 2 = 1 := by
          simp [Pi.single_apply]
        rw [hsum, mul_one] at h1
        have h2 := (abs_le.1 h1).2
        have h3 : F₀ j j ≤ B :=
          (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |F₀ j j|)
            (fun _ _ => abs_nonneg _) (Finset.mem_univ j))
        linarith
      rw [Set.mem_setOf_eq, isStrictlyReduced_iff]
      refine ⟨(posDef_iff F).2 ⟨hFs, fun x hx => ?_⟩, fun j e he h1 h2 => ?_⟩
      · have := sum_sq_pos5 hx
        have := hbound x
        nlinarith
      · by_cases hXe : val 1 (cast e) ≤ X
        · have hmem : (j, e) ∈ Q := ⟨hXe, he, h1, h2⟩
          simp only [Set.mem_iInter] at hF2
          exact hF2 (j, e) hmem
        · have hlt : X < ∑ i, (cast e i) ^ 2 := by rw [← val_one5]; exact not_le.1 hXe
          have := hbound (cast e)
          have hKX : K / 2 * X = B + 1 := by rw [hX]; field_simp
          have := hdiag j
          nlinarith

/-- Helper: the segment $(1-t)F + tF_0$ tends to $F$ as $t \to 0^+$. -/
theorem tendsto_path (F F₀ : Matrix (Fin n) (Fin n) ℝ) :
    Filter.Tendsto (fun t : ℝ => (1 - t) • F + t • F₀) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F) := by
  have hc : Continuous (fun t : ℝ => (1 - t) • F + t • F₀) :=
    ((continuous_const.sub continuous_id).smul continuous_const).add (continuous_id.smul continuous_const)
  have := hc.tendsto 0
  simp only [sub_zero, one_smul, zero_smul, add_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- **Lemma 5.3 (ii)** (Cassels, Ch. 12, pp. 271–272): the set $\mathcal R$ of reduced forms is the relative closure of
$\mathcal R^\circ$ in $\mathcal P^\circ$: $\mathcal R = \overline{\mathcal R^\circ} \cap \mathcal P^\circ$. -/
@[kb "cassels1978" "Ch. 12, §5, Lemma 5.3 (ii), pp. 271–272"]
theorem lemma_5_3_closure :
    {F : Matrix (Fin n) (Fin n) ℝ | IsMinkowskiReduced F} =
      closure {F | IsStrictlyReduced F} ∩ {F | F.PosDef} := by
  ext F
  constructor
  · intro hF
    refine ⟨?_, hF.1⟩
    obtain ⟨F₀, hF₀⟩ := exists_isStrictlyReduced n
    obtain ⟨hP₀, h₀⟩ := (isStrictlyReduced_iff F₀).1 hF₀
    refine mem_closure_of_tendsto (tendsto_path F F₀) ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    rw [isStrictlyReduced_iff]
    have hcv : (1 - t) • F + t • F₀ ∈ {F : Matrix (Fin n) (Fin n) ℝ | F.PosDef} :=
      thm_5_1_convex hF.1 hP₀ (by linarith [ht.2]) ht.1.le (by ring)
    refine ⟨hcv, fun j e he h1 h2 => ?_⟩
    have e1 := hF.2 j e he
    have e2 := h₀ j e he h1 h2
    have hj : ((1 - t) • F + t • F₀) j j = (1 - t) * F j j + t * F₀ j j := by simp
    rw [hj, val_add_mat]
    nlinarith [mul_nonneg (sub_pos.2 ht.2).le (sub_nonneg.2 e1), mul_pos ht.1 (sub_pos.2 e2)]
  · rintro ⟨hcl, hP⟩
    refine ⟨hP, fun j e he => ?_⟩
    have hclosed : IsClosed {G : Matrix (Fin n) (Fin n) ℝ | G j j ≤ val G (cast e)} :=
      isClosed_le (by fun_prop) (continuous_val_left _)
    have hsub : {G : Matrix (Fin n) (Fin n) ℝ | IsStrictlyReduced G} ⊆
        {G | G j j ≤ val G (cast e)} := fun G hG => hG.1.2 j e he
    exact closure_minimal hsub hclosed hcl

/-- **The set $W_j$** (Cassels, Ch. 12, §5, Definition, p. 272; his $W_{j+1}$): the integral vectors $\vec{e}^{\,*}$ such
that (i) $e_0, \dots, e_{j-1}, \vec{e}^{\,*}$ extend to a basis $e_0, \dots, e_{j-1}, \vec{e}^{\,*}, e^*_{j+1}, \dots, e^*_{n-1}$ of
$\mathbb{Z}^n$ and (ii) some strictly positive definite form $f$ has both $f(\vec{x})$ and
$f(x_0e_0 + \dots + x_{j-1}e_{j-1} + x_j\vec{e}^{\,*} + x_{j+1}e^*_{j+1} + \cdots)$ reduced. In matrix terms: $\vec{e}^{\,*}$ is
column $j$ of some $T \in \mathrm{GL}_n(\mathbb{Z})$ whose columns $0, \dots, j-1$ are $e_0, \dots, e_{j-1}$ and with $F$ and
$T^{\mathsf T}FT$ both reduced for some $F$. Finite (`W_finite`). -/
@[kb "cassels1978" "Ch. 12, §5, Definition (the sets W_j), p. 272"]
def W (j : Fin n) : Set (Fin n → ℤ) :=
  {e | ∃ T : GL (Fin n) ℤ, (∀ i < j, ∀ k, T.val k i = (Pi.single i 1 : Fin n → ℤ) k) ∧ (∀ k, T.val k j = e k) ∧
    ∃ F, IsMinkowskiReduced F ∧ IsMinkowskiReduced (act T.val F)}

/-- **$W_j$ is finite** (Cassels, Ch. 12, p. 272, "by Theorem 1.2"). -/
@[kb "cassels1978" "Ch. 12, §5, Definition of W_j, p. 272 (finite by Thm. 1.2)"]
theorem W_finite (j : Fin n) : (W j).Finite := by
  refine ((finite_gl_reduced_pair n).image fun T : GL (Fin n) ℤ => fun k => T.val k j).subset ?_
  rintro e ⟨T, h1, h2, F, hF, hTF⟩
  exact ⟨T, ⟨F, hF, hTF⟩, funext h2⟩

/-- **Lemma 5.4** (Cassels, Ch. 12, §5, p. 273): if $f$ is positive semi-definite but not strictly definite, then
$\inf_{\vec{b} \in \mathbb{Z}^n \setminus 0} f(\vec{b}) = 0$: for every $\varepsilon > 0$ some nonzero integral $\vec{b}$ has
$f(\vec{b}) < \varepsilon$. (Cassels uses Minkowski's theorem on the set $f < \varepsilon$ of infinite volume; here
Theorem 2.1 is applied to $F + tI$ with $t \to 0$.) -/
@[kb "cassels1978" "Ch. 12, §5, Lemma 5.4, p. 273"]
theorem lemma_5_4 {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosSemidef) (hF' : ¬ F.PosDef) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : Fin n → ℤ, b ≠ 0 ∧ val F (cast b) < ε := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact absurd ((posDef_iff F).2 ⟨Subsingleton.elim _ _, fun x hx =>
      absurd (Subsingleton.elim x 0) hx⟩) hF'
  obtain ⟨hs, hnn⟩ := (posSemidef_iff F).1 hF
  have hx : ∃ x : Fin n → ℝ, x ≠ 0 ∧ val F x = 0 := by
    by_contra hcon
    push_neg at hcon
    exact hF' ((posDef_iff F).2 ⟨hs, fun x hx => lt_of_le_of_ne (hnn x) (Ne.symm (hcon x hx))⟩)
  obtain ⟨x, hx0, hxv⟩ := hx
  have hFx : F *ᵥ x = 0 := by
    have h := sq_bilin_le hF (F *ᵥ x) x
    rw [hxv, mul_zero] at h
    have h2 : ((F *ᵥ x) ⬝ᵥ (F *ᵥ x)) ^ 2 = 0 := le_antisymm h (sq_nonneg _)
    exact dotProduct_self_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h2)
  have hdet : F.det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨x, hx0, hFx⟩
  set g : ℝ → ℝ := fun t => n * (F + t • (1 : Matrix (Fin n) (Fin n) ℝ)).det ^ ((1 : ℝ) / n) with hgdef
  have hdc : Continuous fun t : ℝ => (F + t • (1 : Matrix (Fin n) (Fin n) ℝ)).det :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have hg : Continuous g :=
    continuous_const.mul (hdc.rpow_const (fun _ => Or.inr (by positivity)))
  have hg0 : g 0 = 0 := by
    simp only [hgdef, zero_smul, add_zero, hdet]
    rw [Real.zero_rpow (by positivity)]
    simp
  have hev : ∀ᶠ t in nhds (0 : ℝ), g t < ε :=
    hg.continuousAt.eventually_lt (continuousAt_const (y := ε)) (by simpa [hg0] using hε)
  obtain ⟨t, ht1, ht2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0))).exists
  have ht : 0 < t := ht2
  have hP := posDef_add_smul_one hF ht
  obtain ⟨m, hm0, hm⟩ := exists_val_le_det_rpow hP hn
  refine ⟨m, hm0, ?_⟩
  have e1 : F + t • (1 : Matrix (Fin n) (Fin n) ℝ) = (1 : ℝ) • F + t • 1 := by simp
  have e2 := val_add_mat F 1 1 t (cast m)
  rw [← e1, val_one5] at e2
  have e3 : 0 ≤ ∑ i, (cast m i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have e4 : g t = n * (F + t • (1 : Matrix (Fin n) (Fin n) ℝ)).det ^ ((1 : ℝ) / n) := rfl
  nlinarith

/-- Helper: elements of $W_j$ extend $e_0, \dots, e_{j-1}$. -/
theorem W_extendsBasis {j : Fin n} {e : Fin n → ℤ} (he : e ∈ W j) : ExtendsBasis j e := by
  obtain ⟨T, h1, h2, -⟩ := he
  exact ⟨T, h1, h2⟩

/-- Helper: if $F$ is reduced and $\vec{e}^{\,*}$ extends $e_0, \dots, e_{j-1}$ with $f(\vec{e}^{\,*}) \le f_{jj}$, then
$\vec{e}^{\,*} \in W_j$ (witness: the form $F$ itself). -/
theorem mem_W_of_reduced {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsMinkowskiReduced F) {j : Fin n}
    {e : Fin n → ℤ} (he : ExtendsBasis j e) (hle : val F (cast e) ≤ F j j) : e ∈ W j := by
  obtain ⟨T, h1, h2, hT⟩ := exists_reduced_col hF he hle
  exact ⟨T, h1, h2, F, hF, hT⟩

/-- Helper: the conditions (α) and (β) of Theorem 5.2. -/
def AlphaBeta (F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  0 < F 0 0 ∧ ∀ j : Fin (n + 1), ∀ e ∈ W j, e ≠ Pi.single j 1 → e ≠ -Pi.single j 1 →
    F j j < val F (cast e)

/-- Helper: strictly reduced forms satisfy (α) and (β) (the easy direction of Theorem 5.2). -/
theorem alphaBeta_of_isStrictlyReduced {F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hF : IsStrictlyReduced F) : AlphaBeta F := by
  obtain ⟨hP, h54⟩ := (isStrictlyReduced_iff F).1 hF
  refine ⟨?_, fun j e he h1 h2 => h54 j e (W_extendsBasis he) h1 h2⟩
  have := ((posDef_iff F).1 hP).2 (Pi.single 0 1) (by simp)
  rwa [val_single] at this

/-- Helper: (α) and (β) are preserved by convex combinations. -/
theorem alphaBeta_combo {F G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hF : AlphaBeta F) (hG : AlphaBeta G)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : AlphaBeta (a • F + b • G) := by
  refine ⟨?_, fun j e he h1 h2 => ?_⟩
  · have h1 := hF.1
    have h2 := hG.1
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rcases ha.eq_or_lt with h0 | h0
    · have : b = 1 := by linarith
      subst this; rw [← h0]; linarith
    · nlinarith [mul_pos h0 h1, mul_nonneg hb h2.le]
  · have e1 := hF.2 j e he h1 h2
    have e2 := hG.2 j e he h1 h2
    have hj : (a • F + b • G) j j = a * F j j + b * G j j := by simp
    rw [hj, val_add_mat]
    rcases ha.eq_or_lt with h0 | h0
    · have : b = 1 := by linarith
      subst this; rw [← h0]; linarith
    · nlinarith [mul_pos h0 (sub_pos.2 e1), mul_nonneg hb (sub_pos.2 e2).le]

/-- Helper: combinations of symmetric matrices are symmetric. -/
theorem isSymm_combo {F G : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsSymm) (hG : G.IsSymm) (a b : ℝ) :
    (a • F + b • G).IsSymm := by
  have h1 : Fᵀ = F := hF
  have h2 : Gᵀ = G := hG
  show (a • F + b • G)ᵀ = a • F + b • G
  rw [transpose_add, transpose_smul, transpose_smul, h1, h2]

/-- Helper: the closure of $\mathcal R^\circ$ lies in the set where $f_{jj} \le f(\vec{e}^{\,*})$ for all extending
$\vec{e}^{\,*}$. -/
theorem closure_isStrictlyReduced_le {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : G ∈ closure {F : Matrix (Fin n) (Fin n) ℝ | IsStrictlyReduced F}) {j : Fin n} {e : Fin n → ℤ}
    (he : ExtendsBasis j e) : G j j ≤ val G (cast e) := by
  have hclosed : IsClosed {G : Matrix (Fin n) (Fin n) ℝ | G j j ≤ val G (cast e)} :=
    isClosed_le (by fun_prop) (continuous_val_left _)
  exact closure_minimal (fun F hF => hF.1.2 j e he) hclosed hG

/-- Helper: a form in the closure of $\mathcal R^\circ$ with $f_{00} > 0$ is strictly positive definite (Cassels' use of
Lemma 5.4, p. 273). -/
theorem posDef_of_mem_closure {G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hcl : G ∈ closure {F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ | IsStrictlyReduced F})
    (h0 : 0 < G 0 0) : G.PosDef := by
  have hsd : G.PosSemidef := by
    have hsub : {F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ | IsStrictlyReduced F} ⊆ {F | F.PosDef} :=
      fun F hF => ((isStrictlyReduced_iff F).1 hF).1
    have := closure_mono hsub hcl
    rwa [thm_5_1_closure] at this
  by_contra hnp
  obtain ⟨b, hb0, hb⟩ := lemma_5_4 hsd hnp h0
  obtain ⟨k, hk⟩ : ∃ k, b k ≠ 0 := by
    by_contra hcon; push_neg at hcon; exact hb0 (funext hcon)
  obtain ⟨s, e, t, hs, he, ht0, -, hut⟩ :=
    exists_extendsBasis_decomp (j := (0 : Fin (n + 1))) (u := b) ⟨k, by simp, hk⟩
  have hcast : cast b = (s : ℝ) • cast e := by
    funext i
    have h1 := congrFun hut i
    have h2 : t i = 0 := ht0 i (by simp)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h2, add_zero] at h1
    simp only [cast, Pi.smul_apply, smul_eq_mul, h1]
    push_cast; ring
  have h1 := closure_isStrictlyReduced_le hcl he
  have hs1 : (1 : ℝ) ≤ (s : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ s := hs
    have : (1 : ℝ) ≤ s := by exact_mod_cast this
    nlinarith
  rw [hcast, val_smul] at hb
  nlinarith

/-- Helper: a symmetric form satisfying (α), (β) that lies in the closure of $\mathcal R^\circ$ is strictly reduced
(the heart of Cassels' proof of Theorem 5.2, p. 273). -/
theorem isStrictlyReduced_of_mem_closure {G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (_hs : G.IsSymm)
    (hAB : AlphaBeta G)
    (hcl : G ∈ closure {F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ | IsStrictlyReduced F}) :
    IsStrictlyReduced G := by
  have hP : G.PosDef := posDef_of_mem_closure hcl hAB.1
  have hred : IsMinkowskiReduced G := by
    have : G ∈ {F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ | IsMinkowskiReduced F} := by
      rw [lemma_5_3_closure]; exact ⟨hcl, hP⟩
    exact this
  rw [isStrictlyReduced_iff]
  refine ⟨hP, fun j e he h1 h2 => ?_⟩
  by_contra hlt
  have hle : val G (cast e) ≤ G j j := not_lt.1 hlt
  exact hlt (hAB.2 j e (mem_W_of_reduced hred he hle) h1 h2)

/-- **Theorem 5.2** (Cassels, Ch. 12, §5, p. 272): the set $\mathcal R^\circ$ of strictly reduced forms is defined, among
all real symmetric $F$ (not assumed definite), by the finitely many linear inequalities
(α) $f(e_0) > 0$ and (β) $f(\vec{e}^{\,*}) > f(e_j)$ for $0 \le j < n$ and $\vec{e}^{\,*} \in W_j$, $\vec{e}^{\,*} \ne \pm e_j$.
*Update* (clarification): Cassels' (β) reads "$e^* \in W_j$"; the trivial elements $\pm e_j$ of $W_j$ must be
excluded, as in (5.4).) Stated for $n \ge 1$ variables. -/
@[kb "cassels1978" "Ch. 12, §5, Thm. 5.2, pp. 272–273"]
theorem thm_5_2 {F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hF : F.IsSymm) :
    IsStrictlyReduced F ↔ 0 < F 0 0 ∧ ∀ j : Fin (n + 1), ∀ e ∈ W j, e ≠ Pi.single j 1 → e ≠ -Pi.single j 1 →
      F j j < val F (cast e) := by
  constructor
  · exact alphaBeta_of_isStrictlyReduced
  · intro hAB
    obtain ⟨F₀, hF₀⟩ := exists_isStrictlyReduced (n + 1)
    have hF₀s : F₀.IsSymm := ((posDef_iff F₀).1 (isStrictlyReduced_iff F₀ |>.1 hF₀).1).1
    have hF₀ab := alphaBeta_of_isStrictlyReduced hF₀
    set H : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun x => (1 - x) • F₀ + x • F with hH
    have hHc : Continuous H :=
      ((continuous_const.sub continuous_id).smul continuous_const).add (continuous_id.smul continuous_const)
    have hHs : ∀ x, (H x).IsSymm := fun x => isSymm_combo hF₀s hF _ _
    have hHab : ∀ x ∈ Set.Icc (0 : ℝ) 1, AlphaBeta (H x) := fun x hx =>
      alphaBeta_combo hF₀ab hAB (sub_nonneg.2 hx.2) hx.1 (by ring)
    obtain ⟨U, hUo, hU⟩ := (lemma_5_3_open (n := n + 1))
    set S : Set ℝ := {x | H x ∈ closure {G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ | IsStrictlyReduced G}}
      with hS
    have hsub : Set.Icc (0 : ℝ) 1 ⊆ S := by
      apply IsClosed.Icc_subset_of_forall_mem_nhdsWithin
      · exact (isClosed_closure.preimage hHc).inter isClosed_Icc
      · show H 0 ∈ closure _
        have : H 0 = F₀ := by simp [hH]
        rw [this]; exact subset_closure hF₀
      · rintro x ⟨hxS, hx0, hx1⟩
        have hxR : IsStrictlyReduced (H x) :=
          isStrictlyReduced_of_mem_closure (hHs x) (hHab x ⟨hx0, hx1.le⟩) hxS
        have hxU : H x ∈ U := by
          have : H x ∈ U ∩ {G | G.IsSymm} := by rw [← hU]; exact hxR
          exact this.1
        have hnb : {y | H y ∈ U} ∈ nhds x := (hUo.preimage hHc).mem_nhds hxU
        apply mem_nhdsWithin_of_mem_nhds
        filter_upwards [hnb] with y hy
        have : H y ∈ U ∩ {G | G.IsSymm} := ⟨hy, hHs y⟩
        rw [← hU] at this
        exact subset_closure this
    have h1 : (1 : ℝ) ∈ S := hsub ⟨zero_le_one, le_rfl⟩
    have hH1 : H 1 = F := by simp [hH]
    have : F ∈ closure {G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ | IsStrictlyReduced G} := by
      have := h1; simp only [hS, Set.mem_setOf_eq, hH1] at this; exact this
    exact isStrictlyReduced_of_mem_closure hF hAB this

/-- **Theorem 5.2, Corollary** (Cassels, Ch. 12, p. 273): the set $\mathcal R$ of reduced forms is defined, among all real
symmetric $F$, by (α) $f(e_0) > 0$ and the inequalities (β*) $f(\vec{e}^{\,*}) \ge f(e_j)$ ($\vec{e}^{\,*} \in W_j$). -/
@[kb "cassels1978" "Ch. 12, §5, Thm. 5.2, Corollary, p. 273"]
theorem thm_5_2_cor {F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hF : F.IsSymm) :
    IsMinkowskiReduced F ↔ 0 < F 0 0 ∧ ∀ j : Fin (n + 1), ∀ e ∈ W j, F j j ≤ val F (cast e) := by
  constructor
  · intro hR
    refine ⟨?_, fun j e he => hR.2 j e (W_extendsBasis he)⟩
    have := ((posDef_iff F).1 hR.1).2 (Pi.single 0 1) (by simp)
    rwa [val_single] at this
  · rintro ⟨h0, hβ⟩
    obtain ⟨F₀, hF₀⟩ := exists_isStrictlyReduced (n + 1)
    obtain ⟨hP₀, h₀⟩ := (isStrictlyReduced_iff F₀).1 hF₀
    have hF₀s : F₀.IsSymm := ((posDef_iff F₀).1 hP₀).1
    have hF₀ab := alphaBeta_of_isStrictlyReduced hF₀
    have hcl : F ∈ closure {G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ | IsStrictlyReduced G} := by
      refine mem_closure_of_tendsto (tendsto_path F F₀) ?_
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      apply (thm_5_2 (isSymm_combo hF hF₀s _ _)).2
      refine ⟨?_, fun j e he h1 h2 => ?_⟩
      · have := hF₀ab.1
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        nlinarith [ht.1, ht.2]
      · have e1 := hβ j e he
        have e2 := hF₀ab.2 j e he h1 h2
        have hj : ((1 - t) • F + t • F₀) j j = (1 - t) * F j j + t * F₀ j j := by simp
        rw [hj, val_add_mat]
        nlinarith [mul_nonneg (sub_pos.2 ht.2).le (sub_nonneg.2 e1), mul_pos ht.1 (sub_pos.2 e2)]
    have hP : F.PosDef := posDef_of_mem_closure hcl h0
    have : F ∈ {G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ | IsMinkowskiReduced G} := by
      rw [lemma_5_3_closure]; exact ⟨hcl, hP⟩
    exact this

/-- **Theorem 1.3** (Cassels, Ch. 12, §1, p. 256; proved in §5): there is a finite set $\mathcal C$ of the conditions (1.3),
i.e. of pairs $(j, \vec{b})$ with $\gcd(b_j, \dots, b_{n-1}) = 1$ standing for $f(\vec{b}) \ge f_{jj}$, such that every real
symmetric $F$ (not assumed definite) satisfying the conditions $\mathcal C$ and $f_{00} > 0$ is strictly positive
definite and reduced. (The extra condition is garbled in the machine-read text, p. 257, and reconstructed as
$f_{11} > 0$ in Cassels' 1-based indexing, from (α) of Theorem 5.2.) Geometrically: the reduced forms are a cone in
$\mathbb{R}^{n(n+1)/2}$ bounded by finitely many hyperplanes. Stated for $n \ge 1$ variables. -/
@[kb "cassels1978" "Ch. 12, §1, Thm. 1.3, pp. 256–257; proof in §5, p. 273"]
theorem thm_1_3 (n : ℕ) : ∃ 𝒞 : Finset (Fin (n + 1) × (Fin (n + 1) → ℤ)), (∀ p ∈ 𝒞, tailGcd p.1 p.2 = 1) ∧
    ∀ F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, F.IsSymm → 0 < F 0 0 →
      (∀ p ∈ 𝒞, F p.1 p.1 ≤ val F (cast p.2)) → IsMinkowskiReduced F := by
  have hfin : {p : Fin (n + 1) × (Fin (n + 1) → ℤ) | p.2 ∈ W p.1}.Finite := by
    refine (Set.finite_iUnion fun j : Fin (n + 1) => (W_finite j).image fun e => (j, e)).subset ?_
    rintro ⟨j, e⟩ he
    exact Set.mem_iUnion.2 ⟨j, e, he, rfl⟩
  refine ⟨hfin.toFinset, fun p hp => ?_, fun F hF h0 hC => ?_⟩
  · exact (extendsBasis_iff_gcd _ _).1 (W_extendsBasis (Set.Finite.mem_toFinset hfin |>.1 hp))
  · refine (thm_5_2_cor hF).2 ⟨h0, fun j e he => ?_⟩
    exact hC (j, e) (Set.Finite.mem_toFinset hfin |>.2 he)

end QuadFormsKB.Reduction
