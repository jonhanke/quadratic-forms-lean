/-
# Cassels, Chapter 12, §6, Figure 12.1: the vertices of the tessellation

Cassels, *Rational Quadratic Forms* (1978), Ch. 12, §6, caption of Figure 12.1 (p. 274). The caption says, in paraphrase:
each triangle $T\mathcal{F}$ has one vertex on the circumference and two in the interior; there are infinitely many
triangles; they cover the interior of the circle without overlapping and accumulate only towards the circumference; six
triangles meet at every interior vertex; the set of vertices on the circumference is everywhere dense, and each such vertex
belongs to infinitely many triangles.

**Model.** As in `Tessellation.lean`: a binary form is a symmetric $2 \times 2$ real matrix $F$ (a point of the cone of forms);
its point of the disc is $(\xi, \eta) = $ `(binXi F, binEta F)`, which depends only on the ray $\{cF : c > 0\}$; the triangle
$T\mathcal{F}$ is the set `img T` of the forms $T^{\mathsf T}GT$, $G$ Minkowski-reduced (a cone: it is stable under positive
scaling, `mem_img_smul`), without its vertex on the circle. The three vertices of $\mathcal{F}$ are `vertA` ($x_1^2$, on the circle),
`vertB` ($x_0^2 + x_0x_1 + x_1^2$) and `vertC` ($x_0^2 - x_0x_1 + x_1^2$) (both inside the circle); the vertices of $T\mathcal{F}$
are the rays through `act T vertA`, `act T vertB`, `act T vertC`. A point of the disc is "a vertex" if some positive multiple of
a form representing it is one of these.

**Formalized (all unconditional; no hypotheses beyond the stated ones).**
* Six triangles at every interior vertex: `six_triangles_at_interior_vertex`. For an interior vertex $v$ (`IsInteriorVertex`:
  a positive multiple of `act T vertB` or `act T vertC`), the set of distinct triangles (as subsets of the space of forms)
  containing $v$ has exactly $6$ elements (`encard = 6`), and a triangle contains $v$ iff $v$ is one of its two interior
  vertices. The proof reduces, by the substitution $T$ (a linear equivalence permuting the triangles), to the vertex $B = [1,1,1]$;
  the triangles containing $B$ are $X\mathcal{R}$ with $X^{-1}B$ reduced, i.e. $X^{-1}$ has first column a solution of
  $a^2 + ac + c^2 = 1$; with the bound on the second column this gives $24$ matrices (`cases24`), falling into $6$ classes
  modulo the left action of the $4$ sign matrices (which do not change the triangle; $24 / 4 = 6$). Representatives: $X \in \{I, S_1, S_2, \begin{pmatrix}0&1\\1&1\end{pmatrix}, \begin{pmatrix}1&0\\1&1\end{pmatrix},
  \begin{pmatrix}1&1\\1&0\end{pmatrix}\}$ (`triX`); they are pairwise distinct triangles because $T\mathcal{R} = T'\mathcal{R}$ forces
  $T = DT'$ with $D$ a sign matrix (Thm. 7.2), hence equal absolute values of the entries.
* A vertex on the circle lies in infinitely many triangles: `circle_vertex_in_infinitely_many_triangles` (the triangles
  $T_k\mathcal{F}$, $T_k = \begin{pmatrix}1&k\\0&1\end{pmatrix}T$, all have the vertex `act T vertA`; they are pairwise
  distinct), and the vertex lies in the closure of each of them. Consequently there are infinitely many triangles
  (`infinitely_many_triangles`).
* The vertices on the circle are exactly the forms $(px_0 + qx_1)^2$ with $p, q$ coprime integers (`circle_vertex_forms`), and
  their set of disc points is dense in the circle: `circle_vertices_dense` states that the closure of the set
  (`circleVertexPoints`) of the disc points of the vertices `act T vertA` is the whole circle $\xi^2 + \eta^2 = 1$ (so the
  vertices, which lie on the circle by `vertex_on_circle`, are dense in it). Proof: $s \mapsto (2s/(1+s^2), (1-s^2)/(1+s^2))$
  maps $\mathbb{R}$ continuously onto the circle minus $(0,-1)$ and $s = p/q$ rational to the vertex $(px_0 + qx_1)^2$.
* Accumulation only towards the circumference (local finiteness in the disc): `triangles_locally_finite`: a compact subset
  of the open disc contains points of only finitely many triangles (from Thm. 7.6, `thm_7_6`).

**Not repeated here.** "One vertex on the circumference and two in the interior" is `vertex_on_circle`, `vertex_inside`
(`Tessellation.lean`); that the triangles cover the interior of the circle and do not overlap is Theorems 7.1 and 7.4
(`thm_7_1`, `thm_7_4`, `Sec7.lean`, stated for the cone of forms).

**Conventions.** Indices are 0-based. $T$ acts by $(Tf)(\vec{x}) = f(T\vec{x})$, so `act (S * T) = act T ∘ act S` (see
`Tessellation.lean`). "Interior vertex" and "vertex on the circle" are defined as rays (positive multiples), because only the
ray determines the point $(\xi, \eta)$ of the disc.
-/
import QuadFormsKB.Literature.Cassels.Ch12.Sec6
import QuadFormsKB.Literature.Cassels.Ch12.Tessellation

open Matrix

namespace QuadFormsKB.Reduction

namespace Tessellation

namespace Vertices

/-! ### Scaling -/

/-- Helper: the substitution by an integral matrix $U$ commutes with scaling by a real number $c$: $U^{\mathsf T}(cF)U = c\,U^{\mathsf T}FU$. -/
theorem act_smul' (U : Matrix (Fin 2) (Fin 2) ℤ) (c : ℝ) (F : M2) : act U (c • F) = c • act U F := by
  simp [act]

/-- Helper: if $F$ is Minkowski-reduced and $c > 0$ then $cF$ is Minkowski-reduced. -/
theorem red_smul_aux {c : ℝ} (hc : 0 < c) {F : M2} (h : IsMinkowskiReduced F) :
    IsMinkowskiReduced (c • F) := by
  rw [red_iff] at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [Matrix.smul_apply, smul_eq_mul]
  refine ⟨by rw [h1], mul_pos hc h2, mul_le_mul_of_nonneg_left h3 hc.le, ?_⟩
  have : 2 * (c * F 0 1) = c * (2 * F 0 1) := by ring
  rw [this, abs_mul, abs_of_pos hc]
  exact mul_le_mul_of_nonneg_left h4 hc.le

/-- Helper: for $c > 0$, $cF$ is Minkowski-reduced iff $F$ is (the reduced forms form a cone). -/
theorem red_smul {c : ℝ} (hc : 0 < c) (F : M2) :
    IsMinkowskiReduced (c • F) ↔ IsMinkowskiReduced F := by
  constructor
  · intro h
    have := red_smul_aux (inv_pos.2 hc) h
    rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this
  · exact red_smul_aux hc

/-- Helper: the triangle `img T` is stable under positive scaling: $cF \in T\mathcal{R}$ iff $F \in T\mathcal{R}$, for $c > 0$. -/
theorem mem_img_smul {c : ℝ} (hc : 0 < c) (F : M2) (T : GL (Fin 2) ℤ) :
    c • F ∈ img T ↔ F ∈ img T := by
  rw [mem_img_iff_red7, mem_img_iff_red7, act_smul', red_smul hc]

/-! ### Explicit elements of $\mathrm{GL}_2(\mathbb{Z})$ -/

/-- Helper: the element $\begin{pmatrix}a&b\\c&d\end{pmatrix}$ of $\mathrm{GL}_2(\mathbb{Z})$, for integers $a, b, c, d$ with determinant $ad - bc = \pm1$ (hypothesis `h`); its inverse is $(ad - bc)\begin{pmatrix}d&-b\\-c&a\end{pmatrix}$. -/
def glOfEntries (a b c d : ℤ) (h : a * d - b * c = 1 ∨ a * d - b * c = -1) : GL (Fin 2) ℤ :=
  ⟨!![a, b; c, d], !![(a * d - b * c) * d, -((a * d - b * c) * b); -((a * d - b * c) * c), (a * d - b * c) * a], by
    have hE : (a * d - b * c) * (a * d - b * c) = 1 := by rcases h with h | h <;> rw [h] <;> norm_num
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination hE, by
    have hE : (a * d - b * c) * (a * d - b * c) = 1 := by rcases h with h | h <;> rw [h] <;> norm_num
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination hE⟩

/-- Helper: the matrix of `glOfEntries a b c d h` is $\begin{pmatrix}a&b\\c&d\end{pmatrix}$. -/
theorem glOfEntries_val (a b c d : ℤ) (h) : (glOfEntries a b c d h).val = !![a, b; c, d] := rfl

/-- Helper: the matrix of the inverse of `glOfEntries a b c d h`. -/
theorem glOfEntries_inv_val (a b c d : ℤ) (h) : (glOfEntries a b c d h)⁻¹.val =
    !![(a * d - b * c) * d, -((a * d - b * c) * b); -((a * d - b * c) * c), (a * d - b * c) * a] := rfl

/-- Helper: the entries $(X_{00}, X_{01}, X_{10}, X_{11})$ of the six representatives `triX` of the triangles at the vertex $B$:
the matrices $I$, $S_1$, $S_2$, $\begin{pmatrix}0&1\\1&1\end{pmatrix}$, $\begin{pmatrix}1&0\\1&1\end{pmatrix}$,
$\begin{pmatrix}1&1\\1&0\end{pmatrix}$ (all of determinant $\pm1$, `repData_det`). -/
def repData : Fin 6 → ℤ × ℤ × ℤ × ℤ :=
  ![(1, 0, 0, 1), (0, 1, 1, 0), (1, 1, 0, 1), (0, 1, 1, 1), (1, 0, 1, 1), (1, 1, 1, 0)]

/-- Helper: the six matrices of `repData` have determinant $\pm1$. -/
theorem repData_det (i : Fin 6) :
    (repData i).1 * (repData i).2.2.2 - (repData i).2.1 * (repData i).2.2.1 = 1 ∨
    (repData i).1 * (repData i).2.2.2 - (repData i).2.1 * (repData i).2.2.1 = -1 := by
  fin_cases i <;> simp [repData]

/-- Helper: the six elements of $\mathrm{GL}_2(\mathbb{Z})$ whose triangles `img (triX i)` are the six triangles containing the vertex $B$ = `vertB` (`tri_vertB_eq`). -/
def triX (i : Fin 6) : GL (Fin 2) ℤ :=
  glOfEntries (repData i).1 (repData i).2.1 (repData i).2.2.1 (repData i).2.2.2 (repData_det i)

/-- Helper: the matrix of `triX i`. -/
theorem triX_val (i : Fin 6) : (triX i).val =
    !![(repData i).1, (repData i).2.1; (repData i).2.2.1, (repData i).2.2.2] := rfl

/-- Helper: if the rows of $X$ are $\pm$ the rows of $Y$ (signs `s0`, `s1`, each $\pm1$, one per row) then $X\mathcal{R} = Y\mathcal{R}$ (left multiplication by a sign matrix). -/
theorem img_eq_of_rows (X Y : GL (Fin 2) ℤ) (s0 s1 : ℤ) (h0 : s0 = 1 ∨ s0 = -1) (h1 : s1 = 1 ∨ s1 = -1)
    (a0 : X.val 0 0 = s0 * Y.val 0 0) (a1 : X.val 0 1 = s0 * Y.val 0 1)
    (b0 : X.val 1 0 = s1 * Y.val 1 0) (b1 : X.val 1 1 = s1 * Y.val 1 1) : img X = img Y := by
  refine img_eq_of_signDiag7 (S := mkSD s0 s1 h0 h1) (mkSD_signDiag s0 s1 h0 h1) ?_
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mkSD, Matrix.mul_apply, Fin.sum_univ_two, a0, a1, b0, b1]

/-- Helper: if $X\mathcal{R} = Y\mathcal{R}$ then corresponding entries of $X$ and $Y$ have equal absolute values (Thm. 7.2: $XY^{-1}$ is a sign matrix, so $X$ is $Y$ with rows multiplied by $\pm1$). -/
theorem abs_entries_of_img_eq {X Y : GL (Fin 2) ℤ} (h : img X = img Y) (i j : Fin 2) :
    |X.val i j| = |Y.val i j| := by
  have h1 : img (X * Y⁻¹) = {G | IsMinkowskiReduced G} := by
    rw [img_mul, h, ← img_mul, mul_inv_cancel, img_one_eq]
  obtain ⟨d, hd, hD⟩ := thm_7_2 h1
  have hX : X.val = diagonal d * Y.val := by
    have : (X * Y⁻¹).val * Y.val = X.val := by
      rw [Units.val_mul, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    rw [← this, hD]
  rw [hX, Matrix.diagonal_mul]
  rcases hd i with hi | hi <;> simp [hi]

/-- Helper: the six triangles `img (triX i)` are pairwise distinct (their representatives have pairwise different matrices of absolute values of entries). -/
theorem img_triX_injective : Function.Injective fun i : Fin 6 => img (triX i) := by
  intro i j h
  have h' : img (triX i) = img (triX j) := h
  have h00 := abs_entries_of_img_eq h' 0 0
  have h01 := abs_entries_of_img_eq h' 0 1
  have h10 := abs_entries_of_img_eq h' 1 0
  have h11 := abs_entries_of_img_eq h' 1 1
  simp only [triX_val] at h00 h01 h10 h11
  fin_cases i <;> fin_cases j <;> simp [repData] at h00 h01 h10 h11 ⊢

/-- Helper: the vertex form $x_0^2 + x_0x_1 + x_1^2$ is Minkowski-reduced. -/
theorem vertB_red : IsMinkowskiReduced vertB := by
  rw [red_iff]; simp [vertB]

/-- Helper: the vertex form $x_0^2 - x_0x_1 + x_1^2$ is Minkowski-reduced. -/
theorem vertC_red : IsMinkowskiReduced vertC := by
  rw [red_iff]; simp [vertC]; norm_num [abs_div]

/-- Helper: the vertex $B$ = `vertB` lies in each of the six triangles `img (triX i)`. -/
theorem vertB_mem_triX (i : Fin 6) : vertB ∈ img (triX i) := by
  rw [mem_img_iff_red7]
  unfold triX
  rw [glOfEntries_inv_val, red_iff]
  fin_cases i <;> simp [repData, act, vertB, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply] <;> norm_num

/-- Helper: the entries of the inverse of $W \in \mathrm{GL}_2(\mathbb{Z})$: $W^{-1} = (\det W)\begin{pmatrix}w_{11}&-w_{01}\\-w_{10}&w_{00}\end{pmatrix}$ with $\det W = \pm1$. -/
theorem inv_entries (W : GL (Fin 2) ℤ) :
    W⁻¹.val 0 0 = (W.val 0 0 * W.val 1 1 - W.val 0 1 * W.val 1 0) * W.val 1 1 ∧
    W⁻¹.val 0 1 = -((W.val 0 0 * W.val 1 1 - W.val 0 1 * W.val 1 0) * W.val 0 1) ∧
    W⁻¹.val 1 0 = -((W.val 0 0 * W.val 1 1 - W.val 0 1 * W.val 1 0) * W.val 1 0) ∧
    W⁻¹.val 1 1 = (W.val 0 0 * W.val 1 1 - W.val 0 1 * W.val 1 0) * W.val 0 0 := by
  have hWX : W.val * W⁻¹.val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  generalize W⁻¹.val = X at hWX ⊢
  have E00 := congrFun (congrFun hWX 0) 0
  have E01 := congrFun (congrFun hWX 0) 1
  have E10 := congrFun (congrFun hWX 1) 0
  have E11 := congrFun (congrFun hWX 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at E00 E01 E10 E11
  have he2 : (W.val 0 0 * W.val 1 1 - W.val 0 1 * W.val 1 0) * (W.val 0 0 * W.val 1 1 - W.val 0 1 * W.val 1 0) = 1 := by
    rcases det_pm W with h | h <;> rw [h] <;> norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-(X 0 0)) * he2 + (W.val 0 0 * W.val 1 1 - W.val 0 1 * W.val 1 0) *
      (W.val 1 1 * E00 - W.val 0 1 * E10)
  · linear_combination (-(X 0 1)) * he2 + (W.val 0 0 * W.val 1 1 - W.val 0 1 * W.val 1 0) *
      (W.val 1 1 * E01 - W.val 0 1 * E11)
  · linear_combination (-(X 1 0)) * he2 + (W.val 0 0 * W.val 1 1 - W.val 0 1 * W.val 1 0) *
      (W.val 0 0 * E10 - W.val 1 0 * E00)
  · linear_combination (-(X 1 1)) * he2 + (W.val 0 0 * W.val 1 1 - W.val 0 1 * W.val 1 0) *
      (W.val 0 0 * E11 - W.val 1 0 * E01)

/-- Helper (the $24$ solutions): integers $a, b, c, d$ with $a^2 + ac + c^2 = 1$, $|2ab + ad + bc + 2cd| \le 1$ and $ad - bc = \pm1$ (the conditions for $W = \begin{pmatrix}a&b\\c&d\end{pmatrix}$ to carry $x_0^2 + x_0x_1 + x_1^2$ to a reduced form) are, up to a sign for each row of the adjugate $\begin{pmatrix}d&-b\\-c&a\end{pmatrix}$, one of the six matrices `repData`. -/
theorem cases24 (a b c d : ℤ) (h1 : a ^ 2 + a * c + c ^ 2 = 1)
    (h2 : |2 * a * b + a * d + b * c + 2 * c * d| ≤ 1) (h3 : a * d - b * c = 1 ∨ a * d - b * c = -1) :
    ∃ i : Fin 6, ∃ s0 ∈ ({1, -1} : Finset ℤ), ∃ s1 ∈ ({1, -1} : Finset ℤ),
      d = s0 * (repData i).1 ∧ -b = s0 * (repData i).2.1 ∧ -c = s1 * (repData i).2.2.1 ∧
        a = s1 * (repData i).2.2.2 := by
  rw [abs_le] at h2
  have ha : -1 ≤ a ∧ a ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (a + 2 * c), sq_nonneg (2 * a + c), sq_nonneg c, sq_nonneg a]
  have hc : -1 ≤ c ∧ c ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (a + 2 * c), sq_nonneg (2 * a + c), sq_nonneg c, sq_nonneg a]
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hc1, hc2⟩ := hc
  interval_cases a <;> interval_cases c <;> (try norm_num at h1) <;>
  · have hb : -1 ≤ b ∧ b ≤ 1 := by omega
    have hd : -1 ≤ d ∧ d ≤ 1 := by omega
    obtain ⟨hb1, hb2⟩ := hb
    obtain ⟨hd1, hd2⟩ := hd
    interval_cases b <;> interval_cases d <;> first | (exfalso; omega) | decide

/-- Helper: the entries of $W^{\mathsf T}BW$ for $B$ = `vertB` ($= x_0^2 + x_0x_1 + x_1^2$) and $W \in \mathrm{GL}_2(\mathbb{Z})$: the $(0,0)$, $(0,1)$, $(1,0)$ and $(1,1)$ entries. -/
theorem act_vertB_entries (W : GL (Fin 2) ℤ) :
    act W.val vertB 0 0 = (W.val 0 0 : ℝ) ^ 2 + W.val 0 0 * W.val 1 0 + (W.val 1 0 : ℝ) ^ 2 ∧
    act W.val vertB 0 1 = (W.val 0 0 : ℝ) * W.val 0 1 + ((W.val 0 0 : ℝ) * W.val 1 1 + W.val 0 1 * W.val 1 0) / 2 +
      W.val 1 0 * W.val 1 1 ∧
    act W.val vertB 1 0 = (W.val 0 0 : ℝ) * W.val 0 1 + ((W.val 0 0 : ℝ) * W.val 1 1 + W.val 0 1 * W.val 1 0) / 2 +
      W.val 1 0 * W.val 1 1 ∧
    act W.val vertB 1 1 = (W.val 0 1 : ℝ) ^ 2 + W.val 0 1 * W.val 1 1 + (W.val 1 1 : ℝ) ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp [act, vertB, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
    ring

/-- Helper: a reduced form equivalent to $B = x_0^2 + x_0x_1 + x_1^2$ is $B$ or $C = x_0^2 - x_0x_1 + x_1^2$ (first coefficient $1$ by `key_eq`; determinant $3/4$ and reducedness force the other coefficients). -/
theorem eq_vertB_or_vertC (W : GL (Fin 2) ℤ) (hG : IsMinkowskiReduced (act W.val vertB)) :
    act W.val vertB = vertB ∨ act W.val vertB = vertC := by
  have k0 := key_eq vertB_red W hG
  obtain ⟨e00, e01, e10, e11⟩ := act_vertB_entries W
  obtain ⟨hs, -, h1, h2⟩ := (red_iff _).1 hG
  have hk : act W.val vertB 0 0 = 1 := by rw [k0]; simp [vertB]
  have hdet : ((W.val 0 0 : ℝ) * W.val 1 1 - W.val 0 1 * W.val 1 0) ^ 2 = 1 := by
    rcases det_pm W with h | h
    · have : ((W.val 0 0 : ℝ) * W.val 1 1 - W.val 0 1 * W.val 1 0) = 1 := by exact_mod_cast h
      rw [this]; norm_num
    · have : ((W.val 0 0 : ℝ) * W.val 1 1 - W.val 0 1 * W.val 1 0) = -1 := by exact_mod_cast h
      rw [this]; norm_num
  have key : act W.val vertB 0 0 * act W.val vertB 1 1 - act W.val vertB 0 1 ^ 2 = 3 / 4 := by
    rw [e00, e01, e11]
    nlinarith [hdet]
  rw [hk] at key h1 h2
  rw [abs_le] at h2
  have hsq : act W.val vertB 0 1 ^ 2 = 1 / 4 := by nlinarith
  have h11 : act W.val vertB 1 1 = 1 := by nlinarith
  have hfac : (2 * act W.val vertB 0 1 - 1) * (2 * act W.val vertB 0 1 + 1) = 0 := by nlinarith
  have hfin : ∀ G : M2, G 1 0 = G 0 1 → G 0 0 = 1 → G 1 1 = 1 →
      (2 * G 0 1 - 1 = 0 ∨ 2 * G 0 1 + 1 = 0) → G = vertB ∨ G = vertC := by
    intro G hs hk h11 h
    rcases h with h | h
    · left
      ext i j
      fin_cases i <;> fin_cases j <;> simp [vertB] <;> linarith
    · right
      ext i j
      fin_cases i <;> fin_cases j <;> simp [vertC] <;> linarith
  exact hfin _ hs hk h11 (mul_eq_zero.1 hfac)

/-- Helper: a product of two numbers each equal to $\pm1$ is $\pm1$. -/
theorem sign_mul {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) : a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

/-- Helper: **the triangles containing the vertex $B = x_0^2 + x_0x_1 + x_1^2$ are exactly the six triangles `img (triX i)`**, $i \in \{0, \dots, 5\}$. (Inclusion $\subseteq$: if $B \in X\mathcal{R}$ then $W = X^{-1}$ carries $B$ to a reduced form, whose first coefficient is $1$ (`key_eq`), whence $a^2 + ac + c^2 = 1$ and $|2ab + ad + bc + 2cd| \le 1$ for the entries of $W$; `cases24` and `inv_entries` express the rows of $X$ as $\pm$ the rows of a `triX i`.) -/
theorem tri_vertB_eq : {S : Set M2 | ∃ X : GL (Fin 2) ℤ, S = img X ∧ vertB ∈ S} =
    Set.range (fun i : Fin 6 => img (triX i)) := by
  ext S
  constructor
  · rintro ⟨X, rfl, hX⟩
    have hG : IsMinkowskiReduced (act X⁻¹.val vertB) := (mem_img_iff_red7 X vertB).1 hX
    have k0 := key_eq vertB_red X⁻¹ hG
    obtain ⟨e00, e01, -, -⟩ := act_vertB_entries X⁻¹
    obtain ⟨-, -, -, hab⟩ := (red_iff _).1 hG
    have hk : act X⁻¹.val vertB 0 0 = 1 := by rw [k0]; simp [vertB]
    have h1 : (X⁻¹.val 0 0) ^ 2 + X⁻¹.val 0 0 * X⁻¹.val 1 0 + (X⁻¹.val 1 0) ^ 2 = 1 := by
      have : ((X⁻¹.val 0 0 : ℤ) : ℝ) ^ 2 + ((X⁻¹.val 0 0 : ℤ) : ℝ) * ((X⁻¹.val 1 0 : ℤ) : ℝ) +
          ((X⁻¹.val 1 0 : ℤ) : ℝ) ^ 2 = 1 := by rw [← e00]; exact hk
      exact_mod_cast this
    have h2 : |2 * X⁻¹.val 0 0 * X⁻¹.val 0 1 + X⁻¹.val 0 0 * X⁻¹.val 1 1 + X⁻¹.val 0 1 * X⁻¹.val 1 0 +
        2 * X⁻¹.val 1 0 * X⁻¹.val 1 1| ≤ 1 := by
      rw [e01, hk] at hab
      have : |((2 * X⁻¹.val 0 0 * X⁻¹.val 0 1 + X⁻¹.val 0 0 * X⁻¹.val 1 1 + X⁻¹.val 0 1 * X⁻¹.val 1 0 +
          2 * X⁻¹.val 1 0 * X⁻¹.val 1 1 : ℤ) : ℝ)| ≤ 1 := by
        refine le_trans (le_of_eq ?_) hab
        congr 1
        push_cast
        ring
      exact_mod_cast this
    obtain ⟨i, s0, hs0, s1, hs1, E1, E2, E3, E4⟩ := cases24 _ _ _ _ h1 h2 (det_pm X⁻¹)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs0 hs1
    refine ⟨i, ?_⟩
    obtain ⟨i00, i01, i10, i11⟩ := inv_entries X⁻¹
    rw [inv_inv] at i00 i01 i10 i11
    have he := det_pm X⁻¹
    have t00 : (triX i).val 0 0 = (repData i).1 := rfl
    have t01 : (triX i).val 0 1 = (repData i).2.1 := rfl
    have t10 : (triX i).val 1 0 = (repData i).2.2.1 := rfl
    have t11 : (triX i).val 1 1 = (repData i).2.2.2 := rfl
    refine (img_eq_of_rows X (triX i)
      ((X⁻¹.val 0 0 * X⁻¹.val 1 1 - X⁻¹.val 0 1 * X⁻¹.val 1 0) * s0)
      ((X⁻¹.val 0 0 * X⁻¹.val 1 1 - X⁻¹.val 0 1 * X⁻¹.val 1 0) * s1)
      (sign_mul he hs0) (sign_mul he hs1) ?_ ?_ ?_ ?_).symm
    · rw [t00]; linear_combination i00 + (X⁻¹.val 0 0 * X⁻¹.val 1 1 - X⁻¹.val 0 1 * X⁻¹.val 1 0) * E1
    · rw [t01]; linear_combination i01 + (X⁻¹.val 0 0 * X⁻¹.val 1 1 - X⁻¹.val 0 1 * X⁻¹.val 1 0) * E2
    · rw [t10]; linear_combination i10 + (X⁻¹.val 0 0 * X⁻¹.val 1 1 - X⁻¹.val 0 1 * X⁻¹.val 1 0) * E3
    · rw [t11]; linear_combination i11 + (X⁻¹.val 0 0 * X⁻¹.val 1 1 - X⁻¹.val 0 1 * X⁻¹.val 1 0) * E4
  · rintro ⟨i, rfl⟩
    exact ⟨triX i, rfl, vertB_mem_triX i⟩

/-! ### Six triangles at every interior vertex -/

/-- **The set of triangles containing a form** $v$: the sets $K = T\mathcal{R}$ (`img T`, $T \in \mathrm{GL}_2(\mathbb{Z})$) with $v \in K$. Distinct matrices $T$ with the same set `img T` give one element. -/
def trianglesAt (v : M2) : Set (Set M2) := {K | ∃ T : GL (Fin 2) ℤ, K = img T ∧ v ∈ K}

/-- Helper: $cT^{\mathsf T}BT \in T'\mathcal{R}$ iff $B \in (T'T^{-1})\mathcal{R}$, for $c > 0$ and $B$ = `vertB`. -/
theorem mem_img_vertB_smul {c : ℝ} (hc : 0 < c) (T T' : GL (Fin 2) ℤ) :
    c • act T.val vertB ∈ img T' ↔ vertB ∈ img (T' * T⁻¹) := by
  rw [mem_img_smul hc, mem_img_iff_red7, mem_img_iff_red7, show (T' * T⁻¹)⁻¹ = T * T'⁻¹ by simp,
    Units.val_mul, act_mul]

/-- Helper: the triangles containing $c\,T^{\mathsf T}BT$ are the images under the substitution $T$ of the triangles containing $B$. -/
theorem trianglesAt_smul {c : ℝ} (hc : 0 < c) (T : GL (Fin 2) ℤ) :
    trianglesAt (c • act T.val vertB) =
      (fun S : Set M2 => actL7 T.val '' S) '' {S : Set M2 | ∃ X : GL (Fin 2) ℤ, S = img X ∧ vertB ∈ S} := by
  ext K
  constructor
  · rintro ⟨T', rfl, hv⟩
    refine ⟨img (T' * T⁻¹), ⟨T' * T⁻¹, rfl, (mem_img_vertB_smul hc T T').1 hv⟩, ?_⟩
    show actL7 T.val '' img (T' * T⁻¹) = img T'
    rw [← img_mul]; simp
  · rintro ⟨_, ⟨X, rfl, hX⟩, rfl⟩
    have hK : (fun S : Set M2 => actL7 T.val '' S) (img X) = img (X * T) := (img_mul X T).symm
    refine ⟨X * T, hK, ?_⟩
    rw [hK]
    refine (mem_img_vertB_smul hc T (X * T)).2 ?_
    simpa using hX

/-- Helper: exactly six distinct triangles contain $c\,T^{\mathsf T}BT$ ($c > 0$, $T \in \mathrm{GL}_2(\mathbb{Z})$, $B$ = `vertB`). -/
theorem trianglesAt_encard {c : ℝ} (hc : 0 < c) (T : GL (Fin 2) ℤ) :
    (trianglesAt (c • act T.val vertB)).encard = 6 := by
  rw [trianglesAt_smul hc T]
  have hinj : Function.Injective fun S : Set M2 => actL7 T.val '' S :=
    Function.Injective.image_injective (actEquiv T).injective
  rw [hinj.encard_image, tri_vertB_eq, img_triX_injective.encard_range]
  simp

/-- Helper: the substitution `binD` ($x_1 \mapsto -x_1$) carries $B = x_0^2 + x_0x_1 + x_1^2$ to $C = x_0^2 - x_0x_1 + x_1^2$. -/
theorem act_binD_vertB : act binD.val vertB = vertC := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [act, binD, vertB, vertC, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;> norm_num

/-- Helper: if a positive multiple $v = c\,T^{\mathsf T}BT$ lies in $T'\mathcal{R}$, then $v$ is a positive multiple of $T'^{\mathsf T}BT'$ or of $T'^{\mathsf T}CT'$ (the two inside vertices of $T'\mathcal{F}$). -/
theorem vertex_of_mem {c : ℝ} (hc : 0 < c) (T T' : GL (Fin 2) ℤ) (hv : c • act T.val vertB ∈ img T') :
    ∃ c' : ℝ, 0 < c' ∧ (c • act T.val vertB = c' • act T'.val vertB ∨
      c • act T.val vertB = c' • act T'.val vertC) := by
  have hB := (mem_img_vertB_smul hc T T').1 hv
  have hG := (mem_img_iff_red7 _ _).1 hB
  have e : vertB = act (T' * T⁻¹).val (act (T' * T⁻¹)⁻¹.val vertB) := (act_act_inv7 _ _).symm
  have e2 : act T.val vertB = act T'.val (act (T' * T⁻¹)⁻¹.val vertB) := by
    conv_lhs => rw [e]
    rw [← act_mul, ← Units.val_mul]
    simp
  refine ⟨c, hc, ?_⟩
  rcases eq_vertB_or_vertC _ hG with h | h
  · left; rw [e2, h]
  · right; rw [e2, h]

/-- Helper: a positive multiple of an inside vertex of $T'\mathcal{F}$ lies in $T'\mathcal{R}$. -/
theorem mem_of_vertex {c : ℝ} (hc : 0 < c) (T' : GL (Fin 2) ℤ) (v : M2)
    (hv : v = c • act T'.val vertB ∨ v = c • act T'.val vertC) : v ∈ img T' := by
  rw [mem_img_iff_red7]
  rcases hv with rfl | rfl
  · rw [act_smul', act_inv_act7, red_smul hc]; exact vertB_red
  · rw [act_smul', act_inv_act7, red_smul hc]; exact vertC_red

/-- **Interior vertex of the tessellation** (Cassels, Ch. 12, §6, Figure 12.1, p. 274): a form $v$ that is a positive multiple of
$T^{\mathsf T}BT$ or of $T^{\mathsf T}CT$ for some $T \in \mathrm{GL}_2(\mathbb{Z})$, where $B = x_0^2 + x_0x_1 + x_1^2$ (`vertB`)
and $C = x_0^2 - x_0x_1 + x_1^2$ (`vertC`) are the two vertices of $\mathcal{F}$ inside the circle (`vertex_inside`). Its point
in the disc is a vertex of a triangle $T\mathcal{F}$ lying in the interior of the circle. -/
def IsInteriorVertex (v : M2) : Prop :=
  ∃ (T : GL (Fin 2) ℤ) (c : ℝ), 0 < c ∧ (v = c • act T.val vertB ∨ v = c • act T.val vertC)

/-- Helper: every interior vertex is a positive multiple of $T^{\mathsf T}BT$ for some $T$ ($C = \mathrm{diag}(1,-1)^{\mathsf T}B\,\mathrm{diag}(1,-1)$). -/
theorem isInteriorVertex_iff (v : M2) :
    IsInteriorVertex v ↔ ∃ (T : GL (Fin 2) ℤ) (c : ℝ), 0 < c ∧ v = c • act T.val vertB := by
  constructor
  · rintro ⟨T, c, hc, h | h⟩
    · exact ⟨T, c, hc, h⟩
    · refine ⟨binD * T, c, hc, ?_⟩
      rw [h, Units.val_mul, act_mul, act_binD_vertB]
  · rintro ⟨T, c, hc, h⟩
    exact ⟨T, c, hc, Or.inl h⟩

/-- **Six triangles meet at every interior vertex** (Cassels, Ch. 12, §6, Figure 12.1 caption, p. 274). For an interior vertex $v$
(`IsInteriorVertex`; $v$ is a form, the point $(\xi, \eta)$ of the disc is that of the ray through $v$):
the set `trianglesAt v` of distinct triangles $T\mathcal{R}$ (as subsets of the space of forms; `img T`, $T \in
\mathrm{GL}_2(\mathbb{Z})$) containing $v$ has exactly $6$ elements (extended cardinality `encard`), and a triangle `img T'` contains $v$ iff
$v$ is a positive multiple of $T'^{\mathsf T}BT'$ or of $T'^{\mathsf T}CT'$, i.e. iff $v$ is one of the two inside vertices of $T'\mathcal{F}$
(so the six triangles are exactly those having $v$ as a vertex; no triangle has $v$ on a side or inside). Unconditional. -/
@[kb "cassels1978" "Ch. 12, §6, Fig. 12.1 caption, p. 274 (six triangles T𝓕 meet at every interior vertex)"]
theorem six_triangles_at_interior_vertex {v : M2} (hv : IsInteriorVertex v) :
    (trianglesAt v).encard = 6 ∧
      ∀ T' : GL (Fin 2) ℤ, v ∈ img T' ↔
        ∃ c : ℝ, 0 < c ∧ (v = c • act T'.val vertB ∨ v = c • act T'.val vertC) := by
  obtain ⟨T, c, hc, rfl⟩ := (isInteriorVertex_iff v).1 hv
  refine ⟨trianglesAt_encard hc T, fun T' => ⟨fun h => vertex_of_mem hc T T' h, ?_⟩⟩
  rintro ⟨c', hc', h⟩
  exact mem_of_vertex hc' T' _ h

/-! ### Vertices on the circle -/

/-- Helper: the form $T^{\mathsf T}x_1^2T$ is the square of the linear form given by the second row of $T$: its $(i,j)$ entry is $T_{1i}T_{1j}$. -/
theorem act_vertA_apply (T : GL (Fin 2) ℤ) (i j : Fin 2) :
    act T.val vertA i j = (T.val 1 i : ℝ) * T.val 1 j := by
  fin_cases i <;> fin_cases j <;> simp [act, vertA, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply]

/-- Helper: the shear $\begin{pmatrix}1&k\\0&1\end{pmatrix} \in \mathrm{GL}_2(\mathbb{Z})$, $k \in \mathbb{Z}$ ($x_0 \mapsto x_0 + kx_1$); it fixes the vertex $x_1^2$ and moves $\mathcal{F}$ to infinitely many different triangles. -/
def shearK (k : ℤ) : GL (Fin 2) ℤ := glOfEntries 1 k 0 1 (Or.inl (by ring))

/-- Helper: the shear fixes the vertex form $x_1^2$. -/
theorem act_shearK_vertA (k : ℤ) : act (shearK k).val vertA = vertA := by
  ext i j
  rw [act_vertA_apply]
  fin_cases i <;> fin_cases j <;> simp [shearK, glOfEntries_val, vertA]

/-- **Vertex on the circle of the tessellation** (Cassels, Ch. 12, §6, Figure 12.1, p. 274): a form $v$ that is a positive multiple
of $T^{\mathsf T}x_1^2T$, i.e. of $(T_{10}x_0 + T_{11}x_1)^2$, for some $T \in \mathrm{GL}_2(\mathbb{Z})$ (`act_vertA_apply`); its point of the
disc lies on the circle (`vertex_on_circle`). -/
def IsCircleVertex (v : M2) : Prop :=
  ∃ (T : GL (Fin 2) ℤ) (c : ℝ), 0 < c ∧ v = c • act T.val vertA

/-- Helper: $\begin{pmatrix}1&k\\0&1\end{pmatrix}\begin{pmatrix}1&j\\0&1\end{pmatrix}^{-1} = \begin{pmatrix}1&k-j\\0&1\end{pmatrix}$. -/
theorem shearK_mul_inv (k j : ℤ) : (shearK k * (shearK j)⁻¹).val = !![1, k - j; 0, 1] := by
  rw [Units.val_mul]
  show (glOfEntries 1 k 0 1 _).val * (glOfEntries 1 j 0 1 _)⁻¹.val = _
  rw [glOfEntries_val, glOfEntries_inv_val]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg, add_comm]

/-- Helper: the triangles $S_k\mathcal{R}$, $S_k$ the shear by $k$, are pairwise distinct (the form $\mathrm{diag}(1,2)$ shears into $S_k\mathcal{R}$ but not into $S_j\mathcal{R}$, $j \ne k$, since $\begin{pmatrix}1&m\\m&m^2+2\end{pmatrix}$ is reduced only for $m = 0$). -/
theorem img_shearK_injective : Function.Injective fun k : ℤ => img (shearK k) := by
  intro k j h
  have h' : img (shearK k) = img (shearK j) := h
  set G0 : M2 := !![1, 0; 0, 2] with hG0
  have hG0r : IsMinkowskiReduced G0 := by
    rw [red_iff]; simp [hG0]
  have hmem : act (shearK k).val G0 ∈ img (shearK k) := ⟨G0, hG0r, rfl⟩
  rw [h', mem_img_iff_red7, red_iff] at hmem
  obtain ⟨-, -, -, h4⟩ := hmem
  have e : act (shearK j)⁻¹.val (act (shearK k).val G0) =
      !![1, ((k - j : ℤ) : ℝ); ((k - j : ℤ) : ℝ), ((k - j : ℤ) : ℝ) ^ 2 + 2] := by
    rw [← act_mul, ← Units.val_mul, shearK_mul_inv]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [act, hG0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, sq]
  rw [e] at h4
  simp at h4
  have h4' : |((k - j : ℤ) : ℝ)| ≤ 1 / 2 := by push_cast; linarith
  rw [abs_le] at h4'
  have h5 : k - j < 1 := by
    have : ((k - j : ℤ) : ℝ) < 1 := by linarith [h4'.2]
    exact_mod_cast this
  have h6 : -1 < k - j := by
    have : (-1 : ℝ) < ((k - j : ℤ) : ℝ) := by linarith [h4'.1]
    exact_mod_cast this
  omega

/-- Helper: the path $\varepsilon \mapsto \mathrm{diag}(\varepsilon, c)$ of matrices is continuous. -/
theorem continuous_diag_path (c : ℝ) : Continuous fun ε : ℝ => (!![ε, 0; 0, c] : M2) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/-- Helper: the vertex on the circle belongs to the closure of its triangle: $c\,T^{\mathsf T}x_1^2T \in \overline{T\mathcal{R}}$ for $c > 0$ (it is the limit of $T^{\mathsf T}\mathrm{diag}(\varepsilon, c)T$ as $\varepsilon \to 0^+$, $0 < \varepsilon \le c$). -/
theorem vertex_mem_closure {c : ℝ} (hc : 0 < c) (T : GL (Fin 2) ℤ) :
    c • act T.val vertA ∈ closure (img T) := by
  have h0 : (!![0, 0; 0, c] : M2) ∈ closure {G : M2 | IsMinkowskiReduced G} := by
    have hI : (0 : ℝ) ∈ closure (Set.Ioc (0 : ℝ) c) := by
      rw [closure_Ioc hc.ne]; exact ⟨le_rfl, hc.le⟩
    have := map_mem_closure (continuous_diag_path c) hI (t := {G : M2 | IsMinkowskiReduced G}) (by
      intro ε hε
      rw [Set.mem_ofPred_eq, red_iff]
      simp
      exact ⟨hε.1, hε.2, hε.1.le⟩ )
    simpa using this
  have := map_mem_closure (continuous_act7 T.val) h0 (t := img T) (fun G hG => ⟨G, hG, rfl⟩)
  convert this using 1
  rw [← act_smul']
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vertA]

/-- **A vertex on the circumference belongs to infinitely many triangles** (Cassels, Ch. 12, §6, Figure 12.1 caption, p. 274). For a
vertex $v$ on the circle (`IsCircleVertex`): (i) the set of distinct triangles `img T'` having $v$ as their vertex on the circle (that is,
$v = c\,T'^{\mathsf T}x_1^2T'$ with $c > 0$) is infinite; (ii) $v$ belongs to the closure of each triangle `img T'` of which it is
such a vertex (the triangles `img T'` themselves do not contain their vertex on the circle: the form $x_1^2$ is not reduced). Unconditional. -/
@[kb "cassels1978" "Ch. 12, §6, Fig. 12.1 caption, p. 274 (a vertex on the circumference belongs to infinitely many T𝓕)"]
theorem circle_vertex_in_infinitely_many_triangles {v : M2} (hv : IsCircleVertex v) :
    {K : Set M2 | ∃ T' : GL (Fin 2) ℤ, K = img T' ∧ ∃ c : ℝ, 0 < c ∧ v = c • act T'.val vertA}.Infinite ∧
      ∀ (T' : GL (Fin 2) ℤ) (c : ℝ), 0 < c → v = c • act T'.val vertA → v ∈ closure (img T') := by
  refine ⟨?_, fun T' c hc h => h ▸ vertex_mem_closure hc T'⟩
  obtain ⟨T, c, hc, rfl⟩ := hv
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℤ => img (shearK k * T)) ?_ ?_
  · intro k j h
    exact img_shearK_injective ((img_mul_inj T).1 h)
  · intro k
    refine ⟨shearK k * T, rfl, c, hc, ?_⟩
    rw [Units.val_mul, act_mul, act_shearK_vertA]

/-- **There are infinitely many triangles $T\mathcal{F}$** (Cassels, Ch. 12, §6, Figure 12.1 caption, p. 274): the set of distinct sets `img T`, $T \in \mathrm{GL}_2(\mathbb{Z})$, is infinite. -/
@[kb "cassels1978" "Ch. 12, §6, Fig. 12.1 caption, p. 274 (infinitely many triangles T𝓕)"]
theorem infinitely_many_triangles : (Set.range fun T : GL (Fin 2) ℤ => img T).Infinite :=
  (Set.infinite_range_of_injective img_shearK_injective).mono (by rintro _ ⟨k, rfl⟩; exact ⟨shearK k, rfl⟩)

/-- Helper: a pair of coprime integers $(p, q)$ is the second row of some $T \in \mathrm{GL}_2(\mathbb{Z})$ (Bézout). -/
theorem exists_T_of_coprime {p q : ℤ} (h : IsCoprime p q) :
    ∃ T : GL (Fin 2) ℤ, T.val 1 0 = p ∧ T.val 1 1 = q := by
  obtain ⟨u, v, huv⟩ := h
  exact ⟨glOfEntries v (-u) p q (Or.inl (by linear_combination huv)), rfl, rfl⟩

/-- Helper: the second row of an element of $\mathrm{GL}_2(\mathbb{Z})$ consists of coprime integers (the determinant is $\pm1$). -/
theorem isCoprime_row (T : GL (Fin 2) ℤ) : IsCoprime (T.val 1 0) (T.val 1 1) := by
  rcases det_pm T with h | h
  · exact ⟨-T.val 0 1, T.val 0 0, by linear_combination h⟩
  · exact ⟨T.val 0 1, -T.val 0 0, by linear_combination -h⟩

/-- **The vertices on the circumference are the squares of primitive linear forms** (Cassels, Ch. 12, §6, Figure 12.1, p. 274): the forms
$T^{\mathsf T}x_1^2T$ for $T \in \mathrm{GL}_2(\mathbb{Z})$ are exactly the forms $(px_0 + qx_1)^2$, with matrix $\begin{pmatrix}p^2&pq\\pq&q^2\end{pmatrix}$,
for coprime integers $p, q$. -/
@[kb "cassels1978" "Ch. 12, §6, Fig. 12.1, p. 274 (the vertices on the circumference are the forms (p x₀ + q x₁)²)"]
theorem circle_vertex_forms :
    {F : M2 | ∃ T : GL (Fin 2) ℤ, F = act T.val vertA} =
      {F : M2 | ∃ p q : ℤ, IsCoprime p q ∧ F = !![(p : ℝ) ^ 2, (p : ℝ) * q; (p : ℝ) * q, (q : ℝ) ^ 2]} := by
  ext F
  constructor
  · rintro ⟨T, rfl⟩
    refine ⟨T.val 1 0, T.val 1 1, isCoprime_row T, ?_⟩
    ext i j
    rw [act_vertA_apply]
    fin_cases i <;> fin_cases j <;> simp [sq, mul_comm]
  · rintro ⟨p, q, hpq, rfl⟩
    obtain ⟨T, h0, h1⟩ := exists_T_of_coprime hpq
    refine ⟨T, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sq, act_vertA_apply, h0, h1, mul_comm]

/-- Helper: the rational parametrisation of the circle, $s \mapsto \bigl(\tfrac{2s}{1+s^2}, \tfrac{1-s^2}{1+s^2}\bigr)$ (the point $(\xi, \eta)$ of the form $(sx_0 + x_1)^2$). -/
noncomputable def circleParam (s : ℝ) : ℝ × ℝ := (2 * s / (1 + s ^ 2), (1 - s ^ 2) / (1 + s ^ 2))

/-- Helper: `circleParam` is continuous. -/
theorem continuous_circleParam : Continuous circleParam := by
  refine Continuous.prodMk ?_ ?_
  · refine Continuous.div (by fun_prop) (by fun_prop) fun s => by positivity
  · refine Continuous.div (by fun_prop) (by fun_prop) fun s => by positivity

/-- Helper: for rational $s = p/q$ in lowest terms, the point `circleParam s` is the point $(\xi, \eta)$ of the vertex $(px_0 + qx_1)^2 = T^{\mathsf T}x_1^2T$ of some triangle. -/
theorem circleParam_rat (s : ℚ) : ∃ T : GL (Fin 2) ℤ,
    (binXi (act T.val vertA), binEta (act T.val vertA)) = circleParam (s : ℝ) := by
  obtain ⟨T, h0, h1⟩ := exists_T_of_coprime (Rat.isCoprime_num_den s)
  refine ⟨T, ?_⟩
  have hden : (0 : ℝ) < (s.den : ℝ) := by exact_mod_cast s.den_pos
  have hs : (s : ℝ) = (s.num : ℝ) / (s.den : ℝ) := by rw [Rat.cast_def]
  unfold binXi binEta circleParam
  simp only [act_vertA_apply, h0, h1, hs]
  push_cast
  have hq : (s.den : ℝ) ≠ 0 := hden.ne'
  refine Prod.ext ?_ ?_
  · simp only
    have : (s.num : ℝ) ^ 2 + (s.den : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  · simp only
    have : (s.num : ℝ) ^ 2 + (s.den : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp
    ring

/-- **The points of the disc that are vertices on the circumference**: the points $(\xi, \eta)$ = `(binXi F, binEta F)` of the forms $F = T^{\mathsf T}x_1^2T$, $T \in \mathrm{GL}_2(\mathbb{Z})$ (`vertA` is the form $x_1^2$), as a subset of $\mathbb{R} \times \mathbb{R}$. -/
def circleVertexPoints : Set (ℝ × ℝ) :=
  Set.range fun T : GL (Fin 2) ℤ => (binXi (act T.val vertA), binEta (act T.val vertA))

/-- Helper: `circleParam` inverts the stereographic coordinate $s = \xi/(1 + \eta)$ on the circle minus $(0, -1)$. -/
theorem circleParam_eq {z : ℝ × ℝ} (hz : z.1 ^ 2 + z.2 ^ 2 = 1) (hne : z.2 ≠ -1) :
    circleParam (z.1 / (1 + z.2)) = z := by
  have h1 : 1 + z.2 ≠ 0 := fun h => hne (by linarith)
  have h2 : (1 + z.2) ^ 2 + z.1 ^ 2 = 2 * (1 + z.2) := by nlinarith
  have h3 : 1 + (z.1 / (1 + z.2)) ^ 2 = 2 / (1 + z.2) := by
    field_simp
    linear_combination h2
  unfold circleParam
  refine Prod.ext ?_ ?_
  · simp only
    rw [h3]
    field_simp
  · simp only
    rw [h3]
    field_simp
    nlinarith

/-- **The vertices on the circumference are everywhere dense** (Cassels, Ch. 12, §6, Figure 12.1 caption, p. 274): the closure in
$\mathbb{R} \times \mathbb{R}$ of the set `circleVertexPoints` of points $(\xi, \eta)$ of the vertices $T^{\mathsf T}x_1^2T$ is the whole circle
$\{(\xi, \eta) : \xi^2 + \eta^2 = 1\}$. (The inclusion $\subseteq$ is `vertex_on_circle`; $\supseteq$ is the density.) Unconditional. -/
@[kb "cassels1978" "Ch. 12, §6, Fig. 12.1 caption, p. 274 (the vertices on the circumference are everywhere dense)"]
theorem circle_vertices_dense :
    closure circleVertexPoints = {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 = 1} := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rintro _ ⟨T, rfl⟩
      exact (vertex_on_circle T).2
    · exact isClosed_eq (by fun_prop) continuous_const
  · intro z hz
    have hz' : z.1 ^ 2 + z.2 ^ 2 = 1 := hz
    by_cases hz2 : z.2 = -1
    · have hz1 : z.1 = 0 := by
        rw [hz2] at hz'
        nlinarith [sq_nonneg z.1]
      apply subset_closure
      obtain ⟨T, h0, h1⟩ := exists_T_of_coprime (isCoprime_one_left : IsCoprime (1 : ℤ) 0)
      refine ⟨T, Prod.ext ?_ ?_⟩
      · simp [binXi, act_vertA_apply, h0, h1, hz1]
      · simp [binEta, act_vertA_apply, h0, h1, hz2]
    · have hcl : circleParam (z.1 / (1 + z.2)) ∈ closure (circleParam '' Set.range ((↑) : ℚ → ℝ)) :=
        image_closure_subset_closure_image continuous_circleParam
          ⟨z.1 / (1 + z.2), by rw [Rat.denseRange_cast.closure_range]; trivial, rfl⟩
      rw [circleParam_eq hz' hz2] at hcl
      refine closure_mono ?_ hcl
      rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
      obtain ⟨T, hT⟩ := circleParam_rat q
      exact ⟨T, hT⟩

/-! ### Accumulation only towards the circumference -/

/-- **The point of the disc of a form** $F$: $(\xi, \eta)$ = `(binXi F, binEta F)` (`Sec6.lean`). -/
noncomputable def discPoint (F : M2) : ℝ × ℝ := (binXi F, binEta F)

/-- Helper: the form of trace $1$ with disc point $z = (\xi, \eta)$: the matrix $\begin{pmatrix}(1-\eta)/2 & \xi/2\\ \xi/2 & (1+\eta)/2\end{pmatrix}$. -/
noncomputable def discToForm (z : ℝ × ℝ) : M2 := !![(1 - z.2) / 2, z.1 / 2; z.1 / 2, (1 + z.2) / 2]

/-- Helper: `discToForm` is continuous. -/
theorem continuous_discToForm : Continuous discToForm := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [discToForm] <;> fun_prop

/-- Helper: `discToForm z` has trace $1$. -/
theorem discToForm_trace (z : ℝ × ℝ) : discToForm z 0 0 + discToForm z 1 1 = 1 := by
  simp [discToForm]; ring

/-- Helper: the disc point of `discToForm z` is $z$. -/
theorem discToForm_disc (z : ℝ × ℝ) : discPoint (discToForm z) = z := by
  have := discToForm_trace z
  unfold discPoint binXi binEta
  rw [this]
  ext <;> simp [discToForm] <;> ring

/-- Helper: the form `discToForm z` is positive definite for $z$ in the open disc. -/
theorem discToForm_posDef {z : ℝ × ℝ} (hz : z.1 ^ 2 + z.2 ^ 2 < 1) : (discToForm z).PosDef := by
  have hs : (discToForm z).IsSymm := (isSymm_iff10 _).2 (by simp [discToForm])
  rw [((binary_posDef_iff hs).2)]
  refine ⟨by rw [discToForm_trace]; norm_num, ?_⟩
  have := discToForm_disc z
  unfold discPoint at this
  rw [Prod.ext_iff] at this
  simp only at this
  rw [this.1, this.2]; exact hz

/-- Helper: a symmetric form $F$ with $f_{00} + f_{11} > 0$ is $(f_{00} + f_{11})$ times the trace-one form of its disc point. -/
theorem discToForm_eq_smul {F : M2} (hs : F.IsSymm) (ht : 0 < F 0 0 + F 1 1) :
    discToForm (discPoint F) = (F 0 0 + F 1 1)⁻¹ • F := by
  have h10 := (isSymm_iff10 F).1 hs
  ext i j
  fin_cases i <;> fin_cases j <;> simp [discToForm, discPoint, binXi, binEta, h10] <;> field_simp <;> ring

/-- **The triangles accumulate only towards the circumference** (Cassels, Ch. 12, §6, Figure 12.1 caption, p. 274; local finiteness in
the open disc): a compact set `C` of points $(\xi, \eta)$ of the open disc $\xi^2 + \eta^2 < 1$ contains the disc point
`discPoint F` of a form $F$ of only finitely many distinct triangles `img T` ($F \in$ `img T`). From Cassels' Theorem 7.6 (`thm_7_6`) applied
to the trace-one forms over `C`. Unconditional. -/
@[kb "cassels1978" "Ch. 12, §6, Fig. 12.1 caption, p. 274 (the triangles accumulate only towards the circumference)"]
theorem triangles_locally_finite {C : Set (ℝ × ℝ)} (hC : IsCompact C)
    (hCd : ∀ z ∈ C, z.1 ^ 2 + z.2 ^ 2 < 1) :
    {K : Set M2 | ∃ T : GL (Fin 2) ℤ, K = img T ∧ ∃ F ∈ K, discPoint F ∈ C}.Finite := by
  have hK0 : IsCompact (discToForm '' C) := hC.image continuous_discToForm
  have hfin := thm_7_6 hK0 (by rintro _ ⟨z, hz, rfl⟩; exact discToForm_posDef (hCd z hz))
  refine (hfin.image img).subset ?_
  rintro _ ⟨T, rfl, F, hF, hFC⟩
  refine ⟨T, ?_, rfl⟩
  refine ⟨discToForm (discPoint F), ?_, ⟨discPoint F, hFC, rfl⟩⟩
  obtain ⟨G, hG, rfl⟩ := hF
  have hPD : (act T.val G).PosDef := PosDef.act hG.1 T
  have hs : (act T.val G).IsSymm := hPD.1
  have ht : 0 < (act T.val G) 0 0 + (act T.val G) 1 1 := (((binary_posDef_iff hs).2).1 hPD).1
  rw [discToForm_eq_smul hs ht, mem_img_smul (inv_pos.2 ht)]
  exact ⟨G, hG, rfl⟩

end Vertices

end Tessellation
end QuadFormsKB.Reduction
