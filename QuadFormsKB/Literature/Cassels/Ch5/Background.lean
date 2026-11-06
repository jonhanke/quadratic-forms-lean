/-
# Cassels, Chapter 5, §§2–3: symmetric sets, lattices and positive definite forms

**Setting.** As in `Ch5/Minkowski.lean`: $\mathbb R^n$ is `Fin n → ℝ` with Lebesgue measure; a lattice with basis
$b_0, \dots, b_{n-1}$ is `span ℤ (Set.range b)` for `b : Basis (Fin n) ℝ (Fin n → ℝ)`, and $B$ = `Matrix.of b` is the
matrix whose $j$-th row is $b_j$, so $d(\Gamma) = \lvert\det B\rvert$ (Cassels' (3.1)). A real quadratic form
$g(\vec u) = \vec u^{\mathsf T} G \vec u$ is given by its symmetric matrix $G$ and $d(g) = \det G$; positive definite
is Mathlib's `Matrix.PosDef`. Indices are $0, \dots, n-1$ (Cassels: $1, \dots, n$).

**Proves** (Cassels, *Rational Quadratic Forms*, Chapter 5)
* the definition of a symmetric set (5.d1, p. 69), compared with Mathlib's pointwise negation: `symmetric_iff_neg_eq`;
* §3, p. 73 (5.r2): a subgroup of finite index of a lattice is a lattice (`isZLattice_of_relIndex_ne_zero`); the form
  $g(\vec u) = \lVert u_0b_0 + \cdots + u_{n-1}b_{n-1}\rVert^2$ of (3.4) is positive definite with
  $d(g) = d(\Gamma)^2$ (3.5) (`gram_posDef`, `gram_eval`, `gram_det`); every positive definite form arises this way
  (`exists_basis_gram`);
* §3, (3.6)–(3.8), p. 73 (5.r3): Minkowski's bound $m \le C_n d(g)^{1/n}$ with $C_n = 4V_n^{-2/n}$ for the minimum $m$
  of a positive definite $g$ at nonzero integral points (`minkowski_minimum_bound`, constant `minkowskiConst`), where
  $V_n$ is the volume of the unit ball (`Siegel.unitBallVol`).
-/
import QuadFormsKB.Literature.Cassels.Ch5.Minkowski
import QuadFormsKB.Siegel.LocalProduct

namespace QuadFormsKB.Cassels.Ch5

open MeasureTheory Module Matrix

variable {n : ℕ}

/-- **Cassels, Ch. 5, §2, p. 69** (definition of a *symmetric* set, 5.d1): *a set $\mathcal Y$ is symmetric (about
$\vec 0$) if $-\vec s \in \mathcal Y$ whenever $\vec s \in \mathcal Y$.* The library spells the condition out as
`∀ x ∈ C, -x ∈ C` (e.g. in `minkowski_convex_body`); this lemma compares it with $-\mathcal Y = \mathcal Y$ for Mathlib's
pointwise negation of sets. Stated in any additive group (Cassels: $\mathbb R^n$). -/
@[kb "cassels1978" "Ch. 5, §2, p. 69 (symmetric set, 5.d1)"]
theorem symmetric_iff_neg_eq {E : Type*} [AddGroup E] (C : Set E) : (∀ x ∈ C, -x ∈ C) ↔ -C = C := by
  constructor
  · intro h
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · have := h _ (Set.mem_neg.1 hx); simpa using this
    · exact Set.mem_neg.2 (h x hx)
  · intro h x hx
    exact Set.mem_neg.1 (by rw [h]; exact hx)

/-- **Cassels, Ch. 5, §3, p. 73** (5.r2, first sentence): *every subgroup $\Lambda$ of finite index in a lattice
$\Gamma$ is itself a lattice.* A lattice is a discrete $\mathbb Z$-submodule of $\mathbb R^n$ spanning $\mathbb R^n$
over $\mathbb R$ (`DiscreteTopology` and `IsZLattice`, as in `minkowski_lattice`); finite index is
`relIndex ≠ 0`. -/
@[kb "cassels1978" "Ch. 5, §3, p. 73 (a subgroup of finite index in a lattice is a lattice)"]
theorem isZLattice_of_relIndex_ne_zero (L L' : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (hle : L' ≤ L) (hidx : L'.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) :
    ∃ _ : DiscreteTopology L', IsZLattice ℝ L' := by
  have hd : DiscreteTopology L' :=
    DiscreteTopology.of_subset (s := (L : Set (Fin n → ℝ))) (t := (L' : Set (Fin n → ℝ))) ‹_› hle
  refine ⟨hd, ⟨?_⟩⟩
  set k := L'.toAddSubgroup.relIndex L.toAddSubgroup
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast hidx
  have hsp : Submodule.span ℝ (L : Set (Fin n → ℝ)) = ⊤ := IsZLattice.span_top
  rw [eq_top_iff, ← hsp]
  refine Submodule.span_le.2 fun x hx => ?_
  have h1 : k • x ∈ L'.toAddSubgroup := AddSubgroup.nsmul_relIndex_mem _ hx
  have h2 : k • x ∈ Submodule.span ℝ (L' : Set (Fin n → ℝ)) := Submodule.subset_span h1
  have h3 := Submodule.smul_mem _ ((k : ℝ)⁻¹) h2
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hk, one_smul] at h3
  exact h3

/-- The matrix of a basis is invertible (its rows are linearly independent). -/
private theorem isUnit_of_basis (b : Basis (Fin n) ℝ (Fin n → ℝ)) : IsUnit (Matrix.of b) := by
  rw [← Matrix.linearIndependent_row_iff_isUnit]
  exact b.linearIndependent

/-- **Cassels, Ch. 5, §3, (3.3)–(3.4), p. 73**: for $\vec x = u_0b_0 + \cdots + u_{n-1}b_{n-1}$,
$x_0^2 + \cdots + x_{n-1}^2 = g(\vec u) = \vec u^{\mathsf T} G \vec u$ with $G = BB^{\mathsf T}$ (the Gram matrix
$G_{ij} = b_i \cdot b_j$). -/
@[kb "cassels1978" "Ch. 5, §3, (3.3)–(3.4), p. 73"]
theorem gram_eval (b : Basis (Fin n) ℝ (Fin n → ℝ)) (u : Fin n → ℝ) :
    ∑ k, (∑ j, u j * b j k) ^ 2 = u ⬝ᵥ (Matrix.of b * (Matrix.of b)ᵀ) *ᵥ u := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  simp only [dotProduct, Matrix.vecMul, sq]
  rfl

/-- **Cassels, Ch. 5, §3, p. 73**: the form $g$ of (3.4), with matrix $G = BB^{\mathsf T}$, is positive definite. -/
@[kb "cassels1978" "Ch. 5, §3, (3.4), p. 73 (g is positive definite)"]
theorem gram_posDef (b : Basis (Fin n) ℝ (Fin n → ℝ)) : (Matrix.of b * (Matrix.of b)ᵀ).PosDef := by
  have h := Matrix.PosDef.mul_conjTranspose_self (Matrix.of b)
    (Matrix.vecMul_injective_iff_isUnit.2 (isUnit_of_basis b))
  simpa using h

/-- **Cassels, Ch. 5, §3, (3.5), p. 73**: $d(g) = d(\Gamma)^2$, where $d(g) = \det G$ and
$d(\Gamma) = \lvert\det(b_0, \dots, b_{n-1})\rvert$. -/
@[kb "cassels1978" "Ch. 5, §3, (3.5), p. 73"]
theorem gram_det (b : Basis (Fin n) ℝ (Fin n → ℝ)) :
    (Matrix.of b * (Matrix.of b)ᵀ).det = |(Matrix.of b).det| ^ 2 := by
  rw [Matrix.det_mul, Matrix.det_transpose, sq_abs, sq]

open scoped MatrixOrder in
/-- **Cassels, Ch. 5, §3, p. 73**: *conversely, every positive definite form $g$ can be obtained in this way*: a
positive definite real symmetric matrix $G$ is $BB^{\mathsf T}$ for the matrix $B$ of some basis $b_0, \dots, b_{n-1}$
of $\mathbb R^n$ (Cassels: "by completing the square successively"; the proof here uses Mathlib's square root of a
positive semidefinite matrix). -/
@[kb "cassels1978" "Ch. 5, §3, p. 73 (every positive definite form is a g of (3.4))"]
theorem exists_basis_gram (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) :
    ∃ b : Basis (Fin n) ℝ (Fin n → ℝ), G = Matrix.of b * (Matrix.of b)ᵀ := by
  classical
  have hP := hG.posSemidef
  set S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt G with hS
  have hSS : S * S = G := CFC.sqrt_mul_sqrt_self G hP.nonneg
  have hSpsd : S.PosSemidef := (CFC.sqrt_nonneg G).posSemidef
  have hSsymm : Sᵀ = S := by
    have := hSpsd.isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hdet : S.det ≠ 0 := by
    have hpos : 0 < G.det := hG.det_pos
    intro h0
    have := congrArg Matrix.det hSS
    rw [Matrix.det_mul, h0] at this
    linarith
  have hli : LinearIndependent ℝ S.row := by
    rw [Matrix.linearIndependent_row_iff_isUnit]
    exact (Matrix.isUnit_iff_isUnit_det S).2 (isUnit_iff_ne_zero.2 hdet)
  let b : Basis (Fin n) ℝ (Fin n → ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank' _ hli (by simp only [Fintype.card_fin, Module.finrank_fin_fun])
  refine ⟨b, ?_⟩
  have : Matrix.of b = S := by
    ext i j; simp only [b, basisOfLinearIndependentOfCardEqFinrank', Basis.coe_mk]; rfl
  rw [this, hSsymm, hSS]

/-- **Minkowski's constant** $C_n = 4V_n^{-2/n}$ of Cassels, Ch. 5, (3.8), p. 73, where $V_n$ is the volume of the unit
ball in $\mathbb R^n$ (`Siegel.unitBallVol`; Cassels: "the volume of the unit sphere"). -/
@[kb "cassels1978" "Ch. 5, §3, (3.8), p. 73"]
noncomputable def minkowskiConst (n : ℕ) : ℝ := 4 * Siegel.unitBallVol n ^ (-(2 / n : ℝ))

/-- **Cassels, Ch. 5, §3, (3.7)–(3.8), p. 73** (Minkowski's bound for the minimum): *let $g$ be a positive definite
form in $n$ variables and $m$ its minimum at integral $\vec u \ne \vec 0$; then $m \le C_n\, d(g)^{1/n}$ with
$C_n = 4V_n^{-2/n}$.* Stated as: some $\vec u \in \mathbb Z^n - \{\vec 0\}$ has
$g(\vec u) = \vec u^{\mathsf T}G\vec u \le C_n (\det G)^{1/n}$ (equivalent, since the minimum is attained). $n \ge 1$
is needed. Proof as Cassels': Minkowski's theorem for the lattice of `exists_basis_gram` and the ball of radius
$\sqrt m$, here in its compact form. -/
@[kb "cassels1978" "Ch. 5, §3, (3.7)–(3.8), p. 73"]
theorem minkowski_minimum_bound (hn : 1 ≤ n) (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) :
    ∃ u : Fin n → ℤ, u ≠ 0 ∧
      (fun i => (u i : ℝ)) ⬝ᵥ G *ᵥ (fun i => (u i : ℝ)) ≤ minkowskiConst n * G.det ^ (1 / n : ℝ) := by
  classical
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨b, hb⟩ := exists_basis_gram G hG
  set d : ℝ := |(Matrix.of b).det| with hd
  have hdet0 : (Matrix.of b).det ≠ 0 := by
    intro h
    have := hG.det_pos
    rw [hb, gram_det, h] at this
    simp at this
  have hdpos : 0 < d := abs_pos.2 hdet0
  set V : ℝ := Siegel.unitBallVol n with hV
  have hball : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) = ENNReal.ofReal V := by
    rw [hV, Siegel.unitBallVol, ENNReal.ofReal_toReal (measure_ball_lt_top).ne]
  have hVpos : 0 < V := by
    rw [hV, Siegel.unitBallVol]
    exact ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  set ρ : ℝ := 2 * (d / V) ^ (1 / n : ℝ) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρn : ρ ^ n * V = 2 ^ n * d := by
    have h2 : ((d / V) ^ (1 / n : ℝ)) ^ n = d / V := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hnr.ne',
        Real.rpow_one]
    rw [hρ, mul_pow, h2]
    field_simp
  -- the body
  set C : Set (Fin n → ℝ) := (fun y : EuclideanSpace ℝ (Fin n) => (WithLp.ofLp y : Fin n → ℝ)) ''
    Metric.closedBall 0 ρ with hC
  have hsymm : ∀ x ∈ C, -x ∈ C := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨-y, by simpa using hy, by simp⟩
  have hconv : Convex ℝ C :=
    (convex_closedBall _ _).linear_image (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap
  have hcpt : IsCompact C := (isCompact_closedBall _ _).image (PiLp.continuous_ofLp 2 _)
  have hCvol : volume C = ENNReal.ofReal (ρ ^ n * V) := by
    have h1 : C = (fun x : Fin n → ℝ => (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))) ⁻¹'
        Metric.closedBall 0 ρ := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨WithLp.toLp 2 x, hx, by simp⟩
    rw [h1, (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
      Metric.isClosed_closedBall.measurableSet.nullMeasurableSet,
      Measure.addHaar_closedBall _ _ hρ0, hball, finrank_euclideanSpace_fin,
      ENNReal.ofReal_mul (by positivity)]
  have hF : volume (ZSpan.fundamentalDomain b) = ENNReal.ofReal d := by
    rw [ZSpan.volume_fundamentalDomain]
  have hvol : volume (ZSpan.fundamentalDomain b) * 2 ^ finrank ℝ (Fin n → ℝ) ≤ volume C := by
    rw [hF, hCvol, hρn, finrank_fin_fun, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by norm_num)]
    simp [mul_comm]
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    (inferInstance : Countable (Submodule.span ℤ (Set.range b)))
  have : DiscreteTopology (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    (inferInstance : DiscreteTopology (Submodule.span ℤ (Set.range b)))
  have fund := ZSpan.isAddFundamentalDomain b volume
  obtain ⟨x, hx0, hxC⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (L := (Submodule.span ℤ (Set.range b)).toAddSubgroup) fund hsymm hconv hcpt hvol
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 x.2
  have hxk : ∀ k, (x : Fin n → ℝ) k = ∑ j, (c j : ℝ) * b j k := by
    intro k
    rw [← hc]
    simp [Finset.sum_apply]
  refine ⟨c, ?_, ?_⟩
  · intro h0
    apply hx0
    apply Subtype.ext
    rw [← hc, h0]
    simp
  · obtain ⟨y, hy, hyx⟩ := hxC
    have hy2 : ∑ k, (y k) ^ 2 ≤ ρ ^ 2 := by
      have := mem_closedBall_zero_iff.1 hy
      rw [EuclideanSpace.norm_eq, Real.sqrt_le_left hρ0] at this
      simpa using this
    have hdot := gram_eval b (fun i => (c i : ℝ))
    rw [← hb] at hdot
    have hsum : ∑ k, (∑ j, (c j : ℝ) * b j k) ^ 2 = ∑ k, (y k) ^ 2 := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hxk k, ← hyx]
    have hdetG : G.det = d ^ 2 := by rw [hb, gram_det]
    have hv : 0 < V ^ (1 / n : ℝ) := Real.rpow_pos_of_pos hVpos _
    have ha : 0 < d ^ (1 / n : ℝ) := Real.rpow_pos_of_pos hdpos _
    have e1 : (d ^ 2) ^ (1 / n : ℝ) = (d ^ (1 / n : ℝ)) ^ 2 := (Real.rpow_pow_comm hdpos.le _ 2).symm
    have e2 : V ^ (-(2 / n : ℝ)) = ((V ^ (1 / n : ℝ)) ^ 2)⁻¹ := by
      rw [Real.rpow_neg hVpos.le, ← Real.rpow_natCast, ← Real.rpow_mul hVpos.le]
      congr 2
      push_cast; ring
    have e3 : ρ ^ 2 = minkowskiConst n * G.det ^ (1 / n : ℝ) := by
      rw [minkowskiConst, hdetG, e1, e2, hρ, Real.div_rpow hdpos.le hVpos.le]
      field_simp
      norm_num
    rw [← hdot, hsum, ← e3]
    exact hy2

end QuadFormsKB.Cassels.Ch5
