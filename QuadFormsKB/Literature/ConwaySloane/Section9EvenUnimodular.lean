/-
# Conway–Sloane, Ch. 15, §9.5–9.6: spinor norms of even unimodular lattices over $\mathbb Z_2$

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5–9.6, pp. 391–393
(`conwaysloane1999`).

**Layer.** $F_\mathfrak p$ = `v.adicCompletion ℚ` with valuation ring $\mathfrak o$ = `v.adicCompletionIntegers ℚ`;
$A$ an integer symmetric Gram matrix (Conway–Sloane's $f(x) = xAx^{\mathsf T}$), $A_{F_\mathfrak p}$ its image over
$F_\mathfrak p$. Wall frames and Wall's formula: `Section9Wall.lean`.

**Proves**
* `exists_sq_valued_wallDet` (the **core lemma**): if $A$ is *even unimodular at $\mathfrak p$*
  ($\lvert\det A\rvert_\mathfrak p = 1$ and every diagonal entry $A_{ii}$ even) and $S$ is an integral matrix with
  $S^{\mathsf T} A S = A$, then for every Wall frame $(P, R)$ of $S$ the valuation of
  $\det(P^{\mathsf T} A R)$ is a square in $\mathbb Z^{\mathrm m 0}$.

*Proof.* Take the Smith normal form of $(1 - S)\mathfrak o^N$ inside $\mathfrak o^N$: a basis $b$ of $\mathfrak o^N$
and $a_j \ne 0$ with $(1 - S)\mathfrak o^N = \bigoplus_j a_j\mathfrak o\, b_{f(j)}$. Then $P_j = b_{f(j)}$ and
$R_j = z_j/a_j$ ($(1 - S)z_j = a_jb_{f(j)}$) is a Wall frame, and its Gram matrix is $C = U\,\mathrm{diag}(a)^{-1}$ with
$U_{kj} = P_k^{\mathsf T}Az_j$ integral. Since $A$ is unimodular and the $P_k$ are part of a basis, $U$ has an
integral right inverse (the Wall form pairs $\mathfrak o^N \cap V_\sigma$ perfectly with $(1 - S)\mathfrak o^N$), so
$\lvert\det U\rvert = 1$. The symmetric part of $C$ is $\tfrac12 P^{\mathsf T}AP$ (`wall_symm_id`), integral off the
diagonal and, as $A$ is even, on the diagonal. The level lemma (`Levels.exists_sq_prod_valued`) makes
$\prod_j\lvert a_j\rvert$ a square, hence $\lvert\det C\rvert = \prod_j\lvert a_j\rvert^{-1}$ is one. Other frames
change the determinant by a square (`Wall.wallDet_eq_mat`).
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Wall
import QuadFormsKB.Literature.ConwaySloane.Section9Levels

open Matrix IsDedekindDomain NumberField WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane.EvenUnimodular

open Wall Levels

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

theorem valued_intCast_le_one (z : ℤ) : Valued.v ((z : ℤ) : Fv) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (K := ℚ) (v := v)).1 (intCast_mem (v.adicCompletionIntegers ℚ) z)

theorem valued_coe_le_one (x : 𝔬) : Valued.v (x : Fv) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (K := ℚ) (v := v)).1 x.2

theorem valued_sum_le_one {ι : Type*} (s : Finset ι) (f : ι → Fv) (h : ∀ i ∈ s, Valued.v (f i) ≤ 1) :
    Valued.v (∑ i ∈ s, f i) ≤ 1 :=
  Valuation.map_sum_le _ h

theorem valued_mul_le_one {x y : Fv} (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ 1) : Valued.v (x * y) ≤ 1 := by
  rw [map_mul]; exact mul_le_one' hx hy

/-- Clearing denominators of a vector over $F_\mathfrak p$. -/
theorem exists_clear {N : ℕ} (z : Fin N → Fv) : ∃ d : 𝔬, d ≠ 0 ∧ ∀ i, Valued.v ((d : Fv) * z i) ≤ 1 := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors 𝔬) (Finset.univ : Finset (Fin N)) z
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, fun i => ?_⟩
  obtain ⟨y, hy⟩ := hb i (Finset.mem_univ i)
  have : ((b : 𝔬) : Fv) * z i = (y : Fv) := by
    have h := hy.symm
    rw [Algebra.smul_def] at h
    exact h
  rw [this]
  exact valued_coe_le_one y

/-- For an integral vector $x$ and a symmetric integer matrix $A$ with even diagonal, $\tfrac12 x^{\mathsf T}Ax$ is
integral. -/
theorem valued_half_quad_le_one {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ) (hA : Aᵀ = A)
    (heven : ∀ i, Even (A i i)) (x : Fin N → Fv) (hx : ∀ i, Valued.v (x i) ≤ 1) :
    Valued.v ((x ⬝ᵥ (A.map (Int.cast : ℤ → Fv) *ᵥ x)) / 2) ≤ 1 := by
  classical
  set Af := A.map (Int.cast : ℤ → Fv)
  choose t ht using heven
  set L : Matrix (Fin N) (Fin N) Fv :=
    Matrix.of fun i j => if j < i then Af i j else if i = j then (t i : Fv) else 0
  have hsymA : ∀ i j, A j i = A i j := fun i j => congrFun (congrFun hA i) j
  have hdec : Af = L + Lᵀ := by
    ext i j
    simp only [L, Matrix.add_apply, transpose_apply, of_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · simp only [not_lt_of_gt h, ne_of_lt h, h, ite_false, ite_true, zero_add, Af, map_apply, hsymA]
    · simp only [lt_irrefl, ite_false, ite_true, Af, map_apply, ht i]
      push_cast; ring
    · simp only [not_lt_of_gt h, ne_of_gt h, ne_of_lt h, h, ite_false, ite_true, add_zero, Af, map_apply]
  have hLt : x ⬝ᵥ (Lᵀ *ᵥ x) = x ⬝ᵥ (L *ᵥ x) := by
    rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]
  have e : (x ⬝ᵥ (Af *ᵥ x)) / 2 = x ⬝ᵥ (L *ᵥ x) := by
    rw [hdec, add_mulVec, dotProduct_add, hLt]
    ring
  rw [e]
  refine valued_sum_le_one _ _ fun i _ => valued_mul_le_one (hx i) ?_
  refine valued_sum_le_one _ _ fun j _ => valued_mul_le_one ?_ (hx j)
  simp only [L, of_apply]
  split_ifs
  · exact valued_intCast_le_one _
  · exact valued_intCast_le_one _
  · simp

/-! ### Integral vectors -/

/-- The vector of $F_\mathfrak p^N$ of an integral vector. -/
def ιv {N : ℕ} (x : Fin N → 𝔬) : Fin N → Fv := fun i => (x i : Fv)

theorem ιv_injective {N : ℕ} : Function.Injective (ιv (v := v) (N := N)) :=
  fun _ _ h => funext fun i => Subtype.ext (congrFun h i)

theorem ιv_add {N : ℕ} (x y : Fin N → 𝔬) : ιv (x + y) = ιv x + ιv y := by
  ext i; simp [ιv]

theorem ιv_sub {N : ℕ} (x y : Fin N → 𝔬) : ιv (x - y) = ιv x - ιv y := by
  ext i; simp [ιv]

theorem ιv_smul {N : ℕ} (c : 𝔬) (x : Fin N → 𝔬) : ιv (c • x) = (c : Fv) • ιv x := by
  ext i; simp [ιv]

theorem ιv_zero {N : ℕ} : ιv (0 : Fin N → 𝔬) = 0 := by
  ext i; simp [ιv]

theorem ιv_sum {N k : ℕ} (x : Fin k → Fin N → 𝔬) : ιv (∑ j, x j) = ∑ j, ιv (x j) := by
  ext i
  simp only [ιv, Finset.sum_apply]
  push_cast
  rfl

theorem ιv_mulVec {N : ℕ} (M : Matrix (Fin N) (Fin N) Fv) (hM : ∀ i j, Valued.v (M i j) ≤ 1)
    (x : Fin N → 𝔬) : ιv (toO M hM *ᵥ x) = M *ᵥ ιv x := by
  ext i
  simp only [ιv, mulVec, dotProduct]
  push_cast
  rfl

theorem valued_ιv_le_one {N : ℕ} (x : Fin N → 𝔬) (i : Fin N) : Valued.v (ιv x i) ≤ 1 := valued_coe_le_one _

/-- An element of $\mathfrak o$ from an element of valuation at most $1$. -/
def toOel (x : Fv) (hx : Valued.v x ≤ 1) : 𝔬 :=
  ⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers (K := ℚ) (v := v)).2 hx⟩

/-! ### The Smith normal form frame -/

/-- **The Smith normal form frame** of an integral $S$: a Wall frame $(P, Z\,\mathrm{diag}(a)^{-1})$ with $P$ part of a
basis $W$ of $\mathfrak o^N$ ($P_{ij} = W_{i f(j)}$), $Z$ integral, $a_j \ne 0$ integral, and every
$(1 - S)y$ ($y$ integral) an integral combination of the $(1 - S)Z_j$. -/
theorem exists_snf_frame {N : ℕ} (S : Matrix (Fin N) (Fin N) Fv) (hS : ∀ i j, Valued.v (S i j) ≤ 1) :
    ∃ (m : ℕ) (W W' : Matrix (Fin N) (Fin N) Fv) (f : Fin m ↪ Fin N) (Z : Matrix (Fin N) (Fin m) Fv)
      (a : Fin m → Fv),
      (∀ i j, Valued.v (W i j) ≤ 1) ∧ (∀ i j, Valued.v (W' i j) ≤ 1) ∧ W * W' = 1 ∧ W' * W = 1 ∧
      (∀ i j, Valued.v (Z i j) ≤ 1) ∧ (∀ j, a j ≠ 0 ∧ Valued.v (a j) ≤ 1) ∧
      IsWallFrame Fv S (Matrix.of fun i j => W i (f j)) (Z * Matrix.diagonal fun j => (a j)⁻¹) ∧
      ∀ y : Fin N → Fv, (∀ i, Valued.v (y i) ≤ 1) →
        ∃ r : Fin m → Fv, (∀ j, Valued.v (r j) ≤ 1) ∧ (1 - S) *ᵥ y = (1 - S) *ᵥ (Z *ᵥ r) := by
  classical
  set T := 1 - S
  have hT : ∀ i j, Valued.v (T i j) ≤ 1 := by
    intro i j
    simp only [T, Matrix.sub_apply, Matrix.one_apply]
    refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ (hS i j))
    split_ifs <;> simp
  set T𝔬 := toO T hT
  set Nsub := LinearMap.range (Matrix.toLin' T𝔬)
  obtain ⟨m, snf⟩ := Submodule.smithNormalForm (Pi.basisFun 𝔬 (Fin N)) Nsub
  set b := snf.bM
  have hz : ∀ j, ∃ z : Fin N → 𝔬, T𝔬 *ᵥ z = (snf.bN j : Fin N → 𝔬) := fun j => by
    obtain ⟨z, hz⟩ := (snf.bN j).2
    exact ⟨z, by rw [← Matrix.toLin'_apply]; exact hz⟩
  choose z hz using hz
  have ha0 : ∀ j, (snf.a j : Fv) ≠ 0 := by
    intro j h0
    apply snf.bN.ne_zero j
    have h1 : snf.a j = 0 := Subtype.ext h0
    apply Subtype.ext
    rw [snf.snf j, h1, zero_smul]
    rfl
  set W𝔬 := (Pi.basisFun 𝔬 (Fin N)).toMatrix b
  set W'𝔬 := b.toMatrix (Pi.basisFun 𝔬 (Fin N))
  have hW𝔬 : ∀ i k, W𝔬 i k = b k i := fun i k => by
    simp [W𝔬, Module.Basis.toMatrix_apply]
  set W : Matrix (Fin N) (Fin N) Fv := W𝔬.map (𝔬).subtype
  set W' : Matrix (Fin N) (Fin N) Fv := W'𝔬.map (𝔬).subtype
  have hWW' : W * W' = 1 := by
    have e : W * W' = (𝔬).subtype.mapMatrix (W𝔬 * W'𝔬) := by rw [map_mul]; rfl
    rw [e, Module.Basis.toMatrix_mul_toMatrix_flip, map_one]
  have hW'W : W' * W = 1 := by
    have e : W' * W = (𝔬).subtype.mapMatrix (W'𝔬 * W𝔬) := by rw [map_mul]; rfl
    rw [e, Module.Basis.toMatrix_mul_toMatrix_flip, map_one]
  set Z : Matrix (Fin N) (Fin m) Fv := Matrix.of fun i j => (z j i : Fv)
  set a : Fin m → Fv := fun j => (snf.a j : Fv)
  set P : Matrix (Fin N) (Fin m) Fv := Matrix.of fun i j => W i (snf.f j)
  have hPcol : ∀ j, (fun i => P i j) = ιv (b (snf.f j)) := fun j => by
    ext i; simp [P, W, hW𝔬, ιv]
  have hTz : ∀ j, T *ᵥ ιv (z j) = a j • ιv (b (snf.f j)) := by
    intro j
    rw [← ιv_mulVec T hT, hz j, snf.snf j, ιv_smul]
  refine ⟨m, W, W', snf.f, Z, a, fun i j => valued_coe_le_one _, fun i j => valued_coe_le_one _, hWW', hW'W,
    fun i j => valued_coe_le_one _, fun j => ⟨ha0 j, valued_coe_le_one _⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · ext i j
    rw [mul_apply_col]
    have hcol : (fun k => (Z * Matrix.diagonal fun j => (a j)⁻¹) k j) = (a j)⁻¹ • ιv (z j) := by
      ext k; simp [Z, mul_diagonal, ιv, mul_comm]
    rw [hcol, mulVec_smul, hTz, smul_smul, inv_mul_cancel₀ (ha0 j), one_smul, ← hPcol j]
  · intro c hc
    obtain ⟨d, hd0, hdc⟩ := exists_clear c
    set c' : Fin m → 𝔬 := fun j => toOel ((d : Fv) * c j) (hdc j)
    have hsum : ∑ j, c' j • b (snf.f j) = 0 := by
      apply ιv_injective
      rw [ιv_sum, ιv_zero]
      simp only [ιv_smul, c', toOel]
      have : P *ᵥ c = ∑ j, c j • ιv (b (snf.f j)) := by
        rw [mulVec_eq_sum_cols]; simp only [hPcol]
      have h2 : (d : Fv) • (P *ᵥ c) = 0 := by rw [hc, smul_zero]
      rw [this, Finset.smul_sum] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul]
    have hli := b.linearIndependent.comp snf.f snf.f.injective
    have h0 := Fintype.linearIndependent_iff.mp hli c' hsum
    funext j
    have h1 : (d : Fv) * c j = 0 := congrArg Subtype.val (h0 j)
    have hd : (d : Fv) ≠ 0 := fun h => hd0 (Subtype.ext h)
    exact (mul_eq_zero.mp h1).resolve_left hd
  · intro z0
    obtain ⟨d, hd0, hdz⟩ := exists_clear z0
    have hd : (d : Fv) ≠ 0 := fun h => hd0 (Subtype.ext h)
    set y : Fin N → 𝔬 := fun i => toOel ((d : Fv) * z0 i) (hdz i)
    have hy : T𝔬 *ᵥ y ∈ Nsub := ⟨y, Matrix.toLin'_apply _ _⟩
    set r := snf.bN.repr ⟨_, hy⟩
    have hrep : T𝔬 *ᵥ y = ∑ j, r j • (snf.bN j : Fin N → 𝔬) := by
      have h2 := congrArg Subtype.val (snf.bN.sum_repr ⟨_, hy⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
      exact h2.symm
    refine ⟨fun j => (r j : Fv) * a j / (d : Fv), ?_⟩
    have h1 : (d : Fv) • (T *ᵥ z0) = ∑ j, ((r j : Fv) * a j) • (fun i => P i j) := by
      have e : (d : Fv) • z0 = ιv y := by ext i; simp [y, ιv, toOel]
      rw [← mulVec_smul, e, ← ιv_mulVec T hT, hrep, ιv_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ιv_smul, snf.snf j, ιv_smul, smul_smul, hPcol]
    calc T *ᵥ z0 = (d : Fv)⁻¹ • ((d : Fv) • (T *ᵥ z0)) := by
          rw [smul_smul, inv_mul_cancel₀ hd, one_smul]
      _ = _ := by
          rw [h1, mulVec_eq_sum_cols, Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [smul_smul]
          congr 1
          field_simp
  · intro y hy
    set y𝔬 : Fin N → 𝔬 := fun i => toOel (y i) (hy i)
    have hy𝔬 : ιv y𝔬 = y := rfl
    have hmem : T𝔬 *ᵥ y𝔬 ∈ Nsub := ⟨y𝔬, Matrix.toLin'_apply _ _⟩
    set r := snf.bN.repr ⟨_, hmem⟩
    have hrep : T𝔬 *ᵥ y𝔬 = ∑ j, r j • (snf.bN j : Fin N → 𝔬) := by
      have h2 := congrArg Subtype.val (snf.bN.sum_repr ⟨_, hmem⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
      exact h2.symm
    refine ⟨fun j => (r j : Fv), fun j => valued_coe_le_one _, ?_⟩
    have hZ : Z *ᵥ (fun j => (r j : Fv)) = ιv (∑ j, r j • z j) := by
      rw [mulVec_eq_sum_cols, ιv_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ιv_smul]
      rfl
    rw [hZ, ← hy𝔬, ← ιv_mulVec T hT, ← ιv_mulVec T hT, hrep, mulVec_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mulVec_smul, hz j]

/-! ### The core lemma -/

theorem gram_apply' {N m m' : ℕ} (P : Matrix (Fin N) (Fin m) Fv) (G : Matrix (Fin N) (Fin N) Fv)
    (R : Matrix (Fin N) (Fin m') Fv) (i : Fin m) (j : Fin m') :
    (Pᵀ * G * R) i j = (fun k => P k i) ⬝ᵥ (G *ᵥ fun k => R k j) := by
  simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem mul_integral {p q r : ℕ} (M : Matrix (Fin p) (Fin q) Fv) (M' : Matrix (Fin q) (Fin r) Fv)
    (hM : ∀ i j, Valued.v (M i j) ≤ 1) (hM' : ∀ i j, Valued.v (M' i j) ≤ 1) :
    ∀ i j, Valued.v ((M * M') i j) ≤ 1 := fun i j =>
  valued_sum_le_one _ _ fun k _ => valued_mul_le_one (hM i k) (hM' k j)

theorem valued_det_le_one {m : ℕ} (M : Matrix (Fin m) (Fin m) Fv) (hM : ∀ i j, Valued.v (M i j) ≤ 1) :
    Valued.v M.det ≤ 1 := by
  rw [← det_toO M hM]; exact valued_coe_le_one _

theorem mulVec_integral {p q : ℕ} (M : Matrix (Fin p) (Fin q) Fv) (x : Fin q → Fv)
    (hM : ∀ i j, Valued.v (M i j) ≤ 1) (hx : ∀ i, Valued.v (x i) ≤ 1) : ∀ i, Valued.v ((M *ᵥ x) i) ≤ 1 :=
  fun i => valued_sum_le_one _ _ fun k _ => valued_mul_le_one (hM i k) (hx k)

/-- **The core lemma**: for $A$ even unimodular at $\mathfrak p$ and an integral $S$ with $S^{\mathsf T}AS = A$, the
determinant of the Wall Gram matrix $P^{\mathsf T}AR$ of every Wall frame of $S$ has square valuation. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (2-adically automorphous numbers of an even unimodular form)"]
theorem exists_sq_valued_wallDet {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ) (hA : Aᵀ = A)
    (hdetA : Valued.v ((A.det : ℤ) : Fv) = 1) (heven : ∀ i, Even (A i i))
    (S : Matrix (Fin N) (Fin N) Fv) (hS : ∀ i j, Valued.v (S i j) ≤ 1)
    (hSA : Sᵀ * A.map (Int.cast : ℤ → Fv) * S = A.map (Int.cast : ℤ → Fv)) {m : ℕ}
    {P R : Matrix (Fin N) (Fin m) Fv} (hf : IsWallFrame Fv S P R) :
    ∃ γ : ℤᵐ⁰, Valued.v (Pᵀ * A.map (Int.cast : ℤ → Fv) * R).det = γ ^ 2 := by
  classical
  set Af := A.map (Int.cast : ℤ → Fv)
  have hAf : ∀ i j, Valued.v (Af i j) ≤ 1 := fun i j => valued_intCast_le_one _
  have hAsym : Afᵀ = Af := by rw [← Matrix.transpose_map, hA]
  obtain ⟨m', W, W', f, Z, a, hW, hW', hWW', hW'W, hZ, ha, hframe, hspan⟩ := exists_snf_frame S hS
  set P0 : Matrix (Fin N) (Fin m') Fv := Matrix.of fun i j => W i (f j)
  set R0 : Matrix (Fin N) (Fin m') Fv := Z * Matrix.diagonal fun j => (a j)⁻¹
  have hP0 : ∀ i j, Valued.v (P0 i j) ≤ 1 := fun i j => hW _ _
  set U := P0ᵀ * Af * Z
  have hU : ∀ k j, Valued.v (U k j) ≤ 1 :=
    mul_integral _ _ (mul_integral _ _ (fun i j => hP0 j i) hAf) hZ
  have hC : P0ᵀ * Af * R0 = U * Matrix.diagonal fun j => (a j)⁻¹ := by
    simp only [R0, U, Matrix.mul_assoc]
  -- `Af` is invertible over `𝔬`
  have hdetAf : Af.det = ((A.det : ℤ) : Fv) := by
    have := RingHom.map_det (Int.castRingHom Fv) A
    rw [RingHom.mapMatrix_apply] at this
    exact this.symm
  have hdet0 : Af.det ≠ 0 := by
    intro h0; rw [hdetAf] at h0; rw [h0, map_zero] at hdetA; exact zero_ne_one hdetA
  have hAinv : ∀ i j, Valued.v (Af⁻¹ i j) ≤ 1 := by
    intro i j
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
    refine valued_mul_le_one ?_ ?_
    · rw [map_inv₀, hdetAf, hdetA, inv_one]
    · have := RingHom.map_adjugate (Int.castRingHom Fv) A
      rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at this
      change Valued.v ((A.map (Int.castRingHom Fv)).adjugate i j) ≤ 1
      rw [← this]
      exact valued_intCast_le_one _
  have hAAinv : Af * Af⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet0)
  -- `U` has an integral right inverse
  have hcolP0 : ∀ k, (fun i => P0 i k) = (1 - S) *ᵥ (fun i => R0 i k) := fun k => by
    ext i; rw [← mul_apply_col, hframe.1]
  have hright : ∀ i, ∃ r : Fin m' → Fv, (∀ j, Valued.v (r j) ≤ 1) ∧
      ∀ k, (U *ᵥ r) k = if k = i then 1 else 0 := by
    intro i
    set e : Fin N → Fv := Pi.single (f i) 1
    set w : Fin N → Fv := Af⁻¹ *ᵥ (W'ᵀ *ᵥ e)
    have hw : ∀ l, Valued.v (w l) ≤ 1 := by
      refine mulVec_integral _ _ hAinv (mulVec_integral _ _ (fun i j => hW' j i) fun l => ?_)
      simp only [e, Pi.single_apply]; split_ifs <;> simp
    obtain ⟨r, hr, hTr⟩ := hspan w hw
    refine ⟨r, hr, fun k => ?_⟩
    have hfix : S *ᵥ (w - Z *ᵥ r) = w - Z *ᵥ r := by
      have h0 : (1 - S) *ᵥ (w - Z *ᵥ r) = 0 := by rw [mulVec_sub, hTr, sub_self]
      rw [sub_mulVec, one_mulVec, sub_eq_zero] at h0
      exact h0.symm
    have horth := orth_ker_mat hSA (fun i => R0 i k) _ hfix
    rw [← hcolP0, mulVec_sub, dotProduct_sub, sub_eq_zero] at horth
    have h1 : (fun l => P0 l k) ⬝ᵥ (Af *ᵥ w) = if k = i then 1 else 0 := by
      have e1 : Af *ᵥ w = W'ᵀ *ᵥ e := by
        rw [mulVec_mulVec, hAAinv, one_mulVec]
      have e2 : (fun l => P0 l k) = W *ᵥ Pi.single (f k) 1 := by
        ext l; simp [P0, mulVec, dotProduct, Pi.single_apply]
      rw [e1, e2, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, ← transpose_mul,
        hW'W, transpose_one, one_mulVec, dotProduct_single, mul_one]
      simp only [e, Pi.single_apply, f.injective.eq_iff]
    have h2 : (fun l => P0 l k) ⬝ᵥ (Af *ᵥ (Z *ᵥ r)) = (U *ᵥ r) k := by
      rw [show U *ᵥ r = (P0ᵀ * Af) *ᵥ (Z *ᵥ r) by rw [mulVec_mulVec]]
      rw [← mulVec_mulVec]
      simp only [mulVec, dotProduct, transpose_apply]
    rw [← h2, ← horth, h1]
  choose r hr hUr using hright
  set V : Matrix (Fin m') (Fin m') Fv := Matrix.of fun j i => r i j
  have hUV : U * V = 1 := by
    ext k i
    rw [mul_apply_col]
    have : (fun j => V j i) = r i := rfl
    rw [this, hUr, Matrix.one_apply]
  have hdetU : Valued.v U.det = 1 := by
    have h1 := congrArg (fun M => Valued.v (Matrix.det M)) hUV
    simp only [det_mul, map_mul, det_one, map_one] at h1
    have hu := valued_det_le_one U hU
    have hv := valued_det_le_one V fun j i => hr i j
    by_contra hne
    have hlt : Valued.v U.det < 1 := lt_of_le_of_ne hu hne
    have := Levels.lt_one_of_lt_le hlt hv
    rw [h1] at this
    exact lt_irrefl _ this
  -- the symmetric part
  have hsymm := wall_symm_id hAsym hSA hframe.1
  rw [hC] at hsymm
  have hCe : ∀ k j, (U * Matrix.diagonal fun j => (a j)⁻¹) k j = U k j / a j := fun k j => by
    simp [mul_diagonal, div_eq_mul_inv]
  have hPP : ∀ k j, Valued.v ((P0ᵀ * Af * P0) k j) ≤ 1 :=
    mul_integral _ _ (mul_integral _ _ (fun i j => hP0 j i) hAf) hP0
  have hsym' : ∀ k j, Valued.v (U k j / a j + U j k / a k) ≤ 1 := by
    intro k j
    have := congrFun (congrFun hsymm k) j
    rw [Matrix.add_apply, transpose_apply, hCe, hCe] at this
    rw [this]; exact hPP k j
  have hdiag' : ∀ k, Valued.v (U k k / a k) ≤ 1 := by
    intro k
    have := congrFun (congrFun hsymm k) k
    rw [Matrix.add_apply, transpose_apply, hCe, gram_apply'] at this
    have e : U k k / a k = ((fun l => P0 l k) ⬝ᵥ (Af *ᵥ fun l => P0 l k)) / 2 := by
      rw [← this]; ring
    rw [e]
    exact valued_half_quad_le_one A hA heven _ fun l => hP0 l k
  obtain ⟨γ0, hγ0⟩ := Levels.exists_sq_prod_valued U a hU hdetU (fun j => (ha j).1) (fun j => (ha j).2)
    hsym' hdiag'
  have hγ0ne : γ0 ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, Finset.prod_eq_zero_iff] at hγ0
    obtain ⟨j, -, hj⟩ := hγ0
    exact (Valuation.ne_zero_iff _).mpr (ha j).1 hj
  -- compare with the given frame
  obtain rfl := wallFrame_size_eq hf hframe
  obtain ⟨u, hu0, hu⟩ := wallDet_eq_mat hSA hframe hf
  refine ⟨Valued.v u * γ0⁻¹, ?_⟩
  rw [hu, hC, map_mul, det_mul, map_mul, map_pow, det_diagonal, hdetU, one_mul, map_prod]
  simp only [map_inv₀]
  rw [Finset.prod_inv_distrib, hγ0, mul_pow, inv_pow]

end QuadFormsKB.ConwaySloane.EvenUnimodular
