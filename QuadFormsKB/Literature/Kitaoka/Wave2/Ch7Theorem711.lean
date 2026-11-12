/-
# Kitaoka 1993, Section 7.1: Theorem 7.1.1 (positive lattices of small rank are of E-type)

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §7.1, Theorem 7.1.1, p. 193 (printed page).

**Proves**
* `isEType_of_hermite`: if Hermite's constant satisfies $\mu_r < \sqrt r$ for $2 \le r \le r_0$, every positive
  lattice of rank $n \le r_0$ is of E-type;
* `theorem711_of_le_eight` (**unconditional**): every positive lattice of rank $n \le 8$ is of E-type;
* `theorem711_of_lemma712`: `Lemma712` (the stated bound $\mu_r < \sqrt r$, $2 \le r < 43$) implies `Theorem711`.

**Proof** (Kitaoka's). Let $X$ be a minimal vector of $L \otimes M$ ($L = (\mathbb Z^n, A)$, $M = (\mathbb Z^m, B)$),
an integer $n \times m$ matrix with $Q(X) = \operatorname{tr}(X^{\mathsf T} A X B)$. Write $X = PR$ with
$P \in M_{n \times r}(\mathbb Z)$ injective and $R \in M_{r \times m}(\mathbb Z)$ with independent rows
(`exists_factor`: $P$ is a $\mathbb Z$-basis of the saturation of the column lattice of $X$, from
`Submodule.basisOfPid`). The positive Gram matrices $G_A = P^{\mathsf T} A P$ and $G_B = R B R^{\mathsf T}$ of rank
$r$ satisfy $Q(X) = \operatorname{tr}(G_A G_B) \ge r(\det G_A \det G_B)^{1/r}$ (Lemma 7.1.3, `lemma713`).
For $c > \mu_r$, Hermite's bound gives nonzero integer $x', y'$ with $G_A[x'] < c(\det G_A)^{1/r}$ and
$G_B[y'] < c(\det G_B)^{1/r}$ (`exists_lt_hermite`; this avoids attainment of the minimum). Minimality gives
$Q(X) \le Q(Px' \otimes R^{\mathsf T}y') = G_A[x']\,G_B[y']$. Hence $r < c^2$; choosing $\mu_r < c < \sqrt r$ gives
a contradiction when $r \ge 2$. So $r \le 1$: $r = 0$ means $X = 0$, excluded, and $r = 1$ means $X = x y^{\mathsf T}$
is split. All indices are 0-based.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import QuadFormsKB.Literature.Kitaoka.Ch7EType
import QuadFormsKB.Literature.Kitaoka.Ch7TraceInequality
import QuadFormsKB.Literature.Kitaoka.Ch2Theorem211

open Matrix

noncomputable section

namespace QuadFormsKB.Kitaoka.EType

/-- A rational positive Gram matrix is positive definite as a real matrix. -/
theorem posDef_ratCast {r : ℕ} (G : Matrix (Fin r) (Fin r) ℚ) (hG : IsPosGram G) :
    (G.map (Rat.cast : ℚ → ℝ)).PosDef := by
  set Gr := G.map (Rat.cast : ℚ → ℝ) with hGr
  have hherm : Gr.IsHermitian := by
    have h : Gᵀ = G := hG.1
    have : Grᵀ = Gr := by rw [hGr, ← Matrix.transpose_map, h]
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hpsd : Gr.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => ?_
    simp only [star_trivial]
    have hdense : DenseRange (fun q : Fin r → ℚ => fun i => (q i : ℝ)) :=
      DenseRange.piMap (f := fun _ : Fin r => (Rat.cast : ℚ → ℝ)) fun _ => Rat.denseRange_cast
    have hcl : IsClosed {v : Fin r → ℝ | 0 ≤ v ⬝ᵥ (Gr *ᵥ v)} :=
      isClosed_le continuous_const (by simp only [dotProduct, mulVec]; fun_prop)
    have hsub : Set.range (fun q : Fin r → ℚ => fun i => (q i : ℝ)) ⊆ {v | 0 ≤ v ⬝ᵥ (Gr *ᵥ v)} := by
      rintro _ ⟨q, rfl⟩
      simp only [Set.mem_ofPred_eq]
      by_cases hq : q = 0
      · subst hq; simp
      · have h1 := (hG.2 q hq).le
        have h2 : ((fun i => (q i : ℝ)) ⬝ᵥ (Gr *ᵥ fun i => (q i : ℝ))) = ((q ⬝ᵥ (G *ᵥ q) : ℚ) : ℝ) := by
          simp [dotProduct, mulVec, Gr]
        rw [h2]; exact_mod_cast h1
    have := closure_minimal hsub hcl
    rw [hdense.closure_range] at this
    exact this (Set.mem_univ x)
  rw [Matrix.posDef_iff_posSemidef_and_mulVec_injective]
  refine ⟨hpsd, ?_⟩
  rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
  have hdet : G.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have := hG.2 v hv
    rw [hGv] at this
    simp at this
  have : Gr.det = (G.det : ℝ) := by
    have := (Rat.castHom ℝ).map_det G
    simpa [hGr] using this.symm
  rw [this]
  exact (Ne.isUnit (by exact_mod_cast hdet))

/-- Clearing denominators in a rational vector. -/
theorem exists_clear_denoms {r : ℕ} (v : Fin r → ℚ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ w : Fin r → ℤ, ∀ i, (D : ℚ) * v i = w i := by
  refine ⟨∏ i, ((v i).den : ℤ), ?_,
    fun i => (∏ j ∈ Finset.univ.erase i, ((v j).den : ℤ)) * (v i).num, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (v i).den_nz
  · intro i
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    push_cast
    rw [← Rat.mul_den_eq_num (v i)]
    ring

/-- An integer matrix with trivial kernel over $\mathbb Z$ has trivial kernel over $\mathbb Q$. -/
theorem mulVec_eq_zero_rat {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℤ)
    (h : ∀ v : Fin b → ℤ, M *ᵥ v = 0 → v = 0) (v : Fin b → ℚ)
    (hv : (M.map (Int.cast : ℤ → ℚ)) *ᵥ v = 0) : v = 0 := by
  obtain ⟨D, hD, w, hw⟩ := exists_clear_denoms v
  have h1 : M *ᵥ w = 0 := by
    ext i
    have h2 := congrFun hv i
    have h3 : ((M *ᵥ w) i : ℚ) = (D : ℚ) * ((M.map (Int.cast : ℤ → ℚ)) *ᵥ v) i := by
      simp only [mulVec, dotProduct, Matrix.map_apply, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hw j]; ring
    simp only [Pi.zero_apply] at h2
    rw [h2, mul_zero] at h3
    simpa using h3
  have h4 := h w h1
  ext i
  have := hw i
  rw [h4] at this
  simp only [Pi.zero_apply, Int.cast_zero] at this
  simpa [hD] using this

/-- Factorisation $X = PR$ with $P$ injective and $R$ of full row rank (over $\mathbb Z$), via a basis of the
saturation of the column lattice of $X$. -/
theorem exists_factor {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℤ) :
    ∃ (r : ℕ) (P : Matrix (Fin n) (Fin r) ℤ) (R : Matrix (Fin r) (Fin m) ℤ),
      X = P * R ∧ (∀ v, P *ᵥ v = 0 → v = 0) ∧ (∀ y : Fin r → ℤ, y ᵥ* R = 0 → y = 0) := by
  let S : Submodule ℤ (Fin n → ℤ) :=
    { carrier := {v | ∃ k : ℤ, k ≠ 0 ∧ ∃ w : Fin m → ℤ, X *ᵥ w = k • v}
      zero_mem' := ⟨1, one_ne_zero, 0, by simp⟩
      add_mem' := by
        rintro v1 v2 ⟨k1, hk1, w1, h1⟩ ⟨k2, hk2, w2, h2⟩
        refine ⟨k1 * k2, mul_ne_zero hk1 hk2, k2 • w1 + k1 • w2, ?_⟩
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h2, smul_add, smul_smul,
          smul_smul, mul_comm k2 k1]
      smul_mem' := by
        rintro c v ⟨k, hk, w, h1⟩
        refine ⟨k, hk, c • w, ?_⟩
        rw [Matrix.mulVec_smul, h1, smul_comm] }
  obtain ⟨r, bas⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin n)) S
  let P : Matrix (Fin n) (Fin r) ℤ := fun i j => (bas j : Fin n → ℤ) i
  have hcol : ∀ l, (fun i => X i l) ∈ S := fun l =>
    ⟨1, one_ne_zero, Pi.single l 1, by ext i; simp⟩
  let R : Matrix (Fin r) (Fin m) ℤ := fun j l => bas.repr ⟨_, hcol l⟩ j
  have hXPR : X = P * R := by
    ext i l
    have h := congrArg (fun s : S => (s : Fin n → ℤ) i) (bas.sum_repr ⟨_, hcol l⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_apply]
    simp only [P, R]
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hP : ∀ v, P *ᵥ v = 0 → v = 0 := by
    intro v hv
    have : ∑ j, v j • bas j = 0 := by
      apply Subtype.ext
      ext i
      have := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, P] at this
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Submodule.coe_zero, Pi.zero_apply]
      simp only [Pi.zero_apply] at this
      exact Eq.trans (Finset.sum_congr rfl fun j _ => mul_comm _ _) this
    exact funext (Fintype.linearIndependent_iff.mp bas.linearIndependent v this)
  refine ⟨r, P, R, hXPR, hP, ?_⟩
  intro y hy
  ext j
  obtain ⟨k, hk, w, hw⟩ := (bas j).2
  have hPj : P *ᵥ (Pi.single j 1 : Fin r → ℤ) = (bas j : Fin n → ℤ) := by
    rw [Matrix.mulVec_single_one]; rfl
  have h1 : R *ᵥ w = k • (Pi.single j 1 : Fin r → ℤ) := by
    have : P *ᵥ (R *ᵥ w - k • (Pi.single j 1 : Fin r → ℤ)) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← hXPR, hw, Matrix.mulVec_smul, hPj, sub_self]
    exact sub_eq_zero.mp (hP _ this)
  have h2 : y ⬝ᵥ (R *ᵥ w) = 0 := by
    rw [Matrix.dotProduct_mulVec, hy]; simp
  rw [h1] at h2
  simp only [dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul] at h2
  have : k * y j = 0 := by simpa [mul_comm] using h2
  simpa [hk] using this

/-- The rational matrix of an integer matrix. -/
abbrev qmat {a b : ℕ} (C : Matrix (Fin a) (Fin b) ℤ) : Matrix (Fin a) (Fin b) ℚ :=
  C.map (Int.cast : ℤ → ℚ)

/-- $v^{\mathsf T} (C^{\mathsf T} M C) v = (Cv)^{\mathsf T} M (Cv)$. -/
theorem quad_conj {a b : ℕ} (C : Matrix (Fin a) (Fin b) ℚ) (M : Matrix (Fin a) (Fin a) ℚ) (v : Fin b → ℚ) :
    v ⬝ᵥ ((Cᵀ * M * C) *ᵥ v) = (C *ᵥ v) ⬝ᵥ (M *ᵥ (C *ᵥ v)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- For an integer matrix $C$ and an integer vector $x$: $x^{\mathsf T}(C^{\mathsf T} A C)x = Q_A(Cx)$. -/
theorem quad_conj_gramQ {a b : ℕ} (C : Matrix (Fin a) (Fin b) ℤ) (A : Matrix (Fin a) (Fin a) ℚ)
    (x : Fin b → ℤ) :
    (fun i => (x i : ℚ)) ⬝ᵥ (((qmat C)ᵀ * A * qmat C) *ᵥ fun i => (x i : ℚ)) = gramQ A (C *ᵥ x) := by
  rw [quad_conj]
  have : (fun i => ((C *ᵥ x) i : ℚ)) = qmat C *ᵥ fun i => (x i : ℚ) := by
    ext i; simp [Matrix.mulVec, dotProduct, qmat]
  rw [gramQ, this]

/-- Real cast of a rational quadratic form value. -/
theorem cast_quad {r : ℕ} (G : Matrix (Fin r) (Fin r) ℚ) (x : Fin r → ℤ) :
    ((fun i => (x i : ℝ)) ⬝ᵥ ((G.map (Rat.cast : ℚ → ℝ)) *ᵥ fun i => (x i : ℝ))) =
      (((fun i => (x i : ℚ)) ⬝ᵥ (G *ᵥ fun i => (x i : ℚ)) : ℚ) : ℝ) := by
  simp [dotProduct, mulVec]

/-- Conjugating a positive Gram matrix by an injective integer matrix gives a positive Gram matrix. -/
theorem isPosGram_conj {a b : ℕ} (C : Matrix (Fin a) (Fin b) ℤ) (hC : ∀ v, C *ᵥ v = 0 → v = 0)
    (A : Matrix (Fin a) (Fin a) ℚ) (hA : IsPosGram A) : IsPosGram ((qmat C)ᵀ * A * qmat C) := by
  refine ⟨?_, fun v hv => ?_⟩
  · have := hA.1
    simp only [Matrix.IsSymm] at this ⊢
    simp [Matrix.transpose_mul, this, Matrix.mul_assoc]
  · rw [quad_conj]
    apply hA.2
    intro h
    exact hv (mulVec_eq_zero_rat C hC v h)

/-- $Q(X) = \operatorname{tr}(X^{\mathsf T} A X B)$ for symmetric $B$. -/
theorem tensorQ_eq_trace {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin m) (Fin m) ℚ)
    (hB : B.IsSymm) (X : Matrix (Fin n) (Fin m) ℤ) :
    tensorQ A B X = ((qmat X)ᵀ * A * qmat X * B).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, Matrix.transpose_apply, qmat,
    Matrix.map_apply, tensorQ]
  have hs : ∀ j l, B l j = B j l := fun j l => by
    have := congrFun (congrFun hB j) l
    simpa using this
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans
    (Finset.sum_comm.trans (Finset.sum_congr rfl fun l _ => Finset.sum_comm.trans
      (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_)))
  rw [hs]; ring

/-- $Q(PR) = \operatorname{tr}(G_A G_B)$ with $G_A = P^{\mathsf T} A P$ and $G_B = R B R^{\mathsf T}$. -/
theorem tensorQ_factor {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin m) (Fin m) ℚ)
    (hB : B.IsSymm) (X : Matrix (Fin n) (Fin m) ℤ) (P : Matrix (Fin n) (Fin r) ℤ)
    (R : Matrix (Fin r) (Fin m) ℤ) (hX : X = P * R) :
    tensorQ A B X =
      (((qmat P)ᵀ * A * qmat P) * ((qmat Rᵀ)ᵀ * B * qmat Rᵀ)).trace := by
  rw [tensorQ_eq_trace A B hB]
  have hq : qmat X = qmat P * qmat R := by
    subst hX; ext i j; simp [qmat, Matrix.mul_apply]
  have hqt : qmat Rᵀ = (qmat R)ᵀ := by ext i j; simp [qmat]
  rw [hq, hqt]
  calc ((qmat P * qmat R)ᵀ * A * (qmat P * qmat R) * B).trace
      = ((qmat R)ᵀ * ((qmat P)ᵀ * A * qmat P * qmat R * B)).trace := by
        congr 1; simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (((qmat P)ᵀ * A * qmat P * qmat R * B) * (qmat R)ᵀ).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp [Matrix.mul_assoc]

/-- Hermite's bound with slack: for positive definite real $p$ of size $r \ge 2$ and $c > \mu_r$ there is a nonzero
integer vector $x$ with $p[x] < c \,(\det p)^{1/r}$. -/
theorem exists_lt_hermite {r : ℕ} (hr : 2 ≤ r) (p : Matrix (Fin r) (Fin r) ℝ) (hp : p.PosDef) (c : ℝ)
    (hc : Reduction.hermiteConst r < c) :
    ∃ x : Fin r → ℤ, x ≠ 0 ∧
      (fun i => (x i : ℝ)) ⬝ᵥ (p *ᵥ fun i => (x i : ℝ)) < c * p.det ^ ((1 : ℝ) / r) := by
  have hd : 0 < p.det ^ ((1 : ℝ) / r) := Real.rpow_pos_of_pos hp.det_pos _
  have hle : Reduction.latMin p / p.det ^ ((1 : ℝ) / r) ≤ Reduction.hermiteConst r := by
    refine le_csSup ⟨(4 / 3 : ℝ) ^ (((r : ℝ) - 1) / 2), ?_⟩ ⟨p, hp, rfl⟩
    rintro _ ⟨q, hq, rfl⟩
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hq.det_pos _)]
    exact (Reduction.theorem211 r hr).2 q hq
  have hlt : Reduction.latMin p < c * p.det ^ ((1 : ℝ) / r) := by
    have := hle.trans_lt hc
    rwa [div_lt_iff₀ hd] at this
  have hne : {s : ℝ | ∃ x : Fin r → ℤ, x ≠ 0 ∧
      s = (fun i => (x i : ℝ)) ⬝ᵥ (p *ᵥ fun i => (x i : ℝ))}.Nonempty := by
    refine ⟨_, fun _ => 1, ?_, rfl⟩
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp at this
  obtain ⟨s, ⟨x, hx, rfl⟩, hs⟩ := exists_lt_of_csInf_lt hne hlt
  exact ⟨x, hx, hs⟩

/-- **Core of Kitaoka's argument.** A minimal vector $X = PR$ of $L \otimes M$ with $P$ injective and $R$ of full row
rank $r \ge 2$ cannot exist when $\mu_r < \sqrt r$. -/
theorem false_of_rank_ge_two {n m r : ℕ} (hr : 2 ≤ r) (hμ : Reduction.hermiteConst r < Real.sqrt r)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsPosGram A) (B : Matrix (Fin m) (Fin m) ℚ) (hB : IsPosGram B)
    (X : Matrix (Fin n) (Fin m) ℤ) (hX : IsMinimalTensor A B X)
    (P : Matrix (Fin n) (Fin r) ℤ) (R : Matrix (Fin r) (Fin m) ℤ) (hXPR : X = P * R)
    (hP : ∀ v, P *ᵥ v = 0 → v = 0) (hR : ∀ y : Fin r → ℤ, y ᵥ* R = 0 → y = 0) : False := by
  have hC : ∀ y, Rᵀ *ᵥ y = 0 → y = 0 := fun y h => hR y (by rwa [Matrix.mulVec_transpose] at h)
  set GA := (qmat P)ᵀ * A * qmat P with hGA
  set GB := (qmat Rᵀ)ᵀ * B * qmat Rᵀ with hGB
  have hGApos : IsPosGram GA := isPosGram_conj P hP A hA
  have hGBpos : IsPosGram GB := isPosGram_conj Rᵀ hC B hB
  set GAr := GA.map (Rat.cast : ℚ → ℝ) with hGAr
  set GBr := GB.map (Rat.cast : ℚ → ℝ) with hGBr
  have hAr : GAr.PosDef := posDef_ratCast GA hGApos
  have hBr : GBr.PosDef := posDef_ratCast GB hGBpos
  have hT : (tensorQ A B X : ℝ) = (GAr * GBr).trace := by
    rw [tensorQ_factor A B hB.1 X P R hXPR]
    have hmap : (GA * GB).map (Rat.cast : ℚ → ℝ) = GAr * GBr := Matrix.map_mul (f := Rat.castHom ℝ)
    have hGG : (qmat P)ᵀ * A * qmat P * ((qmat Rᵀ)ᵀ * B * qmat Rᵀ) = GA * GB := rfl
    rw [hGG, ← hmap]
    simp [Matrix.trace, Matrix.diag]
  have h713 := lemma713 r GAr GBr hAr hBr
  rw [← hT] at h713
  have hrR : (1 : ℝ) < Real.sqrt r := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num; exact_mod_cast hr
  set μ := Reduction.hermiteConst r with hμdef
  set c : ℝ := max ((μ + Real.sqrt r) / 2) 1 with hc
  have hc1 : μ < c := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hc2 : c < Real.sqrt r := max_lt (by linarith) hrR
  have hc0 : 0 ≤ c := le_trans zero_le_one (le_max_right _ _)
  have hc3 : c ^ 2 < r := (Real.lt_sqrt hc0).mp hc2
  obtain ⟨x', hx'0, hx'⟩ := exists_lt_hermite hr GAr hAr c hc1
  obtain ⟨y', hy'0, hy'⟩ := exists_lt_hermite hr GBr hBr c hc1
  have ha : (fun i => (x' i : ℝ)) ⬝ᵥ (GAr *ᵥ fun i => (x' i : ℝ)) = ((gramQ A (P *ᵥ x') : ℚ) : ℝ) := by
    rw [hGAr, cast_quad, hGA, quad_conj_gramQ]
  have hb : (fun i => (y' i : ℝ)) ⬝ᵥ (GBr *ᵥ fun i => (y' i : ℝ)) = ((gramQ B (Rᵀ *ᵥ y') : ℚ) : ℝ) := by
    rw [hGBr, cast_quad, hGB, quad_conj_gramQ]
  have hxne : (fun i => (x' i : ℝ)) ≠ 0 := fun h => hx'0 (by
    ext i; have := congrFun h i; simpa using this)
  have hyne : (fun i => (y' i : ℝ)) ≠ 0 := fun h => hy'0 (by
    ext i; have := congrFun h i; simpa using this)
  have hapos := hAr.dotProduct_mulVec_pos hxne
  have hbpos := hBr.dotProduct_mulVec_pos hyne
  simp only [star_trivial] at hapos hbpos
  have hmin : tensorQ A B X ≤ gramQ A (P *ᵥ x') * gramQ B (Rᵀ *ᵥ y') := by
    rw [← tensorQ_vecMulVec]
    exact hX.2 _ (vecMulVec_ne_zero (fun h => hx'0 (hP _ h)) (fun h => hy'0 (hC _ h)))
  have hminR : (tensorQ A B X : ℝ) ≤
      ((fun i => (x' i : ℝ)) ⬝ᵥ (GAr *ᵥ fun i => (x' i : ℝ))) *
        ((fun i => (y' i : ℝ)) ⬝ᵥ (GBr *ᵥ fun i => (y' i : ℝ))) := by
    rw [ha, hb, ← Rat.cast_mul]; exact_mod_cast hmin
  have hdA := hAr.det_pos
  have hdB := hBr.det_pos
  have hprod : ((fun i => (x' i : ℝ)) ⬝ᵥ (GAr *ᵥ fun i => (x' i : ℝ))) *
        ((fun i => (y' i : ℝ)) ⬝ᵥ (GBr *ᵥ fun i => (y' i : ℝ))) <
      c ^ 2 * (GAr.det * GBr.det) ^ ((1 : ℝ) / r) := by
    have := mul_lt_mul'' hx'  hy' hapos.le hbpos.le
    rw [Real.mul_rpow hdA.le hdB.le]
    calc _ < _ := this
      _ = _ := by ring
  have hpos : 0 < (GAr.det * GBr.det) ^ ((1 : ℝ) / r) := Real.rpow_pos_of_pos (mul_pos hdA hdB) _
  have hfin : (r : ℝ) * (GAr.det * GBr.det) ^ ((1 : ℝ) / r) <
      c ^ 2 * (GAr.det * GBr.det) ^ ((1 : ℝ) / r) := by
    calc _ ≤ _ := h713
      _ ≤ _ := hminR
      _ < _ := hprod
  have := lt_of_mul_lt_mul_right hfin hpos.le
  linarith

/-- **Kitaoka 1993, Theorem 7.1.1 from Hermite's bound** (p. 193): if $\mu_r < \sqrt r$ for all $2 \le r \le r_0$, then
every positive lattice of rank $n \le r_0$ is of E-type. *Proof* (Kitaoka's): a minimal vector $X$ of $L \otimes M$ is
$X = PR$ with $P \in M_{n \times r}(\mathbb Z)$, $R \in M_{r \times m}(\mathbb Z)$ of rank $r$ (basis of the
saturation of the column lattice of $X$). The rank-$r$ lattices $P^{\mathsf T} A P$ and $R B R^{\mathsf T}$ satisfy
$Q(X) = \operatorname{tr}(G_A G_B) \ge r(\det G_A \det G_B)^{1/r}$ (Lemma 7.1.3), while Hermite's bound produces
$x', y'$ with $Q(X) \le G_A[x']\,G_B[y'] < c^2(\det G_A \det G_B)^{1/r}$ for any $c > \mu_r$. With $c < \sqrt r$
this forces $r \le 1$, and $r = 1$ means $X = x y^{\mathsf T}$ is split ($r = 0$ means $X = 0$). -/
theorem isEType_of_hermite (r₀ : ℕ)
    (hμ : ∀ r, 2 ≤ r → r ≤ r₀ → Reduction.hermiteConst r < Real.sqrt r) (n : ℕ) (hn : n ≤ r₀)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsPosGram A) : IsEType A := by
  intro m B hB X hX
  obtain ⟨r, P, R, hXPR, hP, hR⟩ := exists_factor X
  have hrn : r ≤ n := by
    have hinj : Function.Injective P.mulVecLin := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      exact hP v hv
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using this
  rcases Nat.lt_or_ge r 2 with h | h
  · interval_cases r
    · exfalso
      apply hX.1
      rw [hXPR]
      ext i j
      simp [Matrix.mul_apply]
    · exact ⟨fun i => P i 0, R 0, by ext i j; simp [hXPR, Matrix.mul_apply, vecMulVec_apply]⟩
  · exact (false_of_rank_ge_two h (hμ r h (hrn.trans hn)) A hA B hB X hX P R hXPR hP hR).elim

/-- **Kitaoka 1993, Theorem 7.1.1 for rank $\le 8$** (p. 193), *proved unconditionally*: every positive lattice of
rank $n \le 8$ is of E-type. Uses $\mu_r < \sqrt r$ for $2 \le r \le 8$ (`lemma712_of_le_eight`, from Hermite's
bound $(4/3)^{(r-1)/2}$) and `isEType_of_hermite`. -/
@[kb "kitaoka1993" "§7.1, Thm. 7.1.1, p. 193 (rank ≤ 8)"]
theorem theorem711_of_le_eight (n : ℕ) (hn : n ≤ 8) (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsPosGram A) :
    IsEType A :=
  isEType_of_hermite 8 (fun r h2 h8 => lemma712_of_le_eight r h2 h8) n hn A hA

/-- **Kitaoka 1993, Theorem 7.1.1 from Lemma 7.1.2** (p. 193): the stated Hermite bound `Lemma712`
($\mu_r < \sqrt r$ for $2 \le r < 43$) implies `Theorem711` (every positive lattice of rank $< 43$ is of E-type). -/
@[kb "kitaoka1993" "§7.1, Thm. 7.1.1, p. 193 (from Lemma 7.1.2)"]
theorem theorem711_of_lemma712 (h : Lemma712) : Theorem711 :=
  fun n hn A hA => isEType_of_hermite 42 (fun r h2 h42 => h r h2 (by omega)) n (by omega) A hA

end QuadFormsKB.Kitaoka.EType
