/-
# O'Meara §101A over an arbitrary valuated field

**Layer:** $K$ is an arbitrary valuated field in O'Meara's sense (a field with a real absolute value satisfying the
triangle inequality, archimedean or not), modelled as `{K : Type*} [NormedField K]`. The space is
$V = K^n$ = `Fin n → K` with the standard base $e_0, \dots, e_{n-1}$ (O'Meara's $x_1, \dots, x_n$; indices are
0-based). The non-archimedean case is `[IsUltrametricDist K]`. The companion file `Sec101A.lean` treats the
non-archimedean case at a finite place of a number field with norms in `ℤᵐ⁰`.

**Norms are Mathlib's.** O'Meara's $\lVert x\rVert = \max_i \lvert x_i\rvert$ is the sup norm on `Fin n → K`.
For matrices (= linear maps in the standard base) O'Meara's $\lVert\sigma\rVert = \max_{i,j}\lvert a_{ij}\rvert$ is
Mathlib's entrywise sup norm, available through the (non-global) instances `Matrix.normedAddCommGroup` and
`Matrix.normedSpace`, activated locally below. Nothing new is defined except the bilinear form `omearaBil`.
All names live in the namespace `QuadFormsKB.Lattices.Valuated` (several are generic, e.g. `norm_mul_le`).

**Proves** (each theorem is tagged with its book locator)
* 101.r5: `abs_norm_sub_norm_le_norm_sub`, `dist_eq_norm_sub`; 101.r6–r8: `norm_add_le_max`,
  `norm_add_eq_max_of_ne`, `eventually_norm_eq`;
* 101.r9–r10: `continuous_add_vec`, `continuous_neg_vec`, `continuous_smul_vec`, `continuous_sum_vec`,
  `continuous_norm_vec`;
* 101.r12–r13: the matrix versions;
* 101.r14–r16: `norm_mulVec_le`, `norm_mulVec_le_of_ultra`, `norm_mul_le`, `norm_mul_le_of_ultra`, and continuity of
  products, sums, `(σ, x) ↦ σx`;
* 101.r17: continuity of $\det$, openness of $\mathrm{GL}$, continuity of inversion;
* 101.r18 / Example 101:1 (general case): `norm_le_mul_norm_inv_mulVec`, `norm_inv_mulVec_le_mul_norm`,
  `norm_conj_le`, `norm_le_conj`;
* 101.r19–r23: the bilinear form bound, the quadratic form bound, continuity, openness of the anisotropic vectors;
* 101.r24: $\det\sigma = \pm 1$ and $\lvert\det\sigma\rvert_\mathfrak p = 1$ for $\sigma \in O(V_\mathfrak p)$.

**Deviations.** (a) The constants $n$, $n^2$ in the general-case inequalities are *reconstructed from the argument*
(a sum of $n$ terms); the printed formulas are illegible in the scan. (b) O'Meara assumes $V$ regular for the bound
on $B$; it holds without it. (c) The theorems about matrices and vectors are stated for the norm topology given by
the local instances (this topology is the product topology).
-/
import QuadFormsKB.Tamagawa.LocalVolume

open Matrix Topology Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices.Valuated

variable {K : Type*} [NormedField K] {n : ℕ}

/-! ### Vectors -/

section Vectors

/-- **Reverse triangle inequality for vectors** (O'Meara 1973, §101A, p. 285): for the norm
$\lVert x\rVert = \max_i\lvert x_i\rvert$ on $V = K^n$ (Mathlib's sup norm on `Fin n → K`),
$\lvert\,\lVert x\rVert - \lVert y\rVert\,\rvert \le \lVert x - y\rVert$. -/
@[kb "omeara1963" "§101A, p. 285 (| ‖x‖ − ‖y‖ | ≤ ‖x − y‖)"]
theorem abs_norm_sub_norm_le_norm_sub (x y : Fin n → K) : |‖x‖ - ‖y‖| ≤ ‖x - y‖ :=
  abs_norm_sub_norm_le x y

/-- **$V$ is a metric space with distance $\lVert x - y\rVert$** (O'Meara 1973, §101A, p. 285): the metric of
`Fin n → K` is `dist x y = ‖x - y‖`. -/
@[kb "omeara1963" "§101A, p. 285 (distance ‖x − y‖ on V)"]
theorem dist_eq_norm_sub (x y : Fin n → K) : dist x y = ‖x - y‖ :=
  dist_eq_norm x y

/-- **Ultrametric inequality** $\lVert x + y\rVert \le \max(\lVert x\rVert, \lVert y\rVert)$ for $K$
non-archimedean (O'Meara 1973, §101A, p. 285). -/
@[kb "omeara1963" "§101A, p. 285 (‖x + y‖ ≤ max(‖x‖, ‖y‖), non-archimedean)"]
theorem norm_add_le_max [IsUltrametricDist K] (x y : Fin n → K) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ :=
  IsUltrametricDist.norm_add_le_max x y

/-- **$\lVert x + y\rVert = \max(\lVert x\rVert, \lVert y\rVert)$ if $\lVert x\rVert \ne \lVert y\rVert$**, $K$
non-archimedean (O'Meara 1973, §101A, p. 285). -/
@[kb "omeara1963" "§101A, p. 285 (‖x + y‖ = max if ‖x‖ ≠ ‖y‖, non-archimedean)"]
theorem norm_add_eq_max_of_ne [IsUltrametricDist K] {x y : Fin n → K} (h : ‖x‖ ≠ ‖y‖) :
    ‖x + y‖ = max ‖x‖ ‖y‖ :=
  IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h

/-- In an ultrametric normed group the norm is constant near any nonzero point. -/
theorem eventually_norm_eq_of_ultra {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] {x₀ : E}
    (h : x₀ ≠ 0) : ∀ᶠ x in 𝓝 x₀, ‖x‖ = ‖x₀‖ := by
  filter_upwards [Metric.ball_mem_nhds x₀ (norm_pos_iff.mpr h)] with x hx
  rw [mem_ball_iff_norm] at hx
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := x₀) (y := x - x₀) hx.ne'
  rwa [add_sub_cancel, max_eq_left hx.le] at this

/-- **Local constancy of the norm** (O'Meara 1973, §101A, p. 285): for $K$ non-archimedean and
$x_0 \ne 0$ there is a neighbourhood of $x_0$ on which $\lVert x\rVert = \lVert x_0\rVert$. -/
@[kb "omeara1963" "§101A, p. 285 (‖x‖ = ‖x₀‖ near x₀ ≠ 0, non-archimedean)"]
theorem eventually_norm_eq [IsUltrametricDist K] {x₀ : Fin n → K} (h : x₀ ≠ 0) :
    ∀ᶠ x in 𝓝 x₀, ‖x‖ = ‖x₀‖ :=
  eventually_norm_eq_of_ultra h

/-- **Continuity of addition on $V$** (O'Meara 1973, §101A, p. 286). -/
@[kb "omeara1963" "§101A, p. 286 (continuity of (x, y) ↦ x + y)"]
theorem continuous_add_vec : Continuous fun p : (Fin n → K) × (Fin n → K) => p.1 + p.2 :=
  continuous_add

/-- **Continuity of negation on $V$** (O'Meara 1973, §101A, p. 286). -/
@[kb "omeara1963" "§101A, p. 286 (continuity of x ↦ −x)"]
theorem continuous_neg_vec : Continuous fun x : Fin n → K => -x :=
  continuous_neg

/-- **Continuity of scalar multiplication** $K \times V \to V$ (O'Meara 1973, §101A, p. 286). -/
@[kb "omeara1963" "§101A, p. 286 (continuity of (a, x) ↦ ax)"]
theorem continuous_smul_vec : Continuous fun p : K × (Fin n → K) => p.1 • p.2 :=
  continuous_smul

/-- **Continuity of the sum map** $V \times \dots \times V \to V$ ($m$ factors; O'Meara 1973, §101A, p. 286). -/
@[kb "omeara1963" "§101A, p. 286 (continuity of (x₁, …, x_m) ↦ x₁ + ⋯ + x_m)"]
theorem continuous_sum_vec (m : ℕ) : Continuous fun f : Fin m → (Fin n → K) => ∑ i, f i :=
  continuous_finsetSum _ fun i _ => continuous_apply i

/-- **Continuity of the norm** $V \to \mathbb R$ (O'Meara 1973, §101A, p. 286). -/
@[kb "omeara1963" "§101A, p. 286 (continuity of x ↦ ‖x‖)"]
theorem continuous_norm_vec : Continuous fun x : Fin n → K => ‖x‖ :=
  continuous_norm

end Vectors

/-! ### Matrices -/

section Matrices

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

local instance [IsUltrametricDist K] : IsUltrametricDist (Matrix (Fin n) (Fin n) K) :=
  inferInstanceAs (IsUltrametricDist (Fin n → Fin n → K))

/-- **$\lVert\cdot\rVert$ is a norm on matrices** (O'Meara 1973, §101A, p. 286, properties (1)–(3)): for the
entrywise sup norm $\lVert\sigma\rVert = \max_{i,j}\lvert a_{ij}\rvert$ (Mathlib's, via the local instances),
(1) $\lVert\sigma\rVert \ge 0$ with equality iff $\sigma = 0$, (2) $\lVert a\sigma\rVert = \lvert a\rvert\lVert\sigma\rVert$,
(3) $\lVert\sigma + \tau\rVert \le \lVert\sigma\rVert + \lVert\tau\rVert$. -/
@[kb "omeara1963" "§101A, p. 286 (norm properties (1)-(3) for ‖σ‖ = max |a_ij|)"]
theorem matrix_norm_axioms :
    (∀ σ : Matrix (Fin n) (Fin n) K, 0 ≤ ‖σ‖ ∧ (‖σ‖ = 0 ↔ σ = 0)) ∧
    (∀ (a : K) (σ : Matrix (Fin n) (Fin n) K), ‖a • σ‖ = ‖a‖ * ‖σ‖) ∧
    (∀ σ τ : Matrix (Fin n) (Fin n) K, ‖σ + τ‖ ≤ ‖σ‖ + ‖τ‖) :=
  ⟨fun σ => ⟨norm_nonneg σ, norm_eq_zero⟩, fun a σ => norm_smul a σ, fun σ τ => norm_add_le σ τ⟩

/-- **Reverse triangle inequality for matrices** (O'Meara 1973, §101A, p. 286):
$\lvert\,\lVert\sigma\rVert - \lVert\tau\rVert\,\rvert \le \lVert\sigma - \tau\rVert$. -/
@[kb "omeara1963" "§101A, p. 286 (| ‖σ‖ − ‖τ‖ | ≤ ‖σ − τ‖)"]
theorem abs_norm_sub_norm_le_norm_sub_mat (σ τ : Matrix (Fin n) (Fin n) K) : |‖σ‖ - ‖τ‖| ≤ ‖σ - τ‖ :=
  abs_norm_sub_norm_le σ τ

/-- **Ultrametric inequality for matrices** (O'Meara 1973, §101A, p. 286), $K$ non-archimedean. -/
@[kb "omeara1963" "§101A, p. 286 (‖σ + τ‖ ≤ max(‖σ‖, ‖τ‖), non-archimedean)"]
theorem norm_add_le_max_mat [IsUltrametricDist K] (σ τ : Matrix (Fin n) (Fin n) K) :
    ‖σ + τ‖ ≤ max ‖σ‖ ‖τ‖ :=
  IsUltrametricDist.norm_add_le_max σ τ

/-- **Equality case for matrices** (O'Meara 1973, §101A, p. 286), $K$ non-archimedean:
$\lVert\sigma + \tau\rVert = \max(\lVert\sigma\rVert, \lVert\tau\rVert)$ if $\lVert\sigma\rVert \ne \lVert\tau\rVert$. -/
@[kb "omeara1963" "§101A, p. 286 (‖σ + τ‖ = max if ‖σ‖ ≠ ‖τ‖, non-archimedean)"]
theorem norm_add_eq_max_of_ne_mat [IsUltrametricDist K] {σ τ : Matrix (Fin n) (Fin n) K}
    (h : ‖σ‖ ≠ ‖τ‖) : ‖σ + τ‖ = max ‖σ‖ ‖τ‖ :=
  IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h

/-- **Local constancy of the matrix norm** (O'Meara 1973, §101A, p. 286), $K$ non-archimedean, $\sigma_0 \ne 0$. -/
@[kb "omeara1963" "§101A, p. 286 (‖σ‖ = ‖σ₀‖ near σ₀ ≠ 0, non-archimedean)"]
theorem eventually_norm_eq_mat [IsUltrametricDist K] {σ₀ : Matrix (Fin n) (Fin n) K} (h : σ₀ ≠ 0) :
    ∀ᶠ σ in 𝓝 σ₀, ‖σ‖ = ‖σ₀‖ :=
  eventually_norm_eq_of_ultra h

/-- **Continuity of addition on $L(V) = M_n(K)$** (O'Meara 1973, §101A, p. 286). -/
@[kb "omeara1963" "§101A, p. 286 (continuity of (σ, τ) ↦ σ + τ)"]
theorem continuous_add_mat :
    Continuous fun p : Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K => p.1 + p.2 :=
  continuous_add

/-- **Continuity of negation on $L(V)$** (O'Meara 1973, §101A, p. 286). -/
@[kb "omeara1963" "§101A, p. 286 (continuity of σ ↦ −σ)"]
theorem continuous_neg_mat : Continuous fun σ : Matrix (Fin n) (Fin n) K => -σ :=
  continuous_neg

/-- **Continuity of scalar multiplication on $L(V)$** (O'Meara 1973, §101A, p. 286). -/
@[kb "omeara1963" "§101A, p. 286 (continuity of (a, σ) ↦ aσ)"]
theorem continuous_smul_mat :
    Continuous fun p : K × Matrix (Fin n) (Fin n) K => p.1 • p.2 :=
  continuous_smul

/-- **A product bound** $\lVert x\cdot y\rVert \le n\lVert x\rVert\lVert y\rVert$ for $x, y \in K^n$ with
$x\cdot y = \sum_i x_iy_i$ (auxiliary). -/
theorem norm_dotProduct_le (x y : Fin n → K) : ‖x ⬝ᵥ y‖ ≤ n * ‖x‖ * ‖y‖ := by
  rw [dotProduct]
  calc ‖∑ i, x i * y i‖ ≤ ∑ i, ‖x i * y i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖x‖ * ‖y‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_mul]
        exact mul_le_mul (norm_le_pi_norm x i) (norm_le_pi_norm y i) (norm_nonneg _) (norm_nonneg _)
    _ = n * ‖x‖ * ‖y‖ := by simp [mul_assoc]

/-- **$\lVert\sigma x\rVert \le n\,\lVert\sigma\rVert\,\lVert x\rVert$** in general (O'Meara 1973, §101A, pp. 286–287;
$\sigma x$ is `A *ᵥ x`). *The constant $n$ is reconstructed from the argument (a sum of $n$ terms); the printed
formula is illegible in the scan.* -/
@[kb "omeara1963" "§101A, pp. 286–287 (‖σx‖ ≤ n‖σ‖‖x‖, constant reconstructed)"]
theorem norm_mulVec_le (A : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    ‖A *ᵥ x‖ ≤ n * ‖A‖ * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  calc ‖(A *ᵥ x) i‖ = ‖A i ⬝ᵥ x‖ := rfl
    _ ≤ n * ‖A i‖ * ‖x‖ := norm_dotProduct_le _ _
    _ ≤ n * ‖A‖ * ‖x‖ := by
        gcongr
        exact norm_le_pi_norm A i

/-- **$\lVert\sigma x\rVert \le \lVert\sigma\rVert\,\lVert x\rVert$**, $K$ non-archimedean (O'Meara 1973, §101A,
pp. 286–287). -/
@[kb "omeara1963" "§101A, pp. 286–287 (‖σx‖ ≤ ‖σ‖‖x‖, non-archimedean)"]
theorem norm_mulVec_le_of_ultra [IsUltrametricDist K] (A : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    ‖A *ᵥ x‖ ≤ ‖A‖ * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  rw [mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun j _ => ?_
  rw [norm_mul]
  exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A) (norm_le_pi_norm x j) (norm_nonneg _)
    (norm_nonneg _)

/-- **$\lVert\sigma\tau\rVert \le n\,\lVert\sigma\rVert\,\lVert\tau\rVert$** in general (O'Meara 1973, §101A, p. 287).
*The constant $n$ is reconstructed from the argument; the printed formula is illegible in the scan.* -/
@[kb "omeara1963" "§101A, p. 287 (‖στ‖ ≤ n‖σ‖‖τ‖, constant reconstructed)"]
theorem norm_mul_le (A B : Matrix (Fin n) (Fin n) K) : ‖A * B‖ ≤ n * ‖A‖ * ‖B‖ := by
  refine (Matrix.norm_le_iff (by positivity)).mpr fun i j => ?_
  rw [mul_apply]
  calc ‖∑ k, A i k * B k j‖ ≤ ∑ k, ‖A i k * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin n, ‖A‖ * ‖B‖ := Finset.sum_le_sum fun k _ => by
        rw [norm_mul]
        exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A)
          (Matrix.norm_entry_le_entrywise_sup_norm B) (norm_nonneg _) (norm_nonneg _)
    _ = n * ‖A‖ * ‖B‖ := by simp [mul_assoc]

/-- **$\lVert\sigma\tau\rVert \le \lVert\sigma\rVert\,\lVert\tau\rVert$**, $K$ non-archimedean (O'Meara 1973, §101A,
p. 287). -/
@[kb "omeara1963" "§101A, p. 287 (‖στ‖ ≤ ‖σ‖‖τ‖, non-archimedean)"]
theorem norm_mul_le_of_ultra [IsUltrametricDist K] (A B : Matrix (Fin n) (Fin n) K) :
    ‖A * B‖ ≤ ‖A‖ * ‖B‖ := by
  refine (Matrix.norm_le_iff (by positivity)).mpr fun i j => ?_
  rw [mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A) (Matrix.norm_entry_le_entrywise_sup_norm B)
    (norm_nonneg _) (norm_nonneg _)

/-- **Continuity of multiplication on $L(V)$** (O'Meara 1973, §101A, p. 287): $(\sigma, \tau) \mapsto \sigma\tau$. -/
@[kb "omeara1963" "§101A, p. 287 (continuity of (σ, τ) ↦ στ)"]
theorem continuous_mul_mat :
    Continuous fun p : Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K => p.1 * p.2 :=
  continuous_fst.matrix_mul continuous_snd

/-- **Continuity of finite sums of maps** (O'Meara 1973, §101A, p. 287): $(\sigma_0,\dots,\sigma_{m-1}) \mapsto
\sum_i \sigma_i$. -/
@[kb "omeara1963" "§101A, p. 287 (continuity of (σ₁, …, σ_m) ↦ σ₁ + ⋯ + σ_m)"]
theorem continuous_sum_mat (m : ℕ) :
    Continuous fun f : Fin m → Matrix (Fin n) (Fin n) K => ∑ i, f i :=
  continuous_finsetSum _ fun i _ => continuous_apply i

/-- **Continuity of finite products of maps** (O'Meara 1973, §101A, p. 287): $(\sigma_0,\dots,\sigma_{m-1})
\mapsto \sigma_0\sigma_1\cdots\sigma_{m-1}$, the product taken in this order (matrices do not commute), as
`List.prod (List.ofFn f)`. -/
@[kb "omeara1963" "§101A, p. 287 (continuity of (σ₁, …, σ_m) ↦ σ₁ ⋯ σ_m)"]
theorem continuous_prod_mat (m : ℕ) :
    Continuous fun f : Fin m → Matrix (Fin n) (Fin n) K => (List.ofFn f).prod := by
  induction m with
  | zero => simpa using continuous_const
  | succ m ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact (continuous_apply 0).matrix_mul (ih.comp (continuous_pi fun i => continuous_apply i.succ))

/-- **Continuity of $(\sigma, x) \mapsto \sigma x$** $L(V) \times V \to V$ (O'Meara 1973, §101A, p. 287). -/
@[kb "omeara1963" "§101A, p. 287 (continuity of (σ, x) ↦ σx)"]
theorem continuous_mulVec_pair :
    Continuous fun p : Matrix (Fin n) (Fin n) K × (Fin n → K) => p.1 *ᵥ p.2 :=
  continuous_fst.matrix_mulVec continuous_snd

/-- **Continuity of the determinant** $L(V) \to K$ (O'Meara 1973, §101A, p. 287). -/
@[kb "omeara1963" "§101A, p. 287 (continuity of σ ↦ det σ)"]
theorem continuous_det_mat : Continuous fun σ : Matrix (Fin n) (Fin n) K => σ.det :=
  continuous_id.matrix_det

/-- **$\mathrm{GL}(V)$ is open in $L(V)$** (O'Meara 1973, §101A, p. 287): $\{\sigma : \det\sigma \text{ is a unit}\}$
(equivalently $\det\sigma \ne 0$) is an open set. -/
@[kb "omeara1963" "§101A, p. 287 (GL(V) is open in L(V))"]
theorem isOpen_isUnit_det : IsOpen {σ : Matrix (Fin n) (Fin n) K | IsUnit σ.det} := by
  have : {σ : Matrix (Fin n) (Fin n) K | IsUnit σ.det} = (fun σ => σ.det) ⁻¹' {0}ᶜ := by
    ext σ; simp [isUnit_iff_ne_zero]
  rw [this]
  exact isOpen_compl_singleton.preimage continuous_det_mat

/-- **Continuity of inversion on $\mathrm{GL}(V)$** (O'Meara 1973, §101A, p. 287): $\sigma \mapsto \sigma^{-1}$ is
continuous on the open set $\{\sigma : \det\sigma \text{ is a unit}\}$. -/
@[kb "omeara1963" "§101A, p. 287 (continuity of σ ↦ σ⁻¹ on GL(V))"]
theorem continuousOn_inv_isUnit_det :
    ContinuousOn (fun σ : Matrix (Fin n) (Fin n) K => σ⁻¹) {σ | IsUnit σ.det} := by
  intro σ hσ
  have hne : σ.det ≠ 0 := isUnit_iff_ne_zero.mp hσ
  refine (continuousAt_matrix_inv σ ?_).continuousWithinAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ hne

/-! ### Example 101:1: change of base (general case) -/

/-- **Example 101:1, vectors, first inequality** (O'Meara 1973, §101A, pp. 287–288, general case). The new base is
the columns of $P \in \mathrm{GL}_n(K)$, so the new coordinates of $x$ are $P^{-1}x$ and
$\lVert x\rVert' = \lVert P^{-1}x\rVert$. Then $\lVert x\rVert \le n\,\lVert P\rVert\,\lVert x\rVert'$. (O'Meara:
$\lVert x\rVert/(n\lVert a_{ij}\rVert)\le\lVert x\rVert'$, with $P^{\mathsf T} = (a_{ij})$; transposition does not
change the entrywise norm. *The constant is reconstructed from the argument.*) -/
@[kb "omeara1963" "§101A, 101:1, pp. 287–288 (change of base, general; constant reconstructed)"]
theorem norm_le_mul_norm_inv_mulVec (P : GL (Fin n) K) (x : Fin n → K) :
    ‖x‖ ≤ n * ‖P.val‖ * ‖(P⁻¹).val *ᵥ x‖ := by
  conv_lhs => rw [← mulVec_inv_mulVec P x]
  exact norm_mulVec_le _ _

/-- **Example 101:1, vectors, second inequality** (O'Meara 1973, pp. 287–288, general case):
$\lVert x\rVert' = \lVert P^{-1}x\rVert \le n\,\lVert P^{-1}\rVert\,\lVert x\rVert$ (O'Meara:
$\lVert x\rVert'\le n\lVert b_{ij}\rVert\lVert x\rVert$; constant reconstructed). -/
@[kb "omeara1963" "§101A, 101:1, pp. 287–288 (change of base, general; constant reconstructed)"]
theorem norm_inv_mulVec_le_mul_norm (P : GL (Fin n) K) (x : Fin n → K) :
    ‖(P⁻¹).val *ᵥ x‖ ≤ n * ‖(P⁻¹).val‖ * ‖x‖ :=
  norm_mulVec_le _ _

/-- **Example 101:1, maps, upper bound** (O'Meara 1973, pp. 287–288, general case): the matrix of $\sigma$ in the new
base is $P^{-1}\sigma P$, and $\lVert\sigma\rVert' = \lVert P^{-1}\sigma P\rVert \le n^2\,\lVert P^{-1}\rVert\,
\lVert P\rVert\,\lVert\sigma\rVert$ (constant $n^2$ reconstructed from two matrix products). -/
@[kb "omeara1963" "§101A, 101:1, pp. 287–288 (change of base for ‖σ‖, general; constant reconstructed)"]
theorem norm_conj_le (P : GL (Fin n) K) (A : Matrix (Fin n) (Fin n) K) :
    ‖(P⁻¹).val * A * P.val‖ ≤ n ^ 2 * ‖(P⁻¹).val‖ * ‖P.val‖ * ‖A‖ := by
  calc ‖(P⁻¹).val * A * P.val‖ ≤ n * ‖(P⁻¹).val * A‖ * ‖P.val‖ := norm_mul_le _ _
    _ ≤ n * (n * ‖(P⁻¹).val‖ * ‖A‖) * ‖P.val‖ := by gcongr; exact norm_mul_le _ _
    _ = n ^ 2 * ‖(P⁻¹).val‖ * ‖P.val‖ * ‖A‖ := by ring

/-- **Example 101:1, maps, lower bound** (O'Meara 1973, pp. 287–288, general case):
$\lVert\sigma\rVert \le n^2\,\lVert P\rVert\,\lVert P^{-1}\rVert\,\lVert\sigma\rVert'$, where
$\lVert\sigma\rVert' = \lVert P^{-1}\sigma P\rVert$ (constant reconstructed). -/
@[kb "omeara1963" "§101A, 101:1, pp. 287–288 (change of base for ‖σ‖, general; constant reconstructed)"]
theorem norm_le_conj (P : GL (Fin n) K) (A : Matrix (Fin n) (Fin n) K) :
    ‖A‖ ≤ n ^ 2 * ‖P.val‖ * ‖(P⁻¹).val‖ * ‖(P⁻¹).val * A * P.val‖ := by
  have e : A = P.val * ((P⁻¹).val * A * P.val) * (P⁻¹).val := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  conv_lhs => rw [e]
  calc ‖P.val * ((P⁻¹).val * A * P.val) * (P⁻¹).val‖
      ≤ n * ‖P.val * ((P⁻¹).val * A * P.val)‖ * ‖(P⁻¹).val‖ := norm_mul_le _ _
    _ ≤ n * (n * ‖P.val‖ * ‖(P⁻¹).val * A * P.val‖) * ‖(P⁻¹).val‖ := by gcongr; exact norm_mul_le _ _
    _ = n ^ 2 * ‖P.val‖ * ‖(P⁻¹).val‖ * ‖(P⁻¹).val * A * P.val‖ := by ring

/-! ### Bilinear and quadratic forms: continuity -/

theorem coeff_map_self (Q : QuadForm K n) : Q.coeff.map (algebraMap K K) = Q.coeff := by
  ext i j; simp

/-- **O'Meara's bilinear form** $B(x, y) = \tfrac12\,x^{\mathsf T} H y$ of a quadratic form $Q$ over $K$, where
$H$ = `Q.hessian` is the Hessian (so $B(x,x) = Q(x)$ when $2 \ne 0$ in $K$, see `omearaBil_self`). -/
def omearaBil (Q : QuadForm K n) (x y : Fin n → K) : K := (2 : K)⁻¹ * (x ⬝ᵥ (Q.hessian *ᵥ y))

/-- $B(x,x) = Q(x)$ when $2 \ne 0$ in $K$. -/
theorem omearaBil_self (Q : QuadForm K n) (h2 : (2 : K) ≠ 0) (x : Fin n → K) :
    omearaBil Q x x = Q.evalIn K x := by
  have hT : x ⬝ᵥ Q.coeffᵀ *ᵥ x = x ⬝ᵥ Q.coeff *ᵥ x := by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  rw [omearaBil, QuadForm.evalIn_eq_dotProduct, QuadForm.hessian, add_mulVec, dotProduct_add, hT,
    coeff_map_self]
  field_simp
  ring

/-- **The bilinear form is bounded** (O'Meara 1973, §101A, p. 288): there is $A > 0$ with
$\lvert B(x,y)\rvert \le A\lVert x\rVert\lVert y\rVert$ for all $x, y \in V$. (O'Meara assumes $V$ regular; the
bound holds for every quadratic form $Q$, with $B$ as in `omearaBil`, and without any hypothesis on the
characteristic: if $2 = 0$ then $B = 0$ since $2^{-1} = 0$ in Lean.) -/
@[kb "omeara1963" "§101A, p. 288 (|B(x, y)| ≤ A‖x‖‖y‖)"]
theorem exists_norm_omearaBil_le (Q : QuadForm K n) :
    ∃ A : ℝ, 0 < A ∧ ∀ x y : Fin n → K, ‖omearaBil Q x y‖ ≤ A * ‖x‖ * ‖y‖ := by
  refine ⟨‖(2 : K)⁻¹‖ * n ^ 2 * ‖Q.hessian‖ + 1, by positivity, fun x y => ?_⟩
  have h1 := norm_dotProduct_le x (Q.hessian *ᵥ y)
  have h2 := norm_mulVec_le Q.hessian y
  rw [omearaBil, norm_mul]
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc ‖(2 : K)⁻¹‖ * ‖x ⬝ᵥ (Q.hessian *ᵥ y)‖
      ≤ ‖(2 : K)⁻¹‖ * (n * ‖x‖ * (n * ‖Q.hessian‖ * ‖y‖)) := by
        gcongr
        exact h1.trans (by gcongr)
    _ = (‖(2 : K)⁻¹‖ * n ^ 2 * ‖Q.hessian‖) * ‖x‖ * ‖y‖ := by ring
    _ ≤ (‖(2 : K)⁻¹‖ * n ^ 2 * ‖Q.hessian‖ + 1) * ‖x‖ * ‖y‖ := by
        have := mul_nonneg hx hy
        nlinarith

/-- **The quadratic form is bounded** (O'Meara 1973, §101A, p. 288), general case: there is $A > 0$ with
$\lvert Q(x)\rvert \le A\lVert x\rVert^2$ for all $x \in V$ (here $Q(x)$ is `Q.evalIn K x`; no regularity
needed). -/
@[kb "omeara1963" "§101A, p. 288 (|Q(x)| ≤ A‖x‖²)"]
theorem exists_norm_evalIn_le (Q : QuadForm K n) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : Fin n → K, ‖Q.evalIn K x‖ ≤ A * ‖x‖ ^ 2 := by
  refine ⟨n ^ 2 * ‖Q.coeff‖ + 1, by positivity, fun x => ?_⟩
  have h1 := norm_dotProduct_le x (Q.coeff *ᵥ x)
  have h2 := norm_mulVec_le Q.coeff x
  have hx := norm_nonneg x
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [QuadForm.evalIn_eq_dotProduct, coeff_map_self]
  calc ‖x ⬝ᵥ (Q.coeff *ᵥ x)‖ ≤ n * ‖x‖ * (n * ‖Q.coeff‖ * ‖x‖) := h1.trans (by gcongr)
    _ = (n ^ 2 * ‖Q.coeff‖) * ‖x‖ ^ 2 := by ring
    _ ≤ (n ^ 2 * ‖Q.coeff‖ + 1) * ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]

/-- **Continuity of the bilinear form** $V \times V \to K$ (O'Meara 1973, §101A, p. 288). -/
@[kb "omeara1963" "§101A, p. 288 (continuity of (x, y) ↦ B(x, y))"]
theorem continuous_omearaBil (Q : QuadForm K n) :
    Continuous fun p : (Fin n → K) × (Fin n → K) => omearaBil Q p.1 p.2 :=
  continuous_const.mul (continuous_fst.dotProduct (continuous_const.matrix_mulVec continuous_snd))

/-- **Continuity of the quadratic form** $V \to K$ (O'Meara 1973, §101A, p. 288), general case. -/
@[kb "omeara1963" "§101A, p. 288 (continuity of x ↦ Q(x))"]
theorem continuous_quadForm_evalIn (Q : QuadForm K n) : Continuous fun x : Fin n → K => Q.evalIn K x := by
  have : (fun x : Fin n → K => Q.evalIn K x) = fun x => x ⬝ᵥ (Q.coeff *ᵥ x) := by
    funext x
    rw [QuadForm.evalIn_eq_dotProduct]
    rw [coeff_map_self]
  rw [this]
  exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)

/-- **The anisotropic vectors form an open set** (O'Meara 1973, §101A, Example 101:2, p. 288): in $V = K^n$ the set
$\{x : Q(x) \ne 0\}$ is open (from the continuity of $Q$). -/
@[kb "omeara1963" "§101A, 101:2, p. 288 (anisotropic vectors form an open set)"]
theorem isOpen_anisotropic (Q : QuadForm K n) : IsOpen {x : Fin n → K | Q.evalIn K x ≠ 0} :=
  isOpen_compl_singleton.preimage (continuous_quadForm_evalIn Q)

end Matrices

/-! ### Example 101:4 (i): determinants of isometries over a completion -/

open NumberField IsDedekindDomain in
/-- **Example 101:4 (i), determinant part** (O'Meara 1973, §101A, p. 288): for a nondegenerate quadratic form $Q$ over
a number field $F$ and a finite place $\mathfrak p$, every isometry $\sigma \in O(V_\mathfrak p)$
(`orthGroup Q F_𝔭`) has $\det\sigma = \pm 1$, hence $\lvert\det\sigma\rvert_\mathfrak p = 1$
(`Valued.v (det σ) = 1`, i.e. $\det\sigma$ is a unit). -/
@[kb "omeara1963" "§101A, 101:4 (i), p. 288 (det σ = ±1, |det σ| = 1)"]
theorem det_orthGroup_eq_one_or_neg_one_and_valued {F : Type} [Field F] [NumberField F]
    (Q : QuadForm F n) (hQ : Q.Nondegenerate) (v : HeightOneSpectrum (𝓞 F))
    (σ : orthGroup Q (v.adicCompletion F)) :
    ((σ : GL (Fin n) (v.adicCompletion F)).val.det = 1 ∨
        (σ : GL (Fin n) (v.adicCompletion F)).val.det = -1) ∧
      Valued.v (σ : GL (Fin n) (v.adicCompletion F)).val.det = 1 := by
  have h := Tamagawa.det_eq_one_or_neg_one Q hQ σ
  exact ⟨h, by rcases h with h | h <;> simp [h]⟩

end QuadFormsKB.Lattices.Valuated
