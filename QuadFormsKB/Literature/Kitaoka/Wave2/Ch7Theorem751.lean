import Mathlib.Analysis.MeanInequalities
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.RingTheory.PrincipalIdealDomain
import QuadFormsKB.Literature.Kitaoka.Ch7ScalarExtension
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch7Theorem711

open Matrix NumberField

noncomputable section

namespace QuadFormsKB.Kitaoka.EType

section TraceForm

variable (K : Type) [Field K] [NumberField K]

/-- For a totally real field every complex embedding takes real values. -/
theorem embed_conj [IsTotallyReal K] (σ : K →ₐ[ℚ] ℂ) (x : K) : starRingEnd ℂ (σ x) = σ x := by
  have h := ComplexEmbedding.isReal_iff.mp (IsTotallyReal.complexEmbedding_isReal σ.toRingHom)
  exact congrArg (fun f => f x) h

theorem embed_eq_re [IsTotallyReal K] (σ : K →ₐ[ℚ] ℂ) (x : K) : ((σ x).re : ℂ) = σ x :=
  Complex.conj_eq_iff_re.mp (embed_conj K σ x)

/-- $\operatorname{tr}_{K/\mathbb Q}(x^2) = \sum_\sigma \sigma(x)^2$, a sum of real squares. -/
theorem trace_mul_self_eq [IsTotallyReal K] (x : K) :
    ((Algebra.trace ℚ K (x * x) : ℚ) : ℝ) = ∑ σ : K →ₐ[ℚ] ℂ, ((σ x).re) ^ 2 := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := x * x)
  apply Complex.ofReal_injective
  have h2 : ∀ σ : K →ₐ[ℚ] ℂ, σ (x * x) = (((σ x).re ^ 2 : ℝ) : ℂ) := by
    intro σ
    rw [map_mul]
    have := embed_eq_re K σ x
    push_cast
    rw [this]
    ring
  simp_rw [h2] at h
  rw [Complex.ofReal_sum]
  rw [← h]
  simp

theorem sigma_re_ne_zero [IsTotallyReal K] (σ : K →ₐ[ℚ] ℂ) {x : K} (hx : x ≠ 0) : (σ x).re ≠ 0 := by
  intro h
  apply hx
  have := embed_eq_re K σ x
  rw [h] at this
  simp only [Complex.ofReal_zero] at this
  exact (map_eq_zero σ).mp this.symm

theorem nonempty_embeddings : Nonempty (K →ₐ[ℚ] ℂ) := by
  rw [← Fintype.card_pos_iff, AlgHom.card ℚ K ℂ]
  exact Module.finrank_pos

/-- $\operatorname{tr}_{K/\mathbb Q}(x^2) > 0$ for $x \ne 0$ in a totally real field. -/
theorem trace_mul_self_pos [IsTotallyReal K] {x : K} (hx : x ≠ 0) : 0 < Algebra.trace ℚ K (x * x) := by
  have h := trace_mul_self_eq K x
  obtain ⟨σ⟩ := nonempty_embeddings K
  have : (0 : ℝ) < ((Algebra.trace ℚ K (x * x) : ℚ) : ℝ) := by
    rw [h]
    have := sigma_re_ne_zero K σ hx
    exact Finset.sum_pos' (fun τ _ => sq_nonneg _) ⟨σ, Finset.mem_univ _, by positivity⟩
  exact_mod_cast this

/-- **AM–GM for the trace form** (Kitaoka 1993, Lemma 7.5.5, p. 241): for $0 \ne w \in R_K$, $K$ totally real,
$\operatorname{tr}_{K/\mathbb Q}(w^2) \ge [K : \mathbb Q]$, with equality only for $w^2 = 1$. -/
theorem amgm_trace [IsTotallyReal K] (w : 𝓞 K) (hw : w ≠ 0) :
    (Module.finrank ℚ K : ℚ) ≤ Algebra.trace ℚ K ((w : K) * w) ∧
      (Algebra.trace ℚ K ((w : K) * w) = Module.finrank ℚ K → (w : K) * w = 1) := by
  classical
  set r := Module.finrank ℚ K with hr
  have hrpos : 0 < r := Module.finrank_pos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hrpos
  have hcard : Fintype.card (K →ₐ[ℚ] ℂ) = r := AlgHom.card ℚ K ℂ
  have hx : (w : K) ≠ 0 := by exact_mod_cast hw
  set s : (K →ₐ[ℚ] ℂ) → ℝ := fun σ => ((σ (w : K)).re) ^ 2 with hs
  have hspos : ∀ σ, 0 < s σ := fun σ => by
    have := sigma_re_ne_zero K σ hx
    simp only [hs]; positivity
  have hsum : ((Algebra.trace ℚ K ((w : K) * w) : ℚ) : ℝ) = ∑ σ, s σ := trace_mul_self_eq K _
  have hprod : (1 : ℝ) ≤ ∏ σ, s σ := by
    have hN := Algebra.norm_eq_prod_embeddings ℚ ℂ (w : K)
    have hN2 : ((Algebra.norm ℚ (w : K) : ℚ) : ℝ) = ∏ σ : K →ₐ[ℚ] ℂ, (σ (w : K)).re := by
      apply Complex.ofReal_injective
      rw [Complex.ofReal_prod]
      simp_rw [embed_eq_re K _ _]
      rw [← hN]; simp
    obtain ⟨m, hm0, hm⟩ : ∃ m : ℤ, m ≠ 0 ∧ (m : ℝ) = ∏ σ : K →ₐ[ℚ] ℂ, (σ (w : K)).re := by
      refine ⟨Algebra.norm ℤ w, Algebra.norm_ne_zero_iff.mpr hw, ?_⟩
      rw [← hN2, ← Algebra.coe_norm_int]; simp
    have h1 : (∏ σ, s σ) = (m : ℝ) ^ 2 := by
      rw [hm]; simp only [hs]; rw [Finset.prod_pow]
    rw [h1]
    have : (1 : ℤ) ≤ m ^ 2 := by nlinarith [sq_pos_of_ne_zero hm0]
    exact_mod_cast this
  have hw2 : ∑ σ ∈ (Finset.univ : Finset (K →ₐ[ℚ] ℂ)), (fun _ : K →ₐ[ℚ] ℂ => (1 : ℝ) / r) σ = 1 := by
    simp [Finset.sum_const, hcard]; field_simp
  have hGM : (∏ σ, s σ ^ ((1 : ℝ) / r)) = (∏ σ, s σ) ^ ((1 : ℝ) / r) :=
    Real.finsetProd_rpow _ _ (fun σ _ => (hspos σ).le) _
  have hone : (1 : ℝ) ≤ (∏ σ, s σ) ^ ((1 : ℝ) / r) := Real.one_le_rpow hprod (by positivity)
  have hAM : ∑ σ, (1 : ℝ) / r * s σ = ((Algebra.trace ℚ K ((w : K) * w) : ℚ) : ℝ) / r := by
    rw [← Finset.mul_sum, hsum]; ring
  have hle := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => (1 : ℝ) / r) s
    (fun _ _ => by positivity) hw2 (fun σ _ => (hspos σ).le)
  rw [hGM, hAM] at hle
  constructor
  · have h1 : (1 : ℝ) ≤ ((Algebra.trace ℚ K ((w : K) * w) : ℚ) : ℝ) / r := hone.trans hle
    rw [le_div_iff₀ hrR] at h1
    exact_mod_cast (by linarith : (r : ℝ) ≤ ((Algebra.trace ℚ K ((w : K) * w) : ℚ) : ℝ))
  · intro htr
    have htrR : ((Algebra.trace ℚ K ((w : K) * w) : ℚ) : ℝ) = r := by exact_mod_cast htr
    have hAM1 : ∑ σ, (1 : ℝ) / r * s σ = 1 := by rw [hAM, htrR]; field_simp
    have heq : ∏ σ, s σ ^ ((1 : ℝ) / r) = ∑ σ, (1 : ℝ) / r * s σ := by
      rw [hGM, hAM1]
      apply le_antisymm _ hone
      rw [htrR, div_self hrR.ne'] at hle
      exact hle
    have hall := (Real.geom_mean_eq_arith_mean_weighted_iff_of_pos' Finset.univ
      (fun _ : K →ₐ[ℚ] ℂ => (1 : ℝ) / r) s (fun _ _ => by positivity) hw2
      (fun σ _ => (hspos σ).le)).mp heq
    obtain ⟨σ⟩ := nonempty_embeddings K
    have h1 : s σ = 1 := by rw [hall σ (Finset.mem_univ _)]; exact hAM1
    have := embed_eq_re K σ (w : K)
    simp only [hs] at h1
    refine σ.injective ?_
    have h2 : σ ((w : K) * w) = σ 1 := by
      rw [map_mul, map_one, ← this]
      norm_cast
      nlinarith [h1]
    exact h2

end TraceForm

/-! ### Auxiliary facts on minimal vectors and minimal tensors

Local copies (for `Fin`-indexed lattices) of the basic facts of `Wave2/Ch7Lemma711.lean`, so that this file does not
depend on that module. They live in the namespace `Aux751`. -/

namespace Aux751

/-- $Q(x) > 0$ for nonzero integer vectors of a positive lattice. -/
theorem gramQ_pos {ι : Type*} [Fintype ι] {A : Matrix ι ι ℚ} (hA : IsPosGram A) {z : ι → ℤ} (hz : z ≠ 0) :
    0 < gramQ A z := by
  refine hA.2 _ ?_
  intro h
  apply hz
  ext i
  have := congrFun h i
  simpa using this

/-- The Kronecker product of positive Gram matrices is a positive Gram matrix (the Gram matrix of $L \otimes M$). -/
theorem isPosGram_kronecker {n m : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {B : Matrix (Fin m) (Fin m) ℚ}
    (hA : IsPosGram A) (hB : IsPosGram B) : IsPosGram (Matrix.kroneckerMap (· * ·) A B) := by
  classical
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 : Aᵀ = A := hA.1
    have h2 : Bᵀ = B := hB.1
    have e := Matrix.kroneckerMap_transpose (· * ·) A B
    show (Matrix.kroneckerMap (· * ·) A B)ᵀ = _
    rw [← e, h1, h2]
  · have hP := (posDef_ratCast _ hA).kronecker (posDef_ratCast _ hB)
    have hmap : (Matrix.kroneckerMap (· * ·) A B).map (Rat.cast : ℚ → ℝ) =
        Matrix.kroneckerMap (· * ·) (A.map (Rat.cast : ℚ → ℝ)) (B.map (Rat.cast : ℚ → ℝ)) := by
      ext ⟨i, j⟩ ⟨k, l⟩
      simp [Matrix.kroneckerMap_apply]
    have hxr : (fun p => (x p : ℝ)) ≠ 0 := fun h => hx (by
      ext p; have := congrFun h p; simpa using this)
    have := hP.dotProduct_mulVec_pos hxr
    rw [← hmap] at this
    simp only [star_trivial] at this
    have h2 : ((fun p => (x p : ℝ)) ⬝ᵥ ((Matrix.kroneckerMap (· * ·) A B).map (Rat.cast : ℚ → ℝ) *ᵥ
        fun p => (x p : ℝ))) = ((x ⬝ᵥ (Matrix.kroneckerMap (· * ·) A B *ᵥ x) : ℚ) : ℝ) := by
      simp [dotProduct, mulVec]
    rw [h2] at this
    exact_mod_cast this

/-- The vectorisation of an integer matrix. -/
def vecT {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℤ) : Fin n × Fin m → ℤ := fun p => X p.1 p.2

theorem vecT_ne_zero_iff {n m : ℕ} {X : Matrix (Fin n) (Fin m) ℤ} : vecT X ≠ 0 ↔ X ≠ 0 := by
  constructor
  · intro h hX; apply h; ext p; simp [vecT, hX]
  · intro h hX; apply h; ext i j; exact congrFun hX (i, j)

/-- $Q_{A \otimes B}(X) = Q_{A \boxtimes B}(\operatorname{vec} X)$ with $A \boxtimes B$ the Kronecker product. -/
theorem tensorQ_eq_gramQ_kron {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin m) (Fin m) ℚ)
    (X : Matrix (Fin n) (Fin m) ℤ) :
    tensorQ A B X = gramQ (Matrix.kroneckerMap (· * ·) A B) (vecT X) := by
  rw [gramQ_eq_sum]
  simp only [tensorQ, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, vecT]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => by ring

theorem tensorQ_pos {n m : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {B : Matrix (Fin m) (Fin m) ℚ} (hA : IsPosGram A)
    (hB : IsPosGram B) {X : Matrix (Fin n) (Fin m) ℤ} (hX : X ≠ 0) : 0 < tensorQ A B X := by
  rw [tensorQ_eq_gramQ_kron]
  exact gramQ_pos (isPosGram_kronecker hA hB) (vecT_ne_zero_iff.2 hX)

theorem isMinimalTensor_iff {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin m) (Fin m) ℚ)
    (X : Matrix (Fin n) (Fin m) ℤ) :
    IsMinimalTensor A B X ↔ IsMinimalVector (Matrix.kroneckerMap (· * ·) A B) (vecT X) := by
  constructor
  · rintro ⟨h0, hmin⟩
    refine ⟨vecT_ne_zero_iff.2 h0, fun y hy => ?_⟩
    have := hmin (Matrix.of fun i j => y (i, j)) (fun h => hy (by
      ext ⟨i, j⟩; exact congrFun (congrFun h i) j))
    rw [tensorQ_eq_gramQ_kron, tensorQ_eq_gramQ_kron] at this
    exact this
  · rintro ⟨h0, hmin⟩
    refine ⟨vecT_ne_zero_iff.1 h0, fun Y hY => ?_⟩
    rw [tensorQ_eq_gramQ_kron, tensorQ_eq_gramQ_kron]
    exact hmin _ (vecT_ne_zero_iff.2 hY)

/-- A common denominator for finitely many rationals. -/
theorem exists_den {α : Type*} [Fintype α] (f : α → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ a, ∃ z : ℤ, (D : ℚ) * f a = z := by
  classical
  refine ⟨∏ a, (f a).den, Finset.prod_pos fun a _ => (f a).den_pos, fun a => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun a => (f a).den) (Finset.mem_univ a)
  refine ⟨c * (f a).num, ?_⟩
  rw [hc]
  push_cast
  have := Rat.mul_den_eq_num (f a)
  calc ((f a).den : ℚ) * c * f a = c * (f a * (f a).den) := by ring
    _ = _ := by rw [this]

/-- A function with values in $\frac1D \mathbb Z$, positive on a nonempty set $S$, attains its minimum on $S$. -/
theorem exists_min_of_den {α : Type*} (q : α → ℚ) (D : ℕ) (hD : 0 < D)
    (hint : ∀ a, ∃ z : ℤ, (D : ℚ) * q a = z) (S : Set α) (hpos : ∀ a ∈ S, 0 < q a) (a0 : α) (ha0 : a0 ∈ S) :
    ∃ a ∈ S, ∀ b ∈ S, q a ≤ q b := by
  classical
  choose zf hzf using hint
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hzpos : ∀ a ∈ S, 0 < zf a := by
    intro a ha
    have h1 := hpos a ha
    have h2 : (0 : ℚ) < zf a := by rw [← hzf a]; positivity
    exact_mod_cast h2
  have hex : ∃ n : ℕ, ∃ a ∈ S, (n : ℤ) = zf a :=
    ⟨(zf a0).toNat, a0, ha0, Int.toNat_of_nonneg (hzpos a0 ha0).le⟩
  obtain ⟨a1, ha1, hn1⟩ := Nat.find_spec hex
  refine ⟨a1, ha1, fun b hb => ?_⟩
  have hle : Nat.find hex ≤ (zf b).toNat :=
    Nat.find_min' hex ⟨b, hb, Int.toNat_of_nonneg (hzpos b hb).le⟩
  have hle' : zf a1 ≤ zf b := by
    rw [← hn1]
    have := Int.toNat_of_nonneg (hzpos b hb).le
    omega
  have : (D : ℚ) * q a1 ≤ D * q b := by
    rw [hzf, hzf]; exact_mod_cast hle'
  exact le_of_mul_le_mul_left this hDq

theorem exists_den_gramQ {ι : Type*} [Fintype ι] (A : Matrix ι ι ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ z : ι → ℤ, ∃ k : ℤ, (D : ℚ) * gramQ A z = k := by
  obtain ⟨D, hD, h⟩ := exists_den (fun p : ι × ι => A p.1 p.2)
  choose zs hzs using h
  refine ⟨D, hD, fun z => ⟨∑ i, ∑ k, z i * z k * zs (i, k), ?_⟩⟩
  rw [gramQ_eq_sum]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h' : (zs (i, k) : ℚ) = D * A i k := (hzs (i, k)).symm
  rw [h']
  ring

/-- A positive lattice with a nonzero vector has a minimal vector. -/
theorem exists_isMinimalVector {ι : Type*} [Fintype ι] {A : Matrix ι ι ℚ} (hA : IsPosGram A) {z0 : ι → ℤ}
    (hz0 : z0 ≠ 0) : ∃ x, IsMinimalVector A x := by
  obtain ⟨D, hD, h⟩ := exists_den_gramQ A
  obtain ⟨a, ha, hmin⟩ :=
    exists_min_of_den (gramQ A) D hD h {z | z ≠ 0} (fun z hz => gramQ_pos hA hz) z0 hz0
  exact ⟨a, ha, fun y hy => hmin y hy⟩

/-- $L \otimes M$ has a minimal vector as soon as it has a nonzero vector. -/
theorem exists_isMinimalTensor {n m : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {B : Matrix (Fin m) (Fin m) ℚ}
    (hA : IsPosGram A) (hB : IsPosGram B) {X0 : Matrix (Fin n) (Fin m) ℤ} (hX0 : X0 ≠ 0) :
    ∃ X, IsMinimalTensor A B X := by
  obtain ⟨x, hx⟩ := exists_isMinimalVector (isPosGram_kronecker hA hB) (vecT_ne_zero_iff.2 hX0)
  refine ⟨Matrix.of fun i j => x (i, j), (isMinimalTensor_iff A B _).2 ?_⟩
  have : vecT (Matrix.of fun i j => x (i, j) : Matrix (Fin n) (Fin m) ℤ) = x := by
    funext ⟨i, j⟩; rfl
  rw [this]; exact hx

/-- The components of a minimal split tensor are minimal vectors. -/
theorem isMinimalVector_of_split {n m : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {B : Matrix (Fin m) (Fin m) ℚ}
    (hA : IsPosGram A) (hB : IsPosGram B) {x : Fin n → ℤ} {y : Fin m → ℤ}
    (h : IsMinimalTensor A B (vecMulVec x y)) : IsMinimalVector A x ∧ IsMinimalVector B y := by
  have hx : x ≠ 0 := by
    intro h0; apply h.1; ext i j; simp [vecMulVec_apply, h0]
  have hy : y ≠ 0 := by
    intro h0; apply h.1; ext i j; simp [vecMulVec_apply, h0]
  have hxp := gramQ_pos hA hx
  have hyp := gramQ_pos hB hy
  refine ⟨⟨hx, fun a ha => ?_⟩, ⟨hy, fun b hb => ?_⟩⟩
  · have := h.2 _ (vecMulVec_ne_zero ha hy)
    rw [tensorQ_vecMulVec, tensorQ_vecMulVec] at this
    exact le_of_mul_le_mul_right this hyp
  · have := h.2 _ (vecMulVec_ne_zero hx hb)
    rw [tensorQ_vecMulVec, tensorQ_vecMulVec] at this
    exact le_of_mul_le_mul_left this hxp

theorem gramQ_eq_of_minimal {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {x x' : Fin n → ℤ}
    (hx : IsMinimalVector A x) (hx' : IsMinimalVector A x') : gramQ A x = gramQ A x' :=
  le_antisymm (hx.2 _ hx'.1) (hx'.2 _ hx.1)

theorem gramQ_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (g : ℤ) (z : Fin n → ℤ) :
    gramQ A (fun i => g * z i) = (g : ℚ) ^ 2 * gramQ A z := by
  rw [gramQ_eq_sum, gramQ_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast; ring

/-- A minimal vector is primitive: some integer combination of its entries is $1$ (otherwise $y = g y'$ with
$|g| \ge 2$ and $Q(y') < Q(y)$). -/
theorem exists_dual_of_minimal {n : ℕ} {N : Matrix (Fin n) (Fin n) ℚ} (hN : IsPosGram N) {y : Fin n → ℤ}
    (hy : IsMinimalVector N y) : ∃ c : Fin n → ℤ, c ⬝ᵥ y = 1 := by
  classical
  obtain ⟨g, hg⟩ := Submodule.IsPrincipal.principal (Ideal.span (Set.range y))
  have hdvd : ∀ j, g ∣ y j := fun j => by
    have : y j ∈ Ideal.span (Set.range y) := Ideal.subset_span ⟨j, rfl⟩
    rw [hg] at this
    exact Ideal.mem_span_singleton.mp this
  have hgmem : g ∈ Ideal.span (Set.range y) := by
    rw [hg]; exact Submodule.mem_span_singleton_self g
  obtain ⟨c0, hc0⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hgmem
  choose z hz using hdvd
  have hg0 : g ≠ 0 := by
    intro h0; apply hy.1; funext j; rw [hz j, h0]; simp
  have hzne : z ≠ 0 := by
    intro h0; apply hy.1; funext j; rw [hz j, h0]; simp
  have hyz : y = fun j => g * z j := funext hz
  have h1 := hy.2 z hzne
  rw [hyz, gramQ_smul] at h1
  have hq := gramQ_pos hN hzne
  have hg2 : (g : ℚ) * g ≤ 1 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hg2' : g * g ≤ 1 := by exact_mod_cast hg2
  have hg3 : 0 < g * g := mul_self_pos.mpr hg0
  have hgg : g * g = 1 := by omega
  refine ⟨fun j => g * c0 j, ?_⟩
  calc (fun j => g * c0 j) ⬝ᵥ y = g * ∑ j, c0 j • y j := by
        rw [dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by simp only [smul_eq_mul]; ring
    _ = 1 := by rw [hc0, hgg]

end Aux751

/-! ### The trace form $(R_K, B_K)$ and the tensor $R_K L = (R_K, B_K) \otimes L$ -/

section TensorTrace

variable (K : Type) [Field K] [NumberField K]

/-- The rank $[K : \mathbb Q]$ of $R_K$ as a $\mathbb Z$-module. -/
abbrev rk : ℕ := Module.finrank ℤ (𝓞 K)

/-- A $\mathbb Z$-basis $(b_i)_{i < r}$ of $R_K$, indexed by `Fin r`. -/
def zb : Module.Basis (Fin (rk K)) ℤ (𝓞 K) := Module.finBasis ℤ (𝓞 K)

/-- **Gram matrix of $(R_K, B_K)$ in the basis `zb`**, $B_K(x, y) = \operatorname{tr}_{K/\mathbb Q}(xy)$, indexed by
`Fin r` (the `Fin`-indexed form of `traceGram`). -/
def Tg : Matrix (Fin (rk K)) (Fin (rk K)) ℚ :=
  Matrix.of fun i j => Algebra.trace ℚ K (((zb K i : 𝓞 K) : K) * ((zb K j : 𝓞 K) : K))

/-- The element $\sum_i z_i b_i$ of $R_K$ with coordinate vector $z \in \mathbb Z^r$. -/
def wOf (z : Fin (rk K) → ℤ) : 𝓞 K := (zb K).equivFun.symm z

theorem rk_eq : rk K = Module.finrank ℚ K := RingOfIntegers.rank K

theorem coe_wOf (z : Fin (rk K) → ℤ) :
    ((wOf K z : 𝓞 K) : K) = ∑ i, z i • ((zb K i : 𝓞 K) : K) := by
  simp [wOf, Module.Basis.equivFun_symm_apply]

theorem wOf_smul (k : ℤ) (z : Fin (rk K) → ℤ) : wOf K (k • z) = k • wOf K z :=
  map_zsmul (zb K).equivFun.symm k z

theorem wOf_ne_zero {z : Fin (rk K) → ℤ} (hz : z ≠ 0) : wOf K z ≠ 0 := by
  intro h
  apply hz
  have := congrArg (zb K).equivFun h
  rw [wOf, LinearEquiv.apply_symm_apply, map_zero] at this
  exact this

/-- **Bilinear form of $\operatorname{tr}$ in coordinates**: $\operatorname{tr}(w_z w_{z'}) = \sum_{i,l} z_i z'_l T_{il}$. -/
theorem trace_wOf_mul (z z' : Fin (rk K) → ℤ) :
    Algebra.trace ℚ K (((wOf K z : 𝓞 K) : K) * ((wOf K z' : 𝓞 K) : K)) =
      ∑ i, ∑ l, (z i : ℚ) * z' l * Tg K i l := by
  rw [coe_wOf, coe_wOf, Finset.sum_mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_mul_smul_comm, map_zsmul]
  simp [Tg]

theorem gramQ_Tg (z : Fin (rk K) → ℤ) :
    gramQ (Tg K) z = Algebra.trace ℚ K (((wOf K z : 𝓞 K) : K) * ((wOf K z : 𝓞 K) : K)) := by
  rw [trace_wOf_mul, gramQ_eq_sum]

theorem Tg_isPosGram [IsTotallyReal K] : IsPosGram (Tg K) := by
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j; simp [Tg, mul_comm]
  · obtain ⟨D, hD, z, hz⟩ := exists_clear_denoms x
    have hz0 : z ≠ 0 := by
      intro h
      apply hx
      ext i
      have := hz i
      rw [h] at this
      simp only [Pi.zero_apply, Int.cast_zero] at this
      simpa [hD] using this
    have h1 : 0 < gramQ (Tg K) z := by
      rw [gramQ_Tg]
      exact trace_mul_self_pos K (by exact_mod_cast wOf_ne_zero K hz0)
    have h2 : (fun i => (z i : ℚ)) = (D : ℚ) • x := by
      funext i; simp [← hz i]
    have h3 : gramQ (Tg K) z = (D : ℚ) * (D : ℚ) * (x ⬝ᵥ (Tg K *ᵥ x)) := by
      simp only [gramQ, h2, smul_dotProduct, dotProduct_smul, Matrix.mulVec_smul, smul_eq_mul]
      ring
    rw [h3] at h1
    have hDq : (0 : ℚ) < (D : ℚ) * D := by
      have : (D : ℚ) ≠ 0 := by exact_mod_cast hD
      exact mul_self_pos.mpr this
    exact (pos_iff_pos_of_mul_pos h1).mp hDq

theorem trace_algebraMap_rat (c : ℚ) : Algebra.trace ℚ K (algebraMap ℚ K c) = (rk K : ℚ) * c := by
  rw [Algebra.trace_algebraMap, rk_eq, nsmul_eq_mul]

/-- **Minimal vectors of $(R_K, B_K)$** (Kitaoka 1993, Lemma 7.5.5, p. 241: $\mathcal M((R_K, B_K)) = \{\pm 1\}$):
for $K$ totally real, a minimal vector $z$ of the trace form has value $[K : \mathbb Q]$ and corresponds to an element
$w \in R_K$ with $w^2 = 1$, i.e. $w = \pm 1$. -/
@[kb "kitaoka1993" "§7.5, Lemma 7.5.5, p. 241 (M((R_K, B_K)) = {±1})"]
theorem Tg_min [IsTotallyReal K] {z : Fin (rk K) → ℤ} (hz : IsMinimalVector (Tg K) z) :
    gramQ (Tg K) z = (rk K : ℚ) ∧ ((wOf K z : 𝓞 K) : K) * ((wOf K z : 𝓞 K) : K) = 1 := by
  set e : Fin (rk K) → ℤ := (zb K).equivFun 1 with he
  have hwe : wOf K e = 1 := LinearEquiv.symm_apply_apply _ _
  have he0 : e ≠ 0 := by
    intro h
    have := wOf_ne_zero K (z := e)
    rw [h] at hwe
    have h0 : wOf K (0 : Fin (rk K) → ℤ) = 0 := map_zero _
    rw [h0] at hwe
    exact zero_ne_one hwe
  have h1 : gramQ (Tg K) e = rk K := by
    rw [gramQ_Tg, hwe]
    have := trace_algebraMap_rat K 1
    simpa using this
  have hle := hz.2 e he0
  obtain ⟨hge, heq⟩ := amgm_trace K (wOf K z) (wOf_ne_zero K hz.1)
  rw [← rk_eq, ← gramQ_Tg] at hge
  have hval : gramQ (Tg K) z = (rk K : ℚ) := le_antisymm (hle.trans h1.le) hge
  refine ⟨hval, heq ?_⟩
  rw [← gramQ_Tg, hval, rk_eq]

/-- The value $B(y, y) = \sum_{j,k} B_{jk}\, y_j y_k \in K$ of $y \in R_K^n$ (the $K$-bilinear extension of $B$). -/
def formK {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (y : Fin n → 𝓞 K) : K :=
  ∑ j, ∑ k, algebraMap ℚ K (B j k) * (((y j : 𝓞 K) : K) * ((y k : 𝓞 K) : K))

/-- The coordinates of $y \in R_K^n$ in the basis `zb`, an integer $n \times r$ matrix (an element of $L \otimes R_K$). -/
def coords {n : ℕ} (y : Fin n → 𝓞 K) : Matrix (Fin n) (Fin (rk K)) ℤ :=
  Matrix.of fun j i => (zb K).equivFun (y j) i

theorem wOf_coords {n : ℕ} (y : Fin n → 𝓞 K) (j : Fin n) : wOf K (fun i => coords K y j i) = y j :=
  LinearEquiv.symm_apply_apply _ _

/-- **$R_K L = (R_K, B_K) \otimes L$** (Kitaoka 1993, §7.5, proof of Lemma 7.5.5, p. 241):
$\operatorname{tr}_{K/\mathbb Q} B(y, y) = Q_{L \otimes (R_K, B_K)}(\text{coordinates of } y)$. -/
theorem trace_formK {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (y : Fin n → 𝓞 K) :
    Algebra.trace ℚ K (formK K B y) = tensorQ B (Tg K) (coords K y) := by
  unfold formK
  rw [map_sum]
  simp_rw [map_sum]
  have key : ∀ j k, Algebra.trace ℚ K (algebraMap ℚ K (B j k) * (((y j : 𝓞 K) : K) * ((y k : 𝓞 K) : K))) =
      B j k * ∑ i, ∑ l, (coords K y j i : ℚ) * coords K y k l * Tg K i l := by
    intro j k
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
    congr 1
    rw [← trace_wOf_mul]
    rw [wOf_coords, wOf_coords]
  simp_rw [key]
  simp only [tensorQ]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc (∑ k, B j k * ∑ i, ∑ l, (coords K y j i : ℚ) * coords K y k l * Tg K i l)
      = ∑ k, ∑ i, ∑ l, (coords K y j i : ℚ) * coords K y k l * B j k * Tg K i l := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
    _ = _ := Finset.sum_comm

/-- **Splitting of minimal tensors** with the trace form: every minimal vector of $L \otimes (R_K, B_K)$ is split,
$X = x z^{\mathsf T}$. This holds if $L$ is of E-type (`splitOK_of_isEType`) or if $(R_K, B_K)$ is of E-type
(`splitOK_of_traceGram`), the two alternatives of Kitaoka's Lemma 7.5.5 and Theorem 7.5.1. -/
def SplitOK {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  ∀ X : Matrix (Fin n) (Fin (rk K)) ℤ, IsMinimalTensor B (Tg K) X → ∃ (x : Fin n → ℤ) (z : Fin (rk K) → ℤ), X = vecMulVec x z

theorem splitOK_of_isEType [IsTotallyReal K] {n : ℕ} {B : Matrix (Fin n) (Fin n) ℚ} (hE : IsEType B) : SplitOK K B :=
  fun X hX => hE _ (Tg K) (Tg_isPosGram K) X hX

/-- **Kitaoka 1993, Lemma 7.5.5** (p. 241), matrix form. Let $K$ be totally real and $L = (\mathbb Z^n, B)$ a positive
lattice with a minimal vector $x_0$ such that $L$ or $(R_K, B_K)$ is of E-type (`SplitOK`). If $0 \ne y \in R_K^n$ has rational value
$B(y, y) = c \in \mathbb Q$ then (i) $c \ge \min(L) = B[x_0]$, and (ii) if $c = \min(L)$ then $y \in L = \mathbb Z^n$
(and then $y$ is a minimal vector of $L$). *Proof* (Kitaoka's): $\operatorname{tr}\,B(y, y) = [K:\mathbb Q]\,c$ is the
value of the tensor $y \in (R_K, B_K) \otimes L$; a minimal tensor is split, $x \otimes z$, with $z \in
\mathcal M((R_K, B_K)) = \{\pm 1\}$ (`Tg_min`, AM–GM), so $\min = [K:\mathbb Q]\min(L)$, which gives (i); in case
(ii) $y$ is itself a minimal tensor, hence $y = \pm\, x'$ with $x' \in L$. -/
@[kb "kitaoka1993" "§7.5, Lemma 7.5.5, p. 241"]
theorem lemma755 [IsTotallyReal K] {n : ℕ} {B : Matrix (Fin n) (Fin n) ℚ} (hB : IsPosGram B) (hE : SplitOK K B)
    {x₀ : Fin n → ℤ} (hx₀ : IsMinimalVector B x₀) {y : Fin n → 𝓞 K} (hy : y ≠ 0) {c : ℚ}
    (hc : formK K B y = algebraMap ℚ K c) :
    gramQ B x₀ ≤ c ∧ (c = gramQ B x₀ → ∃ x : Fin n → ℤ, y = fun j => (x j : 𝓞 K)) := by
  have hT := Tg_isPosGram K
  have hrk : (0 : ℚ) < (rk K : ℚ) := by
    have : 0 < rk K := by rw [rk_eq]; exact Module.finrank_pos
    exact_mod_cast this
  have hX0 : coords K y ≠ 0 := by
    intro h
    apply hy
    funext j
    rw [← wOf_coords K y j]
    have : (fun i => coords K y j i) = 0 := by
      funext i
      have := congrFun (congrFun h j) i
      simpa using this
    rw [this]
    exact map_zero _
  have hQX : tensorQ B (Tg K) (coords K y) = (rk K : ℚ) * c := by
    rw [← trace_formK, hc, trace_algebraMap_rat]
  obtain ⟨X₀, hX₀⟩ := Aux751.exists_isMinimalTensor hB hT hX0
  obtain ⟨x, z, rfl⟩ := hE X₀ hX₀
  obtain ⟨hxm, hzm⟩ := Aux751.isMinimalVector_of_split hB hT hX₀
  have hz := Tg_min K hzm
  have hQ0 : tensorQ B (Tg K) (vecMulVec x z) = gramQ B x₀ * rk K := by
    rw [tensorQ_vecMulVec, Aux751.gramQ_eq_of_minimal hxm hx₀, hz.1]
  constructor
  · have := hX₀.2 _ hX0
    rw [hQ0, hQX] at this
    nlinarith
  · intro hcc
    have hXmin : IsMinimalTensor B (Tg K) (coords K y) := by
      refine ⟨hX0, fun Y hY => ?_⟩
      have := hX₀.2 Y hY
      rw [hQ0] at this
      rw [hQX, hcc]
      nlinarith
    obtain ⟨x', z', hxz⟩ := hE _ hXmin
    obtain ⟨_, hz'm⟩ := Aux751.isMinimalVector_of_split hB hT (hxz ▸ hXmin)
    have hz' := (Tg_min K hz'm).2
    have hw : wOf K z' * wOf K z' = 1 := by
      apply RingOfIntegers.coe_injective
      simpa using hz'
    have hy' : ∀ j, y j = x' j • wOf K z' := by
      intro j
      rw [← wOf_coords K y j, ← wOf_smul]
      congr 1
      funext i
      have := congrFun (congrFun hxz j) i
      simpa [vecMulVec_apply] using this
    rcases mul_self_eq_one_iff.mp hw with h1 | h1
    · refine ⟨x', funext fun j => ?_⟩
      rw [hy', h1]; simp
    · refine ⟨fun j => - x' j, funext fun j => ?_⟩
      rw [hy', h1]; simp

end TensorTrace

/-! ### Isometries of scalar extensions and unimodular matrices -/

section Iso

variable (K : Type) [Field K] [NumberField K]

theorem formK_eq_dot {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → 𝓞 K) :
    formK K B v = (fun j => ((v j : 𝓞 K) : K)) ⬝ᵥ
      ((B.map (algebraMap ℚ K)) *ᵥ fun j => ((v j : 𝓞 K) : K)) := by
  simp only [formK, dotProduct, mulVec, Matrix.map_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem quad_conjK {F : Type*} [CommRing F] {a b : ℕ} (C : Matrix (Fin a) (Fin b) F)
    (M : Matrix (Fin a) (Fin a) F) (v : Fin b → F) :
    v ⬝ᵥ ((Cᵀ * M * C) *ᵥ v) = (C *ᵥ v) ⬝ᵥ (M *ᵥ (C *ᵥ v)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

omit [NumberField K] in
theorem coe_mulVec {n : ℕ} (P : Matrix (Fin n) (Fin n) (𝓞 K)) (v : Fin n → 𝓞 K) :
    (fun j => (((P *ᵥ v) j : 𝓞 K) : K)) =
      (P.map (algebraMap (𝓞 K) K)) *ᵥ fun j => ((v j : 𝓞 K) : K) := by
  funext j
  simp [Matrix.mulVec, dotProduct, map_sum]

/-- **The isometry preserves the form**: if $P^{\mathsf T} B P = A$ over $K$ then $B(Pv, Pv) = A(v, v)$. -/
theorem formK_mulVec {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℚ} {P : Matrix (Fin n) (Fin n) (𝓞 K)}
    (hrel : (P.map (algebraMap (𝓞 K) K))ᵀ * B.map (algebraMap ℚ K) * P.map (algebraMap (𝓞 K) K) =
      A.map (algebraMap ℚ K)) (v : Fin n → 𝓞 K) : formK K B (P *ᵥ v) = formK K A v := by
  rw [formK_eq_dot, formK_eq_dot, coe_mulVec, ← quad_conjK, hrel]

theorem formK_cast {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℤ) :
    formK K B (fun j => (x j : 𝓞 K)) = algebraMap ℚ K (gramQ B x) := by
  rw [formK_eq_dot]
  simp [gramQ, dotProduct, mulVec, map_sum]

end Iso

section Iso2

variable (K : Type) [Field K] [NumberField K]

/-- The inverse of an isometry $R_K L \cong R_K M$ is an isometry $R_K M \cong R_K L$. -/
theorem isometry_inv {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℚ} {P : Matrix (Fin n) (Fin n) (𝓞 K)}
    (h : IsScalarExtensionIsometry K A B P) : IsScalarExtensionIsometry K B A P⁻¹ := by
  obtain ⟨hu, hrel⟩ := h
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hu
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hu
  refine ⟨isUnit_iff_exists_inv.mpr ⟨P.det, by rw [← Matrix.det_mul, h2, Matrix.det_one]⟩, ?_⟩
  have e1 : (P.map (algebraMap (𝓞 K) K)) * (P⁻¹.map (algebraMap (𝓞 K) K)) = 1 := by
    have := congrArg (algebraMap (𝓞 K) K).mapMatrix h1
    rw [map_mul, map_one] at this
    exact this
  rw [← hrel]
  calc (P⁻¹.map (algebraMap (𝓞 K) K))ᵀ * ((P.map (algebraMap (𝓞 K) K))ᵀ * B.map (algebraMap ℚ K) *
        P.map (algebraMap (𝓞 K) K)) * P⁻¹.map (algebraMap (𝓞 K) K)
      = (P.map (algebraMap (𝓞 K) K) * P⁻¹.map (algebraMap (𝓞 K) K))ᵀ * B.map (algebraMap ℚ K) *
        (P.map (algebraMap (𝓞 K) K) * P⁻¹.map (algebraMap (𝓞 K) K)) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = B.map (algebraMap ℚ K) := by rw [e1]; simp

theorem iso_ne_zero {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℚ} (hA : IsPosGram A) {P : Matrix (Fin n) (Fin n) (𝓞 K)}
    (hiso : IsScalarExtensionIsometry K A B P) {x : Fin n → ℤ} (hx : x ≠ 0) :
    (P *ᵥ fun j => (x j : 𝓞 K)) ≠ 0 := by
  intro h
  have h1 := formK_mulVec K hiso.2 (fun j => (x j : 𝓞 K))
  have h0 : formK K B (0 : Fin n → 𝓞 K) = 0 := by simp [formK]
  rw [h, h0, formK_cast] at h1
  have h2 : gramQ A x = 0 := (map_eq_zero _).mp h1.symm
  exact (Aux751.gramQ_pos hA hx).ne' h2

/-- **Comparison of minima** (Kitaoka 1993, proof of Theorem 7.5.1, p. 242): for an isometry
$\sigma : R_K L \cong R_K M$ and $(R_K, B_K)$ or $M$ of E-type, $\min(M) \le Q_L(x)$ for every nonzero $x \in L$
(since $\sigma(x) \in R_K M$ has the rational value $Q_L(x)$; Lemma 7.5.5 (i)). -/
theorem gramQ_le_of_iso [IsTotallyReal K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℚ} (hA : IsPosGram A)
    (hB : IsPosGram B) (hSB : SplitOK K B) {P : Matrix (Fin n) (Fin n) (𝓞 K)}
    (hiso : IsScalarExtensionIsometry K A B P) {xB : Fin n → ℤ} (hxB : IsMinimalVector B xB)
    {xA : Fin n → ℤ} (hxA : xA ≠ 0) : gramQ B xB ≤ gramQ A xA := by
  have hy := iso_ne_zero K hA hiso hxA
  have hc : formK K B (P *ᵥ fun j => (xA j : 𝓞 K)) = algebraMap ℚ K (gramQ A xA) := by
    rw [formK_mulVec K hiso.2, formK_cast]
  exact (lemma755 K hB hSB hxB hy hc).1

/-- **The image of a minimal vector is a minimal vector** (Kitaoka 1993, proof of Theorem 7.5.1, p. 242: "$x_1 \in L$
and $\sigma(x_1) \in M$"): if $x$ is a minimal vector of $L$, then $P x \in R_K^n$ lies in $\mathbb Z^n$ and is a minimal
vector of $M$. -/
theorem first_col [IsTotallyReal K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℚ} (hA : IsPosGram A)
    (hB : IsPosGram B) (hSA : SplitOK K A) (hSB : SplitOK K B) {P : Matrix (Fin n) (Fin n) (𝓞 K)}
    (hiso : IsScalarExtensionIsometry K A B P) {xA : Fin n → ℤ} (hxA : IsMinimalVector A xA) :
    ∃ yB : Fin n → ℤ, IsMinimalVector B yB ∧ (P *ᵥ fun j => (xA j : 𝓞 K)) = fun j => (yB j : 𝓞 K) := by
  obtain ⟨xB, hxB⟩ := Aux751.exists_isMinimalVector hB hxA.1
  have h1 := gramQ_le_of_iso K hA hB hSB hiso hxB hxA.1
  have h2 := gramQ_le_of_iso K hB hA hSA (isometry_inv K hiso) hxA hxB.1
  have heq : gramQ A xA = gramQ B xB := le_antisymm h2 h1
  have hy := iso_ne_zero K hA hiso hxA.1
  have hc : formK K B (P *ᵥ fun j => (xA j : 𝓞 K)) = algebraMap ℚ K (gramQ A xA) := by
    rw [formK_mulVec K hiso.2, formK_cast]
  obtain ⟨x', hx'⟩ := (lemma755 K hB hSB hxB hy hc).2 heq
  refine ⟨x', ⟨?_, fun w hw => ?_⟩, hx'⟩
  · intro h0
    apply hy
    rw [hx', h0]
    funext j
    simp
  · have h3 : formK K B (fun j => (x' j : 𝓞 K)) = algebraMap ℚ K (gramQ A xA) := by
      rw [← hx', hc]
    rw [formK_cast] at h3
    have h4 : gramQ B x' = gramQ A xA := (algebraMap ℚ K).injective h3
    rw [h4, heq]
    exact hxB.2 w hw

end Iso2

/-! ### The Schur complement step -/

/-- **Schur complement of an isometry with first column $e_0$.** Let $A = P^{\mathsf T} B P$ over a field, with
$P e_0 = e_0$ and $B_{00} \ne 0$. Writing $P = \begin{pmatrix} 1 & r \\ 0 & P'' \end{pmatrix}$ we have
$A_{00} = B_{00}$, $A_{0,j} = B_{00} r_j + \sum_i B_{0,i} P''_{ij}$, and the Schur complements
$S_A = A_{22} - A_{20} A_{02}/A_{00}$, $S_B = B_{22} - B_{20}B_{02}/B_{00}$ satisfy $S_A = P''^{\mathsf T} S_B P''$.
(Indices $i, j$ below are the 0-based indices of the lower right blocks, shifted by `Fin.succ`.) -/
theorem schur_rel {F : Type*} [Field F] {n : ℕ} (A B P : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (hrel : Pᵀ * B * P = A) (hcol : ∀ i, P i 0 = if i = 0 then 1 else 0) (ha : B 0 0 ≠ 0) :
    A 0 0 = B 0 0 ∧
    (∀ j : Fin n, A 0 j.succ = B 0 0 * P 0 j.succ + ∑ i : Fin n, B 0 i.succ * P i.succ j.succ) ∧
    (∀ k l : Fin n, A k.succ l.succ - A k.succ 0 * A 0 l.succ / A 0 0 =
      ∑ i : Fin n, ∑ i' : Fin n,
        P i.succ k.succ * (B i.succ i'.succ - B i.succ 0 * B 0 i'.succ / B 0 0) * P i'.succ l.succ) := by
  have hA : ∀ p q, A p q = ∑ a, ∑ b, P a p * B a b * P b q := by
    intro p q
    rw [← hrel]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hc0 : ∀ i : Fin n, P i.succ 0 = 0 := fun i => by rw [hcol]; simp
  have hc1 : P 0 0 = 1 := by rw [hcol]; simp
  have h00 : A 0 0 = B 0 0 := by
    rw [hA]
    simp [Fin.sum_univ_succ, hc0, hc1]
  have h0l : ∀ j : Fin n, A 0 j.succ = B 0 0 * P 0 j.succ + ∑ i : Fin n, B 0 i.succ * P i.succ j.succ := by
    intro j
    rw [hA]
    simp [Fin.sum_univ_succ, hc0, hc1]
  have hk0 : ∀ k : Fin n, A k.succ 0 = P 0 k.succ * B 0 0 + ∑ i : Fin n, P i.succ k.succ * B i.succ 0 := by
    intro k
    rw [hA]
    simp [Fin.sum_univ_succ, hc0, hc1]
  have hkl : ∀ k l : Fin n, A k.succ l.succ = P 0 k.succ * B 0 0 * P 0 l.succ +
      P 0 k.succ * (∑ i' : Fin n, B 0 i'.succ * P i'.succ l.succ) +
      (∑ i : Fin n, P i.succ k.succ * B i.succ 0) * P 0 l.succ +
      ∑ i : Fin n, ∑ i' : Fin n, P i.succ k.succ * B i.succ i'.succ * P i'.succ l.succ := by
    intro k l
    rw [hA]
    simp only [Fin.sum_univ_succ, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    ring_nf
  refine ⟨h00, h0l, fun k l => ?_⟩
  have hR : ∑ i : Fin n, ∑ i' : Fin n,
        P i.succ k.succ * (B i.succ i'.succ - B i.succ 0 * B 0 i'.succ / B 0 0) * P i'.succ l.succ =
      (∑ i : Fin n, ∑ i' : Fin n, P i.succ k.succ * B i.succ i'.succ * P i'.succ l.succ) -
        (∑ i : Fin n, P i.succ k.succ * B i.succ 0) * (∑ i' : Fin n, B 0 i'.succ * P i'.succ l.succ) /
          B 0 0 := by
    have h1 : ∑ i : Fin n, ∑ i' : Fin n,
        P i.succ k.succ * (B i.succ i'.succ - B i.succ 0 * B 0 i'.succ / B 0 0) * P i'.succ l.succ =
        ∑ i : Fin n, ∑ i' : Fin n, (P i.succ k.succ * B i.succ i'.succ * P i'.succ l.succ -
          (P i.succ k.succ * B i.succ 0) * (B 0 i'.succ * P i'.succ l.succ) / B 0 0) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring
    rw [h1]
    simp only [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_div]
  rw [hR, hkl, hk0, h0l, h00]
  field_simp
  ring

/-- **Schur complement of a positive Gram matrix is a positive Gram matrix.** -/
theorem schur_pos {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hA : IsPosGram A) :
    IsPosGram (Matrix.of fun i j : Fin n => A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0) := by
  have ha : 0 < A 0 0 := by
    have := hA.2 (Pi.single 0 1) (by
      intro h; have := congrFun h 0; simp at this)
    simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using this
  have hs : ∀ i j, A i j = A j i := fun i j => by
    have := congrFun (congrFun hA.1 j) i
    simpa using this
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [hs j.succ i.succ, hs j.succ 0, hs 0 i.succ]
    ring
  · set β : ℚ := ∑ j : Fin n, A 0 j.succ * x j with hβ
    set v : Fin (n + 1) → ℚ := Fin.cons (-β / A 0 0) x with hv
    have hv0 : v ≠ 0 := by
      intro h
      apply hx
      funext i
      have := congrFun h i.succ
      simpa [hv] using this
    have h1 := hA.2 v hv0
    have h2 : v ⬝ᵥ (A *ᵥ v) = x ⬝ᵥ ((Matrix.of fun i j : Fin n =>
        A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0) *ᵥ x) := by
      have e1 : ∑ i : Fin n, x i * A i.succ 0 = β := by
        rw [hβ]
        exact Finset.sum_congr rfl fun i _ => by rw [hs i.succ 0]; ring
      have hL : v ⬝ᵥ (A *ᵥ v) = (-β / A 0 0) * (A 0 0 * (-β / A 0 0) + β) +
          ((∑ i : Fin n, x i * A i.succ 0) * (-β / A 0 0) +
            ∑ i : Fin n, x i * ∑ j : Fin n, A i.succ j.succ * x j) := by
        simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, hv, Fin.cons_zero, Fin.cons_succ]
        rw [← hβ]
        congr 1
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      have hRr : x ⬝ᵥ ((Matrix.of fun i j : Fin n =>
          A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0) *ᵥ x) =
          (∑ i : Fin n, x i * ∑ j : Fin n, A i.succ j.succ * x j) -
            (∑ i : Fin n, x i * A i.succ 0) * β / A 0 0 := by
        simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
        have hj : ∀ i : Fin n, x i * ∑ j : Fin n, (A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0) * x j =
            x i * ∑ j : Fin n, A i.succ j.succ * x j - x i * A i.succ 0 * β / A 0 0 := by
          intro i
          have : ∑ j : Fin n, (A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0) * x j =
              ∑ j : Fin n, A i.succ j.succ * x j - A i.succ 0 * β / A 0 0 := by
            rw [hβ, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun j _ => by ring
          rw [this]; ring
        rw [Finset.sum_congr rfl fun i _ => hj i, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_mul]
      rw [hL, hRr, e1]
      field_simp
      ring
    rw [h2] at h1
    exact h1

/-- The positive diagonal entries of a positive Gram matrix. -/
theorem posGram_diag {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} (hA : IsPosGram A) (i : Fin n) : 0 < A i i := by
  have := hA.2 (Pi.single i 1) (by
    intro h; have := congrFun h i; simp at this)
  simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using this

/-- **Determinant of a matrix with first column $e_0$** equals the determinant of the lower right block. -/
theorem det_of_col {R : Type*} [CommRing R] {n : ℕ} (P : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hcol : ∀ i, P i 0 = if i = 0 then 1 else 0) : P.det = (P.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Finset.sum_eq_single 0]
  · simp [hcol]
  · intro i _ hi
    simp [hcol, hi]
  · simp

/-- Integer matrices viewed over $R_K$. -/
abbrev icast (K : Type) [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) (𝓞 K) :=
  M.map (Int.cast : ℤ → 𝓞 K)

section Main

variable (K : Type) [Field K] [NumberField K]

theorem icast_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℤ) : icast K (M * N) = icast K M * icast K N := by
  ext i j
  simp [Matrix.mul_apply]

theorem icast_one {n : ℕ} : icast K (1 : Matrix (Fin n) (Fin n) ℤ) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem isUnit_det_icast {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℤ} (h : M * N = 1) : IsUnit (icast K M).det := by
  have h1 : IsUnit M.det := isUnit_iff_exists_inv.mpr ⟨N.det, by rw [← Matrix.det_mul, h, Matrix.det_one]⟩
  have h2 := h1.map (Int.castRingHom (𝓞 K))
  have h3 : (Int.castRingHom (𝓞 K)) M.det = (icast K M).det := by
    rw [RingHom.map_det]; rfl
  rwa [h3] at h2

theorem map_icast {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    (icast K M).map (algebraMap (𝓞 K) K) = M.map (Int.cast : ℤ → K) := by
  ext i j; simp

theorem map_qmat {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    (qmat M).map (algebraMap ℚ K) = M.map (Int.cast : ℤ → K) := by
  ext i j; simp [qmat]

theorem icast_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ) :
    icast K M *ᵥ (fun j => (v j : 𝓞 K)) = fun i => ((M *ᵥ v) i : 𝓞 K) := by
  funext i; simp [Matrix.mulVec, dotProduct]

/-- **Change of bases by unimodular matrices**: if $P : R_K L \cong R_K M$ is an isometry and $U$, $V$ are
unimodular, then $V^{-1} P U$ is an isometry $R_K L' \cong R_K M'$ for $L' = U^{\mathsf T} A U$, $M' = V^{\mathsf T} B V$. -/
theorem iso_conj {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℚ} {P : Matrix (Fin n) (Fin n) (𝓞 K)}
    (hiso : IsScalarExtensionIsometry K A B P) {U Ui V Vi : Matrix (Fin n) (Fin n) ℤ}
    (hUUi : U * Ui = 1) (hVVi : V * Vi = 1) (hViV : Vi * V = 1) :
    IsScalarExtensionIsometry K ((qmat U)ᵀ * A * qmat U) ((qmat V)ᵀ * B * qmat V)
      (icast K Vi * P * icast K U) := by
  obtain ⟨hu, hrel⟩ := hiso
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul]
    exact ((isUnit_det_icast K hViV).mul hu).mul (isUnit_det_icast K hUUi)
  · have hV1 : V.map (Int.cast : ℤ → K) * Vi.map (Int.cast : ℤ → K) = 1 := by
      have := congrArg (Int.castRingHom K).mapMatrix hVVi
      rw [map_mul, map_one] at this
      exact this
    simp only [Matrix.map_mul, ← Matrix.transpose_map, map_icast, map_qmat]
    rw [← hrel]
    simp only [Matrix.transpose_map]
    have key : (Vi.map (Int.cast : ℤ → K) * P.map (algebraMap (𝓞 K) K) * U.map (Int.cast : ℤ → K))ᵀ *
        ((V.map (Int.cast : ℤ → K))ᵀ * B.map (algebraMap ℚ K) * V.map (Int.cast : ℤ → K)) *
        (Vi.map (Int.cast : ℤ → K) * P.map (algebraMap (𝓞 K) K) * U.map (Int.cast : ℤ → K)) =
        (U.map (Int.cast : ℤ → K))ᵀ * ((P.map (algebraMap (𝓞 K) K))ᵀ *
          (V.map (Int.cast : ℤ → K) * Vi.map (Int.cast : ℤ → K))ᵀ * B.map (algebraMap ℚ K) *
          (V.map (Int.cast : ℤ → K) * Vi.map (Int.cast : ℤ → K)) * P.map (algebraMap (𝓞 K) K)) *
          U.map (Int.cast : ℤ → K) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [key, hV1]
    simp

/-- **Integrality of an element of $R_K$ that is rational.** -/
theorem int_of_rat {a : 𝓞 K} {q : ℚ} (h : (a : K) = algebraMap ℚ K q) : ∃ z : ℤ, a = (z : 𝓞 K) := by
  have hint : IsIntegral ℤ (algebraMap ℚ K q) := h ▸ RingOfIntegers.isIntegral_coe a
  have hq : IsIntegral ℤ q := isIntegral_algebraMap_iff.mp hint
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq
  refine ⟨z, RingOfIntegers.coe_injective ?_⟩
  show (a : K) = ((z : 𝓞 K) : K)
  rw [h, ← hz]
  simp

end Main

/-- **Completion of a primitive vector to a unimodular matrix**: if $c \cdot x = 1$ for some $c \in \mathbb Z^{n+1}$
then $x$ is the first column of an integer matrix $U$ with an integer inverse $U^{-1}$. (Basis of the kernel of
$c\cdot$ together with $x$, `Basis.mkFinCons`.) -/
theorem exists_unimodular {n : ℕ} (x : Fin (n + 1) → ℤ) (hx : ∃ c : Fin (n + 1) → ℤ, c ⬝ᵥ x = 1) :
    ∃ U Ui : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ, U * Ui = 1 ∧ Ui * U = 1 ∧ ∀ i, U i 0 = x i := by
  obtain ⟨c, hc⟩ := hx
  let φ : (Fin (n + 1) → ℤ) →ₗ[ℤ] ℤ :=
    { toFun := fun v => c ⬝ᵥ v
      map_add' := fun v w => dotProduct_add c v w
      map_smul' := fun a v => by
        show c ⬝ᵥ (a • v) = a • (c ⬝ᵥ v)
        rw [dotProduct_smul] }
  have hφx : φ x = 1 := hc
  obtain ⟨k, kb⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin (n + 1))) (LinearMap.ker φ)
  have hrange : LinearMap.range φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro a
    exact ⟨a • x, by rw [map_smul, hφx, smul_eq_mul, mul_one]⟩
  have hk : k = n := by
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1
    have h2 := Module.finrank_eq_card_basis kb
    simp only [Fintype.card_fin] at h2
    omega
  subst hk
  have hli : ∀ a : ℤ, ∀ v ∈ LinearMap.ker φ, a • x + v = 0 → a = 0 := by
    intro a v hv h
    have h1 := congrArg φ h
    rw [map_add, map_smul, hφx, LinearMap.mem_ker.mp hv, map_zero] at h1
    simpa using h1
  have hsp : ∀ z : Fin (k + 1) → ℤ, ∃ a : ℤ, z + a • x ∈ LinearMap.ker φ := by
    intro z
    refine ⟨-φ z, ?_⟩
    rw [LinearMap.mem_ker, map_add, map_smul, hφx]
    simp
  let bb := Module.Basis.mkFinCons x kb hli hsp
  have hbb0 : bb 0 = x := by
    simp [bb]
  refine ⟨(Pi.basisFun ℤ (Fin (k + 1))).toMatrix bb, bb.toMatrix (Pi.basisFun ℤ (Fin (k + 1))),
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _, fun i => ?_⟩
  rw [Module.Basis.toMatrix_apply, hbb0]
  simp

end QuadFormsKB.Kitaoka.EType
