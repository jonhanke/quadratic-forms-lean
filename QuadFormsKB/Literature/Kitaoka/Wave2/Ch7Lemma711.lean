/-
# Kitaoka 1993, Section 7.1: Lemma 7.1.1 (3), (ii), (iii) (positive lattices of E-type)

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §7.1, Lemma 7.1.1, pp. 191–192 (printed pages).

**Proves**
* `lemma711eq` (Lemma 7.1.1 (3)): for $L$ of E-type, $\min(L \otimes M) = \min(L)\min(M)$ and
  $\mathcal M(L \otimes M) = \{x \otimes y \mid x \in \mathcal M(L),\ y \in \mathcal M(M)\}$;
* `lemma711iii` (Lemma 7.1.1 (iii)): a submodule $M \subseteq L$ of an E-type lattice with $\min M = \min L$ is of
  E-type;
* `lemma711ii` (Lemma 7.1.1 (ii)): $L \perp M$ and $L \otimes M$ are of E-type if $L$, $M$ are.

**Proof sketches** (all indices 0-based; lattices $L = (\mathbb Z^\iota, A)$, elements of $L \otimes M$ are integer
matrices $X$, $Q(X) = \operatorname{tr}(X^{\mathsf T} A X B)$, split elements are $x y^{\mathsf T}$).
* *Positivity.* $Q_{A \otimes B}(X) = Q_{A \boxtimes B}(\operatorname{vec} X)$ where $A \boxtimes B$ is the Kronecker
  product, a positive Gram matrix (Mathlib's `PosDef.kronecker` after the density argument rational $\to$ real
  positive definite). So $Q > 0$ on nonzero tensors.
* *Existence of minima.* On nonzero integer vectors, $D \cdot Q$ takes positive integer values for a common
  denominator $D$ of the Gram matrix, so a minimum exists by well-ordering (`exists_min_of_den`).
* *(3).* A minimal $X$ is split, $X = x' \otimes y'$ (E-type); $Q(x')Q(y') = Q(X) \le Q(a)Q(b)$ for all nonzero
  $a, b$ shows $x'$, $y'$ minimal. Conversely, a minimal tensor $X_0 = x' \otimes y'$ exists, and
  $Q(x \otimes y) = Q(x')Q(y') = Q(X_0)$ for minimal $x$, $y$.
* *(iii).* With $G = P^{\mathsf T} A P$, $Q_{G \otimes N}(V) = Q_{A \otimes N}(PV)$ and by (3) the minimal values agree,
  so $PV$ is minimal in $L \otimes N$, hence $PV = x' \otimes y'$ with $y'$ minimal, hence primitive (a gcd $g \ge 2$
  would give a smaller vector); with $c \cdot y' = 1$ we get $x' = P(Vc)$ and $V = (Vc) \otimes y'$ by injectivity
  of $P$.
* *(ii), $\perp$.* A minimal $V = (X; Y)$ for $A \perp B$ has $Q(V) = Q(X) + Q(Y)$, so one block vanishes and the
  other is minimal in $L \otimes N$ (or $M \otimes N$), hence split.
* *(ii), $\otimes$.* View $U \in (L \otimes M) \otimes N$ as an element of $L \otimes (M \otimes N)$ (reshaping, same
  value). By E-type of $L$ (transported to any index type, `IsEType.general`), $U = z \otimes w$ with $w$ minimal
  in $M \otimes N$; by E-type of $M$, $w$ is split.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.RingTheory.PrincipalIdealDomain
import QuadFormsKB.Literature.Kitaoka.Ch7EType

open Matrix

noncomputable section

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Kitaoka.EType

section Basic

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- $Q(x) > 0$ for nonzero integer vectors. -/
theorem gramQ_pos {A : Matrix ι ι ℚ} (hA : IsPosGram A) {z : ι → ℤ} (hz : z ≠ 0) : 0 < gramQ A z := by
  refine hA.2 _ ?_
  intro h
  apply hz
  ext i
  have := congrFun h i
  simpa using this

/-- A rational positive Gram matrix is positive definite as a real matrix (general index type; the `Fin r`
version is `posDef_ratCast`). -/
theorem posDef_ratCast_gen (G : Matrix ι ι ℚ) (hG : IsPosGram G) :
    (G.map (Rat.cast : ℚ → ℝ)).PosDef := by
  classical
  set Gr := G.map (Rat.cast : ℚ → ℝ) with hGr
  have hherm : Gr.IsHermitian := by
    have h : Gᵀ = G := hG.1
    have : Grᵀ = Gr := by rw [hGr, ← Matrix.transpose_map, h]
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hpsd : Gr.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => ?_
    simp only [star_trivial]
    have hdense : DenseRange (fun q : ι → ℚ => fun i => (q i : ℝ)) :=
      DenseRange.piMap (f := fun _ : ι => (Rat.cast : ℚ → ℝ)) fun _ => Rat.denseRange_cast
    have hcl : IsClosed {v : ι → ℝ | 0 ≤ v ⬝ᵥ (Gr *ᵥ v)} :=
      isClosed_le continuous_const (by simp only [dotProduct, mulVec]; fun_prop)
    have hsub : Set.range (fun q : ι → ℚ => fun i => (q i : ℝ)) ⊆ {v | 0 ≤ v ⬝ᵥ (Gr *ᵥ v)} := by
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

/-- The Kronecker product of positive Gram matrices is a positive Gram matrix (the Gram matrix of $L \otimes M$). -/
theorem isPosGram_kronecker {A : Matrix ι ι ℚ} {B : Matrix κ κ ℚ} (hA : IsPosGram A) (hB : IsPosGram B) :
    IsPosGram (Matrix.kroneckerMap (· * ·) A B) := by
  classical
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 : Aᵀ = A := hA.1
    have h2 : Bᵀ = B := hB.1
    have e := Matrix.kroneckerMap_transpose (· * ·) A B
    show (Matrix.kroneckerMap (· * ·) A B)ᵀ = _
    rw [← e, h1, h2]
  · have hP := (posDef_ratCast_gen A hA).kronecker (posDef_ratCast_gen B hB)
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

/-- $Q(x) = \sum_{i,k} x_i x_k A_{ik}$ is nonnegative for every integer vector. -/
theorem gramQ_nonneg {A : Matrix ι ι ℚ} (hA : IsPosGram A) (z : ι → ℤ) : 0 ≤ gramQ A z := by
  by_cases hz : z = 0
  · subst hz; simp [gramQ]
  · exact (gramQ_pos hA hz).le

/-- The vectorisation of an integer matrix, as an integer vector indexed by pairs. -/
def vecT (X : Matrix ι κ ℤ) : ι × κ → ℤ := fun p => X p.1 p.2

theorem vecT_ne_zero_iff {X : Matrix ι κ ℤ} : vecT X ≠ 0 ↔ X ≠ 0 := by
  constructor
  · intro h hX; apply h; ext p; simp [vecT, hX]
  · intro h hX; apply h; ext i j; exact congrFun hX (i, j)

/-- $Q_{A \otimes B}(X) = Q_{A \boxtimes B}(\operatorname{vec} X)$ with $A \boxtimes B$ the Kronecker product. -/
theorem tensorQ_eq_gramQ_kron (A : Matrix ι ι ℚ) (B : Matrix κ κ ℚ) (X : Matrix ι κ ℤ) :
    tensorQ A B X = gramQ (Matrix.kroneckerMap (· * ·) A B) (vecT X) := by
  rw [gramQ_eq_sum]
  simp only [tensorQ, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, vecT]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => by ring

theorem tensorQ_pos {A : Matrix ι ι ℚ} {B : Matrix κ κ ℚ} (hA : IsPosGram A) (hB : IsPosGram B)
    {X : Matrix ι κ ℤ} (hX : X ≠ 0) : 0 < tensorQ A B X := by
  rw [tensorQ_eq_gramQ_kron]
  exact gramQ_pos (isPosGram_kronecker hA hB) (vecT_ne_zero_iff.2 hX)

theorem tensorQ_nonneg {A : Matrix ι ι ℚ} {B : Matrix κ κ ℚ} (hA : IsPosGram A) (hB : IsPosGram B)
    (X : Matrix ι κ ℤ) : 0 ≤ tensorQ A B X := by
  rw [tensorQ_eq_gramQ_kron]
  exact gramQ_nonneg (isPosGram_kronecker hA hB) _

/-- Minimal tensors are minimal vectors of the Kronecker-product lattice. -/
theorem isMinimalTensor_iff (A : Matrix ι ι ℚ) (B : Matrix κ κ ℚ) (X : Matrix ι κ ℤ) :
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

/-- A function with values in $\frac1D \mathbb Z$, positive on a nonempty set $S$, attains its minimum on $S$
(well-ordering of $\mathbb N$). -/
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
  have hex : ∃ n : ℕ, ∃ a ∈ S, (n : ℤ) = zf a := ⟨(zf a0).toNat, a0, ha0, Int.toNat_of_nonneg (hzpos a0 ha0).le⟩
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

theorem exists_den_gramQ (A : Matrix ι ι ℚ) :
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
theorem exists_isMinimalVector {A : Matrix ι ι ℚ} (hA : IsPosGram A) {z0 : ι → ℤ} (hz0 : z0 ≠ 0) :
    ∃ x, IsMinimalVector A x := by
  obtain ⟨D, hD, h⟩ := exists_den_gramQ A
  obtain ⟨a, ha, hmin⟩ :=
    exists_min_of_den (gramQ A) D hD h {z | z ≠ 0} (fun z hz => gramQ_pos hA hz) z0 hz0
  exact ⟨a, ha, fun y hy => hmin y hy⟩

/-- $L \otimes M$ has a minimal vector as soon as it has a nonzero vector. -/
theorem exists_isMinimalTensor {A : Matrix ι ι ℚ} {B : Matrix κ κ ℚ} (hA : IsPosGram A) (hB : IsPosGram B)
    {X0 : Matrix ι κ ℤ} (hX0 : X0 ≠ 0) : ∃ X, IsMinimalTensor A B X := by
  obtain ⟨x, hx⟩ := exists_isMinimalVector (isPosGram_kronecker hA hB) (vecT_ne_zero_iff.2 hX0)
  refine ⟨Matrix.of fun i j => x (i, j), (isMinimalTensor_iff A B _).2 ?_⟩
  have : vecT (Matrix.of fun i j => x (i, j) : Matrix ι κ ℤ) = x := by
    funext ⟨i, j⟩; rfl
  rw [this]; exact hx

/-- The components of a minimal split tensor are minimal vectors. -/
theorem isMinimalVector_of_split {A : Matrix ι ι ℚ} {B : Matrix κ κ ℚ} (hA : IsPosGram A) (hB : IsPosGram B)
    {x : ι → ℤ} {y : κ → ℤ} (h : IsMinimalTensor A B (vecMulVec x y)) :
    IsMinimalVector A x ∧ IsMinimalVector B y := by
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

theorem gramQ_eq_of_minimal {A : Matrix ι ι ℚ} {x x' : ι → ℤ} (hx : IsMinimalVector A x)
    (hx' : IsMinimalVector A x') : gramQ A x = gramQ A x' :=
  le_antisymm (hx.2 _ hx'.1) (hx'.2 _ hx.1)

end Basic

/-- **Kitaoka 1993, Lemma 7.1.1 (3)** (p. 191): if $L$ is of E-type then for every positive lattice $M$,
$\min(L \otimes M) = \min(L)\min(M)$ and $\mathcal M(L \otimes M) = \{x \otimes y \mid x \in \mathcal M(L),
y \in \mathcal M(M)\}$. *Proof* (Kitaoka's): a minimal $X$ of $L \otimes M$ is split, $X = x' \otimes y'$, and
$Q(x')Q(y') = Q(X) \le Q(a)Q(b)$ for all nonzero $a, b$, so $x'$, $y'$ are minimal. Conversely, a minimal tensor
$X_0 = x' \otimes y'$ exists (positive integer values of $D\,Q$ and well-ordering), and for minimal $x, y$,
$Q(x \otimes y) = Q(x')Q(y') = Q(X_0) \le Q(Y)$ for all nonzero $Y$. -/
@[kb "kitaoka1993" "§7.1, Lemma 7.1.1 (3), p. 191"]
theorem lemma711eq : Lemma711eq := by
  intro ι _ A hA hE m B hB
  have key : ∀ X, IsMinimalTensor A B X →
      ∃ x y, IsMinimalVector A x ∧ IsMinimalVector B y ∧ X = vecMulVec x y := by
    intro X hX
    obtain ⟨x, y, rfl⟩ := hE m B hB X hX
    obtain ⟨hx, hy⟩ := isMinimalVector_of_split hA hB hX
    exact ⟨x, y, hx, hy, rfl⟩
  refine ⟨?_, ?_⟩
  · intro X x y hX hx hy
    obtain ⟨x', y', hx', hy', rfl⟩ := key X hX
    rw [tensorQ_vecMulVec, gramQ_eq_of_minimal hx' hx, gramQ_eq_of_minimal hy' hy]
  · intro X
    constructor
    · exact key X
    · rintro ⟨x, y, hx, hy, rfl⟩
      obtain ⟨X0, hX0⟩ := exists_isMinimalTensor hA hB (vecMulVec_ne_zero hx.1 hy.1)
      obtain ⟨x', y', hx', hy', rfl⟩ := key X0 hX0
      refine ⟨vecMulVec_ne_zero hx.1 hy.1, fun Y hY => ?_⟩
      have h1 := hX0.2 Y hY
      rw [tensorQ_vecMulVec, gramQ_eq_of_minimal hx' hx, gramQ_eq_of_minimal hy' hy] at h1
      rw [tensorQ_vecMulVec]
      exact h1

/-! ### Lemma 7.1.1 (iii): sublattices of the same minimum -/

section Sub

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The rational matrix of an integer matrix (general index types). -/
abbrev qm (C : Matrix ι κ ℤ) : Matrix ι κ ℚ := C.map (Int.cast : ℤ → ℚ)

/-- $v^{\mathsf T} (C^{\mathsf T} M C) v = (Cv)^{\mathsf T} M (Cv)$ (general index types; `Fin` version
`quad_conj`). -/
theorem quad_conj_gen (C : Matrix ι κ ℚ) (M : Matrix ι ι ℚ) (v : κ → ℚ) :
    v ⬝ᵥ ((Cᵀ * M * C) *ᵥ v) = (C *ᵥ v) ⬝ᵥ (M *ᵥ (C *ᵥ v)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem cast_mulVec_int (C : Matrix ι κ ℤ) (v : κ → ℤ) :
    (fun i => ((C *ᵥ v) i : ℚ)) = qm C *ᵥ fun j => (v j : ℚ) := by
  ext i; simp [Matrix.mulVec, dotProduct, qm]

theorem gramQ_conj (P : Matrix ι κ ℤ) (A : Matrix ι ι ℚ) (v : κ → ℤ) :
    gramQ ((qm P)ᵀ * A * qm P) v = gramQ A (P *ᵥ v) := by
  rw [gramQ, gramQ, quad_conj_gen, cast_mulVec_int]

theorem int_inj_of_rat_inj (P : Matrix ι κ ℤ) (h : Function.Injective (qm P).mulVec) :
    ∀ v, P *ᵥ v = 0 → v = 0 := by
  intro v hv
  have h1 : qm P *ᵥ (fun j => (v j : ℚ)) = qm P *ᵥ 0 := by
    rw [← cast_mulVec_int, hv, Matrix.mulVec_zero]; funext i; simp
  have h2 := h h1
  ext j
  have := congrFun h2 j
  simpa using this

theorem isPosGram_conj_gen {P : Matrix ι κ ℤ} (hinj : Function.Injective (qm P).mulVec) {A : Matrix ι ι ℚ}
    (hA : IsPosGram A) : IsPosGram ((qm P)ᵀ * A * qm P) := by
  refine ⟨?_, fun v hv => ?_⟩
  · have := hA.1
    simp only [Matrix.IsSymm] at this ⊢
    simp [Matrix.transpose_mul, this, Matrix.mul_assoc]
  · rw [quad_conj_gen]
    apply hA.2
    intro h
    exact hv (hinj (by rw [h, Matrix.mulVec_zero]))

/-- $Q(X) = \operatorname{tr}(X^{\mathsf T} A X B)$ for symmetric $B$ (general index types; `Fin` version
`tensorQ_eq_trace`). -/
theorem tensorQ_eq_trace_gen (A : Matrix ι ι ℚ) (B : Matrix κ κ ℚ) (hB : B.IsSymm) (X : Matrix ι κ ℤ) :
    tensorQ A B X = ((qm X)ᵀ * A * qm X * B).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, Matrix.transpose_apply, qm,
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

/-- $Q_{G \otimes N}(V) = Q_{A \otimes N}(PV)$ for $G = P^{\mathsf T} A P$. -/
theorem tensorQ_mul {k : ℕ} (A : Matrix ι ι ℚ) (N : Matrix κ κ ℚ) (hN : N.IsSymm) (P : Matrix ι (Fin k) ℤ)
    (V : Matrix (Fin k) κ ℤ) : tensorQ ((qm P)ᵀ * A * qm P) N V = tensorQ A N (P * V) := by
  rw [tensorQ_eq_trace_gen _ _ hN, tensorQ_eq_trace_gen _ _ hN]
  have hq : qm (P * V) = qm P * qm V := by ext i j; simp [qm, Matrix.mul_apply]
  rw [hq]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

theorem mul_left_cancel_int {k m : ℕ} {P : Matrix ι (Fin k) ℤ} (hP : ∀ v, P *ᵥ v = 0 → v = 0)
    {V V' : Matrix (Fin k) (Fin m) ℤ} (h : P * V = P * V') : V = V' := by
  ext a j
  have h0 : P *ᵥ (fun a => V a j - V' a j) = 0 := by
    ext i
    have := congrFun (congrFun h i) j
    simp only [Matrix.mul_apply] at this
    simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, this, sub_self, Pi.zero_apply]
  have := congrFun (hP _ h0) a
  simpa [sub_eq_zero] using this

theorem gramQ_smul (A : Matrix ι ι ℚ) (g : ℤ) (z : ι → ℤ) :
    gramQ A (fun i => g * z i) = (g : ℚ) ^ 2 * gramQ A z := by
  rw [gramQ_eq_sum, gramQ_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast; ring

/-- A minimal vector is primitive: some integer combination of its entries is $1$ (otherwise $y = g y'$ with
$|g| \ge 2$ and $Q(y') < Q(y)$). -/
theorem exists_dual_of_minimal {N : Matrix κ κ ℚ} (hN : IsPosGram N) {y : κ → ℤ}
    (hy : IsMinimalVector N y) : ∃ c : κ → ℤ, c ⬝ᵥ y = 1 := by
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

/-- **Kitaoka 1993, Lemma 7.1.1 (iii)** (p. 191): if $L = (\mathbb Z^\iota, A)$ is of E-type and $M \subseteq L$ is
a submodule (basis: the columns of $P$) with $\min M = \min L$, then $M$ is of E-type. *Proof* (Kitaoka's): for a
minimal $V$ of $M \otimes N$, $PV$ has the same value $Q_{G \otimes N}(V) = Q_{A \otimes N}(PV)$, and
$Q(V) \le Q_G(y)Q_N(n) = Q_A(x)Q_N(n) = \min(L \otimes N)$ by (3); so $PV$ is minimal in $L \otimes N$, hence
$PV = x' \otimes y'$ with $y'$ minimal, hence primitive ($c \cdot y' = 1$). Then $x' = (PV)c = P(Vc)$ and
$PV = P\big((Vc) \otimes y'\big)$, so $V = (Vc) \otimes y'$ by injectivity of $P$. -/
@[kb "kitaoka1993" "§7.1, Lemma 7.1.1 (iii), p. 191"]
theorem lemma711iii : Lemma711iii := by
  intro ι _ A k P hA hE hinj hQ
  have hP : ∀ v, P *ᵥ v = 0 → v = 0 := int_inj_of_rat_inj P hinj
  have hGpos : IsPosGram ((qm P)ᵀ * A * qm P) := isPosGram_conj_gen hinj hA
  have hQ' : ∀ x y, IsMinimalVector A x → IsMinimalVector ((qm P)ᵀ * A * qm P) y →
      gramQ ((qm P)ᵀ * A * qm P) y = gramQ A x := hQ
  show IsEType ((qm P)ᵀ * A * qm P)
  intro m N hN V hV
  obtain ⟨a, j, hVaj⟩ : ∃ a j, V a j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hV.1
    ext a j
    simp [hcon a j]
  have hv0 : (Pi.single a 1 : Fin k → ℤ) ≠ 0 := by
    intro h; have := congrFun h a; simp at this
  have hw0 : (Pi.single j 1 : Fin m → ℤ) ≠ 0 := by
    intro h; have := congrFun h j; simp at this
  have hz0 : P *ᵥ (Pi.single a 1 : Fin k → ℤ) ≠ 0 := fun h => hv0 (hP _ h)
  obtain ⟨x, hx⟩ := exists_isMinimalVector hA hz0
  obtain ⟨y, hy⟩ := exists_isMinimalVector hGpos hv0
  obtain ⟨n, hn⟩ := exists_isMinimalVector hN hw0
  have h3 := @lemma711eq ι _ A hA hE m N hN
  have hxn : IsMinimalTensor A N (vecMulVec x n) := ((h3.2 _).2 ⟨x, n, hx, hn, rfl⟩)
  have hVle : tensorQ ((qm P)ᵀ * A * qm P) N V ≤ gramQ ((qm P)ᵀ * A * qm P) y * gramQ N n :=
    tensorQ_le_of_isMinimal hV hy hn
  have hW : IsMinimalTensor A N (P * V) := by
    refine ⟨?_, fun Y hY => ?_⟩
    · intro h
      apply hV.1
      exact mul_left_cancel_int hP (by rw [h, Matrix.mul_zero])
    · have h4 := hxn.2 Y hY
      rw [← tensorQ_mul A N hN.1 P V]
      calc _ ≤ gramQ ((qm P)ᵀ * A * qm P) y * gramQ N n := hVle
        _ = gramQ A x * gramQ N n := by rw [hQ' x y hx hy]
        _ = tensorQ A N (vecMulVec x n) := (tensorQ_vecMulVec A N x n).symm
        _ ≤ tensorQ A N Y := h4
  obtain ⟨x', y', hxy⟩ := hE m N hN (P * V) hW
  have hy' : IsMinimalVector N y' := (isMinimalVector_of_split hA hN (hxy ▸ hW)).2
  obtain ⟨c, hc⟩ := exists_dual_of_minimal hN hy'
  have hWc : (P * V) *ᵥ c = x' := by
    rw [hxy]
    ext i
    have : ∑ j, x' i * y' j * c j = x' i * (c ⬝ᵥ y') := by
      rw [dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [Matrix.mulVec, dotProduct, vecMulVec_apply]
    rw [this, hc, mul_one]
  refine ⟨V *ᵥ c, y', ?_⟩
  apply mul_left_cancel_int hP
  rw [Matrix.mul_vecMulVec, Matrix.mulVec_mulVec, hWc, ← hxy]

end Sub

/-! ### Lemma 7.1.1 (ii): orthogonal sums and tensor products -/

section Two

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem tensorQ_zero (A : Matrix ι ι ℚ) (N : Matrix κ κ ℚ) : tensorQ A N 0 = 0 := by
  simp [tensorQ]

/-- Re-indexing the second factor along an equivalence does not change the value of the tensor form. -/
theorem tensorQ_reindex {κ' : Type*} [Fintype κ'] (A : Matrix ι ι ℚ) (G : Matrix κ κ ℚ) (f : κ' ≃ κ)
    (X : Matrix ι κ ℤ) : tensorQ A (G.submatrix f f) (X.submatrix id f) = tensorQ A G X := by
  simp only [tensorQ, Matrix.submatrix_apply, id_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Fintype.sum_equiv f _ _ fun j' => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  exact Fintype.sum_equiv f _ _ fun l' => rfl

/-- **E-type for test lattices of arbitrary index type**: the test lattices $M$ in `IsEType` are indexed by
`Fin m`; transporting along `Fintype.equivFin` the same holds for any finite index type. -/
theorem isEType_general {A : Matrix ι ι ℚ} (hE : IsEType A) {G : Matrix κ κ ℚ} (hG : IsPosGram G)
    {X : Matrix ι κ ℤ} (hX : IsMinimalTensor A G X) : ∃ x y, X = vecMulVec x y := by
  classical
  let e := Fintype.equivFin κ
  have hG' : IsPosGram (G.submatrix e.symm e.symm) := by
    refine ⟨hG.1.submatrix _, fun x hx => ?_⟩
    have hxe : (x ∘ e) ≠ 0 := fun h => hx (by
      funext a; have := congrFun h (e.symm a); simpa using this)
    have h1 := hG.2 _ hxe
    have h2 : G.submatrix e.symm e.symm *ᵥ x = (G *ᵥ (x ∘ e)) ∘ e.symm := by
      rw [Matrix.submatrix_mulVec_equiv]; simp
    rw [h2, dotProduct_comp_equiv_symm]
    exact h1
  have hXe : ∀ Y' : Matrix ι (Fin (Fintype.card κ)) ℤ, Y' = (Y'.submatrix id e).submatrix id e.symm := by
    intro Y'; ext i a; simp
  have hmin : IsMinimalTensor A (G.submatrix e.symm e.symm) (X.submatrix id e.symm) := by
    refine ⟨?_, fun Y' hY' => ?_⟩
    · intro h
      apply hX.1
      ext i j
      have := congrFun (congrFun h i) (e j)
      simpa using this
    · have hY : Y'.submatrix id e ≠ 0 := by
        intro h; apply hY'; ext i a
        have := congrFun (congrFun h i) (e.symm a)
        simpa using this
      have hq1 := tensorQ_reindex A G e.symm X
      have hq2 : tensorQ A (G.submatrix e.symm e.symm) Y' = tensorQ A G (Y'.submatrix id e) := by
        have := tensorQ_reindex A G e.symm (Y'.submatrix id e)
        rwa [← hXe Y'] at this
      rw [hq1, hq2]
      exact hX.2 _ hY
  obtain ⟨x, y', h⟩ := hE _ _ hG' _ hmin
  refine ⟨x, y' ∘ e, ?_⟩
  ext i j
  have := congrFun (congrFun h i) (e j)
  simpa [vecMulVec_apply] using this

theorem tensorQ_fromBlocks_rows {A : Matrix ι ι ℚ} {B : Matrix κ κ ℚ} {m : ℕ} (N : Matrix (Fin m) (Fin m) ℚ)
    (X : Matrix ι (Fin m) ℤ) (Y : Matrix κ (Fin m) ℤ) :
    tensorQ (Matrix.fromBlocks A 0 0 B) N (Matrix.fromRows X Y) = tensorQ A N X + tensorQ B N Y := by
  simp [tensorQ, Fintype.sum_sum_type]

/-- $L \perp M$ is of E-type if $L$ and $M$ are. -/
theorem isEType_fromBlocks {A : Matrix ι ι ℚ} {B : Matrix κ κ ℚ} (_hA : IsPosGram A) (hB : IsPosGram B)
    (hEA : IsEType A) (hEB : IsEType B) : IsEType (Matrix.fromBlocks A 0 0 B) := by
  intro m N hN V hV
  obtain ⟨X, Y, rfl⟩ : ∃ (X : Matrix ι (Fin m) ℤ) (Y : Matrix κ (Fin m) ℤ), V = Matrix.fromRows X Y :=
    ⟨V.toRows₁, V.toRows₂, (Matrix.fromRows_toRows V).symm⟩
  have hrows0 : (Matrix.fromRows (0 : Matrix ι (Fin m) ℤ) (0 : Matrix κ (Fin m) ℤ)) = 0 := by
    ext i j; rcases i with i | i <;> simp
  by_cases hX0 : X = 0
  · subst hX0
    have hY0 : Y ≠ 0 := by
      intro hY; apply hV.1; rw [hY, hrows0]
    have hYmin : IsMinimalTensor B N Y := by
      refine ⟨hY0, fun Y' hY' => ?_⟩
      have hne : Matrix.fromRows (0 : Matrix ι (Fin m) ℤ) Y' ≠ 0 := by
        intro h; apply hY'; ext i j
        have := congrFun (congrFun h (Sum.inr i)) j
        simpa using this
      have h1 := hV.2 _ hne
      rw [tensorQ_fromBlocks_rows, tensorQ_fromBlocks_rows, tensorQ_zero, zero_add, zero_add] at h1
      exact h1
    obtain ⟨y, n, hyn⟩ := hEB m N hN Y hYmin
    refine ⟨Sum.elim 0 y, n, ?_⟩
    ext i j
    rcases i with i | i
    · simp [vecMulVec_apply]
    · have := congrFun (congrFun hyn i) j
      simpa [vecMulVec_apply] using this
  · by_cases hY0 : Y = 0
    · subst hY0
      have hXmin : IsMinimalTensor A N X := by
        refine ⟨hX0, fun X' hX' => ?_⟩
        have hne : Matrix.fromRows X' (0 : Matrix κ (Fin m) ℤ) ≠ 0 := by
          intro h; apply hX'; ext i j
          have := congrFun (congrFun h (Sum.inl i)) j
          simpa using this
        have h1 := hV.2 _ hne
        rw [tensorQ_fromBlocks_rows, tensorQ_fromBlocks_rows, tensorQ_zero, add_zero, add_zero] at h1
        exact h1
      obtain ⟨x, n, hxn⟩ := hEA m N hN X hXmin
      refine ⟨Sum.elim x 0, n, ?_⟩
      ext i j
      rcases i with i | i
      · have := congrFun (congrFun hxn i) j
        simpa [vecMulVec_apply] using this
      · simp [vecMulVec_apply]
    · exfalso
      have hne : Matrix.fromRows X (0 : Matrix κ (Fin m) ℤ) ≠ 0 := by
        intro h; apply hX0; ext i j
        have := congrFun (congrFun h (Sum.inl i)) j
        simpa using this
      have h1 := hV.2 _ hne
      rw [tensorQ_fromBlocks_rows, tensorQ_fromBlocks_rows, tensorQ_zero, add_zero] at h1
      have := tensorQ_pos hB hN hY0
      linarith

theorem tensorQ_kron_reshape (A : Matrix ι ι ℚ) (B : Matrix κ κ ℚ) {m : ℕ} (N : Matrix (Fin m) (Fin m) ℚ)
    (U : Matrix (ι × κ) (Fin m) ℤ) :
    tensorQ (Matrix.kroneckerMap (· * ·) A B) N U =
      tensorQ A (Matrix.kroneckerMap (· * ·) B N)
        (Matrix.of fun i (jt : κ × Fin m) => U (i, jt.1) jt.2) := by
  simp only [tensorQ, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => ?_
  exact Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ =>
    Finset.sum_congr rfl fun t' _ => by ring

/-- $L \otimes M$ is of E-type if $L$ and $M$ are. -/
theorem isEType_kronecker {A : Matrix ι ι ℚ} {B : Matrix κ κ ℚ} (hA : IsPosGram A) (hB : IsPosGram B)
    (hEA : IsEType A) (hEB : IsEType B) : IsEType (Matrix.kroneckerMap (· * ·) A B) := by
  intro m N hN U hU
  have hG : IsPosGram (Matrix.kroneckerMap (· * ·) B N) := isPosGram_kronecker hB hN
  set U' : Matrix ι (κ × Fin m) ℤ := Matrix.of fun i jt => U (i, jt.1) jt.2 with hU'def
  have hmin : IsMinimalTensor A (Matrix.kroneckerMap (· * ·) B N) U' := by
    refine ⟨?_, fun Y' hY' => ?_⟩
    · intro h
      apply hU.1
      ext ⟨i, j⟩ t
      have := congrFun (congrFun h i) (j, t)
      simpa [hU'def] using this
    · set Y : Matrix (ι × κ) (Fin m) ℤ := Matrix.of fun p t => Y' p.1 (p.2, t) with hY
      have hYne : Y ≠ 0 := by
        intro h; apply hY'; ext i ⟨j, t⟩
        have := congrFun (congrFun h (i, j)) t
        simpa [hY] using this
      have hYY : (Matrix.of fun i (jt : κ × Fin m) => Y (i, jt.1) jt.2) = Y' := by
        ext i ⟨j, t⟩; rfl
      have h1 := hU.2 Y hYne
      rw [tensorQ_kron_reshape, tensorQ_kron_reshape, hYY] at h1
      exact h1
  obtain ⟨z, w, hzw⟩ := isEType_general hEA hG hmin
  have hw : IsMinimalVector (Matrix.kroneckerMap (· * ·) B N) w :=
    (isMinimalVector_of_split hA hG (hzw ▸ hmin)).2
  have hW : IsMinimalTensor B N (Matrix.of fun j t => w (j, t)) := by
    rw [isMinimalTensor_iff]
    have : vecT (Matrix.of fun j t => w (j, t) : Matrix κ (Fin m) ℤ) = w := by
      funext ⟨j, t⟩; rfl
    rw [this]; exact hw
  obtain ⟨y, n, hyn⟩ := hEB m N hN _ hW
  refine ⟨fun p => z p.1 * y p.2, n, ?_⟩
  ext ⟨i, j⟩ t
  have h1 := congrFun (congrFun hzw i) (j, t)
  have h2 := congrFun (congrFun hyn j) t
  simp only [hU'def, Matrix.of_apply, vecMulVec_apply] at h1 h2 ⊢
  rw [h1, h2]
  ring

/-- **Kitaoka 1993, Lemma 7.1.1 (ii)** (p. 191): if $L$ and $M$ are of E-type then so are $L \perp M$ and
$L \otimes M$. *Proof* (Kitaoka's). $\perp$: a minimal $V = (X; Y)$ of $(L \perp M) \otimes N$ has
$Q(V) = Q(X) + Q(Y)$ with $Q > 0$ on nonzero tensors, so one block vanishes (else $(X;0)$ has smaller value), and the
other is minimal in $L \otimes N$ (or $M \otimes N$) hence split. $\otimes$: view $U \in (L \otimes M) \otimes N$ as
an element of $L \otimes (M \otimes N)$ (reshaping keeps the value); as $L$ is of E-type (for test lattices of any
finite index type, `isEType_general`) $U = z \otimes w$, $w$ is minimal in $M \otimes N$ (`isMinimalVector_of_split`),
hence split since $M$ is of E-type. -/
@[kb "kitaoka1993" "§7.1, Lemma 7.1.1 (ii), p. 191"]
theorem lemma711ii : Lemma711ii := by
  intro ι κ _ _ A B hA hB hEA hEB
  exact ⟨isEType_fromBlocks hA hB hEA hEB, isEType_kronecker hA hB hEA hEB⟩

end Two

end QuadFormsKB.Kitaoka.EType
