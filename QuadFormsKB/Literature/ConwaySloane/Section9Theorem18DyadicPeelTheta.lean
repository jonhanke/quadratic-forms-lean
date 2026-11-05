/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$, peeling with a spinor-norm remainder

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18 and the remark after it, at $p = 2$. The peeling framework of
`Section9Theorem18DyadicPeel.lean` / `Section9Theorem18DyadicPeelBinary.lean` proves that the integral automorphisms
of $L_2$ are *generated* by integral reflections when the lattice has a chain of orthogonal basis vectors followed by
a remainder of rank $\le 2$. For some lattices the remainder after peeling is a block where only a statement about the
**spinor norm** is known: the Wall-formula results for a scaled even unimodular lattice $2^kE$ and for
$2^k(E \perp \langle 2u\rangle)$ (`Section9Theorem18DyadicEven.lean`, `Section9Theorem18DyadicGlue2.lean`). This file
builds the relative spinor-norm version of the peeling framework.

**Layer.** As in `Section9Theorem18DyadicPeel.lean`: over $\mathbb Q$ at the prime $v$ over $2$, the form $Q$ on
$\mathbb Q_2^n$ with bilinear form $B(x, y) = Q(x + y) - Q(x) - Q(y)$, a lattice $L$ with localization $L_2$, a basis
$b_k = \gamma e_k$ of $L_2$ with Gram matrix $G = \gamma^{\mathsf T}H\gamma$ (`locGram`, $G_{kk} = 2Q(b_k)$), the
reflections $\tau_x$ (`symm`), $O(L_2)$ (`locStabV`), the $2$-adic root vectors (`IsRootVector`) and the spinor norm
$\theta$ (`spinorNorm`). Indices are $0$-based. For a set $T$ of indices (the peeled ones) the **complement** is
$K = \{0, \dots, n-1\} \setminus T$, $m = \lvert K\rvert$, enumerated by `compEquiv`, and the **block** of a matrix $A$
on $K$ is `compBlock T A` ($m \times m$).

**Defines**
* `FixTheta Q L v γ T` (the **relative spinor-norm fixing condition**): every $\sigma \in O(L_2)$ fixing $b_t$ for all
  $t \in T$ has $\det\sigma = (-1)^r$ and $\theta(\sigma) = Q(x_1)\cdots Q(x_r)F_2^{\times 2}$ for some $2$-adic root
  vectors $x_1, \dots, x_r$. (`FixGenerated` implies it; for $T = \emptyset$ it is Theorem 18's "only if" for
  all of $O(L_2)$.)
* `compEquiv`, `compBlock`, `conjMat` (the complement of $T$, the block of a matrix on it, and the matrix
  $S' = \gamma^{-1}\sigma\gamma$ of $\sigma$ in the basis $b$);
* `IsBlockEvenUnimodular G T c`, `IsBlockGlue2 G T c l` (**conditions** on the Gram matrix $G$: the block of $cG$ on
  the complement of $T$ is even unimodular, resp. of the form $E \perp \langle 2u\rangle$ with $E$ even unimodular
  and $u$ a unit);
* `PeelChainTheta G T ks` (the **shape predicate**): as `PeelChain2`, except that the final remainder is allowed to be
  a block of the above two kinds (instead of only of rank $\le 2$).

**Proves**
* `fixTheta_of_fixGenerated`: `FixGenerated` implies `FixTheta`;
* `exists_peel_reflections`, `fixTheta_peel` (**the peeling step for `FixTheta`**, the analogue of `fixGenerated_peel`);
* the **restriction lemma** (the blocks of $\sigma$): `conj_block_data`, `restrict_block`, and the generic matrix lemmas
  `blk_rowZero`, `blk_orth`, `blk_det`, `blk_frame`, `blk_gram`: if $\sigma$ fixes the $b_t$ ($t \in T$), then
  $S' = \gamma^{-1}\sigma\gamma$ satisfies $S'e_t = e_t$ and (since $S'$ preserves the orthogonal complement of the
  $b_t$) $S'_{ta} = 0$ for $a \notin T$; the block $S_K$ of $S'$ is integral with $S_K^{\mathsf T}A_KS_K = A_K$
  ($A = cG$), $\det S_K = \det S'$, and a Wall frame $(P, R)$ of $S'$ restricts to the Wall frame $(P_K, R_K)$ of $S_K$
  with $P_K^{\mathsf T}A_KR_K = P^{\mathsf T}AR$ (the rows $t \in T$ of $P = (1 - S')R$ vanish);
* `exists_rootVector_block`: root vectors of every unit norm $c^{-1}w$ in the span of the block, orthogonal to the
  $b_t$;
* `fixTheta_of_wallSq` (**the common tail**: Wall squares plus root vectors of unit norms give `FixTheta`),
  `wallSq_of_block_even`, `wallSq_of_block_glue`;
* `fixTheta_of_block_scaledEvenUnimodular` (**block base case (b)**) and `fixTheta_of_block_glue` (**block base
  case (c)**);
* `fixTheta_of_peelChainTheta`, `theorem18OnlyIf_of_peelChainTheta` (**Theorem 18, "only if", for a peeling chain
  with a spinor-norm remainder**, unconditional).

**Test example.** Let $M = \langle u\rangle \perp 2K \perp 4\langle w\rangle$ be the Gram matrix of the form
(diagonal entries $Q(b_i)$), $u, w$ $2$-adic units and $K$ a binary even unimodular block, $K = \begin{pmatrix}0&1\\1&0
\end{pmatrix}$ or $\begin{pmatrix}2&1\\1&2\end{pmatrix}$, so $G = 2M = \langle 2u\rangle \perp 4K \perp \langle 8w\rangle$
($n = 4$, indices $0$; $1, 2$; $3$). Peel $b_0$ (`ks = [0]`): $b_0$ is orthogonal to the others and the later entries
$\lvert G_{ii'}\rvert \le \lvert 4\rvert = \lvert 2G_{00}\rvert$. The remainder is
$G_K = 4K \perp \langle 8w\rangle = 4(K \perp \langle 2w\rangle)$; with $c = 1/4$ the block of $cG$ is
$K \perp \langle 2w\rangle$, which is `IsBlockGlue2` for $l = 3$ ($cG_{33}/2 = w$ a unit, $G_{i3} = 0$ for $i \ne 3$,
$\lvert\det\rvert = \lvert\det K\rvert\lvert 2w\rvert = \lvert 2\rvert$). So `PeelChainTheta G ∅ [0]` holds and
`theorem18OnlyIf_of_peelChainTheta` gives Theorem 18's "only if" for $L_2$, although `PeelChain2` does not apply (the
remainder has rank $3$) and `FixGenerated` is not available for the remainder.
-/

import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicPeelBinary

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices Wall Levels EvenUnimodular

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion


section BlockMat

variable {K : Type*} [Field K] [CharZero K] {n m : ℕ} {T : Finset (Fin n)}

/-- The index of the $a$-th complement coordinate. -/
abbrev blkIdx (e : Fin m ≃ {i // i ∉ T}) (a : Fin m) : Fin n := (e a).1

theorem blkIdx_inj (e : Fin m ≃ {i // i ∉ T}) : Function.Injective (blkIdx e) :=
  fun _ _ h => e.injective (Subtype.ext h)

theorem blkIdx_notMem (e : Fin m ≃ {i // i ∉ T}) (a : Fin m) : blkIdx e a ∉ T := (e a).2

theorem exists_blkIdx (e : Fin m ≃ {i // i ∉ T}) {i : Fin n} (hi : i ∉ T) : ∃ a, blkIdx e a = i :=
  ⟨e.symm ⟨i, hi⟩, congrArg Subtype.val (e.apply_symm_apply ⟨i, hi⟩)⟩

theorem sum_blk (e : Fin m ≃ {i // i ∉ T}) (f : Fin n → K) (hf : ∀ t ∈ T, f t = 0) :
    ∑ i, f i = ∑ a, f (blkIdx e a) := by
  classical
  rw [← Finset.sum_image (f := f) (s := Finset.univ) (g := blkIdx e) (fun a _ b _ h => blkIdx_inj e h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  by_cases hiT : i ∈ T
  · exact hf i hiT
  · exfalso
    obtain ⟨a, ha⟩ := exists_blkIdx e hiT
    exact hi (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩)

theorem blk_rowZero {G S : Matrix (Fin n) (Fin n) K} (hG : Gᵀ = G)
    (hT : ∀ t ∈ T, ∀ m, m ≠ t → G m t = 0) (hGtt : ∀ t ∈ T, G t t ≠ 0) (hSG : Sᵀ * G * S = G)
    (F1 : ∀ t ∈ T, ∀ i, S i t = if i = t then 1 else 0) {t : Fin n} (ht : t ∈ T) {a : Fin n}
    (ha : a ∉ T) : S t a = 0 := by
  have hat : a ≠ t := fun h => ha (h ▸ ht)
  have hsym : ∀ i j, G j i = G i j := fun i j => by
    simpa [transpose_apply] using congrFun (congrFun hG i) j
  have h := congrFun (congrFun hSG t) a
  rw [Matrix.mul_apply] at h
  have h1 : ∀ j, (Sᵀ * G) t j = G t j := by
    intro j
    simp only [Matrix.mul_apply, transpose_apply, F1 t ht]
    simp
  simp only [h1] at h
  rw [Finset.sum_eq_single t] at h
  · have : G t a = 0 := by rw [hsym]; exact hT t ht a hat
    rw [this] at h
    exact (mul_eq_zero.mp h).resolve_left (hGtt t ht)
  · intro j _ hj
    have : G t j = 0 := by rw [hsym]; exact hT t ht j hj
    rw [this, zero_mul]
  · simp

theorem blk_orth (e : Fin m ≃ {i // i ∉ T}) {A S : Matrix (Fin n) (Fin n) K} (hSA : Sᵀ * A * S = A)
    (F2 : ∀ t ∈ T, ∀ a, a ∉ T → S t a = 0) :
    (S.submatrix (blkIdx e) (blkIdx e))ᵀ * A.submatrix (blkIdx e) (blkIdx e) *
      S.submatrix (blkIdx e) (blkIdx e) = A.submatrix (blkIdx e) (blkIdx e) := by
  ext a b
  have h := congrFun (congrFun hSA (blkIdx e a)) (blkIdx e b)
  simp only [Matrix.mul_apply, transpose_apply, submatrix_apply] at h ⊢
  rw [sum_blk e (fun j => (∑ i, S i (blkIdx e a) * A i j) * S j (blkIdx e b))
    (fun t ht => by rw [F2 t ht _ (blkIdx_notMem e b), mul_zero])] at h
  have : ∀ j, ∑ i, S i (blkIdx e a) * A i j = ∑ x, S (blkIdx e x) (blkIdx e a) * A (blkIdx e x) j :=
    fun j => sum_blk e (fun i => S i (blkIdx e a) * A i j)
      (fun t ht => by rw [F2 t ht _ (blkIdx_notMem e a), zero_mul])
  simp only [this] at h
  exact h

theorem blk_det (e : Fin m ≃ {i // i ∉ T}) {S : Matrix (Fin n) (Fin n) K}
    (F1 : ∀ t ∈ T, ∀ i, S i t = if i = t then 1 else 0)
    (F2 : ∀ t ∈ T, ∀ a, a ∉ T → S t a = 0) :
    (S.submatrix (blkIdx e) (blkIdx e)).det = S.det := by
  classical
  let eq1 : {i // i ∈ T} ⊕ {i // ¬ i ∈ T} ≃ Fin n := Equiv.sumCompl (· ∈ T)
  have hblk : S.submatrix eq1 eq1 =
      fromBlocks (1 : Matrix {i // i ∈ T} {i // i ∈ T} K) 0 0
        (S.submatrix (Subtype.val : {i // ¬ i ∈ T} → Fin n) Subtype.val) := by
    ext x y
    rcases x with x | x <;> rcases y with y | y
    · show S x.1 y.1 = (1 : Matrix {i // i ∈ T} {i // i ∈ T} K) x y
      rw [F1 y.1 y.2 x.1, Matrix.one_apply]
      simp only [Subtype.ext_iff]
    · show S x.1 y.1 = 0
      exact F2 x.1 x.2 y.1 y.2
    · have : (x.1 : Fin n) ≠ y.1 := fun h => x.2 (h ▸ y.2)
      show S x.1 y.1 = 0
      rw [F1 y.1 y.2 x.1]
      simp [this]
    · rfl
  have h1 : S.det = (S.submatrix eq1 eq1).det := (Matrix.det_submatrix_equiv_self eq1 S).symm
  rw [h1, hblk, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
  have := Matrix.det_submatrix_equiv_self e
    (S.submatrix (Subtype.val : {i // ¬ i ∈ T} → Fin n) Subtype.val)
  rw [← this]
  rfl

theorem blk_oneSub_row {S : Matrix (Fin n) (Fin n) K} (F1 : ∀ t ∈ T, ∀ i, S i t = if i = t then 1 else 0)
    (F2 : ∀ t ∈ T, ∀ a, a ∉ T → S t a = 0) {t : Fin n} (ht : t ∈ T) (i : Fin n) : (1 - S) t i = 0 := by
  by_cases hi : i ∈ T
  · rw [Matrix.sub_apply, F1 i hi t, Matrix.one_apply]; simp
  · have hti : t ≠ i := fun h => hi (h ▸ ht)
    rw [Matrix.sub_apply, F2 t ht i hi, Matrix.one_apply]; simp [hti]

theorem blk_oneSub_col {S : Matrix (Fin n) (Fin n) K} (F1 : ∀ t ∈ T, ∀ i, S i t = if i = t then 1 else 0)
    {t : Fin n} (ht : t ∈ T) (i : Fin n) : (1 - S) i t = 0 := by
  rw [Matrix.sub_apply, F1 t ht i, Matrix.one_apply]; simp

theorem blk_oneSub (e : Fin m ≃ {i // i ∉ T}) (S : Matrix (Fin n) (Fin n) K) (a b : Fin m) :
    (1 - S.submatrix (blkIdx e) (blkIdx e)) a b = (1 - S) (blkIdx e a) (blkIdx e b) := by
  simp [Matrix.sub_apply, Matrix.one_apply, (blkIdx_inj e).eq_iff]

theorem blk_P_zero {S : Matrix (Fin n) (Fin n) K} (F1 : ∀ t ∈ T, ∀ i, S i t = if i = t then 1 else 0)
    (F2 : ∀ t ∈ T, ∀ a, a ∉ T → S t a = 0) {m' : ℕ} {P R : Matrix (Fin n) (Fin m') K}
    (hf : IsWallFrame K S P R) {t : Fin n} (ht : t ∈ T) (j : Fin m') : P t j = 0 := by
  rw [← hf.1, Matrix.mul_apply]
  exact Finset.sum_eq_zero fun i _ => by rw [blk_oneSub_row F1 F2 ht, zero_mul]

theorem blk_frame (e : Fin m ≃ {i // i ∉ T}) {S : Matrix (Fin n) (Fin n) K}
    (F1 : ∀ t ∈ T, ∀ i, S i t = if i = t then 1 else 0)
    (F2 : ∀ t ∈ T, ∀ a, a ∉ T → S t a = 0) {m' : ℕ} {P R : Matrix (Fin n) (Fin m') K}
    (hf : IsWallFrame K S P R) :
    IsWallFrame K (S.submatrix (blkIdx e) (blkIdx e)) (P.submatrix (blkIdx e) id)
      (R.submatrix (blkIdx e) id) := by
  obtain ⟨hTR, hinj, hspan⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · ext a j
    have h := congrFun (congrFun hTR (blkIdx e a)) j
    rw [Matrix.mul_apply] at h
    rw [sum_blk e (fun i => (1 - S) (blkIdx e a) i * R i j)
      (fun t ht => by rw [blk_oneSub_col F1 ht, zero_mul])] at h
    simp only [Matrix.mul_apply, submatrix_apply, id, blk_oneSub]
    exact h
  · intro c hc
    apply hinj c
    funext i
    by_cases hiT : i ∈ T
    · simp only [mulVec, dotProduct, Pi.zero_apply]
      exact Finset.sum_eq_zero fun j _ => by
        rw [blk_P_zero F1 F2 ⟨hTR, hinj, hspan⟩ hiT j, zero_mul]
    · obtain ⟨a, rfl⟩ := exists_blkIdx e hiT
      have := congrFun hc a
      simpa [mulVec, dotProduct] using this
  · intro z
    let z' : Fin n → K := fun i => if h : i ∈ T then 0 else z (e.symm ⟨i, h⟩)
    have hz' : ∀ a, z' (blkIdx e a) = z a := fun a => by
      simp [z', blkIdx_notMem e a]
    obtain ⟨c, hc⟩ := hspan z'
    refine ⟨c, ?_⟩
    funext a
    have h := congrFun hc (blkIdx e a)
    simp only [mulVec, dotProduct] at h ⊢
    rw [sum_blk e (fun x => ((1 - S) (blkIdx e a) x) * z' x)
      (fun t ht => by simp [z', ht])] at h
    simp only [hz'] at h
    simp only [blk_oneSub, submatrix_apply, id]
    exact h

theorem blk_gram (e : Fin m ≃ {i // i ∉ T}) {A S : Matrix (Fin n) (Fin n) K}
    (F1 : ∀ t ∈ T, ∀ i, S i t = if i = t then 1 else 0)
    (F2 : ∀ t ∈ T, ∀ a, a ∉ T → S t a = 0) (hA : ∀ t ∈ T, ∀ i, i ∉ T → A i t = 0) {m' : ℕ}
    {P R : Matrix (Fin n) (Fin m') K} (hf : IsWallFrame K S P R) :
    (P.submatrix (blkIdx e) id)ᵀ * A.submatrix (blkIdx e) (blkIdx e) * R.submatrix (blkIdx e) id =
      Pᵀ * A * R := by
  ext a b
  simp only [Matrix.mul_apply, transpose_apply, submatrix_apply, id]
  rw [sum_blk e (fun j => (∑ i, P i a * A i j) * R j b)
    (fun t ht => by
      rw [Finset.sum_eq_zero (fun i _ => ?_), zero_mul]
      by_cases hi : i ∈ T
      · rw [blk_P_zero F1 F2 hf hi, zero_mul]
      · rw [hA t ht i hi, mul_zero])]
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  exact (sum_blk e (fun i => P i a * A i (blkIdx e y)) (fun t ht => by
    rw [blk_P_zero F1 F2 hf ht, zero_mul])).symm

end BlockMat


/-! ### The relative spinor-norm fixing condition -/

section Theta

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

variable (Q L v) in
/-- **The relative spinor-norm fixing condition** for a set $T$ of basis indices of $L_2 = \gamma\,\mathrm{std}$
($b_t = \gamma e_t$): every $\sigma \in O(L_2)$ with $\sigma b_t = b_t$ for all $t \in T$ has the shape of Theorem 18,
i.e. there is a list $x_1, \dots, x_r$ of $2$-adic root vectors of $L$ with $\det\sigma = (-1)^r$ and
$\theta(\sigma) = Q(x_1)\cdots Q(x_r)\,F_2^{\times 2}$. (The $x_j$ are not required to be orthogonal to the $b_t$ and
$\sigma$ itself need not be their product of reflections: this is a statement about the spinor norm only.) It is
implied by `FixGenerated` (`fixTheta_of_fixGenerated`). For $T = \emptyset$ and $\det\sigma = 1$ it is the condition
of Theorem 18 for $\sigma$ (`theorem18OnlyIf_of_peelChainTheta`). -/
def FixTheta (γ : GL (Fin n) Fv) (T : Finset (Fin n)) : Prop :=
  ∀ σ : orthGroup Q Fv, σ ∈ locStabV Q v L →
    (∀ t ∈ T, (σ : GL (Fin n) Fv).val *ᵥ basisVec γ t = basisVec γ t) →
    ∃ xs : List (Fin n → Fv), (∀ x ∈ xs, IsRootVector Q L v x) ∧
      ((σ : GL (Fin n) Fv).val).det = (-1) ^ xs.length ∧ spinorNorm Q Fv σ = sqClassOf (valProd Q Fv xs)

theorem orthGroup_det_mul (a b : orthGroup Q Fv) :
    ((a * b : orthGroup Q Fv) : GL (Fin n) Fv).val.det =
      (a : GL (Fin n) Fv).val.det * (b : GL (Fin n) Fv).val.det := by
  change ((a : GL (Fin n) Fv).val * (b : GL (Fin n) Fv).val).det = _
  exact det_mul _ _

theorem det_symmProd_pow (xs : List (Fin n → Fv)) (hxs : ∀ x ∈ xs, Q.evalIn Fv x ≠ 0) :
    ((symmProd Q Fv xs : orthGroup Q Fv) : GL (Fin n) Fv).val.det = (-1) ^ xs.length := by
  have := detHom_symmProd Q Fv xs hxs
  rwa [detHom_val] at this

theorem valProd_append' (xs ys : List (Fin n → Fv)) :
    valProd Q Fv (xs ++ ys) = valProd Q Fv xs * valProd Q Fv ys := by
  simp [valProd, List.map_append, List.prod_append]

/-- **`FixGenerated` implies `FixTheta`**: a product of reflections $\tau_{x_1}\cdots\tau_{x_r}$ has determinant
$(-1)^r$ (`symm_det`) and spinor norm $Q(x_1)\cdots Q(x_r)F_2^{\times 2}$ (`spinorNorm_symmProd`). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (a product of root reflections has the spinor norm of Thm. 18)"]
theorem fixTheta_of_fixGenerated (hQ : Q.Nondegenerate) {γ : GL (Fin n) Fv} {T : Finset (Fin n)}
    (h : FixGenerated Q L v γ T) : FixTheta Q L v γ T := by
  intro σ hσ hfix
  obtain ⟨l, hl, rfl⟩ := h σ hσ hfix
  have hl0 : ∀ x ∈ l, Q.evalIn Fv x ≠ 0 := fun x hx => (hl x hx).1.1
  exact ⟨l, fun x hx => (hl x hx).1, det_symmProd_pow l hl0, spinorNorm_symmProd Q Fv hQ l hl0⟩

/-- **The peeling step, with the reflections made explicit.** Under the hypotheses of `fixGenerated_peel` (without
`hgen`), every $\sigma \in O(L_2)$ fixing the $b_t$, $t \in T$, factors as $\sigma = \tau_{x_1}\cdots\tau_{x_r}\sigma'$
with $r \le 2$, the $x_j$ $2$-adic root vectors orthogonal to all $b_t$ ($t \in T$), and $\sigma' \in O(L_2)$ fixing
the $b_t$ for $t \in T \cup \{k\}$. (This is the first half of the proof of `fixGenerated_peel`, copied from there.) -/
theorem exists_peel_reflections (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) (T : Finset (Fin n)) (k : Fin n) (hkT : k ∉ T)
    (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0)
    (hk : ∀ m, m ≠ k → locGram Q v γ m k = 0)
    (hd : ∀ i i', i ∉ insert k T → i' ∉ insert k T →
      Valued.v (locGram Q v γ i i') ≤ Valued.v (2 * locGram Q v γ k k))
    (σ : orthGroup Q Fv) (hσ : σ ∈ locStabV Q v L)
    (hfix : ∀ t ∈ T, (σ : GL (Fin n) Fv).val *ᵥ basisVec γ t = basisVec γ t) :
    ∃ (l : List (Fin n → Fv)) (σ' : orthGroup Q Fv),
      (∀ u ∈ l, IsRootVector Q L v u ∧ ∀ t ∈ T, qbil Q Fv u (basisVec γ t) = 0) ∧
      σ = symmProd Q Fv l * σ' ∧ σ' ∈ locStabV Q v L ∧
      ∀ t ∈ insert k T, (σ' : GL (Fin n) Fv).val *ᵥ basisVec γ t = basisVec γ t := by

  have hGkk : locGram Q v γ k k ≠ 0 := locGram_diag_ne_zero hQ γ hk
  have hGtt : ∀ t ∈ T, locGram Q v γ t t ≠ 0 := fun t ht => locGram_diag_ne_zero hQ γ (hT t ht)
  have hbkM : basisVec γ k ∈ loc v L.1 := by
    rw [hγ]; exact ⟨_, single_mem_std k (by simp), rfl⟩
  have hσM : locAct v (σ : GL (Fin n) Fv) (loc v L.1) = loc v L.1 := hσ
  have hyM : (σ : GL (Fin n) Fv).val *ᵥ basisVec γ k ∈ loc v L.1 := by
    have : (σ : GL (Fin n) Fv).val *ᵥ basisVec γ k ∈ locAct v (σ : GL (Fin n) Fv) (loc v L.1) :=
      ⟨_, hbkM, rfl⟩
    rwa [hσM] at this
  set y := (σ : GL (Fin n) Fv).val *ᵥ basisVec γ k with hy
  obtain ⟨d, hdstd, hyd⟩ : ∃ d ∈ std v, γ.val *ᵥ d = y := by rw [hγ] at hyM; exact hyM
  have hdle := mem_std_iff.mp hdstd
  have hbt : ∀ t ∈ T, qbil Q Fv y (basisVec γ t) = 0 := by
    intro t ht
    have h := qbil_orth Q Fv σ (basisVec γ k) (basisVec γ t)
    change qbil Q Fv y ((σ : GL (Fin n) Fv).val *ᵥ basisVec γ t) = _ at h
    rw [hfix t ht, qbil_basisVec] at h
    rw [h]; exact hT t ht k (fun h => hkT (h ▸ ht))
  have hdt : ∀ t ∈ T, d t = 0 := by
    intro t ht
    have := hbt t ht
    rw [← hyd, qbil_vec_basisVec γ (hT t ht)] at this
    exact (mul_eq_zero.mp this).resolve_right (hGtt t ht)
  set s := d k with hs
  set z : Fin n → Fv := Function.update d k 0 with hz
  have hzk : z k = 0 := by simp [hz]
  have hzi : ∀ i, i ≠ k → z i = d i := fun i hi => by simp [hz, hi]
  have hdz : d = z + Pi.single k s := by
    ext i
    by_cases hi : i = k
    · subst hi; simp [hz, hs]
    · simp [hzi i hi, hi]
  have hzsupp : ∀ i ∈ insert k T, z i = 0 := by
    intro i hi
    by_cases hik : i = k
    · subst hik; exact hzk
    · rw [hzi i hik]
      exact hdt i ((Finset.mem_insert.mp hi).resolve_left hik)
  have hz1 : ∀ i, Valued.v (z i) ≤ 1 := fun i => by
    by_cases hi : i = k
    · subst hi; rw [hzk, map_zero]; exact zero_le
    · rw [hzi i hi]; exact hdle i
  have hs1 : Valued.v s ≤ 1 := hdle k
  have hzz : Valued.v (z ⬝ᵥ (locGram Q v γ *ᵥ z)) ≤ Valued.v (2 * locGram Q v γ k k) :=
    valued_dot_gram_le γ hT hk hd hzsupp hz1 hz1
  have hyy : qbil Q Fv y y = locGram Q v γ k k := by
    have h := qbil_orth Q Fv σ (basisVec γ k) (basisVec γ k)
    rw [qbil_basisVec] at h
    exact h
  have hyk : qbil Q Fv y (basisVec γ k) = s * locGram Q v γ k k := by
    rw [← hyd, qbil_vec_basisVec γ hk]
  have hquad : locGram Q v γ k k = z ⬝ᵥ (locGram Q v γ *ᵥ z) + locGram Q v γ k k * s ^ 2 := by
    rw [← dot_gram_split γ hk z hzk s, ← hdz, ← qbil_mulVec_locGram, hyd]
    exact hyy.symm
  have hrel : locGram Q v γ k k * (1 - s ^ 2) = z ⬝ᵥ (locGram Q v γ *ᵥ z) := by
    linear_combination hquad
  have hGv0 : 0 < Valued.v (locGram Q v γ k k) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hGkk)
  have hbnd : Valued.v (1 - s ^ 2) ≤ Valued.v (2 : Fv) := by
    have h1 : Valued.v (locGram Q v γ k k) * Valued.v (1 - s ^ 2) ≤
        Valued.v (locGram Q v γ k k) * Valued.v (2 : Fv) := by
      rw [← map_mul, hrel, mul_comm (Valued.v (locGram Q v γ k k)), ← map_mul]; exact hzz
    exact le_of_mul_le_mul_left h1 hGv0
  obtain ⟨ε, hε, hεv⟩ := exists_sign_of_sq h2 hs1 hbnd
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> ring
  have hεv1 : Valued.v ε = 1 := by rcases hε with rfl | rfl <;> simp
  set bk := basisVec γ k with hbk
  set w := y - ε • bk with hw
  have hbky : qbil Q Fv bk y = s * locGram Q v γ k k := by rw [qbil_comm]; exact hyk
  have hbkbk : qbil Q Fv bk bk = locGram Q v γ k k := qbil_basisVec γ k k
  have hqww : qbil Q Fv w w = 2 * locGram Q v γ k k * (1 - ε * s) := by
    rw [hw]
    simp only [qbil_sub_left, qbil_sub_right, qbil_smul_left, qbil_smul_right']
    rw [hyy, hyk, hbky, hbkbk]
    linear_combination (locGram Q v γ k k) * hεε
  have hQw : Q.evalIn Fv w = locGram Q v γ k k * (1 - ε * s) := by
    have h := two_mul_evalIn_eq Q Fv w
    rw [hqww] at h
    apply mul_left_cancel₀ (two_ne_zero : (2 : Fv) ≠ 0)
    linear_combination h
  have hvw : Valued.v (Q.evalIn Fv w) = Valued.v (2 * locGram Q v γ k k) := by
    rw [hQw, map_mul, hεv, map_mul, mul_comm]
  have hw0 : Q.evalIn Fv w ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvw
    have : Valued.v (2 * locGram Q v γ k k) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr (mul_ne_zero two_ne_zero hGkk)
    exact this hvw.symm
  have hεbk : ε • bk ∈ loc v L.1 := by
    rcases hε with rfl | rfl
    · simpa using hbkM
    · simpa using (loc v L.1).neg_mem hbkM
  have hwM : w ∈ loc v L.1 := (loc v L.1).sub_mem hyM hεbk
  have hwt : ∀ t ∈ T, qbil Q Fv w (basisVec γ t) = 0 := by
    intro t ht
    rw [hw, qbil_sub_left, qbil_smul_left, hbt t ht, qbil_basisVec γ k t, hT t ht k (fun h => hkT (h ▸ ht))]
    ring
  have hroot : IsRootVector Q L v w := by
    refine ⟨hw0, ?_⟩
    show locAct v (symm Q Fv w : GL (Fin n) Fv) (loc v L.1) = loc v L.1
    refine locAct_symm_eq hwM hw0 fun x hx => ?_
    rw [hγ, mem_locAct] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    have hc1 := mem_std_iff.mp hc
    have hGc : (locGram Q v γ *ᵥ c) k = locGram Q v γ k k * c k := by
      have hk' : ∀ m, m ≠ k → locGram Q v γ k m = 0 := fun m hm => by
        rw [locGram_symm']; exact hk m hm
      unfold mulVec dotProduct
      rw [Finset.sum_eq_single k]
      · intro i _ hi; show locGram Q v γ k i * c i = 0; rw [hk' i hi, zero_mul]
      · simp
    have hq1 : qbil Q Fv y (γ.val *ᵥ c) =
        z ⬝ᵥ (locGram Q v γ *ᵥ c) + s * (locGram Q v γ k k * c k) := by
      rw [← hyd, qbil_mulVec_locGram, hdz, add_dotProduct, single_dotProduct, hGc]
    have hq2 : qbil Q Fv bk (γ.val *ᵥ c) = locGram Q v γ k k * c k := by
      rw [hbk]
      show qbil Q Fv (γ.val *ᵥ Pi.single k 1) (γ.val *ᵥ c) = _
      rw [qbil_mulVec_locGram, single_dotProduct, one_mul, hGc]
    rw [hw, qbil_sub_left, qbil_smul_left, hq1, hq2, ← hw, hvw,
      show z ⬝ᵥ (locGram Q v γ *ᵥ c) + s * (locGram Q v γ k k * c k) - ε * (locGram Q v γ k k * c k) =
        z ⬝ᵥ (locGram Q v γ *ᵥ c) + (s - ε) * (locGram Q v γ k k * c k) by ring]
    refine Valuation.map_add_le _ (valued_dot_gram_le γ hT hk hd hzsupp hz1 hc1) ?_
    have hse : s - ε = -(ε * (1 - ε * s)) := by linear_combination (-s) * hεε
    rw [map_mul, map_mul, hse, Valuation.map_neg, map_mul, hεv1, hεv, one_mul]
    calc Valued.v (2 : Fv) * (Valued.v (locGram Q v γ k k) * Valued.v (c k))
        ≤ Valued.v (2 : Fv) * (Valued.v (locGram Q v γ k k) * 1) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl (hc1 k))
      _ = Valued.v (2 * locGram Q v γ k k) := by rw [map_mul, mul_one]
  have hτy : (symm Q Fv w : GL (Fin n) Fv).val *ᵥ y = ε • bk := by
    have hwy : qbil Q Fv w y = Q.evalIn Fv w := by
      rw [hQw, hw, qbil_sub_left, qbil_smul_left, hyy, hbky]
      ring
    rw [symm_mulVec_bil Q Fv hw0, hwy, div_self hw0, one_smul, hw]
    abel
  have hτt : ∀ t ∈ T, (symm Q Fv w : GL (Fin n) Fv).val *ᵥ basisVec γ t = basisVec γ t :=
    fun t ht => symm_fix Q Fv (hwt t ht)
  have hσ1M : symm Q Fv w * σ ∈ locStabV Q v L := mul_mem hroot.2 hσ
  have hσ1t : ∀ t ∈ T, ((symm Q Fv w * σ : orthGroup Q Fv) : GL (Fin n) Fv).val *ᵥ basisVec γ t =
      basisVec γ t := fun t ht => by
    rw [orthGroup_mul_mulVec, hfix t ht]; exact hτt t ht
  have hσ1k : ((symm Q Fv w * σ : orthGroup Q Fv) : GL (Fin n) Fv).val *ᵥ bk = ε • bk := by
    rw [orthGroup_mul_mulVec]; exact hτy
  have hσeq : σ = symm Q Fv w * (symm Q Fv w * σ) := by rw [← mul_assoc, symm_mul_self, one_mul]
  have hbkroot : IsRootVector Q L v bk := isRootVector_basis_of_orth γ hγ k hk hGkk
  have hbkt : ∀ t ∈ T, qbil Q Fv bk (basisVec γ t) = 0 := fun t ht => by
    rw [hbk, qbil_basisVec]; exact hT t ht k (fun h => hkT (h ▸ ht))

  rcases hε with rfl | rfl
  · refine ⟨[w], symm Q Fv w * σ, ?_, ?_, hσ1M, ?_⟩
    · intro u hu
      rw [List.mem_singleton] at hu
      subst hu
      exact ⟨hroot, hwt⟩
    · have : symmProd Q Fv [w] = symm Q Fv w := by simp [symmProd]
      rw [this]; exact hσeq
    · intro t ht
      rcases Finset.mem_insert.mp ht with h | ht
      · rw [h]; exact (by rw [← hbk, hσ1k, one_smul])
      · exact hσ1t t ht
  · have hQbk : Q.evalIn Fv bk ≠ 0 := hbkroot.1
    have hσ2M : symm Q Fv bk * (symm Q Fv w * σ) ∈ locStabV Q v L := mul_mem hbkroot.2 hσ1M
    refine ⟨[w, bk], symm Q Fv bk * (symm Q Fv w * σ), ?_, ?_, hσ2M, ?_⟩
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact ⟨hroot, hwt⟩
      · exact ⟨hbkroot, hbkt⟩
    · have : symm Q Fv w * σ = symm Q Fv bk * (symm Q Fv bk * (symm Q Fv w * σ)) := by
        rw [← mul_assoc, symm_mul_self, one_mul]
      have e2 : symmProd Q Fv [w, bk] = symm Q Fv w * symm Q Fv bk := by simp [symmProd]
      rw [e2, mul_assoc, ← this]
      exact hσeq
    · intro t ht
      rcases Finset.mem_insert.mp ht with h | ht
      · rw [h, ← hbk, orthGroup_mul_mulVec, hσ1k, neg_smul, one_smul]
        exact symm_neg_self Q Fv hQbk
      · rw [orthGroup_mul_mulVec, hσ1t t ht]; exact symm_fix Q Fv (hbkt t ht)

/-- **The peeling step for `FixTheta`** (the analogue of `fixGenerated_peel`): under the same hypotheses on
$T$, $k$ ($b_t$ and $b_k$ orthogonal to all other basis vectors, $\lvert G_{ii'}\rvert \le \lvert 2G_{kk}\rvert$ for
$i, i' \notin T \cup \{k\}$), `FixTheta` for $T \cup \{k\}$ implies it for $T$. *Proof.* By
`exists_peel_reflections`, $\sigma = \tau_{x_1}\cdots\tau_{x_r}\sigma'$ with $\sigma'$ fixing $T \cup \{k\}$; the
determinant and the spinor norm are multiplicative (`spinorNormHom`). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (remark after Thm. 18: peeling an orthogonal basis vector off, spinor-norm version, p = 2)"]
theorem fixTheta_peel (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) (T : Finset (Fin n)) (k : Fin n) (hkT : k ∉ T)
    (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0)
    (hk : ∀ m, m ≠ k → locGram Q v γ m k = 0)
    (hd : ∀ i i', i ∉ insert k T → i' ∉ insert k T →
      Valued.v (locGram Q v γ i i') ≤ Valued.v (2 * locGram Q v γ k k))
    (hgen : FixTheta Q L v γ (insert k T)) : FixTheta Q L v γ T := by
  intro σ hσ hfix
  obtain ⟨l, σ', hl, rfl, hσ', hfix'⟩ := exists_peel_reflections hQ h2 γ hγ T k hkT hT hk hd σ hσ hfix
  obtain ⟨xs, hxs, hdet, hθ⟩ := hgen σ' hσ' hfix'
  have hl0 : ∀ x ∈ l, Q.evalIn Fv x ≠ 0 := fun x hx => (hl x hx).1.1
  have hxs0 : ∀ x ∈ xs, Q.evalIn Fv x ≠ 0 := fun x hx => (hxs x hx).1
  refine ⟨l ++ xs, ?_, ?_, ?_⟩
  · intro u hu
    rcases List.mem_append.mp hu with h | h
    · exact (hl u h).1
    · exact hxs u h
  · rw [orthGroup_det_mul, det_symmProd_pow l hl0, hdet, List.length_append, pow_add]
  · have h1 : spinorNorm Q Fv (symmProd Q Fv l * σ') = spinorNorm Q Fv (symmProd Q Fv l) * spinorNorm Q Fv σ' :=
      (spinorNormHom Q Fv hQ).map_mul _ _
    rw [h1, hθ, spinorNorm_symmProd Q Fv hQ l hl0, valProd_append',
      sqClassOf_mul (valProd_ne_zero Q Fv hl0) (valProd_ne_zero Q Fv hxs0)]

end Theta


/-! ### Blocks of the complement of $T$: Lean-level restriction lemmas -/

section Block

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

/-- **The enumeration of the complement of $T$**: a bijection $\mathrm{Fin}\,m \simeq \{i \notin T\}$,
$m = \lvert\{i \notin T\}\rvert$, used to index the block of a matrix on the complement of $T$. -/
def compEquiv (T : Finset (Fin n)) : Fin (Fintype.card {i // i ∉ T}) ≃ {i // i ∉ T} :=
  (Fintype.equivFin {i // i ∉ T}).symm

/-- **The block of $A$ on the complement of $T$**: the $m \times m$ matrix
$(A_{\iota(a)\iota(b)})_{a, b}$, where $\iota(a) \in \{0, \dots, n-1\} \setminus T$ is the $a$-th index not in $T$
(`compEquiv`), $m = \lvert\{i \notin T\}\rvert$. For $A = cG$ this is the Gram matrix $cG$ of the basis vectors
$b_i$, $i \notin T$. -/
def compBlock {K : Type*} (T : Finset (Fin n)) (A : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin (Fintype.card {i // i ∉ T})) (Fin (Fintype.card {i // i ∉ T})) K :=
  A.submatrix (blkIdx (compEquiv T)) (blkIdx (compEquiv T))

/-- **The matrix of $\sigma$ in the basis $b = \gamma e$**: $S' = \gamma^{-1}S\gamma$. -/
abbrev conjMat {Q : QuadForm ℚ n} (γ : GL (Fin n) Fv) (σ : orthGroup Q Fv) : Matrix (Fin n) (Fin n) Fv :=
  (γ⁻¹ : GL (Fin n) Fv).val * mat Q Fv σ * γ.val

theorem conj_colFix (γ : GL (Fin n) Fv) {σ : orthGroup Q Fv} {t : Fin n}
    (hfix : (σ : GL (Fin n) Fv).val *ᵥ basisVec γ t = basisVec γ t) (i : Fin n) :
    conjMat γ σ i t = if i = t then 1 else 0 := by
  have hgig : (γ⁻¹ : GL (Fin n) Fv).val * γ.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h : conjMat γ σ *ᵥ Pi.single t 1 = Pi.single t 1 := by
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    change (γ⁻¹ : GL (Fin n) Fv).val *ᵥ ((σ : GL (Fin n) Fv).val *ᵥ basisVec γ t) = _
    rw [hfix, basisVec, mulVec_mulVec, hgig, one_mulVec]
  have := congrFun h i
  rw [mulVec_single_one_apply] at this
  rw [this, Pi.single_apply]

theorem det_conj (γ : GL (Fin n) Fv) (M : Matrix (Fin n) (Fin n) Fv) :
    ((γ⁻¹ : GL (Fin n) Fv).val * M * γ.val).det = M.det := by
  have hgig : (γ⁻¹ : GL (Fin n) Fv).val * γ.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h := congrArg Matrix.det hgig
  rw [det_mul, det_one] at h
  calc ((γ⁻¹ : GL (Fin n) Fv).val * M * γ.val).det
      = M.det * ((γ⁻¹ : GL (Fin n) Fv).val.det * γ.val.det) := by rw [det_mul, det_mul]; ring
    _ = M.det := by rw [h, mul_one]

/-- **Restriction lemma, part 1** (the data of $\sigma$ on the block). Let $T$ be a set of basis indices with $b_t$
orthogonal to all other basis vectors, and $\sigma \in O(L_2)$ with $\sigma b_t = b_t$ ($t \in T$). Then
$S' = \gamma^{-1}S\gamma$ is integral, $S'^{\mathsf T}GS' = G$ (`conj_integral_orth`), $S'e_t = e_t$ for $t \in T$,
and the rows $t \in T$ of $S'$ vanish off the column $t$ ($S'_{ta} = 0$ for $a \notin T$, because $S'$ preserves
the orthogonal complement of the $b_t$). -/
theorem conj_block_data (hQ : Q.Nondegenerate) (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v))
    {T : Finset (Fin n)} (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) {σ : orthGroup Q Fv}
    (hσ : σ ∈ locStabV Q v L)
    (hfix : ∀ t ∈ T, (σ : GL (Fin n) Fv).val *ᵥ basisVec γ t = basisVec γ t) :
    (∀ i j, Valued.v (conjMat γ σ i j) ≤ 1) ∧
      (conjMat γ σ)ᵀ * locGram Q v γ * conjMat γ σ = locGram Q v γ ∧
      (∀ t ∈ T, ∀ i, conjMat γ σ i t = if i = t then 1 else 0) ∧
      (∀ t ∈ T, ∀ a, a ∉ T → conjMat γ σ t a = 0) := by
  obtain ⟨hS', hS'G⟩ := conj_integral_orth γ hγ hσ
  have F1 : ∀ t ∈ T, ∀ i, conjMat γ σ i t = if i = t then 1 else 0 :=
    fun t ht => conj_colFix γ (hfix t ht)
  refine ⟨hS', hS'G, F1, fun t ht a ha => ?_⟩
  exact blk_rowZero (locGram_transpose γ) hT (fun t ht => locGram_diag_ne_zero hQ γ (hT t ht)) hS'G F1 ht ha

/-- **Restriction lemma, part 2** (the block of $\sigma$ and its Wall frame). In the situation of
`conj_block_data`, with $A = cG$ for any scalar $c$ and $S_K$, $A_K$ the blocks on the complement of $T$
(`compBlock`): $S_K$ is integral, $S_K^{\mathsf T}A_KS_K = A_K$, $\det S_K = \det S'$, and for a Wall frame $(P, R)$
of $S'$ the row-restricted pair $(P_K, R_K)$ is a Wall frame of $S_K$ with $P_K^{\mathsf T}A_KR_K = P^{\mathsf T}AR$. -/
theorem restrict_block (hQ : Q.Nondegenerate) (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v))
    {T : Finset (Fin n)} (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) {σ : orthGroup Q Fv}
    (hσ : σ ∈ locStabV Q v L)
    (hfix : ∀ t ∈ T, (σ : GL (Fin n) Fv).val *ᵥ basisVec γ t = basisVec γ t) (c : Fv) :
    (∀ a b, Valued.v (compBlock T (conjMat γ σ) a b) ≤ 1) ∧
      (compBlock T (conjMat γ σ))ᵀ * compBlock T (c • locGram Q v γ) * compBlock T (conjMat γ σ) =
        compBlock T (c • locGram Q v γ) ∧
      (compBlock T (conjMat γ σ)).det = (conjMat γ σ).det ∧
      ∀ {m' : ℕ} {P R : Matrix (Fin n) (Fin m') Fv}, IsWallFrame Fv (conjMat γ σ) P R →
        IsWallFrame Fv (compBlock T (conjMat γ σ)) (P.submatrix (blkIdx (compEquiv T)) id)
          (R.submatrix (blkIdx (compEquiv T)) id) ∧
        (P.submatrix (blkIdx (compEquiv T)) id)ᵀ * compBlock T (c • locGram Q v γ) *
            R.submatrix (blkIdx (compEquiv T)) id = Pᵀ * (c • locGram Q v γ) * R := by
  obtain ⟨hS', hSG, F1, F2⟩ := conj_block_data hQ γ hγ hT hσ hfix
  have hSA : (conjMat γ σ)ᵀ * (c • locGram Q v γ) * conjMat γ σ = c • locGram Q v γ := by
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [hSG]
  have hAT : ∀ t ∈ T, ∀ i, i ∉ T → (c • locGram Q v γ) i t = 0 := fun t ht i hi => by
    simp [hT t ht i (fun h => hi (h ▸ ht))]
  refine ⟨fun a b => hS' _ _, blk_orth (compEquiv T) hSA F2, blk_det (compEquiv T) F1 F2, ?_⟩
  intro m' P R hf
  exact ⟨blk_frame (compEquiv T) F1 F2 hf, blk_gram (compEquiv T) F1 F2 hAT hf⟩

/-- **Root vectors in the span of the block** (`exists_rootVector_of_unit_entry`, relative version): let $T$ be a set
of basis indices with $b_t$ orthogonal to the other basis vectors, $c \ne 0$ such that $cG_{ij}$ is integral and
$cG_{ii}/2$ integral for $i, j \notin T$, and $i_0, j \notin T$ with $cG_{i_0j}$ a unit. Then for every unit $w$
there is a $2$-adic root vector $x$ with $Q(x) = c^{-1}w$ that is orthogonal to all $b_t$, $t \in T$ (it lies in
the span of $b_{i_0}, b_j$). (Unlike `exists_rootVector_of_unit_entry`, no integrality is needed for the rows and
columns of $T$: they are orthogonal to the block.) -/
theorem exists_rootVector_block (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) {T : Finset (Fin n)}
    (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) {c : Fv} (hc : c ≠ 0)
    (hint : ∀ i j, i ∉ T → j ∉ T → Valued.v (c * locGram Q v γ i j) ≤ 1)
    (heven : ∀ i, i ∉ T → Valued.v (c * locGram Q v γ i i / 2) ≤ 1) (i0 j : Fin n) (hi0 : i0 ∉ T)
    (hjT : j ∉ T) (hj : Valued.v (c * locGram Q v γ i0 j) = 1) {w : Fv} (hw : Valued.v w = 1) :
    ∃ x, IsRootVector Q L v x ∧ Q.evalIn Fv x = c⁻¹ * w ∧ ∀ t ∈ T, qbil Q Fv x (basisVec γ t) = 0 := by
  set G := locGram Q v γ
  have hv2 : Valued.v (2 : Fv) = exp (-1 : ℤ) := valued_two_dyadic v h2
  have hji0 : j ≠ i0 := by
    rintro rfl
    have h := heven j hi0
    have e : c * G j j = 2 * (c * G j j / 2) := by field_simp
    rw [e, map_mul, hv2] at hj
    have : exp (-1 : ℤ) * Valued.v (c * G j j / 2) ≤ exp (-1 : ℤ) :=
      (mul_le_mul' le_rfl h).trans_eq (mul_one _)
    rw [hj] at this
    exact absurd this (by rw [← exp_zero, exp_le_exp]; omega)
  set β := c * G i0 j with hβ
  have hβ0 : β ≠ 0 := fun h => by rw [h, map_zero] at hj; exact zero_ne_one hj
  have hα1 : Valued.v (c * G i0 i0 / 2) ≤ 1 := heven i0 hi0
  have hδ1 : Valued.v (c * G j j / 2 / β ^ 2) ≤ 1 := by
    rw [map_div₀, map_pow, hj, one_pow, div_one]; exact heven j hjT
  have hw0 : IsUnit (toO v w hw.le) := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hw
  obtain ⟨s, t', hst⟩ := exists_binary_value h2 (toO v _ hα1) (toO v _ hδ1) _ hw0
  have hst' : c * G i0 i0 / 2 * (s : Fv) ^ 2 + (s : Fv) * (t' : Fv) + c * G j j / 2 / β ^ 2 * (t' : Fv) ^ 2 = w := by
    have := congrArg (fun z : 𝔬 => (z : Fv)) hst
    push_cast at this
    exact this
  set t : Fv := (t' : Fv) / β
  have ht1 : Valued.v t ≤ 1 := by rw [map_div₀, hj, div_one]; exact vle_one t'
  set d : Fin n → Fv := Pi.single i0 (s : Fv) + Pi.single j t with hd
  have hGd : ∀ m, (G *ᵥ d) m = G m i0 * s + G m j * t := by
    intro m
    simp [hd, Matrix.mulVec_add, Matrix.mulVec_single]
    ring
  have hdot : ∀ e : Fin n → Fv, d ⬝ᵥ e = s * e i0 + t * e j := fun e => by
    rw [hd, add_dotProduct, single_dotProduct, single_dotProduct]
  have hGsym : ∀ a b, G a b = G b a := locGram_symm' γ
  have hji : G j i0 = G i0 j := hGsym j i0
  have hdstd : d ∈ std v := (std v).add_mem (single_mem_std i0 (vle_one s)) (single_mem_std j ht1)
  have hQx : Q.evalIn Fv (γ.val *ᵥ d) = c⁻¹ * w := by
    have h2Q := two_mul_evalIn_locGram (Q := Q) (v := v) γ d
    rw [hdot, hGd, hGd, hji] at h2Q
    have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
    have hQd : Q.evalIn Fv (γ.val *ᵥ d) =
        ((s : Fv) * (G i0 i0 * s + G i0 j * t) + t * (G i0 j * s + G j j * t)) / 2 := by
      rw [← h2Q]; field_simp
    have hdt : t * β = t' := by simp only [t]; field_simp
    have hG0 : G i0 j ≠ 0 := fun h => hβ0 (by rw [hβ, h, mul_zero])
    rw [hQd, ← hst', ← hdt, hβ]
    field_simp
    ring
  have hcw : c⁻¹ * w ≠ 0 := mul_ne_zero (inv_ne_zero hc) (fun h => by rw [h, map_zero] at hw; exact zero_ne_one hw)
  have hx0 : Q.evalIn Fv (γ.val *ᵥ d) ≠ 0 := by rw [hQx]; exact hcw
  refine ⟨γ.val *ᵥ d, ⟨hx0, symm_mem_of_gram L γ hγ hdstd hx0 fun m => ?_⟩, hQx, ?_⟩
  · rw [hQx, map_mul, hw, mul_one, hGd]
    have hvc : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
    by_cases hmT : m ∈ T
    · have h1 : G m i0 = 0 := by rw [hGsym]; exact hT m hmT i0 (fun h => hi0 (h ▸ hmT))
      have h2' : G m j = 0 := by rw [hGsym]; exact hT m hmT j (fun h => hjT (h ▸ hmT))
      rw [h1, h2']
      simp
    · have key : Valued.v (c * (G m i0 * s + G m j * t)) ≤ 1 := by
        rw [show c * (G m i0 * s + G m j * t) = (c * G m i0) * s + (c * G m j) * t by ring]
        refine Valuation.map_add_le _ ?_ ?_
        · rw [map_mul]; exact mul_le_one' (hint m i0 hmT hi0) (vle_one s)
        · rw [map_mul]; exact mul_le_one' (hint m j hmT hjT) ht1
      rw [map_mul] at key
      rw [map_inv₀]
      calc Valued.v (G m i0 * ↑s + G m j * t)
          = (Valued.v c)⁻¹ * (Valued.v c * Valued.v (G m i0 * ↑s + G m j * t)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hvc, one_mul]
        _ ≤ (Valued.v c)⁻¹ * 1 := mul_le_mul' le_rfl key
        _ = (Valued.v c)⁻¹ := mul_one _
  · intro tt ht
    rw [qbil_vec_basisVec γ (hT tt ht)]
    have hti0 : tt ≠ i0 := fun h => hi0 (h ▸ ht)
    have htj : tt ≠ j := fun h => hjT (h ▸ ht)
    have : d tt = 0 := by simp [hd, hti0, htj]
    rw [this, zero_mul]

end Block


/-! ### The block base cases -/

section BaseCases

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

/-- **The common tail of the block base cases**: suppose that for some $c \ne 0$

* (`hsq`) for every proper $\sigma \in O(L_2)$ fixing the $b_t$, $t \in T$, and every Wall frame $(P, R)$ of
  $S' = \gamma^{-1}\sigma\gamma$ the valuation of $\det(P^{\mathsf T}(cG)R)$ is a square $\delta^2$ (the output of the
  core lemmas `exists_sq_valued_wallDet'`, `exists_sq_valued_wallDet_glue'` on the block), and
* (`hunit`) for every unit $w$ there is a $2$-adic root vector $x$ with $Q(x) = c^{-1}w$ orthogonal to all $b_t$,
  $t \in T$.

Then `FixTheta Q L v γ T` holds. *Proof.* For $\sigma$ proper, Wall's formula gives $\theta(\sigma) = d\,F_2^{\times 2}$
with $\lvert d\rvert = e^{2k}$ (even order, as in `even_log_of_scaledEvenUnimodular`), and
$u = 2^{2k}d$ is a unit, so $\theta(\sigma) = uF_2^{\times 2} = Q(x)Q(y)F_2^{\times 2}$ for root vectors $x, y$ of norms
$c^{-1}u, c^{-1}$: a list of length $2$. For $\sigma$ improper, multiply by the reflection in a root vector $x_0$ of
norm $c^{-1}$ orthogonal to the $b_t$ (this fixes the $b_t$), which makes it proper. -/
theorem fixTheta_of_wallSq (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (T : Finset (Fin n)) {c : Fv} (hc : c ≠ 0)
    (hsq : ∀ σ : orthGroup Q Fv, σ ∈ locStabV Q v L →
      (∀ t ∈ T, (σ : GL (Fin n) Fv).val *ᵥ basisVec γ t = basisVec γ t) →
      ((σ : GL (Fin n) Fv).val).det = 1 → ∀ {m' : ℕ} {P R : Matrix (Fin n) (Fin m') Fv},
        IsWallFrame Fv (conjMat γ σ) P R →
          ∃ δ : ℤᵐ⁰, Valued.v (Pᵀ * (c • locGram Q v γ) * R).det = δ ^ 2)
    (hunit : ∀ w : Fv, Valued.v w = 1 → ∃ x, IsRootVector Q L v x ∧ Q.evalIn Fv x = c⁻¹ * w ∧
      ∀ t ∈ T, qbil Q Fv x (basisVec γ t) = 0) : FixTheta Q L v γ T := by
  have hproper : ∀ σ : orthGroup Q Fv, σ ∈ locStabV Q v L →
      (∀ t ∈ T, (σ : GL (Fin n) Fv).val *ᵥ basisVec γ t = basisVec γ t) →
      ((σ : GL (Fin n) Fv).val).det = 1 →
      ∃ xs : List (Fin n → Fv), (∀ x ∈ xs, IsRootVector Q L v x) ∧ xs.length = 2 ∧
        spinorNorm Q Fv σ = sqClassOf (valProd Q Fv xs) := by
    intro σ hσ hfix hdet
    obtain ⟨m', P, R, hf⟩ := exists_wallFrame (conjMat γ σ)
    obtain ⟨hθ, hne, hdetm⟩ := spinorNorm_eq_wallDet_conj hQ γ σ hf
    obtain ⟨δ, hδ⟩ := hsq σ hσ hfix hdet hf
    have hm : Even m' := by
      have h1 : (mat Q Fv σ).det = 1 := hdet
      rw [h1] at hdetm
      exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : Fv) ≠ 1)).mp hdetm.symm
    obtain ⟨m'', rfl⟩ := hm
    set d := (Pᵀ * locGram Q v γ * R).det with hd
    have hAd : (Pᵀ * (c • locGram Q v γ) * R).det = c ^ (m'' + m'') * d := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, det_smul, Fintype.card_fin, d]
    have hvc : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
    have hvd : Valued.v d = (δ * (Valued.v c ^ m'')⁻¹) ^ 2 := by
      have h := hδ
      rw [hAd, map_mul, map_pow] at h
      have hcm : Valued.v c ^ (m'' + m'') ≠ 0 := pow_ne_zero _ hvc
      rw [mul_pow, inv_pow, ← h, ← pow_mul, show m'' * 2 = m'' + m'' by ring]
      field_simp
    set δ' := δ * (Valued.v c ^ m'')⁻¹ with hδ'
    have hδ'0 : δ' ≠ 0 := by
      intro h0; rw [h0, zero_pow two_ne_zero, Valuation.zero_iff] at hvd; exact hne hvd
    obtain ⟨k, hk⟩ : ∃ k : ℤ, δ' = exp k := ⟨log δ', (exp_log hδ'0).symm⟩
    have hvdk : Valued.v d = exp (2 * k) := by
      rw [hvd, hk, ← WithZero.exp_nsmul, two_nsmul, two_mul]
    have h2k : ((2 : Fv) ^ k) ≠ 0 := zpow_ne_zero _ two_ne_zero
    have hu : Valued.v (((2 : Fv) ^ k) ^ 2 * d) = 1 := by
      rw [map_mul, map_pow, valued_two_zpow h2, hvdk, ← WithZero.exp_nsmul, ← exp_add, ← exp_zero]
      congr 1
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      ring
    obtain ⟨x, hxr, hx, -⟩ := hunit _ hu
    obtain ⟨y, hyr, hy, -⟩ := hunit 1 (map_one _)
    refine ⟨[x, y], ?_, rfl, ?_⟩
    · intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      exacts [hxr, hyr]
    · rw [hθ]
      have hu0 : ((2 : Fv) ^ k) ^ 2 * d ≠ 0 := mul_ne_zero (pow_ne_zero 2 h2k) hne
      have e : valProd Q Fv [x, y] = c⁻¹ ^ 2 * (((2 : Fv) ^ k) ^ 2 * d) := by
        simp only [valProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hx, hy]
        ring
      rw [e, sqClassOf_sq_mul (inv_ne_zero hc) hu0, sqClassOf_sq_mul h2k hne]
  intro σ hσ hfix
  rcases Tamagawa.det_eq_one_or_neg_one Q hQ σ with h | h
  · obtain ⟨xs, hxr, hlen, hθ⟩ := hproper σ hσ hfix h
    exact ⟨xs, hxr, by rw [h, hlen]; norm_num, hθ⟩
  · obtain ⟨x0, hx0r, hx0, hx0t⟩ := hunit 1 (map_one _)
    have hσ1M : symm Q Fv x0 * σ ∈ locStabV Q v L := mul_mem hx0r.2 hσ
    have hfix1 : ∀ t ∈ T, ((symm Q Fv x0 * σ : orthGroup Q Fv) : GL (Fin n) Fv).val *ᵥ basisVec γ t =
        basisVec γ t := fun t ht => by
      rw [orthGroup_mul_mulVec, hfix t ht]; exact symm_fix Q Fv (hx0t t ht)
    have hdet1 : ((symm Q Fv x0 * σ : orthGroup Q Fv) : GL (Fin n) Fv).val.det = 1 := by
      rw [orthGroup_det_mul, symm_det Q Fv hx0r.1, h]; norm_num
    obtain ⟨xs, hxr, hlen, hθ⟩ := hproper _ hσ1M hfix1 hdet1
    have hσeq : σ = symm Q Fv x0 * (symm Q Fv x0 * σ) := by rw [← mul_assoc, symm_mul_self, one_mul]
    have hxs0 : ∀ z ∈ xs, Q.evalIn Fv z ≠ 0 := fun z hz => (hxr z hz).1
    refine ⟨x0 :: xs, ?_, ?_, ?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hx0r
      · exact hxr z hz
    · rw [h, List.length_cons, hlen]; norm_num
    · have h1 : spinorNorm Q Fv σ =
          spinorNorm Q Fv (symm Q Fv x0) * spinorNorm Q Fv (symm Q Fv x0 * σ) :=
        calc spinorNorm Q Fv σ = spinorNorm Q Fv (symm Q Fv x0 * (symm Q Fv x0 * σ)) := by rw [← hσeq]
          _ = _ := (spinorNormHom Q Fv hQ).map_mul _ _
      have hv : valProd Q Fv (x0 :: xs) = Q.evalIn Fv x0 * valProd Q Fv xs := by simp [valProd]
      rw [h1, hθ, spinorNorm_symm Q Fv hQ hx0r.1, hv, sqClassOf_mul hx0r.1 (valProd_ne_zero Q Fv hxs0)]

/-- **The Wall-determinant squares for a scaled even unimodular block** (the hypothesis `hsq` of
`fixTheta_of_wallSq`): if $cG_{ij}$ and $cG_{ii}/2$ are integral on the complement of $T$ and the block
$A_K = (cG_{ij})_{i, j \notin T}$ has $\lvert\det A_K\rvert = 1$, every Wall frame $(P, R)$ of $S' = \gamma^{-1}\sigma\gamma$
($\sigma$ fixing the $b_t$, $t \in T$) has $\lvert\det(P^{\mathsf T}(cG)R)\rvert$ a square. (The restriction
`restrict_block` and the core lemma `exists_sq_valued_wallDet'` for $A_K$.) -/
theorem wallSq_of_block_even (hQ : Q.Nondegenerate) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) {T : Finset (Fin n)}
    (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) {c : Fv}
    (hint : ∀ i j, i ∉ T → j ∉ T → Valued.v (c * locGram Q v γ i j) ≤ 1)
    (heven : ∀ i, i ∉ T → Valued.v (c * locGram Q v γ i i / 2) ≤ 1)
    (hdet : Valued.v (compBlock T (c • locGram Q v γ)).det = 1) :
    ∀ σ : orthGroup Q Fv, σ ∈ locStabV Q v L →
      (∀ t ∈ T, (σ : GL (Fin n) Fv).val *ᵥ basisVec γ t = basisVec γ t) →
      ((σ : GL (Fin n) Fv).val).det = 1 → ∀ {m' : ℕ} {P R : Matrix (Fin n) (Fin m') Fv},
        IsWallFrame Fv (conjMat γ σ) P R →
          ∃ δ : ℤᵐ⁰, Valued.v (Pᵀ * (c • locGram Q v γ) * R).det = δ ^ 2 := by
  intro σ hσ hfix _ m' P R hf
  obtain ⟨hS', horth, -, hframe⟩ := restrict_block hQ γ hγ hT hσ hfix c
  obtain ⟨hf', hgram⟩ := hframe hf
  have hAKsym : (compBlock T (c • locGram Q v γ))ᵀ = compBlock T (c • locGram Q v γ) := by
    simp only [compBlock, transpose_submatrix, transpose_smul, locGram_transpose]
  obtain ⟨δ, hδ⟩ := exists_sq_valued_wallDet' (compBlock T (c • locGram Q v γ)) hAKsym
    (fun a b => by simpa [compBlock] using hint _ _ (blkIdx_notMem (compEquiv T) a) (blkIdx_notMem (compEquiv T) b))
    hdet
    (fun a => by simpa [compBlock] using heven _ (blkIdx_notMem (compEquiv T) a))
    (compBlock T (conjMat γ σ)) hS' horth hf'
  exact ⟨δ, by rw [← hgram]; exact hδ⟩

/-- **Block base case: a scaled even unimodular block.** Let $T$ be a set of basis indices with $b_t$ orthogonal to
all other basis vectors ($G_{mt} = 0$ for $m \ne t$), $K$ the complement of $T$ with $m = \lvert K\rvert \ge 2$, and
$c \ne 0$ such that on $K$ the entries $cG_{ij}$ are integral, the diagonal entries $cG_{ii}/2$ are integral and the
block $A_K = (cG_{ij})_{i, j \in K}$ (`compBlock`) has $\lvert\det A_K\rvert = 1$ (so $A_K$ is an even unimodular
lattice: the complement of $T$ is $2^k E$ with $E$ even unimodular). Then `FixTheta Q L v γ T` holds: every
$\sigma \in O(L_2)$ fixing the $b_t$, $t \in T$, has $\det\sigma = (-1)^r$ and $\theta(\sigma)$ equal to the class of
a product of $r$ norms of $2$-adic root vectors ($r = 2$ or $3$). *Proof.* The block of $\sigma$ is an integral
automorphism of $A_K$ (`restrict_block`), so the core lemma `exists_sq_valued_wallDet'` shows that $\theta(\sigma)$
has even order; every unit class is a product of two root-vector norms in the span of $b_i$, $i \in K$
(`exists_rootVector_block`); see `fixTheta_of_wallSq`. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2: relative spinor norm for a scaled even unimodular remainder block)"]
theorem fixTheta_of_block_scaledEvenUnimodular (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) (T : Finset (Fin n))
    (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) {c : Fv} (hc : c ≠ 0)
    (hm : 2 ≤ Fintype.card {i // i ∉ T})
    (hint : ∀ i j, i ∉ T → j ∉ T → Valued.v (c * locGram Q v γ i j) ≤ 1)
    (hdet : Valued.v (compBlock T (c • locGram Q v γ)).det = 1)
    (heven : ∀ i, i ∉ T → Valued.v (c * locGram Q v γ i i / 2) ≤ 1) : FixTheta Q L v γ T := by
  have hAKint : ∀ a b, Valued.v (compBlock T (c • locGram Q v γ) a b) ≤ 1 := fun a b => by
    simpa [compBlock] using hint _ _ (blkIdx_notMem (compEquiv T) a) (blkIdx_notMem (compEquiv T) b)
  obtain ⟨b, hb⟩ := exists_unit_entry (compBlock T (c • locGram Q v γ)) hAKint hdet ⟨0, by omega⟩
  have hb' : Valued.v (c * locGram Q v γ (blkIdx (compEquiv T) ⟨0, by omega⟩) (blkIdx (compEquiv T) b)) = 1 := by
    simpa [compBlock] using hb
  exact fixTheta_of_wallSq hQ h2 γ T hc (wallSq_of_block_even hQ γ hγ hT hint heven hdet)
    (fun w hw => exists_rootVector_block h2 γ hγ hT hc hint heven _ _ (blkIdx_notMem (compEquiv T) _)
      (blkIdx_notMem (compEquiv T) _) hb' hw)

/-- **The Wall-determinant squares for a scaled $E \perp \langle 2u\rangle$ block** (the hypothesis `hsq` of
`fixTheta_of_wallSq` in the glue case): if on the complement $K$ of $T$ the entries $cG_{ij}$ and $cG_{ii}/2$ are
integral, $G_{il} = 0$ for $i \in K \setminus \{l\}$, $cG_{ll}/2 = u$ is a unit and the block $A_K$ has
$\lvert\det A_K\rvert = \lvert 2\rvert$, then for every proper $\sigma$ fixing the $b_t$, $t \in T$, and every Wall frame
$(P, R)$ of $S'$, $\lvert\det(P^{\mathsf T}(cG)R)\rvert$ is a square (`restrict_block` and the glue lemma
`exists_sq_valued_wallDet_glue'`; $\det S_K = \det S' = \det\sigma = 1$). -/
theorem wallSq_of_block_glue (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) {T : Finset (Fin n)}
    (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) {c : Fv} (l : Fin n) (hlT : l ∉ T)
    (hint : ∀ i j, i ∉ T → j ∉ T → Valued.v (c * locGram Q v γ i j) ≤ 1)
    (heven : ∀ i, i ∉ T → Valued.v (c * locGram Q v γ i i / 2) ≤ 1)
    (hl : ∀ i, i ∉ T → i ≠ l → locGram Q v γ i l = 0)
    (hu : Valued.v (c * locGram Q v γ l l / 2) = 1)
    (hdet : Valued.v (compBlock T (c • locGram Q v γ)).det = Valued.v (2 : Fv)) :
    ∀ σ : orthGroup Q Fv, σ ∈ locStabV Q v L →
      (∀ t ∈ T, (σ : GL (Fin n) Fv).val *ᵥ basisVec γ t = basisVec γ t) →
      ((σ : GL (Fin n) Fv).val).det = 1 → ∀ {m' : ℕ} {P R : Matrix (Fin n) (Fin m') Fv},
        IsWallFrame Fv (conjMat γ σ) P R →
          ∃ δ : ℤᵐ⁰, Valued.v (Pᵀ * (c • locGram Q v γ) * R).det = δ ^ 2 := by
  intro σ hσ hfix hdetσ m' P R hf
  obtain ⟨hS', horth, hdetK, hframe⟩ := restrict_block hQ γ hγ hT hσ hfix c
  obtain ⟨hf', hgram⟩ := hframe hf
  have hAKsym : (compBlock T (c • locGram Q v γ))ᵀ = compBlock T (c • locGram Q v γ) := by
    simp only [compBlock, transpose_submatrix, transpose_smul, locGram_transpose]
  set e := compEquiv T with he
  set l' := e.symm ⟨l, hlT⟩ with hl'
  have hl'ι : blkIdx e l' = l := congrArg Subtype.val (e.apply_symm_apply ⟨l, hlT⟩)
  have hAKl : ∀ a, a ≠ l' → compBlock T (c • locGram Q v γ) a l' = 0 := by
    intro a ha
    have hne : blkIdx e a ≠ l := fun h => ha (blkIdx_inj e (h.trans hl'ι.symm))
    show (c • locGram Q v γ) (blkIdx e a) (blkIdx e l') = 0
    rw [hl'ι]
    simp [hl _ (blkIdx_notMem e a) hne]
  have hAKll : compBlock T (c • locGram Q v γ) l' l' = 2 * (c * locGram Q v γ l l / 2) := by
    show (c • locGram Q v γ) (blkIdx e l') (blkIdx e l') = _
    rw [hl'ι]
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  have hdetS : (compBlock T (conjMat γ σ)).det = 1 := by
    rw [hdetK, det_conj]; exact hdetσ
  obtain ⟨δ, hδ⟩ := exists_sq_valued_wallDet_glue' (compBlock T (c • locGram Q v γ)) l' _ hAKsym
    (fun a b => by simpa [compBlock] using hint _ _ (blkIdx_notMem e a) (blkIdx_notMem e b))
    (fun a => by simpa [compBlock] using heven _ (blkIdx_notMem e a)) hAKl hAKll hu
    (valued_two_dyadic v h2) hdet (compBlock T (conjMat γ σ)) hS' horth hdetS hf'
  exact ⟨δ, by rw [← hgram]; exact hδ⟩

/-- **Block base case: a scaled $E \perp \langle 2u\rangle$ block.** Let $T$ be a set of basis indices with $b_t$
orthogonal to all other basis vectors, $K$ the complement of $T$ with $m = \lvert K\rvert \ge 2$, and $c \ne 0$ such that
on $K$ the entries $cG_{ij}$ and $cG_{ii}/2$ are integral, an index $l \in K$ has $G_{il} = 0$ ($i \in K$, $i \ne l$)
and $cG_{ll}/2$ a unit, and the block $A_K = (cG_{ij})_{i, j \in K}$ has $\lvert\det A_K\rvert = \lvert 2\rvert$ (so
$A_K = E \perp \langle 2u\rangle$ with $E$ even unimodular). Then `FixTheta Q L v γ T` holds. *Proof* as for
`fixTheta_of_block_scaledEvenUnimodular`, with the glue lemma `exists_sq_valued_wallDet_glue'` (which needs
$\det S_K = 1$, true for proper $\sigma$) and a unit entry $A_{i_0j}$, $i_0 \ne l$, from `Glue2.colOne`. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2: relative spinor norm for a scaled E ⊥ ⟨2u⟩ remainder block)"]
theorem fixTheta_of_block_glue (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) (T : Finset (Fin n))
    (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) {c : Fv} (hc : c ≠ 0)
    (hm : 2 ≤ Fintype.card {i // i ∉ T}) (l : Fin n) (hlT : l ∉ T)
    (hint : ∀ i j, i ∉ T → j ∉ T → Valued.v (c * locGram Q v γ i j) ≤ 1)
    (heven : ∀ i, i ∉ T → Valued.v (c * locGram Q v γ i i / 2) ≤ 1)
    (hl : ∀ i, i ∉ T → i ≠ l → locGram Q v γ i l = 0)
    (hu : Valued.v (c * locGram Q v γ l l / 2) = 1)
    (hdet : Valued.v (compBlock T (c • locGram Q v γ)).det = Valued.v (2 : Fv)) :
    FixTheta Q L v γ T := by
  set e := compEquiv T with he
  set l' := e.symm ⟨l, hlT⟩ with hl'
  have hl'ι : blkIdx e l' = l := congrArg Subtype.val (e.apply_symm_apply ⟨l, hlT⟩)
  have hAKint : ∀ a b, Valued.v (compBlock T (c • locGram Q v γ) a b) ≤ 1 := fun a b => by
    simpa [compBlock] using hint _ _ (blkIdx_notMem e a) (blkIdx_notMem e b)
  have hAKl : ∀ a, a ≠ l' → compBlock T (c • locGram Q v γ) a l' = 0 := by
    intro a ha
    have hne : blkIdx e a ≠ l := fun h => ha (blkIdx_inj e (h.trans hl'ι.symm))
    show (c • locGram Q v γ) (blkIdx e a) (blkIdx e l') = 0
    rw [hl'ι]
    simp [hl _ (blkIdx_notMem e a) hne]
  have hAKll : compBlock T (c • locGram Q v γ) l' l' = 2 * (c * locGram Q v γ l l / 2) := by
    show (c • locGram Q v γ) (blkIdx e l') (blkIdx e l') = _
    rw [hl'ι]
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  have hdet1 := Glue2.valued_det_colOne (compBlock T (c • locGram Q v γ)) l' _ hAKl hAKll hu
    (valued_two_dyadic v h2) hdet
  have : Nontrivial (Fin (Fintype.card {i // i ∉ T})) := Fin.nontrivial_iff_two_le.mpr hm
  obtain ⟨a0, ha0⟩ := exists_ne l'
  obtain ⟨b, hb⟩ := exists_unit_entry (Glue2.colOne (compBlock T (c • locGram Q v γ)) l')
    (Glue2.colOne_integral _ l' hAKint) hdet1 a0
  have hbl : b ≠ l' := by
    rintro rfl
    simp [Glue2.colOne, ha0] at hb
  have hb' : Valued.v (compBlock T (c • locGram Q v γ) a0 b) = 1 := by
    simpa [Glue2.colOne, updateCol_ne hbl] using hb
  have hb'' : Valued.v (c * locGram Q v γ (blkIdx e a0) (blkIdx e b)) = 1 := by
    simpa [compBlock] using hb'
  exact fixTheta_of_wallSq hQ h2 γ T hc (wallSq_of_block_glue hQ h2 γ hγ hT l hlT hint heven hl hu hdet)
    (fun w hw => exists_rootVector_block h2 γ hγ hT hc hint heven _ _ (blkIdx_notMem e _)
      (blkIdx_notMem e _) hb'' hw)

end BaseCases

/-! ### Peeling chains with a spinor-norm remainder -/

section ChainTheta

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

/-- **The remainder shape "scaled even unimodular block"** (a **condition** on the Gram matrix $G$ and the set $T$ of
peeled indices): there is $c \ne 0$ such that the complement $K$ of $T$ has at least $2$ elements, $cG_{ij}$
($i, j \in K$) is integral, $cG_{ii}/2$ ($i \in K$) is integral and the block $(cG_{ij})_{i, j \in K}$
has $\lvert\det\rvert = 1$ (the hypotheses of `fixTheta_of_block_scaledEvenUnimodular`; the complement of $T$ is
$2^kE$ with $E$ even unimodular). -/
def IsBlockEvenUnimodular (G : Matrix (Fin n) (Fin n) Fv) (T : Finset (Fin n)) (c : Fv) : Prop :=
  c ≠ 0 ∧ 2 ≤ Fintype.card {i // i ∉ T} ∧ (∀ i j, i ∉ T → j ∉ T → Valued.v (c * G i j) ≤ 1) ∧
    (∀ i, i ∉ T → Valued.v (c * G i i / 2) ≤ 1) ∧ Valued.v (compBlock T (c • G)).det = 1

/-- **The remainder shape "scaled $E \perp \langle 2u\rangle$ block"** (a **condition** on $G$, the set $T$ of peeled
indices, a scalar $c$ and an index $l$): $c \ne 0$, the complement $K$ of $T$ has at least $2$ elements, $l \in K$,
$cG_{ij}$ and $cG_{ii}/2$ are integral on $K$, $G_{il} = 0$ for $i \in K \setminus \{l\}$, $cG_{ll}/2$ is a unit
and the block $(cG_{ij})_{i, j \in K}$ has $\lvert\det\rvert = \lvert 2\rvert$ (the hypotheses of
`fixTheta_of_block_glue`). -/
def IsBlockGlue2 (G : Matrix (Fin n) (Fin n) Fv) (T : Finset (Fin n)) (c : Fv) (l : Fin n) : Prop :=
  c ≠ 0 ∧ 2 ≤ Fintype.card {i // i ∉ T} ∧ l ∉ T ∧ (∀ i j, i ∉ T → j ∉ T → Valued.v (c * G i j) ≤ 1) ∧
    (∀ i, i ∉ T → Valued.v (c * G i i / 2) ≤ 1) ∧ (∀ i, i ∉ T → i ≠ l → G i l = 0) ∧
    Valued.v (c * G l l / 2) = 1 ∧ Valued.v (compBlock T (c • G)).det = Valued.v (2 : Fv)

/-- **The peeling shape with a spinor-norm remainder** (a **condition** on the Gram matrix $G$ of a basis
$b = \gamma e$ of $L_2$): given the set $T$ of indices already peeled and a list $ks = [k_1, \dots, k_r]$ of further
indices,
* if $ks$ is empty, the complement of $T$ has at most $2$ elements (the remainder of `PeelChain2`), **or** is a scaled
  even unimodular block (`IsBlockEvenUnimodular`, for some $c$), **or** a scaled $E \perp \langle 2u\rangle$ block
  (`IsBlockGlue2`, for some $c$ and $l$);
* if $ks = k :: ks'$, then $k \notin T$, $b_k$ is orthogonal to all other basis vectors,
  $\lvert G_{ii'}\rvert \le \lvert 2G_{kk}\rvert$ for $i, i' \notin T \cup \{k\}$, and
  `PeelChainTheta G (insert k T) ks'`.
Example: the Gram matrix $G = \langle 2u\rangle \perp 4K \perp \langle 8w\rangle$ of $B$ for the form
$\langle u\rangle \perp 2K \perp 4\langle w\rangle$ ($K$ binary even unimodular, $u, w$ units): `ks = [0]` and the
remainder, scaled by $c = 1/4$, is $K \perp \langle 2w\rangle$, of the shape `IsBlockGlue2` with $l = 3$ (see the
module docstring). -/
def PeelChainTheta (G : Matrix (Fin n) (Fin n) Fv) : Finset (Fin n) → List (Fin n) → Prop
  | T, [] => (Finset.univ \ T).card ≤ 2 ∨ (∃ c, IsBlockEvenUnimodular G T c) ∨ (∃ c l, IsBlockGlue2 G T c l)
  | T, k :: ks => k ∉ T ∧ (∀ m, m ≠ k → G m k = 0) ∧
      (∀ i i', i ∉ insert k T → i' ∉ insert k T → Valued.v (G i i') ≤ Valued.v (2 * G k k)) ∧
      PeelChainTheta G (insert k T) ks

/-- **Peeling a chain with a spinor-norm remainder** gives `FixTheta` for the set $T$ already peeled
(induction on the list with `fixTheta_peel`; the base cases are `fixGenerated_of_peelChain2`,
`fixTheta_of_block_scaledEvenUnimodular` and `fixTheta_of_block_glue`). -/
theorem fixTheta_of_peelChainTheta (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) :
    ∀ (ks : List (Fin n)) (T : Finset (Fin n)), (∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) →
      PeelChainTheta (locGram Q v γ) T ks → FixTheta Q L v γ T
  | [], T, hT, hc => by
    have hc' : (Finset.univ \ T).card ≤ 2 ∨ (∃ c, IsBlockEvenUnimodular (locGram Q v γ) T c) ∨
        (∃ c l, IsBlockGlue2 (locGram Q v γ) T c l) := hc
    rcases hc' with hc' | ⟨c, hc'⟩ | ⟨c, l, hc'⟩
    · exact fixTheta_of_fixGenerated hQ (fixGenerated_of_peelChain2 hQ h2 γ hγ [] T hT hc')
    · obtain ⟨hc0, hm, hint, heven, hdet⟩ := hc'
      exact fixTheta_of_block_scaledEvenUnimodular hQ h2 γ hγ T hT hc0 hm hint hdet heven
    · obtain ⟨hc0, hm, hlT, hint, heven, hl, hu, hdet⟩ := hc'
      exact fixTheta_of_block_glue hQ h2 γ hγ T hT hc0 hm l hlT hint heven hl hu hdet
  | k :: ks, T, hT, ⟨hkT, hk, hd, hrest⟩ => by
    refine fixTheta_peel hQ h2 γ hγ T k hkT hT hk hd
      (fixTheta_of_peelChainTheta hQ h2 γ hγ ks (insert k T) (fun t ht m hm => ?_) hrest)
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hk m hm
    · exact hT t ht m hm

/-- **Theorem 18, "only if", for a peeling chain with a spinor-norm remainder** (Conway–Sloane §9.5, p. 391;
$p = 2$): if $L_2$ has a basis $b = \gamma e$ and a list $ks$ with `PeelChainTheta (locGram Q v γ) ∅ ks`, every
$A \in \theta(O^+(L_2))$ is, up to squares, the product of the norms of an even number of $2$-adic root vectors.
(For a proper $\sigma$, `FixTheta` for $T = \emptyset$ gives such a list, of even length since
$1 = \det\sigma = (-1)^r$.) Unconditional. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': a peeling chain with a spinor-norm remainder block)"]
theorem theorem18OnlyIf_of_peelChainTheta (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) (ks : List (Fin n))
    (hc : PeelChainTheta (locGram Q v γ) ∅ ks) : Theorem18OnlyIf Q L v hQ := by
  intro A hA
  obtain ⟨σ, ⟨hσL, hσS⟩, hσB⟩ := (mem_localSpinorNormGroup Q hQ v L).mp hA
  obtain ⟨xs, hxs, hdet, hθ⟩ :=
    fixTheta_of_peelChainTheta hQ h2 γ hγ ks ∅ (by simp) hc σ hσL (by simp)
  have h1 : ((σ : GL (Fin n) Fv).val).det = 1 := hσS
  refine ⟨xs, ?_, hxs, hσB.symm.trans hθ⟩
  rw [h1] at hdet
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : Fv) ≠ 1)).mp hdet.symm

end ChainTheta


end QuadFormsKB.ConwaySloane
