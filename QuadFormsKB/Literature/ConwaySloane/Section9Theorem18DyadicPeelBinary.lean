/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$, peeling chains with a binary remainder

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18 and the remark after it, at $p = 2$.

**Layer.** As in `Section9Theorem18DyadicPeel.lean`: over $\mathbb Q$ at the prime $v$ over $2$, a basis
$b = \gamma e$ of $L_2$ with Gram matrix $G$ = `locGram Q v γ`, and the fixing condition `FixGenerated`.

**Defines** `OrthSplit` (a set $T$ of indices of basis vectors orthogonal to all others whose complement is
$\{i, j\}$), `PeelChain2` (peeling chains ending in a remainder of rank at most $2$), `Theorem18DyadicCovered5` and the
named statement `Theorem18DyadicResidual5`.

**Proves** `exists_reflection_of_improper` (an improper isometry fixing the $b_t$ is a reflection in the binary
summand), `exists_rootVector_orth` (a root vector in the binary summand), `fixGenerated_of_orthSplit` (the relative
binary base case), `fixGenerated_of_peelChain2`, `generatedByRootReflections_of_peelChain2`,
`theorem18OnlyIf_of_peelChain2`, `theorem18OnlyIf_of_covered5`, `theorem18DyadicResidual4_of_residual5`,
`theorem18Dyadic_of_residual5`, `theorem18Statement_of_residual5`.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicPeel

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

/-! ### Improper isometries of a binary orthogonal summand: linear algebra -/

section Core

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- **A $2\times 2$ improper isometry is an involution of trace $0$**: if $H$ is a nonsingular $2\times 2$
matrix and $\rho^{\mathsf T}H\rho = H$ with $\det\rho = -1$, then $\rho^2 = 1$ and $\operatorname{tr}\rho = 0$. -/
theorem bin2_improper (H ρ : Matrix (Fin 2) (Fin 2) K) (hH : H.det ≠ 0) (horth : ρᵀ * H * ρ = H)
    (hdet : ρ.det = -1) : ρ * ρ = 1 ∧ ρ.trace = 0 := by
  have hHu : IsUnit H.det := isUnit_iff_ne_zero.mpr hH
  have h1 : ρ * ρ.adjugate = (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [Matrix.mul_adjugate, hdet]
  have hA : H * ρ.adjugate = -(ρᵀ * H) := by
    calc H * ρ.adjugate = (ρᵀ * H * ρ) * ρ.adjugate := by rw [horth]
      _ = ρᵀ * H * (ρ * ρ.adjugate) := by rw [Matrix.mul_assoc]
      _ = -(ρᵀ * H) := by rw [h1]; simp
  have hadj : ρ.adjugate = -(H⁻¹ * (ρᵀ * H)) := by
    calc ρ.adjugate = H⁻¹ * (H * ρ.adjugate) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hHu, Matrix.one_mul]
      _ = _ := by rw [hA, Matrix.mul_neg]
  have htr1 : ρ.adjugate.trace = ρ.trace := by
    rw [Matrix.adjugate_fin_two]; simp [Matrix.trace_fin_two]; ring
  have htr2 : ρ.adjugate.trace = -ρ.trace := by
    rw [hadj, Matrix.trace_neg, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hHu,
      Matrix.mul_one, Matrix.trace_transpose]
  have h2 : (2 : K) * ρ.trace = 0 := by linear_combination htr2 - htr1
  have htr0 : ρ.trace = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  refine ⟨?_, htr0⟩
  have hd2 : ρ 0 0 * ρ 1 1 - ρ 0 1 * ρ 1 0 = -1 := by
    rw [← hdet, Matrix.det_fin_two]
  have ht : ρ 0 0 + ρ 1 1 = 0 := by rwa [Matrix.trace_fin_two] at htr0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination ρ 0 0 * ht - hd2
  · linear_combination ρ 0 1 * ht
  · linear_combination ρ 1 0 * ht
  · linear_combination ρ 1 1 * ht - hd2

/-- Two vectors $w, u \in K^2$ with $\det[w \mid u] = 0$ and $w \ne 0$ are proportional. -/
theorem exists_smul_of_det_eq_zero' {w u : Fin 2 → K} (hw : w ≠ 0) (hd : w 0 * u 1 - u 0 * w 1 = 0) :
    ∃ c : K, u = c • w := by
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := by
      intro h1
      apply hw
      funext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨u 1 / w 1, ?_⟩
    have hu0 : u 0 * w 1 = 0 := by linear_combination -hd + u 1 * h0
    have hu0' : u 0 = 0 := (mul_eq_zero.mp hu0).resolve_right h1
    funext i
    fin_cases i
    · simp [h0, hu0']
    · simp; field_simp
  · refine ⟨u 0 / w 0, ?_⟩
    funext i
    fin_cases i
    · simp; field_simp
    · simp; field_simp; linear_combination hd

/-- **An improper $2\times 2$ involution has rank-one $\rho - 1$**: if $\rho^2 = 1$, $\operatorname{tr}\rho = 0$ and
$\det\rho = -1$, there are $e$ and $w = \rho e - e \ne 0$ with $\rho y - y \in Kw$ for all $y$. -/
theorem bin2_rank_one (ρ : Matrix (Fin 2) (Fin 2) K) (htr : ρ.trace = 0) (hdet : ρ.det = -1) :
    ∃ e w : Fin 2 → K, w = ρ *ᵥ e - e ∧ w ≠ 0 ∧ ∀ y, ∃ c : K, ρ *ᵥ y - y = c • w := by
  have ht : ρ 0 0 + ρ 1 1 = 0 := by rwa [Matrix.trace_fin_two] at htr
  have hd : ρ 0 0 * ρ 1 1 - ρ 0 1 * ρ 1 0 = -1 := by rwa [Matrix.det_fin_two] at hdet
  have e1 : (![ρ 0 0 - 1, ρ 1 0] : Fin 2 → K) = ρ *ᵥ Pi.single 0 1 - Pi.single 0 1 := by
    ext k; fin_cases k <;> simp
  have e2 : (![ρ 0 1, ρ 1 1 - 1] : Fin 2 → K) = ρ *ᵥ Pi.single 1 1 - Pi.single 1 1 := by
    ext k; fin_cases k <;> simp
  have hN : ∀ y : Fin 2 → K, ρ *ᵥ y - y =
      y 0 • (![ρ 0 0 - 1, ρ 1 0] : Fin 2 → K) + y 1 • (![ρ 0 1, ρ 1 1 - 1] : Fin 2 → K) := by
    intro y; ext k; fin_cases k <;> simp <;> ring
  by_cases h1 : (![ρ 0 0 - 1, ρ 1 0] : Fin 2 → K) = 0
  · have a1 : ρ 0 0 = 1 := by
      have := congrFun h1 0; simp at this; linear_combination this
    have a2 : ρ 1 0 = 0 := by
      have := congrFun h1 1; simpa using this
    have h2 : (![ρ 0 1, ρ 1 1 - 1] : Fin 2 → K) ≠ 0 := by
      intro h2
      have b1 : ρ 0 1 = 0 := by have := congrFun h2 0; simpa using this
      have b2 : ρ 1 1 = 1 := by have := congrFun h2 1; simp at this; linear_combination this
      rw [a1, a2, b1, b2] at hd
      norm_num at hd
    refine ⟨Pi.single 1 1, _, e2, h2, fun y => ⟨y 1, ?_⟩⟩
    rw [hN y, h1]; simp
  · refine ⟨Pi.single 0 1, _, e1, h1, fun y => ?_⟩
    have hdet0 : (![ρ 0 0 - 1, ρ 1 0] : Fin 2 → K) 0 * (![ρ 0 1, ρ 1 1 - 1] : Fin 2 → K) 1 -
        (![ρ 0 1, ρ 1 1 - 1] : Fin 2 → K) 0 * (![ρ 0 0 - 1, ρ 1 0] : Fin 2 → K) 1 = 0 := by
      simp
      linear_combination hd - ht
    obtain ⟨c, hc⟩ := exists_smul_of_det_eq_zero' h1 hdet0
    refine ⟨y 0 + y 1 * c, ?_⟩
    rw [hN y, hc, smul_smul, ← add_smul]

/-- **The coordinates $y_0 e_i + y_1 e_j$** of a vector of $K^n$ supported on the two indices $i, j$. -/
def ext2 (i j : Fin n) (y : Fin 2 → K) : Fin n → K := y 0 • Pi.single i 1 + y 1 • Pi.single j 1

theorem ext2_apply (i j : Fin n) (y : Fin 2 → K) (x : Fin n) :
    ext2 i j y x = (if x = i then y 0 else 0) + (if x = j then y 1 else 0) := by
  simp [ext2, Pi.single_apply]

theorem ext2_i {i j : Fin n} (hij : i ≠ j) (y : Fin 2 → K) : ext2 i j y i = y 0 := by
  simp [ext2_apply, hij]

theorem ext2_j {i j : Fin n} (hij : i ≠ j) (y : Fin 2 → K) : ext2 i j y j = y 1 := by
  simp [ext2_apply, hij.symm]

theorem ext2_other {i j : Fin n} (y : Fin 2 → K) {x : Fin n} (hi : x ≠ i) (hj : x ≠ j) : ext2 i j y x = 0 := by
  simp [ext2_apply, hi, hj]

theorem ext2_sub (i j : Fin n) (y y' : Fin 2 → K) : ext2 i j (y - y') = ext2 i j y - ext2 i j y' := by
  ext x; simp only [ext2_apply, Pi.sub_apply]; split_ifs <;> ring

theorem ext2_smul (i j : Fin n) (c : K) (y : Fin 2 → K) : ext2 i j (c • y) = c • ext2 i j y := by
  ext x; simp only [ext2_apply, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

theorem ext2_neg (i j : Fin n) (y : Fin 2 → K) : ext2 i j (-y) = -ext2 i j y := by
  ext x; simp only [ext2_apply, Pi.neg_apply]; split_ifs <;> ring

theorem dot_ext2 (i j : Fin n) (y : Fin 2 → K) (u : Fin n → K) : ext2 i j y ⬝ᵥ u = y 0 * u i + y 1 * u j := by
  simp [ext2, add_dotProduct, smul_dotProduct, single_dotProduct]

/-- The $2\times 2$ block of a matrix at the indices $i, j$. -/
def rhoOf (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) : Matrix (Fin 2) (Fin 2) K :=
  !![M i i, M i j; M j i, M j j]

theorem matrix_eq_of_bilin {m : ℕ} (A B : Matrix (Fin m) (Fin m) K)
    (h : ∀ y y', y ⬝ᵥ (A *ᵥ y') = y ⬝ᵥ (B *ᵥ y')) : A = B := by
  ext a b
  have := h (Pi.single a 1) (Pi.single b 1)
  simpa [mulVec_single, single_dotProduct] using this

/-- **A binary orthogonal summand in coordinates** (the data of the base case with a two-element complement): a
symmetric nonsingular matrix $G$ (the Gram matrix of a basis), a set $T$ of indices whose basis vectors are orthogonal
to all the other basis vectors, and the two remaining indices $i \ne j$. -/
structure OrthSplit (G : Matrix (Fin n) (Fin n) K) (T : Finset (Fin n)) (i j : Fin n) : Prop where
  symm : Gᵀ = G
  det_ne : G.det ≠ 0
  orth : ∀ t ∈ T, ∀ m, m ≠ t → G m t = 0
  cover : ∀ x, x ∈ T ∨ x = i ∨ x = j
  ne : i ≠ j
  iT : i ∉ T
  jT : j ∉ T

namespace OrthSplit

variable {G : Matrix (Fin n) (Fin n) K} {T : Finset (Fin n)} {i j : Fin n}

theorem symm_apply (hs : OrthSplit G T i j) (a b : Fin n) : G b a = G a b := by
  have := congrFun (congrFun hs.symm a) b
  simpa using this

theorem orth' (hs : OrthSplit G T i j) {t : Fin n} (ht : t ∈ T) {m : Fin n} (hm : m ≠ t) : G t m = 0 := by
  rw [← hs.symm_apply t m]; exact hs.orth t ht m hm

theorem diag_ne (hs : OrthSplit G T i j) {t : Fin n} (ht : t ∈ T) : G t t ≠ 0 := by
  intro h0
  refine hs.det_ne (Matrix.det_eq_zero_of_column_eq_zero t fun m => ?_)
  by_cases hm : m = t
  · subst hm; exact h0
  · exact hs.orth t ht m hm

theorem mulVec_T (hs : OrthSplit G T i j) {t : Fin n} (ht : t ∈ T) (y : Fin n → K) :
    (G *ᵥ y) t = G t t * y t := by
  unfold mulVec dotProduct
  rw [Finset.sum_eq_single t]
  · intro k _ hk; show G t k * y k = 0; rw [hs.orth' ht hk, zero_mul]
  · simp

theorem Gext (y : Fin 2 → K) (x : Fin n) :
    (G *ᵥ ext2 i j y) x = G x i * y 0 + G x j * y 1 := by
  simp [ext2, mulVec_add, mulVec_smul, mulVec_single]
  ring

variable {M : Matrix (Fin n) (Fin n) K}

theorem M_col_T (hMt : ∀ t ∈ T, M *ᵥ Pi.single t 1 = Pi.single t 1) {t : Fin n} (ht : t ∈ T) (x : Fin n) :
    M x t = if x = t then 1 else 0 := by
  have := congrFun (hMt t ht) x
  simpa [mulVec_single, Pi.single_apply] using this

theorem M_T_row (hs : OrthSplit G T i j) (hMt : ∀ t ∈ T, M *ᵥ Pi.single t 1 = Pi.single t 1)
    (hMf : ∀ x y, (M *ᵥ x) ⬝ᵥ (G *ᵥ (M *ᵥ y)) = x ⬝ᵥ (G *ᵥ y)) {t a : Fin n} (ht : t ∈ T) (ha : a ∉ T) :
    M t a = 0 := by
  have h := hMf (Pi.single t 1) (Pi.single a 1)
  rw [hMt t ht, single_dotProduct, single_dotProduct, hs.mulVec_T ht, hs.mulVec_T ht] at h
  have hat : a ≠ t := fun h => ha (h ▸ ht)
  simp [mulVec_single, Pi.single_apply, hat] at h
  exact h.resolve_left (hs.diag_ne ht)

theorem M_col_C (hs : OrthSplit G T i j) (hMt : ∀ t ∈ T, M *ᵥ Pi.single t 1 = Pi.single t 1)
    (hMf : ∀ x y, (M *ᵥ x) ⬝ᵥ (G *ᵥ (M *ᵥ y)) = x ⬝ᵥ (G *ᵥ y)) {a : Fin n} (ha : a ∉ T) :
    M *ᵥ Pi.single a 1 = M i a • Pi.single i 1 + M j a • Pi.single j 1 := by
  ext x
  rcases hs.cover x with hx | hx | hx
  · have hxi : x ≠ i := fun h => hs.iT (h ▸ hx)
    have hxj : x ≠ j := fun h => hs.jT (h ▸ hx)
    simp [mulVec_single, Pi.single_apply, hxi, hxj, hs.M_T_row hMt hMf hx ha]
  · subst hx; simp [mulVec_single, Pi.single_apply, hs.ne]
  · subst hx; simp [mulVec_single, Pi.single_apply, hs.ne.symm]

theorem ext2_mulVec (hs : OrthSplit G T i j) (hMt : ∀ t ∈ T, M *ᵥ Pi.single t 1 = Pi.single t 1)
    (hMf : ∀ x y, (M *ᵥ x) ⬝ᵥ (G *ᵥ (M *ᵥ y)) = x ⬝ᵥ (G *ᵥ y)) (y : Fin 2 → K) :
    M *ᵥ ext2 i j y = ext2 i j (rhoOf M i j *ᵥ y) := by
  rw [ext2, mulVec_add, mulVec_smul, mulVec_smul, hs.M_col_C hMt hMf hs.iT, hs.M_col_C hMt hMf hs.jT]
  ext x
  by_cases hxi : x = i
  · subst hxi
    simp [ext2_apply, rhoOf, dotProduct, Fin.sum_univ_two, hs.ne] <;> ring
  · by_cases hxj : x = j
    · subst hxj
      simp [ext2_apply, rhoOf, dotProduct, Fin.sum_univ_two, hs.ne.symm] <;> ring
    · simp [ext2_apply, rhoOf, dotProduct, Fin.sum_univ_two, hxi, hxj] <;> ring

theorem det_rho (hs : OrthSplit G T i j) (hMt : ∀ t ∈ T, M *ᵥ Pi.single t 1 = Pi.single t 1)
    (hMf : ∀ x y, (M *ᵥ x) ⬝ᵥ (G *ᵥ (M *ᵥ y)) = x ⬝ᵥ (G *ᵥ y)) : M.det = (rhoOf M i j).det := by
  classical
  obtain ⟨c, hc0, hc1⟩ : ∃ c : Fin 2 → Fin n, c 0 = i ∧ c 1 = j := ⟨![i, j], rfl, rfl⟩
  let A : Matrix (Fin n) (Fin 2) K := Matrix.of fun x a => if x = c a then 1 else 0
  let B : Matrix (Fin 2) (Fin n) K :=
    Matrix.of fun a y => M (c a) y - (if c a = y then 1 else 0)
  have hM : M = 1 + A * B := by
    ext x y
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, A, B, Matrix.of_apply, hc0, hc1]
    rcases hs.cover x with hx | hx | hx
    · have hxi : x ≠ i := fun h => hs.iT (h ▸ hx)
      have hxj : x ≠ j := fun h => hs.jT (h ▸ hx)
      simp only [hxi, hxj, ite_false, zero_mul, add_zero]
      by_cases hy : y ∈ T
      · rw [M_col_T hMt hy x, Matrix.one_apply]
      · rw [hs.M_T_row hMt hMf hx hy, Matrix.one_apply]
        have : x ≠ y := fun h => hy (h ▸ hx)
        simp [this]
    · subst hx
      simp [hs.ne]
      rw [Matrix.one_apply]; ring
    · subst hx
      simp [hs.ne.symm]
      rw [Matrix.one_apply]; ring
  have hBA' : ∀ a b, (B * A) a b = M (c a) (c b) - (if c a = c b then 1 else 0) := by
    intro a b
    simp only [Matrix.mul_apply, A, B, Matrix.of_apply]
    rw [Finset.sum_eq_single (c b)]
    · simp
    · intro y _ hy; simp [hy]
    · simp
  have hBA : (1 : Matrix (Fin 2) (Fin 2) K) + B * A = rhoOf M i j := by
    ext a b
    rw [Matrix.add_apply, hBA']
    fin_cases a <;> fin_cases b <;>
      simp [hc0, hc1, rhoOf, hs.ne, hs.ne.symm]
  calc M.det = (1 + A * B).det := by rw [← hM]
    _ = (1 + B * A).det := Matrix.det_one_add_mul_comm A B
    _ = _ := by rw [hBA]

theorem tpart_fix (hs : OrthSplit G T i j) (hMt : ∀ t ∈ T, M *ᵥ Pi.single t 1 = Pi.single t 1)
    (d : Fin n → K) :
    M *ᵥ (fun x => if x ∈ T then d x else 0) = fun x => if x ∈ T then d x else 0 := by
  classical
  ext x
  unfold mulVec dotProduct
  by_cases hx : x ∈ T
  · rw [Finset.sum_eq_single x]
    · simp [hx, M_col_T hMt hx]
    · intro z _ hz
      by_cases hzT : z ∈ T
      · show M x z * _ = 0
        rw [M_col_T hMt hzT x, if_neg (Ne.symm hz)]; simp
      · simp [hzT]
    · simp
  · rw [if_neg hx]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hzT : z ∈ T
    · show M x z * _ = 0
      rw [M_col_T hMt hzT x, if_neg (fun (h : x = z) => hx (h ▸ hzT))]; simp
    · simp [hzT]

end OrthSplit

/-- **The improper isometries of the binary summand, in coordinates**: let $G$ be the Gram matrix of a basis, $T$ a set
of indices whose basis vectors are orthogonal to all others, $\{i, j\}$ the two other indices, and $M$ the matrix of an
isometry ($B(Mx, My) = B(x, y)$ for $B(x, y) = x^{\mathsf T}Gy$) fixing the basis vectors $e_t$, $t \in T$, with
$\det M = -1$. Then there is $w \ne 0$ supported on $\{i, j\}$ with $Mw = -w$ and $Md - d \in Kw$ for all $d$. -/
theorem core_improper {G : Matrix (Fin n) (Fin n) K} {T : Finset (Fin n)} {i j : Fin n}
    {M : Matrix (Fin n) (Fin n) K} (hs : OrthSplit G T i j)
    (hMt : ∀ t ∈ T, M *ᵥ Pi.single t 1 = Pi.single t 1)
    (hMf : ∀ x y, (M *ᵥ x) ⬝ᵥ (G *ᵥ (M *ᵥ y)) = x ⬝ᵥ (G *ᵥ y)) (hdet : M.det = -1) :
    ∃ w : Fin n → K, w ≠ 0 ∧ M *ᵥ w = -w ∧ (∀ t ∈ T, w t = 0) ∧ ∀ d, ∃ c : K, M *ᵥ d - d = c • w := by
  classical
  have hdetρ : (rhoOf M i j).det = -1 := by rw [← hs.det_rho hMt hMf]; exact hdet
  set ρ := rhoOf M i j with hρ
  set H : Matrix (Fin 2) (Fin 2) K := !![G i i, G i j; G j i, G j j] with hH
  have key2 : ∀ y y', ext2 i j y ⬝ᵥ (G *ᵥ ext2 i j y') = y ⬝ᵥ (H *ᵥ y') := by
    intro y y'
    rw [dot_ext2, OrthSplit.Gext, OrthSplit.Gext]
    simp [hH, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  have hρy : ∀ y y', (ρ *ᵥ y) ⬝ᵥ (H *ᵥ (ρ *ᵥ y')) = y ⬝ᵥ (H *ᵥ y') := fun y y' => by
    have := hMf (ext2 i j y) (ext2 i j y')
    rwa [hs.ext2_mulVec hMt hMf, hs.ext2_mulVec hMt hMf, key2, key2] at this
  have horth : ρᵀ * H * ρ = H := by
    refine matrix_eq_of_bilin _ _ fun y y' => ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec y, vecMul_transpose, hρy]
  have hHdet : H.det ≠ 0 := by
    intro h0
    obtain ⟨y, hy, hHy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hy
    have hG : G *ᵥ ext2 i j y = 0 := by
      ext x
      rcases hs.cover x with hx | hx | hx
      · have hxi : x ≠ i := fun h => hs.iT (h ▸ hx)
        have hxj : x ≠ j := fun h => hs.jT (h ▸ hx)
        rw [hs.mulVec_T hx, ext2_other y hxi hxj, mul_zero]; rfl
      · subst hx
        have := congrFun hHy 0
        rw [OrthSplit.Gext]
        simpa [hH, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
      · subst hx
        have := congrFun hHy 1
        rw [OrthSplit.Gext]
        simpa [hH, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
    have h0' := Matrix.eq_zero_of_mulVec_eq_zero hs.det_ne hG
    ext a
    fin_cases a
    · have := congrFun h0' i; rw [ext2_i hs.ne] at this; simpa using this
    · have := congrFun h0' j; rw [ext2_j hs.ne] at this; simpa using this
  obtain ⟨hρρ, hρtr⟩ := bin2_improper H ρ hHdet horth hdetρ
  obtain ⟨e, w₂, hw₂, hw₂0, hprop⟩ := bin2_rank_one ρ hρtr hdetρ
  have hρw : ρ *ᵥ w₂ = -w₂ := by
    rw [hw₂, mulVec_sub, mulVec_mulVec, hρρ, Matrix.one_mulVec]; abel
  refine ⟨ext2 i j w₂, ?_, ?_, ?_, ?_⟩
  · intro h0
    apply hw₂0
    ext a
    fin_cases a
    · have := congrFun h0 i; rw [ext2_i hs.ne] at this; simpa using this
    · have := congrFun h0 j; rw [ext2_j hs.ne] at this; simpa using this
  · rw [hs.ext2_mulVec hMt hMf, hρw, ext2_neg]
  · intro t ht
    exact ext2_other w₂ (fun h => hs.iT (h ▸ ht)) (fun h => hs.jT (h ▸ ht))
  · intro d
    set tp : Fin n → K := fun x => if x ∈ T then d x else 0 with htp
    set y : Fin 2 → K := ![d i, d j] with hy
    have hd : d = ext2 i j y + tp := by
      ext x
      rcases hs.cover x with hx | hx | hx
      · have hxi : x ≠ i := fun h => hs.iT (h ▸ hx)
        have hxj : x ≠ j := fun h => hs.jT (h ▸ hx)
        simp [ext2_other y hxi hxj, htp, hx]
      · subst hx; simp [ext2_i hs.ne, hy, htp, hs.iT]
      · subst hx; simp [ext2_j hs.ne, hy, htp, hs.jT]
    obtain ⟨c, hc⟩ := hprop y
    refine ⟨c, ?_⟩
    have e1 : M *ᵥ d = ext2 i j (ρ *ᵥ y) + tp := by
      conv_lhs => rw [hd]
      rw [mulVec_add, hs.ext2_mulVec hMt hMf, hs.tpart_fix hMt d]
    rw [e1]
    conv_lhs => rw [show d = ext2 i j y + tp from hd]
    rw [← ext2_smul, ← hc, ext2_sub]
    abel

end Core

/-! ### Lifting to the lattice -/

section Lift

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- **An isometry with a rank-one $\sigma - 1$ and a negated vector is a reflection**: let $\sigma \in O(V)$,
$w \ne 0$ with $\sigma w = -w$ and $\sigma x - x \in Fw$ for all $x$. Then $Q(w) \ne 0$ and $\sigma = \tau_w$. (Then
$\sigma^2 = 1$; the $(+1)$-eigenvectors $x + \sigma x$ are orthogonal to $w$, so $B(w, \cdot)$ vanishes if $Q(w) = 0$;
and $B(w, \sigma x) = -B(w, x)$ determines the coefficient of $w$.) -/
theorem eq_symm_of_neg_eigen (hQ : Q.Nondegenerate) (σ : orthGroup Q Fv) {w : Fin n → Fv} (hw : w ≠ 0)
    (hσw : (σ : GL (Fin n) Fv).val *ᵥ w = -w)
    (hN : ∀ x, ∃ c : Fv, (σ : GL (Fin n) Fv).val *ᵥ x - x = c • w) :
    Q.evalIn Fv w ≠ 0 ∧ σ = symm Q Fv w := by
  set S := (σ : GL (Fin n) Fv).val with hS
  have hSx : ∀ x, ∃ c : Fv, S *ᵥ x = x + c • w := fun x => by
    obtain ⟨c, hc⟩ := hN x; exact ⟨c, sub_eq_iff_eq_add'.mp hc⟩
  have hwS : ∀ x, qbil Q Fv w (S *ᵥ x) = - qbil Q Fv w x := by
    intro x
    have h := qbil_orth Q Fv σ w (S *ᵥ x)
    change qbil Q Fv (S *ᵥ w) (S *ᵥ (S *ᵥ x)) = _ at h
    obtain ⟨c, hc⟩ := hSx x
    have hSS : S *ᵥ (S *ᵥ x) = x := by rw [hc, mulVec_add, mulVec_smul, hσw, hc]; simp
    rw [hσw, hSS, qbil_neg_left] at h
    linear_combination -h
  have hkey : ∀ x, ∃ c : Fv, S *ᵥ x = x + c • w ∧ 2 * qbil Q Fv w x = - (c * qbil Q Fv w w) := by
    intro x
    obtain ⟨c, hc⟩ := hSx x
    refine ⟨c, hc, ?_⟩
    have h := hwS x
    rw [hc, qbil_add_right, qbil_smul_right'] at h
    linear_combination h
  have hH : (Q.hessian.map (algebraMap ℚ Fv)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero _).mpr hQ
  have hQw : Q.evalIn Fv w ≠ 0 := by
    intro h0
    apply hw
    have hww : qbil Q Fv w w = 0 := by rw [qbil_self, h0, mul_zero]
    have hall : ∀ x, qbil Q Fv w x = 0 := by
      intro x
      obtain ⟨c, _, hc⟩ := hkey x
      rw [hww, mul_zero, neg_zero] at hc
      rcases mul_eq_zero.mp hc with h | h
      · exact absurd h two_ne_zero
      · exact h
    refine Matrix.eq_zero_of_mulVec_eq_zero hH ?_
    funext k
    have h1 := hall (Pi.single k 1)
    rw [qbil_comm] at h1
    have h2 : (Pi.single k 1 : Fin n → Fv) ⬝ᵥ (Q.hessian.map (algebraMap ℚ Fv) *ᵥ w) = 0 := h1
    rw [single_dotProduct, one_mul] at h2
    exact h2
  refine ⟨hQw, ?_⟩
  refine Subtype.ext (Units.ext ?_)
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  simp only [Matrix.toLin'_apply]
  obtain ⟨c, hc, h2⟩ := hkey x
  show S *ᵥ x = ((symm Q Fv w : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ x
  rw [symm_mulVec_bil Q Fv hQw, hc]
  have hc' : c = -(qbil Q Fv w x / Q.evalIn Fv w) := by
    have h2' : (2 : Fv) * (qbil Q Fv w x + c * Q.evalIn Fv w) = 0 := by
      rw [qbil_self] at h2; linear_combination h2
    have := (mul_eq_zero.mp h2').resolve_left two_ne_zero
    field_simp
    linear_combination this
  rw [hc', neg_smul, sub_eq_add_neg]


/-- **An improper isometry fixing the orthogonal summand's complement is a reflection in the binary summand**: let
$b = \gamma e$ be a basis with Gram matrix $G$, $T$ a set of indices of basis vectors orthogonal to all the others,
and $i \ne j$ the two other indices. If $\sigma \in O(V)$ fixes $b_t$ ($t \in T$) and $\det\sigma = -1$, then
$\sigma = \tau_w$ for some $w$ with $Q(w) \ne 0$ and $B(w, b_t) = 0$ for $t \in T$. (This is the argument of
`binary_improper_eq_symm` inside the nondegenerate binary space $\operatorname{span}(b_i, b_j)$.) -/
theorem exists_reflection_of_improper (hQ : Q.Nondegenerate) (γ : GL (Fin n) Fv) {T : Finset (Fin n)}
    {i j : Fin n} (hs : OrthSplit (locGram Q v γ) T i j) (σ : orthGroup Q Fv)
    (hfix : ∀ t ∈ T, (σ : GL (Fin n) Fv).val *ᵥ basisVec γ t = basisVec γ t)
    (hdet : (σ : GL (Fin n) Fv).val.det = -1) :
    ∃ w : Fin n → Fv, Q.evalIn Fv w ≠ 0 ∧ σ = symm Q Fv w ∧ ∀ t ∈ T, qbil Q Fv w (basisVec γ t) = 0 := by
  set S := (σ : GL (Fin n) Fv).val with hS
  set M : Matrix (Fin n) (Fin n) Fv := ((γ⁻¹ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) * S * γ.val with hM
  have hγinv : ∀ u, γ.val *ᵥ (((γ⁻¹ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ u) = u := fun u => by
    rw [mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hinvγ : ∀ u, ((γ⁻¹ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ (γ.val *ᵥ u) = u := fun u => by
    rw [mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hMx : ∀ x, M *ᵥ x = ((γ⁻¹ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ (S *ᵥ (γ.val *ᵥ x)) := by
    intro x; rw [hM, ← mulVec_mulVec, ← mulVec_mulVec]
  have hγM : ∀ x, γ.val *ᵥ (M *ᵥ x) = S *ᵥ (γ.val *ᵥ x) := fun x => by rw [hMx, hγinv]
  have hMt : ∀ t ∈ T, M *ᵥ Pi.single t 1 = Pi.single t 1 := by
    intro t ht
    rw [hMx]
    have h := hfix t ht
    change S *ᵥ (γ.val *ᵥ Pi.single t 1) = γ.val *ᵥ Pi.single t 1 at h
    rw [h, hinvγ]
  have hMf : ∀ x y, (M *ᵥ x) ⬝ᵥ (locGram Q v γ *ᵥ (M *ᵥ y)) = x ⬝ᵥ (locGram Q v γ *ᵥ y) := by
    intro x y
    rw [← qbil_mulVec_locGram, ← qbil_mulVec_locGram, hγM, hγM]
    exact qbil_orth Q Fv σ _ _
  have hdetM : M.det = -1 := by
    have h1 := congrArg Matrix.det (Units.inv_mul γ)
    rw [det_mul, det_one] at h1
    rw [hM, det_mul, det_mul]
    calc _ = S.det * (((γ⁻¹ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv).det * γ.val.det) := by ring
      _ = -1 := by rw [h1, mul_one]; exact hdet
  obtain ⟨w, hw0, hMw, hwt, hprop⟩ := core_improper hs hMt hMf hdetM
  have hγdet : γ.val.det ≠ 0 := (Matrix.isUnits_det_units γ).ne_zero
  have hwV0 : γ.val *ᵥ w ≠ 0 := fun h => hw0 (Matrix.eq_zero_of_mulVec_eq_zero hγdet h)
  have hσw : S *ᵥ (γ.val *ᵥ w) = -(γ.val *ᵥ w) := by
    rw [← hγM, hMw, mulVec_neg]
  have hN : ∀ x, ∃ c : Fv, S *ᵥ x - x = c • (γ.val *ᵥ w) := by
    intro x
    obtain ⟨c, hc⟩ := hprop (((γ⁻¹ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ x)
    refine ⟨c, ?_⟩
    have hx := hγinv x
    have h1 := congrArg (fun u => γ.val *ᵥ u) hc
    simp only [mulVec_sub, mulVec_smul, hγM, hx] at h1
    exact h1
  obtain ⟨hQw, hσ⟩ := eq_symm_of_neg_eigen hQ σ hwV0 hσw hN
  refine ⟨γ.val *ᵥ w, hQw, hσ, fun t ht => ?_⟩
  rw [qbil_vec_basisVec γ (hs.orth t ht), hwt t ht, zero_mul]


/-- **A $2$-adic root vector orthogonal to the fixed basis vectors** (the relative version of
`exists_rootVector_of_max`): if $\{i, j\}$ is the complement of the set $T$ of indices of basis vectors orthogonal to
all others, there is a root vector $r$ of $L$ with $B(r, b_t) = 0$ for all $t \in T$. Take $r \in L_2$ of maximal
$\lvert Q(r)\rvert$ among the vectors of $L_2$ orthogonal to all $b_t$; it is nonzero for some vector since $G$ is
nonsingular (one of $b_i, b_j, b_i + b_j$ has $Q \ne 0$). For $y \in L_2$ drop the $b_t$-components: they are
orthogonal to $r$, so $\lvert B(r, y)\rvert = \lvert B(r, y')\rvert \le \lvert Q(r)\rvert$ for the orthogonal part
$y'$, which lies in $L_2$. -/
theorem exists_rootVector_orth (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {T : Finset (Fin n)}
    {i j : Fin n} (hs : OrthSplit (locGram Q v γ) T i j) :
    ∃ r : Fin n → Fv, IsRootVector Q L v r ∧ ∀ t ∈ T, qbil Q Fv r (basisVec γ t) = 0 := by
  classical
  have hmem : ∀ c ∈ std v, γ.val *ᵥ c ∈ (loc v L.1) := fun c hc => by rw [hγ]; exact ⟨c, hc, rfl⟩
  have hbasis : ∀ k : Fin n, γ.val *ᵥ Pi.single k 1 ∈ (loc v L.1) := fun k =>
    hmem _ (single_mem_std k (by simp))
  -- boundedness
  have hbound : ∃ B : ℤ, ∀ y ∈ (loc v L.1), Valued.v (Q.evalIn Fv y) ≤ exp B := by
    choose k hk using fun i j => exists_valued_le v (locGram Q v γ i j)
    set N : ℕ := Finset.univ.sup (fun p : Fin n × Fin n => k p.1 p.2) with hN
    obtain ⟨k2, hk2⟩ := exists_valued_le v (2⁻¹ : Fv)
    refine ⟨(k2 : ℤ) + N, fun y hy => ?_⟩
    rw [hγ, mem_locAct] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    have hc' := mem_std_iff.mp hc
    have hG : ∀ i j, Valued.v (locGram Q v γ i j) ≤ exp (N : ℤ) := fun i j =>
      (hk i j).trans (exp_le_exp.mpr (by
        exact_mod_cast Finset.le_sup (f := fun p : Fin n × Fin n => k p.1 p.2) (Finset.mem_univ (i, j))))
    have hdot : Valued.v (c ⬝ᵥ (locGram Q v γ *ᵥ c)) ≤ exp (N : ℤ) := by
      unfold dotProduct
      refine Valuation.map_sum_le _ fun i _ => ?_
      rw [map_mul]
      have hin : Valued.v ((locGram Q v γ *ᵥ c) i) ≤ exp (N : ℤ) := by
        unfold mulVec dotProduct
        refine Valuation.map_sum_le _ fun j _ => ?_
        rw [map_mul]
        calc _ ≤ exp (N : ℤ) * 1 := mul_le_mul' (hG i j) (hc' j)
          _ = _ := mul_one _
      calc _ ≤ 1 * exp (N : ℤ) := mul_le_mul' (hc' i) hin
        _ = _ := one_mul _
    have hQy : Q.evalIn Fv (γ.val *ᵥ c) = 2⁻¹ * (c ⬝ᵥ (locGram Q v γ *ᵥ c)) := by
      rw [← two_mul_evalIn_locGram]; field_simp
    rw [hQy, map_mul]
    calc Valued.v (2⁻¹ : Fv) * Valued.v (c ⬝ᵥ (locGram Q v γ *ᵥ c))
        ≤ exp (k2 : ℤ) * exp (N : ℤ) := mul_le_mul' hk2 hdot
      _ = _ := (exp_add _ _).symm
  -- some orthogonal vector of nonzero norm
  have hbt : ∀ k, k ∉ T → ∀ t ∈ T, qbil Q Fv (basisVec γ k) (basisVec γ t) = 0 := fun k hk t ht => by
    rw [qbil_basisVec]; exact hs.orth t ht k (fun h => hk (h ▸ ht))
  have hnz : ∃ y ∈ (loc v L.1), (∀ t ∈ T, qbil Q Fv y (basisVec γ t) = 0) ∧ Q.evalIn Fv y ≠ 0 := by
    by_contra hall
    push Not at hall
    have hbi : Q.evalIn Fv (basisVec γ i) = 0 := hall _ (hbasis i) (hbt i hs.iT)
    have hbj : Q.evalIn Fv (basisVec γ j) = 0 := hall _ (hbasis j) (hbt j hs.jT)
    have hbij : Q.evalIn Fv (basisVec γ i + basisVec γ j) = 0 :=
      hall _ ((loc v L.1).add_mem (hbasis i) (hbasis j)) (fun t ht => by
        rw [qbil_add_left, hbt i hs.iT t ht, hbt j hs.jT t ht, add_zero])
    have g1 : locGram Q v γ i i = 0 := by rw [← qbil_basisVec, qbil_self, hbi, mul_zero]
    have g2 : locGram Q v γ i j = 0 := by
      rw [← qbil_basisVec, qbil_eq_polar, hbij, hbi, hbj]; ring
    refine hs.det_ne (Matrix.det_eq_zero_of_column_eq_zero i fun m => ?_)
    rcases hs.cover m with hm | rfl | rfl
    · exact hs.orth' hm (fun h => hs.iT (h ▸ hm))
    · exact g1
    · rw [hs.symm_apply]; exact g2
  obtain ⟨B, hB⟩ := hbound
  obtain ⟨y0, hy0M, hy0t, hy00⟩ := hnz
  obtain ⟨k1, hk1⟩ := exists_valued_eq_exp v hy00
  obtain ⟨k0, ⟨x, hxM, hxt, hx0, hxk⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun k : ℤ => ∃ y ∈ (loc v L.1), (∀ t ∈ T, qbil Q Fv y (basisVec γ t) = 0) ∧
      Q.evalIn Fv y ≠ 0 ∧ Valued.v (Q.evalIn Fv y) = exp k)
    ⟨B, fun k ⟨y, hyM, _, _, hyk⟩ => by
      have := hB y hyM
      rw [hyk, exp_le_exp] at this
      exact this⟩
    ⟨k1, y0, hy0M, hy0t, hy00, hk1⟩
  have hle : ∀ z ∈ (loc v L.1), (∀ t ∈ T, qbil Q Fv z (basisVec γ t) = 0) →
      Valued.v (Q.evalIn Fv z) ≤ exp k0 := by
    intro z hz hzt
    by_cases hz0 : Q.evalIn Fv z = 0
    · rw [hz0, map_zero]; exact zero_le
    · obtain ⟨k', hk'⟩ := exists_valued_eq_exp v hz0
      rw [hk', exp_le_exp]
      exact hmax k' ⟨z, hz, hzt, hz0, hk'⟩
  refine ⟨x, ⟨hx0, ?_⟩, hxt⟩
  show locAct v (symm Q Fv x : GL (Fin n) Fv) (loc v L.1) = loc v L.1
  refine locAct_symm_eq hxM hx0 fun y hy => ?_
  have hxM' := hxM
  rw [hγ, mem_locAct] at hxM'
  obtain ⟨a, _, hxa⟩ := hxM'
  rw [hγ, mem_locAct] at hy
  obtain ⟨c, hc, rfl⟩ := hy
  set c' : Fin n → Fv := fun k => if k ∈ T then 0 else c k with hc'def
  have hc'std : c' ∈ std v := mem_std_iff.mpr fun k => by
    by_cases hk : k ∈ T
    · simp [hc'def, hk]
    · simp only [hc'def, hk, if_false]; exact (mem_std_iff.mp hc) k
  have hy'M := hmem c' hc'std
  have hy't : ∀ t ∈ T, qbil Q Fv (γ.val *ᵥ c') (basisVec γ t) = 0 := by
    intro t ht
    rw [qbil_vec_basisVec γ (hs.orth t ht)]; simp [hc'def, ht]
  have hat : ∀ t ∈ T, a t = 0 := by
    intro t ht
    have h := hxt t ht
    rw [← hxa, qbil_vec_basisVec γ (hs.orth t ht)] at h
    exact (mul_eq_zero.mp h).resolve_right (hs.diag_ne ht)
  have hGc : ∀ k, k ∉ T → (locGram Q v γ *ᵥ c) k = (locGram Q v γ *ᵥ c') k := by
    intro k hk
    unfold mulVec dotProduct
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : m ∈ T
    · have : locGram Q v γ k m = 0 := hs.orth m hm k (fun h => hk (h ▸ hm))
      simp [hc'def, hm, this]
    · simp [hc'def, hm]
  have hxy : qbil Q Fv x (γ.val *ᵥ c) = qbil Q Fv x (γ.val *ᵥ c') := by
    rw [← hxa, qbil_mulVec_locGram, qbil_mulVec_locGram]
    unfold dotProduct
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k ∈ T
    · rw [hat k hk, zero_mul, zero_mul]
    · rw [hGc k hk]
  rw [hxy, qbil_eq_polar, hxk]
  refine Valuation.map_sub_le _ (Valuation.map_sub_le _ (hle _ ((loc v L.1).add_mem hxM hy'M) ?_) hxk.le)
    (hle _ hy'M hy't)
  intro t ht
  rw [qbil_add_left, hxt t ht, hy't t ht, add_zero]

/-- **The relative binary base case**: if the complement of $T$ is a binary orthogonal summand $\{i, j\}$, every
$\sigma \in O(L_2)$ fixing the $b_t$ ($t \in T$) is a product of at most two reflections in root vectors orthogonal to
the $b_t$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (remark after Thm. 18: a binary orthogonal summand, relative version)"]
theorem fixGenerated_of_orthSplit (hQ : Q.Nondegenerate) (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v))
    {T : Finset (Fin n)} {i j : Fin n} (hs : OrthSplit (locGram Q v γ) T i j) : FixGenerated Q L v γ T := by
  intro σ hσL hfix
  have key : ∀ τ : orthGroup Q Fv, τ ∈ locStabV Q v L →
      (∀ t ∈ T, (τ : GL (Fin n) Fv).val *ᵥ basisVec γ t = basisVec γ t) → (τ : GL (Fin n) Fv).val.det = -1 →
      ∃ w, (IsRootVector Q L v w ∧ ∀ t ∈ T, qbil Q Fv w (basisVec γ t) = 0) ∧ τ = symm Q Fv w := by
    intro τ hτ hτfix hdet
    obtain ⟨w, hw, hτw, hwt⟩ := exists_reflection_of_improper hQ γ hs τ hτfix hdet
    exact ⟨w, ⟨⟨hw, hτw ▸ hτ⟩, hwt⟩, hτw⟩
  rcases Tamagawa.det_eq_one_or_neg_one Q hQ σ with h | h
  · obtain ⟨r, hr, hrt⟩ := exists_rootVector_orth γ hγ hs
    have hdet : ((σ * symm Q Fv r : orthGroup Q Fv) : GL (Fin n) Fv).val.det = -1 := by
      change ((σ : GL (Fin n) Fv).val * (symm Q Fv r : GL (Fin n) Fv).val).det = -1
      rw [det_mul, h, symm_det Q Fv hr.1, one_mul]
    have hfix' : ∀ t ∈ T, ((σ * symm Q Fv r : orthGroup Q Fv) : GL (Fin n) Fv).val *ᵥ basisVec γ t =
        basisVec γ t := by
      intro t ht
      change ((σ : GL (Fin n) Fv).val * (symm Q Fv r : GL (Fin n) Fv).val) *ᵥ basisVec γ t = basisVec γ t
      rw [← mulVec_mulVec, symm_mulVec_bil Q Fv hr.1, hrt t ht, zero_div, zero_smul, sub_zero, hfix t ht]
    obtain ⟨w, hw, hσw⟩ := key _ (mul_mem hσL hr.2) hfix' hdet
    refine ⟨[w, r], ?_, ?_⟩
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      exacts [hw, ⟨hr, hrt⟩]
    · have : σ = (σ * symm Q Fv r) * symm Q Fv r := by rw [mul_assoc, symm_mul_self, mul_one]
      rw [this, hσw]
      simp [symmProd]
  · obtain ⟨w, hw, hσw⟩ := key σ hσL hfix h
    exact ⟨[w], by simpa using hw, by simp [symmProd, hσw]⟩

end Lift

/-! ### Peeling chains ending in a binary remainder -/

section Chain2

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

/-- **The peeling shape with a binary remainder** (a **condition** on the Gram matrix $G$ of a basis $b = \gamma e$ of
$L_2$): as `PeelChain`, except that at the end at most **two** indices may be left outside $T$ (the remainder is an
orthogonal summand of rank $\le 2$, of any shape). Example: $\langle 1\rangle \perp 4K$ for any binary lattice $K$,
e.g. $\langle 1\rangle \perp \langle 4, 4\rangle$ or $\langle 1\rangle \perp 4H$. -/
def PeelChain2 (G : Matrix (Fin n) (Fin n) Fv) : Finset (Fin n) → List (Fin n) → Prop
  | T, [] => (Finset.univ \ T).card ≤ 2
  | T, k :: ks => k ∉ T ∧ (∀ m, m ≠ k → G m k = 0) ∧
      (∀ i i', i ∉ insert k T → i' ∉ insert k T → Valued.v (G i i') ≤ Valued.v (2 * G k k)) ∧
      PeelChain2 G (insert k T) ks

/-- **Peeling a chain with a binary remainder** gives the fixing condition for the set $T$ already peeled. -/
theorem fixGenerated_of_peelChain2 (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) :
    ∀ (ks : List (Fin n)) (T : Finset (Fin n)), (∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) →
      PeelChain2 (locGram Q v γ) T ks → FixGenerated Q L v γ T
  | [], T, hT, hc => by
    have hcard : (Finset.univ \ T).card ≤ 2 := hc
    rcases Nat.lt_or_ge (Finset.univ \ T).card 2 with hlt | hge
    · exact fixGenerated_of_peelChain hQ h2 γ hγ [] T hT (show (Finset.univ \ T).card ≤ 1 by omega)
    · obtain ⟨i, j, hij, hC⟩ := Finset.card_eq_two.mp (le_antisymm hcard hge)
      have hmem : ∀ x, x ∈ Finset.univ \ T ↔ x ∉ T := fun x => by simp
      have hiT : i ∉ T := (hmem i).mp (by rw [hC]; simp)
      have hjT : j ∉ T := (hmem j).mp (by rw [hC]; simp)
      refine fixGenerated_of_orthSplit hQ γ hγ (i := i) (j := j)
        ⟨locGram_transpose γ, locGram_det_ne_zero hQ γ, hT, fun x => ?_, hij, hiT, hjT⟩
      by_cases hx : x ∈ T
      · exact Or.inl hx
      · have := (hmem x).mpr hx
        rw [hC] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        exact Or.inr this
  | k :: ks, T, hT, ⟨hkT, hk, hd, hrest⟩ => by
    refine fixGenerated_peel hQ h2 γ hγ T k hkT hT hk hd
      (fixGenerated_of_peelChain2 hQ h2 γ hγ ks (insert k T) (fun t ht m hm => ?_) hrest)
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hk m hm
    · exact hT t ht m hm

/-- **Integral automorphisms are products of integral reflections for a peeling chain with a binary remainder**
(Conway–Sloane §9.5, p. 391, the remark after Theorem 18; $p = 2$). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (remark after Thm. 18: p = 2, peeling chain with a binary remainder)"]
theorem generatedByRootReflections_of_peelChain2 (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) (ks : List (Fin n))
    (hc : PeelChain2 (locGram Q v γ) ∅ ks) : GeneratedByRootReflections Q v L := by
  intro σ hσ
  obtain ⟨l, hl, h⟩ := fixGenerated_of_peelChain2 hQ h2 γ hγ ks ∅ (by simp) hc σ hσ (by simp)
  exact ⟨l, fun u hu => (hl u hu).1, h⟩

/-- **Theorem 18, "only if", for a peeling chain with a binary remainder** (Conway–Sloane §9.5, p. 391; $p = 2$). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': a peeling chain with a binary remainder)"]
theorem theorem18OnlyIf_of_peelChain2 (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) (ks : List (Fin n))
    (hc : PeelChain2 (locGram Q v γ) ∅ ks) : Theorem18OnlyIf Q L v hQ :=
  theorem18OnlyIf_of_generated hQ (generatedByRootReflections_of_peelChain2 hQ h2 γ hγ ks hc)

/-- **The $2$-adic shapes for which Theorem 18 ("only if") is proved, fifth version**: `Theorem18DyadicCovered4`, or
$L_2$ has a basis and a list of indices with the shape `PeelChain2`. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2: the 2-adic shapes proved in the library, fifth version)"]
def Theorem18DyadicCovered5 (Q : QuadForm ℚ n) (L : Lat ℚ n) (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  Theorem18DyadicCovered4 Q L v ∨ ∃ (γ : GL (Fin n) (v.adicCompletion ℚ)) (ks : List (Fin n)),
    loc v L.1 = locAct v γ (std v) ∧ PeelChain2 (locGram Q v γ) ∅ ks

/-- **Theorem 18, "only if", at $p = 2$ on the covered shapes, fifth version** (unconditional). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': the covered 2-adic shapes, fifth version)"]
theorem theorem18OnlyIf_of_covered5 (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (hc : Theorem18DyadicCovered5 Q L v) : Theorem18OnlyIf Q L v hQ := by
  rcases hc with hc | ⟨γ, ks, hγ, hks⟩
  · exact theorem18OnlyIf_of_covered4 hQ h2 hc
  · exact theorem18OnlyIf_of_peelChain2 hQ h2 γ hγ ks hks

end Chain2

/-- **Theorem 18 at $p = 2$, "only if", for the residual lattices, fifth version** (Conway–Sloane §9.5, p. 391,
"based on Theorem 81 of [Wat3]", G. L. Watson, *Integral Quadratic Forms*, 1960), as a **named statement**: for every
regular form $Q$ over $\mathbb Q$, lattice $L$ and the prime $v$ over $2$ such that $L_2$ is **not** of a shape covered
by `Theorem18DyadicCovered5`, every $2$-adically automorphous number is, up to squares, the product of the norms of an
even number of $2$-adic root vectors (`Theorem18OnlyIf`). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if', lattices outside the proved 2-adic shapes, fifth version; stated; Watson 1960, Thm. 81)"]
structure Theorem18DyadicResidual5 : Prop where
  exists_rootVectors : ∀ (n : ℕ) (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (L : Lat ℚ n)
    (v : HeightOneSpectrum (𝓞 ℚ)), (2 : 𝓞 ℚ) ∈ v.asIdeal → ¬ Theorem18DyadicCovered5 Q L v →
      Theorem18OnlyIf Q L v hQ

/-- **The fourth residual statement from the fifth.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': residual shapes from the fifth residual statement)"]
theorem theorem18DyadicResidual4_of_residual5 (h : Theorem18DyadicResidual5) : Theorem18DyadicResidual4 where
  exists_rootVectors n Q hQ L v h2 _ := by
    by_cases hs : Theorem18DyadicCovered5 Q L v
    · exact theorem18OnlyIf_of_covered5 hQ h2 hs
    · exact h.exists_rootVectors n Q hQ L v h2 hs

/-- **`Theorem18Dyadic` from the fifth residual statement.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if', conditional on the residual shapes, fifth version)"]
theorem theorem18Dyadic_of_residual5 (h : Theorem18DyadicResidual5) : Theorem18Dyadic :=
  theorem18Dyadic_of_residual4 (theorem18DyadicResidual4_of_residual5 h)

/-- **Conway–Sloane's Theorem 18 from the fifth residual statement.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (conditional on the residual 2-adic shapes, fifth version)"]
theorem theorem18Statement_of_residual5 (h : Theorem18DyadicResidual5) : Theorem18Statement :=
  theorem18Statement_of_residual4 (theorem18DyadicResidual4_of_residual5 h)

end QuadFormsKB.ConwaySloane
