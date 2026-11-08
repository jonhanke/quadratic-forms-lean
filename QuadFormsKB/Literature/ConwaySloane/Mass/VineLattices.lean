/-
# Conway–Sloane 1988, §10: splitting off the vectors of norm $1$

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §10, p. 274: every positive definite integral lattice is $L_r \oplus I_{n-r}$, where $L_r$ has
no vectors of norm $1$. The reason is that a vector $v$ with $v \cdot v = 1$ splits off: $L = \mathbb Zv \oplus v^\perp$.

**Conventions.** A lattice is its Gram matrix `A : Matrix (Fin n) (Fin n) ℤ` (`PosDefGram A`), with form
`LocalDensity.ofMatrixZ A`, $x \mapsto x^{\mathsf T}Ax$; $L \oplus I_1$ is `sumOne A`, $L \oplus I_r$ is `sumI A r`.
`Siegel.IntEquiv` is integral equivalence. Indices are 0-based.

**Proof of the splitting.** For symmetric $A$ and $v^{\mathsf T}Av = 1$ the functional $\varphi(x) = v^{\mathsf T}Ax$ is onto
$\mathbb Z$ ($\varphi(v) = 1$), so $\mathbb Z^{m+1} = \ker\varphi \oplus \mathbb Zv$. The kernel is free of rank $m$
(`Submodule.basisOfPid`); the matrix $P$ with the kernel basis in the first $m$ columns and $v$ in the last is invertible and
$P^{\mathsf T}AP = A' \oplus I_1$, where $A'$ is the Gram matrix of the kernel basis.

**Proves**
* `exists_congr_sumOne_of_norm_one`, `intEquiv_sumOne_of_norm_one`: a vector of norm $1$ splits off an $I_1$ summand.
* `intEquiv_sumOne`: integral equivalence is preserved by adjoining $I_1$.
* `sumOne_sumI`, `sumI_zero`, `PosDefGram.sumI`: calculus of $L \oplus I_r$.
* `exists_sumI_no_norm_one` (**§10, p. 274**): $A \cong L_r \oplus I_{n-r}$ with $L_r$ free of vectors of norm $1$.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemma3

set_option linter.unusedSectionVars false

open Matrix QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.LocalDensity QuadFormsKB.Cassels QuadFormsKB.Tamagawa.Frames

namespace QuadFormsKB.ConwaySloane.Mass

variable {n m : ℕ}

/-! ### Symmetry, congruence and positivity -/

/-- $x^{\mathsf T}Ay = y^{\mathsf T}Ax$ for symmetric $A$. -/
theorem dot_symm {A : Matrix (Fin n) (Fin n) ℤ} (hs : Aᵀ = A) (x y : Fin n → ℤ) :
    x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
  rw [dotProduct_mulVec, ← Matrix.vecMul_transpose, hs, dotProduct_comm]

/-- Positive definiteness is invariant under integral congruence. -/
theorem PosDefGram.of_congr {A B : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A) (g : GL (Fin n) ℤ)
    (h : g.valᵀ * A * g.val = B) : PosDefGram B := by
  subst h
  refine ⟨by simp [Matrix.transpose_mul, hA.1, Matrix.mul_assoc], fun x hx => ?_⟩
  set Q : Matrix (Fin n) (Fin n) ℚ := g.val.map (Int.castRingHom ℚ) with hQ
  have hG : gramQ (g.valᵀ * A * g.val) = Qᵀ * gramQ A * Q := by
    unfold gramQ
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have hQx : Q *ᵥ x ≠ 0 := by
    intro h0
    apply hx
    have h1 : (g⁻¹).val.map (Int.castRingHom ℚ) * Q = 1 := by
      rw [hQ, ← Matrix.map_mul, Units.inv_mul]
      simp
    have h2 : x = ((g⁻¹).val.map (Int.castRingHom ℚ) * Q) *ᵥ x := by rw [h1, Matrix.one_mulVec]
    rw [h2, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  have key : x ⬝ᵥ ((Qᵀ * gramQ A * Q) *ᵥ x) = (Q *ᵥ x) ⬝ᵥ (gramQ A *ᵥ (Q *ᵥ x)) := by
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec,
      Matrix.vecMul_transpose]
  rw [hG, key]
  exact hA.2 _ hQx

theorem sumOne_transpose {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) : (sumOne A)ᵀ = sumOne A := by
  rw [sumOne_eq, blockMat_transpose]; simp [hA]

/-- Conversely, $L \oplus I_1$ positive definite forces $L$ positive definite. -/
theorem posDefGram_of_sumOne {A : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram (sumOne A)) : PosDefGram A := by
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j
    have := congrFun (congrFun hA.1 (Fin.castAdd 1 i)) (Fin.castAdd 1 j)
    simpa [sumOne] using this
  · let x' : Fin (n + 1) → ℚ := Fin.addCases (motive := fun _ => ℚ) x (fun _ => 0)
    have hx' : x' ≠ 0 := by
      intro h0
      apply hx
      funext a
      have := congrFun h0 (Fin.castAdd 1 a)
      simpa [x'] using this
    have h := hA.2 x' hx'
    rw [gramQ_sumOne] at h
    have key : x' ⬝ᵥ (blockMat (gramQ A) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℚ) *ᵥ x')
        = (fun a => x' (Fin.castAdd 1 a)) ⬝ᵥ (gramQ A *ᵥ fun a => x' (Fin.castAdd 1 a))
          + (x' (Fin.natAdd n 0)) ^ 2 := by
      simp only [dotProduct, Fin.sum_univ_add, Fin.sum_univ_one, sumOne_mulVec_left, sumOne_mulVec_last]
      simp [sq]
    rw [key] at h
    have e1 : (fun a => x' (Fin.castAdd 1 a)) = x := by funext a; simp [x']
    have e2 : x' (Fin.natAdd n 0) = 0 := by simp [x']
    rw [e1, e2] at h
    simpa using h

/-! ### Splitting off a vector of norm $1$ -/

/-- **A vector of norm $1$ splits off** (§10, p. 274, matrix form): if $A$ is symmetric and $v^{\mathsf T}Av = 1$ then
$A$ is $\mathbb Z$-congruent to $A' \oplus I_1$ for some $A'$ (the Gram matrix of $v^\perp$). -/
theorem exists_congr_sumOne_of_norm_one {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hs : Aᵀ = A)
    {v : Fin (m + 1) → ℤ} (hv : v ⬝ᵥ (A *ᵥ v) = 1) :
    ∃ A' : Matrix (Fin m) (Fin m) ℤ, CongrIn ℤ A (sumOne A') := by
  classical
  let φ : (Fin (m + 1) → ℤ) →ₗ[ℤ] ℤ :=
    { toFun := fun x => v ⬝ᵥ (A *ᵥ x)
      map_add' := fun x y => by simp [Matrix.mulVec_add, dotProduct_add]
      map_smul' := fun c x => by
        show v ⬝ᵥ (A *ᵥ (c • x)) = c • (v ⬝ᵥ (A *ᵥ x))
        rw [Matrix.mulVec_smul, dotProduct_smul] }
  have hφ : ∀ x, φ x = v ⬝ᵥ (A *ᵥ x) := fun _ => rfl
  have hφv : φ v = 1 := hv
  have hmem : ∀ x : Fin (m + 1) → ℤ, x - φ x • v ∈ LinearMap.ker φ := by
    intro x
    rw [LinearMap.mem_ker, map_sub, map_smul, hφv]
    simp
  let e : (Fin (m + 1) → ℤ) ≃ₗ[ℤ] (LinearMap.ker φ) × ℤ :=
    { toFun := fun x => (⟨x - φ x • v, hmem x⟩, φ x)
      map_add' := fun x y => by
        refine Prod.ext (Subtype.ext ?_) (map_add φ x y)
        show (x + y) - φ (x + y) • v = (x - φ x • v) + (y - φ y • v)
        rw [map_add, add_smul]
        abel
      map_smul' := fun c x => by
        refine Prod.ext (Subtype.ext ?_) (map_smul φ c x)
        show (c • x) - φ (c • x) • v = c • (x - φ x • v)
        rw [map_smul, smul_eq_mul, smul_sub, mul_smul]
      invFun := fun p => (p.1 : Fin (m + 1) → ℤ) + p.2 • v
      left_inv := fun x => by simp
      right_inv := fun p => by
        obtain ⟨⟨y, hy⟩, c⟩ := p
        have hy' : φ y = 0 := hy
        refine Prod.ext (Subtype.ext ?_) ?_
        · show y + c • v - φ (y + c • v) • v = y
          rw [map_add, map_smul, hy', hφv]; simp
        · show φ (y + c • v) = c
          rw [map_add, map_smul, hy', hφv]; simp }
  obtain ⟨k, b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin (m + 1))) (LinearMap.ker φ)
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  have hk : k = m := by
    have h1 := LinearEquiv.finrank_eq e
    simp [Module.finrank_prod, Module.finrank_eq_card_basis b] at h1
    omega
  have hk' : m = k := hk.symm
  subst hk'
  let col : Fin (m + 1) → (Fin (m + 1) → ℤ) :=
    fun j => Fin.addCases (motive := fun _ => Fin (m + 1) → ℤ) (fun a => (b a : Fin (m + 1) → ℤ)) (fun _ => v) j
  let P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ := Matrix.of fun i j => col j i
  have hsurj : Function.Surjective P.mulVec := by
    intro y
    have hz := hmem y
    let c := b.repr ⟨y - φ y • v, hz⟩
    refine ⟨Fin.addCases (motive := fun _ => ℤ) (fun a => c a) (fun _ => φ y), ?_⟩
    funext i
    have hs := congrArg (fun w : LinearMap.ker φ => (w : Fin (m + 1) → ℤ) i) (b.sum_repr ⟨y - φ y • v, hz⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Fin.sum_univ_one, P, col, Matrix.of_apply,
      Fin.addCases_left, Fin.addCases_right]
    have : y i = (y - φ y • v) i + φ y * v i := by simp
    rw [this, ← hs]
    simp only [c]
    congr 1
    · exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    · simp [mul_comm]
  obtain ⟨g, hg⟩ := Matrix.mulVec_surjective_iff_isUnit.mp hsurj
  refine ⟨Matrix.of fun i j => (b i : Fin (m + 1) → ℤ) ⬝ᵥ (A *ᵥ (b j : Fin (m + 1) → ℤ)), g, ?_⟩
  have hb0 : ∀ a, v ⬝ᵥ (A *ᵥ (b a : Fin (m + 1) → ℤ)) = 0 := fun a => (b a).2
  have key : ∀ i j, (Pᵀ * A * P) i j = col i ⬝ᵥ (A *ᵥ col j) := fun i j => by
    rw [Matrix.mul_assoc, Matrix.mul_apply']; rfl
  show g.valᵀ * A * g.val = _
  rw [show g.val = P from hg]
  ext i j
  rw [key]
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;> refine Fin.addCases (fun a' => ?_) (fun a' => ?_) j
  · simp [col, sumOne]
  · simp [col, sumOne, Matrix.zero_apply]
    rw [dot_symm hs]
    exact hb0 a
  · simp [col, sumOne, Matrix.zero_apply]
    exact hb0 a'
  · simp [col, sumOne, oneGram, Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero a', hv]

/-- **A vector of norm $1$ splits off** (§10, p. 274): a positive definite lattice with a vector of norm $1$ is
integrally equivalent to $L' \oplus I_1$ with $L'$ positive definite. -/
theorem intEquiv_sumOne_of_norm_one {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hA : PosDefGram A)
    {v : Fin (m + 1) → ℤ} (hv : v ⬝ᵥ (A *ᵥ v) = 1) :
    ∃ A' : Matrix (Fin m) (Fin m) ℤ, PosDefGram A' ∧ IntEquiv (ofMatrixZ A) (ofMatrixZ (sumOne A')) := by
  obtain ⟨A', g, hg⟩ := exists_congr_sumOne_of_norm_one hA.1 hv
  have h1 : PosDefGram (sumOne A') := hA.of_congr g hg
  have h2 : PosDefGram A' := posDefGram_of_sumOne h1
  refine ⟨A', h2, ?_⟩
  exact (isometricGL_gramForm_iff hA.1 h1.1).mpr ⟨g, hg⟩

/-! ### Adjoining $I_r$ -/

/-- Congruence passes to $\oplus\, I_r$. -/
theorem congrIn_blockMat_one {M N : Matrix (Fin n) (Fin n) ℤ} (r : ℕ) (h : CongrIn ℤ M N) :
    CongrIn ℤ (blockMat M 0 0 (1 : Matrix (Fin r) (Fin r) ℤ)) (blockMat N 0 0 (1 : Matrix (Fin r) (Fin r) ℤ)) := by
  obtain ⟨g, hg⟩ := h
  let u : GL (Fin (n + r)) ℤ :=
    ⟨blockMat g.val 0 0 1, blockMat g⁻¹.val 0 0 1,
      by rw [blockMat_mul]; simp [blockMat_one],
      by rw [blockMat_mul]; simp [blockMat_one]⟩
  refine ⟨u, ?_⟩
  show (blockMat g.val 0 0 1)ᵀ * blockMat M 0 0 1 * blockMat g.val 0 0 1 = _
  rw [blockMat_transpose, blockMat_mul, blockMat_mul, ← hg]
  simp [Matrix.mul_assoc]

/-- **Integral equivalence is preserved by adjoining $I_1$.** -/
theorem intEquiv_sumOne {A B : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hB : Bᵀ = B)
    (h : IntEquiv (ofMatrixZ A) (ofMatrixZ B)) :
    IntEquiv (ofMatrixZ (sumOne A)) (ofMatrixZ (sumOne B)) :=
  (isometricGL_gramForm_iff (sumOne_transpose hA) (sumOne_transpose hB)).mpr
    (congrIn_blockMat_one 1 ((isometricGL_gramForm_iff hA hB).mp h))

/-- Entries of $L \oplus I_r$: $L_{ij}$ if both indices are $< n$, else $\delta_{ij}$. -/
theorem sumI_apply (L : Matrix (Fin n) (Fin n) ℤ) (r : ℕ) (i j : Fin (n + r)) :
    sumI L r i j = if h : i.val < n ∧ j.val < n then L ⟨i, h.1⟩ ⟨j, h.2⟩ else if i = j then 1 else 0 := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> refine Fin.addCases (fun a' => ?_) (fun b' => ?_) j
  · simp [sumI]
  · have := castAdd_ne_natAdd a b'
    simp [sumI, this]
  · have := (castAdd_ne_natAdd a' b).symm
    simp [sumI, this]
  · simp [sumI, Matrix.one_apply]

/-- $L \oplus I_0 = L$. -/
theorem sumI_zero (L : Matrix (Fin n) (Fin n) ℤ) : sumI L 0 = L := by
  ext i j
  rw [sumI_apply]
  simp

/-- $(L \oplus I_k) \oplus I_1 = L \oplus I_{k+1}$. -/
theorem sumOne_sumI (L : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) : sumOne (sumI L k) = sumI L (k + 1) := by
  ext i j
  show sumI (sumI L k) 1 i j = sumI L (k + 1) i j
  simp only [sumI_apply]
  by_cases hi : i.val < n + k <;> by_cases hj : j.val < n + k <;> simp [hi, hj, Fin.ext_iff] <;> intro hp hq <;> omega

/-- $L \oplus I_k$ is positive definite when $L$ is. -/
theorem PosDefGram.sumI {L : Matrix (Fin n) (Fin n) ℤ} (hL : PosDefGram L) (k : ℕ) : PosDefGram (sumI L k) := by
  induction k with
  | zero => rw [sumI_zero]; exact hL
  | succ k ih => rw [← sumOne_sumI]; exact ih.sumOne

/-- Reindexing along `finCongr` of a trivial equality is the identity. -/
theorem reindex_finCongr_rfl {a : ℕ} (h : a = a) (M : Matrix (Fin a) (Fin a) ℤ) :
    M.reindex (finCongr h) (finCongr h) = M := by
  ext i j; simp

/-- **§10, p. 274**: every positive definite integral lattice is $L_r \oplus I_{n-r}$ with $L_r$ free of vectors of norm $1$. -/
theorem exists_sumI_no_norm_one {A : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A) :
    ∃ (r k : ℕ) (h : r + k = n) (L : Matrix (Fin r) (Fin r) ℤ), PosDefGram L ∧ (∀ x, x ⬝ᵥ (L *ᵥ x) ≠ 1) ∧
      IntEquiv (ofMatrixZ A) (ofMatrixZ ((sumI L k).reindex (finCongr h) (finCongr h))) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h1 : ∀ x : Fin n → ℤ, x ⬝ᵥ (A *ᵥ x) ≠ 1
    · refine ⟨n, 0, rfl, A, hA, h1, ?_⟩
      have : (sumI A 0).reindex (finCongr (rfl : n + 0 = n)) (finCongr (rfl : n + 0 = n)) = A := by
        ext i j
        rw [Matrix.reindex_apply, Matrix.submatrix_apply, sumI_apply]
        simp
      rw [this]
      exact IsometricGL.refl _
    · push Not at h1
      obtain ⟨v, hv⟩ := h1
      cases n with
      | zero => simp at hv
      | succ m =>
        obtain ⟨A', hA', e⟩ := intEquiv_sumOne_of_norm_one hA hv
        obtain ⟨r, k, h, L, hL, hno, e'⟩ := ih m (Nat.lt_succ_self m) hA'
        subst h
        rw [reindex_finCongr_rfl] at e'
        have hsym : (sumI L k)ᵀ = sumI L k := (hL.sumI k).1
        refine ⟨r, k + 1, rfl, L, hL, hno, ?_⟩
        rw [reindex_finCongr_rfl, ← sumOne_sumI]
        exact e.trans (intEquiv_sumOne hA'.1 hsym e')

end QuadFormsKB.ConwaySloane.Mass

