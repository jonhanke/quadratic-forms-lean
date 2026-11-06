/-
# Conway–Sloane 1988, §10: the automorphism group of $L \oplus I_r$ (the "vines")

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §10, p. 275: "The mass of $L_k \oplus I_r$ is obtained by dividing the mass of
$L_k \oplus I_{r-1}$ by $2r$", for $L_k$ containing no vectors of norm $1$.

The mass is $\sum 1/|\mathrm{Aut}|$ over the classes of a genus, and adjoining $I_r$ gives a bijection of the classes of
the genera of $L_k$ and of $L_k \oplus I_r$ with $|\mathrm{Aut}(L \oplus I_r)| = 2^r r!\,|\mathrm{Aut}(L)|$. This file proves that
statement about automorphism groups, which is the arithmetic content of the sentence.

**Conventions.** A lattice is a positive definite integral Gram matrix `A : Matrix (Fin n) (Fin n) ℤ` (`PosDefGram A`),
with quadratic form `LocalDensity.ofMatrixZ A`, $x \mapsto x^{\mathsf T}Ax$. "No vector of norm $1$" is
`∀ x, x ⬝ᵥ (A *ᵥ x) ≠ 1`. $L \oplus I_r$ is the Gram matrix `sumI A r = blockMat A 0 0 1` in `Fin (n + r)`; the first $n$
coordinates (`Fin.castAdd`) are those of $L$, the last $r$ (`Fin.natAdd`) those of $I_r$. $\mathrm{Aut}$ is the library's
`Siegel.Aut` (the subgroup of $\mathrm{GL}_n(\mathbb Z)$ preserving the form; improper automorphisms included).

**Proves**
* `norm_one_vectors`: the vectors of norm $1$ of $L \oplus I_r$ are exactly $\pm e_i$ in the $I_r$ part.
* `card_aut_sumI`: $|\mathrm{Aut}(L \oplus I_r)| = 2^r\, r!\,|\mathrm{Aut}(L)|$ (as `Nat.card`).
* `card_aut_sumI_succ`: $|\mathrm{Aut}(L \oplus I_{r+1})| = 2(r+1)\,|\mathrm{Aut}(L \oplus I_r)|$.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemmas

open Matrix QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.LocalDensity QuadFormsKB.Tamagawa.Frames

namespace QuadFormsKB.ConwaySloane.Mass

variable {n r : ℕ}

/-- $L \oplus I_r$: the Gram matrix `blockMat A 0 0 1` in `Fin (n + r)`. -/
def sumI (A : Matrix (Fin n) (Fin n) ℤ) (r : ℕ) : Matrix (Fin (n + r)) (Fin (n + r)) ℤ :=
  blockMat A 0 0 (1 : Matrix (Fin r) (Fin r) ℤ)

theorem blockMat_mulVec_castAdd {R : Type*} [CommRing R] (P : Matrix (Fin n) (Fin n) R)
    (D : Matrix (Fin r) (Fin r) R) (v : Fin (n + r) → R) (i : Fin n) :
    (blockMat P 0 0 D *ᵥ v) (Fin.castAdd r i) = (P *ᵥ fun a => v (Fin.castAdd r a)) i := by
  simp [mulVec, dotProduct, Fin.sum_univ_add]

theorem blockMat_mulVec_natAdd {R : Type*} [CommRing R] (P : Matrix (Fin n) (Fin n) R)
    (D : Matrix (Fin r) (Fin r) R) (v : Fin (n + r) → R) (j : Fin r) :
    (blockMat P 0 0 D *ᵥ v) (Fin.natAdd n j) = (D *ᵥ fun b => v (Fin.natAdd n b)) j := by
  simp [mulVec, dotProduct, Fin.sum_univ_add]

/-- $x^{\mathsf T}(A\oplus D)x = x_A^{\mathsf T}Ax_A + x_I^{\mathsf T}Dx_I$. -/
theorem dot_blockMat (P : Matrix (Fin n) (Fin n) ℤ) (D : Matrix (Fin r) (Fin r) ℤ) (x y : Fin (n + r) → ℤ) :
    x ⬝ᵥ (blockMat P 0 0 D *ᵥ y) = (fun a => x (Fin.castAdd r a)) ⬝ᵥ (P *ᵥ fun a => y (Fin.castAdd r a))
      + (fun b => x (Fin.natAdd n b)) ⬝ᵥ (D *ᵥ fun b => y (Fin.natAdd n b)) := by
  simp only [dotProduct, Fin.sum_univ_add, blockMat_mulVec_castAdd, blockMat_mulVec_natAdd]

theorem norm_sumI (A : Matrix (Fin n) (Fin n) ℤ) (x : Fin (n + r) → ℤ) :
    x ⬝ᵥ (sumI A r *ᵥ x) = (fun a => x (Fin.castAdd r a)) ⬝ᵥ (A *ᵥ fun a => x (Fin.castAdd r a))
      + ∑ i, (x (Fin.natAdd n i)) ^ 2 := by
  rw [sumI, dot_blockMat]
  simp [dotProduct, sq]

theorem PosDefGram.pos_int {A : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A) {x : Fin n → ℤ} (hx : x ≠ 0) :
    0 < x ⬝ᵥ (A *ᵥ x) := by
  have hx' : (fun i => (x i : ℚ)) ≠ 0 := by
    intro h; apply hx; funext i; have := congrFun h i; simpa using this
  have h := hA.2 _ hx'
  have e : (fun i => (x i : ℚ)) ⬝ᵥ (gramQ A *ᵥ fun i => (x i : ℚ)) = ((x ⬝ᵥ (A *ᵥ x) : ℤ) : ℚ) := by
    rw [← cast_mulVec]; simp [dotProduct]
  rw [e] at h
  exact_mod_cast h

theorem PosDefGram.nonneg_int {A : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A) (x : Fin n → ℤ) :
    0 ≤ x ⬝ᵥ (A *ᵥ x) := by
  by_cases hx : x = 0
  · subst hx; simp
  · exact (hA.pos_int hx).le

theorem castAdd_ne_natAdd (a : Fin n) (j : Fin r) : Fin.castAdd r a ≠ Fin.natAdd n j := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem sum_sq_eq_one (f : Fin r → ℤ) (h : ∑ i, f i ^ 2 = 1) :
    ∃ j, (f j = 1 ∨ f j = -1) ∧ ∀ i, i ≠ j → f i = 0 := by
  have : ∃ j, f j ≠ 0 := by
    by_contra hc
    push_neg at hc
    simp [hc] at h
  obtain ⟨j, hj⟩ := this
  have hle : f j ^ 2 ≤ 1 := by
    rw [← h]
    exact Finset.single_le_sum (f := fun i => f i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  have hpos : 0 < f j ^ 2 := by positivity
  have h1 : f j ^ 2 = 1 := by omega
  refine ⟨j, ?_, fun i hi => ?_⟩
  · have : (f j - 1) * (f j + 1) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  · have hsub : ∑ k ∈ ({i, j} : Finset (Fin r)), f k ^ 2 ≤ ∑ k, f k ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => sq_nonneg _)
    rw [Finset.sum_pair hi, h, h1] at hsub
    have : f i ^ 2 = 0 := by nlinarith [sq_nonneg (f i)]
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this

/-- **The vectors of norm $1$ of $L \oplus I_r$** (§10, p. 275) are exactly $\pm e_i$, $e_i$ the basis vectors of the $I_r$
part, when $L$ is positive definite with no vector of norm $1$. -/
@[kb "conwaysloane1988" "§10, p. 275 (vines)"]
theorem norm_one_vectors {A : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A) (h1 : ∀ x, x ⬝ᵥ (A *ᵥ x) ≠ 1)
    (x : Fin (n + r) → ℤ) :
    x ⬝ᵥ (sumI A r *ᵥ x) = 1 ↔ ∃ (j : Fin r) (s : ℤ), (s = 1 ∨ s = -1) ∧ x = s • Pi.single (Fin.natAdd n j) 1 := by
  constructor
  · intro hx
    rw [norm_sumI] at hx
    set xA : Fin n → ℤ := fun a => x (Fin.castAdd r a) with hxA
    have hS : 0 ≤ ∑ i, (x (Fin.natAdd n i)) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hq0 := hA.nonneg_int xA
    have hq1 := h1 xA
    have hq : xA ⬝ᵥ (A *ᵥ xA) = 0 := by omega
    have hxA0 : xA = 0 := by
      by_contra hne
      have := hA.pos_int hne
      omega
    have hS1 : ∑ i, (x (Fin.natAdd n i)) ^ 2 = 1 := by omega
    obtain ⟨j, hj, hothers⟩ := sum_sq_eq_one (fun i => x (Fin.natAdd n i)) hS1
    refine ⟨j, x (Fin.natAdd n j), hj, ?_⟩
    funext i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · have := congrFun hxA0 a
      have h2 : x (Fin.castAdd r a) = 0 := by simpa [hxA] using this
      simp [Pi.single_apply, castAdd_ne_natAdd, h2]
    · by_cases hb : b = j
      · subst hb; simp
      · simp [Pi.single_apply, hb, hothers b hb]
  · rintro ⟨j, s, hs, rfl⟩
    rw [norm_sumI]
    have hz : (fun a => (s • (Pi.single (Fin.natAdd n j) 1 : Fin (n + r) → ℤ)) (Fin.castAdd r a)) = 0 := by
      funext a
      simp [Pi.single_apply, castAdd_ne_natAdd]
    rw [hz]
    simp only [Matrix.mulVec_zero, dotProduct_zero, zero_add]
    have : ∀ i : Fin r, ((s • (Pi.single (Fin.natAdd n j) 1 : Fin (n + r) → ℤ)) (Fin.natAdd n i)) ^ 2
        = if i = j then 1 else 0 := by
      intro i
      by_cases hij : i = j
      · subst hij; rcases hs with rfl | rfl <;> simp
      · simp [Pi.single_apply, hij]
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    simp

/-! ### Signed permutation matrices -/

/-- The sign $+1$ (`false`) or $-1$ (`true`). -/
def sgn (c : Bool) : ℤ := if c then -1 else 1

theorem sgn_sq (c : Bool) : sgn c * sgn c = 1 := by cases c <;> simp [sgn]

theorem sgn_ne_zero (c : Bool) : sgn c ≠ 0 := by cases c <;> simp [sgn]

theorem sgn_eq (c : Bool) : sgn c = 1 ∨ sgn c = -1 := by cases c <;> simp [sgn]

/-- **The signed permutation matrix** sending $e_j \mapsto \operatorname{sgn}(b_j)\,e_{\sigma(j)}$. -/
def Pm (σ : Equiv.Perm (Fin r)) (b : Fin r → Bool) : Matrix (Fin r) (Fin r) ℤ :=
  Matrix.of fun i j => if i = σ j then sgn (b j) else 0

theorem Pm_mulVec (σ : Equiv.Perm (Fin r)) (b : Fin r → Bool) (y : Fin r → ℤ) (i : Fin r) :
    (Pm σ b *ᵥ y) i = sgn (b (σ.symm i)) * y (σ.symm i) := by
  simp only [mulVec, dotProduct, Pm, Matrix.of_apply]
  rw [Finset.sum_eq_single (σ.symm i)]
  · simp
  · intro j _ hj
    have : i ≠ σ j := fun h => hj (by rw [h]; simp)
    simp [this]
  · simp

theorem Pm_mul_transpose (σ : Equiv.Perm (Fin r)) (b : Fin r → Bool) : Pm σ b * (Pm σ b)ᵀ = 1 := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Pm, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (σ.symm i)]
  · by_cases hik : i = k
    · subst hik; simp [sgn_sq]
    · have : k ≠ σ (σ.symm i) := by simpa using fun h => hik h.symm
      simp [hik]
      exact fun h => absurd h.symm hik
  · intro j _ hj
    have : i ≠ σ j := fun h => hj (by rw [h]; simp)
    simp [this]
  · simp

theorem Pm_transpose_mul (σ : Equiv.Perm (Fin r)) (b : Fin r → Bool) : (Pm σ b)ᵀ * Pm σ b = 1 := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Pm, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (σ i)]
  · by_cases hik : i = k
    · subst hik; simp [sgn_sq]
    · have : σ i ≠ σ k := fun h => hik (σ.injective h)
      simp [hik, this]
  · intro j _ hj
    simp [hj]
  · simp

theorem sum_sq_Pm (σ : Equiv.Perm (Fin r)) (b : Fin r → Bool) (y : Fin r → ℤ) :
    ∑ i, ((Pm σ b *ᵥ y) i) ^ 2 = ∑ i, (y i) ^ 2 := by
  simp only [Pm_mulVec]
  have : ∀ i, (sgn (b (σ.symm i)) * y (σ.symm i)) ^ 2 = (y (σ.symm i)) ^ 2 := fun i => by
    rw [mul_pow, sq (sgn _), sgn_sq, one_mul]
  simp only [this]
  exact Equiv.sum_comp σ.symm (fun i => (y i) ^ 2)

/-! ### The map $\mathrm{Aut}(L) \times (\text{signed permutations}) \to \mathrm{Aut}(L \oplus I_r)$ -/

theorem blockMat_diag_mul {R : Type*} [CommRing R] (P P' : Matrix (Fin n) (Fin n) R)
    (D D' : Matrix (Fin r) (Fin r) R) :
    blockMat P 0 0 D * blockMat P' 0 0 D' = blockMat (P * P') 0 0 (D * D') := by
  rw [blockMat_mul]; simp

theorem mem_Aut_iff (Q : QuadForm ℤ n) (g : GL (Fin n) ℤ) :
    g ∈ Aut Q ↔ ∀ x, Q.eval (g.val *ᵥ x) = Q.eval x := Iff.rfl

/-- The block diagonal automorphism $h \oplus P_{\sigma,b}$. -/
def autProd (h : GL (Fin n) ℤ) (σ : Equiv.Perm (Fin r)) (b : Fin r → Bool) : GL (Fin (n + r)) ℤ where
  val := blockMat h.val 0 0 (Pm σ b)
  inv := blockMat (h⁻¹).val 0 0 (Pm σ b)ᵀ
  val_inv := by
    rw [blockMat_diag_mul, Units.mul_inv, Pm_mul_transpose]; exact blockMat_one
  inv_val := by
    rw [blockMat_diag_mul, Units.inv_mul, Pm_transpose_mul]; exact blockMat_one

theorem autProd_val (h : GL (Fin n) ℤ) (σ : Equiv.Perm (Fin r)) (b : Fin r → Bool) :
    (autProd h σ b).val = blockMat h.val 0 0 (Pm σ b) := rfl

theorem autProd_mem {A : Matrix (Fin n) (Fin n) ℤ} {h : GL (Fin n) ℤ} (hh : h ∈ Aut (ofMatrixZ A))
    (σ : Equiv.Perm (Fin r)) (b : Fin r → Bool) : autProd h σ b ∈ Aut (ofMatrixZ (sumI A r)) := by
  rw [mem_Aut_iff] at hh ⊢
  intro x
  rw [eval_ofMatrixZ, eval_ofMatrixZ, norm_sumI, norm_sumI]
  have e1 : (fun a => ((autProd h σ b).val *ᵥ x) (Fin.castAdd r a)) = h.val *ᵥ (fun a => x (Fin.castAdd r a)) :=
    funext fun a => blockMat_mulVec_castAdd _ _ _ _
  have e2 : ∀ i, ((autProd h σ b).val *ᵥ x) (Fin.natAdd n i) = (Pm σ b *ᵥ fun j => x (Fin.natAdd n j)) i :=
    fun i => blockMat_mulVec_natAdd _ _ _ _
  rw [e1]
  simp only [e2]
  rw [sum_sq_Pm]
  have := hh (fun a => x (Fin.castAdd r a))
  rw [eval_ofMatrixZ, eval_ofMatrixZ] at this
  rw [this]

theorem Pm_inj {σ σ' : Equiv.Perm (Fin r)} {b b' : Fin r → Bool} (h : Pm σ b = Pm σ' b') :
    σ = σ' ∧ b = b' := by
  have key : ∀ j, σ j = σ' j := by
    intro j
    have := congrFun (congrFun h (σ j)) j
    simp only [Pm, Matrix.of_apply, if_true] at this
    by_contra hne
    rw [if_neg hne] at this
    exact sgn_ne_zero _ this
  have hσ : σ = σ' := Equiv.ext key
  refine ⟨hσ, funext fun j => ?_⟩
  have := congrFun (congrFun h (σ j)) j
  simp only [Pm, Matrix.of_apply, if_true] at this
  rw [if_pos (key j)] at this
  cases hb : b j <;> cases hb' : b' j <;> simp_all [sgn]

/-- The map $\mathrm{Aut}(L) \times (\mathrm{Sym}_r \times \{\pm1\}^r) \to \mathrm{Aut}(L \oplus I_r)$. -/
def autMap (A : Matrix (Fin n) (Fin n) ℤ) (r : ℕ) :
    (Aut (ofMatrixZ A)) × (Equiv.Perm (Fin r) × (Fin r → Bool)) → Aut (ofMatrixZ (sumI A r)) :=
  fun p => ⟨autProd p.1.1 p.2.1 p.2.2, autProd_mem p.1.2 _ _⟩

theorem autMap_injective (A : Matrix (Fin n) (Fin n) ℤ) (r : ℕ) : Function.Injective (autMap A r) := by
  rintro ⟨⟨h, hh⟩, σ, b⟩ ⟨⟨h', hh'⟩, σ', b'⟩ heq
  have h1 : (autProd h σ b).val = (autProd h' σ' b').val := by
    have := congrArg (fun p : Aut (ofMatrixZ (sumI A r)) => p.1.val) heq
    exact this
  rw [autProd_val, autProd_val] at h1
  obtain ⟨e1, -, -, e2⟩ := blockMat_inj h1
  obtain ⟨e3, e4⟩ := Pm_inj e2
  have : h = h' := Units.ext e1
  subst this; subst e3; subst e4
  rfl

/-! ### Surjectivity -/

theorem bil_of_norm {m : ℕ} {M G : Matrix (Fin m) (Fin m) ℤ} (hM : Mᵀ = M)
    (hG : ∀ x, (G *ᵥ x) ⬝ᵥ (M *ᵥ (G *ᵥ x)) = x ⬝ᵥ (M *ᵥ x)) (x y : Fin m → ℤ) :
    (G *ᵥ x) ⬝ᵥ (M *ᵥ (G *ᵥ y)) = x ⬝ᵥ (M *ᵥ y) := by
  have polar : ∀ u v : Fin m → ℤ, (u + v) ⬝ᵥ (M *ᵥ (u + v)) =
      u ⬝ᵥ (M *ᵥ u) + v ⬝ᵥ (M *ᵥ v) + 2 * (u ⬝ᵥ (M *ᵥ v)) := by
    intro u v
    have hvu : v ⬝ᵥ (M *ᵥ u) = u ⬝ᵥ (M *ᵥ v) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM, dotProduct_comm]
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hvu]
    ring
  have h1 := polar (G *ᵥ x) (G *ᵥ y)
  have h2 := polar x y
  rw [← Matrix.mulVec_add, hG, hG x, hG y] at h1
  linarith

theorem single_dot_sumI (A : Matrix (Fin n) (Fin n) ℤ) (k : Fin r) (y : Fin (n + r) → ℤ) :
    (Pi.single (Fin.natAdd n k) 1 : Fin (n + r) → ℤ) ⬝ᵥ (sumI A r *ᵥ y) = y (Fin.natAdd n k) := by
  rw [single_dotProduct, one_mul, sumI, blockMat_mulVec_natAdd]
  simp

theorem Pm_apply_self (σ : Equiv.Perm (Fin r)) (b : Fin r → Bool) (j : Fin r) :
    Pm σ b (σ j) j = sgn (b j) := by simp [Pm]

theorem sumI_symm {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) : (sumI A r)ᵀ = sumI A r := by
  unfold sumI; rw [blockMat_transpose]; simp [hA]

theorem natAdd_inj_iff (i j : Fin r) : (Fin.natAdd n i = Fin.natAdd n j) ↔ i = j := by
  constructor
  · intro h; have := congrArg Fin.val h; simp at this; exact Fin.ext this
  · rintro rfl; rfl

theorem autMap_surjective {A : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A) (h1 : ∀ x, x ⬝ᵥ (A *ᵥ x) ≠ 1)
    (r : ℕ) : Function.Surjective (autMap A r) := by
  classical
  rintro ⟨g, hg⟩
  set G := g.val with hGdef
  have hg' : ∀ x, (G *ᵥ x) ⬝ᵥ (sumI A r *ᵥ (G *ᵥ x)) = x ⬝ᵥ (sumI A r *ᵥ x) := fun x => by
    have := hg x
    rwa [eval_ofMatrixZ, eval_ofMatrixZ] at this
  have hbil := bil_of_norm (sumI_symm hA.1) hg'
  -- columns of the I_r part
  have hcol : ∀ j : Fin r, ∃ k : Fin r, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      G *ᵥ Pi.single (Fin.natAdd n j) 1 = s • Pi.single (Fin.natAdd n k) 1 := by
    intro j
    have hn : (Pi.single (Fin.natAdd n j) 1 : Fin (n + r) → ℤ) ⬝ᵥ
        (sumI A r *ᵥ Pi.single (Fin.natAdd n j) 1) = 1 :=
      (norm_one_vectors hA h1 _).2 ⟨j, 1, Or.inl rfl, by simp⟩
    obtain ⟨k, s, hs, hx⟩ := (norm_one_vectors hA h1 _).1 (by rw [hg']; exact hn)
    exact ⟨k, s, hs, hx⟩
  choose κ sg hsg hcolκ using hcol
  have hGinj : ∀ v, G *ᵥ v = 0 → v = 0 := by
    intro v hv
    have h2 : (g⁻¹).val *ᵥ (G *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, hGdef, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [← h2, hv, Matrix.mulVec_zero]
  have hinj : Function.Injective κ := by
    intro i j hij
    by_contra hne
    have h0 : G *ᵥ (sg j • (Pi.single (Fin.natAdd n i) 1 : Fin (n + r) → ℤ)
        - sg i • Pi.single (Fin.natAdd n j) 1) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hcolκ i, hcolκ j, hij, smul_smul,
        smul_smul, mul_comm, sub_self]
    have := congrFun (hGinj _ h0) (Fin.natAdd n i)
    have hij' : Fin.natAdd n i ≠ Fin.natAdd n j := fun h => hne ((natAdd_inj_iff i j).1 h)
    simp [Pi.single_apply, hij'] at this
    rcases hsg j with h | h <;> simp [h] at this
  let σ : Equiv.Perm (Fin r) := Equiv.ofBijective κ (Finite.injective_iff_bijective.1 hinj)
  have hσ : ∀ j, σ j = κ j := fun j => rfl
  let b : Fin r → Bool := fun j => decide (sg j = -1)
  have hsgb : ∀ j, sg j = sgn (b j) := by
    intro j
    rcases hsg j with h | h <;> simp [b, sgn, h]
  -- the A-columns have no I-part
  have hvan : ∀ (a : Fin n) (i : Fin r), (G *ᵥ Pi.single (Fin.castAdd r a) 1) (Fin.natAdd n i) = 0 := by
    intro a i
    obtain ⟨i', rfl⟩ := σ.surjective i
    have := hbil (Pi.single (Fin.natAdd n i') 1) (Pi.single (Fin.castAdd r a) 1)
    rw [hcolκ i', smul_dotProduct, single_dot_sumI, single_dot_sumI] at this
    have h2 : (Pi.single (Fin.castAdd r a) 1 : Fin (n + r) → ℤ) (Fin.natAdd n i') = 0 := by
      simp [Pi.single_apply, (castAdd_ne_natAdd a i').symm]
    rw [h2] at this
    rw [hσ]
    simp only [smul_eq_mul] at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (by rcases hsg i' with h | h <;> simp [h])
    · exact h
  have hcolent : ∀ i j, G i j = (G *ᵥ Pi.single j 1) i := by
    intro i j; rw [Matrix.mulVec_single_one]; rfl
  set h : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun a c => G (Fin.castAdd r a) (Fin.castAdd r c) with hh
  have hGform : G = blockMat h 0 0 (Pm σ b) := by
    ext i j
    refine Fin.addCases (fun a => ?_) (fun i' => ?_) i <;>
      refine Fin.addCases (fun c => ?_) (fun j' => ?_) j
    · simp [hh]
    · rw [hcolent, hcolκ j']
      simp [Pi.single_apply, castAdd_ne_natAdd]
    · rw [hcolent, hvan]
      simp
    · rw [hcolent, hcolκ j']
      simp only [blockMat_natAdd_natAdd, Pm, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hij : i' = σ j'
      · rw [if_pos hij]
        have hi : i' = κ j' := hij
        rw [hi, Pi.single_eq_same, mul_one, hsgb]
      · rw [if_neg hij]
        have : Fin.natAdd n i' ≠ Fin.natAdd n (κ j') := fun h => hij (((natAdd_inj_iff _ _).1 h))
        simp [Pi.single_apply, this]
  -- h preserves the form of A
  have hhaut : ∀ x : Fin n → ℤ, (ofMatrixZ A).eval (h *ᵥ x) = (ofMatrixZ A).eval x := by
    intro x
    set x' : Fin (n + r) → ℤ := Fin.append x (0 : Fin r → ℤ) with hx'
    have this := hg' x'
    have e3 : (fun a => x' (Fin.castAdd r a)) = x := funext fun a => by simp [hx']
    have e4 : ∀ i, x' (Fin.natAdd n i) = 0 := fun i => by simp [hx']
    have e1 : (fun a => (G *ᵥ x') (Fin.castAdd r a)) = h *ᵥ x := by
      funext a; rw [hGform, blockMat_mulVec_castAdd, e3]
    have e2 : ∀ i, (G *ᵥ x') (Fin.natAdd n i) = 0 := by
      intro i
      rw [hGform, blockMat_mulVec_natAdd]
      have : (fun b => x' (Fin.natAdd n b)) = 0 := funext e4
      rw [this, Matrix.mulVec_zero]; rfl
    rw [norm_sumI, norm_sumI, e1, e3] at this
    simp only [e2, e4] at this
    simpa [eval_ofMatrixZ] using this
  -- h is invertible
  have hmat : hᵀ * A * h = A := by
    have h0 := (eval_mulVec_eq_iff_hessian (ofMatrixZ A) (ofMatrixZ A) h).1 hhaut
    rw [hessian_ofMatrixZ, hA.1, Matrix.mul_add, Matrix.add_mul] at h0
    ext i j
    have := congrFun (congrFun h0 i) j
    simp only [Matrix.add_apply] at this
    omega
  have hd : h.det * h.det = 1 := by
    have h0 := congrArg Matrix.det hmat
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h0
    have h3 : (h.det * h.det) * A.det = 1 * A.det := by linarith
    exact mul_right_cancel₀ hA.det_ne h3
  let hGL : GL (Fin n) ℤ :=
    ⟨h, h.det • h.adjugate, by rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hd, one_smul],
      by rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, hd, one_smul]⟩
  have hmem : hGL ∈ Aut (ofMatrixZ A) := fun x => hhaut x
  refine ⟨(⟨hGL, hmem⟩, σ, b), ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact hGform.symm

/-- **$|\mathrm{Aut}(L \oplus I_r)| = 2^r\,r!\,|\mathrm{Aut}(L)|$** (§10, p. 275, "vines") for a positive definite lattice $L$ with no
vector of norm $1$: every automorphism of $L \oplus I_r$ permutes the norm-$1$ vectors $\pm e_i$ (`norm_one_vectors`),
hence is a block diagonal sum of an automorphism of $L$ and a signed permutation of the $r$ coordinates. -/
@[kb "conwaysloane1988" "§10, p. 275 (vines)"]
theorem card_aut_sumI {A : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A) (h1 : ∀ x, x ⬝ᵥ (A *ᵥ x) ≠ 1) (r : ℕ) :
    Nat.card (Aut (ofMatrixZ (sumI A r))) = 2 ^ r * r.factorial * Nat.card (Aut (ofMatrixZ A)) := by
  have e := Nat.card_congr (Equiv.ofBijective (autMap A r) ⟨autMap_injective A r, autMap_surjective hA h1 r⟩)
  rw [← e, Nat.card_prod, Nat.card_prod]
  have c1 : Nat.card (Equiv.Perm (Fin r)) = r.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have c2 : Nat.card (Fin r → Bool) = 2 ^ r := by
    rw [Nat.card_eq_fintype_card]; simp
  rw [c1, c2]
  ring

/-- **The step of §10, p. 275:** $|\mathrm{Aut}(L \oplus I_{r+1})| = 2(r+1)\,|\mathrm{Aut}(L \oplus I_r)|$, so the mass of
$L \oplus I_{r+1}$ is the mass of $L \oplus I_r$ divided by $2(r+1)$ (adjoining $I_r$ is a bijection of the classes of the genera). -/
@[kb "conwaysloane1988" "§10, p. 275 (vines)"]
theorem card_aut_sumI_succ {A : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A) (h1 : ∀ x, x ⬝ᵥ (A *ᵥ x) ≠ 1)
    (r : ℕ) :
    Nat.card (Aut (ofMatrixZ (sumI A (r + 1)))) = 2 * (r + 1) * Nat.card (Aut (ofMatrixZ (sumI A r))) := by
  rw [card_aut_sumI hA h1, card_aut_sumI hA h1, Nat.factorial_succ, pow_succ]
  ring

end QuadFormsKB.ConwaySloane.Mass
