/-
# Siegel's formula: sanity checks for sums of squares

For $I_n = x_0^2 + \dots + x_{n-1}^2$: $|\mathrm{Aut}(I_n)| = 2^n n!$ over $\mathrm{GL}_n(\mathbb{Z})$ (`card_aut_sumSq`), so
$|\mathrm{Aut}(I_4)| = 384$ (`card_aut_Q4`). For the sum of four squares, consistency with the AWS notes' file
`Literature/AWS/FourSquares.lean`: the same Euler factors (`eulerFactor_Q4_odd`), $\beta_\infty(m) = \pi^2 m$
(`betaInf_Q4`), and `AWS.FourSquaresInputs.siegel` is exactly $r_{I_4}(m) = $ `aE` (`fourSquaresInputs_siegel_iff`).
Class number one (`FourSquaresClassNumberOne`, under which $a_E = r_{I_4}$, `genusRepAvg_Q4`) is proved in
`Siegel/FourSquaresClassNumber.lean` (`fourSquaresClassNumberOne`, `genusRepAvg_Q4'`).
-/
import QuadFormsKB.Siegel.LocalProduct

open Matrix

namespace QuadFormsKB.Siegel

variable {n : ℕ}

/-- **The sum of $n$ squares** $I_n = x_0^2 + \dots + x_{n-1}^2$ (the diagonal form $\langle 1, \dots, 1\rangle$). -/
def sumSq (n : ℕ) : QuadForm ℤ n := QuadForm.diag fun _ => 1

/-- $I_4$ is the AWS notes' `Q4`. -/
theorem sumSq_four : sumSq 4 = AWS.Q4 := rfl

/-- The Hessian of $I_n$ is $2 I$. -/
theorem hessian_sumSq : (sumSq n).hessian = (2 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [sumSq, QuadForm.diag, QuadForm.hessian]
  · simp [sumSq, QuadForm.diag, QuadForm.hessian, h]

/-- $g \in \mathrm{Aut}(I_n)$ iff $g^{\mathsf T} g = 1$ ($g$ is an integral orthogonal matrix). -/
theorem mem_aut_sumSq_iff (g : GL (Fin n) ℤ) : g ∈ Aut (sumSq n) ↔ g.valᵀ * g.val = 1 := by
  change (∀ x, _ = _) ↔ _
  rw [eval_mulVec_eq_iff_hessian, hessian_sumSq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  exact (smul_right_injective _ two_ne_zero).eq_iff

/-- **The signed permutation matrix** $M_{ij} = s_j$ if $i = \sigma(j)$, else $0$ ($\sigma$ a permutation, $s_j = \pm 1$). -/
def signedPerm (σ : Equiv.Perm (Fin n)) (s : Fin n → ℤˣ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => if i = σ j then (s j : ℤ) else 0

/-- Signed permutation matrices are orthogonal: $M^{\mathsf T}M = 1$. -/
theorem signedPerm_transpose_mul (σ : Equiv.Perm (Fin n)) (s : Fin n → ℤˣ) :
    (signedPerm σ s)ᵀ * signedPerm σ s = 1 := by
  ext j k
  simp only [Matrix.mul_apply, transpose_apply, signedPerm, of_apply, Matrix.one_apply]
  simp only [mul_ite, ite_mul, zero_mul, mul_zero]
  rw [Finset.sum_eq_single (σ j)]
  · by_cases h : j = k
    · subst h; simp
    · have : σ j ≠ σ k := fun e => h (σ.injective e)
      simp [h, this]
  · intro b _ hb; simp [hb]
  · simp

/-- A signed permutation matrix as an element of $\mathrm{GL}_n(\mathbb{Z})$ (inverse $M^{\mathsf T}$). -/
def signedPermGL (σ : Equiv.Perm (Fin n)) (s : Fin n → ℤˣ) : GL (Fin n) ℤ where
  val := signedPerm σ s
  inv := (signedPerm σ s)ᵀ
  val_inv := mul_eq_one_comm.mp (signedPerm_transpose_mul σ s)
  inv_val := signedPerm_transpose_mul σ s

/-- The map $(\sigma, s) \mapsto M_{\sigma,s} \in \mathrm{Aut}(I_n)$. -/
def signedPermAut (x : Equiv.Perm (Fin n) × (Fin n → ℤˣ)) : Aut (sumSq n) :=
  ⟨signedPermGL x.1 x.2, (mem_aut_sumSq_iff _).mpr (signedPerm_transpose_mul x.1 x.2)⟩

/-- $(\sigma, s) \mapsto M_{\sigma,s}$ is injective (column $j$ has its nonzero entry $s_j$ in row $\sigma(j)$). -/
theorem signedPermAut_injective : Function.Injective (signedPermAut (n := n)) := by
  rintro ⟨σ, s⟩ ⟨τ, t⟩ h
  have hM : signedPerm σ s = signedPerm τ t := congrArg (fun g : Aut (sumSq n) => g.1.val) h
  have hst : ∀ j, σ j = τ j ∧ s j = t j := by
    intro j
    have e := congrFun (congrFun hM (σ j)) j
    simp only [signedPerm, of_apply, ite_true] at e
    by_cases hj : σ j = τ j
    · rw [ite_eq_left hj] at e
      exact ⟨hj, Units.ext e⟩
    · rw [ite_eq_right hj] at e
      exact absurd e (Units.ne_zero _)
  refine Prod.ext (Equiv.ext fun j => (hst j).1) (funext fun j => (hst j).2)

/-- An integer vector with $\sum_i v_i^2 = 1$ is $\pm\vec{e}_i$ for some $i$. -/
theorem exists_unique_nonzero_of_sum_sq_eq_one (v : Fin n → ℤ) (h : ∑ i, v i ^ 2 = 1) :
    ∃ i, v i ^ 2 = 1 ∧ ∀ k, k ≠ i → v k = 0 := by
  have hex : ∃ i, v i ≠ 0 := by
    by_contra hc
    push Not at hc
    simp [hc] at h
  obtain ⟨i, hi⟩ := hex
  have hsplit := Finset.add_sum_erase Finset.univ (fun k => v k ^ 2) (Finset.mem_univ i)
  rw [h] at hsplit
  have hrest : 0 ≤ ∑ k ∈ Finset.univ.erase i, v k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hi1 : 1 ≤ v i ^ 2 := by
    have : 0 < v i ^ 2 := by positivity
    omega
  refine ⟨i, by omega, fun k hk => ?_⟩
  have h0 : ∑ k ∈ Finset.univ.erase i, v k ^ 2 = 0 := by omega
  have := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg (v k)).mp h0 k
    (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)
  exact pow_eq_zero_iff (two_ne_zero) |>.mp this

/-- **Every integral automorphism of $I_n$ is a signed permutation:** its columns are $\pm\vec{e}_{\sigma(j)}$, and
orthogonality of the columns makes $\sigma$ injective. -/
theorem signedPermAut_surjective : Function.Surjective (signedPermAut (n := n)) := by
  rintro ⟨g, hg⟩
  have hO := (mem_aut_sumSq_iff g).mp hg
  have hcol : ∀ j, ∃ i, g.val i j ^ 2 = 1 ∧ ∀ k, k ≠ i → g.val k j = 0 := by
    intro j
    refine exists_unique_nonzero_of_sum_sq_eq_one (fun i => g.val i j) ?_
    have := congrFun (congrFun hO j) j
    simpa [Matrix.mul_apply, sq] using this
  choose σ' hσ1 hσ0 using hcol
  have hinj : Function.Injective σ' := by
    intro j k hjk
    by_contra hne
    have e := congrFun (congrFun hO j) k
    simp only [Matrix.mul_apply, transpose_apply, Matrix.one_apply, ite_eq_right hne] at e
    rw [Finset.sum_eq_single (σ' j)] at e
    · have h1 := hσ1 j
      have h2 := hσ1 k
      rw [← hjk] at h2
      have : (g.val (σ' j) j * g.val (σ' j) k) ^ 2 = 1 := by rw [mul_pow, h1, h2]; ring
      rw [e] at this
      norm_num at this
    · intro b _ hb
      rw [hσ0 j b hb, zero_mul]
    · simp
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective σ' (Finite.injective_iff_bijective.mp hinj)
  have hunit : ∀ j, IsUnit (g.val (σ' j) j) := fun j =>
    isUnit_iff_exists_inv.mpr ⟨g.val (σ' j) j, by rw [← sq]; exact hσ1 j⟩
  let s : Fin n → ℤˣ := fun j => (hunit j).unit
  refine ⟨(σ, s), Subtype.ext (Units.ext ?_)⟩
  ext i j
  change signedPerm σ s i j = g.val i j
  simp only [signedPerm, of_apply]
  by_cases h : i = σ' j
  · have : i = σ j := h
    rw [ite_eq_left this, h]
    rfl
  · have : ¬ i = σ j := h
    rw [ite_eq_right this, hσ0 j i h]

/-- **$|\mathrm{Aut}(I_n)| = 2^n\, n!$** ($\mathrm{GL}_n(\mathbb{Z})$-automorphisms, the hyperoctahedral group). -/
theorem card_aut_sumSq (n : ℕ) : Nat.card (Aut (sumSq n)) = 2 ^ n * n.factorial := by
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨signedPermAut_injective, signedPermAut_surjective⟩),
    Nat.card_prod, Nat.card_perm, Nat.card_fun]
  simp [Nat.card_eq_fintype_card, Fintype.card_units_int, mul_comm]

/-- **$|\mathrm{Aut}(x_0^2+x_1^2+x_2^2+x_3^2)| = 384 = 2^4 \cdot 4!$.** -/
theorem card_aut_Q4 : Nat.card (Aut AWS.Q4) = 384 := by
  rw [← sumSq_four, card_aut_sumSq]
  decide


/-- $I_n(\vec{x}) = \sum_i x_i^2$. -/
theorem eval_sumSq (x : Fin n → ℤ) : (sumSq n).eval x = ∑ i, x i ^ 2 := by
  simp only [sumSq, QuadForm.diag, QuadForm.evalIn, diagonal_apply, Algebra.algebraMap_self,
    RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp [sq]

/-- $I_n$ is positive definite. -/
theorem posDef_sumSq : IntQF.PosDef (sumSq n) := by
  intro x hx
  rw [eval_sumSq]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, by simpa using sq_pos_of_ne_zero (by simpa using hi)⟩

/-- $x_0^2+\dots+x_3^2$ is nondegenerate. -/
theorem nondegenerate_Q4 : AWS.Q4.Nondegenerate := (sumSq_four ▸ posDef_sumSq).nondegenerate

/-- **Consistency with the AWS notes' Lemma 2.7.4:** the Euler factor of `aE` for the sum of four squares at an odd
$p \nmid m$ is $1 - p^{-2}$ (`AWS.beta_odd_unit`; both files use `LocalDensity.localDensity`). -/
theorem eulerFactor_Q4_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (m : ℤ) (hm : ¬ (p : ℤ) ∣ m) :
    eulerFactor AWS.Q4 m ⟨p, Fact.out⟩ = 1 - 1 / (p : ℝ) ^ 2 :=
  AWS.beta_odd_unit p hp m hm

/-- **`aE` for the sum of four squares** is the right-hand side of `AWS.FourSquaresInputs.siegel`:
$\beta_\infty(m)\prod_p\beta_p(m) = \pi^2 m \prod_p \beta_p(m)$ (as complex numbers, product over the primes). -/
theorem aE_Q4_complex (m : ℕ) (hm : 0 < m) :
    ((aE AWS.Q4 m : ℝ) : ℂ) = ((Real.pi ^ 2 * m : ℝ) : ℂ) *
      ∏' p : AWS.PrimeIdx, ((LocalDensity.localDensity AWS.Q4 p m : ℝ) : ℂ) := by
  have hmult := multipliable_eulerFactor AWS.Q4 nondegenerate_Q4 le_rfl
    (m := (m : ℤ)) (by exact_mod_cast hm.ne')
  have e := hmult.map_tprod Complex.ofRealHom Complex.continuous_ofReal
  simp only [Complex.ofRealHom_eq_coe] at e
  rw [aE, aEWith, Complex.ofReal_mul, betaInf_Q4, eulerProduct, e]
  push_cast
  rfl

/-- **The AWS input `FourSquaresInputs.siegel` is Siegel's formula with this file's `aE`:** for $Q = I_4$,
$r_Q(m) = \pi^2 m \prod_p \beta_p(m)$ for all $m \ge 1$ iff $r_Q(m) = \beta_\infty(m)\prod_p\beta_p(m)$ (`aE`) for all $m \ge 1$. -/
@[kb "hanke2004" "(5.3), p. 368"]
theorem fourSquaresInputs_siegel_iff :
    (∀ m : ℕ, 0 < m → (AWS.r4 m : ℂ) = ((Real.pi ^ 2 * m : ℝ) : ℂ) *
        ∏' p : AWS.PrimeIdx, ((LocalDensity.localDensity AWS.Q4 p m : ℝ) : ℂ)) ↔
      ∀ m : ℕ, 0 < m → (repNum AWS.Q4 m : ℝ) = aE AWS.Q4 m := by
  refine forall_congr' fun m => forall_congr' fun hm => ?_
  rw [← aE_Q4_complex m hm, ← repNum_Q4]
  exact_mod_cast Iff.rfl

/-- **Input: the sum of four squares has class number one** (its genus contains one $\mathrm{GL}_4(\mathbb{Z})$-class).

Field:
- `genus_eq`: `genusClasses Q4` $= \{[Q_4]\}$.

Classical (the AWS notes, `hanke2011aws`, p. 36, state it). *Citation fix (2026-10-21):* this was cited to Conway–Sloane,
*Sphere Packings, Lattices and Groups*, 3rd ed., Table 15.4, but that table (Ch. 15, §8.1, Thm. 12, p. 387) lists all *genera* with
$|\det| \le 11$ — row 1 is the genus $I_{r,s}$, here $I_{4,0}$ — not class numbers; Ch. 15 does not count the classes of a definite
genus of determinant 1 (p. 396 refers one-class definite genera to Watson's papers). The class number of $I_4$ follows from the enumeration of unimodular lattices in Ch. 16,
to which Ch. 15, §10.2, p. 399 refers: Ch. 16, §4, Theorem 5 and the Remark after it, p. 413, with Table 16.7, pp. 416–417. Every unimodular lattice of dimension at most 23 is $\mathbb{Z}^k \oplus L$ with $L$ in Table 16.7, and that table has no entries of dimension $1$–$7$, so every positive definite unimodular lattice of dimension $4$ is $\mathbb{Z}^4$: the genus of $I_4$ has one class.
**Proved** in `Siegel/FourSquaresClassNumber.lean` (`fourSquaresClassNumberOne`); kept as a named structure so the
conditional theorems below stay as stated. -/
@[kb "hanke2011aws" "§2.7.2, p. 36"]
structure FourSquaresClassNumberOne : Prop where
  genus_eq : genusClasses AWS.Q4 = {classOf AWS.Q4}

/-- Under class number one, $a_E(m) = r_{I_4}(m)$ for the sum of four squares. -/
theorem genusRepAvg_Q4 (h : FourSquaresClassNumberOne) (m : ℤ) :
    genusRepAvg AWS.Q4 m = repNum AWS.Q4 m :=
  genusRepAvg_of_classNumber_one (sumSq_four ▸ posDef_sumSq) h.genus_eq m

end QuadFormsKB.Siegel
