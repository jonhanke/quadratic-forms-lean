/-
# Cassels, Chapter 9: Example 10, positive definite improperly primitive forms of determinant 1

**Layer:** classically integral forms `QuadForm ℤ n` (`IsClassicallyIntegral`), Cassels' matrix $(f_{ij}) = H/2$ (`casselsMat`),
improperly primitive forms (`IsImproperlyPrimitive`, `Ch9Sec1.lean`), positive definiteness (`IntQF.PosDef`); the lattice
$E_8$ (`Siegel.e8`) and the rank theorem for even unimodular lattices (`Siegel.eight_dvd_of_posDef_det_one`).

**Proves**
* Example 10, p. 163 (`ex10`): for $n \ge 1$ there is a positive definite improperly primitive integral form $f$ in $n$ variables
  with $d(f) = \det(f_{ij}) = 1$ if and only if $8 \mid n$. Unconditional (no assumed inputs).
* `exists_posDef_det_one_of_eight_dvd`: the orthogonal sum $E_8^{\perp m}$ of $m$ copies of $E_8$ is an integer-valued positive
  definite form in $8m$ variables with $\det H = 1$.

*Proof:* not Cassels' argument via the invariants $c_p$, but Serre's argument with the theta series
(`Siegel/EvenUnimodularRank.lean`). For improperly primitive $f$ the form $Q = f/2$ is integer-valued with Hessian $(f_{ij})$,
so $f$ is as in the example if and only if $Q$ is positive definite with $\det H_Q = 1$; the rank of such a lattice is
divisible by $8$ (theta series), and conversely $E_8^{\perp m}$ exists.

*Convention:* for $n = 0$ the statement is false in this formalization, because primitivity ("$\gcd(f_{ij}) = 1$") is the condition
that every common divisor of the (empty) set of coefficients is a unit, which fails (e.g. for $0$); hence $n \ge 1$.
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec1
import QuadFormsKB.Literature.Cassels.Ch9Sec6Weight
import QuadFormsKB.Siegel.E8
import QuadFormsKB.Siegel.EvenUnimodularRank

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

variable {n : ℕ}

/-! ### Scaling by $2$ -/

/-- The Hessian of $2 \cdot Q$ is $2H$. -/
theorem hessian_two_smul (Q : QuadForm ℤ n) : ((2 : ℤ) • Q).hessian = (2 : ℤ) • Q.hessian := by
  unfold QuadForm.hessian
  rw [QuadForm.smul_coeff, Matrix.transpose_smul, smul_add]

/-- $(2 \cdot Q)(\vec x) = 2\,Q(\vec x)$. -/
theorem eval_two_smul (Q : QuadForm ℤ n) (x : Fin n → ℤ) : ((2 : ℤ) • Q).eval x = 2 * Q.eval x := by
  have h := LocalDensity.two_mul_eval_eq_hessian ((2 : ℤ) • Q) x
  have h' := LocalDensity.two_mul_eval_eq_hessian Q x
  have hh : ((2 : ℤ) • Q).hessian = (2 : ℤ) • Q.hessian := hessian_two_smul Q
  rw [hh, smul_mulVec, dotProduct_smul, smul_eq_mul, ← h'] at h
  linarith

/-! ### The form $E_8^{\perp m}$ -/

/-- The value of `ofGram A` on $\vec x$ is $\vec x^{\mathsf T}A\vec x$ for **any** integral matrix $A$ (symmetry is not needed). -/
theorem eval_ofGram' (A : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    (ofGram A).eval x = x ⬝ᵥ (A *ᵥ x) := by
  have h2 := LocalDensity.two_mul_eval_eq_hessian (ofGram A) x
  rw [hessian_ofGram, add_mulVec, dotProduct_add, dotProduct_mulVec_transpose_self] at h2
  linarith

/-- The block-diagonal coefficient matrix of $m$ copies of $E_8$ (coefficient matrix `e8.coeff`), indexed by `Fin (8 * m)`
through `finProdFinEquiv : Fin 8 × Fin m ≃ Fin (8 * m)`: variable $x_{i + m\cdot\ldots}$ of block $j$ is the pair $(i, j)$. -/
def e8Coeff (m : ℕ) : Matrix (Fin (8 * m)) (Fin (8 * m)) ℤ :=
  (blockDiagonal fun _ : Fin m => e8.coeff).reindex finProdFinEquiv finProdFinEquiv

/-- **The form $E_8^{\perp m}$** in $8m$ variables: $\sum_{j=0}^{m-1} Q_{E_8}(\text{block } j)$. -/
def e8Sum (m : ℕ) : QuadForm ℤ (8 * m) := ofGram (e8Coeff m)

/-- $E_8 = $ `ofGram e8.coeff` (both have Hessian $C + C^{\mathsf T}$). -/
theorem ofGram_e8_coeff : ofGram e8.coeff = e8 := by
  apply eq_of_hessian_eq
  rw [hessian_ofGram]; rfl

/-- **Values of $E_8^{\perp m}$:** $Q(\vec x) = \sum_{j} Q_{E_8}(x_{(0,j)}, \dots, x_{(7,j)})$. -/
theorem eval_e8Sum (m : ℕ) (x : Fin (8 * m) → ℤ) :
    (e8Sum m).eval x = ∑ j : Fin m, e8.eval (fun i => x (finProdFinEquiv (i, j))) := by
  rw [e8Sum, eval_ofGram']
  have hE : ∀ y : Fin 8 → ℤ, e8.eval y = y ⬝ᵥ (e8.coeff *ᵥ y) := fun y => by
    rw [← ofGram_e8_coeff, eval_ofGram', ofGram_e8_coeff]
  simp_rw [hE]
  simp only [dotProduct, mulVec, e8Coeff, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [← (finProdFinEquiv : Fin 8 × Fin m ≃ Fin (8 * m)).sum_comp]
  simp only [Equiv.symm_apply_apply]
  simp_rw [← (finProdFinEquiv : Fin 8 × Fin m ≃ Fin (8 * m)).sum_comp (fun q => _ * _)]
  simp only [Equiv.symm_apply_apply, blockDiagonal_apply, Fintype.sum_prod_type,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  simp [ite_mul, mul_ite, Finset.sum_ite_eq]

/-- **$E_8^{\perp m}$ is positive definite.** -/
theorem e8Sum_posDef (m : ℕ) : IntQF.PosDef (e8Sum m) := by
  intro x hx
  rw [eval_e8Sum]
  obtain ⟨p, hp⟩ : ∃ p, x p ≠ 0 := by
    by_contra h; push Not at h; exact hx (funext h)
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
  refine Finset.sum_pos' (fun j _ => Siegel.eval_nonneg e8_posDef _) ⟨j, Finset.mem_univ _, e8_posDef _ ?_⟩
  intro h
  exact hp (by simpa using congrFun h i)

/-- The Hessian of $E_8^{\perp m}$ is the block-diagonal matrix of $m$ copies of the $E_8$ Cartan matrix. -/
theorem e8Sum_hessian (m : ℕ) :
    (e8Sum m).hessian = (blockDiagonal fun _ : Fin m => e8.hessian).reindex finProdFinEquiv finProdFinEquiv := by
  rw [e8Sum, hessian_ofGram]
  ext a b
  simp [e8Coeff, QuadForm.hessian, blockDiagonal_apply, Matrix.add_apply]
  split_ifs <;> simp

/-- **$\det H(E_8^{\perp m}) = 1$.** -/
theorem e8Sum_det (m : ℕ) : (e8Sum m).hessian.det = 1 := by
  rw [e8Sum_hessian, det_reindex_self, det_blockDiagonal]
  simp [e8_det]

/-- **Existence for $8 \mid n$:** for $n = 8m$ there is a positive definite integer-valued form in $n$ variables whose
Hessian has determinant $1$ (namely $E_8^{\perp m}$). -/
theorem exists_posDef_det_one_of_eight_dvd (h : 8 ∣ n) :
    ∃ Q : IntQF n, Q.PosDef ∧ Q.hessian.det = 1 := by
  obtain ⟨m, rfl⟩ := h
  exact ⟨e8Sum m, e8Sum_posDef m, e8Sum_det m⟩

/-! ### Example 10 -/

/-- If every entry of an integral matrix $H$ with $\det H = 1$ is divisible by $c$, and $n \ge 1$, then $c$ is a unit
(expand $H \operatorname{adj} H = \det H \cdot 1$ at a diagonal entry). -/
theorem isUnit_of_dvd_entries {H : Matrix (Fin n) (Fin n) ℤ} (hn : 0 < n) (hdet : H.det = 1) {c : ℤ}
    (hc : ∀ i j, c ∣ H i j) : IsUnit c := by
  have h := congrFun (congrFun (mul_adjugate H) ⟨0, hn⟩) ⟨0, hn⟩
  rw [hdet, Matrix.mul_apply] at h
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
  have : c ∣ 1 := by
    rw [← h]
    exact Finset.dvd_sum fun k _ => (hc _ _).mul_right _
  exact isUnit_of_dvd_one this

/-- **Cassels, Ch. 9, Example 10** (pp. 163–164): *there exists a positive definite improperly primitive integral form $f$ with
$d(f) = 1$ in $n$ variables precisely when $8 \mid n$* ($n \ge 1$; for $n = 0$ the primitivity condition fails, see the module
header). Here $f$ is classically integral, improperly primitive (all $f_{ii}$ even, $\gcd f_{ij} = 1$), positive definite, and
$d(f) = \det(f_{ij})$ is the determinant of Cassels' matrix `casselsMat f` $= H/2$.

*Proof:* not Cassels' argument via the invariants $c_p$, but Serre's argument with the theta series. ($\Rightarrow$) $f = 2Q$ with
$Q$ integer-valued, $H_Q = (f_{ij})$, so $Q$ is positive definite with $\det H_Q = 1$ and `eight_dvd_of_posDef_det_one` gives
$8 \mid n$. ($\Leftarrow$) $f = 2 E_8^{\perp m}$. -/
@[kb "cassels1978" "Ch. 9, Ex. 10, pp. 163–164"]
theorem ex10 (n : ℕ) (hn : 0 < n) :
    (∃ f : QuadForm ℤ n, IsClassicallyIntegral f ∧ IntQF.PosDef f ∧ IsImproperlyPrimitive f ∧
      (casselsMat f).det = 1) ↔ 8 ∣ n := by
  constructor
  · rintro ⟨f, hci, hpos, hprim, hdet⟩
    obtain ⟨g, hg, -⟩ := exists_half_of_improperlyPrimitive hprim
    have hH : g.hessian = casselsMat f := by
      have h1 : (2 : ℤ) • g.hessian = (2 : ℤ) • casselsMat f := by
        rw [← hessian_two_smul, hg, hessian_eq_two_smul_casselsMat hci]
      ext i j
      have := congrFun (congrFun h1 i) j
      simp only [Matrix.smul_apply, smul_eq_mul] at this
      linarith
    refine eight_dvd_of_posDef_det_one (Q := g) (fun x hx => ?_) (by rw [hH]; exact hdet)
    have := hpos x hx
    rw [← hg, eval_two_smul] at this
    linarith
  · intro h
    obtain ⟨Q, hQ, hdet⟩ := exists_posDef_det_one_of_eight_dvd h
    have hev : ∀ i j, (2 : ℤ) ∣ ((2 : ℤ) • Q).hessian i j := fun i j => by
      rw [hessian_two_smul]; exact ⟨Q.hessian i j, by simp⟩
    have hci : IsClassicallyIntegral ((2 : ℤ) • Q) := ci_of_two_dvd_hessian hev
    have hcm : casselsMat ((2 : ℤ) • Q) = Q.hessian := by
      ext i j
      simp [casselsMat, hessian_two_smul]
    refine ⟨(2 : ℤ) • Q, hci, fun x hx => ?_, ⟨⟨hci, fun c hc => ?_⟩, fun i => ?_⟩, by rw [hcm, hdet]⟩
    · rw [eval_two_smul]; have := hQ x hx; linarith
    · refine isUnit_of_dvd_entries hn hdet fun i j => ?_
      have := hc i j
      rwa [← show casselsMat ((2 : ℤ) • Q) i j = Q.hessian i j by rw [hcm]]
    · simp [QuadForm.smul_coeff]

end QuadFormsKB.Siegel
