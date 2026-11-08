/-
# Watson (1963), §5, Lemma 5: a represented unimodular form splits off

G. L. Watson, *The class-number of a positive quadratic form*, Proc. London Math. Soc. (3) 13 (1963) 549–576.

**Proved here.**
* `exists_intEquiv_orthSum_of_rep` (**Watson 1963, Lemma 5, p. 557, splitting part**): if an integral form $f$ in $n$
  variables represents an integral form $\varphi$ in $v$ variables whose Hessian determinant is a unit ($\pm 1$), then
  $f \cong \varphi \perp \psi$ over $\mathbb Z$ for some form $\psi$ in $n - v$ variables.

Variables are $x_0, \dots, x_{n-1}$; in $\varphi \perp \psi$ the first $v$ variables carry $\varphi$.
-/
import QuadFormsKB.Literature.Watson1963.Perfect

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel

/-- **Splitting of a unimodular sublattice, linear-algebra core.** Let $A$ be an integral $n \times n$ matrix and $H$ an
integral $n \times v$ matrix such that $H^{\mathsf T} A H$ has unit determinant. Then there are $m$ with $v + m = n$ and
an integral $n \times m$ matrix $K$ whose columns lie in the $A$-orthogonal complement of the columns of $H$ (that is,
$(H\vec y)^{\mathsf T} A (K\vec c) = 0$), such that every integral vector is $H\vec y + K\vec c$. -/
theorem exists_complement_of_unimodular {n v : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (H : Matrix (Fin n) (Fin v) ℤ)
    (hB : IsUnit (Hᵀ * A * H).det) :
    ∃ (m : ℕ) (_ : v + m = n) (K : Matrix (Fin n) (Fin m) ℤ),
      (∀ (y : Fin v → ℤ) (c : Fin m → ℤ), (H *ᵥ y) ⬝ᵥ (A *ᵥ (K *ᵥ c)) = 0) ∧
      ∀ z : Fin n → ℤ, ∃ (y : Fin v → ℤ) (c : Fin m → ℤ), z = H *ᵥ y + K *ᵥ c := by
  set B := Hᵀ * A * H with hBdef
  set L : Matrix (Fin v) (Fin n) ℤ := B⁻¹ * (Hᵀ * A) with hL
  have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hB
  have hBB' : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _ hB
  have hLH : L * H = 1 := by
    have : L * H = B⁻¹ * B := by
      rw [hL, hBdef]; simp only [Matrix.mul_assoc]
    rw [this, hBB']
  have hBL : B * L = Hᵀ * A := by
    rw [hL, ← Matrix.mul_assoc, hBB, Matrix.one_mul]
  let Kr : Submodule ℤ (Fin n → ℤ) := LinearMap.ker (Matrix.mulVecLin L)
  let b := Module.finBasis ℤ Kr
  have hmem : ∀ k : Fin n → ℤ, k ∈ Kr ↔ L *ᵥ k = 0 := fun k => by simp [Kr]
  let e : (Fin n → ℤ) ≃ₗ[ℤ] (Fin v → ℤ) × Kr :=
    { toFun := fun z => (L *ᵥ z, ⟨z - H *ᵥ (L *ᵥ z), by
        rw [hmem, mulVec_sub, mulVec_mulVec, hLH, one_mulVec, sub_self]⟩)
      map_add' := fun z w => by
        apply Prod.ext
        · simp [mulVec_add]
        · apply Subtype.ext
          simp [mulVec_add]; abel
      map_smul' := fun r z => by
        apply Prod.ext
        · show L *ᵥ (r • z) = r • (L *ᵥ z)
          rw [mulVec_smul]
        · apply Subtype.ext
          show r • z - H *ᵥ (L *ᵥ (r • z)) = r • (z - H *ᵥ (L *ᵥ z))
          rw [mulVec_smul, mulVec_smul, smul_sub]
      invFun := fun p => H *ᵥ p.1 + (p.2 : Fin n → ℤ)
      left_inv := fun z => by simp
      right_inv := fun p => by
        have hk : L *ᵥ (p.2 : Fin n → ℤ) = 0 := (hmem _).1 p.2.2
        apply Prod.ext
        · simp [mulVec_add, mulVec_mulVec, hLH, hk]
        · apply Subtype.ext
          simp [mulVec_add, mulVec_mulVec, hLH, hk] }
  have hrank : n = v + Module.finrank ℤ Kr := by
    have := e.finrank_eq
    simpa [Module.finrank_prod] using this
  have hK : ∀ c, (Matrix.of fun (i : Fin n) (c : Fin (Module.finrank ℤ Kr)) => ((b c : Kr) : Fin n → ℤ) i) *ᵥ c
      = ((b.equivFun.symm c : Kr) : Fin n → ℤ) := fun c => by
    ext i
    simp [mulVec, dotProduct, Module.Basis.equivFun_symm_apply, Finset.sum_apply, Submodule.coe_sum, mul_comm]
  refine ⟨Module.finrank ℤ Kr, hrank.symm,
    Matrix.of fun i c => ((b c : Kr) : Fin n → ℤ) i, ?_, ?_⟩
  · intro y c
    rw [hK]
    have hk : L *ᵥ ((b.equivFun.symm c : Kr) : Fin n → ℤ) = 0 := (hmem _).1 (b.equivFun.symm c).2
    have h0 : Hᵀ *ᵥ (A *ᵥ ((b.equivFun.symm c : Kr) : Fin n → ℤ)) = 0 := by
      rw [mulVec_mulVec, ← hBL, ← mulVec_mulVec, hk, mulVec_zero]
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, h0, zero_dotProduct]
  · intro z
    refine ⟨(e z).1, b.equivFun (e z).2, ?_⟩
    have hz : z = H *ᵥ (e z).1 + ((e z).2 : Fin n → ℤ) := (e.symm_apply_apply z).symm
    rw [hK, LinearEquiv.symm_apply_apply]
    exact hz

/-- **Watson 1963, Lemma 5, p. 557 (splitting part).** Let $\varphi$ be an integral form in $v$ variables with
$|A(\varphi)| = 1$, that is, whose Hessian determinant is a unit of $\mathbb Z$ (so $\pm 1$). If an integral form $f$ in
$n$ variables represents $\varphi$ (`Rep`), then $\varphi$ splits off: $f \cong \varphi \perp \psi$ over $\mathbb Z$
(`IntEquiv`) for an integral form $\psi$ in $m = n - v$ variables. Arguments: the Hessian-determinant hypothesis `hφ`
and the representation `h`. The first $v$ variables of $\varphi \perp \psi$ carry $\varphi$. -/
@[kb "watson1963" "§5, Lemma 5, p. 557 (splitting part)"]
theorem exists_intEquiv_orthSum_of_rep {n v : ℕ} {f : QuadForm ℤ n} {φ : QuadForm ℤ v}
    (hφ : IsUnit φ.hessian.det) (h : Rep f φ) :
    ∃ (m : ℕ) (hm : v + m = n) (ψ : QuadForm ℤ m), IntEquiv f (hm ▸ QuadForm.orthSum φ ψ) := by
  obtain ⟨H, hH⟩ := h
  have hhess : φ.hessian = Hᵀ * f.hessian * H := by
    have : f.compMat H = φ := QuadForm.eq_of_eval_eq (fun y => by rw [QuadForm.eval_compMat, hH])
    rw [← this, QuadForm.hessian_compMat]
  rw [hhess] at hφ
  obtain ⟨m, hm, K, horth, hspan⟩ := exists_complement_of_unimodular _ H hφ
  refine ⟨m, hm, f.compMat K, ?_⟩
  subst hm
  let T : Matrix (Fin (v + m)) (Fin (v + m)) ℤ :=
    Matrix.of fun i j => Fin.append (fun a => H i a) (fun b => K i b) j
  have hT : ∀ x, T *ᵥ x = H *ᵥ (fun a => x (Fin.castAdd m a)) + K *ᵥ (fun b => x (Fin.natAdd v b)) := by
    intro x; ext i
    simp [T, mulVec, dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  have surj : ∀ z : Fin (v + m) → ℤ, ∃ x, T *ᵥ x = z := by
    intro z
    obtain ⟨y, c, hz⟩ := hspan z
    refine ⟨Fin.append y c, ?_⟩
    rw [hT]
    simpa [Fin.append_left, Fin.append_right] using hz.symm
  choose S hS using surj
  let S' : Matrix (Fin (v + m)) (Fin (v + m)) ℤ := Matrix.of fun i j => S (Pi.single j 1) i
  have hTS : T * S' = 1 := by
    ext i j
    have := congrFun (hS (Pi.single j 1)) i
    simp only [mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, S', Matrix.of_apply, this, Matrix.one_apply, Pi.single_apply, eq_comm]
  have hST : S' * T = 1 := mul_eq_one_comm.mp hTS
  refine ⟨⟨T, S', hTS, hST⟩, fun x => ?_⟩
  show f.eval (T *ᵥ x) = (QuadForm.orthSum φ (f.compMat K)).eval x
  rw [hT]
  have hpol := QuadForm.eval_polar f (H *ᵥ fun a => x (Fin.castAdd m a)) (K *ᵥ fun b => x (Fin.natAdd v b))
  rw [horth] at hpol
  show _ = (QuadForm.orthSum φ (f.compMat K)).evalIn ℤ x
  rw [QuadForm.evalIn_orthSum]
  show _ = φ.eval _ + (f.compMat K).eval _
  rw [QuadForm.eval_compMat, ← hH]
  linarith

end QuadFormsKB.Watson1963
