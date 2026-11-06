/-
# Hanke 2011, §2: splitting off binary blocks from Hessian matrices (for Sublemmas 2.7--2.9)

Let $R$ be a commutative ring and $H$ a Hessian matrix (`IsHess`) on a finite index type $\iota$.

**Proves**
* `split_at`: for $k \ne l$ with the $2 \times 2$ principal block on $\{k, l\}$ of unit determinant, $H$ is congruent
  to the block sum of that block and a Hessian matrix $S$ on the remaining indices, and $\det H = \det(\text{block})\det S$;
* `split_single`: if row and column $i$ of $H$ vanish off the diagonal, $H$ is congruent to $(H_{ii}) \oplus H'$.
-/
import QuadFormsKB.Literature.Hanke2011Structure.DyadicCong

open Matrix

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Hanke2011Structure.Dyadic

section Split

variable {R : Type*} [CommRing R]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The two-element set $\{k, l\}$ and its complement, as an equivalence
$\mathrm{Fin}\,2 \oplus \{x // x \ne k, l\} \simeq \iota$. -/
noncomputable def pairEquiv (k l : ι) (hkl : k ≠ l) : Fin 2 ⊕ {x : ι // ¬ (x = k ∨ x = l)} ≃ ι :=
  (Equiv.sumCongr
    (Equiv.ofBijective (fun i : Fin 2 => (⟨![k, l] i, by fin_cases i <;> simp⟩ : {x : ι // x = k ∨ x = l}))
      ⟨by
        intro i j h
        have h' : ![k, l] i = ![k, l] j := congrArg Subtype.val h
        fin_cases i <;> fin_cases j <;> simp_all [Ne.symm hkl],
       by
        rintro ⟨x, hx⟩
        rcases hx with rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩⟩)
    (Equiv.refl _)).trans (Equiv.sumCompl (fun x : ι => x = k ∨ x = l))

@[simp] theorem pairEquiv_inl (k l : ι) (hkl : k ≠ l) (i : Fin 2) : pairEquiv k l hkl (Sum.inl i) = ![k, l] i :=
  rfl

@[simp] theorem pairEquiv_inr (k l : ι) (hkl : k ≠ l) (x : {x : ι // ¬ (x = k ∨ x = l)}) :
    pairEquiv k l hkl (Sum.inr x) = x.1 := by
  simp [pairEquiv]

/-- **Splitting off a $2 \times 2$ block with unit determinant** from a Hessian matrix. -/
theorem split_at (H : Matrix ι ι R) (hH : IsHess H) {k l : ι} (hkl : k ≠ l)
    (hA : IsUnit (H.submatrix ![k, l] ![k, l]).det) :
    ∃ S : Matrix {x : ι // ¬ (x = k ∨ x = l)} {x : ι // ¬ (x = k ∨ x = l)} R, IsHess S ∧
      Cong H (Matrix.fromBlocks (H.submatrix ![k, l] ![k, l]) 0 0 S) ∧
      H.det = (H.submatrix ![k, l] ![k, l]).det * S.det := by
  set e := pairEquiv k l hkl with he
  have hH1 : IsHess (H.submatrix e e) := hH.submatrix e
  have h11 : (H.submatrix e e).toBlocks₁₁ = H.submatrix ![k, l] ![k, l] := by
    ext i j; simp [Matrix.toBlocks₁₁, he]
  have hA' : IsUnit (H.submatrix e e).toBlocks₁₁.det := by rw [h11]; exact hA
  obtain ⟨S, hS, hc, hd⟩ := exists_cong_fromBlocks (H.submatrix e e) hH1 hA'
  rw [h11] at hc hd
  refine ⟨S, hS, (cong_submatrix H e).trans hc, ?_⟩
  rw [← Matrix.det_submatrix_equiv_self e H]
  exact hd

/-- **Splitting off a single index** at which the Hessian matrix is block diagonal: if $H_{ij} = 0$ for $j \ne i$, then
$H$ is congruent to $H|_{\{i\}} \oplus H|_{\{x \ne i\}}$ (and $\det H$ is the product of the determinants). -/
theorem split_single (H : Matrix ι ι R) (i : ι) (h : ∀ j, j ≠ i → H i j = 0) (hs : Hᵀ = H) :
    Cong H (Matrix.fromBlocks (H.submatrix (fun x : {x : ι // x = i} => x.1) (fun x : {x : ι // x = i} => x.1))
      0 0 (H.submatrix (fun x : {x : ι // ¬ x = i} => x.1) (fun x : {x : ι // ¬ x = i} => x.1))) ∧
    H.det = (H.submatrix (fun x : {x : ι // x = i} => x.1) (fun x : {x : ι // x = i} => x.1)).det *
      (H.submatrix (fun x : {x : ι // ¬ x = i} => x.1) (fun x : {x : ι // ¬ x = i} => x.1)).det := by
  set e := Equiv.sumCompl (fun x : ι => x = i) with he
  have hH1 : H.submatrix e e = Matrix.fromBlocks
      (H.submatrix (fun x : {x : ι // x = i} => x.1) (fun x : {x : ι // x = i} => x.1)) 0 0
      (H.submatrix (fun x : {x : ι // ¬ x = i} => x.1) (fun x : {x : ι // ¬ x = i} => x.1)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · simp [he]
    · have h1 := h b.1 (by simpa using b.2)
      have : a.1 = i := a.2
      simp [he, this, h1]
    · have h1 := h a.1 (by simpa using a.2)
      have : b.1 = i := b.2
      have h2 : H a.1 i = 0 := by
        have := congrFun (congrFun hs a.1) i
        simpa [Matrix.transpose_apply, h1] using this.symm ▸ h1
      simp [he, this, h2]
    · simp [he]
  refine ⟨?_, ?_⟩
  · rw [← hH1]; exact cong_submatrix H e
  · have := congrArg Matrix.det hH1
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁] at this
    exact this

/-- **Splitting off a hyperbolic pair**: if $v$ has a unit coordinate $v_k$, $v^{\mathsf T}Hv = 0$, and
$(Hv)_l = \beta$ is a unit for some $l \ne k$, then $H$ is congruent to
$\begin{pmatrix} 0 & \beta\\ \beta & H_{ll}\end{pmatrix} \oplus S$ with $S$ a Hessian matrix on the remaining
indices, and $v_k^2\det H = -\beta^2\det S$. (Replace the basis vector $e_k$ by $v$, then `split_at`.) -/
theorem pair_split (H : Matrix ι ι R) (hH : IsHess H) {k l : ι} (hkl : k ≠ l) (v : ι → R) (hvk : IsUnit (v k))
    (hv0 : v ⬝ᵥ (H *ᵥ v) = 0) (hvl : IsUnit ((H *ᵥ v) l)) :
    ∃ S : Matrix {x : ι // ¬ (x = k ∨ x = l)} {x : ι // ¬ (x = k ∨ x = l)} R, IsHess S ∧
      Cong H (Matrix.fromBlocks (!![0, (H *ᵥ v) l; (H *ᵥ v) l, H l l] : Matrix (Fin 2) (Fin 2) R) 0 0 S) ∧
      v k ^ 2 * H.det = -((H *ᵥ v) l) ^ 2 * S.det := by
  set U : Matrix ι ι R := Matrix.updateCol 1 k v with hU
  have hdU : U.det = v k := by
    have := Matrix.cramer_apply (1 : Matrix ι ι R) v k
    rw [Matrix.cramer_one] at this
    simpa [hU] using this.symm
  have hUu : IsUnit U.det := by rw [hdU]; exact hvk
  set H' : Matrix ι ι R := Uᵀ * H * U with hH'
  have hs := hH.symm_eq
  have hc : Cong H H' := cong_of_isUnit_det H U hUu
  have hHess' : IsHess H' := hH.cong hc
  have hUl : ∀ j, U j l = if j = l then 1 else 0 := by
    intro j; simp [hU, Matrix.updateCol_apply, Ne.symm hkl, Matrix.one_apply]
  have hUk : ∀ j, U j k = v j := by intro j; simp [hU, Matrix.updateCol_apply]
  have hsym : ∀ i j, H i j = H j i := fun i j => by
    have := congrFun (congrFun hs j) i
    simpa [Matrix.transpose_apply] using this
  have e00 : H' k k = 0 := by
    simp only [hH', Matrix.mul_apply, Matrix.transpose_apply, hUk]
    rw [← hv0]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_comm.trans ?_
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  have e01 : H' k l = (H *ᵥ v) l := by
    simp only [hH', Matrix.mul_apply, Matrix.transpose_apply, hUk, hUl]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun x _ => by rw [hsym x l]; ring
  have e10 : H' l k = (H *ᵥ v) l := by
    simp only [hH', Matrix.mul_apply, Matrix.transpose_apply, hUk, hUl]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_eq]
    simp only [Matrix.mulVec, dotProduct]
  have e11 : H' l l = H l l := by
    simp only [hH', Matrix.mul_apply, Matrix.transpose_apply, hUl]
    simp [ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
  have hblock : H'.submatrix ![k, l] ![k, l] = !![0, (H *ᵥ v) l; (H *ᵥ v) l, H l l] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [e00, e01, e10, e11]
  have hdet : IsUnit (H'.submatrix ![k, l] ![k, l]).det := by
    rw [hblock, Matrix.det_fin_two_of]
    simpa using hvl.pow 2 |>.neg
  obtain ⟨S, hS, hc', hd⟩ := split_at H' hHess' hkl hdet
  rw [hblock] at hc' hd
  refine ⟨S, hS, hc.trans hc', ?_⟩
  have h1 : H'.det = U.det ^ 2 * H.det := by
    rw [hH', Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]; ring
  rw [hdU] at h1
  rw [← h1, hd, Matrix.det_fin_two_of]
  ring

end Split

end QuadFormsKB.Hanke2011Structure.Dyadic
