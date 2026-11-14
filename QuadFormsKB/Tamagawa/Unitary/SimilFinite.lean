import QuadFormsKB.Lattices.Finite

/-! # Finiteness of similitude endomorphisms of a definite lattice

For an integral lattice $M$ in a totally positive definite quadratic space $(F^n, b)$ and a fixed multiplier
$c \in F$, there are only finitely many matrices $A$ with $AM \subseteq M$ and $b(Ax, Ax) = c\,b(x,x)$.
The proof adapts `finite_autLat`: such an $A$ is determined by the images of a $\mathbb Z$-frame of $M$; each image
is a lattice vector whose coordinate vector $y$ satisfies $y^{\mathsf T} G y = \mathrm{Tr}_{F/\mathbb Q}(c\,b(m_j,m_j))$,
a quantity independent of $A$, so $y$ lies in a finite set of short vectors.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Unitary

open QuadFormsKB.Lattices Matrix NumberField

variable {F : Type*} [Field F] [NumberField F] {n : ℕ}

/-- **Finitely many similitude endomorphisms**: for an integral lattice $M$ in a totally positive definite space and $c\in F$, the matrices $A$ with $AM\subseteq M$ and $b(Ax,Ax) = c\,b(x,x)$ form a finite set (as `finite_autLat`: $A$ is determined by the images of a $\mathbb Z$-frame, which are short vectors). -/
@[kb "omeara1963" "§82C, p. 223 (finiteness of O(L), adapted to similitudes)"]
theorem finite_similEndo {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) {M : Submodule (𝓞 F) (Fin n → F)}
    (hM : M.IsLattice F) (hMi : IsIntegral Q M) (c : F) :
    {A : Matrix (Fin n) (Fin n) F | (∀ x ∈ M, A *ᵥ x ∈ M) ∧
      ∀ x, bil Q (A *ᵥ x) (A *ᵥ x) = c * bil Q x x}.Finite := by
  classical
  have := zLat_isLattice hM
  set b := frame hM
  set N := zrank F n
  set G := gram Q b
  set t : Fin N → ℚ := fun j => trForm Q (c • (b j : Fin n → F)) (b j : Fin n → F) with ht
  let f : Matrix (Fin n) (Fin n) F → (Fin N → Fin N → ℤ) := fun A j =>
    if h : A *ᵥ (b j : Fin n → F) ∈ M then b.repr ⟨_, h⟩ else 0
  set S := Set.pi Set.univ fun j : Fin N => {y : Fin N → ℤ | y ⬝ᵥ (G *ᵥ y) ≤ ⌈t j⌉}
  have hS : S.Finite := Set.Finite.pi fun j =>
    finite_short_vectors (gram_isPosDefInt hQ hMi b) ⌈t j⌉
  refine Set.Finite.of_injOn (f := f) (t := S) ?_ ?_ hS
  · rintro A ⟨hA, hc⟩ j -
    have hmem := hA _ (b j).2
    have hfj : f A j = b.repr ⟨_, hmem⟩ := dif_pos hmem
    have h1 := dotProduct_gram Q hMi b (f A j)
    have h2 : ∑ i, f A j i • (b i : Fin n → F) = A *ᵥ (b j : Fin n → F) := by
      rw [hfj]; exact (coe_eq_sum b ⟨_, hmem⟩).symm
    rw [h2, trForm_apply, hc] at h1
    have h3 : ((f A j ⬝ᵥ (G *ᵥ f A j) : ℤ) : ℚ) = t j := by
      rw [h1, ht]
      simp only [trForm_apply, bil_smul_left]
    show f A j ⬝ᵥ (G *ᵥ f A j) ≤ ⌈t j⌉
    have : ((f A j ⬝ᵥ (G *ᵥ f A j) : ℤ) : ℚ) ≤ ⌈t j⌉ := h3 ▸ Int.le_ceil _
    exact_mod_cast this
  · rintro A ⟨hA, -⟩ A' ⟨hA', -⟩ he
    have hb : ∀ j, A *ᵥ (b j : Fin n → F) = A' *ᵥ (b j : Fin n → F) := by
      intro j
      have hm := hA _ (b j).2
      have hm' := hA' _ (b j).2
      have e1 : A *ᵥ (b j : Fin n → F) = ∑ i, f A j i • (b i : Fin n → F) := by
        rw [show f A j = b.repr ⟨_, hm⟩ from dif_pos hm]; exact coe_eq_sum b ⟨_, hm⟩
      have e2 : A' *ᵥ (b j : Fin n → F) = ∑ i, f A' j i • (b i : Fin n → F) := by
        rw [show f A' j = b.repr ⟨_, hm'⟩ from dif_pos hm']; exact coe_eq_sum b ⟨_, hm'⟩
      rw [e1, e2, he]
    have hlin : (Matrix.mulVecLin A).restrictScalars ℚ = (Matrix.mulVecLin A').restrictScalars ℚ := by
      refine (b.extendOfIsLattice ℚ).ext fun j => ?_
      simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Module.Basis.extendOfIsLattice_apply]
      exact hb j
    ext i j
    have := congrFun (LinearMap.congr_fun hlin (Pi.single j 1)) i
    simpa using this

end QuadFormsKB.Tamagawa.Unitary
