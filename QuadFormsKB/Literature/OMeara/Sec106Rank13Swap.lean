/-
# O'Meara §106F, toward 106.r38: the listed lattices have improper automorphisms

The transposition of the coordinates $x_0, x_1$ is an isometry of $I_n$ of determinant $-1$ that maps $\mathbb Z^n$ and
$E_m \perp \mathbb Z^{n-m}$ ($m \ge 2$) onto themselves. So isometries onto these lattices can be taken proper
(`isProperIsometric_of_isIsometric_swap`). Indices are 0-based.
-/
import QuadFormsKB.Literature.OMeara.Sec106Rank13Basis
import QuadFormsKB.Literature.OMeara.Sec106Rank13Bridge

open Matrix NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {n : ℕ}

theorem swapGL_mulVec (hn : 2 ≤ n) (y : Fin n → ℚ) :
    (swapGL hn).val *ᵥ y = y ∘ Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ := by
  rw [swapGL_val, Matrix.permMatrix_mulVec]

/-- A submodule closed under the swap of $x_0$, $x_1$ is mapped onto itself by `swapGL`. -/
theorem glImage_swapGL_eq (hn : 2 ≤ n) {L : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (hL : ∀ y ∈ L, y ∘ Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ ∈ L) :
    glImage (swapGL hn) L = L := by
  ext x
  rw [mem_glImage]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [swapGL_mulVec]; exact hL y hy
  · intro hx
    refine ⟨x ∘ Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩, hL x hx, ?_⟩
    rw [swapGL_mulVec]
    funext i; simp [Equiv.swap_apply_self]

theorem intVec_swap (hn : 2 ≤ n) : glImage (swapGL hn) (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) = intVec :=
  glImage_swapGL_eq hn fun y hy => mem_intVec_iff_int.mpr fun i => mem_intVec_iff_int.mp hy _

/-- $E_m$ is stable under permutations of the coordinates. -/
theorem omearaE_comp_perm {m : ℕ} (h4 : 4 ∣ m) (hm : 0 < m) (e : Equiv.Perm (Fin m)) {v : Fin m → ℚ}
    (hv : v ∈ omearaE m) : v ∘ e ∈ omearaE m := by
  obtain ⟨h1, h2, s, hs⟩ := (omeara106_11 h4 hm v).mp hv
  refine (omeara106_11 h4 hm _).mpr ⟨fun i => h1 (e i), fun i j => h2 (e i) (e j), s, ?_⟩
  rw [← hs]
  exact Equiv.sum_comp e v

theorem omearaEPerp_swap {m : ℕ} (h4 : 4 ∣ m) (h8 : 8 ≤ m) (hmn : m ≤ n) :
    glImage (swapGL (n := n) (by omega)) (omearaEPerp m n) = omearaEPerp m n := by
  refine glImage_swapGL_eq _ fun y hy => ?_
  obtain ⟨hh, ht⟩ := hy
  refine ⟨?_, fun i hi => ?_⟩
  · have e : omearaEPerpHead m n (y ∘ Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) =
        (omearaEPerpHead m n y) ∘ Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩ := by
      funext j
      simp only [omearaEPerpHead, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
      rw [dif_pos (by omega), dif_pos (by have := (Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩ j).isLt; omega)]
      congr 1
      simp only [Equiv.swap_apply_def, Fin.ext_iff]
      split_ifs <;> simp_all <;> omega
    change omearaEPerpHead m n _ ∈ omearaE m
    rw [e]
    exact omearaE_comp_perm h4 (by omega) _ hh
  · have hfix : Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ i = i := by
      apply Equiv.swap_apply_of_ne_of_ne <;> intro h <;> rw [h] at hi <;> simp at hi <;> omega
    simp only [Function.comp_apply, hfix]
    exact ht i hi

end QuadFormsKB.Lattices
