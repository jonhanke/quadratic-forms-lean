/-
# Kitaoka 1993, Corollary 2.1.1: finiteness of the class number

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §2.1, Corollary 2.1.1, p. 41 (printed page).

**Proves** `Reduction.corollary211 : Reduction.Corollary211`: for $d \ne 0$ the integral symmetric $m \times m$
matrices of determinant $d$ (definite or indefinite) fall into finitely many classes under
$q \mapsto {}^tu\,q\,u$, $u \in \mathrm{GL}_m(\mathbb Z)$.

*Proof.* Kitaoka derives the corollary from Theorem 2.1.3 through majorants, and remarks (p. 42) that Hermite's bound
for indefinite forms suffices. The repository already has the second route, Cassels' proof of his Theorem 1.1
(Ch. 9, §3), in the matrix form `Siegel.finite_reduction_SL` (`Cassels/Ch9Sec3Finite.lean`): every such matrix is
$\mathrm{SL}_m(\mathbb Z)$-equivalent to one of a finite set. That form is for $m \ge 1$; for $m = 0$ the only matrix
is the empty one, of determinant $1$.
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec3Finite
import QuadFormsKB.Literature.Kitaoka.Ch2Reduction

open Matrix

namespace QuadFormsKB.Kitaoka.Reduction

/-- **Kitaoka 1993, Corollary 2.1.1** (finiteness of class number, p. 41), *proved*: the number of
$\mathrm{GL}_m(\mathbb Z)$-equivalence classes of integral symmetric $m \times m$ matrices of determinant $d \ne 0$ is
finite. -/
@[kb "kitaoka1993" "§2.1, Cor. 2.1.1, p. 41"]
theorem corollary211 : Corollary211 := by
  intro m d hd
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨if d = 1 then {1} else ∅, ?_, ?_⟩
    · intro q hq
      split_ifs at hq with h1
      · rw [Finset.mem_singleton] at hq
        subst hq
        exact ⟨by simp, by simp [h1]⟩
      · simp at hq
    · intro q _ hqd
      have h1 : d = 1 := by rw [← hqd]; simp
      refine ⟨1, by simp [h1], 1, ?_⟩
      ext i
      exact i.elim0
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    obtain ⟨S, hS, hSp, hcov⟩ := Siegel.finite_reduction_SL k d hd
    refine ⟨hS.toFinset, fun q hq => ?_, fun q hq hqd => ?_⟩
    · obtain ⟨h1, h2⟩ := hSp q (hS.mem_toFinset.mp hq)
      exact ⟨h1, h2⟩
    · obtain ⟨F0, hF0, T, hT, hTF⟩ := hcov q hq hqd
      have hTu : IsUnit T.det := by rw [hT]; exact isUnit_one
      have hTinv : (T⁻¹ : Matrix _ _ ℤ) * T = 1 := nonsing_inv_mul T hTu
      have hTinv' : T * (T⁻¹ : Matrix _ _ ℤ) = 1 := mul_nonsing_inv T hTu
      refine ⟨F0, hS.mem_toFinset.mpr hF0, ⟨T⁻¹, T, hTinv, hTinv'⟩, ?_⟩
      show q = (T⁻¹)ᵀ * F0 * T⁻¹
      rw [← hTF]
      simp only [← Matrix.mul_assoc, ← transpose_mul, hTinv', transpose_one, Matrix.one_mul]
      rw [Matrix.mul_assoc, hTinv', Matrix.mul_one]

end QuadFormsKB.Kitaoka.Reduction
