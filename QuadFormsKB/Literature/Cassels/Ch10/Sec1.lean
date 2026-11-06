/-
# Cassels, Chapter 10, §1: the motivating example — the spin group of a definite real space

**Item.** Cassels' introduction to Chapter 10 (pp. 169–171) motivates the spin group by Hamilton's quaternions:
for $V = \mathbb R^3$ with $\phi = x_1^2 + x_2^2 + x_3^2$, the quaternions $u$ of norm $1$ act on $V$ by
$\vec x \mapsto u\vec x u'$, this maps onto the rotation group $O^+(V)$ with kernel $\{\pm 1\}$, and the group of such
$u$ is the $3$-sphere $u_0^2 + u_1^2 + u_2^2 + u_3^2 = 1$.

**Formalized** in the general language of §3 (the quaternions are $C_0(V)$, Theorem 3.1 Corollary 2):
* for a positive definite real space the spinor norm is trivial, $\Theta = O^+(V)$
  (`orthPrime_eq_orthPlus_of_posDef`), so $u \mapsto T_u$ maps $\operatorname{Spin}(V)$ onto $O^+(V)$
  (`range_spinConj_of_posDef`), with kernel $\{\pm 1\}$ (Theorem 3.3, `spinConj_eq_one_iff`);
* for $\dim V = 3$ with an orthonormal basis, $\operatorname{Spin}(V)$ consists exactly of the
  $u = u_0 + u_1E_0 + u_2E_1 + u_3E_2$ with $u_0^2 + u_1^2 + u_2^2 + u_3^2 = 1$ (`mem_spinGroup_iff_sphere`).
-/
import QuadFormsKB.Literature.Cassels.Ch10.Ternary

open Module CliffordAlgebra

namespace QuadFormsKB.Cassels

set_option linter.unusedSectionVars false

open QuadFormsKB.OMeara

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] {Q : QuadraticForm ℝ V}

/-- **For a positive definite real space the spinor norm is trivial**: $\Theta = O^+(V)$ (all values of $\phi$ are
positive, hence squares). -/
theorem orthPrime_eq_orthPlus_of_posDef (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hpos : ∀ x, x ≠ 0 → 0 < Q x) : orthPrime Q = orthPlus Q := by
  refine le_antisymm (orthPrime_le_orthPlus Q) fun σ hσ => ⟨hσ, ?_⟩
  obtain ⟨l, hl, hσl, -⟩ := exists_symmetry_prod_eq_length_le Q hQ hσ.1
  have hprod : 0 < (l.map Q).prod := by
    refine List.prod_pos fun c hc => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hc
    exact hpos y fun h => hl y hy (by rw [h, map_zero])
  have h1 : HasSpinorNorm Q σ (l.map Q).prod := ⟨l, hl, hσl, 1, one_ne_zero, by simp⟩
  refine HasSpinorNorm.of_eq_mul_sq Q h1 (s := (Real.sqrt (l.map Q).prod)⁻¹)
    (inv_ne_zero (Real.sqrt_pos.2 hprod).ne') ?_
  rw [inv_pow, Real.sq_sqrt hprod.le, mul_inv_cancel₀ hprod.ne']

/-- **Cassels, Ch. 10, §1** (pp. 169–171), first part: for a positive definite real space $V \ne 0$, $u \mapsto T_u$
maps $\operatorname{Spin}(V)$ onto the rotation group $O^+(V)$ (its kernel is $\{\pm 1\}$ by Theorem 3.3,
`spinConj_eq_one_iff`). -/
@[kb "cassels1978" "Ch. 10, §1, pp. 169–171 (Spin(V) → O⁺(V) onto for definite real V, kernel ±1)"]
theorem range_spinConj_of_posDef [Nontrivial V] (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hpos : ∀ x, x ≠ 0 → 0 < Q x) : (spinConj (Q := Q)).range = orthPlus Q := by
  rw [range_spinConj hQ, orthPrime_eq_orthPlus_of_posDef hQ hpos]

/-- **Cassels, Ch. 10, §1** (pp. 169–171), second part: for $\dim V = 3$ and an orthonormal basis
$\vec e_0, \vec e_1, \vec e_2$ ($\phi(\vec e_i) = 1$), the spin group is the $3$-sphere: $u \in \operatorname{Spin}(V)$ if and
only if $u = u_0 + u_1E_0 + u_2E_1 + u_3E_2$ with $u_0^2 + u_1^2 + u_2^2 + u_3^2 = 1$. -/
@[kb "cassels1978" "Ch. 10, §1, p. 171 (Spin(ℝ³) is the 3-sphere of quaternions of norm 1)"]
theorem mem_spinGroup_iff_sphere (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : finrank ℝ V = 3)
    (e : Basis (Fin 3) ℝ V) (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (e i) (e j) = 0)
    (hone : ∀ i, Q (e i) = 1) (u : CliffordAlgebra Q) :
    u ∈ spinGroup Q ↔ ∃ c : Fin 4 → ℝ, u = ternElt Q e c ∧ c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2 + c 3 ^ 2 = 1 := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hn
  have hnorm : ∀ c : Fin 4 → ℝ, (normForm Q e).eval c = c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2 + c 3 ^ 2 := by
    intro c
    rw [normForm, Siegel.Kneser.eval_diag, Fin.sum_univ_four]
    simp [hone]
  rw [mem_spinGroup_iff hQ]
  constructor
  · rintro ⟨h0, h1, -⟩
    obtain ⟨c, rfl⟩ := (mem_evenOdd_zero_iff_ternary horth _).1 h0
    refine ⟨c, rfl, ?_⟩
    rw [mul_reverse_ternary horth, ← map_one (algebraMap ℝ (CliffordAlgebra Q))] at h1
    rw [← hnorm]; exact (algebraMap ℝ (CliffordAlgebra Q)).injective h1
  · rintro ⟨c, rfl, hc⟩
    have h0 : ternElt Q e c ∈ evenOdd Q 0 := (mem_evenOdd_zero_iff_ternary horth _).2 ⟨c, rfl⟩
    have h1 : ternElt Q e c * reverse (ternElt Q e c) = 1 := by
      rw [mul_reverse_ternary horth, hnorm, hc, map_one]
    refine ⟨h0, h1, fun x => ?_⟩
    obtain ⟨U, hU, hUu⟩ := (mem_M0_iff_ternary hQ hn _).2 ⟨h0, by rw [h1]; exact one_ne_zero⟩
    obtain ⟨y, hy⟩ := hU.2 x
    have hinv : (↑(U⁻¹) : CliffordAlgebra Q) = reverse (ternElt Q e c) := by
      rw [← hUu]
      exact eq_of_mul_eq_one_of_mul_eq_one U.mul_inv (mul_eq_one_comm_of_finiteDimensional ℝ (hUu ▸ h1))
    exact ⟨y, by rw [hy, hinv, hUu]⟩

end QuadFormsKB.Cassels
