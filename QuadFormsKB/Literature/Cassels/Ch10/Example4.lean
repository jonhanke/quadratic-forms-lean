/-
# Cassels, Chapter 10, Example 4 (i): the centre of the Clifford algebra of a ternary space

**Setting.** As in `Ch10/Ternary.lean`: a field $k$ of characteristic $\ne 2$, a regular quadratic space $(V, Q)$ of
dimension $3$ with an orthogonal basis $\vec e_0, \vec e_1, \vec e_2$ of anisotropic vectors, $f_i = \phi(\vec e_i)$.
The determinant of $V$ is $d = f_0f_1f_2$ (up to squares).

**Proves** (Cassels, *Rational Quadratic Forms*, Ch. 10, Example 4 (i), p. 193): the centre of $C(V)$ has dimension
$2$ over $k$, with basis $1, \epsilon$ where $\epsilon = \vec e_0\vec e_1\vec e_2$ and $\epsilon^2 = -d$
(`ternEps_sq`, `ternEps_comm`, `mem_center_iff_ternary`, `finrank_center_ternary`).

**Proof.** $\epsilon$ commutes with each $\vec e_i$ (moving $\vec e_i$ across $\epsilon$ passes two anticommuting factors).
If $z$ is central, so are its even and odd parts; the even part is a scalar (Lemma 2.3), and the odd part times
$\epsilon$ is even and central, hence a scalar, so the odd part is a multiple of $\epsilon^{-1} = -d^{-1}\epsilon$.
-/
import QuadFormsKB.Literature.Cassels.Ch10.Ternary

open Module CliffordAlgebra

namespace QuadFormsKB.Cassels

set_option linter.unusedSectionVars false

variable {k V : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] {Q : QuadraticForm k V}

section Basis

variable (Q) (e : Basis (Fin 3) k V)

/-- $\epsilon = \vec e_0\vec e_1\vec e_2$. -/
noncomputable def ternEps : CliffordAlgebra Q := ι Q (e 0) * ι Q (e 1) * ι Q (e 2)

variable {Q e}
variable (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (e i) (e j) = 0)
include horth

/-- $\epsilon^2 = -f_0f_1f_2$. -/
theorem ternEps_sq : ternEps Q e * ternEps Q e = algebraMap k _ (-(Q (e 0) * Q (e 1) * Q (e 2))) := by
  simp only [ternEps, mul_assoc, t_t10 horth, t_t20 horth, t_t21 horth, t_p10 horth, t_p20 horth, t_p21 horth,
    t_s horth, t_q horth, mul_neg, neg_mul, neg_neg, mul_smul_comm, smul_neg, mul_one, smul_mul_assoc, one_mul]
  rw [Algebra.algebraMap_eq_smul_one, smul_smul, smul_smul, neg_smul]
  congr 2
  rw [mul_assoc]
  ring


/-- $\epsilon$ commutes with every vector. -/
theorem ternEps_comm_ι (x : V) : ternEps Q e * ι Q x = ι Q x * ternEps Q e := by
  have h : ∀ i, ternEps Q e * ι Q (e i) = ι Q (e i) * ternEps Q e := by
    intro i
    fin_cases i <;>
    · simp only [ternEps, mul_assoc, t_t10 horth, t_t20 horth, t_t21 horth, t_p10 horth, t_p20 horth, t_p21 horth,
        t_s horth, t_q horth, mul_neg, neg_mul, neg_neg, mul_smul_comm, smul_neg, mul_one, smul_mul_assoc, one_mul,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
  rw [← e.sum_repr x]
  simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, h]

/-- $\epsilon$ is central in $C(V)$. -/
theorem ternEps_comm (w : CliffordAlgebra Q) : ternEps Q e * w = w * ternEps Q e := by
  induction w using CliffordAlgebra.induction with
  | algebraMap r => exact (Algebra.commutes r _).symm
  | ι x => exact ternEps_comm_ι horth x
  | mul a b ha hb => rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]
  | add a b ha hb => rw [mul_add, add_mul, ha, hb]

variable (hne : ∀ i, Q (e i) ≠ 0) (hQ : (QuadraticMap.associated Q).Nondegenerate)
include hne hQ

/-- **Cassels, Ch. 10, Example 4 (i)** (p. 193): for $n = 3$, $z$ is central in $C(V)$ if and only if
$z = a + b\epsilon$ with $a, b \in k$. -/
@[kb "cassels1978" "Ch. 10, Example 4 (i), p. 193 (the centre of C(V) is k + kε)"]
theorem mem_center_iff_ternary (z : CliffordAlgebra Q) :
    (∀ w, z * w = w * z) ↔ ∃ a b : k, z = algebraMap k _ a + b • ternEps Q e := by
  constructor
  · intro h
    have hz : ∀ x, z * ι Q x = ι Q x * z := fun x => h _
    have hz' : ∀ x, involute z * ι Q x = ι Q x * involute z := by
      intro x
      have := congrArg involute (hz x)
      rw [map_mul, map_mul, involute_ι] at this
      simpa using this
    obtain ⟨r, h2⟩ : ∃ r : k, r + r = 1 := ⟨⅟(2 : k), by rw [← two_mul]; exact mul_invOf_self _⟩
    set z0 : CliffordAlgebra Q := r • (z + involute z) with hz0def
    set z1 : CliffordAlgebra Q := r • (z - involute z) with hz1def
    have hsplit : z = z0 + z1 := by
      have : z0 + z1 = (r + r) • z := by rw [hz0def, hz1def]; module
      rw [this, h2, one_smul]
    have hz0e : z0 ∈ evenOdd Q 0 := by
      apply mem_even_of_involute_eq Q
      rw [hz0def, map_smul, map_add, involute_involute, add_comm]
    have hz1o : z1 ∈ evenOdd Q 1 := by
      apply mem_odd_of_involute_eq_neg Q
      rw [hz1def, map_smul, map_sub, involute_involute]
      module
    have hz0c : ∀ x, z0 * ι Q x = ι Q x * z0 := by
      intro x
      simp only [hz0def, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, hz x, hz' x]
    have hz1c : ∀ x, z1 * ι Q x = ι Q x * z1 := by
      intro x
      simp only [hz1def, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, hz x, hz' x]
    obtain ⟨a, ha⟩ := mem_range_algebraMap_of_even_comm hQ hz0e hz0c
    have hεo : ternEps Q e ∈ evenOdd Q 1 := by
      have := SetLike.mul_mem_graded (t_ee (e 0) (e 1)) (ι_mem_evenOdd_one Q (e 2))
      rwa [zero_add] at this
    have hze : z1 * ternEps Q e ∈ evenOdd Q 0 := by
      have := SetLike.mul_mem_graded hz1o hεo
      rwa [show (1 : ZMod 2) + 1 = 0 from by decide] at this
    have hzc : ∀ x, z1 * ternEps Q e * ι Q x = ι Q x * (z1 * ternEps Q e) := by
      intro x
      rw [mul_assoc, ternEps_comm_ι horth x, ← mul_assoc, hz1c x, mul_assoc]
    obtain ⟨c, hc⟩ := mem_range_algebraMap_of_even_comm hQ hze hzc
    have hD : (-(Q (e 0) * Q (e 1) * Q (e 2))) ≠ 0 := by
      have := hne 0; have := hne 1; have := hne 2
      simpa using mul_ne_zero (mul_ne_zero (hne 0) (hne 1)) (hne 2)
    have hz1eq : z1 = (c * (-(Q (e 0) * Q (e 1) * Q (e 2)))⁻¹) • ternEps Q e := by
      calc z1 = z1 * algebraMap k _ ((-(Q (e 0) * Q (e 1) * Q (e 2))) * (-(Q (e 0) * Q (e 1) * Q (e 2)))⁻¹) := by
            rw [mul_inv_cancel₀ hD, map_one, mul_one]
        _ = z1 * algebraMap k _ (-(Q (e 0) * Q (e 1) * Q (e 2))) *
              algebraMap k _ ((-(Q (e 0) * Q (e 1) * Q (e 2)))⁻¹) := by rw [map_mul]; exact (mul_assoc _ _ _).symm
        _ = (z1 * ternEps Q e) * ternEps Q e * algebraMap k _ ((-(Q (e 0) * Q (e 1) * Q (e 2)))⁻¹) := by
            rw [← ternEps_sq horth]; simp only [mul_assoc]
        _ = _ := by
            rw [← hc]
            simp [Algebra.algebraMap_eq_smul_one, smul_smul]
            congr 1; ring
    exact ⟨a, _, by rw [hsplit, ← ha, hz1eq]⟩
  · rintro ⟨a, b, rfl⟩ w
    rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, Algebra.commutes, ternEps_comm horth w]

/-- **Cassels, Ch. 10, Example 4 (i)** (p. 193): for $n = 3$ the centre of $C(V)$ has dimension $2$ over $k$, with
basis $1, \epsilon$, and $\epsilon^2 = -f_0f_1f_2 \in -d(k^\times)^2$ (`ternEps_sq`). -/
@[kb "cassels1978" "Ch. 10, Example 4 (i), p. 193 (the centre has dimension 2)"]
theorem finrank_center_ternary : finrank k (Subalgebra.center k (CliffordAlgebra Q)) = 2 := by
  have hspan : Subalgebra.toSubmodule (Subalgebra.center k (CliffordAlgebra Q)) =
      Submodule.span k (Set.range ![(1 : CliffordAlgebra Q), ternEps Q e]) := by
    have hr : Set.range ![(1 : CliffordAlgebra Q), ternEps Q e] = {1, ternEps Q e} := by
      ext y; simp [or_comm]
    rw [hr]
    ext z
    rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_center_iff, Submodule.mem_span_pair]
    constructor
    · intro h
      obtain ⟨a, b, hab⟩ := (mem_center_iff_ternary horth hne hQ z).1 (fun w => (h w).symm)
      exact ⟨a, b, by rw [hab]; simp [Algebra.algebraMap_eq_smul_one]⟩
    · rintro ⟨a, b, rfl⟩ w
      exact ((mem_center_iff_ternary horth hne hQ _).2 ⟨a, b, by simp [Algebra.algebraMap_eq_smul_one]⟩ w).symm
  have hε0 : ternEps Q e ≠ 0 := by
    intro h0
    have := ternEps_sq horth (Q := Q) (e := e)
    rw [h0, mul_zero, eq_comm, ← map_zero (algebraMap k (CliffordAlgebra Q))] at this
    have := (algebraMap k (CliffordAlgebra Q)).injective this
    have := mul_ne_zero (mul_ne_zero (hne 0) (hne 1)) (hne 2)
    simp_all
  have hinv : involute (ternEps Q e) = -ternEps Q e := by
    simp [ternEps, involute_ι]
  have hli : LinearIndependent k ![(1 : CliffordAlgebra Q), ternEps Q e] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h' := congrArg involute h
    rw [map_add, map_smul, map_smul, hinv, map_one, smul_neg, map_zero] at h'
    have h3 : (2 : k) • (s • (1 : CliffordAlgebra Q)) = 0 := by linear_combination (norm := module) h + h'
    have h4 : (2 : k) • (t • ternEps Q e) = 0 := by linear_combination (norm := module) h - h'
    have h2 : (2 : k) ≠ 0 := Invertible.ne_zero (2 : k)
    rw [smul_eq_zero] at h3 h4
    constructor
    · rcases h3 with h3 | h3
      · exact absurd h3 h2
      · rw [Algebra.smul_def, mul_one] at h3
        exact (algebraMap k (CliffordAlgebra Q)).injective (by rw [h3, map_zero])
    · rcases h4 with h4 | h4
      · exact absurd h4 h2
      · exact (smul_eq_zero.1 h4).resolve_right hε0
  rw [← Subalgebra.finrank_toSubmodule, hspan, finrank_span_eq_card hli]
  simp

end Basis

end QuadFormsKB.Cassels
