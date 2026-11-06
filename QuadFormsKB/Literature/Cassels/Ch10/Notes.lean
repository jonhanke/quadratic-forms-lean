/-
# Cassels, Chapter 10, Notes: the even Clifford algebra of an anisotropic ternary space is a division algebra

**Item.** The Notes to Chapter 10 (pp. 191–192) are mostly bibliographical. Their mathematical claim: for a ternary form
$f$ the even Clifford algebra $C_0(f)$ is a generalized quaternion algebra (Theorem 3.1, Corollary 2,
`Ch10/Ternary.lean`), and "it is a division algebra provided that $f$ is anisotropic".

**Proves** `exists_inverse_of_anisotropic`: for a regular anisotropic ternary space every nonzero $u \in C_0(V)$ has an
inverse in $C_0(V)$.

**Proof.** $uu' = c \in k$ (Corollary 2). If $c \ne 0$, $c^{-1}u'$ is the inverse (Lemma 2.5). If $c = 0$ and
$u \ne 0$, write $u = c_0 + \vec y\epsilon$ with $\epsilon = \vec e_0\vec e_1\vec e_2$ ($C_0(V) = k \oplus V\epsilon$, since
$\vec e_i\epsilon = f_iE_i$), so $0 = uu' = c_0^2 + d\,\phi(\vec y)$ with $d = f_0f_1f_2$; anisotropy forces $c_0 \ne 0$.
For $\vec z \ne 0$ orthogonal to $\vec y$, $\vec w = u\vec z u'$ is a vector (odd and fixed by the involution) with
$\vec w^2 = u\vec z(u'u)\vec zu' = 0$, and $\vec w = 2c_0(c_0\vec z + \epsilon\vec y\vec z)$ with $\epsilon\vec y\vec z \perp \vec z$, so
$\vec w \ne 0$: an isotropic vector, a contradiction.
-/
import QuadFormsKB.Literature.Cassels.Ch10.Example4

open Module CliffordAlgebra

namespace QuadFormsKB.Cassels

set_option linter.unusedSectionVars false

variable {k V : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] {Q : QuadraticForm k V}


omit [Invertible (2 : k)] in
theorem notes_exists_polar_zero (y : V) (hn : finrank k V = 3) :
    ∃ z : V, z ≠ 0 ∧ QuadraticMap.polar Q y z = 0 := by
  have hlt : finrank k k < finrank k V := by rw [finrank_self, hn]; norm_num
  have := (QuadraticMap.polarBilin Q y).ker_ne_bot_of_finrank_lt hlt
  obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).1 this
  exact ⟨z, hz0, by simpa using hz⟩

theorem notes_odd_fixed {e : Basis (Fin 3) k V}
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (e i) (e j) = 0) {w : CliffordAlgebra Q}
    (hw : w ∈ evenOdd Q 1) (hrev : reverse w = w) : ∃ v : V, w = ι Q v := by
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 (t_odd_mem horth hw)
  simp only [Fin.sum_univ_four, tv1] at hd
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue] at hd
  have hr2 := hrev
  rw [← hd] at hr2
  simp only [map_add, map_smul, reverse_ι, t_revT horth, smul_neg] at hr2
  have hneg : d 3 • (ι Q (e 0) * (ι Q (e 1) * ι Q (e 2))) =
      -(d 3 • (ι Q (e 0) * (ι Q (e 1) * ι Q (e 2)))) := by
    exact (add_left_cancel hr2).symm
  have h0 := eq_zero_of_eq_neg Q hneg
  refine ⟨d 0 • e 0 + d 1 • e 1 + d 2 • e 2, ?_⟩
  rw [← hd, h0, add_zero]
  simp only [map_smul, map_add]

theorem notes_E_eq {e : Basis (Fin 3) k V}
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (e i) (e j) = 0) (i : Fin 3) :
    ι Q (e i) * ternEps Q e = Q (e i) • ternE Q e i := by
  fin_cases i
  · show ι Q (e 0) * (ι Q (e 0) * ι Q (e 1) * ι Q (e 2)) = Q (e 0) • (ι Q (e 1) * ι Q (e 2))
    simp only [mul_assoc, t_s horth]
  · show ι Q (e 1) * (ι Q (e 0) * ι Q (e 1) * ι Q (e 2)) = Q (e 1) • (ι Q (e 2) * ι Q (e 0))
    simp only [mul_assoc, t_t10 horth, t_s horth, t_p20 horth, mul_smul_comm, smul_neg, mul_neg]
  · show ι Q (e 2) * (ι Q (e 0) * ι Q (e 1) * ι Q (e 2)) = Q (e 2) • (ι Q (e 0) * ι Q (e 1))
    simp only [mul_assoc, t_t20 horth, t_t21 horth, t_q horth, mul_neg, neg_neg, mul_smul_comm, smul_neg,
      mul_one]

theorem notes_decomp {e : Basis (Fin 3) k V}
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (e i) (e j) = 0) (hne : ∀ i, Q (e i) ≠ 0)
    (c : Fin 4 → k) :
    ∃ y : V, ternElt Q e c = algebraMap k _ (c 0) + ι Q y * ternEps Q e := by
  refine ⟨(c 1 / Q (e 0)) • e 0 + (c 2 / Q (e 1)) • e 1 + (c 3 / Q (e 2)) • e 2, ?_⟩
  simp only [map_add, map_smul, add_mul, smul_mul_assoc, notes_E_eq horth, smul_smul,
    div_mul_cancel₀ _ (hne _), ternElt, add_assoc]

/-- **Cassels, Ch. 10, Notes** (p. 192): if $V$ is a regular anisotropic ternary space, $C_0(V)$ is a division
algebra: every nonzero $u \in C_0(V)$ has an inverse in $C_0(V)$. -/
@[kb "cassels1978" "Ch. 10, Notes, p. 192 (C₀(f) is a division algebra if f is anisotropic)"]
theorem exists_inverse_of_anisotropic (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : finrank k V = 3)
    (haniso : ∀ x : V, Q x = 0 → x = 0) {u : CliffordAlgebra Q} (hu : u ∈ evenOdd Q 0) (hu0 : u ≠ 0) :
    ∃ w ∈ evenOdd Q 0, u * w = 1 ∧ w * u = 1 := by
  obtain ⟨e, horth, hne⟩ := t_exists_basis hQ hn
  obtain ⟨c, hc⟩ := mul_reverse_mem_of_even hQ hn hu
  by_cases hc0 : c = 0
  swap
  · obtain ⟨-, h1, h2⟩ := inverse_of_mul_reverse Q hc0 hc
    exact ⟨_, Submodule.smul_mem _ _ (t_rev_even horth hu), h1, h2⟩
  exfalso
  subst hc0
  rw [map_zero] at hc
  obtain ⟨c', hc'⟩ := (mem_evenOdd_zero_iff_ternary horth _).1 hu
  obtain ⟨y, hy⟩ := notes_decomp horth hne c'
  have hy' : u = algebraMap k _ (c' 0) + ι Q y * ternEps Q e := by rw [hc', hy]
  clear hy hc'
  generalize c' 0 = c0 at hy'
  -- notation
  set ε := ternEps Q e with hεdef
  set A : CliffordAlgebra Q := ι Q y * ε with hA
  set a : CliffordAlgebra Q := algebraMap k _ c0 with ha
  set d : k := Q (e 0) * Q (e 1) * Q (e 2) with hd
  have hdne : d ≠ 0 := mul_ne_zero (mul_ne_zero (hne 0) (hne 1)) (hne 2)
  have hε2 : ε * ε = algebraMap k _ (-d) := ternEps_sq horth
  have hεr : reverse ε = -ε := by
    have : ε = ι Q (e 0) * (ι Q (e 1) * ι Q (e 2)) := by simp only [hεdef, ternEps, mul_assoc]
    rw [this]; exact t_revT horth
  have hAA : A * A = algebraMap k _ (-(d * Q y)) := by
    calc A * A = ι Q y * (ε * ι Q y) * ε := by simp only [hA, mul_assoc]
      _ = (ι Q y * ι Q y) * (ε * ε) := by rw [ternEps_comm_ι horth]; simp only [mul_assoc]; rfl
      _ = _ := by rw [ι_sq_scalar, hε2, ← map_mul]; congr 1; ring
  have hrA : reverse A = -A := by
    rw [hA, reverse.map_mul, reverse_ι, hεr, neg_mul, ternEps_comm_ι horth]
  have hru : reverse u = a - A := by
    rw [hy', map_add, hrA, ha, reverse.commutes]; rw [sub_eq_add_neg]
  have haA : a * A = A * a := Algebra.commutes c0 A
  have huu : u * reverse u = algebraMap k _ (c0 * c0 + d * Q y) := by
    have h : (a + A) * (a - A) = a * a - A * A := by simp only [add_mul, mul_sub, haA]; abel
    rw [hru, hy', h, hAA, ha, ← map_mul, ← map_sub]
    congr 1; ring
  have hs : c0 * c0 + d * Q y = 0 := by
    have := hc
    rw [huu, ← map_zero (algebraMap k (CliffordAlgebra Q))] at this
    exact (algebraMap k (CliffordAlgebra Q)).injective this
  have hAa : A * A = a * a := by
    rw [hAA, ha, ← map_mul]; congr 1; linear_combination (-1 : k) * hs
  have hc0 : c0 ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_add] at hs
    have hQy : Q y = 0 := (mul_eq_zero.1 hs).resolve_left hdne
    have : y = 0 := haniso y hQy
    apply hu0
    rw [hy', ha, hA, h0, this]
    simp
  obtain ⟨z, hz0, hz⟩ := notes_exists_polar_zero (Q := Q) y hn
  have hanti : ι Q y * ι Q z = -(ι Q z * ι Q y) := by
    have := ι_mul_ι_add_swap (Q := Q) y z
    rw [hz, map_zero] at this
    exact eq_neg_of_add_eq_zero_left this
  have hAz : A * ι Q z = -(ι Q z * A) := by
    calc A * ι Q z = ι Q y * (ε * ι Q z) := by simp only [hA, mul_assoc]
      _ = (ι Q y * ι Q z) * ε := by rw [ternEps_comm_ι horth]; simp only [mul_assoc]; rfl
      _ = _ := by rw [hanti, neg_mul, hA, mul_assoc]
  have hA2 : A * (A * ι Q z) = (c0 * c0) • ι Q z := by
    rw [← mul_assoc, hAa, ha, ← map_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  have hw : (a + A) * ι Q z * (a - A) = (2 * c0 * c0) • ι Q z + (2 * c0) • (A * ι Q z) := by
    have h3 : ι Q z * A = -(A * ι Q z) := by rw [hAz, neg_neg]
    rw [ha, Algebra.algebraMap_eq_smul_one]
    simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, sub_mul, mul_assoc, h3, mul_neg,
      hA2, smul_smul, smul_neg, smul_add]
    module
  have hru_u : reverse u * u = 0 := by
    have h : (a - A) * (a + A) = a * a - A * A := by simp only [mul_add, sub_mul, haA]; abel
    rw [hru, hy', h, hAa, sub_self]
  have hru_ev := t_rev_even horth hu
  have hwodd : u * ι Q z * reverse u ∈ evenOdd Q 1 := by
    have := SetLike.mul_mem_graded (SetLike.mul_mem_graded hu (ι_mem_evenOdd_one Q z)) hru_ev
    rwa [zero_add, add_zero] at this
  have hrevw : reverse (u * ι Q z * reverse u) = u * ι Q z * reverse u := by
    rw [reverse.map_mul, reverse.map_mul, reverse_reverse, reverse_ι, mul_assoc]
  obtain ⟨v, hv⟩ := notes_odd_fixed horth hwodd hrevw
  have hww : (u * ι Q z * reverse u) * (u * ι Q z * reverse u) = 0 := by
    calc (u * ι Q z * reverse u) * (u * ι Q z * reverse u)
        = u * ι Q z * (reverse u * u) * ι Q z * reverse u := by simp only [mul_assoc]
      _ = 0 := by rw [hru_u]; simp
  rw [hv, ι_sq_scalar, ← map_zero (algebraMap k (CliffordAlgebra Q))] at hww
  have hQv : Q v = 0 := (algebraMap k (CliffordAlgebra Q)).injective hww
  have hv0 : v = 0 := haniso v hQv
  have hw0 : u * ι Q z * reverse u = 0 := by rw [hv, hv0, map_zero]
  have hw' : u * ι Q z * reverse u = (2 * c0 * c0) • ι Q z + (2 * c0) • (A * ι Q z) := by
    rw [hru, hy']; exact hw
  rw [hw'] at hw0
  have hzz : ι Q z * ι Q z = Q z • (1 : CliffordAlgebra Q) := by
    rw [ι_sq_scalar, Algebra.algebraMap_eq_smul_one]
  have h5 : ((2 * c0 * c0) • ι Q z + (2 * c0) • (A * ι Q z)) * ι Q z = (2 * c0 * Q z) • u := by
    rw [hy', ha, Algebra.algebraMap_eq_smul_one]
    simp only [add_mul, smul_mul_assoc, mul_assoc, hzz, mul_smul_comm, mul_one, smul_add, smul_smul]
    module
  rw [hw0, zero_mul] at h5
  have h6 := (smul_eq_zero.1 h5.symm).resolve_right hu0
  have h2 : (2 : k) ≠ 0 := Invertible.ne_zero (2 : k)
  have hQz : Q z = 0 := by
    rcases mul_eq_zero.1 h6 with h | h
    · exact absurd h (mul_ne_zero h2 hc0)
    · exact h
  exact hz0 (haniso z hQz)

end QuadFormsKB.Cassels
