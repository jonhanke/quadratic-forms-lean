/-
# Cassels, Chapter 10, Theorem 3.1, Corollary 2: the even Clifford algebra of a ternary space

**Setting.** As in `Ch10/SpinGroup.lean`: a field $k$ of characteristic $\ne 2$, a regular quadratic space
$(V, Q)$, now of dimension $n = 3$, with an orthogonal basis $\vec e_0, \vec e_1, \vec e_2$ of anisotropic vectors
(`e : Basis (Fin 3) k V`), $f_i = \phi(\vec e_i)$ = `Q (e i)`. Indices are $0$-based (Cassels: $e_1, e_2, e_3$).

**Proves** (Cassels, *Rational Quadratic Forms*, Ch. 10, Theorem 3.1, Corollary 2, pp. 177–178)
* $C_0(V)$ has the $k$-basis (spanning set) $1, E_0, E_1, E_2$ with $E_0 = \vec e_1\vec e_2$, $E_1 = \vec e_2\vec e_0$,
  $E_2 = \vec e_0\vec e_1$ (`mem_evenOdd_zero_iff_ternary`); $E_i^2 = -f_jf_l$, $E_i' = -E_i$ and
  $E_iE_j + E_jE_i = 0$ for $i \ne j$ (`ternE_sq`, `reverse_ternE`, `ternE_anticomm`);
* for $u = u_0 + u_1E_0 + u_2E_1 + u_3E_2$:
  $uu' = u_0^2 + f_1f_2u_1^2 + f_2f_0u_2^2 + f_0f_1u_3^2 \in k$ (`mul_reverse_ternary`), a regular quaternary form whose
  determinant $(f_0f_1f_2)^2$ is a square (`normForm_nondegenerate`, `normForm_det`);
* Corollary 2: for $n = 3$, $uu' \in k$ for every $u \in C_0(V)$ (`mul_reverse_mem_of_even`), and $M_0(V)$ consists
  precisely of the $u \in C_0(V)$ with $uu' \ne 0$ (`mem_M0_iff_ternary`).

**Proof notes.** The span of the eight words $1, \vec e_i, E_i, \vec e_0\vec e_1\vec e_2$ is closed under left
multiplication by the $\vec e_i$, so it is $C(V)$; an even element has no odd component (apply the grade involution).
For the description of $M_0(V)$: if $uu' = c \ne 0$ then $u^{-1} = c^{-1}u'$ (Lemma 2.5), and $u\vec xu'$ is odd and
fixed by the involution; an odd element is $\vec v + \beta\,\vec e_0\vec e_1\vec e_2$ and the involution changes the
sign of the second term, so $u\vec xu' \in V$ (Cassels' footnote checks this for $u = \vec y\vec z$ only).
-/
import QuadFormsKB.Literature.Cassels.Ch10.SpinGroup
import QuadFormsKB.Siegel.UnimodularPadic

open Module CliffordAlgebra

namespace QuadFormsKB.Cassels

set_option linter.unusedSectionVars false

variable {k V : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] {Q : QuadraticForm k V}

section Basis

variable (Q) (e : Basis (Fin 3) k V)

/-- Cassels' elements $E_0 = \vec e_1\vec e_2$, $E_1 = \vec e_2\vec e_0$, $E_2 = \vec e_0\vec e_1$ of $C_0(V)$
($E_i = \vec e_{i+1}\vec e_{i+2}$, indices mod $3$). -/
noncomputable def ternE (i : Fin 3) : CliffordAlgebra Q := ι Q (e (i + 1)) * ι Q (e (i + 2))

/-- The element $u_0 + u_1E_0 + u_2E_1 + u_3E_2$ of $C_0(V)$. -/
noncomputable def ternElt (c : Fin 4 → k) : CliffordAlgebra Q :=
  algebraMap k _ (c 0) + c 1 • ternE Q e 0 + c 2 • ternE Q e 1 + c 3 • ternE Q e 2

/-- The quaternary norm form $g(\vec u) = u_0^2 + f_1f_2u_1^2 + f_2f_0u_2^2 + f_0f_1u_3^2$ (Cassels, p. 178). -/
noncomputable def normForm : QuadForm k 4 :=
  QuadForm.diag ![1, Q (e 1) * Q (e 2), Q (e 2) * Q (e 0), Q (e 0) * Q (e 1)]

/-- Spanning vectors of the even part. -/
noncomputable def tv0 : Fin 4 → CliffordAlgebra Q :=
  ![1, ternE Q e 0, ternE Q e 1, ternE Q e 2]

/-- Spanning vectors of the odd part. -/
noncomputable def tv1 : Fin 4 → CliffordAlgebra Q :=
  ![ι Q (e 0), ι Q (e 1), ι Q (e 2), ι Q (e 0) * (ι Q (e 1) * ι Q (e 2))]

/-- Even span. -/
noncomputable def tA0 : Submodule k (CliffordAlgebra Q) := Submodule.span k (Set.range (tv0 Q e))

/-- Odd span. -/
noncomputable def tA1 : Submodule k (CliffordAlgebra Q) := Submodule.span k (Set.range (tv1 Q e))

variable {Q e}
theorem t_ee (x y : V) : ι Q x * ι Q y ∈ evenOdd Q 0 := by
  have := SetLike.mul_mem_graded (ι_mem_evenOdd_one Q x) (ι_mem_evenOdd_one Q y)
  rwa [show (1 : ZMod 2) + 1 = 0 from by decide] at this

theorem t_ooo (x y z : V) : ι Q x * (ι Q y * ι Q z) ∈ evenOdd Q 1 := by
  have := SetLike.mul_mem_graded (ι_mem_evenOdd_one Q x) (t_ee y z)
  rwa [add_zero] at this

theorem t_disj {z : CliffordAlgebra Q} (h0 : z ∈ evenOdd Q 0) (h1 : z ∈ evenOdd Q 1) : z = 0 := by
  have := (evenOdd_isCompl Q).disjoint
  rw [Submodule.disjoint_def] at this
  exact this _ h0 h1

variable (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (e i) (e j) = 0)
include horth

theorem t_p10 : ι Q (e 1) * ι Q (e 0) = -(ι Q (e 0) * ι Q (e 1)) := ι_anticomm horth (by decide)
theorem t_p20 : ι Q (e 2) * ι Q (e 0) = -(ι Q (e 0) * ι Q (e 2)) := ι_anticomm horth (by decide)
theorem t_p21 : ι Q (e 2) * ι Q (e 1) = -(ι Q (e 1) * ι Q (e 2)) := ι_anticomm horth (by decide)

theorem t_t10 (x : CliffordAlgebra Q) : ι Q (e 1) * (ι Q (e 0) * x) = -(ι Q (e 0) * (ι Q (e 1) * x)) := by
  rw [← mul_assoc, t_p10 horth, neg_mul, mul_assoc]
theorem t_t20 (x : CliffordAlgebra Q) : ι Q (e 2) * (ι Q (e 0) * x) = -(ι Q (e 0) * (ι Q (e 2) * x)) := by
  rw [← mul_assoc, t_p20 horth, neg_mul, mul_assoc]
theorem t_t21 (x : CliffordAlgebra Q) : ι Q (e 2) * (ι Q (e 1) * x) = -(ι Q (e 1) * (ι Q (e 2) * x)) := by
  rw [← mul_assoc, t_p21 horth, neg_mul, mul_assoc]

theorem t_q (i : Fin 3) : ι Q (e i) * ι Q (e i) = Q (e i) • (1 : CliffordAlgebra Q) := by
  rw [ι_sq_scalar, Algebra.algebraMap_eq_smul_one]

theorem t_s (i : Fin 3) (x : CliffordAlgebra Q) : ι Q (e i) * (ι Q (e i) * x) = Q (e i) • x := by
  rw [← mul_assoc, t_q horth, smul_mul_assoc, one_mul]

theorem t_m1 : (1 : CliffordAlgebra Q) ∈ tA0 Q e := Submodule.subset_span ⟨0, rfl⟩
theorem t_mE0 : ι Q (e 1) * ι Q (e 2) ∈ tA0 Q e := Submodule.subset_span ⟨1, rfl⟩
theorem t_mE1 : ι Q (e 2) * ι Q (e 0) ∈ tA0 Q e := Submodule.subset_span ⟨2, rfl⟩
theorem t_mE2 : ι Q (e 0) * ι Q (e 1) ∈ tA0 Q e := Submodule.subset_span ⟨3, rfl⟩
theorem t_mE1' : ι Q (e 0) * ι Q (e 2) ∈ tA0 Q e := by
  have := Submodule.neg_mem _ (t_mE1 horth)
  rwa [t_p20 horth, neg_neg] at this
theorem t_n0 : ι Q (e 0) ∈ tA1 Q e := Submodule.subset_span ⟨0, rfl⟩
theorem t_n1 : ι Q (e 1) ∈ tA1 Q e := Submodule.subset_span ⟨1, rfl⟩
theorem t_n2 : ι Q (e 2) ∈ tA1 Q e := Submodule.subset_span ⟨2, rfl⟩
theorem t_nT : ι Q (e 0) * (ι Q (e 1) * ι Q (e 2)) ∈ tA1 Q e := Submodule.subset_span ⟨3, rfl⟩

theorem t_mulA0 (i : Fin 3) : ∀ w ∈ tA0 Q e, ι Q (e i) * w ∈ tA1 Q e := by
  intro w hw
  have : tA0 Q e ≤ (tA1 Q e).comap (LinearMap.mulLeft k (ι Q (e i))) := by
    rw [tA0, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    fin_cases i <;> fin_cases j <;>
    · simp only [tv0, ternE, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, mul_assoc, mul_one, Fin.isValue, Fin.reduceAdd, t_t10 horth, t_t20 horth, t_t21 horth,
        t_p10 horth, t_p20 horth, t_p21 horth, t_s horth, t_q horth, mul_smul_comm, mul_neg, smul_neg, neg_neg]
      all_goals
        repeat' (first | apply Submodule.neg_mem | apply Submodule.smul_mem)
        first | exact t_n0 horth | exact t_n1 horth | exact t_n2 horth | exact t_nT horth
  exact this hw

theorem t_mulA1 (i : Fin 3) : ∀ w ∈ tA1 Q e, ι Q (e i) * w ∈ tA0 Q e := by
  intro w hw
  have : tA1 Q e ≤ (tA0 Q e).comap (LinearMap.mulLeft k (ι Q (e i))) := by
    rw [tA1, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    fin_cases i <;> fin_cases j <;>
    · simp only [tv1, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, mul_assoc, mul_one, Fin.isValue, Fin.reduceAdd, t_t10 horth, t_t20 horth, t_t21 horth,
        t_p10 horth, t_p20 horth, t_p21 horth, t_s horth, t_q horth, mul_smul_comm, mul_neg, smul_neg, neg_neg]
      all_goals
        repeat' (first | apply Submodule.neg_mem | apply Submodule.smul_mem)
        first | exact t_m1 horth | exact t_mE0 horth | exact t_mE1' horth | exact t_mE2 horth
  exact this hw

theorem t_top (z : CliffordAlgebra Q) : z ∈ tA0 Q e ⊔ tA1 Q e := by
  have hb : ∀ l, bword Q e l ∈ tA0 Q e ⊔ tA1 Q e := by
    intro l
    induction l with
    | nil => exact Submodule.mem_sup_left (t_m1 horth)
    | cons i l ih =>
      rw [bword_cons]
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 ih
      rw [← hab, mul_add]
      exact Submodule.add_mem _ (Submodule.mem_sup_right (t_mulA0 horth i a ha))
        (Submodule.mem_sup_left (t_mulA1 horth i b hb))
  exact (Submodule.span_le.2 (by rintro _ ⟨l, rfl⟩; exact hb l)) (mem_span_bword Q e z)

theorem t_A0_even : tA0 Q e ≤ evenOdd Q 0 := by
  rw [tA0, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  fin_cases j
  · exact one_le_evenOdd_zero Q (Submodule.mem_one.2 ⟨1, by simp [tv0]⟩)
  all_goals exact t_ee _ _

theorem t_A1_odd : tA1 Q e ≤ evenOdd Q 1 := by
  rw [tA1, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  fin_cases j
  all_goals first | exact ι_mem_evenOdd_one Q _ | exact t_ooo _ _ _

theorem t_even_mem {u : CliffordAlgebra Q} (hu : u ∈ evenOdd Q 0) : u ∈ tA0 Q e := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (t_top horth u)
  have hb0 : b ∈ evenOdd Q 0 := by
    have := Submodule.sub_mem _ hu (t_A0_even horth ha)
    simpa using this
  rw [t_disj hb0 (t_A1_odd horth hb), add_zero]; exact ha

theorem t_odd_mem {u : CliffordAlgebra Q} (hu : u ∈ evenOdd Q 1) : u ∈ tA1 Q e := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (t_top horth u)
  have ha0 : a ∈ evenOdd Q 1 := by
    have := Submodule.sub_mem _ hu (t_A1_odd horth hb)
    simpa using this
  rw [t_disj (t_A0_even horth ha) ha0, zero_add]; exact hb

theorem tA0_iff {u : CliffordAlgebra Q} : u ∈ tA0 Q e ↔ ∃ c, u = ternElt Q e c := by
  rw [tA0, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    simp [Fin.sum_univ_four, tv0, ternElt, Algebra.algebraMap_eq_smul_one]
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    simp [Fin.sum_univ_four, tv0, ternElt, Algebra.algebraMap_eq_smul_one]

/-- $E_i^2 = -f_{i+1}f_{i+2}$ (Cassels, p. 177). -/
theorem ternE_sq (i : Fin 3) :
    ternE Q e i * ternE Q e i = algebraMap k _ (-(Q (e (i + 1)) * Q (e (i + 2)))) := by
  have h : ∀ a b : Fin 3, a ≠ b → ι Q (e a) * ι Q (e b) * (ι Q (e a) * ι Q (e b)) =
      algebraMap k _ (-(Q (e a) * Q (e b))) := by
    intro a b hab
    have h1 := ι_anticomm horth hab
    calc ι Q (e a) * ι Q (e b) * (ι Q (e a) * ι Q (e b))
        = ι Q (e a) * (ι Q (e b) * ι Q (e a)) * ι Q (e b) := by simp only [mul_assoc]
      _ = _ := by
        rw [h1, mul_neg, neg_mul, ← mul_assoc, ι_sq_scalar, mul_assoc, ι_sq_scalar,
          ← map_mul, ← map_neg]
  unfold ternE
  exact h _ _ (by fin_cases i <;> decide)

/-- $E_i' = -E_i$. -/
theorem reverse_ternE (i : Fin 3) : reverse (ternE Q e i) = -ternE Q e i := by
  unfold ternE
  rw [reverse.map_mul, reverse_ι, reverse_ι]
  exact ι_anticomm horth (by fin_cases i <;> decide)

/-- $E_iE_j + E_jE_i = 0$ for $i \ne j$ (Cassels, p. 177). -/
theorem ternE_anticomm {i j : Fin 3} (hij : i ≠ j) : ternE Q e i * ternE Q e j + ternE Q e j * ternE Q e i = 0 := by
  fin_cases i <;> fin_cases j <;> try exact absurd rfl hij
  all_goals
    simp only [ternE, mul_assoc]
    simp [t_t10 horth, t_t20 horth, t_t21 horth, t_p20 horth, t_p21 horth, t_s horth]

/-- **$C_0(V)$ for $n = 3$** (Cassels, p. 177): an element of $C(V)$ is even if and only if it is
$u_0 + u_1E_0 + u_2E_1 + u_3E_2$ for some $u_j \in k$. -/
@[kb "cassels1978" "Ch. 10, Thm. 3.1, Cor. 2, proof, p. 177 (basis 1, E₁, E₂, E₃ of C₀(V))"]
theorem mem_evenOdd_zero_iff_ternary (u : CliffordAlgebra Q) :
    u ∈ evenOdd Q 0 ↔ ∃ c : Fin 4 → k, u = ternElt Q e c := by
  constructor
  · intro hu
    exact (tA0_iff horth).1 (t_even_mem horth hu)
  · intro hu
    exact t_A0_even horth ((tA0_iff horth).2 hu)

/-- **$uu'$ for $n = 3$** (Cassels, p. 178): $uu' = u_0^2 + f_1f_2u_1^2 + f_2f_0u_2^2 + f_0f_1u_3^2$. -/
@[kb "cassels1978" "Ch. 10, Thm. 3.1, Cor. 2, proof, p. 178 (uu' = u₀² + F₁u₁² + F₂u₂² + F₃u₃²)"]
theorem mul_reverse_ternary (c : Fin 4 → k) :
    ternElt Q e c * reverse (ternElt Q e c) = algebraMap k _ ((normForm Q e).eval c) := by
  have hr1 : reverse (1 : CliffordAlgebra Q) = 1 := by
    simpa using reverse.commutes (Q := Q) (1 : k)
  have hr : reverse (ternElt Q e c) = c 0 • (1 : CliffordAlgebra Q) - c 1 • ternE Q e 0 - c 2 • ternE Q e 1 -
      c 3 • ternE Q e 2 := by
    simp only [ternElt, map_add, map_smul, reverse.commutes, reverse_ternE horth, Algebra.algebraMap_eq_smul_one,
      smul_neg, hr1]
    abel
  have s0 : ternE Q e 0 * ternE Q e 0 = (-(Q (e 1) * Q (e 2))) • (1 : CliffordAlgebra Q) := by
    rw [ternE_sq horth]; simp [Algebra.algebraMap_eq_smul_one]
  have s1 : ternE Q e 1 * ternE Q e 1 = (-(Q (e 2) * Q (e 0))) • (1 : CliffordAlgebra Q) := by
    rw [ternE_sq horth]; simp [Algebra.algebraMap_eq_smul_one]
  have s2 : ternE Q e 2 * ternE Q e 2 = (-(Q (e 0) * Q (e 1))) • (1 : CliffordAlgebra Q) := by
    rw [ternE_sq horth]; simp [Algebra.algebraMap_eq_smul_one]
  have a10 : ternE Q e 1 * ternE Q e 0 = -(ternE Q e 0 * ternE Q e 1) :=
    eq_neg_of_add_eq_zero_left (ternE_anticomm horth (i := 1) (j := 0) (by decide))
  have a20 : ternE Q e 2 * ternE Q e 0 = -(ternE Q e 0 * ternE Q e 2) :=
    eq_neg_of_add_eq_zero_left (ternE_anticomm horth (i := 2) (j := 0) (by decide))
  have a21 : ternE Q e 2 * ternE Q e 1 = -(ternE Q e 1 * ternE Q e 2) :=
    eq_neg_of_add_eq_zero_left (ternE_anticomm horth (i := 2) (j := 1) (by decide))
  rw [hr, normForm, QuadFormsKB.Siegel.Kneser.eval_diag, Fin.sum_univ_four, Algebra.algebraMap_eq_smul_one]
  simp only [ternElt, Algebra.algebraMap_eq_smul_one, add_mul, mul_add, sub_eq_add_neg, mul_neg, neg_mul,
    smul_mul_smul_comm, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, s0, s1, s2, a10, a20, a21, smul_neg,
    neg_neg, smul_smul]
  simp
  module

omit horth in
theorem t_hess : (normForm Q e).hessian = Matrix.diagonal (fun i => 2 * ![1, Q (e 1) * Q (e 2), Q (e 2) * Q (e 0),
      Q (e 0) * Q (e 1)] i) := by
  ext i j
  simp only [QuadForm.hessian, normForm, QuadForm.diag, Matrix.add_apply, Matrix.transpose_apply,
    Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp; ring
  · simp [h, Ne.symm h]

omit horth in
theorem t_det : (normForm Q e).hessian.det = 2 ^ 4 * (Q (e 0) * Q (e 1) * Q (e 2)) ^ 2 := by
  rw [t_hess, Matrix.det_diagonal, Fin.prod_univ_four]
  simp
  ring

omit horth in
/-- **The norm form is regular** (Cassels, p. 178) when the $f_i$ are nonzero. -/
@[kb "cassels1978" "Ch. 10, Thm. 3.1, Cor. 2, proof, p. 178 (a regular quaternary form)"]
theorem normForm_nondegenerate (hne : ∀ i, Q (e i) ≠ 0) : (normForm Q e).Nondegenerate := by
  unfold QuadForm.Nondegenerate
  rw [t_det]
  have h2 : (2 : k) ≠ 0 := Invertible.ne_zero (2 : k)
  have := hne 0; have := hne 1; have := hne 2
  positivity

omit horth in
/-- **The determinant of the norm form is a square** (Cassels, p. 178): its matrix is
$\operatorname{diag}(1, f_1f_2, f_2f_0, f_0f_1)$, of determinant $(f_0f_1f_2)^2$; the Hessian has determinant
$2^4(f_0f_1f_2)^2$. -/
@[kb "cassels1978" "Ch. 10, Thm. 3.1, Cor. 2, proof, p. 178 (the determinant is a perfect square)"]
theorem normForm_det : (normForm Q e).hessian.det = 2 ^ 4 * (Q (e 0) * Q (e 1) * Q (e 2)) ^ 2 := by
  exact t_det

omit horth in
theorem t_exists_basis (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : finrank k V = 3) :
    ∃ e : Basis (Fin 3) k V, (∀ i j, i ≠ j → QuadraticMap.polar Q (e i) (e j) = 0) ∧ ∀ i, Q (e i) ≠ 0 := by
  obtain ⟨e, ho, hne⟩ := exists_orthogonal_basis_aniso hQ
  refine ⟨e.reindex (finCongr hn), fun i j hij => ?_, fun i => ?_⟩
  · simp only [Basis.reindex_apply]
    exact ho _ _ (fun h => hij (by simpa using h))
  · simp only [Basis.reindex_apply]
    exact hne _

theorem t_revT : reverse (ι Q (e 0) * (ι Q (e 1) * ι Q (e 2))) = -(ι Q (e 0) * (ι Q (e 1) * ι Q (e 2))) := by
  simp [reverse.map_mul, mul_assoc, t_t10 horth, t_t20 horth, t_t21 horth, t_p10 horth,
    t_p20 horth, t_p21 horth]

theorem t_rev_even {u : CliffordAlgebra Q} (hu : u ∈ evenOdd Q 0) : reverse u ∈ evenOdd Q 0 := by
  obtain ⟨c, rfl⟩ := (mem_evenOdd_zero_iff_ternary horth _).1 hu
  have hr1 : reverse (1 : CliffordAlgebra Q) = 1 := by
    simpa using reverse.commutes (Q := Q) (1 : k)
  simp only [ternElt, map_add, map_smul, reverse.commutes, reverse_ternE horth, Algebra.algebraMap_eq_smul_one,
    hr1]
  repeat' (first | apply Submodule.add_mem | apply Submodule.neg_mem | apply Submodule.smul_mem)
  all_goals first | exact t_ee _ _ | exact one_le_evenOdd_zero Q (Submodule.mem_one.2 ⟨1, by simp⟩)

end Basis

/-- **Cassels, Ch. 10, Theorem 3.1, Corollary 2** (p. 177), first part: if $n = 3$ then $uu' \in k$ for every
$u \in C_0(V)$. -/
@[kb "cassels1978" "Ch. 10, Thm. 3.1, Cor. 2, p. 177 (uu' ∈ k for u ∈ C₀(V))"]
theorem mul_reverse_mem_of_even (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : finrank k V = 3)
    {u : CliffordAlgebra Q} (hu : u ∈ evenOdd Q 0) :
    ∃ c : k, u * reverse u = algebraMap k _ c := by
  obtain ⟨e, horth, -⟩ := t_exists_basis hQ hn
  obtain ⟨c, rfl⟩ := (mem_evenOdd_zero_iff_ternary horth _).1 hu
  exact ⟨_, mul_reverse_ternary horth c⟩

/-- **Cassels, Ch. 10, Theorem 3.1, Corollary 2** (p. 177), second part: if $n = 3$, $M_0(V)$ consists precisely of
the $u \in C_0(V)$ with $uu' \ne 0$ (such $u$ are automatically invertible). -/
@[kb "cassels1978" "Ch. 10, Thm. 3.1, Cor. 2, p. 177 (M₀(V) = {u ∈ C₀(V) : uu' ≠ 0})"]
theorem mem_M0_iff_ternary (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : finrank k V = 3)
    (u : CliffordAlgebra Q) :
    (∃ U ∈ M0 Q, (U : CliffordAlgebra Q) = u) ↔ u ∈ evenOdd Q 0 ∧ u * reverse u ≠ 0 := by
  constructor
  · rintro ⟨U, hU, rfl⟩
    refine ⟨hU.1, ?_⟩
    obtain ⟨c, hc, h⟩ := M0_mul_reverse hQ ⟨U, hU⟩
    rw [h]
    exact fun h0 => hc ((algebraMap k (CliffordAlgebra Q)).injective (by rw [h0, map_zero]))
  · rintro ⟨hu, hne0⟩
    obtain ⟨e, horth, -⟩ := t_exists_basis hQ hn
    obtain ⟨c, hc⟩ := mul_reverse_mem_of_even hQ hn hu
    have hc0 : c ≠ 0 := fun h0 => hne0 (by rw [hc, h0, map_zero])
    obtain ⟨-, h1, h2⟩ := inverse_of_mul_reverse Q hc0 hc
    refine ⟨⟨u, c⁻¹ • reverse u, h1, h2⟩, ⟨hu, fun x => ?_⟩, rfl⟩
    have hru := t_rev_even horth hu
    have hw : u * ι Q x * reverse u ∈ evenOdd Q 1 := by
      have := SetLike.mul_mem_graded (SetLike.mul_mem_graded hu (ι_mem_evenOdd_one Q x)) hru
      rwa [zero_add, add_zero] at this
    have hrev : reverse (u * ι Q x * reverse u) = u * ι Q x * reverse u := by
      rw [reverse.map_mul, reverse.map_mul, reverse_reverse, reverse_ι, mul_assoc]
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
    refine ⟨c⁻¹ • (d 0 • e 0 + d 1 • e 1 + d 2 • e 2), ?_⟩
    show _ = u * ι Q x * (c⁻¹ • reverse u)
    rw [mul_smul_comm, ← hd, h0, add_zero]
    simp only [map_smul, map_add]

end QuadFormsKB.Cassels
