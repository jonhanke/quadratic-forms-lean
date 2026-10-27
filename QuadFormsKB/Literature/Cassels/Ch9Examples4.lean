/-
# Cassels, Chapter 9: Example 15 (i), orders of proper automorphs of positive definite ternary forms

**Layer:** forms over $\mathbb Q$ (`QuadForm ℚ 3`), integral forms `QuadForm ℤ n` and their automorph groups
`Siegel.Aut` (`Ch9Sec1.lean`, `Siegel/Genus.lean`).

**Proves**
* Example 15 (i), p. 165 (`orderOf_mem_of_proper_automorph`): if $f(x, y, z) \in \mathbb Q[x, y, z]$ is positive definite
  and $T \in M_3(\mathbb Z)$ has $\det T = 1$ and $f(T\mathbf x) = f(\mathbf x)$, then $T$ has order $1, 2, 3, 4$ or $6$.
  Unconditional (no assumed inputs).

*Proof (purely algebraic, no eigenvalues; Cassels' hint refers to Ch. 2, Ex. 9):* clear denominators to get an integral
positive definite form with the same automorphs, so $T$ lies in a finite group and $T^k = 1$; the trace of $T^{-1}$ equals
that of $T$ (since $T^{\mathsf T} H T = H$), so Cayley–Hamilton gives $(T - 1)(T^2 - tT + 1) = 0$ with $t = \operatorname{tr} T - 1$;
the traces of the powers satisfy $u_{j+2} = t u_{j+1} - u_j$, which forces $|t| \le 2$; the five cases $t \in \{-2, \dots, 2\}$
give $T^m = 1$ for $m = 2, 3, 4, 6, 1$ respectively (the extreme cases by a unipotent-of-finite-order argument).
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec1
import QuadFormsKB.Lattices.Finite

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

variable {n : ℕ}

/-- **Binomial formula for a cube-zero perturbation of $1$.** If $N^3 = 0$ then for every $m \\ge 0$ there is an
integer $c$ (namely $\\binom m2$) with $(1 + N)^m = 1 + mN + cN^2$. -/
theorem unipotent_pow_formula {N : Matrix (Fin n) (Fin n) ℤ} (h3 : N ^ 3 = 0) (m : ℕ) :
    ∃ c : ℤ, (1 + N) ^ m = 1 + (m : ℤ) • N + c • N ^ 2 := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨(m : ℤ) + c, ?_⟩
    have e1 : N * N = N ^ 2 := (sq N).symm
    have e2 : N ^ 2 * N = 0 := by rw [← pow_succ]; exact h3
    rw [pow_succ, hc]
    simp only [add_mul, mul_add, smul_mul_assoc, one_mul, mul_one, e1, e2, smul_zero,
      add_zero]
    push_cast
    module

/-- **A unipotent integer matrix of finite order is trivial.** Hypotheses: `h3` ($N^3 = 0$), `hk` ($k \\ge 1$),
`h` ($(1 + N)^k = 1$); conclusion $N = 0$. (Multiply $kN + cN^2 = 0$ by $N$ to get $kN^2 = 0$, then use that
$\\mathbb Z$ is torsion free, entrywise.) -/
theorem eq_zero_of_nilpotent_pow_eq_one {N : Matrix (Fin n) (Fin n) ℤ} (h3 : N ^ 3 = 0) {k : ℕ}
    (hk : 0 < k) (h : (1 + N) ^ k = 1) : N = 0 := by
  obtain ⟨c, hc⟩ := unipotent_pow_formula h3 k
  rw [h] at hc
  have h1 : (k : ℤ) • N + c • N ^ 2 = 0 := by
    have : (1 : Matrix (Fin n) (Fin n) ℤ) + ((k : ℤ) • N + c • N ^ 2) = 1 + 0 := by
      rw [add_zero, ← add_assoc]; exact hc.symm
    exact add_left_cancel this
  have h2 : (k : ℤ) • N ^ 2 = 0 := by
    have := congrArg (· * N) h1
    simp only [add_mul, smul_mul_assoc, zero_mul] at this
    have e : N ^ 2 * N = 0 := by rw [← pow_succ]; exact h3
    rw [e, smul_zero, add_zero, ← sq] at this
    exact this
  have hN2 : N ^ 2 = 0 := by
    ext i j
    have := congrFun (congrFun h2 i) j
    simp at this
    exact this.resolve_left hk.ne'
  rw [hN2, smul_zero, add_zero] at h1
  ext i j
  have := congrFun (congrFun h1 i) j
  simp at this
  exact this.resolve_left hk.ne'

/-- **Cayley–Hamilton for $3 \\times 3$ matrices**, in the form $T^3 - (\\operatorname{tr} T) T^2
+ (\\operatorname{tr}\\operatorname{adj} T) T - (\\det T) \\cdot 1 = 0$, over any $\\mathbb Z$-matrix (checked entrywise). -/
theorem cayley3 (T : Matrix (Fin 3) (Fin 3) ℤ) :
    T ^ 3 - T.trace • T ^ 2 + (adjugate T).trace • T - T.det • (1 : Matrix (Fin 3) (Fin 3) ℤ) = 0 := by
  rw [Matrix.eta_fin_three T]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [pow_succ, pow_zero, one_mul, Matrix.mul_apply, Fin.sum_univ_three,
    trace_fin_three, det_fin_three, adjugate_fin_three, Matrix.one_apply, Matrix.sub_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply]
  all_goals (simp; try ring_nf)

/-- **Newton's identity for $3 \\times 3$ matrices:** $\\operatorname{tr}(T^2) = (\\operatorname{tr} T)^2
- 2 \\operatorname{tr}(\\operatorname{adj} T)$. -/
theorem trace_sq3 (T : Matrix (Fin 3) (Fin 3) ℤ) :
    (T ^ 2).trace = T.trace ^ 2 - 2 * (adjugate T).trace := by
  rw [Matrix.eta_fin_three T]
  simp only [pow_succ, pow_zero, one_mul, Matrix.mul_apply, Fin.sum_univ_three, trace_fin_three,
    adjugate_fin_three]
  simp
  ring_nf

/-- **A bounded recurrence forces $|t| \\le 2$.** Hypotheses: `h0`, `h1` ($u_0 = 2$, $u_1 = t$), `hrec`
($u_{j+2} = t u_{j+1} - u_j$), `hk` ($k \\ge 1$), `hk2` ($u_k = 2$). If $|t| \\ge 3$ then $|u_{j+1}| \\ge |u_j| + 1$, so
$|u_k| \\ge 2 + k$, contradicting $u_k = 2$. -/
theorem abs_le_two_of_seq (u : ℕ → ℤ) (t : ℤ) (h0 : u 0 = 2) (h1 : u 1 = t)
    (hrec : ∀ j, u (j + 2) = t * u (j + 1) - u j) {k : ℕ} (hk : 0 < k) (hk2 : u k = 2) :
    |t| ≤ 2 := by
  by_contra hlt
  push Not at hlt
  have step : ∀ j, |u j| + 1 ≤ |u (j + 1)| := by
    intro j
    induction j with
    | zero => rw [h0, h1]; norm_num; omega
    | succ j ih =>
      rw [hrec j]
      have h3 : |t * u (j + 1)| = |t| * |u (j + 1)| := abs_mul _ _
      have h4 := abs_sub_abs_le_abs_sub (t * u (j + 1)) (u j)
      have h5 : 0 ≤ |u j| := abs_nonneg _
      nlinarith [abs_nonneg (u (j + 1))]
  have grow : ∀ j : ℕ, 2 + (j : ℤ) ≤ |u j| := by
    intro j
    induction j with
    | zero => simp [h0]
    | succ j ih => have := step j; push_cast; linarith
  have := grow k
  rw [hk2] at this
  have : (0 : ℤ) < k := by exact_mod_cast hk
  norm_num at *
  omega

/-- **Core algebra of Example 15 (i).** For $T \\in M_3(\\mathbb Z)$ with `hdet` ($\\det T = 1$), `htr`
($\\operatorname{tr}\\operatorname{adj} T = \\operatorname{tr} T$) and `hTk` ($T^k = 1$, $k \\ge 1$ by `hk`), some $T^m = 1$
with $m \\in \\{1, 2, 3, 4, 6\\}$. -/
theorem exists_pow_eq_one_of_trace {T : Matrix (Fin 3) (Fin 3) ℤ} (hdet : T.det = 1)
    (htr : (adjugate T).trace = T.trace) {k : ℕ} (hk : 0 < k) (hTk : T ^ k = 1) :
    ∃ m ∈ ({1, 2, 3, 4, 6} : Finset ℕ), T ^ m = 1 := by
  obtain ⟨t, ht⟩ : ∃ t : ℤ, t = T.trace - 1 := ⟨_, rfl⟩
  have ch : T ^ 3 - T.trace • T ^ 2 + T.trace • T - 1 = 0 := by
    have := cayley3 T
    rw [htr, hdet, one_smul] at this
    exact this
  have hP : (T - 1) * (T ^ 2 - t • T + 1) = 0 := by
    have e : (T - 1) * (T ^ 2 - t • T + 1) = T ^ 3 - T.trace • T ^ 2 + T.trace • T - 1 := by
      rw [ht, sub_smul, one_smul]
      simp only [pow_succ, pow_zero, one_mul, mul_one, mul_sub, mul_add, sub_mul,
        mul_smul_comm, smul_sub, mul_assoc]
      module
    rw [e, ch]
  set P : Matrix (Fin 3) (Fin 3) ℤ := T ^ 2 - t • T + 1 with hPdef
  have hTP : T * P = P := by
    have := hP
    rw [sub_mul, one_mul, sub_eq_zero] at this
    exact this
  have hTjP : ∀ j : ℕ, T ^ j * P = P := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', mul_assoc, ih, hTP]
  have htrP : P.trace = 2 - t := by
    simp only [hPdef, trace_add, trace_sub, trace_smul, trace_one, trace_sq3, htr, ht]
    simp
    ring
  have hrec : ∀ j : ℕ, ((T ^ (j + 2)).trace - 1) = t * ((T ^ (j + 1)).trace - 1) - ((T ^ j).trace - 1) := by
    intro j
    have e : T ^ j * P = T ^ (j + 2) - t • T ^ (j + 1) + T ^ j := by
      rw [hPdef, pow_add, pow_succ]
      noncomm_ring
    have h := congrArg Matrix.trace (hTjP j)
    rw [e] at h
    simp only [trace_add, trace_sub, trace_smul, htrP, smul_eq_mul] at h
    linear_combination h
  have habs := abs_le_two_of_seq (fun j => (T ^ j).trace - 1) t (by simp) (by simp [ht]) hrec hk
    (by simp [hTk])
  rw [abs_le] at habs
  have hcases : t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2 := by omega
  rcases hcases with h | h | h | h | h
  · -- t = -2: N = T² - 1 has N² = 0
    subst h
    have hN2 : (T ^ 2 - 1) ^ 2 = 0 := by
      have e : (T ^ 2 - 1) ^ 2 = (T - 1) * ((T - 1) * (T ^ 2 - (-2 : ℤ) • T + 1)) := by
        noncomm_ring
      rw [e, hP, mul_zero]
    have hN3 : (T ^ 2 - 1) ^ 3 = 0 := by rw [pow_succ, hN2, zero_mul]
    have := eq_zero_of_nilpotent_pow_eq_one hN3 hk (by
      rw [add_sub_cancel, ← pow_mul, mul_comm, pow_mul, hTk, one_pow])
    exact ⟨2, by simp, sub_eq_zero.mp this⟩
  · subst h
    refine ⟨3, by simp, ?_⟩
    have e : T ^ 3 - 1 = (T - 1) * (T ^ 2 - (-1 : ℤ) • T + 1) := by noncomm_ring
    rw [hP] at e
    exact sub_eq_zero.mp e
  · subst h
    refine ⟨4, by simp, ?_⟩
    have e : T ^ 4 - 1 = (T + 1) * ((T - 1) * (T ^ 2 - (0 : ℤ) • T + 1)) := by
      rw [zero_smul]; noncomm_ring
    rw [hP, mul_zero] at e
    exact sub_eq_zero.mp e
  · subst h
    refine ⟨6, by simp, ?_⟩
    have e : T ^ 6 - 1 = ((T + 1) * (T ^ 2 + T + 1)) * ((T - 1) * (T ^ 2 - (1 : ℤ) • T + 1)) := by
      noncomm_ring
    rw [hP, mul_zero] at e
    exact sub_eq_zero.mp e
  · subst h
    have hN3 : (T - 1) ^ 3 = 0 := by
      have e : (T - 1) ^ 3 = (T - 1) * (T ^ 2 - (2 : ℤ) • T + 1) := by noncomm_ring
      rw [e, hP]
    have := eq_zero_of_nilpotent_pow_eq_one hN3 hk (by rw [add_sub_cancel]; exact hTk)
    exact ⟨1, by simp, by rw [pow_one]; exact sub_eq_zero.mp this⟩

/-- **Positive definite over $\mathbb Q$:** $f(\mathbf x) > 0$ for every nonzero $\mathbf x \in \mathbb Q^n$. -/
def RatPosDef (f : QuadForm ℚ n) : Prop := ∀ x : Fin n → ℚ, x ≠ 0 → 0 < f.eval x

/-- `RatPosDef` is the library's totally positive definiteness `Lattices.IsTotallyPosDef` over the number field
$\mathbb Q$ (whose only embedding into $\mathbb C$ is the inclusion). -/
theorem ratPosDef_iff_isTotallyPosDef (f : QuadForm ℚ n) : RatPosDef f ↔ Lattices.IsTotallyPosDef f := by
  have key : ∀ a : ℚ, Lattices.IsTotallyPos a ↔ 0 < a := fun a => by
    constructor
    · intro h
      have := h (Algebra.ofId ℚ ℂ)
      rw [Algebra.ofId_apply, show algebraMap ℚ ℂ a = ((a : ℝ) : ℂ) by simp] at this
      exact_mod_cast Complex.zero_lt_real.1 this
    · intro h σ
      rw [show σ a = algebraMap ℚ ℂ a from σ.commutes a, show algebraMap ℚ ℂ a = ((a : ℝ) : ℂ) by simp]
      exact Complex.zero_lt_real.2 (by exact_mod_cast h)
  simp only [RatPosDef, Lattices.IsTotallyPosDef, key]

/-- **Clearing denominators.** For a rational form $f$ there is an integer $N \ge 1$ and an integral form $Q$ with
$Q(\mathbf x) = N f(\mathbf x)$ for all $\mathbf x \in \mathbb Q^n$ ($N$ = the product of the denominators of the
coefficients of $f$). -/
theorem exists_intForm_smul (f : QuadForm ℚ n) :
    ∃ N : ℕ, 0 < N ∧ ∃ Q : QuadForm ℤ n, ∀ x : Fin n → ℚ, Q.evalIn ℚ x = N * f.eval x := by
  set N : ℕ := ∏ p : Fin n × Fin n, (f.coeff p.1 p.2).den with hNdef
  have hNpos : 0 < N := Finset.prod_pos fun p _ => (f.coeff p.1 p.2).den_pos
  have hdvd : ∀ i j, (f.coeff i j).den ∣ N := fun i j =>
    Finset.dvd_prod_of_mem (fun p : Fin n × Fin n => (f.coeff p.1 p.2).den) (Finset.mem_univ (i, j))
  let Q : QuadForm ℤ n :=
    ⟨Matrix.of fun i j => (f.coeff i j).num * ((N / (f.coeff i j).den : ℕ) : ℤ), by
      intro i j hij
      have h0 : f.coeff i j = 0 := f.upper hij
      simp [h0]⟩
  have key : ∀ i j, ((Q.coeff i j : ℤ) : ℚ) = N * f.coeff i j := by
    intro i j
    have hd : ((f.coeff i j).den : ℚ) ≠ 0 := by exact_mod_cast (f.coeff i j).den_nz
    simp only [Q, Matrix.of_apply, Int.cast_mul, Int.cast_natCast]
    rw [Nat.cast_div (hdvd i j) hd]
    conv_rhs => rw [← Rat.num_div_den (f.coeff i j)]
    field_simp
  refine ⟨N, hNpos, Q, fun x => ?_⟩
  simp only [QuadForm.eval, QuadForm.evalIn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · have := key i j
    simp only [eq_intCast, Algebra.algebraMap_self, RingHom.id_apply] at this ⊢
    rw [this]
    ring
  · simp

/-- **Trace of the inverse of an automorph.** If $Q$ is a nondegenerate integral form and $T \in M_3(\mathbb Z)$
satisfies $\det T = 1$ and $T^{\mathsf T} H T = H$ ($H$ the Hessian of $Q$), then $\operatorname{tr}(\operatorname{adj} T)
= \operatorname{tr}(T^{-1}) = \operatorname{tr}(T)$. -/
theorem trace_adjugate_eq {H T : Matrix (Fin 3) (Fin 3) ℤ} (hH : H.det ≠ 0) (hdet : T.det = 1)
    (hT : Tᵀ * H * T = H) : (adjugate T).trace = T.trace := by
  set φ := Int.castRingHom ℚ
  set Hq : Matrix (Fin 3) (Fin 3) ℚ := H.map φ
  set Tq : Matrix (Fin 3) (Fin 3) ℚ := T.map φ
  have hHq : IsUnit Hq.det := by
    have : Hq.det = (H.det : ℚ) := (RingHom.map_det φ H).symm
    rw [isUnit_iff_ne_zero, this]
    exact_mod_cast hH
  have hTq : Tq.det = 1 := by
    have : Tq.det = (T.det : ℚ) := (RingHom.map_det φ T).symm
    rw [this, hdet]; simp
  have hT' : Tqᵀ * Hq * Tq = Hq := by
    have := congrArg (fun M => M.map φ) hT
    simpa [Hq, Tq, Matrix.map_mul, Matrix.transpose_map] using this
  have hinv : Tq⁻¹ = Hq⁻¹ * Tqᵀ * Hq := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Tqᵀ, hT', Matrix.nonsing_inv_mul _ hHq]
  have hadj : Tq⁻¹ = (adjugate T).map φ := by
    rw [Matrix.inv_def, hTq, Ring.inverse_one, one_smul]
    exact (RingHom.map_adjugate φ T).symm
  have htr : (Tq⁻¹).trace = Tq.trace := by
    rw [hinv, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hHq, Matrix.one_mul,
      Matrix.trace_transpose]
  rw [hadj] at htr
  have : ((adjugate T).trace : ℚ) = (T.trace : ℚ) := by
    simpa [Matrix.trace, Tq, φ] using htr
  exact_mod_cast this

/-- **Cassels, Ch. 9, Example 15 (i)** (p. 165): *let $f(x, y, z) \in \mathbb Q[x, y, z]$ be a positive definite
quadratic form. Show that a proper integral automorph $T$ has order $1, 2, 3, 4$ or $6$.*

Hypotheses: `hf` ($f$ is positive definite over $\mathbb Q$), `hdet` ($T$ is an integral matrix with $\det T = 1$,
i.e. proper), `haut` ($T$ is an automorph, $f(T\mathbf x) = f(\mathbf x)$ for all $\mathbf x \in \mathbb Q^3$).
The order is that of $T$ in the monoid $M_3(\mathbb Z)$ (it is positive since $T$ has finite order).
Unconditional (no assumed inputs).

*Proof (no eigenvalues).* Clear denominators ($Nf = Q$ integral, `exists_intForm_smul`); $T$ lies in the finite group
$\mathrm{Aut}(Q)$ (`IntQF.PosDef.finite_aut`), so $T^k = 1$ for some $k \ge 1$. From $T^{\mathsf T}HT = H$ one gets
$\operatorname{tr}(T^{-1}) = \operatorname{tr} T =: s$ (`trace_adjugate_eq`), and Cayley–Hamilton (`cayley3`) reads
$(T - 1)(T^2 - tT + 1) = 0$ with $t = s - 1$. The integers $u_j = \operatorname{tr}(T^j) - 1$ satisfy
$u_{j+2} = t u_{j+1} - u_j$, $u_0 = 2$, $u_1 = t$, and $u_k = 2$ forces $|t| \le 2` (`abs_le_two_of_seq`).
The five values of $t$ give $T^3 = 1$ ($t = -1$), $T^4 = 1$ ($t = 0$), $T^6 = 1$ ($t = 1$), and $T = 1$ ($t = 2$),
$T^2 = 1$ ($t = -2$) via the nilpotent lemma `eq_zero_of_nilpotent_pow_eq_one`
(`exists_pow_eq_one_of_trace`).

*Source note:* Cassels' hint refers to Ch. 2, Ex. 9. -/
@[kb "cassels1978" "Ch. 9, Ex. 15 (i), p. 165"]
theorem orderOf_mem_of_proper_automorph {f : QuadForm ℚ 3} (hf : RatPosDef f)
    {T : Matrix (Fin 3) (Fin 3) ℤ} (hdet : T.det = 1)
    (haut : ∀ x : Fin 3 → ℚ, f.eval ((T.map (Int.castRingHom ℚ)) *ᵥ x) = f.eval x) :
    orderOf T ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  obtain ⟨N, hN, Q, hQ⟩ := exists_intForm_smul f
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hQpos : IntQF.PosDef Q := by
    intro x hx
    have hx' : (fun i => (x i : ℚ)) ≠ 0 := by
      intro h
      apply hx
      funext i
      have := congrFun h i
      simpa using this
    have h1 := hQ (fun i => (x i : ℚ))
    rw [Siegel.evalIn_intCast] at h1
    have : (0 : ℚ) < (Q.eval x : ℚ) := by rw [h1]; exact mul_pos hNq (hf _ hx')
    exact_mod_cast this
  have hTQ : ∀ x : Fin 3 → ℤ, Q.eval (T *ᵥ x) = Q.eval x := by
    intro x
    have e : (fun i => ((T *ᵥ x) i : ℚ)) = (T.map (Int.castRingHom ℚ)) *ᵥ (fun i => (x i : ℚ)) := by
      funext i
      simp [Matrix.mulVec, dotProduct]
    have h1 := hQ (fun i => ((T *ᵥ x) i : ℚ))
    have h2 := hQ (fun i => (x i : ℚ))
    rw [Siegel.evalIn_intCast] at h1 h2
    rw [e, haut, ← h2] at h1
    exact_mod_cast h1
  have hunit : IsUnit T.det := by rw [hdet]; exact isUnit_one
  let g : GL (Fin 3) ℤ := Matrix.nonsingInvUnit T hunit
  have hg : g ∈ Siegel.Aut Q := hTQ
  have := hQpos.finite_aut
  obtain ⟨k, hk, hgk⟩ := (isOfFinOrder_of_finite (⟨g, hg⟩ : Siegel.Aut Q)).exists_pow_eq_one
  have hTk : T ^ k = 1 := by
    have := congrArg (fun z : Siegel.Aut Q => ((z : GL (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ)) hgk
    simpa [g, Matrix.nonsingInvUnit] using this
  have htr : (adjugate T).trace = T.trace :=
    trace_adjugate_eq hQpos.nondegenerate hdet ((eval_mulVec_eq_iff_hessian Q Q T).mp hTQ)
  obtain ⟨m, hm, hTm⟩ := exists_pow_eq_one_of_trace hdet htr hk hTk
  have hdvd : orderOf T ∣ m := orderOf_dvd_of_pow_eq_one hTm
  have hall : ∀ m ∈ ({1, 2, 3, 4, 6} : Finset ℕ), ∀ d ∈ Nat.divisors m,
      d ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by decide
  exact hall m hm _ (Nat.mem_divisors.mpr ⟨hdvd, by simp at hm; omega⟩)

end QuadFormsKB.Siegel
