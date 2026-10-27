import QuadFormsKB.Binary.SiegelBinary

/-!
# The Euler product of $L(s,\chi)$ at $s = 1$ in the natural order

For a **nontrivial** Dirichlet character $\chi$ modulo $q \ge 1$ (complex values),
$$\prod_{p < N}\Big(1 - \frac{\chi(p)}{p}\Big) \longrightarrow L(1,\chi)^{-1} \qquad (N \to \infty),$$
the product over the primes in their natural order (`EulerOne.tendsto_prod_primesBelow`), with $L(1,\chi)$ the value
at $1$ of Mathlib's entire `DirichletCharacter.LFunction`. For the Kronecker character $\chi_D$ of a fundamental
discriminant $D$ (either sign) this **proves** the named input `EulerProductAtOne D` (`eulerProductAtOne`), so the
natural-order Siegel formula for binary forms becomes unconditional (`siegelFormula_binary_natural'`).

**Route** (elementary, no prime number theorem; Mathlib supplies $L(1,\chi) \ne 0$, the Euler product for
$\operatorname{Re}s > 1$, the entire continuation of $L$, and Chebyshev's bound $\psi(x) \le (\log 4 + 4)x$):
1. **Abel's inequality** (`EulerOne.norm_sum_Ico_mul_le`): if $|\sum_{k<n}a_k| \le B$ for all $n$ and $w$ is
   nonincreasing and $\ge 0$ on $[M, N]$, then $|\sum_{M \le n < N}a_nw_n| \le 2Bw_M$.
2. **Bounded character sums** (`EulerOne.norm_sum_range_le`): $|\sum_{k<n}\chi(k)| \le q$.
3. **$L(1,\chi) = \sum_n\chi(n)/n$ with rate** (`EulerOne.norm_lpart_one_sub_LFunction_le`):
   $|\sum_{n<M}\chi(n)/n - L(1,\chi)| \le 4q/(M+1)$. The partial sums of $\sum\chi(n)n^{-s}$ are uniformly Cauchy on
   $s \in [1,2]$ (1, 2), so their limit is continuous there; it is $L(s,\chi)$ for $s > 1$, hence $L(1,\chi)$ at $s = 1$
   (an Abelian argument, `EulerOne.exists_continuousOn_limit`, `EulerOne.eq_at_one_of_continuousOn`).
4. **Twisted Chebyshev sums are bounded** (`EulerOne.norm_sum_fA_le`):
   $\sum_{n\le N}\chi(n)\log n/n = \sum_{d \le N}\frac{\Lambda(d)\chi(d)}{d}\sum_{m \le N/d}\frac{\chi(m)}{m}$
   (from $\log = \Lambda * 1$), the inner sum is $L(1,\chi) + O(qd/N)$ by 3, the left side is $O(q)$ by 1, and
   $\sum_{d\le N}\Lambda(d) = \psi(N) = O(N)$; dividing by $L(1,\chi) \ne 0$ gives
   $|\sum_{n\le N}\Lambda(n)\chi(n)/n| \le (26q+3)/|L(1,\chi)|$.
5. **Mertens-type bound for primes** (`EulerOne.norm_sum_aP_le`): $|\sum_{p<N}\chi(p)\log p/p| \le C_\chi$
   (the prime powers contribute a convergent series).
6. **Uniform convergence of the log-product on $[1,2]$** (`EulerOne.norm_Gpart_sub_le`):
   $\log(1 - \chi(p)p^{-s}) = -\chi(p)p^{-s} + O(p^{-2})$, and $\chi(p)p^{-s} = \frac{\chi(p)\log p}{p}\cdot
   \frac{p^{1-s}}{\log p}$ with the second factor nonincreasing in $p$, so 1 and 5 give the tail bound
   $2C_\chi/\log M + \sum_{k \ge M}k^{-2}$, uniformly in $s \ge 1$.
7. **Identification** (`EulerOne.tendsto_prod_primesBelow`): the limit $G(s)$ of the log-partial-sums is continuous on
   $[1,2]$ and $e^{G(s)} = L(s,\chi)^{-1}$ for $s > 1$ (Mathlib's Euler product, natural order:
   `DirichletCharacter.LSeries_eulerProduct`); continuity of $L$ at $1$ and $L(1,\chi) \ne 0$ give
   $e^{G(1)} = L(1,\chi)^{-1}$.

Indices: sums over `Finset.range N` are over $0 \le n < N$ (0-based); the $n = 0$ terms vanish.

Sources: Montgomery–Vaughan, *Multiplicative Number Theory I*, §4.3 (Mertens-type estimates for characters)
[unverified locator]; Davenport, *Multiplicative Number Theory*, Ch. 4 and Ch. 6–7 (Dirichlet's theorem; $L(1,\chi)$)
[unverified locator]; Apostol, *Introduction to Analytic Number Theory*, Thm. 4.2 (Abel's identity), Ch. 6–7
($\sum\chi(n)/n$; $\sum_{n \le x}\chi(n)\Lambda(n)/n = O(1)$ for $L(1,\chi) \ne 0$) [unverified locators].
-/

set_option linter.unusedSectionVars false

open Filter Topology Finset

namespace QuadFormsKB.Binary.EulerOne

/-- **Summation by parts on $[M, N)$.** With $A_n = \sum_{k<n}a_k$:
$\sum_{M\le n<N}a_nw_n = (A_N - A_M)w_N + \sum_{M \le n < N}(A_{n+1} - A_M)(w_n - w_{n+1})$. Source: Apostol, Thm. 4.2
(discrete form) [unverified locator]. -/
theorem sum_Ico_mul_eq (a : ℕ → ℂ) (w : ℕ → ℝ) (M : ℕ) : ∀ N, M ≤ N →
    ∑ n ∈ Ico M N, a n * w n =
      (∑ k ∈ range N, a k - ∑ k ∈ range M, a k) * w N +
      ∑ n ∈ Ico M N, (∑ k ∈ range (n + 1), a k - ∑ k ∈ range M, a k) * ((w n : ℂ) - w (n + 1)) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hMN ih =>
    rw [sum_Ico_succ_top hMN, sum_Ico_succ_top hMN, ih, sum_range_succ]
    ring

/-- **Abel's inequality.** If $|\sum_{k<n}a_k| \le B$ for every $n$, and the real weights satisfy
$w_{n+1} \le w_n$ for $M \le n < N$ and $w_N \ge 0$, then $\left|\sum_{M \le n < N}a_nw_n\right| \le 2Bw_M$.
Source: Montgomery–Vaughan §4.3 / Apostol Thm. 4.2 (partial summation) [unverified locators]. -/
@[kb "apostol1976" "Thm. 4.2 (Abel's identity), discrete form [unverified locator]"]
theorem norm_sum_Ico_mul_le (a : ℕ → ℂ) (w : ℕ → ℝ) {B : ℝ}
    (hA : ∀ n, ‖∑ k ∈ range n, a k‖ ≤ B) {M N : ℕ} (hMN : M ≤ N)
    (hw : ∀ n, M ≤ n → n < N → w (n + 1) ≤ w n) (hw0 : 0 ≤ w N) :
    ‖∑ n ∈ Ico M N, a n * w n‖ ≤ 2 * B * w M := by
  have hd : ∀ n m, ‖∑ k ∈ range n, a k - ∑ k ∈ range m, a k‖ ≤ 2 * B := fun n m =>
    (norm_sub_le _ _).trans (by linarith [hA n, hA m])
  have hR : ∀ N', M ≤ N' → N' ≤ N →
      ‖∑ n ∈ Ico M N', (∑ k ∈ range (n + 1), a k - ∑ k ∈ range M, a k) * ((w n : ℂ) - w (n + 1))‖
        ≤ 2 * B * (w M - w N') := by
    intro N' hN'
    induction N', hN' using Nat.le_induction with
    | base => simp
    | succ N' hMN' ih =>
      intro hle
      rw [sum_Ico_succ_top hMN']
      have h1 := ih (by omega)
      have hwN : w (N' + 1) ≤ w N' := hw N' hMN' (by omega)
      calc _ ≤ _ + _ := norm_add_le _ _
        _ ≤ 2 * B * (w M - w N') + 2 * B * (w N' - w (N' + 1)) := by
          gcongr
          rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
          exact mul_le_mul (hd (N' + 1) M) le_rfl (by linarith) ((norm_nonneg _).trans (hd (N' + 1) M))
        _ = _ := by ring
  rw [sum_Ico_mul_eq a w M N hMN]
  calc _ ≤ _ + _ := norm_add_le _ _
    _ ≤ 2 * B * w N + 2 * B * (w M - w N) := by
      gcongr
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0]
        exact mul_le_mul_of_nonneg_right (hd _ _) hw0
      · exact hR N hMN le_rfl
    _ = _ := by ring

/-- **Uniformly Cauchy sequences have a continuous limit.** If $F_N$ is continuous on $S$ and
$|F_N(s) - F_M(s)| \le b_M$ for all $M \le N$, $s \in S$, with $b_M \to 0$, then $F_N \to G$ pointwise on $S$ for some
$G$ continuous on $S$, and $|G(s) - F_M(s)| \le b_M$. -/
theorem exists_continuousOn_limit {F : ℕ → ℝ → ℂ} {S : Set ℝ} (hc : ∀ N, ContinuousOn (F N) S)
    {b : ℕ → ℝ} (hb : Tendsto b atTop (𝓝 0))
    (hu : ∀ M N, M ≤ N → ∀ s ∈ S, ‖F N s - F M s‖ ≤ b M) :
    ∃ G : ℝ → ℂ, ContinuousOn G S ∧ ∀ s ∈ S, Tendsto (F · s) atTop (𝓝 (G s)) ∧
      ∀ M, ‖G s - F M s‖ ≤ b M := by
  have hcs : ∀ s ∈ S, CauchySeq (F · s) := by
    intro s hs
    refine cauchySeq_of_le_tendsto_0 (fun M => 2 * b M) (fun n m M hn hm => ?_) (by simpa using hb.const_mul 2)
    rw [dist_eq_norm]
    calc ‖F n s - F m s‖ = ‖(F n s - F M s) - (F m s - F M s)‖ := by ring_nf
      _ ≤ ‖F n s - F M s‖ + ‖F m s - F M s‖ := norm_sub_le _ _
      _ ≤ b M + b M := add_le_add (hu M n hn s hs) (hu M m hm s hs)
      _ = 2 * b M := by ring
  choose! G hG using fun s hs => cauchySeq_tendsto_of_complete (hcs s hs)
  have hbd : ∀ s ∈ S, ∀ M, ‖G s - F M s‖ ≤ b M := by
    intro s hs M
    have : Tendsto (fun N => ‖F N s - F M s‖) atTop (𝓝 ‖G s - F M s‖) :=
      ((hG s hs).sub_const _).norm
    exact le_of_tendsto this (eventually_atTop.mpr ⟨M, fun N hN => hu M N hN s hs⟩)
  refine ⟨G, ?_, fun s hs => ⟨hG s hs, hbd s hs⟩⟩
  refine TendstoUniformlyOn.continuousOn (F := F) (p := atTop) ?_ (Frequently.of_forall hc)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hb.eventually (gt_mem_nhds hε)] with M hM s hs
  rw [dist_eq_norm]
  exact (hbd s hs M).trans_lt hM

/-! ### Character sums -/

section chars
variable {q : ℕ} [NeZero q]

/-- A full period of a nontrivial character sums to $0$: $\sum_{0 \le k < q}\chi(n + k) = 0$. -/
theorem sum_range_period (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ∑ k ∈ range q, χ ((n + k : ℕ) : ZMod q) = 0 := by
  rw [Finset.sum_range (fun k => χ ((n + k : ℕ) : ZMod q))]
  rw [← MulChar.sum_eq_zero_of_ne_one hχ]
  refine Fintype.sum_bijective (fun i : Fin q => ((n + i : ℕ) : ZMod q)) ?_ _ _ (fun _ => rfl)
  rw [Fintype.bijective_iff_injective_and_card, ZMod.card, Fintype.card_fin]
  refine ⟨fun i j h => ?_, rfl⟩
  simp only at h
  rw [ZMod.natCast_eq_natCast_iff] at h
  have := Nat.ModEq.add_left_cancel' n h
  exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt this i.2 j.2)

/-- **Character sums are bounded:** for $\chi \ne 1$ modulo $q$, $\left|\sum_{0 \le k < n}\chi(k)\right| \le q$ for
every $n$. Source: Davenport Ch. 4; Apostol Thm. 6.17 context [unverified locators]. -/
@[kb "davenport2000" "Ch. 4 (character sums over a period vanish) [unverified locator]"]
theorem norm_sum_range_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ range n, χ (k : ZMod q)‖ ≤ q := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < q
    · calc _ ≤ ∑ k ∈ range n, ‖χ (k : ZMod q)‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ range n, (1 : ℝ) := sum_le_sum fun k _ => DirichletCharacter.norm_le_one χ _
        _ = n := by simp
        _ ≤ q := by exact_mod_cast hn.le
    · replace hn := not_lt.mp hn
      have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
      obtain ⟨m, rfl⟩ : ∃ m, n = m + q := ⟨n - q, by omega⟩
      rw [sum_range_add, sum_range_period χ hχ m, add_zero]
      exact ih m (by omega)

end chars

/-! ### The weight $n^{-s}$ and $L(1,\chi) = \sum_n\chi(n)/n$ -/

/-- The real weight $n \mapsto n^{-s}$, with value $0$ at $n = 0$. -/
noncomputable def wpow (s : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else (n : ℝ) ^ (-s)

/-- $n^{-s} \ge 0$. -/
theorem wpow_nonneg (s : ℝ) (n : ℕ) : 0 ≤ wpow s n := by
  unfold wpow; split_ifs <;> positivity

/-- $n \mapsto n^{-s}$ is nonincreasing for $n \ge 1$, $s \ge 0$. -/
theorem wpow_succ_le {s : ℝ} (hs : 0 ≤ s) {n : ℕ} (hn : 1 ≤ n) : wpow s (n + 1) ≤ wpow s n := by
  unfold wpow
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (by omega : 0 < n)) (by push_cast; linarith)
    (by linarith)

/-- $n^{-s} \le 2/(n+1)$ for $n \ge 1$, $s \ge 1$. -/
theorem wpow_le_inv {s : ℝ} (hs : 1 ≤ s) {n : ℕ} (hn : 1 ≤ n) : wpow s n ≤ 2 / (n + 1) := by
  unfold wpow
  rw [ite_eq_right (by omega)]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc (n : ℝ) ^ (-s) ≤ (n : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn' (by linarith)
    _ = 1 / n := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 2 / (n + 1) := by rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith

/-- $s \mapsto n^{-s}$ is continuous. -/
theorem continuous_wpow (n : ℕ) : Continuous fun s => wpow s n := by
  unfold wpow
  split_ifs with h
  · exact continuous_const
  · exact continuous_const.rpow continuous_neg fun _ => Or.inl (by exact_mod_cast h)


/-- Abel's inequality for weights with $w_0 = 0$, $w \ge 0$, nonincreasing from $n = 1$ on:
$\left|\sum_{M \le n < N}a_nw_n\right| \le 2Bw_{\max(M,1)}$. -/
theorem norm_sum_Ico_mul_le' (a : ℕ → ℂ) (w : ℕ → ℝ) {B : ℝ}
    (hA : ∀ n, ‖∑ k ∈ range n, a k‖ ≤ B) (hw0 : w 0 = 0) (hpos : ∀ n, 0 ≤ w n)
    (hw : ∀ n, 1 ≤ n → w (n + 1) ≤ w n) {M N : ℕ} (hMN : M ≤ N) :
    ‖∑ n ∈ Ico M N, a n * w n‖ ≤ 2 * B * w (max M 1) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hA 0)
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [Ico_self, sum_empty, norm_zero]; exact mul_nonneg (by linarith) (hpos _)
    · rw [sum_eq_sum_Ico_succ_bot hN, hw0, Complex.ofReal_zero, mul_zero, zero_add]
      exact norm_sum_Ico_mul_le a w hA hN (fun n hn _ => hw n hn) (hpos _)
  · rw [max_eq_left hM]
    exact norm_sum_Ico_mul_le a w hA hMN (fun n hn _ => hw n (by omega)) (hpos _)

/-- Tail bound with the weight $n^{-s}$, $s \ge 1$: $\left|\sum_{M \le n < N}a_nn^{-s}\right| \le 4B/(M+1)$. -/
theorem norm_sum_Ico_mul_wpow_le (a : ℕ → ℂ) {B : ℝ} (hA : ∀ n, ‖∑ k ∈ range n, a k‖ ≤ B)
    {s : ℝ} (hs : 1 ≤ s) {M N : ℕ} (hMN : M ≤ N) :
    ‖∑ n ∈ Ico M N, a n * wpow s n‖ ≤ 4 * B / (M + 1) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hA 0)
  refine (norm_sum_Ico_mul_le' a (wpow s) hA (by simp [wpow]) (wpow_nonneg s)
    (fun n hn => wpow_succ_le (by linarith) hn) hMN).trans ?_
  have h1 := wpow_le_inv hs (le_max_right M 1)
  have h2 : (2 : ℝ) / ((max M 1 : ℕ) + 1) ≤ 2 / (M + 1) := by
    gcongr; exact_mod_cast le_max_left M 1
  calc 2 * B * wpow s (max M 1) ≤ 2 * B * (2 / (M + 1)) := by gcongr; exact h1.trans h2
    _ = 4 * B / (M + 1) := by ring

/-- **Identification at the boundary point.** If $G$ is continuous on $[1,2]$, $L_f$ is continuous at $1$, and
$G = L_f$ on $(1,2]$, then $G(1) = L_f(1)$. -/
theorem eq_at_one_of_continuousOn {G Lf : ℝ → ℂ} (hG : ContinuousOn G (Set.Icc 1 2))
    (hL : ContinuousAt Lf 1) (h : ∀ s ∈ Set.Ioc (1 : ℝ) 2, G s = Lf s) : G 1 = Lf 1 := by
  have hmem : Set.Ioc (1 : ℝ) 2 ∈ 𝓝[>] (1 : ℝ) := Ioc_mem_nhdsGT (by norm_num)
  have h1 : Tendsto G (𝓝[>] 1) (𝓝 (G 1)) :=
    ((hG 1 ⟨le_rfl, by norm_num⟩).mono_of_mem_nhdsWithin
      (mem_of_superset hmem Set.Ioc_subset_Icc_self))
  have h2 : Tendsto Lf (𝓝[>] 1) (𝓝 (Lf 1)) := hL.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique_of_eventuallyEq h1 h2 (eventually_of_mem hmem h)

section Lone
variable {q : ℕ} [NeZero q]

/-- Partial sums $\sum_{n<N}\chi(n)n^{-s}$. -/
noncomputable def lpart (χ : DirichletCharacter ℂ q) (N : ℕ) (s : ℝ) : ℂ :=
  ∑ n ∈ range N, χ n * (wpow s n : ℂ)

/-- Mathlib's L-series term $\chi(n)/n^s$ at real $s$ is $\chi(n)\cdot n^{-s}$ (`wpow`). -/
theorem term_eq_wpow (χ : DirichletCharacter ℂ q) (s : ℝ) (n : ℕ) :
    LSeries.term (fun n => χ n) (s : ℂ) n = χ n * (wpow s n : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [wpow]
  · rw [LSeries.term_of_ne_zero hn, wpow, ite_eq_right hn,
      Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_neg, Complex.cpow_neg,
      div_eq_mul_inv]
    simp

/-- For $s > 1$, $\sum_{n<N}\chi(n)n^{-s} \to L(s,\chi)$. -/
theorem lpart_tendsto (χ : DirichletCharacter ℂ q) {s : ℝ} (hs : 1 < s) :
    Tendsto (lpart χ · s) atTop (𝓝 (χ.LFunction s)) := by
  have hsum := (DirichletCharacter.LSeriesSummable_of_one_lt_re χ (s := (s : ℂ))
    (by simpa using hs)).hasSum
  rw [DirichletCharacter.LFunction_eq_LSeries χ (by simpa using hs)]
  refine hsum.tendsto_sum_nat.congr fun N => ?_
  simp only [lpart, term_eq_wpow]

/-- Uniform Cauchy bound: $\left|\sum_{M \le n < N}\chi(n)n^{-s}\right| \le 4q/(M+1)$ for $s \ge 1$, $\chi \ne 1$. -/
theorem norm_lpart_sub_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 1 ≤ s)
    {M N : ℕ} (hMN : M ≤ N) : ‖lpart χ N s - lpart χ M s‖ ≤ 4 * q / (M + 1) := by
  rw [lpart, lpart, ← sum_Ico_eq_sub _ hMN]
  exact norm_sum_Ico_mul_wpow_le _ (norm_sum_range_le χ hχ) hs hMN

/-- The partial sums $s \mapsto \sum_{n<N}\chi(n)n^{-s}$ are continuous. -/
theorem continuous_lpart (χ : DirichletCharacter ℂ q) (N : ℕ) : Continuous (lpart χ N) := by
  unfold lpart
  exact continuous_finsetSum _ fun n _ =>
    continuous_const.mul (Complex.continuous_ofReal.comp (continuous_wpow n))

/-- **$L(1,\chi) = \sum_{n \ge 1}\chi(n)/n$, with rate.** For a nontrivial Dirichlet character $\chi$ mod $q$
and every $M$: $\left|\sum_{0 \le n < M}\chi(n)/n - L(1,\chi)\right| \le 4q/(M+1)$, where $L(1,\chi)$ is Mathlib's
`DirichletCharacter.LFunction χ 1` (an Abelian argument: uniform convergence on $[1,2]$ plus continuity of $L$).
Source: Apostol Thm. 6.17(a) / Davenport Ch. 6 [unverified locators]. -/
@[kb "apostol1976" "Ch. 6, Thm. 6.17 (sum of χ(n)/n with error O(1/x)) [unverified locator]"]
theorem norm_lpart_one_sub_LFunction_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M : ℕ) :
    ‖lpart χ M 1 - χ.LFunction 1‖ ≤ 4 * q / (M + 1) := by
  have hb : Tendsto (fun M : ℕ => 4 * (q : ℝ) / (M + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (4 * (q : ℝ))
  obtain ⟨G, hGc, hG⟩ := exists_continuousOn_limit (S := Set.Icc 1 2)
    (fun N => (continuous_lpart χ N).continuousOn) hb
    (fun M N hMN s hs => norm_lpart_sub_le χ hχ hs.1 hMN)
  have hGL : G 1 = χ.LFunction ((1 : ℝ) : ℂ) := by
    refine eq_at_one_of_continuousOn (Lf := fun s : ℝ => χ.LFunction s) hGc ?_ fun s hs => ?_
    · exact ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
        Complex.continuous_ofReal).continuousAt
    · exact tendsto_nhds_unique (hG s (Set.Ioc_subset_Icc_self hs)).1 (lpart_tendsto χ hs.1)
  have := (hG 1 ⟨le_rfl, by norm_num⟩).2 M
  rw [hGL, norm_sub_rev] at this
  simpa using this

end Lone


/-- $\log n / n \ge 0$. -/
theorem log_div_nonneg (n : ℕ) : 0 ≤ Real.log n / n :=
  div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)

/-- $\log n / n \le 1$. -/
theorem log_div_le_one (n : ℕ) : Real.log n / n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_one hn']
    linarith [Real.log_le_sub_one_of_pos hn']

/-- $\sum_{0 \le n \le N}f(n) = \sum_{1 \le n \le N}f(n)$ when $f(0) = 0$. -/
theorem sum_range_succ_eq_sum_Ioc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (h0 : f 0 = 0) (N : ℕ) :
    ∑ n ∈ range (N + 1), f n = ∑ n ∈ Ioc 0 N, f n := by
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), h0, zero_add]
  rfl

section Mertens
variable {q : ℕ} [NeZero q]

open ArithmeticFunction in
/-- $\left|\sum_{0 \le n < N}\chi(n)\log n/n\right| \le 2q + 3$ for $\chi \ne 1$ (Abel's inequality; $\log x/x$
decreases for $x \ge e$). -/
theorem norm_sum_chi_log_div_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ range N, χ n * ((Real.log n / n : ℝ) : ℂ)‖ ≤ 2 * q + 3 := by
  set w : ℕ → ℝ := fun n => Real.log n / n
  rw [← sum_range_add_sum_Ico _ (min_le_left N 3)]
  have h1 : ‖∑ n ∈ range (min N 3), χ n * (w n : ℂ)‖ ≤ 3 := by
    calc _ ≤ ∑ n ∈ range (min N 3), ‖χ n * (w n : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ range (min N 3), (1 : ℝ) := by
        refine sum_le_sum fun n _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (log_div_nonneg n)]
        calc ‖χ n‖ * w n ≤ 1 * 1 :=
              mul_le_mul (DirichletCharacter.norm_le_one χ _) (log_div_le_one n) (log_div_nonneg n) zero_le_one
          _ = 1 := one_mul 1
      _ ≤ 3 := by simp
  have h2 : ‖∑ n ∈ Ico (min N 3) N, χ n * (w n : ℂ)‖ ≤ 2 * q := by
    rcases le_or_gt N 3 with hN | hN
    · rw [min_eq_left hN, Ico_self, sum_empty, norm_zero]; positivity
    · rw [min_eq_right hN.le]
      have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      refine (norm_sum_Ico_mul_le (fun n => χ n) w (norm_sum_range_le χ hχ) hN.le
        (fun n hn _ => ?_) (log_div_nonneg N)).trans ?_
      · refine Real.log_div_self_antitoneOn (Set.mem_Ici.mpr ?_) (Set.mem_Ici.mpr ?_) (by simp)
        · exact he.trans (by exact_mod_cast hn)
        · exact he.trans (by exact_mod_cast (by omega : 3 ≤ n + 1))
      · have := log_div_le_one 3
        have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
        calc 2 * (q : ℝ) * w 3 ≤ 2 * q * 1 := by gcongr
          _ = 2 * q := by ring
  calc _ ≤ _ + _ := norm_add_le _ _
    _ ≤ 3 + 2 * q := add_le_add h1 h2
    _ = _ := by ring

/-- $\Lambda(n)\chi(n)/n$ as an arithmetic function. -/
noncomputable def fA (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  ⟨fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * χ n * (n : ℂ)⁻¹, by simp⟩

/-- $\chi(n)/n$ as an arithmetic function. -/
noncomputable def gA (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  ⟨fun n => χ n * (n : ℂ)⁻¹, by simp⟩

/-- $\sum_{dm = n}\frac{\Lambda(d)\chi(d)}{d}\cdot\frac{\chi(m)}{m} = \chi(n)\frac{\log n}{n}$ (from $\sum_{d\mid n}\Lambda(d) = \log n$). -/
theorem fA_mul_gA_apply (χ : DirichletCharacter ℂ q) (n : ℕ) :
    (fA χ * gA χ) n = χ n * ((Real.log n / n : ℝ) : ℂ) := by
  rw [ArithmeticFunction.mul_apply]
  have : ∀ x ∈ n.divisorsAntidiagonal, fA χ x.1 * gA χ x.2 =
      (ArithmeticFunction.vonMangoldt x.1 : ℂ) * (χ n * (n : ℂ)⁻¹) := by
    intro x hx
    obtain ⟨hx, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    simp only [fA, gA, ArithmeticFunction.coe_mk]
    rw [← hx]; push_cast
    rw [map_mul, mul_inv]; ring
  rw [sum_congr rfl this, ← sum_mul, Nat.sum_divisorsAntidiagonal (fun a _ => (ArithmeticFunction.vonMangoldt a : ℂ))]
  rw [← Complex.ofReal_sum, ArithmeticFunction.vonMangoldt_sum]
  push_cast; ring

/-- $\sum_{1 \le m \le K}\chi(m)/m$ is the partial sum `lpart χ (K + 1) 1`. -/
theorem gA_partial (χ : DirichletCharacter ℂ q) (K : ℕ) :
    ∑ m ∈ Ioc 0 K, gA χ m = lpart χ (K + 1) 1 := by
  rw [lpart, sum_range_succ_eq_sum_Ioc _ (by simp [wpow])]
  refine sum_congr rfl fun m _ => ?_
  simp only [gA, ArithmeticFunction.coe_mk, wpow]
  split_ifs with h
  · simp [h]
  · rw [Real.rpow_neg_one]; push_cast; rfl



/-- $|\Lambda(d)\chi(d)/d| \le \Lambda(d)/d$. -/
theorem norm_fA_le (χ : DirichletCharacter ℂ q) (d : ℕ) :
    ‖fA χ d‖ ≤ ArithmeticFunction.vonMangoldt d / d := by
  simp only [fA, ArithmeticFunction.coe_mk, norm_mul, norm_inv, Complex.norm_real, Complex.norm_natCast,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  rw [div_eq_mul_inv]
  have h1 := DirichletCharacter.norm_le_one χ (d : ZMod q)
  have h2 := @ArithmeticFunction.vonMangoldt_nonneg d
  have h3 : (0 : ℝ) ≤ (d : ℝ)⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right h2 h1) h3

/-- **The twisted Chebyshev sum is bounded.** For a nontrivial Dirichlet character $\chi$ mod $q$ and every $N$:
$$\left|\sum_{1 \le n \le N}\frac{\Lambda(n)\chi(n)}{n}\right| \le \frac{26q + 3}{|L(1,\chi)|}.$$
This is where $L(1,\chi) \ne 0$ (Mathlib, `DirichletCharacter.LFunction_apply_one_ne_zero`) is used. Source:
Apostol Ch. 7 (Lemma: $\sum_{n \le x}\chi(n)\Lambda(n)/n = O(1)$ if $L(1,\chi) \ne 0$); Montgomery–Vaughan §4.3;
Davenport Ch. 7 [unverified locators]. -/
@[kb "apostol1976" "Ch. 7 (Σ χ(n)Λ(n)/n = O(1) when L(1,χ) ≠ 0) [unverified locator]"]
theorem norm_sum_fA_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ d ∈ Ioc 0 N, fA χ d‖ ≤ (26 * q + 3) / ‖χ.LFunction 1‖ := by
  set L1 := χ.LFunction 1
  have hL1 : L1 ≠ 0 := DirichletCharacter.LFunction_apply_one_ne_zero hχ
  have hid := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum (fA χ) (gA χ) N
  simp_rw [gA_partial] at hid
  have hsplit : ∑ d ∈ Ioc 0 N, fA χ d * lpart χ (N / d + 1) 1 =
      L1 * ∑ d ∈ Ioc 0 N, fA χ d + ∑ d ∈ Ioc 0 N, fA χ d * (lpart χ (N / d + 1) 1 - L1) := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun d _ => by ring
  rw [hsplit] at hid
  have hlhs : ‖∑ n ∈ Ioc 0 N, (fA χ * gA χ) n‖ ≤ 2 * q + 3 := by
    rw [← sum_range_succ_eq_sum_Ioc _ (by simp)]
    simp_rw [fA_mul_gA_apply]
    exact norm_sum_chi_log_div_le χ hχ (N + 1)
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have herr : ‖∑ d ∈ Ioc 0 N, fA χ d * (lpart χ (N / d + 1) 1 - L1)‖ ≤ 24 * q := by
    have hterm : ∀ d ∈ Ioc 0 N, ‖fA χ d * (lpart χ (N / d + 1) 1 - L1)‖ ≤
        4 * q * ArithmeticFunction.vonMangoldt d / (N + 1) := by
      intro d hd
      have hd1 : 0 < d := (mem_Ioc.mp hd).1
      have hd' : (0 : ℝ) < d := by exact_mod_cast hd1
      have hlt : N + 1 ≤ d * (N / d + 2) := by
        have := Nat.lt_mul_div_succ N hd1; nlinarith
      have hlt' : (N : ℝ) + 1 ≤ d * ((N / d : ℕ) + 2) := by exact_mod_cast hlt
      have hΛ := @ArithmeticFunction.vonMangoldt_nonneg d
      rw [norm_mul]
      calc _ ≤ ArithmeticFunction.vonMangoldt d / d * (4 * q / ((N / d + 1 : ℕ) + 1)) :=
            mul_le_mul (norm_fA_le χ d) (norm_lpart_one_sub_LFunction_le χ hχ _) (norm_nonneg _)
              (by positivity)
        _ = 4 * q * ArithmeticFunction.vonMangoldt d / (d * ((N / d : ℕ) + 2)) := by
            push_cast; field_simp; ring
        _ ≤ _ := by gcongr
    calc _ ≤ ∑ d ∈ Ioc 0 N, ‖fA χ d * (lpart χ (N / d + 1) 1 - L1)‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ Ioc 0 N, 4 * q * ArithmeticFunction.vonMangoldt d / (N + 1) := sum_le_sum hterm
      _ = 4 * q * Chebyshev.psi N / (N + 1) := by
          rw [← sum_div, ← mul_sum, Chebyshev.psi, Nat.floor_natCast]
      _ ≤ 4 * q * ((Real.log 4 + 4) * N) / (N + 1) := by
          gcongr; exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N)
      _ ≤ 4 * q * 6 := by
          rw [div_le_iff₀ (by positivity)]
          have hlog : Real.log 4 < 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
            push_cast
            linarith [Real.log_two_lt_d9]
          have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
          have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
          nlinarith [mul_nonneg hq hN]
      _ = 24 * q := by ring
  rw [le_div_iff₀ (norm_pos_iff.mpr hL1), mul_comm, ← norm_mul]
  have : L1 * ∑ d ∈ Ioc 0 N, fA χ d = ∑ n ∈ Ioc 0 N, (fA χ * gA χ) n -
      ∑ d ∈ Ioc 0 N, fA χ d * (lpart χ (N / d + 1) 1 - L1) := by rw [hid]; ring
  rw [this]
  calc _ ≤ _ + _ := norm_sub_le _ _
    _ ≤ (2 * q + 3) + 24 * q := add_le_add hlhs herr
    _ = _ := by ring



/-- $\chi(p)\log p/p$ at primes, $0$ elsewhere. -/
noncomputable def aP (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  if n.Prime then χ n * ((Real.log n / n : ℝ) : ℂ) else 0

/-- The constant bounding the non-prime part of $\sum\Lambda(n)/n$. -/
noncomputable def nonPrimeConst : ℝ :=
  ∑' n : ℕ, (if n.Prime then 0 else ArithmeticFunction.vonMangoldt n) / n

/-- $\sum_{n \text{ not prime}}\Lambda(n)/n$ converges (Mathlib's `summable_residueClass_non_primes_div`, $q = 1$). -/
theorem summable_nonPrime :
    Summable fun n : ℕ => (if n.Prime then 0 else ArithmeticFunction.vonMangoldt n) / n := by
  have h := ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div (q := 1) 0
  refine h.congr fun n => ?_
  congr 2
  simp [ArithmeticFunction.vonMangoldt.residueClass, Subsingleton.elim ((n : ZMod 1)) 0]

/-- Split $\Lambda(n)\chi(n)/n$ into its prime part and its prime-power part. -/
theorem fA_sub_aP (χ : DirichletCharacter ℂ q) (n : ℕ) :
    fA χ n = aP χ n + (if n.Prime then 0 else fA χ n) := by
  unfold aP
  split_ifs with h
  · simp only [fA, ArithmeticFunction.coe_mk, ArithmeticFunction.vonMangoldt_apply_prime h, add_zero]
    push_cast; ring
  · simp

/-- **Mertens-type bound over primes.** For a nontrivial Dirichlet character $\chi$ mod $q$ and every $N$:
$$\left|\sum_{p < N}\frac{\chi(p)\log p}{p}\right| \le \frac{26q + 3}{|L(1,\chi)|} + \sum_{n \text{ not prime}}\frac{\Lambda(n)}{n}.$$
Source: Montgomery–Vaughan §4.3 [unverified locator]; Davenport Ch. 7 [unverified locator]. -/
@[kb "montgomeryvaughan2007" "§4.3 (Mertens-type estimate for χ(p) log p / p) [unverified locator]"]
theorem norm_sum_aP_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ range N, aP χ n‖ ≤ (26 * q + 3) / ‖χ.LFunction 1‖ + nonPrimeConst := by
  have hK : 0 ≤ nonPrimeConst := tsum_nonneg fun n => by
    split_ifs <;> positivity [@ArithmeticFunction.vonMangoldt_nonneg n]
  have hC : 0 ≤ (26 * (q : ℝ) + 3) / ‖χ.LFunction 1‖ := by positivity
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [range_zero, sum_empty, norm_zero]; linarith
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hsum : ∑ n ∈ range (M + 1), aP χ n = ∑ n ∈ Ioc 0 M, fA χ n -
      ∑ n ∈ range (M + 1), (if n.Prime then 0 else fA χ n) := by
    rw [← sum_range_succ_eq_sum_Ioc _ (by simp), eq_sub_iff_add_eq, ← sum_add_distrib]
    exact sum_congr rfl fun n _ => (fA_sub_aP χ n).symm
  rw [hsum]
  refine (norm_sub_le _ _).trans (add_le_add (norm_sum_fA_le χ hχ M) ?_)
  calc _ ≤ ∑ n ∈ range (M + 1), ‖(if n.Prime then 0 else fA χ n)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ range (M + 1), (if n.Prime then 0 else ArithmeticFunction.vonMangoldt n) / n := by
        refine sum_le_sum fun n _ => ?_
        split_ifs
        · simp
        · exact norm_fA_le χ n
    _ ≤ nonPrimeConst := summable_nonPrime.sum_le_tsum _ fun n _ => by
        split_ifs <;> positivity [@ArithmeticFunction.vonMangoldt_nonneg n]



/-- $n^{-s} \le 1/n$ for $n \ge 1$, $s \ge 1$. -/
theorem wpow_le_inv' {s : ℝ} (hs : 1 ≤ s) {n : ℕ} (hn : 1 ≤ n) : wpow s n ≤ 1 / n := by
  unfold wpow
  rw [ite_eq_right (by omega)]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc (n : ℝ) ^ (-s) ≤ (n : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn' (by linarith)
    _ = 1 / n := by rw [Real.rpow_neg_one, one_div]

/-- The Abel weight $v_s(n) = n^{1-s}/\log n$. -/
noncomputable def vw (s : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (1 - s) / Real.log n

/-- $v_s(n) \ge 0$. -/
theorem vw_nonneg (s : ℝ) (n : ℕ) : 0 ≤ vw s n :=
  div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Real.log_natCast_nonneg n)

/-- $v_s(n) = n^{1-s}/\log n$ is nonincreasing for $n \ge 2$, $s \ge 1$. -/
theorem vw_succ_le {s : ℝ} (hs : 1 ≤ s) {n : ℕ} (hn : 2 ≤ n) : vw s (n + 1) ≤ vw s n := by
  unfold vw
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  push_cast
  have h1 : ((n : ℝ) + 1) ^ (1 - s) ≤ (n : ℝ) ^ (1 - s) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have h2 : Real.log n ≤ Real.log (n + 1) := Real.log_le_log (by linarith) (by linarith)
  exact div_le_div₀ (Real.rpow_nonneg (by positivity) _) h1 hlog h2

/-- $v_s(n) \le 1/\log n$ for $n \ge 2$, $s \ge 1$. -/
theorem vw_le {s : ℝ} (hs : 1 ≤ s) {n : ℕ} (hn : 2 ≤ n) : vw s n ≤ 1 / Real.log n := by
  unfold vw
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  gcongr
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)

/-- $\frac{\chi(p)\log p}{p}\cdot\frac{p^{1-s}}{\log p} = \chi(p)p^{-s}$ at primes. -/
theorem aP_mul_vw (χ : DirichletCharacter ℂ q) (s : ℝ) (n : ℕ) :
    aP χ n * (vw s n : ℂ) = if n.Prime then χ n * (wpow s n : ℂ) else 0 := by
  unfold aP
  split_ifs with h
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h.two_le
    have hn : (0 : ℝ) < n := by linarith
    have hlog : Real.log n ≠ 0 := (Real.log_pos (by linarith)).ne'
    rw [mul_assoc, ← Complex.ofReal_mul]
    congr 2
    rw [vw, wpow, ite_eq_right h.ne_zero, Real.rpow_sub hn, Real.rpow_one, Real.rpow_neg hn.le]
    field_simp
  · simp

/-- **Uniform tail bound for $\sum_p\chi(p)p^{-s}$:** $\left|\sum_{M \le p < N}\chi(p)p^{-s}\right| \le
2C_\chi/\log\max(M,2)$ for all $s \ge 1$ (Abel's inequality with the weights $v_s(\max(n,2))$). -/
theorem norm_sum_Ico_aP_vw_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 1 ≤ s)
    {M N : ℕ} (hMN : M ≤ N) :
    ‖∑ n ∈ Ico M N, aP χ n * (vw s n : ℂ)‖ ≤
      2 * ((26 * q + 3) / ‖χ.LFunction 1‖ + nonPrimeConst) / Real.log ((max M 2 : ℕ) : ℝ) := by
  have heq : ∑ n ∈ Ico M N, aP χ n * (vw s n : ℂ) =
      ∑ n ∈ Ico M N, aP χ n * (vw s (max n 2) : ℂ) := by
    refine sum_congr rfl fun n _ => ?_
    rcases le_or_gt 2 n with h | h
    · rw [max_eq_left h]
    · have : ¬ n.Prime := fun hp => by have := hp.two_le; omega
      simp [aP, this]
  rw [heq]
  refine (norm_sum_Ico_mul_le (aP χ) (fun n => vw s (max n 2)) (norm_sum_aP_le χ hχ) hMN
    (fun n _ _ => ?_) (vw_nonneg _ _)).trans ?_
  · rcases le_or_gt 2 n with h | h
    · rw [max_eq_left h, max_eq_left (by omega)]; exact vw_succ_le hs h
    · rcases (by omega : n + 1 = 2 ∨ n + 1 < 2) with h' | h'
      · rw [h', max_eq_right h.le, max_self]
      · rw [max_eq_right h.le, max_eq_right h'.le]
  · have hK : 0 ≤ nonPrimeConst := tsum_nonneg fun n => by
      split_ifs <;> positivity [@ArithmeticFunction.vonMangoldt_nonneg n]
    have hC : 0 ≤ (26 * (q : ℝ) + 3) / ‖χ.LFunction 1‖ := by positivity
    calc _ ≤ 2 * ((26 * q + 3) / ‖χ.LFunction 1‖ + nonPrimeConst) * (1 / Real.log ((max M 2 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (vw_le hs (le_max_right M 2)) (by positivity)
      _ = _ := by ring



/-- $\log(1 - \chi(p)p^{-s})$ at primes, $0$ elsewhere. -/
noncomputable def lterm (χ : DirichletCharacter ℂ q) (s : ℝ) (n : ℕ) : ℂ :=
  if n.Prime then Complex.log (1 - χ n * (wpow s n : ℂ)) else 0

/-- Partial sums of `lterm` over `n < N`. -/
noncomputable def Gpart (χ : DirichletCharacter ℂ q) (N : ℕ) (s : ℝ) : ℂ :=
  ∑ n ∈ range N, lterm χ s n

/-- $|\chi(n)n^{-s}| \le 1/n$ for $n \ge 1$, $s \ge 1$. -/
theorem norm_chi_wpow_le (χ : DirichletCharacter ℂ q) {s : ℝ} (hs : 1 ≤ s) {n : ℕ} (hn : 1 ≤ n) :
    ‖χ n * (wpow s n : ℂ)‖ ≤ 1 / n := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (wpow_nonneg s n)]
  calc _ ≤ 1 * wpow s n :=
        mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (wpow_nonneg s n)
    _ ≤ 1 / n := by rw [one_mul]; exact wpow_le_inv' hs hn

/-- $1 - \chi(p)p^{-s}$ has positive real part ($\ge \frac12$) for $s \ge 1$, so the principal logarithm is
continuous there. -/
theorem slitPlane_mem (χ : DirichletCharacter ℂ q) {s : ℝ} (hs : 1 ≤ s) {n : ℕ} (hn : n.Prime) :
    1 - χ n * (wpow s n : ℂ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have h1 := norm_chi_wpow_le χ hs hn.one_le
  have h2 : (1 : ℝ) / n ≤ 1 / 2 := by
    gcongr; exact_mod_cast hn.two_le
  have h3 := Complex.re_le_norm (χ n * (wpow s n : ℂ))
  rw [Complex.sub_re, Complex.one_re]
  linarith

/-- $|\log(1 - \chi(p)p^{-s}) + \chi(p)p^{-s}| \le 1/p^2$ for $s \ge 1$ (and $0$ off the primes). -/
theorem norm_lterm_add_le (χ : DirichletCharacter ℂ q) {s : ℝ} (hs : 1 ≤ s) (n : ℕ) :
    ‖lterm χ s n + aP χ n * (vw s n : ℂ)‖ ≤ 1 / (n : ℝ) ^ 2 := by
  rw [aP_mul_vw, lterm]
  split_ifs with hn
  · set z := χ n * (wpow s n : ℂ)
    have h1 := norm_chi_wpow_le χ hs hn.one_le
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
    have h2 : ‖z‖ ≤ 1 / 2 := h1.trans (by gcongr)
    have h := Complex.norm_log_one_add_sub_self_le (z := -z) (by rw [norm_neg]; linarith)
    rw [norm_neg, sub_neg_eq_add, ← sub_eq_add_neg] at h
    refine h.trans ?_
    have hz0 := norm_nonneg z
    have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    calc ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 * 2 / 2 := by gcongr
      _ = ‖z‖ ^ 2 := by ring
      _ ≤ (1 / n) ^ 2 := by gcongr
      _ = 1 / (n : ℝ) ^ 2 := by ring
  · simp

/-- A block sum of a nonnegative summable sequence is at most its tail: $\sum_{M\le n<N}f(n) \le \sum_{k \ge 0}f(k+M)$. -/
theorem sum_Ico_le_tail (f : ℕ → ℝ) (hf : Summable f) (h0 : ∀ n, 0 ≤ f n) (M N : ℕ) :
    ∑ n ∈ Ico M N, f n ≤ ∑' k, f (k + M) := by
  rw [sum_Ico_eq_sum_range]
  simp_rw [add_comm M]
  exact ((summable_nat_add_iff M).mpr hf).sum_le_tsum _ fun n _ => h0 _

/-- The uniform tail bound for `Gpart`. -/
noncomputable def gtail (χ : DirichletCharacter ℂ q) (M : ℕ) : ℝ :=
  2 * ((26 * q + 3) / ‖χ.LFunction 1‖ + nonPrimeConst) / Real.log ((max M 2 : ℕ) : ℝ) +
    ∑' k : ℕ, 1 / ((k + M : ℕ) : ℝ) ^ 2

/-- The tail bound `gtail χ M` tends to $0$. -/
theorem tendsto_gtail (χ : DirichletCharacter ℂ q) : Tendsto (gtail χ) atTop (𝓝 0) := by
  rw [show (0 : ℝ) = 0 + 0 by simp]
  refine Tendsto.add ?_ ?_
  · refine Tendsto.div_atTop tendsto_const_nhds ?_
    refine Real.tendsto_log_atTop.comp ?_
    refine tendsto_natCast_atTop_atTop.comp ?_
    exact tendsto_atTop_mono (fun M => le_max_left M 2) tendsto_id
  · exact tendsto_sum_nat_add fun k : ℕ => 1 / ((k : ℕ) : ℝ) ^ 2

/-- **The log-partial-products are uniformly Cauchy on $s \ge 1$:**
$\left|\sum_{M \le p < N}\log(1 - \chi(p)p^{-s})\right| \le$ `gtail χ M` $\to 0$. -/
theorem norm_Gpart_sub_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 1 ≤ s)
    {M N : ℕ} (hMN : M ≤ N) : ‖Gpart χ N s - Gpart χ M s‖ ≤ gtail χ M := by
  rw [Gpart, Gpart, ← sum_Ico_eq_sub _ hMN]
  have hsplit : ∑ n ∈ Ico M N, lterm χ s n = -∑ n ∈ Ico M N, aP χ n * (vw s n : ℂ) +
      ∑ n ∈ Ico M N, (lterm χ s n + aP χ n * (vw s n : ℂ)) := by
    rw [sum_add_distrib]; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_neg]; exact norm_sum_Ico_aP_vw_le χ hχ hs hMN
  · refine (norm_sum_le _ _).trans ((sum_le_sum fun n _ => norm_lterm_add_le χ hs n).trans ?_)
    exact sum_Ico_le_tail (fun n : ℕ => 1 / (n : ℝ) ^ 2)
      (Real.summable_one_div_nat_pow.mpr one_lt_two) (fun n => by positivity) M N

/-- Each `Gpart χ N` is continuous on $[1,2]$. -/
theorem continuousOn_Gpart (χ : DirichletCharacter ℂ q) (N : ℕ) :
    ContinuousOn (Gpart χ N) (Set.Icc 1 2) := by
  unfold Gpart
  refine continuousOn_finsetSum _ fun n _ => ?_
  unfold lterm
  split_ifs with hn
  · refine ContinuousOn.clog ?_ fun s hs => slitPlane_mem χ hs.1 hn
    exact (continuous_const.sub (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_wpow n)))).continuousOn
  · exact continuousOn_const

/-- $\exp\sum_{p<N}\log(1 - \chi(p)p^{-s}) = \prod_{p<N}(1 - \chi(p)p^{-s})$ for $s \ge 1$. -/
theorem exp_Gpart (χ : DirichletCharacter ℂ q) {s : ℝ} (hs : 1 ≤ s) (N : ℕ) :
    Complex.exp (Gpart χ N s) = ∏ p ∈ Nat.primesBelow N, (1 - χ p * (wpow s p : ℂ)) := by
  rw [Gpart, Nat.primesBelow, ← sum_filter_add_sum_filter_not (range N) Nat.Prime]
  rw [sum_eq_zero (s := filter (fun n => ¬ n.Prime) (range N)) fun n hn => by
    simp [lterm, (mem_filter.mp hn).2], add_zero, Complex.exp_sum]
  refine prod_congr rfl fun n hn => ?_
  have hp := (mem_filter.mp hn).2
  rw [lterm, ite_eq_left hp, Complex.exp_log (Complex.slitPlane_ne_zero (slitPlane_mem χ hs hp))]

/-- `wpow s n` as a complex power: $n^{-s}$. -/
theorem wpow_cast_eq {s : ℝ} {n : ℕ} (hn : n ≠ 0) : ((wpow s n : ℝ) : ℂ) = (n : ℂ) ^ (-(s : ℂ)) := by
  rw [wpow, ite_eq_right hn, Complex.ofReal_cpow (Nat.cast_nonneg n)]
  simp

/-- Mathlib's Euler product for $s > 1$, natural order: $\prod_{p<N}(1 - \chi(p)p^{-s}) \to L(s,\chi)^{-1}$. -/
theorem tendsto_prod_of_one_lt (χ : DirichletCharacter ℂ q) {s : ℝ} (hs : 1 < s) :
    Tendsto (fun N => ∏ p ∈ Nat.primesBelow N, (1 - χ p * (wpow s p : ℂ))) atTop
      (𝓝 (χ.LFunction s)⁻¹) := by
  have hs' : 1 < (s : ℂ).re := by simpa using hs
  have h := DirichletCharacter.LSeries_eulerProduct χ hs'
  rw [← DirichletCharacter.LFunction_eq_LSeries χ hs'] at h
  have hne : χ.LFunction s ≠ 0 := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs']
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hs'
  refine (h.inv₀ hne).congr fun N => ?_
  rw [prod_inv_distrib, inv_inv]
  refine prod_congr rfl fun p hp => ?_
  rw [wpow_cast_eq (Nat.prime_of_mem_primesBelow hp).ne_zero]

/-- **The Euler product of $L(s,\chi)$ at $s = 1$, natural order of the primes.** For every nontrivial Dirichlet
character $\chi$ modulo $q \ge 1$ (values in $\mathbb{C}$):
$$\prod_{p < N}\Big(1 - \frac{\chi(p)}{p}\Big) \longrightarrow L(1,\chi)^{-1} \qquad (N \to \infty),$$
the product over the primes $p < N$ (`Nat.primesBelow N`), with $L(1,\chi)$ = `DirichletCharacter.LFunction χ 1`
($\ne 0$). Proof: route steps 1–7 of the module docstring (Mertens-type bound plus an Abelian argument on $[1,2]$).
Sources: Montgomery–Vaughan §4.3 [unverified locator]; Davenport Ch. 7 [unverified locator];
Landau, *Handbuch* (1909) [unverified]. -/
@[kb "montgomeryvaughan2007" "§4.3 (Euler product at s = 1 for nonprincipal χ) [unverified locator]"]
theorem tendsto_prod_primesBelow (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Tendsto (fun N => ∏ p ∈ Nat.primesBelow N, (1 - χ p / p)) atTop (𝓝 (χ.LFunction 1)⁻¹) := by
  obtain ⟨G, hGc, hG⟩ := exists_continuousOn_limit (continuousOn_Gpart χ) (tendsto_gtail χ)
    (fun M N hMN s hs => norm_Gpart_sub_le χ hχ hs.1 hMN)
  have hL1 : χ.LFunction 1 ≠ 0 := DirichletCharacter.LFunction_apply_one_ne_zero hχ
  have hval : Complex.exp (G 1) = (χ.LFunction ((1 : ℝ) : ℂ))⁻¹ := by
    refine eq_at_one_of_continuousOn (G := fun s => Complex.exp (G s))
      (Lf := fun s : ℝ => (χ.LFunction s)⁻¹) (Complex.continuous_exp.comp_continuousOn hGc) ?_
      fun s hs => ?_
    · refine ContinuousAt.inv₀ ?_ (by simpa using hL1)
      exact ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
        Complex.continuous_ofReal).continuousAt
    · have h1 : Tendsto (fun N => Complex.exp (Gpart χ N s)) atTop (𝓝 (Complex.exp (G s))) :=
        (Complex.continuous_exp.tendsto _).comp (hG s (Set.Ioc_subset_Icc_self hs)).1
      simp_rw [exp_Gpart χ hs.1.le] at h1
      exact tendsto_nhds_unique h1 (tendsto_prod_of_one_lt χ hs.1)
  have h1 : Tendsto (fun N => Complex.exp (Gpart χ N 1)) atTop (𝓝 (Complex.exp (G 1))) :=
    (Complex.continuous_exp.tendsto _).comp (hG 1 ⟨le_rfl, by norm_num⟩).1
  simp_rw [exp_Gpart χ le_rfl, hval] at h1
  refine (h1.congr fun N => prod_congr rfl fun p hp => ?_).trans (by simp)
  rw [wpow, ite_eq_right (Nat.prime_of_mem_primesBelow hp).ne_zero, Real.rpow_neg_one]
  push_cast; ring

end Mertens

end QuadFormsKB.Binary.EulerOne

/-! ### The Kronecker character: The input is a theorem -/

namespace QuadFormsKB.Binary

open BinQF Siegel

variable {D : ℤ} [IsQuadDisc D]

/-- **`EulerProductAtOne D` holds** for every fundamental discriminant $D \ne 1$ (`IsQuadDisc D`; either sign):
$$\prod_{p \le X}\Big(1 - \frac{\chi_D(p)}{p}\Big) \longrightarrow L(1,\chi_D)^{-1} \qquad (X \to \infty),$$
the product over the primes $p \le X$ (`Siegel.primesUpTo X`) in $\mathbb{C}$. This is
`EulerOne.tendsto_prod_primesBelow` for the nontrivial character $\chi_D$ (`kroneckerChar_ne_one`), reindexed from
$p < X + 1$ to $p \le X$. It discharges the input of `isEulerProductValue_binary` and `siegelFormula_binary_natural`.
Sources: Montgomery–Vaughan §4.3 [unverified locator]; Landau, *Handbuch* (1909) [unverified]. -/
@[kb "montgomeryvaughan2007" "§4.3 (Euler product at s = 1 for nonprincipal χ) [unverified locator]"]
theorem eulerProductAtOne (D : ℤ) [IsQuadDisc D] : EulerProductAtOne D := by
  constructor
  have h := (EulerOne.tendsto_prod_primesBelow (kroneckerChar D) kroneckerChar_ne_one).comp
    (tendsto_add_atTop_nat 1)
  refine h.congr fun X => ?_
  simp only [Function.comp_apply, primesUpTo, Nat.primesBelow]
  exact (Finset.prod_subtype_eq_prod_filter _).symm

/-- **The real form:** $\prod_{p \le X}(1 - \chi_D(p)/p) \to L(1,\chi_D)^{-1}$ in $\mathbb{R}$ (`kronR`, `LOne`),
unconditionally. -/
@[kb "montgomeryvaughan2007" "§4.3 (Euler product at s = 1 for nonprincipal χ) [unverified locator]"]
theorem tendsto_prod_one_sub_kronR_div :
    Tendsto (fun X : ℕ => ∏ p ∈ primesUpTo X, (1 - kronR D p / p)) atTop (𝓝 (LOne D)⁻¹) :=
  (eulerProductAtOne D).tendsto_real

/-- **The natural-order value of $\prod_p\beta_p(m)$ is `binaryEulerValue`, unconditionally.** For any form $f$ of
fundamental discriminant $D$ and $m \ne 0$: $\prod_{p \le X}\beta_p(m) \to L(1,\chi_D)^{-1}C_f(m)$ as $X \to \infty$
(`isEulerProductValue_binary` with `eulerProductAtOne`). -/
@[kb "siegel1935" "§§1–2 (n = 2: conditionally convergent product) [unverified locator]"]
theorem isEulerProductValue_binary' {f : BinQF} (hD : f.disc = D) {m : ℤ} (hm : m ≠ 0) :
    IsEulerProductValue f m (binaryEulerValue f D m) :=
  isEulerProductValue_binary (eulerProductAtOne D) hD hm

/-- **Siegel's formula for binary forms in the natural order of the primes, unconditional.** For $D < 0$
fundamental, $f$ primitive positive definite of discriminant $D$, $m \ge 1$, and **any** $P$ with
$\prod_{p \le X}\beta_p(m) \to P$ (`IsEulerProductValue f m P`):
$$r_{\mathcal G}(m) = \frac12\,\beta_\infty(m)\,P = \frac12\,\beta_\infty(m)\prod_p\beta_p(m).$$
(`siegelFormula_binary_natural` with its input discharged by `eulerProductAtOne`.) Source: Siegel (1935), Hauptsatz
($\varepsilon = \frac12$ for $n = 2$) [unverified locator]. -/
@[kb "siegel1935" "Hauptsatz (ε = 1/2 for n = 2), natural-order product [unverified locator]"]
theorem siegelFormula_binary_natural' [Fact (D < 0)] (f : PosForms D) {m : ℕ} (hm : m ≠ 0) {P : ℝ}
    (hP : IsEulerProductValue f.1 m P) :
    Siegel.genusRepAvg f.1 m = (1 / 2 : ℝ) * aEWith f.1 m P :=
  siegelFormula_binary_natural (eulerProductAtOne D) f hm hP

/-- **The natural-order Euler product exists and Siegel's formula holds with it, unconditionally** ($D < 0$
fundamental, $f$ primitive positive definite of discriminant $D$, $m \ge 1$). -/
@[kb "siegel1935" "Hauptsatz (ε = 1/2 for n = 2), natural-order product [unverified locator]"]
theorem exists_siegelFormula_binary_natural' [Fact (D < 0)] (f : PosForms D) {m : ℕ} (hm : m ≠ 0) :
    ∃ P : ℝ, IsEulerProductValue f.1 m P ∧ Siegel.genusRepAvg f.1 m = (1 / 2 : ℝ) * aEWith f.1 m P :=
  exists_siegelFormula_binary_natural (eulerProductAtOne D) f hm

end QuadFormsKB.Binary
