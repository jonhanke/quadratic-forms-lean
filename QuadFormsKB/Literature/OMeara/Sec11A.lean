/-
# O'Meara §11B–E: non-archimedean valuations, equivalence of valuations, weak approximation (11:1 – 11:8)

**Setting.** O'Meara's *valuation* on a field $F$ (Ch. I, §11A) is a function $|\ |\colon F \to \mathbb R$ with
$|a| = 0 \iff a = 0$, $|ab| = |a||b|$ and the triangle law; this is Mathlib's `AbsoluteValue F ℝ`. It is
*non-archimedean* when the strong triangle law $|a+b| \le \max(|a|,|b|)$ holds, Mathlib's `IsNonarchimedean`.
Two valuations are *equivalent* when they define the same topology (O'Meara §11C); Mathlib's
`AbsoluteValue.IsEquiv` is the order-theoretic version, and 11:4 below shows the two agree. For results about
convergent series the field is a Mathlib `NormedField`, with $|a| = \lVert a\rVert$.

**Proves** (O'Meara 1963, 1973 printing):
* `isNonarchimedean_iff_natCast_bounded` (**11:1**): a valuation is non-archimedean iff it is bounded on the natural
  integers of the field (the proof follows O'Meara's binomial estimate);
* `domination_sum` (**11:2**, Principle of Domination) and `domination_tsum` (**11:2a**, the series version);
* `eq_one_of_trivial_on_algebraic` (**11:3**): a valuation trivial on $F$ is trivial on an algebraic extension $E$;
* `equivalent_valuations_tfae` (**11:4**): equivalence of valuations (same topology; $|a|_1 < 1 \iff |a|_2 < 1$;
  $|\ |_1^{\varrho} = |\ |_2$ for some $\varrho > 0$), from Mathlib's `AbsoluteValue.isEquiv_iff_exists_rpow_eq`;
* `isEquiv_trivial_iff` (**11:4b**): the trivial valuation is equivalent to itself alone;
* `eq_of_isEquiv_of_eq_on_subfield` (**11:5**);
* `exists_one_lt_lt_one` (**11:7**) and `weak_approximation` (**11:8**, the Weak Approximation Theorem), from
  Mathlib's `AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv` and `AbsoluteValue.denseRange_algebraMap_pi`.

**Conventions that differ from the book.** Indices of the finite family of valuations in 11:7, 11:8 run over an
arbitrary finite type `ι` rather than $1,\dots,n$. In 11:2a the series is indexed from $0$, so the dominating term is
`a 0` and the hypothesis is $\lVert a_n\rVert < \lVert a_0\rVert$ for $n \ge 1$. "Series" means the limit of the
sequence of partial sums, as in the book.
-/
import QuadFormsKB.Citation
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Analysis.SpecificLimits.Normed

open Filter Topology

namespace QuadFormsKB.OMeara

variable {K : Type*} [Field K]

/-- Sufficiency half of 11:1: a valuation $|\ |$ on a field $F$ that is bounded on the natural integers
$1 + \cdots + 1$ of $F$ satisfies the strong triangle law (is non-archimedean). The proof is O'Meara's binomial
estimate $|a+b|^n \le (n+1)M \max(|a|,|b|)^n$ followed by $n \to \infty$. -/
theorem isNonarchimedean_of_natCast_le (v : AbsoluteValue K ℝ) (M : ℝ)
    (h : ∀ n : ℕ, v (n : K) ≤ M) : IsNonarchimedean v := by
  intro a b
  have hM : 0 ≤ M := by simpa using h 0
  by_contra hlt
  rw [not_le] at hlt
  set m := max (v a) (v b) with hm
  have hm0 : 0 ≤ m := le_trans (v.nonneg a) (le_max_left _ _)
  have hmpos : 0 < m := by
    rcases hm0.eq_or_lt with h0 | h0
    · exfalso
      have ha : v a = 0 := le_antisymm (h0 ▸ le_max_left _ _) (v.nonneg a)
      have hb : v b = 0 := le_antisymm (h0 ▸ le_max_right _ _) (v.nonneg b)
      have h1 := (AbsoluteValue.eq_zero v).1 ha
      have h2 := (AbsoluteValue.eq_zero v).1 hb
      rw [h1, h2, add_zero, map_zero] at hlt
      linarith
    · exact h0
  have key : ∀ n : ℕ, v (a + b) ^ n ≤ (n + 1) * M * m ^ n := by
    intro n
    rw [← map_pow, add_pow]
    refine (v.sum_le _ _).trans ?_
    calc ∑ k ∈ Finset.range (n + 1), v (a ^ k * b ^ (n - k) * (n.choose k : K))
        ≤ ∑ k ∈ Finset.range (n + 1), M * m ^ n := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
          rw [map_mul, map_mul, map_pow, map_pow]
          have h1 : v a ^ k ≤ m ^ k := pow_le_pow_left₀ (v.nonneg a) (le_max_left _ _) k
          have h2 : v b ^ (n - k) ≤ m ^ (n - k) :=
            pow_le_pow_left₀ (v.nonneg b) (le_max_right _ _) _
          have h3 := h (n.choose k)
          have : m ^ k * m ^ (n - k) = m ^ n := by rw [← pow_add]; congr 1; omega
          calc v a ^ k * v b ^ (n - k) * v (n.choose k : K)
              ≤ (m ^ k * m ^ (n - k)) * M := by
                gcongr
          _ = M * m ^ n := by rw [this]; ring
      _ = (n + 1) * M * m ^ n := by simp [Finset.sum_const]; ring
  set r := v (a + b) / m with hr
  have hr1 : 1 < r := by rw [hr, lt_div_iff₀ hmpos]; linarith
  have hkey : ∀ n : ℕ, r ^ n ≤ (n + 1) * M := by
    intro n
    have := key n
    rw [hr, div_pow, div_le_iff₀ (pow_pos hmpos n)]
    linarith
  have t1 := tendsto_pow_const_div_const_pow_of_one_lt 1 hr1
  have t2 : Tendsto (fun n : ℕ => (1 : ℝ) / r ^ n) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hr1)
    simpa [Function.comp_def] using this
  have t3 := (t1.add t2).mul_const M
  simp only [zero_add, zero_mul] at t3
  obtain ⟨n, hn⟩ := (t3.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).exists
  have hpos : 0 < r ^ n := pow_pos (by linarith) n
  have : ((n : ℝ) ^ 1 / r ^ n + 1 / r ^ n) * M < 1 := hn
  have h2 : (n + 1) * M < r ^ n := by
    have : ((n : ℝ) ^ 1 / r ^ n + 1 / r ^ n) * M = ((n + 1) * M) / r ^ n := by
      field_simp
    rw [this, div_lt_one hpos] at hn
    exact hn
  linarith [hkey n]


/-- **11:1.** A valuation $|\ |$ on a field $F$ is non-archimedean (satisfies
$|a+b| \le \max(|a|,|b|)$ for all $a, b \in F$) if and only if it is bounded on the natural integers
$1 + \cdots + 1 \in F$. Here a valuation is a Mathlib `AbsoluteValue F ℝ` and non-archimedean is `IsNonarchimedean`.
The forward direction uses Mathlib's `IsNonarchimedean.apply_natCast_le_one` (the bound is $1$). -/
@[kb "omeara1963" "§11B, 11:1, p. 4"]
theorem isNonarchimedean_iff_natCast_bounded (v : AbsoluteValue K ℝ) :
    IsNonarchimedean v ↔ ∃ M : ℝ, ∀ n : ℕ, v (n : K) ≤ M := by
  refine ⟨fun h => ⟨1, fun n => ?_⟩, fun ⟨M, hM⟩ => isNonarchimedean_of_natCast_le v M hM⟩
  exact h.apply_natCast_le_one (by simp) (map_one v)

/-- Principle of Domination for a function $f\colon G \to \mathbb R$ on an abelian group that is even
($f(-x) = f(x)$) and satisfies the strong triangle law: if $f(a_i) < f(a_0)$ for all $i \in s$ then
$f(a_0 + \sum_{i \in s} a_i) = f(a_0)$. This is the common core of `domination_sum` and `domination_tsum`. -/
theorem domination_sum_aux {G : Type*} [AddCommGroup G] (f : G → ℝ) (hna : IsNonarchimedean f)
    (f_neg : ∀ x, f (-x) = f x) {ι : Type*}
    (s : Finset ι) (a₀ : G) (a : ι → G) (h : ∀ i ∈ s, f (a i) < f a₀) :
    f (a₀ + ∑ i ∈ s, a i) = f a₀ := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have h1 : f (∑ i ∈ s, a i) < f a₀ := by
      refine lt_of_le_of_lt (hna.apply_sum_le_sup hs) ?_
      exact (Finset.sup'_lt_iff hs).2 h
    exact hna.add_eq_left_of_lt f_neg h1

/-- **11:2 (Principle of Domination).** In a non-archimedean valued field $F$ (a Mathlib `AbsoluteValue F ℝ` with
`IsNonarchimedean`), if $|a_i| < |a_0|$ for every $i$ in a finite index set $s$, then
$|a_0 + \sum_{i \in s} a_i| = |a_0|$. O'Meara writes $|\alpha_1 + \cdots + \alpha_r| = |\alpha_1|$ if
$|\alpha_\lambda| < |\alpha_1|$ for $\lambda > 1$. -/
@[kb "omeara1963" "§11B, 11:2 (Principle of Domination), p. 4"]
theorem domination_sum (v : AbsoluteValue K ℝ) (hna : IsNonarchimedean v) {ι : Type*}
    (s : Finset ι) (a₀ : K) (a : ι → K) (h : ∀ i ∈ s, v (a i) < v a₀) :
    v (a₀ + ∑ i ∈ s, a i) = v a₀ :=
  domination_sum_aux v hna (fun x => v.map_neg x) s a₀ a h

/-- **11:2a.** Let $F$ be a non-archimedean normed field (`NormedField` with `IsNonarchimedean (norm)`), and let
$\sum_n a_n$ be a convergent series with sum $S$ (the partial sums $\sum_{i<N} a_i$ tend to $S$). If
$\lVert a_n\rVert < \lVert a_0\rVert$ for all $n \ge 1$, then $\lVert S\rVert = \lVert a_0\rVert$.
(O'Meara indexes the series from $1$; here it starts at $0$.) -/
@[kb "omeara1963" "§11B, 11:2a, p. 5"]
theorem domination_tsum {K : Type*} [NormedField K] (hna : IsNonarchimedean (norm : K → ℝ))
    (a : ℕ → K) (S : K)
    (hS : Tendsto (fun N => ∑ i ∈ Finset.range N, a i) atTop (𝓝 S))
    (h : ∀ n, 1 ≤ n → ‖a n‖ < ‖a 0‖) : ‖S‖ = ‖a 0‖ := by
  have hn : ∀ N : ℕ, ‖∑ i ∈ Finset.range (N + 1), a i‖ = ‖a 0‖ := by
    intro N
    rw [Finset.sum_range_succ', add_comm]
    exact domination_sum_aux (norm : K → ℝ) hna (fun x => norm_neg x) (Finset.range N) (a 0)
      (fun i => a (i + 1)) (fun i _ => h (i + 1) (by omega))
  have h2 : Tendsto (fun N => ‖∑ i ∈ Finset.range (N + 1), a i‖) atTop (𝓝 ‖S‖) :=
    ((continuous_norm.tendsto S).comp (hS.comp (tendsto_add_atTop_nat 1)))
  simp only [hn] at h2
  exact (tendsto_nhds_unique h2 tendsto_const_nhds)


/-- **11:3.** Let $E/F$ be an algebraic extension of fields and let $|\ |$ be a valuation on $E$ whose restriction
to $F$ is trivial ($|x| = 1$ for $x \in F^\times$). Then $|\ |$ is trivial on $E$. The restriction to $F$ is
expressed through `algebraMap F E`. The proof is O'Meara's (a minimal polynomial of an element with $|\alpha| > 1$
contradicts the Principle of Domination); the strong triangle law is obtained from 11:1. -/
@[kb "omeara1963" "§11B, 11:3, p. 5"]
theorem eq_one_of_trivial_on_algebraic {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E] (v : AbsoluteValue E ℝ)
    (hF : ∀ x : F, x ≠ 0 → v (algebraMap F E x) = 1) : ∀ x : E, x ≠ 0 → v x = 1 := by
  have hle : ∀ x : F, v (algebraMap F E x) ≤ 1 := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · exact (hF x hx).le
  have hna : IsNonarchimedean v := by
    refine isNonarchimedean_of_natCast_le v 1 fun n => ?_
    have := hle (n : F)
    simpa using this
  -- key claim: no element has `1 < v α`
  have key : ∀ α : E, ¬ 1 < v α := by
    intro α hα
    have hint : IsIntegral F α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
    set p := minpoly F α with hp
    have hmon : p.Monic := minpoly.monic hint
    have hpos : 0 < p.natDegree := minpoly.natDegree_pos hint
    have hroot : Polynomial.aeval α p = 0 := minpoly.aeval F α
    set n := p.natDegree with hn
    have hsum : α ^ n = - ∑ i ∈ Finset.range n, algebraMap F E (p.coeff i) * α ^ i := by
      have h1 := hmon.as_sum
      rw [h1] at hroot
      simp only [map_add, map_pow, Polynomial.aeval_X, map_sum, map_mul, Polynomial.aeval_C] at hroot
      rw [eq_neg_iff_add_eq_zero]
      exact hroot
    have hne : (Finset.range n).Nonempty := ⟨0, Finset.mem_range.2 hpos⟩
    have hle2 : v (α ^ n) ≤ v α ^ (n - 1) := by
      rw [hsum, v.map_neg]
      refine (hna.apply_sum_le_sup hne).trans ?_
      refine Finset.sup'_le _ _ fun i hi => ?_
      rw [map_mul, map_pow]
      have hi' : i ≤ n - 1 := by have := Finset.mem_range.1 hi; omega
      calc v (algebraMap F E (p.coeff i)) * v α ^ i ≤ 1 * v α ^ i := by
            gcongr
            exact hle _
        _ = v α ^ i := one_mul _
        _ ≤ v α ^ (n - 1) := pow_le_pow_right₀ hα.le hi'
    rw [map_pow] at hle2
    have : v α ^ (n - 1) < v α ^ n := pow_lt_pow_right₀ hα (by omega)
    linarith
  intro x hx
  have h1 := key x
  have h2 := key x⁻¹
  rw [map_inv₀] at h2
  have hpos : 0 < v x := v.pos hx
  rw [not_lt] at h1 h2
  rw [inv_le_one_iff₀] at h2
  rcases h2 with h2 | h2
  · linarith
  · exact le_antisymm h1 h2


/-- Two valuations $|\ |_1$, $|\ |_2$ on the same field $K$ *define the same topology*: the identity map
$(K, |\ |_1) \to (K, |\ |_2)$ is a homeomorphism. This is O'Meara's definition of *equivalent valuations* (§11C),
via Mathlib's `WithAbs`, which carries the topology of $|\ |$ on $K$. Mathlib's own `AbsoluteValue.IsEquiv` is the
order-theoretic version; the two agree by `equivalent_valuations_tfae`. -/
@[kb "omeara1963" "§11C, definition of equivalent valuations, p. 5"]
def SameTopology (v w : AbsoluteValue K ℝ) : Prop :=
  IsHomeomorph (WithAbs.congr v w (RingEquiv.refl K))

/-- **11:4.** For two valuations $|\ |_1$, $|\ |_2$ on a field $K$ the following are equivalent:
(1) they define the same topology (`SameTopology`); (2) $|a|_1 < 1 \iff |a|_2 < 1$ for all $a \in K$;
(3) there is a real number $\varrho > 0$ with $|a|_1^{\varrho} = |a|_2$ for all $a \in K$.
Proved from Mathlib's `AbsoluteValue.isEquiv_iff_isHomeomorph`, `isEquiv_iff_lt_one_iff` and
`isEquiv_iff_exists_rpow_eq`. -/
@[kb "omeara1963" "§11C, 11:4, p. 5"]
theorem equivalent_valuations_tfae (v w : AbsoluteValue K ℝ) :
    List.TFAE [SameTopology v w, ∀ a : K, v a < 1 ↔ w a < 1,
      ∃ c : ℝ, 0 < c ∧ ∀ a : K, v a ^ c = w a] := by
  tfae_have 1 ↔ 2 := by
    rw [SameTopology, ← AbsoluteValue.isEquiv_iff_isHomeomorph, AbsoluteValue.isEquiv_iff_lt_one_iff]
  tfae_have 2 ↔ 3 := by
    rw [← AbsoluteValue.isEquiv_iff_lt_one_iff, AbsoluteValue.isEquiv_iff_exists_rpow_eq]
    constructor
    · rintro ⟨c, hc, h⟩; exact ⟨c, hc, fun a => congrFun h a⟩
    · rintro ⟨c, hc, h⟩; exact ⟨c, hc, funext h⟩
  tfae_finish

/-- **11:4b.** The trivial valuation ($|a| = 1$ for $a \ne 0$) of a field $K$ is equivalent to itself and to no
other valuation: a valuation equivalent (in Mathlib's sense `IsEquiv`, which is equivalent to O'Meara's by 11:4) to the
trivial one is the trivial one. -/
@[kb "omeara1963" "§11C, 11:4b, p. 6"]
theorem isEquiv_trivial_iff {K : Type*} [Field K] [DecidablePred fun x : K => x = 0]
    (v : AbsoluteValue K ℝ) : v.IsEquiv AbsoluteValue.trivial ↔ v = AbsoluteValue.trivial :=
  AbsoluteValue.isEquiv_trivial_iff_eq_trivial

/-- **11:5.** Let $|\ |_1$, $|\ |_2$ be two equivalent valuations on a field $E$ and $F$ a subfield of $E$. If the
two valuations induce the same non-trivial valuation on $F$ (agree on $F$, and are not trivial there), then
$|\ |_1 = |\ |_2$ on $E$. Non-triviality of the common valuation on $F$ is stated as the existence of
$x \in F$, $x \ne 0$, with $|x|_1 \ne 1$. -/
@[kb "omeara1963" "§11C, 11:5, p. 6"]
theorem eq_of_isEquiv_of_eq_on_subfield {E : Type*} [Field E] (v w : AbsoluteValue E ℝ)
    (h : v.IsEquiv w) (F : Subfield E) (hF : ∀ x ∈ F, v x = w x)
    (hnt : ∃ x ∈ F, x ≠ 0 ∧ v x ≠ 1) : v = w := by
  obtain ⟨c, hc, hvw⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 h
  obtain ⟨x, hxF, hx0, hx1⟩ := hnt
  have h1 : v x ^ c = v x := by
    have := congrFun hvw x
    rw [this]; exact (hF x hxF).symm
  have hpos : 0 < v x := v.pos hx0
  have hc1 : c = 1 := by
    have := congrArg Real.log h1
    rw [Real.log_rpow hpos] at this
    have hlog : Real.log (v x) ≠ 0 := by
      intro h0
      rcases Real.log_eq_zero.1 h0 with h | h | h <;> [linarith; exact hx1 h; linarith]
    have : (c - 1) * Real.log (v x) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hlog
  subst hc1
  ext a
  have := congrFun hvw a
  simpa using this

/-- **11:7.** Let $|\ |_i$ ($i$ in a finite index type) be finitely many non-trivial, pairwise inequivalent
valuations on a field $K$. Then for each $i$ there is $\alpha \in K$ with $|\alpha|_i > 1$ and $|\alpha|_j < 1$ for all
$j \ne i$. (O'Meara states it for $i = 1$; the index is arbitrary here.) Mathlib's
`AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv`. -/
@[kb "omeara1963" "§11E, 11:7, p. 8"]
theorem exists_one_lt_lt_one {ι : Type*} [Finite ι] (v : ι → AbsoluteValue K ℝ)
    (hnt : ∀ i, (v i).IsNontrivial) (hv : Pairwise fun i j => ¬(v i).IsEquiv (v j)) (i : ι) :
    ∃ a : K, 1 < v i a ∧ ∀ j, j ≠ i → v j a < 1 :=
  AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv hnt hv i

/-- **11:8 (Weak Approximation Theorem).** Let $|\ |_i$ ($i$ in a finite index type) be finitely many non-trivial,
pairwise inequivalent valuations on a field $K$, let $a_i \in K$ and $\varepsilon > 0$. Then there is
$\alpha \in K$ with $|\alpha - a_i|_i < \varepsilon$ for all $i$. Deduced from Mathlib's
`AbsoluteValue.denseRange_algebraMap_pi` (density of the diagonal embedding). -/
@[kb "omeara1963" "§11E, 11:8, p. 8"]
theorem weak_approximation {ι : Type*} [Finite ι] (v : ι → AbsoluteValue K ℝ)
    (hnt : ∀ i, (v i).IsNontrivial) (hv : Pairwise fun i j => ¬(v i).IsEquiv (v j))
    (a : ι → K) {ε : ℝ} (hε : 0 < ε) : ∃ x : K, ∀ i, v i (x - a i) < ε := by
  have := Fintype.ofFinite ι
  have hd := AbsoluteValue.denseRange_algebraMap_pi hnt hv
  obtain ⟨x, hx⟩ := Metric.denseRange_iff.1 hd (fun i => WithAbs.toAbs (v i) (a i)) ε hε
  refine ⟨x, fun i => ?_⟩
  have := (dist_pi_lt_iff hε).1 hx i
  simp only [dist_eq_norm, WithAbs.norm_eq_apply_ofAbs] at this
  have e : v i (a i - x) < ε := this
  rwa [AbsoluteValue.map_sub] at e

end QuadFormsKB.OMeara
