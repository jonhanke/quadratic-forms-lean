/-
# Rank one over $\mathbb Z$: the local densities of $\langle a\rangle$ and the failure of the Euler product

**Layer:** the unary form $\langle a\rangle$ = `RankOne.unary a` (`Siegel/RankOne.lean`), the local densities
$\beta_p(m)$ = `LocalDensity.localDensity` ($\lim_k r_{p^k}(m)/p^{k(n-1)}$, here $n - 1 = 0$, so $\beta_p(m)$ is the
eventual number of solutions of $a x_0^2 \equiv m \bmod p^k$), and the Euler factors / partial products of
`Siegel/LocalProduct.lean` (`eulerFactor`, `eulerPartialProd`, `IsEulerProductValue`).

**Proves (unconditionally; only Mathlib's Dirichlet theorem is used, for one prime $p \equiv 3 \bmod 4$)**
* `localDensity_unary_good`: $\beta_p(\langle a\rangle, m) = 1 + \left(\frac{am}{p}\right)$ for $p \nmid 2am$;
* `one_le_localDensity_unary`: $\beta_p(\langle a\rangle, ak^2) \ge 1$ for every prime $p$ ($k \ne 0$);
* `localDensity_unary_eq_zero`: $\beta_p(\langle a\rangle, m) = 0$ if $v_p(m) < v_p(a)$ or $v_p(m) - v_p(a)$ is odd;
* `tendsto_eulerPartialProd_atTop`, `not_isEulerProductValue`, `not_multipliable_eulerFactor`: for $m = ak^2 \ne 0$ the
  partial products $\prod_{p \le X}\beta_p(m)$ tend to $+\infty$;
* `exists_eulerFactor_eq_zero`, `hasProd_eulerFactor_zero`: for $m \ne ak^2$ some $\beta_p(m) = 0$, so the product is $0$;
* `siegel_rank_one_dichotomy`, `no_siegel_formula_rank_one` (the headline).

*Note:* the claim "the product diverges when $am$ is a square" is true only when $m/a$ is the square
of an **integer**. If $am$ is a square but $m/a \notin \mathbb Z^2$ (e.g. $a = 4$, $m = 1$), then $\beta_2(\langle 4\rangle, 1) = 0$
and the product is $0$, matching $r(1) = 0$. The divergent case is exactly the represented case $r(m) = 2$.
-/
import QuadFormsKB.Siegel.RankOne

open Matrix Filter Topology

namespace QuadFormsKB.Siegel.RankOne

open LocalDensity

/-! ### The local densities -/

/-- **The local density at a good prime** (Hanke 2004, Table 1, $n = 1$; Siegel 1935 [unverified]): for an odd prime
$p$ with $p \nmid a$ and $p \nmid m$,
$$\beta_p(\langle a\rangle, m) = \#\{x_0 \in \mathbb F_p : a x_0^2 = m\} = 1 + \left(\frac{am}{p}\right).$$ -/
@[kb "hanke2004" "Table 1, p. 363 (n = 1)"]
theorem localDensity_unary_good (a : ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (ha : ¬ (p : ℤ) ∣ a) (m : ℤ)
    (hm : ¬ (p : ℤ) ∣ m) : localDensity (unary a) p m = 1 + legendreSym p (a * m) := by
  rw [unary, localDensity_unit _ p hp (fun _ => ha) m hm]
  have h := ((card_diag_mod_p (fun _ : Fin 1 => a) p hp (fun _ => ha) le_rfl m hm).2 odd_one).2
  simp only [Finset.univ_unique, Finset.prod_singleton, pow_zero, one_mul, mul_one,
    Nat.sub_self, Nat.zero_div] at h
  simp only [Nat.sub_self, pow_zero, div_one]
  exact_mod_cast h

/-- For $a, m \ne 0$, $\beta_p(\langle a\rangle, m)$ is the number of solutions of $a x_0^2 \equiv m \bmod p^k$ for all large
$k$ (`LocalDensity.localDensity_eventually_eq`, with $p^{k(n-1)} = 1$). -/
theorem eventually_repCount_unary {a m : ℤ} (ha : a ≠ 0) (hm : m ≠ 0) (p : ℕ) [Fact p.Prime] :
    ∀ᶠ k in atTop, (repCount (unary a) p k m : ℝ) = localDensity (unary a) p m := by
  filter_upwards [localDensity_eventually_eq (unary a) (nondegenerate_unary ha) p m hm] with k hk
  simpa using hk

/-- **$\beta_p(\langle a\rangle, ak^2) \ge 1$ at every prime** ($a, k \ne 0$): $x_0 = k$ solves $a x_0^2 \equiv ak^2 \bmod p^K$
for every $K$, and $\beta_p$ is an eventual solution count. -/
theorem one_le_localDensity_unary {a k : ℤ} (ha : a ≠ 0) (hk : k ≠ 0) (p : ℕ) [hp : Fact p.Prime] :
    1 ≤ localDensity (unary a) p (a * k ^ 2) := by
  have hm : a * k ^ 2 ≠ 0 := mul_ne_zero ha (pow_ne_zero 2 hk)
  obtain ⟨K, hK⟩ := (eventually_repCount_unary ha hm p).exists
  rw [← hK]
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hne : Nonempty {x : Fin 1 → ZMod (p ^ K) //
      (unary a).evalIn (ZMod (p ^ K)) x = ((a * k ^ 2 : ℤ) : ZMod (p ^ K))} :=
    ⟨⟨fun _ => (k : ZMod (p ^ K)), by rw [evalIn_unary]; push_cast; ring⟩⟩
  have : 0 < repCount (unary a) p K (a * k ^ 2) := Nat.card_pos
  exact_mod_cast this

/-- If $p^K \mid u - m$ with $K > v_p(m)$ and $m \ne 0$, then $u \ne 0$ and $v_p(u) = v_p(m)$. -/
theorem padicValInt_eq_of_dvd_sub {p : ℕ} [Fact p.Prime] {u m : ℤ} (hm : m ≠ 0) {K : ℕ}
    (hK : padicValInt p m < K) (h : (p : ℤ) ^ K ∣ u - m) : u ≠ 0 ∧ padicValInt p u = padicValInt p m := by
  set e := padicValInt p m
  have hem : (p : ℤ) ^ e ∣ m := padicValInt_dvd m
  have he1 : ¬ (p : ℤ) ^ (e + 1) ∣ m := by
    rw [padicValInt_dvd_iff]; omega
  have hpK1 : (p : ℤ) ^ (e + 1) ∣ (p : ℤ) ^ K := pow_dvd_pow _ (by omega)
  have hpK : (p : ℤ) ^ e ∣ (p : ℤ) ^ K := pow_dvd_pow _ (by omega)
  have hu1 : ¬ (p : ℤ) ^ (e + 1) ∣ u := fun hu => he1 (by
    have := dvd_sub hu (hpK1.trans h); simpa using this)
  have hu0 : u ≠ 0 := by rintro rfl; exact hu1 (dvd_zero _)
  have hue : (p : ℤ) ^ e ∣ u := by
    have := dvd_add (hpK.trans h) hem; simpa using this
  refine ⟨hu0, ?_⟩
  rw [padicValInt_dvd_iff] at hue hu1
  push Not at hu1
  omega

/-- **The local obstruction** ($a, m \ne 0$): if $v_p(m) < v_p(a)$ or $v_p(m) - v_p(a)$ is odd, then $a x_0^2 \equiv m$ has
no solution modulo $p^K$ for $K > v_p(m)$ (a solution would give $v_p(m) = v_p(a) + 2v_p(x_0)$), so
$\beta_p(\langle a\rangle, m) = 0$. -/
theorem localDensity_unary_eq_zero {a m : ℤ} (ha : a ≠ 0) (hm : m ≠ 0) (p : ℕ) [hp : Fact p.Prime]
    (h : ¬ (padicValInt p a ≤ padicValInt p m ∧ Even (padicValInt p m - padicValInt p a))) :
    localDensity (unary a) p m = 0 := by
  have hzero : ∀ K, padicValInt p m < K → repCount (unary a) p K m = 0 := by
    intro K hK
    have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    rw [repCount, Nat.card_eq_zero]
    left
    refine ⟨fun ⟨x, hx⟩ => h ?_⟩
    rw [evalIn_unary] at hx
    set y : ℤ := ((x 0).val : ℤ)
    have hy : ((y : ℤ) : ZMod (p ^ K)) = x 0 := by simp [y]
    have hd : ((p : ℤ) ^ K) ∣ a * y ^ 2 - m := by
      have : (((a * y ^ 2 - m : ℤ)) : ZMod (p ^ K)) = 0 := by push_cast; rw [hy, hx]; ring
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ K)).mp this
      exact_mod_cast this
    obtain ⟨hu0, hv⟩ := padicValInt_eq_of_dvd_sub hm hK hd
    have hy0 : y ≠ 0 := by rintro h0; simp [h0] at hu0
    rw [pow_two, ← mul_assoc, padicValInt.mul (mul_ne_zero ha hy0) hy0, padicValInt.mul ha hy0] at hv
    exact ⟨by omega, ⟨padicValInt p y, by omega⟩⟩
  obtain ⟨K, hK1, hK2⟩ := ((eventually_repCount_unary ha hm p).and
    (eventually_gt_atTop (padicValInt p m))).exists
  rw [← hK1, hzero K hK2]; simp

/-! ### The Euler product -/

/-- **For $m = ak^2$, every Euler factor is $\ge 1$.** -/
theorem one_le_eulerFactor {a k : ℤ} (ha : a ≠ 0) (hk : k ≠ 0) (p : AWS.PrimeIdx) :
    1 ≤ eulerFactor (unary a) (a * k ^ 2) p := by
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  exact one_le_localDensity_unary ha hk p

/-- **For $m = ak^2$ and $p \nmid 2ak$, the Euler factor is $2$** ($\left(\frac{a\cdot ak^2}{p}\right) = \left(\frac{(ak)^2}{p}\right) = 1$). -/
theorem eulerFactor_eq_two {a k : ℤ} (p : AWS.PrimeIdx) (hp : ¬ ((p : ℕ) : ℤ) ∣ 2 * a * k) :
    eulerFactor (unary a) (a * k ^ 2) p = 2 := by
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  have hpZ : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp p.2
  have hp2 : (p : ℕ) ≠ 2 := by
    intro e; apply hp; rw [e, mul_assoc]; exact dvd_mul_right _ _
  have hpa : ¬ ((p : ℕ) : ℤ) ∣ a := fun h => hp ((h.mul_left 2).mul_right k)
  have hpk : ¬ ((p : ℕ) : ℤ) ∣ k := fun h => hp (h.mul_left _)
  have hpm : ¬ ((p : ℕ) : ℤ) ∣ a * k ^ 2 := by
    intro h
    rcases hpZ.dvd_or_dvd h with h | h
    · exact hpa h
    · exact hpk (hpZ.dvd_of_dvd_pow h)
  rw [eulerFactor, localDensity_unary_good a p hp2 hpa _ hpm,
    show a * (a * k ^ 2) = (a * k) ^ 2 by ring, legendreSym.sq_one']
  · norm_num
  · rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h
    rcases hpZ.dvd_or_dvd h with h | h
    · exact hpa h
    · exact hpk h

/-- $\prod_S f \le \prod_T f$ for $S \subseteq T$ when $f \ge 1$ on $T$. -/
theorem prod_le_prod_of_subset_of_one_le_real {ι : Type*} [DecidableEq ι] {S T : Finset ι} {f : ι → ℝ} (h : S ⊆ T)
    (hf : ∀ i ∈ T, 1 ≤ f i) : ∏ i ∈ S, f i ≤ ∏ i ∈ T, f i := by
  rw [← Finset.prod_sdiff h]
  have h1 : 1 ≤ ∏ i ∈ T \ S, f i := Finset.one_le_prod₀ fun i hi => hf i (Finset.sdiff_subset hi)
  have h0 : 0 ≤ ∏ i ∈ S, f i := Finset.prod_nonneg fun i hi => zero_le_one.trans (hf i (h hi))
  exact le_mul_of_one_le_left h0 h1

theorem mem_primesUpTo {X : ℕ} {p : AWS.PrimeIdx} : p ∈ primesUpTo X ↔ (p : ℕ) ≤ X := by
  simp only [primesUpTo, Finset.mem_subtype, Finset.mem_range]; omega

/-- **The partial products diverge when $m$ is represented** (Siegel 1935, $\varepsilon$ for $r = n$; Weil 1982, §3.7
[unverified]): for $a, k \ne 0$ and $m = ak^2$,
$$\prod_{p \le X}\beta_p(\langle a\rangle, m) \longrightarrow +\infty \qquad (X \to \infty),$$
since every factor is $\ge 1$ (`one_le_eulerFactor`) and infinitely many (all $p \nmid 2ak$) equal $2$
(`eulerFactor_eq_two`). -/
@[kb "siegel1935" "ε for r = n (rank one: divergence) [unverified]"]
theorem tendsto_eulerPartialProd_atTop {a k : ℤ} (ha : a ≠ 0) (hk : k ≠ 0) :
    Tendsto (eulerPartialProd (unary a) (a * k ^ 2)) atTop atTop := by
  have h1 := one_le_eulerFactor ha hk
  refine tendsto_atTop_atTop_of_monotone (fun X Y hXY => ?_) fun b => ?_
  · exact prod_le_prod_of_subset_of_one_le_real
      (fun p hp => mem_primesUpTo.mpr ((mem_primesUpTo.mp hp).trans hXY)) fun p _ => h1 p
  · -- the good primes form an infinite set
    have : Infinite AWS.PrimeIdx := Nat.infinite_setOfPred_prime.to_subtype
    have hG : {p : AWS.PrimeIdx | ¬ ((p : ℕ) : ℤ) ∣ 2 * a * k}.Infinite := by
      have hfin := finite_primes_dvd (N := 2 * a * k) (by simp [ha, hk])
      have := hfin.infinite_compl
      simpa [Set.compl_def] using this
    obtain ⟨N, hN⟩ := exists_nat_ge b
    obtain ⟨S, hSG, hScard⟩ := hG.exists_subset_card_eq N
    refine ⟨S.sup Subtype.val, ?_⟩
    have hsub : S ⊆ primesUpTo (S.sup Subtype.val) := fun p hp =>
      mem_primesUpTo.mpr (Finset.le_sup (f := Subtype.val) hp)
    have hS : ∏ p ∈ S, eulerFactor (unary a) (a * k ^ 2) p = 2 ^ N := by
      rw [Finset.prod_congr rfl fun p hp => eulerFactor_eq_two p (hSG hp), Finset.prod_const, hScard]
    have hN2 : (N : ℝ) ≤ 2 ^ N := by
      have := Nat.lt_two_pow_self (n := N)
      exact_mod_cast this.le
    calc b ≤ N := hN
      _ ≤ 2 ^ N := hN2
      _ = ∏ p ∈ S, eulerFactor (unary a) (a * k ^ 2) p := hS.symm
      _ ≤ eulerPartialProd (unary a) (a * k ^ 2) (S.sup Subtype.val) :=
        prod_le_prod_of_subset_of_one_le_real hsub fun p _ => h1 p

/-- **No value in the natural order:** for $m = ak^2 \ne 0$ there is no $P \in \mathbb R$ with $\prod_{p\le X}\beta_p(m) \to P$. -/
theorem not_isEulerProductValue {a k : ℤ} (ha : a ≠ 0) (hk : k ≠ 0) (P : ℝ) :
    ¬ IsEulerProductValue (unary a) (a * k ^ 2) P := fun h =>
  not_tendsto_nhds_of_tendsto_atTop (tendsto_eulerPartialProd_atTop ha hk) P h

/-- **Not unconditionally convergent:** for $m = ak^2 \ne 0$, $\prod_p\beta_p(m)$ is not `Multipliable`. -/
theorem not_multipliable_eulerFactor {a k : ℤ} (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ Multipliable (eulerFactor (unary a) (a * k ^ 2)) := fun h =>
  not_isEulerProductValue ha hk _ (isEulerProductValue_of_hasProd h.hasProd)

/-- **A vanishing Euler factor when $m$ is not represented** ($a, m \ne 0$, $m \ne ak^2$ for all $k \in \mathbb Z$): some
$\beta_p(\langle a\rangle, m) = 0$. *Proof:* if some $p$ has $v_p(m) < v_p(a)$ or $v_p(m) - v_p(a)$ odd, use
`localDensity_unary_eq_zero`. Otherwise $a \mid m$ and $m/a$ has even valuations, so $m/a = \pm r^2$; as $m \ne ar^2$,
$m = -ar^2$, and for a prime $p \equiv 3 \bmod 4$, $p > |a| + |m|$ (Dirichlet's theorem, Mathlib's
`Nat.forall_exists_prime_gt_and_eq_mod`), $\beta_p = 1 + \left(\frac{-(ar)^2}{p}\right) = 1 + \left(\frac{-1}{p}\right) = 0$. -/
theorem exists_eulerFactor_eq_zero {a m : ℤ} (ha : a ≠ 0) (hm : m ≠ 0) (h : ∀ k : ℤ, m ≠ a * k ^ 2) :
    ∃ p : AWS.PrimeIdx, eulerFactor (unary a) m p = 0 := by
  by_contra hall
  push Not at hall
  have hloc : ∀ p : ℕ, p.Prime →
      padicValInt p a ≤ padicValInt p m ∧ Even (padicValInt p m - padicValInt p a) := by
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    by_contra hc
    exact hall ⟨p, hp⟩ (localDensity_unary_eq_zero ha hm p hc)
  -- `a ∣ m`
  have hdvd : a ∣ m := by
    refine Int.natAbs_dvd_natAbs.mp ((Nat.factorization_le_iff_dvd (by simpa using ha)
      (by simpa using hm)).mp (Finsupp.le_def.mpr fun p => ?_))
    by_cases hp : p.Prime
    · rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
      exact (hloc p hp).1
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  obtain ⟨q, rfl⟩ := hdvd
  have hq : q ≠ 0 := by rintro rfl; simp at hm
  have hsq : IsSquare q.natAbs := by
    refine Nat.isSquare_iff_even_factorization.mpr fun p hp => ?_
    have : Fact p.Prime := ⟨hp⟩
    rw [Nat.factorization_def _ hp]
    have h2 := (hloc p hp).2
    rw [padicValInt.mul ha hq, Nat.add_sub_cancel_left] at h2
    exact h2
  obtain ⟨r, hr⟩ := hsq
  rcases Int.natAbs_eq q with hq' | hq'
  · exact h r (by rw [hq', hr]; push_cast; ring)
  · -- `m = -a r²`
    have hr0 : (r : ℤ) ≠ 0 := by
      rintro h0; apply hq; rw [hq', hr]; push_cast; simp [show (r : ℤ) = 0 from h0]
    have hm' : a * q = -1 * (r : ℤ) ^ 2 * a := by rw [hq', hr]; push_cast; ring
    obtain ⟨p, hpN, hp, hp4⟩ := Nat.forall_exists_prime_gt_and_eq_mod (q := 4) (a := (3 : ZMod 4))
      (by decide) (a.natAbs + (a * q).natAbs + 2)
    have : Fact p.Prime := ⟨hp⟩
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hndvd : ∀ t : ℤ, t ≠ 0 → t.natAbs < p → ¬ (p : ℤ) ∣ t := by
      intro t ht htp hd
      have := Nat.le_of_dvd (Int.natAbs_pos.mpr ht) (Int.natCast_dvd.mp hd)
      omega
    have hpa : ¬ (p : ℤ) ∣ a := hndvd a ha (by omega)
    have hpm : ¬ (p : ℤ) ∣ a * q := hndvd _ hm (by omega)
    have hpr : ¬ (p : ℤ) ∣ r := fun hd => hpm (by rw [hm']; exact (hd.pow two_ne_zero).mul_left _ |>.mul_right _)
    have hp2 : p ≠ 2 := by omega
    have hp43 : p % 4 = 3 := by
      have : ((p : ℕ) : ZMod 4) = ((3 : ℕ) : ZMod 4) := by simpa using hp4
      rw [ZMod.natCast_eq_natCast_iff'] at this
      simpa using this
    apply hall ⟨p, hp⟩
    rw [eulerFactor]
    change localDensity (unary a) p (a * q) = 0
    rw [localDensity_unary_good a p hp2 hpa _ hpm, hm',
      show a * (-1 * (r : ℤ) ^ 2 * a) = -1 * (a * r) ^ 2 by ring, legendreSym.mul,
      legendreSym.at_neg_one hp2, ZMod.χ₄_nat_three_mod_four hp43, legendreSym.sq_one']
    · norm_num
    · rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro hd
      rcases hpZ.dvd_or_dvd hd with hd | hd
      · exact hpa hd
      · exact hpr hd

/-- **The product is $0$ when a factor vanishes.** -/
theorem hasProd_eulerFactor_zero {a m : ℤ} (ha : a ≠ 0) (hm : m ≠ 0) (h : ∀ k : ℤ, m ≠ a * k ^ 2) :
    HasProd (eulerFactor (unary a) m) 0 := by
  obtain ⟨p, hp⟩ := exists_eulerFactor_eq_zero ha hm h
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop {p}] with s hs
  exact (Finset.prod_eq_zero (Finset.singleton_subset_iff.mp hs) hp).symm

/-- **Siegel's formula degenerates in rank one** (Siegel 1935, the factor $\varepsilon = \tfrac12$ for $r = n$; Weil 1982,
§3.7 [unverified]). For $a, m \in \mathbb Z \setminus \{0\}$, exactly one of:
1. $m = ak^2$ for some $k \in \mathbb Z$: then $r_{\langle a\rangle}(m) = 2$ and the partial Euler products
   $\prod_{p\le X}\beta_p(m)$ tend to $+\infty$;
2. $m \ne ak^2$ for all $k$: then $r_{\langle a\rangle}(m) = 0$, and $\prod_p\beta_p(m) = 0$ (unconditionally, and in the
   natural order), because some $\beta_p(m) = 0$.

So the Euler product is never a finite nonzero number: it is $+\infty$ exactly when $m$ is represented. -/
@[kb "siegel1935" "ε for r = n (rank one) [unverified]"]
theorem siegel_rank_one_dichotomy {a m : ℤ} (ha : a ≠ 0) (hm : m ≠ 0) :
    ((∃ k : ℤ, m = a * k ^ 2) ∧ repNum (unary a) m = 2 ∧
        Tendsto (eulerPartialProd (unary a) m) atTop atTop) ∨
      ((∀ k : ℤ, m ≠ a * k ^ 2) ∧ repNum (unary a) m = 0 ∧
        HasProd (eulerFactor (unary a) m) 0 ∧ IsEulerProductValue (unary a) m 0) := by
  by_cases h : ∃ k : ℤ, m = a * k ^ 2
  · obtain ⟨k, rfl⟩ := h
    have hk : k ≠ 0 := by rintro rfl; simp at hm
    exact Or.inl ⟨⟨k, rfl⟩, repNum_unary_of_eq ha hk, tendsto_eulerPartialProd_atTop ha hk⟩
  · push Not at h
    have hP := hasProd_eulerFactor_zero ha hm h
    exact Or.inr ⟨h, repNum_unary_eq_zero h, hP, isEulerProductValue_of_hasProd hP⟩

/-- **No Euler-product Siegel formula in rank one:** for $a, k \ne 0$ and $m = ak^2$, the genus average is
$a_E(m) = r_{\langle a\rangle}(m) = 2 > 0$, while $\prod_p\beta_p(m)$ has no value, neither in the natural order
(`IsEulerProductValue`) nor unconditionally (`Multipliable`). So no identity $a_E(m) = c\,\beta_\infty(m)\prod_p\beta_p(m)$
with a real constant $c$ can hold. (Siegel's general theorem needs $n \ge 2$; in rank one $SO_1$ is trivial and the
mass $\tfrac12$ is the whole content, `mass_unary`.) -/
@[kb "weil1982" "§3.7 (rank one excluded) [unverified]"]
theorem no_siegel_formula_rank_one {a k : ℤ} (ha : a ≠ 0) (hk : k ≠ 0) :
    genusRepAvg (unary a) (a * k ^ 2) = 2 ∧ (∀ P : ℝ, ¬ IsEulerProductValue (unary a) (a * k ^ 2) P) ∧
      ¬ Multipliable (eulerFactor (unary a) (a * k ^ 2)) := by
  refine ⟨?_, not_isEulerProductValue ha hk, not_multipliable_eulerFactor ha hk⟩
  rw [genusRepAvg_unary, repNum_unary_of_eq ha hk]; norm_num

end QuadFormsKB.Siegel.RankOne
