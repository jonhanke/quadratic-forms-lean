/-
# O'Meara §22C: generating fractional ideals (22:5, 22:5a, 22:5c, 22:9)

**Setting.** As in `Sec22.lean`: $\mathfrak o$ a Dedekind domain (`IsDedekindDomain R`) with fraction field $F$
(`IsFractionRing R K`); fractional ideals are Mathlib's `FractionalIdeal R⁰ K` (O'Meara's fractional ideals are the
non-zero ones), $\alpha\mathfrak a$ is `spanSingleton R⁰ α * a`, $\mathfrak a + \mathfrak b$ is `a + b` (the supremum),
$\mathfrak o$ is `1`, and $\mathfrak a$ is integral when `a ≤ 1`.

**Proves** `exists_eq_smul_add_smul` (**22:5**), `exists_eq_span_pair` (**22:5a**), `exists_coprime_in_class`
(**22:5c**), `exists_smul_mul_add_smul_mul_eq` (**22:9**). `Lattices.Steinitz.exists_spanSingleton_mul_add_eq_one` is the
special case $\mathfrak c = \mathfrak o$ of 22:5 used for Steinitz classes.
-/
import QuadFormsKB.Citation
import QuadFormsKB.Literature.OMeara.Sec22
import QuadFormsKB.Literature.OMeara.Sec21

open IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors

namespace QuadFormsKB.OMeara

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]


open WithZero Multiplicative in
/-- Approximation in count language: given a finite set `T` of primes outside which `count a = g`, there is a
nonzero `α` with `count (α a) = g` on `T` and `≥ g` everywhere (from 21:2a). -/
theorem exists_approx_count {a : FractionalIdeal R⁰ K} (ha : a ≠ 0) (T : Finset (HeightOneSpectrum R))
    (g : HeightOneSpectrum R → ℤ) (hT : ∀ v ∉ T, count K v a = g v) :
    ∃ α : K, α ≠ 0 ∧ (∀ v ∈ T, count K v (spanSingleton R⁰ α * a) = g v) ∧
      ∀ v, g v ≤ count K v (spanSingleton R⁰ α * a) := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | hne
  · refine ⟨1, one_ne_zero, by simp, fun v => ?_⟩
    simp [hT v (Finset.notMem_empty v)]
  obtain ⟨A, hA1, hA2⟩ := exists_valuation_eq_le K T (fun v => exp (count K v a - g v))
    (fun v => exp_ne_zero) (fun v hv => by rw [hT v hv]; simp)
  obtain ⟨v₀, hv₀⟩ := hne
  have hA0 : A ≠ 0 := by
    rintro rfl
    have := hA1 v₀ hv₀
    simp at this
    exact exp_ne_zero this.symm
  have key : ∀ v, v.valuation K A = exp (-count K v (spanSingleton R⁰ A)) :=
    fun v => valuation_eq_exp_neg_count v hA0
  have hc : ∀ v, count K v (spanSingleton R⁰ A * a) = count K v (spanSingleton R⁰ A) + count K v a :=
    fun v => count_mul K v (spanSingleton_ne_zero' hA0) ha
  refine ⟨A, hA0, fun v hv => ?_, fun v => ?_⟩
  · have := hA1 v hv
    rw [key, exp_inj] at this
    rw [hc]; omega
  · have := hA2 v
    rw [key, exp_le_exp] at this
    rw [hc]; omega

theorem finite_count_ne {I J : FractionalIdeal R⁰ K} :
    {v : HeightOneSpectrum R | count K v I ≠ count K v J}.Finite := by
  have h1 := Filter.eventually_cofinite.1 (finite_factors (K := K) I)
  have h2 := Filter.eventually_cofinite.1 (finite_factors (K := K) J)
  refine (h1.union h2).subset fun v hv => ?_
  by_contra h
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
  exact hv (by rw [h.1, h.2])

/-- **22:5.** Let $\mathfrak a, \mathfrak b, \mathfrak c$ be fractional ideals. Then there are non-zero
$\alpha, \beta \in F$ with $\mathfrak c = \alpha\mathfrak a + \beta\mathfrak b$; in fact $\beta$ can be any non-zero
element with $\beta\mathfrak b \subseteq \mathfrak c$. -/
@[kb "omeara1963" "§22C, 22:5, p. 48"]
theorem exists_eq_smul_add_smul {a b c : FractionalIdeal R⁰ K} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    {β : K} (hβ : β ≠ 0) (hβb : spanSingleton R⁰ β * b ≤ c) :
    ∃ α : K, α ≠ 0 ∧ c = spanSingleton R⁰ α * a + spanSingleton R⁰ β * b := by
  classical
  have hβ' : spanSingleton R⁰ β * b ≠ 0 := mul_ne_zero (spanSingleton_ne_zero' hβ) hb
  set T : Finset (HeightOneSpectrum R) :=
    (finite_count_ne (K := K) (I := a) (J := c)).toFinset ∪
      (finite_count_ne (K := K) (I := spanSingleton R⁰ β * b) (J := c)).toFinset with hT
  obtain ⟨α, hα, hαT, hαge⟩ := exists_approx_count (K := K) ha T (fun v => count K v c) (by
    intro v hv
    by_contra h
    exact hv (by rw [hT]; simp [Set.Finite.mem_toFinset, h]))
  have hαa : spanSingleton R⁰ α * a ≠ 0 := mul_ne_zero (spanSingleton_ne_zero' hα) ha
  have hle := (le_iff_forall_count K hβ' hc).1 (hβb.trans le_rfl)
  refine ⟨α, hα, ?_⟩
  rw [← sup_eq_add]
  refine eq_of_forall_count_eq K hc (sup_ne_zero' hαa) fun v => ?_
  rw [count_sup hαa hβ']
  by_cases hv : v ∈ T
  · rw [hαT v hv]
    have := hle v
    omega
  · have h2 : count K v (spanSingleton R⁰ β * b) = count K v c := by
      by_contra h
      exact hv (by rw [hT]; simp [Set.Finite.mem_toFinset, h])
    have := hαge v
    omega

/-- **22:5a (Corollary).** Every fractional ideal is of the form $\alpha\mathfrak o + \beta\mathfrak o$ with
$\alpha, \beta \in F$. -/
@[kb "omeara1963" "§22C, 22:5a, p. 48"]
theorem exists_eq_span_pair (a : FractionalIdeal R⁰ K) :
    ∃ α β : K, a = spanSingleton R⁰ α + spanSingleton R⁰ β := by
  by_cases h0 : a = 0
  · exact ⟨0, 0, by simp [h0]⟩
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ a, x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply h0
    ext y
    simp only [mem_zero_iff]
    exact ⟨fun hy => hcon y hy, fun hy => hy ▸ zero_mem a⟩
  obtain ⟨α, hα, h⟩ := exists_eq_smul_add_smul (one_ne_zero (α := FractionalIdeal R⁰ K)) one_ne_zero h0
    hx0 (by rw [mul_one, spanSingleton_le_iff_mem]; exact hx)
  exact ⟨α, x, by rw [h, mul_one, mul_one]⟩

/-- **22:5c (Corollary).** Let $\mathfrak a$ be a fractional ideal and $\mathfrak b$ an integral ideal. Then there is
an integral ideal $\mathfrak a' = \gamma\mathfrak a$ ($\gamma \ne 0$) in the ideal class of $\mathfrak a$ which is
relatively prime to $\mathfrak b$: $\mathfrak a' + \mathfrak b = \mathfrak o$. -/
@[kb "omeara1963" "§22C, 22:5c, p. 48"]
theorem exists_coprime_in_class {a b : FractionalIdeal R⁰ K} (ha : a ≠ 0) (hb : b ≠ 0) (hb1 : b ≤ 1) :
    ∃ γ : K, γ ≠ 0 ∧ spanSingleton R⁰ γ * a ≤ 1 ∧ spanSingleton R⁰ γ * a + b = 1 := by
  classical
  set T : Finset (HeightOneSpectrum R) :=
    (finite_count_ne (K := K) (I := a) (J := 1)).toFinset ∪
      (finite_count_ne (K := K) (I := b) (J := 1)).toFinset with hT
  obtain ⟨α, hα, hαT, hαge⟩ := exists_approx_count (K := K) ha T (fun _ => 0) (by
    intro v hv
    by_contra h
    exact hv (by rw [hT]; simp [Set.Finite.mem_toFinset, count_one, h]))
  have hαa : spanSingleton R⁰ α * a ≠ 0 := mul_ne_zero (spanSingleton_ne_zero' hα) ha
  have hb0 := (le_iff_forall_count K hb one_ne_zero).1 hb1
  refine ⟨α, hα, ?_, ?_⟩
  · rw [le_iff_forall_count K hαa one_ne_zero]
    intro v; have := hαge v; rw [count_one]; exact this
  · rw [← sup_eq_add]
    refine eq_of_forall_count_eq K (sup_ne_zero' hαa) one_ne_zero fun v => ?_
    rw [count_sup hαa hb, count_one]
    by_cases hv : v ∈ T
    · have := hαT v hv
      have := hb0 v
      rw [count_one] at this
      omega
    · have h2 : count K v b = 0 := by
        by_contra h
        exact hv (by rw [hT]; simp [Set.Finite.mem_toFinset, count_one, h])
      have := hαge v
      omega

/-- **22:9 (Example).** Given fractional ideals $\mathfrak a, \mathfrak b, \mathfrak r_1, \mathfrak r_2$ there are
non-zero $\alpha, \beta \in F$ with $\alpha\mathfrak a\mathfrak r_1 + \beta\mathfrak b\mathfrak r_2 = \mathfrak r_1 + \mathfrak r_2$.

The displayed formula is lost in the machine-read text of the book; it is reconstructed from the proof, which reduces
to the case $\mathfrak r_1 + \mathfrak r_2 = \mathfrak o$ (replace $\mathfrak r_i$ by
$\mathfrak r_i(\mathfrak r_1 + \mathfrak r_2)^{-1}$) and then finds $\alpha, \beta$ with $\alpha\mathfrak a +
\beta\mathfrak b = \mathfrak o$ and $\alpha\mathfrak a\mathfrak r_1 + \beta\mathfrak b\mathfrak r_2 = \mathfrak o$. -/
@[kb "omeara1963" "§22C, 22:9, p. 50"]
theorem exists_smul_mul_add_smul_mul_eq {a b r₁ r₂ : FractionalIdeal R⁰ K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0) :
    ∃ α β : K, α ≠ 0 ∧ β ≠ 0 ∧
      spanSingleton R⁰ α * a * r₁ + spanSingleton R⁰ β * b * r₂ = r₁ + r₂ := by
  classical
  set D : Finset (HeightOneSpectrum R) :=
    (finite_count_ne (K := K) (I := a) (J := 1)).toFinset ∪
      (finite_count_ne (K := K) (I := b) (J := 1)).toFinset ∪
      (finite_count_ne (K := K) (I := r₁) (J := r₂)).toFinset with hD
  have hDa : ∀ v ∉ D, count K v a = 0 := by
    intro v hv; by_contra h
    exact hv (by rw [hD]; simp [Set.Finite.mem_toFinset, count_one, h])
  have hDb : ∀ v ∉ D, count K v b = 0 := by
    intro v hv; by_contra h
    exact hv (by rw [hD]; simp [Set.Finite.mem_toFinset, count_one, h])
  have hDr : ∀ v ∉ D, count K v r₁ = count K v r₂ := by
    intro v hv; by_contra h
    exact hv (by rw [hD]; simp [Set.Finite.mem_toFinset, count_one, h])
  obtain ⟨α, hα, hαD, hαge⟩ := exists_approx_count (K := K) ha D (fun _ => 0) hDa
  have hαa : spanSingleton R⁰ α * a ≠ 0 := mul_ne_zero (spanSingleton_ne_zero' hα) ha
  set E : Finset (HeightOneSpectrum R) :=
    D ∪ (finite_count_ne (K := K) (I := spanSingleton R⁰ α * a) (J := 1)).toFinset with hE
  obtain ⟨β, hβ, hβE, hβge⟩ := exists_approx_count (K := K) hb E (fun _ => 0) (by
    intro v hv
    exact hDb v (fun h => hv (by rw [hE]; exact Finset.mem_union_left _ h)))
  have hβb : spanSingleton R⁰ β * b ≠ 0 := mul_ne_zero (spanSingleton_ne_zero' hβ) hb
  refine ⟨α, β, hα, hβ, ?_⟩
  have h1 : spanSingleton R⁰ α * a * r₁ ≠ 0 := mul_ne_zero hαa hr₁
  have h2 : spanSingleton R⁰ β * b * r₂ ≠ 0 := mul_ne_zero hβb hr₂
  rw [← sup_eq_add, ← sup_eq_add]
  refine eq_of_forall_count_eq K (sup_ne_zero' h1) (sup_ne_zero' hr₁) fun v => ?_
  rw [count_sup h1 h2, count_sup hr₁ hr₂, count_mul K v hαa hr₁, count_mul K v hβb hr₂]
  have a1 := hαge v
  have b1 := hβge v
  have a2 : v ∈ D → count K v (spanSingleton R⁰ α * a) = 0 := fun h => hαD v h
  have b2 : v ∈ E → count K v (spanSingleton R⁰ β * b) = 0 := fun h => hβE v h
  have c1 : count K v r₁ ≠ count K v r₂ → count K v (spanSingleton R⁰ α * a) = 0 ∧
      count K v (spanSingleton R⁰ β * b) = 0 := by
    intro h
    have hvD : v ∈ D := by
      by_contra hv; exact h (hDr v hv)
    exact ⟨a2 hvD, b2 (by rw [hE]; exact Finset.mem_union_left _ hvD)⟩
  have c2 : count K v (spanSingleton R⁰ α * a) ≠ 0 → count K v (spanSingleton R⁰ β * b) = 0 := by
    intro h
    apply b2
    rw [hE]
    apply Finset.mem_union_right
    simp [Set.Finite.mem_toFinset, count_one, h]
  omega

end QuadFormsKB.OMeara
