/-
# O'Meara §22: ideal theory of a Dedekind domain

**Setting.** $\mathfrak o$ is a Dedekind domain (`IsDedekindDomain R`), $F$ its field of fractions (`IsFractionRing R K`),
the "spots" of O'Meara's Dedekind set $S$ are the height-one primes $\mathfrak p$ of $\mathfrak o$
(`IsDedekindDomain.HeightOneSpectrum R`), with discrete valuation $|\cdot|_{\mathfrak p}$ = `v.valuation K` (values in
$\mathbb Z_{m0}$, $|\pi|_{\mathfrak p} = e^{-1}$ for a uniformizer; O'Meara's normalization is a choice of base).
Fractional ideals are Mathlib's `FractionalIdeal R⁰ K`; O'Meara's $\mathfrak a + \mathfrak b$ is `⊔` and
$\mathfrak a \cap \mathfrak b$ is `⊓`; $\operatorname{ord}_{\mathfrak p}$ is `FractionalIdeal.count K v`.
The book works with an abstract Dedekind set $S$ of spots on a field (axioms D1-D3, see `Sec21.lean`); a Dedekind domain
$\mathfrak o$ is the same as $\mathfrak o(S)$ with $S$ = its height-one primes (22:10, `Sec23.lean`), so the statements
below are O'Meara's, read in the language of $\mathfrak o$. No restriction to number fields is made.

**Proves** (item by item)
* 22:1 (1), (2): ideal membership and inclusion are decided by the values $|\mathfrak a|_{\mathfrak p}$ (`idealAbs`),
  and the maximum $\max_{\alpha\in\mathfrak a}|\alpha|_{\mathfrak p}$ is attained (`isGreatest_valuation_image`);
* 22:2: local ideals glue (`exists_fractionalIdeal_of_local`);
* 22:3: the eight lattice identities for $+$, $\cap$, product and powers;
* 22:4: $(\mathfrak a + \mathfrak b)^{-1} = \mathfrak a^{-1}\cap\mathfrak b^{-1}$ and dually;
* 22:5b: fractional ideals are finitely generated modules;
* 22:6: prime = indecomposable = maximal = $\mathfrak o \cap \mathfrak m(\mathfrak p)$ (`tfae_prime_indecomposable_maximal`);
* 22:7: unique factorization with the primes as a free base;
* 22:8: the order $\operatorname{ord}_{\mathfrak p}$, additivity and $|\mathfrak a|_{\mathfrak p} = |\pi|^{\operatorname{ord}}$.

*Proof notes.* The bridge is `le_iff_forall_count`: for nonzero fractional ideals $\mathfrak a\subseteq\mathfrak b$ iff
$\operatorname{ord}_{\mathfrak p}\mathfrak b \le \operatorname{ord}_{\mathfrak p}\mathfrak a$ for all $\mathfrak p$ (Mathlib has only the forward
direction `count_mono`; the converse uses the factorization $\prod\mathfrak p^{\operatorname{ord}}$). Then $\operatorname{ord}$ of
$\sqcup$/$\sqcap$ is min/max (`count_sup`, `count_inf`) and all identities of 22:3-22:4 are identities in
$\mathbb Z$. The maximum of $|\alpha|_{\mathfrak p}$ over $\mathfrak a$ is shown attained by comparing $\mathfrak a$ with
$\mathfrak a\mathfrak p$ (`exists_mem_valuation_eq`), in place of O'Meara's appeal to the Strong Approximation Theorem.
-/
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import QuadFormsKB.Citation

set_option linter.unusedSectionVars false

open IsDedekindDomain FractionalIdeal WithZero Multiplicative
open scoped nonZeroDivisors

noncomputable section

namespace QuadFormsKB.OMeara

section Core
variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem le_iff_forall_count {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I ≤ J ↔ ∀ v : HeightOneSpectrum R, count K v J ≤ count K v I := by
  refine ⟨fun h v => count_mono K v hI h, fun h => ?_⟩
  have hM : I * J⁻¹ ≠ 0 := mul_ne_zero hI (inv_ne_zero hJ)
  have hle : I * J⁻¹ ≤ 1 := by
    rw [← finprod_heightOneSpectrum_factorization' (K := K) hM]
    refine finprod_induction (· ≤ 1) le_rfl (fun x y hx hy => ?_) (fun v => ?_)
    · calc x * y ≤ 1 * 1 := mul_le_mul' hx hy
        _ = 1 := one_mul 1
    · have hn : 0 ≤ count K v (I * J⁻¹) := by
        rw [count_mul K v hI (inv_ne_zero hJ), count_inv]; linarith [h v]
      lift count K v (I * J⁻¹) to ℕ using hn with n hn'
      rw [zpow_natCast]
      exact Right.pow_le_one_of_le coeIdeal_le_one
  calc I = (I * J⁻¹) * J := by rw [mul_assoc, inv_mul_cancel₀ hJ, mul_one]
    _ ≤ 1 * J := mul_le_mul_left hle J
    _ = J := one_mul J

theorem eq_of_forall_count_eq {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, count K v I = count K v J) : I = J :=
  le_antisymm ((le_iff_forall_count K hI hJ).2 fun v => (h v).ge)
    ((le_iff_forall_count K hJ hI).2 fun v => (h v).le)


variable {K}

theorem spanSingleton_ne_zero' {x : K} (hx : x ≠ 0) : spanSingleton R⁰ x ≠ 0 :=
  (spanSingleton_ne_zero_iff).2 hx

/-- The order of a nonzero field element at `v` equals minus the exponent of `v` in the principal
ideal it generates. -/
theorem valuation_eq_exp_neg_count (v : HeightOneSpectrum R) {x : K} (hx : x ≠ 0) :
    v.valuation K x = exp (-count K v (spanSingleton R⁰ x)) := by
  obtain ⟨⟨n, d, hd⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors R) x
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hd' : algebraMap R K d ≠ 0 := by simpa using hd0
  have hxe : x = algebraMap R K n * (algebraMap R K d)⁻¹ := by
    field_simp
    simpa using hnd
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hnd
    rcases hnd with h | h
    · exact hx h
    · exact hd0 h
  have hmk : x = IsLocalization.mk' K n ⟨d, hd⟩ := by
    rw [IsLocalization.eq_mk'_iff_mul_eq]; simpa using hnd
  have hspan : spanSingleton R⁰ x = ((Ideal.span {d} : Ideal R) : FractionalIdeal R⁰ K)⁻¹ *
      ((Ideal.span {n} : Ideal R) : FractionalIdeal R⁰ K) := by
    rw [hxe, map_mul, ← spanSingleton_inv, coeIdeal_span_singleton,
      coeIdeal_span_singleton, mul_comm]
  have hdI : ((Ideal.span {d} : Ideal R) : FractionalIdeal R⁰ K) ≠ 0 := by
    rw [coeIdeal_ne_zero]; simpa using hd0
  have hnI : ((Ideal.span {n} : Ideal R) : FractionalIdeal R⁰ K) ≠ 0 := by
    rw [coeIdeal_ne_zero]; simpa using hn
  have hdI' : (Ideal.span {d} : Ideal R) ≠ 0 := by simpa using hd0
  have hnI' : (Ideal.span {n} : Ideal R) ≠ 0 := by simpa using hn
  rw [hspan, count_mul K v (inv_ne_zero hdI) hnI, count_inv, count_coe K v hdI',
    count_coe K v hnI', hmk, HeightOneSpectrum.valuation_of_mk', v.intValuation_if_neg hn,
    v.intValuation_if_neg hd0]
  simp only [div_eq_mul_inv, ← exp_neg, ← exp_add]
  congr 1
  ring


theorem exists_ideal_with_count (e : HeightOneSpectrum R → ℤ)
    (he : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, e v = 0) :
    ∃ I : FractionalIdeal R⁰ K, I ≠ 0 ∧ ∀ v, count K v I = e v := by
  refine ⟨∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ e v, ?_,
    fun v => count_finprod K v e he⟩
  refine finprod_induction (· ≠ 0) one_ne_zero (fun x y hx hy => mul_ne_zero hx hy) (fun v => ?_)
  exact zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)

/-- The absolute value `|𝔞|_𝔭` of a fractional ideal at `𝔭` (O'Meara 22B: maximum of `|α|_𝔭` over `𝔞`),
written as `exp(-ord_𝔭 𝔞)`; see `exists_mem_valuation_eq` for the maximum. -/
def idealAbs (v : HeightOneSpectrum R) (I : FractionalIdeal R⁰ K) : ℤᵐ⁰ := exp (-count K v I)

theorem mem_iff_valuation_le {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (x : K) :
    x ∈ I ↔ ∀ v : HeightOneSpectrum R, v.valuation K x ≤ idealAbs v I := by
  by_cases hx : x = 0
  · subst hx; simp [FractionalIdeal.zero_mem]
  rw [← spanSingleton_le_iff_mem, le_iff_forall_count K (spanSingleton_ne_zero' hx) hI]
  refine forall_congr' fun v => ?_
  rw [valuation_eq_exp_neg_count v hx, idealAbs, exp_le_exp, neg_le_neg_iff]

theorem valuation_le_idealAbs {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) {x : K} (hx : x ∈ I)
    (v : HeightOneSpectrum R) : v.valuation K x ≤ idealAbs v I :=
  (mem_iff_valuation_le hI x).1 hx v

theorem exists_mem_valuation_eq {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (v : HeightOneSpectrum R) :
    ∃ a ∈ I, v.valuation K a = idealAbs v I := by
  classical
  by_contra hcon
  push Not at hcon
  have hv0 : (v.asIdeal : FractionalIdeal R⁰ K) ≠ 0 := coeIdeal_ne_zero.mpr v.ne_bot
  have hJ : I * (v.asIdeal : FractionalIdeal R⁰ K) ≠ 0 := mul_ne_zero hI hv0
  have hJI : I * (v.asIdeal : FractionalIdeal R⁰ K) ≤ I :=
    calc _ ≤ I * 1 := mul_le_mul_right coeIdeal_le_one I
      _ = I := mul_one I
  have hcnt : ∀ w, count K w (I * (v.asIdeal : FractionalIdeal R⁰ K)) =
      count K w I + if v = w then 1 else 0 := by
    intro w
    rw [count_mul K w hI hv0, count_maximal K w v]
  have hIJ : I ≤ I * (v.asIdeal : FractionalIdeal R⁰ K) := by
    intro a ha
    by_cases ha0 : a = 0
    · subst ha0; exact FractionalIdeal.zero_mem _
    rw [← spanSingleton_le_iff_mem, le_iff_forall_count K (spanSingleton_ne_zero' ha0) hJ]
    intro w
    have h1 : count K w I ≤ count K w (spanSingleton R⁰ a) := by
      have := count_mono K w (spanSingleton_ne_zero' ha0) ((spanSingleton_le_iff_mem).2 ha)
      exact this
    rw [hcnt w]
    by_cases hw : v = w
    · subst hw
      simp only [ite_true]
      have hlt : v.valuation K a < idealAbs v I :=
        lt_of_le_of_ne (valuation_le_idealAbs hI ha v) (hcon a ha)
      rw [valuation_eq_exp_neg_count v ha0, idealAbs, exp_lt_exp, neg_lt_neg_iff] at hlt
      omega
    · simp only [hw, ite_false, add_zero]; exact h1
  have heq := le_antisymm hIJ hJI
  have h2 := hcnt v
  rw [← heq] at h2
  simp at h2


theorem inf_ne_zero' {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) : I ⊓ J ≠ 0 := by
  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_mem_isInteger hI
  obtain ⟨b, hb0, hb⟩ := exists_ne_zero_mem_isInteger hJ
  intro h
  have hx : algebraMap R K a * algebraMap R K b ∈ I ⊓ J := by
    refine ⟨?_, ?_⟩
    · have := I.val.smul_mem b ha
      simpa [Algebra.smul_def, mul_comm] using this
    · have := J.val.smul_mem a hb
      simpa [Algebra.smul_def] using this
  rw [h] at hx
  have := (FractionalIdeal.mem_zero_iff R⁰).1 hx
  rcases mul_eq_zero.1 this with h1 | h1
  · exact ha0 ((map_eq_zero_iff _ (IsFractionRing.injective R K)).1 h1)
  · exact hb0 ((map_eq_zero_iff _ (IsFractionRing.injective R K)).1 h1)

theorem sup_ne_zero' {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) : I ⊔ J ≠ 0 := fun h =>
  hI (FractionalIdeal.le_zero_iff.mp (h ▸ le_sup_left))

theorem count_sup {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) (v : HeightOneSpectrum R) :
    count K v (I ⊔ J) = min (count K v I) (count K v J) := by
  have hS := sup_ne_zero' (J := J) hI
  obtain ⟨c, hc0, hc⟩ := exists_ideal_with_count (K := K)
    (fun w => min (count K w I) (count K w J))
    (by filter_upwards [finite_factors I, finite_factors J] with w h1 h2 using by simp [h1, h2])
  have hIc : I ≤ c := (le_iff_forall_count K hI hc0).2 fun w => by rw [hc]; exact min_le_left _ _
  have hJc : J ≤ c := (le_iff_forall_count K hJ hc0).2 fun w => by rw [hc]; exact min_le_right _ _
  apply le_antisymm
  · exact le_min (count_mono K v hI le_sup_left) (count_mono K v hJ le_sup_right)
  · have := count_mono K v hS (sup_le hIc hJc)
    rwa [hc] at this

theorem count_inf {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) (v : HeightOneSpectrum R) :
    count K v (I ⊓ J) = max (count K v I) (count K v J) := by
  have hS := inf_ne_zero' hI hJ
  obtain ⟨c, hc0, hc⟩ := exists_ideal_with_count (K := K)
    (fun w => max (count K w I) (count K w J))
    (by filter_upwards [finite_factors I, finite_factors J] with w h1 h2 using by simp [h1, h2])
  have hcI : c ≤ I := (le_iff_forall_count K hc0 hI).2 fun w => by rw [hc]; exact le_max_left _ _
  have hcJ : c ≤ J := (le_iff_forall_count K hc0 hJ).2 fun w => by rw [hc]; exact le_max_right _ _
  apply le_antisymm
  · have := count_mono K v hc0 (le_inf hcI hcJ)
    rwa [hc] at this
  · exact max_le (count_mono K v hS inf_le_left) (count_mono K v hS inf_le_right)


/-! ### Items of §22 -/

section Items

/-- **O'Meara 22:1 (1).** An element $x$ of the field lies in the nonzero fractional ideal $\mathfrak a$ exactly
when $|x|_{\mathfrak p} \le |\mathfrak a|_{\mathfrak p}$ for every prime $\mathfrak p$, where
$|\mathfrak a|_{\mathfrak p} = \max_{\alpha \in \mathfrak a}|\alpha|_{\mathfrak p}$ is `idealAbs`
($= e^{-\operatorname{ord}_{\mathfrak p}\mathfrak a}$; the maximum is attained, `exists_mem_valuation_eq`). -/
@[kb "omeara1963" "§22B, 22:1, p. 46 (1)"]
theorem mem_iff_forall_valuation_le_idealAbs {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (x : K) :
    x ∈ I ↔ ∀ v : HeightOneSpectrum R, v.valuation K x ≤ idealAbs v I :=
  mem_iff_valuation_le hI x

/-- **O'Meara 22:1 (2).** For nonzero fractional ideals, $\mathfrak a \subseteq \mathfrak b$ if and only if
$|\mathfrak a|_{\mathfrak p} \le |\mathfrak b|_{\mathfrak p}$ for every prime $\mathfrak p$. -/
@[kb "omeara1963" "§22B, 22:1, p. 46 (2)"]
theorem le_iff_forall_idealAbs_le {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I ≤ J ↔ ∀ v : HeightOneSpectrum R, idealAbs v I ≤ idealAbs v J := by
  rw [le_iff_forall_count K hI hJ]
  refine forall_congr' fun v => ?_
  rw [idealAbs, idealAbs, exp_le_exp, neg_le_neg_iff]

/-- **O'Meara §22B, p. 45** ($|\mathfrak a|_{\mathfrak p} = \max_{\alpha\in\mathfrak a}|\alpha|_{\mathfrak p}$):
for a nonzero fractional ideal the supremum of the $\mathfrak p$-adic values of its elements is attained by an
element of $\mathfrak a$ and equals `idealAbs`. -/
@[kb "omeara1963" "§22B, p. 45 (|𝔞|_𝔭 is the maximum of |α|_𝔭 over 𝔞)"]
theorem isGreatest_valuation_image {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (v : HeightOneSpectrum R) :
    IsGreatest ((fun x => v.valuation K x) '' (I : Set K)) (idealAbs v I) := by
  obtain ⟨a, ha, hav⟩ := exists_mem_valuation_eq hI v
  exact ⟨⟨a, ha, hav⟩, by rintro _ ⟨x, hx, rfl⟩; exact valuation_le_idealAbs hI hx v⟩

/-- **O'Meara 22:2.** Local ideals glue to a global one: given exponents $e_{\mathfrak p} \in \mathbb Z$, zero for
almost all $\mathfrak p$ (so $|\mathfrak a_{\mathfrak p}| = e^{-e_{\mathfrak p}}$ is $1$ for almost all
$\mathfrak p$), the set $\mathfrak a = \{x \in F : |x|_{\mathfrak p} \le |\mathfrak a_{\mathfrak p}|\ \forall\mathfrak p\}$ is a
nonzero fractional ideal with $|\mathfrak a|_{\mathfrak p} = |\mathfrak a_{\mathfrak p}|$ for every $\mathfrak p$. -/
@[kb "omeara1963" "§22B, 22:2, p. 47"]
theorem exists_fractionalIdeal_of_local (e : HeightOneSpectrum R → ℤ)
    (he : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, e v = 0) :
    ∃ I : FractionalIdeal R⁰ K, I ≠ 0 ∧ (∀ x : K, x ∈ I ↔ ∀ v : HeightOneSpectrum R,
      v.valuation K x ≤ exp (-e v)) ∧ ∀ v : HeightOneSpectrum R, idealAbs v I = exp (-e v) := by
  obtain ⟨I, hI, hc⟩ := exists_ideal_with_count (K := K) e he
  refine ⟨I, hI, fun x => ?_, fun v => by rw [idealAbs, hc]⟩
  rw [mem_iff_valuation_le hI x]
  simp [idealAbs, hc]


section Identities

variable {a b c : FractionalIdeal R⁰ K}

/-- **O'Meara 22:3**, first identity: $\mathfrak a(\mathfrak b + \mathfrak c) = \mathfrak a\mathfrak b + \mathfrak a\mathfrak c$
(here $+$ is the gcd $\sqcup$). -/
@[kb "omeara1963" "§22B, 22:3, p. 47 (a(b + c) = ab + ac)"]
theorem mul_sup_eq (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : a * (b ⊔ c) = a * b ⊔ a * c := by
  refine eq_of_forall_count_eq K (mul_ne_zero ha (sup_ne_zero' hb)) (sup_ne_zero' (mul_ne_zero ha hb))
    fun v => ?_
  rw [count_mul K v ha (sup_ne_zero' hb), count_sup hb hc, count_sup (mul_ne_zero ha hb)
    (mul_ne_zero ha hc), count_mul K v ha hb, count_mul K v ha hc]
  omega

/-- **O'Meara 22:3**: $\mathfrak a(\mathfrak b \cap \mathfrak c) = \mathfrak a\mathfrak b \cap \mathfrak a\mathfrak c$. -/
@[kb "omeara1963" "§22B, 22:3, p. 47 (a(b ∩ c) = ab ∩ ac)"]
theorem mul_inf_eq (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : a * (b ⊓ c) = a * b ⊓ a * c := by
  refine eq_of_forall_count_eq K (mul_ne_zero ha (inf_ne_zero' hb hc))
    (inf_ne_zero' (mul_ne_zero ha hb) (mul_ne_zero ha hc)) fun v => ?_
  rw [count_mul K v ha (inf_ne_zero' hb hc), count_inf hb hc, count_inf (mul_ne_zero ha hb)
    (mul_ne_zero ha hc), count_mul K v ha hb, count_mul K v ha hc]
  omega

/-- **O'Meara 22:3**: $(\mathfrak a + \mathfrak b)^n = \mathfrak a^n + \mathfrak b^n$ for $n \in \mathbb N$. -/
@[kb "omeara1963" "§22B, 22:3, p. 47 ((a + b)^n = a^n + b^n)"]
theorem sup_pow_eq (ha : a ≠ 0) (hb : b ≠ 0) (n : ℕ) : (a ⊔ b) ^ n = a ^ n ⊔ b ^ n := by
  refine eq_of_forall_count_eq K (pow_ne_zero n (sup_ne_zero' ha))
    (sup_ne_zero' (pow_ne_zero n ha)) fun v => ?_
  rw [count_pow, count_sup ha hb, count_sup (pow_ne_zero n ha) (pow_ne_zero n hb), count_pow,
    count_pow]
  rcases le_total (count K v a) (count K v b) with h | h
  · rw [min_eq_left h, min_eq_left (by nlinarith)]
  · rw [min_eq_right h, min_eq_right (by nlinarith)]

/-- **O'Meara 22:3**: $(\mathfrak a \cap \mathfrak b)^n = \mathfrak a^n \cap \mathfrak b^n$ for $n \in \mathbb N$. -/
@[kb "omeara1963" "§22B, 22:3, p. 47 ((a ∩ b)^n = a^n ∩ b^n)"]
theorem inf_pow_eq (ha : a ≠ 0) (hb : b ≠ 0) (n : ℕ) : (a ⊓ b) ^ n = a ^ n ⊓ b ^ n := by
  refine eq_of_forall_count_eq K (pow_ne_zero n (inf_ne_zero' ha hb))
    (inf_ne_zero' (pow_ne_zero n ha) (pow_ne_zero n hb)) fun v => ?_
  rw [count_pow, count_inf ha hb, count_inf (pow_ne_zero n ha) (pow_ne_zero n hb), count_pow,
    count_pow]
  rcases le_total (count K v a) (count K v b) with h | h
  · rw [max_eq_right h, max_eq_right (by nlinarith)]
  · rw [max_eq_left h, max_eq_left (by nlinarith)]

/-- **O'Meara 22:3**: $\mathfrak a \cap (\mathfrak b + \mathfrak c) = (\mathfrak a \cap \mathfrak b) + (\mathfrak a \cap \mathfrak c)$. -/
@[kb "omeara1963" "§22B, 22:3, p. 47 (a ∩ (b + c) = (a ∩ b) + (a ∩ c))"]
theorem inf_sup_eq (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) := by
  refine eq_of_forall_count_eq K (inf_ne_zero' ha (sup_ne_zero' hb))
    (sup_ne_zero' (inf_ne_zero' ha hb)) fun v => ?_
  rw [count_inf ha (sup_ne_zero' hb), count_sup hb hc, count_sup (inf_ne_zero' ha hb)
    (inf_ne_zero' ha hc), count_inf ha hb, count_inf ha hc]
  omega

/-- **O'Meara 22:3**: $\mathfrak a + (\mathfrak b \cap \mathfrak c) = (\mathfrak a + \mathfrak b) \cap (\mathfrak a + \mathfrak c)$. -/
@[kb "omeara1963" "§22B, 22:3, p. 47 (a + (b ∩ c) = (a + b) ∩ (a + c))"]
theorem sup_inf_eq (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) := by
  refine eq_of_forall_count_eq K (sup_ne_zero' ha)
    (inf_ne_zero' (sup_ne_zero' ha) (sup_ne_zero' ha)) fun v => ?_
  rw [count_sup ha (inf_ne_zero' hb hc), count_inf hb hc, count_inf (sup_ne_zero' ha)
    (sup_ne_zero' ha), count_sup ha hb, count_sup ha hc]
  omega

/-- **O'Meara 22:3**: $\mathfrak a\mathfrak b = (\mathfrak a + \mathfrak b)(\mathfrak a \cap \mathfrak b)$ (product equals
gcd times lcm). -/
@[kb "omeara1963" "§22B, 22:3, p. 47 (ab = (a + b)(a ∩ b))"]
theorem mul_eq_sup_mul_inf (ha : a ≠ 0) (hb : b ≠ 0) : a * b = (a ⊔ b) * (a ⊓ b) := by
  refine eq_of_forall_count_eq K (mul_ne_zero ha hb)
    (mul_ne_zero (sup_ne_zero' ha) (inf_ne_zero' ha hb)) fun v => ?_
  rw [count_mul K v ha hb, count_mul K v (sup_ne_zero' ha) (inf_ne_zero' ha hb), count_sup ha hb,
    count_inf ha hb]
  omega

/-- **O'Meara 22:3**: if $\mathfrak a^n = \mathfrak b^n$ for some $n \ge 1$ then $\mathfrak a = \mathfrak b$. -/
@[kb "omeara1963" "§22B, 22:3, p. 47 (a^n = b^n ⇒ a = b)"]
theorem eq_of_pow_eq_pow (ha : a ≠ 0) (hb : b ≠ 0) {n : ℕ} (hn : 0 < n) (h : a ^ n = b ^ n) :
    a = b := by
  refine eq_of_forall_count_eq K ha hb fun v => ?_
  have := congrArg (count K v) h
  rw [count_pow, count_pow] at this
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  exact (mul_left_cancel₀ hn'.ne' this)

/-- **O'Meara 22:4**: $(\mathfrak a + \mathfrak b)^{-1} = \mathfrak a^{-1} \cap \mathfrak b^{-1}$. -/
@[kb "omeara1963" "§22C, 22:4, p. 48 ((a + b)^{-1} = a^{-1} ∩ b^{-1})"]
theorem inv_sup_eq (ha : a ≠ 0) (hb : b ≠ 0) : (a ⊔ b)⁻¹ = a⁻¹ ⊓ b⁻¹ := by
  refine eq_of_forall_count_eq K (inv_ne_zero (sup_ne_zero' ha))
    (inf_ne_zero' (inv_ne_zero ha) (inv_ne_zero hb)) fun v => ?_
  rw [count_inv, count_sup ha hb, count_inf (inv_ne_zero ha) (inv_ne_zero hb), count_inv, count_inv]
  omega

/-- **O'Meara 22:4**: $(\mathfrak a \cap \mathfrak b)^{-1} = \mathfrak a^{-1} + \mathfrak b^{-1}$. -/
@[kb "omeara1963" "§22C, 22:4, p. 48 ((a ∩ b)^{-1} = a^{-1} + b^{-1})"]
theorem inv_inf_eq (ha : a ≠ 0) (hb : b ≠ 0) : (a ⊓ b)⁻¹ = a⁻¹ ⊔ b⁻¹ := by
  refine eq_of_forall_count_eq K (inv_ne_zero (inf_ne_zero' ha hb))
    (sup_ne_zero' (inv_ne_zero ha)) fun v => ?_
  rw [count_inv, count_inf ha hb, count_sup (inv_ne_zero ha) (inv_ne_zero hb), count_inv, count_inv]
  omega

end Identities

/-- **O'Meara 22:5b.** Every fractional ideal is a finitely generated $\mathfrak o$-module. -/
@[kb "omeara1963" "§22C, 22:5b, p. 48"]
theorem fractionalIdeal_fg (I : FractionalIdeal R⁰ K) : (I : Submodule R K).FG :=
  FractionalIdeal.fg_of_isNoetherianRing le_rfl I

/-- **O'Meara 22:6.** For an ideal $0 \ne \mathfrak a \subsetneq \mathfrak o$ of a Dedekind domain the following
are equivalent: (1) $\mathfrak a = \mathfrak o \cap \mathfrak m(\mathfrak p)$ for a prime $\mathfrak p$ (a height-one
prime ideal); (2) $\mathfrak a$ is prime; (3) $\mathfrak a$ is indecomposable (not a product $\mathfrak b\mathfrak c$
of ideals both different from $\mathfrak o$); (4) $\mathfrak a$ is maximal. -/
@[kb "omeara1963" "§22C, 22:6, p. 49"]
theorem tfae_prime_indecomposable_maximal (a : Ideal R) (h0 : a ≠ ⊥) (h1 : a ≠ ⊤) :
    List.TFAE [∃ v : HeightOneSpectrum R, a = v.asIdeal, a.IsPrime,
      ¬ ∃ b c : Ideal R, b ≠ ⊤ ∧ c ≠ ⊤ ∧ a = b * c, a.IsMaximal] := by
  tfae_have 1 → 2 := by rintro ⟨v, rfl⟩; exact v.isPrime
  tfae_have 2 → 3 := by
    intro hp
    rintro ⟨b, c, hb, hc, habc⟩
    have hb0 : b ≠ ⊥ := by rintro rfl; apply h0; rw [habc]; simp
    have hc0 : c ≠ ⊥ := by rintro rfl; apply h0; rw [habc]; simp
    have hle : b * c ≤ a := habc ▸ le_rfl
    rcases (hp.mul_le).1 hle with hba | hca
    · have : b ≤ a := hba
      have hab : a ≤ b := habc ▸ Ideal.mul_le_left
      have : b = a := le_antisymm ‹b ≤ a› hab
      subst this
      apply hc
      have : b * c = b * ⊤ := by rw [Ideal.mul_top, ← habc]
      exact mul_left_cancel₀ hb0 this
    · have hab : a ≤ c := habc ▸ Ideal.mul_le_right
      have : c = a := le_antisymm hca hab
      subst this
      apply hb
      have : b * c = ⊤ * c := by rw [Ideal.top_mul, ← habc]
      exact mul_right_cancel₀ hc0 this
  tfae_have 3 → 4 := by
    intro h3
    refine ⟨⟨h1, fun b hb => ?_⟩⟩
    by_contra hb'
    have hbd : b ∣ a := Ideal.dvd_iff_le.2 hb.le
    obtain ⟨c, hc⟩ := hbd
    refine h3 ⟨b, c, hb', fun hct => ?_, hc⟩
    subst hct
    rw [Ideal.mul_top] at hc
    exact hb.ne hc
  tfae_have 4 → 1 := fun h => ⟨⟨a, h.isPrime, h0⟩, rfl⟩
  tfae_finish


/-- **O'Meara 22:7 (Unique Factorization Theorem)**, existence and uniqueness. Every nonzero fractional ideal
$\mathfrak a$ is a product $\prod_{\mathfrak p}\mathfrak p^{e_{\mathfrak p}}$ with integer exponents $e_{\mathfrak p}$,
almost all zero (a finitely supported function), and the exponent function is unique. -/
@[kb "omeara1963" "§22C, 22:7, p. 49 (existence and uniqueness of the factorization)"]
theorem existsUnique_prime_factorization {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    ∃! e : HeightOneSpectrum R →₀ ℤ,
      I = e.prod fun v n => (v.asIdeal : FractionalIdeal R⁰ K) ^ n := by
  classical
  have hfin : (Function.support fun v : HeightOneSpectrum R => count K v I).Finite := by
    exact Filter.eventually_cofinite.1 (finite_factors I)
  refine ⟨Finsupp.ofSupportFinite _ hfin, ?_, fun e he => ?_⟩
  · simp only [Finsupp.prod]
    conv_lhs => rw [← finprod_heightOneSpectrum_factorization' (K := K) hI]
    rw [finprod_eq_finsetProd_of_mulSupport_subset (s := hfin.toFinset)]
    · rfl
    · intro v hv
      simp only [Function.mem_mulSupport] at hv
      simp only [Set.Finite.coe_toFinset, Function.mem_support]
      intro h; apply hv; simp [h]
  · ext v
    have := count_finsuppProd K v e
    rw [← he] at this
    simpa [Finsupp.ofSupportFinite_coe] using this.symm

/-- **O'Meara 22:7**, group structure: the factorization map $e \mapsto \prod_{\mathfrak p}\mathfrak p^{e_{\mathfrak p}}$
from the free abelian group on the primes is multiplicative, so together with
`existsUnique_prime_factorization` the fractional ideals form a free abelian group with the prime ideals as base. -/
@[kb "omeara1963" "§22C, 22:7, p. 49 (the factorization map is a homomorphism)"]
theorem prod_add_eq_mul (e e' : HeightOneSpectrum R →₀ ℤ) :
    ((e + e').prod fun v n => (v.asIdeal : FractionalIdeal R⁰ K) ^ n) =
      (e.prod fun v n => (v.asIdeal : FractionalIdeal R⁰ K) ^ n) *
        (e'.prod fun v n => (v.asIdeal : FractionalIdeal R⁰ K) ^ n) := by
  refine Finsupp.prod_add_index' (fun v => zpow_zero _) fun v m n => ?_
  exact zpow_add₀ (coeIdeal_ne_zero.mpr v.ne_bot) m n

/-- **O'Meara 22:8** (definition of the order and its additivity). The order $\operatorname{ord}_{\mathfrak p}\mathfrak a$
of a fractional ideal at $\mathfrak p$ is the exponent of $\mathfrak p$ in its factorization, `FractionalIdeal.count`;
it is additive: $\operatorname{ord}_{\mathfrak p}(\mathfrak a\mathfrak b) = \operatorname{ord}_{\mathfrak p}\mathfrak a +
\operatorname{ord}_{\mathfrak p}\mathfrak b$. -/
@[kb "omeara1963" "§22C, 22:8, p. 50 (ord_𝔭 𝔞𝔟 = ord_𝔭 𝔞 + ord_𝔭 𝔟)"]
theorem ord_mul {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) (v : HeightOneSpectrum R) :
    count K v (I * J) = count K v I + count K v J :=
  count_mul K v hI hJ

/-- **O'Meara 22:8**: $\operatorname{ord}_{\mathfrak p}(x\mathfrak o) = \operatorname{ord}_{\mathfrak p}x$, i.e. the order of
a principal ideal is the order of the generator, and $|x|_{\mathfrak p} = |\pi|_{\mathfrak p}^{\operatorname{ord}_{\mathfrak p}(x\mathfrak o)}$
for a prime element $\pi$ (a uniformizer with $|\pi|_{\mathfrak p} = e^{-1}$). -/
@[kb "omeara1963" "§22C, 22:8, p. 50 (ord_𝔭 x𝔬 = ord_𝔭 x, |𝔞|_𝔭 = |π|_𝔭^{ord_𝔭 𝔞})"]
theorem valuation_eq_uniformizer_pow_ord (v : HeightOneSpectrum R) {π x : K}
    (hπ : v.valuation K π = exp (-1 : ℤ)) (hx : x ≠ 0) :
    v.valuation K x = v.valuation K π ^ count K v (spanSingleton R⁰ x) := by
  rw [valuation_eq_exp_neg_count v hx, hπ, ← exp_zsmul]
  congr 1
  simp

/-- **O'Meara 22:8**, ideal form: $|\mathfrak a|_{\mathfrak p} = |\pi|_{\mathfrak p}^{\operatorname{ord}_{\mathfrak p}\mathfrak a}$. -/
@[kb "omeara1963" "§22C, 22:8, p. 50 (|𝔞|_𝔭 = |π|_𝔭^{ord_𝔭 𝔞})"]
theorem idealAbs_eq_uniformizer_pow_ord (v : HeightOneSpectrum R) {π : K}
    (hπ : v.valuation K π = exp (-1 : ℤ)) (I : FractionalIdeal R⁰ K) :
    idealAbs v I = v.valuation K π ^ count K v I := by
  rw [idealAbs, hπ, ← exp_zsmul]
  congr 1
  simp

end Items


end Core
end QuadFormsKB.OMeara
