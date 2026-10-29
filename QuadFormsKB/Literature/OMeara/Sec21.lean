/-
# O'Meara §21: Dedekind axioms and strong approximation

**Setting.** As in `Sec22.lean`: $\mathfrak o$ a Dedekind domain with fraction field $F$; O'Meara's Dedekind set $S$ of
spots is read as the set of all height-one primes $\mathfrak p$ of $\mathfrak o$ with the discrete valuations
$|\cdot|_{\mathfrak p}$ = `IsDedekindDomain.HeightOneSpectrum.valuation` (values in $\mathbb Z_{m0}$, so $\varepsilon>0$
is a nonzero element of $\mathbb Z_{m0}$). The abstract notion of Dedekind set of spots on a field is only
formalized through this model (`DedekindAxioms`); the book's converse (every abstract Dedekind set gives such a
domain) is not formalized, so every statement below is the special case $S$ = primes of a Mathlib Dedekind domain.

**Proves**
* `DedekindAxioms` (definition of D1-D3 for the primes of $\mathfrak o$) and `dedekindAxioms`: they always hold
  (Chinese remainder theorem for D3); 21:1: `rat_dedekindAxioms` ($\mathbb Z \subset \mathbb Q$);
* 21:2 `strong_approximation` (Strong Approximation Theorem); 21:2a `exists_valuation_eq_le`;
* 21:3 `ringOfIntegers_eq_and_isFractionRing` ($\mathfrak o(S) = \mathfrak o$ and $F = \operatorname{Frac}\mathfrak o$);
* 21:4 `valuation_le_one_iff_mem_closure` ($\mathfrak o(\mathfrak p)$ is the closure of $\mathfrak o$) and
  `exists_sub_lt_one_of_valuation_le_one` ($\mathfrak o$ contains a residue system).

*Proof notes.* 21:2: clear denominators ($d\,a_{\mathfrak p} \in \mathfrak o$) and solve a Chinese-remainder system modulo
high powers of the primes in $T$ and of the primes dividing $d$, then divide by $d$ (O'Meara instead uses (D3)
directly; here D3 is the consequence). Strong approximation for number fields in adelic form, with a very strong
version, is `Lattices.exists_scalar_approx` / `Lattices.exists_very_strong_approx` (33:11).
-/
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import QuadFormsKB.Citation

set_option linter.unusedSectionVars false

open IsDedekindDomain WithZero
open scoped nonZeroDivisors

noncomputable section

namespace QuadFormsKB.OMeara

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- **O'Meara 21:2 (Strong Approximation Theorem).** Let $T$ be a finite set of primes $\mathfrak p$ of a Dedekind
domain $\mathfrak o$ with fraction field $F$, let $a_{\mathfrak p} \in F$ be given for $\mathfrak p \in T$, and let
$\varepsilon > 0$ be a value (`ε : ℤᵐ⁰`, $\varepsilon \ne 0$). Then there is $A \in F$ with
$|A - a_{\mathfrak p}|_{\mathfrak p} < \varepsilon$ for all $\mathfrak p \in T$ and $|A|_{\mathfrak p} \le 1$ for all
$\mathfrak p \notin T$. -/
@[kb "omeara1963" "§21, 21:2, p. 42 (Strong Approximation Theorem)"]
theorem strong_approximation (T : Finset (HeightOneSpectrum R)) (a : HeightOneSpectrum R → K)
    {ε : ℤᵐ⁰} (hε : ε ≠ 0) :
    ∃ A : K, (∀ v ∈ T, v.valuation K (A - a v) < ε) ∧ ∀ v ∉ T, v.valuation K A ≤ 1 := by
  classical
  obtain ⟨M, hM⟩ := exists_exp_neg_natCast_lt hε
  obtain ⟨⟨d, hd⟩, hdint⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R)
    (T.image a)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hd0' : algebraMap R K d ≠ 0 := by simpa using hd0
  choose! b hb using fun v (hv : v ∈ T) => hdint (a v) (Finset.mem_image_of_mem a hv)
  have hspan : Ideal.span {d} ≠ ⊥ := by simpa using hd0
  let k : HeightOneSpectrum R → ℕ :=
    fun v => (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d} : Ideal R)).factors
  have hk : ∀ v : HeightOneSpectrum R, v.intValuation d = exp (-(k v : ℤ)) := fun v =>
    v.intValuation_if_neg hd0
  let U : Finset (HeightOneSpectrum R) := (Ideal.finite_factors hspan).toFinset
  obtain ⟨c, hc⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T ∪ U)
    (fun v => v.asIdeal) (fun v => if v ∈ T then k v + M else k v) (fun v _ => v.prime)
    (fun v _ w _ h hvw => h (HeightOneSpectrum.ext hvw))
    (fun v => if (v : HeightOneSpectrum R) ∈ T then b v else 0)
  refine ⟨algebraMap R K c * (algebraMap R K d)⁻¹, fun v hv => ?_, fun v hv => ?_⟩
  · have hcv := hc v (Finset.mem_union_left _ hv)
    simp only [hv, ite_true] at hcv
    have hav : a v = algebraMap R K (b v) * (algebraMap R K d)⁻¹ := by
      have := hb v hv
      rw [Algebra.smul_def] at this
      field_simp
      rw [this]; simp [mul_comm]
    rw [hav, ← sub_mul, ← map_sub, map_mul, map_inv₀, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, hk]
    have h1 : v.intValuation (c - b v) ≤ exp (-((k v + M : ℕ) : ℤ)) :=
      (v.intValuation_le_pow_iff_mem _ _).2 hcv
    calc v.intValuation (c - b v) * (exp (-(k v : ℤ)))⁻¹
        ≤ exp (-((k v + M : ℕ) : ℤ)) * (exp (-(k v : ℤ)))⁻¹ := by gcongr
      _ = exp (-(M : ℤ)) := by
        rw [← exp_neg, ← exp_add]; congr 1; push_cast; ring
      _ < ε := hM
  · rw [map_mul, map_inv₀, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap]
    by_cases hvU : v ∈ U
    · have hcv := hc v (Finset.mem_union_right _ hvU)
      simp only [hv, ite_false, sub_zero] at hcv
      have h1 : v.intValuation c ≤ exp (-(k v : ℤ)) := (v.intValuation_le_pow_iff_mem _ _).2 hcv
      rw [hk]
      calc v.intValuation c * (exp (-(k v : ℤ)))⁻¹ ≤ exp (-(k v : ℤ)) * (exp (-(k v : ℤ)))⁻¹ := by
            gcongr
        _ = 1 := by rw [mul_inv_cancel₀]; exact exp_ne_zero
    · have hnd : ¬ v.asIdeal ∣ Ideal.span {d} := by
        intro h
        exact hvU ((Set.Finite.mem_toFinset _).2 h)
      have : v.intValuation d = 1 := by
        refine le_antisymm (v.intValuation_le_one d) ?_
        by_contra hlt
        push Not at hlt
        exact hnd ((v.intValuation_lt_one_iff_dvd d).1 hlt)
      rw [this, inv_one, mul_one]
      exact v.intValuation_le_one c

/-- **O'Meara 21:2a.** Let $\xi_{\mathfrak p}$ be nonzero values, equal to $1$ outside the finite set $T$. Then there is
$A \in F$ with $|A|_{\mathfrak p} = \xi_{\mathfrak p}$ for $\mathfrak p \in T$ and $|A|_{\mathfrak p} \le \xi_{\mathfrak p}$ for
all $\mathfrak p$. (Every nonzero value of $\mathbb Z_{m0}$ is a value of the valuation, so the hypothesis "$\xi_{\mathfrak p}$
in the value group" is automatic.) -/
@[kb "omeara1963" "§21, 21:2a, p. 43"]
theorem exists_valuation_eq_le (T : Finset (HeightOneSpectrum R)) (ξ : HeightOneSpectrum R → ℤᵐ⁰)
    (hξ : ∀ v, ξ v ≠ 0) (hT : ∀ v ∉ T, ξ v = 1) :
    ∃ A : K, (∀ v ∈ T, v.valuation K A = ξ v) ∧ ∀ v, v.valuation K A ≤ ξ v := by
  classical
  have hsurj := fun v : HeightOneSpectrum R => v.valuation_surjective (K := K) (ξ v)
  choose c hc using hsurj
  rcases T.eq_empty_or_nonempty with rfl | hne
  · refine ⟨1, by simp, fun v => ?_⟩
    simp [hT v (Finset.notMem_empty v)]
  obtain ⟨v₀, hv₀, hmin⟩ := Finset.exists_min_image T ξ hne
  obtain ⟨A, hA1, hA2⟩ := strong_approximation K T c (hξ v₀)
  have hAT : ∀ v ∈ T, v.valuation K A = ξ v := by
    intro v hv
    have h1 : v.valuation K (A - c v) < v.valuation K (c v) := by
      rw [hc]; exact lt_of_lt_of_le (hA1 v hv) (hmin v hv)
    rw [← hc v]
    have := Valuation.map_sub_swap (v.valuation K) A (c v)
    exact Valuation.map_eq_of_sub_lt _ h1
  refine ⟨A, hAT, fun v => ?_⟩
  by_cases hv : v ∈ T
  · exact (hAT v hv).le
  · rw [hT v hv]; exact hA2 v hv

/-- **O'Meara 21:3.** For a Dedekind domain $\mathfrak o$ with fraction field $F$, the ring of integers at the set of
all primes, $\mathfrak o(S) = \bigcap_{\mathfrak p}\mathfrak o(\mathfrak p)$, is $\mathfrak o$, and $F$ is its quotient
field. -/
@[kb "omeara1963" "§21, 21:3, p. 43"]
theorem ringOfIntegers_eq_and_isFractionRing :
    (∀ x : K, (∀ v : HeightOneSpectrum R, v.valuation K x ≤ 1) ↔ x ∈ (algebraMap R K).range) ∧
      ∀ x : K, ∃ a b : R, b ≠ 0 ∧ x = algebraMap R K a / algebraMap R K b := by
  refine ⟨fun x => ⟨HeightOneSpectrum.mem_integers_of_valuation_le_one K x, ?_⟩, fun x => ?_⟩
  · rintro ⟨r, rfl⟩ v
    exact v.valuation_le_one r
  · obtain ⟨a, b, hb, h⟩ := IsFractionRing.div_surjective (A := R) x
    exact ⟨a, b, nonZeroDivisors.ne_zero hb, h.symm⟩

/-- **O'Meara 21:4.** $\mathfrak o(\mathfrak p)$ is the closure of $\mathfrak o$ in $F$ at $\mathfrak p$: an element
$x \in F$ has $|x|_{\mathfrak p} \le 1$ if and only if for every value $\varepsilon \ne 0$ there is $a \in \mathfrak o$
with $|a - x|_{\mathfrak p} < \varepsilon$. -/
@[kb "omeara1963" "§21, 21:4, p. 44"]
theorem valuation_le_one_iff_mem_closure (v : HeightOneSpectrum R) (x : K) :
    v.valuation K x ≤ 1 ↔ ∀ ε : ℤᵐ⁰, ε ≠ 0 → ∃ a : R, v.valuation K (algebraMap R K a - x) < ε := by
  constructor
  · intro hx ε hε
    exact v.exists_valuation_sub_lt_of_integer hx (Units.mk0 ε hε)
  · intro h
    obtain ⟨a, ha⟩ := h 1 one_ne_zero
    have h1 : v.valuation K (algebraMap R K a) ≤ 1 := v.valuation_le_one a
    have : x = algebraMap R K a - (algebraMap R K a - x) := by ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le h1 ha.le)

/-- **O'Meara 21:4** (second part): $\mathfrak o$ contains a representative set of the residue class field of $F$ at
$\mathfrak p$; i.e. every $x$ with $|x|_{\mathfrak p} \le 1$ is congruent modulo $\mathfrak m(\mathfrak p)$
($|a - x|_{\mathfrak p} < 1$) to an element $a$ of $\mathfrak o$. -/
@[kb "omeara1963" "§21, 21:4, p. 44 (𝔬 contains a representative set of the residue class field)"]
theorem exists_sub_lt_one_of_valuation_le_one (v : HeightOneSpectrum R) {x : K}
    (hx : v.valuation K x ≤ 1) : ∃ a : R, v.valuation K (algebraMap R K a - x) < 1 :=
  (valuation_le_one_iff_mem_closure K v x).1 hx 1 one_ne_zero

/-- **The Dedekind axioms (D1)–(D3) of O'Meara §21** for the set $S$ of all height-one primes of the Dedekind
domain $\mathfrak o$, as spots on $F$ (valuations $|\cdot|_{\mathfrak p}$ = `v.valuation K`, values in $\mathbb Z_{m0}$):
(D1) every spot is discrete (the valuation is non-trivial; a $\mathbb Z_{m0}$-valued valuation is discrete);
(D2) for each $a \in F$, $|a|_{\mathfrak p} \le 1$ for almost all $\mathfrak p$;
(D3) for distinct $\mathfrak q, \mathfrak q'$ and every value $\varepsilon \ne 0$ there is $a \in F$ with
$|a - 1|_{\mathfrak q} < \varepsilon$, $|a|_{\mathfrak q'} < \varepsilon$ and $|a|_{\mathfrak p} \le 1$ for all other $\mathfrak p$. -/
@[kb "omeara1963" "§21, p. 42 (Dedekind axioms (D1)-(D3) for S)"]
def DedekindAxioms (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] : Prop :=
  (∀ v : HeightOneSpectrum R, (v.valuation K).IsNontrivial) ∧
  (∀ a : K, ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, v.valuation K a ≤ 1) ∧
  ∀ v w : HeightOneSpectrum R, v ≠ w → ∀ ε : ℤᵐ⁰, ε ≠ 0 → ∃ a : K,
    v.valuation K (a - 1) < ε ∧ w.valuation K a < ε ∧
      ∀ u : HeightOneSpectrum R, u ≠ v → u ≠ w → u.valuation K a ≤ 1

/-- **(D2)** for the primes of a Dedekind domain. -/
theorem valuation_le_one_cofinite (a : K) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, v.valuation K a ≤ 1 := by
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors R) a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hspan : Ideal.span {d} ≠ ⊥ := by simpa using hd0
  have hfin := Ideal.finite_factors hspan
  rw [Filter.eventually_cofinite]
  refine hfin.subset fun v hv => ?_
  by_contra hnd'
  apply hv
  have : v.intValuation d = 1 := by
    refine le_antisymm (v.intValuation_le_one d) ?_
    by_contra hlt
    push Not at hlt
    exact hnd' ((v.intValuation_lt_one_iff_dvd d).1 hlt)
  rw [← hnd, HeightOneSpectrum.valuation_of_mk']
  simp only [this, div_one]
  exact v.intValuation_le_one n

/-- **(D3)** for the primes of a Dedekind domain (Chinese remainder theorem). -/
theorem exists_approx_pair (v w : HeightOneSpectrum R) (hvw : v ≠ w) {ε : ℤᵐ⁰} (hε : ε ≠ 0) :
    ∃ a : K, v.valuation K (a - 1) < ε ∧ w.valuation K a < ε ∧
      ∀ u : HeightOneSpectrum R, u ≠ v → u ≠ w → u.valuation K a ≤ 1 := by
  classical
  obtain ⟨N, hN⟩ := exists_exp_neg_natCast_lt hε
  obtain ⟨c, hc⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := ({v, w} : Finset _))
    (fun u => u.asIdeal) (fun _ => N) (fun u _ => u.prime)
    (fun u _ u' _ h huu' => h (HeightOneSpectrum.ext huu'))
    (fun u => if (u : HeightOneSpectrum R) = v then 1 else 0)
  have hv := hc v (by simp)
  have hw := hc w (by simp)
  simp only [ite_true] at hv
  simp only [hvw.symm, ite_false, sub_zero] at hw
  refine ⟨algebraMap R K c, ?_, ?_, fun u _ _ => u.valuation_le_one c⟩
  · rw [← map_one (algebraMap R K), ← map_sub, HeightOneSpectrum.valuation_of_algebraMap]
    exact lt_of_le_of_lt ((v.intValuation_le_pow_iff_mem _ _).2 hv) hN
  · rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact lt_of_le_of_lt ((w.intValuation_le_pow_iff_mem _ _).2 hw) hN

/-- **The primes of every Dedekind domain satisfy the Dedekind axioms** (D1)–(D3) of O'Meara §21: the set of
all height-one primes of a Dedekind domain $\mathfrak o$ with fraction field $F$ is a Dedekind set of spots on
$F$. This is the content of "$S$ is Dedekind" in 21:1, 23:1 and 31:2 (each is this theorem for a particular
$\mathfrak o$); O'Meara's 22:10 and 23:1–23:2 are the converse correspondence. -/
@[kb "omeara1963" "§21, p. 42 (the set of primes of a Dedekind domain satisfies (D1)-(D3))"]
theorem dedekindAxioms : DedekindAxioms R K :=
  ⟨fun _ => inferInstance, valuation_le_one_cofinite K, fun v w hvw _ hε => exists_approx_pair K v w hvw hε⟩

/-- **O'Meara 21:1.** The set of all non-archimedean spots of the field $\mathbb Q$ of rational numbers is a Dedekind
set: the finite spots of $\mathbb Q$ are the height-one primes of $\mathbb Z$ (the $p$-adic spots; O'Meara 31:1), and
they satisfy (D1)–(D3) (`dedekindAxioms`). Moreover $\mathfrak o(S) = \mathbb Z$: a rational number is integral at
every prime iff it is an integer. -/
@[kb "omeara1963" "§21, 21:1, p. 42"]
theorem rat_dedekindAxioms :
    DedekindAxioms ℤ ℚ ∧ ∀ x : ℚ, (∀ v : HeightOneSpectrum ℤ, v.valuation ℚ x ≤ 1) ↔
      x ∈ (algebraMap ℤ ℚ).range :=
  ⟨dedekindAxioms ℚ, (ringOfIntegers_eq_and_isFractionRing (R := ℤ) ℚ).1⟩

end QuadFormsKB.OMeara
