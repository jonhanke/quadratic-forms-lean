/-
# O'Meara §22F and §23: uniqueness of the spots of a Dedekind domain; extension fields

**Setting.** As in `Sec21.lean`, `Sec22.lean`: $\mathfrak o$ a Dedekind domain (`IsDedekindDomain`), its spots are the
height-one primes with the valuations $|\cdot|_{\mathfrak p}$ (values in $\mathbb Z_{m0}$). For an extension
$E/F$ the spots of $E$ over the spots of $\mathfrak o$ ($T \,\|\, S$) are the primes of the integral closure
$\mathfrak O$ of $\mathfrak o$ in $E$ (every prime of $\mathfrak O$ lies over a prime of $\mathfrak o$).

**Proves**
* 22:10 `existsUnique_heightOneSpectrum_isEquiv`: every discrete spot $w$ of $F$ with $\mathfrak o \subseteq \mathfrak o(w)$ is
  the spot of a unique prime of $\mathfrak o$ (so the underlying set of spots of a Dedekind domain is unique);
* 23:1 `integralClosure_dedekindAxioms`: for a finite separable extension, $\mathfrak O$ is a Dedekind domain with
  fraction field $E$ and its spots satisfy (D1)-(D3);
* 23:2 `tfae_integral_over`: $\alpha \in \mathfrak o(T)$ iff its minimal polynomial over $F$ has coefficients in
  $\mathfrak o$ iff it satisfies a monic polynomial over $\mathfrak o$.

*Proof notes.* 22:10: the prime ideal $\{r : |r|_w < 1\}$ of $\mathfrak o$ is nonzero because $w$ is non-trivial, and the
valuation rings of $w$ and of the corresponding $\mathfrak p$ agree (clearing denominators prime to $\mathfrak p$), as in
O'Meara, but with Mathlib's valuation ring machinery instead of Strong Approximation. 23:1 and 23:2 are Mathlib's
`IsIntegralClosure.isDedekindDomain` and the minimal-polynomial description of integral elements
(`minpoly.isIntegrallyClosed_eq_field_fractions'`), together with 21:3 for $\mathfrak O$ in place of the
local-field argument of O'Meara's proof.
-/
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import QuadFormsKB.Literature.OMeara.Sec21
import QuadFormsKB.Citation

set_option linter.unusedSectionVars false

open IsDedekindDomain WithZero
open scoped nonZeroDivisors

noncomputable section

namespace QuadFormsKB.OMeara

section Spots

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- The prime ideal `{r : w r < 1}` of a nontrivial valuation that is `≤ 1` on `R`. -/
def ltIdeal (w : Valuation K ℤᵐ⁰) (hw : ∀ r : R, w (algebraMap R K r) ≤ 1) : Ideal R where
  carrier := {r | w (algebraMap R K r) < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact lt_of_le_of_lt (w.map_add _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *
    calc w (algebraMap R K c) * w (algebraMap R K a) ≤ 1 * w (algebraMap R K a) :=
          mul_le_mul_left (hw c) _
      _ < 1 := by rwa [one_mul]

theorem mem_ltIdeal {w : Valuation K ℤᵐ⁰} {hw : ∀ r : R, w (algebraMap R K r) ≤ 1} {r : R} :
    r ∈ ltIdeal K w hw ↔ w (algebraMap R K r) < 1 := Iff.rfl


theorem ltIdeal_isPrime (w : Valuation K ℤᵐ⁰) (hw : ∀ r : R, w (algebraMap R K r) ≤ 1) :
    (ltIdeal K w hw).IsPrime := by
  refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
  · rw [Ideal.eq_top_iff_one, mem_ltIdeal] at h
    simp at h
  · rw [mem_ltIdeal, map_mul, Valuation.map_mul] at hab
    rw [mem_ltIdeal, mem_ltIdeal]
    by_contra hcon
    push Not at hcon
    have h1 := le_antisymm (hw a) hcon.1
    have h2 := le_antisymm (hw b) hcon.2
    rw [h1, h2] at hab
    simp at hab

theorem ltIdeal_ne_bot (w : Valuation K ℤᵐ⁰) [w.IsNontrivial]
    (hw : ∀ r : R, w (algebraMap R K r) ≤ 1) : ltIdeal K w hw ≠ ⊥ := by
  obtain ⟨x, hx0, hx1⟩ := Valuation.IsNontrivial.exists_val_nontrivial (v := w)
  obtain ⟨a, b, hb, rfl⟩ : ∃ a b : R, b ≠ 0 ∧ x = algebraMap R K a / algebraMap R K b := by
    obtain ⟨a, b, hb, h⟩ := IsFractionRing.div_surjective (A := R) x
    exact ⟨a, b, nonZeroDivisors.ne_zero hb, h.symm⟩
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx0
  have hb0 : (algebraMap R K b) ≠ 0 := by simpa using hb
  rw [map_div₀] at hx0 hx1
  have hne : w (algebraMap R K a) ≠ w (algebraMap R K b) := by
    intro h; rw [h, div_self] at hx1; exact hx1 rfl
    simpa using (w.ne_zero_iff.2 hb0)
  intro hbot
  have hlt : w (algebraMap R K a) < 1 ∨ w (algebraMap R K b) < 1 := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl (lt_of_lt_of_le h (hw b))
    · exact Or.inr (lt_of_lt_of_le h (hw a))
  rcases hlt with h | h
  · have : a ∈ ltIdeal K w hw := h
    rw [hbot] at this
    exact ha0 (by simpa using this)
  · have : b ∈ ltIdeal K w hw := h
    rw [hbot] at this
    exact hb (by simpa using this)


theorem isEquiv_of_ltIdeal (w : Valuation K ℤᵐ⁰) [w.IsNontrivial]
    (hw : ∀ r : R, w (algebraMap R K r) ≤ 1) :
    ((⟨ltIdeal K w hw, ltIdeal_isPrime K w hw, ltIdeal_ne_bot K w hw⟩ : HeightOneSpectrum R).valuation
      K).IsEquiv w := by
  set v : HeightOneSpectrum R := ⟨ltIdeal K w hw, ltIdeal_isPrime K w hw, ltIdeal_ne_bot K w hw⟩
    with hvdef
  have : v.asIdeal.IsPrime := v.isPrime
  have hcomp : ∀ d : R, d ∈ v.asIdeal.primeCompl → w (algebraMap R K d) = 1 := by
    intro d hd
    have : ¬ w (algebraMap R K d) < 1 := hd
    exact le_antisymm (hw d) (not_lt.1 this)
  have hcomp' : ∀ d : R, w (algebraMap R K d) = 1 → d ∈ v.asIdeal.primeCompl := by
    intro d hd h
    have : w (algebraMap R K d) < 1 := h
    rw [hd] at this; exact lt_irrefl _ this
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  constructor
  · intro hx
    obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v x hx
    have h1 := congrArg w hnd
    rw [Valuation.map_mul, hcomp d d.2, mul_one] at h1
    rw [h1]; exact hw n
  · intro hx
    obtain ⟨n, d, (hnd | hnd)⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq v x
    · have h1 := congrArg (v.valuation K) hnd
      rw [Valuation.map_mul, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.valuation_of_algebraMap,
        (v.intValuation_eq_one_iff_mem_primeCompl d).2 d.2, mul_one] at h1
      rw [h1]; exact v.intValuation_le_one n
    · have h1 := congrArg w hnd
      rw [Valuation.map_mul, hcomp d d.2] at h1
      have hn : w (algebraMap R K n) = 1 := by
        refine le_antisymm (hw n) ?_
        by_contra hlt
        push Not at hlt
        have : w x * w (algebraMap R K n) < 1 := lt_of_le_of_lt (mul_le_mul_left hx _) (by rwa [one_mul])
        rw [h1] at this; exact lt_irrefl _ this
      have hnc := hcomp' n hn
      have h2 := congrArg (v.valuation K) hnd
      rw [Valuation.map_mul, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.valuation_of_algebraMap,
        (v.intValuation_eq_one_iff_mem_primeCompl n).2 hnc,
        (v.intValuation_eq_one_iff_mem_primeCompl d).2 d.2, mul_one] at h2
      rw [h2]

/-- **O'Meara 22:10 (the spots of a Dedekind domain are unique).** Let $\mathfrak o$ be a Dedekind domain with
fraction field $F$. Every discrete spot $w$ of $F$ (a non-trivial valuation with values in $\mathbb Z_{m0}$) with
$\mathfrak o \subseteq \mathfrak o(w)$ is the spot of exactly one prime $\mathfrak p$ of $\mathfrak o$ (i.e. $w$ is
equivalent to $|\cdot|_{\mathfrak p}$ for a unique height-one prime $\mathfrak p$). Hence if
$\mathfrak o(S) = \mathfrak o(T) = \mathfrak o$ for sets $S, T$ of discrete spots, then each spot of $T$ lies in $S$ and
conversely, $S = T$: the set of spots of a Dedekind domain is determined by the domain. -/
@[kb "omeara1963" "§22F, 22:10, p. 52"]
theorem existsUnique_heightOneSpectrum_isEquiv (w : Valuation K ℤᵐ⁰) [w.IsNontrivial]
    (hw : ∀ r : R, w (algebraMap R K r) ≤ 1) :
    ∃! v : HeightOneSpectrum R, (v.valuation K).IsEquiv w :=
  ⟨⟨ltIdeal K w hw, ltIdeal_isPrime K w hw, ltIdeal_ne_bot K w hw⟩, isEquiv_of_ltIdeal K w hw,
    fun v' hv' => by
      have h := (isEquiv_of_ltIdeal K w hw)
      exact HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (hv'.trans h.symm)⟩

end Spots

section Extension

variable (A : Type*) [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
  [IsFractionRing A K] (L : Type*) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [Algebra.IsSeparable K L] [FiniteDimensional K L]
  (C : Type*) [CommRing C] [IsDomain C] [Algebra C L] [Algebra A C] [IsScalarTower A C L]
  [IsIntegralClosure C A L]

include A K

/-- **O'Meara 23:1.** Let $E/F$ be a finite separable extension, $\mathfrak o$ a Dedekind domain with fraction field
$F$ (the Dedekind set $S$) and $\mathfrak O$ the integral closure of $\mathfrak o$ in $E$ (so that the spots of $E$ over
$S$, $T \,\|\, S$, are the primes of $\mathfrak O$). Then $\mathfrak O$ is a Dedekind domain with fraction field $E$ and
$T$ satisfies the Dedekind axioms (D1)–(D3). -/
@[kb "omeara1963" "§23, 23:1, p. 52"]
theorem integralClosure_dedekindAxioms :
    ∃ _ : IsDedekindDomain C, ∃ _ : IsFractionRing C L, DedekindAxioms C L := by
  have hD : IsDedekindDomain C := IsIntegralClosure.isDedekindDomain A K L C
  have hF : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension A K L C
  exact ⟨hD, hF, dedekindAxioms L⟩

omit [IsDomain C] in
/-- **O'Meara 23:2.** In the situation of 23:1, for $\alpha \in E$ the following are equivalent:
(1) $\alpha \in \mathfrak o(T)$, i.e. $|\alpha|_{\mathfrak P} \le 1$ for every prime $\mathfrak P$ of $\mathfrak O$;
(2) the irreducible polynomial of $\alpha$ over $F$ has all its coefficients in $\mathfrak o = \mathfrak o(S)$;
(3) $\alpha$ satisfies a monic polynomial with coefficients in $\mathfrak o$.
(The instances `IsDedekindDomain C`, `IsFractionRing C L` hold by 23:1.) -/
@[kb "omeara1963" "§23, 23:2, p. 53"]
theorem tfae_integral_over [IsDedekindDomain C] [IsFractionRing C L] (α : L) :
    List.TFAE [∀ w : HeightOneSpectrum C, w.valuation L α ≤ 1,
      ∀ i, (minpoly K α).coeff i ∈ (algebraMap A K).range,
      ∃ p : Polynomial A, p.Monic ∧ Polynomial.aeval α p = 0] := by
  tfae_have 1 ↔ 3 := by
    rw [(ringOfIntegers_eq_and_isFractionRing (R := C) L).1 α]
    constructor
    · rintro ⟨c, rfl⟩
      exact (IsIntegralClosure.isIntegral A L c).algebraMap
    · rintro ⟨p, hp, hp0⟩
      exact (IsIntegralClosure.isIntegral_iff (R := A) (A := C) (B := L)).1 ⟨p, hp, hp0⟩
  tfae_have 3 → 2 := by
    rintro ⟨p, hp, hp0⟩ i
    have hint : IsIntegral A α := ⟨p, hp, hp0⟩
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hint]
    simp
  tfae_have 2 → 3 := by
    intro h
    have hl : minpoly K α ∈ Polynomial.lifts (algebraMap A K) :=
      Polynomial.lifts_iff_coeff_lifts _ |>.2 h
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl
      (minpoly.monic (Algebra.IsIntegral.isIntegral α))
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_map_algebraMap K, hq]
    exact minpoly.aeval K α
  tfae_finish

end Extension

end QuadFormsKB.OMeara
