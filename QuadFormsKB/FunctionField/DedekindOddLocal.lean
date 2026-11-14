/-
# The odd local theory at the finite places of every global function field

**Theorem** (`FF.oddLocalAxioms_adicCompletion`): let $R$ be a Dedekind domain with fraction field $K$ and $w$ a
height-one prime of $R$ with finite residue field $R/w$ in which $2 \ne 0$. Then the completion $K_w$ satisfies the
odd local axioms `FF.OddLocalAxioms`, hence (`OddLocal.lean`, `OddLocalClassification.lean`) the Hilbert symbol of
$K_w$ is multiplicative, every $5$-dimensional form over $K_w$ is isotropic, and nondegenerate forms over $K_w$ are
classified by dimension, discriminant and Hasse invariant. This is the proof of
`RatFuncPlace.oddLocalAxioms_finite` (round 1, for $R = k[t]$) for an arbitrary Dedekind domain.

**Application to function fields** (`FunctionFieldPlace.oddLocalAxioms`): for a finite field $k$ of odd
characteristic and a finite separable extension $F$ of $k(t)$ (a global function field, Mathlib's
`FunctionField k F`), the residue fields of the ring of integers $\mathcal{O}_F$ (the integral closure of $k[t]$,
`FunctionField.ringOfIntegers k F`) are finite (`finite_quotient`), so the odd local theory holds at every finite
place of $F$: O'Meara 63:11 (multiplicativity), 63:19 (five-dimensional forms) and 63:20 (classification) for the
completions of $F$ at the places of $\mathcal{O}_F$. The places of $F$ above $\infty$ are not in Mathlib.

Indices are 0-based.
-/
import QuadFormsKB.FunctionField.OddLocalClassification

open IsDedekindDomain WithZero Polynomial

namespace QuadFormsKB.FF

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (w : HeightOneSpectrum R)

/-- An element of $K$ with $v_w(y) \le 1$ is a quotient $a / s$ with $a, s \in R$, $s \notin w$. -/
lemma exists_mul_eq_of_valuation_le_one (y : K) (hy : w.valuation K y ≤ 1) :
    ∃ a s : R, s ∉ w.asIdeal ∧ y * algebraMap R K s = algebraMap R K a := by
  have hy' : y ∈ HeightOneSpectrum.valuationSubringAtPrime K w := by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]; exact hy
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.mk'_surjective w.asIdeal.primeCompl
    (⟨y, hy'⟩ : HeightOneSpectrum.valuationSubringAtPrime K w)
  have h2 := IsLocalization.mk'_spec (HeightOneSpectrum.valuationSubringAtPrime K w) a s
  simp only at h
  rw [h] at h2
  exact ⟨a, s, s.2, congrArg Subtype.val h2⟩

/-- **The odd local axioms at a non-dyadic place with finite residue field** of the fraction field of a Dedekind
domain (O'Meara §63, for the completion $K_w$). -/
@[kb "omeara1963" "§63A–63B (non-dyadic local fields) [unverified]; serre1973 Ch. II §3.3, Ch. III §1.2 [unverified]"]
theorem oddLocalAxioms_adicCompletion [Finite (R ⧸ w.asIdeal)] (h2 : (2 : R) ∉ w.asIdeal) :
    OddLocalAxioms (w.adicCompletion K) := by
  have := w.isMaximal
  letI : Field (R ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  set ρ : R →+* w.adicCompletion K := (algebraMap K (w.adicCompletion K)).comp (algebraMap R K) with hρ
  have hρv : ∀ p, Valued.v (ρ p) = w.intValuation p := by
    intro p
    rw [hρ, RingHom.comp_apply, valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  set μ : R →+* R ⧸ w.asIdeal := Ideal.Quotient.mk w.asIdeal
  have hker : ∀ r, μ r = 0 ↔ Valued.v (ρ r) < 1 := by
    intro r
    rw [hρv, HeightOneSpectrum.intValuation_lt_one_iff_mem, Ideal.Quotient.eq_zero_iff_mem]
  have hκ : ringChar (R ⧸ w.asIdeal) ≠ 2 := by
    intro h
    have h0 : ((2 : ℕ) : R ⧸ w.asIdeal) = 0 := by rw [← h]; exact ringChar.Nat.cast_ringChar
    apply h2
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact_mod_cast h0
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer K
  have hπ' : ∃ π : w.adicCompletion K, Valued.v π = exp (-1 : ℤ) :=
    ⟨algebraMap _ _ π, by rw [valued_algebraMap, hπ]⟩
  refine oddLocalAxioms_of_residue hκ ρ μ Ideal.Quotient.mk_surjective
    (fun r => by rw [hρv]; exact w.intValuation_le_one r) hker hπ' ?_
  intro y hy
  obtain ⟨g, hg⟩ := RatFuncPlace.exists_near (algebraMap K (w.adicCompletion K))
    (HeightOneSpectrum.denseRange_algebraMap K w) y
  have hgv : Valued.v (algebraMap K (w.adicCompletion K) g) ≤ 1 := RatFuncPlace.v_le_one_of_near hy hg
  rw [valued_algebraMap] at hgv
  obtain ⟨b, s, hs, hgs⟩ := exists_mul_eq_of_valuation_le_one w g hgv
  obtain ⟨t, i, hi, hti⟩ := Ideal.IsMaximal.exists_inv w.isMaximal hs
  refine ⟨t * b, RatFuncPlace.near_trans hg ?_⟩
  rw [hρ, RingHom.comp_apply, ← map_sub, valued_algebraMap]
  have hi' : w.valuation K (algebraMap R K i) < 1 := (w.valuation_lt_one_iff_mem i).mpr hi
  have e : g - algebraMap R K (t * b) = g * algebraMap R K i := by
    have e1 : algebraMap R K t * algebraMap R K s + algebraMap R K i = 1 := by
      rw [← map_mul, ← map_add, hti, map_one]
    rw [map_mul]
    linear_combination (-g) * e1 + algebraMap R K t * hgs
  rw [e, map_mul]
  calc w.valuation K g * w.valuation K (algebraMap R K i) ≤ 1 * w.valuation K (algebraMap R K i) := by
        gcongr
    _ < 1 := by rw [one_mul]; exact hi'

end QuadFormsKB.FF

namespace QuadFormsKB.FunctionFieldPlace

variable (k : Type) [Field k] (F : Type) [Field F] [Algebra k[X] F] [Algebra (RatFunc k) F]
  [IsScalarTower k[X] (RatFunc k) F] [FunctionField k F] [Algebra.IsSeparable (RatFunc k) F]

local notation "𝒪" => FunctionField.ringOfIntegers k F

/-- **The residue fields of a global function field are finite:** for $k$ finite and $F/k(t)$ finite separable,
$\mathcal{O}_F / w$ is finite for every height-one prime $w$ of the integral closure $\mathcal{O}_F$ of $k[t]$
($\mathcal{O}_F / w$ is a finite module over $k[t]/(w \cap k[t])$, which is finite since $w \cap k[t] \ne 0$). -/
theorem finite_quotient [Finite k] (w : HeightOneSpectrum 𝒪) : Finite (𝒪 ⧸ w.asIdeal) := by
  have hne : w.asIdeal.under k[X] ≠ ⊥ := Ideal.IsIntegral.under_ne_bot k[X] w.ne_bot
  have hprime : (w.asIdeal.under k[X]).IsPrime := Ideal.IsPrime.under k[X] w.asIdeal
  haveI : Finite (k[X] ⧸ w.asIdeal.under k[X]) :=
    RatFuncPlace.finite_quotient ⟨w.asIdeal.under k[X], hprime, hne⟩
  have : Module.Finite k[X] 𝒪 := Module.IsNoetherian.finite k[X] 𝒪
  exact Module.finite_of_finite (k[X] ⧸ w.asIdeal.under k[X])

/-- **The odd local axioms at every finite place of a global function field of odd characteristic**: for $k$
finite with $\operatorname{char} k \ne 2$, $F/k(t)$ finite separable and $w$ a height-one prime of
$\mathcal{O}_F$, the completion $F_w$ satisfies `FF.OddLocalAxioms`. -/
@[kb "omeara1963" "§63A–63B (non-dyadic local fields; completions of a global function field) [unverified]"]
theorem oddLocalAxioms [Finite k] (hk : ringChar k ≠ 2) (w : HeightOneSpectrum 𝒪) :
    FF.OddLocalAxioms (w.adicCompletion F) := by
  have := finite_quotient k F w
  refine FF.oddLocalAxioms_adicCompletion w fun h => w.isPrime.ne_top ?_
  refine Ideal.eq_top_of_isUnit_mem _ h ?_
  have hu : IsUnit (C (2 : k)) := isUnit_C.mpr (Ring.two_ne_zero hk).isUnit
  have : (2 : 𝒪) = algebraMap k[X] 𝒪 (C 2) := by rw [map_ofNat C, map_ofNat]
  rw [this]
  exact hu.map _

/-- **The local Hilbert symbol is multiplicative at every finite place of a global function field** of odd
characteristic (O'Meara 63:11 for the completions $F_w$, $w$ a place of $\mathcal{O}_F$). -/
@[kb "omeara1963" "§63B, 63:11 (completions of a global function field) [unverified]"]
theorem hilbertSymbol_mul_left [Finite k] (hk : ringChar k ≠ 2) (w : HeightOneSpectrum 𝒪)
    (a b c : w.adicCompletion F) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    hilbertSymbol (w.adicCompletion F) (a * b) c =
      hilbertSymbol (w.adicCompletion F) a c * hilbertSymbol (w.adicCompletion F) b c :=
  (oddLocalAxioms k F hk w).hilbertSymbol_mul_left a b c ha hb hc

/-- **Five-dimensional forms are isotropic at every finite place of a global function field** of odd
characteristic (O'Meara 63:19 for $F_w$): every diagonal form $\langle a_0, \dots, a_4 \rangle$ with $a_i \ne 0$ is
isotropic over $F_w$. -/
@[kb "omeara1963" "§63C, 63:19 (completions of a global function field) [unverified]"]
theorem isotropic_five [Finite k] (hk : ringChar k ≠ 2) (w : HeightOneSpectrum 𝒪)
    (a : Fin 5 → w.adicCompletion F) (ha : ∀ i, a i ≠ 0) :
    (QuadForm.diag a).IsotropicIn (w.adicCompletion F) :=
  (oddLocalAxioms k F hk w).isotropic_five a ha

/-- **Local classification at every finite place of a global function field** of odd characteristic (O'Meara
63:20 for $F_w$): two nondegenerate diagonal forms over $F_w$ are isometric iff they have the same discriminant (up
to squares) and the same Hasse invariant. -/
@[kb "omeara1963" "§63C, 63:20, p. 170 (completions of a global function field)"]
theorem isometric_iff_invariants [Finite k] (hk : ringChar k ≠ 2) (w : HeightOneSpectrum 𝒪)
    {n : ℕ} {a b : Fin n → w.adicCompletion F} (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    (QuadForm.diag a).IsometricIn (w.adicCompletion F) (QuadForm.diag b) ↔
      (∃ t, t ≠ 0 ∧ ∏ i, b i = t ^ 2 * ∏ i, a i) ∧
        PadicClass.hasseVec a = PadicClass.hasseVec b := by
  have h := oddLocalAxioms k F hk w
  have : NeZero (2 : w.adicCompletion F) := ⟨h.two_ne_zero⟩
  have : Infinite (w.adicCompletion F) :=
    Infinite.of_injective (((algebraMap F (w.adicCompletion F)).comp (algebraMap (RatFunc k) F)).comp
      (algebraMap k[X] (RatFunc k)))
      (((algebraMap F _).comp (algebraMap (RatFunc k) F)).injective.comp
        (IsFractionRing.injective k[X] (RatFunc k)))
  exact PadicClass.isometric_iff_invariants h.localHilbertField ha hb

end QuadFormsKB.FunctionFieldPlace
