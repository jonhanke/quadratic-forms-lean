/-
# O'Meara §31: rational global fields

**Setting.** The rational function field $k(x)$ = `RatFunc k` with integers $k[x]$ and the finite spots = height-one
primes of $k[x]$ (prime polynomials); the place at infinity is Mathlib's `RatFunc.inftyValuation`. The finite $k$ of
O'Meara's definition is not needed for these statements. Number fields: Mathlib's `NumberField`.

**Proves**
* 31:2 `ratFunc_dedekindAxioms` (function field case; the case of $\mathbb Q$ is `rat_dedekindAxioms`, 21:1);
* 31:3 `inftyValuation_le_one_iff`, `integral_everywhere_iff_const`;
* 31:4 (number case) `residue_card_int`;
* 31:6 `numberField_iff` (definition); 31:9 `numberField_finite_separable` (number field case only).

Not formalized: 31:5 (power series expansion of $p$-adic numbers), 31:7, 31:8 (definitions involving function
fields), the function field half of 31:9 (separable generation).
-/
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import QuadFormsKB.Literature.OMeara.Sec21
import QuadFormsKB.Citation

set_option linter.unusedSectionVars false

open IsDedekindDomain WithZero Polynomial
open scoped nonZeroDivisors

noncomputable section

namespace QuadFormsKB.OMeara

/-- **O'Meara 31:2** (function field case). For the rational function field $k(x)$ with integers $k[x]$, the set
of all finite spots (the primes of $k[x]$, i.e. the prime polynomials) is a Dedekind set, and
$k[x] = \mathfrak o(S)$. The number-field case $\mathbb Z \subset \mathbb Q$ is `rat_dedekindAxioms` (21:1). -/
@[kb "omeara1963" "§31, 31:2, p. 57 (rational function field)"]
theorem ratFunc_dedekindAxioms (k : Type*) [Field k] :
    DedekindAxioms k[X] (RatFunc k) ∧ ∀ x : RatFunc k,
      (∀ v : HeightOneSpectrum k[X], v.valuation (RatFunc k) x ≤ 1) ↔
        x ∈ (algebraMap k[X] (RatFunc k)).range :=
  ⟨dedekindAxioms (RatFunc k), (ringOfIntegers_eq_and_isFractionRing (R := k[X]) (RatFunc k)).1⟩

/-- **O'Meara 31:3.** In a rational function field $k(x)$ the polynomials integral at $\infty$ are exactly the
constants; consequently an element integral at all finite spots and at $\infty$ is a constant, so $k$ is the
intersection of the valuation rings of the spots (the finite spots and $\infty$ are all spots by 31:1). -/
@[kb "omeara1963" "§31, 31:3, p. 57"]
theorem inftyValuation_le_one_iff (k : Type*) [Field k] [DecidableEq (RatFunc k)] (f : k[X]) :
    RatFunc.inftyValuation k (algebraMap k[X] (RatFunc k) f) ≤ 1 ↔ f.natDegree = 0 := by
  by_cases hf : f = 0
  · simp [hf]
  rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation.polynomial k hf]
  rw [← exp_zero, exp_le_exp]
  omega

/-- **O'Meara 31:3** (the constant field). An element of $k(x)$ is integral at every finite spot and at $\infty$ if
and only if it is a constant. -/
@[kb "omeara1963" "§31, 31:3, p. 57 (k is the intersection of all valuation rings)"]
theorem integral_everywhere_iff_const (k : Type*) [Field k] [DecidableEq (RatFunc k)] (x : RatFunc k) :
    ((∀ v : HeightOneSpectrum k[X], v.valuation (RatFunc k) x ≤ 1) ∧
        RatFunc.inftyValuation k x ≤ 1) ↔ ∃ c : k, x = RatFunc.C c := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨f, rfl⟩ := ((ratFunc_dedekindAxioms k).2 x).1 h1
    have := (inftyValuation_le_one_iff k f).1 h2
    rw [natDegree_eq_zero] at this
    obtain ⟨c, rfl⟩ := this
    exact ⟨c, by simp⟩
  · rintro ⟨c, rfl⟩
    refine ⟨fun v => ?_, ?_⟩
    · have := (ratFunc_dedekindAxioms k).2 (RatFunc.C c)
      exact (this.2 ⟨Polynomial.C c, by simp⟩) v
    · have := (inftyValuation_le_one_iff k (Polynomial.C c)).2 (by simp)
      simpa using this

/-- **O'Meara 31:4** (number field case). For the finite spot of $\mathbb Q$ at a prime $p$, the residue class
field has $p$ elements and $0, 1, \dots, p-1$ is a representative set of $\mathbb Z$ modulo the prime. -/
@[kb "omeara1963" "§31, 31:4, p. 57 (number case)"]
theorem residue_card_int (v : HeightOneSpectrum ℤ) :
    ∃ p : ℕ, p.Prime ∧ v.asIdeal = Ideal.span {(p : ℤ)} ∧ Nat.card (ℤ ⧸ v.asIdeal) = p ∧
      ∀ x : ℤ, ∃ r : ℕ, r < p ∧ x - r ∈ v.asIdeal := by
  have hprime := Submodule.IsPrincipal.prime_generator_of_isPrime v.asIdeal v.ne_bot
  set g := Submodule.IsPrincipal.generator v.asIdeal
  have hg : v.asIdeal = Ideal.span {g} := Ideal.span_singleton_generator _ |>.symm
  have hp : (g.natAbs).Prime := Int.prime_iff_natAbs_prime.1 hprime
  have hspan : v.asIdeal = Ideal.span {((g.natAbs : ℕ) : ℤ)} := by
    rw [hg, Ideal.span_singleton_eq_span_singleton]
    exact Int.associated_natAbs g
  have : Fact (g.natAbs).Prime := ⟨hp⟩
  refine ⟨g.natAbs, hp, hspan, ?_, fun x => ?_⟩
  · rw [hspan]
    rw [Nat.card_congr (Int.quotientSpanNatEquivZMod g.natAbs).toEquiv]
    simp
  · refine ⟨(x % (g.natAbs : ℤ)).toNat, ?_, ?_⟩
    · have h1 := Int.emod_lt_of_pos x (by exact_mod_cast hp.pos : (0 : ℤ) < g.natAbs)
      have h2 := Int.emod_nonneg x (by exact_mod_cast hp.ne_zero : (g.natAbs : ℤ) ≠ 0)
      omega
    · rw [hspan, Ideal.mem_span_singleton]
      have h2 := Int.emod_nonneg x (by exact_mod_cast hp.ne_zero : (g.natAbs : ℤ) ≠ 0)
      rw [Int.toNat_of_nonneg h2]
      exact ⟨x / g.natAbs, by rw [Int.emod_def]; ring⟩

/-- **O'Meara 31:6** (definition, in Mathlib's terms). A number field is a finite extension of a rational number
field (a prime field of characteristic $0$, i.e. $\mathbb Q$): a field of characteristic $0$ that is finite
dimensional over $\mathbb Q$ (`NumberField F`). -/
@[kb "omeara1963" "§31, 31:6, p. 58"]
theorem numberField_iff (F : Type*) [Field F] [CharZero F] :
    NumberField F ↔ FiniteDimensional ℚ F :=
  ⟨fun h => h.to_finiteDimensional, fun _ => ⟨⟩⟩

/-- **O'Meara 31:9** (number field case). A number field is a finite separable extension of the rational number
field $\mathbb Q$. (The function field case, which is the content of the book's proof, is not formalized.) -/
@[kb "omeara1963" "§31, 31:9, p. 58 (number field case)"]
theorem numberField_finite_separable (F : Type*) [Field F] [NumberField F] :
    FiniteDimensional ℚ F ∧ Algebra.IsSeparable ℚ F :=
  ⟨inferInstance, inferInstance⟩

end QuadFormsKB.OMeara
