/-
# Cassels, Chapter 9, §6: quantitative study of representations

**Layer:** integer-valued forms `f : QuadForm ℤ n`; representations of $a$: vectors $b \in \mathbb Z^n$ with
$f(b) = a$ (`Siegel.repSet`); *primitive* representations: $\gcd(b_0, \dots, b_{n-1}) = 1$ (`primRepSet`, Cassels'
footnote p. 130); their number `primRepNum` (as `Nat.card`, $0$ for an infinite set); orbits of representations under
the proper automorphs $O^{+}(f)$ = `AutPlus f` (`SameOrbit`, (6.3)).

**Proves**
* Lemma 6.1 for positive definite forms (`finite_orbits_of_posDef`): the representations of $a$ fall into finitely many
  orbits (there are finitely many representations);
* Lemma 6.5 (`primRepNum_sumSq_four`): for $a > 0$ odd and squarefree the number of primitive representations of $a$ as
  a sum of four squares is $8\prod_{p \mid a}(p + 1)$. *Proof (not Cassels'):* for squarefree $a$ every representation
  is primitive, and Jacobi's four-square theorem (`repNum_sumSq_four_odd`, $r_4(a) = 8\sigma(a)$) gives the count;
  Cassels derives it from Lemma 6.2 and the weight of a ternary genus (Lemma 6.6).
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec1
import QuadFormsKB.Siegel.FourSquaresJacobi

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

variable {n : ℕ}

/-! ### Primitive representations and orbits -/

/-- **The primitive representations of $a$ by $f$:** $b \in \mathbb Z^n$ with $f(b) = a$ and
$\gcd(b_0, \dots, b_{n-1}) = 1$ (Cassels, Ch. 9, §1, footnote p. 130: *a representation $b$ is primitive if the
vector $b$ is primitive*, and §2: $b$ is primitive iff its coordinates are coprime). -/
@[kb "cassels1978" "Ch. 9, §1, p. 130, footnote (primitive representation)"]
def primRepSet (f : QuadForm ℤ n) (a : ℤ) : Set (Fin n → ℤ) := {b | Finset.univ.gcd b = 1 ∧ f.eval b = a}

/-- **The number of primitive representations** of $a$ by $f$ (`Nat.card`; $0$ if there are infinitely many). -/
def primRepNum (f : QuadForm ℤ n) (a : ℤ) : ℕ := Nat.card (primRepSet f a)

/-- **Representations in the same orbit** (Cassels, Ch. 9, §6, (6.3), p. 144): $b^{*} = Tb$ for some proper
integral automorph $T \in O^{+}(f)$. An equivalence relation; $f(b^{*}) = f(b)$ (6.4). -/
@[kb "cassels1978" "Ch. 9, §6, (6.1)–(6.4), p. 144 (orbits of representations under O⁺(f))"]
def SameOrbit (f : QuadForm ℤ n) (b b' : Fin n → ℤ) : Prop := ∃ T ∈ AutPlus f, b' = T.val *ᵥ b

theorem SameOrbit.eval_eq {f : QuadForm ℤ n} {b b' : Fin n → ℤ} (h : SameOrbit f b b') : f.eval b' = f.eval b := by
  obtain ⟨T, hT, rfl⟩ := h
  exact ((mem_autPlus_iff.mp hT).1 b)

/-- Being in the same orbit is an equivalence relation (Cassels, p. 144: *this is clearly an equivalence relation*). -/
theorem equivalence_sameOrbit (f : QuadForm ℤ n) : Equivalence (SameOrbit f) where
  refl b := ⟨1, (AutPlus f).one_mem, by simp⟩
  symm := by
    rintro b b' ⟨T, hT, rfl⟩
    refine ⟨T⁻¹, (AutPlus f).inv_mem hT, ?_⟩
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  trans := by
    rintro b b' b'' ⟨T, hT, rfl⟩ ⟨T', hT', rfl⟩
    exact ⟨T' * T, (AutPlus f).mul_mem hT' hT, by rw [Units.val_mul, mulVec_mulVec]⟩

/-- The orbits as a setoid on the representations of $a$. -/
def orbitSetoid (f : QuadForm ℤ n) (a : ℤ) : Setoid (repSet f a) where
  r b b' := SameOrbit f b.1 b'.1
  iseqv := ⟨fun b => (equivalence_sameOrbit f).refl b.1, fun h => (equivalence_sameOrbit f).symm h,
    fun h h' => (equivalence_sameOrbit f).trans h h'⟩

/-- **Cassels, Lemma 6.1** (Ch. 9, p. 144), positive definite case: *the set of representations of $a$ falls into
finitely many orbits* (here there are only finitely many representations, `IntQF.PosDef.repSet_finite`). For
indefinite forms the statement is not formalized. -/
@[kb "cassels1978" "Ch. 9, Lemma 6.1, p. 144 (positive definite case)"]
theorem finite_orbits_of_posDef {f : QuadForm ℤ n} (hf : IntQF.PosDef f) (a : ℤ) :
    Finite (Quotient (orbitSetoid f a)) := by
  have : Finite (repSet f a) := (IntQF.PosDef.repSet_finite hf a).to_subtype
  exact Quotient.finite _

/-! ### Lemma 6.5 -/

/-- For squarefree $a \ne 0$ every representation of $a$ is primitive. -/
theorem gcd_eq_one_of_squarefree {f : QuadForm ℤ n} {b : Fin n → ℤ} {a : ℤ} (ha : Squarefree a)
    (hb : f.eval b = a) : Finset.univ.gcd b = 1 := by
  set g := Finset.univ.gcd b
  choose k hk using fun i => Finset.gcd_dvd (s := Finset.univ) (f := b) (Finset.mem_univ i)
  have hbk : b = g • k := funext fun i => by rw [Pi.smul_apply, smul_eq_mul, ← hk i]
  have hdvd : g * g ∣ a := by
    have e : f.eval (g • k) = g ^ 2 * f.eval k := by
      simp only [QuadForm.eval, QuadForm.evalIn, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp; ring
    rw [← hb, hbk, e]
    exact ⟨f.eval k, by ring⟩
  have hu := ha g hdvd
  have hnn : 0 ≤ g := Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd (s := Finset.univ) (f := b))
  rcases Int.isUnit_iff.mp hu with h | h
  · exact h
  · omega

/-- **Cassels, Lemma 6.5** (Ch. 9, p. 152): *let $a > 0$ be odd and squarefree. Then the number of primitive
representations of $a$ by $f(\mathbf x) = x_1^2 + x_2^2 + x_3^2 + x_4^2$ (6.43) is $8\prod_{p \mid a}(p + 1)$ (6.44),
where $p$, as always, denotes a prime.* (The formula (6.44) is garbled in the scan; it is the value forced by Lemma 6.6
and $\rho(\mathcal F, \mathcal G) = 2^\alpha$, and agrees with Jacobi's theorem.) -/
@[kb "cassels1978" "Ch. 9, Lemma 6.5, p. 152"]
theorem primRepNum_sumSq_four {a : ℕ} (ha : Odd a) (hsq : Squarefree a) :
    primRepNum (sumSq 4) a = 8 * ∏ p ∈ a.primeFactors, (p + 1) := by
  have hsqZ : Squarefree (a : ℤ) := Int.squarefree_natCast.mpr hsq
  have hset : primRepSet (sumSq 4) a = repSet (sumSq 4) a := by
    ext b
    exact ⟨fun h => h.2, fun h => ⟨gcd_eq_one_of_squarefree hsqZ h, h⟩⟩
  rw [primRepNum, hset, ← repNum, repNum_sumSq_four_odd ha, ArithmeticFunction.sigma_one_apply,
    Nat.sum_divisors ha.pos.ne']
  congr 1
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp' := Nat.prime_of_mem_primeFactors hp
  rw [Nat.factorization_eq_one_of_squarefree hsq hp' (Nat.dvd_of_mem_primeFactors hp)]
  simp [Finset.sum_range_succ, add_comm]

end QuadFormsKB.Siegel
