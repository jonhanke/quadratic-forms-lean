/-
# Cassels, Chapter 11, Theorem 1.3: integer forms at the primes of $\mathbb Q$

**Layer:** an integer-valued form $f$ = `f : QuadForm ℤ n`, the space $V = (\mathbb Q^n, f)$
(`f.map (Int.castRingHom ℚ)`), a finite prime $v$ of $\mathbb Q$ with prime number $p$ =
`Rat.HeightOneSpectrum.natGenerator v`, the completion $\mathbb Q_v$.

**Proves** the translations used in the proof of Theorem 1.3 (`Ch11Thm13.lean`): $\lvert z\rvert_v \le \lvert p\rvert^k$
iff $p^k \mid z$ (`valued_intCast_le_iff`); $v \mid 2$ iff $p = 2$; $f$ is integral on $\mathbb Z_p^n$; the Gram matrix
of the standard basis is the Hessian of $f$.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec3DyadicCor

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-! ### Integer forms at the primes of $\mathbb Q$ -/

section Helpers

variable {n : ℕ}

private theorem asIdeal_eq_span (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ)} := by
  have h := Rat.HeightOneSpectrum.span_natGenerator v
  have h2 : v.asIdeal = (v.asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))).comap
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) :=
    (Ideal.comap_map_of_bijective _ (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).bijective).symm
  rw [← h] at h2
  rw [h2]
  ext x
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  have e1 : Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) =
      ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) := map_natCast _ _
  rw [← e1]
  exact map_dvd_iff _

/-- $\lvert z\rvert_v \le \lvert p\rvert_v^k$ iff $p^k \mid z$, for $z \in \mathbb Z$ and $p$ the prime of $v$. -/
theorem valued_intCast_le_iff (v : HeightOneSpectrum (𝓞 ℚ)) (z : ℤ) (k : ℕ) :
    Valued.v ((z : v.adicCompletion ℚ)) ≤ exp (-(k : ℤ)) ↔
      ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) ^ k ∣ z := by

  have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (z : 𝓞 ℚ)
  have hz : Valued.v ((z : ℤ) : v.adicCompletion ℚ) = v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ (z : 𝓞 ℚ)) := by
    rw [← h1]
    congr 1
    simp
  rw [hz, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_le_pow_iff_dvd, asIdeal_eq_span, Ideal.span_singleton_pow,
    Ideal.span_singleton_dvd_span_singleton_iff_dvd, ← map_dvd_iff (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))]
  simp

/-- $v \mid 2$ iff the prime of $v$ is $2$. -/
theorem two_mem_iff_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    (2 : 𝓞 ℚ) ∈ v.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator v = 2 := by

  have hp := Rat.HeightOneSpectrum.prime_natGenerator v
  rw [asIdeal_eq_span, Ideal.mem_span_singleton, ← map_dvd_iff (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))]
  have e2 : Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) (2 : 𝓞 ℚ) = ((2 : ℕ) : ℤ) := by
    rw [Nat.cast_ofNat]; exact map_ofNat _ 2
  rw [map_natCast, e2, Int.natCast_dvd_natCast]
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two)

/-- An integer-valued form takes integral values on $\mathfrak o_v^n$. -/
theorem valued_evalIn_le_one_int (v : HeightOneSpectrum (𝓞 ℚ)) (f : QuadForm ℤ n)
    {x : Fin n → v.adicCompletion ℚ} (hx : x ∈ std v) :
    Valued.v ((f.map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) x) ≤ 1 := by

  rw [mem_std_iff] at hx
  unfold QuadForm.evalIn
  refine Valuation.map_sum_le _ fun i _ => Valuation.map_sum_le _ fun j _ => ?_
  split_ifs
  · have hc : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((f.map (Int.castRingHom ℚ)).coeff i j)) ≤ 1 := by
      have : algebraMap ℚ (v.adicCompletion ℚ) ((f.map (Int.castRingHom ℚ)).coeff i j) =
          ((f.coeff i j : ℤ) : v.adicCompletion ℚ) := by simp [QuadForm.map]
      rw [this]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers (K := ℚ) (v := v)).1
        (intCast_mem (v.adicCompletionIntegers ℚ) (f.coeff i j))
    rw [map_mul, map_mul]
    exact mul_le_one' (mul_le_one' hc (hx i)) (hx j)
  · simp

/-- The Gram matrix of the standard basis is the Hessian $H$ of $f$. -/
theorem locGram_one_int (v : HeightOneSpectrum (𝓞 ℚ)) (f : QuadForm ℤ n) (k l : Fin n) :
    locGram (f.map (Int.castRingHom ℚ)) v 1 k l = ((f.hessian k l : ℤ) : v.adicCompletion ℚ) := by

  simp [locGram, QuadForm.hessian, QuadForm.map]

theorem locGram_one_int_det (v : HeightOneSpectrum (𝓞 ℚ)) (f : QuadForm ℤ n) :
    (locGram (f.map (Int.castRingHom ℚ)) v 1).det = ((f.hessian.det : ℤ) : v.adicCompletion ℚ) := by
  have : locGram (f.map (Int.castRingHom ℚ)) v 1 = f.hessian.map (Int.castRingHom (v.adicCompletion ℚ)) := by
    ext k l; rw [locGram_one_int]; rfl
  rw [this]; exact (RingHom.map_det (Int.castRingHom (v.adicCompletion ℚ)) f.hessian).symm

end Helpers

end QuadFormsKB.Lattices
