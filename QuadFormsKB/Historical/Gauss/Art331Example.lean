import QuadFormsKB.Historical.Gauss.SectionSix

/-!
# Gauss, *Disquisitiones Arithmeticae* Art. 331: the six residues of $997331$ leave only the prime $127$
.  Gauss shows that the residues $-6, 13, -14, 17, 37, -53$ of $997331$ exclude every
odd prime below $998$ except $127$ (a prime divisor of $997331$ must have each of them as a quadratic residue).

**Proved** (`art331_only_127`): if $p < 998$ is an odd prime that divides none of the six numbers and none of them
is a quadratic non-residue of $p$, then $p = 127$.  The finite computation (`art331_survivors`) is a Boolean
function (Euler's criterion by `Nat.pow` and `%`, plus trial division), evaluated by the kernel
with `decide +kernel` (no `native_decide`), and bridged to the Legendre symbol by Euler's criterion.
-/

namespace QuadFormsKB.Historical.Gauss

/-- Trial division: $p$ has no divisor $d$ with $2 \le d < p$. -/
def trialDivisionPrime (p : ℕ) : Bool := (List.range p).all fun d => decide (d < 2) || decide (p % d ≠ 0)

/-- The Boolean test for the primes surviving Gauss's six residues: $p \ne 2$, for each residue $r$ of the list,
$p \nmid r$ and $(r \bmod p)^{\lfloor p/2 \rfloor} \equiv 1 \pmod p$ (Euler's criterion), and $p$ is prime. -/
def art331Survives (p : ℕ) : Bool :=
  decide (3 ≤ p) &&
    art331Residues.all (fun r => decide (r % (p : ℤ) ≠ 0) &&
      decide ((r % (p : ℤ)).toNat ^ (p / 2) % p = 1)) &&
    trialDivisionPrime p

/-- **The surviving primes below $998$ are exactly $[127]$**, by kernel evaluation. -/
theorem art331_survivors : (List.range 998).filter art331Survives = [127] := by
  decide +kernel

/-- Euler's criterion in the form used by the Boolean test. -/
theorem pow_mod_eq_one_of_legendreSym_ne {p : ℕ} [hf : Fact p.Prime] {r : ℤ} (hr : ¬ (p : ℤ) ∣ r)
    (hl : legendreSym p r ≠ -1) : ((r % (p : ℤ)).toNat ^ (p / 2)) % p = 1 := by
  have hp : p.Prime := hf.out
  have ha0 : (r : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hr
  have hl1 : legendreSym p r = 1 := (legendreSym.eq_one_or_neg_one p ha0).resolve_right hl
  have hpow := legendreSym.eq_pow p r
  rw [hl1] at hpow
  have hcast : (r : ZMod p) = (((r % p).toNat : ℕ) : ZMod p) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.ne_zero)),
      ZMod.intCast_mod]
  have h1 : ((((r % (p : ℤ)).toNat ^ (p / 2) : ℕ)) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    rw [Nat.cast_pow, ← hcast, ← hpow]; simp
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
  exact Eq.trans (show _ % p = 1 % p from h2) (Nat.mod_eq_of_lt hp.one_lt)

/-- **Only $127$ survives** (*Disq. Arith.* Art. 331): if $p < 998$ is an odd prime that
divides none of $-6, 13, -14, 17, 37, -53$ and for which none of them is a quadratic non-residue
($\left(\frac{r}{p}\right) \ne -1$), then $p = 127$.  Since a prime divisor of $997331$ must have each of the six as
a quadratic residue (`art331_prime_legendreSym`), the only possible prime factor of $997331$ below $998$ is $127$. -/
@[kb "gauss1801" "Art. 331"]
theorem art331_only_127 {p : ℕ} [hf : Fact p.Prime] (hp2 : p ≠ 2) (hlt : p < 998)
    (hnd : ∀ r ∈ art331Residues, ¬ (p : ℤ) ∣ r)
    (hleg : ∀ r ∈ art331Residues, legendreSym p r ≠ -1) : p = 127 := by
  have hp : p.Prime := hf.out
  have hs : art331Survives p = true := by
    unfold art331Survives trialDivisionPrime
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true]
    refine ⟨⟨by have := hp.two_le; omega, fun r hr => ⟨fun h => hnd r hr (Int.dvd_of_emod_eq_zero h),
      pow_mod_eq_one_of_legendreSym_ne (hnd r hr) (hleg r hr)⟩⟩, fun d hd => ?_⟩
    have hdp := List.mem_range.1 hd
    by_cases h2 : d < 2
    · exact Or.inl h2
    · refine Or.inr fun h0 => ?_
      rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero h0) with h | h <;> omega
  have hmem : p ∈ (List.range 998).filter art331Survives :=
    List.mem_filter.2 ⟨List.mem_range.2 hlt, hs⟩
  rw [art331_survivors] at hmem
  simpa using hmem

end QuadFormsKB.Historical.Gauss
