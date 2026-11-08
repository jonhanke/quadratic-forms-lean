/-
# Hanke 2011 (enumerating maximal definite forms): the even-rank bounds (Lemmas 6.1, 7.3, 7.4)

J. Hanke, *Enumerating maximal definite quadratic forms of bounded class number over $\mathbb Z$ in $n\ge3$ variables*,
arXiv:1110.1876v1 (`hanke2011enumerating`), §6, pp. 9–10, and §7, pp. 11–13.

**Setting** as in `Bounds.lean`, with $n\ge4$ even: $\chi$ is the quadratic character of $\mathbb Q(\sqrt\delta)$,
$\delta = (-1)^{n/2}\det(H)/2^n$ (`discK`), $q = \mathrm{Cond}(\chi)$ = `condNorm Q₀` $=\prod_{v\text{ ramified}}p_v^{f_v}$
(`condFactor`, $f_v$ = `condExp` the conductor exponent), and $t$ = `numRam Q₀` the number of ramified primes, i.e. the
number of prime divisors of $\mathrm{Cond}(\chi)$; these are exactly the primes of Gan–Hanke–Yu mass-type III (`evenTypeAt_eq_III`).
$|L(1-r,\chi)|$ ($r = n/2$) is `absLNeg Q₀ r` $= q^{r-\frac12}\frac{2\,\Gamma(r)}{(2\pi)^r}L(r,\chi)$, i.e. it is *defined*
through the functional equation, which is exactly the relation the proof of Lemma 6.1 extracts from the functional
equation ("$2(2\pi)^{-r}q^{r-\frac12}\Gamma(r)|L(r,\chi)| = |L(1-r,\chi)|$").

**Proves.**
* **Lemma 6.1** for the character $\chi$ of $Q_0$ (`lemma_6_1`, `lemma_6_1_primePower`), by the paper's proof: the
  Euler-product bound $L(r,\chi)\ge\zeta(2r)/\zeta(r)$ (`NFEuler.zeta_ratio_pow_le_LFunctionNF`) and
  $q^{r-\frac12}/2^t = \prod_{p\mid q}p^{\mathrm{ord}_p(q)(r-\frac12)}/2$, each factor $>1$. The divisor $q'\mid q$ is given by
  its prime-power factors: a finite set $T$ of ramified primes and exponents $1\le e_v\le f_v$.
* **Lemma 7.4, $n$ even** (`lemma_7_4_prod_even`: (8); `lemma_7_4_even`: (7), with the factor $2^t$, see the *Erratum*
  in `Bounds.lean`).
* **Lemma 7.3** (`lemma_7_3`).

*Deviation (Lemma 6.1):* the paper states Lemma 6.1 for every primitive quadratic Dirichlet character, with
$L(1-r,\chi)$ the analytically continued value. Here it is proved for the characters $\chi$ of the forms $Q_0$ (the case
used in Lemma 7.3 and Thm 4.2), with $|L(1-r,\chi)|$ given by the functional-equation expression above; the comparison
with Mathlib's `DirichletCharacter.LFunction` (via `DirichletCharacter.IsPrimitive.completedLFunction_one_sub` and
$|\tau(\chi)| = \sqrt q$) is not formalized.
-/
import QuadFormsKB.Literature.Hanke2011Enumerating.Bounds

open NumberField IsDedekindDomain
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2011Enumerating

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Hanke2005

variable {n : ℕ}

/-! ### Ramified primes, the conductor and type III -/

section Ram

variable {F : Type} [Field F] [NumberField F]

/-- The conductor exponent $f_v$ of $\chi$ at $v$ (`condExp` of $\delta$, Gan–Hanke–Yu 2001 Lemma A.1(iv)). -/
abbrev condExpAt (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n) : ℕ :=
  condExp v (algebraMap F (v.adicCompletion F) (discK Q₀))

/-- Ramified places are not self-dual ($n$ even). -/
theorem dualIndexAt_ne_one_of_isRamifiedAt (heven : Even n) (Q₀ : QuadForm (𝓞 F) n)
    {v : HeightOneSpectrum (𝓞 F)} (h : IsRamifiedAt v Q₀) : dualIndexAt v Q₀ ≠ 1 := fun hd =>
  not_isRamifiedAt_of_dualIndexAt_eq_one v Q₀ heven hd h

/-- Only finitely many places are ramified in $F(\sqrt\delta)$ ($n$ even). -/
theorem finite_isRamifiedAt (heven : Even n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) :
    {v : HeightOneSpectrum (𝓞 F) | IsRamifiedAt v Q₀}.Finite :=
  (hasFiniteMulSupport_dualIndexAt Q₀ hQ).subset fun _ hv => dualIndexAt_ne_one_of_isRamifiedAt heven Q₀ hv

/-- **$t$, the number of primes dividing $\mathrm{Cond}(\chi)$** (Hanke 2011, proof of Thm 4.2, p. 7, and Lemma 7.3, p. 12):
the number of places ramified in $F(\sqrt\delta)$. -/
@[kb "hanke2011enumerating" "Thm 4.2 proof, p. 7; Lemma 7.3, p. 12 (t = number of prime divisors of Cond(χ))"]
def numRam (Q₀ : QuadForm (𝓞 F) n) : ℕ := Set.ncard {v : HeightOneSpectrum (𝓞 F) | IsRamifiedAt v Q₀}

/-- The Gan–Hanke–Yu mass-type at $v$ is III if and only if $v$ is ramified in $F(\sqrt\delta)$ (Hanke 2011, proof of Thm 4.2,
p. 7: "$E_\delta/\mathbb Q_p$ is ramified iff $p\mid\mathrm{Cond}(\chi)$"). -/
theorem evenTypeAt_eq_III (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) :
    evenTypeAt v Q₀ = .III ↔ IsRamifiedAt v Q₀ := by
  classical
  unfold evenTypeAt evenTypeOf
  constructor
  · intro h
    by_contra hr
    split_ifs at h <;> simp_all
  · intro hr
    rw [if_neg (not_isSquare_of_isRamifiedAt v Q₀ hQ hr), if_pos hr]

/-- At a ramified place the conductor exponent $f_v$ is $\ge1$ ($n\ge4$ even, $\mathcal O_F^n$ maximal): the dual index
there is $q_v^{f_v}$ (`ramifiedDualIndexConductor_proved`) and is $\ne1$. -/
theorem one_le_condExp (hn : 4 ≤ n) (heven : Even n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hmax : StdIsMaximal Q₀) {v : HeightOneSpectrum (𝓞 F)} (h : IsRamifiedAt v Q₀) :
    1 ≤ condExpAt v Q₀ := by
  by_contra h0
  push_neg at h0
  have he : condExpAt v Q₀ = 0 := by omega
  apply dualIndexAt_ne_one_of_isRamifiedAt heven Q₀ h
  rw [ramifiedDualIndexConductor_proved.dual_eq hn heven Q₀ hQ hmax v h]
  rw [show condExp v (algebraMap F (v.adicCompletion F) (discK Q₀)) = 0 from he, pow_zero]

/-- `condFactor` is $1$ off the (finite) ramified set. -/
theorem condFactor_eq_one_of_not (Q₀ : QuadForm (𝓞 F) n) {v : HeightOneSpectrum (𝓞 F)} (h : ¬ IsRamifiedAt v Q₀) :
    condFactor v Q₀ = 1 := by
  unfold condFactor; rw [if_neg h]

/-- $\mathrm{Cond}(\chi) = \prod_{v\text{ ramified}}q_v^{f_v}$, a finite product. -/
theorem condNorm_eq_prod (heven : Even n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) :
    condNorm Q₀ = ∏ v ∈ (finite_isRamifiedAt heven Q₀ hQ).toFinset,
      (normQ v) ^ condExpAt v Q₀ := by
  classical
  unfold condNorm
  rw [tprod_eq_prod (L := SummationFilter.unconditional _) (s := (finite_isRamifiedAt heven Q₀ hQ).toFinset)
    fun v hv => condFactor_eq_one_of_not Q₀ fun h => hv ((Set.Finite.mem_toFinset _).2 h)]
  refine Finset.prod_congr rfl fun v hv => ?_
  have hr : IsRamifiedAt v Q₀ := (Set.Finite.mem_toFinset _).1 hv
  unfold condFactor
  rw [if_pos hr]

theorem condNorm_pos (heven : Even n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) : 0 < condNorm Q₀ := by
  rw [condNorm_eq_prod heven Q₀ hQ]
  exact Finset.prod_pos fun v _ => pow_pos (lt_trans zero_lt_one (one_lt_normQ v)) _

theorem absLNeg_pos (heven : Even n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) {k : ℕ} (hk : 2 ≤ k) :
    0 < absLNeg Q₀ k := by
  unfold absLNeg
  have hD : 0 < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero F)
  have hc := condNorm_pos heven Q₀ hQ
  have hk' : (1 : ℝ) < k := by exact_mod_cast hk
  have hL := NFEuler.LFunctionNF_pos (fun v => abs_chiK_le v Q₀) hk'
  have hπ : 0 < Real.pi := Real.pi_pos
  have h1 : 0 < |(discr F : ℝ)| * condNorm Q₀ := mul_pos hD hc
  have h2 : 0 < (|(discr F : ℝ)| * condNorm Q₀) ^ ((k : ℝ) - 1 / 2) := Real.rpow_pos_of_pos h1 _
  positivity

end Ram

/-! ### Lemma 6.1 -/

section Lemma61

/-- **The prime-power factor** $p^{\nu(r-\frac12)}/2$ of $q^{r-\frac12}/2^t$ (Hanke 2011, Lemma 6.1, p. 10). -/
def ppFactor (p : ℝ) (ν r : ℕ) : ℝ := p ^ ((ν : ℝ) * ((r : ℝ) - 1 / 2)) / 2

theorem one_lt_ppFactor {p : ℝ} (hp : 2 ≤ p) {ν r : ℕ} (hν : 1 ≤ ν) (hr : 2 ≤ r) : 1 < ppFactor p ν r := by
  unfold ppFactor
  rw [lt_div_iff₀ (by norm_num), one_mul]
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hν' : (1 : ℝ) ≤ ν := by exact_mod_cast hν
  have hexp : (3 / 2 : ℝ) ≤ (ν : ℝ) * ((r : ℝ) - 1 / 2) := by nlinarith
  calc (2 : ℝ) < 2 ^ (3 / 2 : ℝ) := by
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one]
        have : (1 : ℝ) < 2 ^ (1 / 2 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
        linarith
    _ ≤ 2 ^ ((ν : ℝ) * ((r : ℝ) - 1 / 2)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ ≤ p ^ ((ν : ℝ) * ((r : ℝ) - 1 / 2)) := Real.rpow_le_rpow (by norm_num) hp (by linarith)

theorem ppFactor_mono {p : ℝ} (hp : 1 ≤ p) {ν ν' r : ℕ} (h : ν ≤ ν') (hr : 1 ≤ r) :
    ppFactor p ν r ≤ ppFactor p ν' r := by
  unfold ppFactor
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr' : (1 / 2 : ℝ) ≤ (r : ℝ) - 1 / 2 := by linarith
  have hh : (ν : ℝ) ≤ ν' := by exact_mod_cast h
  exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hp (by nlinarith)) (by norm_num)

variable {F : Type} [Field F] [NumberField F]

/-- **$q^{r-\frac12}/2^t = \prod_{p\mid q}p^{\mathrm{ord}_p(q)(r-\frac12)}/2$** (Hanke 2011, proof of Lemma 6.1, p. 10). -/
theorem condNorm_rpow_div (heven : Even n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (r : ℕ) :
    condNorm Q₀ ^ ((r : ℝ) - 1 / 2) / 2 ^ numRam Q₀ =
      ∏ v ∈ (finite_isRamifiedAt heven Q₀ hQ).toFinset,
        ppFactor (normQ v) (condExpAt v Q₀) r := by
  classical
  rw [condNorm_eq_prod heven Q₀ hQ, numRam, Set.ncard_eq_toFinset_card _ (finite_isRamifiedAt heven Q₀ hQ),
    ← Real.finsetProd_rpow _ _ (fun v _ => (pow_pos (lt_trans zero_lt_one (one_lt_normQ v)) _).le)]
  unfold ppFactor
  rw [Finset.prod_div_distrib, Finset.prod_const]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (lt_trans zero_lt_one (one_lt_normQ v)).le]

/-- **Lemma 6.1** (Hanke 2011, p. 10), for the quadratic character $\chi$ of $Q_0$ ($n\ge4$ even, $r = n/2$; *Deviation*,
see the module docstring). For every $K > 0$: if $q = \mathrm{Cond}(\chi)$ has a divisor $q' = \prod_{v\in T}p_v^{e_v}$
($T$ a set of ramified primes, $1\le e_v\le f_v = \mathrm{ord}_{p_v}(q)$) with
$$\prod_{p\mid q'}\frac{p^{\mathrm{ord}_p(q')(r-\frac12)}}2 > \frac{K\,(2\pi)^r\,\zeta(r)}{2\,\Gamma(r)\,\zeta(2r)},$$
then $|L(1-r,\chi)|/2^t > K$. ($\Gamma(r) = (r-1)!$, $\zeta$ = `NFEuler.zetaR`.) *Proof* (the paper's): $L(r,\chi)\ge
\zeta(2r)/\zeta(r)$ gives $|L(1-r,\chi)|\ge q^{r-\frac12}\cdot2\Gamma(r)\zeta(2r)/((2\pi)^r\zeta(r))$, and
$q^{r-\frac12}/2^t$ is the product of the factors $p^{\nu(r-\frac12)}/2 > 1$ over $p\mid q$, which only grows from $q'$
to $q$. -/
@[kb "hanke2011enumerating" "Lemma 6.1, p. 10"]
theorem lemma_6_1 (hn : 4 ≤ n) (heven : Even n) (Q₀ : QuadForm (𝓞 ℚ) n) (hQ : Q₀.Nondegenerate)
    (hmax : StdIsMaximal Q₀) {K : ℝ} (hK : 0 < K) (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hT : ∀ v ∈ T, IsRamifiedAt v Q₀) (e : HeightOneSpectrum (𝓞 ℚ) → ℕ) (he1 : ∀ v ∈ T, 1 ≤ e v)
    (hef : ∀ v ∈ T, e v ≤ condExpAt v Q₀)
    (hq' : K * (2 * Real.pi) ^ (n / 2) * NFEuler.zetaR (n / 2 : ℕ) /
        (2 * (Nat.factorial (n / 2 - 1) : ℝ) * NFEuler.zetaR (2 * (n / 2 : ℕ))) <
      ∏ v ∈ T, ppFactor (normQ v) (e v) (n / 2)) :
    K < absLNeg Q₀ (n / 2) / 2 ^ numRam Q₀ := by
  classical
  set r := n / 2 with hr
  have hr2 : 2 ≤ r := by omega
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr2
  set R := (finite_isRamifiedAt heven Q₀ hQ).toFinset
  have hTR : T ⊆ R := fun v hv => (Set.Finite.mem_toFinset _).2 (hT v hv)
  -- the product over q' is at most the product over q
  have hfac : ∀ v : HeightOneSpectrum (𝓞 ℚ), 2 ≤ normQ v := fun v => by
    have := NFEuler.two_le_normP v
    unfold normQ
    exact_mod_cast this
  have hprod : ∏ v ∈ T, ppFactor (normQ v) (e v) r ≤
      ∏ v ∈ R, ppFactor (normQ v) (condExpAt v Q₀) r := by
    rw [← Finset.prod_sdiff hTR]
    have h1 : ∏ v ∈ T, ppFactor (normQ v) (e v) r ≤
        ∏ v ∈ T, ppFactor (normQ v) (condExpAt v Q₀) r :=
      Finset.prod_le_prod₀ (fun v hv => (lt_trans zero_lt_one (one_lt_ppFactor (hfac v) (he1 v hv) hr2)).le)
        fun v hv => ppFactor_mono (by linarith [hfac v]) (hef v hv) (by omega)
    have h2 : 1 ≤ ∏ v ∈ R \ T, ppFactor (normQ v) (condExpAt v Q₀) r := by
      have := Finset.prod_le_prod₀ (s := R \ T) (f := fun _ => (1 : ℝ))
        (g := fun v => ppFactor (normQ v) (condExpAt v Q₀) r)
        (fun _ _ => zero_le_one) fun v hv => (one_lt_ppFactor (hfac v)
          (one_le_condExp hn heven Q₀ hQ hmax ((Set.Finite.mem_toFinset _).1 (Finset.mem_sdiff.1 hv).1)) hr2).le
      simpa using this
    have h0 : 0 ≤ ∏ v ∈ T, ppFactor (normQ v) (condExpAt v Q₀) r :=
      Finset.prod_nonneg fun v hv => (lt_trans zero_lt_one (one_lt_ppFactor (hfac v)
        (le_trans (he1 v hv) (hef v hv)) hr2)).le
    nlinarith
  rw [← condNorm_rpow_div heven Q₀ hQ r] at hprod
  -- the Euler-product lower bound
  have hL := NFEuler.zeta_ratio_pow_le_LFunctionNF (F := ℚ) (fun v => abs_chiK_le v Q₀) hr1
  rw [Module.finrank_self, pow_one] at hL
  have hz1 : 0 < NFEuler.zetaR r := lt_of_lt_of_le one_pos (NFEuler.one_le_zetaR hr1)
  have hz2 : 0 < NFEuler.zetaR (2 * (r : ℝ)) := lt_of_lt_of_le one_pos (NFEuler.one_le_zetaR (by linarith))
  have hπ : 0 < Real.pi := Real.pi_pos
  have hfact : (0 : ℝ) < Nat.factorial (r - 1) := by exact_mod_cast Nat.factorial_pos _
  have hq := condNorm_pos heven Q₀ hQ
  have hqr : 0 < condNorm Q₀ ^ ((r : ℝ) - 1 / 2) := Real.rpow_pos_of_pos hq _
  have h2t : (0 : ℝ) < 2 ^ numRam Q₀ := by positivity
  -- absLNeg = q^{r-1/2} * (2 (r-1)! / (2π)^r) * L(r, χ)
  have habs : absLNeg Q₀ r = condNorm Q₀ ^ ((r : ℝ) - 1 / 2) *
      (2 * (Nat.factorial (r - 1) : ℝ) / (2 * Real.pi) ^ r) * NFEuler.LFunctionNF (fun v => chiK v Q₀) r := by
    unfold absLNeg
    rw [Rat.numberField_discr, Int.cast_one, abs_one, one_mul, Module.finrank_self, pow_one]
  rw [habs]
  set A := condNorm Q₀ ^ ((r : ℝ) - 1 / 2) / 2 ^ numRam Q₀ with hA
  set C := K * (2 * Real.pi) ^ r * NFEuler.zetaR r / (2 * (Nat.factorial (r - 1) : ℝ) * NFEuler.zetaR (2 * (r : ℝ)))
    with hC
  have hzr : (NFEuler.zetaR (2 * (r : ℕ)) : ℝ) = NFEuler.zetaR (2 * (r : ℝ)) := rfl
  have hCA : C < A := by
    have := lt_of_lt_of_le hq' hprod
    simpa [hC, hA] using this
  -- K = C * (2 (r-1)! ζ(2r)) / ((2π)^r ζ(r))
  have hK' : K = C * (2 * (Nat.factorial (r - 1) : ℝ) * NFEuler.zetaR (2 * (r : ℝ))) /
      ((2 * Real.pi) ^ r * NFEuler.zetaR r) := by
    rw [hC]; field_simp
  have hpi : 0 < (2 * Real.pi) ^ r := by positivity
  have key : K < A * (2 * (Nat.factorial (r - 1) : ℝ) / (2 * Real.pi) ^ r) *
      (NFEuler.zetaR (2 * (r : ℝ)) / NFEuler.zetaR r) := by
    rw [hK']
    have hpos : 0 < 2 * (Nat.factorial (r - 1) : ℝ) * NFEuler.zetaR (2 * (r : ℝ)) / ((2 * Real.pi) ^ r *
        NFEuler.zetaR r) := by positivity
    have := mul_lt_mul_of_pos_right hCA hpos
    calc C * (2 * (Nat.factorial (r - 1) : ℝ) * NFEuler.zetaR (2 * (r : ℝ))) / ((2 * Real.pi) ^ r * NFEuler.zetaR r)
        = C * (2 * (Nat.factorial (r - 1) : ℝ) * NFEuler.zetaR (2 * (r : ℝ)) / ((2 * Real.pi) ^ r *
          NFEuler.zetaR r)) := by ring
      _ < A * (2 * (Nat.factorial (r - 1) : ℝ) * NFEuler.zetaR (2 * (r : ℝ)) / ((2 * Real.pi) ^ r *
          NFEuler.zetaR r)) := this
      _ = A * (2 * (Nat.factorial (r - 1) : ℝ) / (2 * Real.pi) ^ r) *
          (NFEuler.zetaR (2 * (r : ℝ)) / NFEuler.zetaR r) := by field_simp
  have hApos : 0 < A * (2 * (Nat.factorial (r - 1) : ℝ) / (2 * Real.pi) ^ r) := by positivity
  have := mul_le_mul_of_nonneg_left hL hApos.le
  calc K < _ := key
    _ ≤ A * (2 * (Nat.factorial (r - 1) : ℝ) / (2 * Real.pi) ^ r) *
        NFEuler.LFunctionNF (fun v => chiK v Q₀) r := this
    _ = _ := by rw [hA]; field_simp

end Lemma61

/-! ### Lemma 7.4 and Lemma 7.3, $n$ even -/

section Even

/-- **The exceptional primes** ($\lambda_{\mathrm{even},p} < 1$, Lemma 7.2) are the $t$ ramified primes and, for $n = 4$, at
most the prime $2$: any finite set of them has at most $t + [n = 4]$ elements. -/
theorem card_le_of_lambdaEven_lt_one (hn : 4 ≤ n) (heven : Even n) (Q₀ : QuadForm (𝓞 ℚ) n) (hQ : Q₀.Nondegenerate)
    (E : Finset (HeightOneSpectrum (𝓞 ℚ))) (hE : ∀ v ∈ E, lambdaEven (normQ v) n (evenTypeAt v Q₀) < 1) :
    E.card ≤ numRam Q₀ + (if n = 4 then 1 else 0) := by
  classical
  have h2 : ∀ v : HeightOneSpectrum (𝓞 ℚ), 2 ≤ NFEuler.normP v := fun v => NFEuler.two_le_normP v
  have hcase : ∀ v ∈ E, (n = 4 ∧ normQ v = 2) ∨ IsRamifiedAt v Q₀ := fun v hv => by
    rcases lemma_7_2_even (h2 v) hn heven _ (hE v hv) with ⟨h4, hp, -⟩ | h3
    · left
      refine ⟨h4, ?_⟩
      unfold normQ
      exact_mod_cast hp
    · exact Or.inr ((evenTypeAt_eq_III Q₀ hQ v).1 h3)
  rw [← Finset.card_filter_add_card_filter_not (s := E) (fun v => IsRamifiedAt v Q₀)]
  apply add_le_add
  · rw [numRam, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard (fun v hv => (Finset.mem_filter.1 hv).2) (finite_isRamifiedAt heven Q₀ hQ)
  · split_ifs with h4
    · refine Finset.card_le_one.2 fun a ha b hb => ?_
      have ha' := (hcase a (Finset.mem_filter.1 ha).1).resolve_right (Finset.mem_filter.1 ha).2
      have hb' := (hcase b (Finset.mem_filter.1 hb).1).resolve_right (Finset.mem_filter.1 hb).2
      exact eq_of_normQ_eq (ha'.2.trans hb'.2.symm)
    · refine le_of_eq (Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun a ha => ?_))
      have := (hcase a (Finset.mem_filter.1 ha).1).resolve_right (Finset.mem_filter.1 ha).2
      exact h4 this.1

theorem rpow_neg_half' (a : ℝ) : (2 : ℝ) ^ ((2 - a) / 2) = ((2 : ℝ) ^ ((a - 2) / 2))⁻¹ := by
  rw [← Real.rpow_neg (by norm_num)]; ring_nf

/-- From (2) and $\mathrm{Mass}^+\le h\le B$ ($n$ even):
$|L(1-\frac n2,\chi)|\prod_k|\zeta(1-2k)|\prod_p\lambda_{\mathrm{even},p}\le B\,2^{\frac{n-2}2}$. -/
theorem massPlus_even_le (hn : 4 ≤ n) (heven : Even n) (Q₀ : QuadForm (𝓞 ℚ) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 ℚ) ℚ))) (hmax : StdIsMaximal Q₀) {B : ℝ}
    (hB : (Lattices.classNumber (Q₀.map (algebraMap (𝓞 ℚ) ℚ)) (stdLat ℚ n) : ℝ) ≤ B) :
    absLNeg Q₀ (n / 2) * zetaProd ((n - 2) / 2) *
        ∏' v : HeightOneSpectrum (𝓞 ℚ), lambdaEven (normQ v) n (evenTypeAt v Q₀) ≤
      B * (2 : ℝ) ^ (((n : ℝ) - 2) / 2) := by
  have hM := massPlus_le_classNumber (by omega) Q₀ hQ hpd
  rw [mass_formula_even hn heven Q₀ hQ hpd hmax] at hM
  have hX := le_of_massPlus hM hB
  rw [rpow_neg_half'] at hX
  have h2 : 0 < (2 : ℝ) ^ (((n : ℝ) - 2) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have := mul_le_mul_of_nonneg_left hX h2.le
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ h2.ne', one_mul] at this
  unfold zetaProd
  linarith

/-- **Lemma 7.4, (8), $n$ even** (Hanke 2011, p. 13), with $B''$ multiplied by $B$ (*Erratum*, `Bounds.lean`): if
$h(L)\le B$ then $\prod_p\lambda_{\mathrm{even},p}\le B\cdot B''$. -/
@[kb "hanke2011enumerating" "Lemma 7.4, (8), p. 13 (n even)"]
theorem lemma_7_4_prod_even (hn : 4 ≤ n) (heven : Even n) (Q₀ : QuadForm (𝓞 ℚ) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 ℚ) ℚ))) (hmax : StdIsMaximal Q₀) {B : ℝ}
    (hB : (Lattices.classNumber (Q₀.map (algebraMap (𝓞 ℚ) ℚ)) (stdLat ℚ n) : ℝ) ≤ B) :
    ∏' v : HeightOneSpectrum (𝓞 ℚ), lambdaEven (normQ v) n (evenTypeAt v Q₀) ≤ B * bEven Q₀ := by
  have h := massPlus_even_le hn heven Q₀ hQ hpd hmax hB
  have hL := absLNeg_pos heven Q₀ hQ (k := n / 2) (by omega)
  have hZ := zetaProd_pos ((n - 2) / 2)
  unfold bEven
  rw [mul_div_assoc', le_div_iff₀ (mul_pos hL hZ)]
  linarith

/-- **Lemma 7.4, (7), $n$ even, corrected** (Hanke 2011, pp. 12–13; *Erratum*, `Bounds.lean`): if $h(L)\le B$ then
$\lambda_{\mathrm{even},p}\le\epsilon\,2^t\,B\,B''$ for every $p$, $t$ = `numRam Q₀`. *Proof*: (8) and Lemma 7.2 (the other
factors are $\ge1$ except the $t$ factors $\frac12$ of type III and, for $n = 4$, the factor at $2$, which is $\ge\frac12$). -/
@[kb "hanke2011enumerating" "Lemma 7.4, (7), pp. 12–13 (n even; with the factor 2^t)"]
theorem lemma_7_4_even (hn : 4 ≤ n) (heven : Even n) (Q₀ : QuadForm (𝓞 ℚ) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 ℚ) ℚ))) (hmax : StdIsMaximal Q₀) {B : ℝ}
    (hB : (Lattices.classNumber (Q₀.map (algebraMap (𝓞 ℚ) ℚ)) (stdLat ℚ n) : ℝ) ≤ B)
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    lambdaEven (normQ p) n (evenTypeAt p Q₀) ≤ epsilon n * 2 ^ numRam Q₀ * B * bEven Q₀ := by
  classical
  set f := fun v : HeightOneSpectrum (𝓞 ℚ) => lambdaEven (normQ v) n (evenTypeAt v Q₀) with hfdef
  have hf := hasFiniteMulSupport_lambdaEven hn heven Q₀ hQ hmax
  have hP := lemma_7_4_prod_even hn heven Q₀ hQ hpd hmax hB
  set E := hf.toFinset.filter fun v => f v < 1
  have hE : ∀ v ∈ E, 1 / 2 ≤ f v := fun v _ => half_le_lambdaEven (NFEuler.two_le_normP v) hn heven _
  have hnE : ∀ v, v ∉ E → 1 ≤ f v := fun v hv => by
    by_contra hlt
    push_neg at hlt
    exact hv (Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset _).2 (ne_of_lt hlt), hlt⟩)
  have hpos : ∀ v, 0 ≤ f v := fun v =>
    le_trans (by norm_num) (half_le_lambdaEven (NFEuler.two_le_normP v) hn heven (evenTypeAt v Q₀))
  have hmain := mul_pow_card_le_tprod hf (by norm_num : (0 : ℝ) ≤ 1 / 2) E hE hnE hpos p
  have hcard := card_le_of_lambdaEven_lt_one hn heven Q₀ hQ E fun v hv => (Finset.mem_filter.1 hv).2
  set m := numRam Q₀ + (if n = 4 then 1 else 0)
  have hpow : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ (E.erase p).card :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) ((Finset.card_erase_le).trans hcard)
  have hfp := hpos p
  have hm := mul_le_mul_of_nonneg_left hpow hfp
  have h2m : (2 : ℝ) ^ m = epsilon n * 2 ^ numRam Q₀ := by
    unfold epsilon
    simp only [m]
    split_ifs with h1 h2 h2
    · rw [pow_add, pow_one, mul_comm]
    · omega
    · omega
    · rw [add_zero, one_mul]
  have hhalf : (1 / 2 : ℝ) ^ m * 2 ^ m = 1 := by rw [← mul_pow]; norm_num
  have h2pos : (0 : ℝ) < 2 ^ m := by positivity
  rw [← h2m]
  have : f p * (1 / 2 : ℝ) ^ m ≤ B * bEven Q₀ := le_trans hm (le_trans hmain hP)
  have := mul_le_mul_of_nonneg_right this h2pos.le
  rw [mul_assoc, hhalf, mul_one] at this
  linarith

/-- **Lemma 7.3** (Hanke 2011, p. 12): for $n\ge4$ even and $h(L)\le B$,
$$\frac{|L(1-\frac n2,\chi)|}{2^t}\le\frac{B\,2^{\frac{n-2}2}}{\prod_{k=1}^{\frac{n-2}2}|\zeta(1-2k)|}\cdot\begin{cases}2&n = 4,\\
1&n\ge6,\end{cases}$$
$t$ = `numRam Q₀` the number of prime divisors of $\mathrm{Cond}(\chi)$ (the factor is `epsilon n`). *Proof* (the paper's):
(2) as (3), and $\prod_{p\nmid\mathrm{Cond}(\chi)}\lambda_{\mathrm{even},p}\ge\frac12$ ($n = 4$), $\ge1$ ($n\ge6$), by Lemma 7.2;
here in the form $\prod_p\lambda_{\mathrm{even},p}\ge2^{-t}\cdot(\frac12\text{ if }n = 4)$. -/
@[kb "hanke2011enumerating" "Lemma 7.3, (6), p. 12"]
theorem lemma_7_3 (hn : 4 ≤ n) (heven : Even n) (Q₀ : QuadForm (𝓞 ℚ) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 ℚ) ℚ))) (hmax : StdIsMaximal Q₀) {B : ℝ}
    (hB : (Lattices.classNumber (Q₀.map (algebraMap (𝓞 ℚ) ℚ)) (stdLat ℚ n) : ℝ) ≤ B) :
    absLNeg Q₀ (n / 2) / 2 ^ numRam Q₀ ≤
      B * (2 : ℝ) ^ (((n : ℝ) - 2) / 2) / zetaProd ((n - 2) / 2) * epsilon n := by
  classical
  set f := fun v : HeightOneSpectrum (𝓞 ℚ) => lambdaEven (normQ v) n (evenTypeAt v Q₀) with hfdef
  have hf := hasFiniteMulSupport_lambdaEven hn heven Q₀ hQ hmax
  have h := massPlus_even_le hn heven Q₀ hQ hpd hmax hB
  set E := hf.toFinset.filter fun v => f v < 1
  have hE : ∀ v ∈ E, 1 / 2 ≤ f v := fun v _ => half_le_lambdaEven (NFEuler.two_le_normP v) hn heven _
  have hnE : ∀ v, v ∉ E → 1 ≤ f v := fun v hv => by
    by_contra hlt
    push_neg at hlt
    exact hv (Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset _).2 (ne_of_lt hlt), hlt⟩)
  have hlow := pow_card_le_tprod hf (by norm_num : (0 : ℝ) ≤ 1 / 2) E hE hnE
  have hcard := card_le_of_lambdaEven_lt_one hn heven Q₀ hQ E fun v hv => (Finset.mem_filter.1 hv).2
  set m := numRam Q₀ + (if n = 4 then 1 else 0)
  have hpow : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ E.card := pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard
  have hL := absLNeg_pos heven Q₀ hQ (k := n / 2) (by omega)
  have hZ := zetaProd_pos ((n - 2) / 2)
  have hLZ : 0 < absLNeg Q₀ (n / 2) * zetaProd ((n - 2) / 2) := mul_pos hL hZ
  have h1 : absLNeg Q₀ (n / 2) * zetaProd ((n - 2) / 2) * (1 / 2 : ℝ) ^ m ≤ B * (2 : ℝ) ^ (((n : ℝ) - 2) / 2) :=
    le_trans (mul_le_mul_of_nonneg_left (hpow.trans hlow) hLZ.le) h
  have h2m : (2 : ℝ) ^ m = epsilon n * 2 ^ numRam Q₀ := by
    unfold epsilon
    simp only [m]
    split_ifs with h1 h2 h2
    · rw [pow_add, pow_one, mul_comm]
    · omega
    · omega
    · rw [add_zero, one_mul]
  have hhalf : (1 / 2 : ℝ) ^ m * 2 ^ m = 1 := by rw [← mul_pow]; norm_num
  have h2t : (0 : ℝ) < 2 ^ numRam Q₀ := by positivity
  have hε : 0 < epsilon n := by unfold epsilon; split_ifs <;> norm_num
  have h3 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 ^ m)
  rw [mul_assoc (absLNeg Q₀ (n / 2) * zetaProd ((n - 2) / 2)), hhalf, mul_one, h2m] at h3
  rw [div_le_iff₀ h2t, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hZ]
  nlinarith

end Even

/-! ### Theorem 4.2: the statement, and the bound on the eligible primes for odd $n$ -/

/-- **$\lambda_{\mathrm{odd},p}\ge\frac{p-1}2$ for the non-generic types** (types I, II$^\pm$; $p\ge2$, $n\ge3$ odd). -/
theorem lambdaOdd_ge_of_ne_gen {p : ℝ} (hp : 2 ≤ p) (hn : 3 ≤ n) (hodd : Odd n) {T : OddType} (hT : T ≠ .gen) :
    (p - 1) / 2 ≤ lambdaOdd p n T := by
  obtain ⟨k, rfl⟩ := hodd
  have hk : 1 ≤ k := by omega
  have e1 : 2 * k + 1 - 1 = 2 * k := by omega
  have e2 : (2 * k + 1 - 1) / 2 = k := by omega
  have hpk : p ≤ p ^ k := by simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p) hk
  have hp2k : p ^ 2 ≤ p ^ (2 * k) := pow_le_pow_right₀ (by linarith) (by omega)
  cases T with
  | gen => exact absurd rfl hT
  | I =>
    simp only [lambdaOdd, e1]
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  | IIplus => simp only [lambdaOdd, e2]; linarith
  | IIminus => simp only [lambdaOdd, e2]; linarith

/-- **The eligible primes are bounded, $n$ odd** (Hanke 2011, proof of Thm 4.2, p. 7: "there are only finitely many
primes $p$ where $0 < \lambda_{\mathrm{odd},p} < B'$"; with the bound of Lemma 7.4): if $h(L)\le B$, every prime $p$ at which
the Gan–Hanke–Yu mass-type of $Q_0$ is not generic satisfies $p\le2\,\epsilon\,B\,B''+1$. -/
@[kb "hanke2011enumerating" "Thm 4.2, proof, p. 7 (n odd: finitely many eligible primes)"]
theorem eligible_prime_bound_odd (hn : 3 ≤ n) (hodd : Odd n) (Q₀ : QuadForm (𝓞 ℚ) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 ℚ) ℚ))) (hmax : StdIsMaximal Q₀) {B : ℝ}
    (hB : (Lattices.classNumber (Q₀.map (algebraMap (𝓞 ℚ) ℚ)) (stdLat ℚ n) : ℝ) ≤ B)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hgen : oddTypeAt v Q₀ ≠ .gen) :
    normQ v ≤ 2 * epsilon n * B * bOdd n + 1 := by
  have h := lemma_7_4_odd hn hodd Q₀ hQ hpd hmax hB v
  have h2 : (2 : ℝ) ≤ normQ v := by have := NFEuler.two_le_normP v; unfold normQ; exact_mod_cast this
  have := lambdaOdd_ge_of_ne_gen h2 hn hodd hgen
  linarith

/-- $\mathrm{ppFactor}(p,\nu,r)^2\ge2$ for $p\ge2$, $\nu\ge1$, $r\ge2$. -/
theorem two_le_sq_ppFactor {p : ℝ} (hp : 2 ≤ p) {ν r : ℕ} (hν : 1 ≤ ν) (hr : 2 ≤ r) : 2 ≤ ppFactor p ν r ^ 2 := by
  unfold ppFactor
  set x : ℝ := (ν : ℝ) * ((r : ℝ) - 1 / 2)
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hν' : (1 : ℝ) ≤ ν := by exact_mod_cast hν
  have hx : (3 : ℝ) ≤ 2 * x := by
    have : (3 / 2 : ℝ) ≤ x := by
      calc (3 / 2 : ℝ) = 1 * (2 - 1 / 2) := by norm_num
        _ ≤ (ν : ℝ) * ((r : ℝ) - 1 / 2) := mul_le_mul hν' (by linarith) (by norm_num) (by linarith)
    linarith
  have hp0 : 0 ≤ p := by linarith
  have e : (p ^ x / 2) ^ 2 = p ^ (2 * x) / 4 := by
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp0]; norm_num [mul_comm]
  rw [e]
  have h8 : (8 : ℝ) ≤ p ^ (2 * x) :=
    calc (8 : ℝ) = 2 ^ (3 : ℝ) := by norm_num
      _ ≤ 2 ^ (2 * x) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hx
      _ ≤ p ^ (2 * x) := Real.rpow_le_rpow (by norm_num) hp (by linarith)
  linarith

/-- **Lemma 7.3, finiteness of the eligible characters** (Hanke 2011, p. 12: "Lemma 6.1 ... gives that there are only
finitely many such $\chi$"): for even $n\ge4$ and a bound $B$ there is $C$ such that every non-degenerate positive definite
$Q_0$ over $\mathbb Z$ in $n$ variables with $\mathbb Z^n$ maximal and class number $h\le B$ has a character $\chi$ of conductor
$\mathrm{Cond}(\chi)\le C$ (so only finitely many $\chi$ occur). *Proof*, the paper's: the bound (6) (`lemma_7_3`) and
Lemma 6.1 (`lemma_6_1`) with $q' = \mathrm{Cond}(\chi)$ bound $\mathrm{Cond}(\chi)^{r-\frac12}/2^t$; each prime factor contributes at
least $\sqrt2$, which bounds $2^t$ and then $\mathrm{Cond}(\chi)$. -/
@[kb "hanke2011enumerating" "Lemma 7.3, p. 12 (finitely many eligible χ, via Lemma 6.1)"]
theorem lemma_7_3_finite (hn : 4 ≤ n) (heven : Even n) (B : ℝ) :
    ∃ C : ℝ, ∀ Q₀ : QuadForm (𝓞 ℚ) n, Q₀.Nondegenerate → IsTotallyPosDef (Q₀.map (algebraMap (𝓞 ℚ) ℚ)) →
      StdIsMaximal Q₀ → (Lattices.classNumber (Q₀.map (algebraMap (𝓞 ℚ) ℚ)) (stdLat ℚ n) : ℝ) ≤ B →
      condNorm Q₀ ≤ C := by
  classical
  set K₀ := B * (2 : ℝ) ^ (((n : ℝ) - 2) / 2) / zetaProd ((n - 2) / 2) * epsilon n
  set K := max K₀ 1
  have hK : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  set D := K * (2 * Real.pi) ^ (n / 2) * NFEuler.zetaR (n / 2 : ℕ) /
    (2 * (Nat.factorial (n / 2 - 1) : ℝ) * NFEuler.zetaR (2 * (n / 2 : ℕ)))
  refine ⟨max 1 (D ^ 3), fun Q₀ hQ hpd hmax hB => ?_⟩
  set T := (finite_isRamifiedAt heven Q₀ hQ).toFinset
  have hr : 2 ≤ n / 2 := by omega
  have h2 : ∀ v : HeightOneSpectrum (𝓞 ℚ), (2 : ℝ) ≤ normQ v := fun v => by
    have := NFEuler.two_le_normP v; unfold normQ; exact_mod_cast this
  have hTram : ∀ v ∈ T, IsRamifiedAt v Q₀ := fun v hv => (Set.Finite.mem_toFinset _).1 hv
  have he1 : ∀ v ∈ T, 1 ≤ condExpAt v Q₀ := fun v hv => one_le_condExp hn heven Q₀ hQ hmax (hTram v hv)
  -- the product of the prime-power factors is at most `D`
  have hP : ∏ v ∈ T, ppFactor (normQ v) (condExpAt v Q₀) (n / 2) ≤ D := by
    by_contra hlt
    push Not at hlt
    have h61 := lemma_6_1 hn heven Q₀ hQ hmax hK T hTram (fun v => condExpAt v Q₀) he1 (fun _ _ => le_rfl) hlt
    have h73 := lemma_7_3 hn heven Q₀ hQ hpd hmax hB
    have : K₀ ≤ K := le_max_left _ _
    linarith
  have hpos : ∀ v ∈ T, 0 < ppFactor (normQ v) (condExpAt v Q₀) (n / 2) := fun v hv =>
    lt_trans one_pos (one_lt_ppFactor (h2 v) (he1 v hv) hr)
  have hD0 : 0 ≤ D := le_trans (Finset.prod_nonneg fun v hv => (hpos v hv).le) hP
  -- `2^t ≤ D²`
  have ht : (2 : ℝ) ^ numRam Q₀ ≤ D ^ 2 := by
    have hcard : numRam Q₀ = T.card := by
      unfold numRam; rw [Set.ncard_eq_toFinset_card _ (finite_isRamifiedAt heven Q₀ hQ)]
    rw [hcard, ← Finset.prod_const]
    calc ∏ _v ∈ T, (2 : ℝ) ≤ ∏ v ∈ T, ppFactor (normQ v) (condExpAt v Q₀) (n / 2) ^ 2 :=
          Finset.prod_le_prod₀ (fun _ _ => by norm_num) fun v hv => two_le_sq_ppFactor (h2 v) (he1 v hv) hr
      _ = (∏ v ∈ T, ppFactor (normQ v) (condExpAt v Q₀) (n / 2)) ^ 2 := Finset.prod_pow _ _ _
      _ ≤ D ^ 2 := pow_le_pow_left₀ (Finset.prod_nonneg fun v hv => (hpos v hv).le) hP 2
  -- `Cond(χ)^{r - 1/2} ≤ D³`
  have hc : condNorm Q₀ ^ (((n / 2 : ℕ) : ℝ) - 1 / 2) ≤ D ^ 3 := by
    have e := condNorm_rpow_div heven Q₀ hQ (n / 2)
    have h2t : (0 : ℝ) < 2 ^ numRam Q₀ := by positivity
    rw [div_eq_iff h2t.ne'] at e
    rw [e]
    calc (∏ v ∈ T, ppFactor (normQ v) (condExpAt v Q₀) (n / 2)) * 2 ^ numRam Q₀ ≤ D * D ^ 2 :=
          mul_le_mul hP ht h2t.le hD0
      _ = D ^ 3 := by ring
  have hc1 : 1 ≤ condNorm Q₀ := by
    rw [condNorm_eq_prod heven Q₀ hQ]
    calc (1 : ℝ) = ∏ _v ∈ T, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun v _ => one_le_pow₀ (by linarith [h2 v])
  have hexp : (1 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) - 1 / 2 := by
    have : (2 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hr
    linarith
  calc condNorm Q₀ = condNorm Q₀ ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ condNorm Q₀ ^ (((n / 2 : ℕ) : ℝ) - 1 / 2) := Real.rpow_le_rpow_of_exponent_le hc1 hexp
    _ ≤ D ^ 3 := hc
    _ ≤ max 1 (D ^ 3) := le_max_right _ _

/-- **Theorem 4.2** (Hanke 2011, p. 7), the statement: for each $n\ge3$ and $B$ there are only finitely many classes of
maximal $\mathbb Z$-valued positive definite forms in $n$ variables with class number $h\le B$: a finite list $S$ of forms
such that every nondegenerate positive definite $Q_0$ with $\mathbb Z^n$ maximal and $h(\mathbb Z^n)\le B$ is
$\mathbb Z$-equivalent (`IsometricIn (𝓞 ℚ)`) to a member of $S$. Field: `finite`. **Proved** (unconditionally) as
`theorem_4_2` in `Theorem42.lean`, through the bound on the Hessian determinant (`abs_det_le`) obtained from the bounds
of Lemmas 6.1, 7.3, 7.4 proved here. -/
@[kb "hanke2011enumerating" "Theorem 4.2, p. 7"]
structure Theorem42 : Prop where
  finite : ∀ n : ℕ, 3 ≤ n → ∀ B : ℝ, ∃ S : Finset (QuadForm (𝓞 ℚ) n), ∀ Q₀ : QuadForm (𝓞 ℚ) n,
    Q₀.Nondegenerate → IsTotallyPosDef (Q₀.map (algebraMap (𝓞 ℚ) ℚ)) → StdIsMaximal Q₀ →
    (Lattices.classNumber (Q₀.map (algebraMap (𝓞 ℚ) ℚ)) (stdLat ℚ n) : ℝ) ≤ B →
    ∃ Q' ∈ S, QuadForm.IsometricIn (𝓞 ℚ) Q₀ Q'

/-- **Theorem 7.5** (Hanke 2011, p. 13), as a **named statement** (the result of a computer enumeration, carried out
with the algorithm of §7; not proved here): there are exactly $115$ maximal $\mathbb Z$-valued positive definite quadratic
forms $Q$ in $n\ge3$ variables with class number $h(Q) = 1$, up to $\mathbb Z$-equivalence (they are listed in §8). Field
`enum`: a finite family $S$ of forms (each with its number of variables $n$) with $\#S = 115$, each member satisfying the
hypotheses ($n\ge3$, non-degenerate, positive definite, $\mathbb Z^n$ maximal, $h(\mathbb Z^n) = 1$), no two members
$\mathbb Z$-equivalent (`IsometricIn (𝓞 ℚ)`), and every form with these properties $\mathbb Z$-equivalent to a member.
Not used as a hypothesis anywhere. -/
@[kb "hanke2011enumerating" "Theorem 7.5, p. 13 (with the tables of §8, pp. 16–19)"]
structure Theorem75 : Prop where
  enum : ∃ S : Finset (Σ n : ℕ, QuadForm (𝓞 ℚ) n), S.card = 115 ∧
    (∀ x ∈ S, 3 ≤ x.1 ∧ x.2.Nondegenerate ∧ IsTotallyPosDef (x.2.map (algebraMap (𝓞 ℚ) ℚ)) ∧ StdIsMaximal x.2 ∧
      Lattices.classNumber (x.2.map (algebraMap (𝓞 ℚ) ℚ)) (stdLat ℚ x.1) = 1) ∧
    (∀ x ∈ S, ∀ y ∈ S, ∀ h : x.1 = y.1,
      QuadForm.IsometricIn (𝓞 ℚ) (h ▸ x.2 : QuadForm (𝓞 ℚ) y.1) y.2 → x = y) ∧
    ∀ n : ℕ, 3 ≤ n → ∀ Q₀ : QuadForm (𝓞 ℚ) n,
      Q₀.Nondegenerate → IsTotallyPosDef (Q₀.map (algebraMap (𝓞 ℚ) ℚ)) → StdIsMaximal Q₀ →
      Lattices.classNumber (Q₀.map (algebraMap (𝓞 ℚ) ℚ)) (stdLat ℚ n) = 1 →
      ∃ x ∈ S, ∃ h : x.1 = n, QuadForm.IsometricIn (𝓞 ℚ) Q₀ (h ▸ x.2 : QuadForm (𝓞 ℚ) n)

end QuadFormsKB.Hanke2011Enumerating
