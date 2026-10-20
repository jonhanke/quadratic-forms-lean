/-
# Hanke, AWS 2009 notes, §4.3: the adelic exponential is trivial on $\mathbb{Q}$

J. Hanke, *Quadratic Forms and Automorphic Forms* (bibkey `hanke2011aws`), §4.3, p. 59. The list
D1, D2, … of the notes' derivations is in `AWS/Overview.lean`; this file is **D13**.

The notes define $e_\mathbb{A}((x_v)_v) := e^{2\pi i x_\infty}\prod_p e^{-2\pi i\,\mathrm{Frac}_p(x_p)}$,
"where $\mathrm{Frac}_p(x_p) \in \mathbb{Q}/\mathbb{Z}$ is defined as any rational number with $p$-power
denominator for which $x_p \in \mathrm{Frac}_p(x_p) + \mathbb{Z}_p$", and state that the Weil
representation formulas "are also visibly trivial on elements of $\mathrm{Sp}_2(F)$, because the adelic
absolute value $|\cdot|_\mathbb{A}$, the rational Hilbert symbol $(\cdot,\cdot)_F := \prod_v(\cdot,\cdot)_{F_v}$,
and the adelic exponential $e_\mathbb{A}(\cdot)$ are all trivial on rational elements".

- `sub_sum_frac_isInt`: for $x \in \mathbb{Q}$ and any admissible choices $r_p = \mathrm{Frac}_p(x)$,
  $x - \sum_p r_p \in \mathbb{Z}$; hence `adelicExp_rat`: $e_\mathbb{A}(x) = 1$.
- `chiV_rat`: the Hilbert symbol part, from the repo's Hilbert reciprocity (`hilbert_product_formula`).

*Update (candidate; pending author):* p. 59 says the Weil representation $\mathcal{W} :
\mathrm{Sp}_2(F)\backslash\mathrm{Sp}_2(\mathbb{A}) \to \mathrm{GL}(S(V_\mathbb{A}))$ and that the formulas are
"visibly trivial on elements of $\mathrm{Sp}_2(F)$". $\mathcal{W}$ is a representation of
$\mathrm{Sp}_2(\mathbb{A})$ (of its metaplectic cover for odd $n$); it is **not** trivial on
$\mathrm{Sp}_2(F)$: e.g. $\mathcal{W}(n(x))\Phi(\vec v) = e_\mathbb{A}(xQ(\vec v))\Phi(\vec v)$ for $x \in F$,
$\vec v \in V_\mathbb{A}$. What is trivial on rational elements are the scalar factors
$\chi_V(a)|a|^{n/2}_\mathbb{A}$ ($a \in F^\times$) and $e_\mathbb{A}(xQ(\vec v))$ for $\vec v \in V(F)$, so the
**theta distribution** $\theta(\Phi) = \sum_{\vec v \in V(F)}\Phi(\vec v)$ is $\mathrm{Sp}_2(F)$-invariant
(Lemma 4.4.1, with Poisson summation for formula 3).

*Erratum (candidate; pending author):* p. 59, the additive Haar measure $d_\mathbb{A}\vec v$ is "normalized
so that $\mathrm{Vol}(V_\mathbb{A}) = 1$"; $V_\mathbb{A}$ has infinite volume. The intended normalization is
$\mathrm{Vol}(V_\mathbb{A}/V(F)) = 1$ (the self-dual measure for $e_\mathbb{A}(H(\vec v,\vec w))$).
Also Remark 4.3.1, p. 59: "$\Phi_v$ is the characteristic function of $\mathbb{Z}_p$" should read
$\mathbb{Z}_p^n$ (or $L_p$).
-/
import QuadFormsKB.Literature.AWS.Adelic
import QuadFormsKB.Literature.LocalGlobal.HilbertReciprocity

open Complex

namespace QuadFormsKB.AWS

/-- A rational number whose denominator is prime to $q$ is $q$-integral. -/
theorem mem_subring_of_not_dvd {q : ℕ} [Fact q.Prime] {a : ℚ} (h : ¬ q ∣ a.den) :
    (a : ℚ_[q]) ∈ PadicInt.subring q := by
  rw [PadicInt.mem_subring_iff]; exact Padic.norm_rat_le_one h

/-- A prime $q$ does not divide a power of a different prime $p$. -/
theorem not_dvd_pow_of_ne {p q k : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : q ≠ p) : ¬ q ∣ p ^ k := by
  intro h
  exact hne ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h))

/-- **D13 (§4.3, p. 59): $x - \sum_p \mathrm{Frac}_p(x) \in \mathbb{Z}$ for $x \in \mathbb{Q}$.** Let $S$ be a finite
set of primes containing every prime dividing the denominator of $x$, and for $p \in S$ let $r_p$ be a
rational with $p$-power denominator and $x - r_p \in \mathbb{Z}_p$ (an admissible $\mathrm{Frac}_p(x)$; for
$p \notin S$ one may take $\mathrm{Frac}_p(x) = 0$). Then $x - \sum_{p \in S} r_p$ is an integer. -/
@[kb "hanke2011aws" "§4.3, p. 59"]
theorem sub_sum_frac_isInt (x : ℚ) (S : Finset ℕ) (hSp : ∀ p ∈ S, p.Prime)
    (hS : ∀ p, p.Prime → p ∣ x.den → p ∈ S) (r : ℕ → ℚ) (hr : ∀ p ∈ S, ∃ k, (r p).den = p ^ k)
    (hx : ∀ p ∈ S, ¬ p ∣ (x - r p).den) : ∃ z : ℤ, x - ∑ p ∈ S, r p = z := by
  classical
  rw [rat_isInt_iff]
  intro q
  have hq : (q : ℕ).Prime := q.2
  -- every r p with p ≠ q is q-integral
  have hrq : ∀ p ∈ S, p ≠ (q : ℕ) → ((r p : ℚ) : ℚ_[(q : ℕ)]) ∈ PadicInt.subring (q : ℕ) := by
    intro p hp hne
    obtain ⟨k, hk⟩ := hr p hp
    apply mem_subring_of_not_dvd
    rw [hk]; exact not_dvd_pow_of_ne (hSp p hp) hq (Ne.symm hne)
  have key : (((x - ∑ p ∈ S, r p : ℚ)) : ℚ_[(q : ℕ)]) ∈ PadicInt.subring (q : ℕ) := by
    by_cases hqS : (q : ℕ) ∈ S
    · have e : x - ∑ p ∈ S, r p = (x - r q) - ∑ p ∈ S.erase q, r p := by
        rw [← Finset.add_sum_erase S r hqS]; ring
      rw [e]; push_cast
      refine Subring.sub_mem _ ?_ (Subring.sum_mem _ fun p hp => ?_)
      · exact_mod_cast mem_subring_of_not_dvd (hx q hqS)
      · exact hrq p (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp)
    · push_cast
      refine Subring.sub_mem _ ?_ (Subring.sum_mem _ fun p hp => ?_)
      · exact mem_subring_of_not_dvd fun hd => hqS (hS q hq hd)
      · exact hrq p hp fun h => hqS (h ▸ hp)
  rwa [PadicInt.mem_subring_iff] at key

/-- **D13: the adelic exponential is trivial on $\mathbb{Q}$** (p. 59): for $x \in \mathbb{Q}$ embedded
diagonally, $e_\mathbb{A}(x) = e^{2\pi i x}\prod_{p \in S} e^{-2\pi i\,\mathrm{Frac}_p(x)} = 1$. -/
@[kb "hanke2011aws" "§4.3, p. 59"]
theorem adelicExp_rat (x : ℚ) (S : Finset ℕ) (hSp : ∀ p ∈ S, p.Prime)
    (hS : ∀ p, p.Prime → p ∣ x.den → p ∈ S) (r : ℕ → ℚ) (hr : ∀ p ∈ S, ∃ k, (r p).den = p ^ k)
    (hx : ∀ p ∈ S, ¬ p ∣ (x - r p).den) :
    cexp (2 * Real.pi * I * (x : ℂ)) * ∏ p ∈ S, cexp (-2 * Real.pi * I * (r p : ℂ)) = 1 := by
  obtain ⟨z, hz⟩ := sub_sum_frac_isInt x S hSp hS r hr hx
  rw [← Complex.exp_sum, ← Complex.exp_add]
  have : 2 * Real.pi * I * (x : ℂ) + ∑ p ∈ S, -2 * Real.pi * I * (r p : ℂ) =
      (z : ℂ) * (2 * Real.pi * I) := by
    have hz' : ((x - ∑ p ∈ S, r p : ℚ) : ℂ) = (z : ℂ) := by exact_mod_cast hz
    push_cast at hz'
    rw [← Finset.mul_sum, ← hz']
    ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

/-- **D13, the Hilbert-symbol part (p. 59):** $\chi_V(a) = (a, (-1)^{n/2}\det Q)_F :=
\prod_v (a, (-1)^{n/2}\det Q)_v$ is trivial on $a \in \mathbb{Q}^\times$: the places where the local
symbol is $-1$ are finite in number and even in number. This is Hilbert reciprocity over $\mathbb{Q}$,
proved in this repo (`hilbert_product_formula`). -/
@[kb "hanke2011aws" "§4.3, p. 59"]
theorem chiV_rat (a d : ℚ) (ha : a ≠ 0) (hd : d ≠ 0) :
    {v : RatPlace | v.hilbert a d = -1}.Finite ∧ Even {v : RatPlace | v.hilbert a d = -1}.ncard :=
  hilbert_product_formula a d ha hd

end QuadFormsKB.AWS
