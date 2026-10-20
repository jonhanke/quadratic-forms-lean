/-
# Hanke, AWS 2009 notes, §2.7: the sum of four squares via Siegel's formula

J. Hanke, *Quadratic Forms and Automorphic Forms* (bibkey `hanke2011aws`), §2.7.2–§2.7.5,
pp. 36–40. The list D1, D2, … of the notes' derivations is in `AWS/Overview.lean`; this file is
**D4, D6, D7**.

$Q = x^2 + y^2 + z^2 + w^2$ (`Q4`), $r_Q(m) = \#\{\vec x \in \mathbb{Z}^4 : Q(\vec x) = m\}$ (`r4`), and
$\beta_p(m)$ is this repo's local density `LocalDensity.localDensity` (Hanke 2004, (5.1)–(5.2); the
notes' (2.7) and Lemma 2.7.2 are the same limit).

- **Lemma 2.7.4** (p. 38–39), for odd $p$: **proved** from the repo's local-density theory
  (`beta_odd_unit`, `beta_odd_ord_one`, from `LocalDensity.localDensity_diag_even_unit` and
  `LocalDensity.localDensity_diag_even_ord_one`).
- (2.9) (p. 37): `betaInf_calc`, the algebra $\frac{\pi^2}{2}\cdot\frac{(m+\varepsilon)^2-(m-\varepsilon)^2}{2\varepsilon}
  = \pi^2 m$ (exact for every $\varepsilon \ne 0$, so the limit is immediate).
- **(2.10)–(2.23)**, relative to `FourSquaresInputs` (Siegel's formula for $Q$, whose class number is
  one, with $\beta_\infty(m) = \pi^2 m$, and Lemma 2.7.6 at $p = 2$, odd $m$):
  `r4_one` ($r_Q(1) = 8$), `r4_prime` ($r_Q(p) = 8(p+1)$), `r4_squarefree`
  ($r_Q(t) = 8\prod_{p\mid t}(p+1)$ for odd squarefree $t$), using Mathlib's Euler product and
  $\zeta(2) = \pi^2/6$.
- `FourSquaresInputs` is **proved** (`Siegel.fourSquaresInputs`, `Siegel/FourSquaresSiegel.lean`): $\beta_p(m)$ for all
  $p$ and $m$ (`Siegel.localDensity_Q4_odd`, `Siegel.localDensity_Q4_two_nat`) with Jacobi's theorem give Siegel's
  formula for $Q$ (`Siegel.fourSquares_siegel`). So (2.10)–(2.23) hold unconditionally.
-/
import QuadFormsKB.LocalDensity.LowerBounds
import QuadFormsKB.Literature.AWS.Adelic

open Complex

namespace QuadFormsKB.AWS

/-- **The sum of four squares** $Q = x_0^2 + x_1^2 + x_2^2 + x_3^2$. -/
def Q4 : QuadForm ℤ 4 := QuadForm.diag fun _ => 1

/-- $r_Q(m) = \#\{\vec x \in \mathbb{Z}^4 : x_0^2 + x_1^2 + x_2^2 + x_3^2 = m\}$. -/
noncomputable def r4 (m : ℕ) : ℕ := Nat.card {x : Fin 4 → ℤ // Q4.eval x = m}

/-- **Lemma 2.7.4 (p. 38), $p \nmid m$:** $\beta_p(m) = 1 - 1/p^2$ for odd primes $p$. Proved from the
repo's formalization of Hanke 2004 (Table 1 / Remark 3.4.1(a)). -/
@[kb "hanke2011aws" "§2.7.4, Lemma 2.7.4, p. 38"]
theorem beta_odd_unit (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (m : ℤ) (hm : ¬ (p : ℤ) ∣ m) :
    LocalDensity.localDensity Q4 p m = 1 - 1 / (p : ℝ) ^ 2 := by
  have := LocalDensity.localDensity_diag_even_unit (fun _ : Fin 4 => (1 : ℤ)) p hp
    (fun _ => by
      intro h
      have := Int.eq_one_of_dvd_one (by positivity) h
      exact (Fact.out : p.Prime).one_lt.ne' (by exact_mod_cast this))
    (by norm_num) (by decide) m hm
  rw [Q4, this]
  simp [legendreSym.at_one]

/-- **Lemma 2.7.4 (p. 38), $p \mid m$, $p^2 \nmid m$:** $\beta_p(m) = (1 - 1/p^2)(1 + 1/p)$ for odd $p$. -/
@[kb "hanke2011aws" "§2.7.4, Lemma 2.7.4, p. 38"]
theorem beta_odd_ord_one (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (m : ℤ) (h1 : (p : ℤ) ∣ m)
    (h2 : ¬ (p : ℤ) ^ 2 ∣ m) :
    LocalDensity.localDensity Q4 p m = (1 - 1 / (p : ℝ) ^ 2) * (1 + 1 / (p : ℝ)) := by
  have := LocalDensity.localDensity_diag_even_ord_one (fun _ : Fin 4 => (1 : ℤ)) p hp
    (fun _ => by
      intro h
      have := Int.eq_one_of_dvd_one (by positivity) h
      exact (Fact.out : p.Prime).one_lt.ne' (by exact_mod_cast this))
    (by norm_num) (by decide) m h1 h2
  rw [Q4, this]
  simp [legendreSym.at_one]

/-- **(2.9), p. 37: the archimedean density.** With $\mathrm{Vol}(B_{4,r}) = \frac{\pi^2}{2}r^4$ and
$U_\varepsilon = (m-\varepsilon, m+\varepsilon)$,
$\frac{\mathrm{Vol}(Q^{-1}(U_\varepsilon))}{\mathrm{Vol}(U_\varepsilon)} =
\frac{\frac{\pi^2}{2}\bigl(\sqrt{m+\varepsilon}^4 - \sqrt{m-\varepsilon}^4\bigr)}{2\varepsilon} = \pi^2 m$
for every $0 < \varepsilon \le m$ (so $\beta_\infty(m) = \pi^2 m$). -/
@[kb "hanke2011aws" "§2.7.2, (2.9), p. 37"]
theorem betaInf_calc (m ε : ℝ) (hε : 0 < ε) (hεm : ε ≤ m) :
    (Real.pi ^ 2 / 2) * (Real.sqrt (m + ε) ^ 4 - Real.sqrt (m - ε) ^ 4) / (2 * ε) =
      Real.pi ^ 2 * m := by
  have h1 : Real.sqrt (m + ε) ^ 4 = (m + ε) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by linarith)]
  have h2 : Real.sqrt (m - ε) ^ 4 = (m - ε) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by linarith)]
  rw [h1, h2]
  field_simp
  ring

/-- **The inputs for §2.7.5** (pp. 39–40):

- `siegel`: **Siegel's formula** (Theorem 2.5.1) for $Q = x^2+y^2+z^2+w^2$, which has class number
  $h_Q = 1$ (so $a_E(m) = r_Q(m)$, p. 36), with $\beta_\infty(m) = \pi^2 m$ ((2.9), `betaInf_calc`):
  $r_Q(m) = \pi^2 m \prod_p \beta_p(m)$ for $m \ge 1$ (the product as a `tprod` over the primes).
  Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. of Math. 36 (1935); the notes
  §2.5.
- `beta_two`: **Lemma 2.7.6** (p. 39) for odd $m$: $\beta_2(m) = 1$ (by enumerating $(\mathbb{Z}/8)^4$;
  not yet derived here from the local-density theory). -/
structure FourSquaresInputs : Prop where
  siegel : ∀ m : ℕ, 0 < m →
    (r4 m : ℂ) = ((Real.pi ^ 2 * m : ℝ) : ℂ) *
      ∏' p : PrimeIdx, ((LocalDensity.localDensity Q4 p m : ℝ) : ℂ)
  beta_two : ∀ m : ℕ, Odd m → LocalDensity.localDensity Q4 2 m = 1

/-- $\prod_p (1 - p^{-2}) = 1/\zeta(2) = 6/\pi^2$ (Mathlib's Euler product and $\zeta(2) = \pi^2/6$). -/
theorem hasProd_one_sub_inv_sq :
    HasProd (fun p : PrimeIdx => (1 - 1 / ((p : ℕ) : ℂ) ^ 2)) (6 / (Real.pi : ℂ) ^ 2) := by
  have hz : HasProd (fun p : PrimeIdx => (1 - ((p : ℕ) : ℂ) ^ (-(2 : ℂ)))⁻¹) (riemannZeta 2) :=
    riemannZeta_eulerProduct_hasProd (s := 2) (by norm_num)
  have hz0 : riemannZeta 2 ≠ 0 := by
    rw [riemannZeta_two]
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact div_ne_zero (pow_ne_zero _ this) (by norm_num)
  have h := hz.inv₀ hz0
  rw [riemannZeta_two, inv_div] at h
  convert h using 1
  funext p
  rw [inv_inv, Complex.cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast,
    one_div]

/-- The correction factor at $p = 2$ ($\beta_2 = 1$ instead of $1 - 2^{-2}$). -/
noncomputable def corr2 (p : PrimeIdx) : ℂ := if (p : ℕ) = 2 then 4 / 3 else 1

theorem hasProd_corr2 : HasProd corr2 (4 / 3) := by
  have h : HasProd corr2 (∏ p ∈ ({⟨2, Nat.prime_two⟩} : Finset PrimeIdx), corr2 p) :=
    hasProd_prod_of_ne_finset_one fun p hp => by
      rw [Finset.mem_singleton] at hp
      simp only [corr2]
      rw [if_neg]
      intro h2; exact hp (Subtype.ext h2)
  rw [Finset.prod_singleton] at h
  have e : corr2 ⟨2, Nat.prime_two⟩ = 4 / 3 := if_pos rfl
  rwa [e] at h

/-- The factor at $p \mid t$: $1 + 1/p$. -/
noncomputable def corrT (t : ℕ) (p : PrimeIdx) : ℂ := if (p : ℕ) ∣ t then 1 + 1 / ((p : ℕ) : ℂ) else 1

theorem hasProd_corrT (t : ℕ) (ht : t ≠ 0) :
    HasProd (corrT t) (∏ p ∈ t.primeFactors, (1 + 1 / (p : ℂ))) := by
  let s : Finset PrimeIdx :=
    t.primeFactors.preimage (fun p : PrimeIdx => (p : ℕ)) Subtype.val_injective.injOn
  have h : HasProd (corrT t) (∏ p ∈ s, corrT t p) :=
    hasProd_prod_of_ne_finset_one fun p hp => by
      simp only [corrT]
      rw [if_neg]
      intro hd
      apply hp
      rw [Finset.mem_preimage]
      exact Nat.mem_primeFactors.mpr ⟨p.2, hd, ht⟩
  convert h using 1
  have e : ∀ p ∈ s, corrT t p = (fun x : ℕ => 1 + 1 / (x : ℂ)) (p : ℕ) := by
    intro p hp
    rw [Finset.mem_preimage] at hp
    simp [corrT, Nat.dvd_of_mem_primeFactors hp]
  rw [Finset.prod_congr rfl e]
  exact (Finset.prod_preimage (fun p : PrimeIdx => (p : ℕ)) t.primeFactors
    Subtype.val_injective.injOn (fun x : ℕ => 1 + 1 / (x : ℂ))
    (fun x hx hxr => absurd ⟨⟨x, Nat.prime_of_mem_primeFactors hx⟩, rfl⟩ hxr)).symm

/-- **The local densities of $Q$ at an odd squarefree $t$** (Lemmas 2.7.4, 2.7.6):
$\beta_p(t) = (1 - p^{-2})\cdot c_2(p)\cdot c_t(p)$ with $c_2(2) = 4/3$, $c_t(p) = 1 + 1/p$ for $p \mid t$. -/
theorem beta_eq (I : FourSquaresInputs) (t : ℕ) (ht : Odd t) (hsq : Squarefree t) (p : PrimeIdx) :
    ((LocalDensity.localDensity Q4 p t : ℝ) : ℂ) =
      (1 - 1 / ((p : ℕ) : ℂ) ^ 2) * corr2 p * corrT t p := by
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  by_cases h2 : (p : ℕ) = 2
  · have hnd : ¬ (p : ℕ) ∣ t := by
      rw [h2]; exact fun h => (Nat.not_even_iff_odd.mpr ht) (even_iff_two_dvd.mpr h)
    have hb := I.beta_two t ht
    have : (LocalDensity.localDensity Q4 (p : ℕ) t) = 1 := by rw [h2]; exact hb
    have e1 : corr2 p = 4 / 3 := if_pos h2
    have e2 : corrT t p = 1 := if_neg hnd
    rw [this, e1, e2, h2]
    norm_num
  · by_cases hd : (p : ℕ) ∣ t
    · have h1 : ((p : ℕ) : ℤ) ∣ (t : ℤ) := Int.natCast_dvd_natCast.mpr hd
      have hp2 : ¬ ((p : ℕ) : ℤ) ^ 2 ∣ (t : ℤ) := by
        intro h
        have : (p : ℕ) * p ∣ t := by
          rw [← sq]; exact_mod_cast h
        exact (Fact.out : (p : ℕ).Prime).one_lt.ne' (Nat.isUnit_iff.mp (hsq _ this))
      rw [beta_odd_ord_one (p : ℕ) h2 t h1 hp2]
      have e1 : corr2 p = 1 := if_neg h2
      have e2 : corrT t p = 1 + 1 / ((p : ℕ) : ℂ) := if_pos hd
      rw [e1, e2]
      push_cast; ring
    · have h1 : ¬ ((p : ℕ) : ℤ) ∣ (t : ℤ) := fun h => hd (Int.natCast_dvd_natCast.mp h)
      rw [beta_odd_unit (p : ℕ) h2 t h1]
      have e1 : corr2 p = 1 := if_neg h2
      have e2 : corrT t p = 1 := if_neg hd
      rw [e1, e2]
      push_cast; ring

/-- **(2.21)–(2.23), p. 40: $r_Q(t) = 8\prod_{p \mid t}(p+1)$ for odd squarefree $t$**, relative to
`FourSquaresInputs`. (By Jacobi, Theorem 2.7.1, this is $8\sum_{d \mid t} d$.) -/
@[kb "hanke2011aws" "§2.7.5, (2.21)-(2.23), p. 40"]
theorem r4_squarefree (I : FourSquaresInputs) (t : ℕ) (ht : Odd t) (hsq : Squarefree t) :
    (r4 t : ℂ) = 8 * ∏ p ∈ t.primeFactors, ((p : ℂ) + 1) := by
  have ht0 : t ≠ 0 := by rintro rfl; exact (Nat.not_even_iff_odd.mpr ht) ⟨0, rfl⟩
  have hprod : HasProd (fun p : PrimeIdx => ((LocalDensity.localDensity Q4 p t : ℝ) : ℂ))
      (6 / (Real.pi : ℂ) ^ 2 * (4 / 3) * ∏ p ∈ t.primeFactors, (1 + 1 / (p : ℂ))) := by
    have := (hasProd_one_sub_inv_sq.mul hasProd_corr2).mul (hasProd_corrT t ht0)
    convert this using 1
    funext p
    exact beta_eq I t ht hsq p
  rw [I.siegel t (Nat.pos_of_ne_zero ht0), hprod.tprod_eq]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have htp : (t : ℂ) = ∏ p ∈ t.primeFactors, (p : ℂ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
  have hfac : ∏ p ∈ t.primeFactors, ((p : ℂ) + 1) =
      (∏ p ∈ t.primeFactors, (p : ℂ)) * ∏ p ∈ t.primeFactors, (1 + 1 / (p : ℂ)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    field_simp
  rw [hfac, ← htp]
  push_cast
  field_simp
  ring

/-- **(2.10)–(2.16), p. 39: $r_Q(1) = 8$** ("which we could also have worked out (perhaps more quickly)
by observing that … all but one $x_i$ is zero"), relative to `FourSquaresInputs`. -/
@[kb "hanke2011aws" "§2.7.5, (2.10)-(2.16), p. 39"]
theorem r4_one (I : FourSquaresInputs) : (r4 1 : ℂ) = 8 := by
  have := r4_squarefree I 1 odd_one squarefree_one
  simpa using this

/-- **(2.17)–(2.20), p. 40: $r_Q(p) = 8(p+1)$ for odd primes $p$**, relative to `FourSquaresInputs`. -/
@[kb "hanke2011aws" "§2.7.5, (2.17)-(2.20), p. 40"]
theorem r4_prime (I : FourSquaresInputs) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (r4 p : ℂ) = 8 * ((p : ℂ) + 1) := by
  have := r4_squarefree I p (hp.odd_of_ne_two hp2) hp.squarefree
  rwa [Nat.Prime.primeFactors hp, Finset.prod_singleton] at this

end QuadFormsKB.AWS
