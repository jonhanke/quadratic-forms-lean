/-
# Hanke 2011, §6–§7: the constant $V(r)$, Lemmas 7.8 and 7.10, Theorem 7.11 (algebraic part)

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`).

* `volV r` $= V(r) := \tfrac12\pi^{r(r+1)/4}\prod_{i=1}^r\Gamma(i/2)^{-1}$ (Theorem 6.2, p. 26), with `volV_one`
  ($V(1) = 1/2$) and `volV_two` ($V(2) = \pi/2$, used in the proof of Lemma 7.8).
* `lemma_7_8_constant`: the constant of Corollary 6.3 for $n = 2$ over a field of degree $d$ in which $2$ splits
  completely ($N(2\mathcal O_F) = 2^d$): $V(2)^d\,N(2\mathcal O_F)^{n(n+1)/2} = (4\pi)^d$ (proof of Lemma 7.8, p. 32).
* `theorem_7_11_finite`: Theorem 7.11 (p. 33) from Lemma 7.8, Lemma 7.10 and the table of the proof of Theorem 7.6
  (`LocalDatum.a`, `LocalDatum.b` in `BinarySeries.lean`), truncated to a finite set $T$ of primes containing the
  dyadic primes and the support of $S$. Outside $T$ the local factors are $A^*_{\mathfrak p} = B^*_{\mathfrak p} = 1$, and
  $\beta^{-1}_{2,\mathfrak p} = \gamma_{\mathfrak p}^{-1}$ occurs on both sides, so the identity over $T$ is the theorem up to
  the common factor $\prod_{\mathfrak p\notin T}\gamma_{\mathfrak p}(\widetilde S)^{-1}$ (whose convergence is an analytic matter not
  treated here). The table itself (Lemmas 7.2, 7.3 and the Conway–Sloane 2-adic mass formula) is not formalized: it is
  taken as the definition of $A^*$, $B^*$, as in `BinarySeries.lean`.

*Update (typographical; proposed by the formalization, not yet confirmed by the author):* the last paragraph of the proof of
Theorem 7.11 reads "When $I(S) = \square$ and $\widetilde S \equiv 1\ (4)$ then from Remark 7.7 we have
$B^*_{n=2}(S) = (-1)^\tau A^*_{n=2}(S)$"; by Remark 7.7 and the statement of the theorem this is the case
$\widetilde S \equiv 3 \pmod 4$ (for $\widetilde S \equiv 1$ the $B^*$-term vanishes).
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2011Structure.BinarySeries

namespace QuadFormsKB.Hanke2011Structure

open Finset Real

/-- **The constant $V(r)$ of Theorem 6.2** (Hanke 2011, p. 26): $V(r) := \tfrac12\,\pi^{r(r+1)/4}\prod_{i=1}^{r}\Gamma(i/2)^{-1}$
for $r \in \mathbb Z_{\ge0}$. -/
@[kb "hanke2011structure" "Thm. 6.2, p. 26 (V(r))"]
noncomputable def volV (r : ℕ) : ℝ :=
  1 / 2 * π ^ ((r * (r + 1) : ℝ) / 4) * ∏ i ∈ Icc 1 r, (Gamma ((i : ℝ) / 2))⁻¹

/-- $V(1) = \tfrac12\pi^{1/2}\Gamma(1/2)^{-1} = \tfrac12$. -/
theorem volV_one : volV 1 = 1 / 2 := by
  have hs : sqrt π ≠ 0 := (sqrt_pos.mpr pi_pos).ne'
  simp only [volV, Icc_self, prod_singleton, Nat.cast_one]
  rw [show ((1 : ℝ) * (1 + 1)) / 4 = 1 / 2 by norm_num, ← sqrt_eq_rpow, Gamma_one_half_eq]
  field_simp

/-- **$V(2) = \pi/2$** (Hanke 2011, proof of Lemma 7.8, p. 32): $\tfrac12\pi^{3/2}\Gamma(1/2)^{-1}\Gamma(1)^{-1} = \pi/2$. -/
@[kb "hanke2011structure" "Lemma 7.8, proof, p. 32 (V(2) = π/2)"]
theorem volV_two : volV 2 = π / 2 := by
  have hs : sqrt π ≠ 0 := (sqrt_pos.mpr pi_pos).ne'
  have hI : Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  simp only [volV, hI, prod_insert (by decide : (1 : ℕ) ∉ ({2} : Finset ℕ)), prod_singleton, Nat.cast_one,
    Nat.cast_ofNat]
  rw [show ((2 : ℝ) * (2 + 1)) / 4 = 1 + 1 / 2 by norm_num, rpow_add pi_pos, rpow_one, ← sqrt_eq_rpow,
    Gamma_one_half_eq, show (2 : ℝ) / 2 = 1 by norm_num, Gamma_one]
  field_simp

/-- **The constant of Lemma 7.8** (Hanke 2011, proof of Lemma 7.8, p. 32): for $n = 2$, $[F:\mathbb Q] = d$ and $2$ split
completely in $F$ (so $N_{F/\mathbb Q}(2\mathcal O_F) = 2^d$), the constant $V(n)^{[F:\mathbb Q]}N(2\mathcal O_F)^{n(n+1)/2}$ of
Corollary 6.3 is $(\pi/2)^d\,2^{3d} = (4\pi)^d$. -/
@[kb "hanke2011structure" "Lemma 7.8, proof, p. 32 (constant)"]
theorem lemma_7_8_constant (d : ℕ) : volV 2 ^ d * ((2 : ℝ) ^ d) ^ (2 * (2 + 1) / 2) = (4 * π) ^ d := by
  rw [volV_two, show 2 * (2 + 1) / 2 = 3 by norm_num, ← pow_mul, mul_comm d 3, pow_mul, ← mul_pow]
  congr 1
  ring

variable {K : Type*} [Field K] [CharZero K]

/-- The hypotheses of Theorem 7.11 on the table data at one prime (a local genus exists, the residue field has $q > 1$
elements, $\chi = \pm1$; at the dyadic primes $q = 2$, $\nu \ne 1$, and $u \equiv 3 \pmod 4$ if $\nu = 0$, i.e. there is a
primitive binary genus with this determinant, Remark 2.11). -/
def LocalDatum.Admissible (d : LocalDatum K) : Prop :=
  (d.chi = 1 ∨ d.chi = -1) ∧ d.q ≠ 0 ∧ gammaP d.chi d.q ≠ 0 ∧
    (d.dyadic → d.q = 2 ∧ d.nu ≠ 1 ∧ (d.nu = 0 → d.u3))

omit [CharZero K] in
/-- The local factor of $A^*$ in the form used in the proof of Theorem 7.11: $q^{-\nu}$ times $\gamma_{\mathfrak p}$ iff
$\mathfrak p \mid I(S)$. -/
theorem LocalDatum.a_eq {d : LocalDatum K} (h : d.Admissible) :
    d.a = (d.q ^ d.nu)⁻¹ * (if d.nu = 0 then 1 else gammaP d.chi d.q) := by
  obtain ⟨-, -, -, hd⟩ := h
  unfold LocalDatum.a
  cases hdy : d.dyadic
  · simp only [Bool.false_eq_true, ite_false, aNondyadic]
    split_ifs with h0 <;> simp [h0]
  · obtain ⟨hq, h1, hu⟩ := hd hdy
    simp only [ite_true, aDyadic, hq]
    by_cases h0 : d.nu = 0
    · simp [h0, hu h0]
    · simp [h0, h1]

omit [CharZero K] in
/-- **Lemma 7.10, truncated to a finite set $T$ of primes** (Hanke 2011, p. 32): with the convention of Definition 7.5,
$\beta^{-1}_{2;\mathfrak p}(\widetilde S_{\mathfrak p}) = \gamma_{\mathfrak p}(\widetilde S)^{-1}$ at $\mathfrak p \nmid 2$ and $2\gamma_{\mathfrak p}(\widetilde S)^{-1}$
at the dyadic primes (which split completely), so $\prod_{\mathfrak p\in T}\beta^{-1}_{2;\mathfrak p} = 2^{\#\{\mathfrak p\in T,\ \mathfrak p\mid2\}}
\prod_{\mathfrak p\in T}\gamma_{\mathfrak p}^{-1}$; when $T$ contains all $[F:\mathbb Q]$ dyadic primes the power of $2$ is
$2^{[F:\mathbb Q]}$. -/
@[kb "hanke2011structure" "Lemma 7.10, p. 32 (finite product)"]
theorem lemma_7_10_finite {ι : Type*} (T : Finset ι) (d : ι → LocalDatum K) :
    ∏ p ∈ T, (if (d p).dyadic then 2 * (gammaP (d p).chi (d p).q)⁻¹ else (gammaP (d p).chi (d p).q)⁻¹) =
      2 ^ (T.filter fun p => (d p).dyadic).card * ∏ p ∈ T, (gammaP (d p).chi (d p).q)⁻¹ := by
  classical
  rw [card_filter, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  refine prod_congr rfl fun p _ => ?_
  split_ifs <;> simp

/-- The constant $\kappa(S)$ of Theorem 7.11 (Hanke 2011, p. 33): $2$ if $I(S)$ is a square, $\widetilde S \equiv 3 \pmod 4$
and $\tau$ is even, $0$ if $I(S)$ is a square, $\widetilde S \equiv 3 \pmod 4$ and $\tau$ is odd, and $1$ otherwise; here
$\tau$ is the number of dyadic primes not dividing $I(S)$. On the data over $T$: "$I(S)$ is a square" is "every
$\nu_{\mathfrak p}$ is even", "$\widetilde S \equiv 3 \pmod 4$" is "$u \equiv 3 \pmod 4$ at every dyadic prime". -/
noncomputable def kappa {ι : Type*} (T : Finset ι) (d : ι → LocalDatum K) : K :=
  open Classical in
  if ∀ p ∈ T, Even (d p).nu ∧ ((d p).dyadic → (d p).u3) then
    (if Even (T.filter fun p => (d p).dyadic ∧ (d p).nu = 0).card then 2 else 0)
  else 1

/-- **Theorem 7.11, algebraic part, over a finite set $T$ of primes** (Hanke 2011, p. 33). Let $T$ be a finite set of primes
containing the dyadic primes and the support of $S$, with admissible table data $d_{\mathfrak p}$ (`LocalDatum.Admissible`),
$N := \prod_{\mathfrak p\in T}q_{\mathfrak p}^{\nu_{\mathfrak p}} = N_{F/\mathbb Q}(I(S))$, $A^* = \prod_{\mathfrak p\in T}A^*_{\mathfrak p;2}$,
$B^* = \prod_{\mathfrak p\in T}B^*_{\mathfrak p;2}$, $\beta^{-1} = \prod_{\mathfrak p\in T}\beta^{-1}_{2;\mathfrak p}$ (Lemma 7.10), $\delta$ the number of
dyadic primes in $T$ ($= [F:\mathbb Q]$ when $2$ splits completely), and any $c$ (standing for $|\Delta_F|^{1/2}$), $\rho$
(standing for $N(I(S))^{1/2}$) and $\varpi \ne 0$ (standing for $\pi$). Then the right side of Lemma 7.8 for
the totally definite signature ($\varepsilon_\infty = 1$),
$$\frac{\beta^{-1}\,c\,N\rho\,(A^* + B^*)}{2\,(4\varpi)^{\delta}},$$
equals the right side of Theorem 7.11, $\dfrac{\kappa(S)\,c\,\rho}{2\,(2\varpi)^{\delta}}\prod_{\mathfrak p\in T,\ \mathfrak p\nmid I(S)}\gamma_{\mathfrak p}^{-1}$. -/
@[kb "hanke2011structure" "Thm. 7.11, p. 33 (algebraic part, finite product)"]
theorem theorem_7_11_finite {ι : Type*} (T : Finset ι) (d : ι → LocalDatum K) (hd : ∀ p ∈ T, (d p).Admissible)
    (c ρ ϖ : K) (hϖ : ϖ ≠ 0) :
    (∏ p ∈ T, (if (d p).dyadic then 2 * (gammaP (d p).chi (d p).q)⁻¹ else (gammaP (d p).chi (d p).q)⁻¹)) *
        c * (∏ p ∈ T, (d p).q ^ (d p).nu) * ρ * (∏ p ∈ T, (d p).a + ∏ p ∈ T, (d p).b) /
          (2 * (4 * ϖ) ^ (T.filter fun p => (d p).dyadic).card) =
      kappa T d * c * ρ / (2 * (2 * ϖ) ^ (T.filter fun p => (d p).dyadic).card) *
        ∏ p ∈ T.filter (fun p => (d p).nu = 0), (gammaP (d p).chi (d p).q)⁻¹ := by
  classical
  set δ := (T.filter fun p => (d p).dyadic).card
  set N := ∏ p ∈ T, (d p).q ^ (d p).nu
  have hN : N ≠ 0 := prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (hd p hp).2.1
  -- `A* = N⁻¹ ∏_{p | I(S)} γ_p`
  have hA : ∏ p ∈ T, (d p).a = N⁻¹ * ∏ p ∈ T.filter (fun p => (d p).nu ≠ 0), gammaP (d p).chi (d p).q := by
    rw [prod_congr rfl fun p hp => LocalDatum.a_eq (hd p hp), prod_mul_distrib, prod_inv_distrib, prod_filter]
    simp only [ne_eq, ite_not]
    rfl
  -- `B* = κ' A*` with `κ' = κ - 1`
  have hB : ∏ p ∈ T, (d p).b = (kappa T d - 1) * ∏ p ∈ T, (d p).a := by
    unfold kappa
    split_ifs with h hτ
    · rw [remark_7_7 T d h, hτ.neg_one_pow]; ring
    · rw [remark_7_7 T d h, (Nat.not_even_iff_odd.mp hτ).neg_one_pow]; ring
    · simp only [not_forall, not_and, exists_prop] at h
      obtain ⟨p, hp, hbad⟩ := h
      rw [remark_7_7_vanish T d ⟨p, hp, ?_⟩]
      · ring
      · by_cases he : Even (d p).nu
        · exact Or.inr ⟨(hbad he).1, by simpa using (hbad he).2⟩
        · exact Or.inl he
  -- split `∏ γ⁻¹` over `ν = 0` and `ν ≠ 0`
  have hγ : ∏ p ∈ T, (gammaP (d p).chi (d p).q)⁻¹ =
      (∏ p ∈ T.filter (fun p => (d p).nu = 0), (gammaP (d p).chi (d p).q)⁻¹) *
        (∏ p ∈ T.filter (fun p => (d p).nu ≠ 0), gammaP (d p).chi (d p).q)⁻¹ := by
    rw [← prod_filter_mul_prod_filter_not T (fun p => (d p).nu = 0)]
    simp only [ne_eq, prod_inv_distrib]
  have hG : ∏ p ∈ T.filter (fun p => (d p).nu ≠ 0), gammaP (d p).chi (d p).q ≠ 0 :=
    prod_ne_zero_iff.mpr fun p hp => (hd p (mem_filter.mp hp).1).2.2.1
  rw [lemma_7_10_finite, hB, hA, hγ]
  have h4 : (4 * ϖ) ^ δ = 2 ^ δ * (2 * ϖ) ^ δ := by rw [← mul_pow]; ring
  rw [h4]
  have h2 : (2 : K) ^ δ ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2ϖ : (2 * ϖ) ^ δ ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero hϖ)
  field_simp
  ring

end QuadFormsKB.Hanke2011Structure
