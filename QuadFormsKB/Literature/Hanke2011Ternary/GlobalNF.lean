/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Hanke2011Ternary.Global
import QuadFormsKB.Literature.Hanke2011Structure.SquareclassSeries

/-!
# Hanke 2011 (ternary masses), Theorem 7.1 over a number field $F$ in which $2$ splits completely

J. Hanke, *Explicit formulas for masses of ternary quadratic lattices of varying determinant over number fields*,
arXiv:1109.1054 (bib key `hanke2011ternary`), §7, Theorem 7.1, pp. 25–26.

**Setting.** $F$ is a number field, $\mathfrak p$ runs over the nonzero primes of $\mathcal O_F$ (`HeightOneSpectrum`),
$q_{\mathfrak p} = N\mathfrak p$ (`qv`), and $\operatorname{ord}_{\mathfrak p}\mathfrak a$ (`ordI`) is the exponent of
$\mathfrak p$ in the nonzero ideal $\mathfrak a$. By paper 6, Cor. 4.13 and Lemma 4.7, the coefficient of
$N(\mathfrak a)^{-s}$ (here: of $\mathfrak a^{-s}$) in $D_{A^*,\lambda;3}(s)$ is the product over all $\mathfrak p$ of the
normalized local mass sums $A^*_{\mathfrak p}(\lambda(\mathfrak a)_{\mathfrak p})$. Paper 7 computes these:

* at $\mathfrak p \nmid 2$ they are the values of Table 2 (Thm. 2.4) with $q = q_{\mathfrak p}$ and
  $\varepsilon' = \left(\frac{-1}{\mathfrak p}\right)$ (`epsOdd`, $+1$ iff $q_{\mathfrak p} \equiv 1 \pmod 4$), namely
  `Astar q ε' ν 1`, `Bstar q ε' ν 1` with $\nu = \operatorname{ord}_{\mathfrak p}\mathfrak a$ (they do not depend on the
  unit part, `Astar_eq_sum`);
* at $\mathfrak p \mid 2$ with $F_{\mathfrak p} = \mathbb Q_2$ they are Table 5.3, `dyadicA ν` and
  `dyadicB ε_𝔭 ν` with $\varepsilon_{\mathfrak p} = (-1,\lambda(\mathfrak a))_{\mathfrak p}$.

These products are `coeffA`, `coeffB`. The right sides of Theorem 7.1 are written as Euler products: for a family of
local power series $E_{\mathfrak p}(X) \in \mathbb Q[[X]]$ with constant term $1$, the coefficient of $\mathfrak a^{-s}$ in
$\prod_{\mathfrak p}E_{\mathfrak p}(N\mathfrak p^{-s})$ is $\prod_{\mathfrak p}[X^{\operatorname{ord}_{\mathfrak p}\mathfrak a}]E_{\mathfrak p}$
(`eulerCoeff`). With $\zeta_F(s) = \prod_{\mathfrak p}(1 - N\mathfrak p^{-s})^{-1}$, the local factor of
$\zeta_F(s+1)\zeta_F(2s+3)/\zeta_F(3s+6)$ at $\mathfrak p$ is `EA q` and that of $\zeta_F(2s+2)\zeta_F(s+2)/\zeta_F(3s+6)$
is `EB q` ($q = N\mathfrak p$, $X = q^{-s}$); the factor $N(2\mathcal O_F)^{-s} = \prod_{\mathfrak p\mid 2}N\mathfrak p^{-s}$
($2$ unramified) contributes $X$ at each $\mathfrak p \mid 2$ (`twoShift`).

**Results.**
* `theorem_7_1_A` (**proved**, for every number field $F$ whose primes above $2$ have norm $2$, e.g. $2$ split
  completely): $D_{A^*,\lambda;3}(s) = \dfrac{\zeta_F(s+1)\zeta_F(2s+3)}{N(2\mathcal O_F)^{s}\,\zeta_F(3s+6)}$,
  coefficientwise.
* `theorem_7_1_B_signed` (**proved**): $D_{B^*,\lambda;3}$ has coefficient $\sigma(\mathfrak a)$ times that of
  $\dfrac{\zeta_F(2s+2)\zeta_F(s+2)}{N(2\mathcal O_F)^{s}\,\zeta_F(3s+6)}$, with
  $\sigma(\mathfrak a) = \prod_{\mathfrak p\nmid 2}\left(\frac{-1}{\mathfrak p}\right)^{\operatorname{ord}_{\mathfrak p}\mathfrak a}
  \prod_{\mathfrak p\mid 2}\bigl(-\varepsilon_{\mathfrak p}\bigr)$ (the paper's sign bookkeeping, proof of Thm. 7.1).

*Update:* the paper prints
$2^s$ in the denominators; each of the $[F:\mathbb Q]$ primes above $2$ contributes $N\mathfrak p^{-s} = 2^{-s}$, so the
factor is $N(2\mathcal O_F)^{s} = 2^{[F:\mathbb Q]s}$ (as Theorem 8.1's $(\pi^2 2^{s+2})^{[F:\mathbb Q]}$ already uses). Indices are
0-based.
-/

namespace QuadFormsKB.Hanke2011Ternary.NF

open IsDedekindDomain NumberField PowerSeries
open scoped nonZeroDivisors

noncomputable section

variable {F : Type} [Field F] [NumberField F]

/-! ### Local data -/

/-- The size $q_{\mathfrak p} = N\mathfrak p = |\mathcal O_F/\mathfrak p|$ of the residue field at $\mathfrak p$. -/
def qv (v : HeightOneSpectrum (𝓞 F)) : ℕ := Ideal.absNorm v.asIdeal

theorem one_lt_qv (v : HeightOneSpectrum (𝓞 F)) : 1 < qv v := by
  have h0 : qv v ≠ 0 := by
    unfold qv; rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : qv v ≠ 1 := by
    unfold qv; rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem one_lt_qv_rat (v : HeightOneSpectrum (𝓞 F)) : (1 : ℚ) < qv v := by exact_mod_cast one_lt_qv v

/-- $\varepsilon'_{\mathfrak p} = \left(\frac{-1}{\mathfrak p}\right)$ at $\mathfrak p \nmid 2$: $+1$ iff
$N\mathfrak p \equiv 1 \pmod 4$ (iff $-1$ is a square in $\mathcal O_F/\mathfrak p$). -/
def epsOdd (v : HeightOneSpectrum (𝓞 F)) : ℤˣ := negOneChar (qv v)

/-- The exponent $\operatorname{ord}_{\mathfrak p}\mathfrak a$ of $\mathfrak p$ in the nonzero ideal $\mathfrak a$. -/
def ordI (v : HeightOneSpectrum (𝓞 F)) (a : (Ideal (𝓞 F))⁰) : ℕ :=
  (UniqueFactorizationMonoid.normalizedFactors (a : Ideal (𝓞 F))).count v.asIdeal

theorem ordI_eq_idealOrd (v : HeightOneSpectrum (𝓞 F)) (a : (Ideal (𝓞 F))⁰) :
    (ordI v a : ℤ) = Hanke2011Structure.idealOrd v (a : Ideal (𝓞 F)) := rfl

open Classical in
/-- **The local factor of $D_{A^*,\lambda;3}$ at $\mathfrak p$** for $\operatorname{ord}_{\mathfrak p}\lambda(\mathfrak a) = \nu$:
Table 5.3 (`dyadicA ν`) at $\mathfrak p \mid 2$, Table 2 (`Astar q ε' ν 1`) at $\mathfrak p \nmid 2$. -/
@[kb "hanke2011ternary" "§7, proof of Thm. 7.1, p. 26 (local factors from Tables 2 and 5.3)"]
def locA (v : HeightOneSpectrum (𝓞 F)) (ν : ℕ) : ℚ :=
  if (2 : 𝓞 F) ∈ v.asIdeal then dyadicA ν else Astar (qv v) (epsOdd v) ν 1

open Classical in
/-- **The local factor of $D_{B^*,\lambda;3}$ at $\mathfrak p$** for $\operatorname{ord}_{\mathfrak p}\lambda(\mathfrak a) = \nu$ and
$\varepsilon = (-1,\lambda(\mathfrak a))_{\mathfrak p}$ (used only at $\mathfrak p \mid 2$). -/
@[kb "hanke2011ternary" "§7, proof of Thm. 7.1, p. 26 (local factors from Tables 2 and 5.3)"]
def locB (v : HeightOneSpectrum (𝓞 F)) (ε : ℤˣ) (ν : ℕ) : ℚ :=
  if (2 : 𝓞 F) ∈ v.asIdeal then dyadicB ε ν else Bstar (qv v) (epsOdd v) ν 1

/-- **The coefficient of $\mathfrak a^{-s}$ in $D_{A^*,\lambda;3}(s)$** (paper 6, Cor. 4.13 and Lemma 4.7):
$\prod_{\mathfrak p}A^*_{\mathfrak p}(\lambda(\mathfrak a)_{\mathfrak p})$. -/
@[kb "hanke2011ternary" "§7, Thm. 7.1, p. 26 (coefficients of D_{A*,λ;3})"]
def coeffA (a : (Ideal (𝓞 F))⁰) : ℚ := ∏ᶠ v, locA v (ordI v a)

/-- **The coefficient of $\mathfrak a^{-s}$ in $D_{B^*,\lambda;3}(s)$**, $\varepsilon_{\mathfrak p} = (-1,\lambda(\mathfrak a))_{\mathfrak p}$
given by `ε a 𝔭`. -/
@[kb "hanke2011ternary" "§7, Thm. 7.1, p. 26 (coefficients of D_{B*,λ;3})"]
def coeffB (ε : (Ideal (𝓞 F))⁰ → HeightOneSpectrum (𝓞 F) → ℤˣ) (a : (Ideal (𝓞 F))⁰) : ℚ :=
  ∏ᶠ v, locB v (ε a v) (ordI v a)

/-! ### Euler products -/

/-- The local factor of $\zeta_F(s+1)\zeta_F(2s+3)/\zeta_F(3s+6)$ at a prime of norm $q$, in $X = q^{-s}$:
$(1-q^{-1}X)^{-1}(1-q^{-3}X^2)^{-1}(1-q^{-6}X^3)$. -/
def EA (q : ℚ) : PowerSeries ℚ := geom 1 q⁻¹ * geom 2 (q⁻¹ ^ 3) * (1 - C (q⁻¹ ^ 6) * X ^ 3)

/-- The local factor of $\zeta_F(2s+2)\zeta_F(s+2)/\zeta_F(3s+6)$ at a prime of norm $q$:
$(1-q^{-2}X^2)^{-1}(1-q^{-2}X)^{-1}(1-q^{-6}X^3)$. -/
def EB (q : ℚ) : PowerSeries ℚ := geom 2 (q⁻¹ ^ 2) * geom 1 (q⁻¹ ^ 2) * (1 - C (q⁻¹ ^ 6) * X ^ 3)

open Classical in
/-- The local factor of $N(2\mathcal O_F)^{-s}$ for $2$ unramified: $X = N\mathfrak p^{-s}$ at $\mathfrak p \mid 2$, $1$
elsewhere. -/
def twoShift (v : HeightOneSpectrum (𝓞 F)) : PowerSeries ℚ := if (2 : 𝓞 F) ∈ v.asIdeal then X else 1

/-- **The coefficient of $\mathfrak a^{-s}$ in the Euler product** $N(2\mathcal O_F)^{-s}\prod_{\mathfrak p}E(N\mathfrak p)$
evaluated at $X = N\mathfrak p^{-s}$: $\prod_{\mathfrak p}[X^{\operatorname{ord}_{\mathfrak p}\mathfrak a}]\,(\mathrm{twoShift}_{\mathfrak p}\cdot E(N\mathfrak p))$. -/
def eulerCoeff (E : ℚ → PowerSeries ℚ) (a : (Ideal (𝓞 F))⁰) : ℚ :=
  ∏ᶠ v, coeff (ordI v a) (twoShift v * E (qv v))

/-! ### Finiteness -/

theorem count_ne_zero_of_le (v : HeightOneSpectrum (𝓞 F)) {I : Ideal (𝓞 F)} (hI : I ≠ 0) (h : I ≤ v.asIdeal) :
    (UniqueFactorizationMonoid.normalizedFactors I).count v.asIdeal ≠ 0 := by
  rw [Multiset.count_ne_zero]
  have hd : v.asIdeal ∣ I := Ideal.dvd_iff_le.mpr h
  obtain ⟨q, hq, hassoc⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hI v.irreducible hd
  rwa [associated_iff_eq.mp hassoc]

theorem maxPow_ne_one (v : HeightOneSpectrum (𝓞 F)) {I : Ideal (𝓞 F)} (hI : I ≠ 0)
    (h : (UniqueFactorizationMonoid.normalizedFactors I).count v.asIdeal ≠ 0) : v.maxPowDividing I ≠ 1 := by
  rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count v hI]
  intro h1
  have hle : v.asIdeal ^ _ ≤ v.asIdeal := Ideal.pow_le_self h
  rw [h1, Ideal.one_eq_top, top_le_iff] at hle
  exact v.isPrime.ne_top hle

/-- Only finitely many primes divide $2\mathfrak a$. -/
theorem finite_bad (a : (Ideal (𝓞 F))⁰) :
    {v : HeightOneSpectrum (𝓞 F) | (2 : 𝓞 F) ∈ v.asIdeal ∨ ordI v a ≠ 0}.Finite := by
  have ha : (a : Ideal (𝓞 F)) ≠ 0 := nonZeroDivisors.coe_ne_zero a
  have h2 : (Ideal.span {(2 : 𝓞 F)}) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact two_ne_zero
  refine ((Ideal.hasFiniteMulSupport (R := 𝓞 F) h2).union (Ideal.hasFiniteMulSupport (R := 𝓞 F) ha)).subset
    fun v hv => ?_
  rcases hv with hv | hv
  · left
    exact maxPow_ne_one v h2 (count_ne_zero_of_le v h2 (by rw [Ideal.span_singleton_le_iff_mem]; exact hv))
  · right
    exact maxPow_ne_one v ha hv

/-! ### The local identities (Lemmas 3.3 and 6.4) -/

theorem cancel_D {S T D : PowerSeries ℚ} (hD : constantCoeff D = 1) (h : S * D = T * D) : S = T :=
  mul_right_cancel₀ (fun h0 => by simp [h0] at hD) h

/-- At $\mathfrak p \nmid 2$ with $N\mathfrak p = q$: $A^*_{\mathfrak p}(\pi^\nu u) = [X^\nu]\,E_A(q)$ (Lemma 3.3). -/
theorem Astar_eq_coeff_EA {q : ℚ} (hq : 1 < q) (ε' : ℤˣ) (ν : ℕ) : Astar q ε' ν 1 = coeff ν (EA q) := by
  have h := lemma_3_1 hq ε' 1
  have hS : PowerSeries.mk (fun ν => Astar q ε' ν 1) = EA q := by
    refine cancel_D (D := (1 - C q⁻¹ * X) * (1 - C (q⁻¹ ^ 3) * X ^ 2)) (by simp) ?_
    rw [h, EA]
    have h1 := geom_mul 1 one_pos q⁻¹
    have h2 := geom_mul 2 two_pos (q⁻¹ ^ 3)
    rw [pow_one] at h1
    linear_combination (-(1 - C (q⁻¹ ^ 6) * X ^ 3)) * (geom 2 (q⁻¹ ^ 3) *
      (1 - C (q⁻¹ ^ 3) * X ^ 2)) * h1 - (1 - C (q⁻¹ ^ 6) * X ^ 3) * h2
  have := congrArg (coeff ν) hS
  simpa using this

/-- At $\mathfrak p \nmid 2$ with $N\mathfrak p = q$: $\varepsilon'^\nu B^*_{\mathfrak p}(\pi^\nu u) = [X^\nu]\,E_B(q)$
(Lemma 3.3, rescaled by $X \mapsto \varepsilon' X$). -/
theorem Bstar_eq_coeff_EB {q : ℚ} (hq : 1 < q) (ε' : ℤˣ) (ν : ℕ) :
    ((ε' : ℤ) : ℚ) ^ ν * Bstar q ε' ν 1 = coeff ν (EB q) := by
  have hε : ((ε' : ℤ) : ℚ) ^ 2 = 1 := by rcases Int.units_eq_one_or ε' with h | h <;> simp [h]
  have h := congrArg (rescale ((ε' : ℤ) : ℚ)) (lemma_3_2 hq ε' 1)
  simp only [map_mul, map_add, map_sub, map_one, rescale_X, rescale_C', map_pow] at h
  have hS : PowerSeries.mk (fun ν => ((ε' : ℤ) : ℚ) ^ ν * Bstar q ε' ν 1) = EB q := by
    refine cancel_D (D := 1 - C (q⁻¹ ^ 2) * X ^ 2) (by simp) ?_
    have hr : rescale ((ε' : ℤ) : ℚ) (PowerSeries.mk fun ν => Bstar q ε' ν 1) =
        PowerSeries.mk (fun ν => ((ε' : ℤ) : ℚ) ^ ν * Bstar q ε' ν 1) := by
      rw [rescale_mk]
    rw [← hr, EB]
    have h1 := geom_mul 1 one_pos (q⁻¹ ^ 2)
    have h2 := geom_mul 2 two_pos (q⁻¹ ^ 2)
    rw [pow_one] at h1
    have hX : (C ((ε' : ℤ) : ℚ) * X) ^ 2 = X ^ 2 := by
      rw [mul_pow, ← map_pow, hε, map_one, one_mul]
    rw [hX] at h
    simp only [map_pow]
    rw [h]
    set t := q⁻¹
    set e := ((ε' : ℤ) : ℚ)
    have hC : C e * C e = (1 : PowerSeries ℚ) := by rw [← map_mul, ← sq, hε, map_one]
    simp only [map_pow] at h1 h2 ⊢
    linear_combination (C t ^ 2 * X) * hC - (1 + C t ^ 2 * X + C t ^ 4 * X ^ 2) * h2 -
      (1 + C t ^ 2 * X + C t ^ 4 * X ^ 2) * (geom 2 (t ^ 2) * (1 - C t ^ 2 * X ^ 2)) * h1
  have := congrArg (coeff ν) hS
  simpa using this

theorem EA_two : EA ((2 : ℕ) : ℚ) = localSeries (zetaShift 1 1 * zetaShift 2 3 * zetaShiftInv 3 6) 2 := by
  rw [localSeries_gA Nat.prime_two, EA]

theorem EB_two : EB ((2 : ℕ) : ℚ) = localSeries (zetaShift 2 2 * zetaShift 1 2 * zetaShiftInv 3 6) 2 := by
  rw [localSeries_gB Nat.prime_two, EB]

/-- At $\mathfrak p \mid 2$ with $F_{\mathfrak p} = \mathbb Q_2$: `dyadicA ν` $= [X^\nu]\,X E_A(2)$ (Lemma 6.4). -/
theorem dyadicA_eq_coeff (ν : ℕ) : dyadicA ν = coeff ν (X * EA ((2 : ℕ) : ℚ)) := by
  rw [EA_two, ← dyadicA_eq_gA, coeff_mk]

/-- At $\mathfrak p \mid 2$ with $F_{\mathfrak p} = \mathbb Q_2$: `dyadicB ε ν` $= -\varepsilon\,[X^\nu]\,X E_B(2)$
(Lemma 6.4). -/
theorem dyadicB_eq_coeff (ε : ℤˣ) (ν : ℕ) :
    dyadicB ε ν = -((ε : ℤ) : ℚ) * coeff ν (X * EB ((2 : ℕ) : ℚ)) := by
  have hsign : dyadicB ε ν = ((ε : ℤ) : ℚ) * dyadicB 1 ν := by
    simp only [dyadicB, Units.val_one, Int.cast_one]; ring
  have h1 : dyadicB 1 ν = -coeff ν (X * EB ((2 : ℕ) : ℚ)) := by
    rw [EB_two]
    have := congrArg (coeff ν) dyadicB_eq_gB
    simpa using this
  rw [hsign, h1]; ring

/-! ### Theorem 7.1 -/

open Classical in
/-- The sign of the coefficient at $\mathfrak p$ in the proof of Theorem 7.1: $\left(\frac{-1}{\mathfrak p}\right)^{\operatorname{ord}_{\mathfrak p}\mathfrak a}$ at
$\mathfrak p \nmid 2$ and $-\varepsilon_{\mathfrak p}$ at $\mathfrak p \mid 2$. -/
def sgnAt (ε : (Ideal (𝓞 F))⁰ → HeightOneSpectrum (𝓞 F) → ℤˣ) (a : (Ideal (𝓞 F))⁰)
    (v : HeightOneSpectrum (𝓞 F)) : ℤˣ :=
  if (2 : 𝓞 F) ∈ v.asIdeal then -(ε a v) else epsOdd v ^ ordI v a

theorem locA_eq (h2 : ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal → qv v = 2)
    (v : HeightOneSpectrum (𝓞 F)) (ν : ℕ) : locA v ν = coeff ν (twoShift v * EA (qv v)) := by
  unfold locA twoShift
  split_ifs with hv
  · rw [h2 v hv, dyadicA_eq_coeff]
  · rw [one_mul, Astar_eq_coeff_EA (one_lt_qv_rat v)]

theorem locB_eq (h2 : ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal → qv v = 2)
    (ε : (Ideal (𝓞 F))⁰ → HeightOneSpectrum (𝓞 F) → ℤˣ) (a : (Ideal (𝓞 F))⁰) (v : HeightOneSpectrum (𝓞 F)) :
    locB v (ε a v) (ordI v a) = ((sgnAt ε a v : ℤ) : ℚ) * coeff (ordI v a) (twoShift v * EB (qv v)) := by
  unfold locB twoShift sgnAt
  split_ifs with hv
  · rw [h2 v hv, dyadicB_eq_coeff]; push_cast; ring
  · rw [one_mul, ← Bstar_eq_coeff_EB (one_lt_qv_rat v)]
    have hε : ((epsOdd v : ℤ) : ℚ) ^ 2 = 1 := by
      rcases Int.units_eq_one_or (epsOdd v) with h | h <;> simp [h]
    push_cast
    rw [← mul_assoc, ← mul_pow, ← sq, hε, one_pow, one_mul]

theorem coeff_zero_shift_E (E : ℚ → PowerSeries ℚ) (hE : ∀ q, constantCoeff (E q) = 1) (v : HeightOneSpectrum (𝓞 F))
    (hv : (2 : 𝓞 F) ∉ v.asIdeal) : coeff 0 (twoShift v * E (qv v)) = 1 := by
  unfold twoShift; rw [if_neg hv, one_mul, coeff_zero_eq_constantCoeff_apply, hE]

theorem constantCoeff_geom (k : ℕ) (c : ℚ) : constantCoeff (geom k c) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, geom, coeff_spread]; simp

theorem constantCoeff_EA (q : ℚ) : constantCoeff (EA q) = 1 := by simp [EA, constantCoeff_geom]
theorem constantCoeff_EB (q : ℚ) : constantCoeff (EB q) = 1 := by simp [EB, constantCoeff_geom]

/-- **Theorem 7.1, $A^*$ part** (Hanke 2011, p. 26), for a number field $F$ in which every prime above $2$ has norm $2$
(e.g. $2$ splits completely, the paper's hypothesis): coefficientwise,
$$D_{A^*,\lambda;3}(s) = \frac{\zeta_F(s+1)\,\zeta_F(2s+3)}{N(2\mathcal O_F)^{s}\,\zeta_F(3s+6)},$$
the right side as its Euler product (its factor $\prod_{\mathfrak p\mid2}N\mathfrak p^{-s}$ is $N(2\mathcal O_F)^{-s}$ because $2$ is
unramified when it splits completely; the identity itself only uses $N\mathfrak p = 2$). *Update:* the paper prints
$2^s$ for $N(2\mathcal O_F)^s = 2^{[F:\mathbb Q]s}$ (module docstring). -/
@[kb "hanke2011ternary" "§7, Thm. 7.1, p. 26 (D_{A*,λ;3}, F with 2 split completely; 2^{[F:Q]s} for 2^s)"]
theorem theorem_7_1_A (h2 : ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal → qv v = 2)
    (a : (Ideal (𝓞 F))⁰) : coeffA a = eulerCoeff EA a :=
  finprod_congr fun v => locA_eq h2 v _

/-- **Theorem 7.1, $B^*$ part, signed form** (Hanke 2011, p. 26, the sign bookkeeping of its proof): coefficientwise,
$$[\mathfrak a^{-s}]\,D_{B^*,\lambda;3} = \sigma(\mathfrak a)\cdot[\mathfrak a^{-s}]\,\frac{\zeta_F(2s+2)\,\zeta_F(s+2)}{N(2\mathcal O_F)^{s}\,\zeta_F(3s+6)},
\qquad \sigma(\mathfrak a) = \prod_{\mathfrak p\nmid2}\Bigl(\frac{-1}{\mathfrak p}\Bigr)^{\operatorname{ord}_{\mathfrak p}\mathfrak a}\prod_{\mathfrak p\mid2}(-\varepsilon_{\mathfrak p}),$$
using $(1\mp X)(1\pm X+X^2) = 1\pm X^3$ at $\mathfrak p \nmid 2$. -/
@[kb "hanke2011ternary" "§7, Thm. 7.1, p. 26, and its proof (D_{B*,λ;3}, signed form)"]
theorem theorem_7_1_B_signed (h2 : ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal → qv v = 2)
    (ε : (Ideal (𝓞 F))⁰ → HeightOneSpectrum (𝓞 F) → ℤˣ) (a : (Ideal (𝓞 F))⁰) :
    coeffB ε a = (∏ᶠ v, ((sgnAt ε a v : ℤ) : ℚ)) * eulerCoeff EB a := by
  unfold coeffB eulerCoeff
  rw [finprod_congr fun v => locB_eq h2 ε a v]
  refine finprod_mul_distrib ((finite_bad a).subset fun v hv => ?_) ((finite_bad a).subset fun v hv => ?_)
  · by_contra hb
    simp only [Set.mem_ofPred_eq, not_or, not_not] at hb
    apply hv
    simp [sgnAt, hb.1, hb.2]
  · by_contra hb
    simp only [Set.mem_ofPred_eq, not_or, not_not] at hb
    apply hv
    show coeff (ordI v a) _ = 1
    rw [hb.2]; exact coeff_zero_shift_E EB constantCoeff_EB v hb.1

end

end QuadFormsKB.Hanke2011Ternary.NF

#print axioms QuadFormsKB.Hanke2011Ternary.NF.theorem_7_1_A
#print axioms QuadFormsKB.Hanke2011Ternary.NF.theorem_7_1_B_signed
