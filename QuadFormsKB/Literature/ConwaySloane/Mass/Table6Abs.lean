/-
# Conway–Sloane 1988, §8: $\zeta_D(s)$ from (13) without evaluating the Gauss sum

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §8, pp. 268–271.

The closed formula (13) (`zetaD_formula`) contains the Gauss sum $G(\psi) = \sum_{r=1}^{k_1}\psi(r)e^{2\pi i r/k_1}$ of the
primitive character $\psi$ attached to $D$. For a real primitive $\psi$ only its square is needed: $G(\psi)^2 = \psi(-1)k_1$
(Fourier inversion on $\mathbb Z/k_1$), and the remaining sign ambiguity is removed by the positivity of $\zeta_D(s)$ for
real $s > 1$ (every factor of the Euler product (8) is positive). This gives (13) in the form
$$\zeta_D(s) = \frac{\lvert E\rvert\,(2\pi)^s\,\lvert S\rvert}{2\,s!\,\sqrt{k_1}},\qquad
E = \prod_{p \mid 4D}\Bigl(1 - \frac{\psi(p)}{p^s}\Bigr),\quad S = \sum_{r=1}^{k_1}\psi(r)\,B_s\!\Bigl(\frac r{k_1}\Bigr),$$
which needs no knowledge of the sign of $G(\psi)$. (Conversely, comparing with (13) determines that sign, for
every real primitive $\psi$ for which some admissible $s$ has $S \ne 0$; this is not used.)

**Proves**
* `gaussSum_sq_of_real`: $G(\psi)^2 = \psi(-1)\,k_1$ for a primitive real Dirichlet character $\psi$ modulo $k_1$.
* `zetaD_nonneg`: $\zeta_D(s) \ge 0$ for real $s > 1$ (Euler product).
* `zetaD_eq_abs`: the displayed form of (13).
* `table6_eq_abs`: the corresponding Table 6 entry
  $\zeta_D(s)\,d^{s-1}\sqrt d/\pi^s = \lvert E\rvert\,2^s\lvert S\rvert\,d^{s-1}c/(2\,s!)$ when $\sqrt d = c\sqrt{k_1}$, $c$ rational.
* `isPrimitive_of_prime_witness`: a character modulo $n$ is primitive if for every prime $p \mid n$ some $a$ coprime to
  $n$ with $a \equiv 1 \pmod{n/p}$ has $\psi(a) \ne 1$.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.Table6

namespace QuadFormsKB.ConwaySloane.Mass

open Complex ZMod Finset QuadFormsKB.Binary
open scoped Real

/-- **$G(\psi)^2 = \psi(-1)\,k_1$** for a primitive real Dirichlet character $\psi$ modulo $k_1$ ($\bar\psi = \psi$), from
Fourier inversion on $\mathbb Z/k_1$ and $\hat\psi(k) = G(\psi)\,\bar\psi(-k)$. -/
theorem gaussSum_sq_of_real {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hreal : χ⁻¹ = χ) : gaussSum χ stdAddChar ^ 2 = χ (-1) * N := by
  have hF : 𝓕 (χ : ZMod N → ℂ) = fun k => gaussSum χ stdAddChar • (fun j => χ (-j)) k := by
    funext k
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, hreal, smul_eq_mul, mul_comm]
  have h := congrFun (dft_dft (χ : ZMod N → ℂ)) 1
  rw [hF] at h
  rw [show (fun k => gaussSum χ stdAddChar • (fun j => χ (-j)) k) =
      gaussSum χ stdAddChar • (fun j => (χ : ZMod N → ℂ) (-j)) from rfl, _root_.map_smul, dft_comp_neg] at h
  simp only [Pi.smul_apply, hF, neg_neg, smul_eq_mul, MulChar.map_one, mul_one] at h
  rw [sq, h, mul_comm]

/-- **Positivity of $\zeta_D$**: $\zeta_D(s) \ge 0$ for real $s > 1$, since every factor $(1 - \chi_D(p)p^{-s})^{-1}$ of the
Euler product (8) is positive. -/
theorem zetaD_nonneg {D : ℤ} (hD : D ≠ 0) {s : ℝ} (hs : 1 < s) : 0 ≤ zetaD D s := by
  refine (eulerProduct_zetaD hD hs).nonneg (fun p => inv_nonneg.mpr ?_)
  have hp1 : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.prop.one_lt.le
  have hle : ((p : ℕ) : ℝ) ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
  have hge : 0 ≤ ((p : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (by linarith) _
  have htri : chiD D p = 0 ∨ chiD D p = 1 ∨ chiD D p = -1 := by
    unfold chiD
    split_ifs
    · exact Or.inl rfl
    · exact jacobiSym.trichotomy _ _
  rcases htri with h | h | h <;> rw [h] <;> push_cast <;> linarith

/-- **(13) without the sign of the Gauss sum**: under the hypotheses of `zetaD_formula`, if the Euler factor
$\prod_{p \mid 4D}(1 - \psi(p)p^{-s})$ is the rational number $E$ and $\sum_{r=1}^{k_1}\psi(r)B_s(r/k_1)$ is the rational
number $S$, then $\zeta_D(s) = \lvert E\rvert(2\pi)^s\lvert S\rvert/(2\,s!\sqrt{k_1})$. -/
@[kb "conwaysloane1988" "§8 (13), p. 268"]
theorem zetaD_eq_abs {D : ℤ} (hD : D ≠ 0) {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hreal : χ⁻¹ = χ) (hdvd : N ∣ 4 * D.natAbs)
    (hval : ∀ m : ℕ, (chiD D m : ℂ) = DirichletCharacter.changeLevel hdvd χ (m : ZMod (4 * D.natAbs)))
    {s : ℕ} (hs : 2 ≤ s) (hpar : χ (-1) = (-1) ^ s) (E S : ℚ)
    (hE : ∏ p ∈ (4 * D.natAbs).primeFactors, (1 - χ p * (p : ℂ) ^ (-(s : ℂ))) = (E : ℂ))
    (hS : ∑ r ∈ Icc 1 N, χ r * (((Polynomial.bernoulli s).eval ((r : ℚ) / N) : ℚ) : ℂ) = (S : ℂ)) :
    zetaD D s = |(E : ℝ)| * (2 * π) ^ s * |(S : ℝ)| / (2 * s.factorial * Real.sqrt N) := by
  have hG2 := gaussSum_sq_of_real hχ hreal
  rw [hpar] at hG2
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hG : gaussSum χ stdAddChar ≠ 0 := by
    intro h0
    rw [h0] at hG2
    have : ((-1 : ℂ) ^ s) * N ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hN
    exact this (by rw [← hG2]; ring)
  have h := zetaD_formula hD hχ hreal hdvd hval hs hpar hG
  rw [hE, hS, hpar, I_cpow_neg_add] at h
  set X : ℝ := (E : ℝ) * (2 * π) ^ s * (S : ℝ) / (2 * s.factorial) with hX
  have hsq : (zetaD D s) ^ 2 * N = X ^ 2 := by
    apply Complex.ofReal_injective
    push_cast
    rw [h]
    have hI : I ^ s ≠ 0 := pow_ne_zero _ I_ne_zero
    have hI2 : (I ^ s) ^ 2 = (-1) ^ s := by rw [← pow_mul, mul_comm, pow_mul, I_sq]
    have hf : (s.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos s).ne'
    have e : ((E : ℂ) * (-(2 * (π : ℂ)) ^ s / ((s.factorial : ℂ) * (2 * (I ^ s)⁻¹))) * (S : ℂ) /
        gaussSum χ stdAddChar) ^ 2 * N =
        ((E : ℂ) * (2 * π) ^ s * S / (2 * s.factorial)) ^ 2 * ((I ^ s) ^ 2 * N / gaussSum χ stdAddChar ^ 2) := by
      field_simp
    rw [e, hI2, hG2, div_self (mul_ne_zero (pow_ne_zero _ (by norm_num)) hN), mul_one, hX]
    push_cast
    ring
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hz := zetaD_nonneg hD (show (1 : ℝ) < (s : ℕ) by exact_mod_cast hs)
  have hz' : zetaD D s = |X| / Real.sqrt N := by
    rw [eq_div_iff (Real.sqrt_pos.mpr hNr).ne', ← Real.sqrt_sq_eq_abs, ← hsq,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hz]
  rw [hz', hX, abs_div, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π) ^ s),
    abs_of_pos (by positivity : (0 : ℝ) < 2 * s.factorial)]
  field_simp

/-- **A Table 6 entry from (13)**: under the hypotheses of `zetaD_eq_abs`, if $\sqrt d = c\sqrt{k_1}$ with $c$ rational,
then $\zeta_D(s)\,d^{s-1}\sqrt d/\pi^s$ is the rational number $\lvert E\rvert\,2^s\lvert S\rvert\,d^{s-1}c/(2\,s!)$. -/
theorem table6_eq_abs {D : ℤ} (hD : D ≠ 0) {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hreal : χ⁻¹ = χ) (hdvd : N ∣ 4 * D.natAbs)
    (hval : ∀ m : ℕ, (chiD D m : ℂ) = DirichletCharacter.changeLevel hdvd χ (m : ZMod (4 * D.natAbs)))
    {s : ℕ} (hs : 2 ≤ s) (hpar : χ (-1) = (-1) ^ s) (E S : ℚ)
    (hE : ∏ p ∈ (4 * D.natAbs).primeFactors, (1 - χ p * (p : ℂ) ^ (-(s : ℂ))) = (E : ℂ))
    (hS : ∑ r ∈ Icc 1 N, χ r * (((Polynomial.bernoulli s).eval ((r : ℚ) / N) : ℚ) : ℂ) = (S : ℂ))
    (d : ℕ) (c : ℚ) (hc : Real.sqrt d = c * Real.sqrt N) :
    zetaD D s * (d : ℝ) ^ (s - 1) * Real.sqrt d / π ^ s =
      ((|E| * 2 ^ s * |S| * (d : ℚ) ^ (s - 1) * c / (2 * s.factorial) : ℚ) : ℝ) := by
  rw [zetaD_eq_abs hD hχ hreal hdvd hval hs hpar E S hE hS, hc]
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hsN : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hNr).ne'
  have hπ : π ^ s ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hf : (s.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos s).ne'
  push_cast
  field_simp
  ring

/-- An integer whose absolute value has no repeated prime factor is squarefree. -/
theorem int_squarefree_of_nodup {n : ℤ} (h0 : n ≠ 0) (h : (Nat.primeFactorsList n.natAbs).Nodup) :
    Squarefree n :=
  Int.squarefree_natAbs.mp ((Nat.squarefree_iff_nodup_primeFactorsList (Int.natAbs_ne_zero.mpr h0)).mpr h)

/-- The trivial character modulo $1$ takes the value $1$ everywhere. -/
theorem one_level_one_apply (x : ZMod 1) : (1 : DirichletCharacter ℂ 1) x = 1 :=
  MulChar.one_apply (isUnit_of_subsingleton x)

/-- $\sqrt d = (a/b)\sqrt N$ when $b^2 d = a^2 N$ (natural numbers, $b > 0$). -/
theorem sqrt_eq_rat_mul_sqrt {d N a b : ℕ} (hb : 0 < b) (h : b ^ 2 * d = a ^ 2 * N) :
    Real.sqrt d = ((a / b : ℚ) : ℝ) * Real.sqrt N := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have e0 : (b : ℝ) ^ 2 * d = (a : ℝ) ^ 2 * N := by exact_mod_cast h
  have e := congrArg Real.sqrt e0
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hb'.le,
    Real.sqrt_sq (Nat.cast_nonneg _)] at e
  push_cast
  field_simp
  linarith

/-- **Primitivity from one witness per prime**: a Dirichlet character $\psi$ modulo $n$ is primitive if for every prime
$p \mid n$ there is an integer $a$ coprime to $n$ with $a \equiv 1 \pmod{n/p}$ and $\psi(a) \ne 1$ (every proper divisor of
$n$ divides some $n/p$). -/
theorem isPrimitive_of_prime_witness {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n)
    (h : ∀ p ∈ n.primeFactors, ∃ a : ℤ, IsCoprime a n ∧ (a : ZMod (n / p)) = 1 ∧ χ a ≠ 1) :
    χ.IsPrimitive := by
  refine isPrimitive_of_witness χ (fun d hd hlt => ?_)
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  obtain ⟨k, hk⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hk; omega)
  have hk1 : k ≠ 1 := by rintro rfl; omega
  obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd hk1
  obtain ⟨j, hj⟩ := hpk
  have hpn : p ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, ⟨d * j, by rw [hk, hj]; ring⟩, hn.ne'⟩
  obtain ⟨a, ha, ha1, hne⟩ := h p hpn
  refine ⟨a, ha, ?_, hne⟩
  have hdp : d ∣ n / p := ⟨j, by
    rw [hk, hj, show d * (p * j) = p * (d * j) by ring, Nat.mul_div_cancel_left _ hp.pos]⟩
  have := congrArg (ZMod.castHom hdp (ZMod d)) ha1
  rwa [map_intCast, map_one] at this

end QuadFormsKB.ConwaySloane.Mass
