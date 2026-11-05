/-
# Conway–Sloane 1988, §8: the primitive characters of conductor $3, 4, 8, 12$ and their Gauss sums

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §8, pp. 268–269 (the Gauss sum $G(\psi)$ of (11), (13) and the characters $\psi$ of
Table 5).

**Definitions (book $\to$ Lean).** The primitive character $\psi$ attached to $D$ in §8 is the Kronecker character
$\left(\frac{\Delta}{\cdot}\right)$ of the fundamental discriminant $\Delta$ of $\mathbb Q(\sqrt D)$, i.e. the repository's
`Binary.kroneckerChar Δ`, a Dirichlet character modulo $k_1 = \lvert\Delta\rvert$. This file uses five of them, with the
modulus written as a numeral:

| Lean | $\Delta$ | $k_1$ | $D$ of §8 | values $\psi(1), \dots, \psi(k_1)$ (Table 5) | $G(\psi)$ |
|---|---|---|---|---|---|
| `psiNeg3` | $-3$ | $3$ | $-3$ | $+,-,0$ | $i\sqrt3$ |
| `psiNeg4` | $-4$ | $4$ | $-1$ | $+,0,-,0$ | $2i$ |
| `psi8` | $8$ | $8$ | $2$ | $+,0,-,0,-,0,+,0$ | $2\sqrt2$ |
| `psiNeg8` | $-8$ | $8$ | $-2$ | $+,0,+,0,-,0,-,0$ | $2i\sqrt2$ |
| `psi12` | $12$ | $12$ | $3$ | $+,0,0,0,-,0,-,0,0,0,+,0$ | $2\sqrt3$ |

Here $G(\psi) = \sum_{r=1}^{k_1}\psi(r)e^{2\pi i r/k_1}$ is `gaussSum ψ stdAddChar` (see `ZetaFormula.lean`).

**Proves**
* `gaussSum_psiNeg3`, `gaussSum_psiNeg4`, `gaussSum_psi8`, `gaussSum_psiNeg8`, `gaussSum_psi12`: the Gauss sums of the
  table, by direct evaluation of the finite sums of roots of unity (no general sign theorem is used).
* `isPrimitive_psiNeg3`, …: each character is primitive (its conductor is $k_1$), via `isPrimitive_of_witness`: a character
  modulo $n$ is primitive if for every proper divisor $d$ of $n$ some $a \equiv 1 \pmod d$ coprime to $n$ has $\psi(a) \ne 1$.
* `kroneckerChar_inv`: the Kronecker characters are real, $\bar\psi = \psi$.
* `chiD_eq_changeLevel_*`: $\chi_D = \chi_1\psi$ on $\mathbb Z/4\lvert D\rvert$ for $D = -3, -1, 2, -2, 3$ (the hypothesis `hval` of
  `zetaD_formula`), by a check over one period.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.ZetaFormula
import QuadFormsKB.Tamagawa.Classical.LValues
import QuadFormsKB.Tamagawa.SiegelBinaryAllRat

namespace QuadFormsKB.ConwaySloane.Mass

open Complex ZMod Finset QuadFormsKB.Binary
open scoped Real

/-! ### General tools -/

/-- **Primitivity criterion.** A Dirichlet character $\psi$ modulo $n$ is primitive if for every proper divisor $d$ of $n$
there is an integer $a$ coprime to $n$ with $a \equiv 1 \pmod d$ and $\psi(a) \ne 1$ (then $\psi$ does not factor through
$\mathbb Z/d$). -/
theorem isPrimitive_of_witness {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n)
    (h : ∀ d, d ∣ n → d < n → ∃ a : ℤ, IsCoprime a n ∧ (a : ZMod d) = 1 ∧ χ a ≠ 1) :
    χ.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  by_contra hne
  have hc := χ.conductor_dvd_level
  have hlt : χ.conductor < n :=
    lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) hc) hne
  obtain ⟨a, hcop, ha1, hne1⟩ := h _ hc hlt
  have hf := χ.factorsThrough_conductor
  have e := congrArg (fun ψ : DirichletCharacter ℂ n => ψ (a : ZMod n)) hf.eq_changeLevel
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop, ha1, map_one] at e
  exact hne1 e

theorem sum_zmod_eq_sum_range {N : ℕ} [NeZero N] (F : ZMod N → ℂ) :
    ∑ x : ZMod N, F x = ∑ r ∈ range N, F r := by
  refine Finset.sum_nbij' (fun x => x.val) (fun r => (r : ZMod N)) ?_ ?_ ?_ ?_ ?_
  · intro x _; exact mem_range.mpr (ZMod.val_lt x)
  · intro r _; exact mem_univ _
  · intro x _; simp
  · intro r hr; simp [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp hr)]
  · intro x _; simp

/-- The Gauss sum as the explicit sum $\sum_{r=0}^{M-1}\psi(r)e^{2\pi i r/M}$ (for the modulus $N = M$). -/
theorem gaussSum_eq_sum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (M : ℕ) (hM : N = M) :
    gaussSum χ stdAddChar = ∑ r ∈ range M, χ r * cexp (2 * π * I * r / M) := by
  subst hM
  rw [gaussSum, sum_zmod_eq_sum_range]
  refine sum_congr rfl (fun r _ => ?_)
  rw [show ((r : ZMod N)) = ((r : ℤ) : ZMod N) by simp, stdAddChar_coe]
  simp

theorem cexp_two_pi (r N : ℕ) :
    cexp (2 * π * I * r / N) = Real.cos (2 * π * r / N) + Real.sin (2 * π * r / N) * I := by
  rw [show 2 * π * I * r / N = ((2 * π * r / N : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
    ← ofReal_cos, ← ofReal_sin]

/-- The Kronecker characters are real: $\bar\psi = \psi$. -/
theorem kroneckerChar_inv (Δ : ℤ) [IsQuadDisc Δ] : (kroneckerChar Δ)⁻¹ = kroneckerChar Δ := by
  refine MulChar.ext' (fun a => ?_)
  rw [MulChar.inv_apply_eq_inv', kroneckerChar_apply]
  have : kronZ Δ a = 0 ∨ kronZ Δ a = 1 ∨ kronZ Δ a = -1 := by
    unfold kronZ
    split_ifs
    · exact jacobiSym.trichotomy _ _
    · exact jacobiSym.trichotomy _ _
    · exact Or.inl rfl
  rcases this with h | h | h <;> simp [h]

/-- For $4 \mid \Delta$ the Kronecker character is $\chi_{\Delta/4}$ of Conway–Sloane. -/
theorem kroneckerChar_natCast_of_zero (Δ : ℤ) [IsQuadDisc Δ] (h : Δ % 4 = 0) (n : ℕ) :
    kroneckerChar Δ (n : ZMod Δ.natAbs) = (chiD (Δ / 4) n : ℂ) := by
  rw [kroneckerChar_apply]
  rcases Nat.even_or_odd n with he | ho
  · have hn : n % 2 = 0 := Nat.even_iff.mp he
    have hno : ¬ Odd (n % Δ.natAbs) := by
      rw [odd_mod_natAbs_iff (by omega)]
      exact Nat.not_odd_iff_even.mpr he
    simp [kronZ, chiD, hn, hno, show Δ % 4 ≠ 1 by omega]
  · rw [kronZ_natCast_of_zero h ho]
    simp [chiD, Nat.odd_iff.mp ho]

/-- For $\Delta \equiv 1 \pmod 4$ the Kronecker character is $n \mapsto \left(\frac{n}{\lvert\Delta\rvert}\right)$. -/
theorem kroneckerChar_natCast_of_one (Δ : ℤ) [IsQuadDisc Δ] (h : Δ % 4 = 1) (n : ℕ) :
    kroneckerChar Δ (n : ZMod Δ.natAbs) = (jacobiSym n Δ.natAbs : ℂ) := by
  rw [kroneckerChar_apply, kronZ_natCast_of_one h]

/-! ### The instances for $\Delta = -8, 12$ -/

instance isQuadDisc_neg_eight : IsQuadDisc (-8) where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    right
    refine ⟨?_, ?_, ?_⟩ <;> norm_num
    exact Int.prime_two.neg.squarefree
  ne_one := by norm_num

instance isQuadDisc_twelve : IsQuadDisc 12 where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    right
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  ne_one := by norm_num

/-! ### The five characters -/

/-- $\psi$ for $D = -3$: the character $\left(\frac{-3}{\cdot}\right) = \left(\frac{\cdot}{3}\right)$ modulo $3$. -/
@[kb "conwaysloane1988" "§8, Table 5, p. 269 (D = -3)"]
noncomputable def psiNeg3 : DirichletCharacter ℂ 3 := kroneckerChar (-3)

/-- $\psi$ for $D = -1$: the character $\left(\frac{-4}{\cdot}\right)$ modulo $4$. -/
@[kb "conwaysloane1988" "§8, Table 5, p. 269 (D = -1)"]
noncomputable def psiNeg4 : DirichletCharacter ℂ 4 := kroneckerChar (-4)

/-- $\psi$ for $D = 2$: the character $\left(\frac{8}{\cdot}\right)$ modulo $8$. -/
@[kb "conwaysloane1988" "§8, Table 5, p. 269 (D = 2)"]
noncomputable def psi8 : DirichletCharacter ℂ 8 := kroneckerChar 8

/-- $\psi$ for $D = -2$: the character $\left(\frac{-8}{\cdot}\right)$ modulo $8$. -/
@[kb "conwaysloane1988" "§8, Table 5, p. 269 (D = -2)"]
noncomputable def psiNeg8 : DirichletCharacter ℂ 8 := kroneckerChar (-8)

/-- $\psi$ for $D = 3$: the character $\left(\frac{12}{\cdot}\right)$ modulo $12$. -/
@[kb "conwaysloane1988" "§8, Table 5, p. 269 (D = 3)"]
noncomputable def psi12 : DirichletCharacter ℂ 12 := kroneckerChar 12

theorem psiNeg3_natCast (n : ℕ) : psiNeg3 n = (jacobiSym n 3 : ℂ) :=
  kroneckerChar_natCast_of_one (-3) (by norm_num) n

theorem psiNeg4_natCast (n : ℕ) : psiNeg4 n = (chiD (-1) n : ℂ) :=
  kroneckerChar_natCast_of_zero (-4) (by norm_num) n

theorem psi8_natCast (n : ℕ) : psi8 n = (chiD 2 n : ℂ) :=
  kroneckerChar_natCast_of_zero 8 (by norm_num) n

theorem psiNeg8_natCast (n : ℕ) : psiNeg8 n = (chiD (-2) n : ℂ) :=
  kroneckerChar_natCast_of_zero (-8) (by norm_num) n

theorem psi12_natCast (n : ℕ) : psi12 n = (chiD 3 n : ℂ) :=
  kroneckerChar_natCast_of_zero 12 (by norm_num) n

theorem psiNeg3_inv : psiNeg3⁻¹ = psiNeg3 := kroneckerChar_inv (-3)
theorem psiNeg4_inv : psiNeg4⁻¹ = psiNeg4 := kroneckerChar_inv (-4)
theorem psi8_inv : psi8⁻¹ = psi8 := kroneckerChar_inv 8
theorem psiNeg8_inv : psiNeg8⁻¹ = psiNeg8 := kroneckerChar_inv (-8)
theorem psi12_inv : psi12⁻¹ = psi12 := kroneckerChar_inv 12

/-! ### Parity: $\psi(-1)$ -/

theorem psiNeg3_neg_one : psiNeg3 (-1) = -1 := by
  rw [show (-1 : ZMod 3) = ((2 : ℕ) : ZMod 3) by decide, psiNeg3_natCast]; norm_num

theorem psiNeg4_neg_one : psiNeg4 (-1) = -1 := by
  rw [show (-1 : ZMod 4) = ((3 : ℕ) : ZMod 4) by decide, psiNeg4_natCast]; norm_num [chiD]

theorem psi8_neg_one : psi8 (-1) = 1 := by
  rw [show (-1 : ZMod 8) = ((7 : ℕ) : ZMod 8) by decide, psi8_natCast]; norm_num [chiD]

theorem psiNeg8_neg_one : psiNeg8 (-1) = -1 := by
  rw [show (-1 : ZMod 8) = ((7 : ℕ) : ZMod 8) by decide, psiNeg8_natCast]; norm_num [chiD]

theorem psi12_neg_one : psi12 (-1) = 1 := by
  rw [show (-1 : ZMod 12) = ((11 : ℕ) : ZMod 12) by decide, psi12_natCast]; norm_num [chiD]

/-! ### Primitivity -/

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -3, conductor 3)"]
theorem isPrimitive_psiNeg3 : psiNeg3.IsPrimitive := by
  refine isPrimitive_of_witness _ (fun d hd hlt => ⟨2, by norm_num [Int.isCoprime_iff_gcd_eq_one], ?_, ?_⟩)
  · interval_cases d <;> first | decide | (exfalso; norm_num at hd)
  · rw [show ((2 : ℤ) : ZMod 3) = ((2 : ℕ) : ZMod 3) by norm_cast, psiNeg3_natCast]; norm_num

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -1, conductor 4)"]
theorem isPrimitive_psiNeg4 : psiNeg4.IsPrimitive := by
  refine isPrimitive_of_witness _ (fun d hd hlt => ⟨3, by norm_num [Int.isCoprime_iff_gcd_eq_one], ?_, ?_⟩)
  · interval_cases d <;> first | decide | (exfalso; norm_num at hd)
  · rw [show ((3 : ℤ) : ZMod 4) = ((3 : ℕ) : ZMod 4) by norm_cast, psiNeg4_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 2, conductor 8)"]
theorem isPrimitive_psi8 : psi8.IsPrimitive := by
  refine isPrimitive_of_witness _ (fun d hd hlt => ⟨5, by norm_num [Int.isCoprime_iff_gcd_eq_one], ?_, ?_⟩)
  · interval_cases d <;> first | decide | (exfalso; norm_num at hd)
  · rw [show ((5 : ℤ) : ZMod 8) = ((5 : ℕ) : ZMod 8) by norm_cast, psi8_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = -2, conductor 8)"]
theorem isPrimitive_psiNeg8 : psiNeg8.IsPrimitive := by
  refine isPrimitive_of_witness _ (fun d hd hlt => ⟨5, by norm_num [Int.isCoprime_iff_gcd_eq_one], ?_, ?_⟩)
  · interval_cases d <;> first | decide | (exfalso; norm_num at hd)
  · rw [show ((5 : ℤ) : ZMod 8) = ((5 : ℕ) : ZMod 8) by norm_cast, psiNeg8_natCast]; norm_num [chiD]

@[kb "conwaysloane1988" "§8, Table 4, p. 269 (D = 3, conductor 12)"]
theorem isPrimitive_psi12 : psi12.IsPrimitive := by
  refine isPrimitive_of_witness _ (fun d hd hlt => ?_)
  interval_cases d <;> norm_num at hd
  · exact ⟨5, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((5 : ℤ) : ZMod 12) = ((5 : ℕ) : ZMod 12) by norm_cast, psi12_natCast]; norm_num [chiD]⟩
  · exact ⟨5, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((5 : ℤ) : ZMod 12) = ((5 : ℕ) : ZMod 12) by norm_cast, psi12_natCast]; norm_num [chiD]⟩
  · exact ⟨7, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((7 : ℤ) : ZMod 12) = ((7 : ℕ) : ZMod 12) by norm_cast, psi12_natCast]; norm_num [chiD]⟩
  · exact ⟨5, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((5 : ℤ) : ZMod 12) = ((5 : ℕ) : ZMod 12) by norm_cast, psi12_natCast]; norm_num [chiD]⟩
  · exact ⟨7, by norm_num [Int.isCoprime_iff_gcd_eq_one], by decide,
      by rw [show ((7 : ℤ) : ZMod 12) = ((7 : ℕ) : ZMod 12) by norm_cast, psi12_natCast]; norm_num [chiD]⟩

/-! ### The Gauss sums -/

/-- **$G(\psi) = i\sqrt3$** for the character $\psi$ modulo $3$ of $D = -3$:
$e^{2\pi i/3} - e^{4\pi i/3} = i\sqrt3$. -/
@[kb "conwaysloane1988" "§8 (11), p. 268 (Gauss sum, D = -3)"]
theorem gaussSum_psiNeg3 : gaussSum psiNeg3 stdAddChar = I * Real.sqrt 3 := by
  rw [gaussSum_eq_sum _ 3 rfl]
  simp only [sum_range_succ, sum_range_zero, psiNeg3_natCast, cexp_two_pi]
  have a1 : (2 * π * ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = π - π / 3 := by push_cast; ring
  have a2 : (2 * π * ((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = π / 3 + π := by push_cast; ring
  rw [a1, a2, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_add_pi, Real.sin_add_pi,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  norm_num
  ring

/-- **$G(\psi) = 2i$** for the character $\psi$ modulo $4$ of $D = -1$: $e^{\pi i/2} - e^{3\pi i/2} = 2i$. -/
@[kb "conwaysloane1988" "§8 (11), p. 268 (Gauss sum, D = -1)"]
theorem gaussSum_psiNeg4 : gaussSum psiNeg4 stdAddChar = 2 * I := by
  rw [gaussSum_eq_sum _ 4 rfl]
  simp only [sum_range_succ, sum_range_zero, psiNeg4_natCast, cexp_two_pi]
  have a1 : (2 * π * ((1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = π / 2 := by push_cast; ring
  have a3 : (2 * π * ((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = π / 2 + π := by push_cast; ring
  rw [a1, a3, Real.cos_add_pi, Real.sin_add_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
  norm_num [chiD]
  ring

/-- **$G(\psi) = 2\sqrt2$** for the character $\psi$ modulo $8$ of $D = 2$:
$e^{\pi i/4} - e^{3\pi i/4} - e^{5\pi i/4} + e^{7\pi i/4} = 2\sqrt2$. -/
@[kb "conwaysloane1988" "§8 (11), p. 268 (Gauss sum, D = 2)"]
theorem gaussSum_psi8 : gaussSum psi8 stdAddChar = 2 * Real.sqrt 2 := by
  rw [gaussSum_eq_sum _ 8 rfl]
  simp only [sum_range_succ, sum_range_zero, psi8_natCast, cexp_two_pi]
  have a1 : (2 * π * ((1 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = π / 4 := by push_cast; ring
  have a3 : (2 * π * ((3 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = π - π / 4 := by push_cast; ring
  have a5 : (2 * π * ((5 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = π / 4 + π := by push_cast; ring
  have a7 : (2 * π * ((7 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = (π - π / 4) + π := by push_cast; ring
  rw [a1, a3, a5, a7]
  simp only [Real.cos_add_pi, Real.sin_add_pi, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  norm_num [chiD]
  ring

/-- **$G(\psi) = 2i\sqrt2$** for the character $\psi$ modulo $8$ of $D = -2$:
$e^{\pi i/4} + e^{3\pi i/4} - e^{5\pi i/4} - e^{7\pi i/4} = 2i\sqrt2$. -/
@[kb "conwaysloane1988" "§8 (11), p. 268 (Gauss sum, D = -2)"]
theorem gaussSum_psiNeg8 : gaussSum psiNeg8 stdAddChar = 2 * I * Real.sqrt 2 := by
  rw [gaussSum_eq_sum _ 8 rfl]
  simp only [sum_range_succ, sum_range_zero, psiNeg8_natCast, cexp_two_pi]
  have a1 : (2 * π * ((1 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = π / 4 := by push_cast; ring
  have a3 : (2 * π * ((3 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = π - π / 4 := by push_cast; ring
  have a5 : (2 * π * ((5 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = π / 4 + π := by push_cast; ring
  have a7 : (2 * π * ((7 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = (π - π / 4) + π := by push_cast; ring
  rw [a1, a3, a5, a7]
  simp only [Real.cos_add_pi, Real.sin_add_pi, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  norm_num [chiD]
  ring

/-- **$G(\psi) = 2\sqrt3$** for the character $\psi$ modulo $12$ of $D = 3$:
$e^{\pi i/6} - e^{5\pi i/6} - e^{7\pi i/6} + e^{11\pi i/6} = 2\sqrt3$. -/
@[kb "conwaysloane1988" "§8 (11), p. 268 (Gauss sum, D = 3)"]
theorem gaussSum_psi12 : gaussSum psi12 stdAddChar = 2 * Real.sqrt 3 := by
  rw [gaussSum_eq_sum _ 12 rfl]
  simp only [sum_range_succ, sum_range_zero, psi12_natCast, cexp_two_pi]
  have a1 : (2 * π * ((1 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = π / 6 := by push_cast; ring
  have a5 : (2 * π * ((5 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = π - π / 6 := by push_cast; ring
  have a7 : (2 * π * ((7 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = π / 6 + π := by push_cast; ring
  have a11 : (2 * π * ((11 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = (π - π / 6) + π := by push_cast; ring
  rw [a1, a5, a7, a11]
  simp only [Real.cos_add_pi, Real.sin_add_pi, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_six,
    Real.sin_pi_div_six]
  norm_num [chiD]
  ring

/-! ### $\chi_D = \chi_1\psi$ -/

theorem chiD_eq_changeLevel_neg3 :
    ∀ m : ℕ, (chiD (-3) m : ℂ) = DirichletCharacter.changeLevel (show 3 ∣ 4 * (-3 : ℤ).natAbs by decide)
      psiNeg3 (m : ZMod (4 * (-3 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (-3 : ℤ).natAbs) < 12 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (-3 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psiNeg3_natCast] <;> norm_num [chiD]

theorem chiD_eq_changeLevel_neg1 :
    ∀ m : ℕ, (chiD (-1) m : ℂ) = DirichletCharacter.changeLevel (show 4 ∣ 4 * (-1 : ℤ).natAbs by decide)
      psiNeg4 (m : ZMod (4 * (-1 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (-1 : ℤ).natAbs) < 4 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (-1 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psiNeg4_natCast] <;> norm_num [chiD]

theorem chiD_eq_changeLevel_two :
    ∀ m : ℕ, (chiD 2 m : ℂ) = DirichletCharacter.changeLevel (show 8 ∣ 4 * (2 : ℤ).natAbs by decide)
      psi8 (m : ZMod (4 * (2 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (2 : ℤ).natAbs) < 8 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (2 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psi8_natCast] <;> norm_num [chiD]

theorem chiD_eq_changeLevel_neg2 :
    ∀ m : ℕ, (chiD (-2) m : ℂ) = DirichletCharacter.changeLevel (show 8 ∣ 4 * (-2 : ℤ).natAbs by decide)
      psiNeg8 (m : ZMod (4 * (-2 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (-2 : ℤ).natAbs) < 8 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (-2 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psiNeg8_natCast] <;> norm_num [chiD]

theorem chiD_eq_changeLevel_three :
    ∀ m : ℕ, (chiD 3 m : ℂ) = DirichletCharacter.changeLevel (show 12 ∣ 4 * (3 : ℤ).natAbs by decide)
      psi12 (m : ZMod (4 * (3 : ℤ).natAbs)) := by
  intro m
  rw [← chiD_mod, ← ZMod.natCast_mod m, changeLevel_natCast]
  have hr : m % (4 * (3 : ℤ).natAbs) < 12 := Nat.mod_lt _ (by norm_num)
  generalize m % (4 * (3 : ℤ).natAbs) = r at hr ⊢
  interval_cases r <;> simp only [psi12_natCast] <;> norm_num [chiD]

end QuadFormsKB.ConwaySloane.Mass
