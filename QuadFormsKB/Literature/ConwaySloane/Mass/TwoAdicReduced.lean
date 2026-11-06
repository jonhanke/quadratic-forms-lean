/-
# Formula (3) at $p = 2$ reduced to two statements about unimodular forms

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), (3), p. 263, Tables 1–2, p. 264, §5–6, pp. 265–266 (bibliography key `conwaysloane1988`).

By `pMassDensity_blk_two_rho` (`TwoAdicRho.lean`), splitting off the unimodular constituent $U = f_1$ of $U \perp 2B$
changes the 2-mass by $m_2(U)\,2^{as/2}/\rho(U, B)$, where $\rho(U, B)$ is the proportion of $W$ (modulo $4$) with
$U + 2W^{\mathsf T}BW \sim U$. Comparing with the recursion of the right-hand side of (3) (`pMassTwo_succ`), the one-step
identity `StepEq` holds as soon as
* $m_2(U)$ is given by (3) for the unimodular form $U$ alone, and
* $\rho(U, B)$ has the value `rhoValue σ` read from the symbol $\sigma$:
  $1$ if $f_1$, $f_2$ have type II; $P(f_1)$ if $f_1$ has type II and $f_2$ type I; for $f_1$ of type I and $f_2$ of type
  II, $\frac12$ if $f_4$ has type I and $P(f_2)$ otherwise; for $f_1$, $f_2$ of type I, $\frac18 r(f_1) r'(f_2)$ with
  $r'(f_2) = 1$ if $f_4$ has type I and $r(f_2)$ otherwise. Here $P(f) = \frac12(1 + \varepsilon 2^{-t})$ for a type II
  constituent of dimension $2t$ and sign $\varepsilon$ (the proportion of zeros of its quadratic form over
  $\mathbb F_2$), and $r(f) = M_2^{\mathrm{free}}(f)/M_2^{\mathrm{bound}}(f)$ for a type I constituent: $1$ for octane
  value $\pm2$, $1 + 2^{-t}$ for $0, \pm1$, $1 - 2^{-t}$ for $\pm3, 4$, $t = \lfloor (n-1)/2\rfloor$ (Table 1).

**Proves** `stepFactor_lowT` (the ratio of the right-hand sides of (3) for $U$ alone and for $U \perp 2B$ is
`rhoValue σ`), `stepEq_of_rho` (the one-step identity from the two statements), and
`pMassStepTwoTypeI_of_inputs`: the former input `PMassStepTwoTypeI` follows from the two named inputs
`PMassUnimodularTwoTypeI` (formula (3) for a single unimodular constituent of type I) and `RhoValueTwo` (the value of
$\rho$ when $f_1$ or $f_2$ has type I). Both are statements about unimodular forms over $\mathbb Z_2$ only. The values
of $\rho$ were checked numerically (outside Lean, 408 cases). Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicRho
import QuadFormsKB.Literature.ConwaySloane.Mass.MainTwo
import QuadFormsKB.Literature.ConwaySloane.LocalExistence

set_option linter.unusedSectionVars false

namespace QuadFormsKB.ConwaySloane.Mass.Two

open Matrix QuadFormsKB.Cassels QuadFormsKB.ConwaySloane

/-! ### Free and bound diagonal factors -/

/-- The diagonal factor $M_2$ of a 2-adic constituent when it is free. -/
def mFree (f : TwoFactor) : ℚ := (twoSpecies f False).diagFactor 2

/-- The diagonal factor $M_2$ of a 2-adic constituent when it is bound. -/
def mBound (f : TwoFactor) : ℚ := (twoSpecies f True).diagFactor 2

/-- $t$ of Table 1: $n/2$ for type II, $(n-1)/2$ for type I. -/
def tq (f : TwoFactor) : ℕ := if f.type = .II then f.dim / 2 else (f.dim - 1) / 2

theorem lowerProd_succ (t : ℕ) : lowerProd 2 (t + 1) = lowerProd 2 t * (1 - ((2 : ℚ) ^ (2 * (t + 1)))⁻¹) :=
  Finset.prod_range_succ _ _

theorem twoSpecies_true (f : TwoFactor) : twoSpecies f True = ⟨2 * tq f + 1, .plus⟩ := by
  simp [twoSpecies, tq]

theorem diagFactor_odd (t : ℕ) : Species.diagFactor 2 ⟨2 * t + 1, .plus⟩ = (2 * lowerProd 2 t)⁻¹ := by
  unfold Species.diagFactor
  simp only [show 2 * t + 1 ≠ 0 by omega, ite_false, show Odd (2 * t + 1) from odd_two_mul_add_one t, ite_true,
    show (2 * t + 1) / 2 = t by omega]
  norm_num

theorem mBound_eq (f : TwoFactor) : mBound f = (2 * lowerProd 2 (tq f))⁻¹ := by
  rw [mBound, twoSpecies_true, diagFactor_odd]

theorem diagFactor_even {t : ℕ} (ht : 1 ≤ t) (s : Sign) :
    (Species.diagFactor 2 ⟨2 * t, s⟩) = (2 * lowerProd 2 t)⁻¹ * (1 + s.toInt * ((2 : ℚ) ^ t)⁻¹) := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  unfold Species.diagFactor
  simp only [show 2 * (t + 1) ≠ 0 by omega, ite_false, show ¬ Odd (2 * (t + 1)) by simp, show 2 * (t + 1) / 2 - 1 = t by omega,
    show 2 * (t + 1) / 2 = t + 1 by omega]
  rw [lowerProd_succ]
  have hL := lowerProd_pos t
  have hx : (0 : ℚ) < ((2 : ℚ) ^ (t + 1))⁻¹ := by positivity
  have hx1 : ((2 : ℚ) ^ (t + 1))⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    calc ((1 : ℚ) / 2)⁻¹ = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (t + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have e : ((2 : ℚ) ^ (2 * (t + 1)))⁻¹ = ((2 : ℚ) ^ (t + 1))⁻¹ * ((2 : ℚ) ^ (t + 1))⁻¹ := by
    rw [← mul_inv, ← pow_add]; ring_nf
  rw [e]
  generalize ((2 : ℚ) ^ (t + 1))⁻¹ = x at hx hx1 ⊢
  have h2 : (1 : ℚ) - x * x ≠ 0 := by nlinarith
  cases s <;> simp only [Sign.toInt] <;> push_cast
  · have h1 : (1 : ℚ) - x ≠ 0 := by linarith
    have h3 : (1 : ℚ) - x ^ 2 ≠ 0 := by nlinarith
    field_simp
    ring
  · have h1 : (1 : ℚ) + x ≠ 0 := by linarith
    have h3 : (1 : ℚ) - x ^ 2 ≠ 0 := by nlinarith
    field_simp
    rw [div_eq_iff (by linarith)]
    ring

theorem mFac_eq (σ : TwoSymbol) (k : ℕ) : mFac σ k = if IsBound σ k then mBound (σ k) else mFree (σ k) := by
  unfold mFac mBound mFree
  split_ifs with h
  · exact congrArg _ (twoSpecies_congr (iff_true_intro h) rfl rfl rfl)
  · exact congrArg _ (twoSpecies_congr (iff_false_intro h) rfl rfl rfl)

theorem dim_even_of_II {f : TwoFactor} (hf : f.Exists) (ht : f.type = .II) : f.dim % 2 = 0 := by
  have h1 := hf.2.2.2.1
  rw [hf.2.2.2.2 ht] at h1
  simpa using h1.symm

theorem twoSpecies_false_II {f : TwoFactor} (hf : f.Exists) (ht : f.type = .II) :
    twoSpecies f False = ⟨2 * tq f, f.sign⟩ := by
  have ho := hf.2.2.2.2 ht
  unfold twoSpecies octane
  simp only [ht, ho, tq, ite_true, false_or, zero_add]
  cases f.sign
  · rw [if_neg (show ¬ (Sign.plus = Sign.minus) by decide), if_neg (by decide), if_neg (by decide)]
  · rw [if_pos rfl, if_neg (by decide), if_pos (by decide)]

/-- **Free over bound, type II**: $M_2^{\mathrm{free}}(f) = M_2^{\mathrm{bound}}(f)\,(1 + \varepsilon 2^{-t})$ for a type
II constituent of dimension $2t$ and sign $\varepsilon$. -/
theorem mFree_II {f : TwoFactor} (hf : f.Exists) (ht : f.type = .II) :
    mFree f = mBound f * (1 + f.sign.toInt * ((2 : ℚ) ^ (f.dim / 2))⁻¹) := by
  have hev := dim_even_of_II hf ht
  have htq : tq f = f.dim / 2 := by simp [tq, ht]
  rw [mFree, twoSpecies_false_II hf ht, mBound_eq, htq]
  rcases Nat.eq_zero_or_pos (f.dim / 2) with h0 | hpos
  · have hd : f.dim = 0 := by omega
    have hs : f.sign = .plus := (hf.1 hd).2
    rw [h0, hs]
    simp [Species.diagFactor, lowerProd, Sign.toInt]
    norm_num
  · rw [diagFactor_even hpos]

/-- $r(f) = M_2^{\mathrm{free}}(f)/M_2^{\mathrm{bound}}(f)$ for a type I constituent (Table 1): $1$ for octane value
$\pm2$, $1 - 2^{-t}$ for $\pm3, 4$, $1 + 2^{-t}$ for $0, \pm1$, $t = \lfloor (n-1)/2 \rfloor$. -/
def rI (f : TwoFactor) : ℚ :=
  if octane f = 2 ∨ octane f = 6 then 1
  else if octane f = 3 ∨ octane f = 4 ∨ octane f = 5 then 1 - ((2 : ℚ) ^ ((f.dim - 1) / 2))⁻¹
  else 1 + ((2 : ℚ) ^ ((f.dim - 1) / 2))⁻¹

theorem octane_small {f : TwoFactor} (hf : f.Exists) (ht : f.type = .I) (hd : f.dim ≤ 2) :
    octane f = 0 ∨ octane f = 1 ∨ octane f = 2 ∨ octane f = 6 ∨ octane f = 7 := by
  obtain ⟨h0, h1, h2, -, -⟩ := hf
  unfold octane
  rcases Nat.lt_or_ge f.dim 1 with hd0 | hd1
  · have := (h0 (by omega)).1; rw [ht] at this; exact absurd this (by decide)
  rcases Nat.lt_or_ge f.dim 2 with hd1' | hd2
  · obtain ⟨hp, hm⟩ := h1 (by omega)
    cases hs : f.sign
    · rcases hp hs with h | h <;> rw [h] <;> decide
    · rcases hm hs with h | h <;> rw [h] <;> decide
  · obtain ⟨hp, hm⟩ := h2 (by omega) ht
    cases hs : f.sign
    · rcases hp hs with h | h | h <;> rw [h] <;> decide
    · rcases hm hs with h | h | h <;> rw [h] <;> decide

/-- **Free over bound, type I**: $M_2^{\mathrm{free}}(f) = M_2^{\mathrm{bound}}(f)\,r(f)$. -/
theorem mFree_I {f : TwoFactor} (hf : f.Exists) (ht : f.type = .I) : mFree f = mBound f * rI f := by
  have htq : tq f = (f.dim - 1) / 2 := by simp [tq, ht]
  have hd1 : 1 ≤ f.dim := by
    by_contra h
    have := (hf.1 (by omega)).1
    rw [ht] at this; exact absurd this (by decide)
  rw [mBound_eq, htq, mFree, rI]
  unfold twoSpecies
  simp only [false_or, ht, show ¬ (ScaledType.I = ScaledType.II) by decide, ite_false]
  split_ifs with h26 h345
  · rw [diagFactor_odd, mul_one]
  · have hpos : 1 ≤ (f.dim - 1) / 2 := by
      by_contra hlt
      rcases octane_small hf ht (by omega) with h | h | h | h | h <;> rw [h] at h345 <;>
        revert h345 <;> decide
    rw [diagFactor_even hpos]
    simp only [Sign.toInt]
    push_cast
    ring
  · rcases Nat.eq_zero_or_pos ((f.dim - 1) / 2) with h0 | hpos
    · rw [h0]
      simp [Species.diagFactor, lowerProd]
      norm_num
    · rw [diagFactor_even hpos]
      simp only [Sign.toInt]
      push_cast
      ring

/-! ### The value of $\rho$ -/

/-- $P(f) = \frac12(1 + \varepsilon 2^{-t})$ for a type II constituent of dimension $2t$ and sign $\varepsilon$ (the
proportion of zeros of its quadratic form over $\mathbb F_2$). -/
def pII (f : TwoFactor) : ℚ := (1 + f.sign.toInt * ((2 : ℚ) ^ (f.dim / 2))⁻¹) / 2

/-- **The value of $\rho$** read from the 2-adic symbol $\sigma$ (constituents $f_1, f_2, f_4$ at $k = 0, 1, 2$):
$1$ for $f_1, f_2$ of type II; $P(f_1)$ for $f_1$ of type II and $f_2$ of type I; for $f_1$ of type I and $f_2$ of type
II, $\frac12$ if $f_4$ has type I and $P(f_2)$ otherwise; for $f_1$, $f_2$ of type I,
$\frac18 r(f_1)\,r'(f_2)$ with $r'(f_2) = 1$ if $f_4$ has type I and $r(f_2)$ otherwise. -/
def rhoValue (σ : TwoSymbol) : ℚ :=
  if (σ 0).type = .II then (if (σ 1).type = .II then 1 else pII (σ 0))
  else if (σ 1).type = .II then (if (σ 2).type = .I then 1 / 2 else pII (σ 1))
  else rI (σ 0) * (if (σ 2).type = .I then 1 else rI (σ 1)) / 8

/-- The symbol of the unimodular constituent alone: $f_1$ at $k = 0$, zero-dimensional constituents elsewhere. -/
def lowT (σ : TwoSymbol) : TwoSymbol := fun k => if k = 0 then σ 0 else TwoFactor.trivial

theorem blockSymbol_low (D : List DyBlock) : blockSymbol (low D) = lowT (blockSymbol D) := by
  funext k
  by_cases hk : k = 0
  · subst hk; simp [lowT, blockSymbol_low_zero]
  · simp [lowT, hk, blockSymbol_low_pos D hk]

/-- The rational part of `stepFactor`. -/
def qPart (σ : TwoSymbol) : ℚ :=
  halfFactor σ * mFac σ 0 * mFac σ 1 / (halfFactor (shiftT σ) * mFac (shiftT σ) 0)

theorem mBound_pos (f : TwoFactor) : 0 < mBound f := by
  rw [mBound_eq]; have := lowerProd_pos (tq f); positivity

theorem trivial_type : TwoFactor.trivial.type = .II := rfl

theorem rI_ne_zero {f : TwoFactor} (hf : f.Exists) (ht : f.type = .I) : rI f ≠ 0 := fun h => by
  have := mFree_I hf ht
  rw [h, mul_zero] at this
  exact (diagFactor_pos _).ne' this

theorem one_add_ne_zero_II {f : TwoFactor} (hf : f.Exists) (ht : f.type = .II) :
    (1 + f.sign.toInt * ((2 : ℚ) ^ (f.dim / 2))⁻¹) ≠ 0 := fun h => by
  have := mFree_II hf ht
  rw [h, mul_zero] at this
  exact (diagFactor_pos _).ne' this

theorem qPart_lowT (σ : TwoSymbol) (h0 : (σ 0).Exists) (h1 : (σ 1).Exists) :
    qPart (lowT σ) = rhoValue σ * qPart σ * (if (σ 0).type = .I ∧ (σ 1).type = .I then 2 else 1) := by
  have hl0 : lowT σ 0 = σ 0 := rfl
  have hl : ∀ k, lowT σ (k + 1) = TwoFactor.trivial := fun k => rfl
  have hsh : ∀ k, shiftT (lowT σ) k = TwoFactor.trivial := fun k => rfl
  have hm0 : mFac (lowT σ) 0 = mFree (σ 0) := by
    rw [mFac_eq, if_neg]; · rfl
    simp [IsBound, hl, trivial_type]
  have hm1 : mFac (lowT σ) 1 = if (σ 0).type = .I then 1 / 2 else 1 := by
    unfold mFac
    rw [hl 0]
    split_ifs with h
    · rw [twoSpecies_trivial_bound (by simp [IsBound, hl0, h])]; simp [Species.diagFactor, Species.odd, lowerProd]
    · rw [twoSpecies_trivial_free (by simp [IsBound, hl0, h, hl, trivial_type])]
      simp [Species.diagFactor, Species.plus]
  have hh : halfFactor (lowT σ) = halfFactor σ := rfl
  have hhs : halfFactor (shiftT (lowT σ)) = 1 := by simp [halfFactor, hsh, trivial_type]
  have hms : mFac (shiftT (lowT σ)) 0 = 1 := by
    unfold mFac; rw [hsh 0, twoSpecies_trivial_free (by simp [IsBound, hsh, trivial_type])]
    simp [Species.diagFactor, Species.plus]
  have hσ0 : mFac σ 0 = if (σ 1).type = .I then mBound (σ 0) else mFree (σ 0) := by
    rw [mFac_eq]; simp [IsBound]
  have hσ1 : mFac σ 1 = if (σ 0).type = .I ∨ (σ 2).type = .I then mBound (σ 1) else mFree (σ 1) := by
    rw [mFac_eq]; simp [IsBound]
  have hσs : mFac (shiftT σ) 0 = if (σ 2).type = .I then mBound (σ 1) else mFree (σ 1) := by
    rw [mFac_eq]; simp [IsBound, shiftT]
  have hhσ : halfFactor (shiftT σ) = if (σ 1).type = .I then 1 / 2 else 1 := by simp [halfFactor, shiftT]
  have hb0 := mBound_pos (σ 0)
  have hb1 := mBound_pos (σ 1)
  have hf0 : 0 < mFree (σ 0) := diagFactor_pos _
  have hf1 : 0 < mFree (σ 1) := diagFactor_pos _
  unfold qPart
  rw [hm0, hm1, hh, hhs, hms, hσ0, hσ1, hσs, hhσ]
  unfold rhoValue halfFactor
  cases ht0 : (σ 0).type <;> cases ht1 : (σ 1).type <;> cases ht2 : (σ 2).type <;>
    simp only [ht0, ht1, ht2, ite_true, ite_false, true_or, or_true, false_or, or_false, and_true, and_false,
      true_and, false_and, show ¬ (ScaledType.I = ScaledType.II) by decide,
      show ¬ (ScaledType.II = ScaledType.I) by decide, not_false_eq_true]
  all_goals first
    | (field_simp; (try ring); done)
    | (rw [mFree_II h0 ht0]; unfold pII; field_simp; (try ring); done)
    | (have := one_add_ne_zero_II h1 ht1; rw [mFree_II h1 ht1]; unfold pII
       generalize (1 + ((σ 1).sign.toInt : ℚ) * ((2 : ℚ) ^ ((σ 1).dim / 2))⁻¹) = X at this ⊢
       field_simp; (try ring); done)
    | (have := one_add_ne_zero_II h0 ht0; rw [mFree_II h0 ht0]; unfold pII
       generalize (1 + ((σ 0).sign.toInt : ℚ) * ((2 : ℚ) ^ ((σ 0).dim / 2))⁻¹) = X at this ⊢
       field_simp; (try ring); done)
    | (have := rI_ne_zero h1 ht1; rw [mFree_I h0 ht0, mFree_I h1 ht1]; field_simp; (try ring); done)
    | (rw [mFree_I h0 ht0]; field_simp; (try ring); done)

/-- **The ratio of the right-hand sides of (3)** for $U$ alone and for $U \perp 2B$: the step factor of $U$ alone is
$\rho$ times the step factor of $U \perp 2B$ (`rhoValue`). -/
theorem stepFactor_lowT (σ : TwoSymbol) (h0 : (σ 0).Exists) (h1 : (σ 1).Exists) :
    stepFactor (lowT σ) = (rhoValue σ : ℝ) * stepFactor σ := by
  have hq := qPart_lowT σ h0 h1
  unfold stepFactor
  change ((qPart (lowT σ) : ℚ) : ℝ) * _ = _ * (((qPart σ : ℚ) : ℝ) * _)
  rw [hq]
  have hl1 : (lowT σ 1).type = .II := rfl
  have hl0 : lowT σ 0 = σ 0 := rfl
  simp only [hl1, hl0, show ¬ (ScaledType.II = ScaledType.I) by decide, and_false, ite_false]
  push_cast
  split_ifs with h1 h2 h2 <;>
    (try (exfalso; rw [h1.1] at h2; exact absurd h2 (by decide))) <;> push_cast <;>
    (try simp only [zpow_sub₀ (two_ne_zero' ℝ), zpow_zero, zpow_one, sub_zero, zero_sub, zpow_neg]) <;>
    field_simp <;> ring

theorem pMassTwo_lowT_one (σ : TwoSymbol) : pMassTwo (lowT σ) 1 = stepFactor (lowT σ) := by
  rw [pMassTwo_succ]
  have hs : shiftT (lowT σ) = blockSymbol [] := by funext k; rfl
  rw [hs, pMassTwo_nil]
  simp

/-! ### The two named inputs and the step -/

/-- **Input: formula (3) for a single unimodular constituent of type I** (Conway–Sloane 1988, (3), p. 263, Table 1,
p. 264, §6, p. 266, for a 2-adic form with only the constituent $f_1$; the paper does not prove (3) at $p = 2$). For a
list $L$ of blocks $u x^2$, $2xy$, $2x^2 + 2xy + 2y^2$ of exponent $0$ with at least one block $u x^2$ (an odd
unimodular form $U$), the counting 2-mass is $m_2(U) = $ `pMassTwo σ 1`, i.e. $\alpha_2(U) = 4/M_2(f_1)$ with the
species of $f_1$ free (Table 1). The analogue for type II is proved (`pMassDensity_intMat_typeII_unimodular`).
Field:
- `base`: the identity for every such $L$. -/
@[kb "conwaysloane1988" "(3), p. 263; Table 1, p. 264; §6, p. 266 (p = 2, one odd unimodular constituent)"]
structure PMassUnimodularTwoTypeI : Prop where
  base : ∀ L : List DyBlock, (∀ b ∈ L, b.Valid) → (∀ b ∈ L, blockExp b = 0) → (blockSymbol L 0).type = .I →
    pMassDensity 2 (intMat L) = pMassTwo (blockSymbol L) 1

/-- **Input: the value of $\rho$ next to a type I constituent** (Conway–Sloane 1988, (3), p. 263, Table 1, p. 264,
§5–6, pp. 265–266, the bound/free rule, the factor of $f_{1/2}$ and the factor $2^{n(\mathrm{I,I})}$, translated into
a statement about one splitting step; the paper does not prove (3) at $p = 2$). For a decomposition $D$ into blocks of
nonnegative exponents whose constituent $f_1$ or $f_2$ has type I, with $U$ the blocks of exponent $0$ and $B$ the
others lowered by one, the proportion $\rho(U, B)$ of $W \in M_{b\times a}(\mathbb Z/4)$ with
$U + 2W^{\mathsf T}BW \sim U$ over $\mathbb Z_2$ (`rho`) is `rhoValue σ`, $\sigma$ the symbol of $D$. A statement
about unimodular forms over $\mathbb Z_2$ only; checked numerically (outside Lean) in 408 cases.
Field:
- `rho_eq`: the identity for every such $D$. -/
@[kb "conwaysloane1988" "(3), p. 263; Table 1, p. 264; §5–6, pp. 265–266 (p = 2, the proportion rho of one step)"]
structure RhoValueTwo : Prop where
  rho_eq : ∀ D : List DyBlock, (∀ b ∈ D, b.Valid) → (∀ b ∈ D, 0 ≤ blockExp b) →
    ((blockSymbol D 0).type = .I ∨ (blockSymbol D 1).type = .I) →
    rho (intMat (low D)) (intMat (high D)) = rhoValue (blockSymbol D)

theorem valid_high' {D : List DyBlock} (hv : ∀ b ∈ D, b.Valid) : ∀ b ∈ high D, b.Valid := valid_high hv

/-- **The one-step identity from the unimodular value and $\rho$**: if $m_2(U) = $ `stepFactor (lowT σ)` and
$\rho(U, B) = $ `rhoValue σ`, then `StepEq D`. -/
theorem stepEq_of_rho {D : List DyBlock} (hv : ∀ b ∈ D, b.Valid) (he : ∀ b ∈ D, 0 ≤ blockExp b)
    (hU : pMassDensity 2 (intMat (low D)) = stepFactor (lowT (blockSymbol D)))
    (hρ : rho (intMat (low D)) (intMat (high D)) = rhoValue (blockSymbol D)) : StepEq D := by
  have hex := blockSymbol_exists D hv
  have hρpos : (0 : ℝ) < rhoValue (blockSymbol D) := by rw [← hρ]; exact rho_pos
  unfold StepEq
  rw [pMassDensity_blk_two_rho (valid_low hv) exp_low (isSymm_intMat _) (det_intMat_ne _ (valid_high hv)), hU,
    stepFactor_lowT _ (hex 0) (hex 1), hρ]
  field_simp

theorem stepFactor_lowT_II (σ : TwoSymbol) (h : (σ 0).type = .II) :
    stepFactor (lowT σ) = (mFree (σ 0) : ℝ) * (2 : ℝ) ^ (-((σ 0).dim : ℤ)) := by
  have hl : ∀ k, lowT σ (k + 1) = TwoFactor.trivial := fun k => rfl
  have hsh : ∀ k, shiftT (lowT σ) k = TwoFactor.trivial := fun k => rfl
  have hm0 : mFac (lowT σ) 0 = mFree (σ 0) := by
    rw [mFac_eq, if_neg]; · rfl
    simp [IsBound, hl, trivial_type]
  have hm1 : mFac (lowT σ) 1 = 1 := by
    unfold mFac
    rw [hl 0, twoSpecies_trivial_free (by simp [IsBound, lowT, h, hl, trivial_type])]
    simp [Species.diagFactor, Species.plus]
  have hms : mFac (shiftT (lowT σ)) 0 = 1 := by
    unfold mFac; rw [hsh 0, twoSpecies_trivial_free (by simp [IsBound, hsh, trivial_type])]
    simp [Species.diagFactor, Species.plus]
  unfold stepFactor
  rw [hm0, hm1, hms]
  have hl0 : lowT σ 0 = σ 0 := rfl
  simp [halfFactor, hl0, h, hsh, trivial_type, hl]

/-- **The unimodular value** $m_2(U) = $ `stepFactor (lowT σ)`: from `PMassUnimodularTwoTypeI` when $f_1$ has type I,
proved (`pMassDensity_intMat_typeII_unimodular`) when $f_1$ has type II. -/
theorem pMassDensity_low (I : PMassUnimodularTwoTypeI) {D : List DyBlock} (hv : ∀ b ∈ D, b.Valid) :
    pMassDensity 2 (intMat (low D)) = stepFactor (lowT (blockSymbol D)) := by
  by_cases h : (blockSymbol D 0).type = .I
  · rw [I.base (low D) (valid_low hv) exp_low (by rw [blockSymbol_low_zero]; exact h), blockSymbol_low,
      pMassTwo_lowT_one]
  · have h2 : (blockSymbol D 0).type = .II := by cases h' : (blockSymbol D 0).type <;> simp_all
    rw [typeIIBase (low D) (valid_low hv) exp_low (not_sq_of_typeII h2), stepFactor_lowT_II _ h2, dyDim_low,
      blockSymbol_low]
    congr 2
    rw [mFac_eq, if_neg]; · rfl
    simp [IsBound, lowT, TwoFactor.trivial]

/-- **The former input from the two unimodular inputs**: `PMassUnimodularTwoTypeI` and `RhoValueTwo` imply
`PMassStepTwoTypeI` (the one-step identity of (3) at $p = 2$ next to a type I constituent). -/
@[kb "conwaysloane1988" "(3), p. 263; Table 1, p. 264; §6, p. 266 (one step at p = 2 next to type I)"]
theorem pMassStepTwoTypeI_of_inputs (I : PMassUnimodularTwoTypeI) (R : RhoValueTwo) : PMassStepTwoTypeI :=
  ⟨fun D hv he h => stepEq_of_rho hv he (pMassDensity_low I hv) (R.rho_eq D hv he h)⟩

/-- **Formula (3) at $p = 2$ from the two unimodular inputs** (Conway–Sloane 1988, (3), p. 263, Tables 1–2, §6). -/
@[kb "conwaysloane1988" "(3), p. 263 (p = 2); Tables 1–2, p. 264; §6, p. 266"]
theorem pMassFormulaTwo_of_inputs (I : PMassUnimodularTwoTypeI) (R : RhoValueTwo) : PMassFormulaTwo :=
  pMassFormulaTwo_of_stepTypeI (pMassStepTwoTypeI_of_inputs I R)

end QuadFormsKB.ConwaySloane.Mass.Two

namespace QuadFormsKB.ConwaySloane.Mass

open Two

/-- **The mass formula from the genus symbols, conditional only on the two unimodular inputs at $p = 2$**
(Conway–Sloane 1988, (2), (3), §7, §9): for a positive definite symmetric integral Gram matrix $A$ of dimension
$n \ge 3$, $m(f) = \mathrm{std}(f)\prod_{p \mid 2d} m_p(\sigma_p)/\mathrm{std}_p(f)$, assuming
`PMassUnimodularTwoTypeI` and `RhoValueTwo` (both about unimodular forms over $\mathbb Z_2$). -/
@[kb "conwaysloane1988" "(2), (3), p. 263; §7, p. 266; §9, p. 272"]
theorem mass_eq_stdMass_mul_symbols_of_inputs (I : PMassUnimodularTwoTypeI) (R : RhoValueTwo) {n : ℕ}
    (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) (hQ : IntQF.PosDef (LocalDensity.ofMatrixZ A))
    (τ : TwoSymbol) (N₂ : ℕ) (hτ : IsTwoSymbolOf (A.map (Int.cast : ℤ → ℚ_[2])) τ) (hτN : τ.SupportedBelow N₂)
    (σ : ℕ → OddSymbol) (N : ℕ → ℕ)
    (hodd : ∀ p : ℕ, (hp : p.Prime) → p ≠ 2 → (p : ℤ) ∣ A.det →
      haveI : Fact p.Prime := ⟨hp⟩
      IsOddSymbolOf p (A.map (Int.cast : ℤ → ℚ_[p])) (σ p) ∧ ∀ k, N p ≤ k → σ p k = OddFactor.trivial) :
    Siegel.mass (LocalDensity.ofMatrixZ A) = stdMass n A.det *
      ∏ p ∈ (2 * A.det).natAbs.primeFactors,
        ((if p = 2 then pMassTwo τ N₂ else pMassOdd p (σ p) (N p)) / (stdP p n A.det : ℝ)) :=
  mass_eq_stdMass_mul_symbols_stepTypeI (pMassStepTwoTypeI_of_inputs I R) hn hA hQ τ N₂ hτ hτN σ N hodd

/-- **§9 (i)** (Conway–Sloane 1988, pp. 269–272): $m(\mathrm{diag}(7,1,1)) = \frac3{16}$, conditional only on the two
unimodular inputs at $p = 2$. -/
@[kb "conwaysloane1988" "§9 (i), pp. 269–272"]
theorem example_i_mass_of_inputs (I : PMassUnimodularTwoTypeI) (R : RhoValueTwo) :
    Siegel.mass (LocalDensity.ofMatrixZ ex1Gram) = 3 / 16 :=
  example_i_mass_stepTypeI (pMassStepTwoTypeI_of_inputs I R)

end QuadFormsKB.ConwaySloane.Mass
