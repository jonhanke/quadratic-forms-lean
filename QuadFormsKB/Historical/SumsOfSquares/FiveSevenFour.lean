/-
# Five and seven squares for $n = 4m$, $m$ odd squarefree (Eisenstein, Smith; Dickson's tables (103)-(104))

**Library** `QuadFormsKB.Historical.SumsOfSquares` (historical library, not imported by `QuadFormsKB`).  Target
(Dickson, *Studies in the Theory of Numbers* (1930), ch. XIII, (101), tables (103)-(104)), the classes $4 \mid n$ left open in `OddSquares.lean`. A number
$n \equiv 4 \pmod 8$ without odd square factor is $n = 4m$ with $m$ odd and squarefree, and then
$$r_s(n) = \frac{c_s(n)}{\pi^{(s-1)/2}}\,n^{(s-2)/2}\sum_{q\ \mathrm{odd}}
   \Bigl(\frac{(-1)^{(s-1)/2}n}{q}\Bigr)q^{-(s-1)/2},$$
with $c_5(n) = 100, 90, 94$ for $n \equiv 12 \pmod{16}$, $n \equiv 4, 20 \pmod{32}$, and
$c_7(n) = 574, 1155/2, 1157/2$ for $n \equiv 4 \pmod{16}$, $n \equiv 12, 28 \pmod{32}$
(`five_squares_four_mul`, `seven_squares_four_mul`). The classes $8 \mid n$ are not listed by Dickson.

The constants were checked numerically against brute-force counts for $m \le 21$.

**Route.** As for `five_squares_squarefree`: Siegel's formula (`repNum_sumSq_eq_siegel`); at odd primes the densities
of $4m$ equal those of $m$ (unit factor $4$); at $p = 2$ the recursion
$\beta_2(4T) = \beta_2(T)/2^{s-2} + \beta^{\ne 0}_2(4T)$ (`localDensityOf_nonZero_eq`) with the level-3 count
(`localDensityOf_nonZero_sumSq_two`), as in `SixSquaresAll.lean`.

**Index convention.** The variables $x_1, \dots, x_s$ of the sources are `x 0, …, x (s-1)` here (`Fin s`).
-/
import QuadFormsKB.Historical.SumsOfSquares.OddSquares

namespace QuadFormsKB.Historical.SumsOfSquares

open QuadFormsKB.Siegel QuadFormsKB.LocalDensity

/-- Dickson's $c_5(4m)$ for odd $m$ (table (103)): $100$ if $m \equiv 3 \pmod 4$ ($n \equiv 12 \bmod 16$), $90$ if
$m \equiv 1 \pmod 8$ ($n \equiv 4 \bmod 32$), $94$ if $m \equiv 5 \pmod 8$ ($n \equiv 20 \bmod 32$). -/
def c5Four (m : ℕ) : ℝ := if m % 4 = 3 then 100 else if m % 8 = 1 then 90 else 94

/-- Dickson's $c_7(4m)$ for odd $m$ (table (104)): $574$ if $m \equiv 1 \pmod 4$ ($n \equiv 4 \bmod 16$), $1155/2$
if $m \equiv 3 \pmod 8$ ($n \equiv 12 \bmod 32$), $1157/2$ if $m \equiv 7 \pmod 8$ ($n \equiv 28 \bmod 32$). -/
noncomputable def c7Four (m : ℕ) : ℝ := if m % 4 = 1 then 574 else if m % 8 = 3 then 1155 / 2 else 1157 / 2

/-! ### Odd-prime densities and the Euler product, hypothesis only at odd primes -/

theorem localDensity_sumSq_odd_oddsqfree (k : ℕ) (hk : 1 ≤ k) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {M : ℤ}
    (hM : ¬ (p : ℤ) ^ 2 ∣ M) :
    localDensity (sumSq (2 * k + 1)) p M =
      (1 - 1 / (p : ℝ) ^ (2 * k)) / (1 - (jacobiSym ((-1) ^ k * M) p : ℝ) / (p : ℝ) ^ k) := by
  have hpp : p.Prime := Fact.out
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpp
  have hodd : Odd (2 * k + 1) := odd_two_mul_add_one k
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  have hpk : (1 : ℝ) < (p : ℝ) ^ k := one_lt_pow₀ hp1 (by omega)
  have hsq : (p : ℝ) ^ (2 * k) = ((p : ℝ) ^ k) ^ 2 := by rw [← pow_mul, mul_comm]
  have hidx : (2 * k + 1 - 1) / 2 = k := by omega
  by_cases hdvd : (p : ℤ) ∣ M
  · rw [sumSq_eq_diag, localDensity_diag_odd_ord_one (fun _ : Fin (2 * k + 1) => (1 : ℤ)) p hp
      (not_dvd_one_sumSq p) hodd M hdvd hM]
    have hz : jacobiSym ((-1) ^ k * M) p = 0 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_zero_iff,
        ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact Dvd.dvd.mul_left hdvd _
    rw [hz]
    simp
  · rw [sumSq_eq_diag, localDensity_diag_odd_unit (fun _ : Fin (2 * k + 1) => (1 : ℤ)) p hp
      (not_dvd_one_sumSq p) hodd M hdvd, hidx]
    simp only [Finset.prod_const_one, mul_one]
    have hne : (((-1) ^ k * M : ℤ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro h
      rcases hpz.dvd_or_dvd h with h | h
      · have := hpz.dvd_of_dvd_pow h
        rw [dvd_neg] at this
        exact not_dvd_one_sumSq p (0 : Fin 1) this
      · exact hdvd h
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    have ht0 : (p : ℝ) ^ k ≠ 0 := by positivity
    have htpos : 0 < 1 / (p : ℝ) ^ k := by positivity
    have htlt : 1 / (p : ℝ) ^ k < 1 := by rw [div_lt_one (by positivity)]; exact hpk
    rw [hsq]
    rcases legendreSym.eq_one_or_neg_one p hne with h | h <;> rw [h] <;> push_cast
    · have : (1 : ℝ) - 1 / (p : ℝ) ^ k ≠ 0 := by linarith
      rw [eq_div_iff this]
      field_simp
      ring
    · have : (1 : ℝ) - -1 / (p : ℝ) ^ k ≠ 0 := by
        rw [neg_div]; linarith
      rw [eq_div_iff this]
      field_simp
      ring

theorem eulerProduct_sumSq_odd_oddsqfree (k : ℕ) (hk : 2 ≤ k) {M : ℤ}
    (hM : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (p : ℤ) ^ 2 ∣ M) :
    eulerProduct (sumSq (2 * k + 1)) M =
      localDensity (sumSq (2 * k + 1)) 2 M / (1 - 1 / (2 : ℝ) ^ (2 * k)) *
        oddJacobiSeries ((-1) ^ k * M) k * (∑' m : ℕ, 1 / (m : ℝ) ^ (2 * k))⁻¹ := by
  have hk1 : 1 ≤ k := by omega
  have h2k : (1 : ℝ) - 1 / (2 : ℝ) ^ (2 * k) ≠ 0 := by
    have : (1 : ℝ) < 2 ^ (2 * k) := one_lt_pow₀ (by norm_num) (by omega)
    have : 1 / (2 : ℝ) ^ (2 * k) < 1 := by rw [div_lt_one (by positivity)]; exact this
    linarith
  set c : ℝ := localDensity (sumSq (2 * k + 1)) 2 M / (1 - 1 / (2 : ℝ) ^ (2 * k)) with hc_def
  have hc : HasProd (fun p : AWS.PrimeIdx => if (p : ℕ) = 2 then c else 1) c := by
    have h : HasProd (fun p : AWS.PrimeIdx => if (p : ℕ) = 2 then c else 1)
        (∏ p ∈ ({⟨2, Nat.prime_two⟩} : Finset AWS.PrimeIdx), if (p : ℕ) = 2 then c else 1) :=
      hasProd_prod_of_ne_finset_one fun p hp => by
        rw [if_neg]
        intro h2; exact hp (Finset.mem_singleton.mpr (Subtype.ext h2))
    rw [Finset.prod_singleton] at h
    simpa using h
  have hall : HasProd (fun p : AWS.PrimeIdx => (if (p : ℕ) = 2 then c else 1) *
        ((1 - 1 / ((p : ℕ) : ℝ) ^ (2 * k)) * (1 - oddJacobiTerm ((-1) ^ k * M) k p)⁻¹))
      (c * ((∑' m : ℕ, 1 / (m : ℝ) ^ (2 * k))⁻¹ * oddJacobiSeries ((-1) ^ k * M) k)) :=
    hc.mul ((hasProd_one_sub_inv_pow k hk1).mul (hasProd_oddJacobiTerm ((-1) ^ k * M) hk))
  have hpt : ∀ p : AWS.PrimeIdx, eulerFactor (sumSq (2 * k + 1)) M p =
      (if (p : ℕ) = 2 then c else 1) *
        ((1 - 1 / ((p : ℕ) : ℝ) ^ (2 * k)) * (1 - oddJacobiTerm ((-1) ^ k * M) k p)⁻¹) := by
    intro p
    by_cases h2 : (p : ℕ) = 2
    · have hf : oddJacobiTerm ((-1) ^ k * M) k p = 0 := by
        show (if Odd (p : ℕ) then _ else 0) = (0 : ℝ)
        rw [if_neg (by rw [h2]; decide)]
      rw [hf, if_pos h2]
      show localDensity (sumSq (2 * k + 1)) (p : ℕ) M = _
      rw [h2]
      simp only [sub_zero, inv_one, mul_one, Nat.cast_ofNat]
      rw [hc_def, div_mul_cancel₀ _ h2k]
    · haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
      rw [if_neg h2, one_mul]
      show localDensity (sumSq (2 * k + 1)) (p : ℕ) M = _
      rw [localDensity_sumSq_odd_oddsqfree k hk1 (p : ℕ) h2 (hM p p.2 h2)]
      have : oddJacobiTerm ((-1) ^ k * M) k p =
          (jacobiSym ((-1) ^ k * M) p : ℝ) / ((p : ℕ) : ℝ) ^ k := by
        show (if Odd (p : ℕ) then _ else 0) = _
        rw [if_pos (p.2.odd_of_ne_two h2)]
      rw [this, div_eq_mul_inv]
  have hfun : eulerFactor (sumSq (2 * k + 1)) M = fun p : AWS.PrimeIdx =>
      (if (p : ℕ) = 2 then c else 1) *
        ((1 - 1 / ((p : ℕ) : ℝ) ^ (2 * k)) * (1 - oddJacobiTerm ((-1) ^ k * M) k p)⁻¹) :=
    funext hpt
  have hE : eulerProduct (sumSq (2 * k + 1)) M =
      c * ((∑' m : ℕ, 1 / (m : ℝ) ^ (2 * k))⁻¹ * oddJacobiSeries ((-1) ^ k * M) k) := by
    unfold eulerProduct
    rw [hfun]
    exact hall.tprod_eq
  rw [hE]
  ring

theorem not_sq_dvd_four_mul {m : ℕ} (hsf : Squarefree m) (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
    ¬ (p : ℤ) ^ 2 ∣ ((4 * m : ℕ) : ℤ) := by
  intro h
  have h' : p ^ 2 ∣ 4 * m := by exact_mod_cast h
  have hc : Nat.Coprime (p ^ 2) (2 ^ 2) :=
    Nat.Coprime.pow 2 2 ((Nat.coprime_primes hp Nat.prime_two).mpr h2)
  have h'' : p ^ 2 ∣ m := hc.dvd_of_dvd_mul_left (by simpa using h')
  have := hsf p (by rw [← sq]; exact h'')
  exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)

theorem count_four_odd (T : ℤ) (hT : Odd T) : (((4 * T : ℤ)) : ZMod 8) = 4 := by
  obtain ⟨k, rfl⟩ := hT
  rw [show ((4 : ZMod 8)) = ((4 : ℤ) : ZMod 8) by norm_cast, ZMod.intCast_eq_intCast_iff]
  unfold Int.ModEq
  omega

theorem card_sumSq_five_mod_two : ∀ c : ZMod (2 ^ 1),
    Fintype.card {x : Fin 5 → ZMod (2 ^ 1) // ∑ i, x i ^ 2 = c} = 16 := by
  decide

theorem card_sumSq_seven_mod_two : ∀ c : ZMod (2 ^ 1),
    Fintype.card {x : Fin 7 → ZMod (2 ^ 1) // ∑ i, x i ^ 2 = c} = 64 := by
  decide

theorem sqTable8_five_four : sqTable8 5 4 = 3072 := by decide
theorem sqTable8_seven_four : sqTable8 7 4 = 294912 := by decide

theorem repCountOf_nonZero_five_four (T : ℤ) (hT : Odd T) :
    repCountOf (sumSq 5) 2 3 (4 * T) (fun x => ¬ IsZeroType 2 3 x) = 2560 := by
  have hsplit := repCount_eq_zero_add_nonZero (sumSq 5) 2 3 (4 * T)
  have hz := repCountZero_eq (sumSq 5) 2 (4 * T) 3 (by norm_num)
  have hd : ((2 : ℕ) : ℤ) ^ 2 ∣ 4 * T := ⟨T, by norm_num⟩
  rw [if_pos hd] at hz
  have h1 : repCount (sumSq 5) 2 1 (4 * T / ((2 : ℕ) : ℤ) ^ 2) = 16 := by
    unfold repCount
    rw [Nat.card_eq_fintype_card]
    rw [← card_sumSq_five_mod_two ((4 * T / ((2 : ℕ) : ℤ) ^ 2 : ℤ) : ZMod (2 ^ 1))]
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [evalIn_sumSq]
  have h2 : repCount (sumSq 5) 2 3 (4 * T) = 3072 := by
    unfold repCount
    rw [Nat.card_eq_fintype_card]
    have := sqCount8_eq 5 (by norm_num) (((4 * T : ℤ)) : ZMod 8)
    have h3 : sqTable8 5 (((4 * T : ℤ)) : ZMod 8) = 3072 := by
      rw [count_four_odd T hT, sqTable8_five_four]
    rw [← h3, ← this]
    unfold sqCount8
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun x => by rw [evalIn_sumSq])
  rw [hz, h1, h2] at hsplit
  norm_num at hsplit
  omega

theorem repCountOf_nonZero_seven_four (T : ℤ) (hT : Odd T) :
    repCountOf (sumSq 7) 2 3 (4 * T) (fun x => ¬ IsZeroType 2 3 x) = 286720 := by
  have hsplit := repCount_eq_zero_add_nonZero (sumSq 7) 2 3 (4 * T)
  have hz := repCountZero_eq (sumSq 7) 2 (4 * T) 3 (by norm_num)
  have hd : ((2 : ℕ) : ℤ) ^ 2 ∣ 4 * T := ⟨T, by norm_num⟩
  rw [if_pos hd] at hz
  have h1 : repCount (sumSq 7) 2 1 (4 * T / ((2 : ℕ) : ℤ) ^ 2) = 64 := by
    unfold repCount
    rw [Nat.card_eq_fintype_card]
    rw [← card_sumSq_seven_mod_two ((4 * T / ((2 : ℕ) : ℤ) ^ 2 : ℤ) : ZMod (2 ^ 1))]
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [evalIn_sumSq]
  have h2 : repCount (sumSq 7) 2 3 (4 * T) = 294912 := by
    unfold repCount
    rw [Nat.card_eq_fintype_card]
    have := sqCount8_eq 7 (by norm_num) (((4 * T : ℤ)) : ZMod 8)
    have h3 : sqTable8 7 (((4 * T : ℤ)) : ZMod 8) = 294912 := by
      rw [count_four_odd T hT, sqTable8_seven_four]
    rw [← h3, ← this]
    unfold sqCount8
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun x => by rw [evalIn_sumSq])
  rw [hz, h1, h2] at hsplit
  norm_num at hsplit
  omega

/-- $\beta_2(4T) = \beta_2(T)/8 + 5/8$ for odd $T$ (five squares). -/
theorem localDensity_sumSq_five_two_rec (T : ℤ) (hT : Odd T) :
    localDensity (sumSq 5) 2 (4 * T) = localDensity (sumSq 5) 2 T / 8 + 5 / 8 := by
  have hT0 : T ≠ 0 := by rintro rfl; exact absurd hT (by decide)
  have hK := localDensityOf_nonZero_eq (sumSq 5) posDef_sumSq.nondegenerate 2 (by norm_num) T hT0
  rw [localDensityOf_nonZero_sumSq_two] at hK
  have e : (((2 : ℕ) : ℤ) ^ 2 * T) = 4 * T := by norm_num
  rw [e, repCountOf_nonZero_five_four T hT] at hK
  norm_num at hK
  linarith

/-- $\beta_2(4T) = \beta_2(T)/32 + 35/32$ for odd $T$ (seven squares). -/
theorem localDensity_sumSq_seven_two_rec (T : ℤ) (hT : Odd T) :
    localDensity (sumSq 7) 2 (4 * T) = localDensity (sumSq 7) 2 T / 32 + 35 / 32 := by
  have hT0 : T ≠ 0 := by rintro rfl; exact absurd hT (by decide)
  have hK := localDensityOf_nonZero_eq (sumSq 7) posDef_sumSq.nondegenerate 2 (by norm_num) T hT0
  rw [localDensityOf_nonZero_sumSq_two] at hK
  have e : (((2 : ℕ) : ℤ) ^ 2 * T) = 4 * T := by norm_num
  rw [e, repCountOf_nonZero_seven_four T hT] at hK
  norm_num at hK
  linarith

theorem five_squares_of_beta (n : ℕ) (c : ℝ) (hn : 1 ≤ n)
    (hM : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (p : ℤ) ^ 2 ∣ (n : ℤ))
    (hb : localDensity (sumSq 5) 2 (n : ℤ) = c / 128) :
    (Nat.card {x : Fin 5 → ℤ // ∑ i, x i ^ 2 = n} : ℝ) =
      c / Real.pi ^ 2 * (n : ℝ) ^ ((3 : ℝ) / 2) * oddJacobiSeries n 2 := by
  have h1 := repNum_sumSq_eq_siegel (n := 5) (by norm_num) (by norm_num) (m := (n : ℤ))
    (by exact_mod_cast hn)
  have hE : eulerProduct (sumSq 5) (n : ℤ) = localDensity (sumSq 5) 2 (n : ℤ) / (1 - 1 / (2 : ℝ) ^ (2 * 2)) *
      oddJacobiSeries ((-1) ^ 2 * (n : ℤ)) 2 * (∑' m : ℕ, 1 / (m : ℝ) ^ (2 * 2))⁻¹ :=
    eulerProduct_sumSq_odd_oddsqfree 2 (by norm_num) hM
  have hcard : (Nat.card {x : Fin 5 → ℤ // ∑ i, x i ^ 2 = n}) = repNum (sumSq 5) (n : ℤ) :=
    sqRep_eq_repNum 5 n
  rw [zeta_four_tsum, show ((-1 : ℤ) ^ 2 * (n : ℤ)) = n by ring] at hE
  rw [hcard, h1, hE, betaInf_sumSq_five]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [hb]
  push_cast
  field_simp
  norm_num
  ring

theorem seven_squares_of_beta (n : ℕ) (c : ℝ) (hn : 1 ≤ n)
    (hM : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (p : ℤ) ^ 2 ∣ (n : ℤ))
    (hb : localDensity (sumSq 7) 2 (n : ℤ) = c / 512) :
    (Nat.card {x : Fin 7 → ℤ // ∑ i, x i ^ 2 = n} : ℝ) =
      c / Real.pi ^ 3 * (n : ℝ) ^ ((5 : ℝ) / 2) * oddJacobiSeries (-(n : ℤ)) 3 := by
  have h1 := repNum_sumSq_eq_siegel (n := 7) (by norm_num) (by norm_num) (m := (n : ℤ))
    (by exact_mod_cast hn)
  have hE : eulerProduct (sumSq 7) (n : ℤ) = localDensity (sumSq 7) 2 (n : ℤ) / (1 - 1 / (2 : ℝ) ^ (2 * 3)) *
      oddJacobiSeries ((-1) ^ 3 * (n : ℤ)) 3 * (∑' m : ℕ, 1 / (m : ℝ) ^ (2 * 3))⁻¹ :=
    eulerProduct_sumSq_odd_oddsqfree 3 (by norm_num) hM
  have hcard : (Nat.card {x : Fin 7 → ℤ // ∑ i, x i ^ 2 = n}) = repNum (sumSq 7) (n : ℤ) :=
    sqRep_eq_repNum 7 n
  rw [zeta_six_tsum, show ((-1 : ℤ) ^ 3 * (n : ℤ)) = -(n : ℤ) by ring] at hE
  rw [hcard, h1, hE, betaInf_sumSq_seven]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [hb]
  push_cast
  field_simp
  norm_num
  ring

/-- **Five squares, $n = 4m$** (five-square part, classes $4 \mid n$; Dickson,
*Studies* (1930), ch. XIII, (101), table (103)): for odd squarefree $m$ and $n = 4m$,
$$r_5(n) = \frac{c_5(n)}{\pi^2}\,n^{3/2}\sum_{q\ \mathrm{odd}}\Bigl(\frac nq\Bigr)\frac1{q^2}.$$ -/
@[kb "dickson1930" "ch. XIII, (101), table (103)"]
theorem five_squares_four_mul (m : ℕ) (hm : Odd m) (hsf : Squarefree m) :
    (Nat.card {x : Fin 5 → ℤ // ∑ i, x i ^ 2 = 4 * m} : ℝ) =
      c5Four m / Real.pi ^ 2 * ((4 * m : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * oddJacobiSeries (4 * m : ℕ) 2 := by
  have hodd : Odd (m : ℤ) := by exact_mod_cast hm
  have hm4 : m % 4 ≠ 0 := by obtain ⟨k, rfl⟩ := hm; omega
  have hm1 : 1 ≤ m := by obtain ⟨k, rfl⟩ := hm; omega
  have hb := beta2_five m hm4
  have hrec := localDensity_sumSq_five_two_rec (m : ℤ) hodd
  refine five_squares_of_beta (4 * m) (c5Four m) (by omega) (not_sq_dvd_four_mul hsf) ?_
  have e : (((4 * m : ℕ) : ℤ)) = 4 * (m : ℤ) := by push_cast; ring
  rw [e, hrec]
  have hm2 := Nat.odd_iff.mp hm
  have hb' : localDensity (sumSq 5) 2 (m : ℤ) = c5 m / 128 := by rw [← hb]; ring
  rw [hb']
  unfold c5Four c5
  split_ifs <;> first | omega | norm_num

/-- **Seven squares, $n = 4m$** (seven-square part, classes $4 \mid n$; Dickson,
*Studies* (1930), ch. XIII, (101), table (104)): for odd squarefree $m$ and $n = 4m$,
$$r_7(n) = \frac{c_7(n)}{\pi^3}\,n^{5/2}\sum_{q\ \mathrm{odd}}\Bigl(\frac{-n}{q}\Bigr)\frac1{q^3}.$$ -/
@[kb "dickson1930" "ch. XIII, (101), table (104)"]
theorem seven_squares_four_mul (m : ℕ) (hm : Odd m) (hsf : Squarefree m) :
    (Nat.card {x : Fin 7 → ℤ // ∑ i, x i ^ 2 = 4 * m} : ℝ) =
      c7Four m / Real.pi ^ 3 * ((4 * m : ℕ) : ℝ) ^ ((5 : ℝ) / 2) * oddJacobiSeries (-((4 * m : ℕ) : ℤ)) 3 := by
  have hodd : Odd (m : ℤ) := by exact_mod_cast hm
  have hm4 : m % 4 ≠ 0 := by obtain ⟨k, rfl⟩ := hm; omega
  have hm1 : 1 ≤ m := by obtain ⟨k, rfl⟩ := hm; omega
  have hb := beta2_seven m hm4
  have hrec := localDensity_sumSq_seven_two_rec (m : ℤ) hodd
  refine seven_squares_of_beta (4 * m) (c7Four m) (by omega) (not_sq_dvd_four_mul hsf) ?_
  have e : (((4 * m : ℕ) : ℤ)) = 4 * (m : ℤ) := by push_cast; ring
  rw [e, hrec]
  have hm2 := Nat.odd_iff.mp hm
  have hb' : localDensity (sumSq 7) 2 (m : ℤ) = c7 m / 512 := by rw [← hb]; ring
  rw [hb']
  unfold c7Four c7
  split_ifs <;> first | omega | norm_num

end QuadFormsKB.Historical.SumsOfSquares
