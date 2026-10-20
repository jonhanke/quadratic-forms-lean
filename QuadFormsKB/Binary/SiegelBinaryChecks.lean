import QuadFormsKB.Binary.SiegelBinary
import QuadFormsKB.LocalDensity.BridgeDyadic

/-!
# Cross-checks of Siegel's formula for $n = 2$: $D = -4$ and $D = -20$

Concrete instances of `siegelFormula_binary`, with the constants evaluated:

* **$D = -4$**, $f = x^2 + y^2$ ($w = 4$, $t = 1$): $\beta_\infty = \pi$ (`betaInf_sumTwoSq`); for odd $m$,
  $\beta_2(m) = 1 + \chi_{-4}(m)$ (`localDensity_sumTwoSq_two_odd`), which at $m = 1$ agrees with the independent
  dyadic computation `LocalDensity.localDensity_sumTwoSq_two` ($\beta_2(1) = 2$); and the Siegel side gives
  $$r_{\mathcal G}(m) = \frac{4}{h(-4)}\sum_{d \mid m}\chi_{-4}(d)\ (m \equiv 1 \bmod 4), \qquad 0\ (m \equiv 3 \bmod 4)$$
  (`siegel_sumTwoSq`), i.e. Jacobi's $r_2(m) = 4\sum_{d \mid m}\chi_{-4}(d)$ once $h(-4) = 1$ (not formalized here).
  E.g. $r_{\mathcal G}(5) = 8/h$, $r_{\mathcal G}(3) = 0$.
* **$D = -20$** ($h = 2$, two genera, $w = 2$, $t = 2$): $f = x^2 + 5y^2$, $g = 2x^2 + 2xy + 3y^2$, $m = 3$:
  $\beta_5(f, 3) = 0$, $\beta_5(g, 3) = \beta_2(g, 3) = 2$, $\beta_3(3) = \frac43$, and
  $r_{\mathrm{Gen}(f)}(3) = 0$, $r_{\mathrm{Gen}(g)}(3) = 8/h(-20)$ (`siegel_neg_twenty_three`); with $h(-20) = 2$ this is
  $r_g(3) = 4$ ($g(0, \pm1) = g(1, -1) = g(-1, 1) = 3$).
-/

open QuadFormsKB.LocalDensity QuadFormsKB.Siegel

namespace QuadFormsKB.Binary

open BinQF

/-! ### $D = -4$ -/

instance isQuadDisc_neg_four : IsQuadDisc (-4) where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    right
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  ne_one := by norm_num

instance : Fact ((-4 : ℤ) < 0) := ⟨by norm_num⟩

/-- $x^2 + y^2$. -/
def sumTwoSq : BinQF := BinQF.mk 1 0 1

theorem sumTwoSq_primitive : Primitive sumTwoSq := by simp [sumTwoSq, Primitive]

theorem sumTwoSq_disc : sumTwoSq.disc = -4 := by simp [sumTwoSq, BinQF.disc]

/-- $x^2 + y^2$ as an element of `PosForms (-4)`. -/
def sumTwoSqPos : PosForms (-4) :=
  ⟨sumTwoSq, sumTwoSq_primitive, sumTwoSq_disc, by simp [sumTwoSq, PosDef', BinQF.disc]⟩

/-- $x^2 + y^2$ is the repo's diagonal form $\langle 1, 1\rangle$. -/
theorem sumTwoSq_eq_diag : sumTwoSq = QuadForm.diag ![(1 : ℤ), 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sumTwoSq, BinQF.mk, QuadForm.ofUpper, QuadForm.diag]

/-- **$\beta_\infty = \pi$ for $x^2 + y^2$** (the area of $\{x^2 + y^2 \le t\}$ is $\pi t$). -/
theorem betaInf_sumTwoSq (m : ℝ) : betaInf sumTwoSq m = Real.pi := by
  rw [betaInf_binary sumTwoSq (by simp [sumTwoSq, BinQF.disc]) m]
  have : -((sumTwoSq.disc : ℤ) : ℝ) = 2 ^ 2 := by simp [sumTwoSq, BinQF.disc]; norm_num
  rw [this, Real.sqrt_sq (by norm_num)]
  ring

/-- **$\beta_2(m) = 1 + \chi_{-4}(m)$ for $x^2 + y^2$ and odd $m$** (`localDensity_ram_unit` with $\chi_2(f) = 1$,
$\psi_2 = \chi_{-4}$). -/
theorem localDensity_sumTwoSq_two_odd (m : ℤ) (hm : ¬ (2 : ℤ) ∣ m) :
    localDensity sumTwoSq 2 m = 1 + (ZMod.χ₄ (m : ZMod 4) : ℝ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [localDensity_ram_unit sumTwoSq_primitive sumTwoSq_disc 2 (by norm_num) m (by exact_mod_cast hm)]
  have h1 : formChar sumTwoSq 2 = 1 := by
    simp [formChar, charCoeff, genusChar, sumTwoSq, BinQF.disc]
  have h2 : genusChar (-4) 2 m = ZMod.χ₄ (m : ZMod 4) := by simp [genusChar]
  rw [h1, h2]
  simp

/-- **Agreement with the independent dyadic computation:** $\beta_2(x^2 + y^2, 1) = 2$ from the binary formula,
as in `LocalDensity.localDensity_sumTwoSq_two` (computed via the DVR layer at level $8$). -/
@[kb "hanke2004" "Remark 3.4.1(a), p. 361 (p = 2 check)"]
theorem localDensity_sumTwoSq_two_one :
    localDensity sumTwoSq 2 1 = 2 ∧ localDensity (QuadForm.diag ![(1 : ℤ), 1]) 2 1 = 2 := by
  refine ⟨?_, LocalDensity.localDensity_sumTwoSq_two.1⟩
  rw [localDensity_sumTwoSq_two_odd 1 (by norm_num)]
  simp; norm_num

theorem primeFactors_four : Nat.primeFactors 4 = {2} := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]

/-- **Siegel's formula for $x^2 + y^2$** ($D = -4$, $w = 4$, $t = 1$), $m$ odd: the Siegel side
$\frac12\beta_\infty(m)P_f(m)$, and hence the genus average, is $\frac{4}{h}\sum_{d\mid m}\chi_{-4}(d)$ for $m \equiv 1 \pmod 4$
and $0$ for $m \equiv 3 \pmod 4$ (Jacobi's two-squares formula, given $h(-4) = 1$). -/
@[kb "grosswald1985" "Ch. 2, Thm. 3 (Jacobi, r₂) [unverified locator]"]
theorem siegel_sumTwoSq {m : ℕ} (hm : ¬ 2 ∣ m) :
    genusRepAvg sumTwoSq m = (1 / 2 : ℝ) * aEWith sumTwoSq m (binaryEulerValue sumTwoSq (-4) m) ∧
    (1 / 2 : ℝ) * aEWith sumTwoSq m (binaryEulerValue sumTwoSq (-4) m) =
      4 / NumberField.classNumber (QField (-4)) *
        (if m % 4 = 1 then ∑ d ∈ m.divisors, kronR (-4) d else 0) := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hcop : Nat.Coprime m (-4 : ℤ).natAbs := by
    rw [show (-4 : ℤ).natAbs = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm)))
  refine ⟨siegelFormula_binary_coprime sumTwoSqPos hm0 hcop, ?_⟩
  rw [siegelSide_explicit (by norm_num) sumTwoSq_primitive sumTwoSq_disc hm0 hcop]
  rw [show (-4 : ℤ).natAbs = 4 by norm_num, primeFactors_four, Finset.prod_singleton,
    torsionOrder_of_neg (by norm_num : (-4 : ℤ) < 0)]
  have h1 : formChar sumTwoSq 2 = 1 := by
    simp [formChar, charCoeff, genusChar, sumTwoSq, BinQF.disc]
  have h2 : genusChar (-4) 2 (m : ℤ) = ZMod.χ₄ ((m : ℤ) : ZMod 4) := by simp [genusChar]
  rw [h1, h2]
  have hodd : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rw [ZMod.χ₄_int_eq_if_mod_four]
  have hh : (NumberField.classNumber (QField (-4)) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ClassGroup (NumberField.RingOfIntegers (QField (-4))))).ne'
  rcases hodd with h | h
  · have h' : (m : ℤ) % 4 = 1 := by omega
    have h2' : ¬ (m : ℤ) % 2 = 0 := by omega
    simp only [h', h2', h, ite_false, ite_true]
    norm_num
    field_simp
  · have h' : (m : ℤ) % 4 = 3 := by omega
    have h2' : ¬ (m : ℤ) % 2 = 0 := by omega
    simp only [h', h2', h]
    norm_num

/-! ### $D = -20$ -/

instance isQuadDisc_neg_twenty : IsQuadDisc (-20) where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    right
    refine ⟨by norm_num, ?_, by norm_num⟩
    norm_num
    exact Int.squarefree_natAbs.mp (by norm_num; exact Nat.prime_five.squarefree)
  ne_one := by norm_num

instance : Fact ((-20 : ℤ) < 0) := ⟨by norm_num⟩

/-- $x^2 + 5y^2$ (principal genus of discriminant $-20$). -/
def f20 : BinQF := BinQF.mk 1 0 5

/-- $2x^2 + 2xy + 3y^2$ (the other genus of discriminant $-20$). -/
def g20 : BinQF := BinQF.mk 2 2 3

theorem f20_primitive : Primitive f20 := by simp [f20, Primitive]
theorem f20_disc : f20.disc = -20 := by simp [f20, BinQF.disc]
theorem g20_primitive : Primitive g20 := by simp [g20, Primitive]; decide
theorem g20_disc : g20.disc = -20 := by simp [g20, BinQF.disc]

/-- $x^2 + 5y^2$ in `PosForms (-20)`. -/
def f20Pos : PosForms (-20) := ⟨f20, f20_primitive, f20_disc, by simp [f20, PosDef', BinQF.disc]⟩

/-- $2x^2 + 2xy + 3y^2$ in `PosForms (-20)`. -/
def g20Pos : PosForms (-20) := ⟨g20, g20_primitive, g20_disc, by simp [g20, PosDef', BinQF.disc]⟩

theorem primeFactors_twenty : Nat.primeFactors 20 = {2, 5} := by
  rw [show (20 : ℕ) = 2 ^ 2 * 5 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Nat.prime_five.primeFactors]
  rfl

theorem coprime_three_twenty : Nat.Coprime 3 (-20 : ℤ).natAbs := by norm_num

/-- **The local data at $m = 3$, $D = -20$:** $\beta_5(f, 3) = 0$ ($\psi_5(3) = -1 \ne \chi_5(f) = 1$),
$\beta_5(g, 3) = \beta_2(g, 3) = 2$, and $\beta_3(3) = (1 - \frac13)(1 + 1) = \frac43$ ($\chi_{-20}(3) = 1$). -/
theorem localDensity_neg_twenty_three :
    localDensity f20 5 3 = 0 ∧ localDensity g20 5 3 = 2 ∧ localDensity g20 2 3 = 2 ∧
      localDensity f20 3 3 = 4 / 3 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [localDensity_ram_unit f20_primitive f20_disc 5 (by norm_num) 3 (by norm_num)]
    simp [formChar, charCoeff, genusChar, f20]
    norm_num
  · rw [localDensity_ram_unit g20_primitive g20_disc 5 (by norm_num) 3 (by norm_num)]
    simp [formChar, charCoeff, genusChar, g20]
    norm_num
  · rw [localDensity_ram_unit g20_primitive g20_disc 2 (by norm_num) 3 (by norm_num)]
    simp [formChar, charCoeff, genusChar, g20, BinQF.disc]
    norm_num
  · rw [localDensity_good_binary f20 f20_disc 3 (by norm_num) 3 (by norm_num),
      kronZ_odd_prime 3 (by norm_num)]
    have hv : (Int.natAbs 3).factorization 3 = 1 := by
      simp [Nat.Prime.factorization_self Nat.prime_three]
    rw [hv]
    simp [goodFactor, Finset.sum_range_succ]
    norm_num

/-- **Siegel's formula at $D = -20$, $m = 3$:** the Siegel side is $0$ for the principal genus ($x^2 + 5y^2$
does not represent $3$) and $8/h(-20)$ for the genus of $g = 2x^2 + 2xy + 3y^2$ (so $r_g(3) = 4$ once $h(-20) = 2$). -/
@[kb "cox2013" "§2 (x² + 5y² and 2x² + 2xy + 3y²) [unverified locator]"]
theorem siegel_neg_twenty_three :
    genusRepAvg f20 3 = (1 / 2 : ℝ) * aEWith f20 3 (binaryEulerValue f20 (-20) 3) ∧
    (1 / 2 : ℝ) * aEWith f20 3 (binaryEulerValue f20 (-20) 3) = 0 ∧
    genusRepAvg g20 3 = (1 / 2 : ℝ) * aEWith g20 3 (binaryEulerValue g20 (-20) 3) ∧
    (1 / 2 : ℝ) * aEWith g20 3 (binaryEulerValue g20 (-20) 3) = 8 / NumberField.classNumber (QField (-20)) := by
  have hdiv : Nat.divisors 3 = {1, 3} := by decide
  have hk3 : kronR (-20) 3 = 1 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    unfold kronR
    rw [show ((3 : ℕ) : ZMod (-20 : ℤ).natAbs) = ((3 : ℕ) : ZMod (-20 : ℤ).natAbs) from rfl,
      kronZ_odd_prime 3 (by norm_num)]
    norm_num
  have hS : ∑ d ∈ Nat.divisors 3, kronR (-20) d = 2 := by
    rw [hdiv, Finset.sum_pair (by norm_num), kronR_one, hk3]; norm_num
  have hw : NumberField.Units.torsionOrder (QField (-20)) = 2 := by
    rw [torsionOrder_of_neg (by norm_num : (-20 : ℤ) < 0)]; norm_num
  have hh : (NumberField.classNumber (QField (-20)) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ClassGroup (NumberField.RingOfIntegers (QField (-20))))).ne'
  refine ⟨siegelFormula_binary_coprime f20Pos (by norm_num) coprime_three_twenty, ?_,
    siegelFormula_binary_coprime g20Pos (by norm_num) coprime_three_twenty, ?_⟩
  · rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, siegelSide_explicit (by norm_num) f20_primitive f20_disc
      (by norm_num) coprime_three_twenty,
      show (-20 : ℤ).natAbs = 20 by norm_num, primeFactors_twenty, Finset.prod_pair (by norm_num)]
    simp [formChar, charCoeff, genusChar, f20]
  · rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, siegelSide_explicit (by norm_num) g20_primitive g20_disc
      (by norm_num) coprime_three_twenty,
      show (-20 : ℤ).natAbs = 20 by norm_num, primeFactors_twenty, Finset.prod_pair (by norm_num), hS, hw]
    simp [formChar, charCoeff, genusChar, g20, BinQF.disc]
    norm_num
    field_simp

end QuadFormsKB.Binary
