/-
# Five and seven squares for squarefree numbers (Eisenstein 1847/1850, Smith 1867/1882)

**Library** `QuadFormsKB.Historical.SumsOfSquares` (historical library, not imported by `QuadFormsKB`).  Targets
:

* (Dickson, *Studies in the Theory of Numbers* (1930), ch. XIII, (101), tables (103)–(104);
  ): for $s = 5, 7$ and $n$ without odd square factor,
  $$r_s(n) = \frac{c_s(n)}{\pi^{(s-1)/2}}\,n^{(s-2)/2}\sum_{m\ \mathrm{odd},\,(m,n)=1}
     \Bigl(\frac{(-1)^{(s-1)/2}n}{m}\Bigr)m^{-(s-1)/2},$$
  $c_5(n) = 80, 160, 112$ for $n \equiv 1;\ 2,3,6,7;\ 5 \pmod 8$, and $c_7(n) = 448, 560, 592$ for
  $n \equiv 1,2,5,6;\ 3;\ 7 \pmod 8$. **Proved here for squarefree $n$** (`five_squares_squarefree`,
  `seven_squares_squarefree`); the classes $4 \mid n$ of the tables ($n = 4m$, $m$ odd squarefree) are
  `five_squares_four_mul`, `seven_squares_four_mul` in `FiveSevenFour.lean`.
* (same source): Eisenstein's statement (1847/50) of these
  formulas for odd squarefree $n$: the case $n$ odd of the two theorems above.
* (Smith, *Collected Mathematical Papers* II, Paper XLIV, Art. 16, pp. 672–675): Smith's five-squares
  formula for the number of *primitive* representations (`SumsOfSquares.SmithFiveSquares`). **Proved here for squarefree
  $M$** (`smithFiveSquares_squarefree`), where every representation is primitive.

**Route.** $r_n(m) = \beta_\infty(m)\prod_p\beta_p(m)$ (`repNum_sumSq_eq_siegel`: Siegel's formula and one class in the
genus, both proved in this library). For squarefree $M$ and $n = 2k+1$, with $\chi(m) = \bigl(\frac{(-1)^kM}{m}\bigr)$
(Jacobi symbol): $\beta_p(M) = (1 - p^{-2k})/(1 - \chi(p)p^{-k})$ at every odd prime $p$ (Hanke's Table 2,
`localDensity_diag_odd_unit`, `localDensity_diag_odd_ord_one`), $\beta_2(M) = N_n(M \bmod 8)/8^{n-1}$
(`localDensity_sumSq_two`), so by the Euler products of $\zeta(2k)$ and of $\sum_{m\ \mathrm{odd}}\chi(m)m^{-k}$,
$$\prod_p\beta_p(M) = \frac{\beta_2(M)}{1 - 2^{-2k}}\cdot\frac{\sum_{m\ \mathrm{odd}}\chi(m)m^{-k}}{\zeta(2k)}.$$
With $\beta_\infty$, $\zeta(4) = \pi^4/90$ and $\zeta(6) = \pi^6/945$ this gives the constants $c_5 = 128\beta_2$ and
$c_7 = 512\beta_2$.

**Index convention.** The variables $x_1, \dots, x_s$ of the sources are `x 0, …, x (s-1)` here (`Fin s`).
-/
import QuadFormsKB.Historical.SumsOfSquares.Siegel
import QuadFormsKB.Historical.SumsOfSquares
import QuadFormsKB.Historical.SumsOfSquares.JacobiCounts

namespace QuadFormsKB.Historical.SumsOfSquares

open QuadFormsKB.Siegel QuadFormsKB.LocalDensity

/-! ### The Dirichlet series $\sum_{m\ \mathrm{odd}}\bigl(\frac Dm\bigr)m^{-k}$ -/

/-- $m \mapsto \bigl(\frac Dm\bigr)m^{-k}$ on odd $m$ and $0$ on even $m$: completely multiplicative. -/
noncomputable def oddJacobiTerm (D : ℤ) (k : ℕ) : ℕ →*₀ ℝ where
  toFun m := if Odd m then (jacobiSym D m : ℝ) / (m : ℝ) ^ k else 0
  map_zero' := by simp
  map_one' := by simp [jacobiSym.one_right]
  map_mul' := by
    intro m n
    by_cases hm : m = 0
    · subst hm; simp
    by_cases hn : n = 0
    · subst hn; simp
    haveI : NeZero m := ⟨hm⟩
    haveI : NeZero n := ⟨hn⟩
    by_cases hmo : Odd m <;> by_cases hno : Odd n <;>
      simp [Nat.odd_mul, hmo, hno, jacobiSym.mul_right, mul_pow, div_mul_div_comm]

/-- **The series** $L_{\mathrm{odd}}(D, k) = \sum_{m \ge 1\ \mathrm{odd}}\bigl(\frac Dm\bigr)m^{-k}$
(Jacobi symbol, Mathlib's `jacobiSym`; the terms with $\gcd(m, D) > 1$ vanish, so this is the sum over odd $m$ prime to
$D$ of Dickson's (101)). Absolutely convergent for $k \ge 2$. -/
noncomputable def oddJacobiSeries (D : ℤ) (k : ℕ) : ℝ :=
  ∑' m : ℕ, if Odd m then (jacobiSym D m : ℝ) / (m : ℝ) ^ k else 0

theorem smithSeries_eq (M : ℕ) : smithSeries M = oddJacobiSeries M 2 := rfl

theorem summable_oddJacobiTerm (D : ℤ) {k : ℕ} (hk : 2 ≤ k) : Summable (‖oddJacobiTerm D k ·‖) := by
  have hs : Summable fun n : ℕ => 1 / (n : ℝ) ^ k := Real.summable_one_div_nat_pow.mpr (by omega)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hs
  show ‖(if Odd n then (jacobiSym D n : ℝ) / (n : ℝ) ^ k else 0)‖ ≤ 1 / (n : ℝ) ^ k
  split_ifs with h
  · rw [norm_div, norm_pow, Real.norm_natCast]
    have : ‖(jacobiSym D n : ℝ)‖ ≤ 1 := by
      rcases jacobiSym.trichotomy D n with h | h | h <;> simp [h]
    exact div_le_div_of_nonneg_right this (by positivity)
  · simp

/-- **Euler product:** $\prod_p \bigl(1 - \chi(p)p^{-k}\bigr)^{-1} = L_{\mathrm{odd}}(D, k)$, $\chi(2) := 0$. -/
theorem hasProd_oddJacobiTerm (D : ℤ) {k : ℕ} (hk : 2 ≤ k) :
    HasProd (fun p : Nat.Primes => (1 - oddJacobiTerm D k p)⁻¹) (oddJacobiSeries D k) :=
  EulerProduct.eulerProduct_completely_multiplicative_hasProd (summable_oddJacobiTerm D hk)

/-- **Euler product of $\zeta(2k)$, real form:** $\prod_p(1 - p^{-2k}) = 1/\sum_{m \ge 1} m^{-2k}$. -/
theorem hasProd_one_sub_inv_pow (k : ℕ) (hk : 1 ≤ k) :
    HasProd (fun p : Nat.Primes => 1 - 1 / ((p : ℕ) : ℝ) ^ (2 * k))
      (∑' m : ℕ, 1 / (m : ℝ) ^ (2 * k))⁻¹ := by
  let f : ℕ →*₀ ℝ :=
    { toFun := fun m => 1 / (m : ℝ) ^ (2 * k)
      map_zero' := by simp; omega
      map_one' := by simp
      map_mul' := fun m n => by simp [mul_pow]; ring }
  have hsum : Summable fun m : ℕ => 1 / (m : ℝ) ^ (2 * k) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  have h := EulerProduct.eulerProduct_completely_multiplicative_hasProd (f := f)
    (by simpa [f] using hsum.norm)
  have hpos : (∑' m : ℕ, 1 / (m : ℝ) ^ (2 * k)) ≠ 0 := by
    refine (hsum.tsum_pos (fun m => by positivity) 1 (by simp)).ne'
  have h2 := (show HasProd (fun p : Nat.Primes => (1 - f p)⁻¹) (∑' m : ℕ, 1 / (m : ℝ) ^ (2 * k)) from h).inv₀ hpos
  simpa [f] using h2

/-! ### Local densities at odd primes, $M$ squarefree -/

/-- **$\beta_p(M)$ for $I_{2k+1}$, $p$ odd, $M$ squarefree:** $(1 - p^{-2k})/(1 - \chi(p)p^{-k})$ with
$\chi(p) = \bigl(\frac{(-1)^kM}{p}\bigr)$. (For $p \nmid M$ this is $1 + \chi(p)p^{-k}$; for $p \mid M$ it is $1 - p^{-2k}$.) -/
theorem localDensity_sumSq_odd_squarefree (k : ℕ) (hk : 1 ≤ k) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {M : ℤ}
    (hM : Squarefree M) :
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
  · have h2 : ¬ (p : ℤ) ^ 2 ∣ M := fun h => by
      have := hM (p : ℤ) (by rw [← sq]; exact h)
      exact hpz.not_isUnit this
    rw [sumSq_eq_diag, localDensity_diag_odd_ord_one (fun _ : Fin (2 * k + 1) => (1 : ℤ)) p hp
      (not_dvd_one_sumSq p) hodd M hdvd h2]
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

/-! ### The Euler product -/

/-- **The Euler product of $I_{2k+1}$ at squarefree $M$** ($k \ge 2$):
$$\prod_p\beta_p(M) = \frac{\beta_2(M)}{1 - 2^{-2k}}\cdot\frac{L_{\mathrm{odd}}((-1)^kM, k)}{\zeta(2k)}.$$ -/
theorem eulerProduct_sumSq_odd_squarefree (k : ℕ) (hk : 2 ≤ k) {M : ℤ} (hM0 : M ≠ 0) (hM : Squarefree M) :
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
      rw [localDensity_sumSq_odd_squarefree k hk1 (p : ℕ) h2 hM]
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

/-! ### The headline counts -/

/-- **Eisenstein's constant $c_5$** (Dickson, *Studies*, table (103)), for $n \not\equiv 0 \pmod 4$:
$80$ ($n \equiv 1 \bmod 8$), $112$ ($n \equiv 5 \bmod 8$), $160$ ($n \equiv 2, 3, 6, 7 \bmod 8$). -/
def c5 (n : ℕ) : ℝ := if n % 8 = 1 then 80 else if n % 8 = 5 then 112 else 160

/-- **Eisenstein's constant $c_7$** (Dickson, *Studies*, table (104)), for $n \not\equiv 0 \pmod 4$:
$560$ ($n \equiv 3 \bmod 8$), $592$ ($n \equiv 7 \bmod 8$), $448$ ($n \equiv 1, 2, 5, 6 \bmod 8$). -/
def c7 (n : ℕ) : ℝ := if n % 8 = 3 then 560 else if n % 8 = 7 then 592 else 448

/-! ### Helper lemmas for the headline counts -/

theorem mod_four_ne_zero_of_squarefree {n : ℕ} (hsf : Squarefree n) : n % 4 ≠ 0 := by
  intro h
  have h4 : 2 * 2 ∣ n := by omega
  have := hsf 2 h4
  exact absurd (Nat.isUnit_iff.mp this) (by norm_num)

theorem beta2_five (n : ℕ) (h4 : n % 4 ≠ 0) :
    128 * localDensity (sumSq 5) 2 (n : ℤ) = c5 n := by
  have key : ∀ r : ℕ, r < 8 → r % 4 ≠ 0 →
      128 * sqTable8 5 (r : ZMod 8) = (if r % 8 = 1 then 80 else if r % 8 = 5 then 112 else 160) * 4096 := by
    decide
  have hnd : ¬ (4 : ℤ) ∣ (n : ℤ) := by omega
  rw [localDensity_sumSq_two 5 n hnd, Int.cast_natCast, sqCount8_eq 5 (by norm_num),
    ← ZMod.natCast_mod n 8]
  have := key (n % 8) (Nat.mod_lt _ (by norm_num)) (by omega)
  rw [Nat.mod_mod] at this
  have h' : (128 * (sqTable8 5 ((n % 8 : ℕ) : ZMod 8) : ℝ)) =
      (if n % 8 = 1 then 80 else if n % 8 = 5 then 112 else 160) * 4096 := by
    exact_mod_cast this
  have hT : (sqTable8 5 ((n % 8 : ℕ) : ZMod 8) : ℝ) = (if n % 8 = 1 then 80 else if n % 8 = 5 then 112 else 160) * 4096 / 128 := by
    rw [eq_div_iff (by norm_num)]; linarith
  unfold c5
  rw [hT]
  split_ifs <;> norm_num

theorem beta2_seven (n : ℕ) (h4 : n % 4 ≠ 0) :
    512 * localDensity (sumSq 7) 2 (n : ℤ) = c7 n := by
  have key : ∀ r : ℕ, r < 8 → r % 4 ≠ 0 →
      512 * sqTable8 7 (r : ZMod 8) = (if r % 8 = 3 then 560 else if r % 8 = 7 then 592 else 448) * 262144 := by
    decide
  have hnd : ¬ (4 : ℤ) ∣ (n : ℤ) := by omega
  rw [localDensity_sumSq_two 7 n hnd, Int.cast_natCast, sqCount8_eq 7 (by norm_num),
    ← ZMod.natCast_mod n 8]
  have := key (n % 8) (Nat.mod_lt _ (by norm_num)) (by omega)
  rw [Nat.mod_mod] at this
  have h' : (512 * (sqTable8 7 ((n % 8 : ℕ) : ZMod 8) : ℝ)) =
      (if n % 8 = 3 then 560 else if n % 8 = 7 then 592 else 448) * 262144 := by
    exact_mod_cast this
  have hT : (sqTable8 7 ((n % 8 : ℕ) : ZMod 8) : ℝ) = (if n % 8 = 3 then 560 else if n % 8 = 7 then 592 else 448) * 262144 / 512 := by
    rw [eq_div_iff (by norm_num)]; linarith
  unfold c7
  rw [hT]
  split_ifs <;> norm_num

theorem zeta_four_tsum : (∑' m : ℕ, 1 / (m : ℝ) ^ (2 * 2)) = Real.pi ^ 4 / 90 :=
  hasSum_zeta_four.tsum_eq

theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd ⟨2, rfl⟩ (by norm_num)
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, h5, Nat.choose]

theorem zeta_six_tsum : (∑' m : ℕ, 1 / (m : ℝ) ^ (2 * 3)) = Real.pi ^ 6 / 945 := by
  rw [(hasSum_zeta_nat (k := 3) (by norm_num)).tsum_eq, bernoulli_eq_bernoulli'_of_ne_one (by norm_num),
    bernoulli'_six]
  norm_num [Nat.factorial]
  ring

/-- **Five squares, squarefree $n$** (five-square part, and for odd
$n$; Eisenstein 1847, Smith 1867; Dickson, *Studies in the Theory of Numbers*, ch. XIII, (101) and table (103)): for
squarefree $n \ge 1$,
$$\#\{\vec x \in \mathbb Z^5 : x_0^2 + \dots + x_4^2 = n\}
  = \frac{c_5(n)}{\pi^2}\,n^{3/2}\sum_{m\ \mathrm{odd}}\Bigl(\frac nm\Bigr)\frac1{m^2}.$$
**Proved** (unconditional). Restriction: squarefree $n$ (the source covers $n$ with no odd square factor, including
$4 \mid n$; loose end). -/
@[kb "dickson1930" "ch. XIII, (101), table (103) (-1335); Eisenstein 1847"]
theorem five_squares_squarefree (n : ℕ) (hn : 1 ≤ n) (hsf : Squarefree n) :
    (Nat.card {x : Fin 5 → ℤ // ∑ i, x i ^ 2 = n} : ℝ) =
      c5 n / Real.pi ^ 2 * (n : ℝ) ^ ((3 : ℝ) / 2) * oddJacobiSeries n 2 := by
  have hn4 := mod_four_ne_zero_of_squarefree hsf
  have h0 : (n : ℤ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hsfZ : Squarefree (n : ℤ) := Int.squarefree_natCast.mpr hsf
  have h1 := repNum_sumSq_eq_siegel (n := 5) (by norm_num) (by norm_num) (m := (n : ℤ))
    (by exact_mod_cast hn)
  have hE : eulerProduct (sumSq 5) (n : ℤ) = localDensity (sumSq 5) 2 (n : ℤ) / (1 - 1 / (2 : ℝ) ^ (2 * 2)) *
      oddJacobiSeries ((-1) ^ 2 * (n : ℤ)) 2 * (∑' m : ℕ, 1 / (m : ℝ) ^ (2 * 2))⁻¹ :=
    eulerProduct_sumSq_odd_squarefree 2 (by norm_num) h0 hsfZ
  have hcard : (Nat.card {x : Fin 5 → ℤ // ∑ i, x i ^ 2 = n}) = repNum (sumSq 5) (n : ℤ) :=
    sqRep_eq_repNum 5 n
  have hb := beta2_five n hn4
  rw [zeta_four_tsum, show ((-1 : ℤ) ^ 2 * (n : ℤ)) = n by ring] at hE
  rw [hcard, h1, hE, betaInf_sumSq_five]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hb' : localDensity (sumSq 5) 2 (n : ℤ) = c5 n / 128 := by rw [← hb]; ring
  rw [hb']
  push_cast
  field_simp
  norm_num
  ring

/-- **Seven squares, squarefree $n$** (seven-square part, and for odd
$n$; Eisenstein 1847/1850, Smith 1867; Dickson, *Studies*, ch. XIII, (101) and table (104)): for squarefree $n \ge 1$,
$$\#\{\vec x \in \mathbb Z^7 : x_0^2 + \dots + x_6^2 = n\}
  = \frac{c_7(n)}{\pi^3}\,n^{5/2}\sum_{m\ \mathrm{odd}}\Bigl(\frac{-n}{m}\Bigr)\frac1{m^3}.$$
**Proved** (unconditional). Restriction: squarefree $n$ (loose end, as for five squares). -/
@[kb "dickson1930" "ch. XIII, (101), table (104) (-1335); Eisenstein 1847/1850"]
theorem seven_squares_squarefree (n : ℕ) (hn : 1 ≤ n) (hsf : Squarefree n) :
    (Nat.card {x : Fin 7 → ℤ // ∑ i, x i ^ 2 = n} : ℝ) =
      c7 n / Real.pi ^ 3 * (n : ℝ) ^ ((5 : ℝ) / 2) * oddJacobiSeries (-(n : ℤ)) 3 := by
  have hn4 := mod_four_ne_zero_of_squarefree hsf
  have h0 : (n : ℤ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hsfZ : Squarefree (n : ℤ) := Int.squarefree_natCast.mpr hsf
  have h1 := repNum_sumSq_eq_siegel (n := 7) (by norm_num) (by norm_num) (m := (n : ℤ))
    (by exact_mod_cast hn)
  have hE : eulerProduct (sumSq 7) (n : ℤ) = localDensity (sumSq 7) 2 (n : ℤ) / (1 - 1 / (2 : ℝ) ^ (2 * 3)) *
      oddJacobiSeries ((-1) ^ 3 * (n : ℤ)) 3 * (∑' m : ℕ, 1 / (m : ℝ) ^ (2 * 3))⁻¹ :=
    eulerProduct_sumSq_odd_squarefree 3 (by norm_num) h0 hsfZ
  have hcard : (Nat.card {x : Fin 7 → ℤ // ∑ i, x i ^ 2 = n}) = repNum (sumSq 7) (n : ℤ) :=
    sqRep_eq_repNum 7 n
  have hb := beta2_seven n hn4
  rw [zeta_six_tsum, show ((-1 : ℤ) ^ 3 * (n : ℤ)) = -(n : ℤ) by ring] at hE
  rw [hcard, h1, hE, betaInf_sumSq_seven]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hb' : localDensity (sumSq 7) 2 (n : ℤ) = c7 n / 512 := by rw [← hb]; ring
  rw [hb']
  push_cast
  field_simp
  norm_num
  ring

/-- **Smith's five-squares formula for squarefree $M$** (Smith, *Collected Mathematical
Papers* II, Paper XLIV, Art. 16, pp. 672–675): for squarefree $M \ge 1$ the number of primitive representations of $M$
by $x_0^2 + \dots + x_4^2$ is
$$N(M) = \frac{160\,\zeta'(M)\,M^{3/2}}{\pi^2}\sum_{m\ \mathrm{odd}}\Bigl(\frac Mm\Bigr)\frac1{m^2}$$
(`primRepFive`, `smithZeta'`, `smithSeries`): `SmithFiveSquares` restricted to squarefree $M$. **Proved**
(unconditional); for squarefree $M$ every representation is primitive and Smith's $160\zeta'(M) = c_5(M)$. The general
case ($M$ with square factors) stays stated (`SmithFiveSquares`; loose end). -/
@[kb "smith1894" "Paper XLIV, Art. 16, pp. 672–675, squarefree M (occurrences smith1894-papers2:p672.2, p673.2–p675.1)"]
theorem smithFiveSquares_squarefree (M : ℕ) (hM : 1 ≤ M) (hsf : Squarefree M) :
    (primRepFive M : ℝ) =
      160 * smithZeta' M * (M : ℝ) ^ ((3 : ℝ) / 2) / Real.pi ^ 2 * smithSeries M := by
  have hn4 := mod_four_ne_zero_of_squarefree hsf
  have h5 := five_squares_squarefree M hM hsf
  have hp : primRepFive M = Nat.card {x : Fin 5 → ℤ // ∑ i, x i ^ 2 = M} :=
    sqRepProper_eq_sqRep_of_squarefree 5 M hsf
  rw [hp, h5, smithSeries_eq]
  have hc : 160 * smithZeta' M = c5 M := by
    unfold smithZeta' c5
    split_ifs <;> first | omega | norm_num
  rw [← hc]
  ring

end QuadFormsKB.Historical.SumsOfSquares
