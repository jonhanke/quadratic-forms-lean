/-
# Classical special cases over $\mathbb Q$: Dirichlet's formula for $x_0^2-2x_1^2$ for every $m\ge1$

**Layer:** $\mathbb Q$.

`dirichlet_pell2` (`Binary.lean`) assumes that $m$ is represented by $x_0^2-2x_1^2$ over $\mathbb Q$ (a rational frame of
$\langle m\rangle$). Here that hypothesis is removed, as for `dirichlet_sumTwoSq`: if $m$ is not represented, the left
side is $0$, and so is $\sum_{d\mid m}\chi_8(d)$, since a nonzero divisor sum forces every prime $q\equiv3,5\pmod8$ to
divide $m$ to an even power, which by the criterion `pell2_value_iff` (`Pell2Values.lean`) makes $m$ a value.
-/
import QuadFormsKB.Tamagawa.Classical.Binary
import QuadFormsKB.Tamagawa.Classical.Pell2Values

open NumberField IsDedekindDomain
open scoped ENNReal

namespace QuadFormsKB.Tamagawa.Classical

open QuadFormsKB.Binary QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Tamagawa.Measure.Weil RatBridge LocalDensity

/-- **If $\sum_{d\mid m}\chi_8(d)\ne0$, every prime $q\equiv3,5\pmod 8$ divides $m$ to an even power.** -/
theorem even_padicValNat_of_sum_chi8_ne_zero {m : ℕ} (hm : m ≠ 0)
    (h : ∑ d ∈ m.divisors, (ZMod.χ₈ (d : ZMod 8) : ℝ) ≠ 0) {q : ℕ} (hq : q.Prime) (h8 : q % 8 = 3 ∨ q % 8 = 5) :
    Even (padicValNat q m) := by
  by_cases hqm : q ∣ m
  · rw [← prod_locRatio₈ hm, Finset.prod_ne_zero_iff] at h
    have hmem : q ∈ (2 * m).primeFactors :=
      Nat.mem_primeFactors.2 ⟨hq, Dvd.dvd.mul_left hqm 2, by omega⟩
    have hloc := h q hmem
    have hq2 : q ≠ 2 := by omega
    have hχ : (ZMod.χ₈ (q : ZMod 8) : ℝ) = -1 := by
      rw [ZMod.χ₈_nat_eq_if_mod_eight]
      rcases h8 with h8 | h8 <;> simp [h8] <;> omega
    rw [locRatio₈, ite_eq_right hq2, hχ, sum_range_neg_one_pow] at hloc
    rw [← Nat.factorization_def m hq]
    by_contra hodd
    exact hloc (ite_eq_left (Nat.not_even_iff_odd.1 hodd).add_one)
  · rw [padicValNat.eq_zero_of_not_dvd hqm]; exact ⟨0, rfl⟩

/-- **Dirichlet's formula for $x_0^2-2x_1^2$, every $m\ge1$** (Dirichlet, *Vorlesungen über Zahlentheorie*, §§ 89–93
[unverified locator]; Siegel 1935, Hauptsatz for $n = 2$, $m = 1$): for every $m\ge1$, the number of representations of
$m$ by the genus of $\mathbb Z^2$ with $x_0^2 - 2x_1^2$, each class $M_i$ counted modulo its (infinite) unit group
$SO(M_i)$, is $\sum_{d\mid m}\chi_8(d)$, $\chi_8 = \left(\frac 8\cdot\right)$. If $m$ is not a value of $x_0^2-2x_1^2$ both
sides vanish (`pell2_value_iff`). This is `dirichlet_pell2` without its hypothesis that $m$ is represented over
$\mathbb Q$. Unconditional. -/
@[kb "dirichlet1863" "Vorlesungen über Zahlentheorie, §§ 89–93 (number of representations by a genus) [unverified locator]"]
theorem dirichlet_pell2_uncond (m : ℕ) (hm : 1 ≤ m) :
    ∑' i, Indefinite.repCount (up pell2Z) (DVR.unary (((m : ℤ) : 𝓞 ℚ))) i =
      ENNReal.ofReal (∑ d ∈ m.divisors, (ZMod.χ₈ (d : ZMod 8) : ℝ)) := by
  have hm0 : m ≠ 0 := by omega
  by_cases hne : Nonempty (RatFrame (up pell2Z) (DVR.unary (((m : ℤ) : 𝓞 ℚ))))
  · obtain ⟨Ξ⟩ := hne
    exact dirichlet_pell2 m hm Ξ
  · rw [tsum_repCount_eq_zero_of_isEmpty _ _ (not_nonempty_iff.1 hne)]
    by_cases hs : ∑ d ∈ m.divisors, (ZMod.χ₈ (d : ZMod 8) : ℝ) = 0
    · rw [hs, ENNReal.ofReal_zero]
    · exfalso
      obtain ⟨x, y, hxy⟩ := pell2_value_iff.2 fun q hq h8 =>
        even_padicValNat_of_sum_chi8_ne_zero hm0 hs (Nat.prime_of_mem_primeFactors hq) h8
      exact hne ⟨ratFrameOfInt 1 (-2) (x := x) (y := y) (by rw [← hxy]; ring)⟩

/-! ### Negative $m$

The integral automorphism $\sigma(x_0,x_1) = (x_0+2x_1,\,x_0+x_1)$ (multiplication by the unit $1+\sqrt2$ of norm $-1$,
inverse $(y_0,y_1)\mapsto(-y_0+2y_1,\,y_0-y_1)$) satisfies $Q\circ\sigma = -Q$ for $Q = x_0^2-2x_1^2$, so the local
densities of $Q$ at $m$ and $-m$ agree. -/

/-- $Q(x) = x_0^2 - 2x_1^2$ for `pell2Z` over any commutative ring $K$. -/
theorem pell2Z_evalIn (K : Type*) [CommRing K] (x : Fin 2 → K) : pell2Z.evalIn K x = x 0 ^ 2 - 2 * x 1 ^ 2 := by
  simp [pell2Z, QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_two, Matrix.diagonal]
  ring

/-- The automorphism $\sigma(x_0,x_1) = (x_0+2x_1,\,x_0+x_1)$ of $K^2$, with $Q(\sigma x) = -Q(x)$ for $Q = x_0^2-2x_1^2$. -/
def pell2Flip (K : Type*) [CommRing K] : (Fin 2 → K) ≃ (Fin 2 → K) where
  toFun x := ![x 0 + 2 * x 1, x 0 + x 1]
  invFun y := ![-y 0 + 2 * y 1, y 0 - y 1]
  left_inv x := by funext i; fin_cases i <;> simp <;> ring
  right_inv y := by funext i; fin_cases i <;> simp <;> ring

/-- $Q(\sigma x) = -Q(x)$ for $Q = x_0^2 - 2x_1^2$ and $\sigma$ = `pell2Flip`. -/
theorem pell2Z_evalIn_flip (K : Type*) [CommRing K] (x : Fin 2 → K) :
    pell2Z.evalIn K (pell2Flip K x) = -pell2Z.evalIn K x := by
  simp only [pell2Z_evalIn, pell2Flip, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- $r_{p^k}(-m) = r_{p^k}(m)$ for $x_0^2-2x_1^2$. -/
theorem repCount_pell2Z_neg (p k : ℕ) (m : ℤ) :
    LocalDensity.repCount pell2Z p k (-m) = LocalDensity.repCount pell2Z p k m := by
  unfold LocalDensity.repCount
  refine Nat.card_congr ((pell2Flip (ZMod (p ^ k))).subtypeEquiv fun x => ?_)
  rw [pell2Z_evalIn_flip, Int.cast_neg]; exact neg_eq_iff_eq_neg.symm

/-- $\beta_p(-m) = \beta_p(m)$ for $x_0^2-2x_1^2$. -/
theorem localDensity_pell2Z_neg (p : ℕ) (m : ℤ) :
    LocalDensity.localDensity pell2Z p (-m) = LocalDensity.localDensity pell2Z p m := by
  unfold LocalDensity.localDensity
  simp_rw [repCount_pell2Z_neg]

/-- **Dirichlet's formula for $x_0^2-2x_1^2$ at negative integers** (Dirichlet, *Vorlesungen über Zahlentheorie*,
§§ 89–93 [unverified locator]): for every $m\ge1$, the number of representations of $-m$ by the genus of $\mathbb Z^2$ with
$x_0^2 - 2x_1^2$, each class $M_i$ counted modulo its unit group $SO(M_i)$, is $\sum_{d\mid m}\chi_8(d)$, the same as for
$m$. Unconditional. -/
@[kb "dirichlet1863" "Vorlesungen über Zahlentheorie, §§ 89–93 (number of representations by a genus) [unverified locator]"]
theorem dirichlet_pell2_neg (m : ℕ) (hm : 1 ≤ m) :
    ∑' i, Indefinite.repCount (up pell2Z) (DVR.unary ((-(m : ℤ) : ℤ) : 𝓞 ℚ)) i =
      ENNReal.ofReal (∑ d ∈ m.divisors, (ZMod.χ₈ (d : ZMod 8) : ℝ)) := by
  have hm0 : m ≠ 0 := by omega
  have Ξ₁ : RatFrame (up pell2Z) (DVR.unary ((1 : ℤ) : 𝓞 ℚ)) := ratFrameOfInt 1 (-2) (x := 1) (y := 0) (by norm_num)
  by_cases hne : Nonempty (RatFrame (up pell2Z) (DVR.unary ((-(m : ℤ) : ℤ) : 𝓞 ℚ)))
  · obtain ⟨Ξ⟩ := hne
    rw [tsum_repCount_eq_tprod (up pell2Z) nondegenerate_up_pell2 anisotropicF_up_pell2 (QField 8) isDiscField_pell2
      (by simpa using Ξ₁) tsum_repCount_one_pell2 (by push_cast; exact neg_ne_zero.2 (by exact_mod_cast hm0)) Ξ _
      (mulSupport_locRatio₈_finite hm0) (fun v => ?_), tprod_locRatio₈ hm0]
    have : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
    rw [nfLocalDensity_up, localDensity_pell2Z_neg, ← nfLocalDensity_up]
    exact nfLocalDensity_pell2_eq v hm0
  · rw [tsum_repCount_eq_zero_of_isEmpty _ _ (not_nonempty_iff.1 hne)]
    by_cases hs : ∑ d ∈ m.divisors, (ZMod.χ₈ (d : ZMod 8) : ℝ) = 0
    · rw [hs, ENNReal.ofReal_zero]
    · exfalso
      obtain ⟨x, y, hxy⟩ := (pell2_value_neg_iff (m : ℤ)).2 (pell2_value_iff.2 fun q hq h8 =>
        even_padicValNat_of_sum_chi8_ne_zero hm0 hs (Nat.prime_of_mem_primeFactors hq) h8)
      exact hne ⟨ratFrameOfInt 1 (-2) (x := x) (y := y) (by rw [← hxy]; ring)⟩

end QuadFormsKB.Tamagawa.Classical
