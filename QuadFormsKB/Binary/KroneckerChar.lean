import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.QuadraticField

/-!
# The Kronecker character $\chi_D$ of a fundamental discriminant

For a fundamental discriminant $D \ne 1$ (`IsQuadDisc D`) we build the **Kronecker character**
$\chi_D = \left(\frac{D}{\cdot}\right)$ as a Dirichlet character modulo $|D|$ (`kroneckerChar D`):

* $D \equiv 1 \pmod 4$: $\chi_D(n) = \left(\frac{n}{|D|}\right)$ (Jacobi symbol in the *lower* entry fixed);
* $D = 4m$: $\chi_D(n) = \left(\frac{m}{n}\right)$ for odd $n$ (Jacobi symbol), $\chi_D(n) = 0$ for even $n$.

The main result `kroneckerChar_prime` is the **uniform description at every prime $p$, including $p = 2$**:
$$\chi_D(p) = \#\{x \in \mathbb{F}_p : x^2 = a_D + b_D x\} - 1,$$
the number of roots mod $p$ of $f_D = X^2 - b_D X - a_D$ (the minimal polynomial of
$\omega = (b_D + \sqrt D)/2$) minus one. For odd $p$ this is $\left(\frac{D}{p}\right)$ (Legendre), via quadratic
reciprocity for the Jacobi symbol; for $p = 2$ it is $1, -1, 0$ as $D \equiv 1 \pmod 8$, $D \equiv 5 \pmod 8$, $4 \mid D$.

Sources: Davenport, *Multiplicative Number Theory*, Ch. 5 (the character $\chi_D$, there for prime
discriminants) and Ch. 6; Cohen, *A Course in Computational Algebraic Number Theory*, §1.4.2 (Kronecker symbol)
and §5.3; Zagier, *Zetafunktionen und quadratische Körper*, §8.
-/

open QuadraticAlgebra

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Binary

variable {D : ℤ}

/-! ### Elementary facts about $|D|$ -/

theorem natAbs_odd_of_one (h : D % 4 = 1) : Odd D.natAbs := by
  rw [Nat.odd_iff]; omega

theorem three_le_natAbs [hD : IsQuadDisc D] : 3 ≤ D.natAbs := by
  have h1 := hD.fund.1
  have h2 := hD.ne_one
  have h0 := hD.fund.ne_zero
  rcases h1 with h | h
  · -- D = 4m with m ≢ 0 (mod 4), so m ≠ 0 and |D| ≥ 4
    have := (Int.isFundamentalDiscr_iff_squarefree.mp hD.fund)
    omega
  · omega

/-! ### The character -/

/-- **The values of the Kronecker character** $\chi_D$ on $\mathbb{Z}/|D|$, as integers, with $x$ represented by
$0 \le n = $ `x.val` $< |D|$: $\left(\frac{n}{|D|}\right)$ if $D \equiv 1 \pmod 4$; $\left(\frac{D/4}{n}\right)$ for odd
$n$ and $0$ for even $n$ if $4 \mid D$. -/
def kronZ (D : ℤ) (x : ZMod D.natAbs) : ℤ :=
  if D % 4 = 1 then jacobiSym (x.val : ℤ) D.natAbs
  else if Odd x.val then jacobiSym (D / 4) x.val else 0

theorem kronZ_natCast_of_one (h : D % 4 = 1) (n : ℕ) :
    kronZ D (n : ZMod D.natAbs) = jacobiSym n D.natAbs := by
  rw [kronZ, ite_eq_left h, ZMod.val_natCast]
  exact (jacobiSym.mod_left' (by push_cast; exact Int.emod_emod_of_dvd _ (dvd_refl _))).trans rfl

theorem kronZ_natCast_of_zero [IsQuadDisc D] (h : D % 4 = 0) {n : ℕ} (hn : Odd n) :
    kronZ D (n : ZMod D.natAbs) = jacobiSym (D / 4) n := by
  have hN : D.natAbs = 4 * (D / 4).natAbs := by omega
  have hNe : Even D.natAbs := ⟨2 * (D / 4).natAbs, by omega⟩
  have hodd : Odd (n % D.natAbs) := by
    rw [Nat.odd_iff, Nat.mod_mod_of_dvd n (even_iff_two_dvd.mp hNe)]
    exact Nat.odd_iff.mp hn
  rw [kronZ, ite_eq_right (by omega), ZMod.val_natCast, ite_eq_left hodd, jacobiSym.mod_right _ hn, ← hN]

theorem kronZ_one [IsQuadDisc D] : kronZ D 1 = 1 := by
  have : Fact (1 < D.natAbs) := ⟨by linarith [three_le_natAbs (D := D)]⟩
  rw [kronZ, ZMod.val_one]
  split_ifs with h h'
  · exact jacobiSym.one_left _
  · exact jacobiSym.one_right _
  · exact absurd odd_one h'

theorem natAbs_eq_of_zero [hD : IsQuadDisc D] (h : D % 4 ≠ 1) : D.natAbs = 4 * (D / 4).natAbs := by
  have := hD.fund.1; omega

theorem odd_mod_natAbs_iff [IsQuadDisc D] (h : D % 4 ≠ 1) (n : ℕ) :
    Odd (n % D.natAbs) ↔ Odd n := by
  have hNe : 2 ∣ D.natAbs := ⟨2 * (D / 4).natAbs, by rw [natAbs_eq_of_zero h]; ring⟩
  rw [Nat.odd_iff, Nat.odd_iff, Nat.mod_mod_of_dvd n hNe]

theorem kronZ_mul [IsQuadDisc D] (x y : ZMod D.natAbs) : kronZ D (x * y) = kronZ D x * kronZ D y := by
  have hN0 : D.natAbs ≠ 0 := by linarith [three_le_natAbs (D := D)]
  have : NeZero D.natAbs := ⟨hN0⟩
  rw [kronZ, kronZ, kronZ, ZMod.val_mul]
  by_cases h : D % 4 = 1
  · simp only [h, ↓reduceIte]
    rw [← jacobiSym.mul_left]
    exact jacobiSym.mod_left' (by push_cast; exact Int.emod_emod_of_dvd _ (dvd_refl _))
  · simp only [h, ↓reduceIte, odd_mod_natAbs_iff h, Nat.odd_mul]
    by_cases hx : Odd x.val <;> by_cases hy : Odd y.val <;> simp only [hx, hy, and_self, and_true,
      and_false, ↓reduceIte, mul_zero, zero_mul]
    have hx0 : x.val ≠ 0 := fun h0 => by simp [h0] at hx
    have hy0 : y.val ≠ 0 := fun h0 => by simp [h0] at hy
    have : NeZero x.val := ⟨hx0⟩
    have : NeZero y.val := ⟨hy0⟩
    rw [← jacobiSym.mul_right, jacobiSym.mod_right _ (hx.mul hy), ← natAbs_eq_of_zero h]

theorem kronZ_nonunit [IsQuadDisc D] (x : ZMod D.natAbs) (hx : ¬ IsUnit x) : kronZ D x = 0 := by
  have hN0 : D.natAbs ≠ 0 := by linarith [three_le_natAbs (D := D)]
  have : NeZero D.natAbs := ⟨hN0⟩
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime] at hx
  rw [kronZ]
  by_cases h : D % 4 = 1
  · simp only [h, ↓reduceIte]
    rw [jacobiSym.eq_zero_iff]
    exact ⟨hN0, by rwa [Int.gcd_natCast_natCast]⟩
  · simp only [h, ↓reduceIte]
    split_ifs with ho
    · rw [jacobiSym.eq_zero_iff]
      refine ⟨fun h0 => by simp [h0] at ho, fun hg => hx ?_⟩
      have hN := natAbs_eq_of_zero h
      suffices Nat.Coprime x.val (4 * (D / 4).natAbs) by rwa [← hN] at this
      refine Nat.Coprime.mul_right ?_ ?_
      · have := Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr ho)
        norm_num at this
        exact this
      · rw [Int.gcd_comm] at hg
        exact hg
    · rfl

/-- **The Kronecker character as a multiplicative character** $\mathbb{Z}/|D| \to \mathbb{Z}$. -/
def kronMulChar (D : ℤ) [IsQuadDisc D] : MulChar (ZMod D.natAbs) ℤ where
  toFun := kronZ D
  map_one' := kronZ_one
  map_mul' := kronZ_mul
  map_nonunit' := kronZ_nonunit

/-- **The Kronecker character $\chi_D = \left(\frac{D}{\cdot}\right)$**, a (real, quadratic) Dirichlet character
modulo $|D|$ with values in $\{0, \pm 1\} \subset \mathbb{C}$: $\chi_D(n) = \left(\frac{n}{|D|}\right)$ (Jacobi) if
$D \equiv 1 \pmod 4$, and $\chi_D(n) = \left(\frac{D/4}{n}\right)$ for odd $n$, $\chi_D(n) = 0$ for even $n$, if
$4 \mid D$. Its values at primes are given by `kroneckerChar_prime` (the splitting law). Source: Davenport, Ch. 5;
Cohen §1.4.2; Zagier §8. -/
@[kb "davenport2000" "Ch. 5"]
noncomputable def kroneckerChar (D : ℤ) [IsQuadDisc D] : DirichletCharacter ℂ D.natAbs :=
  (kronMulChar D).ringHomComp (Int.castRingHom ℂ)

theorem kroneckerChar_apply [IsQuadDisc D] (x : ZMod D.natAbs) :
    kroneckerChar D x = (kronZ D x : ℂ) := rfl

/-! ### Values at primes -/

/-- **The number of roots of $f_D = X^2 - b_D X - a_D$ in $\mathbb{F}_p$**,
$\#\{x \in \mathbb{Z}/p : x^2 = a_D + b_D x\}$. -/
def rootCount (D : ℤ) (p : ℕ) [NeZero p] : ℕ :=
  (Finset.univ.filter fun x : ZMod p => x ^ 2 = (qa D : ZMod p) + (qb D : ZMod p) * x).card

/-- For odd $p$, completing the square: $x \mapsto 2x - b_D$ is a bijection from the roots of $f_D$ onto the
square roots of $D$ in $\mathbb{F}_p$. -/
theorem rootCount_eq_card_sqrts [hD : IsQuadDisc D] (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    rootCount D p = (Finset.univ.filter fun y : ZMod p => y ^ 2 = (D : ZMod p)).card := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this)
  have hdisc : ((qb D : ZMod p)) ^ 2 + 4 * (qa D : ZMod p) = D := by
    have := discr_qa_qb hD.fund.1
    rw [discr_def] at this
    exact_mod_cast congrArg (fun z : ℤ => (z : ZMod p)) this
  refine Finset.card_bij' (fun x _ => 2 * x - qb D) (fun y _ => (y + qb D) * 2⁻¹) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [← hdisc]; linear_combination 4 * hx
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    obtain ⟨z, rfl⟩ : ∃ z, y = 2 * z - qb D := ⟨(y + qb D) * 2⁻¹, by field_simp; ring⟩
    have hz : (2 * z - qb D + qb D) * 2⁻¹ = z := by field_simp; ring
    rw [hz]
    have h4 : (4 : ZMod p) ≠ 0 := by
      rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
    apply mul_left_cancel₀ h4
    rw [← hdisc] at hy
    linear_combination hy
  · intro x _
    field_simp; ring
  · intro y _
    field_simp; ring

/-- **For odd $p$, $\#\{\text{roots of } f_D \bmod p\} = 1 + \left(\frac{D}{p}\right)$.** -/
theorem rootCount_odd [IsQuadDisc D] (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (rootCount D p : ℤ) = legendreSym p D + 1 := by
  rw [rootCount_eq_card_sqrts p hp, legendreSym, ← quadraticChar_card_sqrts]
  · congr 2
    ext y; simp
  · rw [ZMod.ringChar_zmod_n]; exact hp

/-- **At odd primes, $\chi_D(p) = \left(\frac{D}{p}\right)$** (Legendre symbol). For $D \equiv 1 \pmod 4$ this is
quadratic reciprocity for the Jacobi symbol $\left(\frac{p}{|D|}\right)$ (with the supplement
$\left(\frac{-1}{p}\right)$ when $D < 0$); for $D = 4m$ it is $\left(\frac{4m}{p}\right) = \left(\frac{m}{p}\right)$. -/
theorem kronZ_odd_prime [hD : IsQuadDisc D] (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    kronZ D (p : ZMod D.natAbs) = legendreSym p D := by
  have hpo : Odd p := hp.out.odd_of_ne_two hp2
  rw [jacobiSym.legendreSym.to_jacobiSym]
  by_cases h : D % 4 = 1
  · rw [kronZ_natCast_of_one h]
    rcases le_or_gt 0 D with hpos | hneg
    · have hN : (D.natAbs : ℤ) = D := Int.natAbs_of_nonneg hpos
      rw [show jacobiSym D p = jacobiSym (D.natAbs : ℤ) p by rw [hN],
        jacobiSym.quadratic_reciprocity_one_mod_four (by omega) hpo]
    · have hN : D = -(D.natAbs : ℤ) := by omega
      have hN3 : D.natAbs % 4 = 3 := by omega
      conv_rhs => rw [hN, neg_eq_neg_one_mul, jacobiSym.mul_left, jacobiSym.at_neg_one hpo,
        ZMod.χ₄_nat_eq_if_mod_four]
      have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by rcases Nat.odd_iff.mp hpo with h; omega
      rcases hp4 with h4 | h4
      · rw [ite_eq_right (by omega), ite_eq_left h4, one_mul,
          jacobiSym.quadratic_reciprocity_one_mod_four' (natAbs_odd_of_one h) h4]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), jacobiSym.quadratic_reciprocity_three_mod_four hN3 h4]
        ring
  · rw [kronZ_natCast_of_zero (by have := hD.fund.1; omega) hpo]
    have h4 : D = 4 * (D / 4) := by have := hD.fund.1; omega
    conv_rhs => rw [h4, jacobiSym.mul_left, jacobiSym.at_four hpo, one_mul]

/-- **$\chi_D(2)$**: $1$ if $D \equiv 1 \pmod 8$, $-1$ if $D \equiv 5 \pmod 8$, $0$ if $4 \mid D$. -/
theorem kronZ_two [hD : IsQuadDisc D] :
    kronZ D (2 : ZMod D.natAbs) = if D % 4 = 1 then (if D % 8 = 1 then 1 else -1) else 0 := by
  have h3 := three_le_natAbs (D := D)
  by_cases h : D % 4 = 1
  · rw [ite_eq_left h, show (2 : ZMod D.natAbs) = ((2 : ℕ) : ZMod D.natAbs) by norm_num,
      kronZ_natCast_of_one h, show ((2 : ℕ) : ℤ) = 2 by norm_num,
      jacobiSym.at_two (natAbs_odd_of_one h), ZMod.χ₈_nat_eq_if_mod_eight]
    split_ifs <;> omega
  · rw [ite_eq_right h, kronZ, ite_eq_right h, show (2 : ZMod D.natAbs) = ((2 : ℕ) : ZMod D.natAbs) by norm_num,
      ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), ite_eq_right (by decide)]

theorem intCast_zmod_two (n : ℤ) : (n : ZMod 2) = if n % 2 = 0 then 0 else 1 := by
  rw [← ZMod.intCast_mod n 2]
  have : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases this with h | h <;> simp [h]

/-- **The roots of $f_D$ mod $2$**: two if $D \equiv 1 \pmod 8$, none if $D \equiv 5 \pmod 8$, one if $4 \mid D$. -/
theorem rootCount_two [hD : IsQuadDisc D] :
    rootCount D 2 = if D % 4 = 1 then (if D % 8 = 1 then 2 else 0) else 1 := by
  have key : ∀ A B : ZMod 2, (Finset.univ.filter fun x : ZMod 2 => x ^ 2 = A + B * x).card =
      if B = 0 then 1 else if A = 0 then 2 else 0 := by decide
  have := hD.fund.1
  by_cases h : D % 4 = 1
  · have hb : ((qb D : ℤ) : ZMod 2) = 1 := by
      rw [intCast_zmod_two, ite_eq_right (by unfold qb; omega)]
    rw [rootCount, key, hb, ite_eq_left h, ite_eq_right one_ne_zero]
    by_cases h8 : D % 8 = 1
    · have ha : ((qa D : ℤ) : ZMod 2) = 0 := by
        rw [intCast_zmod_two, ite_eq_left (by unfold qa; omega)]
      rw [ha, ite_eq_left rfl, ite_eq_left h8]
    · have ha : ((qa D : ℤ) : ZMod 2) = 1 := by
        rw [intCast_zmod_two, ite_eq_right (by unfold qa; omega)]
      rw [ha, ite_eq_right one_ne_zero, ite_eq_right h8]
  · have hb : ((qb D : ℤ) : ZMod 2) = 0 := by
      rw [intCast_zmod_two, ite_eq_left (by unfold qb; omega)]
    rw [rootCount, key, hb, ite_eq_right h, ite_eq_left rfl]

/-- **The splitting law for $\chi_D$ (uniform in $p$, including $p = 2$):**
$$\chi_D(p) = \#\{x \in \mathbb{F}_p : x^2 = a_D + b_D x\} - 1,$$
i.e. $\chi_D(p) = 1, 0, -1$ according as $f_D = X^2 - b_D X - a_D$ has two, one (double) or no roots mod $p$.
For odd $p$ both sides are $\left(\frac{D}{p}\right)$ (`kronZ_odd_prime`, `rootCount_odd`); for $p = 2$ both are
$1, -1, 0$ as $D \equiv 1 \pmod 8$, $D \equiv 5 \pmod 8$, $4 \mid D$. -/
@[kb "marcus1977" "Ch. 3, Thm. 25"]
theorem kroneckerChar_prime [IsQuadDisc D] (p : ℕ) [Fact p.Prime] :
    kroneckerChar D p = (rootCount D p : ℂ) - 1 := by
  rw [show ((p : ZMod D.natAbs)) = ((p : ℕ) : ZMod D.natAbs) from rfl, kroneckerChar_apply]
  by_cases hp2 : p = 2
  · subst hp2
    have h1 := rootCount_two (D := D)
    have h2 := kronZ_two (D := D)
    rw [show ((2 : ℕ) : ZMod D.natAbs) = 2 by norm_num, h2, h1]
    split_ifs <;> norm_num
  · rw [kronZ_odd_prime p hp2]
    have := rootCount_odd (D := D) p hp2
    have : ((rootCount D p : ℤ) : ℂ) = ((legendreSym p D + 1 : ℤ) : ℂ) := by rw [this]
    push_cast at this; rw [this]; ring
