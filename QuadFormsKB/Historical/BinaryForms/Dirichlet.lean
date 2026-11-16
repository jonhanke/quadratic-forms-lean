/-
# Dirichlet's formula for the binary forms of class number one: $x^2 + 2y^2$, $x^2 + xy + y^2$, $x^2 + xy + 2y^2$

**Library** `QuadFormsKB.Historical.BinaryForms` (historical library, not imported by `QuadFormsKB`). Infrastructure
for the historical sources targets on primes of the form $x^2 + ny^2$ and on Smith's representation counts
(`Primes.lean`, `Smith.lean`).

For a fundamental discriminant $D < 0$ with class number $h(D) = 1$ and a primitive positive definite form $f$ of
discriminant $D$, Dirichlet's formula (`Binary.dirichlet_sum_repNum_int`, proved in this library through the ideals of
$\mathcal O_{\mathbb Q(\sqrt D)}$) has a single term:
$$r_f(m) = w\sum_{d \mid m}\chi_D(d)\qquad(m \ge 1),$$
$w$ the number of roots of unity of $\mathbb Q(\sqrt D)$ (`repNum_eq_of_classNumber_one`). Here it is made explicit for
$D = -8$ ($x^2 + 2y^2$, $w = 2$), $D = -3$ ($x^2 + xy + y^2$, $w = 6$) and $D = -7$ ($x^2 + xy + 2y^2$, $w = 2$), with
$h = 1$ from Minkowski's bound (Mathlib's `RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt`) and the characters
written out:
* $\chi_{-8}(d) = 1, -1, 0$ for $d \equiv 1, 3;\ 5, 7;\ $ even $\pmod 8$ (`chiNeg8`);
* $\chi_{-3}(d) = \bigl(\frac d3\bigr)$ (Legendre's symbol, `chi3`);
* $\chi_{-7}(d) = \bigl(\frac d7\bigr)$ (`chi7`).

Counts are of ordered pairs $(x, y) \in \mathbb Z^2$, signs included. Unconditional.
-/
import QuadFormsKB.Binary.RepresentationCount
import QuadFormsKB.Binary.FormAut
import Mathlib.RingTheory.Prime
import Mathlib.Tactic.NormNum.LegendreSymbol

open NumberField

namespace QuadFormsKB.Historical.BinaryForms

open QuadFormsKB QuadFormsKB.Binary

/-! ### The general statement -/

/-- **Dirichlet's formula for class number one:** for a fundamental discriminant $D < 0$ with $h(D) = 1$, a primitive
positive definite form $f$ of discriminant $D$ and $m \ge 1$,
$r_f(m) = w\sum_{d \mid m}\chi_D(d)$, $w$ = `torsionOrder (QField D)`, $\chi_D$ = `kronZ D`. -/
theorem repNum_eq_of_classNumber_one {D : ℤ} [IsQuadDisc D] [Fact (D < 0)]
    (h1 : classNumber (QField D) = 1) (f : PrimPosForm D) {m : ℕ} (hm : m ≠ 0) :
    (Siegel.repNum f.1 m : ℤ) =
      NumberField.Units.torsionOrder (QField D) * ∑ d ∈ m.divisors, kronZ D (d : ZMod D.natAbs) := by
  have hcard : Nat.card (Quotient (slSetoid D)) = 1 := by rw [card_slClasses Fact.out, h1]
  have hsub : Subsingleton (Quotient (slSetoid D)) :=
    haveI := finite_slClasses (D := D) Fact.out
    Finite.card_le_one_iff_subsingleton.mp hcard.le
  have huniv : (Finset.univ : Finset (Quotient (slSetoid D))) = {Quotient.mk (slSetoid D) f} := by
    ext c; simp [Subsingleton.elim c (Quotient.mk (slSetoid D) f)]
  have h := dirichlet_sum_repNum_int (D := D) hm
  rw [huniv, Finset.sum_singleton] at h
  exact h

/-- $r_f(m)$ for $f = ax^2 + bxy + cy^2$ is the number of pairs $(x, y) \in \mathbb Z^2$ with $ax^2 + bxy + cy^2 = m$. -/
theorem repNum_mk_eq_card (a b c m : ℤ) :
    Siegel.repNum (BinQF.mk a b c) m = Nat.card {p : ℤ × ℤ // a * p.1 ^ 2 + b * p.1 * p.2 + c * p.2 ^ 2 = m} := by
  unfold Siegel.repNum Siegel.repSet
  refine Nat.card_congr
    { toFun := fun x => ⟨(x.1 0, x.1 1), ?_⟩
      invFun := fun p => ⟨![p.1.1, p.1.2], ?_⟩
      left_inv := fun x => Subtype.ext (by funext i; fin_cases i <;> rfl)
      right_inv := fun p => rfl }
  · have h : (BinQF.mk a b c).eval (x.1 0) (x.1 1) = m := by
      have hx : QuadForm.eval (BinQF.mk a b c) x.1 = m := x.2
      rw [BinQF.eval]
      convert hx using 2
      funext i; fin_cases i <;> rfl
    rw [BinQF.eval_eq] at h
    simpa [BinQF.a, BinQF.b, BinQF.c, BinQF.mk, QuadForm.ofUpper] using h
  · have h : (BinQF.mk a b c).eval p.1.1 p.1.2 = m := by
      rw [BinQF.eval_eq]
      simpa [BinQF.a, BinQF.b, BinQF.c, BinQF.mk, QuadForm.ofUpper] using p.2
    exact h

/-! ### The characters, written out -/

/-- $\chi_{-8}(d) = \bigl(\frac{-8}{d}\bigr)$: $1$ for $d \equiv 1, 3 \pmod 8$, $-1$ for $d \equiv 5, 7 \pmod 8$, $0$ for even
$d$. -/
def chiNeg8 (d : ℕ) : ℤ := if d % 8 = 1 ∨ d % 8 = 3 then 1 else if d % 8 = 5 ∨ d % 8 = 7 then -1 else 0

/-- $\bigl(\frac d3\bigr)$ (Legendre's symbol modulo $3$, $= \chi_{-3}(d)$): $1$, $-1$, $0$ for $d \equiv 1, 2, 0 \pmod 3$. -/
def chi3 (d : ℕ) : ℤ := if d % 3 = 1 then 1 else if d % 3 = 2 then -1 else 0

/-- $\bigl(\frac d7\bigr)$ (Legendre's symbol modulo $7$, $= \chi_{-7}(d)$): $1$ for $d \equiv 1, 2, 4$, $-1$ for
$d \equiv 3, 5, 6$, $0$ for $d \equiv 0 \pmod 7$. -/
def chi7 (d : ℕ) : ℤ :=
  if d % 7 = 1 ∨ d % 7 = 2 ∨ d % 7 = 4 then 1 else if d % 7 = 3 ∨ d % 7 = 5 ∨ d % 7 = 6 then -1 else 0

/-! ### The three discriminants: instances, class number one, torsion, characters -/

instance isQuadDisc_neg_eight' : IsQuadDisc (-8) where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    right
    refine ⟨?_, ?_, ?_⟩ <;> norm_num
    exact Int.prime_two.neg.squarefree
  ne_one := by norm_num

instance isQuadDisc_neg_three' : IsQuadDisc (-3) where
  fund := Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨by norm_num, Int.prime_three.neg.squarefree⟩)
  ne_one := by norm_num

instance isQuadDisc_neg_seven' : IsQuadDisc (-7) where
  fund := by
    rw [Int.isFundamentalDiscr_iff_squarefree]
    left
    refine ⟨by norm_num, ?_⟩
    exact (Int.prime_iff_natAbs_prime.2 (by norm_num : Nat.Prime ((7 : ℤ).natAbs))).neg.squarefree
  ne_one := by norm_num

instance : Fact ((-8 : ℤ) < 0) := ⟨by norm_num⟩
instance : Fact ((-3 : ℤ) < 0) := ⟨by norm_num⟩
instance : Fact ((-7 : ℤ) < 0) := ⟨by norm_num⟩

instance isPrincipalIdealRing_QField_neg_three' : IsPrincipalIdealRing (𝓞 (QField (-3))) := by
  refine RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt ?_
  rw [discr_eq, finrank_eq, nrComplexPlaces_of_neg (by norm_num)]
  have hπ := Real.pi_gt_three
  norm_num [Nat.factorial]
  nlinarith

instance isPrincipalIdealRing_QField_neg_eight' : IsPrincipalIdealRing (𝓞 (QField (-8))) := by
  refine RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt ?_
  rw [discr_eq, finrank_eq, nrComplexPlaces_of_neg (by norm_num)]
  have hπ := Real.pi_gt_d2
  norm_num [Nat.factorial]
  nlinarith

instance isPrincipalIdealRing_QField_neg_seven' : IsPrincipalIdealRing (𝓞 (QField (-7))) := by
  refine RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt ?_
  rw [discr_eq, finrank_eq, nrComplexPlaces_of_neg (by norm_num)]
  have hπ := Real.pi_gt_d2
  norm_num [Nat.factorial]
  nlinarith

private theorem kronZ_neg_three (d : ℕ) : kronZ (-3) (d : ZMod (-3 : ℤ).natAbs) = chi3 d := by
  rw [kronZ_natCast_of_one (by norm_num)]
  have h1 : ((-3 : ℤ).natAbs) = 3 := by norm_num
  rw [h1, jacobiSym.mod_left]
  have h2 : (d : ℤ) % ((3 : ℕ) : ℤ) = ((d % 3 : ℕ) : ℤ) := by push_cast; rfl
  rw [h2, chi3]
  have : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
  rcases this with h | h | h <;> simp [h] <;> norm_num

private theorem kronZ_neg_seven (d : ℕ) : kronZ (-7) (d : ZMod (-7 : ℤ).natAbs) = chi7 d := by
  rw [kronZ_natCast_of_one (by norm_num)]
  have h1 : ((-7 : ℤ).natAbs) = 7 := by norm_num
  rw [h1, jacobiSym.mod_left]
  have h2 : (d : ℤ) % ((7 : ℕ) : ℤ) = ((d % 7 : ℕ) : ℤ) := by push_cast; rfl
  rw [h2, chi7]
  have : d % 7 = 0 ∨ d % 7 = 1 ∨ d % 7 = 2 ∨ d % 7 = 3 ∨ d % 7 = 4 ∨ d % 7 = 5 ∨ d % 7 = 6 := by omega
  rcases this with h | h | h | h | h | h | h <;> simp [h] <;> norm_num

private theorem kronZ_neg_eight (d : ℕ) : kronZ (-8) (d : ZMod (-8 : ℤ).natAbs) = chiNeg8 d := by
  by_cases hd : Odd d
  · rw [kronZ_natCast_of_zero (by norm_num) hd]
    have h4 : ((-8 : ℤ) / 4) = -2 := by norm_num
    rw [h4, jacobiSym.mod_right _ hd]
    have h8 : (4 * (-2 : ℤ).natAbs) = 8 := by norm_num
    rw [h8]
    have : d % 8 = 1 ∨ d % 8 = 3 ∨ d % 8 = 5 ∨ d % 8 = 7 := by obtain ⟨k, hk⟩ := hd; omega
    rcases this with h | h | h | h <;> simp [chiNeg8, h] <;> norm_num
  · have hd' : d % 2 = 0 := by simpa [Nat.odd_iff] using hd
    have h8 : d % 8 ≠ 1 ∧ d % 8 ≠ 3 ∧ d % 8 ≠ 5 ∧ d % 8 ≠ 7 := by omega
    have hodd : ¬ Odd (((d : ℕ) : ZMod (-8 : ℤ).natAbs).val) := by
      rw [ZMod.val_natCast, Nat.odd_iff]
      have : ((-8 : ℤ).natAbs) = 8 := by norm_num
      rw [this]; omega
    rw [kronZ, if_neg (by norm_num), if_neg hodd]
    simp [chiNeg8, h8.1, h8.2.1, h8.2.2.1, h8.2.2.2]

/-- Dirichlet's count for a form of class number one, in the form used below. -/
private theorem card_of_classNumber_one {D : ℤ} [IsQuadDisc D] [Fact (D < 0)]
    (h1 : classNumber (QField D) = 1) (a b c : ℤ) (ha : 0 < a) (hd : b ^ 2 - 4 * a * c = D) {m : ℕ}
    (hm : m ≠ 0) :
    (Nat.card {p : ℤ × ℤ // a * p.1 ^ 2 + b * p.1 * p.2 + c * p.2 ^ 2 = m} : ℤ) =
      NumberField.Units.torsionOrder (QField D) * ∑ d ∈ m.divisors, kronZ D (d : ZMod D.natAbs) := by
  have hf : (BinQF.mk a b c).disc = D ∧ (BinQF.mk a b c).PosDef ∧ (BinQF.mk a b c).IsPrimitive :=
    (mem_primPosForm_iff IsQuadDisc.fund Fact.out _).2 ⟨by simp [BinQF.disc, hd], by simpa using ha⟩
  have := repNum_eq_of_classNumber_one h1 ⟨BinQF.mk a b c, hf⟩ hm
  rw [← this]
  simp only [repNum_mk_eq_card]

/-! ### Dirichlet's counts for the three forms -/

/-- **Dirichlet's count for $x^2 + 2y^2$** ($D = -8$, $h = 1$, $w = 2$): for $m \ge 1$,
$\#\{(x, y) \in \mathbb Z^2 : x^2 + 2y^2 = m\} = 2\sum_{d \mid m}\chi_{-8}(d)$. -/
@[kb "dirichlet1863" "§§ 89–93 (number of representations by the forms of a determinant) [unverified locator]"]
theorem card_x2_add_2y2 (m : ℕ) (hm : 1 ≤ m) :
    (Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 2 * p.2 ^ 2 = m} : ℤ) = 2 * ∑ d ∈ m.divisors, chiNeg8 d := by
  have h := card_of_classNumber_one (D := -8) (NumberField.classNumber_eq_one_iff.2 inferInstance) 1 0 2
    (by norm_num) (by norm_num) (m := m) (by omega)
  rw [torsionOrder_of_neg (by norm_num)] at h
  simp only [kronZ_neg_eight] at h
  rw [show Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 2 * p.2 ^ 2 = (m : ℤ)} =
      Nat.card {p : ℤ × ℤ // 1 * p.1 ^ 2 + 0 * p.1 * p.2 + 2 * p.2 ^ 2 = (m : ℤ)} from
    Nat.card_congr (Equiv.subtypeEquivRight fun p => by constructor <;> intro h <;> linarith), h]
  norm_num

/-- **Dirichlet's count for $x^2 + xy + y^2$** ($D = -3$, $h = 1$, $w = 6$): for $m \ge 1$,
$\#\{(x, y) \in \mathbb Z^2 : x^2 + xy + y^2 = m\} = 6\sum_{d \mid m}\bigl(\frac d3\bigr)$. -/
@[kb "dirichlet1863" "§§ 89–93 (number of representations by the forms of a determinant) [unverified locator]"]
theorem card_x2_add_xy_add_y2 (m : ℕ) (hm : 1 ≤ m) :
    (Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = m} : ℤ) = 6 * ∑ d ∈ m.divisors, chi3 d := by
  have h := card_of_classNumber_one (D := -3) (NumberField.classNumber_eq_one_iff.2 inferInstance) 1 1 1
    (by norm_num) (by norm_num) (m := m) (by omega)
  rw [torsionOrder_of_neg (by norm_num)] at h
  simp only [kronZ_neg_three] at h
  rw [show Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = (m : ℤ)} =
      Nat.card {p : ℤ × ℤ // 1 * p.1 ^ 2 + 1 * p.1 * p.2 + 1 * p.2 ^ 2 = (m : ℤ)} from
    Nat.card_congr (Equiv.subtypeEquivRight fun p => by constructor <;> intro h <;> linarith), h]
  norm_num

/-- **Dirichlet's count for $x^2 + xy + 2y^2$** ($D = -7$, $h = 1$, $w = 2$): for $m \ge 1$,
$\#\{(x, y) \in \mathbb Z^2 : x^2 + xy + 2y^2 = m\} = 2\sum_{d \mid m}\bigl(\frac d7\bigr)$. -/
@[kb "dirichlet1863" "§§ 89–93 (number of representations by the forms of a determinant) [unverified locator]"]
theorem card_x2_add_xy_add_2y2 (m : ℕ) (hm : 1 ≤ m) :
    (Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.1 * p.2 + 2 * p.2 ^ 2 = m} : ℤ) = 2 * ∑ d ∈ m.divisors, chi7 d := by
  have h := card_of_classNumber_one (D := -7) (NumberField.classNumber_eq_one_iff.2 inferInstance) 1 1 2
    (by norm_num) (by norm_num) (m := m) (by omega)
  rw [torsionOrder_of_neg (by norm_num)] at h
  simp only [kronZ_neg_seven] at h
  rw [show Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.1 * p.2 + 2 * p.2 ^ 2 = (m : ℤ)} =
      Nat.card {p : ℤ × ℤ // 1 * p.1 ^ 2 + 1 * p.1 * p.2 + 2 * p.2 ^ 2 = (m : ℤ)} from
    Nat.card_congr (Equiv.subtypeEquivRight fun p => by constructor <;> intro h <;> linarith), h]
  norm_num

end QuadFormsKB.Historical.BinaryForms
