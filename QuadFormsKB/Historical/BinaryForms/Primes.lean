/-
# Primes of the form $x^2 + 2y^2$, $x^2 + 3y^2$, $x^2 + 5y^2$, $x^2 + 7y^2$ (Fermat, Euler, Lagrange, Gauss)

**Library** `QuadFormsKB.Historical.BinaryForms` (historical library, not imported by `QuadFormsKB`).  Targets
:

* (Gauss, *Disquisitiones Arithmeticae*, Art. 182, II, 1801 p. 220, occurrence
  `gauss1801-disquisitiones:art182.9`), with the same statement in (Dickson, *History* II) and
  (Dickson, *History* III, with the converse): every prime $p \equiv 1, 3 \pmod 8$ is
  $x^2 + 2y^2$ in exactly one way with $x, y \ge 0$ (`prime_x2_add_2y2_existsUnique`); an odd prime of that form is
  $\equiv 1, 3 \pmod 8$ (`prime_mod_eight_of_x2_add_2y2`).
* (Gauss, Art. 182, III, 1801 p. 221, `gauss1801-disquisitiones:art182.12`) and 
  (Dickson, *History* III): every prime $p \equiv 1 \pmod 3$ is $x^2 + 3y^2$ in exactly one way with $x, y \ge 0$
  (`prime_x2_add_3y2_existsUnique`); a prime $p$ is $x^2 + 3y^2$ iff $p = 3$ or $p \equiv 1 \pmod 3$
  (`prime_x2_add_3y2_iff`).
* (Eisenstein, *Über die quadratische Zerfällung der Primzahlen*, 1848): a prime $q \ne 2, 7$ is $x^2 + 7y^2$ iff
  $q \equiv 1, 2, 4 \pmod 7$ (`prime_x2_add_7y2_iff`).
* (Gauss, Art. 182, end, 1801 p. 221, `gauss1801-disquisitiones:art182.13`) and 
  (Euler's conjecture of 1755, Dickson, *History* III): primes $\equiv 1, 9 \pmod{20}$ are $x^2 + 5y^2$, primes
  $\equiv 3, 7 \pmod{20}$ are $2x^2 + 2xy + 3y^2$; twice a prime $\equiv 1, 9$ is $2x^2 + 2xy + 3y^2$, twice a prime
  $\equiv 3, 7$ is $x^2 + 5y^2$ (`prime_x2_add_5y2`, `prime_2x2_add_2xy_add_3y2`, `two_mul_prime_2x2_add_2xy_add_3y2`,
  `two_mul_prime_x2_add_5y2`). **Partial:** the row's first sentence (every number having $-5$ as a quadratic residue
  is primitively represented by one of the two forms) is not formalized (loose end).

All **proved**, unconditional, from Dirichlet's formula (`Dirichlet.lean`): for an odd prime $p \nmid D$,
$r(p) = w(1 + \chi_D(p))$ summed over the classes of discriminant $D$; for $D = -20$ the two classes $x^2 + 5y^2$ and
$2x^2 + 2xy + 3y^2$ (every form of discriminant $-20$ reduces to one of them) are separated by their values
modulo $20$ and $40$.
-/
import QuadFormsKB.Historical.BinaryForms.Smith
import QuadFormsKB.Binary.SiegelBinaryChecks
import QuadFormsKB.Literature.ConwaySloane.NormedIdealsForms

namespace QuadFormsKB.Historical.BinaryForms

open QuadFormsKB QuadFormsKB.Binary
open QuadFormsKB.ConwaySloane.Binary (BinForm ProperEquiv IsReducedPos)
open QuadFormsKB.ConwaySloane (toBinQF properEquiv_iff_sLEquiv)

/-! ### Helper: uniqueness from a count of four -/

/-- If $x^2 + cy^2 = p$ has exactly $4$ integer solutions and none with $x = 0$ or $y = 0$ among the naturals,
then it has exactly one solution in $\mathbb N^2$ (the four sign changes of a solution are distinct). -/
private theorem existsUnique_of_card_four (c p : ℕ)
    (hpos : ∀ x y : ℕ, x ^ 2 + c * y ^ 2 = p → 0 < x ∧ 0 < y)
    (hcard : Nat.card {z : ℤ × ℤ // z.1 ^ 2 + (c : ℤ) * z.2 ^ 2 = p} = 4) :
    ∃! q : ℕ × ℕ, q.1 ^ 2 + c * q.2 ^ 2 = p := by
  have hfin : Finite {z : ℤ × ℤ // z.1 ^ 2 + (c : ℤ) * z.2 ^ 2 = p} :=
    Nat.finite_of_card_ne_zero (by omega)
  have hne : Nonempty {z : ℤ × ℤ // z.1 ^ 2 + (c : ℤ) * z.2 ^ 2 = p} :=
    (Nat.card_pos_iff.1 (by omega)).1
  let sg : Bool → ℤ := fun b => if b then 1 else -1
  let φ : {q : ℕ × ℕ // q.1 ^ 2 + c * q.2 ^ 2 = p} × (Bool × Bool) →
      {z : ℤ × ℤ // z.1 ^ 2 + (c : ℤ) * z.2 ^ 2 = p} :=
    fun x => ⟨(sg x.2.1 * x.1.1.1, sg x.2.2 * x.1.1.2), by
      have h : ((x.1.1.1 ^ 2 + c * x.1.1.2 ^ 2 : ℕ) : ℤ) = p := by exact_mod_cast x.1.2
      push_cast at h
      rcases x.2 with ⟨b1, b2⟩
      cases b1 <;> cases b2 <;> simp [sg] <;> linarith⟩
  have hinj : Function.Injective φ := by
    rintro ⟨⟨⟨a, b⟩, hq⟩, b1, b2⟩ ⟨⟨⟨a', b'⟩, hq'⟩, b1', b2'⟩ h
    obtain ⟨ha, hb⟩ := hpos a b hq
    obtain ⟨ha', hb'⟩ := hpos a' b' hq'
    have h1 := congrArg (fun z : {z : ℤ × ℤ // z.1 ^ 2 + (c : ℤ) * z.2 ^ 2 = p} => z.1.1) h
    have h2 := congrArg (fun z : {z : ℤ × ℤ // z.1 ^ 2 + (c : ℤ) * z.2 ^ 2 = p} => z.1.2) h
    simp only [φ, sg] at h1 h2
    cases b1 <;> cases b1' <;> cases b2 <;> cases b2' <;> simp at h1 h2 ⊢ <;> omega
  have hS : Finite {q : ℕ × ℕ // q.1 ^ 2 + c * q.2 ^ 2 = p} := by
    haveI : Finite ({q : ℕ × ℕ // q.1 ^ 2 + c * q.2 ^ 2 = p} × (Bool × Bool)) := Finite.of_injective φ hinj
    exact Finite.of_injective (fun q => (q, (true, true))) (fun a b h => by simpa using h)
  have hle := hcard ▸ Nat.card_le_card_of_injective φ hinj
  rw [Nat.card_prod] at hle
  have h4 : Nat.card (Bool × Bool) = 4 := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool)]; simp
  rw [h4] at hle
  obtain ⟨z⟩ := hne
  have hq0 : z.1.1.natAbs ^ 2 + c * z.1.2.natAbs ^ 2 = p := by
    have h := z.2
    zify
    rw [sq_abs, sq_abs]
    exact h
  have hpos' : 0 < Nat.card {q : ℕ × ℕ // q.1 ^ 2 + c * q.2 ^ 2 = p} :=
    Nat.card_pos_iff.2 ⟨⟨(z.1.1.natAbs, z.1.2.natAbs), hq0⟩, hS⟩
  have h1 : Nat.card {q : ℕ × ℕ // q.1 ^ 2 + c * q.2 ^ 2 = p} = 1 := by omega
  obtain ⟨hsub, ⟨⟨q, hq⟩⟩⟩ := Nat.card_eq_one_iff_unique.1 h1
  exact ⟨q, hq, fun q' hq' => congrArg Subtype.val (hsub.elim ⟨q', hq'⟩ ⟨q, hq⟩)⟩

/-! ### Helper: squares modulo small numbers -/

private theorem sq_mod_three (x : ℤ) : x ^ 2 % 3 = 0 ∨ x ^ 2 % 3 = 1 := by
  rcases (by omega : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2) with h | h | h <;>
    simp [pow_two, Int.mul_emod, h]

private theorem sq_mod_five (x : ℤ) : x ^ 2 % 5 = 0 ∨ x ^ 2 % 5 = 1 ∨ x ^ 2 % 5 = 4 := by
  rcases (by omega : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4) with h | h | h | h | h <;>
    simp [pow_two, Int.mul_emod, h]

private theorem sq_mod_seven (x : ℤ) : x ^ 2 % 7 = 0 ∨ x ^ 2 % 7 = 1 ∨ x ^ 2 % 7 = 2 ∨ x ^ 2 % 7 = 4 := by
  rcases (by omega : x % 7 = 0 ∨ x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨ x % 7 = 4 ∨ x % 7 = 5 ∨ x % 7 = 6) with
    h | h | h | h | h | h | h <;> simp [pow_two, Int.mul_emod, h]

private theorem sq_mod_eight (x : ℤ) : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  rcases (by omega : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨
      x % 8 = 7) with h | h | h | h | h | h | h | h <;> simp [pow_two, Int.mul_emod, h]

private theorem mod_eight_aux (x y : ℤ) (h : (x ^ 2 + 2 * y ^ 2) % 2 = 1) :
    (x ^ 2 + 2 * y ^ 2) % 8 = 1 ∨ (x ^ 2 + 2 * y ^ 2) % 8 = 3 := by
  have hx := sq_mod_eight x
  have hy := sq_mod_eight y
  omega

/-! ### Helper: representation numbers of `mk a b c` -/

private theorem repNum_mk_eq_zero (a b c : ℤ) (m : ℕ) (h : ∀ x y : ℤ, a * x ^ 2 + b * x * y + c * y ^ 2 ≠ m) :
    Siegel.repNum (BinQF.mk a b c) m = 0 := by
  rw [repNum_mk_eq_card]
  haveI : IsEmpty {p : ℤ × ℤ // a * p.1 ^ 2 + b * p.1 * p.2 + c * p.2 ^ 2 = m} :=
    ⟨fun p => h p.1.1 p.1.2 p.2⟩
  exact Nat.card_of_isEmpty

private theorem exists_of_repNum_ne_zero (a b c : ℤ) (m : ℕ) (h : Siegel.repNum (BinQF.mk a b c) m ≠ 0) :
    ∃ x y : ℤ, a * x ^ 2 + b * x * y + c * y ^ 2 = m := by
  rw [repNum_mk_eq_card] at h
  obtain ⟨⟨⟨x, y⟩, hxy⟩, -⟩ := Nat.card_ne_zero.1 h
  exact ⟨x, y, hxy⟩

/-! ### $x^2 + 2y^2$ -/

/-- **Fermat's theorem for $x^2 + 2y^2$** (;
Gauss, *D.A.* Art. 182, II; first proved by Lagrange, 1775): every prime $p \equiv 1, 3 \pmod 8$ is $x^2 + 2y^2$ with
$x, y \ge 0$, in exactly one way. -/
@[kb "gauss1801" "Art. 182, II, p. 220 (occurrence gauss1801-disquisitiones:art182.9)"]
theorem prime_x2_add_2y2_existsUnique (p : ℕ) (hp : p.Prime) (h : p % 8 = 1 ∨ p % 8 = 3) :
    ∃! q : ℕ × ℕ, q.1 ^ 2 + 2 * q.2 ^ 2 = p := by
  have hp1 := hp.one_lt
  refine existsUnique_of_card_four 2 p ?_ ?_
  · intro x y hxy
    refine ⟨Nat.pos_of_ne_zero ?_, Nat.pos_of_ne_zero ?_⟩
    · rintro rfl
      simp at hxy
      omega
    · rintro rfl
      have := (Nat.Prime.pow_eq_iff hp).1 (by simpa using hxy)
      omega
  · have h4 := card_x2_add_2y2 p hp.pos
    rw [hp.divisors, Finset.sum_pair (by omega : 1 ≠ p)] at h4
    have e1 : chiNeg8 1 = 1 := by decide
    have e2 : chiNeg8 p = 1 := by unfold chiNeg8; rw [if_pos h]
    rw [e1, e2] at h4
    have h5 : (Nat.card {z : ℤ × ℤ // z.1 ^ 2 + 2 * z.2 ^ 2 = (p : ℤ)} : ℤ) = 4 := by linarith
    simp only [Nat.cast_ofNat]
    exact_mod_cast h5

/-- **The converse**: an odd prime $p = x^2 + 2y^2$ is $\equiv 1, 3 \pmod 8$. -/
@[kb "dickson1923" "[unverified locator]"]
theorem prime_mod_eight_of_x2_add_2y2 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (x y : ℤ)
    (h : x ^ 2 + 2 * y ^ 2 = p) : p % 8 = 1 ∨ p % 8 = 3 := by
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have key := mod_eight_aux x y (by rw [h]; omega)
  rw [h] at key
  omega

/-! ### $x^2 + 3y^2$ -/

/-- **Fermat's theorem for $x^2 + 3y^2$** (Gauss, *D.A.* Art. 182, III; first proved by
Euler): every prime $p \equiv 1 \pmod 3$ is $x^2 + 3y^2$ with $x, y \ge 0$, in exactly one way. -/
@[kb "gauss1801" "Art. 182, III, p. 221 (occurrence gauss1801-disquisitiones:art182.12)"]
theorem prime_x2_add_3y2_existsUnique (p : ℕ) (hp : p.Prime) (h : p % 3 = 1) :
    ∃! q : ℕ × ℕ, q.1 ^ 2 + 3 * q.2 ^ 2 = p := by
  have hp1 := hp.one_lt
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by rintro rfl; omega)
  refine existsUnique_of_card_four 3 p ?_ ?_
  · intro x y hxy
    refine ⟨Nat.pos_of_ne_zero ?_, Nat.pos_of_ne_zero ?_⟩
    · rintro rfl
      simp at hxy
      omega
    · rintro rfl
      have := (Nat.Prime.pow_eq_iff hp).1 (by simpa using hxy)
      omega
  · have h4 := card_x2_add_3y2 p hp.pos
    rw [hp.divisors, Finset.sum_pair (by omega : 1 ≠ p)] at h4
    have h44 : ¬ 4 ∣ p := by omega
    rw [if_neg h44] at h4
    have e1 : chi3 1 = 1 := by decide
    have e2 : chi3 p = 1 := by unfold chi3; rw [if_pos h]
    rw [e1, e2] at h4
    have h5 : (Nat.card {z : ℤ × ℤ // z.1 ^ 2 + 3 * z.2 ^ 2 = (p : ℤ)} : ℤ) = 4 := by linarith
    simp only [Nat.cast_ofNat]
    exact_mod_cast h5

/-- **Primes of the form $x^2 + 3y^2$** (Dickson, *History* III): a prime $p$ is
$x^2 + 3y^2$ ($x, y \in \mathbb Z$) iff $p = 3$ or $p \equiv 1 \pmod 3$. -/
@[kb "dickson1923" "[unverified locator]"]
theorem prime_x2_add_3y2_iff (p : ℕ) (hp : p.Prime) :
    (∃ x y : ℤ, x ^ 2 + 3 * y ^ 2 = p) ↔ p = 3 ∨ p % 3 = 1 := by
  constructor
  · rintro ⟨x, y, h⟩
    have hx := sq_mod_three x
    have hmod : (p : ℤ) % 3 = x ^ 2 % 3 := by omega
    by_cases h3 : p % 3 = 0
    · left
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (by omega)
      omega
    · right
      omega
  · rintro (rfl | h)
    · exact ⟨0, 1, by norm_num⟩
    · obtain ⟨q, hq, -⟩ := prime_x2_add_3y2_existsUnique p hp h
      exact ⟨q.1, q.2, by exact_mod_cast hq⟩

/-! ### $x^2 + 7y^2$ -/

/-- **Primes of the form $x^2 + 7y^2$** (Eisenstein 1848): a prime $q \ne 2, 7$ is
$x^2 + 7y^2$ ($x, y \in \mathbb Z$) iff $q \equiv 1, 2, 4 \pmod 7$, i.e. iff $q$ is a quadratic residue modulo $7$. -/
@[kb "eisenstein1848" "[unverified locator]"]
theorem prime_x2_add_7y2_iff (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hq7 : q ≠ 7) :
    (∃ x y : ℤ, x ^ 2 + 7 * y ^ 2 = q) ↔ q % 7 = 1 ∨ q % 7 = 2 ∨ q % 7 = 4 := by
  have hq1 := hq.one_lt
  have hn7 : q % 7 ≠ 0 := fun h0 =>
    hq7 ((Nat.prime_dvd_prime_iff_eq Nat.prime_seven hq).1 (by omega)).symm
  have hodd : Odd q := hq.eq_two_or_odd'.resolve_left hq2
  constructor
  · rintro ⟨x, y, h⟩
    have hx := sq_mod_seven x
    omega
  · intro h
    have h7 := smith_x2_add_7y2_odd q hodd
    rw [hq.divisors] at h7
    simp only [Finset.card_filter, Finset.sum_pair (show 1 ≠ q by omega)] at h7
    have hne : Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 7 * p.2 ^ 2 = (q : ℤ)} ≠ 0 := by
      intro h0
      rw [h0] at h7
      rcases h with h | h | h <;> simp [h] at h7
    obtain ⟨⟨⟨x, y⟩, hxy⟩, -⟩ := Nat.card_ne_zero.1 hne
    exact ⟨x, y, hxy⟩

/-! ### Discriminant $-20$: $x^2 + 5y^2$ and $2x^2 + 2xy + 3y^2$ -/

/-- **The doubled form** $(2a)^{b}(2c)$ of $f = ax^2 + bxy + cy^2$ (Conway–Sloane's convention; copied from the
mass-formula files, which are not importable here). -/
private def dblForm (f : BinQF) : BinForm := ⟨2 * f.a, f.b, 2 * f.c⟩

private theorem sLEquiv_iff_properEquiv_dblForm (f g : BinQF) :
    SLEquiv f g ↔ ProperEquiv (dblForm f) (dblForm g) := by
  rw [properEquiv_iff_sLEquiv, sLEquiv_iff, sLEquiv_iff]
  constructor
  · rintro ⟨p, q, r, s, hd, rfl⟩
    refine ⟨p, q, r, s, hd, BinQF.ext_abc ?_ ?_ ?_⟩ <;> simp [dblForm, toBinQF, BinQF.subst] <;> ring
  · rintro ⟨p, q, r, s, hd, h⟩
    have ha := congrArg BinQF.a h
    have hb := congrArg BinQF.b h
    have hc := congrArg BinQF.c h
    simp [dblForm, toBinQF, BinQF.subst] at ha hb hc
    refine ⟨p, q, r, s, hd, BinQF.ext_abc ?_ ?_ ?_⟩ <;> simp [BinQF.subst] <;> linarith

/-- **Existence of a reduced form** (Gauss; copied from the mass-formula files). -/
private theorem exists_sLEquiv_reduced (f : BinQF) (ha : 0 < f.a) (hd : f.disc < 0) :
    ∃ g : BinQF, SLEquiv f g ∧ IsReducedPos (2 * g.a) g.b (2 * g.c) := by
  have hdet : 0 < (dblForm f).det := by
    simp only [BinQF.disc] at hd
    simp only [dblForm, QuadFormsKB.ConwaySloane.Binary.BinForm.det]
    linarith
  obtain ⟨g', e, hg'⟩ :=
    QuadFormsKB.ConwaySloane.Binary.exists_reduced_pos (dblForm f) (by simp [dblForm]; omega) hdet
  rw [properEquiv_iff_sLEquiv, sLEquiv_iff] at e
  obtain ⟨p, q, r, s, hps, h⟩ := e
  refine ⟨BinQF.subst p q r s f, (sLEquiv_iff _ _).2 ⟨p, q, r, s, hps, rfl⟩, ?_⟩
  have ha' := congrArg BinQF.a h
  have hb' := congrArg BinQF.b h
  have hc' := congrArg BinQF.c h
  simp [dblForm, toBinQF, BinQF.subst] at ha' hb' hc'
  have e1 : 2 * (BinQF.subst p q r s f).a = g'.a := by simp [BinQF.subst]; linarith
  have e2 : (BinQF.subst p q r s f).b = g'.b := by simp [BinQF.subst]; linarith
  have e3 : 2 * (BinQF.subst p q r s f).c = g'.c := by simp [BinQF.subst]; linarith
  rw [e1, e2, e3]
  exact hg'

/-- The reduced forms of discriminant $-20$ are $x^2 + 5y^2$ and $2x^2 + 2xy + 3y^2$. -/
private theorem reduced_neg_twenty (a b c : ℤ) (hr : IsReducedPos (2 * a) b (2 * c)) (hd : b ^ 2 - 4 * a * c = -20) :
    (a = 1 ∧ b = 0 ∧ c = 5) ∨ (a = 2 ∧ b = 2 ∧ c = 3) := by
  obtain ⟨h1, h2, h3, h4⟩ := hr
  have ha : a ≤ 2 := by nlinarith
  have ha0 : 0 < a := by omega
  have hb1 : -a < b := by omega
  have hb2 : b ≤ a := by omega
  interval_cases a <;> interval_cases b <;> omega

private theorem mem_prim_one_zero_five :
    (BinQF.mk 1 0 5).disc = -20 ∧ (BinQF.mk 1 0 5).PosDef ∧ (BinQF.mk 1 0 5).IsPrimitive :=
  (mem_primPosForm_iff (D := -20) IsQuadDisc.fund (by norm_num) _).2 ⟨by simp [BinQF.disc], by simp⟩

private theorem mem_prim_two_two_three :
    (BinQF.mk 2 2 3).disc = -20 ∧ (BinQF.mk 2 2 3).PosDef ∧ (BinQF.mk 2 2 3).IsPrimitive :=
  (mem_primPosForm_iff (D := -20) IsQuadDisc.fund (by norm_num) _).2 ⟨by simp [BinQF.disc], by simp⟩

/-- $x^2 + 5y^2$ as a class of discriminant $-20$. -/
private def F20 : PrimPosForm (-20) := ⟨BinQF.mk 1 0 5, mem_prim_one_zero_five⟩

/-- $2x^2 + 2xy + 3y^2$ as a class of discriminant $-20$. -/
private def G20 : PrimPosForm (-20) := ⟨BinQF.mk 2 2 3, mem_prim_two_two_three⟩

/-- **Every class of discriminant $-20$ is that of $x^2 + 5y^2$ or of $2x^2 + 2xy + 3y^2$.** -/
private theorem class_cases (c : Quotient (slSetoid (-20))) :
    c = Quotient.mk _ F20 ∨ c = Quotient.mk _ G20 := by
  induction c using Quotient.inductionOn with
  | h f =>
    obtain ⟨g, hfg, hg⟩ := exists_sLEquiv_reduced f.1 f.a_pos (by rw [f.2.1]; norm_num)
    have hdg : g.disc = -20 := by
      obtain ⟨p, q, r, s, hps, rfl⟩ := (sLEquiv_iff _ _).1 hfg
      rw [BinQF.disc_subst_of_det _ _ _ _ _ (by rw [hps]; norm_num), f.2.1]
    have hd : g.b ^ 2 - 4 * g.a * g.c = -20 := by rw [← hdg, BinQF.disc]
    rcases reduced_neg_twenty g.a g.b g.c hg hd with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
    · left
      have hgf : g = BinQF.mk 1 0 5 := BinQF.ext_abc (by simpa using ha) (by simpa using hb) (by simpa using hc)
      exact Quotient.sound (show SLEquiv f.1 (BinQF.mk 1 0 5) by rw [← hgf]; exact hfg)
    · right
      have hgf : g = BinQF.mk 2 2 3 := BinQF.ext_abc (by simpa using ha) (by simpa using hb) (by simpa using hc)
      exact Quotient.sound (show SLEquiv f.1 (BinQF.mk 2 2 3) by rw [← hgf]; exact hfg)

/-- The two classes are distinct: $x^2 + 5y^2$ represents $1$, $2x^2 + 2xy + 3y^2$ does not. -/
private theorem class_ne : Quotient.mk (slSetoid (-20)) F20 ≠ Quotient.mk (slSetoid (-20)) G20 := by
  intro h
  have h' : SLEquiv (BinQF.mk 1 0 5) (BinQF.mk 2 2 3) := Quotient.exact h
  have h1 := Siegel.repNum_eq_of_intEquiv (SLEquiv.intEquiv h') 1
  have hg : Siegel.repNum (BinQF.mk 2 2 3) ((1 : ℕ) : ℤ) = 0 := by
    refine repNum_mk_eq_zero 2 2 3 1 fun x y hxy => ?_
    have hy : y ^ 2 < 1 := by push_cast at hxy; nlinarith [sq_nonneg (2 * x + y), sq_nonneg y]
    have hy0 : y = 0 := by
      have : -1 < y := by nlinarith
      have : y < 1 := by nlinarith
      omega
    subst hy0
    push_cast at hxy
    omega
  have hf : Siegel.repNum (BinQF.mk 1 0 5) ((1 : ℕ) : ℤ) ≠ 0 := by
    rw [repNum_mk_eq_card]
    have hfin : ({z : ℤ × ℤ | 1 * z.1 ^ 2 + 0 * z.1 * z.2 + 5 * z.2 ^ 2 = ((1 : ℕ) : ℤ)}).Finite :=
      ((Set.finite_Icc (-1 : ℤ) 1).prod (Set.finite_Icc (-1 : ℤ) 1)).subset fun z hz => by
        simp only [Set.mem_setOf_eq] at hz
        simp only [Set.mem_prod, Set.mem_Icc]
        push_cast at hz
        have h1 := Int.le_self_sq z.1
        have h2 := Int.le_self_sq (-z.1)
        have h3 := Int.le_self_sq z.2
        have h4 := Int.le_self_sq (-z.2)
        rw [neg_sq] at h2 h4
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [sq_nonneg z.1, sq_nonneg z.2]
    haveI := hfin.to_subtype
    refine Nat.card_ne_zero.2 ⟨⟨⟨(1, 0), by norm_num⟩⟩, this⟩
  exact hf (h1.trans hg)

/-- **Dirichlet's formula for $D = -20$:** $r_{x^2+5y^2}(m) + r_{2x^2+2xy+3y^2}(m) = 2\sum_{d \mid m}\chi_{-20}(d)$. -/
private theorem rep20 (m : ℕ) (hm : m ≠ 0) :
    (Siegel.repNum (BinQF.mk 1 0 5) m : ℤ) + Siegel.repNum (BinQF.mk 2 2 3) m =
      2 * ∑ d ∈ m.divisors, kronZ (-20) (d : ZMod (-20 : ℤ).natAbs) := by
  classical
  have h := dirichlet_sum_repNum_int (D := -20) hm
  have huniv : (Finset.univ : Finset (Quotient (slSetoid (-20)))) =
      ({Quotient.mk (slSetoid (-20)) F20, Quotient.mk (slSetoid (-20)) G20} : Finset (Quotient (slSetoid (-20)))) := by
    ext c
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact class_cases c
  rw [huniv, Finset.sum_pair class_ne, torsionOrder_of_neg (by norm_num)] at h
  have e1 : slClassRepNum m (Quotient.mk (slSetoid (-20)) F20) = Siegel.repNum (BinQF.mk 1 0 5) m := rfl
  have e2 : slClassRepNum m (Quotient.mk (slSetoid (-20)) G20) = Siegel.repNum (BinQF.mk 2 2 3) m := rfl
  rw [e1, e2] at h
  norm_num at h
  exact h

private theorem kronZ_neg_twenty_odd (d : ℕ) (hd : d % 2 = 1) :
    kronZ (-20) (d : ZMod (-20 : ℤ).natAbs) = jacobiSym (-5) d := by
  rw [kronZ_natCast_of_zero (by norm_num) (Nat.odd_iff.2 hd)]
  norm_num

private theorem kronZ_neg_twenty_even (d : ℕ) (hd : d % 2 = 0) :
    kronZ (-20) (d : ZMod (-20 : ℤ).natAbs) = 0 := by
  have hodd : ¬ Odd ((d : ZMod (-20 : ℤ).natAbs).val) := by
    rw [ZMod.val_natCast, Nat.odd_iff]
    have : ((-20 : ℤ).natAbs) = 20 := by norm_num
    rw [this]; omega
  rw [kronZ, if_neg (by norm_num), if_neg hodd]

private theorem jacobi_neg_five (d : ℕ) (h : d % 20 = 1 ∨ d % 20 = 3 ∨ d % 20 = 7 ∨ d % 20 = 9) :
    jacobiSym (-5) d = 1 := by
  have hodd : Odd d := Nat.odd_iff.2 (by omega)
  rw [jacobiSym.mod_right _ hodd]
  have : 4 * (-5 : ℤ).natAbs = 20 := by norm_num
  rw [this]
  rcases h with h | h | h | h <;> rw [h] <;> norm_num

private theorem kronZ_one_neg_twenty : kronZ (-20) ((1 : ℕ) : ZMod (-20 : ℤ).natAbs) = 1 := by
  rw [Nat.cast_one]; exact kronZ_one

/-- For a prime $p \equiv 1, 3, 7, 9 \pmod{20}$: $r_f(p) + r_g(p) = 4$. -/
private theorem rep20_prime (p : ℕ) (hp : p.Prime)
    (h : p % 20 = 1 ∨ p % 20 = 3 ∨ p % 20 = 7 ∨ p % 20 = 9) :
    (Siegel.repNum (BinQF.mk 1 0 5) p : ℤ) + Siegel.repNum (BinQF.mk 2 2 3) p = 4 := by
  have hp1 := hp.one_lt
  rw [rep20 p hp.ne_zero, hp.divisors, Finset.sum_pair (by omega : 1 ≠ p),
    kronZ_one_neg_twenty, kronZ_neg_twenty_odd p (by omega), jacobi_neg_five p h]
  norm_num

/-- For a prime $p \equiv 1, 3, 7, 9 \pmod{20}$: $r_f(2p) + r_g(2p) = 4$. -/
private theorem rep20_two_mul_prime (p : ℕ) (hp : p.Prime)
    (h : p % 20 = 1 ∨ p % 20 = 3 ∨ p % 20 = 7 ∨ p % 20 = 9) :
    (Siegel.repNum (BinQF.mk 1 0 5) ((2 * p : ℕ) : ℤ) : ℤ) + Siegel.repNum (BinQF.mk 2 2 3) ((2 * p : ℕ) : ℤ) = 4 := by
  have hp1 := hp.one_lt
  have hd : (2 * p).divisors = {1, 2, p, 2 * p} := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hd, -⟩
      obtain ⟨a, b, ha, hb, rfl⟩ := Nat.dvd_mul.1 hd
      rcases (Nat.dvd_prime Nat.prime_two).1 ha with rfl | rfl <;>
        rcases (Nat.dvd_prime hp).1 hb with rfl | rfl <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      · simp; omega
      · simp; omega
      · exact ⟨Dvd.intro_left 2 rfl, by omega⟩
      · exact ⟨dvd_refl _, by omega⟩
  rw [rep20 (2 * p) (by omega), hd, Finset.sum_insert (by simp <;> omega), Finset.sum_insert (by simp <;> omega),
    Finset.sum_pair (by omega), kronZ_one_neg_twenty, kronZ_neg_twenty_odd p (by omega), jacobi_neg_five p h,
    kronZ_neg_twenty_even 2 (by norm_num), kronZ_neg_twenty_even (2 * p) (by omega)]
  norm_num

private theorem repNum_f20_zero (m : ℕ) (h : m % 5 = 2 ∨ m % 5 = 3) : Siegel.repNum (BinQF.mk 1 0 5) m = 0 := by
  refine repNum_mk_eq_zero 1 0 5 m fun x y hxy => ?_
  have := sq_mod_five x
  omega

private theorem repNum_g20_zero (m : ℕ) (h : m % 5 = 1 ∨ m % 5 = 4) : Siegel.repNum (BinQF.mk 2 2 3) m = 0 := by
  refine repNum_mk_eq_zero 2 2 3 m fun x y hxy => ?_
  have h1 := sq_mod_five (2 * x + y)
  have h2 : 2 * (2 * x ^ 2 + 2 * x * y + 3 * y ^ 2) = (2 * x + y) ^ 2 + 5 * y ^ 2 := by ring
  omega

/-- **Primes $\equiv 1, 9 \pmod{20}$ are $x^2 + 5y^2$** (Gauss,
*D.A.* Art. 182, end; conjectured by Euler, 1755). -/
@[kb "gauss1801" "Art. 182 (end), p. 221 (occurrence gauss1801-disquisitiones:art182.13)"]
theorem prime_x2_add_5y2 (p : ℕ) (hp : p.Prime) (h : p % 20 = 1 ∨ p % 20 = 9) :
    ∃ x y : ℤ, x ^ 2 + 5 * y ^ 2 = p := by
  have h4 := rep20_prime p hp (by omega)
  rw [repNum_g20_zero p (by omega)] at h4
  obtain ⟨x, y, hxy⟩ := exists_of_repNum_ne_zero 1 0 5 p (by omega)
  exact ⟨x, y, by linear_combination hxy⟩

/-- **Primes $\equiv 3, 7 \pmod{20}$ are $2x^2 + 2xy + 3y^2$** (Gauss, *D.A.* Art. 182,
end). -/
@[kb "gauss1801" "Art. 182 (end), p. 221 (occurrence gauss1801-disquisitiones:art182.13)"]
theorem prime_2x2_add_2xy_add_3y2 (p : ℕ) (hp : p.Prime) (h : p % 20 = 3 ∨ p % 20 = 7) :
    ∃ x y : ℤ, 2 * x ^ 2 + 2 * x * y + 3 * y ^ 2 = p := by
  have h4 := rep20_prime p hp (by omega)
  rw [repNum_f20_zero p (by omega)] at h4
  exact exists_of_repNum_ne_zero 2 2 3 p (by omega)

/-- **Twice a prime $\equiv 1, 9 \pmod{20}$ is $2x^2 + 2xy + 3y^2$**. -/
@[kb "gauss1801" "Art. 182 (end), p. 221 (occurrence gauss1801-disquisitiones:art182.13)"]
theorem two_mul_prime_2x2_add_2xy_add_3y2 (p : ℕ) (hp : p.Prime) (h : p % 20 = 1 ∨ p % 20 = 9) :
    ∃ x y : ℤ, 2 * x ^ 2 + 2 * x * y + 3 * y ^ 2 = 2 * p := by
  have h4 := rep20_two_mul_prime p hp (by omega)
  rw [repNum_f20_zero (2 * p) (by omega)] at h4
  obtain ⟨x, y, hxy⟩ := exists_of_repNum_ne_zero 2 2 3 (2 * p) (by omega)
  exact ⟨x, y, by push_cast at hxy; linear_combination hxy⟩

/-- **Twice a prime $\equiv 3, 7 \pmod{20}$ is $x^2 + 5y^2$** (: Euler's
$2p = x^2 + 5y^2$). -/
@[kb "gauss1801" "Art. 182 (end), p. 221 (occurrence gauss1801-disquisitiones:art182.13)"]
theorem two_mul_prime_x2_add_5y2 (p : ℕ) (hp : p.Prime) (h : p % 20 = 3 ∨ p % 20 = 7) :
    ∃ x y : ℤ, x ^ 2 + 5 * y ^ 2 = 2 * p := by
  have h4 := rep20_two_mul_prime p hp (by omega)
  rw [repNum_g20_zero (2 * p) (by omega)] at h4
  obtain ⟨x, y, hxy⟩ := exists_of_repNum_ne_zero 1 0 5 (2 * p) (by omega)
  exact ⟨x, y, by push_cast at hxy; linear_combination hxy⟩

/-- **Numbers with $-5$ a quadratic residue** (first sentence; Gauss, *D.A.* Art. 182,
end): if $N \ge 1$ and $-5$ is a square modulo $N$ ($N \mid b^2 + 5$ for some $b$), then $N$ is primitively represented
($\gcd(x, y) = 1$) by $x^2 + 5y^2$ or by $2x^2 + 2xy + 3y^2$. **Proved** (the form $Nx^2 + 2bxy + \frac{b^2+5}{N}y^2$ of
discriminant $-20$ represents $N$ primitively at $(1, 0)$ and is properly equivalent to one of the two reduced
forms). -/
@[kb "gauss1801" "Art. 182 (end), p. 221 (occurrence gauss1801-disquisitiones:art182.13)"]
theorem primitive_rep_of_neg_five_sq (N : ℕ) (hN : 1 ≤ N) (h : ∃ b : ℤ, (N : ℤ) ∣ b ^ 2 + 5) :
    ∃ x y : ℤ, IsCoprime x y ∧ (x ^ 2 + 5 * y ^ 2 = N ∨ 2 * x ^ 2 + 2 * x * y + 3 * y ^ 2 = N) := by
  obtain ⟨b, k, hk⟩ := h
  have hN0 : (0 : ℤ) < N := by exact_mod_cast hN
  have hdisc : (BinQF.mk (N : ℤ) (2 * b) k).disc = -20 := by
    simp only [BinQF.disc, BinQF.b_mk, BinQF.a_mk, BinQF.c_mk]; linarith
  obtain ⟨g, hfg, hg⟩ := exists_sLEquiv_reduced (BinQF.mk (N : ℤ) (2 * b) k)
    (by simpa using hN0) (by rw [hdisc]; norm_num)
  obtain ⟨p, q, r, s, hps, rfl⟩ := (sLEquiv_iff _ _).1 hfg
  have hdg := BinQF.disc_subst_of_det p q r s (BinQF.mk (N : ℤ) (2 * b) k) (by rw [hps]; norm_num)
  rw [hdisc] at hdg
  have hd : (BinQF.subst p q r s (BinQF.mk (N : ℤ) (2 * b) k)).b ^ 2 -
      4 * (BinQF.subst p q r s (BinQF.mk (N : ℤ) (2 * b) k)).a *
        (BinQF.subst p q r s (BinQF.mk (N : ℤ) (2 * b) k)).c = -20 := by rw [← hdg, BinQF.disc]
  have hev := BinQF.eval_subst p q r s (BinQF.mk (N : ℤ) (2 * b) k) s (-r)
  have e1 : p * s + q * -r = 1 := by linarith
  have e2 : r * s + s * -r = 0 := by ring
  rw [e1, e2, BinQF.eval_eq] at hev
  have hcop : IsCoprime s (-r) := ⟨p, q, by linarith⟩
  refine ⟨s, -r, hcop, ?_⟩
  rcases reduced_neg_twenty _ _ _ hg hd with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
  · left
    rw [BinQF.eval_eq, ha, hb, hc] at hev
    simp only [BinQF.a_mk, BinQF.b_mk, BinQF.c_mk] at hev
    linarith
  · right
    rw [BinQF.eval_eq, ha, hb, hc] at hev
    simp only [BinQF.a_mk, BinQF.b_mk, BinQF.c_mk] at hev
    linarith

end QuadFormsKB.Historical.BinaryForms
