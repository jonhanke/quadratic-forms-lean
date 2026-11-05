/-
# Cassels, Chapter 11, Examples 1 and 2 (pp. 251–252): one class by spinor genera; an explicit equivalence

**Layer:** integer-valued ternary forms `f : QuadForm ℤ 3` ($f = $ `QuadForm.diag ![1, 5, -7]` etc.; variables
$x_0, x_1, x_2$), Siegel's genus `Siegel.SameGenus` (equivalence over every $\mathbb Z_p$ and over $\mathbb R$), integral
equivalence `IntEquiv` and proper integral equivalence `ProperIntEquiv` (`Ch9Sec1.lean`), primitive representations
over $\mathbb Z$ (greatest common divisor of the coordinates is $1$) and over $\mathbb Z_p$ (some coordinate is a unit).

**Proves**
* Example 1 (p. 251), first part (`ex1_properIntEquiv_of_sameGenus`): the genus of $x^2 + 5y^2 - 7z^2$ contains
  exactly one proper equivalence class. *Method (Cassels'):* the determinant is $d = -35$, so by Chapter 11,
  Theorem 1.5 (`Ch11Thm13.lean`, in the form `intEquiv_of_sameGenus_of_ch11` of `Ch9Examples.lean`) every form of the
  genus is equivalent to $f$ (the genus is one spinor genus and an indefinite spinor genus is one class, Theorem 1.4);
  $f$ has the improper automorph $x_0 \mapsto -x_0$, so equivalence is proper equivalence.
* Example 1 (p. 251), second part (`ex1_primRep_iff`): *necessary and sufficient conditions for an integer $a$ to be
  primitively represented by $f$.* They are
  $$a \equiv 1, 2, 5, 6, 7 \pmod 8 \quad\text{and}\quad \bigl(5 \nmid a \ \text{ or } \ a \equiv 5, 20 \pmod{25}\bigr),$$
  i.e. $a \not\equiv 0, 3, 4 \pmod 8$, and if $5 \mid a$ then $a/5 \equiv \pm 1 \pmod 5$. The conditions are
  *reconstructed* by us (Cassels does not print the answer) and were checked numerically against all $|a| \le 40$.
  Necessity is by congruences; sufficiency by the Corollary to Chapter 9, Theorem 5.1 (`exists_primRep_of_one_class`):
  with one class it suffices to find primitive $p$-adic representations for $p \mid 2d$, i.e. $p = 2, 5, 7$.
* Example 2 (p. 251) (`ex2_properIntEquiv`): the forms $x^2 - 3y^2 - 2yz - 23z^2$ and $x^2 - 7y^2 - 6yz - 11z^2$ are
  (properly) integrally equivalent, by an explicit matrix found by computer search (Chapter 9, Example 3 shows that
  the binary parts $3y^2 + 2yz + 23z^2$ and $7y^2 + 6yz + 11z^2$ are in one genus but not equivalent, which is the
  point of the example). *Reconstruction:* the coefficient of $z^2$ in the first form is garbled in the scan ("232?");
  $-23$ is forced by equality of the determinants.
-/
import QuadFormsKB.Literature.Cassels.Ch9Examples
import QuadFormsKB.Literature.Cassels.Ch9Sec5
import QuadFormsKB.Literature.Cassels.Ch9Sec5Squares
import QuadFormsKB.Literature.Cassels.Ch9Sec8Int

open Matrix NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

/-! ### Example 1: the form $x^2 + 5y^2 - 7z^2$ -/

/-- The form $x_0^2 + 5x_1^2 - 7x_2^2$ of Cassels' Example 1 (Ch. 11, p. 251). -/
def ch11Ex1Form : QuadForm ℤ 3 := QuadForm.diag ![1, 5, -7]

/-- Helper: evaluation of $x_0^2 + 5x_1^2 - 7x_2^2$ over any commutative ring. -/
theorem eval_map_ch11Ex1Form {R : Type*} [CommRing R] (x : Fin 3 → R) :
    (ch11Ex1Form.map (Int.castRingHom R)).eval x = x 0 ^ 2 + 5 * x 1 ^ 2 - 7 * x 2 ^ 2 := by
  simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_three, ch11Ex1Form, QuadForm.diag, QuadForm.map,
    Matrix.diagonal_apply]
  ring

/-- Helper: evaluation of $x_0^2 + 5x_1^2 - 7x_2^2$ over $\mathbb Z$. -/
theorem eval_ch11Ex1Form (x : Fin 3 → ℤ) : ch11Ex1Form.eval x = x 0 ^ 2 + 5 * x 1 ^ 2 - 7 * x 2 ^ 2 := by
  have h := eval_map_ch11Ex1Form (R := ℤ) x
  simpa [QuadForm.map] using h

/-- Helper: evaluation of $x_0^2 + 5x_1^2 - 7x_2^2$ over a field extension of $\mathbb R$-type coordinates. -/
theorem evalIn_ch11Ex1Form {K : Type*} [Field K] [Algebra ℤ K] (x : Fin 3 → K) :
    ch11Ex1Form.evalIn K x = x 0 ^ 2 + 5 * x 1 ^ 2 - 7 * x 2 ^ 2 := by
  simp [QuadForm.evalIn, Fin.sum_univ_three, ch11Ex1Form, QuadForm.diag, Matrix.diagonal_apply]
  ring

/-- Helper: the Hessian determinant of $x_0^2 + 5x_1^2 - 7x_2^2$ is $-280 = 8 \cdot (-35)$. -/
theorem hessian_det_ch11Ex1Form : ch11Ex1Form.hessian.det = -280 := by
  rw [ch11Ex1Form, hessian_diag, det_diagonal, Fin.prod_univ_three]
  simp

/-- Helper: $f$ is indefinite over $\mathbb Q$ (isotropic at the infinite place). -/
theorem isIndefinite_ch11Ex1Form :
    Lattices.IsIndefinite (ch11Ex1Form.map (Int.castRingHom ℚ)) := by
  refine Lattices.isIndefinite_of_neg_pos ch11Ex1Form ![0, 0, 1] ![1, 0, 0] ?_ ?_
  · rw [evalIn_ch11Ex1Form]; simp
  · rw [evalIn_ch11Ex1Form]; simp

/-- Helper: $x_0 \mapsto -x_0$ is an improper automorph of $x_0^2 + 5x_1^2 - 7x_2^2$. -/
theorem hasImproperAut_ch11Ex1Form : HasImproperAut ch11Ex1Form := by
  refine ⟨reflFirst (n := 3) (by norm_num), fun x => ?_, det_reflFirst _⟩
  rw [eval_ch11Ex1Form, eval_ch11Ex1Form]
  simp only [reflFirst, mulVec_diagonal]
  simp

/-- **Cassels, Ch. 11, Example 1** (p. 251), first part: *use the theory of spinor genera to show that the genus of
$f = x^2 + 5y^2 - 7z^2$ contains only one proper equivalence class.* Every form in the genus of $f$
(`Siegel.SameGenus`) is properly integrally equivalent to $f$ (`ProperIntEquiv`). Here $d = -35$, so $p^3 \nmid d$ for
odd $p$ and $2^{2} \nmid d$ (Theorem 1.5 applies); $f$ is indefinite. -/
@[kb "cassels1978" "Ch. 11, Ex. 1, p. 251 (one proper class)"]
theorem ex1_properIntEquiv_of_sameGenus (f' : QuadForm ℤ 3) (h : SameGenus ch11Ex1Form f') :
    ProperIntEquiv ch11Ex1Form f' := by
  have hdet : ch11Ex1Form.hessian.det ≠ 0 := by rw [hessian_det_ch11Ex1Form]; norm_num
  have hi : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (p : ℤ) ^ (3 * (3 - 1) / 2) ∣ ch11Ex1Form.hessian.det := by
    intro p hp hp2 hd
    rw [hessian_det_ch11Ex1Form] at hd
    have h1 : (p : ℤ) ^ 3 ≤ 280 := by
      have := Int.le_of_dvd (by norm_num) ((dvd_neg).mpr hd)
      simpa using this
    have h2 : p ≤ 6 := by
      by_contra hc
      push Not at hc
      have : (7 : ℤ) ≤ p := by exact_mod_cast hc
      nlinarith [pow_le_pow_left₀ (by norm_num) this 3]
    have h3 := hp.two_le
    interval_cases p <;> omega
  have hii : ¬ IsClassicallyIntegral ch11Ex1Form ∨
      ¬ (2 : ℤ) ^ (Lattices.casselsExpTwo 3 + (3 : ℕ)).toNat ∣ ch11Ex1Form.hessian.det := by
    right
    rw [hessian_det_ch11Ex1Form]
    have e : (Lattices.casselsExpTwo 3 + (3 : ℕ)).toNat = 5 := by simp [Lattices.casselsExpTwo]
    rw [e]
    omega
  have hone := intEquiv_of_sameGenus_of_ch11 (n := 3) le_rfl ch11Ex1Form hdet isIndefinite_ch11Ex1Form hi hii f' h
  exact (intEquiv_iff_properIntEquiv_of_hasImproperAut hasImproperAut_ch11Ex1Form f').mp hone

/-! ### Example 1, second part: primitive representations -/

/-- Helper: $5$ is prime. -/
instance factPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Helper: $7$ is prime. -/
instance factPrimeSeven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- Helper: for an odd prime $p$, an integer $c$ prime to $p$ that is a square modulo $p$ is the square of a unit of
$\mathbb Z_p$. Here `r` is a square root of `c` modulo $p$. -/
theorem sqrt_unit_of_cong (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (c r : ℤ) (hc : ¬ (p : ℤ) ∣ c)
    (hr : (p : ℤ) ∣ r * r - c) : ∃ w : ℤ_[p], IsUnit w ∧ w * w = c := by
  have hu : IsUnit (c : ℤ_[p]) := (isUnit_intCast_padic c).mpr hc
  have hsq : IsSquare (PadicInt.toZMod (hu.unit : ℤ_[p])) := by
    refine ⟨(r : ZMod p), ?_⟩
    have h1 : ((r * r - c : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hr
    push_cast at h1
    simp only [IsUnit.unit_spec, map_intCast]
    exact (sub_eq_zero.mp h1).symm
  have h2 := (HilbertLocal.isSquare_unit_iff hp2 hu.unit).mpr hsq
  obtain ⟨w, hw, hwu⟩ := exists_sq_root_of_isSquare hu.unit h2
  exact ⟨w, hwu, by rw [hw]; rfl⟩

/-- Helper: a $2$-adic primitive representation with prescribed tail `(y0, z0)`. -/
theorem ex1_local_two (a y0 z0 : ℤ) (h : (a - 5 * (y0 * y0) + 7 * (z0 * z0)) % 8 = 1) :
    ∃ x : Fin 3 → ℤ_[2], (∃ i, IsUnit (x i)) ∧ (ch11Ex1Form.map (Int.castRingHom ℤ_[2])).eval x = a := by
  obtain ⟨w, hw, hww⟩ := two_adic_sq _ h
  refine ⟨![w, y0, z0], ⟨0, by simpa using hw⟩, ?_⟩
  rw [eval_map_ch11Ex1Form]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  push_cast at hww
  linear_combination hww

/-- Helper: a $p$-adic primitive representation with unit first coordinate (`p` odd), prescribed tail `(y0, z0)`,
given a square root `r` modulo $p$ of `a - 5 y0^2 + 7 z0^2`. -/
theorem ex1_local_head (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a y0 z0 r : ℤ)
    (hc : ¬ (p : ℤ) ∣ a - 5 * (y0 * y0) + 7 * (z0 * z0))
    (hr : (p : ℤ) ∣ r * r - (a - 5 * (y0 * y0) + 7 * (z0 * z0))) :
    ∃ x : Fin 3 → ℤ_[p], (∃ i, IsUnit (x i)) ∧ (ch11Ex1Form.map (Int.castRingHom ℤ_[p])).eval x = a := by
  obtain ⟨w, hw, hww⟩ := sqrt_unit_of_cong p hp2 _ r hc hr
  refine ⟨![w, y0, z0], ⟨0, by simpa using hw⟩, ?_⟩
  rw [eval_map_ch11Ex1Form]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  push_cast at hww
  linear_combination hww

/-- Helper: at $p = 5$ with $5 \mid a$ and $a/5 \equiv \pm 1 \pmod 5$, the representation $(0, y, 0)$ with $5y^2 = a$. -/
theorem ex1_local_five_dvd (a : ℤ) (h5 : a % 25 = 5 ∨ a % 25 = 20) :
    ∃ x : Fin 3 → ℤ_[5], (∃ i, IsUnit (x i)) ∧ (ch11Ex1Form.map (Int.castRingHom ℤ_[5])).eval x = a := by
  obtain ⟨w, hw, hww⟩ : ∃ w : ℤ_[5], IsUnit w ∧ w * w = ((a / 5 : ℤ) : ℤ_[5]) := by
    rcases h5 with h | h
    · exact sqrt_unit_of_cong 5 (by norm_num) _ 1 (by omega) (by omega)
    · exact sqrt_unit_of_cong 5 (by norm_num) _ 2 (by omega) (by omega)
  refine ⟨![0, w, 0], ⟨1, by simpa using hw⟩, ?_⟩
  rw [eval_map_ch11Ex1Form]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  have ha : a = 5 * (a / 5) := by omega
  have : (a : ℤ_[5]) = 5 * ((a / 5 : ℤ) : ℤ_[5]) := by
    conv_lhs => rw [ha]
    push_cast; ring
  rw [this, ← hww]
  ring

/-- Helper: at $p = 5$ with $5 \nmid a$, a representation with $x_1 = 0$. -/
theorem ex1_local_five_unit (a : ℤ) (h5 : a % 5 ≠ 0) :
    ∃ x : Fin 3 → ℤ_[5], (∃ i, IsUnit (x i)) ∧ (ch11Ex1Form.map (Int.castRingHom ℤ_[5])).eval x = a := by
  have h : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by omega
  rcases h with h | h | h | h
  · exact ex1_local_head 5 (by norm_num) a 0 0 1 (by omega) (by omega)
  · exact ex1_local_head 5 (by norm_num) a 0 1 2 (by omega) (by omega)
  · exact ex1_local_head 5 (by norm_num) a 0 2 1 (by omega) (by omega)
  · exact ex1_local_head 5 (by norm_num) a 0 0 2 (by omega) (by omega)

/-- Helper: at $p = 7$ every integer is primitively represented. -/
theorem ex1_local_seven (a : ℤ) :
    ∃ x : Fin 3 → ℤ_[7], (∃ i, IsUnit (x i)) ∧ (ch11Ex1Form.map (Int.castRingHom ℤ_[7])).eval x = a := by
  have h : a % 7 = 0 ∨ a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 3 ∨ a % 7 = 4 ∨ a % 7 = 5 ∨ a % 7 = 6 := by omega
  rcases h with h | h | h | h | h | h | h
  · exact ex1_local_head 7 (by norm_num) a 1 0 3 (by omega) (by omega)
  · exact ex1_local_head 7 (by norm_num) a 0 0 1 (by omega) (by omega)
  · exact ex1_local_head 7 (by norm_num) a 0 0 3 (by omega) (by omega)
  · exact ex1_local_head 7 (by norm_num) a 2 0 2 (by omega) (by omega)
  · exact ex1_local_head 7 (by norm_num) a 0 0 2 (by omega) (by omega)
  · exact ex1_local_head 7 (by norm_num) a 3 0 3 (by omega) (by omega)
  · exact ex1_local_head 7 (by norm_num) a 1 0 1 (by omega) (by omega)

/-- Helper: residues of squares modulo $8$ by parity. -/
theorem sq_mod_eight_parity (x : ℤ) :
    (x % 2 = 1 → x ^ 2 % 8 = 1) ∧ (x % 2 = 0 → x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 4) := by
  have h : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨
      x % 8 = 7 := by omega
  rcases h with h | h | h | h | h | h | h | h <;> simp [pow_two, Int.mul_emod, h] <;> omega

/-- Helper: $u^2 - 2v^2 \equiv 0 \pmod 5$ forces $5 \mid u$ and $5 \mid v$ ($2$ is not a square modulo $5$). -/
theorem five_dvd_of_sq_sub (u v : ℤ) (h : (5 : ℤ) ∣ u ^ 2 - 2 * v ^ 2) : (5 : ℤ) ∣ u ∧ (5 : ℤ) ∣ v := by
  have key : ∀ s t : ZMod 5, s ^ 2 - 2 * t ^ 2 = 0 → s = 0 ∧ t = 0 := by decide
  have h1 : ((u ^ 2 - 2 * v ^ 2 : ℤ) : ZMod 5) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mpr h
  push_cast at h1
  obtain ⟨a, b⟩ := key _ _ h1
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp a, (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp b⟩

/-- Helper: a primitive integer vector has a coordinate prime to `p`. -/
theorem exists_not_dvd_of_gcd {n : ℕ} (x : Fin n → ℤ) (h : Finset.univ.gcd x = 1) (p : ℤ) (hp : ¬ IsUnit p) :
    ∃ i, ¬ p ∣ x i := by
  by_contra hall
  push Not at hall
  have : p ∣ Finset.univ.gcd x := Finset.dvd_gcd fun i _ => hall i
  rw [h] at this
  exact hp (isUnit_of_dvd_one this)

/-- **Cassels, Ch. 11, Example 1** (p. 251), second part: *deduce necessary and sufficient conditions for an integer
$a$ to be primitively represented by $f = x^2 + 5y^2 - 7z^2$.* An integer $a$ is represented over $\mathbb Z$ by
$f(x_0, x_1, x_2)$ with $\gcd(x_0, x_1, x_2) = 1$ if and only if $a \equiv 1, 2, 5, 6, 7 \pmod 8$ and
($5 \nmid a$ or $a \equiv 5, 20 \pmod{25}$). *Reconstruction:* the conditions are our own computation (the book
leaves them to the reader), confirmed numerically for $|a| \le 40$. -/
@[kb "cassels1978" "Ch. 11, Ex. 1, p. 251 (primitive representations)"]
theorem ex1_primRep_iff (a : ℤ) :
    (∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ch11Ex1Form.eval x = a) ↔
      (a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7) ∧
        (a % 5 ≠ 0 ∨ a % 25 = 5 ∨ a % 25 = 20) := by
  constructor
  · rintro ⟨x, hx, hxa⟩
    rw [eval_ch11Ex1Form] at hxa
    have hodd : ¬ ∀ i, x i % 2 = 0 := not_forall_even_of_gcd x hx
    have p0 := sq_mod_eight_parity (x 0)
    have p1 := sq_mod_eight_parity (x 1)
    have p2 := sq_mod_eight_parity (x 2)
    have hodd' : x 0 % 2 = 1 ∨ x 1 % 2 = 1 ∨ x 2 % 2 = 1 := by
      by_contra hc
      push Not at hc
      apply hodd
      intro i
      fin_cases i <;> simp <;> omega
    constructor
    · generalize x 0 ^ 2 = X0 at *
      generalize x 1 ^ 2 = X1 at *
      generalize x 2 ^ 2 = X2 at *
      omega
    · by_cases h5 : a % 5 = 0
      · right
        have h1 : (5 : ℤ) ∣ x 0 ^ 2 - 2 * x 2 ^ 2 := by
          have : (5 : ℤ) ∣ a := by omega
          have e : x 0 ^ 2 - 2 * x 2 ^ 2 = a - 5 * x 1 ^ 2 + 5 * x 2 ^ 2 := by linear_combination hxa
          rw [e]
          exact dvd_add (dvd_sub this (dvd_mul_right _ _)) (dvd_mul_right _ _)
        obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := five_dvd_of_sq_sub _ _ h1
        have h1' : ¬ (5 : ℤ) ∣ x 1 := by
          intro hd
          obtain ⟨i, hi⟩ := exists_not_dvd_of_gcd x hx 5 (by
            intro hu; have := Int.isUnit_iff.mp hu; omega)
          fin_cases i
          · exact hi ⟨s, hs⟩
          · exact hi hd
          · exact hi ⟨t, ht⟩
        have hsq : x 1 ^ 2 % 5 = 1 ∨ x 1 ^ 2 % 5 = 4 := by
          have h : x 1 % 5 = 1 ∨ x 1 % 5 = 2 ∨ x 1 % 5 = 3 ∨ x 1 % 5 = 4 := by omega
          rcases h with h | h | h | h <;> simp [pow_two, Int.mul_emod, h]
        have e : a = 5 * x 1 ^ 2 + 25 * (s ^ 2 - 7 * t ^ 2) := by
          rw [← hxa, hs, ht]; ring
        generalize x 1 ^ 2 = X1 at *
        generalize s ^ 2 - 7 * t ^ 2 = K at *
        omega
      · left; exact h5
  · rintro ⟨h8, h5⟩
    have ha : a ≠ 0 := by omega
    have hdet : ch11Ex1Form.hessian.det ≠ 0 := by rw [hessian_det_ch11Ex1Form]; norm_num
    have hreal : ∃ x : Fin 3 → ℝ, ch11Ex1Form.evalIn ℝ x = a :=
      Lattices.exists_real_rep_of_neg_pos ch11Ex1Form ![0, 0, 1] ![1, 0, 0]
        (by rw [evalIn_ch11Ex1Form]; simp) (by rw [evalIn_ch11Ex1Form]; simp) ha
    refine exists_primRep_of_one_class ch11Ex1Form (by norm_num) hdet
      (fun f' h => (ex1_properIntEquiv_of_sameGenus f' h).intEquiv) ha hreal ?_
    intro p hpf hp
    rcases hp with rfl | hp | ⟨h3, -⟩
    · have h : a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := h8
      rcases h with h | h | h | h | h
      · exact ex1_local_two a 0 0 (by omega)
      · exact ex1_local_two a 0 1 (by omega)
      · exact ex1_local_two a 2 0 (by omega)
      · exact ex1_local_two a 1 0 (by omega)
      · exact ex1_local_two a 1 1 (by omega)
    · rw [hessian_det_ch11Ex1Form] at hp
      have hpn : p ∣ 280 := by
        have : (p : ℤ) ∣ 280 := (dvd_neg).mp (by simpa using hp)
        exact_mod_cast this
      have h280 : (280 : ℕ) = 2 ^ 3 * 5 * 7 := by norm_num
      rw [h280] at hpn
      have hpr := hpf.out
      rcases (Nat.Prime.dvd_mul hpr).mp hpn with h | h
      · rcases (Nat.Prime.dvd_mul hpr).mp h with h | h
        · have := (Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp (hpr.dvd_of_dvd_pow h)
          subst this
          have h : a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := h8
          rcases h with h | h | h | h | h
          · exact ex1_local_two a 0 0 (by omega)
          · exact ex1_local_two a 0 1 (by omega)
          · exact ex1_local_two a 2 0 (by omega)
          · exact ex1_local_two a 1 0 (by omega)
          · exact ex1_local_two a 1 1 (by omega)
        · have := (Nat.prime_dvd_prime_iff_eq hpr (by norm_num : Nat.Prime 5)).mp h
          subst this
          rcases h5 with h | h | h
          · exact ex1_local_five_unit a h
          · exact ex1_local_five_dvd a (Or.inl h)
          · exact ex1_local_five_dvd a (Or.inr h)
      · have := (Nat.prime_dvd_prime_iff_eq hpr (by norm_num : Nat.Prime 7)).mp h
        subst this
        exact ex1_local_seven a
    · omega

/-! ### Example 2: an explicit equivalence -/

/-- $x_0^2 - 3x_1^2 - 2x_1x_2 - 23x_2^2$ (Example 2, first form). -/
def ch11Ex2f : QuadForm ℤ 3 := QuadForm.ofUpper ![![1, 0, 0], ![0, -3, -2], ![0, 0, -23]]

/-- $x_0^2 - 7x_1^2 - 6x_1x_2 - 11x_2^2$ (Example 2, second form). -/
def ch11Ex2g : QuadForm ℤ 3 := QuadForm.ofUpper ![![1, 0, 0], ![0, -7, -6], ![0, 0, -11]]

/-- Helper: the substitution matrix of Example 2. -/
def ch11Ex2T : GL (Fin 3) ℤ :=
  ⟨!![-10, -25, -1; -1, -3, -2; -2, -5, 0], !![-10, 5, 47; 4, -2, -19; -1, 0, 5],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

/-- **Cassels, Ch. 11, Example 2** (p. 251): *show that the forms $x^2 - 3y^2 - 2yz - 23z^2$ and
$x^2 - 7y^2 - 6yz - 11z^2$ are integrally equivalent* (even properly, by the matrix of determinant $1$ found by
search; $f(Tx) = g(x)$). -/
@[kb "cassels1978" "Ch. 11, Ex. 2, p. 251"]
theorem ex2_properIntEquiv : ProperIntEquiv ch11Ex2f ch11Ex2g := by
  refine ⟨ch11Ex2T, ?_, fun x => ?_⟩
  · simp [ch11Ex2T, Matrix.det_fin_three]
  · simp [ch11Ex2T, ch11Ex2f, ch11Ex2g, QuadForm.eval, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_three,
      Matrix.mulVec, dotProduct]
    ring

end QuadFormsKB.Siegel
