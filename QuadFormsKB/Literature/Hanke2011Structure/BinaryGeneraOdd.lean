/-
# Hanke 2011, Lemma 7.2 for $\mathfrak p \nmid 2$ over $\mathbb Q_p$: the genera, counted with their Hasse invariants

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), Lemma 7.2, p. 27 (first table) and Case 1 of the proof, p. 28.

`BinaryHasse.lean` computes the Hasse invariants of the representative forms $u_1x^2 + p^\nu u_2y^2$; this file
counts the genera themselves. The local genera with fixed $\det_H = s$ are Cassels' $\mathbb Z_p$-classes
`Composition.LocalClasses p D` of primitive binary forms of discriminant $D = -s$ (Cassels' integer $D$ must be
$\equiv 0, 1 \bmod 4$; every squareclass of $\mathbb Q_p^\times$ has such a representative, e.g. $4s$, since $4$ is a unit
square for $p$ odd), and `hasseCount p D ε` counts those with $c_p = \varepsilon$ (Serre's convention). With
$s = p^\nu u$, $p \nmid u$, the table is

| Jordan block structure | $c_p = 1$ | $c_p = -1$ | condition |
|---|---|---|---|
| $(2)$ ($\nu = 0$) | 1 | 0 | – |
| $(1,1)$ ($\nu \ge 1$) | 1 | 1 | $\nu$ odd |
| $(1,1)$ ($\nu \ge 1$) | 2 | 0 | $\nu$ even |

**Proof.** The number of classes is $1$ for $p \nmid D$ and $2$ for $p \mid D$ (Cassels, Ch. 14, Lemma 3.1,
`Composition.card_localClasses_odd_of_not_dvd`, `Composition.card_localClasses_odd_of_dvd`). A class representing the
unit $w$ has $c_p = (w, p^\nu(-u))_p = \left(\frac{w}{p}\right)^\nu$ (`hasseClass_odd`, from the Hilbert symbol formula); for
$\nu$ even this is $1$, and for $\nu$ odd the forms $x^2 + ey^2$ and $\varepsilon x^2 + e'y^2$ ($\varepsilon$ a nonresidue)
give both signs.

**Proves** (unconditional): `lemma_7_2_odd_two`, `lemma_7_2_odd_one_one_even`, `lemma_7_2_odd_one_one_odd`.
-/
import QuadFormsKB.Literature.Hanke2011Structure.DyadicHasseTable
import QuadFormsKB.Literature.Hanke2011Structure.BinaryHasse

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Hanke2011Structure

open QuadFormsKB.Composition QuadFormsKB.Siegel QuadFormsKB.HilbertLocal

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

theorem unitChar_eq_one_or (u : ℤ_[p]ˣ) : unitChar u = 1 ∨ unitChar u = -1 := by
  unfold unitChar
  exact quadraticChar_dichotomy (u.isUnit.map (PadicInt.toZMod (p := p))).ne_zero

/-- **The Hasse invariant of a class at $p$ odd**: if $D = p^\nu v$ ($v$ a unit) and the class of $F$ represents the
unit $w$, then $c_p = \left(\frac{w}{p}\right)^\nu$. -/
theorem hasseClass_odd (hp2 : p ≠ 2) {D : ℤ} (hD : D ≠ 0) {ν : ℕ} (v : ℤ_[p]ˣ)
    (hDv : (D : ℚ_[p]) = (p : ℚ_[p]) ^ ν * ((v : ℤ_[p]) : ℚ_[p])) (F : LocalPrimForm p D) {x : Fin 2 → ℤ_[p]}
    (hx : IsUnit (F.1.eval x)) :
    hasseClass (Quotient.mk (localSetoid p D) F) = unitChar hx.unit ^ ν := by
  show hasseC (F.1.map PadicInt.Coe.ringHom) = _
  rcases hasseC_eq_of_unit_value hD F (v := x) with h | h
  · rw [h, hDv]
    have hf := hilbertSymbol_odd_formula hp2 0 ν hx.unit v
    simp only [pow_zero, one_mul, IsUnit.unit_spec, zero_mul, pow_zero] at hf
    rw [hf]; ring
  · exact absurd h hx.ne_zero

/-- The diagonal class $wx^2 + ey^2$ with $w$ a unit, $-4we = D$. -/
theorem exists_class_with_unit (hp2 : p ≠ 2) (D : ℤ) (w : ℤ_[p]ˣ) :
    ∃ (F : LocalPrimForm p D), F.1.eval ![1, 0] = (w : ℤ_[p]) := by
  have h4 : IsUnit ((4 : ℤ_[p]) * w) := by
    have h2 := isUnit_two_padic hp2 (p := p)
    have : (4 : ℤ_[p]) * w = 2 * 2 * w := by norm_num
    rw [this]; exact (h2.mul h2).mul w.isUnit
  obtain ⟨i, hi⟩ := h4.exists_right_inv
  have h : -4 * (w : ℤ_[p]) * (-(D : ℤ_[p]) * i) = (D : ℤ_[p]) := by linear_combination (D : ℤ_[p]) * hi
  refine ⟨diagForm (w : ℤ_[p]) (-(D : ℤ_[p]) * i) w.isUnit h, ?_⟩
  show (bq (w : ℤ_[p]) 0 _).eval ![1, 0] = _
  rw [bq_eval]; ring

/-- A unit of $\mathbb Z_p$ that is a quadratic nonresidue ($p$ odd). -/
theorem exists_nonresidue_unit (hp2 : p ≠ 2) : ∃ ε : ℤ_[p]ˣ, unitChar ε = -1 := by
  have hring : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  obtain ⟨e, he⟩ := quadraticChar_exists_neg_one hring
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  let e' : ℤ_[p] := ((e.val : ℕ) : ℤ_[p])
  have he' : PadicInt.toZMod e' = e := by simp [e']
  have heU : IsUnit e' := by
    by_contra hne
    have hm : e' ∈ IsLocalRing.maximalIdeal ℤ_[p] := (IsLocalRing.mem_maximalIdeal _).mpr hne
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, he'] at hm
    exact he0 hm
  exact ⟨heU.unit, by unfold unitChar; rw [IsUnit.unit_spec, he', he]⟩

/-- Setup: $s = p^\nu u$, $D = -s$, $D \ne 0$ and $D = p^\nu \cdot(-u)$ in $\mathbb Q_p$ with $-u$ a unit. -/
theorem odd_setup {ν : ℕ} {u : ℤ} (hpu : ¬ (p : ℤ) ∣ u) :
    ∃ v : ℤ_[p]ˣ, ((-(p ^ ν * u) : ℤ) : ℚ_[p]) = (p : ℚ_[p]) ^ ν * ((v : ℤ_[p]) : ℚ_[p]) := by
  have hu' : ¬ (p : ℤ) ∣ -u := by rwa [Int.dvd_neg]
  refine ⟨(isUnit_intCast_of_not_dvd p hu').unit, ?_⟩
  rw [IsUnit.unit_spec]; push_cast; ring

theorem odd_ne_zero {ν : ℕ} {u : ℤ} (hpu : ¬ (p : ℤ) ∣ u) : (-(p ^ ν * u) : ℤ) ≠ 0 := by
  have hu : u ≠ 0 := by rintro rfl; exact hpu (dvd_zero _)
  exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)) hu)

/-- For $\nu$ even every class has $c_p = 1$. -/
theorem hasseClass_odd_even (hp2 : p ≠ 2) {ν : ℕ} (hν : Even ν) {u : ℤ} (hpu : ¬ (p : ℤ) ∣ u)
    (G : LocalClasses p (-(p ^ ν * u))) : hasseClass G = 1 := by
  obtain ⟨v, hv⟩ := odd_setup (ν := ν) hpu
  induction G using localClasses_ind with | _ F => ?_
  obtain ⟨x, hx⟩ := exists_unit_value F.2.1
  rw [hasseClass_odd hp2 (odd_ne_zero hpu) v hv F hx]
  rcases unitChar_eq_one_or hx.unit with h | h <;> rw [h]
  · exact one_pow ν
  · exact hν.neg_one_pow

theorem counts_of_all_one {D : ℤ} (hall : ∀ G : LocalClasses p D, hasseClass G = 1) :
    hasseCount p D 1 = Nat.card (LocalClasses p D) ∧ hasseCount p D (-1) = 0 := by
  refine ⟨Nat.card_congr (Equiv.subtypeUnivEquiv hall), ?_⟩
  unfold hasseCount
  rw [Nat.card_eq_zero]
  left
  exact ⟨fun G => by have := G.2; rw [hall] at this; exact absurd this (by decide)⟩

/-- **Lemma 7.2, Jordan block structure $(2)$, $p$ odd** (Hanke 2011, p. 27): for $\det_H = u$ a unit there is one
genus, with $c_p = 1$. -/
@[kb "hanke2011structure" "Lemma 7.2, p. 27 (p ∤ 2, type (2), genera)"]
theorem lemma_7_2_odd_two (hp2 : p ≠ 2) {u : ℤ} (hpu : ¬ (p : ℤ) ∣ u)
    (hD4 : (-u) % 4 = 0 ∨ (-u) % 4 = 1) :
    hasseCount p (-u) 1 = 1 ∧ hasseCount p (-u) (-1) = 0 := by
  have e : (-u : ℤ) = -((p : ℤ) ^ 0 * u) := by ring
  have h := counts_of_all_one (hasseClass_odd_even hp2 (ν := 0) (by decide) hpu)
  rw [← e] at h
  rw [card_localClasses_odd_of_not_dvd hp2 hD4 (by rwa [Int.dvd_neg])] at h
  exact h

/-- **Lemma 7.2, Jordan block structure $(1,1)$, $\nu$ even, $p$ odd** (Hanke 2011, p. 27): for $\det_H = p^\nu u$,
$\nu \ge 2$ even, there are two genera, both with $c_p = 1$. -/
@[kb "hanke2011structure" "Lemma 7.2, p. 27 (p ∤ 2, type (1,1), ν even, genera)"]
theorem lemma_7_2_odd_one_one_even (hp2 : p ≠ 2) {ν : ℕ} (hν : Even ν) (hν0 : ν ≠ 0) {u : ℤ}
    (hpu : ¬ (p : ℤ) ∣ u) (hD4 : (-(p ^ ν * u)) % 4 = 0 ∨ (-(p ^ ν * u)) % 4 = 1) :
    hasseCount p (-(p ^ ν * u)) 1 = 2 ∧ hasseCount p (-(p ^ ν * u)) (-1) = 0 := by
  have h := counts_of_all_one (hasseClass_odd_even hp2 hν hpu)
  rw [card_localClasses_odd_of_dvd hp2 (odd_ne_zero hpu) hD4
    (Dvd.dvd.neg_right (Dvd.dvd.mul_right (dvd_pow_self _ hν0) _))] at h
  exact h

/-- **Lemma 7.2, Jordan block structure $(1,1)$, $\nu$ odd, $p$ odd** (Hanke 2011, p. 27): for $\det_H = p^\nu u$,
$\nu$ odd, there are two genera, one with $c_p = 1$ and one with $c_p = -1$. -/
@[kb "hanke2011structure" "Lemma 7.2, p. 27 (p ∤ 2, type (1,1), ν odd, genera)"]
theorem lemma_7_2_odd_one_one_odd (hp2 : p ≠ 2) {ν : ℕ} (hν : Odd ν) {u : ℤ}
    (hpu : ¬ (p : ℤ) ∣ u) (hD4 : (-(p ^ ν * u)) % 4 = 0 ∨ (-(p ^ ν * u)) % 4 = 1) :
    hasseCount p (-(p ^ ν * u)) 1 = 1 ∧ hasseCount p (-(p ^ ν * u)) (-1) = 1 := by
  set D : ℤ := -(p ^ ν * u) with hDdef
  obtain ⟨v, hv⟩ := odd_setup (ν := ν) hpu
  have hD0 : D ≠ 0 := odd_ne_zero hpu
  have hcard : Nat.card (LocalClasses p D) = 2 :=
    card_localClasses_odd_of_dvd hp2 hD0 hD4
      (Dvd.dvd.neg_right (Dvd.dvd.mul_right (dvd_pow_self _ hν.pos.ne') _))
  have : Finite (LocalClasses p D) := Nat.finite_of_card_ne_zero (by omega)
  -- every class has `c = ±1`
  have hpm : ∀ G : LocalClasses p D, hasseClass G = 1 ∨ hasseClass G = -1 := by
    intro G
    induction G using localClasses_ind with | _ F => ?_
    obtain ⟨x, hx⟩ := exists_unit_value F.2.1
    rw [hasseClass_odd hp2 hD0 v hv F hx]
    rcases unitChar_eq_one_or hx.unit with h | h <;> rw [h]
    · left; exact one_pow ν
    · right; exact hν.neg_one_pow
  -- witnesses
  have hwit : ∀ w : ℤ_[p]ˣ, ∃ G : LocalClasses p D, hasseClass G = unitChar w ^ ν := by
    intro w
    obtain ⟨F, hF⟩ := exists_class_with_unit hp2 D w
    have hx : IsUnit (F.1.eval ![1, 0]) := by rw [hF]; exact w.isUnit
    refine ⟨Quotient.mk _ F, ?_⟩
    rw [hasseClass_odd hp2 hD0 v hv F hx]
    congr 2
    exact Units.ext hF
  obtain ⟨G1, hG1⟩ := hwit 1
  obtain ⟨ε, hε⟩ := exists_nonresidue_unit hp2 (p := p)
  obtain ⟨G2, hG2⟩ := hwit ε
  have hchar1 : unitChar (1 : ℤ_[p]ˣ) = 1 := by unfold unitChar; simp
  rw [hchar1, one_pow] at hG1
  rw [hε, hν.neg_one_pow] at hG2
  -- counting
  have hsplit : Nat.card (LocalClasses p D) = hasseCount p D 1 + hasseCount p D (-1) := by
    unfold hasseCount
    rw [← Nat.card_sum]
    refine Nat.card_congr ((Equiv.sumCompl (fun G : LocalClasses p D => hasseClass G = 1)).symm.trans
      (Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivRight fun G => ?_)))
    rcases hpm G with h | h <;> simp [h]
  have h1 : 1 ≤ hasseCount p D 1 := by
    unfold hasseCount
    have : Nonempty {G : LocalClasses p D // hasseClass G = 1} := ⟨⟨G1, hG1⟩⟩
    exact Nat.card_pos
  have h2 : 1 ≤ hasseCount p D (-1) := by
    unfold hasseCount
    have : Nonempty {G : LocalClasses p D // hasseClass G = -1} := ⟨⟨G2, hG2⟩⟩
    exact Nat.card_pos
  omega

end

end QuadFormsKB.Hanke2011Structure
