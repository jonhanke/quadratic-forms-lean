/-
# Cassels, Chapter 14, §3 and §5: the groups $\mathcal G_p$ and Theorem 5.1

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §3, p. 339 and §5, p. 343.
-/
import QuadFormsKB.Literature.Cassels.Ch14.ExistenceImage
import QuadFormsKB.Literature.Cassels.Ch14.LocalClassesTwo
import QuadFormsKB.Literature.Cassels.Ch14.Group
import QuadFormsKB.Literature.Cassels.Ch14.LocalComposition530

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Composition

open BinQF Binary FormClass Siegel QuadForm

/-! ### A generic description of the classes of forms with a unit value -/

section Generic

variable {R : Type*} [CommRing R]

/-- Helper: data of a "principal form" $x^2 + \beta xy + cy^2$ of discriminant $D$ over $R$. -/
structure PrinData (R : Type*) [CommRing R] (D : R) where
  /-- The middle coefficient $\beta$. -/
  β : R
  /-- The last coefficient $c$. -/
  c : R
  /-- The discriminant relation $\beta^2 - 4c = D$. -/
  h : β ^ 2 - 4 * c = D

variable {D : R}

/-- Helper: the principal norm form $x^2 + \beta xy + cy^2$. -/
def PrinData.norm (P : PrinData R D) (x y : R) : R := x ^ 2 + P.β * x * y + P.c * y ^ 2

/-- Helper: the principal form as a quadratic form. -/
def PrinData.form (P : PrinData R D) : QuadForm R 2 := bq 1 P.β P.c

theorem PrinData.form_eval (P : PrinData R D) (v : Fin 2 → R) : P.form.eval v = P.norm (v 0) (v 1) := by
  rw [PrinData.form]; conv_lhs => rw [vec_eta v]
  rw [bq_eval, PrinData.norm]; ring

theorem PrinData.disc2_form (P : PrinData R D) : disc2 P.form = D := by
  rw [disc2, PrinData.form, bq_coeff00, bq_coeff01, bq_coeff11]; linear_combination P.h

theorem PrinData.norm_smul (P : PrinData R D) (t x y : R) : P.norm (t * x) (t * y) = t ^ 2 * P.norm x y := by
  simp only [PrinData.norm]; ring

/-- **The norm group:** the units of $R$ represented by the principal form. A subgroup of $R^\times$ (the norm
form is multiplicative, $N(x + y\omega)N(x' + y'\omega) = N((x + y\omega)(x' + y'\omega))$, and the conjugate
of $x + y\omega$ has the same norm). -/
def PrinData.subgroup (P : PrinData R D) : Subgroup Rˣ where
  carrier := {h | ∃ x y : R, P.norm x y = (h : R)}
  mul_mem' := by
    rintro a b ⟨x, y, hx⟩ ⟨x', y', hy⟩
    refine ⟨x * x' - P.c * y * y', x * y' + x' * y + P.β * y * y', ?_⟩
    rw [Units.val_mul, ← hx, ← hy]; simp only [PrinData.norm]; ring
  one_mem' := ⟨1, 0, by simp [PrinData.norm]⟩
  inv_mem' := by
    rintro a ⟨x, y, hx⟩
    refine ⟨(x + P.β * y) * ((a⁻¹ : Rˣ) : R), -y * ((a⁻¹ : Rˣ) : R), ?_⟩
    have e : P.norm ((x + P.β * y) * ((a⁻¹ : Rˣ) : R)) (-y * ((a⁻¹ : Rˣ) : R)) =
        ((a⁻¹ : Rˣ) : R) ^ 2 * P.norm x y := by
      simp only [PrinData.norm]; ring
    rw [e, hx]
    have := a.mul_inv
    linear_combination (((a⁻¹ : Rˣ) : R)) * this

theorem PrinData.mem_subgroup (P : PrinData R D) {a : Rˣ} (x y : R) (h : P.norm x y = (a : R)) :
    a ∈ P.subgroup := ⟨x, y, h⟩

end Generic

section GenericLocal

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] {D : R}

/-- Helper: the middle coefficient of a form with unit first coefficient and fixed discriminant is determined
modulo $2$. -/
def HalfProp (R : Type*) [CommRing R] : Prop :=
  ∀ u b b' c c' : R, IsUnit u → b ^ 2 - 4 * u * c = b' ^ 2 - 4 * u * c' → ∃ k, b' = b + 2 * k

omit [IsDomain R] [IsLocalRing R] in
theorem halfProp_of_isUnit_two (h2 : IsUnit (2 : R)) : HalfProp R := by
  intro u b b' c c' _ _
  obtain ⟨i, hi⟩ := h2.exists_right_inv
  exact ⟨(b' - b) * i, by linear_combination (-(b' - b)) * hi⟩

/-- **Two forms of discriminant $D$ representing the same unit are equivalent.** -/
theorem equiv_of_same_unit_value (h4 : (4 : R) ≠ 0) (hh : HalfProp R) {F F' : QuadForm R 2}
    (hF : disc2 F = D) (hF' : disc2 F' = D) {v v' : Fin 2 → R} (hv : IsUnit (F.eval v))
    (hvv : F'.eval v' = F.eval v) : IsometricGL F F' := by
  obtain ⟨b, c, hbc, hi⟩ := exists_first hv
  have hv' : IsUnit (F'.eval v') := hvv ▸ hv
  obtain ⟨b', c', hbc', hi'⟩ := exists_first hv'
  rw [hvv] at hi' hbc'
  set u := F.eval v with hu
  obtain ⟨k, hk⟩ := hh u b b' c c' hv (by rw [hbc, hbc', hF, hF'])
  obtain ⟨ui, hui⟩ := hv.exists_right_inv
  have hb : b + 2 * u * (k * ui) = b' := by rw [hk]; linear_combination (2 * k) * hui
  have hc : u * (k * ui) ^ 2 + b * (k * ui) + c = c' := by
    have hu0 : (4 * u : R) ≠ 0 := mul_ne_zero h4 hv.ne_zero
    refine mul_left_cancel₀ hu0 ?_
    have e1 : b ^ 2 - 4 * u * c = D := by rw [hbc, hF]
    have e2 : b' ^ 2 - 4 * u * c' = D := by rw [hbc', hF']
    rw [← hb] at e2
    linear_combination e2 - e1
  have key := isometricGL_shear u b c (k * ui)
  rw [hb, hc] at key
  exact hi.trans (key.trans hi'.symm)

variable (P : PrinData R D)

/-- Helper: the values of a form with a unit value $u$ differ from the norm group: $u \cdot F(w)$ is a value of the
principal form. -/
theorem mul_value_mem (h4 : (4 : R) ≠ 0) (hh : HalfProp R) {F : QuadForm R 2} (hF : disc2 F = D)
    {v : Fin 2 → R} (hv : IsUnit (F.eval v)) (w : Fin 2 → R) :
    ∃ x y : R, P.norm x y = F.eval v * F.eval w := by
  obtain ⟨b, c, hbc, hi⟩ := exists_first hv
  set u := F.eval v with hu
  have hQ : disc2 (bq 1 b (u * c)) = D := by
    rw [disc2, bq_coeff00, bq_coeff01, bq_coeff11, ← hF, ← hbc]; ring
  have hPQ : IsometricGL P.form (bq 1 b (u * c)) :=
    equiv_of_same_unit_value h4 hh P.disc2_form hQ (v := ![1, 0]) (v' := ![1, 0])
      (by simp [PrinData.form_eval, PrinData.norm]) (by simp [PrinData.form_eval, PrinData.norm, bq_eval])
  obtain ⟨T, hT⟩ := hi.symm
  obtain ⟨M, hM⟩ := hPQ
  have h1 := hT w
  rw [vec_eta (T.val.mulVec w), bq_eval] at h1
  set s := (T.val.mulVec w) 0
  set t := (T.val.mulVec w) 1
  have h2 := hM ![u * s, t]
  rw [bq_eval, PrinData.form_eval] at h2
  refine ⟨(M.val.mulVec ![u * s, t]) 0, (M.val.mulVec ![u * s, t]) 1, ?_⟩
  rw [h2, ← h1]; ring

/-- Helper: every element $u h$ with $h$ in the norm group is a value of $F$. -/
theorem exists_value_mul (h4 : (4 : R) ≠ 0) (hh : HalfProp R) {F : QuadForm R 2} (hF : disc2 F = D)
    {v : Fin 2 → R} (hv : IsUnit (F.eval v)) (x y : R) :
    ∃ w : Fin 2 → R, F.eval w = F.eval v * P.norm x y := by
  obtain ⟨b, c, hbc, hi⟩ := exists_first hv
  set u := F.eval v with hu
  have hQ : disc2 (bq 1 b (u * c)) = D := by
    rw [disc2, bq_coeff00, bq_coeff01, bq_coeff11, ← hF, ← hbc]; ring
  have hQP : IsometricGL (bq 1 b (u * c)) P.form :=
    equiv_of_same_unit_value h4 hh hQ P.disc2_form (v := ![1, 0]) (v' := ![1, 0])
      (by simp [bq_eval]) (by simp [PrinData.form_eval, PrinData.norm, bq_eval])
  obtain ⟨N, hN⟩ := hQP
  obtain ⟨ui, hui⟩ := hv.exists_right_inv
  have h2 := hN ![u * x, u * y]
  rw [PrinData.form_eval, vec_eta (N.val.mulVec ![u * x, u * y]), bq_eval] at h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h2
  set w1 := (N.val.mulVec ![u * x, u * y]) 0
  set w2 := (N.val.mulVec ![u * x, u * y]) 1
  obtain ⟨g, hg⟩ := hi
  refine ⟨g.val.mulVec ![w1 * ui, w2], ?_⟩
  rw [hg, bq_eval]
  have h3 : u * (u * (w1 * ui) ^ 2 + b * (w1 * ui) * w2 + c * w2 ^ 2) = u * (u * P.norm x y) := by
    have : (u * (w1 * ui)) = w1 := by linear_combination w1 * hui
    have e : u * (u * (w1 * ui) ^ 2 + b * (w1 * ui) * w2 + c * w2 ^ 2) =
        (u * (w1 * ui)) ^ 2 + b * (u * (w1 * ui)) * w2 + u * c * w2 ^ 2 := by ring
    rw [e, this]; simp only [PrinData.norm] at h2 ⊢; linear_combination h2
  exact mul_left_cancel₀ hv.ne_zero h3

end GenericLocal

/-! ### The group $R^\times / N$ and the class of a form with a unit value -/

section Coset

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] {D : R} (P : PrinData R D)

theorem cg_aux1 {G : Type*} [CommGroup G] (a b : G) : a⁻¹ * b * a ^ 2 = a * b := by
  rw [sq, ← mul_assoc, mul_right_comm a⁻¹ b a, inv_mul_cancel, one_mul, mul_comm]

/-- Helper: the square of every unit is in the norm group ($N(a, 0) = a^2$). -/
theorem PrinData.sq_mem (a : Rˣ) : a ^ 2 ∈ P.subgroup :=
  ⟨a, 0, by simp [PrinData.norm]⟩

/-- Helper: two units have the same image in $R^\times / N$ iff their product is in $N$ (as $R^\times / N$ has
exponent $2$). -/
theorem PrinData.mk_eq_iff (a b : Rˣ) :
    (QuotientGroup.mk a : Rˣ ⧸ P.subgroup) = QuotientGroup.mk b ↔ a * b ∈ P.subgroup := by
  rw [QuotientGroup.eq]
  constructor
  · intro h
    have := P.subgroup.mul_mem h (P.sq_mem a)
    rwa [cg_aux1] at this
  · intro h
    have := P.subgroup.mul_mem h (P.subgroup.inv_mem (P.sq_mem a))
    rw [← eq_mul_inv_of_mul_eq (cg_aux1 a b)] at this
    exact this

/-- **The class of a binary form with a unit value in $R^\times / N$:** for a form $F$ over $R$ that takes a unit
value $F(v_0)$, the image of $F(v_0)$ in $R^\times / N$, where $N$ is the norm group of the principal form `P`
(`PrinData.subgroup`). It does not depend on the choice of the unit value (`cosetOf_eq`). -/
noncomputable def cosetOf (F : QuadForm R 2) (hF : ∃ v, IsUnit (F.eval v)) : Rˣ ⧸ P.subgroup :=
  QuotientGroup.mk hF.choose_spec.unit

variable (h4 : (4 : R) ≠ 0) (hh : HalfProp R)
include h4 hh

/-- Helper: the product of two unit values of isometric forms of discriminant $D$ is a norm. -/
theorem PrinData.mul_mem_of_isometric {F F' : QuadForm R 2} (hF : disc2 F = D) (hiso : IsometricGL F F')
    {v v' : Fin 2 → R} (hv : IsUnit (F.eval v)) (hv' : IsUnit (F'.eval v')) :
    hv.unit * hv'.unit ∈ P.subgroup := by
  obtain ⟨T, hT⟩ := hiso
  obtain ⟨x, y, hxy⟩ := mul_value_mem P h4 hh hF hv (T.val.mulVec v')
  refine P.mem_subgroup x y ?_
  rw [hxy, hT v', Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec]

/-- **The class of a form is independent of the unit value chosen.** -/
theorem cosetOf_eq {F : QuadForm R 2} (hF : disc2 F = D) (hex : ∃ v, IsUnit (F.eval v)) {v : Fin 2 → R}
    (hv : IsUnit (F.eval v)) : cosetOf P F hex = QuotientGroup.mk hv.unit :=
  (P.mk_eq_iff _ _).2 (P.mul_mem_of_isometric h4 hh hF (IsometricGL.refl F) _ hv)

/-- **Two forms of discriminant $D$ with unit values are $R$-equivalent iff their unit values have the same image
in $R^\times / N$.** -/
theorem cosetOf_eq_iff {F F' : QuadForm R 2} (hF : disc2 F = D) (hF' : disc2 F' = D)
    (hex : ∃ v, IsUnit (F.eval v)) (hex' : ∃ v, IsUnit (F'.eval v)) :
    cosetOf P F hex = cosetOf P F' hex' ↔ IsometricGL F F' := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := hex
    obtain ⟨v', hv'⟩ := hex'
    rw [cosetOf_eq P h4 hh hF ⟨v, hv⟩ hv, cosetOf_eq P h4 hh hF' ⟨v', hv'⟩ hv'] at h
    obtain ⟨x, y, hxy⟩ := QuotientGroup.eq.1 h.symm
    obtain ⟨w, hw⟩ := exists_value_mul P h4 hh hF' hv' x y
    refine equiv_of_same_unit_value h4 hh hF hF' hv (v' := w) ?_
    have hinv : F'.eval v' * ((hv'.unit⁻¹ : Rˣ) : R) = 1 := by
      have := hv'.unit.mul_inv
      rwa [IsUnit.unit_spec] at this
    rw [hw, hxy, Units.val_mul, ← mul_assoc, hinv, one_mul, IsUnit.unit_spec]
  · intro h
    obtain ⟨v, hv⟩ := hex
    obtain ⟨v', hv'⟩ := hex'
    rw [cosetOf_eq P h4 hh hF ⟨v, hv⟩ hv, cosetOf_eq P h4 hh hF' ⟨v', hv'⟩ hv']
    exact (P.mk_eq_iff _ _).2 (P.mul_mem_of_isometric h4 hh hF h hv hv')

omit h4 hh

/-- Helper: a form of discriminant $D$ with a prescribed unit value $w$: $w x^2 + \beta xy + w^{-1} c y^2$. -/
def PrinData.unitForm (w : Rˣ) : QuadForm R 2 := bq (w : R) P.β (((w⁻¹ : Rˣ) : R) * P.c)

theorem PrinData.disc2_unitForm (w : Rˣ) : disc2 (P.unitForm w) = D := by
  rw [PrinData.unitForm, disc2, bq_coeff00, bq_coeff01, bq_coeff11]
  have := w.mul_inv
  linear_combination P.h + (-4 * P.c) * this

theorem PrinData.eval_unitForm (w : Rˣ) : (P.unitForm w).eval ![1, 0] = (w : R) := by
  rw [PrinData.unitForm, bq_eval]; simp

/-- Helper: every class of $R^\times / N$ is the class of some form of discriminant $D$ (with a unit
first coefficient). -/
theorem PrinData.cosetOf_unitForm (h4 : (4 : R) ≠ 0) (hh : HalfProp R) (w : Rˣ)
    (hex : ∃ v, IsUnit ((P.unitForm w).eval v)) :
    cosetOf P (P.unitForm w) hex = QuotientGroup.mk w := by
  have hv : IsUnit ((P.unitForm w).eval ![1, 0]) := by rw [P.eval_unitForm]; exact w.isUnit
  rw [cosetOf_eq P h4 hh (P.disc2_unitForm w) hex hv]
  congr 1
  exact Units.ext (by simp [P.eval_unitForm])

end Coset

/-! ### Half-integrality of middle coefficients, over $\mathbb Z_p$ and $\mathbb R$ -/

section HalfInst

theorem halfProp_of_prime_two {R : Type*} [CommRing R] (h2 : Prime (2 : R)) : HalfProp R := by
  intro u b b' c c' _ h
  have e : (b' - b) * (b' + b) = 2 * (2 * u * (c' - c)) := by linear_combination -h
  rcases h2.dvd_or_dvd ⟨_, e⟩ with ⟨k, hk⟩ | ⟨m, hm⟩
  · exact ⟨k, by linear_combination hk⟩
  · exact ⟨m - b, by linear_combination hm⟩

theorem halfProp_padic (p : ℕ) [Fact p.Prime] : HalfProp ℤ_[p] := by
  rcases eq_or_ne p 2 with rfl | hp
  · refine halfProp_of_prime_two ?_
    have := (PadicInt.irreducible_p (p := 2)).prime
    simpa using this
  · exact halfProp_of_isUnit_two (isUnit_two_padic hp)

theorem halfProp_real : HalfProp ℝ :=
  halfProp_of_isUnit_two (isUnit_iff_ne_zero.2 two_ne_zero)

end HalfInst

/-! ### The groups $\mathcal G_p$ and $\mathcal G_\infty$ -/

section Groups

/-- **The principal form over any ring** (Cassels, Ch. 14, (1.11), p. 332), $x^2 + \beta xy + c y^2$ with
$\beta = D \bmod 2$ and $c = (\beta - D)/4$, as `PrinData` of discriminant $D$. -/
def principalData (R : Type*) [CommRing R] (D : ℤ) [NonzeroDisc D] : PrinData R (D : R) where
  β := ((D % 2 : ℤ) : R)
  c := (((D % 2 - D) / 4 : ℤ) : R)
  h := by
    have h : (D % 2) ^ 2 - 4 * ((D % 2 - D) / 4) = D := by
      have h4 := NonzeroDisc.mod_four (D := D)
      have h2 : D % 2 = 0 ∨ D % 2 = 1 := by omega
      rcases h2 with h2 | h2 <;> simp only [h2] <;> omega
    have := congrArg (fun z : ℤ => (z : R)) h
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] using this

variable (p : ℕ) [Fact p.Prime] (D : ℤ) [NonzeroDisc D]

/-- **The group $\mathcal G_p$** (Cassels, Ch. 14, §3, p. 339): the group of $\mathbb Z_p$-classes of primitive
$\mathbb Z_p$-integral binary forms of discriminant $D$, realized concretely as the quotient
$\mathbb Z_p^\times / N$ of the unit group of $\mathbb Z_p$ by the group $N$ of units represented by the principal form
$x^2 + \beta xy + c y^2$ of discriminant $D$ (`PrinData.subgroup`). The class of a form is the class of any unit value
it takes (`cosetOf`); that this is a bijection `LocalClasses p D ≃ LocalGroup p D` is `localEquiv`. The group law is
the one transported from the quotient (Cassels: "by mimicking the argument of Section 2"; the agreement with the law
induced by composition is `localHom`, a homomorphism by `classHom`). *Deviation:* Cassels gives no explicit model of $\mathcal G_p$. -/
abbrev LocalGroup : Type := ℤ_[p]ˣ ⧸ (principalData ℤ_[p] D).subgroup

/-- **The group $\mathcal G_\infty$** (Cassels, Ch. 14, §3, p. 339, $p = \infty$): the classes of real binary forms
of discriminant $D$ as the quotient $\mathbb R^\times / N$ by the values of the principal form. -/
abbrev RealGroup : Type := ℝˣ ⧸ (principalData ℝ D).subgroup

theorem disc2_localPrim (F : LocalPrimForm p D) : disc2 F.1 = (D : ℤ_[p]) := by
  rw [← neg_det_eq_disc2]; exact F.2.2

theorem disc2_realForm (F : RealForm D) : disc2 F.1 = (D : ℝ) := by
  rw [← neg_det_eq_disc2]; exact F.2

/-- Helper: over a field, a form of non-zero discriminant takes a non-zero value. -/
theorem exists_isUnit_val_field {K : Type*} [Field K] (F : QuadForm K 2) (h : disc2 F ≠ 0) :
    ∃ v, IsUnit (F.eval v) := by
  by_contra hcon
  push Not at hcon
  have z : ∀ v, F.eval v = 0 := fun v => by
    by_contra hv; exact hcon v (isUnit_iff_ne_zero.2 hv)
  have h1 := z ![1, 0]
  have h2 := z ![0, 1]
  have h3 := z ![1, 1]
  rw [eval_two] at h1 h2 h3
  simp at h1 h2 h3
  apply h
  rw [disc2]
  have hb : F.coeff 0 1 = 0 := by rw [h1, h2] at h3; linear_combination h3
  rw [hb, h1]; ring

/-- The class of a $\mathbb Z_p$-form of discriminant $D$ in $\mathcal G_p$. -/
noncomputable def localCoset (F : LocalPrimForm p D) : LocalGroup p D :=
  cosetOf (principalData ℤ_[p] D) F.1 (exists_unit_value F.2.1)

/-- The class of a real form of discriminant $D$ in $\mathcal G_\infty$. -/
noncomputable def realCoset (F : RealForm D) : RealGroup D :=
  cosetOf (principalData ℝ D) F.1
    (exists_isUnit_val_field F.1 (by rw [disc2_realForm]; exact_mod_cast NonzeroDisc.ne_zero))

/-- **$\mathcal G_p$ is the set of $\mathbb Z_p$-classes:** the map sending the $\mathbb Z_p$-class of a primitive
form of discriminant $D$ to the class of a unit value it takes is a well defined bijection
`LocalClasses p D ≃ LocalGroup p D` (two forms of discriminant $D$ with unit values in the same coset
of the norm group are equivalent, `equiv_of_same_unit_value`, and every coset is the class of
$w x^2 + \beta xy + w^{-1} c y^2$). -/
@[kb "cassels1978" "Ch. 14, §3, p. 339 (𝒢_p: the ℤ_p-classes form a group, ℤ_p^×/N)"]
noncomputable def localEquiv : LocalClasses p D ≃ LocalGroup p D :=
  Equiv.ofBijective
    (Quotient.lift (localCoset p D) (fun F G h =>
      (cosetOf_eq_iff _ four_ne_zero_padic (halfProp_padic p) (disc2_localPrim p D F) (disc2_localPrim p D G)
        _ _).2 h))
    ⟨by
      intro x y
      induction x using localClasses_ind with | _ F => ?_
      induction y using localClasses_ind with | _ G => ?_
      intro h
      exact localClasses_sound ((cosetOf_eq_iff _ four_ne_zero_padic (halfProp_padic p) (disc2_localPrim p D F)
        (disc2_localPrim p D G) _ _).1 h),
    by
      intro g
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective g
      refine ⟨Quotient.mk _ ⟨(principalData ℤ_[p] D).unitForm w, Or.inl ?_, ?_⟩, ?_⟩
      · rw [PrinData.unitForm, bq_coeff00]; exact w.isUnit
      · rw [neg_det_eq_disc2]; exact (principalData ℤ_[p] D).disc2_unitForm w
      · exact (principalData ℤ_[p] D).cosetOf_unitForm four_ne_zero_padic (halfProp_padic p) w _⟩

/-- **$\mathcal G_\infty$ is the set of real classes:** the analogue of `localEquiv` for
`RealClasses D ≃ RealGroup D`. -/
@[kb "cassels1978" "Ch. 14, §3, p. 339 (𝒢_∞: the real classes form a group, ℝ^×/N)"]
noncomputable def realEquiv : RealClasses D ≃ RealGroup D :=
  Equiv.ofBijective
    (Quotient.lift (realCoset D) (fun F G h =>
      (cosetOf_eq_iff _ (by norm_num) halfProp_real (disc2_realForm D F) (disc2_realForm D G) _ _).2 h))
    ⟨by
      intro x y
      induction x using Quotient.inductionOn with | _ F => ?_
      induction y using Quotient.inductionOn with | _ G => ?_
      intro h
      exact Quotient.sound ((cosetOf_eq_iff _ (by norm_num) halfProp_real (disc2_realForm D F)
        (disc2_realForm D G) _ _).1 h),
    by
      intro g
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective g
      refine ⟨Quotient.mk _ ⟨(principalData ℝ D).unitForm w, ?_⟩, ?_⟩
      · rw [neg_det_eq_disc2]; exact (principalData ℝ D).disc2_unitForm w
      · exact (principalData ℝ D).cosetOf_unitForm (by norm_num) halfProp_real w _⟩

end Groups

/-! ### The homomorphism $\mathcal G \to \mathcal G_p$ -/

section ClassHom

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] (D : ℤ) [NonzeroDisc D]

theorem disc2_map_int (f : BinQF) : disc2 (f.map (Int.castRingHom R)) = ((f.disc : ℤ) : R) := by
  rw [← neg_det_eq_disc2, neg_det_map_int]; simp

theorem eval_map_e0 (f : BinQF) : (f.map (Int.castRingHom R)).eval ![1, 0] = (f.a : R) := by
  rw [eval_map_two]; simp

/-- Helper: the class of a mapped integral form with unit first coefficient is the class of that coefficient. -/
theorem cosetOf_map_e0 (h4 : (4 : R) ≠ 0) (hh : HalfProp R) (f : PrimForm D)
    (hex : ∃ v, IsUnit ((f.1.map (Int.castRingHom R)).eval v)) (hu : IsUnit (f.1.a : R)) :
    cosetOf (principalData R D) (f.1.map (Int.castRingHom R)) hex = QuotientGroup.mk hu.unit := by
  have hv : IsUnit ((f.1.map (Int.castRingHom R)).eval ![1, 0]) := by rw [eval_map_e0]; exact hu
  rw [cosetOf_eq _ h4 hh (by rw [disc2_map_int, f.2.2]) hex hv]
  congr 1
  exact Units.ext (by simp [IsUnit.unit_spec, eval_map_e0])

/-- **The natural map $\mathcal G \to R^\times / N$** (Cassels, Ch. 14, §3, (3.1), p. 339), for the local ring
$R = \mathbb Z_p$ or $\mathbb R$ (with `hex`, `hu`, the inputs saying that every primitive integral form takes a unit
value over $R$ and that integers coprime to `M` are units of $R$): a class of $\mathcal G$ goes to the class of the unit
values of its representatives. That it is a homomorphism uses concordant representatives with first coefficients
prime to `M` (Lemma 2.3), for which the composition $[a_1 a_2, b, *]$ takes the value $a_1 a_2$. -/
noncomputable def classHom (h4 : (4 : R) ≠ 0) (hh : HalfProp R)
    (hex : ∀ f : PrimForm D, ∃ v, IsUnit ((f.1.map (Int.castRingHom R)).eval v))
    (M : ℤ) (hM : M ≠ 0) (hu : ∀ n : ℤ, IsCoprime n M → IsUnit (n : R)) :
    FormClass D →* Rˣ ⧸ (principalData R D).subgroup where
  toFun := Quotient.lift
    (fun f : PrimForm D => cosetOf (principalData R D) (f.1.map (Int.castRingHom R)) (hex f))
    (by
      intro f g h
      refine (cosetOf_eq_iff _ h4 hh ?_ ?_ _ _).2 ?_
      · rw [disc2_map_int, f.2.2]
      · rw [disc2_map_int, g.2.2]
      · exact IsometricGL.map (Int.castRingHom R) (SLEquiv.intEquiv (h : SLEquiv f.1 g.1)))
  map_one' := by
    have ha : (principal D).1.a = 1 := by simp [principal, principalForm]
    have hu1 : IsUnit (((principal D).1.a : ℤ) : R) := by rw [ha]; simp
    show cosetOf (principalData R D) ((principal D).1.map (Int.castRingHom R)) _ = 1
    rw [cosetOf_map_e0 D h4 hh _ _ hu1, ← QuotientGroup.mk_one]
    congr 1
    exact Units.ext (by simp [IsUnit.unit_spec, ha])
  map_mul' := by
    intro x y
    obtain ⟨f₁, rfl⟩ := mk_surjective x
    obtain ⟨f₂, rfl⟩ := mk_surjective y
    have hD0 : f₁.1.disc ≠ 0 := by rw [f₁.2.2]; exact NonzeroDisc.ne_zero
    obtain ⟨a₁, a₂, e₁, e₂, hc, -, hcop⟩ :=
      exists_concordant f₁.2.1 f₂.2.1 (f₁.2.2.trans f₂.2.2.symm) hD0 hM
    obtain ⟨g₁, hg₁, v₁⟩ : ∃ g : PrimForm D, mk g = mk f₁ ∧ g.1 = a₁ :=
      ⟨ofEquiv f₁ e₁, mk_ofEquiv f₁ e₁, rfl⟩
    obtain ⟨g₂, hg₂, v₂⟩ : ∃ g : PrimForm D, mk g = mk f₂ ∧ g.1 = a₂ :=
      ⟨ofEquiv f₂ e₂, mk_ofEquiv f₂ e₂, rfl⟩
    have hcg : Concordant g₁.1 g₂.1 := by rw [v₁, v₂]; exact hc
    have hu₁ : IsUnit (g₁.1.a : R) := hu _ (by rw [v₁]; exact hcop.of_mul_left_left)
    have hu₂ : IsUnit (g₂.1.a : R) := hu _ (by rw [v₂]; exact hcop.of_mul_left_right)
    have hu₃ : IsUnit (((PrimForm.comp g₁ g₂ hcg).1.a : ℤ) : R) := by
      rw [primComp_a]; push_cast; exact hu₁.mul hu₂
    rw [← hg₁, ← hg₂, mk_mul_mk g₁ g₂ hcg]
    show cosetOf (principalData R D) ((PrimForm.comp g₁ g₂ hcg).1.map (Int.castRingHom R)) _ =
      cosetOf (principalData R D) (g₁.1.map (Int.castRingHom R)) _ *
        cosetOf (principalData R D) (g₂.1.map (Int.castRingHom R)) _
    rw [cosetOf_map_e0 D h4 hh _ _ hu₃, cosetOf_map_e0 D h4 hh _ _ hu₁, cosetOf_map_e0 D h4 hh _ _ hu₂,
      ← QuotientGroup.mk_mul]
    congr 1
    exact Units.ext (by simp [IsUnit.unit_spec, primComp_a])

end ClassHom

section Instances

variable (p : ℕ) [Fact p.Prime] (D : ℤ) [NonzeroDisc D]

/-- Helper: a primitive integral binary form has a unit coefficient over $\mathbb Z_p$. -/
theorem isPrimitiveZp_map (f : BinQF) (hf : f.IsPrimitive) :
    IsPrimitiveZp (f.map (Int.castRingHom ℤ_[p])) := by
  have h00 : (f.map (Int.castRingHom ℤ_[p])).coeff 0 0 = ((f.a : ℤ) : ℤ_[p]) := rfl
  have h01 : (f.map (Int.castRingHom ℤ_[p])).coeff 0 1 = ((f.b : ℤ) : ℤ_[p]) := rfl
  have h11 : (f.map (Int.castRingHom ℤ_[p])).coeff 1 1 = ((f.c : ℤ) : ℤ_[p]) := rfl
  unfold IsPrimitiveZp
  rw [h00, h01, h11]
  by_cases ha : (p : ℤ) ∣ f.a
  · by_cases hb : (p : ℤ) ∣ f.b
    · by_cases hc : (p : ℤ) ∣ f.c
      · exfalso
        have hu := hf _ ha hb hc
        rw [Int.isUnit_iff] at hu
        have := (Fact.out : p.Prime).one_lt
        omega
      · exact Or.inr (Or.inr (isUnit_intCast_of_not_dvd p hc))
    · exact Or.inr (Or.inl (isUnit_intCast_of_not_dvd p hb))
  · exact Or.inl (isUnit_intCast_of_not_dvd p ha)

/-- **The natural homomorphism $\mathcal G \to \mathcal G_p$** (Cassels, Ch. 14, §3, (3.1), p. 339): a class goes to
the class, in $\mathbb Z_p^\times / N$, of a unit value of (any form of) the class. Well defined and a homomorphism for
every prime $p$ (`classHom`; in terms of $\mathbb Z_p$-classes of forms it is `localHom_mk`, so that the group law of
$\mathcal G_p$ is the one for which composition is compatible, `localCompositionWellDefined`). -/
@[kb "cassels1978" "Ch. 14, §3, p. 339, (3.1) (the natural homomorphism 𝒢 → 𝒢_p)"]
noncomputable def localHom : FormClass D →* LocalGroup p D :=
  classHom D four_ne_zero_padic (halfProp_padic p)
    (fun f => exists_unit_value (isPrimitiveZp_map p f.1 f.2.1)) p
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    (fun n hn => isUnit_intCast_of_not_dvd p (not_dvd_of_isCoprime hn))

/-- The `LocalPrimForm` of a global primitive form. -/
noncomputable def toLocalPrim (f : PrimForm D) : LocalPrimForm p D :=
  ⟨f.1.map (Int.castRingHom ℤ_[p]), isPrimitiveZp_map p f.1 f.2.1, by
    rw [neg_det_map_int, f.2.2]; simp⟩

/-- **(3.1): $\mathcal G \to \mathcal G_p$ sends a class to the $\mathbb Z_p$-class containing it:** under the
bijection `localEquiv`, `localHom` of the class of $f$ is the $\mathbb Z_p$-class of $f$. -/
@[kb "cassels1978" "Ch. 14, §3, p. 339, (3.1) (maps a class to the ℤ_p-class containing it)"]
theorem localHom_mk (f : PrimForm D) :
    localHom p D (mk f) = localEquiv p D (Quotient.mk (localSetoid p D) (toLocalPrim p D f)) := rfl

/-- The real analogue of `localHom`: $\mathcal G \to \mathcal G_\infty$. -/
@[kb "cassels1978" "Ch. 14, §3, p. 339, (3.1) (the natural homomorphism 𝒢 → 𝒢_∞)"]
noncomputable def realHom : FormClass D →* RealGroup D :=
  classHom D (by norm_num) halfProp_real
    (fun f => exists_isUnit_val_field _ (by
      rw [disc2_map_int, f.2.2]; exact_mod_cast NonzeroDisc.ne_zero)) 2 two_ne_zero
    (fun n hn => isUnit_iff_ne_zero.2 (by
      have := ne_zero_of_coprime_two_mul (N := 1) (by simpa using hn)
      exact_mod_cast this))

/-- The `RealForm` of a global primitive form. -/
noncomputable def toRealForm (f : PrimForm D) : RealForm D :=
  ⟨f.1.map (Int.castRingHom ℝ), by rw [neg_det_map_int, f.2.2]; simp⟩

theorem realHom_mk (f : PrimForm D) :
    realHom D (mk f) = realEquiv D (Quotient.mk (realSetoid D) (toRealForm D f)) := rfl

end Instances

-- PART4

end QuadFormsKB.Composition
