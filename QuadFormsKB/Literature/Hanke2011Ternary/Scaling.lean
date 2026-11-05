/-
# Hanke 2011 (ternary masses), §8: removing primitivity

J. Hanke, *Explicit formulas for masses of ternary quadratic lattices of varying determinant over number fields*,
arXiv:1109.1054 (bib key `hanke2011ternary`), proof of Theorem 8.1, p. 27.

Every positive definite integer-valued form is uniquely $Q = cQ_0$ with $c \ge 1$ and $Q_0$ primitive, and
$\det_H(cQ_0) = c^3\det_H(Q_0)$, $\mathrm{Aut}(cQ_0) = \mathrm{Aut}(Q_0)$. Hence (`DMass3_eq_DMass3star_mul`)
$$D_{\mathrm{Mass};3}(s) = D_{\mathrm{Mass}^*;3}(s)\cdot\zeta(3s),$$
the paper's "multiplying the primitive Dirichlet series by the local factor $(1 - q^{-3s})^{-1}$" at every prime.
-/
import QuadFormsKB.Literature.Hanke2011Ternary.Masses
import QuadFormsKB.Siegel.GenusFinite

namespace QuadFormsKB.Hanke2011Ternary

open Finset ArithmeticFunction QuadFormsKB.Siegel

section Helpers

open Matrix

/-- Helper: the scaled form $cQ$ (all coefficients multiplied by $c$). -/
def scaleForm (c : ℤ) (Q : QuadForm ℤ 3) : QuadForm ℤ 3 :=
  ⟨c • Q.coeff, fun i j h => by
    have := Q.upper h
    simp [this]⟩

theorem hessian_scaleForm (c : ℤ) (Q : QuadForm ℤ 3) :
    (scaleForm c Q).hessian = c • Q.hessian := by
  ext i j
  simp only [QuadForm.hessian, scaleForm, Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply,
    smul_eq_mul, mul_add]

theorem eval_scaleForm (c : ℤ) (Q : QuadForm ℤ 3) (x : Fin 3 → ℤ) :
    (scaleForm c Q).eval x = c * Q.eval x := by
  have h1 := LocalDensity.two_mul_eval_eq_hessian (scaleForm c Q) x
  have h2 := LocalDensity.two_mul_eval_eq_hessian Q x
  rw [hessian_scaleForm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h1
  have : 2 * (scaleForm c Q).eval x = 2 * (c * Q.eval x) := by
    rw [h1, ← mul_assoc, mul_comm 2 c, mul_assoc, h2]
  exact mul_left_cancel₀ two_ne_zero this

theorem det_hessian_scaleForm (c : ℤ) (Q : QuadForm ℤ 3) :
    (scaleForm c Q).hessian.det = c ^ 3 * Q.hessian.det := by
  rw [hessian_scaleForm, Matrix.det_smul]; simp

theorem posDef_scaleForm {c : ℤ} (hc : 0 < c) {Q : QuadForm ℤ 3} (hQ : IntQF.PosDef Q) :
    IntQF.PosDef (scaleForm c Q) := fun x hx => by
  rw [eval_scaleForm]; exact mul_pos hc (hQ x hx)

theorem posDef_of_scaleForm {c : ℤ} (hc : 0 < c) {Q : QuadForm ℤ 3}
    (hQ : IntQF.PosDef (scaleForm c Q)) : IntQF.PosDef Q := fun x hx => by
  have := hQ x hx
  rw [eval_scaleForm] at this
  exact (mul_pos_iff_of_pos_left hc).mp this

theorem intEquiv_scaleForm {c : ℤ} {Q Q' : QuadForm ℤ 3} (h : IntEquiv Q Q') :
    IntEquiv (scaleForm c Q) (scaleForm c Q') := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, fun x => by rw [eval_scaleForm, eval_scaleForm, hg]⟩

theorem intEquiv_scaleForm_iff {c : ℤ} (hc : c ≠ 0) {Q Q' : QuadForm ℤ 3} :
    IntEquiv (scaleForm c Q) (scaleForm c Q') ↔ IntEquiv Q Q' := by
  refine ⟨?_, intEquiv_scaleForm⟩
  rintro ⟨g, hg⟩
  exact ⟨g, fun x => by simpa [eval_scaleForm, hc] using hg x⟩

theorem aut_scaleForm {c : ℤ} (hc : c ≠ 0) (Q : QuadForm ℤ 3) : Aut (scaleForm c Q) = Aut Q := by
  ext g
  change (∀ x, (scaleForm c Q).eval (g.val *ᵥ x) = (scaleForm c Q).eval x) ↔
    ∀ x, Q.eval (g.val *ᵥ x) = Q.eval x
  simp [eval_scaleForm, hc]

/-- Helper: scaling on classes. -/
noncomputable def scaleClass (c : ℤ) : QClass 3 → QClass 3 :=
  Quotient.map (sa := intSetoid 3) (sb := intSetoid 3) (scaleForm c)
    fun _ _ h => intEquiv_scaleForm h

theorem scaleClass_classOf (c : ℤ) (Q : QuadForm ℤ 3) :
    scaleClass c (classOf Q) = classOf (scaleForm c Q) := rfl

theorem scaleClass_injective {c : ℤ} (hc : c ≠ 0) : Function.Injective (scaleClass c) := by
  intro a b
  refine Quotient.inductionOn₂ (s₁ := intSetoid 3) (s₂ := intSetoid 3) a b fun Q Q' h => ?_
  change classOf (scaleForm c Q) = classOf (scaleForm c Q') at h
  exact classOf_eq_classOf_iff.mpr ((intEquiv_scaleForm_iff hc).mp (classOf_eq_classOf_iff.mp h))

theorem autCard_scaleClass {c : ℤ} (hc : c ≠ 0) (a : QClass 3) :
    (scaleClass c a).autCard = a.autCard := by
  refine Quotient.inductionOn (s := intSetoid 3) a fun Q => ?_
  change (classOf (scaleForm c Q)).autCard = (classOf Q).autCard
  simp [aut_scaleForm hc]

theorem eval_eq_dot (Q : QuadForm ℤ 3) (x : Fin 3 → ℤ) : Q.eval x = x ⬝ᵥ (Q.coeff *ᵥ x) := by
  have := eval_map_eq_dotProduct (RingHom.id ℤ) Q x
  simpa [QuadForm.map] using this

/-- Helper: `d` divides every coefficient of `Q`. -/
def FormDiv (d : ℤ) (Q : QuadForm ℤ 3) : Prop := ∀ i j, d ∣ Q.coeff i j

theorem formDiv_iff_eval (d : ℤ) (Q : QuadForm ℤ 3) : FormDiv d Q ↔ ∀ x, d ∣ Q.eval x := by
  constructor
  · intro h x
    rw [eval_eq_dot]
    simp only [dotProduct, Matrix.mulVec]
    exact Finset.dvd_sum fun i _ => Dvd.dvd.mul_left
      (Finset.dvd_sum fun j _ => Dvd.dvd.mul_right (h i j) _) _
  · intro h i j
    have hdiag : ∀ i, d ∣ Q.coeff i i := fun i => by
      have := h (Pi.single i 1)
      rw [eval_eq_dot] at this
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
    rcases lt_trichotomy i j with hij | rfl | hij
    · have h1 := QuadForm.polar_eq_hessian ℤ Q (Pi.single i 1) (Pi.single j 1)
      have h2 : d ∣ Q.evalIn ℤ (Pi.single i 1 + Pi.single j 1) - Q.evalIn ℤ (Pi.single i 1) -
          Q.evalIn ℤ (Pi.single j 1) :=
        dvd_sub (dvd_sub (h _) (h _)) (h _)
      rw [h1] at h2
      have h3 : Q.coeff j i = 0 := Q.upper hij
      simpa [QuadForm.hessian, h3, Matrix.mulVec, dotProduct, Pi.single_apply] using h2
    · exact hdiag i
    · rw [Q.upper hij]; exact dvd_zero _

theorem formDiv_congr {d : ℤ} {Q Q' : QuadForm ℤ 3} (h : IntEquiv Q Q') :
    FormDiv d Q → FormDiv d Q' := by
  obtain ⟨g, hg⟩ := h
  intro hQ
  rw [formDiv_iff_eval] at hQ ⊢
  intro x
  rw [← hg]
  exact hQ _

theorem QuadForm.ext3 {A B : QuadForm ℤ 3} (h : A.coeff = B.coeff) : A = B := by
  cases A; cases B; simp_all

theorem exists_content {Q : QuadForm ℤ 3} (hdet : Q.hessian.det ≠ 0) :
    ∃ (c : ℕ) (Q0 : QuadForm ℤ 3), 0 < c ∧ Q = scaleForm c Q0 ∧ IsPrimitiveForm Q0 := by
  classical
  obtain ⟨g, hgdef⟩ : ∃ g : ℤ, g = Finset.univ.gcd (fun p : Fin 3 × Fin 3 => Q.coeff p.1 p.2) := ⟨_, rfl⟩
  have hdvd : ∀ i j, g ∣ Q.coeff i j := fun i j =>
    hgdef ▸ Finset.gcd_dvd (f := fun p : Fin 3 × Fin 3 => Q.coeff p.1 p.2) (Finset.mem_univ (i, j))
  have hg0 : g ≠ 0 := by
    intro h0
    apply hdet
    have hC : Q.coeff = 0 := by
      ext i j
      have := hdvd i j
      rw [h0] at this
      simpa using this
    have hh : Q.hessian = 0 := by simp [QuadForm.hessian, hC]
    rw [hh]; simp
  have hdg : ∀ i j, (g.natAbs : ℤ) ∣ Q.coeff i j := fun i j => Int.natAbs_dvd.mpr (hdvd i j)
  have hgpos : (g.natAbs : ℤ) ≠ 0 := by exact_mod_cast Int.natAbs_ne_zero.mpr hg0
  let Q0 : QuadForm ℤ 3 := ⟨Matrix.of fun i j => Q.coeff i j / (g.natAbs : ℤ), fun i j h => by
    have := Q.upper h
    simp [this]⟩
  have hQ : Q = scaleForm (g.natAbs : ℤ) Q0 := by
    apply QuadForm.ext3
    ext i j
    simp only [scaleForm, Q0, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    exact (Int.mul_ediv_cancel' (hdg i j)).symm
  refine ⟨g.natAbs, Q0, Int.natAbs_pos.mpr hg0, hQ, ?_⟩
  intro d hd
  have h1 : d * (g.natAbs : ℤ) ∣ g := by
    have hk : ∀ y : ℤ, (∀ p : Fin 3 × Fin 3, y ∣ Q.coeff p.1 p.2) → y ∣ g := fun y hy => by
      rw [hgdef]; exact Finset.dvd_gcd fun p _ => hy p
    refine hk _ fun p => ?_
    have := mul_dvd_mul_right (hd p.1 p.2) (g.natAbs : ℤ)
    have e : Q0.coeff p.1 p.2 * (g.natAbs : ℤ) = Q.coeff p.1 p.2 := Int.ediv_mul_cancel (hdg _ _)
    rwa [e] at this
  have h2 : d * (g.natAbs : ℤ) ∣ 1 * (g.natAbs : ℤ) := by
    rw [one_mul]; exact Int.dvd_natAbs.mpr h1
  exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hgpos).mp h2)

theorem formDiv_scale_iff {c d : ℤ} (hc : c ≠ 0) {Q0 : QuadForm ℤ 3} (hQ0 : IsPrimitiveForm Q0) :
    FormDiv d (scaleForm c Q0) ↔ d ∣ c := by
  constructor
  · intro h
    obtain ⟨e, a, b, he, hab, hd, hc'⟩ := Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_right d hc)
    have hcop : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.mpr hab
    have hdiv : ∀ i j, a ∣ Q0.coeff i j := fun i j => by
      have := h i j
      simp only [scaleForm, Matrix.smul_apply, smul_eq_mul] at this
      rw [hd, hc'] at this
      have he0 : (e : ℤ) ≠ 0 := by exact_mod_cast he.ne'
      exact hcop.dvd_of_dvd_mul_left ((mul_dvd_mul_iff_right he0).mp (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using this))
    have hua := hQ0 a hdiv
    rw [hd, hc']
    exact mul_dvd_mul hua.dvd dvd_rfl
  · intro h i j
    exact Dvd.dvd.mul_right h _

theorem content_unique {c c' : ℕ} (hc : 0 < c) (hc' : 0 < c') {Q0 Q0' : QuadForm ℤ 3}
    (h0 : IsPrimitiveForm Q0) (h0' : IsPrimitiveForm Q0')
    (he : IntEquiv (scaleForm c Q0) (scaleForm c' Q0')) : c = c' := by
  have hz : (c : ℤ) ≠ 0 := by exact_mod_cast hc.ne'
  have hz' : (c' : ℤ) ≠ 0 := by exact_mod_cast hc'.ne'
  have a1 : (c : ℤ) ∣ c' :=
    (formDiv_scale_iff hz' h0').mp (formDiv_congr he ((formDiv_scale_iff hz h0).mpr dvd_rfl))
  have a2 : (c' : ℤ) ∣ c :=
    (formDiv_scale_iff hz h0).mp (formDiv_congr (IsometricGL.symm he)
      ((formDiv_scale_iff hz' h0').mpr dvd_rfl))
  exact Nat.dvd_antisymm (Int.natCast_dvd_natCast.mp a1) (Int.natCast_dvd_natCast.mp a2)

theorem finite_primitiveTernaryClasses (M : ℕ) : (primitiveTernaryClasses M).Finite := by
  refine ((finite_setOf_hessian_bounded (n := 3) (Hermite.entryBound 3 (M : ℤ))).image
    classOf).subset ?_
  rintro k ⟨Q, rfl, hQ, -, hdet⟩
  obtain ⟨Q', he, hb⟩ := exists_intEquiv_hessian_bounded hQ
  exact ⟨Q', fun i j => by rw [hdet] at hb; exact hb i j, (classOf_eq_classOf_iff.mpr he).symm⟩

theorem nat_div_cast {N c : ℕ} {D : ℤ} (hc : 0 < c) (h : (N : ℤ) = (c : ℤ) ^ 3 * D) :
    c ^ 3 ∣ N ∧ ((N / c ^ 3 : ℕ) : ℤ) = D := by
  have hd : c ^ 3 ∣ N := Int.natCast_dvd_natCast.mp ⟨D, by push_cast; exact h⟩
  obtain ⟨m, hm⟩ := hd
  refine ⟨⟨m, hm⟩, ?_⟩
  rw [hm, Nat.mul_div_cancel_left _ (by positivity)]
  have hz : ((c : ℤ) ^ 3) ≠ 0 := by positivity
  apply mul_left_cancel₀ hz
  rw [← h, hm]; push_cast; ring

theorem ternaryClasses_eq {N : ℕ} (hN : N ≠ 0) :
    ternaryClasses N = ⋃ c ∈ (((N.divisors.filter fun c => c ^ 3 ∣ N : Finset ℕ)) : Set ℕ),
      scaleClass c '' primitiveTernaryClasses (N / c ^ 3) := by
  ext k
  simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors, Set.mem_image,
    exists_prop]
  constructor
  · rintro ⟨Q, rfl, hQ, hdet⟩
    have hdet0 : Q.hessian.det ≠ 0 := by rw [hdet]; exact_mod_cast hN
    obtain ⟨c, Q0, hc, rfl, hp⟩ := exists_content hdet0
    have hcz : (0 : ℤ) < c := by exact_mod_cast hc
    rw [det_hessian_scaleForm] at hdet
    obtain ⟨hd3, hdiv⟩ := nat_div_cast hc hdet.symm
    exact ⟨c, ⟨⟨(dvd_pow_self c (by norm_num)).trans hd3, hN⟩, hd3⟩, classOf Q0,
      ⟨Q0, rfl, posDef_of_scaleForm hcz hQ, hp, hdiv.symm⟩, rfl⟩
  · rintro ⟨c, ⟨⟨hcN, -⟩, hd3⟩, k', ⟨Q0, rfl, hpos, hp, hdet⟩, rfl⟩
    have hc : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hcN; exact hN hcN)
    refine ⟨scaleForm c Q0, rfl, posDef_scaleForm (by exact_mod_cast hc) hpos, ?_⟩
    rw [det_hessian_scaleForm, hdet]
    exact_mod_cast Nat.mul_div_cancel' hd3

theorem sum_scale {N : ℕ} (hN : N ≠ 0) :
    TMass3 N = ∑ c ∈ N.divisors.filter (fun c => c ^ 3 ∣ N), TMass3star (N / c ^ 3) := by
  have hpos : ∀ c ∈ N.divisors.filter (fun c => c ^ 3 ∣ N), 0 < c := fun c hc =>
    Nat.pos_of_mem_divisors (Finset.mem_filter.mp hc).1
  unfold TMass3
  rw [ternaryClasses_eq hN, finsum_mem_biUnion, finsum_mem_coe_finset
    (fun c : ℕ => ∑ᶠ j ∈ scaleClass (c : ℤ) '' primitiveTernaryClasses (N / c ^ 3), ((j.autCard : ℚ))⁻¹)]
  · refine Finset.sum_congr rfl fun c hc => ?_
    have hcz : (c : ℤ) ≠ 0 := by exact_mod_cast (hpos c hc).ne'
    rw [finsum_mem_image ((scaleClass_injective hcz).injOn)]
    unfold TMass3star
    refine finsum_mem_congr rfl fun a _ => ?_
    rw [autCard_scaleClass hcz]
  · intro c hc c' hc' hne
    refine Set.disjoint_left.mpr ?_
    rintro k ⟨a, ⟨Q0, rfl, -, hp, -⟩, h1⟩ ⟨b, ⟨Q0', rfl, -, hp', -⟩, h2⟩
    apply hne
    have hcc : IntEquiv (scaleForm c Q0) (scaleForm c' Q0') :=
      classOf_eq_classOf_iff.mp (by
        change scaleClass c (classOf Q0) = scaleClass c' (classOf Q0')
        rw [h1, h2])
    exact content_unique (hpos c hc) (hpos c' hc') hp hp' hcc
  · exact Finset.finite_toSet _
  · intro c _
    exact (finite_primitiveTernaryClasses _).image _

end Helpers

/-- **Removing primitivity** (proof of Theorem 8.1, p. 27, for $F = \mathbb{Q}$):
$D_{\mathrm{Mass};3}(s) = D_{\mathrm{Mass}^*;3}(s)\cdot\zeta(3s)$, i.e.
$\mathrm{TMass}_3(N) = \sum_{c^3 \mid N}\mathrm{TMass}^*_3(N/c^3)$. -/
@[kb "hanke2011ternary" "§8, proof of Thm. 8.1, p. 27 (non-primitive formula, F = Q)"]
theorem DMass3_eq_DMass3star_mul : DMass3 = DMass3star * zetaShift 3 0 := by
  ext N
  by_cases hN : N = 0
  · subst hN; simp
  rw [ArithmeticFunction.mul_apply]
  have hL : DMass3 N = TMass3 N := by simp [DMass3, hN]
  rw [hL, sum_scale hN]
  have hz : ∀ c : ℕ, 0 < c → zetaShift 3 0 (c ^ 3) = 1 := fun c hc => by
    unfold zetaShift
    rw [powPush_apply_pow (by norm_num) _ hc.ne']
    simp
  have himg : ∀ c ∈ N.divisors.filter (fun c => c ^ 3 ∣ N), 0 < c := fun c hc =>
    Nat.pos_of_mem_divisors (Finset.mem_filter.mp hc).1
  rw [← Finset.sum_subset (s₁ := (N.divisors.filter (fun c => c ^ 3 ∣ N)).image
      (fun c => (N / c ^ 3, c ^ 3))) (s₂ := N.divisorsAntidiagonal)]
  · rw [Finset.sum_image]
    · refine Finset.sum_congr rfl fun c hc => ?_
      have hd3 := (Finset.mem_filter.mp hc).2
      have hcp := himg c hc
      have hne : N / c ^ 3 ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hd3)
        (by positivity)).ne'
      simp [DMass3star, hne, hz c hcp]
    · intro c hc c' hc' h
      have := (Prod.mk.inj h).2
      exact Nat.pow_left_injective (by norm_num) this
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
    have hd3 := (Finset.mem_filter.mp hc).2
    rw [Nat.mem_divisorsAntidiagonal]
    exact ⟨Nat.div_mul_cancel hd3, hN⟩
  · intro x hx hnot
    rw [Nat.mem_divisorsAntidiagonal] at hx
    by_cases hex : ∃ m, m ^ 3 = x.2
    · exfalso
      obtain ⟨m, hm⟩ := hex
      apply hnot
      refine Finset.mem_image.mpr ⟨m, ?_, ?_⟩
      · have hd3 : m ^ 3 ∣ N := ⟨x.1, by rw [hm, ← hx.1, mul_comm]⟩
        have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; simp [← hm] at hx; exact hN hx.1.symm)
        exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨(dvd_pow_self m (by norm_num)).trans hd3, hN⟩, hd3⟩
      · have hm0 : 0 < m ^ 3 := by
          rcases Nat.eq_zero_or_pos (m ^ 3) with h | h
          · exfalso; rw [h] at hm; rw [← hm] at hx; simp at hx; exact hN hx.1.symm
          · exact h
        ext
        · simp only; rw [hm]; exact Nat.div_eq_of_eq_mul_left (hm ▸ hm0) (by rw [← hx.1])
        · simp only; exact hm
    · unfold zetaShift
      rw [powPush_apply_of_not _ hex, mul_zero]

/-- **Corollary 8.2** (both identities) under the named input `PrimitiveMassLocalFormula`: the primitive part is
`cor_8_2_primitive`, and the total part follows by `DMass3_eq_DMass3star_mul`, since
$\frac{1}{\zeta(3s)}\cdot\zeta(3s) = 1$ (`zetaShift_mul_zetaShiftInv`). -/
@[kb "hanke2011ternary" "§8, Cor. 8.2, p. 27; proof of Thm. 8.1, p. 27 (F = Q)"]
theorem cor82_of_input (H : PrimitiveMassLocalFormula) : Cor82 := by
  refine ⟨cor_8_2_primitive H, ?_⟩
  rw [DMass3_eq_DMass3star_mul, cor_8_2_primitive H, smul_mul_assoc, mul_assoc, mul_assoc,
    mul_comm (zetaShiftInv 3 0), zetaShift_mul_zetaShiftInv (by norm_num) 0, mul_one]

/-- **Theorem 1.1** (Hanke 2011, p. 2), under the named input `PrimitiveMassLocalFormula`: for every $m \ge 1$,
$$\mathrm{TMass}_3(2m) = \frac{1}{48}\sum_{\substack{m = a\cdot b^2\\ a, b > 0}} (ab - b^2),$$
and $\mathrm{TMass}_3(N) = 0$ for odd $N$. -/
@[kb "hanke2011ternary" "§1, Thm. 1.1, p. 2"]
theorem theorem_1_1 (H : PrimitiveMassLocalFormula) :
    (∀ m : ℕ, m ≠ 0 → TMass3 (2 * m) = (1 / 48) *
      ∑ ab ∈ (m.divisors ×ˢ m.divisors).filter (fun ab => ab.1 * ab.2 ^ 2 = m),
        ((ab.1 : ℚ) * ab.2 - (ab.2 : ℚ) ^ 2)) ∧
    (∀ N : ℕ, ¬ 2 ∣ N → TMass3 N = 0) :=
  ⟨fun m hm => theorem_1_1_divisor_sum (cor82_of_input H) m hm,
    fun N hN => theorem_1_1_odd (cor82_of_input H) N hN⟩

end QuadFormsKB.Hanke2011Ternary
