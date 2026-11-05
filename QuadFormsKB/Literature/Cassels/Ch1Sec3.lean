/-
# Cassels, Chapter 1, §3: a genus with two classes, and genera with one class

**Setting.** Integral forms `Q : QuadForm ℤ n`; the genus is `Siegel.SameGenus` ($\mathrm{GL}_n(\mathbb Z_p)$-equivalence
for every prime $p$ and $\mathrm{GL}_n(\mathbb R)$-equivalence), classes are `Siegel.IntEquiv`
($\mathrm{GL}_n(\mathbb Z)$-equivalence). Indices are $0$-based.

**Proves** (Cassels, *Rational Quadratic Forms*, Ch. 1, §3, p. 9)
* the forms $x_0^2 + 82x_1^2$ and $2x_0^2 + 41x_1^2$ are in the same genus (`sameGenus_f82_g41`) but are not
  integrally equivalent (`not_intEquiv_f82_g41`): the first represents $1$, the second does not. Cassels states this
  without proof (the theory is in Chapter 9). The local equivalences are explicit: with $u^2 = 2$,
  $(x_0, x_1) \mapsto (ux_0, u^{-1}x_1)$; with $v^2 = 41$, $(x_0, x_1) \mapsto (vx_1, v^{-1}x_0)$; with $z^2 = 82$
  ($p$ odd), $(x_0, x_1) \mapsto (x_0 + \tfrac z2x_1, z^{-1}x_0 - \tfrac12x_1)$. For every prime $p$ one of $2$, $41$,
  $82$ is a square in $\mathbb Z_p$ (for $p = 2$: $41 \equiv 1 \bmod 8$; for $p = 41$: $2 \equiv 17^2$; for other odd $p$
  the Legendre symbol is multiplicative).
* The genera of $x^2 + y^2$, $x^2 + y^2 + z^2$, $x^2 + y^2 + z^2 + t^2$ have one class each: the tag on
  `Siegel.sameGenus_sumSq_intEquiv` (proved for $n \le 5$).
-/
import QuadFormsKB.Siegel.FourSquaresClassNumber
import QuadFormsKB.Siegel.UnimodularPadic
import QuadFormsKB.Binary.GenusLocal

open Matrix

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels

open QuadFormsKB.Siegel

/-- The form $x_0^2 + 82x_1^2$ (Cassels' $x^2 + 82y^2$). -/
def f82 : QuadForm ℤ 2 := QuadForm.diag ![1, 82]

/-- The form $2x_0^2 + 41x_1^2$ (Cassels' $2x^2 + 41y^2$). -/
def g41 : QuadForm ℤ 2 := QuadForm.diag ![2, 41]

theorem map_diag {S : Type*} [CommRing S] (φ : ℤ →+* S) {m : ℕ} (a : Fin m → ℤ) :
    (QuadForm.diag a).map φ = QuadForm.diag (fun i => φ (a i)) := by
  ext i j
  simp only [QuadForm.map, QuadForm.diag, Matrix.map_apply, diagonal_apply]
  split_ifs <;> simp

theorem eval_f82 {S : Type*} [CommRing S] (φ : ℤ →+* S) (x : Fin 2 → S) :
    (f82.map φ).eval x = x 0 ^ 2 + 82 * x 1 ^ 2 := by
  rw [f82, map_diag, Kneser.eval_diag, Fin.sum_univ_two]
  simp

theorem eval_g41 {S : Type*} [CommRing S] (φ : ℤ →+* S) (x : Fin 2 → S) :
    (g41.map φ).eval x = 2 * x 0 ^ 2 + 41 * x 1 ^ 2 := by
  rw [g41, map_diag, Kneser.eval_diag, Fin.sum_univ_two]
  simp

/-- A $2 \times 2$ matrix with unit determinant as an element of $\mathrm{GL}_2$. -/
noncomputable def gl2 {S : Type*} [CommRing S] (a b c d : S) (h : IsUnit (a * d - b * c)) : GL (Fin 2) S :=
  Matrix.nonsingInvUnit !![a, b; c, d] (by rwa [det_fin_two_of])

theorem gl2_mulVec {S : Type*} [CommRing S] (a b c d : S) (h : IsUnit (a * d - b * c)) (x : Fin 2 → S) :
    ((gl2 a b c d h : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) *ᵥ x = ![a * x 0 + b * x 1, c * x 0 + d * x 1] := by
  ext i; fin_cases i <;> simp [gl2, Matrix.nonsingInvUnit, mulVec, dotProduct, Fin.sum_univ_two]

/-- Local equivalence when $2 = u^2$ with $u$ a unit: $(x_0, x_1) \mapsto (ux_0, u^{-1}x_1)$. -/
theorem isometricGL_of_sq_two {S : Type*} [CommRing S] (φ : ℤ →+* S) {u w : S} (huw : u * w = 1)
    (hu : u ^ 2 = 2) : IsometricGL (f82.map φ) (g41.map φ) := by
  refine ⟨gl2 u 0 0 w (by rw [mul_zero, sub_zero, huw]; exact isUnit_one), fun x => ?_⟩
  rw [gl2_mulVec, eval_f82, eval_g41]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination x 0 ^ 2 * hu + x 1 ^ 2 * (41 * (u * w + 1) * huw - 41 * w ^ 2 * hu)

/-- Local equivalence when $41 = v^2$ with $v$ a unit: $(x_0, x_1) \mapsto (vx_1, v^{-1}x_0)$. -/
theorem isometricGL_of_sq_41 {S : Type*} [CommRing S] (φ : ℤ →+* S) {v w : S} (hvw : v * w = 1)
    (hv : v ^ 2 = 41) : IsometricGL (f82.map φ) (g41.map φ) := by
  refine ⟨gl2 0 v w 0 (by rw [mul_zero, zero_sub, hvw]; exact isUnit_one.neg), fun x => ?_⟩
  rw [gl2_mulVec, eval_f82, eval_g41]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination x 0 ^ 2 * (2 * (v * w + 1) * hvw - 2 * w ^ 2 * hv) + x 1 ^ 2 * hv

/-- Local equivalence when $82 = z^2$ with $z$ a unit and $2$ a unit ($2h = 1$):
$(x_0, x_1) \mapsto (x_0 + zhx_1, z^{-1}x_0 - hx_1)$. -/
theorem isometricGL_of_sq_82 {S : Type*} [CommRing S] (φ : ℤ →+* S) {z w h : S} (hzw : z * w = 1)
    (hz : z ^ 2 = 82) (h2 : 2 * h = 1) : IsometricGL (f82.map φ) (g41.map φ) := by
  have hdet : 1 * -h - z * h * w = -1 := by linear_combination (-h) * hzw - h2
  refine ⟨gl2 1 (z * h) w (-h) (by rw [hdet]; exact isUnit_one.neg), fun x => ?_⟩
  rw [gl2_mulVec, eval_f82, eval_g41]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination x 0 ^ 2 * (-(w ^ 2) * hz + (z * w + 1) * hzw) +
    x 0 * x 1 * (-2 * h * z * hzw + 2 * h * w * hz) + x 1 ^ 2 * (h ^ 2 * hz + 41 * (2 * h + 1) * h2)

/-- A unit square root gives an inverse. -/
theorem exists_inv_of_sq_isUnit {S : Type*} [CommRing S] {u c : S} (hc : IsUnit c) (hu : u ^ 2 = c) :
    ∃ w, u * w = 1 := by
  have : IsUnit u := (isUnit_pow_iff two_ne_zero).1 (hu ▸ hc)
  exact ⟨_, this.mul_val_inv⟩

/-- Over $\mathbb Z_p$, an integer prime to $p$ which is a square modulo $p$ ($p$ odd) is a square. -/
theorem exists_sq_padic_of_isSquare {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a : ℤ} (ha : (a : ZMod p) ≠ 0)
    (hsq : IsSquare (a : ZMod p)) : ∃ z : ℤ_[p], z ^ 2 = a := by
  obtain ⟨s, hs⟩ := hsq
  refine Kneser.exists_sq_eq_of_toZMod hp2 (a : ℤ_[p]) (s := s) ?_ ?_
  · rintro rfl; exact ha (by rw [hs, mul_zero])
  · rw [map_intCast, hs, sq]

theorem isUnit_intCast_padic' {p : ℕ} [Fact p.Prime] {a : ℤ} (ha : (a : ZMod p) ≠ 0) : IsUnit (a : ℤ_[p]) :=
  Kneser.isUnit_of_toZMod_ne_zero (by rwa [map_intCast])

theorem two_ne_zero_zmod41 : ((2 : ℤ) : ZMod 41) ≠ 0 := by decide

theorem two_eq_sq_zmod41 : ((2 : ℤ) : ZMod 41) = 17 * 17 := by decide

/-- **Local equivalence at every prime** $p$: $x_0^2 + 82x_1^2$ and $2x_0^2 + 41x_1^2$ are equivalent over
$\mathbb Z_p$. -/
theorem isometricGL_padic_f82_g41 (p : ℕ) [hp : Fact p.Prime] :
    IsometricGL (f82.map (Int.castRingHom ℤ_[p])) (g41.map (Int.castRingHom ℤ_[p])) := by
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨v, hv⟩ := Binary.exists_sq_padic_two (c := 41) (by decide)
    have hu41 : IsUnit ((41 : ℤ) : ℤ_[2]) := isUnit_intCast_padic' (by decide +revert)
    obtain ⟨w, hw⟩ := exists_inv_of_sq_isUnit hu41 hv
    exact isometricGL_of_sq_41 _ hw (by rw [hv]; norm_num)
  have h2u : IsUnit ((2 : ℤ) : ℤ_[p]) := isUnit_intCast_padic' (by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h'))
  obtain ⟨h, hh⟩ := h2u.exists_right_inv
  by_cases hp41 : p = 41
  · subst hp41
    obtain ⟨u, hu⟩ := exists_sq_padic_of_isSquare hp2 (a := 2) two_ne_zero_zmod41 ⟨17, two_eq_sq_zmod41⟩
    obtain ⟨w, hw⟩ := exists_inv_of_sq_isUnit h2u hu
    exact isometricGL_of_sq_two _ hw (by rw [hu]; norm_num)
  have hne : ∀ q : ℕ, q.Prime → q ≠ p → ((q : ℤ) : ZMod p) ≠ 0 := by
    intro q hq hqp h
    have h' : ((q : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hqp ((Nat.prime_dvd_prime_iff_eq hp.out hq).1 h').symm
  have h2 : ((2 : ℤ) : ZMod p) ≠ 0 := hne 2 Nat.prime_two (Ne.symm hp2)
  have h41 : ((41 : ℤ) : ZMod p) ≠ 0 := hne 41 (by norm_num) (Ne.symm hp41)
  by_cases hs2 : IsSquare ((2 : ℤ) : ZMod p)
  · obtain ⟨u, hu⟩ := exists_sq_padic_of_isSquare hp2 h2 hs2
    obtain ⟨w, hw⟩ := exists_inv_of_sq_isUnit h2u hu
    exact isometricGL_of_sq_two _ hw (by rw [hu]; norm_num)
  by_cases hs41 : IsSquare ((41 : ℤ) : ZMod p)
  · obtain ⟨v, hv⟩ := exists_sq_padic_of_isSquare hp2 h41 hs41
    obtain ⟨w, hw⟩ := exists_inv_of_sq_isUnit (isUnit_intCast_padic' h41) hv
    exact isometricGL_of_sq_41 _ hw (by rw [hv]; norm_num)
  -- neither `2` nor `41` is a square mod `p`, so `82` is
  have h82 : ((82 : ℤ) : ZMod p) ≠ 0 := by
    rw [show (82 : ℤ) = 2 * 41 by norm_num, Int.cast_mul]; exact mul_ne_zero h2 h41
  have hs82 : IsSquare ((82 : ℤ) : ZMod p) := by
    rw [← legendreSym.eq_one_iff p h82, show (82 : ℤ) = 2 * 41 by norm_num, legendreSym.mul,
      (legendreSym.eq_neg_one_iff p).2 hs2, (legendreSym.eq_neg_one_iff p).2 hs41]
    norm_num
  obtain ⟨z, hz⟩ := exists_sq_padic_of_isSquare hp2 h82 hs82
  obtain ⟨w, hw⟩ := exists_inv_of_sq_isUnit (isUnit_intCast_padic' h82) hz
  exact isometricGL_of_sq_82 _ hw (by rw [hz]; norm_num) (by exact_mod_cast hh)

/-- **$x^2 + 82y^2$ and $2x^2 + 41y^2$ are in the same genus** (Cassels, Ch. 1, §3, p. 9: "integrally equivalent
everywhere locally"). -/
@[kb "cassels1978" "Ch. 1, §3, p. 9 (x² + 82y² and 2x² + 41y² are equivalent everywhere locally)"]
theorem sameGenus_f82_g41 : SameGenus f82 g41 := by
  refine ⟨fun p _ => isometricGL_padic_f82_g41 p, ?_⟩
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  exact isometricGL_of_sq_two _ (w := (Real.sqrt 2)⁻¹) (mul_inv_cancel₀ hne) (by rw [hs])

/-- **$x^2 + 82y^2$ and $2x^2 + 41y^2$ are not integrally equivalent** (Cassels, Ch. 1, §3, p. 9: "but not
globally"): the first represents $1$ and the second does not. -/
@[kb "cassels1978" "Ch. 1, §3, p. 9 (x² + 82y² and 2x² + 41y² are not equivalent globally)"]
theorem not_intEquiv_f82_g41 : ¬ IntEquiv f82 g41 := by
  intro h
  obtain ⟨g, hg⟩ := IsometricGL.symm h
  have h1 := hg ![1, 0]
  have e1 : f82.eval ![1, 0] = 1 := by
    have := eval_f82 (RingHom.id ℤ) ![1, 0]
    simpa [QuadForm.map] using this
  have e2 : ∀ y : Fin 2 → ℤ, g41.eval y = 2 * y 0 ^ 2 + 41 * y 1 ^ 2 := by
    intro y
    have := eval_g41 (RingHom.id ℤ) y
    simpa [QuadForm.map] using this
  rw [e1, e2] at h1
  set a := (g.val *ᵥ ![1, 0]) 0
  set b := (g.val *ᵥ ![1, 0]) 1
  have ha := sq_nonneg a
  have hb := sq_nonneg b
  omega

/-- The two forms lie in one genus that contains at least two classes. -/
theorem f82_g41_genus_two_classes : SameGenus f82 g41 ∧ ¬ IntEquiv f82 g41 :=
  ⟨sameGenus_f82_g41, not_intEquiv_f82_g41⟩

-- Ch. 1, §3, p. 9: the genera of x² + y², x² + y² + z² and x² + y² + z² + t² contain only one class
attribute [kb "cassels1978" "Ch. 1, §3, p. 9 (the genera of x² + y², x² + y² + z², x² + y² + z² + t² have one class; generalization: n ≤ 5)"]
  Siegel.sameGenus_sumSq_intEquiv

end QuadFormsKB.Cassels
